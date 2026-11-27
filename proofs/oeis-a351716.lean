import OMAStatements.S_oeis_a351716

-- Credit: @LoopsGod

namespace OMA.S_oeis_a351716.Proof

private theorem three_le_lucasTail (k : ℕ) : 3 ≤ lucasTail k := by
  induction k using Nat.twoStepInduction with
  | zero => decide
  | one => decide
  | more k h₀ h₁ => rw [lucasTail]; omega

private theorem step (k : ℕ) : lucasTail k < lucasTail (k+1) := by
  cases k with
  | zero => decide
  | succ k =>
    change lucasTail (k+1) < lucasTail (k+1) + lucasTail k
    have := three_le_lucasTail k
    omega

private theorem mono : StrictMono lucasTail := strictMono_nat_of_lt_succ step

private theorem largest_on (k n : ℕ) (h : lucasTail k ≤ n) (h' : n < lucasTail (k+1)) :
    largestLucas n = lucasTail k := by
  have hk := three_le_lucasTail k
  unfold largestLucas
  rw [if_neg (by omega)]
  apply congrArg lucasTail
  apply Nat.findGreatest_eq_iff.mpr
  refine ⟨(mono.id_le k).trans h, fun _ => h, ?_⟩
  intro j hj _
  exact Nat.not_le_of_lt (lt_of_lt_of_le h' (mono.monotone hj))

private theorem largest_le (n : ℕ) : largestLucas n ≤ n := by
  unfold largestLucas
  split
  · exact le_rfl
  · apply Nat.findGreatest_spec (P := fun k => lucasTail k ≤ n) (m := 0) (Nat.zero_le _)
    change 3 ≤ n
    omega

private theorem shift (k t : ℕ) (h : t < lucasTail k) :
    greedyWeight (lucasTail (k+1)+t) = 1 + greedyWeight t := by
  have hb := three_le_lucasTail (k+1)
  rw [greedyWeight.eq_def, dif_neg (by change lucasTail (k+1)+t ≠ 0; omega)]
  rw [largest_on (k+1) _ (by omega) (by change _ < lucasTail (k+1) + lucasTail k; omega)]
  rw [Nat.add_sub_cancel_left]

private theorem w0 : greedyWeight 0 = 0 := by rw [greedyWeight.eq_def]; rfl
private theorem at_coin (n : ℕ) (hp : 0 < n) (h : largestLucas n = n) :
    greedyWeight n = 1 := by
  rw [greedyWeight.eq_def, dif_neg (by omega), h, Nat.sub_self, w0]
private theorem w1 : greedyWeight 1 = 1 := at_coin 1 (by decide) (by decide)
private theorem w2 : greedyWeight 2 = 1 := at_coin 2 (by decide) (by decide)
private theorem w3 : greedyWeight 3 = 1 := at_coin 3 (by decide) (by decide)
private theorem w4 : greedyWeight 4 = 1 := at_coin 4 (by decide) (by decide)
private theorem w5 : greedyWeight 5 = 2 := by
  have h := shift 0 1 (by decide)
  change greedyWeight 5 = 1 + greedyWeight 1 at h
  simpa [w1] using h

/-- Every four-term window starting at n has an equal adjacent pair. -/
private def pairAt (n : ℕ) : Prop :=
  greedyWeight n = greedyWeight (n+1) ∨ greedyWeight (n+1) = greedyWeight (n+2) ∨ greedyWeight (n+2) = greedyWeight (n+3)

private def block (k : ℕ) : Prop :=
  greedyWeight (lucasTail k - 2) = greedyWeight (lucasTail k - 1) ∧ ∀ n, n+3 < lucasTail k → pairAt n

private theorem pairShift (k t : ℕ) (h : t+3 < lucasTail k) (p : pairAt t) :
    pairAt (lucasTail (k+1) + t) := by
  unfold pairAt at *
  simp only [Nat.add_assoc]
  rw [shift k t (by omega), shift k (t+1) (by omega),
      shift k (t+2) (by omega), shift k (t+3) h]
  simpa using p

/-- The last two weights before a Lucas denomination agree, and every four-term window
contained in that block contains an adjacent equal pair. -/
private theorem blocks (k : ℕ) : block k := by
  induction k using Nat.twoStepInduction with
  | zero =>
    constructor
    · change greedyWeight 1 = greedyWeight 2
      rw [w1, w2]
    · intro n h
      change n+3 < 3 at h
      omega
  | one =>
    constructor
    · change greedyWeight 2 = greedyWeight 3
      rw [w2, w3]
    · intro n h
      change n+3 < 4 at h
      have hn : n = 0 := by omega
      subst n
      exact Or.inr (Or.inl (w1.trans w2.symm))
  | more k ihA ihB =>
    obtain ⟨sa, pa⟩ := ihA
    obtain ⟨sb, pb⟩ := ihB
    have ha : 3 ≤ lucasTail k := three_le_lucasTail k
    have hb : 3 ≤ lucasTail (k+1) := three_le_lucasTail (k+1)
    change greedyWeight (lucasTail (k+1) + lucasTail k - 2) = greedyWeight (lucasTail (k+1) + lucasTail k - 1) ∧
      ∀ n, n+3 < lucasTail (k+1) + lucasTail k → pairAt n
    constructor
    · rw [show lucasTail (k+1) + lucasTail k - 2 = lucasTail (k+1) + (lucasTail k - 2) by omega,
          show lucasTail (k+1) + lucasTail k - 1 = lucasTail (k+1) + (lucasTail k - 1) by omega,
          shift k _ (by omega), shift k _ (by omega), sa]
    · intro n hn
      by_cases left : n+3 < lucasTail (k+1)
      · exact pb n left
      by_cases right : lucasTail (k+1) ≤ n
      · have h : n - lucasTail (k+1) + 3 < lucasTail k := by omega
        have hh := pairShift k _ h (pa _ h)
        rwa [show lucasTail (k+1) + (n - lucasTail (k+1)) = n by omega] at hh
      by_cases e : n+1 = lucasTail (k+1)
      · right; right
        rw [show n+2 = lucasTail (k+1)+1 by omega, show n+3 = lucasTail (k+1)+2 by omega,
            shift k 1 (by omega), shift k 2 (by omega), w1, w2]
      by_cases e' : n+2 = lucasTail (k+1)
      · left
        convert sb using 2 <;> omega
      · right; left
        convert sb using 2 <;> omega

private theorem every_pair (n : ℕ) : pairAt n := by
  have h : n+4 ≤ lucasTail (n+4) := mono.id_le _
  exact (blocks (n+4)).2 n (by omega)

private theorem zero_of_weight_zero (n : ℕ) (h : greedyWeight n = 0) : n = 0 := by
  by_contra hn
  rw [greedyWeight.eq_def, dif_neg hn] at h
  omega

private theorem coin_of_weight_one (n : ℕ) (hp : 0 < n) (h : greedyWeight n = 1) :
    largestLucas n = n := by
  rw [greedyWeight.eq_def, dif_neg (by omega)] at h
  have h' := zero_of_weight_zero (n - largestLucas n) (by omega)
  have := largest_le n
  omega

/-- Equal greedy weights of consecutive Lucas-Niven integers divide their difference. -/
private theorem adjacent_bound (t : ℕ) (p : IsLucasNiven t)
    (q : IsLucasNiven (t+1)) (same : greedyWeight t = greedyWeight (t+1)) : t ≤ 3 := by
  obtain ⟨ht, dt⟩ := p
  obtain ⟨hu, du⟩ := q
  change greedyWeight t ∣ t at dt
  change greedyWeight (t+1) ∣ t+1 at du
  rw [← same] at du
  have one : greedyWeight t = 1 := Nat.eq_one_of_dvd_one (by simpa using Nat.dvd_sub du dt)
  have ct := coin_of_weight_one t ht one
  have cu := coin_of_weight_one (t+1) hu (same.symm.trans one)
  by_contra! big
  unfold largestLucas at ct cu
  rw [if_neg (by omega)] at ct cu
  generalize Nat.findGreatest (fun k => lucasTail k ≤ t) t = i at ct
  generalize Nat.findGreatest (fun k => lucasTail k ≤ t+1) (t+1) = j at cu
  change lucasTail i = t at ct
  change lucasTail j = t+1 at cu
  have ij : i < j := mono.lt_iff_lt.mp (by omega)
  have gap := mono.monotone (show i+1 ≤ j from ij)
  cases i with
  | zero =>
    change 3 = t at ct
    omega
  | succ i =>
    change lucasTail (i+1) + lucasTail i ≤ lucasTail j at gap
    have := three_le_lucasTail i
    change lucasTail (i+1) = t at ct
    omega

theorem result (n : ℕ) : (∀ i : Fin 4, IsLucasNiven (n+i.val)) ↔ n = 1 := by
  constructor
  · intro h
    have h0 : IsLucasNiven n := h 0
    have h1 : IsLucasNiven (n+1) := h 1
    have h2 : IsLucasNiven (n+2) := h 2
    have h3 : IsLucasNiven (n+3) := h 3
    have low : n ≤ 3 := by
      rcases every_pair n with a | a | a
      · exact adjacent_bound n h0 h1 a
      · have := adjacent_bound (n+1) h1 h2 a
        omega
      · have := adjacent_bound (n+2) h2 h3 a
        omega
    have five : ¬IsLucasNiven 5 := by
      intro hf
      have hd := hf.2
      change greedyWeight 5 ∣ 5 at hd
      rw [w5] at hd
      omega
    have positive := h0.1
    by_contra hn
    have cases : n=2 ∨ n=3 := by omega
    rcases cases with rfl | rfl
    · exact five h3
    · exact five h2
  · rintro rfl i
    fin_cases i
    · change IsLucasNiven 1
      exact ⟨by decide, by rw [w1]⟩
    · change IsLucasNiven 2
      exact ⟨by decide, by rw [w2]; exact one_dvd _⟩
    · change IsLucasNiven 3
      exact ⟨by decide, by rw [w3]; exact one_dvd _⟩
    · change IsLucasNiven 4
      exact ⟨by decide, by rw [w4]; exact one_dvd _⟩

end OMA.S_oeis_a351716.Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a351716.main :=
  OMA.S_oeis_a351716.Proof.result
