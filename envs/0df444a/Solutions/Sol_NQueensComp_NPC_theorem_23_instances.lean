-- Prove2me | solution 1 for NQueensComp.NPC.theorem_23_instances
-- status  : ACCEPTED   (prove)
-- author  : @Victorized
-- created : 2026-11-03T03:09:09.292329+00:00
-- url     : https://prove2.me/submissions/4705aa4b-9356-443d-a3e4-182ea9a87561

import Mathlib
import Definitions.Def_NQueensComp_NPC_Reductions
import Theorems.Thm_NQueensComp_NPC_lemma_21

/-! Theorem 23, instance-level half (Gent, Jefferson & Nightingale 2017, pp. 829–830): for a valid
Problem 5 instance `Ms`, `def20 Ms` is a valid Problem 4 instance with exactly as many solutions
as `Ms`.  The bijection is `lemma22_map`, with inverse `lemma21_map` (Lemma 21); Lemma 22 is
reproved below. -/

open NQueensComp.NPC

namespace NQueensComp.NPC.T23Proof

/-! ### Lemma 22 (reproved here, since its platform statement is not imported) -/

theorem le_foldr_max (l : List ℕ) (x : ℕ) (hx : x ∈ l) : x ≤ l.foldr max 0 := by
  induction l with
  | nil => simp at hx
  | cons y l ih =>
    simp only [List.foldr_cons]
    rcases List.mem_cons.mp hx with rfl | h
    · exact le_max_left _ _
    · exact le_trans (ih h) (le_max_right _ _)

theorem band_nat (n x y a b : ℕ) (hx : x < n) (hy : y < n) (hab : a ≠ b) :
    x + 2 * n * a ≠ y + 2 * n * b := by
  intro h
  rcases Nat.lt_or_gt_of_ne hab with hlt | hlt
  · have : 2 * n * (a + 1) ≤ 2 * n * b := Nat.mul_le_mul_left _ hlt
    nlinarith
  · have : 2 * n * (b + 1) ≤ 2 * n * a := Nat.mul_le_mul_left _ hlt
    nlinarith

/-- Offsets that are multiples of `2n` separate the bands `[0, n)`. -/
theorem band_eq (n x y a b : ℕ) (hx : x < n) (hy : y < n)
    (h : x + 2 * n * a = y + 2 * n * b) : a = b ∧ x = y := by
  by_cases hab : a = b
  · subst hab
    exact ⟨rfl, by omega⟩
  · exact absurd h (band_nat n x y a b hx hy hab)

/-- The excluded sum-diagonals force the column block and the row block of a queen to agree. -/
theorem same_block (N k a b c r : ℕ) (ha : a < k) (hb : b < k) (hc : c < N) (hr : r < N)
    (hD : ¬ (c + 2 * N * a + (r + 2 * N * (k - 1 - b)) < 2 * N * (k - 1) ∨
      (2 * N * k ≤ c + 2 * N * a + (r + 2 * N * (k - 1 - b)) ∧
        c + 2 * N * a + (r + 2 * N * (k - 1 - b)) ≤ 2 * (N * (2 * k - 1)) - 2))) : a = b := by
  have hb' : 2 * N * (k - 1 - b) + 2 * N * b = 2 * N * (k - 1) := by
    rw [← Nat.mul_add]; congr 1; omega
  have ha' : 2 * N * a ≤ 2 * N * (k - 1) := Nat.mul_le_mul_left _ (by omega)
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have hk1 : 2 * N * (j + 1) = 2 * N * (j + 1 - 1) + 2 * N := by
    rw [Nat.add_sub_cancel]; ring
  have hk2 : N * (2 * (j + 1) - 1) = 2 * N * (j + 1 - 1) + N := by
    have : 2 * (j + 1) - 1 = 2 * j + 1 := by omega
    rw [this, Nat.add_sub_cancel]; ring
  rcases lt_trichotomy a b with h | h | h
  · have h1 : 2 * N * (a + 1) ≤ 2 * N * b := Nat.mul_le_mul_left _ h
    rw [Nat.mul_add, Nat.mul_one] at h1
    exact absurd (Or.inl (by omega)) hD
  · exact h
  · have h1 : 2 * N * (b + 1) ≤ 2 * N * a := Nat.mul_le_mul_left _ h
    rw [Nat.mul_add, Nat.mul_one] at h1
    exact absurd (Or.inr ⟨by omega, by omega⟩) hD

theorem nmax_ge (Ms : Inst5) (M : Inst4) (hM : M ∈ Ms) : M.n ≤ def20_nmax Ms :=
  le_foldr_max _ _ (List.mem_map_of_mem hM)

theorem valid_facts (M : Inst4) (hM : M.Valid) :
    1 ≤ M.n ∧ M.C.card = M.R.card ∧ (∀ c ∈ M.C, c < M.n) ∧ (∀ r ∈ M.R, r < M.n) ∧
      (∀ d ∈ M.Dm, -((M.n : ℤ) - 1) ≤ d ∧ d ≤ (M.n : ℤ) - 1) := by
  obtain ⟨⟨⟨h1, _, _⟩, h2, _, h3, h4⟩, h5, _⟩ := hM
  exact ⟨h1, h2, h3, h4, h5⟩

theorem sol_facts (M : Inst4) (S : Finset Queen) (hS : M.IsSol S) :
    S.card = M.C.card ∧ NonAttacking S ∧ (∀ q ∈ S, q.1 ∈ M.C ∧ q.2 ∈ M.R) ∧
      (∀ q ∈ S, diffDiag q ∉ M.Dm ∧ sumDiag q ∉ M.Dp) := by
  obtain ⟨⟨s1, _, s3, s4⟩, s5⟩ := hS
  simp only [Inst4.toInst3, Finset.card_empty, add_zero, Finset.sdiff_empty] at s1 s4
  exact ⟨s1, s3, fun q hq => s4 q hq, s5⟩

theorem sol_of_facts (M : Inst4) (S : Finset Queen) (h1 : S.card = M.C.card)
    (h2 : NonAttacking S) (h3 : ∀ q ∈ S, q.1 ∈ M.C ∧ q.2 ∈ M.R)
    (h4 : ∀ q ∈ S, diffDiag q ∉ M.Dm ∧ sumDiag q ∉ M.Dp) : M.IsSol S := by
  refine ⟨⟨?_, Finset.empty_subset _, h2, ?_⟩, h4⟩
  · simpa [Inst4.toInst3] using h1
  · intro q hq
    simp only [Inst4.toInst3, Finset.sdiff_empty] at hq
    exact h3 q hq

theorem def20_C_mem (Ms : Inst5) (hk : Ms.length ≠ 0) (x : ℕ) :
    x ∈ (def20 Ms).C ↔
      ∃ a, ∃ ha : a < Ms.length, ∃ c ∈ (Ms.get ⟨a, ha⟩).C, c + def20_alpha Ms a = x := by
  rw [def20, if_neg hk]
  simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_image]
  constructor
  · rintro ⟨⟨a, ha⟩, c, hc, h⟩
    exact ⟨a, ha, c, hc, h⟩
  · rintro ⟨a, ha, c, hc, h⟩
    exact ⟨⟨a, ha⟩, c, hc, h⟩

theorem def20_R_mem (Ms : Inst5) (hk : Ms.length ≠ 0) (x : ℕ) :
    x ∈ (def20 Ms).R ↔
      ∃ a, ∃ ha : a < Ms.length, ∃ r ∈ (Ms.get ⟨a, ha⟩).R, r + def20_beta Ms a = x := by
  rw [def20, if_neg hk]
  simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_image]
  constructor
  · rintro ⟨⟨a, ha⟩, c, hc, h⟩
    exact ⟨a, ha, c, hc, h⟩
  · rintro ⟨a, ha, c, hc, h⟩
    exact ⟨⟨a, ha⟩, c, hc, h⟩

theorem def20_Dm_mem (Ms : Inst5) (hk : Ms.length ≠ 0) (x : ℤ) :
    x ∈ (def20 Ms).Dm ↔
      ∃ a, ∃ ha : a < Ms.length, ∃ d ∈ (Ms.get ⟨a, ha⟩).Dm,
        d + (def20_alpha Ms a : ℤ) - (def20_beta Ms a : ℤ) = x := by
  rw [def20, if_neg hk]
  simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_image]
  constructor
  · rintro ⟨⟨a, ha⟩, c, hc, h⟩
    exact ⟨a, ha, c, hc, h⟩
  · rintro ⟨a, ha, c, hc, h⟩
    exact ⟨⟨a, ha⟩, c, hc, h⟩

theorem def20_Dp_mem (Ms : Inst5) (hk : Ms.length ≠ 0) (x : ℕ) :
    x ∈ (def20 Ms).Dp ↔
      (x < 2 * def20_nmax Ms * (Ms.length - 1) ∨
        (2 * def20_nmax Ms * Ms.length ≤ x ∧
          x ≤ 2 * (def20_nmax Ms * (2 * Ms.length - 1)) - 2)) := by
  rw [def20, if_neg hk]
  simp only [Finset.mem_union, Finset.mem_range, Finset.mem_Icc]

/-- Every queen of a solution of `def20 Ms` lies in exactly one diagonal block
`[0, n′)² + (αₐ, βₐ)` and comes from an admissible queen of the gadget `Mₐ`. -/
theorem decomp (Ms : Inst5) (hMs : Inst5Valid Ms) (hk : Ms.length ≠ 0) (S₄ : Finset Queen)
    (hS : (def20 Ms).IsSol S₄) (q : Queen) (hq : q ∈ S₄) :
    ∃ a, ∃ ha : a < Ms.length, ∃ p : Queen,
      p.1 ∈ (Ms.get ⟨a, ha⟩).C ∧ p.2 ∈ (Ms.get ⟨a, ha⟩).R ∧
      diffDiag p ∉ (Ms.get ⟨a, ha⟩).Dm ∧ p.1 < def20_nmax Ms ∧ p.2 < def20_nmax Ms ∧
      q = p + (def20_alpha Ms a, def20_beta Ms a) := by
  obtain ⟨_, _, hCR, hDD⟩ := sol_facts _ _ hS
  obtain ⟨hcq, hrq⟩ := hCR q hq
  obtain ⟨hdq, hsq⟩ := hDD q hq
  rw [def20_C_mem Ms hk] at hcq
  rw [def20_R_mem Ms hk] at hrq
  rw [def20_Dm_mem Ms hk] at hdq
  rw [def20_Dp_mem Ms hk] at hsq
  obtain ⟨a, ha, c, hc, hcq⟩ := hcq
  obtain ⟨b, hb, r, hr, hrq⟩ := hrq
  have hna := nmax_ge Ms _ (List.get_mem Ms ⟨a, ha⟩)
  have hnb := nmax_ge Ms _ (List.get_mem Ms ⟨b, hb⟩)
  have hcN : c < def20_nmax Ms :=
    lt_of_lt_of_le ((valid_facts _ (hMs _ (List.get_mem Ms ⟨a, ha⟩)).1).2.2.1 c hc) hna
  have hrN : r < def20_nmax Ms :=
    lt_of_lt_of_le ((valid_facts _ (hMs _ (List.get_mem Ms ⟨b, hb⟩)).1).2.2.2.1 r hr) hnb
  obtain ⟨x, y⟩ := q
  simp only at hcq hrq
  subst hcq hrq
  have hab : a = b := by
    apply same_block (def20_nmax Ms) Ms.length a b c r ha hb hcN hrN
    simpa only [sumDiag, def20_alpha, def20_beta] using hsq
  subst hab
  refine ⟨a, ha, (c, r), hc, hr, ?_, hcN, hrN, rfl⟩
  intro hd
  apply hdq
  refine ⟨a, ha, _, hd, ?_⟩
  simp only [diffDiag]
  push_cast
  ring

theorem l22_length (Ms : Inst5) (S₄ : Finset Queen) :
    (lemma22_map Ms S₄).length = Ms.length := by
  simp [lemma22_map]

theorem l22_mem (Ms : Inst5) (S₄ : Finset Queen) (a : ℕ) (ha : a < Ms.length) (p : Queen) :
    p ∈ (lemma22_map Ms S₄).getD a ∅ ↔
      p.1 < def20_nmax Ms ∧ p.2 < def20_nmax Ms ∧
        p + (def20_alpha Ms a, def20_beta Ms a) ∈ S₄ := by
  rw [List.getD_eq_getElem _ _ (by rw [l22_length]; exact ha)]
  simp [lemma22_map, Finset.mem_filter, Finset.mem_product, Finset.mem_range, and_assoc]

/-- Attacks are invariant under translation. -/
theorem attacks_shift (p₁ p₂ t : Queen) (h : Attacks p₁ p₂) : Attacks (p₁ + t) (p₂ + t) := by
  obtain ⟨hne, hl⟩ := h
  refine ⟨fun h' => hne (add_right_cancel h'), ?_⟩
  simp only [col, row, sumDiag, diffDiag, Prod.fst_add, Prod.snd_add] at hl ⊢
  rcases hl with h | h | h | h
  · left; omega
  · right; left; omega
  · right; right; left; omega
  · right; right; right; push_cast; linarith

/-- A queen of the `a`-th restricted block is an admissible queen of the gadget `Mₐ`. -/
theorem block_mem (Ms : Inst5) (hMs : Inst5Valid Ms) (hk : Ms.length ≠ 0) (S₄ : Finset Queen)
    (hS : (def20 Ms).IsSol S₄) (a : ℕ) (ha : a < Ms.length) (p : Queen)
    (h1 : p.1 < def20_nmax Ms) (_h2 : p.2 < def20_nmax Ms)
    (h3 : p + (def20_alpha Ms a, def20_beta Ms a) ∈ S₄) :
    p.1 ∈ (Ms.get ⟨a, ha⟩).C ∧ p.2 ∈ (Ms.get ⟨a, ha⟩).R ∧ diffDiag p ∉ (Ms.get ⟨a, ha⟩).Dm := by
  obtain ⟨b, hb, p', hC, hR, hD, h1', h2', heq⟩ := decomp Ms hMs hk S₄ hS _ h3
  have e1 := congrArg Prod.fst heq
  have e2 := congrArg Prod.snd heq
  simp only [Prod.fst_add, Prod.snd_add, def20_alpha, def20_beta] at e1 e2
  obtain ⟨rfl, h11⟩ := band_eq _ _ _ _ _ h1 h1' e1
  have h22 : p.2 = p'.2 := by omega
  have : p = p' := Prod.ext h11 h22
  subst this
  exact ⟨hC, hR, hD⟩

theorem offsets_sum (Ms : Inst5) (a : ℕ) (ha : a < Ms.length) :
    def20_alpha Ms a + def20_beta Ms a = 2 * def20_nmax Ms * (Ms.length - 1) := by
  simp only [def20_alpha, def20_beta]
  rw [← Nat.mul_add]
  congr 1
  omega

/-- The `a`-th restricted block is a solution of the gadget `Mₐ`. -/
theorem block_sol (Ms : Inst5) (hMs : Inst5Valid Ms) (hk : Ms.length ≠ 0) (S₄ : Finset Queen)
    (hS : (def20 Ms).IsSol S₄) (i : ℕ) (h₁ : i < Ms.length) :
    (Ms.get ⟨i, h₁⟩).IsSol ((lemma22_map Ms S₄).getD i ∅) := by
  obtain ⟨hcard, hNA, hCR, _⟩ := sol_facts _ _ hS
  have hinj : Set.InjOn Prod.fst (S₄ : Set Queen) := by
    intro q₁ h₁ q₂ h₂ h
    by_contra hne
    exact hNA q₁ h₁ q₂ h₂ ⟨hne, Or.inl h⟩
  have himg : S₄.image Prod.fst = (def20 Ms).C := by
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hx
      exact (hCR q hq).1
    · rw [Finset.card_image_of_injOn hinj, hcard]
  have hmem := l22_mem Ms S₄ i h₁
  have hbm : ∀ p ∈ (lemma22_map Ms S₄).getD i ∅, p.1 ∈ (Ms.get ⟨i, h₁⟩).C ∧
      p.2 ∈ (Ms.get ⟨i, h₁⟩).R ∧ diffDiag p ∉ (Ms.get ⟨i, h₁⟩).Dm := by
    intro p hp
    obtain ⟨p1, p2, p3⟩ := (hmem p).mp hp
    exact block_mem Ms hMs hk S₄ hS i h₁ p p1 p2 p3
  have hNAa : NonAttacking ((lemma22_map Ms S₄).getD i ∅) := by
    intro p₁ hp₁ p₂ hp₂ hatt
    exact hNA _ ((hmem p₁).mp hp₁).2.2 _ ((hmem p₂).mp hp₂).2.2 (attacks_shift _ _ _ hatt)
  apply sol_of_facts
  · have hinja : Set.InjOn Prod.fst (((lemma22_map Ms S₄).getD i ∅ : Finset Queen) : Set Queen) := by
      intro p₁ hp₁ p₂ hp₂ h
      by_contra hne
      exact hNAa p₁ hp₁ p₂ hp₂ ⟨hne, Or.inl h⟩
    rw [← Finset.card_image_of_injOn hinja]
    congr 1
    ext c
    simp only [Finset.mem_image]
    constructor
    · rintro ⟨p, hp, rfl⟩
      exact (hbm p hp).1
    · intro hc
      have hcN : c < def20_nmax Ms :=
        lt_of_lt_of_le ((valid_facts _ (hMs _ (List.get_mem Ms ⟨i, h₁⟩)).1).2.2.1 c hc)
          (nmax_ge Ms _ (List.get_mem Ms ⟨i, h₁⟩))
      have hx : c + def20_alpha Ms i ∈ (def20 Ms).C :=
        (def20_C_mem Ms hk _).mpr ⟨i, h₁, c, hc, rfl⟩
      rw [← himg] at hx
      obtain ⟨q, hq, hqc⟩ := Finset.mem_image.mp hx
      obtain ⟨b, hb, p', _, _, _, h1', h2', heq⟩ := decomp Ms hMs hk S₄ hS q hq
      rw [heq] at hqc hq
      simp only [Prod.fst_add, def20_alpha] at hqc
      obtain ⟨rfl, hpc⟩ := band_eq _ _ _ _ _ h1' hcN hqc
      exact ⟨p', (hmem p').mpr ⟨h1', h2', hq⟩, hpc⟩
  · exact hNAa
  · intro p hp
    exact ⟨(hbm p hp).1, (hbm p hp).2.1⟩
  · intro p hp
    refine ⟨(hbm p hp).2.2, ?_⟩
    rw [(hMs _ (List.get_mem _ _)).2]
    exact Finset.notMem_empty _

theorem lemma22_proof (Ms : Inst5) (hMs : Inst5Valid Ms) (hk : Ms ≠ []) (S₄ : Finset Queen)
    (hS : (def20 Ms).IsSol S₄) : Inst5IsSol Ms (lemma22_map Ms S₄) := by
  have hk0 : Ms.length ≠ 0 := fun h => hk (List.length_eq_zero_iff.mp h)
  obtain ⟨_, hNA, _, _⟩ := sol_facts _ _ hS
  refine ⟨List.forall₂_iff_get.mpr ⟨(l22_length Ms S₄).symm, fun i h₁ h₂ => ?_⟩, ?_⟩
  · have hblock : (lemma22_map Ms S₄).get ⟨i, h₂⟩ = (lemma22_map Ms S₄).getD i ∅ := by
      rw [List.getD_eq_getElem _ _ h₂]
      rfl
    rw [hblock]
    exact block_sol Ms hMs hk0 S₄ hS i h₁
  · intro a ha b hb hab qa hqa qb hqb hsum
    rw [l22_length] at ha hb
    obtain ⟨a1, _, a3⟩ := (l22_mem Ms S₄ a ha qa).mp hqa
    obtain ⟨b1, _, b3⟩ := (l22_mem Ms S₄ b hb qb).mp hqb
    apply hNA _ a3 _ b3
    refine ⟨fun h => ?_, Or.inr (Or.inr (Or.inl ?_))⟩
    · have e1 := congrArg Prod.fst h
      simp only [Prod.fst_add, def20_alpha] at e1
      exact hab (band_eq _ _ _ _ _ a1 b1 e1).1
    · have ta := offsets_sum Ms a ha
      have tb := offsets_sum Ms b hb
      simp only [sumDiag, Prod.fst_add, Prod.snd_add] at hsum ⊢
      omega


/-! ### Theorem 23: validity of `def20 Ms` and the bijection of solutions -/

theorem valid_of_facts (M : Inst4) (h1 : 1 ≤ M.n) (h2 : M.C.card = M.R.card)
    (h3 : ∀ c ∈ M.C, c < M.n) (h4 : ∀ r ∈ M.R, r < M.n)
    (h5 : ∀ d ∈ M.Dm, -((M.n : ℤ) - 1) ≤ d ∧ d ≤ (M.n : ℤ) - 1)
    (h6 : ∀ d ∈ M.Dp, (d : ℤ) ≤ 2 * (M.n : ℤ) - 2) : M.Valid := by
  refine ⟨⟨⟨h1, ?_, ?_⟩, h2, ?_, h3, h4⟩, h5, h6⟩
  · simp [Inst4.toInst3]
  · simp [Inst4.toInst3, DistinctRowsCols]
  · simp [Inst4.toInst3]

theorem dm_bound (N n na X Y T : ℕ) (d : ℤ) (hXY : X + Y = T) (hn : n = T + N)
    (hna : na ≤ N) (hd1 : -((na : ℤ) - 1) ≤ d) (hd2 : d ≤ (na : ℤ) - 1) :
    -((n : ℤ) - 1) ≤ d + (X : ℤ) - (Y : ℤ) ∧ d + (X : ℤ) - (Y : ℤ) ≤ (n : ℤ) - 1 := by
  subst hn hXY
  constructor <;> push_cast <;> omega

theorem dp_bound (N n T U V d : ℕ) (hN : 1 ≤ N) (hn : n = T + N) (hV : V = n)
    (hd : d < T ∨ (U ≤ d ∧ d ≤ 2 * V - 2)) : (d : ℤ) ≤ 2 * (n : ℤ) - 2 := by
  subst hn hV
  omega

theorem nmax_split (N k : ℕ) (hk : k ≠ 0) : N * (2 * k - 1) = 2 * N * (k - 1) + N := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have : 2 * (j + 1) - 1 = 2 * j + 1 := by omega
  rw [this, Nat.add_sub_cancel]
  ring

theorem def20_n (Ms : Inst5) (hk : Ms.length ≠ 0) :
    (def20 Ms).n = 2 * def20_nmax Ms * (Ms.length - 1) + def20_nmax Ms := by
  rw [def20, if_neg hk]
  exact nmax_split _ _ hk

theorem card_C (Ms : Inst5) (hMs : Inst5Valid Ms) (hk : Ms.length ≠ 0) :
    (def20 Ms).C.card = ∑ a : Fin Ms.length, (Ms.get a).C.card := by
  have hdisj : ((Finset.univ : Finset (Fin Ms.length)) : Set (Fin Ms.length)).PairwiseDisjoint
      (fun a => (Ms.get a).C.image (fun c => c + def20_alpha Ms a)) := by
    intro a _ b _ hab
    rw [Function.onFun, Finset.disjoint_left]
    intro c hca hcb
    simp only [Finset.mem_image, def20_alpha] at hca hcb
    obtain ⟨x, hx, rfl⟩ := hca
    obtain ⟨y, hy, hxy⟩ := hcb
    have h1 : x < def20_nmax Ms :=
      lt_of_lt_of_le ((valid_facts _ (hMs _ (List.get_mem Ms a)).1).2.2.1 x hx)
        (nmax_ge Ms _ (List.get_mem Ms a))
    have h2 : y < def20_nmax Ms :=
      lt_of_lt_of_le ((valid_facts _ (hMs _ (List.get_mem Ms b)).1).2.2.1 y hy)
        (nmax_ge Ms _ (List.get_mem Ms b))
    exact band_nat (def20_nmax Ms) y x b a h2 h1 (fun h => hab (Fin.ext h).symm) hxy
  rw [def20, if_neg hk]
  dsimp only
  rw [Finset.card_biUnion hdisj]
  apply Finset.sum_congr rfl
  intro a _
  exact Finset.card_image_of_injective _ (add_left_injective _)

theorem card_R (Ms : Inst5) (hMs : Inst5Valid Ms) (hk : Ms.length ≠ 0) :
    (def20 Ms).R.card = ∑ a : Fin Ms.length, (Ms.get a).R.card := by
  have hdisj : ((Finset.univ : Finset (Fin Ms.length)) : Set (Fin Ms.length)).PairwiseDisjoint
      (fun a => (Ms.get a).R.image (fun r => r + def20_beta Ms a)) := by
    intro a _ b _ hab
    rw [Function.onFun, Finset.disjoint_left]
    intro c hca hcb
    simp only [Finset.mem_image, def20_beta] at hca hcb
    obtain ⟨x, hx, rfl⟩ := hca
    obtain ⟨y, hy, hxy⟩ := hcb
    have h1 : x < def20_nmax Ms :=
      lt_of_lt_of_le ((valid_facts _ (hMs _ (List.get_mem Ms a)).1).2.2.2.1 x hx)
        (nmax_ge Ms _ (List.get_mem Ms a))
    have h2 : y < def20_nmax Ms :=
      lt_of_lt_of_le ((valid_facts _ (hMs _ (List.get_mem Ms b)).1).2.2.2.1 y hy)
        (nmax_ge Ms _ (List.get_mem Ms b))
    have ha := a.2
    have hb := b.2
    exact band_nat (def20_nmax Ms) y x (Ms.length - 1 - b) (Ms.length - 1 - a) h2 h1
      (fun h => hab (Fin.ext (by omega))) hxy
  rw [def20, if_neg hk]
  dsimp only
  rw [Finset.card_biUnion hdisj]
  apply Finset.sum_congr rfl
  intro a _
  exact Finset.card_image_of_injective _ (add_left_injective _)

/-- For a non-empty valid family, `def20 Ms` is an instance of Problem 4. -/
theorem def20_valid (Ms : Inst5) (hMs : Inst5Valid Ms) (hk : Ms.length ≠ 0) :
    (def20 Ms).Valid := by
  have hv := fun a (ha : a < Ms.length) =>
    valid_facts _ (hMs _ (List.get_mem Ms ⟨a, ha⟩)).1
  have hnle : ∀ a (ha : a < Ms.length), (Ms.get ⟨a, ha⟩).n ≤ def20_nmax Ms :=
    fun a ha => nmax_ge Ms _ (List.get_mem _ _)
  have hN : 1 ≤ def20_nmax Ms := by
    have h1 := (hv 0 (by omega)).1
    have h2 := hnle 0 (by omega)
    omega
  have hn := def20_n Ms hk
  have hα : ∀ a, a < Ms.length →
      def20_alpha Ms a + def20_beta Ms a = 2 * def20_nmax Ms * (Ms.length - 1) :=
    fun a ha => offsets_sum Ms a ha
  apply valid_of_facts
  · rw [hn]; omega
  · rw [card_C Ms hMs hk, card_R Ms hMs hk]
    apply Finset.sum_congr rfl
    intro a _
    exact (hv a a.2).2.1
  · intro x hx
    obtain ⟨a, ha, c, hc, rfl⟩ := (def20_C_mem Ms hk x).mp hx
    have h1 := (hv a ha).2.2.1 c hc
    have h2 := hnle a ha
    have h3 := hα a ha
    rw [hn]
    omega
  · intro x hx
    obtain ⟨a, ha, r, hr, rfl⟩ := (def20_R_mem Ms hk x).mp hx
    have h1 := (hv a ha).2.2.2.1 r hr
    have h2 := hnle a ha
    have h3 := hα a ha
    rw [hn]
    omega
  · intro x hx
    obtain ⟨a, ha, d, hd, rfl⟩ := (def20_Dm_mem Ms hk x).mp hx
    obtain ⟨hd1, hd2⟩ := (hv a ha).2.2.2.2 d hd
    exact dm_bound _ _ _ _ _ _ d (hα a ha) hn (hnle a ha) hd1 hd2
  · intro x hx
    have hx' := (def20_Dp_mem Ms hk x).mp hx
    exact dp_bound (def20_nmax Ms) _ _ _ _ x hN hn
      (by rw [hn, nmax_split _ _ hk]) hx'

/-- `lemma21_map ∘ lemma22_map` is the identity on solutions of `def20 Ms`. -/
theorem roundtrip1 (Ms : Inst5) (hMs : Inst5Valid Ms) (hk : Ms.length ≠ 0) (S₄ : Finset Queen)
    (hS : (def20 Ms).IsSol S₄) : lemma21_map Ms (lemma22_map Ms S₄) = S₄ := by
  ext q
  simp only [lemma21_map, shiftSet, Finset.mem_biUnion, Finset.mem_range, Finset.mem_image]
  constructor
  · rintro ⟨a, ha, p, hp, rfl⟩
    exact ((l22_mem Ms S₄ a ha p).mp hp).2.2
  · intro hq
    obtain ⟨a, ha, p, _, _, _, h1, h2, heq⟩ := decomp Ms hMs hk S₄ hS q hq
    refine ⟨a, ha, p, (l22_mem Ms S₄ a ha p).mpr ⟨h1, h2, ?_⟩, heq.symm⟩
    rw [← heq]
    exact hq

/-- The queens of a solution of the Problem 5 instance lie in `[0, n′)²`. -/
theorem ss_block (Ms : Inst5) (hMs : Inst5Valid Ms) (Ss : List (Finset Queen))
    (hSs : Inst5IsSol Ms Ss) (a : ℕ) (ha : a < Ms.length) (p : Queen)
    (hp : p ∈ Ss.getD a ∅) : p.1 < def20_nmax Ms ∧ p.2 < def20_nmax Ms := by
  obtain ⟨hF, _⟩ := hSs
  have hlen := hF.length_eq
  have h := (List.forall₂_iff_get.mp hF).2 a ha (by omega)
  rw [List.getD_eq_getElem _ _ (by omega)] at hp
  obtain ⟨_, _, hCR, _⟩ := sol_facts _ _ h
  obtain ⟨hc, hr⟩ := hCR p hp
  have hv := valid_facts _ (hMs _ (List.get_mem Ms ⟨a, ha⟩)).1
  have hn := nmax_ge Ms _ (List.get_mem Ms ⟨a, ha⟩)
  have h1 := hv.2.2.1 _ hc
  have h2 := hv.2.2.2.1 _ hr
  exact ⟨by omega, by omega⟩

/-- `lemma22_map ∘ lemma21_map` is the identity on solutions of `Ms`. -/
theorem roundtrip2 (Ms : Inst5) (hMs : Inst5Valid Ms) (Ss : List (Finset Queen))
    (hSs : Inst5IsSol Ms Ss) : lemma22_map Ms (lemma21_map Ms Ss) = Ss := by
  have hlen : Ss.length = Ms.length := hSs.1.length_eq.symm
  apply List.ext_getElem
  · rw [l22_length, hlen]
  · intro i h₁ h₂
    have hi : i < Ms.length := by rw [l22_length] at h₁; exact h₁
    rw [← List.getD_eq_getElem _ (∅ : Finset Queen) h₁,
      ← List.getD_eq_getElem _ (∅ : Finset Queen) h₂]
    ext p
    rw [l22_mem Ms _ i hi p]
    simp only [lemma21_map, shiftSet, Finset.mem_biUnion, Finset.mem_range, Finset.mem_image]
    constructor
    · rintro ⟨h1, _, b, hb, p', hp', heq⟩
      obtain ⟨h1', _⟩ := ss_block Ms hMs Ss hSs b hb p' hp'
      have e1 := congrArg Prod.fst heq
      have e2 := congrArg Prod.snd heq
      simp only [Prod.fst_add, Prod.snd_add, def20_alpha, def20_beta] at e1 e2
      obtain ⟨rfl, h11⟩ := band_eq _ _ _ _ _ h1' h1 e1
      have h22 : p'.2 = p.2 := by omega
      have : p' = p := Prod.ext h11 h22
      subst this
      exact hp'
    · intro hp
      obtain ⟨h1, h2⟩ := ss_block Ms hMs Ss hSs i hi p hp
      exact ⟨h1, h2, i, hi, p, hp, rfl⟩

/-- The empty family: `def20 [] = ⟨1, {0}, {0}, {}, {}⟩` has the unique solution `{(0, 0)}`. -/
theorem sols_nil : {S : Finset Queen | (def20 []).IsSol S} = {{((0 : ℕ), (0 : ℕ))}} := by
  have hd : def20 [] = ⟨1, {0}, {0}, ∅, ∅⟩ := by rw [def20, if_pos List.length_nil]
  ext S
  simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff, hd]
  constructor
  · intro hS
    obtain ⟨hcard, _, hCR, _⟩ := sol_facts _ _ hS
    simp only [Finset.card_singleton] at hcard
    obtain ⟨x, rfl⟩ := Finset.card_eq_one.mp hcard
    obtain ⟨h1, h2⟩ := hCR x (Finset.mem_singleton_self x)
    simp only [Finset.mem_singleton] at h1 h2
    rw [show x = (0, 0) from Prod.ext h1 h2]
  · rintro rfl
    apply sol_of_facts
    · simp
    · intro q₁ h₁ q₂ h₂ hatt
      rw [Finset.mem_singleton] at h₁ h₂
      exact hatt.1 (h₁.trans h₂.symm)
    · intro q hq
      rw [Finset.mem_singleton] at hq
      subst hq
      simp
    · intro q _
      simp

theorem sols5_nil : {Ss : List (Finset Queen) | Inst5IsSol [] Ss} = {[]} := by
  ext Ss
  simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hF, _⟩
    exact List.forall₂_nil_left_iff.mp hF
  · rintro rfl
    exact ⟨List.Forall₂.nil, fun a ha => absurd ha (by simp)⟩

theorem theorem23_proof :
    ∀ Ms : Inst5, Inst5Valid Ms →
      (def20 Ms).Valid ∧
        _root_.Set.ncard {S : Finset Queen | (def20 Ms).IsSol S} =
          _root_.Set.ncard {Ss : List (Finset Queen) | Inst5IsSol Ms Ss} := by
  intro Ms hMs
  by_cases hk : Ms.length = 0
  · have h0 : Ms = [] := List.length_eq_zero_iff.mp hk
    subst h0
    refine ⟨?_, ?_⟩
    · have hd : def20 [] = ⟨1, {0}, {0}, ∅, ∅⟩ := by rw [def20, if_pos List.length_nil]
      rw [hd]
      apply valid_of_facts <;> simp
    · rw [sols_nil, sols5_nil, Set.ncard_singleton, Set.ncard_singleton]
  · have hne : Ms ≠ [] := fun h => hk (by simp [h])
    refine ⟨def20_valid Ms hMs hk, ?_⟩
    apply Set.ncard_congr (fun S _ => lemma22_map Ms S)
    · intro S hS
      exact lemma22_proof Ms hMs hne S hS
    · intro S S' hS hS' h
      calc S = lemma21_map Ms (lemma22_map Ms S) := (roundtrip1 Ms hMs hk S hS).symm
        _ = lemma21_map Ms (lemma22_map Ms S') := by rw [h]
        _ = S' := roundtrip1 Ms hMs hk S' hS'
    · intro Ss hSs
      exact ⟨lemma21_map Ms Ss, NQueensComp.NPC.lemma_21 Ms hMs hne Ss hSs,
        roundtrip2 Ms hMs Ss hSs⟩

end NQueensComp.NPC.T23Proof

theorem solution :
    ∀ Ms : Inst5, Inst5Valid Ms →
      (def20 Ms).Valid ∧
        _root_.Set.ncard {S : Finset Queen | (def20 Ms).IsSol S} =
          _root_.Set.ncard {Ss : List (Finset Queen) | Inst5IsSol Ms Ss} :=
  NQueensComp.NPC.T23Proof.theorem23_proof
