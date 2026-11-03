-- Prove2me | solution 1 for NQueensComp.NPC.theorem_36_instances
-- status  : ACCEPTED   (prove)
-- author  : @Victorized
-- created : 2026-11-03T04:35:37.800176+00:00
-- url     : https://prove2.me/submissions/f2104961-9596-4e08-9472-a1123e48b0eb

import Mathlib
import Definitions.Def_NQueensComp_NPC_Reductions

/-! Theorem 36, instance-level half (Gent, Jefferson & Nightingale 2017, p. 836): the family
`M₅` of Definition 31 is an instance of Problem 5, and its solutions correspond bijectively to
the solutions of the Restricted 1-in-3-SAT instance. -/

open NQueensComp.NPC

namespace NQueensComp.NPC.T36Proof






/-! ### Queens in general position and gadget solutions -/

/-- Two queens with different columns, rows, sum-diagonals and difference-diagonals. -/
abbrev Indep (p q : Queen) : Prop :=
  p.1 ≠ q.1 ∧ p.2 ≠ q.2 ∧ p.1 + p.2 ≠ q.1 + q.2 ∧ (p.1 : ℤ) - p.2 ≠ (q.1 : ℤ) - q.2

theorem Indep.symm' {p q : Queen} (h : Indep p q) : Indep q p :=
  ⟨h.1.symm, h.2.1.symm, h.2.2.1.symm, h.2.2.2.symm⟩

theorem not_attacks_of_indep {p q : Queen} (h : Indep p q) : ¬ Attacks p q := by
  rintro ⟨-, h' | h' | h' | h'⟩
  · exact h.1 h'
  · exact h.2.1 h'
  · exact h.2.2.1 h'
  · exact h.2.2.2 h'

theorem na_pair {S : Finset Queen} (hna : NonAttacking S) {p q : Queen} (hp : p ∈ S)
    (hq : q ∈ S) (hne : p ≠ q) : Indep p q := by
  have h := hna p hp q hq
  exact ⟨fun h1 => h ⟨hne, Or.inl h1⟩, fun h2 => h ⟨hne, Or.inr (Or.inl h2)⟩,
    fun h3 => h ⟨hne, Or.inr (Or.inr (Or.inl h3))⟩,
    fun h4 => h ⟨hne, Or.inr (Or.inr (Or.inr h4))⟩⟩

theorem na_two {p1 p2 : Queen} (h12 : Indep p1 p2) : NonAttacking {p1, p2} := by
  intro q hq q' hq'
  simp only [Finset.mem_insert, Finset.mem_singleton] at hq hq'
  rcases hq with rfl | rfl <;> rcases hq' with rfl | rfl
  · exact fun h => h.1 rfl
  · exact not_attacks_of_indep h12
  · exact not_attacks_of_indep h12.symm'
  · exact fun h => h.1 rfl

theorem na_three {p1 p2 p3 : Queen} (h12 : Indep p1 p2) (h13 : Indep p1 p3)
    (h23 : Indep p2 p3) : NonAttacking {p1, p2, p3} := by
  intro q hq q' hq'
  simp only [Finset.mem_insert, Finset.mem_singleton] at hq hq'
  rcases hq with rfl | rfl | rfl <;> rcases hq' with rfl | rfl | rfl
  · exact fun h => h.1 rfl
  · exact not_attacks_of_indep h12
  · exact not_attacks_of_indep h13
  · exact not_attacks_of_indep h12.symm'
  · exact fun h => h.1 rfl
  · exact not_attacks_of_indep h23
  · exact not_attacks_of_indep h13.symm'
  · exact not_attacks_of_indep h23.symm'
  · exact fun h => h.1 rfl

/-- Solutions of a gadget with `D⁺ = {}`. -/
theorem isSol_iff (M : Inst4) (hM : M.Dp = ∅) (S : Finset Queen) :
    M.IsSol S ↔ S.card = M.C.card ∧ NonAttacking S ∧ (∀ q ∈ S, q.1 ∈ M.C ∧ q.2 ∈ M.R) ∧
      (∀ q ∈ S, diffDiag q ∉ M.Dm) := by
  simp only [Inst4.IsSol, Inst4.toInst3, Inst3.IsSol, hM, Finset.card_empty, add_zero,
    Finset.empty_subset, true_and, Finset.sdiff_empty, Finset.notMem_empty, not_false_eq_true,
    and_true, col, row]
  constructor
  · rintro ⟨⟨h1, h2, h3⟩, h4⟩
    exact ⟨h1, h2, h3, h4⟩
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨⟨h1, h2, h3⟩, h4⟩

theorem card_three {p1 p2 p3 : Queen} (h12 : Indep p1 p2) (h13 : Indep p1 p3)
    (h23 : Indep p2 p3) : ({p1, p2, p3} : Finset Queen).card = 3 :=
  Finset.card_eq_three.mpr ⟨p1, p2, p3, fun h => h12.1 (congrArg Prod.fst h),
    fun h => h13.1 (congrArg Prod.fst h), fun h => h23.1 (congrArg Prod.fst h), rfl⟩

theorem card_two {p1 p2 : Queen} (h12 : Indep p1 p2) : ({p1, p2} : Finset Queen).card = 2 :=
  Finset.card_pair (fun h => h12.1 (congrArg Prod.fst h))

theorem sol3_of (M : Inst4) (hP : M.Dp = ∅) (p1 p2 p3 : Queen) (hC : M.C.card = 3)
    (i12 : Indep p1 p2) (i13 : Indep p1 p3) (i23 : Indep p2 p3)
    (hm1 : p1.1 ∈ M.C ∧ p1.2 ∈ M.R) (hm2 : p2.1 ∈ M.C ∧ p2.2 ∈ M.R)
    (hm3 : p3.1 ∈ M.C ∧ p3.2 ∈ M.R) (hd1 : diffDiag p1 ∉ M.Dm) (hd2 : diffDiag p2 ∉ M.Dm)
    (hd3 : diffDiag p3 ∉ M.Dm) : M.IsSol {p1, p2, p3} := by
  rw [isSol_iff M hP]
  refine ⟨by rw [hC]; exact card_three i12 i13 i23, na_three i12 i13 i23, ?_, ?_⟩
  · intro q hq
    simp only [Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with rfl | rfl | rfl <;> assumption
  · intro q hq
    simp only [Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with rfl | rfl | rfl <;> assumption

theorem sol2_of (M : Inst4) (hP : M.Dp = ∅) (p1 p2 : Queen) (hC : M.C.card = 2)
    (i12 : Indep p1 p2) (hm1 : p1.1 ∈ M.C ∧ p1.2 ∈ M.R) (hm2 : p2.1 ∈ M.C ∧ p2.2 ∈ M.R)
    (hd1 : diffDiag p1 ∉ M.Dm) (hd2 : diffDiag p2 ∉ M.Dm) : M.IsSol {p1, p2} := by
  rw [isSol_iff M hP]
  refine ⟨by rw [hC]; exact card_two i12, na_two i12, ?_, ?_⟩
  · intro q hq
    simp only [Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with rfl | rfl <;> assumption
  · intro q hq
    simp only [Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with rfl | rfl <;> assumption

/-- A non-attacking set of three queens in three given columns has one queen in each. -/
theorem perm3 (S : Finset Queen) (c1 c2 c3 : ℕ) (h12 : c1 ≠ c2) (h13 : c1 ≠ c3)
    (h23 : c2 ≠ c3) (hcard : S.card = 3) (hcol : ∀ q ∈ S, q.1 = c1 ∨ q.1 = c2 ∨ q.1 = c3)
    (hna : NonAttacking S) : ∃ r1 r2 r3 : ℕ, S = {(c1, r1), (c2, r2), (c3, r3)} := by
  have hinj : ∀ q ∈ S, ∀ q' ∈ S, q.1 = q'.1 → q = q' := by
    intro q hq q' hq' h
    by_contra hne
    exact hna q hq q' hq' ⟨hne, Or.inl h⟩
  have himg : S.image Prod.fst = {c1, c2, c3} := by
    apply Finset.eq_of_subset_of_card_le
    · intro c hc
      rw [Finset.mem_image] at hc
      obtain ⟨q, hq, rfl⟩ := hc
      simp only [Finset.mem_insert, Finset.mem_singleton]
      exact hcol q hq
    · rw [Finset.card_image_of_injOn (fun q hq q' hq' h => hinj q hq q' hq' h), hcard]
      exact Finset.card_le_three
  have hex : ∀ c ∈ ({c1, c2, c3} : Finset ℕ), ∃ r, (c, r) ∈ S := by
    intro c hc
    rw [← himg, Finset.mem_image] at hc
    obtain ⟨q, hq, rfl⟩ := hc
    exact ⟨q.2, by simpa using hq⟩
  obtain ⟨r1, hr1⟩ := hex c1 (by simp)
  obtain ⟨r2, hr2⟩ := hex c2 (by simp)
  obtain ⟨r3, hr3⟩ := hex c3 (by simp)
  refine ⟨r1, r2, r3, ?_⟩
  ext q
  simp only [Finset.mem_insert, Finset.mem_singleton]
  constructor
  · intro hq
    rcases hcol q hq with h | h | h
    · exact Or.inl (hinj q hq _ hr1 h)
    · exact Or.inr (Or.inl (hinj q hq _ hr2 h))
    · exact Or.inr (Or.inr (hinj q hq _ hr3 h))
  · rintro (rfl | rfl | rfl) <;> assumption

/-- A non-attacking set of two queens in two given columns has one queen in each. -/
theorem perm2 (S : Finset Queen) (c1 c2 : ℕ) (h12 : c1 ≠ c2) (hcard : S.card = 2)
    (hcol : ∀ q ∈ S, q.1 = c1 ∨ q.1 = c2) (hna : NonAttacking S) :
    ∃ r1 r2 : ℕ, S = {(c1, r1), (c2, r2)} := by
  have hinj : ∀ q ∈ S, ∀ q' ∈ S, q.1 = q'.1 → q = q' := by
    intro q hq q' hq' h
    by_contra hne
    exact hna q hq q' hq' ⟨hne, Or.inl h⟩
  have himg : S.image Prod.fst = {c1, c2} := by
    apply Finset.eq_of_subset_of_card_le
    · intro c hc
      rw [Finset.mem_image] at hc
      obtain ⟨q, hq, rfl⟩ := hc
      simp only [Finset.mem_insert, Finset.mem_singleton]
      exact hcol q hq
    · rw [Finset.card_image_of_injOn (fun q hq q' hq' h => hinj q hq q' hq' h), hcard]
      exact Finset.card_le_two
  have hex : ∀ c ∈ ({c1, c2} : Finset ℕ), ∃ r, (c, r) ∈ S := by
    intro c hc
    rw [← himg, Finset.mem_image] at hc
    obtain ⟨q, hq, rfl⟩ := hc
    exact ⟨q.2, by simpa using hq⟩
  obtain ⟨r1, hr1⟩ := hex c1 (by simp)
  obtain ⟨r2, hr2⟩ := hex c2 (by simp)
  refine ⟨r1, r2, ?_⟩
  ext q
  simp only [Finset.mem_insert, Finset.mem_singleton]
  constructor
  · intro hq
    rcases hcol q hq with h | h
    · exact Or.inl (hinj q hq _ hr1 h)
    · exact Or.inr (hinj q hq _ hr2 h)
  · rintro (rfl | rfl) <;> assumption

/-- The solutions of a `G¹`-shaped gadget. -/
theorem g3_struct (M : Inst4) (c1 c2 c3 : ℕ) (hC : M.C = {c1, c2, c3}) (hR : M.R = {0, 7, 14})
    (hD : M.Dm = {(c3 : ℤ) - 7, (c1 : ℤ) - 14}) (hP : M.Dp = ∅)
    (h12 : c1 ≠ c2) (h13 : c1 ≠ c3) (h23 : c2 ≠ c3) (S : Finset Queen) (h : M.IsSol S) :
    ∃ r1 r2 r3 : ℕ, ((r1 = 0 ∧ r2 = 7 ∧ r3 = 14) ∨ (r1 = 7 ∧ r2 = 0 ∧ r3 = 14) ∨
      (r1 = 7 ∧ r2 = 14 ∧ r3 = 0)) ∧ S = {(c1, r1), (c2, r2), (c3, r3)} := by
  rw [isSol_iff M hP, hC, hR, hD] at h
  obtain ⟨hcard, hna, hmem, hdm⟩ := h
  have hc3 : ({c1, c2, c3} : Finset ℕ).card = 3 :=
    Finset.card_eq_three.mpr ⟨c1, c2, c3, h12, h13, h23, rfl⟩
  obtain ⟨r1, r2, r3, rfl⟩ := perm3 S c1 c2 c3 h12 h13 h23 (hcard.trans hc3)
    (fun q hq => by simpa using (hmem q hq).1) hna
  refine ⟨r1, r2, r3, ?_, rfl⟩
  have m1 := (hmem (c1, r1) (by simp)).2
  have m2 := (hmem (c2, r2) (by simp)).2
  have m3 := (hmem (c3, r3) (by simp)).2
  have d1 := hdm (c1, r1) (by simp)
  have d3 := hdm (c3, r3) (by simp)
  have i12 := na_pair hna (p := (c1, r1)) (q := (c2, r2)) (by simp) (by simp) (by simp [h12])
  have i13 := na_pair hna (p := (c1, r1)) (q := (c3, r3)) (by simp) (by simp) (by simp [h13])
  have i23 := na_pair hna (p := (c2, r2)) (q := (c3, r3)) (by simp) (by simp) (by simp [h23])
  simp only [Finset.mem_insert, Finset.mem_singleton] at m1 m2 m3 d1 d3
  simp only [diffDiag] at d1 d3
  obtain ⟨-, a12, -, -⟩ := i12
  obtain ⟨-, a13, -, -⟩ := i13
  obtain ⟨-, a23, -, -⟩ := i23
  dsimp only at a12 a13 a23 d1 d3
  omega

/-- The solutions of a `G²`/`G³`-shaped gadget. -/
theorem g2_struct (M : Inst4) (c1 c2 h : ℕ) (hh : h ≠ 0) (hC : M.C = {c1, c2})
    (hR : M.R = {0, h}) (hP : M.Dp = ∅) (h12 : c1 ≠ c2) (S : Finset Queen) (hS : M.IsSol S) :
    ∃ s1 s2 : ℕ, ((s1 = 0 ∧ s2 = h) ∨ (s1 = h ∧ s2 = 0)) ∧ S = {(c1, s1), (c2, s2)} := by
  rw [isSol_iff M hP, hC, hR] at hS
  obtain ⟨hcard, hna, hmem, -⟩ := hS
  have hc2 : ({c1, c2} : Finset ℕ).card = 2 := Finset.card_pair h12
  obtain ⟨s1, s2, rfl⟩ := perm2 S c1 c2 h12 (hcard.trans hc2)
    (fun q hq => by simpa using (hmem q hq).1) hna
  refine ⟨s1, s2, ?_, rfl⟩
  have m1 := (hmem (c1, s1) (by simp)).2
  have m2 := (hmem (c2, s2) (by simp)).2
  have i12 := na_pair hna (p := (c1, s1)) (q := (c2, s2)) (by simp) (by simp) (by simp [h12])
  simp only [Finset.mem_insert, Finset.mem_singleton] at m1 m2
  obtain ⟨-, a12, -, -⟩ := i12
  dsimp only at a12
  omega

/-! ### The variable gadget -/

theorem red_eq (δ : ℕ) : redSol δ = {(δ, 0), (δ + 1, 3), (δ + 3, 2)} := by
  simp only [redSol, shiftSet, Finset.image_insert, Finset.image_singleton, Prod.mk_add_mk,
    zero_add, add_zero]
  rw [add_comm 1 δ, add_comm 3 δ]

theorem blue_eq (δ : ℕ) : blueSol δ = {(δ, 2), (δ + 1, 0), (δ + 3, 3)} := by
  simp only [blueSol, shiftSet, Finset.image_insert, Finset.image_singleton, Prod.mk_add_mk,
    zero_add, add_zero]
  rw [add_comm 1 δ, add_comm 3 δ]

theorem red_ne_blue (δ : ℕ) : redSol δ ≠ blueSol δ := by
  intro h
  have hm : (δ, 0) ∈ redSol δ := by rw [red_eq]; simp
  rw [h, blue_eq] at hm
  simp at hm

theorem G0v_C (cs : Inst6) (v : ℕ) :
    (G0v cs v).C = {delta cs v, delta cs v + 1, delta cs v + 3} := by
  simp only [G0v, Inst4.shift, G0, Finset.image_insert, Finset.image_singleton, zero_add]
  rw [add_comm 1 (delta cs v), add_comm 3 (delta cs v)]

/-- `G⁰ᵢ` has exactly the red and the blue solution. -/
theorem G0v_sol (cs : Inst6) (v : ℕ) (S : Finset Queen) :
    (G0v cs v).IsSol S ↔ S = redSol (delta cs v) ∨ S = blueSol (delta cs v) := by
  have hDm : (G0v cs v).Dm = ∅ := by simp [G0v, Inst4.shift, G0]
  have hR : (G0v cs v).R = {0, 2, 3} := rfl
  rw [isSol_iff _ rfl, G0v_C, hDm, hR, red_eq, blue_eq]
  generalize delta cs v = δ
  have hc3 : ({δ, δ + 1, δ + 3} : Finset ℕ).card = 3 :=
    Finset.card_eq_three.mpr ⟨δ, δ + 1, δ + 3, by omega, by omega, by omega, rfl⟩
  constructor
  · rintro ⟨hcard, hna, hmem, -⟩
    obtain ⟨r1, r2, r3, rfl⟩ := perm3 S δ (δ + 1) (δ + 3) (by omega) (by omega) (by omega)
      (hcard.trans hc3) (fun q hq => by simpa using (hmem q hq).1) hna
    have m1 := (hmem (δ, r1) (by simp)).2
    have m2 := (hmem (δ + 1, r2) (by simp)).2
    have m3 := (hmem (δ + 3, r3) (by simp)).2
    have i12 := na_pair hna (p := (δ, r1)) (q := (δ + 1, r2)) (by simp) (by simp) (by simp)
    have i13 := na_pair hna (p := (δ, r1)) (q := (δ + 3, r3)) (by simp) (by simp) (by simp)
    have i23 := na_pair hna (p := (δ + 1, r2)) (q := (δ + 3, r3)) (by simp) (by simp) (by simp)
    simp only [Finset.mem_insert, Finset.mem_singleton] at m1 m2 m3
    obtain ⟨-, a12, b12, c12⟩ := i12
    obtain ⟨-, a13, b13, c13⟩ := i13
    obtain ⟨-, a23, b23, c23⟩ := i23
    dsimp only at a12 b12 c12 a13 b13 c13 a23 b23 c23
    push_cast at c12 c13 c23
    rcases m1 with rfl | rfl | rfl <;> rcases m2 with rfl | rfl | rfl <;>
      rcases m3 with rfl | rfl | rfl <;>
      first
      | (exfalso; omega)
      | (left; rfl)
      | (right; rfl)
  · rintro (rfl | rfl)
    · refine ⟨?_, na_three ?_ ?_ ?_, ?_, by simp⟩
      · rw [hc3]; exact card_three (by omega) (by omega) (by omega)
      all_goals first
        | (refine ⟨?_, ?_, ?_, ?_⟩ <;> dsimp only <;> (try push_cast) <;> omega)
        | (intro q hq
           simp only [Finset.mem_insert, Finset.mem_singleton] at hq
           rcases hq with rfl | rfl | rfl <;> simp)
    · refine ⟨?_, na_three ?_ ?_ ?_, ?_, by simp⟩
      · rw [hc3]; exact card_three (by omega) (by omega) (by omega)
      all_goals first
        | (refine ⟨?_, ?_, ?_, ?_⟩ <;> dsimp only <;> (try push_cast) <;> omega)
        | (intro q hq
           simp only [Finset.mem_insert, Finset.mem_singleton] at hq
           rcases hq with rfl | rfl | rfl <;> simp)

/-! ### Colours and sum-diagonal conflicts -/

/-- No queen of `A` shares a sum-diagonal with a queen of `B`. -/
def SumDisj (A B : Finset Queen) : Prop := ∀ q ∈ A, ∀ q' ∈ B, sumDiag q ≠ sumDiag q'

/-- The red (`true`) or blue (`false`) solution of `G⁰ ⊕ δ`. -/
def colorSol (b : Bool) (δ : ℕ) : Finset Queen := if b then redSol δ else blueSol δ

theorem colorSol_true (δ : ℕ) : colorSol true δ = redSol δ := rfl

theorem colorSol_false (δ : ℕ) : colorSol false δ = blueSol δ := rfl

theorem exists_color {S : Finset Queen} {δ : ℕ} (h : S = redSol δ ∨ S = blueSol δ) :
    ∃ b, S = colorSol b δ := by
  rcases h with rfl | rfl
  · exact ⟨true, rfl⟩
  · exact ⟨false, rfl⟩

theorem colorSol_sol (cs : Inst6) (v : ℕ) (b : Bool) :
    (G0v cs v).IsSol (colorSol b (delta cs v)) := by
  rw [G0v_sol]
  cases b
  · exact Or.inr rfl
  · exact Or.inl rfl

theorem dRed_cases (r : ℕ) : dRed r = 0 ∨ dRed r = 4 ∨ dRed r = 5 := by
  match r with
  | 0 => exact Or.inl rfl
  | 1 => exact Or.inr (Or.inl rfl)
  | r + 2 => exact Or.inr (Or.inr rfl)

theorem dBlue_cases (r : ℕ) : dBlue r = 1 ∨ dBlue r = 2 ∨ dBlue r = 6 := by
  match r with
  | 0 => exact Or.inl rfl
  | 1 => exact Or.inr (Or.inl rfl)
  | r + 2 => exact Or.inr (Or.inr rfl)

theorem blue_hit (δ r : ℕ) : ∃ q ∈ blueSol δ, sumDiag q = δ + dBlue r := by
  rw [blue_eq]
  rcases dBlue_cases r with h | h | h <;> rw [h]
  · exact ⟨(δ + 1, 0), by simp, rfl⟩
  · exact ⟨(δ, 2), by simp, rfl⟩
  · exact ⟨(δ + 3, 3), by simp, by simp only [sumDiag]; try omega⟩

theorem red_hit (δ r : ℕ) : ∃ q ∈ redSol δ, sumDiag q = δ + dRed r := by
  rw [red_eq]
  rcases dRed_cases r with h | h | h <;> rw [h]
  · exact ⟨(δ, 0), by simp, rfl⟩
  · exact ⟨(δ + 1, 3), by simp, by simp only [sumDiag]; try omega⟩
  · exact ⟨(δ + 3, 2), by simp, by simp only [sumDiag]; try omega⟩

/-- A row-`0` queen in the blue column of `v` meets the blue solution of `G⁰_v`. -/
theorem hit_blue {S : Finset Queen} {δ r c : ℕ} (hd : SumDisj S (blueSol δ))
    (hc : c = δ + dBlue r) (hmem : (c, 0) ∈ S) : False := by
  obtain ⟨q, hq, hsum⟩ := blue_hit δ r
  exact hd (c, 0) hmem q hq (by rw [hsum, hc]; rfl)

/-- A row-`0` queen in the red column of `v` meets the red solution of `G⁰_v`. -/
theorem hit_red {S : Finset Queen} {δ r c : ℕ} (hd : SumDisj S (redSol δ))
    (hc : c = δ + dRed r) (hmem : (c, 0) ∈ S) : False := by
  obtain ⟨q, hq, hsum⟩ := red_hit δ r
  exact hd (c, 0) hmem q hq (by rw [hsum, hc]; rfl)

/-! ### Clauses and variable indices -/

theorem mem_vars (cs : Inst6) (v : ℕ) : v ∈ vars cs ↔ ∃ c ∈ cs, v ∈ c := by
  unfold vars
  induction cs with
  | nil => simp
  | cons c cs ih => simp [List.foldr, ih]

theorem mem_vars_of (cs : Inst6) (j : ℕ) (hj : j < cs.length) (v : ℕ) (hv : v ∈ cs[j]) :
    v ∈ vars cs :=
  (mem_vars cs v).mpr ⟨cs[j], List.getElem_mem hj, hv⟩

theorem varIdx_lt (cs : Inst6) {u v : ℕ} (hu : u ∈ vars cs) (huv : u < v) :
    varIdx cs u < varIdx cs v := by
  unfold varIdx
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset]
  · exact ⟨u, Finset.mem_filter.mpr ⟨hu, huv⟩, by simp⟩
  · intro w hw
    simp only [Finset.mem_filter] at hw ⊢
    exact ⟨hw.1, by omega⟩

theorem sort_lt (s : Finset ℕ) : (s.sort (· ≤ ·)).Pairwise (· < ·) :=
  ((Finset.pairwise_sort s (· ≤ ·)).and (Finset.sort_nodup s (· ≤ ·))).imp
    (fun h => lt_of_le_of_ne h.1 h.2)

/-- The three variables of a clause, in increasing order. -/
theorem clause_facts (cs : Inst6) (hcs : Inst6Valid cs) (j : ℕ) (hj : j < cs.length) :
    clauseVar cs j 0 < clauseVar cs j 1 ∧ clauseVar cs j 1 < clauseVar cs j 2 ∧
    cs[j] = {clauseVar cs j 0, clauseVar cs j 1, clauseVar cs j 2} := by
  have hc : cs.getD j ∅ = cs[j] := List.getD_eq_getElem _ _ hj
  have hcard : (cs[j]).card = 3 := hcs.2.1 _ (List.getElem_mem hj)
  have hsorted := sort_lt (cs[j])
  have hlen : ((cs[j]).sort (· ≤ ·)).length = 3 := by rw [Finset.length_sort, hcard]
  have htf := Finset.sort_toFinset (cs[j]) (· ≤ ·)
  unfold clauseVar
  rw [hc]
  generalize (cs[j]).sort (· ≤ ·) = L at hsorted hlen htf
  obtain ⟨x, y, z, rfl⟩ : ∃ x y z, L = [x, y, z] := by
    match L, hlen with
    | [x, y, z], _ => exact ⟨x, y, z, rfl⟩
  simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq, List.Pairwise.nil, and_true, IsEmpty.forall_iff, implies_true] at hsorted
  refine ⟨by simpa using hsorted.1.1, by simpa using hsorted.2, ?_⟩
  rw [← htf]
  simp

theorem clause_arith (cs : Inst6) (hcs : Inst6Valid cs) (j : ℕ) (hj : j < cs.length) :
    varIdx cs (clauseVar cs j 0) < varIdx cs (clauseVar cs j 1) ∧
    varIdx cs (clauseVar cs j 1) < varIdx cs (clauseVar cs j 2) := by
  obtain ⟨h01, h12, hc⟩ := clause_facts cs hcs j hj
  have m0 : clauseVar cs j 0 ∈ vars cs := mem_vars_of cs j hj _ (by rw [hc]; simp)
  have m1 : clauseVar cs j 1 ∈ vars cs := mem_vars_of cs j hj _ (by rw [hc]; simp)
  exact ⟨varIdx_lt cs m0 h01, varIdx_lt cs m1 h12⟩

theorem dBlue_le (r : ℕ) : dBlue r ≤ 6 := by
  rcases dBlue_cases r with h | h | h <;> omega

theorem dRed_le (r : ℕ) : dRed r ≤ 6 := by
  rcases dRed_cases r with h | h | h <;> omega

/-- Linear facts about the columns of a clause gadget. -/
theorem cols_facts (cs : Inst6) (j v : ℕ) :
    colBlue cs j v = 21 * varIdx cs v + dBlue (occRank cs v j) ∧
    colRed cs j v = 21 * varIdx cs v + dRed (occRank cs v j) ∧
    delta cs v = 21 * varIdx cs v ∧ dBlue (occRank cs v j) ≤ 6 ∧ dRed (occRank cs v j) ≤ 6 :=
  ⟨rfl, rfl, rfl, dBlue_le _, dRed_le _⟩

/-! ### The clause gadgets -/

theorem clauseSols_zero (cs : Inst6) (j : ℕ) : clauseSols cs j 0 =
    [{(colBlue cs j (clauseVar cs j 0), 0), (colBlue cs j (clauseVar cs j 1), 7),
        (colBlue cs j (clauseVar cs j 2), 14)},
      {(colRed cs j (clauseVar cs j 1), 0), (colRed cs j (clauseVar cs j 0), 7)},
      {(colRed cs j (clauseVar cs j 2), 0), (colRed cs j (clauseVar cs j 1), 14)}] := rfl

theorem clauseSols_one (cs : Inst6) (j : ℕ) : clauseSols cs j 1 =
    [{(colBlue cs j (clauseVar cs j 1), 0), (colBlue cs j (clauseVar cs j 0), 7),
        (colBlue cs j (clauseVar cs j 2), 14)},
      {(colRed cs j (clauseVar cs j 0), 0), (colRed cs j (clauseVar cs j 1), 7)},
      {(colRed cs j (clauseVar cs j 2), 0), (colRed cs j (clauseVar cs j 1), 14)}] := rfl

theorem clauseSols_two (cs : Inst6) (j : ℕ) : clauseSols cs j 2 =
    [{(colBlue cs j (clauseVar cs j 2), 0), (colBlue cs j (clauseVar cs j 0), 7),
        (colBlue cs j (clauseVar cs j 1), 14)},
      {(colRed cs j (clauseVar cs j 0), 0), (colRed cs j (clauseVar cs j 1), 7)},
      {(colRed cs j (clauseVar cs j 1), 0), (colRed cs j (clauseVar cs j 2), 14)}] := rfl

theorem clauseSols_eq (cs : Inst6) (j t : ℕ) : clauseSols cs j t =
    [(clauseSols cs j t).getD 0 ∅, (clauseSols cs j t).getD 1 ∅,
      (clauseSols cs j t).getD 2 ∅] := by
  match t with
  | 0 => rfl
  | 1 => rfl
  | t + 2 => rfl

/-- The three listed solutions of `G¹_c, G²_c, G³_c` are solutions. -/
theorem clauseSols_sol (cs : Inst6) (hcs : Inst6Valid cs) (j : ℕ) (hj : j < cs.length) (t : ℕ)
    (ht : t < 3) :
    (G1 cs j).IsSol ((clauseSols cs j t).getD 0 ∅) ∧
    (G2 cs j).IsSol ((clauseSols cs j t).getD 1 ∅) ∧
    (G3 cs j).IsSol ((clauseSols cs j t).getD 2 ∅) := by
  have hx := clause_arith cs hcs j hj
  have fi := cols_facts cs j (clauseVar cs j 0)
  have fj := cols_facts cs j (clauseVar cs j 1)
  have fk := cols_facts cs j (clauseVar cs j 2)
  have hC1 : (G1 cs j).C.card = 3 :=
    Finset.card_eq_three.mpr ⟨_, _, _, by omega, by omega, by omega, rfl⟩
  have hC2 : (G2 cs j).C.card = 2 := Finset.card_pair (by omega)
  have hC3 : (G3 cs j).C.card = 2 := Finset.card_pair (by omega)
  rcases (by omega : t = 0 ∨ t = 1 ∨ t = 2) with rfl | rfl | rfl
  all_goals
    simp only [clauseSols_zero, clauseSols_one, clauseSols_two, List.getD_cons_zero,
      List.getD_cons_succ]
    exact ⟨sol3_of _ rfl _ _ _ hC1 (by ((refine ⟨?_, ?_, ?_, ?_⟩ <;> dsimp only <;> (try push_cast) <;> omega))) (by ((refine ⟨?_, ?_, ?_, ?_⟩ <;> dsimp only <;> (try push_cast) <;> omega))) (by ((refine ⟨?_, ?_, ?_, ?_⟩ <;> dsimp only <;> (try push_cast) <;> omega))) (by ((simp [G1, G2, G3])))
        (by ((simp [G1, G2, G3]))) (by ((simp [G1, G2, G3]))) (by (((simp only [G1, G2, G3, diffDiag, Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty, not_false_eq_true]) <;> (try push_cast) <;> omega))) (by (((simp only [G1, G2, G3, diffDiag, Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty, not_false_eq_true]) <;> (try push_cast) <;> omega))) (by (((simp only [G1, G2, G3, diffDiag, Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty, not_false_eq_true]) <;> (try push_cast) <;> omega))),
      sol2_of _ rfl _ _ hC2 (by ((refine ⟨?_, ?_, ?_, ?_⟩ <;> dsimp only <;> (try push_cast) <;> omega))) (by ((simp [G1, G2, G3]))) (by ((simp [G1, G2, G3]))) (by (((simp only [G1, G2, G3, diffDiag, Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty, not_false_eq_true]) <;> (try push_cast) <;> omega))) (by (((simp only [G1, G2, G3, diffDiag, Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty, not_false_eq_true]) <;> (try push_cast) <;> omega))),
      sol2_of _ rfl _ _ hC3 (by ((refine ⟨?_, ?_, ?_, ?_⟩ <;> dsimp only <;> (try push_cast) <;> omega))) (by ((simp [G1, G2, G3]))) (by ((simp [G1, G2, G3]))) (by (((simp only [G1, G2, G3, diffDiag, Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty, not_false_eq_true]) <;> (try push_cast) <;> omega))) (by (((simp only [G1, G2, G3, diffDiag, Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty, not_false_eq_true]) <;> (try push_cast) <;> omega)))⟩

/-- The combinatorial core of Lemma 33. -/
theorem core_logic (ci cj ck : Bool) (r1 r2 r3 s1 s2 u1 u2 : ℕ)
    (hr : (r1 = 0 ∧ r2 = 7 ∧ r3 = 14) ∨ (r1 = 7 ∧ r2 = 0 ∧ r3 = 14) ∨
      (r1 = 7 ∧ r2 = 14 ∧ r3 = 0))
    (hs : (s1 = 0 ∧ s2 = 7) ∨ (s1 = 7 ∧ s2 = 0))
    (hu : (u1 = 0 ∧ u2 = 14) ∨ (u1 = 14 ∧ u2 = 0))
    (e1 : r1 = 0 → ci = true) (e2 : r2 = 0 → cj = true) (e3 : r3 = 0 → ck = true)
    (e4 : s1 = 0 → ci = false) (e5 : s2 = 0 → cj = false)
    (e6 : u1 = 0 → cj = false) (e7 : u2 = 0 → ck = false) (e8 : ¬ (s2 = 0 ∧ u1 = 0)) :
    (ci = true ∧ cj = false ∧ ck = false ∧ r1 = 0 ∧ r2 = 7 ∧ r3 = 14 ∧ s1 = 7 ∧ s2 = 0 ∧
        u1 = 14 ∧ u2 = 0) ∨
      (ci = false ∧ cj = true ∧ ck = false ∧ r1 = 7 ∧ r2 = 0 ∧ r3 = 14 ∧ s1 = 0 ∧ s2 = 7 ∧
        u1 = 14 ∧ u2 = 0) ∨
      (ci = false ∧ cj = false ∧ ck = true ∧ r1 = 7 ∧ r2 = 14 ∧ r3 = 0 ∧ s1 = 0 ∧ s2 = 7 ∧
        u1 = 0 ∧ u2 = 14) := by
  rcases hr with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
    rcases hs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases hu with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    cases ci <;> cases cj <;> cases ck <;>
    first
    | exact Or.inl ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    | exact Or.inr (Or.inl ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩)
    | exact Or.inr (Or.inr ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩)
    | exact absurd (e1 rfl) (by decide)
    | exact absurd (e2 rfl) (by decide)
    | exact absurd (e3 rfl) (by decide)
    | exact absurd (e4 rfl) (by decide)
    | exact absurd (e5 rfl) (by decide)
    | exact absurd (e6 rfl) (by decide)
    | exact absurd (e7 rfl) (by decide)
    | exact absurd ⟨rfl, rfl⟩ e8

/-- Once the colours of the three variable gadgets are fixed, the solutions of the three clause
gadgets are forced, and exactly one variable is red. -/
theorem clause_unique (cs : Inst6) (hcs : Inst6Valid cs) (j : ℕ) (hj : j < cs.length)
    (ci cj ck : Bool) (S1 S2 S3 : Finset Queen)
    (h1 : (G1 cs j).IsSol S1) (h2 : (G2 cs j).IsSol S2) (h3 : (G3 cs j).IsSol S3)
    (d1i : SumDisj S1 (colorSol ci (delta cs (clauseVar cs j 0))))
    (d1j : SumDisj S1 (colorSol cj (delta cs (clauseVar cs j 1))))
    (d1k : SumDisj S1 (colorSol ck (delta cs (clauseVar cs j 2))))
    (d2i : SumDisj S2 (colorSol ci (delta cs (clauseVar cs j 0))))
    (d2j : SumDisj S2 (colorSol cj (delta cs (clauseVar cs j 1))))
    (d3j : SumDisj S3 (colorSol cj (delta cs (clauseVar cs j 1))))
    (d3k : SumDisj S3 (colorSol ck (delta cs (clauseVar cs j 2))))
    (d23 : SumDisj S2 S3) :
    ∃ t, t < 3 ∧ ci = decide (t = 0) ∧ cj = decide (t = 1) ∧ ck = decide (t = 2) ∧
      [S1, S2, S3] = clauseSols cs j t := by
  have hx := clause_arith cs hcs j hj
  have fi := cols_facts cs j (clauseVar cs j 0)
  have fj := cols_facts cs j (clauseVar cs j 1)
  have fk := cols_facts cs j (clauseVar cs j 2)
  obtain ⟨r1, r2, r3, hr, rfl⟩ := g3_struct (G1 cs j) _ _ _ rfl rfl rfl rfl
    (by omega) (by omega) (by omega) S1 h1
  obtain ⟨s1, s2, hs, rfl⟩ := g2_struct (G2 cs j) _ _ 7 (by norm_num) rfl rfl rfl
    (by omega) S2 h2
  obtain ⟨u1, u2, hu, rfl⟩ := g2_struct (G3 cs j) _ _ 14 (by norm_num) rfl rfl rfl
    (by omega) S3 h3
  have e1 : r1 = 0 → ci = true := by
    rintro rfl
    cases ci
    · exact (hit_blue (δ := delta cs (clauseVar cs j 0)) (r := occRank cs (clauseVar cs j 0) j)
        (c := colBlue cs j (clauseVar cs j 0)) d1i rfl (by simp)).elim
    · rfl
  have e2 : r2 = 0 → cj = true := by
    rintro rfl
    cases cj
    · exact (hit_blue (δ := delta cs (clauseVar cs j 1)) (r := occRank cs (clauseVar cs j 1) j)
        (c := colBlue cs j (clauseVar cs j 1)) d1j rfl (by simp)).elim
    · rfl
  have e3 : r3 = 0 → ck = true := by
    rintro rfl
    cases ck
    · exact (hit_blue (δ := delta cs (clauseVar cs j 2)) (r := occRank cs (clauseVar cs j 2) j)
        (c := colBlue cs j (clauseVar cs j 2)) d1k rfl (by simp)).elim
    · rfl
  have e4 : s1 = 0 → ci = false := by
    rintro rfl
    cases ci
    · rfl
    · exact (hit_red (δ := delta cs (clauseVar cs j 0)) (r := occRank cs (clauseVar cs j 0) j)
        (c := colRed cs j (clauseVar cs j 0)) d2i rfl (by simp)).elim
  have e5 : s2 = 0 → cj = false := by
    rintro rfl
    cases cj
    · rfl
    · exact (hit_red (δ := delta cs (clauseVar cs j 1)) (r := occRank cs (clauseVar cs j 1) j)
        (c := colRed cs j (clauseVar cs j 1)) d2j rfl (by simp)).elim
  have e6 : u1 = 0 → cj = false := by
    rintro rfl
    cases cj
    · rfl
    · exact (hit_red (δ := delta cs (clauseVar cs j 1)) (r := occRank cs (clauseVar cs j 1) j)
        (c := colRed cs j (clauseVar cs j 1)) d3j rfl (by simp)).elim
  have e7 : u2 = 0 → ck = false := by
    rintro rfl
    cases ck
    · rfl
    · exact (hit_red (δ := delta cs (clauseVar cs j 2)) (r := occRank cs (clauseVar cs j 2) j)
        (c := colRed cs j (clauseVar cs j 2)) d3k rfl (by simp)).elim
  have e8 : ¬ (s2 = 0 ∧ u1 = 0) := by
    rintro ⟨rfl, rfl⟩
    exact d23 (colRed cs j (clauseVar cs j 1), 0) (by simp) (colRed cs j (clauseVar cs j 1), 0)
      (by simp) rfl
  rcases core_logic ci cj ck r1 r2 r3 s1 s2 u1 u2 hr hs hu e1 e2 e3 e4 e5 e6 e7 e8 with
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · refine ⟨0, by norm_num, rfl, rfl, rfl, ?_⟩
    rw [clauseSols_zero, Finset.pair_comm (colRed cs j (clauseVar cs j 0), 7),
      Finset.pair_comm (colRed cs j (clauseVar cs j 1), 14)]
  · refine ⟨1, by norm_num, rfl, rfl, rfl, ?_⟩
    rw [clauseSols_one, Finset.insert_comm (colBlue cs j (clauseVar cs j 0), 7),
      Finset.pair_comm (colRed cs j (clauseVar cs j 1), 14)]
  · refine ⟨2, by norm_num, rfl, rfl, rfl, ?_⟩
    rw [clauseSols_two, Finset.pair_comm (colBlue cs j (clauseVar cs j 1), 14),
      Finset.insert_comm (colBlue cs j (clauseVar cs j 0), 7)]

/-! ### Sum-diagonal signatures -/

theorem varIdx_inj (cs : Inst6) {u v : ℕ} (hu : u ∈ vars cs) (hv : v ∈ vars cs)
    (h : varIdx cs u = varIdx cs v) : u = v := by
  rcases lt_trichotomy u v with huv | huv | huv
  · exact absurd h (varIdx_lt cs hu huv).ne
  · exact huv
  · exact absurd h (varIdx_lt cs hv huv).ne'

theorem getD_mem_vars (cs : Inst6) (j : ℕ) (hj : j < cs.length) (v : ℕ)
    (hv : v ∈ cs.getD j ∅) : v ∈ vars cs := by
  rw [List.getD_eq_getElem _ _ hj] at hv
  exact mem_vars_of cs j hj v hv

/-- A queen of the variable gadget of `v`: its sum-diagonal is `21 i + d` with `d ∈ {0, 4, 5}` if
`v ∈ T` (red) and `d ∈ {1, 2, 6}` otherwise (blue). -/
def DescV (cs : Inst6) (T : Finset ℕ) (v : ℕ) (q : Queen) : Prop :=
  ∃ d, sumDiag q = 21 * varIdx cs v + d ∧ (v ∈ T → d = 0 ∨ d = 4 ∨ d = 5) ∧
    (v ∉ T → d = 1 ∨ d = 2 ∨ d = 6)

/-- A queen of `G¹_c` (`c = c_j`): it sits in a blue column, on row `0` only for a true variable. -/
def DescB (cs : Inst6) (T : Finset ℕ) (j : ℕ) (q : Queen) : Prop :=
  ∃ v ∈ cs.getD j ∅, ∃ α, α ≤ 2 ∧ q = (colBlue cs j v, 7 * α) ∧ (α = 0 → v ∈ T)

/-- A queen of `G²_c` or `G³_c`: it sits in a red column, on row `0` only for a false variable. -/
def DescR (cs : Inst6) (T : Finset ℕ) (j : ℕ) (q : Queen) : Prop :=
  ∃ v ∈ cs.getD j ∅, ∃ α, α ≤ 2 ∧ q = (colRed cs j v, 7 * α) ∧ (α = 0 → v ∉ T)

theorem descV_of (cs : Inst6) (T : Finset ℕ) (v : ℕ) (q : Queen)
    (hq : q ∈ (if v ∈ T then redSol (delta cs v) else blueSol (delta cs v))) :
    DescV cs T v q := by
  have hδ : delta cs v = 21 * varIdx cs v := rfl
  by_cases hv : v ∈ T
  · rw [if_pos hv, red_eq] at hq
    simp only [Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with rfl | rfl | rfl
    · exact ⟨0, by simp only [sumDiag]; try omega, fun _ => Or.inl rfl, fun h => absurd hv h⟩
    · exact ⟨4, by simp only [sumDiag]; try omega, fun _ => Or.inr (Or.inl rfl),
        fun h => absurd hv h⟩
    · exact ⟨5, by simp only [sumDiag]; try omega, fun _ => Or.inr (Or.inr rfl),
        fun h => absurd hv h⟩
  · rw [if_neg hv, blue_eq] at hq
    simp only [Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with rfl | rfl | rfl
    · exact ⟨2, by simp only [sumDiag]; try omega, fun h => absurd h hv,
        fun _ => Or.inr (Or.inl rfl)⟩
    · exact ⟨1, by simp only [sumDiag]; try omega, fun h => absurd h hv, fun _ => Or.inl rfl⟩
    · exact ⟨6, by simp only [sumDiag]; try omega, fun h => absurd h hv,
        fun _ => Or.inr (Or.inr rfl)⟩

theorem VV (cs : Inst6) (T : Finset ℕ) (v v' : ℕ) (q q' : Queen) (h : DescV cs T v q)
    (h' : DescV cs T v' q') (heq : sumDiag q = sumDiag q') : varIdx cs v = varIdx cs v' := by
  obtain ⟨d, h1, h2, h3⟩ := h
  obtain ⟨d', h1', h2', h3'⟩ := h'
  have hd : d ≤ 6 := by
    by_cases hv : v ∈ T
    · rcases h2 hv with h | h | h <;> omega
    · rcases h3 hv with h | h | h <;> omega
  have hd' : d' ≤ 6 := by
    by_cases hv : v' ∈ T
    · rcases h2' hv with h | h | h <;> omega
    · rcases h3' hv with h | h | h <;> omega
  omega

theorem VB (cs : Inst6) (T : Finset ℕ) (v j : ℕ) (q q' : Queen) (hv : v ∈ vars cs)
    (hj : j < cs.length) (h : DescV cs T v q) (h' : DescB cs T j q')
    (heq : sumDiag q = sumDiag q') : False := by
  obtain ⟨d, h1, h2, h3⟩ := h
  obtain ⟨v', hv', α, hα, rfl, h5⟩ := h'
  have f := cols_facts cs j v'
  have hb := dBlue_cases (occRank cs v' j)
  rw [h1] at heq
  simp only [sumDiag] at heq
  by_cases hvT : v ∈ T
  · have hd := h2 hvT
    omega
  · have hd := h3 hvT
    have hx1 : varIdx cs v = varIdx cs v' := by omega
    have hx2 : α = 0 := by omega
    have hvv := varIdx_inj cs hv (getD_mem_vars cs j hj v' hv') hx1
    subst hvv
    exact hvT (h5 hx2)

theorem VR (cs : Inst6) (T : Finset ℕ) (v j : ℕ) (q q' : Queen) (hv : v ∈ vars cs)
    (hj : j < cs.length) (h : DescV cs T v q) (h' : DescR cs T j q')
    (heq : sumDiag q = sumDiag q') : False := by
  obtain ⟨d, h1, h2, h3⟩ := h
  obtain ⟨v', hv', α, hα, rfl, h5⟩ := h'
  have f := cols_facts cs j v'
  have hr := dRed_cases (occRank cs v' j)
  rw [h1] at heq
  simp only [sumDiag] at heq
  by_cases hvT : v ∈ T
  · have hd := h2 hvT
    have hx1 : varIdx cs v = varIdx cs v' := by omega
    have hx2 : α = 0 := by omega
    have hvv := varIdx_inj cs hv (getD_mem_vars cs j hj v' hv') hx1
    subst hvv
    exact h5 hx2 hvT
  · have hd := h3 hvT
    omega

theorem BR (cs : Inst6) (T : Finset ℕ) (j j' : ℕ) (q q' : Queen) (h : DescB cs T j q)
    (h' : DescR cs T j' q') (heq : sumDiag q = sumDiag q') : False := by
  obtain ⟨v, -, α, hα, rfl, -⟩ := h
  obtain ⟨v', -, α', hα', rfl, -⟩ := h'
  have f := cols_facts cs j v
  have f' := cols_facts cs j' v'
  have hb := dBlue_cases (occRank cs v j)
  have hr := dRed_cases (occRank cs v' j')
  simp only [sumDiag] at heq
  omega



/-- The queens of the listed solutions of `G¹_c, G²_c, G³_c` when the `t`-th variable is the
true one. -/
theorem desc_clause (cs : Inst6) (hcs : Inst6Valid cs) (T : Finset ℕ) (j : ℕ)
    (hj : j < cs.length) (t : ℕ) (ht : t < 3) (h0 : clauseVar cs j 0 ∈ T ↔ t = 0)
    (h1 : clauseVar cs j 1 ∈ T ↔ t = 1) (h2 : clauseVar cs j 2 ∈ T ↔ t = 2) (s : ℕ)
    (hs : s < 3) (q : Queen) (hq : q ∈ (clauseSols cs j t).getD s ∅) :
    (s = 0 → DescB cs T j q) ∧ (s ≠ 0 → DescR cs T j q) := by
  obtain ⟨-, -, hc⟩ := clause_facts cs hcs j hj
  have hg : cs.getD j ∅ = {clauseVar cs j 0, clauseVar cs j 1, clauseVar cs j 2} := by
    rw [List.getD_eq_getElem _ _ hj]
    exact hc
  have mi : clauseVar cs j 0 ∈ cs.getD j ∅ := by rw [hg]; simp
  have mj : clauseVar cs j 1 ∈ cs.getD j ∅ := by rw [hg]; simp
  have mk : clauseVar cs j 2 ∈ cs.getD j ∅ := by rw [hg]; simp
  rcases (by omega : t = 0 ∨ t = 1 ∨ t = 2) with rfl | rfl | rfl <;>
    simp at h0 h1 h2 <;>
    rcases (by omega : s = 0 ∨ s = 1 ∨ s = 2) with rfl | rfl | rfl <;>
    simp only [clauseSols_zero, clauseSols_one, clauseSols_two, List.getD_cons_zero,
      List.getD_cons_succ, Finset.mem_insert, Finset.mem_singleton] at hq
  · refine ⟨fun _ => ?_, fun h => absurd rfl h⟩
    rcases hq with rfl | rfl | rfl <;> (first | exact ⟨_, by assumption, 0, by norm_num, rfl, fun _ => by assumption⟩ | exact ⟨_, by assumption, 1, by norm_num, rfl, fun h => absurd h (by norm_num)⟩ | exact ⟨_, by assumption, 2, by norm_num, rfl, fun h => absurd h (by norm_num)⟩)
  · refine ⟨fun h => absurd h one_ne_zero, fun _ => ?_⟩
    rcases hq with rfl | rfl <;> (first | exact ⟨_, by assumption, 0, by norm_num, rfl, fun _ => by assumption⟩ | exact ⟨_, by assumption, 1, by norm_num, rfl, fun h => absurd h (by norm_num)⟩ | exact ⟨_, by assumption, 2, by norm_num, rfl, fun h => absurd h (by norm_num)⟩)
  · refine ⟨fun h => absurd h two_ne_zero, fun _ => ?_⟩
    rcases hq with rfl | rfl <;> (first | exact ⟨_, by assumption, 0, by norm_num, rfl, fun _ => by assumption⟩ | exact ⟨_, by assumption, 1, by norm_num, rfl, fun h => absurd h (by norm_num)⟩ | exact ⟨_, by assumption, 2, by norm_num, rfl, fun h => absurd h (by norm_num)⟩)
  · refine ⟨fun _ => ?_, fun h => absurd rfl h⟩
    rcases hq with rfl | rfl | rfl <;> (first | exact ⟨_, by assumption, 0, by norm_num, rfl, fun _ => by assumption⟩ | exact ⟨_, by assumption, 1, by norm_num, rfl, fun h => absurd h (by norm_num)⟩ | exact ⟨_, by assumption, 2, by norm_num, rfl, fun h => absurd h (by norm_num)⟩)
  · refine ⟨fun h => absurd h one_ne_zero, fun _ => ?_⟩
    rcases hq with rfl | rfl <;> (first | exact ⟨_, by assumption, 0, by norm_num, rfl, fun _ => by assumption⟩ | exact ⟨_, by assumption, 1, by norm_num, rfl, fun h => absurd h (by norm_num)⟩ | exact ⟨_, by assumption, 2, by norm_num, rfl, fun h => absurd h (by norm_num)⟩)
  · refine ⟨fun h => absurd h two_ne_zero, fun _ => ?_⟩
    rcases hq with rfl | rfl <;> (first | exact ⟨_, by assumption, 0, by norm_num, rfl, fun _ => by assumption⟩ | exact ⟨_, by assumption, 1, by norm_num, rfl, fun h => absurd h (by norm_num)⟩ | exact ⟨_, by assumption, 2, by norm_num, rfl, fun h => absurd h (by norm_num)⟩)
  · refine ⟨fun _ => ?_, fun h => absurd rfl h⟩
    rcases hq with rfl | rfl | rfl <;> (first | exact ⟨_, by assumption, 0, by norm_num, rfl, fun _ => by assumption⟩ | exact ⟨_, by assumption, 1, by norm_num, rfl, fun h => absurd h (by norm_num)⟩ | exact ⟨_, by assumption, 2, by norm_num, rfl, fun h => absurd h (by norm_num)⟩)
  · refine ⟨fun h => absurd h one_ne_zero, fun _ => ?_⟩
    rcases hq with rfl | rfl <;> (first | exact ⟨_, by assumption, 0, by norm_num, rfl, fun _ => by assumption⟩ | exact ⟨_, by assumption, 1, by norm_num, rfl, fun h => absurd h (by norm_num)⟩ | exact ⟨_, by assumption, 2, by norm_num, rfl, fun h => absurd h (by norm_num)⟩)
  · refine ⟨fun h => absurd h two_ne_zero, fun _ => ?_⟩
    rcases hq with rfl | rfl <;> (first | exact ⟨_, by assumption, 0, by norm_num, rfl, fun _ => by assumption⟩ | exact ⟨_, by assumption, 1, by norm_num, rfl, fun h => absurd h (by norm_num)⟩ | exact ⟨_, by assumption, 2, by norm_num, rfl, fun h => absurd h (by norm_num)⟩)

/-- Inside one clause, `G²_c` and `G³_c` use different sum-diagonals. -/
theorem clause23_disj (cs : Inst6) (hcs : Inst6Valid cs) (j : ℕ) (hj : j < cs.length) (t : ℕ)
    (ht : t < 3) :
    SumDisj ((clauseSols cs j t).getD 1 ∅) ((clauseSols cs j t).getD 2 ∅) := by
  have hx := clause_arith cs hcs j hj
  have fi := cols_facts cs j (clauseVar cs j 0)
  have fj := cols_facts cs j (clauseVar cs j 1)
  have fk := cols_facts cs j (clauseVar cs j 2)
  rcases (by omega : t = 0 ∨ t = 1 ∨ t = 2) with rfl | rfl | rfl <;>
    simp only [clauseSols_zero, clauseSols_one, clauseSols_two, List.getD_cons_zero,
      List.getD_cons_succ, SumDisj, Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp,
      forall_eq, sumDiag] <;>
    omega

theorem colorSol_eq_if {b : Bool} {P : Prop} [Decidable P] (δ : ℕ) (h : P ↔ b = true) :
    colorSol b δ = if P then redSol δ else blueSol δ := by
  by_cases hP : P
  · rw [if_pos hP, h.mp hP]
    rfl
  · have hb : b = false := by
      cases b
      · rfl
      · exact absurd (h.mpr rfl) hP
    rw [if_neg hP, hb]
    rfl

/-! ### Positions in `def31 cs` and `lemma34_map cs T` -/

theorem varIdx_lt_card (cs : Inst6) {v : ℕ} (hv : v ∈ vars cs) :
    varIdx cs v < (vars cs).card := by
  unfold varIdx
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset (Finset.filter_subset _ _)]
  exact ⟨v, hv, by simp⟩

theorem sorted_filter_card (L : List ℕ) : L.Pairwise (· < ·) → ∀ (a : ℕ) (ha : a < L.length),
    (L.toFinset.filter (· < L[a])).card = a := by
  induction L with
  | nil =>
    intro _ a ha
    simp at ha
  | cons x L ih =>
    intro hL a ha
    rw [List.pairwise_cons] at hL
    obtain ⟨hx, hL⟩ := hL
    cases a with
    | zero =>
      simp only [List.getElem_cons_zero]
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro y hy
      rw [List.mem_toFinset, List.mem_cons] at hy
      rcases hy with rfl | hy
      · exact lt_irrefl _
      · exact not_lt.mpr (le_of_lt (hx y hy))
    | succ a =>
      have ha' : a < L.length := by simpa using ha
      simp only [List.getElem_cons_succ]
      have hxa : x < L[a] := hx _ (List.getElem_mem ha')
      rw [List.toFinset_cons, Finset.filter_insert, if_pos hxa, Finset.card_insert_of_notMem,
        ih hL a ha']
      simp only [Finset.mem_filter, List.mem_toFinset, not_and]
      intro hxL
      exact absurd (hx x hxL) (lt_irrefl x)

/-- The variable at position `a` of the sorted variable list has index `a`. -/
theorem varIdx_sort (cs : Inst6) (a : ℕ) (ha : a < ((vars cs).sort (· ≤ ·)).length) :
    varIdx cs (((vars cs).sort (· ≤ ·))[a]) = a := by
  have h := sorted_filter_card _ (sort_lt (vars cs)) a ha
  rw [Finset.sort_toFinset] at h
  exact h

theorem sort_get_varIdx (cs : Inst6) (v : ℕ) (hv : v ∈ vars cs) :
    ((vars cs).sort (· ≤ ·))[varIdx cs v]? = some v := by
  obtain ⟨a, ha, hav⟩ := List.mem_iff_getElem.mp ((Finset.mem_sort (· ≤ ·)).mpr hv)
  rw [← hav, varIdx_sort cs a ha]
  exact List.getElem?_eq_getElem ha

theorem idx_lt (cs : Inst6) (v : ℕ) (hv : v ∈ vars cs) :
    varIdx cs v < ((vars cs).sort (· ≤ ·)).length := by
  rw [Finset.length_sort]
  exact varIdx_lt_card cs hv

theorem flat_len {α : Type} (g : ℕ → List α) (hg : ∀ j, (g j).length = 3) (m : ℕ) :
    ((List.range m).flatMap g).length = 3 * m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [List.range_succ, List.flatMap_append, List.length_append, ih, List.flatMap_cons,
      List.flatMap_nil, List.append_nil, hg]
    ring

theorem flat_get {α : Type} (g : ℕ → List α) (hg : ∀ j, (g j).length = 3) (m : ℕ) :
    ∀ j s, j < m → s < 3 → ((List.range m).flatMap g)[3 * j + s]? = (g j)[s]? := by
  induction m with
  | zero =>
    intro j s hj
    exact absurd hj (Nat.not_lt_zero j)
  | succ m ih =>
    intro j s hj hs
    rw [List.range_succ, List.flatMap_append]
    rcases Nat.lt_or_ge j m with h | h
    · rw [List.getElem?_append_left (by rw [flat_len g hg m]; omega), ih j s h hs]
    · obtain rfl : j = m := by omega
      rw [List.getElem?_append_right (by rw [flat_len g hg]; omega), flat_len g hg,
        List.flatMap_cons, List.flatMap_nil, List.append_nil, Nat.add_sub_cancel_left]

/-- The position of the `s`-th clause gadget of `c_j` in `def31 cs`. -/
def slot (cs : Inst6) (j s : ℕ) : ℕ := ((vars cs).sort (· ≤ ·)).length + (3 * j + s)

theorem clauseSols_len (cs : Inst6) (j t : ℕ) : (clauseSols cs j t).length = 3 := by
  rw [clauseSols_eq]
  rfl

theorem def31_len (cs : Inst6) :
    (def31 cs).length = ((vars cs).sort (· ≤ ·)).length + 3 * cs.length := by
  unfold def31
  rw [List.length_append, List.length_map, flat_len _ (fun _ => rfl)]

theorem l34_len (cs : Inst6) (T : Finset ℕ) :
    (lemma34_map cs T).length = ((vars cs).sort (· ≤ ·)).length + 3 * cs.length := by
  unfold lemma34_map
  rw [List.length_append, List.length_map, flat_len _ (fun j => clauseSols_len cs j _)]

theorem def31_get_v (cs : Inst6) (v : ℕ) (hv : v ∈ vars cs) :
    (def31 cs)[varIdx cs v]? = some (G0v cs v) := by
  unfold def31
  rw [List.getElem?_append_left (by rw [List.length_map]; exact idx_lt cs v hv),
    List.getElem?_map, sort_get_varIdx cs v hv]
  rfl

theorem def31_get_c (cs : Inst6) (j s : ℕ) (hj : j < cs.length) (hs : s < 3) :
    (def31 cs)[slot cs j s]? = [G1 cs j, G2 cs j, G3 cs j][s]? := by
  unfold def31 slot
  rw [List.getElem?_append_right (by rw [List.length_map]; omega), List.length_map,
    Nat.add_sub_cancel_left, flat_get _ (fun _ => rfl) _ j s hj hs]

theorem l34_get_v (cs : Inst6) (T : Finset ℕ) (v : ℕ) (hv : v ∈ vars cs) :
    (lemma34_map cs T)[varIdx cs v]? =
      some (if v ∈ T then redSol (delta cs v) else blueSol (delta cs v)) := by
  unfold lemma34_map
  rw [List.getElem?_append_left (by rw [List.length_map]; exact idx_lt cs v hv),
    List.getElem?_map, sort_get_varIdx cs v hv]
  rfl

theorem l34_get_c (cs : Inst6) (T : Finset ℕ) (j s : ℕ) (hj : j < cs.length) (hs : s < 3) :
    (lemma34_map cs T)[slot cs j s]? = (clauseSols cs j (truePos cs j T))[s]? := by
  unfold lemma34_map slot
  rw [List.getElem?_append_right (by rw [List.length_map]; omega), List.length_map,
    Nat.add_sub_cancel_left, flat_get _ (fun j => clauseSols_len cs j _) _ j s hj hs]

theorem getD_of_some {l : List (Finset Queen)} {i : ℕ} {x : Finset Queen} (h : l[i]? = some x) :
    l.getD i ∅ = x := by
  rw [List.getD_eq_getElem?_getD, h]
  rfl

theorem getD_congr {l l' : List (Finset Queen)} {i i' : ℕ} (h : l[i]? = l'[i']?) :
    l.getD i ∅ = l'.getD i' ∅ := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, h]

theorem f2_get {Ms : List Inst4} {Ss : List (Finset Queen)}
    (h : List.Forall₂ (fun (M : Inst4) (S : Finset Queen) => M.IsSol S) Ms Ss) {a : ℕ}
    {M : Inst4} (hM : Ms[a]? = some M) : M.IsSol (Ss.getD a ∅) := by
  rw [List.forall₂_iff_get] at h
  obtain ⟨hlen, hR⟩ := h
  obtain ⟨ha, rfl⟩ := List.getElem?_eq_some_iff.mp hM
  have ha' : a < Ss.length := hlen ▸ ha
  rw [List.getD_eq_getElem _ _ ha']
  exact hR a ha ha'

theorem f2_of {Ms : List Inst4} {Ss : List (Finset Queen)} (hlen : Ms.length = Ss.length)
    (h : ∀ (a : ℕ) (M : Inst4) (S : Finset Queen), Ms[a]? = some M → Ss[a]? = some S →
      M.IsSol S) :
    List.Forall₂ (fun (M : Inst4) (S : Finset Queen) => M.IsSol S) Ms Ss := by
  rw [List.forall₂_iff_get]
  exact ⟨hlen, fun i h1 h2 =>
    h i _ _ (List.getElem?_eq_getElem h1) (List.getElem?_eq_getElem h2)⟩

theorem idx_cases (cs : Inst6) (a : ℕ)
    (ha : a < ((vars cs).sort (· ≤ ·)).length + 3 * cs.length) :
    (∃ v ∈ vars cs, a = varIdx cs v) ∨ (∃ j s, j < cs.length ∧ s < 3 ∧ a = slot cs j s) := by
  by_cases h : a < ((vars cs).sort (· ≤ ·)).length
  · left
    exact ⟨_, (Finset.mem_sort (· ≤ ·)).mp (List.getElem_mem h), (varIdx_sort cs a h).symm⟩
  · right
    refine ⟨(a - ((vars cs).sort (· ≤ ·)).length) / 3,
      (a - ((vars cs).sort (· ≤ ·)).length) % 3, by omega, by omega, ?_⟩
    unfold slot
    omega

/-! ### Exactly one true variable per clause -/

theorem card_inter_one {x y z : ℕ} {T : Finset ℕ}
    (h : (x ∈ T ∧ y ∉ T ∧ z ∉ T) ∨ (x ∉ T ∧ y ∈ T ∧ z ∉ T) ∨ (x ∉ T ∧ y ∉ T ∧ z ∈ T)) :
    (({x, y, z} : Finset ℕ) ∩ T).card = 1 := by
  rw [Finset.card_eq_one]
  rcases h with ⟨hx, hy, hz⟩ | ⟨hx, hy, hz⟩ | ⟨hx, hy, hz⟩
  · refine ⟨x, ?_⟩
    ext w
    simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨rfl | rfl | rfl, hw⟩
      · rfl
      · exact absurd hw hy
      · exact absurd hw hz
    · rintro rfl
      exact ⟨Or.inl rfl, hx⟩
  · refine ⟨y, ?_⟩
    ext w
    simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨rfl | rfl | rfl, hw⟩
      · exact absurd hw hx
      · rfl
      · exact absurd hw hz
    · rintro rfl
      exact ⟨Or.inr (Or.inl rfl), hy⟩
  · refine ⟨z, ?_⟩
    ext w
    simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨rfl | rfl | rfl, hw⟩
      · exact absurd hw hx
      · exact absurd hw hy
      · rfl
    · rintro rfl
      exact ⟨Or.inr (Or.inr rfl), hz⟩

theorem one_of_card_inter {x y z : ℕ} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    {T : Finset ℕ} (h : (({x, y, z} : Finset ℕ) ∩ T).card = 1) :
    (x ∈ T ∧ y ∉ T ∧ z ∉ T) ∨ (x ∉ T ∧ y ∈ T ∧ z ∉ T) ∨ (x ∉ T ∧ y ∉ T ∧ z ∈ T) := by
  obtain ⟨w, hw⟩ := Finset.card_eq_one.mp h
  have hm : ∀ u, u ∈ ({x, y, z} : Finset ℕ) ∩ T ↔ u = w := fun u => by
    rw [hw, Finset.mem_singleton]
  have ex := hm x
  have ey := hm y
  have ez := hm z
  have ew := (hm w).mpr rfl
  simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton, true_or, or_true,
    true_and] at ex ey ez ew
  obtain ⟨hw1 | hw1 | hw1, hw2⟩ := ew <;> subst hw1
  · exact Or.inl ⟨hw2, fun h => hxy (ey.mp h).symm, fun h => hxz (ez.mp h).symm⟩
  · exact Or.inr (Or.inl ⟨fun h => hxy (ex.mp h), hw2, fun h => hyz (ez.mp h).symm⟩)
  · exact Or.inr (Or.inr ⟨fun h => hxz (ex.mp h), fun h => hyz (ey.mp h), hw2⟩)

theorem truePos_lt (cs : Inst6) (j : ℕ) (T : Finset ℕ) : truePos cs j T < 3 := by
  unfold truePos
  split_ifs <;> norm_num

theorem truePos_of (cs : Inst6) (j : ℕ) (T : Finset ℕ) (t : ℕ) (ht : t < 3)
    (h0 : clauseVar cs j 0 ∈ T ↔ t = 0) (h1 : clauseVar cs j 1 ∈ T ↔ t = 1) :
    truePos cs j T = t := by
  unfold truePos
  rcases (by omega : t = 0 ∨ t = 1 ∨ t = 2) with rfl | rfl | rfl
  · rw [if_pos (h0.mpr rfl)]
  · rw [if_neg (fun h => absurd (h0.mp h) one_ne_zero), if_pos (h1.mpr rfl)]
  · rw [if_neg (fun h => absurd (h0.mp h) two_ne_zero),
      if_neg (fun h => absurd (h1.mp h) (by norm_num))]

/-- Under a solution `T` of `M₆`, the true variable of `c_j` sits at position `truePos`. -/
theorem truePos_spec (cs : Inst6) (hcs : Inst6Valid cs) (T : Finset ℕ) (hT : Inst6IsSol cs T)
    (j : ℕ) (hj : j < cs.length) :
    (clauseVar cs j 0 ∈ T ↔ truePos cs j T = 0) ∧ (clauseVar cs j 1 ∈ T ↔ truePos cs j T = 1) ∧
      (clauseVar cs j 2 ∈ T ↔ truePos cs j T = 2) := by
  obtain ⟨h01, h12, hc⟩ := clause_facts cs hcs j hj
  have hcard := hT.2 (cs[j]) (List.getElem_mem hj)
  rw [hc] at hcard
  rcases one_of_card_inter (by omega) (by omega) (by omega) hcard with
    ⟨p0, p1, p2⟩ | ⟨p0, p1, p2⟩ | ⟨p0, p1, p2⟩
  · have ht : truePos cs j T = 0 := by simp [truePos, p0]
    rw [ht]
    simp [p0, p1, p2]
  · have ht : truePos cs j T = 1 := by simp [truePos, p0, p1]
    rw [ht]
    simp [p0, p1, p2]
  · have ht : truePos cs j T = 2 := by simp [truePos, p0, p1]
    rw [ht]
    simp [p0, p1, p2]

/-! ### Occurrence ranks -/

theorem countP_take_succ (cs : Inst6) (v j : ℕ) (hj : j < cs.length) (hv : v ∈ cs[j]) :
    (cs.take (j + 1)).countP (fun c => decide (v ∈ c)) = occRank cs v j + 1 := by
  unfold occRank
  rw [List.take_add_one, List.getElem?_eq_getElem hj, Option.toList_some, List.countP_append]
  simp [hv]

theorem countP_take_le (cs : Inst6) (v a b : ℕ) (hab : a ≤ b) :
    (cs.take a).countP (fun c => decide (v ∈ c)) ≤
      (cs.take b).countP (fun c => decide (v ∈ c)) := by
  have h : cs.take a = (cs.take b).take a := by
    rw [List.take_take]
    congr 1
    omega
  rw [h]
  exact (List.take_sublist _ _).countP_le

theorem occRank_le_two (cs : Inst6) (hcs : Inst6Valid cs) (j : ℕ) (hj : j < cs.length) (v : ℕ)
    (hv : v ∈ cs.getD j ∅) : occRank cs v j ≤ 2 := by
  rw [List.getD_eq_getElem _ _ hj] at hv
  have h1 := countP_take_succ cs v j hj hv
  have h2 := countP_take_le cs v (j + 1) cs.length (by omega)
  rw [List.take_of_length_le (le_refl _)] at h2
  have h3 := hcs.2.2 v
  unfold occurrences at h3
  omega

theorem occRank_inj (cs : Inst6) (j j' : ℕ) (hj : j < cs.length) (hj' : j' < cs.length) (v : ℕ)
    (hv : v ∈ cs.getD j ∅) (hv' : v ∈ cs.getD j' ∅) (h : occRank cs v j = occRank cs v j') :
    j = j' := by
  rw [List.getD_eq_getElem _ _ hj] at hv
  rw [List.getD_eq_getElem _ _ hj'] at hv'
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · have h1 := countP_take_succ cs v j hj hv
    have h2 := countP_take_le cs v (j + 1) j' hlt
    have h3 : occRank cs v j' = (cs.take j').countP (fun c => decide (v ∈ c)) := rfl
    omega
  · have h1 := countP_take_succ cs v j' hj' hv'
    have h2 := countP_take_le cs v (j' + 1) j hlt
    have h3 : occRank cs v j = (cs.take j).countP (fun c => decide (v ∈ c)) := rfl
    omega

theorem dBlue_inj {r r' : ℕ} (hr : r ≤ 2) (hr' : r' ≤ 2) (h : dBlue r = dBlue r') : r = r' := by
  interval_cases r <;> interval_cases r' <;> first | rfl | (revert h; decide)

theorem dRed_inj {r r' : ℕ} (hr : r ≤ 2) (hr' : r' ≤ 2) (h : dRed r = dRed r') : r = r' := by
  interval_cases r <;> interval_cases r' <;> first | rfl | (revert h; decide)

theorem BB (cs : Inst6) (hcs : Inst6Valid cs) (T : Finset ℕ) (j j' : ℕ) (q q' : Queen)
    (hj : j < cs.length) (hj' : j' < cs.length) (h : DescB cs T j q) (h' : DescB cs T j' q')
    (heq : sumDiag q = sumDiag q') : j = j' := by
  obtain ⟨v, hv, α, hα, rfl, -⟩ := h
  obtain ⟨v', hv', α', hα', rfl, -⟩ := h'
  have f := cols_facts cs j v
  have f' := cols_facts cs j' v'
  simp only [sumDiag] at heq
  have hx1 : varIdx cs v = varIdx cs v' := by omega
  have hx2 : dBlue (occRank cs v j) = dBlue (occRank cs v' j') := by omega
  have hvv := varIdx_inj cs (getD_mem_vars cs j hj v hv) (getD_mem_vars cs j' hj' v' hv') hx1
  subst hvv
  exact occRank_inj cs j j' hj hj' v hv hv'
    (dBlue_inj (occRank_le_two cs hcs j hj v hv) (occRank_le_two cs hcs j' hj' v hv') hx2)

theorem RR (cs : Inst6) (hcs : Inst6Valid cs) (T : Finset ℕ) (j j' : ℕ) (q q' : Queen)
    (hj : j < cs.length) (hj' : j' < cs.length) (h : DescR cs T j q) (h' : DescR cs T j' q')
    (heq : sumDiag q = sumDiag q') : j = j' := by
  obtain ⟨v, hv, α, hα, rfl, -⟩ := h
  obtain ⟨v', hv', α', hα', rfl, -⟩ := h'
  have f := cols_facts cs j v
  have f' := cols_facts cs j' v'
  simp only [sumDiag] at heq
  have hx1 : varIdx cs v = varIdx cs v' := by omega
  have hx2 : dRed (occRank cs v j) = dRed (occRank cs v' j') := by omega
  have hvv := varIdx_inj cs (getD_mem_vars cs j hj v hv) (getD_mem_vars cs j' hj' v' hv') hx1
  subst hvv
  exact occRank_inj cs j j' hj hj' v hv hv'
    (dRed_inj (occRank_le_two cs hcs j hj v hv) (occRank_le_two cs hcs j' hj' v hv') hx2)

/-! ### Lemma 34 -/

/-- The queens of `lemma34_map cs T` at position `a`. -/
theorem desc34 (cs : Inst6) (hcs : Inst6Valid cs) (T : Finset ℕ) (hT : Inst6IsSol cs T) (a : ℕ)
    (ha : a < (lemma34_map cs T).length) (q : Queen) (hq : q ∈ (lemma34_map cs T).getD a ∅) :
    (∃ v ∈ vars cs, a = varIdx cs v ∧ DescV cs T v q) ∨
      (∃ j s, j < cs.length ∧ s < 3 ∧ a = slot cs j s ∧ (s = 0 → DescB cs T j q) ∧
        (s ≠ 0 → DescR cs T j q)) := by
  rw [l34_len] at ha
  rcases idx_cases cs a ha with ⟨v, hv, rfl⟩ | ⟨j, s, hj, hs, rfl⟩
  · left
    refine ⟨v, hv, rfl, descV_of cs T v q ?_⟩
    rwa [getD_of_some (l34_get_v cs T v hv)] at hq
  · right
    refine ⟨j, s, hj, hs, rfl, ?_⟩
    rw [getD_congr (l34_get_c cs T j s hj hs)] at hq
    obtain ⟨h0, h1, h2⟩ := truePos_spec cs hcs T hT j hj
    exact desc_clause cs hcs T j hj _ (truePos_lt cs j T) h0 h1 h2 s hs q hq

theorem l34_cross (cs : Inst6) (hcs : Inst6Valid cs) (T : Finset ℕ) (hT : Inst6IsSol cs T) :
    ∀ a < (lemma34_map cs T).length, ∀ b < (lemma34_map cs T).length, a ≠ b →
      ∀ qa ∈ (lemma34_map cs T).getD a ∅, ∀ qb ∈ (lemma34_map cs T).getD b ∅,
        sumDiag qa ≠ sumDiag qb := by
  intro a ha b hb hab qa hqa qb hqb heq
  rcases desc34 cs hcs T hT a ha qa hqa with ⟨v, hv, rfl, dv⟩ | ⟨j, s, hj, hs, rfl, dB, dR⟩ <;>
    rcases desc34 cs hcs T hT b hb qb hqb with
      ⟨v', hv', rfl, dv'⟩ | ⟨j', s', hj', hs', rfl, dB', dR'⟩
  · exact hab (VV cs T v v' qa qb dv dv' heq)
  · by_cases hs0 : s' = 0
    · exact VB cs T v j' qa qb hv hj' dv (dB' hs0) heq
    · exact VR cs T v j' qa qb hv hj' dv (dR' hs0) heq
  · by_cases hs0 : s = 0
    · exact VB cs T v' j qb qa hv' hj dv' (dB hs0) heq.symm
    · exact VR cs T v' j qb qa hv' hj dv' (dR hs0) heq.symm
  · by_cases hs0 : s = 0 <;> by_cases hs0' : s' = 0
    · have hjj := BB cs hcs T j j' qa qb hj hj' (dB hs0) (dB' hs0') heq
      subst hjj
      exact hab (by rw [hs0, hs0'])
    · exact BR cs T j j' qa qb (dB hs0) (dR' hs0') heq
    · exact BR cs T j' j qb qa (dB' hs0') (dR hs0) heq.symm
    · have hjj := RR cs hcs T j j' qa qb hj hj' (dR hs0) (dR' hs0') heq
      subst hjj
      by_cases hss : s = s'
      · exact hab (by rw [hss])
      · rw [getD_congr (l34_get_c cs T j s hj hs)] at hqa
        rw [getD_congr (l34_get_c cs T j s' hj hs')] at hqb
        have hd := clause23_disj cs hcs j hj _ (truePos_lt cs j T)
        rcases (by omega : (s = 1 ∧ s' = 2) ∨ (s = 2 ∧ s' = 1)) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact hd qa hqa qb hqb heq
        · exact hd qb hqb qa hqa heq.symm

/-- Lemma 34. -/
theorem lemma34 (cs : Inst6) (hcs : Inst6Valid cs) (T : Finset ℕ) (hT : Inst6IsSol cs T) :
    Inst5IsSol (def31 cs) (lemma34_map cs T) := by
  refine ⟨f2_of (by rw [def31_len, l34_len]) ?_, l34_cross cs hcs T hT⟩
  intro a M S hM hS
  have ha : a < (def31 cs).length := (List.getElem?_eq_some_iff.mp hM).1
  rw [def31_len] at ha
  rcases idx_cases cs a ha with ⟨v, hv, rfl⟩ | ⟨j, s, hj, hs, rfl⟩
  · rw [def31_get_v cs v hv] at hM
    rw [l34_get_v cs T v hv] at hS
    obtain rfl := Option.some.inj hM
    obtain rfl := Option.some.inj hS
    rw [G0v_sol]
    by_cases hvT : v ∈ T
    · rw [if_pos hvT]
      exact Or.inl rfl
    · rw [if_neg hvT]
      exact Or.inr rfl
  · rw [def31_get_c cs j s hj hs] at hM
    rw [l34_get_c cs T j s hj hs, clauseSols_eq] at hS
    obtain ⟨g1, g2, g3⟩ := clauseSols_sol cs hcs j hj (truePos cs j T) (truePos_lt cs j T)
    rcases (by omega : s = 0 ∨ s = 1 ∨ s = 2) with rfl | rfl | rfl
    · obtain rfl := Option.some.inj hM
      obtain rfl := Option.some.inj hS
      exact g1
    · obtain rfl := Option.some.inj hM
      obtain rfl := Option.some.inj hS
      exact g2
    · obtain rfl := Option.some.inj hM
      obtain rfl := Option.some.inj hS
      exact g3

/-! ### Lemma 35 -/

theorem colorSol_eq_red (b : Bool) (δ : ℕ) : colorSol b δ = redSol δ ↔ b = true := by
  cases b
  · exact ⟨fun h => absurd h.symm (red_ne_blue δ), fun h => absurd h (by decide)⟩
  · exact ⟨fun _ => rfl, fun _ => rfl⟩

theorem sol_len (cs : Inst6) (Ss : List (Finset Queen)) (hS : Inst5IsSol (def31 cs) Ss) :
    Ss.length = ((vars cs).sort (· ≤ ·)).length + 3 * cs.length := by
  rw [← hS.1.length_eq, def31_len]

theorem sol_var (cs : Inst6) (Ss : List (Finset Queen)) (hS : Inst5IsSol (def31 cs) Ss)
    (v : ℕ) (hv : v ∈ vars cs) :
    Ss.getD (varIdx cs v) ∅ = redSol (delta cs v) ∨
      Ss.getD (varIdx cs v) ∅ = blueSol (delta cs v) :=
  (G0v_sol cs v _).mp (f2_get hS.1 (def31_get_v cs v hv))

/-- In a solution of `M₅`, the colours of the variables of `c_j` and the solutions of
`G¹_c, G²_c, G³_c` are as in the proof of Lemma 33. -/
theorem clause_of_sol (cs : Inst6) (hcs : Inst6Valid cs) (Ss : List (Finset Queen))
    (hS : Inst5IsSol (def31 cs) Ss) (j : ℕ) (hj : j < cs.length) :
    ∃ t, t < 3 ∧ (clauseVar cs j 0 ∈ lemma35_map cs Ss ↔ t = 0) ∧
      (clauseVar cs j 1 ∈ lemma35_map cs Ss ↔ t = 1) ∧
      (clauseVar cs j 2 ∈ lemma35_map cs Ss ↔ t = 2) ∧
      [Ss.getD (slot cs j 0) ∅, Ss.getD (slot cs j 1) ∅, Ss.getD (slot cs j 2) ∅] =
        clauseSols cs j t := by
  have hlen := sol_len cs Ss hS
  obtain ⟨hF, hX⟩ := hS
  obtain ⟨-, -, hc⟩ := clause_facts cs hcs j hj
  have hmv : ∀ s, s < 3 → clauseVar cs j s ∈ vars cs := by
    intro s hs
    apply mem_vars_of cs j hj
    rw [hc]
    rcases (by omega : s = 0 ∨ s = 1 ∨ s = 2) with rfl | rfl | rfl <;> simp
  have hN0 := idx_lt cs _ (hmv 0 (by norm_num))
  have hN1 := idx_lt cs _ (hmv 1 (by norm_num))
  have hN2 := idx_lt cs _ (hmv 2 (by norm_num))
  have dis : ∀ a b, a < Ss.length → b < Ss.length → a ≠ b →
      SumDisj (Ss.getD a ∅) (Ss.getD b ∅) := fun a b ha hb hab => hX a ha b hb hab
  obtain ⟨ci, hci⟩ := exists_color
    ((G0v_sol cs _ _).mp (f2_get hF (def31_get_v cs _ (hmv 0 (by norm_num)))))
  obtain ⟨cj, hcj⟩ := exists_color
    ((G0v_sol cs _ _).mp (f2_get hF (def31_get_v cs _ (hmv 1 (by norm_num)))))
  obtain ⟨ck, hck⟩ := exists_color
    ((G0v_sol cs _ _).mp (f2_get hF (def31_get_v cs _ (hmv 2 (by norm_num)))))
  have g1 : (G1 cs j).IsSol (Ss.getD (slot cs j 0) ∅) :=
    f2_get hF ((def31_get_c cs j 0 hj (by norm_num)).trans rfl)
  have g2 : (G2 cs j).IsSol (Ss.getD (slot cs j 1) ∅) :=
    f2_get hF ((def31_get_c cs j 1 hj (by norm_num)).trans rfl)
  have g3 : (G3 cs j).IsSol (Ss.getD (slot cs j 2) ∅) :=
    f2_get hF ((def31_get_c cs j 2 hj (by norm_num)).trans rfl)
  have hs0 : slot cs j 0 < Ss.length := by unfold slot; rw [hlen]; omega
  have hs1 : slot cs j 1 < Ss.length := by unfold slot; rw [hlen]; omega
  have hs2 : slot cs j 2 < Ss.length := by unfold slot; rw [hlen]; omega
  have d1i : SumDisj (Ss.getD (slot cs j 0) ∅) (colorSol ci (delta cs (clauseVar cs j 0))) := by
    rw [← hci]; exact dis _ _ hs0 (by omega) (by unfold slot; omega)
  have d1j : SumDisj (Ss.getD (slot cs j 0) ∅) (colorSol cj (delta cs (clauseVar cs j 1))) := by
    rw [← hcj]; exact dis _ _ hs0 (by omega) (by unfold slot; omega)
  have d1k : SumDisj (Ss.getD (slot cs j 0) ∅) (colorSol ck (delta cs (clauseVar cs j 2))) := by
    rw [← hck]; exact dis _ _ hs0 (by omega) (by unfold slot; omega)
  have d2i : SumDisj (Ss.getD (slot cs j 1) ∅) (colorSol ci (delta cs (clauseVar cs j 0))) := by
    rw [← hci]; exact dis _ _ hs1 (by omega) (by unfold slot; omega)
  have d2j : SumDisj (Ss.getD (slot cs j 1) ∅) (colorSol cj (delta cs (clauseVar cs j 1))) := by
    rw [← hcj]; exact dis _ _ hs1 (by omega) (by unfold slot; omega)
  have d3j : SumDisj (Ss.getD (slot cs j 2) ∅) (colorSol cj (delta cs (clauseVar cs j 1))) := by
    rw [← hcj]; exact dis _ _ hs2 (by omega) (by unfold slot; omega)
  have d3k : SumDisj (Ss.getD (slot cs j 2) ∅) (colorSol ck (delta cs (clauseVar cs j 2))) := by
    rw [← hck]; exact dis _ _ hs2 (by omega) (by unfold slot; omega)
  have d23 : SumDisj (Ss.getD (slot cs j 1) ∅) (Ss.getD (slot cs j 2) ∅) :=
    dis _ _ hs1 hs2 (by unfold slot; omega)
  obtain ⟨t, ht, ei, ej, ek, hcl⟩ := clause_unique cs hcs j hj ci cj ck _ _ _ g1 g2 g3
    d1i d1j d1k d2i d2j d3j d3k d23
  have mem35 : ∀ s, s < 3 → ∀ b : Bool,
      Ss.getD (varIdx cs (clauseVar cs j s)) ∅ = colorSol b (delta cs (clauseVar cs j s)) →
      (clauseVar cs j s ∈ lemma35_map cs Ss ↔ b = true) := by
    intro s hs b hb
    unfold lemma35_map
    rw [Finset.mem_filter, hb, colorSol_eq_red]
    exact ⟨fun h => h.2, fun h => ⟨hmv s hs, h⟩⟩
  refine ⟨t, ht, ?_, ?_, ?_, hcl⟩
  · rw [mem35 0 (by norm_num) ci hci, ei, decide_eq_true_iff]
  · rw [mem35 1 (by norm_num) cj hcj, ej, decide_eq_true_iff]
  · rw [mem35 2 (by norm_num) ck hck, ek, decide_eq_true_iff]

/-- Lemma 35. -/
theorem lemma35 (cs : Inst6) (hcs : Inst6Valid cs) (Ss : List (Finset Queen))
    (hS : Inst5IsSol (def31 cs) Ss) :
    (∀ v ∈ vars cs, Ss.getD (varIdx cs v) ∅ = redSol (delta cs v) ∨
      Ss.getD (varIdx cs v) ∅ = blueSol (delta cs v)) ∧
    Inst6IsSol cs (lemma35_map cs Ss) := by
  refine ⟨fun v hv => sol_var cs Ss hS v hv, Finset.filter_subset _ _, ?_⟩
  intro c hc
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hc
  obtain ⟨-, -, hcj⟩ := clause_facts cs hcs j hj
  rw [hcj]
  obtain ⟨t, ht, e0, e1, e2, -⟩ := clause_of_sol cs hcs Ss hS j hj
  apply card_inter_one
  rcases (by omega : t = 0 ∨ t = 1 ∨ t = 2) with rfl | rfl | rfl
  · exact Or.inl ⟨e0.mpr rfl, fun h => absurd (e1.mp h) (by norm_num),
      fun h => absurd (e2.mp h) (by norm_num)⟩
  · exact Or.inr (Or.inl ⟨fun h => absurd (e0.mp h) (by norm_num), e1.mpr rfl,
      fun h => absurd (e2.mp h) (by norm_num)⟩)
  · exact Or.inr (Or.inr ⟨fun h => absurd (e0.mp h) (by norm_num),
      fun h => absurd (e1.mp h) (by norm_num), e2.mpr rfl⟩)
/-! ### The bijection of Theorem 36 -/

/-- Every solution of `M₅` is the one built in Lemma 34 from its own assignment. -/
theorem l34_l35 (cs : Inst6) (hcs : Inst6Valid cs) (Ss : List (Finset Queen))
    (hS : Inst5IsSol (def31 cs) Ss) : lemma34_map cs (lemma35_map cs Ss) = Ss := by
  have hlen := sol_len cs Ss hS
  apply List.ext_getElem?
  intro n
  by_cases hn : n < ((vars cs).sort (· ≤ ·)).length + 3 * cs.length
  · rcases idx_cases cs n hn with ⟨v, hv, rfl⟩ | ⟨j, s, hj, hs, rfl⟩
    · rw [l34_get_v cs _ v hv]
      have hlt : varIdx cs v < Ss.length := by
        have := idx_lt cs v hv
        omega
      rw [List.getElem?_eq_getElem hlt, ← List.getD_eq_getElem Ss ∅ hlt]
      rcases sol_var cs Ss hS v hv with h | h
      · have hm : v ∈ lemma35_map cs Ss := Finset.mem_filter.mpr ⟨hv, h⟩
        rw [if_pos hm, h]
      · have hm : v ∉ lemma35_map cs Ss := fun hm =>
          red_ne_blue (delta cs v) ((Finset.mem_filter.mp hm).2.symm.trans h)
        rw [if_neg hm, h]
    · rw [l34_get_c cs _ j s hj hs]
      obtain ⟨t, ht, e0, e1, -, hcl⟩ := clause_of_sol cs hcs Ss hS j hj
      rw [truePos_of cs j _ t ht e0 e1, ← hcl]
      rcases (by omega : s = 0 ∨ s = 1 ∨ s = 2) with rfl | rfl | rfl
      · have hlt : slot cs j 0 < Ss.length := by unfold slot; omega
        rw [List.getElem?_eq_getElem hlt, ← List.getD_eq_getElem Ss ∅ hlt]
        rfl
      · have hlt : slot cs j 1 < Ss.length := by unfold slot; omega
        rw [List.getElem?_eq_getElem hlt, ← List.getD_eq_getElem Ss ∅ hlt]
        rfl
      · have hlt : slot cs j 2 < Ss.length := by unfold slot; omega
        rw [List.getElem?_eq_getElem hlt, ← List.getD_eq_getElem Ss ∅ hlt]
        rfl
  · rw [List.getElem?_eq_none (by rw [l34_len]; omega),
      List.getElem?_eq_none (by rw [hlen]; omega)]

/-- The assignment read off from the solution of Lemma 34 is the original one. -/
theorem l35_l34 (cs : Inst6) (T : Finset ℕ) (hT : Inst6IsSol cs T) :
    lemma35_map cs (lemma34_map cs T) = T := by
  ext v
  unfold lemma35_map
  rw [Finset.mem_filter]
  constructor
  · rintro ⟨hv, h⟩
    rw [getD_of_some (l34_get_v cs T v hv)] at h
    by_contra hvT
    rw [if_neg hvT] at h
    exact red_ne_blue _ h.symm
  · intro hvT
    have hv := hT.1 hvT
    refine ⟨hv, ?_⟩
    rw [getD_of_some (l34_get_v cs T v hv), if_pos hvT]

/-! ### Validity of `M₅` -/

theorem valid_of (M : Inst4) (h1 : 1 ≤ M.n) (hcard : M.C.card = M.R.card)
    (hC : ∀ c ∈ M.C, c < M.n) (hR : ∀ r ∈ M.R, r < M.n)
    (hD : ∀ d ∈ M.Dm, -((M.n : ℤ) - 1) ≤ d ∧ d ≤ (M.n : ℤ) - 1) (hP : M.Dp = ∅) :
    M.Valid :=
  ⟨⟨⟨h1, fun q hq => absurd hq (Finset.notMem_empty q),
      fun q hq => absurd hq (Finset.notMem_empty q)⟩, hcard,
      fun q hq => absurd hq (Finset.notMem_empty q), hC, hR⟩, hD,
    fun d hd => by rw [hP] at hd; exact absurd hd (Finset.notMem_empty d)⟩

theorem G0v_valid (cs : Inst6) (v : ℕ) : (G0v cs v).Valid := by
  have hC := G0v_C cs v
  have hR : (G0v cs v).R = {0, 2, 3} := rfl
  have hn : (G0v cs v).n = 4 + delta cs v := rfl
  have h3 : ({delta cs v, delta cs v + 1, delta cs v + 3} : Finset ℕ).card = 3 :=
    Finset.card_eq_three.mpr ⟨_, _, _, by omega, by omega, by omega, rfl⟩
  apply valid_of
  · rw [hn]; omega
  · rw [hC, hR, h3]; rfl
  · intro c hc
    rw [hC] at hc
    rw [hn]
    simp only [Finset.mem_insert, Finset.mem_singleton] at hc
    omega
  · intro r hr
    rw [hR] at hr
    rw [hn]
    simp only [Finset.mem_insert, Finset.mem_singleton] at hr
    omega
  · intro d hd
    simp [G0v, Inst4.shift, G0] at hd
  · rfl

theorem G1_valid (cs : Inst6) (hcs : Inst6Valid cs) (j : ℕ) (hj : j < cs.length) :
    (G1 cs j).Valid := by
  have hx := clause_arith cs hcs j hj
  have fi := cols_facts cs j (clauseVar cs j 0)
  have fj := cols_facts cs j (clauseVar cs j 1)
  have fk := cols_facts cs j (clauseVar cs j 2)
  have h3 : (G1 cs j).C.card = 3 :=
    Finset.card_eq_three.mpr ⟨_, _, _, by omega, by omega, by omega, rfl⟩
  apply valid_of
  · show 1 ≤ colBlue cs j (clauseVar cs j 2) + 1
    omega
  · rw [h3]; rfl
  · intro c hc
    simp only [G1, Finset.mem_insert, Finset.mem_singleton] at hc ⊢
    omega
  · intro r hr
    simp only [G1, Finset.mem_insert, Finset.mem_singleton] at hr ⊢
    omega
  · intro d hd
    simp only [G1, Finset.mem_insert, Finset.mem_singleton] at hd ⊢
    push_cast
    omega
  · rfl

theorem G2_valid (cs : Inst6) (hcs : Inst6Valid cs) (j : ℕ) (hj : j < cs.length) :
    (G2 cs j).Valid := by
  have hx := clause_arith cs hcs j hj
  have fi := cols_facts cs j (clauseVar cs j 0)
  have fj := cols_facts cs j (clauseVar cs j 1)
  have h2 : (G2 cs j).C.card = 2 := Finset.card_pair (by omega)
  apply valid_of
  · show 1 ≤ colRed cs j (clauseVar cs j 1) + 1
    omega
  · rw [h2]; rfl
  · intro c hc
    simp only [G2, Finset.mem_insert, Finset.mem_singleton] at hc ⊢
    omega
  · intro r hr
    simp only [G2, Finset.mem_insert, Finset.mem_singleton] at hr ⊢
    omega
  · intro d hd
    simp [G2] at hd
  · rfl

theorem G3_valid (cs : Inst6) (hcs : Inst6Valid cs) (j : ℕ) (hj : j < cs.length) :
    (G3 cs j).Valid := by
  have hx := clause_arith cs hcs j hj
  have fj := cols_facts cs j (clauseVar cs j 1)
  have fk := cols_facts cs j (clauseVar cs j 2)
  have h2 : (G3 cs j).C.card = 2 := Finset.card_pair (by omega)
  apply valid_of
  · show 1 ≤ colRed cs j (clauseVar cs j 2) + 1
    omega
  · rw [h2]; rfl
  · intro c hc
    simp only [G3, Finset.mem_insert, Finset.mem_singleton] at hc ⊢
    omega
  · intro r hr
    simp only [G3, Finset.mem_insert, Finset.mem_singleton] at hr ⊢
    omega
  · intro d hd
    simp [G3] at hd
  · rfl

theorem def31_valid (cs : Inst6) (hcs : Inst6Valid cs) : Inst5Valid (def31 cs) := by
  intro M hM
  unfold def31 at hM
  rw [List.mem_append, List.mem_map, List.mem_flatMap] at hM
  rcases hM with ⟨v, -, rfl⟩ | ⟨j, hj, hM⟩
  · exact ⟨G0v_valid cs v, rfl⟩
  · rw [List.mem_range] at hj
    simp only [List.mem_cons] at hM
    rcases hM with rfl | rfl | rfl | hM
    · exact ⟨G1_valid cs hcs j hj, rfl⟩
    · exact ⟨G2_valid cs hcs j hj, rfl⟩
    · exact ⟨G3_valid cs hcs j hj, rfl⟩
    · simp at hM

/-- Theorem 36, instance-level half. -/
theorem theorem36 (cs : Inst6) (hcs : Inst6Valid cs) :
    Inst5Valid (def31 cs) ∧
      _root_.Set.ncard {Ss : List (Finset Queen) | Inst5IsSol (def31 cs) Ss} =
        _root_.Set.ncard {T : Finset ℕ | Inst6IsSol cs T} := by
  refine ⟨def31_valid cs hcs, ?_⟩
  apply Set.ncard_congr (fun Ss _ => lemma35_map cs Ss)
  · intro Ss hSs
    exact (lemma35 cs hcs Ss hSs).2
  · intro Ss1 Ss2 h1 h2 heq
    exact (l34_l35 cs hcs Ss1 h1).symm.trans
      ((congrArg (lemma34_map cs) heq).trans (l34_l35 cs hcs Ss2 h2))
  · intro T hT
    exact ⟨lemma34_map cs T, lemma34 cs hcs T hT, l35_l34 cs T hT⟩

end NQueensComp.NPC.T36Proof

open NQueensComp.NPC.T36Proof in
theorem solution :
    ∀ cs : Inst6, Inst6Valid cs →
      Inst5Valid (def31 cs) ∧
        _root_.Set.ncard {Ss : List (Finset Queen) | Inst5IsSol (def31 cs) Ss} =
          _root_.Set.ncard {T : Finset ℕ | Inst6IsSol cs T} :=
  fun cs hcs => theorem36 cs hcs
