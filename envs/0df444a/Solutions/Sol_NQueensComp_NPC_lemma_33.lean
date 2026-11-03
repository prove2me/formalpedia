-- Prove2me | solution 1 for NQueensComp.NPC.lemma_33
-- status  : ACCEPTED   (prove)
-- author  : @Victorized
-- created : 2026-11-03T04:14:55.605984+00:00
-- url     : https://prove2.me/submissions/26301aef-7e3a-4252-a2d3-a6a59d0343fb

import Mathlib
import Definitions.Def_NQueensComp_NPC_Reductions

/-! Lemma 33 (Gent, Jefferson & Nightingale 2017, p. 835): the six-gadget family `M₅,c` of a
clause has exactly three solutions. -/

open NQueensComp.NPC

namespace NQueensComp.NPC.L33Proof




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

/-! ### Lemma 33 -/

/-- The three solutions of `M₅,c`; in the `t`-th one the `t`-th variable is red. -/
def famL (cs : Inst6) (j t : ℕ) : List (Finset Queen) :=
  [colorSol (decide (t = 0)) (delta cs (clauseVar cs j 0)),
    colorSol (decide (t = 1)) (delta cs (clauseVar cs j 1)),
    colorSol (decide (t = 2)) (delta cs (clauseVar cs j 2))] ++ clauseSols cs j t

theorem cross_of (L : List (Finset Queen))
    (h : ∀ a b, a < b → b < L.length → SumDisj (L.getD a ∅) (L.getD b ∅)) :
    ∀ a < L.length, ∀ b < L.length, a ≠ b →
      ∀ qa ∈ L.getD a ∅, ∀ qb ∈ L.getD b ∅, sumDiag qa ≠ sumDiag qb := by
  intro a ha b hb hab qa hqa qb hqb
  rcases Nat.lt_or_gt_of_ne hab with h' | h'
  · exact h a b h' hb qa hqa qb hqb
  · exact (h b a h' ha qb hqb qa hqa).symm

theorem famL_len (cs : Inst6) (j t : ℕ) : (famL cs j t).length = 6 := by
  rw [famL, clauseSols_eq]
  rfl

/-- The queens of the `t`-th solution of `M₅,c`, with `T = {v_t}`. -/
theorem desc33 (cs : Inst6) (hcs : Inst6Valid cs) (j : ℕ) (hj : j < cs.length) (t : ℕ)
    (ht : t < 3) (a : ℕ) (ha : a < 6) (q : Queen) (hq : q ∈ (famL cs j t).getD a ∅) :
    (a < 3 ∧ DescV cs {clauseVar cs j t} (clauseVar cs j a) q) ∨
      (a = 3 ∧ DescB cs {clauseVar cs j t} j q) ∨
      ((a = 4 ∨ a = 5) ∧ DescR cs {clauseVar cs j t} j q) := by
  obtain ⟨h01, h12, -⟩ := clause_facts cs hcs j hj
  have e0 : clauseVar cs j 0 ∈ ({clauseVar cs j t} : Finset ℕ) ↔ t = 0 := by
    rw [Finset.mem_singleton]
    rcases (by omega : t = 0 ∨ t = 1 ∨ t = 2) with rfl | rfl | rfl <;>
      constructor <;> intro h <;> omega
  have e1 : clauseVar cs j 1 ∈ ({clauseVar cs j t} : Finset ℕ) ↔ t = 1 := by
    rw [Finset.mem_singleton]
    rcases (by omega : t = 0 ∨ t = 1 ∨ t = 2) with rfl | rfl | rfl <;>
      constructor <;> intro h <;> omega
  have e2 : clauseVar cs j 2 ∈ ({clauseVar cs j t} : Finset ℕ) ↔ t = 2 := by
    rw [Finset.mem_singleton]
    rcases (by omega : t = 0 ∨ t = 1 ∨ t = 2) with rfl | rfl | rfl <;>
      constructor <;> intro h <;> omega
  have hfam : famL cs j t =
      [if clauseVar cs j 0 ∈ ({clauseVar cs j t} : Finset ℕ) then
          redSol (delta cs (clauseVar cs j 0)) else blueSol (delta cs (clauseVar cs j 0)),
        if clauseVar cs j 1 ∈ ({clauseVar cs j t} : Finset ℕ) then
          redSol (delta cs (clauseVar cs j 1)) else blueSol (delta cs (clauseVar cs j 1)),
        if clauseVar cs j 2 ∈ ({clauseVar cs j t} : Finset ℕ) then
          redSol (delta cs (clauseVar cs j 2)) else blueSol (delta cs (clauseVar cs j 2)),
        (clauseSols cs j t).getD 0 ∅, (clauseSols cs j t).getD 1 ∅,
        (clauseSols cs j t).getD 2 ∅] := by
    rw [famL, colorSol_eq_if _ (e0.trans decide_eq_true_iff.symm),
      colorSol_eq_if _ (e1.trans decide_eq_true_iff.symm),
      colorSol_eq_if _ (e2.trans decide_eq_true_iff.symm), clauseSols_eq]
    rfl
  rw [hfam] at hq
  interval_cases a
  · exact Or.inl ⟨by norm_num, descV_of cs _ _ q hq⟩
  · exact Or.inl ⟨by norm_num, descV_of cs _ _ q hq⟩
  · exact Or.inl ⟨by norm_num, descV_of cs _ _ q hq⟩
  · exact Or.inr (Or.inl ⟨rfl, (desc_clause cs hcs _ j hj t ht e0 e1 e2 0 (by norm_num) q hq).1 rfl⟩)
  · exact Or.inr (Or.inr ⟨Or.inl rfl,
      (desc_clause cs hcs _ j hj t ht e0 e1 e2 1 (by norm_num) q hq).2 one_ne_zero⟩)
  · exact Or.inr (Or.inr ⟨Or.inr rfl,
      (desc_clause cs hcs _ j hj t ht e0 e1 e2 2 (by norm_num) q hq).2 two_ne_zero⟩)

theorem m5c_cross (cs : Inst6) (hcs : Inst6Valid cs) (j : ℕ) (hj : j < cs.length) (t : ℕ)
    (ht : t < 3) :
    ∀ a < (famL cs j t).length, ∀ b < (famL cs j t).length, a ≠ b →
      ∀ qa ∈ (famL cs j t).getD a ∅, ∀ qb ∈ (famL cs j t).getD b ∅,
        sumDiag qa ≠ sumDiag qb := by
  have hx := clause_arith cs hcs j hj
  obtain ⟨-, -, hc⟩ := clause_facts cs hcs j hj
  have mv : ∀ s, s < 3 → clauseVar cs j s ∈ vars cs := by
    intro s hs
    apply mem_vars_of cs j hj
    rw [hc]
    rcases (by omega : s = 0 ∨ s = 1 ∨ s = 2) with rfl | rfl | rfl <;> simp
  have h4 : (famL cs j t).getD 4 ∅ = (clauseSols cs j t).getD 1 ∅ := by
    rw [famL, clauseSols_eq]
    rfl
  have h5 : (famL cs j t).getD 5 ∅ = (clauseSols cs j t).getD 2 ∅ := by
    rw [famL, clauseSols_eq]
    rfl
  intro a ha b hb hab qa hqa qb hqb heq
  rw [famL_len] at ha hb
  rcases desc33 cs hcs j hj t ht a ha qa hqa with ⟨ha3, dA⟩ | ⟨rfl, dA⟩ | ⟨ha45, dA⟩ <;>
    rcases desc33 cs hcs j hj t ht b hb qb hqb with ⟨hb3, dB⟩ | ⟨rfl, dB⟩ | ⟨hb45, dB⟩
  · have hv := VV cs _ _ _ qa qb dA dB heq
    interval_cases a <;> interval_cases b <;> first | exact hab rfl | omega
  · exact VB cs _ _ j qa qb (mv a ha3) hj dA dB heq
  · exact VR cs _ _ j qa qb (mv a ha3) hj dA dB heq
  · exact VB cs _ _ j qb qa (mv b hb3) hj dB dA heq.symm
  · exact hab rfl
  · exact BR cs _ j j qa qb dA dB heq
  · exact VR cs _ _ j qb qa (mv b hb3) hj dB dA heq.symm
  · exact BR cs _ j j qb qa dB dA heq.symm
  · have hd := clause23_disj cs hcs j hj t ht
    rcases ha45 with rfl | rfl <;> rcases hb45 with rfl | rfl
    · exact hab rfl
    · rw [h4] at hqa
      rw [h5] at hqb
      exact hd qa hqa qb hqb heq
    · rw [h5] at hqa
      rw [h4] at hqb
      exact hd qb hqb qa hqa heq.symm
    · exact hab rfl

theorem m5c_sol (cs : Inst6) (hcs : Inst6Valid cs) (j : ℕ) (hj : j < cs.length) (t : ℕ)
    (ht : t < 3) : Inst5IsSol (M5c cs j) (famL cs j t) := by
  obtain ⟨g1, g2, g3⟩ := clauseSols_sol cs hcs j hj t ht
  constructor
  · rw [famL, clauseSols_eq]
    simp only [M5c, List.cons_append, List.nil_append, List.forall₂_cons, List.Forall₂.nil,
      and_true]
    exact ⟨colorSol_sol _ _ _, colorSol_sol _ _ _, colorSol_sol _ _ _, g1, g2, g3⟩
  · exact m5c_cross cs hcs j hj t ht

theorem m5c_unique (cs : Inst6) (hcs : Inst6Valid cs) (j : ℕ) (hj : j < cs.length)
    (Ss : List (Finset Queen)) (h : Inst5IsSol (M5c cs j) Ss) :
    ∃ t, t < 3 ∧ Ss = famL cs j t := by
  obtain ⟨hF, hX⟩ := h
  have hlen : Ss.length = 6 := by rw [← hF.length_eq]; rfl
  obtain ⟨S0, S1, S2, S3, S4, S5, rfl⟩ :
      ∃ S0 S1 S2 S3 S4 S5 : Finset Queen, Ss = [S0, S1, S2, S3, S4, S5] := by
    match Ss, hlen with
    | [S0, S1, S2, S3, S4, S5], _ => exact ⟨S0, S1, S2, S3, S4, S5, rfl⟩
  simp only [M5c, List.forall₂_cons, List.Forall₂.nil, and_true] at hF
  obtain ⟨g0, g1, g2, g3, g4, g5⟩ := hF
  have dis : ∀ a b, a < 6 → b < 6 → a ≠ b →
      SumDisj ([S0, S1, S2, S3, S4, S5].getD a ∅) ([S0, S1, S2, S3, S4, S5].getD b ∅) :=
    fun a b ha hb hab => hX a ha b hb hab
  obtain ⟨ci, rfl⟩ := exists_color ((G0v_sol cs _ S0).mp g0)
  obtain ⟨cj, rfl⟩ := exists_color ((G0v_sol cs _ S1).mp g1)
  obtain ⟨ck, rfl⟩ := exists_color ((G0v_sol cs _ S2).mp g2)
  obtain ⟨t, ht, hci, hcj, hck, hcl⟩ := clause_unique cs hcs j hj ci cj ck S3 S4 S5 g3 g4 g5
    (dis 3 0 (by norm_num) (by norm_num) (by norm_num))
    (dis 3 1 (by norm_num) (by norm_num) (by norm_num))
    (dis 3 2 (by norm_num) (by norm_num) (by norm_num))
    (dis 4 0 (by norm_num) (by norm_num) (by norm_num))
    (dis 4 1 (by norm_num) (by norm_num) (by norm_num))
    (dis 5 1 (by norm_num) (by norm_num) (by norm_num))
    (dis 5 2 (by norm_num) (by norm_num) (by norm_num))
    (dis 4 5 (by norm_num) (by norm_num) (by norm_num))
  refine ⟨t, ht, ?_⟩
  rw [famL, ← hcl, ← hci, ← hcj, ← hck]
  rfl

end NQueensComp.NPC.L33Proof

open NQueensComp.NPC.L33Proof in
theorem solution (cs : Inst6) (hcs : Inst6Valid cs) (j : ℕ) (hj : j < cs.length) :
    _root_.Set.ncard {Ss : List (Finset Queen) | Inst5IsSol (M5c cs j) Ss} = 3 ∧
    (∃ Ss, Inst5IsSol (M5c cs j) Ss ∧
      Ss.getD 0 ∅ = redSol (delta cs (clauseVar cs j 0)) ∧
      Ss.getD 1 ∅ = blueSol (delta cs (clauseVar cs j 1)) ∧
      Ss.getD 2 ∅ = blueSol (delta cs (clauseVar cs j 2))) ∧
    (∃ Ss, Inst5IsSol (M5c cs j) Ss ∧
      Ss.getD 0 ∅ = blueSol (delta cs (clauseVar cs j 0)) ∧
      Ss.getD 1 ∅ = redSol (delta cs (clauseVar cs j 1)) ∧
      Ss.getD 2 ∅ = blueSol (delta cs (clauseVar cs j 2))) ∧
    (∃ Ss, Inst5IsSol (M5c cs j) Ss ∧
      Ss.getD 0 ∅ = blueSol (delta cs (clauseVar cs j 0)) ∧
      Ss.getD 1 ∅ = blueSol (delta cs (clauseVar cs j 1)) ∧
      Ss.getD 2 ∅ = redSol (delta cs (clauseVar cs j 2))) := by
  have hset : {Ss : List (Finset Queen) | Inst5IsSol (M5c cs j) Ss} =
      {famL cs j 0, famL cs j 1, famL cs j 2} := by
    ext Ss
    simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · intro h
      obtain ⟨t, ht, rfl⟩ := m5c_unique cs hcs j hj Ss h
      rcases (by omega : t = 0 ∨ t = 1 ∨ t = 2) with rfl | rfl | rfl <;> simp
    · rintro (rfl | rfl | rfl) <;> exact m5c_sol cs hcs j hj _ (by norm_num)
  refine ⟨?_, ⟨famL cs j 0, m5c_sol cs hcs j hj 0 (by norm_num), rfl, rfl, rfl⟩,
    ⟨famL cs j 1, m5c_sol cs hcs j hj 1 (by norm_num), rfl, rfl, rfl⟩,
    ⟨famL cs j 2, m5c_sol cs hcs j hj 2 (by norm_num), rfl, rfl, rfl⟩⟩
  rw [hset, Set.ncard_eq_three]
  refine ⟨_, _, _, ?_, ?_, ?_, rfl⟩
  · intro h
    exact red_ne_blue _ (congrArg (fun L => L.getD 0 ∅) h)
  · intro h
    exact red_ne_blue _ (congrArg (fun L => L.getD 0 ∅) h)
  · intro h
    exact red_ne_blue _ (congrArg (fun L => L.getD 1 ∅) h)
