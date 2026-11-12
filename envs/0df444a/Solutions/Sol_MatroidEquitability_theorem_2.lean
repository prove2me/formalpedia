-- Prove2me | solution 1 for MatroidEquitability.theorem_2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T19:07:49.586674+00:00
-- url     : https://prove2.me/submissions/92b79a7d-f858-4894-9dc9-ec3a71c6b1fa

import Mathlib
import Definitions.Def_MatroidEquitability_setWeight
import Definitions.Def_MatroidEquitability_IsBlock
import Definitions.Def_MatroidEquitability_IsPrimalOptimal
import Definitions.Def_MatroidEquitability_IsDualOptimal
import Definitions.Def_MatroidEquitability_dualVector
import Definitions.Def_MatroidEquitability_supportPlus
import Theorems.Thm_MatroidEquitability_proof_theorem_2_eq_5
import Theorems.Thm_MatroidEquitability_proof_theorem_2_eq_6
import Theorems.Thm_MatroidEquitability_proof_theorem_2_eq_7
import Theorems.Thm_MatroidEquitability_proof_theorem_2_eq_8

section
namespace MatroidEquitability

/-- Theorem 2. -/
theorem chk_theorem_2 {α : Type*} (M : Matroid α) [M.Finite] (w : α → ℝ)
    (hw : ∀ e ∈ M.E, 0 ≤ w e ∧ w e ≤ 1) (B D : Set α) (hB : IsBlock M B) (hD : IsBlock M D)
    (hlt : setWeight w B < setWeight w D)
    (hcons : ∀ C, IsBlock M C → ¬ (setWeight w B < setWeight w C ∧ setWeight w C < setWeight w D)) :
    setWeight w D - setWeight w B ≤ 1 := by
  by_contra hcon
  push_neg at hcon
  have hfin : ∀ P : Set α → Prop, {C | IsBlock M C ∧ P C}.Finite := fun P =>
    (M.ground_finite.finite_subsets).subset (fun C hC => hC.1.1.subset_ground)
  have hFpfin := hfin (fun C => setWeight w D ≤ setWeight w C)
  have hFmfin := hfin (fun C => setWeight w C ≤ setWeight w B)
  set Fp : Finset (Set α) := hFpfin.toFinset with hFp
  set Fm : Finset (Set α) := hFmfin.toFinset with hFm
  have memFp : ∀ C, C ∈ Fp ↔ IsBlock M C ∧ setWeight w D ≤ setWeight w C := by
    intro C; rw [hFp, Set.Finite.mem_toFinset]; rfl
  have memFm : ∀ C, C ∈ Fm ↔ IsBlock M C ∧ setWeight w C ≤ setWeight w B := by
    intro C; rw [hFm, Set.Finite.mem_toFinset]; rfl
  have hFpne : Fp.Nonempty := ⟨D, (memFp D).2 ⟨hD, le_rfl⟩⟩
  have hFmne : Fm.Nonempty := ⟨B, (memFm B).2 ⟨hB, le_rfl⟩⟩
  have hdich : ∀ C, IsBlock M C → C ∈ Fp ∨ C ∈ Fm := by
    intro C hC
    have := hcons C hC
    by_cases h : setWeight w B < setWeight w C
    · left; exact (memFp C).2 ⟨hC, by by_contra h'; exact this ⟨h, not_le.mp h'⟩⟩
    · right; exact (memFm C).2 ⟨hC, not_lt.mp h⟩
  obtain ⟨⟨u, γ, hP⟩, ⟨lam, x, hDu⟩, hmain⟩ :=
    proof_theorem_2_eq_5 M.E M.ground_finite Fp Fm hFpne hFmne
      (fun C hC => ((memFp C).1 hC).1.1.subset_ground)
      (fun C hC => ((memFm C).1 hC).1.1.subset_ground)
  obtain ⟨hγeq, -, hsl, h5⟩ := hmain u γ lam x hP hDu
  have hu := hP.1.1
  have hcons' := hP.1.2
  -- w is feasible
  have hγ1 : setWeight w D - setWeight w B ≤ γ := by
    refine hP.2 w _ ⟨hw, ?_⟩
    intro B' hB' D' hD'
    have := ((memFp B').1 hB').2
    have := ((memFm D').1 hD').2
    linarith
  set b := Fp.inf' hFpne (setWeight u) with hb
  set d := Fm.sup' hFmne (setWeight u) with hd
  have hγ : γ = b - d := hγeq
  have hble : ∀ C ∈ Fp, b ≤ setWeight u C := fun C hC => Finset.inf'_le _ hC
  have hdge : ∀ C ∈ Fm, setWeight u C ≤ d := fun C hC => Finset.le_sup' _ hC
  have hγgt : 1 < γ := by linarith
  have hplus : ∀ B' ∈ supportPlus Fp Fm lam, setWeight u B' = b := by
    intro B' hB'
    have hB'' := Finset.mem_filter.mp hB'
    obtain ⟨D', hD', hl⟩ := hB''.2
    have := hsl B' hB''.1 D' hD' hl
    have := hdge D' hD'
    have := hble B' hB''.1
    linarith
  have hminus : ∀ D' ∈ supportMinus Fp Fm lam, setWeight u D' = d := by
    intro D' hD'
    have hD'' := Finset.mem_filter.mp hD'
    obtain ⟨B', hB', hl⟩ := hD''.2
    have := hsl B' hB' D' hD''.1 hl
    have := hdge D' hD''.1
    have := hble B' hB'
    linarith
  set S : Set α := {e ∈ M.E | u e = 1} with hS
  have hlam : ∀ B ∈ Fp, ∀ D ∈ Fm, 0 ≤ lam B D := hDu.1.1
  have hsum : ∑ B ∈ Fp, ∑ D ∈ Fm, lam B D = 1 := hDu.1.2.1
  have h6 := proof_theorem_2_eq_6 M.E M.ground_finite Fp Fm
    (fun C hC => ((memFp C).1 hC).1.1.subset_ground)
    (fun C hC => ((memFm C).1 hC).1.1.subset_ground) u γ lam hu hlam hsum hsl h5 S hS
  have hchain := h6.1.trans (h6.2.1.trans (h6.2.2.1.trans h6.2.2.2))
  have hnonpos : ∑ B ∈ supportPlus Fp Fm lam, ∑ D ∈ supportMinus Fp Fm lam,
      lam B D * (((B ∩ S).ncard : ℝ) - ((D ∩ S).ncard : ℝ)) ≤ 0 := by
    refine Finset.sum_nonpos fun B' hB' => Finset.sum_nonpos fun D' hD' => ?_
    have hB'' := (Finset.mem_filter.mp hB').1
    have hD'' := (Finset.mem_filter.mp hD').1
    have hBp := (memFp B').1 hB''
    have hDm := (memFm D').1 hD''
    have h7 := proof_theorem_2_eq_7 M u hu S hS B' hBp.1 (by
      intro C hC ⟨h1, h2⟩
      rw [hplus B' hB'] at h1 h2
      rcases hdich C hC with h | h
      · have := hble C h; linarith
      · have := hdge C h; linarith)
    have h8 := proof_theorem_2_eq_8 M u hu S hS D' hDm.1 (by
      intro C hC ⟨h1, h2⟩
      rw [hminus D' hD'] at h1 h2
      rcases hdich C hC with h | h
      · have := hble C h; linarith
      · have := hdge C h; linarith)
    exact mul_nonpos_of_nonneg_of_nonpos (hlam B' hB'' D' hD'') (by linarith)
  linarith

end MatroidEquitability
end

theorem solution : type_of% @MatroidEquitability.chk_theorem_2 := @MatroidEquitability.chk_theorem_2
