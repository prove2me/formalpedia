-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.exists_nextLevel_feasible_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:37.685478+00:00
-- url     : https://prove2.me/submissions/ed1c3ce6-ae4c-4491-83e0-8b2213d9a53c

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_Gamma_zero
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_Gamma_zero
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_exists_nextLevel_strict_refinement
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_exists_sameLevel_opening_strict_refinement

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unnecessarySimpa false
set_option autoImplicit false
open MetricCodes
open MetricCodes.Spherical
open MetricCodes.Spherical.HigherHierarchy
noncomputable section
namespace MetricCodes.Spherical.HigherHierarchy
theorem _root_.solution {r : ℕ} {s : ℝ}
    (hs : 0 < s)
    {a : Fin (r + 1) → ℝ} {b : Fin r → ℝ}
    (h : Interlacing a b) (hgap : s < 2 * Gamma a b) :
    ∃ (A : Fin (r + 2) → ℝ) (B : Fin (r + 1) → ℝ),
      Interlacing A B ∧ s < 2 * Gamma A B ∧ Phi A B < Phi a b := by
  by_cases hlast : 0 < a (Fin.last r)
  · obtain ⟨A, B, hAB, hGamma, hPhi⟩ :=
      exists_nextLevel_strict_refinement h hlast
    exact ⟨A, B, hAB, by linarith, hPhi⟩
  · have hzero : a (Fin.last r) = 0 :=
      le_antisymm (le_of_not_gt hlast) (h.ambient_nonneg _)
    cases r with
    | zero =>
        rw [Gamma_zero] at hgap
        have ha : a 0 = 0 := by simpa using hzero
        simp [ha, spectralAtom, quadraticCoordinate] at hgap
        linarith
    | succ r =>
        obtain ⟨A, hlastA, hA, hGammaA, hPhiA⟩ :=
          exists_sameLevel_opening_strict_refinement (Nat.zero_lt_succ r) h hzero
        obtain ⟨C, D, hCD, hGammaC, hPhiC⟩ :=
          exists_nextLevel_strict_refinement hA hlastA
        exact ⟨C, D, hCD, by linarith, lt_trans hPhiC hPhiA⟩
end MetricCodes.Spherical.HigherHierarchy
