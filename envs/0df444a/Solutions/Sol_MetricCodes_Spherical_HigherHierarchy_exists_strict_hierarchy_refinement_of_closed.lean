-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.exists_strict_hierarchy_refinement_of_closed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:40.232469+00:00
-- url     : https://prove2.me/submissions/66ea4f37-1f2c-4e40-be76-b6376f6c3341

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
open Filter Topology
open scoped BigOperators Topology
namespace MetricCodes.Spherical.HigherHierarchy
theorem _root_.solution
    {r : ℕ} {s : ℝ} (hs : 0 < s)
    (a : Fin (r + 1) → ℝ) (b : Fin r → ℝ)
    (hinterlacing : Interlacing a b)
    (hspectral : s ≤ 2 * Gamma a b) :
    ∃ (r' : ℕ) (A : Fin (r' + 1) → ℝ) (B : Fin r' → ℝ),
      Interlacing A B ∧ s < 2 * Gamma A B ∧ Phi A B < Phi a b := by
  by_cases hlast : 0 < a (Fin.last r)
  · obtain ⟨A, B, hAB, hGamma, hPhi⟩ :=
      exists_nextLevel_strict_refinement hinterlacing hlast
    exact ⟨r + 1, A, B, hAB, by linarith, hPhi⟩
  · have hzero : a (Fin.last r) = 0 :=
      le_antisymm (le_of_not_gt hlast) hinterlacing.1
    cases r with
    | zero =>
        have ha0 : a 0 = 0 := by simpa using hzero
        have hgamma : Gamma a b = 0 := by
          rw [Gamma_zero, ha0]
          norm_num [spectralAtom, quadraticCoordinate]
        rw [hgamma] at hspectral
        norm_num at hspectral
        linarith
    | succ r =>
        obtain ⟨A, _, hA, hGamma, hPhi⟩ :=
          exists_sameLevel_opening_strict_refinement
            (Nat.succ_pos r) hinterlacing hzero
        exact ⟨r + 1, A, b, hA, by linarith, hPhi⟩
end MetricCodes.Spherical.HigherHierarchy
