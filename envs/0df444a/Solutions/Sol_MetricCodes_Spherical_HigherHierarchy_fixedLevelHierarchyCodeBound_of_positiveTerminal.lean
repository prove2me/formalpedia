-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.fixedLevelHierarchyCodeBound_of_positiveTerminal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:42.304385+00:00
-- url     : https://prove2.me/submissions/ed106940-a148-46ee-8774-d8c0c519e1ef

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_exists_sameLevel_opening_strict_refinement
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_WeakInterlacing_ambient_nonneg
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_fixedLevelHierarchyCodeBound_levelZero

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
set_option autoImplicit false
open Filter Topology
open scoped BigOperators InnerProductSpace Matrix Topology
open MetricCodes.Spherical.HigherProjectionInstantiation
namespace MetricCodes.Spherical.HigherHierarchy
theorem _root_.solution
    (hpositive : ∀ {r : ℕ} {s R : ℝ}, 0 < s → s < 1 →
      ∀ (a : Fin (r + 1) → ℝ) (b : Fin r → ℝ),
        Interlacing a b → 0 < a (Fin.last r) →
          s < 2 * Gamma a b → Phi a b < R →
            ∀ᶠ n : ℕ in atTop,
              ∀ C : SpherePacking.SphericalCode n s,
                (C.points.card : ℝ) < (2 : ℝ) ^ (R * (n : ℝ))) :
    FixedLevelHierarchyCodeBound := by
  intro r s R hs hs' a b hinterlacing hspectral hR
  by_cases hlast : 0 < a (Fin.last r)
  · exact hpositive hs hs' a b hinterlacing hlast hspectral hR
  · have hzero : a (Fin.last r) = 0 :=
      le_antisymm (le_of_not_gt hlast)
        (hinterlacing.ambient_nonneg (Fin.last r))
    cases r with
    | zero =>
        exact fixedLevelHierarchyCodeBound_levelZero
          hs hs' a b hinterlacing hspectral hR
    | succ r =>
        obtain ⟨A, hApos, hA, hGamma, hPhi⟩ :=
          exists_sameLevel_opening_strict_refinement
            (Nat.succ_pos r) hinterlacing hzero
        exact hpositive hs hs' A b hA hApos
          (by nlinarith) (by linarith)
end MetricCodes.Spherical.HigherHierarchy
