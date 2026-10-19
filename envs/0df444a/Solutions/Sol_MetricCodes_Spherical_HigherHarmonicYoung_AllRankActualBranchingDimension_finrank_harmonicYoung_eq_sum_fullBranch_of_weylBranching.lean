-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHarmonicYoung.AllRankActualBranchingDimension.finrank_harmonicYoung_eq_sum_fullBranch_of_weylBranching
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:43.40114+00:00
-- url     : https://prove2.me/submissions/bcf94cdd-73ef-43d3-ae06-2924680b4cb7

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_BranchingDimension_fullBranchSignature_antitone

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
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option autoImplicit false
set_option maxHeartbeats 1800000
open MetricCodes
open MetricCodes.Spherical
noncomputable section
set_option autoImplicit false
open scoped BigOperators InnerProductSpace
open MetricCodes.Spherical.HigherHarmonicYoung MetricCodes.Spherical.HigherHarmonicYoung.AllRankActualBranchingDimension
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.BranchingDimension
open MetricCodes.Spherical.HigherHierarchy
namespace MetricCodes.Spherical.HigherHarmonicYoung.AllRankActualBranchingDimension
theorem _root_.solution
    {r n : ℕ} (lam : Fin (r + 1) → ℕ)
    (hn : 2 * r + 5 ≤ n) (hdom : Antitone lam)
    (hbranch : WeylBranchingRecurrence n lam) :
    Module.finrank ℝ (HarmonicYoungSpace (n := n) lam) =
      ∑ mu : FullBranchWeight lam,
        Module.finrank ℝ
          (HarmonicYoungSpace (n := n - 1)
            (fullBranchSignature mu)) := by
  have hreal :
      (Module.finrank ℝ (HarmonicYoungSpace (n := n) lam) : ℝ) =
        (∑ mu : FullBranchWeight lam,
          Module.finrank ℝ
            (HarmonicYoungSpace (n := n - 1)
              (fullBranchSignature mu)) : ℕ) := by
    calc
      (Module.finrank ℝ (HarmonicYoungSpace (n := n) lam) : ℝ) =
          Weyl.dimension n lam :=
        (weyl_dimension_eq_finrank_harmonicYoung (by omega) lam hdom).symm
      _ = ∑ mu : FullBranchWeight lam,
          Weyl.dimension (n - 1) (fullBranchSignature mu) := hbranch
      _ = ∑ mu : FullBranchWeight lam,
          (Module.finrank ℝ
            (HarmonicYoungSpace (n := n - 1)
              (fullBranchSignature mu)) : ℝ) := by
        apply Finset.sum_congr rfl
        intro mu _
        exact weyl_dimension_eq_finrank_harmonicYoung (by omega)
          (fullBranchSignature mu) (fullBranchSignature_antitone mu)
      _ = (∑ mu : FullBranchWeight lam,
          Module.finrank ℝ
            (HarmonicYoungSpace (n := n - 1)
              (fullBranchSignature mu)) : ℕ) := by
        rw [Nat.cast_sum]
  exact_mod_cast hreal
end MetricCodes.Spherical.HigherHarmonicYoung.AllRankActualBranchingDimension
