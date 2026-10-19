-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHarmonicYoung.AllRankOrthogonalTensorPieriDimension.finrank_harmonicYoung_tensorPieri
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:46.222992+00:00
-- url     : https://prove2.me/submissions/45b9aac4-99ab-4a51-9521-38dfa8267868

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankOrthogonalTensorPieriDimension_weyl_tensorPieri_dimension

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
open MetricCodes.Spherical.HigherHarmonicYoung
noncomputable section
set_option autoImplicit false
open scoped BigOperators
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankOrthogonalTensorPieriDimension
open MetricCodes.Spherical.HigherChannel
open MetricCodes.Spherical.HigherHierarchy
open MetricCodes.Spherical.HigherWeylAllRankJacobiTrudiWeylEvaluation
open MetricCodes.Spherical.HigherWeylBinomialDeterminant
open MetricCodes.Spherical.HigherYoungAllRankOrthogonalTensorPieriCoefficient
open MetricCodes.Spherical.HigherYoungAllRankOrthogonalTensorPieriBoundaryColumn
open MetricCodes.Spherical.HigherYoungAllRankOrthogonalTensorPieriRowFiltering
open MetricCodes.Spherical.HigherYoungPenultimateRowProjectedLower
namespace MetricCodes.Spherical.HigherHarmonicYoung.AllRankOrthogonalTensorPieriDimension
theorem _root_.solution
    {r n : ℕ} (hn : 2 * r + 4 ≤ n)
    (lam : Fin (r + 1) → ℕ)
    (hdom : Antitone lam) (hzero : lam (Fin.last r) = 0) :
    (∑ i : {i : Fin (r + 1) // Antitone (raiseWeight lam i)},
      Module.finrank ℝ
        (HarmonicYoungSpace (n := n) (raiseWeight lam i.val))) +
      (∑ i : {i : Fin (r + 1) //
        0 < lam i ∧ Antitone (loweredInternalYoungWeight lam i)},
        Module.finrank ℝ
          (HarmonicYoungSpace (n := n)
            (loweredInternalYoungWeight lam i.val))) =
      n * Module.finrank ℝ (HarmonicYoungSpace (n := n) lam) := by
  have h := weyl_tensorPieri_dimension hn lam hdom hzero
  have hreal :
      ((∑ i : {i : Fin (r + 1) // Antitone (raiseWeight lam i)},
          Module.finrank ℝ
            (HarmonicYoungSpace (n := n) (raiseWeight lam i.val))) +
        (∑ i : {i : Fin (r + 1) //
          0 < lam i ∧ Antitone (loweredInternalYoungWeight lam i)},
          Module.finrank ℝ
            (HarmonicYoungSpace (n := n)
              (loweredInternalYoungWeight lam i.val))) : ℕ) =
        ((n * Module.finrank ℝ
          (HarmonicYoungSpace (n := n) lam) : ℕ) : ℝ) := by
    push_cast
    convert h using 1
    · apply congrArg₂ (· + ·)
      · apply Finset.sum_congr rfl
        intro i _
        exact (weyl_dimension_eq_finrank_harmonicYoung hn
          (raiseWeight lam i.val) i.property).symm
      · apply Finset.sum_congr rfl
        intro i _
        exact (weyl_dimension_eq_finrank_harmonicYoung hn
          (loweredInternalYoungWeight lam i.val) i.property.2).symm
    · rw [weyl_dimension_eq_finrank_harmonicYoung hn lam hdom]
  exact_mod_cast hreal
end MetricCodes.Spherical.HigherHarmonicYoung.AllRankOrthogonalTensorPieriDimension
