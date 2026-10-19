-- Prove2me | solution 1 for MetricCodes.Spherical.HigherYoungAllRankOrthogonalTensorPieriSourceSignatureInjectivity.paddedPieriSource_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:45.453197+00:00
-- url     : https://prove2.me/submissions/a622e2ff-4536-4086-a53b-4063886276ea

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherYoungAllRankOrthogonalTensorPieriSourceSignatureInjectivity_raiseWeight_row_injective
import Theorems.Thm_MetricCodes_Spherical_HigherYoungAllRankOrthogonalTensorPieriSourceSignatureInjectivity_loweredInternalYoungWeight_row_injective_of_positive
import Theorems.Thm_MetricCodes_Spherical_HigherYoungAllRankOrthogonalTensorPieriSourceSignatureInjectivity_raiseWeight_ne_loweredInternalYoungWeight

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
open MetricCodes.Spherical.HigherYoungAllRankOrthogonalTensorPieriSourceSignatureInjectivity
open MetricCodes.Spherical.HigherChannel
open MetricCodes.Spherical.HigherHarmonicYoung.MixedSignature
open MetricCodes.Spherical.HigherYoungPenultimateRowProjectedLower
namespace MetricCodes.Spherical.HigherYoungAllRankOrthogonalTensorPieriSourceSignatureInjectivity
theorem _root_.solution {r : ℕ}
    (lam : Fin (r + 1) → ℕ) :
    Function.Injective (paddedPieriSource lam) := by
  intro i j hij
  cases i with
  | inl a =>
      cases j with
      | inl b =>
          have hab : a.val = b.val :=
            raiseWeight_row_injective lam hij
          exact congrArg Sum.inl (Subtype.ext hab)
      | inr b =>
          exact False.elim
            (raiseWeight_ne_loweredInternalYoungWeight lam a.val b.val hij)
  | inr a =>
      cases j with
      | inl b =>
          exact False.elim
            (raiseWeight_ne_loweredInternalYoungWeight lam b.val a.val
              hij.symm)
      | inr b =>
          have hab : a.val = b.val :=
            loweredInternalYoungWeight_row_injective_of_positive lam
              a.property.1 hij
          exact congrArg Sum.inr (Subtype.ext hab)
end MetricCodes.Spherical.HigherYoungAllRankOrthogonalTensorPieriSourceSignatureInjectivity
