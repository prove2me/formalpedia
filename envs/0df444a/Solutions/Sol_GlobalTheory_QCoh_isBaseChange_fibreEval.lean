-- Prove2me | solution 1 for GlobalTheory.QCoh.isBaseChange_fibreEval
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T18:21:56.697782+00:00
-- url     : https://prove2.me/submissions/2e2384c7-4cd4-4a0d-899e-f81177f214f9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsLocalizedModuleGermLinearPointOfPrime
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_TopologicalKrullDimLeOfIrreducibleCloseds
import Theorems.Thm_GlobalTheory_QCoh_isBaseChange_germLinear


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite TensorProduct IsLocalRing
universe u
noncomputable section
open GlobalTheory GlobalTheory.QCoh
variable {X : Scheme.{u}} {F G H : X.Modules} {U V : X.Opens}
variable (F)
namespace GlobalTheory.QCoh
theorem _root_.solution [F.IsQuasicoherent] (hU : IsAffineOpen U) (x : U) :
    IsBaseChange (X.residueField (x : X)) (fibreEval F x) :=
  (isBaseChange_germLinear F hU x).comp (TensorProduct.isBaseChange _ _ _)
end GlobalTheory.QCoh
