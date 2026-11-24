-- Prove2me | solution 1 for GlobalTheory.QCoh.isBaseChange_germLinear
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:31:14.746388+00:00
-- url     : https://prove2.me/submissions/e83099c9-c9ce-4525-a54a-4a08edea5472

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsQuasicoherentOfForallExistsAffine
import Theorems.Thm_GlobalTheory_QCoh_isLocalizedModule_germLinear

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite TensorProduct
universe u
noncomputable section
open GlobalTheory GlobalTheory.QCoh
variable {X : Scheme.{u}} (F : X.Modules) {U V W : X.Opens}
namespace GlobalTheory.QCoh
theorem _root_.solution [F.IsQuasicoherent] (hU : IsAffineOpen U) (x : U) :
    IsBaseChange (X.presheaf.stalk (x : X)) (germLinear F x) :=
  haveI := hU.isLocalization_stalk x
  (isLocalizedModule_iff_isBaseChange (hU.primeIdealOf x).asIdeal.primeCompl _ _).mp
    (isLocalizedModule_germLinear F hU x)
end GlobalTheory.QCoh
