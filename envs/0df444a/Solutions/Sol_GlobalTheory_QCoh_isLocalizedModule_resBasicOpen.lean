-- Prove2me | solution 1 for GlobalTheory.QCoh.isLocalizedModule_resBasicOpen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T20:50:23.400385+00:00
-- url     : https://prove2.me/submissions/6925ff47-6421-453b-9710-53a0026c07da

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsQuasicoherentOfForallExistsAffine
import Theorems.Thm_GlobalTheory_QCoh_isQuasicoherent_restrict_fromSpec_iff

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
theorem _root_.solution [F.IsQuasicoherent] (hU : IsAffineOpen U) (f : Γ(X, U)) :
    IsLocalizedModule.Away f (resBasicOpen F f) :=
  (isQuasicoherent_restrict_fromSpec_iff F hU).mp inferInstance f
end GlobalTheory.QCoh
