-- Prove2me | solution 1 for GlobalTheory.QCoh.isLocalizedModule_resLinear
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:05:36.341938+00:00
-- url     : https://prove2.me/submissions/e15e7c13-6ba0-4537-a6de-8b6d482a599e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsQuasicoherentOfForallExistsAffine
import Theorems.Thm_GlobalTheory_QCoh_isLocalizedModule_resBasicOpen

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
variable [F.IsQuasicoherent]
namespace GlobalTheory.QCoh
theorem _root_.solution (hU : IsAffineOpen U) (f : Γ(X, U)) (h : V ≤ U)
    (hV : V = X.basicOpen f) :
    letI := resModule F h
    IsLocalizedModule.Away f (resLinear F h) := by
  subst hV
  exact isLocalizedModule_resBasicOpen F hU f
end GlobalTheory.QCoh
