-- Prove2me | solution 1 for GlobalTheory.QCoh.restrict_fromSpec_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:57:50.028175+00:00
-- url     : https://prove2.me/submissions/84f9e7d2-6268-4f27-8f0d-185af4f50917

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsQuasicoherentOfForallExistsAffine
import Theorems.Thm_GlobalTheory_QCoh_fromSpec_appIso_inv_res

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
variable (hU : IsAffineOpen U)
namespace GlobalTheory.QCoh
theorem _root_.solution (W : (Spec Γ(X, U)).Opens) (r : Γ(X, U))
    (s : Γ(F.restrict hU.fromSpec, W)) :
    (F.restrictAppIso hU.fromSpec W).hom (r • s) =
      X.presheaf.map (homOfLE (fromSpec_image_le hU W)).op r •
        (F.restrictAppIso hU.fromSpec W).hom s := by
  rw [← fromSpec_appIso_inv_res]
  rfl
end GlobalTheory.QCoh
