-- Prove2me | solution 1 for GlobalTheory.QCoh.fromSpec_appIso_inv_res
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:41:33.86412+00:00
-- url     : https://prove2.me/submissions/55cddb09-7e46-470d-b774-019ddedcb584

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsQuasicoherentOfForallExistsAffine
import Theorems.Thm_GlobalTheory_QCoh_resLinear_apply
import Theorems.Thm_GlobalTheory_QCoh_resBasicOpen_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.QCoh.resLinear_apply
attribute [local simp] GlobalTheory.QCoh.resBasicOpen_apply

set_option autoImplicit false
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite TensorProduct
universe u
noncomputable section
open GlobalTheory GlobalTheory.QCoh
variable {X : Scheme.{u}} (F : X.Modules) {U V W : X.Opens}
variable (hU : IsAffineOpen U)
namespace GlobalTheory.QCoh
theorem _root_.solution (W : (Spec Γ(X, U)).Opens) (r : Γ(X, U)) :
    (hU.fromSpec.appIso W).inv
      ((Spec Γ(X, U)).presheaf.map W.leTop.op ((Scheme.ΓSpecIso Γ(X, U)).inv r)) =
      X.presheaf.map (homOfLE (fromSpec_image_le hU W)).op r := by
  have : X.presheaf.map (homOfLE (fromSpec_image_le hU W)).op ≫ (hU.fromSpec.appIso W).hom =
      (Scheme.ΓSpecIso Γ(X, U)).inv ≫ (Spec Γ(X, U)).presheaf.map W.leTop.op := by
    rw [Scheme.Hom.appIso_hom', Scheme.Hom.map_appLE, Scheme.Hom.appLE, hU.fromSpec_app_self,
      Category.assoc, ← Functor.map_comp]
    rfl
  rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, ← Category.assoc, ← this]
  simp
end GlobalTheory.QCoh
