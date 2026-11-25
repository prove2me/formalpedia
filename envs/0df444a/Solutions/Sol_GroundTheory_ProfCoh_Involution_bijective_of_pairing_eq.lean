-- Prove2me | solution 1 for GroundTheory.ProfCoh.Involution.bijective_of_pairing_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T07:21:37.838703+00:00
-- url     : https://prove2.me/submissions/d5e20e3d-f75f-40d2-a616-abd7c09808e2

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_TorsionDualFinite
import Definitions.Def_GroundTheory_ProfiniteCohomology_RealPlaces_InvolutionDuality
import Theorems.Thm_GroundTheory_ProfCoh_Involution_tateQuotCongr_mk
import Theorems.Thm_GroundTheory_ProfCoh_QZDual_addCharEquiv_apply
import Theorems.Thm_GroundTheory_ProfCoh_QZDual_eval_apply
import Theorems.Thm_GroundTheory_ProfCoh_QZ_addCharEquiv_apply
import Theorems.Thm_GroundTheory_ProfCoh_QZ_evalHom_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.ProfCoh.QZ.addCharEquiv_apply
attribute [local simp] GroundTheory.ProfCoh.QZ.evalHom_apply
attribute [local simp] GroundTheory.ProfCoh.QZDual.addCharEquiv_apply
attribute [local simp] GroundTheory.ProfCoh.QZDual.eval_apply


attribute [local simp] GroundTheory.ProfCoh.Involution.tateQuotCongr_mk

set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.ProfCoh
open GroundTheory.ProfCoh.Involution
variable {M : Type*} [AddCommGroup M]
variable {σ : M →+ M}
variable {X Y X' Y' : Type*} [AddCommGroup X] [AddCommGroup Y] [AddCommGroup X'] [AddCommGroup Y']
namespace GroundTheory.ProfCoh.Involution
theorem _root_.solution (P : X →+ Y →+ QZ) (Q : X' →+ Y' →+ QZ) (e : X' ≃+ X) (e' : Y' ≃+ Y)
    (h : ∀ x y, P (e x) (e' y) = Q x y) (hQ : Function.Bijective Q) : Function.Bijective P := by
  let pre : (Y' →+ QZ) ≃ (Y →+ QZ) :=
    { toFun := fun φ => φ.comp e'.symm.toAddMonoidHom
      invFun := fun ψ => ψ.comp e'.toAddMonoidHom
      left_inv := fun φ => by ext; simp
      right_inv := fun ψ => by ext; simp }
  have hP : ⇑P = pre ∘ Q ∘ e.symm := by
    funext x
    ext y
    change P x y = Q (e.symm x) (e'.symm y)
    rw [← h, e.apply_symm_apply, e'.apply_symm_apply]
  rw [hP]
  exact pre.bijective.comp (hQ.comp e.symm.bijective)
end GroundTheory.ProfCoh.Involution
