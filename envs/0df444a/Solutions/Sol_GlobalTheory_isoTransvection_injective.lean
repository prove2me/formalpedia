-- Prove2me | solution 1 for GlobalTheory.isoTransvection.injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:11:42.512539+00:00
-- url     : https://prove2.me/submissions/532480bf-39ed-42ca-a9bc-dc59050b1ab8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_DifferentiableToContinuousLinearMap

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open Module
variable {R M : Type*} [CommRing R] [StarRing R] [AddCommGroup M] [Module R M]
open GlobalTheory.isoTransvection
variable (h : M →ₗ[R] M →ₗ⋆[R] R) (x : M) (hx : h x x = 0)
variable {h}
variable (h)
namespace GlobalTheory.isoTransvection
theorem _root_.solution [IsDomain R] [IsTorsionFree R M] (hx0 : ∃ v, h v x ≠ 0) :
    Function.Injective (isoTransvection h x hx) := by
  obtain ⟨v, hv⟩ := hx0
  have hx1 : x ≠ 0 := by rintro rfl; simp at hv
  intro b b' H
  have : isoTransvection h x hx b v = isoTransvection h x hx b' v := by rw [H]
  rw [apply, apply, add_right_inj] at this
  exact mul_right_cancel₀ hv (smul_left_injective R hx1 this)
end GlobalTheory.isoTransvection
