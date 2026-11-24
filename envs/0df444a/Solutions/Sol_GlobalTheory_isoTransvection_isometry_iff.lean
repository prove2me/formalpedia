-- Prove2me | solution 1 for GlobalTheory.isoTransvection.isometry_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:11:43.96915+00:00
-- url     : https://prove2.me/submissions/9b4bb54c-3a20-4092-8738-678b67b53e12

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_DifferentiableToContinuousLinearMap
import Theorems.Thm_GlobalTheory_isoTransvection_form_apply_diag
import Theorems.Thm_GlobalTheory_isoTransvection_isometry

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
namespace GlobalTheory.isoTransvection
theorem _root_.solution [NoZeroDivisors R] (hh : ∀ u v, h v u = star (h u v))
    (hx0 : ∃ v, h v x ≠ 0) (b : R) :
    (∀ u v, h (isoTransvection h x hx b u) (isoTransvection h x hx b v) = h u v)
      ↔ b + star b = 0 := by
  refine ⟨fun H => ?_, fun hb => isometry x hx hh hb⟩
  obtain ⟨v, hv⟩ := hx0
  have := H v v
  rw [form_apply_diag x hx hh, add_eq_left] at this
  simpa [hv] using this
end GlobalTheory.isoTransvection
