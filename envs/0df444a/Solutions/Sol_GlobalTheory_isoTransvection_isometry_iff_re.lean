-- Prove2me | solution 1 for GlobalTheory.isoTransvection.isometry_iff_re
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:38:52.962131+00:00
-- url     : https://prove2.me/submissions/1bc361cd-953d-40f6-8c2d-29e23ce7c3d0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_DifferentiableToContinuousLinearMap
import Theorems.Thm_GlobalTheory_isoTransvection_isometry_iff

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
open GlobalTheory.isoTransvection
variable {W : Type*} [AddCommGroup W] [Module ℂ W] {h : W →ₗ[ℂ] W →ₗ⋆[ℂ] ℂ} (x : W)
  (hx : h x x = 0)
namespace GlobalTheory.isoTransvection
theorem _root_.solution (hh : ∀ u v, h v u = star (h u v)) (hx0 : ∃ v, h v x ≠ 0) (b : ℂ) :
    (∀ u v, h (isoTransvection h x hx b u) (isoTransvection h x hx b v) = h u v)
      ↔ b.re = 0 := by
  rw [isometry_iff x hx hh hx0, Complex.star_def, Complex.add_conj]
  simp
end GlobalTheory.isoTransvection
