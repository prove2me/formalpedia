-- Prove2me | solution 1 for GroundTheory.Global.Elliptic.swap_dslope_comp_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:07:17.907863+00:00
-- url     : https://prove2.me/submissions/2a86e068-ddee-450f-bced-0ac7004b8f61

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_Residue

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open Complex Filter Topology Set
noncomputable section
open GroundTheory GroundTheory.Global
open GroundTheory.Global.Elliptic
namespace GroundTheory.Global.Elliptic
theorem _root_.solution {G : ℂ → ℂ} {c w₀ : ℂ} (hc : c ≠ 0)
    (hG : DifferentiableAt ℂ G (c * w₀)) :
    Function.swap dslope w₀ (fun w ↦ G (c * w)) =
      fun w ↦ c * Function.swap dslope (c * w₀) G (c * w) := by
  funext w
  show dslope (fun w ↦ G (c * w)) w₀ w = c * dslope G (c * w₀) (c * w)
  rcases eq_or_ne w w₀ with rfl | hw
  · rw [dslope_same, dslope_same]
    have := hG.hasDerivAt.comp w ((hasDerivAt_id w).const_mul c)
    exact this.deriv.trans (by ring)
  · have hcw : c * w ≠ c * w₀ := fun h ↦ hw (mul_left_cancel₀ hc h)
    have h1 : w - w₀ ≠ 0 := sub_ne_zero.2 hw
    have h2 : c * w - c * w₀ ≠ 0 := sub_ne_zero.2 hcw
    rw [dslope_of_ne _ hw, dslope_of_ne _ hcw, slope_def_field, slope_def_field]
    rw [show c * w - c * w₀ = c * (w - w₀) by ring]
    field_simp
end GroundTheory.Global.Elliptic
