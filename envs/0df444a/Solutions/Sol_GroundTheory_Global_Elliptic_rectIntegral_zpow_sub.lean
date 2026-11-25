-- Prove2me | solution 1 for GroundTheory.Global.Elliptic.rectIntegral_zpow_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:13:31.948412+00:00
-- url     : https://prove2.me/submissions/1e127e4f-43b7-4695-994f-7bff44d44693

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_RectangleIntegral
import Theorems.Thm_GroundTheory_Global_Elliptic_rectIntegral_eq_zero_of_hasDerivAt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open Complex Set Real MeasureTheory Filter Topology intervalIntegral
open scoped Interval
noncomputable section
open GroundTheory GroundTheory.Global
open GroundTheory.Global.Elliptic
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable {z w : ℂ}
namespace GroundTheory.Global.Elliptic
theorem _root_.solution {p : ℂ} {n : ℤ} (hn : n ≠ -1) (hp : p ∉ rectBoundary z w) :
    rectIntegral (fun u ↦ (u - p) ^ n) z w = 0 := by
  have hn' : (n : ℂ) + 1 ≠ 0 := by exact_mod_cast (show n + 1 ≠ 0 by omega)
  have hup : ∀ u ∈ rectBoundary z w, u - p ≠ 0 := fun u hu h ↦ hp (sub_eq_zero.1 h ▸ hu)
  refine rectIntegral_eq_zero_of_hasDerivAt (F := fun u ↦ (u - p) ^ (n + 1) / ((n : ℂ) + 1))
    (fun u hu ↦ ?_) ?_
  · have h1 : HasDerivAt (fun u : ℂ ↦ u - p) 1 u := (hasDerivAt_id u).sub_const p
    have h2 := ((hasDerivAt_zpow (n + 1) (u - p) (Or.inl (hup u hu))).comp u h1).div_const
      ((n : ℂ) + 1)
    refine h2.congr_deriv ?_
    rw [add_sub_cancel_right]
    push_cast
    field_simp
  · exact continuousOn_of_forall_continuousAt fun u hu ↦
      ((continuousAt_id.sub continuousAt_const).zpow₀ n (Or.inl (hup u hu)))
end GroundTheory.Global.Elliptic
