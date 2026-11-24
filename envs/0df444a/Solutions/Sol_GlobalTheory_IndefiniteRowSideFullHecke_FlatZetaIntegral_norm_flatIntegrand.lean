-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.FlatZetaIntegral.norm_flatIntegrand
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T17:38:40.618188+00:00
-- url     : https://prove2.me/submissions/e69d7955-1dc1-4682-89d6-70a228da7a5d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TorsionBlocks_FlatZetaIntegral

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Set
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.FlatZetaIntegral
variable {X : Type} [MeasurableSpace X]
omit [MeasurableSpace X]
namespace GlobalTheory.IndefiniteRowSideFullHecke.FlatZetaIntegral
theorem _root_.solution (f : X → ℂ) {a : X → ℝ} (s₀ s : ℂ) {x : X} (hx : 0 < a x) :
    ‖flatIntegrand f a s₀ s x‖ = ‖f x‖ * a x ^ (s.re - s₀.re) := by
  rw [flatIntegrand, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx, Complex.sub_re]
end GlobalTheory.IndefiniteRowSideFullHecke.FlatZetaIntegral
