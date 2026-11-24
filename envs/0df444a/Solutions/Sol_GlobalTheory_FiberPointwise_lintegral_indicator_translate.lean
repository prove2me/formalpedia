-- Prove2me | solution 1 for GlobalTheory.FiberPointwise.lintegral_indicator_translate
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T15:00:46.104828+00:00
-- url     : https://prove2.me/submissions/19b99796-ef0e-496f-a3da-72acb73fea92

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_VanishingOfProjectionSupport

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.FiberPointwise
namespace GlobalTheory.FiberPointwise
theorem _root_.solution {X : Type} [AddCommGroup X] [MeasurableSpace X] [MeasurableAdd X]
    (μ : Measure X) [μ.IsAddRightInvariant] (P : X →+ X)
    (h : X → ENNReal) (hinv : ∀ x z, P z = z → h (x + z) = h x) (S : Set X) (z : X) (hz : P z = z) :
    ∫⁻ x, Set.indicator {x | P x - z ∈ S} h x ∂μ = ∫⁻ x, Set.indicator {x | P x ∈ S} h x ∂μ := by
  rw [← lintegral_add_right_eq_self (μ := μ) _ z]
  congr 1
  funext x
  show Set.indicator {x | P x - z ∈ S} h (x + z) = Set.indicator {x | P x ∈ S} h x
  have hx : (P (x + z) - z ∈ S) ↔ (P x ∈ S) := by rw [map_add, hz, add_sub_cancel_right]
  by_cases hxs : P x ∈ S
  · rw [Set.indicator_of_mem (show x + z ∈ {x | P x - z ∈ S} from hx.mpr hxs),
      Set.indicator_of_mem (show x ∈ {x | P x ∈ S} from hxs), hinv x z hz]
  · rw [Set.indicator_of_notMem (show x + z ∉ {x | P x - z ∈ S} from fun h' => hxs (hx.mp h')),
      Set.indicator_of_notMem (show x ∉ {x | P x ∈ S} from hxs)]
end GlobalTheory.FiberPointwise
