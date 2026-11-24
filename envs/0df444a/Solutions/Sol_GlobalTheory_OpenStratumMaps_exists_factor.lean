-- Prove2me | solution 1 for GlobalTheory.OpenStratumMaps.exists_factor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:53:31.550027+00:00
-- url     : https://prove2.me/submissions/4b63fb44-f6d0-4a93-a8ab-d6be4cb94657

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_WeilTensorLiftConclusion
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_BoundaryVanishingPullback
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_OpenClosedSequences
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_DeterminedOnOpenStratum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL
open scoped TensorProduct
open GlobalTheory GlobalTheory.OpenStratumMaps
variable {F G H V W U : Type} [Field F] [Group G] [Group H] [AddCommGroup V] [Module F V]
  [AddCommGroup W] [Module F W] [AddCommGroup U] [Module F U]
namespace GlobalTheory.OpenStratumMaps
theorem _root_.solution {ρ : Representation F G V} {σ : Representation F G W} {τ : Representation F G U}
    (f : ρ.IntertwiningMap σ) (hf : Function.Surjective f) (q : ρ.IntertwiningMap τ)
    (hq : ∀ v, f v = 0 → q v = 0) : ∃ q' : σ.IntertwiningMap τ, ∀ v, q' (f v) = q v := by
  obtain ⟨s, hs⟩ := f.toLinearMap.exists_rightInverse_of_surjective (LinearMap.range_eq_top.2 hf)
  have hs' : ∀ w, f (s w) = w := fun w => congr($hs w)
  have key : ∀ v, q (s (f v)) = q v := fun v => by
    rw [← sub_eq_zero, ← map_sub]
    apply hq
    rw [map_sub, hs', sub_self]
  refine ⟨⟨q.toLinearMap ∘ₗ s, fun g => ?_⟩, key⟩
  ext w
  obtain ⟨v, rfl⟩ := hf w
  show q (s (σ g (f v))) = τ g (q (s (f v)))
  rw [← f.isIntertwining, key, key, q.isIntertwining]
end GlobalTheory.OpenStratumMaps
