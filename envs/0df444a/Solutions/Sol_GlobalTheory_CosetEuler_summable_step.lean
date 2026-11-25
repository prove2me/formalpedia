-- Prove2me | solution 1 for GlobalTheory.CosetEuler.summable_step
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:13:28.021831+00:00
-- url     : https://prove2.me/submissions/d86b7b6c-7e7a-4585-8b69-a9cadef90239

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasSumCosetsEulerProduct
import Theorems.Thm_GlobalTheory_CosetEuler_p_shift_self
import Theorems.Thm_GlobalTheory_CosetEuler_shift_val
import Theorems.Thm_GlobalTheory_CosetEuler_stepMap_injective
import Theorems.Thm_GlobalTheory_CosetEuler_comp_stepMap
import Theorems.Thm_GlobalTheory_CosetEuler_zero_off_stepMap

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology
open GlobalTheory GlobalTheory.CosetEuler
variable {G ι : Type} [Group G] {L : ι → Type} [∀ v, Group (L v)]
variable [DecidableEq ι] {e : ∀ v, L v →* G} {p : ∀ v, G →* L v} {K : ∀ v, Subgroup (L v)} {J H : Subgroup G}
    (hJH : J ≤ H) (hpe : ∀ v a, p v (e v a) = a) (hpe' : ∀ u v, u ≠ v → ∀ a, p u (e v a) = 1)
    (he : ∀ v a, e v a ∈ H) (hJ : ∀ g ∈ H, g ∈ J ↔ ∀ v, p v g ∈ K v)
include hJH hpe hpe' he hJ
namespace GlobalTheory.CosetEuler
theorem _root_.solution (f : G → ℝ) (hf0 : ∀ g ∈ H, 0 ≤ f g)
    (hf : ∀ g ∈ H, ∀ k ∈ J, f (g * k) = f g)
    (c : ℝ) (T : Finset ι) (v : ι) (hv : v ∉ T)
    (hfib : ∀ g ∈ H, p v g = 1 → HasSum (fun a : L v ⧸ K v => f (g * e v a.out)) (c * f g))
    {s : ℝ} (hs : HasSum ((offSet p K J H T).indicator fun y => f ((y.out : H) : G)) s) :
    Summable ((offSet p K J H (insert v T)).indicator fun y => f ((y.out : H) : G)) := by
  have hinj := stepMap_injective hJH hpe hpe' he hJ T v hv
  have hzero := zero_off_stepMap hJH hpe hpe' he hJ f T v
  refine (hinj.summable_iff hzero).1 ?_
  have hnn : 0 ≤ (offSet p K J H (insert v T)).indicator (fun y => f ((y.out : H) : G)) ∘
      stepMap e p K J H he T v :=
    fun x => Set.indicator_nonneg (fun y _ => hf0 _ (y.out).2) _
  have hfib' : ∀ y : offSet p K J H T, HasSum
      (fun a : L v ⧸ K v => f (shift e p v ((y.1.out : H) : G) * e v a.out))
      (c * f ((y.1.out : H) : G)) := fun y => by
    have := hfib _ (shift_mem he v (y.1.out).2) (p_shift_self hpe v _)
    rwa [shift_val hpe hpe' he hJ f hf v (y.1.out).2 (y.2 v hv)] at this
  refine (summable_prod_of_nonneg hnn).2 ⟨fun y => ?_, ?_⟩
  · simpa only [comp_stepMap hJH hpe hpe' he hJ f hf] using (hfib' y).summable
  · simp only [comp_stepMap hJH hpe hpe' he hJ f hf, fun y => (hfib' y).tsum_eq]
    exact ((hasSum_subtype_iff_indicator.2 hs).mul_left c).summable
end GlobalTheory.CosetEuler
