-- Prove2me | solution 1 for GlobalTheory.CosetEuler.hasSum_step
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:13:35.19193+00:00
-- url     : https://prove2.me/submissions/1abb5752-1adc-4f9b-a8cd-3f5b380e7181

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
theorem _root_.solution {E : Type} [NormedField E] (f : G → E)
    (hf : ∀ g ∈ H, ∀ k ∈ J, f (g * k) = f g)
    (c : E) (T : Finset ι) (v : ι) (hv : v ∉ T)
    (hfib : ∀ g ∈ H, p v g = 1 → HasSum (fun a : L v ⧸ K v => f (g * e v a.out)) (c * f g))
    {s : E} (hs : HasSum ((offSet p K J H T).indicator fun y => f ((y.out : H) : G)) s)
    (hsum : Summable ((offSet p K J H (insert v T)).indicator fun y => f ((y.out : H) : G))) :
    HasSum ((offSet p K J H (insert v T)).indicator fun y => f ((y.out : H) : G)) (c * s) := by
  have hinj := stepMap_injective hJH hpe hpe' he hJ T v hv
  have hzero := zero_off_stepMap hJH hpe hpe' he hJ f T v
  have h1 := (hinj.hasSum_iff hzero).2 hsum.hasSum
  have h2 : HasSum (fun y : offSet p K J H T => c * f ((y.1.out : H) : G))
      (∑' y, (offSet p K J H (insert v T)).indicator (fun y => f ((y.out : H) : G)) y) := by
    refine h1.prod_fiberwise fun y => ?_
    have := hfib _ (shift_mem he v (y.1.out).2) (p_shift_self hpe v _)
    rw [shift_val hpe hpe' he hJ f hf v (y.1.out).2 (y.2 v hv)] at this
    simpa only [comp_stepMap hJH hpe hpe' he hJ f hf] using this
  have h3 : HasSum (fun y : offSet p K J H T => c * f ((y.1.out : H) : G)) (c * s) :=
    (hasSum_subtype_iff_indicator.2 hs).mul_left c
  rw [h2.unique h3] at h1
  exact (hinj.hasSum_iff hzero).1 h1
end GlobalTheory.CosetEuler
