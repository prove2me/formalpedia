-- Prove2me | solution 1 for GlobalTheory.CosetEuler.zero_off_stepMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:08:07.714881+00:00
-- url     : https://prove2.me/submissions/a2ccc0bb-10f1-4f76-bbb0-c57ab3a7ae66

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasSumCosetsEulerProduct
import Theorems.Thm_GlobalTheory_CosetEuler_mem_range_stepMap

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
theorem _root_.solution {E : Type} [Zero E] (f : G → E) (T : Finset ι) (v : ι) :
    ∀ x ∉ Set.range (stepMap e p K J H he T v),
      (offSet p K J H (insert v T)).indicator (fun y => f ((y.out : H) : G)) x = 0 :=
  fun x hx => Set.indicator_of_notMem (fun h => hx (mem_range_stepMap hJH hpe hpe' he hJ T v x h)) _
end GlobalTheory.CosetEuler
