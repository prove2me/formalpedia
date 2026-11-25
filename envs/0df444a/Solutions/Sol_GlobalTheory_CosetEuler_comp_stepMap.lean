-- Prove2me | solution 1 for GlobalTheory.CosetEuler.comp_stepMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:07:28.35468+00:00
-- url     : https://prove2.me/submissions/ac7aaf03-93b5-45e4-a825-759bba109ea5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasSumCosetsEulerProduct
import Theorems.Thm_GlobalTheory_CosetEuler_inv_out
import Theorems.Thm_GlobalTheory_CosetEuler_stepMap_mem

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
theorem _root_.solution {E : Type} [Zero E] (f : G → E) (hf : ∀ g ∈ H, ∀ k ∈ J, f (g * k) = f g)
    (T : Finset ι) (v : ι) (x : offSet p K J H T × (L v ⧸ K v)) :
    ((offSet p K J H (insert v T)).indicator (fun y => f ((y.out : H) : G)) ∘
      stepMap e p K J H he T v) x = f (shift e p v ((x.1.1.out : H) : G) * e v x.2.out) := by
  simp only [Function.comp, Set.indicator_of_mem (stepMap_mem hJH hpe hpe' he hJ T v x)]
  exact inv_out hJH f hf _
end GlobalTheory.CosetEuler
