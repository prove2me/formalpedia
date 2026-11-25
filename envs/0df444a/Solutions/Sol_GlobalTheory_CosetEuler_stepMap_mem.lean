-- Prove2me | solution 1 for GlobalTheory.CosetEuler.stepMap_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:02:53.066136+00:00
-- url     : https://prove2.me/submissions/6097984f-6388-42f3-8fd6-3928fb3da5ea

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasSumCosetsEulerProduct
import Theorems.Thm_GlobalTheory_CosetEuler_mem_offSet_mk
import Theorems.Thm_GlobalTheory_CosetEuler_p_shift_ne

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
theorem _root_.solution (T : Finset ι) (v : ι) (x : offSet p K J H T × (L v ⧸ K v)) :
    stepMap e p K J H he T v x ∈ offSet p K J H (insert v T) := by
  refine (mem_offSet_mk hJH hJ _ _).2 fun u hu => ?_
  rw [Finset.mem_insert, not_or] at hu
  simp only [map_mul, p_shift_ne hpe' hu.1, hpe' u v hu.1, mul_one]
  exact x.1.2 u hu.2
end GlobalTheory.CosetEuler
