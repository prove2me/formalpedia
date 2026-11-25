-- Prove2me | solution 1 for GlobalTheory.CosetEuler.mem_range_stepMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:03:03.719841+00:00
-- url     : https://prove2.me/submissions/81e4e6f0-a775-49fd-adfd-96a5762e5af9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasSumCosetsEulerProduct
import Theorems.Thm_GlobalTheory_CosetEuler_cls_eq
import Theorems.Thm_GlobalTheory_CosetEuler_out_mul
import Theorems.Thm_GlobalTheory_CosetEuler_mem_offSet_mk
import Theorems.Thm_GlobalTheory_CosetEuler_p_shift_self
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
theorem _root_.solution (T : Finset ι) (v : ι) (y : H ⧸ J.subgroupOf H)
    (hy : y ∈ offSet p K J H (insert v T)) : y ∈ Set.range (stepMap e p K J H he T v) := by
  set g : H := y.out with hg
  let h : H := ⟨shift e p v g, shift_mem he v g.2⟩
  have hh : (h : H ⧸ J.subgroupOf H) ∈ offSet p K J H T := by
    refine (mem_offSet_mk hJH hJ _ _).2 fun u hu => ?_
    rcases eq_or_ne u v with rfl | huv
    · show p u (shift e p u g) ∈ K u
      rw [p_shift_self hpe]; exact (K u).one_mem
    · show p u (shift e p v g) ∈ K u
      rw [p_shift_ne hpe' huv]
      exact hy u (by simp [huv, hu])
  refine ⟨(⟨_, hh⟩, (p v g : L v ⧸ K v)), ?_⟩
  rw [← QuotientGroup.out_eq' y]
  refine (cls_eq hJ _ _).2 fun u => ?_
  obtain ⟨k, hk, hk'⟩ := out_mul hJH h
  rcases eq_or_ne u v with rfl | huv
  · simp only [map_mul, p_shift_self hpe, hpe, one_mul]
    exact QuotientGroup.eq.1 (QuotientGroup.out_eq' (p u g : L u ⧸ K u))
  · simp only [map_mul, p_shift_ne hpe' huv, hpe' u v huv, mul_one, hk']
    have e1 : p u (h : G) = p u (y.out : G) := p_shift_ne hpe' huv _
    simp only [mul_inv_rev, mul_assoc, e1, inv_mul_cancel, mul_one]
    exact (K u).inv_mem ((hJ k (hJH hk)).1 hk u)
end GlobalTheory.CosetEuler
