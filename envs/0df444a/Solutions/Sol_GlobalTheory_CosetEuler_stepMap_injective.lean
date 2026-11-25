-- Prove2me | solution 1 for GlobalTheory.CosetEuler.stepMap_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:58:05.755059+00:00
-- url     : https://prove2.me/submissions/4206383e-1bc3-4cc9-ac83-ff5b2609ab27

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasSumCosetsEulerProduct
import Theorems.Thm_GlobalTheory_CosetEuler_cls_eq
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
theorem _root_.solution (T : Finset ι) (v : ι) (hv : v ∉ T) :
    Function.Injective (stepMap e p K J H he T v) := by
  rintro ⟨y1, a1⟩ ⟨y2, a2⟩ h
  have h' := (cls_eq hJ _ _).1 h
  have ha : a1 = a2 := by
    have := h' v
    simp only [map_mul, p_shift_self hpe, hpe, one_mul] at this
    rw [← QuotientGroup.out_eq' a1, ← QuotientGroup.out_eq' a2]
    exact QuotientGroup.eq.2 this
  have hy : y1 = y2 := by
    apply Subtype.ext
    rw [← QuotientGroup.out_eq' y1.1, ← QuotientGroup.out_eq' y2.1]
    refine (cls_eq hJ _ _).2 fun u => ?_
    rcases eq_or_ne u v with rfl | hu
    · exact (K u).mul_mem ((K u).inv_mem (y1.2 u hv)) (y2.2 u hv)
    · have := h' u
      simpa only [map_mul, p_shift_ne hpe' hu, hpe' u v hu, mul_one] using this
  exact Prod.ext hy ha
end GlobalTheory.CosetEuler
