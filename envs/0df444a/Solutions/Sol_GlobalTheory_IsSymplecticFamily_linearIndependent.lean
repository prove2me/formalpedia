-- Prove2me | solution 1 for GlobalTheory.IsSymplecticFamily.linearIndependent
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:37:15.162111+00:00
-- url     : https://prove2.me/submissions/c174a97f-f7cb-4866-88f4-6248e3caeaf7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DualRestrictSurjectiveOfIsTorsionFreeQuotient
import Theorems.Thm_GlobalTheory_IsSymplecticFamily_apply_left_sum
import Theorems.Thm_GlobalTheory_IsSymplecticFamily_apply_sum_right

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Function
open GlobalTheory
variable {R M ι : Type*} [CommRing R] [AddCommGroup M] [Module R M]
open GlobalTheory.IsSymplecticFamily
variable {B : LinearMap.BilinForm R M} {e f : ι → M} {d : ι → R}
namespace GlobalTheory.IsSymplecticFamily
theorem _root_.solution [Finite ι] [IsDomain R] (h : IsSymplecticFamily B e f d)
    (hd : ∀ i, d i ≠ 0) : LinearIndependent R (Sum.elim e f) := by
  have := Fintype.ofFinite ι
  rw [Fintype.linearIndependent_iff]
  intro c hc i
  cases i with
  | inl k =>
    have := h.apply_sum_right c k
    rw [hc] at this
    simpa [hd k] using this.symm
  | inr k =>
    have := h.apply_left_sum c k
    rw [hc] at this
    simpa [hd k] using this.symm
end GlobalTheory.IsSymplecticFamily
