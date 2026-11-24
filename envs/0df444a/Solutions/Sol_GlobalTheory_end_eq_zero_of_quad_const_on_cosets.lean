-- Prove2me | solution 1 for GlobalTheory.end_eq_zero_of_quad_const_on_cosets
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:46:22.01173+00:00
-- url     : https://prove2.me/submissions/6731e653-060d-4b7f-83cf-87c0ea9ed7ec

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DualRestrictSurjectiveOfIsTorsionFreeQuotient
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_BaseOver
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsNeZeroHalfStandardAltFormConstOfExponentOn
import Theorems.Thm_GlobalTheory_bilin_eq_zero_of_const_on_cosets
import Theorems.Thm_GlobalTheory_orthogonalQuotientForm_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.orthogonalQuotientForm_mk



set_option autoImplicit false
open Function
open GlobalTheory
variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
namespace GlobalTheory
theorem _root_.solution (h2 : IsUnit (2 : R)) {r : R} (hr : IsNilpotent r)
    (ω : LinearMap.BilinForm R M) (hω : Injective ω) (S : M →ₗ[R] M)
    (hS : ∀ x y, ω (S x) y = ω (S y) x) (u : Rˣ) (q : M → R)
    (hq : ∀ x, 2 * q x = u * ω (S x) x) (T : Set M)
    (hT : ∀ x, ∃ t ∈ T, ∃ a, x = t + r • a) (c : R) (hc : ∀ t ∈ T, q t = c) : S = 0 := by
  have h : (ω ∘ₗ S : LinearMap.BilinForm R M) = 0 := by
    refine bilin_eq_zero_of_const_on_cosets h2 hr (ω ∘ₗ S) hS T hT (↑u⁻¹ * (2 * c)) fun t ht => ?_
    rw [← hc t ht, hq, Units.inv_mul_cancel_left]
    rfl
  ext x
  exact hω ((LinearMap.congr_fun h x).trans (by simp))
end GlobalTheory
