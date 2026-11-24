-- Prove2me | solution 1 for GlobalTheory.HermDiag.eq_zero_of_apply_self_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T17:27:51.379313+00:00
-- url     : https://prove2.me/submissions/2ea90bb7-11b3-4a71-9b2f-a4495fe90ed8

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_ExistsOrthogonalBasisDotProductApplyEq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.HermDiag
open Module Matrix
variable {E : Type*} [Field E] {c : E →+* E}
namespace GlobalTheory.HermDiag
theorem _root_.solution {V : Type*} [AddCommGroup V] [Module E V]
    (h2 : (2 : E) ≠ 0) {B : V →ₗ[E] V →ₛₗ[c] E} (hB : ∀ x y, c (B x y) = B y x)
    (h0 : ∀ x, B x x = 0) : B = 0 := by
  ext x y
  by_contra hne
  have hne' : B x y ≠ 0 := by simpa using hne
  have h1 : B ((B x y)⁻¹ • x) y = 1 := by
    rw [LinearMap.map_smul, LinearMap.smul_apply, smul_eq_mul, inv_mul_cancel₀ hne']
  have h1' : B y ((B x y)⁻¹ • x) = 1 := by rw [← hB, h1, map_one]
  have h3 := h0 ((B x y)⁻¹ • x + y)
  rw [map_add, LinearMap.map_add₂, LinearMap.map_add₂, h0, h0, h1, h1'] at h3
  apply h2
  linear_combination h3
end GlobalTheory.HermDiag
