-- Prove2me | solution 1 for GlobalTheory.HermDiag.dotProduct_mulVec_comp_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:52:59.857323+00:00
-- url     : https://prove2.me/submissions/571b5c6f-487f-46d8-b1a7-d96cbbdecc4a

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
variable {E : Type*} [Field E] {c : E →+* E} {n : Type*} [Fintype n]
namespace GlobalTheory.HermDiag
theorem _root_.solution (c : E → E) (G : Matrix n n E) (x y : n → E) :
    x ⬝ᵥ G *ᵥ (c ∘ y) = ∑ a, ∑ b, x a * G a b * c (y b) := by
  simp only [dotProduct, mulVec, Function.comp_apply, Finset.mul_sum, mul_assoc]
end GlobalTheory.HermDiag
