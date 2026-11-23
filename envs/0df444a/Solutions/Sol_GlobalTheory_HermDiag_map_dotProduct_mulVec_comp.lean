-- Prove2me | solution 1 for GlobalTheory.HermDiag.map_dotProduct_mulVec_comp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:57:11.897711+00:00
-- url     : https://prove2.me/submissions/946954b4-6fcc-4602-9af7-7868bfcc812d

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_ExistsOrthogonalBasisDotProductApplyEq
import Theorems.Thm_GlobalTheory_HermDiag_dotProduct_mulVec_comp_eq_sum

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
theorem _root_.solution (hc : ∀ t, c (c t) = t) {G : Matrix n n E}
    (hG : ∀ a b, c (G a b) = G b a) (x y : n → E) :
    c (x ⬝ᵥ G *ᵥ (c ∘ y)) = y ⬝ᵥ G *ᵥ (c ∘ x) := by
  simp only [dotProduct_mulVec_comp_eq_sum, map_sum, map_mul, hc, hG]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring
end GlobalTheory.HermDiag
