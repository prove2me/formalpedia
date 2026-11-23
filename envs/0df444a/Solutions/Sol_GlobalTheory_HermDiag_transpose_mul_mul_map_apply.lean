-- Prove2me | solution 1 for GlobalTheory.HermDiag.transpose_mul_mul_map_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:37:43.180603+00:00
-- url     : https://prove2.me/submissions/816f2a49-210e-4101-bd01-f97987ad8111

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
theorem _root_.solution {m : Type*} (c : E → E) (G : Matrix n n E) (P : Matrix n m E)
    (a b : m) :
    (Pᵀ * G * P.map c) a b = (fun k => P k a) ⬝ᵥ G *ᵥ (c ∘ fun k => P k b) := by
  rw [Matrix.mul_assoc]
  rfl
end GlobalTheory.HermDiag
