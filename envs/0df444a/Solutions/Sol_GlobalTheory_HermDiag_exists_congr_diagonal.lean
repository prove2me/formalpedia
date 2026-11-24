-- Prove2me | solution 1 for GlobalTheory.HermDiag.exists_congr_diagonal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T18:55:41.430631+00:00
-- url     : https://prove2.me/submissions/dc71fcee-9bcf-43f6-bbcb-89763c6b15ae

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_ExistsOrthogonalBasisDotProductApplyEq
import Theorems.Thm_GlobalTheory_HermDiag_map_dotProduct_mulVec_comp
import Theorems.Thm_GlobalTheory_HermDiag_exists_orthogonal_basis_dotProduct
import Theorems.Thm_GlobalTheory_HermDiag_det_of_basis_ne_zero
import Theorems.Thm_GlobalTheory_HermDiag_ne_zero_of_congr_diagonal
import Theorems.Thm_GlobalTheory_HermDiag_congr_diagonal_of_orthogonal

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
variable [DecidableEq n]
namespace GlobalTheory.HermDiag
theorem _root_.solution (h2 : (2 : E) ≠ 0) (hc : ∀ t, c (c t) = t)
    {G : Matrix n n E} (hG : ∀ a b, c (G a b) = G b a) :
    ∃ (P : Matrix n n E) (d : n → E), P.det ≠ 0 ∧ Pᵀ * G * P.map c = Matrix.diagonal d ∧
      (∀ i, c (d i) = d i) ∧ (G.det ≠ 0 → ∀ i, d i ≠ 0) := by
  obtain ⟨v, hv⟩ := exists_orthogonal_basis_dotProduct h2 hc hG
  have hd := congr_diagonal_of_orthogonal c v hv
  exact ⟨_, _, det_of_basis_ne_zero v, hd, fun i => map_dotProduct_mulVec_comp hc hG _ _,
    ne_zero_of_congr_diagonal (det_of_basis_ne_zero v) hd⟩
end GlobalTheory.HermDiag
