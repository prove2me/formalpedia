-- Prove2me | solution 1 for GlobalTheory.HermDiag.exists_congr_diagonal_col_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T18:59:28.73747+00:00
-- url     : https://prove2.me/submissions/9b26f0ed-c7db-4d95-bdd9-c61128591e97

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_ExistsOrthogonalBasisDotProductApplyEq
import Theorems.Thm_GlobalTheory_HermDiag_map_dotProduct_mulVec_comp
import Theorems.Thm_GlobalTheory_HermDiag_exists_orthogonal_basis_dotProduct_apply_eq
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
    {G : Matrix n n E} (hG : ∀ a b, c (G a b) = G b a) {x : n → E}
    (hx : x ⬝ᵥ G *ᵥ (c ∘ x) ≠ 0) (i₀ : n) :
    ∃ (P : Matrix n n E) (d : n → E), P.det ≠ 0 ∧ Pᵀ * G * P.map c = Matrix.diagonal d ∧
      (∀ i, c (d i) = d i) ∧ (G.det ≠ 0 → ∀ i, d i ≠ 0) ∧
      (∀ k, P k i₀ = x k) ∧ d i₀ = x ⬝ᵥ G *ᵥ (c ∘ x) := by
  obtain ⟨v, hv0, hv⟩ := exists_orthogonal_basis_dotProduct_apply_eq h2 hc hG hx i₀
  have hd := congr_diagonal_of_orthogonal c v hv
  exact ⟨_, _, det_of_basis_ne_zero v, hd, fun i => map_dotProduct_mulVec_comp hc hG _ _,
    ne_zero_of_congr_diagonal (det_of_basis_ne_zero v) hd, fun k => by simp [hv0],
    by simp only [hv0]⟩
end GlobalTheory.HermDiag
