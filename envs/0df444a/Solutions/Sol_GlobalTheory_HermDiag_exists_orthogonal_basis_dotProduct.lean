-- Prove2me | solution 1 for GlobalTheory.HermDiag.exists_orthogonal_basis_dotProduct
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T18:39:55.728676+00:00
-- url     : https://prove2.me/submissions/7ad28bc0-8dbe-4520-a468-a1740a526b96

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_ExistsOrthogonalBasisDotProductApplyEq
import Theorems.Thm_GlobalTheory_HermDiag_exists_orthogonal_basis
import Theorems.Thm_GlobalTheory_HermDiag_map_dotProduct_mulVec_comp
import Theorems.Thm_P2M_GlobalTheory_HermDiag_toLinearMap_____eq_dotProduct_72a26b3ab9da

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
    ∃ v : Basis n E (n → E), ∀ i j, i ≠ j → v i ⬝ᵥ G *ᵥ (c ∘ v j) = 0 := by
  obtain ⟨v, hv⟩ := exists_orthogonal_basis (n := n) h2
    (B := Matrix.toLinearMapₛₗ₂' E (RingHom.id E) c G)
    (fun x y => by
      simp only [toLinearMapₛₗ₂'_eq_dotProduct, map_dotProduct_mulVec_comp hc hG])
    (Module.finrank_fintype_fun_eq_card E)
  exact ⟨v, by simpa only [toLinearMapₛₗ₂'_eq_dotProduct] using hv⟩
end GlobalTheory.HermDiag
