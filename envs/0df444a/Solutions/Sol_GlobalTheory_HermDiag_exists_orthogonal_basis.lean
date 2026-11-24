-- Prove2me | solution 1 for GlobalTheory.HermDiag.exists_orthogonal_basis
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T18:23:30.2806+00:00
-- url     : https://prove2.me/submissions/4f7dbd69-605a-4297-8c1a-99a623ab0167

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_ExistsOrthogonalBasisDotProductApplyEq
import Theorems.Thm_GlobalTheory_HermDiag_exists_orthogonal_basis_fin

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
variable {V : Type*} [AddCommGroup V] [Module E V] [FiniteDimensional E V]
  {n : Type*} [Fintype n]
namespace GlobalTheory.HermDiag
theorem _root_.solution (h2 : (2 : E) ≠ 0) {B : V →ₗ[E] V →ₛₗ[c] E}
    (hB : ∀ x y, c (B x y) = B y x) (hn : finrank E V = Fintype.card n) :
    ∃ v : Basis n E V, ∀ i j, i ≠ j → B (v i) (v j) = 0 := by
  obtain ⟨v, hv⟩ := exists_orthogonal_basis_fin h2 _ B hB hn
  refine ⟨v.reindex (Fintype.equivFin n).symm, fun i j hij => ?_⟩
  simp only [Basis.reindex_apply]
  exact hv _ _ (fun h => hij ((Equiv.injective _) h))
end GlobalTheory.HermDiag
