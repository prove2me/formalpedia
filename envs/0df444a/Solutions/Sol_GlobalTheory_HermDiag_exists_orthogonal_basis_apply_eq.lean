-- Prove2me | solution 1 for GlobalTheory.HermDiag.exists_orthogonal_basis_apply_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T18:23:31.035397+00:00
-- url     : https://prove2.me/submissions/9af33c17-5adc-44af-8c33-af740df2e66e

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_ExistsOrthogonalBasisDotProductApplyEq
import Theorems.Thm_GlobalTheory_HermDiag_finrank_ker_flip_add_one
import Theorems.Thm_GlobalTheory_HermDiag_exists_orthogonal_basis_cons_of_ker
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
    (hB : ∀ x y, c (B x y) = B y x) (hn : finrank E V = Fintype.card n) {x : V}
    (hx : B x x ≠ 0) (i₀ : n) :
    ∃ v : Basis n E V, v i₀ = x ∧ ∀ i j, i ≠ j → B (v i) (v j) = 0 := by
  classical
  have hk := finrank_ker_flip_add_one hx
  obtain ⟨v', hv'⟩ := exists_orthogonal_basis_fin h2 _
    (B.domRestrict₁₂ (LinearMap.ker (B.flip x)) (LinearMap.ker (B.flip x)))
    (fun y z => hB y z) rfl
  obtain ⟨v, hv0, hv⟩ := exists_orthogonal_basis_cons_of_ker hB hx v' hv'
  let e₀ : n ≃ Fin (finrank E (LinearMap.ker (B.flip x)) + 1) :=
    Fintype.equivFinOfCardEq (by omega)
  let e := e₀.trans (Equiv.swap (e₀ i₀) 0)
  have he : e i₀ = 0 := by simp [e]
  refine ⟨v.reindex e.symm, ?_, fun i j hij => ?_⟩
  · rw [Basis.reindex_apply, Equiv.symm_symm, he, hv0]
  · simp only [Basis.reindex_apply]
    exact hv _ _ (fun h => hij ((Equiv.injective _) h))
end GlobalTheory.HermDiag
