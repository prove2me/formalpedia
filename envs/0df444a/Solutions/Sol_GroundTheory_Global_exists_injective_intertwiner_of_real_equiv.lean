-- Prove2me | solution 1 for GroundTheory.Global.exists_injective_intertwiner_of_real_equiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:34:19.200244+00:00
-- url     : https://prove2.me/submissions/01559c86-06fe-404b-9792-51353fee6428

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_HerbrandAbstract
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_Cyclic
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_RationalForm
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_Lattice
import Theorems.Thm_GroundTheory_Global_exists_injective_intertwiner_of_basis

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Global
open GroundTheory.GroupCoh
open scoped TensorProduct
variable {G M M' : Type*} [Group G] [AddCommGroup M] [AddCommGroup M']
variable [Module.Finite ℤ M] [Module.Free ℤ M] [Module.Finite ℤ M'] [Module.Free ℤ M']
namespace GroundTheory.Global
theorem _root_.solution (ρ : Representation ℤ G M)
    (ρ' : Representation ℤ G M') (e : ℝ ⊗[ℤ] M ≃ₗ[ℝ] ℝ ⊗[ℤ] M')
    (he : ∀ g x, e ((ρ g).baseChange ℝ x) = (ρ' g).baseChange ℝ (e x)) :
    ∃ φ : M →ₗ[ℤ] M', Function.Injective φ ∧ (∃ n : ℤ, n ≠ 0 ∧ ∀ y, ∃ x, φ x = n • y) ∧
      ∀ g x, φ (ρ g x) = ρ' g (φ x) := by
  let b := Module.Free.chooseBasis ℤ M
  let b₀ := Module.Free.chooseBasis ℤ M'
  have h1 := e.finrank_eq
  rw [Module.finrank_eq_card_basis (Algebra.TensorProduct.basis ℝ b),
    Module.finrank_eq_card_basis (Algebra.TensorProduct.basis ℝ b₀)] at h1
  exact exists_injective_intertwiner_of_basis ρ ρ' e he b
    (b₀.reindex (Fintype.equivOfCardEq h1).symm)
end GroundTheory.Global
