-- Prove2me | solution 1 for HopfAlgebra.basis_structureConstants_mem_ratLocalizedAt_range_of_basis_match_padic
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/cb919ed4-9db4-5cf8-8732-285a80f7a2d3

import Mathlib
import Definitions.Def_GaloisRep_Flat
import Theorems.Thm_Bialgebra_counit_comp_algEquiv_of_comul_compat
import Theorems.Thm_HopfAlgebra_antipode_comp_algEquiv_of_comul_compat
import Theorems.Thm_HopfAlgebra_basis_structureConstants_mem_ratLocalizedAt_range_of_bialgHom_basis_match
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HopfAlgebra_basis_structureConstants_mem_ratLocalizedAt_range_of_basis_match_padic

open scoped NNReal TensorProduct

theorem solution
    (p : ℕ) [Fact p.Prime]
    (A : Type) [CommRing A] [HopfAlgebra ℚ A]
    (Hp : Type) [CommRing Hp] [HopfAlgebra ℤ_[p] Hp]
    (φ : (ℚ_[p] ⊗[ℚ] A) ≃ₐ[ℚ_[p]] (ℚ_[p] ⊗[ℤ_[p]] Hp))
    (hφcomul : ∀ x, Coalgebra.comul (R := ℚ_[p]) (φ x) =
        (TensorProduct.map φ.toLinearMap φ.toLinearMap) (Coalgebra.comul (R := ℚ_[p]) x))
    (n : ℕ) (b : Module.Basis (Fin n) ℚ A) (bHp : Module.Basis (Fin n) ℤ_[p] Hp)
    (hmatch : ∀ i, φ (1 ⊗ₜ[ℚ] (b i)) = 1 ⊗ₜ[ℤ_[p]] (bHp i)) :
    (∀ i j k, b.repr (b i * b j) k ∈ (algebraMap (GaloisRep.ratLocalizedAt p) ℚ).range) ∧
    (∀ k, b.repr 1 k ∈ (algebraMap (GaloisRep.ratLocalizedAt p) ℚ).range) ∧
    (∀ i jk, (b.tensorProduct b).repr (Coalgebra.comul (R := ℚ) (b i)) jk
        ∈ (algebraMap (GaloisRep.ratLocalizedAt p) ℚ).range) ∧
    (∀ i, Coalgebra.counit (R := ℚ) (b i) ∈ (algebraMap (GaloisRep.ratLocalizedAt p) ℚ).range) ∧
    (∀ i k, b.repr (HopfAlgebra.antipode ℚ (b i)) k
        ∈ (algebraMap (GaloisRep.ratLocalizedAt p) ℚ).range) := by
  have hφcounit : ∀ x, Coalgebra.counit (R := ℚ_[p]) (φ x) = Coalgebra.counit (R := ℚ_[p]) x :=
    Bialgebra.counit_comp_algEquiv_of_comul_compat ℚ_[p] (ℚ_[p] ⊗[ℚ] A) (ℚ_[p] ⊗[ℤ_[p]] Hp)
      φ hφcomul
  have hφanti : ∀ x, φ (HopfAlgebra.antipode ℚ_[p] x) = HopfAlgebra.antipode ℚ_[p] (φ x) :=
    HopfAlgebra.antipode_comp_algEquiv_of_comul_compat ℚ_[p] (ℚ_[p] ⊗[ℚ] A) (ℚ_[p] ⊗[ℤ_[p]] Hp)
      φ hφcomul
  exact HopfAlgebra.basis_structureConstants_mem_ratLocalizedAt_range_of_bialgHom_basis_match
    p A Hp φ hφcomul hφcounit hφanti n b bHp hmatch

end S_HopfAlgebra_basis_structureConstants_mem_ratLocalizedAt_range_of_basis_match_padic
end P2MW
export P2MW.S_HopfAlgebra_basis_structureConstants_mem_ratLocalizedAt_range_of_basis_match_padic (solution)
