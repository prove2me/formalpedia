-- Prove2me | solution 1 for HopfAlgebra.exists_finiteFlat_hopfOrder_ratLocalizedAt_of_algEquiv_baseChange_padic
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/5b8b8719-5c1b-5e05-86b5-ef573cd71b5d

import Mathlib
import Definitions.Def_GaloisRep_Flat
import Theorems.Thm_Module_exists_basis_rat_eq_basis_padicInt_of_linearEquiv_baseChange
import Theorems.Thm_HopfAlgebra_exists_finiteFlat_hopfOrder_ratLocalizedAt_of_basis_match
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HopfAlgebra_exists_finiteFlat_hopfOrder_ratLocalizedAt_of_algEquiv_baseChange_padic

open scoped NNReal TensorProduct

open scoped TensorProduct in
theorem solution
    (p : ℕ) [Fact p.Prime]
    (A : Type) [CommRing A] [HopfAlgebra ℚ A]
    (hAfin : Module.Finite ℚ A) (hAcocomm : Coalgebra.IsCocomm ℚ A)
    (Hp : Type) [CommRing Hp] [HopfAlgebra ℤ_[p] Hp]
    (hfin : Module.Finite ℤ_[p] Hp) (hflat : Module.Flat ℤ_[p] Hp)
    (hcocomm : Coalgebra.IsCocomm ℤ_[p] Hp)
    (φ : (ℚ_[p] ⊗[ℚ] A) ≃ₐ[ℚ_[p]] (ℚ_[p] ⊗[ℤ_[p]] Hp))
    (hφcomul : ∀ x, Coalgebra.comul (R := ℚ_[p]) (φ x) =
        (TensorProduct.map φ.toLinearMap φ.toLinearMap) (Coalgebra.comul (R := ℚ_[p]) x)) :
    ∃ (H : Type) (_ : CommRing H) (_ : HopfAlgebra (GaloisRep.ratLocalizedAt p) H),
      Module.Finite (GaloisRep.ratLocalizedAt p) H ∧
      Module.Flat (GaloisRep.ratLocalizedAt p) H ∧
      Coalgebra.IsCocomm (GaloisRep.ratLocalizedAt p) H ∧
      ∃ ψ : (ℚ ⊗[(GaloisRep.ratLocalizedAt p)] H) ≃ₐ[ℚ] A,
        ∀ x, Coalgebra.comul (R := ℚ) (ψ x) =
          (TensorProduct.map ψ.toLinearMap ψ.toLinearMap) (Coalgebra.comul (R := ℚ) x) := by
  haveI := hAfin; haveI := hfin; haveI := hflat
  obtain ⟨n, b, bHp, hmatch⟩ :=
    Module.exists_basis_rat_eq_basis_padicInt_of_linearEquiv_baseChange p A Hp φ.toLinearEquiv
  exact HopfAlgebra.exists_finiteFlat_hopfOrder_ratLocalizedAt_of_basis_match
    p A hAfin hAcocomm Hp hfin hflat hcocomm φ hφcomul n b bHp hmatch

end S_HopfAlgebra_exists_finiteFlat_hopfOrder_ratLocalizedAt_of_algEquiv_baseChange_padic
end P2MW
export P2MW.S_HopfAlgebra_exists_finiteFlat_hopfOrder_ratLocalizedAt_of_algEquiv_baseChange_padic (solution)
