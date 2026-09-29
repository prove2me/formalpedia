-- Prove2me | solution 1 for HopfAlgebra.exists_algEquiv_comul_of_withConv_equiv_algClosure_padic
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/d0be680a-4c02-538d-bd97-752cc518011c

import Mathlib
import Definitions.Def_GaloisRep_Flat
import Theorems.Thm_HopfAlgebra_algebra_etale_of_module_finite_of_charZero
import Theorems.Thm_HopfAlgebra_exists_algEquiv_comul_of_etale_of_withConv_equiv_algClosure
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HopfAlgebra_exists_algEquiv_comul_of_withConv_equiv_algClosure_padic

set_option maxHeartbeats 3200000
open scoped TensorProduct

theorem solution
    (p : ℕ) [Fact p.Prime]
    {M : Type} [AddCommGroup M]
    [DistribMulAction (AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p]) M]
    (A : Type) [CommRing A] [HopfAlgebra ℚ_[p] A]
    (hAfin : Module.Finite ℚ_[p] A) (hAcocomm : Coalgebra.IsCocomm ℚ_[p] A)
    (eA : WithConv (A →ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p]) ≃ M)
    (heA_add : ∀ f g, eA (f * g) = eA f + eA g)
    (heA_act : ∀ (σ : AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p])
      (f g : WithConv (A →ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p])),
      (∀ a : A, g a = σ (f a)) → eA g = σ • (eA f))
    (B : Type) [CommRing B] [HopfAlgebra ℚ_[p] B]
    (hBfin : Module.Finite ℚ_[p] B) (hBcocomm : Coalgebra.IsCocomm ℚ_[p] B)
    (eB : WithConv (B →ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p]) ≃ M)
    (heB_add : ∀ f g, eB (f * g) = eB f + eB g)
    (heB_act : ∀ (σ : AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p])
      (f g : WithConv (B →ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p])),
      (∀ b : B, g b = σ (f b)) → eB g = σ • (eB f)) :
    ∃ φ : B ≃ₐ[ℚ_[p]] A,
      ∀ x, Coalgebra.comul (R := ℚ_[p]) (φ x) =
        (TensorProduct.map φ.toLinearMap φ.toLinearMap) (Coalgebra.comul (R := ℚ_[p]) x) := by
  haveI := hAfin; haveI := hBfin
  haveI : Algebra.Etale ℚ_[p] A := HopfAlgebra.algebra_etale_of_module_finite_of_charZero ℚ_[p] A
  haveI : Algebra.Etale ℚ_[p] B := HopfAlgebra.algebra_etale_of_module_finite_of_charZero ℚ_[p] B
  exact HopfAlgebra.exists_algEquiv_comul_of_etale_of_withConv_equiv_algClosure
    ℚ_[p] (AlgebraicClosure ℚ_[p]) A eA heA_add heA_act B eB heB_add heB_act

end S_HopfAlgebra_exists_algEquiv_comul_of_withConv_equiv_algClosure_padic
end P2MW
export P2MW.S_HopfAlgebra_exists_algEquiv_comul_of_withConv_equiv_algClosure_padic (solution)
