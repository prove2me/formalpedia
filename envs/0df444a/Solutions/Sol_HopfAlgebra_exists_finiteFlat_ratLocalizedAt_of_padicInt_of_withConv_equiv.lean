-- Prove2me | solution 1 for HopfAlgebra.exists_finiteFlat_ratLocalizedAt_of_padicInt_of_withConv_equiv
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/569db371-ad1a-536f-9fa7-765924060e8c

import Mathlib
import Definitions.Def_GaloisRep_Flat
import Theorems.Thm_HopfAlgebra_exists_algEquiv_baseChange_padic_comul_of_withConv_equiv
import Theorems.Thm_HopfAlgebra_exists_finiteFlat_ratLocalizedAt_of_algEquiv_baseChange_padic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HopfAlgebra_exists_finiteFlat_ratLocalizedAt_of_padicInt_of_withConv_equiv

open scoped NNReal TensorProduct

theorem solution
    (p : ℕ) [Fact p.Prime]
    (A : Type) [CommRing A] [HopfAlgebra ℚ A]
    (hAfin : Module.Finite ℚ A) (hAcocomm : Coalgebra.IsCocomm ℚ A)
    (Hp : Type) [CommRing Hp] [HopfAlgebra ℤ_[p] Hp]
    (hfin : Module.Finite ℤ_[p] Hp) (hflat : Module.Flat ℤ_[p] Hp)
    (hcocomm : Coalgebra.IsCocomm ℤ_[p] Hp)
    {M : Type} [AddCommGroup M]
    [DistribMulAction (AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p]) M]
    (eHp : WithConv (Hp →ₐ[ℤ_[p]] AlgebraicClosure ℚ_[p]) ≃ M)
    (heHp_add : ∀ f g, eHp (f * g) = eHp f + eHp g)
    (heHp_act : ∀ (σ : AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p])
      (f g : WithConv (Hp →ₐ[ℤ_[p]] AlgebraicClosure ℚ_[p])),
      (∀ x : Hp, g x = σ (f x)) → eHp g = σ • (eHp f))
    (eAp : WithConv (A →ₐ[ℚ] AlgebraicClosure ℚ_[p]) ≃ M)
    (heAp_add : ∀ f g, eAp (f * g) = eAp f + eAp g)
    (heAp_act : ∀ (σ : AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p])
      (f g : WithConv (A →ₐ[ℚ] AlgebraicClosure ℚ_[p])),
      (∀ a : A, g a = σ (f a)) → eAp g = σ • (eAp f))
    {N : Type} [AddCommGroup N]
    [DistribMulAction (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) N]
    (eA : WithConv (A →ₐ[ℚ] AlgebraicClosure ℚ) ≃ N)
    (heA_add : ∀ f g, eA (f * g) = eA f + eA g)
    (heA_act : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
      (f g : WithConv (A →ₐ[ℚ] AlgebraicClosure ℚ)),
      (∀ a : A, g a = σ (f a)) → eA g = σ • (eA f)) :
    ∃ (H : Type) (_ : CommRing H) (_ : HopfAlgebra (GaloisRep.ratLocalizedAt p) H),
      Module.Finite (GaloisRep.ratLocalizedAt p) H ∧
      Module.Flat (GaloisRep.ratLocalizedAt p) H ∧
      Coalgebra.IsCocomm (GaloisRep.ratLocalizedAt p) H ∧
      ∃ e : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ) ≃ N,
        (∀ f g, e (f * g) = e f + e g) ∧
        ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
          (f g : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ)),
          (∀ h : H, g h = σ (f h)) → e g = σ • (e f) := by
  obtain ⟨φ, hφcomul⟩ :=
    HopfAlgebra.exists_algEquiv_baseChange_padic_comul_of_withConv_equiv
      p A hAfin hAcocomm Hp hfin hflat hcocomm eHp heHp_add heHp_act eAp heAp_add heAp_act
  exact HopfAlgebra.exists_finiteFlat_ratLocalizedAt_of_algEquiv_baseChange_padic
    p A hAfin hAcocomm Hp hfin hflat hcocomm φ hφcomul eA heA_add heA_act

end S_HopfAlgebra_exists_finiteFlat_ratLocalizedAt_of_padicInt_of_withConv_equiv
end P2MW
export P2MW.S_HopfAlgebra_exists_finiteFlat_ratLocalizedAt_of_padicInt_of_withConv_equiv (solution)
