-- Prove2me | solution 1 for HopfAlgebra.exists_finiteFlat_ratLocalizedAt_of_algEquiv_baseChange_padic
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/e4106ac1-cf52-5bb8-bd84-d0505c1712c1

import Mathlib
import Definitions.Def_GaloisRep_Flat
import Theorems.Thm_HopfAlgebra_exists_finiteFlat_hopfOrder_ratLocalizedAt_of_algEquiv_baseChange_padic
import Theorems.Thm_HopfAlgebra_exists_withConv_equiv_ratLocalizedAt_of_algEquiv_baseChange_rat
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HopfAlgebra_exists_finiteFlat_ratLocalizedAt_of_algEquiv_baseChange_padic

open scoped NNReal TensorProduct

theorem solution
    (p : ℕ) [Fact p.Prime]
    (A : Type) [CommRing A] [HopfAlgebra ℚ A]
    (hAfin : Module.Finite ℚ A) (hAcocomm : Coalgebra.IsCocomm ℚ A)
    (Hp : Type) [CommRing Hp] [HopfAlgebra ℤ_[p] Hp]
    (hfin : Module.Finite ℤ_[p] Hp) (hflat : Module.Flat ℤ_[p] Hp)
    (hcocomm : Coalgebra.IsCocomm ℤ_[p] Hp)
    (φ : (ℚ_[p] ⊗[ℚ] A) ≃ₐ[ℚ_[p]] (ℚ_[p] ⊗[ℤ_[p]] Hp))
    (hφcomul : ∀ x, Coalgebra.comul (R := ℚ_[p]) (φ x) =
        (TensorProduct.map φ.toLinearMap φ.toLinearMap) (Coalgebra.comul (R := ℚ_[p]) x))
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
  obtain ⟨H, hCR, hHopf, hHfin, hHflat, hHcocomm, ψ, hψcomul⟩ :=
    HopfAlgebra.exists_finiteFlat_hopfOrder_ratLocalizedAt_of_algEquiv_baseChange_padic
      p A hAfin hAcocomm Hp hfin hflat hcocomm φ hφcomul
  obtain ⟨e, he_add, he_act⟩ :=
    HopfAlgebra.exists_withConv_equiv_ratLocalizedAt_of_algEquiv_baseChange_rat
      p A eA heA_add heA_act H ψ hψcomul
  exact ⟨H, hCR, hHopf, hHfin, hHflat, hHcocomm, e, he_add, he_act⟩

end S_HopfAlgebra_exists_finiteFlat_ratLocalizedAt_of_algEquiv_baseChange_padic
end P2MW
export P2MW.S_HopfAlgebra_exists_finiteFlat_ratLocalizedAt_of_algEquiv_baseChange_padic (solution)
