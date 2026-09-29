-- Prove2me | solution 1 for MvPolynomial.exists_tensor_kaehlerDifferential_linearEquiv_pi_of_isLocalization
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/6efc2532-8d41-5229-83ca-17e29504f0e9

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MvPolynomial_exists_tensor_kaehlerDifferential_linearEquiv_pi_of_isLocalization

set_option autoImplicit false

open MvPolynomial TensorProduct KaehlerDifferential

theorem solution
    (R : Type) [CommRing R] {n : ℕ} (M : Submonoid (MvPolynomial (Fin n) R))
    (P : Type) [CommRing P] [Algebra (MvPolynomial (Fin n) R) P] [IsLocalization M P]
    [Algebra R P] [IsScalarTower R (MvPolynomial (Fin n) R) P]
    (K : Type) [CommRing K] [Algebra P K] [Algebra (MvPolynomial (Fin n) R) K]
    [IsScalarTower (MvPolynomial (Fin n) R) P K] :
    ∃ e : K ⊗[P] Ω[P⁄R] ≃ₗ[K] (Fin n → K),
      ∀ a : MvPolynomial (Fin n) R,
        e ((1 : K) ⊗ₜ[P] KaehlerDifferential.D R P (algebraMap (MvPolynomial (Fin n) R) P a)) =
          fun i => algebraMap (MvPolynomial (Fin n) R) K (MvPolynomial.pderiv i a) := by
  classical
  haveI : Algebra.FormallyEtale (MvPolynomial (Fin n) R) P := Algebra.FormallyEtale.of_isLocalization M
  let P₀ := MvPolynomial (Fin n) R
  let e₁ : K ⊗[P] Ω[P⁄R] ≃ₗ[K] K ⊗[P] (P ⊗[P₀] Ω[P₀⁄R]) :=
    LinearEquiv.baseChange P K _ _ (tensorKaehlerEquivOfFormallyEtale R P₀ P).symm
  let e₂ : K ⊗[P] (P ⊗[P₀] Ω[P₀⁄R]) ≃ₗ[K] K ⊗[P₀] Ω[P₀⁄R] :=
    TensorProduct.AlgebraTensorModule.cancelBaseChange P₀ P K K Ω[P₀⁄R]
  let b := Algebra.TensorProduct.basis K (mvPolynomialBasis R (Fin n))
  let e₃ : K ⊗[P₀] Ω[P₀⁄R] ≃ₗ[K] (Fin n →₀ K) := b.repr
  let e₄ : (Fin n →₀ K) ≃ₗ[K] (Fin n → K) := Finsupp.linearEquivFunOnFinite K K (Fin n)
  refine ⟨e₁ ≪≫ₗ e₂ ≪≫ₗ e₃ ≪≫ₗ e₄, fun a => ?_⟩
  funext i
  simp only [LinearEquiv.trans_apply]
  rw [show e₁ ((1 : K) ⊗ₜ[P] D R P (algebraMap P₀ P a)) = (1 : K) ⊗ₜ[P] ((1 : P) ⊗ₜ[P₀] D R P₀ a) by
    rw [show e₁ = LinearEquiv.baseChange P K _ _ (tensorKaehlerEquivOfFormallyEtale R P₀ P).symm from rfl,
      LinearEquiv.baseChange_tmul, tensorKaehlerEquivOfFormallyEtale_symm_D_algebraMap]]
  rw [show e₂ ((1 : K) ⊗ₜ[P] ((1 : P) ⊗ₜ[P₀] D R P₀ a)) = (1 : K) ⊗ₜ[P₀] D R P₀ a by
    rw [show e₂ = TensorProduct.AlgebraTensorModule.cancelBaseChange P₀ P K K Ω[P₀⁄R] from rfl,
      TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul, one_smul]]
  rw [show e₃ ((1 : K) ⊗ₜ[P₀] D R P₀ a) = Finsupp.mapRange (algebraMap P₀ K) (map_zero _) ((mvPolynomialBasis R (Fin n)).repr (D R P₀ a)) by
    rw [show e₃ = b.repr from rfl, Algebra.TensorProduct.basis_repr_tmul, one_smul]]
  show (Finsupp.mapRange (algebraMap P₀ K) (map_zero _) ((mvPolynomialBasis R (Fin n)).repr (D R P₀ a))) i = _
  rw [Finsupp.mapRange_apply, mvPolynomialBasis_repr_apply]

end S_MvPolynomial_exists_tensor_kaehlerDifferential_linearEquiv_pi_of_isLocalization
end P2MW
export P2MW.S_MvPolynomial_exists_tensor_kaehlerDifferential_linearEquiv_pi_of_isLocalization (solution)
