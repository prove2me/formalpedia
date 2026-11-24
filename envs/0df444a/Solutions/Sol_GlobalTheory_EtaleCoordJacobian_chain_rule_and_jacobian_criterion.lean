-- Prove2me | solution 1 for GlobalTheory.EtaleCoordJacobian.chain_rule_and_jacobian_criterion
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:51:08.411574+00:00
-- url     : https://prove2.me/submissions/8301f1b5-0043-43e1-b2e4-213c4f55e05c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ChainRuleAndJacobianCriterion
import Theorems.Thm_GlobalTheory_EtaleCoordJacobian_exists_basis_of_etale
import Theorems.Thm_GlobalTheory_EtaleCoordJacobian_etale_of_basis
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open KaehlerDifferential TensorProduct
namespace GlobalTheory.EtaleCoordJacobian
section tower
variable (R B : Type) [CommRing R] [CommRing B] (I : Type) [Algebra R B]
  [Algebra (MvPolynomial I R) B] [IsScalarTower R (MvPolynomial I R) B]
end tower
open KaehlerDifferential TensorProduct in
private theorem exists_basis_D_and_smooth_of_etale_eval2Hom (R B I : Type) [CommRing R] [CommRing B]
    [Finite I] [Algebra R B] (t : I → B)
    (h : (MvPolynomial.eval₂Hom (algebraMap R B) t).Etale) :
    (∃ b : Module.Basis I B Ω[B⁄R], ∀ i, b i = D R B (t i)) ∧ Algebra.Smooth R B := by
  letI : Algebra (MvPolynomial I R) B := (MvPolynomial.eval₂Hom (algebraMap R B) t).toAlgebra
  haveI : IsScalarTower R (MvPolynomial I R) B := IsScalarTower.of_algebraMap_eq fun r => by
    simp [RingHom.algebraMap_toAlgebra, MvPolynomial.algebraMap_eq]
  haveI : Algebra.Etale (MvPolynomial I R) B := h
  obtain ⟨⟨b, hb⟩, hs⟩ := _root_.GlobalTheory.EtaleCoordJacobian.exists_basis_of_etale R B I
  exact ⟨⟨b, fun i => by rw [hb]; simp [RingHom.algebraMap_toAlgebra]⟩, hs⟩
open KaehlerDifferential TensorProduct in
private theorem det_derivation_eq_mul_det_repr {R B I : Type} [CommRing R] [CommRing B] [Fintype I]
    [DecidableEq I] [Algebra R B] (t t' : I → B) (b : Module.Basis I B Ω[B⁄R])
    (hb : ∀ i, b i = D R B (t i)) (C : Type) [CommRing C] (φ : B →+* C) (d : I → B →+ C)
    (hd : ∀ i x y, d i (x * y) = φ x * d i y + φ y * d i x)
    (hc : ∀ i r, d i (algebraMap R B r) = 0) :
    (Matrix.of fun i j => d i (t' j)).det =
      φ (Matrix.of fun k j => b.repr (D R B (t' j)) k).det *
        (Matrix.of fun i j => d i (t j)).det := by
  letI : Algebra B C := φ.toAlgebra
  letI : Algebra R C := (φ.comp (algebraMap R B)).toAlgebra
  haveI : IsScalarTower R B C := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have key : ∀ i j, d i (t' j) = ∑ k, d i (t k) * φ (b.repr (D R B (t' j)) k) := by
    intro i j
    let δ : Derivation R B C := Derivation.mk'
      { toFun := d i
        map_add' := map_add (d i)
        map_smul' := fun r x => by
          rw [RingHom.id_apply, Algebra.smul_def r (d i x), Algebra.smul_def, hd, hc, mul_zero,
            add_zero]
          rfl }
      (fun x y => by
        simp only [LinearMap.coe_mk, AddHom.coe_mk, Algebra.smul_def]
        exact hd i x y)
    have h1 : ∀ x, d i x = δ.liftKaehlerDifferential (D R B x) := fun x => by
      rw [Derivation.liftKaehlerDifferential_comp_D]; rfl
    rw [h1]
    conv_lhs => rw [← b.sum_repr (D R B (t' j))]
    rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul, hb, ← h1, Algebra.smul_def, mul_comm]
    rfl
  have hmat : (Matrix.of fun i j => d i (t' j)) = (Matrix.of fun i j => d i (t j)) *
      (Matrix.of fun k j => b.repr (D R B (t' j)) k).map φ := by
    ext i j
    simp only [Matrix.mul_apply, Matrix.of_apply, Matrix.map_apply, key]
  rw [hmat, Matrix.det_mul, mul_comm]
  congr 1
  exact (RingHom.map_det φ _).symm
open KaehlerDifferential TensorProduct in
private theorem exists_basis_D_of_isUnit_det_repr {R B I : Type} [CommRing R] [CommRing B]
    [Fintype I] [DecidableEq I] [Algebra R B] (t' : I → B) (b : Module.Basis I B Ω[B⁄R])
    (ha : IsUnit (Matrix.of fun k j => b.repr (D R B (t' j)) k).det) :
    ∃ b' : Module.Basis I B Ω[B⁄R], ∀ j, b' j = D R B (t' j) := by
  refine ⟨b.map (Matrix.toLinearEquiv b _ ha), fun j => ?_⟩
  rw [Module.Basis.map_apply, Matrix.toLinearEquiv_apply, Matrix.toLin_self]
  conv_rhs => rw [← b.sum_repr (D R B (t' j))]
  simp only [Matrix.of_apply]
open KaehlerDifferential TensorProduct in
private theorem etale_eval2Hom_of_basis_D (R B I : Type) [CommRing R] [CommRing B]
    [Finite I] [Algebra R B] [Algebra.Smooth R B] (t : I → B) (b : Module.Basis I B Ω[B⁄R])
    (hb : ∀ i, b i = D R B (t i)) : (MvPolynomial.eval₂Hom (algebraMap R B) t).Etale := by
  letI : Algebra (MvPolynomial I R) B := (MvPolynomial.eval₂Hom (algebraMap R B) t).toAlgebra
  haveI : IsScalarTower R (MvPolynomial I R) B := IsScalarTower.of_algebraMap_eq fun r => by
    simp [RingHom.algebraMap_toAlgebra, MvPolynomial.algebraMap_eq]
  exact _root_.GlobalTheory.EtaleCoordJacobian.etale_of_basis R B I b fun i => by
    rw [hb]; simp [RingHom.algebraMap_toAlgebra]
end GlobalTheory.EtaleCoordJacobian
end

set_option autoImplicit false
open KaehlerDifferential TensorProduct
open GlobalTheory GlobalTheory.EtaleCoordJacobian
open KaehlerDifferential TensorProduct
namespace GlobalTheory.EtaleCoordJacobian
namespace _root_.GlobalTheory.EtaleCoordJacobian
theorem _root_.solution : ∀ (R B : Type) [CommRing R] [CommRing B] (c : R →+* B) (I : Type) [Fintype I] [DecidableEq I] (t t' : I → B), (MvPolynomial.eval₂Hom c t).Etale → ∃ a : B, (∀ (C : Type) [CommRing C] (φ : B →+* C) (d : I → B →+ C), (∀ i x y, d i (x * y) = φ x * d i y + φ y * d i x) → (∀ i r, d i (c r) = 0) → (Matrix.of fun i j => d i (t' j)).det = φ a * (Matrix.of fun i j => d i (t j)).det) ∧ (IsUnit a → (MvPolynomial.eval₂Hom c t').Etale) := by
  intro R B _ _ c I _ _ t t' het
  letI : Algebra R B := c.toAlgebra
  obtain ⟨⟨b, hb⟩, hs⟩ := exists_basis_D_and_smooth_of_etale_eval2Hom R B I t het
  refine ⟨(Matrix.of fun k j => b.repr (D R B (t' j)) k).det,
    fun C _ φ d hd hc => det_derivation_eq_mul_det_repr t t' b hb C φ d hd hc, fun ha => ?_⟩
  obtain ⟨b', hb'⟩ := exists_basis_D_of_isUnit_det_repr t' b ha
  exact etale_eval2Hom_of_basis_D R B I t' b' hb'
end _root_.GlobalTheory.EtaleCoordJacobian
end GlobalTheory.EtaleCoordJacobian
