-- Prove2me | solution 1 for MazurTransfer.Order13InverseParameterPolynomialCombinationIndependence.polynomial_combination_kernel
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-17T05:34:17.798374+00:00
-- url     : https://prove2.me/submissions/94085fc7-4744-407e-ab16-8e08e4af4eca

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: independence of the actual inverse parameter combinations
of 1,p/t²,q/t² inside the ordinary t-localization.
Named downstream consumer: the inverse finite algebra's explicit R[S]-basis
and all evaluated-quotient bases for whole single-section FiniteMapData.
-/
import Definitions.Def_MazurTransfer_Order13ActualSingleSectionFiniteBasis
import Definitions.Def_MazurTransfer_Order13InverseCombinationCoordinates
open MazurTransfer
open MazurTransfer.Order13InverseParameterPolynomialCombinationIndependence


noncomputable section
open scoped MazurTransfer.Order13SingleSectionFiniteAlgebra
universe u

open Polynomial
open MazurTorsion.XOneThirteenAffineCurve
open Order13SingleSectionFiniteMapIdentities (t p q)
open Order13SingleSectionFiniteAlgebra (ordinaryParameterLocalization)
open Order13InverseParameterPolynomialIdentities (s a b)
variable (R : Type u) [CommRing R]













variable [IsDomain R] [IsNoetherianRing R]

theorem solution (h104 : IsUnit (104 : R))
    (F : Fin 3 → Polynomial R)
    (hF : ∑ i, aeval (s R) (F i) * generator R i = 0) : ∀ i, F i = 0 := by
  classical
  let N : ℕ := (F 0).natDegree + (F 1).natDegree + (F 2).natDegree
  have hN (i : Fin 3) : (F i).natDegree ≤ N := by
    fin_cases i <;> dsimp [N] <;> omega
  let G : Fin 3 → Polynomial R :=
    ![(F 0).reflect N * X ^ 2, (F 1).reflect N, (F 2).reflect N]
  have hzero : ∑ i, aeval (t R) (G i) *
      Order13SingleSectionPolynomialCombinationIndependence.generator R i = 0 := by
    apply Order13InverseParameterFiniteAlgebra.ordinaryParameter_algebraMap_injective R h104
    simp only [map_sum, map_mul, map_zero]
    let φ := IsScalarTower.toAlgHom R (CoordinateRing R) (ordinaryParameterLocalization R)
    change ∑ i, φ (aeval (t R) (G i)) *
      φ (Order13SingleSectionPolynomialCombinationIndependence.generator R i) = 0
    simp only [← aeval_algHom_apply]
    have he : ∑ i, aeval (tImage R) (G i) *
        algebraMap (CoordinateRing R) (ordinaryParameterLocalization R)
          (Order13SingleSectionPolynomialCombinationIndependence.generator R i) =
      (∑ i, aeval (s R) (F i) * generator R i) * tImage R ^ (N + 2) := by
      simp [Fin.sum_univ_three, G,
        Order13SingleSectionPolynomialCombinationIndependence.generator, generator]
      rw [reflected_aeval R (F 0) N (hN 0), reflected_aeval R (F 1) N (hN 1),
        reflected_aeval R (F 2) N (hN 2)]
      have ha := clear_a R N
      have hb := clear_b R N
      rw [pow_add] at ha hb ⊢
      linear_combination -(aeval (s R) (F 1)) * ha - (aeval (s R) (F 2)) * hb
    change ∑ i, aeval (tImage R) (G i) *
      algebraMap (CoordinateRing R) (ordinaryParameterLocalization R)
        (Order13SingleSectionPolynomialCombinationIndependence.generator R i) = 0
    rw [he, hF, zero_mul]
  have hk : ∀ i, G i = 0 := by
    apply Fintype.linearIndependent_iff.mp
      (Order13SingleSectionFiniteAlgebra.generator_linearIndependent R
        (Order13InverseParameterFiniteAlgebra.two_isUnit_of_104 R h104)) G
    simpa only [Algebra.smul_def, Order13SingleSectionFiniteAlgebra.parameter_algebraMap] using hzero
  intro i
  fin_cases i
  · have h := hk 0
    change (F 0).reflect N * X ^ 2 = 0 at h
    exact reflect_eq_zero_iff.mp ((mul_eq_zero.mp h).resolve_right (pow_ne_zero 2 X_ne_zero))
  · have h := hk 1
    change (F 1).reflect N = 0 at h
    exact reflect_eq_zero_iff.mp h
  · have h := hk 2
    change (F 2).reflect N = 0 at h
    exact reflect_eq_zero_iff.mp h





#print axioms solution
