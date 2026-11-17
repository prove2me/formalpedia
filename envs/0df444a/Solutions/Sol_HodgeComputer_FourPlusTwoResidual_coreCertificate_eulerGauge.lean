-- Prove2me | solution 1 for HodgeComputer.FourPlusTwoResidual.coreCertificate_eulerGauge
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-16T06:54:28.959346+00:00
-- url     : https://prove2.me/submissions/db7e0f0b-a8d3-40a2-8a4c-d8490deaa528

import Definitions.Def_HodgeComputerFourPlusTwoCore
import Mathlib.RingTheory.MvPolynomial.EulerIdentity
import Mathlib.Tactic.Ring

set_option autoImplicit false
open MvPolynomial
open scoped BigOperators
open HodgeComputer.FourPlusTwoResidual

theorem solution
    (D Q : MvPolynomial (Fin 4) ℂ) (k : ℕ)
    (hD : D.IsHomogeneous (k + 1)) (hQ : Q.IsHomogeneous (k + 1))
    (N : Fin 4 → MvPolynomial (Fin 4) ℂ)
    (hN : ∀ i, (N i).IsHomogeneous (k + 2))
    (hcert : CoreCertificate D N) :
    CoreCertificate D (fun i => N i + Q * X i) := by
  rcases hcert with ⟨hD0, _, heq⟩
  refine ⟨hD0, ⟨k, hD, fun i => ?_⟩, ?_⟩
  · exact (hN i).add (hQ.mul (isHomogeneous_X ℂ i))
  · have hcore_hom : core.IsHomogeneous 6 := by
      unfold core
      have hx0 : (X 0 : MvPolynomial (Fin 4) ℂ).IsHomogeneous 1 := isHomogeneous_X ℂ 0
      have hx1 : (X 1 : MvPolynomial (Fin 4) ℂ).IsHomogeneous 1 := isHomogeneous_X ℂ 1
      have hx2 : (X 2 : MvPolynomial (Fin 4) ℂ).IsHomogeneous 1 := isHomogeneous_X ℂ 2
      have hx3 : (X 3 : MvPolynomial (Fin 4) ℂ).IsHomogeneous 1 := isHomogeneous_X ℂ 3
      have t0 := hx0.pow 6
      have t1 := ((hx0.pow 5).C_mul (5 / 7 : ℂ)).mul hx1
      have t2 := ((((hx0.pow 3).C_mul (5 / 7 : ℂ)).mul hx1).mul hx2).mul hx3
      have t3 := (hx0.C_mul (10 / 7 : ℂ)).mul (hx1.pow 5)
      have t4 := (((hx0.C_mul (10 / 7 : ℂ)).mul hx1).mul (hx2.pow 3)).mul hx3
      have t5 := hx1.pow 6
      have t6 := hx2.pow 6
      have t7 := ((hx2.pow 5).C_mul (5 / 7 : ℂ)).mul hx3
      have t8 := (hx2.C_mul (15 / 7 : ℂ)).mul (hx3.pow 5)
      have t9 := hx3.pow 6
      exact (((((((((t0.add t1).add t2).add t3).add t4).add t5).add t6).add t7).add t8).add t9)
    have hE_H : (∑ i : Fin 4, pderiv i core * (Q * X i)) = 6 * Q * core := by
      calc
        (∑ i : Fin 4, pderiv i core * (Q * X i)) =
            ∑ i : Fin 4, Q * (X i * pderiv i core) := by
          apply Finset.sum_congr rfl; intro i _; ring
        _ = Q * ∑ i : Fin 4, X i * pderiv i core := by rw [Finset.mul_sum]
        _ = Q * ((6 : ℕ) • core) := by rw [hcore_hom.sum_X_mul_pderiv]
        _ = 6 * Q * core := by simp [nsmul_eq_mul]; ring
    have hE_div : (∑ i : Fin 4, pderiv i (Q * X i)) = (4 + ((k + 1 : ℕ) : MvPolynomial (Fin 4) ℂ)) * Q := by
      have hsum : (∑ i : Fin 4, pderiv i (Q * X i)) =
          (∑ i : Fin 4, X i * pderiv i Q) + (∑ _i : Fin 4, Q) := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro i _
        simp only [pderiv_mul, pderiv_X_self, mul_one]
        ring
      rw [hsum, hQ.sum_X_mul_pderiv, Finset.sum_const, Finset.card_fin, nsmul_eq_mul, nsmul_eq_mul]
      ring
    have hE_D : (∑ i : Fin 4, pderiv i D * (Q * X i)) = ((k + 1 : ℕ) : MvPolynomial (Fin 4) ℂ) * Q * D := by
      calc
        (∑ i : Fin 4, pderiv i D * (Q * X i)) =
            ∑ i : Fin 4, Q * (X i * pderiv i D) := by
          apply Finset.sum_congr rfl; intro i _; ring
        _ = Q * ∑ i : Fin 4, X i * pderiv i D := by rw [Finset.mul_sum]
        _ = Q * ((k + 1) • D) := by rw [hD.sum_X_mul_pderiv]
        _ = ((k + 1 : ℕ) : MvPolynomial (Fin 4) ℂ) * Q * D := by simp [nsmul_eq_mul]; ring
    have h1 : (∑ i : Fin 4, pderiv i core * (N i + Q * X i)) =
        (∑ i : Fin 4, pderiv i core * N i) + 6 * Q * core := by
      simp only [mul_add, Finset.sum_add_distrib, hE_H]
    have h2 : (∑ i : Fin 4, pderiv i (N i + Q * X i)) =
        (∑ i : Fin 4, pderiv i (N i)) + (4 + ((k + 1 : ℕ) : MvPolynomial (Fin 4) ℂ)) * Q := by
      simp only [map_add, Finset.sum_add_distrib, hE_div]
    have h3 : (∑ i : Fin 4, pderiv i D * (N i + Q * X i)) =
        (∑ i : Fin 4, pderiv i D * N i) + ((k + 1 : ℕ) : MvPolynomial (Fin 4) ℂ) * Q * D := by
      simp only [mul_add, Finset.sum_add_distrib, hE_D]
    rw [h1, h2, h3]
    linear_combination heq
