-- Prove2me | solution 1 for HodgeComputer.FourPlusTwoResidual.degreeSix_coreCertificate_iff_strict
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-21T04:57:59.567035+00:00
-- url     : https://prove2.me/submissions/65c9bcdf-1164-493e-919a-3dab73100156

import Definitions.Def_HodgeComputerFourPlusTwoCore
import Mathlib.RingTheory.MvPolynomial.EulerIdentity
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

open MvPolynomial
open scoped BigOperators
open HodgeComputer.FourPlusTwoResidual

namespace FP2StrictDeg6

private lemma core_hom : core.IsHomogeneous 6 := by
  have hX := isHomogeneous_X (σ := Fin 4) ℂ
  have hC := isHomogeneous_C (Fin 4) (R := ℂ)
  have t1 : (X 0 ^ 6 : MvPolynomial (Fin 4) ℂ).IsHomogeneous 6 := (hX 0).pow 6
  have t2 : (C (5 / 7 : ℂ) * X 0 ^ 5 * X 1 : MvPolynomial (Fin 4) ℂ).IsHomogeneous 6 :=
    ((hC _).mul ((hX 0).pow 5)).mul (hX 1)
  have t3 : (C (5 / 7 : ℂ) * X 0 ^ 3 * X 1 * X 2 * X 3 : MvPolynomial (Fin 4) ℂ).IsHomogeneous 6 :=
    ((((hC _).mul ((hX 0).pow 3)).mul (hX 1)).mul (hX 2)).mul (hX 3)
  have t4 : (C (10 / 7 : ℂ) * X 0 * X 1 ^ 5 : MvPolynomial (Fin 4) ℂ).IsHomogeneous 6 :=
    ((hC _).mul (hX 0)).mul ((hX 1).pow 5)
  have t5 : (C (10 / 7 : ℂ) * X 0 * X 1 * X 2 ^ 3 * X 3 : MvPolynomial (Fin 4) ℂ).IsHomogeneous 6 :=
    ((((hC _).mul (hX 0)).mul (hX 1)).mul ((hX 2).pow 3)).mul (hX 3)
  have t6 : (X 1 ^ 6 : MvPolynomial (Fin 4) ℂ).IsHomogeneous 6 := (hX 1).pow 6
  have t7 : (X 2 ^ 6 : MvPolynomial (Fin 4) ℂ).IsHomogeneous 6 := (hX 2).pow 6
  have t8 : (C (5 / 7 : ℂ) * X 2 ^ 5 * X 3 : MvPolynomial (Fin 4) ℂ).IsHomogeneous 6 :=
    ((hC _).mul ((hX 2).pow 5)).mul (hX 3)
  have t9 : (C (15 / 7 : ℂ) * X 2 * X 3 ^ 5 : MvPolynomial (Fin 4) ℂ).IsHomogeneous 6 :=
    ((hC _).mul (hX 2)).mul ((hX 3).pow 5)
  have t10 : (X 3 ^ 6 : MvPolynomial (Fin 4) ℂ).IsHomogeneous 6 := (hX 3).pow 6
  unfold core
  exact ((((((((t1.add t2).add t3).add t4).add t5).add t6).add t7).add t8).add t9).add t10

private lemma coreSource_hom : coreSource.IsHomogeneous 6 := by
  have hX := isHomogeneous_X (σ := Fin 4) ℂ
  unfold coreSource
  exact ((hX 0).pow 3).mul ((hX 2).pow 3)

private lemma core_ne_zero : core ≠ 0 := by
  intro h
  have hev := congrArg (eval ![1, 0, 0, 0]) h
  simp [core] at hev

private lemma isHomogeneous_of_mul_isHomogeneous
    {P R : MvPolynomial (Fin 4) ℂ} {a b : ℕ}
    (hP : P.IsHomogeneous a) (hP0 : P ≠ 0)
    (hPR : (P * R).IsHomogeneous (a + b)) : R.IsHomogeneous b := by
  suffices hcomp : ∀ n : ℕ, n ≠ b → homogeneousComponent n R = 0 by
    rw [← sum_homogeneousComponent R]
    apply IsHomogeneous.sum
    intro i _
    by_cases hib : i = b
    · rw [hib]; exact homogeneousComponent_isHomogeneous b R
    · rw [hcomp i hib]; exact isHomogeneous_zero _ _ _
  intro n hnb
  have hmul_comp : homogeneousComponent (a + n) (P * R) = P * homogeneousComponent n R := by
    conv_lhs => rw [← sum_homogeneousComponent R, Finset.mul_sum, map_sum]
    by_cases hle : n ≤ R.totalDegree
    · have hmem : n ∈ Finset.range (R.totalDegree + 1) := Finset.mem_range.mpr (by omega)
      rw [Finset.sum_eq_single n]
      · exact homogeneousComponent_eq_self (hP.mul (homogeneousComponent_isHomogeneous n R))
      · intro m _ hmn
        have hmem_m : P * homogeneousComponent m R ∈
            homogeneousSubmodule (Fin 4) ℂ (a + m) :=
          hP.mul (homogeneousComponent_isHomogeneous m R)
        rw [homogeneousComponent_of_mem hmem_m, if_neg (by omega)]
      · intro hnot; exact absurd hmem hnot
    · have hzero : homogeneousComponent n R = 0 :=
        homogeneousComponent_eq_zero n R (by omega)
      rw [hzero, mul_zero]
      apply Finset.sum_eq_zero
      intro m hm
      rw [Finset.mem_range] at hm
      have hmem_m : P * homogeneousComponent m R ∈
          homogeneousSubmodule (Fin 4) ℂ (a + m) :=
        hP.mul (homogeneousComponent_isHomogeneous m R)
      rw [homogeneousComponent_of_mem hmem_m, if_neg (by omega)]
  have hlhs_zero : homogeneousComponent (a + n) (P * R) = 0 := by
    rw [homogeneousComponent_of_mem hPR, if_neg (by omega)]
  rw [hlhs_zero] at hmul_comp
  exact (mul_eq_zero.mp hmul_comp.symm).resolve_left hP0

private theorem equivalence_of_abstract
    (H A D : MvPolynomial (Fin 4) ℂ)
    (hH_ne : H ≠ 0) (hH_hom : H.IsHomogeneous 6) (hA_hom : A.IsHomogeneous 6)
    (hD_ne : D ≠ 0) (hD_hom : D.IsHomogeneous 6) (hD_coprime : IsRelPrime H D) :
    (∃ u : Fin 4 → MvPolynomial (Fin 4) ℂ,
      D ≠ 0 ∧ (∃ k : ℕ, D.IsHomogeneous (k + 1) ∧ ∀ i, (u i).IsHomogeneous (k + 2)) ∧
        2 * A * D ^ 2 - 2 * D * (∑ i, pderiv i H * u i) +
          3 * H * (D * (∑ i, pderiv i (u i)) - ∑ i, pderiv i D * u i) = 0) ↔
    (∃ p : Fin 4 → MvPolynomial (Fin 4) ℂ,
      (∀ i, (p i).IsHomogeneous 7) ∧
      (∑ i, pderiv i H * p i = A * D) ∧
      (D * (∑ i, pderiv i (p i)) - ∑ i, pderiv i D * p i = 0)) := by
  constructor
  · rintro ⟨u, -, ⟨k, hDk, hUk⟩, hc⟩
    have hk6 : k + 1 = 6 := hDk.inj_right hD_hom hD_ne
    have hk : k = 5 := by omega
    subst hk
    let M : MvPolynomial (Fin 4) ℂ := D * (∑ i, pderiv i (u i)) - ∑ i, pderiv i D * u i
    have hdiv_H : H ∣ D * (2 * ((∑ i, pderiv i H * u i) - A * D)) := by
      refine ⟨3 * M, ?_⟩
      dsimp [M]
      linear_combination -hc
    have hdiv2 : H ∣ 2 * ((∑ i, pderiv i H * u i) - A * D) :=
      hD_coprime.dvd_of_dvd_mul_left hdiv_H
    obtain ⟨R2, hR2⟩ := hdiv2
    let R : MvPolynomial (Fin 4) ℂ := C (1 / 2 : ℂ) * R2
    have hR : (∑ i, pderiv i H * u i) - A * D = H * R := by
      have hhalf : C (1 / 2 : ℂ) * (2 : MvPolynomial (Fin 4) ℂ) = 1 := by
        rw [← map_ofNat C 2, ← map_mul]; norm_num
      calc
        (∑ i, pderiv i H * u i) - A * D
            = C (1 / 2 : ℂ) * (2 * ((∑ i, pderiv i H * u i) - A * D)) := by
              linear_combination -(∑ i, pderiv i H * u i - A * D) * hhalf
        _ = C (1 / 2 : ℂ) * (H * R2) := by rw [hR2]
        _ = H * R := by dsimp [R]; ring
    have hLHS_hom : ((∑ i, pderiv i H * u i) - A * D).IsHomogeneous 12 := by
      have h1 : (∑ i, pderiv i H * u i).IsHomogeneous 12 := by
        apply IsHomogeneous.sum
        intro i _
        simpa using (hH_hom.pderiv (i := i)).mul (hUk i)
      have h2 : (A * D).IsHomogeneous 12 := by
        simpa using hA_hom.mul hD_hom
      exact h1.sub h2
    have hR_hom : R.IsHomogeneous 6 :=
      isHomogeneous_of_mul_isHomogeneous hH_hom hH_ne (hR ▸ hLHS_hom)
    have h3M : 3 * M = 2 * D * R := by
      have hc' : H * (3 * M - 2 * D * R) = 0 := by
        dsimp [M]
        linear_combination hc + 2 * D * hR
      exact sub_eq_zero.mp ((mul_eq_zero.mp hc').resolve_left hH_ne)
    let p : Fin 4 → MvPolynomial (Fin 4) ℂ := fun i => u i - C (1 / 6 : ℂ) * R * X i
    refine ⟨p, ?_, ?_, ?_⟩
    · intro i
      have hRX : (C (1 / 6 : ℂ) * R * X i).IsHomogeneous 7 := by
        simpa using (hR_hom.C_mul (1 / 6 : ℂ)).mul (isHomogeneous_X ℂ i)
      exact (hUk i).sub hRX
    · have hE_H : (∑ i : Fin 4, pderiv i H * X i) = 6 * H := by
        calc
          (∑ i : Fin 4, pderiv i H * X i) = ∑ i : Fin 4, X i * pderiv i H :=
            Finset.sum_congr rfl (fun i _ => by ring)
          _ = (6 : ℕ) • H := hH_hom.sum_X_mul_pderiv
          _ = 6 * H := by simp [nsmul_eq_mul]
      have h_pull : (∑ i : Fin 4, pderiv i H * (C (1 / 6 : ℂ) * R * X i)) =
          C (1 / 6 : ℂ) * R * (∑ i : Fin 4, pderiv i H * X i) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun i _ => by ring)
      have hsum_p : (∑ i : Fin 4, pderiv i H * p i) =
          (∑ i : Fin 4, pderiv i H * u i) - C (1 / 6 : ℂ) * R * (∑ i : Fin 4, pderiv i H * X i) := by
        simp only [p, mul_sub, Finset.sum_sub_distrib, h_pull]
      have hsixth : C (1 / 6 : ℂ) * (6 : MvPolynomial (Fin 4) ℂ) = 1 := by
        rw [← map_ofNat C 6, ← map_mul]; norm_num
      rw [hsum_p, hE_H]
      linear_combination hR - H * R * hsixth
    · have hE_R : (∑ i : Fin 4, X i * pderiv i R) = 6 * R := by
        simpa [nsmul_eq_mul] using hR_hom.sum_X_mul_pderiv
      have hE_D : (∑ i : Fin 4, pderiv i D * X i) = 6 * D := by
        calc
          (∑ i : Fin 4, pderiv i D * X i) = ∑ i : Fin 4, X i * pderiv i D :=
            Finset.sum_congr rfl (fun i _ => by ring)
          _ = (6 : ℕ) • D := hD_hom.sum_X_mul_pderiv
          _ = 6 * D := by simp [nsmul_eq_mul]
      have hdiv_RX : (∑ i : Fin 4, pderiv i (C (1 / 6 : ℂ) * R * X i)) =
          C (1 / 6 : ℂ) * ((∑ i : Fin 4, X i * pderiv i R) + 4 * R) := by
        have h1 : ∀ i : Fin 4, pderiv i (C (1 / 6 : ℂ) * R * X i) =
            C (1 / 6 : ℂ) * (X i * pderiv i R + R) := by
          intro i
          simp only [Derivation.leibniz, pderiv_C, pderiv_X_self, smul_eq_mul, mul_one]
          ring
        simp_rw [h1, ← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
        norm_num
      have hdir_D : (∑ i : Fin 4, pderiv i D * (C (1 / 6 : ℂ) * R * X i)) =
          C (1 / 6 : ℂ) * R * (∑ i : Fin 4, pderiv i D * X i) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun i _ => by ring)
      have hexp : D * (∑ i, pderiv i (p i)) - ∑ i, pderiv i D * p i =
          M - D * (∑ i, pderiv i (C (1 / 6 : ℂ) * R * X i)) +
            ∑ i, pderiv i D * (C (1 / 6 : ℂ) * R * X i) := by
        dsimp [M, p]
        simp only [map_sub, mul_sub, Finset.sum_sub_distrib]
        ring
      have htwo_thirds : C (1 / 6 : ℂ) * (4 : MvPolynomial (Fin 4) ℂ) * (3 : MvPolynomial (Fin 4) ℂ) = 2 := by
        rw [← map_ofNat C 4, ← map_ofNat C 3, ← map_mul, ← map_mul]
        norm_num
        exact map_ofNat C 2
      have h3_ne : (3 : MvPolynomial (Fin 4) ℂ) ≠ 0 := by
        rw [← map_ofNat C 3, Ne, C_eq_zero]; norm_num
      apply mul_left_cancel₀ h3_ne
      rw [mul_zero, hexp, hdiv_RX, hdir_D, hE_R, hE_D]
      linear_combination h3M - D * R * htwo_thirds
  · rintro ⟨p, hp_hom, hp_dir, hp_div⟩
    refine ⟨p, hD_ne, ⟨5, hD_hom, hp_hom⟩, ?_⟩
    rw [hp_dir, hp_div]
    ring

end FP2StrictDeg6

theorem solution
    (D : MvPolynomial (Fin 4) ℂ) (hD_ne : D ≠ 0) (hD_hom : D.IsHomogeneous 6)
    (hD_coprime : IsRelPrime HodgeComputer.FourPlusTwoResidual.core D) :
    (∃ u : Fin 4 → MvPolynomial (Fin 4) ℂ,
      HodgeComputer.FourPlusTwoResidual.CoreCertificate D u) ↔
    (∃ p : Fin 4 → MvPolynomial (Fin 4) ℂ,
      (∀ i, (p i).IsHomogeneous 7) ∧
      (∑ i, MvPolynomial.pderiv i HodgeComputer.FourPlusTwoResidual.core * p i =
        HodgeComputer.FourPlusTwoResidual.coreSource * D) ∧
      (D * (∑ i, MvPolynomial.pderiv i (p i)) -
        ∑ i, MvPolynomial.pderiv i D * p i = 0)) :=
  FP2StrictDeg6.equivalence_of_abstract core coreSource D
    FP2StrictDeg6.core_ne_zero FP2StrictDeg6.core_hom FP2StrictDeg6.coreSource_hom
    hD_ne hD_hom hD_coprime
