-- Prove2me | solution 1 for HodgeComputer.FourPlusTwoResidual.no_low_degree_or_scalar_core_certificate
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-21T08:25:44.716646+00:00
-- url     : https://prove2.me/submissions/e2ff3943-ceb9-4068-b56f-2ae7f8c8c50e

import Definitions.Def_HodgeComputerFourPlusTwoSymmetry
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Algebra.Polynomial.Degree.SmallDegree
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Eval.Irreducible
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.RingTheory.MvPolynomial.EulerIdentity
import Mathlib.RingTheory.Polynomial.Eisenstein.Basic
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
noncomputable section

namespace FP2CoreIrreducible

open Polynomial HodgeComputer.FourPlusTwoResidual

private def fcPoly : Polynomial ℂ :=
  X ^ 6 + C (5 / 7 : ℂ) * X ^ 5 + C (15 / 7 : ℂ) * X + 1

private def uBezout : Polynomial ℂ :=
  C (737056232864 / 22772448959039 : ℂ) +
    C (-2256323363175 / 45544897918078 : ℂ) * X +
    C (1618134380625 / 22772448959039 : ℂ) * X ^ 2 +
    C (-4215850734375 / 45544897918078 : ℂ) * X ^ 3 +
    C (-34425156724875 / 22772448959039 : ℂ) * X ^ 4

private def vBezout : Polynomial ℂ :=
  C (10283183272215 / 22772448959039 : ℂ) +
    C (-32397043301 / 3503453686006 : ℂ) * X +
    C (57389585225 / 3503453686006 : ℂ) * X ^ 2 +
    C (-97605519375 / 3503453686006 : ℂ) * X ^ 3 +
    C (159132264375 / 3503453686006 : ℂ) * X ^ 4 +
    C (11475052241625 / 45544897918078 : ℂ) * X ^ 5

private lemma bezout_fc_eval (z : ℂ) :
    eval z uBezout * eval z fcPoly + eval z vBezout * eval z (derivative fcPoly) = 1 := by
  have hd : derivative fcPoly =
      6 * X ^ 5 + C (25 / 7 : ℂ) * X ^ 4 + C (15 / 7 : ℂ) := by
    simp only [fcPoly, derivative_add, derivative_mul, derivative_X_pow, derivative_X,
      derivative_C, derivative_one]
    ext n
    simp only [coeff_add, coeff_C_mul, coeff_ofNat_mul, coeff_X_pow, coeff_C, coeff_one]
    split_ifs <;> norm_num
  rw [hd]
  simp only [fcPoly, uBezout, vBezout, eval_add, eval_mul, eval_pow, eval_X, eval_C, eval_one,
    eval_ofNat]
  ring

private lemma exists_simple_root_fc :
    ∃ r : ℂ, eval r fcPoly = 0 ∧ eval r (derivative fcPoly) ≠ 0 := by
  have hdeg : 0 < fcPoly.degree := by
    have hmon : fcPoly.Monic := by
      unfold fcPoly
      have h5 : (C (5 / 7 : ℂ) * X ^ 5 + C (15 / 7 : ℂ) * X + 1 : Polynomial ℂ).degree < 6 := by
        compute_degree!
      convert Polynomial.monic_X_pow_add h5 using 1
      ring
    rw [Polynomial.degree_eq_natDegree hmon.ne_zero]
    have hnd : fcPoly.natDegree = 6 := by
      unfold fcPoly
      compute_degree!
    rw [hnd]
    decide
  obtain ⟨r, hr⟩ := Complex.exists_root hdeg
  refine ⟨r, hr, ?_⟩
  intro hdr
  have hb := bezout_fc_eval r
  rw [hr, hdr] at hb
  norm_num at hb

private def atZero : Ideal (Polynomial ℂ) := Ideal.span {X}

private lemma atZero_isPrime : atZero.IsPrime := by
  have h0 : (X - C (0 : ℂ) : Polynomial ℂ) = X := by simp
  rw [atZero, ← h0]
  exact (Ideal.span_singleton_prime (Polynomial.X_sub_C_ne_zero 0)).mpr
    (Polynomial.prime_X_sub_C 0)

private lemma planeSec_irreducible (r : ℂ)
    (hr : eval r fcPoly = 0) (hdr : eval r (derivative fcPoly) ≠ 0) :
    Irreducible (X ^ 6 + C (fcPoly.comp (X + C r)) : Polynomial (Polynomial ℂ)) := by
  let sec : Polynomial ℂ := fcPoly.comp (X + C r)
  let P : Polynomial (Polynomial ℂ) := X ^ 6 + C sec
  have hmon : P.Monic := Polynomial.monic_X_pow_add_C sec (by decide)
  have hdeg : P.natDegree = 6 := Polynomial.natDegree_X_pow_add_C
  have hX0 : (X : Polynomial ℂ) = X - C 0 := by simp
  have hmem : sec ∈ atZero := by
    rw [atZero, Ideal.mem_span_singleton, hX0, Polynomial.dvd_iff_isRoot]
    simp [sec, Polynomial.IsRoot, eval_comp, hr]
  have hnot_sq : sec ∉ atZero ^ 2 := by
    intro hsq
    rw [atZero, hX0, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hsq
    have hd : (X - C (0 : ℂ) : Polynomial ℂ) ∣ derivative sec := by
      simpa using Polynomial.pow_sub_one_dvd_derivative_of_pow_dvd hsq
    have he := Polynomial.dvd_iff_isRoot.mp hd
    have hcomp_deriv : derivative sec = (derivative fcPoly).comp (X + C r) := by
      simp [sec, derivative_comp]
    rw [Polynomial.IsRoot, hcomp_deriv, eval_comp] at he
    simp only [eval_add, eval_X, eval_C, zero_add] at he
    exact hdr he
  have heis : P.IsEisensteinAt atZero := by
    refine ⟨?_, ?_, ?_⟩
    · rw [hmon.leadingCoeff, atZero, Ideal.mem_span_singleton, hX0, Polynomial.dvd_iff_isRoot]
      simp [Polynomial.IsRoot]
    · intro n hn
      rw [hdeg] at hn
      by_cases hn0 : n = 0
      · subst hn0; simpa [P] using hmem
      · have h6n : 6 ≠ n := by omega
        simp [P, Polynomial.coeff_X_pow, Polynomial.coeff_C, hn0, Ne.symm h6n]
    · simpa [P] using hnot_sq
  exact heis.irreducible atZero_isPrime hmon.isPrimitive (by rw [hdeg]; decide)

private abbrev Coeff3 := MvPolynomial (Fin 3) ℂ
private def univCore : Polynomial Coeff3 := MvPolynomial.finSuccEquiv ℂ 3 core

private def cCore5 : Coeff3 := MvPolynomial.C (5 / 7 : ℂ) * MvPolynomial.X 0
private def cCore3 : Coeff3 :=
  MvPolynomial.C (5 / 7 : ℂ) * MvPolynomial.X 0 * MvPolynomial.X 1 * MvPolynomial.X 2
private def cCore1 : Coeff3 :=
  MvPolynomial.C (10 / 7 : ℂ) * MvPolynomial.X 0 ^ 5 +
    MvPolynomial.C (10 / 7 : ℂ) * MvPolynomial.X 0 * MvPolynomial.X 1 ^ 3 * MvPolynomial.X 2
private def cCore0 : Coeff3 :=
  MvPolynomial.X 0 ^ 6 + MvPolynomial.X 1 ^ 6 +
    MvPolynomial.C (5 / 7 : ℂ) * MvPolynomial.X 1 ^ 5 * MvPolynomial.X 2 +
    MvPolynomial.C (15 / 7 : ℂ) * MvPolynomial.X 1 * MvPolynomial.X 2 ^ 5 +
    MvPolynomial.X 2 ^ 6

private lemma univCore_formula :
    univCore = X ^ 6 + (C cCore5 * X ^ 5 + C cCore3 * X ^ 3 + C cCore1 * X + C cCore0) := by
  have hX0 : MvPolynomial.finSuccEquiv ℂ 3 (MvPolynomial.X 0) = Polynomial.X := by
    simp [MvPolynomial.finSuccEquiv_apply]
  have hX1 : MvPolynomial.finSuccEquiv ℂ 3 (MvPolynomial.X 1) = C (MvPolynomial.X 0) := by
    simp [MvPolynomial.finSuccEquiv_apply]; rfl
  have hX2 : MvPolynomial.finSuccEquiv ℂ 3 (MvPolynomial.X 2) = C (MvPolynomial.X 1) := by
    simp [MvPolynomial.finSuccEquiv_apply]; rfl
  have hX3 : MvPolynomial.finSuccEquiv ℂ 3 (MvPolynomial.X 3) = C (MvPolynomial.X 2) := by
    simp [MvPolynomial.finSuccEquiv_apply]; rfl
  have hC : ∀ c : ℂ, MvPolynomial.finSuccEquiv ℂ 3 (MvPolynomial.C c) = C (MvPolynomial.C c) := by
    intro c; simp [MvPolynomial.finSuccEquiv_apply]
  unfold univCore core
  simp only [map_add, map_mul, map_pow, hX0, hX1, hX2, hX3, hC,
    cCore5, cCore3, cCore1, cCore0]
  ring

theorem core_irreducible_proof : Irreducible core := by
  obtain ⟨r, hr, hdr⟩ := exists_simple_root_fc
  have hmon : univCore.Monic := by
    rw [univCore_formula]
    have hlt : (C cCore5 * X ^ 5 + C cCore3 * X ^ 3 + C cCore1 * X + C cCore0).degree < 6 := by
      compute_degree!
    exact Polynomial.monic_X_pow_add hlt
  let spec3 : Coeff3 →+* Polynomial ℂ :=
    MvPolynomial.eval₂Hom Polynomial.C ![0, X + C r, 1]
  have hspec : univCore.map spec3 = X ^ 6 + C (fcPoly.comp (X + C r)) := by
    rw [univCore_formula]
    simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_X,
      Polynomial.map_C]
    have hs5 : spec3 cCore5 = 0 := by simp [spec3, cCore5]
    have hs3 : spec3 cCore3 = 0 := by simp [spec3, cCore3]
    have hs1 : spec3 cCore1 = 0 := by simp [spec3, cCore1]
    have hs0 : spec3 cCore0 = fcPoly.comp (X + C r) := by
      simp only [spec3, cCore0, fcPoly, map_add, map_mul, map_pow, MvPolynomial.eval₂Hom_C,
        MvPolynomial.eval₂Hom_X', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.cons_val_two, Matrix.tail_cons, add_comp, mul_comp, pow_comp, X_comp, C_comp,
        one_comp]
      ring
    rw [hs5, hs3, hs1, hs0]
    simp
  have hu : Irreducible univCore :=
    Polynomial.Monic.irreducible_of_irreducible_map spec3 univCore hmon
      (hspec ▸ planeSec_irreducible r hr hdr)
  exact (MulEquiv.irreducible_iff (MvPolynomial.finSuccEquiv ℂ 3)).mp hu

end FP2CoreIrreducible

open MvPolynomial
open scoped BigOperators
open HodgeComputer.FourPlusTwoResidual

namespace FP2CoprimeStrict

private lemma core_irred : Irreducible core := FP2CoreIrreducible.core_irreducible_proof

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

private lemma core_ne_zero : core ≠ 0 := core_irred.ne_zero

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

end FP2CoprimeStrict


namespace FP2Obstructions

open MvPolynomial HodgeComputer.FourPlusTwoResidual
open scoped BigOperators

private abbrev R4 := MvPolynomial (Fin 4) ℂ
private abbrev Exps := ℕ × ℕ × ℕ × ℕ

private theorem coprime_strict
    (D : R4) (hndvd : ¬ (core ∣ D))
    (N : Fin 4 → R4) (hcert : CoreCertificate D N) :
    ∃ p : Fin 4 → R4, StrictCoreCertificate D p := by
  rcases hcert with ⟨hD_ne, ⟨k, hDk, hUk⟩, hc⟩
  have hprime : Prime core :=
    UniqueFactorizationMonoid.irreducible_iff_prime.mp FP2CoreIrreducible.core_irreducible_proof
  let M : R4 := D * (∑ i, pderiv i (N i)) - ∑ i, pderiv i D * N i
  have hdiv_H : core ∣ D * (2 * ((∑ i, pderiv i core * N i) - coreSource * D)) := by
    refine ⟨3 * M, ?_⟩
    dsimp [M]; linear_combination -hc
  have hdiv2 : core ∣ 2 * ((∑ i, pderiv i core * N i) - coreSource * D) :=
    (hprime.dvd_or_dvd hdiv_H).resolve_left hndvd
  obtain ⟨R2, hR2⟩ := hdiv2
  let R : R4 := C (1 / 2 : ℂ) * R2
  have hR : (∑ i, pderiv i core * N i) - coreSource * D = core * R := by
    have hhalf : C (1 / 2 : ℂ) * (2 : R4) = 1 := by
      rw [← map_ofNat C 2, ← map_mul]; norm_num
    calc
      (∑ i, pderiv i core * N i) - coreSource * D
          = C (1 / 2 : ℂ) * (2 * ((∑ i, pderiv i core * N i) - coreSource * D)) := by
            linear_combination -(∑ i, pderiv i core * N i - coreSource * D) * hhalf
      _ = C (1 / 2 : ℂ) * (core * R2) := by rw [hR2]
      _ = core * R := by dsimp [R]; ring
  have hLHS_hom : ((∑ i, pderiv i core * N i) - coreSource * D).IsHomogeneous (6 + (k + 1)) := by
    have h1 : (∑ i, pderiv i core * N i).IsHomogeneous (6 + (k + 1)) := by
      apply IsHomogeneous.sum
      intro i _
      exact (show (6 - 1) + (k + 2) = 6 + (k + 1) by omega) ▸
        (FP2CoprimeStrict.core_hom.pderiv (i := i)).mul (hUk i)
    have h2 : (coreSource * D).IsHomogeneous (6 + (k + 1)) :=
      FP2CoprimeStrict.coreSource_hom.mul hDk
    exact h1.sub h2
  have hR_hom : R.IsHomogeneous (k + 1) :=
    FP2CoprimeStrict.isHomogeneous_of_mul_isHomogeneous
      FP2CoprimeStrict.core_hom FP2CoprimeStrict.core_ne_zero (hR ▸ hLHS_hom)
  have h3M : 3 * M = 2 * D * R := by
    have hc' : core * (3 * M - 2 * D * R) = 0 := by
      dsimp [M]; linear_combination hc + 2 * D * hR
    exact sub_eq_zero.mp ((mul_eq_zero.mp hc').resolve_left FP2CoprimeStrict.core_ne_zero)
  let p : Fin 4 → R4 := fun i => N i - C (1 / 6 : ℂ) * R * X i
  refine ⟨p, hD_ne, ⟨k, hDk, ?_⟩, ?_, ?_⟩
  · intro i
    have hRX : (C (1 / 6 : ℂ) * R * X i).IsHomogeneous (k + 2) := by
      simpa using (hR_hom.C_mul (1 / 6 : ℂ)).mul (isHomogeneous_X ℂ i)
    exact (hUk i).sub hRX
  · have hE_H : (∑ i : Fin 4, pderiv i core * X i) = 6 * core := by
      calc
        (∑ i : Fin 4, pderiv i core * X i) = ∑ i : Fin 4, X i * pderiv i core :=
          Finset.sum_congr rfl (fun i _ => by ring)
        _ = (6 : ℕ) • core := FP2CoprimeStrict.core_hom.sum_X_mul_pderiv
        _ = 6 * core := by simp [nsmul_eq_mul]
    have h_pull : (∑ i : Fin 4, pderiv i core * (C (1 / 6 : ℂ) * R * X i)) =
        C (1 / 6 : ℂ) * R * (∑ i : Fin 4, pderiv i core * X i) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun i _ => by ring)
    have hsum_p : (∑ i : Fin 4, pderiv i core * p i) =
        (∑ i : Fin 4, pderiv i core * N i) -
          C (1 / 6 : ℂ) * R * (∑ i : Fin 4, pderiv i core * X i) := by
      simp only [p, mul_sub, Finset.sum_sub_distrib, h_pull]
    have hsixth : C (1 / 6 : ℂ) * (6 : R4) = 1 := by
      rw [← map_ofNat C 6, ← map_mul]; norm_num
    rw [hsum_p, hE_H]
    linear_combination hR - core * R * hsixth
  · have hE_R : (∑ i : Fin 4, X i * pderiv i R) = ((k + 1 : ℕ) : R4) * R := by
      simpa [nsmul_eq_mul] using hR_hom.sum_X_mul_pderiv
    have hE_D : (∑ i : Fin 4, pderiv i D * X i) = ((k + 1 : ℕ) : R4) * D := by
      calc
        (∑ i : Fin 4, pderiv i D * X i) = ∑ i : Fin 4, X i * pderiv i D :=
          Finset.sum_congr rfl (fun i _ => by ring)
        _ = (k + 1) • D := hDk.sum_X_mul_pderiv
        _ = ((k + 1 : ℕ) : R4) * D := by simp [nsmul_eq_mul]
    have hdiv_RX : (∑ i : Fin 4, pderiv i (C (1 / 6 : ℂ) * R * X i)) =
        C (1 / 6 : ℂ) * ((∑ i : Fin 4, X i * pderiv i R) + 4 * R) := by
      have h1 : ∀ i : Fin 4, pderiv i (C (1 / 6 : ℂ) * R * X i) =
          C (1 / 6 : ℂ) * (X i * pderiv i R + R) := by
        intro i
        simp only [Derivation.leibniz, pderiv_C, pderiv_X_self, smul_eq_mul, mul_one]
        ring
      simp_rw [h1, ← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const, Finset.card_fin,
        nsmul_eq_mul]
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
    have htwo_thirds : C (1 / 6 : ℂ) * (4 : R4) * (3 : R4) = 2 := by
      rw [← map_ofNat C 4, ← map_ofNat C 3, ← map_mul, ← map_mul]
      norm_num
      exact map_ofNat C 2
    have h3_ne : (3 : R4) ≠ 0 := by
      rw [← map_ofNat C 3, Ne, C_eq_zero]; norm_num
    apply mul_left_cancel₀ h3_ne
    rw [mul_zero, hexp, hdiv_RX, hdir_D, hE_R, hE_D]
    linear_combination h3M - D * R * htwo_thirds

def toFS (e : Exps) : Fin 4 →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm ![e.1, e.2.1, e.2.2.1, e.2.2.2]

lemma toFS_apply_0 (a b c d : ℕ) : toFS (a, b, c, d) 0 = a := by
  change (Finsupp.equivFunOnFinite (toFS (a, b, c, d))) 0 = a
  unfold toFS; rw [Equiv.apply_symm_apply]; rfl

lemma toFS_apply_1 (a b c d : ℕ) : toFS (a, b, c, d) 1 = b := by
  change (Finsupp.equivFunOnFinite (toFS (a, b, c, d))) 1 = b
  unfold toFS; rw [Equiv.apply_symm_apply]; rfl

lemma toFS_apply_2 (a b c d : ℕ) : toFS (a, b, c, d) 2 = c := by
  change (Finsupp.equivFunOnFinite (toFS (a, b, c, d))) 2 = c
  unfold toFS; rw [Equiv.apply_symm_apply]; rfl

lemma toFS_apply_3 (a b c d : ℕ) : toFS (a, b, c, d) 3 = d := by
  change (Finsupp.equivFunOnFinite (toFS (a, b, c, d))) 3 = d
  unfold toFS; rw [Equiv.apply_symm_apply]; rfl

lemma eq_toFS (s : Fin 4 →₀ ℕ) : s = toFS (s 0, s 1, s 2, s 3) := by
  ext i
  fin_cases i
  · exact (toFS_apply_0 _ _ _ _).symm
  · exact (toFS_apply_1 _ _ _ _).symm
  · exact (toFS_apply_2 _ _ _ _).symm
  · exact (toFS_apply_3 _ _ _ _).symm

def monP (a b c d : ℕ) : R4 := X 0 ^ a * X 1 ^ b * X 2 ^ c * X 3 ^ d

lemma monP_eq_monomial (a b c d : ℕ) : monP a b c d = monomial (toFS (a, b, c, d)) 1 := by
  rw [monomial_eq, map_one, one_mul, Finsupp.prod_fintype _ _ (fun _ => pow_zero _),
    Fin.prod_univ_four, toFS_apply_0, toFS_apply_1, toFS_apply_2, toFS_apply_3]
  rfl

lemma coeff_monP_mul (a b c d m0 m1 m2 m3 : ℕ) (P : R4) :
    coeff (toFS (m0, m1, m2, m3)) (monP a b c d * P) =
      if a ≤ m0 ∧ b ≤ m1 ∧ c ≤ m2 ∧ d ≤ m3 then
        coeff (toFS (m0 - a, m1 - b, m2 - c, m3 - d)) P
      else 0 := by
  rw [monP_eq_monomial]
  split_ifs with h
  · rcases h with ⟨h0, h1, h2, h3⟩
    have hadd : toFS (m0, m1, m2, m3) =
        toFS (a, b, c, d) + toFS (m0 - a, m1 - b, m2 - c, m3 - d) := by
      ext i; simp only [Finsupp.coe_add, Pi.add_apply]
      fin_cases i
      · change toFS (m0, m1, m2, m3) 0 = toFS (a, b, c, d) 0 + toFS (m0 - a, m1 - b, m2 - c, m3 - d) 0
        rw [toFS_apply_0, toFS_apply_0, toFS_apply_0]; omega
      · change toFS (m0, m1, m2, m3) 1 = toFS (a, b, c, d) 1 + toFS (m0 - a, m1 - b, m2 - c, m3 - d) 1
        rw [toFS_apply_1, toFS_apply_1, toFS_apply_1]; omega
      · change toFS (m0, m1, m2, m3) 2 = toFS (a, b, c, d) 2 + toFS (m0 - a, m1 - b, m2 - c, m3 - d) 2
        rw [toFS_apply_2, toFS_apply_2, toFS_apply_2]; omega
      · change toFS (m0, m1, m2, m3) 3 = toFS (a, b, c, d) 3 + toFS (m0 - a, m1 - b, m2 - c, m3 - d) 3
        rw [toFS_apply_3, toFS_apply_3, toFS_apply_3]; omega
    rw [hadd, coeff_monomial_mul, one_mul]
  · rw [coeff_mul]
    apply Finset.sum_eq_zero
    rintro ⟨u, v⟩ huv
    rw [Finset.mem_antidiagonal] at huv
    rw [coeff_monomial]
    split_ifs with hu
    · exfalso
      apply h
      subst hu
      have k0 := congrArg (fun f : Fin 4 →₀ ℕ => f 0) huv
      have k1 := congrArg (fun f : Fin 4 →₀ ℕ => f 1) huv
      have k2 := congrArg (fun f : Fin 4 →₀ ℕ => f 2) huv
      have k3 := congrArg (fun f : Fin 4 →₀ ℕ => f 3) huv
      simp only [Finsupp.coe_add, Pi.add_apply, toFS_apply_0, toFS_apply_1,
        toFS_apply_2, toFS_apply_3] at k0 k1 k2 k3
      exact ⟨by omega, by omega, by omega, by omega⟩
    · simp

lemma coeff_monP_sc (ea eb ec ed m0 m1 m2 m3 : ℕ) (sc : ℂ) :
    coeff (toFS (m0, m1, m2, m3)) (C sc * monP ea eb ec ed) =
      if ea = m0 ∧ eb = m1 ∧ ec = m2 ∧ ed = m3 then sc else 0 := by
  rw [monP_eq_monomial, C_mul_monomial, mul_one, coeff_monomial]
  by_cases h1 : toFS (ea, eb, ec, ed) = toFS (m0, m1, m2, m3)
  · rw [if_pos h1]
    have k0 := congrArg (fun f : Fin 4 →₀ ℕ => f 0) h1
    have k1 := congrArg (fun f : Fin 4 →₀ ℕ => f 1) h1
    have k2 := congrArg (fun f : Fin 4 →₀ ℕ => f 2) h1
    have k3 := congrArg (fun f : Fin 4 →₀ ℕ => f 3) h1
    simp only [toFS_apply_0, toFS_apply_1, toFS_apply_2, toFS_apply_3] at k0 k1 k2 k3
    rw [if_pos ⟨k0, k1, k2, k3⟩]
  · rw [if_neg h1]
    by_cases h2 : ea = m0 ∧ eb = m1 ∧ ec = m2 ∧ ed = m3
    · exfalso; apply h1; rcases h2 with ⟨rfl, rfl, rfl, rfl⟩; rfl
    · rw [if_neg h2]

lemma coeff_pderiv_0 (m0 m1 m2 m3 : ℕ) (P : R4) :
    coeff (toFS (m0, m1, m2, m3)) (pderiv 0 P) =
      ((m0 + 1 : ℕ) : ℂ) * coeff (toFS (m0 + 1, m1, m2, m3)) P := by
  rw [coeff_pderiv]
  have hs : toFS (m0, m1, m2, m3) + Finsupp.single 0 1 = toFS (m0 + 1, m1, m2, m3) := by
    ext i; fin_cases i <;>
      simp [toFS_apply_0, toFS_apply_1, toFS_apply_2, toFS_apply_3]
  rw [hs, toFS_apply_0]; push_cast; ring

lemma coeff_pderiv_1 (m0 m1 m2 m3 : ℕ) (P : R4) :
    coeff (toFS (m0, m1, m2, m3)) (pderiv 1 P) =
      ((m1 + 1 : ℕ) : ℂ) * coeff (toFS (m0, m1 + 1, m2, m3)) P := by
  rw [coeff_pderiv]
  have hs : toFS (m0, m1, m2, m3) + Finsupp.single 1 1 = toFS (m0, m1 + 1, m2, m3) := by
    ext i; fin_cases i <;>
      simp [toFS_apply_0, toFS_apply_1, toFS_apply_2, toFS_apply_3]
  rw [hs, toFS_apply_1]; push_cast; ring

lemma coeff_pderiv_2 (m0 m1 m2 m3 : ℕ) (P : R4) :
    coeff (toFS (m0, m1, m2, m3)) (pderiv 2 P) =
      ((m2 + 1 : ℕ) : ℂ) * coeff (toFS (m0, m1, m2 + 1, m3)) P := by
  rw [coeff_pderiv]
  have hs : toFS (m0, m1, m2, m3) + Finsupp.single 2 1 = toFS (m0, m1, m2 + 1, m3) := by
    ext i; fin_cases i <;>
      simp [toFS_apply_0, toFS_apply_1, toFS_apply_2, toFS_apply_3]
  rw [hs, toFS_apply_2]; push_cast; ring

lemma coeff_pderiv_3 (m0 m1 m2 m3 : ℕ) (P : R4) :
    coeff (toFS (m0, m1, m2, m3)) (pderiv 3 P) =
      ((m3 + 1 : ℕ) : ℂ) * coeff (toFS (m0, m1, m2, m3 + 1)) P := by
  rw [coeff_pderiv]
  have hs : toFS (m0, m1, m2, m3) + Finsupp.single 3 1 = toFS (m0, m1, m2, m3 + 1) := by
    ext i; fin_cases i <;>
      simp [toFS_apply_0, toFS_apply_1, toFS_apply_2, toFS_apply_3]
  rw [hs, toFS_apply_3]; push_cast; ring

def packKey (tag a b c d : ℕ) : ℕ :=
  ((((tag * 32 + a) * 32 + b) * 32 + c) * 32 + d)

def valFn (N : Fin 4 → R4) (D : R4) (sc : ℂ) (k : ℕ) : ℂ :=
  let d := k % 32
  let k1 := k / 32
  let c := k1 % 32
  let k2 := k1 / 32
  let b := k2 % 32
  let k3 := k2 / 32
  let a := k3 % 32
  let tag := k3 / 32
  match tag with
  | 0 => coeff (toFS (a, b, c, d)) (N 0)
  | 1 => coeff (toFS (a, b, c, d)) (N 1)
  | 2 => coeff (toFS (a, b, c, d)) (N 2)
  | 3 => coeff (toFS (a, b, c, d)) (N 3)
  | 4 => coeff (toFS (a, b, c, d)) D
  | _ => sc

lemma valFn_pack (N : Fin 4 → R4) (D : R4) (sc : ℂ) (tag a b c d : ℕ)
    (ha : a < 32) (hb : b < 32) (hc : c < 32) (hd : d < 32) :
    valFn N D sc (packKey tag a b c d) =
      match tag with
      | 0 => coeff (toFS (a, b, c, d)) (N 0)
      | 1 => coeff (toFS (a, b, c, d)) (N 1)
      | 2 => coeff (toFS (a, b, c, d)) (N 2)
      | 3 => coeff (toFS (a, b, c, d)) (N 3)
      | 4 => coeff (toFS (a, b, c, d)) D
      | _ => sc := by
  unfold valFn packKey
  have h1 : ((((tag * 32 + a) * 32 + b) * 32 + c) * 32 + d) % 32 = d := by omega
  have h2 : ((((tag * 32 + a) * 32 + b) * 32 + c) * 32 + d) / 32 =
      ((tag * 32 + a) * 32 + b) * 32 + c := by omega
  have h3 : (((tag * 32 + a) * 32 + b) * 32 + c) % 32 = c := by omega
  have h4 : (((tag * 32 + a) * 32 + b) * 32 + c) / 32 = (tag * 32 + a) * 32 + b := by omega
  have h5 : ((tag * 32 + a) * 32 + b) % 32 = b := by omega
  have h6 : ((tag * 32 + a) * 32 + b) / 32 = tag * 32 + a := by omega
  have h7 : (tag * 32 + a) % 32 = a := by omega
  have h8 : (tag * 32 + a) / 32 = tag := by omega
  dsimp only
  rw [h1, h2, h3, h4, h5, h6, h7, h8]

def evalPairs (val : ℕ → ℂ) : List (ℕ × ℤ) → ℂ
  | [] => 0
  | (k, w) :: xs => (w : ℂ) * val k + evalPairs val xs

lemma evalPairs_append (val : ℕ → ℂ) :
    ∀ (xs ys : List (ℕ × ℤ)), evalPairs val (xs ++ ys) = evalPairs val xs + evalPairs val ys
  | [], ys => by simp [evalPairs]
  | (k, w) :: xs, ys => by simp [evalPairs, evalPairs_append val xs ys, add_assoc]

def mergeTwoAux : ℕ → List (ℕ × ℤ) → List (ℕ × ℤ) → List (ℕ × ℤ)
  | 0, xs, ys => xs ++ ys
  | _ + 1, [], ys => ys
  | _ + 1, xs, [] => xs
  | n + 1, (k1, w1) :: xs, (k2, w2) :: ys =>
      if k1 == k2 then
        let w := w1 + w2
        if w == 0 then mergeTwoAux n xs ys else (k1, w) :: mergeTwoAux n xs ys
      else if Nat.ble k1 k2 then
        (k1, w1) :: mergeTwoAux n xs ((k2, w2) :: ys)
      else
        (k2, w2) :: mergeTwoAux n ((k1, w1) :: xs) ys

def mergeTwo (bound : ℕ) (xs ys : List (ℕ × ℤ)) : List (ℕ × ℤ) :=
  match xs, ys with
  | [], ys => ys
  | xs, [] => xs
  | xs, ys => mergeTwoAux bound xs ys

lemma evalPairs_mergeTwoAux (val : ℕ → ℂ) :
    ∀ (n : ℕ) (xs ys : List (ℕ × ℤ)),
      evalPairs val (mergeTwoAux n xs ys) = evalPairs val xs + evalPairs val ys := by
  intro n
  induction n with
  | zero => intro xs ys; exact evalPairs_append val xs ys
  | succ n ih =>
      intro xs ys
      cases xs with
      | nil => simp [mergeTwoAux, evalPairs]
      | cons x xs' =>
          cases ys with
          | nil => simp [mergeTwoAux, evalPairs]
          | cons y ys' =>
              rcases x with ⟨k1, w1⟩
              rcases y with ⟨k2, w2⟩
              simp only [mergeTwoAux]
              by_cases h12 : (k1 == k2) = true
              · rw [if_pos h12]
                have hk : k1 = k2 := beq_iff_eq.mp h12
                subst hk
                by_cases hw : (w1 + w2 == 0) = true
                · rw [if_pos hw, ih xs' ys']
                  have hw0 : w1 + w2 = 0 := beq_iff_eq.mp hw
                  have hcast : (w1 : ℂ) + (w2 : ℂ) = 0 := by exact_mod_cast hw0
                  simp only [evalPairs]
                  linear_combination -val k1 * hcast
                · rw [if_neg hw, evalPairs, ih xs' ys']
                  simp only [evalPairs, Int.cast_add]
                  ring
              · rw [if_neg h12]
                by_cases hle : Nat.ble k1 k2 = true
                · rw [if_pos hle, evalPairs, ih xs' ((k2, w2) :: ys')]
                  simp only [evalPairs]; ring
                · rw [if_neg hle, evalPairs, ih ((k1, w1) :: xs') ys']
                  simp only [evalPairs]; ring

lemma evalPairs_mergeTwo (val : ℕ → ℂ) (bound : ℕ) (xs ys : List (ℕ × ℤ)) :
    evalPairs val (mergeTwo bound xs ys) = evalPairs val xs + evalPairs val ys := by
  cases xs with
  | nil => simp [mergeTwo, evalPairs]
  | cons x xs' =>
      cases ys with
      | nil => simp [mergeTwo, evalPairs]
      | cons y ys' => exact evalPairs_mergeTwoAux val bound _ _

def mergeStep (bound : ℕ) : List (List (ℕ × ℤ)) → List (List (ℕ × ℤ))
  | [] => []
  | [x] => [x]
  | x :: y :: rest => mergeTwo bound x y :: mergeStep bound rest

def evalListSum (val : ℕ → ℂ) : List (List (ℕ × ℤ)) → ℂ
  | [] => 0
  | x :: rest => evalPairs val x + evalListSum val rest

lemma evalListSum_mergeStep (val : ℕ → ℂ) (bound : ℕ) :
    ∀ L : List (List (ℕ × ℤ)), evalListSum val (mergeStep bound L) = evalListSum val L
  | [] => rfl
  | [x] => rfl
  | x :: y :: rest => by
      simp only [mergeStep, evalListSum, evalPairs_mergeTwo, evalListSum_mergeStep val bound rest]
      ring

def mergeFold : List (List (ℕ × ℤ)) → List (ℕ × ℤ)
  | [] => []
  | x :: rest => mergeTwo 2048 x (mergeFold rest)

lemma evalPairs_mergeFold (val : ℕ → ℂ) :
    ∀ L : List (List (ℕ × ℤ)), evalPairs val (mergeFold L) = evalListSum val L
  | [] => rfl
  | x :: rest => by
      simp only [mergeFold, evalPairs_mergeTwo, evalPairs_mergeFold val rest, evalListSum]

def mergeAllAux : ℕ → ℕ → List (List (ℕ × ℤ)) → List (ℕ × ℤ)
  | 0, _, L => mergeFold L
  | _ + 1, _, [] => []
  | _ + 1, _, [x] => x
  | fuel + 1, bound, L => mergeAllAux fuel (bound * 2) (mergeStep bound L)

lemma evalPairs_mergeAllAux (val : ℕ → ℂ) :
    ∀ (fuel bound : ℕ) (L : List (List (ℕ × ℤ))),
      evalPairs val (mergeAllAux fuel bound L) = evalListSum val L
  | 0, _, L => evalPairs_mergeFold val L
  | _ + 1, _, [] => rfl
  | _ + 1, _, [x] => by simp [mergeAllAux, evalListSum]
  | fuel + 1, bound, x :: y :: rest => by
      simp only [mergeAllAux,
        evalPairs_mergeAllAux val fuel (bound * 2) (mergeStep bound (x :: y :: rest)),
        evalListSum_mergeStep]

-- Explicit 7 * core and 7 * pderiv i core decompositions
lemma core7_eq : C 7 * core =
    C 7 * monP 6 0 0 0 + C 5 * monP 5 1 0 0 + C 5 * monP 3 1 1 1 + C 10 * monP 1 5 0 0 +
      C 10 * monP 1 1 3 1 + C 7 * monP 0 6 0 0 + C 7 * monP 0 0 6 0 + C 5 * monP 0 0 5 1 +
      C 15 * monP 0 0 1 5 + C 7 * monP 0 0 0 6 := by
  apply MvPolynomial.funext
  intro x
  simp only [core, monP, eval_add, eval_mul, eval_pow, eval_C, eval_X]
  ring

lemma pderiv_X_pow_succ (i j : Fin 4) : ∀ n : ℕ,
    pderiv i (X j ^ (n + 1) : R4) = if j = i then ((n + 1 : ℕ) : R4) * X j ^ n else 0
  | 0 => by
      simp only [zero_add, pow_one, pow_zero, Nat.cast_one, one_mul, pderiv_X]
      by_cases hji : j = i
      · subst hji; simp
      · simp [hji]
  | n + 1 => by
      rw [pow_succ _ (n + 1), pderiv_mul, pderiv_X_pow_succ i j n, pderiv_X]
      by_cases hji : j = i
      · subst hji; simp; ring
      · simp [hji]

lemma pd0_core7_eq : C 7 * pderiv 0 core =
    C 42 * monP 5 0 0 0 + C 25 * monP 4 1 0 0 + C 15 * monP 2 1 1 1 +
      C 10 * monP 0 5 0 0 + C 10 * monP 0 1 3 1 := by
  have h := congrArg (pderiv 0) core7_eq
  rw [pderiv_mul, pderiv_C, zero_mul, zero_add] at h
  rw [h]
  unfold monP
  simp only [pow_zero, mul_one, one_mul, pow_one,
    show ∀ j : Fin 4, (X j : R4) ^ 6 = X j ^ (5 + 1) from fun _ => rfl,
    show ∀ j : Fin 4, (X j : R4) ^ 5 = X j ^ (4 + 1) from fun _ => rfl,
    show ∀ j : Fin 4, (X j : R4) ^ 3 = X j ^ (2 + 1) from fun _ => rfl,
    map_add, pderiv_mul, pderiv_C, pderiv_X_pow_succ, pderiv_X]
  simp
  apply MvPolynomial.funext; intro x
  simp only [map_add, map_mul, map_pow, map_ofNat, eval_X]
  ring

lemma pd1_core7_eq : C 7 * pderiv 1 core =
    C 5 * monP 5 0 0 0 + C 5 * monP 3 0 1 1 + C 50 * monP 1 4 0 0 +
      C 10 * monP 1 0 3 1 + C 42 * monP 0 5 0 0 := by
  have h := congrArg (pderiv 1) core7_eq
  rw [pderiv_mul, pderiv_C, zero_mul, zero_add] at h
  rw [h]
  unfold monP
  simp only [pow_zero, mul_one, one_mul, pow_one,
    show ∀ j : Fin 4, (X j : R4) ^ 6 = X j ^ (5 + 1) from fun _ => rfl,
    show ∀ j : Fin 4, (X j : R4) ^ 5 = X j ^ (4 + 1) from fun _ => rfl,
    show ∀ j : Fin 4, (X j : R4) ^ 3 = X j ^ (2 + 1) from fun _ => rfl,
    map_add, pderiv_mul, pderiv_C, pderiv_X_pow_succ, pderiv_X]
  simp
  apply MvPolynomial.funext; intro x
  simp only [map_add, map_mul, map_pow, map_ofNat, eval_X]
  ring

lemma pd2_core7_eq : C 7 * pderiv 2 core =
    C 5 * monP 3 1 0 1 + C 30 * monP 1 1 2 1 + C 42 * monP 0 0 5 0 +
      C 25 * monP 0 0 4 1 + C 15 * monP 0 0 0 5 := by
  have h := congrArg (pderiv 2) core7_eq
  rw [pderiv_mul, pderiv_C, zero_mul, zero_add] at h
  rw [h]
  unfold monP
  simp only [pow_zero, mul_one, one_mul, pow_one,
    show ∀ j : Fin 4, (X j : R4) ^ 6 = X j ^ (5 + 1) from fun _ => rfl,
    show ∀ j : Fin 4, (X j : R4) ^ 5 = X j ^ (4 + 1) from fun _ => rfl,
    show ∀ j : Fin 4, (X j : R4) ^ 3 = X j ^ (2 + 1) from fun _ => rfl,
    map_add, pderiv_mul, pderiv_C, pderiv_X_pow_succ, pderiv_X]
  simp
  apply MvPolynomial.funext; intro x
  simp only [map_add, map_mul, map_pow, map_ofNat, eval_X]
  ring

lemma pd3_core7_eq : C 7 * pderiv 3 core =
    C 5 * monP 3 1 1 0 + C 10 * monP 1 1 3 0 + C 5 * monP 0 0 5 0 +
      C 75 * monP 0 0 1 4 + C 42 * monP 0 0 0 5 := by
  have h := congrArg (pderiv 3) core7_eq
  rw [pderiv_mul, pderiv_C, zero_mul, zero_add] at h
  rw [h]
  unfold monP
  simp only [pow_zero, mul_one, one_mul, pow_one,
    show ∀ j : Fin 4, (X j : R4) ^ 6 = X j ^ (5 + 1) from fun _ => rfl,
    show ∀ j : Fin 4, (X j : R4) ^ 5 = X j ^ (4 + 1) from fun _ => rfl,
    show ∀ j : Fin 4, (X j : R4) ^ 3 = X j ^ (2 + 1) from fun _ => rfl,
    map_add, pderiv_mul, pderiv_C, pderiv_X_pow_succ, pderiv_X]
  simp
  apply MvPolynomial.funext; intro x
  simp only [map_add, map_mul, map_pow, map_ofNat, eval_X]
  ring

lemma source_core7_eq (sc : ℂ) : C 7 * (2 * C sc * coreSource * core) =
    C sc * (C 14 * monP 9 0 3 0 + C 10 * monP 8 1 3 0 + C 10 * monP 6 1 4 1 +
      C 20 * monP 4 5 3 0 + C 20 * monP 4 1 6 1 + C 14 * monP 3 6 3 0 +
      C 14 * monP 3 0 9 0 + C 10 * monP 3 0 8 1 + C 30 * monP 3 0 4 5 +
      C 14 * monP 3 0 3 6) := by
  have h : C 7 * (2 * C sc * coreSource * core) = 2 * C sc * coreSource * (C 7 * core) := by ring
  rw [h, core7_eq]
  apply MvPolynomial.funext; intro x
  simp only [coreSource, monP, eval_add, eval_mul, eval_pow, eval_C, eval_X, eval_ofNat]
  ring

-- Shift builders for strict and scalar-core rows (no variable shadowing!)
def shMon (tag ea eb ec ed : ℕ) (c0 : ℤ) (m : Exps) (w : ℤ) : List (ℕ × ℤ) :=
  let (m0, m1, m2, m3) := m
  if decide (ea ≤ m0 ∧ eb ≤ m1 ∧ ec ≤ m2 ∧ ed ≤ m3) then
    [(packKey tag (m0 - ea) (m1 - eb) (m2 - ec) (m3 - ed), c0 * w)]
  else []

lemma eval_shMon_v0 (ea eb ec ed : ℕ) (c0 : ℤ) (m0 m1 m2 m3 : ℕ) (w : ℤ)
    (N : Fin 4 → R4) (D : R4) (sc : ℂ)
    (hm : m0 < 31 ∧ m1 < 31 ∧ m2 < 31 ∧ m3 < 31) :
    evalPairs (valFn N D sc) (shMon 0 ea eb ec ed c0 (m0, m1, m2, m3) w) =
      (w : ℂ) * ((c0 : ℂ) * coeff (toFS (m0, m1, m2, m3)) (monP ea eb ec ed * N 0)) := by
  unfold shMon; dsimp only
  rw [coeff_monP_mul]
  by_cases h : ea ≤ m0 ∧ eb ≤ m1 ∧ ec ≤ m2 ∧ ed ≤ m3
  · rw [if_pos (decide_eq_true h), if_pos h, evalPairs, evalPairs, add_zero,
      valFn_pack N D sc 0 _ _ _ _ (by omega) (by omega) (by omega) (by omega)]
    push_cast; ring
  · rw [if_neg (by simpa using h), if_neg h, evalPairs]; ring

lemma eval_shMon_v1 (ea eb ec ed : ℕ) (c0 : ℤ) (m0 m1 m2 m3 : ℕ) (w : ℤ)
    (N : Fin 4 → R4) (D : R4) (sc : ℂ)
    (hm : m0 < 31 ∧ m1 < 31 ∧ m2 < 31 ∧ m3 < 31) :
    evalPairs (valFn N D sc) (shMon 1 ea eb ec ed c0 (m0, m1, m2, m3) w) =
      (w : ℂ) * ((c0 : ℂ) * coeff (toFS (m0, m1, m2, m3)) (monP ea eb ec ed * N 1)) := by
  unfold shMon; dsimp only
  rw [coeff_monP_mul]
  by_cases h : ea ≤ m0 ∧ eb ≤ m1 ∧ ec ≤ m2 ∧ ed ≤ m3
  · rw [if_pos (decide_eq_true h), if_pos h, evalPairs, evalPairs, add_zero,
      valFn_pack N D sc 1 _ _ _ _ (by omega) (by omega) (by omega) (by omega)]
    push_cast; ring
  · rw [if_neg (by simpa using h), if_neg h, evalPairs]; ring

lemma eval_shMon_v2 (ea eb ec ed : ℕ) (c0 : ℤ) (m0 m1 m2 m3 : ℕ) (w : ℤ)
    (N : Fin 4 → R4) (D : R4) (sc : ℂ)
    (hm : m0 < 31 ∧ m1 < 31 ∧ m2 < 31 ∧ m3 < 31) :
    evalPairs (valFn N D sc) (shMon 2 ea eb ec ed c0 (m0, m1, m2, m3) w) =
      (w : ℂ) * ((c0 : ℂ) * coeff (toFS (m0, m1, m2, m3)) (monP ea eb ec ed * N 2)) := by
  unfold shMon; dsimp only
  rw [coeff_monP_mul]
  by_cases h : ea ≤ m0 ∧ eb ≤ m1 ∧ ec ≤ m2 ∧ ed ≤ m3
  · rw [if_pos (decide_eq_true h), if_pos h, evalPairs, evalPairs, add_zero,
      valFn_pack N D sc 2 _ _ _ _ (by omega) (by omega) (by omega) (by omega)]
    push_cast; ring
  · rw [if_neg (by simpa using h), if_neg h, evalPairs]; ring

lemma eval_shMon_v3 (ea eb ec ed : ℕ) (c0 : ℤ) (m0 m1 m2 m3 : ℕ) (w : ℤ)
    (N : Fin 4 → R4) (D : R4) (sc : ℂ)
    (hm : m0 < 31 ∧ m1 < 31 ∧ m2 < 31 ∧ m3 < 31) :
    evalPairs (valFn N D sc) (shMon 3 ea eb ec ed c0 (m0, m1, m2, m3) w) =
      (w : ℂ) * ((c0 : ℂ) * coeff (toFS (m0, m1, m2, m3)) (monP ea eb ec ed * N 3)) := by
  unfold shMon; dsimp only
  rw [coeff_monP_mul]
  by_cases h : ea ≤ m0 ∧ eb ≤ m1 ∧ ec ≤ m2 ∧ ed ≤ m3
  · rw [if_pos (decide_eq_true h), if_pos h, evalPairs, evalPairs, add_zero,
      valFn_pack N D sc 3 _ _ _ _ (by omega) (by omega) (by omega) (by omega)]
    push_cast; ring
  · rw [if_neg (by simpa using h), if_neg h, evalPairs]; ring

lemma eval_shMon_d (ea eb ec ed : ℕ) (c0 : ℤ) (m0 m1 m2 m3 : ℕ) (w : ℤ)
    (N : Fin 4 → R4) (D : R4) (sc : ℂ)
    (hm : m0 < 31 ∧ m1 < 31 ∧ m2 < 31 ∧ m3 < 31) :
    evalPairs (valFn N D sc) (shMon 4 ea eb ec ed c0 (m0, m1, m2, m3) w) =
      (w : ℂ) * ((c0 : ℂ) * coeff (toFS (m0, m1, m2, m3)) (monP ea eb ec ed * D)) := by
  unfold shMon; dsimp only
  rw [coeff_monP_mul]
  by_cases h : ea ≤ m0 ∧ eb ≤ m1 ∧ ec ≤ m2 ∧ ed ≤ m3
  · rw [if_pos (decide_eq_true h), if_pos h, evalPairs, evalPairs, add_zero,
      valFn_pack N D sc 4 _ _ _ _ (by omega) (by omega) (by omega) (by omega)]
    push_cast; ring
  · rw [if_neg (by simpa using h), if_neg h, evalPairs]; ring

def shDer0 (ea eb ec ed : ℕ) (c0 : ℤ) (m : Exps) (w : ℤ) : List (ℕ × ℤ) :=
  let (m0, m1, m2, m3) := m
  if decide (ea ≤ m0 ∧ eb ≤ m1 ∧ ec ≤ m2 ∧ ed ≤ m3) then
    [(packKey 0 (m0 - ea + 1) (m1 - eb) (m2 - ec) (m3 - ed), c0 * ((m0 - ea + 1 : ℕ) : ℤ) * w)]
  else []

def shDer1 (ea eb ec ed : ℕ) (c0 : ℤ) (m : Exps) (w : ℤ) : List (ℕ × ℤ) :=
  let (m0, m1, m2, m3) := m
  if decide (ea ≤ m0 ∧ eb ≤ m1 ∧ ec ≤ m2 ∧ ed ≤ m3) then
    [(packKey 1 (m0 - ea) (m1 - eb + 1) (m2 - ec) (m3 - ed), c0 * ((m1 - eb + 1 : ℕ) : ℤ) * w)]
  else []

def shDer2 (ea eb ec ed : ℕ) (c0 : ℤ) (m : Exps) (w : ℤ) : List (ℕ × ℤ) :=
  let (m0, m1, m2, m3) := m
  if decide (ea ≤ m0 ∧ eb ≤ m1 ∧ ec ≤ m2 ∧ ed ≤ m3) then
    [(packKey 2 (m0 - ea) (m1 - eb) (m2 - ec + 1) (m3 - ed), c0 * ((m2 - ec + 1 : ℕ) : ℤ) * w)]
  else []

def shDer3 (ea eb ec ed : ℕ) (c0 : ℤ) (m : Exps) (w : ℤ) : List (ℕ × ℤ) :=
  let (m0, m1, m2, m3) := m
  if decide (ea ≤ m0 ∧ eb ≤ m1 ∧ ec ≤ m2 ∧ ed ≤ m3) then
    [(packKey 3 (m0 - ea) (m1 - eb) (m2 - ec) (m3 - ed + 1), c0 * ((m3 - ed + 1 : ℕ) : ℤ) * w)]
  else []

lemma eval_shDer0 (ea eb ec ed : ℕ) (c0 : ℤ) (m0 m1 m2 m3 : ℕ) (w : ℤ)
    (N : Fin 4 → R4) (D : R4) (sc : ℂ)
    (hm : m0 < 31 ∧ m1 < 31 ∧ m2 < 31 ∧ m3 < 31) :
    evalPairs (valFn N D sc) (shDer0 ea eb ec ed c0 (m0, m1, m2, m3) w) =
      (w : ℂ) * ((c0 : ℂ) * coeff (toFS (m0, m1, m2, m3)) (monP ea eb ec ed * pderiv 0 (N 0))) := by
  unfold shDer0; dsimp only
  rw [coeff_monP_mul]
  by_cases h : ea ≤ m0 ∧ eb ≤ m1 ∧ ec ≤ m2 ∧ ed ≤ m3
  · rw [if_pos (decide_eq_true h), if_pos h, coeff_pderiv_0, evalPairs, evalPairs, add_zero,
      valFn_pack N D sc 0 _ _ _ _ (by omega) (by omega) (by omega) (by omega)]
    push_cast; ring
  · rw [if_neg (by simpa using h), if_neg h, evalPairs]; ring

lemma eval_shDer1 (ea eb ec ed : ℕ) (c0 : ℤ) (m0 m1 m2 m3 : ℕ) (w : ℤ)
    (N : Fin 4 → R4) (D : R4) (sc : ℂ)
    (hm : m0 < 31 ∧ m1 < 31 ∧ m2 < 31 ∧ m3 < 31) :
    evalPairs (valFn N D sc) (shDer1 ea eb ec ed c0 (m0, m1, m2, m3) w) =
      (w : ℂ) * ((c0 : ℂ) * coeff (toFS (m0, m1, m2, m3)) (monP ea eb ec ed * pderiv 1 (N 1))) := by
  unfold shDer1; dsimp only
  rw [coeff_monP_mul]
  by_cases h : ea ≤ m0 ∧ eb ≤ m1 ∧ ec ≤ m2 ∧ ed ≤ m3
  · rw [if_pos (decide_eq_true h), if_pos h, coeff_pderiv_1, evalPairs, evalPairs, add_zero,
      valFn_pack N D sc 1 _ _ _ _ (by omega) (by omega) (by omega) (by omega)]
    push_cast; ring
  · rw [if_neg (by simpa using h), if_neg h, evalPairs]; ring

lemma eval_shDer2 (ea eb ec ed : ℕ) (c0 : ℤ) (m0 m1 m2 m3 : ℕ) (w : ℤ)
    (N : Fin 4 → R4) (D : R4) (sc : ℂ)
    (hm : m0 < 31 ∧ m1 < 31 ∧ m2 < 31 ∧ m3 < 31) :
    evalPairs (valFn N D sc) (shDer2 ea eb ec ed c0 (m0, m1, m2, m3) w) =
      (w : ℂ) * ((c0 : ℂ) * coeff (toFS (m0, m1, m2, m3)) (monP ea eb ec ed * pderiv 2 (N 2))) := by
  unfold shDer2; dsimp only
  rw [coeff_monP_mul]
  by_cases h : ea ≤ m0 ∧ eb ≤ m1 ∧ ec ≤ m2 ∧ ed ≤ m3
  · rw [if_pos (decide_eq_true h), if_pos h, coeff_pderiv_2, evalPairs, evalPairs, add_zero,
      valFn_pack N D sc 2 _ _ _ _ (by omega) (by omega) (by omega) (by omega)]
    push_cast; ring
  · rw [if_neg (by simpa using h), if_neg h, evalPairs]; ring

lemma eval_shDer3 (ea eb ec ed : ℕ) (c0 : ℤ) (m0 m1 m2 m3 : ℕ) (w : ℤ)
    (N : Fin 4 → R4) (D : R4) (sc : ℂ)
    (hm : m0 < 31 ∧ m1 < 31 ∧ m2 < 31 ∧ m3 < 31) :
    evalPairs (valFn N D sc) (shDer3 ea eb ec ed c0 (m0, m1, m2, m3) w) =
      (w : ℂ) * ((c0 : ℂ) * coeff (toFS (m0, m1, m2, m3)) (monP ea eb ec ed * pderiv 3 (N 3))) := by
  unfold shDer3; dsimp only
  rw [coeff_monP_mul]
  by_cases h : ea ≤ m0 ∧ eb ≤ m1 ∧ ec ≤ m2 ∧ ed ≤ m3
  · rw [if_pos (decide_eq_true h), if_pos h, coeff_pderiv_3, evalPairs, evalPairs, add_zero,
      valFn_pack N D sc 3 _ _ _ _ (by omega) (by omega) (by omega) (by omega)]
    push_cast; ring
  · rw [if_neg (by simpa using h), if_neg h, evalPairs]; ring

def shSc (ea eb ec ed : ℕ) (c0 : ℤ) (m : Exps) (w : ℤ) : List (ℕ × ℤ) :=
  let (m0, m1, m2, m3) := m
  if decide (ea = m0 ∧ eb = m1 ∧ ec = m2 ∧ ed = m3) then
    [(packKey 5 0 0 0 0, c0 * w)]
  else []

lemma eval_shSc (ea eb ec ed : ℕ) (c0 : ℤ) (m0 m1 m2 m3 : ℕ) (w : ℤ)
    (N : Fin 4 → R4) (D : R4) (sc : ℂ) :
    evalPairs (valFn N D sc) (shSc ea eb ec ed c0 (m0, m1, m2, m3) w) =
      (w : ℂ) * ((c0 : ℂ) * coeff (toFS (m0, m1, m2, m3)) (C sc * monP ea eb ec ed)) := by
  unfold shSc; dsimp only
  rw [coeff_monP_sc]
  by_cases h : ea = m0 ∧ eb = m1 ∧ ec = m2 ∧ ed = m3
  · rw [if_pos (decide_eq_true h), if_pos h, evalPairs, evalPairs, add_zero,
      valFn_pack N D sc 5 0 0 0 0 (by omega) (by omega) (by omega) (by omega)]
    push_cast; ring
  · rw [if_neg (by simpa using h), if_neg h, evalPairs]; ring

def rowStrict (m : Exps) (w : ℤ) : List (ℕ × ℤ) :=
  mergeAllAux 6 2 [
    shMon 0 5 0 0 0 42 m w, shMon 0 4 1 0 0 25 m w, shMon 0 2 1 1 1 15 m w,
    shMon 0 0 5 0 0 10 m w, shMon 0 0 1 3 1 10 m w,
    shMon 1 5 0 0 0 5 m w, shMon 1 3 0 1 1 5 m w, shMon 1 1 4 0 0 50 m w,
    shMon 1 1 0 3 1 10 m w, shMon 1 0 5 0 0 42 m w,
    shMon 2 3 1 0 1 5 m w, shMon 2 1 1 2 1 30 m w, shMon 2 0 0 5 0 42 m w,
    shMon 2 0 0 4 1 25 m w, shMon 2 0 0 0 5 15 m w,
    shMon 3 3 1 1 0 5 m w, shMon 3 1 1 3 0 10 m w, shMon 3 0 0 5 0 5 m w,
    shMon 3 0 0 1 4 75 m w, shMon 3 0 0 0 5 42 m w,
    shMon 4 3 0 3 0 (-7) m w
  ]

lemma eval_rowStrict (P : Fin 4 → R4) (D : R4) (m : Exps) (w : ℤ)
    (hm : m.1 < 31 ∧ m.2.1 < 31 ∧ m.2.2.1 < 31 ∧ m.2.2.2 < 31) :
    evalPairs (valFn P D 0) (rowStrict m w) =
      (w : ℂ) * coeff (toFS m) (C 7 * ((∑ i, pderiv i core * P i) - coreSource * D)) := by
  rcases m with ⟨m0, m1, m2, m3⟩
  have hm' : m0 < 31 ∧ m1 < 31 ∧ m2 < 31 ∧ m3 < 31 := hm
  rw [rowStrict, evalPairs_mergeAllAux]
  simp only [evalListSum,
    eval_shMon_v0 _ _ _ _ _ m0 m1 m2 m3 w P D 0 hm',
    eval_shMon_v1 _ _ _ _ _ m0 m1 m2 m3 w P D 0 hm',
    eval_shMon_v2 _ _ _ _ _ m0 m1 m2 m3 w P D 0 hm',
    eval_shMon_v3 _ _ _ _ _ m0 m1 m2 m3 w P D 0 hm',
    eval_shMon_d _ _ _ _ _ m0 m1 m2 m3 w P D 0 hm']
  have hrew : C 7 * ((∑ i, pderiv i core * P i) - coreSource * D) =
      (C 7 * pderiv 0 core) * P 0 + (C 7 * pderiv 1 core) * P 1 +
      (C 7 * pderiv 2 core) * P 2 + (C 7 * pderiv 3 core) * P 3 -
      C 7 * (monP 3 0 3 0 * D) := by
    simp only [Fin.sum_univ_four, coreSource, monP]; ring
  rw [hrew, pd0_core7_eq, pd1_core7_eq, pd2_core7_eq, pd3_core7_eq]
  simp only [add_mul, coeff_add, coeff_sub, mul_assoc, coeff_C_mul]
  push_cast
  ring

def rowScalar (m : Exps) (w : ℤ) : List (ℕ × ℤ) :=
  let terms0 : List (List (ℕ × ℤ)) := [
    shSc 9 0 3 0 14 m w, shSc 8 1 3 0 10 m w, shSc 6 1 4 1 10 m w,
    shSc 4 5 3 0 20 m w, shSc 4 1 6 1 20 m w, shSc 3 6 3 0 14 m w,
    shSc 3 0 9 0 14 m w, shSc 3 0 8 1 10 m w, shSc 3 0 4 5 30 m w,
    shSc 3 0 3 6 14 m w,
    shMon 0 5 0 0 0 (-210) m w, shMon 0 4 1 0 0 (-125) m w, shMon 0 2 1 1 1 (-75) m w,
    shMon 0 0 5 0 0 (-50) m w, shMon 0 0 1 3 1 (-50) m w,
    shMon 1 5 0 0 0 (-25) m w, shMon 1 3 0 1 1 (-25) m w, shMon 1 1 4 0 0 (-250) m w,
    shMon 1 1 0 3 1 (-50) m w, shMon 1 0 5 0 0 (-210) m w,
    shMon 2 3 1 0 1 (-25) m w, shMon 2 1 1 2 1 (-150) m w, shMon 2 0 0 5 0 (-210) m w,
    shMon 2 0 0 4 1 (-125) m w, shMon 2 0 0 0 5 (-75) m w,
    shMon 3 3 1 1 0 (-25) m w, shMon 3 1 1 3 0 (-50) m w, shMon 3 0 0 5 0 (-25) m w,
    shMon 3 0 0 1 4 (-375) m w, shMon 3 0 0 0 5 (-210) m w
  ]
  let termsD01 : List (List (ℕ × ℤ)) := [
    shDer0 6 0 0 0 21 m w, shDer0 5 1 0 0 15 m w, shDer0 3 1 1 1 15 m w,
    shDer0 1 5 0 0 30 m w, shDer0 1 1 3 1 30 m w, shDer0 0 6 0 0 21 m w,
    shDer0 0 0 6 0 21 m w, shDer0 0 0 5 1 15 m w, shDer0 0 0 1 5 45 m w,
    shDer0 0 0 0 6 21 m w,
    shDer1 6 0 0 0 21 m w, shDer1 5 1 0 0 15 m w, shDer1 3 1 1 1 15 m w,
    shDer1 1 5 0 0 30 m w, shDer1 1 1 3 1 30 m w, shDer1 0 6 0 0 21 m w,
    shDer1 0 0 6 0 21 m w, shDer1 0 0 5 1 15 m w, shDer1 0 0 1 5 45 m w,
    shDer1 0 0 0 6 21 m w
  ]
  let termsD23 : List (List (ℕ × ℤ)) := [
    shDer2 6 0 0 0 21 m w, shDer2 5 1 0 0 15 m w, shDer2 3 1 1 1 15 m w,
    shDer2 1 5 0 0 30 m w, shDer2 1 1 3 1 30 m w, shDer2 0 6 0 0 21 m w,
    shDer2 0 0 6 0 21 m w, shDer2 0 0 5 1 15 m w, shDer2 0 0 1 5 45 m w,
    shDer2 0 0 0 6 21 m w,
    shDer3 6 0 0 0 21 m w, shDer3 5 1 0 0 15 m w, shDer3 3 1 1 1 15 m w,
    shDer3 1 5 0 0 30 m w, shDer3 1 1 3 1 30 m w, shDer3 0 6 0 0 21 m w,
    shDer3 0 0 6 0 21 m w, shDer3 0 0 5 1 15 m w, shDer3 0 0 1 5 45 m w,
    shDer3 0 0 0 6 21 m w
  ]
  mergeTwo 128 (mergeAllAux 6 2 terms0) (mergeTwo 128 (mergeAllAux 6 2 termsD01) (mergeAllAux 6 2 termsD23))

lemma eval_rowScalar (N : Fin 4 → R4) (sc : ℂ) (m : Exps) (w : ℤ)
    (hm : m.1 < 31 ∧ m.2.1 < 31 ∧ m.2.2.1 < 31 ∧ m.2.2.2 < 31) :
    evalPairs (valFn N 0 sc) (rowScalar m w) =
      (w : ℂ) * coeff (toFS m)
        (C 7 * (2 * C sc * coreSource * core - 5 * (∑ i, pderiv i core * N i) +
          3 * core * (∑ i, pderiv i (N i)))) := by
  rcases m with ⟨m0, m1, m2, m3⟩
  have hm' : m0 < 31 ∧ m1 < 31 ∧ m2 < 31 ∧ m3 < 31 := hm
  rw [rowScalar, evalPairs_mergeTwo, evalPairs_mergeTwo,
    evalPairs_mergeAllAux, evalPairs_mergeAllAux, evalPairs_mergeAllAux]
  simp only [evalListSum, eval_shSc,
    eval_shMon_v0 _ _ _ _ _ m0 m1 m2 m3 w N 0 sc hm',
    eval_shMon_v1 _ _ _ _ _ m0 m1 m2 m3 w N 0 sc hm',
    eval_shMon_v2 _ _ _ _ _ m0 m1 m2 m3 w N 0 sc hm',
    eval_shMon_v3 _ _ _ _ _ m0 m1 m2 m3 w N 0 sc hm',
    eval_shDer0 _ _ _ _ _ m0 m1 m2 m3 w N 0 sc hm',
    eval_shDer1 _ _ _ _ _ m0 m1 m2 m3 w N 0 sc hm',
    eval_shDer2 _ _ _ _ _ m0 m1 m2 m3 w N 0 sc hm',
    eval_shDer3 _ _ _ _ _ m0 m1 m2 m3 w N 0 sc hm']
  have hrew : C 7 * (2 * C sc * coreSource * core - 5 * (∑ i, pderiv i core * N i) +
      3 * core * (∑ i, pderiv i (N i))) =
      C 7 * (2 * C sc * coreSource * core) -
      C 5 * ((C 7 * pderiv 0 core) * N 0 + (C 7 * pderiv 1 core) * N 1 +
             (C 7 * pderiv 2 core) * N 2 + (C 7 * pderiv 3 core) * N 3) +
      C 3 * ((C 7 * core) * pderiv 0 (N 0) + (C 7 * core) * pderiv 1 (N 1) +
             (C 7 * core) * pderiv 2 (N 2) + (C 7 * core) * pderiv 3 (N 3)) := by
    simp only [Fin.sum_univ_four, ← map_ofNat C 5, ← map_ofNat C 3]; ring
  rw [hrew, source_core7_eq sc, pd0_core7_eq, pd1_core7_eq, pd2_core7_eq, pd3_core7_eq, core7_eq]
  simp only [mul_add, add_mul, coeff_add, coeff_sub, mul_assoc, coeff_C_mul]
  push_cast
  ring

def allBound (ws : List (Exps × ℤ)) : Bool :=
  ws.all fun ⟨(a, b, c, d), _⟩ => decide (a < 31 ∧ b < 31 ∧ c < 31 ∧ d < 31)

def compileStrict (ws : List (Exps × ℤ)) : List (ℕ × ℤ) :=
  mergeAllAux 10 32 (ws.map fun x => rowStrict x.1 x.2)

def compileScalar (ws : List (Exps × ℤ)) : List (ℕ × ℤ) :=
  mergeAllAux 10 32 (ws.map fun x => rowScalar x.1 x.2)

lemma eval_compileStrict_zero (P : Fin 4 → R4) (D : R4)
    (h_eq : (∑ i, pderiv i core * P i) - coreSource * D = 0) :
    ∀ (ws : List (Exps × ℤ)), allBound ws = true →
      evalPairs (valFn P D 0) (compileStrict ws) = 0 := by
  intro ws hb
  rw [compileStrict, evalPairs_mergeAllAux]
  induction ws with
  | nil => rfl
  | cons x rest ih =>
      simp only [allBound, List.all_cons, Bool.and_eq_true] at hb
      rcases x with ⟨m, w⟩
      have hm : m.1 < 31 ∧ m.2.1 < 31 ∧ m.2.2.1 < 31 ∧ m.2.2.2 < 31 := of_decide_eq_true hb.1
      simp only [List.map_cons, evalListSum, eval_rowStrict P D m w hm, ih hb.2,
        h_eq, mul_zero, coeff_zero, add_zero]

lemma zero_of_strict_cert (P : Fin 4 → R4) (D : R4)
    (h_eq : (∑ i, pderiv i core * P i) - coreSource * D = 0)
    (a b c d : ℕ) (k : ℤ) (ws : List (Exps × ℤ))
    (hb : allBound ws = true) (hk : k ≠ 0)
    (hc : compileStrict ws = [(packKey 4 a b c d, k)])
    (habcd : a < 32 ∧ b < 32 ∧ c < 32 ∧ d < 32 := by omega) :
    coeff (toFS (a, b, c, d)) D = 0 := by
  have hz := eval_compileStrict_zero P D h_eq ws hb
  rw [hc, evalPairs, evalPairs, add_zero,
    valFn_pack P D 0 4 a b c d habcd.1 habcd.2.1 habcd.2.2.1 habcd.2.2.2] at hz
  have hkC : (k : ℂ) ≠ 0 := Int.cast_ne_zero.mpr hk
  exact (mul_eq_zero.mp hz).resolve_left hkC

lemma eval_compileScalar_zero (N : Fin 4 → R4) (sc : ℂ)
    (h_eq : 2 * C sc * coreSource * core - 5 * (∑ i, pderiv i core * N i) +
      3 * core * (∑ i, pderiv i (N i)) = 0) :
    ∀ (ws : List (Exps × ℤ)), allBound ws = true →
      evalPairs (valFn N 0 sc) (compileScalar ws) = 0 := by
  intro ws hb
  rw [compileScalar, evalPairs_mergeAllAux]
  induction ws with
  | nil => rfl
  | cons x rest ih =>
      simp only [allBound, List.all_cons, Bool.and_eq_true] at hb
      rcases x with ⟨m, w⟩
      have hm : m.1 < 31 ∧ m.2.1 < 31 ∧ m.2.2.1 < 31 ∧ m.2.2.2 < 31 := of_decide_eq_true hb.1
      simp only [List.map_cons, evalListSum, eval_rowScalar N sc m w hm, ih hb.2,
        h_eq, mul_zero, coeff_zero, add_zero]

def wsScalar : List (Exps × ℤ) :=
  [
    ((0, 1, 0, 11), (-35948227746748622928177170103034597595856864338105813472599838105435281694881727971512290196284129760918544353258977566233613437500 : ℤ)), ((0, 1, 1, 10), (-100655037690896144198896076288496873268399220146696277723279546695218788745668838320234412549595563330571924189125137185454117625000 : ℤ)), ((0, 1, 2, 9), (327949367227198724981161472717596900990696003176750988598579337866914720195084417634299120629173813164033099225190864364371752012500 : ℤ)), ((0, 1, 3, 8), (26995023007024226330755613800835995695415138512343171601896867406602662691181872789612771177184535261425259766407796316677101656250 : ℤ)),
    ((0, 1, 4, 7), (-4468965480251034655803837089789618813983620950884949619818908830761100530360902188638223126760264739381138684533999139069020312500 : ℤ)), ((0, 1, 7, 4), (239994439222999727001507932290423844341462094787716432876330774352349110846969158608702305397645166216392808933578834678123366781250 : ℤ)), ((0, 1, 8, 3), (34097655379913240586444285253578391955805331144967288121161979686505514141057568586502670669624000573712898207197630471430675275000 : ℤ)), ((0, 1, 9, 2), (13026547427323789426883830553320481886403476804489282799212901671489746246929290895143648013088656447399991069762726449118195625000 : ℤ)),
    ((0, 1, 10, 1), (-13590269327403422678351899377193695444539912189087500239356711115625681863196551125542034829623621067119417036840400581394539062500 : ℤ)), ((0, 1, 11, 0), (-1617889205643264604565702306808773267207132403462797647542465609003057364666256086374051765431383460371359171052428640642207031250 : ℤ)), ((0, 3, 0, 9), (549397012379428760181950796944936651835731454968586337700868576913323574680485416015455108019342778217497521757649553175913293844150 : ℤ)), ((0, 3, 1, 8), (189420162873867721109619364408453884626968788066385630996512709536958069099566361308391451954550060252504049209118089725382013100450 : ℤ)),
    ((0, 3, 2, 7), (-199454585456055167678681881152410470584002348048065836135087183098354707837933758146975505277386520189010061453072309873159941875000 : ℤ)), ((0, 3, 3, 6), (121743937786781354426696419022969574745388485317994296796994032000638415503489883633089450907814394459553772677083762767076211286250 : ℤ)), ((0, 3, 4, 5), (-65033815090630022027593193011161429214363392691853751728896245992926226078454490453824771622119790287045292209030964584797818833750 : ℤ)), ((0, 3, 5, 4), (6873124025217118255929101405268276567687968459771363036492164212033817610385782761019923192979307709199906536915882869653001205500 : ℤ)),
    ((0, 3, 6, 3), (-39576786597038659890717112050698157821134736846537644212365466943998469905899557392948603688029708389664956673158701156134441607680 : ℤ)), ((0, 3, 7, 2), (88677643423220513740563481404672334690684687614993750930769496729228205069216831898553247441170647540234866556079060126498383218750 : ℤ)), ((0, 3, 8, 1), (-62916509697502232336976428915164805951496534080923912376972158563059642561700158238990746340223406856157150743318768245082521831250 : ℤ)), ((0, 3, 9, 0), (47405319559381545837186344908124474593557159950356614452691047145935065537657207126597259652838955441381228908955200811336856663750 : ℤ)),
    ((0, 5, 0, 7), (-67374474347680730899033506474535261026152259425963106035191041040050865356092657620795396522303311444543593094952198909486065093750 : ℤ)), ((0, 5, 1, 6), (4468965480251034655803837089789618813983620950884949619818908830761100530360902188638223126760264739381138684533999139069020312500 : ℤ)), ((0, 5, 2, 5), (14953308564832254280800141648401046321902149916284480294613766065219294701840484825953915955198509090564819956123385791557195250000 : ℤ)), ((0, 5, 3, 4), (-208754537554908193554684356066694476483009023719885839348947695954542440808983303492530943217141901158388595128676233864593892479100 : ℤ)),
    ((0, 5, 4, 3), (257705115884392331464080061254190143951056625676707219419704414223633664986113151391158710465701270284438496724949493770597263181250 : ℤ)), ((0, 5, 5, 2), (-34097655379913240586444285253578391955805331144967288121161979686505514141057568586502670669624000573712898207197630471430675275000 : ℤ)), ((0, 5, 6, 1), (-13026547427323789426883830553320481886403476804489282799212901671489746246929290895143648013088656447399991069762726449118195625000 : ℤ)), ((0, 5, 7, 0), (61654475428649954295209497532768487193511108348573329757758102039544843404826680923251050399904543143934909752951283482828380937500 : ℤ)),
    ((0, 7, 0, 5), (2180408496360153540400141823380160376943684096476162346899482686726003507435510773403853797459113419890120299772414058546813888812500 : ℤ)), ((0, 7, 1, 4), (-1274449635332563389680411060856959679709374438054821476002561438846042461879315319633207712113439381246094714837310533006567249418750 : ℤ)), ((0, 7, 2, 3), (86826580527576624363335381247051157077027349374453290712169635479114929369022731750165093489931501704674208978877627248141903050000 : ℤ)), ((0, 7, 3, 2), (14421232621663037345813533097749737618120400326292833726176490583374358094610994582565223337542420065399404760194429497431772656250 : ℤ)),
    ((0, 7, 4, 1), (-2918186024617250200222428690584799541792730855112415953245944346059940262869319939216360268059234209928758795276531704650187500000 : ℤ)), ((0, 7, 5, 0), (-804739095678836826884954238997121024958196571285073325462063007851843722715791362295678978825071080750016189225137306612453970156250 : ℤ)), ((0, 9, 0, 3), (2705206626591098866920842522649527227620951945749950640952308946958828539961019048237388894271748492402163796752518753550163531122900 : ℤ)), ((0, 9, 1, 2), (-136018643515893294221946271513416562280337807219668654371010887865010810134218627277283357023469749437450887551252517182043251541000 : ℤ)),
    ((0, 9, 2, 1), (31916147792461728312935715754691213496961489978856524572491132114917542407741527629243498978054263299935431355582282933801329568750 : ℤ)), ((0, 9, 3, 0), (-1064339194477132077198088684718234333856954993530215209493115886569376130761498517028687271332845842848546058558512347147448050605000 : ℤ)), ((0, 11, 0, 1), (-31726711767658682160789772815049422759864880717844234197588279283423587808144188081643491342593324143878690472427744894349899843750 : ℤ)), ((0, 11, 1, 0), (29620522747531989987365538777015239402332284277048987907913383748237252230441614271276924473770857585937365859782577761002321875000 : ℤ)),
    ((1, 0, 0, 11), (2856005979674669021609738221931177763809095460938014302538394223288253074370018771851298394155925903921299776497951758170925000000 : ℤ)), ((1, 0, 1, 10), (7996816743089073260507267021407297738665467290626440047107503825207108608236052561183635503636592530979639374194264922878590000000 : ℤ)), ((1, 0, 2, 9), (-18490547276314234677813485155070016398400253594348109594920076649178936305071678495288190339820219042356027601150189226747398800000 : ℤ)), ((1, 0, 3, 8), (13988456854837073503121242135937015049125534908290971183479462846341862722485024673282119180543490695050803547698654305728380125000 : ℤ)),
    ((1, 0, 4, 7), (-1713603587804801412965842933158706658285457276562808581523036533972951844622011263110779036493555542352779865898771054902555000000 : ℤ)), ((1, 0, 7, 4), (-10929960901155934109935913622408137088458624429418435545430578368700932814140042212942002671476147333070412203093126742445971250000 : ℤ)), ((1, 0, 8, 3), (4187350084307143802646268006545525650756377227671566923135353250193387066361763810495438859906451343073489658888161311111143025000 : ℤ)), ((1, 0, 9, 2), (14394270137560331868913080638533135929597841123127592084793506885372795494824894610130543906545866555763350873549676861181462000000 : ℤ)),
    ((1, 0, 10, 1), (-8568017939024007064829214665793533291427286382814042907615182669864759223110056315553895182467777711763899329493855274512775000000 : ℤ)), ((1, 0, 11, 0), (-1020002135598096079146335079261134915646105521763576536620855079745804669417863847089749426484259251400464205892125627918187500000 : ℤ)), ((1, 2, 0, 9), (630118283909292795375816581375257153658538492943107541153228219859057812177082997900956441260988593381239718548890699253315721148250 : ℤ)), ((1, 2, 1, 8), (-94267896507556433243194174531611349362690167688509926883770304938315396532064112504681020186282339497910279414044180774196346232475 : ℤ)),
    ((1, 2, 2, 7), (12498634154822197051282433407683080519270047718774838945455356303205563490329363155069898808436527136771202133694387059606491875000 : ℤ)), ((1, 2, 4, 5), (-264617764480019153238739123141893559733935074741159601168320059019907803710959323312353238093233238033878791382063421301913904468750 : ℤ)), ((1, 2, 5, 4), (221988055684257686084658873422885133283113782714863432834679878321094812533282273444171586532284904046417825474502838184862862488125 : ℤ)), ((1, 2, 7, 2), (-12256381303392450840934200500456158075529469591472147003632966253451749104051143744708713125848783681700786940161433159530787500000 : ℤ)),
    ((1, 2, 9, 0), (-1823840692979352703331984766187677645885739749397728527943246684974172703574988471010147301667600423982511544695604444862157700421875 : ℤ)), ((1, 4, 0, 7), (50648263954944781667904588117523336412944021965798650975535065621159487344097716779433120542009676850889525039418043030915297725000 : ℤ)), ((1, 4, 1, 6), (-11791953912355167046860349777218415990483331074896899900532782655643944837872299752056893219505949937869536485105504701313367178750 : ℤ)), ((1, 4, 2, 5), (-6973968553214624679986378764313249795379247076355759008188531569314496847090283567629330880128991131537881707922561331955311464900 : ℤ)),
    ((1, 4, 3, 4), (169448642808856962079777887140290170811583038303176129108585770790964546348105121316837474843589631748634067150679070091308574420394 : ℤ)), ((1, 4, 4, 3), (-198406871343184398596017726545748299584252786381561011742306902437601480195676033302576215229647731229545466079302577750129229398500 : ℤ)), ((1, 4, 5, 2), (28647330751628409494997667359490585990415594336609159894143927370310630820357432687228911013059689843414447736645249545911499343750 : ℤ)), ((1, 4, 7, 0), (-46000235317185913422248345582586563466114242038080168041671559641227343827106225257208064267997942798539407031390670826768806923250 : ℤ)),
    ((1, 6, 0, 5), (-1964475893016263428962003138369919821039198145749158709756392095901313637675510648283503929835871746777301969657245190895280093875000 : ℤ)), ((1, 6, 1, 4), (1292125614707779170309939812168106375095294877713048154639874497664864612538155827490427660266472160447272395272370336105353782362500 : ℤ)), ((1, 6, 2, 3), (66855937690643228928135417326008705824192233144446549195935038553346514743786065982161261792529090239455451394738258584697483050000 : ℤ)), ((1, 6, 5, 0), (701598533220094081772143977989257078942570766338985253484425748536183442026968088672679974941382766706179274877587568176885747812500 : ℤ)),
    ((1, 8, 0, 3), (-1449165074049048569733131543584089130313305502440503359277895031455292939580677867556577191569889439093179599785608201727566291253650 : ℤ)), ((1, 8, 1, 2), (-85683414204100640742869384491938931881251178025262318029910969238185802770391196949261175492686083958818280137394136736738822794975 : ℤ)), ((1, 8, 2, 1), (28190751019712709719584868387732254697699201058770485554980516592126334723145407382090977130332151915823218713528059237531751875000 : ℤ)), ((1, 8, 3, 0), (782438943109202442101296063236219732391588120475900514966852361821061793511168969209582694835922815999602838672035613858768294096875 : ℤ)),
    ((1, 10, 0, 1), (-133252189424166465075317045823207575591432499014945783629870772990379068794205589942902663638891961404290499984196528556269579343750 : ℤ)), ((1, 10, 1, 0), (124406195539634357946935262863464005489795593963605749213236211742596459367854779939363082789837601860936936611086826596209751875000 : ℤ)), ((2, 1, 0, 9), (-281079382996569818570096174262428416520014795332104706709730039123328999358457045796867819273993700134074465752863250574495443050000 : ℤ)), ((2, 1, 1, 8), (26919634227104336378851928449132843553824747275746622955529449088965468443273856554121750230079184122078888885696268395205975625000 : ℤ)),
    ((2, 1, 4, 5), (12155641153374313201024160799028235144186087407802955452911123308124406086006626097774089752530371418233647692273928287918466250000 : ℤ)), ((2, 1, 9, 0), (82484707826468553864092519707691595621262735981520054859039765305129898440759248520609894749313234623728323626144513382303878125000 : ℤ)), ((2, 3, 0, 7), (46049393818622834865303252564143344546030550237162951498677559902280127635339018307727522808631199690899828028972765673962933043750 : ℤ)), ((2, 3, 1, 6), (42937438492671391686815201703605997852124321764846138530456392337835011561028790561696940994024037551874994580854699799895961681250 : ℤ)),
    ((2, 3, 2, 5), (-44445789701110779865347563849890321835566252352707051303550185684095140280249495050105107207515624949351647161139375599840266072500 : ℤ)), ((2, 3, 3, 4), (-103576912044774037970069811322021856890521254823725423633770811716975331179144036899744882893797756846151352233330483680206093474900 : ℤ)), ((2, 3, 4, 3), (-60506418680677921961596147468102485103272885025033876457700704670813078971403880424643110487190178006470724543750000678501340907380 : ℤ)), ((2, 3, 5, 2), (74521053770637253962295974239807932459580159212758203420000292660279989298669285183276943381008498625354742973610715848230163312500 : ℤ)),
    ((2, 3, 7, 0), (-53146853810399048696034479664062811339281285560606350160317509296075390755670259904375126631497244088373961321052519663969411906250 : ℤ)), ((2, 5, 0, 5), (1652558795156588002306234816337154838994526082616481248209501611704665588229899760326498391713223245052227546324344239828898855855000 : ℤ)), ((2, 5, 1, 4), (-1091534117909129699268092132635978451602541748837688113720522320119905066151149801985910695321576592370128424525035331115544748304500 : ℤ)), ((2, 5, 2, 3), (-58127454590138964357709796311433270521262814254752934253185237280332248360628837441199847959922532418037482175437891613419536242500 : ℤ)),
    ((2, 5, 3, 2), (1454338391634341515672379665924785639229227444073842365780565047725314488877360638172781127713158182518311234410231691752897137500 : ℤ)), ((2, 5, 5, 0), (-590199569698781429395083862977555299640902172363029017217679147037380567224964200116606568469008301804366980830122942796035305662500 : ℤ)), ((2, 7, 0, 3), (1433963115981329488686852947504561540051821227398413795891200837071852650234683590288493322637261639924105027027819992341261214200000 : ℤ)), ((2, 7, 1, 2), (11536986097330429876650826478199790094496320261034266980941192466699486475688795666052178670033936052319523808155543597945418125000 : ℤ)),
    ((2, 7, 3, 0), (-1785602158905501468612778777084477016349256843186499891173491316088623574418993568857418821317428925567762608008240293907149420475000 : ℤ)), ((2, 9, 0, 1), (188713771155150484865133661008009464936297997792505049311677080090618105301106286473684227590719968468680322053529582063837548550000 : ℤ)), ((2, 9, 1, 0), (-206332174834294247372136930601976485236802642516664001482770091787344320541238800864923922666356008788773192800175264075997169712500 : ℤ)), ((3, 0, 0, 9), (5930341603253103907332260886312044287858534211768141838807630081999039722842891172858797461720065365525070069295490642302843352500 : ℤ)),
    ((3, 0, 1, 8), (31486031261396175866593088938988798391987689703521638573295162832148670105231106873785887006164066235169324508020731919073209287500 : ℤ)), ((3, 0, 2, 7), (83807436265052582185782952084268775183941809314661039361895065445992107612935441662229416003260386652599359632766996354759011162500 : ℤ)), ((3, 0, 3, 6), (-52307794849389390520571654191912232502113648076973834798914660667740132095547597617444843328282681928564522943610021188680374201000 : ℤ)), ((3, 0, 4, 5), (37958370112835913585877960742989574408794609550461831141717164914730083774429740922496432136527125453538484123438247817456954247500 : ℤ)),
    ((3, 0, 5, 4), (-24712247068326057101355545996890952965184363141382569193453418430910421195318735491792684889023312305269956050604489406451583487500 : ℤ)), ((3, 0, 6, 3), (-8427702493627161629137213477938418776903916203709512569949350836846763551414278366657554225568196301103111743768722121319607177500 : ℤ)), ((3, 0, 7, 2), (80634458114399167447998015370825775986593522911454791343801360269768277484556254298945555496852981046633223238907548450229919250000 : ℤ)), ((3, 0, 8, 1), (-29315345955217579247413704080760974098407936943613387181221764207812022754302199838380148511835340410413398495679485557751008767500 : ℤ)),
    ((3, 0, 9, 0), (51833397077069182398958319712251869443890726896859156311377091179923614224571208627920243388521830769326074122186059430135336633500 : ℤ)), ((3, 2, 0, 7), (55197705712567859755856095311953403741868411456093154844161920650877966794473515927308593372034550159034113680280606036406990625000 : ℤ)), ((3, 2, 2, 5), (9510434771811700773284018202879044897412370457608937599340898414328464303755841763412014109122980433079587574632852706175738487500 : ℤ)), ((3, 2, 3, 4), (-66211876515511253813818187158341959701723975768172455246107552572087967411961796407958195138192762430284317407464600263186943936250 : ℤ)),
    ((3, 2, 4, 3), (24227670804393902740966735604219559198442272548171960659976504180068921598946470898709575207071265709870999997126641555685378062500 : ℤ)), ((3, 2, 7, 0), (49382686819352766245916250325806399916755209383173360389074220272111801810105818976134074135954738179502314558578798193107106156250 : ℤ)), ((3, 4, 0, 5), (-1338912392177672215677772604997376833831680854050435149915527490740536680493882669564032835487681621185318028890351884717104128700500 : ℤ)), ((3, 4, 1, 4), (884838641331775102855857769559935539816759833524472079043358595523759423065786388476089119972782991577495391031133852722579761819030 : ℤ)),
    ((3, 4, 2, 3), (51230252004746406050656714763214791118062790954897057602239061977296760048000497395347807653278216538219060846772288393856736078900 : ℤ)), ((3, 4, 3, 2), (13872105362393952754349431359811562438852850174570983468547543520699658249925004611495807236178361499147034035825072531229606915000 : ℤ)), ((3, 4, 4, 1), (-16126891622879833489599603074165155197318704582290958268760272053953655496911250859789111099370596209326644647781509690045983850000 : ℤ)), ((3, 4, 5, 0), (487782337458025692200156646471780509224004295840804790605998075296592657019786221784648102614273552928879441655948000309707417303750 : ℤ)),
    ((3, 6, 0, 3), (-1201117477331507617265980294673338679193214967354600853950798549951448498540120603859752499891929353706106067767860327672695346615000 : ℤ)), ((3, 6, 3, 0), (1540858729510193849522046697642565713062504655474954119032850205258382809180526621581340253950790964458790979790580647483228070524000 : ℤ)), ((3, 8, 0, 1), (64029338626578717316793070561865948340567357289068059619227827955018441481589278475677968311560078184479571869125503002232109125000 : ℤ)), ((3, 8, 1, 0), (41174370023593048527336708985729589488690490755830721611125298401927601424892721782257372198263440365220716352445982200189457218750 : ℤ)),
    ((4, 1, 3, 4), (40771657333435559822097091139165752019838601846378442917808305431390327364824969724414836116703412604232376439011758143249199975000 : ℤ)), ((4, 1, 4, 3), (26178091049418147282102833986646141506126093993329162584050170859055660799792491487110060298836847285329602219384170451552148475000 : ℤ)), ((4, 3, 0, 5), (-2165290958868882503852803282069196850870698365812135145608094228270260001574526503771513816942899034268125049755342578404184089566250 : ℤ)), ((4, 3, 1, 4), (1023702967433174327053431338002329787285319524065375887039948767224598426833370153736372775194531546547357954228755348952467562707100 : ℤ)),
    ((4, 3, 2, 3), (-165278673700701271754843113404796003439360791017122778893418025618014645420017315510510146560324392823247474843791983635567669627260 : ℤ)), ((4, 3, 3, 2), (46366072798557002194919120062040859143169465623118250069096013346737492107357753378939218432509022133588655491435709070581872125000 : ℤ)), ((4, 3, 4, 1), (-79016415221823657793514005629519773535304878231607456043009596549435299501740575893700920897849664507335288888487440877677376275000 : ℤ)), ((4, 3, 5, 0), (823102786968446396659579258564432171082650207621730385557572024517126848259153204980090956929480550947573932829499650353230384450000 : ℤ)),
    ((4, 5, 0, 3), (948216714078242794364653240425050189490517759111409768193231749095913130218857606249057949772043425418602287343066013152760876785000 : ℤ)), ((4, 5, 1, 2), (46948471329340561976952589297567151648347181368415706384598510506895367877579622611938163182658945690733039991252456317135730812500 : ℤ)), ((4, 5, 3, 0), (-1256748931571102811672366653946424101144641312342115358482973042966237943428983812294054542054746404317319432221999979762364581752500 : ℤ)), ((4, 7, 1, 0), (-10680934689165895914857244034572175944215821368774628781866975760870924787028917732824225682284649350403442825802418422540853750000 : ℤ)),
    ((5, 0, 2, 5), (-3560311563055298638285748011524058648071940456258209593955658586956974929009639244274741894094883116801147608600806140846951250000 : ℤ)), ((5, 0, 3, 4), (21093317259823291475691758814342319932650806664817928303585773193780955539978795246388742451568526790585043450651415732045998373000 : ℤ)), ((5, 0, 4, 3), (-134082091126413673016867875836006986204246179868511085418133479934195697102991318742294325383437751122417931239759227280381190750000 : ℤ)), ((5, 0, 7, 0), (-11443858595534888480204190037041617083088380037972816552000331172361705128959554713740241802447838589717974456216876881293771875000 : ℤ)),
    ((5, 2, 0, 5), (725397334591967685065463609574869804454639726211645717268589110343394181822802956321260924404591360712577633349422994046839566975000 : ℤ)), ((5, 2, 1, 4), (-274548877049541960982750653657825684889574190687548550693592608261043968739352698018748046057022918431244620900913764616677009382500 : ℤ)), ((5, 2, 2, 3), (113062463753838212791178099486357942926063938558135816413223686173654967461750197527311350966332573312731333319924327259865097625000 : ℤ)), ((5, 2, 5, 0), (-283357467153518317244527971071141570665936288973411601441641641637598513183426545694180396942477830895895593358403107387033206937500 : ℤ)),
    ((5, 4, 0, 3), (-768974451754310264375155492545592987490577308702870726548965986562907458445822632711580186310083396722640067427132037117655882892750 : ℤ)), ((5, 4, 1, 2), (-36158683049200475154273944885128941668974416784749626102479034929848310001166743924266902252141687249229520449683638086015246263750 : ℤ)), ((5, 4, 3, 0), (1004580493055288784715687892889908349667848035997617354404705094203919222757354128252135065353047740497439197662684529286304214431250 : ℤ)), ((6, 3, 0, 3), (704940571044534537556656716471818013418348148993597405528139870855109364141950990787587223210486377913027508036276875925758155576060 : ℤ)),
    ((6, 3, 3, 0), (-782297765106795038853387712983725323694459899947962378647068527405405087300534353629603979438657439258253954732525057683639919307500 : ℤ)), ((7, 0, 0, 5), (-387754367839838281553503098874507844232983257320143316206709309578343872001236095867368448857693682728402054333752725014348353775000 : ℤ)), ((7, 0, 1, 4), (248143748456321916759926045068408505124235076347193912129322862527105132391944609320040518594454092343849035060682564650711310322500 : ℤ)), ((7, 0, 2, 3), (4299275386532062825214474563331147195697649808901281787686437049863172599935936289797273657045204749279110456512968695013912250000 : ℤ)),
    ((7, 0, 5, 0), (138483702799942243411965392455181372940351163328622612930967610563694240000441462809774446020604886688715019404911687505124412062500 : ℤ)), ((7, 2, 0, 3), (-809265237770120013157582766851378365087014101315460711399592971337208108769463642599418407292179676303036011016466815816951328125000 : ℤ)), ((7, 2, 3, 0), (-44859925694496762842400424945203138965706449748853440883841298195657884105521454477861747865595527271694459868370157374671585750000 : ℤ)), ((7, 4, 0, 1), (-23108457819183931414485897586040816805642255428092521644274338385909023144604531049717982889691202618569442059332123366196079306250 : ℤ)),
    ((7, 4, 1, 0), (635769921974160471122455002057867615727132224331823141777796176242316951608864150763346766802657699428776358678715382294098437500 : ℤ)), ((8, 1, 0, 3), (670410455632068365084339379180034931021230899342555427090667399670978485514956593711471626917188755612089656198796136401905953750000 : ℤ)), ((8, 1, 3, 0), (-275049283172149975093571908881291089262869420101727147412558734603914038567041404330183063060683045087928037391307587516281813220000 : ℤ)), ((8, 3, 0, 1), (204010720313650809657644128272979780229945648741720300304022458725644965272374114867332561103039697387790084162317119910560237350000 : ℤ)),
    ((8, 3, 1, 0), (-127151457462290744857331118522928866020504750995259405916480706520442908436759109863982718323430944104579303797993457988984176300000 : ℤ)), ((9, 0, 0, 3), (-565606263690105328622841856811584861804112779183964556069981235691262752852079765189102918481921952214877661372419535421435843135000 : ℤ)), ((9, 0, 1, 2), (231084578191839314144858975860408168056422554280925216442743383859090231446045310497179828896912026185694420593321233661960793062500 : ℤ)), ((9, 0, 3, 0), (510886094644375770891000964250878952936506663697595467209922618877206497229922740748707499729392391291091254037954537140820342408500 : ℤ)),
    ((9, 2, 1, 0), (89719851388993525684800849890406277931412899497706881767682596391315768211042908955723495731191054543388919736740314749343171500000 : ℤ)), ((10, 1, 1, 0), (-53404673445829479574286220172860879721079106843873143909334878804354623935144588664121128411423246752017214129012092112704268750000 : ℤ)), ((11, 0, 1, 0), (-6357699219741604711224550020578676157271322243318231417777961762423169516088641507633467668026576994287763586787153822940984375000 : ℤ))
  ]

lemma hb_sc : allBound wsScalar = true := by decide
lemma hc_sc : compileScalar wsScalar = [(packKey 5 0 0 0 0, (1677912150040837402799230197533664816929276041112231127227542665068702070992401566875494159641616886545364510492834228653136027610000 : ℤ))] := by decide
lemma hk_sc : (1677912150040837402799230197533664816929276041112231127227542665068702070992401566875494159641616886545364510492834228653136027610000 : ℤ) ≠ 0 := by decide

theorem no_scalar_core_cert (c : ℂ) (N : Fin 4 → R4) :
    ¬ CoreCertificate (C c * core) N := by
  rintro ⟨hD_ne, -, hcore⟩
  have hreduced : (C c * core) *
      (2 * C c * coreSource * core - 5 * (∑ i, pderiv i core * N i) +
        3 * core * (∑ i, pderiv i (N i))) = 0 := by
    have hp : ∀ i : Fin 4, pderiv i (C c * core) = C c * pderiv i core := fun i => by
      rw [pderiv_mul, pderiv_C, zero_mul, zero_add]
    simp only [Fin.sum_univ_four, hp] at hcore ⊢
    linear_combination hcore
  have hlin0 : 2 * C c * coreSource * core - 5 * (∑ i, pderiv i core * N i) +
      3 * core * (∑ i, pderiv i (N i)) = 0 :=
    (mul_eq_zero.mp hreduced).resolve_left hD_ne
  have hz := eval_compileScalar_zero N c hlin0 wsScalar hb_sc
  rw [hc_sc, evalPairs, evalPairs, add_zero,
    valFn_pack N 0 c 5 0 0 0 0 (by omega) (by omega) (by omega) (by omega)] at hz
  have hc0 : c = 0 := (mul_eq_zero.mp hz).resolve_left (Int.cast_ne_zero.mpr hk_sc)
  apply hD_ne
  rw [hc0, map_zero, zero_mul]

def wsD4_0 : List (Exps × ℤ) :=
  [
    ((0, 1, 0, 9), (-11303753742947716214177144698127628682349343784245595547753390625 : ℤ)), ((0, 1, 1, 8), (4085496739148136312597344568065134334235116185615864817854687500 : ℤ)), ((0, 1, 2, 7), (-1816914408579866627691647846299266117644076565063153900634765625 : ℤ)), ((0, 1, 3, 6), (1016803833136777638335442469488029607773883517580075659453125000 : ℤ)),
    ((0, 1, 4, 5), (-544802772155750966333741816711462888438044591536215255436328125 : ℤ)), ((0, 1, 5, 4), (534180650020952303226025109932036532428597521281544402147656250 : ℤ)), ((0, 1, 6, 3), (-13649237221704000315452083912498733241572701533597618871857890625 : ℤ)), ((0, 1, 7, 2), (10023535019215097578204866593391271601990382829357873535156250 : ℤ)),
    ((0, 1, 8, 1), (-369110616012667667011589493027505378729952674629406707861328125 : ℤ)), ((0, 1, 9, 0), (414281118634594194530853918484751852257606803304247536382812500 : ℤ)), ((0, 3, 0, 7), (-32248711939132896414119069469548897764830951387933066221823281250 : ℤ)), ((0, 3, 1, 6), (19041026307116279231818351489858150798136301934484532059557650000 : ℤ)),
    ((0, 3, 2, 5), (-10957928716729665082589936500407711626969884541336806522924707000 : ℤ)), ((0, 3, 3, 4), (5951065890112603725377218416994019885325998677787961530121278670 : ℤ)), ((0, 3, 4, 3), (-31960516297223155760444341586931257073705683860469977822636548282 : ℤ)), ((0, 3, 5, 2), (858378428855597331478537665677100026852309023597326063759375000 : ℤ)),
    ((0, 3, 7, 0), (3386842426073900542404156489275705616750752589717665598236640000 : ℤ)), ((0, 5, 0, 5), (-14453806635173143795277233336996414259128004061684332784958593750 : ℤ)), ((0, 5, 1, 4), (8562059371969092058267262577878021604906247239877126766055328125 : ℤ)), ((0, 5, 2, 3), (-107817053298297332633883644857841290560277965597090445935910612500 : ℤ)),
    ((0, 5, 3, 2), (13649237221704000315452083912498733241572701533597618871857890625 : ℤ)), ((0, 5, 4, 1), (-10023535019215097578204866593391271601990382829357873535156250 : ℤ)), ((0, 5, 5, 0), (369110616012667667011589493027505378729952674629406707861328125 : ℤ)), ((0, 7, 0, 3), (460744078852442703095689465708827483329791509221047344359935125000 : ℤ)),
    ((0, 7, 1, 2), (-17382465756037562708550742528908999195748974617893228514261718750 : ℤ)), ((0, 7, 2, 1), (-8078342646681667254699411366468996731490424749140836231757812500 : ℤ)), ((0, 9, 0, 1), (4264896845907677301933992098449764767126584703739780499304218750 : ℤ)), ((0, 9, 1, 0), (13875637821867704690319396194949516022379747438028975290676075000 : ℤ)),
    ((1, 0, 0, 9), (-178456358367429199316174454515411594673673280120671864335937500 : ℤ)), ((1, 0, 1, 8), (99570141896114773339139279266888356032252990576073895019531250 : ℤ)), ((1, 0, 2, 7), (-53171050613318219967844194941589817933838956916324414062500000 : ℤ)), ((1, 0, 3, 6), (26969198538077975860095386521140741994392508680921467285156250 : ℤ)),
    ((1, 0, 4, 5), (-12790038236738341269569381864341681154756824183067769726562500 : ℤ)), ((1, 0, 5, 4), (5481281844683674168776228926132054775060694372535235128906250 : ℤ)), ((1, 0, 6, 3), (-38823432727590796531107021718014921663340767094154507226562500 : ℤ)), ((1, 0, 7, 2), (42098847080703409828460439692243340728359607883303068847656250 : ℤ)),
    ((1, 0, 8, 1), (-34690694168779878181260518812457015431544710173723779296875000 : ℤ)), ((1, 0, 9, 0), (25217093518346954132739373768489300074046907549740738769531250 : ℤ)), ((1, 2, 0, 7), (16044364928502377607157497112870881565862479390096689262218750000 : ℤ)), ((1, 2, 1, 6), (-9626618957101426564294498267722528939517487634058013557331250000 : ℤ)),
    ((1, 2, 2, 5), (5390906615976798876004919029924616206129793075072487592105500000 : ℤ)), ((1, 2, 3, 4), (16647824872811653247243380944442686044645802309205299032035856250 : ℤ)), ((1, 2, 4, 3), (16756987724635134983917333746691595320170036024259821753024609375 : ℤ)), ((1, 2, 7, 0), (-1925323791420285312858899653544505787903497526811602711466250000 : ℤ)),
    ((1, 4, 0, 5), (11925744817257179760673585462768005040350854069052993901469906250 : ℤ)), ((1, 4, 1, 4), (-7052540420550916464009213222888592677803370513836804420833381875 : ℤ)), ((1, 4, 2, 3), (88041033549408520417982774243238435865860582070416143291219530125 : ℤ)), ((1, 4, 3, 2), (-11457594579685842105673529082155332938588401134803168950915315625 : ℤ)),
    ((1, 4, 5, 0), (-303114778616884864653483070380613115046851304653956878744140625 : ℤ)), ((1, 6, 0, 3), (-406496033031031221678764669533636945360611501292782906212251087500 : ℤ)), ((1, 6, 1, 2), (13942793160915787204681713000759499664563251273993145660839843750 : ℤ)), ((1, 6, 2, 1), (6785807823212600493947505547833957254451956789278302434676562500 : ℤ)),
    ((1, 8, 0, 1), (-2024054075874103340609190715763940326954646512918660550034687500 : ℤ)), ((1, 8, 1, 0), (-11613555836442793400077157886335336589057687908230509539392125000 : ℤ)), ((2, 3, 0, 5), (401457311282607012152776598127633170018176654777863432872688221250 : ℤ)), ((2, 3, 1, 4), (-214723964881732671601114707528290504749895377959706274751190535775 : ℤ)),
    ((2, 3, 2, 3), (32895321368840478979330056077226837512969772318908804224598844688 : ℤ)), ((2, 3, 3, 2), (4813309478550713282147249133861264469758743817029006778665625000 : ℤ)), ((2, 3, 5, 0), (-146537832437479811977116567182231280506636899470938389271378896875 : ℤ)), ((2, 5, 0, 3), (341786396017359355485864339198723156418484698830800532493056538500 : ℤ)),
    ((2, 5, 1, 2), (-11942756045074451744924050673965665339132857491558266247441406250 : ℤ)), ((2, 5, 2, 1), (-5538511718564951069821916432851144159109835208010957320493156250 : ℤ)), ((2, 7, 0, 1), (678358908099637411003875796958475894707937311811262823226562500 : ℤ)), ((2, 7, 1, 0), (9348544903665208656387897724207421638789564550736049901128125000 : ℤ)),
    ((3, 0, 0, 7), (1099094237643764252340055968227074385236792482876304249218750000 : ℤ)), ((3, 0, 1, 6), (-769365966350634976638039177758952069665754738013412974453125000 : ℤ)), ((3, 0, 2, 5), (538556176445444483646627424431266448766028316609389082117187500 : ℤ)), ((3, 0, 3, 4), (-301591458809448910842111357681509211308975857301257885985625000 : ℤ)),
    ((3, 2, 0, 5), (-197282066414889128927981925036603619940723318782035610231500000 : ℤ)), ((3, 2, 1, 4), (-160750042105487287584940055522342703512457136267112132911200000 : ℤ)), ((3, 2, 2, 3), (-26929194707712615262825560258142594041681197998147980594649218750 : ℤ)), ((3, 4, 0, 3), (-278907862795323672047737445507815276757701614754565310904243345590 : ℤ)),
    ((3, 4, 1, 2), (7330596412488228281193431694972045102859955887378787208022068750 : ℤ)), ((3, 4, 2, 1), (4424309771168230691574894991307207700203331870382028543586345000 : ℤ)), ((3, 6, 0, 1), (-403838533166504492859660684478589572649379103357043231542968750 : ℤ)), ((3, 6, 1, 0), (-7388025460094640660691768130427949675648427154637912805039062500 : ℤ)),
    ((4, 1, 0, 5), (553276498790636441278649949888433929684294128548058466557812500 : ℤ)), ((4, 3, 0, 3), (-329289961621725681617039496535431646376256252205042001899372365003 : ℤ)), ((4, 5, 1, 0), (5914964621920321835133563526458260943150234832160874418897656250 : ℤ)), ((5, 0, 0, 5), (2869955132157089298510753807806499958843663148270026418835937500 : ℤ)),
    ((5, 0, 1, 4), (-1908870619003176450460362085992037789635286344843074169195000000 : ℤ)), ((5, 0, 2, 3), (25543541106732471507299433273311727149487944779954500365181656250 : ℤ)), ((5, 2, 0, 3), (161575168246275691576953361548855564250087187988887883567895312500 : ℤ)), ((5, 4, 1, 0), (-4844109110429016089486244165529776397616331267520325591344125000 : ℤ)),
    ((6, 1, 0, 3), (-3297282712931292757020167904681223155710377448628912747656250000 : ℤ)), ((6, 1, 1, 2), (2308097899051904929914117533276856208997264214040238923359375000 : ℤ)), ((6, 1, 2, 1), (-1615668529336333450939882273293799346298084949828167246351562500 : ℤ)), ((6, 3, 0, 1), (591846199244667386783945775109810859822169956346106830694500000 : ℤ)),
    ((6, 3, 1, 0), (4068419989467377996769149003142610960188932921775781119612600000 : ℤ)), ((7, 0, 0, 3), (-79415045055959791331741409389766690126002084573625773958075217500 : ℤ)), ((7, 0, 1, 2), (1469645547010640338128275438279410670628499275347064033105468750 : ℤ)), ((7, 0, 2, 1), (2280400724263282070755148122877533934489297043471756056279062500 : ℤ)),
    ((7, 2, 0, 1), (-1659829496371909323835949849665301789052882385644175399673437500 : ℤ)), ((7, 2, 1, 0), (-4647522589841346106740659579062845009348070679803691119085625000 : ℤ)), ((8, 1, 0, 1), (1084145779546732810107032216343296201257520254158924221601562500 : ℤ)), ((8, 1, 1, 0), (4525436174928096649415099304305967190242524727177890619703125000 : ℤ)),
    ((9, 0, 0, 1), (-1469645547010640338128275438279410670628499275347064033105468750 : ℤ)), ((9, 0, 1, 0), (-3525012444103824591014640089829161880787956958419845261578125000 : ℤ))
  ]

lemma hb_d4_0 : allBound wsD4_0 = true := by decide
lemma hk_d4_0 : (2111140211666142375894779503770564479162831001108805201899375000 : ℤ) ≠ 0 := by decide
lemma hc_d4_0 : compileStrict wsD4_0 = [(packKey 4 0 0 0 4, (2111140211666142375894779503770564479162831001108805201899375000 : ℤ))] := by decide

def wsD4_1 : List (Exps × ℤ) :=
  [
    ((0, 1, 0, 9), (-128368599428775682888628718750 : ℤ)), ((0, 1, 1, 8), (76981474492948273495977187500 : ℤ)), ((0, 1, 2, 7), (-45440005580364291534667968750 : ℤ)), ((0, 1, 3, 6), (25446403125004003259414062500 : ℤ)),
    ((0, 1, 4, 5), (-13644119008930717938142968750 : ℤ)), ((0, 1, 5, 4), (9839818095348152371792500000 : ℤ)), ((0, 1, 6, 3), (-3502775117702628011240718750 : ℤ)), ((0, 1, 8, 1), (-9088001116072858306933593750 : ℤ)),
    ((0, 1, 9, 0), (10282424119899576827273437500 : ℤ)), ((0, 3, 0, 7), (-52658047113425930698826343750 : ℤ)), ((0, 3, 1, 6), (26067478845627340895317950000 : ℤ)), ((0, 3, 2, 5), (-14597788153551310901378052000 : ℤ)),
    ((0, 3, 3, 4), (8845051106380529689877365620 : ℤ)), ((0, 3, 4, 3), (-1208760447833616485254306187502 : ℤ)), ((0, 3, 5, 2), (-81129554765819684482050000000 : ℤ)), ((0, 3, 7, 0), (5213495769125468179063590000 : ℤ)),
    ((0, 5, 0, 5), (-25446403125004003259414062500 : ℤ)), ((0, 5, 1, 4), (13644119008930717938142968750 : ℤ)), ((0, 5, 2, 3), (-2884322498601793703781924765000 : ℤ)), ((0, 5, 3, 2), (3502775117702628011240718750 : ℤ)),
    ((0, 5, 5, 0), (9088001116072858306933593750 : ℤ)), ((0, 7, 0, 3), (13206863338617942670186454718750 : ℤ)), ((0, 7, 1, 2), (-4578389652666845674410937500 : ℤ)), ((0, 9, 0, 1), (-3502775117702628011240718750 : ℤ)),
    ((1, 2, 0, 7), (180287899479599298849000000000 : ℤ)), ((1, 2, 1, 6), (-108172739687759579309400000000 : ℤ)), ((1, 2, 2, 5), (60576734225145364413264000000 : ℤ)), ((1, 2, 3, 4), (-41113625669756747126375737500 : ℤ)),
    ((1, 2, 4, 3), (28843854811801127748788906250 : ℤ)), ((1, 2, 7, 0), (-21634547937551915861880000000 : ℤ)), ((1, 4, 0, 5), (21374978625003362737907812500 : ℤ)), ((1, 4, 1, 4), (-11461059967501803068040093750 : ℤ)),
    ((1, 4, 2, 3), (2354390835003924674238480320100 : ℤ)), ((1, 4, 3, 2), (48750092364507252700468528125 : ℤ)), ((1, 4, 5, 0), (-7633920937501200977824218750 : ℤ)), ((1, 6, 0, 3), (-11096676176335006642201440618750 : ℤ)),
    ((1, 8, 0, 1), (-10302165684548531362800000000 : ℤ)), ((2, 3, 0, 5), (-181292111689754886360537847500 : ℤ)), ((2, 3, 1, 4), (97207103696506667639031245850 : ℤ)), ((2, 3, 2, 3), (808892558324188887285811416668 : ℤ)),
    ((2, 3, 3, 2), (54086369843879789654700000000 : ℤ)), ((2, 3, 5, 0), (64747182746341030843049231250 : ℤ)), ((2, 5, 0, 3), (9062745870804518278299656460375 : ℤ)), ((3, 0, 4, 3), (-516924234633774602299107318750 : ℤ)),
    ((3, 2, 0, 5), (7211515979183971953960000000 : ℤ)), ((3, 2, 1, 4), (-4038448948343024294217600000 : ℤ)), ((3, 2, 2, 3), (-19229236541200751832525937500 : ℤ)), ((3, 4, 0, 3), (-7243080369482302477413651951840 : ℤ)),
    ((3, 4, 1, 2), (34944783105172883521484981250 : ℤ)), ((4, 3, 0, 3), (-5538438322442936859005813031258 : ℤ)), ((5, 0, 2, 3), (684400638215820369383364825000 : ℤ)), ((5, 2, 0, 3), (115375419247204510995155625000 : ℤ)),
    ((6, 1, 0, 3), (2584621173168873011495536593750 : ℤ)), ((6, 3, 0, 1), (-21634547937551915861880000000 : ℤ)), ((7, 0, 0, 3), (-3696261619934928763580594748750 : ℤ))
  ]

lemma hb_d4_1 : allBound wsD4_1 = true := by decide
lemma hk_d4_1 : (3618469642436422216093751231250 : ℤ) ≠ 0 := by decide
lemma hc_d4_1 : compileStrict wsD4_1 = [(packKey 4 0 0 1 3, (3618469642436422216093751231250 : ℤ))] := by decide

def wsD4_2 : List (Exps × ℤ) :=
  [
    ((0, 1, 0, 9), (37790479724636867957655668430228386060309713957272901275459375 : ℤ)), ((0, 1, 1, 8), (-45788664702477326171098257778821720429000566894262460158750000 : ℤ)), ((0, 1, 2, 7), (31657661972397338902388828201013316349595716195678388582421875 : ℤ)), ((0, 1, 3, 6), (-17694047058375605076225739053073060985081920809456441773437500 : ℤ)),
    ((0, 1, 4, 5), (9466996395248714490209607737805843550398877383949349355234375 : ℤ)), ((0, 1, 5, 4), (-5695318109715924049107320986326555265080861491811144934406250 : ℤ)), ((0, 1, 6, 3), (-113979049931153928875082054488076352339083648123352233920390625 : ℤ)), ((0, 1, 7, 2), (-513654692503570636680071092415942560375203901851837490781250 : ℤ)),
    ((0, 1, 8, 1), (6625049361624365287152091978726059018704974040193870568359375 : ℤ)), ((0, 1, 9, 0), (-7324551904031901179332057512743788779133512184859214393750000 : ℤ)), ((0, 3, 0, 7), (-224625279600152063500763740008420903160033537361100618885468750 : ℤ)), ((0, 3, 1, 6), (133593090758380165502685283435641244595106654263690446441415625 : ℤ)),
    ((0, 3, 2, 5), (-74869576816847073426426065649231765394461436074771651509285250 : ℤ)), ((0, 3, 3, 4), (39409255994882053700908512169516835189840033419934756499309615 : ℤ)), ((0, 3, 4, 3), (-383082489904691455269691447290844350065031402249777462755128038 : ℤ)), ((0, 3, 5, 2), (24809163430652925371589688706386934872492246006597225923515625 : ℤ)),
    ((0, 3, 7, 0), (26636552448598632036362332508167294031590317014016658571008125 : ℤ)), ((0, 5, 0, 5), (18570840273663597093907778563432917265556917563745445423437500 : ℤ)), ((0, 5, 1, 4), (-9971749503688835484538029804504575733327683686408894992984375 : ℤ)), ((0, 5, 2, 3), (-964843563115788922504260368291573454948157759007465828412806250 : ℤ)),
    ((0, 5, 3, 2), (113979049931153928875082054488076352339083648123352233920390625 : ℤ)), ((0, 5, 4, 1), (513654692503570636680071092415942560375203901851837490781250 : ℤ)), ((0, 5, 5, 0), (-6625049361624365287152091978726059018704974040193870568359375 : ℤ)), ((0, 7, 0, 3), (3888842015882205566780985419022423593252314534392100877379600000 : ℤ)),
    ((0, 7, 1, 2), (-123853722175669887405050346730839154948295925859880142392343750 : ℤ)), ((0, 9, 0, 1), (17347964793651320324067147439744046554746093651803628395156250 : ℤ)), ((0, 9, 1, 0), (-587191720672031132111670183784737945203583916894838430187500 : ℤ)), ((1, 0, 0, 9), (13246838009350092615529042706654258004190325676329296875000 : ℤ)),
    ((1, 0, 1, 8), (-7391104202351410652278064067153958095183460682094726562500 : ℤ)), ((1, 0, 2, 7), (3946893799162803275686833489952297062486987908203125000000 : ℤ)), ((1, 0, 3, 6), (-2001927011983253869732034059580422454209838472583007812500 : ℤ)), ((1, 0, 4, 5), (949406152884880429286918801236417051172230797673828125000 : ℤ)),
    ((1, 0, 5, 4), (-406876243269618186272997728586395807446825449745195312500 : ℤ)), ((1, 0, 6, 3), (2881868312309800343833235814808792062236251106548828125000 : ℤ)), ((1, 0, 7, 2), (-3125002733218739469788890421892958511743121340161132812500 : ℤ)), ((1, 0, 8, 1), (2575094607386126066445304081929292847779181204589843750000 : ℤ)),
    ((1, 0, 9, 0), (-1871868035188722811915152001589966118144356954282226562500 : ℤ)), ((1, 2, 0, 7), (-55131474290339834159088197125304299716649435570216057607812500 : ℤ)), ((1, 2, 1, 6), (33078884574203900495452918275182579829989661342129634564687500 : ℤ)), ((1, 2, 2, 5), (-18524175361554184277453634234102244704794210351592595356225000 : ℤ)),
    ((1, 2, 3, 4), (187045336279444618884561765778301344616805221178336548369441250 : ℤ)), ((1, 2, 4, 3), (113874514827401058959970347049664167863757534426325092064921875 : ℤ)), ((1, 2, 7, 0), (6615776914840780099090583655036515965997932268425926912937500 : ℤ)), ((1, 4, 0, 5), (-15580674045560370924784510963677810407999342601061413264281250 : ℤ)),
    ((1, 4, 1, 4), (8364061770714708616775410936149816994896238747984424037106875 : ℤ)), ((1, 4, 2, 3), (787360605791904090575945304695945990621013087395664174111838500 : ℤ)), ((1, 4, 3, 2), (-95742978315831762215137692417147097723242711673837186258753125 : ℤ)), ((1, 4, 5, 0), (5564526444842989615994468201313503717142622357521933308671875 : ℤ)),
    ((1, 6, 0, 3), (-3426541894722324528319234527634918776428550426707431772826412500 : ℤ)), ((1, 6, 1, 2), (101663236242962366902594791572406984286693311012301212557812500 : ℤ)), ((1, 8, 0, 1), (-386972810159301621671051432357997380505684054644175461250000 : ℤ)), ((1, 8, 1, 0), (396524090816336980161272341159780256018262761058589241250000 : ℤ)),
    ((2, 3, 0, 5), (3717646467532611459263999952110156908940875545572984846984397750 : ℤ)), ((2, 3, 1, 4), (-1993332628860158518708895801906458206007730264886852017787166365 : ℤ)), ((2, 3, 2, 3), (337957474720240895116494529347789003342218218739771736764981192 : ℤ)), ((2, 3, 3, 2), (-16539442287101950247726459137591289914994830671064817282343750 : ℤ)),
    ((2, 3, 5, 0), (-1328346374034727457718453271381548914848902441495048175731133125 : ℤ)), ((2, 5, 0, 3), (2874060601287958708876741235578946500008542044356216864162796500 : ℤ)), ((2, 5, 1, 2), (-87551343149870166132766134618546932595886494516770574877031250 : ℤ)), ((2, 7, 0, 1), (3116736560189610817711452343711622739380031694875192539062500 : ℤ)),
    ((2, 7, 1, 0), (-286585996471250323415470342941959596321738083984204421875000 : ℤ)), ((3, 0, 0, 7), (-2051642576935026604368104474023872185775345968035767931875000 : ℤ)), ((3, 0, 5, 2), (-4308449411563555869173019395450131590128226532875112656937500 : ℤ)), ((3, 2, 0, 5), (-1720696859215308646791742289957843477479030150796261016187500 : ℤ)),
    ((3, 2, 1, 4), (994586401036888002150041298131229559877325307982579862915000 : ℤ)), ((3, 2, 2, 3), (-204010125808798732743465697284349277028762401752669113612281250 : ℤ)), ((3, 4, 0, 3), (-2343272319244995649726276756829841736849755767497212571996515810 : ℤ)), ((3, 4, 1, 2), (49632780466585449924821860664024178191675077218965648610693750 : ℤ)),
    ((3, 4, 2, 1), (861689882312711173834603879090026318025645306575022531387500 : ℤ)), ((3, 6, 0, 1), (-2630379645863976053046118531079568841424990262867010950000000 : ℤ)), ((3, 6, 1, 0), (206233618182681966397199113458189987942121800865553906250000 : ℤ)), ((4, 1, 0, 5), (-41069784349009887228328541206019134485878797239497390625000 : ℤ)),
    ((4, 3, 0, 3), (-2431722999587431163021554319959141960222148677859607708091059027 : ℤ)), ((4, 5, 1, 0), (-147791022856503099435740148667151213391725728372422445312500 : ℤ)), ((5, 0, 0, 5), (-184313989146539833240766227939240105776261847902442898437500 : ℤ)), ((5, 0, 1, 4), (120179311533362141506767158737793376887811024395129913750000 : ℤ)),
    ((5, 0, 2, 3), (231080686006072582512706592685214288146009195356970707939812500 : ℤ)), ((5, 2, 0, 3), (1224060754852792396460794183706095662172574410516014681673687500 : ℤ)), ((5, 4, 1, 0), (105479663168980534290702253103969861501831984755727869687500 : ℤ)), ((6, 1, 0, 3), (42345902787938949114157676343852721914403140780258250113900000 : ℤ)),
    ((6, 1, 1, 2), (21542247057817779345865096977250657950641132664375563284687500 : ℤ)), ((6, 3, 0, 1), (5162090577645925940375226869873530432437090452388783048562500 : ℤ)), ((6, 3, 1, 0), (-464942398144727399199984236322558187336026353050105407750000 : ℤ)), ((7, 0, 0, 3), (-709506037680430019443365577723471024951083308644491068916082500 : ℤ)),
    ((7, 0, 1, 2), (8022791786982313754310331470338163742686586394245634920312500 : ℤ)), ((7, 2, 0, 1), (123209353047029661684985623618057403457636391718492171875000 : ℤ)), ((7, 2, 1, 0), (344986188531683052717959746130560729681381896811778081250000 : ℤ)), ((8, 1, 0, 1), (552941967439619499722298683817720317328785543707328695312500 : ℤ)),
    ((8, 1, 1, 0), (-254452164169497523379071066377283764796565843546428359375000 : ℤ)), ((9, 0, 0, 1), (-8022791786982313754310331470338163742686586394245634920312500 : ℤ)), ((9, 0, 1, 0), (186647960304820692353194717764371577472176270771069843750000 : ℤ))
  ]

lemma hb_d4_2 : allBound wsD4_2 = true := by decide
lemma hk_d4_2 : (30159145880944891084211135768150921130897585730125788598562500 : ℤ) ≠ 0 := by decide
lemma hc_d4_2 : compileStrict wsD4_2 = [(packKey 4 0 0 2 2, (30159145880944891084211135768150921130897585730125788598562500 : ℤ))] := by decide

def wsD4_3 : List (Exps × ℤ) :=
  [
    ((0, 1, 0, 9), (5139886293444096412138590262605677127225326332886889790242984375 : ℤ)), ((0, 1, 1, 8), (-3909291513305439998647782114094756184418441222766843219833750000 : ℤ)), ((0, 1, 2, 7), (2464097287221820247366718505502838123526221655120069323005859375 : ℤ)), ((0, 1, 3, 6), (-1379522028363223829161201907728795163072477364559840917539062500 : ℤ)),
    ((0, 1, 4, 5), (736931983327683960331793257803039783311740818195962973226171875 : ℤ)), ((0, 1, 5, 4), (-491469098952601058147662905390756128960684095629330605725781250 : ℤ)), ((0, 1, 6, 3), (-3985816898169921486548959027386138780281003741162605072847015625 : ℤ)), ((0, 1, 7, 2), (-5586787214932640462406830291912791533101434610968550163281250 : ℤ)),
    ((0, 1, 8, 1), (496011907281468415451861889838803505581302293658853036123046875 : ℤ)), ((0, 1, 9, 0), (-572004241613506070456035122228044550178085691666101466515625000 : ℤ)), ((0, 3, 0, 7), (-6924766620121687404864604190806315585259358226358438913626156250 : ℤ)), ((0, 3, 1, 6), (4142308030809210655520088247387708746774756137185265896842525000 : ℤ)),
    ((0, 3, 2, 5), (-2242016806571628861308374628873121731485013758424414741671371000 : ℤ)), ((0, 3, 3, 4), (1139554392857049013057721617999803958781808587360357308284303510 : ℤ)), ((0, 3, 4, 3), (-15194913796709060465059258100649857952882552216836467409120331231 : ℤ)), ((0, 3, 5, 2), (1274612737128909320494838711665339003381598747903529255262500000 : ℤ)),
    ((0, 3, 6, 1), (-18092086216358259297778699065466245024473950335412415625000000 : ℤ)), ((0, 3, 7, 0), (948042157714673358078495300933471151807819315786298368561995000 : ℤ)), ((0, 5, 0, 5), (4837466690132791207671568005430823862930138556444036891267968750 : ℤ)), ((0, 5, 1, 4), (-2803208254324388196921620502287242459998818244245686006266703125 : ℤ)),
    ((0, 5, 2, 3), (-32517900046069643235045467132402679646641462824252227380592357500 : ℤ)), ((0, 5, 3, 2), (3985816898169921486548959027386138780281003741162605072847015625 : ℤ)), ((0, 5, 4, 1), (5586787214932640462406830291912791533101434610968550163281250 : ℤ)), ((0, 5, 5, 0), (-466092119701165944138160366259288702872078498291664753783203125 : ℤ)),
    ((0, 7, 0, 3), (120373051185919460102172434471573602660979018761463915771426812500 : ℤ)), ((0, 7, 1, 2), (-3684571571615849330989767035556426985898056999078088644091718750 : ℤ)), ((0, 7, 2, 1), (2094385130621172991959106650566036189645665675703179763789062500 : ℤ)), ((0, 7, 3, 0), (18092086216358259297778699065466245024473950335412415625000000 : ℤ)),
    ((0, 9, 0, 1), (54779342357134512602686840774841268737849880551413094988843750 : ℤ)), ((0, 9, 1, 0), (-3601509915189107647908296366155533182235118105924715738971575000 : ℤ)), ((1, 0, 0, 9), (114661588082802737321609863639930944041755660425800096796225000 : ℤ)), ((1, 0, 1, 8), (-65622939517378150799373162506742877701641935123211705630906250 : ℤ)),
    ((1, 0, 2, 7), (35542522316486927473054997952562744141404759195832238704687500 : ℤ)), ((1, 0, 3, 6), (-18339512077051540055436886371699555089918263458594859628906250 : ℤ)), ((1, 0, 4, 5), (11561877185011145040858965644701738968436938575752681946875000 : ℤ)), ((1, 0, 5, 4), (-9344120256051405933972433004906381213786958031842534879656250 : ℤ)),
    ((1, 0, 6, 3), (18094857198672554618909595768199010572720867097494746729300000 : ℤ)), ((1, 0, 7, 2), (-23464506302717089942108687226033724439026025366067910685781250 : ℤ)), ((1, 0, 8, 1), (20516793779135722604387392291103248507724394905490968132812500 : ℤ)), ((1, 0, 9, 0), (-2094101205893114629727114770424077215123524855471399660156250 : ℤ)),
    ((1, 2, 0, 7), (-7391678475697635388584318190420469309237654924309549304750000000 : ℤ)), ((1, 2, 1, 6), (4438806423524016467603124441056029496997732484156166190131250000 : ℤ)), ((1, 2, 2, 5), (-2486998043208594300008594195925959155470443367650931935567250000 : ℤ)), ((1, 2, 3, 4), (7927571261425718649448170072089300981468653582832740158713531250 : ℤ)),
    ((1, 2, 4, 3), (3180328835045316776459826447908682025800455151395476235556609375 : ℤ)), ((1, 2, 6, 1), (18996690527176172262667634018739557275697647852183036406250000 : ℤ)), ((1, 2, 7, 0), (876906032974988337941957668771926152384862126629985788651250000 : ℤ)), ((1, 4, 0, 5), (-3980037265591535840038765275501317638556971196926996264205718750 : ℤ)),
    ((1, 4, 1, 4), (2302115990447453737036414878033178693990529649733106779328780625 : ℤ)), ((1, 4, 2, 3), (26531512696316821103687466764110411618397505316551951768420489675 : ℤ)), ((1, 4, 3, 2), (-3351705165902468559624907502157996377550587315996087210537353125 : ℤ)), ((1, 4, 5, 0), (395791562315636940523013655801846005469583722286712918606484375 : ℤ)),
    ((1, 6, 0, 3), (-106637813298202419947666631136340489245645050749397830514907818750 : ℤ)), ((1, 6, 1, 2), (3108799489996482061562449189543446780504109360665289633600781250 : ℤ)), ((1, 6, 2, 1), (-1759283509721785313245649586475470399302359167590671001582812500 : ℤ)), ((1, 6, 3, 0), (-18996690527176172262667634018739557275697647852183036406250000 : ℤ)),
    ((1, 8, 0, 1), (478104711444496504657091775719925263142639270763976083553437500 : ℤ)), ((1, 8, 1, 0), (3014262273896237055648142057035307401552844122568746862064625000 : ℤ)), ((2, 1, 0, 7), (-99732625267674904379005078598382675697412651223960941132812500 : ℤ)), ((2, 1, 1, 6), (55850270149897946452242844015094298390551084685418127034375000 : ℤ)),
    ((2, 1, 2, 5), (-29946382947040517954869258267141038089409772074181338590812500 : ℤ)), ((2, 1, 3, 4), (15265436560590337211523508015314808393834218651648653127480000 : ℤ)), ((2, 1, 6, 1), (-19946525053534980875801015719676535139482530244792188226562500 : ℤ)), ((2, 1, 7, 0), (22568068346285292648049149214262594043528805648393447250625000 : ℤ)),
    ((2, 3, 0, 5), (140753654495985162998319930797855660067064660664503763860388336250 : ℤ)), ((2, 3, 1, 4), (-75609197059546919547965658133404581236664433392075982003430932675 : ℤ)), ((2, 3, 2, 3), (12586323578883273197366016757470856625853739477276370702141366654 : ℤ)), ((2, 3, 3, 2), (-2245998578500054874969296908154250128684842949071139346034375000 : ℤ)),
    ((2, 3, 5, 0), (-49449845695704287979796158752166691984231470790426629955294659375 : ℤ)), ((2, 5, 0, 3), (89564674483084919167730557043733021171935455680722374477497228000 : ℤ)), ((2, 5, 1, 2), (-2693730827018037332767763912107320032679235747809345445223906250 : ℤ)), ((2, 5, 2, 1), (1435910445553876203287163519628074411621068387262100046053781250 : ℤ)),
    ((2, 5, 3, 0), (19946525053534980875801015719676535139482530244792188226562500 : ℤ)), ((2, 7, 0, 1), (31394726131445606207061241227875640054468658237933298414062500 : ℤ)), ((2, 7, 1, 0), (-2426350383418835564888149864426008682893020193709563892190625000 : ℤ)), ((3, 0, 0, 7), (-26785333643318402890361363966422775758733683471578081332812500 : ℤ)),
    ((3, 0, 1, 6), (-39893050107069961751602031439353070278965060489584376453125000 : ℤ)), ((3, 0, 6, 1), (-83775405224846919678364266022641447585826627028127190551562500 : ℤ)), ((3, 2, 0, 5), (-53990106517294349582803495994123882142276480448515535359750000 : ℤ)), ((3, 2, 1, 4), (100654410752353877003896266745809063607254075216624347763900000 : ℤ)),
    ((3, 2, 2, 3), (-6498251368482319788230101692577845175098325117187904196750593750 : ℤ)), ((3, 4, 0, 3), (-73146954325873400374391342686983080818599625618443702568247813145 : ℤ)), ((3, 4, 1, 2), (1462216741560042166816327784608073466276842927720543587634043750 : ℤ)), ((3, 4, 2, 1), (-1147043274006578327445343145894461255608271225654599992781645000 : ℤ)),
    ((3, 6, 0, 1), (-69459142652531015092293572321188046516308451192943483344531250 : ℤ)), ((3, 6, 1, 0), (1917489118505895098046631922986484268792583583551411033945312500 : ℤ)), ((4, 1, 0, 5), (-143625242340389019594540432299241696235182594243598375589062500 : ℤ)), ((4, 3, 0, 3), (-69244550221433316900742278213107141956411747847706957476381246799 : ℤ)),
    ((4, 5, 1, 0), (-1535111438165611901495210543527811321727935474586130365663281250 : ℤ)), ((5, 0, 0, 5), (-757775466938914702191042686422991882584650317453173148882812500 : ℤ)), ((5, 0, 1, 4), (502665677480301193695745507591646246147902877181189295458750000 : ℤ)), ((5, 0, 2, 3), (7853921664328894949375201137088205610240808474262877382530218750 : ℤ)),
    ((5, 2, 0, 3), (39288706086696943442517625391262219077682188656799308003902000000 : ℤ)), ((5, 4, 1, 0), (1257103822632712013393612051247865970854822089734743579496625000 : ℤ)), ((6, 1, 0, 3), (80356000929955208671084091899268327276201050414734243998437500 : ℤ)), ((6, 1, 1, 2), (823392554209924010553065928908247370557838848505021529992500000 : ℤ)),
    ((6, 1, 2, 1), (418877026124234598391821330113207237929133135140635952757812500 : ℤ)), ((6, 3, 0, 1), (161970319551883048748410487982371646426829441345546606079250000 : ℤ)), ((6, 3, 1, 0), (-1056299266540035618562894634836495344113688692481834719436600000 : ℤ)), ((7, 0, 0, 3), (-21376388076659618458718997805118215904409474410812109223957333750 : ℤ)),
    ((7, 0, 1, 2), (151249867022196977710737878532548001496342530130188481010156250 : ℤ)), ((7, 0, 2, 1), (-591215002586776833158742105931212501534262196455640459035312500 : ℤ)), ((7, 2, 0, 1), (430875727021167058783621296897725088705547782730795126767187500 : ℤ)), ((7, 2, 1, 0), (1206452035659267764594139631313630248375533791646226354948125000 : ℤ)),
    ((8, 1, 0, 1), (-239935755928663483777799921410267779820847858484296269898437500 : ℤ)), ((8, 1, 1, 0), (-1174671239917634407031424047921561878507480491111184981265625000 : ℤ)), ((9, 0, 0, 1), (-151249867022196977710737878532548001496342530130188481010156250 : ℤ)), ((9, 0, 1, 0), (915112856850796671782390159086167895500699285631699735640625000 : ℤ))
  ]

lemma hb_d4_3 : allBound wsD4_3 = true := by decide
lemma hk_d4_3 : (586427836573928437748549862158490133100786389196890333860937500 : ℤ) ≠ 0 := by decide
lemma hc_d4_3 : compileStrict wsD4_3 = [(packKey 4 0 0 3 1, (586427836573928437748549862158490133100786389196890333860937500 : ℤ))] := by decide

def wsD4_4 : List (Exps × ℤ) :=
  [
    ((0, 1, 0, 9), (8982683609556579343479243019621502143818655718873990293410061265625 : ℤ)), ((0, 1, 1, 8), (-5690026128263442126416543825744638552643216949616168039247306250000 : ℤ)), ((0, 1, 2, 7), (3395230953511200969092354868350706448488042036955521245117431640625 : ℤ)), ((0, 1, 3, 6), (-1900953117285218002695950103616923658759175501659563331745742187500 : ℤ)),
    ((0, 1, 4, 5), (1019049018672303474305204303975388618700081698130598859355086328125 : ℤ)), ((0, 1, 5, 4), (-725219864169717928840606718424534635254020271997215961534130468750 : ℤ)), ((0, 1, 6, 3), (-1291805168416252228301459054530178882073815697320115462357386484375 : ℤ)), ((0, 1, 7, 2), (-5643250215818099936529339892079285911920585532928482800292968750 : ℤ)),
    ((0, 1, 8, 1), (682270905111279108067916310751329453075848741981349096337939453125 : ℤ)), ((0, 1, 9, 0), (-770059712092060233720856484009858704938034381464112149970828125000 : ℤ)), ((0, 3, 0, 7), (-114568060256072549664526114238904529909611208860182729310562968750 : ℤ)), ((0, 3, 1, 6), (131215584106115020332936686575002185203874972775457103892910237500 : ℤ)),
    ((0, 3, 2, 5), (92578366311756513903999847525062638633461738114082826489244416000 : ℤ)), ((0, 3, 3, 4), (-145302096426786961998471457603133352032904633488189575209152016210 : ℤ)), ((0, 3, 4, 3), (-8997961058657836782006767136130363463306913452260714379108328604734 : ℤ)), ((0, 3, 5, 2), (1242541685775371302165933476274105783922738735843686366020464062500 : ℤ)),
    ((0, 3, 7, 0), (263470393122910040195793611610805954680248884367003998877545117500 : ℤ)), ((0, 5, 0, 5), (9535269030249557089920036790896427911726451577915797020247117968750 : ℤ)), ((0, 5, 1, 4), (-5571563152201218875948657212680640044854427266704832718864989578125 : ℤ)), ((0, 5, 2, 3), (-9550968915411989518067871519145285292414740665131293567663168912500 : ℤ)),
    ((0, 5, 3, 2), (1291805168416252228301459054530178882073815697320115462357386484375 : ℤ)), ((0, 5, 4, 1), (5643250215818099936529339892079285911920585532928482800292968750 : ℤ)), ((0, 5, 5, 0), (-682270905111279108067916310751329453075848741981349096337939453125 : ℤ)), ((0, 7, 0, 3), (18199050267658594637724772209020025187485749163105456749181524625000 : ℤ)),
    ((0, 7, 1, 2), (12102895953593972345378403797283078945089653175319025327980468750 : ℤ)), ((0, 7, 2, 1), (4548106910081778664395768599322045159829109133766290798479648437500 : ℤ)), ((0, 9, 0, 1), (-1013170550936302037220726449606773198253651317008786602266282968750 : ℤ)), ((0, 9, 1, 0), (-7811984093711517740649820057756577520599797807610313088650630225000 : ℤ)),
    ((1, 0, 0, 9), (100470929760862639215006217892176727801278056707938259621132812500 : ℤ)), ((1, 0, 1, 8), (-56057989887512617389935414227258144446158433694329602895996093750 : ℤ)), ((1, 0, 2, 7), (29935301495298157841896281752115067496751332743890645117187500000 : ℤ)), ((1, 0, 3, 6), (-15183658776937900409233702611402237742842982387358786081542968750 : ℤ)),
    ((1, 0, 4, 5), (7200791527283686134767561989624366490128092015067154356054687500 : ℤ)), ((1, 0, 5, 4), (-3085961678556908557021016885412346838359170931737337377574218750 : ℤ)), ((1, 0, 6, 3), (21857592625633618447013253227242400896460851874008987568554687500 : ℤ)), ((1, 0, 7, 2), (-23701650906436019733423227546733000830066459238299627761230468750 : ℤ)),
    ((1, 0, 8, 1), (19530860817023071416049672091413299687959671827806487744140625000 : ℤ)), ((1, 0, 9, 0), (-14197223650829335176732267431659475941688408950504035927246093750 : ℤ)), ((1, 2, 0, 7), (-12868107990793666592359337945769224319448550821355504810000250000000 : ℤ)), ((1, 2, 1, 6), (7720864794476199955415602767461534591669130492813302886000150000000 : ℤ)),
    ((1, 2, 2, 5), (-4323684284906671975032737549778459371334713075975449616160084000000 : ℤ)), ((1, 2, 3, 4), (5231567913122337850330449596909149131698559397156333930903851993750 : ℤ)), ((1, 2, 4, 3), (-459706014950155320029506760708076232597780556388123870829046484375 : ℤ)), ((1, 2, 7, 0), (1544172958895239991083120553492306918333826098562660577200030000000 : ℤ)),
    ((1, 4, 0, 5), (-7830128081868330446802229249906323748966813269136899384325408781250 : ℤ)), ((1, 4, 1, 4), (4568933305447003140655005479866419088111246177490517012186518214375 : ℤ)), ((1, 4, 2, 3), (7778759919863170494819166797612221640527750161060240980284069602125 : ℤ)), ((1, 4, 3, 2), (-1089487859994778595462628256450798741121297356123698785893915584375 : ℤ)),
    ((1, 4, 5, 0), (569201388130069836493839766612834080646121008898771943375041015625 : ℤ)), ((1, 6, 0, 3), (-16901925747780950513350650317389751571879524765254791843713575237500 : ℤ)), ((1, 6, 1, 2), (173877533082865907848371724257827613990503939356421187197167968750 : ℤ)), ((1, 6, 2, 1), (-3820409804468694078092445623430517934256451672363684270722904687500 : ℤ)),
    ((1, 8, 0, 1), (1075903636908102430263206659198923537607080023592381545724216562500 : ℤ)), ((1, 8, 1, 0), (6538431935917292684243439890006794499639478292333776870677766375000 : ℤ)), ((2, 3, 0, 5), (66160013929855396176784148484798595114869829790849614011096570498750 : ℤ)), ((2, 3, 1, 4), (-35774798573913315491032344546200414699297616742526250307908758827425 : ℤ)),
    ((2, 3, 2, 3), (5990572108469495206440925821555386922907882532723596902520232090656 : ℤ)), ((2, 3, 3, 2), (-3860432397238099977707801383730767295834565246406651443000075000000 : ℤ)), ((2, 3, 5, 0), (-21849371831257131577882434544495242587300313608856946382506552153125 : ℤ)), ((2, 5, 0, 3), (14254330890798416666635293154567908358657019294930442447979090699500 : ℤ)),
    ((2, 5, 1, 2), (-185756411653300127387155069948937122546776253540885906727402343750 : ℤ)), ((2, 5, 2, 1), (3118182097552067452309738951695194161578837222110168971437646968750 : ℤ)), ((2, 7, 0, 1), (-134475581624863930731401970572323020667332242529966230755851562500 : ℤ)), ((2, 7, 1, 0), (-5263230780763512473546386418728778382638524842064396094335134375000 : ℤ)),
    ((3, 0, 0, 7), (189044208874727451402489626535056794260728307054724330865625000000 : ℤ)), ((3, 0, 1, 6), (-132330946212309215981742738574539755982509814938307031605937500000 : ℤ)), ((3, 0, 2, 5), (13463904411136112091165685610781661219150707915234727052929687500 : ℤ)), ((3, 0, 7, 0), (-113096797053543341565791759130565954240865946487971707244609375000 : ℤ)),
    ((3, 2, 0, 5), (-9343353565592949506228845304602360814326906645653403158415500000 : ℤ)), ((3, 2, 1, 4), (157933641601407639202223545955196653428447683385550223791505600000 : ℤ)), ((3, 2, 2, 3), (-921027626938537806125882313059301537848231367460643943068622656250 : ℤ)), ((3, 4, 0, 3), (-11776400205634740348081427963007287521854105459564291272802983807830 : ℤ)),
    ((3, 4, 1, 2), (-69428021226529999052707902390743028497534460802610426417557518750 : ℤ)), ((3, 4, 2, 1), (-2490886401167713879356665880105957935214475843025082070039112235000 : ℤ)), ((3, 6, 0, 1), (19511087919147206882413678744594846636881805413404558833300781250 : ℤ)), ((3, 6, 1, 0), (4159458334033282691969465457430935667390064488061144909236992187500 : ℤ)),
    ((4, 1, 0, 5), (-311494668819128316439879921787188302412257594372556916672048437500 : ℤ)), ((4, 3, 0, 3), (4959421396314805138579992711515732583887260049665552369024589877939 : ℤ)), ((4, 5, 1, 0), (-3330125082141141193180196265396000910993582210506572297839380468750 : ℤ)), ((5, 0, 0, 5), (-1632280771646790070505806400669412737365864783410676523052679687500 : ℤ)),
    ((5, 0, 1, 4), (1083931936554503667057964978263155101465320373470055680835691250000 : ℤ)), ((5, 0, 2, 3), (2446711614186120820692494818469004744683038318363930840285071281250 : ℤ)), ((5, 2, 0, 3), (5526165761631226836755293878355809227089388204763863658411735937500 : ℤ)), ((5, 4, 1, 0), (2727233429171536058380755465193264111857994503613943307926742375000 : ℤ)),
    ((6, 1, 0, 3), (-567132626624182354207468879605170382782184921164172992596875000000 : ℤ)), ((6, 1, 1, 2), (396992838636927647945228215723619267947529444814921094817812500000 : ℤ)), ((6, 1, 2, 1), (909621382016355732879153719864409031965821826753258159695929687500 : ℤ)), ((6, 3, 0, 1), (28030060696778848518686535913807082442980719936960209475246500000 : ℤ)),
    ((6, 3, 1, 0), (-2290520454070133812181030888769289970586369234959764770341893800000 : ℤ)), ((7, 0, 0, 3), (-3056309362913800185980147846560710095643227855242859515830215047500 : ℤ)), ((7, 0, 1, 2), (-192077544033099760113313206990502630314773180594384959599316406250 : ℤ)), ((7, 0, 2, 1), (-1283865607760227805835148393180051605117474235474598659685112187500 : ℤ)),
    ((7, 2, 0, 1), (934484006457384949319639765361564907236772783117670750016145312500 : ℤ)), ((7, 2, 1, 0), (2616555218080677858094991343012381740262963792729478100045206875000 : ℤ)), ((8, 1, 0, 1), (-560885977157764185757503117178215979697336610287519389017539062500 : ℤ)), ((8, 1, 1, 0), (-2547820566484518413620700908324259528106541421401152418892859375000 : ℤ)),
    ((9, 0, 0, 1), (192077544033099760113313206990502630314773180594384959599316406250 : ℤ)), ((9, 0, 1, 0), (1984582006030453244741242370573818138883619767590372882268484375000 : ℤ))
  ]

lemma hb_d4_4 : allBound wsD4_4 = true := by decide
lemma hk_d4_4 : (791677579374803390960542313913961679686061625415801950712265625000 : ℤ) ≠ 0 := by decide
lemma hc_d4_4 : compileStrict wsD4_4 = [(packKey 4 0 0 4 0, (791677579374803390960542313913961679686061625415801950712265625000 : ℤ))] := by decide

def wsD4_5 : List (Exps × ℤ) :=
  [
    ((0, 0, 0, 10), (-54014011203995133046875000 : ℤ)), ((0, 0, 1, 9), (-1716937254691040025000000 : ℤ)), ((0, 0, 2, 8), (19947262266639287729625000 : ℤ)), ((0, 0, 3, 7), (1185721073168044641165000000 : ℤ)),
    ((0, 0, 4, 6), (-773104138206596446359375000 : ℤ)), ((0, 0, 5, 5), (479471752933924717968750000 : ℤ)), ((0, 0, 6, 4), (-284786661060184579734375000 : ℤ)), ((0, 0, 7, 3), (162391847440595837557500000 : ℤ)),
    ((0, 0, 8, 2), (1636505058487371709604625000 : ℤ)), ((0, 0, 9, 1), (-698001533073460620112500000 : ℤ)), ((0, 0, 10, 0), (244237191257801065078125000 : ℤ)), ((0, 2, 0, 8), (898599451785765648410781250 : ℤ)),
    ((0, 2, 4, 4), (-1369852171149232541133285000 : ℤ)), ((0, 2, 5, 3), (30192941580001725786602250000 : ℤ)), ((0, 4, 0, 6), (-118343538136418078888345077500 : ℤ)), ((0, 4, 1, 5), (66272381356394124177473243400 : ℤ)),
    ((0, 4, 2, 4), (-35534619717761801820873748604 : ℤ)), ((0, 4, 3, 3), (1850413053326444681180904226 : ℤ)), ((0, 4, 4, 2), (37673115377528942064598162500 : ℤ)), ((0, 4, 6, 0), (-23668707627283615777669015500 : ℤ)),
    ((0, 6, 1, 3), (1369852171149232541133285000 : ℤ)), ((0, 6, 2, 2), (-30192941580001725786602250000 : ℤ)), ((0, 8, 0, 2), (4492997258928828242053906250 : ℤ)), ((1, 3, 0, 6), (51369456418096220292498187500 : ℤ)),
    ((1, 3, 1, 5), (-28766895594133883363798985000 : ℤ)), ((1, 3, 2, 4), (15516012654709940272340489100 : ℤ)), ((1, 3, 3, 3), (-28305882731251617924939609375 : ℤ)), ((1, 3, 6, 0), (10273891283619244058499637500 : ℤ)),
    ((1, 5, 1, 3), (-1150675823765355334551959400 : ℤ)), ((1, 5, 2, 2), (27173647422001553207942025000 : ℤ)), ((2, 0, 0, 8), (-27678077199936927548526300000 : ℤ)), ((2, 0, 1, 7), (17151976419296598596193750000 : ℤ)),
    ((2, 0, 2, 6), (-9605106794806095213868500000 : ℤ)), ((2, 0, 3, 5), (5150166786167458671817110000 : ℤ)), ((2, 0, 4, 4), (-2625343584556959597395001600 : ℤ)), ((2, 0, 5, 3), (11447732086023283408637370000 : ℤ)),
    ((2, 0, 7, 1), (3430395283859319719238750000 : ℤ)), ((2, 0, 8, 0), (-3881247235452258882338700000 : ℤ)), ((2, 4, 0, 4), (-1030033357233491734363422000 : ℤ)), ((2, 4, 1, 3), (1464239365451305749679980516 : ℤ)),
    ((2, 4, 2, 2), (-25115410251685961376398775000 : ℤ)), ((2, 4, 4, 0), (-686079056771863943847750000 : ℤ)), ((3, 1, 3, 3), (-18115764948001035471961350000 : ℤ)), ((3, 3, 0, 4), (-342563322699885272481067753350 : ℤ)),
    ((3, 3, 1, 3), (18870588487501078616626406250 : ℤ)), ((3, 5, 0, 2), (3623152989600207094392270000 : ℤ)), ((4, 4, 0, 2), (-3415907744172892619101912500 : ℤ)), ((6, 0, 1, 3), (273970434229846508226657000 : ℤ)),
    ((8, 0, 0, 2), (3450621894857340089897400000 : ℤ))
  ]

lemma hb_d4_5 : allBound wsD4_5 = true := by decide
lemma hk_d4_5 : (126810354636007248303729450000 : ℤ) ≠ 0 := by decide
lemma hc_d4_5 : compileStrict wsD4_5 = [(packKey 4 0 1 0 3, (126810354636007248303729450000 : ℤ))] := by decide

def wsD4_6 : List (Exps × ℤ) :=
  [
    ((0, 0, 0, 10), (-2572340089661094954600920237401125000000000 : ℤ)), ((0, 0, 1, 9), (1284961021417757055064107325254750000000000 : ℤ)), ((0, 0, 2, 8), (-596394916250392521243654685059285000000000 : ℤ)), ((0, 0, 3, 7), (246457907627858424728594478105969600000000 : ℤ)),
    ((0, 0, 4, 6), (-2376441551773237238952129651344301000000000 : ℤ)), ((0, 0, 5, 5), (2333241431886841792686120115348200000000000 : ℤ)), ((0, 0, 6, 4), (-1847748836153271443883681256250625000000000 : ℤ)), ((0, 0, 7, 3), (1312848682085420807517782182908450000000000 : ℤ)),
    ((0, 0, 8, 2), (-869478230156033251401749327245257000000000 : ℤ)), ((0, 0, 9, 1), (-15036512443407434083093912658930871600000000 : ℤ)), ((0, 0, 10, 0), (8117004514449600599691809874834495000000000 : ℤ)), ((0, 2, 0, 8), (-166742071464848082638320505248537062454218750 : ℤ)),
    ((0, 2, 1, 7), (115962667603435606025876273292235447125000000 : ℤ)), ((0, 2, 2, 6), (-67688961080044349754886821338052360843750000 : ℤ)), ((0, 2, 3, 5), (37905818204824835862736619949309322072500000 : ℤ)), ((0, 2, 4, 4), (-21113398200993024027021114268807411660458750 : ℤ)),
    ((0, 2, 5, 3), (42838004788783064046904735542249975773250000 : ℤ)), ((0, 2, 6, 2), (39661429122357291073417795383067056056250000 : ℤ)), ((0, 2, 8, 0), (-13537792216008869950977364267610472168750000 : ℤ)), ((0, 4, 0, 6), (-71882969097336307487385679644890668029660000 : ℤ)),
    ((0, 4, 1, 5), (39797711050190337324678797683840786334049600 : ℤ)), ((0, 4, 2, 4), (-21067277660531822020127070259705828909018976 : ℤ)), ((0, 4, 3, 3), (-593846579749523605002636403706339092021511931 : ℤ)), ((0, 4, 4, 2), (13884166358011803536977605420227183589888000 : ℤ)),
    ((0, 4, 5, 1), (6851274664769923023857743759469816438400000 : ℤ)), ((0, 4, 6, 0), (-18291607913621503225395846648675171570732000 : ℤ)), ((0, 6, 0, 4), (14018037538253583976283615594119800165000000 : ℤ)), ((0, 6, 1, 3), (21113398200993024027021114268807411660458750 : ℤ)),
    ((0, 6, 2, 2), (-20503485168262250635692559810309302000000000 : ℤ)), ((0, 6, 3, 1), (-4100697033652450127138511962061860400000000 : ℤ)), ((0, 8, 0, 2), (46751293241709844603432756999767596660156250 : ℤ)), ((0, 8, 1, 1), (755513909261364110725632872828857500000000 : ℤ)),
    ((0, 10, 0, 0), (-1890174674911370898254936072059555200000000 : ℤ)), ((1, 1, 0, 8), (6923180765743789311869364739123882965000000 : ℤ)), ((1, 1, 1, 7), (1012969802955813573072906228723614325000000 : ℤ)), ((1, 1, 6, 2), (25834391312010435800972625360989720520000000 : ℤ)),
    ((1, 3, 0, 6), (14349675965339193831360079570542095414578125 : ℤ)), ((1, 3, 1, 5), (-7426816348165955387885400669772923082083750 : ℤ)), ((1, 3, 2, 4), (3572825979746954250241753830452030064012525 : ℤ)), ((1, 3, 3, 3), (-128397353211607530763926346991912283270234375 : ℤ)),
    ((1, 3, 4, 2), (793289604724432316261914516470300375000000 : ℤ)), ((1, 3, 6, 0), (5914946155187804554653235362761670833315625 : ℤ)), ((1, 5, 0, 4), (-11775151532133010540078237099060632138600000 : ℤ)), ((1, 5, 1, 3), (-17735254488834140182697735985798225794785350 : ℤ)),
    ((1, 5, 2, 2), (17222927541340290533981750240659813680000000 : ℤ)), ((1, 7, 0, 2), (-12960201832378557088327617936332810610000000 : ℤ)), ((1, 7, 1, 1), (-793289604724432316261914516470300375000000 : ℤ)), ((1, 9, 0, 0), (1587746726925551554534146300530026368000000 : ℤ)),
    ((2, 0, 0, 8), (52796445557901279863886298697201273145600000 : ℤ)), ((2, 0, 1, 7), (-28133541983587443189100107222462480720000000 : ℤ)), ((2, 0, 2, 6), (16528668368594357362903017019007005152000000 : ℤ)), ((2, 0, 3, 5), (-8776400707545855631566052396218850869120000 : ℤ)),
    ((2, 0, 4, 4), (4420314391958525155508965990529088599347200 : ℤ)), ((2, 0, 5, 3), (-21487012932559103020143300719553483623040000 : ℤ)), ((2, 0, 6, 2), (22837582215899743412859145864899388128000000 : ℤ)), ((2, 0, 7, 1), (-7194803683004767374894557016376080240000000 : ℤ)),
    ((2, 0, 8, 0), (7417050064007309972520350270302018310400000 : ℤ)), ((2, 2, 3, 3), (-36674632738292516907898128619747415890500000 : ℤ)), ((2, 2, 4, 2), (-23707154725803227297519522280670130437500000 : ℤ)), ((2, 4, 0, 4), (11366046677735828300453257330572305166948000 : ℤ)),
    ((2, 4, 1, 3), (13591282928209112241823882744588543714541079 : ℤ)), ((2, 4, 2, 2), (-9759786844848778431802158862037360726592000 : ℤ)), ((2, 4, 3, 1), (-4567516443179948682571829172979877625600000 : ℤ)), ((2, 4, 4, 0), (1438960736600953474978911403275216048000000 : ℤ)),
    ((2, 6, 0, 2), (17452615393046656936936353797582445265500000 : ℤ)), ((2, 6, 1, 1), (4100697033652450127138511962061860400000000 : ℤ)), ((2, 8, 0, 0), (-382400468483246151329218336408055520000000 : ℤ)), ((3, 1, 4, 2), (-17222927541340290533981750240659813680000000 : ℤ)),
    ((3, 3, 0, 4), (224517009295249904554616785552036268785574850 : ℤ)), ((3, 3, 1, 3), (-124849912112378198745303896854245791492343750 : ℤ)), ((3, 5, 0, 2), (-14660196930159191827026537189969254023020000 : ℤ)), ((3, 7, 0, 0), (180859149499286760377769222929964000000000 : ℤ)),
    ((4, 2, 0, 4), (-20769542297231367935608094217371648895000000 : ℤ)), ((4, 2, 2, 2), (13070971794767184780254006879072180025000000 : ℤ)), ((4, 4, 0, 2), (11543245149452927515423141878246376240817625 : ℤ)), ((4, 6, 0, 0), (-64069536765941666125727963588550000000000 : ℤ)),
    ((5, 3, 0, 2), (118535773629016136487597611403350652187500000 : ℤ)), ((6, 0, 0, 4), (2803607507650716795256723118823960033000000 : ℤ)), ((6, 0, 1, 3), (4222679640198604805404222853761482332091750 : ℤ)), ((6, 0, 2, 2), (-4100697033652450127138511962061860400000000 : ℤ)),
    ((6, 2, 0, 2), (7688806938098343988384709928865988250000000 : ℤ)), ((6, 4, 0, 0), (-378034934982274179650987214411911040000000 : ℤ)), ((7, 3, 0, 0), (1403572440266400067387741796528026368000000 : ℤ)), ((8, 0, 0, 2), (3490523078609331387387270759516489053100000 : ℤ)),
    ((8, 0, 1, 1), (4100697033652450127138511962061860400000000 : ℤ)), ((8, 2, 0, 0), (-878521488134592125915981836726197600000000 : ℤ)), ((9, 1, 0, 0), (538184108833909995456114894143820000000000 : ℤ)), ((10, 0, 0, 0), (-320347683829708330628639817942750000000000 : ℤ))
  ]

lemma hb_d4_6 : allBound wsD4_6 = true := by decide
lemma hk_d4_6 : (120560492789382033737872251684618695760000000 : ℤ) ≠ 0 := by decide
lemma hc_d4_6 : compileStrict wsD4_6 = [(packKey 4 0 1 1 2, (120560492789382033737872251684618695760000000 : ℤ))] := by decide

def wsD4_7 : List (Exps × ℤ) :=
  [
    ((0, 0, 0, 10), (82082671493901322481618281250000 : ℤ)), ((0, 0, 1, 9), (-58494246658853976768754687500000 : ℤ)), ((0, 0, 2, 8), (32950321684383532556777343750000 : ℤ)), ((0, 0, 3, 7), (-17782853171855947436559375000000 : ℤ)),
    ((0, 0, 4, 6), (9136587598695837295009968750000 : ℤ)), ((0, 0, 5, 5), (2987492156527972242787968750000 : ℤ)), ((0, 0, 6, 4), (-2903153331379583494120781250000 : ℤ)), ((0, 0, 7, 3), (-10039904570982461928539062500000 : ℤ)),
    ((0, 0, 8, 2), (12327152663152399041949218750000 : ℤ)), ((0, 0, 9, 1), (-10600657870458274654140000000000 : ℤ)), ((0, 0, 10, 0), (18452365855858785572392781250000 : ℤ)), ((0, 2, 0, 8), (-777573381820903373585871998906250 : ℤ)),
    ((0, 2, 1, 7), (924658835887552852214693906250000 : ℤ)), ((0, 2, 2, 6), (-517808948097029597240228587500000 : ℤ)), ((0, 2, 3, 5), (277644226455835869758332090250000 : ℤ)), ((0, 2, 4, 4), (-170369092002927296856763851806250 : ℤ)),
    ((0, 2, 7, 1), (184931767177510570442938781250000 : ℤ)), ((0, 2, 8, 0), (-209237085149411959701153592500000 : ℤ)), ((0, 4, 0, 6), (82074369420747947034709153323360000 : ℤ)), ((0, 4, 1, 5), (-43976066546273563446423502276189100 : ℤ)),
    ((0, 4, 2, 4), (22591463501250804327541263691261096 : ℤ)), ((0, 4, 3, 3), (13001426691524722509176432030399475 : ℤ)), ((0, 4, 4, 2), (1086465187684275447461765625000 : ℤ)), ((0, 4, 5, 1), (-29783704940179303395204353773387500 : ℤ)),
    ((0, 4, 6, 0), (33434133849966334204201461392322000 : ℤ)), ((0, 6, 0, 4), (-4662746289768966516101296471250000 : ℤ)), ((0, 6, 1, 3), (608879298334240361491060289906250 : ℤ)), ((0, 6, 4, 0), (-184931767177510570442938781250000 : ℤ)),
    ((0, 8, 0, 2), (-5531613781493496536503110202031250 : ℤ)), ((0, 8, 2, 0), (4761728816582072173805040847500000 : ℤ)), ((1, 3, 0, 6), (1081404907410750266456554528734375 : ℤ)), ((1, 3, 1, 5), (-605586748150020149215670536091250 : ℤ)),
    ((1, 3, 2, 4), (167197511897388907537397430792975 : ℤ)), ((1, 3, 3, 3), (1141072405838761472113750521046875 : ℤ)), ((1, 3, 6, 0), (216280981482150053291310905746875 : ℤ)), ((1, 5, 0, 4), (3898213706688180816480795157725000 : ℤ)),
    ((1, 5, 1, 3), (-511458610600761903652490643521250 : ℤ)), ((1, 5, 4, 0), (166438590459759513398644903125000 : ℤ)), ((1, 7, 0, 2), (5380382189556307535172520950000000 : ℤ)), ((1, 7, 2, 0), (-4438362412260253690630530750000000 : ℤ)),
    ((2, 0, 0, 8), (10347287501755004261540625000000 : ℤ)), ((2, 0, 1, 7), (-6035917709357085819232031250000 : ℤ)), ((2, 0, 2, 6), (3380113917239968058769937500000 : ℤ)), ((2, 0, 3, 5), (12982156483337891333447031250000 : ℤ)),
    ((2, 0, 4, 4), (-12292577552084945062710262500000 : ℤ)), ((2, 0, 5, 3), (3621550625614251491539218750000 : ℤ)), ((2, 0, 7, 1), (-1207183541871417163846406250000 : ℤ)), ((2, 0, 8, 0), (75338548821235888739698875000000 : ℤ)),
    ((2, 2, 2, 4), (-292340137554208709756197625400000 : ℤ)), ((2, 4, 0, 4), (-3177676626880109781440433449939000 : ℤ)), ((2, 4, 1, 3), (419906162448372180850812987259725 : ℤ)), ((2, 4, 2, 2), (-724310125122850298307843750000 : ℤ)),
    ((2, 4, 4, 0), (-139566979277823707822092437375000 : ℤ)), ((2, 6, 0, 2), (-4707834415861769093275955831250000 : ℤ)), ((2, 6, 2, 0), (3883567110727721979301714406250000 : ℤ)), ((3, 1, 0, 6), (-317025886590018120759323625000000 : ℤ)),
    ((3, 1, 1, 5), (184931767177510570442938781250000 : ℤ)), ((3, 1, 5, 1), (-110959060306506342265763268750000 : ℤ)), ((3, 3, 0, 4), (2181380534093013159817050670992150 : ℤ)), ((3, 3, 1, 3), (-9620410942695227389326584845031250 : ℤ)),
    ((3, 5, 0, 2), (3954580909323886038351802898250000 : ℤ)), ((3, 5, 2, 0), (-3240004560949985194160287447500000 : ℤ)), ((4, 2, 0, 4), (1754040825325252258537185752400000 : ℤ)), ((4, 4, 0, 2), (-3239868861481513697579816523703125 : ℤ)),
    ((4, 4, 2, 0), (2641818983072833002703545010275000 : ℤ)), ((5, 3, 2, 0), (4385102063313130646342964381000000 : ℤ)), ((6, 0, 0, 4), (-994193180346296826701238888000000 : ℤ)), ((6, 0, 1, 3), (121775859666848072298212057981250 : ℤ)),
    ((6, 2, 0, 2), (1883133766344707637310382332500000 : ℤ)), ((6, 2, 2, 0), (-1553426844291088791720685762500000 : ℤ)), ((8, 0, 0, 2), (-941566883172353818655191166250000 : ℤ)), ((8, 0, 2, 0), (797848481251545603910964456250000 : ℤ))
  ]

lemma hb_d4_7 : allBound wsD4_7 = true := by decide
lemma hk_d4_7 : (776713422145544395860342881250000 : ℤ) ≠ 0 := by decide
lemma hc_d4_7 : compileStrict wsD4_7 = [(packKey 4 0 1 2 1, (776713422145544395860342881250000 : ℤ))] := by decide

def wsD4_8 : List (Exps × ℤ) :=
  [
    ((0, 0, 0, 10), (2976735741227451442520211875000000 : ℤ)), ((0, 0, 1, 9), (-2002976481897599563934135156250000 : ℤ)), ((0, 0, 2, 8), (1109595779395933725071367187500000 : ℤ)), ((0, 0, 3, 7), (-587769540245913731436035156250000 : ℤ)),
    ((0, 0, 4, 6), (295153991451017818258125000000000 : ℤ)), ((0, 0, 5, 5), (-138022478816894630560038281250000 : ℤ)), ((0, 0, 6, 4), (181065757000830460976227500000000 : ℤ)), ((0, 0, 7, 3), (-504061443237137319058957031250000 : ℤ)),
    ((0, 0, 8, 2), (509954266300408070190820312500000 : ℤ)), ((0, 0, 9, 1), (-408956345935130214967675781250000 : ℤ)), ((0, 0, 10, 0), (292720138824563686490296875000000 : ℤ)), ((0, 2, 0, 8), (11652588391031916045766805859375000 : ℤ)),
    ((0, 2, 4, 4), (-424075416483525149975934834918750 : ℤ)), ((0, 4, 0, 6), (2220274350273228181896455154358605000 : ℤ)), ((0, 4, 1, 5), (-1190028436088594467667648732334066300 : ℤ)), ((0, 4, 2, 4), (612171252067591947479598678645115728 : ℤ)),
    ((0, 4, 3, 3), (189716818931057649773941862707846875 : ℤ)), ((0, 4, 4, 2), (-20269872904557377751152343750000 : ℤ)), ((0, 4, 5, 1), (-799878000966199712915492311601287500 : ℤ)), ((0, 4, 6, 0), (901128013463902615188143780358171000 : ℤ)),
    ((0, 6, 0, 4), (-117562498173585359709099473643000000 : ℤ)), ((0, 6, 1, 3), (12180325233842061120885882199218750 : ℤ)), ((0, 8, 0, 2), (-82700354046473477037365225390625000 : ℤ)), ((0, 8, 2, 0), (127659682082652696850106571292500000 : ℤ)),
    ((1, 3, 0, 6), (15902828118132193124097556309453125 : ℤ)), ((1, 3, 1, 5), (-8905583746154028149494631533293750 : ℤ)), ((1, 3, 2, 4), (16867736978268081152729839300125 : ℤ)), ((1, 3, 3, 3), (24470435621167023696110292304687500 : ℤ)),
    ((1, 3, 6, 0), (3180565623626438624819511261890625 : ℤ)), ((1, 5, 0, 4), (98234689517714672558403329272620000 : ℤ)), ((1, 5, 1, 3), (-10231473196427331341544141047343750 : ℤ)), ((1, 7, 0, 2), (79256471647504530189830906250000000 : ℤ)),
    ((1, 7, 2, 0), (-118990382766786801324999467250000000 : ℤ)), ((2, 0, 0, 8), (-193046408614832169058593750000000 : ℤ)), ((2, 0, 1, 7), (112610405025318765284179687500000 : ℤ)), ((2, 0, 2, 6), (-63061826814178508559140625000000 : ℤ)),
    ((2, 0, 3, 5), (33813150948935714589329687500000 : ℤ)), ((2, 0, 4, 4), (229339133434420616841609375000000 : ℤ)), ((2, 0, 5, 3), (-67566243015191259170507812500000 : ℤ)), ((2, 0, 7, 1), (22522081005063753056835937500000 : ℤ)),
    ((2, 0, 8, 0), (-25482125937157846315734375000000 : ℤ)), ((2, 2, 2, 4), (-7837499878239023980606631576200000 : ℤ)), ((2, 4, 0, 4), (-80000048878899395032047930191140800 : ℤ)), ((2, 4, 1, 3), (8304963153635232981111038960784375 : ℤ)),
    ((2, 4, 2, 2), (13513248603038251834101562500000 : ℤ)), ((2, 4, 4, 0), (-4504416201012750611367187500000 : ℤ)), ((2, 6, 0, 2), (-69349412691566463916102042968750000 : ℤ)), ((2, 6, 2, 0), (104116584920938451159374533843750000 : ℤ)),
    ((3, 1, 0, 6), (-9246588358875528522146939062500000 : ℤ)), ((3, 1, 1, 5), (5178089480970295972402285875000000 : ℤ)), ((3, 1, 6, 0), (-1849317671775105704429387812500000 : ℤ)), ((3, 3, 0, 4), (-32938594512547730874337122439332000 : ℤ)),
    ((3, 3, 1, 3), (-146822613727002142176661753828125000 : ℤ)), ((3, 5, 0, 2), (58253506660915829689525716093750000 : ℤ)), ((3, 5, 2, 0), (-87457931333588298973874608428750000 : ℤ)), ((4, 2, 0, 4), (47024999269434143883639789457200000 : ℤ)),
    ((4, 4, 0, 2), (-47789563846014808883297278303359375 : ℤ)), ((4, 4, 2, 0), (71382330621795402114867180403275000 : ℤ)), ((5, 3, 2, 0), (117562498173585359709099473643000000 : ℤ)), ((6, 0, 0, 4), (-25238529461707170599287323353600000 : ℤ)),
    ((6, 0, 1, 3), (2436065046768412224177176439843750 : ℤ)), ((6, 2, 0, 2), (27739765076626585566440817187500000 : ℤ)), ((6, 2, 2, 0), (-41646633968375380463749813537500000 : ℤ)), ((8, 0, 0, 2), (-13869882538313292783220408593750000 : ℤ)),
    ((8, 0, 2, 0), (20823316984187690231874906768750000 : ℤ))
  ]

lemma hb_d4_8 : allBound wsD4_8 = true := by decide
lemma hk_d4_8 : (12945223702425739931005714687500000 : ℤ) ≠ 0 := by decide
lemma hc_d4_8 : compileStrict wsD4_8 = [(packKey 4 0 1 3 0, (12945223702425739931005714687500000 : ℤ))] := by decide

def wsD4_9 : List (Exps × ℤ) :=
  [
    ((0, 1, 0, 9), (-2962137890313685077294924964451789752829270778874074106546875 : ℤ)), ((0, 1, 1, 8), (1502001396495386990024756297562095274231047371732488419062500 : ℤ)), ((0, 1, 2, 7), (-852647467254012912331506063926499504633570347968924458984375 : ℤ)), ((0, 1, 3, 6), (600938716697600357378319836814372672306418998965493164062500 : ℤ)),
    ((0, 1, 4, 5), (-341427152682205893772775182576172605953507814690793532421875 : ℤ)), ((0, 1, 5, 4), (253653126099445659843581592951993210370735084704818247656250 : ℤ)), ((0, 1, 6, 3), (-1448925240942483155499706578033636269765965364569921950984375 : ℤ)), ((0, 1, 7, 2), (-142139878084441393450059553546434090861505754846958728906250 : ℤ)),
    ((0, 1, 8, 1), (73522069973245404613741109401858641928697629051760408203125 : ℤ)), ((0, 1, 9, 0), (78175131926236983124954761990383881930599440334949828125000 : ℤ)), ((0, 3, 0, 7), (-1039767912450365688405591338563467193342193431043697986531250 : ℤ)), ((0, 3, 1, 6), (621747110789802050028361614819584192223033208455841616390625 : ℤ)),
    ((0, 3, 2, 5), (-465395561271177001345446873248197711858863363042381513019875 : ℤ)), ((0, 3, 3, 4), (271157797392027451362171107716029853447105089424498483207755 : ℤ)), ((0, 3, 4, 3), (-13397962665404735518700057323349118350747850576774658889520843 : ℤ)), ((0, 3, 5, 2), (946408689912565139861331747878873314825597051256409453515625 : ℤ)),
    ((0, 3, 7, 0), (-43103691026165094750848204106412539003914453033274830780625 : ℤ)), ((0, 5, 0, 5), (-5130082833182427982269110849431202337920172513080973288281250 : ℤ)), ((0, 5, 1, 4), (3050406024069599629099063564881767825876164034017090261359375 : ℤ)), ((0, 5, 2, 3), (-25102615793349370108381735757850361126131275361237098698440000 : ℤ)),
    ((0, 5, 3, 2), (1448925240942483155499706578033636269765965364569921950984375 : ℤ)), ((0, 5, 4, 1), (142139878084441393450059553546434090861505754846958728906250 : ℤ)), ((0, 5, 5, 0), (-73522069973245404613741109401858641928697629051760408203125 : ℤ)), ((0, 7, 0, 3), (102339194053644070272890212651722823589110142474629160945250000 : ℤ)),
    ((0, 7, 1, 2), (-2877146791343061278136334350941379637022642912843731675781250 : ℤ)), ((0, 7, 2, 1), (-2849503579076425839400145102810933591354647177827455460937500 : ℤ)), ((0, 9, 0, 1), (1391896907596893209622482274689119342556980839028472004093750 : ℤ)), ((0, 9, 1, 0), (4796299039104799787711293920701219379137760977897551168715625 : ℤ)),
    ((1, 0, 0, 9), (3901541916455176460384638137977398746946372688267774282887500 : ℤ)), ((1, 0, 1, 8), (-2305183564098396622333605069401581942781724782615905632281250 : ℤ)), ((1, 0, 2, 7), (1275041872129355080237407109246503428767201636650935175000000 : ℤ)), ((1, 0, 3, 6), (-674224282528795254766931306185040374668411305167375253906250 : ℤ)),
    ((1, 0, 4, 5), (337822659427556651980973241439573109559573388296204276562500 : ℤ)), ((1, 0, 5, 4), (-248664895973168449132204884876091515897471784440296995406250 : ℤ)), ((1, 0, 6, 3), (237913856486205424041175944275736887858463624209579686162500 : ℤ)), ((1, 0, 7, 2), (-596987487954653852490250124895023181618324170357226661406250 : ℤ)),
    ((1, 0, 8, 1), (596144081828530360327624350360742503821054138962887984375000 : ℤ)), ((1, 0, 9, 0), (-475498617550633542569171604300289505688570340440839613281250 : ℤ)), ((1, 2, 0, 7), (4229099753697468221197363010960133947842333614602324460937500 : ℤ)), ((1, 2, 1, 6), (-2537459852218480932718417806576080368705400168761394676562500 : ℤ)),
    ((1, 2, 2, 5), (1420977517242349322322313971682605006475024094506381018875000 : ℤ)), ((1, 2, 3, 4), (1074604499707191274460728688256170297889465660453927482850000 : ℤ)), ((1, 2, 4, 3), (2343679515798084023802301673582049422559615886479987584765625 : ℤ)), ((1, 2, 7, 0), (-507491970443696186543683561315216073741080033752278935312500 : ℤ)),
    ((1, 4, 0, 5), (4469366188810459679304969942338975866451720027164589448093750 : ℤ)), ((1, 4, 1, 4), (-2633794181064014150048671325677357353747007421850829493323125 : ℤ)), ((1, 4, 2, 3), (20580957317683564156799023686433066541312975646759124750455225 : ℤ)), ((1, 4, 3, 2), (-1264679973688926935427988714403401844175103631080650376059375 : ℤ)),
    ((1, 4, 5, 0), (-57470277588179932189982338174587241544104819389098853984375 : ℤ)), ((1, 6, 0, 3), (-89723773680460190100778265279487635315292556340415429699056250 : ℤ)), ((1, 6, 1, 2), (2254620752809028861208086391049806041526147780633645996093750 : ℤ)), ((1, 6, 2, 1), (2564553221168783255460130592529840232219182460044709914843750 : ℤ)),
    ((1, 8, 0, 1), (-1015336913663737885314906238114909070338196869051219422187500 : ℤ)), ((1, 8, 1, 0), (-4043731976515937376167610811172895590242142165406259480875000 : ℤ)), ((2, 1, 0, 7), (-5699007158152851678800290205621867182709294355654910921875000 : ℤ)), ((2, 1, 1, 6), (3419404294891711007280174123373120309625576613392946553125000 : ℤ)),
    ((2, 1, 2, 5), (-1914866405139358164076897509088947373390322903500050069750000 : ℤ)), ((2, 1, 3, 4), (1026733129612817758452660283444835591636906471114788751685000 : ℤ)), ((2, 1, 7, 0), (683880858978342201456034824674624061925115322678589310625000 : ℤ)), ((2, 3, 0, 5), (35050385961133234533137626706048791702168607184461021177148750 : ℤ)),
    ((2, 3, 1, 4), (-18602633259117663613625099727471966315211700310742264855265175 : ℤ)), ((2, 3, 2, 3), (10850072971165197864557594449526998658513662326412260376868062 : ℤ)), ((2, 3, 3, 2), (1268729926109240466359208903288040184352700084380697338281250 : ℤ)), ((2, 3, 5, 0), (-13773893334999953618937342062330610224495553633455116932993750 : ℤ)),
    ((2, 5, 0, 3), (75162623265663996132963210778080646546518366031726003196870250 : ℤ)), ((2, 5, 1, 2), (-1893881432359584243414792568481837074881964135732262636718750 : ℤ)), ((2, 5, 2, 1), (-2154224705781777934586509697725065795064113266437556328468750 : ℤ)), ((2, 7, 0, 1), (580236443754485297631283937962073366900854992582114023437500 : ℤ)),
    ((2, 7, 1, 0), (3267426049005491769460365024222980599153612750829234151562500 : ℤ)), ((3, 2, 0, 5), (-63001928337354775871318404656140717708967868482569411812500 : ℤ)), ((3, 2, 1, 4), (-50924794309678409859013731500728995849502439057777004300000 : ℤ)), ((3, 2, 2, 3), (-3065533512404741923340258709754570309390509111409089053906250 : ℤ)),
    ((3, 2, 3, 2), (-1709702147445855503640087061686560154812788306696473276562500 : ℤ)), ((3, 4, 0, 3), (-61326459836992157456912268168344941758647035934104199505064635 : ℤ)), ((3, 4, 1, 2), (990795060201329763176188702567291914253536904834330139606250 : ℤ)), ((3, 4, 2, 1), (1758257688433317799943465534238458463209471494606653117616875 : ℤ)),
    ((3, 6, 0, 1), (-90184830112361154448323455641992241661045911225345839843750 : ℤ)), ((3, 6, 1, 0), (-2589872492338353980811681228602559107684313771324417890625000 : ℤ)), ((4, 1, 0, 5), (184244510507451316113125466362791185243715404014450948437500 : ℤ)), ((4, 3, 0, 3), (-89506134667074011969949164097952640907407054234680473567848997 : ℤ)),
    ((4, 5, 1, 0), (2021707007540530876758304707687550269554767918968989889843750 : ℤ)), ((5, 0, 0, 5), (-252517524314611232455305675797578276650928551430968351562500 : ℤ)), ((5, 0, 1, 4), (38885889600391312092632828887577580991149556172328184687500 : ℤ)), ((5, 0, 2, 3), (5549729279245404240680753271364551078167900135680975553156250 : ℤ)),
    ((5, 2, 0, 3), (35490222548887006576442422875393023404470937735419267089062500 : ℤ)), ((5, 4, 1, 0), (-1609849851754262255042226356399745345545242054883488126078125 : ℤ)), ((6, 3, 0, 1), (189005785012064327613955213968422153126903605447708235437500 : ℤ)), ((6, 3, 1, 0), (1293088112678956265204280571622516966497866681120238123725000 : ℤ)),
    ((7, 0, 0, 3), (-18140322951256384259860921681315590985275064881628759987751250 : ℤ)), ((7, 0, 1, 2), (450924150561805772241617278209961208305229556126729199218750 : ℤ)), ((7, 0, 2, 1), (512910644233756651092026118505968046443836492008941982968750 : ℤ)), ((7, 2, 0, 1), (-552733531522353948339376399088373555731146212043352845312500 : ℤ)),
    ((7, 2, 1, 0), (-1547653888262591055350253917447445956047209393721387966875000 : ℤ)), ((8, 1, 0, 1), (757552572943833697365917027392734829952785654292905054687500 : ℤ)), ((8, 1, 1, 0), (1537858860236864671235075243385993809000556489435211382812500 : ℤ)), ((9, 0, 0, 1), (-450924150561805772241617278209961208305229556126729199218750 : ℤ)),
    ((9, 0, 1, 0), (-1396750990031593465439522099083936855251466462513575796875000 : ℤ))
  ]

lemma hb_d4_9 : allBound wsD4_9 = true := by decide
lemma hk_d4_9 : (11967915032120988525480609431805921083689518146875312935937500 : ℤ) ≠ 0 := by decide
lemma hc_d4_9 : compileStrict wsD4_9 = [(packKey 4 0 2 0 2, (11967915032120988525480609431805921083689518146875312935937500 : ℤ))] := by decide

def wsD4_10 : List (Exps × ℤ) :=
  [
    ((0, 1, 0, 9), (-1726008328874060813522373163866133075326961983096600697738265625 : ℤ)), ((0, 1, 1, 8), (1063418909837500681190759028706349627065175520421749867895312500 : ℤ)), ((0, 1, 2, 7), (-628416126123493824939047170162003400777718279641488872275390625 : ℤ)), ((0, 1, 3, 6), (352244410128665963095937083670372631081411507490792810898437500 : ℤ)),
    ((0, 1, 4, 5), (-232151841820047297195831856662788454427487477733075654236953125 : ℤ)), ((0, 1, 5, 4), (210561714555451448438075866349619791069035008412677925937906250 : ℤ)), ((0, 1, 6, 3), (17741713532659709814133350814375452698572556973081467310234375 : ℤ)), ((0, 1, 7, 2), (-4970692492641316951060025694760899688339063373385636363281250 : ℤ)),
    ((0, 1, 8, 1), (-122842829514618012444346562206823023190778476857791696533203125 : ℤ)), ((0, 1, 9, 0), (-151714282607726377106498006696142675576259655028200255807812500 : ℤ)), ((0, 3, 0, 7), (626441978480206122612991998343814124667747128090245004933281250 : ℤ)), ((0, 3, 1, 6), (-357230436924407115302861890591876680322857186346309610047500000 : ℤ)),
    ((0, 3, 2, 5), (194919938235330418058682397546391260516361659433843961796912500 : ℤ)), ((0, 3, 3, 4), (-87426484916516539842591724671961322047298558590437924602252250 : ℤ)), ((0, 3, 4, 3), (813585547836901567818676073630089994714855476155788535926542386 : ℤ)), ((0, 3, 5, 2), (75322794738407193141630486060807932338367430577103247581250000 : ℤ)),
    ((0, 3, 6, 1), (76936596635063497663803917775895206966575473801341297445312500 : ℤ)), ((0, 3, 7, 0), (-115409856890631993154174616847458311474043136584314091978250000 : ℤ)), ((0, 5, 0, 5), (-352676621562623281635546513468234166216455300010997559433593750 : ℤ)), ((0, 5, 1, 4), (182295191081078497717093611099305568448046036433851923550390625 : ℤ)),
    ((0, 5, 2, 3), (1079915989831382321263265050913742648988263140345192429098087500 : ℤ)), ((0, 5, 3, 2), (-17741713532659709814133350814375452698572556973081467310234375 : ℤ)), ((0, 5, 4, 1), (4970692492641316951060025694760899688339063373385636363281250 : ℤ)), ((0, 5, 5, 0), (122842829514618012444346562206823023190778476857791696533203125 : ℤ)),
    ((0, 7, 0, 3), (2374371258385918813700989913386396858629452782517977183126500000 : ℤ)), ((0, 7, 1, 2), (-18050328597232504471681668105498492897247961422975157753906250 : ℤ)), ((0, 7, 3, 0), (-76936596635063497663803917775895206966575473801341297445312500 : ℤ)), ((0, 9, 0, 1), (-23102266976306892178957765083539617563065836186267269262031250 : ℤ)),
    ((0, 9, 1, 0), (-94614766480592635136592412600563991525661943085479989062500000 : ℤ)), ((1, 0, 0, 9), (-4270597389501400435768953438434360694255966759128340892312500 : ℤ)), ((1, 0, 1, 8), (9270357715434956896213793665501483706014861540654844079843750 : ℤ)), ((1, 0, 2, 7), (-7843347988731303495477458895308706342461476951674287531250000 : ℤ)),
    ((1, 0, 3, 6), (5784068771629098703764184175905927464513364837485579199218750 : ℤ)), ((1, 0, 4, 5), (-3929811337751821939671181131064947245695581422711302335937500 : ℤ)), ((1, 0, 5, 4), (-26204718173110391586856416234297941348181821612442584898281250 : ℤ)), ((1, 0, 6, 3), (39779215021315914503966016639418132006397317333613622698062500 : ℤ)),
    ((1, 0, 7, 2), (-20876908469093531194452107917995778691024066168219672725781250 : ℤ)), ((1, 0, 8, 1), (10360992384592899983448569888364417983521456705790669765625000 : ℤ)), ((1, 0, 9, 0), (-4763753322584408821217774529598481926252445150097552597656250 : ℤ)), ((1, 2, 0, 7), (2256118805696928636095088996472236947584088690126465874902343750 : ℤ)),
    ((1, 2, 1, 6), (-1256731171657977174600660461485714207772568117086189490160312500 : ℤ)), ((1, 2, 2, 5), (671456085541740548757572212966123969426676446571702769562743750 : ℤ)), ((1, 2, 3, 4), (-682180074097062503872462461059638818727130981293760868853818750 : ℤ)), ((1, 2, 4, 3), (340628072990157011466545152941946451150653230072236474806640625 : ℤ)),
    ((1, 2, 6, 1), (484700558800900035281964681988139803889425484948450173905468750 : ℤ)), ((1, 2, 7, 0), (-528317982217824026509826196290365586634185329102066568835187500 : ℤ)), ((1, 4, 0, 5), (294728490753753589259834313447931824615482993324768845314843750 : ℤ)), ((1, 4, 1, 4), (-151990329420686894204927800778911566907398555350990903906390625 : ℤ)),
    ((1, 4, 2, 3), (-872537428722027592471047015297723982672181342300393508095284125 : ℤ)), ((1, 4, 3, 2), (6947196363170973343078811356191753865521484390665708000984375 : ℤ)), ((1, 4, 5, 0), (-105260175269197710449940826231404223076958211901703159041015625 : ℤ)), ((1, 6, 0, 3), (-1951419203263929968636014022438571251227669138065104959357612500 : ℤ)),
    ((1, 6, 1, 2), (-32415857546798890470707234839615135128284439015356140136718750 : ℤ)), ((1, 8, 0, 1), (17303790270700978785108013997242916223433853530516220010937500 : ℤ)), ((1, 8, 1, 0), (71948913644459149613965998619600488785303070665235969140625000 : ℤ)), ((2, 1, 2, 5), (43084494115635558691730193954501315901282265328751126569375000 : ℤ)),
    ((2, 1, 3, 4), (-38488814743301099097945639932687842205145490360351006401975000 : ℤ)), ((2, 1, 7, 0), (215422470578177793458650969772506579506411326643755632846875000 : ℤ)), ((2, 3, 0, 5), (-7169103165172397365046419132577309134099895056228646872241589750 : ℤ)), ((2, 3, 1, 4), (3838986513192945382657708411491060721553203660560124889430192885 : ℤ)),
    ((2, 3, 2, 3), (-530356812826446042231329603683061001211738343155208918781757424 : ℤ)), ((2, 3, 3, 2), (-50215196492271462094420324040538621558911620384735498387500000 : ℤ)), ((2, 3, 5, 0), (2560393987561570487516578261634753262178533948653088168657710625 : ℤ)), ((2, 5, 0, 3), (1646889893690361393473840906834937419472271174046758367140789500 : ℤ)),
    ((2, 5, 1, 2), (27229320339311067995394077265276713507758928772899157714843750 : ℤ)), ((2, 7, 0, 1), (-3660213400712834718292428345318828972199431513962499023437500 : ℤ)), ((2, 7, 1, 0), (-54243369160740310743987231751382694122711076767621630484375000 : ℤ)), ((3, 2, 0, 5), (541329280206183467121008219778791436578370587858469169144687500 : ℤ)),
    ((3, 2, 1, 4), (-299015251381725824966601798350068726845925194139958345658525000 : ℤ)), ((3, 2, 2, 3), (-205474810295572080663891945401554210681579194037920223113281250 : ℤ)), ((3, 2, 4, 1), (-323133705867266690187976454658759869259616989965633449270312500 : ℤ)), ((3, 4, 0, 3), (-1344740578095581074495770354306335083186717128094983925543350930 : ℤ)),
    ((3, 4, 1, 2), (7126747167626159766007464016920117564371519878151445689718750 : ℤ)), ((3, 6, 0, 1), (1296634301871955618828289393584605405131377560614245605468750 : ℤ)), ((3, 6, 1, 0), (105212925395240087537839984436760446306755496726808949453125000 : ℤ)), ((4, 1, 0, 5), (-5926483182422751815124501388277369771720483037047511914062500 : ℤ)),
    ((4, 3, 0, 3), (-5289355905082894712230015132028077091235102161809326486049689831 : ℤ)), ((4, 5, 1, 0), (-90604205752029026258750395047549600082120601761491583007812500 : ℤ)), ((5, 0, 0, 5), (3630576045241475732719210302036895134367857169719887695312500 : ℤ)), ((5, 0, 1, 4), (-3516688198686794894965963182921211398209989689024514087500000 : ℤ)),
    ((5, 0, 2, 3), (-293510591017114790727243442229602542083233312670796153674531250 : ℤ)), ((5, 2, 0, 3), (1232848861773432483983351672409325264089475164227521338679687500 : ℤ)), ((5, 4, 1, 0), (75274901992386639007716279648732640962529615265672216718750000 : ℤ)), ((6, 3, 0, 1), (-8319311282216950423142386042574963437026813747240261082500000 : ℤ)),
    ((6, 3, 1, 0), (-61937183006053749317442070890817164569435025911765835937500000 : ℤ)), ((7, 0, 0, 3), (-382952637844538165327594111167202280301696591353906514461622500 : ℤ)), ((7, 0, 1, 2), (-6483171509359778094141446967923027025656887803071228027343750 : ℤ)), ((7, 2, 0, 1), (17779449547268255445373504164832109315161449111142535742187500 : ℤ)),
    ((7, 2, 1, 0), (49782458732351115247045811661529906082452057511199100078125000 : ℤ)), ((8, 1, 0, 1), (-10891728135724427198157630906110685403103571509159663085937500 : ℤ)), ((8, 1, 1, 0), (22253484200273527269648081206708251844459845109720654671875000 : ℤ)), ((9, 0, 0, 1), (6483171509359778094141446967923027025656887803071228027343750 : ℤ)),
    ((9, 0, 1, 0), (8326308393177430496340521912090231064516902139807130078125000 : ℤ))
  ]

lemma hb_d4_10 : allBound wsD4_10 = true := by decide
lemma hk_d4_10 : (2261935941070866831315835182611319084817318929759434144892187500 : ℤ) ≠ 0 := by decide
lemma hc_d4_10 : compileStrict wsD4_10 = [(packKey 4 0 2 1 1, (2261935941070866831315835182611319084817318929759434144892187500 : ℤ))] := by decide

def wsD4_11 : List (Exps × ℤ) :=
  [
    ((0, 1, 0, 9), (-164460185075457035922212647975934719709720143339869291000000 : ℤ)), ((0, 1, 1, 8), (109988271552402315708227598124562629336988895530276306250000 : ℤ)), ((0, 1, 2, 7), (-64592689682366815760454757832798415728141916542935546875000 : ℤ)), ((0, 1, 3, 6), (36066375069901190911847358873226417125819812193880734375000 : ℤ)),
    ((0, 1, 4, 5), (-19275630661156408844871901999917655276785015329812258125000 : ℤ)), ((0, 1, 5, 4), (19668432720857932565452037700293513691380207251528424812500 : ℤ)), ((0, 1, 6, 3), (-535918449282223985740179557762850927590373068258188125000 : ℤ)), ((0, 1, 7, 2), (1582967283363388710109582697110435229094916052447578125000 : ℤ)),
    ((0, 1, 8, 1), (-13823090669823870986439284536337074705111192481414296875000 : ℤ)), ((0, 1, 9, 0), (15112183968165307317477634366837897542370358142441459375000 : ℤ)), ((0, 3, 0, 7), (-2105410779184007185027476528600258859833484666147239375000 : ℤ)), ((0, 3, 1, 6), (1112385622500130873534438978774894902932571399369658293750 : ℤ)),
    ((0, 3, 2, 5), (-622935948600073289179285828113941145642239983647008644500 : ℤ)), ((0, 3, 3, 4), (1793215469072764137292945237513810876518719149235516063670 : ℤ)), ((0, 3, 4, 3), (-59794068583410459642062471463294715255390685201040949796439 : ℤ)), ((0, 3, 5, 2), (-3145272890284802231862676203104463543450638302695556406250 : ℤ)),
    ((0, 3, 7, 0), (222477124500026174706887795754978980586514279873931658750 : ℤ)), ((0, 5, 0, 5), (-36059297699668930456705053637107551497673607359896359375000 : ℤ)), ((0, 5, 1, 4), (19344954473172328744003558257026954764337678709304445625000 : ℤ)), ((0, 5, 2, 3), (-63304380332657803850448611192683580388272512093045070025000 : ℤ)),
    ((0, 5, 3, 2), (535918449282223985740179557762850927590373068258188125000 : ℤ)), ((0, 5, 4, 1), (-1582967283363388710109582697110435229094916052447578125000 : ℤ)), ((0, 5, 5, 0), (13823090669823870986439284536337074705111192481414296875000 : ℤ)), ((0, 7, 0, 3), (87403484474452788165285718152083574014711442378923062500 : ℤ)),
    ((0, 7, 1, 2), (-6051525037952422595259363082447883515317383838839484375000 : ℤ)), ((0, 9, 0, 1), (132893037666389025207665255469950932225983743265249375000 : ℤ)), ((0, 9, 1, 0), (2183839788895143401457620883183163081176455835796875000000 : ℤ)), ((1, 0, 0, 9), (140760162564441533415740180366145306510890060984968125000 : ℤ)),
    ((1, 0, 1, 8), (-2632524462166664400985095616243709128634592601918096875000 : ℤ)), ((1, 0, 2, 7), (2311293238445281368528334631059610253960021216818203125000 : ℤ)), ((1, 0, 3, 6), (-1737555052871106405206550548584303606364188376103515625000 : ℤ)), ((1, 0, 4, 5), (1195488351766691362286157076997418186166331776118671875000 : ℤ)),
    ((1, 0, 5, 4), (-773424660375182949117773252827072898036320207993096875000 : ℤ)), ((1, 0, 6, 3), (-12556193094479239559650216289446997128869740396161033125000 : ℤ)), ((1, 0, 7, 2), (6648462590126232582460247327863827962198647420279828125000 : ℤ)), ((1, 0, 8, 1), (-3336862832383076630557331546853122499035794282510546875000 : ℤ)),
    ((1, 0, 9, 0), (1559267750787536793562879345627780706747616200499609375000 : ℤ)), ((1, 2, 0, 7), (6989495311744004959694836006898807874334751783767903125000 : ℤ)), ((1, 2, 1, 6), (-4193697187046402975816901604139284724600851070260741875000 : ℤ)), ((1, 2, 2, 5), (2348470424745985666457464898317999445776476599346015450000 : ℤ)),
    ((1, 2, 3, 4), (-33944577978618090507361427004766550122886038231082822100000 : ℤ)), ((1, 2, 4, 3), (34408988367163523400423738457017211369741980342891876562500 : ℤ)), ((1, 2, 7, 0), (-838739437409280595163380320827856944920170214052148375000 : ℤ)), ((1, 4, 0, 5), (30643266069291221646993091563227051106961479918080520000000 : ℤ)),
    ((1, 4, 1, 4), (-16487208860865334419821847583275713746716138771527749950000 : ℤ)), ((1, 4, 2, 3), (52989250889095699176043362314173556635345590740276751246000 : ℤ)), ((1, 4, 3, 2), (2061067121498779763908292429368604646598034701895328600000 : ℤ)), ((1, 4, 5, 0), (-10944023596175436302497532701152518252486242827885900000000 : ℤ)),
    ((1, 6, 0, 3), (14753359756513593287730484187467527224001148846790801418750 : ℤ)), ((1, 6, 1, 2), (530802767419534135672892708914922110965362548828125000000 : ℤ)), ((1, 8, 0, 1), (-526124061432616729482128250767080225276160195121558750000 : ℤ)), ((1, 8, 1, 0), (-1769599795926569704746872220825637565832002128125000000000 : ℤ)),
    ((2, 1, 3, 4), (19539453113666920041600994990703544626431866362245408875000 : ℤ)), ((2, 3, 0, 5), (-686392360568340102050278912345036878821163676344103130133000 : ℤ)), ((2, 3, 1, 4), (368080263751140212362896474452370967973299527927134404537980 : ℤ)), ((2, 3, 2, 3), (43897062414241921491547889697161732513805379359920289447626 : ℤ)),
    ((2, 3, 3, 2), (2096848593523201487908450802069642362300425535130370937500 : ℤ)), ((2, 3, 5, 0), (245140128774407179303671040123227456721844170122893975047500 : ℤ)), ((2, 5, 0, 3), (-16300712818204802370013805715613431793447338303753354966750 : ℤ)), ((2, 5, 1, 2), (-445874324632408673965229875488534573210904541015625000000 : ℤ)),
    ((2, 7, 0, 1), (59935215338342825833693485303764919501003222656250000000 : ℤ)), ((2, 7, 1, 0), (1405743817517358111113917778659461195186083657226562500000 : ℤ)), ((3, 2, 0, 5), (410453051128470604442455547855018923830832906159754302500000 : ℤ)), ((3, 2, 1, 4), (-220137795415817385427556912561348207938792359688605329962500 : ℤ)),
    ((3, 2, 2, 3), (-23293194089722038357397754110621422320471561927813334375000 : ℤ)), ((3, 2, 5, 0), (-146545898352501900312007462430276584698238997716840566562500 : ℤ)), ((3, 4, 0, 3), (13771362198422463456781093123310506809365697304628633443695 : ℤ)), ((3, 4, 1, 2), (22804854930939955260309502986005128867269103996835550000 : ℤ)),
    ((3, 6, 0, 1), (-21232110696781365426915708356596884438614501953125000000 : ℤ)), ((3, 6, 1, 0), (-1099307090189786310170207840037963589718071297851562500000 : ℤ)), ((4, 1, 0, 5), (97044900624755360911289397661885493140760683593750000000 : ℤ)), ((4, 3, 0, 3), (-456395802256501160830490538488752875554546433225284828873256 : ℤ)),
    ((4, 5, 1, 0), (848721527109190765083277319180995154751893088925781250000 : ℤ)), ((5, 0, 0, 5), (-59449909950987823195363983398471276428120605468750000000 : ℤ)), ((5, 0, 1, 4), (-16505669527599975983727680264118925607776995117187500000 : ℤ)), ((5, 0, 2, 3), (3411135224118926481570257382460654704105834594797269500000 : ℤ)),
    ((5, 2, 0, 3), (139759164538332230144386524663728533922829371566880006250000 : ℤ)), ((5, 4, 1, 0), (-648256267453507524775293210482194223562207739443750000000 : ℤ)), ((6, 3, 0, 1), (-373607224395850706503959150733460027291137657802148375000 : ℤ)), ((6, 3, 1, 0), (807200110609604408734548868340743601127981303984375000000 : ℤ)),
    ((7, 0, 0, 3), (-771128641776694683711235541688122103091554299640965216250 : ℤ)), ((7, 0, 1, 2), (106160553483906827134578541782984422193072509765625000000 : ℤ)), ((7, 2, 0, 1), (-291134701874266082733868192985656479422282050781250000000 : ℤ)), ((7, 2, 1, 0), (-815177165247945031654830940359838142382389742187500000000 : ℤ)),
    ((8, 1, 0, 1), (178349729852963469586091950195413829284361816406250000000 : ℤ)), ((8, 1, 1, 0), (746964286502297354596972664508942606112868012695312500000 : ℤ)), ((9, 0, 0, 1), (-106160553483906827134578541782984422193072509765625000000 : ℤ)), ((9, 0, 1, 0), (-646698153182127178946597376298417064293824552539062500000 : ℤ))
  ]

lemma hb_d4_11 : allBound wsD4_11 = true := by decide
lemma hk_d4_11 : (1025821288467513302184052237011936092887672984017883965937500 : ℤ) ≠ 0 := by decide
lemma hc_d4_11 : compileStrict wsD4_11 = [(packKey 4 0 2 2 0, (1025821288467513302184052237011936092887672984017883965937500 : ℤ))] := by decide

def wsD4_12 : List (Exps × ℤ) :=
  [
    ((0, 2, 0, 8), (26583866147816123671875000 : ℤ)), ((0, 2, 3, 5), (1190957203422162340500000 : ℤ)), ((0, 2, 4, 4), (-1660707797794200724668750 : ℤ)), ((0, 2, 8, 0), (1701367433460231915000000 : ℤ)),
    ((0, 4, 0, 6), (86705233607493609299520000 : ℤ)), ((0, 4, 1, 5), (-47699562712000994435421200 : ℤ)), ((0, 4, 2, 4), (25066903561175636318522272 : ℤ)), ((0, 4, 3, 3), (-783355615050645181844210625 : ℤ)),
    ((0, 4, 4, 2), (-30467863837971410917500000 : ℤ)), ((0, 4, 5, 1), (-12830521622931401584650000 : ℤ)), ((0, 4, 6, 0), (24672773363173808479704000 : ℤ)), ((0, 6, 0, 4), (-365623861450603838533500000 : ℤ)),
    ((0, 6, 1, 3), (32744690807112637811718750 : ℤ)), ((0, 8, 0, 2), (5316773229563224734375000 : ℤ)), ((0, 8, 2, 0), (850683716730115957500000 : ℤ)), ((0, 10, 0, 0), (-326187695563953125000000 : ℤ)),
    ((1, 3, 0, 6), (-40405520511914463637921875 : ℤ)), ((1, 3, 1, 5), (25563833209619339712236250 : ℤ)), ((1, 3, 2, 4), (-17175882202667515915346675 : ℤ)), ((1, 3, 3, 3), (55826118910413859710937500 : ℤ)),
    ((1, 3, 6, 0), (6602604512353307647415625 : ℤ)), ((1, 5, 0, 4), (307124043618507224368140000 : ℤ)), ((1, 5, 1, 3), (-27505540277974615761843750 : ℤ)), ((1, 9, 0, 0), (273997664273720625000000 : ℤ)),
    ((2, 0, 0, 8), (260468941262403600562500000 : ℤ)), ((2, 0, 1, 7), (-139091970698507925000000000 : ℤ)), ((2, 0, 2, 6), (70549649283796337812500000 : ℤ)), ((2, 0, 3, 5), (-33457898671116452925000000 : ℤ)),
    ((2, 0, 4, 4), (14338672735197740800500000 : ℤ)), ((2, 0, 5, 3), (-101559546126571369725000000 : ℤ)), ((2, 0, 6, 2), (110127814610521502812500000 : ℤ)), ((2, 0, 7, 1), (-90748573917142443750000000 : ℤ)),
    ((2, 0, 8, 0), (65966257809412092562500000 : ℤ)), ((2, 2, 0, 6), (-59547860171108117025000000 : ℤ)), ((2, 2, 1, 5), (35728716102664870215000000 : ℤ)), ((2, 2, 2, 4), (-20722655339545624724700000 : ℤ)),
    ((2, 4, 0, 4), (-243980139676310701113567600 : ℤ)), ((2, 4, 1, 3), (19582025470316876323614375 : ℤ)), ((2, 4, 2, 2), (20311909225314273945000000 : ℤ)), ((2, 4, 3, 1), (-22025562922104300562500000 : ℤ)),
    ((2, 4, 4, 0), (18149714783428488750000000 : ℤ)), ((2, 8, 0, 0), (4181478300342213850000000 : ℤ)), ((3, 3, 0, 4), (31607233761527728099798800 : ℤ)), ((3, 3, 1, 3), (-334956713462483158265625000 : ℤ)),
    ((3, 3, 3, 1), (-17864358051332435107500000 : ℤ)), ((3, 7, 0, 0), (-368312506533926500000000 : ℤ)), ((4, 2, 0, 4), (124335932037273748348200000 : ℤ)), ((4, 4, 0, 2), (-654893816142252756234375 : ℤ)),
    ((4, 6, 0, 0), (130475078225581250000000 : ℤ)), ((5, 3, 0, 2), (178643580513324351075000000 : ℤ)), ((5, 3, 2, 0), (10718614830799461064500000 : ℤ)), ((6, 0, 0, 4), (-73124772290120767706700000 : ℤ)),
    ((6, 0, 1, 3), (6548938161422527562343750 : ℤ)), ((6, 4, 0, 0), (-65237539112790625000000 : ℤ)), ((7, 3, 0, 0), (4287423445129538875000000 : ℤ)), ((8, 2, 0, 0), (1789074272629170100000000 : ℤ)),
    ((9, 1, 0, 0), (-1095990657094882500000000 : ℤ)), ((10, 0, 0, 0), (652375391127906250000000 : ℤ))
  ]

lemma hb_d4_12 : allBound wsD4_12 = true := by decide
lemma hk_d4_12 : (125050506359327045752500000 : ℤ) ≠ 0 := by decide
lemma hc_d4_12 : compileStrict wsD4_12 = [(packKey 4 0 3 0 1, (125050506359327045752500000 : ℤ))] := by decide

def wsD4_13 : List (Exps × ℤ) :=
  [
    ((0, 2, 4, 4), (351750 : ℤ)), ((0, 4, 3, 3), (1375875 : ℤ)), ((0, 6, 0, 4), (10545000 : ℤ)), ((0, 6, 1, 3), (-1406250 : ℤ)),
    ((1, 3, 0, 6), (-9375 : ℤ)), ((1, 3, 1, 5), (5250 : ℤ)), ((1, 3, 2, 4), (-2815 : ℤ)), ((1, 3, 6, 0), (-1875 : ℤ)),
    ((1, 5, 0, 4), (-8857800 : ℤ)), ((1, 5, 1, 3), (1181250 : ℤ)), ((2, 2, 2, 4), (703000 : ℤ)), ((2, 4, 0, 4), (7229652 : ℤ)),
    ((2, 4, 1, 3), (-964125 : ℤ)), ((3, 3, 0, 4), (-1741860 : ℤ)), ((3, 3, 4, 0), (-5272500 : ℤ)), ((4, 2, 0, 4), (-4218000 : ℤ)),
    ((4, 4, 0, 2), (28125 : ℤ)), ((6, 0, 0, 4), (2109000 : ℤ)), ((6, 0, 1, 3), (-281250 : ℤ))
  ]

lemma hb_d4_13 : allBound wsD4_13 = true := by decide
lemma hk_d4_13 : (36907500 : ℤ) ≠ 0 := by decide
lemma hc_d4_13 : compileStrict wsD4_13 = [(packKey 4 0 3 1 0, (36907500 : ℤ))] := by decide

def wsD4_14 : List (Exps × ℤ) :=
  [
    ((0, 1, 0, 9), (-1202196847360290133029238342251976165588033855991606437482375000 : ℤ)), ((0, 1, 1, 8), (731239171923482155828032822753758592280396134536326431592500000 : ℤ)), ((0, 1, 2, 7), (-443776271541757174187135805121093648238652503458425219515625000 : ℤ)), ((0, 1, 3, 6), (253893279374629058173966074316339541025632472249427838906250000 : ℤ)),
    ((0, 1, 4, 5), (-207724772428733563141007448653584880340057247336307927053125000 : ℤ)), ((0, 1, 5, 4), (198635661319775685562515210728464452215904732596885196037500000 : ℤ)), ((0, 1, 6, 3), (6194637696701604209632706808234090025328401646832927282375000 : ℤ)), ((0, 1, 7, 2), (-80678509668675609437550351727906470179806054690645739662500000 : ℤ)),
    ((0, 1, 8, 1), (-42653248783393943730255531465415032402127040868458906953125000 : ℤ)), ((0, 1, 9, 0), (-266788488595163035533078179493806961384787143536003997843750000 : ℤ)), ((0, 3, 0, 7), (-1638264719563348464852924462411457358305860008747537499452625000 : ℤ)), ((0, 3, 1, 6), (912616964336996505342526013074793903520266444941724247183787500 : ℤ)),
    ((0, 3, 2, 5), (-478499744839273176255812909004045344927296098563623230297921000 : ℤ)), ((0, 3, 3, 4), (370892870617094454308358341840025867570525132182039335064260260 : ℤ)), ((0, 3, 4, 3), (-5348062254146291588143846279119401994540194452915888484427656391 : ℤ)), ((0, 3, 5, 2), (361472197784446374282959418196394482148906051484543621942187500 : ℤ)),
    ((0, 3, 6, 1), (-488486327841673001040024874767588615660796659056135221875000000 : ℤ)), ((0, 3, 7, 0), (461658437348355301662805131053580846795937094163279261936757500 : ℤ)), ((0, 5, 0, 5), (-2516189930163702456008328242258791085772930336135229171298437500 : ℤ)), ((0, 5, 1, 4), (1417020080626291349402475186415602598664556774556570546231031250 : ℤ)),
    ((0, 5, 2, 3), (-8983511582827334802074009053400860870710849595876385158149990000 : ℤ)), ((0, 5, 3, 2), (-6194637696701604209632706808234090025328401646832927282375000 : ℤ)), ((0, 5, 4, 1), (80678509668675609437550351727906470179806054690645739662500000 : ℤ)), ((0, 5, 5, 0), (850487513451560669200196668112314705551169515782542530128906250 : ℤ)),
    ((0, 7, 0, 3), (26482320941176733944641730581947337848004482192830003578795750000 : ℤ)), ((0, 7, 1, 2), (-28274774121128691755558292919911132251777503017739608937500000 : ℤ)), ((0, 7, 3, 0), (488486327841673001040024874767588615660796659056135221875000000 : ℤ)), ((0, 9, 0, 1), (-27892430673818931791167406983783373357680873294866291467625000 : ℤ)),
    ((0, 9, 1, 0), (-111302957031973661288228521552783763689956793764497917500000000 : ℤ)), ((1, 0, 0, 9), (1846668369663669512470245136670254326411689870651899563146512500 : ℤ)), ((1, 0, 1, 8), (-1074828373696406658209100432813839205718561314294198786897750000 : ℤ)), ((1, 0, 2, 7), (587450748251919501997575580128065366281055799873199546589062500 : ℤ)),
    ((1, 0, 3, 6), (-306382436313845750476128226387902793467045552615610938984375000 : ℤ)), ((1, 0, 4, 5), (222640416338132527216206399356555184064499572263848024479687500 : ℤ)), ((1, 0, 5, 4), (-213922274000602241035822088649547909346823006252001795848375000 : ℤ)), ((1, 0, 6, 3), (216797115271023398992809933715268833820078041973276611105162500 : ℤ)),
    ((1, 0, 7, 2), (-338849740608437559637711477257207174755185429700712106582500000 : ℤ)), ((1, 0, 8, 1), (311118572855205363049635960172588601687745691232189684507812500 : ℤ)), ((1, 0, 9, 0), (119978922069314583926543517577975015709993181750457380562500000 : ℤ)), ((1, 2, 0, 7), (1761281670536680201497998552093408049666057901190168532750000000 : ℤ)),
    ((1, 2, 1, 6), (-954186873475256790680393907554851220510867442312312723056250000 : ℤ)), ((1, 2, 2, 5), (500150606197226692708218846996985480389830001560965659380250000 : ℤ)), ((1, 2, 3, 4), (-542540264169011866280045945493630212162777070028628567265975000 : ℤ)), ((1, 2, 4, 3), (367503679021558180286684544239981596425138685354532973806250000 : ℤ)),
    ((1, 2, 6, 1), (512910644233756651092026118505968046443836492008941982968750000 : ℤ)), ((1, 2, 7, 0), (-483929171400055158760093706371523413498651483896143677736250000 : ℤ)), ((1, 4, 0, 5), (2174573032436985697266658701096813804401488288210566254187562500 : ℤ)), ((1, 4, 1, 4), (-1234909074830796553010623703652255179793427515598957473105003750 : ℤ)),
    ((1, 4, 2, 3), (7394490714355947147200646504299676839967795904455903665576391600 : ℤ)), ((1, 4, 3, 2), (-38155927388975332262470513024137131142739751011315663303837500 : ℤ)), ((1, 4, 5, 0), (-776633225870352034738092393248862073000531531503773662209843750 : ℤ)), ((1, 6, 0, 3), (-23082287063084492424974118535532857951595258731210855434379406250 : ℤ)),
    ((1, 6, 1, 2), (-27053228865492488889523899834934494748420059477539062500000000 : ℤ)), ((1, 6, 3, 0), (-512910644233756651092026118505968046443836492008941982968750000 : ℤ)), ((1, 8, 0, 1), (52359943616734587670209034872584156138819798780796918262500000 : ℤ)), ((1, 8, 1, 0), (90190540098846701959730335605943718522975951742598500000000000 : ℤ)),
    ((2, 1, 0, 7), (-2692780882227222418233137122156332243830141583046945410585937500 : ℤ)), ((2, 1, 1, 6), (1507957294047244554210556788407546056544879286506289429928125000 : ℤ)), ((2, 1, 2, 5), (-808552339570093984781469973212808028414063846002896141951937500 : ℤ)), ((2, 1, 3, 4), (412166787135939104711134716413499826633523903594513634441960000 : ℤ)),
    ((2, 1, 6, 1), (-538556176445444483646627424431266448766028316609389082117187500 : ℤ)), ((2, 1, 7, 0), (609337845349702901497327028785090039175277752506623075766875000 : ℤ)), ((2, 3, 0, 5), (-6189075258629940507896442403601817984932029729698844907104485000 : ℤ)), ((2, 3, 1, 4), (3376638872660031386435117450087680199817148799371436203111244100 : ℤ)),
    ((2, 3, 2, 3), (3584224685511613519932936381359542084527981303955752062243437594 : ℤ)), ((2, 3, 3, 2), (-240981465189630916188639612130929654765937367656362414628125000 : ℤ)), ((2, 3, 5, 0), (2210384020939264467105872287000649280332867760606730323965887500 : ℤ)), ((2, 5, 0, 3), (19306687775563785816036032626564900714013312553498215837990309250 : ℤ)),
    ((2, 5, 1, 2), (22724712247013690667200075861344975588672849961132812500000000 : ℤ)), ((2, 5, 3, 0), (538556176445444483646627424431266448766028316609389082117187500 : ℤ)), ((2, 7, 0, 1), (-3054696013612180459754241489933174949878745001578125000000000 : ℤ)), ((2, 7, 1, 0), (-71646026652099657264762270050282966584593375005875781250000000 : ℤ)),
    ((3, 2, 0, 5), (-24228788044937700181688582077161382488191958523270655283750000 : ℤ)), ((3, 2, 1, 4), (16310805992452827022686413869016878843191779744969539458900000 : ℤ)), ((3, 2, 2, 3), (-226966966770710460931440429603364734451145750584662607537500000 : ℤ)), ((3, 4, 0, 3), (-15748205318103529091902733355816392642239033968383533497276567645 : ℤ)),
    ((3, 4, 1, 2), (-212991163729316185131343104013786962898199150108461007689275000 : ℤ)), ((3, 4, 3, 0), (-452387188214173366263167036522263816963463785951886828978437500 : ℤ)), ((3, 6, 0, 1), (1082129154619699555580955993397379789936802379101562500000000 : ℤ)), ((3, 6, 1, 0), (56027978996683022416685007639427527860766673422708281250000000 : ℤ)),
    ((4, 1, 0, 5), (-4946051656048440102042022860488290559871144740746875000000000 : ℤ)), ((4, 3, 0, 3), (-28626711519787512625525036665637384638291754954077682840741875564 : ℤ)), ((4, 5, 1, 0), (-43256477029268494435739990043079084602613988699398940625000000 : ℤ)), ((5, 0, 0, 5), (3029961632935158755626676781512663411823046661484375000000000 : ℤ)),
    ((5, 0, 1, 4), (841238370853140693032671918379601022999105186686093750000000 : ℤ)), ((5, 0, 2, 3), (1944434700191345347486855182869558732986823573306602264392750000 : ℤ)), ((5, 2, 0, 3), (9440144447305930020288053944089185138197299252648811876982812500 : ℤ)), ((5, 4, 1, 0), (33039438080111735223816224983946429765877550195797507000000000 : ℤ)),
    ((6, 3, 0, 1), (72686364134813100545065746231484147464575875569811965851250000 : ℤ)), ((6, 3, 1, 0), (-41140270309315723814112118587097569747064244579069587500000000 : ℤ)), ((7, 0, 0, 3), (-4694965372071363076368373176899619176344484870736364160102921250 : ℤ)), ((7, 0, 1, 2), (-5410645773098497777904779966986898949684011895507812500000000 : ℤ)),
    ((7, 2, 0, 1), (14838154968145320306126068581464871679613434222240625000000000 : ℤ)), ((7, 2, 1, 0), (41546833910806896857152992028101640702917615822273750000000000 : ℤ)), ((8, 1, 0, 1), (-9089884898805476266880030344537990235469139984453125000000000 : ℤ)), ((8, 1, 1, 0), (-38070253279452443942754163740400388004300169756760156250000000 : ℤ)),
    ((9, 0, 0, 1), (5410645773098497777904779966986898949684011895507812500000000 : ℤ)), ((9, 0, 1, 0), (32960026244738001022053666522400013003182003116976031250000000 : ℤ))
  ]

lemma hb_d4_14 : allBound wsD4_14 = true := by decide
lemma hk_d4_14 : (3166710317499213563842169255655846718744246501663207802849062500 : ℤ) ≠ 0 := by decide
lemma hc_d4_14 : compileStrict wsD4_14 = [(packKey 4 0 4 0 0, (3166710317499213563842169255655846718744246501663207802849062500 : ℤ))] := by decide

def wsD4_15 : List (Exps × ℤ) :=
  [
    ((0, 2, 4, 4), (37500 : ℤ)), ((0, 4, 0, 6), (1318125 : ℤ)), ((0, 4, 1, 5), (-738150 : ℤ)), ((0, 4, 2, 4), (395789 : ℤ)),
    ((0, 4, 3, 3), (-2599560 : ℤ)), ((0, 4, 4, 2), (-790875 : ℤ)), ((0, 4, 6, 0), (263625 : ℤ)), ((0, 6, 1, 3), (-37500 : ℤ)),
    ((1, 3, 0, 6), (-1406250 : ℤ)), ((1, 3, 1, 5), (787500 : ℤ)), ((1, 3, 2, 4), (-422250 : ℤ)), ((1, 3, 6, 0), (-281250 : ℤ)),
    ((1, 5, 1, 3), (31500 : ℤ)), ((2, 4, 1, 3), (-25710 : ℤ)), ((2, 4, 2, 2), (527250 : ℤ)), ((3, 3, 0, 4), (2346000 : ℤ)),
    ((4, 0, 3, 3), (-5272500 : ℤ)), ((4, 4, 0, 2), (1055250 : ℤ)), ((6, 0, 1, 3), (-7500 : ℤ))
  ]

lemma hb_d4_15 : allBound wsD4_15 = true := by decide
lemma hk_d4_15 : (36907500 : ℤ) ≠ 0 := by decide
lemma hc_d4_15 : compileStrict wsD4_15 = [(packKey 4 1 0 0 3, (36907500 : ℤ))] := by decide

def wsD4_16 : List (Exps × ℤ) :=
  [
    ((0, 2, 0, 8), (8286587235937500 : ℤ)), ((0, 2, 4, 4), (1732598330636250 : ℤ)), ((0, 2, 5, 3), (-69607332781875000 : ℤ)), ((0, 4, 0, 6), (198083089928561250 : ℤ)),
    ((0, 4, 1, 5), (-110926530359994300 : ℤ)), ((0, 4, 2, 4), (59477749135882658 : ℤ)), ((0, 4, 3, 3), (447259709853971592 : ℤ)), ((0, 4, 4, 2), (-72547056190633500 : ℤ)),
    ((0, 4, 6, 0), (39616617985712250 : ℤ)), ((0, 6, 1, 3), (-1732598330636250 : ℤ)), ((0, 6, 2, 2), (69607332781875000 : ℤ)), ((0, 8, 0, 2), (-207164680898437500 : ℤ)),
    ((1, 3, 0, 6), (-64972437398859375 : ℤ)), ((1, 3, 1, 5), (36384564943361250 : ℤ)), ((1, 3, 2, 4), (-19585535202114175 : ℤ)), ((1, 3, 3, 3), (87009165977343750 : ℤ)),
    ((1, 3, 6, 0), (-12994487479771875 : ℤ)), ((1, 5, 1, 3), (1455382597734450 : ℤ)), ((1, 5, 2, 2), (-58470159536775000 : ℤ)), ((1, 7, 0, 2), (174018331954687500 : ℤ)),
    ((2, 0, 0, 8), (8231593597818750 : ℤ)), ((2, 0, 1, 7), (-4395720157500000 : ℤ)), ((2, 0, 2, 6), (2229578845593750 : ℤ)), ((2, 0, 3, 5), (-1057369155657500 : ℤ)),
    ((2, 0, 4, 4), (453144724726950 : ℤ)), ((2, 0, 5, 3), (-3209583859177500 : ℤ)), ((2, 0, 6, 2), (3480366639093750 : ℤ)), ((2, 0, 7, 1), (-2867924968125000 : ℤ)),
    ((2, 0, 8, 0), (2084730036618750 : ℤ)), ((2, 4, 0, 4), (211473831131500 : ℤ)), ((2, 4, 1, 3), (-1278498360429603 : ℤ)), ((2, 4, 2, 2), (48364704127089000 : ℤ)),
    ((2, 4, 4, 0), (573584993625000 : ℤ)), ((2, 6, 0, 2), (-146175398841937500 : ℤ)), ((3, 3, 0, 4), (668692053219441300 : ℤ)), ((3, 3, 1, 3), (-174018331954687500 : ℤ)),
    ((3, 5, 0, 2), (119306968388133750 : ℤ)), ((4, 0, 4, 2), (-6960733278187500 : ℤ)), ((4, 4, 0, 2), (-95270912565955875 : ℤ)), ((6, 0, 1, 3), (-346519666127250 : ℤ)),
    ((6, 0, 2, 2), (13921466556375000 : ℤ)), ((7, 1, 0, 2), (34803666390937500 : ℤ)), ((8, 0, 0, 2), (-49122889134637500 : ℤ))
  ]

lemma hb_d4_16 : allBound wsD4_16 = true := by decide
lemma hk_d4_16 : (48725132947312500 : ℤ) ≠ 0 := by decide
lemma hc_d4_16 : compileStrict wsD4_16 = [(packKey 4 1 0 1 2, (48725132947312500 : ℤ))] := by decide

def wsD4_17 : List (Exps × ℤ) :=
  [
    ((0, 2, 0, 8), (815589843750 : ℤ)), ((0, 2, 4, 4), (-66715852500 : ℤ)), ((0, 4, 0, 6), (-2905284585000 : ℤ)), ((0, 4, 1, 5), (1632341711350 : ℤ)),
    ((0, 4, 2, 4), (-878449855556 : ℤ)), ((0, 4, 3, 3), (34168824120414 : ℤ)), ((0, 4, 5, 1), (-80735156250 : ℤ)), ((0, 4, 6, 0), (-534922542000 : ℤ)),
    ((0, 6, 1, 3), (66715852500 : ℤ)), ((0, 8, 0, 2), (-15496207031250 : ℤ)), ((1, 3, 0, 6), (2501844468750 : ℤ)), ((1, 3, 1, 5), (-1401032902500 : ℤ)),
    ((1, 3, 2, 4), (746914624150 : ℤ)), ((1, 3, 3, 3), (1712738671875 : ℤ)), ((1, 3, 6, 0), (500368893750 : ℤ)), ((1, 5, 1, 3), (-56041316100 : ℤ)),
    ((1, 7, 0, 2), (13701909375000 : ℤ)), ((2, 4, 0, 4), (-26911718750 : ℤ)), ((2, 4, 1, 3), (60810950974 : ℤ)), ((2, 4, 4, 0), (16147031250 : ℤ)),
    ((2, 6, 0, 2), (-11509603875000 : ℤ)), ((3, 3, 0, 4), (-6594678013650 : ℤ)), ((3, 3, 1, 3), (-10276432031250 : ℤ)), ((3, 5, 0, 2), (9394029067500 : ℤ)),
    ((4, 0, 0, 6), (-461343750000 : ℤ)), ((4, 0, 1, 5), (269117187500 : ℤ)), ((4, 0, 2, 4), (-150705625000 : ℤ)), ((4, 0, 5, 1), (-161470312500 : ℤ)),
    ((4, 4, 0, 2), (-7505533406250 : ℤ)), ((4, 4, 2, 0), (32294062500 : ℤ)), ((6, 0, 1, 3), (13343170500 : ℤ)), ((7, 1, 0, 2), (2740381875000 : ℤ)),
    ((8, 0, 0, 2), (-3867853275000 : ℤ))
  ]

lemma hb_d4_17 : allBound wsD4_17 = true := by decide
lemma hk_d4_17 : (1130292187500 : ℤ) ≠ 0 := by decide
lemma hc_d4_17 : compileStrict wsD4_17 = [(packKey 4 1 0 2 1, (1130292187500 : ℤ))] := by decide

def wsD4_18 : List (Exps × ℤ) :=
  [
    ((0, 2, 0, 8), (8238281250 : ℤ)), ((0, 2, 4, 4), (-673897500 : ℤ)), ((0, 4, 0, 6), (-31629727500 : ℤ)), ((0, 4, 1, 5), (17712647400 : ℤ)),
    ((0, 4, 2, 4), (-9497352844 : ℤ)), ((0, 4, 3, 3), (344952400986 : ℤ)), ((0, 4, 6, 0), (-6325945500 : ℤ)), ((0, 6, 1, 3), (673897500 : ℤ)),
    ((0, 8, 0, 2), (-156527343750 : ℤ)), ((1, 3, 0, 6), (25271156250 : ℤ)), ((1, 3, 1, 5), (-14151847500 : ℤ)), ((1, 3, 2, 4), (7588085850 : ℤ)),
    ((1, 3, 3, 3), (17300390625 : ℤ)), ((1, 3, 6, 0), (5054231250 : ℤ)), ((1, 5, 1, 3), (-566073900 : ℤ)), ((1, 7, 0, 2), (138403125000 : ℤ)),
    ((2, 4, 0, 4), (-516705000 : ℤ)), ((2, 4, 1, 3), (739076426 : ℤ)), ((2, 6, 0, 2), (-116258625000 : ℤ)), ((3, 3, 0, 4), (-66873871350 : ℤ)),
    ((3, 3, 1, 3), (-103802343750 : ℤ)), ((3, 5, 0, 2), (94889182500 : ℤ)), ((4, 0, 0, 6), (-9226875000 : ℤ)), ((4, 0, 1, 5), (5167050000 : ℤ)),
    ((4, 0, 2, 4), (-2770523000 : ℤ)), ((4, 0, 6, 0), (-1845375000 : ℤ)), ((4, 4, 0, 2), (-75813468750 : ℤ)), ((6, 0, 1, 3), (134779500 : ℤ)),
    ((7, 1, 0, 2), (27680625000 : ℤ)), ((8, 0, 0, 2), (-39069225000 : ℤ))
  ]

lemma hb_d4_18 : allBound wsD4_18 = true := by decide
lemma hk_d4_18 : (12917625000 : ℤ) ≠ 0 := by decide
lemma hc_d4_18 : compileStrict wsD4_18 = [(packKey 4 1 0 3 0, (12917625000 : ℤ))] := by decide

def wsD4_19 : List (Exps × ℤ) :=
  [
    ((0, 1, 0, 9), (190730631070274530627423945624506176866765094439679006154015625 : ℤ)), ((0, 1, 1, 8), (-236836205930867851868068559656567014275025248966405962783125000 : ℤ)), ((0, 1, 2, 7), (168500832040425050280470924189210001988421808658224495556640625 : ℤ)), ((0, 1, 3, 6), (-94363572866134217911171764299619853687526872121396302617187500 : ℤ)),
    ((0, 1, 4, 5), (50598698429351126933625935734976081414127896237943080061328125 : ℤ)), ((0, 1, 5, 4), (-30251074381745255664743520614675130068331308282990278942968750 : ℤ)), ((0, 1, 6, 3), (-603530005918576829534639322275314186741751955374475522120234375 : ℤ)), ((0, 1, 7, 2), (46603852442846311620701304933788610159889091858776582031250 : ℤ)),
    ((0, 1, 8, 1), (33673535635260526449453784092165549763307282250582741064453125 : ℤ)), ((0, 1, 9, 0), (-38114734936232858696207943769732856316538107138897969703125000 : ℤ)), ((0, 3, 0, 7), (-1345600888818981773519425757163005097167659127482521553372968750 : ℤ)), ((0, 3, 1, 6), (799657750929356932074588913761167765203709045261811815181412500 : ℤ)),
    ((0, 3, 2, 5), (-447639832276787618443331024725454121145218716931106612095453000 : ℤ)), ((0, 3, 3, 4), (236280554955017113903743257591601882169432799910161209316430930 : ℤ)), ((0, 3, 4, 3), (-2195824161925808384539159646018633352709819440388834063405502778 : ℤ)), ((0, 3, 5, 2), (125347094729741676421692924030113856492812630596931777498437500 : ℤ)),
    ((0, 3, 7, 0), (160172276248231762869830307010519020710539449645945226473622500 : ℤ)), ((0, 5, 0, 5), (97885246132942555493512105839868888739613093980561644267968750 : ℤ)), ((0, 5, 1, 4), (-52619373036804609920201238855840993784582156475566250182640625 : ℤ)), ((0, 5, 2, 3), (-5440084042299903932136258392392383524050525390259287925305087500 : ℤ)),
    ((0, 5, 3, 2), (657385623563121277899302064718440831618354787035414430331953125 : ℤ)), ((0, 5, 4, 1), (-46603852442846311620701304933788610159889091858776582031250 : ℤ)), ((0, 5, 5, 0), (-33673535635260526449453784092165549763307282250582741064453125 : ℤ)), ((0, 7, 0, 3), (20949877845561098205356022013178909968043491004974481376394875000 : ℤ)),
    ((0, 7, 1, 2), (-700802690415123268398234458390012530219296376386710084362031250 : ℤ)), ((0, 9, 0, 1), (95486317777713320876229601891480810841295265611033839718281250 : ℤ)), ((0, 9, 1, 0), (-736154375638030248272896072216386256193937939726194149575000 : ℤ)), ((1, 0, 0, 9), (-75374472755764309280465909678477657158849525590179707031250 : ℤ)),
    ((1, 0, 1, 8), (4176165738789019842419195480509018381119715369630488281250 : ℤ)), ((1, 0, 2, 7), (20399791016034431119399108720592824922692487711849407031250 : ℤ)), ((1, 0, 3, 6), (1411676842201542374377013265551717737241265438785944441406250 : ℤ)), ((1, 0, 4, 5), (-920130584251223885831280839637421805280185355394600488281250 : ℤ)),
    ((1, 0, 5, 4), (570503085066584900319625709091577044417540284413052214843750 : ℤ)), ((1, 0, 6, 3), (-341076657446344233467307872845168128241792924782637207031250 : ℤ)), ((1, 0, 7, 2), (195736180259954508806945480721912162671534185806861644531250 : ℤ)), ((1, 0, 8, 1), (1943873289275402342702301163926898086376150645117074016406250 : ℤ)),
    ((1, 0, 9, 0), (-828449368288492863811626583419312501909547280881139121093750 : ℤ)), ((1, 2, 0, 7), (-278549099399425947603762053400253014428472512437626172218750000 : ℤ)), ((1, 2, 1, 6), (167129459639655568562257232040151808657083507462575703331250000 : ℤ)), ((1, 2, 2, 5), (-93592497398207118394864049942485012847966764179042393865500000 : ℤ)),
    ((1, 2, 3, 4), (987689794265729556400870704234596850821141365993496899969518750 : ℤ)), ((1, 2, 4, 3), (611578601494899514198704646823792506648128591426793056123328125 : ℤ)), ((1, 2, 7, 0), (33425891927931113712451446408030361731416701492515140666250000 : ℤ)), ((1, 4, 0, 5), (-82420036183702088766375030928424441705056310024980158191343750 : ℤ)),
    ((1, 4, 1, 4), (44336188167588653229502551494432373607475185171563542391043125 : ℤ)), ((1, 4, 2, 3), (4439310420708200052971512126539044353028823136462293575283589125 : ℤ)), ((1, 4, 3, 2), (-552135708461532604588720272788921264933769662524791594037434375 : ℤ)), ((1, 4, 5, 0), (27896995275763761749000718404633682183902886961466087690859375 : ℤ)),
    ((1, 6, 0, 3), (-18490592405221752988567434328149171980890192928747942724729975000 : ℤ)), ((1, 6, 1, 2), (582130094435554442352581808992377817701645264482944653249218750 : ℤ)), ((1, 8, 0, 1), (1508082325785686461702161438994870727323140753824370325312500 : ℤ)), ((1, 8, 1, 0), (893031903260811018517248400755612267832054112997643668375000 : ℤ)),
    ((2, 3, 0, 5), (19692689406186076436845278595998147443641613373672657676618503750 : ℤ)), ((2, 3, 1, 4), (-10559138273297074002238194303926029530062221861100077458532717725 : ℤ)), ((2, 3, 2, 3), (1931084568227287768624929402939097255286077211183696098511689352 : ℤ)), ((2, 3, 3, 2), (-83564729819827784281128616020075904328541753731287851665625000 : ℤ)),
    ((2, 3, 5, 0), (-7031297913884467332604326995205054508062808186145506265869415625 : ℤ)), ((2, 5, 0, 3), (15529020156520869970490092678934268655669099041196218236875366500 : ℤ)), ((2, 5, 1, 2), (-501914627560556399183687777739947761639766701764298846700156250 : ℤ)), ((2, 5, 2, 1), (2154224705781777934586509697725065795064113266437556328468750 : ℤ)),
    ((2, 7, 0, 1), (12589743961802669649184414776194159052011555555831185523437500 : ℤ)), ((2, 7, 1, 0), (-832192040050435456842622927815504126765148686943575557812500 : ℤ)), ((3, 0, 0, 7), (-10258212884675133021840522370119360928876729840178839659375000 : ℤ)), ((3, 2, 0, 5), (-9521376161676368597371642730217768009151189857379712454750000 : ℤ)),
    ((3, 2, 1, 4), (5277273822997863613669363748134756870600517498782269057075000 : ℤ)), ((3, 2, 2, 3), (-1157715547858307997378057933095257936470620266034667936097781250 : ℤ)), ((3, 4, 0, 3), (-12672854643893043156517217819505040457660490331396253405541989610 : ℤ)), ((3, 4, 1, 2), (287105524332416449200090275299455011527427686378655231188181250 : ℤ)),
    ((3, 4, 2, 1), (-2527623654783952776581504711997410532875226232620066092070000 : ℤ)), ((3, 6, 0, 1), (-10565019800425012747021024620747105156258665577496024952343750 : ℤ)), ((3, 6, 1, 0), (728063670612209106970677874881791119289639947358681953125000 : ℤ)), ((4, 1, 0, 5), (34550424964099194312945970853294824770136964673902957812500 : ℤ)),
    ((4, 1, 3, 2), (-21542247057817779345865096977250657950641132664375563284687500 : ℤ)), ((4, 3, 0, 3), (-13808753118639946339931813491552787021671688686923263355030526737 : ℤ)), ((4, 5, 1, 0), (-611513846496014553988731022353975973557660325085894749218750 : ℤ)), ((5, 0, 0, 5), (-859059364099663230505406301757683836669420064488118820312500 : ℤ)),
    ((5, 0, 1, 4), (481113001774638806327453124015455326298633389910278600312500 : ℤ)), ((5, 0, 2, 3), (1302460742067059330428809979287394917647346832986256715297156250 : ℤ)), ((5, 2, 0, 3), (6946293287149847984268347598571547618823721596208007616586687500 : ℤ)), ((5, 4, 1, 0), (-218998622464703323098652288941067593416236203656339735250000 : ℤ)),
    ((6, 1, 0, 3), (30774638654025399065521567110358082786630189520536518978125000 : ℤ)), ((6, 1, 1, 2), (129253482346906676075190581863503947703846795986253379708125000 : ℤ)), ((6, 3, 0, 1), (28564128485029105792114928190653304027453569572139137364250000 : ℤ)), ((6, 3, 1, 0), (820452413113542012881342711807898217862232320255548763775000 : ℤ)),
    ((7, 0, 0, 3), (-3715703988846650825750927761121467586341827265475609412933495000 : ℤ)), ((7, 0, 1, 2), (42566886117449930713264600733616164852416598047301285102343750 : ℤ)), ((7, 0, 2, 1), (7180749019272593115288365659083552650213710888125187761562500 : ℤ)), ((7, 2, 0, 1), (-103651274892297582938837912559884474310410894021708873437500 : ℤ)),
    ((7, 2, 1, 0), (-290223569698433232228746155167676528069150503260784845625000 : ℤ)), ((8, 1, 0, 1), (2577178092298989691516218905273051510008260193464356460937500 : ℤ)), ((8, 1, 1, 0), (-596368182410958666383925467285666456372306953980914062500 : ℤ)), ((9, 0, 0, 1), (-42566886117449930713264600733616164852416598047301285102343750 : ℤ)),
    ((9, 0, 1, 0), (145953515940962369203497818100521461832997879159725484375000 : ℤ))
  ]

lemma hb_d4_19 : allBound wsD4_19 = true := by decide
lemma hk_d4_19 : (150795729404724455421055678840754605654487928650628942992812500 : ℤ) ≠ 0 := by decide
lemma hc_d4_19 : compileStrict wsD4_19 = [(packKey 4 1 1 0 2, (150795729404724455421055678840754605654487928650628942992812500 : ℤ))] := by decide

def wsD4_20 : List (Exps × ℤ) :=
  [
    ((0, 1, 0, 9), (307853296284279023608937829067845807923519325201697533179195343750 : ℤ)), ((0, 1, 1, 8), (-184593082034285434595189456926499070313891286569669243989799687500 : ℤ)), ((0, 1, 2, 7), (109373099078136251073797141368402571159675098436904243448980468750 : ℤ)), ((0, 1, 3, 6), (-61827158232327340516336283941423549287765235539221881651289062500 : ℤ)),
    ((0, 1, 4, 5), (33392731492731527391284933674841927007833914004149745122061718750 : ℤ)), ((0, 1, 5, 4), (-24188859163697908470155233889360026936068765559916488350675000000 : ℤ)), ((0, 1, 6, 3), (6931497794550286994634207030308516781680497223939844840522843750 : ℤ)), ((0, 1, 7, 2), (8673341228565598725148271626771641575207706218332579797900000000 : ℤ)),
    ((0, 1, 8, 1), (16918424827875479514674701629811004760387758991190803090996093750 : ℤ)), ((0, 1, 9, 0), (-22546013620913784477030540980968394909932745880533777222367187500 : ℤ)), ((0, 3, 0, 7), (301595679400568442134778480811869474041839473507900041410976437500 : ℤ)), ((0, 3, 1, 6), (-175270715671898717803249620054500238615393861921092812725323231250 : ℤ)),
    ((0, 3, 2, 5), (101739897225982033823183705711042658646349307838023211483237585500 : ℤ)), ((0, 3, 3, 4), (-57774476000013470508876834699292442420578307049509487236245775130 : ℤ)), ((0, 3, 4, 3), (-94302636111871265030852322731664527778455366669000627696492596797 : ℤ)), ((0, 3, 5, 2), (102974116633317437977867541926812597805941961017746170321286718750 : ℤ)),
    ((0, 3, 6, 1), (-732729491762509501560037312151382923491194988584202832812500000 : ℤ)), ((0, 3, 7, 0), (-29579086543466045912244308413891020109422853110305271162215966250 : ℤ)), ((0, 5, 0, 5), (230899986134306039696199072511886449017729621062158503601228125000 : ℤ)), ((0, 5, 1, 4), (-133432899883281990516642445430517556600529404091159586933622125000 : ℤ)),
    ((0, 5, 2, 3), (429570558464514219331875954231313463976935304105028469869444447500 : ℤ)), ((0, 5, 3, 2), (-6931497794550286994634207030308516781680497223939844840522843750 : ℤ)), ((0, 5, 4, 1), (-594998581883931470448860260302644843717281469191743566142187500 : ℤ)), ((0, 5, 5, 0), (-24188933209888980043904171859633101818729141265417555699578125000 : ℤ)),
    ((0, 7, 0, 3), (-1380281765841618293033640649751621867574397272587837045952308250000 : ℤ)), ((0, 7, 1, 2), (63103414697926720714741390393103973498732094886672988055289062500 : ℤ)), ((0, 7, 2, 1), (96940111760180007056392936397627960777885096989690034781093750000 : ℤ)), ((0, 7, 3, 0), (732729491762509501560037312151382923491194988584202832812500000 : ℤ)),
    ((0, 9, 0, 1), (-46949518997316636015621859240676555320623231749275261310512312500 : ℤ)), ((0, 9, 1, 0), (-164371443261822202798352976203324690102149991593009531605612900000 : ℤ)), ((1, 0, 0, 9), (-14467513212817257884055208462199908561063101342949454741209237500 : ℤ)), ((1, 0, 1, 8), (8481586255860189833686750256765086311502348088986118479540687500 : ℤ)),
    ((1, 0, 2, 7), (-4656042677461984315797329455564671041621568465337948098989062500 : ℤ)), ((1, 0, 3, 6), (2440784296451210405120823622231475227067239529215562736914062500 : ℤ)), ((1, 0, 4, 5), (-1640403805034777920969181133605353830620757508373041453129687500 : ℤ)), ((1, 0, 5, 4), (1722319318209022605562922126445934119798260210684888053002562500 : ℤ)),
    ((1, 0, 6, 3), (-1404684387295829866008760323356659392296196967414173743305837500 : ℤ)), ((1, 0, 7, 2), (2498994043912512175885213093271108343612582170605322977797187500 : ℤ)), ((1, 0, 8, 1), (-2359205132013832392236730515839281833245789219127774178539062500 : ℤ)), ((1, 0, 9, 0), (-1087316594548552320350823856272418914604540544820557224945312500 : ℤ)),
    ((1, 2, 0, 7), (-440407011042685591859610867054406480949064688548680057577468750000 : ℤ)), ((1, 2, 1, 6), (264398079818881482111094128068195678983371964076810717141371875000 : ℤ)), ((1, 2, 2, 5), (-148114215762997005647321914330040177035332683532214895797465125000 : ℤ)), ((1, 2, 3, 4), (102345389889271951574624469388691127392256444604199901892488187500 : ℤ)),
    ((1, 2, 4, 3), (-84671689412128703745952012886969298269763086768030944447750781250 : ℤ)), ((1, 2, 6, 1), (769365966350634976638039177758952069665754738013412974453125000 : ℤ)), ((1, 2, 7, 0), (52439978268718790721282803226348306042579675822211621728586875000 : ℤ)), ((1, 4, 0, 5), (-191137807029145452878641175691154513122904627211236620237225375000 : ℤ)),
    ((1, 4, 1, 4), (110289699715193489657916164980800991615113955029535072174506397500 : ℤ)), ((1, 4, 2, 3), (-351664269933965150356361709749345563484077832113061224504414729650 : ℤ)), ((1, 4, 3, 2), (6103395024881407048694485970130485975070857061592304414700356250 : ℤ)), ((1, 4, 5, 0), (20790544922709509715326850465259661894381636506776301623353437500 : ℤ)),
    ((1, 6, 0, 3), (1189433821967365906763138165499600558111791122173208309360031456250 : ℤ)), ((1, 6, 1, 2), (-43312258858398805150182778992831848384922943045577125260351562500 : ℤ)), ((1, 6, 2, 1), (-81429693878551205927370066574007487053423481471339629216118750000 : ℤ)), ((1, 6, 3, 0), (-769365966350634976638039177758952069665754738013412974453125000 : ℤ)),
    ((1, 8, 0, 1), (40169304809707132739248609755069566521972075636162652230194375000 : ℤ)), ((1, 8, 1, 0), (137685484424284619060965517712236429287868551355049750824268000000 : ℤ)), ((2, 1, 0, 7), (24235027940045001764098234099406990194471274247422508695273437500 : ℤ)), ((2, 1, 1, 6), (-13571615646425200987895011095667914508903913578556604869353125000 : ℤ)),
    ((2, 1, 2, 5), (7276971056130845863033229758915272255726574614026065277567437500 : ℤ)), ((2, 1, 3, 4), (-3709501084223451942400212447721498439701715132350622709977640000 : ℤ)), ((2, 1, 6, 1), (4847005588009000352819646819881398038894254849484501739054687500 : ℤ)), ((2, 1, 7, 0), (-5484040608147326113475943259065810352577499772559607681901875000 : ℤ)),
    ((2, 3, 0, 5), (587029414386110040262201548949501806566364489389615720630155972500 : ℤ)), ((2, 3, 1, 4), (-321084891343632787396421912814325060441630680502722429356814223350 : ℤ)), ((2, 3, 2, 3), (20799480942629696210740621559040369519815514521551759760802356198 : ℤ)), ((2, 3, 3, 2), (-133276152262331630022840318882960372389218038671624136734920312500 : ℤ)),
    ((2, 3, 5, 0), (-171730707099311608451572881842188864914815901607302512708601318750 : ℤ)), ((2, 5, 0, 3), (-997723053693156412741151982949183924494822124109299072770899645250 : ℤ)), ((2, 5, 1, 2), (35920677861244615340170710847323381401535819315476737434023437500 : ℤ)), ((2, 5, 2, 1), (66462140622779412837862997194213729909318022496131487845917875000 : ℤ)),
    ((2, 7, 0, 1), (-6682536016722738321401579895730892501039079918827834991609375000 : ℤ)), ((2, 7, 1, 0), (-110883416450459695020707729757520727229458521867370588633850000000 : ℤ)), ((3, 0, 0, 7), (2198188475287528504680111936454148770473584965752608498437500000 : ℤ)), ((3, 0, 1, 6), (-1538731932701269953276078355517904139331509476026825948906250000 : ℤ)),
    ((3, 2, 0, 5), (1348165236549757249997295073118229665246186270746551782566125000 : ℤ)), ((3, 2, 1, 4), (2426621111491725933670384839559040302362843202296065707453050000 : ℤ)), ((3, 2, 2, 3), (72397283945661004989904136400183702999406006943780041834589062500 : ℤ)), ((3, 4, 0, 3), (811729182241575421874009077533561776101312932950602530577213611885 : ℤ)),
    ((3, 4, 1, 2), (-19523878569374398958651451869273572476627323790898936123041037500 : ℤ)), ((3, 4, 2, 1), (-53091717254018768298898739895686492402439982444584342523036140000 : ℤ)), ((3, 6, 0, 1), (2040236740876206196662526830816854763263219617028450200195312500 : ℤ)), ((3, 6, 1, 0), (87661279863649374298744722573068183217072895186706755402500000000 : ℤ)),
    ((4, 1, 0, 5), (-6524749946115201807916393361010985304371741883195879821350000000 : ℤ)), ((4, 1, 4, 1), (-3231337058672666901879764546587598692596169899656334492703125000 : ℤ)), ((4, 3, 0, 3), (1619782594532922117044148936243823717077116412356884336406346019062 : ℤ)), ((4, 5, 1, 0), (-69578461605790050403483449371576625888692093375414774248256250000 : ℤ)),
    ((5, 0, 0, 5), (-31524649896917355518626021077246086834685514392169527402984375000 : ℤ)), ((5, 0, 1, 4), (21220169477703379602573254075548266954548959087135891403621250000 : ℤ)), ((5, 0, 2, 3), (-95194630398685984035266762302469330805074753772996677965191187500 : ℤ)), ((5, 2, 0, 3), (-507088787494101035231719520699323188579849864404947777093354687500 : ℤ)),
    ((5, 4, 1, 0), (56956996410479081195408562881249596381814398275366899767504500000 : ℤ)), ((6, 1, 0, 3), (-6594565425862585514040335809362446311420754897257825495312500000 : ℤ)), ((6, 1, 1, 2), (4616195798103809859828235066553712417994528428080477846718750000 : ℤ)), ((6, 1, 2, 1), (19388022352036001411278587279525592155577019397938006956218750000 : ℤ)),
    ((6, 3, 0, 1), (-4044495709649271749991885219354688995738558812239655347698375000 : ℤ)), ((6, 3, 1, 0), (-47723904659393849905033051207578733723510612708712020585351200000 : ℤ)), ((7, 0, 0, 3), (242361659129056268683012627361978937788827553924951014099799651250 : ℤ)), ((7, 0, 1, 2), (-11300277942024795235652690122311348201552890568018555250195312500 : ℤ)),
    ((7, 0, 2, 1), (-27364808691159384849061777474530407213871564521661072675348750000 : ℤ)), ((7, 2, 0, 1), (35730935131708939933148002815970949376096075147869311927565625000 : ℤ)), ((7, 2, 1, 0), (54807899547367695186497704232492276556722631818845390499340000000 : ℤ)), ((8, 1, 0, 1), (-21754184421463941911793460445415292429405573211119459528359375000 : ℤ)),
    ((8, 1, 1, 0), (-53495483031444907682140234084356874906876065412814340869250000000 : ℤ)), ((9, 0, 0, 1), (11300277942024795235652690122311348201552890568018555250195312500 : ℤ)), ((9, 0, 1, 0), (42253922075004996284237123383278100860741166121476178685656250000 : ℤ))
  ]

lemma hb_d4_20 : allBound wsD4_20 = true := by decide
lemma hk_d4_20 : (22619359410708668313158351826113190848173189297594341448921875000 : ℤ) ≠ 0 := by decide
lemma hc_d4_20 : compileStrict wsD4_20 = [(packKey 4 1 1 1 1, (22619359410708668313158351826113190848173189297594341448921875000 : ℤ))] := by decide

def wsD4_21 : List (Exps × ℤ) :=
  [
    ((0, 1, 0, 9), (1381332831297649420120847231848985785133488125178874620378063265625 : ℤ)), ((0, 1, 1, 8), (-828543661073296125251249312715096743436424682655628360335093750000 : ℤ)), ((0, 1, 2, 7), (485568805449308972066001589433326408413778369261673329627587890625 : ℤ)), ((0, 1, 3, 6), (-271951006154423195220918129654052540299145310639721123465960937500 : ℤ)),
    ((0, 1, 4, 5), (145836869908758681618428744502238261838630666474669551721815078125 : ℤ)), ((0, 1, 5, 4), (-106034217787994120879792965113034843620312048885896123583283218750 : ℤ)), ((0, 1, 6, 3), (24643636827385307358722287120061446248732945866622126283203515625 : ℤ)), ((0, 1, 7, 2), (487126542152562959358593570846273811441357797760883117675781250 : ℤ)),
    ((0, 1, 8, 1), (96835403065774615579281121560467410933360612253614161286845703125 : ℤ)), ((0, 1, 9, 0), (-109724717268470133660915695393934742878892269130009459714246875000 : ℤ)), ((0, 3, 0, 7), (2819869660000194320925052336479180843345236525740102539464416406250 : ℤ)), ((0, 3, 1, 6), (-1642922231177063014775495218628390475682535525377771454130873562500 : ℤ)),
    ((0, 3, 2, 5), (917086909611709801146560725771027194582084339631297328617564965000 : ℤ)), ((0, 3, 3, 4), (-495935560173103345992514481541998290841481325826559387041554441650 : ℤ)), ((0, 3, 4, 3), (-795496352656822439333784654585679881177553843935067903332366584346 : ℤ)), ((0, 3, 5, 2), (971798945569583587415135460422169963075670630049959135443044062500 : ℤ)),
    ((0, 3, 7, 0), (-332798074588906155994694181812637340565272183047346698962923612500 : ℤ)), ((0, 5, 0, 5), (-25175315660716351174632514573512051224877405618753768903128906250 : ℤ)), ((0, 5, 1, 4), (21727239403789819940027158576256870762194423260957527768179921875 : ℤ)), ((0, 5, 2, 3), (3099583364799142364460931603264594834011031598222191831812973312500 : ℤ)),
    ((0, 5, 3, 2), (-24643636827385307358722287120061446248732945866622126283203515625 : ℤ)), ((0, 5, 4, 1), (-487126542152562959358593570846273811441357797760883117675781250 : ℤ)), ((0, 5, 5, 0), (-40287004539002944796385241995184433812927639009628307664541015625 : ℤ)), ((0, 7, 0, 3), (-4349144225385634627781527297911059468202847681050171357857654625000 : ℤ)),
    ((0, 7, 1, 2), (270203939204899844200986330833750210248214919498699703152949218750 : ℤ)), ((0, 7, 2, 1), (-80783426466816672546994113664689967314904247491408362317578125000 : ℤ)), ((0, 9, 0, 1), (-213978535919034943382710729506008231088212243648701356819677343750 : ℤ)), ((0, 9, 1, 0), (139290127960605388373490309938251328440546564712081561988792000000 : ℤ)),
    ((1, 0, 0, 9), (-6731438144202809258724847021529781155681111989409842135546875000 : ℤ)), ((1, 0, 1, 8), (3658343604749764722786620443675092143356751710417846018066406250 : ℤ)), ((1, 0, 2, 7), (-1895341763782606904873151075762462916018506510174244116210937500 : ℤ)), ((1, 0, 3, 6), (924995955915542238108558402590022565766783462324529432128906250 : ℤ)),
    ((1, 0, 4, 5), (-414786265051192154445109053104842654785201404457671928281250000 : ℤ)), ((1, 0, 5, 4), (1668926340057126931489408325723779557370065054774983667597656250 : ℤ)), ((1, 0, 6, 3), (-2299959823158920098310345590433830263919116714896244808593750000 : ℤ)), ((1, 0, 7, 2), (2045931477040764429306092997554350008053702750595709094238281250 : ℤ)),
    ((1, 0, 8, 1), (-1548172053922672483435254785183549730662960016660968305664062500 : ℤ)), ((1, 0, 9, 0), (1069668936281778438156142986337175787817905273414030632519531250 : ℤ)), ((1, 2, 0, 7), (-1980034486895037588595869659461066657246147516796779495834368750000 : ℤ)), ((1, 2, 1, 6), (1188020692137022553157521795676639994347688510078067697500621250000 : ℤ)),
    ((1, 2, 2, 5), (-665291587596732629768212205578918396834705565643717910600347900000 : ℤ)), ((1, 2, 3, 4), (469450542955660381926507410898485724969023877474741280177207443750 : ℤ)), ((1, 2, 4, 3), (-308901874471900636402994122020562557227916523033719548651255859375 : ℤ)), ((1, 2, 7, 0), (237604138427404510631504359135327998869537702015613539500124250000 : ℤ)),
    ((1, 4, 0, 5), (15148223345367398644616496804646307005019639600243224531690781250 : ℤ)), ((1, 4, 1, 4), (-14716858372319880955750516363616185248508849057407247557684571875 : ℤ)), ((1, 4, 2, 3), (-2532708832008549386686310460832367273852390090057208142403329254375 : ℤ)), ((1, 4, 3, 2), (21160646899635442200988790298938380901719497870941835039609703125 : ℤ)),
    ((1, 4, 5, 0), (34150718223547008125650654232991634348991808771419972099347265625 : ℤ)), ((1, 6, 0, 3), (3721818684260696302213783144751277525405688985710163620909200487500 : ℤ)), ((1, 6, 1, 2), (-192130412376982625505003327719035683849556417330463366260253906250 : ℤ)), ((1, 6, 2, 1), (67858078232126004939475055478339572544519567892783024346765625000 : ℤ)),
    ((1, 8, 0, 1), (181229032363516418596791693527190105307860741224934005226632812500 : ℤ)), ((1, 8, 1, 0), (-116568064191638871131107368076814673445413694682976482112671250000 : ℤ)), ((2, 3, 0, 5), (2278791930306293995435088294223434921986650120413662639489712064750 : ℤ)), ((2, 3, 1, 4), (-1216519747362240841931645420065051144882845929310298296009394721385 : ℤ)),
    ((2, 3, 2, 3), (350194942301281730088532215834619780619559282957578800119611577064 : ℤ)), ((2, 3, 3, 2), (-594010346068511276578760897838319997173844255039033848750310625000 : ℤ)), ((2, 3, 5, 0), (-845456473474878074738066497874849669996684556364751146557656773125 : ℤ)), ((2, 5, 0, 3), (-3123030412066053601102557673686391898185068370547908528816072159500 : ℤ)),
    ((2, 5, 1, 2), (159081448497613500494288677750713118224630126343548988735253906250 : ℤ)), ((2, 5, 2, 1), (-55385117185649510698219164328511441591098352080109573204931562500 : ℤ)), ((2, 7, 0, 1), (-30654084502810118642098226285719368176263102642978810052789062500 : ℤ)), ((2, 7, 1, 0), (93829025247522781378404745737552949228347920074983637439015625000 : ℤ)),
    ((3, 0, 0, 7), (10990942376437642523400559682270743852367924828763042492187500000 : ℤ)), ((3, 0, 1, 6), (-7693659663506349766380391777589520696657547380134129744531250000 : ℤ)), ((3, 0, 2, 5), (5385561764454444836466274244312664487660283166093890821171875000 : ℤ)), ((3, 2, 0, 5), (9254111562804725544848722364854402825236896593863281958401250000 : ℤ)),
    ((3, 2, 1, 4), (-7907734924139893219598913488966049892665717731707842920456850000 : ℤ)), ((3, 2, 2, 3), (269394783392468836567736342227980186866391895582995253420277343750 : ℤ)), ((3, 4, 0, 3), (2551014632550323419724491160938832829130766890378624014966989104230 : ℤ)), ((3, 4, 1, 2), (-57191915714541545955124388019308673741063561342132325060257843750 : ℤ)),
    ((3, 4, 2, 1), (44243097711682306915748949913072077002033318703820285435863450000 : ℤ)), ((3, 6, 0, 1), (9223948427780574973476211464279331493313766169245360599316406250 : ℤ)), ((3, 6, 1, 0), (-74148934967827004437109014231167397331018502707202950071875000000 : ℤ)), ((4, 1, 0, 5), (8249264501384522323889056394033808459060796530408023240226562500 : ℤ)),
    ((4, 1, 5, 0), (-22619359410708668313158351826113190848173189297594341448921875000 : ℤ)), ((4, 3, 0, 3), (5383443179236925567271386293478294074160669467813463430041716084491 : ℤ)), ((4, 5, 1, 0), (59357081260165057595828518062222165536475954447645655199718750000 : ℤ)), ((5, 0, 0, 5), (65834085848018628710911429343447635803897791650584484349648437500 : ℤ)),
    ((5, 0, 1, 4), (-39896216502987738466299024542498841095434545175149304640475000000 : ℤ)), ((5, 0, 2, 3), (-712749796907416248471699675750371426283504654603879930530878593750 : ℤ)), ((5, 2, 0, 3), (-1616368700354813019406418053367881121198351373497971520521664062500 : ℤ)), ((5, 4, 1, 0), (-48599530664378857941993872626236501448487515455540585015003750000 : ℤ)),
    ((6, 1, 0, 3), (-32972827129312927570201679046812231557103774486289127476562500000 : ℤ)), ((6, 1, 1, 2), (23080978990519049299141175332768562089972642140402389233593750000 : ℤ)), ((6, 1, 2, 1), (-16156685293363334509398822732937993462980849498281672463515625000 : ℤ)), ((6, 3, 0, 1), (-27762334688414176634546167094563208475710689781589845875203750000 : ℤ)),
    ((6, 3, 1, 0), (40881486734538703717254434469713764657995834587166075356282250000 : ℤ)), ((7, 0, 0, 3), (763205352354603790482871874119862494542339953991340797025590097500 : ℤ)), ((7, 0, 1, 2), (-51615213327121696129081337162532029392752793260608324242675781250 : ℤ)), ((7, 0, 2, 1), (22804007242632820707551481228775339344892970434717560562790625000 : ℤ)),
    ((7, 2, 0, 1), (165254825545799246858862986157249377747472400508568398450264062500 : ℤ)), ((7, 2, 1, 0), (-46674462400921319207509721883770800207937501557833053768981250000 : ℤ)), ((8, 1, 0, 1), (-100562145783875879076341351632714946633808277962063418267851562500 : ℤ)), ((8, 1, 1, 0), (45436926421459595822829361652522475678776727762329901070078125000 : ℤ)),
    ((9, 0, 0, 1), (51615213327121696129081337162532029392752793260608324242675781250 : ℤ)), ((9, 0, 1, 0), (-35408183184230725092572306689076515366415833239535214090390625000 : ℤ))
  ]

lemma hb_d4_21 : allBound wsD4_21 = true := by decide
lemma hk_d4_21 : (158335515874960678192108462782792335937212325083160390142453125000 : ℤ) ≠ 0 := by decide
lemma hc_d4_21 : compileStrict wsD4_21 = [(packKey 4 1 1 2 0, (158335515874960678192108462782792335937212325083160390142453125000 : ℤ))] := by decide

def wsD4_22 : List (Exps × ℤ) :=
  [
    ((0, 0, 0, 10), (120927559480342127293559471653883580000000000 : ℤ)), ((0, 0, 1, 9), (-86436210555625793409759389939718075000000000 : ℤ)), ((0, 0, 2, 8), (48374551660420299417198551356871250000000000 : ℤ)), ((0, 0, 3, 7), (-25920279693438369537348659555296875000000000 : ℤ)),
    ((0, 0, 4, 6), (13202094471102550680334013882655000000000000 : ℤ)), ((0, 0, 5, 5), (-6297133656158477019204550141181175000000000 : ℤ)), ((0, 0, 6, 4), (445893760952173384000605140563080000000000 : ℤ)), ((0, 0, 7, 3), (-17542038545954972044237938068265375000000000 : ℤ)),
    ((0, 0, 8, 2), (19698932358344043908718532024668750000000000 : ℤ)), ((0, 0, 9, 1), (-16440588714884270426737464496584375000000000 : ℤ)), ((0, 0, 10, 0), (12035041017011521808488211060293500000000000 : ℤ)), ((0, 2, 0, 8), (-1094407971287059242193999211818355534472656250 : ℤ)),
    ((0, 2, 1, 7), (1061279105807621951306804869149690309375000000 : ℤ)), ((0, 2, 2, 6), (-618994725224881562160138105880431494531250000 : ℤ)), ((0, 2, 3, 5), (346637046125933674809677339293041636937500000 : ℤ)), ((0, 2, 4, 4), (-199025897984486942812995830678227115435306250 : ℤ)),
    ((0, 2, 5, 3), (-37757534071018653514389200543538335156250000 : ℤ)), ((0, 2, 6, 2), (373227503453523781102841127797036512968750000 : ℤ)), ((0, 2, 8, 0), (-123798945044976312432027621176086298906250000 : ℤ)), ((0, 4, 0, 6), (132011406818765673010880517093693610490679660000 : ℤ)),
    ((0, 4, 1, 5), (-70748161612544009203658801278899219604014129600 : ℤ)), ((0, 4, 2, 4), (36392314580645681593209805659923022044209623776 : ℤ)), ((0, 4, 3, 3), (8331914452082241629590458732414262562001684375 : ℤ)), ((0, 4, 4, 2), (295365540812107002239012882677781795820000000 : ℤ)),
    ((0, 4, 5, 1), (-47673393089471515236514324403538034061497200000 : ℤ)), ((0, 4, 6, 0), (53644220272022571880184288792189027276134332000 : ℤ)), ((0, 6, 0, 4), (-7114773304733597217128967676209117092061000000 : ℤ)), ((0, 6, 1, 3), (908483391079663686859102646722587521378906250 : ℤ)),
    ((0, 8, 0, 2), (-3992189959092491796244657271651042001269531250 : ℤ)), ((0, 8, 1, 1), (-1452911363964161751395447832363187500000000 : ℤ)), ((0, 8, 2, 0), (7664476135698672784297021424557754544960000000 : ℤ)), ((0, 10, 0, 0), (7397667180809251400380580910747000000000000 : ℤ)),
    ((1, 1, 0, 8), (48309302851808378233898640426075984375000000 : ℤ)), ((1, 1, 1, 7), (-28985581711085026940339184255645590625000000 : ℤ)), ((1, 1, 2, 6), (17086237640218542196410466508591085000000000 : ℤ)), ((1, 1, 8, 0), (17086237640218542196410466508591085000000000 : ℤ)),
    ((1, 3, 0, 6), (1201833100904712818469187509249798920402109375 : ℤ)), ((1, 3, 1, 5), (-701356237807383932458944962421085024225181250 : ℤ)), ((1, 3, 2, 4), (124161851254714320692795860035640428634713375 : ℤ)), ((1, 3, 3, 3), (139560354538660158511439094800285963654296875 : ℤ)),
    ((1, 3, 4, 2), (-1525556932162369838965220223981346875000000 : ℤ)), ((1, 3, 6, 0), (98718113677218793112837715643971640080421875 : ℤ)), ((1, 5, 0, 4), (5947704696740654511498363264281225334531240000 : ℤ)), ((1, 5, 1, 3), (-763126048506917496961646223246973517958281250 : ℤ)),
    ((1, 7, 0, 2), (4004659592494419035371272860342653706250000000 : ℤ)), ((1, 7, 1, 1), (1525556932162369838965220223981346875000000 : ℤ)), ((1, 7, 2, 0), (-7128378343499175804342446627384200662000000000 : ℤ)), ((1, 9, 0, 0), (-6214040431879771176319687965027480000000000 : ℤ)),
    ((2, 0, 0, 8), (-2512651094383519106429230698482473416000000000 : ℤ)), ((2, 0, 1, 7), (1341770695199627846158676427851203200000000000 : ℤ)), ((2, 0, 2, 6), (-680567336059929708558358906493679720000000000 : ℤ)), ((2, 0, 3, 5), (322756430399358807249327267777686083200000000 : ℤ)),
    ((2, 0, 4, 4), (-138320068279488442873119216044860156992000000 : ℤ)), ((2, 0, 5, 3), (979708764827142801625391449484728694400000000 : ℤ)), ((2, 0, 6, 2), (-1062363798777928279357498396544911080000000000 : ℤ)), ((2, 0, 7, 1), (875419166913027443150305797881618400000000000 : ℤ)),
    ((2, 0, 8, 0), (-636352991162287337797560808659660744000000000 : ℤ)), ((2, 2, 0, 6), (-42715594100546355491026166271477712500000000 : ℤ)), ((2, 2, 1, 5), (23920732696305959074974653112027519000000000 : ℤ)), ((2, 2, 2, 4), (-472971662063451162697404544029573603962400000 : ℤ)),
    ((2, 2, 3, 3), (14492790855542513470169592127822795312500000 : ℤ)), ((2, 2, 4, 2), (-9611008672622929985480887411082485312500000 : ℤ)), ((2, 2, 6, 0), (-8543118820109271098205233254295542500000000 : ℤ)), ((2, 4, 0, 4), (-4908759472168827223135921380782773148205021600 : ℤ)),
    ((2, 4, 1, 3), (650520226580115112285224617801978036055778125 : ℤ)), ((2, 4, 2, 2), (-195941752965428560325078289896945738880000000 : ℤ)), ((2, 4, 3, 1), (212472759755585655871499679308982216000000000 : ℤ)), ((2, 4, 4, 0), (-175083833382605488630061159576323680000000000 : ℤ)),
    ((2, 6, 0, 2), (-3506492608575207074861558684821125792187500000 : ℤ)), ((2, 6, 2, 0), (6243311233735855318568384462239182459000000000 : ℤ)), ((2, 8, 0, 0), (-37422711331954308414199009589388300000000000 : ℤ)), ((3, 1, 0, 6), (-478414653926119181499493062240550380000000000 : ℤ)),
    ((3, 1, 1, 5), (287048792355671508899695837344330228000000000 : ℤ)), ((3, 3, 0, 4), (3850545582451883206011070913198081624098719750 : ℤ)), ((3, 3, 1, 3), (-6967522803309333298680968647028201743207031250 : ℤ)), ((3, 5, 0, 2), (2945453791203173942883709295249745665437500000 : ℤ)),
    ((3, 5, 2, 0), (-5244381436338118467597442948280913265560000000 : ℤ)), ((3, 7, 0, 0), (35691003281080570809772190916394920000000000 : ℤ)), ((4, 2, 0, 4), (2692902063825281841482731342899213670649400000 : ℤ)), ((4, 2, 2, 2), (6407339115081953323653924940721656875000000 : ℤ)),
    ((4, 2, 3, 1), (-143524396177835754449847918672165114000000000 : ℤ)), ((4, 4, 0, 2), (-2422221000260755244262266687247815593551328125 : ℤ)), ((4, 4, 2, 0), (4280414181849302406410484387311183493890400000 : ℤ)), ((4, 6, 0, 0), (-2959066872323700560152232364298800000000000 : ℤ)),
    ((5, 3, 0, 2), (176201825664753716400482935869845564062500000 : ℤ)), ((5, 3, 2, 0), (6902183895122906655329486307556868442336000000 : ℤ)), ((6, 0, 0, 4), (-1518637591731943279725692147689933494412200000 : ℤ)), ((6, 0, 1, 3), (181696678215932737371820529344517504275781250 : ℤ)),
    ((6, 2, 0, 2), (1396799927087865824556555637077321198750000000 : ℤ)), ((6, 2, 2, 0), (-2411209855787640674757445033692373915200000000 : ℤ)), ((6, 4, 0, 0), (1479533436161850280076116182149400000000000 : ℤ)), ((7, 3, 0, 0), (-42559257622389517418450228613087480000000000 : ℤ)),
    ((8, 0, 0, 2), (-701298521715041414972311736964225158437500000 : ℤ)), ((8, 0, 2, 0), (1248662246747171063713676892447836491800000000 : ℤ)), ((8, 2, 0, 0), (16835033517831719699131757289600900000000000 : ℤ)), ((9, 1, 0, 0), (24856161727519084705278751860109920000000000 : ℤ)),
    ((10, 0, 0, 0), (-14795334361618502800761161821494000000000000 : ℤ))
  ]

lemma hb_d4_22 : allBound wsD4_22 = true := by decide
lemma hk_d4_22 : (1004670773244850281148935430705155798000000000 : ℤ) ≠ 0 := by decide
lemma hc_d4_22 : compileStrict wsD4_22 = [(packKey 4 1 2 0 1, (1004670773244850281148935430705155798000000000 : ℤ))] := by decide

def wsD4_23 : List (Exps × ℤ) :=
  [
    ((0, 2, 0, 8), (-403675781250000 : ℤ)), ((0, 2, 1, 7), (226058437500000 : ℤ)), ((0, 2, 2, 6), (-126592725000000 : ℤ)), ((0, 2, 3, 5), (67877813500000 : ℤ)),
    ((0, 2, 4, 4), (-34602038756250 : ℤ)), ((0, 2, 7, 1), (45211687500000 : ℤ)), ((0, 2, 8, 0), (-51153795000000 : ℤ)), ((0, 4, 0, 6), (-1945102903380000 : ℤ)),
    ((0, 4, 1, 5), (1042945652002800 : ℤ)), ((0, 4, 2, 4), (-536714583663168 : ℤ)), ((0, 4, 3, 3), (549578645188125 : ℤ)), ((0, 4, 5, 1), (694679608350000 : ℤ)),
    ((0, 4, 6, 0), (-785980356876000 : ℤ)), ((0, 6, 0, 4), (275834352500000 : ℤ)), ((0, 6, 1, 3), (4028603906250 : ℤ)), ((0, 8, 0, 2), (16147031250000 : ℤ)),
    ((0, 8, 2, 0), (-110870130000000 : ℤ)), ((1, 3, 0, 6), (26857359375 : ℤ)), ((1, 3, 1, 5), (-15040121250 : ℤ)), ((1, 3, 2, 4), (4141015429775 : ℤ)),
    ((1, 3, 3, 3), (-169543828125000 : ℤ)), ((1, 3, 6, 0), (5371471875 : ℤ)), ((1, 5, 0, 4), (-231700856100000 : ℤ)), ((1, 5, 1, 3), (-3384027281250 : ℤ)),
    ((1, 7, 2, 0), (103341000000000 : ℤ)), ((2, 2, 0, 6), (45211687500000 : ℤ)), ((2, 2, 1, 5), (-25318545000000 : ℤ)), ((2, 2, 2, 4), (20382289900000 : ℤ)),
    ((2, 2, 6, 0), (9042337500000 : ℤ)), ((2, 4, 0, 4), (189112032074000 : ℤ)), ((2, 4, 1, 3), (2762010838125 : ℤ)), ((2, 6, 2, 0), (-90423375000000 : ℤ)),
    ((3, 3, 0, 4), (1359191444952600 : ℤ)), ((3, 3, 1, 3), (339087656250000 : ℤ)), ((3, 5, 2, 0), (75955635000000 : ℤ)), ((4, 2, 0, 4), (-122293739400000 : ℤ)),
    ((4, 2, 4, 0), (-18084675000000 : ℤ)), ((4, 4, 0, 2), (-80572078125 : ℤ)), ((4, 4, 2, 0), (-61994265900000 : ℤ)), ((5, 3, 0, 2), (-135635062500000 : ℤ)),
    ((5, 3, 2, 0), (-102100908000000 : ℤ)), ((6, 0, 0, 4), (55166870500000 : ℤ)), ((6, 0, 1, 3), (805720781250 : ℤ)), ((6, 2, 2, 0), (36169350000000 : ℤ)),
    ((8, 0, 2, 0), (-18084675000000 : ℤ))
  ]

lemma hb_d4_23 : allBound wsD4_23 = true := by decide
lemma hk_d4_23 : (126592725000000 : ℤ) ≠ 0 := by decide
lemma hc_d4_23 : compileStrict wsD4_23 = [(packKey 4 1 2 1 0, (126592725000000 : ℤ))] := by decide

def wsD4_24 : List (Exps × ℤ) :=
  [
    ((0, 1, 0, 9), (-24729345047369207972624625000 : ℤ)), ((0, 1, 1, 8), (14638957961346893232778125000 : ℤ)), ((0, 1, 2, 7), (-8616655222850387068945312500 : ℤ)), ((0, 1, 3, 6), (4825326924796216758609375000 : ℤ)),
    ((0, 1, 4, 5), (-2587294341581209557235312500 : ℤ)), ((0, 1, 5, 4), (1874380558258783228350375000 : ℤ)), ((0, 1, 6, 3), (719639798783549691462187500 : ℤ)), ((0, 1, 8, 1), (-1723331044570077413789062500 : ℤ)),
    ((0, 1, 9, 0), (1949825981856430445315625000 : ℤ)), ((0, 3, 0, 7), (886449602512576131199965703125 : ℤ)), ((0, 3, 1, 6), (-496289827635735258970211390625 : ℤ)), ((0, 3, 2, 5), (265614583603779016397149156875 : ℤ)),
    ((0, 3, 3, 4), (-134900973255181609272740588475 : ℤ)), ((0, 3, 4, 3), (16196666111614137809720412009 : ℤ)), ((0, 3, 5, 2), (-15622991037105034855864921875 : ℤ)), ((0, 3, 6, 1), (184615798083490929392538328125 : ℤ)),
    ((0, 3, 7, 0), (-204752707289141868589778465625 : ℤ)), ((0, 5, 0, 5), (-4825326924796216758609375000 : ℤ)), ((0, 5, 1, 4), (2587294341581209557235312500 : ℤ)), ((0, 5, 2, 3), (526685102874339478373680425000 : ℤ)),
    ((0, 5, 3, 2), (-719639798783549691462187500 : ℤ)), ((0, 5, 5, 0), (1723331044570077413789062500 : ℤ)), ((0, 7, 0, 3), (51939020837896147081400062500 : ℤ)), ((0, 7, 1, 2), (-662254960554565855640625000 : ℤ)),
    ((0, 9, 0, 1), (719639798783549691462187500 : ℤ)), ((1, 2, 0, 7), (34717757860233410790810937500 : ℤ)), ((1, 2, 1, 6), (-20830654716140046474486562500 : ℤ)), ((1, 2, 2, 5), (11665166641038426025712475000 : ℤ)),
    ((1, 2, 3, 4), (-11400374851138894624598306250 : ℤ)), ((1, 2, 4, 3), (4172206251493764890535937500 : ℤ)), ((1, 2, 7, 0), (-4166130943228009294897312500 : ℤ)), ((1, 4, 0, 5), (4053274616828822077231875000 : ℤ)),
    ((1, 4, 1, 4), (-2173327246928216028077662500 : ℤ)), ((1, 4, 2, 3), (-429830736808907107986224157000 : ℤ)), ((1, 4, 3, 2), (604497430978181740828237500 : ℤ)), ((1, 4, 5, 0), (-1447598077438865027582812500 : ℤ)),
    ((1, 6, 0, 3), (-43924434846374186029592887500 : ℤ)), ((1, 8, 0, 1), (-1983871877727623473760625000 : ℤ)), ((2, 3, 0, 5), (-211442942422579030526863426500 : ℤ)), ((2, 3, 1, 4), (113373691984678089701546770590 : ℤ)),
    ((2, 3, 2, 3), (-10356274100706381302719858006 : ℤ)), ((2, 3, 3, 2), (10415327358070023237243281250 : ℤ)), ((2, 3, 5, 0), (75515336579492510902451223750 : ℤ)), ((2, 5, 0, 3), (36896525270954316264858025500 : ℤ)),
    ((3, 2, 0, 5), (1388710314409336431632437500 : ℤ)), ((3, 2, 1, 4), (9068498121716954499221212500 : ℤ)), ((3, 2, 2, 3), (-2781470834329176593690625000 : ℤ)), ((3, 4, 0, 3), (-30114592530674141941888883670 : ℤ)),
    ((3, 4, 1, 2), (12584749605538053847667400000 : ℤ)), ((4, 3, 0, 3), (-62876660233930769008793351964 : ℤ)), ((4, 3, 3, 0), (-73846319233396371757015331250 : ℤ)), ((5, 0, 2, 3), (-125847496055380538476674000000 : ℤ)),
    ((5, 2, 0, 3), (16688825005975059562143750000 : ℤ)), ((6, 3, 0, 1), (-4166130943228009294897312500 : ℤ)), ((7, 0, 0, 3), (-8784886969274837205918577500 : ℤ))
  ]

lemma hb_d4_24 : allBound wsD4_24 = true := by decide
lemma hk_d4_24 : (516924234633774602299107318750 : ℤ) ≠ 0 := by decide
lemma hc_d4_24 : compileStrict wsD4_24 = [(packKey 4 1 3 0 0, (516924234633774602299107318750 : ℤ))] := by decide

def wsD4_25 : List (Exps × ℤ) :=
  [
    ((0, 1, 0, 9), (3227240479100500563140570847194332953971795407354785144140625 : ℤ)), ((0, 1, 1, 8), (-6261520965480899977404977124312527707015972178168575845000000 : ℤ)), ((0, 1, 2, 7), (4394341483056521079402602523486141029585116222070293212890625 : ℤ)), ((0, 1, 3, 6), (-2460827093661509617425891608093520001321668102580006289062500 : ℤ)),
    ((0, 1, 4, 5), (1319469588761991474010522235423764191633667645848042711328125 : ℤ)), ((0, 1, 5, 4), (-750291548516854521293175373917434121717783491028734173593750 : ℤ)), ((0, 1, 6, 3), (-21420926909511117374598623521745122325146736282567582588484375 : ℤ)), ((0, 1, 7, 2), (-62052752132805593487075880784628689954726690368652343750 : ℤ)),
    ((0, 1, 8, 1), (878903755326808676219655976629105136596997373951412158203125 : ℤ)), ((0, 1, 9, 0), (-994396136061906881324981736835335506891189262773951062500000 : ℤ)), ((0, 3, 0, 7), (-80684730778436874488701789311666469423007263299441528581156250 : ℤ)), ((0, 3, 1, 6), (47693186121797563882174607128186378255888984050038467727268750 : ℤ)),
    ((0, 3, 2, 5), (-26728700653975986040061461036524610545155584527701899606589250 : ℤ)), ((0, 3, 3, 4), (14235685669580466054125989969058471570574574160143853974578480 : ℤ)), ((0, 3, 4, 3), (-35846368945644619893534470695130779819769634718043004500257908 : ℤ)), ((0, 3, 5, 2), (2184796534151243098189172940069802730503375130777634171093750 : ℤ)),
    ((0, 3, 7, 0), (9509328044689012396372519933151220334238149010464325432141250 : ℤ)), ((0, 5, 0, 5), (2460577299919120931397104229428431037078314345361580996093750 : ℤ)), ((0, 5, 1, 4), (-1315749746196940388356771628357229549819846557631838414453125 : ℤ)), ((0, 5, 2, 3), (-160141295906368169288074399265551188954837780128335412515492500 : ℤ)),
    ((0, 5, 3, 2), (34346275144201784982117681708095517095531415881192920559296875 : ℤ)), ((0, 5, 4, 1), (62052752132805593487075880784628689954726690368652343750 : ℤ)), ((0, 5, 5, 0), (-878903755326808676219655976629105136596997373951412158203125 : ℤ)), ((0, 7, 0, 3), (628999810737297701790027355177238518947901249421577429961875000 : ℤ)),
    ((0, 7, 1, 2), (-37578764524662540134212682216481231464772706730913743041406250 : ℤ)), ((0, 9, 0, 1), (4406164051214487010719085567104760094625692857541903167593750 : ℤ)), ((0, 9, 1, 0), (43285533896448978278976995998932120314246095792391286093750 : ℤ)), ((1, 0, 0, 9), (1104770737176947459240029525514963326159494911258789062500 : ℤ)),
    ((1, 0, 1, 8), (-616409412753437242197931873616934323499767744128417968750 : ℤ)), ((1, 0, 2, 7), (329166308894430317140126411358743630630381772460937500000 : ℤ)), ((1, 0, 3, 6), (-166958362383695411422089543741200399965690319274902343750 : ℤ)), ((1, 0, 4, 5), (79179358475028131209902984751415051846291884702148437500 : ℤ)),
    ((1, 0, 5, 4), (-33933000984800024647269910071677087243241092647558593750 : ℤ)), ((1, 0, 6, 3), (240344433712418077360731568001093857942322463764648437500 : ℤ)), ((1, 0, 7, 2), (-260621558957783492645718699295440497809852099548339843750 : ℤ)), ((1, 0, 8, 1), (214759866897619487797007396154857582017420411376953125000 : ℤ)),
    ((1, 0, 9, 0), (-156111596418235932454136420836730126860235441784667968750 : ℤ)), ((1, 2, 0, 7), (-4855103409224984662642606533488450512229722512839187046875000 : ℤ)), ((1, 2, 1, 6), (2913062045534990797585563920093070307337833507703512228125000 : ℤ)), ((1, 2, 2, 5), (-1631314745499594846647915795252119372109186764313966847750000 : ℤ)),
    ((1, 2, 3, 4), (33726880168158552258330552175752707086818783505359978877106250 : ℤ)), ((1, 2, 4, 3), (21454887641950269552002301990496884949417448300674227122578125 : ℤ)), ((1, 2, 7, 0), (582612409106998159517112784018614061467566701540702445625000 : ℤ)), ((1, 4, 0, 5), (-2067061367003191339555464532889808561030208068103350302343750 : ℤ)),
    ((1, 4, 1, 4), (1105302518613855184537583106438992411262440447372284893140625 : ℤ)), ((1, 4, 2, 3), (130687943265690291928431054012295760127087003869844939198801825 : ℤ)), ((1, 4, 3, 2), (-28543172803475987877939109110010253751151675909489441009715625 : ℤ)), ((1, 4, 5, 0), (738236202501139764126951618889217343225074310036910822265625 : ℤ)),
    ((1, 6, 0, 3), (-556000586326077291314967608341486969374714920400234298482975000 : ℤ)), ((1, 6, 1, 2), (30755904123346247613362513710476410468378657729154622005468750 : ℤ)), ((1, 8, 0, 1), (281907179204326473567293088118714862072130416269382339062500 : ℤ)), ((1, 8, 1, 0), (-63391598092681086437470012228498260273588155198046253125000 : ℤ)),
    ((2, 3, 0, 5), (689280386723923651470375632494060823037512406855973559334003750 : ℤ)), ((2, 3, 1, 4), (-369568428937064714343067662617653705110687870320763025126890225 : ℤ)), ((2, 3, 2, 3), (48950088980204773351831435274408007523028227632637831694442772 : ℤ)), ((2, 3, 3, 2), (-1456531022767495398792781960046535153668916753851756114062500 : ℤ)),
    ((2, 3, 5, 0), (-246391385534644342661316451370095708819016075230851532040559375 : ℤ)), ((2, 5, 0, 3), (467040492513904924704572791006849054274760533136196810725699000 : ℤ)), ((2, 5, 1, 2), (-25834959463610847995224511516800184793438072492489882484593750 : ℤ)), ((2, 7, 0, 1), (-2115396149828758255216543895210542906572961129750195312500 : ℤ)),
    ((2, 7, 1, 0), (60502650870677434988083088995814797965543712697490468750000 : ℤ)), ((3, 2, 0, 5), (-188731900572312000724155806282656964999222540779400844375000 : ℤ)), ((3, 2, 1, 4), (110525669969044935325932770667538739956717731057218883600000 : ℤ)), ((3, 2, 2, 3), (-34807194510197678110243210467315530278530737353219232752031250 : ℤ)),
    ((3, 4, 0, 3), (-381193913417478470661597655359707596330880410829062153985240160 : ℤ)), ((3, 4, 1, 2), (17255495784707020130164968575153374086726227652933072021018750 : ℤ)), ((3, 4, 2, 1), (307746386540253990655215671103580827866301895205365189781250 : ℤ)), ((3, 6, 0, 1), (749381227166058086362135995266892730061271655275878906250 : ℤ)),
    ((3, 6, 1, 0), (-53699371039701322164445125211272327563144762608291992187500 : ℤ)), ((4, 1, 0, 5), (-3425171795633662826732536255699877704866718979047617187500 : ℤ)), ((4, 3, 0, 3), (-386409661863305033883072301998467118348567439760680564638922257 : ℤ)), ((4, 5, 1, 0), (45541501117839720075203860800288400492066751446958320312500 : ℤ)),
    ((5, 0, 0, 5), (2098267436064962641813980786747299644171560634772460937500 : ℤ)), ((5, 0, 1, 4), (-885676801202639441369192158698724241385973384810546875000 : ℤ)), ((5, 0, 2, 3), (38307520822591672335563708247492529303941800861753368259306250 : ℤ)), ((5, 0, 3, 2), (-3077463865402539906552156711035808278663018952053651897812500 : ℤ)),
    ((5, 2, 0, 3), (208843167061186068661459262803893181671184424119315396512187500 : ℤ)), ((5, 4, 1, 0), (-37428890343614543823922315209628035770087547880989461718750 : ℤ)), ((6, 3, 0, 1), (566195701716936002172467418847970894997667622338202533125000 : ℤ)), ((6, 3, 1, 0), (-72537084728253223806082787238762593357296623311316161250000 : ℤ)),
    ((7, 0, 0, 3), (-111200117265215458262993521668297393874942984080046859696595000 : ℤ)), ((7, 0, 1, 2), (6151180824669249522672502742095282093675731545830924401093750 : ℤ)), ((7, 2, 0, 1), (10275515386900988480197608767099633114600156937142851562500 : ℤ)), ((7, 2, 1, 0), (28771443083322767744553304547878972720880439423999984375000 : ℤ)),
    ((8, 1, 0, 1), (-6294802308194887925441942360241898932514681904317382812500 : ℤ)), ((8, 1, 1, 0), (-4340294444906094570699556228196453390251508559930468750000 : ℤ)), ((9, 0, 0, 1), (3746906135830290431810679976334463650306358276379394531250 : ℤ)), ((9, 0, 1, 0), (-8259705953708210392489278626142206432485233344555273437500 : ℤ))
  ]

lemma hb_d4_25 : allBound wsD4_25 = true := by decide
lemma hk_d4_25 : (21542247057817779345865096977250657950641132664375563284687500 : ℤ) ≠ 0 := by decide
lemma hc_d4_25 : compileStrict wsD4_25 = [(packKey 4 2 0 0 2, (21542247057817779345865096977250657950641132664375563284687500 : ℤ))] := by decide

def wsD4_26 : List (Exps × ℤ) :=
  [
    ((0, 1, 0, 9), (2767746460929377401296268051785529690219132902552879199372312500 : ℤ)), ((0, 1, 1, 8), (-1564956989045594798997860451372136497228332964344907842669062500 : ℤ)), ((0, 1, 2, 7), (3589888769673927485970224037591724783690178121746735385904687500 : ℤ)), ((0, 1, 3, 6), (-3235392328344555714526701770047186431203002145842286030507812500 : ℤ)),
    ((0, 1, 4, 5), (2395597644280696797728818698160112647119492474064787182439062500 : ℤ)), ((0, 1, 5, 4), (-1659810715805327131054040043087510188066422730757392981610937500 : ℤ)), ((0, 1, 6, 3), (883030434497797886010564699367966422512457477098343659743312500 : ℤ)), ((0, 1, 7, 2), (18375819259907344835750644634937308285047535964961713216017812500 : ℤ)),
    ((0, 1, 8, 1), (-9782490394583697266092037841017259777574842069914489046257812500 : ℤ)), ((0, 1, 9, 0), (4600975616032601908419235285663113412839608806586241879304687500 : ℤ)), ((0, 3, 0, 7), (7554506919536537920074734962394326402971835614073709304766125000 : ℤ)), ((0, 3, 1, 6), (-4565014401535146091038986596923300366328106954966751550309181250 : ℤ)),
    ((0, 3, 2, 5), (2588973820049126677717834152594887446187793005385123216298141500 : ℤ)), ((0, 3, 3, 4), (-212673977037263861476937167571711694454490221083865426351065990 : ℤ)), ((0, 3, 4, 3), (40511548224410570938860447959937770475048541057321767169320792609 : ℤ)), ((0, 3, 5, 2), (2500890795077375638013226372285719480930715439777158374149218750 : ℤ)),
    ((0, 3, 6, 1), (-488486327841673001040024874767588615660796659056135221875000000 : ℤ)), ((0, 3, 7, 0), (-633867835826073217613497390946038007173737585818415897561836250 : ℤ)), ((0, 5, 0, 5), (-30714972168906697508893101440164045372079739095517237617484375000 : ℤ)), ((0, 5, 1, 4), (16372139981756746780505307976423370186921040589760266501599843750 : ℤ)),
    ((0, 5, 2, 3), (94462772261736920562308292362685664111756074506088225421320322500 : ℤ)), ((0, 5, 3, 2), (-883030434497797886010564699367966422512457477098343659743312500 : ℤ)), ((0, 5, 4, 1), (624442645087936547302370898997772027417943045017533601076562500 : ℤ)), ((0, 5, 5, 0), (10590324659251863991561978977664159450723884544828572669433593750 : ℤ)),
    ((0, 7, 0, 3), (-359841845599714049161170049344715257674400137844955580967978000000 : ℤ)), ((0, 7, 1, 2), (6854733233668068943534345327714528555757750432001280300824375000 : ℤ)), ((0, 7, 3, 0), (488486327841673001040024874767588615660796659056135221875000000 : ℤ)), ((0, 9, 0, 1), (-1132218087791898336964467314048636259157006897378740690842625000 : ℤ)),
    ((0, 9, 1, 0), (-5918710735293908363760935861843114536107381319894785165937500000 : ℤ)), ((1, 0, 0, 9), (1939389489629092151127895549296061693819158426582478176427762500 : ℤ)), ((1, 0, 1, 8), (-1126562339110601893369686501829605213162026269894632136507125000 : ℤ)), ((1, 0, 2, 7), (615076994846363326607669490196348640805077107185211265339062500 : ℤ)),
    ((1, 0, 3, 6), (-320394905894065685076686741631333676828307056069437843281250000 : ℤ)), ((1, 0, 4, 5), (229285775912652473589473682771123511064281675639031129948437500 : ℤ)), ((1, 0, 5, 4), (-216770200497223878351294519469839683917584542062361903270250000 : ℤ)), ((1, 0, 6, 3), (236968725833606005190324262423454178484864059336740966573912500 : ℤ)),
    ((1, 0, 7, 2), (-360723168298466667354122593179323430338041859314206979629375000 : ℤ)), ((1, 0, 8, 1), (329142923711253618095318236998883116925610769616589098570312500 : ℤ)), ((1, 0, 9, 0), (106876799092671594123184799199977687473246550554320905953125000 : ℤ)), ((1, 2, 0, 7), (-2992981879003162606791483568105091947626851850571197583265625000 : ℤ)),
    ((1, 2, 1, 6), (1898371256248648894293295364564248777864878408744506946553125000 : ℤ)), ((1, 2, 2, 5), (-1097281946448160490877047145389710518700587675030853355601000000 : ℤ)), ((1, 2, 3, 4), (922843404174859716160435729047983558565442231177194086824650000 : ℤ)), ((1, 2, 4, 3), (-31988994248277188661071753267842626114221247863402041725271687500 : ℤ)),
    ((1, 2, 6, 1), (512910644233756651092026118505968046443836492008941982968750000 : ℤ)), ((1, 2, 7, 0), (86582454544725978234644148052296586176497686315220256185625000 : ℤ)), ((1, 4, 0, 5), (25092763635838686134287152768185477573580918480422092813707187500 : ℤ)), ((1, 4, 1, 4), (-13380480713270523918888498157826896830859400971125937004688056250 : ℤ)),
    ((1, 4, 2, 3), (-77081060094839675589803922052328218401290634780732051190127108400 : ℤ)), ((1, 4, 3, 2), (694351819811429023210809494984400959213491468895260480869600000 : ℤ)), ((1, 4, 5, 0), (-8961701298513816476531125988637670561993185171579318862038281250 : ℤ)), ((1, 6, 0, 3), (314706165646081784750296536233427222324859221227801082783623718750 : ℤ)),
    ((1, 6, 1, 2), (-1599403589118806526170660328108414826721797122600860595703125000 : ℤ)), ((1, 6, 3, 0), (-512910644233756651092026118505968046443836492008941982968750000 : ℤ)), ((1, 8, 0, 1), (699416483360904883155772654055710034789138821147646508262500000 : ℤ)), ((1, 8, 1, 0), (4715459747858396956390723878072171061865715342030257367187500000 : ℤ)),
    ((2, 1, 0, 7), (-2692780882227222418233137122156332243830141583046945410585937500 : ℤ)), ((2, 1, 1, 6), (1507957294047244554210556788407546056544879286506289429928125000 : ℤ)), ((2, 1, 2, 5), (-808552339570093984781469973212808028414063846002896141951937500 : ℤ)), ((2, 1, 3, 4), (412166787135939104711134716413499826633523903594513634441960000 : ℤ)),
    ((2, 1, 6, 1), (-538556176445444483646627424431266448766028316609389082117187500 : ℤ)), ((2, 1, 7, 0), (609337845349702901497327028785090039175277752506623075766875000 : ℤ)), ((2, 3, 0, 5), (6596891233804303036183577687497874250602472557199548720109765000 : ℤ)), ((2, 3, 1, 4), (-3708028431889297959799312200166223625727934787028856619011235900 : ℤ)),
    ((2, 3, 2, 3), (-31577520972052426588263195525101532687204194326215364980096778406 : ℤ)), ((2, 3, 3, 2), (-1667260530051583758675484248190479653953810293184772249432812500 : ℤ)), ((2, 3, 5, 0), (-2356032583501536798636992031249240803786597341856981685753487500 : ℤ)), ((2, 5, 0, 3), (-264435612500135887011191317379361566718208450612071812265132315750 : ℤ)),
    ((2, 5, 1, 2), (1343499014859797481983354675611068454446309582984722900390625000 : ℤ)), ((2, 5, 3, 0), (538556176445444483646627424431266448766028316609389082117187500 : ℤ)), ((2, 7, 0, 1), (-180595513834214954040755703333841582720129777957674316406250000 : ℤ)), ((2, 7, 1, 0), (-3696179247901754665139582342700307030693918994232456386718750000 : ℤ)),
    ((3, 2, 0, 5), (244874087262094653583321588116196385706615910564647668825625000 : ℤ)), ((3, 2, 1, 4), (39408471332759512812423720575141131519816352132437173270150000 : ℤ)), ((3, 2, 2, 3), (22392265224930663458161609063967360627295363324001934880649875000 : ℤ)), ((3, 4, 0, 3), (216257616009725629724985986099897435183767586861434213037006874855 : ℤ)),
    ((3, 4, 1, 2), (1127763464220039152522179907482642310600486788714435758713850000 : ℤ)), ((3, 6, 0, 1), (63976143564752261046826413124336593068871884904034423828125000 : ℤ)), ((3, 6, 1, 0), (2859163121680706677744505710375204963817987995130109759375000000 : ℤ)), ((4, 1, 0, 5), (-292413626853294334491361258920301121386790428601373339843750000 : ℤ)),
    ((4, 3, 0, 3), (358389042710709990655312390194137602537211960826015991256735982936 : ℤ)), ((4, 5, 1, 0), (-2187414896364177235446739745579421490727572130295983867015625000 : ℤ)), ((5, 0, 0, 5), (7718919672217529101983897898785872743317237710262743536359375000 : ℤ)), ((5, 0, 1, 4), (-4179740265876738714538552789229588283671294594004930826455000000 : ℤ)),
    ((5, 0, 2, 3), (-22243145649198929068647846284337715158009508959695857831279125000 : ℤ)), ((5, 0, 4, 1), (-4523871882141733662631670365222638169634637859518868289784375000 : ℤ)), ((5, 2, 0, 3), (-126275248702902313494270243017335167032281755194870773052141437500 : ℤ)), ((5, 4, 1, 0), (2562572697884860691684622458760451484644849666813621722000000000 : ℤ)),
    ((6, 3, 0, 1), (-734622261786283960749964764348589157119847731693943006476875000 : ℤ)), ((6, 3, 1, 0), (-2648069402992987782286257148803166612732818930729598017187500000 : ℤ)), ((7, 0, 0, 3), (62862725169761892358685757776892396878946411121066023483497703750 : ℤ)), ((7, 0, 1, 2), (-319880717823761305234132065621682965344359424520172119140625000 : ℤ)),
    ((7, 2, 0, 1), (877240880559883003474083776760903364160371285804120019531250000 : ℤ)), ((7, 2, 1, 0), (2456274465567672409727434574930529419649039600251536054687500000 : ℤ)), ((8, 1, 0, 1), (-537399605943918992793341870244427381778523833193889160156250000 : ℤ)), ((8, 1, 1, 0), (-2142821258476163738586450511357506788795377856133083308593750000 : ℤ)),
    ((9, 0, 0, 1), (319880717823761305234132065621682965344359424520172119140625000 : ℤ)), ((9, 0, 1, 0), (1796301914893949186169730005707902014932384945387783842500000000 : ℤ))
  ]

lemma hb_d4_26 : allBound wsD4_26 = true := by decide
lemma hk_d4_26 : (31667103174992135638421692556558467187442465016632078028490625000 : ℤ) ≠ 0 := by decide
lemma hc_d4_26 : compileStrict wsD4_26 = [(packKey 4 2 0 1 1, (31667103174992135638421692556558467187442465016632078028490625000 : ℤ))] := by decide

def wsD4_27 : List (Exps × ℤ) :=
  [
    ((0, 1, 0, 9), (12288389037267521745000000 : ℤ)), ((0, 1, 1, 8), (-7508394901513229062500000 : ℤ)), ((0, 1, 2, 7), (4419722582176289062500000 : ℤ)), ((0, 1, 3, 6), (-2475044646018721875000000 : ℤ)),
    ((0, 1, 4, 5), (1327095367341467062500000 : ℤ)), ((0, 1, 5, 4), (-952744566968291475000000 : ℤ)), ((0, 1, 6, 3), (-357881506796019937500000 : ℤ)), ((0, 1, 8, 1), (883944516435257812500000 : ℤ)),
    ((0, 1, 9, 0), (-1000120081452463125000000 : ℤ)), ((0, 3, 0, 7), (18216030517729462687500000 : ℤ)), ((0, 3, 1, 6), (-10261623496620689510625000 : ℤ)), ((0, 3, 2, 5), (5746509158107586125950000 : ℤ)),
    ((0, 3, 3, 4), (8033174769401534655994246350 : ℤ)), ((0, 3, 4, 3), (-810598976807085455000036685 : ℤ)), ((0, 3, 5, 2), (7769414063078459859375000 : ℤ)), ((0, 3, 7, 0), (-2052324699324137902125000 : ℤ)),
    ((0, 5, 0, 5), (-206767218808863822197767927500 : ℤ)), ((0, 5, 1, 4), (110866613513705077997469850650 : ℤ)), ((0, 5, 2, 3), (-261903290746719900285000000 : ℤ)), ((0, 5, 3, 2), (357881506796019937500000 : ℤ)),
    ((0, 5, 5, 0), (73845435288879936499202831250 : ℤ)), ((0, 7, 0, 3), (-19186123982433931530000000 : ℤ)), ((0, 7, 1, 2), (341361911087760937500000 : ℤ)), ((0, 9, 0, 1), (-357881506796019937500000 : ℤ)),
    ((1, 2, 0, 7), (-17265364584618799687500000 : ℤ)), ((1, 2, 1, 6), (10359218750771279812500000 : ℤ)), ((1, 2, 2, 5), (-5801162500431916695000000 : ℤ)), ((1, 2, 3, 4), (4984728004962041820750000 : ℤ)),
    ((1, 2, 4, 3), (-2150580039852893906250000 : ℤ)), ((1, 2, 7, 0), (2071843750154255962500000 : ℤ)), ((1, 4, 0, 5), (168761375850552519195657370350 : ℤ)), ((1, 4, 1, 4), (-90488242479867684102052475721 : ℤ)),
    ((1, 4, 2, 3), (213740287195966425959400000 : ℤ)), ((1, 4, 3, 2), (-300620465708656747500000 : ℤ)), ((1, 4, 5, 0), (-60271919946625899712734775125 : ℤ)), ((1, 6, 0, 3), (15940956143523705572250000 : ℤ)),
    ((1, 8, 0, 1), (986592261978217125000000 : ℤ)), ((2, 3, 0, 5), (39358198349339496250050000 : ℤ)), ((2, 3, 1, 4), (-21103491114931558465503000 : ℤ)), ((2, 3, 2, 3), (540171743263998462708357790 : ℤ)),
    ((2, 3, 3, 2), (-5179609375385639906250000 : ℤ)), ((2, 3, 5, 0), (-14056499410478391517875000 : ℤ)), ((2, 5, 0, 3), (-13390403160559912680690000 : ℤ)), ((3, 2, 0, 5), (-690614583384751987500000 : ℤ)),
    ((3, 2, 1, 4), (386744166695461113000000 : ℤ)), ((3, 2, 2, 3), (1433720026568595937500000 : ℤ)), ((3, 4, 0, 3), (2650641991176581268362533425 : ℤ)), ((3, 4, 1, 2), (-6258477031278290280000000 : ℤ)),
    ((4, 3, 0, 3), (-3178481465630869907656396740 : ℤ)), ((5, 0, 0, 5), (49230879488930914504676887500 : ℤ)), ((5, 0, 1, 4), (-26397128716445814158221988250 : ℤ)), ((5, 0, 2, 3), (62584770312782902800000000 : ℤ)),
    ((5, 0, 5, 0), (-17582456960332469465956031250 : ℤ)), ((5, 2, 0, 3), (-8602320159411575625000000 : ℤ)), ((6, 3, 0, 1), (2071843750154255962500000 : ℤ)), ((7, 0, 0, 3), (3188191228704741114450000 : ℤ))
  ]

lemma hb_d4_27 : allBound wsD4_27 = true := by decide
lemma hk_d4_27 : (123077198722327286261692218750 : ℤ) ≠ 0 := by decide
lemma hc_d4_27 : compileStrict wsD4_27 = [(packKey 4 2 0 2 0, (123077198722327286261692218750 : ℤ))] := by decide

def wsD4_28 : List (Exps × ℤ) :=
  [
    ((0, 0, 0, 10), (-218376202239692023800800527993125000000000 : ℤ)), ((0, 0, 1, 9), (106056583041388638793415327274375000000000 : ℤ)), ((0, 0, 2, 8), (-47203380827883328148854499051775000000000 : ℤ)), ((0, 0, 3, 7), (18055059389561305012517886026169000000000 : ℤ)),
    ((0, 0, 4, 6), (-278073352019724928002350486928855000000000 : ℤ)), ((0, 0, 5, 5), (243511353192583418025494526026625000000000 : ℤ)), ((0, 0, 6, 4), (-182824585129414643631871263328125000000000 : ℤ)), ((0, 0, 7, 3), (125682508110800381262609501642375000000000 : ℤ)),
    ((0, 0, 8, 2), (-81259252228891169208404900748855000000000 : ℤ)), ((0, 0, 9, 1), (-1316854140923061875162673800196993000000000 : ℤ)), ((0, 0, 10, 0), (696873410123518943063914931298225000000000 : ℤ)), ((0, 2, 0, 8), (-28647897677749478997403718927258408135531250 : ℤ)),
    ((0, 2, 1, 7), (18178478287192240434639508371048434835000000 : ℤ)), ((0, 2, 2, 6), (-10587161701615891699773432991734016466250000 : ℤ)), ((0, 2, 3, 5), (5928810552904899351873122475371049221100000 : ℤ)), ((0, 2, 4, 4), (-3313818769691515010400220577831987996531250 : ℤ)),
    ((0, 2, 5, 3), (1147829035758967066837431696523565388750000 : ℤ)), ((0, 2, 6, 2), (6718430684688503781215712648795933129750000 : ℤ)), ((0, 2, 8, 0), (-2117432340323178339954686598346803293250000 : ℤ)), ((0, 4, 0, 6), (-7001544521157391875573347491645817795940000 : ℤ)),
    ((0, 4, 1, 5), (3764330526293339289716451393635912585246400 : ℤ)), ((0, 4, 2, 4), (-1930690532074774618962349095533632883098784 : ℤ)), ((0, 4, 3, 3), (-8684288627377623980735321450302673601739965 : ℤ)), ((0, 4, 4, 2), (-1649949323379870363492833473057748717472000 : ℤ)),
    ((0, 4, 5, 1), (2348016083322002409069348025286180707200000 : ℤ)), ((0, 4, 6, 0), (-2742032380415479751725725512778409677588000 : ℤ)), ((0, 6, 0, 4), (-1565717726920521612432592634784397158600000 : ℤ)), ((0, 6, 1, 3), (3313818769691515010400220577831987996531250 : ℤ)),
    ((0, 6, 3, 1), (-390542574633566678775096377339224800000000 : ℤ)), ((0, 8, 0, 2), (-16570153387952051906614966322673421694906250 : ℤ)), ((0, 8, 1, 1), (-290582272792832350279089566472637500000000 : ℤ)), ((0, 10, 0, 0), (-89378831252509283745845814251131200000000 : ℤ)),
    ((1, 1, 0, 8), (581745710131250365258737312078220275000000 : ℤ)), ((1, 1, 1, 7), (61022277286494793558608808959253875000000 : ℤ)), ((1, 1, 6, 2), (2050348516826225063569255981030930200000000 : ℤ)), ((1, 3, 0, 6), (373558975797482717350774722118483947946875 : ℤ)),
    ((1, 3, 1, 5), (-21864861349014736388088186000109390370250 : ℤ)), ((1, 3, 2, 4), (-203215078740556984867686912819161471877285 : ℤ)), ((1, 3, 3, 3), (-20881683735302009598019712893092377540840625 : ℤ)), ((1, 3, 4, 2), (-305111386432473967793044044796269375000000 : ℤ)),
    ((1, 3, 6, 0), (1011352620647374470111883236354904891989375 : ℤ)), ((1, 5, 0, 4), (1315202890613238154443377813218893613224000 : ℤ)), ((1, 5, 1, 3), (-2783607766540872608736185285378869917086250 : ℤ)), ((1, 7, 0, 2), (16276094263672125603832364797265371650000000 : ℤ)),
    ((1, 7, 1, 1), (305111386432473967793044044796269375000000 : ℤ)), ((1, 9, 0, 0), (75078218252107798346510483970950208000000 : ℤ)), ((2, 0, 0, 8), (16642777658912539260760781999511863673600000 : ℤ)), ((2, 0, 1, 7), (-8888726245397088049632277244275446720000000 : ℤ)),
    ((2, 0, 2, 6), (4509366284678430344473211110828646112000000 : ℤ)), ((2, 0, 3, 5), (-2084441144607485838174227234951580174720000 : ℤ)), ((2, 0, 4, 4), (881310343219611640666299821663044613683200 : ℤ)), ((2, 0, 5, 3), (-6468438653909009045906410131767954058240000 : ℤ)),
    ((2, 0, 6, 2), (7024806191159084449812962189484060768000000 : ℤ)), ((2, 0, 7, 1), (-5791920215456037295533862414274552640000000 : ℤ)), ((2, 0, 8, 0), (4289650466408706430669011448647604262400000 : ℤ)), ((2, 2, 3, 3), (-2900999062199962485776262777922929217500000 : ℤ)),
    ((2, 2, 4, 2), (-1922201734524585997096177482216497062500000 : ℤ)), ((2, 4, 0, 4), (-820595726001310454934480541900341072992160 : ℤ)), ((2, 4, 1, 3), (2187547693410395245845033931779187720645185 : ℤ)), ((2, 4, 2, 2), (1293687730781801809181282026353590811648000 : ℤ)),
    ((2, 4, 3, 1), (-1404961238231816889962592437896812153600000 : ℤ)), ((2, 4, 4, 0), (1158384043091207459106772482854910528000000 : ℤ)), ((2, 6, 0, 2), (-12322838675234758611225462881231727517500000 : ℤ)), ((2, 8, 0, 0), (219714120939643013056366597328786880000000 : ℤ)),
    ((3, 3, 0, 4), (94090313453774030591983954897052183955013710 : ℤ)), ((3, 3, 1, 3), (8580704620057069187800607512905295506393750 : ℤ)), ((3, 5, 0, 2), (9531045080466707208001686427822279034700000 : ℤ)), ((3, 5, 2, 0), (82013940673049002542770239241237208000000 : ℤ)),
    ((3, 7, 0, 0), (-213844064754024619509708626225076000000000 : ℤ)), ((4, 0, 0, 6), (-2733798022434966751425674641374573600000000 : ℤ)), ((4, 0, 1, 5), (1640278813460980050855404784824744160000000 : ℤ)), ((4, 0, 2, 4), (-918556135538148828479026679501856729600000 : ℤ)),
    ((4, 2, 0, 4), (-1745237130393751095776211936234660825000000 : ℤ)), ((4, 2, 2, 2), (1281467823016390664730784988144331375000000 : ℤ)), ((4, 4, 0, 2), (-7357246379920889168174796100495649838728625 : ℤ)), ((4, 4, 2, 0), (-96229690389710829650183747376384990720000 : ℤ)),
    ((4, 6, 0, 0), (191968562354430385008376876636142400000000 : ℤ)), ((5, 1, 3, 1), (-820139406730490025427702392412372080000000 : ℤ)), ((5, 3, 0, 2), (9611008672622929985480887411082485312500000 : ℤ)), ((6, 0, 0, 4), (-313143545384104322486518526956879431720000 : ℤ)),
    ((6, 0, 1, 3), (662763753938303002080044115566397599306250 : ℤ)), ((6, 2, 0, 2), (-7688806938098343988384709928865988250000000 : ℤ)), ((6, 4, 0, 0), (-17875766250501856749169162850226240000000 : ℤ)), ((7, 1, 0, 2), (8201394067304900254277023924123720800000000 : ℤ)),
    ((7, 3, 0, 0), (292842031647244885423606844688950208000000 : ℤ)), ((8, 0, 0, 2), (-7151078630649751867546249104317043103500000 : ℤ)), ((8, 0, 2, 0), (273379802243496675142567464137457360000000 : ℤ)), ((8, 2, 0, 0), (-123395479610497046202216306070785600000000 : ℤ)),
    ((9, 1, 0, 0), (27742889683764816785039021081148000000000 : ℤ)), ((10, 0, 0, 0), (178757662505018567491691628502262400000000 : ℤ))
  ]

lemma hb_d4_28 : allBound wsD4_28 = true := by decide
lemma hk_d4_28 : (5740975847113430177993916746886604560000000 : ℤ) ≠ 0 := by decide
lemma hc_d4_28 : compileStrict wsD4_28 = [(packKey 4 2 1 0 1, (5740975847113430177993916746886604560000000 : ℤ))] := by decide

def wsD4_29 : List (Exps × ℤ) :=
  [
    ((0, 2, 0, 8), (-13888912106519531250 : ℤ)), ((0, 2, 1, 7), (8187148189106250000 : ℤ)), ((0, 2, 2, 6), (-4584802985899500000 : ℤ)), ((0, 2, 3, 5), (2458327696248970000 : ℤ)),
    ((0, 2, 4, 4), (-1253332134417937500 : ℤ)), ((0, 2, 7, 1), (1637429637821250000 : ℤ)), ((0, 2, 8, 0), (-1852634675934900000 : ℤ)), ((0, 4, 0, 6), (2119297851562500 : ℤ)),
    ((0, 4, 1, 5), (-1186806796875000 : ℤ)), ((0, 4, 2, 4), (-76705126367187500 : ℤ)), ((0, 4, 3, 3), (-1948298944036603800 : ℤ)), ((0, 4, 4, 2), (-1271578710937500 : ℤ)),
    ((0, 4, 6, 0), (423859570312500 : ℤ)), ((0, 6, 0, 4), (-2458327696248970000 : ℤ)), ((0, 6, 1, 3), (1253332134417937500 : ℤ)), ((0, 6, 4, 0), (-662926978875000000 : ℤ)),
    ((0, 8, 0, 2), (730995374027343750 : ℤ)), ((1, 3, 0, 6), (6660109281536250 : ℤ)), ((1, 3, 1, 5), (-3729661197660300 : ℤ)), ((1, 3, 2, 4), (67004329149602618 : ℤ)),
    ((1, 3, 3, 3), (-4605270856372265625 : ℤ)), ((1, 3, 6, 0), (1332021856307250 : ℤ)), ((1, 5, 0, 4), (2064995264849134800 : ℤ)), ((1, 5, 1, 3), (-1052798992911067500 : ℤ)),
    ((1, 5, 4, 0), (580061106515625000 : ℤ)), ((2, 0, 0, 8), (-12110273437500000 : ℤ)), ((2, 0, 1, 7), (7064326171875000 : ℤ)), ((2, 0, 2, 6), (-3956022656250000 : ℤ)),
    ((2, 0, 3, 5), (2121181671875000 : ℤ)), ((2, 0, 4, 4), (14387004843750000 : ℤ)), ((2, 0, 5, 3), (-4238595703125000 : ℤ)), ((2, 0, 7, 1), (1412865234375000 : ℤ)),
    ((2, 0, 8, 0), (-1598556093750000 : ℤ)), ((2, 4, 0, 4), (-1685853704882668832 : ℤ)), ((2, 4, 1, 3), (853313451153437950 : ℤ)), ((2, 4, 2, 2), (847719140625000 : ℤ)),
    ((2, 4, 4, 0), (-487533902520000000 : ℤ)), ((3, 3, 0, 4), (47531371016750665542 : ℤ)), ((3, 3, 1, 3), (3070180570914843750 : ℤ)), ((4, 0, 2, 4), (30936592347500000 : ℤ)),
    ((4, 4, 0, 2), (-25066642688358750 : ℤ)), ((5, 1, 4, 0), (-232024442606250000 : ℤ)), ((6, 0, 0, 4), (-491665539249794000 : ℤ)), ((6, 0, 1, 3), (250666426883587500 : ℤ))
  ]

lemma hb_d4_29 : allBound wsD4_29 = true := by decide
lemma hk_d4_29 : (1624171098243750000 : ℤ) ≠ 0 := by decide
lemma hc_d4_29 : compileStrict wsD4_29 = [(packKey 4 2 1 1 0, (1624171098243750000 : ℤ))] := by decide

def wsD4_30 : List (Exps × ℤ) :=
  [
    ((0, 1, 0, 9), (-110102495011247457858629641180371271001566676190887649916359375 : ℤ)), ((0, 1, 1, 8), (65746476345563962238283125646607161509198221087723501828125000 : ℤ)), ((0, 1, 2, 7), (-38493714409313830122343351263330875062252880648555579443359375 : ℤ)), ((0, 1, 3, 6), (21551827317858026486097524326063175223755019721659385078125000 : ℤ)),
    ((0, 1, 4, 5), (-13946698063905621440966298988453799353911670488743535603984375 : ℤ)), ((0, 1, 5, 4), (11836304820689410993119733538446673382391947809129857061906250 : ℤ)), ((0, 1, 6, 3), (-4396152202373674418006198569178010133953764009955203424609375 : ℤ)), ((0, 1, 7, 2), (69791270365775736221285721031722166598901622976091152343750 : ℤ)),
    ((0, 1, 8, 1), (-7738623607786066445166547807541444821935662771411739404296875 : ℤ)), ((0, 1, 9, 0), (-3235478935528773831023077247998174712118135476022441975000000 : ℤ)), ((0, 3, 0, 7), (70466959813778604588218774855701849680235692256849402468593750 : ℤ)), ((0, 3, 1, 6), (-37358235664861485353365182163567743943398472593895690419225000 : ℤ)),
    ((0, 3, 2, 5), (18682041960599991658451748018829667178934933829680337624653500 : ℤ)), ((0, 3, 3, 4), (-7822966886599183104284539961998495856342215457325405580126710 : ℤ)), ((0, 3, 4, 3), (51644558250399743210235024923281691538353561561048630106173148 : ℤ)), ((0, 3, 5, 2), (-31001824902546832865939148262532516573533498853196580929375000 : ℤ)),
    ((0, 3, 6, 1), (33578550175836602091491309891524041440523162343518735151687500 : ℤ)), ((0, 3, 7, 0), (-26659390090593212551525213513584429611835787286504129599095000 : ℤ)), ((0, 5, 0, 5), (-21426828721782280002987595004538826609787226241947400605468750 : ℤ)), ((0, 5, 1, 4), (11486346992301081054686447404393531272366382356538794915234375 : ℤ)),
    ((0, 5, 2, 3), (-2478019684839642935838477573392748000215458369388877264843750 : ℤ)), ((0, 5, 3, 2), (4396152202373674418006198569178010133953764009955203424609375 : ℤ)), ((0, 5, 4, 1), (-69791270365775736221285721031722166598901622976091152343750 : ℤ)), ((0, 5, 5, 0), (7738623607786066445166547807541444821935662771411739404296875 : ℤ)),
    ((0, 7, 0, 3), (378980891829533971000496763321623857857343214405719390003875000 : ℤ)), ((0, 7, 1, 2), (-14676239773351631640955381337012195222181788855404742167968750 : ℤ)), ((0, 7, 3, 0), (-3419404294891711007280174123373120309625576613392946553125000 : ℤ)), ((0, 9, 0, 1), (7416215126784368235882122314872933886002719822827329241406250 : ℤ)),
    ((0, 9, 1, 0), (96283072141884173105350462285864438764827596597628906250000 : ℤ)), ((1, 0, 0, 9), (-548619764366347017987418300955251430876325390064306835625000 : ℤ)), ((1, 0, 1, 8), (243530997188882459268643074348871794926138970122458286718750 : ℤ)), ((1, 0, 2, 7), (-107862025880951323824945123397964685406785937313149335937500 : ℤ)),
    ((1, 0, 3, 6), (40861178790915535200009267213978017180107670462058105468750 : ℤ)), ((1, 0, 4, 5), (-10277496519309230932266872629445947159612223285069296875000 : ℤ)), ((1, 0, 5, 4), (-1992139725601019973781141753438591226112727046721916406250 : ℤ)), ((1, 0, 6, 3), (-427729988172342800482424973561052796277778289331409569375000 : ℤ)),
    ((1, 0, 7, 2), (293123335536258092129400028333233099715386816499582839843750 : ℤ)), ((1, 0, 8, 1), (-189071454054052031696074755155726136918721082605248632812500 : ℤ)), ((1, 0, 9, 0), (116213066646212839437758856388924824532433581295410839843750 : ℤ)), ((1, 2, 0, 7), (158652306968789264754302677988616667179968050219779471307031250 : ℤ)),
    ((1, 2, 1, 6), (-91601009671637262294937423963628223982873974687805088903437500 : ℤ)), ((1, 2, 2, 5), (50099773912904768032616896476451213322040474010483318492331250 : ℤ)), ((1, 2, 3, 4), (-36580195682632469503579586082131036676784400125917489210206250 : ℤ)), ((1, 2, 4, 3), (26836047632348375705306008622893807566653692940258027513671875 : ℤ)),
    ((1, 2, 6, 1), (17951872548181482788220914147708881625534277220312969403906250 : ℤ)), ((1, 2, 7, 0), (-28578414819002585480828007162845005725451524777739857440062500 : ℤ)), ((1, 4, 0, 5), (18095362711242559141281918580450271584518195032101471844531250 : ℤ)), ((1, 4, 1, 4), (-9705055761648201963233016054308969176535488452269020076296875 : ℤ)),
    ((1, 4, 2, 3), (2321848297443206636023127212166364625264251873994894108921875 : ℤ)), ((1, 4, 3, 2), (-3607221852359417951028721803397317953265606110496088962796875 : ℤ)), ((1, 4, 5, 0), (-6462629539729485407600685207303668423042212511464811373046875 : ℤ)), ((1, 6, 0, 3), (-325511076881053260560349801052808480085143063256114420269775000 : ℤ)),
    ((1, 6, 1, 2), (9374894705680986233244699114326146047584510978398835449218750 : ℤ)), ((1, 8, 0, 1), (-6174910450471752780678899937308578305295361931584652210937500 : ℤ)), ((1, 8, 1, 0), (-78019690675048095641742254828603410110784263564843750000000 : ℤ)), ((2, 1, 3, 4), (478716601284839541019224377272236843347580725875012517437500 : ℤ)),
    ((2, 3, 0, 5), (-219020548866125407184755815189668509560908562969819248360603250 : ℤ)), ((2, 3, 1, 4), (117438637785309998544623095662121368367340657708868811427518695 : ℤ)), ((2, 3, 2, 3), (-24645545651365407712853095724179664210781181803762591958802932 : ℤ)), ((2, 3, 3, 2), (20667883268364555243959432175021677715688999235464387286250000 : ℤ)),
    ((2, 3, 5, 0), (78221624595044788280269933996310181986038772489221160128786875 : ℤ)), ((2, 5, 0, 3), (273333561259827770962489988008904675902850656989961110523123500 : ℤ)), ((2, 5, 1, 2), (-7874911552772028435925547256033962679970989221855021777343750 : ℤ)), ((2, 7, 0, 1), (1058559539338607359822372882851912262287256782475205648437500 : ℤ)),
    ((2, 7, 1, 0), (61977684481840082724526694243725165173950276561279296875000 : ℤ)), ((3, 2, 0, 5), (17371382050820242813277901723473429923175356789917495000000 : ℤ)), ((3, 2, 1, 4), (-12100544405259547718460158173346253636383869691146765950000 : ℤ)), ((3, 2, 2, 3), (-24140628225352907959033805158146635742825469279104575308593750 : ℤ)),
    ((3, 4, 0, 3), (-223139431296600373558081367051239055266379005452909442783428240 : ℤ)), ((3, 4, 1, 2), (6667341144447670527436615534947774317061985025089134407156250 : ℤ)), ((3, 6, 0, 1), (-374995788227239449329787964573045841903380439135953417968750 : ℤ)), ((3, 6, 1, 0), (-48467229331130240367460835318270385218697687135498046875000 : ℤ)),
    ((4, 1, 0, 5), (1713980749390635776403350856741868194726384193810731089062500 : ℤ)), ((4, 3, 0, 3), (-462263885159917226512319502735241054108485524538052999736635533 : ℤ)), ((4, 5, 1, 0), (37419190015018069327809946155924761121701025847749023437500 : ℤ)), ((5, 0, 0, 5), (-1049988207036270458123406300804528357329465229580669570312500 : ℤ)),
    ((5, 0, 1, 4), (585797874191557234828536091442920971796497174334462068750000 : ℤ)), ((5, 0, 2, 3), (-2399133342327863659240498221657685868380442982988928231718750 : ℤ)), ((5, 2, 0, 3), (144843769352117447754202830948879814456952815674627451851562500 : ℤ)), ((5, 2, 3, 0), (-7180749019272593115288365659083552650213710888125187761562500 : ℤ)),
    ((5, 4, 1, 0), (-28580899241346097667521334915227184516709175771645312500000 : ℤ)), ((6, 3, 0, 1), (-52114146152460728439833705170420289769526070369752485000000 : ℤ)), ((6, 3, 1, 0), (35588556852003176145367998123016993191085048331894531250000 : ℤ)), ((7, 0, 0, 3), (-65193399490741097738930764853851645891951961360913362628705000 : ℤ)),
    ((7, 0, 1, 2), (1874978941136197246648939822865229209516902195679767089843750 : ℤ)), ((7, 2, 0, 1), (-5141942248171907329210052570225604584179152581432193267187500 : ℤ)), ((7, 2, 1, 0), (-35940256336154291211415878464587535274205451759765625000000 : ℤ)), ((8, 1, 0, 1), (3149964621108811374370218902413585071988395688742008710937500 : ℤ)),
    ((8, 1, 1, 0), (32932826231313325808571555114223624620050313460693359375000 : ℤ)), ((9, 0, 0, 1), (-1874978941136197246648939822865229209516902195679767089843750 : ℤ)), ((9, 0, 1, 0), (-28512203712690805678390198557496148255196859404638671875000 : ℤ))
  ]

lemma hb_d4_30 : allBound wsD4_30 = true := by decide
lemma hk_d4_30 : (50265243134908151807018559613584868551495976216876314330937500 : ℤ) ≠ 0 := by decide
lemma hc_d4_30 : compileStrict wsD4_30 = [(packKey 4 2 2 0 0, (50265243134908151807018559613584868551495976216876314330937500 : ℤ))] := by decide

def wsD4_31 : List (Exps × ℤ) :=
  [
    ((0, 0, 0, 10), (-43675240447938404760160105598625000000000 : ℤ)), ((0, 0, 1, 9), (21211316608277727758683065454875000000000 : ℤ)), ((0, 0, 2, 8), (-9440676165576665629770899810355000000000 : ℤ)), ((0, 0, 3, 7), (3611011877912261002503577205233800000000 : ℤ)),
    ((0, 0, 4, 6), (-55614670403944985600470097385771000000000 : ℤ)), ((0, 0, 5, 5), (48702270638516683605098905205325000000000 : ℤ)), ((0, 0, 6, 4), (-36564917025882928726374252665625000000000 : ℤ)), ((0, 0, 7, 3), (25136501622160076252521900328475000000000 : ℤ)),
    ((0, 0, 8, 2), (-16251850445778233841680980149771000000000 : ℤ)), ((0, 0, 9, 1), (-263370828184612375032534760039398600000000 : ℤ)), ((0, 0, 10, 0), (139374682024703788612782986259645000000000 : ℤ)), ((0, 2, 0, 8), (-3140613031379293474654286773073428913906250 : ℤ)),
    ((0, 2, 1, 7), (1723152877661495837155001129182740375000000 : ℤ)), ((0, 2, 2, 6), (-1001782385453289527587161280414417781250000 : ℤ)), ((0, 2, 3, 5), (560998135853842135448810317032073957500000 : ℤ)), ((0, 2, 4, 4), (-267480907117714425823287776612192147186250 : ℤ)),
    ((0, 2, 5, 3), (229565807151793413367486339304713077750000 : ℤ)), ((0, 2, 6, 2), (674296164015767468822627338999755318750000 : ℤ)), ((0, 2, 8, 0), (-200356477090657905517432256082883556250000 : ℤ)), ((0, 4, 0, 6), (1644939773153475249856097571795387651180000 : ℤ)),
    ((0, 4, 1, 5), (-897788933937449380269414456857075659300800 : ℤ)), ((0, 4, 2, 4), (467470793251403358390885928207447814606048 : ℤ)), ((0, 4, 3, 3), (-21582537024818989129340259083315958279847737 : ℤ)), ((0, 4, 4, 2), (345478430916212827812744140663924763072000 : ℤ)),
    ((0, 4, 5, 1), (-350660085427451394750002750225121380400000 : ℤ)), ((0, 4, 6, 0), (529365146303524418399792514487718319036000 : ℤ)), ((0, 6, 0, 4), (311620429343033412439295651085256455000000 : ℤ)), ((0, 6, 1, 3), (267480907117714425823287776612192147186250 : ℤ)),
    ((0, 6, 3, 1), (-97635643658391669693774094334806200000000 : ℤ)), ((0, 8, 0, 2), (5623245228531944181143550779490355174218750 : ℤ)), ((0, 8, 1, 1), (-58116454558566470055817913294527500000000 : ℤ)), ((0, 10, 0, 0), (90008317852922423726425527240931200000000 : ℤ)),
    ((1, 1, 0, 8), (116349142026250073051747462415644055000000 : ℤ)), ((1, 1, 1, 7), (12204455457298958711721761791850775000000 : ℤ)), ((1, 1, 6, 2), (410069703365245012713851196206186040000000 : ℤ)), ((1, 3, 0, 6), (-524533033261185829310235001972650185390625 : ℤ)),
    ((1, 3, 1, 5), (264738394225121533095815225403224563338750 : ℤ)), ((1, 3, 2, 4), (-109419715472844316607572236679428730437825 : ℤ)), ((1, 3, 3, 3), (-3071416484496933883204002587110178841328125 : ℤ)), ((1, 3, 4, 2), (-61022277286494793558608808959253875000000 : ℤ)),
    ((1, 3, 6, 0), (-249907128657949822451628878901827739478125 : ℤ)), ((1, 5, 0, 4), (-261761160648148066449008346911615422200000 : ℤ)), ((1, 5, 1, 3), (-224683961978880117691561732354241403636450 : ℤ)), ((1, 7, 0, 2), (-4946175214570475133510550964670646470000000 : ℤ)),
    ((1, 7, 1, 1), (61022277286494793558608808959253875000000 : ℤ)), ((1, 9, 0, 0), (-75606986996454835930197442882382208000000 : ℤ)), ((2, 0, 0, 8), (-2456649738852565850189873518954293453600000 : ℤ)), ((2, 0, 1, 7), (1311865636789071018827012231198982720000000 : ℤ)),
    ((2, 0, 2, 6), (-665399017054303164571461713362275012000000 : ℤ)), ((2, 0, 3, 5), (315562913699368859925183080528322630720000 : ℤ)), ((2, 0, 4, 4), (-135237224291280093324862761896048601043200 : ℤ)), ((2, 0, 5, 3), (957873254525487859189754091231324210240000 : ℤ)),
    ((2, 0, 6, 2), (-1038686093213649089574977041637329668000000 : ℤ)), ((2, 0, 7, 1), (855908037765613683522532184318270640000000 : ℤ)), ((2, 0, 8, 0), (-622170110705497023498596447997181082400000 : ℤ)), ((2, 2, 3, 3), (-580199812439992497155252555584585843500000 : ℤ)),
    ((2, 2, 4, 2), (-384440346904917199419235496443299412500000 : ℤ)), ((2, 4, 0, 4), (150534383617709935583344482278387299404000 : ℤ)), ((2, 4, 1, 3), (210432354778161029009418652024528656319533 : ℤ)), ((2, 4, 2, 2), (-191574650905097571837950818246264842048000 : ℤ)),
    ((2, 4, 3, 1), (217500783008568984884372817760946553600000 : ℤ)), ((2, 4, 4, 0), (-171181607553122736704506436863654128000000 : ℤ)), ((2, 6, 0, 2), (4424603281489164491347607520017579968500000 : ℤ)), ((2, 8, 0, 0), (18209546118249816729962777924193120000000 : ℤ)),
    ((3, 3, 0, 4), (9487409142488453780437847372198230007176950 : ℤ)), ((3, 3, 1, 3), (6447123460505701982811510790991341856718750 : ℤ)), ((3, 5, 0, 2), (-3716666756450898172731990316814767173540000 : ℤ)), ((3, 7, 0, 0), (-8612340452346988589417582044284000000000 : ℤ)),
    ((4, 2, 0, 4), (-349047426078750219155242387246932165000000 : ℤ)), ((4, 2, 2, 2), (256293564603278132946156997628866275000000 : ℤ)), ((4, 4, 0, 2), (3028158391646616886751453960191808983459875 : ℤ)), ((4, 4, 2, 0), (9763564365839166969377409433480620000000 : ℤ)),
    ((4, 6, 0, 0), (3050930322187698386939426837550000000000 : ℤ)), ((5, 3, 0, 2), (1922201734524585997096177482216497062500000 : ℤ)), ((6, 0, 0, 4), (62324085868606682487859130217051291000000 : ℤ)), ((6, 0, 1, 3), (53496181423542885164657555322438429437250 : ℤ)),
    ((6, 0, 3, 1), (-97635643658391669693774094334806200000000 : ℤ)), ((6, 2, 0, 2), (-1537761387619668797676941985773197650000000 : ℤ)), ((6, 4, 0, 0), (18001663570584484745285105448186240000000 : ℤ)), ((7, 3, 0, 0), (-66836782869828574637511514120382208000000 : ℤ)),
    ((8, 0, 0, 2), (884920656297832898269521504003515993700000 : ℤ)), ((8, 2, 0, 0), (41834356577837720281713420796485600000000 : ℤ)), ((9, 1, 0, 0), (-25627814706376666450291185435420000000000 : ℤ)), ((10, 0, 0, 0), (15254651610938491934697134187750000000000 : ℤ))
  ]

lemma hb_d4_31 : allBound wsD4_31 = true := by decide
lemma hk_d4_31 : (683449505608741687856418660343643400000000 : ℤ) ≠ 0 := by decide
lemma hc_d4_31 : compileStrict wsD4_31 = [(packKey 4 3 0 0 1, (683449505608741687856418660343643400000000 : ℤ))] := by decide

def wsD4_32 : List (Exps × ℤ) :=
  [
    ((0, 2, 0, 8), (-156527343750 : ℤ)), ((0, 2, 1, 7), (92268750000 : ℤ)), ((0, 2, 2, 6), (-51670500000 : ℤ)), ((0, 2, 3, 5), (27705230000 : ℤ)),
    ((0, 2, 4, 4), (-14125500000 : ℤ)), ((0, 2, 7, 1), (18453750000 : ℤ)), ((0, 2, 8, 0), (-20879100000 : ℤ)), ((0, 4, 2, 4), (-2066820000 : ℤ)),
    ((0, 4, 3, 3), (-22058670450 : ℤ)), ((0, 6, 0, 4), (-27705230000 : ℤ)), ((0, 6, 1, 3), (14125500000 : ℤ)), ((0, 6, 4, 0), (-18453750000 : ℤ)),
    ((0, 8, 0, 2), (8238281250 : ℤ)), ((1, 3, 0, 6), (94170000 : ℤ)), ((1, 3, 1, 5), (-52735200 : ℤ)), ((1, 3, 2, 4), (1715194912 : ℤ)),
    ((1, 3, 3, 3), (-51901171875 : ℤ)), ((1, 3, 6, 0), (18834000 : ℤ)), ((1, 5, 0, 4), (23272393200 : ℤ)), ((1, 5, 1, 3), (-11865420000 : ℤ)),
    ((1, 5, 4, 0), (15501150000 : ℤ)), ((2, 4, 0, 4), (-18994705688 : ℤ)), ((2, 4, 1, 3), (9684442800 : ℤ)), ((2, 4, 4, 0), (-12651891000 : ℤ)),
    ((3, 3, 0, 4), (529918361778 : ℤ)), ((3, 3, 1, 3), (34600781250 : ℤ)), ((4, 4, 0, 2), (-282510000 : ℤ)), ((6, 0, 0, 4), (-5541046000 : ℤ)),
    ((6, 0, 1, 3), (2825100000 : ℤ)), ((6, 0, 4, 0), (-3690750000 : ℤ))
  ]

lemma hb_d4_32 : allBound wsD4_32 = true := by decide
lemma hk_d4_32 : (25835250000 : ℤ) ≠ 0 := by decide
lemma hc_d4_32 : compileStrict wsD4_32 = [(packKey 4 3 0 1 0, (25835250000 : ℤ))] := by decide

def wsD4_33 : List (Exps × ℤ) :=
  [
    ((0, 1, 0, 9), (-485861427711024253721967524481158177725132201206210632755246078125 : ℤ)), ((0, 1, 1, 8), (280534631611531787007969627965466398750945443980905863768279687500 : ℤ)), ((0, 1, 2, 7), (-161071577129399016468692260066957647464013016308714124646220703125 : ℤ)), ((0, 1, 3, 6), (89631992446442981590545411553203140198054649955768936999734375000 : ℤ)),
    ((0, 1, 4, 5), (-61824662532027188464641262441840244017290555269424110220382265625 : ℤ)), ((0, 1, 5, 4), (55421667129750309759761118221227629414241782370136163199283531250 : ℤ)), ((0, 1, 6, 3), (-68744929657946118639893424168410048843533370374155349805676328125 : ℤ)), ((0, 1, 7, 2), (8521361190307014478833811264397135726889587656664592032238281250 : ℤ)),
    ((0, 1, 8, 1), (-37083664677483811567357772735904178479596653351265448947666015625 : ℤ)), ((0, 1, 9, 0), (-31397891349977518606961084041043185568575337586655299877073437500 : ℤ)), ((0, 3, 0, 7), (-191596489563572228969558088585178265072163255820296765733943906250 : ℤ)), ((0, 3, 1, 6), (112733662399596524801619315603737385111093804464199713674924687500 : ℤ)),
    ((0, 3, 2, 5), (-65429697302565699805519637032261593556900071753906882625123065000 : ℤ)), ((0, 3, 3, 4), (29526352150761463305112908467320076343537491807933865299245665150 : ℤ)), ((0, 3, 4, 3), (685333127454506884908195233870402029113409853925821257135726129941 : ℤ)), ((0, 3, 5, 2), (-36955870530126873060851120403523463552100937224839090278223437500 : ℤ)),
    ((0, 3, 6, 1), (12361146526033535291317829455993829919296459457415501789546875000 : ℤ)), ((0, 3, 7, 0), (13376406002581936845487534388128522925381102216992023358297987500 : ℤ)), ((0, 5, 0, 5), (80724141876227894397353661743212348743641023031718917273917968750 : ℤ)), ((0, 5, 1, 4), (-37731903099646527888513923239962209699417867853651738451599140625 : ℤ)),
    ((0, 5, 2, 3), (441991388243624832835436067744188083186547127089062156669601137500 : ℤ)), ((0, 5, 3, 2), (68744929657946118639893424168410048843533370374155349805676328125 : ℤ)), ((0, 5, 4, 1), (-8521361190307014478833811264397135726889587656664592032238281250 : ℤ)), ((0, 5, 5, 0), (-47738933112673694606986046612020287201052806514713331485791015625 : ℤ)),
    ((0, 7, 0, 3), (578769098198153284526329870582392846376650464840197437921010875000 : ℤ)), ((0, 7, 1, 2), (-101651574930550098615645023229465858810689346632896578870527343750 : ℤ)), ((0, 7, 2, 1), (-40391713233408336273497056832344983657452123745704181158789062500 : ℤ)), ((0, 7, 3, 0), (-12361146526033535291317829455993829919296459457415501789546875000 : ℤ)),
    ((0, 9, 0, 1), (24404882859016925727120967834494274855179034681410065018884218750 : ℤ)), ((0, 9, 1, 0), (81064999597695757886860975737789875299344200535417157790880375000 : ℤ)), ((1, 0, 0, 9), (-194792460606522444805956611622953762246595802819052813452063500000 : ℤ)), ((1, 0, 1, 8), (113354829947603272978651241841787558380610202953771242099361406250 : ℤ)),
    ((1, 0, 2, 7), (-61948183819518138809584656888154812549180053771267574462164062500 : ℤ)), ((1, 0, 3, 6), (32305001805644193679293940703335497024011745568043755929785156250 : ℤ)), ((1, 0, 4, 5), (-23441193906687607064049518841760002732546239208619381419000000000 : ℤ)), ((1, 0, 5, 4), (22489245179286653679605200452833190755291719128322864739723906250 : ℤ)),
    ((1, 0, 6, 3), (-22957814267095410876900578148693302159424898242664816702174875000 : ℤ)), ((1, 0, 7, 2), (35789716999289460811102007310467970052936268157991286535400781250 : ℤ)), ((1, 0, 8, 1), (-32840903620640462511118078412184088254371021130248535769804687500 : ℤ)), ((1, 0, 9, 0), (-12471701349686296541623372476844930149179049546049321265214843750 : ℤ)),
    ((1, 2, 0, 7), (700745684743949170350650746871211313153913275733849570721328125000 : ℤ)), ((1, 2, 1, 6), (-399292924235592442892750922891066641784818373163892939287233750000 : ℤ)), ((1, 2, 2, 5), (216552542035006081580727341741777270696988424879641111618996525000 : ℤ)), ((1, 2, 3, 4), (-89762418206619032408207844981599503812762995174734666088540943750 : ℤ)),
    ((1, 2, 4, 3), (156758066154321091545001859039782558802011619728919646512701171875 : ℤ)), ((1, 2, 6, 1), (105772433053885296588197626158300730537647961382084015727815625000 : ℤ)), ((1, 2, 7, 0), (-140299975163624372343234542382956602949905366851112311130484250000 : ℤ)), ((1, 4, 0, 5), (-75287759522917678023638141213783363328225620675435362480739531250 : ℤ)),
    ((1, 4, 1, 4), (36775436150403979889003198318162118963887400600067125225071559375 : ℤ)), ((1, 4, 2, 3), (-365473072627181601422373206802106306839519623565165774492212689875 : ℤ)), ((1, 4, 3, 2), (-53154178059255657482130360671725780596683051465757530496333140625 : ℤ)), ((1, 4, 5, 0), (46668884538773995972091894836533858899758561698408905602025390625 : ℤ)),
    ((1, 6, 0, 3), (-494236000591225611438298199425160897281947447740180384470229831250 : ℤ)), ((1, 6, 1, 2), (72554554835455647356808574486465620271400362615107329866699218750 : ℤ)), ((1, 6, 2, 1), (33929039116063002469737527739169786272259783946391512173382812500 : ℤ)), ((1, 6, 3, 0), (-10771123528908889672932548488625328975320566332187781642343750000 : ℤ)),
    ((1, 8, 0, 1), (-16036246288592790048866546027271202227536911047618076347810937500 : ℤ)), ((1, 8, 1, 0), (-67537785892592870706157474670300773390200914474125390196960625000 : ℤ)), ((2, 1, 0, 7), (282741992633858353914479397826414885602164866219929268111523437500 : ℤ)), ((2, 1, 1, 6), (-158335515874960678192108462782792335937212325083160390142453125000 : ℤ)),
    ((2, 1, 2, 5), (84897995654859868402054347187344842983476703830304094904953437500 : ℤ)), ((2, 1, 3, 4), (-43277512649273605994669145223417481796520009877423931616405800000 : ℤ)), ((2, 1, 6, 1), (56548398526771670782895879565282977120432973243985853622304687500 : ℤ)), ((2, 1, 7, 0), (-63980473761718804657219338022434454113404164013195422955521875000 : ℤ)),
    ((2, 3, 0, 5), (420984049051915410620711485020499802196660145619773963761497915250 : ℤ)), ((2, 3, 1, 4), (-222828251537997468210811054863949674965451345789300960788958377415 : ℤ)), ((2, 3, 2, 3), (-389121035015971190861700140427290780201813671528616452176799190794 : ℤ)), ((2, 3, 3, 2), (51565055842356806222898784823912298139702040647028847624675000000 : ℤ)),
    ((2, 3, 5, 0), (-166152552415570613405878726761989956856676237258426517570486201875 : ℤ)), ((2, 5, 0, 3), (425462384382949881185614400514159261653995046801550765652102343250 : ℤ)), ((2, 5, 1, 2), (-62099875011308696244676261335269549132474936703710276549707031250 : ℤ)), ((2, 5, 2, 1), (-27692558592824755349109582164255720795549176040054786602465781250 : ℤ)),
    ((2, 7, 0, 1), (3712537621927466003293574341235362843276954784222017241132812500 : ℤ)), ((2, 7, 1, 0), (54265557316796507294739526976316819685330127129297206536890625000 : ℤ)), ((3, 0, 0, 7), (5495471188218821261700279841135371926183962414381521246093750000 : ℤ)), ((3, 0, 1, 6), (-3846829831753174883190195888794760348328773690067064872265625000 : ℤ)),
    ((3, 0, 2, 5), (2692780882227222418233137122156332243830141583046945410585937500 : ℤ)), ((3, 2, 0, 5), (1850339693269612022751442143700042000287858778762008779688750000 : ℤ)), ((3, 2, 1, 4), (-2680312116885318798362642098295910161786961602085472402329900000 : ℤ)), ((3, 2, 2, 3), (-185188451246577828286671267816708106308236353892581329179964843750 : ℤ)),
    ((3, 4, 0, 3), (-348608420365662395386913251394240415475793888088572983186445916705 : ℤ)), ((3, 4, 1, 2), (61669802988697039345110051806411674685231322083851278312148218750 : ℤ)), ((3, 4, 2, 1), (22121548855841153457874474956536038501016659351910142717931725000 : ℤ)), ((3, 6, 0, 1), (-2132816227067590917634303801699672741190259766590880220214843750 : ℤ)),
    ((3, 6, 1, 0), (-42823065095124920657210766454279638803622636482573933556445312500 : ℤ)), ((4, 1, 0, 5), (3285717917838268417107662149793440157207940840518714207789062500 : ℤ)), ((4, 3, 0, 3), (-551301174907625823606760693248802052260915896674448231666695089611 : ℤ)), ((4, 5, 1, 0), (34116753197674801091420516586814608599025642974241260860113281250 : ℤ)),
    ((5, 0, 0, 5), (14031629689327254823212967976973670135976895841894272719179687500 : ℤ)), ((5, 0, 1, 4), (-6616768535860972916649127404574954942501579195804831829868750000 : ℤ)), ((5, 0, 2, 3), (-102975425333205888953141301935783211882383070153110100581970468750 : ℤ)), ((5, 2, 0, 3), (262904729577891907976589413421003981042923524695700170745218750000 : ℤ)),
    ((5, 4, 1, 0), (-27689686550556812645931924450963257113498799108160366191720625000 : ℤ)), ((6, 1, 0, 3), (-16486413564656463785100839523406115778551887243144563738281250000 : ℤ)), ((6, 1, 1, 2), (11540489495259524649570587666384281044986321070201194616796875000 : ℤ)), ((6, 1, 2, 1), (-8078342646681667254699411366468996731490424749140836231757812500 : ℤ)),
    ((6, 1, 3, 0), (-22619359410708668313158351826113190848173189297594341448921875000 : ℤ)), ((6, 3, 0, 1), (-5551019079808836068254326431100126000863576336286026339066250000 : ℤ)), ((6, 3, 1, 0), (24661828329815040984327517467358299624386410289681212285563000000 : ℤ)), ((7, 0, 0, 3), (-81183056624294075173379322971958688193117933051491767783331766250 : ℤ)),
    ((7, 0, 1, 2), (7916345541228543957321379087930677742859317625763640478027343750 : ℤ)), ((7, 0, 2, 1), (11402003621316410353775740614387669672446485217358780281395312500 : ℤ)), ((7, 2, 0, 1), (-9857153753514805251322986449380320471623822521556142623367187500 : ℤ)), ((7, 2, 1, 0), (-27600030509841454703704362058264897320546703060357199345428125000 : ℤ)),
    ((8, 1, 0, 1), (6375166812108239058557564267892969981011860969162199233007812500 : ℤ)), ((8, 1, 1, 0), (26624557468982989861064683714271876691664141460349269504765625000 : ℤ)), ((9, 0, 0, 1), (-7916345541228543957321379087930677742859317625763640478027343750 : ℤ)), ((9, 0, 1, 0), (-21085864976216613062388835433997810769273895119381709589140625000 : ℤ))
  ]

lemma hb_d4_33 : allBound wsD4_33 = true := by decide
lemma hk_d4_33 : (158335515874960678192108462782792335937212325083160390142453125000 : ℤ) ≠ 0 := by decide
lemma hc_d4_33 : compileStrict wsD4_33 = [(packKey 4 3 1 0 0, (158335515874960678192108462782792335937212325083160390142453125000 : ℤ))] := by decide

def wsD4_34 : List (Exps × ℤ) :=
  [
    ((0, 1, 0, 9), (-1029974107042292856734710339128031141219483792549567280080125000 : ℤ)), ((0, 1, 1, 8), (622000985475642712063354198069041365734719344212865002001250000 : ℤ)), ((0, 1, 2, 7), (-353945071256817984194563863926599374348438467243062866421875000 : ℤ)), ((0, 1, 3, 6), (192830672592573030519785740350368551623138471343405489218750000 : ℤ)),
    ((0, 1, 4, 5), (-119783194728112180118414941969019800772132899784467691540625000 : ℤ)), ((0, 1, 5, 4), (100639912412152095060612124750740758180082916977843526556250000 : ℤ)), ((0, 1, 6, 3), (-7441888604890070815909942880657788181633645658821656969875000 : ℤ)), ((0, 1, 7, 2), (80678509668675609437550351727906470179806054690645739662500000 : ℤ)),
    ((0, 1, 8, 1), (-116891019776321087946084402344123572115291153271838710234375000 : ℤ)), ((0, 1, 9, 0), (7407239321996545240159749859369406274296427791649131437500000 : ℤ)), ((0, 3, 0, 7), (-1440352070268924456559737838715952836127709724712310400547375000 : ℤ)), ((0, 3, 1, 6), (811197079504364393199338976362661302999288446878083297488087500 : ℤ)),
    ((0, 3, 2, 5), (-444941434651955478180324800955587956661731006735718774405829000 : ℤ)), ((0, 3, 3, 4), (147338286572160736495487488542350558224342328395309939947777240 : ℤ)), ((0, 3, 4, 3), (6441236134070221943867989344930819165920853574037929327261127391 : ℤ)), ((0, 3, 5, 2), (-334395054757354866134521854002493521498846936548599105145312500 : ℤ)),
    ((0, 3, 6, 1), (-139933948057328730169575387112535595268057852740118082812500000 : ℤ)), ((0, 3, 7, 0), (242201671933632153022482302193981172181605033798541278247617500 : ℤ)), ((0, 5, 0, 5), (2069465978196500367314576427592082993124159392542395843173437500 : ℤ)), ((0, 5, 1, 4), (-1089512113469445606143052795792997917552366627435794927637281250 : ℤ)),
    ((0, 5, 2, 3), (7768157858807862475967742291201567943765097254633497473556240000 : ℤ)), ((0, 5, 3, 2), (7441888604890070815909942880657788181633645658821656969875000 : ℤ)), ((0, 5, 4, 1), (-80678509668675609437550351727906470179806054690645739662500000 : ℤ)), ((0, 5, 5, 0), (-690943244891845637523856734302776101033751321642244912941406250 : ℤ)),
    ((0, 7, 0, 3), (-22218973819510519364986543986825889098483038446068833786670750000 : ℤ)), ((0, 7, 1, 2), (-43135948585319754916360909089172128419139137820486816843750000 : ℤ)), ((0, 7, 3, 0), (139933948057328730169575387112535595268057852740118082812500000 : ℤ)), ((0, 9, 0, 1), (26645179765630465184890170911359675201375629282877561780125000 : ℤ)),
    ((0, 9, 1, 0), (111302957031973661288228521552783763689956793764497917500000000 : ℤ)), ((1, 0, 0, 9), (-1846668369663669512470245136670254326411689870651899563146512500 : ℤ)), ((1, 0, 1, 8), (1074828373696406658209100432813839205718561314294198786897750000 : ℤ)), ((1, 0, 2, 7), (-587450748251919501997575580128065366281055799873199546589062500 : ℤ)),
    ((1, 0, 3, 6), (306382436313845750476128226387902793467045552615610938984375000 : ℤ)), ((1, 0, 4, 5), (-222640416338132527216206399356555184064499572263848024479687500 : ℤ)), ((1, 0, 5, 4), (213922274000602241035822088649547909346823006252001795848375000 : ℤ)), ((1, 0, 6, 3), (-216797115271023398992809933715268833820078041973276611105162500 : ℤ)),
    ((1, 0, 7, 2), (338849740608437559637711477257207174755185429700712106582500000 : ℤ)), ((1, 0, 8, 1), (-311118572855205363049635960172588601687745691232189684507812500 : ℤ)), ((1, 0, 9, 0), (-119978922069314583926543517577975015709993181750457380562500000 : ℤ)), ((1, 2, 0, 7), (1477753348983986647022541569013019700710296919215840168421875000 : ℤ)),
    ((1, 2, 1, 6), (-857265880298352954877914110114179345419886002454079303662500000 : ℤ)), ((1, 2, 2, 5), (470273516603064643619761624566062941766372111682476144254125000 : ℤ)), ((1, 2, 3, 4), (-381954614703769809300030362663100702355410192809814329084025000 : ℤ)), ((1, 2, 4, 3), (82383874029067033746406428417242945801636151926293508615625000 : ℤ)),
    ((1, 2, 6, 1), (146930645460195166678054156468162375031460745377123986953125000 : ℤ)), ((1, 2, 7, 0), (-255413544894067829077328054290357226244811912134886710420000000 : ℤ)), ((1, 4, 0, 5), (-1799324912784535942763907176776779006576520695592586258562562500 : ℤ)), ((1, 4, 1, 4), (959802382419046128672708895529267247659187792017505953486253750 : ℤ)),
    ((1, 4, 2, 3), (-6395404970710246215782885743736082393632167859042072271517641600 : ℤ)), ((1, 4, 3, 2), (37108236626097020313197634723301224691443346041245130366337500 : ℤ)), ((1, 4, 5, 0), (642616040280191408129966848848849645205900248425923663772343750 : ℤ)), ((1, 6, 0, 3), (19505884651438332460948201778990865505450493207325816315923156250 : ℤ)),
    ((1, 6, 1, 2), (27053228865492488889523899834934494748420059477539062500000000 : ℤ)), ((1, 6, 3, 0), (-146930645460195166678054156468162375031460745377123986953125000 : ℤ)), ((1, 8, 0, 1), (-48921576248215031079931248943199907167383720693692852637500000 : ℤ)), ((1, 8, 1, 0), (-90190540098846701959730335605943718522975951742598500000000000 : ℤ)),
    ((2, 1, 0, 7), (2692780882227222418233137122156332243830141583046945410585937500 : ℤ)), ((2, 1, 1, 6), (-1507957294047244554210556788407546056544879286506289429928125000 : ℤ)), ((2, 1, 2, 5), (808552339570093984781469973212808028414063846002896141951937500 : ℤ)), ((2, 1, 3, 4), (-412166787135939104711134716413499826633523903594513634441960000 : ℤ)),
    ((2, 1, 6, 1), (538556176445444483646627424431266448766028316609389082117187500 : ℤ)), ((2, 1, 7, 0), (-609337845349702901497327028785090039175277752506623075766875000 : ℤ)), ((2, 3, 0, 5), (-2848209316378820747040500187034714671033814692609022848924015000 : ℤ)), ((2, 3, 1, 4), (1529385338844651335285208324808972009405380095669129228032590900 : ℤ)),
    ((2, 3, 2, 3), (-4265400123656601459301085623894431358334476290811628340278251594 : ℤ)), ((2, 3, 3, 2), (222930036504903244089681236001662347665897957699066070096875000 : ℤ)), ((2, 3, 5, 0), (1017217612992435981085892923940969525369219533074651017472862500 : ℤ)), ((2, 5, 0, 3), (-16302509749781011446254262551069627059251709513434782978487059250 : ℤ)),
    ((2, 5, 1, 2), (-22724712247013690667200075861344975588672849961132812500000000 : ℤ)), ((2, 5, 3, 0), (15710506897475043280240006547003105273221362794906332617187500 : ℤ)), ((2, 7, 0, 1), (3054696013612180459754241489933174949878745001578125000000000 : ℤ)), ((2, 7, 1, 0), (71646026652099657264762270050282966584593375005875781250000000 : ℤ)),
    ((3, 2, 0, 5), (21821930886974010568494131926592408208186703862297809346250000 : ℤ)), ((3, 2, 1, 4), (-14962965983993160839297521784698253246388837134824745733900000 : ℤ)), ((3, 2, 2, 3), (-72958068596373015090620218834784960366704140935888380743750000 : ℤ)), ((3, 4, 0, 3), (13296223824678921820566564827531202621162182725207950677662962645 : ℤ)),
    ((3, 4, 1, 2), (191179779198660362619839784329975350599395228878266746689275000 : ℤ)), ((3, 6, 0, 1), (-1082129154619699555580955993397379789936802379101562500000000 : ℤ)), ((3, 6, 1, 0), (-56027978996683022416685007639427527860766673422708281250000000 : ℤ)), ((4, 1, 0, 5), (4946051656048440102042022860488290559871144740746875000000000 : ℤ)),
    ((4, 3, 0, 3), (20747221324842313646006856894241314318867786227590781993325759564 : ℤ)), ((4, 5, 1, 0), (43256477029268494435739990043079084602613988699398940625000000 : ℤ)), ((5, 0, 0, 5), (-3029961632935158755626676781512663411823046661484375000000000 : ℤ)), ((5, 0, 1, 4), (-841238370853140693032671918379601022999105186686093750000000 : ℤ)),
    ((5, 0, 2, 3), (-1726320854884787122371821986031442609998784361004659654392750000 : ℤ)), ((5, 2, 0, 3), (-7640594235103429164155690053460286969290199903525505947295312500 : ℤ)), ((5, 4, 1, 0), (-33039438080111735223816224983946429765877550195797507000000000 : ℤ)), ((6, 3, 0, 1), (-65465792660922031705482395779777224624560111586893428038750000 : ℤ)),
    ((6, 3, 1, 0), (41140270309315723814112118587097569747064244579069587500000000 : ℤ)), ((7, 0, 0, 3), (3979684889742131083563189825591220687115531765959356336411671250 : ℤ)), ((7, 0, 1, 2), (5410645773098497777904779966986898949684011895507812500000000 : ℤ)), ((7, 0, 3, 0), (-131968257938790363554016054994826084295059447477213193984375000 : ℤ)),
    ((7, 2, 0, 1), (-14838154968145320306126068581464871679613434222240625000000000 : ℤ)), ((7, 2, 1, 0), (-41546833910806896857152992028101640702917615822273750000000000 : ℤ)), ((8, 1, 0, 1), (9089884898805476266880030344537990235469139984453125000000000 : ℤ)), ((8, 1, 1, 0), (38070253279452443942754163740400388004300169756760156250000000 : ℤ)),
    ((9, 0, 0, 1), (-5410645773098497777904779966986898949684011895507812500000000 : ℤ)), ((9, 0, 1, 0), (-32960026244738001022053666522400013003182003116976031250000000 : ℤ))
  ]

lemma hb_d4_34 : allBound wsD4_34 = true := by decide
lemma hk_d4_34 : (923777805571532544878112384963782590065416132340492357890625000 : ℤ) ≠ 0 := by decide
lemma hc_d4_34 : compileStrict wsD4_34 = [(packKey 4 4 0 0 0, (923777805571532544878112384963782590065416132340492357890625000 : ℤ))] := by decide

theorem no_deg4_strict (P : Fin 4 → R4) (D : R4)
    (hD_hom : D.IsHomogeneous 4)
    (hdir : ∑ i, pderiv i core * P i = coreSource * D) : D = 0 := by
  have h_eq : (∑ i, pderiv i core * P i) - coreSource * D = 0 := sub_eq_zero.mpr hdir
  have hz_0 : coeff (toFS (0, 0, 0, 4)) D = 0 :=
    zero_of_strict_cert P D h_eq 0 0 0 4 (2111140211666142375894779503770564479162831001108805201899375000 : ℤ) wsD4_0
      hb_d4_0 hk_d4_0 hc_d4_0
  have hz_1 : coeff (toFS (0, 0, 1, 3)) D = 0 :=
    zero_of_strict_cert P D h_eq 0 0 1 3 (3618469642436422216093751231250 : ℤ) wsD4_1
      hb_d4_1 hk_d4_1 hc_d4_1
  have hz_2 : coeff (toFS (0, 0, 2, 2)) D = 0 :=
    zero_of_strict_cert P D h_eq 0 0 2 2 (30159145880944891084211135768150921130897585730125788598562500 : ℤ) wsD4_2
      hb_d4_2 hk_d4_2 hc_d4_2
  have hz_3 : coeff (toFS (0, 0, 3, 1)) D = 0 :=
    zero_of_strict_cert P D h_eq 0 0 3 1 (586427836573928437748549862158490133100786389196890333860937500 : ℤ) wsD4_3
      hb_d4_3 hk_d4_3 hc_d4_3
  have hz_4 : coeff (toFS (0, 0, 4, 0)) D = 0 :=
    zero_of_strict_cert P D h_eq 0 0 4 0 (791677579374803390960542313913961679686061625415801950712265625000 : ℤ) wsD4_4
      hb_d4_4 hk_d4_4 hc_d4_4
  have hz_5 : coeff (toFS (0, 1, 0, 3)) D = 0 :=
    zero_of_strict_cert P D h_eq 0 1 0 3 (126810354636007248303729450000 : ℤ) wsD4_5
      hb_d4_5 hk_d4_5 hc_d4_5
  have hz_6 : coeff (toFS (0, 1, 1, 2)) D = 0 :=
    zero_of_strict_cert P D h_eq 0 1 1 2 (120560492789382033737872251684618695760000000 : ℤ) wsD4_6
      hb_d4_6 hk_d4_6 hc_d4_6
  have hz_7 : coeff (toFS (0, 1, 2, 1)) D = 0 :=
    zero_of_strict_cert P D h_eq 0 1 2 1 (776713422145544395860342881250000 : ℤ) wsD4_7
      hb_d4_7 hk_d4_7 hc_d4_7
  have hz_8 : coeff (toFS (0, 1, 3, 0)) D = 0 :=
    zero_of_strict_cert P D h_eq 0 1 3 0 (12945223702425739931005714687500000 : ℤ) wsD4_8
      hb_d4_8 hk_d4_8 hc_d4_8
  have hz_9 : coeff (toFS (0, 2, 0, 2)) D = 0 :=
    zero_of_strict_cert P D h_eq 0 2 0 2 (11967915032120988525480609431805921083689518146875312935937500 : ℤ) wsD4_9
      hb_d4_9 hk_d4_9 hc_d4_9
  have hz_10 : coeff (toFS (0, 2, 1, 1)) D = 0 :=
    zero_of_strict_cert P D h_eq 0 2 1 1 (2261935941070866831315835182611319084817318929759434144892187500 : ℤ) wsD4_10
      hb_d4_10 hk_d4_10 hc_d4_10
  have hz_11 : coeff (toFS (0, 2, 2, 0)) D = 0 :=
    zero_of_strict_cert P D h_eq 0 2 2 0 (1025821288467513302184052237011936092887672984017883965937500 : ℤ) wsD4_11
      hb_d4_11 hk_d4_11 hc_d4_11
  have hz_12 : coeff (toFS (0, 3, 0, 1)) D = 0 :=
    zero_of_strict_cert P D h_eq 0 3 0 1 (125050506359327045752500000 : ℤ) wsD4_12
      hb_d4_12 hk_d4_12 hc_d4_12
  have hz_13 : coeff (toFS (0, 3, 1, 0)) D = 0 :=
    zero_of_strict_cert P D h_eq 0 3 1 0 (36907500 : ℤ) wsD4_13
      hb_d4_13 hk_d4_13 hc_d4_13
  have hz_14 : coeff (toFS (0, 4, 0, 0)) D = 0 :=
    zero_of_strict_cert P D h_eq 0 4 0 0 (3166710317499213563842169255655846718744246501663207802849062500 : ℤ) wsD4_14
      hb_d4_14 hk_d4_14 hc_d4_14
  have hz_15 : coeff (toFS (1, 0, 0, 3)) D = 0 :=
    zero_of_strict_cert P D h_eq 1 0 0 3 (36907500 : ℤ) wsD4_15
      hb_d4_15 hk_d4_15 hc_d4_15
  have hz_16 : coeff (toFS (1, 0, 1, 2)) D = 0 :=
    zero_of_strict_cert P D h_eq 1 0 1 2 (48725132947312500 : ℤ) wsD4_16
      hb_d4_16 hk_d4_16 hc_d4_16
  have hz_17 : coeff (toFS (1, 0, 2, 1)) D = 0 :=
    zero_of_strict_cert P D h_eq 1 0 2 1 (1130292187500 : ℤ) wsD4_17
      hb_d4_17 hk_d4_17 hc_d4_17
  have hz_18 : coeff (toFS (1, 0, 3, 0)) D = 0 :=
    zero_of_strict_cert P D h_eq 1 0 3 0 (12917625000 : ℤ) wsD4_18
      hb_d4_18 hk_d4_18 hc_d4_18
  have hz_19 : coeff (toFS (1, 1, 0, 2)) D = 0 :=
    zero_of_strict_cert P D h_eq 1 1 0 2 (150795729404724455421055678840754605654487928650628942992812500 : ℤ) wsD4_19
      hb_d4_19 hk_d4_19 hc_d4_19
  have hz_20 : coeff (toFS (1, 1, 1, 1)) D = 0 :=
    zero_of_strict_cert P D h_eq 1 1 1 1 (22619359410708668313158351826113190848173189297594341448921875000 : ℤ) wsD4_20
      hb_d4_20 hk_d4_20 hc_d4_20
  have hz_21 : coeff (toFS (1, 1, 2, 0)) D = 0 :=
    zero_of_strict_cert P D h_eq 1 1 2 0 (158335515874960678192108462782792335937212325083160390142453125000 : ℤ) wsD4_21
      hb_d4_21 hk_d4_21 hc_d4_21
  have hz_22 : coeff (toFS (1, 2, 0, 1)) D = 0 :=
    zero_of_strict_cert P D h_eq 1 2 0 1 (1004670773244850281148935430705155798000000000 : ℤ) wsD4_22
      hb_d4_22 hk_d4_22 hc_d4_22
  have hz_23 : coeff (toFS (1, 2, 1, 0)) D = 0 :=
    zero_of_strict_cert P D h_eq 1 2 1 0 (126592725000000 : ℤ) wsD4_23
      hb_d4_23 hk_d4_23 hc_d4_23
  have hz_24 : coeff (toFS (1, 3, 0, 0)) D = 0 :=
    zero_of_strict_cert P D h_eq 1 3 0 0 (516924234633774602299107318750 : ℤ) wsD4_24
      hb_d4_24 hk_d4_24 hc_d4_24
  have hz_25 : coeff (toFS (2, 0, 0, 2)) D = 0 :=
    zero_of_strict_cert P D h_eq 2 0 0 2 (21542247057817779345865096977250657950641132664375563284687500 : ℤ) wsD4_25
      hb_d4_25 hk_d4_25 hc_d4_25
  have hz_26 : coeff (toFS (2, 0, 1, 1)) D = 0 :=
    zero_of_strict_cert P D h_eq 2 0 1 1 (31667103174992135638421692556558467187442465016632078028490625000 : ℤ) wsD4_26
      hb_d4_26 hk_d4_26 hc_d4_26
  have hz_27 : coeff (toFS (2, 0, 2, 0)) D = 0 :=
    zero_of_strict_cert P D h_eq 2 0 2 0 (123077198722327286261692218750 : ℤ) wsD4_27
      hb_d4_27 hk_d4_27 hc_d4_27
  have hz_28 : coeff (toFS (2, 1, 0, 1)) D = 0 :=
    zero_of_strict_cert P D h_eq 2 1 0 1 (5740975847113430177993916746886604560000000 : ℤ) wsD4_28
      hb_d4_28 hk_d4_28 hc_d4_28
  have hz_29 : coeff (toFS (2, 1, 1, 0)) D = 0 :=
    zero_of_strict_cert P D h_eq 2 1 1 0 (1624171098243750000 : ℤ) wsD4_29
      hb_d4_29 hk_d4_29 hc_d4_29
  have hz_30 : coeff (toFS (2, 2, 0, 0)) D = 0 :=
    zero_of_strict_cert P D h_eq 2 2 0 0 (50265243134908151807018559613584868551495976216876314330937500 : ℤ) wsD4_30
      hb_d4_30 hk_d4_30 hc_d4_30
  have hz_31 : coeff (toFS (3, 0, 0, 1)) D = 0 :=
    zero_of_strict_cert P D h_eq 3 0 0 1 (683449505608741687856418660343643400000000 : ℤ) wsD4_31
      hb_d4_31 hk_d4_31 hc_d4_31
  have hz_32 : coeff (toFS (3, 0, 1, 0)) D = 0 :=
    zero_of_strict_cert P D h_eq 3 0 1 0 (25835250000 : ℤ) wsD4_32
      hb_d4_32 hk_d4_32 hc_d4_32
  have hz_33 : coeff (toFS (3, 1, 0, 0)) D = 0 :=
    zero_of_strict_cert P D h_eq 3 1 0 0 (158335515874960678192108462782792335937212325083160390142453125000 : ℤ) wsD4_33
      hb_d4_33 hk_d4_33 hc_d4_33
  have hz_34 : coeff (toFS (4, 0, 0, 0)) D = 0 :=
    zero_of_strict_cert P D h_eq 4 0 0 0 (923777805571532544878112384963782590065416132340492357890625000 : ℤ) wsD4_34
      hb_d4_34 hk_d4_34 hc_d4_34
  rw [D.as_sum]
  apply Finset.sum_eq_zero
  intro s hs
  have hdeg : s 0 + s 1 + s 2 + s 3 = 4 := by
    have h := hD_hom (mem_support_iff.mp hs)
    simpa [Finsupp.weight_apply, Finsupp.sum_fintype, Fin.sum_univ_four, add_assoc] using h
  have hs0 : coeff s D = 0 := by
    if ha0 : s 0 = 0 then
      if hb0 : s 1 = 0 then
        if hc0 : s 2 = 0 then
          have hd : s 3 = 4 := by omega
          rw [eq_toFS s, ha0, hb0, hc0, hd]; exact hz_0
        else if hc1 : s 2 = 1 then
          have hd : s 3 = 3 := by omega
          rw [eq_toFS s, ha0, hb0, hc1, hd]; exact hz_1
        else if hc2 : s 2 = 2 then
          have hd : s 3 = 2 := by omega
          rw [eq_toFS s, ha0, hb0, hc2, hd]; exact hz_2
        else if hc3 : s 2 = 3 then
          have hd : s 3 = 1 := by omega
          rw [eq_toFS s, ha0, hb0, hc3, hd]; exact hz_3
        else if hc4 : s 2 = 4 then
          have hd : s 3 = 0 := by omega
          rw [eq_toFS s, ha0, hb0, hc4, hd]; exact hz_4
        else omega
      else if hb1 : s 1 = 1 then
        if hc0 : s 2 = 0 then
          have hd : s 3 = 3 := by omega
          rw [eq_toFS s, ha0, hb1, hc0, hd]; exact hz_5
        else if hc1 : s 2 = 1 then
          have hd : s 3 = 2 := by omega
          rw [eq_toFS s, ha0, hb1, hc1, hd]; exact hz_6
        else if hc2 : s 2 = 2 then
          have hd : s 3 = 1 := by omega
          rw [eq_toFS s, ha0, hb1, hc2, hd]; exact hz_7
        else if hc3 : s 2 = 3 then
          have hd : s 3 = 0 := by omega
          rw [eq_toFS s, ha0, hb1, hc3, hd]; exact hz_8
        else omega
      else if hb2 : s 1 = 2 then
        if hc0 : s 2 = 0 then
          have hd : s 3 = 2 := by omega
          rw [eq_toFS s, ha0, hb2, hc0, hd]; exact hz_9
        else if hc1 : s 2 = 1 then
          have hd : s 3 = 1 := by omega
          rw [eq_toFS s, ha0, hb2, hc1, hd]; exact hz_10
        else if hc2 : s 2 = 2 then
          have hd : s 3 = 0 := by omega
          rw [eq_toFS s, ha0, hb2, hc2, hd]; exact hz_11
        else omega
      else if hb3 : s 1 = 3 then
        if hc0 : s 2 = 0 then
          have hd : s 3 = 1 := by omega
          rw [eq_toFS s, ha0, hb3, hc0, hd]; exact hz_12
        else if hc1 : s 2 = 1 then
          have hd : s 3 = 0 := by omega
          rw [eq_toFS s, ha0, hb3, hc1, hd]; exact hz_13
        else omega
      else if hb4 : s 1 = 4 then
        if hc0 : s 2 = 0 then
          have hd : s 3 = 0 := by omega
          rw [eq_toFS s, ha0, hb4, hc0, hd]; exact hz_14
        else omega
      else omega
    else if ha1 : s 0 = 1 then
      if hb0 : s 1 = 0 then
        if hc0 : s 2 = 0 then
          have hd : s 3 = 3 := by omega
          rw [eq_toFS s, ha1, hb0, hc0, hd]; exact hz_15
        else if hc1 : s 2 = 1 then
          have hd : s 3 = 2 := by omega
          rw [eq_toFS s, ha1, hb0, hc1, hd]; exact hz_16
        else if hc2 : s 2 = 2 then
          have hd : s 3 = 1 := by omega
          rw [eq_toFS s, ha1, hb0, hc2, hd]; exact hz_17
        else if hc3 : s 2 = 3 then
          have hd : s 3 = 0 := by omega
          rw [eq_toFS s, ha1, hb0, hc3, hd]; exact hz_18
        else omega
      else if hb1 : s 1 = 1 then
        if hc0 : s 2 = 0 then
          have hd : s 3 = 2 := by omega
          rw [eq_toFS s, ha1, hb1, hc0, hd]; exact hz_19
        else if hc1 : s 2 = 1 then
          have hd : s 3 = 1 := by omega
          rw [eq_toFS s, ha1, hb1, hc1, hd]; exact hz_20
        else if hc2 : s 2 = 2 then
          have hd : s 3 = 0 := by omega
          rw [eq_toFS s, ha1, hb1, hc2, hd]; exact hz_21
        else omega
      else if hb2 : s 1 = 2 then
        if hc0 : s 2 = 0 then
          have hd : s 3 = 1 := by omega
          rw [eq_toFS s, ha1, hb2, hc0, hd]; exact hz_22
        else if hc1 : s 2 = 1 then
          have hd : s 3 = 0 := by omega
          rw [eq_toFS s, ha1, hb2, hc1, hd]; exact hz_23
        else omega
      else if hb3 : s 1 = 3 then
        if hc0 : s 2 = 0 then
          have hd : s 3 = 0 := by omega
          rw [eq_toFS s, ha1, hb3, hc0, hd]; exact hz_24
        else omega
      else omega
    else if ha2 : s 0 = 2 then
      if hb0 : s 1 = 0 then
        if hc0 : s 2 = 0 then
          have hd : s 3 = 2 := by omega
          rw [eq_toFS s, ha2, hb0, hc0, hd]; exact hz_25
        else if hc1 : s 2 = 1 then
          have hd : s 3 = 1 := by omega
          rw [eq_toFS s, ha2, hb0, hc1, hd]; exact hz_26
        else if hc2 : s 2 = 2 then
          have hd : s 3 = 0 := by omega
          rw [eq_toFS s, ha2, hb0, hc2, hd]; exact hz_27
        else omega
      else if hb1 : s 1 = 1 then
        if hc0 : s 2 = 0 then
          have hd : s 3 = 1 := by omega
          rw [eq_toFS s, ha2, hb1, hc0, hd]; exact hz_28
        else if hc1 : s 2 = 1 then
          have hd : s 3 = 0 := by omega
          rw [eq_toFS s, ha2, hb1, hc1, hd]; exact hz_29
        else omega
      else if hb2 : s 1 = 2 then
        if hc0 : s 2 = 0 then
          have hd : s 3 = 0 := by omega
          rw [eq_toFS s, ha2, hb2, hc0, hd]; exact hz_30
        else omega
      else omega
    else if ha3 : s 0 = 3 then
      if hb0 : s 1 = 0 then
        if hc0 : s 2 = 0 then
          have hd : s 3 = 1 := by omega
          rw [eq_toFS s, ha3, hb0, hc0, hd]; exact hz_31
        else if hc1 : s 2 = 1 then
          have hd : s 3 = 0 := by omega
          rw [eq_toFS s, ha3, hb0, hc1, hd]; exact hz_32
        else omega
      else if hb1 : s 1 = 1 then
        if hc0 : s 2 = 0 then
          have hd : s 3 = 0 := by omega
          rw [eq_toFS s, ha3, hb1, hc0, hd]; exact hz_33
        else omega
      else omega
    else if ha4 : s 0 = 4 then
      if hb0 : s 1 = 0 then
        if hc0 : s 2 = 0 then
          have hd : s 3 = 0 := by omega
          rw [eq_toFS s, ha4, hb0, hc0, hd]; exact hz_34
        else omega
      else omega
    else omega
  rw [hs0, map_zero]

lemma hom_zero_eq_C {Q : R4} (hQ : Q.IsHomogeneous 0) : Q = C (coeff 0 Q) := by
  conv_lhs => rw [Q.as_sum]
  by_cases h0 : (0 : Fin 4 →₀ ℕ) ∈ Q.support
  · rw [Finset.sum_eq_single 0]
    · simp [monomial_zero']
    · intro s hs hne
      exfalso; apply hne
      have hdeg : s 0 + s 1 + s 2 + s 3 = 0 := by
        have h := hQ (mem_support_iff.mp hs)
        simpa [Finsupp.weight_apply, Finsupp.sum_fintype, Fin.sum_univ_four, add_assoc] using h
      ext i; fin_cases i <;> simp <;> omega
    · intro hnot; exact absurd h0 hnot
  · rw [notMem_support_iff.mp h0, map_zero]
    apply Finset.sum_eq_zero
    intro s hs
    have hdeg : s 0 + s 1 + s 2 + s 3 = 0 := by
      have h := hQ (mem_support_iff.mp hs)
      simpa [Finsupp.weight_apply, Finsupp.sum_fintype, Fin.sum_univ_four, add_assoc] using h
    have hs_eq : s = 0 := by ext i; fin_cases i <;> simp <;> omega
    subst hs_eq
    exact absurd hs h0

lemma not_core_dvd_of_hom_le_four {d : ℕ} {D : R4}
    (hd : d ≤ 4) (hD_ne : D ≠ 0) (hD_hom : D.IsHomogeneous d) :
    ¬ (core ∣ D) := by
  rintro ⟨Q, hQ⟩
  have hQ_ne : Q ≠ 0 := by
    intro h0; apply hD_ne; rw [hQ, h0, mul_zero]
  have hex_comp : ∃ m ∈ Finset.range (Q.totalDegree + 1), homogeneousComponent m Q ≠ 0 := by
    by_contra hall
    apply hQ_ne
    rw [← sum_homogeneousComponent Q]
    apply Finset.sum_eq_zero
    intro m hm
    by_contra hne
    exact hall ⟨m, hm, hne⟩
  obtain ⟨m, hm_mem, hm_ne⟩ := hex_comp
  rw [Finset.mem_range] at hm_mem
  have hmul_comp : homogeneousComponent (6 + m) (core * Q) = core * homogeneousComponent m Q := by
    conv_lhs => rw [← sum_homogeneousComponent Q, Finset.mul_sum, map_sum]
    rw [Finset.sum_eq_single m]
    · exact homogeneousComponent_eq_self
        (FP2CoprimeStrict.core_hom.mul (homogeneousComponent_isHomogeneous m Q))
    · intro j _ hjm
      have hj_mem : core * homogeneousComponent j Q ∈
          homogeneousSubmodule (Fin 4) ℂ (6 + j) :=
        FP2CoprimeStrict.core_hom.mul (homogeneousComponent_isHomogeneous j Q)
      rw [homogeneousComponent_of_mem hj_mem, if_neg (by omega)]
    · intro hnot
      exact absurd (Finset.mem_range.mpr hm_mem) hnot
  have hlhs_zero : homogeneousComponent (6 + m) (core * Q) = 0 := by
    rw [← hQ, homogeneousComponent_of_mem hD_hom, if_neg (by omega)]
  rw [hlhs_zero] at hmul_comp
  exact hm_ne ((mul_eq_zero.mp hmul_comp.symm).resolve_left FP2CoprimeStrict.core_ne_zero)

end FP2Obstructions

theorem solution :
    (∀ (c : ℂ) (N : Fin 4 → MvPolynomial (Fin 4) ℂ),
      ¬ HodgeComputer.FourPlusTwoResidual.CoreCertificate
        (MvPolynomial.C c * HodgeComputer.FourPlusTwoResidual.core) N) ∧
    (∀ (D : MvPolynomial (Fin 4) ℂ) (N : Fin 4 → MvPolynomial (Fin 4) ℂ),
      D.IsHomogeneous 6 →
      HodgeComputer.FourPlusTwoResidual.CoreCertificate D N →
      ¬ (HodgeComputer.FourPlusTwoResidual.core ∣ D) ∧
        ∃ p : Fin 4 → MvPolynomial (Fin 4) ℂ,
          HodgeComputer.FourPlusTwoResidual.StrictCoreCertificate D p) ∧
    (∀ (d : ℕ) (D : MvPolynomial (Fin 4) ℂ) (N : Fin 4 → MvPolynomial (Fin 4) ℂ),
      d ≤ 4 → D.IsHomogeneous d →
      ¬ HodgeComputer.FourPlusTwoResidual.CoreCertificate D N) := by
  refine ⟨FP2Obstructions.no_scalar_core_cert, ?_, ?_⟩
  · intro D N hD6 hcert
    have hndvd : ¬ (HodgeComputer.FourPlusTwoResidual.core ∣ D) := by
      rintro ⟨Q, hQ⟩
      have hQ0 : Q.IsHomogeneous 0 :=
        FP2CoprimeStrict.isHomogeneous_of_mul_isHomogeneous
          FP2CoprimeStrict.core_hom FP2CoprimeStrict.core_ne_zero
          (show (HodgeComputer.FourPlusTwoResidual.core * Q).IsHomogeneous (6 + 0) from hQ ▸ hD6)
      have hQC := FP2Obstructions.hom_zero_eq_C hQ0
      have hD_eq : D = MvPolynomial.C (MvPolynomial.coeff 0 Q) *
          HodgeComputer.FourPlusTwoResidual.core := by
        conv_lhs => rw [hQ, hQC]
        ring
      exact FP2Obstructions.no_scalar_core_cert (MvPolynomial.coeff 0 Q) N (hD_eq ▸ hcert)
    exact ⟨hndvd, FP2Obstructions.coprime_strict D hndvd N hcert⟩
  · intro d D N hd hDd hcert
    have hD_ne : D ≠ 0 := hcert.1
    have hndvd := FP2Obstructions.not_core_dvd_of_hom_le_four hd hD_ne hDd
    obtain ⟨p, -, -, hp_dir, -⟩ := FP2Obstructions.coprime_strict D hndvd N hcert
    let G : MvPolynomial (Fin 4) ℂ := MvPolynomial.X 0 ^ (4 - d)
    have hG_hom : G.IsHomogeneous (4 - d) := by
      dsimp [G]
      have h1 : (MvPolynomial.X 0 ^ (4 - d) : MvPolynomial (Fin 4) ℂ).IsHomogeneous (1 * (4 - d)) :=
        (MvPolynomial.isHomogeneous_X ℂ (0 : Fin 4)).pow (4 - d)
      have heq : 1 * (4 - d) = 4 - d := by omega
      rwa [heq] at h1
    have hGD_hom : (G * D).IsHomogeneous 4 := by
      have h1 : (G * D).IsHomogeneous ((4 - d) + d) := hG_hom.mul hDd
      have heq : (4 - d) + d = 4 := by omega
      rwa [heq] at h1
    have hGD_dir : ∑ i, MvPolynomial.pderiv i HodgeComputer.FourPlusTwoResidual.core * (G * p i) =
        HodgeComputer.FourPlusTwoResidual.coreSource * (G * D) := by
      calc
        ∑ i, MvPolynomial.pderiv i HodgeComputer.FourPlusTwoResidual.core * (G * p i)
            = G * ∑ i, MvPolynomial.pderiv i HodgeComputer.FourPlusTwoResidual.core * p i := by
              rw [Finset.mul_sum]
              exact Finset.sum_congr rfl (fun i _ => by ring)
        _ = G * (HodgeComputer.FourPlusTwoResidual.coreSource * D) := by rw [hp_dir]
        _ = HodgeComputer.FourPlusTwoResidual.coreSource * (G * D) := by ring
    have hGD0 : G * D = 0 := FP2Obstructions.no_deg4_strict (fun i => G * p i) (G * D) hGD_hom hGD_dir
    have hG_ne : G ≠ 0 := by
      intro h0
      have hev := congrArg (MvPolynomial.eval ![1, 0, 0, 0]) h0
      simp [G] at hev
    exact hD_ne ((mul_eq_zero.mp hGD0).resolve_left hG_ne)
