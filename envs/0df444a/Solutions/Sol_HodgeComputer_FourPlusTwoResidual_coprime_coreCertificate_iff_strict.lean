-- Prove2me | solution 1 for HodgeComputer.FourPlusTwoResidual.coprime_coreCertificate_iff_strict
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-21T08:25:43.762227+00:00
-- url     : https://prove2.me/submissions/b55d06b2-1c88-448b-b379-369c588014f8

import Definitions.Def_HodgeComputerFourPlusTwoSymmetry
import Mathlib.Algebra.MvPolynomial.Equiv
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

theorem solution
    (D : MvPolynomial (Fin 4) ℂ) (hndvd : ¬ (HodgeComputer.FourPlusTwoResidual.core ∣ D)) :
    (∃ N : Fin 4 → MvPolynomial (Fin 4) ℂ,
      HodgeComputer.FourPlusTwoResidual.CoreCertificate D N) ↔
    (∃ p : Fin 4 → MvPolynomial (Fin 4) ℂ,
      HodgeComputer.FourPlusTwoResidual.StrictCoreCertificate D p) := by
  constructor
  · rintro ⟨u, hD_ne, ⟨k, hDk, hUk⟩, hc⟩
    have hprime : Prime core := UniqueFactorizationMonoid.irreducible_iff_prime.mp FP2CoprimeStrict.core_irred
    let M : MvPolynomial (Fin 4) ℂ := D * (∑ i, pderiv i (u i)) - ∑ i, pderiv i D * u i
    have hdiv_H : core ∣ D * (2 * ((∑ i, pderiv i core * u i) - coreSource * D)) := by
      refine ⟨3 * M, ?_⟩
      dsimp [M]; linear_combination -hc
    have hdiv2 : core ∣ 2 * ((∑ i, pderiv i core * u i) - coreSource * D) :=
      (hprime.dvd_or_dvd hdiv_H).resolve_left hndvd
    obtain ⟨R2, hR2⟩ := hdiv2
    let R : MvPolynomial (Fin 4) ℂ := C (1 / 2 : ℂ) * R2
    have hR : (∑ i, pderiv i core * u i) - coreSource * D = core * R := by
      have hhalf : C (1 / 2 : ℂ) * (2 : MvPolynomial (Fin 4) ℂ) = 1 := by
        rw [← map_ofNat C 2, ← map_mul]; norm_num
      calc
        (∑ i, pderiv i core * u i) - coreSource * D
            = C (1 / 2 : ℂ) * (2 * ((∑ i, pderiv i core * u i) - coreSource * D)) := by
              linear_combination -(∑ i, pderiv i core * u i - coreSource * D) * hhalf
        _ = C (1 / 2 : ℂ) * (core * R2) := by rw [hR2]
        _ = core * R := by dsimp [R]; ring
    have hLHS_hom : ((∑ i, pderiv i core * u i) - coreSource * D).IsHomogeneous (6 + (k + 1)) := by
      have h1 : (∑ i, pderiv i core * u i).IsHomogeneous (6 + (k + 1)) := by
        apply IsHomogeneous.sum
        intro i _
        have hp := (FP2CoprimeStrict.core_hom.pderiv (i := i)).mul (hUk i)
        convert hp using 1; omega
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
    let p : Fin 4 → MvPolynomial (Fin 4) ℂ := fun i => u i - C (1 / 6 : ℂ) * R * X i
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
          (∑ i : Fin 4, pderiv i core * u i) -
            C (1 / 6 : ℂ) * R * (∑ i : Fin 4, pderiv i core * X i) := by
        simp only [p, mul_sub, Finset.sum_sub_distrib, h_pull]
      have hsixth : C (1 / 6 : ℂ) * (6 : MvPolynomial (Fin 4) ℂ) = 1 := by
        rw [← map_ofNat C 6, ← map_mul]; norm_num
      rw [hsum_p, hE_H]
      linear_combination hR - core * R * hsixth
    · have hE_R : (∑ i : Fin 4, X i * pderiv i R) = ((k + 1 : ℕ) : MvPolynomial (Fin 4) ℂ) * R := by
        simpa [nsmul_eq_mul] using hR_hom.sum_X_mul_pderiv
      have hE_D : (∑ i : Fin 4, pderiv i D * X i) = ((k + 1 : ℕ) : MvPolynomial (Fin 4) ℂ) * D := by
        calc
          (∑ i : Fin 4, pderiv i D * X i) = ∑ i : Fin 4, X i * pderiv i D :=
            Finset.sum_congr rfl (fun i _ => by ring)
          _ = (k + 1) • D := hDk.sum_X_mul_pderiv
          _ = ((k + 1 : ℕ) : MvPolynomial (Fin 4) ℂ) * D := by simp [nsmul_eq_mul]
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
      have htwo_thirds : C (1 / 6 : ℂ) * (4 : MvPolynomial (Fin 4) ℂ) *
          (3 : MvPolynomial (Fin 4) ℂ) = 2 := by
        rw [← map_ofNat C 4, ← map_ofNat C 3, ← map_mul, ← map_mul]
        norm_num
        exact map_ofNat C 2
      have h3_ne : (3 : MvPolynomial (Fin 4) ℂ) ≠ 0 := by
        rw [← map_ofNat C 3, Ne, C_eq_zero]; norm_num
      apply mul_left_cancel₀ h3_ne
      rw [mul_zero, hexp, hdiv_RX, hdir_D, hE_R, hE_D]
      linear_combination h3M - D * R * htwo_thirds
  · rintro ⟨p, hD_ne, ⟨k, hDk, hpk⟩, hp_dir, hp_div⟩
    refine ⟨p, hD_ne, ⟨k, hDk, hpk⟩, ?_⟩
    rw [hp_dir, hp_div]
    ring
