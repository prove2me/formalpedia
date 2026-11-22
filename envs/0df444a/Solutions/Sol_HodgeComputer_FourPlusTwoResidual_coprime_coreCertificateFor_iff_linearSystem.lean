-- Prove2me | solution 1 for HodgeComputer.FourPlusTwoResidual.coprime_coreCertificateFor_iff_linearSystem
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-21T13:53:38.938792+00:00
-- url     : https://prove2.me/submissions/a70a3580-8781-4e74-a7d1-f9fde5464b6b

import Definitions.Def_HodgeComputerFourPlusTwoSourceAlgebra
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.Polynomial.Degree.SmallDegree
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Eval.Irreducible
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.RingTheory.MvPolynomial.EulerIdentity
import Mathlib.RingTheory.Polynomial.Eisenstein.Basic
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section

namespace FP3CoreIrred

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

end FP3CoreIrred

namespace FP3CoprimeLinear

open MvPolynomial HodgeComputer.FourPlusTwoResidual
open scoped BigOperators

private abbrev R4 := MvPolynomial (Fin 4) ℂ

lemma isHomogeneous_of_mul_isHomogeneous
    {P R : R4} {a b : ℕ}
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

lemma isRelPrime_of_not_core_dvd {D : R4} (hndvd : ¬ (core ∣ D)) : IsRelPrime D core := by
  have hirr : Irreducible core := FP3CoreIrred.core_irreducible_proof
  intro u huD huc
  obtain ⟨v, hv⟩ := huc
  rcases hirr.isUnit_or_isUnit hv with hu | hv_unit
  · exact hu
  · exfalso
    obtain ⟨w, hw⟩ := hv_unit.exists_right_inv
    have hcu : u = core * w := by rw [hv, mul_assoc, hw, mul_one]
    exact hndvd (dvd_trans ⟨w, hcu⟩ huD)

end FP3CoprimeLinear

theorem solution
    (d : ℕ) (S D : MvPolynomial (Fin 4) ℂ) (N : Fin 4 → MvPolynomial (Fin 4) ℂ)
    (_hS : S.IsHomogeneous 6) (hD_ne : D ≠ 0) (hDd : D.IsHomogeneous d)
    (hNd : ∀ i, (N i).IsHomogeneous (d + 1))
    (hndvd : ¬ (HodgeComputer.FourPlusTwoResidual.core ∣ D)) :
    HodgeComputer.FourPlusTwoResidual.CoreCertificateFor S D N ↔
      ∃ T : MvPolynomial (Fin 4) ℂ,
        T.IsHomogeneous d ∧
          HodgeComputer.FourPlusTwoResidual.CoprimeLinearCoreSystem S D N T := by
  open MvPolynomial HodgeComputer.FourPlusTwoResidual in
  constructor
  · rintro ⟨-, -, hres⟩
    have hrel : IsRelPrime D core := FP3CoprimeLinear.isRelPrime_of_not_core_dvd hndvd
    have hdvd_prod : D ∣ core * (3 * ∑ i, pderiv i D * N i) := by
      refine ⟨2 * S * D - 2 * (∑ i, pderiv i core * N i) + 3 * core * (∑ i, pderiv i (N i)), ?_⟩
      unfold coreResidual at hres
      linear_combination -hres
    have hdvd3 : D ∣ 3 * ∑ i, pderiv i D * N i :=
      hrel.dvd_of_dvd_mul_left hdvd_prod
    obtain ⟨T3, hT3⟩ := hdvd3
    let T : MvPolynomial (Fin 4) ℂ := C (1 / 3 : ℂ) * T3
    have hDT : ∑ i, pderiv i D * N i = D * T := by
      have hthird : C (1 / 3 : ℂ) * (3 : MvPolynomial (Fin 4) ℂ) = 1 := by
        rw [← map_ofNat C 3, ← map_mul]; norm_num
      calc
        ∑ i, pderiv i D * N i
            = C (1 / 3 : ℂ) * (3 * ∑ i, pderiv i D * N i) := by
              linear_combination -(∑ i, pderiv i D * N i) * hthird
        _ = C (1 / 3 : ℂ) * (D * T3) := by rw [hT3]
        _ = D * T := by dsimp [T]; ring
    have hT_hom : T.IsHomogeneous d := by
      by_cases hd0 : d = 0
      · subst hd0
        have hp0 : ∀ i : Fin 4, pderiv i D = 0 := by
          intro i
          rw [D.as_sum, map_sum]
          apply Finset.sum_eq_zero
          intro s hs
          have hdeg : s 0 + s 1 + s 2 + s 3 = 0 := by
            have h := hDd (mem_support_iff.mp hs)
            simpa [Finsupp.weight_apply, Finsupp.sum_fintype, Fin.sum_univ_four, add_assoc] using h
          have hs0 : s = 0 := by
            ext j
            fin_cases j
            · simp; omega
            · simp; omega
            · simp; omega
            · simp; omega
          rw [hs0, monomial_zero', pderiv_C]
        have hsum0 : (∑ i, pderiv i D * N i) = 0 := by simp [hp0]
        rw [hsum0] at hDT
        have hT0 : T = 0 := (mul_eq_zero.mp hDT.symm).resolve_left hD_ne
        rw [hT0]
        exact isHomogeneous_zero _ _ _
      · have hsum_hom : (∑ i, pderiv i D * N i).IsHomogeneous (d + d) := by
          apply IsHomogeneous.sum
          intro i _
          have h := (hDd.pderiv (i := i)).mul (hNd i)
          have heq : (d - 1) + (d + 1) = d + d := by omega
          rwa [heq] at h
        rw [hDT] at hsum_hom
        exact FP3CoprimeLinear.isHomogeneous_of_mul_isHomogeneous hDd hD_ne hsum_hom
    have heq2 : 2 * S * D - 2 * (∑ i, pderiv i core * N i) +
        3 * core * ((∑ i, pderiv i (N i)) - T) = 0 := by
      have hmul0 : D * (2 * S * D - 2 * (∑ i, pderiv i core * N i) +
          3 * core * ((∑ i, pderiv i (N i)) - T)) = 0 := by
        unfold coreResidual at hres
        linear_combination hres + 3 * core * hDT
      exact (mul_eq_zero.mp hmul0).resolve_left hD_ne
    exact ⟨T, hT_hom, hDT, heq2⟩
  · rintro ⟨T, _, hDT, heq2⟩
    refine ⟨hD_ne, ⟨d, hDd, hNd⟩, ?_⟩
    unfold coreResidual
    linear_combination D * heq2 - 3 * core * hDT
