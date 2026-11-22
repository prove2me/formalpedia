-- Prove2me | solution 1 for HodgeComputer.FourPlusTwoResidual.core_irreducible
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-21T08:25:43.016191+00:00
-- url     : https://prove2.me/submissions/508b752b-ebd1-4528-a49e-a37536d76fa2

import Definitions.Def_HodgeComputerFourPlusTwoCore
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.Polynomial.Degree.SmallDegree
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Eval.Irreducible
import Mathlib.Analysis.Complex.Polynomial.Basic
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

theorem solution : Irreducible HodgeComputer.FourPlusTwoResidual.core :=
  FP2CoreIrreducible.core_irreducible_proof
