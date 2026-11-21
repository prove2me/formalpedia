-- Prove2me | solution 1 for HodgeComputer.SymmetricSexticResidual.chart_and_target_irreducible
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-21T04:58:02.599181+00:00
-- url     : https://prove2.me/submissions/f65520f6-1ae6-4982-8083-41f1318cbe33

import Definitions.Def_HodgeComputerSymmetricChart
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Algebra.Polynomial.Eval.Irreducible
import Mathlib.Algebra.Polynomial.Degree.SmallDegree
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.RingTheory.Polynomial.Eisenstein.Basic
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section

namespace SymIrreducible
open Polynomial HodgeComputer.SymmetricSexticResidual HodgeComputer.ReflectionChart

private def atI : Ideal (Polynomial ℂ) := Ideal.span {X - C Complex.I}

private lemma atI_isPrime : atI.IsPrime :=
  (Ideal.span_singleton_prime (Polynomial.X_sub_C_ne_zero Complex.I)).mpr
    (Polynomial.prime_X_sub_C Complex.I)

/-! ### 1. Irreducibility of `SymmetricSexticResidual.F` via Eisenstein at `Y₀ - i` -/

private def QX : HodgeComputer.AmbientPoly 5 :=
  MvPolynomial.X 0 * MvPolynomial.X 1 +
    MvPolynomial.X 0 * MvPolynomial.X 2 +
    MvPolynomial.X 1 * MvPolynomial.X 2

private def QY : HodgeComputer.AmbientPoly 5 :=
  MvPolynomial.X 3 * MvPolynomial.X 4 +
    MvPolynomial.X 3 * MvPolynomial.X 5 +
    MvPolynomial.X 4 * MvPolynomial.X 5

private def compactF : HodgeComputer.AmbientPoly 5 :=
  MvPolynomial.X 0 ^ 6 + MvPolynomial.X 1 ^ 6 + MvPolynomial.X 2 ^ 6 +
    MvPolynomial.X 3 ^ 6 + MvPolynomial.X 4 ^ 6 + MvPolynomial.X 5 ^ 6 +
    MvPolynomial.C (1 / 7 : ℂ) * (5 * QX ^ 2 * QY + 10 * QX * QY ^ 2)

private lemma exactF_compact : F = compactF := by
  apply MvPolynomial.funext (σ := Fin 6)
  intro x
  simp [F, compactF, QX, QY]
  ring

private def secConstF : Polynomial ℂ := X ^ 6 + 1
private def planeSecF : Polynomial (Polynomial ℂ) := X ^ 6 + C secConstF

private lemma secConstF_mem : secConstF ∈ atI := by
  have hi6 : Complex.I ^ 6 = -1 := by
    calc
      Complex.I ^ 6 = (Complex.I ^ 2) ^ 3 := by rw [← pow_mul]
      _ = -1 := by rw [Complex.I_sq]; norm_num
  rw [atI, Ideal.mem_span_singleton, Polynomial.dvd_iff_isRoot]
  simp [secConstF, Polynomial.IsRoot, hi6]

private lemma secConstF_not_mem_sq : secConstF ∉ atI ^ 2 := by
  intro h
  rw [atI, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at h
  have hd : (X - C Complex.I : Polynomial ℂ) ∣ derivative secConstF := by
    simpa using Polynomial.pow_sub_one_dvd_derivative_of_pow_dvd h
  have he := Polynomial.dvd_iff_isRoot.mp hd
  norm_num [secConstF, Polynomial.IsRoot, Polynomial.derivative_X_pow] at he

private lemma planeSecF_irreducible : Irreducible planeSecF := by
  have hmon : planeSecF.Monic := Polynomial.monic_X_pow_add_C secConstF (by decide)
  have hdeg : planeSecF.natDegree = 6 := Polynomial.natDegree_X_pow_add_C
  have heis : planeSecF.IsEisensteinAt atI := by
    refine ⟨?_, ?_, ?_⟩
    · rw [hmon.leadingCoeff, atI, Ideal.mem_span_singleton, Polynomial.dvd_iff_isRoot]
      simp [Polynomial.IsRoot]
    · intro n hn
      rw [hdeg] at hn
      by_cases hn0 : n = 0
      · subst hn0; simpa [planeSecF] using secConstF_mem
      · have h6n : 6 ≠ n := by omega
        simp [planeSecF, Polynomial.coeff_X_pow, Polynomial.coeff_C, hn0, Ne.symm h6n]
    · simpa [planeSecF] using secConstF_not_mem_sq
  exact heis.irreducible atI_isPrime hmon.isPrimitive (by rw [hdeg]; decide)

private abbrev CoeffRing5 := MvPolynomial (Fin 5) ℂ
private def univF : Polynomial CoeffRing5 := MvPolynomial.finSuccEquiv ℂ 5 F

private def restQY : CoeffRing5 :=
  MvPolynomial.X 2 * MvPolynomial.X 3 +
    MvPolynomial.X 2 * MvPolynomial.X 4 +
    MvPolynomial.X 3 * MvPolynomial.X 4

private def cF2 : CoeffRing5 :=
  MvPolynomial.C (1 / 7 : ℂ) * (5 * (MvPolynomial.X 0 + MvPolynomial.X 1) ^ 2 * restQY)

private def cF1 : CoeffRing5 :=
  MvPolynomial.C (1 / 7 : ℂ) *
    (10 * (MvPolynomial.X 0 + MvPolynomial.X 1) * (MvPolynomial.X 0 * MvPolynomial.X 1) * restQY +
      10 * (MvPolynomial.X 0 + MvPolynomial.X 1) * restQY ^ 2)

private def cF0 : CoeffRing5 :=
  MvPolynomial.X 0 ^ 6 + MvPolynomial.X 1 ^ 6 +
    MvPolynomial.X 2 ^ 6 + MvPolynomial.X 3 ^ 6 + MvPolynomial.X 4 ^ 6 +
    MvPolynomial.C (1 / 7 : ℂ) *
      (5 * (MvPolynomial.X 0 * MvPolynomial.X 1) ^ 2 * restQY +
        10 * (MvPolynomial.X 0 * MvPolynomial.X 1) * restQY ^ 2)

private lemma univF_formula :
    univF = X ^ 6 + (C cF2 * X ^ 2 + C cF1 * X + C cF0) := by
  have hX : ∀ i : Fin 6, MvPolynomial.finSuccEquiv ℂ 5 (MvPolynomial.X i) =
      ![Polynomial.X, C (MvPolynomial.X 0), C (MvPolynomial.X 1),
        C (MvPolynomial.X 2), C (MvPolynomial.X 3), C (MvPolynomial.X 4)] i := by
    intro i; fin_cases i <;> simp [MvPolynomial.finSuccEquiv_apply] <;> rfl
  have hC : ∀ c : ℂ, MvPolynomial.finSuccEquiv ℂ 5 (MvPolynomial.C c) = C (MvPolynomial.C c) := by
    intro c; simp [MvPolynomial.finSuccEquiv_apply]
  rw [univF, exactF_compact]
  simp [hX, hC, compactF, QX, QY, cF2, cF1, cF0, restQY, map_ofNat]
  ring

private lemma target_irreducible : Irreducible F := by
  have hmon : univF.Monic := by
    rw [univF_formula]
    exact Polynomial.monic_X_pow_add (lt_of_le_of_lt Polynomial.degree_quadratic_le (by norm_num))
  let spec5 : CoeffRing5 →+* Polynomial ℂ :=
    MvPolynomial.eval₂Hom Polynomial.C ![0, 0, Polynomial.X, 1, 0]
  have hspec : univF.map spec5 = planeSecF := by
    rw [univF_formula]
    simp [spec5, cF2, cF1, cF0, restQY, planeSecF, secConstF]
  have hu : Irreducible univF :=
    Polynomial.Monic.irreducible_of_irreducible_map spec5 univF hmon (hspec ▸ planeSecF_irreducible)
  exact (MulEquiv.irreducible_iff (MvPolynomial.finSuccEquiv ℂ 5)).mp hu

/-! ### 2. Irreducibility of `squareLift symWeighted` via Eisenstein in `b` at `v - i` -/

private def secConstH : Polynomial ℂ := 2 + 30 * X ^ 2 + 30 * X ^ 4 + 2 * X ^ 6
private def planeSecH : Polynomial (Polynomial ℂ) := X ^ 6 + C secConstH

private lemma secConstH_mem : secConstH ∈ atI := by
  have hi6 : Complex.I ^ 6 = -1 := by
    calc
      Complex.I ^ 6 = (Complex.I ^ 2) ^ 3 := by rw [← pow_mul]
      _ = -1 := by rw [Complex.I_sq]; norm_num
  rw [atI, Ideal.mem_span_singleton, Polynomial.dvd_iff_isRoot]
  norm_num [secConstH, Polynomial.IsRoot, hi6]

private lemma secConstH_not_mem_sq : secConstH ∉ atI ^ 2 := by
  intro h
  rw [atI, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at h
  have hd : (X - C Complex.I : Polynomial ℂ) ∣ derivative secConstH := by
    simpa using Polynomial.pow_sub_one_dvd_derivative_of_pow_dvd h
  have he := Polynomial.dvd_iff_isRoot.mp hd
  have hi5 : Complex.I ^ 5 = Complex.I := by
    calc
      Complex.I ^ 5 = Complex.I ^ 4 * Complex.I := pow_succ _ _
      _ = Complex.I := by rw [Complex.I_pow_four, one_mul]
  norm_num [secConstH, Polynomial.IsRoot, Polynomial.derivative_X_pow, hi5] at he
  have hz : Complex.I = 0 := by linear_combination (-1 / 48 : ℂ) * he
  exact Complex.I_ne_zero hz

private lemma planeSecH_irreducible : Irreducible planeSecH := by
  have hmon : planeSecH.Monic := Polynomial.monic_X_pow_add_C secConstH (by decide)
  have hdeg : planeSecH.natDegree = 6 := Polynomial.natDegree_X_pow_add_C
  have heis : planeSecH.IsEisensteinAt atI := by
    refine ⟨?_, ?_, ?_⟩
    · rw [hmon.leadingCoeff, atI, Ideal.mem_span_singleton, Polynomial.dvd_iff_isRoot]
      simp [Polynomial.IsRoot]
    · intro n hn
      rw [hdeg] at hn
      by_cases hn0 : n = 0
      · subst hn0; simpa [planeSecH] using secConstH_mem
      · have h6n : 6 ≠ n := by omega
        simp [planeSecH, Polynomial.coeff_X_pow, Polynomial.coeff_C, hn0, Ne.symm h6n]
    · simpa [planeSecH] using secConstH_not_mem_sq
  exact heis.irreducible atI_isPrime hmon.isPrimitive (by rw [hdeg]; decide)

private abbrev CoeffRing4 := MvPolynomial (Fin 4) ℂ
private def bFirst : ChartPoly ≃ₐ[ℂ] Polynomial CoeffRing4 :=
  (MvPolynomial.renameEquiv ℂ (Equiv.swap (0 : Fin 5) 1)).trans (MvPolynomial.finSuccEquiv ℂ 4)

private def univH : Polynomial CoeffRing4 := bFirst (squareLift symWeighted)

private def t4 : CoeffRing4 := 1 - MvPolynomial.X 3 ^ 2
private def q4 : CoeffRing4 :=
  MvPolynomial.X 1 ^ 2 + 2 * MvPolynomial.X 1 * MvPolynomial.X 2 -
    MvPolynomial.X 0 ^ 2 * MvPolynomial.X 3 ^ 2

private def cH2 : CoeffRing4 := 4 * MvPolynomial.C (5 / 7 : ℂ) * q4
private def cH1 : CoeffRing4 :=
  4 * MvPolynomial.C (5 / 7 : ℂ) * t4 * q4 + 2 * MvPolynomial.C (10 / 7 : ℂ) * q4 ^ 2
private def cH0 : CoeffRing4 :=
  2 + 2 * MvPolynomial.X 1 ^ 6 + MvPolynomial.X 2 ^ 6 +
    30 * MvPolynomial.X 3 ^ 2 + 30 * MvPolynomial.X 3 ^ 4 + 2 * MvPolynomial.X 3 ^ 6 +
    30 * MvPolynomial.X 0 ^ 2 * MvPolynomial.X 1 ^ 4 * MvPolynomial.X 3 ^ 2 +
    30 * MvPolynomial.X 0 ^ 4 * MvPolynomial.X 1 ^ 2 * MvPolynomial.X 3 ^ 4 +
    2 * MvPolynomial.X 0 ^ 6 * MvPolynomial.X 3 ^ 6 +
    MvPolynomial.C (5 / 7 : ℂ) * t4 ^ 2 * q4 +
    MvPolynomial.C (10 / 7 : ℂ) * t4 * q4 ^ 2

private lemma univH_formula :
    univH = X ^ 6 + (C cH2 * X ^ 2 + C cH1 * X + C cH0) := by
  have hbX : ∀ i : Fin 5, bFirst (MvPolynomial.X i) =
      ![C (MvPolynomial.X 0), Polynomial.X, C (MvPolynomial.X 1),
        C (MvPolynomial.X 2), C (MvPolynomial.X 3)] i := by
    intro i; fin_cases i <;>
      norm_num [bFirst, MvPolynomial.renameEquiv_apply, MvPolynomial.finSuccEquiv_apply,
        Equiv.swap_apply_def] <;> rfl
  have hbC : ∀ c : ℂ, bFirst (MvPolynomial.C c) = C (MvPolynomial.C c) := by
    intro c; simp [bFirst, MvPolynomial.renameEquiv_apply, MvPolynomial.finSuccEquiv_apply]
  simp [univH, symWeighted, leftQuadric, rightQuadric, squareLift, hbX, hbC,
    cH2, cH1, cH0, t4, q4, map_ofNat]
  ring

private lemma chart_irreducible : Irreducible (squareLift symWeighted) := by
  have hmon : univH.Monic := by
    rw [univH_formula]
    exact Polynomial.monic_X_pow_add (lt_of_le_of_lt Polynomial.degree_quadratic_le (by norm_num))
  let spec4 : CoeffRing4 →+* Polynomial ℂ :=
    MvPolynomial.eval₂Hom Polynomial.C ![0, 0, 0, Polynomial.X]
  have hspec : univH.map spec4 = planeSecH := by
    rw [univH_formula]
    simp [spec4, cH2, cH1, cH0, t4, q4, planeSecH, secConstH, map_ofNat]
  have hu : Irreducible univH :=
    Polynomial.Monic.irreducible_of_irreducible_map spec4 univH hmon (hspec ▸ planeSecH_irreducible)
  exact (MulEquiv.irreducible_iff bFirst).mp hu

end SymIrreducible

theorem solution :
    Irreducible HodgeComputer.SymmetricSexticResidual.F ∧
      Irreducible (HodgeComputer.ReflectionChart.squareLift
        HodgeComputer.SymmetricSexticResidual.symWeighted) :=
  ⟨SymIrreducible.target_irreducible, SymIrreducible.chart_irreducible⟩
