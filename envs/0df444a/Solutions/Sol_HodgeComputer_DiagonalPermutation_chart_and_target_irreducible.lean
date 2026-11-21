-- Prove2me | solution 1 for HodgeComputer.DiagonalPermutation.chart_and_target_irreducible
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-21T04:58:03.317414+00:00
-- url     : https://prove2.me/submissions/c2db8c9e-dbaf-49d7-929c-91941297add2

import Definitions.Def_HodgeComputerDiagonalPermutationQuotient
import Mathlib.Algebra.MvPolynomial.Equiv
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

namespace DiagIrreducible
open Polynomial HodgeComputer.DiagonalPermutation HodgeComputer.ReflectionChart

private def atI : Ideal (Polynomial ℂ) := Ideal.span {X - C Complex.I}

private lemma atI_isPrime : atI.IsPrime :=
  (Ideal.span_singleton_prime (Polynomial.X_sub_C_ne_zero Complex.I)).mpr
    (Polynomial.prime_X_sub_C Complex.I)

/-! ### 1. Irreducibility of `DiagonalPermutation.F` via Eisenstein at `Y₀ - i` -/

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

-- Coefficients of X_0^3, X_0^2, X_0^1, X_0^0 in DiagonalPermutation.F
-- Remaining variables in CoeffRing5: 0=X1, 1=X2, 2=Y0, 3=Y1, 4=Y2
private def cF3 : CoeffRing5 :=
  MvPolynomial.C (5 / 7 : ℂ) * MvPolynomial.X 0 * MvPolynomial.X 2 * MvPolynomial.X 3 +
    MvPolynomial.C (5 / 11 : ℂ) * MvPolynomial.X 0 * MvPolynomial.X 4 ^ 2 +
    MvPolynomial.C (5 / 7 : ℂ) * MvPolynomial.X 1 * MvPolynomial.X 2 * MvPolynomial.X 4 +
    MvPolynomial.C (5 / 11 : ℂ) * MvPolynomial.X 1 * MvPolynomial.X 3 ^ 2

private def cF2 : CoeffRing5 :=
  MvPolynomial.C (5 / 13 : ℂ) * MvPolynomial.X 3 ^ 3 * MvPolynomial.X 4 +
    MvPolynomial.C (5 / 13 : ℂ) * MvPolynomial.X 3 * MvPolynomial.X 4 ^ 3

private def cF1 : CoeffRing5 :=
  MvPolynomial.C (5 / 7 : ℂ) * MvPolynomial.X 0 ^ 3 * MvPolynomial.X 2 * MvPolynomial.X 3 +
    MvPolynomial.C (5 / 11 : ℂ) * MvPolynomial.X 0 ^ 3 * MvPolynomial.X 4 ^ 2 +
    MvPolynomial.C (5 / 7 : ℂ) * MvPolynomial.X 1 ^ 3 * MvPolynomial.X 2 * MvPolynomial.X 4 +
    MvPolynomial.C (5 / 11 : ℂ) * MvPolynomial.X 1 ^ 3 * MvPolynomial.X 3 ^ 2

private def cF0 : CoeffRing5 :=
  MvPolynomial.X 0 ^ 6 +
    MvPolynomial.C (5 / 11 : ℂ) * MvPolynomial.X 0 ^ 3 * MvPolynomial.X 1 * MvPolynomial.X 2 ^ 2 +
    MvPolynomial.C (5 / 7 : ℂ) * MvPolynomial.X 0 ^ 3 * MvPolynomial.X 1 * MvPolynomial.X 3 * MvPolynomial.X 4 +
    MvPolynomial.C (5 / 13 : ℂ) * MvPolynomial.X 0 ^ 2 * MvPolynomial.X 2 ^ 3 * MvPolynomial.X 4 +
    MvPolynomial.C (5 / 13 : ℂ) * MvPolynomial.X 0 ^ 2 * MvPolynomial.X 2 * MvPolynomial.X 4 ^ 3 +
    MvPolynomial.C (5 / 11 : ℂ) * MvPolynomial.X 0 * MvPolynomial.X 1 ^ 3 * MvPolynomial.X 2 ^ 2 +
    MvPolynomial.C (5 / 7 : ℂ) * MvPolynomial.X 0 * MvPolynomial.X 1 ^ 3 * MvPolynomial.X 3 * MvPolynomial.X 4 +
    MvPolynomial.X 1 ^ 6 +
    MvPolynomial.C (5 / 13 : ℂ) * MvPolynomial.X 1 ^ 2 * MvPolynomial.X 2 ^ 3 * MvPolynomial.X 3 +
    MvPolynomial.C (5 / 13 : ℂ) * MvPolynomial.X 1 ^ 2 * MvPolynomial.X 2 * MvPolynomial.X 3 ^ 3 +
    MvPolynomial.X 2 ^ 6 + MvPolynomial.X 3 ^ 6 + MvPolynomial.X 4 ^ 6

private lemma univF_formula :
    univF = X ^ 6 + (C cF3 * X ^ 3 + C cF2 * X ^ 2 + C cF1 * X + C cF0) := by
  have hX0 : MvPolynomial.finSuccEquiv ℂ 5 (MvPolynomial.X 0) = Polynomial.X := by
    simp [MvPolynomial.finSuccEquiv_apply]
  have hX1 : MvPolynomial.finSuccEquiv ℂ 5 (MvPolynomial.X 1) = C (MvPolynomial.X 0) := by
    simp [MvPolynomial.finSuccEquiv_apply]; rfl
  have hX2 : MvPolynomial.finSuccEquiv ℂ 5 (MvPolynomial.X 2) = C (MvPolynomial.X 1) := by
    simp [MvPolynomial.finSuccEquiv_apply]; rfl
  have hX3 : MvPolynomial.finSuccEquiv ℂ 5 (MvPolynomial.X 3) = C (MvPolynomial.X 2) := by
    simp [MvPolynomial.finSuccEquiv_apply]; rfl
  have hX4 : MvPolynomial.finSuccEquiv ℂ 5 (MvPolynomial.X 4) = C (MvPolynomial.X 3) := by
    simp [MvPolynomial.finSuccEquiv_apply]; rfl
  have hX5 : MvPolynomial.finSuccEquiv ℂ 5 (MvPolynomial.X 5) = C (MvPolynomial.X 4) := by
    simp [MvPolynomial.finSuccEquiv_apply]; rfl
  have hC : ∀ c : ℂ, MvPolynomial.finSuccEquiv ℂ 5 (MvPolynomial.C c) = C (MvPolynomial.C c) := by
    intro c; simp [MvPolynomial.finSuccEquiv_apply]
  have h57 : MvPolynomial.C (5 / 7 : ℂ) = MvPolynomial.C (1 / 7 : ℂ) * (5 : CoeffRing5) := by
    rw [← map_ofNat MvPolynomial.C 5, ← map_mul]; norm_num
  have h511 : MvPolynomial.C (5 / 11 : ℂ) = MvPolynomial.C (1 / 11 : ℂ) * (5 : CoeffRing5) := by
    rw [← map_ofNat MvPolynomial.C 5, ← map_mul]; norm_num
  have h513 : MvPolynomial.C (5 / 13 : ℂ) = MvPolynomial.C (1 / 13 : ℂ) * (5 : CoeffRing5) := by
    rw [← map_ofNat MvPolynomial.C 5, ← map_mul]; norm_num
  unfold univF F cF3 cF2 cF1 cF0
  rw [h57, h511, h513]
  simp only [map_add, map_mul, map_pow, map_ofNat, hX0, hX1, hX2, hX3, hX4, hX5, hC]
  ring

private lemma deg_cubic_lt_six (a3 a2 a1 a0 : CoeffRing5) :
    (C a3 * X ^ 3 + C a2 * X ^ 2 + C a1 * X + C a0).degree < (6 : WithBot ℕ) := by
  have hd3 : (C a3 * X ^ 3).degree ≤ 3 := Polynomial.degree_C_mul_X_pow_le 3 a3
  have hd2 : (C a2 * X ^ 2).degree ≤ 2 := Polynomial.degree_C_mul_X_pow_le 2 a2
  have hd1 : (C a1 * X).degree ≤ 1 := by simpa using Polynomial.degree_C_mul_X_pow_le 1 a1
  have hd0 : (C a0).degree ≤ 0 := Polynomial.degree_C_le
  have h32 : (C a3 * X ^ 3 + C a2 * X ^ 2).degree ≤ 3 :=
    (Polynomial.degree_add_le _ _).trans (max_le hd3 (hd2.trans (by decide)))
  have h321 : (C a3 * X ^ 3 + C a2 * X ^ 2 + C a1 * X).degree ≤ 3 :=
    (Polynomial.degree_add_le _ _).trans (max_le h32 (hd1.trans (by decide)))
  have h3210 : (C a3 * X ^ 3 + C a2 * X ^ 2 + C a1 * X + C a0).degree ≤ 3 :=
    (Polynomial.degree_add_le _ _).trans (max_le h321 (hd0.trans (by decide)))
  exact lt_of_le_of_lt h3210 (by decide)

private lemma target_irreducible : Irreducible F := by
  have hmon : univF.Monic := by
    rw [univF_formula]
    exact Polynomial.monic_X_pow_add (deg_cubic_lt_six cF3 cF2 cF1 cF0)
  let spec5 : CoeffRing5 →+* Polynomial ℂ :=
    MvPolynomial.eval₂Hom Polynomial.C ![0, 0, Polynomial.X, 1, 0]
  have hspec : univF.map spec5 = planeSecF := by
    rw [univF_formula]
    simp [spec5, cF3, cF2, cF1, cF0, planeSecF, secConstF]
  have hu : Irreducible univF :=
    Polynomial.Monic.irreducible_of_irreducible_map spec5 univF hmon (hspec ▸ planeSecF_irreducible)
  exact (MulEquiv.irreducible_iff (MvPolynomial.finSuccEquiv ℂ 5)).mp hu

/-! ### 2. Irreducibility of `squareLift diagWeighted` via Eisenstein in `b` at `v - i` -/

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

private def univH : Polynomial CoeffRing4 := bFirst (squareLift diagWeighted)

-- In CoeffRing4, variables are 0=lam, 1=c, 2=d, 3=v; Polynomial.X is b!
private def cH3 : CoeffRing4 :=
  (MvPolynomial.C (10 / 7 : ℂ) * MvPolynomial.X 0 * MvPolynomial.X 2 -
    MvPolynomial.C (20 / 11 : ℂ) * MvPolynomial.X 0 * MvPolynomial.X 1 +
    MvPolynomial.C (10 / 11 : ℂ) * MvPolynomial.X 0 ^ 2) * MvPolynomial.X 3 ^ 2 +
    (MvPolynomial.C (10 / 7 : ℂ) * MvPolynomial.X 1 * MvPolynomial.X 2 +
      MvPolynomial.C (10 / 11 : ℂ) * MvPolynomial.X 1 ^ 2)

private def cH2 : CoeffRing4 :=
  -MvPolynomial.C (10 / 13 : ℂ) * MvPolynomial.X 0 ^ 4 * MvPolynomial.X 3 ^ 4 +
    MvPolynomial.C (10 / 13 : ℂ) * MvPolynomial.X 1 ^ 4

private def cH1 : CoeffRing4 :=
  (MvPolynomial.C (10 / 7 : ℂ) * MvPolynomial.X 0 * MvPolynomial.X 2 -
    MvPolynomial.C (20 / 11 : ℂ) * MvPolynomial.X 0 * MvPolynomial.X 1 +
    MvPolynomial.C (30 / 11 : ℂ) * MvPolynomial.X 0 ^ 2) * MvPolynomial.X 3 ^ 4 +
    (MvPolynomial.C (30 / 7 : ℂ) * MvPolynomial.X 1 * MvPolynomial.X 2 +
      MvPolynomial.C (30 / 11 : ℂ) * MvPolynomial.X 1 ^ 2 +
      MvPolynomial.C (30 / 7 : ℂ) * MvPolynomial.X 0 * MvPolynomial.X 2 -
      MvPolynomial.C (60 / 11 : ℂ) * MvPolynomial.X 0 * MvPolynomial.X 1 +
      MvPolynomial.C (10 / 11 : ℂ) * MvPolynomial.X 0 ^ 2) * MvPolynomial.X 3 ^ 2 +
    (MvPolynomial.C (10 / 7 : ℂ) * MvPolynomial.X 1 * MvPolynomial.X 2 +
      MvPolynomial.C (10 / 11 : ℂ) * MvPolynomial.X 1 ^ 2)

private def cH0 : CoeffRing4 :=
  (MvPolynomial.C 2 + MvPolynomial.C (10 / 7 : ℂ) * MvPolynomial.X 0 ^ 2 +
    MvPolynomial.C 2 * MvPolynomial.X 0 ^ 6) * MvPolynomial.X 3 ^ 6 +
    (MvPolynomial.C 30 - MvPolynomial.C (10 / 11 : ℂ) * MvPolynomial.X 2 ^ 2 -
      MvPolynomial.C (10 / 7 : ℂ) * MvPolynomial.X 1 ^ 2 +
      MvPolynomial.C (30 / 13 : ℂ) * MvPolynomial.X 0 ^ 2 * MvPolynomial.X 1 * MvPolynomial.X 2 -
      MvPolynomial.C (20 / 13 : ℂ) * MvPolynomial.X 0 ^ 3 * MvPolynomial.X 2 +
      MvPolynomial.C 30 * MvPolynomial.X 0 ^ 4 * MvPolynomial.X 1 ^ 2) * MvPolynomial.X 3 ^ 4 +
    (MvPolynomial.C 30 + MvPolynomial.C (10 / 13 : ℂ) * MvPolynomial.X 1 * MvPolynomial.X 2 ^ 3 +
      MvPolynomial.C (10 / 13 : ℂ) * MvPolynomial.X 1 ^ 3 * MvPolynomial.X 2 -
      MvPolynomial.C (20 / 13 : ℂ) * MvPolynomial.X 0 * MvPolynomial.X 2 ^ 3 -
      MvPolynomial.C (60 / 13 : ℂ) * MvPolynomial.X 0 * MvPolynomial.X 1 ^ 2 * MvPolynomial.X 2 -
      MvPolynomial.C (10 / 7 : ℂ) * MvPolynomial.X 0 ^ 2 +
      MvPolynomial.C (30 / 13 : ℂ) * MvPolynomial.X 0 ^ 2 * MvPolynomial.X 1 * MvPolynomial.X 2 +
      MvPolynomial.C 30 * MvPolynomial.X 0 ^ 2 * MvPolynomial.X 1 ^ 4) * MvPolynomial.X 3 ^ 2 +
    (MvPolynomial.C 2 + MvPolynomial.C (10 / 11 : ℂ) * MvPolynomial.X 2 ^ 2 +
      MvPolynomial.X 2 ^ 6 + MvPolynomial.C (10 / 13 : ℂ) * MvPolynomial.X 1 * MvPolynomial.X 2 ^ 3 +
      MvPolynomial.C (10 / 7 : ℂ) * MvPolynomial.X 1 ^ 2 +
      MvPolynomial.C (10 / 13 : ℂ) * MvPolynomial.X 1 ^ 3 * MvPolynomial.X 2 +
      MvPolynomial.C 2 * MvPolynomial.X 1 ^ 6)

private lemma univH_formula :
    univH = X ^ 6 + (C cH3 * X ^ 3 + C cH2 * X ^ 2 + C cH1 * X + C cH0) := by
  have hbX : ∀ i : Fin 5, bFirst (MvPolynomial.X i) =
      ![C (MvPolynomial.X 0), Polynomial.X, C (MvPolynomial.X 1),
        C (MvPolynomial.X 2), C (MvPolynomial.X 3)] i := by
    intro i; fin_cases i <;>
      norm_num [bFirst, MvPolynomial.renameEquiv_apply, MvPolynomial.finSuccEquiv_apply,
        Equiv.swap_apply_def] <;> rfl
  have hbC : ∀ c : ℂ, bFirst (MvPolynomial.C c) = C (MvPolynomial.C c) := by
    intro c; simp [bFirst, MvPolynomial.renameEquiv_apply, MvPolynomial.finSuccEquiv_apply]
  simp [univH, diagWeighted, diagEll, diagB, diagC, diagD, squareLift,
    hbX, hbC, cH3, cH2, cH1, cH0, map_ofNat]
  ring

private lemma deg_cubic4_lt_six (a3 a2 a1 a0 : CoeffRing4) :
    (C a3 * X ^ 3 + C a2 * X ^ 2 + C a1 * X + C a0).degree < (6 : WithBot ℕ) := by
  have hd3 : (C a3 * X ^ 3).degree ≤ 3 := Polynomial.degree_C_mul_X_pow_le 3 a3
  have hd2 : (C a2 * X ^ 2).degree ≤ 2 := Polynomial.degree_C_mul_X_pow_le 2 a2
  have hd1 : (C a1 * X).degree ≤ 1 := by simpa using Polynomial.degree_C_mul_X_pow_le 1 a1
  have hd0 : (C a0).degree ≤ 0 := Polynomial.degree_C_le
  have h32 : (C a3 * X ^ 3 + C a2 * X ^ 2).degree ≤ 3 :=
    (Polynomial.degree_add_le _ _).trans (max_le hd3 (hd2.trans (by decide)))
  have h321 : (C a3 * X ^ 3 + C a2 * X ^ 2 + C a1 * X).degree ≤ 3 :=
    (Polynomial.degree_add_le _ _).trans (max_le h32 (hd1.trans (by decide)))
  have h3210 : (C a3 * X ^ 3 + C a2 * X ^ 2 + C a1 * X + C a0).degree ≤ 3 :=
    (Polynomial.degree_add_le _ _).trans (max_le h321 (hd0.trans (by decide)))
  exact lt_of_le_of_lt h3210 (by decide)

private lemma chart_irreducible : Irreducible (squareLift diagWeighted) := by
  have hmon : univH.Monic := by
    rw [univH_formula]
    exact Polynomial.monic_X_pow_add (deg_cubic4_lt_six cH3 cH2 cH1 cH0)
  let spec4 : CoeffRing4 →+* Polynomial ℂ :=
    MvPolynomial.eval₂Hom Polynomial.C ![0, 0, 0, Polynomial.X]
  have hspec : univH.map spec4 = planeSecH := by
    rw [univH_formula]
    simp [spec4, cH3, cH2, cH1, cH0, planeSecH, secConstH, map_ofNat]
    ring
  have hu : Irreducible univH :=
    Polynomial.Monic.irreducible_of_irreducible_map spec4 univH hmon (hspec ▸ planeSecH_irreducible)
  exact (MulEquiv.irreducible_iff bFirst).mp hu

end DiagIrreducible

theorem solution :
    Irreducible HodgeComputer.DiagonalPermutation.F ∧
      Irreducible (HodgeComputer.ReflectionChart.squareLift
        HodgeComputer.DiagonalPermutation.diagWeighted) :=
  ⟨DiagIrreducible.target_irreducible, DiagIrreducible.chart_irreducible⟩
