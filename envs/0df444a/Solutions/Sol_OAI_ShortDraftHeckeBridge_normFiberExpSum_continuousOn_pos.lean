-- Prove2me | solution 1 for OAI.ShortDraftHeckeBridge.normFiberExpSum_continuousOn_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T06:53:04.869232+00:00
-- url     : https://prove2.me/submissions/052c3ce8-32b3-429b-b6f5-7686a6b26ef1

import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_LocalNonvanishing
import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_NormFiberMellin
import Theorems.Thm_OAI_ShortDraftHeckeBridge_normFiberCoeff_norm_le
import Theorems.Thm_OAI_IdealGaussCRT_traceProdChar_mk
attribute [local simp] OAI.IdealGaussCRT.traceProdChar_mk



set_option autoImplicit false
open OAI
noncomputable section
open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open OAI.ShortDraftHeckeBridge
namespace OAI.ShortDraftHeckeBridge
theorem _root_.solution
    {q r : ℕ} [NeZero q] [NeZero r]
    (χ : DirichletCharacter ℂ q) (ψ : DirichletCharacter ℂ r)
    (weight : Ideal O → ℂ)
    (hcoeff : ∀ n : ℕ, n ≠ 0 → normFiberCoeff weight n = pairInverseCoeff χ ψ n)
    (ha0 : normFiberCoeff weight 0 = 0) :
    ContinuousOn (normFiberExpSum weight) (Set.Ioi (0 : ℝ)) := by
  intro t ht
  change 0 < t at ht
  let eps0 : ℝ := t / 2
  have heps0 : 0 < eps0 := by dsimp [eps0]; linarith
  have heps0t : eps0 < t := by dsimp [eps0]; linarith
  have hexp : Summable (fun n : ℕ => (n : ℝ) * Real.exp (-(n : ℝ) * eps0)) := by
    convert Real.summable_pow_mul_exp_neg_nat_mul 1 heps0 using 1
    ext n
    simp only [pow_one]
    congr 1
    ring_nf
  have hcontTerm (n : ℕ) : ContinuousOn
      (fun u : ℝ => normFiberCoeff weight n * Real.exp (-(n : ℝ) * u))
      (Set.Ici eps0) := by
    fun_prop
  have hbound (n : ℕ) (u : ℝ) (hu : u ∈ Set.Ici eps0) :
      ‖normFiberCoeff weight n * Real.exp (-(n : ℝ) * u)‖ ≤
        (n : ℝ) * Real.exp (-(n : ℝ) * eps0) := by
    have hnu : -(n : ℝ) * u ≤ -(n : ℝ) * eps0 := by
      have hu' : eps0 ≤ u := hu
      nlinarith [mul_le_mul_of_nonneg_left hu'
        (Nat.cast_nonneg (α := ℝ) n)]
    have hexpmon := Real.exp_le_exp.mpr hnu
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
    calc
      ‖normFiberCoeff weight n‖ * Real.exp (-(n : ℝ) * u) ≤
          (n : ℝ) * Real.exp (-(n : ℝ) * u) :=
        mul_le_mul_of_nonneg_right
          (normFiberCoeff_norm_le χ ψ weight hcoeff ha0 n) (Real.exp_pos _).le
      _ ≤ (n : ℝ) * Real.exp (-(n : ℝ) * eps0) :=
        mul_le_mul_of_nonneg_left hexpmon (Nat.cast_nonneg (α := ℝ) n)
  have hcontHalf : ContinuousOn (normFiberExpSum weight) (Set.Ici eps0) := by
    change ContinuousOn
      (fun u : ℝ => ∑' n : ℕ,
        normFiberCoeff weight n * Real.exp (-(n : ℝ) * u)) (Set.Ici eps0)
    exact continuousOn_tsum hcontTerm hexp hbound
  exact (hcontHalf.continuousAt (Ici_mem_nhds heps0t)).continuousWithinAt
end OAI.ShortDraftHeckeBridge
