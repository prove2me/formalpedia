-- Prove2me | solution 1 for OAI.ShortDraftMellin.mobiusExpSum_continuousOn_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:29:35.607198+00:00
-- url     : https://prove2.me/submissions/95c1e7eb-479f-400e-873f-0f1832727383

import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_ExponentialSmoothing
import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_LogProfiles

set_option autoImplicit false
open OAI
open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open OAI.ShortDraftMellin
namespace OAI.ShortDraftMellin
theorem _root_.solution
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :
    ContinuousOn (mobiusExpSum χ) (Set.Ioi (0 : ℝ)) := by
  intro t ht
  change 0 < t at ht
  let δ : ℝ := t / 2
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have hδt : δ < t := by dsimp [δ]; linarith
  have hexp : Summable (fun n : ℕ => Real.exp (-(n : ℝ) * δ)) := by
    convert (Real.summable_exp_nat_mul_iff.mpr (neg_lt_zero.mpr hδ)) using 1
    ext n
    congr 1
    ring
  have hcontTerm (n : ℕ) : ContinuousOn
      (fun u : ℝ => χ n * (ArithmeticFunction.moebius n : ℂ) *
        Real.exp (-(n : ℝ) * u)) (Set.Ici δ) := by
    fun_prop
  have hcoeff (n : ℕ) :
      ‖χ n * (ArithmeticFunction.moebius n : ℂ)‖ ≤ 1 := by
    rw [norm_mul]
    have hχ : ‖χ n‖ ≤ 1 := χ.norm_le_one _
    have hμ : ‖(ArithmeticFunction.moebius n : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_intCast]
      exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := n))
    nlinarith [mul_nonneg (sub_nonneg.mpr hχ)
      (norm_nonneg ((ArithmeticFunction.moebius n : ℂ))),
      mul_nonneg (sub_nonneg.mpr hμ) (norm_nonneg (χ n))]
  have hbound (n : ℕ) (u : ℝ) (hu : u ∈ Set.Ici δ) :
      ‖χ n * (ArithmeticFunction.moebius n : ℂ) *
        Real.exp (-(n : ℝ) * u)‖ ≤
      Real.exp (-(n : ℝ) * δ) := by
    have hnu : -(n : ℝ) * u ≤ -(n : ℝ) * δ := by
      have hu' : δ ≤ u := hu
      nlinarith [mul_le_mul_of_nonneg_left hu'
        (Nat.cast_nonneg (α := ℝ) n)]
    have hexpmon := Real.exp_le_exp.mpr hnu
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
    calc
      ‖χ n * (ArithmeticFunction.moebius n : ℂ)‖ *
          Real.exp (-(n : ℝ) * u) ≤
          1 * Real.exp (-(n : ℝ) * u) :=
        mul_le_mul_of_nonneg_right (hcoeff n) (Real.exp_pos _).le
      _ ≤ Real.exp (-(n : ℝ) * δ) := by simpa using hexpmon
  have hcontHalf : ContinuousOn (mobiusExpSum χ) (Set.Ici δ) := by
    change ContinuousOn
      (fun u : ℝ => ∑' n : ℕ,
        χ n * (ArithmeticFunction.moebius n : ℂ) *
          Real.exp (-(n : ℝ) * u)) (Set.Ici δ)
    exact continuousOn_tsum hcontTerm hexp hbound
  exact (hcontHalf.continuousAt (Ici_mem_nhds hδt)).continuousWithinAt
end OAI.ShortDraftMellin
