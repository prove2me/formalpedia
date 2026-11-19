-- Prove2me | solution 1 for Kyprianou.Ch01.uniformLpTwoNormOfBoundedSquareMomentsPublic
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T22:37:10.293611+00:00
-- url     : https://prove2.me/submissions/d0b3320a-41ad-469f-b729-349b07c55df8

import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSeminorm.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped ENNReal NNReal
set_option autoImplicit false

/-- Convert an integrable real square into the extended-real L2 norm integral. -/
private theorem lintegral_square_eq_ofReal_integral
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (f : Ω → ℝ) (hInt : Integrable (fun ω => f ω ^ 2) P) :
    (∫⁻ ω, ‖f ω‖ₑ ^ (2 : ℝ) ∂P) =
      ENNReal.ofReal (∫ ω, f ω ^ 2 ∂P) := by
  rw [ofReal_integral_eq_lintegral_ofReal hInt
    (Filter.Eventually.of_forall fun ω => sq_nonneg (f ω))]
  apply lintegral_congr
  intro ω
  rw [Real.enorm_eq_ofReal_abs]
  calc
    ENNReal.ofReal |f ω| ^ (2 : ℝ) =
        ENNReal.ofReal (|f ω| ^ 2) := by
      simpa only [ENNReal.rpow_two, pow_two] using
        (ENNReal.ofReal_pow (abs_nonneg (f ω)) 2).symm
    _ = ENNReal.ofReal (f ω ^ 2) := by rw [sq_abs]

/-- Uniformly bounded square moments imply a common finite L2 norm bound. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω)
    (f : ℕ → Ω → ℝ)
    (hMeas : ∀ n, AEStronglyMeasurable (f n) P)
    (K : ℝ) (hK : 0 ≤ K)
    (hMoment : ∀ n, Integrable (fun ω => f n ω ^ 2) P ∧
      (∫ ω, f n ω ^ 2 ∂P) ≤ K) :
    ∃ C : ℝ≥0, ∀ n, eLpNorm (f n) 2 P ≤ (C : ENNReal) := by
  have hfinite : (ENNReal.ofReal K) ^ (1 / 2 : ℝ) ≠ ⊤ := by
    finiteness
  refine ⟨((ENNReal.ofReal K) ^ (1 / 2 : ℝ)).toNNReal, ?_⟩
  intro n
  have hL : eLpNorm (f n) 2 P =
      (ENNReal.ofReal (∫ ω, f n ω ^ 2 ∂P)) ^ (1 / 2 : ℝ) := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal
      (by norm_num : (2 : ENNReal) ≠ 0)
      (by norm_num : (2 : ENNReal) ≠ ⊤)]
    simpa only [ENNReal.toReal_ofNat] using
      congrArg (fun a : ENNReal => a ^ (1 / 2 : ℝ))
        (lintegral_square_eq_ofReal_integral P (f n) (hMoment n).1)
  have hB : eLpNorm (f n) 2 P ≤ (ENNReal.ofReal K) ^ (1 / 2 : ℝ) := by
    rw [hL]
    exact ENNReal.rpow_le_rpow
      (ENNReal.ofReal_le_ofReal (hMoment n).2) (by norm_num)
  simpa only [ENNReal.coe_toNNReal hfinite] using hB
