-- Prove2me | solution 1 for OAI.PiExponent.MatrixTranslationBounds.logTail_product_weight_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T07:51:04.369981+00:00
-- url     : https://prove2.me/submissions/4f415a3a-ffaf-4995-8648-b1a8c8bf853c

import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Algebra.Order.Antidiag.FinsuppEquiv
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.RingTheory.PowerSeries.Order
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.RingTheory.PowerSeries.Log
import Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_AnalyticAggregate_RemainderData
import Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_RowTranslation_CoreData
import Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_LiteralAnalyticSummand_InterfaceData
import Definitions.Def_OAI_PiExponent_LiteralAnalytic_choiceScalarMajorant
import Theorems.Thm_OAI_PiExponent_MatrixTranslationBounds_logTail_product_coeff_support

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open scoped BigOperators Topology
open OAI.PiExponent OAI.PiExponent.MatrixTranslationBounds OAI.PiExponent.RowTranslation

/-!
A nonzero logarithmic-tail coefficient supplies the degree-support inequality.
The remaining real-valued weighted comparison is a finite sum of each
coordinate truncation budget.
-/
theorem solution {σ : Type*} [Fintype σ] [DecidableEq σ]
    (T : σ → ℕ) (β a : σ →₀ ℕ)
    (d : ∀ i, Fin (a i - β i + 1)) (k : ℕ) (w : σ → ℝ)
    (H v F : ℝ) (hv : 0 < v) (hF : 0 < F) (hT : ∀ i, 1 ≤ T i)
    (hk : (k : ℝ) ≤ H / v)
    (hTw : ∀ i, F * w i ≤ v * T i) :
    PowerSeries.coeff k
        (∏ i, (tail (T i) (PowerSeries.log ℂ)) ^ ((d i).val : ℕ)) ≠ 0 →
      weight w (fun i => (d i).val) ≤ H / F := by
  intro hcoeff
  have hdeg :=
    OAI.PiExponent.MatrixTranslationBounds.logTail_product_coeff_support
      T (fun i => (d i).val) hT k hcoeff
  have hdegR : (∑ i, (T i : ℝ) * (d i).val) ≤ (k : ℝ) := by
    exact_mod_cast hdeg
  have hsum :
      (∑ i, F * (w i * ((d i).val : ℝ))) ≤
        ∑ i, v * ((T i : ℝ) * (d i).val) := by
    apply Finset.sum_le_sum
    intro i hi
    have he : 0 ≤ ((d i).val : ℝ) := Nat.cast_nonneg _
    convert mul_le_mul_of_nonneg_right (hTw i) he using 1 <;> ring
  have hweighted :
      F * weight w (fun i => (d i).val) ≤
        v * (∑ i, (T i : ℝ) * (d i).val) := by
    simpa [weight, Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm] using hsum
  have hvk : v * (k : ℝ) ≤ H := by
    calc
      v * (k : ℝ) ≤ v * (H / v) := mul_le_mul_of_nonneg_left hk hv.le
      _ = H := by field_simp
  have hFH : F * weight w (fun i => (d i).val) ≤ H := by
    calc
      F * weight w (fun i => (d i).val) ≤
          v * (∑ i, (T i : ℝ) * (d i).val) := hweighted
      _ ≤ v * (k : ℝ) := mul_le_mul_of_nonneg_left hdegR hv.le
      _ ≤ H := hvk
  exact (le_div_iff₀ hF).2 (by simpa [mul_comm] using hFH)
