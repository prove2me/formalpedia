-- Prove2me | solution 1 for OAI.PiExponent.MatrixTranslationBounds.rowScalar_exp_weight_difference_of_controls
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-16T17:10:40.068661+00:00
-- url     : https://prove2.me/submissions/bcf6a08c-969a-4e23-91cc-f4481ccf5588

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
import Theorems.Thm_OAI_PiExponent_MatrixTranslationBounds_rowScalar_exp_weight_difference_majorant

open scoped BigOperators Topology
open OAI.PiExponent OAI.PiExponent.MatrixTranslationBounds OAI.PiExponent.RowTranslation

theorem solution {σ : Type*} [Fintype σ] [DecidableEq σ]
    (ε : σ → ℂ) (τ : σ → PowerSeries ℂ) (β a : σ →₀ ℕ)
    (d : ∀ i, Fin (a i - β i + 1)) (k : ℕ) (w : σ → ℝ)
    (C ν H ws v F : ℝ) (hC : 0 ≤ C) (hν : 0 ≤ ν)
    (hws : 0 < ws) (hv : 0 < v) (hF : 0 < F)
    (hw : ∀ i, ws ≤ w i) (ha : weight w (fun i => a i) ≤ H)
    (hk : (k : ℝ) ≤ H / v)
    (hcoeff : ‖PowerSeries.coeff k (∏ i, τ i ^ ((d i).val : ℕ))‖ ≤ (2 : ℝ) ^ k)
    (hd : weight w (fun i => (d i).val) ≤ H / F)
    (hε : ∀ i, ‖ε i‖ ≤ Real.exp (C - ν * w i)) :
    ‖rowScalar ε τ β a d k‖ ≤
      Real.exp (-ν * (weight w (fun i => a i) - weight w (fun i => β i)) +
        H * (ν / F + Real.log 2 / v + (Real.log 4 + C) / ws)) := by
  have hmajor := rowScalar_exp_weight_difference_majorant
    ε τ β a d k w C ν ws hC hν hws hw hcoeff hε
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hlog4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have h1 : ν * weight w (fun i => (d i).val) ≤ ν * (H / F) :=
    mul_le_mul_of_nonneg_left hd hν
  have h1' : ν * weight w (fun i => (d i).val) ≤ H * (ν / F) := by
    calc
      ν * weight w (fun i => (d i).val) ≤ ν * (H / F) := h1
      _ = H * (ν / F) := by ring
  have h2 : (k : ℝ) * Real.log 2 ≤ (H / v) * Real.log 2 :=
    mul_le_mul_of_nonneg_right hk hlog2
  have h2' : (k : ℝ) * Real.log 2 ≤ H * (Real.log 2 / v) := by
    calc
      (k : ℝ) * Real.log 2 ≤ (H / v) * Real.log 2 := h2
      _ = H * (Real.log 2 / v) := by ring
  have h3 : (C + Real.log 4) * weight w (fun i => a i) ≤
      (C + Real.log 4) * H :=
    mul_le_mul_of_nonneg_left ha (add_nonneg hC hlog4)
  have h3' : (C + Real.log 4) * weight w (fun i => a i) * (1 / ws) ≤
      (C + Real.log 4) * H * (1 / ws) :=
    mul_le_mul_of_nonneg_right h3 (by positivity)
  have h3'' : (C + Real.log 4) * weight w (fun i => a i) / ws ≤
      H * ((Real.log 4 + C) / ws) := by
    calc
      (C + Real.log 4) * weight w (fun i => a i) / ws =
          (C + Real.log 4) * weight w (fun i => a i) * (1 / ws) := by
            rw [div_eq_mul_inv, one_div]
      _ ≤ (C + Real.log 4) * H * (1 / ws) := h3'
      _ = H * ((Real.log 4 + C) / ws) := by ring
  have hexp :
      Real.exp (-ν * (weight w (fun i => a i) - weight w (fun i => β i)) +
        ν * weight w (fun i => (d i).val) +
        (C + Real.log 4) * weight w (fun i => a i) / ws +
        (k : ℝ) * Real.log 2) ≤
      Real.exp (-ν * (weight w (fun i => a i) - weight w (fun i => β i)) +
        H * (ν / F + Real.log 2 / v + (Real.log 4 + C) / ws)) := by
    apply Real.exp_le_exp.mpr
    nlinarith [h1', h2', h3'']
  exact le_trans hmajor hexp