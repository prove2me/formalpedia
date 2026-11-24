-- Prove2me | solution 1 for HermitekLEAN.integrable_weightedCross
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:03:19.350349+00:00
-- url     : https://prove2.me/submissions/8ae2d52f-c13c-47ca-b152-752c4ed71e2e

module
public import Definitions.Def_LeanPool_PhaseRetrieval_FourierParseval
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite_Definitions
public import Mathlib.Analysis.Complex.Isometry
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
public import Mathlib.MeasureTheory.Integral.Gamma
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermitek_TrueLevelBasis
public import Theorems.Thm_HermitekLEAN_qkn_real
public import Theorems.Thm_HermitekLEAN_continuous_Phi
public import Theorems.Thm_HermitekLEAN_integrable_weightedDiag
attribute [local simp] HermitekLEAN.qkn_real

set_option autoImplicit true
@[expose] public section
public section
open Complex MeasureTheory Real Finset
open scoped BigOperators Topology
noncomputable section
open HermitekLEAN
namespace HermitekLEAN
theorem _root_.solution (k m n : ℕ) :
    Integrable (fun z : ℂ =>
      Phi k m z * (starRingEnd ℂ) (Phi k n z) * (Real.exp (-‖z‖ ^ 2) : ℂ)) := by
  let f : ℂ → ℂ := fun z =>
    Phi k m z * (starRingEnd ℂ) (Phi k n z) * (Real.exp (-‖z‖ ^ 2) : ℂ)
  let g : ℂ → ℝ := fun z =>
    ((‖Phi k m z‖ ^ 2 + ‖Phi k n z‖ ^ 2) / 2) * Real.exp (-‖z‖ ^ 2)
  have hg : Integrable g := by
    have hm : Integrable (fun z : ℂ => ‖Phi k m z‖ ^ 2 * Real.exp (-‖z‖ ^ 2)) :=
      integrable_weightedDiag k m
    have hn : Integrable (fun z : ℂ => ‖Phi k n z‖ ^ 2 * Real.exp (-‖z‖ ^ 2)) :=
      integrable_weightedDiag k n
    have hs : Integrable (fun z : ℂ =>
      (‖Phi k m z‖ ^ 2 * Real.exp (-‖z‖ ^ 2)) +
        (‖Phi k n z‖ ^ 2 * Real.exp (-‖z‖ ^ 2))) := hm.add hn
    convert hs.const_mul (1 / 2) using 1
    funext z
    ring
  have hf_meas : AEStronglyMeasurable f volume := by
    have hcontExp : Continuous (fun z : ℂ => (Real.exp (-‖z‖ ^ 2) : ℂ)) := by
      exact
        Complex.continuous_ofReal.comp
          (Real.continuous_exp.comp (continuous_neg.comp (continuous_norm.pow 2)))
    exact ((continuous_Phi k m).mul (continuous_star.comp (continuous_Phi k n))).mul hcontExp
      |>.aestronglyMeasurable
  have hbound : ∀ z : ℂ, ‖f z‖ ≤ g z := by
    intro z
    calc
      ‖f z‖ = (‖Phi k m z‖ * ‖Phi k n z‖) * Real.exp (-‖z‖ ^ 2) := by
        have hexp_nonneg : 0 ≤ Real.exp (-‖z‖ ^ 2) := by positivity
        calc
          ‖Phi k m z * (starRingEnd ℂ) (Phi k n z) * (Real.exp (-‖z‖ ^ 2) : ℂ)‖
            = ‖Phi k m z * (starRingEnd ℂ) (Phi k n z)‖ *
                ‖((Real.exp (-‖z‖ ^ 2) : ℝ) : ℂ)‖ := by rw [norm_mul]
          _ = (‖Phi k m z‖ * ‖Phi k n z‖) * ‖((Real.exp (-‖z‖ ^ 2) : ℝ) : ℂ)‖ := by
                rw [norm_mul, show ‖(starRingEnd ℂ) (Phi k n z)‖ = ‖Phi k n z‖ by simp]
          _ = (‖Phi k m z‖ * ‖Phi k n z‖) * Real.exp (-‖z‖ ^ 2) := by
                rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hexp_nonneg]
      _ ≤ (((‖Phi k m z‖ ^ 2 + ‖Phi k n z‖ ^ 2) / 2) * Real.exp (-‖z‖ ^ 2)) := by
            have hsq :
                2 * (‖Phi k m z‖ * ‖Phi k n z‖) ≤ ‖Phi k m z‖ ^ 2 + ‖Phi k n z‖ ^ 2 := by
              linarith only [sq_nonneg (‖Phi k m z‖ - ‖Phi k n z‖)]
            have hexp_nonneg : 0 ≤ Real.exp (-‖z‖ ^ 2) := by positivity
            nlinarith only [hsq, hexp_nonneg]
      _ = g z := by simp [g]
  exact MeasureTheory.Integrable.mono' hg hf_meas (Filter.Eventually.of_forall hbound)
end HermitekLEAN
