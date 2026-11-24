-- Prove2me | solution 1 for HermitekLEAN.weightedDefectNorm_smul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:49:57.102669+00:00
-- url     : https://prove2.me/submissions/3c59ca49-3276-442c-aa9c-b20bb4563f24

module
public import Definitions.Def_LeanPool_PhaseRetrieval_FourierParseval
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite_Definitions
public import Mathlib.Analysis.Complex.Isometry
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
public import Mathlib.MeasureTheory.Integral.Gamma
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermitek_TrueLevelBasis
public import Theorems.Thm_HermitekLEAN_qkn_real
attribute [local simp] HermitekLEAN.qkn_real

set_option autoImplicit true
@[expose] public section
public section
open Complex MeasureTheory Real Finset
open scoped BigOperators Topology
noncomputable section
open HermitekLEAN
namespace HermitekLEAN
theorem _root_.solution (c : ℂ) (F0 G : ℂ → ℂ) :
    weightedDefectNorm (c • F0) (c • G) = ‖c‖ * weightedDefectNorm F0 G := by
  have hInt :
      ∫ z : ℂ, (modulusDefect (c • F0) (c • G) z) ^ 2 * Real.exp (-‖z‖ ^ 2)
        = ∫ z : ℂ, ‖c‖ ^ 2 * ((modulusDefect F0 G z) ^ 2 * Real.exp (-‖z‖ ^ 2)) := by
    congr with z
    have hpt : modulusDefect (c • F0) (c • G) z = ‖c‖ * modulusDefect F0 G z := by
      change |‖(c • F0) z + (c • G) z‖ - ‖(c • F0) z‖| = ‖c‖ * |‖F0 z + G z‖ - ‖F0 z‖|
      have hsum : (c • F0) z + (c • G) z = c * (F0 z + G z) := by simp [Pi.smul_apply, mul_add]
      have hleft : ‖(c • F0) z + (c • G) z‖ = ‖c‖ * ‖F0 z + G z‖ := by rw [hsum, norm_mul]
      have hright : ‖(c • F0) z‖ = ‖c‖ * ‖F0 z‖ := by simp
      rw [hleft, hright]
      have hfact : ‖c‖ * ‖F0 z + G z‖ - ‖c‖ * ‖F0 z‖ =
          ‖c‖ * (‖F0 z + G z‖ - ‖F0 z‖) := by ring
      rw [hfact, abs_mul, abs_of_nonneg (norm_nonneg c)]
    rw [hpt]
    ring
  have hsq : weightedDefectNormSq (c • F0) (c • G) = ‖c‖ ^ 2 * weightedDefectNormSq F0 G := by
    change (1 / Real.pi) * ∫ z : ℂ, (modulusDefect (c • F0) (c • G) z) ^ 2 * Real.exp (-‖z‖ ^ 2)
      = ‖c‖ ^ 2 * ((1 / Real.pi) * ∫ z : ℂ, (modulusDefect F0 G z) ^ 2 * Real.exp (-‖z‖ ^ 2))
    rw [hInt, MeasureTheory.integral_const_mul]
    ac_rfl
  have hcsq : √(‖c‖ ^ 2) = ‖c‖ := by rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg c)]
  change √(weightedDefectNormSq (c • F0) (c • G)) = ‖c‖ * √(weightedDefectNormSq F0 G)
  rw [hsq, Real.sqrt_mul (by positivity), hcsq]
end HermitekLEAN
