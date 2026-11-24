-- Prove2me | solution 1 for HermitekLEAN.weightedNorm_smul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:49:56.643122+00:00
-- url     : https://prove2.me/submissions/839285df-6ab8-42a5-856f-964f22b8d4c6

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
theorem _root_.solution (c : ℂ) (G : ℂ → ℂ) :
    weightedNorm (c • G) = ‖c‖ * weightedNorm G := by
  have hInt :
      ∫ z : ℂ, ‖(c • G) z‖ ^ 2 * Real.exp (-‖z‖ ^ 2)
        = ∫ z : ℂ, ‖c‖ ^ 2 * (‖G z‖ ^ 2 * Real.exp (-‖z‖ ^ 2)) := by
    congr with z
    simp [pow_two, mul_comm, mul_left_comm, mul_assoc]
  have hsq : weightedNormSq (c • G) = ‖c‖ ^ 2 * weightedNormSq G := by
    change (1 / Real.pi) * ∫ z : ℂ, ‖(c • G) z‖ ^ 2 * Real.exp (-‖z‖ ^ 2)
      = ‖c‖ ^ 2 * ((1 / Real.pi) * ∫ z : ℂ, ‖G z‖ ^ 2 * Real.exp (-‖z‖ ^ 2))
    rw [hInt, MeasureTheory.integral_const_mul]
    ac_rfl
  have hcsq : √(‖c‖ ^ 2) = ‖c‖ := by rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg c)]
  change √(weightedNormSq (c • G)) = ‖c‖ * √(weightedNormSq G)
  rw [hsq, Real.sqrt_mul (by positivity), hcsq]
end HermitekLEAN
