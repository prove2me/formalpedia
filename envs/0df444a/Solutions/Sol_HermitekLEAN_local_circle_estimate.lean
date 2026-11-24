-- Prove2me | solution 1 for HermitekLEAN.local_circle_estimate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:31:49.878912+00:00
-- url     : https://prove2.me/submissions/1b3ef4d0-356b-4084-bf44-86c66b4c4681

module
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermitek_TrueLevelBasis
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite_ImportedAnalyticInputs
public import Mathlib.Tactic.NormNum.Parity
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermitek_ImportedAnalyticInputs
public import Theorems.Thm_FockSPR_local_circle_estimate
public import Theorems.Thm_HermiteLEAN_local_circle_estimate
public import Theorems.Thm_HermitekLEAN_hermiteCoeff_phi0
public import Theorems.Thm_HermitekLEAN_qkn_real
attribute [local simp] HermitekLEAN.hermiteCoeff_phi0
attribute [local simp] HermitekLEAN.qkn_real



set_option autoImplicit true
@[expose] public section
public section
open Complex MeasureTheory Real Finset
open scoped BigOperators
noncomputable section
open HermitekLEAN
namespace HermitekLEAN
theorem _root_.solution
    (E : Finset ℕ)
    (hpos : ∀ n ∈ E, 1 ≤ n)
    (c : ℕ → ℂ) :
    circleL2Sq (positiveTrigonometricPolynomial E c)
      ≤ 144 * E.card * circleRhoNormSq (positiveTrigonometricPolynomial E c) := by
  simpa [circleL2Sq, circleRhoNormSq, positiveTrigonometricPolynomial] using
    HermiteLEAN.local_circle_estimate E hpos c
end HermitekLEAN
