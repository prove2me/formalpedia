-- Prove2me | solution 1 for HermitekLEAN.high_frequency_circle_estimate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:31:50.633014+00:00
-- url     : https://prove2.me/submissions/af499129-8fd6-4f9d-b6cb-4fd8e09e4488

module
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermitek_TrueLevelBasis
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite_ImportedAnalyticInputs
public import Mathlib.Tactic.NormNum.Parity
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermitek_ImportedAnalyticInputs
public import Theorems.Thm_HermiteLEAN_high_frequency_circle_estimate


set_option autoImplicit true
@[expose] public section
public section
open Complex MeasureTheory Real Finset
open scoped BigOperators
noncomputable section
open HermitekLEAN
namespace HermitekLEAN
theorem _root_.solution
    (N L : ℕ)
    (hN : 1 ≤ N)
    (hL : 1 ≤ L)
    (c : ℕ → ℂ)
    (hband : 1343 * (L : ℝ) ^ 2 ≤ (N : ℝ) ^ 2) :
    circleL2Sq (positiveTrigonometricPolynomial (frequencyBand N L) c)
      ≤ 32 * circleRhoNormSq (positiveTrigonometricPolynomial (frequencyBand N L) c) := by
  exact
    HermiteLEAN.high_frequency_circle_estimate N L hN hL c hband
end HermitekLEAN
