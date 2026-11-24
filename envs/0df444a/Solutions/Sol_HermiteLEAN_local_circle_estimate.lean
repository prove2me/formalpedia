-- Prove2me | solution 1 for HermiteLEAN.local_circle_estimate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:06:51.51543+00:00
-- url     : https://prove2.me/submissions/dc0cdea1-290b-41e4-8631-cd858922bdca

module
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite_Definitions
public import Definitions.Def_LeanPool_PhaseRetrieval_Constant_Internal_Definitions
public import Definitions.Def_LeanPool_PhaseRetrieval_Constant_Internal_HighFreqBandEstimate
public import Definitions.Def_LeanPool_PhaseRetrieval_Constant_Internal_LocalCircleEstimate
public import Mathlib.Tactic.NormNum.Parity
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite_ImportedAnalyticInputs
public import Theorems.Thm_FockSPR_local_circle_estimate


set_option autoImplicit true
@[expose] public section
public section
open Complex MeasureTheory Real Finset
open scoped BigOperators
noncomputable section
open HermiteLEAN
namespace HermiteLEAN
theorem _root_.solution
    (E : Finset ℕ)
    (hpos : ∀ n ∈ E, 1 ≤ n)
    (c : ℕ → ℂ) :
    circleL2Sq (positiveTrigonometricPolynomial E c)
      ≤ 144 * E.card * circleRhoNormSq (positiveTrigonometricPolynomial E c) := by
  by_cases hE0 : E.card = 0
  · have hE_empty : E = ∅ := Finset.card_eq_zero.mp hE0
    simp [circleL2Sq, circleRhoNormSq, positiveTrigonometricPolynomial, hE_empty, rho]
  · have hcard : 1 ≤ E.card := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hE0)
    have h := FockSPR.local_circle_estimate (L := E.card) hcard rfl hpos c
        (positiveTrigonometricPolynomial E c) rfl
    simp only [T, FockSPR.T, circleL2Sq, circleRhoNormSq, positiveTrigonometricPolynomial,
      FockSPR.circleNormSq, rho, FockSPR.rho, sq_abs] at h ⊢
    exact h
end HermiteLEAN
