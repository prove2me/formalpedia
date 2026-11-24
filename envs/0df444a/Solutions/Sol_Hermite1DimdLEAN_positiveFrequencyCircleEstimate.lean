-- Prove2me | solution 1 for Hermite1DimdLEAN.positiveFrequencyCircleEstimate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:32:48.983733+00:00
-- url     : https://prove2.me/submissions/ecadf708-611d-4259-a34d-bce75b34446a

module
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite1Dimd_Definitions
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermitek_BasisLocalization
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermitek_ImportedAnalyticInputs
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.Tactic.NormNum.Parity
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite1Dimd_ImportedAnalyticInputs
public import Theorems.Thm_FockSPR_local_circle_estimate
public import Theorems.Thm_HermiteLEAN_local_circle_estimate
public import Theorems.Thm_HermitekLEAN_hermiteCoeff_phi0
public import Theorems.Thm_HermitekLEAN_local_circle_estimate
public import Theorems.Thm_HermitekLEAN_qkn_real
attribute [local simp] HermitekLEAN.hermiteCoeff_phi0
attribute [local simp] HermitekLEAN.qkn_real



set_option autoImplicit true
@[expose] public section
public section
open Complex MeasureTheory Real Finset
open scoped BigOperators ComplexConjugate
noncomputable section
open Hermite1DimdLEAN
namespace Hermite1DimdLEAN
theorem _root_.solution
    (E : Finset ℕ) (b : ℕ → ℂ)
    (hpos : ∀ n ∈ E, 0 < n)
    (_hP : HasPositiveFrequencySupport (positiveFrequencyPolynomial E b) E) :
    circleL2NormSq (positiveFrequencyPolynomial E b) ≤
      144 * E.card * circleL2NormSq (fun t => rho 1 (positiveFrequencyPolynomial E b t)) := by
  /-
  Scaffolding guidance:
  this is the circle estimate used on low annuli. Keep the positive-frequency
  hypothesis explicit and keep the exact constant `144`.
  -/
  rw [show circleL2NormSq (positiveFrequencyPolynomial E b) =
      HermiteLEAN.circleL2Sq (HermiteLEAN.positiveTrigonometricPolynomial E b) by
      rfl]
  rw [show circleL2NormSq (fun t => rho 1 (positiveFrequencyPolynomial E b t)) =
      HermiteLEAN.circleRhoNormSq (HermiteLEAN.positiveTrigonometricPolynomial E b) by
      simp [circleL2NormSq, rho, positiveFrequencyPolynomial, HermiteLEAN.circleRhoNormSq,
        HermiteLEAN.positiveTrigonometricPolynomial, HermiteLEAN.rho, sq_abs]]
  exact
    HermitekLEAN.local_circle_estimate E
      (by
        intro n hn
        exact Nat.succ_le_of_lt (hpos n hn))
      b
end Hermite1DimdLEAN
