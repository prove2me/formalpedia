-- Prove2me | solution 1 for HermitekLEAN.truncCirclePoly_support_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:50:34.301419+00:00
-- url     : https://prove2.me/submissions/4e6200bb-db56-41e9-a130-5eea3dc562e1

module
public import Definitions.Def_LeanPool_PhaseRetrieval_FourierParseval
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite_Definitions
public import Mathlib.Analysis.Complex.Isometry
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
public import Mathlib.MeasureTheory.Integral.Gamma
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermitek_TrueLevelBasis
public import Theorems.Thm_HermitekLEAN_qkn_real
public import Theorems.Thm_HermitekLEAN_hermiteCoeff_phi0
public import Theorems.Thm_HermitekLEAN_finiteCirclePoly_support_pos
attribute [local simp] HermitekLEAN.qkn_real
attribute [local simp] HermitekLEAN.hermiteCoeff_phi0

set_option autoImplicit true
@[expose] public section
public section
open Complex MeasureTheory Real Finset
open scoped BigOperators Topology
noncomputable section
open HermitekLEAN
namespace HermitekLEAN
theorem _root_.solution :
    ∀ {k J : ℕ} (r : ℝ) (G : ℂ → ℂ),
      weightedInner G (phi0 k) = 0 →
        truncCirclePoly k r J G =
          positiveTrigonometricPolynomial
            (frequencyBand 1 J)
            (finiteCircleCoeff k r (fun n : Fin (J + 1) => hermiteCoeff k G n.1)) := by
  intro k J r G h
  have h0 : hermiteCoeff k G 0 = 0 := by simpa only [hermiteCoeff_phi0] using h
  simpa only [truncCirclePoly, h0] using
    (finiteCirclePoly_support_pos (k := k) (D := J) (r := r)
      (a := fun n : Fin (J + 1) => hermiteCoeff k G n.1) h0)
end HermitekLEAN
