-- Prove2me | solution 1 for HermitekLEAN.truncCirclePoly_support
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:50:32.425218+00:00
-- url     : https://prove2.me/submissions/6028ba49-13aa-4c15-bcdd-e74952306793

module
public import Definitions.Def_LeanPool_PhaseRetrieval_FourierParseval
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite_Definitions
public import Mathlib.Analysis.Complex.Isometry
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
public import Mathlib.MeasureTheory.Integral.Gamma
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermitek_TrueLevelBasis

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
      truncCirclePoly k r J G =
        positiveTrigonometricPolynomial
          (frequencyBand 0 (J + 1))
          (finiteCircleCoeff k r (fun n : Fin (J + 1) => hermiteCoeff k G n.1)) := by
  intro k J r G
  rfl
end HermitekLEAN
