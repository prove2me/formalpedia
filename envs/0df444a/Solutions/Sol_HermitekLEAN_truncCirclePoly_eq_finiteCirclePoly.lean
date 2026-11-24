-- Prove2me | solution 1 for HermitekLEAN.truncCirclePoly_eq_finiteCirclePoly
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:49:57.652231+00:00
-- url     : https://prove2.me/submissions/c8f3ecaa-b6bf-4b05-8b5b-6457f0fbe3a2

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
    ∀ {k J : ℕ} {G : ℂ → ℂ} {r : ℝ},
      truncCirclePoly k r J G =
        finiteCirclePoly k r (fun n : Fin (J + 1) => hermiteCoeff k G n.1) := by
  intro k J G r
  rfl
end HermitekLEAN
