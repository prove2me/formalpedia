-- Prove2me | solution 1 for HermitekLEAN.integrable_truncate_normSq_exp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:08:36.350328+00:00
-- url     : https://prove2.me/submissions/3c710b01-43c4-44dd-a8b2-725f4aaadcb2

module
public import Definitions.Def_LeanPool_PhaseRetrieval_FourierParseval
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite_Definitions
public import Mathlib.Analysis.Complex.Isometry
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
public import Mathlib.MeasureTheory.Integral.Gamma
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermitek_TrueLevelBasis
public import Theorems.Thm_HermitekLEAN_truncate_mem_Hk

set_option autoImplicit true
@[expose] public section
public section
open Complex MeasureTheory Real Finset
open scoped BigOperators Topology
noncomputable section
open HermitekLEAN
namespace HermitekLEAN
theorem _root_.solution (k J : ℕ) (G : ℂ → ℂ) :
    Integrable (fun z : ℂ => ‖truncate k J G z‖ ^ 2 * rexp (-‖z‖ ^ 2)) := by
  exact (truncate_mem_Hk k J G).1
end HermitekLEAN
