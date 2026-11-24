-- Prove2me | solution 1 for HermitekLEAN.modulusDefect_le_norm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:51:23.389234+00:00
-- url     : https://prove2.me/submissions/505830fe-dd37-4483-ae79-665cd9389a3e

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
theorem _root_.solution (F0 G : ℂ → ℂ) (z : ℂ) :
    modulusDefect F0 G z ≤ ‖G z‖ := by
  have h := abs_norm_sub_norm_le (F0 z + G z) (F0 z)
  rw [add_sub_cancel_left] at h
  exact h
end HermitekLEAN
