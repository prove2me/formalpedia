-- Prove2me | solution 1 for HermitekLEAN.truncate_mem_Hk
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:07:48.225638+00:00
-- url     : https://prove2.me/submissions/9ec176aa-ed4f-465e-b5df-ec3a44e61acd

module
public import Definitions.Def_LeanPool_PhaseRetrieval_FourierParseval
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite_Definitions
public import Mathlib.Analysis.Complex.Isometry
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
public import Mathlib.MeasureTheory.Integral.Gamma
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermitek_TrueLevelBasis
public import Theorems.Thm_HermitekLEAN_finiteHermiteSum_mem_Hk

set_option autoImplicit true
@[expose] public section
public section
open Complex MeasureTheory Real Finset
open scoped BigOperators Topology
noncomputable section
open HermitekLEAN
namespace HermitekLEAN
theorem _root_.solution :
    ∀ (k J : ℕ) (G : ℂ → ℂ), truncate k J G ∈ Hk k := by
  intro k J G
  exact
    (finiteHermiteSum_mem_Hk k (a := fun n : Fin (J + 1) => hermiteCoeff k G n.1))
end HermitekLEAN
