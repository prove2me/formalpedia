-- Prove2me | solution 1 for HermitekLEAN.truncate_eq_finiteHermiteSum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:11:22.208774+00:00
-- url     : https://prove2.me/submissions/fc7910cb-6e0c-443a-bc95-f49c633c4905

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
    ∀ {k J : ℕ} {G : ℂ → ℂ},
      truncate k J G =
        finiteHermiteSum k (fun n : Fin (J + 1) => hermiteCoeff k G n.1) := by
  intro k J G
  rfl
end HermitekLEAN
