-- Prove2me | solution 1 for HermitekLEAN.truncate_normSq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:06:56.411625+00:00
-- url     : https://prove2.me/submissions/ced71c28-124b-46f5-97e7-ab7de8ef0f0d

module
public import Definitions.Def_LeanPool_PhaseRetrieval_FourierParseval
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite_Definitions
public import Mathlib.Analysis.Complex.Isometry
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
public import Mathlib.MeasureTheory.Integral.Gamma
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermitek_TrueLevelBasis
public import Theorems.Thm_HermitekLEAN_finiteHermiteSum_normSq

set_option autoImplicit true
@[expose] public section
public section
open Complex MeasureTheory Real Finset
open scoped BigOperators Topology
noncomputable section
open HermitekLEAN
namespace HermitekLEAN
theorem _root_.solution :
    ∀ (k J : ℕ) (G : ℂ → ℂ),
      weightedNormSq (truncate k J G) =
        ∑ n : Fin (J + 1), ‖hermiteCoeff k G n.1‖ ^ 2 := by
  intro k J G
  exact
    (finiteHermiteSum_normSq (k := k) (a := fun n : Fin (J + 1) => hermiteCoeff k G n.1))
end HermitekLEAN
