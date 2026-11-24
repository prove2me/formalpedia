-- Prove2me | solution 1 for HermitekLEAN.truncCirclePoly_l2_identity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:50:34.861644+00:00
-- url     : https://prove2.me/submissions/1bab2882-9949-4fa0-9774-232037b28b37

module
public import Definitions.Def_LeanPool_PhaseRetrieval_FourierParseval
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite_Definitions
public import Mathlib.Analysis.Complex.Isometry
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
public import Mathlib.MeasureTheory.Integral.Gamma
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermitek_TrueLevelBasis
public import Theorems.Thm_HermitekLEAN_finiteCirclePoly_l2_identity

set_option autoImplicit true
@[expose] public section
public section
open Complex MeasureTheory Real Finset
open scoped BigOperators Topology
noncomputable section
open HermitekLEAN
namespace HermitekLEAN
theorem _root_.solution :
    ∀ (k J : ℕ) (r : ℝ) (G : ℂ → ℂ),
      circleL2Sq (truncCirclePoly k r J G) =
        ∑ n : Fin (J + 1), ‖hermiteCoeff k G n.1‖ ^ 2 * |qkn k n.1 r| ^ 2 := by
  intro k J r G
  exact
    (finiteCirclePoly_l2_identity (k := k) (D := J + 1) (r := r)
      (a := fun n : Fin (J + 1) => hermiteCoeff k G n.1))
end HermitekLEAN
