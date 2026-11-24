-- Prove2me | solution 1 for HermitekLEAN.qkn_real
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:59:35.838186+00:00
-- url     : https://prove2.me/submissions/aef59de5-f01c-4e82-bd38-d2ecc7e25ed3

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
    ∀ {k n : ℕ} {r : ℝ}, star (qkn k n r : ℂ) = (qkn k n r : ℂ) := by
  simp only [RCLike.star_def, conj_ofReal, implies_true]
end HermitekLEAN
