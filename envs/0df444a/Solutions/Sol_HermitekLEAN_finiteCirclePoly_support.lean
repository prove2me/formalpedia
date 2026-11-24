-- Prove2me | solution 1 for HermitekLEAN.finiteCirclePoly_support
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:50:18.423412+00:00
-- url     : https://prove2.me/submissions/97988270-475c-484e-b6f2-8cd4a2a8db3e

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
    ∀ {k D : ℕ} (r : ℝ) (a : Fin D → ℂ),
      finiteCirclePoly k r a =
        positiveTrigonometricPolynomial (frequencyBand 0 D) (finiteCircleCoeff k r a) := by
  intro k D r a
  rfl
end HermitekLEAN
