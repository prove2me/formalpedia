-- Prove2me | solution 1 for HermitekLEAN.continuous_of_mem_Hk
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:51:08.597157+00:00
-- url     : https://prove2.me/submissions/9a6801f8-d932-4ac6-85c1-e5a61f7ce04f

module
public import Definitions.Def_LeanPool_PhaseRetrieval_FourierParseval
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite_Definitions
public import Mathlib.Analysis.Complex.Isometry
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
public import Mathlib.MeasureTheory.Integral.Gamma
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermitek_TrueLevelBasis
public import Theorems.Thm_HermitekLEAN_hermite_series_locally_uniform

set_option autoImplicit true
@[expose] public section
public section
open Complex MeasureTheory Real Finset
open scoped BigOperators Topology
noncomputable section
open HermitekLEAN
namespace HermitekLEAN
theorem _root_.solution :
    ∀ {k : ℕ} {G : ℂ → ℂ},
      G ∈ Hk k → Continuous G := by
  intro k G hG
  obtain ⟨_, _, hcont⟩ := hermite_series_locally_uniform hG
  exact hcont
end HermitekLEAN
