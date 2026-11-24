-- Prove2me | solution 1 for HermitekLEAN.h_k_expansion
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:50:38.282829+00:00
-- url     : https://prove2.me/submissions/7c3d4b86-c5de-4a86-94fb-b1b6cb896bef

module
public import Definitions.Def_LeanPool_PhaseRetrieval_FourierParseval
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite_Definitions
public import Mathlib.Analysis.Complex.Isometry
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
public import Mathlib.MeasureTheory.Integral.Gamma
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermitek_TrueLevelBasis
public import Theorems.Thm_HermitekLEAN_hermiteCoeff_expansion
public import Theorems.Thm_HermitekLEAN_hermiteCoeff_parseval

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
      G ∈ Hk k →
        ∃ g : ℕ → ℂ,
          G = hermiteSeries k g ∧
            weightedNormSq G = ∑' n : ℕ, ‖g n‖ ^ 2 := by
  intro k G hG
  exact ⟨hermiteCoeff k G, hermiteCoeff_expansion hG, hermiteCoeff_parseval hG⟩
end HermitekLEAN
