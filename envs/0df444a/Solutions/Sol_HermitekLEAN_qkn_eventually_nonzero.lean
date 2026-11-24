-- Prove2me | solution 1 for HermitekLEAN.qkn_eventually_nonzero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:12:53.913661+00:00
-- url     : https://prove2.me/submissions/854c37b3-b944-418d-a985-d927115b0401

module
public import Definitions.Def_LeanPool_PhaseRetrieval_FourierParseval
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite_Definitions
public import Mathlib.Analysis.Complex.Isometry
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
public import Mathlib.MeasureTheory.Integral.Gamma
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermitek_TrueLevelBasis
public import Theorems.Thm_HermitekLEAN_qkn_eventual_lower_bound

set_option autoImplicit true
@[expose] public section
public section
open Complex MeasureTheory Real Finset
open scoped BigOperators Topology
noncomputable section
open HermitekLEAN
namespace HermitekLEAN
theorem _root_.solution :
    ∀ k n : ℕ,
      ∃ R0 : ℝ,
        1 ≤ R0 ∧
          ∀ r ≥ R0, qkn k n r ≠ 0 := by
  intro k n
  obtain ⟨R, c, hR, hc, hbound⟩ := qkn_eventual_lower_bound k n
  refine ⟨R, hR, fun r hr hqkn => ?_⟩
  have h1 := hbound r hr
  rw [hqkn, Complex.ofReal_zero, norm_zero] at h1
  have h2 : 0 < r := lt_of_lt_of_le (lt_of_lt_of_le zero_lt_one hR) hr
  linarith only [hc, h1, h2, mul_pos hc (pow_pos h2 n)]
end HermitekLEAN
