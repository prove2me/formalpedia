-- Prove2me | solution 1 for Lean4LPD.exists_norm_threshold
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:07:25.615565+00:00
-- url     : https://prove2.me/submissions/38b378aa-06e4-493c-87a3-6426ed171340

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_Total
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_Threshold
public import Theorems.Thm_Lean4LPD_exists_eventual_norm_threshold

set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Filter
open scoped Topology
namespace Lean4LPD
theorem _root_.solution {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) (c M : ℝ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ m : ℕ, 1 ≤ m ∧ q ^ (m + 1) * (Real.exp 1 * ((m : ℝ) + 1)) ^ c * M ≤ ε := by
  obtain ⟨m, hm, hbound⟩ := exists_eventual_norm_threshold hq0 hq1 c M hε
  exact ⟨m, hm, hbound m le_rfl⟩
end Lean4LPD
