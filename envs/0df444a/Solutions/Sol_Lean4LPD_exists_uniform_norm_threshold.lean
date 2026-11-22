-- Prove2me | solution 1 for Lean4LPD.exists_uniform_norm_threshold
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:12:43.926612+00:00
-- url     : https://prove2.me/submissions/d7de0d5a-6562-4f69-8ad1-c33a5e606356

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
theorem _root_.solution {ι : Type*} {error : ι → ℕ → ℝ} {q c M : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hbound : ∀ i m, 1 ≤ m → error i m ≤
      q ^ (m + 1) * (Real.exp 1 * ((m : ℝ) + 1)) ^ c * M)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ m₀ : ℕ, 1 ≤ m₀ ∧ ∀ m, m₀ ≤ m → ∀ i, error i m ≤ ε := by
  obtain ⟨m₀, hm₀, hsmall⟩ := exists_eventual_norm_threshold hq0 hq1 c M hε
  exact ⟨m₀, hm₀, fun m hm i =>
    (hbound i m (le_trans hm₀ hm)).trans (hsmall m hm)⟩
end Lean4LPD
