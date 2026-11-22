-- Prove2me | solution 1 for Lean4LPD.exists_eventual_norm_threshold
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:06:13.198324+00:00
-- url     : https://prove2.me/submissions/8de1b752-fc45-4544-8f6e-555c1f0d9eac

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_Total
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_Threshold
public import Theorems.Thm_Lean4LPD_norm_majorant_tendsto_zero

set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Filter
open scoped Topology
namespace Lean4LPD
theorem _root_.solution {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1)
    (c M : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ m₀ : ℕ, 1 ≤ m₀ ∧ ∀ m, m₀ ≤ m →
      q ^ (m + 1) * (Real.exp 1 * ((m : ℝ) + 1)) ^ c * M ≤ ε := by
  have hevent : ∀ᶠ m : ℕ in atTop,
      q ^ (m + 1) * (Real.exp 1 * ((m : ℝ) + 1)) ^ c * M < ε :=
    (tendsto_order.mp (norm_majorant_tendsto_zero hq0 hq1 c M)).2 ε hε
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hevent
  refine ⟨max 1 N, le_max_left _ _, fun m hm => ?_⟩
  exact (hN m (le_trans (le_max_right _ _) hm)).le
end Lean4LPD
