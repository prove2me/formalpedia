-- Prove2me | solution 1 for Lean4LPD.exists_admissible_step_count
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:12:48.942821+00:00
-- url     : https://prove2.me/submissions/bf8e1922-be95-43cc-92ed-8ebe2223cca0

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_Total
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_Threshold

set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Filter
open scoped Topology
namespace Lean4LPD
theorem _root_.solution (m : ℕ) (B₁ B₂ : ℝ) :
    ∃ r : ℕ, 5 ≤ r ∧ m ≤ r ∧ B₁ ≤ (r : ℝ) ∧ B₂ ≤ (r : ℝ) := by
  obtain ⟨k, hk⟩ := exists_nat_ge (max B₁ B₂)
  have hkR : (k : ℝ) ≤ (max 5 (max m k) : ℕ) := by
    exact_mod_cast le_trans (le_max_right m k) (le_max_right 5 (max m k))
  exact ⟨max 5 (max m k), le_max_left _ _,
    le_trans (le_max_left m k) (le_max_right 5 (max m k)),
    (le_max_left B₁ B₂).trans (hk.trans hkR),
    (le_max_right B₁ B₂).trans (hk.trans hkR)⟩
end Lean4LPD
