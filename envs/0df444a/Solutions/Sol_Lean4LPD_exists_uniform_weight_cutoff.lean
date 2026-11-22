-- Prove2me | solution 1 for Lean4LPD.exists_uniform_weight_cutoff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:12:44.369073+00:00
-- url     : https://prove2.me/submissions/9917c304-f0ec-400e-979a-26dbe10750a6

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_Total
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_Threshold
public import Theorems.Thm_Lean4LPD_exists_norm_threshold

set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Filter
open scoped Topology
namespace Lean4LPD
theorem _root_.solution {ι : Type*} {error : ι → ℕ → ℝ} {q c M : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q < 1) (ko kh : ℕ)
    (hbound : ∀ i m, 1 ≤ m → error i (ko + (kh - 1) * m) ≤
      q ^ (m + 1) * (Real.exp 1 * ((m : ℝ) + 1)) ^ c * M)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ w m : ℕ, 1 ≤ m ∧ w = ko + (kh - 1) * m ∧ ∀ i, error i w ≤ ε := by
  obtain ⟨m, hm, hsmall⟩ := exists_norm_threshold hq0 hq1 c M hε
  exact ⟨ko + (kh - 1) * m, m, hm, rfl, fun i => (hbound i m hm).trans hsmall⟩
end Lean4LPD
