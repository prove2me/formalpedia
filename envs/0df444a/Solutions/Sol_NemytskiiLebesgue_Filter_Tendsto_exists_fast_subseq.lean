-- Prove2me | solution 1 for NemytskiiLebesgue.Filter.Tendsto.exists_fast_subseq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:34:10.520197+00:00
-- url     : https://prove2.me/submissions/bb0c5663-72b2-4d65-940e-bf3a7a53cf7d

module
public import Mathlib.MeasureTheory.Function.UnifTight
public import Definitions.Def_LeanPool_NemytskiiLebesgue_Caratheodory
public import Definitions.Def_LeanPool_NemytskiiLebesgue_Continuity

set_option autoImplicit true
@[expose] public section
public section
open NemytskiiLebesgue
open scoped NemytskiiLebesgue
open MeasureTheory _root_.Filter
open scoped NNReal ENNReal Topology
namespace NemytskiiLebesgue
namespace Filter.Tendsto
theorem _root_.solution
    {f : ℕ → ℝ≥0∞} (hf : Tendsto f atTop (𝓝 0)) :
    ∃ s : ℕ → ℕ, StrictMono s ∧ ∀ n : ℕ, f (s n) ≤ (1 / 2 : ℝ≥0∞) ^ n := by
  have hN : ∀ k : ℕ, ∃ N : ℕ, ∀ n ≥ N, f n ≤ (1 / 2) ^ k :=
    fun k : ℕ => by simpa using hf.eventually (ge_mem_nhds <| ENNReal.pow_pos (by norm_num) _)
  choose N hN using hN
  exact ⟨fun n : ℕ => n.recOn (N 0) fun k : ℕ => fun m : ℕ => (N (k + 1)) ⊔ (m + 1),
    strictMono_nat_of_lt_succ (by simp),
    (hN _ _ <| ·.recOn (by norm_num) (by simp))⟩
end Filter.Tendsto
end NemytskiiLebesgue
