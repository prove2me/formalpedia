-- Prove2me | solution 1 for NemytskiiLebesgue.Filter.Tendsto.extract_fast_subseq_eLpNorm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:37:18.236865+00:00
-- url     : https://prove2.me/submissions/9f4d4c1c-6e31-4725-bbb1-0fe2eeee2211

module
public import Mathlib.Analysis.Calculus.MeanValue
public import Definitions.Def_LeanPool_NemytskiiLebesgue_Continuity
public import Definitions.Def_LeanPool_NemytskiiLebesgue_Frechet
public import Theorems.Thm_NemytskiiLebesgue_Filter_Tendsto_exists_fast_subseq


set_option autoImplicit true
@[expose] public section
public section
open NemytskiiLebesgue
open scoped NemytskiiLebesgue
open MeasureTheory _root_.Filter
open scoped ENNReal Topology
namespace NemytskiiLebesgue
namespace Filter.Tendsto
theorem _root_.solution
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {E : Type*} [NormedAddCommGroup E]
    {p : ℝ≥0∞} {l : ℕ → Ω → E} (hlp : Tendsto (fun n : ℕ => eLpNorm (l n) p μ) atTop (𝓝 0)) :
    ∃ s : ℕ → ℕ, StrictMono s ∧ ∀ k : ℕ, eLpNorm (l (s k)) p μ ≤ ↱(1 / 2 ^ k) := by
  convert Filter.Tendsto.exists_fast_subseq hlp
  rw [←one_pow, ←div_pow, ENNReal.ofReal_pow one_half_pos.le]
  norm_num [ENNReal.ofReal_div_of_pos]
end Filter.Tendsto
end NemytskiiLebesgue
