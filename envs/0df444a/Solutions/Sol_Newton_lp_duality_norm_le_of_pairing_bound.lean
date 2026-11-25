-- Prove2me | solution 1 for Newton.lp_duality_norm_le_of_pairing_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:54:57.560748+00:00
-- url     : https://prove2.me/submissions/9a2bbf0d-f258-45df-9e08-4b0fcf68bfc9

import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sign
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_Newton_MeasureTheory_Integral_Holder
import Definitions.Def_Newton_MeasureTheory_Function_LpSpace_Duality
import Theorems.Thm_Newton_lp_duality_exists_norm_one_attainer

set_option autoImplicit false
open scoped ENNReal
open MeasureTheory Real Topology
open Newton
variable {α : Type*} [MeasurableSpace α] {μ : Measure α}
variable {β : Type*} [MeasurableSpace β] {ν : Measure β}
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
namespace Newton
theorem _root_.solution
    (p q : ℝ≥0∞) (hp : 1 < p) (hq : 1 < q)
    (hpq : IsConjugateExponent p q)
    {f : α → ℝ}
    (hf : MemLp f p μ)
    {B : ℝ}
    (hB : ∀ g : α → ℝ,
      MemLp g q μ →
      (eLpNorm g q μ).toReal ≤ 1 →
      Integrable (fun x => f x * g x) μ →
      |∫ x, f x * g x ∂μ| ≤ B) :
    (eLpNorm f p μ).toReal ≤ B := by
  have h_nonneg : 0 ≤ (eLpNorm f p μ).toReal := ENNReal.toReal_nonneg
  by_cases hzero : (eLpNorm f p μ).toReal = 0
  · have hB_nonneg : 0 ≤ B := by
      have h_zero_mem : MemLp (fun _ : α => (0 : ℝ)) q μ := MemLp.zero
      have h_zero_norm : (eLpNorm (fun _ : α => (0 : ℝ)) q μ).toReal ≤ 1 := by
        simp
      have h_zero_int : Integrable (fun x => f x * (0 : ℝ)) μ := by
        simp
      have h_bound :=
        hB (fun _ : α => (0 : ℝ)) h_zero_mem h_zero_norm h_zero_int
      simpa using h_bound
    simpa [hzero] using hB_nonneg
  · have hf_ne_zero : (eLpNorm f p μ).toReal ≠ 0 := hzero
    obtain ⟨g, hg_mem, hg_norm_one, hg_int, hg_eq⟩ :=
      lp_duality_exists_norm_one_attainer (μ := μ)
        (p := p) (q := q) hp hq hpq hf hf_ne_zero
    have h_bound := hB g hg_mem (by simp [hg_norm_one]) hg_int
    have h_abs := h_bound
    have : (eLpNorm f p μ).toReal ≤ B := by
      simpa [hg_eq, abs_of_nonneg h_nonneg]
        using h_abs
    exact this
end Newton
