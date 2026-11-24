-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.p2m810_antitone_null_set_integral
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T07:45:34.034019+00:00
-- url     : https://prove2.me/submissions/801620bd-b49a-4ab4-9cdc-3173819b5c92

import Theorems.Thm_Kyprianou_Ch08_StageB_p2m810_null_indicator_integral
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
open MeasureTheory ProbabilityTheory Set Filter Topology
open Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Strict record limit proof. -/
theorem solution :
    ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
      (g : Ω → ℝ) (A : ℕ → Set Ω), Integrable g P →
      (∀ n, NullMeasurableSet (A n) P) → Antitone A →
      Tendsto (fun n => ∫ ω in A n, g ω ∂P)
        atTop (nhds (∫ ω in ⋂ n, A n, g ω ∂P)) := by
  intro Ω mΩ P g A hg hm ha
  have hI (n : ℕ) := p2m810_null_indicator_integral Ω P g (A n) hg (hm n)
  have hJ := p2m810_null_indicator_integral Ω P g (⋂ n,A n) hg (NullMeasurableSet.iInter hm)
  have hlim (ω : Ω) : Tendsto (fun n => (A n).indicator g ω) atTop
      (nhds ((⋂ n,A n).indicator g ω)) := by
    by_cases h : ω ∈ ⋂ n,A n
    · have hmem (n : ℕ) := mem_iInter.mp h n
      simpa [Set.indicator_of_mem,h,hmem] using (tendsto_const_nhds (x := g ω))
    · obtain ⟨k,hk⟩ : ∃ k : ℕ, ω ∉ A k := by simpa [mem_iInter] using h
      rw [Set.indicator_of_notMem h]
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_ge_atTop k] with n hn
      have hnot : ω ∉ A n := fun hw => hk (ha hn hw)
      simp [hnot]
  have hbound (n : ℕ) : ∀ᵐ ω ∂P, ‖(A n).indicator g ω‖ ≤ ‖g ω‖ :=
    Filter.Eventually.of_forall (fun ω => by by_cases h : ω ∈ A n <;> simp [h])
  have h := tendsto_integral_of_dominated_convergence (fun ω => ‖g ω‖)
    (fun n => (hI n).1) hg.norm hbound (Filter.Eventually.of_forall hlim)
  rw [hJ.2] at h
  exact h.congr (fun n => (hI n).2)
