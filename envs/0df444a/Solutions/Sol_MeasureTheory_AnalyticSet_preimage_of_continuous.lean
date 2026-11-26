-- Prove2me | solution 1 for MeasureTheory.AnalyticSet.preimage_of_continuous
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:03:17.157544+00:00
-- url     : https://prove2.me/submissions/6bbb139e-710b-4e40-b5ef-f24d7c9df5c2

import Definitions.Def_BicausalOT_DescriptiveSetTheory_Capacitability
import Definitions.Def_BicausalOT_DescriptiveSetTheory_LowerSemianalytic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Probability.Kernel.Composition.Prod
import Mathlib.MeasureTheory.Integral.Lebesgue.Sub
import Definitions.Def_BicausalOT_DescriptiveSetTheory_KernelIntegral

set_option autoImplicit false
open Set Topology MeasureTheory ProbabilityTheory Filter
open scoped Classical ENNReal
noncomputable section
namespace MeasureTheory.AnalyticSet
theorem _root_.solution
    {W V : Type*} [TopologicalSpace W] [PolishSpace W]
    [TopologicalSpace V] [T2Space V]
    {S : Set V} (hS : AnalyticSet S) {h : W → V} (hh : Continuous h) :
    AnalyticSet (h ⁻¹' S) := by
  rw [AnalyticSet] at hS
  rcases hS with rfl | ⟨g, hg_cont, hg_range⟩
  · rw [preimage_empty]; exact analyticSet_empty
  have hpre : h ⁻¹' range g = Prod.fst '' {p : W × (ℕ → ℕ) | g p.2 = h p.1} := by
    ext w
    simp only [mem_preimage, mem_range, mem_image, Prod.exists, mem_ofPred_eq]
    constructor
    · rintro ⟨σ, hσ⟩; exact ⟨w, σ, hσ, rfl⟩
    · rintro ⟨w', σ, hgσ, rfl⟩; exact ⟨σ, hgσ⟩
  rw [← hg_range, hpre]
  refine AnalyticSet.image_of_continuous ?_ continuous_fst
  exact (isClosed_eq (hg_cont.comp continuous_snd)
    (hh.comp continuous_fst)).analyticSet
end MeasureTheory.AnalyticSet
