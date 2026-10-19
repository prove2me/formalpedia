-- Prove2me | solution 1 for OAI.EntropyRateDimension.MeasureEntropy.CompactlyCarried.map_affine
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T05:19:31.291831+00:00
-- url     : https://prove2.me/submissions/78c1f834-4441-4023-8d89-70f81b2397e9

import Mathlib
import Definitions.Def_SelfSimilar
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Basic
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteEntropy
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteDistribution
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_MeasureEntropy

open OAI OAI.EntropyRateDimension OAI.EntropyRateDimension.MeasureEntropy
universe uι uα uβ uγ uδ
open scoped BigOperators ENNReal
open MeasureTheory


theorem solution {μ : Measure ℝ} (hμ : CompactlyCarried μ) (a b : ℝ) :
    CompactlyCarried (μ.map (fun x => a*x+b)) := by
  obtain ⟨B, hB0, hB⟩ := hμ
  refine ⟨|a| * B + |b|, by positivity, ?_⟩
  have hf : Measurable (fun x : ℝ => a * x + b) := by fun_prop
  rw [Measure.map_apply hf measurableSet_Icc.compl]
  apply measure_mono_null _ hB
  intro x hx
  simp only [Set.mem_preimage, Set.mem_compl_iff] at hx ⊢
  intro hxB
  apply hx
  have h1 : |x| ≤ B := abs_le.mpr hxB
  have h2 : |a * x + b| ≤ |a| * B + |b| := calc
    |a * x + b| ≤ |a * x| + |b| := abs_add_le _ _
    _ = |a| * |x| + |b| := by rw [abs_mul]
    _ ≤ |a| * B + |b| := by gcongr
  exact abs_le.mp h2

