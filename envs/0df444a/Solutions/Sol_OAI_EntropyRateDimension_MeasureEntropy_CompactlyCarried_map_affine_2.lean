-- Prove2me | solution 2 for OAI.EntropyRateDimension.MeasureEntropy.CompactlyCarried.map_affine
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T05:55:09.037045+00:00
-- url     : https://prove2.me/submissions/e419447c-0891-49bc-aa3f-e0a2eeed7666

-- Generated from openai/math@1581d4c lean/OAI/MeasureTheory/SelfSimilar/MeasureEntropy.lean:L383-L396
-- (upload_full_project.md Phase 4): solution for node OAI.EntropyRateDimension.MeasureEntropy.CompactlyCarried.map_affine. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_SelfSimilar
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Basic
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteEntropy
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteDistribution
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_MeasureEntropy

-- ---- from OAI.MeasureTheory.SelfSimilar.MeasureEntropy ----
namespace OAI

universe uι uα uβ uγ uδ

section
open scoped BigOperators ENNReal
open MeasureTheory
namespace EntropyRateDimension
namespace MeasureEntropy

theorem CompactlyCarried.map_affine {μ : Measure ℝ} (hμ : CompactlyCarried μ) (a b : ℝ) :
    CompactlyCarried (μ.map (fun x => a*x+b)) := by
  obtain ⟨B,hB,hμB⟩ := hμ
  let C := |a| * B + |b|
  refine ⟨C,by dsimp [C]; positivity,?_⟩
  rw [Measure.map_apply (f := fun x : ℝ => a*x+b) (by fun_prop) measurableSet_Icc.compl]
  apply measure_mono_null _ hμB
  intro x hx hxin
  apply hx
  have hxb : |x| ≤ B := abs_le.mpr hxin
  have hax : |a*x+b| ≤ C := (abs_add_le _ _).trans (by
    rw [abs_mul]
    exact add_le_add_left (mul_le_mul_of_nonneg_left hxb (abs_nonneg a)) _)
  exact abs_le.mp hax

end MeasureEntropy
end EntropyRateDimension
end

end OAI

-- ---- platform node ----
open OAI OAI.EntropyRateDimension OAI.EntropyRateDimension.MeasureEntropy
open scoped BigOperators ENNReal
open MeasureTheory


theorem solution : type_of% @_root_.OAI.EntropyRateDimension.MeasureEntropy.CompactlyCarried.map_affine := @_root_.OAI.EntropyRateDimension.MeasureEntropy.CompactlyCarried.map_affine
