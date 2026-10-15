-- Prove2me | solution 1 for OAI.IndependentProducts.integral_excess_independent_copy
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T04:12:56.881057+00:00
-- url     : https://prove2.me/submissions/5100febd-65d0-422f-906b-71efe9a37ce2

-- Generated from openai/math@1581d4c lean/OAI/Analysis/ProductSpaces/GaussianMoments.lean:L143-L160
-- (upload_full_project.md Phase 4): solution for node OAI.IndependentProducts.integral_excess_independent_copy. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` restates it and is proved by it.
import Mathlib
import Definitions.Def_IndependentProducts
import Definitions.Def_OAI_Analysis_ProductSpaces_TreeObstruction
import Definitions.Def_OAI_Analysis_ProductSpaces_PathMoments
import Definitions.Def_OAI_Analysis_ProductSpaces_WeakNullity
import Definitions.Def_OAI_Analysis_ProductSpaces_ScalarBounds
import Definitions.Def_OAI_Analysis_ProductSpaces_GaussianMoments

-- ---- from OAI.Analysis.ProductSpaces.GaussianMoments ----
namespace OAI

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology

noncomputable section

universe uΩ uι

namespace IndependentProducts
section WeightedMoments
variable {Ω : Type uΩ} {ι : Type uι} [MeasurableSpace Ω] [Fintype ι]
variable {P : Measure Ω}

variable [IsProbabilityMeasure P]

end WeightedMoments
section GaussianVector
variable {ι : Type uι} [Fintype ι]

end GaussianVector
end IndependentProducts

namespace IndependentProducts

lemma excess_midpoint (t r u v : ℝ) (ht : 0 ≤ t) :
    excess t r ((u - v) / 2) ≤ (excess t r u + excess t r v) / 2 := by
  unfold excess
  rw [max_le_iff]
  constructor
  · rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    have hh := abs_sub u v
    have hh' := mul_le_mul_of_nonneg_left hh ht
    have hu := le_max_left (t * |u| - r) 0
    have hv := le_max_left (t * |v| - r) 0
    linarith
  · positivity

lemma integrable_excess {Ω : Type uΩ} [MeasurableSpace Ω] {P : Measure Ω}
    [IsFiniteMeasure P] {X : Ω → ℝ} (hX : Integrable X P) (t r : ℝ) :
    Integrable (fun ω => excess t r (X ω)) P :=
  ((hX.abs.const_mul t).sub (integrable_const r)).sup (integrable_const 0)

lemma integral_excess_independent_copy {Ω : Type uΩ} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : Ω → ℝ} (hX : Integrable X P)
    {t : ℝ} (ht : 0 ≤ t) (r : ℝ) :
    (∫ z : Ω × Ω, excess t r ((X z.1 - X z.2) / 2) ∂P.prod P) ≤
      ∫ ω, excess t r (X ω) ∂P := by
  have hxf := hX.comp_fst P
  have hxs := hX.comp_snd P
  have h1 := integrable_excess ((hxf.sub hxs).div_const 2) t r
  have h2 := ((integrable_excess hxf t r).add (integrable_excess hxs t r)).div_const 2
  calc
    _ ≤ ∫ z : Ω × Ω, (excess t r (X z.1) + excess t r (X z.2)) / 2 ∂P.prod P :=
      integral_mono h1 h2 (fun z => excess_midpoint t r (X z.1) (X z.2) ht)
    _ = ∫ ω, excess t r (X ω) ∂P := by
      simp_rw [div_eq_mul_inv]
      rw [integral_mul_const, integral_add (integrable_excess hxf t r) (integrable_excess hxs t r),
        integral_fun_fst (fun ω => excess t r (X ω)), integral_fun_snd (fun ω => excess t r (X ω))]
      simp
      ring

end IndependentProducts

namespace IndependentProducts

section GaussianFinite
variable {ι : Type uι} [Fintype ι]

end GaussianFinite
end IndependentProducts

end

end OAI

-- ---- platform node ----
open OAI OAI.IndependentProducts
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
universe uΩ uι

theorem solution {Ω : Type uΩ} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : Ω → ℝ} (hX : Integrable X P)
    {t : ℝ} (ht : 0 ≤ t) (r : ℝ) :
    (∫ z : Ω × Ω, excess t r ((X z.1 - X z.2) / 2) ∂P.prod P) ≤
      ∫ ω, excess t r (X ω) ∂P := by
  first
    | exact OAI.IndependentProducts.integral_excess_independent_copy hX ht r
    | exact OAI.IndependentProducts.integral_excess_independent_copy
    | (apply OAI.IndependentProducts.integral_excess_independent_copy <;> assumption)
    | (intros; apply OAI.IndependentProducts.integral_excess_independent_copy <;> assumption)
