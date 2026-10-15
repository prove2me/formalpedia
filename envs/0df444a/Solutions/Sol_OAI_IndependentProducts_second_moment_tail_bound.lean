-- Prove2me | solution 1 for OAI.IndependentProducts.second_moment_tail_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T04:07:05.763612+00:00
-- url     : https://prove2.me/submissions/cc38c843-b388-4e91-b743-922f853ad4a9

-- Generated from openai/math@1581d4c lean/OAI/Analysis/ProductSpaces/ScalarBounds.lean:L124-L159
-- (upload_full_project.md Phase 4): solution for node OAI.IndependentProducts.second_moment_tail_bound. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` restates it and is proved by it.
import Mathlib
import Definitions.Def_IndependentProducts
import Definitions.Def_OAI_Analysis_ProductSpaces_TreeObstruction
import Definitions.Def_OAI_Analysis_ProductSpaces_PathMoments
import Definitions.Def_OAI_Analysis_ProductSpaces_WeakNullity
import Definitions.Def_OAI_Analysis_ProductSpaces_ScalarBounds

-- ---- from OAI.Analysis.ProductSpaces.ScalarBounds ----
namespace OAI

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology

noncomputable section

universe uΩ uι

namespace IndependentProducts

section SecondMoment
variable {Ω : Type uΩ} [MeasurableSpace Ω] {μ : Measure Ω}

lemma integral_mul_sq_le [IsProbabilityMeasure μ] (f g : Ω → ℝ) (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    (∫ ω, f ω * g ω ∂μ) ^ 2 ≤ (∫ ω, f ω ^ 2 ∂μ) * ∫ ω, g ω ^ 2 ∂μ := by
  have h := real_inner_mul_inner_self_le (hf.toLp f) (hg.toLp g)
  have hfg : inner ℝ (hf.toLp f) (hg.toLp g) = ∫ ω, f ω * g ω ∂μ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with ω hω hω'
    simp only [hω, hω', RCLike.inner_apply, conj_trivial]
    ring
  have hff : inner ℝ (hf.toLp f) (hf.toLp f) = ∫ ω, f ω ^ 2 ∂μ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hf.coeFn_toLp] with ω hω
    rw [hω, real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs]
  have hgg : inner ℝ (hg.toLp g) (hg.toLp g) = ∫ ω, g ω ^ 2 ∂μ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hg.coeFn_toLp] with ω hω
    rw [hω, real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs]
  simpa only [hfg, hff, hgg, pow_two] using h

variable [IsProbabilityMeasure μ]

/-- A second-moment lower bound on the probability of exceeding half the mean. -/
lemma second_moment_tail_bound (V : Ω → ℝ) (hV : MemLp V 2 μ)
    (hVmeas : Measurable V) (hpos : ∀ ω, 0 ≤ V ω)
    (a b : ℝ) (ha : 0 ≤ a) (hb : a < b) (hmean : b ≤ ∫ ω, V ω ∂μ) :
    (b - a) ^ 2 ≤ (∫ ω, V ω ^ 2 ∂μ) * μ.real {ω | a ≤ V ω} := by
  let A : Set Ω := {ω | a ≤ V ω}
  have hm : MeasurableSet A := measurableSet_le measurable_const hVmeas
  have hint : Integrable V μ := hV.integrable (by norm_num)
  have hind : MemLp (A.indicator (fun _ : Ω => (1 : ℝ))) 2 μ := (memLp_const 1).indicator hm
  have hcs := integral_mul_sq_le V _ hV hind
  have hg : (∫ ω, (A.indicator (fun _ : Ω => (1 : ℝ)) ω) ^ 2 ∂μ) = μ.real A := by
    have he : (fun ω => (A.indicator (fun _ : Ω => (1 : ℝ)) ω) ^ 2) = A.indicator (fun _ => 1) := by
      funext ω
      by_cases hω : ω ∈ A <;> simp [hω]
    rw [he, integral_indicator hm]
    simp
  have hf : (∫ ω, V ω * A.indicator (fun _ => (1 : ℝ)) ω ∂μ) = ∫ ω in A, V ω ∂μ := by
    rw [← integral_indicator hm]
    congr 1
    funext ω
    by_cases hω : ω ∈ A <;> simp [hω]
  rw [hg, hf] at hcs
  have hlower : b - a ≤ ∫ ω in A, V ω ∂μ := by
    have hcompl : (∫ ω in Aᶜ, V ω ∂μ) ≤ a := by
      calc
        (∫ ω in Aᶜ, V ω ∂μ) ≤ ∫ _ in Aᶜ, a ∂μ := by
          apply integral_mono_ae hint.restrict (integrable_const _)
          filter_upwards [ae_restrict_mem hm.compl] with ω hω
          exact le_of_lt (not_le.mp hω)
        _ = a * μ.real Aᶜ := by simp [mul_comm]
        _ ≤ a * 1 := mul_le_mul_of_nonneg_left measureReal_le_one ha
        _ = a := mul_one _
    have he := integral_add_compl hm hint
    linarith
  exact ((sq_le_sq₀ (sub_nonneg.mpr hb.le)
    (integral_nonneg (μ := μ.restrict A) (f := V) hpos)).2 hlower).trans hcs

end SecondMoment
end IndependentProducts

namespace IndependentProducts

section GaussianSum
variable {Ω : Type uΩ} {ι : Type uι} [MeasurableSpace Ω] [DecidableEq ι]
  {P : Measure Ω} [IsProbabilityMeasure P]

variable [Fintype ι]

end GaussianSum
end IndependentProducts

end

end OAI

-- ---- platform node ----
open OAI OAI.IndependentProducts
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
universe uΩ uι
variable {Ω : Type uΩ} [MeasurableSpace Ω] {μ : Measure Ω}
variable [IsProbabilityMeasure μ]

theorem solution (V : Ω → ℝ) (hV : MemLp V 2 μ)
    (hVmeas : Measurable V) (hpos : ∀ ω, 0 ≤ V ω)
    (a b : ℝ) (ha : 0 ≤ a) (hb : a < b) (hmean : b ≤ ∫ ω, V ω ∂μ) :
    (b - a) ^ 2 ≤ (∫ ω, V ω ^ 2 ∂μ) * μ.real {ω | a ≤ V ω} := by
  first
    | exact OAI.IndependentProducts.second_moment_tail_bound V hV hVmeas hpos a b ha hb hmean
    | exact OAI.IndependentProducts.second_moment_tail_bound
    | (apply OAI.IndependentProducts.second_moment_tail_bound <;> assumption)
    | (intros; apply OAI.IndependentProducts.second_moment_tail_bound <;> assumption)
