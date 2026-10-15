-- Prove2me | solution 1 for OAI.IndependentProducts.midpointGain_eq_integral_excess
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T04:22:31.773353+00:00
-- url     : https://prove2.me/submissions/4c18145f-f73d-470d-be6a-7d6619c0fec6

-- Generated from openai/math@1581d4c lean/OAI/Analysis/ProductSpaces/ConditionalBounds.lean:L78-L113
-- (upload_full_project.md Phase 4): solution for node OAI.IndependentProducts.midpointGain_eq_integral_excess. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` restates it and is proved by it.
import Mathlib
import Definitions.Def_IndependentProducts
import Definitions.Def_OAI_Analysis_ProductSpaces_TreeObstruction
import Definitions.Def_OAI_Analysis_ProductSpaces_PathMoments
import Definitions.Def_OAI_Analysis_ProductSpaces_WeakNullity
import Definitions.Def_OAI_Analysis_ProductSpaces_ScalarBounds
import Definitions.Def_OAI_Analysis_ProductSpaces_GaussianMoments
import Definitions.Def_OAI_Analysis_ProductSpaces_GaussianExcess
import Definitions.Def_OAI_Analysis_ProductSpaces_RandomSigns
import Definitions.Def_OAI_Analysis_ProductSpaces_MidpointModulus
import Definitions.Def_OAI_Analysis_ProductSpaces_ConditionalBounds

-- ---- from OAI.Analysis.ProductSpaces.ConditionalBounds ----
namespace OAI

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology

noncomputable section

universe uΛ uΩ uι

namespace IndependentProducts
section ConditionalScalar
variable {ι : Type uι} {Ω : Type uΩ} [Fintype ι] [MeasurableSpace Ω]
variable (μ : Measure ℝ) [IsProbabilityMeasure μ] (ν : Measure Ω)
variable (hμ : MemLp (fun w : ℝ => w) 2 μ)

variable [IsProbabilityMeasure ν]

end ConditionalScalar

lemma real_midpoint_excess (a c : ℝ) :
    (|a + c| + |a - c|) / 2 - |a| = max (|c| - |a|) 0 := by
  simp only [abs_eq_max_neg, max_def]
  split_ifs <;> linarith

lemma midpointGain_eq_integral_excess {Ω : Type uΩ} [MeasurableSpace Ω] (P : Measure Ω)
    (x y : Lp ℝ 1 P) (f g : Ω → ℝ) (hf : x =ᵐ[P] f) (hg : y =ᵐ[P] g)
    (t : ℝ) (ht : 0 ≤ t) :
    midpointGain t x y = ∫ ω, excess t |f ω| (g ω) ∂P := by
  have hx : Integrable (fun ω => x ω) P := memLp_one_iff_integrable.mp (Lp.memLp x)
  have hy : Integrable (fun ω => y ω) P := memLp_one_iff_integrable.mp (Lp.memLp y)
  have hp : Integrable (fun ω => |x ω + t * y ω|) P := (hx.add (hy.const_mul t)).abs
  have hm : Integrable (fun ω => |x ω - t * y ω|) P := (hx.sub (hy.const_mul t)).abs
  have he : (fun ω => excess t |x ω| (y ω)) =
      fun ω => (|x ω + t * y ω| + |x ω - t * y ω|) / 2 - |x ω| := by
    funext ω
    rw [real_midpoint_excess, abs_mul, abs_of_nonneg ht]
    rfl
  have hp' : ‖x + t • y‖ = ∫ ω, |x ω + t * y ω| ∂P := by
    rw [L1.norm_eq_integral_norm]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_add x (t • y), Lp.coeFn_smul t y] with ω h1 h2
    simp only [h1, Pi.add_apply, h2, Pi.smul_apply, smul_eq_mul, Real.norm_eq_abs]
  have hm' : ‖x - t • y‖ = ∫ ω, |x ω - t * y ω| ∂P := by
    rw [L1.norm_eq_integral_norm]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub x (t • y), Lp.coeFn_smul t y] with ω h1 h2
    simp only [h1, Pi.sub_apply, h2, Pi.smul_apply, smul_eq_mul, Real.norm_eq_abs]
  calc
    _ = ∫ ω, excess t |x ω| (y ω) ∂P := by
      have hs : Integrable (fun ω => (|x ω + t * y ω| + |x ω - t * y ω|) / 2) P := by
        simpa only [Pi.add_apply] using (hp.add hm).div_const 2
      have hi := integral_add hp hm
      rw [he, integral_sub hs hx.abs, integral_div, hi]
      unfold midpointGain
      rw [hp', hm', L1.norm_eq_integral_norm]
      simp only [Real.norm_eq_abs]
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [hf, hg] with ω h1 h2
      rw [h1, h2]

end IndependentProducts

namespace IndependentProducts
section IntegratedConditional
variable {ι : Type uι} {Ω : Type uΩ} {Λ : Type uΛ}
  [Fintype ι] [MeasurableSpace Ω] [MeasurableSpace Λ]
variable (μ : Measure ℝ) [IsProbabilityMeasure μ] (ν : Measure Ω) [IsProbabilityMeasure ν]
variable (η : Measure Λ) [IsProbabilityMeasure η]

end IntegratedConditional
end IndependentProducts

end

end OAI

-- ---- platform node ----
open OAI OAI.IndependentProducts
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
universe uΛ uΩ uι

theorem solution {Ω : Type uΩ} [MeasurableSpace Ω] (P : Measure Ω)
    (x y : Lp ℝ 1 P) (f g : Ω → ℝ) (hf : x =ᵐ[P] f) (hg : y =ᵐ[P] g)
    (t : ℝ) (ht : 0 ≤ t) :
    midpointGain t x y = ∫ ω, excess t |f ω| (g ω) ∂P := by
  first
    | exact OAI.IndependentProducts.midpointGain_eq_integral_excess P x y f g hf hg t ht
    | exact OAI.IndependentProducts.midpointGain_eq_integral_excess
    | (apply OAI.IndependentProducts.midpointGain_eq_integral_excess <;> assumption)
    | (intros; apply OAI.IndependentProducts.midpointGain_eq_integral_excess <;> assumption)
