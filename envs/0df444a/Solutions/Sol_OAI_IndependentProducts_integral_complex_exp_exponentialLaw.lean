-- Prove2me | solution 1 for OAI.IndependentProducts.integral_complex_exp_exponentialLaw
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T04:45:25.229211+00:00
-- url     : https://prove2.me/submissions/68263e86-bae4-47e1-9d44-fa5d904e4a3b

-- Generated from openai/math@1581d4c lean/OAI/Analysis/ProductSpaces/ExponentialLaw.lean:L67-L81
-- (upload_full_project.md Phase 4): solution for node OAI.IndependentProducts.integral_complex_exp_exponentialLaw. The node keeps its source
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
import Definitions.Def_OAI_Analysis_ProductSpaces_FiniteHeads
import Definitions.Def_OAI_Analysis_ProductSpaces_Resampling
import Definitions.Def_OAI_Analysis_ProductSpaces_ClosedTails
import Definitions.Def_OAI_Analysis_ProductSpaces_TailCoefficients
import Definitions.Def_OAI_Analysis_ProductSpaces_ExponentialLaw

-- ---- from OAI.Analysis.ProductSpaces.ExponentialLaw ----
namespace OAI

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology

noncomputable section

universe uE

namespace IndependentProducts

lemma exponentialLaw_density : exponentialLaw =
    (volume.restrict (Ioi (0 : ℝ))).withDensity (fun x => ENNReal.ofReal (Real.exp (-x))) := by
  change volume.withDensity (exponentialPDF 1) = _
  rw [← withDensity_indicator measurableSet_Ioi]
  apply withDensity_congr_ae
  filter_upwards [volume.ae_ne (0 : ℝ)] with x hx
  rw [exponentialPDF_eq]
  by_cases hp : 0 < x
  · simp [hp.le, hp]
  · have hn : x < 0 := lt_of_le_of_ne (le_of_not_gt hp) hx
    simp [not_le.mpr hn, hp]

lemma integral_exponentialLaw {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (f : ℝ → E) :
    (∫ x, f x ∂exponentialLaw) = ∫ x in Ioi 0, Real.exp (-x) • f x := by
  rw [exponentialLaw_density, integral_withDensity_eq_integral_toReal_smul (by fun_prop)
    (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (Real.exp_nonneg _)]

lemma integral_complex_exp_exponentialLaw (z : ℂ) (hz : z.re < 1) :
    (∫ x : ℝ, Complex.exp (z * x) ∂exponentialLaw) = 1 / (1 - z) := by
  rw [integral_exponentialLaw]
  have he : (fun x : ℝ => Real.exp (-x) • Complex.exp (z * x)) =
      (fun x : ℝ => Complex.exp ((z - 1) * x)) := by
    funext x
    rw [Complex.real_smul, Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [he, integral_exp_mul_complex_Ioi (by simpa using sub_neg.mpr hz) 0]
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero]
  calc
    -1 / (z - 1) = 1 / -(z - 1) := by rw [div_neg, neg_div]
    _ = 1 / (1 - z) := by congr 1; ring

end IndependentProducts

end

end OAI

-- ---- platform node ----
open OAI OAI.IndependentProducts
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
universe uE

theorem solution (z : ℂ) (hz : z.re < 1) :
    (∫ x : ℝ, Complex.exp (z * x) ∂exponentialLaw) = 1 / (1 - z) := by
  first
    | exact OAI.IndependentProducts.integral_complex_exp_exponentialLaw z hz
    | exact OAI.IndependentProducts.integral_complex_exp_exponentialLaw
    | (apply OAI.IndependentProducts.integral_complex_exp_exponentialLaw <;> assumption)
    | (intros; apply OAI.IndependentProducts.integral_complex_exp_exponentialLaw <;> assumption)
