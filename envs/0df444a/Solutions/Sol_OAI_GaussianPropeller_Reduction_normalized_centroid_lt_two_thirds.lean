-- Prove2me | solution 1 for OAI.GaussianPropeller.Reduction.normalized_centroid_lt_two_thirds
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T08:47:00.805055+00:00
-- url     : https://prove2.me/submissions/5794a6cd-bd1f-43a1-b8d9-c1fe9f8d4ff4

-- Generated from openai/math@1581d4c lean/OAI/Probability/GaussianPropeller/Attainment.lean:L368-L382
-- (upload_full_project.md Phase 4): solution for node OAI.GaussianPropeller.Reduction.normalized_centroid_lt_two_thirds. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_GaussianPropeller
import Definitions.Def_OAI_Probability_GaussianPropeller_Moments
import Definitions.Def_OAI_Probability_GaussianPropeller_Dual
import Definitions.Def_OAI_Probability_GaussianPropeller_Deletion
import Definitions.Def_OAI_Probability_GaussianPropeller_Translation
import Definitions.Def_OAI_Probability_GaussianPropeller_HeatConvolution
import Definitions.Def_OAI_Probability_GaussianPropeller_Quantile
import Definitions.Def_OAI_Probability_GaussianPropeller_QuantileCalculus
import Definitions.Def_OAI_Probability_GaussianPropeller_HeatMaximum
import Definitions.Def_OAI_Probability_GaussianPropeller_SmoothedConcavity
import Definitions.Def_OAI_Probability_GaussianPropeller_SoftMinimum
import Definitions.Def_OAI_Probability_GaussianPropeller_ConeConcavity
import Definitions.Def_OAI_Probability_GaussianPropeller_OneCell
import Definitions.Def_OAI_Probability_GaussianPropeller_Mills
import Definitions.Def_OAI_Probability_GaussianPropeller_Taylor
import Definitions.Def_OAI_Probability_GaussianPropeller_ProbabilityBounds
import Definitions.Def_OAI_Probability_GaussianPropeller_Attainment

-- ---- from OAI.Probability.GaussianPropeller.Moments ----
namespace OAI

universe uF

open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace GaussianPropeller

open scoped RealInnerProductSpace

theorem integrable_id_gaussian (d : ℕ) :
    Integrable (fun x : Space d => x) (gaussian d) := by
  exact IsGaussian.integrable_id (μ := stdGaussian (Space d))

theorem integrable_id_restrict (d : ℕ) (A : Set (Space d)) :
    Integrable (fun x : Space d => x) ((gaussian d).restrict A) :=
  (integrable_id_gaussian d).restrict

end GaussianPropeller

end OAI

-- ---- from OAI.Probability.GaussianPropeller.Analytic ----
namespace OAI

universe uE

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal RealInnerProductSpace
open Filter
open scoped Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
open scoped RealInnerProductSpace
open Set Filter
open scoped Topology RealInnerProductSpace
open scoped NNReal
open Set Filter
open scoped Topology RealInnerProductSpace NNReal
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology BigOperators

open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology

namespace GaussianPropeller.Analytic

theorem integral_pos_mul_exp {b : ℝ} (hb : 0 < b) :
    ∫ r : ℝ in Ioi 0, r * Real.exp (-b * r ^ 2) = (2 * b)⁻¹ := by
  have hb' : b ≠ 0 := ne_of_gt hb
  have hd (x : ℝ) : HasDerivAt (fun x => -(2 * b)⁻¹ * Real.exp (-b * x ^ 2))
      (x * Real.exp (-b * x ^ 2)) x := by
    apply (((hasDerivAt_pow 2 x).const_mul (-b)).exp.const_mul (-(2 * b)⁻¹)).congr_deriv
    field_simp [hb']
    ring
  have ht : Tendsto (fun y : ℝ => -(2 * b)⁻¹ * Real.exp (-b * y ^ 2))
      atTop (𝓝 (-(2 * b)⁻¹ * 0)) := by
    apply Tendsto.const_mul
    exact Real.tendsto_exp_atBot.comp
      ((tendsto_pow_atTop two_ne_zero).const_mul_atTop_of_neg (neg_lt_zero.mpr hb))
  convert integral_Ioi_of_hasDerivAt_of_tendsto' (fun x _ => hd x)
    (integrable_mul_exp_neg_mul_sq hb).integrableOn ht using 1
  simp

theorem integral_abs_mul_exp {b : ℝ} (hb : 0 < b) :
    ∫ r : ℝ, |r| * Real.exp (-b * r ^ 2) = b⁻¹ := by
  let f : ℝ → ℝ := fun r => |r| * Real.exp (-b * r ^ 2)
  have hf : Integrable f := by
    simpa only [f, abs_mul, abs_of_pos (Real.exp_pos _)] using
      (integrable_mul_exp_neg_mul_sq hb).abs
  have hpos : ∫ r in Ioi 0, f r = (2 * b)⁻¹ := by
    rw [← integral_pos_mul_exp hb]
    exact setIntegral_congr_fun measurableSet_Ioi (fun r hr => by
      simp only [f, abs_of_pos (show (0 : ℝ) < r from hr)])
  have hneg : ∫ r in Iic 0, f r = ∫ r in Ioi 0, f r := by
    calc
      ∫ r in Iic 0, f r = ∫ r in Ioi 0, f (-r) := by
        simpa [f] using (integral_comp_neg_Ioi 0 f).symm
      _ = ∫ r in Ioi 0, f r := by simp only [f, abs_neg, neg_sq]
  change (∫ r, f r) = _
  rw [← integral_add_compl measurableSet_Ioi hf, compl_Ioi, hneg, hpos]
  field_simp
  ring

theorem integral_abs_gaussianReal_std :
    ∫ x : ℝ, |x| ∂gaussianReal 0 1 = 2 / Real.sqrt (2 * Real.pi) := by
  rw [integral_gaussianReal_eq_integral_smul (by norm_num : (1 : NNReal) ≠ 0)]
  have hfun : (fun x : ℝ => gaussianPDFReal 0 1 x • |x|) =
      (fun x : ℝ => (Real.sqrt (2 * Real.pi))⁻¹ *
        (|x| * Real.exp (-(1 / 2 : ℝ) * x ^ 2))) := by
    ext x
    simp only [gaussianPDFReal, NNReal.coe_one, sub_zero, mul_one, smul_eq_mul]
    rw [show -(x ^ 2) / (2 : ℝ) = -(1 / 2 : ℝ) * x ^ 2 by ring]
    ring
  rw [hfun, integral_const_mul, integral_abs_mul_exp (by norm_num : (0 : ℝ) < 1/2)]
  norm_num
  ring

theorem integral_abs_dual_stdGaussian {E : Type uE} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (L : StrongDual ℝ E) :
    ∫ x, |L x| ∂stdGaussian E = ‖L‖ * (2 / Real.sqrt (2 * Real.pi)) := by
  have hm : (stdGaussian E).map L = (gaussianReal 0 1).map (‖L‖ * ·) := by
    rw [IsGaussian.map_eq_gaussianReal, integral_strongDual_stdGaussian,
      variance_dual_stdGaussian, gaussianReal_map_const_mul]
    simp only [mul_zero, mul_one, Real.toNNReal_of_nonneg (sq_nonneg ‖L‖)]
  rw [← integral_map L.continuous.aemeasurable (by fun_prop :
    AEStronglyMeasurable (fun x : ℝ => |x|) ((stdGaussian E).map L)), hm,
    integral_map (by fun_prop) (by fun_prop)]
  simp_rw [abs_mul, abs_of_nonneg (norm_nonneg L)]
  rw [integral_const_mul, integral_abs_gaussianReal_std]

theorem integral_abs_inner_stdGaussian {E : Type uE} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (v : E) :
    ∫ x, |⟪v, x⟫| ∂stdGaussian E = ‖v‖ * (2 / Real.sqrt (2 * Real.pi)) := by
  simpa only [InnerProductSpace.toDual_apply_apply, LinearIsometryEquiv.norm_map] using
    integral_abs_dual_stdGaussian (InnerProductSpace.toDual ℝ E v)

end GaussianPropeller.Analytic

end OAI

-- ---- from OAI.Probability.GaussianPropeller.Attainment ----
namespace OAI

universe uE

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal RealInnerProductSpace
open Filter
open scoped Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
open scoped RealInnerProductSpace
open Set Filter
open scoped Topology RealInnerProductSpace
open scoped NNReal
open Set Filter
open scoped Topology RealInnerProductSpace NNReal
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology

namespace GaussianPropeller.Reduction

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

theorem centroid_norm_le {d : ℕ} {A : Set (Space d)} (hA : MeasurableSet A) :
    ‖centroid A‖ ≤ 1 / Real.sqrt (2 * Real.pi) := by
  let z := centroid A
  let f : Space d → ℝ := fun x => ⟪z, x⟫
  have hi : Integrable f (gaussian d) := (integrable_id_gaussian d).const_inner z
  have he : ∫ x, (A.indicator f) x ∂gaussian d = ‖z‖^2 := by
    rw [integral_indicator hA]
    change (∫ x in A, ⟪z, x⟫ ∂gaussian d) = _
    rw [integral_inner (integrable_id_restrict d A)]
    exact real_inner_self_eq_norm_sq z
  have hz : ∫ x, f x ∂gaussian d = 0 := by
    change (∫ x, ⟪z, x⟫ ∂gaussian d) = 0
    rw [integral_inner (integrable_id_gaussian d)]
    simp only [gaussian, integral_id_stdGaussian, inner_zero_right]
  have hab : ∫ x, |f x| ∂gaussian d = ‖z‖ * (2 / Real.sqrt (2 * Real.pi)) :=
    Analytic.integral_abs_inner_stdGaussian z
  have hp (x : Space d) : A.indicator f x ≤ (|f x| + f x) / 2 := by
    by_cases hx : x ∈ A
    · rw [Set.indicator_of_mem hx]
      linarith only [le_abs_self (f x)]
    · rw [Set.indicator_of_notMem hx]
      linarith only [neg_abs_le (f x)]
  have h := integral_mono_ae (hi.indicator hA) ((hi.abs.add hi).div_const 2)
    (Filter.Eventually.of_forall hp)
  rw [he, integral_div] at h
  change ‖z‖^2 ≤ (∫ x, |f x| + f x ∂gaussian d) / 2 at h
  rw [integral_add hi.abs hi, hab, hz, add_zero] at h
  have hn := norm_nonneg z
  have hq : 0 ≤ 1 / Real.sqrt (2 * Real.pi) := by positivity
  have hn' : ‖z‖^2 ≤ (1 / Real.sqrt (2 * Real.pi)) * ‖z‖ := by
    convert h using 1; ring
  nlinarith only [hn, hq, hn']

theorem centroid_norm_sq_le {d : ℕ} {A : Set (Space d)} (hA : MeasurableSet A) :
    ‖centroid A‖^2 ≤ 1 / (2 * Real.pi) := by
  have h := (sq_le_sq₀ (norm_nonneg (centroid A)) (by positivity :
      0 ≤ 1 / Real.sqrt (2 * Real.pi))).mpr (centroid_norm_le hA)
  simpa only [div_pow, one_pow, Real.sq_sqrt (by positivity : 0 ≤ 2 * Real.pi)] using h

theorem normalized_centroid_lt_two_thirds {d : ℕ} {A : Set (Space d)}
    (hA : MeasurableSet A) {C : ℝ} (hC : 9 / (8 * Real.pi) < C) :
    ‖centroid A‖ / Real.sqrt C < 2 / 3 := by
  have hp : 0 < Real.pi := Real.pi_pos
  have hCp : 0 < C := (by positivity : (0 : ℝ) < 9 / (8 * Real.pi)).trans hC
  have ht : 0 < Real.sqrt C := Real.sqrt_pos.mpr hCp
  have hn := centroid_norm_sq_le hA
  have hC' : 9 < C * (8 * Real.pi) := (div_lt_iff₀ (by positivity)).mp hC
  have hn' : ‖centroid A‖^2 * (2 * Real.pi) ≤ 1 :=
    (le_div_iff₀ (by positivity)).mp hn
  have hsq : 9 * ‖centroid A‖^2 < 4 * C := by nlinarith only [hC', hn', hp]
  apply (div_lt_iff₀ ht).mpr
  have ht2 := Real.sq_sqrt hCp.le
  have hz := norm_nonneg (centroid A)
  nlinarith only [hsq, ht2, hz, ht]

end GaussianPropeller.Reduction

namespace GaussianPropeller

end GaussianPropeller

end OAI

-- ---- platform node ----
open OAI OAI.GaussianPropeller OAI.GaussianPropeller.Reduction
open MeasureTheory ProbabilityTheory
open scoped ENNReal
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal RealInnerProductSpace
open Filter
open scoped Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
open scoped RealInnerProductSpace
open Set Filter
open scoped Topology RealInnerProductSpace
open scoped NNReal
open Set Filter
open scoped Topology RealInnerProductSpace NNReal
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace


theorem solution : type_of% @_root_.OAI.GaussianPropeller.Reduction.normalized_centroid_lt_two_thirds := @_root_.OAI.GaussianPropeller.Reduction.normalized_centroid_lt_two_thirds
