-- Prove2me | solution 1 for OAI.GaussianPropeller.Cap.hasDerivAt_capP
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T11:04:58.529221+00:00
-- url     : https://prove2.me/submissions/48ab60aa-df3e-4ac7-af00-756123d1d260

-- Generated from openai/math@1581d4c lean/OAI/Probability/GaussianPropeller/CapIntegral.lean:L74-L98
-- (upload_full_project.md Phase 4): solution for node OAI.GaussianPropeller.Cap.hasDerivAt_capP. The node keeps its source
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
import Definitions.Def_OAI_Probability_GaussianPropeller_PairIntegral
import Definitions.Def_OAI_Probability_GaussianPropeller_ResidualBounds
import Definitions.Def_OAI_Probability_GaussianPropeller_Polar
import Definitions.Def_OAI_Probability_GaussianPropeller_CapIntegral

-- ---- from OAI.Probability.GaussianPropeller.OneCell ----
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

namespace GaussianPropeller.OneCell

lemma density_integrable : Integrable density := by
  change Integrable (fun x : ℝ => Real.exp (-x^2/2))
  simpa only [ show ∀ x : ℝ, -x^2/2 = -(1/2:ℝ)*x^2 by intro x; ring]
    using integrable_exp_neg_mul_sq (by norm_num : (0:ℝ) < 1/2)

lemma hasDerivAt_density (x : ℝ) : HasDerivAt density (-x*density x) x := by
  unfold density
  convert (((hasDerivAt_pow 2 x).neg.div_const 2).exp) using 1 <;>
  first | rfl | (solve | ring) | (dsimp; ring)

lemma gaussianConst_bounds : (39/100:ℝ) ≤ gaussianConst ∧ gaussianConst ≤ 398943/1000000 := by
  have hp := Real.pi_pos
  have hs := Real.sq_sqrt (show 0 ≤ 2*Real.pi by positivity)
  have hspos : 0 < Real.sqrt (2*Real.pi) := by positivity
  constructor
  · rw [gaussianConst, inv_eq_one_div, le_div_iff₀ hspos]
    have hh := Real.pi_lt_d2
    nlinarith
  · rw [gaussianConst, inv_eq_one_div, div_le_iff₀ hspos]
    have hh := Real.pi_gt_d6
    nlinarith

lemma integral_gaussianReal_std (f : ℝ → ℝ) :
    ∫ x, f x ∂gaussianReal 0 1 = gaussianConst * ∫ x, f x*density x := by
  rw [integral_gaussianReal_eq_integral_smul (by norm_num : (1:NNReal) ≠ 0), ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [gaussianPDFReal, NNReal.coe_one, sub_zero, mul_one, smul_eq_mul, gaussianConst, density]
  ring

section GeneralCell
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

end GeneralCell
end GaussianPropeller.OneCell

end OAI

-- ---- from OAI.Probability.GaussianPropeller.Mills ----
namespace OAI

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

namespace GaussianPropeller.Mills
open OneCell

lemma tail_pos (x : ℝ) : 0 < tail x := by
  apply (setIntegral_pos_iff_support_of_nonneg_ae
    (ae_of_all _ (fun x => (Real.exp_pos _).le)) density_integrable.integrableOn).mpr
  simp [Function.support, Real.exp_ne_zero]

lemma hasDerivAt_tail (x : ℝ) : HasDerivAt tail (-density x) x := by
  have heq : tail = fun a => tail 0 - ∫ t in (0:ℝ)..a, density t := by
    funext a
    have hi := intervalIntegral.integral_Ioi_sub_Ioi'
      (a := 0) (b := a) density_integrable.integrableOn density_integrable.integrableOn
    change tail 0-tail a = _ at hi
    linarith only [hi]
  rw [heq]
  exact (intervalIntegral.integral_hasDerivAt_right
    (density_integrable.intervalIntegrable)
    (by exact (show StronglyMeasurable density by unfold density; fun_prop).stronglyMeasurableAtFilter) (hasDerivAt_density x).continuousAt).const_sub _

end GaussianPropeller.Mills

end OAI

-- ---- from OAI.Probability.GaussianPropeller.ProbabilityBounds ----
namespace OAI

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

namespace GaussianPropeller.ProbabilityBounds
open OneCell Mills Taylor
lemma gaussianConst_tight : (398942/1000000:ℝ) ≤ gaussianConst ∧ gaussianConst ≤ 398943/1000000 := by
  refine ⟨?_, gaussianConst_bounds.2⟩
  have hs := Real.sq_sqrt (show 0 ≤ 2*Real.pi by positivity)
  have hspos : 0 < Real.sqrt (2*Real.pi) := by positivity
  rw [gaussianConst, inv_eq_one_div, le_div_iff₀ hspos]
  have hh := Real.pi_lt_d6
  nlinarith

lemma p_pos (x : ℝ) : 0 < p x :=
  mul_pos (lt_of_lt_of_le (by norm_num) gaussianConst_tight.1) (tail_pos x)

lemma hasDerivAt_p (x : ℝ) : HasDerivAt p (-gaussianConst*density x) x := by
  convert (hasDerivAt_tail x).const_mul gaussianConst using 1 <;> first | rfl | ring

end GaussianPropeller.ProbabilityBounds

end OAI

-- ---- from OAI.Probability.GaussianPropeller.CapIntegral ----
namespace OAI

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
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology ENNReal
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology ENNReal
open Metric

namespace GaussianPropeller.Cap
open OneCell ProbabilityBounds Polar
open scoped Topology

lemma p_eq_integral_indicator (a : ℝ) :
    p a = ∫ x : ℝ, (Ioi a).indicator (fun _ => (1:ℝ)) x ∂gaussianReal 0 1 := by
  rw [integral_gaussianReal_std]
  have he : (fun x : ℝ => (Ioi a).indicator (fun _ => (1:ℝ)) x*density x) =
      (Ioi a).indicator density := by
    funext x
    by_cases hx : x∈Ioi a <;> simp [hx]
  rw [he,integral_indicator measurableSet_Ioi]
  rfl

lemma p_le_one (a : ℝ) : p a ≤ 1 := by
  rw [p_eq_integral_indicator, integral_indicator measurableSet_Ioi, setIntegral_const,
    smul_eq_mul, mul_one]
  exact measureReal_le_one

lemma density_le_one (a : ℝ) : density a ≤ 1 := by
  unfold density
  rw [Real.exp_le_one_iff]
  linarith [sq_nonneg a]

variable {n : ℕ}
lemma integrable_p_norm (a : ℝ) : Integrable (fun y : CE n => p (a*‖y‖)) (stdGaussian (CE n)) := by
  apply Integrable.mono' (integrable_const (1:ℝ))
    (((continuous_iff_continuousAt.mpr (fun x => (hasDerivAt_p x).continuousAt)).comp (by fun_prop)).aestronglyMeasurable)
  filter_upwards [] with y
  dsimp only [Function.comp_def]
  rw [Real.norm_eq_abs,abs_of_pos (p_pos _)]
  exact p_le_one _

lemma hasDerivAt_capP (a : ℝ) : HasDerivAt (capP n)
    (-gaussianConst * ∫ y : CE n, ‖y‖*density (a*‖y‖) ∂stdGaussian (CE n)) a := by
  have hc : 0 < gaussianConst := by dsimp [gaussianConst]; positivity
  have hd := hasDerivAt_integral_of_dominated_loc_of_deriv_le (s:=univ)
    (bound:= fun y : CE n => gaussianConst*‖y‖)
    (F:= fun s y => p (s*‖y‖))
    (F':=fun s y => -gaussianConst*(‖y‖*density (s*‖y‖)))
    (by simp : univ ∈ 𝓝 a)
    (Filter.Eventually.of_forall (fun s => (integrable_p_norm s).aestronglyMeasurable))
    (integrable_p_norm a)
    (by unfold density; fun_prop : AEStronglyMeasurable (fun y : CE n => -gaussianConst*(‖y‖*density (a*‖y‖))) (stdGaussian (CE n)))
    (by
      filter_upwards [] with y
      intro s _
      simp only [norm_mul,norm_neg,Real.norm_eq_abs,abs_of_pos hc,abs_of_nonneg (norm_nonneg y),abs_of_pos (show 0 < density (s*‖y‖) from Real.exp_pos _)]
      exact mul_le_mul_of_nonneg_left (by nlinarith only [density_le_one (s*‖y‖),norm_nonneg y] :
        ‖y‖*density (s*‖y‖) ≤ ‖y‖) hc.le)
    (IsGaussian.integrable_id.norm.const_mul gaussianConst)
    (by
      filter_upwards [] with y
      intro s _
      convert (hasDerivAt_p (s*‖y‖)).comp s ((hasDerivAt_id s).mul_const ‖y‖) using 1 <;> first | rfl | ring)
  have hd2 := hd.2
  rw [integral_const_mul] at hd2
  exact hd2

end GaussianPropeller.Cap

end OAI

-- ---- platform node ----
open OAI OAI.GaussianPropeller OAI.GaussianPropeller.Cap
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
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology ENNReal
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology ENNReal
open Metric
open OneCell ProbabilityBounds Polar
open scoped Topology


theorem solution : type_of% @_root_.OAI.GaussianPropeller.Cap.hasDerivAt_capP := @_root_.OAI.GaussianPropeller.Cap.hasDerivAt_capP
