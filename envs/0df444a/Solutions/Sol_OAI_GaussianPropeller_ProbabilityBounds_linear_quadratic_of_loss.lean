-- Prove2me | solution 1 for OAI.GaussianPropeller.ProbabilityBounds.linear_quadratic_of_loss
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T08:40:04.59586+00:00
-- url     : https://prove2.me/submissions/5d1e5dbe-37b8-44f6-a9ba-5b30f43102e7

-- Generated from openai/math@1581d4c lean/OAI/Probability/GaussianPropeller/ProbabilityBounds.lean:L406-L431
-- (upload_full_project.md Phase 4): solution for node OAI.GaussianPropeller.ProbabilityBounds.linear_quadratic_of_loss. The node keeps its source
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
import Theorems.Thm_OAI_GaussianPropeller_ProbabilityBounds_loss_antitone
import Theorems.Thm_OAI_GaussianPropeller_ProbabilityBounds_test_probability

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

lemma tail_zero : gaussianConst*tail 0 = 1/2 := by
  have h : tail 0 = Real.sqrt (2*Real.pi)/2 := by
    simpa only [tail, density, show ∀ x : ℝ, -x^2/2 = -(1/2:ℝ)*x^2 by intro x; ring,
      show Real.pi/(1/2:ℝ) = 2*Real.pi by ring] using integral_gaussian_Ioi (1/2)
  rw [h, gaussianConst]
  field_simp

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

lemma hasDerivAt_p (x : ℝ) : HasDerivAt p (-gaussianConst*density x) x := by
  convert (hasDerivAt_tail x).const_mul gaussianConst using 1 <;> first | rfl | ring

lemma exists_p {P : ℝ} (hP : 0 < P) (hPh : P ≤ 1/2) : ∃ x ≥ (0:ℝ), p x=P := by
  have ht : Tendsto p atTop (𝓝 0) := by
    convert! (tendsto_integral_Ioi_zero (f := density) (μ := volume) tendsto_id).const_mul gaussianConst using 1
    simp only [mul_zero]
  have hh := isPreconnected_Ici.intermediate_value_Ioc (a := (0:ℝ)) self_mem_Ici
    (le_principal_iff.mpr (Ici_mem_atTop (0:ℝ)))
    (show ContinuousOn p (Ici 0) from fun x _ => (hasDerivAt_p x).continuousAt.continuousWithinAt) ht
  have hm : P ∈ Ioc 0 (p 0) := by exact ⟨hP, by simpa [p,tail_zero] using hPh⟩
  exact hh hm

lemma linear_quadratic_of_loss {r x : ℝ} (hr : 0 < r) (hrcap : r ≤ 2/3) (hx : 0 ≤ x)
    (hc : (9/(8*Real.pi))*r^2/(1+Real.sqrt (1-r^2)) ≤ loss x) :
    0.415*r+0.15*r^2 < p x := by
  let P₀ := (0.415+0.15*r)*r
  have hP₀ : 0 < P₀ := by dsimp [P₀]; positivity
  have hP₀h : P₀ ≤ 1/2 := by dsimp [P₀]; nlinarith only [hr,hrcap]
  obtain ⟨y,hy,hPy⟩ := exists_p hP₀ hP₀h
  have ht := test_probability hr hrcap hy hPy
  have ht' := mul_lt_mul_of_pos_right ht (sq_pos_of_pos hr)
  have htest : loss y < (9/(8*Real.pi))*r^2/(1+Real.sqrt (1-r^2)) := by
    unfold loss
    rw [hPy]
    dsimp [P₀] at *
    calc
      _ = (0.415+0.15*r)^2*G y*r^2 := by ring
      _ < (9/(8*Real.pi))/(1+Real.sqrt (1-r^2))*r^2 := ht'
      _ = _ := by ring
  by_contra! hh
  have hpx : p x ≤ p y := by rw [hPy]; dsimp [P₀]; nlinarith only [hh]
  have hyx : y ≤ x := by
    by_contra! hgt
    have hd : StrictAnti p := strictAnti_of_hasDerivAt_neg (fun z => hasDerivAt_p z)
      (fun z => mul_neg_of_neg_of_pos (by linarith [gaussianConst_tight.1]) (Real.exp_pos _))
    exact (not_lt_of_ge hpx) (hd hgt)
  have hh' := loss_antitone hy hx hyx
  exact (not_lt_of_ge (hc.trans hh')) htest

end GaussianPropeller.ProbabilityBounds

end OAI

-- ---- platform node ----
open OAI OAI.GaussianPropeller OAI.GaussianPropeller.ProbabilityBounds
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
open OneCell Mills Taylor


theorem solution : type_of% @_root_.OAI.GaussianPropeller.ProbabilityBounds.linear_quadratic_of_loss := @_root_.OAI.GaussianPropeller.ProbabilityBounds.linear_quadratic_of_loss
