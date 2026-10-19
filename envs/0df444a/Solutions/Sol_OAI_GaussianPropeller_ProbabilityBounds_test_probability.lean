-- Prove2me | solution 1 for OAI.GaussianPropeller.ProbabilityBounds.test_probability
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T08:37:52.536995+00:00
-- url     : https://prove2.me/submissions/47732d0a-ac09-41f5-8b59-5c6aeacb2ac4

-- Generated from openai/math@1581d4c lean/OAI/Probability/GaussianPropeller/ProbabilityBounds.lean:L293-L404
-- (upload_full_project.md Phase 4): solution for node OAI.GaussianPropeller.ProbabilityBounds.test_probability. The node keeps its source
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
import Theorems.Thm_OAI_GaussianPropeller_Mills_G_le_one
import Theorems.Thm_OAI_GaussianPropeller_Mills_G_monotone
import Theorems.Thm_OAI_GaussianPropeller_ProbabilityBounds_lambda_taylor_upper
import Theorems.Thm_OAI_GaussianPropeller_Taylor_integral_exp_bounds

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

lemma tendsto_density : Tendsto density atTop (𝓝 0) := by
  apply Real.tendsto_exp_atBot.comp
  convert (tendsto_pow_atTop two_ne_zero).const_mul_atTop_of_neg (by norm_num : (-(1/2:ℝ)) < 0) using 1
  ext x
  ring

lemma tail_zero : gaussianConst*tail 0 = 1/2 := by
  have h : tail 0 = Real.sqrt (2*Real.pi)/2 := by
    simpa only [tail, density, show ∀ x : ℝ, -x^2/2 = -(1/2:ℝ)*x^2 by intro x; ring,
      show Real.pi/(1/2:ℝ) = 2*Real.pi by ring] using integral_gaussian_Ioi (1/2)
  rw [h, gaussianConst]
  field_simp

lemma tail_sub {a : ℝ} (ha : 0 ≤ a) : tail a = tail 0 - ∫ x in (0:ℝ)..a, density x := by
  have h := intervalIntegral.integral_Ioi_sub_Ioi density_integrable.integrableOn ha
  change tail 0-tail a = _ at h
  linarith

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

lemma hasDerivAt_barrier (x : ℝ) : HasDerivAt barrier (barrier' x) x := by
  unfold barrier barrier'
  convert (((hasDerivAt_id x).const_mul 3).add
    (((hasDerivAt_pow 2 x).add_const 8).sqrt (by positivity))).div_const 4 using 1 <;>
    first | rfl | (dsimp; ring)

lemma barrier_pos {x : ℝ} (hx : 0 ≤ x) : 0 < barrier x := by
  unfold barrier
  have : 0 < Real.sqrt (x^2+8) := Real.sqrt_pos.mpr (by positivity)
  positivity

lemma barrier_ge_half {x : ℝ} (hx : 0 ≤ x) : 1/2 ≤ barrier x := by
  have hs := Real.sq_sqrt (show 0 ≤ x^2+8 by positivity)
  have hn := Real.sqrt_nonneg (x^2+8)
  unfold barrier
  nlinarith only [hs,hn,hx,sq_nonneg x]

lemma barrier_differential {x : ℝ} (hx : 0 ≤ x) :
    barrier x ^ 2 - x*barrier x - barrier' x ≤ 0 := by
  let s := Real.sqrt (x^2+8)
  have hs : s^2=x^2+8 := Real.sq_sqrt (by positivity)
  have hp : 0 < s := Real.sqrt_pos.mpr (by positivity)
  have hid : (x^2+2)^2*s^2-(x^3+6*x)^2=32 := by rw [hs]; ring
  have hh : x^3+6*x ≤ (x^2+2)*s := by
    have hnon : 0 ≤ x^3+6*x := by positivity
    have hnon' : 0 ≤ (x^2+2)*s := by positivity
    apply (sq_le_sq₀ hnon hnon').mp
    nlinarith only [hid]
  have heq : barrier x^2-x*barrier x-barrier' x =
      (x^3+6*x-(x^2+2)*s)/(8*s) := by
    dsimp [barrier,barrier']
    change ((3*x+s)/4)^2-x*((3*x+s)/4)-(3+x/s)/4 = _
    field_simp [hp.ne']
    have hsm := congrArg (fun t : ℝ => x*t) hs
    have hss := congrArg (fun t : ℝ => s*t) hs
    nlinarith only [hs,hsm,hss]
  rw [heq]
  exact div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hh) (by positivity)

lemma tail_le_barrier {x : ℝ} (hx : 0 ≤ x) : tail x ≤ density x / barrier x := by
  let f : ℝ → ℝ := fun y => density y/barrier y-tail y
  let f' : ℝ → ℝ := fun y => density y*(barrier y^2-y*barrier y-barrier' y)/barrier y^2
  have hd (y : ℝ) (hy : 0 ≤ y) : HasDerivAt f (f' y) y := by
    convert ((hasDerivAt_density y).div (hasDerivAt_barrier y) (barrier_pos hy).ne').sub
      (hasDerivAt_tail y) using 1 <;>
    first | rfl | (dsimp [f']; field_simp [(barrier_pos hy).ne']; ring)
  have hm : AntitoneOn f (Ici 0) := antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici 0)
    (fun y hy => (hd y hy).continuousAt.continuousWithinAt)
    (fun y hy => (hd y (interior_subset hy)).hasDerivWithinAt)
    (fun y hy => div_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le
        (barrier_differential (interior_subset hy))) (sq_nonneg _))
  have ht : Tendsto (fun y => density y/barrier y) atTop (𝓝 0) := by
    apply squeeze_zero' _ _ (by simpa using tendsto_density.const_mul 2)
    · filter_upwards [eventually_ge_atTop (0:ℝ)] with y hy
      exact div_nonneg (Real.exp_pos _).le (barrier_pos hy).le
    · filter_upwards [eventually_ge_atTop (0:ℝ)] with y hy
      apply (div_le_iff₀ (barrier_pos hy)).mpr
      have hh := mul_le_mul_of_nonneg_left (barrier_ge_half hy) (Real.exp_pos (-y^2/2)).le
      change density y * (1/2) ≤ density y*barrier y at hh
      nlinarith only [hh]
  have ht' : Tendsto f atTop (𝓝 0) := by
    simpa only [sub_zero, f, tail, id_eq] using ht.sub (tendsto_integral_Ioi_zero (f := density) tendsto_id)
  have hnon : 0 ≤ f x := le_of_tendsto ht' (by
    filter_upwards [eventually_ge_atTop x] with y hy
    exact hm hx (hx.trans hy) hy)
  dsimp [f] at hnon
  linarith only [hnon]

lemma lambda_ge_barrier {x : ℝ} (hx : 0 ≤ x) : barrier x ≤ lambda x := by
  rw [lambda, le_div_iff₀ (tail_pos x)]
  have hh := (le_div_iff₀ (barrier_pos hx)).mp (tail_le_barrier hx)
  linarith only [hh]

lemma lambda_pos (x : ℝ) : 0 < lambda x := div_pos (Real.exp_pos _) (tail_pos x)

lemma G_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ G x := by
  apply mul_nonneg (lambda_pos x).le
  have hb := lambda_ge_barrier hx
  have hs := Real.sq_sqrt (show (0:ℝ) ≤ x^2+8 by positivity)
  have hp := Real.sqrt_nonneg (x^2+8)
  have hh : x ≤ Real.sqrt (x^2+8) := by nlinarith only [hs,hp,hx]
  dsimp [barrier] at hb
  linarith only [hb,hh]

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

lemma p_antitone : Antitone p := by
  apply antitone_of_hasDerivAt_nonpos (fun x => hasDerivAt_p x)
  intro x
  exact mul_nonpos_of_nonpos_of_nonneg (by linarith [gaussianConst_tight.1]) (Real.exp_pos _).le

lemma p_taylor_upper {x : ℝ} (hx : 0 ≤ x) (n : ℕ) (hJ : 0 ≤ J (2*n+1) x) :
    p x ≤ 1/2-(398942/1000000:ℝ)*J (2*n+1) x := by
  have hh := (integral_exp_bounds n hx).1
  change J (2*n+1) x ≤ ∫ t in (0:ℝ)..x, density t at hh
  have hmul := mul_le_mul_of_nonneg_left hh
    (lt_of_lt_of_le (by norm_num) gaussianConst_tight.1).le
  have hmul' := mul_le_mul_of_nonneg_right gaussianConst_tight.1 hJ
  unfold p
  rw [tail_sub hx, mul_sub, tail_zero]
  linarith only [hmul,hmul']

lemma G_upper_of_lambda {x L U : ℝ} (hx : 0 ≤ x) (h : lambda x ≤ L)
    (hLU : L*(L-x) ≤ U) : G x ≤ U := by
  have hl : 0 ≤ lambda x-x := (mul_nonneg_iff_of_pos_left (lambda_pos x)).mp (G_nonneg hx)
  have hh := mul_nonneg (sub_nonneg.mpr h)
    (show 0 ≤ L+lambda x-x by linarith [lambda_pos x])
  unfold G
  nlinarith only [hh,hLU]

lemma certificate_005 : p (2.1) < (0.415+0.15*0.05)*0.05 ∧ G (2.1) ≤ 0.91 := by
  have hj12 : 0 ≤ J 12 (2.1) := by norm_num [J, Finset.sum_range_succ, Nat.factorial]
  have hj13 : 0 ≤ J 13 (2.1) := by norm_num [J, Finset.sum_range_succ, Nat.factorial]
  constructor
  · have ht := p_taylor_upper (by norm_num : (0:ℝ) ≤ 2.1) 6 hj13
    have hc : 1/2-(398942/1000000:ℝ)*J 13 (2.1) < (0.415+0.15*0.05)*0.05 := by
      norm_num [J, Finset.sum_range_succ, Nat.factorial]
    exact lt_of_le_of_lt ht hc
  · apply G_upper_of_lambda (by norm_num : (0:ℝ) ≤ 2.1) (L := 2.463)
    · apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj12
      norm_num [E,J, Finset.sum_range_succ, Nat.factorial]
    · norm_num

lemma certificate_014 : p (1.6) < (0.415+0.15*0.14)*0.14 ∧ G (1.6) ≤ 0.87 := by
  have hj12 : 0 ≤ J 12 (1.6) := by norm_num [J, Finset.sum_range_succ, Nat.factorial]
  have hj13 : 0 ≤ J 13 (1.6) := by norm_num [J, Finset.sum_range_succ, Nat.factorial]
  constructor
  · have ht := p_taylor_upper (by norm_num : (0:ℝ) ≤ 1.6) 6 hj13
    have hc : 1/2-(398942/1000000:ℝ)*J 13 (1.6) < (0.415+0.15*0.14)*0.14 := by
      norm_num [J, Finset.sum_range_succ, Nat.factorial]
    exact lt_of_le_of_lt ht hc
  · apply G_upper_of_lambda (by norm_num : (0:ℝ) ≤ 1.6) (L := 2.025)
    · apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj12
      norm_num [E,J, Finset.sum_range_succ, Nat.factorial]
    · norm_num

lemma certificate_024 : p (1.3) < (0.415+0.15*0.24)*0.24 ∧ G (1.3) ≤ 0.836 := by
  have hj12 : 0 ≤ J 12 (1.3) := by norm_num [J, Finset.sum_range_succ, Nat.factorial]
  have hj13 : 0 ≤ J 13 (1.3) := by norm_num [J, Finset.sum_range_succ, Nat.factorial]
  constructor
  · have ht := p_taylor_upper (by norm_num : (0:ℝ) ≤ 1.3) 6 hj13
    have hc : 1/2-(398942/1000000:ℝ)*J 13 (1.3) < (0.415+0.15*0.24)*0.24 := by
      norm_num [J, Finset.sum_range_succ, Nat.factorial]
    exact lt_of_le_of_lt ht hc
  · apply G_upper_of_lambda (by norm_num : (0:ℝ) ≤ 1.3) (L := 1.771)
    · apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj12
      norm_num [E,J, Finset.sum_range_succ, Nat.factorial]
    · norm_num

lemma certificate_033 : p (1.04) < (0.415+0.15*0.33)*0.33 ∧ G (1.04) ≤ 0.809 := by
  have hj12 : 0 ≤ J 12 (1.04) := by norm_num [J, Finset.sum_range_succ, Nat.factorial]
  have hj13 : 0 ≤ J 13 (1.04) := by norm_num [J, Finset.sum_range_succ, Nat.factorial]
  constructor
  · have ht := p_taylor_upper (by norm_num : (0:ℝ) ≤ 1.04) 6 hj13
    have hc : 1/2-(398942/1000000:ℝ)*J 13 (1.04) < (0.415+0.15*0.33)*0.33 := by
      norm_num [J, Finset.sum_range_succ, Nat.factorial]
    exact lt_of_le_of_lt ht hc
  · apply G_upper_of_lambda (by norm_num : (0:ℝ) ≤ 1.04) (L := 1.558)
    · apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj12
      norm_num [E,J, Finset.sum_range_succ, Nat.factorial]
    · norm_num

lemma certificate_041 : p (0.87) < (0.415+0.15*0.41)*0.41 ∧ G (0.87) ≤ 0.788 := by
  have hj12 : 0 ≤ J 12 (0.87) := by norm_num [J, Finset.sum_range_succ, Nat.factorial]
  have hj13 : 0 ≤ J 13 (0.87) := by norm_num [J, Finset.sum_range_succ, Nat.factorial]
  constructor
  · have ht := p_taylor_upper (by norm_num : (0:ℝ) ≤ 0.87) 6 hj13
    have hc : 1/2-(398942/1000000:ℝ)*J 13 (0.87) < (0.415+0.15*0.41)*0.41 := by
      norm_num [J, Finset.sum_range_succ, Nat.factorial]
    exact lt_of_le_of_lt ht hc
  · apply G_upper_of_lambda (by norm_num : (0:ℝ) ≤ 0.87) (L := 1.423)
    · apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj12
      norm_num [E,J, Finset.sum_range_succ, Nat.factorial]
    · norm_num

lemma certificate_048 : p (0.74) < (0.415+0.15*0.48)*0.48 ∧ G (0.74) ≤ 0.771 := by
  have hj12 : 0 ≤ J 12 (0.74) := by norm_num [J, Finset.sum_range_succ, Nat.factorial]
  have hj13 : 0 ≤ J 13 (0.74) := by norm_num [J, Finset.sum_range_succ, Nat.factorial]
  constructor
  · have ht := p_taylor_upper (by norm_num : (0:ℝ) ≤ 0.74) 6 hj13
    have hc : 1/2-(398942/1000000:ℝ)*J 13 (0.74) < (0.415+0.15*0.48)*0.48 := by
      norm_num [J, Finset.sum_range_succ, Nat.factorial]
    exact lt_of_le_of_lt ht hc
  · apply G_upper_of_lambda (by norm_num : (0:ℝ) ≤ 0.74) (L := 1.322)
    · apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj12
      norm_num [E,J, Finset.sum_range_succ, Nat.factorial]
    · norm_num

lemma certificate_054 : p (0.63) < (0.415+0.15*0.54)*0.54 ∧ G (0.63) ≤ 0.756 := by
  have hj12 : 0 ≤ J 12 (0.63) := by norm_num [J, Finset.sum_range_succ, Nat.factorial]
  have hj13 : 0 ≤ J 13 (0.63) := by norm_num [J, Finset.sum_range_succ, Nat.factorial]
  constructor
  · have ht := p_taylor_upper (by norm_num : (0:ℝ) ≤ 0.63) 6 hj13
    have hc : 1/2-(398942/1000000:ℝ)*J 13 (0.63) < (0.415+0.15*0.54)*0.54 := by
      norm_num [J, Finset.sum_range_succ, Nat.factorial]
    exact lt_of_le_of_lt ht hc
  · apply G_upper_of_lambda (by norm_num : (0:ℝ) ≤ 0.63) (L := 1.238)
    · apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj12
      norm_num [E,J, Finset.sum_range_succ, Nat.factorial]
    · norm_num

lemma certificate_059 : p (0.55) < (0.415+0.15*0.59)*0.59 ∧ G (0.55) ≤ 0.743 := by
  have hj12 : 0 ≤ J 12 (0.55) := by norm_num [J, Finset.sum_range_succ, Nat.factorial]
  have hj13 : 0 ≤ J 13 (0.55) := by norm_num [J, Finset.sum_range_succ, Nat.factorial]
  constructor
  · have ht := p_taylor_upper (by norm_num : (0:ℝ) ≤ 0.55) 6 hj13
    have hc : 1/2-(398942/1000000:ℝ)*J 13 (0.55) < (0.415+0.15*0.59)*0.59 := by
      norm_num [J, Finset.sum_range_succ, Nat.factorial]
    exact lt_of_le_of_lt ht hc
  · apply G_upper_of_lambda (by norm_num : (0:ℝ) ≤ 0.55) (L := 1.178)
    · apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj12
      norm_num [E,J, Finset.sum_range_succ, Nat.factorial]
    · norm_num

lemma certificate_064 : p (0.47) < (0.415+0.15*0.64)*0.64 ∧ G (0.47) ≤ 0.73 := by
  have hj12 : 0 ≤ J 12 (0.47) := by norm_num [J, Finset.sum_range_succ, Nat.factorial]
  have hj13 : 0 ≤ J 13 (0.47) := by norm_num [J, Finset.sum_range_succ, Nat.factorial]
  constructor
  · have ht := p_taylor_upper (by norm_num : (0:ℝ) ≤ 0.47) 6 hj13
    have hc : 1/2-(398942/1000000:ℝ)*J 13 (0.47) < (0.415+0.15*0.64)*0.64 := by
      norm_num [J, Finset.sum_range_succ, Nat.factorial]
    exact lt_of_le_of_lt ht hc
  · apply G_upper_of_lambda (by norm_num : (0:ℝ) ≤ 0.47) (L := 1.120)
    · apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj12
      norm_num [E,J, Finset.sum_range_succ, Nat.factorial]
    · norm_num

lemma G_test_bound {a r x w U : ℝ} (ha : 0 ≤ a) (har : a ≤ r)
    (hx : 0 ≤ x) (hw : 0 ≤ w) (hp : p x=(0.415+0.15*r)*r)
    (hc : p w < (0.415+0.15*a)*a ∧ G w ≤ U) : G x ≤ U := by
  have hpw : p w < p x := by
    rw [hp]
    have hm := mul_nonneg (sub_nonneg.mpr har) (show 0 ≤ r+a by linarith)
    nlinarith only [hc.1,har,hm]
  have hxw : x ≤ w := by
    by_contra! hgt
    exact (not_lt_of_ge (p_antitone hgt.le)) hpw
  exact (G_monotone hx hw hxw).trans hc.2

lemma row_margin {a b r x U S : ℝ} (ha : 0 ≤ a) (har : a ≤ r) (hrb : r ≤ b)
    (hb : b ≤ 2/3) (hU : 0 ≤ U) (hG : G x ≤ U) (hS : 0 ≤ S)
    (hSsq : 1-a^2 ≤ S^2)
    (hc : U*(0.415+0.15*b)^2 < (9/(8*3.1416:ℝ))/(1+S)) :
    (0.415+0.15*r)^2*G x < (9/(8*Real.pi))/(1+Real.sqrt (1-r^2)) := by
  have hr : 0 ≤ r := ha.trans har
  have hr2 : r^2 ≤ (1:ℝ) := by nlinarith only [hr,hrb,hb]
  have hs := Real.sq_sqrt (show 0 ≤ 1-r^2 by linarith only [hr2])
  have hsp := Real.sqrt_nonneg (1-r^2)
  have hsq : Real.sqrt (1-r^2) ≤ S := by
    have hm := mul_nonneg (sub_nonneg.mpr har) (show 0 ≤ r+a by positivity)
    nlinarith only [hs,hsp,hSsq,hS,hm]
  have hbcoef : (0.415+0.15*r)^2 ≤ (0.415+0.15*b)^2 := by
    nlinarith only [hr,hrb, sq_nonneg (b-r)]
  have hh₁ := mul_le_mul_of_nonneg_left hG (sq_nonneg (0.415+0.15*r))
  have hh₂ := mul_le_mul_of_nonneg_right hbcoef hU
  have hB : (9/(8*3.1416:ℝ)) ≤ 9/(8*Real.pi) :=
    div_le_div_of_nonneg_left (by norm_num) (by positivity) (by linarith [Real.pi_lt_d4])
  have hd₁ := div_le_div_of_nonneg_left (by norm_num : (0:ℝ) ≤ 9/(8*3.1416))
    (show 0 < 1+Real.sqrt (1-r^2) by positivity) (show 1+Real.sqrt (1-r^2) ≤ 1+S by linarith only [hsq])
  have hd₂ := div_le_div_of_nonneg_right hB (show 0 ≤ 1+Real.sqrt (1-r^2) by positivity)
  have hc' : (0.415+0.15*b)^2*U < (9/(8*3.1416:ℝ))/(1+S) := by simpa only [mul_comm] using hc
  exact lt_of_le_of_lt (hh₁.trans hh₂) (lt_of_lt_of_le hc' (hd₁.trans hd₂))

lemma test_probability {r x : ℝ} (hr : 0 < r) (hrcap : r ≤ 2/3) (hx : 0 ≤ x)
    (hp : p x=(0.415+0.15*r)*r) :
    (0.415+0.15*r)^2*G x < (9/(8*Real.pi))/(1+Real.sqrt (1-r^2)) := by
  by_cases h0 : r ≤ 0.05
  · apply row_margin (a := 0) (b := 0.05) (U := 1) (S := 1)
    · norm_num
    · exact hr.le
    · exact h0
    · norm_num
    · norm_num
    · exact G_le_one x
    · norm_num
    · norm_num
    · norm_num
  by_cases h1 : r ≤ 0.14
  · apply row_margin (a := 0.05) (b := 0.14) (U := 0.91) (S := 0.99875)
    · norm_num
    · exact (lt_of_not_ge h0).le
    · exact h1
    · norm_num
    · norm_num
    · exact G_test_bound (by norm_num) (lt_of_not_ge h0).le hx (by norm_num) hp certificate_005
    · norm_num
    · norm_num
    · norm_num
  by_cases h2 : r ≤ 0.24
  · apply row_margin (a := 0.14) (b := 0.24) (U := 0.87) (S := 0.99016)
    · norm_num
    · exact (lt_of_not_ge h1).le
    · exact h2
    · norm_num
    · norm_num
    · exact G_test_bound (by norm_num) (lt_of_not_ge h1).le hx (by norm_num) hp certificate_014
    · norm_num
    · norm_num
    · norm_num
  by_cases h3 : r ≤ 0.33
  · apply row_margin (a := 0.24) (b := 0.33) (U := 0.836) (S := 0.97078)
    · norm_num
    · exact (lt_of_not_ge h2).le
    · exact h3
    · norm_num
    · norm_num
    · exact G_test_bound (by norm_num) (lt_of_not_ge h2).le hx (by norm_num) hp certificate_024
    · norm_num
    · norm_num
    · norm_num
  by_cases h4 : r ≤ 0.41
  · apply row_margin (a := 0.33) (b := 0.41) (U := 0.809) (S := 0.94399)
    · norm_num
    · exact (lt_of_not_ge h3).le
    · exact h4
    · norm_num
    · norm_num
    · exact G_test_bound (by norm_num) (lt_of_not_ge h3).le hx (by norm_num) hp certificate_033
    · norm_num
    · norm_num
    · norm_num
  by_cases h5 : r ≤ 0.48
  · apply row_margin (a := 0.41) (b := 0.48) (U := 0.788) (S := 0.91209)
    · norm_num
    · exact (lt_of_not_ge h4).le
    · exact h5
    · norm_num
    · norm_num
    · exact G_test_bound (by norm_num) (lt_of_not_ge h4).le hx (by norm_num) hp certificate_041
    · norm_num
    · norm_num
    · norm_num
  by_cases h6 : r ≤ 0.54
  · apply row_margin (a := 0.48) (b := 0.54) (U := 0.771) (S := 0.87727)
    · norm_num
    · exact (lt_of_not_ge h5).le
    · exact h6
    · norm_num
    · norm_num
    · exact G_test_bound (by norm_num) (lt_of_not_ge h5).le hx (by norm_num) hp certificate_048
    · norm_num
    · norm_num
    · norm_num
  by_cases h7 : r ≤ 0.59
  · apply row_margin (a := 0.54) (b := 0.59) (U := 0.756) (S := 0.84167)
    · norm_num
    · exact (lt_of_not_ge h6).le
    · exact h7
    · norm_num
    · norm_num
    · exact G_test_bound (by norm_num) (lt_of_not_ge h6).le hx (by norm_num) hp certificate_054
    · norm_num
    · norm_num
    · norm_num
  by_cases h8 : r ≤ 0.64
  · apply row_margin (a := 0.59) (b := 0.64) (U := 0.743) (S := 0.80741)
    · norm_num
    · exact (lt_of_not_ge h7).le
    · exact h8
    · norm_num
    · norm_num
    · exact G_test_bound (by norm_num) (lt_of_not_ge h7).le hx (by norm_num) hp certificate_059
    · norm_num
    · norm_num
    · norm_num
  apply row_margin (a := 0.64) (b := (2/3)) (U := 0.73) (S := 0.76838)
  · norm_num
  · exact (lt_of_not_ge h8).le
  · exact hrcap
  · norm_num
  · norm_num
  · exact G_test_bound (by norm_num) (lt_of_not_ge h8).le hx (by norm_num) hp certificate_064
  · norm_num
  · norm_num
  · norm_num

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


theorem solution : type_of% @_root_.OAI.GaussianPropeller.ProbabilityBounds.test_probability := @_root_.OAI.GaussianPropeller.ProbabilityBounds.test_probability
