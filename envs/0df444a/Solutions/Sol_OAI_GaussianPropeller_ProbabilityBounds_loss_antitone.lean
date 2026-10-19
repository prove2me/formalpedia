-- Prove2me | solution 1 for OAI.GaussianPropeller.ProbabilityBounds.loss_antitone
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T08:36:12.222983+00:00
-- url     : https://prove2.me/submissions/0b0a0639-c4c1-4d2e-975c-d5768d40e1dd

-- Generated from openai/math@1581d4c lean/OAI/Probability/GaussianPropeller/ProbabilityBounds.lean:L241-L255
-- (upload_full_project.md Phase 4): solution for node OAI.GaussianPropeller.ProbabilityBounds.loss_antitone. The node keeps its source
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
lemma loss_eq (x : ℝ) : loss x=gaussianConst^2*density x*(density x-x*tail x) := by
  unfold loss p G lambda
  field_simp [(tail_pos x).ne']

lemma hasDerivAt_loss (x : ℝ) : HasDerivAt loss
    (gaussianConst^2*density x*(x^2*tail x-x*density x-tail x)) x := by
  have he : loss = fun x => gaussianConst^2*density x*(density x-x*tail x) := funext loss_eq
  rw [he]
  convert ((hasDerivAt_density x).const_mul (gaussianConst^2)).mul
    ((hasDerivAt_density x).sub ((hasDerivAt_id x).mul (hasDerivAt_tail x))) using 1 <;>
      first | rfl | (simp only [Pi.sub_apply, Pi.mul_apply, id_eq]; ring)

lemma loss_antitone : AntitoneOn loss (Ici 0) := by
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici 0)
    (fun x _ => (hasDerivAt_loss x).continuousAt.continuousWithinAt)
    (fun x _ => (hasDerivAt_loss x).hasDerivWithinAt)
  intro x hx
  have hx' : 0 ≤ x := interior_subset hx
  have hl : x ≤ lambda x := by
    have hh := (mul_nonneg_iff_of_pos_left (lambda_pos x)).mp (G_nonneg hx')
    linarith only [hh]
  rw [lambda, le_div_iff₀ (tail_pos x)] at hl
  apply mul_nonpos_of_nonneg_of_nonpos (mul_nonneg (sq_nonneg _) (Real.exp_pos _).le)
  have hh := mul_le_mul_of_nonneg_left hl hx'
  have ht : 0 < tail x := tail_pos x
  have hm : 0 ≤ x*density x := mul_nonneg hx' (Real.exp_pos _).le
  nlinarith only [hh,ht,hm]

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


theorem solution : type_of% @_root_.OAI.GaussianPropeller.ProbabilityBounds.loss_antitone := @_root_.OAI.GaussianPropeller.ProbabilityBounds.loss_antitone
