-- Prove2me | solution 1 for OAI.GaussianPropeller.FourCertificates.large_5
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T12:30:57.599143+00:00
-- url     : https://prove2.me/submissions/88294d00-6697-40cc-9596-088c37659a06

-- Generated from openai/math@1581d4c lean/OAI/Probability/GaussianPropeller/LargeCertificates.lean:L137-L155
-- (upload_full_project.md Phase 4): solution for node OAI.GaussianPropeller.FourCertificates.large_5. The node keeps its source
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
import Definitions.Def_OAI_Probability_GaussianPropeller_Coordinates
import Definitions.Def_OAI_Probability_GaussianPropeller_CapBounds
import Definitions.Def_OAI_Probability_GaussianPropeller_CapNumeric
import Definitions.Def_OAI_Probability_GaussianPropeller_Geometry
import Definitions.Def_OAI_Probability_GaussianPropeller_QuarticCertificates
import Theorems.Thm_OAI_GaussianPropeller_FourCertificates_loss_row
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

lemma p_pos (x : ℝ) : 0 < p x :=
  mul_pos (lt_of_lt_of_le (by norm_num) gaussianConst_tight.1) (tail_pos x)

lemma p_taylor_lower {x : ℝ} (hx : 0 ≤ x) (n : ℕ) (hJ : 0 ≤ J (2*n) x) :
    1/2-(398943/1000000:ℝ)*J (2*n) x ≤ p x := by
  have hh := (integral_exp_bounds n hx).2
  change (∫ t in (0:ℝ)..x, density t) ≤ J (2*n) x at hh
  have hmul := mul_le_mul_of_nonneg_left hh
    (lt_of_lt_of_le (by norm_num) gaussianConst_tight.1).le
  have hmul' := mul_le_mul_of_nonneg_right gaussianConst_tight.2 hJ
  unfold p
  rw [tail_sub hx, mul_sub, tail_zero]
  linarith only [hmul,hmul']

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

end GaussianPropeller.ProbabilityBounds

end OAI

-- ---- from OAI.Probability.GaussianPropeller.QuarticCertificates ----
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
open MeasureTheory ProbabilityTheory Set
open scoped RealInnerProductSpace ENNReal

namespace GaussianPropeller.FourCertificates
open OneCell ProbabilityBounds Mills Taylor

lemma loss_bound {x pu gu : ℝ} (hx:0≤x) (hp:p x≤pu) (hg:G x≤gu) : loss x≤pu^2*gu := by
  have hp0 := p_pos x
  have hg0 := G_nonneg hx
  have hsq : (p x)^2≤pu^2 := sq_le_sq₀ hp0.le (hp0.le.trans hp) |>.mpr hp
  exact (mul_le_mul_of_nonneg_right hsq hg0).trans (mul_le_mul_of_nonneg_left hg (sq_nonneg pu))

lemma large_mono : MonotoneOn large (Ici 0) := by
  intro a ha b hb hab
  have h2:=pow_le_pow_left₀ ha hab 2
  unfold large; linarith only [h2]

end GaussianPropeller.FourCertificates

end OAI

-- ---- from OAI.Probability.GaussianPropeller.LargeCertificates ----
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
open MeasureTheory ProbabilityTheory Set
open scoped RealInnerProductSpace ENNReal
namespace GaussianPropeller.FourCertificates
open OneCell ProbabilityBounds Mills Taylor

lemma large_5 {r x:ℝ} (hr:r∈Icc (33/80:ℝ) (83/200:ℝ)) (hx:0≤x)
    (hl:(9/(8*Real.pi))*r^2/(1+Real.sqrt (1-(4/3:ℝ)*r^2))≤loss x) : large r < p x := by
  by_contra hn
  have hP : p x ≤ large (83/200:ℝ) := (le_of_not_gt hn).trans (large_mono (by change 0≤r; linarith only [hr.1]) (by norm_num) hr.2)
  have hj : 0≤J 12 (83467/100000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hj' : 0≤J 13 (83467/100000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hpL : large (83/200:ℝ) ≤ p (83467/100000:ℝ) := by
    apply le_trans ?_ (p_taylor_lower (by norm_num) 6 hj)
    norm_num [large,J,Finset.sum_range_succ,Nat.factorial]
  have hpU : p (83467/100000:ℝ)≤(100977/500000:ℝ) := by
    apply le_trans (p_taylor_upper (by norm_num) 6 hj')
    norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hla : lambda (83467/100000:ℝ)≤(21788/15625:ℝ) := by
    apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj
    norm_num [E,J,Finset.sum_range_succ,Nat.factorial]
  have hg : G (83467/100000:ℝ)≤(780551/1000000:ℝ) := G_upper_of_lambda (by norm_num) hla (by norm_num)
  exact loss_row (lo:=(33/80:ℝ)) (q:=(83467/100000:ℝ)) (v:=(219819/250000:ℝ))
    (u:=(100977/500000:ℝ)^2*(780551/1000000:ℝ)) (by norm_num) hr.1 hx (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (loss_bound (by norm_num) hpU hg) (hP.trans hpL) hl

end GaussianPropeller.FourCertificates

end OAI

-- ---- platform node ----
open OAI OAI.GaussianPropeller OAI.GaussianPropeller.FourCertificates
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
open MeasureTheory ProbabilityTheory Set
open scoped RealInnerProductSpace ENNReal
open OneCell ProbabilityBounds Mills Taylor


theorem solution : type_of% @_root_.OAI.GaussianPropeller.FourCertificates.large_5 := @_root_.OAI.GaussianPropeller.FourCertificates.large_5
