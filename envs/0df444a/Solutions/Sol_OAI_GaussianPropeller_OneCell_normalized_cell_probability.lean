-- Prove2me | solution 1 for OAI.GaussianPropeller.OneCell.normalized_cell_probability
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T08:25:25.002039+00:00
-- url     : https://prove2.me/submissions/16cf5916-c384-44b5-a39a-2f9e7ee972a2

-- Generated from openai/math@1581d4c lean/OAI/Probability/GaussianPropeller/OneCell.lean:L431-L447
-- (upload_full_project.md Phase 4): solution for node OAI.GaussianPropeller.OneCell.normalized_cell_probability. The node keeps its source
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

lemma nonneg_of_deriv_nonneg (f f' : ℝ → ℝ) (hf : Continuous f)
    (hd : ∀ x, HasDerivAt f (f' x) x) (hpos : ∀ x, 0 ≤ x → 0 ≤ f' x)
    (h0 : 0 ≤ f 0) {x : ℝ} (hx : 0 ≤ x) : 0 ≤ f x := by
  have hm : MonotoneOn f (Ici 0) := monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0)
    hf.continuousOn (fun x _ => (hd x).hasDerivWithinAt)
    (fun x hx => hpos x (interior_subset hx))
  exact h0.trans (hm (by simp) hx hx)

lemma exp_neg_le_quadratic {x : ℝ} (hx : 0 ≤ x) :
    Real.exp (-x) ≤ 1-x+x^2/2 := by
  have h := nonneg_of_deriv_nonneg
    (fun x => (1-x+x^2/2)-Real.exp (-x)) (fun x => -1+x+Real.exp (-x))
    (by fun_prop) (fun x => by convert
      (((hasDerivAt_const x 1).sub (hasDerivAt_id x)).add
        ((hasDerivAt_pow 2 x).div_const 2)).sub ((hasDerivAt_id x).neg.exp) using 1 <;> first | rfl | (solve | ring) | (dsimp; ring))
    (fun x _ => by have hh := Real.add_one_le_exp (-x); linarith)
    (by simp) hx
  linarith

lemma exp_neg_ge_cubic {x : ℝ} (hx : 0 ≤ x) :
    1-x+x^2/2-x^3/6 ≤ Real.exp (-x) := by
  have h := nonneg_of_deriv_nonneg
    (fun x => Real.exp (-x)-(1-x+x^2/2-x^3/6))
    (fun x => -Real.exp (-x)+1-x+x^2/2)
    (by fun_prop) (fun x => by convert
      (((hasDerivAt_id x).neg.exp).sub
        ((((hasDerivAt_const x 1).sub (hasDerivAt_id x)).add
          ((hasDerivAt_pow 2 x).div_const 2)).sub ((hasDerivAt_pow 3 x).div_const 6))) using 1 <;> first | rfl | (solve | ring) | (dsimp; ring))
    (fun x hx => by have hh := exp_neg_le_quadratic hx; linarith)
    (by simp) hx
  linarith

lemma exp_neg_le_quartic {x : ℝ} (hx : 0 ≤ x) :
    Real.exp (-x) ≤ 1-x+x^2/2-x^3/6+x^4/24 := by
  have h := nonneg_of_deriv_nonneg
    (fun x => (1-x+x^2/2-x^3/6+x^4/24)-Real.exp (-x))
    (fun x => -1+x-x^2/2+x^3/6+Real.exp (-x))
    (by fun_prop) (fun x => by convert
      (((((hasDerivAt_const x 1).sub (hasDerivAt_id x)).add
        ((hasDerivAt_pow 2 x).div_const 2)).sub ((hasDerivAt_pow 3 x).div_const 6)).add
          ((hasDerivAt_pow 4 x).div_const 24)).sub ((hasDerivAt_id x).neg.exp) using 1 <;> first | rfl | (solve | ring) | (dsimp; ring))
    (fun x hx => by have hh := exp_neg_ge_cubic hx; linarith)
    (by simp) hx
  linarith

lemma exp_neg_sq_upper (x : ℝ) :
    Real.exp (-x^2/2) ≤ 1-x^2/2+x^4/8-x^6/48+x^8/384 := by
  convert exp_neg_le_quartic (show (0:ℝ) ≤ x^2/2 by positivity) using 1 <;> ring_nf

lemma hasDerivAt_P (x : ℝ) : HasDerivAt P (P' x) x := by
  unfold P P' Q
  convert (((((((hasDerivAt_id x).add ((hasDerivAt_pow 3 x).div_const 2)).sub
    ((hasDerivAt_pow 5 x).div_const 24)).add ((hasDerivAt_pow 7 x).div_const 240)).sub
      ((hasDerivAt_pow 9 x).div_const 2688)).add ((hasDerivAt_pow 11 x).div_const 3456)).const_mul
      (398943/1000000:ℝ)).sub ((hasDerivAt_pow 2 x).div_const 2) using 1 <;> first | rfl | (solve | ring)

lemma hasDerivAt_P' (x : ℝ) : HasDerivAt P' (P'' x) x := by
  unfold P' P''
  convert (((((((hasDerivAt_const x 1).add (((hasDerivAt_pow 2 x).const_mul 3).div_const 2)).sub
    (((hasDerivAt_pow 4 x).const_mul 5).div_const 24)).add (((hasDerivAt_pow 6 x).const_mul 7).div_const 240)).sub
      (((hasDerivAt_pow 8 x).const_mul 9).div_const 2688)).add (((hasDerivAt_pow 10 x).const_mul 11).div_const 3456)).const_mul
      (398943/1000000:ℝ)).sub (hasDerivAt_id x) using 1 <;> first | rfl | (solve | ring)

lemma P''_nonpos {x : ℝ} (hx : x ∈ Icc (0:ℝ) 1) : P'' x ≤ 0 := by
  have hx2 : x^2 ≤ 1 := pow_le_one₀ hx.1 hx.2
  have hx5 : x^5 ≤ 1 := pow_le_one₀ hx.1 hx.2
  have hx7 : 0 ≤ x^7 := pow_nonneg hx.1 _
  have hx9 : x^9 ≤ 1 := pow_le_one₀ hx.1 hx.2
  have hf : 0 ≤ (1-x)*(13-5*x-5*x^2) := mul_nonneg (by linarith [hx.2]) (by linarith only [hx.2,hx2])
  have ha : 3*x-5*x^3/6 ≤ 13/6 := by nlinarith only [hf]
  unfold P''
  linarith only [ha,hx5,hx7,hx9]

lemma concaveOn_P : ConcaveOn ℝ (Icc (0:ℝ) 1) P :=
  concaveOn_of_hasDerivWithinAt2_nonpos (convex_Icc 0 1)
    (by unfold P Q; fun_prop) (fun x _ => (hasDerivAt_P x).hasDerivWithinAt)
    (fun x _ => (hasDerivAt_P' x).hasDerivWithinAt)
    (fun x hx => P''_nonpos (interior_subset hx))

lemma P_global_upper {x : ℝ} (hx : x ∈ Icc (0:ℝ) 1) : P x ≤ 81/800 := by
  have hq : (153/250:ℝ) ∈ Icc (0:ℝ) 1 := by norm_num
  have hpq : P (153/250) ≤ 10123/100000 := by norm_num [P,Q]
  have hdq : P' (153/250) ∈ Icc (0:ℝ) (11/1000000) := by norm_num [P']
  rcases lt_trichotomy x (153/250) with hlt | heq | hgt
  · have hh := concaveOn_P.le_slope_of_hasDerivAt hx hq hlt (hasDerivAt_P (153/250))
    rw [slope_def_field] at hh
    have hh' := (le_div_iff₀ (sub_pos.mpr hlt)).mp hh
    have hg : 0 ≤ P' (153/250)*(153/250-x) := mul_nonneg hdq.1 (sub_nonneg.mpr hlt.le)
    linarith only [hpq,hh',hg]
  · rw [heq]
    linarith only [hpq]
  · have hh := concaveOn_P.slope_le_of_hasDerivAt hq hx hgt (hasDerivAt_P (153/250))
    rw [slope_def_field] at hh
    have hh' := (div_le_iff₀ (sub_pos.mpr hgt)).mp hh
    have hg : P' (153/250)*(x-153/250) ≤ 11/1000000 := by
      calc
        _ ≤ (11/1000000)*(x-153/250) := mul_le_mul_of_nonneg_right hdq.2 (sub_nonneg.mpr hgt.le)
        _ ≤ _ := by linarith only [hx.2]
    linarith only [hpq,hh',hg]

lemma density_integrable : Integrable density := by
  change Integrable (fun x : ℝ => Real.exp (-x^2/2))
  simpa only [ show ∀ x : ℝ, -x^2/2 = -(1/2:ℝ)*x^2 by intro x; ring]
    using integrable_exp_neg_mul_sq (by norm_num : (0:ℝ) < 1/2)

lemma mul_density_integrable : Integrable (fun x : ℝ => x*density x) := by
  simpa only [density, show ∀ x : ℝ, -x^2/2 = -(1/2:ℝ)*x^2 by intro x; ring]
    using integrable_mul_exp_neg_mul_sq (by norm_num : (0:ℝ) < 1/2)

lemma sq_density_integrable : Integrable (fun x : ℝ => x^2*density x) := by
  have h := integrable_rpow_mul_exp_neg_mul_sq (by norm_num : (0:ℝ) < 1/2)
    (by norm_num : (-1:ℝ) < 2)
  simpa only [density, Real.rpow_two, show ∀ x : ℝ, -x^2/2 = -(1/2:ℝ)*x^2 by intro x; ring]
    using h

lemma hasDerivAt_density (x : ℝ) : HasDerivAt density (-x*density x) x := by
  unfold density
  convert (((hasDerivAt_pow 2 x).neg.div_const 2).exp) using 1 <;>
  first | rfl | (solve | ring) | (dsimp; ring)

lemma tendsto_density : Tendsto density atTop (𝓝 0) := by
  apply Real.tendsto_exp_atBot.comp
  convert (tendsto_pow_atTop two_ne_zero).const_mul_atTop_of_neg (by norm_num : (-(1/2:ℝ)) < 0) using 1
  ext x
  ring

lemma tail_first_moment (a : ℝ) : ∫ x in Ioi a, x*density x = density a := by
  have hd (x : ℝ) : HasDerivAt (fun x => -density x) (x*density x) x := by
    convert (hasDerivAt_density x).neg using 1 <;> first | rfl | ring
  have ht : Tendsto (fun x => -density x) atTop (𝓝 (-0)) := tendsto_density.neg
  simpa only [neg_zero, zero_sub, neg_neg] using
    integral_Ioi_of_hasDerivAt_of_tendsto' (fun x _ => hd x)
      mul_density_integrable.integrableOn ht

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

lemma tendsto_mul_density : Tendsto (fun x : ℝ => x*density x) atTop (𝓝 0) := by
  have ht := (tendsto_rpow_abs_mul_exp_neg_mul_sq_cocompact
    (by norm_num : (0:ℝ) < 1/2) 1).mono_left atTop_le_cocompact
  apply ht.congr'
  filter_upwards [eventually_ge_atTop (0:ℝ)] with x hx
  simp only [Real.rpow_one, abs_of_nonneg hx, density]
  rw [show -(1/2:ℝ)*x^2 = -x^2/2 by ring]

lemma tail_second_moment (a : ℝ) : ∫ x in Ioi a, x^2*density x = a*density a+tail a := by
  have hd (x : ℝ) : HasDerivAt (fun x => -(x*density x))
      (x^2*density x-density x) x := by
    convert ((hasDerivAt_id x).mul (hasDerivAt_density x)).neg using 1 <;> first | rfl | (dsimp; ring)
  have ht : Tendsto (fun x : ℝ => -(x*density x)) atTop (𝓝 (-0)) := tendsto_mul_density.neg
  have hh := integral_Ioi_of_hasDerivAt_of_tendsto' (a := a) (fun x _ => hd x)
    (sq_density_integrable.sub density_integrable).integrableOn ht
  rw [integral_sub sq_density_integrable.integrableOn density_integrable.integrableOn] at hh
  change (∫ x in Ioi a, x^2*density x)-tail a = -0- -(a*density a) at hh
  linarith

lemma integral_density_upper {a : ℝ} (ha : 0 ≤ a) :
    ∫ x in (0:ℝ)..a, density x ≤ densityPrimitive a := by
  have hd (x : ℝ) : HasDerivAt densityPrimitive (densityUpper x) x := by
    unfold densityPrimitive densityUpper
    convert (((((hasDerivAt_id x).sub ((hasDerivAt_pow 3 x).div_const 6)).add
      ((hasDerivAt_pow 5 x).div_const 40)).sub ((hasDerivAt_pow 7 x).div_const 336)).add
      ((hasDerivAt_pow 9 x).div_const 3456)) using 1 <;> first | rfl | ring
  have hh : ∫ x in (0:ℝ)..a, densityUpper x = densityPrimitive a := by
    simpa only [densityPrimitive, zero_pow (by decide : 3≠0), zero_pow (by decide : 5≠0),
      zero_pow (by decide : 7≠0), zero_pow (by decide : 9≠0), zero_div, sub_zero, add_zero]
      using intervalIntegral.integral_eq_sub_of_hasDerivAt (a := (0:ℝ)) (b := a) (fun x _ => hd x)
        (by unfold densityUpper; apply Continuous.intervalIntegrable; fun_prop)
  rw [← hh]
  exact intervalIntegral.integral_mono_on ha density_integrable.intervalIntegrable
    (by unfold densityUpper; apply Continuous.intervalIntegrable; fun_prop)
    (fun x _ => exp_neg_sq_upper x)

lemma integral_density_lower : (479/560:ℝ) ≤ ∫ x in (0:ℝ)..1, density x := by
  have hd (x : ℝ) : HasDerivAt densityLowerPrimitive (densityLower x) x := by
    unfold densityLowerPrimitive densityLower
    convert ((((hasDerivAt_id x).sub ((hasDerivAt_pow 3 x).div_const 6)).add
      ((hasDerivAt_pow 5 x).div_const 40)).sub ((hasDerivAt_pow 7 x).div_const 336)) using 1 <;>
        first | rfl | ring
  have hh : ∫ x in (0:ℝ)..1, densityLower x = 479/560 := by
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := (0:ℝ)) (b := 1)
      (fun x _ => hd x) (by unfold densityLower; apply Continuous.intervalIntegrable; fun_prop)
    norm_num [densityLowerPrimitive] at h ⊢
    linarith
  rw [← hh]
  apply intervalIntegral.integral_mono_on (by norm_num)
    (by unfold densityLower; apply Continuous.intervalIntegrable; fun_prop)
    density_integrable.intervalIntegrable
  intro x _
  have h := exp_neg_ge_cubic (show (0:ℝ) ≤ x^2/2 by positivity)
  convert h using 1 <;> first | rfl | (unfold densityLower; ring) | (unfold density; congr 1; ring)

lemma tail_second_bound : gaussianConst*(∫ x in Ioi (1:ℝ), x^2*density x)/4 ≤ 81/800 := by
  rw [tail_second_moment, one_mul, tail_sub (by norm_num : (0:ℝ) ≤ 1)]
  have hc := gaussianConst_bounds
  have h2 := tail_zero
  have hlow := integral_density_lower
  have he : density 1 ≤ 233/384 := by
    have h := exp_neg_sq_upper 1
    norm_num at h
    simpa only [density, one_pow, neg_div] using h
  have hneg : density 1-(∫ x in (0:ℝ)..1, density x) ≤ -(31/125:ℝ) := by
    linarith
  have hh := mul_le_mul_of_nonneg_left hneg (le_trans (by norm_num : (0:ℝ) ≤ 39/100) hc.1)
  have hh' := mul_le_mul_of_nonpos_right hc.1 (by norm_num : -(31/125:ℝ) ≤ 0)
  nlinarith only [hh,hh',h2]

lemma normalized_excess_small {a : ℝ} (ha : a ∈ Icc (0:ℝ) 1) :
    a*gaussianConst*(density a-a*tail a) ≤ 81/800 := by
  have hp : 0 ≤ gaussianConst := gaussianConst_bounds.1.trans' (by norm_num)
  have hi : 0 ≤ ∫ x in (0:ℝ)..a, density x :=
    intervalIntegral.integral_nonneg ha.1 (fun x _ => (Real.exp_pos _).le)
  have hd : 0 ≤ density a := (Real.exp_pos _).le
  have hu : a*density a+a^2*(∫ x in (0:ℝ)..a, density x) ≤ Q a := by
    have h1 := mul_le_mul_of_nonneg_left (exp_neg_sq_upper a) ha.1
    have h2 := mul_le_mul_of_nonneg_left (integral_density_upper ha.1) (sq_nonneg a)
    unfold Q densityPrimitive at *
    change a*Real.exp (-a^2/2)+a^2*(∫ x in (0:ℝ)..a, density x) ≤ _
    nlinarith only [h1,h2]
  have hq : 0 ≤ Q a := (add_nonneg (mul_nonneg ha.1 hd) (mul_nonneg (sq_nonneg a) hi)).trans hu
  have h1 := mul_le_mul_of_nonneg_left hu hp
  have h2 := mul_le_mul_of_nonneg_right gaussianConst_bounds.2 hq
  have h3 := P_global_upper ha
  have h0 := tail_zero
  rw [tail_sub ha.1]
  unfold P at h3
  nlinarith only [h1,h2,h3,h0]

lemma normalized_excess_large {a : ℝ} (ha : 1 ≤ a) :
    a*gaussianConst*(density a-a*tail a) ≤ 81/800 := by
  have he : ∫ x in Ioi a, a*(x-a)*density x = a*(density a-a*tail a) := by
    have hf : (fun x : ℝ => a*(x-a)*density x) =
        (fun x => a*(x*density x-a*density x)) := by ext x; ring
    rw [hf, integral_const_mul, integral_sub mul_density_integrable.integrableOn
      (density_integrable.const_mul a).integrableOn, integral_const_mul, tail_first_moment]
    rfl
  have hu : ∫ x in Ioi a, a*(x-a)*density x ≤ (∫ x in Ioi a, x^2*density x)/4 := by
    rw [← integral_div]
    apply setIntegral_mono_on
      (by convert (mul_density_integrable.sub (density_integrable.const_mul a)).const_mul a |>.integrableOn using 1; ext x; dsimp; ring)
      (sq_density_integrable.div_const 4).integrableOn measurableSet_Ioi
    intro x _
    have h : a*(x-a) ≤ x^2/4 := by nlinarith only [sq_nonneg (x-2*a)]
    have hd : 0 ≤ density x := (Real.exp_pos _).le
    exact (mul_le_mul_of_nonneg_right h hd).trans_eq (by ring)
  have hm : (∫ x in Ioi a, x^2*density x) ≤ ∫ x in Ioi (1:ℝ), x^2*density x := by
    exact setIntegral_mono_set sq_density_integrable.integrableOn
      (ae_of_all _ (fun x => mul_nonneg (sq_nonneg x) (Real.exp_pos _).le))
      (ae_of_all _ (fun _ hx => Ioi_subset_Ioi ha hx))
  rw [he] at hu
  have hc : 0 ≤ gaussianConst := gaussianConst_bounds.1.trans' (by norm_num)
  have hu' := mul_le_mul_of_nonneg_left hu hc
  have hm' := mul_le_mul_of_nonneg_left hm hc
  have hb := tail_second_bound
  nlinarith only [hu',hm',hb]

lemma normalized_excess_bound {a : ℝ} (ha : 0 ≤ a) :
    a*gaussianConst*(density a-a*tail a) ≤ 81/800 := by
  rcases le_total a 1 with h | h
  · exact normalized_excess_small ⟨ha,h⟩
  · exact normalized_excess_large h

lemma integral_gaussianReal_std (f : ℝ → ℝ) :
    ∫ x, f x ∂gaussianReal 0 1 = gaussianConst * ∫ x, f x*density x := by
  rw [integral_gaussianReal_eq_integral_smul (by norm_num : (1:NNReal) ≠ 0), ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [gaussianPDFReal, NNReal.coe_one, sub_zero, mul_one, smul_eq_mul, gaussianConst, density]
  ring

lemma integral_excess_gaussian (a : ℝ) : ∫ x : ℝ, max (x-a) 0 ∂gaussianReal 0 1 =
    gaussianConst*(density a-a*tail a) := by
  rw [integral_gaussianReal_std]
  congr 1
  have hh : ∫ x : ℝ, max (x-a) 0*density x = ∫ x in Ioi a, (x-a)*density x := by
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Ioi a)]
    · exact setIntegral_congr_fun measurableSet_Ioi (fun x hx => by rw [max_eq_left (sub_nonneg.mpr hx.le)])
    · intro x hx
      simp only [mem_Ioi, not_lt] at hx
      rw [max_eq_right (sub_nonpos.mpr hx), zero_mul]
  rw [hh]
  simp_rw [sub_mul]
  rw [integral_sub mul_density_integrable.integrableOn (density_integrable.const_mul a).integrableOn,
    integral_const_mul, tail_first_moment]
  rfl

lemma gaussian_excess_bound {a : ℝ} (ha : 0 ≤ a) :
    a*(∫ x : ℝ, max (x-a) 0 ∂gaussianReal 0 1) ≤ 81/800 := by
  rw [integral_excess_gaussian]
  simpa only [mul_assoc] using normalized_excess_bound ha

section GeneralCell
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma map_unit_inner_gaussian (e : E) (he : ‖e‖=1) :
    (stdGaussian E).map (fun x => ⟪e,x⟫) = gaussianReal 0 1 := by
  change (stdGaussian E).map (InnerProductSpace.toDual ℝ E e) = _
  rw [IsGaussian.map_eq_gaussianReal, integral_strongDual_stdGaussian,
    variance_dual_stdGaussian, LinearIsometryEquiv.norm_map, he]
  norm_num

lemma projection_rearrangement {A : Set E} (hA : MeasurableSet A)
    (e : E) (he : ‖e‖=1) (a : ℝ) :
    ∫ x in A, ⟪e,x⟫ ∂stdGaussian E ≤ a*(stdGaussian E).real A+
      ∫ x : ℝ, max (x-a) 0 ∂gaussianReal 0 1 := by
  let f : E → ℝ := fun x => ⟪e,x⟫
  have hi : Integrable f (stdGaussian E) := IsGaussian.integrable_id.const_inner e
  have hconst : Integrable (fun _ : E => a) (stdGaussian E) := integrable_const a
  have hpos : Integrable (fun x : E => max (f x-a) 0) (stdGaussian E) :=
    (hi.sub hconst).pos_part
  have hm : ∫ x, max (f x-a) 0 ∂stdGaussian E =
      ∫ x : ℝ, max (x-a) 0 ∂gaussianReal 0 1 := by
    rw [← integral_map (by fun_prop : AEMeasurable f (stdGaussian E))
      (by fun_prop : AEStronglyMeasurable (fun x : ℝ => max (x-a) 0) ((stdGaussian E).map f)),
      map_unit_inner_gaussian e he]
  have hp (x : E) : A.indicator f x ≤ A.indicator (fun _ => a) x+max (f x-a) 0 := by
    by_cases hx : x∈A
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]
      linarith only [le_max_left (f x-a) 0]
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx, zero_add]
      exact le_max_right _ _
  have hh := integral_mono_ae (hi.indicator hA) ((hconst.indicator hA).add hpos)
    (ae_of_all _ hp)
  simp only [Pi.add_apply] at hh
  rw [integral_indicator hA, integral_add (hconst.indicator hA) hpos,
    integral_indicator hA, setIntegral_const, smul_eq_mul, hm, mul_comm] at hh
  exact hh

lemma cell_norm_sq_le {A : Set E} (hA : MeasurableSet A) :
    ‖∫ x in A, x ∂stdGaussian E‖^2 ≤ (81/200:ℝ)*(stdGaussian E).real A := by
  let z : E := ∫ x in A, x ∂stdGaussian E
  change ‖z‖^2 ≤ _
  by_cases hz : z=0
  · rw [hz, norm_zero, zero_pow (by decide : 2≠0)]
    positivity
  have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hP : 0 < (stdGaussian E).real A := by
    apply lt_of_le_of_ne measureReal_nonneg
    intro h
    have hzero : stdGaussian E A = 0 := (measureReal_eq_zero_iff (by finiteness)).mp h.symm
    apply hz
    exact setIntegral_measure_zero _ hzero
  let e : E := ‖z‖⁻¹ • z
  have he : ‖e‖=1 := by
    rw [norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hn, inv_mul_cancel₀ hn.ne']
  have hm : ∫ x in A, ⟪e,x⟫ ∂stdGaussian E = ‖z‖ := by
    have hi : Integrable (fun x : E => x) (stdGaussian E) := IsGaussian.integrable_id
    rw [integral_inner hi.restrict]
    change ⟪‖z‖⁻¹ • z,z⟫ = ‖z‖
    rw [real_inner_smul_left, real_inner_self_eq_norm_sq]
    field_simp
  let a : ℝ := ‖z‖/(2*(stdGaussian E).real A)
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hr := projection_rearrangement hA e he a
  rw [hm] at hr
  have hr' := mul_le_mul_of_nonneg_left hr ha
  have hb := gaussian_excess_bound ha
  have hh : a*‖z‖ ≤ a^2*(stdGaussian E).real A+81/800 := by
    nlinarith only [hr',hb]
  dsimp [a] at hh
  have hden : (stdGaussian E).real A ≠ 0 := hP.ne'
  field_simp at hh
  nlinarith only [hh,hP]

lemma normalized_cell_probability {A : Set E} (hA : MeasurableSet A)
    {C : ℝ} (hC : 9/(8*Real.pi) < C) :
    (884/1000:ℝ)*(‖∫ x in A, x ∂stdGaussian E‖/Real.sqrt C)^2 ≤
      (stdGaussian E).real A := by
  have hp : 0 < Real.pi := Real.pi_pos
  have hCp : 0 < C := (by positivity : (0:ℝ) < 9/(8*Real.pi)).trans hC
  have hnum : (81/200:ℝ)*(884/1000) < 9/(8*Real.pi) := by
    apply (lt_div_iff₀ (by positivity)).mpr
    nlinarith only [Real.pi_lt_d4]
  have hCc : (81/200:ℝ)*(884/1000) < C := hnum.trans hC
  have hz := cell_norm_sq_le hA
  rw [div_pow, Real.sq_sqrt hCp.le, ← mul_div_assoc]
  apply (div_le_iff₀ hCp).mpr
  have hm := mul_le_mul_of_nonneg_left hz (by norm_num : (0:ℝ) ≤ 884/1000)
  have hP : 0 ≤ (stdGaussian E).real A := measureReal_nonneg
  have hc := mul_le_mul_of_nonneg_right hCc.le hP
  nlinarith only [hm,hc]

end GeneralCell
end GaussianPropeller.OneCell

end OAI

-- ---- platform node ----
open OAI OAI.GaussianPropeller OAI.GaussianPropeller.OneCell
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


theorem solution.{uE} : type_of% @_root_.OAI.GaussianPropeller.OneCell.normalized_cell_probability.{uE} := @_root_.OAI.GaussianPropeller.OneCell.normalized_cell_probability.{uE}
