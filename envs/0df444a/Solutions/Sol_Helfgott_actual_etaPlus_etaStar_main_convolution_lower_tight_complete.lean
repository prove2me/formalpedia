-- Prove2me | solution 1 for Helfgott.actual_etaPlus_etaStar_main_convolution_lower_tight_complete
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-06T06:44:42.038211+00:00
-- url     : https://prove2.me/submissions/ffdb6761-5ca5-4456-aef0-e411c78d85d8

import Theorems.Thm_Helfgott_etaPlus_regularity
import Theorems.Thm_Helfgott_etaPlus_approximation_l1_l2
import Theorems.Thm_Helfgott_actual_etaPlus_approximation_l2_tight_complete
import Theorems.Thm_Helfgott_reference_etaCircle_etaStar_main_convolution_lower_tight
import Definitions.Def_Helfgott_Smoothings
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.Analysis.Convolution
import Mathlib.Analysis.Real.Pi.Bounds

section
open MeasureTheory Set
namespace Helfgott
lemma etaPlus_continuous : Continuous etaPlus := etaPlus_regularity.1
lemma etaPlus_integrable : Integrable etaPlus := etaPlus_regularity.2.1
lemma etaPlus_square_integrable : Integrable (fun t : ℝ => (etaPlus t)^2) := etaPlus_regularity.2.2.1
lemma etaPlus_square_integral_upper : (∫ t : ℝ,(etaPlus t)^2)≤(321/500 : ℝ) := etaPlus_regularity.2.2.2.1
lemma etaPlus_convolution_continuous : Continuous (fun ρ : ℝ => ∫ u : ℝ,etaPlus u*etaPlus (ρ-u)) := etaPlus_regularity.2.2.2.2
lemma etaPlus_measurable : Measurable etaPlus := etaPlus_continuous.measurable
end Helfgott

namespace Helfgott
lemma etaCircle_abs_le_one (t : ℝ) : |etaCircle t| ≤ 1 := by
  by_cases ht : t ∈ Icc (0 : ℝ) 2
  · have htn : 0 ≤ t*(2-t) := mul_nonneg ht.1 (by linarith [ht.2])
    have htl : t*(2-t) ≤ 1 := by nlinarith [sq_nonneg (t-1)]
    have hp : (t*(2-t))^3 ≤ 1 := by simpa using pow_le_pow_left₀ htn htl 3
    have he : Real.exp (-((t-1)^2)/2) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg (t-1)])
    rw [etaCircle,Set.indicator_of_mem ht,
      show t^3*(2-t)^3=(t*(2-t))^3 by ring,abs_of_nonneg (by positivity)]
    exact mul_le_one₀ hp (by positivity) he
  · simp [etaCircle,Set.indicator_of_notMem ht]


end Helfgott
end

section
open MeasureTheory Set
namespace Helfgott
lemma etaPlus_approx_integrable : Integrable (fun t : ℝ => etaPlus t-etaCircle t) := etaPlus_approximation_l1_l2.1
lemma etaPlus_approx_square_integrable : Integrable (fun t : ℝ => (etaPlus t-etaCircle t)^2) := etaPlus_approximation_l1_l2.2.1
lemma etaPlus_approx_l1_le : (∫ t : ℝ,|etaPlus t-etaCircle t|)≤1/1800 := etaPlus_approximation_l1_l2.2.2.1
lemma etaPlus_approx_l2_square_le : (∫ t : ℝ,(etaPlus t-etaCircle t)^2)≤1/6250000 := etaPlus_approximation_l1_l2.2.2.2
end Helfgott
end

section
open MeasureTheory
namespace Helfgott
lemma etaPlus_approx_l2_square_le_tight :
    (∫ t : ℝ,(etaPlus t-etaCircle t)^2)≤1/1568000000 :=
  actual_etaPlus_approximation_l2_tight_complete.2
end Helfgott
end

section
open MeasureTheory Set
namespace Helfgott
lemma etaCircle_etaStar_main_convolution_lower_tight :
    (4011/5000 : ℝ)/49≤∫ w in Ioi (0 : ℝ),etaStar w*(∫ u : ℝ,
      etaCircle u*etaCircle (2+9/(196*Real.sqrt (2*Real.pi))-w-u)) :=
  reference_etaCircle_etaStar_main_convolution_lower_tight
end Helfgott
end

section

open MeasureTheory Filter Set
open scoped Topology

namespace Helfgott

private lemma body_hasDerivAt (t : ℝ) :
    HasDerivAt (fun s : ℝ => s^3 * (2-s)^3 * Real.exp (-((s-1)^2)/2))
      (-(t-1) * (1-(t-1)^2)^2 * (7-(t-1)^2) * Real.exp (-((t-1)^2)/2)) t := by
  convert! ((((hasDerivAt_id t).pow 3).mul
    (((hasDerivAt_const t (2 : ℝ)).sub (hasDerivAt_id t)).pow 3)).mul
    (((((hasDerivAt_id t).sub_const 1).pow 2).neg.div_const 2).exp)) using 1 <;>
    simp <;> ring

theorem etaCircle_hasDerivAt (t : ℝ) :
    HasDerivAt etaCircle
      ((Set.Icc (0 : ℝ) 2).indicator (fun t =>
        -(t-1) * (1-(t-1)^2)^2 * (7-(t-1)^2) * Real.exp (-((t-1)^2)/2)) t) t := by
  by_cases ht : t ∈ Set.Icc (0 : ℝ) 2
  · rw [Set.indicator_of_mem ht]
    by_cases hboundary : t = 0 ∨ t = 2
    · have hval : etaCircle t = 0 := by
        rcases hboundary with rfl | rfl <;> norm_num [etaCircle]
      have hd : -(t-1) * (1-(t-1)^2)^2 * (7-(t-1)^2) * Real.exp (-((t-1)^2)/2) = 0 := by
        rcases hboundary with rfl | rfl <;> norm_num
      rw [hd]
      have hinside : HasDerivWithinAt etaCircle 0 (Set.Icc (0 : ℝ) 2) t := by
        have h := (body_hasDerivAt t).hasDerivWithinAt (s := Set.Icc (0 : ℝ) 2)
        rw [hd] at h
        apply h.congr
        · intro x hx; simp only [etaCircle, Set.indicator_of_mem hx]
        · simp only [etaCircle, Set.indicator_of_mem ht]
      have houtside : HasDerivWithinAt etaCircle 0 (Set.Icc (0 : ℝ) 2)ᶜ t := by
        apply (hasDerivAt_const t (0 : ℝ)).hasDerivWithinAt.congr
        · intro x hx; simp only [etaCircle, Set.indicator_of_notMem hx]
        · exact hval
      simpa only [Set.union_compl_self, hasDerivWithinAt_univ] using hinside.union houtside
    · have h0 : 0 < t := lt_of_le_of_ne ht.1 (by tauto)
      have h2 : t < 2 := lt_of_le_of_ne ht.2 (by tauto)
      apply (body_hasDerivAt t).congr_of_eventuallyEq
      filter_upwards [Icc_mem_nhds h0 h2] with x hx
      simp only [etaCircle, Set.indicator_of_mem hx]
  · rw [Set.indicator_of_notMem ht]
    apply (hasDerivAt_const t (0 : ℝ)).congr_of_eventuallyEq
    filter_upwards [isClosed_Icc.isOpen_compl.mem_nhds ht] with x hx
    simp only [etaCircle, Set.indicator_of_notMem hx]

lemma etaCircle_continuous : Continuous etaCircle :=
  continuous_iff_continuousAt.mpr (fun t => (etaCircle_hasDerivAt t).continuousAt)

lemma etaCircle_nonneg (t : ℝ) : 0 ≤ etaCircle t := by
  by_cases ht : t ∈ Set.Icc (0 : ℝ) 2
  · simp only [etaCircle, Set.indicator_of_mem ht]
    have h2 : 0 ≤ 2-t := sub_nonneg.mpr ht.2
    have h0 : 0 ≤ t := ht.1
    positivity
  · simp only [etaCircle, Set.indicator_of_notMem ht, le_refl]

lemma etaCircle_symmetric (t : ℝ) : etaCircle (2-t) = etaCircle t := by
  by_cases ht : t ∈ Set.Icc (0 : ℝ) 2
  · have ht' : 2-t ∈ Set.Icc (0 : ℝ) 2 := by constructor <;> linarith [ht.1,ht.2]
    simp only [etaCircle, Set.indicator_of_mem ht, Set.indicator_of_mem ht']
    have he : -((2-t-1)^2)/2 = -((t-1)^2)/2 := by ring
    rw [he]
    ring
  · have ht' : 2-t ∉ Set.Icc (0 : ℝ) 2 := by
      intro h; apply ht; constructor <;> linarith [h.1,h.2]
    simp only [etaCircle, Set.indicator_of_notMem ht, Set.indicator_of_notMem ht']

lemma etaCircle_hasCompactSupport : HasCompactSupport etaCircle := by
  apply HasCompactSupport.intro (K := Set.Icc (0 : ℝ) 2) isCompact_Icc
  intro t ht
  simp only [etaCircle,Set.indicator_of_notMem ht]

lemma etaCircle_integrable : Integrable etaCircle :=
  etaCircle_continuous.integrable_of_hasCompactSupport etaCircle_hasCompactSupport

lemma etaCircle_square_integrable : Integrable (fun t => etaCircle t ^ 2) := by
  apply (etaCircle_continuous.pow 2).integrable_of_hasCompactSupport
  apply HasCompactSupport.intro (K := Set.Icc (0 : ℝ) 2) isCompact_Icc
  intro t ht
  change etaCircle t ^ 2 = 0
  simp only [etaCircle,Set.indicator_of_notMem ht,zero_pow (by norm_num : (2 : ℕ) ≠ 0)]

lemma etaCircle_deriv_continuous : Continuous (fun t =>
    ((Set.Icc (0 : ℝ) 2).indicator (fun t =>
      -(t-1) * (1-(t-1)^2)^2 * (7-(t-1)^2) * Real.exp (-((t-1)^2)/2)) t)) := by
  apply continuous_indicator
  · intro t ht
    have hb := frontier_subset_closure ht
    rw [isClosed_Icc.closure_eq] at hb
    have hn : t ∉ interior (Set.Icc (0 : ℝ) 2) := ht.2
    rw [interior_Icc] at hn
    have he : t=0 ∨ t=2 := by
      by_contra hh
      apply hn
      have hne0 : t ≠ 0 := by tauto
      have hne2 : t ≠ 2 := by tauto
      exact ⟨lt_of_le_of_ne hb.1 (Ne.symm hne0),lt_of_le_of_ne hb.2 hne2⟩
    rcases he with rfl | rfl <;> norm_num
  · apply Continuous.continuousOn
    fun_prop

lemma etaCircle_deriv_square_integrable : Integrable (fun t =>
    (((Set.Icc (0 : ℝ) 2).indicator (fun t =>
      -(t-1) * (1-(t-1)^2)^2 * (7-(t-1)^2) * Real.exp (-((t-1)^2)/2)) t))^2) := by
  apply (etaCircle_deriv_continuous.pow 2).integrable_of_hasCompactSupport
  apply HasCompactSupport.intro (K := Set.Icc (0 : ℝ) 2) isCompact_Icc
  intro t ht
  change (((Set.Icc (0 : ℝ) 2).indicator (fun t =>
    -(t-1) * (1-(t-1)^2)^2 * (7-(t-1)^2) * Real.exp (-((t-1)^2)/2)) t))^2 = 0
  simp only [Set.indicator_of_notMem ht,zero_pow (by norm_num : (2 : ℕ) ≠ 0)]

end Helfgott


end

section

open MeasureTheory Set Filter
open scoped Interval

namespace Helfgott

lemma exp_neg_upper_quadratic (u : ℝ) (hu : 0 ≤ u) :
    Real.exp (-u) ≤ 1-u+u^2/2 := by
  let g : ℝ → ℝ := fun t => 1-t+t^2/2-Real.exp (-t)
  have hd (t : ℝ) : HasDerivAt g (-1+t+Real.exp (-t)) t := by
    dsimp [g]
    convert! (((hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_id t)).add
      (((hasDerivAt_id t).pow 2).div_const 2)).sub
      (((hasDerivAt_id t).neg).exp) using 1 <;> simp <;> ring
  have hm : Monotone g := monotone_of_hasDerivAt_nonneg hd (by
    intro t
    have ht := Real.add_one_le_exp (-t)
    change 0 ≤ -1+t+Real.exp (-t)
    linarith)
  have h := hm hu
  dsimp [g] at h
  norm_num at h
  linarith

lemma symmetric_smoothing_l2_upper :
    (∫ t in (-1 : ℝ)..1, ((1-t^2)^3*Real.exp (-(t^2)/2))^2) ≤ 641/1000 := by
  let P : ℝ → ℝ := fun t => (1-t^2)^6*(1-t^2+t^4/2)
  have hp (t : ℝ) : ((1-t^2)^3*Real.exp (-(t^2)/2))^2 ≤ P t := by
    have he := exp_neg_upper_quadratic (t^2) (sq_nonneg t)
    have hexp : Real.exp (-(t^2)/2)^2=Real.exp (-(t^2)) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    rw [mul_pow,← pow_mul,hexp]
    dsimp [P]
    convert! mul_le_mul_of_nonneg_left he (by positivity : (0 : ℝ) ≤ (1-t^2)^6) using 1 <;>
      (first | rfl | ring | (ext x; ring))
  let Q : ℝ → ℝ := fun t => (1/1 : ℝ)*t^1/1 + (-7/1 : ℝ)*t^3/3 + (43/2 : ℝ)*t^5/5 + (-38/1 : ℝ)*t^7/7 + (85/2 : ℝ)*t^9/9 + (-31/1 : ℝ)*t^11/11 + (29/2 : ℝ)*t^13/13 + (-4/1 : ℝ)*t^15/15 + (1/2 : ℝ)*t^17/17
  have hd (t : ℝ) : HasDerivAt Q (P t) t := by
    dsimp [Q,P]
    convert! ((((((((((hasDerivAt_const t (0 : ℝ)).add ((((hasDerivAt_id t).pow 1).const_mul (1/1 : ℝ)).div_const 1)).add ((((hasDerivAt_id t).pow 3).const_mul (-7/1 : ℝ)).div_const 3)).add ((((hasDerivAt_id t).pow 5).const_mul (43/2 : ℝ)).div_const 5)).add ((((hasDerivAt_id t).pow 7).const_mul (-38/1 : ℝ)).div_const 7)).add ((((hasDerivAt_id t).pow 9).const_mul (85/2 : ℝ)).div_const 9)).add ((((hasDerivAt_id t).pow 11).const_mul (-31/1 : ℝ)).div_const 11)).add ((((hasDerivAt_id t).pow 13).const_mul (29/2 : ℝ)).div_const 13)).add ((((hasDerivAt_id t).pow 15).const_mul (-4/1 : ℝ)).div_const 15)).add ((((hasDerivAt_id t).pow 17).const_mul (1/2 : ℝ)).div_const 17)) using 1
    all_goals try funext x
    all_goals simp
    all_goals ring
  have hi : (∫ t in (-1 : ℝ)..1, P t)=490496/765765 := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t)
      ((by dsimp [P]; fun_prop : Continuous P).intervalIntegrable _ _)]
    norm_num [Q]
  have hm : (∫ t in (-1 : ℝ)..1, ((1-t^2)^3*Real.exp (-(t^2)/2))^2) ≤
      ∫ t in (-1 : ℝ)..1, P t := by
    apply intervalIntegral.integral_mono_on (by norm_num)
    · exact (by fun_prop : Continuous (fun t : ℝ =>
        ((1-t^2)^3*Real.exp (-(t^2)/2))^2)).intervalIntegrable _ _
    · exact (by dsimp [P]; fun_prop : Continuous P).intervalIntegrable _ _
    · exact fun t _ => hp t
  rw [hi] at hm
  exact hm.trans (by norm_num)

lemma etaCircle_square_integral_eq_symmetric :
    (∫ t : ℝ, (etaCircle t)^2) =
      ∫ t in (-1 : ℝ)..1, ((1-t^2)^3*Real.exp (-(t^2)/2))^2 := by
  have heq : (∫ t : ℝ, (etaCircle t)^2) =
      ∫ t in (-1 : ℝ)..1, ((1-t^2)^3 * Real.exp (-(t^2)/2))^2 := by
    calc
      (∫ t : ℝ, (etaCircle t)^2) =
          ∫ t : ℝ, (Set.Icc (0 : ℝ) 2).indicator
            (fun t => (t^3*(2-t)^3*Real.exp (-((t-1)^2)/2))^2) t := by
        apply integral_congr_ae
        exact Eventually.of_forall (fun t => by
          by_cases ht : t ∈ Set.Icc (0 : ℝ) 2 <;> simp [etaCircle,ht])
      _ = ∫ t in (0 : ℝ)..2, (t^3*(2-t)^3*Real.exp (-((t-1)^2)/2))^2 := by
        rw [integral_indicator measurableSet_Icc,integral_Icc_eq_integral_Ioc,
          intervalIntegral.integral_of_le (by norm_num)]
      _ = ∫ t in (-1 : ℝ)..1,
          ((t+1)^3*(2-(t+1))^3*Real.exp (-(((t+1)-1)^2)/2))^2 := by
        simpa only [neg_add_cancel,one_add_one_eq_two] using
          (intervalIntegral.integral_comp_add_right
            (fun t : ℝ => (t^3*(2-t)^3*Real.exp (-((t-1)^2)/2))^2) 1
            (a := (-1 : ℝ)) (b := 1)).symm
      _ = _ := by
        apply intervalIntegral.integral_congr
        intro t _
        simp only [add_sub_cancel_right]
        ring
  exact heq

lemma etaCircle_square_integral_upper : (∫ t : ℝ, (etaCircle t)^2) ≤ 641/1000 := by
  rw [etaCircle_square_integral_eq_symmetric]
  exact symmetric_smoothing_l2_upper

end Helfgott

end

section

open MeasureTheory Set

set_option backward.isDefEq.respectTransparency false

namespace Helfgott

lemma abs_mul_le_half_squares (x y : ℝ) : |x*y| ≤ (x^2+y^2)/2 := by
  apply abs_le.mpr
  constructor
  · nlinarith [sq_nonneg (x+y)]
  · nlinarith [sq_nonneg (x-y)]

lemma abs_mul_le_unequal_squares (x y : ℝ) : |x*y| ≤ x^2/4000+1000*y^2 := by
  apply abs_le.mpr
  constructor
  · nlinarith [sq_nonneg (x+2000*y)]
  · nlinarith [sq_nonneg (x-2000*y)]

lemma integrable_mul_of_square_integrable (f g : ℝ → ℝ)
    (hf : Measurable f) (hg : Measurable g)
    (hf2 : Integrable (fun u => (f u)^2)) (hg2 : Integrable (fun u => (g u)^2)) :
    Integrable (fun u => f u*g u) := by
  apply (hf2.add hg2).mono' (hf.mul hg).aestronglyMeasurable
  exact ae_of_all _ (fun u => by
    simp only [Real.norm_eq_abs,Pi.add_apply,Pi.mul_apply]
    nlinarith [abs_mul_le_half_squares (f u) (g u),sq_nonneg (f u),sq_nonneg (g u)])

theorem convolution_difference_error_bound (f g : ℝ → ℝ)
    (hf : Measurable f) (hg : Measurable g)
    (hg2 : Integrable (fun u => (g u)^2))
    (hd2 : Integrable (fun u => (f u-g u)^2))
    (hgb : (∫ u : ℝ, (g u)^2) ≤ 641/1000)
    (hdb : (∫ u : ℝ, (f u-g u)^2) ≤ 1/6250000)
    (ρ : ℝ) :
    Integrable (fun u => f u*f (ρ-u)) ∧
    |(∫ u : ℝ, f u*f (ρ-u))-(∫ u : ℝ, g u*g (ρ-u))| ≤ 32033/50000000 := by
  let d : ℝ → ℝ := fun u => f u-g u
  have hd : Measurable d := hf.sub hg
  have hd2' : Integrable (fun u => (d u)^2) := hd2
  have hdb' : (∫ u : ℝ, (d u)^2) ≤ 1/6250000 := hdb
  have hgm : Measurable (fun u => g (ρ-u)) := hg.comp (measurable_const.sub measurable_id)
  have hdm : Measurable (fun u => d (ρ-u)) := hd.comp (measurable_const.sub measurable_id)
  have hgsq := hg2.comp_sub_left ρ
  have hdsq := hd2'.comp_sub_left ρ
  have hiA := integrable_mul_of_square_integrable g (fun u => g (ρ-u)) hg hgm hg2 hgsq
  have hiB := integrable_mul_of_square_integrable d (fun u => g (ρ-u)) hd hgm hd2' hgsq
  have hiC := integrable_mul_of_square_integrable g (fun u => d (ρ-u)) hg hdm hg2 hdsq
  have hiD := integrable_mul_of_square_integrable d (fun u => d (ρ-u)) hd hdm hd2' hdsq
  have hBM : (∫ u : ℝ, |d u*g (ρ-u)|) ≤ 1281/4000000 := by
    calc
      _ ≤ ∫ u : ℝ, (g (ρ-u))^2/4000+1000*(d u)^2 := by
        apply integral_mono hiB.abs ((hgsq.div_const 4000).add (hd2'.const_mul 1000))
        intro u
        simpa only [mul_comm,Pi.add_apply] using abs_mul_le_unequal_squares (g (ρ-u)) (d u)
      _ = (∫ u : ℝ, (g u)^2)/4000+1000*(∫ u : ℝ, (d u)^2) := by
        rw [integral_add (hgsq.div_const 4000) (hd2'.const_mul 1000),integral_div,
          integral_const_mul,integral_sub_left_eq_self (fun u => (g u)^2) volume ρ]
      _ ≤ _ := by linarith
  have hCM : (∫ u : ℝ, |g u*d (ρ-u)|) ≤ 1281/4000000 := by
    calc
      _ ≤ ∫ u : ℝ, (g u)^2/4000+1000*(d (ρ-u))^2 :=
        integral_mono hiC.abs ((hg2.div_const 4000).add (hdsq.const_mul 1000))
          (fun u => abs_mul_le_unequal_squares (g u) (d (ρ-u)))
      _ = (∫ u : ℝ, (g u)^2)/4000+1000*(∫ u : ℝ, (d u)^2) := by
        rw [integral_add (hg2.div_const 4000) (hdsq.const_mul 1000),integral_div,
          integral_const_mul,integral_sub_left_eq_self (fun u => (d u)^2) volume ρ]
      _ ≤ _ := by linarith
  have hDM : (∫ u : ℝ, |d u*d (ρ-u)|) ≤ 1/6250000 := by
    calc
      _ ≤ ∫ u : ℝ, ((d u)^2+(d (ρ-u))^2)/2 :=
        integral_mono hiD.abs ((hd2'.add hdsq).div_const 2)
          (fun u => abs_mul_le_half_squares (d u) (d (ρ-u)))
      _ = (∫ u : ℝ, (d u)^2) := by
        rw [integral_div,integral_add hd2' hdsq,
          integral_sub_left_eq_self (fun u => (d u)^2) volume ρ]
        ring
      _ ≤ _ := hdb'
  have heq : (fun u => f u*f (ρ-u)) =
      (fun u => g u*g (ρ-u)+d u*g (ρ-u)+g u*d (ρ-u)+d u*d (ρ-u)) := by
    funext u
    dsimp only [d]
    ring
  have hiF : Integrable (fun u => f u*f (ρ-u)) := by
    rw [heq]
    exact ((hiA.add hiB).add hiC).add hiD
  refine ⟨hiF,?_⟩
  have hEA : (∫ u : ℝ, f u*f (ρ-u))-(∫ u : ℝ, g u*g (ρ-u)) =
      (∫ u : ℝ, d u*g (ρ-u))+(∫ u : ℝ, g u*d (ρ-u))+(∫ u : ℝ, d u*d (ρ-u)) := by
    have e1 := integral_add hiA hiB
    have e2 := integral_add (hiA.add hiB) hiC
    have e3 := integral_add ((hiA.add hiB).add hiC) hiD
    simp only [Pi.add_apply] at e1 e2 e3
    rw [heq,e3,e2,e1]
    ring
  rw [hEA]
  have hnB := norm_integral_le_integral_norm (μ := volume) (fun u => d u*g (ρ-u))
  have hnC := norm_integral_le_integral_norm (μ := volume) (fun u => g u*d (ρ-u))
  have hnD := norm_integral_le_integral_norm (μ := volume) (fun u => d u*d (ρ-u))
  simp only [Real.norm_eq_abs] at hnB hnC hnD
  have ht1 := abs_add_le (∫ u : ℝ, d u*g (ρ-u)) (∫ u : ℝ, g u*d (ρ-u))
  have ht2 := abs_add_le ((∫ u : ℝ, d u*g (ρ-u))+(∫ u : ℝ, g u*d (ρ-u)))
    (∫ u : ℝ, d u*d (ρ-u))
  linarith

theorem etaPlus_convolution_approximation (ρ : ℝ) :
    Integrable (fun u : ℝ => etaPlus u*etaPlus (ρ-u)) ∧
    |(∫ u : ℝ, etaPlus u*etaPlus (ρ-u))-
      (∫ u : ℝ, etaCircle u*etaCircle (ρ-u))| ≤ 32033/50000000 :=
  convolution_difference_error_bound etaPlus etaCircle etaPlus_measurable
    etaCircle_continuous.measurable etaCircle_square_integrable etaPlus_approx_square_integrable
    etaCircle_square_integral_upper etaPlus_approx_l2_square_le ρ

end Helfgott

end

section

open MeasureTheory Set
open scoped Interval

namespace Helfgott

lemma etaTwo_nonneg (t : ℝ) : 0 ≤ etaTwo t := by
  unfold etaTwo
  split_ifs <;> positivity

lemma etaTwo_le (t : ℝ) : etaTwo t ≤ 4 * Real.log 2 := by
  have hlog : 0 ≤ Real.log (2 : ℝ) := Real.log_nonneg (by norm_num)
  unfold etaTwo
  split_ifs
  · apply mul_le_mul_of_nonneg_left _ (by norm_num)
    exact max_le (sub_le_self _ (abs_nonneg _)) hlog
  · positivity

lemma etaTwo_eq_zero_of_not_mem (t : ℝ) (ht : t ∉ Set.Icc (1/4 : ℝ) 1) :
    etaTwo t = 0 := by
  by_cases hpos : 0 < t
  · unfold etaTwo
    rw [if_pos hpos]
    have htwopos : 0 < 2*t := by positivity
    have hm : Real.log 2 - |Real.log (2*t)| ≤ 0 := by
      rcases (not_and_or.mp ht) with hlo | hhi
      · have hlt : 2*t ≤ (1/2 : ℝ) := by push_neg at hlo; linarith
        have hlog := Real.log_le_log htwopos hlt
        have hhalf : Real.log (1/2 : ℝ) = -Real.log 2 := by
          rw [one_div, Real.log_inv]
        rw [hhalf] at hlog
        linarith [neg_le_abs (Real.log (2*t))]
      · have hlt : (2 : ℝ) ≤ 2*t := by push_neg at hhi; linarith
        have hlog := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hlt
        linarith [le_abs_self (Real.log (2*t))]
    rw [max_eq_right hm, mul_zero]
  · simp [etaTwo,hpos]

lemma etaTwo_eq_lower (t : ℝ) (ht : t ∈ Set.Icc (1/4 : ℝ) (1/2)) :
    etaTwo t = 4 * Real.log (4*t) := by
  have hpos : 0 < t := by linarith [ht.1]
  have hprod : 0 < 2*t := by positivity
  have hlogneg : Real.log (2*t) ≤ 0 := Real.log_nonpos (le_of_lt hprod) (by linarith [ht.2])
  have hsum : Real.log 2 + Real.log (2*t) = Real.log (4*t) := by
    rw [← Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (ne_of_gt hprod)]
    congr 1; ring
  have hn : 0 ≤ Real.log (4*t) := Real.log_nonneg (by linarith [ht.1])
  unfold etaTwo
  rw [if_pos hpos, abs_of_nonpos hlogneg, sub_neg_eq_add, hsum, max_eq_left hn]

lemma etaTwo_eq_upper (t : ℝ) (ht : t ∈ Set.Icc (1/2 : ℝ) 1) :
    etaTwo t = -4 * Real.log t := by
  have hpos : 0 < t := by linarith [ht.1]
  have hlogpos : 0 ≤ Real.log (2*t) := Real.log_nonneg (by linarith [ht.1])
  have hlogneg : Real.log t ≤ 0 := Real.log_nonpos (le_of_lt hpos) ht.2
  have hlog : Real.log (2*t) = Real.log 2 + Real.log t :=
    Real.log_mul (by norm_num) (ne_of_gt hpos)
  unfold etaTwo
  rw [if_pos hpos, abs_of_nonneg hlogpos, hlog]
  have hm : Real.log 2 - (Real.log 2 + Real.log t) = -Real.log t := by ring
  rw [hm, max_eq_left (neg_nonneg.mpr hlogneg)]
  ring

lemma etaTwo_continuousOn_pos : ContinuousOn etaTwo (Set.Ioi (0 : ℝ)) := by
  intro t ht
  apply ContinuousAt.continuousWithinAt
  have hg : ContinuousAt (fun s : ℝ => 4 * max (Real.log 2 - |Real.log (2*s)|) 0) t := by
    have hpos : 0 < t := ht
    have hn : 2*t ≠ 0 := by positivity
    fun_prop
  apply hg.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds ht] with x hx
  simp only [etaTwo, if_pos (show 0 < x from hx)]

theorem etaTwo_mass_interval : (∫ t in (1/4 : ℝ)..1, etaTwo t) = 1 := by
  have hint (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : IntervalIntegrable etaTwo volume a b := by
    apply ContinuousOn.intervalIntegrable
    apply etaTwo_continuousOn_pos.mono
    intro t ht
    exact lt_of_lt_of_le (lt_min ha hb) ht.1
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hint (1/4) (1/2) (by norm_num) (by norm_num))
    (hint (1/2) 1 (by norm_num) (by norm_num))]
  have hlo : (∫ t in (1/4 : ℝ)..(1/2), etaTwo t) =
      ∫ t in (1/4 : ℝ)..(1/2), 4 * (Real.log 4 + Real.log t) := by
    apply intervalIntegral.integral_congr
    intro t ht
    have hmem : t ∈ Set.Icc (1/4 : ℝ) (1/2) := by
      have h := Set.uIcc_of_le (by norm_num : (1/4 : ℝ) ≤ 1/2)
      rw [h] at ht
      exact ht
    rw [etaTwo_eq_lower t hmem, Real.log_mul (by norm_num) (by linarith [hmem.1] : t ≠ 0)]
  have hhi : (∫ t in (1/2 : ℝ)..1, etaTwo t) = ∫ t in (1/2 : ℝ)..1, -4 * Real.log t := by
    apply intervalIntegral.integral_congr
    intro t ht
    apply etaTwo_eq_upper
    rw [Set.uIcc_of_le (by norm_num : (1/2 : ℝ) ≤ 1)] at ht
    exact ht
  rw [hlo,hhi,intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul,
    intervalIntegral.integral_add (intervalIntegrable_const) (intervalIntegral.intervalIntegrable_log'),
    intervalIntegral.integral_const,integral_log,integral_log]
  have h4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2^2 by norm_num, Real.log_pow]
    norm_num
  have hhalf : Real.log (1/2 : ℝ) = -Real.log 2 := by rw [one_div,Real.log_inv]
  have hquarter : Real.log (1/4 : ℝ) = -(2 * Real.log 2) := by rw [one_div,Real.log_inv,h4]
  rw [h4,hhalf,hquarter,Real.log_one]
  norm_num
  ring

lemma etaTwo_continuous : Continuous etaTwo := by
  apply continuous_iff_continuousAt.mpr
  intro t
  by_cases ht : 0 < t
  · exact (etaTwo_continuousOn_pos t ht).continuousAt (Ioi_mem_nhds ht)
  · have hlo : t < (1/4 : ℝ) := by linarith
    apply (continuousAt_const (y := (0 : ℝ))).congr_of_eventuallyEq
    filter_upwards [Iio_mem_nhds hlo] with x hx
    apply etaTwo_eq_zero_of_not_mem
    intro h; exact (not_lt_of_ge h.1) hx

lemma etaTwo_hasCompactSupport : HasCompactSupport etaTwo := by
  apply HasCompactSupport.intro (K := Set.Icc (1/4 : ℝ) 1) isCompact_Icc
  exact etaTwo_eq_zero_of_not_mem

lemma etaTwo_integrable : Integrable etaTwo :=
  etaTwo_continuous.integrable_of_hasCompactSupport etaTwo_hasCompactSupport

theorem etaTwo_mass : (∫ t : ℝ, etaTwo t) = 1 := by
  have hind : (Set.Icc (1/4 : ℝ) 1).indicator etaTwo = etaTwo := by
    funext t
    by_cases ht : t ∈ Set.Icc (1/4 : ℝ) 1
    · exact Set.indicator_of_mem ht etaTwo
    · rw [Set.indicator_of_notMem ht,etaTwo_eq_zero_of_not_mem t ht]
  calc
    (∫ t : ℝ, etaTwo t) = ∫ t : ℝ, (Set.Icc (1/4 : ℝ) 1).indicator etaTwo t := by rw [hind]
    _ = ∫ t in Set.Icc (1/4 : ℝ) 1, etaTwo t := integral_indicator measurableSet_Icc
    _ = ∫ t in (1/4 : ℝ)..1, etaTwo t := by
      rw [intervalIntegral.integral_of_le (by norm_num),integral_Icc_eq_integral_Ioc]
    _ = 1 := etaTwo_mass_interval

end Helfgott



end

section

open MeasureTheory Set
open scoped Interval

namespace Helfgott

lemma etaTwo_scaled_zero (T w : ℝ) (hT : 0 < T) (hw : w ∉ Icc T (4*T)) :
    etaTwo (T/w) = 0 := by
  by_cases hwp : 0 < w
  · apply etaTwo_eq_zero_of_not_mem
    intro h
    apply hw
    constructor
    · simpa using (div_le_iff₀ hwp).mp h.2
    · have hh := (le_div_iff₀ hwp).mp h.1
      nlinarith
  · have hh : T/w ≤ 0 := div_nonpos_of_nonneg_of_nonpos hT.le (le_of_not_gt hwp)
    simp [etaTwo, not_lt_of_ge hh]

lemma etaTwo_scaled_weight_continuous (T : ℝ) (hT : 0 < T) :
    Continuous (fun w : ℝ => etaTwo (T/w)/w) := by
  apply continuous_iff_continuousAt.mpr
  intro w
  by_cases hw : w = 0
  · subst w
    apply (continuousAt_const (y := (0 : ℝ))).congr_of_eventuallyEq
    filter_upwards [Iio_mem_nhds hT] with x hx
    change x < T at hx
    rw [etaTwo_scaled_zero T x hT (by intro hm; linarith [hm.1]), zero_div]
  · have hc : ContinuousAt (fun x : ℝ => T/x) w := by fun_prop
    exact (etaTwo_continuous.continuousAt.comp hc).div continuousAt_id hw

lemma etaTwo_scaled_weight_integrable (T : ℝ) (hT : 0 < T) :
    Integrable (fun w : ℝ => etaTwo (T/w)/w) := by
  apply (etaTwo_scaled_weight_continuous T hT).integrable_of_hasCompactSupport
  apply HasCompactSupport.intro (K := Icc T (4*T)) isCompact_Icc
  intro w hw
  rw [etaTwo_scaled_zero T w hT hw,zero_div]

lemma etaTwo_scaled_lower (T w : ℝ) (hT : 0 < T) (hw : w ∈ Icc T (2*T)) :
    etaTwo (T/w) = 4 * (Real.log w - Real.log T) := by
  have hwp : 0 < w := lt_of_lt_of_le hT hw.1
  have hm : T/w ∈ Icc (1/2 : ℝ) 1 := by
    constructor
    · apply (le_div_iff₀ hwp).mpr; linarith [hw.2]
    · apply (div_le_iff₀ hwp).mpr; simpa using hw.1
  rw [etaTwo_eq_upper _ hm, Real.log_div hT.ne' hwp.ne']
  ring

lemma etaTwo_scaled_upper (T w : ℝ) (hT : 0 < T) (hw : w ∈ Icc (2*T) (4*T)) :
    etaTwo (T/w) = 4 * (Real.log (4*T) - Real.log w) := by
  have hwp : 0 < w := by linarith [hw.1]
  have hm : T/w ∈ Icc (1/4 : ℝ) (1/2) := by
    constructor
    · apply (le_div_iff₀ hwp).mpr; linarith [hw.2]
    · apply (div_le_iff₀ hwp).mpr; linarith [hw.1]
  rw [etaTwo_eq_lower _ hm]
  rw [show 4*(T/w) = (4*T)/w by ring,
    Real.log_div (by positivity : 4*T ≠ 0) hwp.ne']

theorem etaTwo_scaled_log_mass (T : ℝ) (hT : 0 < T) :
    (∫ w in Ioi (0 : ℝ), etaTwo (T/w)/w) = 4 * (Real.log 2)^2 := by
  have hf := etaTwo_scaled_weight_continuous T hT
  have hi (a b : ℝ) : IntervalIntegrable (fun w => etaTwo (T/w)/w) volume a b :=
    hf.intervalIntegrable _ _
  have hrestrict : (∫ w in Ioi (0 : ℝ), etaTwo (T/w)/w) =
      ∫ w in T..4*T, etaTwo (T/w)/w := by
    rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
      (show Icc T (4*T) ⊆ Ioi (0 : ℝ) by intro w hw; exact lt_of_lt_of_le hT hw.1)
      (show ∀ w ∈ Ioi (0 : ℝ) \ Icc T (4*T), etaTwo (T/w)/w = 0 by
        intro w hw; rw [etaTwo_scaled_zero T w hT hw.2,zero_div])]
    rw [intervalIntegral.integral_of_le (by linarith),integral_Icc_eq_integral_Ioc]
  rw [hrestrict, ← intervalIntegral.integral_add_adjacent_intervals (hi T (2*T)) (hi (2*T) (4*T))]
  have hlo : (∫ w in T..2*T, etaTwo (T/w)/w) =
      2*(Real.log (2*T)-Real.log T)^2 := by
    have heq : (∫ w in T..2*T, etaTwo (T/w)/w) =
        ∫ w in T..2*T, 4*(Real.log w-Real.log T)/w := by
      apply intervalIntegral.integral_congr
      intro w hw
      rw [Set.uIcc_of_le (by linarith : T ≤ 2*T)] at hw
      dsimp only
      rw [etaTwo_scaled_lower T w hT hw]
    rw [heq]
    have hint : IntervalIntegrable (fun w : ℝ => 4*(Real.log w-Real.log T)/w)
        volume T (2*T) := by
      apply ContinuousOn.intervalIntegrable
      intro w hw
      have hwp : 0 < w := by
        rw [Set.uIcc_of_le (by linarith : T ≤ 2*T)] at hw
        linarith [hw.1]
      apply ContinuousAt.continuousWithinAt
      have hwn : w ≠ 0 := hwp.ne'
      fun_prop
    have hd (w : ℝ) (hw : w ∈ uIcc T (2*T)) :
        HasDerivAt (fun w : ℝ => 2*(Real.log w-Real.log T)^2)
          (4*(Real.log w-Real.log T)/w) w := by
      rw [Set.uIcc_of_le (by linarith : T ≤ 2*T)] at hw
      have hwp : 0 < w := by linarith [hw.1]
      convert! (((Real.hasDerivAt_log hwp.ne').sub_const (Real.log T)).pow 2).const_mul 2 using 1 <;> simp <;> ring
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hint]
    simp
  have hhi : (∫ w in 2*T..4*T, etaTwo (T/w)/w) =
      2*(Real.log (4*T)-Real.log (2*T))^2 := by
    have heq : (∫ w in 2*T..4*T, etaTwo (T/w)/w) =
        ∫ w in 2*T..4*T, 4*(Real.log (4*T)-Real.log w)/w := by
      apply intervalIntegral.integral_congr
      intro w hw
      rw [Set.uIcc_of_le (by linarith : 2*T ≤ 4*T)] at hw
      dsimp only
      rw [etaTwo_scaled_upper T w hT hw]
    rw [heq]
    have hint : IntervalIntegrable (fun w : ℝ => 4*(Real.log (4*T)-Real.log w)/w)
        volume (2*T) (4*T) := by
      apply ContinuousOn.intervalIntegrable
      intro w hw
      have hwp : 0 < w := by
        rw [Set.uIcc_of_le (by linarith : 2*T ≤ 4*T)] at hw
        linarith [hw.1]
      apply ContinuousAt.continuousWithinAt
      have hwn : w ≠ 0 := hwp.ne'
      fun_prop
    have hd (w : ℝ) (hw : w ∈ uIcc (2*T) (4*T)) :
        HasDerivAt (fun w : ℝ => -2*(Real.log (4*T)-Real.log w)^2)
          (4*(Real.log (4*T)-Real.log w)/w) w := by
      rw [Set.uIcc_of_le (by linarith : 2*T ≤ 4*T)] at hw
      have hwp : 0 < w := by linarith [hw.1]
      convert! (((Real.hasDerivAt_log hwp.ne').const_sub (Real.log (4*T))).pow 2).const_mul (-2) using 1 <;> simp <;> ring
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hint]
    simp
  rw [hlo,hhi,Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hT.ne',
    Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) hT.ne']
  have h4 : Real.log (4 : ℝ) = 2*Real.log 2 := by
    rw [show (4 : ℝ) = 2^2 by norm_num, Real.log_pow]; norm_num
  rw [h4]
  ring

lemma phi_nonneg (t : ℝ) : 0 ≤ phi t := by unfold phi; positivity

lemma phi_le (t : ℝ) : phi t ≤ 2 / Real.exp 1 := by
  have h := Real.mul_exp_neg_le_exp_neg_one (t^2/2)
  have he : Real.exp (-1 : ℝ) = (Real.exp 1)⁻¹ := Real.exp_neg 1
  rw [he] at h
  unfold phi
  have heq : -(t^2/2) = -(t^2)/2 := by ring
  rw [heq] at h
  calc
    t^2*Real.exp (-(t^2)/2) = 2*((t^2/2)*Real.exp (-(t^2)/2)) := by ring
    _ ≤ 2*(Real.exp 1)⁻¹ := mul_le_mul_of_nonneg_left h (by norm_num)
    _ = 2/Real.exp 1 := by ring

lemma mellin_etaTwo_phi_integrable (T : ℝ) (hT : 0 < T) :
    Integrable (fun w : ℝ => etaTwo (T/w)*phi w/w) := by
  have hphi : Continuous phi := by unfold phi; fun_prop
  have hc : Continuous (fun w : ℝ => (etaTwo (T/w)/w)*phi w) :=
    (etaTwo_scaled_weight_continuous T hT).mul hphi
  have hs : HasCompactSupport (fun w : ℝ => (etaTwo (T/w)/w)*phi w) := by
    apply HasCompactSupport.intro (K := Icc T (4*T)) isCompact_Icc
    intro w hw
    rw [etaTwo_scaled_zero T w hT hw,zero_div,zero_mul]
  have hh : Integrable (fun w : ℝ => (etaTwo (T/w)/w)*phi w) := hc.integrable_of_hasCompactSupport hs
  have heq : (fun w : ℝ => etaTwo (T/w)*phi w/w) = (fun w : ℝ => (etaTwo (T/w)/w)*phi w) := by
    funext w; ring
  rw [heq]
  exact hh

lemma mellin_etaTwo_phi_nonneg (T : ℝ) : 0 ≤ mellinConv etaTwo phi T := by
  unfold mellinConv
  apply integral_nonneg_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with w hw
  exact div_nonneg (mul_nonneg (etaTwo_nonneg _) (phi_nonneg _)) (le_of_lt hw)

lemma mellin_etaTwo_phi_le (T : ℝ) :
    mellinConv etaTwo phi T ≤ 8*(Real.log 2)^2/Real.exp 1 := by
  by_cases hT : 0 < T
  · have hi := (mellin_etaTwo_phi_integrable T hT).restrict (s := Ioi (0 : ℝ))
    have hg := ((etaTwo_scaled_weight_integrable T hT).const_mul (2/Real.exp 1)).restrict
      (s := Ioi (0 : ℝ))
    have hbound : (∫ w in Ioi (0 : ℝ), etaTwo (T/w)*phi w/w) ≤
        ∫ w in Ioi (0 : ℝ), (2/Real.exp 1)*(etaTwo (T/w)/w) := by
      apply integral_mono_ae hi hg
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with w hw
      have he := mul_le_mul_of_nonneg_left (phi_le w) (etaTwo_nonneg (T/w))
      have hh := div_le_div_of_nonneg_right he (le_of_lt hw)
      convert! hh using 1 <;> ring
    unfold mellinConv
    refine hbound.trans_eq ?_
    rw [integral_const_mul,etaTwo_scaled_log_mass T hT]
    ring
  · have hz : mellinConv etaTwo phi T = 0 := by
      unfold mellinConv
      apply integral_eq_zero_of_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with w hw
      have hh : T/w ≤ 0 := div_nonpos_of_nonpos_of_nonneg (le_of_not_gt hT) (le_of_lt hw)
      simp [etaTwo,not_lt_of_ge hh]
    rw [hz]
    positivity

lemma mellin_etaTwo_phi_le_rational (T : ℝ) :
    mellinConv etaTwo phi T ≤ (707/500 : ℝ) := by
  apply (mellin_etaTwo_phi_le T).trans
  apply (div_le_iff₀ (Real.exp_pos 1)).mpr
  have hlog : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hs : (Real.log 2)^2 ≤ (0.6931471808 : ℝ)^2 :=
    pow_le_pow_left₀ hlog Real.log_two_lt_d9.le 2
  nlinarith only [hs, Real.exp_one_gt_d9]

theorem etaStar_abs_le (t : ℝ) : |etaStar t| ≤ (707/500 : ℝ) := by
  unfold etaStar
  rw [abs_of_nonneg (mellin_etaTwo_phi_nonneg (49*t))]
  exact mellin_etaTwo_phi_le_rational (49*t)

end Helfgott

end

section

open MeasureTheory Set Filter

namespace Helfgott

lemma mellin_inner_integrable (f : ℝ → ℝ) (hf : IntegrableOn f (Ioi (0 : ℝ)))
    (w c : ℝ) (hw : 0 < w) :
    IntegrableOn (fun t : ℝ => f (t/w)*c/w) (Ioi (0 : ℝ)) := by
  have hh : IntegrableOn (fun t : ℝ => f (t*w⁻¹)) (Ioi (0 : ℝ)) := by
    apply (integrableOn_Ioi_comp_mul_right_iff f 0 (inv_pos.mpr hw)).mpr
    simpa using hf
  simpa only [IntegrableOn,div_eq_mul_inv,mul_assoc] using (hh.mul_const c).mul_const w⁻¹

lemma mellin_inner_integral (f : ℝ → ℝ) (w c : ℝ) (hw : 0 < w) :
    (∫ t in Ioi (0 : ℝ), f (t/w)*c/w) = c*(∫ t in Ioi (0 : ℝ), f t) := by
  simp_rw [div_eq_mul_inv]
  rw [integral_mul_const,integral_mul_const,
    integral_comp_mul_right_Ioi f 0 (inv_pos.mpr hw)]
  simp only [zero_mul,inv_inv,smul_eq_mul]
  field_simp

theorem mellin_integrable_mass (f g : ℝ → ℝ) (hf : Continuous f) (hg : Continuous g)
    (hfi : IntegrableOn f (Ioi (0 : ℝ))) (hgi : IntegrableOn g (Ioi (0 : ℝ)))
    (hfn : ∀ t, 0 < t → 0 ≤ f t) (hgn : ∀ t, 0 < t → 0 ≤ g t) :
    IntegrableOn (mellinConv f g) (Ioi (0 : ℝ)) ∧
    (∫ t in Ioi (0 : ℝ), mellinConv f g t) =
      (∫ t in Ioi (0 : ℝ), f t)*(∫ t in Ioi (0 : ℝ), g t) := by
  let μ : Measure ℝ := volume.restrict (Ioi (0 : ℝ))
  have hm : Measurable (fun z : ℝ × ℝ => f (z.2/z.1)*g z.1/z.1) := by
    fun_prop
  have hp : Integrable (fun z : ℝ × ℝ => f (z.2/z.1)*g z.1/z.1) (μ.prod μ) := by
    apply (integrable_prod_iff hm.aestronglyMeasurable).mpr
    constructor
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with w hw
      exact mellin_inner_integrable f hfi w (g w) hw
    · have heq : (fun w : ℝ => ∫ t, ‖f (t/w)*g w/w‖ ∂μ) =ᵐ[μ]
          fun w => g w*(∫ t, f t ∂μ) := by
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with w hw
        have hnorm : (∫ t, ‖f (t/w)*g w/w‖ ∂μ) = ∫ t, f (t/w)*g w/w ∂μ := by
          apply integral_congr_ae
          filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
          exact Real.norm_of_nonneg
            (div_nonneg (mul_nonneg (hfn _ (div_pos ht hw)) (hgn _ hw)) hw.le)
        rw [hnorm]
        exact mellin_inner_integral f w (g w) hw
      apply (hgi.mul_const (∫ t, f t ∂μ)).congr
      exact heq.symm
  constructor
  · exact hp.integral_prod_right
  unfold mellinConv
  change (∫ t, ∫ w, f (t/w)*g w/w ∂μ ∂μ) = _
  rw [← integral_integral_swap hp]
  have heq : (∫ w, ∫ t, f (t/w)*g w/w ∂μ ∂μ) =
      ∫ w, g w*(∫ t, f t ∂μ) ∂μ := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with w hw
    exact mellin_inner_integral f w (g w) hw
  rw [heq,integral_mul_const]
  exact mul_comm _ _

lemma mellin_moment_identity (f g : ℝ → ℝ) (k : ℕ) (t : ℝ) :
    t^k*mellinConv f g t =
      mellinConv (fun t => t^k*f t) (fun w => w^k*g w) t := by
  unfold mellinConv
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with w hw
  rw [div_pow]
  have hn : w ≠ 0 := hw.ne'
  field_simp

theorem mellin_moment (f g : ℝ → ℝ) (hf : Continuous f) (hg : Continuous g)
    (k : ℕ) (hfi : IntegrableOn (fun t => t^k*f t) (Ioi (0 : ℝ)))
    (hgi : IntegrableOn (fun t => t^k*g t) (Ioi (0 : ℝ)))
    (hfn : ∀ t, 0 < t → 0 ≤ f t) (hgn : ∀ t, 0 < t → 0 ≤ g t) :
    IntegrableOn (fun t => t^k*mellinConv f g t) (Ioi (0 : ℝ)) ∧
    (∫ t in Ioi (0 : ℝ), t^k*mellinConv f g t) =
      (∫ t in Ioi (0 : ℝ), t^k*f t)*(∫ t in Ioi (0 : ℝ), t^k*g t) := by
  simp_rw [mellin_moment_identity]
  apply mellin_integrable_mass _ _ ((continuous_id.pow k).mul hf) ((continuous_id.pow k).mul hg)
    hfi hgi
  · intro t ht; exact mul_nonneg (pow_nonneg ht.le k) (hfn t ht)
  · intro t ht; exact mul_nonneg (pow_nonneg ht.le k) (hgn t ht)

end Helfgott

end

section

open MeasureTheory Set
open scoped Interval

namespace Helfgott

lemma integral_power_log (k : ℕ) (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (C : ℝ) :
    (∫ t in a..b, t^k*(C+Real.log t)) =
      b^(k+1)/((k:ℝ)+1)*(C+Real.log b-1/((k:ℝ)+1)) -
      a^(k+1)/((k:ℝ)+1)*(C+Real.log a-1/((k:ℝ)+1)) := by
  have hkn : (k:ℝ)+1 ≠ 0 := by have hk := Nat.cast_nonneg (α := ℝ) k; linarith
  have hpos (t : ℝ) (ht : t ∈ uIcc a b) : 0 < t := lt_of_lt_of_le (lt_min ha hb) ht.1
  have hi : IntervalIntegrable (fun t : ℝ => t^k*(C+Real.log t)) volume a b := by
    apply ContinuousOn.intervalIntegrable
    intro t ht
    have hn : t ≠ 0 := (hpos t ht).ne'
    apply ContinuousAt.continuousWithinAt
    fun_prop
  have hd (t : ℝ) (ht : t ∈ uIcc a b) :
      HasDerivAt (fun t : ℝ => t^(k+1)/((k:ℝ)+1)*(C+Real.log t-1/((k:ℝ)+1)))
        (t^k*(C+Real.log t)) t := by
    have hn : t ≠ 0 := (hpos t ht).ne'
    have hp := ((hasDerivAt_id t).pow (k+1)).div_const ((k:ℝ)+1)
    have hl := ((Real.hasDerivAt_log hn).const_add C).sub_const (1/((k:ℝ)+1))
    convert! hp.mul hl using 1
    all_goals simp only [Nat.cast_add,Nat.cast_one,Nat.add_sub_cancel,one_mul,id_eq,Pi.pow_apply]
    all_goals field_simp
    all_goals simp only [pow_succ]
    all_goals ring
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi

lemma etaTwo_moment_integrable (k : ℕ) : Integrable (fun t : ℝ => t^k*etaTwo t) := by
  apply ((continuous_id.pow k).mul etaTwo_continuous).integrable_of_hasCompactSupport
  exact etaTwo_hasCompactSupport.mul_left

lemma etaTwo_moment_formula (k : ℕ) :
    (∫ t : ℝ, t^k*etaTwo t) =
      4*((1/2:ℝ)^(k+1)/((k:ℝ)+1)*(Real.log 4+Real.log (1/2)-1/((k:ℝ)+1)) -
        (1/4:ℝ)^(k+1)/((k:ℝ)+1)*(Real.log 4+Real.log (1/4)-1/((k:ℝ)+1))) -
      4*(1/((k:ℝ)+1)*(Real.log 1-1/((k:ℝ)+1)) -
        (1/2:ℝ)^(k+1)/((k:ℝ)+1)*(Real.log (1/2)-1/((k:ℝ)+1))) := by
  have hc : Continuous (fun t : ℝ => t^k*etaTwo t) := (continuous_id.pow k).mul etaTwo_continuous
  have heq : (∫ t : ℝ, t^k*etaTwo t) = ∫ t in (1/4:ℝ)..1, t^k*etaTwo t := by
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Icc (1/4:ℝ) 1)
      (show ∀ t : ℝ, t ∉ Icc (1/4:ℝ) 1 → t^k*etaTwo t = 0 by
        intro t ht; rw [etaTwo_eq_zero_of_not_mem t ht,mul_zero])]
    rw [intervalIntegral.integral_of_le (by norm_num),integral_Icc_eq_integral_Ioc]
  rw [heq, ← intervalIntegral.integral_add_adjacent_intervals
    (hc.intervalIntegrable (1/4) (1/2)) (hc.intervalIntegrable (1/2) 1)]
  have hlo : (∫ t in (1/4:ℝ)..(1/2), t^k*etaTwo t) =
      4*∫ t in (1/4:ℝ)..(1/2), t^k*(Real.log 4+Real.log t) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le (by norm_num : (1/4:ℝ) ≤ 1/2)] at ht
    dsimp only
    rw [etaTwo_eq_lower t ht,Real.log_mul (by norm_num) (by linarith [ht.1] : t ≠ 0)]
    ring
  have hhi : (∫ t in (1/2:ℝ)..1, t^k*etaTwo t) =
      -4*∫ t in (1/2:ℝ)..1, t^k*(0+Real.log t) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le (by norm_num : (1/2:ℝ) ≤ 1)] at ht
    dsimp only
    rw [etaTwo_eq_upper t ht]
    ring
  rw [hlo,hhi,integral_power_log k (1/4) (1/2) (by norm_num) (by norm_num) (Real.log 4),
    integral_power_log k (1/2) 1 (by norm_num) (by norm_num) 0]
  simp
  ring

theorem etaTwo_first_moment : (∫ t : ℝ, t*etaTwo t) = (9/16 : ℝ) := by
  have h := etaTwo_moment_formula 1
  have heq : (fun t : ℝ => t*etaTwo t) = fun t => t^1*etaTwo t := by simp
  rw [heq,h]
  have h4 : Real.log (4 : ℝ) = 2*Real.log 2 := by
    rw [show (4:ℝ) = 2^2 by norm_num,Real.log_pow]; norm_num
  have hh : Real.log (1/2 : ℝ) = -Real.log 2 := by rw [one_div,Real.log_inv]
  have hq : Real.log (1/4 : ℝ) = -(2*Real.log 2) := by rw [one_div,Real.log_inv,h4]
  rw [hh,hq,h4,Real.log_one]
  norm_num
  ring

theorem etaTwo_second_moment : (∫ t : ℝ, t^2*etaTwo t) = (49/144 : ℝ) := by
  rw [etaTwo_moment_formula 2]
  have h4 : Real.log (4 : ℝ) = 2*Real.log 2 := by
    rw [show (4:ℝ) = 2^2 by norm_num,Real.log_pow]; norm_num
  have hh : Real.log (1/2 : ℝ) = -Real.log 2 := by rw [one_div,Real.log_inv]
  have hq : Real.log (1/4 : ℝ) = -(2*Real.log 2) := by rw [one_div,Real.log_inv,h4]
  rw [hh,hq,h4,Real.log_one]
  norm_num
  ring

end Helfgott

end

section

open MeasureTheory Set

namespace Helfgott

lemma phi_moment_integrable (k : ℕ) :
    IntegrableOn (fun t : ℝ => t^k*phi t) (Ioi (0 : ℝ)) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1/2)
    (s := ((k+2 : ℕ) : ℝ)) (by have hk := Nat.cast_nonneg (α := ℝ) (k+2); linarith : (-1 : ℝ) < ((k+2 : ℕ) : ℝ))
  convert! h using 1
  funext t
  rw [Real.rpow_natCast]
  unfold phi
  rw [pow_add]
  have he : -(1/2 : ℝ)*t^2 = -(t^2)/2 := by ring
  rw [he]
  ring

lemma gaussian_power_integral (k : ℕ) :
    (∫ t in Ioi (0 : ℝ), t^k*Real.exp (-(t^2)/2)) =
      (1/2 : ℝ)^(-(((k : ℝ)+1)/2))*(1/2)*Real.Gamma (((k : ℝ)+1)/2) := by
  have h := integral_rpow_mul_exp_neg_mul_rpow
    (p := (2 : ℝ)) (q := (k : ℝ)) (b := (1/2 : ℝ))
    (by norm_num) (by have hk := Nat.cast_nonneg (α := ℝ) k; linarith) (by norm_num)
  simp only [neg_div] at h ⊢
  rw [← h]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  dsimp only
  rw [Real.rpow_natCast,Real.rpow_two]
  congr 1 <;> ring

theorem phi_mass : (∫ t in Ioi (0 : ℝ), phi t) = Real.sqrt (Real.pi/2) := by
  have h := gaussian_power_integral 2
  norm_num only [Nat.cast_ofNat] at h
  have hg : Real.Gamma (3/2 : ℝ) = (1/2)*Real.sqrt Real.pi := by
    rw [show (3/2 : ℝ) = 1/2+1 by norm_num,
      Real.Gamma_add_one (by norm_num),Real.Gamma_one_half_eq]
  have he : (1/2 : ℝ)^(-(3/2 : ℝ)) = 2*Real.sqrt 2 := by
    rw [show (-(3/2 : ℝ)) = -1+ -(1/2 : ℝ) by norm_num,
      Real.rpow_add (by norm_num : (0 : ℝ) < 1/2),Real.rpow_neg_one,
      Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 1/2),← Real.sqrt_eq_rpow]
    norm_num
  change (∫ t in Ioi (0 : ℝ), t^2*Real.exp (-(t^2)/2)) = _
  rw [h]
  norm_num
  rw [hg,he]
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hn : Real.sqrt 2 ≠ 0 := (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne'
  field_simp
  nlinarith

theorem phi_first_moment : (∫ t in Ioi (0 : ℝ), t*phi t) = 2 := by
  have h := gaussian_power_integral 3
  have hg : Real.Gamma (2 : ℝ) = 1 := by
    rw [show (2 : ℝ) = 1+1 by norm_num,Real.Gamma_add_one (by norm_num),Real.Gamma_one]
    norm_num
  have he : (1/2 : ℝ)^(-(2 : ℝ)) = 4 := by
    rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 1/2),Real.rpow_two]
    norm_num
  have heq : (fun t : ℝ => t*phi t) = fun t => t^3*Real.exp (-(t^2)/2) := by
    funext t; unfold phi; ring
  rw [heq,h]
  norm_num [hg,he]

theorem phi_second_moment : (∫ t in Ioi (0 : ℝ), t^2*phi t) =
    3*Real.sqrt (Real.pi/2) := by
  have h := gaussian_power_integral 4
  have hg : Real.Gamma (5/2 : ℝ) = (3/4)*Real.sqrt Real.pi := by
    rw [show (5/2 : ℝ) = 3/2+1 by norm_num,Real.Gamma_add_one (by norm_num),
      show (3/2 : ℝ) = 1/2+1 by norm_num,Real.Gamma_add_one (by norm_num),Real.Gamma_one_half_eq]
    ring
  have he : (1/2 : ℝ)^(-(5/2 : ℝ)) = 4*Real.sqrt 2 := by
    rw [show (-(5/2 : ℝ)) = -2+ -(1/2 : ℝ) by norm_num,
      Real.rpow_add (by norm_num : (0 : ℝ) < 1/2),Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 1/2),
      Real.rpow_two,Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 1/2),← Real.sqrt_eq_rpow]
    norm_num
  have heq : (fun t : ℝ => t^2*phi t) = fun t => t^4*Real.exp (-(t^2)/2) := by
    funext t; unfold phi; ring
  rw [heq,h]
  norm_num
  rw [hg,he]
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hn : Real.sqrt 2 ≠ 0 := (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne'
  field_simp
  nlinarith

end Helfgott

end

section

open MeasureTheory Set

namespace Helfgott

lemma etaTwo_moment_pos_integral (k : ℕ) :
    (∫ t in Ioi (0 : ℝ), t^k*etaTwo t) = ∫ t : ℝ, t^k*etaTwo t := by
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro t ht
  simp [etaTwo,show ¬0 < t from ht]

lemma mellin_etaTwo_phi_moment (k : ℕ) :
    IntegrableOn (fun t => t^k*mellinConv etaTwo phi t) (Ioi (0 : ℝ)) ∧
    (∫ t in Ioi (0 : ℝ), t^k*mellinConv etaTwo phi t) =
      (∫ t : ℝ, t^k*etaTwo t)*(∫ t in Ioi (0 : ℝ), t^k*phi t) := by
  rw [← etaTwo_moment_pos_integral]
  apply mellin_moment _ _ etaTwo_continuous (by unfold phi; fun_prop)
    k (etaTwo_moment_integrable k).integrableOn (phi_moment_integrable k)
  · intro t ht; exact etaTwo_nonneg t
  · intro t ht; unfold phi; positivity

lemma scaled_moment_integral (F : ℝ → ℝ) (κ : ℝ) (hκ : 0 < κ) (k : ℕ) :
    (∫ t in Ioi (0 : ℝ), t^k*F (κ*t)) =
      (∫ t in Ioi (0 : ℝ), t^k*F t)/κ^(k+1) := by
  have heq : (fun t : ℝ => t^k*F (κ*t)) =
      fun t => (κ^k)⁻¹*((κ*t)^k*F (κ*t)) := by
    funext t
    rw [mul_pow]
    field_simp
  rw [heq,integral_const_mul,
    integral_comp_mul_left_Ioi (fun t => t^k*F t) 0 hκ]
  simp only [mul_zero,smul_eq_mul,pow_succ,div_eq_mul_inv,mul_inv_rev]
  ring

lemma etaStar_moment_integrable (k : ℕ) :
    IntegrableOn (fun t : ℝ => t^k*etaStar t) (Ioi (0 : ℝ)) := by
  have hmc := (mellin_etaTwo_phi_moment k).1
  have hs : IntegrableOn (fun t : ℝ => (49*t)^k*mellinConv etaTwo phi (49*t)) (Ioi (0 : ℝ)) := by
    apply (integrableOn_Ioi_comp_mul_left_iff
      (fun t => t^k*mellinConv etaTwo phi t) 0 (by norm_num : (0 : ℝ) < 49)).mpr
    simpa using hmc
  have hh := hs.const_mul ((49 : ℝ)^k)⁻¹
  have heq : (fun t : ℝ => t^k*etaStar t) =
      fun t => ((49 : ℝ)^k)⁻¹*((49*t)^k*mellinConv etaTwo phi (49*t)) := by
    funext t
    unfold etaStar
    rw [mul_pow]
    field_simp
  rw [heq]
  exact hh

lemma etaStar_moment_formula (k : ℕ) :
    (∫ t in Ioi (0 : ℝ), t^k*etaStar t) =
      ((∫ t : ℝ, t^k*etaTwo t)*(∫ t in Ioi (0 : ℝ), t^k*phi t))/(49 : ℝ)^(k+1) := by
  unfold etaStar
  rw [scaled_moment_integral _ 49 (by norm_num), (mellin_etaTwo_phi_moment k).2]

theorem etaStar_moments :
    (∫ t in Ioi (0 : ℝ), etaStar t) = Real.sqrt (Real.pi/2)/49 ∧
    (∫ t in Ioi (0 : ℝ), t*etaStar t) = (9/19208 : ℝ) ∧
    (∫ t in Ioi (0 : ℝ), t^2*etaStar t) = Real.sqrt (Real.pi/2)/115248 := by
  constructor
  · have h := etaStar_moment_formula 0
    simpa [etaTwo_mass,phi_mass] using h
  constructor
  · have h := etaStar_moment_formula 1
    norm_num [etaTwo_first_moment,phi_first_moment] at h
    simpa using h
  · rw [etaStar_moment_formula 2,etaTwo_second_moment,phi_second_moment]
    norm_num
    ring

end Helfgott

end

section

open MeasureTheory Set Filter
open scoped Convolution

namespace Helfgott

lemma etaCircle_le_one (t : ℝ) : etaCircle t ≤ 1 := by
  by_cases ht : t ∈ Icc (0 : ℝ) 2
  · have htn : 0 ≤ t*(2-t) := mul_nonneg ht.1 (by linarith [ht.2])
    have htl : t*(2-t) ≤ 1 := by nlinarith [sq_nonneg (t-1)]
    have hp : (t*(2-t))^3 ≤ 1 := by
      simpa using pow_le_pow_left₀ htn htl 3
    have he : Real.exp (-((t-1)^2)/2) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg (t-1)])
    rw [etaCircle,indicator_of_mem ht]
    have heq : t^3*(2-t)^3 = (t*(2-t))^3 := by ring
    rw [heq]
    exact mul_le_one₀ hp (by positivity) he
  · simp [etaCircle,ht]

lemma etaCircle_convolution_continuous :
    Continuous (fun ρ : ℝ => ∫ u : ℝ, etaCircle u*etaCircle (ρ-u)) := by
  have h := etaCircle_hasCompactSupport.continuous_convolution_right
    (L := ContinuousLinearMap.lsmul ℝ ℝ) etaCircle_integrable.locallyIntegrable etaCircle_continuous
  exact h

lemma etaCircle_convolution_nonneg (ρ : ℝ) :
    0 ≤ ∫ u : ℝ, etaCircle u*etaCircle (ρ-u) := by
  apply integral_nonneg
  intro u
  exact mul_nonneg (etaCircle_nonneg u) (etaCircle_nonneg (ρ-u))

lemma etaCircle_convolution_le (ρ : ℝ) :
    (∫ u : ℝ, etaCircle u*etaCircle (ρ-u)) ≤ ∫ u : ℝ, etaCircle u := by
  have hc : Continuous (fun u : ℝ => etaCircle u*etaCircle (ρ-u)) :=
    etaCircle_continuous.mul (etaCircle_continuous.comp (continuous_const.sub continuous_id))
  have hi : Integrable (fun u : ℝ => etaCircle u*etaCircle (ρ-u)) :=
    hc.integrable_of_hasCompactSupport etaCircle_hasCompactSupport.mul_right
  apply integral_mono hi etaCircle_integrable
  intro u
  exact mul_le_of_le_one_right (etaCircle_nonneg u) (etaCircle_le_one (ρ-u))

lemma main_convolution_integrable (ρ : ℝ) :
    IntegrableOn (fun w : ℝ => etaStar w*(∫ u : ℝ, etaCircle u*etaCircle (ρ-w-u)))
      (Ioi (0 : ℝ)) := by
  have hs : IntegrableOn etaStar (Ioi (0 : ℝ)) := by
    simpa using etaStar_moment_integrable 0
  have hc : Continuous (fun w : ℝ => ∫ u : ℝ, etaCircle u*etaCircle (ρ-w-u)) :=
    etaCircle_convolution_continuous.comp (continuous_const.sub continuous_id)
  apply (hs.mul_const (∫ u : ℝ, etaCircle u)).mono'
  · exact hs.aestronglyMeasurable.mul hc.aestronglyMeasurable
  · exact Eventually.of_forall (fun w => by
      have hn : 0 ≤ etaStar w := mellin_etaTwo_phi_nonneg (49*w)
      have hcn := etaCircle_convolution_nonneg (ρ-w)
      rw [Real.norm_of_nonneg (mul_nonneg hn hcn)]
      exact mul_le_mul_of_nonneg_left (etaCircle_convolution_le (ρ-w)) hn)


end Helfgott
end

section

open MeasureTheory Set

set_option backward.isDefEq.respectTransparency false

namespace Helfgott

lemma etaPlus_convolution_measurable :
    Measurable (fun ρ : ℝ => ∫ u : ℝ, etaPlus u*etaPlus (ρ-u)) := by
  have hm : Measurable (fun p : ℝ × ℝ => etaPlus p.2*etaPlus (p.1-p.2)) :=
    (etaPlus_measurable.comp measurable_snd).mul
      (etaPlus_measurable.comp (measurable_fst.sub measurable_snd))
  exact hm.stronglyMeasurable.integral_prod_right'.measurable

lemma etaCircle_convolution_square_mass_upper (ρ : ℝ) :
    (∫ u : ℝ, etaCircle u*etaCircle (ρ-u)) ≤ 641/1000 := by
  have hg2 := etaCircle_square_integrable
  have hgsq := hg2.comp_sub_left ρ
  have hi := integrable_mul_of_square_integrable etaCircle (fun u => etaCircle (ρ-u))
    etaCircle_continuous.measurable
    (etaCircle_continuous.measurable.comp (measurable_const.sub measurable_id)) hg2 hgsq
  calc
    _ ≤ ∫ u : ℝ, ((etaCircle u)^2+(etaCircle (ρ-u))^2)/2 := by
      apply integral_mono hi ((hg2.add hgsq).div_const 2)
      intro u
      have h := abs_mul_le_half_squares (etaCircle u) (etaCircle (ρ-u))
      exact (le_abs_self _).trans h
    _ = ∫ u : ℝ, (etaCircle u)^2 := by
      rw [integral_div]
      have ha := integral_add hg2 hgsq
      rw [ha,integral_sub_left_eq_self (fun u => (etaCircle u)^2) volume ρ]
      ring
    _ ≤ _ := etaCircle_square_integral_upper

lemma etaPlus_convolution_abs_le_one (ρ : ℝ) :
    |∫ u : ℝ, etaPlus u*etaPlus (ρ-u)| ≤ 1 := by
  have hd := (etaPlus_convolution_approximation ρ).2
  have ht := abs_add_le
    ((∫ u : ℝ, etaPlus u*etaPlus (ρ-u))-(∫ u : ℝ, etaCircle u*etaCircle (ρ-u)))
    (∫ u : ℝ, etaCircle u*etaCircle (ρ-u))
  rw [sub_add_cancel,abs_of_nonneg (etaCircle_convolution_nonneg ρ)] at ht
  linarith [etaCircle_convolution_square_mass_upper ρ]

lemma actual_main_convolution_integrable (ρ : ℝ) :
    IntegrableOn (fun w : ℝ => etaStar w*(∫ u : ℝ, etaPlus u*etaPlus (ρ-w-u)))
      (Ioi (0 : ℝ)) := by
  have hs : IntegrableOn etaStar (Ioi (0 : ℝ)) := by
    simpa using etaStar_moment_integrable 0
  have hm : Measurable (fun w : ℝ => ∫ u : ℝ, etaPlus u*etaPlus (ρ-w-u)) :=
    etaPlus_convolution_measurable.comp (measurable_const.sub measurable_id)
  apply hs.mono' (hs.aestronglyMeasurable.mul hm.aestronglyMeasurable)
  exact ae_of_all _ (fun w => by
    have hn : 0 ≤ etaStar w := mellin_etaTwo_phi_nonneg (49*w)
    simp only [Pi.mul_apply,Real.norm_eq_abs,abs_mul,abs_of_nonneg hn]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left
      (etaPlus_convolution_abs_le_one (ρ-w)) hn)


end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set
namespace Helfgott
lemma abs_mul_le_unequal_squares_tight (x y : ℝ) : |x*y| ≤ x^2/64000+16000*y^2 := by
  apply abs_le.mpr
  constructor
  · nlinarith [sq_nonneg (x+32000*y)]
  · nlinarith [sq_nonneg (x-32000*y)]

theorem convolution_difference_error_bound_tight (f g : ℝ → ℝ)
    (hf : Measurable f) (hg : Measurable g)
    (hg2 : Integrable (fun u => (g u)^2))
    (hd2 : Integrable (fun u => (f u-g u)^2))
    (hgb : (∫ u : ℝ, (g u)^2) ≤ 641/1000)
    (hdb : (∫ u : ℝ, (f u-g u)^2) ≤ 1/1568000000)
    (ρ : ℝ) :
    Integrable (fun u => f u*f (ρ-u)) ∧
    |(∫ u : ℝ, f u*f (ρ-u))-(∫ u : ℝ, g u*g (ρ-u))| ≤ 21/500000 := by
  let d : ℝ → ℝ := fun u => f u-g u
  have hd : Measurable d := hf.sub hg
  have hd2' : Integrable (fun u => (d u)^2) := hd2
  have hdb' : (∫ u : ℝ, (d u)^2) ≤ 1/1568000000 := hdb
  have hgm : Measurable (fun u => g (ρ-u)) := hg.comp (measurable_const.sub measurable_id)
  have hdm : Measurable (fun u => d (ρ-u)) := hd.comp (measurable_const.sub measurable_id)
  have hgsq := hg2.comp_sub_left ρ
  have hdsq := hd2'.comp_sub_left ρ
  have hiA := integrable_mul_of_square_integrable g (fun u => g (ρ-u)) hg hgm hg2 hgsq
  have hiB := integrable_mul_of_square_integrable d (fun u => g (ρ-u)) hd hgm hd2' hgsq
  have hiC := integrable_mul_of_square_integrable g (fun u => d (ρ-u)) hg hdm hg2 hdsq
  have hiD := integrable_mul_of_square_integrable d (fun u => d (ρ-u)) hd hdm hd2' hdsq
  have hBM : (∫ u : ℝ, |d u*g (ρ-u)|) ≤ 41/2000000 := by
    calc
      _ ≤ ∫ u : ℝ, (g (ρ-u))^2/64000+16000*(d u)^2 := by
        apply integral_mono hiB.abs ((hgsq.div_const 64000).add (hd2'.const_mul 16000))
        intro u
        simpa only [mul_comm,Pi.add_apply] using abs_mul_le_unequal_squares_tight (g (ρ-u)) (d u)
      _ = (∫ u : ℝ, (g u)^2)/64000+16000*(∫ u : ℝ, (d u)^2) := by
        rw [integral_add (hgsq.div_const 64000) (hd2'.const_mul 16000),integral_div,
          integral_const_mul,integral_sub_left_eq_self (fun u => (g u)^2) volume ρ]
      _ ≤ _ := by linarith
  have hCM : (∫ u : ℝ, |g u*d (ρ-u)|) ≤ 41/2000000 := by
    calc
      _ ≤ ∫ u : ℝ, (g u)^2/64000+16000*(d (ρ-u))^2 :=
        integral_mono hiC.abs ((hg2.div_const 64000).add (hdsq.const_mul 16000))
          (fun u => abs_mul_le_unequal_squares_tight (g u) (d (ρ-u)))
      _ = (∫ u : ℝ, (g u)^2)/64000+16000*(∫ u : ℝ, (d u)^2) := by
        rw [integral_add (hg2.div_const 64000) (hdsq.const_mul 16000),integral_div,
          integral_const_mul,integral_sub_left_eq_self (fun u => (d u)^2) volume ρ]
      _ ≤ _ := by linarith
  have hDM : (∫ u : ℝ, |d u*d (ρ-u)|) ≤ 1/1568000000 := by
    calc
      _ ≤ ∫ u : ℝ, ((d u)^2+(d (ρ-u))^2)/2 :=
        integral_mono hiD.abs ((hd2'.add hdsq).div_const 2)
          (fun u => abs_mul_le_half_squares (d u) (d (ρ-u)))
      _ = (∫ u : ℝ, (d u)^2) := by
        rw [integral_div,integral_add hd2' hdsq,
          integral_sub_left_eq_self (fun u => (d u)^2) volume ρ]
        ring
      _ ≤ _ := hdb'
  have heq : (fun u => f u*f (ρ-u)) =
      (fun u => g u*g (ρ-u)+d u*g (ρ-u)+g u*d (ρ-u)+d u*d (ρ-u)) := by
    funext u
    dsimp only [d]
    ring
  have hiF : Integrable (fun u => f u*f (ρ-u)) := by
    rw [heq]
    exact ((hiA.add hiB).add hiC).add hiD
  refine ⟨hiF,?_⟩
  have hEA : (∫ u : ℝ, f u*f (ρ-u))-(∫ u : ℝ, g u*g (ρ-u)) =
      (∫ u : ℝ, d u*g (ρ-u))+(∫ u : ℝ, g u*d (ρ-u))+(∫ u : ℝ, d u*d (ρ-u)) := by
    have e1 := integral_add hiA hiB
    have e2 := integral_add (hiA.add hiB) hiC
    have e3 := integral_add ((hiA.add hiB).add hiC) hiD
    simp only [Pi.add_apply] at e1 e2 e3
    rw [heq,e3,e2,e1]
    ring
  rw [hEA]
  have hnB := norm_integral_le_integral_norm (μ := volume) (fun u => d u*g (ρ-u))
  have hnC := norm_integral_le_integral_norm (μ := volume) (fun u => g u*d (ρ-u))
  have hnD := norm_integral_le_integral_norm (μ := volume) (fun u => d u*d (ρ-u))
  simp only [Real.norm_eq_abs] at hnB hnC hnD
  have ht1 := abs_add_le (∫ u : ℝ, d u*g (ρ-u)) (∫ u : ℝ, g u*d (ρ-u))
  have ht2 := abs_add_le ((∫ u : ℝ, d u*g (ρ-u))+(∫ u : ℝ, g u*d (ρ-u)))
    (∫ u : ℝ, d u*d (ρ-u))
  linarith

theorem etaPlus_convolution_approximation_tight (ρ : ℝ) :
    Integrable (fun u : ℝ => etaPlus u*etaPlus (ρ-u)) ∧
    |(∫ u : ℝ, etaPlus u*etaPlus (ρ-u))-
      (∫ u : ℝ, etaCircle u*etaCircle (ρ-u))| ≤ 21/500000 :=
  convolution_difference_error_bound_tight etaPlus etaCircle etaPlus_measurable
    etaCircle_continuous.measurable etaCircle_square_integrable etaPlus_approx_square_integrable
    etaCircle_square_integral_upper etaPlus_approx_l2_square_le_tight ρ

lemma actual_main_convolution_approximation_tight (ρ : ℝ) :
    |(∫ w in Ioi (0 : ℝ), etaStar w*(∫ u : ℝ, etaPlus u*etaPlus (ρ-w-u)))-
      (∫ w in Ioi (0 : ℝ), etaStar w*(∫ u : ℝ, etaCircle u*etaCircle (ρ-w-u)))| ≤
        (21/500000 : ℝ)*(Real.sqrt (Real.pi/2)/49) := by
  let f : ℝ → ℝ := fun w => etaStar w*(∫ u : ℝ, etaPlus u*etaPlus (ρ-w-u))
  let g : ℝ → ℝ := fun w => etaStar w*(∫ u : ℝ, etaCircle u*etaCircle (ρ-w-u))
  have hf : IntegrableOn f (Ioi (0 : ℝ)) := actual_main_convolution_integrable ρ
  have hg : IntegrableOn g (Ioi (0 : ℝ)) := main_convolution_integrable ρ
  have hs : IntegrableOn etaStar (Ioi (0 : ℝ)) := by
    simpa using etaStar_moment_integrable 0
  have hd : IntegrableOn (fun w => f w-g w) (Ioi (0 : ℝ)) := hf.sub hg
  have hb (w : ℝ) : |f w-g w| ≤ etaStar w*(21/500000 : ℝ) := by
    have hn : 0 ≤ etaStar w := mellin_etaTwo_phi_nonneg (49*w)
    have he : f w-g w = etaStar w*((∫ u : ℝ, etaPlus u*etaPlus (ρ-w-u))-
      (∫ u : ℝ, etaCircle u*etaCircle (ρ-w-u))) := by dsimp [f,g]; ring
    rw [he,abs_mul,abs_of_nonneg hn]
    exact mul_le_mul_of_nonneg_left (etaPlus_convolution_approximation_tight (ρ-w)).2 hn
  change |(∫ w in Ioi (0 : ℝ), f w)-(∫ w in Ioi (0 : ℝ), g w)| ≤ _
  calc
    _ = |∫ w in Ioi (0 : ℝ), f w-g w| := by rw [integral_sub hf hg]
    _ ≤ ∫ w in Ioi (0 : ℝ), |f w-g w| := by
      simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (fun w => f w-g w)
    _ ≤ ∫ w in Ioi (0 : ℝ), etaStar w*(21/500000 : ℝ) :=
      integral_mono hd.abs (hs.mul_const (21/500000 : ℝ)) hb
    _ = _ := by rw [integral_mul_const,etaStar_moments.1]; ring

theorem etaPlus_etaStar_main_convolution_lower_tight :
    IntegrableOn (fun w : ℝ => etaStar w*(∫ u : ℝ,
      etaPlus u*etaPlus (2+9/(196*Real.sqrt (2*Real.pi))-w-u))) (Ioi (0 : ℝ)) ∧
    (40107/50000 : ℝ)/49 ≤
      ∫ w in Ioi (0 : ℝ), etaStar w*(∫ u : ℝ,
        etaPlus u*etaPlus (2+9/(196*Real.sqrt (2*Real.pi))-w-u)) := by
  refine ⟨actual_main_convolution_integrable _,?_⟩
  have hd := (abs_le.mp (actual_main_convolution_approximation_tight
    (2+9/(196*Real.sqrt (2*Real.pi))))).1
  have hc := etaCircle_etaStar_main_convolution_lower_tight
  have hA : Real.sqrt (Real.pi/2) ≤ 127/100 := by
    have hs := Real.sq_sqrt (by positivity : (0 : ℝ) ≤ Real.pi/2)
    have hn := Real.sqrt_nonneg (Real.pi/2)
    nlinarith [Real.pi_lt_d2]
  have hnum : (21/500000 : ℝ)*(Real.sqrt (Real.pi/2)/49) ≤ (6/100000 : ℝ)/49 := by
    nlinarith [hA]
  linarith

end Helfgott
end
open MeasureTheory Helfgott Set
theorem solution :
    IntegrableOn (fun w : ℝ => etaStar w*(∫ u : ℝ,
      etaPlus u*etaPlus (2+9/(196*Real.sqrt (2*Real.pi))-w-u))) (Ioi (0 : ℝ)) ∧
    (40107/50000 : ℝ)/49 ≤
      ∫ w in Ioi (0 : ℝ), etaStar w*(∫ u : ℝ,
        etaPlus u*etaPlus (2+9/(196*Real.sqrt (2*Real.pi))-w-u)) := etaPlus_etaStar_main_convolution_lower_tight
#print axioms solution
