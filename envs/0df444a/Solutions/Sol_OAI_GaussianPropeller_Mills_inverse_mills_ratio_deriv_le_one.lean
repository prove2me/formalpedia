-- Prove2me | solution 1 for OAI.GaussianPropeller.Mills.inverse_mills_ratio_deriv_le_one
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-19T00:18:54.02905+00:00
-- url     : https://prove2.me/submissions/5e645966-c49b-4152-bced-88d8bbba3c88

import Mathlib
import Definitions.Def_HairerSPDE_CameronMartin
import Definitions.Def_OAIQWGP000

section
-- module Solutions.OAIQW_GaussianPropeller.OneCell
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

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
  convert (((hasDerivAt_pow 2 x).neg.div_const 2).exp) using 1 <;> first | rfl | ring1 | (norm_num <;> ring1)

lemma tendsto_density : Tendsto density atTop (𝓝 0) := by
  apply Real.tendsto_exp_atBot.comp
  convert (tendsto_pow_atTop two_ne_zero).const_mul_atTop_of_neg (by norm_num : (-(1/2:ℝ)) < 0) using 1
  ext x
  ring

lemma tail_first_moment (a : ℝ) : ∫ x in Ioi a, x*density x = density a := by
  have hd (x : ℝ) : HasDerivAt (fun x => -density x) (x*density x) x := by
    convert (hasDerivAt_density x).neg using 1 <;> first | rfl | ring1
  have ht : Tendsto (fun x => -density x) atTop (𝓝 (-0)) := tendsto_density.neg
  simpa only [neg_zero, zero_sub, neg_neg] using
    integral_Ioi_of_hasDerivAt_of_tendsto' (fun x _ => hd x)
      mul_density_integrable.integrableOn ht

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

end GaussianPropeller.OneCell

end OAI
end

section
-- module Solutions.OAIQW_GaussianPropeller.Mills
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

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

lemma G_le_one_core (x : ℝ) : G x ≤ 1 := by
  have hi : Integrable (fun t : ℝ => (t-lambda x)^2*density t) volume := by
    have hh := (sq_density_integrable.sub (mul_density_integrable.const_mul (2*lambda x))).add
      (density_integrable.const_mul (lambda x^2))
    convert! hh using 1
    ext t
    simp only [Pi.add_apply, Pi.sub_apply]
    ring
  have hz : 0 ≤ ∫ t in Ioi x, (t-lambda x)^2*density t := by
    apply integral_nonneg
    intro t
    exact mul_nonneg (sq_nonneg _) (Real.exp_pos _).le
  have heq : (fun t : ℝ => (t-lambda x)^2*density t) =
      fun t => (t^2*density t-2*lambda x*(t*density t))+lambda x^2*density t := by
    funext t
    ring
  rw [heq] at hz
  have h₁ : IntegrableOn (fun t : ℝ => t^2*density t-2*lambda x*(t*density t)) (Ioi x) :=
    (sq_density_integrable.sub (mul_density_integrable.const_mul (2*lambda x))).integrableOn
  have h₂ : IntegrableOn (fun t : ℝ => lambda x^2*density t) (Ioi x) :=
    (density_integrable.const_mul (lambda x^2)).integrableOn
  rw [integral_add h₁ h₂, integral_sub sq_density_integrable.integrableOn
    (show IntegrableOn (fun t : ℝ => 2*lambda x*(t*density t)) (Ioi x) volume from
      (mul_density_integrable.const_mul (2*lambda x)).integrableOn),
    integral_const_mul, integral_const_mul, tail_first_moment, tail_second_moment] at hz
  change 0 ≤ x*density x+tail x-2*lambda x*density x+lambda x^2*tail x at hz
  have he : lambda x*tail x=density x := by
    rw [lambda, div_mul_cancel₀ _ (tail_pos x).ne']
  have ht : tail x*(1-G x) ≥ 0 := by
    dsimp [G]
    nlinarith only [hz,he, congrArg (fun t : ℝ => lambda x*t) he,
      congrArg (fun t : ℝ => x*t) he]
  have h := (mul_nonneg_iff_of_pos_left (tail_pos x)).mp ht
  linarith only [h]

theorem inverse_mills_ratio_deriv_le_one_oai (x : ℝ) :
    (Real.exp (-x^2/2) / ∫ t in Set.Ioi x, Real.exp (-t^2/2)) *
      (Real.exp (-x^2/2) / (∫ t in Set.Ioi x, Real.exp (-t^2/2)) - x) ≤ 1 :=
  G_le_one_core x

end GaussianPropeller.Mills

end OAI
end

theorem solution : type_of% @OAI.GaussianPropeller.Mills.inverse_mills_ratio_deriv_le_one_oai := @OAI.GaussianPropeller.Mills.inverse_mills_ratio_deriv_le_one_oai
