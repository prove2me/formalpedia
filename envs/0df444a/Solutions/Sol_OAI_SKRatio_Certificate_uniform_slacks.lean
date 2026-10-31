-- Prove2me | solution 1 for OAI.SKRatio.Certificate.uniform_slacks
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T01:14:49.197819+00:00
-- url     : https://prove2.me/submissions/a62197c8-f48c-4ca8-96e3-d3f6d94719a0

import Mathlib
import Definitions.Def_OAIQ024S016
import Theorems.Thm_OAI_SKRatio_Certificate_Data_J3K0_integral_bound
import Theorems.Thm_OAI_SKRatio_Certificate_Data_J3K1_checks
import Theorems.Thm_OAI_SKRatio_Certificate_Data_J3K2_checks
import Theorems.Thm_OAI_SKRatio_Certificate_Data_J3K3_checks
import Theorems.Thm_OAI_SKRatio_Certificate_Data_J3K4_integral_bound
import Theorems.Thm_OAI_SKRatio_Certificate_Data_J3K5_checks
import Theorems.Thm_OAI_SKRatio_Certificate_Data_J3K6_checks
import Theorems.Thm_OAI_SKRatio_Certificate_Data_J3K7_integral_bound
import Theorems.Thm_OAI_SKRatio_Certificate_valid0
import Theorems.Thm_OAI_SKRatio_Certificate_valid1
import Theorems.Thm_OAI_SKRatio_Certificate_valid2
import Theorems.Thm_OAI_SKRatio_Certificate_valid4

section
-- module Solutions.OAIQ024_SK.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {c : Prop} {_ : Decidable c} {a b : α} (h : c) :
    (if c then a else b) = a := if_pos h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Calculus_PlusSpin
attribute [-instance] _root_.OAI.SKRatio.Observation.History.historyTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators Topology Matrix
open ContinuousLinearMap
namespace SKRatio.Calculus

open Real Set

lemma hasDerivAt_tanh (y : ℝ) : HasDerivAt tanh (1 - tanh y ^ 2) y := by
  convert! (Real.hasDerivAt_sinh y).div (Real.hasDerivAt_cosh y) (cosh_pos y).ne' using 1
  · ext x
    exact tanh_eq_sinh_div_cosh x
  · rw [tanh_eq_sinh_div_cosh]
    field_simp

end SKRatio.Calculus
end
end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Gaussian_Planted
attribute [-instance] _root_.OAI.SKRatio.Observation.History.historyBorel _root_.OAI.SKRatio.Observation.History.historyMeasurable _root_.OAI.SKRatio.Observation.History.historyTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Topology ENNReal NNReal
open MeasureTheory ProbabilityTheory Real Filter
namespace SKRatio.Planted
open Calculus
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

lemma gaussianReal_tilt (μ : ℝ) (v : ℝ≥0) (a : ℝ) :
    (gaussianReal μ v).withDensity
      (fun z => ENNReal.ofReal (exp (a*z-(a*μ+(v:ℝ)*a^2/2)))) =
      gaussianReal (μ+(v:ℝ)*a) v := by
  by_cases hv : v=0
  · subst v
    simp [dirac_withDensity]
  have hvr : (v:ℝ) ≠ 0 := by exact_mod_cast hv
  rw [gaussianReal_of_var_ne_zero _ hv,gaussianReal_of_var_ne_zero _ hv,
    ←withDensity_mul volume (measurable_gaussianPDF _ _) (by fun_prop)]
  congr 1
  funext z
  simp only [Pi.mul_apply,gaussianPDF_def,←ENNReal.ofReal_mul (gaussianPDFReal_nonneg _ _ _)]
  congr 1
  simp only [gaussianPDFReal_def,mul_assoc,←exp_add]
  congr 2
  field_simp
  ring

end SKRatio.Planted

end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Variational_ScalarKernel
attribute [-instance] _root_.OAI.SKRatio.Observation.History.historyBorel _root_.OAI.SKRatio.Observation.History.historyMeasurable _root_.OAI.SKRatio.Observation.History.historySecondCountable _root_.OAI.SKRatio.Observation.History.historyTopology
attribute [-simp] _root_.OAI.SKRatio.Planted.compactWeight_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Real
namespace SKRatio.Scalar

lemma v_pos (h : ℝ) : 0 < v h := sub_pos.mpr (tanh_sq_lt_one h)
lemma v_le_one (h : ℝ) : v h ≤ 1 := by dsimp [v]; nlinarith [sq_nonneg (m h)]
lemma v_factor (h : ℝ) : v h = w h * (1+m h) := by unfold v w; ring
lemma kernel_nonneg (h t : ℝ) : 0 ≤ kernel h t :=
  div_nonneg (mul_nonneg (v_pos h).le (v_pos t).le) (add_pos (w_pos h) (w_pos t)).le
lemma kernel_diag (h : ℝ) : kernel h h = (1+m h)*v h/2 := by
  unfold kernel
  nth_rw 1 [v_factor h]
  have hw := (w_pos h).ne'
  field_simp
  ring

lemma kernel_diag_le_one (h : ℝ) : kernel h h ≤ 1 := by
  rw [kernel_diag]
  have hm := (m_bounds h).2.le
  have hv := v_le_one h
  have hv0 := (v_pos h).le
  nlinarith [(mul_le_mul_of_nonneg_right (show 1+m h ≤ 2 by linarith) hv0)]

lemma residual_identity (h t : ℝ) :
    kernel h t - (3/2)*g h*g t = kernel h t*q h*q t := by
  have hht := (add_pos (w_pos h) (w_pos t)).ne'
  have hh : w h+3/4 ≠ 0 := by linarith [w_pos h]
  have ht : w t+3/4 ≠ 0 := by linarith [w_pos t]
  unfold kernel g q
  have hh4 : w h*4+3 ≠ 0 := by linarith [w_pos h]
  have ht4 : w t*4+3 ≠ 0 := by linarith [w_pos t]
  field_simp [hht,hh4,ht4]
  ring

lemma rho_eq (h : ℝ) : rho h = kernel h h * q h^2 := by
  have hh := residual_identity h h
  rw [kernel_diag] at hh
  unfold rho
  rw [kernel_diag]
  nlinarith only [hh]

lemma rho_nonneg (h : ℝ) : 0 ≤ rho h := by
  rw [rho_eq]
  exact mul_nonneg (kernel_nonneg h h) (sq_nonneg (q h))

lemma rho_le_one (h : ℝ) : rho h ≤ 1 := by
  have hi := kernel_diag_le_one h
  rw [kernel_diag] at hi
  unfold rho
  nlinarith [sq_nonneg (g h)]

lemma abs_g_le_one (h : ℝ) : |g h| ≤ 1 := by
  have hi := kernel_diag_le_one h
  rw [kernel_diag] at hi
  have hr := rho_nonneg h
  unfold rho at hr
  rw [abs_le]
  constructor <;> nlinarith [sq_nonneg (g h+1),sq_nonneg (g h-1)]

lemma continuous_m : Continuous m := by
  unfold m
  simp_rw [tanh_eq_sinh_div_cosh]
  exact Continuous.div Real.continuous_sinh Real.continuous_cosh (fun h => ne_of_gt (Real.cosh_pos h))
lemma continuous_v : Continuous v := continuous_const.sub (continuous_m.pow 2)
lemma continuous_w : Continuous w := continuous_const.sub continuous_m
lemma continuous_g : Continuous g := by
  apply continuous_v.div (continuous_w.add continuous_const)
  intro h
  change w h+3/4 ≠ 0
  linarith [w_pos h]
lemma continuous_rho : Continuous rho :=
  (((continuous_const.add continuous_m).mul continuous_v).div_const 2).sub
    ((continuous_g.pow 2).const_mul (3/2))

section Integration
variable {μ : Measure ℝ} [IsProbabilityMeasure μ]

lemma memLp_g : MemLp g 2 μ := by
  apply (memLp_const (1:ℝ)).of_le_mul continuous_g.aestronglyMeasurable
    (c := (1:ℝ))
  exact Filter.Eventually.of_forall (fun h => by simpa using abs_g_le_one h)

lemma integrable_rho : Integrable rho μ := by
  exact ((integrable_const (1:ℝ)).mono' continuous_rho.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun h => by
      simpa only [Real.norm_eq_abs,abs_of_nonneg (rho_nonneg h)] using rho_le_one h)))

end Integration
end SKRatio.Scalar

end
end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Variational_ScalarMoments
attribute [-instance] _root_.OAI.SKRatio.Observation.History.historyBorel _root_.OAI.SKRatio.Observation.History.historyMeasurable _root_.OAI.SKRatio.Observation.History.historySecondCountable _root_.OAI.SKRatio.Observation.History.historyTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Topology NNReal ENNReal
open MeasureTheory ProbabilityTheory Real
namespace SKRatio.Scalar

lemma memLp_m {μ : Measure ℝ} [IsFiniteMeasure μ] {p : ENNReal} : MemLp m p μ := by
  apply MemLp.of_bound continuous_m.aestronglyMeasurable 1
  exact ae_of_all _ (fun h => by simpa only [Real.norm_eq_abs] using (abs_lt.mpr (m_bounds h)).le)

lemma memLp_v {μ : Measure ℝ} [IsFiniteMeasure μ] {p : ENNReal} : MemLp v p μ := by
  apply MemLp.of_bound continuous_v.aestronglyMeasurable 1
  exact ae_of_all _ (fun h => by simpa only [Real.norm_eq_abs,abs_of_nonneg (v_pos h).le] using v_le_one h)

lemma memLp_mv {μ : Measure ℝ} [IsFiniteMeasure μ] {p : ENNReal} :
    MemLp (fun h => m h*v h) p μ := by
  apply MemLp.of_bound (continuous_m.mul continuous_v).aestronglyMeasurable 1
  apply ae_of_all
  intro h
  change |m h*v h| ≤ 1
  rw [abs_mul,abs_of_nonneg (v_pos h).le]
  exact (mul_le_mul (abs_lt.mpr (m_bounds h)).le (v_le_one h)
    (v_pos h).le (by norm_num : (0:ℝ) ≤ 1)).trans_eq (by ring)

lemma tilted_integral (β : ℝ) (f : ℝ → ℝ) :
    ∫ h, f h ∂fieldLaw β =
      ∫ h, exp (h-β^2/2)*f h ∂gaussianReal 0 (variance β) := by
  have he := Planted.gaussianReal_tilt 0 (variance β) 1
  simp only [one_mul,mul_zero,one_pow,mul_one,zero_add,variance_coe] at he
  rw [fieldLaw,←he,integral_withDensity_eq_integral_toReal_smul (by fun_prop)
    (ae_of_all _ (fun h => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (exp_pos _).le,smul_eq_mul]

lemma centered_gaussian_integral_neg (s : ℝ≥0) (f : ℝ → ℝ) :
    ∫ h, f (-h) ∂gaussianReal 0 s = ∫ h, f h ∂gaussianReal 0 s := by
  have hp : MeasurePreserving (fun h : ℝ => -h) (gaussianReal 0 s) (gaussianReal 0 s) :=
    ⟨measurable_neg,by simpa using (gaussianReal_map_neg (μ := 0) (v := s))⟩
  exact hp.integral_comp (Homeomorph.neg ℝ).measurableEmbedding f

lemma tilted_odd_integrand (h : ℝ) :
    exp h*(m h-m h^2) = -(exp (-h)*(m (-h)-m (-h)^2)) := by
  have hh := Calculus.exp_two_mul_one_sub_tanh h
  have hp := exp_pos h
  simp only [show 2*h=h+h by ring,exp_add,m,tanh_neg,neg_sq] at hh ⊢
  rw [exp_neg]
  field_simp
  nlinarith only [hh, mul_eq_mul_right_iff.mp (congrArg (fun t : ℝ => t*tanh h) hh)]

theorem sign_identity (β : ℝ) (F : ℝ → ℝ) (hF : Measurable F)
    (heven : ∀ h, F (-h) = F h) {C : ℝ} (hC : ∀ h, |F h| ≤ C) :
    ∫ h, m h*F h ∂fieldLaw β = ∫ h, m h^2*F h ∂fieldLaw β := by
  have hFlp : MemLp F 2 (fieldLaw β) := MemLp.of_bound hF.aestronglyMeasurable C
    (ae_of_all _ (fun h => by simpa only [Real.norm_eq_abs] using hC h))
  have h1 : Integrable (fun h => m h*F h) (fieldLaw β) := (memLp_m (p := 2)).integrable_mul hFlp
  have hm2 : MemLp (fun h => m h^2) 2 (fieldLaw β) := by
    apply MemLp.of_bound (continuous_m.pow 2).aestronglyMeasurable 1
    exact ae_of_all _ (fun h => by
      change |m h^2| ≤ 1
      rw [abs_of_nonneg (sq_nonneg _)]
      exact (tanh_sq_lt_one h).le)
  have h2 : Integrable (fun h => m h^2*F h) (fieldLaw β) := hm2.integrable_mul hFlp
  suffices hz : ∫ h, m h*F h-m h^2*F h ∂fieldLaw β = 0 by
    rw [integral_sub h1 h2] at hz
    linarith
  rw [tilted_integral]
  let A : ℝ → ℝ := fun h => exp (h-β^2/2)*(m h*F h-m h^2*F h)
  have ha (h : ℝ) : A (-h) = -A h := by
    have hh := tilted_odd_integrand h
    dsimp [A]
    rw [heven h,exp_sub,exp_sub]
    have hd := (exp_pos (β^2/2)).ne'
    apply (mul_right_cancel₀ hd)
    field_simp
    have hhh := congrArg (fun t : ℝ => t*F h) hh
    nlinarith only [hhh]
  have hi := centered_gaussian_integral_neg (variance β) A
  simp_rw [ha,integral_neg] at hi
  change ∫ h, A h ∂gaussianReal 0 (variance β) = 0
  linarith

lemma mean_m_eq_mean_m_sq (β : ℝ) :
    ∫ h, m h ∂fieldLaw β = ∫ h, m h^2 ∂fieldLaw β := by
  simpa using sign_identity β (fun _ => (1:ℝ)) measurable_const (fun _ => rfl)
    (C := 1) (fun _ => by norm_num)

lemma mean_mv_eq_mean_m_sq_v (β : ℝ) :
    ∫ h, m h*v h ∂fieldLaw β = ∫ h, m h^2*v h ∂fieldLaw β := by
  apply sign_identity β v continuous_v.measurable
  · intro h
    simp [v,m,tanh_neg]
  · intro h
    simpa only [abs_of_nonneg (v_pos h).le] using v_le_one h

lemma memLp_field (β : ℝ) : MemLp (fun h : ℝ => h) 2 (fieldLaw β) :=
  memLp_id_gaussianReal 2

lemma memLp_field_v (β : ℝ) : MemLp (fun h : ℝ => h*v h) 2 (fieldLaw β) := by
  apply (memLp_field β).of_le_mul
    (continuous_id.mul continuous_v).aestronglyMeasurable (c := (1:ℝ))
  apply ae_of_all
  intro h
  change |h*v h| ≤ 1*|h|
  simp only [abs_mul,one_mul,abs_of_nonneg (v_pos h).le]
  exact mul_le_of_le_one_right (abs_nonneg _) (v_le_one h)

lemma multiplier_pos (h : ℝ) : 4464/10000 ≤ multiplier h := by
  unfold multiplier
  nlinarith [sq_nonneg (m h-12/100)]

lemma multiplier_le (h : ℝ) : multiplier h ≤ 76/100 := by
  unfold multiplier
  have hm := m_bounds h
  have hs := (tanh_sq_lt_one h).le
  change m h^2 ≤ 1 at hs
  nlinarith

lemma continuous_multiplier : Continuous multiplier := by
  exact (continuous_const.add ((continuous_m.pow 2).const_mul (1/4))).sub
    (continuous_m.const_mul (6/100))

lemma mean_multiplier (β : ℝ) :
    ∫ h, multiplier h ∂fieldLaw β = 64/100-(19/100)*(∫ h, v h ∂fieldLaw β) := by
  have hmI : Integrable m (fieldLaw β) := memLp_m.integrable (by norm_num : (1:ENNReal) ≤ 2)
  have hm2I : Integrable (fun h => m h^2) (fieldLaw β) := memLp_m.integrable_sq
  have hv : (∫ h, v h ∂fieldLaw β) = 1-∫ h, m h^2 ∂fieldLaw β := by
    unfold v
    rw [integral_sub (integrable_const 1) hm2I,integral_const]
    simp
  have hsum : Integrable (fun h => 45/100+(1/4)*m h^2) (fieldLaw β) := by
    exact (integrable_const (45/100:ℝ)).add (hm2I.const_mul (1/4:ℝ))
  unfold multiplier
  rw [integral_sub hsum (hmI.const_mul _),
    integral_add (integrable_const _) (hm2I.const_mul _),integral_const_mul,integral_const_mul,
    integral_const,mean_m_eq_mean_m_sq,hv]
  simp only [probReal_univ,smul_eq_mul,one_mul]
  ring

end SKRatio.Scalar

end
end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Certificates_CertifiedGaussian
attribute [-instance] _root_.OAI.SKRatio.Observation.History.historyBorel _root_.OAI.SKRatio.Observation.History.historyMeasurable _root_.OAI.SKRatio.Observation.History.historySecondCountable _root_.OAI.SKRatio.Observation.History.historyTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Topology ENNReal NNReal
open Real Set MeasureTheory ProbabilityTheory
namespace SKRatio.Certificate

lemma gaussian_weight_factor (x : ℝ) :
    gaussianWeight x = exp ((-(1/4:ℝ)*x^2))*exp ((-(1/4:ℝ)*x^2)) := by
  unfold gaussianWeight
  rw [←exp_add]
  congr 1
  ring

lemma polynomial_weight_bound (x : ℝ) :
    (1+x^2)*exp ((-(1/4:ℝ)*x^2)) ≤ 4 := by
  have h := add_one_le_exp ((1/4:ℝ)*x^2)
  have h' : 1+x^2 ≤ 4*exp ((1/4:ℝ)*x^2) := by linarith
  have hm := mul_le_mul_of_nonneg_right h' (exp_pos ((-(1/4:ℝ)*x^2))).le
  have hh : rexp ((1/4:ℝ)*x^2)*rexp (-(1/4:ℝ)*x^2) = 1 := by
    rw [←exp_add,show (1/4:ℝ)*x^2+(-(1/4:ℝ)*x^2)=0 by ring,exp_zero]
  simpa only [mul_assoc,hh,mul_one] using hm

lemma polynomial_tail_bound {x : ℝ} (hx : 10 ≤ |x|) :
    (1+x^2)*exp ((-(1/4:ℝ)*x^2)) ≤ 101*exp (-25) := by
  have h := add_one_le_exp ((x^2-100)/4)
  have hx2 : 100 ≤ x^2 := by nlinarith [sq_abs x]
  have h' : 1+x^2 ≤ 101*exp ((x^2-100)/4) := by nlinarith only [h,hx2]
  have hm := mul_le_mul_of_nonneg_right h' (exp_pos ((-(1/4:ℝ)*x^2))).le
  rw [mul_assoc,←exp_add,show (x^2-100)/4+(-(1/4:ℝ)*x^2) = -25 by ring] at hm
  exact hm

lemma gaussian_tail_constant : 12928*exp (-25:ℝ) ≤ 1/1000000 := by
  have he : (27/10:ℝ) ≤ exp 1 := by linarith [exp_one_gt_d9]
  have hp := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 27/10) he 25
  have hh : 12928000000 ≤ exp (25:ℝ) := by
    rw [show exp (25:ℝ) = (exp (1:ℝ))^25 by simp]
    norm_num at hp ⊢
    linarith only [hp]
  rw [exp_neg]
  have he25 := exp_pos (25:ℝ)
  apply (mul_le_mul_iff_of_pos_right he25).mp
  field_simp
  linarith only [hh]

lemma integrable_weighted {f : ℝ → ℝ} (hf : AEStronglyMeasurable f volume)
    (hb : ∀ x, |f x| ≤ 32*(1+x^2)) :
    Integrable (fun x => f x*gaussianWeight x) volume := by
  have hbase := (integrable_exp_neg_mul_sq (by norm_num : (0:ℝ) < 1/4)).const_mul (128:ℝ)
  apply hbase.mono' (hf.mul (by unfold gaussianWeight; fun_prop))
  apply ae_of_all
  intro x
  change |f x*gaussianWeight x| ≤ _
  rw [abs_mul,abs_of_pos (show 0 < gaussianWeight x from exp_pos _)]
  calc
    |f x| *gaussianWeight x ≤ (32*(1+x^2))*gaussianWeight x :=
      mul_le_mul_of_nonneg_right (hb x) (exp_pos _).le
    _ = 32*((1+x^2)*exp ((-(1/4:ℝ)*x^2)))*exp ((-(1/4:ℝ)*x^2)) := by
      rw [gaussian_weight_factor]
      ring
    _ ≤ 128*exp ((-(1/4:ℝ)*x^2)) := by
      have hp := mul_le_mul_of_nonneg_right (polynomial_weight_bound x) (exp_pos ((-(1/4:ℝ)*x^2))).le
      nlinarith only [hp]

lemma gaussian_truncation {f : ℝ → ℝ} (hf : AEStronglyMeasurable f volume)
    (hb : ∀ x, |f x| ≤ 32*(1+x^2)) :
    |(∫ x, f x*gaussianWeight x)-(∫ x in (-10:ℝ)..10, f x*gaussianWeight x)| ≤ 1/1000000 := by
  have hi := integrable_weighted hf hb
  let s : Set ℝ := Icc (-10) 10
  have hs : MeasurableSet s := measurableSet_Icc
  have hi' := ((integrable_exp_neg_mul_sq (by norm_num : (0:ℝ) < 1/4)).const_mul
    (3232*exp (-25:ℝ))).integrableOn (s := sᶜ)
  have hm : ∀ᵐ x ∂volume.restrict sᶜ,
      |f x*gaussianWeight x| ≤ (3232*exp (-25:ℝ))*exp ((-(1/4:ℝ)*x^2)) := by
    rw [ae_restrict_iff' hs.compl]
    apply ae_of_all
    intro x hx
    have hxabs : 10 ≤ |x| := by
      by_contra h
      have ha := abs_lt.mp (lt_of_not_ge h)
      exact hx ⟨ha.1.le,ha.2.le⟩
    rw [abs_mul,abs_of_pos (show 0 < gaussianWeight x from exp_pos _)]
    calc
      |f x| *gaussianWeight x ≤ (32*(1+x^2))*gaussianWeight x :=
        mul_le_mul_of_nonneg_right (hb x) (exp_pos _).le
      _ = 32*((1+x^2)*exp ((-(1/4:ℝ)*x^2)))*exp ((-(1/4:ℝ)*x^2)) := by
        rw [gaussian_weight_factor]; ring
      _ ≤ (3232*exp (-25:ℝ))*exp ((-(1/4:ℝ)*x^2)) := by
        have hp := mul_le_mul_of_nonneg_right (polynomial_tail_bound hxabs) (exp_pos ((-(1/4:ℝ)*x^2))).le
        nlinarith only [hp]
  have hnorm := (norm_integral_le_integral_norm (f := fun x => f x*gaussianWeight x)
    (μ := volume.restrict sᶜ)).trans (integral_mono_ae hi.integrableOn.norm hi' (by
      filter_upwards [hm] with x hx
      simpa only [Real.norm_eq_abs] using hx))
  have hfull : (∫ x in sᶜ, (3232*exp (-25:ℝ))*exp ((-(1/4:ℝ)*x^2))) ≤
      ∫ x, (3232*exp (-25:ℝ))*exp ((-(1/4:ℝ)*x^2)) := by
    apply integral_mono_measure Measure.restrict_le_self (ae_of_all _ (fun x => by positivity))
    exact (integrable_exp_neg_mul_sq (by norm_num : (0:ℝ) < 1/4)).const_mul _
  have hsqrt : sqrt (Real.pi/(1/4:ℝ)) ≤ 4 := by
    apply (sqrt_le_iff).mpr
    exact ⟨by norm_num,by nlinarith [pi_lt_four]⟩
  simp only [integral_const_mul,integral_gaussian] at hfull
  have hlast : (3232*exp (-25:ℝ))*sqrt (Real.pi/(1/4:ℝ)) ≤ 12928*exp (-25:ℝ) := by
    nlinarith only [mul_le_mul_of_nonneg_left hsqrt (by positivity : 0 ≤ 3232*exp (-25:ℝ))]
  rw [Real.norm_eq_abs,setIntegral_compl hs hi] at hnorm
  have he : (∫ x in s, f x*gaussianWeight x) = ∫ x in (-10:ℝ)..10, f x*gaussianWeight x := by
    rw [intervalIntegral.integral_of_le (by norm_num : (-10:ℝ) ≤ 10)]
    exact integral_Icc_eq_integral_Ioc
  rw [he] at hnorm
  rw [integral_const_mul] at hnorm
  exact hnorm.trans (hfull.trans (hlast.trans gaussian_tail_constant))

lemma normalizer_bounds : (39894227/100000000:ℝ) ≤ gaussianNormalizer ∧
    gaussianNormalizer ≤ 39894229/100000000 := by
  have hpi0 := pi_pos
  have hpiL := pi_gt_d20
  have hpiU := pi_lt_d20
  have hp : 0 < sqrt (2*Real.pi) := sqrt_pos.2 (by positivity)
  have hs : sqrt (2*Real.pi)^2 = 2*Real.pi := sq_sqrt (by positivity)
  unfold gaussianNormalizer
  constructor
  · rw [inv_eq_one_div,le_div_iff₀ hp]
    nlinarith only [hs,hpiL,hpiU,hp]
  · rw [inv_eq_one_div,div_le_iff₀ hp]
    nlinarith only [hs,hpiL,hpiU,hp]

lemma affine_gaussian_integral (β : ℝ) {f : ℝ → ℝ} (hf : Measurable f) :
    (∫ h, f h ∂Scalar.fieldLaw β) =
      gaussianNormalizer*(∫ x, f (β^2+β*x)*gaussianWeight x) := by
  have hl : HasLaw (fun x : ℝ => β^2+β*x) (Scalar.fieldLaw β) (gaussianReal 0 1) := by
    have h := gaussianReal_const_add (gaussianReal_const_mul (HasLaw.id (μ := gaussianReal 0 1)) β) (β^2)
    convert! h using 1
    all_goals try with_reducible_and_instances rfl
    simp [Scalar.fieldLaw,Scalar.variance]
    congr 1
    exact Real.toNNReal_of_nonneg (sq_nonneg β)
  rw [←hl.integral_comp hf.aestronglyMeasurable,
    integral_gaussianReal_eq_integral_smul (by norm_num : (1:ℝ≥0) ≠ 0)]
  simp only [gaussianPDFReal,NNReal.coe_one,mul_one,sub_zero,smul_eq_mul]
  rw [←integral_const_mul]
  apply integral_congr_ae
  apply ae_of_all
  intro x
  dsimp [gaussianNormalizer,gaussianWeight]
  ring

end SKRatio.Certificate

end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Certificates_FixedExp
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Real
namespace SKRatio.Certificate.Fixed

lemma S_pos : (0:ℝ) < S := by norm_num [S]
lemma mem_round {a b : ℚ} {x : ℝ} (hx : (a:ℝ) ≤ x ∧ x ≤ b) : Mem (round a b) x := by
  have hl : (⌊a*(S:ℚ)⌋:ℚ) ≤ a*(S:ℚ) := Int.floor_le _
  have hu : b*(S:ℚ) ≤ (⌈b*(S:ℚ)⌉:ℚ) := Int.le_ceil _
  have hl' : (⌊a*(S:ℚ)⌋:ℝ) ≤ (a:ℝ)*(S:ℝ) := by exact_mod_cast hl
  have hu' : (b:ℝ)*(S:ℝ) ≤ (⌈b*(S:ℚ)⌉:ℝ) := by exact_mod_cast hu
  exact ⟨((div_le_iff₀ S_pos).mpr hl').trans hx.1,hx.2.trans ((le_div_iff₀ S_pos).mpr hu')⟩

lemma mem_sq {A : I} {x : ℝ} (hx : Mem A x) (hp : 0 ≤ x) : Mem (sq A) (x^2) := by
  have hl0 : (0:ℝ) ≤ (max 0 A.lo : ℤ)/(S:ℝ) := div_nonneg (by positivity) S_pos.le
  have hl : ((max 0 A.lo : ℤ):ℝ)/(S:ℝ) ≤ x := by
    rw [Int.cast_max,Int.cast_zero,←max_div_div_right S_pos.le]
    exact max_le (by simpa using hp) hx.1
  have hu0 : (0:ℝ) ≤ (A.hi:ℝ)/(S:ℝ) := hp.trans hx.2
  have hl2 := (sq_le_sq₀ hl0 hp).mpr hl
  have hu2 := (sq_le_sq₀ hp hu0).mpr hx.2
  have hL : ((max 0 A.lo)^2/S)*S ≤ (max 0 A.lo)^2 := Int.ediv_mul_le _ (by norm_num [S])
  have hU : A.hi^2 ≤ ((A.hi^2+S)/S)*S := by
    have hh := Int.lt_ediv_mul (A.hi^2+S) (by norm_num [S] : (0:ℤ) < S)
    linarith only [hh]
  have hL' : ((max 0 A.lo)^2/S:ℤ)*(S:ℝ) ≤ ((max 0 A.lo:ℤ):ℝ)^2 := by exact_mod_cast hL
  have hU' : (A.hi:ℝ)^2 ≤ ((A.hi^2+S)/S:ℤ)*(S:ℝ) := by exact_mod_cast hU
  refine ⟨?_,?_⟩
  · change (((max 0 A.lo)^2/S:ℤ):ℝ)/(S:ℝ) ≤ x^2
    apply le_trans _ hl2
    rw [div_pow,div_le_div_iff₀ S_pos (sq_pos_of_pos S_pos)]
    nlinarith only [mul_le_mul_of_nonneg_right hL' S_pos.le]
  · change x^2 ≤ (((A.hi^2+S)/S:ℤ):ℝ)/(S:ℝ)
    apply le_trans hu2
    rw [div_pow,div_le_div_iff₀ (sq_pos_of_pos S_pos) S_pos]
    nlinarith only [mul_le_mul_of_nonneg_right hU' S_pos.le]

lemma mem_iter {A : I} {x : ℝ} (hx : Mem A x) (hp : 0 ≤ x) (n : ℕ) :
    Mem (iter n A) (x^(2^n)) := by
  induction n generalizing A x with
  | zero => simpa only [iter,pow_zero,pow_one] using hx
  | succ n hn =>
    have h := hn (mem_sq hx hp) (sq_nonneg x)
    simpa only [iter,←pow_mul,show (2:ℕ)^(n+1) = 2*2^n by rw [pow_succ,Nat.mul_comm]] using h

lemma mem_expBounds {a b : ℚ} {x : ℝ} (hx : (a:ℝ) ≤ x ∧ x ≤ b)
    (hb : b < 1073741824) : Mem (expBounds a b) (exp x) := by
  have hhi : (b:ℝ) < 1073741824 := by exact_mod_cast hb
  have hr : Mem (round (1+a/1073741824) (1/(1-b/1073741824))) (exp (x/1073741824)) := by
    apply mem_round
    push_cast
    constructor
    · have ht := add_one_le_exp (x/1073741824)
      linarith only [hx.1,ht]
    · have hden : 0 < 1-(b:ℝ)/1073741824 := by linarith
      have hz : 1-(b:ℝ)/1073741824 ≤ exp (-(x/1073741824)) := by
        have ht := add_one_le_exp (-(x/1073741824))
        linarith only [hx.2,ht]
      have h := one_div_le_one_div_of_le hden hz
      simpa only [exp_neg,one_div,inv_inv] using h
  have he : exp (x/1073741824)^(2^30) = exp x := by
    rw [←exp_nat_mul]
    congr 1
    norm_num
    ring
  rw [←he]
  exact mem_iter hr (exp_pos _).le 30
end SKRatio.Certificate.Fixed

end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Certificates_CertifiedInterval
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Real
namespace SKRatio.Certificate

lemma down_le (q : ℚ) : (down q : ℝ) ≤ q := by
  have h : (down q : ℚ) ≤ q := by
    unfold down
    exact (div_le_iff₀ (by norm_num : (0:ℚ) < scale)).mpr (Int.floor_le _)
  exact_mod_cast h

lemma le_up (q : ℚ) : (q : ℝ) ≤ up q := by
  have h : q ≤ up q := by
    unfold up
    exact (le_div_iff₀ (by norm_num : (0:ℚ) < scale)).mpr (Int.le_ceil _)
  exact_mod_cast h

namespace Box

lemma mem_rat (q : ℚ) : (q:ℝ) ∈ rat q := ⟨le_rfl,le_rfl⟩
lemma mem_round {x : ℝ} {a b : ℚ} (hx : (a:ℝ) ≤ x ∧ x ≤ b) : x ∈ round a b :=
  ⟨(down_le a).trans hx.1,hx.2.trans (le_up b)⟩
lemma mem_add {A B : Box} {x y : ℝ} (hx : x ∈ A) (hy : y ∈ B) : x+y ∈ add A B := by
  change _ ∧ _
  simp only [add,Rat.cast_add]
  exact ⟨add_le_add hx.1 hy.1,add_le_add hx.2 hy.2⟩
lemma mem_neg {A : Box} {x : ℝ} (hx : x ∈ A) : -x ∈ neg A := by
  change _ ∧ _
  simp only [neg,Rat.cast_neg]
  exact ⟨neg_le_neg hx.2,neg_le_neg hx.1⟩
lemma mem_sub {A B : Box} {x y : ℝ} (hx : x ∈ A) (hy : y ∈ B) : x-y ∈ sub A B := by
  exact mem_add hx (mem_neg hy)

lemma four_products {a b c d x y : ℝ} (hx : a ≤ x ∧ x ≤ b) (hy : c ≤ y ∧ y ≤ d) :
    min (min (a*c) (a*d)) (min (b*c) (b*d)) ≤ x*y ∧
    x*y ≤ max (max (a*c) (a*d)) (max (b*c) (b*d)) := by
  have hlo : min (min (a*c) (a*d)) (min (b*c) (b*d)) ≤ a*c ∧
      min (min (a*c) (a*d)) (min (b*c) (b*d)) ≤ a*d ∧
      min (min (a*c) (a*d)) (min (b*c) (b*d)) ≤ b*c ∧
      min (min (a*c) (a*d)) (min (b*c) (b*d)) ≤ b*d := by
    simp only [min_le_iff,le_refl,or_true,true_or,and_self]
  have hhi : a*c ≤ max (max (a*c) (a*d)) (max (b*c) (b*d)) ∧
      a*d ≤ max (max (a*c) (a*d)) (max (b*c) (b*d)) ∧
      b*c ≤ max (max (a*c) (a*d)) (max (b*c) (b*d)) ∧
      b*d ≤ max (max (a*c) (a*d)) (max (b*c) (b*d)) := by
    simp only [le_max_iff,le_refl,or_true,true_or,and_self]
  have lower {L : ℝ} (h : L ≤ a*c ∧ L ≤ a*d ∧ L ≤ b*c ∧ L ≤ b*d) : L ≤ x*y := by
    rcases le_total 0 y with hp | hn
    · have ha : L ≤ a*y := by
        rcases le_total 0 a with hap | han
        · exact h.1.trans (mul_le_mul_of_nonneg_left hy.1 hap)
        · exact h.2.1.trans (mul_le_mul_of_nonpos_left hy.2 han)
      exact ha.trans (mul_le_mul_of_nonneg_right hx.1 hp)
    · have hb : L ≤ b*y := by
        rcases le_total 0 b with hbp | hbn
        · exact h.2.2.1.trans (mul_le_mul_of_nonneg_left hy.1 hbp)
        · exact h.2.2.2.trans (mul_le_mul_of_nonpos_left hy.2 hbn)
      exact hb.trans (mul_le_mul_of_nonpos_right hx.2 hn)
  have upper {U : ℝ} (h : a*c ≤ U ∧ a*d ≤ U ∧ b*c ≤ U ∧ b*d ≤ U) : x*y ≤ U := by
    rcases le_total 0 y with hp | hn
    · have hb : b*y ≤ U := by
        rcases le_total 0 b with hbp | hbn
        · exact (mul_le_mul_of_nonneg_left hy.2 hbp).trans h.2.2.2
        · exact (mul_le_mul_of_nonpos_left hy.1 hbn).trans h.2.2.1
      exact (mul_le_mul_of_nonneg_right hx.2 hp).trans hb
    · have ha : a*y ≤ U := by
        rcases le_total 0 a with hap | han
        · exact (mul_le_mul_of_nonneg_left hy.2 hap).trans h.2.1
        · exact (mul_le_mul_of_nonpos_left hy.1 han).trans h.1
      exact (mul_le_mul_of_nonpos_right hx.1 hn).trans ha
  exact ⟨lower hlo,upper hhi⟩

lemma mem_mul {A B : Box} {x y : ℝ} (hx : x ∈ A) (hy : y ∈ B) : x*y ∈ mul A B := by
  apply mem_round
  simp only [Rat.cast_min,Rat.cast_max,Rat.cast_mul]
  exact four_products hx hy

lemma mem_inv {A B : Box} {x : ℝ} (hx : x ∈ A) (he : inv A=some B) : x⁻¹ ∈ B ∧ x ≠ 0 := by
  unfold inv at he
  split_ifs at he with hp
  · cases he
    have hp' : 0 < (A.lo:ℝ) := by exact_mod_cast hp
    have hx' : 0 < x := hp'.trans_le hx.1
    have hh : 0 < (A.hi:ℝ) := hx'.trans_le hx.2
    refine ⟨mem_round ?_,hx'.ne'⟩
    simp only [one_div,Rat.cast_inv]
    exact ⟨inv_anti₀ hx' hx.2,inv_anti₀ hp' hx.1⟩

lemma mem_sq {A : Box} {x : ℝ} (hx : x ∈ A) : x^2 ∈ sq A := by
  apply mem_round
  constructor
  · split_ifs with hp hn
    · rw [Rat.cast_pow]
      exact (sq_le_sq₀ (by exact_mod_cast hp) (by exact (show (0:ℝ) ≤ A.lo from by exact_mod_cast hp).trans hx.1)).mpr hx.1
    · rw [Rat.cast_pow]
      have hn' : (A.hi:ℝ) ≤ 0 := by exact_mod_cast hn
      nlinarith [hx.2]
    · simpa using sq_nonneg x
  · simp only [Rat.cast_max,Rat.cast_pow]
    rcases le_total 0 x with hp | hn
    · exact (show x^2 ≤ (A.hi:ℝ)^2 from (sq_le_sq₀ hp (hp.trans hx.2)).mpr hx.2).trans (le_max_right _ _)
    · have ha : (A.lo:ℝ) ≤ 0 := hx.1.trans hn
      exact (show x^2 ≤ (A.lo:ℝ)^2 by nlinarith [hx.1]).trans (le_max_left _ _)

lemma mem_exp {A B : Box} {x : ℝ} (hx : x ∈ A) (he : exp A=some B) : Real.exp x ∈ B := by
  unfold exp at he
  split_ifs at he with hh
  cases he
  have hb := Fixed.mem_expBounds hx hh
  change _ ∧ _
  simp only [Rat.cast_div,Rat.cast_intCast]
  exact hb

end Box
end SKRatio.Certificate

end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Certificates_CertifiedJet
attribute [-instance] _root_.OAI.SKRatio.Certificate.Expr.instAdd _root_.OAI.SKRatio.Certificate.Expr.instDiv _root_.OAI.SKRatio.Certificate.Expr.instMul _root_.OAI.SKRatio.Certificate.Expr.instNeg _root_.OAI.SKRatio.Certificate.Expr.instOfNat _root_.OAI.SKRatio.Certificate.Expr.instSub _root_.OAI.SKRatio.Observation.History.historyTopology
attribute [-simp] _root_.OAI.SKRatio.Certificate.Expr.val_add _root_.OAI.SKRatio.Certificate.Expr.val_div _root_.OAI.SKRatio.Certificate.Expr.val_mul _root_.OAI.SKRatio.Certificate.Expr.val_ofNat _root_.OAI.SKRatio.Certificate.Expr.val_sub
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Real
namespace SKRatio.Certificate

namespace Jet
open Box

lemma tanh_formula (x : ℝ) : Real.tanh x = (Real.exp (2*x)-1)*(Real.exp (2*x)+1)⁻¹ := by
  have h := Calculus.exp_two_mul_one_sub_tanh x
  have hd : Real.exp (2*x)+1 ≠ 0 := by positivity
  apply (mul_right_cancel₀ hd)
  field_simp
  linarith only [h]

lemma mem_tanhBox {A B : Box} {x : ℝ} (hx : x ∈ A) (he : tanhBox A=some B) : Real.tanh x ∈ B := by
  simp only [tanhBox,bind, pure, Option.bind_eq_some_iff,Option.some.injEq] at he
  obtain ⟨E,hE,D,hD,rfl⟩ := he
  have he' := Box.mem_exp (Box.mem_mul (Box.mem_rat 2) hx) hE
  norm_num only [Rat.cast_ofNat] at he'
  have hd' := Box.mem_inv (Box.mem_add he' (Box.mem_rat 1)) hD
  rw [tanh_formula]
  exact Box.mem_mul (Box.mem_sub he' (by exact_mod_cast Box.mem_rat 1)) (by simpa only [Rat.cast_one] using hd'.1)
end Jet

namespace Expr

lemma derivatives (e : Expr) (x : ℝ) (h : e.Regular x) :
    HasDerivAt e.val (e.der x) x ∧ HasDerivAt e.der (e.sec x) x := by
  induction e with
  | rat q => exact ⟨hasDerivAt_const _ _,hasDerivAt_const _ _⟩
  | var => exact ⟨hasDerivAt_id _,hasDerivAt_const _ _⟩
  | add a b ha hb =>
    exact ⟨(ha h.1).1.add (hb h.2).1,(ha h.1).2.add (hb h.2).2⟩
  | neg a ha => exact ⟨(ha h).1.neg,(ha h).2.neg⟩
  | mul a b ha hb =>
    obtain ⟨ha,ha'⟩ := ha h.1
    obtain ⟨hb,hb'⟩ := hb h.2
    refine ⟨ha.mul hb,?_⟩
    convert! (ha'.mul hb).add (ha.mul hb') using 1
    all_goals try with_reducible_and_instances rfl
    dsimp [der,sec]
    ring
  | sq a ha =>
    obtain ⟨ha,ha'⟩ := ha h
    refine ⟨?_,?_⟩
    · convert! ha.pow 2 using 1
      all_goals try with_reducible_and_instances rfl
      dsimp [der,val]
      ring
    · convert! ((ha.const_mul 2).mul ha') using 1
      all_goals try with_reducible_and_instances rfl
      dsimp [der,sec]
      ring
  | inv a ha =>
    obtain ⟨ha,ha'⟩ := ha h.1
    have hi := ha.inv h.2
    refine ⟨?_,?_⟩
    · convert! hi using 1
      all_goals try with_reducible_and_instances rfl
      dsimp [val,der]
      field_simp
    · convert! ha'.neg.mul (hi.pow 2) using 1
      all_goals try with_reducible_and_instances rfl
      dsimp [der,sec]
      field_simp
      ring
  | exp a ha =>
    obtain ⟨ha,ha'⟩ := ha h
    refine ⟨ha.exp,?_⟩
    convert! ha.exp.mul ha' using 1
    all_goals try with_reducible_and_instances rfl
    dsimp [der,sec]
    ring
  | tanh a ha =>
    obtain ⟨ha,ha'⟩ := ha h
    have hm := (Calculus.hasDerivAt_tanh (a.val x)).comp x ha
    refine ⟨hm,?_⟩
    convert! ((hasDerivAt_const x (1:ℝ)).sub (hm.pow 2)).mul ha' using 1
    all_goals try with_reducible_and_instances rfl
    dsimp [der,sec]
    ring

lemma compute_sound (e : Expr) {B : Box} {J : Jet} (hc : e.compute B=some J)
    {x : ℝ} (hx : x ∈ B) :
    e.val x ∈ J.val ∧ e.der x ∈ J.der ∧ e.sec x ∈ J.sec ∧ e.Regular x := by
  induction e generalizing J with
  | rat q =>
    simp only [compute,Option.some.injEq] at hc
    cases hc
    exact ⟨Box.mem_rat q,by simpa only [Jet.rat,Jet.var,der,sec,Rat.cast_zero] using Box.mem_rat 0,by simpa only [Jet.rat,Jet.var,der,sec,Rat.cast_zero] using Box.mem_rat 0,trivial⟩
  | var =>
    simp only [compute,Option.some.injEq] at hc
    cases hc
    exact ⟨hx,by simpa only [Jet.rat,Jet.var,der,sec,Rat.cast_one] using Box.mem_rat 1,by simpa only [Jet.rat,Jet.var,der,sec,Rat.cast_zero] using Box.mem_rat 0,trivial⟩
  | add a b ha hb =>
    simp only [compute,bind, pure, Option.bind_eq_some_iff,Option.some.injEq] at hc
    obtain ⟨A,hA,C,hC,rfl⟩ := hc
    obtain ⟨ha0,ha1,ha2,har⟩ := ha hA
    obtain ⟨hb0,hb1,hb2,hbr⟩ := hb hC
    exact ⟨Box.mem_add ha0 hb0,Box.mem_add ha1 hb1,Box.mem_add ha2 hb2,har,hbr⟩
  | neg a ha =>
    simp only [compute,bind, pure, Option.bind_eq_some_iff,Option.some.injEq] at hc
    obtain ⟨A,hA,rfl⟩ := hc
    obtain ⟨ha0,ha1,ha2,har⟩ := ha hA
    exact ⟨Box.mem_neg ha0,Box.mem_neg ha1,Box.mem_neg ha2,har⟩
  | mul a b ha hb =>
    simp only [compute,bind, pure, Option.bind_eq_some_iff,Option.some.injEq] at hc
    obtain ⟨A,hA,C,hC,rfl⟩ := hc
    obtain ⟨ha0,ha1,ha2,har⟩ := ha hA
    obtain ⟨hb0,hb1,hb2,hbr⟩ := hb hC
    refine ⟨Box.mem_mul ha0 hb0,Box.mem_add (Box.mem_mul ha1 hb0) (Box.mem_mul ha0 hb1),?_,har,hbr⟩
    simpa only [sec,der,Jet.mul,Jet.sq,Rat.cast_ofNat,mul_assoc] using Box.mem_add
      (Box.mem_add (Box.mem_mul ha2 hb0) (Box.mem_mul (Box.mem_rat 2) (Box.mem_mul ha1 hb1))) (Box.mem_mul ha0 hb2)
  | sq a ha =>
    simp only [compute,bind, pure, Option.bind_eq_some_iff,Option.some.injEq] at hc
    obtain ⟨A,hA,rfl⟩ := hc
    obtain ⟨ha0,ha1,ha2,har⟩ := ha hA
    refine ⟨Box.mem_sq ha0,?_,?_,har⟩
    · simpa only [sec,der,Jet.mul,Jet.sq,Rat.cast_ofNat,mul_assoc] using Box.mem_mul (Box.mem_rat 2) (Box.mem_mul ha0 ha1)
    · exact Box.mem_mul (by simpa using Box.mem_rat 2) (Box.mem_add (Box.mem_sq ha1) (Box.mem_mul ha0 ha2))
  | inv a ha =>
    simp only [compute,bind, pure, Option.bind_eq_some_iff,Jet.inv,Option.some.injEq] at hc
    obtain ⟨A,hA,C,hC,rfl⟩ := hc
    obtain ⟨ha0,ha1,ha2,har⟩ := ha hA
    obtain ⟨hi,hn⟩ := Box.mem_inv ha0 hC
    refine ⟨hi,?_,?_,har,hn⟩
    · simpa only [der,neg_mul] using Box.mem_neg (Box.mem_mul ha1 (Box.mem_sq hi))
    · have h := Box.mem_sub (Box.mem_mul (Box.mem_rat 2) (Box.mem_mul (Box.mem_sq ha1)
          (Box.mem_mul hi (Box.mem_sq hi)))) (Box.mem_mul ha2 (Box.mem_sq hi))
      convert! h using 1
      all_goals try with_reducible_and_instances rfl
      dsimp [sec,Jet.inv]
      ring
  | exp a ha =>
    simp only [compute,bind, pure, Option.bind_eq_some_iff,Jet.exp,Option.some.injEq] at hc
    obtain ⟨A,hA,C,hC,rfl⟩ := hc
    obtain ⟨ha0,ha1,ha2,har⟩ := ha hA
    have he := Box.mem_exp ha0 hC
    exact ⟨he,Box.mem_mul he ha1,Box.mem_mul he (Box.mem_add ha2 (Box.mem_sq ha1)),har⟩
  | tanh a ha =>
    simp only [compute,bind, pure, Option.bind_eq_some_iff,Jet.tanh,Option.some.injEq] at hc
    obtain ⟨A,hA,C,hC,rfl⟩ := hc
    obtain ⟨ha0,ha1,ha2,har⟩ := ha hA
    have hm := Jet.mem_tanhBox ha0 hC
    have hv := Box.mem_sub (Box.mem_rat 1) (Box.mem_sq hm)
    norm_num only [Rat.cast_one] at hv
    refine ⟨hm,Box.mem_mul hv ha1,?_,har⟩
    have h := Box.mem_sub (Box.mem_mul hv ha2) (Box.mem_mul (Box.mem_rat 2)
      (Box.mem_mul hm (Box.mem_mul hv (Box.mem_sq ha1))))
    simpa only [sec,der,Jet.mul,Jet.sq,Rat.cast_ofNat,mul_assoc] using h

end Expr
end SKRatio.Certificate

end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Certificates_CertifiedQuadrature
attribute [-instance] _root_.OAI.SKRatio.Certificate.Expr.instAdd _root_.OAI.SKRatio.Certificate.Expr.instDiv _root_.OAI.SKRatio.Certificate.Expr.instMul _root_.OAI.SKRatio.Certificate.Expr.instNeg _root_.OAI.SKRatio.Certificate.Expr.instOfNat _root_.OAI.SKRatio.Certificate.Expr.instSub _root_.OAI.SKRatio.Observation.History.historyTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Real Set MeasureTheory
namespace SKRatio.Certificate

namespace Box

lemma mem_of_contains {A B : Box} {x : ℝ} (h : contains A B=true) (hx : x ∈ B) : x ∈ A := by
  have h' : A.lo ≤ B.lo ∧ B.hi ≤ A.hi := of_decide_eq_true h
  have hl : (A.lo:ℝ) ≤ B.lo := by exact_mod_cast h'.1
  have hu : (B.hi:ℝ) ≤ A.hi := by exact_mod_cast h'.2
  exact ⟨hl.trans hx.1,hx.2.trans hu⟩

lemma absUpper_nonneg (A : Box) : (0:ℝ) ≤ A.absUpper := by
  exact_mod_cast (abs_nonneg A.lo).trans (le_max_left |A.lo| |A.hi|)

lemma abs_le_absUpper {A : Box} {x : ℝ} (hx : x ∈ A) : |x| ≤ A.absUpper := by
  have hl : |(A.lo:ℝ)| ≤ (A.absUpper:ℝ) := by simp [absUpper]
  have hu : |(A.hi:ℝ)| ≤ (A.absUpper:ℝ) := by simp [absUpper]
  exact abs_le.mpr ⟨by linarith [hx.1,(abs_le.mp hl).1],by linarith [hx.2,(abs_le.mp hu).2]⟩

lemma mem_widen {A : Box} {x y : ℝ} {r : ℚ} (hx : x ∈ A) (hy : |x-y| ≤ (r:ℝ)) : y ∈ widen A r := by
  change (A.lo-r:ℚ) ≤ y ∧ y ≤ (A.hi+r:ℚ)
  push_cast
  obtain ⟨hy0,hy1⟩ := abs_le.mp hy
  exact ⟨by linarith [hx.1],by linarith [hx.2]⟩
end Box

lemma trapezoid_bound {f f' f'' : ℝ → ℝ} {a b M : ℝ} (hab : a < b)
    (hf : ∀ x ∈ Icc a b, HasDerivAt f (f' x) x)
    (hf' : ∀ x ∈ Icc a b, HasDerivAt f' (f'' x) x)
    (hM : 0 ≤ M) (hb : ∀ x ∈ Icc a b, |f'' x| ≤ M) :
    |(b-a)/2*(f a+f b)-(∫ x in a..b, f x)| ≤ (b-a)^3*M/12 := by
  have hud := uniqueDiffOn_Icc hab
  have hd : EqOn (derivWithin f (Icc a b)) f' (Icc a b) := fun x hx =>
    (hf x hx).hasDerivWithinAt.derivWithin (hud x hx)
  have hdd : DifferentiableOn ℝ (derivWithin f (Icc a b)) (Icc a b) :=
    (show DifferentiableOn ℝ f' (Icc a b) from
      fun x hx => (hf' x hx).differentiableAt.differentiableWithinAt).congr hd
  have h2 : ∀ x, |iteratedDerivWithin 2 f (Icc a b) x| ≤ M := by
    intro x
    rw [iteratedDerivWithin_succ',iteratedDerivWithin_succ',iteratedDerivWithin_zero]
    by_cases hx : x ∈ Icc a b
    · rw [derivWithin_congr hd (hd hx), (hf' x hx).hasDerivWithinAt.derivWithin (hud x hx)]
      exact hb x hx
    · rw [derivWithin_zero_of_notMem_closure (by simpa using hx), abs_zero]
      exact hM
  have h := trapezoidal_error_le (f := f) (a := a) (b := b)
    (by rw [uIcc_of_lt hab]; exact fun x hx => (hf x hx).differentiableAt.differentiableWithinAt)
    (by rwa [uIcc_of_lt hab]) (ζ := M) (by rwa [uIcc_of_lt hab]) (N := 1) (by decide)
  simpa [trapezoidal_error,trapezoidal_integral_one,abs_of_pos (sub_pos.mpr hab)] using h

namespace Expr

lemma cell_sound (e : Expr) {a b : ℚ} {A : Box} (hc : e.cell a b=some A) :
    IntervalIntegrable e.val volume a b ∧ (∫ x in (a:ℝ)..b, e.val x) ∈ A := by
  unfold cell at hc
  split_ifs at hc with hab
  have hab' : (a:ℝ) < b := by exact_mod_cast hab
  simp only [bind,pure,Option.bind_eq_some_iff,Option.some.injEq] at hc
  obtain ⟨JA,hJA,JB,hJB,J,hJ,rfl⟩ := hc
  have hA := e.compute_sound hJA (Box.mem_rat a)
  have hB := e.compute_sound hJB (Box.mem_rat b)
  have hI (x : ℝ) (hx : x ∈ Icc (a:ℝ) b) := e.compute_sound hJ hx
  have hf (x : ℝ) (hx : x ∈ Icc (a:ℝ) b) := (e.derivatives x (hI x hx).2.2.2).1
  have hf' (x : ℝ) (hx : x ∈ Icc (a:ℝ) b) := (e.derivatives x (hI x hx).2.2.2).2
  refine ⟨(show ContinuousOn e.val (Icc (a:ℝ) b) from
      fun x hx => (hf x hx).continuousAt.continuousWithinAt).intervalIntegrable_of_Icc hab'.le,?_⟩
  have ht := Box.mem_mul (Box.mem_rat ((b-a)/2)) (Box.mem_add hA.1 hB.1)
  apply Box.mem_widen ht
  push_cast
  exact trapezoid_bound hab' hf hf' (Box.absUpper_nonneg J.sec)
    (fun x hx => Box.abs_le_absUpper (hI x hx).2.2.1)

lemma quad_sound (e : Expr) {h a : ℚ} {n : ℕ} {A : Box}
    (hc : e.quad h n a=some A) :
    IntervalIntegrable e.val volume a (a+n*h:ℚ) ∧
      (∫ x in (a:ℝ)..(a+n*h:ℚ), e.val x) ∈ A := by
  induction n generalizing A a with
  | zero =>
    simp only [quad,Option.some.injEq] at hc
    cases hc
    simp only [Nat.cast_zero,zero_mul,add_zero,IntervalIntegrable.refl,intervalIntegral.integral_same]
    exact ⟨trivial,by simpa only [Rat.cast_zero] using Box.mem_rat 0⟩
  | succ n hn =>
    simp only [quad,bind,pure,Option.bind_eq_some_iff,Option.some.injEq] at hc
    obtain ⟨B,hB,C,hC,rfl⟩ := hc
    obtain ⟨hi,hm⟩ := e.cell_sound hB
    obtain ⟨hi',hm'⟩ := hn hC
    have hh : a+h+(n:ℚ)*h = a+(n+1:ℕ)*h := by push_cast; ring
    rw [hh] at hi' hm'
    refine ⟨hi.trans hi',?_⟩
    rw [←intervalIntegral.integral_add_adjacent_intervals hi hi']
    exact Box.mem_add hm hm'

lemma check_sound (e : Expr) {a h : ℚ} {n : ℕ} {A : Box}
    (hc : e.check a h n A=true) :
    IntervalIntegrable e.val volume a (a+n*h:ℚ) ∧
      (∫ x in (a:ℝ)..(a+n*h:ℚ), e.val x) ∈ A := by
  unfold check at hc
  split at hc
  · contradiction
  · rename_i B hB
    obtain ⟨hi,hm⟩ := e.quad_sound hB
    exact ⟨hi,Box.mem_of_contains hc hm⟩

end Expr
end SKRatio.Certificate

end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Certificates_CertifiedBatches
attribute [-instance] _root_.OAI.SKRatio.Certificate.Expr.instAdd _root_.OAI.SKRatio.Certificate.Expr.instDiv _root_.OAI.SKRatio.Certificate.Expr.instMul _root_.OAI.SKRatio.Certificate.Expr.instNeg _root_.OAI.SKRatio.Certificate.Expr.instOfNat _root_.OAI.SKRatio.Certificate.Expr.instSub _root_.OAI.SKRatio.Observation.History.historyBorel _root_.OAI.SKRatio.Observation.History.historyMeasurable _root_.OAI.SKRatio.Observation.History.historySecondCountable _root_.OAI.SKRatio.Observation.History.historyTopology
attribute [-simp] _root_.OAI.SKRatio.Certificate.Expr.val_add _root_.OAI.SKRatio.Certificate.Expr.val_div _root_.OAI.SKRatio.Certificate.Expr.val_mul _root_.OAI.SKRatio.Certificate.Expr.val_ofNat _root_.OAI.SKRatio.Certificate.Expr.val_sub
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Real Set MeasureTheory
namespace SKRatio.Certificate

lemma integral_batches (e : Expr) (a h : ℚ) (k m : ℕ) (B : ℕ → Box)
    (hc : ∀ i < m, e.check (a+i*(k*h)) h k (B i) = true) :
    IntervalIntegrable e.val volume a (a+m*(k*h):ℚ) ∧
    (∫ x in (a:ℝ)..(a+m*(k*h):ℚ), e.val x) ∈ sumBoxes B m := by
  induction m with
  | zero =>
    simp only [sumBoxes,Nat.cast_zero,zero_mul,add_zero,IntervalIntegrable.refl,intervalIntegral.integral_same]
    exact ⟨trivial,by simpa only [Rat.cast_zero] using Box.mem_rat 0⟩
  | succ m hm =>
    have ht := hm (fun i hi => hc i (lt_trans hi (Nat.lt_succ_self m)))
    have hn := e.check_sound (hc m (Nat.lt_succ_self m))
    have he : a+(m:ℚ)*(k*h)+k*h = a+(m+1:ℕ)*(k*h) := by push_cast; ring
    rw [he] at hn
    refine ⟨ht.1.trans hn.1,?_⟩
    rw [←intervalIntegral.integral_add_adjacent_intervals ht.1 hn.1]
    exact Box.mem_add ht.2 hn.2

lemma normalizer_mem : gaussianNormalizer ∈ normalizerBox := by
  change ((39894227/100000000:ℚ):ℝ) ≤ gaussianNormalizer ∧ gaussianNormalizer ≤ ((39894229/100000000:ℚ):ℝ)
  norm_num only [Rat.cast_div,Rat.cast_ofNat]
  exact normalizer_bounds

lemma gaussian_certificate {e : Expr} {β : ℝ} {f : ℝ → ℝ} {B : ℕ → Box} {A : Box}
    {h : ℚ} {k : ℕ} (hh : (k:ℚ)*h=1/2)
    (hfun : ∀ x, e.val x = f (β^2+β*x)*gaussianWeight x)
    (hf : Measurable f) (hb : ∀ x, |f (β^2+β*x)| ≤ 32*(1+x^2))
    (hc : ∀ i : ℕ, i < 40 → e.check (-10+(i:ℚ)*(k*h)) h k (B i) = true)
    (hsum : batchCheck B 40 A = true) : (∫ h, f h ∂Scalar.fieldLaw β) ∈ A := by
  have ht := integral_batches e (-10) h k 40 B hc
  rw [hh] at ht
  norm_num only [show (-10:ℚ)+40*(1/2) = 10 by norm_num] at ht
  have htail := gaussian_truncation (f := fun x => f (β^2+β*x))
    (hf.comp (by fun_prop)).aestronglyMeasurable hb
  have hI : (∫ x in (-10:ℝ)..10, f (β^2+β*x)*gaussianWeight x) ∈ sumBoxes B 40 := by
    simpa only [hfun,Rat.cast_neg,Rat.cast_ofNat] using ht.2
  have hfull := Box.mem_widen (y := ∫ x, f (β^2+β*x)*gaussianWeight x) (r := 1/1000000) hI (by simpa only [Rat.cast_div,Rat.cast_one,Rat.cast_ofNat,abs_sub_comm] using htail)
  rw [affine_gaussian_integral β hf]
  exact Box.mem_of_contains hsum (Box.mem_mul normalizer_mem hfull)
end SKRatio.Certificate

end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Variational_ScalarReduction
attribute [-instance] _root_.OAI.SKRatio.Observation.History.historyBorel _root_.OAI.SKRatio.Observation.History.historyMeasurable _root_.OAI.SKRatio.Observation.History.historySecondCountable _root_.OAI.SKRatio.Observation.History.historyTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Real
namespace SKRatio.Scalar

lemma multiplier_strict_pos (h : ℝ) : 0 < multiplier h := by
  linarith [multiplier_pos h]

section Probability
variable (μ : Measure ℝ) [IsProbabilityMeasure μ]

lemma integrable_multiplier : Integrable multiplier μ := by
  apply (integrable_const (76/100:ℝ)).mono' continuous_multiplier.aestronglyMeasurable
  exact ae_of_all _ (fun h => by
    simpa only [norm_eq_abs,abs_of_pos (multiplier_strict_pos h)] using multiplier_le h)

lemma mean_multiplier_pos : 0 < ∫ h, multiplier h ∂μ := by
  have h := integral_mono (integrable_const (4464/10000:ℝ)) (integrable_multiplier μ)
    multiplier_pos
  simp only [integral_const,probReal_univ,smul_eq_mul,one_mul] at h
  linarith

variable {μ}

lemma integral_centered_sq {f : ℝ → ℝ} (hf : MemLp f 2 μ) :
    ∫ h, (f h-(∫ t, f t ∂μ))^2 ∂μ =
      (∫ h, f h^2 ∂μ)-(∫ h, f h ∂μ)^2 := by
  have hI := hf.integrable (by norm_num : (1:ENNReal) ≤ 2)
  have hid (h : ℝ) : (f h-(∫ t, f t ∂μ))^2 =
      f h^2-(2*(∫ t, f t ∂μ))*f h+(∫ t, f t ∂μ)^2 := by ring
  simp_rw [hid]
  have hsub : Integrable (fun h => f h^2-(2*(∫ t, f t ∂μ))*f h) μ :=
    hf.integrable_sq.sub (hI.const_mul _)
  rw [integral_add hsub (integrable_const _),
    integral_sub hf.integrable_sq (hI.const_mul _),integral_const_mul,integral_const]
  simp only [probReal_univ,smul_eq_mul,one_mul]
  ring

end Probability

end SKRatio.Scalar

end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Variational_ScalarHilbert
attribute [-instance] _root_.OAI.SKRatio.Observation.History.historyMeasurable _root_.OAI.SKRatio.Observation.History.historyTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory Real
namespace SKRatio.Scalar

section Measure
variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

lemma l2Norm_nonneg (f : α → ℝ) : 0 ≤ l2Norm μ f := sqrt_nonneg _
lemma l2Norm_sq (f : α → ℝ) : l2Norm μ f^2 = ∫ x, f x^2 ∂μ :=
  sq_sqrt (integral_nonneg (fun x => sq_nonneg (f x)))

lemma abs_integral_mul_le {f u : α → ℝ} (hf : MemLp f 2 μ) (hu : MemLp u 2 μ) :
    |∫ x, f x*u x ∂μ| ≤ l2Norm μ f*l2Norm μ u := by
  have h := integral_mul_norm_le_Lp_mul_Lq Real.HolderConjugate.two_two
    (by simpa using hf) (by simpa using hu)
  simp only [norm_eq_abs,Real.rpow_two,sq_abs,←sqrt_eq_rpow] at h
  have h' : |∫ x, f x*u x ∂μ| ≤ ∫ x, |f x| * |u x| ∂μ := by
    simpa only [abs_mul] using (abs_integral_le_integral_abs (f := fun x => f x*u x) (μ := μ))
  exact h'.trans h

lemma integral_square_add {u z : α → ℝ}
    (hu : MemLp u 2 μ) (hz : MemLp z 2 μ) (s t : ℝ) :
    ∫ x, (s*u x+t*z x)^2 ∂μ =
      s^2*(∫ x, u x^2 ∂μ)+(2*s*t)*(∫ x, u x*z x ∂μ)+t^2*(∫ x, z x^2 ∂μ) := by
  have hpair : Integrable (fun x => u x*z x) μ := hu.integrable_mul hz
  have hsum : Integrable (fun x => s^2*u x^2+(2*s*t)*(u x*z x)) μ :=
    (hu.integrable_sq.const_mul _).add (hpair.const_mul _)
  have he (x : α) : (s*u x+t*z x)^2 = s^2*u x^2+(2*s*t)*(u x*z x)+t^2*z x^2 := by ring
  simp_rw [he]
  rw [integral_add hsum (hz.integrable_sq.const_mul _),
    integral_add (hu.integrable_sq.const_mul _) (hpair.const_mul _),
    integral_const_mul,integral_const_mul,integral_const_mul]

end Measure

section Probability
variable {μ : Measure ℝ} [IsProbabilityMeasure μ]

omit [IsProbabilityMeasure μ] in
lemma sd_nonneg (f : ℝ → ℝ) : 0 ≤ sd μ f := l2Norm_nonneg _

lemma memLp_centered {f : ℝ → ℝ} (hf : MemLp f 2 μ) : MemLp (centered μ f) 2 μ :=
  hf.sub (memLp_const _)

end Probability
end SKRatio.Scalar

end
end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Variational_ScalarCoherent
attribute [-instance] _root_.OAI.SKRatio.Observation.History.historyMeasurable _root_.OAI.SKRatio.Observation.History.historyTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Topology NNReal ENNReal
open MeasureTheory ProbabilityTheory Real
namespace SKRatio.Scalar

lemma l_eq (β : ℝ) : l β = 64/100-(19/100)*a β := mean_multiplier β
lemma l_pos (β : ℝ) : 0 < l β := mean_multiplier_pos _
lemma a_nonneg (β : ℝ) : 0 ≤ a β := integral_nonneg (fun h => (v_pos h).le)
lemma a_le_one (β : ℝ) : a β ≤ 1 := by
  have h := integral_mono (memLp_v.integrable (by norm_num : (1:ENNReal) ≤ 2))
    (integrable_const (μ := fieldLaw β) 1) v_le_one
  simpa only [a,integral_const,probReal_univ,smul_eq_mul,one_mul] using h

lemma memLp_F (β : ℝ) : MemLp (F β) 2 (fieldLaw β) := by
  convert! (((((memLp_field_v β).add ((memLp_field β).const_mul (a β))).add
      (memLp_mv.const_mul (2*β^2))).add (memLp_v.const_mul (50/100-β^2*a β/l β))).add
      (memLp_m.const_mul (12/100:ℝ))).add (memLp_g.const_mul (3*β^2*G β)) using 1
  all_goals try with_reducible_and_instances rfl
  ext h
  dsimp [F]
  ring

end SKRatio.Scalar

end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Certificates_CertifiedFunctions
attribute [-instance] _root_.OAI.SKRatio.Observation.History.historyTopology
attribute [-simp] _root_.OAI.SKRatio.Planted.compactWeight_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Real MeasureTheory ProbabilityTheory
namespace SKRatio.Certificate
open Scalar

lemma scalarExpr_val (β A C M Q : ℚ) (k : ℕ) (h : Expr) (x : ℝ) :
    (scalarExpr β A C M Q k h).val x = scalarFunction β A C M Q k (h.val x) := by
  have hg : (7/4:ℝ)-Real.tanh (h.val x) = w (h.val x)+3/4 := by unfold w m; ring
  unfold scalarExpr scalarFunction
  split <;> simp only [Expr.val_sub,Expr.val_div,
    Expr.val,Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_pow,
    Rat.cast_ofNat,Rat.cast_one,hg] <;>
    dsimp [v,m,g,rho,multiplier,approxF] <;> ring

lemma integrandExpr_val (β A C M Q : ℚ) (k : ℕ) (x : ℝ) :
    (integrandExpr β A C M Q k).val x =
      scalarFunction β A C M Q k ((β:ℝ)^2+β*x)*gaussianWeight x := by
  unfold integrandExpr
  rw [Expr.val_mul,scalarExpr_val]
  simp only [Expr.val,Rat.cast_pow,Rat.cast_neg,
    Rat.cast_div,Rat.cast_one,Rat.cast_ofNat,gaussianWeight]
  congr 2
  ring

lemma continuous_approxF (β A C : ℝ) : Continuous (approxF β A C) := by
  unfold approxF
  exact (((((continuous_v.add continuous_const).mul continuous_id).add
    (continuous_const.mul (continuous_m.mul continuous_v))).add
    (continuous_const.mul continuous_v)).add (continuous_const.mul continuous_m)).add
      (continuous_const.mul continuous_g)

lemma continuous_scalarFunction (β A C M Q : ℝ) (k : ℕ) :
    Continuous (scalarFunction β A C M Q k) := by
  unfold scalarFunction
  split
  · exact continuous_v
  · exact continuous_g
  · exact continuous_m.mul continuous_v
  · exact continuous_rho
  · exact (continuous_v.sub continuous_const).pow 2
  · exact (continuous_g.sub continuous_const).pow 2
  · exact ((continuous_m.mul continuous_v).sub continuous_const).pow 2
  · exact ((continuous_approxF β A C).sub continuous_const).pow 2
  · exact (((continuous_const.add continuous_v).pow 2).div continuous_multiplier
      (fun h => (multiplier_strict_pos h).ne')).div_const 16
  · exact ((continuous_v.pow 2).div continuous_multiplier
      (fun h => (multiplier_strict_pos h).ne')).div_const 16
  · exact ((continuous_v.pow 2).div (continuous_const.sub continuous_m)
      (fun h => by change 2-m h ≠ 0; linarith [(m_bounds h).2])).div_const 4
  · exact ((continuous_v.pow 2).div ((continuous_const.sub continuous_m).pow 2)
      (fun h => pow_ne_zero _ (by change 2-m h ≠ 0; linarith [(m_bounds h).2]))).div_const 4
  · exact (continuous_v.mul (continuous_const.add continuous_m)).div_const 4

end SKRatio.Certificate

end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Certificates_CertifiedFunctionBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Topology ENNReal NNReal
open Real MeasureTheory ProbabilityTheory
namespace SKRatio.Certificate
open Scalar

lemma abs_v_le (h : ℝ) : |v h| ≤ 1 := by rw [abs_of_pos (v_pos h)]; exact v_le_one h
lemma abs_m_le (h : ℝ) : |m h| ≤ 1 := (abs_lt.mpr (m_bounds h)).le
lemma abs_mv_le (h : ℝ) : |m h*v h| ≤ 1 := by
  rw [abs_mul]
  nlinarith [mul_le_mul (abs_m_le h) (abs_v_le h) (abs_nonneg (v h)) (by norm_num : (0:ℝ) ≤ 1)]

lemma approx_coefficient_bound {β A : ℝ} (hβ : 0 ≤ β) (hb : β ≤ 1/2)
    (hA : 0 ≤ A) (hA1 : A ≤ 1) : |1/2-β^2*A/(64/100-(19/100)*A)| ≤ 1 := by
  have hd : 0 < 64/100-(19/100)*A := by linarith
  have hp : 0 ≤ β^2*A/(64/100-(19/100)*A) := by positivity
  have hu : β^2*A/(64/100-(19/100)*A) ≤ 3/2 := by
    apply (div_le_iff₀ hd).mpr
    have hh : β^2 ≤ (1/4:ℝ) := by nlinarith
    have hh' := mul_le_mul_of_nonneg_right hh hA
    nlinarith
  exact abs_le.mpr ⟨by linarith,by linarith⟩

lemma approxF_bound {β A C Q : ℝ} (hβ : 0 ≤ β) (hb : β ≤ 1/2)
    (hA : 0 ≤ A) (hA1 : A ≤ 1) (hC : 0 ≤ C) (hC1 : C ≤ 1)
    (hQ : 0 ≤ Q) (hQ1 : Q ≤ 1) (x : ℝ) :
    |approxF β A C (β^2+β*x)-Q| ≤ |x|+4 := by
  let h := β^2+β*x
  have hh : |h| ≤ 1/4+|x|/2 := by
    have ht := abs_add_le (β^2) (β*x)
    rw [abs_of_nonneg (sq_nonneg β),abs_mul,abs_of_nonneg hβ] at ht
    have hm := mul_le_mul_of_nonneg_right hb (abs_nonneg x)
    dsimp [h]
    nlinarith
  have hp : |(v h+A)*h| ≤ 2*|h| := by
    rw [abs_mul,abs_of_nonneg (by positivity [v_pos h] : 0 ≤ v h+A)]
    exact mul_le_mul_of_nonneg_right (by linarith [v_le_one h]) (abs_nonneg h)
  have h2 : |2*β^2*(m h*v h)| ≤ 1/2 := by
    rw [abs_mul,abs_of_nonneg (by positivity : 0 ≤ 2*β^2)]
    have ht := mul_le_mul_of_nonneg_left (abs_mv_le h) (by positivity : 0 ≤ 2*β^2)
    nlinarith
  have h3 : |(1/2-β^2*A/(64/100-(19/100)*A))*v h| ≤ 1 := by
    rw [abs_mul]
    simpa using mul_le_mul (approx_coefficient_bound hβ hb hA hA1) (abs_v_le h)
      (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 1)
  have h4 : |(12/100:ℝ)*m h| ≤ 12/100 := by
    rw [abs_mul,abs_of_pos (by norm_num : (0:ℝ) < 12/100)]
    nlinarith [abs_m_le h]
  have h5 : |3*β^2*C*g h| ≤ 3/4 := by
    rw [abs_mul,abs_of_nonneg (by positivity : 0 ≤ 3*β^2*C)]
    have ht := mul_le_mul_of_nonneg_left (abs_g_le_one h) (by positivity : 0 ≤ 3*β^2*C)
    have hh' := mul_le_mul_of_nonneg_left hC1 (by positivity : 0 ≤ 3*β^2)
    nlinarith
  have hsum : |approxF β A C h-Q| ≤ 2*|h|+237/100+Q := by
    unfold approxF
    calc
      _ ≤ |(v h+A)*h+2*β^2*(m h*v h)+(1/2-β^2*A/(64/100-(19/100)*A))*v h+
        (12/100)*m h+3*β^2*C*g h|+|Q| := abs_sub _ _
      _ ≤ ((((|(v h+A)*h|+|2*β^2*(m h*v h)|)+|(1/2-β^2*A/(64/100-(19/100)*A))*v h|)+
        |(12/100)*m h|)+|3*β^2*C*g h|)+|Q| := by
          gcongr
          exact (abs_add_le _ _).trans (add_le_add
            ((abs_add_le _ _).trans (add_le_add
              ((abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)) le_rfl)) le_rfl)
      _ ≤ _ := by rw [abs_of_nonneg hQ]; linarith only [hp,h2,h3,h4,h5]
  change |approxF β A C h-Q| ≤ _
  linarith only [hsum,hh,hQ1]

lemma bounded_center_square {u c : ℝ} (hu : |u| ≤ 1) (hc : 0 ≤ c) (hc1 : c ≤ 1) :
    |(u-c)^2| ≤ 4 := by
  rw [abs_of_nonneg (sq_nonneg _)]
  have h := abs_sub u c
  rw [abs_of_nonneg hc] at h
  have hh : |u-c| ≤ 2 := by linarith
  simpa only [sq_abs,show (2:ℝ)^2=4 by norm_num] using (sq_le_sq₀ (abs_nonneg (u-c)) (by norm_num : (0:ℝ) ≤ 2)).mpr hh

lemma scalarFunction_bound {β A C M Q : ℝ} (hβ : 0 ≤ β) (hb : β ≤ 1/2)
    (hA : 0 ≤ A) (hA1 : A ≤ 1) (hC : 0 ≤ C) (hC1 : C ≤ 1)
    (hM : 0 ≤ M) (hM1 : M ≤ 1) (hQ : 0 ≤ Q) (hQ1 : Q ≤ 1)
    (k : ℕ) (x : ℝ) : |scalarFunction β A C M Q k (β^2+β*x)| ≤ 32*(1+x^2) := by
  let h := β^2+β*x
  have ht : (4:ℝ) ≤ 32*(1+x^2) := by nlinarith [sq_nonneg x]
  have hv := v_le_one h
  have hv0 := (v_pos h).le
  have hL := multiplier_pos h
  have hL0 := multiplier_strict_pos h
  have hm := m_bounds h
  have hd : 0 < 2-m h := by linarith
  have hd1 : 1 ≤ 2-m h := by linarith
  have hv2 : v h^2 ≤ 1 := by nlinarith
  have hs : |(approxF β A C h-Q)^2| ≤ 32*(1+x^2) := by
    have hh := approxF_bound hβ hb hA hA1 hC hC1 hQ hQ1 x
    rw [abs_of_nonneg (sq_nonneg _)]
    have hs := (sq_le_sq₀ (abs_nonneg _) (by positivity : 0 ≤ |x|+4)).mpr hh
    rw [sq_abs] at hs
    nlinarith [sq_nonneg (|x|-1),sq_abs x]
  unfold scalarFunction
  split
  · exact (abs_v_le h).trans ((by norm_num : (1:ℝ) ≤ 4).trans ht)
  · exact (abs_g_le_one h).trans ((by norm_num : (1:ℝ) ≤ 4).trans ht)
  · exact (abs_mv_le h).trans ((by norm_num : (1:ℝ) ≤ 4).trans ht)
  · rw [abs_of_nonneg (rho_nonneg h)]
    exact (rho_le_one h).trans ((by norm_num : (1:ℝ) ≤ 4).trans ht)
  · exact (bounded_center_square (abs_v_le h) hA hA1).trans ht
  · exact (bounded_center_square (abs_g_le_one h) hC hC1).trans ht
  · exact (bounded_center_square (abs_mv_le h) hM hM1).trans ht
  · exact hs
  · apply le_trans _ ht
    rw [abs_of_nonneg (by positivity : 0 ≤ (1+v h)^2/multiplier h/16)]
    apply (div_le_iff₀ (by norm_num : (0:ℝ) < 16)).mpr
    apply (div_le_iff₀ hL0).mpr
    nlinarith
  · apply le_trans _ ht
    rw [abs_of_nonneg (by positivity : 0 ≤ v h^2/multiplier h/16)]
    apply (div_le_iff₀ (by norm_num : (0:ℝ) < 16)).mpr
    apply (div_le_iff₀ hL0).mpr
    nlinarith
  · apply le_trans _ ht
    rw [abs_of_nonneg (by positivity : 0 ≤ v h^2/(2-m h)/4)]
    apply (div_le_iff₀ (by norm_num : (0:ℝ) < 4)).mpr
    apply (div_le_iff₀ hd).mpr
    nlinarith
  · apply le_trans _ ht
    rw [abs_of_nonneg (by positivity : 0 ≤ v h^2/(2-m h)^2/4)]
    apply (div_le_iff₀ (by norm_num : (0:ℝ) < 4)).mpr
    apply (div_le_iff₀ (sq_pos_of_pos hd)).mpr
    nlinarith
  · apply le_trans _ ht
    have hm' : 0 ≤ 1+m h := by linarith
    rw [abs_of_nonneg (by positivity : 0 ≤ v h*(1+m h)/4)]
    have ht' := mul_le_mul hv (show 1+m h ≤ 2 by linarith) hm' (by norm_num : (0:ℝ) ≤ 1)
    nlinarith

end SKRatio.Certificate

end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Variational_ScalarTemperature
attribute [-instance] _root_.OAI.SKRatio.Observation.History.historyMeasurable _root_.OAI.SKRatio.Observation.History.historyTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Topology NNReal ENNReal
open MeasureTheory ProbabilityTheory Real Set
namespace SKRatio.Scalar

lemma variance_ne_zero {β : ℝ} (hβ : 0 < β) : variance β ≠ 0 := by
  intro hz
  have he := congrArg (fun t : ℝ≥0 => (t:ℝ)) hz
  simp only [variance_coe,NNReal.coe_zero] at he
  nlinarith

lemma field_pdf {β : ℝ} (hβ : 0 < β) (h : ℝ) :
    gaussianPDFReal (β^2) (variance β) h =
      (sqrt (2*Real.pi)*β)⁻¹*exp (-β^2/2+h-h^2/(2*β^2)) := by
  unfold gaussianPDFReal
  rw [variance_coe,sqrt_mul (by positivity : 0 ≤ 2*Real.pi),sqrt_sq hβ.le]
  congr 2
  field_simp
  ring

lemma thermal_prefactor_deriv (β : ℝ) :
    HasDerivAt (fun t : ℝ => t*exp (-t^2/2))
      ((1-β^2)*exp (-β^2/2)) β := by
  convert! (hasDerivAt_id β).mul
    ((((hasDerivAt_id β).pow 2).neg.div_const 2).exp) using 1
  all_goals try with_reducible_and_instances rfl
  simp only [Nat.cast_ofNat,show 2-1=1 from rfl,pow_one,id_eq,Pi.neg_apply,Pi.pow_apply]
  ring

lemma thermal_prefactor_mono {β z : ℝ} (hβ : 0 ≤ β) (hβz : β ≤ z) (hz : z ≤ 1) :
    β*exp (-β^2/2) ≤ z*exp (-z^2/2) := by
  apply (monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc (0:ℝ) 1)
    (fun x _ => (thermal_prefactor_deriv x).continuousAt.continuousWithinAt)
    (fun x _ => (thermal_prefactor_deriv x).hasDerivWithinAt) ?_) ⟨hβ,le_trans hβz hz⟩ ⟨le_trans hβ hβz,hz⟩ hβz
  intro x hx
  have hx' : x ∈ Icc (0:ℝ) 1 := interior_subset hx
  exact mul_nonneg (by nlinarith [hx'.1,hx'.2]) (exp_pos _).le

lemma scaled_field_pdf {β : ℝ} (hβ : 0 < β) (h : ℝ) :
    β^2*gaussianPDFReal (β^2) (variance β) h =
      (sqrt (2*Real.pi))⁻¹*(β*exp (-β^2/2))*exp (h-h^2/(2*β^2)) := by
  rw [field_pdf hβ]
  have he : -β^2/2+h-h^2/(2*β^2) = -β^2/2+(h-h^2/(2*β^2)) := by ring
  rw [he,exp_add]
  field_simp

lemma scaled_field_pdf_mono {β z : ℝ} (hβ : 0 < β) (hβz : β ≤ z) (hz : z ≤ 1) (h : ℝ) :
    β^2*gaussianPDFReal (β^2) (variance β) h ≤
      z^2*gaussianPDFReal (z^2) (variance z) h := by
  have hzpos : 0 < z := lt_of_lt_of_le hβ hβz
  rw [scaled_field_pdf hβ,scaled_field_pdf hzpos]
  have hq : h^2/(2*z^2) ≤ h^2/(2*β^2) := by
    apply div_le_div_of_nonneg_left (sq_nonneg h) (by positivity)
    nlinarith
  apply mul_le_mul
  · exact mul_le_mul_of_nonneg_left (thermal_prefactor_mono hβ.le hβz hz) (by positivity)
  · exact exp_le_exp.mpr (by linarith only [hq])
  · exact (exp_pos _).le
  · positivity

theorem scaled_fieldLaw_mono {β z : ℝ} (hβ : 0 < β) (hβz : β ≤ z) (hz : z ≤ 1) :
    ENNReal.ofReal (β^2) • fieldLaw β ≤ ENNReal.ofReal (z^2) • fieldLaw z := by
  have hzpos : 0 < z := lt_of_lt_of_le hβ hβz
  rw [fieldLaw,fieldLaw,gaussianReal_of_var_ne_zero _ (variance_ne_zero hβ),
    gaussianReal_of_var_ne_zero _ (variance_ne_zero hzpos),
    ←withDensity_smul' _ _ ENNReal.ofReal_ne_top,←withDensity_smul' _ _ ENNReal.ofReal_ne_top]
  apply withDensity_mono
  apply ae_of_all
  intro h
  simp only [Pi.smul_apply,smul_eq_mul,gaussianPDF,←ENNReal.ofReal_mul (sq_nonneg β),
    ←ENNReal.ofReal_mul (sq_nonneg z)]
  exact ENNReal.ofReal_le_ofReal (scaled_field_pdf_mono hβ hβz hz h)

lemma scaled_integral_mono {β z : ℝ} (hβ : 0 < β) (hβz : β ≤ z) (hz : z ≤ 1)
    {f : ℝ → ℝ} (hf : ∀ h, 0 ≤ f h) (hfi : Integrable f (fieldLaw z)) :
    β^2*(∫ h, f h ∂fieldLaw β) ≤ z^2*(∫ h, f h ∂fieldLaw z) := by
  have h := integral_mono_measure (scaled_fieldLaw_mono hβ hβz hz)
    (ae_of_all _ hf) (hfi.smul_measure ENNReal.ofReal_ne_top)
  simpa only [integral_smul_measure,ENNReal.toReal_ofReal (sq_nonneg _),smul_eq_mul] using h

end SKRatio.Scalar

end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Variational_ScalarVariance
attribute [-instance] _root_.OAI.SKRatio.Observation.History.historyBorel _root_.OAI.SKRatio.Observation.History.historyMeasurable _root_.OAI.SKRatio.Observation.History.historySecondCountable _root_.OAI.SKRatio.Observation.History.historyTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Topology ENNReal NNReal
open MeasureTheory ProbabilityTheory Real
namespace SKRatio.Scalar

section Norm
variable {μ : Measure ℝ}

lemma l2Norm_add {f g : ℝ → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    l2Norm μ (fun x => f x+g x) ≤ l2Norm μ f+l2Norm μ g := by
  have he := integral_square_add hf hg 1 1
  simp only [one_mul,one_pow,mul_one] at he
  have hcs := (le_abs_self _).trans (abs_integral_mul_le hf hg)
  apply (sq_le_sq₀ (l2Norm_nonneg _) (add_nonneg (l2Norm_nonneg _) (l2Norm_nonneg _))).mp
  rw [l2Norm_sq,he]
  nlinarith only [hcs,l2Norm_sq (μ := μ) f,l2Norm_sq (μ := μ) g]

lemma l2Norm_const_mul (f : ℝ → ℝ) (c : ℝ) :
    l2Norm μ (fun x => c*f x) = |c| *l2Norm μ f := by
  apply (sq_eq_sq₀ (l2Norm_nonneg _) (mul_nonneg (abs_nonneg _) (l2Norm_nonneg _))).mp
  simp only [l2Norm_sq,mul_pow,integral_const_mul,sq_abs]

end Norm
section Probability
variable {μ ν : Measure ℝ} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]

omit [IsProbabilityMeasure μ] in
lemma sd_sq (f : ℝ → ℝ) : sd μ f^2 = ∫ x, centered μ f x^2 ∂μ := l2Norm_sq _

lemma sd_sq_eq {f : ℝ → ℝ} (hf : MemLp f 2 μ) :
    sd μ f^2 = (∫ x, f x^2 ∂μ)-(∫ x, f x ∂μ)^2 := by
  rw [sd_sq]
  exact integral_centered_sq hf

lemma square_center_expansion {f : ℝ → ℝ} (hf : MemLp f 2 μ) (c : ℝ) :
    ∫ x, (f x-c)^2 ∂μ = sd μ f^2+((∫ x, f x ∂μ)-c)^2 := by
  have he := integral_square_add hf (memLp_const (1:ℝ)) 1 (-c)
  simp only [one_mul,one_pow,mul_one,one_mul,←sub_eq_add_neg,neg_sq,
    integral_const,probReal_univ,smul_eq_mul,one_mul] at he
  rw [he,sd_sq_eq hf]
  ring

lemma sd_min_center {f : ℝ → ℝ} (hf : MemLp f 2 μ) (c : ℝ) :
    sd μ f^2 ≤ ∫ x, (f x-c)^2 ∂μ := by
  rw [square_center_expansion hf c]
  exact le_add_of_nonneg_right (sq_nonneg _)

omit [IsProbabilityMeasure μ] in
lemma centered_add {f g : ℝ → ℝ} (hf : Integrable f μ) (hg : Integrable g μ) :
    centered μ (fun x => f x+g x) = fun x => centered μ f x+centered μ g x := by
  ext x
  simp only [centered,integral_add hf hg]
  ring

omit [IsProbabilityMeasure μ] in
lemma centered_const_mul (f : ℝ → ℝ) (c : ℝ) :
    centered μ (fun x => c*f x) = fun x => c*centered μ f x := by
  ext x
  simp only [centered,integral_const_mul]
  ring

lemma sd_add {f g : ℝ → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    sd μ (fun x => f x+g x) ≤ sd μ f+sd μ g := by
  unfold sd
  rw [centered_add (hf.integrable (by norm_num)) (hg.integrable (by norm_num))]
  exact l2Norm_add (memLp_centered hf) (memLp_centered hg)

omit [IsProbabilityMeasure μ] in
lemma sd_const_mul (f : ℝ → ℝ) (c : ℝ) :
    sd μ (fun x => c*f x) = |c| *sd μ f := by
  unfold sd
  rw [centered_const_mul,l2Norm_const_mul]

lemma sd_sub {f g : ℝ → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    sd μ (fun x => f x-g x) ≤ sd μ f+sd μ g := by
  have he (x : ℝ) : f x-g x = f x+(-1)*g x := by ring
  simp_rw [he]
  have hh := sd_add hf (hg.const_mul (-1))
  simpa only [sd_const_mul,abs_neg,abs_one,one_mul] using hh

lemma abs_sd_sub_le {f g : ℝ → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    |sd μ f-sd μ g| ≤ sd μ (fun x => f x-g x) := by
  have h1 := sd_add (hf.sub hg) hg
  have h2 := sd_sub hf (hf.sub hg)
  simp only [Pi.sub_apply,sub_add_cancel,sub_sub_cancel] at h1 h2
  change sd μ f ≤ sd μ (fun x => f x-g x)+sd μ g at h1
  change sd μ g ≤ sd μ f+sd μ (fun x => f x-g x) at h2
  exact abs_le.mpr ⟨by linarith,by linarith⟩

lemma sd_mono_measure {C : ℝ} (hC : 0 ≤ C)
    (hμν : μ ≤ ENNReal.ofReal C • ν)
    {f : ℝ → ℝ} (hf : MemLp f 2 μ) (hf' : MemLp f 2 ν) :
    sd μ f^2 ≤ C*sd ν f^2 := by
  calc
    sd μ f^2 ≤ ∫ x, (f x-(∫ y, f y ∂ν))^2 ∂μ := sd_min_center hf _
    _ ≤ ∫ x, (f x-(∫ y, f y ∂ν))^2 ∂(ENNReal.ofReal C • ν) :=
      integral_mono_measure hμν (ae_of_all _ (fun _ => sq_nonneg _))
        ((memLp_centered hf').integrable_sq.smul_measure ENNReal.ofReal_ne_top)
    _ = C*sd ν f^2 := by
      rw [integral_smul_measure,ENNReal.toReal_ofReal hC,smul_eq_mul,sd_sq]
      rfl

lemma sd_mono_measure_sqrt {C : ℝ} (hC : 0 ≤ C)
    (hμν : μ ≤ ENNReal.ofReal C • ν)
    {f : ℝ → ℝ} (hf : MemLp f 2 μ) (hf' : MemLp f 2 ν) :
    sd μ f ≤ sqrt C*sd ν f := by
  apply (sq_le_sq₀ (sd_nonneg _) (mul_nonneg (sqrt_nonneg _) (sd_nonneg _))).mp
  rw [mul_pow,sq_sqrt hC]
  exact sd_mono_measure hC hμν hf hf'

lemma weighted_sd_mono_measure {B Z : ℝ} (hB : 0 ≤ B) (hZ : 0 ≤ Z)
    (hμν : ENNReal.ofReal B • μ ≤ ENNReal.ofReal Z • ν)
    {f : ℝ → ℝ} (hf : MemLp f 2 μ) (hf' : MemLp f 2 ν) :
    B*sd μ f^2 ≤ Z*sd ν f^2 := by
  calc
    B*sd μ f^2 ≤ B*(∫ x, (f x-(∫ y, f y ∂ν))^2 ∂μ) :=
      mul_le_mul_of_nonneg_left (sd_min_center hf _) hB
    _ = ∫ x, (f x-(∫ y, f y ∂ν))^2 ∂(ENNReal.ofReal B • μ) := by
      rw [integral_smul_measure,ENNReal.toReal_ofReal hB,smul_eq_mul]
    _ ≤ ∫ x, (f x-(∫ y, f y ∂ν))^2 ∂(ENNReal.ofReal Z • ν) :=
      integral_mono_measure hμν (ae_of_all _ (fun _ => sq_nonneg _))
        ((memLp_centered hf').integrable_sq.smul_measure ENNReal.ofReal_ne_top)
    _ = Z*sd ν f^2 := by
      rw [integral_smul_measure,ENNReal.toReal_ofReal hZ,smul_eq_mul,sd_sq]
      rfl
end Probability

lemma weighted_sd_temperature_mono {β z : ℝ} (hβ : 0 < β) (hβz : β ≤ z) (hz : z ≤ 1)
    {f : ℝ → ℝ} (hf : MemLp f 2 (fieldLaw β)) (hf' : MemLp f 2 (fieldLaw z)) :
    β^2*sd (fieldLaw β) f^2 ≤ z^2*sd (fieldLaw z) f^2 :=
  weighted_sd_mono_measure (sq_nonneg _) (sq_nonneg _)
    (scaled_fieldLaw_mono hβ hβz hz) hf hf'

lemma weighted_sd_temperature_mono' {β z : ℝ} (hβ : 0 < β) (hβz : β ≤ z) (hz : z ≤ 1)
    {f : ℝ → ℝ} (hf : MemLp f 2 (fieldLaw β)) (hf' : MemLp f 2 (fieldLaw z)) :
    β*sd (fieldLaw β) f ≤ z*sd (fieldLaw z) f := by
  apply (sq_le_sq₀ (mul_nonneg hβ.le (sd_nonneg _))
    (mul_nonneg (hβ.le.trans hβz) (sd_nonneg _))).mp
  simpa only [mul_pow] using weighted_sd_temperature_mono hβ hβz hz hf hf'

lemma weighted_mv_temperature_mono {β z : ℝ} (hβ : 0 < β) (hβz : β ≤ z) (hz : z ≤ 1) :
    β^2*(∫ h, m h*v h ∂fieldLaw β) ≤ z^2*(∫ h, m h*v h ∂fieldLaw z) := by
  simp_rw [mean_mv_eq_mean_m_sq_v]
  apply scaled_integral_mono hβ hβz hz (fun h => mul_nonneg (sq_nonneg _) (v_pos h).le)
  apply (integrable_const (1:ℝ)).mono'
    ((continuous_m.pow 2).mul continuous_v).aestronglyMeasurable
  apply ae_of_all
  intro h
  change |m h^2*v h| ≤ 1
  rw [abs_of_nonneg (mul_nonneg (sq_nonneg _) (v_pos h).le)]
  exact (mul_le_mul_of_nonneg_right (tanh_sq_lt_one h).le (v_pos h).le).trans (by simpa using v_le_one h)

lemma weighted_R_temperature_mono {β z : ℝ} (hβ : 0 < β) (hβz : β ≤ z) (hz : z ≤ 1) :
    β^2*R β ≤ z^2*R z := by
  apply scaled_integral_mono hβ hβz hz rho_nonneg
  exact integrable_rho

end SKRatio.Scalar

end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Certificates_CertifiedCoefficient
attribute [-instance] _root_.OAI.SKRatio.Observation.History.historyMeasurable _root_.OAI.SKRatio.Observation.History.historyTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Topology ENNReal NNReal
open Real MeasureTheory ProbabilityTheory
namespace SKRatio.Certificate
open Scalar

lemma memLp_approxF (β A C : ℝ) : MemLp (approxF β A C) 2 (fieldLaw β) := by
  convert! (((((memLp_field_v β).add ((memLp_field β).const_mul A)).add
      (memLp_mv.const_mul (2*β^2))).add (memLp_v.const_mul
        (1/2-β^2*A/(64/100-(19/100)*A)))).add
      (memLp_m.const_mul (12/100:ℝ))).add (memLp_g.const_mul (3*β^2*C)) using 1
  all_goals try with_reducible_and_instances rfl
  ext h
  dsimp [approxF]
  ring

lemma sd_le_of_center {μ : Measure ℝ} [IsProbabilityMeasure μ] {f : ℝ → ℝ}
    (hf : MemLp f 2 μ) {c B : ℝ} (hB : 0 ≤ B)
    (hc : (∫ x, (f x-c)^2 ∂μ) ≤ B^2) : sd μ f ≤ B := by
  have ht := (sd_min_center hf c).trans hc
  nlinarith only [ht,sd_nonneg (μ := μ) f,hB]

lemma sd_unit {μ : Measure ℝ} [IsProbabilityMeasure μ] {f : ℝ → ℝ}
    (hf : MemLp f 2 μ) (hb : ∀ h, |f h| ≤ 1) : sd μ f ≤ 1 := by
  apply sd_le_of_center hf (c := 0) (by norm_num)
  simp only [sub_zero,one_pow]
  have ht := integral_mono hf.integrable_sq (integrable_const (μ := μ) (1:ℝ))
    (fun h => by nlinarith [hb h,sq_abs (f h),abs_nonneg (f h)])
  simpa only [integral_const,probReal_univ,smul_eq_mul,one_mul] using ht

lemma sd_field (β : ℝ) : sd (fieldLaw β) (fun h : ℝ => h) = |β| := by
  have hh := variance_id_gaussianReal (μ := β^2) (v := variance β)
  rw [variance_eq_integral measurable_id.aemeasurable] at hh
  change ∫ h, (h-(∫ t, t ∂fieldLaw β))^2 ∂fieldLaw β = _ at hh
  rw [variance_coe] at hh
  unfold sd l2Norm centered
  rw [hh,sqrt_sq_eq_abs]

lemma ratio_coefficient_error {A B : ℝ} (hA : 0 ≤ A) (hA1 : A ≤ 1)
    (hB : 0 ≤ B) (hB1 : B ≤ 1) :
    |A/(64/100-(19/100)*A)-B/(64/100-(19/100)*B)| ≤ 4*|A-B| := by
  have hDA : 45/100 ≤ 64/100-(19/100)*A := by linarith
  have hDB : 45/100 ≤ 64/100-(19/100)*B := by linarith
  have hDA0 : 0 < 64/100-(19/100)*A := by linarith
  have hDB0 : 0 < 64/100-(19/100)*B := by linarith
  have he : A/(64/100-(19/100)*A)-B/(64/100-(19/100)*B) =
      (64/100)*(A-B)/((64/100-(19/100)*A)*(64/100-(19/100)*B)) := by
    rw [div_sub_div A B hDA0.ne' hDB0.ne']
    congr 1
    ring
  rw [he,abs_div,abs_mul,abs_of_pos (by norm_num : (0:ℝ) < 64/100),
    abs_of_pos (mul_pos hDA0 hDB0)]
  apply (div_le_iff₀ (mul_pos hDA0 hDB0)).mpr
  have hp : (104/625:ℝ) ≤
      (64/100-(19/100)*A)*(64/100-(19/100)*B) := by
    nlinarith only [hA1,hB1,mul_nonneg hA hB]
  have hh := mul_le_mul_of_nonneg_right hp (abs_nonneg (A-B))
  nlinarith only [hh,abs_nonneg (A-B)]

lemma approxF_error {β A C : ℝ} (hβ : 0 ≤ β) (hb : β ≤ 1/2)
    (hA : 0 ≤ A) (hA1 : A ≤ 1) :
    sd (fieldLaw β) (F β) ≤ sd (fieldLaw β) (approxF β A C)+
      2*|a β-A|+|G β-C| := by
  let ca := a β-A
  let cv := β^2*(A/(64/100-(19/100)*A)-a β/l β)
  let cg := 3*β^2*(G β-C)
  have he (h : ℝ) : F β h-approxF β A C h = ca*h+cv*v h+cg*g h := by
    dsimp [F,approxF,ca,cv,cg]
    ring
  have hi : MemLp (fun h : ℝ => ca*h) 2 (fieldLaw β) := (memLp_field β).const_mul ca
  have hiv : MemLp (fun h => cv*v h) 2 (fieldLaw β) := memLp_v.const_mul cv
  have hig : MemLp (fun h => cg*g h) 2 (fieldLaw β) := memLp_g.const_mul cg
  have h1 := sd_add hi hiv
  have h2 := sd_add (hi.add hiv) hig
  have hdiff := (le_abs_self _).trans (abs_sd_sub_le (memLp_F β) (memLp_approxF β A C))
  simp_rw [he] at hdiff
  have hid : sd (fieldLaw β) (fun h : ℝ => ca*h) = |ca| *β := by
    change sd (fieldLaw β) (fun h => ca*(fun t : ℝ => t) h) = _
    rw [sd_const_mul,sd_field,abs_of_nonneg hβ]
  simp only [Pi.add_def,sd_const_mul,hid] at h1 h2
  have hcv : |cv| ≤ |a β-A| := by
    have hh := ratio_coefficient_error (a_nonneg β) (a_le_one β) hA hA1
    rw [←l_eq,abs_sub_comm] at hh
    dsimp [cv]
    rw [abs_mul,abs_of_nonneg (sq_nonneg β)]
    have hp := mul_le_mul_of_nonneg_left hh (sq_nonneg β)
    have hβ2 : β^2 ≤ (1/4:ℝ) := by nlinarith
    have hh' := mul_le_mul_of_nonneg_right hβ2 (abs_nonneg (a β-A))
    nlinarith only [hp,hh']
  have hcg : |cg| ≤ |G β-C| := by
    dsimp [cg]
    rw [abs_mul,abs_of_nonneg (by positivity : 0 ≤ 3*β^2)]
    have hβ2 : 3*β^2 ≤ 1 := by nlinarith
    nlinarith only [mul_le_mul_of_nonneg_right hβ2 (abs_nonneg (G β-C))]
  have hva := sd_unit (μ := fieldLaw β) memLp_v abs_v_le
  have hga := sd_unit (μ := fieldLaw β) memLp_g abs_g_le_one
  have hpv := mul_le_mul hcv hva (sd_nonneg (μ := fieldLaw β) v) (abs_nonneg (a β-A))
  have hpg := mul_le_mul hcg hga (sd_nonneg (μ := fieldLaw β) g) (abs_nonneg (G β-C))
  have hpa := mul_le_mul_of_nonneg_left hb (abs_nonneg ca)
  dsimp [ca] at h1 h2 hpa
  nlinarith only [hdiff,h1,h2,hpv,hpg,hpa,abs_nonneg (a β-A)]

end SKRatio.Certificate

end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Variational_ScalarDensity
attribute [-instance] _root_.OAI.SKRatio.Observation.History.historyMeasurable _root_.OAI.SKRatio.Observation.History.historyTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Topology ENNReal NNReal
open MeasureTheory ProbabilityTheory Real
namespace SKRatio.Scalar

lemma field_pdf_ratio {β z : ℝ} (hβ : 0 < β) (hz : 0 < z) (h : ℝ) :
    gaussianPDFReal (β^2) (variance β) h =
      (z/β)*exp ((z^2-β^2)/2+(1/(2*z^2)-1/(2*β^2))*h^2)*
      gaussianPDFReal (z^2) (variance z) h := by
  rw [field_pdf hβ,field_pdf hz]
  have he : (z^2-β^2)/2+(1/(2*z^2)-1/(2*β^2))*h^2 +
      (-z^2/2+h-h^2/(2*z^2)) = -β^2/2+h-h^2/(2*β^2) := by ring
  calc
    _ = (z/β)*(sqrt (2*Real.pi)*z)⁻¹*exp (-β^2/2+h-h^2/(2*β^2)) := by
      field_simp
    _ = _ := by rw [←he,exp_add]; ring

lemma densityFactor_pos {β z : ℝ} (hβ : 0 < β) (hz : 0 < z) :
    0 < densityFactor β z := mul_pos (div_pos hz hβ) (exp_pos _)

lemma field_pdf_le_factor {β z : ℝ} (hβ : 0 < β) (hβz : β ≤ z) (h : ℝ) :
    gaussianPDFReal (β^2) (variance β) h ≤
      densityFactor β z*gaussianPDFReal (z^2) (variance z) h := by
  have hz : 0 < z := hβ.trans_le hβz
  rw [field_pdf_ratio hβ hz]
  have hi : 1/(2*z^2) ≤ 1/(2*β^2) := by
    apply one_div_le_one_div_of_le (by positivity)
    nlinarith
  apply mul_le_mul_of_nonneg_right _ (gaussianPDFReal_nonneg _ _ _)
  apply mul_le_mul_of_nonneg_left _ (div_pos hz hβ).le
  apply exp_le_exp.mpr
  have hh := mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hi) (sq_nonneg h)
  linarith

lemma densityFactor_mono_left {j β z : ℝ} (hj : 0 < j) (hjβ : j ≤ β) (hβz : β ≤ z) :
    densityFactor β z ≤ densityFactor j z := by
  have hβ : 0 < β := hj.trans_le hjβ
  have hz : 0 < z := hβ.trans_le hβz
  apply mul_le_mul
  · exact div_le_div_of_nonneg_left hz.le hj hjβ
  · apply exp_le_exp.mpr
    nlinarith
  · exact (exp_pos _).le
  · exact (div_pos hz hj).le

lemma fieldLaw_le_factor {β z : ℝ} (hβ : 0 < β) (hβz : β ≤ z) :
    fieldLaw β ≤ ENNReal.ofReal (densityFactor β z) • fieldLaw z := by
  have hz : 0 < z := hβ.trans_le hβz
  rw [fieldLaw,fieldLaw,gaussianReal_of_var_ne_zero _ (variance_ne_zero hβ),
    gaussianReal_of_var_ne_zero _ (variance_ne_zero hz),
    ←withDensity_smul' _ _ ENNReal.ofReal_ne_top]
  apply withDensity_mono
  apply ae_of_all
  intro h
  simp only [Pi.smul_apply,smul_eq_mul,gaussianPDF,
    ←ENNReal.ofReal_mul (densityFactor_pos hβ hz).le]
  exact ENNReal.ofReal_le_ofReal (field_pdf_le_factor hβ hβz h)

lemma fieldLaw_le_interval_factor {j β z : ℝ} (hj : 0 < j) (hjβ : j ≤ β) (hβz : β ≤ z) :
    fieldLaw β ≤ ENNReal.ofReal (densityFactor j z) • fieldLaw z := by
  apply (fieldLaw_le_factor (hj.trans_le hjβ) hβz).trans
  intro s
  simp only [Measure.smul_apply,smul_eq_mul]
  exact mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal (densityFactor_mono_left hj hjβ hβz)) (bot_le : (0:ENNReal) ≤ _)

lemma sd_temperature_interval_bound {j β z : ℝ} (hj : 0 < j) (hjβ : j ≤ β) (hβz : β ≤ z)
    {f : ℝ → ℝ} (hf : MemLp f 2 (fieldLaw β)) (hf' : MemLp f 2 (fieldLaw z)) :
    sd (fieldLaw β) f ≤ sqrt (densityFactor j z)*sd (fieldLaw z) f :=
  sd_mono_measure_sqrt (densityFactor_pos hj (hj.trans_le (hjβ.trans hβz))).le
    (fieldLaw_le_interval_factor hj hjβ hβz) hf hf'

end SKRatio.Scalar

end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Variational_ScalarMonotone
attribute [-instance] _root_.OAI.SKRatio.Observation.History.historyBorel _root_.OAI.SKRatio.Observation.History.historyMeasurable _root_.OAI.SKRatio.Observation.History.historySecondCountable _root_.OAI.SKRatio.Observation.History.historyTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Topology ENNReal NNReal
open MeasureTheory ProbabilityTheory Real
namespace SKRatio.Scalar

section Covariance
variable {μ : Measure ℝ} [IsProbabilityMeasure μ]

lemma covariance_nonpos_of_pairwise {f r : ℝ → ℝ}
    (hf : Integrable f μ) (hr : Integrable r μ)
    (hfr : Integrable (fun x => f x*r x) μ)
    (hsign : ∀ x y, (f x-f y)*(r x-r y) ≤ 0) :
    (∫ x, f x*r x ∂μ) ≤ (∫ x, f x ∂μ)*(∫ x, r x ∂μ) := by
  have hpoint (x : ℝ) :
      f x*r x-f x*(∫ y, r y ∂μ)-r x*(∫ y, f y ∂μ)+(∫ y, f y*r y ∂μ) ≤ 0 := by
    have hc1 : Integrable (fun y => f x*r x-f x*r y) μ :=
      (integrable_const _).sub (hr.const_mul _)
    have hc : Integrable (fun y => f x*r x-f x*r y-r x*f y) μ :=
      hc1.sub (hf.const_mul _)
    have he (y : ℝ) : (f x-f y)*(r x-r y) = f x*r x-f x*r y-r x*f y+f y*r y := by ring
    have hi := integral_nonpos (μ := μ) (hsign x)
    simp_rw [he] at hi
    rw [integral_add hc hfr,
      integral_sub hc1 (hf.const_mul _),
      integral_sub (integrable_const _) (hr.const_mul _),integral_const_mul,integral_const_mul,
      integral_const] at hi
    simpa only [integral_const_mul,probReal_univ,smul_eq_mul,one_mul] using hi
  have hh := integral_nonpos (μ := μ) hpoint
  have hc1 : Integrable (fun x => f x*r x-f x*(∫ y, r y ∂μ)) μ := hfr.sub (hf.mul_const _)
  have hc : Integrable (fun x => f x*r x-f x*(∫ y, r y ∂μ)-r x*(∫ y, f y ∂μ)) μ :=
    hc1.sub (hr.mul_const _)
  rw [integral_add hc (integrable_const _),
    integral_sub hc1 (hr.mul_const _),
    integral_sub hfr (hf.mul_const _),integral_mul_const,integral_mul_const,integral_const] at hh
  simp only [probReal_univ,smul_eq_mul,one_mul] at hh
  nlinarith only [hh]
end Covariance

lemma continuous_likelihood (β z : ℝ) : Continuous (likelihood β z) := by
  unfold likelihood
  fun_prop

lemma likelihood_pos {β z : ℝ} (hβ : 0 < β) (hz : 0 < z) (h : ℝ) :
    0 < likelihood β z h := mul_pos (div_pos hβ hz) (exp_pos _)

lemma fieldLaw_withDensity_likelihood {β z : ℝ} (hβ : 0 < β) (hz : 0 < z) :
    (fieldLaw β).withDensity (fun h => ENNReal.ofReal (likelihood β z h)) = fieldLaw z := by
  rw [fieldLaw,fieldLaw,gaussianReal_of_var_ne_zero _ (variance_ne_zero hβ),
    gaussianReal_of_var_ne_zero _ (variance_ne_zero hz),
    ←withDensity_mul _ (measurable_gaussianPDF _ _) ((continuous_likelihood β z).measurable.ennreal_ofReal)]
  apply withDensity_congr_ae
  apply ae_of_all
  intro h
  simp only [Pi.mul_apply,gaussianPDF,←ENNReal.ofReal_mul (gaussianPDFReal_nonneg _ _ _)]
  congr 1
  exact (mul_comm _ _).trans (field_pdf_ratio hz hβ h).symm

lemma integral_likelihood {β z : ℝ} (hβ : 0 < β) (hz : 0 < z) :
    ∫ h, likelihood β z h ∂fieldLaw β = 1 := by
  have hh := integral_const (μ := fieldLaw z) (1:ℝ)
  rw [←fieldLaw_withDensity_likelihood hβ hz,
    integral_withDensity_eq_integral_toReal_smul ((continuous_likelihood β z).measurable.ennreal_ofReal)
      (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))] at hh
  simpa only [ENNReal.toReal_ofReal (likelihood_pos hβ hz _).le,smul_eq_mul,mul_one,
    fieldLaw_withDensity_likelihood hβ hz,probReal_univ,one_mul] using hh

lemma likelihood_integrable_iff {β z : ℝ} (hβ : 0 < β) (hz : 0 < z) (f : ℝ → ℝ) :
    Integrable f (fieldLaw z) ↔ Integrable (fun h => f h*likelihood β z h) (fieldLaw β) := by
  rw [←fieldLaw_withDensity_likelihood hβ hz,
    integrable_withDensity_iff ((continuous_likelihood β z).measurable.ennreal_ofReal)
      (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (likelihood_pos hβ hz _).le]

lemma integral_mul_likelihood {β z : ℝ} (hβ : 0 < β) (hz : 0 < z) (f : ℝ → ℝ) :
    ∫ h, f h*likelihood β z h ∂fieldLaw β = ∫ h, f h ∂fieldLaw z := by
  rw [←fieldLaw_withDensity_likelihood hβ hz,
    integral_withDensity_eq_integral_toReal_smul ((continuous_likelihood β z).measurable.ennreal_ofReal)
      (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (likelihood_pos hβ hz _).le,smul_eq_mul,mul_comm]

lemma likelihood_mono_sq {β z : ℝ} (hβ : 0 < β) (hβz : β ≤ z) {x y : ℝ} (hxy : x^2 ≤ y^2) :
    likelihood β z x ≤ likelihood β z y := by
  have hz : 0 < z := hβ.trans_le hβz
  have hi : 1/(2*z^2) ≤ 1/(2*β^2) := by
    apply one_div_le_one_div_of_le (by positivity)
    nlinarith
  unfold likelihood
  apply mul_le_mul_of_nonneg_left _ (div_pos hβ hz).le
  apply exp_le_exp.mpr
  nlinarith only [mul_le_mul_of_nonneg_left hxy (sub_nonneg.mpr hi)]

lemma integral_temperature_antitone {β z : ℝ} (hβ : 0 < β) (hβz : β ≤ z)
    {f : ℝ → ℝ} (hf : Integrable f (fieldLaw β)) (hf' : Integrable f (fieldLaw z))
    (hanti : ∀ x y : ℝ, x^2 ≤ y^2 → f y ≤ f x) :
    ∫ h, f h ∂fieldLaw z ≤ ∫ h, f h ∂fieldLaw β := by
  have hz : 0 < z := hβ.trans_le hβz
  have hr : Integrable (likelihood β z) (fieldLaw β) := by
    simpa only [one_mul] using (likelihood_integrable_iff hβ hz (fun _ => (1:ℝ))).mp (integrable_const _)
  have hcov := covariance_nonpos_of_pairwise hf hr ((likelihood_integrable_iff hβ hz f).mp hf')
    (fun x y => by
      rcases le_total (x^2) (y^2) with hh|hh
      · exact mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr (hanti x y hh))
          (sub_nonpos.mpr (likelihood_mono_sq hβ hβz hh))
      · exact mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr (hanti y x hh))
          (sub_nonneg.mpr (likelihood_mono_sq hβ hβz hh)))
  simpa only [integral_mul_likelihood hβ hz,integral_likelihood hβ hz,mul_one] using hcov

lemma m_mono : Monotone m := by
  apply monotone_of_deriv_nonneg
    (fun r => (Calculus.hasDerivAt_tanh r).differentiableAt)
  intro r
  rw [(Calculus.hasDerivAt_tanh r).deriv]
  exact (v_pos r).le

lemma m_nonneg {h : ℝ} (hh : 0 ≤ h) : 0 ≤ m h := by
  have hh' := m_mono hh
  simpa only [m,tanh_zero] using hh'

lemma m_abs_sq (x : ℝ) : m |x|^2 = m x^2 := by
  rcases le_total 0 x with h|h
  · rw [abs_of_nonneg h]
  · rw [abs_of_nonpos h]
    simp only [m,tanh_neg,neg_sq]

lemma m_sq_mono_sq {x y : ℝ} (hxy : x^2 ≤ y^2) : m x^2 ≤ m y^2 := by
  rw [←m_abs_sq x,←m_abs_sq y]
  exact (sq_le_sq₀ (m_nonneg (abs_nonneg _)) (m_nonneg (abs_nonneg _))).mpr
    (m_mono (sq_le_sq.mp hxy))

lemma a_temperature_antitone {β z : ℝ} (hβ : 0 < β) (hβz : β ≤ z) : a z ≤ a β := by
  apply integral_temperature_antitone hβ hβz
    (memLp_v.integrable (by norm_num : (1:ENNReal) ≤ 2))
    (memLp_v.integrable (by norm_num : (1:ENNReal) ≤ 2))
  intro x y hxy
  exact sub_le_sub_left (m_sq_mono_sq hxy) 1

lemma gSignFactor_denom (h : ℝ) : (2:ℝ) < (7/4)^2-m h^2 := by
  have hh := tanh_sq_lt_one h
  change m h^2 < 1 at hh
  linarith

lemma continuous_gSignFactor : Continuous gSignFactor :=
  continuous_v.div (continuous_const.sub (continuous_m.pow 2))
    (fun h => ne_of_gt (lt_trans (by norm_num : (0:ℝ) < 2) (gSignFactor_denom h)))

lemma gSignFactor_abs_le (h : ℝ) : |gSignFactor h| ≤ 1 := by
  have hd : 0 < (7/4)^2-m h^2 := lt_trans (by norm_num) (gSignFactor_denom h)
  rw [gSignFactor,abs_of_nonneg (div_nonneg (v_pos h).le hd.le)]
  apply (div_le_one hd).mpr
  linarith [v_le_one h,gSignFactor_denom h]

lemma memLp_gSignFactor {μ : Measure ℝ} [IsProbabilityMeasure μ] : MemLp gSignFactor 2 μ :=
  MemLp.of_bound continuous_gSignFactor.aestronglyMeasurable 1
    (ae_of_all _ (fun h => by simpa only [Real.norm_eq_abs] using gSignFactor_abs_le h))

lemma g_sign_expansion (h : ℝ) :
    g h = (7/4)*gSignFactor h+m h*gSignFactor h := by
  have hm := m_bounds h
  have hd := gSignFactor_denom h
  have h0 : (7/4:ℝ)-m h ≠ 0 := by linarith [hm.2]
  have h1 : (7/4:ℝ)^2-m h^2 ≠ 0 := by linarith
  calc
    g h = v h/(7/4-m h) := by unfold g w; congr 1; ring
    _ = ((7/4+m h)*v h)/((7/4)^2-m h^2) :=
      (div_eq_div_iff h0 h1).mpr (by ring)
    _ = _ := by unfold gSignFactor; ring

lemma signMeanG_expansion (h : ℝ) :
    signMeanG h = (7/4)*gSignFactor h+m h^2*gSignFactor h := by
  unfold signMeanG gSignFactor v
  ring

lemma memLp_signMeanG {μ : Measure ℝ} [IsProbabilityMeasure μ] : MemLp signMeanG 2 μ := by
  have hi : MemLp (fun h => m h^2*gSignFactor h) 2 μ := by
    apply memLp_gSignFactor.of_le_mul
      ((continuous_m.pow 2).mul continuous_gSignFactor).aestronglyMeasurable (c := (1:ℝ))
    apply ae_of_all
    intro h
    change |m h^2*gSignFactor h| ≤ 1*|gSignFactor h|
    rw [abs_mul,abs_of_nonneg (sq_nonneg _)]
    exact mul_le_mul_of_nonneg_right (tanh_sq_lt_one h).le (abs_nonneg _)
  convert! (memLp_gSignFactor.const_mul (7/4:ℝ)).add hi using 1
  all_goals try with_reducible_and_instances rfl
  exact funext signMeanG_expansion

lemma G_eq_signMeanG (β : ℝ) : G β = ∫ h, signMeanG h ∂fieldLaw β := by
  have hkey := sign_identity β gSignFactor continuous_gSignFactor.measurable
    (fun h => by simp only [gSignFactor,v,m,tanh_neg,neg_sq]) gSignFactor_abs_le
  have hf : Integrable gSignFactor (fieldLaw β) := memLp_gSignFactor.integrable (by norm_num)
  have hmf : Integrable (fun h => m h*gSignFactor h) (fieldLaw β) :=
    (memLp_m (p := 2)).integrable_mul memLp_gSignFactor
  have hm2f : Integrable (fun h => m h^2*gSignFactor h) (fieldLaw β) := by
    have hi := memLp_signMeanG.integrable (μ := fieldLaw β) (by norm_num : (1:ENNReal) ≤ 2)
    convert! hi.sub (hf.const_mul (7/4:ℝ)) using 1
    all_goals try with_reducible_and_instances rfl
    ext h
    simp only [Pi.sub_apply,signMeanG_expansion]
    ring
  unfold G
  simp_rw [g_sign_expansion,signMeanG_expansion]
  rw [integral_add (hf.const_mul _) hmf,integral_add (hf.const_mul _) hm2f,hkey]

lemma signMeanG_antitone_sq {x y : ℝ} (hxy : x^2 ≤ y^2) : signMeanG y ≤ signMeanG x := by
  let u := m x^2
  let t := m y^2
  have hu : 0 ≤ u := sq_nonneg _
  have hut : u ≤ t := m_sq_mono_sq hxy
  have ht : t ≤ 1 := (tanh_sq_lt_one y).le
  have hdenu : 0 < (7/4)^2-u := by dsimp [u]; linarith [gSignFactor_denom x]
  have hdent : 0 < (7/4)^2-t := by dsimp [t]; linarith [gSignFactor_denom y]
  change (1-t)*(7/4+t)/((7/4)^2-t) ≤ (1-u)*(7/4+u)/((7/4)^2-u)
  apply (div_le_div_iff₀ hdent hdenu).mpr
  have hprod : 0 ≤ (t-u)*(35/64+(49/16)*(u+t)-u*t) := by
    apply mul_nonneg (sub_nonneg.mpr hut)
    have hh : u*t ≤ u := by nlinarith only [mul_nonneg hu (sub_nonneg.mpr ht)]
    nlinarith only [hh,hu,hut]
  nlinarith only [hprod]

lemma G_temperature_antitone {β z : ℝ} (hβ : 0 < β) (hβz : β ≤ z) : G z ≤ G β := by
  simp_rw [G_eq_signMeanG]
  exact integral_temperature_antitone hβ hβz
    (memLp_signMeanG.integrable (by norm_num : (1:ENNReal) ≤ 2))
    (memLp_signMeanG.integrable (by norm_num : (1:ENNReal) ≤ 2))
    (fun _ _ => signMeanG_antitone_sq)

end SKRatio.Scalar

end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Variational_ScalarInterpolation
attribute [-instance] _root_.OAI.SKRatio.Observation.History.historyMeasurable _root_.OAI.SKRatio.Observation.History.historyTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Topology ENNReal NNReal
open MeasureTheory ProbabilityTheory Real
namespace SKRatio.Scalar

lemma G_nonneg (β : ℝ) : 0 ≤ G β := by
  apply integral_nonneg
  intro h
  exact div_nonneg (v_pos h).le (by linarith [w_pos h])

lemma l_temperature_monotone {β z : ℝ} (hβ : 0 < β) (hβz : β ≤ z) : l β ≤ l z := by
  rw [l_eq,l_eq]
  linarith [a_temperature_antitone hβ hβz]

lemma memLp_F_other (β z : ℝ) : MemLp (F β) 2 (fieldLaw z) := by
  convert! (((((memLp_field_v z).add ((memLp_field z).const_mul (a β))).add
      (memLp_mv.const_mul (2*β^2))).add (memLp_v.const_mul (50/100-β^2*a β/l β))).add
      (memLp_m.const_mul (12/100:ℝ))).add (memLp_g.const_mul (3*β^2*G β)) using 1
  all_goals try with_reducible_and_instances rfl
  ext h
  dsimp [F]
  ring

lemma F_sub_F (β z h : ℝ) : F β h-F z h =
    (a β-a z)*h+(2*(β^2-z^2))*(m h*v h)+
      (z^2*a z/l z-β^2*a β/l β)*v h+(3*(β^2*G β-z^2*G z))*g h := by
  unfold F
  ring

lemma sd_F_difference (β z : ℝ) : sd (fieldLaw z) (fun h => F β h-F z h) ≤
    |a β-a z| *|z|+2*|β^2-z^2| *sd (fieldLaw z) (fun h => m h*v h)+
      |z^2*a z/l z-β^2*a β/l β| *sd (fieldLaw z) v+
      3*|β^2*G β-z^2*G z| *sd (fieldLaw z) g := by
  let A := fun h : ℝ => (a β-a z)*h
  let B := fun h : ℝ => (2*(β^2-z^2))*(m h*v h)
  let C := fun h : ℝ => (z^2*a z/l z-β^2*a β/l β)*v h
  let D := fun h : ℝ => (3*(β^2*G β-z^2*G z))*g h
  have hA : MemLp A 2 (fieldLaw z) := (memLp_field z).const_mul _
  have hB : MemLp B 2 (fieldLaw z) := memLp_mv.const_mul _
  have hC : MemLp C 2 (fieldLaw z) := memLp_v.const_mul _
  have hD : MemLp D 2 (fieldLaw z) := memLp_g.const_mul _
  have hAB : MemLp (fun h => A h+B h) 2 (fieldLaw z) := hA.add hB
  have hABC : MemLp (fun h => A h+B h+C h) 2 (fieldLaw z) := hAB.add hC
  have h1 := sd_add hA hB
  have h2 := sd_add hAB hC
  have h3 := sd_add hABC hD
  have hsum : sd (fieldLaw z) (fun h => A h+B h+C h+D h) ≤
      sd (fieldLaw z) A+sd (fieldLaw z) B+sd (fieldLaw z) C+sd (fieldLaw z) D := by linarith
  simp_rw [F_sub_F]
  have hzsd : sd (fieldLaw z) (fun h : ℝ => h) = |z| := by
    have hh := variance_id_gaussianReal (μ := z^2) (v := variance z)
    rw [variance_eq_integral measurable_id.aemeasurable] at hh
    change ∫ h, (h-(∫ t, t ∂fieldLaw z))^2 ∂fieldLaw z = _ at hh
    rw [variance_coe] at hh
    unfold sd l2Norm centered
    rw [hh,sqrt_sq_eq_abs]
  have hAsd : sd (fieldLaw z) A = |a β-a z| * |z| := by
    change sd (fieldLaw z) (fun h => (a β-a z)*(fun x : ℝ => x) h) = _
    rw [sd_const_mul,hzsd]
  rw [hAsd] at hsum
  dsimp [B,C,D] at hsum
  simp only [sd_const_mul,abs_mul,show |(2:ℝ)|=2 from by norm_num,
    show |(3:ℝ)|=3 from by norm_num] at hsum
  exact hsum

lemma abs_sub_le_interval {x y L U : ℝ} (hxL : L ≤ x) (hxU : x ≤ U)
    (hyL : L ≤ y) (hyU : y ≤ U) : |x-y| ≤ U-L := by
  exact abs_le.mpr ⟨by linarith,by linarith⟩

lemma temp_a_ratio_bounds {j β z : ℝ} (hj : 0 < j) (hjβ : j ≤ β) (hβz : β ≤ z) :
    j^2*a z/l z ≤ β^2*a β/l β ∧ β^2*a β/l β ≤ z^2*a j/l j := by
  have hβ : 0 < β := hj.trans_le hjβ
  have ha1 := a_temperature_antitone hj hjβ
  have ha2 := a_temperature_antitone hβ hβz
  have hl1 := l_temperature_monotone hj hjβ
  have hl2 := l_temperature_monotone hβ hβz
  have hb1 : j^2*a z ≤ β^2*a β := mul_le_mul (by nlinarith) ha2 (a_nonneg _) (sq_nonneg _)
  have hb2 : β^2*a β ≤ z^2*a j := mul_le_mul (by nlinarith) ha1 (a_nonneg _) (sq_nonneg _)
  exact ⟨(div_le_div_of_nonneg_left (mul_nonneg (sq_nonneg _) (a_nonneg _)) (l_pos β) hl2).trans
      (div_le_div_of_nonneg_right hb1 (l_pos β).le),
    (div_le_div_of_nonneg_right hb2 (l_pos β).le).trans
      (div_le_div_of_nonneg_left (mul_nonneg (sq_nonneg _) (a_nonneg _)) (l_pos j) hl1)⟩

lemma temp_G_bounds {j β z : ℝ} (hj : 0 < j) (hjβ : j ≤ β) (hβz : β ≤ z) :
    j^2*G z ≤ β^2*G β ∧ β^2*G β ≤ z^2*G j := by
  have hβ : 0 < β := hj.trans_le hjβ
  exact ⟨mul_le_mul (by nlinarith) (G_temperature_antitone hβ hβz) (G_nonneg _) (sq_nonneg _),
    mul_le_mul (by nlinarith) (G_temperature_antitone hj hjβ) (G_nonneg _) (sq_nonneg _)⟩

theorem sd_F_interval {j β z : ℝ} (hj : 0 < j) (hjβ : j ≤ β) (hβz : β ≤ z) :
    sd (fieldLaw β) (F β) ≤ crossBound j z := by
  have hβ : 0 < β := hj.trans_le hjβ
  have hz : 0 < z := hβ.trans_le hβz
  have hfchg := sd_temperature_interval_bound hj hjβ hβz (memLp_F β) (memLp_F_other β z)
  have hfd := sd_F_difference β z
  have hftriangle := abs_sd_sub_le (memLp_F_other β z) (memLp_F z)
  have haβ := a_temperature_antitone hβ hβz
  have haj := a_temperature_antitone hj hjβ
  have ha : |a β-a z| ≤ a j-a z := by rw [abs_of_nonneg (sub_nonneg.mpr haβ)]; linarith
  have hsqβ : β^2 ≤ z^2 := by nlinarith
  have hj2 : j^2 ≤ β^2 := by nlinarith
  have hb : |β^2-z^2| ≤ z^2-j^2 := by rw [abs_of_nonpos (sub_nonpos.mpr hsqβ)]; linarith
  have hal1 := temp_a_ratio_bounds hj hjβ hβz
  have hal2 := temp_a_ratio_bounds hj (hjβ.trans hβz) (le_refl z)
  have hc := abs_sub_le_interval hal2.1 hal2.2 hal1.1 hal1.2
  have hgl1 := temp_G_bounds hj hjβ hβz
  have hgl2 := temp_G_bounds hj (hjβ.trans hβz) (le_refl z)
  have hd := abs_sub_le_interval hgl1.1 hgl1.2 hgl2.1 hgl2.2
  rw [abs_of_pos hz] at hfd
  have hupper : sd (fieldLaw z) (F β) ≤
      sd (fieldLaw z) (F z)+(a j-a z)*z+
      2*(z^2-j^2)*sd (fieldLaw z) (fun h => m h*v h)+
      (z^2*a j/l j-j^2*a z/l z)*sd (fieldLaw z) v+
      3*(z^2*G j-j^2*G z)*sd (fieldLaw z) g := by
    have hat := mul_le_mul_of_nonneg_right ha hz.le
    have hbt := mul_le_mul_of_nonneg_right hb (sd_nonneg (μ := fieldLaw z) (fun h => m h*v h))
    have hct := mul_le_mul_of_nonneg_right hc (sd_nonneg (μ := fieldLaw z) v)
    have hdt := mul_le_mul_of_nonneg_right hd (sd_nonneg (μ := fieldLaw z) g)
    have htri := (le_abs_self _).trans hftriangle
    nlinarith only [hfd,htri,hat,hbt,hct,hdt]
  exact hfchg.trans (mul_le_mul_of_nonneg_left hupper (sqrt_nonneg _))

theorem U₁_interval {j β z : ℝ} (hj : 0 < j) (hjβ : j ≤ β) (hβz : β ≤ z) (hz : z ≤ 1) :
    slackBound₁ j z ≤ U₁ β := by
  have hβ : 0 < β := hj.trans_le hjβ
  have hv := weighted_sd_temperature_mono' hβ hβz hz memLp_v memLp_v
  have hm := weighted_mv_temperature_mono hj hjβ (hβz.trans hz)
  have hg := weighted_sd_temperature_mono hβ hβz hz memLp_g memLp_g
  have hr := weighted_R_temperature_mono hβ hβz hz
  unfold slackBound₁ U₁
  nlinarith only [hv,hm,hg,hr]

lemma coherent_a_slack_mono {x y t : ℝ} (ht : 0 < t) (_hy : 0 ≤ y)
    (hyx : y ≤ x) (hreg : t ≤ 2*y) : y^2/t-y ≤ x^2/t-x := by
  apply (mul_le_mul_iff_of_pos_right ht).mp
  field_simp
  have hp := mul_nonneg (sub_nonneg.mpr hyx) (show 0 ≤ x+y-t by linarith)
  nlinarith only [hp]

theorem U₀_interval {j β z : ℝ} (hj : 0 < j) (hjβ : j ≤ β) (hβz : β ≤ z) (hz : z ≤ 1)
    (hreg : l z ≤ 2*a z) (hc : 0 ≤ a z^2/l z-a z-(3/2)*G j^2) :
    slackBound₀ j z ≤ U₀ β := by
  have hβ : 0 < β := hj.trans_le hjβ
  have hj2 : j^2 ≤ β^2 := by nlinarith
  have ha := a_temperature_antitone hβ hβz
  have hg := G_temperature_antitone hj hjβ
  have hl1 := l_temperature_monotone hj hjβ
  have hl2 := l_temperature_monotone hβ hβz
  have hh1 := coherent_a_slack_mono (l_pos z) (a_nonneg z) ha hreg
  have hh2 := div_le_div_of_nonneg_left (sq_nonneg (a β)) (l_pos β) hl2
  have hg2 : G β^2 ≤ G j^2 := (sq_le_sq₀ (G_nonneg β) (G_nonneg j)).mpr hg
  have hcoef : a z^2/l z-a z-(3/2)*G j^2 ≤ a β^2/l β-a β-(3/2)*G β^2 := by
    linarith
  have hprod := mul_le_mul hj2 hcoef hc (sq_nonneg β)
  have hr := weighted_R_temperature_mono hβ hβz hz
  unfold slackBound₀ U₀
  linarith

end SKRatio.Scalar

end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Certificates_CertifiedInterpolation
attribute [-instance] _root_.OAI.SKRatio.Observation.History.historyMeasurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Topology ENNReal NNReal
open Real MeasureTheory ProbabilityTheory
namespace SKRatio.Certificate
open Scalar

namespace Box

lemma mem_divPos {A B : Box} {x y : ℝ} (hx : x ∈ A) (hy : y ∈ B)
    (hB : 0 < B.lo) : x/y ∈ divPos A B := by
  have hi : inv B=some (posInv B) := by simp only [inv,posInv,ite_eq_left hB]
  exact mem_mul hx (mem_inv hy hi).1

lemma lower {A : Box} {q : ℚ} {x : ℝ} (h : q ≤ A.lo) (hx : x ∈ A) : (q:ℝ) ≤ x :=
  (by exact_mod_cast h : (q:ℝ) ≤ A.lo).trans hx.1
lemma upper {A : Box} {q : ℚ} {x : ℝ} (h : A.hi ≤ q) (hx : x ∈ A) : x ≤ (q:ℝ) :=
  hx.2.trans (by exact_mod_cast h)
end Box

lemma mem_lBox {β : ℝ} {A : Box} (ha : a β ∈ A) : l β ∈ lBox A := by
  rw [l_eq]
  simpa only [lBox,Rat.cast_div,Rat.cast_ofNat] using
    Box.mem_sub (Box.mem_rat (64/100)) (Box.mem_mul (Box.mem_rat (19/100)) ha)

lemma coefficient_mem {j z : ℝ} {X Y : Enclosures} (hx : Valid j X) (hy : Valid z Y)
    (hY : 0 < (lBox Y.av).lo) : a z^2/l z-a z-(3/2)*G j^2 ∈ coefficientBox X Y := by
  simpa only [coefficientBox,Rat.cast_div,Rat.cast_ofNat] using Box.mem_sub
    (Box.mem_sub (Box.mem_divPos (Box.mem_sq hy.mem_a) (mem_lBox hy.mem_a) hY) hy.mem_a)
    (Box.mem_mul (Box.mem_rat (3/2)) (Box.mem_sq hx.mem_G))

lemma slack₀_mem {j z : ℚ} {X Y : Enclosures} (hx : Valid j X) (hy : Valid z Y)
    (hY : 0 < (lBox Y.av).lo) : slackBound₀ j z ∈ slackBox₀ j z X Y := by
  have hh := Box.mem_sub
    (Box.mem_add (Box.mem_add (mem_lBox hx.mem_a) (Box.mem_rat (18/1000)))
      (Box.mem_mul (Box.mem_rat (j^2)) (coefficient_mem hx hy hY)))
    (Box.mem_mul (Box.mem_rat (z^2)) hy.mem_R)
  rw [Rat.cast_pow,Rat.cast_pow] at hh
  simpa only [slackBound₀,slackBox₀,Rat.cast_div,Rat.cast_ofNat] using hh

lemma slack₁_mem {j z : ℚ} {X Y : Enclosures} (hx : Valid j X) (hy : Valid z Y) :
    slackBound₁ j z ∈ slackBox₁ j z X Y := by
  have hh := Box.mem_sub
    (Box.mem_add (Box.mem_sub (Box.mem_rat (4644/10000))
      (Box.mem_mul (Box.mem_rat (z/2)) hy.mem_v))
      (Box.mem_mul (Box.mem_rat (j^2)) hx.mem_M))
    (Box.mem_mul (Box.mem_rat (z^2))
      (Box.mem_add (Box.mem_mul (Box.mem_rat (3/2)) (Box.mem_sq hy.mem_g)) hy.mem_R))
  simp only [Rat.cast_div,Rat.cast_ofNat,Rat.cast_pow] at hh
  convert! hh using 1
  all_goals try with_reducible_and_instances rfl
  unfold slackBound₁
  ring

lemma cross_mem {j z t : ℚ} {X Y : Enclosures} (hx : Valid j X) (hy : Valid z Y)
    (hX : 0 < (lBox X.av).lo) (hY : 0 < (lBox Y.av).lo)
    (ht : sqrt (densityFactor j z) ≤ (t:ℝ)) : crossBound j z ∈ crossBox j z t X Y := by
  have ht' : sqrt (densityFactor j z) ∈ (⟨0,t⟩ : Box) := by
    exact ⟨by simpa only [Rat.cast_zero] using sqrt_nonneg _,ht⟩
  have hh := Box.mem_mul ht' (Box.mem_add (Box.mem_add (Box.mem_add
      (Box.mem_add hy.mem_F (Box.mem_mul (Box.mem_sub hx.mem_a hy.mem_a) (Box.mem_rat z)))
        (Box.mem_mul (Box.mem_rat (2*(z^2-j^2))) hy.mem_mv))
        (Box.mem_mul (Box.mem_sub
          (Box.mem_divPos (Box.mem_mul (Box.mem_rat (z^2)) hx.mem_a) (mem_lBox hx.mem_a) hX)
          (Box.mem_divPos (Box.mem_mul (Box.mem_rat (j^2)) hy.mem_a) (mem_lBox hy.mem_a) hY)) hy.mem_v))
        (Box.mem_mul (Box.mem_mul (Box.mem_rat 3)
          (Box.mem_sub (Box.mem_mul (Box.mem_rat (z^2)) hx.mem_G)
            (Box.mem_mul (Box.mem_rat (j^2)) hy.mem_G))) hy.mem_g))
  repeat rw [Rat.cast_mul] at hh
  repeat rw [Rat.cast_sub] at hh
  repeat rw [Rat.cast_pow] at hh
  simpa only [crossBound,crossBox,Rat.cast_div,Rat.cast_ofNat] using hh

lemma interpolation_check_sound {j z t : ℚ} {X Y : Enclosures}
    (hx : Valid j X) (hy : Valid z Y)
    (ht : sqrt (densityFactor j z) ≤ (t:ℝ))
    (hc : interpolationCheck j z t X Y = true) :
    l z ≤ 2*a z ∧ 0 ≤ a z^2/l z-a z-(3/2)*G j^2 ∧
    511/1000 ≤ slackBound₀ j z ∧ 425/1000 ≤ slackBound₁ j z ∧ crossBound j z ≤ 925/1000 := by
  rcases of_decide_eq_true hc with ⟨hX,hY,hreg,hcoeff,hS₀,hS₁,hC⟩
  have hreg' : ((lBox Y.av).hi:ℝ) ≤ 2*(Y.av.lo:ℝ) := by exact_mod_cast hreg
  have hreg'' : l (z:ℝ) ≤ 2*a z := by
    linarith only [(mem_lBox hy.mem_a).2,hy.mem_a.1,hreg']
  refine ⟨hreg'',?_,?_,?_,?_⟩
  · simpa only [Rat.cast_zero] using Box.lower hcoeff (coefficient_mem hx hy hY)
  · simpa only [Rat.cast_div,Rat.cast_ofNat] using Box.lower hS₀ (slack₀_mem hx hy hY)
  · simpa only [Rat.cast_div,Rat.cast_ofNat] using Box.lower hS₁ (slack₁_mem hx hy)
  · simpa only [Rat.cast_div,Rat.cast_ofNat] using Box.upper hC (cross_mem hx hy hX hY ht)

lemma certified_slacks {j z t : ℚ} {X Y : Enclosures} {β : ℝ}
    (hj : 0 < (j:ℝ)) (hjβ : (j:ℝ) ≤ β) (hβz : β ≤ (z:ℝ)) (hz : (z:ℝ) ≤ 1)
    (hx : Valid j X) (hy : Valid z Y) (ht : sqrt (densityFactor j z) ≤ (t:ℝ))
    (hc : interpolationCheck j z t X Y = true) :
    511/1000 ≤ U₀ β ∧ 425/1000 ≤ U₁ β ∧ sd (fieldLaw β) (F β) ≤ 925/1000 := by
  obtain ⟨hreg,hcoeff,hS₀,hS₁,hC⟩ := interpolation_check_sound hx hy ht hc
  exact ⟨hS₀.trans (U₀_interval hj hjβ hβz hz hreg hcoeff),
    hS₁.trans (U₁_interval hj hjβ hβz hz),(sd_F_interval hj hjβ hβz).trans hC⟩

end SKRatio.Certificate

end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Certificates_CertifiedConstants
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Real MeasureTheory
namespace SKRatio.Certificate
open Scalar

lemma sqrt_densityFactor_bound {j z t : ℝ} (hj : 0 < j) (hz : 0 ≤ z) (ht : 0 ≤ t)
    (hexp : (z^2-j^2)/2 < 1)
    (harith : z/j/(1-(z^2-j^2)/2) ≤ t^2) : sqrt (densityFactor j z) ≤ t := by
  have hpos : 0 < 1-(z^2-j^2)/2 := by linarith only [hexp]
  have he : exp ((z^2-j^2)/2) ≤ 1/(1-(z^2-j^2)/2) := by
    have hh := one_div_le_one_div_of_le hpos (show 1-(z^2-j^2)/2 ≤ exp (-((z^2-j^2)/2)) by
      linarith only [add_one_le_exp (-((z^2-j^2)/2))])
    simpa only [exp_neg,one_div,inv_inv] using hh
  apply (sqrt_le_iff).mpr
  refine ⟨ht,?_⟩
  have hm := mul_le_mul_of_nonneg_left he (div_nonneg hz hj.le)
  unfold densityFactor
  exact hm.trans (by simpa only [mul_one_div] using harith)

lemma density0 : sqrt (densityFactor (7/20) (2/5)) ≤ 27/25 := by
  apply sqrt_densityFactor_bound <;> norm_num
lemma check0 : interpolationCheck (7/20) (2/5) (27/25) X0 X1 = true := by decide +kernel

lemma density1 : sqrt (densityFactor (2/5) (89/200)) ≤ 1067/1000 := by
  apply sqrt_densityFactor_bound <;> norm_num
lemma check1 : interpolationCheck (2/5) (89/200) (1067/1000) X1 X2 = true := by decide +kernel

lemma density2 : sqrt (densityFactor (89/200) (19/40)) ≤ 521/500 := by
  apply sqrt_densityFactor_bound <;> norm_num
lemma check2 : interpolationCheck (89/200) (19/40) (521/500) X2 X3 = true := by decide +kernel

lemma density3 : sqrt (densityFactor (19/40) (1/2)) ≤ 517/500 := by
  apply sqrt_densityFactor_bound <;> norm_num
lemma check3 : interpolationCheck (19/40) (1/2) (517/500) X3 X4 = true := by decide +kernel

end SKRatio.Certificate

end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Certificates_CertifiedMomentAssembly
attribute [-instance] _root_.OAI.SKRatio.Observation.History.historyMeasurable _root_.OAI.SKRatio.Observation.History.historyTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Real MeasureTheory
namespace SKRatio.Certificate
open Scalar

lemma abs_sub_center {x : ℝ} {A e : ℚ} (hx : x ∈ (⟨A-e,A+e⟩ : Box)) :
    |x-(A:ℝ)| ≤ (e:ℝ) := by
  change ((A-e:ℚ):ℝ) ≤ x ∧ x ≤ ((A+e:ℚ):ℝ) at hx
  rw [Rat.cast_sub,Rat.cast_add] at hx
  exact abs_le.mpr ⟨by linarith only [hx.1],by linarith only [hx.2]⟩

lemma mem_sd_center {μ : Measure ℝ} [IsProbabilityMeasure μ] {f : ℝ → ℝ}
    (hf : MemLp f 2 μ) {c B : ℚ} (hB : 0 ≤ B)
    (hc : (∫ h, (f h-(c:ℝ))^2 ∂μ) ∈ (⟨0,B^2⟩ : Box)) :
    sd μ f ∈ (⟨0,B⟩ : Box) := by
  have hi := hc.2
  change (∫ h, (f h-(c:ℝ))^2 ∂μ) ≤ ((B^2:ℚ):ℝ) at hi
  rw [Rat.cast_pow] at hi
  exact ⟨by simpa only [Rat.cast_zero] using sd_nonneg (μ := μ) f,
    sd_le_of_center hf (by exact_mod_cast hB) hi⟩

lemma mem_F_of_center {β : ℝ} {A C Q sa sf : ℚ}
    (hβ : 0 ≤ β) (hβh : β ≤ 1/2) (hA : 0 ≤ A) (hA1 : A ≤ 1)
    (ha : a β ∈ (⟨A-3/2000,A+3/2000⟩ : Box))
    (hg : G β ∈ (⟨C-3/2000,C+3/2000⟩ : Box))
    (hsa : 0 ≤ sa)
    (hc : (∫ h, (approxF β A C h-(Q:ℝ))^2 ∂fieldLaw β) ∈ (⟨0,sa^2⟩ : Box))
    (harith : sa+9/2000 ≤ sf) : sd (fieldLaw β) (F β) ∈ (⟨0,sf⟩ : Box) := by
  have hbound := approxF_error hβ hβh (A := (A:ℝ)) (C := (C:ℝ))
    (by exact_mod_cast hA) (by exact_mod_cast hA1)
  have hsd := (mem_sd_center (memLp_approxF β A C) hsa hc).2
  change sd (fieldLaw β) (approxF β A C) ≤ (sa:ℝ) at hsd
  have heA := abs_sub_center ha
  have heG := abs_sub_center hg
  have ha' : (sa:ℝ)+9/2000 ≤ (sf:ℝ) := by
    have hh : ((sa+9/2000:ℚ):ℝ) ≤ (sf:ℝ) := Rat.cast_le.mpr harith
    simpa only [Rat.cast_add,Rat.cast_div,Rat.cast_ofNat] using hh
  norm_num only [Rat.cast_div,Rat.cast_ofNat] at heA heG
  exact ⟨by simpa only [Rat.cast_zero] using sd_nonneg (μ := fieldLaw β) (F β),
    by linarith only [hbound,hsd,heA,heG,ha']⟩

end SKRatio.Certificate

end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Certificates_ScalarDataJ3K1
attribute [-instance] _root_.OAI.SKRatio.Observation.History.historyBorel _root_.OAI.SKRatio.Observation.History.historyMeasurable _root_.OAI.SKRatio.Observation.History.historyTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Real MeasureTheory
namespace SKRatio.Certificate.Data.J3K1

theorem integral_bound :
    (∫ h, scalarFunction (19/40) (406349/500000) (66273/125000) (28579/250000) (135787/200000) 1 h ∂Scalar.fieldLaw (19/40)) ∈ (⟨132171/250000,132921/250000⟩ : Box) := by
  apply gaussian_certificate (e := expression) (B := blocks) (h := (1/10)) (k := 5) (by norm_num)
  · simpa only [expression,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero] using integrandExpr_val (19/40) (406349/500000) (66273/125000) (28579/250000) (135787/200000) 1
  · exact (continuous_scalarFunction _ _ _ _ _ _).measurable
  · intro x
    apply scalarFunction_bound <;> norm_num
  · exact checks
  · decide +kernel

end SKRatio.Certificate.Data.J3K1

end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Certificates_ScalarDataJ3K2
attribute [-instance] _root_.OAI.SKRatio.Observation.History.historyBorel _root_.OAI.SKRatio.Observation.History.historyMeasurable _root_.OAI.SKRatio.Observation.History.historyTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Real MeasureTheory
namespace SKRatio.Certificate.Data.J3K2

theorem integral_bound :
    (∫ h, scalarFunction (19/40) (406349/500000) (66273/125000) (28579/250000) (135787/200000) 2 h ∂Scalar.fieldLaw (19/40)) ∈ (⟨7051/62500,14477/125000⟩ : Box) := by
  apply gaussian_certificate (e := expression) (B := blocks) (h := (1/10)) (k := 5) (by norm_num)
  · simpa only [expression,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero] using integrandExpr_val (19/40) (406349/500000) (66273/125000) (28579/250000) (135787/200000) 2
  · exact (continuous_scalarFunction _ _ _ _ _ _).measurable
  · intro x
    apply scalarFunction_bound <;> norm_num
  · exact checks
  · decide +kernel

end SKRatio.Certificate.Data.J3K2

end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Certificates_ScalarDataJ3K3
attribute [-instance] _root_.OAI.SKRatio.Observation.History.historyBorel _root_.OAI.SKRatio.Observation.History.historyMeasurable _root_.OAI.SKRatio.Observation.History.historyTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Real MeasureTheory
namespace SKRatio.Certificate.Data.J3K3

theorem integral_bound :
    (∫ h, scalarFunction (19/40) (406349/500000) (66273/125000) (28579/250000) (135787/200000) 3 h ∂Scalar.fieldLaw (19/40)) ∈ (⟨0,13/500⟩ : Box) := by
  apply gaussian_certificate (e := expression) (B := blocks) (h := (1/10)) (k := 5) (by norm_num)
  · simpa only [expression,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero] using integrandExpr_val (19/40) (406349/500000) (66273/125000) (28579/250000) (135787/200000) 3
  · exact (continuous_scalarFunction _ _ _ _ _ _).measurable
  · intro x
    apply scalarFunction_bound <;> norm_num
  · exact checks
  · decide +kernel

end SKRatio.Certificate.Data.J3K3

end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Certificates_ScalarDataJ3K5
attribute [-instance] _root_.OAI.SKRatio.Observation.History.historyBorel _root_.OAI.SKRatio.Observation.History.historyMeasurable _root_.OAI.SKRatio.Observation.History.historyTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Real MeasureTheory
namespace SKRatio.Certificate.Data.J3K5

theorem integral_bound :
    (∫ h, scalarFunction (19/40) (406349/500000) (66273/125000) (28579/250000) (135787/200000) 5 h ∂Scalar.fieldLaw (19/40)) ∈ (⟨0,11881/1000000⟩ : Box) := by
  apply gaussian_certificate (e := expression) (B := blocks) (h := (1/10)) (k := 5) (by norm_num)
  · simpa only [expression,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero] using integrandExpr_val (19/40) (406349/500000) (66273/125000) (28579/250000) (135787/200000) 5
  · exact (continuous_scalarFunction _ _ _ _ _ _).measurable
  · intro x
    apply scalarFunction_bound <;> norm_num
  · exact checks
  · decide +kernel

end SKRatio.Certificate.Data.J3K5

end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Certificates_ScalarDataJ3K6
attribute [-instance] _root_.OAI.SKRatio.Observation.History.historyBorel _root_.OAI.SKRatio.Observation.History.historyMeasurable _root_.OAI.SKRatio.Observation.History.historyTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Real MeasureTheory
namespace SKRatio.Certificate.Data.J3K6

theorem integral_bound :
    (∫ h, scalarFunction (19/40) (406349/500000) (66273/125000) (28579/250000) (135787/200000) 6 h ∂Scalar.fieldLaw (19/40)) ∈ (⟨0,1024/15625⟩ : Box) := by
  apply gaussian_certificate (e := expression) (B := blocks) (h := (1/10)) (k := 5) (by norm_num)
  · simpa only [expression,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero] using integrandExpr_val (19/40) (406349/500000) (66273/125000) (28579/250000) (135787/200000) 6
  · exact (continuous_scalarFunction _ _ _ _ _ _).measurable
  · intro x
    apply scalarFunction_bound <;> norm_num
  · exact checks
  · decide +kernel

end SKRatio.Certificate.Data.J3K6

end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Certificates_CertifiedMomentsJ3
attribute [-instance] _root_.OAI.SKRatio.Observation.History.historyMeasurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Real MeasureTheory
namespace SKRatio.Certificate
open Scalar

theorem valid3 : Valid (19/40) X3 := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_⟩
  · exact Data.J3K0.integral_bound
  · exact Data.J3K1.integral_bound
  · exact Data.J3K2.integral_bound
  · exact Data.J3K3.integral_bound
  · apply mem_sd_center memLp_v (c := (406349/500000)) (by norm_num : (0:ℚ) ≤ 49/250)
    convert! Data.J3K4.integral_bound using 1 <;> norm_num [scalarFunction]
  · apply mem_sd_center memLp_g (c := (66273/125000)) (by norm_num : (0:ℚ) ≤ 109/1000)
    convert! Data.J3K5.integral_bound using 1 <;> norm_num [scalarFunction]
  · apply mem_sd_center memLp_mv (c := (28579/250000)) (by norm_num : (0:ℚ) ≤ 32/125)
    convert! Data.J3K6.integral_bound using 1 <;> norm_num [scalarFunction]
  · apply mem_F_of_center (A := (406349/500000)) (C := (66273/125000)) (Q := (135787/200000))
      (sa := (823/1000)) (sf := (207/250)) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
    · convert! Data.J3K0.integral_bound using 1
      all_goals try with_reducible_and_instances rfl
      norm_num [scalarFunction,a]
    · convert! Data.J3K1.integral_bound using 1
      all_goals try with_reducible_and_instances rfl
      norm_num [scalarFunction,G]
    · norm_num
    · convert! Data.J3K7.integral_bound using 1 <;> norm_num [scalarFunction]
    · norm_num

end SKRatio.Certificate

end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Certificates_FinalScalar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Real MeasureTheory
namespace SKRatio.Certificate
open Scalar

lemma uniform_slacks_oai {β : ℝ} (hβ : 7/20 ≤ β) (hβh : β ≤ 1/2) :
    511/1000 ≤ U₀ β ∧ 425/1000 ≤ U₁ β ∧
      sd (fieldLaw β) (F β) ≤ 925/1000 := by
  by_cases h1 : β ≤ 2/5
  · apply certified_slacks (j := 7/20) (z := 2/5) (t := 27/25) (X := X0) (Y := X1)
    · norm_num
    · simpa only [Rat.cast_div,Rat.cast_ofNat] using hβ
    · simpa only [Rat.cast_div,Rat.cast_ofNat] using h1
    · norm_num
    · simpa only [Rat.cast_div,Rat.cast_ofNat] using valid0
    · simpa only [Rat.cast_div,Rat.cast_ofNat] using valid1
    · simpa only [Rat.cast_div,Rat.cast_ofNat] using density0
    · exact check0
  by_cases h2 : β ≤ 89/200
  · apply certified_slacks (j := 2/5) (z := 89/200) (t := 1067/1000) (X := X1) (Y := X2)
    · norm_num
    · simp only [Rat.cast_div,Rat.cast_ofNat]; linarith
    · simpa only [Rat.cast_div,Rat.cast_ofNat] using h2
    · norm_num
    · simpa only [Rat.cast_div,Rat.cast_ofNat] using valid1
    · simpa only [Rat.cast_div,Rat.cast_ofNat] using valid2
    · simpa only [Rat.cast_div,Rat.cast_ofNat] using density1
    · exact check1
  by_cases h3 : β ≤ 19/40
  · apply certified_slacks (j := 89/200) (z := 19/40) (t := 521/500) (X := X2) (Y := X3)
    · norm_num
    · simp only [Rat.cast_div,Rat.cast_ofNat]; linarith
    · simpa only [Rat.cast_div,Rat.cast_ofNat] using h3
    · norm_num
    · simpa only [Rat.cast_div,Rat.cast_ofNat] using valid2
    · simpa only [Rat.cast_div,Rat.cast_ofNat] using valid3
    · simpa only [Rat.cast_div,Rat.cast_ofNat] using density2
    · exact check2
  · apply certified_slacks (j := 19/40) (z := 1/2) (t := 517/500) (X := X3) (Y := X4)
    · norm_num
    · simp only [Rat.cast_div,Rat.cast_ofNat]; linarith
    · simpa only [Rat.cast_div,Rat.cast_ofNat,Rat.cast_one] using hβh
    · norm_num
    · simpa only [Rat.cast_div,Rat.cast_ofNat] using valid3
    · simpa only [Rat.cast_div,Rat.cast_ofNat,Rat.cast_one] using valid4
    · simpa only [Rat.cast_div,Rat.cast_ofNat,Rat.cast_one] using density3
    · exact check3

end SKRatio.Certificate

end

end OAI
end

theorem solution : type_of% @OAI.SKRatio.Certificate.uniform_slacks_oai := @OAI.SKRatio.Certificate.uniform_slacks_oai
