-- Prove2me | solution 1 for OAI.SKRatio.Certificate.diagonal_envelope
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T01:11:05.414822+00:00
-- url     : https://prove2.me/submissions/8e831ff5-d0ef-4ac2-9046-5b96c07aae06

import Mathlib
import Definitions.Def_OAIQ024S012
import Definitions.Def_OAIQ024S016
import Theorems.Thm_OAI_SKRatio_Certificate_Data_J4K10_checks
import Theorems.Thm_OAI_SKRatio_Certificate_Data_J4K12_checks
import Theorems.Thm_OAI_SKRatio_Certificate_endpointD_prime_lower
import Theorems.Thm_OAI_SKRatio_Certificate_endpointD_prime_upper
import Theorems.Thm_OAI_SKRatio_Certificate_endpointK_one_bound
import Theorems.Thm_OAI_SKRatio_Certificate_endpointK_zero_bound

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
-- module Solutions.OAIQ024_SK.SKRatio_Variational_ScalarKernel
attribute [-instance] _root_.OAI.SKRatio.Observation.History.historyTopology
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

end SKRatio.Scalar

end
end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Variational_ScalarMoments
attribute [-instance] _root_.OAI.SKRatio.Observation.History.historyTopology
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

lemma multiplier_pos (h : ℝ) : 4464/10000 ≤ multiplier h := by
  unfold multiplier
  nlinarith [sq_nonneg (m h-12/100)]

lemma continuous_multiplier : Continuous multiplier := by
  exact (continuous_const.add ((continuous_m.pow 2).const_mul (1/4))).sub
    (continuous_m.const_mul (6/100))

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
attribute [-instance] _root_.OAI.SKRatio.Observation.History.historyTopology
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

lemma abs_inv_multiplier_le (h : ℝ) : |(multiplier h)⁻¹| ≤ 3 := by
  rw [abs_of_pos (inv_pos.mpr (multiplier_strict_pos h)),inv_eq_one_div,div_le_iff₀ (multiplier_strict_pos h)]
  linarith [multiplier_pos h]

lemma abs_v_sum_le (h t : ℝ) : |v h+v t| ≤ 2 := by
  rw [abs_of_nonneg (add_nonneg (v_pos h).le (v_pos t).le)]
  linarith [v_le_one h,v_le_one t]

lemma v_sum_sq_le (h t : ℝ) : (v h+v t)^2 ≤ 4 := by
  nlinarith [abs_v_sum_le h t,neg_le_abs (v h+v t),le_abs_self (v h+v t)]

lemma abs_diagonal_kernel_le (h t : ℝ) : |v t^2/(w h+w t)| ≤ 2 := by
  rw [abs_of_nonneg (div_nonneg (sq_nonneg _) (add_pos (w_pos h) (w_pos t)).le)]
  apply (div_le_iff₀ (add_pos (w_pos h) (w_pos t))).mpr
  have ht : v t ≤ 2*w t := by rw [v_factor]; nlinarith [w_pos t,(m_bounds t).2]
  have hv : v t^2 ≤ v t := by nlinarith [v_pos t,v_le_one t]
  linarith [w_pos h]

lemma continuous_diagonal_kernel :
    Continuous (fun z : ℝ×ℝ => v z.2^2/(w z.1+w z.2)) := by
  apply ((continuous_v.comp continuous_snd).pow 2).div
    ((continuous_w.comp continuous_fst).add (continuous_w.comp continuous_snd))
  intro z
  exact (add_pos (w_pos z.1) (w_pos z.2)).ne'

section Probability
variable (μ : Measure ℝ) [IsProbabilityMeasure μ]

lemma abs_cost_integrand_le (β h t : ℝ) :
    |(β^2/4)*(v h+v t)^2/(multiplier h)| ≤ 3*β^2 := by
  rw [div_eq_mul_inv,abs_mul,abs_mul,abs_of_nonneg (div_nonneg (sq_nonneg β) (by norm_num)),
    abs_of_nonneg (sq_nonneg _)]
  calc
    _ ≤ (β^2/4)*4*3 := by
      gcongr
      · exact v_sum_sq_le h t
      · exact abs_inv_multiplier_le h
    _ = _ := by ring

lemma continuous_cost_integrand (β : ℝ) :
    Continuous (fun z : ℝ×ℝ => (β^2/4)*(v z.1+v z.2)^2/(multiplier z.1)) := by
  exact ((((continuous_v.comp continuous_fst).add (continuous_v.comp continuous_snd)).pow 2).const_mul _).div
    (continuous_multiplier.comp continuous_fst) (fun z => (multiplier_strict_pos z.1).ne')

end Probability

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
-- module Solutions.OAIQ024_SK.SKRatio_Variational_ScalarTemperature
attribute [-instance] _root_.OAI.SKRatio.Observation.History.historyBorel _root_.OAI.SKRatio.Observation.History.historyMeasurable _root_.OAI.SKRatio.Observation.History.historySecondCountable _root_.OAI.SKRatio.Observation.History.historyTopology
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

lemma integral_diagonal_kernel {μ : Measure ℝ} [IsProbabilityMeasure μ] (h : ℝ) :
    Integrable (fun t => v t^2/(w h+w t)) μ := by
  apply (integrable_const (2:ℝ)).mono'
    (continuous_diagonal_kernel.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  exact ae_of_all _ (fun t => by
    simpa only [norm_eq_abs,Function.comp_apply,id_eq] using abs_diagonal_kernel_le h t)

lemma diagonal_temperature_mono {β z : ℝ} (hβ : 0 < β) (hβz : β ≤ z) (hz : z ≤ 1) (h : ℝ) :
    diagonal (fieldLaw β) β h ≤ diagonal (fieldLaw z) z h := by
  apply scaled_integral_mono hβ hβz hz
    (fun t => div_nonneg (sq_nonneg _) (add_pos (w_pos h) (w_pos t)).le)
    (integral_diagonal_kernel h)

lemma cost_temperature_mono {β z : ℝ} (hβ : 0 < β) (hβz : β ≤ z) (hz : z ≤ 1) (t : ℝ) :
    cost (fieldLaw β) β t ≤ cost (fieldLaw z) z t := by
  have hi : Integrable (fun h => (v h+v t)^2/(4*multiplier h)) (fieldLaw z) := by
    have hehe (h : ℝ) : (v h+v t)^2/(4*multiplier h) =
        ((1:ℝ)^2/4)*(v h+v t)^2/multiplier h := by ring
    simp_rw [hehe]
    exact (integrable_const (3:ℝ)).mono'
      ((continuous_cost_integrand 1).comp (continuous_id.prodMk continuous_const)).aestronglyMeasurable
      (ae_of_all _ (fun h => by simpa only [norm_eq_abs,one_pow,mul_one] using abs_cost_integrand_le 1 h t))
  have he (B h : ℝ) : (B^2/4)*(v h+v t)^2/multiplier h =
      B^2*((v h+v t)^2/(4*multiplier h)) := by ring
  unfold cost
  simp_rw [he,integral_const_mul]
  exact scaled_integral_mono hβ hβz hz
    (fun h => div_nonneg (sq_nonneg _) (mul_pos (by norm_num) (multiplier_strict_pos h)).le) hi

end SKRatio.Scalar

end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Variational_ScalarEnvelope
attribute [-instance] _root_.OAI.SKRatio.Observation.History.historyBorel _root_.OAI.SKRatio.Observation.History.historyMeasurable _root_.OAI.SKRatio.Observation.History.historySecondCountable _root_.OAI.SKRatio.Observation.History.historyTopology
attribute [-simp] _root_.OAI.SKRatio.Planted.compactWeight_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Topology ENNReal NNReal
open MeasureTheory ProbabilityTheory Real
namespace SKRatio.Scalar

lemma integrable_K_integrand {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {y : ℝ} (hy : |y| ≤ 1) :
    Integrable (fun h => (1-y^2+v h)^2/multiplier h) μ := by
  have hy2 : y^2 ≤ 1 := by simpa only [sq_abs,one_pow] using
    (sq_le_sq₀ (abs_nonneg y) (by norm_num : (0:ℝ) ≤ 1)).mpr hy
  apply (integrable_const (12:ℝ)).mono'
    (((continuous_const.add continuous_v).pow 2).div continuous_multiplier
      (fun h => (multiplier_strict_pos h).ne')).aestronglyMeasurable
  apply ae_of_all
  intro h
  change |(1-y^2+v h)^2/multiplier h| ≤ 12
  have hs : (1-y^2+v h)^2 ≤ 4 := by nlinarith [sq_nonneg y,v_le_one h,(v_pos h).le]
  rw [abs_of_nonneg (div_nonneg (sq_nonneg _) (multiplier_strict_pos h).le)]
  exact (div_le_div_of_nonneg_right hs (multiplier_strict_pos h).le).trans (by
    rw [div_le_iff₀ (multiplier_strict_pos h)]
    linarith [multiplier_pos h])

lemma D_integrand_pos {y : ℝ} (hy : y ≤ 1) (h : ℝ) : 0 < 2-y-m h := by
  linarith [(m_bounds h).2]

lemma D_integrand_le_two {y : ℝ} (hy : y ≤ 1) (h : ℝ) :
    |v h^2/(2-y-m h)| ≤ 2 := by
  have hd := D_integrand_pos hy h
  rw [abs_of_nonneg (div_nonneg (sq_nonneg _) hd.le)]
  apply (div_le_iff₀ hd).mpr
  have hbase : v h^2 ≤ 2*(1-m h) := by
    have hvw : v h = (1-m h)*(1+m h) := by unfold v; ring
    have hv : v h^2 ≤ v h := by nlinarith [v_le_one h,(v_pos h).le]
    have hmu := (m_bounds h).2
    have hmm : v h ≤ 2*(1-m h) := by rw [hvw]; nlinarith [sq_nonneg (1-m h)]
    linarith
  linarith

lemma integrable_D_integrand {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {y : ℝ} (hy : y ≤ 1) : Integrable (fun h => v h^2/(2-y-m h)) μ := by
  exact (integrable_const (2:ℝ)).mono'
    ((continuous_v.pow 2).div (continuous_const.sub continuous_m)
      (fun h => (D_integrand_pos hy h).ne')).aestronglyMeasurable
    (ae_of_all _ (fun h => by simpa only [norm_eq_abs] using D_integrand_le_two hy h))

lemma integrable_DPrime_integrand {μ : Measure ℝ} [IsProbabilityMeasure μ] :
    Integrable (fun h => v h^2/(2-m h)^2) μ := by
  have hden (h : ℝ) : 0 < 2-m h := by linarith [(m_bounds h).2]
  apply (integrable_const (1:ℝ)).mono'
    ((continuous_v.pow 2).div ((continuous_const.sub continuous_m).pow 2)
      (fun h => pow_ne_zero _ (hden h).ne')).aestronglyMeasurable
  apply ae_of_all
  intro h
  change |v h^2/(2-m h)^2| ≤ 1
  rw [abs_of_nonneg (div_nonneg (sq_nonneg _) (sq_nonneg _))]
  apply (div_le_one (sq_pos_of_pos (hden h))).mpr
  nlinarith [v_le_one h,(v_pos h).le,(m_bounds h).2]

lemma endpointK_quadratic {y : ℝ} (hy : |y| ≤ 1) :
    endpointK y ≤ endpointK 0+(endpointK 1-endpointK 0)*y^2 := by
  have hy2 : y^2 ≤ 1 := by simpa only [sq_abs,one_pow] using
    (sq_le_sq₀ (abs_nonneg y) (by norm_num : (0:ℝ) ≤ 1)).mpr hy
  have hi0 : Integrable (fun h => (1+v h)^2/multiplier h) (fieldLaw (1/2)) := by
    simpa using integrable_K_integrand (y := 0) (μ := fieldLaw (1/2)) (by norm_num)
  have hi1 : Integrable (fun h => v h^2/multiplier h) (fieldLaw (1/2)) := by
    simpa using integrable_K_integrand (y := 1) (μ := fieldLaw (1/2)) (by norm_num)
  have hp (h : ℝ) : (1-y^2+v h)^2/multiplier h ≤
      (1-y^2)*((1+v h)^2/multiplier h)+y^2*(v h^2/multiplier h) := by
    have hs : (1-y^2+v h)^2 ≤ (1-y^2)*(1+v h)^2+y^2*v h^2 := by
      nlinarith only [mul_nonneg (sq_nonneg y) (sub_nonneg.mpr hy2)]
    convert! div_le_div_of_nonneg_right hs (multiplier_strict_pos h).le using 1
    all_goals try with_reducible_and_instances rfl
    ring
  have hi := integral_mono (integrable_K_integrand hy)
    ((hi0.const_mul (1-y^2)).add (hi1.const_mul (y^2))) hp
  simp only [Pi.add_apply] at hi
  rw [integral_add (hi0.const_mul _) (hi1.const_mul _),integral_const_mul,integral_const_mul] at hi
  dsimp [endpointK]
  simp only [zero_pow (by decide : (2:ℕ) ≠ 0),sub_zero,one_pow,sub_self,zero_add]
  nlinarith only [hi]

lemma resolvent_quadratic {A y : ℝ} (hA : 1 < A) (hy : y ≤ 1) :
    1/(A-y) ≤ 1/A+y/A^2+y^2*(1/(A-1)-1/A-1/A^2) := by
  have hA0 : 0 < A := by linarith
  have hA1 : 0 < A-1 := by linarith
  have hAy : 0 < A-y := by linarith
  have he : (1/A+y/A^2+y^2*(1/(A-1)-1/A-1/A^2))-1/(A-y) =
      y^2*(1-y)/(A^2*(A-1)*(A-y)) := by
    field_simp
    ring
  have hz : 0 ≤ y^2*(1-y)/(A^2*(A-1)*(A-y)) :=
    div_nonneg (mul_nonneg (sq_nonneg _) (sub_nonneg.mpr hy)) (by positivity)
  linarith only [he,hz]

lemma endpointD_quadratic {y : ℝ} (hy : y ≤ 1) :
    endpointD y ≤ endpointD 0+endpointDPrime*y+
      y^2*(endpointD 1-endpointD 0-endpointDPrime) := by
  let b0 := fun h => v h^2/(2-m h)
  let b1 := fun h => v h^2/(1-m h)
  let bp := fun h => v h^2/(2-m h)^2
  have hi0 : Integrable b0 (fieldLaw (1/2)) := by
    simpa only [sub_zero,b0] using integrable_D_integrand (y := 0) (μ := fieldLaw (1/2)) (by norm_num)
  have hi1 : Integrable b1 (fieldLaw (1/2)) := by
    simpa only [b1,show (2:ℝ)-1=1 from by norm_num] using
      integrable_D_integrand (y := 1) (μ := fieldLaw (1/2)) (by norm_num)
  have hip : Integrable bp (fieldLaw (1/2)) := integrable_DPrime_integrand
  have hrem : Integrable (fun h => b1 h-b0 h-bp h) (fieldLaw (1/2)) :=
    (hi1.sub hi0).sub hip
  have ihl : Integrable (fun h => b0 h+y*bp h) (fieldLaw (1/2)) := hi0.add (hip.const_mul _)
  have hp (h : ℝ) : v h^2/(2-y-m h) ≤ b0 h+y*bp h+y^2*(b1 h-b0 h-bp h) := by
    have hh := mul_le_mul_of_nonneg_left (resolvent_quadratic (A := 2-m h) (by
      linarith [(m_bounds h).2]) hy) (sq_nonneg (v h))
    convert! hh using 1
    · have hd : (2:ℝ)-m h-y = 2-y-m h := by ring
      rw [hd]; ring
    · dsimp [b0,b1,bp]
      have hd : (2:ℝ)-m h-1 = 1-m h := by ring
      rw [hd]; ring
  have hi := integral_mono (integrable_D_integrand hy) (ihl.add (hrem.const_mul _)) hp
  simp only [Pi.add_apply] at hi
  rw [integral_add ihl (hrem.const_mul _),integral_add hi0 (hip.const_mul _),
    integral_const_mul,integral_const_mul] at hi
  have hir : (∫ h, b1 h-b0 h-bp h ∂fieldLaw (1/2)) =
      (∫ h, b1 h ∂fieldLaw (1/2))-(∫ h, b0 h ∂fieldLaw (1/2))-(∫ h, bp h ∂fieldLaw (1/2)) := by
    have hsub : Integrable (fun h => b1 h-b0 h) (fieldLaw (1/2)) := hi1.sub hi0
    rw [integral_sub hsub hip,integral_sub hi1 hi0]
  rw [hir] at hi
  dsimp [endpointD,endpointDPrime]
  simp only [sub_zero,show (2:ℝ)-1=1 from by norm_num]
  dsimp [b0,b1,bp] at hi
  nlinarith only [hi]

lemma endpointD_field (h : ℝ) : diagonal (fieldLaw (1/2)) (1/2) h = endpointD (m h) := by
  unfold diagonal endpointD w
  have hd (t : ℝ) : 1-m h+(1-m t) = 2-m h-m t := by ring
  simp_rw [hd]
  congr 1
  norm_num

lemma endpointK_field (h : ℝ) : cost (fieldLaw (1/2)) (1/2) h = endpointK (m h) := by
  unfold cost endpointK
  norm_num only [show (1/2:ℝ)^2/4 = 1/16 by norm_num]
  rw [←integral_const_mul]
  apply integral_congr_ae
  apply ae_of_all
  intro t
  rw [v]
  change (1/16)*(v t+(1-m h^2))^2/multiplier t = (1/16)*((1-m h^2+v t)^2/multiplier t)
  ring

lemma envelope_of_endpoint_data
    (hk0 : endpointK 0 ≤ 4280/10000) (hk1 : endpointK 1 ≤ 902/10000)
    (hd0 : endpointD 0 ≤ 929/10000) (hd1 : endpointD 1 ≤ 2292/10000)
    (hdp0 : 520/10000 ≤ endpointDPrime) (hdp1 : endpointDPrime ≤ 526/10000)
    {β : ℝ} (hβ : 0 < β) (hβh : β ≤ 1/2) (h : ℝ) :
    multiplier h+diagonal (fieldLaw β) β h+cost (fieldLaw β) β h ≤ 9789/10000 := by
  have hm := m_bounds h
  have hma : |m h| ≤ 1 := (abs_lt.mpr hm).le
  have hy2 : m h^2 ≤ 1 := (tanh_sq_lt_one h).le
  have hD := diagonal_temperature_mono hβ hβh (by norm_num : (1/2:ℝ) ≤ 1) h
  have hK := cost_temperature_mono hβ hβh (by norm_num : (1/2:ℝ) ≤ 1) h
  rw [endpointD_field] at hD
  rw [endpointK_field] at hK
  have hDQ := endpointD_quadratic hm.2.le
  have hKQ := endpointK_quadratic hma
  have hA : 45/100+endpointD 0+endpointK 0 ≤ (9709/10000:ℝ) := by linarith
  have hB : 70/100+endpointK 1+endpointD 1-endpointDPrime ≤ (9709/10000:ℝ) := by linarith
  have hM : |endpointDPrime-6/100| ≤ (80/10000:ℝ) := by
    rw [abs_le]
    constructor <;> linarith
  have hC : (endpointDPrime-6/100)*m h ≤ (80/10000:ℝ) := by
    calc
      _ ≤ |endpointDPrime-6/100| *|m h| := by rw [←abs_mul]; exact le_abs_self _
      _ ≤ 80/10000 := by nlinarith [mul_le_mul hM hma (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 80/10000)]
  have hAw := mul_le_mul_of_nonneg_left hA (sub_nonneg.mpr hy2)
  have hBw := mul_le_mul_of_nonneg_left hB (sq_nonneg (m h))
  unfold multiplier
  nlinarith only [hD,hK,hDQ,hKQ,hAw,hBw,hC]

end SKRatio.Scalar

end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Certificates_CertifiedEndpointAssembly
attribute [-instance] _root_.OAI.SKRatio.Observation.History.historyMeasurable
attribute [-simp] _root_.OAI.SKRatio.Planted.compactWeight_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Real MeasureTheory
namespace SKRatio.Certificate
open Scalar

lemma endpointD_zero_integral (β A C M Q : ℝ) : endpointD 0 =
    ∫ h, scalarFunction β A C M Q 10 h ∂fieldLaw (1/2) := by
  unfold endpointD
  simp only [sub_zero]
  rw [←integral_const_mul]
  apply integral_congr_ae
  exact ae_of_all _ (fun h => by norm_num [scalarFunction]; ring)

lemma endpointD_one_integral (β A C M Q : ℝ) : endpointD 1 =
    ∫ h, scalarFunction β A C M Q 12 h ∂fieldLaw (1/2) := by
  unfold endpointD
  norm_num only [show (2:ℝ)-1=1 by norm_num]
  rw [←integral_const_mul]
  apply integral_congr_ae
  apply ae_of_all
  intro h
  have hd : 1-m h ≠ 0 := by linarith only [(m_bounds h).2]
  norm_num only [scalarFunction]
  rw [v_factor,w]
  field_simp
  ring

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
-- module Solutions.OAIQ024_SK.SKRatio_Certificates_ScalarDataJ4K10
attribute [-instance] _root_.OAI.SKRatio.Observation.History.historyBorel _root_.OAI.SKRatio.Observation.History.historyMeasurable _root_.OAI.SKRatio.Observation.History.historyTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Real MeasureTheory
namespace SKRatio.Certificate.Data.J4K10

theorem integral_bound :
    (∫ h, scalarFunction (1/2) (397973/500000) (524071/1000000) (119553/1000000) (702377/1000000) 10 h ∂Scalar.fieldLaw (1/2)) ∈ (⟨0,929/10000⟩ : Box) := by
  apply gaussian_certificate (e := expression) (B := blocks) (h := (1/20)) (k := 10) (by norm_num)
  · simpa only [expression,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero] using integrandExpr_val (1/2) (397973/500000) (524071/1000000) (119553/1000000) (702377/1000000) 10
  · exact (continuous_scalarFunction _ _ _ _ _ _).measurable
  · intro x
    apply scalarFunction_bound <;> norm_num
  · exact checks
  · decide +kernel

end SKRatio.Certificate.Data.J4K10

end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Certificates_ScalarDataJ4K12
attribute [-instance] _root_.OAI.SKRatio.Observation.History.historyBorel _root_.OAI.SKRatio.Observation.History.historyMeasurable _root_.OAI.SKRatio.Observation.History.historyTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Real MeasureTheory
namespace SKRatio.Certificate.Data.J4K12

theorem integral_bound :
    (∫ h, scalarFunction (1/2) (397973/500000) (524071/1000000) (119553/1000000) (702377/1000000) 12 h ∂Scalar.fieldLaw (1/2)) ∈ (⟨0,573/2500⟩ : Box) := by
  apply gaussian_certificate (e := expression) (B := blocks) (h := (1/20)) (k := 10) (by norm_num)
  · simpa only [expression,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero] using integrandExpr_val (1/2) (397973/500000) (524071/1000000) (119553/1000000) (702377/1000000) 12
  · exact (continuous_scalarFunction _ _ _ _ _ _).measurable
  · intro x
    apply scalarFunction_bound <;> norm_num
  · exact checks
  · decide +kernel

end SKRatio.Certificate.Data.J4K12

end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Certificates_CertifiedEndpoints
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

lemma endpointD_zero_bound : endpointD 0 ≤ 929/10000 := by
  rw [endpointD_zero_integral (1/2) (397973/500000) (524071/1000000)
    (119553/1000000) (702377/1000000)]
  convert! Data.J4K10.integral_bound.2 using 1; norm_num

lemma endpointD_one_bound : endpointD 1 ≤ 2292/10000 := by
  rw [endpointD_one_integral (1/2) (397973/500000) (524071/1000000)
    (119553/1000000) (702377/1000000)]
  convert! Data.J4K12.integral_bound.2 using 1; norm_num

theorem diagonal_envelope_oai {β : ℝ} (hβ : 0 < β) (hβh : β ≤ 1/2) (h : ℝ) :
    multiplier h+diagonal (fieldLaw β) β h+cost (fieldLaw β) β h ≤ 9789/10000 :=
  envelope_of_endpoint_data endpointK_zero_bound endpointK_one_bound
    endpointD_zero_bound endpointD_one_bound endpointD_prime_lower endpointD_prime_upper
    hβ hβh h

end SKRatio.Certificate

end

end OAI
end

theorem solution : type_of% @OAI.SKRatio.Certificate.diagonal_envelope_oai := @OAI.SKRatio.Certificate.diagonal_envelope_oai
