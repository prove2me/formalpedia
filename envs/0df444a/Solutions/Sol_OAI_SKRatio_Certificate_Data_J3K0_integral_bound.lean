-- Prove2me | solution 1 for OAI.SKRatio.Certificate.Data.J3K0.integral_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T22:29:05.472951+00:00
-- url     : https://prove2.me/submissions/654c87d5-0003-4787-8749-959deebc481d

import Mathlib
import Definitions.Def_OAIQ024S016

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
-- module Solutions.OAIQ024_SK.SKRatio_Certificates_ScalarDataJ3K0
attribute [-instance] _root_.OAI.SKRatio.Observation.History.historyBorel _root_.OAI.SKRatio.Observation.History.historyMeasurable _root_.OAI.SKRatio.Observation.History.historyTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Real MeasureTheory
namespace SKRatio.Certificate.Data.J3K0

lemma check_0 : expression.check (-10+(0:ℚ)*(5*(1/10))) (1/10) 5 (blocks 0) = true := by decide +kernel
lemma check_1 : expression.check (-10+(1:ℚ)*(5*(1/10))) (1/10) 5 (blocks 1) = true := by decide +kernel
lemma check_2 : expression.check (-10+(2:ℚ)*(5*(1/10))) (1/10) 5 (blocks 2) = true := by decide +kernel
lemma check_3 : expression.check (-10+(3:ℚ)*(5*(1/10))) (1/10) 5 (blocks 3) = true := by decide +kernel
lemma check_4 : expression.check (-10+(4:ℚ)*(5*(1/10))) (1/10) 5 (blocks 4) = true := by decide +kernel
lemma check_5 : expression.check (-10+(5:ℚ)*(5*(1/10))) (1/10) 5 (blocks 5) = true := by decide +kernel
lemma check_6 : expression.check (-10+(6:ℚ)*(5*(1/10))) (1/10) 5 (blocks 6) = true := by decide +kernel
lemma check_7 : expression.check (-10+(7:ℚ)*(5*(1/10))) (1/10) 5 (blocks 7) = true := by decide +kernel
lemma check_8 : expression.check (-10+(8:ℚ)*(5*(1/10))) (1/10) 5 (blocks 8) = true := by decide +kernel
lemma check_9 : expression.check (-10+(9:ℚ)*(5*(1/10))) (1/10) 5 (blocks 9) = true := by decide +kernel
lemma check_10 : expression.check (-10+(10:ℚ)*(5*(1/10))) (1/10) 5 (blocks 10) = true := by decide +kernel
lemma check_11 : expression.check (-10+(11:ℚ)*(5*(1/10))) (1/10) 5 (blocks 11) = true := by decide +kernel
lemma check_12 : expression.check (-10+(12:ℚ)*(5*(1/10))) (1/10) 5 (blocks 12) = true := by decide +kernel
lemma check_13 : expression.check (-10+(13:ℚ)*(5*(1/10))) (1/10) 5 (blocks 13) = true := by decide +kernel
lemma check_14 : expression.check (-10+(14:ℚ)*(5*(1/10))) (1/10) 5 (blocks 14) = true := by decide +kernel
lemma check_15 : expression.check (-10+(15:ℚ)*(5*(1/10))) (1/10) 5 (blocks 15) = true := by decide +kernel
lemma check_16 : expression.check (-10+(16:ℚ)*(5*(1/10))) (1/10) 5 (blocks 16) = true := by decide +kernel
lemma check_17 : expression.check (-10+(17:ℚ)*(5*(1/10))) (1/10) 5 (blocks 17) = true := by decide +kernel
lemma check_18 : expression.check (-10+(18:ℚ)*(5*(1/10))) (1/10) 5 (blocks 18) = true := by decide +kernel
lemma check_19 : expression.check (-10+(19:ℚ)*(5*(1/10))) (1/10) 5 (blocks 19) = true := by decide +kernel
lemma check_20 : expression.check (-10+(20:ℚ)*(5*(1/10))) (1/10) 5 (blocks 20) = true := by decide +kernel
lemma check_21 : expression.check (-10+(21:ℚ)*(5*(1/10))) (1/10) 5 (blocks 21) = true := by decide +kernel
lemma check_22 : expression.check (-10+(22:ℚ)*(5*(1/10))) (1/10) 5 (blocks 22) = true := by decide +kernel
lemma check_23 : expression.check (-10+(23:ℚ)*(5*(1/10))) (1/10) 5 (blocks 23) = true := by decide +kernel
lemma check_24 : expression.check (-10+(24:ℚ)*(5*(1/10))) (1/10) 5 (blocks 24) = true := by decide +kernel
lemma check_25 : expression.check (-10+(25:ℚ)*(5*(1/10))) (1/10) 5 (blocks 25) = true := by decide +kernel
lemma check_26 : expression.check (-10+(26:ℚ)*(5*(1/10))) (1/10) 5 (blocks 26) = true := by decide +kernel
lemma check_27 : expression.check (-10+(27:ℚ)*(5*(1/10))) (1/10) 5 (blocks 27) = true := by decide +kernel
lemma check_28 : expression.check (-10+(28:ℚ)*(5*(1/10))) (1/10) 5 (blocks 28) = true := by decide +kernel
lemma check_29 : expression.check (-10+(29:ℚ)*(5*(1/10))) (1/10) 5 (blocks 29) = true := by decide +kernel
lemma check_30 : expression.check (-10+(30:ℚ)*(5*(1/10))) (1/10) 5 (blocks 30) = true := by decide +kernel
lemma check_31 : expression.check (-10+(31:ℚ)*(5*(1/10))) (1/10) 5 (blocks 31) = true := by decide +kernel
lemma check_32 : expression.check (-10+(32:ℚ)*(5*(1/10))) (1/10) 5 (blocks 32) = true := by decide +kernel
lemma check_33 : expression.check (-10+(33:ℚ)*(5*(1/10))) (1/10) 5 (blocks 33) = true := by decide +kernel
lemma check_34 : expression.check (-10+(34:ℚ)*(5*(1/10))) (1/10) 5 (blocks 34) = true := by decide +kernel
lemma check_35 : expression.check (-10+(35:ℚ)*(5*(1/10))) (1/10) 5 (blocks 35) = true := by decide +kernel
lemma check_36 : expression.check (-10+(36:ℚ)*(5*(1/10))) (1/10) 5 (blocks 36) = true := by decide +kernel
lemma check_37 : expression.check (-10+(37:ℚ)*(5*(1/10))) (1/10) 5 (blocks 37) = true := by decide +kernel
lemma check_38 : expression.check (-10+(38:ℚ)*(5*(1/10))) (1/10) 5 (blocks 38) = true := by decide +kernel
lemma check_39 : expression.check (-10+(39:ℚ)*(5*(1/10))) (1/10) 5 (blocks 39) = true := by decide +kernel

lemma checks (i : ℕ) (hi : i < 40) :
    expression.check (-10+(i:ℚ)*(5*(1/10))) (1/10) 5 (blocks i) = true := by
  interval_cases i
  · exact check_0
  · exact check_1
  · exact check_2
  · exact check_3
  · exact check_4
  · exact check_5
  · exact check_6
  · exact check_7
  · exact check_8
  · exact check_9
  · exact check_10
  · exact check_11
  · exact check_12
  · exact check_13
  · exact check_14
  · exact check_15
  · exact check_16
  · exact check_17
  · exact check_18
  · exact check_19
  · exact check_20
  · exact check_21
  · exact check_22
  · exact check_23
  · exact check_24
  · exact check_25
  · exact check_26
  · exact check_27
  · exact check_28
  · exact check_29
  · exact check_30
  · exact check_31
  · exact check_32
  · exact check_33
  · exact check_34
  · exact check_35
  · exact check_36
  · exact check_37
  · exact check_38
  · exact check_39

theorem integral_bound_oai :
    (∫ h, scalarFunction (19/40) (406349/500000) (66273/125000) (28579/250000) (135787/200000) 0 h ∂Scalar.fieldLaw (19/40)) ∈ (⟨405599/500000,407099/500000⟩ : Box) := by
  apply gaussian_certificate (e := expression) (B := blocks) (h := (1/10)) (k := 5) (by norm_num)
  · simpa only [expression,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero] using integrandExpr_val (19/40) (406349/500000) (66273/125000) (28579/250000) (135787/200000) 0
  · exact (continuous_scalarFunction _ _ _ _ _ _).measurable
  · intro x
    apply scalarFunction_bound <;> norm_num
  · exact checks
  · decide +kernel

end SKRatio.Certificate.Data.J3K0

end

end OAI
end

theorem solution : type_of% @OAI.SKRatio.Certificate.Data.J3K0.integral_bound_oai := @OAI.SKRatio.Certificate.Data.J3K0.integral_bound_oai
