-- Prove2me | solution 1 for OAI.GaussianPropeller.FourCertificates.small_of_loss
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-19T00:20:44.149146+00:00
-- url     : https://prove2.me/submissions/9bd05b6f-14d5-4a41-8b76-69d40b8ff830

import Mathlib
import Definitions.Def_HairerSPDE_CameronMartin
import Definitions.Def_OAIQWGP000
import Theorems.Thm_OAI_GaussianPropeller_Mills_gaussian_tail_le_sampford

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

lemma hasDerivAt_density (x : ℝ) : HasDerivAt density (-x*density x) x := by
  unfold density
  convert (((hasDerivAt_pow 2 x).neg.div_const 2).exp) using 1 <;> first | rfl | ring1 | (norm_num <;> ring1)

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

lemma barrier_pos {x : ℝ} (hx : 0 ≤ x) : 0 < barrier x := by
  unfold barrier
  have : 0 < Real.sqrt (x^2+8) := Real.sqrt_pos.mpr (by positivity)
  positivity

lemma tail_le_barrier {x : ℝ} (hx : 0 ≤ x) : tail x ≤ density x / barrier x :=
  gaussian_tail_le_sampford hx

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
end

section
-- module Solutions.OAIQW_GaussianPropeller.Taylor
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

open MeasureTheory Set Filter
open scoped Topology BigOperators

namespace GaussianPropeller.Taylor

lemma E_zero (n : ℕ) : E n 0 = 1 := by
  unfold E
  rw [Finset.sum_eq_single 0]
  · norm_num
  · intro k hk hk0
    simp [zero_pow hk0]
  · simp

lemma exp_remainder {x : ℝ} (hx : 0 < x) (n : ℕ) :
    ∃ c : ℝ, Real.exp (-x)-E n x =
      (-1:ℝ)^(n+1)*Real.exp (-c)*x^(n+1)/(Nat.factorial (n+1)) := by
  obtain ⟨c,hc,h⟩ := taylor_mean_remainder_lagrange_iteratedDeriv
    (f := fun t : ℝ => Real.exp ((-1)*t)) (x₀ := 0) (x := x) (n := n) hx.ne
    (by fun_prop)
  refine ⟨c, ?_⟩
  have he : taylorWithinEval (fun t : ℝ => Real.exp ((-1)*t)) n (uIcc 0 x) 0 x = E n x := by
    rw [taylor_within_apply]
    apply Finset.sum_congr rfl
    intro k hk
    rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_uIcc hx.ne)
      (by fun_prop) (by simp), iteratedDeriv_exp_const_mul]
    simp only [mul_zero, Real.exp_zero, mul_one, sub_zero, smul_eq_mul]
    ring
  rw [he, iteratedDeriv_exp_const_mul] at h
  simpa only [neg_one_mul, sub_zero, mul_assoc] using h

lemma exp_le_E_even (n : ℕ) {x : ℝ} (hx : 0 ≤ x) : Real.exp (-x) ≤ E (2*n) x := by
  obtain rfl | hp := hx.eq_or_lt
  · simp [E_zero]
  obtain ⟨c,h⟩ := exp_remainder hp (2*n)
  have hn : (-1:ℝ)^(2*n+1) = -1 := by rw [pow_add, pow_mul]; norm_num
  rw [hn] at h
  have : (-1:ℝ)*Real.exp (-c)*x^(2*n+1)/(Nat.factorial (2*n+1)) ≤ 0 := by
    apply div_nonpos_of_nonpos_of_nonneg
    · exact mul_nonpos_of_nonpos_of_nonneg (by linarith [Real.exp_pos (-c)]) (pow_nonneg hx _)
    · positivity
  linarith only [h,this]

lemma E_odd_le_exp (n : ℕ) {x : ℝ} (hx : 0 ≤ x) : E (2*n+1) x ≤ Real.exp (-x) := by
  obtain rfl | hp := hx.eq_or_lt
  · simp [E_zero]
  obtain ⟨c,h⟩ := exp_remainder hp (2*n+1)
  have hn : (-1:ℝ)^(2*n+1+1) = 1 := by rw [show 2*n+1+1=2*(n+1) by omega, pow_mul]; norm_num
  rw [hn] at h
  have : 0 ≤ (1:ℝ)*Real.exp (-c)*x^(2*n+1+1)/(Nat.factorial (2*n+1+1)) := by positivity
  linarith only [h,this]

lemma hasDerivAt_J (n : ℕ) (x : ℝ) : HasDerivAt (J n) (E n (x^2/2)) x := by
  unfold J E
  convert! HasDerivAt.sum (u := Finset.range (n+1)) (fun k hk =>
    (((hasDerivAt_pow (2*k+1) x).const_mul ((-1:ℝ)^k)).div_const
      ((2:ℝ)^k*(Nat.factorial k)*(2*k+1)))) using 1
  · funext y
    simp only [Finset.sum_apply]
  · apply Finset.sum_congr rfl
    intro k hk
    have hfact : (Nat.factorial k : ℝ) ≠ 0 := by positivity
    have hk' : (2*(k:ℝ)+1) ≠ 0 := by positivity
    simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
    rw [div_pow, pow_mul]
    field_simp

lemma J_zero (n : ℕ) : J n 0 = 0 := by simp [J]

lemma integral_E (n : ℕ) (x : ℝ) :
    ∫ t in (0:ℝ)..x, E n (t^2/2) = J n x := by
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => hasDerivAt_J n t)
    (show IntervalIntegrable (fun t : ℝ => E n (t^2/2)) volume 0 x from
      (by unfold E; exact (by fun_prop : Continuous _).intervalIntegrable _ _))
  simpa only [J_zero, sub_zero] using h

lemma integral_exp_bounds (n : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    J (2*n+1) x ≤ (∫ t in (0:ℝ)..x, Real.exp (-t^2/2)) ∧
      (∫ t in (0:ℝ)..x, Real.exp (-t^2/2)) ≤ J (2*n) x := by
  have hi (k : ℕ) : IntervalIntegrable (fun t : ℝ => E k (t^2/2)) volume 0 x := by
    unfold E; exact (by fun_prop : Continuous _).intervalIntegrable _ _
  have he : IntervalIntegrable (fun t : ℝ => Real.exp (-t^2/2)) volume 0 x := (by fun_prop : Continuous _).intervalIntegrable _ _
  constructor
  · rw [← integral_E]
    apply intervalIntegral.integral_mono_on hx (hi _) he
    intro t ht
    simpa only [neg_div] using E_odd_le_exp n (show (0:ℝ) ≤ t^2/2 by positivity)
  · rw [← integral_E]
    apply intervalIntegral.integral_mono_on hx he (hi _)
    intro t ht
    simpa only [neg_div] using exp_le_E_even n (show (0:ℝ) ≤ t^2/2 by positivity)
end GaussianPropeller.Taylor

end OAI
end

section
-- module Solutions.OAIQW_GaussianPropeller.ProbabilityBounds
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

lemma hasDerivAt_p (x : ℝ) : HasDerivAt p (-gaussianConst*density x) x := by
  convert (hasDerivAt_tail x).const_mul gaussianConst using 1 <;> first | rfl | ring

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

lemma lambda_taylor_upper {x : ℝ} (hx : 0 ≤ x) (n : ℕ) {L : ℝ} (hL : 0 ≤ L)
    (hJ : 0 ≤ J (2*n) x)
    (hc : (398943/1000000:ℝ)*E (2*n) (x^2/2) ≤
      L*(1/2-(398943/1000000:ℝ)*J (2*n) x)) : lambda x ≤ L := by
  have he := exp_le_E_even n (show 0 ≤ x^2/2 by positivity)
  rw [← neg_div] at he
  change density x ≤ E (2*n) (x^2/2) at he
  have hd : 0 ≤ density x := (Real.exp_pos _).le
  have hmul := mul_le_mul he gaussianConst_tight.2
    (le_trans (by norm_num) gaussianConst_tight.1) (hd.trans he)
  have ht := mul_le_mul_of_nonneg_left (p_taylor_lower hx n hJ) hL
  have hpos : 0 < gaussianConst := lt_of_lt_of_le (by norm_num) gaussianConst_tight.1
  rw [lambda, div_le_iff₀ (tail_pos x)]
  apply (mul_le_mul_iff_right₀ hpos).mp
  dsimp [p] at ht
  nlinarith only [hmul,hc,ht]

lemma G_upper_of_lambda {x L U : ℝ} (hx : 0 ≤ x) (h : lambda x ≤ L)
    (hLU : L*(L-x) ≤ U) : G x ≤ U := by
  have hl : 0 ≤ lambda x-x := (mul_nonneg_iff_of_pos_left (lambda_pos x)).mp (G_nonneg hx)
  have hh := mul_nonneg (sub_nonneg.mpr h)
    (show 0 ≤ L+lambda x-x by linarith [lambda_pos x])
  unfold G
  nlinarith only [hh,hLU]

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
end

section
-- module Solutions.OAIQW_GaussianPropeller.QuarticCertificates
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

lemma loss_row {r x lo q v u : ℝ} (hlo:0≤lo) (hr:lo≤r) (hx:0≤x)
    (hq:0≤q) (hv:0≤v) (hs:1-(4/3:ℝ)*lo^2≤v^2)
    (hnum : u*(1+v) < (9/(8*(31416/10000:ℝ)))*lo^2)
    (hL:loss q≤u) (hP:p x≤p q)
    (h : (9/(8*Real.pi))*r^2/(1+Real.sqrt (1-(4/3:ℝ)*r^2))≤loss x) : False := by
  have hC : (9/(8*(31416/10000:ℝ))) ≤ 9/(8*Real.pi) := by
    apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
    have hh := Real.pi_lt_d6
    linarith only [hh]
  have hrr : lo^2≤r^2 := sq_le_sq₀ hlo (hlo.trans hr) |>.mpr hr
  have hsv : Real.sqrt (1-(4/3:ℝ)*r^2)≤v := Real.sqrt_le_iff.mpr ⟨hv,by nlinarith only [hs,hrr]⟩
  have hxq : q≤x := by
    by_contra hh
    have hxq : x<q := lt_of_not_ge hh
    have hpstrict : p q<p x := by
      apply strictAnti_of_deriv_neg (fun y => ?_) hxq
      rw [(hasDerivAt_p y).deriv]
      have hc : 0<gaussianConst := by dsimp [gaussianConst]; positivity
      exact mul_neg_of_neg_of_pos (neg_neg_of_pos hc) (Real.exp_pos _)
    linarith only [hpstrict,hP]
  have hlxu := (loss_antitone hq hx hxq).trans hL
  have hh := (div_le_iff₀ (show 0<1+Real.sqrt (1-(4/3:ℝ)*r^2) by positivity)).mp (h.trans hlxu)
  have hl0 : 0 ≤ loss q := by unfold loss; exact mul_nonneg (sq_nonneg _) (G_nonneg hq)
  have hu : 0≤u := hl0.trans hL
  have hm := mul_le_mul_of_nonneg_left hsv hu
  have hc := mul_le_mul hC hrr (sq_nonneg lo) (by positivity : (0:ℝ)≤9/(8*Real.pi))
  nlinarith only [hnum,hh,hm,hc]

lemma small_mono : MonotoneOn small (Ici 0) := by
  intro a ha b hb hab
  have h2:=pow_le_pow_left₀ ha hab 2
  unfold small; linarith only [h2,hab]

end GaussianPropeller.FourCertificates

end OAI
end

section
-- module Solutions.OAIQW_GaussianPropeller.SmallCertificates
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

lemma small_0 {r x:ℝ} (hr:r∈Icc (39/250:ℝ) (157/1000:ℝ)) (hx:0≤x)
    (hl:(9/(8*Real.pi))*r^2/(1+Real.sqrt (1-(4/3:ℝ)*r^2))≤loss x) : small r < p x := by
  by_contra hn
  have hP : p x ≤ small (157/1000:ℝ) := (le_of_not_gt hn).trans (small_mono (by change 0≤r; linarith only [hr.1]) (by norm_num) hr.2)
  have hj : 0≤J 12 (9139/6250:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hj' : 0≤J 13 (9139/6250:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hpL : small (157/1000:ℝ) ≤ p (9139/6250:ℝ) := by
    apply le_trans ?_ (p_taylor_lower (by norm_num) 6 hj)
    norm_num [small,J,Finset.sum_range_succ,Nat.factorial]
  have hpU : p (9139/6250:ℝ)≤(449/6250:ℝ) := by
    apply le_trans (p_taylor_upper (by norm_num) 6 hj')
    norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hla : lambda (9139/6250:ℝ)≤(953337/500000:ℝ) := by
    apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj
    norm_num [E,J,Finset.sum_range_succ,Nat.factorial]
  have hg : G (9139/6250:ℝ)≤(847391/1000000:ℝ) := G_upper_of_lambda (by norm_num) hla (by norm_num)
  exact loss_row (lo:=(39/250:ℝ)) (q:=(9139/6250:ℝ)) (v:=(983643/1000000:ℝ))
    (u:=(449/6250:ℝ)^2*(847391/1000000:ℝ)) (by norm_num) hr.1 hx (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (loss_bound (by norm_num) hpU hg) (hP.trans hpL) hl

lemma small_1 {r x:ℝ} (hr:r∈Icc (157/1000:ℝ) (79/500:ℝ)) (hx:0≤x)
    (hl:(9/(8*Real.pi))*r^2/(1+Real.sqrt (1-(4/3:ℝ)*r^2))≤loss x) : small r < p x := by
  by_contra hn
  have hP : p x ≤ small (79/500:ℝ) := (le_of_not_gt hn).trans (small_mono (by change 0≤r; linarith only [hr.1]) (by norm_num) hr.2)
  have hj : 0≤J 12 (72937/50000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hj' : 0≤J 13 (72937/50000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hpL : small (79/500:ℝ) ≤ p (72937/50000:ℝ) := by
    apply le_trans ?_ (p_taylor_lower (by norm_num) 6 hj)
    norm_num [small,J,Finset.sum_range_succ,Nat.factorial]
  have hpU : p (72937/50000:ℝ)≤(72321/1000000:ℝ) := by
    apply le_trans (p_taylor_upper (by norm_num) 6 hj')
    norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hla : lambda (72937/50000:ℝ)≤(1903709/1000000:ℝ) := by
    apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj
    norm_num [E,J,Finset.sum_range_succ,Nat.factorial]
  have hg : G (72937/50000:ℝ)≤(211773/250000:ℝ) := G_upper_of_lambda (by norm_num) hla (by norm_num)
  exact loss_row (lo:=(157/1000:ℝ)) (q:=(72937/50000:ℝ)) (v:=(983431/1000000:ℝ))
    (u:=(72321/1000000:ℝ)^2*(211773/250000:ℝ)) (by norm_num) hr.1 hx (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (loss_bound (by norm_num) hpU hg) (hP.trans hpL) hl

lemma small_2 {r x:ℝ} (hr:r∈Icc (79/500:ℝ) (159/1000:ℝ)) (hx:0≤x)
    (hl:(9/(8*Real.pi))*r^2/(1+Real.sqrt (1-(4/3:ℝ)*r^2))≤loss x) : small r < p x := by
  by_contra hn
  have hP : p x ≤ small (159/1000:ℝ) := (le_of_not_gt hn).trans (small_mono (by change 0≤r; linarith only [hr.1]) (by norm_num) hr.2)
  have hj : 0≤J 12 (5821/4000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hj' : 0≤J 13 (5821/4000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hpL : small (159/1000:ℝ) ≤ p (5821/4000:ℝ) := by
    apply le_trans ?_ (p_taylor_lower (by norm_num) 6 hj)
    norm_num [small,J,Finset.sum_range_succ,Nat.factorial]
  have hpU : p (5821/4000:ℝ)≤(72803/1000000:ℝ) := by
    apply le_trans (p_taylor_upper (by norm_num) 6 hj')
    norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hla : lambda (5821/4000:ℝ)≤(950377/500000:ℝ) := by
    apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj
    norm_num [E,J,Finset.sum_range_succ,Nat.factorial]
  have hg : G (5821/4000:ℝ)≤(423397/500000:ℝ) := G_upper_of_lambda (by norm_num) hla (by norm_num)
  exact loss_row (lo:=(79/500:ℝ)) (q:=(5821/4000:ℝ)) (v:=(983217/1000000:ℝ))
    (u:=(72803/1000000:ℝ)^2*(423397/500000:ℝ)) (by norm_num) hr.1 hx (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (loss_bound (by norm_num) hpU hg) (hP.trans hpL) hl

lemma small_3 {r x:ℝ} (hr:r∈Icc (159/1000:ℝ) (4/25:ℝ)) (hx:0≤x)
    (hl:(9/(8*Real.pi))*r^2/(1+Real.sqrt (1-(4/3:ℝ)*r^2))≤loss x) : small r < p x := by
  by_contra hn
  have hP : p x ≤ small (4/25:ℝ) := (le_of_not_gt hn).trans (small_mono (by change 0≤r; linarith only [hr.1]) (by norm_num) hr.2)
  have hj : 0≤J 12 (72589/50000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hj' : 0≤J 13 (72589/50000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hpL : small (4/25:ℝ) ≤ p (72589/50000:ℝ) := by
    apply le_trans ?_ (p_taylor_lower (by norm_num) 6 hj)
    norm_num [small,J,Finset.sum_range_succ,Nat.factorial]
  have hpU : p (72589/50000:ℝ)≤(18321/250000:ℝ) := by
    apply le_trans (p_taylor_upper (by norm_num) 6 hj')
    norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hla : lambda (72589/50000:ℝ)≤(1897817/1000000:ℝ) := by
    apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj
    norm_num [E,J,Finset.sum_range_succ,Nat.factorial]
  have hg : G (72589/50000:ℝ)≤(846497/1000000:ℝ) := G_upper_of_lambda (by norm_num) hla (by norm_num)
  exact loss_row (lo:=(159/1000:ℝ)) (q:=(72589/50000:ℝ)) (v:=(491501/500000:ℝ))
    (u:=(18321/250000:ℝ)^2*(846497/1000000:ℝ)) (by norm_num) hr.1 hx (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (loss_bound (by norm_num) hpU hg) (hP.trans hpL) hl

lemma small_4 {r x:ℝ} (hr:r∈Icc (4/25:ℝ) (161/1000:ℝ)) (hx:0≤x)
    (hl:(9/(8*Real.pi))*r^2/(1+Real.sqrt (1-(4/3:ℝ)*r^2))≤loss x) : small r < p x := by
  by_contra hn
  have hP : p x ≤ small (161/1000:ℝ) := (le_of_not_gt hn).trans (small_mono (by change 0≤r; linarith only [hr.1]) (by norm_num) hr.2)
  have hj : 0≤J 12 (4526/3125:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hj' : 0≤J 13 (4526/3125:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hpL : small (161/1000:ℝ) ≤ p (4526/3125:ℝ) := by
    apply le_trans ?_ (p_taylor_lower (by norm_num) 6 hj)
    norm_num [small,J,Finset.sum_range_succ,Nat.factorial]
  have hpU : p (4526/3125:ℝ)≤(36883/500000:ℝ) := by
    apply le_trans (p_taylor_upper (by norm_num) 6 hj')
    norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hla : lambda (4526/3125:ℝ)≤(1894889/1000000:ℝ) := by
    apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj
    norm_num [E,J,Finset.sum_range_succ,Nat.factorial]
  have hg : G (4526/3125:ℝ)≤(846199/1000000:ℝ) := G_upper_of_lambda (by norm_num) hla (by norm_num)
  exact loss_row (lo:=(4/25:ℝ)) (q:=(4526/3125:ℝ)) (v:=(491393/500000:ℝ))
    (u:=(36883/500000:ℝ)^2*(846199/1000000:ℝ)) (by norm_num) hr.1 hx (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (loss_bound (by norm_num) hpU hg) (hP.trans hpL) hl

lemma small_5 {r x:ℝ} (hr:r∈Icc (161/1000:ℝ) (81/500:ℝ)) (hx:0≤x)
    (hl:(9/(8*Real.pi))*r^2/(1+Real.sqrt (1-(4/3:ℝ)*r^2))≤loss x) : small r < p x := by
  by_contra hn
  have hP : p x ≤ small (81/500:ℝ) := (le_of_not_gt hn).trans (small_mono (by change 0≤r; linarith only [hr.1]) (by norm_num) hr.2)
  have hj : 0≤J 12 (144487/100000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hj' : 0≤J 13 (144487/100000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hpL : small (81/500:ℝ) ≤ p (144487/100000:ℝ) := by
    apply le_trans ?_ (p_taylor_lower (by norm_num) 6 hj)
    norm_num [small,J,Finset.sum_range_succ,Nat.factorial]
  have hpU : p (144487/100000:ℝ)≤(297/4000:ℝ) := by
    apply le_trans (p_taylor_upper (by norm_num) 6 hj')
    norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hla : lambda (144487/100000:ℝ)≤(189197/100000:ℝ) := by
    apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj
    norm_num [E,J,Finset.sum_range_succ,Nat.factorial]
  have hg : G (144487/100000:ℝ)≤(8459/10000:ℝ) := G_upper_of_lambda (by norm_num) hla (by norm_num)
  exact loss_row (lo:=(161/1000:ℝ)) (q:=(144487/100000:ℝ)) (v:=(122821/125000:ℝ))
    (u:=(297/4000:ℝ)^2*(8459/10000:ℝ)) (by norm_num) hr.1 hx (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (loss_bound (by norm_num) hpU hg) (hP.trans hpL) hl

lemma small_6 {r x:ℝ} (hr:r∈Icc (81/500:ℝ) (163/1000:ℝ)) (hx:0≤x)
    (hl:(9/(8*Real.pi))*r^2/(1+Real.sqrt (1-(4/3:ℝ)*r^2))≤loss x) : small r < p x := by
  by_contra hn
  have hP : p x ≤ small (163/1000:ℝ) := (le_of_not_gt hn).trans (small_mono (by change 0≤r; linarith only [hr.1]) (by norm_num) hr.2)
  have hj : 0≤J 12 (28829/20000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hj' : 0≤J 13 (28829/20000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hpL : small (163/1000:ℝ) ≤ p (28829/20000:ℝ) := by
    apply le_trans ?_ (p_taylor_lower (by norm_num) 6 hj)
    norm_num [small,J,Finset.sum_range_succ,Nat.factorial]
  have hpU : p (28829/20000:ℝ)≤(74731/1000000:ℝ) := by
    apply le_trans (p_taylor_upper (by norm_num) 6 hj')
    norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hla : lambda (28829/20000:ℝ)≤(944539/500000:ℝ) := by
    apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj
    norm_num [E,J,Finset.sum_range_succ,Nat.factorial]
  have hg : G (28829/20000:ℝ)≤(169121/200000:ℝ) := G_upper_of_lambda (by norm_num) hla (by norm_num)
  exact loss_row (lo:=(81/500:ℝ)) (q:=(28829/20000:ℝ)) (v:=(982349/1000000:ℝ))
    (u:=(74731/1000000:ℝ)^2*(169121/200000:ℝ)) (by norm_num) hr.1 hx (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (loss_bound (by norm_num) hpU hg) (hP.trans hpL) hl

lemma small_7 {r x:ℝ} (hr:r∈Icc (163/1000:ℝ) (41/250:ℝ)) (hx:0≤x)
    (hl:(9/(8*Real.pi))*r^2/(1+Real.sqrt (1-(4/3:ℝ)*r^2))≤loss x) : small r < p x := by
  by_contra hn
  have hP : p x ≤ small (41/250:ℝ) := (le_of_not_gt hn).trans (small_mono (by change 0≤r; linarith only [hr.1]) (by norm_num) hr.2)
  have hj : 0≤J 12 (143803/100000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hj' : 0≤J 13 (143803/100000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hpL : small (41/250:ℝ) ≤ p (143803/100000:ℝ) := by
    apply le_trans ?_ (p_taylor_lower (by norm_num) 6 hj)
    norm_num [small,J,Finset.sum_range_succ,Nat.factorial]
  have hpU : p (143803/100000:ℝ)≤(15043/200000:ℝ) := by
    apply le_trans (p_taylor_upper (by norm_num) 6 hj')
    norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hla : lambda (143803/100000:ℝ)≤(1886187/1000000:ℝ) := by
    apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj
    norm_num [E,J,Finset.sum_range_succ,Nat.factorial]
  have hg : G (143803/100000:ℝ)≤(211327/250000:ℝ) := G_upper_of_lambda (by norm_num) hla (by norm_num)
  exact loss_row (lo:=(163/1000:ℝ)) (q:=(143803/100000:ℝ)) (v:=(61383/62500:ℝ))
    (u:=(15043/200000:ℝ)^2*(211327/250000:ℝ)) (by norm_num) hr.1 hx (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (loss_bound (by norm_num) hpU hg) (hP.trans hpL) hl

lemma small_8 {r x:ℝ} (hr:r∈Icc (41/250:ℝ) (33/200:ℝ)) (hx:0≤x)
    (hl:(9/(8*Real.pi))*r^2/(1+Real.sqrt (1-(4/3:ℝ)*r^2))≤loss x) : small r < p x := by
  by_contra hn
  have hP : p x ≤ small (33/200:ℝ) := (le_of_not_gt hn).trans (small_mono (by change 0≤r; linarith only [hr.1]) (by norm_num) hr.2)
  have hj : 0≤J 12 (143463/100000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hj' : 0≤J 13 (143463/100000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hpL : small (33/200:ℝ) ≤ p (143463/100000:ℝ) := by
    apply le_trans ?_ (p_taylor_lower (by norm_num) 6 hj)
    norm_num [small,J,Finset.sum_range_succ,Nat.factorial]
  have hpU : p (143463/100000:ℝ)≤(75699/1000000:ℝ) := by
    apply le_trans (p_taylor_upper (by norm_num) 6 hj')
    norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hla : lambda (143463/100000:ℝ)≤(941657/500000:ℝ) := by
    apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj
    norm_num [E,J,Finset.sum_range_succ,Nat.factorial]
  have hg : G (143463/100000:ℝ)≤(845013/1000000:ℝ) := G_upper_of_lambda (by norm_num) hla (by norm_num)
  exact loss_row (lo:=(41/250:ℝ)) (q:=(143463/100000:ℝ)) (v:=(490953/500000:ℝ))
    (u:=(75699/1000000:ℝ)^2*(845013/1000000:ℝ)) (by norm_num) hr.1 hx (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (loss_bound (by norm_num) hpU hg) (hP.trans hpL) hl

lemma small_9 {r x:ℝ} (hr:r∈Icc (33/200:ℝ) (83/500:ℝ)) (hx:0≤x)
    (hl:(9/(8*Real.pi))*r^2/(1+Real.sqrt (1-(4/3:ℝ)*r^2))≤loss x) : small r < p x := by
  by_contra hn
  have hP : p x ≤ small (83/500:ℝ) := (le_of_not_gt hn).trans (small_mono (by change 0≤r; linarith only [hr.1]) (by norm_num) hr.2)
  have hj : 0≤J 12 (229/160:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hj' : 0≤J 13 (229/160:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hpL : small (83/500:ℝ) ≤ p (229/160:ℝ) := by
    apply le_trans ?_ (p_taylor_lower (by norm_num) 6 hj)
    norm_num [small,J,Finset.sum_range_succ,Nat.factorial]
  have hpU : p (229/160:ℝ)≤(38091/500000:ℝ) := by
    apply le_trans (p_taylor_upper (by norm_num) 6 hj')
    norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hla : lambda (229/160:ℝ)≤(1880459/1000000:ℝ) := by
    apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj
    norm_num [E,J,Finset.sum_range_succ,Nat.factorial]
  have hg : G (229/160:ℝ)≤(10559/12500:ℝ) := G_upper_of_lambda (by norm_num) hla (by norm_num)
  exact loss_row (lo:=(33/200:ℝ)) (q:=(229/160:ℝ)) (v:=(981683/1000000:ℝ))
    (u:=(38091/500000:ℝ)^2*(10559/12500:ℝ)) (by norm_num) hr.1 hx (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (loss_bound (by norm_num) hpU hg) (hP.trans hpL) hl

lemma small_10 {r x:ℝ} (hr:r∈Icc (83/500:ℝ) (167/1000:ℝ)) (hx:0≤x)
    (hl:(9/(8*Real.pi))*r^2/(1+Real.sqrt (1-(4/3:ℝ)*r^2))≤loss x) : small r < p x := by
  by_contra hn
  have hP : p x ≤ small (167/1000:ℝ) := (le_of_not_gt hn).trans (small_mono (by change 0≤r; linarith only [hr.1]) (by norm_num) hr.2)
  have hj : 0≤J 12 (35697/25000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hj' : 0≤J 13 (35697/25000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hpL : small (167/1000:ℝ) ≤ p (35697/25000:ℝ) := by
    apply le_trans ?_ (p_taylor_lower (by norm_num) 6 hj)
    norm_num [small,J,Finset.sum_range_succ,Nat.factorial]
  have hpU : p (35697/25000:ℝ)≤(38333/500000:ℝ) := by
    apply le_trans (p_taylor_upper (by norm_num) 6 hj')
    norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hla : lambda (35697/25000:ℝ)≤(1877613/1000000:ℝ) := by
    apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj
    norm_num [E,J,Finset.sum_range_succ,Nat.factorial]
  have hg : G (35697/25000:ℝ)≤(33777/40000:ℝ) := G_upper_of_lambda (by norm_num) hla (by norm_num)
  exact loss_row (lo:=(83/500:ℝ)) (q:=(35697/25000:ℝ)) (v:=(490729/500000:ℝ))
    (u:=(38333/500000:ℝ)^2*(33777/40000:ℝ)) (by norm_num) hr.1 hx (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (loss_bound (by norm_num) hpU hg) (hP.trans hpL) hl

lemma small_11 {r x:ℝ} (hr:r∈Icc (167/1000:ℝ) (21/125:ℝ)) (hx:0≤x)
    (hl:(9/(8*Real.pi))*r^2/(1+Real.sqrt (1-(4/3:ℝ)*r^2))≤loss x) : small r < p x := by
  by_contra hn
  have hP : p x ≤ small (21/125:ℝ) := (le_of_not_gt hn).trans (small_mono (by change 0≤r; linarith only [hr.1]) (by norm_num) hr.2)
  have hj : 0≤J 12 (35613/25000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hj' : 0≤J 13 (35613/25000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hpL : small (21/125:ℝ) ≤ p (35613/25000:ℝ) := by
    apply le_trans ?_ (p_taylor_lower (by norm_num) 6 hj)
    norm_num [small,J,Finset.sum_range_succ,Nat.factorial]
  have hpU : p (35613/25000:ℝ)≤(1543/20000:ℝ) := by
    apply le_trans (p_taylor_upper (by norm_num) 6 hj')
    norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hla : lambda (35613/25000:ℝ)≤(234347/125000:ℝ) := by
    apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj
    norm_num [E,J,Finset.sum_range_succ,Nat.factorial]
  have hg : G (35613/25000:ℝ)≤(84413/100000:ℝ) := G_upper_of_lambda (by norm_num) hla (by norm_num)
  exact loss_row (lo:=(167/1000:ℝ)) (q:=(35613/25000:ℝ)) (v:=(61327/62500:ℝ))
    (u:=(1543/20000:ℝ)^2*(84413/100000:ℝ)) (by norm_num) hr.1 hx (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (loss_bound (by norm_num) hpU hg) (hP.trans hpL) hl

lemma small_12 {r x:ℝ} (hr:r∈Icc (21/125:ℝ) (169/1000:ℝ)) (hx:0≤x)
    (hl:(9/(8*Real.pi))*r^2/(1+Real.sqrt (1-(4/3:ℝ)*r^2))≤loss x) : small r < p x := by
  by_contra hn
  have hP : p x ≤ small (169/1000:ℝ) := (le_of_not_gt hn).trans (small_mono (by change 0≤r; linarith only [hr.1]) (by norm_num) hr.2)
  have hj : 0≤J 12 (71059/50000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hj' : 0≤J 13 (71059/50000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hpL : small (169/1000:ℝ) ≤ p (71059/50000:ℝ) := by
    apply le_trans ?_ (p_taylor_lower (by norm_num) 6 hj)
    norm_num [small,J,Finset.sum_range_succ,Nat.factorial]
  have hpU : p (71059/50000:ℝ)≤(15527/200000:ℝ) := by
    apply le_trans (p_taylor_upper (by norm_num) 6 hj')
    norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hla : lambda (71059/50000:ℝ)≤(935979/500000:ℝ) := by
    apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj
    norm_num [E,J,Finset.sum_range_succ,Nat.factorial]
  have hg : G (71059/50000:ℝ)≤(421919/500000:ℝ) := G_upper_of_lambda (by norm_num) hla (by norm_num)
  exact loss_row (lo:=(21/125:ℝ)) (q:=(71059/50000:ℝ)) (v:=(245251/250000:ℝ))
    (u:=(15527/200000:ℝ)^2*(421919/500000:ℝ)) (by norm_num) hr.1 hx (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (loss_bound (by norm_num) hpU hg) (hP.trans hpL) hl

lemma small_13 {r x:ℝ} (hr:r∈Icc (169/1000:ℝ) (17/100:ℝ)) (hx:0≤x)
    (hl:(9/(8*Real.pi))*r^2/(1+Real.sqrt (1-(4/3:ℝ)*r^2))≤loss x) : small r < p x := by
  by_contra hn
  have hP : p x ≤ small (17/100:ℝ) := (le_of_not_gt hn).trans (small_mono (by change 0≤r; linarith only [hr.1]) (by norm_num) hr.2)
  have hj : 0≤J 12 (28357/20000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hj' : 0≤J 13 (28357/20000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hpL : small (17/100:ℝ) ≤ p (28357/20000:ℝ) := by
    apply le_trans ?_ (p_taylor_lower (by norm_num) 6 hj)
    norm_num [small,J,Finset.sum_range_succ,Nat.factorial]
  have hpU : p (28357/20000:ℝ)≤(1953/25000:ℝ) := by
    apply le_trans (p_taylor_upper (by norm_num) 6 hj')
    norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hla : lambda (28357/20000:ℝ)≤(1869149/1000000:ℝ) := by
    apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj
    norm_num [E,J,Finset.sum_range_succ,Nat.factorial]
  have hg : G (28357/20000:ℝ)≤(421773/500000:ℝ) := G_upper_of_lambda (by norm_num) hla (by norm_num)
  exact loss_row (lo:=(169/1000:ℝ)) (q:=(28357/20000:ℝ)) (v:=(39231/40000:ℝ))
    (u:=(1953/25000:ℝ)^2*(421773/500000:ℝ)) (by norm_num) hr.1 hx (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (loss_bound (by norm_num) hpU hg) (hP.trans hpL) hl

lemma small_14 {r x:ℝ} (hr:r∈Icc (17/100:ℝ) (171/1000:ℝ)) (hx:0≤x)
    (hl:(9/(8*Real.pi))*r^2/(1+Real.sqrt (1-(4/3:ℝ)*r^2))≤loss x) : small r < p x := by
  by_contra hn
  have hP : p x ≤ small (171/1000:ℝ) := (le_of_not_gt hn).trans (small_mono (by change 0≤r; linarith only [hr.1]) (by norm_num) hr.2)
  have hj : 0≤J 12 (70727/50000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hj' : 0≤J 13 (70727/50000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hpL : small (171/1000:ℝ) ≤ p (70727/50000:ℝ) := by
    apply le_trans ?_ (p_taylor_lower (by norm_num) 6 hj)
    norm_num [small,J,Finset.sum_range_succ,Nat.factorial]
  have hpU : p (70727/50000:ℝ)≤(19651/250000:ℝ) := by
    apply le_trans (p_taylor_upper (by norm_num) 6 hj')
    norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hla : lambda (70727/50000:ℝ)≤(933179/500000:ℝ) := by
    apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj
    norm_num [E,J,Finset.sum_range_succ,Nat.factorial]
  have hg : G (70727/50000:ℝ)≤(168651/200000:ℝ) := G_upper_of_lambda (by norm_num) hla (by norm_num)
  exact loss_row (lo:=(17/100:ℝ)) (q:=(70727/50000:ℝ)) (v:=(196109/200000:ℝ))
    (u:=(19651/250000:ℝ)^2*(168651/200000:ℝ)) (by norm_num) hr.1 hx (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (loss_bound (by norm_num) hpU hg) (hP.trans hpL) hl

lemma small_15 {r x:ℝ} (hr:r∈Icc (171/1000:ℝ) (43/250:ℝ)) (hx:0≤x)
    (hl:(9/(8*Real.pi))*r^2/(1+Real.sqrt (1-(4/3:ℝ)*r^2))≤loss x) : small r < p x := by
  by_contra hn
  have hP : p x ≤ small (43/250:ℝ) := (le_of_not_gt hn).trans (small_mono (by change 0≤r; linarith only [hr.1]) (by norm_num) hr.2)
  have hj : 0≤J 12 (141123/100000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hj' : 0≤J 13 (141123/100000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hpL : small (43/250:ℝ) ≤ p (141123/100000:ℝ) := by
    apply le_trans ?_ (p_taylor_lower (by norm_num) 6 hj)
    norm_num [small,J,Finset.sum_range_succ,Nat.factorial]
  have hpU : p (141123/100000:ℝ)≤(79091/1000000:ℝ) := by
    apply le_trans (p_taylor_upper (by norm_num) 6 hj')
    norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hla : lambda (141123/100000:ℝ)≤(1863567/1000000:ℝ) := by
    apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj
    norm_num [E,J,Finset.sum_range_succ,Nat.factorial]
  have hg : G (141123/100000:ℝ)≤(842961/1000000:ℝ) := G_upper_of_lambda (by norm_num) hla (by norm_num)
  exact loss_row (lo:=(171/1000:ℝ)) (q:=(141123/100000:ℝ)) (v:=(980313/1000000:ℝ))
    (u:=(79091/1000000:ℝ)^2*(842961/1000000:ℝ)) (by norm_num) hr.1 hx (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (loss_bound (by norm_num) hpU hg) (hP.trans hpL) hl

lemma small_16 {r x:ℝ} (hr:r∈Icc (43/250:ℝ) (173/1000:ℝ)) (hx:0≤x)
    (hl:(9/(8*Real.pi))*r^2/(1+Real.sqrt (1-(4/3:ℝ)*r^2))≤loss x) : small r < p x := by
  by_contra hn
  have hP : p x ≤ small (173/1000:ℝ) := (le_of_not_gt hn).trans (small_mono (by change 0≤r; linarith only [hr.1]) (by norm_num) hr.2)
  have hj : 0≤J 12 (28159/20000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hj' : 0≤J 13 (28159/20000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hpL : small (173/1000:ℝ) ≤ p (28159/20000:ℝ) := by
    apply le_trans ?_ (p_taylor_lower (by norm_num) 6 hj)
    norm_num [small,J,Finset.sum_range_succ,Nat.factorial]
  have hpU : p (28159/20000:ℝ)≤(3183/40000:ℝ) := by
    apply le_trans (p_taylor_upper (by norm_num) 6 hj')
    norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hla : lambda (28159/20000:ℝ)≤(1860803/1000000:ℝ) := by
    apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj
    norm_num [E,J,Finset.sum_range_succ,Nat.factorial]
  have hg : G (28159/20000:ℝ)≤(842671/1000000:ℝ) := G_upper_of_lambda (by norm_num) hla (by norm_num)
  exact loss_row (lo:=(43/250:ℝ)) (q:=(28159/20000:ℝ)) (v:=(980079/1000000:ℝ))
    (u:=(3183/40000:ℝ)^2*(842671/1000000:ℝ)) (by norm_num) hr.1 hx (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (loss_bound (by norm_num) hpU hg) (hP.trans hpL) hl

lemma small_17 {r x:ℝ} (hr:r∈Icc (173/1000:ℝ) (87/500:ℝ)) (hx:0≤x)
    (hl:(9/(8*Real.pi))*r^2/(1+Real.sqrt (1-(4/3:ℝ)*r^2))≤loss x) : small r < p x := by
  by_contra hn
  have hP : p x ≤ small (87/500:ℝ) := (le_of_not_gt hn).trans (small_mono (by change 0≤r; linarith only [hr.1]) (by norm_num) hr.2)
  have hj : 0≤J 12 (140467/100000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hj' : 0≤J 13 (140467/100000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hpL : small (87/500:ℝ) ≤ p (140467/100000:ℝ) := by
    apply le_trans ?_ (p_taylor_lower (by norm_num) 6 hj)
    norm_num [small,J,Finset.sum_range_succ,Nat.factorial]
  have hpU : p (140467/100000:ℝ)≤(40031/500000:ℝ) := by
    apply le_trans (p_taylor_upper (by norm_num) 6 hj')
    norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hla : lambda (140467/100000:ℝ)≤(46451/25000:ℝ) := by
    apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj
    norm_num [E,J,Finset.sum_range_succ,Nat.factorial]
  have hg : G (140467/100000:ℝ)≤(42119/50000:ℝ) := G_upper_of_lambda (by norm_num) hla (by norm_num)
  exact loss_row (lo:=(173/1000:ℝ)) (q:=(140467/100000:ℝ)) (v:=(195969/200000:ℝ))
    (u:=(40031/500000:ℝ)^2*(42119/50000:ℝ)) (by norm_num) hr.1 hx (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (loss_bound (by norm_num) hpU hg) (hP.trans hpL) hl

lemma small_18 {r x:ℝ} (hr:r∈Icc (87/500:ℝ) (7/40:ℝ)) (hx:0≤x)
    (hl:(9/(8*Real.pi))*r^2/(1+Real.sqrt (1-(4/3:ℝ)*r^2))≤loss x) : small r < p x := by
  by_contra hn
  have hP : p x ≤ small (7/40:ℝ) := (le_of_not_gt hn).trans (small_mono (by change 0≤r; linarith only [hr.1]) (by norm_num) hr.2)
  have hj : 0≤J 12 (140141/100000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hj' : 0≤J 13 (140141/100000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hpL : small (7/40:ℝ) ≤ p (140141/100000:ℝ) := by
    apply le_trans ?_ (p_taylor_lower (by norm_num) 6 hj)
    norm_num [small,J,Finset.sum_range_succ,Nat.factorial]
  have hpU : p (140141/100000:ℝ)≤(20137/250000:ℝ) := by
    apply le_trans (p_taylor_upper (by norm_num) 6 hj')
    norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hla : lambda (140141/100000:ℝ)≤(371059/200000:ℝ) := by
    apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj
    norm_num [E,J,Finset.sum_range_succ,Nat.factorial]
  have hg : G (140141/100000:ℝ)≤(842091/1000000:ℝ) := G_upper_of_lambda (by norm_num) hla (by norm_num)
  exact loss_row (lo:=(87/500:ℝ)) (q:=(140141/100000:ℝ)) (v:=(979609/1000000:ℝ))
    (u:=(20137/250000:ℝ)^2*(842091/1000000:ℝ)) (by norm_num) hr.1 hx (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (loss_bound (by norm_num) hpU hg) (hP.trans hpL) hl

lemma small_19 {r x:ℝ} (hr:r∈Icc (7/40:ℝ) (22/125:ℝ)) (hx:0≤x)
    (hl:(9/(8*Real.pi))*r^2/(1+Real.sqrt (1-(4/3:ℝ)*r^2))≤loss x) : small r < p x := by
  by_contra hn
  have hP : p x ≤ small (22/125:ℝ) := (le_of_not_gt hn).trans (small_mono (by change 0≤r; linarith only [hr.1]) (by norm_num) hr.2)
  have hj : 0≤J 12 (17477/12500:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hj' : 0≤J 13 (17477/12500:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hpL : small (22/125:ℝ) ≤ p (17477/12500:ℝ) := by
    apply le_trans ?_ (p_taylor_lower (by norm_num) 6 hj)
    norm_num [small,J,Finset.sum_range_succ,Nat.factorial]
  have hpU : p (17477/12500:ℝ)≤(16207/200000:ℝ) := by
    apply le_trans (p_taylor_upper (by norm_num) 6 hj')
    norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hla : lambda (17477/12500:ℝ)≤(1852559/1000000:ℝ) := by
    apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj
    norm_num [E,J,Finset.sum_range_succ,Nat.factorial]
  have hg : G (17477/12500:ℝ)≤(841801/1000000:ℝ) := G_upper_of_lambda (by norm_num) hla (by norm_num)
  exact loss_row (lo:=(7/40:ℝ)) (q:=(17477/12500:ℝ)) (v:=(979371/1000000:ℝ))
    (u:=(16207/200000:ℝ)^2*(841801/1000000:ℝ)) (by norm_num) hr.1 hx (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (loss_bound (by norm_num) hpU hg) (hP.trans hpL) hl

lemma small_20 {r x:ℝ} (hr:r∈Icc (22/125:ℝ) (177/1000:ℝ)) (hx:0≤x)
    (hl:(9/(8*Real.pi))*r^2/(1+Real.sqrt (1-(4/3:ℝ)*r^2))≤loss x) : small r < p x := by
  by_contra hn
  have hP : p x ≤ small (177/1000:ℝ) := (le_of_not_gt hn).trans (small_mono (by change 0≤r; linarith only [hr.1]) (by norm_num) hr.2)
  have hj : 0≤J 12 (34873/25000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hj' : 0≤J 13 (34873/25000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hpL : small (177/1000:ℝ) ≤ p (34873/25000:ℝ) := by
    apply le_trans ?_ (p_taylor_lower (by norm_num) 6 hj)
    norm_num [small,J,Finset.sum_range_succ,Nat.factorial]
  have hpU : p (34873/25000:ℝ)≤(40761/500000:ℝ) := by
    apply le_trans (p_taylor_upper (by norm_num) 6 hj')
    norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hla : lambda (34873/25000:ℝ)≤(231229/125000:ℝ) := by
    apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj
    norm_num [E,J,Finset.sum_range_succ,Nat.factorial]
  have hg : G (34873/25000:ℝ)≤(841511/1000000:ℝ) := G_upper_of_lambda (by norm_num) hla (by norm_num)
  exact loss_row (lo:=(22/125:ℝ)) (q:=(34873/25000:ℝ)) (v:=(244783/250000:ℝ))
    (u:=(40761/500000:ℝ)^2*(841511/1000000:ℝ)) (by norm_num) hr.1 hx (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (loss_bound (by norm_num) hpU hg) (hP.trans hpL) hl

lemma small_21 {r x:ℝ} (hr:r∈Icc (177/1000:ℝ) (89/500:ℝ)) (hx:0≤x)
    (hl:(9/(8*Real.pi))*r^2/(1+Real.sqrt (1-(4/3:ℝ)*r^2))≤loss x) : small r < p x := by
  by_contra hn
  have hP : p x ≤ small (89/500:ℝ) := (le_of_not_gt hn).trans (small_mono (by change 0≤r; linarith only [hr.1]) (by norm_num) hr.2)
  have hj : 0≤J 12 (13917/10000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hj' : 0≤J 13 (13917/10000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hpL : small (89/500:ℝ) ≤ p (13917/10000:ℝ) := by
    apply le_trans ?_ (p_taylor_lower (by norm_num) 6 hj)
    norm_num [small,J,Finset.sum_range_succ,Nat.factorial]
  have hpU : p (13917/10000:ℝ)≤(82009/1000000:ℝ) := by
    apply le_trans (p_taylor_upper (by norm_num) 6 hj')
    norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hla : lambda (13917/10000:ℝ)≤(1847123/1000000:ℝ) := by
    apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj
    norm_num [E,J,Finset.sum_range_succ,Nat.factorial]
  have hg : G (13917/10000:ℝ)≤(841223/1000000:ℝ) := G_upper_of_lambda (by norm_num) hla (by norm_num)
  exact loss_row (lo:=(177/1000:ℝ)) (q:=(13917/10000:ℝ)) (v:=(244723/250000:ℝ))
    (u:=(82009/1000000:ℝ)^2*(841223/1000000:ℝ)) (by norm_num) hr.1 hx (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (loss_bound (by norm_num) hpU hg) (hP.trans hpL) hl

lemma small_22 {r x:ℝ} (hr:r∈Icc (89/500:ℝ) (179/1000:ℝ)) (hx:0≤x)
    (hl:(9/(8*Real.pi))*r^2/(1+Real.sqrt (1-(4/3:ℝ)*r^2))≤loss x) : small r < p x := by
  by_contra hn
  have hP : p x ≤ small (179/1000:ℝ) := (le_of_not_gt hn).trans (small_mono (by change 0≤r; linarith only [hr.1]) (by norm_num) hr.2)
  have hj : 0≤J 12 (138849/100000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hj' : 0≤J 13 (138849/100000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hpL : small (179/1000:ℝ) ≤ p (138849/100000:ℝ) := by
    apply le_trans ?_ (p_taylor_lower (by norm_num) 6 hj)
    norm_num [small,J,Finset.sum_range_succ,Nat.factorial]
  have hpU : p (138849/100000:ℝ)≤(1289/15625:ℝ) := by
    apply le_trans (p_taylor_upper (by norm_num) 6 hj')
    norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hla : lambda (138849/100000:ℝ)≤(230553/125000:ℝ) := by
    apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj
    norm_num [E,J,Finset.sum_range_succ,Nat.factorial]
  have hg : G (138849/100000:ℝ)≤(105117/125000:ℝ) := G_upper_of_lambda (by norm_num) hla (by norm_num)
  exact loss_row (lo:=(89/500:ℝ)) (q:=(138849/100000:ℝ)) (v:=(19573/20000:ℝ))
    (u:=(1289/15625:ℝ)^2*(105117/125000:ℝ)) (by norm_num) hr.1 hx (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (loss_bound (by norm_num) hpU hg) (hP.trans hpL) hl

lemma small_23 {r x:ℝ} (hr:r∈Icc (179/1000:ℝ) (9/50:ℝ)) (hx:0≤x)
    (hl:(9/(8*Real.pi))*r^2/(1+Real.sqrt (1-(4/3:ℝ)*r^2))≤loss x) : small r < p x := by
  by_contra hn
  have hP : p x ≤ small (9/50:ℝ) := (le_of_not_gt hn).trans (small_mono (by change 0≤r; linarith only [hr.1]) (by norm_num) hr.2)
  have hj : 0≤J 12 (138529/100000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hj' : 0≤J 13 (138529/100000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hpL : small (9/50:ℝ) ≤ p (138529/100000:ℝ) := by
    apply le_trans ?_ (p_taylor_lower (by norm_num) 6 hj)
    norm_num [small,J,Finset.sum_range_succ,Nat.factorial]
  have hpU : p (138529/100000:ℝ)≤(10373/125000:ℝ) := by
    apply le_trans (p_taylor_upper (by norm_num) 6 hj')
    norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hla : lambda (138529/100000:ℝ)≤(920867/500000:ℝ) := by
    apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj
    norm_num [E,J,Finset.sum_range_succ,Nat.factorial]
  have hg : G (138529/100000:ℝ)≤(840649/1000000:ℝ) := G_upper_of_lambda (by norm_num) hla (by norm_num)
  exact loss_row (lo:=(179/1000:ℝ)) (q:=(138529/100000:ℝ)) (v:=(978407/1000000:ℝ))
    (u:=(10373/125000:ℝ)^2*(840649/1000000:ℝ)) (by norm_num) hr.1 hx (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (loss_bound (by norm_num) hpU hg) (hP.trans hpL) hl

lemma small_of_loss_oai {r x:ℝ} (hr:r∈Icc (39/250:ℝ) (9/50:ℝ)) (hx:0≤x)
    (hl:(9/(8*Real.pi))*r^2/(1+Real.sqrt (1-(4/3:ℝ)*r^2))≤loss x) : small r < p x := by
  by_cases h0 : r≤(157/1000:ℝ)
  · exact small_0 ⟨by linarith only [hr.1],h0⟩ hx hl
  by_cases h1 : r≤(79/500:ℝ)
  · exact small_1 ⟨by linarith only [h0],h1⟩ hx hl
  by_cases h2 : r≤(159/1000:ℝ)
  · exact small_2 ⟨by linarith only [h1],h2⟩ hx hl
  by_cases h3 : r≤(4/25:ℝ)
  · exact small_3 ⟨by linarith only [h2],h3⟩ hx hl
  by_cases h4 : r≤(161/1000:ℝ)
  · exact small_4 ⟨by linarith only [h3],h4⟩ hx hl
  by_cases h5 : r≤(81/500:ℝ)
  · exact small_5 ⟨by linarith only [h4],h5⟩ hx hl
  by_cases h6 : r≤(163/1000:ℝ)
  · exact small_6 ⟨by linarith only [h5],h6⟩ hx hl
  by_cases h7 : r≤(41/250:ℝ)
  · exact small_7 ⟨by linarith only [h6],h7⟩ hx hl
  by_cases h8 : r≤(33/200:ℝ)
  · exact small_8 ⟨by linarith only [h7],h8⟩ hx hl
  by_cases h9 : r≤(83/500:ℝ)
  · exact small_9 ⟨by linarith only [h8],h9⟩ hx hl
  by_cases h10 : r≤(167/1000:ℝ)
  · exact small_10 ⟨by linarith only [h9],h10⟩ hx hl
  by_cases h11 : r≤(21/125:ℝ)
  · exact small_11 ⟨by linarith only [h10],h11⟩ hx hl
  by_cases h12 : r≤(169/1000:ℝ)
  · exact small_12 ⟨by linarith only [h11],h12⟩ hx hl
  by_cases h13 : r≤(17/100:ℝ)
  · exact small_13 ⟨by linarith only [h12],h13⟩ hx hl
  by_cases h14 : r≤(171/1000:ℝ)
  · exact small_14 ⟨by linarith only [h13],h14⟩ hx hl
  by_cases h15 : r≤(43/250:ℝ)
  · exact small_15 ⟨by linarith only [h14],h15⟩ hx hl
  by_cases h16 : r≤(173/1000:ℝ)
  · exact small_16 ⟨by linarith only [h15],h16⟩ hx hl
  by_cases h17 : r≤(87/500:ℝ)
  · exact small_17 ⟨by linarith only [h16],h17⟩ hx hl
  by_cases h18 : r≤(7/40:ℝ)
  · exact small_18 ⟨by linarith only [h17],h18⟩ hx hl
  by_cases h19 : r≤(22/125:ℝ)
  · exact small_19 ⟨by linarith only [h18],h19⟩ hx hl
  by_cases h20 : r≤(177/1000:ℝ)
  · exact small_20 ⟨by linarith only [h19],h20⟩ hx hl
  by_cases h21 : r≤(89/500:ℝ)
  · exact small_21 ⟨by linarith only [h20],h21⟩ hx hl
  by_cases h22 : r≤(179/1000:ℝ)
  · exact small_22 ⟨by linarith only [h21],h22⟩ hx hl
  exact small_23 ⟨by linarith only [h22],hr.2⟩ hx hl

end GaussianPropeller.FourCertificates

end OAI
end

theorem solution : type_of% @OAI.GaussianPropeller.FourCertificates.small_of_loss_oai := @OAI.GaussianPropeller.FourCertificates.small_of_loss_oai
