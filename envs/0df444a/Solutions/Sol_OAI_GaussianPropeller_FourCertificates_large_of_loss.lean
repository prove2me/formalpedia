-- Prove2me | solution 1 for OAI.GaussianPropeller.FourCertificates.large_of_loss
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-19T00:19:39.123468+00:00
-- url     : https://prove2.me/submissions/6c817955-d8c5-4fb3-b2f9-7a69788c4728

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

lemma large_mono : MonotoneOn large (Ici 0) := by
  intro a ha b hb hab
  have h2:=pow_le_pow_left₀ ha hab 2
  unfold large; linarith only [h2]

end GaussianPropeller.FourCertificates

end OAI
end

section
-- module Solutions.OAIQW_GaussianPropeller.LargeCertificates
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

lemma large_0 {r x:ℝ} (hr:r∈Icc (2/5:ℝ) (161/400:ℝ)) (hx:0≤x)
    (hl:(9/(8*Real.pi))*r^2/(1+Real.sqrt (1-(4/3:ℝ)*r^2))≤loss x) : large r < p x := by
  by_contra hn
  have hP : p x ≤ large (161/400:ℝ) := (le_of_not_gt hn).trans (large_mono (by change 0≤r; linarith only [hr.1]) (by norm_num) hr.2)
  have hj : 0≤J 12 (1717/2000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hj' : 0≤J 13 (1717/2000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hpL : large (161/400:ℝ) ≤ p (1717/2000:ℝ) := by
    apply le_trans ?_ (p_taylor_lower (by norm_num) 6 hj)
    norm_num [large,J,Finset.sum_range_succ,Nat.factorial]
  have hpU : p (1717/2000:ℝ)≤(195311/1000000:ℝ) := by
    apply le_trans (p_taylor_upper (by norm_num) 6 hj')
    norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hla : lambda (1717/2000:ℝ)≤(1413067/1000000:ℝ) := by
    apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj
    norm_num [E,J,Finset.sum_range_succ,Nat.factorial]
  have hg : G (1717/2000:ℝ)≤(783641/1000000:ℝ) := G_upper_of_lambda (by norm_num) hla (by norm_num)
  exact loss_row (lo:=(2/5:ℝ)) (q:=(1717/2000:ℝ)) (v:=(886943/1000000:ℝ))
    (u:=(195311/1000000:ℝ)^2*(783641/1000000:ℝ)) (by norm_num) hr.1 hx (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (loss_bound (by norm_num) hpU hg) (hP.trans hpL) hl

lemma large_1 {r x:ℝ} (hr:r∈Icc (161/400:ℝ) (81/200:ℝ)) (hx:0≤x)
    (hl:(9/(8*Real.pi))*r^2/(1+Real.sqrt (1-(4/3:ℝ)*r^2))≤loss x) : large r < p x := by
  by_contra hn
  have hP : p x ≤ large (81/200:ℝ) := (le_of_not_gt hn).trans (large_mono (by change 0≤r; linarith only [hr.1]) (by norm_num) hr.2)
  have hj : 0≤J 12 (683/800:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hj' : 0≤J 13 (683/800:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hpL : large (81/200:ℝ) ≤ p (683/800:ℝ) := by
    apply le_trans ?_ (p_taylor_lower (by norm_num) 6 hj)
    norm_num [large,J,Finset.sum_range_succ,Nat.factorial]
  have hpU : p (683/800:ℝ)≤(12289/62500:ℝ) := by
    apply le_trans (p_taylor_upper (by norm_num) 6 hj')
    norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hla : lambda (683/800:ℝ)≤(1409347/1000000:ℝ) := by
    apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj
    norm_num [E,J,Finset.sum_range_succ,Nat.factorial]
  have hg : G (683/800:ℝ)≤(783029/1000000:ℝ) := G_upper_of_lambda (by norm_num) hla (by norm_num)
  exact loss_row (lo:=(161/400:ℝ)) (q:=(683/800:ℝ)) (v:=(442717/500000:ℝ))
    (u:=(12289/62500:ℝ)^2*(783029/1000000:ℝ)) (by norm_num) hr.1 hx (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (loss_bound (by norm_num) hpU hg) (hP.trans hpL) hl

lemma large_2 {r x:ℝ} (hr:r∈Icc (81/200:ℝ) (163/400:ℝ)) (hx:0≤x)
    (hl:(9/(8*Real.pi))*r^2/(1+Real.sqrt (1-(4/3:ℝ)*r^2))≤loss x) : large r < p x := by
  by_contra hn
  have hP : p x ≤ large (163/400:ℝ) := (le_of_not_gt hn).trans (large_mono (by change 0≤r; linarith only [hr.1]) (by norm_num) hr.2)
  have hj : 0≤J 12 (849/1000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hj' : 0≤J 13 (849/1000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hpL : large (163/400:ℝ) ≤ p (849/1000:ℝ) := by
    apply le_trans ?_ (p_taylor_lower (by norm_num) 6 hj)
    norm_num [large,J,Finset.sum_range_succ,Nat.factorial]
  have hpU : p (849/1000:ℝ)≤(197943/1000000:ℝ) := by
    apply le_trans (p_taylor_upper (by norm_num) 6 hj')
    norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hla : lambda (849/1000:ℝ)≤(1405629/1000000:ℝ) := by
    apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj
    norm_num [E,J,Finset.sum_range_succ,Nat.factorial]
  have hg : G (849/1000:ℝ)≤(391207/500000:ℝ) := G_upper_of_lambda (by norm_num) hla (by norm_num)
  exact loss_row (lo:=(81/200:ℝ)) (q:=(849/1000:ℝ)) (v:=(110489/125000:ℝ))
    (u:=(197943/1000000:ℝ)^2*(391207/500000:ℝ)) (by norm_num) hr.1 hx (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (loss_bound (by norm_num) hpU hg) (hP.trans hpL) hl

lemma large_3 {r x:ℝ} (hr:r∈Icc (163/400:ℝ) (41/100:ℝ)) (hx:0≤x)
    (hl:(9/(8*Real.pi))*r^2/(1+Real.sqrt (1-(4/3:ℝ)*r^2))≤loss x) : large r < p x := by
  by_contra hn
  have hP : p x ≤ large (41/100:ℝ) := (le_of_not_gt hn).trans (large_mono (by change 0≤r; linarith only [hr.1]) (by norm_num) hr.2)
  have hj : 0≤J 12 (84423/100000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hj' : 0≤J 13 (84423/100000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hpL : large (41/100:ℝ) ≤ p (84423/100000:ℝ) := by
    apply le_trans ?_ (p_taylor_lower (by norm_num) 6 hj)
    norm_num [large,J,Finset.sum_range_succ,Nat.factorial]
  have hpU : p (84423/100000:ℝ)≤(199273/1000000:ℝ) := by
    apply le_trans (p_taylor_upper (by norm_num) 6 hj')
    norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hla : lambda (84423/100000:ℝ)≤(1401899/1000000:ℝ) := by
    apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj
    norm_num [E,J,Finset.sum_range_succ,Nat.factorial]
  have hg : G (84423/100000:ℝ)≤(195449/250000:ℝ) := G_upper_of_lambda (by norm_num) hla (by norm_num)
  exact loss_row (lo:=(163/400:ℝ)) (q:=(84423/100000:ℝ)) (v:=(882379/1000000:ℝ))
    (u:=(199273/1000000:ℝ)^2*(195449/250000:ℝ)) (by norm_num) hr.1 hx (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (loss_bound (by norm_num) hpU hg) (hP.trans hpL) hl

lemma large_4 {r x:ℝ} (hr:r∈Icc (41/100:ℝ) (33/80:ℝ)) (hx:0≤x)
    (hl:(9/(8*Real.pi))*r^2/(1+Real.sqrt (1-(4/3:ℝ)*r^2))≤loss x) : large r < p x := by
  by_contra hn
  have hP : p x ≤ large (33/80:ℝ) := (le_of_not_gt hn).trans (large_mono (by change 0≤r; linarith only [hr.1]) (by norm_num) hr.2)
  have hj : 0≤J 12 (41973/50000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hj' : 0≤J 13 (41973/50000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hpL : large (33/80:ℝ) ≤ p (41973/50000:ℝ) := by
    apply le_trans ?_ (p_taylor_lower (by norm_num) 6 hj)
    norm_num [large,J,Finset.sum_range_succ,Nat.factorial]
  have hpU : p (41973/50000:ℝ)≤(6269/31250:ℝ) := by
    apply le_trans (p_taylor_upper (by norm_num) 6 hj')
    norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hla : lambda (41973/50000:ℝ)≤(349543/250000:ℝ) := by
    apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj
    norm_num [E,J,Finset.sum_range_succ,Nat.factorial]
  have hg : G (41973/50000:ℝ)≤(97647/125000:ℝ) := G_upper_of_lambda (by norm_num) hla (by norm_num)
  exact loss_row (lo:=(41/100:ℝ)) (q:=(41973/50000:ℝ)) (v:=(880833/1000000:ℝ))
    (u:=(6269/31250:ℝ)^2*(97647/125000:ℝ)) (by norm_num) hr.1 hx (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (loss_bound (by norm_num) hpU hg) (hP.trans hpL) hl

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

lemma large_6 {r x:ℝ} (hr:r∈Icc (83/200:ℝ) (167/400:ℝ)) (hx:0≤x)
    (hl:(9/(8*Real.pi))*r^2/(1+Real.sqrt (1-(4/3:ℝ)*r^2))≤loss x) : large r < p x := by
  by_contra hn
  have hP : p x ≤ large (167/400:ℝ) := (le_of_not_gt hn).trans (large_mono (by change 0≤r; linarith only [hr.1]) (by norm_num) hr.2)
  have hj : 0≤J 12 (20747/25000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hj' : 0≤J 13 (20747/25000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hpL : large (167/400:ℝ) ≤ p (20747/25000:ℝ) := by
    apply le_trans ?_ (p_taylor_lower (by norm_num) 6 hj)
    norm_num [large,J,Finset.sum_range_succ,Nat.factorial]
  have hpU : p (20747/25000:ℝ)≤(101653/500000:ℝ) := by
    apply le_trans (p_taylor_upper (by norm_num) 6 hj')
    norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hla : lambda (20747/25000:ℝ)≤(278139/200000:ℝ) := by
    apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj
    norm_num [E,J,Finset.sum_range_succ,Nat.factorial]
  have hg : G (20747/25000:ℝ)≤(779923/1000000:ℝ) := G_upper_of_lambda (by norm_num) hla (by norm_num)
  exact loss_row (lo:=(83/200:ℝ)) (q:=(20747/25000:ℝ)) (v:=(438853/500000:ℝ))
    (u:=(101653/500000:ℝ)^2*(779923/1000000:ℝ)) (by norm_num) hr.1 hx (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (loss_bound (by norm_num) hpU hg) (hP.trans hpL) hl

lemma large_7 {r x:ℝ} (hr:r∈Icc (167/400:ℝ) (21/50:ℝ)) (hx:0≤x)
    (hl:(9/(8*Real.pi))*r^2/(1+Real.sqrt (1-(4/3:ℝ)*r^2))≤loss x) : large r < p x := by
  by_contra hn
  have hP : p x ≤ large (21/50:ℝ) := (le_of_not_gt hn).trans (large_mono (by change 0≤r; linarith only [hr.1]) (by norm_num) hr.2)
  have hj : 0≤J 12 (20627/25000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hj' : 0≤J 13 (20627/25000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hpL : large (21/50:ℝ) ≤ p (20627/25000:ℝ) := by
    apply le_trans ?_ (p_taylor_lower (by norm_num) 6 hj)
    norm_num [large,J,Finset.sum_range_succ,Nat.factorial]
  have hpU : p (20627/25000:ℝ)≤(102333/500000:ℝ) := by
    apply le_trans (p_taylor_upper (by norm_num) 6 hj')
    norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hla : lambda (20627/25000:ℝ)≤(1386953/1000000:ℝ) := by
    apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj
    norm_num [E,J,Finset.sum_range_succ,Nat.factorial]
  have hg : G (20627/25000:ℝ)≤(194823/250000:ℝ) := G_upper_of_lambda (by norm_num) hla (by norm_num)
  exact loss_row (lo:=(167/400:ℝ)) (q:=(20627/25000:ℝ)) (v:=(219031/250000:ℝ))
    (u:=(102333/500000:ℝ)^2*(194823/250000:ℝ)) (by norm_num) hr.1 hx (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (loss_bound (by norm_num) hpU hg) (hP.trans hpL) hl

lemma large_8 {r x:ℝ} (hr:r∈Icc (21/50:ℝ) (169/400:ℝ)) (hx:0≤x)
    (hl:(9/(8*Real.pi))*r^2/(1+Real.sqrt (1-(4/3:ℝ)*r^2))≤loss x) : large r < p x := by
  by_contra hn
  have hP : p x ≤ large (169/400:ℝ) := (le_of_not_gt hn).trans (large_mono (by change 0≤r; linarith only [hr.1]) (by norm_num) hr.2)
  have hj : 0≤J 12 (41013/50000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hj' : 0≤J 13 (41013/50000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hpL : large (169/400:ℝ) ≤ p (41013/50000:ℝ) := by
    apply le_trans ?_ (p_taylor_lower (by norm_num) 6 hj)
    norm_num [large,J,Finset.sum_range_succ,Nat.factorial]
  have hpU : p (41013/50000:ℝ)≤(51509/250000:ℝ) := by
    apply le_trans (p_taylor_upper (by norm_num) 6 hj')
    norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hla : lambda (41013/50000:ℝ)≤(1383199/1000000:ℝ) := by
    apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj
    norm_num [E,J,Finset.sum_range_succ,Nat.factorial]
  have hg : G (41013/50000:ℝ)≤(778657/1000000:ℝ) := G_upper_of_lambda (by norm_num) hla (by norm_num)
  exact loss_row (lo:=(21/50:ℝ)) (q:=(41013/50000:ℝ)) (v:=(874529/1000000:ℝ))
    (u:=(51509/250000:ℝ)^2*(778657/1000000:ℝ)) (by norm_num) hr.1 hx (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (loss_bound (by norm_num) hpU hg) (hP.trans hpL) hl

lemma large_9 {r x:ℝ} (hr:r∈Icc (169/400:ℝ) (17/40:ℝ)) (hx:0≤x)
    (hl:(9/(8*Real.pi))*r^2/(1+Real.sqrt (1-(4/3:ℝ)*r^2))≤loss x) : large r < p x := by
  by_contra hn
  have hP : p x ≤ large (17/40:ℝ) := (le_of_not_gt hn).trans (large_mono (by change 0≤r; linarith only [hr.1]) (by norm_num) hr.2)
  have hj : 0≤J 12 (10193/12500:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hj' : 0≤J 13 (10193/12500:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hpL : large (17/40:ℝ) ≤ p (10193/12500:ℝ) := by
    apply le_trans ?_ (p_taylor_lower (by norm_num) 6 hj)
    norm_num [large,J,Finset.sum_range_succ,Nat.factorial]
  have hpU : p (10193/12500:ℝ)≤(207413/1000000:ℝ) := by
    apply le_trans (p_taylor_upper (by norm_num) 6 hj')
    norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hla : lambda (10193/12500:ℝ)≤(172431/125000:ℝ) := by
    apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj
    norm_num [E,J,Finset.sum_range_succ,Nat.factorial]
  have hg : G (10193/12500:ℝ)≤(38901/50000:ℝ) := G_upper_of_lambda (by norm_num) hla (by norm_num)
  exact loss_row (lo:=(169/400:ℝ)) (q:=(10193/12500:ℝ)) (v:=(436461/500000:ℝ))
    (u:=(207413/1000000:ℝ)^2*(38901/50000:ℝ)) (by norm_num) hr.1 hx (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (loss_bound (by norm_num) hpU hg) (hP.trans hpL) hl

lemma large_10 {r x:ℝ} (hr:r∈Icc (17/40:ℝ) (171/400:ℝ)) (hx:0≤x)
    (hl:(9/(8*Real.pi))*r^2/(1+Real.sqrt (1-(4/3:ℝ)*r^2))≤loss x) : large r < p x := by
  by_contra hn
  have hP : p x ≤ large (171/400:ℝ) := (le_of_not_gt hn).trans (large_mono (by change 0≤r; linarith only [hr.1]) (by norm_num) hr.2)
  have hj : 0≤J 12 (81061/100000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hj' : 0≤J 13 (81061/100000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hpL : large (171/400:ℝ) ≤ p (81061/100000:ℝ) := by
    apply le_trans ?_ (p_taylor_lower (by norm_num) 6 hj)
    norm_num [large,J,Finset.sum_range_succ,Nat.factorial]
  have hpU : p (81061/100000:ℝ)≤(208797/1000000:ℝ) := by
    apply le_trans (p_taylor_upper (by norm_num) 6 hj')
    norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hla : lambda (81061/100000:ℝ)≤(343923/250000:ℝ) := by
    apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj
    norm_num [E,J,Finset.sum_range_succ,Nat.factorial]
  have hg : G (81061/100000:ℝ)≤(777379/1000000:ℝ) := G_upper_of_lambda (by norm_num) hla (by norm_num)
  exact loss_row (lo:=(17/40:ℝ)) (q:=(81061/100000:ℝ)) (v:=(435651/500000:ℝ))
    (u:=(208797/1000000:ℝ)^2*(777379/1000000:ℝ)) (by norm_num) hr.1 hx (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (loss_bound (by norm_num) hpU hg) (hP.trans hpL) hl

lemma large_11 {r x:ℝ} (hr:r∈Icc (171/400:ℝ) (43/100:ℝ)) (hx:0≤x)
    (hl:(9/(8*Real.pi))*r^2/(1+Real.sqrt (1-(4/3:ℝ)*r^2))≤loss x) : large r < p x := by
  by_contra hn
  have hP : p x ≤ large (43/100:ℝ) := (le_of_not_gt hn).trans (large_mono (by change 0≤r; linarith only [hr.1]) (by norm_num) hr.2)
  have hj : 0≤J 12 (2518/3125:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hj' : 0≤J 13 (2518/3125:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hpL : large (43/100:ℝ) ≤ p (2518/3125:ℝ) := by
    apply le_trans ?_ (p_taylor_lower (by norm_num) 6 hj)
    norm_num [large,J,Finset.sum_range_succ,Nat.factorial]
  have hpU : p (2518/3125:ℝ)≤(210193/1000000:ℝ) := by
    apply le_trans (p_taylor_upper (by norm_num) 6 hj')
    norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hla : lambda (2518/3125:ℝ)≤(342981/250000:ℝ) := by
    apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj
    norm_num [E,J,Finset.sum_range_succ,Nat.factorial]
  have hg : G (2518/3125:ℝ)≤(388367/500000:ℝ) := G_upper_of_lambda (by norm_num) hla (by norm_num)
  exact loss_row (lo:=(171/400:ℝ)) (q:=(2518/3125:ℝ)) (v:=(86967/100000:ℝ))
    (u:=(210193/1000000:ℝ)^2*(388367/500000:ℝ)) (by norm_num) hr.1 hx (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (loss_bound (by norm_num) hpU hg) (hP.trans hpL) hl

lemma large_12 {r x:ℝ} (hr:r∈Icc (43/100:ℝ) (173/400:ℝ)) (hx:0≤x)
    (hl:(9/(8*Real.pi))*r^2/(1+Real.sqrt (1-(4/3:ℝ)*r^2))≤loss x) : large r < p x := by
  by_contra hn
  have hP : p x ≤ large (173/400:ℝ) := (le_of_not_gt hn).trans (large_mono (by change 0≤r; linarith only [hr.1]) (by norm_num) hr.2)
  have hj : 0≤J 12 (80091/100000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hj' : 0≤J 13 (80091/100000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hpL : large (173/400:ℝ) ≤ p (80091/100000:ℝ) := by
    apply le_trans ?_ (p_taylor_lower (by norm_num) 6 hj)
    norm_num [large,J,Finset.sum_range_succ,Nat.factorial]
  have hpU : p (80091/100000:ℝ)≤(105797/500000:ℝ) := by
    apply le_trans (p_taylor_upper (by norm_num) 6 hj')
    norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hla : lambda (80091/100000:ℝ)≤(1368159/1000000:ℝ) := by
    apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj
    norm_num [E,J,Finset.sum_range_succ,Nat.factorial]
  have hg : G (80091/100000:ℝ)≤(776087/1000000:ℝ) := G_upper_of_lambda (by norm_num) hla (by norm_num)
  exact loss_row (lo:=(43/100:ℝ)) (q:=(80091/100000:ℝ)) (v:=(34721/40000:ℝ))
    (u:=(105797/500000:ℝ)^2*(776087/1000000:ℝ)) (by norm_num) hr.1 hx (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (loss_bound (by norm_num) hpU hg) (hP.trans hpL) hl

lemma large_13 {r x:ℝ} (hr:r∈Icc (173/400:ℝ) (87/200:ℝ)) (hx:0≤x)
    (hl:(9/(8*Real.pi))*r^2/(1+Real.sqrt (1-(4/3:ℝ)*r^2))≤loss x) : large r < p x := by
  by_contra hn
  have hP : p x ≤ large (87/200:ℝ) := (le_of_not_gt hn).trans (large_mono (by change 0≤r; linarith only [hr.1]) (by norm_num) hr.2)
  have hj : 0≤J 12 (15921/20000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hj' : 0≤J 13 (15921/20000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hpL : large (87/200:ℝ) ≤ p (15921/20000:ℝ) := by
    apply le_trans ?_ (p_taylor_lower (by norm_num) 6 hj)
    norm_num [large,J,Finset.sum_range_succ,Nat.factorial]
  have hpU : p (15921/20000:ℝ)≤(53251/250000:ℝ) := by
    apply le_trans (p_taylor_upper (by norm_num) 6 hj')
    norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hla : lambda (15921/20000:ℝ)≤(1364389/1000000:ℝ) := by
    apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj
    norm_num [E,J,Finset.sum_range_succ,Nat.factorial]
  have hg : G (15921/20000:ℝ)≤(193859/250000:ℝ) := G_upper_of_lambda (by norm_num) hla (by norm_num)
  exact loss_row (lo:=(173/400:ℝ)) (q:=(15921/20000:ℝ)) (v:=(866367/1000000:ℝ))
    (u:=(53251/250000:ℝ)^2*(193859/250000:ℝ)) (by norm_num) hr.1 hx (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (loss_bound (by norm_num) hpU hg) (hP.trans hpL) hl

lemma large_14 {r x:ℝ} (hr:r∈Icc (87/200:ℝ) (7/16:ℝ)) (hx:0≤x)
    (hl:(9/(8*Real.pi))*r^2/(1+Real.sqrt (1-(4/3:ℝ)*r^2))≤loss x) : large r < p x := by
  by_contra hn
  have hP : p x ≤ large (7/16:ℝ) := (le_of_not_gt hn).trans (large_mono (by change 0≤r; linarith only [hr.1]) (by norm_num) hr.2)
  have hj : 0≤J 12 (39559/50000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hj' : 0≤J 13 (39559/50000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hpL : large (7/16:ℝ) ≤ p (39559/50000:ℝ) := by
    apply le_trans ?_ (p_taylor_lower (by norm_num) 6 hj)
    norm_num [large,J,Finset.sum_range_succ,Nat.factorial]
  have hpU : p (39559/50000:ℝ)≤(107211/500000:ℝ) := by
    apply le_trans (p_taylor_upper (by norm_num) 6 hj')
    norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hla : lambda (39559/50000:ℝ)≤(272123/200000:ℝ) := by
    apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj
    norm_num [E,J,Finset.sum_range_succ,Nat.factorial]
  have hg : G (39559/50000:ℝ)≤(387391/500000:ℝ) := G_upper_of_lambda (by norm_num) hla (by norm_num)
  exact loss_row (lo:=(87/200:ℝ)) (q:=(39559/50000:ℝ)) (v:=(864697/1000000:ℝ))
    (u:=(107211/500000:ℝ)^2*(387391/500000:ℝ)) (by norm_num) hr.1 hx (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (loss_bound (by norm_num) hpU hg) (hP.trans hpL) hl

lemma large_15 {r x:ℝ} (hr:r∈Icc (7/16:ℝ) (11/25:ℝ)) (hx:0≤x)
    (hl:(9/(8*Real.pi))*r^2/(1+Real.sqrt (1-(4/3:ℝ)*r^2))≤loss x) : large r < p x := by
  by_contra hn
  have hP : p x ≤ large (11/25:ℝ) := (le_of_not_gt hn).trans (large_mono (by change 0≤r; linarith only [hr.1]) (by norm_num) hr.2)
  have hj : 0≤J 12 (78631/100000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hj' : 0≤J 13 (78631/100000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hpL : large (11/25:ℝ) ≤ p (78631/100000:ℝ) := by
    apply le_trans ?_ (p_taylor_lower (by norm_num) 6 hj)
    norm_num [large,J,Finset.sum_range_succ,Nat.factorial]
  have hpU : p (78631/100000:ℝ)≤(43169/200000:ℝ) := by
    apply le_trans (p_taylor_upper (by norm_num) 6 hj')
    norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hla : lambda (78631/100000:ℝ)≤(339211/250000:ℝ) := by
    apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj
    norm_num [E,J,Finset.sum_range_succ,Nat.factorial]
  have hg : G (78631/100000:ℝ)≤(387063/500000:ℝ) := G_upper_of_lambda (by norm_num) hla (by norm_num)
  exact loss_row (lo:=(7/16:ℝ)) (q:=(78631/100000:ℝ)) (v:=(431507/500000:ℝ))
    (u:=(43169/200000:ℝ)^2*(387063/500000:ℝ)) (by norm_num) hr.1 hx (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (loss_bound (by norm_num) hpU hg) (hP.trans hpL) hl

lemma large_16 {r x:ℝ} (hr:r∈Icc (11/25:ℝ) (177/400:ℝ)) (hx:0≤x)
    (hl:(9/(8*Real.pi))*r^2/(1+Real.sqrt (1-(4/3:ℝ)*r^2))≤loss x) : large r < p x := by
  by_contra hn
  have hP : p x ≤ large (177/400:ℝ) := (le_of_not_gt hn).trans (large_mono (by change 0≤r; linarith only [hr.1]) (by norm_num) hr.2)
  have hj : 0≤J 12 (39071/50000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hj' : 0≤J 13 (39071/50000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hpL : large (177/400:ℝ) ≤ p (39071/50000:ℝ) := by
    apply le_trans ?_ (p_taylor_lower (by norm_num) 6 hj)
    norm_num [large,J,Finset.sum_range_succ,Nat.factorial]
  have hpU : p (39071/50000:ℝ)≤(679/3125:ℝ) := by
    apply le_trans (p_taylor_upper (by norm_num) 6 hj')
    norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hla : lambda (39071/50000:ℝ)≤(67653/50000:ℝ) := by
    apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj
    norm_num [E,J,Finset.sum_range_succ,Nat.factorial]
  have hg : G (39071/50000:ℝ)≤(96683/125000:ℝ) := G_upper_of_lambda (by norm_num) hla (by norm_num)
  exact loss_row (lo:=(11/25:ℝ)) (q:=(39071/50000:ℝ)) (v:=(861317/1000000:ℝ))
    (u:=(679/3125:ℝ)^2*(96683/125000:ℝ)) (by norm_num) hr.1 hx (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (loss_bound (by norm_num) hpU hg) (hP.trans hpL) hl

lemma large_17 {r x:ℝ} (hr:r∈Icc (177/400:ℝ) (89/200:ℝ)) (hx:0≤x)
    (hl:(9/(8*Real.pi))*r^2/(1+Real.sqrt (1-(4/3:ℝ)*r^2))≤loss x) : large r < p x := by
  by_contra hn
  have hP : p x ≤ large (89/200:ℝ) := (le_of_not_gt hn).trans (large_mono (by change 0≤r; linarith only [hr.1]) (by norm_num) hr.2)
  have hj : 0≤J 12 (19413/25000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hj' : 0≤J 13 (19413/25000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hpL : large (89/200:ℝ) ≤ p (19413/25000:ℝ) := by
    apply le_trans ?_ (p_taylor_lower (by norm_num) 6 hj)
    norm_num [large,J,Finset.sum_range_succ,Nat.factorial]
  have hpU : p (19413/25000:ℝ)≤(54681/250000:ℝ) := by
    apply le_trans (p_taylor_upper (by norm_num) 6 hj')
    norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hla : lambda (19413/25000:ℝ)≤(168659/125000:ℝ) := by
    apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj
    norm_num [E,J,Finset.sum_range_succ,Nat.factorial]
  have hg : G (19413/25000:ℝ)≤(772799/1000000:ℝ) := G_upper_of_lambda (by norm_num) hla (by norm_num)
  exact loss_row (lo:=(177/400:ℝ)) (q:=(19413/25000:ℝ)) (v:=(107451/125000:ℝ))
    (u:=(54681/250000:ℝ)^2*(772799/1000000:ℝ)) (by norm_num) hr.1 hx (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (loss_bound (by norm_num) hpU hg) (hP.trans hpL) hl

lemma large_18 {r x:ℝ} (hr:r∈Icc (89/200:ℝ) (179/400:ℝ)) (hx:0≤x)
    (hl:(9/(8*Real.pi))*r^2/(1+Real.sqrt (1-(4/3:ℝ)*r^2))≤loss x) : large r < p x := by
  by_contra hn
  have hP : p x ≤ large (179/400:ℝ) := (le_of_not_gt hn).trans (large_mono (by change 0≤r; linarith only [hr.1]) (by norm_num) hr.2)
  have hj : 0≤J 12 (38581/50000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hj' : 0≤J 13 (38581/50000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hpL : large (179/400:ℝ) ≤ p (38581/50000:ℝ) := by
    apply le_trans ?_ (p_taylor_lower (by norm_num) 6 hj)
    norm_num [large,J,Finset.sum_range_succ,Nat.factorial]
  have hpU : p (38581/50000:ℝ)≤(55043/250000:ℝ) := by
    apply le_trans (p_taylor_upper (by norm_num) 6 hj')
    norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hla : lambda (38581/50000:ℝ)≤(84093/62500:ℝ) := by
    apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj
    norm_num [E,J,Finset.sum_range_succ,Nat.factorial]
  have hg : G (38581/50000:ℝ)≤(772133/1000000:ℝ) := G_upper_of_lambda (by norm_num) hla (by norm_num)
  exact loss_row (lo:=(89/200:ℝ)) (q:=(38581/50000:ℝ)) (v:=(171577/200000:ℝ))
    (u:=(55043/250000:ℝ)^2*(772133/1000000:ℝ)) (by norm_num) hr.1 hx (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (loss_bound (by norm_num) hpU hg) (hP.trans hpL) hl

lemma large_19 {r x:ℝ} (hr:r∈Icc (179/400:ℝ) (9/20:ℝ)) (hx:0≤x)
    (hl:(9/(8*Real.pi))*r^2/(1+Real.sqrt (1-(4/3:ℝ)*r^2))≤loss x) : large r < p x := by
  by_contra hn
  have hP : p x ≤ large (9/20:ℝ) := (le_of_not_gt hn).trans (large_mono (by change 0≤r; linarith only [hr.1]) (by norm_num) hr.2)
  have hj : 0≤J 12 (7667/10000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hj' : 0≤J 13 (7667/10000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hpL : large (9/20:ℝ) ≤ p (7667/10000:ℝ) := by
    apply le_trans ?_ (p_taylor_lower (by norm_num) 6 hj)
    norm_num [large,J,Finset.sum_range_succ,Nat.factorial]
  have hpU : p (7667/10000:ℝ)≤(3463/15625:ℝ) := by
    apply le_trans (p_taylor_upper (by norm_num) 6 hj')
    norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hla : lambda (7667/10000:ℝ)≤(1341691/1000000:ℝ) := by
    apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj
    norm_num [E,J,Finset.sum_range_succ,Nat.factorial]
  have hg : G (7667/10000:ℝ)≤(771461/1000000:ℝ) := G_upper_of_lambda (by norm_num) hla (by norm_num)
  exact loss_row (lo:=(179/400:ℝ)) (q:=(7667/10000:ℝ)) (v:=(17123/20000:ℝ))
    (u:=(3463/15625:ℝ)^2*(771461/1000000:ℝ)) (by norm_num) hr.1 hx (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (loss_bound (by norm_num) hpU hg) (hP.trans hpL) hl

lemma large_20 {r x:ℝ} (hr:r∈Icc (9/20:ℝ) (181/400:ℝ)) (hx:0≤x)
    (hl:(9/(8*Real.pi))*r^2/(1+Real.sqrt (1-(4/3:ℝ)*r^2))≤loss x) : large r < p x := by
  by_contra hn
  have hP : p x ≤ large (181/400:ℝ) := (le_of_not_gt hn).trans (large_mono (by change 0≤r; linarith only [hr.1]) (by norm_num) hr.2)
  have hj : 0≤J 12 (38089/50000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hj' : 0≤J 13 (38089/50000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hpL : large (181/400:ℝ) ≤ p (38089/50000:ℝ) := by
    apply le_trans ?_ (p_taylor_lower (by norm_num) 6 hj)
    norm_num [large,J,Finset.sum_range_succ,Nat.factorial]
  have hpU : p (38089/50000:ℝ)≤(111549/500000:ℝ) := by
    apply le_trans (p_taylor_upper (by norm_num) 6 hj')
    norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hla : lambda (38089/50000:ℝ)≤(668949/500000:ℝ) := by
    apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj
    norm_num [E,J,Finset.sum_range_succ,Nat.factorial]
  have hg : G (38089/50000:ℝ)≤(192697/250000:ℝ) := G_upper_of_lambda (by norm_num) hla (by norm_num)
  exact loss_row (lo:=(9/20:ℝ)) (q:=(38089/50000:ℝ)) (v:=(854401/1000000:ℝ))
    (u:=(111549/500000:ℝ)^2*(192697/250000:ℝ)) (by norm_num) hr.1 hx (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (loss_bound (by norm_num) hpU hg) (hP.trans hpL) hl

lemma large_21 {r x:ℝ} (hr:r∈Icc (181/400:ℝ) (91/200:ℝ)) (hx:0≤x)
    (hl:(9/(8*Real.pi))*r^2/(1+Real.sqrt (1-(4/3:ℝ)*r^2))≤loss x) : large r < p x := by
  by_contra hn
  have hP : p x ≤ large (91/200:ℝ) := (le_of_not_gt hn).trans (large_mono (by change 0≤r; linarith only [hr.1]) (by norm_num) hr.2)
  have hj : 0≤J 12 (15137/20000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hj' : 0≤J 13 (15137/20000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hpL : large (91/200:ℝ) ≤ p (15137/20000:ℝ) := by
    apply le_trans ?_ (p_taylor_lower (by norm_num) 6 hj)
    norm_num [large,J,Finset.sum_range_succ,Nat.factorial]
  have hpU : p (15137/20000:ℝ)≤(56143/250000:ℝ) := by
    apply le_trans (p_taylor_upper (by norm_num) 6 hj')
    norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hla : lambda (15137/20000:ℝ)≤(13341/10000:ℝ) := by
    apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj
    norm_num [E,J,Finset.sum_range_succ,Nat.factorial]
  have hg : G (15137/20000:ℝ)≤(77011/100000:ℝ) := G_upper_of_lambda (by norm_num) hla (by norm_num)
  exact loss_row (lo:=(181/400:ℝ)) (q:=(15137/20000:ℝ)) (v:=(852639/1000000:ℝ))
    (u:=(56143/250000:ℝ)^2*(77011/100000:ℝ)) (by norm_num) hr.1 hx (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (loss_bound (by norm_num) hpU hg) (hP.trans hpL) hl

lemma large_22 {r x:ℝ} (hr:r∈Icc (91/200:ℝ) (183/400:ℝ)) (hx:0≤x)
    (hl:(9/(8*Real.pi))*r^2/(1+Real.sqrt (1-(4/3:ℝ)*r^2))≤loss x) : large r < p x := by
  by_contra hn
  have hP : p x ≤ large (183/400:ℝ) := (le_of_not_gt hn).trans (large_mono (by change 0≤r; linarith only [hr.1]) (by norm_num) hr.2)
  have hj : 0≤J 12 (75191/100000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hj' : 0≤J 13 (75191/100000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hpL : large (183/400:ℝ) ≤ p (75191/100000:ℝ) := by
    apply le_trans ?_ (p_taylor_lower (by norm_num) 6 hj)
    norm_num [large,J,Finset.sum_range_succ,Nat.factorial]
  have hpU : p (75191/100000:ℝ)≤(45211/200000:ℝ) := by
    apply le_trans (p_taylor_upper (by norm_num) 6 hj')
    norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hla : lambda (75191/100000:ℝ)≤(665149/500000:ℝ) := by
    apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj
    norm_num [E,J,Finset.sum_range_succ,Nat.factorial]
  have hg : G (75191/100000:ℝ)≤(769429/1000000:ℝ) := G_upper_of_lambda (by norm_num) hla (by norm_num)
  exact loss_row (lo:=(91/200:ℝ)) (q:=(75191/100000:ℝ)) (v:=(850863/1000000:ℝ))
    (u:=(45211/200000:ℝ)^2*(769429/1000000:ℝ)) (by norm_num) hr.1 hx (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (loss_bound (by norm_num) hpU hg) (hP.trans hpL) hl

lemma large_23 {r x:ℝ} (hr:r∈Icc (183/400:ℝ) (23/50:ℝ)) (hx:0≤x)
    (hl:(9/(8*Real.pi))*r^2/(1+Real.sqrt (1-(4/3:ℝ)*r^2))≤loss x) : large r < p x := by
  by_contra hn
  have hP : p x ≤ large (23/50:ℝ) := (le_of_not_gt hn).trans (large_mono (by change 0≤r; linarith only [hr.1]) (by norm_num) hr.2)
  have hj : 0≤J 12 (9337/12500:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hj' : 0≤J 13 (9337/12500:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hpL : large (23/50:ℝ) ≤ p (9337/12500:ℝ) := by
    apply le_trans ?_ (p_taylor_lower (by norm_num) 6 hj)
    norm_num [large,J,Finset.sum_range_succ,Nat.factorial]
  have hpU : p (9337/12500:ℝ)≤(113773/500000:ℝ) := by
    apply le_trans (p_taylor_upper (by norm_num) 6 hj')
    norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hla : lambda (9337/12500:ℝ)≤(1326491/1000000:ℝ) := by
    apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj
    norm_num [E,J,Finset.sum_range_succ,Nat.factorial]
  have hg : G (9337/12500:ℝ)≤(768743/1000000:ℝ) := G_upper_of_lambda (by norm_num) hla (by norm_num)
  exact loss_row (lo:=(183/400:ℝ)) (q:=(9337/12500:ℝ)) (v:=(424537/500000:ℝ))
    (u:=(113773/500000:ℝ)^2*(768743/1000000:ℝ)) (by norm_num) hr.1 hx (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (loss_bound (by norm_num) hpU hg) (hP.trans hpL) hl

lemma large_24 {r x:ℝ} (hr:r∈Icc (23/50:ℝ) (37/80:ℝ)) (hx:0≤x)
    (hl:(9/(8*Real.pi))*r^2/(1+Real.sqrt (1-(4/3:ℝ)*r^2))≤loss x) : large r < p x := by
  by_contra hn
  have hP : p x ≤ large (37/80:ℝ) := (le_of_not_gt hn).trans (large_mono (by change 0≤r; linarith only [hr.1]) (by norm_num) hr.2)
  have hj : 0≤J 12 (371/500:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hj' : 0≤J 13 (371/500:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hpL : large (37/80:ℝ) ≤ p (371/500:ℝ) := by
    apply le_trans ?_ (p_taylor_lower (by norm_num) 6 hj)
    norm_num [large,J,Finset.sum_range_succ,Nat.factorial]
  have hpU : p (371/500:ℝ)≤(114523/500000:ℝ) := by
    apply le_trans (p_taylor_upper (by norm_num) 6 hj')
    norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hla : lambda (371/500:ℝ)≤(33067/25000:ℝ) := by
    apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj
    norm_num [E,J,Finset.sum_range_succ,Nat.factorial]
  have hg : G (371/500:ℝ)≤(384027/500000:ℝ) := G_upper_of_lambda (by norm_num) hla (by norm_num)
  exact loss_row (lo:=(23/50:ℝ)) (q:=(371/500:ℝ)) (v:=(847271/1000000:ℝ))
    (u:=(114523/500000:ℝ)^2*(384027/500000:ℝ)) (by norm_num) hr.1 hx (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (loss_bound (by norm_num) hpU hg) (hP.trans hpL) hl

end GaussianPropeller.FourCertificates

end OAI
end

section
-- module Solutions.OAIQW_GaussianPropeller.LossCertificates
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

lemma large_25 {r x:ℝ} (hr:r∈Icc (37/80:ℝ) (93/200:ℝ)) (hx:0≤x)
    (hl:(9/(8*Real.pi))*r^2/(1+Real.sqrt (1-(4/3:ℝ)*r^2))≤loss x) : large r < p x := by
  by_contra hn
  have hP : p x ≤ large (93/200:ℝ) := (le_of_not_gt hn).trans (large_mono (by change 0≤r; linarith only [hr.1]) (by norm_num) hr.2)
  have hj : 0≤J 12 (73703/100000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hj' : 0≤J 13 (73703/100000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hpL : large (93/200:ℝ) ≤ p (73703/100000:ℝ) := by
    apply le_trans ?_ (p_taylor_lower (by norm_num) 6 hj)
    norm_num [large,J,Finset.sum_range_succ,Nat.factorial]
  have hpU : p (73703/100000:ℝ)≤(46111/200000:ℝ) := by
    apply le_trans (p_taylor_upper (by norm_num) 6 hj')
    norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hla : lambda (73703/100000:ℝ)≤(263773/200000:ℝ) := by
    apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj
    norm_num [E,J,Finset.sum_range_succ,Nat.factorial]
  have hg : G (73703/100000:ℝ)≤(383681/500000:ℝ) := G_upper_of_lambda (by norm_num) hla (by norm_num)
  exact loss_row (lo:=(37/80:ℝ)) (q:=(73703/100000:ℝ)) (v:=(422727/500000:ℝ))
    (u:=(46111/200000:ℝ)^2*(383681/500000:ℝ)) (by norm_num) hr.1 hx (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (loss_bound (by norm_num) hpU hg) (hP.trans hpL) hl

lemma large_26 {r x:ℝ} (hr:r∈Icc (93/200:ℝ) (187/400:ℝ)) (hx:0≤x)
    (hl:(9/(8*Real.pi))*r^2/(1+Real.sqrt (1-(4/3:ℝ)*r^2))≤loss x) : large r < p x := by
  by_contra hn
  have hP : p x ≤ large (187/400:ℝ) := (le_of_not_gt hn).trans (large_mono (by change 0≤r; linarith only [hr.1]) (by norm_num) hr.2)
  have hj : 0≤J 12 (36603/50000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hj' : 0≤J 13 (36603/50000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hpL : large (187/400:ℝ) ≤ p (36603/50000:ℝ) := by
    apply le_trans ?_ (p_taylor_lower (by norm_num) 6 hj)
    norm_num [large,J,Finset.sum_range_succ,Nat.factorial]
  have hpU : p (36603/50000:ℝ)≤(58017/250000:ℝ) := by
    apply le_trans (p_taylor_upper (by norm_num) 6 hj')
    norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hla : lambda (36603/50000:ℝ)≤(657527/500000:ℝ) := by
    apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj
    norm_num [E,J,Finset.sum_range_succ,Nat.factorial]
  have hg : G (36603/50000:ℝ)≤(766669/1000000:ℝ) := G_upper_of_lambda (by norm_num) hla (by norm_num)
  exact loss_row (lo:=(93/200:ℝ)) (q:=(36603/50000:ℝ)) (v:=(105453/125000:ℝ))
    (u:=(58017/250000:ℝ)^2*(766669/1000000:ℝ)) (by norm_num) hr.1 hx (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (loss_bound (by norm_num) hpU hg) (hP.trans hpL) hl

lemma large_27 {r x:ℝ} (hr:r∈Icc (187/400:ℝ) (47/100:ℝ)) (hx:0≤x)
    (hl:(9/(8*Real.pi))*r^2/(1+Real.sqrt (1-(4/3:ℝ)*r^2))≤loss x) : large r < p x := by
  by_contra hn
  have hP : p x ≤ large (47/100:ℝ) := (le_of_not_gt hn).trans (large_mono (by change 0≤r; linarith only [hr.1]) (by norm_num) hr.2)
  have hj : 0≤J 12 (18177/25000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hj' : 0≤J 13 (18177/25000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hpL : large (47/100:ℝ) ≤ p (18177/25000:ℝ) := by
    apply le_trans ?_ (p_taylor_lower (by norm_num) 6 hj)
    norm_num [large,J,Finset.sum_range_succ,Nat.factorial]
  have hpU : p (18177/25000:ℝ)≤(233591/1000000:ℝ) := by
    apply le_trans (p_taylor_upper (by norm_num) 6 hj')
    norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hla : lambda (18177/25000:ℝ)≤(655619/500000:ℝ) := by
    apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj
    norm_num [E,J,Finset.sum_range_succ,Nat.factorial]
  have hg : G (18177/25000:ℝ)≤(765971/1000000:ℝ) := G_upper_of_lambda (by norm_num) hla (by norm_num)
  exact loss_row (lo:=(187/400:ℝ)) (q:=(18177/25000:ℝ)) (v:=(841779/1000000:ℝ))
    (u:=(233591/1000000:ℝ)^2*(765971/1000000:ℝ)) (by norm_num) hr.1 hx (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (loss_bound (by norm_num) hpU hg) (hP.trans hpL) hl

lemma large_28 {r x:ℝ} (hr:r∈Icc (47/100:ℝ) (189/400:ℝ)) (hx:0≤x)
    (hl:(9/(8*Real.pi))*r^2/(1+Real.sqrt (1-(4/3:ℝ)*r^2))≤loss x) : large r < p x := by
  by_contra hn
  have hP : p x ≤ large (189/400:ℝ) := (le_of_not_gt hn).trans (large_mono (by change 0≤r; linarith only [hr.1]) (by norm_num) hr.2)
  have hj : 0≤J 12 (4513/6250:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hj' : 0≤J 13 (4513/6250:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hpL : large (189/400:ℝ) ≤ p (4513/6250:ℝ) := by
    apply le_trans ?_ (p_taylor_lower (by norm_num) 6 hj)
    norm_num [large,J,Finset.sum_range_succ,Nat.factorial]
  have hpU : p (4513/6250:ℝ)≤(1881/8000:ℝ) := by
    apply le_trans (p_taylor_upper (by norm_num) 6 hj')
    norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hla : lambda (4513/6250:ℝ)≤(130741/100000:ℝ) := by
    apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj
    norm_num [E,J,Finset.sum_range_succ,Nat.factorial]
  have hg : G (4513/6250:ℝ)≤(765267/1000000:ℝ) := G_upper_of_lambda (by norm_num) hla (by norm_num)
  exact loss_row (lo:=(47/100:ℝ)) (q:=(4513/6250:ℝ)) (v:=(839921/1000000:ℝ))
    (u:=(1881/8000:ℝ)^2*(765267/1000000:ℝ)) (by norm_num) hr.1 hx (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (loss_bound (by norm_num) hpU hg) (hP.trans hpL) hl

lemma large_29 {r x:ℝ} (hr:r∈Icc (189/400:ℝ) (19/40:ℝ)) (hx:0≤x)
    (hl:(9/(8*Real.pi))*r^2/(1+Real.sqrt (1-(4/3:ℝ)*r^2))≤loss x) : large r < p x := by
  by_contra hn
  have hP : p x ≤ large (19/40:ℝ) := (le_of_not_gt hn).trans (large_mono (by change 0≤r; linarith only [hr.1]) (by norm_num) hr.2)
  have hj : 0≤J 12 (17927/25000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hj' : 0≤J 13 (17927/25000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hpL : large (19/40:ℝ) ≤ p (17927/25000:ℝ) := by
    apply le_trans ?_ (p_taylor_lower (by norm_num) 6 hj)
    norm_num [large,J,Finset.sum_range_succ,Nat.factorial]
  have hpU : p (17927/25000:ℝ)≤(47333/200000:ℝ) := by
    apply le_trans (p_taylor_upper (by norm_num) 6 hj')
    norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hla : lambda (17927/25000:ℝ)≤(651793/500000:ℝ) := by
    apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj
    norm_num [E,J,Finset.sum_range_succ,Nat.factorial]
  have hg : G (17927/25000:ℝ)≤(382281/500000:ℝ) := G_upper_of_lambda (by norm_num) hla (by norm_num)
  exact loss_row (lo:=(189/400:ℝ)) (q:=(17927/25000:ℝ)) (v:=(838049/1000000:ℝ))
    (u:=(47333/200000:ℝ)^2*(382281/500000:ℝ)) (by norm_num) hr.1 hx (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (loss_bound (by norm_num) hpU hg) (hP.trans hpL) hl

lemma large_30 {r x:ℝ} (hr:r∈Icc (19/40:ℝ) (191/400:ℝ)) (hx:0≤x)
    (hl:(9/(8*Real.pi))*r^2/(1+Real.sqrt (1-(4/3:ℝ)*r^2))≤loss x) : large r < p x := by
  by_contra hn
  have hP : p x ≤ large (191/400:ℝ) := (le_of_not_gt hn).trans (large_mono (by change 0≤r; linarith only [hr.1]) (by norm_num) hr.2)
  have hj : 0≤J 12 (8901/12500:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hj' : 0≤J 13 (8901/12500:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hpL : large (191/400:ℝ) ≤ p (8901/12500:ℝ) := by
    apply le_trans ?_ (p_taylor_lower (by norm_num) 6 hj)
    norm_num [large,J,Finset.sum_range_succ,Nat.factorial]
  have hpU : p (8901/12500:ℝ)≤(23821/100000:ℝ) := by
    apply le_trans (p_taylor_upper (by norm_num) 6 hj')
    norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hla : lambda (8901/12500:ℝ)≤(649883/500000:ℝ) := by
    apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj
    norm_num [E,J,Finset.sum_range_succ,Nat.factorial]
  have hg : G (8901/12500:ℝ)≤(152771/200000:ℝ) := G_upper_of_lambda (by norm_num) hla (by norm_num)
  exact loss_row (lo:=(19/40:ℝ)) (q:=(8901/12500:ℝ)) (v:=(418081/500000:ℝ))
    (u:=(23821/100000:ℝ)^2*(152771/200000:ℝ)) (by norm_num) hr.1 hx (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (loss_bound (by norm_num) hpU hg) (hP.trans hpL) hl

lemma large_31 {r x:ℝ} (hr:r∈Icc (191/400:ℝ) (12/25:ℝ)) (hx:0≤x)
    (hl:(9/(8*Real.pi))*r^2/(1+Real.sqrt (1-(4/3:ℝ)*r^2))≤loss x) : large r < p x := by
  by_contra hn
  have hP : p x ≤ large (12/25:ℝ) := (le_of_not_gt hn).trans (large_mono (by change 0≤r; linarith only [hr.1]) (by norm_num) hr.2)
  have hj : 0≤J 12 (35353/50000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hj' : 0≤J 13 (35353/50000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hpL : large (12/25:ℝ) ≤ p (35353/50000:ℝ) := by
    apply le_trans ?_ (p_taylor_lower (by norm_num) 6 hj)
    norm_num [large,J,Finset.sum_range_succ,Nat.factorial]
  have hpU : p (35353/50000:ℝ)≤(239767/1000000:ℝ) := by
    apply le_trans (p_taylor_upper (by norm_num) 6 hj')
    norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hla : lambda (35353/50000:ℝ)≤(1295933/1000000:ℝ) := by
    apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj
    norm_num [E,J,Finset.sum_range_succ,Nat.factorial]
  have hg : G (35353/50000:ℝ)≤(38157/50000:ℝ) := G_upper_of_lambda (by norm_num) hla (by norm_num)
  exact loss_row (lo:=(191/400:ℝ)) (q:=(35353/50000:ℝ)) (v:=(417131/500000:ℝ))
    (u:=(239767/1000000:ℝ)^2*(38157/50000:ℝ)) (by norm_num) hr.1 hx (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (loss_bound (by norm_num) hpU hg) (hP.trans hpL) hl

lemma large_32 {r x:ℝ} (hr:r∈Icc (12/25:ℝ) (193/400:ℝ)) (hx:0≤x)
    (hl:(9/(8*Real.pi))*r^2/(1+Real.sqrt (1-(4/3:ℝ)*r^2))≤loss x) : large r < p x := by
  by_contra hn
  have hP : p x ≤ large (193/400:ℝ) := (le_of_not_gt hn).trans (large_mono (by change 0≤r; linarith only [hr.1]) (by norm_num) hr.2)
  have hj : 0≤J 12 (70203/100000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hj' : 0≤J 13 (70203/100000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hpL : large (193/400:ℝ) ≤ p (70203/100000:ℝ) := by
    apply le_trans ?_ (p_taylor_lower (by norm_num) 6 hj)
    norm_num [large,J,Finset.sum_range_succ,Nat.factorial]
  have hpU : p (70203/100000:ℝ)≤(241333/1000000:ℝ) := by
    apply le_trans (p_taylor_upper (by norm_num) 6 hj')
    norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hla : lambda (70203/100000:ℝ)≤(1292097/1000000:ℝ) := by
    apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj
    norm_num [E,J,Finset.sum_range_succ,Nat.factorial]
  have hg : G (70203/100000:ℝ)≤(95303/125000:ℝ) := G_upper_of_lambda (by norm_num) hla (by norm_num)
  exact loss_row (lo:=(12/25:ℝ)) (q:=(70203/100000:ℝ)) (v:=(832347/1000000:ℝ))
    (u:=(241333/1000000:ℝ)^2*(95303/125000:ℝ)) (by norm_num) hr.1 hx (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (loss_bound (by norm_num) hpU hg) (hP.trans hpL) hl

lemma large_33 {r x:ℝ} (hr:r∈Icc (193/400:ℝ) (97/200:ℝ)) (hx:0≤x)
    (hl:(9/(8*Real.pi))*r^2/(1+Real.sqrt (1-(4/3:ℝ)*r^2))≤loss x) : large r < p x := by
  by_contra hn
  have hP : p x ≤ large (97/200:ℝ) := (le_of_not_gt hn).trans (large_mono (by change 0≤r; linarith only [hr.1]) (by norm_num) hr.2)
  have hj : 0≤J 12 (697/1000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hj' : 0≤J 13 (697/1000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hpL : large (97/200:ℝ) ≤ p (697/1000:ℝ) := by
    apply le_trans ?_ (p_taylor_lower (by norm_num) 6 hj)
    norm_num [large,J,Finset.sum_range_succ,Nat.factorial]
  have hpU : p (697/1000:ℝ)≤(30363/125000:ℝ) := by
    apply le_trans (p_taylor_upper (by norm_num) 6 hj')
    norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hla : lambda (697/1000:ℝ)≤(161033/125000:ℝ) := by
    apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj
    norm_num [E,J,Finset.sum_range_succ,Nat.factorial]
  have hg : G (697/1000:ℝ)≤(152341/200000:ℝ) := G_upper_of_lambda (by norm_num) hla (by norm_num)
  exact loss_row (lo:=(193/400:ℝ)) (q:=(697/1000:ℝ)) (v:=(830417/1000000:ℝ))
    (u:=(30363/125000:ℝ)^2*(152341/200000:ℝ)) (by norm_num) hr.1 hx (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (loss_bound (by norm_num) hpU hg) (hP.trans hpL) hl

lemma large_34 {r x:ℝ} (hr:r∈Icc (97/200:ℝ) (39/80:ℝ)) (hx:0≤x)
    (hl:(9/(8*Real.pi))*r^2/(1+Real.sqrt (1-(4/3:ℝ)*r^2))≤loss x) : large r < p x := by
  by_contra hn
  have hP : p x ≤ large (39/80:ℝ) := (le_of_not_gt hn).trans (large_mono (by change 0≤r; linarith only [hr.1]) (by norm_num) hr.2)
  have hj : 0≤J 12 (17299/25000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hj' : 0≤J 13 (17299/25000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hpL : large (39/80:ℝ) ≤ p (17299/25000:ℝ) := by
    apply le_trans ?_ (p_taylor_lower (by norm_num) 6 hj)
    norm_num [large,J,Finset.sum_range_succ,Nat.factorial]
  have hpU : p (17299/25000:ℝ)≤(61121/250000:ℝ) := by
    apply le_trans (p_taylor_upper (by norm_num) 6 hj')
    norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hla : lambda (17299/25000:ℝ)≤(321107/250000:ℝ) := by
    apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj
    norm_num [E,J,Finset.sum_range_succ,Nat.factorial]
  have hg : G (17299/25000:ℝ)≤(760983/1000000:ℝ) := G_upper_of_lambda (by norm_num) hla (by norm_num)
  exact loss_row (lo:=(97/200:ℝ)) (q:=(17299/25000:ℝ)) (v:=(828473/1000000:ℝ))
    (u:=(61121/250000:ℝ)^2*(760983/1000000:ℝ)) (by norm_num) hr.1 hx (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (loss_bound (by norm_num) hpU hg) (hP.trans hpL) hl

lemma large_35 {r x:ℝ} (hr:r∈Icc (39/80:ℝ) (49/100:ℝ)) (hx:0≤x)
    (hl:(9/(8*Real.pi))*r^2/(1+Real.sqrt (1-(4/3:ℝ)*r^2))≤loss x) : large r < p x := by
  by_contra hn
  have hP : p x ≤ large (49/100:ℝ) := (le_of_not_gt hn).trans (large_mono (by change 0≤r; linarith only [hr.1]) (by norm_num) hr.2)
  have hj : 0≤J 12 (68691/100000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hj' : 0≤J 13 (68691/100000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hpL : large (49/100:ℝ) ≤ p (68691/100000:ℝ) := by
    apply le_trans ?_ (p_taylor_lower (by norm_num) 6 hj)
    norm_num [large,J,Finset.sum_range_succ,Nat.factorial]
  have hpU : p (68691/100000:ℝ)≤(30759/125000:ℝ) := by
    apply le_trans (p_taylor_upper (by norm_num) 6 hj')
    norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hla : lambda (68691/100000:ℝ)≤(1280587/1000000:ℝ) := by
    apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj
    norm_num [E,J,Finset.sum_range_succ,Nat.factorial]
  have hg : G (68691/100000:ℝ)≤(11879/15625:ℝ) := G_upper_of_lambda (by norm_num) hla (by norm_num)
  exact loss_row (lo:=(39/80:ℝ)) (q:=(68691/100000:ℝ)) (v:=(413257/500000:ℝ))
    (u:=(30759/125000:ℝ)^2*(11879/15625:ℝ)) (by norm_num) hr.1 hx (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (loss_bound (by norm_num) hpU hg) (hP.trans hpL) hl

lemma large_36 {r x:ℝ} (hr:r∈Icc (49/100:ℝ) (197/400:ℝ)) (hx:0≤x)
    (hl:(9/(8*Real.pi))*r^2/(1+Real.sqrt (1-(4/3:ℝ)*r^2))≤loss x) : large r < p x := by
  by_contra hn
  have hP : p x ≤ large (197/400:ℝ) := (le_of_not_gt hn).trans (large_mono (by change 0≤r; linarith only [hr.1]) (by norm_num) hr.2)
  have hj : 0≤J 12 (13637/20000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hj' : 0≤J 13 (13637/20000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hpL : large (197/400:ℝ) ≤ p (13637/20000:ℝ) := by
    apply le_trans ?_ (p_taylor_lower (by norm_num) 6 hj)
    norm_num [large,J,Finset.sum_range_succ,Nat.factorial]
  have hpU : p (13637/20000:ℝ)≤(247669/1000000:ℝ) := by
    apply le_trans (p_taylor_upper (by norm_num) 6 hj')
    norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hla : lambda (13637/20000:ℝ)≤(638371/500000:ℝ) := by
    apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj
    norm_num [E,J,Finset.sum_range_succ,Nat.factorial]
  have hg : G (13637/20000:ℝ)≤(189881/250000:ℝ) := G_upper_of_lambda (by norm_num) hla (by norm_num)
  exact loss_row (lo:=(49/100:ℝ)) (q:=(13637/20000:ℝ)) (v:=(824541/1000000:ℝ))
    (u:=(247669/1000000:ℝ)^2*(189881/250000:ℝ)) (by norm_num) hr.1 hx (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (loss_bound (by norm_num) hpU hg) (hP.trans hpL) hl

lemma large_37 {r x:ℝ} (hr:r∈Icc (197/400:ℝ) (99/200:ℝ)) (hx:0≤x)
    (hl:(9/(8*Real.pi))*r^2/(1+Real.sqrt (1-(4/3:ℝ)*r^2))≤loss x) : large r < p x := by
  by_contra hn
  have hP : p x ≤ large (99/200:ℝ) := (le_of_not_gt hn).trans (large_mono (by change 0≤r; linarith only [hr.1]) (by norm_num) hr.2)
  have hj : 0≤J 12 (67679/100000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hj' : 0≤J 13 (67679/100000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hpL : large (99/200:ℝ) ≤ p (67679/100000:ℝ) := by
    apply le_trans ?_ (p_taylor_lower (by norm_num) 6 hj)
    norm_num [large,J,Finset.sum_range_succ,Nat.factorial]
  have hpU : p (67679/100000:ℝ)≤(31159/125000:ℝ) := by
    apply le_trans (p_taylor_upper (by norm_num) 6 hj')
    norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hla : lambda (67679/100000:ℝ)≤(636451/500000:ℝ) := by
    apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj
    norm_num [E,J,Finset.sum_range_succ,Nat.factorial]
  have hg : G (67679/100000:ℝ)≤(758793/1000000:ℝ) := G_upper_of_lambda (by norm_num) hla (by norm_num)
  exact loss_row (lo:=(197/400:ℝ)) (q:=(67679/100000:ℝ)) (v:=(102819/125000:ℝ))
    (u:=(31159/125000:ℝ)^2*(758793/1000000:ℝ)) (by norm_num) hr.1 hx (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (loss_bound (by norm_num) hpU hg) (hP.trans hpL) hl

lemma large_38 {r x:ℝ} (hr:r∈Icc (99/200:ℝ) (199/400:ℝ)) (hx:0≤x)
    (hl:(9/(8*Real.pi))*r^2/(1+Real.sqrt (1-(4/3:ℝ)*r^2))≤loss x) : large r < p x := by
  by_contra hn
  have hP : p x ≤ large (199/400:ℝ) := (le_of_not_gt hn).trans (large_mono (by change 0≤r; linarith only [hr.1]) (by norm_num) hr.2)
  have hj : 0≤J 12 (67171/100000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hj' : 0≤J 13 (67171/100000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hpL : large (199/400:ℝ) ≤ p (67171/100000:ℝ) := by
    apply le_trans ?_ (p_taylor_lower (by norm_num) 6 hj)
    norm_num [large,J,Finset.sum_range_succ,Nat.factorial]
  have hpU : p (67171/100000:ℝ)≤(250887/1000000:ℝ) := by
    apply le_trans (p_taylor_upper (by norm_num) 6 hj')
    norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hla : lambda (67171/100000:ℝ)≤(1269049/1000000:ℝ) := by
    apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj
    norm_num [E,J,Finset.sum_range_succ,Nat.factorial]
  have hg : G (67171/100000:ℝ)≤(758053/1000000:ℝ) := G_upper_of_lambda (by norm_num) hla (by norm_num)
  exact loss_row (lo:=(99/200:ℝ)) (q:=(67171/100000:ℝ)) (v:=(820549/1000000:ℝ))
    (u:=(250887/1000000:ℝ)^2*(758053/1000000:ℝ)) (by norm_num) hr.1 hx (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (loss_bound (by norm_num) hpU hg) (hP.trans hpL) hl

lemma large_39 {r x:ℝ} (hr:r∈Icc (199/400:ℝ) (1/2:ℝ)) (hx:0≤x)
    (hl:(9/(8*Real.pi))*r^2/(1+Real.sqrt (1-(4/3:ℝ)*r^2))≤loss x) : large r < p x := by
  by_contra hn
  have hP : p x ≤ large (1/2:ℝ) := (le_of_not_gt hn).trans (large_mono (by change 0≤r; linarith only [hr.1]) (by norm_num) hr.2)
  have hj : 0≤J 12 (66663/100000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hj' : 0≤J 13 (66663/100000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hpL : large (1/2:ℝ) ≤ p (66663/100000:ℝ) := by
    apply le_trans ?_ (p_taylor_lower (by norm_num) 6 hj)
    norm_num [large,J,Finset.sum_range_succ,Nat.factorial]
  have hpU : p (66663/100000:ℝ)≤(252507/1000000:ℝ) := by
    apply le_trans (p_taylor_upper (by norm_num) 6 hj')
    norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hla : lambda (66663/100000:ℝ)≤(1265201/1000000:ℝ) := by
    apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj
    norm_num [E,J,Finset.sum_range_succ,Nat.factorial]
  have hg : G (66663/100000:ℝ)≤(757313/1000000:ℝ) := G_upper_of_lambda (by norm_num) hla (by norm_num)
  exact loss_row (lo:=(199/400:ℝ)) (q:=(66663/100000:ℝ)) (v:=(818531/1000000:ℝ))
    (u:=(252507/1000000:ℝ)^2*(757313/1000000:ℝ)) (by norm_num) hr.1 hx (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (loss_bound (by norm_num) hpU hg) (hP.trans hpL) hl

lemma large_40 {r x:ℝ} (hr:r∈Icc (1/2:ℝ) (201/400:ℝ)) (hx:0≤x)
    (hl:(9/(8*Real.pi))*r^2/(1+Real.sqrt (1-(4/3:ℝ)*r^2))≤loss x) : large r < p x := by
  by_contra hn
  have hP : p x ≤ large (201/400:ℝ) := (le_of_not_gt hn).trans (large_mono (by change 0≤r; linarith only [hr.1]) (by norm_num) hr.2)
  have hj : 0≤J 12 (33077/50000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hj' : 0≤J 13 (33077/50000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hpL : large (201/400:ℝ) ≤ p (33077/50000:ℝ) := by
    apply le_trans ?_ (p_taylor_lower (by norm_num) 6 hj)
    norm_num [large,J,Finset.sum_range_succ,Nat.factorial]
  have hpU : p (33077/50000:ℝ)≤(31767/125000:ℝ) := by
    apply le_trans (p_taylor_upper (by norm_num) 6 hj')
    norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hla : lambda (33077/50000:ℝ)≤(315337/250000:ℝ) := by
    apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj
    norm_num [E,J,Finset.sum_range_succ,Nat.factorial]
  have hg : G (33077/50000:ℝ)≤(756567/1000000:ℝ) := G_upper_of_lambda (by norm_num) hla (by norm_num)
  exact loss_row (lo:=(1/2:ℝ)) (q:=(33077/50000:ℝ)) (v:=(816497/1000000:ℝ))
    (u:=(31767/125000:ℝ)^2*(756567/1000000:ℝ)) (by norm_num) hr.1 hx (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (loss_bound (by norm_num) hpU hg) (hP.trans hpL) hl

lemma large_41 {r x:ℝ} (hr:r∈Icc (201/400:ℝ) (101/200:ℝ)) (hx:0≤x)
    (hl:(9/(8*Real.pi))*r^2/(1+Real.sqrt (1-(4/3:ℝ)*r^2))≤loss x) : large r < p x := by
  by_contra hn
  have hP : p x ≤ large (101/200:ℝ) := (le_of_not_gt hn).trans (large_mono (by change 0≤r; linarith only [hr.1]) (by norm_num) hr.2)
  have hj : 0≤J 12 (16411/25000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hj' : 0≤J 13 (16411/25000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hpL : large (101/200:ℝ) ≤ p (16411/25000:ℝ) := by
    apply le_trans ?_ (p_taylor_lower (by norm_num) 6 hj)
    norm_num [large,J,Finset.sum_range_succ,Nat.factorial]
  have hpU : p (16411/25000:ℝ)≤(255773/1000000:ℝ) := by
    apply le_trans (p_taylor_upper (by norm_num) 6 hj')
    norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hla : lambda (16411/25000:ℝ)≤(314373/250000:ℝ) := by
    apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj
    norm_num [E,J,Finset.sum_range_succ,Nat.factorial]
  have hg : G (16411/25000:ℝ)≤(755819/1000000:ℝ) := G_upper_of_lambda (by norm_num) hla (by norm_num)
  exact loss_row (lo:=(201/400:ℝ)) (q:=(16411/25000:ℝ)) (v:=(50903/62500:ℝ))
    (u:=(255773/1000000:ℝ)^2*(755819/1000000:ℝ)) (by norm_num) hr.1 hx (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (loss_bound (by norm_num) hpU hg) (hP.trans hpL) hl

lemma large_42 {r x:ℝ} (hr:r∈Icc (101/200:ℝ) (203/400:ℝ)) (hx:0≤x)
    (hl:(9/(8*Real.pi))*r^2/(1+Real.sqrt (1-(4/3:ℝ)*r^2))≤loss x) : large r < p x := by
  by_contra hn
  have hP : p x ≤ large (203/400:ℝ) := (le_of_not_gt hn).trans (large_mono (by change 0≤r; linarith only [hr.1]) (by norm_num) hr.2)
  have hj : 0≤J 12 (65133/100000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hj' : 0≤J 13 (65133/100000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hpL : large (203/400:ℝ) ≤ p (65133/100000:ℝ) := by
    apply le_trans ?_ (p_taylor_lower (by norm_num) 6 hj)
    norm_num [large,J,Finset.sum_range_succ,Nat.factorial]
  have hpU : p (65133/100000:ℝ)≤(257419/1000000:ℝ) := by
    apply le_trans (p_taylor_upper (by norm_num) 6 hj')
    norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hla : lambda (65133/100000:ℝ)≤(19588/15625:ℝ) := by
    apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj
    norm_num [E,J,Finset.sum_range_succ,Nat.factorial]
  have hg : G (65133/100000:ℝ)≤(377533/500000:ℝ) := G_upper_of_lambda (by norm_num) hla (by norm_num)
  exact loss_row (lo:=(101/200:ℝ)) (q:=(65133/100000:ℝ)) (v:=(25387/31250:ℝ))
    (u:=(257419/1000000:ℝ)^2*(377533/500000:ℝ)) (by norm_num) hr.1 hx (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (loss_bound (by norm_num) hpU hg) (hP.trans hpL) hl

lemma large_43 {r x:ℝ} (hr:r∈Icc (203/400:ℝ) (51/100:ℝ)) (hx:0≤x)
    (hl:(9/(8*Real.pi))*r^2/(1+Real.sqrt (1-(4/3:ℝ)*r^2))≤loss x) : large r < p x := by
  by_contra hn
  have hP : p x ≤ large (51/100:ℝ) := (le_of_not_gt hn).trans (large_mono (by change 0≤r; linarith only [hr.1]) (by norm_num) hr.2)
  have hj : 0≤J 12 (32311/50000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hj' : 0≤J 13 (32311/50000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hpL : large (51/100:ℝ) ≤ p (32311/50000:ℝ) := by
    apply le_trans ?_ (p_taylor_lower (by norm_num) 6 hj)
    norm_num [large,J,Finset.sum_range_succ,Nat.factorial]
  have hpU : p (32311/50000:ℝ)≤(259071/1000000:ℝ) := by
    apply le_trans (p_taylor_upper (by norm_num) 6 hj')
    norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hla : lambda (32311/50000:ℝ)≤(78111/62500:ℝ) := by
    apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj
    norm_num [E,J,Finset.sum_range_succ,Nat.factorial]
  have hg : G (32311/50000:ℝ)≤(75431/100000:ℝ) := G_upper_of_lambda (by norm_num) hla (by norm_num)
  exact loss_row (lo:=(203/400:ℝ)) (q:=(32311/50000:ℝ)) (v:=(12661/15625:ℝ))
    (u:=(259071/1000000:ℝ)^2*(75431/100000:ℝ)) (by norm_num) hr.1 hx (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (loss_bound (by norm_num) hpU hg) (hP.trans hpL) hl

lemma large_44 {r x:ℝ} (hr:r∈Icc (51/100:ℝ) (41/80:ℝ)) (hx:0≤x)
    (hl:(9/(8*Real.pi))*r^2/(1+Real.sqrt (1-(4/3:ℝ)*r^2))≤loss x) : large r < p x := by
  by_contra hn
  have hP : p x ≤ large (41/80:ℝ) := (le_of_not_gt hn).trans (large_mono (by change 0≤r; linarith only [hr.1]) (by norm_num) hr.2)
  have hj : 0≤J 12 (64109/100000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hj' : 0≤J 13 (64109/100000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hpL : large (41/80:ℝ) ≤ p (64109/100000:ℝ) := by
    apply le_trans ?_ (p_taylor_lower (by norm_num) 6 hj)
    norm_num [large,J,Finset.sum_range_succ,Nat.factorial]
  have hpU : p (64109/100000:ℝ)≤(52147/200000:ℝ) := by
    apply le_trans (p_taylor_upper (by norm_num) 6 hj')
    norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hla : lambda (64109/100000:ℝ)≤(1245909/1000000:ℝ) := by
    apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj
    norm_num [E,J,Finset.sum_range_succ,Nat.factorial]
  have hg : G (64109/100000:ℝ)≤(15071/20000:ℝ) := G_upper_of_lambda (by norm_num) hla (by norm_num)
  exact loss_row (lo:=(51/100:ℝ)) (q:=(64109/100000:ℝ)) (v:=(50513/62500:ℝ))
    (u:=(52147/200000:ℝ)^2*(15071/20000:ℝ)) (by norm_num) hr.1 hx (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (loss_bound (by norm_num) hpU hg) (hP.trans hpL) hl

lemma large_45 {r x:ℝ} (hr:r∈Icc (41/80:ℝ) (103/200:ℝ)) (hx:0≤x)
    (hl:(9/(8*Real.pi))*r^2/(1+Real.sqrt (1-(4/3:ℝ)*r^2))≤loss x) : large r < p x := by
  by_contra hn
  have hP : p x ≤ large (103/200:ℝ) := (le_of_not_gt hn).trans (large_mono (by change 0≤r; linarith only [hr.1]) (by norm_num) hr.2)
  have hj : 0≤J 12 (15899/25000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hj' : 0≤J 13 (15899/25000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hpL : large (103/200:ℝ) ≤ p (15899/25000:ℝ) := by
    apply le_trans ?_ (p_taylor_lower (by norm_num) 6 hj)
    norm_num [large,J,Finset.sum_range_succ,Nat.factorial]
  have hpU : p (15899/25000:ℝ)≤(65601/250000:ℝ) := by
    apply le_trans (p_taylor_upper (by norm_num) 6 hj')
    norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hla : lambda (15899/25000:ℝ)≤(621023/500000:ℝ) := by
    apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj
    norm_num [E,J,Finset.sum_range_succ,Nat.factorial]
  have hg : G (15899/25000:ℝ)≤(752787/1000000:ℝ) := G_upper_of_lambda (by norm_num) hla (by norm_num)
  exact loss_row (lo:=(41/80:ℝ)) (q:=(15899/25000:ℝ)) (v:=(806097/1000000:ℝ))
    (u:=(65601/250000:ℝ)^2*(752787/1000000:ℝ)) (by norm_num) hr.1 hx (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (loss_bound (by norm_num) hpU hg) (hP.trans hpL) hl

lemma large_46 {r x:ℝ} (hr:r∈Icc (103/200:ℝ) (207/400:ℝ)) (hx:0≤x)
    (hl:(9/(8*Real.pi))*r^2/(1+Real.sqrt (1-(4/3:ℝ)*r^2))≤loss x) : large r < p x := by
  by_contra hn
  have hP : p x ≤ large (207/400:ℝ) := (le_of_not_gt hn).trans (large_mono (by change 0≤r; linarith only [hr.1]) (by norm_num) hr.2)
  have hj : 0≤J 12 (31541/50000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hj' : 0≤J 13 (31541/50000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hpL : large (207/400:ℝ) ≤ p (31541/50000:ℝ) := by
    apply le_trans ?_ (p_taylor_lower (by norm_num) 6 hj)
    norm_num [large,J,Finset.sum_range_succ,Nat.factorial]
  have hpU : p (31541/50000:ℝ)≤(132041/500000:ℝ) := by
    apply le_trans (p_taylor_upper (by norm_num) 6 hj')
    norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hla : lambda (31541/50000:ℝ)≤(1238179/1000000:ℝ) := by
    apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj
    norm_num [E,J,Finset.sum_range_succ,Nat.factorial]
  have hg : G (31541/50000:ℝ)≤(37601/50000:ℝ) := G_upper_of_lambda (by norm_num) hla (by norm_num)
  exact loss_row (lo:=(103/200:ℝ)) (q:=(31541/50000:ℝ)) (v:=(80397/100000:ℝ))
    (u:=(132041/500000:ℝ)^2*(37601/50000:ℝ)) (by norm_num) hr.1 hx (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (loss_bound (by norm_num) hpU hg) (hP.trans hpL) hl

lemma large_47 {r x:ℝ} (hr:r∈Icc (207/400:ℝ) (13/25:ℝ)) (hx:0≤x)
    (hl:(9/(8*Real.pi))*r^2/(1+Real.sqrt (1-(4/3:ℝ)*r^2))≤loss x) : large r < p x := by
  by_contra hn
  have hP : p x ≤ large (13/25:ℝ) := (le_of_not_gt hn).trans (large_mono (by change 0≤r; linarith only [hr.1]) (by norm_num) hr.2)
  have hj : 0≤J 12 (62567/100000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hj' : 0≤J 13 (62567/100000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hpL : large (13/25:ℝ) ≤ p (62567/100000:ℝ) := by
    apply le_trans ?_ (p_taylor_lower (by norm_num) 6 hj)
    norm_num [large,J,Finset.sum_range_succ,Nat.factorial]
  have hpU : p (62567/100000:ℝ)≤(33221/125000:ℝ) := by
    apply le_trans (p_taylor_upper (by norm_num) 6 hj')
    norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hla : lambda (62567/100000:ℝ)≤(1234309/1000000:ℝ) := by
    apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj
    norm_num [E,J,Finset.sum_range_succ,Nat.factorial]
  have hg : G (62567/100000:ℝ)≤(751249/1000000:ℝ) := G_upper_of_lambda (by norm_num) hla (by norm_num)
  exact loss_row (lo:=(207/400:ℝ)) (q:=(62567/100000:ℝ)) (v:=(801827/1000000:ℝ))
    (u:=(33221/125000:ℝ)^2*(751249/1000000:ℝ)) (by norm_num) hr.1 hx (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (loss_bound (by norm_num) hpU hg) (hP.trans hpL) hl

lemma large_48 {r x:ℝ} (hr:r∈Icc (13/25:ℝ) (209/400:ℝ)) (hx:0≤x)
    (hl:(9/(8*Real.pi))*r^2/(1+Real.sqrt (1-(4/3:ℝ)*r^2))≤loss x) : large r < p x := by
  by_contra hn
  have hP : p x ≤ large (209/400:ℝ) := (le_of_not_gt hn).trans (large_mono (by change 0≤r; linarith only [hr.1]) (by norm_num) hr.2)
  have hj : 0≤J 12 (15513/25000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hj' : 0≤J 13 (15513/25000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hpL : large (209/400:ℝ) ≤ p (15513/25000:ℝ) := by
    apply le_trans ?_ (p_taylor_lower (by norm_num) 6 hj)
    norm_num [large,J,Finset.sum_range_succ,Nat.factorial]
  have hpU : p (15513/25000:ℝ)≤(13373/50000:ℝ) := by
    apply le_trans (p_taylor_upper (by norm_num) 6 hj')
    norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hla : lambda (15513/25000:ℝ)≤(615221/500000:ℝ) := by
    apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj
    norm_num [E,J,Finset.sum_range_succ,Nat.factorial]
  have hg : G (15513/25000:ℝ)≤(375237/500000:ℝ) := G_upper_of_lambda (by norm_num) hla (by norm_num)
  exact loss_row (lo:=(13/25:ℝ)) (q:=(15513/25000:ℝ)) (v:=(799667/1000000:ℝ))
    (u:=(13373/50000:ℝ)^2*(375237/500000:ℝ)) (by norm_num) hr.1 hx (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (loss_bound (by norm_num) hpU hg) (hP.trans hpL) hl

lemma large_49 {r x:ℝ} (hr:r∈Icc (209/400:ℝ) (21/40:ℝ)) (hx:0≤x)
    (hl:(9/(8*Real.pi))*r^2/(1+Real.sqrt (1-(4/3:ℝ)*r^2))≤loss x) : large r < p x := by
  by_contra hn
  have hP : p x ≤ large (21/40:ℝ) := (le_of_not_gt hn).trans (large_mono (by change 0≤r; linarith only [hr.1]) (by norm_num) hr.2)
  have hj : 0≤J 12 (12307/20000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hj' : 0≤J 13 (12307/20000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hpL : large (21/40:ℝ) ≤ p (12307/20000:ℝ) := by
    apply le_trans ?_ (p_taylor_lower (by norm_num) 6 hj)
    norm_num [large,J,Finset.sum_range_succ,Nat.factorial]
  have hpU : p (12307/20000:ℝ)≤(67291/250000:ℝ) := by
    apply le_trans (p_taylor_upper (by norm_num) 6 hj')
    norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hla : lambda (12307/20000:ℝ)≤(245313/200000:ℝ) := by
    apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj
    norm_num [E,J,Finset.sum_range_succ,Nat.factorial]
  have hg : G (12307/20000:ℝ)≤(149939/200000:ℝ) := G_upper_of_lambda (by norm_num) hla (by norm_num)
  exact loss_row (lo:=(209/400:ℝ)) (q:=(12307/20000:ℝ)) (v:=(797491/1000000:ℝ))
    (u:=(67291/250000:ℝ)^2*(149939/200000:ℝ)) (by norm_num) hr.1 hx (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (loss_bound (by norm_num) hpU hg) (hP.trans hpL) hl

lemma large_of_loss_oai {r x:ℝ} (hr:r∈Icc (2/5:ℝ) (21/40:ℝ)) (hx:0≤x)
    (hl:(9/(8*Real.pi))*r^2/(1+Real.sqrt (1-(4/3:ℝ)*r^2))≤loss x) : large r < p x := by
  by_cases h0 : r≤(161/400:ℝ)
  · exact large_0 ⟨by linarith only [hr.1],h0⟩ hx hl
  by_cases h1 : r≤(81/200:ℝ)
  · exact large_1 ⟨by linarith only [h0],h1⟩ hx hl
  by_cases h2 : r≤(163/400:ℝ)
  · exact large_2 ⟨by linarith only [h1],h2⟩ hx hl
  by_cases h3 : r≤(41/100:ℝ)
  · exact large_3 ⟨by linarith only [h2],h3⟩ hx hl
  by_cases h4 : r≤(33/80:ℝ)
  · exact large_4 ⟨by linarith only [h3],h4⟩ hx hl
  by_cases h5 : r≤(83/200:ℝ)
  · exact large_5 ⟨by linarith only [h4],h5⟩ hx hl
  by_cases h6 : r≤(167/400:ℝ)
  · exact large_6 ⟨by linarith only [h5],h6⟩ hx hl
  by_cases h7 : r≤(21/50:ℝ)
  · exact large_7 ⟨by linarith only [h6],h7⟩ hx hl
  by_cases h8 : r≤(169/400:ℝ)
  · exact large_8 ⟨by linarith only [h7],h8⟩ hx hl
  by_cases h9 : r≤(17/40:ℝ)
  · exact large_9 ⟨by linarith only [h8],h9⟩ hx hl
  by_cases h10 : r≤(171/400:ℝ)
  · exact large_10 ⟨by linarith only [h9],h10⟩ hx hl
  by_cases h11 : r≤(43/100:ℝ)
  · exact large_11 ⟨by linarith only [h10],h11⟩ hx hl
  by_cases h12 : r≤(173/400:ℝ)
  · exact large_12 ⟨by linarith only [h11],h12⟩ hx hl
  by_cases h13 : r≤(87/200:ℝ)
  · exact large_13 ⟨by linarith only [h12],h13⟩ hx hl
  by_cases h14 : r≤(7/16:ℝ)
  · exact large_14 ⟨by linarith only [h13],h14⟩ hx hl
  by_cases h15 : r≤(11/25:ℝ)
  · exact large_15 ⟨by linarith only [h14],h15⟩ hx hl
  by_cases h16 : r≤(177/400:ℝ)
  · exact large_16 ⟨by linarith only [h15],h16⟩ hx hl
  by_cases h17 : r≤(89/200:ℝ)
  · exact large_17 ⟨by linarith only [h16],h17⟩ hx hl
  by_cases h18 : r≤(179/400:ℝ)
  · exact large_18 ⟨by linarith only [h17],h18⟩ hx hl
  by_cases h19 : r≤(9/20:ℝ)
  · exact large_19 ⟨by linarith only [h18],h19⟩ hx hl
  by_cases h20 : r≤(181/400:ℝ)
  · exact large_20 ⟨by linarith only [h19],h20⟩ hx hl
  by_cases h21 : r≤(91/200:ℝ)
  · exact large_21 ⟨by linarith only [h20],h21⟩ hx hl
  by_cases h22 : r≤(183/400:ℝ)
  · exact large_22 ⟨by linarith only [h21],h22⟩ hx hl
  by_cases h23 : r≤(23/50:ℝ)
  · exact large_23 ⟨by linarith only [h22],h23⟩ hx hl
  by_cases h24 : r≤(37/80:ℝ)
  · exact large_24 ⟨by linarith only [h23],h24⟩ hx hl
  by_cases h25 : r≤(93/200:ℝ)
  · exact large_25 ⟨by linarith only [h24],h25⟩ hx hl
  by_cases h26 : r≤(187/400:ℝ)
  · exact large_26 ⟨by linarith only [h25],h26⟩ hx hl
  by_cases h27 : r≤(47/100:ℝ)
  · exact large_27 ⟨by linarith only [h26],h27⟩ hx hl
  by_cases h28 : r≤(189/400:ℝ)
  · exact large_28 ⟨by linarith only [h27],h28⟩ hx hl
  by_cases h29 : r≤(19/40:ℝ)
  · exact large_29 ⟨by linarith only [h28],h29⟩ hx hl
  by_cases h30 : r≤(191/400:ℝ)
  · exact large_30 ⟨by linarith only [h29],h30⟩ hx hl
  by_cases h31 : r≤(12/25:ℝ)
  · exact large_31 ⟨by linarith only [h30],h31⟩ hx hl
  by_cases h32 : r≤(193/400:ℝ)
  · exact large_32 ⟨by linarith only [h31],h32⟩ hx hl
  by_cases h33 : r≤(97/200:ℝ)
  · exact large_33 ⟨by linarith only [h32],h33⟩ hx hl
  by_cases h34 : r≤(39/80:ℝ)
  · exact large_34 ⟨by linarith only [h33],h34⟩ hx hl
  by_cases h35 : r≤(49/100:ℝ)
  · exact large_35 ⟨by linarith only [h34],h35⟩ hx hl
  by_cases h36 : r≤(197/400:ℝ)
  · exact large_36 ⟨by linarith only [h35],h36⟩ hx hl
  by_cases h37 : r≤(99/200:ℝ)
  · exact large_37 ⟨by linarith only [h36],h37⟩ hx hl
  by_cases h38 : r≤(199/400:ℝ)
  · exact large_38 ⟨by linarith only [h37],h38⟩ hx hl
  by_cases h39 : r≤(1/2:ℝ)
  · exact large_39 ⟨by linarith only [h38],h39⟩ hx hl
  by_cases h40 : r≤(201/400:ℝ)
  · exact large_40 ⟨by linarith only [h39],h40⟩ hx hl
  by_cases h41 : r≤(101/200:ℝ)
  · exact large_41 ⟨by linarith only [h40],h41⟩ hx hl
  by_cases h42 : r≤(203/400:ℝ)
  · exact large_42 ⟨by linarith only [h41],h42⟩ hx hl
  by_cases h43 : r≤(51/100:ℝ)
  · exact large_43 ⟨by linarith only [h42],h43⟩ hx hl
  by_cases h44 : r≤(41/80:ℝ)
  · exact large_44 ⟨by linarith only [h43],h44⟩ hx hl
  by_cases h45 : r≤(103/200:ℝ)
  · exact large_45 ⟨by linarith only [h44],h45⟩ hx hl
  by_cases h46 : r≤(207/400:ℝ)
  · exact large_46 ⟨by linarith only [h45],h46⟩ hx hl
  by_cases h47 : r≤(13/25:ℝ)
  · exact large_47 ⟨by linarith only [h46],h47⟩ hx hl
  by_cases h48 : r≤(209/400:ℝ)
  · exact large_48 ⟨by linarith only [h47],h48⟩ hx hl
  exact large_49 ⟨by linarith only [h48],hr.2⟩ hx hl

end GaussianPropeller.FourCertificates

end OAI
end

theorem solution : type_of% @OAI.GaussianPropeller.FourCertificates.large_of_loss_oai := @OAI.GaussianPropeller.FourCertificates.large_of_loss_oai
