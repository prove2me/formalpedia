-- Prove2me | solution 1 for OAI.GaussianPropeller.Reduction.Configuration.impossible_four
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-19T00:20:45.464975+00:00
-- url     : https://prove2.me/submissions/1741e508-38e6-4971-93eb-b6b2bee97797

import Mathlib
import Definitions.Def_GaussianPropeller
import Definitions.Def_HairerSPDE_CameronMartin
import Definitions.Def_OAIQWGP000
import Theorems.Thm_OAI_GaussianPropeller_FourCertificates_large_of_loss
import Theorems.Thm_OAI_GaussianPropeller_FourCertificates_small_of_loss
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
-- module Solutions.OAIQW_GaussianPropeller.ResidualBounds
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

namespace GaussianPropeller.Reduction

open scoped RealInnerProductSpace

variable {d k : ℕ} [NeZero k]

omit [NeZero k] in
theorem residualCoefficient_pos {z y : Space d} (h : ⟪z,y⟫ < 0) :
    0 < residualCoefficient z y := by
  have hz : z ≠ 0 := by intro hz; simp [hz] at h
  exact div_pos (neg_pos.mpr h) (sq_pos_of_pos (norm_pos_iff.mpr hz))

end GaussianPropeller.Reduction

end OAI
end

section
-- module Solutions.OAIQW_GaussianPropeller.FourReduction
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

namespace GaussianPropeller.Reduction
variable {d k : ℕ}

lemma residual_inner_base {z y:Space d} (hz:z≠0) :
    ⟪z,y⟫ = -residualCoefficient z y*‖z‖^2 := by
  unfold residualCoefficient
  field_simp

lemma residual_norm_sq {z y:Space d} (hz:z≠0) :
    ‖residualVector z y‖^2=‖y‖^2-(residualCoefficient z y)^2*‖z‖^2 := by
  rw [residualVector,norm_add_sq_real,real_inner_smul_right,norm_smul]
  rw [real_inner_comm z y,residual_inner_base hz]
  simp only [mul_pow,Real.norm_eq_abs,sq_abs]
  ring

lemma residual_coefficient_sum (z:Fin k→Space d) (hsum:∑ j,z j=0) (i:Fin k) (hi:z i≠0) :
    ∑ j ∈ Finset.univ.erase i,residualCoefficient (z i) (z j)=1 := by
  have hh : ∑ j ∈ Finset.univ.erase i,⟪z i,z j⟫ = -‖z i‖^2 := by
    have he := congrArg (fun y=>⟪z i,y⟫) hsum
    rw [inner_sum,inner_zero_right,← Finset.sum_erase_add _ _ (Finset.mem_univ i),
      real_inner_self_eq_norm_sq] at he
    linarith only [he]
  simp only [residualCoefficient,←Finset.sum_div,Finset.sum_neg_distrib,hh,neg_neg]
  exact div_self (pow_ne_zero _ (norm_ne_zero_iff.mpr hi))

lemma residual_sum (z:Fin k→Space d) (hsum:∑ j,z j=0) (i:Fin k) (hi:z i≠0) :
    ∑ j ∈ Finset.univ.erase i,residualVector (z i) (z j)=0 := by
  have hh : ∑ j ∈ Finset.univ.erase i,z j = -(z i) := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)] at hsum
    exact eq_neg_of_add_eq_zero_left hsum
  simp only [residualVector,Finset.sum_add_distrib,←Finset.sum_smul,
    residual_coefficient_sum z hsum i hi,one_smul,hh,neg_add_cancel]

end GaussianPropeller.Reduction

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

lemma quartic_mono : MonotoneOn quartic (Ici 0) := by
  intro a ha b hb hab
  have h2:=pow_le_pow_left₀ ha hab 2
  have h4:=pow_le_pow_left₀ ha hab 4
  unfold quartic; linarith only [h2,h4]

lemma quartic_0 {r x:ℝ} (hr:r∈Icc (147/500:ℝ) (251/840:ℝ)) (hx:0≤x)
    (hl:(9/(8*Real.pi))*r^2/(1+Real.sqrt (1-(4/3:ℝ)*r^2))≤loss x) : quartic r < p x := by
  by_contra hn
  have hP : p x ≤ quartic (251/840:ℝ) := (le_of_not_gt hn).trans (quartic_mono (by change 0≤r; linarith only [hr.1]) (by norm_num) hr.2)
  have hj : 0≤J 12 (21689/20000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hj' : 0≤J 13 (21689/20000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hpL : quartic (251/840:ℝ) ≤ p (21689/20000:ℝ) := by
    apply le_trans ?_ (p_taylor_lower (by norm_num) 6 hj)
    norm_num [quartic,J,Finset.sum_range_succ,Nat.factorial]
  have hpU : p (21689/20000:ℝ)≤(27817/200000:ℝ) := by
    apply le_trans (p_taylor_upper (by norm_num) 6 hj')
    norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hla : lambda (21689/20000:ℝ)≤(1593231/1000000:ℝ) := by
    apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj
    norm_num [E,J,Finset.sum_range_succ,Nat.factorial]
  have hg : G (21689/20000:ℝ)≤(405303/500000:ℝ) := G_upper_of_lambda (by norm_num) hla (by norm_num)
  exact loss_row (lo:=(147/500:ℝ)) (q:=(21689/20000:ℝ)) (v:=(940613/1000000:ℝ))
    (u:=(27817/200000:ℝ)^2*(405303/500000:ℝ)) (by norm_num) hr.1 hx (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (loss_bound (by norm_num) hpU hg) (hP.trans hpL) hl

lemma quartic_1 {r x:ℝ} (hr:r∈Icc (251/840:ℝ) (797/2625:ℝ)) (hx:0≤x)
    (hl:(9/(8*Real.pi))*r^2/(1+Real.sqrt (1-(4/3:ℝ)*r^2))≤loss x) : quartic r < p x := by
  by_contra hn
  have hP : p x ≤ quartic (797/2625:ℝ) := (le_of_not_gt hn).trans (quartic_mono (by change 0≤r; linarith only [hr.1]) (by norm_num) hr.2)
  have hj : 0≤J 12 (21537/20000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hj' : 0≤J 13 (21537/20000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hpL : quartic (797/2625:ℝ) ≤ p (21537/20000:ℝ) := by
    apply le_trans ?_ (p_taylor_lower (by norm_num) 6 hj)
    norm_num [quartic,J,Finset.sum_range_succ,Nat.factorial]
  have hpU : p (21537/20000:ℝ)≤(17597/125000:ℝ) := by
    apply le_trans (p_taylor_upper (by norm_num) 6 hj')
    norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hla : lambda (21537/20000:ℝ)≤(793537/500000:ℝ) := by
    apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj
    norm_num [E,J,Finset.sum_range_succ,Nat.factorial]
  have hg : G (21537/20000:ℝ)≤(202441/250000:ℝ) := G_upper_of_lambda (by norm_num) hla (by norm_num)
  exact loss_row (lo:=(251/840:ℝ)) (q:=(21537/20000:ℝ)) (v:=(93859/100000:ℝ))
    (u:=(17597/125000:ℝ)^2*(202441/250000:ℝ)) (by norm_num) hr.1 hx (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (loss_bound (by norm_num) hpU hg) (hP.trans hpL) hl

lemma quartic_2 {r x:ℝ} (hr:r∈Icc (797/2625:ℝ) (2159/7000:ℝ)) (hx:0≤x)
    (hl:(9/(8*Real.pi))*r^2/(1+Real.sqrt (1-(4/3:ℝ)*r^2))≤loss x) : quartic r < p x := by
  by_contra hn
  have hP : p x ≤ quartic (2159/7000:ℝ) := (le_of_not_gt hn).trans (quartic_mono (by change 0≤r; linarith only [hr.1]) (by norm_num) hr.2)
  have hj : 0≤J 12 (26729/25000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hj' : 0≤J 13 (26729/25000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hpL : quartic (2159/7000:ℝ) ≤ p (26729/25000:ℝ) := by
    apply le_trans ?_ (p_taylor_lower (by norm_num) 6 hj)
    norm_num [quartic,J,Finset.sum_range_succ,Nat.factorial]
  have hpU : p (26729/25000:ℝ)≤(142501/1000000:ℝ) := by
    apply le_trans (p_taylor_upper (by norm_num) 6 hj')
    norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hla : lambda (26729/25000:ℝ)≤(395213/250000:ℝ) := by
    apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj
    norm_num [E,J,Finset.sum_range_succ,Nat.factorial]
  have hg : G (26729/25000:ℝ)≤(80891/100000:ℝ) := G_upper_of_lambda (by norm_num) hla (by norm_num)
  exact loss_row (lo:=(797/2625:ℝ)) (q:=(26729/25000:ℝ)) (v:=(93653/100000:ℝ))
    (u:=(142501/1000000:ℝ)^2*(80891/100000:ℝ)) (by norm_num) hr.1 hx (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (loss_bound (by norm_num) hpU hg) (hP.trans hpL) hl

lemma quartic_3 {r x:ℝ} (hr:r∈Icc (2159/7000:ℝ) (3289/10500:ℝ)) (hx:0≤x)
    (hl:(9/(8*Real.pi))*r^2/(1+Real.sqrt (1-(4/3:ℝ)*r^2))≤loss x) : quartic r < p x := by
  by_contra hn
  have hP : p x ≤ quartic (3289/10500:ℝ) := (le_of_not_gt hn).trans (quartic_mono (by change 0≤r; linarith only [hr.1]) (by norm_num) hr.2)
  have hj : 0≤J 12 (13267/12500:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hj' : 0≤J 13 (13267/12500:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hpL : quartic (3289/10500:ℝ) ≤ p (13267/12500:ℝ) := by
    apply le_trans ?_ (p_taylor_lower (by norm_num) 6 hj)
    norm_num [quartic,J,Finset.sum_range_succ,Nat.factorial]
  have hpU : p (13267/12500:ℝ)≤(72133/500000:ℝ) := by
    apply le_trans (p_taylor_upper (by norm_num) 6 hj')
    norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hla : lambda (13267/12500:ℝ)≤(787273/500000:ℝ) := by
    apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj
    norm_num [E,J,Finset.sum_range_succ,Nat.factorial]
  have hg : G (13267/12500:ℝ)≤(161607/200000:ℝ) := G_upper_of_lambda (by norm_num) hla (by norm_num)
  exact loss_row (lo:=(2159/7000:ℝ)) (q:=(13267/12500:ℝ)) (v:=(29201/31250:ℝ))
    (u:=(72133/500000:ℝ)^2*(161607/200000:ℝ)) (by norm_num) hr.1 hx (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (loss_bound (by norm_num) hpU hg) (hP.trans hpL) hl

lemma quartic_4 {r x:ℝ} (hr:r∈Icc (3289/10500:ℝ) (6679/21000:ℝ)) (hx:0≤x)
    (hl:(9/(8*Real.pi))*r^2/(1+Real.sqrt (1-(4/3:ℝ)*r^2))≤loss x) : quartic r < p x := by
  by_contra hn
  have hP : p x ≤ quartic (6679/21000:ℝ) := (le_of_not_gt hn).trans (quartic_mono (by change 0≤r; linarith only [hr.1]) (by norm_num) hr.2)
  have hj : 0≤J 12 (52673/50000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hj' : 0≤J 13 (52673/50000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hpL : quartic (6679/21000:ℝ) ≤ p (52673/50000:ℝ) := by
    apply le_trans ?_ (p_taylor_lower (by norm_num) 6 hj)
    norm_num [quartic,J,Finset.sum_range_succ,Nat.factorial]
  have hpU : p (52673/50000:ℝ)≤(36517/250000:ℝ) := by
    apply le_trans (p_taylor_upper (by norm_num) 6 hj')
    norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hla : lambda (52673/50000:ℝ)≤(1568167/1000000:ℝ) := by
    apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj
    norm_num [E,J,Finset.sum_range_succ,Nat.factorial]
  have hg : G (52673/50000:ℝ)≤(807147/1000000:ℝ) := G_upper_of_lambda (by norm_num) hla (by norm_num)
  exact loss_row (lo:=(3289/10500:ℝ)) (q:=(52673/50000:ℝ)) (v:=(932297/1000000:ℝ))
    (u:=(36517/250000:ℝ)^2*(807147/1000000:ℝ)) (by norm_num) hr.1 hx (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (loss_bound (by norm_num) hpU hg) (hP.trans hpL) hl

lemma quartic_5 {r x:ℝ} (hr:r∈Icc (6679/21000:ℝ) (113/350:ℝ)) (hx:0≤x)
    (hl:(9/(8*Real.pi))*r^2/(1+Real.sqrt (1-(4/3:ℝ)*r^2))≤loss x) : quartic r < p x := by
  by_contra hn
  have hP : p x ≤ quartic (113/350:ℝ) := (le_of_not_gt hn).trans (quartic_mono (by change 0≤r; linarith only [hr.1]) (by norm_num) hr.2)
  have hj : 0≤J 12 (52273/50000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hj' : 0≤J 13 (52273/50000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hpL : quartic (113/350:ℝ) ≤ p (52273/50000:ℝ) := by
    apply le_trans ?_ (p_taylor_lower (by norm_num) 6 hj)
    norm_num [quartic,J,Finset.sum_range_succ,Nat.factorial]
  have hpU : p (52273/50000:ℝ)≤(36977/250000:ℝ) := by
    apply le_trans (p_taylor_upper (by norm_num) 6 hj')
    norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hla : lambda (52273/50000:ℝ)≤(780857/500000:ℝ) := by
    apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj
    norm_num [E,J,Finset.sum_range_succ,Nat.factorial]
  have hg : G (52273/50000:ℝ)≤(403121/500000:ℝ) := G_upper_of_lambda (by norm_num) hla (by norm_num)
  exact loss_row (lo:=(6679/21000:ℝ)) (q:=(52273/50000:ℝ)) (v:=(930123/1000000:ℝ))
    (u:=(36977/250000:ℝ)^2*(403121/500000:ℝ)) (by norm_num) hr.1 hx (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (loss_bound (by norm_num) hpU hg) (hP.trans hpL) hl

lemma quartic_6 {r x:ℝ} (hr:r∈Icc (113/350:ℝ) (983/3000:ℝ)) (hx:0≤x)
    (hl:(9/(8*Real.pi))*r^2/(1+Real.sqrt (1-(4/3:ℝ)*r^2))≤loss x) : quartic r < p x := by
  by_contra hn
  have hP : p x ≤ quartic (983/3000:ℝ) := (le_of_not_gt hn).trans (quartic_mono (by change 0≤r; linarith only [hr.1]) (by norm_num) hr.2)
  have hj : 0≤J 12 (20747/20000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hj' : 0≤J 13 (20747/20000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hpL : quartic (983/3000:ℝ) ≤ p (20747/20000:ℝ) := by
    apply le_trans ?_ (p_taylor_lower (by norm_num) 6 hj)
    norm_num [quartic,J,Finset.sum_range_succ,Nat.factorial]
  have hpU : p (20747/20000:ℝ)≤(149789/1000000:ℝ) := by
    apply le_trans (p_taylor_upper (by norm_num) 6 hj')
    norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hla : lambda (20747/20000:ℝ)≤(77759/50000:ℝ) := by
    apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj
    norm_num [E,J,Finset.sum_range_succ,Nat.factorial]
  have hg : G (20747/20000:ℝ)≤(805319/1000000:ℝ) := G_upper_of_lambda (by norm_num) hla (by norm_num)
  exact loss_row (lo:=(113/350:ℝ)) (q:=(20747/20000:ℝ)) (v:=(927911/1000000:ℝ))
    (u:=(149789/1000000:ℝ)^2*(805319/1000000:ℝ)) (by norm_num) hr.1 hx (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (loss_bound (by norm_num) hpU hg) (hP.trans hpL) hl

lemma quartic_7 {r x:ℝ} (hr:r∈Icc (983/3000:ℝ) (3491/10500:ℝ)) (hx:0≤x)
    (hl:(9/(8*Real.pi))*r^2/(1+Real.sqrt (1-(4/3:ℝ)*r^2))≤loss x) : quartic r < p x := by
  by_contra hn
  have hP : p x ≤ quartic (3491/10500:ℝ) := (le_of_not_gt hn).trans (quartic_mono (by change 0≤r; linarith only [hr.1]) (by norm_num) hr.2)
  have hj : 0≤J 12 (51457/50000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hj' : 0≤J 13 (51457/50000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hpL : quartic (3491/10500:ℝ) ≤ p (51457/50000:ℝ) := by
    apply le_trans ?_ (p_taylor_lower (by norm_num) 6 hj)
    norm_num [quartic,J,Finset.sum_range_succ,Nat.factorial]
  have hpU : p (51457/50000:ℝ)≤(151709/1000000:ℝ) := by
    apply le_trans (p_taylor_upper (by norm_num) 6 hj')
    norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hla : lambda (51457/50000:ℝ)≤(1548573/1000000:ℝ) := by
    apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj
    norm_num [E,J,Finset.sum_range_succ,Nat.factorial]
  have hg : G (51457/50000:ℝ)≤(40219/50000:ℝ) := G_upper_of_lambda (by norm_num) hla (by norm_num)
  exact loss_row (lo:=(983/3000:ℝ)) (q:=(51457/50000:ℝ)) (v:=(46283/50000:ℝ))
    (u:=(151709/1000000:ℝ)^2*(40219/50000:ℝ)) (by norm_num) hr.1 hx (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (loss_bound (by norm_num) hpU hg) (hP.trans hpL) hl

lemma quartic_8 {r x:ℝ} (hr:r∈Icc (3491/10500:ℝ) (2361/7000:ℝ)) (hx:0≤x)
    (hl:(9/(8*Real.pi))*r^2/(1+Real.sqrt (1-(4/3:ℝ)*r^2))≤loss x) : quartic r < p x := by
  by_contra hn
  have hP : p x ≤ quartic (2361/7000:ℝ) := (le_of_not_gt hn).trans (quartic_mono (by change 0≤r; linarith only [hr.1]) (by norm_num) hr.2)
  have hj : 0≤J 12 (102083/100000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hj' : 0≤J 13 (102083/100000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hpL : quartic (2361/7000:ℝ) ≤ p (102083/100000:ℝ) := by
    apply le_trans ?_ (p_taylor_lower (by norm_num) 6 hj)
    norm_num [quartic,J,Finset.sum_range_succ,Nat.factorial]
  have hpU : p (102083/100000:ℝ)≤(15367/100000:ℝ) := by
    apply le_trans (p_taylor_upper (by norm_num) 6 hj')
    norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hla : lambda (102083/100000:ℝ)≤(770947/500000:ℝ) := by
    apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj
    norm_num [E,J,Finset.sum_range_succ,Nat.factorial]
  have hg : G (102083/100000:ℝ)≤(401713/500000:ℝ) := G_upper_of_lambda (by norm_num) hla (by norm_num)
  exact loss_row (lo:=(3491/10500:ℝ)) (q:=(102083/100000:ℝ)) (v:=(923371/1000000:ℝ))
    (u:=(15367/100000:ℝ)^2*(401713/500000:ℝ)) (by norm_num) hr.1 hx (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (loss_bound (by norm_num) hpU hg) (hP.trans hpL) hl

lemma quartic_9 {r x:ℝ} (hr:r∈Icc (2361/7000:ℝ) (898/2625:ℝ)) (hx:0≤x)
    (hl:(9/(8*Real.pi))*r^2/(1+Real.sqrt (1-(4/3:ℝ)*r^2))≤loss x) : quartic r < p x := by
  by_contra hn
  have hP : p x ≤ quartic (898/2625:ℝ) := (le_of_not_gt hn).trans (quartic_mono (by change 0≤r; linarith only [hr.1]) (by norm_num) hr.2)
  have hj : 0≤J 12 (50621/50000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hj' : 0≤J 13 (50621/50000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hpL : quartic (898/2625:ℝ) ≤ p (50621/50000:ℝ) := by
    apply le_trans ?_ (p_taylor_lower (by norm_num) 6 hj)
    norm_num [quartic,J,Finset.sum_range_succ,Nat.factorial]
  have hpU : p (50621/50000:ℝ)≤(155671/1000000:ℝ) := by
    apply le_trans (p_taylor_upper (by norm_num) 6 hj')
    norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hla : lambda (50621/50000:ℝ)≤(767571/500000:ℝ) := by
    apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj
    norm_num [E,J,Finset.sum_range_succ,Nat.factorial]
  have hg : G (50621/50000:ℝ)≤(802453/1000000:ℝ) := G_upper_of_lambda (by norm_num) hla (by norm_num)
  exact loss_row (lo:=(2361/7000:ℝ)) (q:=(50621/50000:ℝ)) (v:=(460521/500000:ℝ))
    (u:=(155671/1000000:ℝ)^2*(802453/1000000:ℝ)) (by norm_num) hr.1 hx (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (loss_bound (by norm_num) hpU hg) (hP.trans hpL) hl

lemma quartic_10 {r x:ℝ} (hr:r∈Icc (898/2625:ℝ) (1457/4200:ℝ)) (hx:0≤x)
    (hl:(9/(8*Real.pi))*r^2/(1+Real.sqrt (1-(4/3:ℝ)*r^2))≤loss x) : quartic r < p x := by
  by_contra hn
  have hP : p x ≤ quartic (1457/4200:ℝ) := (le_of_not_gt hn).trans (quartic_mono (by change 0≤r; linarith only [hr.1]) (by norm_num) hr.2)
  have hj : 0≤J 12 (100391/100000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hj' : 0≤J 13 (100391/100000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hpL : quartic (1457/4200:ℝ) ≤ p (100391/100000:ℝ) := by
    apply le_trans ?_ (p_taylor_lower (by norm_num) 6 hj)
    norm_num [quartic,J,Finset.sum_range_succ,Nat.factorial]
  have hpU : p (100391/100000:ℝ)≤(157713/1000000:ℝ) := by
    apply le_trans (p_taylor_upper (by norm_num) 6 hj')
    norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hla : lambda (100391/100000:ℝ)≤(764159/500000:ℝ) := by
    apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj
    norm_num [E,J,Finset.sum_range_succ,Nat.factorial]
  have hg : G (100391/100000:ℝ)≤(801463/1000000:ℝ) := G_upper_of_lambda (by norm_num) hla (by norm_num)
  exact loss_row (lo:=(898/2625:ℝ)) (q:=(100391/100000:ℝ)) (v:=(459337/500000:ℝ))
    (u:=(157713/1000000:ℝ)^2*(801463/1000000:ℝ)) (by norm_num) hr.1 hx (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (loss_bound (by norm_num) hpU hg) (hP.trans hpL) hl

lemma quartic_11 {r x:ℝ} (hr:r∈Icc (1457/4200:ℝ) (1231/3500:ℝ)) (hx:0≤x)
    (hl:(9/(8*Real.pi))*r^2/(1+Real.sqrt (1-(4/3:ℝ)*r^2))≤loss x) : quartic r < p x := by
  by_contra hn
  have hP : p x ≤ quartic (1231/3500:ℝ) := (le_of_not_gt hn).trans (quartic_mono (by change 0≤r; linarith only [hr.1]) (by norm_num) hr.2)
  have hj : 0≤J 12 (9953/10000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hj' : 0≤J 13 (9953/10000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hpL : quartic (1231/3500:ℝ) ≤ p (9953/10000:ℝ) := by
    apply le_trans ?_ (p_taylor_lower (by norm_num) 6 hj)
    norm_num [quartic,J,Finset.sum_range_succ,Nat.factorial]
  have hpU : p (9953/10000:ℝ)≤(79899/500000:ℝ) := by
    apply le_trans (p_taylor_upper (by norm_num) 6 hj')
    norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hla : lambda (9953/10000:ℝ)≤(1521423/1000000:ℝ) := by
    apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj
    norm_num [E,J,Finset.sum_range_succ,Nat.factorial]
  have hg : G (9953/10000:ℝ)≤(100057/125000:ℝ) := G_upper_of_lambda (by norm_num) hla (by norm_num)
  exact loss_row (lo:=(1457/4200:ℝ)) (q:=(9953/10000:ℝ)) (v:=(458133/500000:ℝ))
    (u:=(79899/500000:ℝ)^2*(100057/125000:ℝ)) (by norm_num) hr.1 hx (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (loss_bound (by norm_num) hpU hg) (hP.trans hpL) hl

lemma quartic_12 {r x:ℝ} (hr:r∈Icc (1231/3500:ℝ) (7487/21000:ℝ)) (hx:0≤x)
    (hl:(9/(8*Real.pi))*r^2/(1+Real.sqrt (1-(4/3:ℝ)*r^2))≤loss x) : quartic r < p x := by
  by_contra hn
  have hP : p x ≤ quartic (7487/21000:ℝ) := (le_of_not_gt hn).trans (quartic_mono (by change 0≤r; linarith only [hr.1]) (by norm_num) hr.2)
  have hj : 0≤J 12 (98659/100000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hj' : 0≤J 13 (98659/100000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hpL : quartic (7487/21000:ℝ) ≤ p (98659/100000:ℝ) := by
    apply le_trans ?_ (p_taylor_lower (by norm_num) 6 hj)
    norm_num [quartic,J,Finset.sum_range_succ,Nat.factorial]
  have hpU : p (98659/100000:ℝ)≤(40481/250000:ℝ) := by
    apply le_trans (p_taylor_upper (by norm_num) 6 hj')
    norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hla : lambda (98659/100000:ℝ)≤(189307/125000:ℝ) := by
    apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj
    norm_num [E,J,Finset.sum_range_succ,Nat.factorial]
  have hg : G (98659/100000:ℝ)≤(79943/100000:ℝ) := G_upper_of_lambda (by norm_num) hla (by norm_num)
  exact loss_row (lo:=(1231/3500:ℝ)) (q:=(98659/100000:ℝ)) (v:=(456909/500000:ℝ))
    (u:=(40481/250000:ℝ)^2*(79943/100000:ℝ)) (by norm_num) hr.1 hx (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (loss_bound (by norm_num) hpU hg) (hP.trans hpL) hl

lemma quartic_13 {r x:ℝ} (hr:r∈Icc (7487/21000:ℝ) (271/750:ℝ)) (hx:0≤x)
    (hl:(9/(8*Real.pi))*r^2/(1+Real.sqrt (1-(4/3:ℝ)*r^2))≤loss x) : quartic r < p x := by
  by_contra hn
  have hP : p x ≤ quartic (271/750:ℝ) := (le_of_not_gt hn).trans (quartic_mono (by change 0≤r; linarith only [hr.1]) (by norm_num) hr.2)
  have hj : 0≤J 12 (97777/100000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hj' : 0≤J 13 (97777/100000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hpL : quartic (271/750:ℝ) ≤ p (97777/100000:ℝ) := by
    apply le_trans ?_ (p_taylor_lower (by norm_num) 6 hj)
    norm_num [quartic,J,Finset.sum_range_succ,Nat.factorial]
  have hpU : p (97777/100000:ℝ)≤(164097/1000000:ℝ) := by
    apply le_trans (p_taylor_upper (by norm_num) 6 hj')
    norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hla : lambda (97777/100000:ℝ)≤(1507411/1000000:ℝ) := by
    apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj
    norm_num [E,J,Finset.sum_range_succ,Nat.factorial]
  have hg : G (97777/100000:ℝ)≤(798387/1000000:ℝ) := G_upper_of_lambda (by norm_num) hla (by norm_num)
  exact loss_row (lo:=(7487/21000:ℝ)) (q:=(97777/100000:ℝ)) (v:=(91133/100000:ℝ))
    (u:=(164097/1000000:ℝ)^2*(798387/1000000:ℝ)) (by norm_num) hr.1 hx (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (loss_bound (by norm_num) hpU hg) (hP.trans hpL) hl

lemma quartic_14 {r x:ℝ} (hr:r∈Icc (271/750:ℝ) (2563/7000:ℝ)) (hx:0≤x)
    (hl:(9/(8*Real.pi))*r^2/(1+Real.sqrt (1-(4/3:ℝ)*r^2))≤loss x) : quartic r < p x := by
  by_contra hn
  have hP : p x ≤ quartic (2563/7000:ℝ) := (le_of_not_gt hn).trans (quartic_mono (by change 0≤r; linarith only [hr.1]) (by norm_num) hr.2)
  have hj : 0≤J 12 (48443/50000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hj' : 0≤J 13 (48443/50000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hpL : quartic (2563/7000:ℝ) ≤ p (48443/50000:ℝ) := by
    apply le_trans ?_ (p_taylor_lower (by norm_num) 6 hj)
    norm_num [quartic,J,Finset.sum_range_succ,Nat.factorial]
  have hpU : p (48443/50000:ℝ)≤(16631/100000:ℝ) := by
    apply le_trans (p_taylor_upper (by norm_num) 6 hj')
    norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hla : lambda (48443/50000:ℝ)≤(1500303/1000000:ℝ) := by
    apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj
    norm_num [E,J,Finset.sum_range_succ,Nat.factorial]
  have hg : G (48443/50000:ℝ)≤(398663/500000:ℝ) := G_upper_of_lambda (by norm_num) hla (by norm_num)
  exact loss_row (lo:=(271/750:ℝ)) (q:=(48443/50000:ℝ)) (v:=(908801/1000000:ℝ))
    (u:=(16631/100000:ℝ)^2*(398663/500000:ℝ)) (by norm_num) hr.1 hx (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (loss_bound (by norm_num) hpU hg) (hP.trans hpL) hl

lemma quartic_15 {r x:ℝ} (hr:r∈Icc (2563/7000:ℝ) (779/2100:ℝ)) (hx:0≤x)
    (hl:(9/(8*Real.pi))*r^2/(1+Real.sqrt (1-(4/3:ℝ)*r^2))≤loss x) : quartic r < p x := by
  by_contra hn
  have hP : p x ≤ quartic (779/2100:ℝ) := (le_of_not_gt hn).trans (quartic_mono (by change 0≤r; linarith only [hr.1]) (by norm_num) hr.2)
  have hj : 0≤J 12 (19197/20000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hj' : 0≤J 13 (19197/20000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hpL : quartic (779/2100:ℝ) ≤ p (19197/20000:ℝ) := by
    apply le_trans ?_ (p_taylor_lower (by norm_num) 6 hj)
    norm_num [quartic,J,Finset.sum_range_succ,Nat.factorial]
  have hpU : p (19197/20000:ℝ)≤(21071/125000:ℝ) := by
    apply le_trans (p_taylor_upper (by norm_num) 6 hj')
    norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hla : lambda (19197/20000:ℝ)≤(2389/1600:ℝ) := by
    apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj
    norm_num [E,J,Finset.sum_range_succ,Nat.factorial]
  have hg : G (19197/20000:ℝ)≤(796247/1000000:ℝ) := G_upper_of_lambda (by norm_num) hla (by norm_num)
  exact loss_row (lo:=(2563/7000:ℝ)) (q:=(19197/20000:ℝ)) (v:=(90623/100000:ℝ))
    (u:=(21071/125000:ℝ)^2*(796247/1000000:ℝ)) (by norm_num) hr.1 hx (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (loss_bound (by norm_num) hpU hg) (hP.trans hpL) hl

lemma quartic_16 {r x:ℝ} (hr:r∈Icc (779/2100:ℝ) (7891/21000:ℝ)) (hx:0≤x)
    (hl:(9/(8*Real.pi))*r^2/(1+Real.sqrt (1-(4/3:ℝ)*r^2))≤loss x) : quartic r < p x := by
  by_contra hn
  have hP : p x ≤ quartic (7891/21000:ℝ) := (le_of_not_gt hn).trans (quartic_mono (by change 0≤r; linarith only [hr.1]) (by norm_num) hr.2)
  have hj : 0≤J 12 (47537/50000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hj' : 0≤J 13 (47537/50000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hpL : quartic (7891/21000:ℝ) ≤ p (47537/50000:ℝ) := by
    apply le_trans ?_ (p_taylor_lower (by norm_num) 6 hj)
    norm_num [quartic,J,Finset.sum_range_succ,Nat.factorial]
  have hpU : p (47537/50000:ℝ)≤(170871/1000000:ℝ) := by
    apply le_trans (p_taylor_upper (by norm_num) 6 hj')
    norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hla : lambda (47537/50000:ℝ)≤(1485877/1000000:ℝ) := by
    apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj
    norm_num [E,J,Finset.sum_range_succ,Nat.factorial]
  have hg : G (47537/50000:ℝ)≤(198787/250000:ℝ) := G_upper_of_lambda (by norm_num) hla (by norm_num)
  exact loss_row (lo:=(779/2100:ℝ)) (q:=(47537/50000:ℝ)) (v:=(903619/1000000:ℝ))
    (u:=(170871/1000000:ℝ)^2*(198787/250000:ℝ)) (by norm_num) hr.1 hx (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (loss_bound (by norm_num) hpU hg) (hP.trans hpL) hl

lemma quartic_17 {r x:ℝ} (hr:r∈Icc (7891/21000:ℝ) (333/875:ℝ)) (hx:0≤x)
    (hl:(9/(8*Real.pi))*r^2/(1+Real.sqrt (1-(4/3:ℝ)*r^2))≤loss x) : quartic r < p x := by
  by_contra hn
  have hP : p x ≤ quartic (333/875:ℝ) := (le_of_not_gt hn).trans (quartic_mono (by change 0≤r; linarith only [hr.1]) (by norm_num) hr.2)
  have hj : 0≤J 12 (94153/100000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hj' : 0≤J 13 (94153/100000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hpL : quartic (333/875:ℝ) ≤ p (94153/100000:ℝ) := by
    apply le_trans ?_ (p_taylor_lower (by norm_num) 6 hj)
    norm_num [quartic,J,Finset.sum_range_succ,Nat.factorial]
  have hpU : p (94153/100000:ℝ)≤(173219/1000000:ℝ) := by
    apply le_trans (p_taylor_upper (by norm_num) 6 hj')
    norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hla : lambda (94153/100000:ℝ)≤(9241/6250:ℝ) := by
    apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj
    norm_num [E,J,Finset.sum_range_succ,Nat.factorial]
  have hg : G (94153/100000:ℝ)≤(49627/62500:ℝ) := G_upper_of_lambda (by norm_num) hla (by norm_num)
  exact loss_row (lo:=(7891/21000:ℝ)) (q:=(94153/100000:ℝ)) (v:=(180193/200000:ℝ))
    (u:=(173219/1000000:ℝ)^2*(49627/62500:ℝ)) (by norm_num) hr.1 hx (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (loss_bound (by norm_num) hpU hg) (hP.trans hpL) hl

lemma quartic_18 {r x:ℝ} (hr:r∈Icc (333/875:ℝ) (8093/21000:ℝ)) (hx:0≤x)
    (hl:(9/(8*Real.pi))*r^2/(1+Real.sqrt (1-(4/3:ℝ)*r^2))≤loss x) : quartic r < p x := by
  by_contra hn
  have hP : p x ≤ quartic (8093/21000:ℝ) := (le_of_not_gt hn).trans (quartic_mono (by change 0≤r; linarith only [hr.1]) (by norm_num) hr.2)
  have hj : 0≤J 12 (46611/50000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hj' : 0≤J 13 (46611/50000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hpL : quartic (8093/21000:ℝ) ≤ p (46611/50000:ℝ) := by
    apply le_trans ?_ (p_taylor_lower (by norm_num) 6 hj)
    norm_num [quartic,J,Finset.sum_range_succ,Nat.factorial]
  have hpU : p (46611/50000:ℝ)≤(87807/500000:ℝ) := by
    apply le_trans (p_taylor_upper (by norm_num) 6 hj')
    norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hla : lambda (46611/50000:ℝ)≤(1471173/1000000:ℝ) := by
    apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj
    norm_num [E,J,Finset.sum_range_succ,Nat.factorial]
  have hg : G (46611/50000:ℝ)≤(396447/500000:ℝ) := G_upper_of_lambda (by norm_num) hla (by norm_num)
  exact loss_row (lo:=(333/875:ℝ)) (q:=(46611/50000:ℝ)) (v:=(898269/1000000:ℝ))
    (u:=(87807/500000:ℝ)^2*(396447/500000:ℝ)) (by norm_num) hr.1 hx (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (loss_bound (by norm_num) hpU hg) (hP.trans hpL) hl

lemma quartic_19 {r x:ℝ} (hr:r∈Icc (8093/21000:ℝ) (4097/10500:ℝ)) (hx:0≤x)
    (hl:(9/(8*Real.pi))*r^2/(1+Real.sqrt (1-(4/3:ℝ)*r^2))≤loss x) : quartic r < p x := by
  by_contra hn
  have hP : p x ≤ quartic (4097/10500:ℝ) := (le_of_not_gt hn).trans (quartic_mono (by change 0≤r; linarith only [hr.1]) (by norm_num) hr.2)
  have hj : 0≤J 12 (92281/100000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hj' : 0≤J 13 (92281/100000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hpL : quartic (4097/10500:ℝ) ≤ p (92281/100000:ℝ) := by
    apply le_trans ?_ (p_taylor_lower (by norm_num) 6 hj)
    norm_num [quartic,J,Finset.sum_range_succ,Nat.factorial]
  have hpU : p (92281/100000:ℝ)≤(22257/125000:ℝ) := by
    apply le_trans (p_taylor_upper (by norm_num) 6 hj')
    norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hla : lambda (92281/100000:ℝ)≤(1463719/1000000:ℝ) := by
    apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj
    norm_num [E,J,Finset.sum_range_succ,Nat.factorial]
  have hg : G (92281/100000:ℝ)≤(791739/1000000:ℝ) := G_upper_of_lambda (by norm_num) hla (by norm_num)
  exact loss_row (lo:=(8093/21000:ℝ)) (q:=(92281/100000:ℝ)) (v:=(895531/1000000:ℝ))
    (u:=(22257/125000:ℝ)^2*(791739/1000000:ℝ)) (by norm_num) hr.1 hx (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (loss_bound (by norm_num) hpU hg) (hP.trans hpL) hl

lemma quartic_20 {r x:ℝ} (hr:r∈Icc (4097/10500:ℝ) (79/200:ℝ)) (hx:0≤x)
    (hl:(9/(8*Real.pi))*r^2/(1+Real.sqrt (1-(4/3:ℝ)*r^2))≤loss x) : quartic r < p x := by
  by_contra hn
  have hP : p x ≤ quartic (79/200:ℝ) := (le_of_not_gt hn).trans (quartic_mono (by change 0≤r; linarith only [hr.1]) (by norm_num) hr.2)
  have hj : 0≤J 12 (91331/100000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hj' : 0≤J 13 (91331/100000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hpL : quartic (79/200:ℝ) ≤ p (91331/100000:ℝ) := by
    apply le_trans ?_ (p_taylor_lower (by norm_num) 6 hj)
    norm_num [quartic,J,Finset.sum_range_succ,Nat.factorial]
  have hpU : p (91331/100000:ℝ)≤(90271/500000:ℝ) := by
    apply le_trans (p_taylor_upper (by norm_num) 6 hj')
    norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hla : lambda (91331/100000:ℝ)≤(364051/250000:ℝ) := by
    apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj
    norm_num [E,J,Finset.sum_range_succ,Nat.factorial]
  have hg : G (91331/100000:ℝ)≤(158113/200000:ℝ) := G_upper_of_lambda (by norm_num) hla (by norm_num)
  exact loss_row (lo:=(4097/10500:ℝ)) (q:=(91331/100000:ℝ)) (v:=(3571/4000:ℝ))
    (u:=(90271/500000:ℝ)^2*(158113/200000:ℝ)) (by norm_num) hr.1 hx (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (loss_bound (by norm_num) hpU hg) (hP.trans hpL) hl

lemma quartic_of_loss {r x:ℝ} (hr:r∈Icc (147/500:ℝ) (79/200:ℝ)) (hx:0≤x)
    (hl:(9/(8*Real.pi))*r^2/(1+Real.sqrt (1-(4/3:ℝ)*r^2))≤loss x) : quartic r < p x := by
  by_cases h0 : r≤(251/840:ℝ)
  · exact quartic_0 ⟨by linarith only [hr.1],h0⟩ hx hl
  by_cases h1 : r≤(797/2625:ℝ)
  · exact quartic_1 ⟨by linarith only [h0],h1⟩ hx hl
  by_cases h2 : r≤(2159/7000:ℝ)
  · exact quartic_2 ⟨by linarith only [h1],h2⟩ hx hl
  by_cases h3 : r≤(3289/10500:ℝ)
  · exact quartic_3 ⟨by linarith only [h2],h3⟩ hx hl
  by_cases h4 : r≤(6679/21000:ℝ)
  · exact quartic_4 ⟨by linarith only [h3],h4⟩ hx hl
  by_cases h5 : r≤(113/350:ℝ)
  · exact quartic_5 ⟨by linarith only [h4],h5⟩ hx hl
  by_cases h6 : r≤(983/3000:ℝ)
  · exact quartic_6 ⟨by linarith only [h5],h6⟩ hx hl
  by_cases h7 : r≤(3491/10500:ℝ)
  · exact quartic_7 ⟨by linarith only [h6],h7⟩ hx hl
  by_cases h8 : r≤(2361/7000:ℝ)
  · exact quartic_8 ⟨by linarith only [h7],h8⟩ hx hl
  by_cases h9 : r≤(898/2625:ℝ)
  · exact quartic_9 ⟨by linarith only [h8],h9⟩ hx hl
  by_cases h10 : r≤(1457/4200:ℝ)
  · exact quartic_10 ⟨by linarith only [h9],h10⟩ hx hl
  by_cases h11 : r≤(1231/3500:ℝ)
  · exact quartic_11 ⟨by linarith only [h10],h11⟩ hx hl
  by_cases h12 : r≤(7487/21000:ℝ)
  · exact quartic_12 ⟨by linarith only [h11],h12⟩ hx hl
  by_cases h13 : r≤(271/750:ℝ)
  · exact quartic_13 ⟨by linarith only [h12],h13⟩ hx hl
  by_cases h14 : r≤(2563/7000:ℝ)
  · exact quartic_14 ⟨by linarith only [h13],h14⟩ hx hl
  by_cases h15 : r≤(779/2100:ℝ)
  · exact quartic_15 ⟨by linarith only [h14],h15⟩ hx hl
  by_cases h16 : r≤(7891/21000:ℝ)
  · exact quartic_16 ⟨by linarith only [h15],h16⟩ hx hl
  by_cases h17 : r≤(333/875:ℝ)
  · exact quartic_17 ⟨by linarith only [h16],h17⟩ hx hl
  by_cases h18 : r≤(8093/21000:ℝ)
  · exact quartic_18 ⟨by linarith only [h17],h18⟩ hx hl
  by_cases h19 : r≤(4097/10500:ℝ)
  · exact quartic_19 ⟨by linarith only [h18],h19⟩ hx hl
  exact quartic_20 ⟨by linarith only [h19],hr.2⟩ hx hl

end GaussianPropeller.FourCertificates

end OAI
end

section
-- module Solutions.OAIQW_GaussianPropeller.CapCertificates
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

lemma cap_envelope {r P F:ℝ} (_hP:P≤1/2) (hF:F≤1/2)
    (hcap:r≤(8/3:ℝ)*P*(1-P)) (hpoly:(8/3:ℝ)*F*(1-F)≤r) : F≤P := by
  by_contra hn
  have hd : 0<F-P := sub_pos.mpr (lt_of_not_ge hn)
  have he : 0<(F-P)*(1-P-F) := mul_pos hd (by linarith only [hd,hF])
  nlinarith only [he,hcap,hpoly]

lemma affine_cap_poly_0 {r:ℝ} (hr:r∈Icc (39/250:ℝ) (617/1500:ℝ)) :
    (8/3:ℝ)*affine r*(1-affine r)≤r := by
  have hl : 0≤r-(39/250:ℝ) := sub_nonneg.mpr hr.1
  have hu : 0≤(617/1500:ℝ)-r := sub_nonneg.mpr hr.2
  have he : r-(8/3:ℝ)*affine r*(1-affine r)-(1/10000000:ℝ) =
    (2391277896991494/336213480015625:ℝ)*(r-(39/250:ℝ))^0*((617/1500:ℝ)-r)^4 + (16684638404902488/336213480015625:ℝ)*(r-(39/250:ℝ))^1*((617/1500:ℝ)-r)^3 + (26003061476182116/336213480015625:ℝ)*(r-(39/250:ℝ))^2*((617/1500:ℝ)-r)^2 + (13152961928422872/336213480015625:ℝ)*(r-(39/250:ℝ))^3*((617/1500:ℝ)-r)^1 + (2112546341425734/336213480015625:ℝ)*(r-(39/250:ℝ))^4*((617/1500:ℝ)-r)^0 := by unfold affine; ring
  have hp : 0≤r-(8/3:ℝ)*affine r*(1-affine r)-(1/10000000:ℝ) := by rw [he]; positivity
  linarith only [hp]

lemma affine_cap_poly_1 {r:ℝ} (hr:r∈Icc (617/1500:ℝ) (539/1000:ℝ)) :
    (8/3:ℝ)*affine r*(1-affine r)≤r := by
  have hl : 0≤r-(617/1500:ℝ) := sub_nonneg.mpr hr.1
  have hu : 0≤(539/1000:ℝ)-r := sub_nonneg.mpr hr.2
  have he : r-(8/3:ℝ)*affine r*(1-affine r)-(1/10000000:ℝ) =
    (33800741462811744/336213480015625:ℝ)*(r-(617/1500:ℝ))^0*((539/1000:ℝ)-r)^4 + (97580753349487488/336213480015625:ℝ)*(r-(617/1500:ℝ))^1*((539/1000:ℝ)-r)^3 + (86815626229463616/336213480015625:ℝ)*(r-(617/1500:ℝ))^2*((539/1000:ℝ)-r)^2 + (24717526517503872/336213480015625:ℝ)*(r-(617/1500:ℝ))^3*((539/1000:ℝ)-r)^1 + (2351197555989984/336213480015625:ℝ)*(r-(617/1500:ℝ))^4*((539/1000:ℝ)-r)^0 := by unfold affine; ring
  have hp : 0≤r-(8/3:ℝ)*affine r*(1-affine r)-(1/10000000:ℝ) := by rw [he]; positivity
  linarith only [hp]

lemma affine_cap_poly_2 {r:ℝ} (hr:r∈Icc (539/1000:ℝ) (6851/12000:ℝ)) :
    (8/3:ℝ)*affine r*(1-affine r)≤r := by
  have hl : 0≤r-(539/1000:ℝ) := sub_nonneg.mpr hr.1
  have hu : 0≤(6851/12000:ℝ)-r := sub_nonneg.mpr hr.2
  have he : r-(8/3:ℝ)*affine r*(1-affine r)-(1/10000000:ℝ) =
    (601906574333435904/336213480015625:ℝ)*(r-(539/1000:ℝ))^0*((6851/12000:ℝ)-r)^4 + (1427611174546931712/336213480015625:ℝ)*(r-(539/1000:ℝ))^1*((6851/12000:ℝ)-r)^3 + (1099717789846450176/336213480015625:ℝ)*(r-(539/1000:ℝ))^2*((6851/12000:ℝ)-r)^2 + (369439192509401088/336213480015625:ℝ)*(r-(539/1000:ℝ))^3*((6851/12000:ℝ)-r)^1 + (96095288257720704/336213480015625:ℝ)*(r-(539/1000:ℝ))^4*((6851/12000:ℝ)-r)^0 := by unfold affine; ring
  have hp : 0≤r-(8/3:ℝ)*affine r*(1-affine r)-(1/10000000:ℝ) := by rw [he]; positivity
  linarith only [hp]

lemma affine_cap_poly_3 {r:ℝ} (hr:r∈Icc (6851/12000:ℝ) (3617/6000:ℝ)) :
    (8/3:ℝ)*affine r*(1-affine r)≤r := by
  have hl : 0≤r-(6851/12000:ℝ) := sub_nonneg.mpr hr.1
  have hu : 0≤(3617/6000:ℝ)-r := sub_nonneg.mpr hr.2
  have he : r-(8/3:ℝ)*affine r*(1-affine r)-(1/10000000:ℝ) =
    (96095288257720704/336213480015625:ℝ)*(r-(6851/12000:ℝ))^0*((3617/6000:ℝ)-r)^4 + (399323113552364544/336213480015625:ℝ)*(r-(6851/12000:ℝ))^1*((3617/6000:ℝ)-r)^3 + (1189369552975340544/336213480015625:ℝ)*(r-(6851/12000:ℝ))^2*((3617/6000:ℝ)-r)^2 + (1613038898973118464/336213480015625:ℝ)*(r-(6851/12000:ℝ))^3*((3617/6000:ℝ)-r)^1 + (727566456673695744/336213480015625:ℝ)*(r-(6851/12000:ℝ))^4*((3617/6000:ℝ)-r)^0 := by unfold affine; ring
  have hp : 0≤r-(8/3:ℝ)*affine r*(1-affine r)-(1/10000000:ℝ) := by rw [he]; positivity
  linarith only [hp]

lemma affine_cap_poly_4 {r:ℝ} (hr:r∈Icc (3617/6000:ℝ) (2/3:ℝ)) :
    (8/3:ℝ)*affine r*(1-affine r)≤r := by
  have hl : 0≤r-(3617/6000:ℝ) := sub_nonneg.mpr hr.1
  have hu : 0≤(2/3:ℝ)-r := sub_nonneg.mpr hr.2
  have he : r-(8/3:ℝ)*affine r*(1-affine r)-(1/10000000:ℝ) =
    (45472903542105984/336213480015625:ℝ)*(r-(3617/6000:ℝ))^0*((2/3:ℝ)-r)^4 + (2752359841069056/2689707840125:ℝ)*(r-(3617/6000:ℝ))^1*((2/3:ℝ)-r)^3 + (300227333815296/107588313605:ℝ)*(r-(3617/6000:ℝ))^2*((2/3:ℝ)-r)^2 + (67293444556800/21517662721:ℝ)*(r-(3617/6000:ℝ))^3*((2/3:ℝ)-r)^1 + (26399424960000/21517662721:ℝ)*(r-(3617/6000:ℝ))^4*((2/3:ℝ)-r)^0 := by unfold affine; ring
  have hp : 0≤r-(8/3:ℝ)*affine r*(1-affine r)-(1/10000000:ℝ) := by rw [he]; positivity
  linarith only [hp]

lemma affine_from_cap {r P:ℝ} (hr:r∈Icc (39/250:ℝ) (2/3:ℝ)) (hP:P≤1/2)
    (hcap:r≤(8/3:ℝ)*P*(1-P)) : affine r≤P := by
  have hr0 : 0≤r := by linarith only [hr.1]
  have h2 : r^2≤(2/3:ℝ)^2 := (sq_le_sq₀ hr0 (by norm_num)).mpr hr.2
  have h4 : r^4≤(2/3:ℝ)^4 := pow_le_pow_left₀ hr0 hr.2 4
  apply cap_envelope hP (by unfold affine; nlinarith only [h2,h4]) hcap

  by_cases h0 : r≤(617/1500:ℝ)
  · exact affine_cap_poly_0 ⟨by linarith only [hr.1],h0⟩
  by_cases h1 : r≤(539/1000:ℝ)
  · exact affine_cap_poly_1 ⟨by linarith only [h0],h1⟩
  by_cases h2 : r≤(6851/12000:ℝ)
  · exact affine_cap_poly_2 ⟨by linarith only [h1],h2⟩
  by_cases h3 : r≤(3617/6000:ℝ)
  · exact affine_cap_poly_3 ⟨by linarith only [h2],h3⟩
  exact affine_cap_poly_4 ⟨by linarith only [h3],hr.2⟩

lemma quartic_cap_poly_0 {r:ℝ} (hr:r∈Icc (79/200:ℝ) (637/1200:ℝ)) :
    (8/3:ℝ)*quartic r*(1-quartic r)≤r := by
  have hl : 0≤r-(79/200:ℝ) := sub_nonneg.mpr hr.1
  have hu : 0≤(637/1200:ℝ)-r := sub_nonneg.mpr hr.2
  have he : r-(8/3:ℝ)*quartic r*(1-quartic r)-(1/10000000:ℝ) =
    (52024221825751854618624/12457785357953028025:ℝ)*(r-(79/200:ℝ))^0*((637/1200:ℝ)-r)^8 + (2022092731453728987242496/12457785357953028025:ℝ)*(r-(79/200:ℝ))^1*((637/1200:ℝ)-r)^7 + (10641317401425423011309568/12457785357953028025:ℝ)*(r-(79/200:ℝ))^2*((637/1200:ℝ)-r)^6 + (24639517032378527009875968/12457785357953028025:ℝ)*(r-(79/200:ℝ))^3*((637/1200:ℝ)-r)^5 + (6174657923095921459389696/2491557071590605605:ℝ)*(r-(79/200:ℝ))^4*((637/1200:ℝ)-r)^4 + (22098785106243529719470592/12457785357953028025:ℝ)*(r-(79/200:ℝ))^5*((637/1200:ℝ)-r)^3 + (8843151939179947854507648/12457785357953028025:ℝ)*(r-(79/200:ℝ))^6*((637/1200:ℝ)-r)^2 + (1795249145491503220347264/12457785357953028025:ℝ)*(r-(79/200:ℝ))^7*((637/1200:ℝ)-r)^1 + (145872797130502554458904/12457785357953028025:ℝ)*(r-(79/200:ℝ))^8*((637/1200:ℝ)-r)^0 := by unfold quartic; ring
  have hp : 0≤r-(8/3:ℝ)*quartic r*(1-quartic r)-(1/10000000:ℝ) := by rw [he]; positivity
  linarith only [hp]

lemma quartic_cap_poly_1 {r:ℝ} (hr:r∈Icc (637/1200:ℝ) (479/800:ℝ)) :
    (8/3:ℝ)*quartic r*(1-quartic r)≤r := by
  have hl : 0≤r-(637/1200:ℝ) := sub_nonneg.mpr hr.1
  have hu : 0≤(479/800:ℝ)-r := sub_nonneg.mpr hr.2
  have he : r-(8/3:ℝ)*quartic r*(1-quartic r)-(1/10000000:ℝ) =
    (37343436065408653941479424/12457785357953028025:ℝ)*(r-(637/1200:ℝ))^0*((479/800:ℝ)-r)^8 + (218329342161991435093303296/12457785357953028025:ℝ)*(r-(637/1200:ℝ))^1*((479/800:ℝ)-r)^7 + (505783344687681532854970368/12457785357953028025:ℝ)*(r-(637/1200:ℝ))^2*((479/800:ℝ)-r)^6 + (586736977997481131452704768/12457785357953028025:ℝ)*(r-(637/1200:ℝ))^3*((479/800:ℝ)-r)^5 + (76177094565115399735178496/2491557071590605605:ℝ)*(r-(637/1200:ℝ))^4*((479/800:ℝ)-r)^4 + (222056334656784469020436992/12457785357953028025:ℝ)*(r-(637/1200:ℝ))^5*((479/800:ℝ)-r)^3 + (200800305393913204441746048/12457785357953028025:ℝ)*(r-(637/1200:ℝ))^6*((479/800:ℝ)-r)^2 + (130431517445084725503713664/12457785357953028025:ℝ)*(r-(637/1200:ℝ))^7*((479/800:ℝ)-r)^1 + (32741625248235314790977304/12457785357953028025:ℝ)*(r-(637/1200:ℝ))^8*((479/800:ℝ)-r)^0 := by unfold quartic; ring
  have hp : 0≤r-(8/3:ℝ)*quartic r*(1-quartic r)-(1/10000000:ℝ) := by rw [he]; positivity
  linarith only [hp]

lemma quartic_cap_poly_2 {r:ℝ} (hr:r∈Icc (479/800:ℝ) (2/3:ℝ)) :
    (8/3:ℝ)*quartic r*(1-quartic r)≤r := by
  have hl : 0≤r-(479/800:ℝ) := sub_nonneg.mpr hr.1
  have hu : 0≤(2/3:ℝ)-r := sub_nonneg.mpr hr.2
  have he : r-(8/3:ℝ)*quartic r*(1-quartic r)-(1/10000000:ℝ) =
    (32741625248235314790977304/12457785357953028025:ℝ)*(r-(479/800:ℝ))^0*((2/3:ℝ)-r)^8 + (15737379461067212446076928/498311414318121121:ℝ)*(r-(479/800:ℝ))^1*((2/3:ℝ)-r)^7 + (81672843558603292159168512/498311414318121121:ℝ)*(r-(479/800:ℝ))^2*((2/3:ℝ)-r)^6 + (235981919035699122733056000/498311414318121121:ℝ)*(r-(479/800:ℝ))^3*((2/3:ℝ)-r)^5 + (414325433731694159993241600/498311414318121121:ℝ)*(r-(479/800:ℝ))^4*((2/3:ℝ)-r)^4 + (453499398278084265246720000/498311414318121121:ℝ)*(r-(479/800:ℝ))^5*((2/3:ℝ)-r)^3 + (303087682730152112947200000/498311414318121121:ℝ)*(r-(479/800:ℝ))^6*((2/3:ℝ)-r)^2 + (113422069316840325120000000/498311414318121121:ℝ)*(r-(479/800:ℝ))^7*((2/3:ℝ)-r)^1 + (18245141539690905600000000/498311414318121121:ℝ)*(r-(479/800:ℝ))^8*((2/3:ℝ)-r)^0 := by unfold quartic; ring
  have hp : 0≤r-(8/3:ℝ)*quartic r*(1-quartic r)-(1/10000000:ℝ) := by rw [he]; positivity
  linarith only [hp]

lemma quartic_from_cap {r P:ℝ} (hr:r∈Icc (79/200:ℝ) (2/3:ℝ)) (hP:P≤1/2)
    (hcap:r≤(8/3:ℝ)*P*(1-P)) : quartic r≤P := by
  have hr0 : 0≤r := by linarith only [hr.1]
  have h2 : r^2≤(2/3:ℝ)^2 := (sq_le_sq₀ hr0 (by norm_num)).mpr hr.2
  have h4 : r^4≤(2/3:ℝ)^4 := pow_le_pow_left₀ hr0 hr.2 4
  apply cap_envelope hP (by unfold quartic; nlinarith only [h2,h4]) hcap

  by_cases h0 : r≤(637/1200:ℝ)
  · exact quartic_cap_poly_0 ⟨by linarith only [hr.1],h0⟩
  by_cases h1 : r≤(479/800:ℝ)
  · exact quartic_cap_poly_1 ⟨by linarith only [h0],h1⟩
  exact quartic_cap_poly_2 ⟨by linarith only [h1],hr.2⟩

lemma large_cap_poly_0 {r:ℝ} (hr:r∈Icc (21/40:ℝ) (2/3:ℝ)) :
    (8/3:ℝ)*large r*(1-large r)≤r := by
  have hl : 0≤r-(21/40:ℝ) := sub_nonneg.mpr hr.1
  have hu : 0≤(2/3:ℝ)-r := sub_nonneg.mpr hr.2
  have he : r-(8/3:ℝ)*large r*(1-large r)-(1/10000000:ℝ) =
    (22643631/20880250:ℝ)*(r-(21/40:ℝ))^0*((2/3:ℝ)-r)^4 + (631811232/10440125:ℝ)*(r-(21/40:ℝ))^1*((2/3:ℝ)-r)^3 + (2057374848/10440125:ℝ)*(r-(21/40:ℝ))^2*((2/3:ℝ)-r)^2 + (2438965632/10440125:ℝ)*(r-(21/40:ℝ))^3*((2/3:ℝ)-r)^1 + (3041528224/31320375:ℝ)*(r-(21/40:ℝ))^4*((2/3:ℝ)-r)^0 := by unfold large; ring
  have hp : 0≤r-(8/3:ℝ)*large r*(1-large r)-(1/10000000:ℝ) := by rw [he]; positivity
  linarith only [hp]

lemma large_from_cap {r P:ℝ} (hr:r∈Icc (21/40:ℝ) (2/3:ℝ)) (hP:P≤1/2)
    (hcap:r≤(8/3:ℝ)*P*(1-P)) : large r≤P := by
  have hr0 : 0≤r := by linarith only [hr.1]
  have h2 : r^2≤(2/3:ℝ)^2 := (sq_le_sq₀ hr0 (by norm_num)).mpr hr.2
  have h4 : r^4≤(2/3:ℝ)^4 := pow_le_pow_left₀ hr0 hr.2 4
  apply cap_envelope hP (by unfold large; nlinarith only [h2,h4]) hcap

  exact large_cap_poly_0 ⟨by linarith only [hr.1],hr.2⟩

end GaussianPropeller.FourCertificates

end OAI
end

section
-- module Solutions.OAIQW_GaussianPropeller.FourAlgebra
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

namespace GaussianPropeller.FourAlgebra
open scoped RealInnerProductSpace

lemma quartic_positive {t L c₀ c₁ c₂ c₄:ℝ} (ht:0≤t) (htL:t≤L) (hL:0<L)
    (hc₄:0≤c₄) (hconc:c₂+3*c₄*L^2≤0) (hc₀:0<c₀)
    (hend:0<c₀+c₁*L+c₂*L^2+c₄*L^4) : 0<c₀+c₁*t+c₂*t^2+c₄*t^4 := by
  have ht2 : t^2≤L^2 := (sq_le_sq₀ ht hL.le).mpr htL
  have htL' : L*t≤L^2 := by nlinarith only [mul_le_mul_of_nonneg_left htL hL.le]
  have hb : 0≤-c₂-c₄*(t^2+L*t+L^2) := by
    have hh := mul_le_mul_of_nonneg_left (show t^2+L*t+L^2≤3*L^2 by linarith only [ht2,htL']) hc₄
    linarith only [hh,hconc]
  have hp:=mul_nonneg (mul_nonneg ht (sub_nonneg.mpr htL)) hb
  have hid : L*(c₀+c₁*t+c₂*t^2+c₄*t^4) =
      (L-t)*c₀+t*(c₀+c₁*L+c₂*L^2+c₄*L^4)+L*(t*(L-t)*(-c₂-c₄*(t^2+L*t+L^2))) := by ring
  have hlin : 0<(L-t)*c₀+t*(c₀+c₁*L+c₂*L^2+c₄*L^4) := by
    by_cases htz:t=0
    · subst t; simpa using mul_pos hL hc₀
    · exact add_pos_of_nonneg_of_pos (mul_nonneg (sub_nonneg.mpr htL) hc₀.le)
        (mul_pos (lt_of_le_of_ne ht (Ne.symm htz)) hend)
  have hm:=mul_nonneg hL.le hp
  nlinarith only [hid,hlin,hm,hL]

lemma small_numeric_one {t:ℝ} (ht:t∈Set.Icc (0:ℝ) (39/250:ℝ)) :
    4*(150/157:ℝ)^2*t^2*(13/10:ℝ)^4 <
      (1-2*t^2)^2-(10/3:ℝ)*((10003/40000:ℝ)-(83/200:ℝ)*t+(81/250:ℝ)*t^2) := by
  have hh:=quartic_positive (c₀:=(1997/12000:ℝ)) (c₁:=(83/60:ℝ))
    (c₂:=-(9556648/616225:ℝ)) (c₄:=4) ht.1 ht.2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  nlinarith only [hh]

lemma small_numeric_two {t:ℝ} (ht:t∈Set.Icc (0:ℝ) (39/250:ℝ)) :
    4*(150/157:ℝ)^2*t^2*(4/3:ℝ)^4 <
      (1-(14/9:ℝ)*t^2)^2-(10/3:ℝ)*((10003/40000:ℝ)-(83/200:ℝ)*t+(81/250:ℝ)*t^2) := by
  have hh:=quartic_positive (c₀:=(1997/12000:ℝ)) (c₁:=(83/60:ℝ))
    (c₂:=-(87244007/5546025:ℝ)) (c₄:=(196/81:ℝ)) ht.1 ht.2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  nlinarith only [hh]

lemma pair_product {a b B:ℝ} (ha:0≤a) (hb:0≤b) (hab:a+b≤B) :
    (1+a)^2*(1+b)^2≤(1+B/2)^4 := by
  have hB:0≤B := (add_nonneg ha hb).trans hab
  have hh : (1+a)*(1+b)≤(1+B/2)^2 := by
    have hs:(a+b)^2≤B^2 := (sq_le_sq₀ (add_nonneg ha hb) hB).mpr hab
    nlinarith only [hs,hab,sq_nonneg (a-b)]
  have hq:((1+a)*(1+b))^2≤((1+B/2)^2)^2 :=
    (sq_le_sq₀ (by positivity) (sq_nonneg _)).mpr hh
  nlinarith only [hq]

lemma small_core {t a b c H V D:ℝ} (ht:t∈Set.Icc (0:ℝ) (39/250:ℝ))
    (ha:0≤a) (hb:0≤b) (hc:0≤c) (hs:a+b+c=1) (hac:a≤c) (hbc:b≤c)
    (hH:H=1-t^2-(a^2+b^2+c^2)*t^2)
    (hV:(3/5:ℝ)*V≤(10003/40000:ℝ)-(83/200:ℝ)*t+(81/250:ℝ)*t^2)
    (hD:4*D=H^2-2*V)
    (hpair:D≤(3/Real.pi)^2*t^2*(1+a)^2*(1+b)^2) : False := by
  have hk : (3/Real.pi)^2≤(150/157:ℝ)^2 := by
    apply (sq_le_sq₀ (by positivity) (by norm_num)).mpr
    rw [div_le_iff₀ Real.pi_pos]
    have hp:=Real.pi_gt_d2
    linarith only [hp]
  have hab : a+b≤2/3 := by linarith only [hac,hbc,hs]
  have ht2 : t^2≤(39/250:ℝ)^2 := (sq_le_sq₀ ht.1 (by norm_num)).mpr ht.2
  have hcoef : a^2+b^2+c^2≤1 := by
    nlinarith only [hs,mul_nonneg ha hb,mul_nonneg ha hc,mul_nonneg hb hc]
  have hpair' : D≤(150/157:ℝ)^2*t^2*(1+a)^2*(1+b)^2 := hpair.trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hk (sq_nonneg t)) (sq_nonneg (1+a))) (sq_nonneg (1+b)))
  by_cases hsmall : a+b≤3/5
  · have hprod := pair_product ha hb hsmall
    have hd : D≤(150/157:ℝ)^2*t^2*(13/10:ℝ)^4 := by
      have hh:=mul_le_mul_of_nonneg_left hprod (mul_nonneg (sq_nonneg (150/157:ℝ)) (sq_nonneg t))
      norm_num at hh
      nlinarith only [hpair',hh]
    have hl : 1-2*t^2≤H := by
      have hh:=mul_le_mul_of_nonneg_right hcoef (sq_nonneg t)
      nlinarith only [hh,hH]
    have hl0 : 0≤1-2*t^2 := by nlinarith only [ht2]
    have hsq : (1-2*t^2)^2≤H^2 := (sq_le_sq₀ hl0 (hl0.trans hl)).mpr hl
    have hn:=small_numeric_one ht
    nlinarith only [hV,hD,hd,hsq,hn]
  · have hablo : 3/5≤a+b := (lt_of_not_ge hsmall).le
    have hcoef' : a^2+b^2+c^2≤5/9 := by
      have hh:=mul_nonneg (sub_nonneg.mpr hab) (show 0≤2*(a+b)-2/3 by linarith only [hablo])
      nlinarith only [hs,hh,mul_nonneg ha hb]
    have hprod := pair_product ha hb hab
    have hd : D≤(150/157:ℝ)^2*t^2*(4/3:ℝ)^4 := by
      have hh:=mul_le_mul_of_nonneg_left hprod (mul_nonneg (sq_nonneg (150/157:ℝ)) (sq_nonneg t))
      norm_num at hh
      nlinarith only [hpair',hh]
    have hl : 1-(14/9:ℝ)*t^2≤H := by
      have hh:=mul_le_mul_of_nonneg_right hcoef' (sq_nonneg t)
      nlinarith only [hh,hH]
    have hl0 : 0≤1-(14/9:ℝ)*t^2 := by nlinarith only [ht2]
    have hsq : (1-(14/9:ℝ)*t^2)^2≤H^2 := (sq_le_sq₀ hl0 (hl0.trans hl)).mpr hl
    have hn:=small_numeric_two ht
    nlinarith only [hV,hD,hd,hsq,hn]

lemma small_exclusion {t a b c H V D:ℝ} (ht:t∈Set.Icc (0:ℝ) (39/250:ℝ))
    (ha:0≤a) (hb:0≤b) (hc:0≤c) (hs:a+b+c=1)
    (hH:H=1-t^2-(a^2+b^2+c^2)*t^2)
    (hV:(3/5:ℝ)*V≤(10003/40000:ℝ)-(83/200:ℝ)*t+(81/250:ℝ)*t^2)
    (hD:4*D=H^2-2*V)
    (hab:D≤(3/Real.pi)^2*t^2*(1+a)^2*(1+b)^2)
    (hac:D≤(3/Real.pi)^2*t^2*(1+a)^2*(1+c)^2)
    (hbc:D≤(3/Real.pi)^2*t^2*(1+b)^2*(1+c)^2) : False := by
  by_cases hac':a≤c
  · by_cases hbc':b≤c
    · exact small_core ht ha hb hc hs hac' hbc' hH hV hD hab
    · apply small_core (a:=a) (b:=c) (c:=b) ht ha hc hb (by linarith only [hs])
        (hac'.trans (le_of_not_ge hbc')) (le_of_not_ge hbc')
        (by nlinarith only [hH]) hV hD hac
  · by_cases hba:b≤a
    · exact small_core (a:=b) (b:=c) (c:=a) ht hb hc ha (by linarith only [hs]) hba
        (le_of_not_ge hac') (by nlinarith only [hH]) hV hD hbc
    · exact small_core (a:=a) (b:=c) (c:=b) ht ha hc hb (by linarith only [hs])
        (le_of_not_ge hba) ((le_of_not_ge hac').trans (le_of_not_ge hba))
        (by nlinarith only [hH]) hV hD hac

end GaussianPropeller.FourAlgebra

end OAI
end

section
-- module Solutions.OAIQW_GaussianPropeller.FourCells
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
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal RealInnerProductSpace

namespace GaussianPropeller.Reduction
open FourCertificates ProbabilityBounds
open scoped RealInnerProductSpace
variable {d:ℕ}

lemma triangle_gram (u v w : Space d) (hs:u+v+w=0) :
    let D:=‖u‖^2*‖v‖^2-⟪u,v⟫^2
    D=‖u‖^2*‖w‖^2-⟪u,w⟫^2 ∧ D=‖v‖^2*‖w‖^2-⟪v,w⟫^2 ∧
    4*D=(‖u‖^2+‖v‖^2+‖w‖^2)^2-2*(‖u‖^4+‖v‖^4+‖w‖^4) := by
  have hw:w=-(u+v) := eq_neg_of_add_eq_zero_left (by simpa only [add_comm] using hs)
  subst w
  simp only [norm_neg,norm_add_sq_real,inner_neg_right,inner_add_right,real_inner_self_eq_norm_sq,
    real_inner_comm u v]
  constructor
  · ring
  constructor
  · ring
  · have h4:‖u+v‖^4=(‖u‖^2+‖v‖^2+2*⟪u,v⟫)^2 := by rw [show (4:ℕ)=2*2 by rfl,pow_mul,norm_add_sq_real]; ring
    rw [h4]
    ring

lemma residual_fourth_le (x y:Space d) (hx:x≠0) :
    ‖residualVector x y‖^4≤‖y‖^4 := by
  have h:=residual_norm_sq (z:=x) (y:=y) hx
  have hle:‖residualVector x y‖^2≤‖y‖^2 := by nlinarith only [h,mul_nonneg (sq_nonneg (residualCoefficient x y)) (sq_nonneg ‖x‖)]
  have hh: (‖residualVector x y‖^2)^2≤(‖y‖^2)^2 := (sq_le_sq₀ (sq_nonneg _) (sq_nonneg _)).mpr hle
  simpa only [←pow_mul] using hh

lemma four_incompatibility (z:Fin 4→Space d) (P:Fin 4→ℝ)
    (hsum:∑ j,z j=0) (hnorm:∑ j,‖z j‖^2=1)
    (hpos:∀ j,z j≠0) (horder:Antitone (fun j=>‖z j‖))
    (hneg:Pairwise (fun j l=>⟪z j,z l⟫<0)) (hcap:∀ j,‖z j‖≤2/3)
    (hprob:∑ j,P j=1) (hPh:∀ j,P j≤1/2)
    (hcap3:∀ j,‖z j‖≤(8/3:ℝ)*P j*(1-P j))
    (hlin:∀ j,0.415*‖z j‖+0.15*‖z j‖^2≤P j)
    (hloss:∀ j,∃ x≥(0:ℝ),p x=P j ∧
      (9/(8*Real.pi))*‖z j‖^2/(1+Real.sqrt (1-(4/3:ℝ)*‖z j‖^2))≤loss x)
    (hpair:∀ i j l, i≠j → i≠l →
      ‖residualVector (z i) (z j)‖^2*‖residualVector (z i) (z l)‖^2-
      ⟪residualVector (z i) (z j),residualVector (z i) (z l)⟫^2≤
      (3/Real.pi)^2*‖z i‖^2*(1+residualCoefficient (z i) (z j))^2*
      (1+residualCoefficient (z i) (z l))^2) : False := by
  have hn:‖z 0‖^2+‖z 1‖^2+‖z 2‖^2+‖z 3‖^2=1 := by
    simpa [Fin.sum_univ_succ,add_assoc] using hnorm
  have hp:P 0+P 1+P 2+P 3=1 := by simpa [Fin.sum_univ_succ,add_assoc] using hprob
  have hq:∀ j,‖z j‖^2≤(2/3:ℝ)^2 := fun j=>(sq_le_sq₀ (norm_nonneg _) (by norm_num)).mpr (hcap j)
  have hquartic:∀ j, (147/500:ℝ)≤‖z j‖ → quartic ‖z j‖≤P j := by
    intro j hj
    by_cases ht:‖z j‖≤79/200
    · obtain ⟨x,hx,hpx,hl⟩:=hloss j
      rw [←hpx]
      exact (quartic_of_loss ⟨hj,ht⟩ hx hl).le
    · exact quartic_from_cap ⟨(le_of_not_ge ht),(hcap j)⟩ (hPh j) (hcap3 j)
  by_cases ht:‖z 3‖≤39/250
  · have ht2:‖z 3‖^2≤(39/250:ℝ)^2 := (sq_le_sq₀ (norm_nonneg _) (by norm_num)).mpr ht
    have h0:(147/500:ℝ)≤‖z 0‖ := by nlinarith only [hn,hq 1,hq 2,ht2,norm_nonneg (z 0)]
    have h1:(147/500:ℝ)≤‖z 1‖ := by nlinarith only [hn,hq 0,hq 2,ht2,norm_nonneg (z 1)]
    have h2:(147/500:ℝ)≤‖z 2‖ := by nlinarith only [hn,hq 0,hq 1,ht2,norm_nonneg (z 2)]
    let a:=residualCoefficient (z 3) (z 0)
    let b:=residualCoefficient (z 3) (z 1)
    let c:=residualCoefficient (z 3) (z 2)
    let u:=residualVector (z 3) (z 0)
    let v:=residualVector (z 3) (z 1)
    let w:=residualVector (z 3) (z 2)
    have ha:0≤a := (residualCoefficient_pos (hneg (by decide : (3:Fin 4)≠0))).le
    have hb:0≤b := (residualCoefficient_pos (hneg (by decide : (3:Fin 4)≠1))).le
    have hc:0≤c := (residualCoefficient_pos (hneg (by decide : (3:Fin 4)≠2))).le
    have habc:a+b+c=1 := by
      have hh:=residual_coefficient_sum z hsum 3 (hpos 3)
      have he:(Finset.univ.erase (3:Fin 4))={0,1,2} := by decide
      rw [he] at hh
      simpa [a,b,c,Finset.sum_insert,add_assoc] using hh
    have hs:u+v+w=0 := by
      have hh:=residual_sum z hsum 3 (hpos 3)
      have he:(Finset.univ.erase (3:Fin 4))={0,1,2} := by decide
      rw [he] at hh
      simpa [u,v,w,Finset.sum_insert,add_assoc] using hh
    obtain ⟨hD1,hD2,hD3⟩:=triangle_gram u v w hs
    have hu:‖u‖^2=‖z 0‖^2-a^2*‖z 3‖^2 := residual_norm_sq (hpos 3)
    have hv:‖v‖^2=‖z 1‖^2-b^2*‖z 3‖^2 := residual_norm_sq (hpos 3)
    have hw:‖w‖^2=‖z 2‖^2-c^2*‖z 3‖^2 := residual_norm_sq (hpos 3)
    have hH:‖u‖^2+‖v‖^2+‖w‖^2=1-‖z 3‖^2-(a^2+b^2+c^2)*‖z 3‖^2 := by
      nlinarith only [hu,hv,hw,hn]
    have he0:=hquartic 0 h0
    have he1:=hquartic 1 h1
    have he2:=hquartic 2 h2
    unfold quartic at he0 he1 he2
    have hV:(3/5:ℝ)*(‖u‖^4+‖v‖^4+‖w‖^4)≤(10003/40000:ℝ)-(83/200:ℝ)*‖z 3‖+(81/250:ℝ)*‖z 3‖^2 := by
      nlinarith only [he0,he1,he2,hlin 3,hn,hp,
        residual_fourth_le (z 3) (z 0) (hpos 3),residual_fourth_le (z 3) (z 1) (hpos 3),residual_fourth_le (z 3) (z 2) (hpos 3)]
    apply FourAlgebra.small_exclusion ⟨norm_nonneg _,ht⟩ ha hb hc habc hH hV hD3
    · exact hpair 3 0 1 (by decide) (by decide)
    · rw [hD1]; exact hpair 3 0 2 (by decide) (by decide)
    · rw [hD2]; exact hpair 3 1 2 (by decide) (by decide)
  have htlo:(39/250:ℝ)≤‖z 3‖ := (lt_of_not_ge ht).le
  have hmin:∀ j, ‖z 3‖≤‖z j‖ := fun j=>horder (show j≤3 by omega)
  have haff:∀ j,affine ‖z j‖≤P j := fun j=> affine_from_cap ⟨htlo.trans (hmin j),hcap j⟩ (hPh j) (hcap3 j)
  have ha0:=haff 0; have ha1:=haff 1; have ha2:=haff 2
  unfold affine at ha0 ha1 ha2
  by_cases ht18:‖z 3‖≤9/50
  · obtain ⟨x,hx,hpx,hl⟩:=hloss 3
    have hsmall:=small_of_loss ⟨htlo,ht18⟩ hx hl
    rw [hpx] at hsmall
    unfold small at hsmall
    have hprod:=mul_nonneg (sub_nonneg.mpr htlo) (sub_nonneg.mpr ht18)
    nlinarith only [ha0,ha1,ha2,hsmall,hn,hp,hprod,htlo,ht18]
  by_cases ht40:‖z 3‖≤2/5
  · have hlo:(9/50:ℝ)≤‖z 3‖ := (lt_of_not_ge ht18).le
    have hprod:=mul_nonneg (sub_nonneg.mpr hlo) (sub_nonneg.mpr ht40)
    nlinarith only [ha0,ha1,ha2,hlin 3,hn,hp,hprod,hlo,ht40]
  have hlarge:∀ j,large ‖z j‖≤P j := by
    intro j
    have hj:(2/5:ℝ)≤‖z j‖ := (le_of_not_ge ht40).trans (hmin j)
    by_cases hj525:‖z j‖≤21/40
    · obtain ⟨x,hx,hpx,hl⟩:=hloss j
      rw [←hpx]
      exact (large_of_loss ⟨hj,hj525⟩ hx hl).le
    · exact large_from_cap ⟨le_of_not_ge hj525,hcap j⟩ (hPh j) (hcap3 j)
  have hl0:=hlarge 0; have hl1:=hlarge 1; have hl2:=hlarge 2; have hl3:=hlarge 3
  unfold large at hl0 hl1 hl2 hl3
  nlinarith only [hl0,hl1,hl2,hl3,hn,hp]

end GaussianPropeller.Reduction

end OAI
end

section
-- module Solutions.OAIQW_GaussianPropeller.Elimination
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
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal RealInnerProductSpace

namespace GaussianPropeller.Reduction.Configuration
variable {d k:ℕ}

lemma impossible_four_oai (D:Configuration d 4) : False :=
  four_incompatibility D.z D.P D.zero D.norm D.pos D.order D.obtuse D.cap
    D.probability D.half (D.cap3 rfl) D.linear (D.loss4 rfl) D.pair

end GaussianPropeller.Reduction.Configuration

end OAI
end

theorem solution : type_of% @OAI.GaussianPropeller.Reduction.Configuration.impossible_four_oai := @OAI.GaussianPropeller.Reduction.Configuration.impossible_four_oai
