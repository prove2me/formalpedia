-- Prove2me | solution 1 for OAI.PrimeDegreePackets.AnalyticGrowth.hasSum_realZeroPole
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T06:31:11.036478+00:00
-- url     : https://prove2.me/submissions/4ccfc3a4-c1ff-47f3-b5e6-899fa96d1b6e

import Mathlib
import Definitions.Def_OAIQ244Duke012

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_AnalyticLogarithms
attribute [-instance] _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal
open MeasureTheory Filter Set Module
universe u
open scoped TensorProduct
open Set Module
open MeasureTheory Set
open scoped ENNReal
open IsDiscreteValuationRing IsLocalRing
open scoped ENNReal BigOperators
open MeasureTheory Set IsDiscreteValuationRing
open Filter
open scoped BigOperators Topology
open NumberField
open scoped NumberField nonZeroDivisors
open scoped BigOperators ArithmeticFunction.zeta
open Finset
open scoped BigOperators Classical ArithmeticFunction.Moebius
open Finset Nat ArithmeticFunction BoundingSieve
open scoped BigOperators Classical
open Finset Nat
open scoped BigOperators
open Filter Topology
open scoped nonZeroDivisors
open Ideal NumberField Finset UniqueFactorizationMonoid
open Filter Set Topology NumberField
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace
open Filter Set Topology
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors RealInnerProductSpace
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace Matrix
open MeasureTheory Filter Set Module TopologicalSpace
open MeasureTheory Filter Set
open scoped BigOperators Topology ENNReal
open scoped BigOperators Topology ENNReal Classical
open scoped BigOperators Topology ENNReal Classical Matrix Matrix.Norms.Elementwise
open scoped BigOperators Topology ENNReal Classical Matrix Matrix.Norms.Elementwise Pointwise
open scoped BigOperators Topology ENNReal Classical Matrix Pointwise
open scoped BigOperators Topology ENNReal Classical Matrix
open MeasureTheory ProbabilityTheory Filter Set
open Set Filter
open scoped Topology
open scoped Classical
open scoped Topology ENNReal Classical
open scoped ENNReal Classical
open MeasureTheory Set Topology UniformSpace TopologicalSpace
open scoped ENNReal Topology
open MeasureTheory Filter Set Matrix
open scoped Topology Classical
open scoped Matrix Classical
open scoped Topology Classical Matrix
open scoped Classical Pointwise
open scoped Topology Classical ENNReal
open scoped Matrix Topology Classical
open MeasureTheory ProbabilityTheory Set Filter
open scoped Matrix Topology Classical ENNReal ProbabilityTheory
open scoped ENNReal ProbabilityTheory
open Set Filter Topology
open Set Filter Topology MeasureTheory
open MeasureTheory Set Filter Topology
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped Matrix ENNReal NNReal ProbabilityTheory
open MeasureTheory
open scoped BigOperators ENNReal
open NumberField Finset
open NumberField Filter Set Topology
open MeasureTheory ProbabilityTheory Matrix
open scoped Classical BigOperators ENNReal
open MeasureTheory Set Filter Topology Module
open scoped BigOperators SchwartzMap
open MeasureTheory Set Filter Topology Module WithLp
open scoped BigOperators SchwartzMap ZeroAtInfty
open scoped FourierTransform
open scoped BigOperators SchwartzMap FourierTransform
open scoped BigOperators FourierTransform
open MeasureTheory Set Filter Topology Module WithLp Asymptotics
open Module WithLp MeasureTheory
open scoped BigOperators Matrix
open Module MeasureTheory
open MeasureTheory Module WithLp
open scoped BigOperators NumberField nonZeroDivisors ENNReal
open Complex Set Metric Filter
namespace PrimeDegreePackets.AnalyticGrowth

 

lemma exists_disk_logarithm {g : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (hg : DifferentiableOn ℂ g (ball 0 R))
    (hzero : ∀ z ∈ ball 0 R, g z ≠ 0) :
    ∃ h : ℂ → ℂ, h 0 = 0 ∧
      (∀ z ∈ ball 0 R, HasDerivAt h (logDeriv g z) z) ∧
      (∀ z ∈ ball 0 R, Complex.exp (h z) = g z / g 0) := by
  have hga : AnalyticOnNhd ℂ g (ball 0 R) := hg.analyticOnNhd isOpen_ball
  have hld : DifferentiableOn ℂ (logDeriv g) (ball 0 R) := by
    intro z hz
    exact (((hga z hz).deriv.differentiableAt).div
      ((hg z hz).differentiableAt (isOpen_ball.mem_nhds hz)) (hzero z hz)).differentiableWithinAt
  obtain ⟨h,h0,hh⟩ := hld.isExactOn_ball.with_val_at 0 0
  refine ⟨h,h0,hh,?_⟩
  have HD : ∀ z ∈ ball 0 R,
      HasDerivAt (fun z => g z * Complex.exp (-h z)) 0 z := by
    intro z hz
    have H := ((hg z hz).differentiableAt (isOpen_ball.mem_nhds hz)).hasDerivAt.mul ((hh z hz).neg.cexp)
    apply H.congr_deriv
    dsimp only [Pi.neg_apply, logDeriv_apply]
    field_simp [hzero z hz]
    ring
  have HE : EqOn (fun z => g z * Complex.exp (-h z)) (fun _ => g 0) (ball 0 R) := by
    apply isOpen_ball.eqOn_of_deriv_eq (convex_ball (0:ℂ) R).isPreconnected
      (fun z hz => (HD z hz).differentiableAt.differentiableWithinAt)
      (differentiableOn_const _) (fun z hz => by rw [(HD z hz).deriv, deriv_const])
      (mem_ball_self hR)
    simp [h0]
  intro z hz
  have H := HE hz
  rw [eq_div_iff (hzero 0 (mem_ball_self hR))]
  have He : Complex.exp (-h z) * Complex.exp (h z) = 1 := by
    rw [← Complex.exp_add, neg_add_cancel, Complex.exp_zero]
  have HH := congrArg (fun w => w*Complex.exp (h z)) H
  rw [mul_assoc, He, mul_one] at HH
  exact (mul_comm _ _).trans HH.symm

lemma disk_logarithm_re {g h : ℂ → ℂ} {z : ℂ}
    (hzero : g 0 ≠ 0) (hz : Complex.exp (h z) = g z / g 0) :
    (h z).re = Real.log ‖g z‖ - Real.log ‖g 0‖ := by
  have Hg : g z ≠ 0 := by
    intro H
    rw [H, zero_div] at hz
    exact Complex.exp_ne_zero _ hz
  have H := congrArg (fun w : ℂ => Real.log ‖w‖) hz
  simpa only [Complex.norm_exp, Real.log_exp, norm_div,
    Real.log_div (norm_ne_zero_iff.mpr Hg) (norm_ne_zero_iff.mpr hzero)] using H

end PrimeDegreePackets.AnalyticGrowth


namespace PrimeDegreePackets.AnalyticGrowth

 

lemma deriv_sub_le_of_re_le {h : ℂ → ℂ} {R M : ℝ} (hR : 0 < R) (hM : 0 < M)
    (hh : DifferentiableOn ℂ h (ball 0 R)) (h0 : h 0 = 0)
    (hreal : ∀ z ∈ ball 0 R, (h z).re ≤ M)
    {z w : ℂ} (hz : z ∈ Metric.ball 0 (R/4)) (hw : w ∈ Metric.ball 0 (R/4)) :
    ‖deriv h z - deriv h w‖ ≤ (64*M/R^2)*‖z-w‖ := by
  have HR4 : 0 < R/4 := by positivity
  have HE : ∀ a ∈ Metric.ball (0:ℂ) (R/4),
      closedBall a (R/4) ⊆ ball (0:ℂ) R := by
    intro a ha b hb
    rw [mem_ball_zero_iff] at ha ⊢
    have HB := norm_le_norm_sub_add b a
    have HH : ‖b-a‖ ≤ R/4 := by simpa [dist_eq_norm] using hb
    linarith
  have HB : ∀ a ∈ Metric.ball (0:ℂ) (R/4), ∀ b ∈ sphere a (R/4), ‖h b‖ ≤ 2*M := by
    intro a ha b hb
    have Hba : ‖b-a‖ = R/4 := by simpa [dist_eq_norm] using hb
    have Ha : ‖a‖ < R/4 := mem_ball_zero_iff.mp ha
    have Hb : ‖b‖ < R/2 := by linarith [norm_le_norm_sub_add b a]
    have HBR : b ∈ ball (0:ℂ) R := mem_ball_zero_iff.mpr (by linarith)
    have H := Complex.borelCaratheodory_zero hM hh (fun x hx => hreal x hx) hR HBR h0
    apply H.trans
    rw [div_le_iff₀ (by linarith : 0 < R-‖b‖)]
    nlinarith
  have H2 : ∀ a ∈ Metric.ball (0:ℂ) (R/4),
      ‖deriv (deriv h) a‖ ≤ 64*M/R^2 := by
    intro a ha
    have H := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le
      2 HR4 (hh.diffContOnCl_ball (HE a ha)) (HB a ha)
    have HN : (2:ℝ)*(2*M)/(R/4)^2 = 64*M/R^2 := by ring
    simpa only [iteratedDeriv_succ, iteratedDeriv_zero, Nat.factorial_two,
      Nat.cast_ofNat, HN] using H
  apply Convex.norm_image_sub_le_of_norm_deriv_le _ H2 (convex_ball (0:ℂ) (R/4)) hw hz
  intro a ha
  apply ((hh.analyticOnNhd isOpen_ball) a (HE a ha (mem_closedBall_self HR4.le))).deriv.differentiableAt

 

lemma logDeriv_sub_le_of_log_norm_le {g : ℂ → ℂ} {R M : ℝ}
    (hR : 0 < R) (hM : 0 < M) (hg : DifferentiableOn ℂ g (ball 0 R))
    (hzero : ∀ z ∈ ball 0 R, g z ≠ 0)
    (hbound : ∀ z ∈ ball 0 R, Real.log ‖g z‖ - Real.log ‖g 0‖ ≤ M)
    {z w : ℂ} (hz : z ∈ Metric.ball 0 (R/4)) (hw : w ∈ Metric.ball 0 (R/4)) :
    ‖logDeriv g z - logDeriv g w‖ ≤ (64*M/R^2)*‖z-w‖ := by
  obtain ⟨h,h0,hh,HE⟩ := exists_disk_logarithm hR hg hzero
  have hh' : DifferentiableOn ℂ h (ball 0 R) :=
    fun z hz => (hh z hz).differentiableAt.differentiableWithinAt
  have H := deriv_sub_le_of_re_le hR hM hh' h0 (fun z hz => by
    rw [disk_logarithm_re (hzero 0 (mem_ball_self hR)) (HE z hz)]
    exact hbound z hz) hz hw
  have hs : Metric.ball (0:ℂ) (R/4) ⊆ ball 0 R := ball_subset_ball (by linarith)
  rwa [(hh z (hs hz)).deriv, (hh w (hs hw)).deriv] at H

end PrimeDegreePackets.AnalyticGrowth

open Complex Set Metric Filter MeromorphicOn
namespace PrimeDegreePackets.AnalyticGrowth

lemma entire_order_ne_top {f : ℂ → ℂ} (hf : Differentiable ℂ f) (h0 : f 0 ≠ 0)
    (z : ℂ) : meromorphicOrderAt f z ≠ ⊤ := by
  have HM : Meromorphic f := fun z => (hf.analyticAt z).meromorphicAt
  apply HM.exists_meromorphicOrderAt_ne_top_iff_forall.mp
  use 0
  rw [(hf.analyticAt 0).meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mpr h0]
  simp

lemma divisor_sphere_eq_zero {f : ℂ → ℂ} {R : ℝ} (hf : Differentiable ℂ f)
    (hS : ∀ z ∈ sphere (0:ℂ) R, f z ≠ 0) : divisor f (sphere 0 R) = 0 := by
  ext z
  by_cases hz : z ∈ sphere (0:ℂ) R
  · rw [MeromorphicOn.divisor_apply (fun z _ => (hf.analyticAt z).meromorphicAt) hz,
      (hf.analyticAt z).meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mpr (hS z hz)]
    simp
  · simp only [divisor_def, hz, and_false, ite_false, if_false, Function.locallyFinsuppWithin.coe_zero, Pi.zero_apply]

lemma exists_entire_ecanonicalDecomp {f : ℂ → ℂ} {R : ℝ}
    (hf : Differentiable ℂ f) (h0 : f 0 ≠ 0) :
    ∃ g, ECanonicalDecomp f g R := by
  exact MeromorphicOn.exists_ecanonicalDecomp (fun z _ => (hf.analyticAt z).meromorphicAt)
    (fun z => entire_order_ne_top hf h0 z)

lemma ecanonical_log_norm_eq_on_sphere {f g : ℂ → ℂ} {R : ℝ}
    (D : ECanonicalDecomp f g R) (hf : Differentiable ℂ f) (hR : 0 < R)
    (hS : ∀ z ∈ sphere (0:ℂ) R, f z ≠ 0) {z : ℂ} (hz : z ∈ sphere (0:ℂ) R) :
    Real.log ‖g z‖ = Real.log ‖f z‖ := by
  rw [D.log_norm_eq (sphere_subset_closedBall hz)
    ((hf.analyticAt z).meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mpr (hS z hz)) hR,
    (hf.analyticAt z).meromorphicTrailingCoeffAt_of_ne_zero (hS z hz),
    divisor_sphere_eq_zero hf hS]
  suffices (∑ᶠ i, (divisor f (ball (0:ℂ) R) i : ℝ) *
      Real.log ‖canonicalFactor R i z‖) = 0 by simp [this]
  trans ∑ᶠ _i : ℂ, (0:ℝ)
  · apply finsum_congr
    intro i
    by_cases hi : divisor f (ball (0:ℂ) R) i = 0
    · simp [hi]
    · have hiB := (divisor f (ball (0:ℂ) R)).supportWithinDomain hi
      rw [norm_canonicalFactor_eval_circle_eq_one hiB hz, Real.log_one, mul_zero]
  · exact finsum_zero

lemma norm_canonicalFactor_zero {R : ℝ} {i : ℂ} (hR : 0 < R) :
    ‖canonicalFactor R i 0‖ = R/‖i‖ := by
  simp only [canonicalFactor_apply, mul_zero, sub_zero, zero_sub, norm_div,
    norm_pow, norm_real, Real.norm_eq_abs, abs_of_pos hR, norm_mul, norm_neg]
  by_cases hi : i = 0
  · simp [hi]
  · field_simp

lemma ecanonical_log_norm_zero_ge {f g : ℂ → ℂ} {R : ℝ}
    (D : ECanonicalDecomp f g R) (hf : Differentiable ℂ f) (hR : 0 < R)
    (hS : ∀ z ∈ sphere (0:ℂ) R, f z ≠ 0) (h0 : f 0 ≠ 0) :
    Real.log ‖f 0‖ ≤ Real.log ‖g 0‖ := by
  rw [D.log_norm_eq (mem_closedBall_self hR.le)
    ((hf.analyticAt 0).meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mpr h0) hR,
    (hf.analyticAt 0).meromorphicTrailingCoeffAt_of_ne_zero h0,
    divisor_sphere_eq_zero hf hS]
  simp only [Function.locallyFinsuppWithin.coe_zero, Pi.zero_apply, Int.cast_zero, zero_mul,
    finsum_zero, sub_zero, le_add_iff_nonneg_left]
  apply finsum_nonneg
  intro i
  by_cases hi : divisor f (ball (0:ℂ) R) i = 0
  · simp [hi]
  have hiB := (divisor f (ball (0:ℂ) R)).supportWithinDomain hi
  have hi0 : i ≠ 0 := by
    intro H
    subst i
    rw [MeromorphicOn.divisor_apply (fun z _ => (hf.analyticAt z).meromorphicAt)
      (mem_ball_self hR), (hf.analyticAt 0).meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mpr h0] at hi
    simp at hi
  apply mul_nonneg
  · exact_mod_cast AnalyticOnNhd.divisor_nonneg (fun z _ => hf.analyticAt z) i
  · rw [norm_canonicalFactor_zero hR]
    apply Real.log_nonneg
    apply (le_div_iff₀ (norm_pos_iff.mpr hi0)).mpr
    simpa using (mem_ball_zero_iff.mp hiB).le

lemma ecanonical_log_norm_le {f g : ℂ → ℂ} {R B : ℝ}
    (D : ECanonicalDecomp f g R) (hf : Differentiable ℂ f) (hR : 0 < R)
    (hS : ∀ z ∈ sphere (0:ℂ) R, f z ≠ 0)
    (hbound : ∀ z ∈ sphere (0:ℂ) R, ‖f z‖ ≤ Real.exp B)
    {z : ℂ} (hz : z ∈ closedBall (0:ℂ) R) : Real.log ‖g z‖ ≤ B := by
  apply (Real.log_le_iff_le_exp (norm_pos_iff.mpr (D.ne_zero z hz))).mpr
  apply Complex.norm_le_of_forall_mem_frontier_norm_le (isBounded_ball (x := (0:ℂ)) (r := R))
    (D.analyticOnNhd.differentiableOn.diffContOnCl_ball subset_rfl)
  · intro w hw
    have hwS : w ∈ sphere (0:ℂ) R := by simpa [frontier_ball _ hR.ne'] using hw
    have H := ecanonical_log_norm_eq_on_sphere D hf hR hS hwS
    have HE := congrArg Real.exp H
    rw [Real.exp_log (norm_pos_iff.mpr (D.ne_zero w (sphere_subset_closedBall hwS))),
      Real.exp_log (norm_pos_iff.mpr (hS w hwS))] at HE
    exact HE ▸ hbound w hwS
  · simpa [closure_ball _ hR.ne'] using hz

end PrimeDegreePackets.AnalyticGrowth

open scoped Topology ComplexConjugate
namespace PrimeDegreePackets.AnalyticGrowth

lemma canonicalNumerator_norm_lower {R : ℝ} {ρ z : ℂ} (hR : 0 < R)
    (hρ : ‖ρ‖ ≤ R) (hz : ‖z‖ ≤ R/2) :
    R^2/2 ≤ ‖(R:ℂ)^2-conj ρ*z‖ := by
  have H := norm_sub_norm_le ((R:ℂ)^2) (conj ρ*z)
  simp only [norm_pow, norm_real, Real.norm_eq_abs, abs_of_pos hR,
    norm_mul, norm_conj] at H
  have H' := mul_le_mul hρ hz (norm_nonneg z) hR.le
  nlinarith

lemma canonicalNumerator_ne_zero {R : ℝ} {ρ z : ℂ} (hR : 0 < R)
    (hρ : ‖ρ‖ ≤ R) (hz : ‖z‖ ≤ R/2) : (R:ℂ)^2-conj ρ*z ≠ 0 := by
  exact norm_pos_iff.mp (lt_of_lt_of_le (by positivity) (canonicalNumerator_norm_lower hR hρ hz))

lemma norm_canonicalCorrection_sub_le {R : ℝ} {ρ z w : ℂ} (hR : 0 < R)
    (hρ : ‖ρ‖ ≤ R) (hz : ‖z‖ ≤ R/2) (hw : ‖w‖ ≤ R/2) :
    ‖canonicalCorrection R ρ z-canonicalCorrection R ρ w‖ ≤ 4/R^2*‖z-w‖ := by
  have hZ := canonicalNumerator_ne_zero hR hρ hz
  have hW := canonicalNumerator_ne_zero hR hρ hw
  have HE : canonicalCorrection R ρ z-canonicalCorrection R ρ w =
      (conj ρ)^2*(z-w)/(((R:ℂ)^2-conj ρ*z)*((R:ℂ)^2-conj ρ*w)) := by
    unfold canonicalCorrection
    field_simp
    ring
  rw [HE, norm_div, norm_mul, norm_mul, norm_pow, norm_conj]
  have Hden : R^4/4 ≤ ‖(R:ℂ)^2-conj ρ*z‖*‖(R:ℂ)^2-conj ρ*w‖ := by
    have H := mul_le_mul (canonicalNumerator_norm_lower hR hρ hz)
      (canonicalNumerator_norm_lower hR hρ hw) (by positivity : 0 ≤ R^2/2)
      (norm_nonneg _)
    nlinarith
  have Hn : ‖ρ‖^2*‖z-w‖ ≤ R^2*‖z-w‖ :=
    mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hρ 2) (norm_nonneg _)
  calc
    _ ≤ R^2*‖z-w‖/(R^4/4) := div_le_div₀ (by positivity) Hn (by positivity) Hden
    _ = _ := by field_simp

lemma logDeriv_canonicalFactor {R : ℝ} {ρ z : ℂ} (hR : R ≠ 0)
    (hz : z ≠ ρ) (hnum : (R:ℂ)^2-conj ρ*z ≠ 0) :
    logDeriv (canonicalFactor R ρ) z = -canonicalCorrection R ρ z - 1/(z-ρ) := by
  have HR : (R:ℂ) ≠ 0 := by exact_mod_cast hR
  have HZ : z-ρ ≠ 0 := sub_ne_zero.mpr hz
  have Hn : HasDerivAt (fun z : ℂ => (R:ℂ)^2-conj ρ*z) (-conj ρ) z := by
    apply ((hasDerivAt_const z ((R:ℂ)^2)).sub
      ((hasDerivAt_id z).const_mul (conj ρ))).congr_deriv
    simp
  have Hd : HasDerivAt (fun z : ℂ => (R:ℂ)*(z-ρ)) (R:ℂ) z := by
    apply (((hasDerivAt_id z).sub_const ρ).const_mul (R:ℂ)).congr_deriv
    simp
  unfold canonicalFactor
  rw [logDeriv_div (g := fun z : ℂ => (R:ℂ)*(z-ρ)) z hnum (mul_ne_zero HR HZ) Hn.differentiableAt Hd.differentiableAt]
  rw [logDeriv_apply, logDeriv_apply, Hn.deriv, Hd.deriv]
  unfold canonicalCorrection
  field_simp

end PrimeDegreePackets.AnalyticGrowth


namespace PrimeDegreePackets.AnalyticGrowth

 

lemma ecanonical_logDeriv {f g : ℂ → ℂ} {R : ℝ}
    (D : ECanonicalDecomp f g R) (hf : Differentiable ℂ f) (hR : 0 < R)
    (hS : ∀ z ∈ sphere (0:ℂ) R, f z ≠ 0) {z : ℂ}
    (hz : ‖z‖ ≤ R/2) (hfz : f z ≠ 0) :
    logDeriv f z = (∑ᶠ ρ, (divisor f (ball (0:ℂ) R) ρ : ℂ) *
      (1/(z-ρ)+canonicalCorrection R ρ z)) + logDeriv g z := by
  classical
  let t := D.meromorphicOn.divisor_ball_support_finite.toFinset
  have ht (ρ : ℂ) : ρ ∈ t ↔ divisor f (ball (0:ℂ) R) ρ ≠ 0 := by
    simp only [t, Set.Finite.mem_toFinset, Function.mem_support]
  have hρB (ρ : ℂ) (hρ : ρ ∈ t) : ρ ∈ ball (0:ℂ) R :=
    (divisor f (ball (0:ℂ) R)).supportWithinDomain ((ht ρ).mp hρ)
  have hzB : z ∈ closedBall (0:ℂ) R := mem_closedBall_zero_iff.mpr (by linarith)
  have havoid (ρ : ℂ) (hρ : ρ ∈ t) : z ≠ ρ := by
    intro H
    obtain rfl := H
    have HH := (ht z).mp hρ
    rw [MeromorphicOn.divisor_apply (fun z _ => (hf.analyticAt z).meromorphicAt) (hρB z hρ),
      (hf.analyticAt z).meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mpr hfz] at HH
    simp at HH
  let P : ℂ → ℂ := fun x => ∏ ρ ∈ t, canonicalFactor R ρ x ^ (-divisor f (ball 0 R) ρ)
  have HPa : AnalyticAt ℂ P z := by
    apply Finset.analyticAt_fun_prod
    intro ρ hρ
    apply (analyticOnNhd_canonicalFactor R ρ z (havoid ρ hρ)).fun_zpow
    exact canonicalFactor_ne_zero (hρB ρ hρ) hzB (havoid ρ hρ)
  have HPz : P z ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro ρ hρ
    exact zpow_ne_zero _ (canonicalFactor_ne_zero (hρB ρ hρ) hzB (havoid ρ hρ))
  have HP : (∏ᶠ ρ, (canonicalFactor R ρ)^(-divisor f (ball (0:ℂ) R) ρ)) = P := by
    rw [finprod_eq_prod_of_mulSupport_subset (s := t) _ ?_]
    · ext x
      simp only [P, Finset.prod_apply, Pi.pow_apply]
    · intro ρ hρ
      apply (ht ρ).mpr
      intro H
      simp [H] at hρ
  have HE : f =ᶠ[codiscreteWithin (closedBall (0:ℂ) R)] (fun x => P x*g x) := by
    have H := D.eventuallyEq
    rw [HP, divisor_sphere_eq_zero hf hS] at H
    filter_upwards [H] with x hx
    simpa only [Function.locallyFinsuppWithin.coe_zero, Pi.zero_apply, zpow_zero,
      finprod_one, mul_one, Pi.smul_apply, smul_eq_mul, Pi.mul_apply] using hx
  have HEz : f =ᶠ[𝓝 z] (fun x => P x*g x) := by
    apply ((hf z).continuousAt.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE
      (HPa.mul (D.analyticOnNhd z hzB)).continuousAt).mp
    apply (hf.analyticAt z).meromorphicAt.eventuallyEq_nhdsNE_of_eventuallyEq_codiscreteWithin_preperfect
      (HPa.mul (D.analyticOnNhd z hzB)).meromorphicAt hzB _ HE
    rw [← closure_ball _ hR.ne']
    exact isOpen_ball.perfect_closure.2
  rw [(logDeriv_congr_nhds HEz).eq_of_nhds,
    logDeriv_mul z HPz (D.ne_zero z hzB) HPa.differentiableAt (D.analyticOnNhd z hzB).differentiableAt]
  congr 1
  change logDeriv (fun x => ∏ ρ ∈ t, canonicalFactor R ρ x ^ (-divisor f (ball 0 R) ρ)) z = _
  rw [logDeriv_prod (f := fun ρ x : ℂ => canonicalFactor R ρ x ^
    (-divisor f (ball 0 R) ρ)) (s := t) (x := z) (fun ρ hρ => zpow_ne_zero _
    (canonicalFactor_ne_zero (hρB ρ hρ) hzB (havoid ρ hρ))) (fun ρ hρ =>
      ((analyticOnNhd_canonicalFactor R ρ z (havoid ρ hρ)).fun_zpow
        (canonicalFactor_ne_zero (hρB ρ hρ) hzB (havoid ρ hρ))).differentiableAt)]
  rw [finsum_eq_sum_of_support_subset (s := t) _ (by
    intro ρ hρ
    apply (ht ρ).mpr
    intro H
    simp [H] at hρ)]
  apply Finset.sum_congr rfl
  intro ρ hρ
  rw [logDeriv_fun_zpow (analyticOnNhd_canonicalFactor R ρ z (havoid ρ hρ)).differentiableAt,
    logDeriv_canonicalFactor hR.ne' (havoid ρ hρ)
      (canonicalNumerator_ne_zero hR (mem_ball_zero_iff.mp (hρB ρ hρ)).le hz)]
  push_cast
  ring

end PrimeDegreePackets.AnalyticGrowth


namespace PrimeDegreePackets.AnalyticGrowth


lemma zeroMultiplicity_nonneg {f : ℂ → ℂ} (hf : Differentiable ℂ f) (z : ℂ) :
    0 ≤ zeroMultiplicity f z := by
  have H := AnalyticOnNhd.divisor_nonneg (fun z (_ : z ∈ (univ : Set ℂ)) => hf.analyticAt z) z
  simpa only [zeroMultiplicity, MeromorphicOn.divisor_apply
    (fun z _ => (hf.analyticAt z).meromorphicAt) (mem_univ z),
    Function.locallyFinsuppWithin.coe_zero, Pi.zero_apply] using H

lemma zeroMultiplicity_eq_zero_iff {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (h0 : f 0 ≠ 0) (z : ℂ) : zeroMultiplicity f z = 0 ↔ f z ≠ 0 := by
  rw [zeroMultiplicity, WithTop.untop₀_eq_zero]
  simp only [entire_order_ne_top hf h0 z, or_false,
    (hf.analyticAt z).meromorphicNFAt.meromorphicOrderAt_eq_zero_iff]

lemma zeroMultiplicity_ne_zero_iff {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (h0 : f 0 ≠ 0) (z : ℂ) : zeroMultiplicity f z ≠ 0 ↔ f z = 0 := by
  simp [zeroMultiplicity_eq_zero_iff hf h0]

lemma exists_zero_free_sphere {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (h0 : f 0 ≠ 0) {a b : ℝ} (hab : a < b) :
    ∃ R ∈ Ioo a b, ∀ z ∈ sphere (0:ℂ) R, f z ≠ 0 := by
  have Hfin := ((divisor f (closedBall (0:ℂ) b)).finiteSupport (isCompact_closedBall 0 b)).image
    (fun z : ℂ => ‖z‖)
  obtain ⟨R,hR,H⟩ := (Set.Ioo_infinite hab).exists_notMem_finite Hfin
  refine ⟨R,hR,?_⟩
  intro z hz hz0
  apply H
  have HZ : ‖z‖ = R := mem_sphere_zero_iff_norm.mp hz
  refine ⟨z,?_,HZ⟩
  change divisor f (closedBall (0:ℂ) b) z ≠ 0
  rw [MeromorphicOn.divisor_apply (fun z _ => (hf.analyticAt z).meromorphicAt)
    (show z ∈ closedBall (0:ℂ) b from mem_closedBall_zero_iff.mpr (HZ ▸ hR.2.le))]
  exact (zeroMultiplicity_ne_zero_iff hf h0 z).mpr hz0


lemma diskZeroCount_eq_finsum (f : ℂ → ℂ) (R : ℝ) :
    diskZeroCount f R = ∑ᶠ z, (divisor f (closedBall (0:ℂ) R) z : ℝ) := by
  exact map_finsum (Int.castRingHom ℝ)
    ((divisor f (closedBall (0:ℂ) R)).finiteSupport (isCompact_closedBall 0 R))


lemma diskZeroCount_le {f : ℂ → ℂ} (hf : Differentiable ℂ f) (h0 : f 0 ≠ 0)
    {R B : ℝ} (hR : 0 < R) (hB : 0 ≤ B)
    (hbound : ∀ z : ℂ, ‖z‖ ≤ 2*R → ‖f z‖ ≤ Real.exp B) :
    diskZeroCount f R ≤ (B-Real.log ‖f 0‖)/Real.log 2 := by
  have H := AnalyticOnNhd.sum_divisor_le (f := f) (c := (0:ℂ)) (r := R) (R := 2*R)
    (by simpa [abs_of_pos hR] using hR)
    (by rw [abs_of_pos hR, abs_of_pos (by positivity : 0 < 2*R)]; linarith)
    (Real.one_le_exp_iff.mpr hB) (fun z _ => hf.analyticAt z) h0
    (fun z hz => hbound z (by
      simpa only [abs_of_pos (by positivity : 0 < 2*R)] using
        le_of_eq (mem_sphere_zero_iff_norm.mp hz)))
  rw [abs_of_pos hR] at H
  have HE : 2*R/R = 2 := by field_simp
  simpa only [diskZeroCount, abs_of_pos hR, Real.log_div (Real.exp_ne_zero B)
    (norm_ne_zero_iff.mpr h0), Real.log_exp, HE] using H

end PrimeDegreePackets.AnalyticGrowth
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_MellinGrowth
attribute [-instance] _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal
open MeasureTheory Filter Set Module
universe u
open scoped TensorProduct
open Set Module
open MeasureTheory Set
open scoped ENNReal
open IsDiscreteValuationRing IsLocalRing
open scoped ENNReal BigOperators
open MeasureTheory Set IsDiscreteValuationRing
open Filter
open scoped BigOperators Topology
open NumberField
open scoped NumberField nonZeroDivisors
open scoped BigOperators ArithmeticFunction.zeta
open Finset
open scoped BigOperators Classical ArithmeticFunction.Moebius
open Finset Nat ArithmeticFunction BoundingSieve
open scoped BigOperators Classical
open Finset Nat
open scoped BigOperators
open Filter Topology
open scoped nonZeroDivisors
open Ideal NumberField Finset UniqueFactorizationMonoid
open Filter Set Topology NumberField
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace
open Filter Set Topology
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors RealInnerProductSpace
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace Matrix
open MeasureTheory Filter Set Module TopologicalSpace
open MeasureTheory Filter Set
open scoped BigOperators Topology ENNReal
open scoped BigOperators Topology ENNReal Classical
open scoped BigOperators Topology ENNReal Classical Matrix Matrix.Norms.Elementwise
open scoped BigOperators Topology ENNReal Classical Matrix Matrix.Norms.Elementwise Pointwise
open scoped BigOperators Topology ENNReal Classical Matrix Pointwise
open scoped BigOperators Topology ENNReal Classical Matrix
open MeasureTheory ProbabilityTheory Filter Set
open Set Filter
open scoped Topology
open scoped Classical
open scoped Topology ENNReal Classical
open scoped ENNReal Classical
open MeasureTheory Set Topology UniformSpace TopologicalSpace
open scoped ENNReal Topology
open MeasureTheory Filter Set Matrix
open scoped Topology Classical
open scoped Matrix Classical
open scoped Topology Classical Matrix
open scoped Classical Pointwise
open scoped Topology Classical ENNReal
open scoped Matrix Topology Classical
open MeasureTheory ProbabilityTheory Set Filter
open scoped Matrix Topology Classical ENNReal ProbabilityTheory
open scoped ENNReal ProbabilityTheory
open Set Filter Topology
open Set Filter Topology MeasureTheory
open MeasureTheory Set Filter Topology
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped Matrix ENNReal NNReal ProbabilityTheory
open MeasureTheory
open scoped BigOperators ENNReal
open NumberField Finset
open NumberField Filter Set Topology
open MeasureTheory ProbabilityTheory Matrix
open scoped Classical BigOperators ENNReal
open MeasureTheory Set Filter Topology Module
open scoped BigOperators SchwartzMap
open MeasureTheory Set Filter Topology Module WithLp
open scoped BigOperators SchwartzMap ZeroAtInfty
open scoped FourierTransform
open scoped BigOperators SchwartzMap FourierTransform
open scoped BigOperators FourierTransform
open MeasureTheory Set Filter Topology Module WithLp Asymptotics
open Module WithLp MeasureTheory
open scoped BigOperators Matrix
open Module MeasureTheory
open MeasureTheory Module WithLp
open scoped BigOperators NumberField nonZeroDivisors ENNReal
open Complex Set Metric Filter
open Complex Set Metric Filter MeromorphicOn
open scoped Topology ComplexConjugate
open MeasureTheory Set Filter


namespace PrimeDegreePackets.AnalyticGrowth

 

lemma diskZeroCount_subquadratic {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (h0 : f 0 ≠ 0) (hg : HasSubquadraticGrowth f) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ R : ℝ in atTop, diskZeroCount f R ≤ ε*R^2 := by
  have hL : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have HT : Tendsto (fun R : ℝ => 2*R) atTop atTop :=
    Tendsto.const_mul_atTop (by norm_num : (0:ℝ) < 2) tendsto_id
  have HB := HT.eventually (hg (ε*Real.log 2/8) (by positivity))
  have HC := (tendsto_const_mul_pow_atTop (by decide : (2:ℕ) ≠ 0)
    (by positivity : 0 < ε*Real.log 2/2)).eventually_ge_atTop (-Real.log ‖f 0‖)
  filter_upwards [HB, HC, eventually_gt_atTop (0:ℝ)] with R hB hC hR
  apply (diskZeroCount_le hf h0 hR (by positivity) hB).trans
  apply (div_le_iff₀ hL).mpr
  nlinarith

end PrimeDegreePackets.AnalyticGrowth


namespace PrimeDegreePackets.AnalyticGrowth

lemma divisor_ball_eq_closedBall {f : ℂ → ℂ} {R : ℝ} (hf : Differentiable ℂ f)
    (hS : ∀ z ∈ sphere (0:ℂ) R, f z ≠ 0) :
    (divisor f (ball (0:ℂ) R) : ℂ → ℤ) = divisor f (closedBall (0:ℂ) R) := by
  ext z
  by_cases hz : z ∈ ball (0:ℂ) R
  · rw [MeromorphicOn.divisor_apply (fun z _ => (hf.analyticAt z).meromorphicAt) hz,
      MeromorphicOn.divisor_apply (fun z _ => (hf.analyticAt z).meromorphicAt)
        (ball_subset_closedBall hz)]
  · by_cases hzC : z ∈ closedBall (0:ℂ) R
    · have hzS : z ∈ sphere (0:ℂ) R := by
        rw [mem_sphere_zero_iff_norm]
        exact le_antisymm (mem_closedBall_zero_iff.mp hzC) (not_lt.mp (by simpa using hz))
      rw [MeromorphicOn.divisor_apply (fun z _ => (hf.analyticAt z).meromorphicAt) hzC,
        (hf.analyticAt z).meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mpr (hS z hzS)]
      simp [hz]
    · simp [hz, hzC]

lemma mem_zeroDiskFinset (f : ℂ → ℂ) (R : ℝ) (z : ℂ) :
    z ∈ zeroDiskFinset f R ↔ divisor f (closedBall (0:ℂ) R) z ≠ 0 := by
  simp [zeroDiskFinset, Function.mem_support]

lemma zeroDiskFinset_norm_le {f : ℂ → ℂ} {R : ℝ} {z : ℂ}
    (hz : z ∈ zeroDiskFinset f R) : ‖z‖ ≤ R :=
  mem_closedBall_zero_iff.mp ((divisor f (closedBall (0:ℂ) R)).supportWithinDomain
    ((mem_zeroDiskFinset f R z).mp hz))

lemma divisor_closedBall_eq_multiplicity {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    {R : ℝ} {z : ℂ} (hz : ‖z‖ ≤ R) :
    divisor f (closedBall (0:ℂ) R) z = zeroMultiplicity f z :=
  MeromorphicOn.divisor_apply (fun z _ => (hf.analyticAt z).meromorphicAt)
    (mem_closedBall_zero_iff.mpr hz)

lemma diskZeroCount_eq_sum {f : ℂ → ℂ} (hf : Differentiable ℂ f) (R : ℝ) :
    diskZeroCount f R = ∑ ρ ∈ zeroDiskFinset f R, (zeroMultiplicity f ρ : ℝ) := by
  classical
  rw [diskZeroCount_eq_finsum, finsum_eq_sum_of_support_subset (s := zeroDiskFinset f R) _ (by
    intro z hz
    apply (mem_zeroDiskFinset f R z).mpr
    intro H
    simp [H] at hz)]
  apply Finset.sum_congr rfl
  intro ρ hρ
  rw [divisor_closedBall_eq_multiplicity hf (zeroDiskFinset_norm_le hρ)]

lemma ecanonical_logDeriv_finite {f g : ℂ → ℂ} {R : ℝ}
    (D : ECanonicalDecomp f g R) (hf : Differentiable ℂ f) (hR : 0 < R)
    (hS : ∀ z ∈ sphere (0:ℂ) R, f z ≠ 0) {z : ℂ}
    (hz : ‖z‖ ≤ R/2) (hfz : f z ≠ 0) :
    logDeriv f z = diskPoleSum f R z +
      (∑ ρ ∈ zeroDiskFinset f R, (zeroMultiplicity f ρ : ℂ)*canonicalCorrection R ρ z) +
      logDeriv g z := by
  classical
  rw [ecanonical_logDeriv D hf hR hS hz hfz, divisor_ball_eq_closedBall hf hS]
  rw [finsum_eq_sum_of_support_subset (s := zeroDiskFinset f R) _ (by
    intro ρ hρ
    apply (mem_zeroDiskFinset f R ρ).mpr
    intro H
    simp [H] at hρ)]
  congr 1
  simp only [diskPoleSum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro ρ hρ
  rw [divisor_closedBall_eq_multiplicity hf (zeroDiskFinset_norm_le hρ), mul_add]

lemma correction_sum_sub_le {f : ℂ → ℂ} (hf : Differentiable ℂ f) {R : ℝ}
    (hR : 0 < R) {z w : ℂ} (hz : ‖z‖ ≤ R/2) (hw : ‖w‖ ≤ R/2) :
    ‖(∑ ρ ∈ zeroDiskFinset f R, (zeroMultiplicity f ρ : ℂ)*canonicalCorrection R ρ z) -
      (∑ ρ ∈ zeroDiskFinset f R, (zeroMultiplicity f ρ : ℂ)*canonicalCorrection R ρ w)‖ ≤
      (4*diskZeroCount f R/R^2)*‖z-w‖ := by
  classical
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ ρ ∈ zeroDiskFinset f R, ‖(zeroMultiplicity f ρ : ℂ)*
        canonicalCorrection R ρ z-(zeroMultiplicity f ρ : ℂ)*canonicalCorrection R ρ w‖ :=
      norm_sum_le _ _
    _ ≤ ∑ ρ ∈ zeroDiskFinset f R, (zeroMultiplicity f ρ : ℝ)*(4/R^2*‖z-w‖) := by
      apply Finset.sum_le_sum
      intro ρ hρ
      rw [← mul_sub, norm_mul, Complex.norm_intCast,
        abs_of_nonneg (show (0:ℝ) ≤ zeroMultiplicity f ρ by exact_mod_cast zeroMultiplicity_nonneg hf ρ)]
      exact mul_le_mul_of_nonneg_left
        (norm_canonicalCorrection_sub_le hR (zeroDiskFinset_norm_le hρ) hz hw)
        (by exact_mod_cast zeroMultiplicity_nonneg hf ρ)
    _ = _ := by rw [← Finset.sum_mul, ← diskZeroCount_eq_sum hf]; ring

lemma diskPoleSum_error_le {f : ℂ → ℂ} (hf : Differentiable ℂ f) (h0 : f 0 ≠ 0)
    {R B : ℝ} (hR : 0 < R) (hS : ∀ z ∈ sphere (0:ℂ) R, f z ≠ 0)
    (hbound : ∀ z ∈ sphere (0:ℂ) R, ‖f z‖ ≤ Real.exp B)
    (hB : Real.log ‖f 0‖ < B) {z w : ℂ}
    (hz : ‖z‖ < R/4) (hw : ‖w‖ < R/4) (hfz : f z ≠ 0) (hfw : f w ≠ 0) :
    ‖(logDeriv f z-logDeriv f w)-(diskPoleSum f R z-diskPoleSum f R w)‖ ≤
      ((64*(B-Real.log ‖f 0‖)+4*diskZeroCount f R)/R^2)*‖z-w‖ := by
  obtain ⟨g,D⟩ := exists_entire_ecanonicalDecomp (R := R) hf h0
  have hz' : ‖z‖ ≤ R/2 := by linarith
  have hw' : ‖w‖ ≤ R/2 := by linarith
  have HE : (logDeriv f z-logDeriv f w)-(diskPoleSum f R z-diskPoleSum f R w) =
      ((∑ ρ ∈ zeroDiskFinset f R, (zeroMultiplicity f ρ : ℂ)*canonicalCorrection R ρ z) -
       (∑ ρ ∈ zeroDiskFinset f R, (zeroMultiplicity f ρ : ℂ)*canonicalCorrection R ρ w)) +
      (logDeriv g z-logDeriv g w) := by
    rw [ecanonical_logDeriv_finite D hf hR hS hz' hfz,
      ecanonical_logDeriv_finite D hf hR hS hw' hfw]
    ring
  rw [HE]
  apply (norm_add_le _ _).trans
  have Hg := logDeriv_sub_le_of_log_norm_le hR (sub_pos.mpr hB)
    (D.analyticOnNhd.differentiableOn.mono ball_subset_closedBall)
    (fun z hz => D.ne_zero z (ball_subset_closedBall hz))
    (fun z hz => sub_le_sub (ecanonical_log_norm_le D hf hR hS hbound (ball_subset_closedBall hz))
      (ecanonical_log_norm_zero_ge D hf hR hS h0))
    (mem_ball_zero_iff.mpr hz) (mem_ball_zero_iff.mpr hw)
  have HC := correction_sum_sub_le hf hR hz' hw'
  calc
    _ ≤ (4*diskZeroCount f R/R^2)*‖z-w‖ +
      (64*(B-Real.log ‖f 0‖)/R^2)*‖z-w‖ := add_le_add HC Hg
    _ = _ := by ring

end PrimeDegreePackets.AnalyticGrowth


namespace PrimeDegreePackets.AnalyticGrowth

 

lemma tendsto_diskPoleSum_sub {f : ℂ → ℂ} (hf : Differentiable ℂ f) (h0 : f 0 ≠ 0)
    (hg : HasSubquadraticGrowth f) {ι : Type*} {l : Filter ι} {r : ι → ℝ}
    (hr : Tendsto r l atTop) (hS : ∀ᶠ i in l, ∀ z ∈ sphere (0:ℂ) (r i), f z ≠ 0)
    {z w : ℂ} (hfz : f z ≠ 0) (hfw : f w ≠ 0) :
    Tendsto (fun i => diskPoleSum f (r i) z-diskPoleSum f (r i) w) l
      (𝓝 (logDeriv f z-logDeriv f w)) := by
  apply Metric.tendsto_nhds.2
  intro ε hε
  let η := ε/(200*(‖z-w‖+1))
  have hη : 0 < η := by dsimp [η] <;> positivity
  have HP := (tendsto_const_mul_pow_atTop (by decide : (2:ℕ) ≠ 0) hη).eventually_ge_atTop
    (|Real.log ‖f 0‖|+1-Real.log ‖f 0‖)
  filter_upwards [hr.eventually (hg η hη), hr.eventually (diskZeroCount_subquadratic hf h0 hg hη),
    hr.eventually HP, hr.eventually (eventually_gt_atTop (4*(‖z‖+‖w‖+1))), hS]
    with i hG hN hP hR hS'
  have hR0 : 0 < r i := by linarith [norm_nonneg z, norm_nonneg w]
  have hz : ‖z‖ < r i/4 := by linarith [norm_nonneg w]
  have hw : ‖w‖ < r i/4 := by linarith [norm_nonneg z]
  have HB : Real.log ‖f 0‖ < η*(r i)^2+|Real.log ‖f 0‖|+1 := by
    nlinarith [le_abs_self (Real.log ‖f 0‖), sq_nonneg (r i)]
  have H := diskPoleSum_error_le hf h0 hR0 hS' (B := η*(r i)^2+|Real.log ‖f 0‖|+1)
    (fun a ha => (hG a (le_of_eq (mem_sphere_zero_iff_norm.mp ha))).trans
      (Real.exp_le_exp.mpr (by linarith [abs_nonneg (Real.log ‖f 0‖)]))) HB hz hw hfz hfw
  rw [dist_eq_norm']
  apply H.trans_lt
  have HE : (64*(η*(r i)^2+|Real.log ‖f 0‖|+1-Real.log ‖f 0‖)+4*diskZeroCount f (r i))/(r i)^2
      ≤ 132*η := by
    apply (div_le_iff₀ (sq_pos_of_pos hR0)).mpr
    nlinarith
  calc
    _ ≤ (132*η)*‖z-w‖ := mul_le_mul_of_nonneg_right HE (norm_nonneg _)
    _ < ε := by
      dsimp [η]
      have Hden : 0 < 200*(‖z-w‖+1) := by positivity
      rw [show 132*(ε/(200*(‖z-w‖+1)))*‖z-w‖ =
        ε*(132*‖z-w‖)/(200*(‖z-w‖+1)) by ring]
      apply (div_lt_iff₀ Hden).mpr
      nlinarith [norm_nonneg (z-w)]

 

lemma exists_good_radii {f : ℂ → ℂ} (hf : Differentiable ℂ f) (h0 : f 0 ≠ 0) :
    ∃ r : ℕ → ℝ, Tendsto r atTop atTop ∧
      (∀ j : ℕ, (j:ℝ)+1 < r j ∧ r j < j+2) ∧
      ∀ j z, z ∈ sphere (0:ℂ) (r j) → f z ≠ 0 := by
  choose r hR hS using fun j : ℕ => exists_zero_free_sphere hf h0
    (show (j:ℝ)+1 < j+2 by linarith)
  refine ⟨r,?_,hR,hS⟩
  apply tendsto_atTop_mono (fun j => (hR j).1.le)
  exact tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop

end PrimeDegreePackets.AnalyticGrowth
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_ZeroReflection
attribute [-instance] _root_.OAI.PrimeDegreePackets.instNonemptyLeafTestSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal
open MeasureTheory Filter Set Module
universe u
open scoped TensorProduct
open Set Module
open MeasureTheory Set
open scoped ENNReal
open IsDiscreteValuationRing IsLocalRing
open scoped ENNReal BigOperators
open MeasureTheory Set IsDiscreteValuationRing
open Filter
open scoped BigOperators Topology
open NumberField
open scoped NumberField nonZeroDivisors
open scoped BigOperators ArithmeticFunction.zeta
open Finset
open scoped BigOperators Classical ArithmeticFunction.Moebius
open Finset Nat ArithmeticFunction BoundingSieve
open scoped BigOperators Classical
open Finset Nat
open scoped BigOperators
open Filter Topology
open scoped nonZeroDivisors
open Ideal NumberField Finset UniqueFactorizationMonoid
open Filter Set Topology NumberField
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace
open Filter Set Topology
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors RealInnerProductSpace
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace Matrix
open MeasureTheory Filter Set Module TopologicalSpace
open MeasureTheory Filter Set
open scoped BigOperators Topology ENNReal
open scoped BigOperators Topology ENNReal Classical
open scoped BigOperators Topology ENNReal Classical Matrix Matrix.Norms.Elementwise
open scoped BigOperators Topology ENNReal Classical Matrix Matrix.Norms.Elementwise Pointwise
open scoped BigOperators Topology ENNReal Classical Matrix Pointwise
open scoped BigOperators Topology ENNReal Classical Matrix
open MeasureTheory ProbabilityTheory Filter Set
open Set Filter
open scoped Topology
open scoped Classical
open scoped Topology ENNReal Classical
open scoped ENNReal Classical
open MeasureTheory Set Topology UniformSpace TopologicalSpace
open scoped ENNReal Topology
open MeasureTheory Filter Set Matrix
open scoped Topology Classical
open scoped Matrix Classical
open scoped Topology Classical Matrix
open scoped Classical Pointwise
open scoped Topology Classical ENNReal
open scoped Matrix Topology Classical
open MeasureTheory ProbabilityTheory Set Filter
open scoped Matrix Topology Classical ENNReal ProbabilityTheory
open scoped ENNReal ProbabilityTheory
open Set Filter Topology
open Set Filter Topology MeasureTheory
open MeasureTheory Set Filter Topology
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped Matrix ENNReal NNReal ProbabilityTheory
open MeasureTheory
open scoped BigOperators ENNReal
open NumberField Finset
open NumberField Filter Set Topology
open MeasureTheory ProbabilityTheory Matrix
open scoped Classical BigOperators ENNReal
open MeasureTheory Set Filter Topology Module
open scoped BigOperators SchwartzMap
open MeasureTheory Set Filter Topology Module WithLp
open scoped BigOperators SchwartzMap ZeroAtInfty
open scoped FourierTransform
open scoped BigOperators SchwartzMap FourierTransform
open scoped BigOperators FourierTransform
open MeasureTheory Set Filter Topology Module WithLp Asymptotics
open Module WithLp MeasureTheory
open scoped BigOperators Matrix
open Module MeasureTheory
open MeasureTheory Module WithLp
open scoped BigOperators NumberField nonZeroDivisors ENNReal
open Complex Set Metric Filter
open Complex Set Metric Filter MeromorphicOn
open scoped Topology ComplexConjugate
open MeasureTheory Set Filter
namespace PrimeDegreePackets.AnalyticGrowth

lemma zeroMultiplicity_reflection {f : ℂ → ℂ} (hfe : ∀ z, f (1-z) = f z) (z : ℂ) :
    zeroMultiplicity f (1-z) = zeroMultiplicity f z := by
  have Hg : HasDerivAt (fun z : ℂ => 1-z) (-1) z := by
    apply ((hasDerivAt_id z).const_sub 1).congr_deriv
    simp
  have H := meromorphicOrderAt_comp_of_deriv_ne_zero (f := f)
    (g := fun z : ℂ => 1-z) (x := z) (analyticAt_const.sub analyticAt_id) (by rw [Hg.deriv]; norm_num)
  have HE : f ∘ (fun z : ℂ => 1-z) = f := funext hfe
  rw [HE] at H
  exact congrArg WithTop.untop₀ H.symm

lemma logDeriv_reflection {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hfe : ∀ z, f (1-z) = f z) (z : ℂ) : logDeriv f (1-z) = -logDeriv f z := by
  have Hg : HasDerivAt (fun z : ℂ => 1-z) (-1) z := by
    apply ((hasDerivAt_id z).const_sub 1).congr_deriv
    simp
  have H := ((hf (1-z)).hasDerivAt.comp z Hg)
  have HE : (fun z : ℂ => f (1-z)) = f := funext hfe
  simp only [Function.comp_def] at H
  rw [HE] at H
  have HD := H.deriv
  rw [logDeriv_apply, logDeriv_apply, hfe]
  have HD' : deriv f (1-z) = -deriv f z := by linear_combination HD
  rw [HD', neg_div]

 

lemma hasSum_of_nonneg_finite_exhaustion {α ι : Type*} {l : Filter ι} [NeBot l]
    {a : α → ℝ} (ha : ∀ x, 0 ≤ a x) (t : ι → Finset α)
    (ht : ∀ x, a x ≠ 0 → ∀ᶠ i in l, x ∈ t i) {A : ℝ}
    (hA : Tendsto (fun i => ∑ x ∈ t i, a x) l (𝓝 A)) : HasSum a A := by
  classical
  have HB : ∀ s : Finset α, ∑ x ∈ s, a x ≤ A := by
    intro s
    have H : ∀ᶠ i in l, ∀ x ∈ s, a x ≠ 0 → x ∈ t i := by
      rw [Filter.eventually_all_finset]
      intro x hx
      by_cases hx0 : a x = 0
      · exact Filter.Eventually.of_forall (by simp [hx0])
      · exact (ht x hx0).mono (fun i hi _ => hi)
    apply ge_of_tendsto hA
    filter_upwards [H] with i hi
    calc
      _ = ∑ x ∈ s.filter (fun x => a x ≠ 0), a x := by
        symm
        apply Finset.sum_subset (Finset.filter_subset _ _)
        intro x hx hn
        by_contra h
        exact hn (Finset.mem_filter.mpr ⟨hx,h⟩)
      _ ≤ ∑ x ∈ t i, a x := Finset.sum_le_sum_of_subset_of_nonneg
        (fun x hx => hi x (Finset.mem_filter.mp hx).1 (Finset.mem_filter.mp hx).2)
        (fun x _ _ => ha x)
  have HS := summable_of_sum_le ha HB
  have HE : ∑' x, a x = A := le_antisymm (HS.tsum_le_of_sum_le HB)
    (le_of_tendsto hA (Filter.Eventually.of_forall (fun i => HS.sum_le_tsum (t i) (fun x _ => ha x))))
  exact HE ▸ HS.hasSum

end PrimeDegreePackets.AnalyticGrowth


namespace PrimeDegreePackets.AnalyticGrowth


lemma realZeroPole_nonneg {f : ℂ → ℂ} (hf : Differentiable ℂ f) (h0 : f 0 ≠ 0)
    (hstrip : ∀ ρ, f ρ = 0 → ρ.re ≤ 1) {σ : ℝ} (hσ : 1 < σ) (ρ : ℂ) :
    0 ≤ realZeroPole f σ ρ := by
  by_cases hm : zeroMultiplicity f ρ = 0
  · simp [realZeroPole, hm]
  have hρ := hstrip ρ ((zeroMultiplicity_ne_zero_iff hf h0 ρ).mp hm)
  unfold realZeroPole
  apply mul_nonneg (by exact_mod_cast zeroMultiplicity_nonneg hf ρ)
  simp only [one_div, Complex.inv_re, Complex.sub_re, Complex.ofReal_re]
  exact div_nonneg (by linarith) (Complex.normSq_nonneg _)

lemma realZeroPole_pair {f : ℂ → ℂ} (hfe : ∀ z, f (1-z) = f z)
    (σ : ℝ) (ρ : ℂ) :
    realZeroPole f σ ρ + realZeroPole f σ (1-ρ) =
      ((zeroMultiplicity f ρ : ℂ)*(1/((σ:ℂ)-ρ)-1/((1-(σ:ℂ))-ρ))).re := by
  have HE : (σ:ℂ)-(1-ρ) = -((1-(σ:ℂ))-ρ) := by ring
  simp only [realZeroPole, zeroMultiplicity_reflection hfe, HE, one_div, inv_neg,
    Complex.neg_re, Complex.mul_re, Complex.intCast_re, Complex.intCast_im,
    zero_mul, sub_zero, Complex.sub_re]
  ring

lemma diskPoleSum_sub_re {f : ℂ → ℂ} (hfe : ∀ z, f (1-z) = f z)
    (σ R : ℝ) :
    (diskPoleSum f R σ-diskPoleSum f R (1-(σ:ℂ))).re =
      ∑ ρ ∈ zeroDiskFinset f R, (realZeroPole f σ ρ+realZeroPole f σ (1-ρ)) := by
  classical
  simp only [diskPoleSum, ← Finset.sum_sub_distrib, ← mul_sub,
    realZeroPole_pair hfe]
  exact map_sum Complex.reAddGroupHom _ _

 

theorem hasSum_realZeroPole_oai {f : ℂ → ℂ} (hf : Differentiable ℂ f) (h0 : f 0 ≠ 0)
    (hg : HasSubquadraticGrowth f) (hfe : ∀ z, f (1-z) = f z)
    (hstrip : ∀ ρ, f ρ = 0 → ρ.re ≤ 1) {σ : ℝ} (hσ : 1 < σ) :
    HasSum (realZeroPole f σ) (logDeriv f σ).re := by
  classical
  have hσ0 : f (σ:ℂ) ≠ 0 := by
    intro h
    have HH := hstrip σ h
    simp only [Complex.ofReal_re] at HH
    linarith
  have hσ1 : f (1-(σ:ℂ)) ≠ 0 := by rwa [hfe]
  obtain ⟨r,hr,_,hS⟩ := exists_good_radii hf h0
  have HT := (Complex.continuous_re.tendsto _).comp (tendsto_diskPoleSum_sub hf h0 hg hr
    (Filter.Eventually.of_forall hS) hσ0 hσ1)
  have HT' : Tendsto (fun j => ∑ ρ ∈ zeroDiskFinset f (r j),
      (realZeroPole f σ ρ+realZeroPole f σ (1-ρ))) atTop (𝓝 (2*(logDeriv f σ).re)) := by
    simpa only [Function.comp_def, diskPoleSum_sub_re hfe,
      logDeriv_reflection hf hfe, Complex.sub_re, Complex.neg_re, sub_neg_eq_add, two_mul, Complex.add_re] using HT
  have HNN := realZeroPole_nonneg hf h0 hstrip hσ
  have Hsum : HasSum (fun ρ => realZeroPole f σ ρ+realZeroPole f σ (1-ρ))
      (2*(logDeriv f σ).re) := by
    apply hasSum_of_nonneg_finite_exhaustion (fun ρ => add_nonneg (HNN ρ) (HNN (1-ρ)))
      (fun j => zeroDiskFinset f (r j)) _ HT'
    intro ρ hρ
    have Hm : zeroMultiplicity f ρ ≠ 0 := by
      intro H
      apply hρ
      simp [realZeroPole, zeroMultiplicity_reflection hfe, H]
    filter_upwards [hr.eventually_ge_atTop ‖ρ‖] with j hj
    rw [mem_zeroDiskFinset, divisor_closedBall_eq_multiplicity hf hj]
    exact Hm
  have HS : Summable (realZeroPole f σ) := Hsum.summable.of_nonneg_of_le HNN
    (fun ρ => le_add_of_nonneg_right (HNN (1-ρ)))
  let e : ℂ ≃ ℂ := ⟨fun ρ => 1-ρ, fun ρ => 1-ρ, by intro ρ; ring, by intro ρ; ring⟩
  have HS' : Summable (fun ρ => realZeroPole f σ (1-ρ)) := e.summable_iff.mpr HS
  have HE : (∑' ρ, realZeroPole f σ (1-ρ)) = ∑' ρ, realZeroPole f σ ρ :=
    e.tsum_eq (realZeroPole f σ)
  have HH := Hsum.tsum_eq
  rw [HS.tsum_add HS', HE] at HH
  have HA : (∑' ρ, realZeroPole f σ ρ) = (logDeriv f σ).re := by linarith
  exact HA ▸ HS.hasSum

end PrimeDegreePackets.AnalyticGrowth


end
end

end OAI
end

theorem solution : type_of% @OAI.PrimeDegreePackets.AnalyticGrowth.hasSum_realZeroPole_oai := @OAI.PrimeDegreePackets.AnalyticGrowth.hasSum_realZeroPole_oai
