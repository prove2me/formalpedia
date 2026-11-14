-- Prove2me | solution 1 for OAI.PrimeDegreePackets.HeckeMellin.boundedDegree_near_one_zero_real_simple_unique
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T06:48:30.368632+00:00
-- url     : https://prove2.me/submissions/e99f244c-e05c-4a9a-a62e-e5b36ed946cc

import Mathlib
import Definitions.Def_DukePrimeDegree
import Definitions.Def_OAIQ244Duke023
import Definitions.Def_OAIQ244Duke024
import Theorems.Thm_OAI_PrimeDegreePackets_HeckeMellin_completedThetaXi_conj_totallyReal
import Theorems.Thm_OAI_PrimeDegreePackets_HeckeMellin_completedThetaXi_eq_totallyReal
import Theorems.Thm_OAI_PrimeDegreePackets_HeckeMellin_completedThetaXi_functionalEquation_totallyReal
import Theorems.Thm_OAI_PrimeDegreePackets_HeckeMellin_dedekindXiZeros_ne_zero_totallyReal

section
-- module Solutions.OAIQ244_DUKE.Compat
attribute [-instance] _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.OAI.PrimeDegreePackets.rootGroupMeasurableSpace _root_.OAI.PrimeDegreePackets.xMeasurableSpace _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.infiniteAdeleRingT2Space
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
/-- Mathlib's newer name for `measurable_pi_lambda` (with `f` implicit). -/
theorem Measurable.of_eval {δ ι : Type*} {π : ι → Type*} [MeasurableSpace δ]
    [∀ i, MeasurableSpace (π i)] {f : δ → ∀ i, π i}
    (h : ∀ i, Measurable fun a => f a i) : Measurable f := measurable_pi_lambda f h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_AnalyticLogarithms
attribute [-instance] _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.diagonalLogAction_continuous _root_.OAI.PrimeDegreePackets.instContinuousSMulPadicLocalAlgebra _root_.OAI.PrimeDegreePackets.instIsModuleTopologyPadicLocalAlgebra _root_.OAI.PrimeDegreePackets.instIsTopologicalRingLocalAlgebra _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.OAI.PrimeDegreePackets.xT2Space _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.finiteIdeleGroupT2Space _root_.ideleGroupT2Space _root_.infiniteAdeleRingT2Space _root_.infiniteIdeleGroupT2Space
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply
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
-- module Solutions.OAIQ244_DUKE.PrimePackets_PrimeFactors
attribute [-instance] _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.infiniteAdeleRingT2Space
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply
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


namespace PrimeDegreePackets
universe v

lemma ennreal_tsum_fintype_prod {ι : Type u} [Fintype ι]
    (κ : ι → Type v) (f : ∀ i, κ i → ℝ≥0∞) :
    (∑' k : ∀ i, κ i, ∏ i, f i (k i)) = ∏ i, ∑' x : κ i, f i x := by
  classical
  revert κ f
  refine Fintype.induction_empty_option (P := fun ι [Fintype ι] =>
    ∀ (κ : ι → Type v) (f : ∀ i, κ i → ℝ≥0∞),
      (∑' k : ∀ i, κ i, ∏ i, f i (k i)) = ∏ i, ∑' x : κ i, f i x)
    ?_ ?_ ?_ ι
  · intro α β _ e ih κ f
    let : Fintype α := Fintype.ofEquiv β e.symm
    have h := ih (fun i => κ (e i)) (fun i => f (e i))
    rw [← (Equiv.piCongrLeft κ e).tsum_eq]
    convert h using 1
    · apply tsum_congr
      intro k
      exact (Fintype.prod_equiv e _ _ (by intro i; simp)).symm
    · exact (Fintype.prod_equiv e _ _ (by intro i; rfl)).symm
  · intro κ f
    simp
  · intro α _ ih κ f
    rw [← Equiv.piOptionEquivProd.symm.tsum_eq]
    simp only [Fintype.prod_option]
    change (∑' c : κ none × (∀ i, κ (some i)),
      f none c.1 * ∏ i, f (some i) (c.2 i)) = _
    rw [ENNReal.tsum_prod']
    simp_rw [ENNReal.tsum_mul_left]
    rw [ENNReal.tsum_mul_right, ih]



end PrimeDegreePackets


end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_IdealCoefficients
attribute [-instance] _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply
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
namespace PrimeDegreePackets

variable (K : Type*) [Field K] [NumberField K]



lemma idealCoefficient_pos (m : ℕ) (hm : m ≠ 0) :
    idealCoefficient K m = Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = m} := by
  simp [idealCoefficient,hm]

lemma idealCoefficient_one : idealCoefficient K 1 = 1 := by
  simp [idealCoefficient, Ideal.absNorm_eq_one_iff]

lemma idealCoefficient_multiplicative : (idealCoefficient K).IsMultiplicative := by
  refine ⟨idealCoefficient_one K, ?_⟩
  intro m n hmn
  by_cases hm : m = 0
  · simp [hm]
  by_cases hn : n = 0
  · simp [hn]
  rw [idealCoefficient_pos K _ (mul_ne_zero hm hn), idealCoefficient_pos K _ hm,
    idealCoefficient_pos K _ hn, ← Nat.card_prod]
  exact Nat.card_congr (idealNormProductEquiv K m n hm hn hmn).symm


open Filter Topology Asymptotics

lemma idealCoefficientReal_nonneg (m : ℕ) : 0 ≤ idealCoefficientReal K m := Nat.cast_nonneg _

 
lemma idealCoefficient_summatory_limit :
    Tendsto (fun n : ℕ => (∑k ∈ Icc 1 n, idealCoefficientReal K k) / (n:ℝ))
      atTop (𝓝 (NumberField.dedekindZeta_residue K)) := by
  refine ((NumberField.Ideal.tendsto_norm_le_div_atTop₀ K).comp tendsto_natCast_atTop_atTop).congr fun n => ?_
  simp only [Function.comp_apply, Nat.cast_le]
  congr 1
  simp only [idealCoefficientReal,ArithmeticFunction.coe_mk]
  rw [←Nat.cast_sum]
  congr 1
  rw [←add_left_inj 1, ←Ideal.card_norm_le_eq_card_norm_le_add_one,
    show Finset.Icc 1 n = Finset.Ioc 0 n from Icc_succ_left_eq_Ioc _ _]
  have H : (∑k ∈ Ioc 0 n, idealCoefficient K k) =
      ∑k ∈ Ioc 0 n, Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = k} := by
    apply sum_congr rfl
    intro k hk
    exact idealCoefficient_pos K k (Nat.ne_of_gt (Finset.mem_Ioc.mp hk).1)
  rw [H, show 1 = Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = 0} by
      simp [Ideal.absNorm_eq_zero_iff], sum_Ioc_add_eq_sum_Icc n.zero_le,
    ←card_preimage_eq_sum_card_image_eq (fun k _ => Ideal.finite_setOfPred_absNorm_eq k)]
  simp [Set.coe_eq_subtype]

lemma idealCoefficient_LSeriesSummable {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (fun m => (idealCoefficientReal K m : ℂ)) s := by
  refine LSeriesSummable_of_sum_norm_bigO_and_nonneg ?_ (idealCoefficientReal_nonneg K) zero_le_one hs
  apply isBigO_atTop_natCast_rpow_of_tendsto_div_rpow
  simpa using idealCoefficient_summatory_limit K


lemma realDirichletTerm_ofReal (f : ArithmeticFunction ℝ) (s : ℝ) (m : ℕ) :
    (realDirichletTerm f s m : ℂ) = LSeries.term (fun m => (f m : ℂ)) s m := by
  by_cases hm : m = 0
  · subst m
    simp [realDirichletTerm]
  · simp only [realDirichletTerm, ArithmeticFunction.coe_mk,LSeries.term_of_ne_zero hm,
      Complex.ofReal_div, Complex.ofReal_cpow (Nat.cast_nonneg m),Complex.ofReal_natCast]

lemma idealCoefficient_real_summable {s : ℝ} (hs : 1 < s) :
    Summable (realDirichletTerm (idealCoefficientReal K) s) := by
  apply Complex.summable_ofReal.mp
  simp_rw [realDirichletTerm_ofReal]
  exact idealCoefficient_LSeriesSummable K (by simpa using hs)

lemma idealCoefficient_LSeries_eq (s : ℂ) :
    LSeries (fun m => (idealCoefficientReal K m : ℂ)) s = NumberField.dedekindZeta K s := by
  apply LSeries_congr _ s
  intro m hm
  simp only [idealCoefficientReal,ArithmeticFunction.coe_mk,idealCoefficient_pos K m hm,
    Complex.ofReal_natCast]

 
lemma idealDirichlet_eq_dedekindZeta (s : ℝ) :
    ((∑'m, realDirichletTerm (idealCoefficientReal K) s m : ℝ) : ℂ) =
      NumberField.dedekindZeta K s := by
  rw [Complex.ofReal_tsum, ←idealCoefficient_LSeries_eq]
  apply tsum_congr
  intro m
  exact realDirichletTerm_ofReal _ _ _

end PrimeDegreePackets
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_MangoldtBounds
attribute [-instance] _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.infiniteAdeleRingT2Space
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
namespace PrimeDegreePackets

open scoped ArithmeticFunction.vonMangoldt


lemma realDirichletTerm_nonneg {f : ArithmeticFunction ℝ}
    (hf0 : ∀m, 0 ≤ f m) (s : ℝ) (m : ℕ) : 0 ≤ realDirichletTerm f s m := by
  exact div_nonneg (hf0 m) (Real.rpow_nonneg (Nat.cast_nonneg m) s)

end PrimeDegreePackets


end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_PrimeSums
attribute [-instance] _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply
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


namespace PrimeDegreePackets
open scoped ENNReal


variable (K : Type*) [Field K] [NumberField K]

lemma idealsOverPrime_norm_two_le {p : ℕ} {P : Ideal (𝓞 K)}
    (hP : P ∈ idealsOverPrime K p) : 2 ≤ Ideal.absNorm P := by
  have hP0 : Ideal.absNorm P ≠ 0 := by
    exact fun he => (idealsOverPrime_prime K hP).ne_zero (Ideal.absNorm_eq_zero_iff.mp he)
  have hP1 : Ideal.absNorm P ≠ 1 := by
    intro he
    have := Ideal.absNorm_eq_one_iff.mp he
    exact (idealsOverPrime_prime K hP).not_isUnit (by simp [this])
  omega



end PrimeDegreePackets
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_LocalEuler
attribute [-instance] _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.infiniteAdeleRingT2Space
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply
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


namespace PrimeDegreePackets
open NumberField Finset
open scoped BigOperators ENNReal nonZeroDivisors

lemma dedekindZeta_real_eq_terms (K : Type*) [Field K] [NumberField K] (s : ℝ) :
    (NumberField.dedekindZeta K s).re =
      ∑' m : ℕ, realDirichletTerm (idealCoefficientReal K) s m := by
  simpa only [Complex.ofReal_re] using
    (congrArg Complex.re (idealDirichlet_eq_dedekindZeta K s)).symm

lemma dedekindZeta_real_antitone (K : Type*) [Field K] [NumberField K]
    {s t : ℝ} (hs : 1 < s) (hst : s ≤ t) :
    (NumberField.dedekindZeta K t).re ≤ (NumberField.dedekindZeta K s).re := by
  simp only [dedekindZeta_real_eq_terms]
  apply Summable.tsum_le_tsum _ (idealCoefficient_real_summable K (hs.trans_le hst))
    (idealCoefficient_real_summable K hs)
  intro m
  by_cases hm : m = 0
  · simp [hm]
  · change (idealCoefficientReal K m) / (m:ℝ)^t ≤ (idealCoefficientReal K m) / (m:ℝ)^s
    exact div_le_div_of_nonneg_left (idealCoefficientReal_nonneg K m)
      (Real.rpow_pos_of_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hm)) s)
      (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast Nat.pos_of_ne_zero hm) hst)



end PrimeDegreePackets
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_IntervalGeometry
attribute [-instance] _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.infiniteAdeleRingT2Space
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply
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


namespace PrimeDegreePackets
open NumberField Finset Filter Topology
open scoped BigOperators ENNReal nonZeroDivisors

lemma dedekindZeta_real_one_le (K : Type*) [Field K] [NumberField K]
    {s : ℝ} (hs : 1 < s) : 1 ≤ (NumberField.dedekindZeta K s).re := by
  rw [dedekindZeta_real_eq_terms]
  have H := (idealCoefficient_real_summable K hs).le_tsum 1
    (fun m _ => realDirichletTerm_nonneg (idealCoefficientReal_nonneg K) s m)
  simpa [realDirichletTerm,idealCoefficientReal,idealCoefficient_one] using H



end PrimeDegreePackets
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_ZetaResidues
attribute [-instance] _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
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
namespace PrimeDegreePackets

open scoped NumberField nonZeroDivisors



open scoped Pointwise



open FractionalIdeal



lemma fractionalIdeal_absNorm_pos {K : Type*} [Field K] [NumberField K]
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    0 < (FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) : ℝ) := by
  exact_mod_cast lt_of_le_of_ne (FractionalIdeal.absNorm_nonneg I.1)
    (fun h => I.ne_zero (FractionalIdeal.absNorm_eq_zero_iff.mp h.symm))

end PrimeDegreePackets
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_HaarUniqueness
attribute [-instance] _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.infiniteAdeleRingT2Space
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply
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
open scoped BigOperators Classical
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


namespace PrimeDegreePackets
open Filter Set Topology

lemma idealCoefficient_abscissa_le_one (K : Type*) [Field K] [NumberField K] :
    LSeries.abscissaOfAbsConv (fun m => (idealCoefficientReal K m : ℂ)) ≤ 1 := by
  apply LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable
  intro y hy
  exact idealCoefficient_LSeriesSummable K (by simpa using hy)

lemma dedekindZeta_differentiableAt (K : Type*) [Field K] [NumberField K]
    {s : ℂ} (hs : 1 < s.re) : DifferentiableAt ℂ (NumberField.dedekindZeta K) s := by
  have hab : LSeries.abscissaOfAbsConv (fun m => (idealCoefficientReal K m : ℂ)) < s.re :=
    (idealCoefficient_abscissa_le_one K).trans_lt (by exact_mod_cast hs)
  have H := (LSeries_hasDerivAt hab).differentiableAt
  have heq : LSeries (fun m => (idealCoefficientReal K m : ℂ)) =
      NumberField.dedekindZeta K := funext (idealCoefficient_LSeries_eq K)
  rw [heq] at H
  exact H



end PrimeDegreePackets


end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_ZetaDerivatives
attribute [-instance] _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.instNonemptyLeafTestSpace _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.infiniteAdeleRingT2Space
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
open scoped BigOperators Classical
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


namespace PrimeDegreePackets



lemma realDedekindZeta_deriv_nonpos (K : Type*) [Field K] [NumberField K]
    {s : ℝ} (hs : 1 < s) : deriv (realDedekindZeta K) s ≤ 0 := by
  have H : AntitoneOn (realDedekindZeta K) (Ioi 1) := by
    intro x hx y _ hxy
    exact dedekindZeta_real_antitone K hx hxy
  have HH := H.derivWithin_nonpos (x := s)
  rwa [derivWithin_of_isOpen isOpen_Ioi hs] at HH

lemma realDedekindZeta_pos (K : Type*) [Field K] [NumberField K]
    {s : ℝ} (hs : 1 < s) : 0 < realDedekindZeta K s :=
  lt_of_lt_of_le zero_lt_one (dedekindZeta_real_one_le K hs)

lemma complex_digamma_continuousAt_of_re_pos {s : ℂ} (hs : 0 < s.re) :
    ContinuousAt Complex.digamma s := by
  let D : Set ℂ := {z | 0 < z.re}
  have ho : IsOpen D := Complex.continuous_re.isOpen_preimage _ isOpen_Ioi
  have hall : ∀ z ∈ D, ∀ m : ℕ, z ≠ -(m:ℂ) := by
    intro z hz m hm
    have hh : 0 < z.re := hz
    rw [hm] at hh
    simp only [Complex.neg_re,Complex.natCast_re] at hh
    exact (not_lt_of_ge (neg_nonpos.mpr (Nat.cast_nonneg m))) hh
  have hd : DifferentiableOn ℂ Complex.Gamma D := by
    intro z hz
    exact (Complex.differentiableAt_Gamma z (hall z hz)).differentiableWithinAt
  have ha := hd.analyticOnNhd ho s hs
  exact ha.deriv.continuousAt.div ha.continuousAt (Complex.Gamma_ne_zero (hall s hs))

lemma archimedeanZetaTerm_continuousOn (n : ℕ) :
    ContinuousOn (archimedeanZetaTerm n) (Icc 1 2) := by
  intro s hs
  apply ContinuousAt.continuousWithinAt
  unfold archimedeanZetaTerm
  apply ContinuousAt.const_mul
  apply ContinuousAt.sub _ continuousAt_const
  apply Complex.continuous_re.continuousAt.comp
  have hc0 : ContinuousAt (fun t : ℝ => (t:ℂ)/2) s :=
    Complex.continuous_ofReal.continuousAt.div_const 2
  have hp : 0 < ((s:ℂ)/2).re := by
    have hs1 := hs.1
    simp only [Complex.div_ofNat_re,Complex.ofReal_re]
    positivity
  exact ContinuousAt.comp (f := fun t : ℝ => (t:ℂ)/2)
    (complex_digamma_continuousAt_of_re_pos hp) hc0

lemma archimedeanZetaTerm_bounded (n : ℕ) :
    ∃ B : ℝ, 0 < B ∧ ∀ s ∈ Icc (1:ℝ) 2, |archimedeanZetaTerm n s| ≤ B := by
  obtain ⟨B,hB⟩ := (isCompact_Icc.bddAbove_image
    (archimedeanZetaTerm_continuousOn n).abs)
  refine ⟨max B 1,lt_of_lt_of_le zero_lt_one (le_max_right _ _),?_⟩
  intro s hs
  exact (hB (Set.mem_image_of_mem _ hs)).trans (le_max_left _ _)



end PrimeDegreePackets


open MeasureTheory Filter Set Matrix
open scoped Topology Classical
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_RootOverlaps
attribute [-instance] _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.finiteIdeleGroupT2Space _root_.ideleGroupT2Space _root_.infiniteAdeleRingT2Space _root_.infiniteIdeleGroupT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.OAI.PrimeDegreePackets.totallyRealCompletedXi_one
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
open scoped BigOperators Classical
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
namespace PrimeDegreePackets
universe v

lemma complex_summable_fintype_prod {ι : Type*} [Fintype ι]
    (κ : ι → Type v) (f : ∀ i, κ i → ℂ)
    (hf : ∀ i, Summable (fun a => ‖f i a‖)) :
    Summable (fun k : ∀ i, κ i => ‖∏ i, f i (k i)‖) := by
  classical
  apply tsum_enorm_ne_top_iff_summable_norm.mp
  simp only [enorm_eq_nnnorm, nnnorm_prod, ENNReal.ofNNReal_finsetProd]
  rw [ennreal_tsum_fintype_prod κ (fun i a => (‖f i a‖₊ : ℝ≥0∞))]
  exact ENNReal.prod_ne_top (fun i _ => tsum_enorm_ne_top_iff_summable_norm.mpr (hf i))

lemma complex_tsum_fintype_prod {ι : Type*} [Fintype ι]
    (κ : ι → Type v) (f : ∀ i, κ i → ℂ)
    (hf : ∀ i, Summable (fun a => ‖f i a‖)) :
    (∑' k : ∀ i, κ i, ∏ i, f i (k i)) = ∏ i, ∑' x : κ i, f i x := by
  classical
  revert κ f
  refine Fintype.induction_empty_option (P := fun ι [Fintype ι] =>
    ∀ (κ : ι → Type v) (f : ∀ i, κ i → ℂ),
      (∀ i, Summable (fun a => ‖f i a‖)) →
      (∑' k : ∀ i, κ i, ∏ i, f i (k i)) = ∏ i, ∑' x : κ i, f i x)
    ?_ ?_ ?_ ι
  · intro α β _ e ih κ f hf
    let : Fintype α := Fintype.ofEquiv β e.symm
    have h := ih (fun i => κ (e i)) (fun i => f (e i)) (fun i => hf (e i))
    rw [← (Equiv.piCongrLeft κ e).tsum_eq]
    convert h using 1
    · apply tsum_congr
      intro k
      exact (Fintype.prod_equiv e _ _ (by intro i; simp)).symm
    · exact (Fintype.prod_equiv e _ _ (by intro i; rfl)).symm
  · intro κ f _
    simp
  · intro α _ ih κ f hf
    rw [← Equiv.piOptionEquivProd.symm.tsum_eq]
    simp only [Fintype.prod_option]
    change (∑' c : κ none × (∀ i, κ (some i)),
      f none c.1 * ∏ i, f (some i) (c.2 i)) = _
    rw [←tsum_mul_tsum_of_summable_norm (hf none)
      (complex_summable_fintype_prod _ _ (fun i => hf (some i))), ih _ _ (fun i => hf (some i))]

lemma complex_tsum_multiset_prod {α : Type*} [Fintype α]
    (f : α → ℂ) (hf : ∀ a, ‖f a‖ < 1) :
    Summable (fun m : Multiset α => ‖(m.map f).prod‖) ∧
    (∑' m : Multiset α, (m.map f).prod) = ∏ a, (1-f a)⁻¹ := by
  classical
  let e : (α → ℕ) ≃ Multiset α :=
    Finsupp.equivFunOnFinite.symm.trans Multiset.toFinsupp.symm.toEquiv
  have hm (m : Multiset α) : (m.map f).prod = ∏ a, f a ^ m.count a := by
    rw [Finset.prod_multiset_map_count]
    apply Finset.prod_subset (Finset.subset_univ _)
    intro a _ ha
    rw [Multiset.count_eq_zero.mpr (by simpa using ha),pow_zero]
  have he (k : α → ℕ) (a : α) : (e k).count a = k a := by simp [e]
  have hfS (a : α) : Summable (fun k : ℕ => ‖f a ^ k‖) := by
    simpa only [norm_pow] using summable_geometric_of_norm_lt_one
      (show ‖‖f a‖‖ < 1 by simpa using hf a)
  have hS := complex_summable_fintype_prod (fun _ : α => ℕ) (fun a k => f a ^ k) hfS
  have hT := complex_tsum_fintype_prod (fun _ : α => ℕ) (fun a k => f a ^ k) hfS
  constructor
  · rw [←e.summable_iff]
    simpa only [Function.comp_def,hm,he] using hS
  · rw [←e.tsum_eq]
    simp only [hm,he]
    rw [hT]
    apply Finset.prod_congr rfl
    intro a _
    exact tsum_geometric_of_norm_lt_one (hf a)

end PrimeDegreePackets

open NumberField Finset
namespace PrimeDegreePackets
variable (K : Type*) [Field K] [NumberField K]

lemma zetaSummand_norm_lt_one {s : ℂ} (hs : 1 < s.re) {m : ℕ} (hm : 2 ≤ m) :
    ‖riemannZetaSummandHom (Complex.ne_zero_of_one_lt_re hs) m‖ < 1 := by
  change ‖(m : ℂ)^(-s)‖ < 1
  rw [←Complex.ofReal_natCast,
    Complex.norm_cpow_eq_rpow_re_of_nonneg (Nat.cast_nonneg m)
      (Complex.re_neg_ne_zero_of_one_lt_re hs),Complex.neg_re]
  apply Real.rpow_lt_one_of_one_lt_of_neg
  · exact_mod_cast hm
  · linarith

lemma primary_ideal_complex_series {s : ℂ} (hs : 1 < s.re) {p : ℕ} :
    Summable (fun I : PrimaryIdeal K p =>
      ‖riemannZetaSummandHom (Complex.ne_zero_of_one_lt_re hs) (Ideal.absNorm I.1)‖) ∧
    (∑' I : PrimaryIdeal K p,
      riemannZetaSummandHom (Complex.ne_zero_of_one_lt_re hs) (Ideal.absNorm I.1)) =
      ∏ P : idealsOverPrime K p,
        (1-riemannZetaSummandHom (Complex.ne_zero_of_one_lt_re hs) (Ideal.absNorm P.1))⁻¹ := by
  classical
  let H := riemannZetaSummandHom (Complex.ne_zero_of_one_lt_re hs)
  have HM (m : Multiset (idealsOverPrime K p)) :
      H (Ideal.absNorm (primaryIdealMultisetEquiv K p m).1) =
        (m.map (fun P => H (Ideal.absNorm P.1))).prod := by
    rw [primaryIdealMultisetEquiv_val]
    induction m using Multiset.induction_on with
    | empty => simp
    | @cons P m ih =>
      simp only [Multiset.map_cons,Multiset.prod_cons,map_mul]
      exact congrArg (fun z => H (Ideal.absNorm P.1)*z) ih
  obtain ⟨hS,hT⟩ := complex_tsum_multiset_prod
    (fun P : idealsOverPrime K p => H (Ideal.absNorm P.1))
    (fun P => zetaSummand_norm_lt_one hs (idealsOverPrime_norm_two_le K P.2))
  constructor
  · rw [←(primaryIdealMultisetEquiv K p).summable_iff]
    change Summable (fun m => ‖H (Ideal.absNorm (primaryIdealMultisetEquiv K p m).1)‖)
    simpa only [HM] using hS
  · rw [←(primaryIdealMultisetEquiv K p).tsum_eq]
    exact (tsum_congr HM).trans hT

lemma norm_fiber_complex_tsum (m : ℕ) (hm : m ≠ 0) (F : ℕ → ℂ) :
    (∑' I : {I : Ideal (𝓞 K) // Ideal.absNorm I = m}, F (Ideal.absNorm I.1)) =
      (idealCoefficient K m : ℂ) * F m := by
  classical
  have : Finite {I : Ideal (𝓞 K) // Ideal.absNorm I = m} :=
    (Ideal.finite_setOfPred_absNorm_eq _).to_subtype
  let : Fintype {I : Ideal (𝓞 K) // Ideal.absNorm I = m} := Fintype.ofFinite _
  have he : (fun I : {I : Ideal (𝓞 K) // Ideal.absNorm I = m} => F (Ideal.absNorm I.1)) =
      (fun _ => F m) := funext (fun I => congrArg F I.2)
  rw [he,tsum_fintype,sum_const,idealCoefficient_pos K m hm,Nat.card_eq_fintype_card,
    nsmul_eq_mul,Finset.card_univ]

lemma primary_ideal_tsum_by_norm {p : ℕ} (hp : p.Prime) (H : ℕ → ℂ)
    (HS : Summable (fun I : PrimaryIdeal K p => H (Ideal.absNorm I.1))) :
    (∑' I : PrimaryIdeal K p, H (Ideal.absNorm I.1)) =
      ∑' e : ℕ, (idealCoefficient K (p^e) : ℂ) * H (p^e) := by
  have HE : Summable (fun I : Σe : ℕ, {I : Ideal (𝓞 K) // Ideal.absNorm I = p^e} =>
      H (Ideal.absNorm I.2.1)) :=
    (primaryIdealNormEquiv K p hp).summable_iff.mpr HS
  calc
    _ = ∑' I : Σe : ℕ, {I : Ideal (𝓞 K) // Ideal.absNorm I = p^e},
          H (Ideal.absNorm I.2.1) :=
      ((primaryIdealNormEquiv K p hp).tsum_eq (fun I => H (Ideal.absNorm I.1))).symm
    _ = ∑' e : ℕ, ∑' I : {I : Ideal (𝓞 K) // Ideal.absNorm I = p^e},
          H (Ideal.absNorm I.1) := HE.tsum_sigma
    _ = _ := tsum_congr (fun e => norm_fiber_complex_tsum K _ (pow_ne_zero _ hp.ne_zero) H)

lemma ideal_local_complex_euler {s : ℂ} (hs : 1 < s.re) {p : ℕ} (hp : p.Prime) :
    (∑' e : ℕ, (idealCoefficient K (p^e) : ℂ) *
      riemannZetaSummandHom (Complex.ne_zero_of_one_lt_re hs) (p^e)) =
        ∏ P : idealsOverPrime K p,
          (1-riemannZetaSummandHom (Complex.ne_zero_of_one_lt_re hs) (Ideal.absNorm P.1))⁻¹ := by
  have HD := primary_ideal_complex_series K hs (p := p)
  exact (primary_ideal_tsum_by_norm K hp _ HD.1.of_norm).symm.trans HD.2

end PrimeDegreePackets


namespace PrimeDegreePackets

lemma primePower_succ_injective : Function.Injective
    (fun a : Nat.Primes × ℕ => (a.1 : ℕ) ^ (a.2+1)) := by
  rintro ⟨p,k⟩ ⟨q,l⟩ h
  obtain ⟨hp,hk⟩ := p.property.pow_inj q.property h
  exact Prod.ext (Subtype.ext hp) hk

 

theorem complex_multiplicative_tsum_ne_zero
    (f : ℕ → ℂ) (hzero : f 0 = 0) (hone : f 1 = 1)
    (hmul : ∀ {m n : ℕ}, m.Coprime n → f (m*n) = f m * f n)
    (hs : Summable (fun m => ‖f m‖))
    (hlocal : ∀ p : Nat.Primes, (∑' k : ℕ, f ((p:ℕ)^k)) ≠ 0) :
    (∑' m : ℕ, f m) ≠ 0 := by
  let E (p : Nat.Primes) : ℂ := ∑' k : ℕ, f ((p:ℕ)^k)
  have hpS (p : Nat.Primes) : Summable (fun k : ℕ => f ((p:ℕ)^k)) :=
    hs.of_norm.comp_injective (Nat.pow_right_injective p.property.two_le)
  have hspp : Summable (fun a : Nat.Primes × ℕ => f ((a.1:ℕ)^(a.2+1))) :=
    hs.of_norm.comp_injective primePower_succ_injective
  have he (p : Nat.Primes) : E p = 1 + ∑' k : ℕ, f ((p:ℕ)^(k+1)) := by
    change (∑' k : ℕ, f ((p:ℕ)^k)) = _
    rw [(hpS p).tsum_eq_zero_add]
    simp only [pow_zero,hone]
  have hdev : Summable (fun p : Nat.Primes => 1-E p) := by
    have H := hspp.prod.neg
    exact H.congr (fun p => by dsimp; rw [he]; ring)
  have hl : Summable (fun p : Nat.Primes => Complex.log (E p)) := by
    simpa only [sub_sub_cancel] using hdev.clog_one_sub
  have hP := hl.hasSum.cexp
  have hexp (p : Nat.Primes) : Complex.exp (Complex.log (E p)) = E p :=
    Complex.exp_log (hlocal p)
  simp only [Function.comp_def,hexp] at hP
  have hE : HasProd E (∑' m : ℕ, f m) :=
    EulerProduct.eulerProduct_hasProd hone hmul hs hzero
  rw [hE.unique hP]
  exact Complex.exp_ne_zero _

end PrimeDegreePackets


namespace PrimeDegreePackets

lemma dedekindZeta_ne_zero_of_one_lt_re (K : Type*) [Field K] [NumberField K]
    {s : ℂ} (hs : 1 < s.re) : NumberField.dedekindZeta K s ≠ 0 := by
  classical
  let H := riemannZetaSummandHom (Complex.ne_zero_of_one_lt_re hs)
  let f (m : ℕ) : ℂ := (idealCoefficient K m : ℂ) * H m
  have hf (m : ℕ) : f m = LSeries.term (fun k => (idealCoefficientReal K k : ℂ)) s m := by
    by_cases hm : m = 0
    · subst m
      simp [f]
    · simp only [f,H,riemannZetaSummandHom,MonoidWithZeroHom.coe_mk,ZeroHom.coe_mk,
        LSeries.term_of_ne_zero hm,idealCoefficientReal,ArithmeticFunction.coe_mk,
        Complex.ofReal_natCast,Complex.cpow_neg,div_eq_mul_inv]
  have hS : Summable (fun m => ‖f m‖) := by
    simpa only [hf] using (idealCoefficient_LSeriesSummable K hs).norm
  have h0 : f 0 = 0 := by simp [f]
  have h1 : f 1 = 1 := by simp [f,idealCoefficient_one]
  have hm {m n : ℕ} (h : m.Coprime n) : f (m*n) = f m * f n := by
    simp only [f,(idealCoefficient_multiplicative K).map_mul_of_coprime h,
      Nat.cast_mul,map_mul]
    ring
  have hE (p : Nat.Primes) : (∑' k : ℕ, f ((p:ℕ)^k)) ≠ 0 := by
    change (∑' k : ℕ, (idealCoefficient K ((p:ℕ)^k) : ℂ) * H ((p:ℕ)^k)) ≠ 0
    rw [ideal_local_complex_euler K hs p.property]
    apply Finset.prod_ne_zero_iff.mpr
    intro P _
    apply inv_ne_zero
    intro he
    have hn := zetaSummand_norm_lt_one hs (idealsOverPrime_norm_two_le K P.2)
    rw [←sub_eq_zero.mp he,norm_one] at hn
    exact (lt_irrefl _ hn)
  have HN := complex_multiplicative_tsum_ne_zero f h0 h1 (fun h => hm h) hS hE
  have he : (∑' m : ℕ, f m) = NumberField.dedekindZeta K s := by
    calc
      _ = LSeries (fun k => (idealCoefficientReal K k : ℂ)) s := tsum_congr hf
      _ = _ := idealCoefficient_LSeries_eq K s
  rwa [he] at HN

end PrimeDegreePackets


namespace PrimeDegreePackets


lemma half_ne_nonpositive_integer {s : ℂ} (hs : 0 < s.re) (m : ℕ) :
    s/2 ≠ -(m:ℂ) := by
  intro he
  have hr := congrArg Complex.re he
  simp only [Complex.div_ofNat_re,Complex.neg_re,Complex.natCast_re] at hr
  have hm : (0:ℝ) ≤ m := Nat.cast_nonneg m
  linarith

lemma completionExponential_ne_zero (n : ℕ) (D : ℝ) (s : ℂ) :
    completionExponential n D s ≠ 0 := Complex.exp_ne_zero _

lemma completionExponential_hasDerivAt (n : ℕ) (D : ℝ) (s : ℂ) :
    HasDerivAt (completionExponential n D)
      (completionExponential n D s *
        (((Real.log D : ℝ) : ℂ) - n * (Real.log Real.pi : ℂ))/2) s := by
  have h := (((hasDerivAt_id s).mul_const
    (((Real.log D : ℝ) : ℂ) - n * (Real.log Real.pi : ℂ))).div_const 2).cexp
  change HasDerivAt (fun z : ℂ => Complex.exp
    (z * ((Real.log D : ℂ)-n*(Real.log Real.pi : ℂ))/2))
    (Complex.exp (s*((Real.log D : ℂ)-n*(Real.log Real.pi : ℂ))/2)*
      ((Real.log D : ℂ)-n*(Real.log Real.pi : ℂ))/2) s
  simpa only [one_mul,mul_div_assoc,id_eq] using h

lemma completionExponential_logDeriv (n : ℕ) (D : ℝ) (s : ℂ) :
    logDeriv (completionExponential n D) s =
      (((Real.log D : ℝ) : ℂ) - n * (Real.log Real.pi : ℂ))/2 := by
  rw [logDeriv,Pi.div_apply, (completionExponential_hasDerivAt n D s).deriv]
  field_simp [completionExponential_ne_zero]

lemma gammaHalf_hasDerivAt {s : ℂ} (hs : 0 < s.re) :
    HasDerivAt (fun z : ℂ => Complex.Gamma (z/2))
      (deriv Complex.Gamma (s/2) / 2) s := by
  have h := (Complex.differentiableAt_Gamma (s/2)
    (half_ne_nonpositive_integer hs)).hasDerivAt.comp s
      ((hasDerivAt_id s).div_const 2)
  simpa only [Function.comp_def,div_eq_mul_inv,id_eq,one_mul] using h

lemma gammaHalf_logDeriv {s : ℂ} (hs : 0 < s.re) :
    logDeriv (fun z : ℂ => Complex.Gamma (z/2)) s =
      Complex.digamma (s/2) / 2 := by
  rw [logDeriv,Pi.div_apply, (gammaHalf_hasDerivAt hs).deriv,Complex.digamma_def,logDeriv,Pi.div_apply]
  ring

lemma totallyRealCompletedXi_ne_zero (K : Type*) [Field K] [NumberField K]
    {s : ℂ} (hs : 1 < s.re) : totallyRealCompletedXi K s ≠ 0 := by
  have hs0 : s ≠ 0 := Complex.ne_zero_of_one_lt_re hs
  have hs1 : s-1 ≠ 0 := by
    intro he
    have hr := congrArg Complex.re (sub_eq_zero.mp he)
    simp [hr] at hs
  unfold totallyRealCompletedXi
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero hs0 hs1)
    (completionExponential_ne_zero _ _ _))
    (pow_ne_zero _ (Complex.Gamma_ne_zero (half_ne_nonpositive_integer (by linarith)))))
    (dedekindZeta_ne_zero_of_one_lt_re K hs)

lemma totallyRealCompletedXi_logDeriv (K : Type*) [Field K] [NumberField K]
    {s : ℂ} (hs : 1 < s.re) :
    logDeriv (totallyRealCompletedXi K) s =
      1/s + 1/(s-1) + (Real.log |(NumberField.discr K : ℝ)| : ℂ)/2 +
        logDeriv (NumberField.dedekindZeta K) s +
        (Module.finrank ℚ K : ℂ)/2 *
          (Complex.digamma (s/2) - (Real.log Real.pi : ℂ)) := by
  let n := Module.finrank ℚ K
  let D := |(NumberField.discr K : ℝ)|
  have h0 : s ≠ 0 := Complex.ne_zero_of_one_lt_re hs
  have h1 : s-1 ≠ 0 := by
    intro he
    have hr := congrArg Complex.re (sub_eq_zero.mp he)
    simp [hr] at hs
  have hG : Complex.Gamma (s/2) ≠ 0 :=
    Complex.Gamma_ne_zero (half_ne_nonpositive_integer (by linarith))
  have hE := completionExponential_ne_zero n D s
  have dG := (gammaHalf_hasDerivAt (by linarith : 0 < s.re)).differentiableAt
  have dE := (completionExponential_hasDerivAt n D s).differentiableAt
  have dZ := dedekindZeta_differentiableAt K hs
  have dS : DifferentiableAt ℂ (fun z : ℂ => z*(z-1)) s :=
    differentiableAt_id.mul (differentiableAt_id.sub_const 1)
  change logDeriv (fun z : ℂ => z*(z-1)*completionExponential n D z*
    Complex.Gamma (z/2)^n*NumberField.dedekindZeta K z) s = _
  have H1 := logDeriv_mul (f := fun z : ℂ => z) (g := fun z : ℂ => z-1) s
    h0 h1 differentiableAt_id (differentiableAt_id.sub_const 1)
  have H2 := logDeriv_mul (f := fun z : ℂ => z*(z-1))
    (g := completionExponential n D) s (mul_ne_zero h0 h1) hE dS dE
  have H3 := logDeriv_mul (f := fun z : ℂ => z*(z-1)*completionExponential n D z)
    (g := fun z : ℂ => Complex.Gamma (z/2)^n) s
    (mul_ne_zero (mul_ne_zero h0 h1) hE) (pow_ne_zero n hG)
    (dS.mul dE) (dG.pow n)
  have H4 := logDeriv_mul
    (f := fun z : ℂ => z*(z-1)*completionExponential n D z*Complex.Gamma (z/2)^n)
    (g := NumberField.dedekindZeta K) s
    (mul_ne_zero (mul_ne_zero (mul_ne_zero h0 h1) hE) (pow_ne_zero n hG))
    (dedekindZeta_ne_zero_of_one_lt_re K hs) ((dS.mul dE).mul (dG.pow n)) dZ
  rw [H4,H3,H2,H1,completionExponential_logDeriv]
  have hslog : logDeriv (fun z : ℂ => z-1) s = 1/(s-1) := by
    have h : HasDerivAt (fun z : ℂ => z-1) 1 s :=
      (hasDerivAt_id s).sub_const 1
    rw [logDeriv,Pi.div_apply,h.deriv]
  rw [hslog,logDeriv_fun_pow dG n,gammaHalf_logDeriv (by linarith),show logDeriv (fun z : ℂ => z) s = 1/s from logDeriv_id s]
  change (1/s + 1/(s-1) + ((Real.log D : ℂ)-n*(Real.log Real.pi : ℂ))/2 +
    n*(Complex.digamma (s/2)/2)) + logDeriv (NumberField.dedekindZeta K) s = _
  dsimp only [n,D]
  ring

lemma dedekindZeta_ofReal (K : Type*) [Field K] [NumberField K] (s : ℝ) :
    NumberField.dedekindZeta K (s:ℂ) = (realDedekindZeta K s : ℂ) := by
  rw [realDedekindZeta,←idealDirichlet_eq_dedekindZeta K]
  simp

lemma dedekindZeta_logDeriv_re (K : Type*) [Field K] [NumberField K]
    {s : ℝ} (hs : 1 < s) :
    (logDeriv (NumberField.dedekindZeta K) (s:ℂ)).re =
      deriv (realDedekindZeta K) s / realDedekindZeta K s := by
  have h := (dedekindZeta_differentiableAt K (s := (s:ℂ))
    (by simpa using hs)).hasDerivAt.real_of_complex
  have hd : deriv (realDedekindZeta K) s =
      (deriv (NumberField.dedekindZeta K) (s:ℂ)).re := h.deriv
  rw [logDeriv_apply,dedekindZeta_ofReal,Complex.div_ofReal_re,hd]

 

lemma totallyRealCompletedXi_logDeriv_re (K : Type*) [Field K] [NumberField K]
    {s : ℝ} (hs : 1 < s) :
    (logDeriv (totallyRealCompletedXi K) (s:ℂ)).re =
      1/s + 1/(s-1) + Real.log |(NumberField.discr K : ℝ)|/2 +
        deriv (realDedekindZeta K) s / realDedekindZeta K s +
          archimedeanZetaTerm (Module.finrank ℚ K) s := by
  rw [totallyRealCompletedXi_logDeriv K (by simpa using hs)]
  simp only [Complex.add_re,Complex.div_ofNat_re,Complex.sub_re,Complex.mul_re,
    Complex.natCast_re,Complex.ofReal_re,Complex.natCast_im,
    Complex.div_ofNat_im,zero_div,zero_mul,sub_zero,Complex.div_ofReal_re,
    Complex.one_re,dedekindZeta_logDeriv_re K hs,archimedeanZetaTerm]
  congr 3
  norm_cast

end PrimeDegreePackets
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_CoordinateLattices
attribute [-instance] _root_.CyclicCohomology.permutationSublattice_discreteTopology _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.infiniteAdeleRingT2Space
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [local instance] OAI.circleMeasurableSpace OAI.circleBorelSpace

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
open scoped BigOperators Classical
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
namespace PrimeDegreePackets.ThetaConstruction
variable {d : Type*} [Fintype d]

omit [Fintype d] in
lemma integerVector_closedEmbedding : IsClosedEmbedding (integerVector (d := d)) := by
  exact IsClosedEmbedding.piMap (fun _ => Int.isClosedEmbedding_coe_real)

lemma integerVector_tendsto : Tendsto (integerVector (d := d)) cofinite (cocompact _) := by
  simpa only [cocompact_eq_cofinite] using (integerVector_closedEmbedding (d := d)).tendsto_cocompact

lemma integerVectorInLattice_injective : Function.Injective (integerVectorInLattice (d := d)) := by
  intro z w h
  have hv := congrArg Subtype.val h
  ext i
  exact Int.cast_injective (congrFun hv i)

lemma coordinateLattice_rank : Module.finrank ℤ (coordinateLattice (d := d)) = Fintype.card d := by
  rw [ZLattice.rank ℝ (coordinateLattice (d := d))]
  simp

lemma summable_integerVector_rpow {r : ℝ} (hr : r < -(Fintype.card d : ℝ)) :
    Summable (fun z : d → ℤ => ‖integerVector z‖ ^ r) := by
  have hr' : r < -(Module.finrank ℤ (coordinateLattice (d := d)) : ℝ) := by
    simpa only [coordinateLattice_rank] using hr
  have H := ZLattice.summable_norm_rpow (coordinateLattice (d := d)) r hr'
  exact H.comp_injective (i := integerVectorInLattice (d := d))
    (integerVectorInLattice_injective (d := d))

end PrimeDegreePackets.ThetaConstruction

open MeasureTheory Set Filter Topology Module WithLp
open scoped BigOperators SchwartzMap ZeroAtInfty
namespace PrimeDegreePackets.ThetaConstruction
variable {d : Type*} [Fintype d]

 

lemma locallyNormal_of_polynomial_decay (f : C(d → ℝ,ℂ)) (p : ℕ)
    (hp : Fintype.card d < p) (C : ℝ) (hC : 0 < C)
    (hdecay : ∀ x, ‖x‖^p * ‖f x‖ ≤ C) : LocallyNormal f := by
  intro K
  obtain ⟨R,hR⟩ := K.isCompact.isBounded.subset_closedBall 0
  have hsum : Summable (fun z : d → ℤ => C * 2^p * ‖integerVector z‖ ^ (-(p:ℝ))) :=
    (summable_integerVector_rpow (by apply neg_lt_neg; exact_mod_cast hp)).mul_left _
  apply Summable.of_norm_bounded_eventually hsum
  have hz : ∀ᶠ z : d → ℤ in cofinite, 2*|R|+1 < ‖integerVector z‖ := by
    exact ((tendsto_norm_cocompact_atTop (E := d → ℝ)).comp
      (integerVector_tendsto (d := d))).eventually (eventually_gt_atTop (2*|R|+1))
  filter_upwards [hz] with z hz
  rw [norm_norm]
  apply (ContinuousMap.norm_le _ (by positivity)).mpr
  rintro ⟨x,hx⟩
  change ‖f (x + integerVector z)‖ ≤ C * 2^p * ‖integerVector z‖ ^ (-(p:ℝ))
  have hxR : ‖x‖ ≤ R := by simpa using hR hx
  have hzpos : 0 < ‖integerVector z‖ := by linarith [abs_nonneg R]
  have htri := norm_sub_le (x + integerVector z) x
  have hzle : ‖integerVector z‖/2 ≤ ‖x + integerVector z‖ := by
    simp only [add_sub_cancel_left] at htri
    linarith [le_abs_self R]
  have hwpos : 0 < ‖x + integerVector z‖ := lt_of_lt_of_le (by positivity) hzle
  have hbound : (‖integerVector z‖/2)^p * ‖f (x+integerVector z)‖ ≤ C :=
    (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hzle _) (norm_nonneg _)).trans
      (hdecay _)
  rw [Real.rpow_neg (norm_nonneg _),Real.rpow_natCast]
  apply (le_mul_inv_iff₀ (pow_pos hzpos p)).mpr
  rw [div_pow] at hbound
  have H := (div_le_iff₀ (by positivity : 0 < (2:ℝ)^p)).mp
    (show ‖f (x+integerVector z)‖ * ‖integerVector z‖^p / 2^p ≤ C by
      simpa only [div_mul_eq_mul_div,mul_comm] using hbound)
  exact H

lemma gaussian_polynomial_bound (b : ℝ) (hb : 0 < b) (p : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, |t|^p * Real.exp (-b*t^2) ≤ C := by
  let h : C₀(ℝ,ℝ) := {
    toFun t := |t|^p * Real.exp (-b*t^2)
    continuous_toFun := by fun_prop
    zero_at_infty' := by
      simpa only [Real.rpow_natCast] using
        tendsto_rpow_abs_mul_exp_neg_mul_sq_cocompact hb (p:ℝ) }
  refine ⟨‖h.toBCF‖+1,by positivity,fun t => ?_⟩
  have H := BoundedContinuousFunction.norm_coe_le_norm h.toBCF t
  exact (le_abs_self (h t)).trans (H.trans (by linarith))

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma coordinateGaussian_decay (A : (d → ℝ) ≃L[ℝ] E) (b : ℝ) (hb : 0 < b) (p : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ x, ‖x‖^p * ‖coordinateGaussian A b x‖ ≤ C := by
  obtain ⟨C,hC,hbound⟩ := gaussian_polynomial_bound b hb p
  let B := ‖A.symm.toContinuousLinearMap‖ + 1
  have hB : 0 < B := by dsimp [B] <;> positivity
  refine ⟨B^p*C,by positivity,fun x => ?_⟩
  have hx : ‖x‖ ≤ B * ‖A x‖ := by
    have H := A.symm.toContinuousLinearMap.le_opNorm (A x)
    simp only [ContinuousLinearEquiv.coe_coe,ContinuousLinearEquiv.symm_apply_apply] at H
    exact H.trans (by dsimp [B] <;> nlinarith [norm_nonneg (A x)])
  have hnorm : ‖coordinateGaussian A b x‖ = Real.exp (-b*‖A x‖^2) := by
    simp [coordinateGaussian,Complex.norm_exp,pow_two]
  rw [hnorm]
  calc
    _ ≤ (B*‖A x‖)^p * Real.exp (-b*‖A x‖^2) :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hx _) (Real.exp_nonneg _)
    _ = B^p * (‖A x‖^p * Real.exp (-b*‖A x‖^2)) := by rw [mul_pow,mul_assoc]
    _ ≤ B^p*C := mul_le_mul_of_nonneg_left (by simpa only [abs_norm] using hbound ‖A x‖)
      (pow_nonneg hB.le _)

lemma coordinateGaussian_locallyNormal (A : (d → ℝ) ≃L[ℝ] E) (b : ℝ) (hb : 0 < b) :
    LocallyNormal (coordinateGaussian A b) := by
  obtain ⟨C,hC,hdecay⟩ := coordinateGaussian_decay A b hb (Fintype.card d + 1)
  exact locallyNormal_of_polynomial_decay _ _ (Nat.lt_succ_self _) C hC hdecay

end PrimeDegreePackets.ThetaConstruction

open scoped FourierTransform

open scoped BigOperators SchwartzMap FourierTransform

open scoped BigOperators FourierTransform
namespace PrimeDegreePackets.ThetaConstruction
variable {d : Type*} [Fintype d]



lemma summable_of_locallyNormal (f : C(d → ℝ,ℂ)) (hf : LocallyNormal f) :
    Summable (fun z : d → ℤ => f (integerVector z)) := by
  have H := ContinuousMap.summable_of_locally_summable_norm hf
  have H' := (ContinuousMap.evalCLM ℂ (x := (0:d→ℝ))).summable H
  simpa [translate] using H'

lemma latticeTheta_summable (B : EuclideanSpace ℝ d ≃L[ℝ] EuclideanSpace ℝ d)
    (b : ℝ) (hb : 0 < b) :
    Summable (fun z : d → ℤ => Complex.exp (-(b:ℂ) * ‖B (euclideanInteger z)‖^2)) := by
  exact summable_of_locallyNormal (coordinateGaussian (coordinateBasis B) b)
    (coordinateGaussian_locallyNormal _ b hb)

end PrimeDegreePackets.ThetaConstruction

open MeasureTheory Set Filter Topology Module WithLp Asymptotics
namespace PrimeDegreePackets.ThetaConstruction
variable {d : Type*} [Fintype d]

lemma thetaRemainder_summable (B : EuclideanSpace ℝ d ≃L[ℝ] EuclideanSpace ℝ d)
    {t : ℝ} (ht : 0 < t) : Summable (fun z : NonzeroIntegerVector d =>
      Complex.exp (-(t:ℂ) * ‖B (euclideanInteger z.1)‖^2)) :=
  (latticeTheta_summable B t ht).subtype _

lemma gaussianTerm_norm (t r : ℝ) :
    ‖Complex.exp (-(t:ℂ) * (r:ℂ)^2)‖ = Real.exp (-t*r^2) := by
  simp [Complex.norm_exp,pow_two]

lemma euclideanInteger_norm_one_le (z : NonzeroIntegerVector d) :
    1 ≤ ‖euclideanInteger z.1‖ := by
  obtain ⟨i,hi⟩ : ∃ i, z.1 i ≠ 0 := by
    by_contra! H
    exact z.2 (funext H)
  have H : (1:ℝ) ≤ |(z.1 i:ℝ)| := by exact_mod_cast Int.one_le_abs hi
  exact H.trans (by simpa [euclideanInteger,integerVector,Real.norm_eq_abs] using
    PiLp.norm_apply_le (euclideanInteger z.1) i)

end PrimeDegreePackets.ThetaConstruction
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_LatticeTheta
attribute [-instance] _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
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
open scoped BigOperators Classical
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
namespace PrimeDegreePackets
open ThetaConstruction
variable {n : ℕ} {K : Type*} [Field K] [NumberField K]

lemma fullLatticeEuclideanBasis_det (M : FullLattice n K) (σ : OrderedEmbeddings n K)
    (hn : Module.finrank ℚ K = n) :
    LinearMap.det (fullLatticeEuclideanBasis M σ hn).toLinearMap = (embeddingMatrix M σ).det := by
  change LinearMap.det ((Matrix.toLin (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
    (EuclideanSpace.basisFun (Fin n) ℝ).toBasis) (embeddingMatrix M σ).transpose) = _
  rw [LinearMap.det_toLin,Matrix.det_transpose]

end PrimeDegreePackets


open Module MeasureTheory
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_ThetaTails
attribute [-instance] _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.OAI.PrimeDegreePackets.instSecondCountableTopologyLeafTestSpace _root_.OAI.PrimeDegreePackets.rootSliceSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.finiteIdeleGroupT2Space _root_.ideleGroupT2Space _root_.infiniteAdeleRingT2Space _root_.infiniteIdeleGroupT2Space
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue
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
open scoped BigOperators Classical
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
namespace PrimeDegreePackets.ThetaConstruction
variable {d : Type*} [Fintype d]

 

theorem thetaRemainder_uniform_exponential_bound (R : ℝ) (hR : 0 ≤ R) :
    ∃ a C : ℝ, 0 < a ∧ 0 ≤ C ∧
      ∀ (B : EuclideanSpace ℝ d ≃L[ℝ] EuclideanSpace ℝ d),
        ‖B.symm.toContinuousLinearMap‖ ≤ R → ∀ t : ℝ, 1 ≤ t →
          ‖thetaRemainder B t‖ ≤ C * Real.exp (-a*t) := by
  let c : ℝ := (R+1)⁻¹
  have hc : 0 < c := inv_pos.mpr (by linarith)
  let a : ℝ := c^2/2
  have ha : 0 < a := by dsimp [a] <;> positivity
  let v := fun z : NonzeroIntegerVector d => Real.exp (-a*‖euclideanInteger z.1‖^2)
  have hv : Summable v := by
    have H := (thetaRemainder_summable (ContinuousLinearEquiv.refl ℝ (EuclideanSpace ℝ d)) ha).norm
    simpa only [ContinuousLinearEquiv.refl_apply,gaussianTerm_norm] using H
  refine ⟨a,∑' z, v z,ha,tsum_nonneg (fun z => (Real.exp_pos _).le),fun B hB t ht => ?_⟩
  have hbound (z : NonzeroIntegerVector d) : c*‖euclideanInteger z.1‖ ≤ ‖B (euclideanInteger z.1)‖ := by
    have H := B.symm.toContinuousLinearMap.le_opNorm (B (euclideanInteger z.1))
    simp only [ContinuousLinearEquiv.coe_coe,ContinuousLinearEquiv.symm_apply_apply] at H
    have HR : 0 < R+1 := by linarith
    rw [show c*‖euclideanInteger z.1‖ = ‖euclideanInteger z.1‖/(R+1) by dsimp [c]; ring,
      div_le_iff₀ HR]
    calc
      ‖euclideanInteger z.1‖ ≤ ‖B.symm.toContinuousLinearMap‖ * ‖B (euclideanInteger z.1)‖ := H
      _ ≤ ‖B (euclideanInteger z.1)‖*(R+1) := by nlinarith [norm_nonneg (B (euclideanInteger z.1))]
  have ht' : 0 < t := by linarith
  calc
    ‖thetaRemainder B t‖ ≤ ∑' z : NonzeroIntegerVector d,
        ‖Complex.exp (-(t:ℂ)*‖B (euclideanInteger z.1)‖^2)‖ :=
      norm_tsum_le_tsum_norm (thetaRemainder_summable B ht').norm
    _ ≤ ∑' z, v z * Real.exp (-a*t) := by
      apply (thetaRemainder_summable B ht').norm.tsum_le_tsum _ (hv.mul_right _)
      intro z
      rw [gaussianTerm_norm]
      dsimp only [v]
      rw [←Real.exp_add]
      apply Real.exp_le_exp.mpr
      have hx := euclideanInteger_norm_one_le z
      have hy := hbound z
      have hx2 : 1 ≤ ‖euclideanInteger z.1‖^2 := by nlinarith
      have hcsq : c^2 * ‖euclideanInteger z.1‖^2 ≤ ‖B (euclideanInteger z.1)‖^2 := by
        have H := (sq_le_sq₀ (mul_nonneg hc.le (norm_nonneg _)) (norm_nonneg _)).mpr hy
        simpa only [mul_pow] using H
      have h1 := mul_nonneg (sub_nonneg.mpr ht) (mul_nonneg (sq_nonneg c)
        (sq_nonneg ‖euclideanInteger z.1‖))
      have h2 := mul_nonneg ht'.le (sub_nonneg.mpr hcsq)
      have h3 := mul_nonneg (sq_nonneg c) (sub_nonneg.mpr hx2)
      have h4 := mul_nonneg ht'.le h3
      dsimp only [a]
      nlinarith
    _ = _ := tsum_mul_right

end PrimeDegreePackets.ThetaConstruction


namespace PrimeDegreePackets.ThetaConstruction
variable {d : Type*} [Fintype d]
variable {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
variable (B : α → EuclideanSpace ℝ d ≃L[ℝ] EuclideanSpace ℝ d)

omit [IsFiniteMeasure μ] in
lemma normalizedThetaTail_joint_stronglyMeasurable
    (hB : ∀ z : d → ℤ, Measurable (fun x => B x (euclideanInteger z))) :
    StronglyMeasurable (fun p : α × ℝ => normalizedThetaTail (B p.1) p.2) := by
  have HH : Measurable (fun p : α × ℝ => thetaRemainder (B p.1) (Real.pi*max p.2 1)) := by
    unfold thetaRemainder
    apply Measurable.tsum
    intro z
    have HB : Measurable (fun p : α × ℝ => B p.1 (euclideanInteger z.1)) :=
      (hB z.1).comp measurable_fst
    fun_prop
  have HP : MeasurableSet {p : α × ℝ | 1 < p.2} :=
    measurableSet_lt measurable_const measurable_snd
  apply Measurable.stronglyMeasurable
  convert HH.indicator HP using 1
  all_goals try with_reducible_and_instances rfl
  ext p
  simp only [normalizedThetaTail,Set.indicator_apply]
  rfl


omit [IsFiniteMeasure μ] in
lemma averagedNormalizedThetaTail_eq_zero {t : ℝ} (ht : t ≤ 1) :
    averagedNormalizedThetaTail μ B t = 0 := by
  simp [averagedNormalizedThetaTail,normalizedThetaTail,not_lt.mpr ht]

lemma averagedNormalizedThetaTail_stronglyMeasurable
    (hB : StronglyMeasurable (fun p : α × ℝ => normalizedThetaTail (B p.1) p.2)) :
    StronglyMeasurable (averagedNormalizedThetaTail μ B) :=
  hB.integral_prod_left'

lemma averagedNormalizedThetaTail_bounds (R : ℝ) (hR : 0 ≤ R)
    (hB : ∀ x, ‖(B x).symm.toContinuousLinearMap‖ ≤ R) :
    ∃ a C : ℝ, 0 < a ∧ 0 ≤ C ∧
      (∀ t : ℝ, ‖averagedNormalizedThetaTail μ B t‖ ≤ C) ∧
      ∀ t : ℝ, 1 < t → ‖averagedNormalizedThetaTail μ B t‖ ≤ C * Real.exp (-a*t) := by
  obtain ⟨a,C,ha,hC,hbound⟩ := thetaRemainder_uniform_exponential_bound (d := d) R hR
  have Hb (t : ℝ) (ht : 1 < t) :
      ‖averagedNormalizedThetaTail μ B t‖ ≤ (C*μ.real Set.univ) * Real.exp (-(a*Real.pi)*t) := by
    have HP : 1 ≤ Real.pi*t := by nlinarith [Real.pi_gt_three]
    have HH := norm_integral_le_of_norm_le_const (μ := μ)
      (Filter.Eventually.of_forall (fun x => hbound (B x) (hB x) (Real.pi*t) HP))
    have HE : averagedNormalizedThetaTail μ B t = ∫ x, thetaRemainder (B x) (Real.pi*t) ∂μ := by
      simp only [averagedNormalizedThetaTail,normalizedThetaTail,
        Set.indicator_of_mem (show t ∈ Set.Ioi 1 from ht),max_eq_left ht.le]
    rw [HE]
    rw [show -a*(Real.pi*t) = -(a*Real.pi)*t by ring] at HH
    simpa only [mul_assoc,mul_left_comm,mul_comm] using HH
  refine ⟨a*Real.pi,C*μ.real Set.univ,mul_pos ha Real.pi_pos,
    mul_nonneg hC (measureReal_nonneg),?_,Hb⟩
  intro t
  by_cases ht : 1 < t
  · apply (Hb t ht).trans
    apply mul_le_of_le_one_right (mul_nonneg hC (measureReal_nonneg))
    rw [Real.exp_le_one_iff]
    have := mul_pos (mul_pos ha Real.pi_pos) (zero_lt_one.trans ht)
    nlinarith
  · rw [averagedNormalizedThetaTail_eq_zero μ B (not_lt.mp ht),norm_zero]
    positivity

lemma averagedNormalizedThetaTail_locallyIntegrable (R : ℝ) (hR : 0 ≤ R)
    (hbound : ∀ x, ‖(B x).symm.toContinuousLinearMap‖ ≤ R)
    (hB : StronglyMeasurable (fun p : α × ℝ => normalizedThetaTail (B p.1) p.2)) :
    LocallyIntegrable (averagedNormalizedThetaTail μ B) := by
  obtain ⟨a,C,ha,hC,hall,_⟩ := averagedNormalizedThetaTail_bounds μ B R hR hbound
  rw [locallyIntegrable_iff]
  intro k hk
  have : IsFiniteMeasure (volume.restrict k) := isFiniteMeasure_restrict.mpr hk.measure_lt_top.ne
  exact (integrable_const C).mono'
    (averagedNormalizedThetaTail_stronglyMeasurable μ B hB).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun t => hall t))

omit [IsFiniteMeasure μ] in
lemma averagedNormalizedThetaTail_bigO_zero (b : ℝ) :
    averagedNormalizedThetaTail μ B =O[𝓝[>] 0] (fun t : ℝ => t^(-b)) := by
  apply IsBigO.of_bound 0
  have H : ∀ᶠ t : ℝ in 𝓝[>] 0, t < 1 :=
    eventually_nhdsWithin_of_eventually_nhds (eventually_lt_nhds zero_lt_one)
  filter_upwards [H] with t ht
  simp [averagedNormalizedThetaTail_eq_zero μ B ht.le]

 

theorem averagedNormalizedThetaTail_mellin_differentiable (R : ℝ) (hR : 0 ≤ R)
    (hbound : ∀ x, ‖(B x).symm.toContinuousLinearMap‖ ≤ R)
    (hB : StronglyMeasurable (fun p : α × ℝ => normalizedThetaTail (B p.1) p.2)) :
    Differentiable ℂ (mellin (averagedNormalizedThetaTail μ B)) := by
  obtain ⟨a,C,ha,_,_,hdecay⟩ := averagedNormalizedThetaTail_bounds μ B R hR hbound
  have Hdecay : averagedNormalizedThetaTail μ B =O[atTop] (fun t => Real.exp (-a*t)) := by
    apply IsBigO.of_bound C
    filter_upwards [eventually_gt_atTop (1:ℝ)] with t ht
    simpa only [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)] using hdecay t ht
  intro s
  exact mellin_differentiableAt_of_isBigO_rpow_exp ha
    ((averagedNormalizedThetaTail_locallyIntegrable μ B R hR hbound hB).locallyIntegrableOn (Set.Ioi 0))
    Hdecay (averagedNormalizedThetaTail_bigO_zero μ B (s.re-1)) (by linarith)

end PrimeDegreePackets.ThetaConstruction


namespace PrimeDegreePackets.ThetaConstruction
variable {d : Type*} [Fintype d]


lemma logScale_symm (u : d → ℝ) : (logScale u).symm = logScale (-u) := by
  ext x i
  rfl

lemma logScale_norm_le {u : d → ℝ} {R : ℝ} (hR : ∀ i, u i ≤ R)
    (x : EuclideanSpace ℝ d) : ‖logScale u x‖ ≤ Real.exp R*‖x‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.exp_pos _).le (norm_nonneg _))).mp
  rw [mul_pow,EuclideanSpace.real_norm_sq_eq,EuclideanSpace.real_norm_sq_eq,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  rw [logScale_apply,mul_pow]
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  exact (sq_le_sq₀ (Real.exp_pos _).le (Real.exp_pos _).le).mpr (Real.exp_le_exp.mpr (hR i))

lemma logScaledLattice_inverse_bound (B : EuclideanSpace ℝ d ≃L[ℝ] EuclideanSpace ℝ d)
    {u : d → ℝ} {R : ℝ} (hR : ∀ i, -u i ≤ R) :
    ‖(logScaledLattice B u).symm.toContinuousLinearMap‖ ≤
      ‖B.symm.toContinuousLinearMap‖*Real.exp R := by
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (norm_nonneg _) (Real.exp_pos _).le)
  intro x
  change ‖B.symm ((logScale u).symm x)‖ ≤ _
  calc
    _ ≤ ‖B.symm.toContinuousLinearMap‖*‖(logScale u).symm x‖ :=
      B.symm.toContinuousLinearMap.le_opNorm _
    _ ≤ ‖B.symm.toContinuousLinearMap‖*(Real.exp R*‖x‖) := by
      gcongr
      rw [logScale_symm]
      exact logScale_norm_le hR x
    _ = _ := by ring

lemma logScaledLattice_measurable_apply {α : Type*} [MeasurableSpace α]
    (B : EuclideanSpace ℝ d ≃L[ℝ] EuclideanSpace ℝ d) (u : α → d → ℝ)
    (hu : ∀ i, Measurable (fun a => u a i)) (x : EuclideanSpace ℝ d) :
    Measurable (fun a => logScaledLattice B (u a) x) := by
  change Measurable (fun a => toLp 2 (fun i => Real.exp (u a i)*(B x) i))
  exact (PiLp.continuous_toLp 2 (fun _ : d => ℝ)).measurable.comp (Measurable.of_eval (fun i =>
    ((hu i).exp).mul_const _))



end PrimeDegreePackets.ThetaConstruction


namespace PrimeDegreePackets
open ThetaConstruction


lemma restoredLogCoordinates_continuous {d : ℕ} (i : Fin (d+1)) :
    Continuous (fun u : LogCoordinates d => restoredLogCoordinates u i) := by
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [restoredLogCoordinates,Fin.snoc_last]
    fun_prop
  · simp only [restoredLogCoordinates,Fin.snoc_castSucc]
    exact continuous_apply j

end PrimeDegreePackets


namespace PrimeDegreePackets.ThetaConstruction
variable {d : Type*} [Fintype d]

lemma exponentialTail_mellinConvergent {a : ℝ} (ha : 0 < a) (s : ℂ) :
    MellinConvergent (exponentialTail a) s := by
  have HL : LocallyIntegrable (exponentialTail a) :=
    (show Continuous (fun t : ℝ => (Real.exp (-a*t):ℂ)) by fun_prop).locallyIntegrable.indicator
      measurableSet_Ioi
  have HE : exponentialTail a =O[atTop] (fun t => Real.exp (-a*t)) := by
    apply IsBigO.of_bound 1
    filter_upwards [eventually_gt_atTop (1:ℝ)] with t ht
    simp [exponentialTail,ht,Complex.norm_exp]
  have HZ : exponentialTail a =O[𝓝[>] 0] (fun t : ℝ => t^(-(s.re-1))) := by
    apply IsBigO.of_bound 0
    have H : ∀ᶠ t : ℝ in 𝓝[>] 0, t < 1 :=
      eventually_nhdsWithin_of_eventually_nhds (eventually_lt_nhds zero_lt_one)
    filter_upwards [H] with t ht
    simp [exponentialTail,not_lt.mpr ht.le]
  exact mellinConvergent_of_isBigO_rpow_exp ha (HL.locallyIntegrableOn (Set.Ioi 0)) HE HZ (by linarith)

lemma normalizedThetaTail_uniform_majorant (R : ℝ) (hR : 0 ≤ R) :
    ∃ a C : ℝ, 0 < a ∧ 0 ≤ C ∧
      ∀ (B : EuclideanSpace ℝ d ≃L[ℝ] EuclideanSpace ℝ d),
        ‖B.symm.toContinuousLinearMap‖ ≤ R → ∀ t : ℝ,
          ‖normalizedThetaTail B t‖ ≤ C * ‖exponentialTail a t‖ := by
  obtain ⟨a,C,ha,hC,hbound⟩ := thetaRemainder_uniform_exponential_bound (d := d) R hR
  refine ⟨a*Real.pi,C,mul_pos ha Real.pi_pos,hC,fun B hB t => ?_⟩
  by_cases ht : 1 < t
  · have H := hbound B hB (Real.pi*t) (by nlinarith [Real.pi_gt_three])
    simpa [normalizedThetaTail,exponentialTail,ht,max_eq_left ht.le,
      Real.norm_eq_abs,abs_of_pos (Real.exp_pos _),mul_assoc,Complex.norm_exp] using H
  · simp [normalizedThetaTail,exponentialTail,ht]

 
theorem normalizedThetaTail_mellin_integrableProd
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    (B : α → EuclideanSpace ℝ d ≃L[ℝ] EuclideanSpace ℝ d)
    (R : ℝ) (hR : 0 ≤ R) (hbound : ∀ x, ‖(B x).symm.toContinuousLinearMap‖ ≤ R)
    (hB : StronglyMeasurable (fun p : α × ℝ => normalizedThetaTail (B p.1) p.2)) (s : ℂ) :
    Integrable (fun p : α × ℝ => (p.2:ℂ)^(s-1) * normalizedThetaTail (B p.1) p.2)
      (μ.prod (volume.restrict (Set.Ioi 0))) := by
  let ν : Measure ℝ := volume.restrict (Set.Ioi 0)
  obtain ⟨a,C,ha,_,hmajorant⟩ := normalizedThetaTail_uniform_majorant (d := d) R hR
  let F : α × ℝ → ℂ := fun p => (p.2:ℂ)^(s-1) * normalizedThetaTail (B p.1) p.2
  let g : ℝ → ℂ := fun t => (t:ℂ)^(s-1) * exponentialTail a t
  have hg : Integrable g ν := exponentialTail_mellinConvergent ha s
  have hF : AEStronglyMeasurable F (μ.prod ν) := by
    apply StronglyMeasurable.aestronglyMeasurable
    exact ((Complex.measurable_ofReal.comp measurable_snd).pow_const (s-1)).stronglyMeasurable.mul hB
  have HF : Integrable F (μ.prod ν) := by
    apply ((integrable_const C).mul_prod hg.norm).mono' hF
    apply Filter.Eventually.of_forall
    intro p
    change ‖(p.2:ℂ)^(s-1) * normalizedThetaTail (B p.1) p.2‖ ≤
      C * ‖(p.2:ℂ)^(s-1) * exponentialTail a p.2‖
    simp only [norm_mul]
    calc
      _ ≤ ‖(p.2:ℂ)^(s-1)‖*(C*‖exponentialTail a p.2‖) :=
        mul_le_mul_of_nonneg_left (hmajorant (B p.1) (hbound p.1) p.2) (norm_nonneg _)
      _ = _ := by ring
  exact HF

lemma normalizedThetaTail_mellin_integrable
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    (B : α → EuclideanSpace ℝ d ≃L[ℝ] EuclideanSpace ℝ d)
    (R : ℝ) (hR : 0 ≤ R) (hbound : ∀ x, ‖(B x).symm.toContinuousLinearMap‖ ≤ R)
    (hB : StronglyMeasurable (fun p : α × ℝ => normalizedThetaTail (B p.1) p.2)) (s : ℂ) :
    Integrable (fun x => mellin (normalizedThetaTail (B x)) s) μ := by
  simpa only [mellin,smul_eq_mul] using
    (normalizedThetaTail_mellin_integrableProd μ B R hR hbound hB s).integral_prod_left

 

theorem averagedNormalizedThetaTail_mellin_eq_integral
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    (B : α → EuclideanSpace ℝ d ≃L[ℝ] EuclideanSpace ℝ d)
    (R : ℝ) (hR : 0 ≤ R) (hbound : ∀ x, ‖(B x).symm.toContinuousLinearMap‖ ≤ R)
    (hB : StronglyMeasurable (fun p : α × ℝ => normalizedThetaTail (B p.1) p.2)) (s : ℂ) :
    mellin (averagedNormalizedThetaTail μ B) s =
      ∫ x, mellin (normalizedThetaTail (B x)) s ∂μ := by
  let ν : Measure ℝ := volume.restrict (Set.Ioi 0)
  have HF := normalizedThetaTail_mellin_integrableProd μ B R hR hbound hB s
  calc
    mellin (averagedNormalizedThetaTail μ B) s =
        ∫ t, ∫ x, (t:ℂ)^(s-1) * normalizedThetaTail (B x) t ∂μ ∂ν := by
      unfold mellin averagedNormalizedThetaTail
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun t => (integral_const_mul _ _).symm)
    _ = ∫ x, ∫ t, (t:ℂ)^(s-1) * normalizedThetaTail (B x) t ∂ν ∂μ :=
      (integral_integral_swap HF).symm
    _ = _ := rfl

end PrimeDegreePackets.ThetaConstruction
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_LatticeDuality
attribute [-instance] _root_.CyclicCohomology.permutationSublattice_discreteTopology _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.OAI.PrimeDegreePackets.instNonemptyLeafTestSpace _root_.OAI.PrimeDegreePackets.instSecondCountableTopologyLeafTestSpace _root_.OAI.PrimeDegreePackets.rootSliceSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue
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
open scoped BigOperators Classical
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
namespace PrimeDegreePackets.ThetaConstruction
variable {d : Type*} [Fintype d]

lemma logScale_selfAdjoint (u : d → ℝ) :
    (logScale u).toContinuousLinearMap.adjoint = (logScale u).toContinuousLinearMap := by
  symm
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro x y
  simp only [PiLp.inner_apply,ContinuousLinearEquiv.coe_coe,logScale_apply]
  apply Finset.sum_congr rfl
  intro i _
  simp [mul_assoc,mul_left_comm,mul_comm]

lemma adjointEquiv_logScaledLattice (B : EuclideanSpace ℝ d ≃L[ℝ] EuclideanSpace ℝ d)
    (u : d → ℝ) :
    adjointEquiv (logScaledLattice B u).symm =
      logScaledLattice (adjointEquiv B.symm) (-u) := by
  have HE : (logScaledLattice B u).symm.toContinuousLinearMap =
      B.symm.toContinuousLinearMap.comp (logScale u).symm.toContinuousLinearMap := by
    ext x
    rfl
  apply ContinuousLinearEquiv.ext
  funext x
  change ((logScaledLattice B u).symm.toContinuousLinearMap.adjoint) x = _
  rw [HE,ContinuousLinearMap.adjoint_comp,logScale_symm,logScale_selfAdjoint]
  rfl

lemma logScale_det (u : d → ℝ) :
    LinearMap.det (logScale u).toLinearMap = Real.exp (∑ i, u i) := by
  classical
  let b := (EuclideanSpace.basisFun d ℝ).toBasis
  have HE : (logScale u).toLinearMap = Matrix.toLin b b (Matrix.diagonal (fun i => Real.exp (u i))) := by
    ext x i
    rw [Matrix.toLin_apply]
    simp [b,EuclideanSpace.basisFun_apply,Matrix.mulVec,Matrix.diagonal_apply,Pi.single_apply,dotProduct]
  rw [HE,LinearMap.det_toLin,Matrix.det_diagonal,Real.exp_sum]

lemma logScaledLattice_det (B : EuclideanSpace ℝ d ≃L[ℝ] EuclideanSpace ℝ d)
    (u : d → ℝ) :
    LinearMap.det (logScaledLattice B u).toLinearMap =
      Real.exp (∑ i, u i) * LinearMap.det B.toLinearMap := by
  change LinearMap.det ((logScale u).toLinearMap.comp B.toLinearMap) = _
  rw [LinearMap.det_comp,logScale_det]

end PrimeDegreePackets.ThetaConstruction


namespace PrimeDegreePackets
open ThetaConstruction

lemma restoredLogCoordinates_sum {d : ℕ} (u : LogCoordinates d) :
    ∑ i, restoredLogCoordinates u i = 0 := by
  simp [restoredLogCoordinates,Fin.sum_univ_castSucc]

end PrimeDegreePackets


namespace PrimeDegreePackets.ThetaConstruction
variable {d : Type*} [Fintype d]

 

theorem averagedThetaMellinXi_differentiable
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    (B : α → EuclideanSpace ℝ d ≃L[ℝ] EuclideanSpace ℝ d)
    (R T : ℝ) (hR : 0 ≤ R) (hT : 0 ≤ T)
    (hbound : ∀ x, ‖(B x).symm.toContinuousLinearMap‖ ≤ R)
    (hdual : ∀ x, ‖(adjointEquiv (B x).symm).symm.toContinuousLinearMap‖ ≤ T)
    (hB : StronglyMeasurable (fun p : α × ℝ => normalizedThetaTail (B p.1) p.2))
    (hD : StronglyMeasurable (fun p : α × ℝ =>
      normalizedThetaTail (adjointEquiv (B p.1).symm) p.2))
    (c : ℂ) (hc : ∀ x, ((|(LinearMap.det (B x).toLinearMap)⁻¹|:ℝ):ℂ) = c) :
    Differentiable ℂ (fun s => ∫ x, thetaMellinXi (B x) s ∂μ) := by
  let a : ℂ := (Fintype.card d:ℂ)/2
  let P := mellin (averagedNormalizedThetaTail μ B)
  let Q := mellin (averagedNormalizedThetaTail μ (fun x => adjointEquiv (B x).symm))
  have HP : Differentiable ℂ P := averagedNormalizedThetaTail_mellin_differentiable μ B R hR hbound hB
  have HQ : Differentiable ℂ Q := averagedNormalizedThetaTail_mellin_differentiable μ _ T hT hdual hD
  have HE : (fun s => ∫ x, thetaMellinXi (B x) s ∂μ) =
      fun s => s*(s-a)*(P s+c*Q (a-s)) + (μ.real Set.univ:ℂ)*(c*s-(s-a)) := by
    funext s
    have hP := normalizedThetaTail_mellin_integrable μ B R hR hbound hB s
    have hQ := normalizedThetaTail_mellin_integrable μ _ T hT hdual hD (a-s)
    have hQc : Integrable (fun x => c*mellin (normalizedThetaTail (adjointEquiv (B x).symm)) (a-s)) μ := hQ.const_mul c
    have hPQ : Integrable (fun x => mellin (normalizedThetaTail (B x)) s +
        c*mellin (normalizedThetaTail (adjointEquiv (B x).symm)) (a-s)) μ := hP.add hQc
    have hPQc : Integrable (fun x => s*(s-a)*(mellin (normalizedThetaTail (B x)) s +
        c*mellin (normalizedThetaTail (adjointEquiv (B x).symm)) (a-s))) μ := hPQ.const_mul _
    have HPv := averagedNormalizedThetaTail_mellin_eq_integral μ B R hR hbound hB s
    have HQv := averagedNormalizedThetaTail_mellin_eq_integral μ _ T hT hdual hD (a-s)
    calc
      (∫ x, thetaMellinXi (B x) s ∂μ) = ∫ x,
          s*(s-a)*(mellin (normalizedThetaTail (B x)) s +
            c*mellin (normalizedThetaTail (adjointEquiv (B x).symm)) (a-s)) +
          (c*s-(s-a)) ∂μ := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun x => by simp only [thetaMellinXi,hc x]; dsimp [a] <;> ring)
      _ = s*(s-a)*(P s+c*Q (a-s)) + (μ.real Set.univ:ℂ)*(c*s-(s-a)) := by
        rw [integral_add hPQc (integrable_const (c*s-(s-a))),
          integral_const_mul,integral_add hP hQc,integral_const_mul,
          integral_const,←HPv,←HQv]
        simp only [P,Q,Complex.real_smul]
  rw [HE]
  fun_prop

end PrimeDegreePackets.ThetaConstruction


namespace PrimeDegreePackets
open ThetaConstruction

lemma restoredLogCoordinates_abs_bound_on_compact {d : ℕ} {S : Set (LogCoordinates d)}
    (hS : IsCompact S) : ∃ R : ℝ, ∀ u ∈ S, ∀ i, |restoredLogCoordinates u i| ≤ R := by
  let f : LogCoordinates d → ℝ := fun u => ∑ i, |restoredLogCoordinates u i|
  have hf : Continuous f := continuous_finsetSum _ (fun i _ =>
    (restoredLogCoordinates_continuous i).abs)
  obtain ⟨R,hR⟩ := hS.bddAbove_image hf.continuousOn
  refine ⟨R,fun u hu i => le_trans ?_ (hR (Set.mem_image_of_mem f hu))⟩
  change |restoredLogCoordinates u i| ≤ ∑ j, |restoredLogCoordinates u j|
  exact Finset.single_le_sum (fun j _ => abs_nonneg (restoredLogCoordinates u j)) (Finset.mem_univ i)

 

theorem arithmeticFlowThetaXi_boundedAverage_entire {d : ℕ} {K : Type*}
    [Field K] [NumberField K] (M : FullLattice (d+1) K)
    (σ : OrderedEmbeddings (d+1) K) (hn : finrank ℚ K = d+1)
    {S : Set (LogCoordinates d)} (hS : MeasurableSet S) (hbd : Bornology.IsBounded S) :
    Differentiable ℂ (fun s => ∫ u in S,
      thetaMellinXi (logScaledLattice (fullLatticeEuclideanBasis M σ hn)
        (restoredLogCoordinates u)) s) := by
  let μ : Measure S := Measure.comap ((↑) : S → LogCoordinates d) volume
  have hμ : IsFiniteMeasure μ := ⟨by
    dsimp only [μ]
    rw [comap_subtype_coe_apply hS,Set.image_univ,Subtype.range_coe]
    exact hbd.measure_lt_top⟩
  let B := fullLatticeEuclideanBasis M σ hn
  let u : S → Fin (d+1) → ℝ := fun x => restoredLogCoordinates x.1
  let F := fun x : S => logScaledLattice B (u x)
  have hu : ∀ i, Measurable (fun x => u x i) := fun i =>
    ((restoredLogCoordinates_continuous i).comp continuous_subtype_val).measurable
  obtain ⟨U,hU⟩ := restoredLogCoordinates_abs_bound_on_compact hbd.isCompact_closure
  let R := ‖B.symm.toContinuousLinearMap‖*Real.exp U
  let T := ‖(adjointEquiv B.symm).symm.toContinuousLinearMap‖*Real.exp U
  have hR : 0 ≤ R := mul_nonneg (norm_nonneg _) (Real.exp_pos _).le
  have hT : 0 ≤ T := mul_nonneg (norm_nonneg _) (Real.exp_pos _).le
  have HB : ∀ x, ‖(F x).symm.toContinuousLinearMap‖ ≤ R := by
    intro x
    exact logScaledLattice_inverse_bound B (fun i =>
      (neg_le_abs _).trans (hU x.1 (subset_closure x.2) i))
  have HD : ∀ x, ‖(adjointEquiv (F x).symm).symm.toContinuousLinearMap‖ ≤ T := by
    intro x
    rw [show F x = logScaledLattice B (u x) from rfl,adjointEquiv_logScaledLattice]
    apply logScaledLattice_inverse_bound
    intro i
    simp only [Pi.neg_apply,neg_neg]
    exact (le_abs_self _).trans (hU x.1 (subset_closure x.2) i)
  have HM : StronglyMeasurable (fun p : S × ℝ => normalizedThetaTail (F p.1) p.2) :=
    normalizedThetaTail_joint_stronglyMeasurable (B := F)
      (fun z => logScaledLattice_measurable_apply B u hu (euclideanInteger z))
  have HN : StronglyMeasurable (fun p : S × ℝ =>
      normalizedThetaTail (adjointEquiv (F p.1).symm) p.2) := by
    have HE : (fun x => adjointEquiv (F x).symm) =
        fun x => logScaledLattice (adjointEquiv B.symm) (-u x) := by
      funext x
      exact adjointEquiv_logScaledLattice B (u x)
    simp_rw [show ∀ x, adjointEquiv (F x).symm =
      logScaledLattice (adjointEquiv B.symm) (-u x) from congrFun HE]
    exact normalizedThetaTail_joint_stronglyMeasurable
      (B := fun x => logScaledLattice (adjointEquiv B.symm) (-u x))
      (fun z => logScaledLattice_measurable_apply _ _ (fun i => (hu i).neg) (euclideanInteger z))
  have HC : ∀ x, ((|(LinearMap.det (F x).toLinearMap)⁻¹|:ℝ):ℂ) =
      ((|(embeddingMatrix M σ).det⁻¹|:ℝ):ℂ) := by
    intro x
    dsimp only [F,u]
    rw [logScaledLattice_det,restoredLogCoordinates_sum,Real.exp_zero,one_mul,
      show LinearMap.det B.toLinearMap = (embeddingMatrix M σ).det from
        fullLatticeEuclideanBasis_det M σ hn]
  have H := averagedThetaMellinXi_differentiable μ F R T hR hT HB HD HM HN _ HC
  have HE : (fun s => ∫ x, thetaMellinXi (F x) s ∂μ) =
      fun s => ∫ u in S, thetaMellinXi (logScaledLattice B (restoredLogCoordinates u)) s := by
    funext s
    exact integral_subtype_comap hS (fun u => thetaMellinXi (logScaledLattice B (restoredLogCoordinates u)) s)
  rw [HE] at H
  exact H

end PrimeDegreePackets

open MeasureTheory Module WithLp
namespace PrimeDegreePackets
open ThetaConstruction

 

theorem arithmeticFlowThetaXi_unitAverage_entire {d : ℕ} {K : Type*}
    [Field K] [NumberField K] [NumberField.IsTotallyReal K] (M : FullLattice (d+1) K)
    (σ : OrderedEmbeddings (d+1) K) (hn : finrank ℚ K = d+1) :
    Differentiable ℂ (fun s => ∫ u in orderedThetaLogDomain σ,
      thetaMellinXi (logScaledLattice (fullLatticeEuclideanBasis M σ hn)
        (restoredLogCoordinates u)) s) :=
  arithmeticFlowThetaXi_boundedAverage_entire M σ hn
    (ZSpan.fundamentalDomain_measurableSet _) (ZSpan.fundamentalDomain_isBounded _)



end PrimeDegreePackets

open scoped BigOperators NumberField nonZeroDivisors ENNReal
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_MellinGrowth
attribute [-instance] _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.instIsTopologicalRingLocalAlgebra _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.OAI.PrimeDegreePackets.rootGroupBorelSpace _root_.OAI.PrimeDegreePackets.rootGroupMeasurableSpace _root_.OAI.PrimeDegreePackets.xBorelSpace _root_.OAI.PrimeDegreePackets.xMeasurableSpace _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.infiniteAdeleRingT2Space
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply
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

 
lemma real_mellin_kernel_bound {c r t : ℝ} (hc : 0 < c) (hr : 0 < r)
    (ht : 0 < t) :
    r * Real.log t - c*t/2 ≤ r * Real.log (2*r/c) := by
  have hA : 0 < 2*r/c := by positivity
  have H := Real.log_le_sub_one_of_pos (div_pos ht hA)
  rw [Real.log_div (ne_of_gt ht) (ne_of_gt hA)] at H
  have H' := mul_le_mul_of_nonneg_left H hr.le
  have HE : r*(t/(2*r/c)) = c*t/2 := by field_simp
  rw [mul_sub, mul_sub, HE] at H'
  nlinarith

 

theorem mellin_norm_le {f : ℝ → ℂ} {c C r : ℝ} (hc : 0 < c)
    (hC : 0 ≤ C) (hr : 0 < r)
    (hzero : ∀ t, t ≤ 1 → f t = 0)
    (hbound : ∀ t, 1 < t → ‖f t‖ ≤ C * Real.exp (-c*t))
    (s : ℂ) (hs : s.re - 1 ≤ r) :
    ‖mellin f s‖ ≤ (2*C/c) * Real.exp (r * Real.log (2*r/c)) := by
  let A := Real.exp (r * Real.log (2*r/c))
  have Hpt (t : ℝ) (ht : 0 < t) :
      ‖(t:ℂ)^(s-1) * f t‖ ≤ C*A*Real.exp ((-c/2)*t) := by
    by_cases ht1 : 1 < t
    · rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht,
        Complex.sub_re, Complex.one_re]
      calc
        _ ≤ t^(s.re-1)*(C*Real.exp (-c*t)) :=
          mul_le_mul_of_nonneg_left (hbound t ht1) (Real.rpow_nonneg ht.le _)
        _ ≤ t^r*(C*Real.exp (-c*t)) :=
          mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le ht1.le hs) (by positivity)
        _ = C * Real.exp (r*Real.log t-c*t) := by
          rw [Real.rpow_def_of_pos ht, show r*Real.log t-c*t = Real.log t*r + (-c*t) by ring, Real.exp_add]
          ring
        _ ≤ C * Real.exp (r*Real.log (2*r/c) + (-c/2)*t) := by
          apply mul_le_mul_of_nonneg_left _ hC
          apply Real.exp_le_exp.mpr
          have H := real_mellin_kernel_bound hc hr ht
          linarith
        _ = _ := by rw [Real.exp_add]; dsimp [A] <;> ring
    · rw [hzero t (le_of_not_gt ht1), mul_zero, norm_zero]
      positivity
  unfold mellin
  simp only [smul_eq_mul]
  calc
    _ ≤ ∫ t in Ioi (0:ℝ), C*A*Real.exp ((-c/2)*t) := by
      apply norm_integral_le_of_norm_le
        ((integrableOn_exp_mul_Ioi (by linarith : -c/2 < 0) 0).const_mul (C*A))
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact Hpt t ht
    _ = _ := by
      rw [integral_const_mul, integral_exp_mul_Ioi (by linarith : -c/2 < 0)]
      simp only [mul_zero, Real.exp_zero]
      dsimp [A]
      field_simp

end PrimeDegreePackets.AnalyticGrowth


namespace PrimeDegreePackets.AnalyticGrowth


lemma eventually_const_le_exp_quad {ε : ℝ} (hε : 0 < ε) (B : ℝ) :
    ∀ᶠ R : ℝ in atTop, B ≤ Real.exp (ε*R^2) :=
  (Real.tendsto_exp_atTop.comp (tendsto_const_mul_pow_atTop (by decide : (2:ℕ) ≠ 0)
    hε)).eventually_ge_atTop B

lemma hasSubquadraticGrowth_const (c : ℂ) : HasSubquadraticGrowth (fun _ => c) := by
  intro ε hε
  filter_upwards [eventually_const_le_exp_quad hε ‖c‖] with R hR
  exact fun _ _ => hR

lemma HasSubquadraticGrowth.of_bound {f : ℂ → ℂ} {B : ℝ → ℝ}
    (hB : Tendsto (fun R => B R / R^2) atTop (𝓝 0))
    (hf : ∀ᶠ R : ℝ in atTop, ∀ z : ℂ, ‖z‖ ≤ R → ‖f z‖ ≤ Real.exp (B R)) :
    HasSubquadraticGrowth f := by
  intro ε hε
  filter_upwards [hf, hB.eventually (gt_mem_nhds hε), eventually_gt_atTop (0:ℝ)]
    with R hR hBR hRp
  intro z hz
  apply (hR z hz).trans
  apply Real.exp_le_exp.mpr
  exact ((div_lt_iff₀ (sq_pos_of_pos hRp)).mp hBR).le

lemma HasSubquadraticGrowth.add {f g : ℂ → ℂ}
    (hf : HasSubquadraticGrowth f) (hg : HasSubquadraticGrowth g) :
    HasSubquadraticGrowth (fun z => f z + g z) := by
  intro ε hε
  filter_upwards [hf (ε/2) (by positivity), hg (ε/2) (by positivity),
    eventually_const_le_exp_quad (by positivity : 0 < ε/2) 2] with R hR hS hT
  intro z hz
  calc
    _ ≤ ‖f z‖ + ‖g z‖ := norm_add_le _ _
    _ ≤ 2*Real.exp ((ε/2)*R^2) := by linarith [hR z hz, hS z hz]
    _ ≤ Real.exp ((ε/2)*R^2)*Real.exp ((ε/2)*R^2) :=
      mul_le_mul_of_nonneg_right hT (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

lemma HasSubquadraticGrowth.mul {f g : ℂ → ℂ}
    (hf : HasSubquadraticGrowth f) (hg : HasSubquadraticGrowth g) :
    HasSubquadraticGrowth (fun z => f z * g z) := by
  intro ε hε
  filter_upwards [hf (ε/2) (by positivity), hg (ε/2) (by positivity)] with R hR hS
  intro z hz
  calc
    _ = ‖f z‖*‖g z‖ := norm_mul _ _
    _ ≤ Real.exp ((ε/2)*R^2)*Real.exp ((ε/2)*R^2) :=
      mul_le_mul (hR z hz) (hS z hz) (norm_nonneg _) (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

lemma HasSubquadraticGrowth.neg {f : ℂ → ℂ} (hf : HasSubquadraticGrowth f) :
    HasSubquadraticGrowth (fun z => -f z) := by
  simpa only [neg_mul, one_mul] using (hasSubquadraticGrowth_const (-1)).mul hf

lemma HasSubquadraticGrowth.sub {f g : ℂ → ℂ}
    (hf : HasSubquadraticGrowth f) (hg : HasSubquadraticGrowth g) :
    HasSubquadraticGrowth (fun z => f z - g z) := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

lemma HasSubquadraticGrowth.finset_sum {ι : Type*} (S : Finset ι) (f : ι → ℂ → ℂ)
    (hf : ∀ i ∈ S, HasSubquadraticGrowth (f i)) :
    HasSubquadraticGrowth (fun z => ∑ i ∈ S, f i z) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using hasSubquadraticGrowth_const 0
  | @insert i S hi IH =>
    simpa only [Finset.sum_insert hi] using
      (hf i (Finset.mem_insert_self _ _)).add (IH (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

lemma HasSubquadraticGrowth.comp_affine {f : ℂ → ℂ} (hf : HasSubquadraticGrowth f)
    (a b : ℂ) : HasSubquadraticGrowth (fun z => f (a*z+b)) := by
  let A : ℝ := ‖a‖ + ‖b‖ + 1
  have hA : 0 < A := by dsimp [A] <;> positivity
  intro ε hε
  have H := (Tendsto.const_mul_atTop hA tendsto_id).eventually
    (hf (ε/A^2) (by positivity))
  filter_upwards [H, eventually_ge_atTop (1:ℝ)] with R hR hRp
  intro z hz
  have hzz : ‖a*z+b‖ ≤ A*R := by
    calc
      _ ≤ ‖a*z‖+‖b‖ := norm_add_le _ _
      _ = ‖a‖*‖z‖+‖b‖ := by rw [norm_mul]
      _ ≤ A*R := by dsimp [A] <;> nlinarith [mul_le_mul_of_nonneg_left hz (norm_nonneg a), norm_nonneg b]
  have HE : ε/A^2*(A*R)^2 = ε*R^2 := by field_simp
  simpa only [id_eq, HE] using hR (a*z+b) hzz

lemma tendsto_mellin_bound {a : ℝ} (ha : 0 < a) (k : ℝ) :
    Tendsto (fun R : ℝ => (k+(R+1)*Real.log (a*(R+1)))/R^2) atTop (𝓝 0) := by
  have HR : Tendsto (fun R : ℝ => R+1) atTop atTop := tendsto_atTop_add_const_right atTop 1 tendsto_id
  have HI : Tendsto (fun R : ℝ => (R+1)/R) atTop (𝓝 1) := by
    have H := (tendsto_const_nhds (x := (1:ℝ))).add (tendsto_inv_atTop_zero : Tendsto (fun R:ℝ => R⁻¹) _ _)
    apply (show Tendsto (fun R : ℝ => 1+R⁻¹) atTop (𝓝 (1:ℝ)) by simpa using H).congr'
    filter_upwards [eventually_gt_atTop (0:ℝ)] with R hR
    field_simp
  have HL0 : Tendsto (fun R : ℝ => Real.log R / R) atTop (𝓝 0) := by
    simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
  have HL : Tendsto (fun R : ℝ => Real.log (a*(R+1))/(R+1)) atTop (𝓝 0) := by
    have H := (tendsto_const_nhds.div_atTop HR (a := Real.log a)).add (HL0.comp HR)
    apply (show Tendsto (fun R : ℝ => Real.log a/(R+1)+Real.log (R+1)/(R+1))
      atTop (𝓝 0) by simpa using H).congr'
    filter_upwards [eventually_gt_atTop (0:ℝ)] with R hR
    rw [Real.log_mul (ne_of_gt ha) (by positivity : R+1 ≠ 0), add_div]
  have HK : Tendsto (fun R : ℝ => k/R^2) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_pow_atTop (by decide : (2:ℕ) ≠ 0))
  have H := HK.add ((HI.pow 2).mul HL)
  apply (show Tendsto (fun R : ℝ => k/R^2+((R+1)/R)^2*(Real.log (a*(R+1))/(R+1)))
    atTop (𝓝 0) by simpa using H).congr'
  filter_upwards [eventually_gt_atTop (0:ℝ)] with R hR
  field_simp

 

theorem mellin_hasSubquadraticGrowth {f : ℝ → ℂ} {c C : ℝ} (hc : 0 < c)
    (hC : 0 ≤ C) (hzero : ∀ t, t ≤ 1 → f t = 0)
    (hbound : ∀ t, 1 < t → ‖f t‖ ≤ C*Real.exp (-c*t)) :
    HasSubquadraticGrowth (mellin f) := by
  apply HasSubquadraticGrowth.of_bound (tendsto_mellin_bound (by positivity : 0 < 2/c) (2*C/c))
  filter_upwards [eventually_ge_atTop (1:ℝ)] with R hR
  intro z hz
  have H := mellin_norm_le hc hC (by linarith : 0 < R+1) hzero hbound z
    (by linarith [Complex.re_le_norm z] : z.re-1 ≤ R+1)
  calc
    _ ≤ (2*C/c)*Real.exp ((R+1)*Real.log ((2/c)*(R+1))) := by
      simpa only [div_mul_eq_mul_div] using H
    _ ≤ Real.exp (2*C/c) * Real.exp ((R+1)*Real.log ((2/c)*(R+1))) := by
      apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
      linarith [Real.add_one_le_exp (2*C/c)]
    _ = _ := by rw [← Real.exp_add]

end PrimeDegreePackets.AnalyticGrowth


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
attribute [-instance] _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.PrimeDegreePackets.instNonemptyLeafTestSpace _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.finiteIdeleGroupT2Space _root_.ideleGroupT2Space _root_.infiniteAdeleRingT2Space _root_.infiniteIdeleGroupT2Space
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue
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

 

theorem hasSum_realZeroPole {f : ℂ → ℂ} (hf : Differentiable ℂ f) (h0 : f 0 ≠ 0)
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

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_IdealThetaXi
attribute [-instance] _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
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
open scoped ENNReal BigOperators Topology
open MeasureTheory Set Module
open scoped BigOperators ENNReal NumberField nonZeroDivisors
open scoped BigOperators ENNReal NumberField nonZeroDivisors Topology
namespace PrimeDegreePackets.HeckeMellin
open ThetaConstruction


lemma idealThetaXi_entire {d : ℕ} {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (σ : OrderedEmbeddings (d+1) K)
    (hn : finrank ℚ K = d+1) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    Differentiable ℂ (idealThetaXi σ hn I) := by
  exact (arithmeticFlowThetaXi_unitAverage_entire
    (fractionalIdealFullLattice hn I) σ hn).comp (by fun_prop)

end PrimeDegreePackets.HeckeMellin


namespace PrimeDegreePackets.HeckeMellin
open ThetaConstruction

lemma classThetaXi_entire {d : ℕ} {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (σ : OrderedEmbeddings (d+1) K)
    (hn : finrank ℚ K = d+1) : Differentiable ℂ (classThetaXi σ hn) := by
  unfold classThetaXi
  apply Differentiable.fun_sum
  intro c _
  apply Differentiable.mul _ (idealThetaXi_entire σ hn _)
  apply Differentiable.const_cpow differentiable_id
  exact Or.inl (Complex.ofReal_ne_zero.mpr (ne_of_gt (fractionalIdeal_absNorm_pos _)))

end PrimeDegreePackets.HeckeMellin

open Set


namespace PrimeDegreePackets.HeckeMellin
open ThetaConstruction

lemma completedThetaXi_entire {d : ℕ} {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (σ : OrderedEmbeddings (d+1) K)
    (hn : finrank ℚ K = d+1) : Differentiable ℂ (completedThetaXi σ hn) := by
  unfold completedThetaXi
  exact (Differentiable.const_mul (by fun_prop) _).mul (classThetaXi_entire σ hn)

end PrimeDegreePackets.HeckeMellin

open Filter Set Module MeasureTheory
open scoped Topology NumberField

open Filter Set Module MeasureTheory WithLp
open scoped Topology NumberField BigOperators nonZeroDivisors
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_RealMellin
attribute [-instance] _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
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
open scoped ENNReal BigOperators Topology
open MeasureTheory Set Module
open scoped BigOperators ENNReal NumberField nonZeroDivisors
open scoped BigOperators ENNReal NumberField nonZeroDivisors Topology
open Set
open Filter Set Module MeasureTheory
open scoped Topology NumberField
open Filter Set Module MeasureTheory WithLp
open scoped Topology NumberField BigOperators nonZeroDivisors
open scoped Topology NumberField BigOperators nonZeroDivisors ComplexConjugate
open MeasureTheory Set Filter Module WithLp
open scoped Topology BigOperators NumberField nonZeroDivisors
open Complex Set Filter Module
open Complex
open Complex Set Filter
open scoped Topology NumberField ComplexConjugate
open scoped Topology NumberField ComplexConjugate Classical
open Filter Set Topology Module
open MeasureTheory ProbabilityTheory Set Filter TopologicalSpace
open MeasureTheory MeasureTheory.Measure ProbabilityTheory Set Filter
open scoped Matrix Topology Classical ENNReal NNReal ProbabilityTheory
open scoped Matrix Topology Classical ENNReal
open scoped Topology ENNReal
open scoped Matrix Topology ENNReal ProbabilityTheory
open scoped Topology ENNReal CompactlySupported
open MeasureTheory Set Filter TopologicalSpace
open Module Set Matrix MeasureTheory Filter
open scoped NumberField
open CategoryTheory Module
open MeasureTheory Module Set Filter
open scoped BigOperators ENNReal RealInnerProductSpace
open Module Matrix
open scoped NumberField BigOperators
open Module MeasureTheory Set WithLp
open scoped NumberField BigOperators ENNReal


namespace PrimeDegreePackets.HeckeMellin

lemma completedThetaXi_logDeriv_totallyReal {d : ℕ} {K : Type*}
    [Field K] [NumberField K] [NumberField.IsTotallyReal K]
    (σ : OrderedEmbeddings (d+1) K) (hn : finrank ℚ K = d+1)
     {s : ℂ} (hs : 1 < s.re) :
    logDeriv (completedThetaXi σ hn) s = logDeriv (totallyRealCompletedXi K) s := by
  apply Filter.EventuallyEq.eq_of_nhds
  apply logDeriv_congr_nhds
  filter_upwards [isOpen_lt continuous_const Complex.continuous_re |>.mem_nhds hs] with z hz
  exact completedThetaXi_eq_totallyReal σ hn  hz

end PrimeDegreePackets.HeckeMellin


end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_SubquadraticGrowth
attribute [-instance] _root_.CyclicCohomology.permutationSublattice_discreteTopology _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.OAI.PrimeDegreePackets.instSecondCountableTopologyLeafTestSpace _root_.OAI.PrimeDegreePackets.rootSliceSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.finiteIdeleGroupT2Space _root_.ideleGroupT2Space _root_.infiniteAdeleRingT2Space _root_.infiniteIdeleGroupT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue
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
open scoped BigOperators Classical
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
open scoped ENNReal BigOperators Topology
open MeasureTheory Set Module
open scoped BigOperators ENNReal NumberField nonZeroDivisors
open scoped BigOperators ENNReal NumberField nonZeroDivisors Topology
open Set
open Filter Set Module MeasureTheory
open scoped Topology NumberField
open Filter Set Module MeasureTheory WithLp
open scoped Topology NumberField BigOperators nonZeroDivisors
open scoped Topology NumberField BigOperators nonZeroDivisors ComplexConjugate
namespace PrimeDegreePackets.AnalyticGrowth

lemma tendsto_affine_div_sq (a b : ℝ) :
    Tendsto (fun R : ℝ => (a*R+b)/R^2) atTop (𝓝 0) := by
  have H1 : Tendsto (fun R : ℝ => a/R) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  have H2 : Tendsto (fun R : ℝ => b/R^2) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_pow_atTop (by decide : (2:ℕ) ≠ 0))
  apply (show Tendsto (fun R : ℝ => a/R+b/R^2) atTop (𝓝 0) by simpa using H1.add H2).congr'
  filter_upwards [eventually_gt_atTop (0:ℝ)] with R hR
  field_simp

lemma hasSubquadraticGrowth_id : HasSubquadraticGrowth (fun z => z) := by
  apply HasSubquadraticGrowth.of_bound (by simpa using tendsto_affine_div_sq 1 0)
  apply Filter.Eventually.of_forall
  intro R z hz
  exact hz.trans (by linarith [Real.add_one_le_exp R])

lemma hasSubquadraticGrowth_exp_affine (a b : ℂ) :
    HasSubquadraticGrowth (fun z => Complex.exp (a*z+b)) := by
  apply HasSubquadraticGrowth.of_bound (tendsto_affine_div_sq ‖a‖ ‖b‖)
  apply Filter.Eventually.of_forall
  intro R z hz
  rw [Complex.norm_exp]
  apply Real.exp_le_exp.mpr
  calc
    _ ≤ ‖a*z+b‖ := Complex.re_le_norm _
    _ ≤ ‖a*z‖+‖b‖ := norm_add_le _ _
    _ ≤ ‖a‖*R+‖b‖ := by rw [norm_mul]; gcongr

lemma hasSubquadraticGrowth_const_cpow {a : ℝ} (ha : 0 < a) :
    HasSubquadraticGrowth (fun z : ℂ => (a:ℂ)^z) := by
  simpa only [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr ha.ne'), add_zero]
    using hasSubquadraticGrowth_exp_affine (Complex.log (a:ℂ)) 0

lemma HasSubquadraticGrowth.congr {f g : ℂ → ℂ} (hf : HasSubquadraticGrowth f)
    (h : ∀ z, f z = g z) : HasSubquadraticGrowth g := by
  have : f = g := funext h
  rwa [← this]

end PrimeDegreePackets.AnalyticGrowth

open MeasureTheory Set Filter Module WithLp
open scoped Topology BigOperators NumberField nonZeroDivisors
namespace PrimeDegreePackets.ThetaConstruction
open AnalyticGrowth
variable {d : Type*} [Fintype d]

lemma averagedNormalizedThetaTail_mellin_hasSubquadraticGrowth
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    (B : α → EuclideanSpace ℝ d ≃L[ℝ] EuclideanSpace ℝ d)
    (R : ℝ) (hR : 0 ≤ R) (hbound : ∀ x, ‖(B x).symm.toContinuousLinearMap‖ ≤ R) :
    HasSubquadraticGrowth (mellin (averagedNormalizedThetaTail μ B)) := by
  obtain ⟨a,C,ha,hC,_,hdecay⟩ := averagedNormalizedThetaTail_bounds μ B R hR hbound
  exact mellin_hasSubquadraticGrowth ha hC
    (fun t ht => averagedNormalizedThetaTail_eq_zero μ B ht) hdecay

theorem averagedThetaMellinXi_hasSubquadraticGrowth
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    (B : α → EuclideanSpace ℝ d ≃L[ℝ] EuclideanSpace ℝ d)
    (R T : ℝ) (hR : 0 ≤ R) (hT : 0 ≤ T)
    (hbound : ∀ x, ‖(B x).symm.toContinuousLinearMap‖ ≤ R)
    (hdual : ∀ x, ‖(adjointEquiv (B x).symm).symm.toContinuousLinearMap‖ ≤ T)
    (hB : StronglyMeasurable (fun p : α × ℝ => normalizedThetaTail (B p.1) p.2))
    (hD : StronglyMeasurable (fun p : α × ℝ =>
      normalizedThetaTail (adjointEquiv (B p.1).symm) p.2))
    (c : ℂ) (hc : ∀ x, ((|(LinearMap.det (B x).toLinearMap)⁻¹|:ℝ):ℂ) = c) :
    HasSubquadraticGrowth (fun s => ∫ x, thetaMellinXi (B x) s ∂μ) := by
  let a : ℂ := (Fintype.card d:ℂ)/2
  let P := mellin (averagedNormalizedThetaTail μ B)
  let Q := mellin (averagedNormalizedThetaTail μ (fun x => adjointEquiv (B x).symm))
  have HP : HasSubquadraticGrowth P := averagedNormalizedThetaTail_mellin_hasSubquadraticGrowth μ B R hR hbound
  have HQ : HasSubquadraticGrowth Q := averagedNormalizedThetaTail_mellin_hasSubquadraticGrowth μ _ T hT hdual
  have HE : (fun s => ∫ x, thetaMellinXi (B x) s ∂μ) =
      fun s => s*(s-a)*(P s+c*Q (a-s)) + (μ.real Set.univ:ℂ)*(c*s-(s-a)) := by
    funext s
    have hP := normalizedThetaTail_mellin_integrable μ B R hR hbound hB s
    have hQ := normalizedThetaTail_mellin_integrable μ _ T hT hdual hD (a-s)
    have hQc : Integrable (fun x => c*mellin (normalizedThetaTail (adjointEquiv (B x).symm)) (a-s)) μ := hQ.const_mul c
    have hPQ : Integrable (fun x => mellin (normalizedThetaTail (B x)) s +
        c*mellin (normalizedThetaTail (adjointEquiv (B x).symm)) (a-s)) μ := hP.add hQc
    have hPQc : Integrable (fun x => s*(s-a)*(mellin (normalizedThetaTail (B x)) s +
        c*mellin (normalizedThetaTail (adjointEquiv (B x).symm)) (a-s))) μ := hPQ.const_mul _
    have HPv := averagedNormalizedThetaTail_mellin_eq_integral μ B R hR hbound hB s
    have HQv := averagedNormalizedThetaTail_mellin_eq_integral μ _ T hT hdual hD (a-s)
    calc
      (∫ x, thetaMellinXi (B x) s ∂μ) = ∫ x,
          s*(s-a)*(mellin (normalizedThetaTail (B x)) s +
            c*mellin (normalizedThetaTail (adjointEquiv (B x).symm)) (a-s)) +
          (c*s-(s-a)) ∂μ := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun x => by simp only [thetaMellinXi,hc x]; dsimp [a] <;> ring)
      _ = s*(s-a)*(P s+c*Q (a-s)) + (μ.real Set.univ:ℂ)*(c*s-(s-a)) := by
        rw [integral_add hPQc (integrable_const (c*s-(s-a))),
          integral_const_mul,integral_add hP hQc,integral_const_mul,
          integral_const,←HPv,←HQv]
        simp only [P,Q,Complex.real_smul]
  rw [HE]
  have Hq : HasSubquadraticGrowth (fun s => Q (a-s)) :=
    (HQ.comp_affine (-1) a).congr (fun s => by congr 1; ring)
  have Hid := hasSubquadraticGrowth_id
  have Hsa := Hid.sub (hasSubquadraticGrowth_const a)
  exact ((Hid.mul Hsa).mul (HP.add ((hasSubquadraticGrowth_const c).mul Hq))).add
    ((hasSubquadraticGrowth_const (μ.real Set.univ:ℂ)).mul
      (((hasSubquadraticGrowth_const c).mul Hid).sub Hsa))

end PrimeDegreePackets.ThetaConstruction


namespace PrimeDegreePackets
open ThetaConstruction AnalyticGrowth

theorem arithmeticFlowThetaXi_boundedAverage_hasSubquadraticGrowth {d : ℕ} {K : Type*}
    [Field K] [NumberField K] (M : FullLattice (d+1) K)
    (σ : OrderedEmbeddings (d+1) K) (hn : finrank ℚ K = d+1)
    {S : Set (LogCoordinates d)} (hS : MeasurableSet S) (hbd : Bornology.IsBounded S) :
    HasSubquadraticGrowth (fun s => ∫ u in S,
      thetaMellinXi (logScaledLattice (fullLatticeEuclideanBasis M σ hn)
        (restoredLogCoordinates u)) s) := by
  let μ : Measure S := Measure.comap ((↑) : S → LogCoordinates d) volume
  have hμ : IsFiniteMeasure μ := ⟨by
    dsimp only [μ]
    rw [comap_subtype_coe_apply hS,Set.image_univ,Subtype.range_coe]
    exact hbd.measure_lt_top⟩
  let B := fullLatticeEuclideanBasis M σ hn
  let u : S → Fin (d+1) → ℝ := fun x => restoredLogCoordinates x.1
  let F := fun x : S => logScaledLattice B (u x)
  have hu : ∀ i, Measurable (fun x => u x i) := fun i =>
    ((restoredLogCoordinates_continuous i).comp continuous_subtype_val).measurable
  obtain ⟨U,hU⟩ := restoredLogCoordinates_abs_bound_on_compact hbd.isCompact_closure
  let R := ‖B.symm.toContinuousLinearMap‖*Real.exp U
  let T := ‖(adjointEquiv B.symm).symm.toContinuousLinearMap‖*Real.exp U
  have hR : 0 ≤ R := mul_nonneg (norm_nonneg _) (Real.exp_pos _).le
  have hT : 0 ≤ T := mul_nonneg (norm_nonneg _) (Real.exp_pos _).le
  have HB : ∀ x, ‖(F x).symm.toContinuousLinearMap‖ ≤ R := by
    intro x
    exact logScaledLattice_inverse_bound B (fun i =>
      (neg_le_abs _).trans (hU x.1 (subset_closure x.2) i))
  have HD : ∀ x, ‖(adjointEquiv (F x).symm).symm.toContinuousLinearMap‖ ≤ T := by
    intro x
    rw [show F x = logScaledLattice B (u x) from rfl,adjointEquiv_logScaledLattice]
    apply logScaledLattice_inverse_bound
    intro i
    simp only [Pi.neg_apply,neg_neg]
    exact (le_abs_self _).trans (hU x.1 (subset_closure x.2) i)
  have HM : StronglyMeasurable (fun p : S × ℝ => normalizedThetaTail (F p.1) p.2) :=
    normalizedThetaTail_joint_stronglyMeasurable (B := F)
      (fun z => logScaledLattice_measurable_apply B u hu (euclideanInteger z))
  have HN : StronglyMeasurable (fun p : S × ℝ =>
      normalizedThetaTail (adjointEquiv (F p.1).symm) p.2) := by
    have HE : (fun x => adjointEquiv (F x).symm) =
        fun x => logScaledLattice (adjointEquiv B.symm) (-u x) := by
      funext x
      exact adjointEquiv_logScaledLattice B (u x)
    simp_rw [show ∀ x, adjointEquiv (F x).symm =
      logScaledLattice (adjointEquiv B.symm) (-u x) from congrFun HE]
    exact normalizedThetaTail_joint_stronglyMeasurable
      (B := fun x => logScaledLattice (adjointEquiv B.symm) (-u x))
      (fun z => logScaledLattice_measurable_apply _ _ (fun i => (hu i).neg) (euclideanInteger z))
  have HC : ∀ x, ((|(LinearMap.det (F x).toLinearMap)⁻¹|:ℝ):ℂ) =
      ((|(embeddingMatrix M σ).det⁻¹|:ℝ):ℂ) := by
    intro x
    dsimp only [F,u]
    rw [logScaledLattice_det,restoredLogCoordinates_sum,Real.exp_zero,one_mul,
      show LinearMap.det B.toLinearMap = (embeddingMatrix M σ).det from
        fullLatticeEuclideanBasis_det M σ hn]
  have H := averagedThetaMellinXi_hasSubquadraticGrowth μ F R T hR hT HB HD HM HN _ HC
  have HE : (fun s => ∫ x, thetaMellinXi (F x) s ∂μ) =
      fun s => ∫ u in S, thetaMellinXi (logScaledLattice B (restoredLogCoordinates u)) s := by
    funext s
    exact integral_subtype_comap hS (fun u => thetaMellinXi (logScaledLattice B (restoredLogCoordinates u)) s)
  rw [HE] at H
  exact H

end PrimeDegreePackets


namespace PrimeDegreePackets.HeckeMellin
open ThetaConstruction AnalyticGrowth

lemma idealThetaXi_hasSubquadraticGrowth {d : ℕ} {K : Type*}
    [Field K] [NumberField K] [NumberField.IsTotallyReal K]
    (σ : OrderedEmbeddings (d+1) K) (hn : finrank ℚ K = d+1)
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    HasSubquadraticGrowth (idealThetaXi σ hn I) := by
  have H := arithmeticFlowThetaXi_boundedAverage_hasSubquadraticGrowth
    (fractionalIdealFullLattice hn I) σ hn
    (S := orderedThetaLogDomain σ) (ZSpan.fundamentalDomain_measurableSet _) (ZSpan.fundamentalDomain_isBounded _)
  exact (H.comp_affine (((d+1 : ℕ) : ℂ)/2) 0).congr (fun s => by
    unfold idealThetaXi
    congr 1
    ring_nf)

lemma classThetaXi_hasSubquadraticGrowth {d : ℕ} {K : Type*}
    [Field K] [NumberField K] [NumberField.IsTotallyReal K]
    (σ : OrderedEmbeddings (d+1) K) (hn : finrank ℚ K = d+1) :
    HasSubquadraticGrowth (classThetaXi σ hn) := by
  classical
  unfold classThetaXi
  apply HasSubquadraticGrowth.finset_sum
  intro c _
  exact (hasSubquadraticGrowth_const_cpow (fractionalIdeal_absNorm_pos _)).mul
    (idealThetaXi_hasSubquadraticGrowth σ hn _)

 

theorem completedThetaXi_hasSubquadraticGrowth {d : ℕ} {K : Type*}
    [Field K] [NumberField K] [NumberField.IsTotallyReal K]
    (σ : OrderedEmbeddings (d+1) K) (hn : finrank ℚ K = d+1) :
    HasSubquadraticGrowth (completedThetaXi σ hn) := by
  unfold completedThetaXi
  have H := hasSubquadraticGrowth_exp_affine
    ((Real.log |(NumberField.discr K : ℝ)| : ℂ)/2) 0
  have HE : HasSubquadraticGrowth (fun s : ℂ =>
      Complex.exp (s*(Real.log |(NumberField.discr K : ℝ)| : ℂ)/2)) :=
    H.congr (fun s => by congr 1; ring)
  exact ((hasSubquadraticGrowth_const _).mul HE).mul
    (classThetaXi_hasSubquadraticGrowth σ hn)

end PrimeDegreePackets.HeckeMellin

open Complex Set Filter Module

open Complex
namespace PrimeDegreePackets.AnalyticGrowth

lemma near_one_kernel_lower {a b : ℝ} (ha : 1 ≤ a) (ha' : a ≤ 5/4)
    (hb : |b| ≤ 1/4) : (10/13:ℝ) ≤ a/(a^2+b^2) := by
  have hb' := abs_le.mp hb
  have hbs : b^2 ≤ 1/16 := by nlinarith
  have hd : 0 < a^2+b^2 := by nlinarith [sq_nonneg b]
  apply (le_div_iff₀ hd).mpr
  have Hp : 0 ≤ (5/4-a)*(10*a-1/2) := mul_nonneg (by linarith) (by linarith)
  nlinarith

lemma real_inverse_pole_scaled {L h : ℝ} (hL : L ≠ 0) (ρ : ℂ) :
    (1/(((1+h:ℝ):ℂ)-ρ)).re =
      L*((L*(1-ρ.re)+L*h)/((L*(1-ρ.re)+L*h)^2+(L*ρ.im)^2)) := by
  simp only [one_div, Complex.inv_re, Complex.sub_re, Complex.ofReal_re,
    Complex.normSq_apply, Complex.sub_im, Complex.ofReal_im, zero_sub]
  have HE : L*(1-ρ.re)+L*h = L*(1+h-ρ.re) := by ring
  rw [HE]
  simp only [mul_pow, neg_mul_neg]
  rw [← mul_add, ← mul_div_assoc, ← mul_assoc, ← pow_two]
  rw [show L*L = L^2 by ring]
  rw [mul_div_mul_left _ _ (pow_ne_zero 2 hL)]
  congr 1; ring

 

lemma near_one_complex_pole_lower {L : ℝ} (hL : 0 < L) {ρ : ℂ}
    (hβ : ρ.re ≤ 1) (hβ' : 1-1/(4*L) ≤ ρ.re) (hγ : |ρ.im| ≤ 1/(4*L)) :
    (10/13)*L ≤ (1/(((1+1/L:ℝ):ℂ)-ρ)).re := by
  have hX : 0 ≤ L*(1-ρ.re) := mul_nonneg hL.le (by linarith)
  have hX' : L*(1-ρ.re) ≤ 1/4 := by
    have H := mul_le_mul_of_nonneg_left (show 1-ρ.re ≤ 1/(4*L) by linarith) hL.le
    have HE : L*(1/(4*L)) = (1/4:ℝ) := by field_simp
    rwa [HE] at H
  have hY : |L*ρ.im| ≤ 1/4 := by
    rw [abs_mul, abs_of_pos hL]
    have H := mul_le_mul_of_nonneg_left hγ hL.le
    have HE : L*(1/(4*L)) = (1/4:ℝ) := by field_simp
    rwa [HE] at H
  have H := near_one_kernel_lower (a := L*(1-ρ.re)+1) (by linarith) (by linarith) hY
  rw [real_inverse_pole_scaled hL.ne', mul_one_div_cancel hL.ne']
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left H hL.le

end PrimeDegreePackets.AnalyticGrowth

open Complex Set Filter
namespace PrimeDegreePackets.AnalyticGrowth



lemma nearOneBox_multiplicity_sum_le_one {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (h0 : f 0 ≠ 0) (hg : HasSubquadraticGrowth f)
    (hfe : ∀ z, f (1-z) = f z) (hstrip : ∀ ρ, f ρ = 0 → ρ.re ≤ 1)
    {L A : ℝ} (hL : 0 < L) (hA : 26*A < L)
    (hbound : (logDeriv f (((1+1/L:ℝ)):ℂ)).re ≤ (3/2)*L+A)
    (t : Finset ℂ) (ht : ∀ ρ ∈ t, f ρ = 0 ∧ InNearOneBox L ρ) :
    ∑ ρ ∈ t, zeroMultiplicity f ρ ≤ 1 := by
  have hs : 1 < 1+1/L := by have H := one_div_pos.mpr hL; linarith
  have HS := hasSum_realZeroPole hf h0 hg hfe hstrip hs
  have Hlower : (10/13)*L*(∑ ρ ∈ t, (zeroMultiplicity f ρ : ℝ)) ≤
      ∑ ρ ∈ t, realZeroPole f (1+1/L) ρ := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro ρ hρ
    have H := near_one_complex_pole_lower hL (hstrip ρ (ht ρ hρ).1)
      (ht ρ hρ).2.1 (ht ρ hρ).2.2
    simpa only [realZeroPole, mul_comm] using mul_le_mul_of_nonneg_left H
      (show (0:ℝ) ≤ zeroMultiplicity f ρ by exact_mod_cast zeroMultiplicity_nonneg hf ρ)
  have Hupper := (HS.summable.sum_le_tsum t
    (fun ρ _ => realZeroPole_nonneg hf h0 hstrip hs ρ)).trans_eq HS.tsum_eq
  have Htotal := Hlower.trans (Hupper.trans hbound)
  by_contra h
  have Htwo : (2:ℤ) ≤ ∑ ρ ∈ t, zeroMultiplicity f ρ := by omega
  have Htwo' : (2:ℝ) ≤ ∑ ρ ∈ t, (zeroMultiplicity f ρ : ℝ) := by exact_mod_cast Htwo
  have HH := mul_le_mul_of_nonneg_left Htwo' (show 0 ≤ (10/13)*L by positivity)
  nlinarith

 

theorem nearOneBox_real_simple_unique {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (h0 : f 0 ≠ 0) (hg : HasSubquadraticGrowth f)
    (hfe : ∀ z, f (1-z) = f z) (hconj : ∀ z, f (conj z) = conj (f z))
    (hstrip : ∀ ρ, f ρ = 0 → ρ.re ≤ 1)
    {L A : ℝ} (hL : 0 < L) (hA : 26*A < L)
    (hbound : (logDeriv f (((1+1/L:ℝ)):ℂ)).re ≤ (3/2)*L+A)
    {ρ : ℂ} (hρ : f ρ = 0) (hbox : InNearOneBox L ρ) :
    zeroMultiplicity f ρ = 1 ∧ ρ.im = 0 ∧
      ∀ τ, f τ = 0 → InNearOneBox L τ → τ = ρ := by
  classical
  have HP {τ : ℂ} (hτ : f τ = 0) : 1 ≤ zeroMultiplicity f τ := by
    have H := zeroMultiplicity_nonneg hf τ
    have H' := (zeroMultiplicity_ne_zero_iff hf h0 τ).mpr hτ
    omega
  have Huniq : ∀ τ, f τ = 0 → InNearOneBox L τ → τ = ρ := by
    intro τ hτ hτbox
    by_contra hne
    have H := nearOneBox_multiplicity_sum_le_one hf h0 hg hfe hstrip hL hA hbound
      {τ,ρ} (by
        intro z hz
        simp only [Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with rfl | rfl
        · exact ⟨hτ,hτbox⟩
        · exact ⟨hρ,hbox⟩)
    simp only [Finset.sum_pair hne] at H
    have Hτ := HP hτ
    have Hρ := HP hρ
    omega
  have Hsimple := nearOneBox_multiplicity_sum_le_one hf h0 hg hfe hstrip hL hA hbound
    {ρ} (by intro z hz; have H := Finset.mem_singleton.mp hz; subst z; exact ⟨hρ,hbox⟩)
  have HS : zeroMultiplicity f ρ = 1 := by
    simp only [Finset.sum_singleton] at Hsimple
    exact le_antisymm Hsimple (HP hρ)
  have Hc := Huniq (conj ρ) (by rw [hconj, hρ]; simp) (by
    simpa only [InNearOneBox, Complex.conj_re, Complex.conj_im, abs_neg] using hbox)
  have HI := congrArg Complex.im Hc
  simp only [Complex.conj_im] at HI
  exact ⟨HS, by linarith, Huniq⟩

end PrimeDegreePackets.AnalyticGrowth

open scoped Topology NumberField ComplexConjugate
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_FunctionalEquation
attribute [-instance] _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.DukePrimeDegree.EmbeddingOrder.toRealOrder_apply
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
open scoped ENNReal BigOperators Topology
open MeasureTheory Set Module
open scoped BigOperators ENNReal NumberField nonZeroDivisors
open scoped BigOperators ENNReal NumberField nonZeroDivisors Topology
open Set
open Filter Set Module MeasureTheory
open scoped Topology NumberField
open Filter Set Module MeasureTheory WithLp
open scoped Topology NumberField BigOperators nonZeroDivisors
open scoped Topology NumberField BigOperators nonZeroDivisors ComplexConjugate
open MeasureTheory Set Filter Module WithLp
open scoped Topology BigOperators NumberField nonZeroDivisors
open Complex Set Filter Module
open Complex
open Complex Set Filter
open scoped Topology NumberField ComplexConjugate
open scoped Topology NumberField ComplexConjugate Classical
open Filter Set Topology Module
open MeasureTheory ProbabilityTheory Set Filter TopologicalSpace
open MeasureTheory MeasureTheory.Measure ProbabilityTheory Set Filter
open scoped Matrix Topology Classical ENNReal NNReal ProbabilityTheory
open scoped Matrix Topology Classical ENNReal
open scoped Topology ENNReal
open scoped Matrix Topology ENNReal ProbabilityTheory
open scoped Topology ENNReal CompactlySupported
open MeasureTheory Set Filter TopologicalSpace
open Module Set Matrix MeasureTheory Filter
open scoped NumberField
open CategoryTheory Module
open MeasureTheory Module Set Filter
open scoped BigOperators ENNReal RealInnerProductSpace
open Module Matrix
open scoped NumberField BigOperators
open Module MeasureTheory Set WithLp
open scoped NumberField BigOperators ENNReal


namespace PrimeDegreePackets.HeckeMellin

lemma completedThetaXi_ne_zero_of_re_gt_one_totallyReal {d : ℕ} {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (σ : OrderedEmbeddings (d+1) K)
    (hn : finrank ℚ K = d+1)  {s : ℂ} (hs : 1 < s.re) :
    completedThetaXi σ hn s ≠ 0 := by
  rw [completedThetaXi_eq_totallyReal σ hn  hs]
  exact totallyRealCompletedXi_ne_zero K hs

lemma completedThetaXi_ne_zero_of_re_neg_totallyReal {d : ℕ} {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (σ : OrderedEmbeddings (d+1) K)
    (hn : finrank ℚ K = d+1)  {s : ℂ} (hs : s.re < 0) :
    completedThetaXi σ hn s ≠ 0 := by
  rw [completedThetaXi_functionalEquation_totallyReal σ hn  s]
  apply completedThetaXi_ne_zero_of_re_gt_one_totallyReal σ hn 
  simp only [Complex.sub_re, Complex.one_re]
  linarith

lemma dedekindXiZeros_re_mem_Icc_totallyReal {d : ℕ} {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (σ : OrderedEmbeddings (d+1) K)
    (hn : finrank ℚ K = d+1) 
    {s : ℂ} (hs : s ∈ dedekindXiZeros σ hn) : s.re ∈ Icc (0:ℝ) 1 := by
  constructor
  · by_contra h
    exact completedThetaXi_ne_zero_of_re_neg_totallyReal σ hn  (lt_of_not_ge h) hs
  · by_contra h
    exact completedThetaXi_ne_zero_of_re_gt_one_totallyReal σ hn  (lt_of_not_ge h) hs

end PrimeDegreePackets.HeckeMellin


namespace PrimeDegreePackets.HeckeMellin
open AnalyticGrowth

lemma completedThetaXi_logDeriv_base_le_totallyReal {d : ℕ} {K : Type*}
    [Field K] [NumberField K] [NumberField.IsTotallyReal K]
    (σ : OrderedEmbeddings (d+1) K) (hn : finrank ℚ K = d+1)
     {B L : ℝ}
    (hL : L = Real.log |(NumberField.discr K : ℝ)|) (hL1 : 1 ≤ L)
    (hB : ∀ s ∈ Icc (1:ℝ) 2, |archimedeanZetaTerm (d+1) s| ≤ B) :
    (logDeriv (completedThetaXi σ hn) (((1+1/L:ℝ)):ℂ)).re ≤ (3/2)*L+B+1 := by
  have hLp : 0 < L := lt_of_lt_of_le zero_lt_one hL1
  have hs : 1 < 1+1/L := by have H := one_div_pos.mpr hLp; linarith
  have hsu : 1+1/L ≤ 2 := by
    have H := (div_le_one hLp).mpr hL1
    linarith
  rw [completedThetaXi_logDeriv_totallyReal σ hn  (by simpa using hs),
    totallyRealCompletedXi_logDeriv_re K hs, hn, ← hL]
  have HG := (abs_le.mp (hB (1+1/L) ⟨hs.le,hsu⟩)).2
  have HD : deriv (realDedekindZeta K) (1+1/L) / realDedekindZeta K (1+1/L) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (realDedekindZeta_deriv_nonpos K hs)
      (realDedekindZeta_pos K hs).le
  have Hr : 1/(1+1/L) ≤ 1 := (div_le_one (by linarith)).mpr hs.le
  have HE : 1/(1+1/L-1) = L := by field_simp <;> ring
  rw [HE]
  linarith

theorem dedekind_near_one_zero_real_simple_unique_totallyReal (d : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyReal K],
      ∀ (σ : OrderedEmbeddings (d+1) K) (hn : finrank ℚ K = d+1)
        ,
      C < Real.log |(NumberField.discr K : ℝ)| →
      ∀ ρ, ρ ∈ dedekindXiZeros σ hn →
        InNearOneBox (Real.log |(NumberField.discr K : ℝ)|) ρ →
        zeroMultiplicity (completedThetaXi σ hn) ρ = 1 ∧ ρ.im = 0 ∧
          ∀ τ, τ ∈ dedekindXiZeros σ hn →
            InNearOneBox (Real.log |(NumberField.discr K : ℝ)|) τ → τ = ρ := by
  obtain ⟨B,hB,harch⟩ := archimedeanZetaTerm_bounded (d+1)
  refine ⟨max 1 (26*(B+1)), lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro K _ _ _ σ hn  hL ρ hρ hρbox
  have hL1 : 1 < Real.log |(NumberField.discr K : ℝ)| :=
    lt_of_le_of_lt (le_max_left _ _) hL
  have hLp : 0 < Real.log |(NumberField.discr K : ℝ)| := by linarith
  have Hbase := completedThetaXi_logDeriv_base_le_totallyReal σ hn  rfl hL1.le harch
  apply nearOneBox_real_simple_unique (completedThetaXi_entire σ hn)
    (dedekindXiZeros_ne_zero_totallyReal σ hn ) (completedThetaXi_hasSubquadraticGrowth σ hn)
    (fun z => (completedThetaXi_functionalEquation_totallyReal σ hn  z).symm)
    (completedThetaXi_conj_totallyReal σ hn )
    (fun z hz => (dedekindXiZeros_re_mem_Icc_totallyReal σ hn  hz).2)
    hLp (lt_of_le_of_lt (le_max_right _ _) hL) _ hρ hρbox
  simpa only [add_assoc] using Hbase

end PrimeDegreePackets.HeckeMellin

open IntermediateField Module

open Module IntermediateField
open scoped BigOperators NumberField Pointwise
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_NormalClosure
attribute [-instance] _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
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
open scoped ENNReal BigOperators Topology
open MeasureTheory Set Module
open scoped BigOperators ENNReal NumberField nonZeroDivisors
open scoped BigOperators ENNReal NumberField nonZeroDivisors Topology
open Set
open Filter Set Module MeasureTheory
open scoped Topology NumberField
open Filter Set Module MeasureTheory WithLp
open scoped Topology NumberField BigOperators nonZeroDivisors
open scoped Topology NumberField BigOperators nonZeroDivisors ComplexConjugate
open MeasureTheory Set Filter Module WithLp
open scoped Topology BigOperators NumberField nonZeroDivisors
open Complex Set Filter Module
open Complex
open Complex Set Filter
open scoped Topology NumberField ComplexConjugate
open scoped Topology NumberField ComplexConjugate Classical
open Filter Set Topology Module
open MeasureTheory ProbabilityTheory Set Filter TopologicalSpace
open MeasureTheory MeasureTheory.Measure ProbabilityTheory Set Filter
open scoped Matrix Topology Classical ENNReal NNReal ProbabilityTheory
open scoped Matrix Topology Classical ENNReal
open scoped Topology ENNReal
open scoped Matrix Topology ENNReal ProbabilityTheory
open scoped Topology ENNReal CompactlySupported
open MeasureTheory Set Filter TopologicalSpace
open Module Set Matrix MeasureTheory Filter
open scoped NumberField
open CategoryTheory Module
open MeasureTheory Module Set Filter
open scoped BigOperators ENNReal RealInnerProductSpace
open Module Matrix
open scoped NumberField BigOperators
open Module MeasureTheory Set WithLp
open scoped NumberField BigOperators ENNReal
open IntermediateField Module
open Module IntermediateField
open scoped BigOperators NumberField Pointwise
open Module IntermediateField Set
namespace PrimeDegreePackets

namespace HeckeMellin
open AnalyticGrowth

 

lemma boundedDegree_near_one_zero_real_simple_unique_oai (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ {d : ℕ}, d+1 ≤ n →
      ∀ {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyReal K]
        (σ : OrderedEmbeddings (d+1) K) (hn : finrank ℚ K = d+1),
      C < Real.log |(NumberField.discr K : ℝ)| →
      ∀ ρ, ρ ∈ dedekindXiZeros σ hn →
        InNearOneBox (Real.log |(NumberField.discr K : ℝ)|) ρ →
        zeroMultiplicity (completedThetaXi σ hn) ρ = 1 ∧ ρ.im = 0 ∧
          ∀ τ, τ ∈ dedekindXiZeros σ hn →
            InNearOneBox (Real.log |(NumberField.discr K : ℝ)|) τ → τ = ρ := by
  classical
  choose C hC hzero using dedekind_near_one_zero_real_simple_unique_totallyReal
  refine ⟨(∑ i ∈ Finset.range n, C i)+1,?_,?_⟩
  · have H := Finset.sum_nonneg (s := Finset.range n) (fun i _ => (hC i).le)
    linarith
  intro d hd K _ _ _ σ hn hL
  apply hzero d σ hn
  have H := Finset.single_le_sum (fun i _ => (hC i).le)
    (show d ∈ Finset.range n from Finset.mem_range.mpr (by omega))
  linarith



end HeckeMellin
end PrimeDegreePackets


end
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.PrimeDegreePackets.HeckeMellin.boundedDegree_near_one_zero_real_simple_unique_oai.{u_1} := @OAI.PrimeDegreePackets.HeckeMellin.boundedDegree_near_one_zero_real_simple_unique_oai.{u_1}
