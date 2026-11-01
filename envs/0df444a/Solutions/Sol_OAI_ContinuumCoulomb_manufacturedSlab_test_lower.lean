-- Prove2me | solution 1 for OAI.ContinuumCoulomb.manufacturedSlab_test_lower
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T21:24:24.779545+00:00
-- url     : https://prove2.me/submissions/c2e0f7a7-0ccb-4312-873e-25cdf9392d49

import Mathlib
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range
import Mathlib.Analysis.CStarAlgebra.GelfandNaimarkSegal
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.Calculus.BumpFunction.Basic
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Const
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Convolution
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Operator.Compact
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.VonNeumannAlgebra.Basic
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Combinatorics.Young.YoungDiagram
import Mathlib.Data.List.Nodup
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.ExpDecay
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.MeasurableSpace.Embedding
import Mathlib.MeasureTheory.Measure.FiniteMeasure
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Probability.Kernel.CondDistrib
import Mathlib.Probability.Kernel.Defs
import Mathlib.Probability.Moments.Variance
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Algebra.LinearMapCompletion
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.Algebra.Support
import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.UniformSpace.Cauchy
import Mathlib.Topology.UniformSpace.HeineCantor
import Definitions.Def_ContinuumCoulombHardness
import Definitions.Def_OAIQ092A008
import Definitions.Def_OAIQ092A009

section
-- module Solutions.OAIQ092_CC.CoulombRadii_Packets_CoulombKernel
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
namespace NeutralAtom
open scoped Convolution
open ContinuousLinearMap

theorem contDiff_regularizedKernel {ε : ℝ} (hε : ε ≠ 0) :
    ContDiff ℝ ∞ (regularizedKernel ε) := by
  apply ContDiff.rpow_const_of_ne
  · exact (contDiff_norm_sq ℝ).add contDiff_const
  · intro x
    exact (add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_ne_zero hε)).ne'

theorem coulombKernel_eq_rpow (x : Position) :
    coulombKernel x = (‖x‖^2)^(-1/2 : ℝ) := by
  rw [← Real.rpow_natCast_mul (norm_nonneg x)]
  norm_num [coulombKernel, Real.rpow_neg_one]

theorem regularizedKernel_le {ε : ℝ} {x : Position} (hx : x ≠ 0) :
    regularizedKernel ε x ≤ coulombKernel x := by
  rw [coulombKernel_eq_rpow]
  exact Real.rpow_le_rpow_of_nonpos (sq_pos_of_pos (norm_pos_iff.mpr hx))
    (le_add_of_nonneg_right (sq_nonneg ε)) (by norm_num)

theorem regularizedKernel_nonneg (ε : ℝ) (x : Position) :
    0 ≤ regularizedKernel ε x := by unfold regularizedKernel; positivity

theorem regularizedKernel_tendsto {ε : ℕ → ℝ} (hlim : Tendsto ε atTop (𝓝 0))
    {x : Position} (hx : x ≠ 0) :
    Tendsto (fun n => regularizedKernel (ε n) x) atTop (𝓝 (coulombKernel x)) := by
  have hh : Tendsto (fun n => ‖x‖^2+(ε n)^2) atTop (𝓝 (‖x‖^2)) := by
    simpa using tendsto_const_nhds.add (hlim.pow 2)
  have hr := hh.rpow tendsto_const_nhds
    (Or.inl (pow_ne_zero 2 (norm_ne_zero_iff.mpr hx)) : ‖x‖^2 ≠ 0 ∨ 0 < (-1/2:ℝ))
  simpa only [regularizedKernel, coulombKernel_eq_rpow] using hr

end NeutralAtom
end
end
end

end OAI
end

section
-- module Solutions.OAIQ092_CC.CoulombRadii_Localization_TruncatedCoulomb
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.Coulomb.complexWindow_apply _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
namespace Coulomb
lemma coulombKernel_nonneg (x : Space) : 0 ≤ coulombKernel x := inv_nonneg.mpr (norm_nonneg _)
lemma coulombKernel_measurable : Measurable coulombKernel := measurable_norm.inv
lemma coulombKernel_integrableOn_ball (R : ℝ) : IntegrableOn coulombKernel (Metric.ball 0 R) := by
  apply integrableOn_ball_of_norm_le_rpow (C := 1) (α := 1) (by simp) (by norm_num)
  · exact Filter.Eventually.of_forall (fun x => by simp [coulombKernel, Real.rpow_neg_one])
  · exact coulombKernel_measurable.aestronglyMeasurable

lemma truncatedCoulomb_integrable (R : ℝ) : Integrable (truncatedCoulomb R) :=
  (coulombKernel_integrableOn_ball R).integrable_indicator measurableSet_ball

lemma coulomb_integrand_bound {f : Space → ℝ} {M R : ℝ} (hf0 : ∀ y, 0 ≤ f y)
    (hfM : ∀ y, f y ≤ M) (hR : 0 < R) (x y : Space) :
    coulombKernel (x-y) * f y ≤ M * truncatedCoulomb R (x-y) + R⁻¹ * f y := by
  by_cases h : x-y ∈ Metric.ball (0:Space) R
  · rw [truncatedCoulomb, Set.indicator_of_mem h]
    have H := mul_le_mul_of_nonneg_left (hfM y) (coulombKernel_nonneg (x-y))
    linarith [mul_nonneg (inv_nonneg.mpr hR.le) (hf0 y)]
  · rw [truncatedCoulomb, Set.indicator_of_notMem h, mul_zero, zero_add]
    have hn : R ≤ ‖x-y‖ := by simpa [Metric.mem_ball, dist_zero_right] using h
    exact mul_le_mul_of_nonneg_right (inv_anti₀ hR hn) (hf0 y)

lemma coulomb_convolution_integrable {f : Space → ℝ} (hf : Integrable f) (hm : Measurable f)
    {M R : ℝ} (hf0 : ∀ y, 0 ≤ f y) (hfM : ∀ y, f y ≤ M) (hR : 0 < R) (x : Space) :
    Integrable (fun y => coulombKernel (x-y) * f y) := by
  have hnear := (truncatedCoulomb_integrable R).comp_sub_left x
  apply ((hnear.const_mul M).add (hf.const_mul R⁻¹)).mono'
    (((coulombKernel_measurable.comp (measurable_const.sub measurable_id)).mul hm).aestronglyMeasurable)
  exact Filter.Eventually.of_forall (fun y => by
    change ‖coulombKernel (x-y) * f y‖ ≤ _
    rw [Real.norm_of_nonneg (mul_nonneg (coulombKernel_nonneg _) (hf0 _))]
    exact coulomb_integrand_bound hf0 hfM hR x y)

lemma coulomb_signed_convolution_integrable {f : Space → ℝ} (hf : Integrable f)
    (hm : Measurable f) {M : ℝ} (hM : ∀ x, ‖f x‖ ≤ M) (x : Space) :
    Integrable (fun y => coulombKernel (x-y)*f y) := by
  have h := coulomb_convolution_integrable hf.norm hm.norm (fun y => norm_nonneg _) hM
    (by norm_num : (0:ℝ) < 1) x
  apply h.mono' (((coulombKernel_measurable.comp (by fun_prop)).mul hm).aestronglyMeasurable)
  exact Filter.Eventually.of_forall (fun y => by
    change ‖coulombKernel (x-y)*f y‖ ≤ coulombKernel (x-y)*‖f y‖
    rw [norm_mul, Real.norm_of_nonneg (coulombKernel_nonneg _)] )

end Coulomb

open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology

end
end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Nuclei_SlabLineIntegral
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Centered-interval comparison for the actual one-coordinate Coulomb
integrals. It is the coordinatewise monotonicity step in the slab estimate. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

theorem centeredLineIntegral_translate (f : ℝ → ℝ) (H x : ℝ) :
    centeredLineIntegral f H x = ∫ t in (-H)..H, f (x-t) := by
  rw [intervalIntegral.integral_comp_sub_left]
  simp only [centeredLineIntegral, sub_neg_eq_add]

theorem centeredLineIntegral_hasDerivAt (f : ℝ → ℝ) (hf : Continuous f) (H x : ℝ) :
    HasDerivAt (centeredLineIntegral f H) (f (x+H)-f (x-H)) x := by
  let F : ℝ → ℝ := fun a => ∫ t in (0:ℝ)..a, f t
  have hF (a : ℝ) : HasDerivAt F (f a) a :=
    intervalIntegral.integral_hasDerivAt_right (hf.intervalIntegrable _ _)
      hf.aestronglyMeasurable.stronglyMeasurableAtFilter hf.continuousAt
  have he : centeredLineIntegral f H = (fun a => F (a+H)-F (a-H)) := by
    funext a
    exact (intervalIntegral.integral_interval_sub_left
      (hf.intervalIntegrable 0 (a+H)) (hf.intervalIntegrable 0 (a-H))).symm
  rw [he]
  simpa only [Function.comp_def, id_eq, mul_one] using
    ((hF (x+H)).comp x ((hasDerivAt_id x).add_const H)).fun_sub
      ((hF (x-H)).comp x ((hasDerivAt_id x).sub_const H))

theorem centeredLineIntegral_even (f : ℝ → ℝ) (heven : ∀ t, f (-t) = f t)
    (H x : ℝ) : centeredLineIntegral f H (-x) = centeredLineIntegral f H x := by
  have h := intervalIntegral.integral_comp_neg (f := f) (a := x-H) (b := x+H)
  simp only [heven] at h
  have ha : -(x+H) = -x-H := by ring
  have hb : -(x-H) = -x+H := by ring
  rw [ha, hb] at h
  exact h.symm

theorem centeredLineIntegral_antitone (f : ℝ → ℝ) (hf : Continuous f)
    (hdec : ∀ a b : ℝ, |a| ≤ |b| → f b ≤ f a)
    {H : ℝ} (hH : 0 ≤ H) :
    AntitoneOn (centeredLineIntegral f H) (Set.Ici (0:ℝ)) := by
  have hd : Differentiable ℝ (centeredLineIntegral f H) :=
    fun x => (centeredLineIntegral_hasDerivAt f hf H x).differentiableAt
  apply antitoneOn_of_deriv_nonpos (convex_Ici 0) hd.continuous.continuousOn
    hd.differentiableOn
  intro x hx
  have hx0 : 0 ≤ x := (interior_subset hx : x ∈ Set.Ici (0:ℝ))
  rw [(centeredLineIntegral_hasDerivAt f hf H x).deriv]
  apply sub_nonpos.mpr
  apply hdec
  rw [abs_of_nonneg (add_nonneg hx0 hH)]
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem centeredLineIntegral_le_center (f : ℝ → ℝ) (hf : Continuous f)
    (hdec : ∀ a b : ℝ, |a| ≤ |b| → f b ≤ f a)
    {H : ℝ} (hH : 0 ≤ H) (x : ℝ) :
    centeredLineIntegral f H x ≤ centeredLineIntegral f H 0 := by
  have heven (t : ℝ) : f (-t) = f t := by
    apply le_antisymm
    · exact hdec t (-t) (by simp)
    · exact hdec (-t) t (by simp)
  have ha := centeredLineIntegral_antitone f hf hdec hH
  by_cases hx : 0 ≤ x
  · exact ha (Set.mem_Ici.mpr le_rfl) hx hx
  · have hn : 0 ≤ -x := by linarith
    rw [← centeredLineIntegral_even f heven H x]
    exact ha (Set.mem_Ici.mpr le_rfl) hn hn

theorem coulombLineKernel_continuous {A : ℝ} (hA : 0 < A) :
    Continuous (coulombLineKernel A) := by
  apply Continuous.inv₀
  · exact (continuous_const.add (continuous_id.pow 2)).sqrt
  · intro t
    exact (Real.sqrt_pos.mpr (by nlinarith [sq_nonneg t] : 0 < A+t^2)).ne'

theorem coulombLineKernel_radial_antitone {A : ℝ} (hA : 0 < A)
    {a b : ℝ} (hab : |a| ≤ |b|) : coulombLineKernel A b ≤ coulombLineKernel A a := by
  have hs : a^2 ≤ b^2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg a) (abs_nonneg b)).mpr hab
  exact inv_anti₀ (Real.sqrt_pos.mpr (by nlinarith [sq_nonneg a] : 0 < A+a^2))
    (Real.sqrt_le_sqrt (by linarith : A+a^2 ≤ A+b^2))

theorem coulombLineIntegral_antitone {A H : ℝ} (hA : 0 < A) (hH : 0 ≤ H) :
    AntitoneOn (centeredLineIntegral (coulombLineKernel A) H) (Set.Ici (0:ℝ)) :=
  centeredLineIntegral_antitone _ (coulombLineKernel_continuous hA)
    (fun _ _ hab => coulombLineKernel_radial_antitone hA hab) hH

theorem coulombLineIntegral_le_center {A H : ℝ} (hA : 0 < A) (hH : 0 ≤ H) (x : ℝ) :
    centeredLineIntegral (coulombLineKernel A) H x ≤
      centeredLineIntegral (coulombLineKernel A) H 0 :=
  centeredLineIntegral_le_center _ (coulombLineKernel_continuous hA)
    (fun _ _ hab => coulombLineKernel_radial_antitone hA hab) hH x

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Nuclei_SlabKernelEstimates
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The inverse-cube horizontal tail bound and the exact absolute-value
integral that produce the quadratic potential of the infinite slab. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

theorem reciprocal_sqrt_difference_bound {R A B : ℝ} (hR : 0 < R)
    (hA : R^2 ≤ A) (hB : R^2 ≤ B) :
    |(Real.sqrt A)⁻¹ - (Real.sqrt B)⁻¹| ≤ |A-B|/(2*R^3) := by
  have hA0 : 0 ≤ A := (sq_nonneg R).trans hA
  have hB0 : 0 ≤ B := (sq_nonneg R).trans hB
  have hsA : R ≤ Real.sqrt A := by
    rw [← Real.sqrt_sq hR.le]
    exact Real.sqrt_le_sqrt hA
  have hsB : R ≤ Real.sqrt B := by
    rw [← Real.sqrt_sq hR.le]
    exact Real.sqrt_le_sqrt hB
  have hpA : 0 < Real.sqrt A := hR.trans_le hsA
  have hpB : 0 < Real.sqrt B := hR.trans_le hsB
  have hd : 0 < Real.sqrt A * Real.sqrt B * (Real.sqrt A + Real.sqrt B) := by positivity
  have he : (Real.sqrt A)⁻¹ - (Real.sqrt B)⁻¹ =
      (B-A)/(Real.sqrt A * Real.sqrt B * (Real.sqrt A+Real.sqrt B)) := by
    field_simp
    nlinarith [Real.sq_sqrt hA0, Real.sq_sqrt hB0]
  have hprod : R^2 ≤ Real.sqrt A * Real.sqrt B := by
    simpa only [pow_two] using mul_le_mul hsA hsB hR.le hpA.le
  have hsum : 2*R ≤ Real.sqrt A+Real.sqrt B := by linarith
  have hden : 2*R^3 ≤ Real.sqrt A*Real.sqrt B*(Real.sqrt A+Real.sqrt B) := by
    have h := mul_le_mul hprod hsum (by positivity : 0 ≤ 2*R)
      (mul_nonneg hpA.le hpB.le)
    nlinarith only [h]
  rw [he, abs_div, abs_of_pos hd, abs_sub_comm B A]
  exact div_le_div_of_nonneg_left (abs_nonneg _) (by positivity) hden

private theorem integral_abs_sub_of_inside {S z : ℝ} (_hS : 0 ≤ S)
    (hz : |z| ≤ S) :
    (∫ w in (-S)..S, |z-w|) = S^2+z^2 := by
  have hzlo : -S ≤ z := (abs_le.mp hz).1
  have hzhi : z ≤ S := (abs_le.mp hz).2
  have hc : Continuous (fun w : ℝ => |z-w|) := by fun_prop
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hc.intervalIntegrable (-S) z) (hc.intervalIntegrable z S)]
  have hl : (∫ w in (-S)..z, |z-w|) = ∫ w in (-S)..z, z-w := by
    apply intervalIntegral.integral_congr
    intro w hw
    have hmem : w ∈ Set.Icc (-S) z := by simpa only [Set.uIcc_of_le hzlo] using hw
    exact abs_of_nonneg (sub_nonneg.mpr hmem.2)
  have hr : (∫ w in z..S, |z-w|) = ∫ w in z..S, w-z := by
    apply intervalIntegral.integral_congr
    intro w hw
    have hmem : w ∈ Set.Icc z S := by simpa only [Set.uIcc_of_le hzhi] using hw
    change |z-w| = w-z
    rw [abs_of_nonpos (sub_nonpos.mpr hmem.1)]
    ring
  rw [hl, hr]
  calc
    _ = ((∫ w : ℝ in (-S)..z, z) - (∫ w : ℝ in (-S)..z, w)) +
        ((∫ w : ℝ in z..S, w) - (∫ w : ℝ in z..S, z)) := by
      exact congrArg₂ (· + ·)
        (intervalIntegral.integral_sub (f := fun _ : ℝ => z) (g := fun w : ℝ => w)
          (continuous_const.intervalIntegrable _ _) (continuous_id.intervalIntegrable _ _))
        (intervalIntegral.integral_sub (f := fun w : ℝ => w) (g := fun _ : ℝ => z)
          (continuous_id.intervalIntegrable _ _) (continuous_const.intervalIntegrable _ _))
    _ = _ := by
      simp only [intervalIntegral.integral_const, smul_eq_mul, integral_id]
      ring

theorem slab_absolute_difference_integral {S z : ℝ} (hS : 0 ≤ S) (hz : |z| ≤ S) :
    (∫ w in (-S)..S, (|z-w|-|w|)) = z^2 := by
  have hc : Continuous (fun w : ℝ => |z-w|) := by fun_prop
  rw [intervalIntegral.integral_sub (hc.intervalIntegrable _ _)
    (continuous_abs.intervalIntegrable _ _),
    integral_abs_sub_of_inside hS hz]
  have h := integral_abs_sub_of_inside hS (show |(0:ℝ)| ≤ S by simpa using hS)
  simp only [zero_sub, abs_neg, zero_pow (by decide : 2 ≠ 0), add_zero] at h
  rw [h]
  ring

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Nuclei_SlabCoordinates
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact ordinary product coordinates for the slab Coulomb integral.
These allow the finite-box potential to be treated by one-coordinate
integrals without changing the Euclidean volume normalization. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

theorem slabPotential_eq_setIntegral (rho H S : ℝ) (y : Position) :
    slabPotential rho H S y = -rho * ∫ x in slabDomain H S, Coulomb.coulombKernel (y-x) := by
  have he : (fun x => Coulomb.coulombKernel (y-x)*slabDensity rho H S x) =
      (slabDomain H S).indicator (fun x => rho*Coulomb.coulombKernel (y-x)) := by
    funext x
    by_cases hx : x ∈ slabDomain H S
    · simp only [slabDensity, Set.indicator_of_mem hx]
      ring
    · simp only [slabDensity, Set.indicator_of_notMem hx, mul_zero]
  unfold slabPotential
  rw [he, integral_indicator (slabDomain_isClosed H S).measurableSet, integral_const_mul]
  ring

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Nuclei_SlabRegularization
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.Coulomb.complexWindow_apply _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Regularization of the actual finite-slab potential. The singular
Coulomb limit is justified on the full volume integral; no continuity of
the slab indicator is assumed. -/

noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace ContinuumCoulomb

theorem slabCoulomb_integrableOn {H S : ℝ} (hH : 0 ≤ H) (hS : 0 ≤ S) (y : Position) :
    IntegrableOn (fun x => Coulomb.coulombKernel (y-x)) (slabDomain H S) := by
  have hm : Measurable (slabDensity 1 H S) :=
    measurable_const.indicator (slabDomain_isClosed H S).measurableSet
  have hb (x : Position) : ‖slabDensity 1 H S x‖ ≤ 1 := by
    by_cases hx : x ∈ slabDomain H S <;>
      simp [slabDensity, hx]
  have hi := Coulomb.coulomb_signed_convolution_integrable
    (slabDensity_integrable hH hS 1) hm hb y
  have he : (fun x => Coulomb.coulombKernel (y-x)*slabDensity 1 H S x) =
      (slabDomain H S).indicator (fun x => Coulomb.coulombKernel (y-x)) := by
    funext x
    by_cases hx : x ∈ slabDomain H S <;> simp [slabDensity, hx]
  rw [he, integrable_indicator_iff (slabDomain_isClosed H S).measurableSet] at hi
  exact hi

theorem regularizedSlab_integrableOn {epsilon H S : ℝ} (hepsilon : epsilon ≠ 0)
    (hH : 0 ≤ H) (hS : 0 ≤ S) (y : Position) :
    IntegrableOn (fun x => NeutralAtom.regularizedKernel epsilon (y-x)) (slabDomain H S) :=
  ((NeutralAtom.contDiff_regularizedKernel hepsilon).continuous.comp
    (continuous_const.sub continuous_id)).continuousOn.integrableOn_compact
      (slabDomain_isCompact hH hS)

theorem regularizedSlabPotential_tendsto {epsilon : ℕ → ℝ}
    (hepsilon : ∀ n, 0 < epsilon n) (hlim : Tendsto epsilon atTop (𝓝 0))
    (rho : ℝ) {H S : ℝ} (hH : 0 ≤ H) (hS : 0 ≤ S) (y : Position) :
    Tendsto (fun n => regularizedSlabPotential (epsilon n) rho H S y)
      atTop (𝓝 (slabPotential rho H S y)) := by
  have hae : ∀ᵐ x ∂(volume.restrict (slabDomain H S)), y-x ≠ 0 := by
    filter_upwards [ae_restrict_of_ae (volume.ae_ne y)] with x hx
    exact sub_ne_zero.mpr (Ne.symm hx)
  have hi := slabCoulomb_integrableOn hH hS y
  have hc : Tendsto
      (fun n => ∫ x in slabDomain H S, NeutralAtom.regularizedKernel (epsilon n) (y-x))
      atTop (𝓝 (∫ x in slabDomain H S, Coulomb.coulombKernel (y-x))) := by
    apply tendsto_integral_of_dominated_convergence
      (fun x => Coulomb.coulombKernel (y-x))
    · intro n
      exact ((NeutralAtom.contDiff_regularizedKernel (hepsilon n).ne').continuous.comp
        (continuous_const.sub continuous_id)).aestronglyMeasurable
    · exact hi
    · intro n
      filter_upwards [hae] with x hx
      rw [Real.norm_eq_abs, abs_of_nonneg (NeutralAtom.regularizedKernel_nonneg _ _)]
      exact NeutralAtom.regularizedKernel_le hx
    · filter_upwards [hae] with x hx
      exact NeutralAtom.regularizedKernel_tendsto hlim hx
  rw [slabPotential_eq_setIntegral]
  exact hc.const_mul (-rho)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Nuclei_SlabSections
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite product sections of the actual rectangular slab measure. -/

noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology
namespace ContinuumCoulomb

theorem slabProductDomain_preimage (H S : ℝ) :
    (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).symm ⁻¹' slabProductDomain H S = slabDomain H S := by
  ext x
  change (∀ i : Fin 3, i ∈ Set.univ → -slabSide H S i ≤ x i ∧ x i ≤ slabSide H S i) ↔
    |x 0| ≤ H ∧ |x 1| ≤ H ∧ |x 2| ≤ S
  simp only [Set.mem_univ, true_implies, abs_le]
  constructor
  · intro h
    exact ⟨by simpa [slabSide] using h 0,
      by simpa [slabSide] using h 1, by simpa [slabSide] using h 2⟩
  · rintro ⟨h0, h1, h2⟩ i
    fin_cases i
    · simpa [slabSide] using h0
    · simpa [slabSide] using h1
    · simpa [slabSide] using h2

theorem slabProductMeasure_eq (H S : ℝ) :
    slabProductMeasure H S = (volume : Measure (Fin 3 → ℝ)).restrict (slabProductDomain H S) := by
  exact (Measure.restrict_pi_pi (fun _ : Fin 3 => (volume : Measure ℝ))
    (fun i => Set.Icc (-slabSide H S i) (slabSide H S i))).symm

theorem slabProduct_measurePreserving (H S : ℝ) :
    MeasurePreserving (MeasurableEquiv.toLp 2 (Fin 3 → ℝ))
      (slabProductMeasure H S) (volume.restrict (slabDomain H S)) := by
  have hm := (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin 3)).restrict_preimage
    (s := slabProductDomain H S)
    (MeasurableSet.univ_pi (fun i => measurableSet_Icc))
  rw [slabProductDomain_preimage, ← slabProductMeasure_eq] at hm
  exact MeasurePreserving.symm (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).symm hm

theorem slabProduct_integral (H S : ℝ) (f : Position → ℝ) :
    (∫ x, f (WithLp.toLp 2 x) ∂slabProductMeasure H S) =
      ∫ y in slabDomain H S, f y := by
  exact (slabProduct_measurePreserving H S).integral_comp' f

theorem slabProduct_integrable (H S : ℝ) (f : Position → ℝ) :
    Integrable (fun x => f (WithLp.toLp 2 x)) (slabProductMeasure H S) ↔
      IntegrableOn f (slabDomain H S) :=
  (slabProduct_measurePreserving H S).integrable_comp_emb
    (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).measurableEmbedding

theorem regularizedKernel_eq_sqrt (epsilon : ℝ) (x : Position) :
    NeutralAtom.regularizedKernel epsilon x = (Real.sqrt (‖x‖^2+epsilon^2))⁻¹ := by
  rw [NeutralAtom.regularizedKernel, Real.sqrt_eq_rpow]
  convert Real.rpow_neg (add_nonneg (sq_nonneg ‖x‖) (sq_nonneg epsilon)) (1/2:ℝ) using 1
  all_goals try with_reducible_and_instances rfl
  norm_num

theorem regularizedKernel_section (epsilon : ℝ) (y : Position) (i : Fin 3)
    (t : ℝ) (v : Fin 2 → ℝ) :
    NeutralAtom.regularizedKernel epsilon (y-WithLp.toLp 2 (i.insertNth t v)) =
      coulombLineKernel
        (epsilon^2+∑ j : Fin 2, (y (i.succAbove j)-v j)^2) (y i-t) := by
  rw [regularizedKernel_eq_sqrt]
  unfold coulombLineKernel
  congr 2
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_succAbove _ i]
  simp only [PiLp.sub_apply, Fin.insertNth_apply_same,
    Fin.insertNth_apply_succAbove]
  ring

theorem zeroPositionCoordinate_same (i : Fin 3) (y : Position) :
    zeroPositionCoordinate i y i = 0 := by simp [zeroPositionCoordinate]

theorem zeroPositionCoordinate_other (i : Fin 3) (y : Position) (j : Fin 2) :
    zeroPositionCoordinate i y (i.succAbove j) = y (i.succAbove j) := by
  simp [zeroPositionCoordinate, Fin.succAbove_ne]

private theorem regularizedProduct_integrable {epsilon H S : ℝ} (hepsilon : epsilon ≠ 0)
    (hH : 0 ≤ H) (hS : 0 ≤ S) (y : Position) :
    Integrable (fun x : Fin 3 → ℝ => NeutralAtom.regularizedKernel epsilon
      (y-WithLp.toLp 2 x)) (slabProductMeasure H S) :=
  (slabProduct_integrable H S _).mpr (regularizedSlab_integrableOn hepsilon hH hS y)

private theorem regularizedSection_integrable {epsilon H S : ℝ} (hepsilon : epsilon ≠ 0)
    (hH : 0 ≤ H) (hS : 0 ≤ S) (y : Position) (i : Fin 3) :
    Integrable (fun p : ℝ × (Fin 2 → ℝ) => NeutralAtom.regularizedKernel epsilon
      (y-WithLp.toLp 2 (i.insertNth p.1 p.2)))
      ((slabAxisMeasure H S i).prod
        (Measure.pi (fun j : Fin 2 => slabAxisMeasure H S (i.succAbove j)))) := by
  have hp := (measurePreserving_piFinSuccAbove (slabAxisMeasure H S) i).symm
  have h := (hp.integrable_comp_emb
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) i).symm.measurableEmbedding).mpr
    (regularizedProduct_integrable hepsilon hH hS y)
  exact h

theorem regularizedSlab_sectionIntegral {epsilon H S : ℝ} (hepsilon : epsilon ≠ 0)
    (hH : 0 ≤ H) (hS : 0 ≤ S) (y : Position) (i : Fin 3) :
    (∫ x in slabDomain H S, NeutralAtom.regularizedKernel epsilon (y-x)) =
      ∫ v : Fin 2 → ℝ, ∫ t : ℝ,
        NeutralAtom.regularizedKernel epsilon (y-WithLp.toLp 2 (i.insertNth t v))
        ∂slabAxisMeasure H S i
        ∂Measure.pi (fun j : Fin 2 => slabAxisMeasure H S (i.succAbove j)) := by
  rw [← slabProduct_integral H S (fun x => NeutralAtom.regularizedKernel epsilon (y-x))]
  change (∫ x : Fin 3 → ℝ, NeutralAtom.regularizedKernel epsilon (y-WithLp.toLp 2 x)
    ∂Measure.pi (slabAxisMeasure H S)) = _
  rw [← ((measurePreserving_piFinSuccAbove (slabAxisMeasure H S) i).symm).integral_comp']
  simp only [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv]
  exact integral_prod_symm _ (regularizedSection_integrable hepsilon hH hS y i)

private theorem coulombLine_setIntegral_le_center {A H : ℝ} (hA : 0 < A) (hH : 0 ≤ H)
    (x : ℝ) :
    (∫ t in Set.Icc (-H) H, coulombLineKernel A (x-t)) ≤
      ∫ t in Set.Icc (-H) H, coulombLineKernel A (0-t) := by
  have h := coulombLineIntegral_le_center hA hH x
  simp only [centeredLineIntegral_translate,
    intervalIntegral.integral_of_le (show -H ≤ H by linarith),
    ← integral_Icc_eq_integral_Ioc] at h
  exact h

/-- Centering one coordinate increases the attractive Coulomb integral.
The statement holds for the actual finite slab, before taking the singular limit. -/
theorem regularizedSlab_coordinate_max {epsilon H S : ℝ} (hepsilon : epsilon ≠ 0)
    (hH : 0 ≤ H) (hS : 0 ≤ S) (y : Position) (i : Fin 3) :
    (∫ x in slabDomain H S, NeutralAtom.regularizedKernel epsilon (y-x)) ≤
      ∫ x in slabDomain H S, NeutralAtom.regularizedKernel epsilon
        (zeroPositionCoordinate i y-x) := by
  rw [regularizedSlab_sectionIntegral hepsilon hH hS y i,
    regularizedSlab_sectionIntegral hepsilon hH hS (zeroPositionCoordinate i y) i]
  apply integral_mono
    (regularizedSection_integrable hepsilon hH hS y i).integral_prod_right
    (regularizedSection_integrable hepsilon hH hS (zeroPositionCoordinate i y) i).integral_prod_right
  intro v
  simp_rw [regularizedKernel_section, zeroPositionCoordinate_same, zeroPositionCoordinate_other]
  have hA : 0 < epsilon^2+∑ j : Fin 2, (y (i.succAbove j)-v j)^2 :=
    add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero hepsilon)
      (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  have hside : 0 ≤ slabSide H S i := by unfold slabSide; split <;> assumption
  exact coulombLine_setIntegral_le_center hA hside (y i)

/-- The actual singular finite-slab potential is minimized in each centered
coordinate. The regularized comparison passes through a dominated limit. -/
theorem slabPotential_coordinate_min {rho H S : ℝ} (hrho : 0 ≤ rho)
    (hH : 0 ≤ H) (hS : 0 ≤ S) (y : Position) (i : Fin 3) :
    slabPotential rho H S (zeroPositionCoordinate i y) ≤ slabPotential rho H S y := by
  let epsilon : ℕ → ℝ := fun n => ((n:ℝ)+1)⁻¹
  have hep (n : ℕ) : 0 < epsilon n := by dsimp [epsilon]; positivity
  have heps : Tendsto epsilon atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp
      (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
  apply le_of_tendsto_of_tendsto
    (regularizedSlabPotential_tendsto hep heps rho hH hS (zeroPositionCoordinate i y))
    (regularizedSlabPotential_tendsto hep heps rho hH hS y)
  exact Filter.Eventually.of_forall (fun n =>
    mul_le_mul_of_nonpos_left (regularizedSlab_coordinate_max (hep n).ne' hH hS y i)
      (neg_nonpos.mpr hrho))

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Nuclei_SlabMonotonicity
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Coordinatewise monotonicity of the actual singular slab potential.
This strengthens centering to comparison at any two absolute coordinates. -/

noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace ContinuumCoulomb

theorem coulombLineIntegral_abs_antitone {A H x y : ℝ} (hA : 0 < A)
    (hH : 0 ≤ H) (hxy : |x| ≤ |y|) :
    centeredLineIntegral (coulombLineKernel A) H y ≤
      centeredLineIntegral (coulombLineKernel A) H x := by
  have he (t : ℝ) : coulombLineKernel A (-t) = coulombLineKernel A t := by
    simp [coulombLineKernel]
  have ha (t : ℝ) : centeredLineIntegral (coulombLineKernel A) H |t| =
      centeredLineIntegral (coulombLineKernel A) H t := by
    rcases le_total 0 t with ht | ht
    · rw [abs_of_nonneg ht]
    · rw [abs_of_nonpos ht]
      exact centeredLineIntegral_even _ he H t
  rw [← ha x, ← ha y]
  exact coulombLineIntegral_antitone hA hH (abs_nonneg x) (abs_nonneg y) hxy

private theorem coulombLine_setIntegral_abs_antitone {A H x y : ℝ}
    (hA : 0 < A) (hH : 0 ≤ H) (hxy : |x| ≤ |y|) :
    (∫ t in Set.Icc (-H) H, coulombLineKernel A (y-t)) ≤
      ∫ t in Set.Icc (-H) H, coulombLineKernel A (x-t) := by
  have h := coulombLineIntegral_abs_antitone hA hH hxy
  simp only [centeredLineIntegral_translate,
    intervalIntegral.integral_of_le (show -H ≤ H by linarith),
    ← integral_Icc_eq_integral_Ioc] at h
  exact h

private theorem regularizedSections_integrable {epsilon H S : ℝ} (hepsilon : epsilon ≠ 0)
    (hH : 0 ≤ H) (hS : 0 ≤ S) (y : Position) (i : Fin 3) :
    Integrable (fun p : ℝ × (Fin 2 → ℝ) => NeutralAtom.regularizedKernel epsilon
      (y-WithLp.toLp 2 (i.insertNth p.1 p.2)))
      ((slabAxisMeasure H S i).prod
        (Measure.pi (fun j : Fin 2 => slabAxisMeasure H S (i.succAbove j)))) := by
  have hp := (measurePreserving_piFinSuccAbove (slabAxisMeasure H S) i).symm
  exact (hp.integrable_comp_emb
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) i).symm.measurableEmbedding).mpr
      ((slabProduct_integrable H S _).mpr (regularizedSlab_integrableOn hepsilon hH hS y))

theorem regularizedSlab_coordinate_antitone {epsilon H S : ℝ} (hepsilon : epsilon ≠ 0)
    (hH : 0 ≤ H) (hS : 0 ≤ S) (x y : Position) (i : Fin 3)
    (hother : ∀ j : Fin 2, x (i.succAbove j) = y (i.succAbove j))
    (hxy : |x i| ≤ |y i|) :
    (∫ b in slabDomain H S, NeutralAtom.regularizedKernel epsilon (y-b)) ≤
      ∫ b in slabDomain H S, NeutralAtom.regularizedKernel epsilon (x-b) := by
  rw [regularizedSlab_sectionIntegral hepsilon hH hS y i,
    regularizedSlab_sectionIntegral hepsilon hH hS x i]
  apply integral_mono
    (regularizedSections_integrable hepsilon hH hS y i).integral_prod_right
    (regularizedSections_integrable hepsilon hH hS x i).integral_prod_right
  intro v
  simp_rw [regularizedKernel_section, hother]
  have hA : 0 < epsilon^2+∑ j : Fin 2, (y (i.succAbove j)-v j)^2 :=
    add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero hepsilon)
      (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  have hside : 0 ≤ slabSide H S i := by unfold slabSide; split <;> assumption
  exact coulombLine_setIntegral_abs_antitone hA hside hxy

/-- Increasing a single absolute coordinate increases the singular slab potential. -/
theorem slabPotential_coordinate_monotone {rho H S : ℝ} (hrho : 0 ≤ rho)
    (hH : 0 ≤ H) (hS : 0 ≤ S) (x y : Position) (i : Fin 3)
    (hother : ∀ j : Fin 2, x (i.succAbove j) = y (i.succAbove j))
    (hxy : |x i| ≤ |y i|) : slabPotential rho H S x ≤ slabPotential rho H S y := by
  let epsilon : ℕ → ℝ := fun n => ((n:ℝ)+1)⁻¹
  have hep (n : ℕ) : 0 < epsilon n := by dsimp [epsilon]; positivity
  have heps : Tendsto epsilon atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp
      (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
  apply le_of_tendsto_of_tendsto
    (regularizedSlabPotential_tendsto hep heps rho hH hS x)
    (regularizedSlabPotential_tendsto hep heps rho hH hS y)
  exact Filter.Eventually.of_forall (fun n =>
    mul_le_mul_of_nonpos_left
      (regularizedSlab_coordinate_antitone (hep n).ne' hH hS x y i hother hxy)
      (neg_nonpos.mpr hrho))

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_PlanarGroundTransform
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.planarHeatResolventPrimitive_zero _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The planar manufactured well's ground-state transform. Integration by
parts establishes positivity on actual compact C¹ test functions. Existence,
decay and the excitation gap of the specific resolvent-generated mode remain
separate analytic steps. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb

theorem planarPartial_C1 {phi : PlanarPosition → ℝ} (hphi : ContDiff ℝ 2 phi)
    (e : PlanarPosition) : ContDiff ℝ 1 (planarPartial phi e) :=
  (hphi.fderiv_right (show (1 : WithTop ℕ∞) + 1 ≤ 2 by norm_num)).clm_apply contDiff_const

theorem planarPartial_mul_square (phi v : PlanarPosition → ℝ)
    (hphi : ContDiff ℝ 1 phi) (hv : ContDiff ℝ 1 v) (e x : PlanarPosition) :
    planarPartial (fun y => phi y * v y ^ 2) e x =
      planarPartial phi e x * v x ^ 2 + 2 * phi x * v x * planarPartial v e x := by
  rw [planarPartial_mul phi (fun y => v y ^ 2) hphi (hv.pow 2)]
  have hp : planarPartial (fun y => v y ^ 2) e x = 2 * v x * planarPartial v e x := by
    dsimp [planarPartial]
    rw [fderiv_fun_pow 2 (hv.differentiable (by norm_num) x)]
    simp only [smul_apply, smul_eq_mul, nsmul_eq_mul, Nat.reduceSub, pow_one, Nat.cast_ofNat]
  rw [hp]
  ring

theorem planar_transform_integrable (phi v : PlanarPosition → ℝ)
    (hphi : ContDiff ℝ 2 phi) (hv : ContDiff ℝ 1 v) (hc : HasCompactSupport v)
    (e : PlanarPosition) :
    Integrable (fun x => planarPartial (fun y => phi y * v y ^ 2) e x * planarPartial phi e x) ∧
    Integrable (fun x => (phi x * v x ^ 2) * planarPartial (planarPartial phi e) e x) ∧
    Integrable (fun x => (phi x * v x ^ 2) * planarPartial phi e x) ∧
    Integrable (fun x => phi x ^ 2 * planarPartial v e x ^ 2) := by
  have hphi1 : ContDiff ℝ 1 phi := hphi.of_le (by norm_num)
  have hp := planarPartial_C1 hphi e
  have hvc : HasCompactSupport (planarPartial v e) := hc.fderiv_apply ℝ e
  have hv2c : HasCompactSupport (fun x => v x ^ 2) :=
    hc.comp_left (g := fun t : ℝ => t ^ 2) (by norm_num)
  have hf : ContDiff ℝ 1 (fun x => phi x * v x ^ 2) := hphi1.mul (hv.pow 2)
  have hfc : HasCompactSupport (fun x => phi x * v x ^ 2) := hv2c.mul_left
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact ((planarPartial_continuous hf e).mul hp.continuous).integrable_of_hasCompactSupport
      (hfc.fderiv_apply ℝ e).mul_right
  · exact (hf.continuous.mul (planarPartial_continuous hp e)).integrable_of_hasCompactSupport
      hfc.mul_right
  · exact (hf.continuous.mul hp.continuous).integrable_of_hasCompactSupport hfc.mul_right
  · have hsq : HasCompactSupport (fun x => planarPartial v e x ^ 2) :=
      hvc.comp_left (g := fun t : ℝ => t ^ 2) (by norm_num)
    have hcompact : HasCompactSupport (fun x => phi x ^ 2 * planarPartial v e x ^ 2) :=
      hsq.mul_left
    exact ((hphi.continuous.pow 2).mul ((planarPartial_continuous hv e).pow 2)).integrable_of_hasCompactSupport hcompact

theorem planar_transform_ibp (phi v : PlanarPosition → ℝ)
    (hphi : ContDiff ℝ 2 phi) (hv : ContDiff ℝ 1 v) (hc : HasCompactSupport v)
    (e : PlanarPosition) :
    (∫ x, (phi x * v x ^ 2) * planarPartial (planarPartial phi e) e x) =
      -(∫ x, planarPartial (fun y => phi y * v y ^ 2) e x * planarPartial phi e x) := by
  obtain ⟨hA, hB, hfg, hR⟩ := planar_transform_integrable phi v hphi hv hc e
  have hf : ContDiff ℝ 1 (fun x => phi x * v x ^ 2) :=
    (hphi.of_le (by norm_num)).mul (hv.pow 2)
  exact integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable hA hB hfg
    (fun x _ => hf.differentiable (by norm_num) x)
    (fun x _ => (planarPartial_C1 hphi e).differentiable (by norm_num) x)

theorem planar_ground_transform_direction (phi v : PlanarPosition → ℝ)
    (hphi : ContDiff ℝ 2 phi) (hv : ContDiff ℝ 1 v) (hc : HasCompactSupport v)
    (e : PlanarPosition) :
    (∫ x, planarPartial (fun y => phi y * v y) e x ^ 2 +
      phi x * planarPartial (planarPartial phi e) e x * v x ^ 2) =
      ∫ x, phi x ^ 2 * planarPartial v e x ^ 2 := by
  have hphi1 : ContDiff ℝ 1 phi := hphi.of_le (by norm_num)
  obtain ⟨hA, hB, hfg, hR⟩ := planar_transform_integrable phi v hphi hv hc e
  have heq : (fun x => planarPartial (fun y => phi y * v y) e x ^ 2 +
      phi x * planarPartial (planarPartial phi e) e x * v x ^ 2) =
      (fun x => (phi x ^ 2 * planarPartial v e x ^ 2 +
        planarPartial (fun y => phi y * v y ^ 2) e x * planarPartial phi e x) +
        (phi x * v x ^ 2) * planarPartial (planarPartial phi e) e x) := by
    funext x
    rw [planarPartial_mul phi v hphi1 hv, planarPartial_mul_square phi v hphi1 hv]
    ring
  rw [heq]
  change (∫ x, ((fun y => phi y ^ 2 * planarPartial v e y ^ 2) +
    (fun y => planarPartial (fun z => phi z * v z ^ 2) e y * planarPartial phi e y)) x +
    (fun y => phi y * v y ^ 2 * planarPartial (planarPartial phi e) e y) x) = _
  rw [integral_add (hR.add hA) hB, integral_add' hR hA,
    planar_transform_ibp phi v hphi hv hc e]
  ring

/-- Nonnegativity of the shifted manufactured-well form on compact C¹
tests follows from the actual directional integration-by-parts identities. -/
theorem planar_ground_transform_nonnegative (phi v : PlanarPosition → ℝ)
    (hphi : ContDiff ℝ 2 phi) (hv : ContDiff ℝ 1 v) (hc : HasCompactSupport v) :
    0 ≤ ∑ a : Fin 2, ∫ x,
      planarPartial (fun y => phi y * v y) (planarAxis a) x ^ 2 +
        phi x * planarPartial (planarPartial phi (planarAxis a)) (planarAxis a) x * v x ^ 2 := by
  apply Finset.sum_nonneg
  intro a _
  rw [planar_ground_transform_direction phi v hphi hv hc]
  exact integral_nonneg (fun _ => mul_nonneg (sq_nonneg _) (sq_nonneg _))

theorem planar_partial_square_integrable (u : PlanarPosition → ℝ)
    (hu : ContDiff ℝ 1 u) (hc : HasCompactSupport u) (e : PlanarPosition) :
    Integrable (fun x => planarPartial u e x ^ 2) := by
  have hpc : HasCompactSupport (planarPartial u e) := hc.fderiv_apply ℝ e
  have hsq : HasCompactSupport (fun x => planarPartial u e x ^ 2) :=
    hpc.comp_left (g := fun t : ℝ => t ^ 2) (by norm_num)
  exact ((planarPartial_continuous hu e).pow 2).integrable_of_hasCompactSupport hsq

theorem planar_transform_energy_split (phi v : PlanarPosition → ℝ)
    (hphi : ContDiff ℝ 2 phi) (hv : ContDiff ℝ 1 v) (hc : HasCompactSupport v) :
    (∑ a : Fin 2, ∫ x,
      planarPartial (fun y => phi y * v y) (planarAxis a) x ^ 2 +
        phi x * planarPartial (planarPartial phi (planarAxis a)) (planarAxis a) x * v x ^ 2) =
    (∑ a : Fin 2, ∫ x, planarPartial (fun y => phi y * v y) (planarAxis a) x ^ 2) +
      ∫ x, phi x * planarLaplacian phi x * v x ^ 2 := by
  have hu : ContDiff ℝ 1 (fun x => phi x * v x) := (hphi.of_le (by norm_num)).mul hv
  have huc : HasCompactSupport (fun x => phi x * v x) := hc.mul_left
  have hvc : HasCompactSupport (fun x => v x ^ 2) :=
    hc.comp_left (g := fun t : ℝ => t ^ 2) (by norm_num)
  have hb (a : Fin 2) : Integrable (fun x =>
      phi x * planarPartial (planarPartial phi (planarAxis a)) (planarAxis a) x * v x ^ 2) := by
    have hs : HasCompactSupport (fun x =>
        phi x * planarPartial (planarPartial phi (planarAxis a)) (planarAxis a) x * v x ^ 2) := hvc.mul_left
    exact ((hphi.continuous.mul (planarPartial_continuous (planarPartial_C1 hphi _) _)).mul
      (hv.continuous.pow 2)).integrable_of_hasCompactSupport hs
  have hd (a : Fin 2) := planar_partial_square_integrable _ hu huc (planarAxis a)
  simp_rw [integral_add (hd _) (hb _)]
  rw [Finset.sum_add_distrib, ← integral_finsetSum _ (fun a _ => hb a)]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [planarLaplacian, Finset.mul_sum, Finset.sum_mul]

/-- A positive classical mode at energy `-1/2` gives the lower bound on
every compact C¹ test, without assuming the well's spectral conclusion. -/
theorem planar_positive_mode_form_lower (phi W u : PlanarPosition → ℝ)
    (hphi : ContDiff ℝ 2 phi) (hpos : ∀ x, 0 < phi x) (hW : Continuous W)
    (heigen : ∀ x, planarLaplacian phi x = (2 * W x + 1) * phi x)
    (hu : ContDiff ℝ 1 u) (hc : HasCompactSupport u) :
    -(1 / 2 : ℝ) * (∫ x, u x ^ 2) ≤ planarTestForm W u := by
  let v : PlanarPosition → ℝ := fun x => u x / phi x
  have hv : ContDiff ℝ 1 v := hu.div (hphi.of_le (by norm_num)) (fun x => (hpos x).ne')
  have hvc : HasCompactSupport v := by
    change HasCompactSupport (fun x => u x / phi x)
    simp only [div_eq_mul_inv]
    exact hc.mul_right
  have hv2c : HasCompactSupport (fun x => v x ^ 2) :=
    hvc.comp_left (g := fun t : ℝ => t ^ 2) (by norm_num)
  have hu2c : HasCompactSupport (fun x => u x ^ 2) :=
    hc.comp_left (g := fun t : ℝ => t ^ 2) (by norm_num)
  have hfactor (x : PlanarPosition) : phi x * v x = u x := by
    dsimp [v]
    field_simp [(hpos x).ne']
  have hfactor_fun : (fun x => phi x * v x) = u := funext hfactor
  have hB (x : PlanarPosition) :
      phi x * planarLaplacian phi x * v x ^ 2 = (2 * W x + 1) * u x ^ 2 := by
    rw [heigen]
    calc
      _ = (2 * W x + 1) * (phi x * v x) ^ 2 := by ring
      _ = _ := by rw [hfactor]
  have hnonneg := planar_ground_transform_nonnegative phi v hphi hv hvc
  rw [planar_transform_energy_split phi v hphi hv hvc, hfactor_fun] at hnonneg
  simp_rw [hB] at hnonneg
  have hpot : Integrable (fun x => W x * u x ^ 2) :=
    (hW.mul (hu.continuous.pow 2)).integrable_of_hasCompactSupport hu2c.mul_left
  have hmass : Integrable (fun x => u x ^ 2) :=
    (hu.continuous.pow 2).integrable_of_hasCompactSupport hu2c
  have heq : (∫ x, (2 * W x + 1) * u x ^ 2) =
      2 * (∫ x, W x * u x ^ 2) + ∫ x, u x ^ 2 := by
    rw [show (fun x => (2 * W x + 1) * u x ^ 2) =
      (fun x => 2 * (W x * u x ^ 2) + u x ^ 2) from by funext x; ring]
    rw [integral_add (hpot.const_mul 2) hmass, integral_const_mul]
  rw [heq] at hnonneg
  dsimp [planarTestForm]
  linarith

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Nuclei_SlabPlanarIntegral
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.planarHeatResolventPrimitive_zero _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact horizontal-plane Coulomb differences. The individually divergent
plane integrals are never separated; their integrable difference has a
finite antiderivative and a zero limit at infinity. -/

noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace ContinuumCoulomb

theorem slabRootDifference_quotient {A B : ℝ} (hA : 0 < A) (hB : 0 < B) (r : ℝ) :
    slabRootDifference A B r = (A-B)/(Real.sqrt (r^2+A)+Real.sqrt (r^2+B)) := by
  have hpA : 0 < r^2+A := by positivity
  have hpB : 0 < r^2+B := by positivity
  have hden : 0 < Real.sqrt (r^2+A)+Real.sqrt (r^2+B) := by positivity
  apply (eq_div_iff hden.ne').mpr
  unfold slabRootDifference
  nlinarith [Real.sq_sqrt hpA.le, Real.sq_sqrt hpB.le]

theorem slabRootDifference_tendsto {A B : ℝ} (hA : 0 < A) (hB : 0 < B) :
    Tendsto (slabRootDifference A B) atTop (𝓝 0) := by
  have hp : Tendsto (fun r : ℝ => r^2) atTop atTop := tendsto_pow_atTop (by norm_num)
  have ha := Real.tendsto_sqrt_atTop.comp (tendsto_atTop_add_const_right _ A hp)
  have hb := Real.tendsto_sqrt_atTop.comp (tendsto_atTop_add_const_right _ B hp)
  have hd := ha.atTop_add_atTop hb
  simpa only [Function.comp_apply, ← slabRootDifference_quotient hA hB] using hd.const_div_atTop (A-B)

theorem slabRootDifference_hasDerivAt {A B : ℝ} (hA : 0 < A) (hB : 0 < B) (r : ℝ) :
    HasDerivAt (slabRootDifference A B) (slabRadialDifference A B r) r := by
  have hpA : 0 < r^2+A := by positivity
  have hpB : 0 < r^2+B := by positivity
  have ha := (((hasDerivAt_id r).pow 2).add_const A).sqrt hpA.ne'
  have hb := (((hasDerivAt_id r).pow 2).add_const B).sqrt hpB.ne'
  refine (ha.fun_sub hb).congr_deriv ?_
  · dsimp only [slabRadialDifference, coulombLineKernel]
    simp only [Pi.pow_apply, id_eq, Nat.cast_ofNat, Nat.reduceSub, pow_one]
    rw [add_comm A (r^2), add_comm B (r^2)]
    field_simp

theorem slabRadialDifference_nonnegative {A B : ℝ} (hA : 0 < A) (hAB : A ≤ B)
    {r : ℝ} (hr : 0 ≤ r) : 0 ≤ slabRadialDifference A B r := by
  apply mul_nonneg hr
  apply sub_nonneg.mpr
  unfold coulombLineKernel
  exact inv_anti₀ (Real.sqrt_pos.mpr (by positivity : 0 < A+r^2))
    (Real.sqrt_le_sqrt (by linarith : A+r^2 ≤ B+r^2))

theorem slabRadialDifference_integrable {A B : ℝ} (hA : 0 < A) (hB : 0 < B) :
    IntegrableOn (slabRadialDifference A B) (Set.Ioi (0:ℝ)) := by
  rcases le_total A B with hAB | hBA
  · exact integrableOn_Ioi_deriv_of_nonneg'
      (fun r _ => slabRootDifference_hasDerivAt hA hB r)
      (fun r hr => slabRadialDifference_nonnegative hA hAB hr.le)
      (slabRootDifference_tendsto hA hB)
  · have h := (integrableOn_Ioi_deriv_of_nonneg'
      (fun r _ => slabRootDifference_hasDerivAt hB hA r)
      (fun r hr => slabRadialDifference_nonnegative hB hBA hr.le)
      (slabRootDifference_tendsto hB hA)).neg
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    funext r
    change slabRadialDifference A B r = -slabRadialDifference B A r
    unfold slabRadialDifference
    ring

theorem slabRadialDifference_integral {A B : ℝ} (hA : 0 < A) (hB : 0 < B) :
    (∫ r in Set.Ioi (0:ℝ), slabRadialDifference A B r) = Real.sqrt B-Real.sqrt A := by
  have h := integral_Ioi_of_hasDerivAt_of_tendsto'
    (fun r _ => slabRootDifference_hasDerivAt hA hB r)
    (slabRadialDifference_integrable hA hB) (slabRootDifference_tendsto hA hB)
  simpa [slabRootDifference] using h

theorem slabPlanarDifference_integrable {A B : ℝ} (hA : 0 < A) (hB : 0 < B) :
    Integrable (fun p : PlanarPosition =>
      coulombLineKernel A ‖p‖-coulombLineKernel B ‖p‖) := by
  apply (integrable_fun_norm_addHaar (E := PlanarPosition) volume
    (f := fun r => coulombLineKernel A r-coulombLineKernel B r)).mpr
  simp only [finrank_euclideanSpace_fin, Nat.reduceSub, pow_one, smul_eq_mul]
  exact slabRadialDifference_integrable hA hB

/-- Exact difference of two horizontal Coulomb plane integrals. -/
theorem slabPlanarDifference_integral {A B : ℝ} (hA : 0 < A) (hB : 0 < B) :
    (∫ p : PlanarPosition, coulombLineKernel A ‖p‖-coulombLineKernel B ‖p‖) =
      2*Real.pi*(Real.sqrt B-Real.sqrt A) := by
  have h := integral_fun_norm_addHaar (E := PlanarPosition) volume
    (fun r => coulombLineKernel A r-coulombLineKernel B r)
  simp only [finrank_euclideanSpace_fin, Nat.reduceSub, pow_one, smul_eq_mul,
    nsmul_eq_mul] at h
  have hm : volume.real (Metric.ball (0 : PlanarPosition) 1) = Real.pi := by
    simp [Measure.real, EuclideanSpace.volume_ball_fin_two, ENNReal.toReal_ofReal Real.pi_pos.le]
  have hi : (∫ r in Set.Ioi (0:ℝ),
      r*(coulombLineKernel A r-coulombLineKernel B r)) = Real.sqrt B-Real.sqrt A :=
    slabRadialDifference_integral hA hB
  rw [hm, hi] at h
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  norm_num
  ring

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Nuclei_SlabPlanarTail
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.planarHeatResolventPrimitive_zero _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The inverse-cube tail in two horizontal dimensions. Its exact mass is
`2π/H`, giving the finite-slab truncation error without divergent integrals. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

private theorem slabRadialTail_weight {H : ℝ} (hH : 0 < H) (r : ℝ) :
    r * slabRadialTail H r = (Set.Ioi H).indicator (fun t : ℝ => t ^ (-2 : ℝ)) r := by
  by_cases hr : H < r
  · simp only [slabRadialTail, Set.indicator_of_mem (Set.mem_Ioi.mpr hr)]
    have hp : 0 < r := hH.trans hr
    rw [show (-2 : ℝ) = -3+1 by norm_num, Real.rpow_add hp, Real.rpow_one]
    ring
  · simp [slabRadialTail, hr]

private theorem slabRadialTail_weight_integrable {H : ℝ} (hH : 0 < H) :
    IntegrableOn (fun r : ℝ => r * slabRadialTail H r) (Set.Ioi 0) := by
  have hi := integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) hH
  have h := (integrable_indicator_iff measurableSet_Ioi).mpr hi
  simpa only [slabRadialTail_weight hH] using h.integrableOn

private theorem slabRadialTail_weight_integral {H : ℝ} (hH : 0 < H) :
    (∫ r in Set.Ioi (0:ℝ), r * slabRadialTail H r) = H⁻¹ := by
  simp_rw [slabRadialTail_weight hH]
  rw [integral_indicator measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi]
  rw [Set.Ioi_inter_Ioi, max_eq_left hH.le]
  have h := integral_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) hH
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  norm_num
  rw [Real.rpow_neg_one]

theorem slabPlanarTail_integrable {H : ℝ} (hH : 0 < H) :
    Integrable (slabPlanarTail H) := by
  apply (integrable_fun_norm_addHaar (E := PlanarPosition) volume
    (f := slabRadialTail H)).mpr
  simp only [finrank_euclideanSpace_fin, Nat.reduceSub, pow_one, smul_eq_mul]
  exact slabRadialTail_weight_integrable hH

theorem slabPlanarTail_nonnegative (H : ℝ) (p : PlanarPosition) :
    0 ≤ slabPlanarTail H p := by
  unfold slabPlanarTail slabRadialTail
  by_cases h : H < ‖p‖
  · rw [Set.indicator_of_mem (Set.mem_Ioi.mpr h)]
    exact Real.rpow_nonneg (norm_nonneg p) _
  · simp [h]

/-- The exact horizontal inverse-cube tail mass. -/
theorem slabPlanarTail_integral {H : ℝ} (hH : 0 < H) :
    (∫ p, slabPlanarTail H p) = 2*Real.pi/H := by
  have h := integral_fun_norm_addHaar (E := PlanarPosition) volume (slabRadialTail H)
  simp only [finrank_euclideanSpace_fin, Nat.reduceSub, pow_one, smul_eq_mul,
    nsmul_eq_mul] at h
  have hm : volume.real (Metric.ball (0 : PlanarPosition) 1) = Real.pi := by
    simp [Measure.real, EuclideanSpace.volume_ball_fin_two, ENNReal.toReal_ofReal Real.pi_pos.le]
  rw [hm, slabRadialTail_weight_integral hH] at h
  change (∫ p, slabRadialTail H ‖p‖) = _
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  norm_num
  ring

theorem slabPlanarBox_measurable (H : ℝ) : MeasurableSet (slabPlanarBox H) := by
  have h0 : IsClosed {p : PlanarPosition | |p 0| ≤ H} :=
    isClosed_le (by fun_prop) continuous_const
  have h1 : IsClosed {p : PlanarPosition | |p 1| ≤ H} :=
    isClosed_le (by fun_prop) continuous_const
  exact (h0.inter h1).measurableSet

theorem slabPlanarBox_compl_norm {H : ℝ} {p : PlanarPosition}
    (hp : p ∉ slabPlanarBox H) : H < ‖p‖ := by
  by_contra h
  have hn : ‖p‖ ≤ H := le_of_not_gt h
  apply hp
  have h0 : |p 0| ≤ ‖p‖ := by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le p 0
  have h1 : |p 1| ≤ ‖p‖ := by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le p 1
  exact ⟨h0.trans hn, h1.trans hn⟩

theorem slab_regularized_line_difference_uniform {R S epsilon z w : ℝ}
    (hR : 0 < R) (hz : |z| ≤ S) (hw : |w| ≤ S) :
    |coulombLineKernel (epsilon^2+(z-w)^2) R -
      coulombLineKernel (epsilon^2+w^2) R| ≤ 3*S^2/(2*R^3) := by
  have h := reciprocal_sqrt_difference_bound hR
    (show R^2 ≤ (epsilon^2+(z-w)^2)+R^2 by nlinarith [sq_nonneg epsilon, sq_nonneg (z-w)])
    (show R^2 ≤ (epsilon^2+w^2)+R^2 by nlinarith [sq_nonneg epsilon, sq_nonneg w])
  have hS : 0 ≤ S := (abs_nonneg z).trans hz
  have hz2 : z^2 ≤ S^2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg z) hS).mpr hz
  have hzw : |z*w| ≤ S^2 := by
    rw [abs_mul, pow_two]
    exact mul_le_mul hz hw (abs_nonneg w) hS
  have ha : |(epsilon^2+(z-w)^2+R^2)-(epsilon^2+w^2+R^2)| ≤ 3*S^2 := by
    rw [show (epsilon^2+(z-w)^2+R^2)-(epsilon^2+w^2+R^2) = z^2-2*(z*w) by ring]
    apply (abs_sub _ _).trans
    rw [abs_of_nonneg (sq_nonneg z), abs_mul, abs_of_pos (by norm_num : (0:ℝ)<2)]
    linarith
  exact h.trans (div_le_div_of_nonneg_right ha (by positivity))

/-- The finite square loses at most the integrable radial tail. -/
theorem slabPlanarDifference_tail_bound {H S epsilon z w : ℝ} (hH : 0 < H)
    (hepsilon : epsilon ≠ 0) (hz : |z| ≤ S) (hw : |w| ≤ S) :
    |∫ p in (slabPlanarBox H)ᶜ,
      (coulombLineKernel (epsilon^2+(z-w)^2) ‖p‖-
       coulombLineKernel (epsilon^2+w^2) ‖p‖)| ≤ 3*Real.pi*S^2/H := by
  let f := fun p : PlanarPosition =>
    coulombLineKernel (epsilon^2+(z-w)^2) ‖p‖-
      coulombLineKernel (epsilon^2+w^2) ‖p‖
  have hA : 0 < epsilon^2+(z-w)^2 := add_pos_of_pos_of_nonneg
    (sq_pos_of_ne_zero hepsilon) (sq_nonneg _)
  have hB : 0 < epsilon^2+w^2 := add_pos_of_pos_of_nonneg
    (sq_pos_of_ne_zero hepsilon) (sq_nonneg _)
  have hi : Integrable f := slabPlanarDifference_integrable hA hB
  have ht : Integrable (fun p => (3*S^2/2)*slabPlanarTail H p) :=
    (slabPlanarTail_integrable hH).const_mul _
  have hpt (p : PlanarPosition) (hp : p ∈ (slabPlanarBox H)ᶜ) :
      ‖f p‖ ≤ (3*S^2/2)*slabPlanarTail H p := by
    have hn := slabPlanarBox_compl_norm hp
    have hn0 : 0 < ‖p‖ := hH.trans hn
    have hbound := slab_regularized_line_difference_uniform (epsilon := epsilon) hn0 hz hw
    rw [Real.norm_eq_abs]
    change |coulombLineKernel (epsilon^2+(z-w)^2) ‖p‖-
      coulombLineKernel (epsilon^2+w^2) ‖p‖| ≤ _
    unfold slabPlanarTail slabRadialTail
    rw [Set.indicator_of_mem (Set.mem_Ioi.mpr hn), Real.rpow_neg (norm_nonneg p), Real.rpow_ofNat]
    convert hbound using 1
    all_goals try with_reducible_and_instances rfl
    ring
  have hm : (∫ p in (slabPlanarBox H)ᶜ, ‖f p‖) ≤
      ∫ p in (slabPlanarBox H)ᶜ, (3*S^2/2)*slabPlanarTail H p :=
    setIntegral_mono_on hi.norm.integrableOn ht.integrableOn
      (slabPlanarBox_measurable H).compl hpt
  have hall : (∫ p in (slabPlanarBox H)ᶜ, (3*S^2/2)*slabPlanarTail H p) ≤
      ∫ p, (3*S^2/2)*slabPlanarTail H p :=
    setIntegral_le_integral ht (Filter.Eventually.of_forall
      (fun p => mul_nonneg (by positivity) (slabPlanarTail_nonnegative H p)))
  calc
    _ = ‖∫ p in (slabPlanarBox H)ᶜ, f p‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∫ p in (slabPlanarBox H)ᶜ, ‖f p‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ p, (3*S^2/2)*slabPlanarTail H p := hm.trans hall
    _ = _ := by rw [integral_const_mul, slabPlanarTail_integral hH]; ring

/-- The finite horizontal square differs from the infinite-plane formula by
at most the inverse-cube tail. -/
theorem slabPlanarDifference_estimate {H S epsilon z w : ℝ} (hH : 0 < H)
    (hepsilon : epsilon ≠ 0) (hz : |z| ≤ S) (hw : |w| ≤ S) :
    |(∫ p in slabPlanarBox H,
       (coulombLineKernel (epsilon^2+(z-w)^2) ‖p‖-
        coulombLineKernel (epsilon^2+w^2) ‖p‖)) -
      2*Real.pi*(Real.sqrt (epsilon^2+w^2)-Real.sqrt (epsilon^2+(z-w)^2))| ≤
        3*Real.pi*S^2/H := by
  have hA : 0 < epsilon^2+(z-w)^2 := add_pos_of_pos_of_nonneg
    (sq_pos_of_ne_zero hepsilon) (sq_nonneg _)
  have hB : 0 < epsilon^2+w^2 := add_pos_of_pos_of_nonneg
    (sq_pos_of_ne_zero hepsilon) (sq_nonneg _)
  have hs := integral_add_compl (slabPlanarBox_measurable H)
    (slabPlanarDifference_integrable hA hB)
  rw [slabPlanarDifference_integral hA hB] at hs
  have he : (∫ p in slabPlanarBox H,
       (coulombLineKernel (epsilon^2+(z-w)^2) ‖p‖-
        coulombLineKernel (epsilon^2+w^2) ‖p‖)) -
      2*Real.pi*(Real.sqrt (epsilon^2+w^2)-Real.sqrt (epsilon^2+(z-w)^2)) =
      -(∫ p in (slabPlanarBox H)ᶜ,
       (coulombLineKernel (epsilon^2+(z-w)^2) ‖p‖-
        coulombLineKernel (epsilon^2+w^2) ‖p‖)) := by linarith
  rw [he, abs_neg]
  exact slabPlanarDifference_tail_bound hH hepsilon hz hw

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Nuclei_SlabProfile
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Quantitative removal of the vertical regularization. -/

noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace ContinuumCoulomb

theorem slab_sqrt_regularization (epsilon a : ℝ) :
    0 ≤ Real.sqrt (epsilon^2+a^2)-|a| ∧
      Real.sqrt (epsilon^2+a^2)-|a| ≤ |epsilon| := by
  have hp : 0 ≤ epsilon^2+a^2 := by positivity
  have hl : |a| ≤ Real.sqrt (epsilon^2+a^2) := by
    rw [← Real.sqrt_sq_eq_abs a]
    exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg epsilon])
  constructor
  · linarith
  · have hs := Real.sq_sqrt hp
    have he := sq_abs epsilon
    have ha := sq_abs a
    nlinarith [Real.sqrt_nonneg (epsilon^2+a^2), abs_nonneg epsilon,
      abs_nonneg a, mul_nonneg (abs_nonneg epsilon) (abs_nonneg a)]

theorem slabRegularizedProfile_error {S z : ℝ} (hS : 0 ≤ S) (hz : |z| ≤ S)
    (epsilon : ℝ) : |slabRegularizedProfile epsilon S z-z^2| ≤ 4*S*|epsilon| := by
  have hc : Continuous (fun w : ℝ => Real.sqrt (epsilon^2+(z-w)^2)-
      Real.sqrt (epsilon^2+w^2)) := by fun_prop
  have hd : Continuous (fun w : ℝ => |z-w|-|w|) := by fun_prop
  rw [slabRegularizedProfile, ← slab_absolute_difference_integral hS hz,
    ← intervalIntegral.integral_sub (hc.intervalIntegrable _ _) (hd.intervalIntegrable _ _)]
  have hbound (w : ℝ) :
      ‖(Real.sqrt (epsilon^2+(z-w)^2)-Real.sqrt (epsilon^2+w^2))-(|z-w|-|w|)‖ ≤
        2*|epsilon| := by
    obtain ⟨ha0,ha1⟩ := slab_sqrt_regularization epsilon (z-w)
    obtain ⟨hb0,hb1⟩ := slab_sqrt_regularization epsilon w
    rw [Real.norm_eq_abs, abs_le]
    constructor <;> linarith
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := -S) (b := S) (fun w _ => hbound w)
  rw [Real.norm_eq_abs, sub_neg_eq_add, abs_of_nonneg (by linarith : 0 ≤ S+S)] at h
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  ring

theorem slabRegularizedProfile_tendsto {S z : ℝ} (hS : 0 ≤ S) (hz : |z| ≤ S)
    {epsilon : ℕ → ℝ} (hepsilon : Tendsto epsilon atTop (𝓝 0)) :
    Tendsto (fun n => slabRegularizedProfile (epsilon n) S z) atTop (𝓝 (z^2)) := by
  apply Metric.tendsto_nhds.mpr
  intro delta hdelta
  have hlim : Tendsto (fun n => 4*S*|epsilon n|) atTop (𝓝 0) := by
    simpa using hepsilon.abs.const_mul (4*S)
  filter_upwards [((tendsto_order.1 hlim).2 delta hdelta)] with n hn
  rw [Real.dist_eq]
  exact (slabRegularizedProfile_error hS hz (epsilon n)).trans_lt hn

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Nuclei_SlabVerticalCoordinates
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Vertical-first coordinates for the actual three-dimensional slab. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb

theorem slabVerticalEquiv_symm_apply (p : ℝ × PlanarPosition) :
    slabVerticalEquiv.symm p = WithLp.toLp 2 ![p.2 0, p.2 1, p.1] := by
  ext i
  fin_cases i <;> rfl

theorem slabVerticalEquiv_apply (x : Position) :
    slabVerticalEquiv x = (x 2, WithLp.toLp 2 ![x 0, x 1]) := by
  apply Prod.ext
  · rfl
  · ext i
    fin_cases i <;> rfl

theorem slabVerticalEquiv_measurePreserving : MeasurePreserving slabVerticalEquiv :=
  ((MeasurePreserving.id volume).prod (PiLp.volume_preserving_toLp (Fin 2))).comp
    ((volume_preserving_piFinSuccAbove (fun _ : Fin 3 => ℝ) 2).comp
      (PiLp.volume_preserving_ofLp (Fin 3)))

theorem slabVerticalEquiv_preimage (H S : ℝ) :
    slabVerticalEquiv ⁻¹' (Set.Icc (-S) S ×ˢ slabPlanarBox H) = slabDomain H S := by
  ext x
  simp only [Set.mem_preimage, Set.mem_prod, Set.mem_Icc, slabVerticalEquiv_apply,
    slabPlanarBox, Set.mem_ofPred_eq, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one, slabDomain, abs_le]
  tauto

theorem slabVertical_setIntegral (H S : ℝ) (f : Position → ℝ) :
    (∫ x in slabDomain H S, f x) =
      ∫ p in Set.Icc (-S) S ×ˢ slabPlanarBox H, f (slabVerticalEquiv.symm p) := by
  have h := slabVerticalEquiv_measurePreserving.restrict_preimage
    (s := Set.Icc (-S) S ×ˢ slabPlanarBox H)
    (measurableSet_Icc.prod (slabPlanarBox_measurable H))
  rw [slabVerticalEquiv_preimage] at h
  simpa only [Function.comp_apply, MeasurableEquiv.symm_apply_apply] using
    h.integral_comp' (f ∘ slabVerticalEquiv.symm)

theorem regularizedSlab_vertical_kernel (epsilon z : ℝ) (p : ℝ × PlanarPosition) :
    NeutralAtom.regularizedKernel epsilon (slabAxisPoint z-slabVerticalEquiv.symm p) =
      coulombLineKernel (epsilon^2+(z-p.1)^2) ‖p.2‖ := by
  rw [regularizedKernel_eq_sqrt, slabVerticalEquiv_symm_apply]
  unfold coulombLineKernel
  congr 2
  rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
  simp only [slabAxisPoint, PiLp.sub_apply, Fin.sum_univ_succ,
    Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_fin_one,
    zero_sub, neg_sq]
  rw [Fin.succ_zero_eq_one]
  ring

theorem regularizedSlab_vertical_integrable {epsilon H S : ℝ} (hepsilon : epsilon ≠ 0)
    (hH : 0 ≤ H) (hS : 0 ≤ S) (z : ℝ) :
    IntegrableOn (fun p : ℝ × PlanarPosition =>
      coulombLineKernel (epsilon^2+(z-p.1)^2) ‖p.2‖)
      (Set.Icc (-S) S ×ˢ slabPlanarBox H) := by
  have h := slabVerticalEquiv_measurePreserving.restrict_preimage
    (s := Set.Icc (-S) S ×ˢ slabPlanarBox H)
    (measurableSet_Icc.prod (slabPlanarBox_measurable H))
  rw [slabVerticalEquiv_preimage] at h
  have hs := (MeasurePreserving.symm slabVerticalEquiv h).integrable_comp_emb
    (g := fun x : Position => NeutralAtom.regularizedKernel epsilon (slabAxisPoint z-x))
    slabVerticalEquiv.symm.measurableEmbedding
  exact (hs.mpr (regularizedSlab_integrableOn hepsilon hH hS (slabAxisPoint z))).congr
    (Filter.Eventually.of_forall (regularizedSlab_vertical_kernel epsilon z))

theorem regularizedSlab_vertical (epsilon rho : ℝ) {H S : ℝ} (hepsilon : epsilon ≠ 0)
    (hH : 0 ≤ H) (hS : 0 ≤ S) (z : ℝ) :
    regularizedSlabPotential epsilon rho H S (slabAxisPoint z) =
      -rho * ∫ w in Set.Icc (-S) S, ∫ p in slabPlanarBox H,
        coulombLineKernel (epsilon^2+(z-w)^2) ‖p‖ := by
  unfold regularizedSlabPotential
  rw [slabVertical_setIntegral]
  simp_rw [regularizedSlab_vertical_kernel]
  rw [Measure.volume_eq_prod, setIntegral_prod _
    (regularizedSlab_vertical_integrable hepsilon hH hS z)]

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Nuclei_SlabConfinement
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Quantitative confinement by the actual finite rectangular Coulomb slab. -/

noncomputable section
open MeasureTheory Filter
open scoped Topology BigOperators
namespace ContinuumCoulomb

private theorem slabPlanarBox_compact {H : ℝ} (hH : 0 ≤ H) :
    IsCompact (slabPlanarBox H) := by
  have h0 : IsClosed {p : PlanarPosition | |p 0| ≤ H} :=
    isClosed_le (by fun_prop) continuous_const
  have h1 : IsClosed {p : PlanarPosition | |p 1| ≤ H} :=
    isClosed_le (by fun_prop) continuous_const
  apply (isCompact_closedBall (0 : PlanarPosition) (2*(H+1))).of_isClosed_subset (h0.inter h1)
  intro p hp
  have hcoord (i : Fin 2) : |p i| ≤ H := by
    fin_cases i
    · exact hp.1
    · exact hp.2
  have hsq : ‖p‖^2 ≤ 2*H^2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    have h := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
      (sq_le_sq₀ (abs_nonneg (p i)) hH).mpr (hcoord i))
    simpa only [sq_abs, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, Nat.cast_ofNat] using h
  rw [Metric.mem_closedBall, dist_zero_right]
  nlinarith [norm_nonneg p]

private theorem slabPlanarSection_kernel_integrable {epsilon H : ℝ}
    (hepsilon : epsilon ≠ 0) (hH : 0 ≤ H) (z w : ℝ) :
    IntegrableOn (fun p : PlanarPosition => coulombLineKernel (epsilon^2+(z-w)^2) ‖p‖)
      (slabPlanarBox H) :=
  ((coulombLineKernel_continuous (add_pos_of_pos_of_nonneg
    (sq_pos_of_ne_zero hepsilon) (sq_nonneg _))).comp continuous_norm).continuousOn.integrableOn_compact
      (slabPlanarBox_compact hH)

private theorem slabPlanarSection_intervalIntegrable {epsilon H S : ℝ}
    (hepsilon : epsilon ≠ 0) (hH : 0 ≤ H) (hS : 0 ≤ S) (z : ℝ) :
    IntervalIntegrable (slabPlanarSection epsilon H z) volume (-S) S := by
  have hp : Integrable (fun p : ℝ × PlanarPosition =>
      coulombLineKernel (epsilon^2+(z-p.1)^2) ‖p.2‖)
      ((volume.restrict (Set.Icc (-S) S)).prod (volume.restrict (slabPlanarBox H))) := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
    exact regularizedSlab_vertical_integrable hepsilon hH hS z
  exact (intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith)).mpr hp.integral_prod_left

private theorem slabPlanarSection_sub {epsilon H : ℝ} (hepsilon : epsilon ≠ 0)
    (hH : 0 ≤ H) (z w : ℝ) :
    slabPlanarSection epsilon H z w-slabPlanarSection epsilon H 0 w =
      ∫ p in slabPlanarBox H,
        (coulombLineKernel (epsilon^2+(z-w)^2) ‖p‖-
          coulombLineKernel (epsilon^2+w^2) ‖p‖) := by
  unfold slabPlanarSection
  rw [← integral_sub (slabPlanarSection_kernel_integrable hepsilon hH z w)
    (slabPlanarSection_kernel_integrable hepsilon hH 0 w)]
  simp only [zero_sub, neg_sq]

private theorem regularizedSlab_vertical_interval (epsilon rho : ℝ) {H S : ℝ}
    (hepsilon : epsilon ≠ 0) (hH : 0 ≤ H) (hS : 0 ≤ S) (z : ℝ) :
    regularizedSlabPotential epsilon rho H S (slabAxisPoint z) =
      -rho * ∫ w in (-S)..S, slabPlanarSection epsilon H z w := by
  rw [regularizedSlab_vertical epsilon rho hepsilon hH hS z,
    intervalIntegral.integral_of_le (by linarith), ← integral_Icc_eq_integral_Ioc]
  rfl

private theorem slabPlaneError_bound {epsilon H S z w : ℝ} (hepsilon : epsilon ≠ 0)
    (hH : 0 < H) (hz : |z| ≤ S) (hw : |w| ≤ S) :
    |slabPlaneError epsilon H z w| ≤ 3*Real.pi*S^2/H := by
  unfold slabPlaneError
  rw [slabPlanarSection_sub hepsilon hH.le]
  have he := slabPlanarDifference_estimate hH hepsilon hz hw
  convert he using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  ring

private theorem regularizedSlab_error_identity {epsilon rho H S z : ℝ}
    (hepsilon : epsilon ≠ 0) (hH : 0 ≤ H) (hS : 0 ≤ S) :
    regularizedSlabPotential epsilon rho H S (slabAxisPoint z)-
      regularizedSlabPotential epsilon rho H S (slabAxisPoint 0)-
      2*Real.pi*rho*slabRegularizedProfile epsilon S z =
        -rho*∫ w in (-S)..S, slabPlaneError epsilon H z w := by
  let P := fun w : ℝ => Real.sqrt (epsilon^2+(z-w)^2)-Real.sqrt (epsilon^2+w^2)
  have hP : Continuous P := by dsimp [P]; fun_prop
  have hIz := slabPlanarSection_intervalIntegrable hepsilon hH hS z
  have hI0 := slabPlanarSection_intervalIntegrable hepsilon hH hS 0
  rw [regularizedSlab_vertical_interval epsilon rho hepsilon hH hS z,
    regularizedSlab_vertical_interval epsilon rho hepsilon hH hS 0]
  unfold slabPlaneError slabRegularizedProfile
  rw [intervalIntegral.integral_add (hIz.sub hI0)
    ((hP.intervalIntegrable _ _).const_mul _),
    intervalIntegral.integral_sub hIz hI0, intervalIntegral.integral_const_mul]
  ring

/-- The regularized finite slab differs from its one-dimensional profile
by at most the horizontal inverse-cube tail. -/
theorem regularizedSlab_confinement_error {epsilon rho H S z : ℝ}
    (hepsilon : epsilon ≠ 0) (hrho : 0 ≤ rho) (hH : 0 < H)
    (hS : 0 ≤ S) (hz : |z| ≤ S) :
    |regularizedSlabPotential epsilon rho H S (slabAxisPoint z)-
      regularizedSlabPotential epsilon rho H S (slabAxisPoint 0)-
      2*Real.pi*rho*slabRegularizedProfile epsilon S z| ≤ 6*Real.pi*rho*S^3/H := by
  have hbound (w : ℝ) (hw : w ∈ Set.uIoc (-S) S) :
      ‖slabPlaneError epsilon H z w‖ ≤ 3*Real.pi*S^2/H := by
    have hh : w ∈ Set.Ioc (-S) S := by
      simpa only [Set.uIoc_of_le (by linarith : -S ≤ S)] using hw
    rw [Real.norm_eq_abs]
    exact slabPlaneError_bound hepsilon hH hz (abs_le.mpr ⟨hh.1.le, hh.2⟩)
  have hEI := intervalIntegral.norm_integral_le_of_norm_le_const hbound
  rw [Real.norm_eq_abs, sub_neg_eq_add, abs_of_nonneg (by linarith : 0 ≤ S+S)] at hEI
  rw [regularizedSlab_error_identity hepsilon hH.le hS,
    abs_mul, abs_neg, abs_of_nonneg hrho]
  calc
    _ ≤ rho*((3*Real.pi*S^2/H)*(S+S)) := mul_le_mul_of_nonneg_left hEI hrho
    _ = _ := by ring

/-- The actual singular finite-slab potential has the quadratic profile,
with a uniform error controlled by its finite horizontal extent. -/
theorem slabPotential_axis_error {rho H S z : ℝ} (hrho : 0 ≤ rho)
    (hH : 0 < H) (hS : 0 ≤ S) (hz : |z| ≤ S) :
    |slabPotential rho H S (slabAxisPoint z)-slabPotential rho H S 0-
      2*Real.pi*rho*z^2| ≤ 6*Real.pi*rho*S^3/H := by
  let epsilon : ℕ → ℝ := fun n => ((n:ℝ)+1)⁻¹
  have hep (n : ℕ) : 0 < epsilon n := by dsimp [epsilon]; positivity
  have heps : Tendsto epsilon atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp
      (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
  have hzlim := regularizedSlabPotential_tendsto hep heps rho hH.le hS (slabAxisPoint z)
  have hzero : slabAxisPoint 0 = 0 := by ext i; fin_cases i <;> rfl
  have h0lim : Tendsto (fun n => regularizedSlabPotential (epsilon n) rho H S (slabAxisPoint 0))
      atTop (𝓝 (slabPotential rho H S 0)) := by
    simpa only [hzero] using
      regularizedSlabPotential_tendsto hep heps rho hH.le hS (slabAxisPoint 0)
  have hplim := (slabRegularizedProfile_tendsto hS hz heps).const_mul (2*Real.pi*rho)
  have hlim : Tendsto (fun n => |regularizedSlabPotential (epsilon n) rho H S (slabAxisPoint z)-
      regularizedSlabPotential (epsilon n) rho H S (slabAxisPoint 0)-
      2*Real.pi*rho*slabRegularizedProfile (epsilon n) S z|) atTop
      (𝓝 |slabPotential rho H S (slabAxisPoint z)-slabPotential rho H S 0-2*Real.pi*rho*z^2|) :=
    ((hzlim.sub h0lim).sub hplim).abs
  apply le_of_tendsto hlim
  exact Filter.Eventually.of_forall (fun n =>
    regularizedSlab_confinement_error (hep n).ne' hrho hH hS hz)

/-- Global capped-quadratic confinement in the physical vertical coordinate. -/
theorem slabPotential_confinement {rho H S : ℝ} (hrho : 0 ≤ rho)
    (hH : 0 < H) (hS : 0 ≤ S) (y : Position) :
    2*Real.pi*rho*min ((y 2)^2) (S^2)-6*Real.pi*rho*S^3/H ≤
      slabPotential rho H S y-slabPotential rho H S 0 := by
  let t : ℝ := min |y 2| S
  have ht0 : 0 ≤ t := le_min (abs_nonneg _) hS
  have htS : |t| ≤ S := by rw [abs_of_nonneg ht0]; exact min_le_right _ _
  have hty : |t| ≤ |y 2| := by rw [abs_of_nonneg ht0]; exact min_le_left _ _
  have ht2 : t^2 = min ((y 2)^2) (S^2) := by
    by_cases h : |y 2| ≤ S
    · have hs : (y 2)^2 ≤ S^2 := by
        simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hS).mpr h
      simp only [t, min_eq_left h, sq_abs, min_eq_left hs]
    · have hs : S^2 ≤ (y 2)^2 := by
        simpa only [sq_abs] using (sq_le_sq₀ hS (abs_nonneg _)).mpr (le_of_not_ge h)
      simp only [t, min_eq_right (le_of_not_ge h), min_eq_right hs]
  have haxis : slabPotential rho H S (slabAxisPoint t) ≤
      slabPotential rho H S (slabAxisPoint (y 2)) := by
    apply slabPotential_coordinate_monotone hrho hH.le hS _ _ 2
    · intro j
      fin_cases j <;> rfl
    · exact hty
  have h0 := slabPotential_coordinate_min hrho hH.le hS y 0
  have h1 := slabPotential_coordinate_min hrho hH.le hS (zeroPositionCoordinate 0 y) 1
  have he : zeroPositionCoordinate 1 (zeroPositionCoordinate 0 y) = slabAxisPoint (y 2) := by
    ext j
    fin_cases j <;> simp [zeroPositionCoordinate, slabAxisPoint]
  rw [he] at h1
  have hmono := haxis.trans (h1.trans h0)
  have herr := (abs_le.mp (slabPotential_axis_error hrho hH hS htS)).1
  rw [ht2] at herr
  linarith

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_PlanarHeatLimit
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.planarHeatResolventPrimitive_zero _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The Gaussian change of scale and the actual time-zero limit of the heat
average. The bound by the normalized time-one Gaussian permits dominated
convergence even though the Gaussian has noncompact support. -/

noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace ContinuumCoulomb

theorem planarHeatKernel_sqrt_scale {t : ℝ} (ht : 0 < t) (r : PlanarPosition) :
    planarHeatKernel t (Real.sqrt t • r) = t⁻¹ * planarHeatKernel 1 r := by
  have hs : Real.sqrt t ^ 2 = t := Real.sq_sqrt ht.le
  rw [planarHeatKernel, planarHeatKernel, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), mul_pow, hs]
  have he : -(t * ‖r‖ ^ 2) / (4 * t) = -‖r‖ ^ 2 / (4 * 1) := by
    field_simp
  rw [he]
  ring

theorem planarHeatAverage_scaled {t : ℝ} (ht : 0 < t) (r : PlanarPosition) :
    planarHeatAverage t r = ∫ b, planarHeatKernel 1 b * planarForcing (r - Real.sqrt t • b) := by
  have hi := Measure.integral_comp_smul_of_nonneg (volume : Measure PlanarPosition)
    (fun b => planarHeatKernel t b * planarForcing (r - b)) (Real.sqrt t)
    (hR := Real.sqrt_nonneg t)
  simp only [finrank_euclideanSpace_fin, Real.sq_sqrt ht.le, smul_eq_mul,
    planarHeatKernel_sqrt_scale ht] at hi
  simp_rw [mul_assoc] at hi
  rw [integral_const_mul] at hi
  exact (mul_left_cancel₀ (inv_ne_zero ht.ne') hi).symm

theorem planarScaledHeatIntegrand_measurable (t : ℝ) (r : PlanarPosition) :
    AEStronglyMeasurable (fun b => planarHeatKernel 1 b *
      planarForcing (r - Real.sqrt t • b)) := by
  have hc : Continuous (fun b : PlanarPosition => r - Real.sqrt t • b) := by fun_prop
  exact ((planarHeatKernel_continuous 1).mul
    (planarForcing_C7.continuous.comp hc)).aestronglyMeasurable

theorem planarScaledHeatIntegrand_bound (t : ℝ) (r b : PlanarPosition) :
    ‖planarHeatKernel 1 b * planarForcing (r - Real.sqrt t • b)‖ ≤ planarHeatKernel 1 b := by
  have hk : 0 < planarHeatKernel 1 b := planarHeatKernel_positive (by norm_num) b
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hk.le (planarForcing_nonnegative _))]
  exact mul_le_of_le_one_right hk.le (planarForcing_le_one _)

theorem planarScaledHeatIntegrand_tendsto (r b : PlanarPosition) :
    Tendsto (fun t : ℝ => planarHeatKernel 1 b * planarForcing (r - Real.sqrt t • b))
      (𝓝[>] (0 : ℝ)) (𝓝 (planarHeatKernel 1 b * planarForcing r)) := by
  have hs : Tendsto (fun t : ℝ => Real.sqrt t • b) (𝓝[>] 0) (𝓝 (0 : PlanarPosition)) := by
    have hs0 : Tendsto Real.sqrt (𝓝 (0 : ℝ)) (𝓝 (Real.sqrt 0)) :=
      Real.continuous_sqrt.continuousAt.tendsto
    simpa only [Real.sqrt_zero, zero_smul] using
      (hs0.mono_left nhdsWithin_le_nhds).smul_const b
  have hr : Tendsto (fun t : ℝ => r - Real.sqrt t • b) (𝓝[>] 0) (𝓝 r) := by
    simpa only [sub_zero] using tendsto_const_nhds.sub hs
  exact tendsto_const_nhds.mul (planarForcing_C7.continuous.continuousAt.tendsto.comp hr)

theorem planarHeatAverage_tendsto_zero (r : PlanarPosition) :
    Tendsto (fun t => planarHeatAverage t r) (𝓝[>] (0 : ℝ)) (𝓝 (planarForcing r)) := by
  have hconv : Tendsto
      (fun t : ℝ => ∫ b, planarHeatKernel 1 b * planarForcing (r - Real.sqrt t • b))
      (𝓝[>] (0 : ℝ)) (𝓝 (∫ b, planarHeatKernel 1 b * planarForcing r)) := by
    apply tendsto_integral_filter_of_dominated_convergence
      (F := fun t b => planarHeatKernel 1 b * planarForcing (r - Real.sqrt t • b))
      (f := fun b => planarHeatKernel 1 b * planarForcing r)
      (bound := planarHeatKernel 1)
    · exact Eventually.of_forall (fun t => planarScaledHeatIntegrand_measurable t r)
    · exact Eventually.of_forall (fun t => Eventually.of_forall (fun b =>
        planarScaledHeatIntegrand_bound t r b))
    · exact planarHeatKernel_integrable (by norm_num)
    · exact Eventually.of_forall (planarScaledHeatIntegrand_tendsto r)
  have hv : (∫ b, planarHeatKernel 1 b * planarForcing r) = planarForcing r := by
    rw [integral_mul_const, planarHeatKernel_integral (by norm_num), one_mul]
  rw [hv] at hconv
  apply hconv.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact (planarHeatAverage_scaled ht r).symm

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_PlanarHeatDifferential
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.planarHeatResolventPrimitive_zero _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Pointwise differential identities for the actual two-dimensional Gaussian
kernel. Its time derivative is its coordinate Laplacian. -/

noncomputable section
open MeasureTheory
open scoped RealInnerProductSpace BigOperators
namespace ContinuumCoulomb

theorem planarHeatKernel_C2 (t : ℝ) : ContDiff ℝ 2 (planarHeatKernel t) := by
  unfold planarHeatKernel
  exact contDiff_const.mul (((contDiff_norm_sq ℝ).neg.div_const (4 * t)).exp)

theorem planarHeatKernel_hasDerivAt {t : ℝ} (ht : 0 < t) (r : PlanarPosition) :
    HasDerivAt (fun s => planarHeatKernel s r) (planarHeatTimeDerivative t r) t := by
  have hi := hasDerivAt_inv ht.ne'
  have h := (hi.const_mul ((4 * Real.pi)⁻¹)).mul
    ((hi.const_mul (-‖r‖ ^ 2 / 4)).exp)
  refine (h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)).congr_deriv ?_
  · beta_reduce
    change planarHeatKernel s r = (4 * Real.pi)⁻¹ * s⁻¹ * Real.exp (-‖r‖ ^ 2 / 4 * s⁻¹)
    unfold planarHeatKernel
    congr 1 <;> ring_nf
  · dsimp [planarHeatTimeDerivative, planarHeatKernel]
    have he : -‖r‖ ^ 2 / (4 * t) = -‖r‖ ^ 2 / 4 * t⁻¹ := by ring
    rw [he]
    field_simp
    ring

theorem planarHeatKernel_partial (t : ℝ) (e r : PlanarPosition) :
    planarPartial (planarHeatKernel t) e r =
      (-inner ℝ e r / (2 * t)) * planarHeatKernel t r := by
  have hd := ((((hasStrictFDerivAt_norm_sq r).hasFDerivAt.neg).mul_const (4 * t)⁻¹).exp).const_mul
    ((4 * Real.pi * t)⁻¹)
  change fderiv ℝ (planarHeatKernel t) r e = _
  rw [show fderiv ℝ (planarHeatKernel t) r = _ from hd.fderiv]
  simp only [smul_apply, smul_eq_mul, neg_apply, Pi.neg_apply,
    innerSL_apply_apply, planarHeatKernel]
  rw [real_inner_comm r e]
  ring_nf

theorem planarHeatKernel_partial_partial (t : ℝ) (e r : PlanarPosition) :
    planarPartial (planarPartial (planarHeatKernel t) e) e r =
      ((inner ℝ e r) ^ 2 / (4 * t ^ 2) - ‖e‖ ^ 2 / (2 * t)) * planarHeatKernel t r := by
  have hlin : ContDiff ℝ 1 (fun s : PlanarPosition => -inner ℝ e s / (2 * t)) :=
    ((innerSL ℝ e).contDiff.neg).div_const _
  have heq : planarPartial (planarHeatKernel t) e =
      fun s => (-inner ℝ e s / (2 * t)) * planarHeatKernel t s :=
    funext (planarHeatKernel_partial t e)
  rw [heq, planarPartial_mul _ _ hlin ((planarHeatKernel_C2 t).of_le (by norm_num)),
    planarHeatKernel_partial]
  have hpart : planarPartial (fun s : PlanarPosition => -inner ℝ e s / (2 * t)) e r =
      -‖e‖ ^ 2 / (2 * t) := by
    have hd := ((innerSL ℝ e).hasFDerivAt (x := r)).neg.mul_const (2 * t)⁻¹
    have hd' : HasFDerivAt (fun s : PlanarPosition => -inner ℝ e s / (2 * t))
        ((2 * t)⁻¹ • -(innerSL ℝ e)) r := by
      simpa only [Pi.neg_apply, innerSL_apply_apply, div_eq_mul_inv] using hd
    change fderiv ℝ (fun s : PlanarPosition => -inner ℝ e s / (2 * t)) r e = _
    rw [hd'.fderiv]
    simp only [smul_apply, smul_eq_mul, neg_apply,
      innerSL_apply_apply, real_inner_self_eq_norm_sq]
    ring
  rw [hpart]
  ring

theorem planarHeatKernel_laplacian (t : ℝ) (r : PlanarPosition) :
    planarLaplacian (planarHeatKernel t) r = planarHeatTimeDerivative t r := by
  have hn : ‖r‖ ^ 2 = ∑ a : Fin 2, (r a) ^ 2 := by
    simpa only [Real.norm_eq_abs, sq_abs] using EuclideanSpace.norm_sq_eq r
  have ha (a : Fin 2) : inner ℝ (planarAxis a) r = r a := by
    simp [planarAxis, EuclideanSpace.inner_single_left]
  have he (a : Fin 2) : ‖planarAxis a‖ ^ 2 = 1 := by simp [planarAxis]
  simp only [planarLaplacian, planarHeatKernel_partial_partial, ha, he,
    planarHeatTimeDerivative, hn, Fin.sum_univ_two]
  ring

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_PlanarHeatEvolution
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Differentiation in time of the actual heat average. The compact forcing
allows a fixed compact dominating set on every positive time neighborhood. -/

noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace ContinuumCoulomb

theorem planarHeatAverage_flip (t : ℝ) (r : PlanarPosition) :
    planarHeatAverage t r = ∫ b, planarHeatKernel t (r - b) * planarForcing b := by
  unfold planarHeatAverage
  rw [← integral_sub_left_eq_self _ volume r]
  simp only [sub_sub_self]

theorem planarHeatTimeDerivative_forcing_continuous (t : ℝ) (r : PlanarPosition) :
    Continuous (fun b => planarHeatTimeDerivative t (r - b) * planarForcing b) := by
  have hg : Continuous (fun b : PlanarPosition => planarHeatTimeDerivative t (r - b)) := by
    unfold planarHeatTimeDerivative planarHeatKernel
    fun_prop
  exact hg.mul planarForcing_C7.continuous

theorem planarHeatTimeDerivative_forcing_joint_continuousAt (r : PlanarPosition)
    {p : ℝ × PlanarPosition} (hp : 0 < p.1) :
    ContinuousAt (fun q : ℝ × PlanarPosition =>
      planarHeatTimeDerivative q.1 (r - q.2) * planarForcing q.2) p := by
  have h4 : 4 * p.1 ≠ 0 := by positivity
  have h42 : 4 * p.1 ^ 2 ≠ 0 := by positivity
  have hpi : 4 * Real.pi * p.1 ≠ 0 := by positivity
  have hne : p.1 ≠ 0 := hp.ne'
  have hcomp : ContinuousAt (fun q : ℝ × PlanarPosition => planarHeatTimeDerivative q.1 (r - q.2)) p := by
    unfold planarHeatTimeDerivative planarHeatKernel
    fun_prop
  have hf : Continuous (fun q : ℝ × PlanarPosition => planarForcing q.2) :=
    planarForcing_C7.continuous.comp continuous_snd
  exact hcomp.mul hf.continuousAt

theorem planarHeatTimeDerivative_local_bound {t : ℝ} (ht : 0 < t) (r : PlanarPosition) :
    ∃ bound : PlanarPosition → ℝ, Integrable bound ∧
      ∀ b s, s ∈ Set.Ioo (t / 2) (3 * t / 2) →
        ‖planarHeatTimeDerivative s (r - b) * planarForcing b‖ ≤ bound b := by
  let S : Set (ℝ × PlanarPosition) := Set.Icc (t / 2) (3 * t / 2) ×ˢ tsupport planarForcing
  let F : ℝ × PlanarPosition → ℝ := fun p =>
    planarHeatTimeDerivative p.1 (r - p.2) * planarForcing p.2
  have hS : IsCompact S := isCompact_Icc.prod planarForcing_hasCompactSupport
  have hF : ContinuousOn F S := by
    intro p hp
    have hpos : 0 < p.1 := lt_of_lt_of_le (by linarith) hp.1.1
    exact (planarHeatTimeDerivative_forcing_joint_continuousAt r hpos).continuousWithinAt
  obtain ⟨C, hC⟩ := hS.bddAbove_image hF.norm
  let bound : PlanarPosition → ℝ := (tsupport planarForcing).indicator (fun _ => max 0 C)
  refine ⟨bound, ?_, ?_⟩
  · exact (integrable_indicator_iff (isClosed_tsupport _).measurableSet).mpr
      (integrableOn_const planarForcing_hasCompactSupport.measure_ne_top)
  · intro b s hs
    by_cases hb : b ∈ tsupport planarForcing
    · have hf : ‖F (s, b)‖ ≤ C := hC ⟨(s, b), ⟨⟨hs.1.le, hs.2.le⟩, hb⟩, rfl⟩
      simpa only [bound, Set.indicator_of_mem hb] using hf.trans (le_max_right 0 C)
    · simp only [bound, Set.indicator_of_notMem hb, image_eq_zero_of_notMem_tsupport hb,
        mul_zero, norm_zero, le_refl]

theorem planarHeatAverage_hasDerivAt {t : ℝ} (ht : 0 < t) (r : PlanarPosition) :
    HasDerivAt (fun s => planarHeatAverage s r)
      (∫ b, planarHeatTimeDerivative t (r - b) * planarForcing b) t := by
  obtain ⟨bound, hbi, hb⟩ := planarHeatTimeDerivative_local_bound ht r
  have hn : Set.Ioo (t / 2) (3 * t / 2) ∈ 𝓝 t := Ioo_mem_nhds (by linarith) (by linarith)
  have hi : Integrable (fun b => planarHeatKernel t (r - b) * planarForcing b) :=
    ((planarHeatKernel_continuous t).comp (continuous_const.sub continuous_id)
      |>.mul planarForcing_C7.continuous).integrable_of_hasCompactSupport
      planarForcing_hasCompactSupport.mul_left
  have hmeas : ∀ᶠ s in 𝓝 t,
      AEStronglyMeasurable (fun b => planarHeatKernel s (r - b) * planarForcing b) :=
    Eventually.of_forall (fun s => ((planarHeatKernel_continuous s).comp
      (continuous_const.sub continuous_id) |>.mul planarForcing_C7.continuous).aestronglyMeasurable)
  have hd := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun s b => planarHeatKernel s (r - b) * planarForcing b)
    (F' := fun s b => planarHeatTimeDerivative s (r - b) * planarForcing b)
    hn hmeas hi (planarHeatTimeDerivative_forcing_continuous t r).aestronglyMeasurable
    (Eventually.of_forall hb) hbi
    (Eventually.of_forall (fun b s hs => (planarHeatKernel_hasDerivAt
      (by linarith [hs.1] : 0 < s) (r - b)).mul_const (planarForcing b)))
  simpa only [← planarHeatAverage_flip] using hd.2

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_PlanarLaplaceIBP
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.planarHeatResolventPrimitive_zero _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Two integrations by parts transfer the planar Laplacian from the
Gaussian kernel to the compact forcing. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb

theorem planarPartial_reflect {f : PlanarPosition → ℝ} (hf : ContDiff ℝ 1 f)
    (r e x : PlanarPosition) :
    planarPartial (fun y => f (r - y)) e x = -planarPartial f e (r - x) := by
  have hd := ((hf.differentiable (by norm_num) (r - x)).hasFDerivAt).comp x
    ((hasFDerivAt_const r x).sub (hasFDerivAt_id x))
  change fderiv ℝ (fun y => f (r - y)) x e = -(fderiv ℝ f (r - x) e)
  rw [show fderiv ℝ (fun y => f (r - y)) x = _ from hd.fderiv]
  simp only [ContinuousLinearMap.comp_apply, zero_sub, neg_apply,
    ContinuousLinearMap.id_apply, map_neg]

theorem planarPartial_neg {f : PlanarPosition → ℝ} (hf : ContDiff ℝ 1 f)
    (e x : PlanarPosition) :
    planarPartial (fun y => -f y) e x = -planarPartial f e x := by
  have hd := (hf.differentiable (by norm_num) x).hasFDerivAt.neg
  change fderiv ℝ (fun y => -f y) x e = -(fderiv ℝ f x e)
  rw [show fderiv ℝ (fun y => -f y) x = _ from hd.fderiv]
  simp only [neg_apply]

theorem planarLaplacian_reflect {f : PlanarPosition → ℝ} (hf : ContDiff ℝ 2 f)
    (r x : PlanarPosition) :
    planarLaplacian (fun y => f (r - y)) x = planarLaplacian f (r - x) := by
  apply Finset.sum_congr rfl
  intro a _
  have hp := planarPartial_C1 hf (planarAxis a)
  have hpr : ContDiff ℝ 1 (fun y => planarPartial f (planarAxis a) (r - y)) :=
    hp.comp (contDiff_const.sub contDiff_id)
  rw [show planarPartial (fun y => f (r - y)) (planarAxis a) =
      fun y => -planarPartial f (planarAxis a) (r - y) from
    funext (planarPartial_reflect (hf.of_le (by norm_num)) r (planarAxis a)),
    planarPartial_neg hpr, planarPartial_reflect hp, neg_neg]

theorem planar_integral_mul_laplacian_C2 (f phi : PlanarPosition → ℝ)
    (hf : ContDiff ℝ 2 f) (hphi : ContDiff ℝ 2 phi) (hc : HasCompactSupport phi) :
    (∫ x, f x * planarLaplacian phi x) = ∫ x, planarLaplacian f x * phi x := by
  have hp (g : PlanarPosition → ℝ) (hg : ContDiff ℝ 2 g) (v : PlanarPosition) :
      ContDiff ℝ 1 (planarPartial g v) :=
    (hg.fderiv_right (show (1 : WithTop ℕ∞) + 1 ≤ 2 by norm_num)).clm_apply contDiff_const
  have hpp (g : PlanarPosition → ℝ) (hg : ContDiff ℝ 2 g) (v : PlanarPosition) :
      Continuous (planarPartial (planarPartial g v) v) :=
    (((hp g hg v).fderiv_right (show (0 : WithTop ℕ∞) + 1 ≤ 1 by norm_num)).clm_apply
      contDiff_const).continuous
  have hpc (v : PlanarPosition) : HasCompactSupport (planarPartial phi v) :=
    hc.fderiv_apply ℝ v
  have hppc (v : PlanarPosition) : HasCompactSupport (planarPartial (planarPartial phi v) v) :=
    (hpc v).fderiv_apply ℝ v
  have hleft (v : PlanarPosition) : Integrable (fun x => f x * planarPartial (planarPartial phi v) v x) :=
    (hf.continuous.mul (hpp phi hphi v)).integrable_of_hasCompactSupport (hppc v).mul_left
  have hright (v : PlanarPosition) : Integrable (fun x => planarPartial (planarPartial f v) v x * phi x) :=
    ((hpp f hf v).mul hphi.continuous).integrable_of_hasCompactSupport hc.mul_left
  have hcross (v : PlanarPosition) : Integrable (fun x => planarPartial f v x * planarPartial phi v x) :=
    ((hp f hf v).continuous.mul (hp phi hphi v).continuous).integrable_of_hasCompactSupport
      (hpc v).mul_left
  have hfg (v : PlanarPosition) : Integrable (fun x => f x * planarPartial phi v x) :=
    (hf.continuous.mul (hp phi hphi v).continuous).integrable_of_hasCompactSupport
      (hpc v).mul_left
  have hfpg (v : PlanarPosition) : Integrable (fun x => planarPartial f v x * phi x) :=
    ((hp f hf v).continuous.mul hphi.continuous).integrable_of_hasCompactSupport hc.mul_left
  have hby (v : PlanarPosition) :
      (∫ x, f x * planarPartial (planarPartial phi v) v x) =
        ∫ x, planarPartial (planarPartial f v) v x * phi x := by
    calc
      _ = -(∫ x, planarPartial f v x * planarPartial phi v x) :=
        integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
          (hcross v) (hleft v) (hfg v)
          (fun x _ => hf.differentiable (by norm_num) x)
          (fun x _ => (hp phi hphi v).differentiable (by norm_num) x)
      _ = _ := by
        have h : (∫ x, planarPartial f v x * planarPartial phi v x) =
            -(∫ x, planarPartial (planarPartial f v) v x * phi x) :=
          integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
            (hright v) (hcross v) (hfpg v)
            (fun x _ => (hp f hf v).differentiable (by norm_num) x)
            (fun x _ => hphi.differentiable (by norm_num) x)
        rw [h, neg_neg]
  simp_rw [planarLaplacian, Finset.mul_sum]
  rw [integral_finsetSum _ (fun a _ => hleft (planarAxis a))]
  simp_rw [hby]
  rw [← integral_finsetSum _ (fun a _ => hright (planarAxis a))]
  simp_rw [Finset.sum_mul]

theorem planarLaplacian_continuous {f : PlanarPosition → ℝ} (hf : ContDiff ℝ 2 f) :
    Continuous (planarLaplacian f) :=
  continuous_finsetSum _ (fun a _ =>
    planarPartial_continuous (planarPartial_C1 hf (planarAxis a)) (planarAxis a))

theorem planarLaplacian_hasCompactSupport {f : PlanarPosition → ℝ} (hc : HasCompactSupport f) :
    HasCompactSupport (planarLaplacian f) := by
  change HasCompactSupport (fun x => ∑ a : Fin 2,
    fderiv ℝ (fun y => fderiv ℝ f y (planarAxis a)) x (planarAxis a))
  have h := HasCompactSupport.finset_sum (s := Finset.univ)
    (fun a _ => (hc.fderiv_apply ℝ (planarAxis a)).fderiv_apply ℝ (planarAxis a))
  simpa only [Finset.sum_fn] using h

theorem planarHeatAverage_hasDerivAt_laplacian {t : ℝ} (ht : 0 < t) (r : PlanarPosition) :
    HasDerivAt (fun s => planarHeatAverage s r)
      (∫ b, planarHeatKernel t b * planarLaplacian planarForcing (r - b)) t := by
  have hf2 : ContDiff ℝ 2 planarForcing := planarForcing_C7.of_le (by norm_num)
  have hr : ContDiff ℝ 2 (fun b : PlanarPosition => planarForcing (r - b)) :=
    hf2.comp (contDiff_const.sub contDiff_id)
  have hrc : HasCompactSupport (fun b : PlanarPosition => planarForcing (r - b)) :=
    planarForcing_hasCompactSupport.comp_homeomorph (Homeomorph.subLeft r)
  have heq : (∫ b, planarHeatTimeDerivative t (r - b) * planarForcing b) =
      ∫ b, planarHeatKernel t b * planarLaplacian planarForcing (r - b) := by
    calc
      _ = ∫ b, planarHeatTimeDerivative t b * planarForcing (r - b) := by
        rw [← integral_sub_left_eq_self _ volume r]
        simp only [sub_sub_self]
      _ = ∫ b, planarLaplacian (planarHeatKernel t) b * planarForcing (r - b) := by
        simp only [planarHeatKernel_laplacian]
      _ = ∫ b, planarHeatKernel t b * planarLaplacian (fun y => planarForcing (r - y)) b :=
        (planar_integral_mul_laplacian_C2 _ _ (planarHeatKernel_C2 t) hr hrc).symm
      _ = _ := by simp only [planarLaplacian_reflect hf2]
  rw [← heq]
  exact planarHeatAverage_hasDerivAt ht r

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_PlanarModeProperties
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.planarHeatResolventPrimitive_zero _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Positivity, finite L² normalization and compact support of the actual
manufactured planar potential. The differential eigen-equation and gap are
not assumed by these declarations. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

theorem planarResolventMode_memLp : MemLp planarResolventMode 2 :=
  (memLp_two_iff_integrable_sq planarResolventMode_C7.continuous.aestronglyMeasurable).mpr
    planarResolventMode_square_integrable

theorem normalizedPlanarMode_normalized : (∫ r, normalizedPlanarMode r ^ 2) = 1 := by
  simp_rw [normalizedPlanarMode, div_pow]
  rw [integral_div, Real.sq_sqrt planarResolventMode_square_integral_positive.le,
    div_self planarResolventMode_square_integral_positive.ne']

theorem manufacturedPlanarWell_nonpositive (r : PlanarPosition) : manufacturedPlanarWell r ≤ 0 :=
  div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (planarForcing_nonnegative r))
    (mul_nonneg (by norm_num) (planarResolventMode_positive r).le)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_PlanarModeDerivatives
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.planarHeatResolventPrimitive_zero _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual first and second directional derivatives of the resolvent mode.
Differentiation is transferred to the compact forcing, which also gives
finite L¹ and L² derivatives without differentiating the singular kernel. -/

noncomputable section
open MeasureTheory
open scoped Convolution
namespace ContinuumCoulomb

theorem planarResolventMode_partial_partial (e v r : PlanarPosition) :
    planarPartial (planarPartial planarResolventMode e) v r =
      planarResolventOf (planarPartial (planarPartial planarForcing e) v) r := by
  rw [show planarPartial planarResolventMode e =
    planarResolventOf (planarPartial planarForcing e) from funext (planarResolventMode_partial e)]
  exact planarResolventOf_partial
    (planarPartial_C1 (planarForcing_C7.of_le (by norm_num)) e)
    (planarForcing_hasCompactSupport.fderiv_apply ℝ e) v r

theorem planarResolventMode_partial_partial_square_integrable (e v : PlanarPosition) :
    Integrable (fun r => planarPartial (planarPartial planarResolventMode e) v r ^ 2) := by
  simp_rw [planarResolventMode_partial_partial]
  exact planarResolventOf_square_integrable
    (planarPartial_continuous (planarPartial_C1 (planarForcing_C7.of_le (by norm_num)) e) v)
    ((planarForcing_hasCompactSupport.fderiv_apply ℝ e).fderiv_apply ℝ v)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_PlanarResolventEquation
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The differential eigen-equation of the constructed resolvent mode is
obtained from its heat representation and the fundamental theorem of calculus,
not supplied as an assumption. -/

noncomputable section
open MeasureTheory Filter
open scoped Topology BigOperators
namespace ContinuumCoulomb

theorem planarResolvent_joint_integrable {g : PlanarPosition → ℝ}
    (hg : Continuous g) (hc : HasCompactSupport g) (r : PlanarPosition) :
    Integrable (fun p : ℝ × PlanarPosition => planarResolventIntegrand p * g (r - p.2))
      ((volume.restrict (Set.Ioi (0 : ℝ))).prod (volume : Measure PlanarPosition)) := by
  obtain ⟨B, hB⟩ := hg.bounded_above_of_compact_support hc
  apply planarResolventIntegrand_integrable.mul_bdd
    ((hg.comp (continuous_const.sub continuous_snd)).aestronglyMeasurable)
  exact Eventually.of_forall (fun p => by
    change ‖g (r - p.2)‖ ≤ B
    exact hB _)

theorem planarResolventOf_heat_representation {g : PlanarPosition → ℝ}
    (hg : Continuous g) (hc : HasCompactSupport g) (r : PlanarPosition) :
    planarResolventOf g r = ∫ t in Set.Ioi (0 : ℝ),
      Real.exp (-t) * ∫ b, planarHeatKernel t b * g (r - b) := by
  unfold planarResolventOf planarResolventKernel
  simp_rw [← integral_mul_const]
  rw [← integral_integral_swap (planarResolvent_joint_integrable hg hc r)]
  simp_rw [planarResolventIntegrand, mul_assoc, integral_const_mul]

theorem planarResolventOf_heat_integrable {g : PlanarPosition → ℝ}
    (hg : Continuous g) (hc : HasCompactSupport g) (r : PlanarPosition) :
    IntegrableOn (fun t => Real.exp (-t) * ∫ b, planarHeatKernel t b * g (r - b))
      (Set.Ioi (0 : ℝ)) := by
  have h := (planarResolvent_joint_integrable hg hc r).integral_prod_left
  change Integrable _ _
  simpa only [planarResolventIntegrand, mul_assoc, integral_const_mul] using h

theorem planarResolventMode_laplacian_integral (r : PlanarPosition) :
    planarLaplacian planarResolventMode r = planarResolventOf (planarLaplacian planarForcing) r := by
  have hi (a : Fin 2) : Integrable (fun b => planarResolventKernel b *
      planarPartial (planarPartial planarForcing (planarAxis a)) (planarAxis a) (r - b)) :=
    ((planarForcing_hasCompactSupport.fderiv_apply ℝ (planarAxis a)).fderiv_apply ℝ
      (planarAxis a)).convolutionExists_right (ContinuousLinearMap.mul ℝ ℝ)
      planarResolventKernel_integrable.locallyIntegrable
      (planarPartial_continuous (planarPartial_C1 (planarForcing_C7.of_le (by norm_num)) _) _) r
  unfold planarLaplacian
  simp_rw [planarResolventMode_partial_partial]
  change (∑ a : Fin 2, ∫ b, planarResolventKernel b *
      planarPartial (planarPartial planarForcing (planarAxis a)) (planarAxis a) (r - b)) =
    ∫ b, planarResolventKernel b * ∑ a : Fin 2,
      planarPartial (planarPartial planarForcing (planarAxis a)) (planarAxis a) (r - b)
  rw [← integral_finsetSum _ (fun a _ => hi a)]
  simp only [Finset.mul_sum]

theorem planarHeatResolventPrimitive_hasDerivAt (r : PlanarPosition) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (planarHeatResolventPrimitive r) (planarHeatResolventDerivative r t) t := by
  have he : HasDerivAt (fun s : ℝ => Real.exp (-s)) (-Real.exp (-t)) t := by
    simpa only [Pi.neg_apply, id_eq, mul_neg, mul_one] using (hasDerivAt_id t).neg.exp
  have hd := he.mul (planarHeatAverage_hasDerivAt_laplacian ht r)
  have hd' : HasDerivAt (fun s => Real.exp (-s) * planarHeatAverage s r)
      (planarHeatResolventDerivative r t) t := by
    convert hd using 1
    all_goals try with_reducible_and_instances rfl
    dsimp [planarHeatResolventDerivative]
    ring
  apply hd'.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds ht] with s hs
  simp only [planarHeatResolventPrimitive, ite_eq_right (show s ≠ 0 from (show 0 < s from hs).ne')]

theorem planarHeatResolventPrimitive_continuousWithinAt (r : PlanarPosition) :
    ContinuousWithinAt (planarHeatResolventPrimitive r) (Set.Ici (0 : ℝ)) 0 := by
  have he : Tendsto (fun t : ℝ => Real.exp (-t)) (𝓝[>] 0) (𝓝 1) := by
    have he0 : Tendsto (fun t : ℝ => Real.exp (-t)) (𝓝 (0 : ℝ)) (𝓝 (Real.exp (-0))) :=
      (Real.continuous_exp.comp continuous_neg).continuousAt.tendsto
    simpa only [neg_zero, Real.exp_zero] using
      he0.mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
  have hlim := he.mul (planarHeatAverage_tendsto_zero r)
  apply continuousWithinAt_Ioi_iff_Ici.mp
  change Tendsto _ _ (𝓝 (planarHeatResolventPrimitive r 0))
  rw [planarHeatResolventPrimitive_zero]
  have hlim' : Tendsto (fun t => Real.exp (-t) * planarHeatAverage t r)
      (𝓝[>] (0 : ℝ)) (𝓝 (planarForcing r)) := by simpa only [one_mul] using hlim
  apply hlim'.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  simp only [planarHeatResolventPrimitive, ite_eq_right (show t ≠ 0 from (show 0 < t from ht).ne')]

theorem planarHeatResolventDerivative_integrable (r : PlanarPosition) :
    IntegrableOn (planarHeatResolventDerivative r) (Set.Ioi (0 : ℝ)) :=
  (planarResolventOf_heat_integrable
    (planarLaplacian_continuous (planarForcing_C7.of_le (by norm_num)))
    (planarLaplacian_hasCompactSupport planarForcing_hasCompactSupport) r).sub
    (planarResolventMode_heat_integrable r)

theorem planarHeatResolventPrimitive_integrable (r : PlanarPosition) :
    IntegrableOn (planarHeatResolventPrimitive r) (Set.Ioi (0 : ℝ)) := by
  apply (planarResolventMode_heat_integrable r).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  simp only [planarHeatResolventPrimitive, ite_eq_right (show t ≠ 0 from (show 0 < t from ht).ne')]

theorem planarResolventMode_equation (r : PlanarPosition) :
    planarLaplacian planarResolventMode r = planarResolventMode r - planarForcing r := by
  have hd := fun t (ht : t ∈ Set.Ioi (0 : ℝ)) => planarHeatResolventPrimitive_hasDerivAt r ht
  have hzero := tendsto_zero_of_hasDerivAt_of_integrableOn_Ioi hd
    (planarHeatResolventDerivative_integrable r) (planarHeatResolventPrimitive_integrable r)
  have hFTC := integral_Ioi_of_hasDerivAt_of_tendsto
    (planarHeatResolventPrimitive_continuousWithinAt r) hd
    (planarHeatResolventDerivative_integrable r) hzero
  have hL := planarResolventOf_heat_representation
    (planarLaplacian_continuous (planarForcing_C7.of_le (by norm_num)))
    (planarLaplacian_hasCompactSupport planarForcing_hasCompactSupport) r
  have hLi := planarResolventOf_heat_integrable
    (planarLaplacian_continuous (planarForcing_C7.of_le (by norm_num)))
    (planarLaplacian_hasCompactSupport planarForcing_hasCompactSupport) r
  simp only [planarHeatResolventDerivative, planarHeatResolventPrimitive_zero, zero_sub,
    integral_sub hLi (planarResolventMode_heat_integrable r), ← hL,
    ← planarResolventMode_heat_representation, ← planarResolventMode_laplacian_integral] at hFTC
  linarith

theorem manufacturedPlanarWell_eigen_equation (r : PlanarPosition) :
    planarLaplacian planarResolventMode r =
      (2 * manufacturedPlanarWell r + 1) * planarResolventMode r := by
  rw [planarResolventMode_equation]
  unfold manufacturedPlanarWell
  field_simp [(planarResolventMode_positive r).ne']
  ring

theorem manufacturedPlanarWell_test_lower (u : PlanarPosition → ℝ)
    (hu : ContDiff ℝ 1 u) (hc : HasCompactSupport u) :
    -(1 / 2 : ℝ) * (∫ x, u x ^ 2) ≤ planarTestForm manufacturedPlanarWell u :=
  planar_positive_mode_form_lower planarResolventMode manufacturedPlanarWell u
    (planarResolventMode_C7.of_le (by norm_num)) planarResolventMode_positive
    manufacturedPlanarWell_C7.continuous manufacturedPlanarWell_eigen_equation hu hc

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_VerticalMode
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual normalized Gaussian in the transverse direction. -/

noncomputable section
open MeasureTheory
open scoped ContDiff
namespace ContinuumCoulomb

theorem verticalMode_normalized {freq : ℝ} (hfreq : 0 < freq) :
    (∫ z : ℝ, verticalMode freq z ^ 2) = 1 := by
  simp_rw [verticalMode_square hfreq]
  rw [integral_div, integral_gaussian, div_self]
  exact (Real.sqrt_pos.mpr (div_pos Real.pi_pos hfreq)).ne'

theorem verticalMode_memLp {freq : ℝ} (hfreq : 0 < freq) : MemLp (verticalMode freq) 2 :=
  (memLp_two_iff_integrable_sq (verticalMode_smooth freq).continuous.aestronglyMeasurable).mpr
    (verticalMode_square_integrable hfreq)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_SplitCoordinates
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Volume-preserving planar/transverse coordinates for the actual
three-dimensional Coulomb space. The intermediate product has its Euclidean
L² norm; the final ordinary product carries the same product volume. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

theorem positionSplitCoordinates_integral (f : SplitPosition → ℝ) :
    (∫ x : Position, f (positionSplitCoordinates x)) = ∫ p, f p :=
  positionSplitCoordinates_measurePreserving.integral_comp
    positionSplitCoordinates.toHomeomorph.measurableEmbedding f

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_LocalizedCoulomb
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite actual Coulomb interactions of the localized densities. Bounded
probability densities permit the existing elementary near/far Coulomb bound;
no interaction coefficient is introduced as a spectral input. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

theorem localizedDensity_potential_nonnegative (freq : ℝ) (u : PlanarPosition) (x : Position) :
    0 ≤ NeutralAtom.potentialOf (localizedDensity freq u) x :=
  integral_nonneg (fun _ => mul_nonneg (NeutralAtom.coulombKernel_nonneg _)
    (localizedDensity_nonnegative freq u _))

theorem localizedCoulombCoeff_nonnegative (freq : ℝ) (u v : PlanarPosition) :
    0 ≤ localizedCoulombCoeff freq u v :=
  integral_nonneg (fun x => mul_nonneg (localizedDensity_nonnegative freq u x)
    (localizedDensity_potential_nonnegative freq v x))

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_PlanarSharpDecay
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.planarHeatResolventPrimitive_zero _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A sharp exponential rate for the actual planar resolvent mode. Gaussian
exponential tilting gives a polynomial prefactor and decay `exp (-|r|)`, as
needed to bracket the contact hoppings at lengths `(1±ε)D`. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

theorem planarHeatKernel_tilt {t : ℝ} (ht : 0 < t) (e b : PlanarPosition) :
    planarHeatKernel t b * Real.exp (inner ℝ e b) =
      Real.exp (t * ‖e‖ ^ 2) * planarHeatKernel t (b - (2 * t) • e) := by
  have he : -‖b‖ ^ 2 / (4 * t) + inner ℝ e b =
      t * ‖e‖ ^ 2 + -‖b - (2 * t) • e‖ ^ 2 / (4 * t) := by
    rw [norm_sub_sq_real, real_inner_smul_right, norm_smul, mul_pow,
      Real.norm_eq_abs, sq_abs, real_inner_comm b e]
    field_simp
    ring
  unfold planarHeatKernel
  rw [mul_assoc, ← Real.exp_add, he, Real.exp_add]
  ring

theorem planarForcing_exponential_bound (e s : PlanarPosition) :
    planarForcing s ≤ Real.exp (‖e‖ - inner ℝ e s) := by
  by_cases hf : planarForcing s = 0
  · rw [hf]
    exact (Real.exp_pos _).le
  have hs : ‖s‖ ≤ 1 := le_of_lt (lt_of_not_ge
    (fun h => hf (planarForcing_zero_of_norm_ge_one h)))
  have hi : inner ℝ e s ≤ ‖e‖ := (real_inner_le_norm e s).trans
    (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hs (norm_nonneg e))
  exact (planarForcing_le_one s).trans (Real.one_le_exp (by linarith))

theorem planarHeatForcing_tilt_bound {t : ℝ} (ht : 0 < t) (e r b : PlanarPosition) :
    planarHeatKernel t b * planarForcing (r - b) ≤
      (Real.exp (‖e‖ - inner ℝ e r) * Real.exp (t * ‖e‖ ^ 2)) *
        planarHeatKernel t (b - (2 * t) • e) := by
  calc
    _ ≤ planarHeatKernel t b * Real.exp (‖e‖ - inner ℝ e (r - b)) :=
      mul_le_mul_of_nonneg_left (planarForcing_exponential_bound e (r - b))
        (planarHeatKernel_positive ht b).le
    _ = Real.exp (‖e‖ - inner ℝ e r) *
        (planarHeatKernel t b * Real.exp (inner ℝ e b)) := by
      rw [inner_sub_right, show ‖e‖ - (inner ℝ e r - inner ℝ e b) =
        (‖e‖ - inner ℝ e r) + inner ℝ e b by ring, Real.exp_add]
      ring
    _ = _ := by rw [planarHeatKernel_tilt ht]; ring

theorem planarHeatAverage_tilt_bound {t : ℝ} (ht : 0 < t) (e r : PlanarPosition) :
    planarHeatAverage t r ≤
      Real.exp (‖e‖ - inner ℝ e r) * Real.exp (t * ‖e‖ ^ 2) := by
  have hi := ((planarHeatKernel_integrable ht).comp_sub_right ((2 * t) • e)).const_mul
    (Real.exp (‖e‖ - inner ℝ e r) * Real.exp (t * ‖e‖ ^ 2))
  have h := integral_mono (planarHeatAverage_integrand_integrable ht r) hi
    (planarHeatForcing_tilt_bound ht e r)
  simpa only [planarHeatAverage, integral_const_mul, integral_sub_right_eq_self,
    planarHeatKernel_integral ht, mul_one] using h

theorem planarResolventMode_tilt_bound (e r : PlanarPosition) (he : ‖e‖ < 1) :
    planarResolventMode r ≤ Real.exp (‖e‖ - inner ℝ e r) / (1 - ‖e‖ ^ 2) := by
  have hc : 0 < 1 - ‖e‖ ^ 2 := by nlinarith [norm_nonneg e]
  have hi : IntegrableOn (fun t : ℝ => Real.exp (-(1 - ‖e‖ ^ 2) * t)) (Set.Ioi 0) :=
    exp_neg_integrableOn_Ioi 0 hc
  rw [planarResolventMode_heat_representation]
  have h := integral_mono_ae (planarResolventMode_heat_integrable r)
    (hi.const_mul (Real.exp (‖e‖ - inner ℝ e r))) (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      calc
        _ ≤ Real.exp (-t) * (Real.exp (‖e‖ - inner ℝ e r) * Real.exp (t * ‖e‖ ^ 2)) :=
          mul_le_mul_of_nonneg_left (planarHeatAverage_tilt_bound ht e r) (Real.exp_pos _).le
        _ = Real.exp (‖e‖ - inner ℝ e r) * Real.exp (-(1 - ‖e‖ ^ 2) * t) := by
          rw [show -(1 - ‖e‖ ^ 2) * t = -t + t * ‖e‖ ^ 2 by ring, Real.exp_add]
          ring)
  have heval : (∫ t : ℝ in Set.Ioi 0, Real.exp (-(1 - ‖e‖ ^ 2) * t)) =
      (1 - ‖e‖ ^ 2)⁻¹ := by
    rw [integral_exp_mul_Ioi (by linarith : -(1 - ‖e‖ ^ 2) < 0)]
    simp
    rw [show ‖e‖ ^ 2 - 1 = -(1 - ‖e‖ ^ 2) by ring, div_neg]
    simp only [neg_div, neg_neg, one_div]
  simpa only [integral_const_mul, heval, div_eq_mul_inv] using h

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_PlanarExponentialEnvelope
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.planarHeatResolventPrimitive_zero _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Global exponential envelopes at every fixed rate below one, and
integrability of their planar radial envelopes. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

theorem planarExponentialConstant_positive {a : ℝ} (ha : 0 ≤ a) (ha₁ : a < 1) :
    0 < planarExponentialConstant a := div_pos (Real.exp_pos _) (by nlinarith)

theorem planarResolventMode_exponential_envelope {a : ℝ} (ha : 0 ≤ a) (ha₁ : a < 1)
    (r : PlanarPosition) : planarResolventMode r ≤ planarExponentialConstant a * Real.exp (-a * ‖r‖) := by
  have hd : 0 < 1 - a ^ 2 := by nlinarith
  by_cases hr : r = 0
  · subst r
    simp only [norm_zero, mul_zero, Real.exp_zero, mul_one]
    apply (planarResolventMode_le_one 0).trans
    apply (le_div_iff₀ hd).mpr
    have h := Real.one_le_exp ha
    nlinarith [sq_nonneg a]
  have hnorm : 0 < ‖r‖ := norm_pos_iff.mpr hr
  let e : PlanarPosition := (a / ‖r‖) • r
  have he : ‖e‖ = a := by
    dsimp [e]
    rw [norm_smul, Real.norm_of_nonneg (div_nonneg ha hnorm.le)]
    field_simp
  have hi : inner ℝ e r = a * ‖r‖ := by
    dsimp [e]
    rw [real_inner_smul_left, real_inner_self_eq_norm_sq]
    field_simp
  have h := planarResolventMode_tilt_bound e r (by rw [he]; exact ha₁)
  rw [he, hi] at h
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  unfold planarExponentialConstant
  rw [show a - a * ‖r‖ = a + -a * ‖r‖ by ring, Real.exp_add]
  ring

theorem exponential_inverse_cubic_bound {c : ℝ} (hc : 0 < c) {t : ℝ} (ht : 0 ≤ t) :
    Real.exp (-c * t) ≤ (1 + 3 / c) ^ 3 / (1 + t) ^ 3 := by
  have hq : 0 < c / 3 := by positivity
  have he := Real.add_one_le_exp (c / 3 * t)
  have ht' : t ≤ (3 / c) * Real.exp (c / 3 * t) := by
    have h : t * c ≤ 3 * Real.exp (c / 3 * t) := by nlinarith only [he]
    calc
      _ ≤ (3 * Real.exp (c / 3 * t)) / c := (le_div_iff₀ hc).mpr h
      _ = _ := by ring
  have h₁ : 1 ≤ Real.exp (c / 3 * t) := Real.one_le_exp (mul_nonneg hq.le ht)
  have hb : 1 + t ≤ (1 + 3 / c) * Real.exp (c / 3 * t) := by nlinarith only [ht', h₁]
  have hp := pow_le_pow_left₀ (by linarith : 0 ≤ 1 + t) hb 3
  rw [mul_pow, ← Real.exp_nat_mul] at hp
  norm_num only [Nat.cast_ofNat] at hp
  have harg : (3 : ℝ) * (c / 3 * t) = c * t := by ring
  rw [harg] at hp
  have hm := mul_le_mul_of_nonneg_left hp (Real.exp_pos (-c * t)).le
  have hexp : Real.exp (-c * t) * Real.exp (c * t) = 1 := by
    rw [← Real.exp_add]
    simp
  have hbound : Real.exp (-c * t) * (1 + t) ^ 3 ≤ (1 + 3 / c) ^ 3 := by
    calc
      _ ≤ Real.exp (-c * t) * ((1 + 3 / c) ^ 3 * Real.exp (c * t)) := hm
      _ = _ := by rw [mul_left_comm, hexp, mul_one]
  exact (le_div_iff₀ (pow_pos (by linarith : 0 < 1 + t) 3)).mpr hbound

theorem planar_exp_norm_integrable {c : ℝ} (hc : 0 < c) :
    Integrable (fun r : PlanarPosition => Real.exp (-c * ‖r‖)) := by
  have hi : Integrable (fun r : PlanarPosition => (1 + ‖r‖) ^ (-(3 : ℝ))) :=
    integrable_one_add_norm (by norm_num [PlanarPosition])
  apply (hi.const_mul ((1 + 3 / c) ^ 3)).mono' (by fun_prop)
  exact Filter.Eventually.of_forall (fun r => by
    rw [Real.norm_of_nonneg (Real.exp_pos _).le, Real.rpow_neg (by positivity)]
    simpa only [Real.rpow_ofNat, div_eq_mul_inv] using exponential_inverse_cubic_bound hc (norm_nonneg r))

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_PlanarOverlap
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual normalized planar orbitals have overlap bounded at rate 0.9,
uniformly over every pair of centers. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

theorem normalizedPlanarExponentialConstant_positive {a : ℝ} (ha : 0 ≤ a) (ha₁ : a < 1) :
    0 < normalizedPlanarExponentialConstant a :=
  div_pos (planarExponentialConstant_positive ha ha₁)
    (Real.sqrt_pos.mpr planarResolventMode_square_integral_positive)

theorem normalizedPlanarMode_exponential_envelope {a : ℝ} (ha : 0 ≤ a) (ha₁ : a < 1)
    (r : PlanarPosition) :
    normalizedPlanarMode r ≤ normalizedPlanarExponentialConstant a * Real.exp (-a * ‖r‖) := by
  have h := div_le_div_of_nonneg_right (planarResolventMode_exponential_envelope ha ha₁ r)
    (Real.sqrt_nonneg (∫ r, planarResolventMode r ^ 2))
  convert h using 1 <;> first | rfl | (unfold normalizedPlanarExponentialConstant; ring)

theorem planarModeOverlap_integrable (u v : PlanarPosition) :
    Integrable (fun r => normalizedPlanarMode (r - u) * normalizedPlanarMode (r - v)) :=
  (normalizedPlanarMode_memLp.comp_measurePreserving (measurePreserving_sub_right volume u)).integrable_mul
    (normalizedPlanarMode_memLp.comp_measurePreserving (measurePreserving_sub_right volume v))

theorem planarModeOverlap_nonnegative (u v : PlanarPosition) : 0 ≤ planarModeOverlap u v :=
  integral_nonneg (fun _ => mul_nonneg (normalizedPlanarMode_positive _).le (normalizedPlanarMode_positive _).le)

theorem planarModeOverlap_diagonal (u : PlanarPosition) : planarModeOverlap u u = 1 := by
  unfold planarModeOverlap
  simp_rw [← pow_two]
  rw [integral_sub_right_eq_self (fun r => normalizedPlanarMode r ^ 2) u,
    normalizedPlanarMode_normalized]

theorem planarModeOverlap_envelope {a b : ℝ} (hb : 0 ≤ b) (hba : b < a) (ha₁ : a < 1)
    (u v : PlanarPosition) :
    planarModeOverlap u v ≤
      (normalizedPlanarExponentialConstant a ^ 2 *
        (∫ r : PlanarPosition, Real.exp (-(a - b) * ‖r‖))) * Real.exp (-b * ‖u - v‖) := by
  have ha : 0 ≤ a := le_trans hb hba.le
  have hC := (normalizedPlanarExponentialConstant_positive ha ha₁).le
  have hpt (r : PlanarPosition) :
      normalizedPlanarMode (r - u) * normalizedPlanarMode (r - v) ≤
        (normalizedPlanarExponentialConstant a ^ 2 * Real.exp (-b * ‖u - v‖)) *
          Real.exp (-(a - b) * ‖r - u‖) := by
    have ht : ‖u - v‖ ≤ ‖r - u‖ + ‖r - v‖ := by
      simpa only [dist_eq_norm, norm_sub_rev u r] using dist_triangle u r v
    have hs := mul_le_mul_of_nonneg_left ht hb
    have he : -a * (‖r - u‖ + ‖r - v‖) ≤ -b * ‖u - v‖ + -(a - b) * ‖r - u‖ := by
      nlinarith [mul_nonneg (sub_pos.mpr hba).le (norm_nonneg (r - v))]
    calc
      _ ≤ (normalizedPlanarExponentialConstant a * Real.exp (-a * ‖r - u‖)) *
          (normalizedPlanarExponentialConstant a * Real.exp (-a * ‖r - v‖)) :=
        mul_le_mul (normalizedPlanarMode_exponential_envelope ha ha₁ _)
          (normalizedPlanarMode_exponential_envelope ha ha₁ _)
          (normalizedPlanarMode_positive _).le (mul_nonneg hC (Real.exp_pos _).le)
      _ = normalizedPlanarExponentialConstant a ^ 2 * Real.exp (-a * (‖r - u‖ + ‖r - v‖)) := by
        rw [show -a * (‖r - u‖ + ‖r - v‖) = -a * ‖r - u‖ + -a * ‖r - v‖ by ring,
          Real.exp_add]
        ring
      _ ≤ normalizedPlanarExponentialConstant a ^ 2 *
          Real.exp (-b * ‖u - v‖ + -(a - b) * ‖r - u‖) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr he) (sq_nonneg _)
      _ = _ := by rw [Real.exp_add]; ring
  have hi := ((planar_exp_norm_integrable (sub_pos.mpr hba)).comp_sub_right u).const_mul
    (normalizedPlanarExponentialConstant a ^ 2 * Real.exp (-b * ‖u - v‖))
  have h := integral_mono (planarModeOverlap_integrable u v) hi hpt
  rw [integral_const_mul, integral_sub_right_eq_self
    (fun r : PlanarPosition => Real.exp (-(a - b) * ‖r‖)) u] at h
  exact h.trans_eq (by ring)

theorem planarOverlapConstant_nonnegative : 0 ≤ planarOverlapConstant :=
  mul_nonneg (sq_nonneg _) (integral_nonneg (fun _ => (Real.exp_pos _).le))

theorem planarModeOverlap_decay (u v : PlanarPosition) :
    planarModeOverlap u v ≤ planarOverlapConstant * Real.exp (-(9 / 10 : ℝ) * ‖u - v‖) := by
  have h := planarModeOverlap_envelope (a := 19 / 20) (b := 9 / 10)
    (by norm_num) (by norm_num) (by norm_num) u v
  norm_num only [show (19 / 20 : ℝ) - 9 / 10 = 1 / 20 by norm_num] at h
  exact h

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_CoulombGramApprox
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Quantitative local duality for overlapping densities. The compact local
tests are disjoint; the electron density packets need not be disjoint. -/

noncomputable section
open MeasureTheory
open scoped BigOperators ContDiff
namespace ContinuumCoulomb

theorem dualMatrix_quadratic_lower {m : ℕ} (A : Fin m → Fin m → ℝ)
    {a delta : ℝ} (hdelta : 0 ≤ delta) (hdiag : ∀ i, a ≤ A i i)
    (hoff : ∀ i j, i ≠ j → |A i j| ≤ delta) (d : Fin m → ℝ) :
    (a - m * delta) * ∑ i, d i ^ 2 ≤ ∑ i, ∑ j, A i j * d i * d j := by
  classical
  have hpoint (i j : Fin m) :
      (if i = j then a * d i ^ 2 else 0) - delta / 2 * (d i ^ 2 + d j ^ 2) ≤
        A i j * d i * d j := by
    by_cases hij : i = j
    · subst j
      rw [ite_eq_left rfl]
      have h := mul_le_mul_of_nonneg_right (hdiag i) (sq_nonneg (d i))
      have hzero := mul_nonneg hdelta (sq_nonneg (d i))
      nlinarith
    · rw [ite_eq_right hij, zero_sub]
      have hprod : |A i j * d i * d j| ≤ delta * (|d i| * |d j|) := by
        calc
          _ = |A i j| * (|d i| * |d j|) := by simp only [abs_mul]; ring
          _ ≤ _ := mul_le_mul_of_nonneg_right (hoff i j hij)
            (mul_nonneg (abs_nonneg _) (abs_nonneg _))
      have htwo : 2 * (|d i| * |d j|) ≤ d i ^ 2 + d j ^ 2 := by
        nlinarith [sq_nonneg (|d i| - |d j|), sq_abs (d i), sq_abs (d j)]
      have hscaled := mul_le_mul_of_nonneg_left htwo hdelta
      nlinarith [neg_abs_le (A i j * d i * d j)]
  have hsum := Finset.sum_le_sum (s := Finset.univ) fun i _ =>
    Finset.sum_le_sum (s := Finset.univ) fun j _ => hpoint i j
  have hrow (i : Fin m) :
      (∑ j, ((if i = j then a * d i ^ 2 else 0) - delta / 2 * (d i ^ 2 + d j ^ 2))) =
      a * d i ^ 2 - delta / 2 * ((m : ℝ) * d i ^ 2 + ∑ j, d j ^ 2) := by
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_add_distrib]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true, if_true, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  simp_rw [hrow] at hsum
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  convert hsum using 1
  all_goals try with_reducible_and_instances rfl
  ring

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_LocalizedCounterterms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The manuscript's actual well-depth counterterms: direct Coulomb sums
divided by the fixed positive onsite well integral. Their diagonal action
cancels the required linear occupancy term exactly. -/

noncomputable section
open scoped BigOperators
namespace ContinuumCoulomb

theorem localizedOffsiteSum_nonnegative (freq : ℝ) {m : ℕ} (u : Fin m → PlanarPosition) (i : Fin m) :
    0 ≤ localizedOffsiteSum freq u i := by
  apply Finset.sum_nonneg
  intro j _
  split_ifs
  · exact le_rfl
  · exact localizedCoulombCoeff_nonnegative freq _ _

theorem localizedCounterterm_nonnegative (freq : ℝ) {m : ℕ} (u : Fin m → PlanarPosition) (i : Fin m) :
    0 ≤ localizedCounterterm freq u i :=
  div_nonneg (localizedOffsiteSum_nonnegative freq u i) (planarHopping_positive 0).le

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_PlanarSobolev
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Closure of the actual manufactured-well inequality on the planar
Sobolev graph. The bounded potential acts on actual L² classes, and the
form is continuous in the function-and-gradient norm. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb

namespace PlanarSobolev

theorem planar_integral_change_borel
    (m : MeasurableSpace PlanarPosition) (hm : @BorelSpace PlanarPosition _ m)
    (f : PlanarPosition → ℝ) :
    (letI : MeasurableSpace PlanarPosition := m
     letI : BorelSpace PlanarPosition := hm
     letI : MeasureSpace PlanarPosition := measureSpaceOfInnerProductSpace
     ∫ x, f x) = originalIntegral f := by
  have he : m = originalMeasurable :=
    hm.measurable_eq.trans originalBorel.measurable_eq.symm
  cases he
  rfl

attribute [local instance] OAI.ContinuumCoulomb.PlanarSobolev.instMeasurableSpacePlanarPosition
attribute [local instance] OAI.ContinuumCoulomb.PlanarSobolev.instBorelSpacePlanarPosition
attribute [local instance] OAI.ContinuumCoulomb.PlanarSobolev.instMeasureSpacePlanarPosition
theorem wellBound_nonnegative : 0 ≤ wellBound :=
  (norm_nonneg (manufacturedPlanarWell 0)).trans (wellBound_spec 0)

theorem form_continuous : Continuous form :=
  (continuous_const.mul (continuous_snd.norm.pow 2)).add
    (continuous_fst.inner (wellMultiplier.continuous.comp continuous_fst))

private theorem l2_norm_sq (u : Lp PlanarPosition 2 (volume : Measure PlanarPosition)) :
    ‖u‖ ^ 2 = ∫ x, ‖u x‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  simp only [real_inner_self_eq_norm_sq]

private theorem l2_real_norm_sq (u : Lp ℝ 2 (volume : Measure PlanarPosition)) :
    ‖u‖ ^ 2 = ∫ x, u x ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  simp only [RCLike.inner_apply, conj_trivial, sq]

open RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean in
theorem graph_mass (u : Test) :
    ‖(graph (μ := volume) u).1‖ ^ 2 = ∫ x, u.val x ^ 2 := by
  rw [l2_real_norm_sq]
  apply integral_congr_ae
  filter_upwards [(memLp_of_mem_C1c (μ := volume) u.property).coeFn_toLp] with x hx
  exact congrArg (fun t : ℝ => t ^ 2) hx

open RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean in
theorem graph_kinetic (u : Test) :
    ‖(graph (μ := volume) u).2‖ ^ 2 =
      ∑ a : Fin 2, ∫ x, planarPartial u.val (planarAxis a) x ^ 2 := by
  rw [l2_norm_sq]
  have hi (a : Fin 2) : Integrable (fun x => planarPartial u.val (planarAxis a) x ^ 2) := by
    have hc : HasCompactSupport (planarPartial u.val (planarAxis a)) :=
      u.property.2.fderiv_apply ℝ (planarAxis a)
    have hs : HasCompactSupport (fun x => planarPartial u.val (planarAxis a) x ^ 2) :=
      hc.comp_left (g := fun t : ℝ => t ^ 2) (by norm_num)
    exact ((planarPartial_continuous u.property.1 (planarAxis a)).pow 2).integrable_of_hasCompactSupport hs
  rw [← integral_finsetSum Finset.univ (fun a _ => hi a)]
  apply integral_congr_ae
  filter_upwards [(memLp_grad_of_mem_C1c (μ := volume) u.property).coeFn_toLp] with x hx
  change ‖toL2Grad (μ := volume) u x‖ ^ 2 = _
  change toL2Grad (μ := volume) u x = grad u.val x at hx
  rw [hx, EuclideanSpace.real_norm_sq_eq]
  exact Finset.sum_congr rfl (fun a _ => congrArg (fun t : ℝ => t ^ 2) (grad_coordinate _ _ _))

open RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean in
theorem graph_form (u : Test) :
    form (graph (μ := volume) u) = planarTestForm manufacturedPlanarWell u.val := by
  unfold form planarTestForm
  rw [graph_kinetic, L2.inner_def]
  have he (f : PlanarPosition → ℝ) := planar_integral_change_borel
    (borel PlanarPosition) ⟨rfl⟩ f
  apply congrArg₂ (· + ·)
  · congr 1
    exact Finset.sum_congr rfl (fun a _ => he _)
  · change (∫ x, inner ℝ ((graph (μ := volume) u).1 x)
        (wellMultiplier (graph (μ := volume) u).1 x)) =
      originalIntegral (fun x => manufacturedPlanarWell x * u.val x ^ 2)
    rw [← he (fun x => manufacturedPlanarWell x * u.val x ^ 2)]
    apply integral_congr_ae
    filter_upwards [(memLp_of_mem_C1c (μ := volume) u.property).coeFn_toLp,
      wellMultiply_ae (toL2 (μ := volume) u)] with x hx hw
    change toL2 (μ := volume) u x = u.val x at hx
    change inner ℝ (toL2 (μ := volume) u x) (wellMultiply (toL2 (μ := volume) u) x) = _
    rw [hw, hx, RCLike.inner_apply, conj_trivial]
    ring

open RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean in
/-- The proved inequality survives closure in the actual Sobolev norm. -/
theorem form_lower (u : Sobolev) :
    -(1 / 2 : ℝ) * ‖u.val.1‖ ^ 2 ≤ form u.val := by
  have hclosed : IsClosed {v : Target | -(1 / 2 : ℝ) * ‖v.1‖ ^ 2 ≤ form v} :=
    isClosed_le (continuous_const.mul (continuous_fst.norm.pow 2)) form_continuous
  have hdense : (LinearMap.range (graph (μ := volume) (E := PlanarPosition)) : Set Target) ⊆
      {v | -(1 / 2 : ℝ) * ‖v.1‖ ^ 2 ≤ form v} := by
    rintro _ ⟨v, rfl⟩
    change -(1 / 2 : ℝ) * ‖(graph (μ := volume) v).1‖ ^ 2 ≤ form (graph (μ := volume) v)
    rw [graph_mass, graph_form]
    rw [planar_integral_change_borel (borel PlanarPosition) ⟨rfl⟩]
    exact manufacturedPlanarWell_test_lower v.val v.property.1 v.property.2
  exact closure_minimal hdense hclosed u.property

end PlanarSobolev
end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_PlanarModeH1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Membership of the manufactured mode in the closed planar Sobolev
graph, obtained by expanding compact cutoffs. -/

noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology ContDiff
namespace ContinuumCoulomb
namespace PlanarSobolev
open RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean

attribute [local instance] OAI.ContinuumCoulomb.PlanarSobolev.instMeasurableSpacePlanarPosition_1
attribute [local instance] OAI.ContinuumCoulomb.PlanarSobolev.instBorelSpacePlanarPosition_1
attribute [local instance] OAI.ContinuumCoulomb.PlanarSobolev.instMeasureSpacePlanarPosition_1
theorem cutoffGradBound_spec (x : PlanarPosition) : ‖grad cutoffBump x‖ ≤ cutoffGradBound :=
  Classical.choose_spec bump_grad_bounded x

end PlanarSobolev
end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_PlanarIMS
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.planarHeatResolventPrimitive_zero _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! IMS localization for the actual planar kinetic and potential integrals.
The partition functions need not have compact support; the test function
does. In particular the exterior member of a multiwell partition is allowed. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb

theorem planarPartial_finsetSum {ι : Type*} (s : Finset ι)
    (f : ι → PlanarPosition → ℝ) (hf : ∀ i ∈ s, ContDiff ℝ 1 (f i))
    (e x : PlanarPosition) :
    planarPartial (fun y => ∑ i ∈ s, f i y) e x = ∑ i ∈ s, planarPartial (f i) e x := by
  unfold planarPartial
  rw [fderiv_fun_sum (fun i hi => (hf i hi).differentiable (by norm_num) x)]
  simp only [sum_apply]

theorem planar_partition_cross {ι : Type*} [Fintype ι]
    (θ : ι → PlanarPosition → ℝ) (hθ : ∀ i, ContDiff ℝ 1 (θ i))
    (hpart : ∀ x, ∑ i, θ i x ^ 2 = 1) (e x : PlanarPosition) :
    ∑ i, θ i x * planarPartial (θ i) e x = 0 := by
  have he : (fun y => ∑ i, θ i y * θ i y) = (fun _ : PlanarPosition => (1 : ℝ)) := by
    funext y
    simpa only [← sq] using hpart y
  have hd := congrArg (fun f : PlanarPosition → ℝ => planarPartial f e x) he
  rw [planarPartial_finsetSum _ _ (fun i _ => (hθ i).mul (hθ i))] at hd
  simp_rw [planarPartial_mul _ _ (hθ _) (hθ _)] at hd
  have hz : planarPartial (fun _ : PlanarPosition => (1 : ℝ)) e x = 0 := by
    simp [planarPartial]
  rw [hz, Finset.sum_add_distrib] at hd
  linarith

theorem planar_partition_gradient_identity {ι : Type*} [Fintype ι]
    (θ : ι → PlanarPosition → ℝ) (hθ : ∀ i, ContDiff ℝ 1 (θ i))
    (hpart : ∀ x, ∑ i, θ i x ^ 2 = 1)
    (u : PlanarPosition → ℝ) (hu : ContDiff ℝ 1 u) (e x : PlanarPosition) :
    (∑ i, planarPartial (fun y => θ i y * u y) e x ^ 2) =
      planarPartial u e x ^ 2 + (∑ i, planarPartial (θ i) e x ^ 2) * u x ^ 2 := by
  simp_rw [planarPartial_mul _ _ (hθ _) hu]
  calc
    (∑ i, (θ i x * planarPartial u e x + u x * planarPartial (θ i) e x) ^ 2) =
        (∑ i, θ i x ^ 2) * planarPartial u e x ^ 2 +
          (2 * u x * planarPartial u e x) * (∑ i, θ i x * planarPartial (θ i) e x) +
          (∑ i, planarPartial (θ i) e x ^ 2) * u x ^ 2 := by
      simp only [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = _ := by rw [hpart x, planar_partition_cross θ hθ hpart e x]; ring

theorem planar_partition_potential_identity {ι : Type*} [Fintype ι]
    (θ : ι → PlanarPosition → ℝ) (hpart : ∀ x, ∑ i, θ i x ^ 2 = 1)
    (W u : PlanarPosition → ℝ) (x : PlanarPosition) :
    (∑ i, W x * (θ i x * u x) ^ 2) = W x * u x ^ 2 := by
  calc
    (∑ i, W x * (θ i x * u x) ^ 2) = (W x * u x ^ 2) * ∑ i, θ i x ^ 2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = _ := by rw [hpart x, mul_one]

theorem planar_partition_direction_integral {ι : Type*} [Fintype ι]
    (θ : ι → PlanarPosition → ℝ) (hθ : ∀ i, ContDiff ℝ 1 (θ i))
    (hpart : ∀ x, ∑ i, θ i x ^ 2 = 1)
    (u : PlanarPosition → ℝ) (hu : ContDiff ℝ 1 u) (hc : HasCompactSupport u)
    (e : PlanarPosition) :
    (∑ i, ∫ x, planarPartial (fun y => θ i y * u y) e x ^ 2) =
      (∫ x, planarPartial u e x ^ 2) +
        ∫ x, (∑ i, planarPartial (θ i) e x ^ 2) * u x ^ 2 := by
  have hi (i : ι) : Integrable (fun x => planarPartial (fun y => θ i y * u y) e x ^ 2) :=
    planar_partial_square_integrable _ ((hθ i).mul hu) hc.mul_left e
  have he : Integrable (fun x => (∑ i, planarPartial (θ i) e x ^ 2) * u x ^ 2) := by
    have hs : HasCompactSupport (fun x => u x ^ 2) :=
      hc.comp_left (g := fun t : ℝ => t ^ 2) (by norm_num)
    have hm : HasCompactSupport (fun x => (∑ i, planarPartial (θ i) e x ^ 2) * u x ^ 2) :=
      hs.mul_left
    have hd : Continuous (fun x => ∑ i, planarPartial (θ i) e x ^ 2) :=
      continuous_finsetSum _ (fun i _ => (planarPartial_continuous (hθ i) e).pow 2)
    exact (hd.mul (hu.continuous.pow 2)).integrable_of_hasCompactSupport hm
  rw [← integral_finsetSum _ (fun i _ => hi i),
    ← integral_add (planar_partial_square_integrable u hu hc e) he]
  exact integral_congr_ae (Filter.Eventually.of_forall
    (planar_partition_gradient_identity θ hθ hpart u hu e))

theorem planar_potential_test_integrable (W u : PlanarPosition → ℝ) (hW : Continuous W)
    (hu : Continuous u) (hc : HasCompactSupport u) : Integrable (fun x => W x * u x ^ 2) := by
  have hs : HasCompactSupport (fun x => u x ^ 2) :=
    hc.comp_left (g := fun t : ℝ => t ^ 2) (by norm_num)
  have hm : HasCompactSupport (fun x => W x * u x ^ 2) := hs.mul_left
  exact (hW.mul (hu.pow 2)).integrable_of_hasCompactSupport hm

/-- Exact IMS formula, with the localization cost expressed through the
actual classical directional derivatives of the partition. -/
theorem planar_IMS {ι : Type*} [Fintype ι]
    (θ : ι → PlanarPosition → ℝ) (hθ : ∀ i, ContDiff ℝ 1 (θ i))
    (hpart : ∀ x, ∑ i, θ i x ^ 2 = 1)
    (W u : PlanarPosition → ℝ) (hW : Continuous W)
    (hu : ContDiff ℝ 1 u) (hc : HasCompactSupport u) :
    (∑ i, planarTestForm W (fun x => θ i x * u x)) =
      planarTestForm W u + (1/2 : ℝ) *
        ∑ a : Fin 2, ∫ x, (∑ i, planarPartial (θ i) (planarAxis a) x ^ 2) * u x ^ 2 := by
  have hi (i : ι) : Integrable (fun x => W x * (θ i x * u x) ^ 2) := by
    have hm : HasCompactSupport (fun x => θ i x * u x) := hc.mul_left
    exact planar_potential_test_integrable W _ hW ((hθ i).continuous.mul hu.continuous) hm
  have hp : (∑ i, ∫ x, W x * (θ i x * u x) ^ 2) = ∫ x, W x * u x ^ 2 := by
    rw [← integral_finsetSum _ (fun i _ => hi i)]
    exact integral_congr_ae (Filter.Eventually.of_forall
      (planar_partition_potential_identity θ hpart W u))
  unfold planarTestForm
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_comm]
  simp_rw [planar_partition_direction_integral θ hθ hpart u hu hc]
  rw [Finset.sum_add_distrib, hp]
  ring

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_PlanarPartition
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.planarHeatResolventPrimitive_zero _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A smooth square partition for finitely many disjoint planar cutoffs.
The exterior function is smooth even on the regions where all site cutoffs
vanish; no square root at a zero is used. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb

theorem planarTrigPartition_C1 {ι : Type*} [Fintype ι]
    (χ : ι → PlanarPosition → ℝ) (hχ : ∀ i, ContDiff ℝ 1 (χ i))
    (i : Option ι) : ContDiff ℝ 1 (planarTrigPartition χ i) := by
  cases i with
  | none => exact contDiff_const.add (ContDiff.sum (fun i _ => (hχ i).cos.sub contDiff_const))
  | some i => exact (hχ i).sin

theorem disjoint_cutoff_vanish {ι : Type*}
    (χ : ι → PlanarPosition → ℝ)
    (hdisj : ∀ i j, i ≠ j → Disjoint (tsupport (χ i)) (tsupport (χ j)))
    {i j : ι} {x : PlanarPosition} (hxi : x ∈ tsupport (χ i)) (hji : j ≠ i)
    (e : PlanarPosition) : χ j x = 0 ∧ planarPartial (χ j) e x = 0 := by
  have hxj : x ∉ tsupport (χ j) :=
    fun hxj => Set.disjoint_left.mp (hdisj i j hji.symm) hxi hxj
  refine ⟨image_eq_zero_of_notMem_tsupport hxj, ?_⟩
  simp only [planarPartial, fderiv_of_notMem_tsupport ℝ hxj, zero_apply]

theorem planarTrigPartition_exterior_at {ι : Type*} [Fintype ι]
    (χ : ι → PlanarPosition → ℝ)
    (hdisj : ∀ i j, i ≠ j → Disjoint (tsupport (χ i)) (tsupport (χ j)))
    {i : ι} {x : PlanarPosition} (hxi : x ∈ tsupport (χ i)) :
    planarTrigPartition χ none x = Real.cos (χ i x) := by
  classical
  dsimp only [planarTrigPartition]
  rw [Finset.sum_eq_single i]
  · ring
  · intro j _ hji
    rw [(disjoint_cutoff_vanish χ hdisj hxi hji 0).1, Real.cos_zero, sub_self]
  · simp

/-- The exterior and all site members have square sum exactly one. -/
theorem planarTrigPartition_square_sum {ι : Type*} [Fintype ι]
    (χ : ι → PlanarPosition → ℝ)
    (hdisj : ∀ i j, i ≠ j → Disjoint (tsupport (χ i)) (tsupport (χ j)))
    (x : PlanarPosition) : ∑ i, planarTrigPartition χ i x ^ 2 = 1 := by
  classical
  rw [Fintype.sum_option]
  by_cases hx : ∃ i, x ∈ tsupport (χ i)
  · obtain ⟨i, hi⟩ := hx
    rw [planarTrigPartition_exterior_at χ hdisj hi]
    have hs : (∑ j, planarTrigPartition χ (some j) x ^ 2) = Real.sin (χ i x) ^ 2 := by
      apply Finset.sum_eq_single i
      · intro j _ hji
        simp only [planarTrigPartition, (disjoint_cutoff_vanish χ hdisj hi hji 0).1,
          Real.sin_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
      · simp
    rw [hs]
    nlinarith [Real.sin_sq_add_cos_sq (χ i x)]
  · have hz (i : ι) : χ i x = 0 :=
      image_eq_zero_of_notMem_tsupport (fun hi => hx ⟨i, hi⟩)
    simp only [planarTrigPartition, hz, Real.cos_zero, Real.sin_zero, sub_self,
      Finset.sum_const_zero, add_zero, one_pow, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, zero_pow]

theorem planarTrigPartition_partial_site {ι : Type*} [Fintype ι]
    (χ : ι → PlanarPosition → ℝ) (hχ : ∀ i, ContDiff ℝ 1 (χ i))
    (i : ι) (e x : PlanarPosition) :
    planarPartial (planarTrigPartition χ (some i)) e x =
      Real.cos (χ i x) * planarPartial (χ i) e x := by
  dsimp only [planarTrigPartition, planarPartial]
  rw [fderiv_sin ((hχ i).differentiable (by norm_num) x)]
  rfl

theorem planarTrigPartition_partial_exterior {ι : Type*} [Fintype ι]
    (χ : ι → PlanarPosition → ℝ) (hχ : ∀ i, ContDiff ℝ 1 (χ i))
    (e x : PlanarPosition) :
    planarPartial (planarTrigPartition χ none) e x =
      -(∑ i, Real.sin (χ i x) * planarPartial (χ i) e x) := by
  have hd (i : ι) : HasFDerivAt (fun y => Real.cos (χ i y) - 1)
      (-Real.sin (χ i x) • fderiv ℝ (χ i) x) x := by
    simpa only [sub_zero, Pi.sub_def] using
      (((hχ i).differentiable (by norm_num) x).hasFDerivAt.cos.sub (hasFDerivAt_const 1 x))
  have hs := (hasFDerivAt_const (1 : ℝ) x).add
    (HasFDerivAt.fun_sum (fun i (_ : i ∈ (Finset.univ : Finset ι)) => hd i))
  have he := congrArg (fun L : PlanarPosition →L[ℝ] ℝ => L e) hs.fderiv
  simpa only [planarTrigPartition, planarPartial, zero_add, sum_apply, smul_apply,
    smul_eq_mul, neg_mul, Finset.sum_neg_distrib, Pi.add_def, Pi.sub_def] using he

/-- Disjoint supports prevent a factor equal to the number of wells in the
localization error: the square gradient equals that of the active angle. -/
theorem planarTrigPartition_gradient_square {ι : Type*} [Fintype ι]
    (χ : ι → PlanarPosition → ℝ) (hχ : ∀ i, ContDiff ℝ 1 (χ i))
    (hdisj : ∀ i j, i ≠ j → Disjoint (tsupport (χ i)) (tsupport (χ j)))
    (e x : PlanarPosition) :
    (∑ i, planarPartial (planarTrigPartition χ i) e x ^ 2) =
      ∑ i, planarPartial (χ i) e x ^ 2 := by
  classical
  rw [Fintype.sum_option, planarTrigPartition_partial_exterior χ hχ]
  simp_rw [planarTrigPartition_partial_site χ hχ]
  by_cases hx : ∃ i, x ∈ tsupport (χ i)
  · obtain ⟨i, hi⟩ := hx
    have hz (j : ι) (hji : j ≠ i) : planarPartial (χ j) e x = 0 :=
      (disjoint_cutoff_vanish χ hdisj hi hji e).2
    have hs : (∑ j, Real.sin (χ j x) * planarPartial (χ j) e x) =
        Real.sin (χ i x) * planarPartial (χ i) e x := by
      apply Finset.sum_eq_single i
      · intro j _ hji
        rw [hz j hji, mul_zero]
      · simp
    have hc : (∑ j, (Real.cos (χ j x) * planarPartial (χ j) e x) ^ 2) =
        (Real.cos (χ i x) * planarPartial (χ i) e x) ^ 2 := by
      apply Finset.sum_eq_single i
      · intro j _ hji
        rw [hz j hji, mul_zero, zero_pow (by decide : 2 ≠ 0)]
      · simp
    have hg : (∑ j, planarPartial (χ j) e x ^ 2) = planarPartial (χ i) e x ^ 2 := by
      apply Finset.sum_eq_single i
      · intro j _ hji
        rw [hz j hji, zero_pow (by decide : 2 ≠ 0)]
      · simp
    rw [hs, hc, hg]
    calc
      _ = (Real.sin (χ i x) ^ 2 + Real.cos (χ i x) ^ 2) * planarPartial (χ i) e x ^ 2 := by ring
      _ = _ := by rw [Real.sin_sq_add_cos_sq, one_mul]
  · have hz (i : ι) : planarPartial (χ i) e x = 0 := by
      have hi : x ∉ tsupport (χ i) := fun hi => hx ⟨i, hi⟩
      simp only [planarPartial, fderiv_of_notMem_tsupport ℝ hi, zero_apply]
    simp only [hz, mul_zero, Finset.sum_const_zero, neg_zero, ne_eq,
      OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero]

theorem planarTrigPartition_gradient_bound {ι : Type*} [Fintype ι]
    (χ : ι → PlanarPosition → ℝ) (hχ : ∀ i, ContDiff ℝ 1 (χ i))
    (hdisj : ∀ i j, i ≠ j → Disjoint (tsupport (χ i)) (tsupport (χ j)))
    {G : ℝ} (hG : 0 ≤ G) (e : PlanarPosition)
    (hbound : ∀ i x, |planarPartial (χ i) e x| ≤ G) (x : PlanarPosition) :
    (∑ i, planarPartial (planarTrigPartition χ i) e x ^ 2) ≤ G ^ 2 := by
  classical
  rw [planarTrigPartition_gradient_square χ hχ hdisj]
  by_cases hx : ∃ i, x ∈ tsupport (χ i)
  · obtain ⟨i, hi⟩ := hx
    rw [Finset.sum_eq_single i]
    · simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hG).mpr (hbound i x)
    · intro j _ hji
      rw [(disjoint_cutoff_vanish χ hdisj hi hji e).2, zero_pow (by decide : 2 ≠ 0)]
    · simp
  · have hz (i : ι) : planarPartial (χ i) e x = 0 := by
      have hi : x ∉ tsupport (χ i) := fun hi => hx ⟨i, hi⟩
      simp only [planarPartial, fderiv_of_notMem_tsupport ℝ hi, zero_apply]
    simp only [hz, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, Finset.sum_const_zero]
    exact sq_nonneg G

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_PlanarSiteCutoffs
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual scaled cutoffs for separated planar sites. Their square
partition has a localization cost of order D⁻² independent of site count. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb
open PlanarSobolev
open RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean

theorem planarSiteAngle_C1 (D : ℝ) (u : PlanarPosition) :
    ContDiff ℝ 1 (planarSiteAngle D u) :=
  contDiff_const.mul ((cutoffBump_smooth.of_le (by first | simp | exact_mod_cast le_top)).comp
    ((contDiff_id.sub contDiff_const).const_smul (6 / D)))

theorem planarSiteAngle_support {D : ℝ} (hD : 0 < D) (u : PlanarPosition) :
    tsupport (planarSiteAngle D u) ⊆ Metric.closedBall u (D / 3) := by
  apply closure_minimal ?_ Metric.isClosed_closedBall
  intro x hx
  change planarSiteAngle D u x ≠ 0 at hx
  change dist x u ≤ D / 3
  by_contra! hn
  have hb : cutoffBump ((6 / D) • (x - u)) = 0 := by
    apply cutoffBump.zero_of_le_dist
    change 2 ≤ dist ((6 / D) • (x - u)) 0
    rw [dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos (by norm_num) hD)]
    rw [div_mul_eq_mul_div, le_div_iff₀ hD]
    rw [dist_eq_norm] at hn
    linarith
  exact hx (by simp only [planarSiteAngle, hb, mul_zero])

theorem planarSiteAngle_disjoint {ι : Type*} {D : ℝ} (hD : 0 < D)
    (u : ι → PlanarPosition) (hsep : ∀ i j, i ≠ j → D ≤ ‖u i - u j‖)
    (i j : ι) (hij : i ≠ j) :
    Disjoint (tsupport (planarSiteAngle D (u i))) (tsupport (planarSiteAngle D (u j))) := by
  apply Set.disjoint_left.mpr
  intro x hi hj
  have hi' := planarSiteAngle_support hD (u i) hi
  have hj' := planarSiteAngle_support hD (u j) hj
  simp only [Metric.mem_closedBall, dist_eq_norm] at hi' hj'
  have ht : ‖u i - u j‖ ≤ ‖x - u i‖ + ‖x - u j‖ := by
    simpa only [dist_eq_norm, norm_sub_rev (u i) x] using dist_triangle (u i) x (u j)
  have hs := hsep i j hij
  linarith

theorem planarSiteAngle_inner {D : ℝ} (hD : 0 < D) (u x : PlanarPosition)
    (hx : ‖x-u‖ ≤ D / 8) : planarSiteAngle D u x = Real.pi / 2 := by
  have hb : cutoffBump ((6 / D) • (x - u)) = 1 := by
    apply cutoffBump.one_of_mem_closedBall
    change dist ((6 / D) • (x - u)) 0 ≤ 1
    rw [dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos (by norm_num) hD)]
    rw [div_mul_eq_mul_div, div_le_iff₀ hD]
    linarith
  simp only [planarSiteAngle, hb, mul_one]

theorem planarSitePartition_C1 {ι : Type*} [Fintype ι] (D : ℝ)
    (u : ι → PlanarPosition) (i : Option ι) : ContDiff ℝ 1 (planarSitePartition D u i) :=
  planarTrigPartition_C1 _ (fun i => planarSiteAngle_C1 D (u i)) i

theorem planarSitePartition_square_sum {ι : Type*} [Fintype ι] {D : ℝ} (hD : 0 < D)
    (u : ι → PlanarPosition) (hsep : ∀ i j, i ≠ j → D ≤ ‖u i-u j‖) (x : PlanarPosition) :
    ∑ i, planarSitePartition D u i x ^ 2 = 1 :=
  planarTrigPartition_square_sum _ (planarSiteAngle_disjoint hD u hsep) x

theorem planarSiteAngle_partial (D : ℝ) (u e x : PlanarPosition) :
    planarPartial (planarSiteAngle D u) e x =
      (Real.pi / 2 * (6 / D)) * planarPartial cutoffBump e ((6 / D) • (x-u)) := by
  change fderiv ℝ (fun y => Real.pi / 2 * cutoffBump ((6 / D) • (y-u))) x e =
    (Real.pi / 2 * (6 / D)) * fderiv ℝ cutoffBump ((6 / D) • (x-u)) e
  have hm := ((hasFDerivAt_id (𝕜 := ℝ) x).sub (hasFDerivAt_const u x)).const_smul (6 / D)
  have hb := (cutoffBump_smooth.differentiable (by simp) ((6 / D) • (x-u))).hasFDerivAt.comp x hm
  have ha := hb.const_mul (Real.pi / 2)
  have he := congrArg (fun L : PlanarPosition →L[ℝ] ℝ => L e) ha.fderiv
  simpa only [Pi.sub_def, Pi.mul_def, Pi.smul_def,
    id_eq, Function.comp_def,
    ContinuousLinearMap.comp_apply, smul_apply, smul_eq_mul, sub_zero,
    ContinuousLinearMap.id_apply, zero_apply, map_smul, mul_assoc] using he

theorem planarSiteDerivativeBound_nonnegative {D : ℝ} (hD : 0 < D) :
    0 ≤ planarSiteDerivativeBound D := by
  unfold planarSiteDerivativeBound
  exact mul_nonneg (mul_nonneg (div_nonneg Real.pi_pos.le (by norm_num))
    (div_pos (by norm_num) hD).le) cutoffGradBound_nonnegative

theorem planarSiteAngle_partial_bound {D : ℝ} (hD : 0 < D)
    (u x : PlanarPosition) (a : Fin 2) :
    |planarPartial (planarSiteAngle D u) (planarAxis a) x| ≤ planarSiteDerivativeBound D := by
  have hc : 0 ≤ Real.pi / 2 * (6 / D) :=
    mul_nonneg (div_nonneg Real.pi_pos.le (by norm_num)) (div_pos (by norm_num) hD).le
  rw [planarSiteAngle_partial, abs_mul, abs_of_nonneg hc]
  apply mul_le_mul_of_nonneg_left ?_ hc
  rw [← grad_coordinate]
  exact (PiLp.norm_apply_le (grad cutoffBump ((6 / D) • (x-u))) a).trans (cutoffGradBound_spec _)

theorem planarSitePartition_direction_bound {ι : Type*} [Fintype ι] {D : ℝ} (hD : 0 < D)
    (u : ι → PlanarPosition) (hsep : ∀ i j, i ≠ j → D ≤ ‖u i-u j‖)
    (a : Fin 2) (x : PlanarPosition) :
    (∑ i, planarPartial (planarSitePartition D u i) (planarAxis a) x ^ 2) ≤
      planarSiteDerivativeBound D ^ 2 :=
  planarTrigPartition_gradient_bound _ (fun i => planarSiteAngle_C1 D (u i))
    (planarSiteAngle_disjoint hD u hsep) (planarSiteDerivativeBound_nonnegative hD)
    (planarAxis a) (fun i x => planarSiteAngle_partial_bound hD (u i) x a) x

theorem planarSitePartition_gradient_bound {ι : Type*} [Fintype ι] {D : ℝ} (hD : 0 < D)
    (u : ι → PlanarPosition) (hsep : ∀ i j, i ≠ j → D ≤ ‖u i-u j‖) (x : PlanarPosition) :
    (∑ a : Fin 2, ∑ i, planarPartial (planarSitePartition D u i) (planarAxis a) x ^ 2) ≤
      2 * planarSiteDerivativeBound D ^ 2 := by
  rw [Fin.sum_univ_two]
  linarith [planarSitePartition_direction_bound hD u hsep 0 x,
    planarSitePartition_direction_bound hD u hsep 1 x]

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_PlanarIMSBounds
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Quantitative IMS lower bounds, attached to the actual separated-site
partition. The error constant depends on one fixed bump and D, not on the
number of sites. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb

theorem planar_localization_cost_integrable {ι : Type*} [Fintype ι]
    (θ : ι → PlanarPosition → ℝ) (hθ : ∀ i, ContDiff ℝ 1 (θ i))
    (u : PlanarPosition → ℝ) (hu : Continuous u) (hc : HasCompactSupport u)
    (e : PlanarPosition) :
    Integrable (fun x => (∑ i, planarPartial (θ i) e x ^ 2) * u x ^ 2) := by
  have hs : HasCompactSupport (fun x => u x ^ 2) :=
    hc.comp_left (g := fun t : ℝ => t ^ 2) (by norm_num)
  have hm : HasCompactSupport (fun x => (∑ i, planarPartial (θ i) e x ^ 2) * u x ^ 2) := hs.mul_left
  have hd : Continuous (fun x => ∑ i, planarPartial (θ i) e x ^ 2) :=
    continuous_finsetSum _ (fun i _ => (planarPartial_continuous (hθ i) e).pow 2)
  exact (hd.mul (hu.pow 2)).integrable_of_hasCompactSupport hm

theorem planar_IMS_cost_bound {ι : Type*} [Fintype ι]
    (θ : ι → PlanarPosition → ℝ) (hθ : ∀ i, ContDiff ℝ 1 (θ i))
    (u : PlanarPosition → ℝ) (hu : Continuous u) (hc : HasCompactSupport u)
    {C : ℝ} (hbound : ∀ x, (∑ a : Fin 2, ∑ i, planarPartial (θ i) (planarAxis a) x ^ 2) ≤ C) :
    (∑ a : Fin 2, ∫ x, (∑ i, planarPartial (θ i) (planarAxis a) x ^ 2) * u x ^ 2) ≤
      C * ∫ x, u x ^ 2 := by
  have hi (a : Fin 2) := planar_localization_cost_integrable θ hθ u hu hc (planarAxis a)
  have hs : Integrable (fun x => ∑ a : Fin 2,
      (∑ i, planarPartial (θ i) (planarAxis a) x ^ 2) * u x ^ 2) :=
    integrable_finsetSum _ (fun a _ => hi a)
  have hm : Integrable (fun x => C * u x ^ 2) :=
    planar_potential_test_integrable (fun _ => C) u continuous_const hu hc
  rw [← integral_finsetSum _ (fun a _ => hi a), ← integral_const_mul]
  apply integral_mono hs hm
  intro x
  dsimp only
  rw [← Finset.sum_mul]
  exact mul_le_mul_of_nonneg_right (hbound x) (sq_nonneg _)

theorem planar_IMS_lower {ι : Type*} [Fintype ι]
    (θ : ι → PlanarPosition → ℝ) (hθ : ∀ i, ContDiff ℝ 1 (θ i))
    (hpart : ∀ x, ∑ i, θ i x ^ 2 = 1)
    (W u : PlanarPosition → ℝ) (hW : Continuous W)
    (hu : ContDiff ℝ 1 u) (hc : HasCompactSupport u)
    {C : ℝ} (hbound : ∀ x, (∑ a : Fin 2, ∑ i, planarPartial (θ i) (planarAxis a) x ^ 2) ≤ C) :
    (∑ i, planarTestForm W (fun x => θ i x * u x)) - (C/2) * (∫ x, u x ^ 2) ≤
      planarTestForm W u := by
  have he := planar_IMS θ hθ hpart W u hW hu hc
  have hb := planar_IMS_cost_bound θ hθ u hu.continuous hc hbound
  linarith

/-- An actual multiwell localization estimate with fixed bump constant and
quadratic inverse-separation error. -/
theorem planarSitePartition_IMS_lower {ι : Type*} [Fintype ι] {D : ℝ} (hD : 0 < D)
    (u : ι → PlanarPosition) (hsep : ∀ i j, i ≠ j → D ≤ ‖u i-u j‖)
    (W f : PlanarPosition → ℝ) (hW : Continuous W)
    (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f) :
    (∑ i, planarTestForm W (fun x => planarSitePartition D u i x * f x)) -
      planarSiteDerivativeBound D ^ 2 * (∫ x, f x ^ 2) ≤ planarTestForm W f := by
  have h := planar_IMS_lower (planarSitePartition D u) (planarSitePartition_C1 D u)
    (planarSitePartition_square_sum hD u hsep) W f hW hf hc
    (planarSitePartition_gradient_bound hD u hsep)
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  ring

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_PlanarWellLocalization
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact localization of the actual sum of manufactured wells. Site
pieces see exactly their own well; the exterior piece sees zero potential. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb

theorem planarWellSum_continuous {ι : Type*} [Fintype ι] (u : ι → PlanarPosition) :
    Continuous (planarWellSum u) :=
  continuous_finsetSum _ (fun i _ => manufacturedPlanarWell_C7.continuous.comp
    (continuous_id.sub (continuous_const : Continuous (fun _ : PlanarPosition => u i))))

theorem manufacturedPlanarWell_zero_of_norm_ge_one {x : PlanarPosition} (hx : 1 ≤ ‖x‖) :
    manufacturedPlanarWell x = 0 := by
  simp only [manufacturedPlanarWell, planarForcing_zero_of_norm_ge_one hx, neg_zero, zero_div]

theorem planarSitePartition_exterior_inner {ι : Type*} [Fintype ι] {D : ℝ} (hD : 0 < D)
    (u : ι → PlanarPosition) (hsep : ∀ i j, i ≠ j → D ≤ ‖u i-u j‖)
    (i : ι) (x : PlanarPosition) (hx : ‖x-u i‖ ≤ D/8) :
    planarSitePartition D u none x = 0 := by
  have ha := planarSiteAngle_inner hD (u i) x hx
  have hs : x ∈ tsupport (planarSiteAngle D (u i)) := by
    apply subset_tsupport
    change planarSiteAngle D (u i) x ≠ 0
    rw [ha]
    exact div_ne_zero Real.pi_ne_zero (by norm_num)
  change planarTrigPartition (fun j => planarSiteAngle D (u j)) none x = 0
  rw [planarTrigPartition_exterior_at _ (planarSiteAngle_disjoint hD u hsep) hs,
    ha, Real.cos_pi_div_two]

theorem planarWellSum_site_product {ι : Type*} [Fintype ι] {D : ℝ} (hD : 8 ≤ D)
    (u : ι → PlanarPosition) (hsep : ∀ i j, i ≠ j → D ≤ ‖u i-u j‖)
    (i : ι) (x : PlanarPosition) :
    planarWellSum u x * planarSitePartition D u (some i) x =
      manufacturedPlanarWell (x-u i) * planarSitePartition D u (some i) x := by
  classical
  by_cases hz : planarSitePartition D u (some i) x = 0
  · rw [hz, mul_zero, mul_zero]
  have hangle : planarSiteAngle D (u i) x ≠ 0 := by
    intro ha
    exact hz (by simp only [planarSitePartition, planarTrigPartition, ha, Real.sin_zero])
  have hi := planarSiteAngle_support (by linarith : 0 < D) (u i) (subset_tsupport _ hangle)
  simp only [Metric.mem_closedBall, dist_eq_norm] at hi
  unfold planarWellSum
  rw [Finset.sum_mul, Finset.sum_eq_single i]
  · intro j _ hji
    have ht : ‖u i-u j‖ ≤ ‖x-u i‖ + ‖x-u j‖ := by
      simpa only [dist_eq_norm, norm_sub_rev (u i) x] using dist_triangle (u i) x (u j)
    have hs := hsep i j hji.symm
    rw [manufacturedPlanarWell_zero_of_norm_ge_one (by linarith : 1 ≤ ‖x-u j‖), zero_mul]
  · simp

theorem planarWellSum_exterior_product {ι : Type*} [Fintype ι] {D : ℝ} (hD : 8 ≤ D)
    (u : ι → PlanarPosition) (hsep : ∀ i j, i ≠ j → D ≤ ‖u i-u j‖)
    (x : PlanarPosition) : planarWellSum u x * planarSitePartition D u none x = 0 := by
  unfold planarWellSum
  rw [Finset.sum_mul]
  apply Finset.sum_eq_zero
  intro i _
  by_cases hi : 1 ≤ ‖x-u i‖
  · rw [manufacturedPlanarWell_zero_of_norm_ge_one hi, zero_mul]
  · have hx : ‖x-u i‖ ≤ D/8 := by push Not at hi; linarith
    rw [planarSitePartition_exterior_inner (by linarith : 0 < D) u hsep i x hx, mul_zero]

theorem planarTestForm_potential_product_congr (W V f : PlanarPosition → ℝ)
    (h : ∀ x, W x * f x = V x * f x) : planarTestForm W f = planarTestForm V f := by
  unfold planarTestForm
  congr 1
  apply integral_congr_ae
  filter_upwards [] with x
  simpa only [pow_two, ← mul_assoc] using congrArg (fun t : ℝ => t * f x) (h x)

theorem planarWellSum_localized_forms {ι : Type*} [Fintype ι] {D : ℝ} (hD : 8 ≤ D)
    (u : ι → PlanarPosition) (hsep : ∀ i j, i ≠ j → D ≤ ‖u i-u j‖)
    (f : PlanarPosition → ℝ) :
    (∑ i, planarTestForm (planarWellSum u) (fun x => planarSitePartition D u i x * f x)) =
      planarTestForm (fun _ => 0) (fun x => planarSitePartition D u none x * f x) +
        ∑ i, planarTestForm (fun x => manufacturedPlanarWell (x-u i))
          (fun x => planarSitePartition D u (some i) x * f x) := by
  rw [Fintype.sum_option]
  apply congrArg₂ (· + ·)
  · apply planarTestForm_potential_product_congr
    intro x
    rw [← mul_assoc, planarWellSum_exterior_product hD u hsep, zero_mul, zero_mul]
  · apply Finset.sum_congr rfl
    intro i _
    apply planarTestForm_potential_product_congr
    intro x
    rw [← mul_assoc, ← mul_assoc, planarWellSum_site_product hD u hsep]

theorem planarWellSum_localization_lower {ι : Type*} [Fintype ι] {D : ℝ} (hD : 8 ≤ D)
    (u : ι → PlanarPosition) (hsep : ∀ i j, i ≠ j → D ≤ ‖u i-u j‖)
    (f : PlanarPosition → ℝ) (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f) :
    planarTestForm (fun _ => 0) (fun x => planarSitePartition D u none x * f x) +
        (∑ i, planarTestForm (fun x => manufacturedPlanarWell (x-u i))
          (fun x => planarSitePartition D u (some i) x * f x)) -
        planarSiteDerivativeBound D ^ 2 * (∫ x, f x ^ 2) ≤ planarTestForm (planarWellSum u) f := by
  have h := planarSitePartition_IMS_lower (by linarith : 0 < D) u hsep
    (planarWellSum u) f (planarWellSum_continuous u) hf hc
  rwa [planarWellSum_localized_forms hD u hsep f] at h

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_ExplicitVerticalCutoff
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! An explicit smooth transverse cutoff. Its formula uses only the fixed
smooth transition function, so rational approximation can use the actual
exponential formula instead of a classically selected bump function. -/

noncomputable section
namespace ContinuumCoulomb

namespace verticalCutoffBump

theorem nonneg {z : ℝ} : 0 ≤ verticalCutoffBump z :=
  Real.smoothTransition.nonneg _

theorem le_one {z : ℝ} : verticalCutoffBump z ≤ 1 :=
  Real.smoothTransition.le_one _

theorem one_of_mem_closedBall {z : ℝ} (hz : z ∈ Metric.closedBall (0 : ℝ) 1) :
    verticalCutoffBump z = 1 := by
  apply Real.smoothTransition.one_of_one_le
  have hab : |z| ≤ 1 := by simpa [Metric.mem_closedBall, Real.dist_eq] using hz
  have hsq := (sq_le_sq₀ (abs_nonneg z) (by norm_num : (0:ℝ) ≤ 1)).mpr hab
  rw [sq_abs] at hsq
  linarith

end verticalCutoffBump
end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_VerticalCappedForm
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual capped transverse oscillator and its two-part IMS formula.
The cutoff is one on the inner half-slab and zero beyond the slab. -/

noncomputable section
open MeasureTheory
open scoped ContDiff
namespace ContinuumCoulomb

theorem verticalCutoffAngle_smooth (S : ℝ) : ContDiff ℝ ∞ (verticalCutoffAngle S) :=
  contDiff_const.mul (verticalCutoffBump.contDiff.comp (contDiff_const.mul contDiff_id))

theorem verticalInnerCutoff_smooth (S : ℝ) : ContDiff ℝ ∞ (verticalInnerCutoff S) :=
  (verticalCutoffAngle_smooth S).sin

theorem verticalOuterCutoff_smooth (S : ℝ) : ContDiff ℝ ∞ (verticalOuterCutoff S) :=
  (verticalCutoffAngle_smooth S).cos

theorem verticalCutoff_partition (S z : ℝ) :
    verticalInnerCutoff S z^2 + verticalOuterCutoff S z^2 = 1 := Real.sin_sq_add_cos_sq _

theorem verticalCutoff_inner {S : ℝ} (hS : 0 < S) {z : ℝ} (hz : |z| ≤ S/2) :
    verticalInnerCutoff S z = 1 ∧ verticalOuterCutoff S z = 0 := by
  have hb : verticalCutoffBump ((2/S)*z) = 1 := by
    apply verticalCutoffBump.one_of_mem_closedBall
    change dist ((2/S)*z) 0 ≤ 1
    rw [dist_zero_right, Real.norm_eq_abs, abs_mul, abs_of_pos (div_pos (by norm_num) hS)]
    have hm := mul_le_mul_of_nonneg_left hz (div_pos (by norm_num : (0:ℝ)<2) hS).le
    have he : (2/S)*(S/2) = (1:ℝ) := by field_simp
    exact hm.trans_eq he
  simp [verticalInnerCutoff, verticalOuterCutoff, verticalCutoffAngle, hb]

theorem verticalCutoff_outer {S : ℝ} (hS : 0 < S) {z : ℝ} (hz : S ≤ |z|) :
    verticalInnerCutoff S z = 0 ∧ verticalOuterCutoff S z = 1 := by
  have hb : verticalCutoffBump ((2/S)*z) = 0 := by
    apply verticalCutoffBump.zero_of_le_dist
    rw [dist_zero_right, Real.norm_eq_abs, abs_mul, abs_of_pos (div_pos (by norm_num) hS)]
    have hm := mul_le_mul_of_nonneg_left hz (div_pos (by norm_num : (0:ℝ)<2) hS).le
    have he : (2/S)*S = (2:ℝ) := by field_simp
    exact he.symm.le.trans hm
  simp [verticalInnerCutoff, verticalOuterCutoff, verticalCutoffAngle, hb]

theorem vertical_deriv_square_integrable (u : ℝ → ℝ)
    (hu : ContDiff ℝ 1 u) (hc : HasCompactSupport u) : Integrable (fun z => deriv u z^2) := by
  have hd : Continuous (deriv u) := hu.continuous_deriv (by norm_num)
  have hdc : HasCompactSupport (deriv u) := hc.deriv
  have hsq : HasCompactSupport (fun z => deriv u z^2) :=
    hdc.comp_left (g := fun t : ℝ => t^2) (by norm_num)
  exact (hd.pow 2).integrable_of_hasCompactSupport hsq

theorem vertical_product_integrable (V u : ℝ → ℝ) (hV : Continuous V)
    (hu : Continuous u) (hc : HasCompactSupport u) : Integrable (fun z => V z*u z^2) := by
  have huc : HasCompactSupport (fun z => u z^2) :=
    hc.comp_left (g := fun t : ℝ => t^2) (by norm_num)
  have hprod : HasCompactSupport (fun z => V z * u z^2) := huc.mul_left
  exact (hV.mul (hu.pow 2)).integrable_of_hasCompactSupport hprod

theorem verticalCutoffAngle_deriv (S z : ℝ) :
    deriv (verticalCutoffAngle S) z =
      (Real.pi/2 * (2/S)) * deriv (verticalCutoffBump : ℝ → ℝ) ((2/S)*z) := by
  have hs : ContDiff ℝ 1 (verticalCutoffBump : ℝ → ℝ) := verticalCutoffBump.contDiff
  have hb := (hs.differentiable (by norm_num) ((2/S)*z)).hasDerivAt
  have h := (hb.comp z ((hasDerivAt_id z).const_mul (2/S))).const_mul (Real.pi/2)
  change HasDerivAt (verticalCutoffAngle S) _ z at h
  rw [h.deriv]
  ring

theorem verticalCutoffAngle_deriv_bound {S : ℝ} (hS : 0 < S) (z : ℝ) :
    |deriv (verticalCutoffAngle S) z| ≤ verticalCutoffDerivativeBound S := by
  have hc : 0 ≤ Real.pi/2 * (2/S) := by positivity
  rw [verticalCutoffAngle_deriv, abs_mul, abs_of_nonneg hc]
  exact mul_le_mul_of_nonneg_left
    (Classical.choose_spec verticalCutoffBump_deriv_bounded ((2/S)*z)) hc

theorem verticalCutoff_deriv_identity (S : ℝ) (u : ℝ → ℝ)
    (hu : ContDiff ℝ 1 u) (z : ℝ) :
    deriv (fun x => verticalInnerCutoff S x*u x) z^2 +
      deriv (fun x => verticalOuterCutoff S x*u x) z^2 =
      deriv u z^2 + deriv (verticalCutoffAngle S) z^2*u z^2 := by
  have ha := (verticalCutoffAngle_smooth S).differentiable (by simp) z
  have hi := ha.hasDerivAt.sin
  have ho := ha.hasDerivAt.cos
  have hu' := (hu.differentiable (by norm_num) z).hasDerivAt
  have hdi : deriv (fun x => verticalInnerCutoff S x*u x) z =
      Real.cos (verticalCutoffAngle S z) * deriv (verticalCutoffAngle S) z * u z +
        Real.sin (verticalCutoffAngle S z) * deriv u z := by
    simpa only [verticalInnerCutoff] using (hi.fun_mul hu').deriv
  have hdo : deriv (fun x => verticalOuterCutoff S x*u x) z =
      -(Real.sin (verticalCutoffAngle S z) * deriv (verticalCutoffAngle S) z) * u z +
        Real.cos (verticalCutoffAngle S z) * deriv u z := by
    simpa only [verticalOuterCutoff, neg_mul] using (ho.fun_mul hu').deriv
  rw [hdi, hdo]
  linear_combination (deriv u z^2 + deriv (verticalCutoffAngle S) z^2*u z^2) *
    Real.sin_sq_add_cos_sq (verticalCutoffAngle S z)

/-- Exact IMS identity on the actual one-dimensional capped form. -/
theorem verticalCappedForm_IMS (freq S : ℝ) (u : ℝ → ℝ)
    (hu : ContDiff ℝ 1 u) (hc : HasCompactSupport u) :
    verticalCappedForm freq S (fun z => verticalInnerCutoff S z*u z) +
      verticalCappedForm freq S (fun z => verticalOuterCutoff S z*u z) =
      verticalCappedForm freq S u + (1/2:ℝ)*∫ z, deriv (verticalCutoffAngle S) z^2*u z^2 := by
  have hi : ContDiff ℝ 1 (verticalInnerCutoff S) := (verticalInnerCutoff_smooth S).of_le (by first | simp | exact_mod_cast le_top)
  have ho : ContDiff ℝ 1 (verticalOuterCutoff S) := (verticalOuterCutoff_smooth S).of_le (by first | simp | exact_mod_cast le_top)
  have ha : Continuous (fun z => deriv (verticalCutoffAngle S) z^2) :=
    ((verticalCutoffAngle_smooth S).continuous_deriv (by simp)).pow 2
  have hV : Continuous (verticalCapPotential freq S) := by unfold verticalCapPotential; fun_prop
  have hd : (∫ z, deriv (fun x => verticalInnerCutoff S x*u x) z^2) +
      (∫ z, deriv (fun x => verticalOuterCutoff S x*u x) z^2) =
      (∫ z, deriv u z^2) + ∫ z, deriv (verticalCutoffAngle S) z^2*u z^2 := by
    rw [← integral_add (vertical_deriv_square_integrable _ (hi.mul hu) hc.mul_left)
      (vertical_deriv_square_integrable _ (ho.mul hu) hc.mul_left),
      ← integral_add (vertical_deriv_square_integrable u hu hc)
      (vertical_product_integrable _ u ha hu.continuous hc)]
    exact integral_congr_ae (Filter.Eventually.of_forall (verticalCutoff_deriv_identity S u hu))
  have hp : (∫ z, verticalCapPotential freq S z*(verticalInnerCutoff S z*u z)^2) +
      (∫ z, verticalCapPotential freq S z*(verticalOuterCutoff S z*u z)^2) =
      ∫ z, verticalCapPotential freq S z*u z^2 := by
    rw [← integral_add
      (vertical_product_integrable _ _ hV (hi.mul hu).continuous hc.mul_left)
      (vertical_product_integrable _ _ hV (ho.mul hu).continuous hc.mul_left)]
    apply integral_congr_ae
    filter_upwards [] with z
    linear_combination (verticalCapPotential freq S z*u z^2) * verticalCutoff_partition S z
  unfold verticalCappedForm
  linarith

/-- On the supported inner piece the capped potential is exactly harmonic. -/
theorem verticalCappedForm_inner {S : ℝ} (hS : 0 < S) (freq : ℝ) (u : ℝ → ℝ) :
    verticalCappedForm freq S (fun z => verticalInnerCutoff S z*u z) =
      verticalForm freq (fun z => verticalInnerCutoff S z*u z) := by
  unfold verticalCappedForm verticalForm
  congr 1
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with z
  by_cases hz : |z| ≤ S
  · have hs : z^2 ≤ S^2 := by
      nlinarith [sq_abs z, (sq_le_sq₀ (abs_nonneg z) hS.le).mpr hz]
    simp only [verticalCapPotential, min_eq_left hs]
    ring
  · rw [(verticalCutoff_outer hS (le_of_not_ge hz)).1]
    simp

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_ManufacturedWellField
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual compact three-dimensional well field in the unit-charge
construction. Its coefficients are Coulomb counterterms. The cutoff only weakens the attractive uncorrected wells. -/

noncomputable section
open scoped BigOperators ContDiff
namespace ContinuumCoulomb

theorem slabWellCutoff_bounds (S z : ℝ) :
    0 ≤ slabWellCutoff S z ∧ slabWellCutoff S z ≤ 1 :=
  ⟨verticalCutoffBump.nonneg, verticalCutoffBump.le_one⟩

theorem countertermWellSum_nonpositive (freq : ℝ) {scale : ℝ} (hscale : 0 ≤ scale)
    {m : ℕ} (u : Fin m → PlanarPosition) (r : PlanarPosition) :
    countertermWellSum freq scale u r ≤ 0 := by
  apply Finset.sum_nonpos
  intro i _
  exact mul_nonpos_of_nonneg_of_nonpos
    (add_nonneg zero_le_one (div_nonneg (localizedCounterterm_nonnegative freq u i) hscale))
    (manufacturedPlanarWell_nonpositive _)

theorem positionSplitCoordinates_fst_zero (x : Position) :
    (positionSplitCoordinates x).1 0 = x 0 := rfl

theorem positionSplitCoordinates_fst_one (x : Position) :
    (positionSplitCoordinates x).1 1 = x 1 := rfl

theorem positionSplitCoordinates_snd (x : Position) :
    (positionSplitCoordinates x).2 = x 2 := rfl

private theorem well_zero_away_from_near_site {m : ℕ} (u : Fin m → PlanarPosition)
    (hsep : ∀ i j, i ≠ j → 2 ≤ ‖u i-u j‖) (r : PlanarPosition)
    (i : Fin m) (hi : ‖r-u i‖ < 1) (j : Fin m) (hji : j ≠ i) :
    manufacturedPlanarWell (r-u j) = 0 := by
  apply manufacturedPlanarWell_zero_of_norm_ge_one
  have ht : ‖u i-u j‖ ≤ ‖r-u i‖ + ‖r-u j‖ := by
    simpa only [dist_eq_norm, norm_sub_rev (u i) r] using dist_triangle (u i) r (u j)
  linarith [hsep i j hji.symm]

/-- Disjoint planar supports prevent the counterterm perturbation from
growing with the number of sites. -/
theorem countertermWellSum_lower (freq scale : ℝ) {m : ℕ}
    (u : Fin m → PlanarPosition) (hsep : ∀ i j, i ≠ j → 2 ≤ ‖u i-u j‖)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hcoeff : ∀ i, 0 ≤ localizedCounterterm freq u i / scale ∧
      localizedCounterterm freq u i / scale ≤ δ) (r : PlanarPosition) :
    planarWellSum u r - δ*PlanarSobolev.wellBound ≤ countertermWellSum freq scale u r := by
  classical
  by_cases hnear : ∃ i, ‖r-u i‖ < 1
  · obtain ⟨i, hi⟩ := hnear
    have hz := well_zero_away_from_near_site u hsep r i hi
    have hsum : planarWellSum u r = manufacturedPlanarWell (r-u i) := by
      unfold planarWellSum
      exact Finset.sum_eq_single i (fun j _ hji => hz j hji) (by simp)
    have hsum' : countertermWellSum freq scale u r =
        (1+localizedCounterterm freq u i/scale)*manufacturedPlanarWell (r-u i) := by
      unfold countertermWellSum
      exact Finset.sum_eq_single i (fun j _ hji => by rw [hz j hji, mul_zero]) (by simp)
    rw [hsum, hsum']
    have hw : -PlanarSobolev.wellBound ≤ manufacturedPlanarWell (r-u i) := by
      exact (abs_le.mp (by simpa only [Real.norm_eq_abs] using
        PlanarSobolev.wellBound_spec (r-u i))).1
    have h1 := mul_le_mul_of_nonneg_left hw (hcoeff i).1
    have h2 := mul_le_mul_of_nonneg_right (hcoeff i).2 PlanarSobolev.wellBound_nonnegative
    nlinarith only [h1, h2]
  · have hz (i : Fin m) : manufacturedPlanarWell (r-u i) = 0 :=
      manufacturedPlanarWell_zero_of_norm_ge_one (le_of_not_gt (fun hi => hnear ⟨i, hi⟩))
    simp only [planarWellSum, countertermWellSum, hz, mul_zero, Finset.sum_const_zero]
    linarith [mul_nonneg hδ PlanarSobolev.wellBound_nonnegative]

/-- Global lower comparison to the separable uncapped multiwell field. -/
theorem manufacturedWellField_lower (freq : ℝ) {scale : ℝ} (hscale : 0 ≤ scale)
    (S : ℝ) {m : ℕ} (u : Fin m → PlanarPosition)
    (hsep : ∀ i j, i ≠ j → 2 ≤ ‖u i-u j‖) {δ : ℝ} (hδ : 0 ≤ δ)
    (hcoeff : ∀ i, 0 ≤ localizedCounterterm freq u i / scale ∧
      localizedCounterterm freq u i / scale ≤ δ) (x : Position) :
    planarWellSum u (positionSplitCoordinates x).1 - δ*PlanarSobolev.wellBound ≤
      manufacturedWellField freq scale S u x := by
  apply (countertermWellSum_lower freq scale u hsep hδ hcoeff _).trans
  exact le_mul_of_le_one_left (countertermWellSum_nonpositive freq hscale u _)
    (slabWellCutoff_bounds S _).2

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_PlanarCutoffTail
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual site cutoff changes its normalized ground mode by an
exponentially small L2 vector. This controls the rank-one terms in IMS. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

theorem planar_l2_pair_sq_le (f g : PlanarPosition → ℝ) (hf : MemLp f 2) (hg : MemLp g 2) :
    (∫ x, f x * g x)^2 ≤ (∫ x, f x^2) * (∫ x, g x^2) := by
  have hpair (a b : PlanarPosition → ℝ) (ha : MemLp a 2) (hb : MemLp b 2) :
      inner ℝ (ha.toLp a) (hb.toLp b) = ∫ x, a x * b x := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [ha.coeFn_toLp, hb.coeFn_toLp] with x hx hy
    rw [hx, hy, RCLike.inner_apply, conj_trivial]
    ring
  have h := real_inner_mul_inner_self_le (hf.toLp f) (hg.toLp g)
  rw [hpair f g hf hg, hpair f f hf hf, hpair g g hg hg] at h
  simpa only [pow_two] using h

theorem planarSiteCutoff_deviation_bound (D : ℝ) (u x : PlanarPosition) :
    |Real.sin (planarSiteAngle D u x) - 1| ≤ 2 := by
  have h := abs_sub (Real.sin (planarSiteAngle D u x)) (1 : ℝ)
  have hs := Real.abs_sin_le_one (planarSiteAngle D u x)
  norm_num only [abs_one] at h
  linarith

theorem planarSiteCutoffError_memLp (D : ℝ) (u : PlanarPosition) :
    MemLp (planarSiteCutoffError D u) 2 := by
  have hm := normalizedPlanarMode_memLp.comp_measurePreserving (measurePreserving_sub_right volume u)
  apply hm.of_le_mul (c := 2)
    ((((planarSiteAngle_C1 D u).sin.continuous.sub continuous_const).mul
      (normalizedPlanarMode_C7.continuous.comp (continuous_id.sub continuous_const))).aestronglyMeasurable)
  filter_upwards [] with x
  change ‖(Real.sin (planarSiteAngle D u x) - 1) * normalizedPlanarMode (x-u)‖ ≤ _
  rw [norm_mul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right (planarSiteCutoff_deviation_bound D u x) (norm_nonneg _)

theorem planarSiteCutoffError_square_bound {D : ℝ} (hD : 0 < D) (u x : PlanarPosition) :
    planarSiteCutoffError D u x ^ 2 ≤
      (4 * normalizedPlanarExponentialConstant (19/20)^2 * Real.exp (-(19/20 : ℝ) * (D/8))) *
        Real.exp (-(19/20 : ℝ) * ‖x-u‖) := by
  by_cases hx : ‖x-u‖ ≤ D/8
  · rw [planarSiteCutoffError, planarSiteAngle_inner hD u x hx, Real.sin_pi_div_two,
      sub_self, zero_mul, zero_pow (by decide : 2 ≠ 0)]
    positivity
  · have hr : D/8 ≤ ‖x-u‖ := (le_of_not_ge hx)
    have hdev : (Real.sin (planarSiteAngle D u x) - 1)^2 ≤ (4 : ℝ) := by
      have h := planarSiteCutoff_deviation_bound D u x
      have hs := (sq_le_sq₀ (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)).mpr h
      simpa only [sq_abs, show (2 : ℝ)^2 = 4 by norm_num] using hs
    have hmode := pow_le_pow_left₀ (normalizedPlanarMode_positive (x-u)).le
      (normalizedPlanarMode_exponential_envelope (by norm_num : (0 : ℝ) ≤ 19/20)
        (by norm_num : (19/20 : ℝ) < 1) (x-u)) 2
    have he : Real.exp (-(19/20 : ℝ) * ‖x-u‖)^2 ≤
        Real.exp (-(19/20 : ℝ) * (D/8)) * Real.exp (-(19/20 : ℝ) * ‖x-u‖) := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]
      apply Real.exp_le_exp.mpr
      norm_num only [Nat.cast_ofNat]
      linarith
    rw [mul_pow] at hmode
    have hmode' := hmode.trans (mul_le_mul_of_nonneg_left he
      (sq_nonneg (normalizedPlanarExponentialConstant (19/20))))
    unfold planarSiteCutoffError
    rw [mul_pow]
    calc
      _ ≤ 4 * (normalizedPlanarExponentialConstant (19/20)^2 *
          (Real.exp (-(19/20 : ℝ) * (D/8)) * Real.exp (-(19/20 : ℝ) * ‖x-u‖))) :=
        mul_le_mul hdev hmode' (sq_nonneg _) (by norm_num)
      _ = _ := by ring

theorem planarSiteCutoffError_integral_bound {D : ℝ} (hD : 0 < D) (u : PlanarPosition) :
    (∫ x, planarSiteCutoffError D u x ^ 2) ≤
      planarSiteTailConstant * Real.exp (-(19/20 : ℝ) * (D/8)) := by
  have hi : Integrable (fun x => planarSiteCutoffError D u x ^ 2) :=
    (memLp_two_iff_integrable_sq (planarSiteCutoffError_memLp D u).aestronglyMeasurable).mp
      (planarSiteCutoffError_memLp D u)
  have he := ((planar_exp_norm_integrable (by norm_num : (0 : ℝ) < 19/20)).comp_sub_right u).const_mul
    (4 * normalizedPlanarExponentialConstant (19/20)^2 * Real.exp (-(19/20 : ℝ) * (D/8)))
  have h := integral_mono hi he (planarSiteCutoffError_square_bound hD u)
  rw [integral_const_mul, integral_sub_right_eq_self
    (fun r : PlanarPosition => Real.exp (-(19/20 : ℝ) * ‖r‖)) u] at h
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  unfold planarSiteTailConstant
  ring

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_PlanarModeEnergy
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual manufactured planar mode attains energy `-1/2`.
The integration by parts uses its proved square-integrable first and second
derivatives, rather than imposing an eigenvalue or normalization hypothesis. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb

theorem planarResolventMode_partial_memLp (e : PlanarPosition) :
    MemLp (planarPartial planarResolventMode e) 2 :=
  (memLp_two_iff_integrable_sq
    (planarPartial_continuous (planarResolventMode_C7.of_le (by norm_num)) e).aestronglyMeasurable).mpr
      (planarResolventMode_partial_square_integrable e)

theorem planarResolventMode_second_memLp (e : PlanarPosition) :
    MemLp (planarPartial (planarPartial planarResolventMode e) e) 2 :=
  (memLp_two_iff_integrable_sq
    (planarPartial_continuous (planarPartial_C1 (planarResolventMode_C7.of_le (by norm_num)) e)
      e).aestronglyMeasurable).mpr (planarResolventMode_partial_partial_square_integrable e e)

theorem planarResolventMode_energy_ibp (e : PlanarPosition) :
    (∫ x, planarResolventMode x * planarPartial (planarPartial planarResolventMode e) e x) =
      -(∫ x, planarPartial planarResolventMode e x ^ 2) := by
  have hi := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (planarResolventMode_partial_memLp e |>.integrable_mul (planarResolventMode_partial_memLp e))
    (planarResolventMode_memLp.integrable_mul (planarResolventMode_second_memLp e))
    (planarResolventMode_memLp.integrable_mul (planarResolventMode_partial_memLp e))
    (fun x _ => (planarResolventMode_C7.differentiable (by norm_num)) x)
    (fun x _ => (planarPartial_C1 (planarResolventMode_C7.of_le (by norm_num)) e).differentiable
      (by norm_num) x)
  simpa only [planarPartial, pow_two] using hi

theorem planarResolventMode_energy :
    planarTestForm manufacturedPlanarWell planarResolventMode =
      -(1 / 2 : ℝ) * ∫ x, planarResolventMode x ^ 2 := by
  have hi (a : Fin 2) : Integrable (fun x => planarResolventMode x *
      planarPartial (planarPartial planarResolventMode (planarAxis a)) (planarAxis a) x) :=
    planarResolventMode_memLp.integrable_mul (planarResolventMode_second_memLp (planarAxis a))
  have hsum : (∫ x, planarResolventMode x * planarLaplacian planarResolventMode x) =
      -(∑ a : Fin 2, ∫ x, planarPartial planarResolventMode (planarAxis a) x ^ 2) := by
    simp only [planarLaplacian, Finset.mul_sum]
    rw [integral_finsetSum Finset.univ (fun a _ => hi a)]
    simp only [planarResolventMode_energy_ibp, Finset.sum_neg_distrib]
  have hpot : Integrable (fun x => manufacturedPlanarWell x * planarResolventMode x ^ 2) :=
    (manufacturedPlanarWell_C7.continuous.mul (planarResolventMode_C7.continuous.pow 2)).integrable_of_hasCompactSupport
      manufacturedPlanarWell_hasCompactSupport.mul_right
  have heq : (∫ x, planarResolventMode x * planarLaplacian planarResolventMode x) =
      2 * (∫ x, manufacturedPlanarWell x * planarResolventMode x ^ 2) +
        ∫ x, planarResolventMode x ^ 2 := by
    simp_rw [manufacturedPlanarWell_eigen_equation]
    rw [show (fun x => planarResolventMode x * ((2 * manufacturedPlanarWell x + 1) * planarResolventMode x)) =
      (fun x => 2 * (manufacturedPlanarWell x * planarResolventMode x ^ 2) + planarResolventMode x ^ 2)
      from by funext x; ring]
    rw [integral_add (hpot.const_mul 2) planarResolventMode_square_integrable, integral_const_mul]
  unfold planarTestForm
  linarith

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_PlanarWellBottom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact variational bottom of the manufactured planar well on its
closed Sobolev graph. This is an analytic component of the continuum
construction; it does not assert the hardness reduction. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb
namespace PlanarSobolev
open RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean

attribute [local instance] OAI.ContinuumCoulomb.PlanarSobolev.instMeasurableSpacePlanarPosition_2
attribute [local instance] OAI.ContinuumCoulomb.PlanarSobolev.instBorelSpacePlanarPosition_2
attribute [local instance] OAI.ContinuumCoulomb.PlanarSobolev.instMeasureSpacePlanarPosition_2
theorem mode_mass : ‖mode.val.1‖ ^ 2 = originalIntegral (fun x => planarResolventMode x ^ 2) := by
  rw [← planar_integral_change_borel (borel PlanarPosition) ⟨rfl⟩,
    ← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [mode_memLp.coeFn_toLp] with x hx
  change inner ℝ (mode_memLp.toLp planarResolventMode x)
    (mode_memLp.toLp planarResolventMode x) = _
  rw [hx, RCLike.inner_apply, conj_trivial]
  ring

theorem mode_kinetic : ‖mode.val.2‖ ^ 2 =
    ∑ a : Fin 2, originalIntegral (fun x => planarPartial planarResolventMode (planarAxis a) x ^ 2) := by
  have hi (a : Fin 2) : Integrable (fun x => planarPartial planarResolventMode (planarAxis a) x ^ 2) :=
    (planar_integrable_change_borel (borel PlanarPosition) ⟨rfl⟩ _).mpr
      (planarResolventMode_partial_square_integrable (planarAxis a))
  simp_rw [← planar_integral_change_borel (borel PlanarPosition) ⟨rfl⟩]
  rw [← real_inner_self_eq_norm_sq, L2.inner_def,
    ← integral_finsetSum Finset.univ (fun a _ => hi a)]
  apply integral_congr_ae
  filter_upwards [mode_grad_memLp.coeFn_toLp] with x hx
  change inner ℝ (mode_grad_memLp.toLp (grad planarResolventMode) x)
    (mode_grad_memLp.toLp (grad planarResolventMode) x) = _
  rw [hx, real_inner_self_eq_norm_sq, grad_norm_sq]

theorem mode_form : form mode.val = planarTestForm manufacturedPlanarWell planarResolventMode := by
  unfold form planarTestForm
  rw [mode_kinetic]
  apply congrArg₂ (· + ·)
  · rfl
  · change inner ℝ modeTarget.1 (wellMultiplier modeTarget.1) =
      originalIntegral (fun x => manufacturedPlanarWell x * planarResolventMode x ^ 2)
    rw [← planar_integral_change_borel (borel PlanarPosition) ⟨rfl⟩, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [mode_memLp.coeFn_toLp, wellMultiply_ae modeTarget.1] with x hx hw
    change inner ℝ (modeTarget.1 x) (wellMultiply modeTarget.1 x) = _
    change modeTarget.1 x = planarResolventMode x at hx
    rw [hw, hx, RCLike.inner_apply, conj_trivial]
    ring

theorem form_smul (c : ℝ) (u : Target) : form (c • u) = c ^ 2 * form u := by
  change (1 / 2 : ℝ) * ‖c • u.2‖ ^ 2 + inner ℝ (c • u.1) (wellMultiplier (c • u.1)) = _
  rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, map_smul,
    real_inner_smul_left, real_inner_smul_right]
  unfold form
  ring

theorem mode_energy : form mode.val = -(1 / 2 : ℝ) * ‖mode.val.1‖ ^ 2 := by
  rw [mode_form, mode_mass]
  exact planarResolventMode_energy

theorem mode_mass_positive : 0 < ‖mode.val.1‖ ^ 2 := by
  rw [mode_mass]
  exact planarResolventMode_square_integral_positive

theorem normalizedMode_mass : ‖normalizedMode.val.1‖ ^ 2 = 1 := by
  change ‖(Real.sqrt (‖mode.val.1‖ ^ 2))⁻¹ • mode.val.1‖ ^ 2 = 1
  rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, inv_pow,
    Real.sq_sqrt mode_mass_positive.le, inv_mul_cancel₀ mode_mass_positive.ne']

theorem normalizedMode_energy : form normalizedMode.val = -(1 / 2 : ℝ) := by
  change form ((Real.sqrt (‖mode.val.1‖ ^ 2))⁻¹ • mode.val) = _
  rw [form_smul, mode_energy, inv_pow, Real.sq_sqrt mode_mass_positive.le]
  calc
    _ = -(1 / 2 : ℝ) * ((‖mode.val.1‖ ^ 2)⁻¹ * ‖mode.val.1‖ ^ 2) := by ring
    _ = _ := by rw [inv_mul_cancel₀ mode_mass_positive.ne', mul_one]

end PlanarSobolev
end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_PlanarProjectionGap
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The isolated-well orthogonal gap implies the actual rank-one projection
bound on every vector in the closed Sobolev graph. The ground cross term
vanishes by the proved variational minimum, without a further spectral input. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb.PlanarSobolev
open RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean

attribute [local instance] OAI.ContinuumCoulomb.PlanarSobolev.instMeasurableSpacePlanarPosition_3
attribute [local instance] OAI.ContinuumCoulomb.PlanarSobolev.instBorelSpacePlanarPosition_3
attribute [local instance] OAI.ContinuumCoulomb.PlanarSobolev.instMeasureSpacePlanarPosition_3
theorem shiftedForm_add_smul (u g : Target) (t : ℝ) :
    shiftedForm (u + t • g) = shiftedForm u + t * shiftedCross u g + t^2 * shiftedForm g := by
  change (1/2 : ℝ) * ‖u.2 + t • g.2‖ ^ 2 +
      inner ℝ (u.1 + t • g.1) (wellMultiplier (u.1 + t • g.1)) +
      (1/2 : ℝ) * ‖u.1 + t • g.1‖ ^ 2 = _
  rw [norm_add_sq_real, norm_add_sq_real, map_add, map_smul]
  simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
    norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  unfold shiftedForm form shiftedCross
  ring

theorem shiftedForm_nonnegative (u : Sobolev) : 0 ≤ shiftedForm u.val := by
  have h := form_lower u
  unfold shiftedForm
  linarith

theorem shiftedForm_normalizedMode : shiftedForm normalizedMode.val = 0 := by
  rw [shiftedForm, normalizedMode_energy, normalizedMode_mass]
  norm_num

private theorem affine_nonnegative_slope_zero (a b : ℝ) (h : ∀ t : ℝ, 0 ≤ a + t*b) : b = 0 := by
  by_contra hb
  have ht := h (-(a+1)/b)
  have he : a + (-(a+1)/b)*b = -1 := by field_simp [hb]; ring
  rw [he] at ht
  linarith

theorem shiftedCross_normalizedMode (u : Sobolev) : shiftedCross u.val normalizedMode.val = 0 := by
  apply affine_nonnegative_slope_zero (shiftedForm u.val)
  intro t
  have h := shiftedForm_nonnegative (u + t • normalizedMode)
  change 0 ≤ shiftedForm (u.val + t • normalizedMode.val) at h
  rw [shiftedForm_add_smul, shiftedForm_normalizedMode, mul_zero, add_zero] at h
  exact h

theorem shiftedForm_remove_ground (u : Sobolev) (t : ℝ) :
    shiftedForm (u - t • normalizedMode).val = shiftedForm u.val := by
  change shiftedForm (u.val - t • normalizedMode.val) = _
  rw [sub_eq_add_neg, ← neg_smul, shiftedForm_add_smul,
    shiftedCross_normalizedMode, shiftedForm_normalizedMode]
  ring

/-- The precise rank-one closed-form bound needed in the multiwell IMS
argument, derived from the already cited isolated spectral input. -/
theorem manufacturedPlanarWell_projection_gap (hpublished : ManufacturedPlanarGroundGap) :
    ∃ γ : ℝ, 0 < γ ∧ γ ≤ 1/4 ∧ ∀ u : Sobolev,
      ((-1/2 : ℝ) + γ) * ‖u.val.1‖^2 -
        γ * (inner ℝ u.val.1 normalizedMode.val.1)^2 ≤ form u.val := by
  obtain ⟨γ₀, hγ₀, hgap₀⟩ := hpublished
  let γ := min γ₀ (1/4 : ℝ)
  have hγ : 0 < γ := lt_min hγ₀ (by norm_num)
  have hgap (u : Sobolev) (hu : inner ℝ u.val.1 normalizedMode.val.1 = 0) :
      ((-1/2 : ℝ) + γ) * ‖u.val.1‖^2 ≤ form u.val := by
    have hcoef : (-1/2 : ℝ) + γ ≤ -1/2 + γ₀ := by
      dsimp only [γ]
      linarith [min_le_left γ₀ (1/4 : ℝ)]
    exact (mul_le_mul_of_nonneg_right hcoef (sq_nonneg ‖u.val.1‖)).trans (hgap₀ u hu)
  refine ⟨γ, hγ, min_le_right _ _, fun u => ?_⟩
  let c := inner ℝ u.val.1 normalizedMode.val.1
  let v : Sobolev := u - c • normalizedMode
  have hv : inner ℝ v.val.1 normalizedMode.val.1 = 0 := by
    change inner ℝ (u.val.1 - c • normalizedMode.val.1) normalizedMode.val.1 = 0
    rw [inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq, normalizedMode_mass]
    dsimp only [c]
    ring
  have hn : ‖v.val.1‖^2 = ‖u.val.1‖^2 - c^2 := by
    change ‖u.val.1 - c • normalizedMode.val.1‖^2 = _
    rw [norm_sub_sq_real, real_inner_smul_right, norm_smul, mul_pow,
      Real.norm_eq_abs, sq_abs, normalizedMode_mass]
    dsimp only [c]
    ring
  have hshift : shiftedForm v.val = shiftedForm u.val := shiftedForm_remove_ground u c
  have hg := hgap v hv
  unfold shiftedForm at hshift
  rw [hn] at hg hshift
  dsimp only [c] at hg hshift
  linarith

theorem normalizedMode_ae : normalizedMode.val.1 =ᵐ[volume] normalizedPlanarMode := by
  have hs := Lp.coeFn_smul (Real.sqrt (‖mode.val.1‖^2))⁻¹ mode.val.1
  filter_upwards [hs, mode_memLp.coeFn_toLp] with x hx hm
  change (((Real.sqrt (‖mode.val.1‖^2))⁻¹ • mode.val.1 : Lp ℝ 2 volume) x) = _
  rw [hx]
  change (Real.sqrt (‖mode.val.1‖^2))⁻¹ * mode.val.1 x = _
  change mode.val.1 x = planarResolventMode x at hm
  rw [hm, mode_mass, normalizedPlanarMode_eq_const_mul]
  rfl

theorem graph_normalizedMode_inner (u : Test) :
    inner ℝ (graph (μ := volume) u).1 normalizedMode.val.1 =
      ∫ x, u.val x * normalizedPlanarMode x := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(memLp_of_mem_C1c (μ := volume) u.property).coeFn_toLp,
    normalizedMode_ae] with x hx hg
  change toL2 (μ := volume) u x = u.val x at hx
  change inner ℝ (toL2 (μ := volume) u x) (normalizedMode.val.1 x) = _
  rw [hx, hg, RCLike.inner_apply, conj_trivial]
  ring

/-- The rank-one inequality is attached to the actual normalized planar
function and actual test-function integrals used by localization. -/
theorem manufacturedPlanarWell_test_projection_gap (hpublished : ManufacturedPlanarGroundGap) :
    ∃ γ : ℝ, 0 < γ ∧ γ ≤ 1/4 ∧ ∀ u : Test,
      ((-1/2 : ℝ) + γ) * (∫ x, u.val x ^ 2) -
        γ * (∫ x, u.val x * normalizedPlanarMode x)^2 ≤
          planarTestForm manufacturedPlanarWell u.val := by
  obtain ⟨γ, hγ, hsmall, hgap⟩ := manufacturedPlanarWell_projection_gap hpublished
  refine ⟨γ, hγ, hsmall, fun u => ?_⟩
  let v : Sobolev := ⟨graph (μ := volume) u, subset_closure ⟨u, rfl⟩⟩
  have hg := hgap v
  change ((-1/2 : ℝ) + γ) * ‖(graph (μ := volume) u).1‖^2 -
      γ * (inner ℝ (graph (μ := volume) u).1 normalizedMode.val.1)^2 ≤
        form (graph (μ := volume) u) at hg
  rw [graph_mass, graph_normalizedMode_inner, graph_form] at hg
  exact hg

end ContinuumCoulomb.PlanarSobolev

namespace ContinuumCoulomb

/-- Export the isolated projection inequality with the ambient Euclidean
measure used by the actual continuum construction. -/
theorem manufacturedPlanarWell_actual_projection_gap
    (hpublished : PlanarSobolev.ManufacturedPlanarGroundGap) :
    ∃ γ : ℝ, 0 < γ ∧ γ ≤ 1/4 ∧ ∀ f : PlanarPosition → ℝ,
      ContDiff ℝ 1 f → HasCompactSupport f →
      ((-1/2 : ℝ) + γ) * (∫ x, f x ^ 2) -
        γ * (∫ x, f x * normalizedPlanarMode x)^2 ≤
          planarTestForm manufacturedPlanarWell f := by
  let : MeasurableSpace PlanarPosition := borel PlanarPosition
  let : BorelSpace PlanarPosition := ⟨rfl⟩
  let : MeasureSpace PlanarPosition := measureSpaceOfInnerProductSpace
  obtain ⟨γ, hγ, hsmall, hgap⟩ := PlanarSobolev.manufacturedPlanarWell_test_projection_gap hpublished
  refine ⟨γ, hγ, hsmall, fun f hf hc => ?_⟩
  have h := hgap ⟨f, hf, hc⟩
  have he (g : PlanarPosition → ℝ) := PlanarSobolev.planar_integral_change_borel
    (borel PlanarPosition) ⟨rfl⟩ g
  rw [he (fun x => f x ^ 2), he (fun x => f x * normalizedPlanarMode x)] at h
  exact h

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_PlanarTranslatedGap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The same fixed isolated-well projection gap holds at every actual
planar site, by translation of test functions and Euclidean volume. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb

theorem planarPartial_add_right (f : PlanarPosition → ℝ) (u e x : PlanarPosition) :
    planarPartial (fun y => f (y+u)) e x = planarPartial f e (x+u) := by
  simp only [planarPartial, fderiv_comp_add_right]

theorem planarTestForm_translate (W f : PlanarPosition → ℝ) (u : PlanarPosition) :
    planarTestForm W (fun x => f (x+u)) =
      planarTestForm (fun x => W (x-u)) f := by
  unfold planarTestForm
  apply congrArg₂ (· + ·)
  · congr 1
    apply Finset.sum_congr rfl
    intro a _
    simp_rw [planarPartial_add_right]
    exact integral_add_right_eq_self (fun x => planarPartial f (planarAxis a) x ^ 2) u
  · rw [← integral_add_right_eq_self (fun x => W (x-u) * f x ^ 2) u]
    apply integral_congr_ae
    filter_upwards [] with x
    simp only [add_sub_cancel_right]

theorem manufacturedPlanarWell_translated_projection_gap
    (hpublished : PlanarSobolev.ManufacturedPlanarGroundGap) :
    ∃ γ : ℝ, 0 < γ ∧ γ ≤ 1/4 ∧ ∀ (u : PlanarPosition) (f : PlanarPosition → ℝ),
      ContDiff ℝ 1 f → HasCompactSupport f →
      ((-1/2 : ℝ) + γ) * (∫ x, f x ^ 2) -
        γ * (∫ x, f x * normalizedPlanarMode (x-u))^2 ≤
          planarTestForm (fun x => manufacturedPlanarWell (x-u)) f := by
  obtain ⟨γ, hγ, hsmall, hgap⟩ := manufacturedPlanarWell_actual_projection_gap hpublished
  refine ⟨γ, hγ, hsmall, fun u f hf hc => ?_⟩
  have hF : ContDiff ℝ 1 (fun x => f (x+u)) := hf.comp (contDiff_id.add contDiff_const)
  have hC : HasCompactSupport (fun x => f (x+u)) := hc.comp_homeomorph (Homeomorph.addRight u)
  have h := hgap (fun x => f (x+u)) hF hC
  have hm : (∫ x, f (x+u)^2) = ∫ x, f x^2 :=
    integral_add_right_eq_self (fun x => f x^2) u
  have hp : (∫ x, f (x+u) * normalizedPlanarMode x) =
      ∫ x, f x * normalizedPlanarMode (x-u) := by
    rw [← integral_add_right_eq_self (fun x => f x * normalizedPlanarMode (x-u)) u]
    apply integral_congr_ae
    filter_upwards [] with x
    simp only [add_sub_cancel_right]
  rwa [hm, hp, planarTestForm_translate] at h

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_PlanarMultiwellGap
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual planar multiwell form has a fixed excitation gap away from
the span of the translated manufactured modes, up to explicit inverse-square
localization and exponential tail errors. No multiwell spectral input is used. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb

theorem planar_partition_mass {ι : Type*} [Fintype ι]
    (θ : ι → PlanarPosition → ℝ) (hθ : ∀ i, Continuous (θ i))
    (hpart : ∀ x, ∑ i, θ i x ^ 2 = 1)
    (f : PlanarPosition → ℝ) (hf : Continuous f) (hc : HasCompactSupport f) :
    (∑ i, ∫ x, (θ i x * f x)^2) = ∫ x, f x^2 := by
  have hi (i : ι) : Integrable (fun x => (θ i x * f x)^2) := by
    have hm : HasCompactSupport (fun x => θ i x * f x) := hc.mul_left
    have hs : HasCompactSupport (fun x => (θ i x * f x)^2) :=
      hm.comp_left (g := fun t : ℝ => t^2) (by norm_num)
    exact (((hθ i).mul hf).pow 2).integrable_of_hasCompactSupport hs
  rw [← integral_finsetSum _ (fun i _ => hi i)]
  apply integral_congr_ae
  filter_upwards [] with x
  calc
    (∑ i, (θ i x * f x)^2) = (∑ i, θ i x^2) * f x^2 := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = _ := by rw [hpart x, one_mul]

theorem planar_free_form_nonnegative (f : PlanarPosition → ℝ) :
    0 ≤ planarTestForm (fun _ => 0) f := by
  unfold planarTestForm
  simp only [zero_mul, integral_zero, add_zero]
  apply mul_nonneg (by norm_num)
  exact Finset.sum_nonneg (fun a _ => integral_nonneg (fun x => sq_nonneg _))

theorem planarWellSum_projection_lower {γ : ℝ} (hsmall : γ ≤ 1/4)
    (hgap : ∀ (u : PlanarPosition) (f : PlanarPosition → ℝ),
      ContDiff ℝ 1 f → HasCompactSupport f →
      ((-1/2 : ℝ)+γ) * (∫ x, f x^2) - γ * (∫ x, f x * normalizedPlanarMode (x-u))^2 ≤
        planarTestForm (fun x => manufacturedPlanarWell (x-u)) f)
    {m : ℕ} {D : ℝ} (hD : 8 ≤ D) (u : Fin m → PlanarPosition)
    (hsep : ∀ i j, i ≠ j → D ≤ ‖u i-u j‖)
    (f : PlanarPosition → ℝ) (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f) :
    ((-1/2 : ℝ)+γ) * (∫ x, f x^2) -
      γ * (∑ i, (∫ x, (planarSitePartition D u (some i) x * f x) * normalizedPlanarMode (x-u i))^2) -
      planarSiteDerivativeBound D ^ 2 * (∫ x, f x^2) ≤ planarTestForm (planarWellSum u) f := by
  have hsite (i : Fin m) := hgap (u i) (fun x => planarSitePartition D u (some i) x * f x)
    ((planarSitePartition_C1 D u (some i)).mul hf)
    (show HasCompactSupport (fun x => planarSitePartition D u (some i) x * f x) from hc.mul_left)
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin m))) => hsite i)
  simp only [Finset.sum_sub_distrib, ← Finset.mul_sum] at hs
  have he : ((-1/2 : ℝ)+γ) * (∫ x, (planarSitePartition D u none x * f x)^2) ≤
      planarTestForm (fun _ => 0) (fun x => planarSitePartition D u none x * f x) := by
    have hneg : (-1/2 : ℝ)+γ ≤ 0 := by linarith
    exact (mul_nonpos_of_nonpos_of_nonneg hneg (integral_nonneg (fun x => sq_nonneg _))).trans
      (planar_free_form_nonnegative _)
  have hm := planar_partition_mass (planarSitePartition D u)
    (fun i => (planarSitePartition_C1 D u i).continuous)
    (planarSitePartition_square_sum (by linarith : 0 < D) u hsep) f hf.continuous hc
  rw [Fintype.sum_option] at hm
  have hl := planarWellSum_localization_lower hD u hsep f hf hc
  calc
    _ = (((-1/2 : ℝ)+γ) * (∫ x, (planarSitePartition D u none x * f x)^2) +
        (((-1/2 : ℝ)+γ) * (∑ i, ∫ x, (planarSitePartition D u (some i) x * f x)^2) -
          γ * (∑ i, (∫ x, (planarSitePartition D u (some i) x * f x) * normalizedPlanarMode (x-u i))^2))) -
        planarSiteDerivativeBound D^2 * (∫ x, f x^2) := by rw [← hm]; ring
    _ ≤ _ := (sub_le_sub_right (add_le_add he hs) _).trans hl

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_PlanarMultiwellProjection
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A global multiwell lower bound on every test function, with actual
uncut orbital coefficients. This form of the estimate is stable under H1
approximation and tensor products; no exact orthogonality of approximants
is needed. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb

private theorem cutoff_add_sq_le {η : ℝ} (hη : 0 < η) (a b : ℝ) :
    (a+b)^2 ≤ (1+η)*a^2 + (1+η⁻¹)*b^2 := by
  have he : (((1+η)*a^2 + (1+η⁻¹)*b^2) - (a+b)^2)*η = (η*a-b)^2 := by
    field_simp [hη.ne']
    ring
  have hn : 0 ≤ (((1+η)*a^2 + (1+η⁻¹)*b^2) - (a+b)^2)*η := by
    rw [he]
    exact sq_nonneg _
  exact sub_nonneg.mp ((nonneg_of_mul_nonneg_left hn hη))

theorem planarSiteCutoff_pair_error {D : ℝ} (hD : 0 < D) (u : PlanarPosition)
    (f : PlanarPosition → ℝ) (hf : MemLp f 2) :
    ((∫ x, (Real.sin (planarSiteAngle D u x)*f x)*normalizedPlanarMode (x-u)) -
      (∫ x, f x*normalizedPlanarMode (x-u)))^2 ≤
      (∫ x, f x^2)*(planarSiteTailConstant*Real.exp (-(19/20:ℝ)*(D/8))) := by
  have hm := normalizedPlanarMode_memLp.comp_measurePreserving (measurePreserving_sub_right volume u)
  have hi₀ : Integrable (fun x => f x*normalizedPlanarMode (x-u)) := hf.integrable_mul hm
  have hi₁ : Integrable (fun x => f x*planarSiteCutoffError D u x) :=
    hf.integrable_mul (planarSiteCutoffError_memLp D u)
  have he : (∫ x, (Real.sin (planarSiteAngle D u x)*f x)*normalizedPlanarMode (x-u)) -
      (∫ x, f x*normalizedPlanarMode (x-u)) = ∫ x, f x*planarSiteCutoffError D u x := by
    have hp : (fun x => (Real.sin (planarSiteAngle D u x)*f x)*normalizedPlanarMode (x-u)) =
        (fun x => f x*normalizedPlanarMode (x-u) + f x*planarSiteCutoffError D u x) := by
      funext x
      unfold planarSiteCutoffError
      ring
    rw [hp, integral_add hi₀ hi₁]
    ring
  rw [he]
  exact (planar_l2_pair_sq_le f (planarSiteCutoffError D u) hf
    (planarSiteCutoffError_memLp D u)).trans
      (mul_le_mul_of_nonneg_left (planarSiteCutoffError_integral_bound hD u)
        (integral_nonneg (fun x => sq_nonneg _)))

theorem planarSiteCutoff_pair_bound {D η : ℝ} (hD : 0 < D) (hη : 0 < η)
    (u : PlanarPosition) (f : PlanarPosition → ℝ) (hf : MemLp f 2) :
    (∫ x, (Real.sin (planarSiteAngle D u x)*f x)*normalizedPlanarMode (x-u))^2 ≤
      (1+η)*(∫ x, f x*normalizedPlanarMode (x-u))^2 +
      (1+η⁻¹)*(∫ x, f x^2)*(planarSiteTailConstant*Real.exp (-(19/20:ℝ)*(D/8))) := by
  have hy := cutoff_add_sq_le hη (∫ x, f x*normalizedPlanarMode (x-u))
    ((∫ x, (Real.sin (planarSiteAngle D u x)*f x)*normalizedPlanarMode (x-u)) -
      (∫ x, f x*normalizedPlanarMode (x-u)))
  have he := mul_le_mul_of_nonneg_left (planarSiteCutoff_pair_error hD u f hf)
    (show 0 ≤ 1+η⁻¹ by positivity)
  nlinarith

/-- Global lower bound with explicitly controlled finite orbital form and
cutoff error. The only spectral input is the published isolated-well gap. -/
theorem planarWellSum_test_projection_bound
    (hpublished : PlanarSobolev.ManufacturedPlanarGroundGap) :
    ∃ γ : ℝ, 0 < γ ∧ γ ≤ 1/4 ∧ ∀ (m : ℕ) (D η : ℝ), 8 ≤ D → 0 < η →
      ∀ u : Fin m → PlanarPosition, (∀ i j, i ≠ j → D ≤ ‖u i-u j‖) →
      ∀ f : PlanarPosition → ℝ, ContDiff ℝ 1 f → HasCompactSupport f →
      ((-1/2:ℝ)+γ-planarSiteDerivativeBound D^2-
        γ*(1+η⁻¹)*m*planarSiteTailConstant*Real.exp (-(19/20:ℝ)*(D/8)))*(∫ x, f x^2) -
        γ*(1+η)*(∑ i, (∫ x, f x*normalizedPlanarMode (x-u i))^2) ≤
          planarTestForm (planarWellSum u) f := by
  obtain ⟨γ, hγ, hsmall, hgap⟩ := manufacturedPlanarWell_translated_projection_gap hpublished
  refine ⟨γ, hγ, hsmall, fun m D η hD hη u hsep f hf hc => ?_⟩
  have hL2 : MemLp f 2 := hf.continuous.memLp_of_hasCompactSupport hc
  have h := planarWellSum_projection_lower hsmall hgap hD u hsep f hf hc
  have hs : (∑ i, (∫ x, (planarSitePartition D u (some i) x*f x)*
      normalizedPlanarMode (x-u i))^2) ≤
      (1+η)*(∑ i, (∫ x, f x*normalizedPlanarMode (x-u i))^2) +
        (1+η⁻¹)*m*(∫ x, f x^2)*(planarSiteTailConstant*Real.exp (-(19/20:ℝ)*(D/8))) := by
    calc
      _ ≤ ∑ i, ((1+η)*(∫ x, f x*normalizedPlanarMode (x-u i))^2 +
          (1+η⁻¹)*(∫ x, f x^2)*(planarSiteTailConstant*Real.exp (-(19/20:ℝ)*(D/8)))) :=
        Finset.sum_le_sum (fun i _ => planarSiteCutoff_pair_bound (by linarith) hη (u i) f hL2)
      _ = _ := by
        simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
          Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring
  have hm := mul_le_mul_of_nonneg_left hs hγ.le
  nlinarith

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_LocalizedOrbitalGram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual localized L2 orbitals form a well-conditioned independent
family whenever the exponentially small pair overlaps have a small row sum.
In particular their finite span has an actual orthonormal basis. -/

noncomputable section
open MeasureTheory InnerProductSpace
open scoped BigOperators
namespace ContinuumCoulomb

theorem dualMatrix_quadratic_upper {m : ℕ} (A : Fin m → Fin m → ℝ)
    {a delta : ℝ} (hdelta : 0 ≤ delta) (hdiag : ∀ i, A i i ≤ a)
    (hoff : ∀ i j, i ≠ j → |A i j| ≤ delta) (d : Fin m → ℝ) :
    (∑ i, ∑ j, A i j * d i * d j) ≤ (a + m * delta) * ∑ i, d i ^ 2 := by
  have h := dualMatrix_quadratic_lower (fun i j => -A i j) hdelta
    (fun i => neg_le_neg (hdiag i)) (fun i j hij => by simpa only [abs_neg] using hoff i j hij) d
  simp only [neg_mul, Finset.sum_neg_distrib] at h
  linarith

theorem localizedOverlapBound_nonnegative (D : ℝ) : 0 ≤ localizedOverlapBound D :=
  mul_nonneg planarOverlapConstant_nonnegative (Real.exp_pos _).le

theorem planarModeOverlap_offsite {D : ℝ} {m : ℕ} (u : Fin m → PlanarPosition)
    (hsep : ∀ i j, i ≠ j → D ≤ ‖u i - u j‖) (i j : Fin m) (hij : i ≠ j) :
    |planarModeOverlap (u i) (u j)| ≤ localizedOverlapBound D := by
  rw [abs_of_nonneg (planarModeOverlap_nonnegative _ _)]
  exact (planarModeOverlap_decay _ _).trans (mul_le_mul_of_nonneg_left
    (Real.exp_le_exp.mpr (by linarith [hsep i j hij])) planarOverlapConstant_nonnegative)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_PlanarFrameBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual uncut planar modes satisfy the finite-frame bound needed
when combining planar and transverse spectral estimates. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb

private theorem frame_bound_from_synthesis {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {m : ℕ} (v : Fin m → E) {C : ℝ} (hC : 0 ≤ C)
    (hsynth : ∀ d : Fin m → ℝ, ‖∑ i, d i • v i‖^2 ≤ C*∑ i, (d i)^2)
    (f : E) : ∑ i, (inner ℝ (v i) f)^2 ≤ C*‖f‖^2 := by
  let d : Fin m → ℝ := fun i => inner ℝ (v i) f
  let S : ℝ := ∑ i, (d i)^2
  let g : E := ∑ i, d i • v i
  have hS : 0 ≤ S := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hg : ‖g‖^2 ≤ C*S := hsynth d
  have hpair : inner ℝ g f = S := by
    simp only [g, S, sum_inner, real_inner_smul_left, d, pow_two]
  have hcs : S^2 ≤ ‖g‖^2*‖f‖^2 := by
    rw [← hpair]
    simpa only [pow_two, real_inner_self_eq_norm_sq] using real_inner_mul_inner_self_le g f
  have hh : S^2 ≤ C*S*‖f‖^2 := hcs.trans
    (mul_le_mul_of_nonneg_right hg (sq_nonneg _))
  change S ≤ C*‖f‖^2
  rcases eq_or_lt_of_le hS with hs | hs
  · rw [← hs]
    exact mul_nonneg hC (sq_nonneg _)
  · nlinarith

theorem planarOrbitalL2_inner (u v : PlanarPosition) :
    inner ℝ (planarOrbitalL2 u) (planarOrbitalL2 v) = planarModeOverlap u v := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [
    (normalizedPlanarMode_memLp.comp_measurePreserving
      (measurePreserving_sub_right volume u)).coeFn_toLp,
    (normalizedPlanarMode_memLp.comp_measurePreserving
      (measurePreserving_sub_right volume v)).coeFn_toLp] with r hu hv
  change inner ℝ (planarOrbitalL2 u r) (planarOrbitalL2 v r) = _
  change planarOrbitalL2 u r = normalizedPlanarMode (r-u) at hu
  change planarOrbitalL2 v r = normalizedPlanarMode (r-v) at hv
  rw [hu,hv, RCLike.inner_apply, conj_trivial]
  exact mul_comm _ _

theorem planarOrbitalL2_frame_bound {D : ℝ} {m : ℕ} (u : Fin m → PlanarPosition)
    (hsep : ∀ i j, i ≠ j → D ≤ ‖u i-u j‖)
    (f : Lp ℝ 2 (volume : Measure PlanarPosition)) :
    ∑ i, (inner ℝ (planarOrbitalL2 (u i)) f)^2 ≤
      (1+m*localizedOverlapBound D)*‖f‖^2 := by
  apply frame_bound_from_synthesis (fun i => planarOrbitalL2 (u i))
    (by have h := localizedOverlapBound_nonnegative D; positivity)
  intro d
  have he : ‖∑ i, d i • planarOrbitalL2 (u i)‖^2 =
      ∑ i, ∑ j, planarModeOverlap (u i) (u j)*d i*d j := by
    rw [← real_inner_self_eq_norm_sq]
    simp_rw [sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right,
      planarOrbitalL2_inner]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [he]
  exact dualMatrix_quadratic_upper _ (localizedOverlapBound_nonnegative D)
    (fun i => (planarModeOverlap_diagonal (u i)).le) (planarModeOverlap_offsite u hsep) d

/-- Integral form, usable on almost-everywhere L2 slices. -/
theorem planar_modes_frame_bound {D : ℝ} {m : ℕ} (u : Fin m → PlanarPosition)
    (hsep : ∀ i j, i ≠ j → D ≤ ‖u i-u j‖)
    (f : PlanarPosition → ℝ) (hf : MemLp f 2) :
    ∑ i, (∫ r, f r*normalizedPlanarMode (r-u i))^2 ≤
      (1+m*localizedOverlapBound D)*(∫ r, f r^2) := by
  have h := planarOrbitalL2_frame_bound u hsep (hf.toLp f)
  have hi (i : Fin m) : inner ℝ (planarOrbitalL2 (u i)) (hf.toLp f) =
      ∫ r, f r*normalizedPlanarMode (r-u i) := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hf.coeFn_toLp,
      (normalizedPlanarMode_memLp.comp_measurePreserving
        (measurePreserving_sub_right volume (u i))).coeFn_toLp] with r hfr hmr
    change inner ℝ (planarOrbitalL2 (u i) r) (hf.toLp f r) = _
    change planarOrbitalL2 (u i) r = normalizedPlanarMode (r-u i) at hmr
    rw [hfr, hmr, RCLike.inner_apply, conj_trivial]
  have hn : ‖hf.toLp f‖^2 = ∫ r, f r^2 := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hf.coeFn_toLp] with r hr
    rw [hr, RCLike.inner_apply, conj_trivial]
    ring
  simpa only [hi, hn] using h

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_VerticalSliceProjection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual transverse Gaussian defines a contraction on the full L2
product space. No compact-support or smoothness hypothesis is imposed here. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

private theorem line_pair_sq_le (f g : ℝ → ℝ) (hf : MemLp f 2) (hg : MemLp g 2) :
    (∫ z, f z*g z)^2 ≤ (∫ z, f z^2)*(∫ z, g z^2) := by
  have hp (a b : ℝ → ℝ) (ha : MemLp a 2) (hb : MemLp b 2) :
      inner ℝ (ha.toLp a) (hb.toLp b) = ∫ z, a z*b z := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [ha.coeFn_toLp,hb.coeFn_toLp] with z hz hz'
    rw [hz,hz',RCLike.inner_apply,conj_trivial]
    ring
  have h := real_inner_mul_inner_self_le (hf.toLp f) (hg.toLp g)
  rw [hp f g hf hg,hp f f hf hf,hp g g hg hg] at h
  simpa only [pow_two] using h

theorem split_memLp_vertical_slices (f : SplitPosition → ℝ) (hf : MemLp f 2) :
    ∀ᵐ r : PlanarPosition, MemLp (fun z : ℝ => f (r,z)) 2 := by
  have hp : MemLp f 2 ((volume : Measure PlanarPosition).prod (volume : Measure ℝ)) := by
    simpa only [Measure.volume_eq_prod] using hf
  filter_upwards [hp.aestronglyMeasurable.prodMk_left,hp.integrable_sq.prod_right_ae] with r hr hi
  exact (memLp_two_iff_integrable_sq hr).mpr hi

/-- The normalized Gaussian coefficient is an L2 contraction on arbitrary
real wavefunctions, including the closure needed for the continuum form. -/
theorem verticalCoefficient_contraction {freq : ℝ} (hfreq : 0 < freq)
    (f : SplitPosition → ℝ) (hf : MemLp f 2) :
    MemLp (verticalCoefficient freq f) 2 ∧
      (∫ r, (verticalCoefficient freq f r)^2) ≤ ∫ p, f p^2 := by
  have hfprod : MemLp f 2 ((volume : Measure PlanarPosition).prod (volume : Measure ℝ)) := by
    simpa only [Measure.volume_eq_prod] using hf
  have hfsq := hfprod.integrable_sq
  have hm : AEStronglyMeasurable (verticalCoefficient freq f) volume :=
    (hfprod.aestronglyMeasurable.mul (verticalMode_memLp hfreq).aestronglyMeasurable.comp_snd).integral_prod_right'
  have hs := split_memLp_vertical_slices f hf
  have hdom : ∀ᵐ r : PlanarPosition,
      (verticalCoefficient freq f r)^2 ≤ ∫ z : ℝ, f (r,z)^2 := by
    filter_upwards [hs] with r hr
    simpa only [verticalCoefficient,verticalMode_normalized hfreq,mul_one] using
      line_pair_sq_le (fun z => f (r,z)) (verticalMode freq) hr (verticalMode_memLp hfreq)
  have hi : Integrable (fun r : PlanarPosition => ∫ z : ℝ, f (r,z)^2) := hfsq.integral_prod_left
  have ha : Integrable (fun r => (verticalCoefficient freq f r)^2) :=
    hi.mono' (hm.pow 2) (hdom.mono (fun r hr => by
      simpa only [Real.norm_eq_abs,
        abs_of_nonneg (sq_nonneg (verticalCoefficient freq f r))] using hr))
  refine ⟨(memLp_two_iff_integrable_sq hm).mpr ha, ?_⟩
  have h := integral_mono_ae ha hi hdom
  rw [← integral_prod _ hfsq] at h
  simpa only [Measure.volume_eq_prod] using h

theorem verticalCoefficient_sub_ae {freq : ℝ} (hfreq : 0 < freq)
    (f g : SplitPosition → ℝ) (hf : MemLp f 2) (hg : MemLp g 2) :
    verticalCoefficient freq (fun p => f p-g p) =ᵐ[volume]
      fun r => verticalCoefficient freq f r-verticalCoefficient freq g r := by
  filter_upwards [split_memLp_vertical_slices f hf,split_memLp_vertical_slices g hg] with r hr hr'
  unfold verticalCoefficient
  rw [show (fun z => (f (r,z)-g (r,z))*verticalMode freq z) =
    (fun z => f (r,z)*verticalMode freq z-g (r,z)*verticalMode freq z) from
      funext (fun z => sub_mul _ _ _)]
  simpa only [Pi.mul_apply] using
    integral_sub (hr.integrable_mul (verticalMode_memLp hfreq))
      (hr'.integrable_mul (verticalMode_memLp hfreq))

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_VerticalResidual
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact L2 mass splitting into the Gaussian transverse mode and its
orthogonal residual, for arbitrary product-space wavefunctions. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

theorem verticalLift_memLp {freq : ℝ} (hfreq : 0 < freq)
    (a : PlanarPosition → ℝ) (ha : MemLp a 2) : MemLp (verticalLift freq a) 2 := by
  have hm : AEStronglyMeasurable (verticalLift freq a)
      ((volume : Measure PlanarPosition).prod (volume : Measure ℝ)) :=
    ha.aestronglyMeasurable.comp_fst.mul (verticalMode_memLp hfreq).aestronglyMeasurable.comp_snd
  have hi := ha.integrable_sq.mul_prod (verticalMode_square_integrable hfreq)
  have he : (fun p : SplitPosition => verticalLift freq a p^2) =
      fun p => (a p.1)^2*(verticalMode freq p.2)^2 := by
    funext p
    exact mul_pow _ _ _
  rw [← he] at hi
  apply (memLp_two_iff_integrable_sq (by simpa only [Measure.volume_eq_prod] using hm)).mpr
  simpa only [Measure.volume_eq_prod] using hi

theorem verticalLift_mass {freq : ℝ} (hfreq : 0 < freq) (a : PlanarPosition → ℝ) :
    (∫ p, (verticalLift freq a p)^2) = ∫ r, a r^2 := by
  simp_rw [verticalLift, mul_pow]
  rw [Measure.volume_eq_prod,
    integral_prod_mul (fun r => a r^2) (fun z => verticalMode freq z^2),
    verticalMode_normalized hfreq,mul_one]

theorem verticalCoefficient_lift {freq : ℝ} (hfreq : 0 < freq)
    (a : PlanarPosition → ℝ) (r : PlanarPosition) :
    verticalCoefficient freq (verticalLift freq a) r = a r := by
  unfold verticalCoefficient verticalLift
  rw [show (fun z => a r*verticalMode freq z*verticalMode freq z) =
    (fun z => a r*(verticalMode freq z)^2) from funext (fun z => by ring)]
  rw [integral_const_mul,verticalMode_normalized hfreq,mul_one]

theorem verticalCoefficient_pair_identity {freq : ℝ} (hfreq : 0 < freq)
    (f : SplitPosition → ℝ) (hf : MemLp f 2) :
    (∫ p, f p*verticalLift freq (verticalCoefficient freq f) p) =
      ∫ r, (verticalCoefficient freq f r)^2 := by
  have ha := (verticalCoefficient_contraction hfreq f hf).1
  have hi := hf.integrable_mul (verticalLift_memLp hfreq _ ha)
  have hiprod : Integrable (fun p => f p*verticalLift freq (verticalCoefficient freq f) p)
      ((volume : Measure PlanarPosition).prod (volume : Measure ℝ)) := by
    rw [← Measure.volume_eq_prod]
    exact hi
  rw [Measure.volume_eq_prod,integral_prod _ hiprod]
  apply integral_congr_ae
  filter_upwards [] with r
  change (∫ z, f (r,z)*(verticalCoefficient freq f r*verticalMode freq z)) = _
  rw [show (fun z => f (r,z)*(verticalCoefficient freq f r*verticalMode freq z)) =
    (fun z => verticalCoefficient freq f r*(f (r,z)*verticalMode freq z)) from
      funext (fun z => by ring),integral_const_mul]
  change verticalCoefficient freq f r*verticalCoefficient freq f r = _
  ring

/-- Exact Pythagoras identity for the actual transverse projection. -/
theorem verticalResidual_mass {freq : ℝ} (hfreq : 0 < freq)
    (f : SplitPosition → ℝ) (hf : MemLp f 2) :
    MemLp (verticalResidual freq f) 2 ∧
      (∫ p, (verticalResidual freq f p)^2) =
        (∫ p, f p^2)-(∫ r, (verticalCoefficient freq f r)^2) := by
  let a := verticalCoefficient freq f
  let g := verticalLift freq a
  have ha : MemLp a 2 := (verticalCoefficient_contraction hfreq f hf).1
  have hg : MemLp g 2 := verticalLift_memLp hfreq a ha
  refine ⟨hf.sub hg,?_⟩
  have he : (fun p => (verticalResidual freq f p)^2) =
      (fun p => f p^2+(g p^2-2*(f p*g p))) := by
    funext p
    change (f p-g p)^2 = _
    ring
  rw [he,integral_add (f := fun p => f p^2) (g := fun p => g p^2-2*(f p*g p))
    hf.integrable_sq (hg.integrable_sq.sub ((hf.integrable_mul hg).const_mul 2)),
    integral_sub (f := fun p => g p^2) (g := fun p => 2*(f p*g p))
      hg.integrable_sq ((hf.integrable_mul hg).const_mul 2),integral_const_mul]
  have hm : (∫ p, g p^2) = ∫ r, a r^2 := verticalLift_mass hfreq a
  have hp : (∫ p, f p*g p) = ∫ r, a r^2 := verticalCoefficient_pair_identity hfreq f hf
  rw [hm,hp]
  dsimp [a]
  ring

theorem verticalResidual_coefficient_zero {freq : ℝ} (hfreq : 0 < freq)
    (f : SplitPosition → ℝ) (hf : MemLp f 2) :
    verticalCoefficient freq (verticalResidual freq f) =ᵐ[volume] 0 := by
  have ha := (verticalCoefficient_contraction hfreq f hf).1
  have h := verticalCoefficient_sub_ae hfreq f
    (verticalLift freq (verticalCoefficient freq f)) hf (verticalLift_memLp hfreq _ ha)
  filter_upwards [h] with r hr
  change verticalCoefficient freq (fun p => f p-verticalLift freq (verticalCoefficient freq f) p) r = 0
  simpa only [verticalCoefficient_lift hfreq,sub_self] using hr

/-- The residual is orthogonal to every product with the transverse mode. -/
theorem verticalResidual_orthogonal {freq : ℝ} (hfreq : 0 < freq)
    (f : SplitPosition → ℝ) (hf : MemLp f 2)
    (a : PlanarPosition → ℝ) (ha : MemLp a 2) :
    (∫ p, verticalResidual freq f p*verticalLift freq a p) = 0 := by
  have hr := (verticalResidual_mass hfreq f hf).1
  have hi := hr.integrable_mul (verticalLift_memLp hfreq a ha)
  have hiprod : Integrable (fun p => verticalResidual freq f p*verticalLift freq a p)
      ((volume : Measure PlanarPosition).prod (volume : Measure ℝ)) := by
    rw [← Measure.volume_eq_prod]
    exact hi
  rw [Measure.volume_eq_prod,integral_prod _ hiprod]
  apply integral_eq_zero_of_ae
  filter_upwards [verticalResidual_coefficient_zero hfreq f hf] with r hz
  change (∫ z, verticalResidual freq f (r,z)*(a r*verticalMode freq z)) = 0
  rw [show (fun z => verticalResidual freq f (r,z)*(a r*verticalMode freq z)) =
    (fun z => a r*(verticalResidual freq f (r,z)*verticalMode freq z)) from
      funext (fun z => by ring),integral_const_mul]
  change a r*verticalCoefficient freq (verticalResidual freq f) r = 0
  simp only [hz,Pi.zero_apply,mul_zero]

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_PlanarSliceProjection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Planar orbital coefficients on product L2, with exact contraction
and subtraction identities. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

theorem split_memLp_planar_slices (f : SplitPosition → ℝ) (hf : MemLp f 2) :
    ∀ᵐ z : ℝ, MemLp (fun r : PlanarPosition => f (r,z)) 2 := by
  have hp : MemLp f 2 ((volume : Measure PlanarPosition).prod (volume : Measure ℝ)) := by
    simpa only [Measure.volume_eq_prod] using hf
  filter_upwards [hp.aestronglyMeasurable.prodMk_right,hp.integrable_sq.prod_left_ae] with z hz hi
  exact (memLp_two_iff_integrable_sq hz).mpr hi

theorem planarCoefficient_contraction (u : PlanarPosition)
    (f : SplitPosition → ℝ) (hf : MemLp f 2) :
    MemLp (planarCoefficient u f) 2 ∧
      (∫ z, (planarCoefficient u f z)^2) ≤ ∫ p, f p^2 := by
  have hp : MemLp f 2 ((volume : Measure PlanarPosition).prod (volume : Measure ℝ)) := by
    simpa only [Measure.volume_eq_prod] using hf
  have hphi : MemLp (fun r => normalizedPlanarMode (r-u)) 2 :=
    normalizedPlanarMode_memLp.comp_measurePreserving (measurePreserving_sub_right volume u)
  have hm : AEStronglyMeasurable (planarCoefficient u f) volume :=
    (hp.aestronglyMeasurable.mul hphi.aestronglyMeasurable.comp_fst).prod_swap.integral_prod_right'
  have hdom : ∀ᵐ z : ℝ, (planarCoefficient u f z)^2 ≤ ∫ r : PlanarPosition, f (r,z)^2 := by
    filter_upwards [split_memLp_planar_slices f hf] with z hz
    have h := planar_l2_pair_sq_le (fun r => f (r,z))
      (fun r => normalizedPlanarMode (r-u)) hz hphi
    rw [integral_sub_right_eq_self (fun r => normalizedPlanarMode r^2) u,
      normalizedPlanarMode_normalized,mul_one] at h
    exact h
  have hi : Integrable (fun z : ℝ => ∫ r : PlanarPosition, f (r,z)^2) :=
    hp.integrable_sq.integral_prod_right
  have ha : Integrable (fun z => (planarCoefficient u f z)^2) :=
    hi.mono' (hm.pow 2) (hdom.mono (fun z hz => by
      simpa only [Real.norm_eq_abs,
        abs_of_nonneg (sq_nonneg (planarCoefficient u f z))] using hz))
  refine ⟨(memLp_two_iff_integrable_sq hm).mpr ha,?_⟩
  have h := integral_mono_ae ha hi hdom
  rw [← integral_prod_symm _ hp.integrable_sq] at h
  simpa only [Measure.volume_eq_prod] using h

theorem planarCoefficient_sub_ae (u : PlanarPosition)
    (f g : SplitPosition → ℝ) (hf : MemLp f 2) (hg : MemLp g 2) :
    planarCoefficient u (fun p => f p-g p) =ᵐ[volume]
      fun z => planarCoefficient u f z-planarCoefficient u g z := by
  have hphi : MemLp (fun r => normalizedPlanarMode (r-u)) 2 :=
    normalizedPlanarMode_memLp.comp_measurePreserving (measurePreserving_sub_right volume u)
  filter_upwards [split_memLp_planar_slices f hf,split_memLp_planar_slices g hg] with z hz hz'
  unfold planarCoefficient
  rw [show (fun r => (f (r,z)-g (r,z))*normalizedPlanarMode (r-u)) =
    (fun r => f (r,z)*normalizedPlanarMode (r-u)-g (r,z)*normalizedPlanarMode (r-u)) from
      funext (fun r => sub_mul _ _ _)]
  simpa only [Pi.mul_apply] using integral_sub (hz.integrable_mul hphi) (hz'.integrable_mul hphi)

theorem planarCoefficient_lift (u : PlanarPosition) (freq : ℝ)
    (a : PlanarPosition → ℝ) (z : ℝ) :
    planarCoefficient u (verticalLift freq a) z =
      (∫ r, a r*normalizedPlanarMode (r-u))*verticalMode freq z := by
  unfold planarCoefficient verticalLift
  rw [show (fun r => a r*verticalMode freq z*normalizedPlanarMode (r-u)) =
    (fun r => (a r*normalizedPlanarMode (r-u))*verticalMode freq z) from
      funext (fun r => by ring),integral_mul_const]

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_SplitFrameBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The planar frame estimate on arbitrary full L2 slices. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb

theorem split_planar_frame_bound {D : ℝ} {m : ℕ} (u : Fin m → PlanarPosition)
    (hsep : ∀ i j, i ≠ j → D ≤ ‖u i-u j‖)
    (f : SplitPosition → ℝ) (hf : MemLp f 2) :
    (∫ z, ∑ i, (planarCoefficient (u i) f z)^2) ≤
      (1+m*localizedOverlapBound D)*(∫ p, f p^2) := by
  have hp : MemLp f 2 ((volume : Measure PlanarPosition).prod (volume : Measure ℝ)) := by
    simpa only [Measure.volume_eq_prod] using hf
  have hi : Integrable (fun z : ℝ => ∑ i, (planarCoefficient (u i) f z)^2) :=
    integrable_finsetSum _ (fun i _ => (planarCoefficient_contraction (u i) f hf).1.integrable_sq)
  have hraw := hp.integrable_sq.integral_prod_right
  have hbound : ∀ᵐ z : ℝ, (∑ i, (planarCoefficient (u i) f z)^2) ≤
      (1+m*localizedOverlapBound D)*(∫ r : PlanarPosition, f (r,z)^2) := by
    filter_upwards [split_memLp_planar_slices f hf] with z hz
    exact planar_modes_frame_bound u hsep (fun r => f (r,z)) hz
  have h := integral_mono_ae hi (hraw.const_mul (1+m*localizedOverlapBound D)) hbound
  rw [integral_const_mul,← integral_prod_symm _ hp.integrable_sq] at h
  simpa only [Measure.volume_eq_prod] using h

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_SplitProjectionPairing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fubini identities for the actual localized tensor orbitals and the
transverse residual. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

theorem planarCoefficient_pair_tensor {freq : ℝ} (hfreq : 0 < freq)
    (u : PlanarPosition) (f : SplitPosition → ℝ) (hf : MemLp f 2) :
    (∫ z, planarCoefficient u f z*verticalMode freq z) =
      ∫ p, f p*localizedMode freq u p := by
  have hi : Integrable (fun p => f p*localizedMode freq u p)
      ((volume : Measure PlanarPosition).prod (volume : Measure ℝ)) := by
    rw [← Measure.volume_eq_prod]
    exact hf.integrable_mul (localizedMode_memLp hfreq u)
  rw [Measure.volume_eq_prod,integral_prod_symm _ hi]
  apply integral_congr_ae
  filter_upwards [] with z
  unfold planarCoefficient
  rw [← integral_mul_const]
  apply integral_congr_ae
  filter_upwards [] with r
  unfold localizedMode
  ring

theorem verticalCoefficient_pair_tensor {freq : ℝ} (hfreq : 0 < freq)
    (u : PlanarPosition) (f : SplitPosition → ℝ) (hf : MemLp f 2) :
    (∫ p, f p*localizedMode freq u p) =
      ∫ r, verticalCoefficient freq f r*normalizedPlanarMode (r-u) := by
  have hi : Integrable (fun p => f p*localizedMode freq u p)
      ((volume : Measure PlanarPosition).prod (volume : Measure ℝ)) := by
    rw [← Measure.volume_eq_prod]
    exact hf.integrable_mul (localizedMode_memLp hfreq u)
  rw [Measure.volume_eq_prod,integral_prod _ hi]
  apply integral_congr_ae
  filter_upwards [] with r
  unfold verticalCoefficient
  rw [← integral_mul_const]
  apply integral_congr_ae
  filter_upwards [] with z
  unfold localizedMode
  ring

theorem residual_planarCoefficient_orthogonal {freq : ℝ} (hfreq : 0 < freq)
    (u : PlanarPosition) (f : SplitPosition → ℝ) (hf : MemLp f 2) :
    (∫ z, planarCoefficient u (verticalResidual freq f) z*verticalMode freq z) = 0 := by
  rw [planarCoefficient_pair_tensor hfreq u _ (verticalResidual_mass hfreq f hf).1]
  exact verticalResidual_orthogonal hfreq f hf (fun r => normalizedPlanarMode (r-u))
    (normalizedPlanarMode_memLp.comp_measurePreserving (measurePreserving_sub_right volume u))

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_SplitProjectionBudget
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The full planar slice penalty is controlled by transverse mass and
the finite family of actual tensor-orbital coefficients. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb

theorem planarCoefficient_mass_split {freq : ℝ} (hfreq : 0 < freq)
    (u : PlanarPosition) (f : SplitPosition → ℝ) (hf : MemLp f 2) :
    (∫ z, (planarCoefficient u f z)^2) =
      (∫ z, (planarCoefficient u (verticalResidual freq f) z)^2) +
        (∫ p, f p*localizedMode freq u p)^2 := by
  let a := verticalCoefficient freq f
  let c := ∫ r, a r*normalizedPlanarMode (r-u)
  let b := planarCoefficient u f
  let r := planarCoefficient u (verticalResidual freq f)
  have ha : MemLp a 2 := (verticalCoefficient_contraction hfreq f hf).1
  have hl := verticalLift_memLp hfreq a ha
  have hr := (planarCoefficient_contraction u (verticalResidual freq f)
    (verticalResidual_mass hfreq f hf).1).1
  have hbeq : b =ᵐ[volume] fun z => r z+c*verticalMode freq z := by
    have hs := planarCoefficient_sub_ae u f (verticalLift freq a) hf hl
    filter_upwards [hs] with z hz
    have he := planarCoefficient_lift u freq a z
    change r z = b z-planarCoefficient u (verticalLift freq a) z at hz
    rw [he] at hz
    change b z = r z+c*verticalMode freq z
    dsimp [c]
    linarith
  rw [verticalCoefficient_pair_tensor hfreq u f hf]
  change (∫ z, (b z)^2) = (∫ z, (r z)^2)+c^2
  calc
    _ = ∫ z, (r z+c*verticalMode freq z)^2 :=
      integral_congr_ae (hbeq.mono (fun z hz => by rw [hz]))
    _ = (∫ z, (r z)^2)+(2*c)*(∫ z, r z*verticalMode freq z)+
        c^2*(∫ z, (verticalMode freq z)^2) := by
      have he : (fun z => (r z+c*verticalMode freq z)^2) =
          (fun z => (r z)^2+((2*c)*(r z*verticalMode freq z)+c^2*(verticalMode freq z)^2)) := by
        funext z
        ring
      have hc := hr.integrable_mul (verticalMode_memLp hfreq)
      rw [he,integral_add (f := fun z => (r z)^2)
        (g := fun z => (2*c)*(r z*verticalMode freq z)+c^2*(verticalMode freq z)^2)
        hr.integrable_sq
        ((hc.const_mul (2*c)).add ((verticalMode_square_integrable hfreq).const_mul (c^2))),
        integral_add (f := fun z => (2*c)*(r z*verticalMode freq z))
          (g := fun z => c^2*(verticalMode freq z)^2)
          (hc.const_mul (2*c)) ((verticalMode_square_integrable hfreq).const_mul (c^2)),
        integral_const_mul,integral_const_mul]
      ring
    _ = _ := by
      rw [residual_planarCoefficient_orthogonal hfreq u f hf,verticalMode_normalized hfreq]
      ring

/-- The estimate removes the spurious infinite-dimensional planar penalty
in the excited transverse sector, retaining only actual tensor coefficients. -/
theorem split_projection_budget {freq D : ℝ} (hfreq : 0 < freq)
    {m : ℕ} (u : Fin m → PlanarPosition)
    (hsep : ∀ i j, i ≠ j → D ≤ ‖u i-u j‖)
    (f : SplitPosition → ℝ) (hf : MemLp f 2) :
    (∫ z, ∑ i, (planarCoefficient (u i) f z)^2) ≤
      (1+m*localizedOverlapBound D)*
        ((∫ p, f p^2)-(∫ r, (verticalCoefficient freq f r)^2)) +
      ∑ i, (∫ p, f p*localizedMode freq (u i) p)^2 := by
  have hR := verticalResidual_mass hfreq f hf
  have hb := split_planar_frame_bound u hsep (verticalResidual freq f) hR.1
  rw [hR.2] at hb
  have he : (∫ z, ∑ i, (planarCoefficient (u i) f z)^2) =
      (∫ z, ∑ i, (planarCoefficient (u i) (verticalResidual freq f) z)^2) +
      ∑ i, (∫ p, f p*localizedMode freq (u i) p)^2 := by
    rw [integral_finsetSum _ (fun i _ => (planarCoefficient_contraction (u i) f hf).1.integrable_sq),
      integral_finsetSum _ (fun i _ =>
        (planarCoefficient_contraction (u i) (verticalResidual freq f) hR.1).1.integrable_sq)]
    simp_rw [planarCoefficient_mass_split hfreq _ f hf]
    rw [Finset.sum_add_distrib]
  rw [he]
  exact add_le_add hb le_rfl

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_VerticalCutoffTail
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Gaussian control of the inner-slab projection error for the actual
transverse cutoff. The loss decays exponentially in the square of the slab
width, with the oscillator frequency fixed by the construction. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

theorem verticalCutoffError_memLp {freq : ℝ} (hfreq : 0 < freq) (S : ℝ) :
    MemLp (verticalCutoffError freq S) 2 := by
  apply (verticalMode_memLp hfreq).of_le_mul (c := 2)
    ((((verticalInnerCutoff_smooth S).continuous.sub continuous_const).mul
      (verticalMode_smooth freq).continuous).aestronglyMeasurable)
  filter_upwards [] with z
  change ‖(verticalInnerCutoff S z-1)*verticalMode freq z‖ ≤ _
  rw [norm_mul, Real.norm_eq_abs]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  have h := abs_sub (verticalInnerCutoff S z) (1:ℝ)
  have hs := Real.abs_sin_le_one (verticalCutoffAngle S z)
  simp only [abs_one] at h
  change |verticalInnerCutoff S z| ≤ 1 at hs
  linarith

theorem verticalCutoffError_square_bound {freq S : ℝ}
    (hfreq : 0 < freq) (hS : 0 < S) (z : ℝ) :
    verticalCutoffError freq S z^2 ≤
      ((4 / Real.sqrt (Real.pi/freq)) * Real.exp (-freq*S^2/8)) *
        Real.exp (-(freq/2)*z^2) := by
  by_cases hz : |z| ≤ S/2
  · rw [verticalCutoffError, (verticalCutoff_inner hS hz).1, sub_self, zero_mul, zero_pow (by decide : 2 ≠ 0)]
    positivity
  · have hz' : S/2 ≤ |z| := (le_of_not_ge hz)
    have hsq : S^2/4 ≤ z^2 := by
      have h := (sq_le_sq₀ (by positivity : 0 ≤ S/2) (abs_nonneg z)).mpr hz'
      nlinarith [sq_abs z]
    have hd : (verticalInnerCutoff S z-1)^2 ≤ (4:ℝ) := by
      have h := abs_sub (verticalInnerCutoff S z) (1:ℝ)
      have hs := Real.abs_sin_le_one (verticalCutoffAngle S z)
      simp only [abs_one] at h
      change |verticalInnerCutoff S z| ≤ 1 at hs
      have ha : |verticalInnerCutoff S z-1| ≤ 2 := by linarith
      nlinarith [sq_abs (verticalInnerCutoff S z-1), abs_nonneg (verticalInnerCutoff S z-1)]
    have he : Real.exp (-freq*z^2) ≤
        Real.exp (-freq*S^2/8)*Real.exp (-(freq/2)*z^2) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      nlinarith [mul_le_mul_of_nonneg_left hsq hfreq.le]
    unfold verticalCutoffError
    rw [mul_pow, verticalMode_square hfreq]
    calc
      _ ≤ 4 * (Real.exp (-freq*z^2) / Real.sqrt (Real.pi/freq)) :=
        mul_le_mul_of_nonneg_right hd (by positivity)
      _ ≤ 4 * ((Real.exp (-freq*S^2/8)*Real.exp (-(freq/2)*z^2)) /
          Real.sqrt (Real.pi/freq)) :=
        mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right he (Real.sqrt_nonneg _)) (by norm_num)
      _ = _ := by ring

theorem verticalCutoffError_integral_bound {freq S : ℝ}
    (hfreq : 0 < freq) (hS : 0 < S) :
    (∫ z, verticalCutoffError freq S z^2) ≤
      verticalCutoffTailConstant freq * Real.exp (-freq*S^2/8) := by
  have hi : Integrable (fun z => verticalCutoffError freq S z^2) :=
    (memLp_two_iff_integrable_sq (verticalCutoffError_memLp hfreq S).aestronglyMeasurable).mp
      (verticalCutoffError_memLp hfreq S)
  have he := (integrable_exp_neg_mul_sq (show 0 < freq/2 by linarith)).const_mul
    ((4 / Real.sqrt (Real.pi/freq)) * Real.exp (-freq*S^2/8))
  have h := integral_mono hi he (verticalCutoffError_square_bound hfreq hS)
  rw [integral_const_mul] at h
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  unfold verticalCutoffTailConstant
  ring

/-- The projection error is bounded for every actual L2 test function. -/
theorem verticalCutoff_pair_error {freq S : ℝ} (hfreq : 0 < freq) (hS : 0 < S)
    (u : ℝ → ℝ) (hu : MemLp u 2) :
    ((∫ z, (verticalInnerCutoff S z*u z)*verticalMode freq z) -
      (∫ z, u z*verticalMode freq z))^2 ≤
      (∫ z, u z^2)*(verticalCutoffTailConstant freq * Real.exp (-freq*S^2/8)) := by
  have hi₀ : Integrable (fun z => u z*verticalMode freq z) := hu.integrable_mul (verticalMode_memLp hfreq)
  have hi₁ : Integrable (fun z => u z*verticalCutoffError freq S z) :=
    hu.integrable_mul (verticalCutoffError_memLp hfreq S)
  have hp : (∫ z, (verticalInnerCutoff S z*u z)*verticalMode freq z) -
      (∫ z, u z*verticalMode freq z) = ∫ z, u z*verticalCutoffError freq S z := by
    have he : (fun z => (verticalInnerCutoff S z*u z)*verticalMode freq z) =
        (fun z => u z*verticalMode freq z + u z*verticalCutoffError freq S z) := by
      funext z
      unfold verticalCutoffError
      ring
    rw [he, integral_add hi₀ hi₁]
    ring
  rw [hp]
  have hpair (f g : ℝ → ℝ) (hf : MemLp f 2) (hg : MemLp g 2) :
      inner ℝ (hf.toLp f) (hg.toLp g) = ∫ z, f z*g z := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with z hz hf'
    rw [hz, hf', RCLike.inner_apply, conj_trivial]
    ring
  have h := real_inner_mul_inner_self_le (hu.toLp u)
    ((verticalCutoffError_memLp hfreq S).toLp (verticalCutoffError freq S))
  rw [hpair _ _ hu (verticalCutoffError_memLp hfreq S), hpair _ _ hu hu,
    hpair _ _ (verticalCutoffError_memLp hfreq S) (verticalCutoffError_memLp hfreq S)] at h
  have hc := verticalCutoffError_integral_bound hfreq hS
  simp only [← pow_two] at h
  exact h.trans (mul_le_mul_of_nonneg_left hc (integral_nonneg (fun z => sq_nonneg _)))

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_VerticalCappedGap
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The capped transverse oscillator inherits the published oscillator
projection bound, with a proved IMS cost and a proved Gaussian cutoff error. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

theorem verticalCutoff_mass (S : ℝ) (u : ℝ → ℝ)
    (hu : Continuous u) (hc : HasCompactSupport u) :
    (∫ z, (verticalInnerCutoff S z*u z)^2) +
      (∫ z, (verticalOuterCutoff S z*u z)^2) = ∫ z, u z^2 := by
  have hci : HasCompactSupport (fun z => verticalInnerCutoff S z*u z) := hc.mul_left
  have hco : HasCompactSupport (fun z => verticalOuterCutoff S z*u z) := hc.mul_left
  have hsi : HasCompactSupport (fun z => (verticalInnerCutoff S z*u z)^2) :=
    hci.comp_left (g := fun t : ℝ => t^2) (by norm_num)
  have hso : HasCompactSupport (fun z => (verticalOuterCutoff S z*u z)^2) :=
    hco.comp_left (g := fun t : ℝ => t^2) (by norm_num)
  have hi : Integrable (fun z => (verticalInnerCutoff S z*u z)^2) :=
    (((verticalInnerCutoff_smooth S).continuous.mul hu).pow 2).integrable_of_hasCompactSupport hsi
  have ho : Integrable (fun z => (verticalOuterCutoff S z*u z)^2) :=
    (((verticalOuterCutoff_smooth S).continuous.mul hu).pow 2).integrable_of_hasCompactSupport hso
  rw [← integral_add hi ho]
  apply integral_congr_ae
  filter_upwards [] with z
  linear_combination u z^2 * verticalCutoff_partition S z

theorem verticalCappedForm_outer_lower {S : ℝ} (hS : 0 < S)
    (freq : ℝ) (u : ℝ → ℝ) (hu : ContDiff ℝ 1 u) (hc : HasCompactSupport u) :
    (freq^2*S^2/8) * (∫ z, (verticalOuterCutoff S z*u z)^2) ≤
      verticalCappedForm freq S (fun z => verticalOuterCutoff S z*u z) := by
  have ho : ContDiff ℝ 1 (fun z => verticalOuterCutoff S z*u z) :=
    ((verticalOuterCutoff_smooth S).of_le (by first | simp | exact_mod_cast le_top)).mul hu
  have hi := vertical_product_integrable (verticalCapPotential freq S) _
    (by unfold verticalCapPotential; fun_prop) ho.continuous hc.mul_left
  have hlo := vertical_product_integrable (fun _ => freq^2*S^2/8) _
    continuous_const ho.continuous hc.mul_left
  have hp : (∫ z, (freq^2*S^2/8)*(verticalOuterCutoff S z*u z)^2) ≤
      ∫ z, verticalCapPotential freq S z*(verticalOuterCutoff S z*u z)^2 := by
    apply integral_mono hlo hi
    intro z
    change (freq^2*S^2/8)*(verticalOuterCutoff S z*u z)^2 ≤
      verticalCapPotential freq S z*(verticalOuterCutoff S z*u z)^2
    by_cases hz : |z| ≤ S/2
    · rw [(verticalCutoff_inner hS hz).2]
      simp
    · have hs : S^2/4 ≤ z^2 := by
        have h := (sq_le_sq₀ (by positivity : 0 ≤ S/2) (abs_nonneg z)).mpr
          (le_of_not_ge hz)
        nlinarith [sq_abs z]
      have hm : S^2/4 ≤ min (z^2) (S^2) := le_min hs (by nlinarith [sq_nonneg S])
      have hv : freq^2*S^2/8 ≤ verticalCapPotential freq S z := by
        unfold verticalCapPotential
        nlinarith [mul_le_mul_of_nonneg_left hm (sq_nonneg freq)]
      exact mul_le_mul_of_nonneg_right hv (sq_nonneg _)
  rw [integral_const_mul] at hp
  unfold verticalCappedForm
  exact hp.trans (le_add_of_nonneg_left
    (mul_nonneg (by norm_num) (integral_nonneg (fun z => sq_nonneg _))))

/-- The only input is the published harmonic-oscillator gap. The slab
cutoff, exterior barrier and localization cost are explicit actual functions. -/
theorem verticalCappedForm_projection_lower (hpublished : PublishedVerticalOscillatorGap)
    {freq S : ℝ} (hfreq : 0 < freq) (hS : 0 < S)
    (hbarrier : 3*freq/2 ≤ freq^2*S^2/8)
    (u : ℝ → ℝ) (hu : ContDiff ℝ 1 u) (hc : HasCompactSupport u) :
    (3*freq/2) * (∫ z, u z^2) -
      freq * (∫ z, (verticalInnerCutoff S z*u z)*verticalMode freq z)^2 -
      (verticalCutoffDerivativeBound S^2/2) * (∫ z, u z^2) ≤
      verticalCappedForm freq S u := by
  have hi : ContDiff ℝ 1 (fun z => verticalInnerCutoff S z*u z) :=
    ((verticalInnerCutoff_smooth S).of_le (by first | simp | exact_mod_cast le_top)).mul hu
  have hin := hpublished freq hfreq _ hi hc.mul_left
  rw [← verticalCappedForm_inner hS freq u] at hin
  have hout := (mul_le_mul_of_nonneg_right hbarrier
    (integral_nonneg (fun z => sq_nonneg (verticalOuterCutoff S z*u z)))).trans
      (verticalCappedForm_outer_lower hS freq u hu hc)
  have hm := verticalCutoff_mass S u hu.continuous hc
  have hims := verticalCappedForm_IMS freq S u hu hc
  have hcost : (∫ z, deriv (verticalCutoffAngle S) z^2*u z^2) ≤
      verticalCutoffDerivativeBound S^2 * (∫ z, u z^2) := by
    rw [← integral_const_mul]
    apply integral_mono
      (vertical_product_integrable _ u
        (((verticalCutoffAngle_smooth S).continuous_deriv (by simp)).pow 2) hu.continuous hc)
      (vertical_product_integrable _ u continuous_const hu.continuous hc)
    intro z
    change deriv (verticalCutoffAngle S) z^2*u z^2 ≤ verticalCutoffDerivativeBound S^2*u z^2
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    have hb := verticalCutoffAngle_deriv_bound hS z
    have hB : 0 ≤ verticalCutoffDerivativeBound S := by
      exact (abs_nonneg _).trans hb
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hB).mpr hb
  nlinarith

private theorem vertical_add_sq_le {η : ℝ} (hη : 0 < η) (a b : ℝ) :
    (a+b)^2 ≤ (1+η)*a^2 + (1+η⁻¹)*b^2 := by
  have he : (((1+η)*a^2 + (1+η⁻¹)*b^2) - (a+b)^2)*η = (η*a-b)^2 := by
    field_simp [hη.ne']
    ring
  have hn : 0 ≤ (((1+η)*a^2 + (1+η⁻¹)*b^2) - (a+b)^2)*η := by
    rw [he]
    exact sq_nonneg _
  exact sub_nonneg.mp (nonneg_of_mul_nonneg_left hn hη)

theorem verticalCutoff_pair_bound {freq S η : ℝ}
    (hfreq : 0 < freq) (hS : 0 < S) (hη : 0 < η)
    (u : ℝ → ℝ) (hu : MemLp u 2) :
    (∫ z, (verticalInnerCutoff S z*u z)*verticalMode freq z)^2 ≤
      (1+η)*(∫ z, u z*verticalMode freq z)^2 +
      (1+η⁻¹)*(∫ z, u z^2)*
        (verticalCutoffTailConstant freq*Real.exp (-freq*S^2/8)) := by
  have hy := vertical_add_sq_le hη (∫ z, u z*verticalMode freq z)
    ((∫ z, (verticalInnerCutoff S z*u z)*verticalMode freq z) -
      (∫ z, u z*verticalMode freq z))
  have he := mul_le_mul_of_nonneg_left (verticalCutoff_pair_error hfreq hS u hu)
    (show 0 ≤ 1+η⁻¹ by positivity)
  nlinarith

/-- The capped form has a global finite-rank lower bound. Unlike the
orthogonality corollary, this bound passes directly through approximation. -/
theorem verticalCappedForm_global_projection_lower
    (hpublished : PublishedVerticalOscillatorGap)
    {freq S η : ℝ} (hfreq : 0 < freq) (hS : 0 < S) (hη : 0 < η)
    (hbarrier : 3*freq/2 ≤ freq^2*S^2/8)
    (u : ℝ → ℝ) (hu : ContDiff ℝ 1 u) (hc : HasCompactSupport u) :
    (3*freq/2 - verticalCutoffDerivativeBound S^2/2 -
      freq*(1+η⁻¹)*verticalCutoffTailConstant freq*Real.exp (-freq*S^2/8)) *
      (∫ z, u z^2) - freq*(1+η)*(∫ z, u z*verticalMode freq z)^2 ≤
        verticalCappedForm freq S u := by
  have h := verticalCappedForm_projection_lower hpublished hfreq hS hbarrier u hu hc
  have hp := verticalCutoff_pair_bound hfreq hS hη u
    (hu.continuous.memLp_of_hasCompactSupport hc)
  have hm := mul_le_mul_of_nonneg_left hp hfreq.le
  nlinarith

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_SplitSpectralBudget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Combining the actual planar and transverse form estimates. The
projection budget removes the planar penalty from transverse excitations. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb

theorem split_form_projection_lower {freq D S Ep Ev a b : ℝ}
    (hfreq : 0 < freq) (ha : 0 ≤ a)
    {m : ℕ} (u : Fin m → PlanarPosition)
    (hsep : ∀ i j, i ≠ j → D ≤ ‖u i-u j‖)
    (hdominate : a*(1+m*localizedOverlapBound D) ≤ b)
    (f : SplitPosition → ℝ) (hf : MemLp f 2)
    (hp : Ep*(∫ p, f p^2)-a*(∫ z, ∑ i, (planarCoefficient (u i) f z)^2) ≤
      splitPlanarForm u f)
    (hv : Ev*(∫ p, f p^2)-b*(∫ r, (verticalCoefficient freq f r)^2) ≤
      splitVerticalForm freq S f) :
    (Ep+Ev-b)*(∫ p, f p^2)-a*(∑ i, (∫ p, f p*localizedMode freq (u i) p)^2) ≤
      splitPlanarForm u f+splitVerticalForm freq S f := by
  let M := ∫ p, f p^2
  let Z := ∫ r, (verticalCoefficient freq f r)^2
  let P := ∫ z, ∑ i, (planarCoefficient (u i) f z)^2
  let T := ∑ i, (∫ p, f p*localizedMode freq (u i) p)^2
  let C := 1+m*localizedOverlapBound D
  have hZ : Z ≤ M := (verticalCoefficient_contraction hfreq f hf).2
  have hP : P ≤ C*(M-Z)+T := split_projection_budget hfreq u hsep f hf
  have hpen : a*P+b*Z ≤ b*M+a*T := by
    calc
      a*P+b*Z ≤ a*(C*(M-Z)+T)+b*Z :=
        add_le_add (mul_le_mul_of_nonneg_left hP ha) le_rfl
      _ = a*C*M+(b-a*C)*Z+a*T := by ring
      _ ≤ a*C*M+(b-a*C)*M+a*T :=
        add_le_add (add_le_add le_rfl
          (mul_le_mul_of_nonneg_left hZ (sub_nonneg.mpr hdominate))) le_rfl
      _ = b*M+a*T := by ring
  change (Ep+Ev-b)*M-a*T ≤ _
  change Ep*M-a*P ≤ _ at hp
  change Ev*M-b*Z ≤ _ at hv
  nlinarith

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_SplitTestFunctions
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Classical test functions in split coordinates: compact slices and
their exact directional derivatives. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb

theorem compact_planar_slice {f : SplitPosition → ℝ} (hc : HasCompactSupport f) (z : ℝ) :
    HasCompactSupport (fun r => f (r,z)) := by
  have hK := hc.image (continuous_fst : Continuous (Prod.fst : SplitPosition → PlanarPosition))
  apply hK.of_isClosed_subset (isClosed_tsupport _)
  apply closure_minimal _ hK.isClosed
  intro r hr
  exact ⟨(r,z),subset_tsupport f hr,rfl⟩

theorem compact_vertical_slice {f : SplitPosition → ℝ} (hc : HasCompactSupport f) (r : PlanarPosition) :
    HasCompactSupport (fun z => f (r,z)) := by
  have hK := hc.image (continuous_snd : Continuous (Prod.snd : SplitPosition → ℝ))
  apply hK.of_isClosed_subset (isClosed_tsupport _)
  apply closure_minimal _ hK.isClosed
  intro z hz
  exact ⟨(r,z),subset_tsupport f hz,rfl⟩

theorem splitPlanarPartial_eq {f : SplitPosition → ℝ} (hf : ContDiff ℝ 1 f)
    (a : Fin 2) (r : PlanarPosition) (z : ℝ) :
    planarPartial (fun s => f (s,z)) (planarAxis a) r = splitPlanarPartial f a (r,z) := by
  have h := ((hf.differentiable (by norm_num)) (r,z)).hasFDerivAt.comp r
    ((hasFDerivAt_id (𝕜 := ℝ) r).prodMk (hasFDerivAt_const z r))
  unfold planarPartial splitPlanarPartial
  have he := congrArg (fun L => L (planarAxis a)) h.fderiv
  exact he

theorem splitVerticalPartial_eq {f : SplitPosition → ℝ} (hf : ContDiff ℝ 1 f)
    (r : PlanarPosition) (z : ℝ) :
    deriv (fun s => f (r,s)) z = splitVerticalPartial f (r,z) := by
  have h := ((hf.differentiable (by norm_num)) (r,z)).hasFDerivAt.comp_hasDerivAt z
    ((hasDerivAt_const z r).prodMk (hasDerivAt_id z))
  exact h.deriv

theorem compact_directional_square_integrable
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [IsLocallyFiniteMeasure μ]
    {f : E → ℝ} (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f) (e : E) :
    Integrable (fun x => (fderiv ℝ f x e)^2) μ := by
  have hd : Continuous (fderiv ℝ f) := hf.continuous_fderiv one_ne_zero
  have he : Continuous (fun x => fderiv ℝ f x e) := hd.clm_apply continuous_const
  have hs : HasCompactSupport (fun x => fderiv ℝ f x e) := hc.fderiv_apply ℝ e
  exact (he.memLp_of_hasCompactSupport hs (p := 2) (μ := μ)).integrable_sq

theorem splitPlanarPartial_square_integrable {f : SplitPosition → ℝ}
    (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f) (a : Fin 2) :
    Integrable (fun p => (splitPlanarPartial f a p)^2) :=
  compact_directional_square_integrable volume hf hc (planarAxis a,0)

theorem splitVerticalPartial_square_integrable {f : SplitPosition → ℝ}
    (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f) :
    Integrable (fun p => (splitVerticalPartial f p)^2) :=
  compact_directional_square_integrable volume hf hc (0,1)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_SplitFormIntegrals
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Integrability of the actual sliced forms. These lemmas justify applying
Fubini and integrating the published one-dimensional and planar estimates. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb

theorem split_potential_integrable {f V : SplitPosition → ℝ}
    (hf : Continuous f) (hc : HasCompactSupport f) (hV : Continuous V) :
    Integrable (fun p => V p*f p^2) := by
  have hs : HasCompactSupport (fun p => f p^2) :=
    hc.comp_left (g := fun t : ℝ => t^2) (by norm_num)
  have hp : HasCompactSupport (fun p => V p*f p^2) := hs.mul_left
  exact (hV.mul (hf.pow 2)).integrable_of_hasCompactSupport hp

theorem split_planar_slice_contDiff {f : SplitPosition → ℝ}
    (hf : ContDiff ℝ 1 f) (z : ℝ) : ContDiff ℝ 1 (fun r => f (r,z)) :=
  hf.comp (contDiff_id.prodMk contDiff_const)

theorem split_vertical_slice_contDiff {f : SplitPosition → ℝ}
    (hf : ContDiff ℝ 1 f) (r : PlanarPosition) : ContDiff ℝ 1 (fun z => f (r,z)) :=
  hf.comp (contDiff_const.prodMk contDiff_id)

theorem split_planar_mass_integral {f : SplitPosition → ℝ}
    (hf : MemLp f 2) :
    (∫ z : ℝ, ∫ r : PlanarPosition, f (r,z)^2) = ∫ p, f p^2 := by
  have hi : Integrable (fun p : SplitPosition => f p^2) (volume.prod volume) := by
    rw [← Measure.volume_eq_prod]
    exact hf.integrable_sq
  simpa only [Measure.volume_eq_prod] using (integral_prod_symm _ hi).symm

theorem split_vertical_mass_integral {f : SplitPosition → ℝ}
    (hf : MemLp f 2) :
    (∫ r : PlanarPosition, ∫ z : ℝ, f (r,z)^2) = ∫ p, f p^2 := by
  have hi : Integrable (fun p : SplitPosition => f p^2) (volume.prod volume) := by
    rw [← Measure.volume_eq_prod]
    exact hf.integrable_sq
  simpa only [Measure.volume_eq_prod] using (integral_prod _ hi).symm

theorem split_planar_form_integrable {m : ℕ} (u : Fin m → PlanarPosition)
    {f : SplitPosition → ℝ} (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f) :
    Integrable (fun z => planarTestForm (planarWellSum u) (fun r => f (r,z))) := by
  have hk : ∀ a : Fin 2, Integrable (fun z : ℝ =>
      ∫ r : PlanarPosition, (splitPlanarPartial f a (r,z))^2) := by
    intro a
    have hi : Integrable (fun p => (splitPlanarPartial f a p)^2) (volume.prod volume) := by
      rw [← Measure.volume_eq_prod]
      exact splitPlanarPartial_square_integrable hf hc a
    exact hi.integral_prod_right
  have hi : Integrable (fun p : SplitPosition => planarWellSum u p.1*f p^2)
      (volume.prod volume) := by
    rw [← Measure.volume_eq_prod]
    exact split_potential_integrable hf.continuous hc
      ((planarWellSum_continuous u).comp continuous_fst)
  have he : (fun z => planarTestForm (planarWellSum u) (fun r => f (r,z))) =
      (fun z => (1/2:ℝ)*(∑ a : Fin 2, ∫ r : PlanarPosition,
        (splitPlanarPartial f a (r,z))^2) + ∫ r, planarWellSum u r*f (r,z)^2) := by
    funext z
    simp only [planarTestForm, splitPlanarPartial_eq hf]
  rw [he]
  exact ((integrable_finsetSum _ (fun a _ => hk a)).const_mul (1/2)).add
    hi.integral_prod_right

theorem split_vertical_form_integrable (freq S : ℝ)
    {f : SplitPosition → ℝ} (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f) :
    Integrable (fun r : PlanarPosition => verticalCappedForm freq S (fun z => f (r,z))) := by
  have hk : Integrable (fun p : SplitPosition => (splitVerticalPartial f p)^2)
      (volume.prod volume) := by
    rw [← Measure.volume_eq_prod]
    exact splitVerticalPartial_square_integrable hf hc
  have hi : Integrable (fun p : SplitPosition => verticalCapPotential freq S p.2*f p^2)
      (volume.prod volume) := by
    rw [← Measure.volume_eq_prod]
    apply split_potential_integrable hf.continuous hc
    unfold verticalCapPotential
    fun_prop
  have he : (fun r : PlanarPosition => verticalCappedForm freq S (fun z => f (r,z))) =
      (fun r => (1/2:ℝ)*(∫ z : ℝ, (splitVerticalPartial f (r,z))^2) +
        ∫ z, verticalCapPotential freq S z*f (r,z)^2) := by
    funext r
    simp only [verticalCappedForm, splitVerticalPartial_eq hf]
  rw [he]
  exact (hk.integral_prod_left.const_mul (1/2)).add hi.integral_prod_left

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_SplitFormIdentity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fubini identities for the full split-coordinate kinetic and potential
forms. No domain restriction beyond compact C1 test functions is introduced. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb

theorem split_integral_planar (g : SplitPosition → ℝ) (hg : Integrable g) :
    (∫ z : ℝ, ∫ r : PlanarPosition, g (r,z)) = ∫ p, g p := by
  have hi : Integrable g (volume.prod volume) := by
    rw [← Measure.volume_eq_prod]
    exact hg
  simpa only [Measure.volume_eq_prod] using (integral_prod_symm _ hi).symm

theorem split_integral_vertical (g : SplitPosition → ℝ) (hg : Integrable g) :
    (∫ r : PlanarPosition, ∫ z : ℝ, g (r,z)) = ∫ p, g p := by
  have hi : Integrable g (volume.prod volume) := by
    rw [← Measure.volume_eq_prod]
    exact hg
  simpa only [Measure.volume_eq_prod] using (integral_prod _ hi).symm

theorem splitPlanarForm_eq {m : ℕ} (u : Fin m → PlanarPosition)
    {f : SplitPosition → ℝ} (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f) :
    splitPlanarForm u f =
      (1/2:ℝ)*(∑ a : Fin 2, ∫ p, (splitPlanarPartial f a p)^2) +
      ∫ p, planarWellSum u p.1*f p^2 := by
  have hk (a : Fin 2) : Integrable (fun z : ℝ => ∫ r : PlanarPosition,
      (splitPlanarPartial f a (r,z))^2) := by
    have hi : Integrable (fun p => (splitPlanarPartial f a p)^2) (volume.prod volume) := by
      rw [← Measure.volume_eq_prod]
      exact splitPlanarPartial_square_integrable hf hc a
    exact hi.integral_prod_right
  have hp : Integrable (fun p : SplitPosition => planarWellSum u p.1*f p^2) :=
    split_potential_integrable hf.continuous hc ((planarWellSum_continuous u).comp continuous_fst)
  have hp' : Integrable (fun z : ℝ => ∫ r : PlanarPosition, planarWellSum u r*f (r,z)^2) := by
    have hi : Integrable (fun p : SplitPosition => planarWellSum u p.1*f p^2)
        (volume.prod volume) := by
      rw [← Measure.volume_eq_prod]
      exact hp
    exact hi.integral_prod_right
  unfold splitPlanarForm
  simp_rw [planarTestForm, splitPlanarPartial_eq hf]
  rw [integral_add ((integrable_finsetSum _ (fun a _ => hk a)).const_mul _) hp',
    integral_const_mul, integral_finsetSum _ (fun a _ => hk a)]
  simp_rw [split_integral_planar _ (splitPlanarPartial_square_integrable hf hc _)]
  rw [split_integral_planar _ hp]

theorem splitVerticalForm_eq (freq S : ℝ)
    {f : SplitPosition → ℝ} (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f) :
    splitVerticalForm freq S f =
      (1/2:ℝ)*(∫ p, (splitVerticalPartial f p)^2) +
      ∫ p, verticalCapPotential freq S p.2*f p^2 := by
  have hk := splitVerticalPartial_square_integrable hf hc
  have hk' : Integrable (fun r : PlanarPosition => ∫ z : ℝ,
      (splitVerticalPartial f (r,z))^2) := by
    have hi : Integrable (fun p => (splitVerticalPartial f p)^2) (volume.prod volume) := by
      rw [← Measure.volume_eq_prod]
      exact hk
    exact hi.integral_prod_left
  have hp : Integrable (fun p : SplitPosition => verticalCapPotential freq S p.2*f p^2) := by
    apply split_potential_integrable hf.continuous hc
    unfold verticalCapPotential
    fun_prop
  have hp' : Integrable (fun r : PlanarPosition => ∫ z : ℝ, verticalCapPotential freq S z*f (r,z)^2) := by
    have hi : Integrable (fun p : SplitPosition => verticalCapPotential freq S p.2*f p^2)
        (volume.prod volume) := by
      rw [← Measure.volume_eq_prod]
      exact hp
    exact hi.integral_prod_left
  unfold splitVerticalForm
  simp_rw [verticalCappedForm, splitVerticalPartial_eq hf]
  rw [integral_add (hk'.const_mul _) hp', integral_const_mul,
    split_integral_vertical _ hk, split_integral_vertical _ hp]

theorem splitSeparableForm_eq {m : ℕ} (u : Fin m → PlanarPosition) (freq S : ℝ)
    {f : SplitPosition → ℝ} (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f) :
    splitRealForm (splitSeparablePotential u freq S) f =
      splitPlanarForm u f+splitVerticalForm freq S f := by
  have hp : Integrable (fun p : SplitPosition => planarWellSum u p.1*f p^2) :=
    split_potential_integrable hf.continuous hc ((planarWellSum_continuous u).comp continuous_fst)
  have hv : Integrable (fun p : SplitPosition => verticalCapPotential freq S p.2*f p^2) := by
    apply split_potential_integrable hf.continuous hc
    unfold verticalCapPotential
    fun_prop
  rw [splitPlanarForm_eq u hf hc, splitVerticalForm_eq freq S hf hc]
  unfold splitRealForm splitRealKinetic splitSeparablePotential
  simp_rw [add_mul]
  rw [integral_add hp hv]
  ring

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_SplitPullback
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact kinetic-energy pullback between physical Euclidean space and
planar/transverse product coordinates. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb

theorem splitPullback_contDiff {f : Position → ℝ} (hf : ContDiff ℝ 1 f) :
    ContDiff ℝ 1 (splitPullback f) :=
  hf.comp positionSplitCoordinates.symm.contDiff

theorem splitPullback_compact {f : Position → ℝ} (hc : HasCompactSupport f) :
    HasCompactSupport (splitPullback f) :=
  hc.comp_homeomorph positionSplitCoordinates.symm.toHomeomorph

theorem splitPullback_integral (f : Position → ℝ) :
    (∫ p, splitPullback f p) = ∫ x, f x := by
  rw [← positionSplitCoordinates_integral (splitPullback f)]
  simp only [splitPullback, ContinuousLinearEquiv.symm_apply_apply]

theorem splitCoordinate_planar_axis (a : Fin 2) :
    positionSplitCoordinates.symm (planarAxis a,0) =
      EuclideanSpace.single (Fin.castSucc a) (1:ℝ) := by
  apply positionSplitCoordinates.injective
  rw [ContinuousLinearEquiv.apply_symm_apply]
  apply Prod.ext
  · ext i
    fin_cases i <;> fin_cases a <;>
      simp [planarAxis, positionSplitCoordinates_fst_zero, positionSplitCoordinates_fst_one]
  · rw [positionSplitCoordinates_snd]
    fin_cases a <;> simp

theorem splitCoordinate_vertical_axis :
    positionSplitCoordinates.symm (0,1) = EuclideanSpace.single (2:Fin 3) (1:ℝ) := by
  apply positionSplitCoordinates.injective
  rw [ContinuousLinearEquiv.apply_symm_apply]
  apply Prod.ext
  · ext i
    fin_cases i <;> simp [positionSplitCoordinates_fst_zero, positionSplitCoordinates_fst_one]
  · rw [positionSplitCoordinates_snd]
    simp

theorem splitPullback_planar_partial {f : Position → ℝ} (hf : ContDiff ℝ 1 f)
    (a : Fin 2) (p : SplitPosition) :
    splitPlanarPartial (splitPullback f) a p =
      fderiv ℝ f (positionSplitCoordinates.symm p) (EuclideanSpace.single (Fin.castSucc a) 1) := by
  have h := ((hf.differentiable (by norm_num)) (positionSplitCoordinates.symm p)).hasFDerivAt.comp p
    positionSplitCoordinates.symm.hasFDerivAt
  have he := congrArg (fun L => L (planarAxis a,0)) h.fderiv
  unfold splitPlanarPartial splitPullback
  simpa only [Function.comp_def,
    ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    splitCoordinate_planar_axis] using he

theorem splitPullback_vertical_partial {f : Position → ℝ} (hf : ContDiff ℝ 1 f)
    (p : SplitPosition) :
    splitVerticalPartial (splitPullback f) p =
      fderiv ℝ f (positionSplitCoordinates.symm p) (EuclideanSpace.single (2:Fin 3) 1) := by
  have h := ((hf.differentiable (by norm_num)) (positionSplitCoordinates.symm p)).hasFDerivAt.comp p
    positionSplitCoordinates.symm.hasFDerivAt
  have he := congrArg (fun L => L ((0:PlanarPosition),(1:ℝ))) h.fderiv
  unfold splitVerticalPartial splitPullback
  simpa only [Function.comp_def,
    ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    splitCoordinate_vertical_axis] using he

theorem splitPullback_kinetic {f : Position → ℝ} (hf : ContDiff ℝ 1 f) :
    splitRealKinetic (splitPullback f) = positionRealKinetic f := by
  unfold splitRealKinetic positionRealKinetic
  simp_rw [splitPullback_planar_partial hf, splitPullback_vertical_partial hf]
  have hi (a : Fin 3) : (∫ p, (fderiv ℝ f (positionSplitCoordinates.symm p)
      (EuclideanSpace.single a 1))^2) = ∫ x, (fderiv ℝ f x (EuclideanSpace.single a 1))^2 :=
    splitPullback_integral (fun x => (fderiv ℝ f x (EuclideanSpace.single a 1))^2)
  simp_rw [hi]
  rw [Fin.sum_univ_castSucc (n := 2)]
  rfl

theorem splitPullback_form (V : Position → ℝ) {f : Position → ℝ} (hf : ContDiff ℝ 1 f) :
    splitRealForm (fun p => V (positionSplitCoordinates.symm p)) (splitPullback f) =
      positionRealForm V f := by
  unfold splitRealForm positionRealForm
  rw [splitPullback_kinetic hf]
  congr 1
  exact splitPullback_integral (fun x => V x*f x^2)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_ComplexFormSplit
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The physical complex one-electron quadratic form splits exactly into
its real and imaginary parts. Finite real-orbital penalties split as well. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb

theorem complex_norm_sq_parts (z : ℂ) : ‖z‖^2 = z.re^2+z.im^2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  ring

theorem complex_mass_parts {f : Position → ℂ} (hf : MemLp f 2) :
    (∫ x, ‖f x‖^2) = (∫ x, (f x).re^2)+(∫ x, (f x).im^2) := by
  simp_rw [complex_norm_sq_parts]
  exact integral_add hf.re.integrable_sq hf.im.integrable_sq

theorem complex_real_orbital_parts {f : Position → ℂ} {ψ : Position → ℝ}
    (hf : MemLp f 2) (hψ : MemLp ψ 2) :
    ‖∫ x, f x*(ψ x : ℂ)‖^2 =
      (∫ x, (f x).re*ψ x)^2+(∫ x, (f x).im*ψ x)^2 := by
  have hi : Integrable (fun x => f x*(ψ x : ℂ)) := hf.integrable_mul hψ.ofReal
  have hr := integral_re hi
  have hm := integral_im hi
  change (∫ x, (f x*(ψ x : ℂ)).re) = (∫ x, f x*(ψ x : ℂ)).re at hr
  change (∫ x, (f x*(ψ x : ℂ)).im) = (∫ x, f x*(ψ x : ℂ)).im at hm
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, sub_zero, zero_add] at hr hm
  rw [complex_norm_sq_parts,← hr,← hm]

theorem realPart_partial {f : Position → ℂ} (hf : ContDiff ℝ 1 f) (x e : Position) :
    fderiv ℝ (fun y => (f y).re) x e = (fderiv ℝ f x e).re := by
  exact congrArg (fun L : Position →L[ℝ] ℝ => L e)
    (Complex.reCLM.hasFDerivAt.comp x (hf.differentiable (by norm_num) x).hasFDerivAt).fderiv

theorem imagPart_partial {f : Position → ℂ} (hf : ContDiff ℝ 1 f) (x e : Position) :
    fderiv ℝ (fun y => (f y).im) x e = (fderiv ℝ f x e).im := by
  exact congrArg (fun L : Position →L[ℝ] ℝ => L e)
    (Complex.imCLM.hasFDerivAt.comp x (hf.differentiable (by norm_num) x).hasFDerivAt).fderiv

theorem positionComplexForm_parts {f : Position → ℂ}
    (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f)
    (V : Position → ℝ) (hV : Continuous V) :
    positionComplexForm V f = positionRealForm V (fun x => (f x).re) +
      positionRealForm V (fun x => (f x).im) := by
  have hr : ContDiff ℝ 1 (fun x => (f x).re) := Complex.reCLM.contDiff.comp hf
  have hi : ContDiff ℝ 1 (fun x => (f x).im) := Complex.imCLM.contDiff.comp hf
  have hrc : HasCompactSupport (fun x => (f x).re) := hc.comp_left (g := Complex.re) rfl
  have hic : HasCompactSupport (fun x => (f x).im) := hc.comp_left (g := Complex.im) rfl
  have hkr (a : Fin 3) := compact_directional_square_integrable volume hr hrc (EuclideanSpace.single a 1)
  have hki (a : Fin 3) := compact_directional_square_integrable volume hi hic (EuclideanSpace.single a 1)
  have hrr : HasCompactSupport (fun x => (f x).re^2) :=
    hrc.comp_left (g := fun t : ℝ => t^2) (by simp)
  have hii : HasCompactSupport (fun x => (f x).im^2) :=
    hic.comp_left (g := fun t : ℝ => t^2) (by simp)
  have hprc : HasCompactSupport (fun x => V x*(f x).re^2) := hrr.mul_left
  have hpic : HasCompactSupport (fun x => V x*(f x).im^2) := hii.mul_left
  have hpr : Integrable (fun x => V x*(f x).re^2) :=
    (hV.mul (hr.continuous.pow 2)).integrable_of_hasCompactSupport
      hprc
  have hpi : Integrable (fun x => V x*(f x).im^2) :=
    (hV.mul (hi.continuous.pow 2)).integrable_of_hasCompactSupport
      hpic
  have hk (a : Fin 3) : (∫ x, ‖fderiv ℝ f x (EuclideanSpace.single a 1)‖^2) =
      (∫ x, (fderiv ℝ (fun y => (f y).re) x (EuclideanSpace.single a 1))^2)+
      (∫ x, (fderiv ℝ (fun y => (f y).im) x (EuclideanSpace.single a 1))^2) := by
    rw [← integral_add (hkr a) (hki a)]
    apply integral_congr_ae
    filter_upwards [] with x
    rw [realPart_partial hf, imagPart_partial hf, complex_norm_sq_parts]
  have hp : (∫ x, V x*‖f x‖^2) = (∫ x, V x*(f x).re^2)+(∫ x, V x*(f x).im^2) := by
    rw [← integral_add hpr hpi]
    apply integral_congr_ae
    filter_upwards [] with x
    rw [complex_norm_sq_parts,mul_add]
  unfold positionComplexForm positionComplexKinetic positionRealForm positionRealKinetic
  simp_rw [hk]
  rw [Finset.sum_add_distrib,hp]
  ring

/-- Real-valued orbitals give the same finite-rank lower estimate for
arbitrary complex test functions, without a reality restriction on states. -/
theorem real_form_lower_to_complex {ι : Type*} [Fintype ι]
    (V : Position → ℝ) (hV : Continuous V) (ψ : ι → Position → ℝ)
    (hψ : ∀ i, MemLp (ψ i) 2) (E κ : ℝ)
    (hbound : ∀ g : Position → ℝ, ContDiff ℝ 1 g → HasCompactSupport g →
      E*(∫ x, g x^2)-κ*(∑ i, (∫ x, g x*ψ i x)^2) ≤ positionRealForm V g)
    (f : Position → ℂ) (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f) :
    E*(∫ x, ‖f x‖^2)-κ*(∑ i, ‖∫ x, f x*(ψ i x : ℂ)‖^2) ≤ positionComplexForm V f := by
  have hr : ContDiff ℝ 1 (fun x => (f x).re) := Complex.reCLM.contDiff.comp hf
  have hi : ContDiff ℝ 1 (fun x => (f x).im) := Complex.imCLM.contDiff.comp hf
  have hrc : HasCompactSupport (fun x => (f x).re) := hc.comp_left (g := Complex.re) rfl
  have hic : HasCompactSupport (fun x => (f x).im) := hc.comp_left (g := Complex.im) rfl
  have hfr := hbound _ hr hrc
  have hfi := hbound _ hi hic
  have hL2 : MemLp f 2 := hf.continuous.memLp_of_hasCompactSupport hc
  rw [complex_mass_parts hL2,positionComplexForm_parts hf hc V hV]
  simp_rw [complex_real_orbital_parts hL2 (hψ _)]
  rw [Finset.sum_add_distrib]
  nlinarith

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_ManufacturedSlabLower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Global comparison of the actual manufactured Coulomb field with the
separable capped oscillator and planar wells. -/

noncomputable section
namespace ContinuumCoulomb

theorem manufacturedSlabPotential_lower {rho H S freq scale δ : ℝ}
    (hrho : 0 ≤ rho) (hH : 0 < H) (hS : 0 ≤ S) (hscale : 0 ≤ scale)
    (hfreq : freq^2 = 4*Real.pi*rho) {m : ℕ} (u : Fin m → PlanarPosition)
    (hsep : ∀ i j, i ≠ j → 2 ≤ ‖u i-u j‖) (hδ : 0 ≤ δ)
    (hcoeff : ∀ i, 0 ≤ localizedCounterterm freq u i / scale ∧
      localizedCounterterm freq u i / scale ≤ δ) (x : Position) :
    planarWellSum u (positionSplitCoordinates x).1 +
      verticalCapPotential freq S (positionSplitCoordinates x).2 -
      (δ*PlanarSobolev.wellBound+6*Real.pi*rho*S^3/H) ≤
      manufacturedSlabPotential rho H S freq scale u x := by
  have hs := slabPotential_confinement hrho hH hS x
  have hw := manufacturedWellField_lower freq hscale S u hsep hδ hcoeff x
  have he : verticalCapPotential freq S (positionSplitCoordinates x).2 =
      2*Real.pi*rho*min ((x 2)^2) (S^2) := by
    rw [verticalCapPotential,hfreq,positionSplitCoordinates_snd]
    ring
  rw [he]
  unfold manufacturedSlabPotential
  linarith

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_SplitIntegratedBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual integrated form bounds. The premises name only the published
isolated-well and harmonic-oscillator spectral results. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb

theorem splitPlanarForm_projection_lower
    (hpublished : PlanarSobolev.ManufacturedPlanarGroundGap) :
    ∃ γ : ℝ, 0 < γ ∧ γ ≤ 1/4 ∧ ∀ (m : ℕ) (D η : ℝ), 8 ≤ D → 0 < η →
      ∀ u : Fin m → PlanarPosition, (∀ i j, i ≠ j → D ≤ ‖u i-u j‖) →
      ∀ f : SplitPosition → ℝ, ContDiff ℝ 1 f → HasCompactSupport f →
      ((-1/2:ℝ)+γ-planarSiteDerivativeBound D^2-
        γ*(1+η⁻¹)*m*planarSiteTailConstant*Real.exp (-(19/20:ℝ)*(D/8)))*(∫ p, f p^2) -
        γ*(1+η)*(∫ z, ∑ i, (planarCoefficient (u i) f z)^2) ≤ splitPlanarForm u f := by
  obtain ⟨γ,hγ,hsmall,hbound⟩ := planarWellSum_test_projection_bound hpublished
  refine ⟨γ,hγ,hsmall,fun m D η hD hη u hsep f hf hc => ?_⟩
  have hL2 : MemLp f 2 := hf.continuous.memLp_of_hasCompactSupport hc
  have hmass : Integrable (fun z : ℝ => ∫ r : PlanarPosition, f (r,z)^2) := by
    have hi : Integrable (fun p : SplitPosition => f p^2) (volume.prod volume) := by
      rw [← Measure.volume_eq_prod]
      exact hL2.integrable_sq
    exact hi.integral_prod_right
  have hcoeff : Integrable (fun z : ℝ => ∑ i, (planarCoefficient (u i) f z)^2) :=
    integrable_finsetSum _ (fun i _ => (planarCoefficient_contraction (u i) f hL2).1.integrable_sq)
  have hb := integral_mono
    ((hmass.const_mul _).sub (hcoeff.const_mul _))
    (split_planar_form_integrable u hf hc)
    (fun z => hbound m D η hD hη u hsep (fun r => f (r,z))
      (split_planar_slice_contDiff hf z) (compact_planar_slice hc z))
  simp only [Pi.sub_apply] at hb
  rw [integral_sub (hmass.const_mul _) (hcoeff.const_mul _),
    integral_const_mul, integral_const_mul, split_planar_mass_integral hL2] at hb
  exact hb

theorem splitVerticalForm_projection_lower
    (hpublished : PublishedVerticalOscillatorGap)
    {freq S η : ℝ} (hfreq : 0 < freq) (hS : 0 < S) (hη : 0 < η)
    (hbarrier : 3*freq/2 ≤ freq^2*S^2/8)
    (f : SplitPosition → ℝ) (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f) :
    (3*freq/2-verticalCutoffDerivativeBound S^2/2-
      freq*(1+η⁻¹)*verticalCutoffTailConstant freq*Real.exp (-freq*S^2/8))*(∫ p, f p^2) -
      freq*(1+η)*(∫ r, (verticalCoefficient freq f r)^2) ≤ splitVerticalForm freq S f := by
  have hL2 : MemLp f 2 := hf.continuous.memLp_of_hasCompactSupport hc
  have hmass : Integrable (fun r : PlanarPosition => ∫ z : ℝ, f (r,z)^2) := by
    have hi : Integrable (fun p : SplitPosition => f p^2) (volume.prod volume) := by
      rw [← Measure.volume_eq_prod]
      exact hL2.integrable_sq
    exact hi.integral_prod_left
  have hcoeff := (verticalCoefficient_contraction hfreq f hL2).1.integrable_sq
  have hb := integral_mono
    ((hmass.const_mul _).sub (hcoeff.const_mul _))
    (split_vertical_form_integrable freq S hf hc)
    (fun r => verticalCappedForm_global_projection_lower hpublished hfreq hS hη hbarrier
      (fun z => f (r,z)) (split_vertical_slice_contDiff hf r) (compact_vertical_slice hc r))
  simp only [Pi.sub_apply] at hb
  rw [integral_sub (hmass.const_mul _) (hcoeff.const_mul _),
    integral_const_mul, integral_const_mul, split_vertical_mass_integral hL2] at hb
  exact hb

/-- Conditional on the two precisely stated published spectral inputs, this
is a finite-rank lower bound for the actual split-coordinate Schrödinger form. -/
theorem split_test_spectral_lower
    (hp : PlanarSobolev.ManufacturedPlanarGroundGap)
    (hv : PublishedVerticalOscillatorGap) :
    ∃ γ : ℝ, 0 < γ ∧ γ ≤ 1/4 ∧ ∀ (m : ℕ) (D η freq S : ℝ),
      8 ≤ D → 0 < η → 0 < freq → 0 < S → 3*freq/2 ≤ freq^2*S^2/8 →
      ∀ u : Fin m → PlanarPosition, (∀ i j, i ≠ j → D ≤ ‖u i-u j‖) →
      γ*(1+η)*(1+m*localizedOverlapBound D) ≤ freq*(1+η) →
      ∀ f : SplitPosition → ℝ, ContDiff ℝ 1 f → HasCompactSupport f →
      (((-1/2:ℝ)+γ-planarSiteDerivativeBound D^2-
        γ*(1+η⁻¹)*m*planarSiteTailConstant*Real.exp (-(19/20:ℝ)*(D/8))) +
        (3*freq/2-verticalCutoffDerivativeBound S^2/2-
          freq*(1+η⁻¹)*verticalCutoffTailConstant freq*Real.exp (-freq*S^2/8)) -
        freq*(1+η))*(∫ p, f p^2) -
        γ*(1+η)*(∑ i, (∫ p, f p*localizedMode freq (u i) p)^2) ≤
        splitPlanarForm u f+splitVerticalForm freq S f := by
  obtain ⟨γ,hγ,hsmall,hplanar⟩ := splitPlanarForm_projection_lower hp
  refine ⟨γ,hγ,hsmall,fun m D η freq S hD hη hfreq hS hbarrier u hsep hdom f hf hc => ?_⟩
  exact split_form_projection_lower hfreq (mul_nonneg hγ.le (by positivity)) u hsep hdom f
    (hf.continuous.memLp_of_hasCompactSupport hc)
    (hplanar m D η hD hη u hsep f hf hc)
    (splitVerticalForm_projection_lower hv hfreq hS hη hbarrier f hf hc)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Reduction_PhysicalOneElectronLower
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
A finite-rank lower bound for the manufactured one-electron Coulomb
field, obtained from the planar and vertical spectral estimates.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb

theorem physicalSeparablePotential_continuous {m : ℕ} (u : Fin m → PlanarPosition)
    (freq S : ℝ) : Continuous (physicalSeparablePotential u freq S) := by
  unfold physicalSeparablePotential splitSeparablePotential verticalCapPotential
  exact (((planarWellSum_continuous u).comp positionSplitCoordinates.continuous.fst).add
    ((continuous_const.mul ((positionSplitCoordinates.continuous.snd.pow 2).min continuous_const))))

theorem positionRealForm_mono_shift {V W : Position → ℝ} {ε : ℝ}
    (hV : Continuous V) (hW : Continuous W) (hVW : ∀ x, W x-ε ≤ V x)
    {f : Position → ℝ} (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f) :
    positionRealForm W f-ε*(∫ x, f x^2) ≤ positionRealForm V f := by
  have hsqc : HasCompactSupport (fun x => f x^2) :=
    hc.comp_left (g := fun t : ℝ => t^2) (by simp)
  have hsq : Integrable (fun x => f x^2) :=
    (hf.continuous.pow 2).integrable_of_hasCompactSupport hsqc
  have hi (U : Position → ℝ) (hU : Continuous U) : Integrable (fun x => U x*f x^2) := by
    have hcU : HasCompactSupport (fun x => U x*f x^2) := hsqc.mul_left
    exact (hU.mul (hf.continuous.pow 2)).integrable_of_hasCompactSupport hcU
  have h := integral_mono ((hi W hW).sub (hsq.const_mul ε)) (hi V hV)
    (fun x => by
      change W x*f x^2-ε*f x^2 ≤ V x*f x^2
      nlinarith [mul_le_mul_of_nonneg_right (hVW x) (sq_nonneg (f x))])
  simp only [Pi.sub_apply] at h
  rw [integral_sub (hi W hW) (hsq.const_mul ε),integral_const_mul] at h
  unfold positionRealForm
  linarith

theorem physicalSeparable_test_lower
    (hp : PlanarSobolev.ManufacturedPlanarGroundGap)
    (hv : PublishedVerticalOscillatorGap) :
    ∃ γ : ℝ, 0 < γ ∧ γ ≤ 1/4 ∧ ∀ (m : ℕ) (D η freq S : ℝ),
      8 ≤ D → 0 < η → 0 < freq → 0 < S → 3*freq/2 ≤ freq^2*S^2/8 →
      ∀ u : Fin m → PlanarPosition, (∀ i j, i ≠ j → D ≤ ‖u i-u j‖) →
      γ*(1+η)*(1+m*localizedOverlapBound D) ≤ freq*(1+η) →
      ∀ f : Position → ℝ, ContDiff ℝ 1 f → HasCompactSupport f →
      (planarSpectralLevel γ m D η+verticalSpectralLevel freq S η-freq*(1+η))*(∫ x, f x^2) -
        γ*(1+η)*(∑ i, (∫ x, f x*continuumLocalizedMode freq (u i) x)^2) ≤
        positionRealForm (physicalSeparablePotential u freq S) f := by
  obtain ⟨γ,hγ,hsmall,hbound⟩ := split_test_spectral_lower hp hv
  refine ⟨γ,hγ,hsmall,fun m D η freq S hD hη hfreq hS hbarrier u hsep hdom f hf hc => ?_⟩
  have h := hbound m D η freq S hD hη hfreq hS hbarrier u hsep hdom
    (splitPullback f) (splitPullback_contDiff hf) (splitPullback_compact hc)
  rw [← splitSeparableForm_eq u freq S (splitPullback_contDiff hf) (splitPullback_compact hc)] at h
  have hpot : (fun p => physicalSeparablePotential u freq S (positionSplitCoordinates.symm p)) =
      splitSeparablePotential u freq S := by
    funext p
    simp only [physicalSeparablePotential,ContinuousLinearEquiv.apply_symm_apply]
  rw [← hpot,splitPullback_form _ hf] at h
  have hm : (∫ p, splitPullback f p^2) = ∫ x, f x^2 := splitPullback_integral (fun x => f x^2)
  have ho (i : Fin m) : (∫ p, splitPullback f p*localizedMode freq (u i) p) =
      ∫ x, f x*continuumLocalizedMode freq (u i) x := by
    rw [← positionSplitCoordinates_integral (fun p => splitPullback f p*localizedMode freq (u i) p)]
    simp only [splitPullback,ContinuousLinearEquiv.symm_apply_apply,continuumLocalizedMode]
  rw [hm] at h
  simp_rw [ho] at h
  exact h

/-- The actual Coulomb slab and compact counterterm well field have the
same lower bound, up to the proved finite-slab and counterterm errors. -/
theorem manufacturedSlab_test_lower_oai
    (hp : PlanarSobolev.ManufacturedPlanarGroundGap)
    (hv : PublishedVerticalOscillatorGap) :
    ∃ γ : ℝ, 0 < γ ∧ γ ≤ 1/4 ∧ ∀ (m : ℕ) (D η freq S rho H scale δ : ℝ),
      8 ≤ D → 0 < η → 0 < freq → 0 < S → 0 ≤ rho → 0 < H → 0 ≤ scale → 0 ≤ δ →
      freq^2 = 4*Real.pi*rho → 3*freq/2 ≤ freq^2*S^2/8 →
      ∀ u : Fin m → PlanarPosition, (∀ i j, i ≠ j → D ≤ ‖u i-u j‖) →
      (∀ i, 0 ≤ localizedCounterterm freq u i/scale ∧ localizedCounterterm freq u i/scale ≤ δ) →
      γ*(1+η)*(1+m*localizedOverlapBound D) ≤ freq*(1+η) →
      ∀ f : Position → ℂ, ContDiff ℝ 1 f → HasCompactSupport f →
      (planarSpectralLevel γ m D η+verticalSpectralLevel freq S η-freq*(1+η)-
        (δ*PlanarSobolev.wellBound+6*Real.pi*rho*S^3/H))*(∫ x, ‖f x‖^2) -
        γ*(1+η)*(∑ i, ‖∫ x, f x*(continuumLocalizedMode freq (u i) x : ℂ)‖^2) ≤
        positionComplexForm (manufacturedSlabPotential rho H S freq scale u) f := by
  obtain ⟨γ,hγ,hsmall,hbound⟩ := physicalSeparable_test_lower hp hv
  refine ⟨γ,hγ,hsmall,fun m D η freq S rho H scale δ hD hη hfreq hS hrho hH hscale hδ
    hrelation hbarrier u hsep hcoeff hdom f hf hc => ?_⟩
  have hseparate (i j : Fin m) (hij : i ≠ j) : 2 ≤ ‖u i-u j‖ := by
    linarith [hsep i j hij]
  apply real_form_lower_to_complex _ (manufacturedSlabPotential_continuous hrho hH.le hS.le _ _ u)
    (fun i => continuumLocalizedMode freq (u i))
    (fun i => continuumLocalizedMode_memLp hfreq (u i)) _ _ ?_ f hf hc
  intro g hg hgc
  have hs := hbound m D η freq S hD hη hfreq hS hbarrier u hsep hdom g hg hgc
  have hvw := positionRealForm_mono_shift
    (manufacturedSlabPotential_continuous hrho hH.le hS.le _ _ u)
    (physicalSeparablePotential_continuous u freq S)
    (manufacturedSlabPotential_lower hrho hH hS.le hscale hrelation u hseparate hδ hcoeff) hg hgc
  nlinarith

end ContinuumCoulomb

end

end OAI
end

theorem solution : type_of% @OAI.ContinuumCoulomb.manufacturedSlab_test_lower_oai := @OAI.ContinuumCoulomb.manufacturedSlab_test_lower_oai
