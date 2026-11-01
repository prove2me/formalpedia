-- Prove2me | solution 1 for OAI.ContinuumCoulomb.exists_actual_oneBody_parameters
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T21:23:33.556641+00:00
-- url     : https://prove2.me/submissions/7378ad7d-e9c9-4cbf-ae8f-76f0f59c9100

import Mathlib
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range
import Mathlib.Analysis.CStarAlgebra.GelfandNaimarkSegal
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.Calculus.BumpFunction.Basic
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.Bounds
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
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Convolution
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Operator.Compact
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
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
import Mathlib.MeasureTheory.Function.Jacobian
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
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Probability.Kernel.CondDistrib
import Mathlib.Probability.Kernel.Defs
import Mathlib.Probability.Moments.Variance
import Mathlib.Tactic
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Algebra.LinearMapCompletion
import Mathlib.Topology.Algebra.Module.Determinant
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.Algebra.Support
import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
import Mathlib.Topology.MetricSpace.Antilipschitz
import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.UniformSpace.Cauchy
import Mathlib.Topology.UniformSpace.HeineCantor
import Definitions.Def_ContinuumCoulombHardness
import Definitions.Def_OAIQ092A010

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

theorem normalizedPlanarMode_normalized : (∫ r, normalizedPlanarMode r ^ 2) = 1 := by
  simp_rw [normalizedPlanarMode, div_pow]
  rw [integral_div, Real.sq_sqrt planarResolventMode_square_integral_positive.le,
    div_self planarResolventMode_square_integral_positive.ne']

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

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_PlanarNormalized
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Analytic identities for the actual normalized planar mode. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb

theorem planarLaplacian_const_mul {f : PlanarPosition → ℝ} (hf : ContDiff ℝ 2 f)
    (c : ℝ) (r : PlanarPosition) :
    planarLaplacian (fun x => c * f x) r = c * planarLaplacian f r := by
  have h (e : PlanarPosition) : planarPartial (fun x => c * f x) e =
      fun x => c * planarPartial f e x :=
    funext (planarPartial_const_mul (hf.of_le (by norm_num)) c e)
  simp only [planarLaplacian]
  simp_rw [h]
  simp_rw [planarPartial_const_mul (planarPartial_C1 hf _)]
  exact (Finset.mul_sum _ _ _).symm

theorem normalizedPlanarMode_eigen_equation (r : PlanarPosition) :
    planarLaplacian normalizedPlanarMode r =
      (2 * manufacturedPlanarWell r + 1) * normalizedPlanarMode r := by
  rw [normalizedPlanarMode_eq_const_mul,
    planarLaplacian_const_mul (planarResolventMode_C7.of_le (by norm_num)),
    manufacturedPlanarWell_eigen_equation]
  ring

theorem planarPartial_translate (f : PlanarPosition → ℝ) (u e r : PlanarPosition) :
    planarPartial (fun x => f (x - u)) e r = planarPartial f e (r - u) := by
  simp only [planarPartial, fderiv_comp_sub]

theorem planarLaplacian_translate (f : PlanarPosition → ℝ) (u r : PlanarPosition) :
    planarLaplacian (fun x => f (x - u)) r = planarLaplacian f (r - u) := by
  have h (e : PlanarPosition) : planarPartial (fun x => f (x - u)) e =
      fun x => planarPartial f e (x - u) := funext (planarPartial_translate f u e)
  simp only [planarLaplacian]
  simp_rw [h, planarPartial_translate]

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

theorem verticalMode_second_hasDerivAt (freq z : ℝ) :
    HasDerivAt (deriv (verticalMode freq))
      ((freq ^ 2 * z ^ 2 - freq) * verticalMode freq z) z := by
  rw [show deriv (verticalMode freq) = (fun x => -freq * x * verticalMode freq x)
    from funext (verticalMode_deriv freq)]
  refine (((hasDerivAt_id z).const_mul (-freq)).mul (verticalMode_hasDerivAt freq z)).congr_deriv ?_
  · simp only [id_eq]
    ring

theorem verticalMode_second_deriv (freq z : ℝ) :
    deriv (deriv (verticalMode freq)) z = (freq ^ 2 * z ^ 2 - freq) * verticalMode freq z :=
  (verticalMode_second_hasDerivAt freq z).deriv

theorem verticalMode_normalized {freq : ℝ} (hfreq : 0 < freq) :
    (∫ z : ℝ, verticalMode freq z ^ 2) = 1 := by
  simp_rw [verticalMode_square hfreq]
  rw [integral_div, integral_gaussian, div_self]
  exact (Real.sqrt_pos.mpr (div_pos Real.pi_pos hfreq)).ne'

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_LocalizedModes
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual localized modes in planar/transverse coordinates. The measure is
the product of planar Euclidean volume and one-dimensional Lebesgue measure.
The split Laplacian below is the sum of the three coordinate derivatives. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

theorem localizedMode_normalized {freq : ℝ} (hfreq : 0 < freq)
    (u : PlanarPosition) : (∫ p, localizedMode freq u p ^ 2) = 1 := by
  simp_rw [localizedMode, mul_pow]
  rw [Measure.volume_eq_prod,
    integral_prod_mul (fun r => normalizedPlanarMode (r - u) ^ 2)
      (fun z => verticalMode freq z ^ 2),
    integral_sub_right_eq_self (fun r => normalizedPlanarMode r ^ 2) u,
    normalizedPlanarMode_normalized, verticalMode_normalized hfreq, one_mul]

theorem localizedMode_planar_laplacian (freq : ℝ) (u : PlanarPosition) (p : SplitPosition) :
    planarLaplacian (fun r => localizedMode freq u (r, p.2)) p.1 =
      (2 * manufacturedPlanarWell (p.1 - u) + 1) * localizedMode freq u p := by
  have hc : ContDiff ℝ 2 (fun r => normalizedPlanarMode (r - u)) :=
    (normalizedPlanarMode_C7.comp (contDiff_id.sub contDiff_const)).of_le (by norm_num)
  change planarLaplacian (fun r => normalizedPlanarMode (r - u) * verticalMode freq p.2) p.1 = _
  rw [show (fun r => normalizedPlanarMode (r - u) * verticalMode freq p.2) =
    (fun r => verticalMode freq p.2 * normalizedPlanarMode (r - u))
    from funext (fun r => mul_comm _ _), planarLaplacian_const_mul hc,
    planarLaplacian_translate, normalizedPlanarMode_eigen_equation]
  simp only [localizedMode]
  ring

theorem localizedMode_vertical_second (freq : ℝ) (u : PlanarPosition) (p : SplitPosition) :
    deriv (deriv (fun z => localizedMode freq u (p.1, z))) p.2 =
      (freq ^ 2 * p.2 ^ 2 - freq) * localizedMode freq u p := by
  simp only [localizedMode, deriv_const_mul_field', deriv_const_mul_field,
    verticalMode_second_deriv]
  ring

theorem localizedMode_eigen_equation (freq : ℝ) (u : PlanarPosition) (p : SplitPosition) :
    -(1 / 2 : ℝ) * splitLaplacian (localizedMode freq u) p +
      localizedPotential freq u p * localizedMode freq u p =
        ((-1 / 2 : ℝ) + freq / 2) * localizedMode freq u p := by
  simp only [splitLaplacian, localizedMode_planar_laplacian,
    localizedMode_vertical_second, localizedPotential]
  ring

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

theorem positionSplitCoordinates_norm_sq (x : Position) :
    ‖x‖ ^ 2 = ‖(positionSplitCoordinates x).1‖ ^ 2 +
      (positionSplitCoordinates x).2 ^ 2 := by
  change ‖x‖ ^ 2 = ‖(positionSplitIsometry x).fst‖ ^ 2 + (positionSplitIsometry x).snd ^ 2
  have h := WithLp.prod_norm_sq_eq_of_L2 (positionSplitIsometry x)
  rw [positionSplitIsometry.norm_map] at h
  simpa only [Real.norm_eq_abs, sq_abs] using h

theorem continuumLocalizedMode_normalized {freq : ℝ} (hfreq : 0 < freq)
    (u : PlanarPosition) : (∫ x : Position, continuumLocalizedMode freq u x ^ 2) = 1 := by
  change (∫ x : Position, (localizedMode freq u (positionSplitCoordinates x)) ^ 2) = 1
  rw [positionSplitCoordinates_integral (fun p => localizedMode freq u p ^ 2),
    localizedMode_normalized hfreq]

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.CoulombRadii_Variational_CorrectionDensity
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

theorem translated_kernel_indicator_eq (x : Position) (r : ℝ) :
    (Metric.ball x r).indicator (fun y => coulombKernel (x-y)) =
      (fun y => (Metric.ball (0 : Position) r).indicator coulombKernel (x-y)) := by
  ext y
  have hh : x-y ∈ Metric.ball (0 : Position) r ↔ y ∈ Metric.ball x r := by
    simp only [Metric.mem_ball, dist_eq_norm, sub_zero, norm_sub_rev]
  by_cases hy : y ∈ Metric.ball x r <;> simp [hh, hy]

theorem translated_kernel_indicator_integrable (x : Position) (r : ℝ) :
    Integrable ((Metric.ball x r).indicator (fun y => coulombKernel (x-y))) := by
  rw [translated_kernel_indicator_eq]
  exact (integrable_comp_sub_left
    ((Metric.ball (0 : Position) r).indicator coulombKernel) x).mpr
      ((coulombKernel_integrableOn_ball r).integrable_indicator measurableSet_ball)

theorem translated_kernel_indicator_integral (x : Position) (r : ℝ) :
    (∫ y, (Metric.ball x r).indicator (fun y => coulombKernel (x-y)) y) =
      kernelBallMass r := by
  rw [translated_kernel_indicator_eq, integral_sub_left_eq_self,
    integral_indicator measurableSet_ball]
  rfl

theorem kernelBallMass_nonneg (r : ℝ) : 0 ≤ kernelBallMass r :=
  integral_nonneg (fun _ => coulombKernel_nonneg _)

theorem potential_integrable_and_bound {ρ : Position → ℝ} {x : Position} {r A : ℝ}
    (hρ : Integrable ρ) (hpos : ∀ y, 0 ≤ ρ y) (hr : 0 < r)
    (hloc : ∀ y ∈ Metric.ball x r, ρ y ≤ A) :
    Integrable (fun y => coulombKernel (x-y)*ρ y) ∧
      potentialOf ρ x ≤ A*kernelBallMass r+r⁻¹*(∫ y, ρ y) := by
  let b : Position → ℝ := fun y =>
    A*((Metric.ball x r).indicator (fun y => coulombKernel (x-y))) y+r⁻¹*ρ y
  have hb : Integrable b :=
    ((translated_kernel_indicator_integrable x r).const_mul A).add (hρ.const_mul r⁻¹)
  have hdom : ∀ y, coulombKernel (x-y)*ρ y ≤ b y := by
    intro y
    by_cases hy : y ∈ Metric.ball x r
    · simp only [b, Set.indicator_of_mem hy]
      exact (mul_le_mul_of_nonneg_left (hloc y hy) (coulombKernel_nonneg _)).trans
        (by nlinarith [mul_nonneg (inv_nonneg.mpr hr.le) (hpos y)])
    · simp only [b, Set.indicator_of_notMem hy, mul_zero, zero_add]
      have hd : r ≤ ‖x-y‖ := by
        simpa only [Metric.mem_ball, not_lt, dist_eq_norm, norm_sub_rev] using hy
      exact mul_le_mul_of_nonneg_right (inv_anti₀ hr hd) (hpos y)
  have hprod : AEStronglyMeasurable (fun y => coulombKernel (x-y)*ρ y) volume :=
    ((measurable_coulombKernel.comp (measurable_const.sub measurable_id)).aestronglyMeasurable).mul
      hρ.aestronglyMeasurable
  have hi : Integrable (fun y => coulombKernel (x-y)*ρ y) := hb.mono' hprod
    (Filter.Eventually.of_forall (fun y => by
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (coulombKernel_nonneg _) (hpos y))]
      exact hdom y))
  refine ⟨hi, (integral_mono hi hb hdom).trans_eq ?_⟩
  dsimp [b]
  rw [integral_add ((translated_kernel_indicator_integrable x r).const_mul A) (hρ.const_mul r⁻¹),
    integral_const_mul, integral_const_mul, translated_kernel_indicator_integral]

theorem potentialOf_nonneg {ρ : Position → ℝ} (hρ : ∀ y, 0 ≤ ρ y) (x : Position) :
    0 ≤ potentialOf ρ x := integral_nonneg (fun y => mul_nonneg (coulombKernel_nonneg _) (hρ y))

end NeutralAtom
end
end
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

theorem localizedDensity_mass {freq : ℝ} (hfreq : 0 < freq) (u : PlanarPosition) :
    (∫ x, localizedDensity freq u x) = 1 := continuumLocalizedMode_normalized hfreq u

theorem localizedDensity_coulomb_integrable_bound {freq : ℝ} (hfreq : 0 < freq)
    (u : PlanarPosition) (x : Position) :
    Integrable (fun y => NeutralAtom.coulombKernel (x - y) * localizedDensity freq u y) ∧
      NeutralAtom.potentialOf (localizedDensity freq u) x ≤ localizedPotentialBound freq := by
  have h := NeutralAtom.bounded_density_convolution NeutralAtom.measurable_coulombKernel
    NeutralAtom.coulombKernel_nonneg (NeutralAtom.coulombKernel_integrableOn_ball 1)
    (fun _ => NeutralAtom.coulombKernel_le_one) (localizedDensity_integrable hfreq u)
    (localizedDensity_nonnegative freq u) (localizedDensity_bound hfreq u) x
  simpa only [localizedDensity_mass hfreq u, localizedPotentialBound, NeutralAtom.kernelBallMass,
    NeutralAtom.potentialOf] using h

theorem localizedDensity_potential_nonnegative (freq : ℝ) (u : PlanarPosition) (x : Position) :
    0 ≤ NeutralAtom.potentialOf (localizedDensity freq u) x :=
  integral_nonneg (fun _ => mul_nonneg (NeutralAtom.coulombKernel_nonneg _)
    (localizedDensity_nonnegative freq u _))

theorem localizedDensity_potential_continuous {freq : ℝ} (hfreq : 0 < freq)
    (u : PlanarPosition) : Continuous (NeutralAtom.potentialOf (localizedDensity freq u)) :=
  NeutralAtom.potentialOf_continuous (localizedDensity_integrable hfreq u)
    (localizedDensity_nonnegative freq u) (localizedDensity_bound hfreq u)

theorem localizedCoulombCoeff_integrable {freq : ℝ} (hfreq : 0 < freq)
    (u v : PlanarPosition) :
    Integrable (fun x => localizedDensity freq u x *
      NeutralAtom.potentialOf (localizedDensity freq v) x) := by
  apply (localizedDensity_integrable hfreq u).mul_bdd (c := localizedPotentialBound freq)
    (localizedDensity_potential_continuous hfreq v).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun x => by
    rw [Real.norm_of_nonneg (localizedDensity_potential_nonnegative freq v x)]
    exact (localizedDensity_coulomb_integrable_bound hfreq v x).2)

theorem localizedCoulombCoeff_nonnegative (freq : ℝ) (u v : PlanarPosition) :
    0 ≤ localizedCoulombCoeff freq u v :=
  integral_nonneg (fun x => mul_nonneg (localizedDensity_nonnegative freq u x)
    (localizedDensity_potential_nonnegative freq v x))

theorem localizedCoulombCoeff_le {freq : ℝ} (hfreq : 0 < freq) (u v : PlanarPosition) :
    localizedCoulombCoeff freq u v ≤ localizedPotentialBound freq := by
  have hi := (localizedDensity_integrable hfreq u).mul_const (localizedPotentialBound freq)
  have h := integral_mono (localizedCoulombCoeff_integrable hfreq u v) hi
    (fun x => mul_le_mul_of_nonneg_left
      (localizedDensity_coulomb_integrable_bound hfreq v x).2
      (localizedDensity_nonnegative freq u x))
  simpa only [integral_mul_const, localizedDensity_mass hfreq u, one_mul,
    localizedCoulombCoeff] using h

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_LocalizedCoulombTranslation
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Direct Coulomb coefficients as actual translated-density profiles. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

theorem planarCenter_norm (u : PlanarPosition) : ‖planarCenter u‖ = ‖u‖ := by
  have h := positionSplitCoordinates_norm_sq (planarCenter u)
  simp only [planarCenter, ContinuousLinearEquiv.apply_symm_apply, zero_pow (by norm_num : 2 ≠ 0),
    add_zero] at h
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h

theorem continuumLocalizedMode_translate (freq : ℝ) (u : PlanarPosition) (x : Position) :
    continuumLocalizedMode freq u x = continuumLocalizedMode freq 0 (x - planarCenter u) := by
  simp only [continuumLocalizedMode, localizedMode, map_sub, planarCenter,
    ContinuousLinearEquiv.apply_symm_apply, Prod.fst_sub, Prod.snd_sub, sub_zero]

theorem localizedDensity_translate (freq : ℝ) (u : PlanarPosition) (x : Position) :
    localizedDensity freq u x = localizedDensity freq 0 (x - planarCenter u) := by
  simp only [localizedDensity, continuumLocalizedMode_translate freq u]

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
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_LocalizedHigherMoments
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The spatial moments needed to control the finite-slab
operator residual. All moments refer to the actual normalized orbital density. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

private theorem polynomial_exponential_bound (k : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    t^k*Real.exp (-t/2) ≤ (2:ℝ)^k*(k.factorial:ℝ) := by
  have hf : 0 < (k.factorial : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos k)
  have he := Real.pow_div_factorial_le_exp (t/2) (by positivity : 0 ≤ t/2) k
  have hid : ((t/2)^k/(k.factorial:ℝ))*((2:ℝ)^k*(k.factorial:ℝ)) = t^k := by
    rw [div_pow]
    field_simp
  have h := mul_le_mul_of_nonneg_right he
    (show 0 ≤ (2:ℝ)^k*(k.factorial:ℝ) by positivity)
  rw [hid] at h
  have h' := mul_le_mul_of_nonneg_right h (Real.exp_pos (-t/2)).le
  have hc : (Real.exp (t/2)*((2:ℝ)^k*(k.factorial:ℝ)))*Real.exp (-t/2) =
      (2:ℝ)^k*(k.factorial:ℝ) := by
    rw [mul_right_comm,← Real.exp_add]
    rw [show t/2 + -t/2 = 0 by ring, Real.exp_zero, one_mul]
  exact h'.trans_eq hc

theorem normalizedPlanarMode_norm_moment_integrable (k : ℕ) :
    Integrable (fun r : PlanarPosition => ‖r‖^k*normalizedPlanarMode r^2) := by
  let C := planarExponentialConstant (1/2)^2*((2:ℝ)^k*(k.factorial:ℝ))
  have hmajor := (planar_exp_norm_integrable (by norm_num : (0:ℝ)<1/2)).const_mul C
  have hraw : Integrable (fun r : PlanarPosition => ‖r‖^k*planarResolventMode r^2) := by
    apply hmajor.mono'
      ((continuous_norm.pow k).mul (planarResolventMode_C7.continuous.pow 2)).aestronglyMeasurable
    filter_upwards [] with r
    change ‖‖r‖^k*planarResolventMode r^2‖ ≤ C*Real.exp (-(1/2:ℝ)*‖r‖)
    rw [Real.norm_of_nonneg (mul_nonneg (pow_nonneg (norm_nonneg _) _) (sq_nonneg _))]
    have hm := pow_le_pow_left₀ (planarResolventMode_positive r).le
      (planarResolventMode_exponential_envelope (by norm_num : (0:ℝ)≤1/2)
        (by norm_num : (1/2:ℝ)<1) r) 2
    rw [mul_pow] at hm
    have hex : Real.exp (-(1/2:ℝ)*‖r‖)^2 =
        Real.exp (-‖r‖/2)*Real.exp (-(1/2:ℝ)*‖r‖) := by
      rw [pow_two]
      congr 1
      congr 1
      ring
    rw [hex] at hm
    calc
      _ ≤ ‖r‖^k*(planarExponentialConstant (1/2)^2*
          (Real.exp (-‖r‖/2)*Real.exp (-(1/2:ℝ)*‖r‖))) :=
        mul_le_mul_of_nonneg_left hm (pow_nonneg (norm_nonneg _) _)
      _ = (planarExponentialConstant (1/2)^2*(‖r‖^k*Real.exp (-‖r‖/2)))*
          Real.exp (-(1/2:ℝ)*‖r‖) := by ring
      _ ≤ C*Real.exp (-(1/2:ℝ)*‖r‖) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (polynomial_exponential_bound k (norm_nonneg r))
            (sq_nonneg _)) (Real.exp_pos _).le
  simp_rw [normalizedPlanarMode,div_pow,← mul_div_assoc]
  exact hraw.div_const _

private theorem localizedDensity_even_moment_integrable {freq : ℝ} (hfreq : 0 < freq)
    (k : ℕ) : Integrable (fun x : Position => ‖x‖^(2*k)*localizedDensity freq 0 x) := by
  have hp := (normalizedPlanarMode_norm_moment_integrable (2*k)).mul_prod (verticalMode_square_integrable hfreq)
  have hz := normalizedPlanarMode_square_integrable.mul_prod (verticalMode_moment_integrable hfreq (2*k))
  have hi : Integrable (fun p : SplitPosition => (‖p.1‖^2+p.2^2)^k*localizedMode freq 0 p^2) := by
    apply ((hp.add hz).const_mul ((2:ℝ)^(k-1))).mono'
      ((((continuous_fst.norm.pow 2).add (continuous_snd.pow 2)).pow k).mul
        ((localizedMode_C7 freq 0).continuous.pow 2)).aestronglyMeasurable
    filter_upwards [] with p
    change ‖(‖p.1‖^2+p.2^2)^k*localizedMode freq 0 p^2‖ ≤ _
    rw [Real.norm_of_nonneg (mul_nonneg (pow_nonneg (by positivity) _) (sq_nonneg _))]
    have h : (‖p.1‖^2+p.2^2)^k ≤ (2:ℝ)^(k-1)*(‖p.1‖^(2*k)+p.2^(2*k)) := by
      simpa only [← pow_mul] using add_pow_le (sq_nonneg ‖p.1‖) (sq_nonneg p.2) k
    have hm := mul_le_mul_of_nonneg_right h (sq_nonneg (localizedMode freq 0 p))
    convert hm using 1
    all_goals try with_reducible_and_instances rfl
    simp only [localizedMode,sub_zero,mul_pow,Pi.add_apply]
    ring
  have ht := positionSplitCoordinates_measurePreserving.integrable_comp_of_integrable hi
  convert ht using 1
  all_goals try with_reducible_and_instances rfl
  funext x
  simp only [Function.comp_apply,localizedDensity,continuumLocalizedMode]
  rw [pow_mul, positionSplitCoordinates_norm_sq]

theorem localizedDensity_fourth_moment_integrable {freq : ℝ} (hfreq : 0 < freq) :
    Integrable (fun x : Position => ‖x‖^4*localizedDensity freq 0 x) :=
  localizedDensity_even_moment_integrable hfreq 2

theorem localizedDensity_eighth_moment_integrable {freq : ℝ} (hfreq : 0 < freq) :
    Integrable (fun x : Position => ‖x‖^8*localizedDensity freq 0 x) :=
  localizedDensity_even_moment_integrable hfreq 4

/-- This moment absorbs the polynomial growth of the finite slab's global
potential bound when the horizontal radius is the fourth power of its thickness. -/
theorem localizedDensity_twentyFourth_moment_integrable {freq : ℝ} (hfreq : 0 < freq) :
    Integrable (fun x : Position => ‖x‖^24*localizedDensity freq 0 x) :=
  localizedDensity_even_moment_integrable hfreq 12

/-- A wider horizontal slab is needed for simultaneous nuclear cubature and
compressed-energy accuracy. This moment absorbs its polynomial growth. -/
theorem localizedDensity_seventySecond_moment_integrable {freq : ℝ} (hfreq : 0 < freq) :
    Integrable (fun x : Position => ‖x‖^72*localizedDensity freq 0 x) :=
  localizedDensity_even_moment_integrable hfreq 36

end ContinuumCoulomb

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
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Nuclei_DensitySynthesis
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Nonnegative continuous-density synthesis for the unit-charge construction

The density is the uniform slab plus `ΔV/(4π)`. Compact support of `V`
inside the slab makes its attractive Coulomb field exactly the slab field
plus `V`. A pointwise Laplacian bound makes the density nonnegative.
Only C² regularity is required, as the manuscript's manufactured well is
finitely smooth.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb

theorem slabDensity_integral (rho H S : ℝ) :
    (∫ x, slabDensity rho H S x) = volume.real (slabDomain H S) * rho := by
  exact integral_indicator_const rho (slabDomain_isClosed H S).measurableSet

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
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_PlanarHopping
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.planarHeatResolventPrimitive_zero _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual positive contact hopping integral. Its Lipschitz control is
inherited from the compact forcing through the mass-one resolvent kernel. -/

noncomputable section
open MeasureTheory
open scoped NNReal
namespace ContinuumCoulomb

theorem planarAxis_zero_norm : ‖planarAxis 0‖ = 1 := by
  simp [planarAxis]

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_PlanarRadial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Rotation/reflection invariance of the actual manufactured planar data.
The hopping between arbitrary translated centers depends only on distance. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

theorem planarForcing_isometry (L : PlanarPosition ≃ₗᵢ[ℝ] PlanarPosition) (r : PlanarPosition) :
    planarForcing (L r) = planarForcing r := by
  simp only [planarForcing, L.norm_map]

theorem planarResolventKernel_isometry (L : PlanarPosition ≃ₗᵢ[ℝ] PlanarPosition)
    (r : PlanarPosition) : planarResolventKernel (L r) = planarResolventKernel r := by
  simp only [planarResolventKernel, planarResolventIntegrand, planarHeatKernel, L.norm_map]

theorem planarResolventMode_isometry (L : PlanarPosition ≃ₗᵢ[ℝ] PlanarPosition)
    (r : PlanarPosition) : planarResolventMode (L r) = planarResolventMode r := by
  unfold planarResolventMode
  rw [← MeasureTheory.integral_comp L
    (fun b => planarResolventKernel b * planarForcing (L r - b))]
  apply integral_congr_ae
  filter_upwards [] with b
  rw [planarResolventKernel_isometry, ← L.map_sub, planarForcing_isometry]

theorem planarHoppingAt_isometry (L : PlanarPosition ≃ₗᵢ[ℝ] PlanarPosition)
    (u : PlanarPosition) : planarHoppingAt (L u) = planarHoppingAt u := by
  unfold planarHoppingAt
  congr 1
  rw [← MeasureTheory.integral_comp L
    (fun r => planarForcing r * planarResolventMode (r - L u))]
  apply integral_congr_ae
  filter_upwards [] with r
  rw [planarForcing_isometry, ← L.map_sub, planarResolventMode_isometry]

theorem planarHoppingAt_norm (u : PlanarPosition) : planarHoppingAt u = planarHopping ‖u‖ := by
  have hn : ‖‖u‖ • planarAxis 0‖ = ‖u‖ := by
    rw [norm_smul, planarAxis_zero_norm, mul_one, Real.norm_of_nonneg (norm_nonneg u)]
  have h := planarHoppingAt_isometry ((ℝ ∙ (‖u‖ • planarAxis 0 - u))ᗮ.reflection)
    (‖u‖ • planarAxis 0)
  rw [Submodule.reflection_sub hn] at h
  exact h

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_PlanarWellMatrix
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual well matrix elements. The well at the first orbital center gives
exactly the distance-dependent hopping; a well far from both centers gives
an error decaying at rate 1.9. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

theorem planarWellMatrix_integrable (u v w : PlanarPosition) :
    Integrable (fun r => normalizedPlanarMode (r - u) * manufacturedPlanarWell (r - w) *
      normalizedPlanarMode (r - v)) := by
  apply (((normalizedPlanarMode_C7.continuous.comp (continuous_id.sub continuous_const)).mul
    (manufacturedPlanarWell_C7.continuous.comp (continuous_id.sub continuous_const))).mul
    (normalizedPlanarMode_C7.continuous.comp (continuous_id.sub continuous_const))).integrable_of_hasCompactSupport
  exact (manufacturedPlanarWell_hasCompactSupport.comp_homeomorph (Homeomorph.subRight w)).mul_left.mul_right

theorem planarWellMatrix_hopping (u v : PlanarPosition) :
    planarWellMatrix u v u = -planarHopping ‖u - v‖ := by
  let S : ℝ := ∫ r, planarResolventMode r ^ 2
  have hS : 0 < S := planarResolventMode_square_integral_positive
  have hsqrt : Real.sqrt S ≠ 0 := (Real.sqrt_pos.mpr hS).ne'
  have hpt (r : PlanarPosition) :
      normalizedPlanarMode (r - u) * manufacturedPlanarWell (r - u) * normalizedPlanarMode (r - v) =
        -(1 / (2 * S)) * (planarForcing (r - u) * planarResolventMode (r - v)) := by
    unfold normalizedPlanarMode manufacturedPlanarWell
    change (planarResolventMode (r - u) / Real.sqrt S) *
      (-planarForcing (r - u) / (2 * planarResolventMode (r - u))) *
      (planarResolventMode (r - v) / Real.sqrt S) = _
    field_simp [hsqrt, (planarResolventMode_positive (r - u)).ne', hS.ne']
    rw [Real.sq_sqrt hS.le]
    ring
  have hi : (∫ r, planarForcing (r - u) * planarResolventMode (r - v)) =
      ∫ r, planarForcing r * planarResolventMode (r - (v - u)) := by
    have h := integral_sub_right_eq_self (μ := volume)
      (fun r => planarForcing r * planarResolventMode (r - (v - u))) u
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    congr 1
    funext r
    rw [show r - u - (v - u) = r - v by abel]
  unfold planarWellMatrix
  simp_rw [hpt]
  rw [integral_const_mul, hi, norm_sub_rev u v, ← planarHoppingAt_norm (v - u)]
  simp only [planarHoppingAt]
  change -(1 / (2 * S)) * _ = -(_ / (2 * S))
  ring

theorem planarWellMatrixConstant_nonnegative : 0 ≤ planarWellMatrixConstant :=
  mul_nonneg (mul_nonneg (sq_nonneg _) (Real.exp_pos _).le)
    (integral_nonneg (fun _ => abs_nonneg _))

theorem planarWellMatrix_two_far {D : ℝ} (u v w : PlanarPosition)
    (hu : D ≤ ‖u - w‖) (hv : D ≤ ‖v - w‖) :
    |planarWellMatrix u v w| ≤ planarWellMatrixConstant * Real.exp (-(19 / 10 : ℝ) * D) := by
  let C := normalizedPlanarExponentialConstant (19 / 20)
  have hC : 0 ≤ C := (normalizedPlanarExponentialConstant_positive (by norm_num) (by norm_num)).le
  let B := C ^ 2 * Real.exp ((19 / 10 : ℝ) - (19 / 10 : ℝ) * D)
  have hpt (r : PlanarPosition) :
      ‖normalizedPlanarMode (r - u) * manufacturedPlanarWell (r - w) * normalizedPlanarMode (r - v)‖ ≤
        B * |manufacturedPlanarWell (r - w)| := by
    by_cases hw : manufacturedPlanarWell (r - w) = 0
    · simp only [hw, mul_zero, zero_mul, norm_zero, abs_zero, le_refl]
    have hs : ‖r - w‖ ≤ 1 := by
      have hm := (manufacturedPlanarWell_support.trans planarForcing_support)
        (subset_tsupport _ (show r - w ∈ Function.support manufacturedPlanarWell from hw))
      simpa only [Metric.mem_closedBall, dist_zero_right] using hm
    have htu : ‖u - w‖ ≤ ‖r - u‖ + ‖r - w‖ := by
      simpa only [dist_eq_norm, norm_sub_rev u r] using dist_triangle u r w
    have htv : ‖v - w‖ ≤ ‖r - v‖ + ‖r - w‖ := by
      simpa only [dist_eq_norm, norm_sub_rev v r] using dist_triangle v r w
    have he : -(19 / 20 : ℝ) * (‖r - u‖ + ‖r - v‖) ≤ 19 / 10 - (19 / 10 : ℝ) * D := by
      linarith
    have hp : normalizedPlanarMode (r - u) * normalizedPlanarMode (r - v) ≤ B := by
      calc
        _ ≤ (C * Real.exp (-(19 / 20 : ℝ) * ‖r - u‖)) *
            (C * Real.exp (-(19 / 20 : ℝ) * ‖r - v‖)) :=
          mul_le_mul (normalizedPlanarMode_exponential_envelope (by norm_num) (by norm_num) _)
            (normalizedPlanarMode_exponential_envelope (by norm_num) (by norm_num) _)
            (normalizedPlanarMode_positive _).le (mul_nonneg hC (Real.exp_pos _).le)
        _ = C ^ 2 * Real.exp (-(19 / 20 : ℝ) * (‖r - u‖ + ‖r - v‖)) := by
          rw [show -(19 / 20 : ℝ) * (‖r - u‖ + ‖r - v‖) =
            -(19 / 20 : ℝ) * ‖r - u‖ + -(19 / 20 : ℝ) * ‖r - v‖ by ring, Real.exp_add]
          ring
        _ ≤ B := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr he) (sq_nonneg C)
    rw [norm_mul, norm_mul, Real.norm_of_nonneg (normalizedPlanarMode_positive _).le,
      Real.norm_of_nonneg (normalizedPlanarMode_positive _).le, Real.norm_eq_abs]
    convert mul_le_mul_of_nonneg_right hp (abs_nonneg (manufacturedPlanarWell (r - w))) using 1
    all_goals try with_reducible_and_instances rfl
    ring
  have hiW : Integrable manufacturedPlanarWell :=
    manufacturedPlanarWell_C7.continuous.integrable_of_hasCompactSupport manufacturedPlanarWell_hasCompactSupport
  have hi := (hiW.abs.comp_sub_right w).const_mul B
  have h := norm_integral_le_of_norm_le hi (Filter.Eventually.of_forall hpt)
  rw [integral_const_mul, integral_sub_right_eq_self (fun r : PlanarPosition => |manufacturedPlanarWell r|) w] at h
  rw [Real.norm_eq_abs] at h
  apply h.trans_eq
  dsimp [B, C, planarWellMatrixConstant]
  rw [show (19 / 10 : ℝ) - (19 / 10 : ℝ) * D =
    (19 / 10 : ℝ) + -(19 / 10 : ℝ) * D by ring, Real.exp_add]
  ring

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
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Programs_PolynomialConstantBounds
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fixed positive analytic constants fit uniform polynomial ranges for
every size parameter at least two. -/

noncomputable section
namespace ContinuumCoulomb

theorem exists_polynomial_constant_bounds {c : ℝ} (hc : 0 < c) (C : ℝ) :
    ∃ q : ℕ, 0 < q ∧ ∀ N : ℝ, 2 ≤ N → (N ^ q)⁻¹ ≤ c ∧ C ≤ N ^ q := by
  obtain ⟨q, hq⟩ := exists_nat_ge (max 1 (max (1 / c) C))
  have hq₁ : (1 : ℝ) ≤ q := (le_max_left _ _).trans hq
  have hqc : 1 / c ≤ (q : ℝ) := (le_max_left _ _).trans ((le_max_right _ _).trans hq)
  have hqC : C ≤ (q : ℝ) := (le_max_right _ _).trans ((le_max_right _ _).trans hq)
  have hpow : (q : ℝ) ≤ (2 : ℝ) ^ q := by exact_mod_cast (Nat.lt_two_pow_self (n := q)).le
  refine ⟨q, by exact_mod_cast (by linarith : (0 : ℝ) < q), fun N hN => ?_⟩
  have hNp : 0 < N := by linarith
  have hp := hpow.trans (pow_le_pow_left₀ (by norm_num) hN q)
  refine ⟨?_, hqC.trans hp⟩
  rw [inv_eq_one_div]
  apply (div_le_iff₀ (pow_pos hNp q)).mpr
  have h := (div_le_iff₀ hc).mp (hqc.trans hp)
  nlinarith only [h]

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_LocalizedCounterterms
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
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

theorem localizedCountertermBound_nonnegative (freq : ℝ) : 0 ≤ localizedCountertermBound freq :=
  div_nonneg (localizedPotentialBound_nonnegative freq) (planarHopping_positive 0).le

theorem localizedOffsiteSum_bound {freq : ℝ} (hfreq : 0 < freq)
    {m : ℕ} (u : Fin m → PlanarPosition) (i : Fin m) :
    localizedOffsiteSum freq u i ≤ m * localizedPotentialBound freq := by
  calc
    _ ≤ ∑ _j : Fin m, localizedPotentialBound freq := by
      apply Finset.sum_le_sum
      intro j _
      split_ifs
      · exact localizedPotentialBound_nonnegative freq
      · exact localizedCoulombCoeff_le hfreq _ _
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

theorem localizedCounterterm_bound {freq : ℝ} (hfreq : 0 < freq)
    {m : ℕ} (u : Fin m → PlanarPosition) (i : Fin m) :
    localizedCounterterm freq u i ≤ m * localizedCountertermBound freq := by
  exact (div_le_div_of_nonneg_right (localizedOffsiteSum_bound hfreq u i)
    (planarHopping_positive 0).le).trans_eq (by unfold localizedCountertermBound; ring)

theorem localizedCounterterm_diagonal (freq : ℝ) {m : ℕ} (u : Fin m → PlanarPosition) (i : Fin m) :
    localizedCounterterm freq u i * planarWellMatrix (u i) (u i) (u i) = -localizedOffsiteSum freq u i := by
  rw [planarWellMatrix_hopping, sub_self, norm_zero]
  unfold localizedCounterterm
  field_simp [(planarHopping_positive 0).ne']

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_PlanarSobolev
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

attribute [local instance] OAI.ContinuumCoulomb.PlanarSobolev.instMeasurableSpacePlanarPosition
attribute [local instance] OAI.ContinuumCoulomb.PlanarSobolev.instBorelSpacePlanarPosition
attribute [local instance] OAI.ContinuumCoulomb.PlanarSobolev.instMeasureSpacePlanarPosition
theorem wellBound_nonnegative : 0 ≤ wellBound :=
  (norm_nonneg (manufacturedPlanarWell 0)).trans (wellBound_spec 0)

end PlanarSobolev
end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_PlanarWellLocalization
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

theorem slabWellCutoff_inner {S : ℝ} (hS : 0 < S) {z : ℝ} (hz : |z| ≤ S/2) :
    slabWellCutoff S z = 1 := by
  apply verticalCutoffBump.one_of_mem_closedBall
  change dist ((2/S)*z) 0 ≤ 1
  rw [dist_zero_right, Real.norm_eq_abs, abs_mul, abs_of_pos (div_pos (by norm_num) hS)]
  have hm := mul_le_mul_of_nonneg_left hz (div_pos (by norm_num : (0:ℝ)<2) hS).le
  have he : (2/S)*(S/2) = (1:ℝ) := by field_simp
  exact hm.trans_eq he

theorem manufacturedWellField_inner (freq scale : ℝ) {S : ℝ} (hS : 0 < S)
    {m : ℕ} (u : Fin m → PlanarPosition) (x : Position)
    (hx : |(positionSplitCoordinates x).2| ≤ S/2) :
    manufacturedWellField freq scale S u x =
      countertermWellSum freq scale u (positionSplitCoordinates x).1 := by
  simp only [manufacturedWellField, slabWellCutoff_inner hS hx, one_mul]

theorem positionSplitCoordinates_fst_zero (x : Position) :
    (positionSplitCoordinates x).1 0 = x 0 := rfl

theorem positionSplitCoordinates_fst_one (x : Position) :
    (positionSplitCoordinates x).1 1 = x 1 := rfl

theorem positionSplitCoordinates_snd (x : Position) :
    (positionSplitCoordinates x).2 = x 2 := rfl

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_OrbitalCutoffTail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Quantitative Sobolev tails of the localized orbitals. The 24th
moments give a twelfth-power decay in the H1 norm of the removed tail. -/

noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace ContinuumCoulomb

theorem localized_weighted_coefficient_tail {R A : ℝ} (hR : 0 < R) (_hA : 0 ≤ A)
    (c : Position) {a f : Position → ℝ} (ha : Continuous a) (hf : Continuous f)
    (hbound : ∀ x, |a x| ≤ A) (hzero : ∀ x, ‖x-c‖ < R → a x = 0)
    (hm : Integrable (fun x => ‖x-c‖^24*f x^2)) :
    Integrable (fun x => (a x*f x)^2) ∧
      (∫ x, (a x*f x)^2) ≤ A^2/R^24*(∫ x, ‖x-c‖^24*f x^2) := by
  have hp (x : Position) : (a x*f x)^2 ≤ A^2/R^24*(‖x-c‖^24*f x^2) := by
    by_cases hx : ‖x-c‖ < R
    · rw [hzero x hx,zero_mul,pow_two,zero_mul]
      positivity
    have hd : R ≤ ‖x-c‖ := le_of_not_gt hx
    have hs : (a x)^2 ≤ A^2 := by
      have h := pow_le_pow_left₀ (abs_nonneg (a x)) (hbound x) 2
      simpa only [sq_abs] using h
    have hr : 1 ≤ ‖x-c‖^24/R^24 :=
      (le_div_iff₀ (pow_pos hR 24)).mpr (by simpa only [one_mul] using pow_le_pow_left₀ hR.le hd 24)
    calc
      _ ≤ A^2*f x^2 := by rw [mul_pow]; exact mul_le_mul_of_nonneg_right hs (sq_nonneg _)
      _ ≤ (A^2*f x^2)*(‖x-c‖^24/R^24) := le_mul_of_one_le_right (by positivity) hr
      _ = _ := by ring
  have hi : Integrable (fun x => (a x*f x)^2) := by
    apply (hm.const_mul (A^2/R^24)).mono' ((ha.mul hf).pow 2).aestronglyMeasurable
    filter_upwards [] with x
    change ‖(a x*f x)^2‖ ≤ _
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact hp x
  refine ⟨hi,?_⟩
  have h := integral_mono hi (hm.const_mul (A^2/R^24)) hp
  simpa only [integral_const_mul] using h

theorem continuumLocalizedMode_centered_twentyFourth_moment_integrable {freq : ℝ} (hfreq : 0 < freq) (u : PlanarPosition) :
    Integrable (fun x : Position => ‖x-planarCenter u‖^24*continuumLocalizedMode freq u x^2) := by
  have hi := (localizedDensity_twentyFourth_moment_integrable hfreq).comp_sub_right (planarCenter u)
  simpa only [localizedDensity,continuumLocalizedMode_translate freq u] using hi

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_LocalizedMomentTail
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Translated fourth/eighth moments and the weighted tails used in the
finite-slab operator estimate. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

theorem localizedDensityMoment_nonnegative (freq : ℝ) (u : PlanarPosition) (k : ℕ) :
    0 ≤ localizedDensityMoment freq u k :=
  integral_nonneg (fun x => mul_nonneg (pow_nonneg (norm_nonneg x) k)
    (localizedDensity_nonnegative freq u x))

private theorem translated_moment {freq : ℝ} (hfreq : 0 < freq) (k : ℕ)
    (hk : Integrable (fun x : Position => ‖x‖^k*localizedDensity freq 0 x))
    (u : PlanarPosition) :
    Integrable (fun x : Position => ‖x‖^k*localizedDensity freq u x) ∧
      localizedDensityMoment freq u k ≤
        (2:ℝ)^(k-1)*(localizedDensityMoment freq 0 k+‖u‖^k) := by
  let c := planarCenter u
  let F (x : Position) := ‖x‖^k*localizedDensity freq 0 x+
    ‖c‖^k*localizedDensity freq 0 x
  have hF : Integrable F := hk.add ((localizedDensity_integrable hfreq 0).const_mul _)
  have hmajor : Integrable (fun x => (2:ℝ)^(k-1)*F (x-c)) :=
    (hF.comp_sub_right c).const_mul _
  have hp (x : Position) : ‖x‖^k*localizedDensity freq u x ≤ (2:ℝ)^(k-1)*F (x-c) := by
    have hn : ‖x‖ ≤ ‖x-c‖+‖c‖ := by
      simpa only [sub_add_cancel] using norm_add_le (x-c) c
    have hb := (pow_le_pow_left₀ (norm_nonneg x) hn k).trans
      (add_pow_le (norm_nonneg (x-c)) (norm_nonneg c) k)
    have hm := mul_le_mul_of_nonneg_right hb (localizedDensity_nonnegative freq 0 (x-c))
    rw [localizedDensity_translate]
    convert hm using 1
    all_goals try with_reducible_and_instances rfl
    dsimp [F, c]
    ring
  have hi : Integrable (fun x : Position => ‖x‖^k*localizedDensity freq u x) := by
    apply hmajor.mono' ((continuous_norm.pow k).mul (localizedDensity_continuous freq u)).aestronglyMeasurable
    filter_upwards [] with x
    change ‖‖x‖^k*localizedDensity freq u x‖ ≤ _
    rw [Real.norm_of_nonneg (mul_nonneg (pow_nonneg (norm_nonneg x) k)
      (localizedDensity_nonnegative freq u x))]
    exact hp x
  refine ⟨hi, ?_⟩
  have h := integral_mono hi hmajor hp
  change localizedDensityMoment freq u k ≤ _ at h
  rw [integral_const_mul, integral_sub_right_eq_self] at h
  dsimp [F] at h
  rw [integral_add hk ((localizedDensity_integrable hfreq 0).const_mul _),
    integral_const_mul, localizedDensity_mass hfreq 0, mul_one] at h
  simpa only [c, planarCenter_norm, localizedDensityMoment] using h

theorem localizedDensity_fourth_moment_translate {freq : ℝ} (hfreq : 0 < freq)
    (u : PlanarPosition) :
    Integrable (fun x : Position => ‖x‖^4*localizedDensity freq u x) ∧
      localizedDensityMoment freq u 4 ≤ 8*(localizedDensityMoment freq 0 4+‖u‖^4) := by
  convert translated_moment hfreq 4 (localizedDensity_fourth_moment_integrable hfreq) u using 1
  all_goals try with_reducible_and_instances rfl
  norm_num

theorem localizedDensity_eighth_moment_translate {freq : ℝ} (hfreq : 0 < freq)
    (u : PlanarPosition) :
    Integrable (fun x : Position => ‖x‖^8*localizedDensity freq u x) ∧
      localizedDensityMoment freq u 8 ≤ 128*(localizedDensityMoment freq 0 8+‖u‖^8) := by
  convert translated_moment hfreq 8 (localizedDensity_eighth_moment_integrable hfreq) u using 1
  all_goals try with_reducible_and_instances rfl
  norm_num

theorem localizedDensity_seventySecond_moment_translate {freq : ℝ} (hfreq : 0 < freq)
    (u : PlanarPosition) :
    Integrable (fun x : Position => ‖x‖^72*localizedDensity freq u x) ∧
      localizedDensityMoment freq u 72 ≤
        (2:ℝ)^71*(localizedDensityMoment freq 0 72+‖u‖^72) :=
  translated_moment hfreq 72 (localizedDensity_seventySecond_moment_integrable hfreq) u

private theorem weighted_tail {freq R : ℝ} (hR : 0 < R) (u : PlanarPosition)
    (a b : ℕ) (ha : Integrable (fun x : Position => ‖x‖^a*localizedDensity freq u x))
    (hab : Integrable (fun x : Position => ‖x‖^(a+b)*localizedDensity freq u x))
    {S : Set Position} (hS : MeasurableSet S) (hout : ∀ x ∉ S, R ≤ ‖x‖) :
    (∫ x in Sᶜ, ‖x‖^a*localizedDensity freq u x) ≤
      localizedDensityMoment freq u (a+b)/R^b := by
  have hp (x : Position) (hx : x ∈ Sᶜ) :
      R^b*(‖x‖^a*localizedDensity freq u x) ≤ ‖x‖^(a+b)*localizedDensity freq u x := by
    have h := mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ hR.le (hout x hx) b)
      (mul_nonneg (pow_nonneg (norm_nonneg x) a) (localizedDensity_nonnegative freq u x))
    simpa only [pow_add, mul_left_comm, mul_assoc] using h
  have h := setIntegral_mono_on (ha.const_mul (R^b)).integrableOn hab.integrableOn hS.compl hp
  have hfull := integral_mono_measure (μ := volume.restrict Sᶜ) Measure.restrict_le_self
    (Filter.Eventually.of_forall (fun x => mul_nonneg (pow_nonneg (norm_nonneg x) (a+b))
      (localizedDensity_nonnegative freq u x))) hab
  rw [integral_const_mul] at h
  apply (le_div_iff₀ (pow_pos hR b)).mpr
  simpa only [localizedDensityMoment, mul_comm] using h.trans hfull

theorem localizedDensity_mass_tail_seventySecond {freq R : ℝ} (hfreq : 0 < freq) (hR : 0 < R)
    (u : PlanarPosition) {S : Set Position} (hS : MeasurableSet S)
    (hout : ∀ x ∉ S, R ≤ ‖x‖) :
    (∫ x in Sᶜ, localizedDensity freq u x) ≤ localizedDensityMoment freq u 72/R^72 := by
  simpa only [pow_zero,one_mul,zero_add] using weighted_tail hR u 0 72
    (by simpa only [pow_zero,one_mul] using localizedDensity_integrable hfreq u)
    (localizedDensity_seventySecond_moment_translate hfreq u).1 hS hout

theorem localizedDensity_fourth_tail_seventySecond {freq R : ℝ} (hfreq : 0 < freq) (hR : 0 < R)
    (u : PlanarPosition) {S : Set Position} (hS : MeasurableSet S)
    (hout : ∀ x ∉ S, R ≤ ‖x‖) :
    (∫ x in Sᶜ, ‖x‖^4*localizedDensity freq u x) ≤ localizedDensityMoment freq u 72/R^68 := by
  exact weighted_tail hR u 4 68 (localizedDensity_fourth_moment_translate hfreq u).1
    (localizedDensity_seventySecond_moment_translate hfreq u).1 hS hout

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_WellFieldOrbitalResidual
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The cutoff and depth-counterterm contribution to the actual localized
one-particle residual. The estimate uses polynomially many spatial modes. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb

theorem planarWellSum_abs_bound {m : ℕ} (u : Fin m → PlanarPosition) (r : PlanarPosition) :
    |planarWellSum u r| ≤ (m : ℝ)*PlanarSobolev.wellBound := by
  unfold planarWellSum
  calc
    _ ≤ ∑ i, |manufacturedPlanarWell (r-u i)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin m, PlanarSobolev.wellBound := Finset.sum_le_sum (fun i _ => by
      simpa only [Real.norm_eq_abs] using PlanarSobolev.wellBound_spec (r-u i))
    _ = _ := by simp

theorem countertermWellSum_sub_eq (freq scale : ℝ) {m : ℕ}
    (u : Fin m → PlanarPosition) (r : PlanarPosition) :
    countertermWellSum freq scale u r-planarWellSum u r =
      ∑ i, (localizedCounterterm freq u i/scale)*manufacturedPlanarWell (r-u i) := by
  unfold countertermWellSum planarWellSum
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem countertermWellSum_sub_abs_bound (freq scale : ℝ) {m : ℕ}
    (u : Fin m → PlanarPosition) {δ : ℝ}
    (hcoeff : ∀ i, 0 ≤ localizedCounterterm freq u i/scale ∧
      localizedCounterterm freq u i/scale ≤ δ) (r : PlanarPosition) :
    |countertermWellSum freq scale u r-planarWellSum u r| ≤
      (m : ℝ)*δ*PlanarSobolev.wellBound := by
  rw [countertermWellSum_sub_eq]
  calc
    _ ≤ ∑ i, |(localizedCounterterm freq u i/scale)*manufacturedPlanarWell (r-u i)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin m, δ*PlanarSobolev.wellBound := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul, abs_of_nonneg (hcoeff i).1]
      exact mul_le_mul (hcoeff i).2 (by
        simpa only [Real.norm_eq_abs] using PlanarSobolev.wellBound_spec (r-u i))
        (abs_nonneg _) ((hcoeff i).1.trans (hcoeff i).2)
    _ = _ := by simp [mul_assoc]

theorem manufacturedWellField_sub_abs_bound (freq scale S : ℝ) {m : ℕ}
    (u : Fin m → PlanarPosition) {δ : ℝ} (_hδ : 0 ≤ δ)
    (hcoeff : ∀ i, 0 ≤ localizedCounterterm freq u i/scale ∧
      localizedCounterterm freq u i/scale ≤ δ) (x : Position) :
    |manufacturedWellField freq scale S u x-planarWellSum u (positionSplitCoordinates x).1| ≤
      (m : ℝ)*(δ+1)*PlanarSobolev.wellBound := by
  let t := slabWellCutoff S (positionSplitCoordinates x).2
  let a := countertermWellSum freq scale u (positionSplitCoordinates x).1
  let b := planarWellSum u (positionSplitCoordinates x).1
  have ht : 0 ≤ t ∧ t ≤ 1 := slabWellCutoff_bounds _ _
  have hdiff := countertermWellSum_sub_abs_bound freq scale u hcoeff (positionSplitCoordinates x).1
  have hb := planarWellSum_abs_bound u (positionSplitCoordinates x).1
  have h1 : |t-1| ≤ 1 := by rw [abs_of_nonpos (by linarith : t-1 ≤ 0)]; linarith
  have he : t*a-b = t*(a-b)+(t-1)*b := by ring
  change |t*a-b| ≤ _
  rw [he]
  calc
    _ ≤ |t*(a-b)|+|(t-1)*b| := abs_add_le _ _
    _ ≤ (m : ℝ)*δ*PlanarSobolev.wellBound+(m : ℝ)*PlanarSobolev.wellBound := by
      rw [abs_mul, abs_mul, abs_of_nonneg ht.1]
      exact add_le_add
        ((mul_le_mul_of_nonneg_right ht.2 (abs_nonneg _)).trans (by simpa only [one_mul] using hdiff))
        ((mul_le_mul_of_nonneg_right h1 (abs_nonneg _)).trans (by simpa only [one_mul] using hb))
    _ = _ := by ring

theorem wellFieldOrbitalResidual_square_integrable {freq : ℝ} (hfreq : 0 < freq)
    (scale S : ℝ) {m : ℕ} (u : Fin m → PlanarPosition) {δ : ℝ} (hδ : 0 ≤ δ)
    (hcoeff : ∀ i, 0 ≤ localizedCounterterm freq u i/scale ∧
      localizedCounterterm freq u i/scale ≤ δ) (j : Fin m) :
    Integrable (fun x => wellFieldOrbitalResidual freq scale S u j x^2) := by
  have hm : MemLp (wellFieldOrbitalResidual freq scale S u j) 2 := by
    apply (continuumLocalizedMode_memLp hfreq (u j)).of_le_mul
      (c := (m : ℝ)*(δ+1)*PlanarSobolev.wellBound)
      ((((manufacturedWellField_C7 freq scale S u).continuous.sub
        ((planarWellSum_continuous u).comp positionSplitCoordinates.continuous.fst)).mul
        (continuumLocalizedMode_C7 freq (u j)).continuous).aestronglyMeasurable)
    filter_upwards [] with x
    change ‖(manufacturedWellField freq scale S u x-planarWellSum u (positionSplitCoordinates x).1)*
      continuumLocalizedMode freq (u j) x‖ ≤ _
    rw [norm_mul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (manufacturedWellField_sub_abs_bound freq scale S u hδ hcoeff x)
      (norm_nonneg _)
  exact hm.integrable_sq

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_ManyBody_FiniteWellResidual
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite vertical cutoff error after retaining the intended well-depth
counterterms. Its bound decays with the slab height and does not include the
counterterm itself as an error. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

theorem countertermWellSum_abs_bound (freq scale : ℝ) {m : ℕ}
    (u : Fin m → PlanarPosition) {δ : ℝ}
    (hcoeff : ∀ i, 0 ≤ localizedCounterterm freq u i/scale ∧
      localizedCounterterm freq u i/scale ≤ δ) (r : PlanarPosition) :
    |countertermWellSum freq scale u r| ≤ (m:ℝ)*(δ+1)*PlanarSobolev.wellBound := by
  have h := (abs_add_le (countertermWellSum freq scale u r-planarWellSum u r) (planarWellSum u r)).trans
    (add_le_add (countertermWellSum_sub_abs_bound freq scale u hcoeff r) (planarWellSum_abs_bound u r))
  rw [sub_add_cancel] at h
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  ring

theorem finiteWellOrbitalResidual_continuous (freq scale S : ℝ) {m : ℕ}
    (u : Fin m → PlanarPosition) (j : Fin m) :
    Continuous (finiteWellOrbitalResidual freq scale S u j) :=
  ((manufacturedWellField_C7 freq scale S u).continuous.sub
    ((countertermWellSum_C7 freq scale u).continuous.comp positionSplitCoordinates.continuous.fst)).mul
      (continuumLocalizedMode_C7 freq (u j)).continuous

theorem finiteWellOrbitalResidual_square_bound {freq S : ℝ} (hfreq : 0 < freq) (hS : 0 < S)
    (scale : ℝ) {m : ℕ} (u : Fin m → PlanarPosition) {δ : ℝ} (hδ : 0 ≤ δ)
    (hcoeff : ∀ i, 0 ≤ localizedCounterterm freq u i/scale ∧
      localizedCounterterm freq u i/scale ≤ δ) (j : Fin m) :
    Integrable (fun x => finiteWellOrbitalResidual freq scale S u j x^2) ∧
    (∫ x, finiteWellOrbitalResidual freq scale S u j x^2) ≤
      ((m:ℝ)*(δ+1)*PlanarSobolev.wellBound)^2/(S/2)^24*
        (∫ x, ‖x‖^24*continuumLocalizedMode freq 0 x^2) := by
  let a : Position → ℝ := fun x => manufacturedWellField freq scale S u x-
    countertermWellSum freq scale u (positionSplitCoordinates x).1
  let B := (m:ℝ)*(δ+1)*PlanarSobolev.wellBound
  have hB : 0 ≤ B := mul_nonneg (mul_nonneg (Nat.cast_nonneg m) (by linarith))
    PlanarSobolev.wellBound_nonnegative
  have ha : Continuous a := (manufacturedWellField_C7 freq scale S u).continuous.sub
    ((countertermWellSum_C7 freq scale u).continuous.comp positionSplitCoordinates.continuous.fst)
  have hb (x : Position) : |a x| ≤ B := by
    have ht := slabWellCutoff_bounds S (positionSplitCoordinates x).2
    have ht' : |slabWellCutoff S (positionSplitCoordinates x).2-1| ≤ 1 := by
      rw [abs_of_nonpos (by linarith)]
      linarith
    change |slabWellCutoff S (positionSplitCoordinates x).2*
      countertermWellSum freq scale u (positionSplitCoordinates x).1-
      countertermWellSum freq scale u (positionSplitCoordinates x).1| ≤ B
    rw [← sub_one_mul,abs_mul]
    exact (mul_le_mul_of_nonneg_right ht' (abs_nonneg _)).trans
      (by simpa only [one_mul] using countertermWellSum_abs_bound freq scale u hcoeff (positionSplitCoordinates x).1)
  have hz (x : Position) (hx : ‖x-planarCenter (u j)‖ < S/2) : a x = 0 := by
    have hcenter : planarCenter (u j) 2 = 0 := by
      simpa only [planarCenter,ContinuousLinearEquiv.apply_symm_apply] using
        (positionSplitCoordinates_snd (planarCenter (u j))).symm
    have hcoord := (PiLp.norm_apply_le (x-planarCenter (u j)) 2).trans hx.le
    have hcoord' : |(positionSplitCoordinates x).2| ≤ S/2 := by
      simpa only [positionSplitCoordinates_snd,PiLp.sub_apply,hcenter,sub_zero,Real.norm_eq_abs] using hcoord
    exact sub_eq_zero.mpr (manufacturedWellField_inner freq scale hS u x hcoord')
  have h := localized_weighted_coefficient_tail (half_pos hS) hB (planarCenter (u j)) ha
    (continuumLocalizedMode_C7 freq (u j)).continuous hb hz
    (continuumLocalizedMode_centered_twentyFourth_moment_integrable hfreq (u j))
  refine ⟨h.1,?_⟩
  apply h.2.trans_eq
  simp_rw [continuumLocalizedMode_translate freq (u j)]
  rw [integral_sub_right_eq_self (μ := volume)
    (fun x : Position => ‖x‖^24*continuumLocalizedMode freq 0 x^2) (planarCenter (u j))]

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
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_ManyBody_WeightedSourcePairing
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Weighted Cauchy--Schwarz for the absolute nuclear error measure. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

theorem weighted_real_pairing {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (F f g : X → ℝ)
    (hF : AEMeasurable F μ) (hf : AEMeasurable f μ) (hg : AEMeasurable g μ)
    (hfi : Integrable (fun x => |F x| *f x^2) μ)
    (hgi : Integrable (fun x => |F x| *g x^2) μ) :
    Integrable (fun x => F x*f x*g x) μ ∧
      |∫ x, F x*f x*g x ∂μ|^2 ≤
        (∫ x, |F x| *f x^2 ∂μ)*(∫ x, |F x| *g x^2 ∂μ) := by
  let a : X → ℝ := fun x => Real.sqrt |F x| *|f x|
  let b : X → ℝ := fun x => Real.sqrt |F x| *|g x|
  have ha : AEMeasurable a μ := (Real.continuous_sqrt.measurable.comp_aemeasurable hF.abs).mul hf.abs
  have hb : AEMeasurable b μ := (Real.continuous_sqrt.measurable.comp_aemeasurable hF.abs).mul hg.abs
  have hasq (x : X) : a x^2 = |F x| *f x^2 := by
    dsimp [a]
    rw [mul_pow,Real.sq_sqrt (abs_nonneg _),sq_abs]
  have hbsq (x : X) : b x^2 = |F x| *g x^2 := by
    dsimp [b]
    rw [mul_pow,Real.sq_sqrt (abs_nonneg _),sq_abs]
  have hpa : MemLp a 2 μ := (memLp_two_iff_integrable_sq ha.aestronglyMeasurable).mpr (by simpa only [hasq] using hfi)
  have hpb : MemLp b 2 μ := (memLp_two_iff_integrable_sq hb.aestronglyMeasurable).mpr (by simpa only [hbsq] using hgi)
  let A := hpa.toLp a
  let B := hpb.toLp b
  have hi : inner ℝ A B = ∫ x, a x*b x ∂μ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hpa.coeFn_toLp,hpb.coeFn_toLp] with x hax hbx
    change inner ℝ (A x) (B x) = a x*b x
    rw [hax,hbx,Real.inner_apply]
  have hnA : ‖A‖^2 = ∫ x, |F x| *f x^2 ∂μ := by
    rw [← real_inner_self_eq_norm_sq,L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hpa.coeFn_toLp] with x hax
    rw [real_inner_self_eq_norm_sq,hax,Real.norm_eq_abs,sq_abs,hasq]
  have hnB : ‖B‖^2 = ∫ x, |F x| *g x^2 ∂μ := by
    rw [← real_inner_self_eq_norm_sq,L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hpb.coeFn_toLp] with x hbx
    rw [real_inner_self_eq_norm_sq,hbx,Real.norm_eq_abs,sq_abs,hbsq]
  have hab (x : X) : a x*b x = ‖F x*f x*g x‖ := by
    dsimp [a,b]
    rw [abs_mul,abs_mul]
    calc
      _ = (Real.sqrt |F x|)^2*(|f x| *|g x|) := by ring
      _ = _ := by rw [Real.sq_sqrt (abs_nonneg (F x))]; ring
  have hip := hpa.integrable_mul hpb
  have hIfg : Integrable (fun x => F x*f x*g x) μ := by
    apply hip.mono' ((hF.mul hf).mul hg).aestronglyMeasurable
    exact Filter.Eventually.of_forall (fun x => (hab x).ge)
  refine ⟨hIfg,?_⟩
  have hle : |∫ x, F x*f x*g x ∂μ| ≤ ∫ x, a x*b x ∂μ := by
    have h := norm_integral_le_integral_norm (μ := μ) (fun x => F x*f x*g x)
    simpa only [Real.norm_eq_abs,← hab] using h
  have hcs := pow_le_pow_left₀ (norm_nonneg (inner ℝ A B)) (norm_inner_le_norm (𝕜 := ℝ) A B) 2
  rw [mul_pow,hnA,hnB,hi,Real.norm_eq_abs,sq_abs] at hcs
  exact (pow_le_pow_left₀ (abs_nonneg _) hle 2).trans hcs

theorem weighted_source_pairing (F f g : Position → ℝ)
    (hF : Measurable F) (hf : Measurable f) (hg : Measurable g)
    (hfi : Integrable (fun x => |F x| *f x^2))
    (hgi : Integrable (fun x => |F x| *g x^2)) :
    Integrable (fun x => F x*f x*g x) ∧
      |∫ x, F x*f x*g x|^2 ≤
        (∫ x, |F x| *f x^2)*(∫ x, |F x| *g x^2) :=
  weighted_real_pairing volume F f g hF.aemeasurable hf.aemeasurable hg.aemeasurable hfi hgi

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Nuclei_SlabLineIntegral
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

theorem coulombLineKernel_continuous {A : ℝ} (hA : 0 < A) :
    Continuous (coulombLineKernel A) := by
  apply Continuous.inv₀
  · exact (continuous_const.add (continuous_id.pow 2)).sqrt
  · intro t
    exact (Real.sqrt_pos.mpr (by nlinarith [sq_nonneg t] : 0 < A+t^2)).ne'

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

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Nuclei_SlabLineFlatness
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Quadratic horizontal variation of a centered Coulomb line integral. -/

noncomputable section
namespace ContinuumCoulomb

theorem coulombLine_boundary_difference {A H x : ℝ} (hA : 0 < A) (hH : 0 < H)
    (hx : |x| ≤ H/2) :
    |coulombLineKernel A (x+H)-coulombLineKernel A (x-H)| ≤ 16*|x|/H^2 := by
  have hlo : -(H/2) ≤ x := (abs_le.mp hx).1
  have hhi : x ≤ H/2 := (abs_le.mp hx).2
  have hp : (H/2)^2 ≤ (x+H)^2 :=
    (sq_le_sq₀ (by positivity) (by linarith)).mpr (by linarith)
  have hn : (H/2)^2 ≤ (H-x)^2 :=
    (sq_le_sq₀ (by positivity) (by linarith)).mpr (by linarith)
  have hb := reciprocal_sqrt_difference_bound (show 0 < H/2 by positivity)
    (show (H/2)^2 ≤ A+(x+H)^2 by linarith)
    (show (H/2)^2 ≤ A+(x-H)^2 by nlinarith)
  have he : (A+(x+H)^2)-(A+(x-H)^2) = 4*H*x := by ring
  rw [he, abs_mul, abs_mul, abs_of_pos (by norm_num : (0:ℝ)<4), abs_of_pos hH] at hb
  change |coulombLineKernel A (x+H)-coulombLineKernel A (x-H)| ≤ _ at hb
  convert hb using 1
  all_goals try with_reducible_and_instances rfl
  field_simp
  ring

theorem coulombLineIntegral_quadratic_variation {A H x : ℝ} (hA : 0 < A) (hH : 0 < H)
    (hx : |x| ≤ H/2) :
    |centeredLineIntegral (coulombLineKernel A) H x-
      centeredLineIntegral (coulombLineKernel A) H 0| ≤ 16*x^2/H^2 := by
  let f := centeredLineIntegral (coulombLineKernel A) H
  let d := fun t => coulombLineKernel A (t+H)-coulombLineKernel A (t-H)
  have hd (t : ℝ) : HasDerivAt f (d t) t :=
    centeredLineIntegral_hasDerivAt _ (coulombLineKernel_continuous hA) H t
  have hbound (t : ℝ) (ht : t ∈ Set.Icc (-|x|) |x|) : ‖d t‖ ≤ 16*|x|/H^2 := by
    have ht' : |t| ≤ |x| := abs_le.mpr ht
    have h := coulombLine_boundary_difference hA hH (ht'.trans hx)
    rw [Real.norm_eq_abs]
    exact h.trans (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left ht' (by norm_num)) (sq_nonneg H))
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun t _ => (hd t).hasDerivWithinAt) hbound (convex_Icc (-|x|) |x|)
    (show (0:ℝ) ∈ Set.Icc (-|x|) |x| by constructor <;> linarith [abs_nonneg x])
    (show x ∈ Set.Icc (-|x|) |x| from ⟨neg_abs_le x, le_abs_self x⟩)
  simpa only [Real.norm_eq_abs, sub_zero, f, div_mul_eq_mul_div, mul_assoc, ← pow_two, sq_abs] using h

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Nuclei_SlabInterior
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Interior horizontal flatness and the full finite-slab approximation. -/

noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace ContinuumCoulomb

private theorem coulombLine_setIntegral_variation {A H x : ℝ} (hA : 0 < A)
    (hH : 0 < H) (hx : |x| ≤ H/2) :
    |(∫ t in Set.Icc (-H) H, coulombLineKernel A (x-t))-
      (∫ t in Set.Icc (-H) H, coulombLineKernel A (0-t))| ≤ 16*x^2/H^2 := by
  have h := coulombLineIntegral_quadratic_variation hA hH hx
  simp only [centeredLineIntegral_translate,
    intervalIntegral.integral_of_le (show -H ≤ H by linarith),
    ← integral_Icc_eq_integral_Ioc] at h
  exact h

private theorem slabOtherMeasure_mass {H S : ℝ} (hH : 0 ≤ H) (hS : 0 ≤ S)
    (i : Fin 3) (hi : i ≠ 2) :
    (Measure.pi (fun j : Fin 2 => slabAxisMeasure H S (i.succAbove j))).real Set.univ = 4*H*S := by
  rw [Measure.real, Measure.pi_univ, Fin.prod_univ_two, ENNReal.toReal_mul]
  simp only [slabAxisMeasure, Measure.restrict_apply_univ, Real.volume_Icc]
  fin_cases i
  · norm_num [slabSide, Fin.succAbove, ENNReal.toReal_ofReal, hH, hS, Fin.ext_iff]
    ring
  · norm_num [slabSide, Fin.succAbove, ENNReal.toReal_ofReal, hH, hS, Fin.ext_iff]
    ring
  · exact (hi rfl).elim

private theorem slabInteriorSection_integrable {epsilon H S : ℝ} (hepsilon : epsilon ≠ 0)
    (hH : 0 ≤ H) (hS : 0 ≤ S) (y : Position) (i : Fin 3) :
    Integrable (fun v : Fin 2 → ℝ => ∫ t : ℝ,
      NeutralAtom.regularizedKernel epsilon (y-WithLp.toLp 2 (i.insertNth t v))
      ∂slabAxisMeasure H S i)
      (Measure.pi (fun j : Fin 2 => slabAxisMeasure H S (i.succAbove j))) := by
  have hp := (measurePreserving_piFinSuccAbove (slabAxisMeasure H S) i).symm
  have hi := (hp.integrable_comp_emb
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) i).symm.measurableEmbedding).mpr
      ((slabProduct_integrable H S _).mpr (regularizedSlab_integrableOn hepsilon hH hS y))
  exact hi.integral_prod_right

private theorem regularizedSlab_coordinate_variation {epsilon rho H S : ℝ}
    (hepsilon : epsilon ≠ 0) (hrho : 0 ≤ rho) (hH : 0 < H) (hS : 0 ≤ S)
    (y : Position) (i : Fin 3) (hi : i ≠ 2) (hy : |y i| ≤ H/2) :
    |regularizedSlabPotential epsilon rho H S y-
      regularizedSlabPotential epsilon rho H S (zeroPositionCoordinate i y)| ≤
        64*rho*S*(y i)^2/H := by
  let mu := Measure.pi (fun j : Fin 2 => slabAxisMeasure H S (i.succAbove j))
  let F := fun (v : Fin 2 → ℝ) => ∫ t : ℝ,
    NeutralAtom.regularizedKernel epsilon (y-WithLp.toLp 2 (i.insertNth t v))
    ∂slabAxisMeasure H S i
  let G := fun (v : Fin 2 → ℝ) => ∫ t : ℝ,
    NeutralAtom.regularizedKernel epsilon (zeroPositionCoordinate i y-
      WithLp.toLp 2 (i.insertNth t v)) ∂slabAxisMeasure H S i
  have hF : Integrable F mu := slabInteriorSection_integrable hepsilon hH.le hS y i
  have hG : Integrable G mu :=
    slabInteriorSection_integrable hepsilon hH.le hS (zeroPositionCoordinate i y) i
  have hb (v : Fin 2 → ℝ) : ‖F v-G v‖ ≤ 16*(y i)^2/H^2 := by
    dsimp only [F, G]
    simp_rw [regularizedKernel_section, zeroPositionCoordinate_same, zeroPositionCoordinate_other]
    have hA : 0 < epsilon^2+∑ j : Fin 2, (y (i.succAbove j)-v j)^2 :=
      add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero hepsilon)
        (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
    rw [Real.norm_eq_abs]
    change |(∫ t in Set.Icc (-slabSide H S i) (slabSide H S i),
      coulombLineKernel _ (y i-t))-(∫ t in Set.Icc (-slabSide H S i) (slabSide H S i),
      coulombLineKernel _ (0-t))| ≤ _
    rw [show slabSide H S i = H by simp [slabSide, hi]]
    exact coulombLine_setIntegral_variation hA hH hy
  have hI : |(∫ v, F v ∂mu)-(∫ v, G v ∂mu)| ≤ (16*(y i)^2/H^2)*(4*H*S) := by
    rw [← integral_sub hF hG, ← Real.norm_eq_abs]
    have h := norm_integral_le_of_norm_le_const (μ := mu) (f := fun v => F v-G v)
      (Filter.Eventually.of_forall hb)
    simpa only [mu, slabOtherMeasure_mass hH.le hS i hi] using h
  unfold regularizedSlabPotential
  rw [regularizedSlab_sectionIntegral hepsilon hH.le hS y i,
    regularizedSlab_sectionIntegral hepsilon hH.le hS (zeroPositionCoordinate i y) i,
    ← mul_sub, abs_mul, abs_neg, abs_of_nonneg hrho]
  change rho*|(∫ v, F v ∂mu)-(∫ v, G v ∂mu)| ≤ _
  apply (mul_le_mul_of_nonneg_left hI hrho).trans_eq
  field_simp
  ring

theorem slabPotential_coordinate_variation {rho H S : ℝ} (hrho : 0 ≤ rho)
    (hH : 0 < H) (hS : 0 ≤ S) (y : Position) (i : Fin 3) (hi : i ≠ 2)
    (hy : |y i| ≤ H/2) :
    |slabPotential rho H S y-slabPotential rho H S (zeroPositionCoordinate i y)| ≤
      64*rho*S*(y i)^2/H := by
  let epsilon : ℕ → ℝ := fun n => ((n:ℝ)+1)⁻¹
  have hep (n : ℕ) : 0 < epsilon n := by dsimp [epsilon]; positivity
  have heps : Tendsto epsilon atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp
      (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
  have hlim := ((regularizedSlabPotential_tendsto hep heps rho hH.le hS y).sub
    (regularizedSlabPotential_tendsto hep heps rho hH.le hS (zeroPositionCoordinate i y))).abs
  exact le_of_tendsto hlim (Filter.Eventually.of_forall (fun n =>
    regularizedSlab_coordinate_variation (hep n).ne' hrho hH hS y i hi hy))

theorem slabPotential_horizontal_variation {rho H S : ℝ} (hrho : 0 ≤ rho)
    (hH : 0 < H) (hS : 0 ≤ S) (y : Position)
    (hy0 : |y 0| ≤ H/2) (hy1 : |y 1| ≤ H/2) :
    |slabPotential rho H S y-slabPotential rho H S (slabAxisPoint (y 2))| ≤
      64*rho*S*((y 0)^2+(y 1)^2)/H := by
  have h0 := slabPotential_coordinate_variation hrho hH hS y 0 (by decide) hy0
  have h1 := slabPotential_coordinate_variation hrho hH hS (zeroPositionCoordinate 0 y) 1
    (by decide) (by simpa [zeroPositionCoordinate] using hy1)
  have he : zeroPositionCoordinate 1 (zeroPositionCoordinate 0 y) = slabAxisPoint (y 2) := by
    ext j
    fin_cases j <;> simp [zeroPositionCoordinate, slabAxisPoint]
  rw [he] at h1
  have hcoord : zeroPositionCoordinate 0 y 1 = y 1 := by simp [zeroPositionCoordinate]
  rw [hcoord] at h1
  calc
    _ ≤ |slabPotential rho H S y-slabPotential rho H S (zeroPositionCoordinate 0 y)|+
        |slabPotential rho H S (zeroPositionCoordinate 0 y)-slabPotential rho H S (slabAxisPoint (y 2))| :=
      abs_sub_le _ _ _
    _ ≤ 64*rho*S*(y 0)^2/H+64*rho*S*(y 1)^2/H := add_le_add h0 h1
    _ = _ := by ring

/-- The finite slab approximates the harmonic potential throughout its
central horizontal half-box and vertical thickness. -/
theorem slabPotential_interior_error {rho H S : ℝ} (hrho : 0 ≤ rho)
    (hH : 0 < H) (hS : 0 ≤ S) (y : Position)
    (hy0 : |y 0| ≤ H/2) (hy1 : |y 1| ≤ H/2) (hy2 : |y 2| ≤ S) :
    |slabPotential rho H S y-slabPotential rho H S 0-2*Real.pi*rho*(y 2)^2| ≤
      64*rho*S*((y 0)^2+(y 1)^2)/H+6*Real.pi*rho*S^3/H := by
  have h0 := slabPotential_horizontal_variation hrho hH hS y hy0 hy1
  have h1 := slabPotential_axis_error hrho hH hS hy2
  calc
    _ = |(slabPotential rho H S y-slabPotential rho H S (slabAxisPoint (y 2)))+
        (slabPotential rho H S (slabAxisPoint (y 2))-slabPotential rho H S 0-
          2*Real.pi*rho*(y 2)^2)| := by congr 1; ring
    _ ≤ _ := (abs_add_le _ _).trans (add_le_add h0 h1)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Nuclei_SlabRegularity
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Continuity and global boundedness of the actual slab field, including
its discontinuous density at the slab boundary. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

theorem slabPotential_abs_bound {rho H S : ℝ} (hrho : 0 ≤ rho)
    (hH : 0 ≤ H) (hS : 0 ≤ S) (x : Position) :
    |slabPotential rho H S x| ≤
      rho*NeutralAtom.kernelBallMass 1+volume.real (slabDomain H S)*rho := by
  have hb := (NeutralAtom.potential_integrable_and_bound
    (slabDensity_integrable hH hS rho) (slabDensity_nonnegative hrho H S)
    (by norm_num : (0:ℝ)<1) (fun y _ => slabDensity_le hrho H S y) (x := x)).2
  rw [slabDensity_integral] at hb
  rw [slabPotential_eq_negativePotentialOf, abs_neg,
    abs_of_nonneg (NeutralAtom.potentialOf_nonneg (slabDensity_nonnegative hrho H S) x)]
  simpa only [inv_one, one_mul] using hb

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Nuclei_SlabOrbitalResidual
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite slab's actual harmonic-oscillator residual on a localized
orbital. Interior accuracy and weighted tails are kept separately. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

theorem slabResidualMultiplier_abs_bound {rho H S : ℝ} (hrho : 0 ≤ rho)
    (hH : 0 ≤ H) (hS : 0 ≤ S) (x : Position) :
    |slabResidualMultiplier rho H S x| ≤
      2*slabUniformBound rho H S+(2*Real.pi*rho)*‖x‖^2 := by
  have hx := slabPotential_abs_bound hrho hH hS x
  have h0 := slabPotential_abs_bound hrho hH hS 0
  have hn : (x 2)^2 ≤ ‖x‖^2 := by
    have h := PiLp.norm_apply_le x 2
    rw [Real.norm_eq_abs] at h
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) (norm_nonneg _)).mpr h
  have hc : 0 ≤ 2*Real.pi*rho := by positivity
  unfold slabResidualMultiplier
  calc
    _ ≤ |slabPotential rho H S x-slabPotential rho H S 0|+
        |2*Real.pi*rho*(x 2)^2| := abs_sub _ _
    _ ≤ 2*slabUniformBound rho H S+(2*Real.pi*rho)*(x 2)^2 := by
      rw [abs_of_nonneg (mul_nonneg hc (sq_nonneg _))]
      have h := (abs_sub (slabPotential rho H S x) (slabPotential rho H S 0)).trans
        (add_le_add hx h0)
      dsimp [slabUniformBound]
      linarith
    _ ≤ _ := add_le_add le_rfl (mul_le_mul_of_nonneg_left hn hc)

private theorem square_times_density_bound {f : ℝ} {A B t d : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (ht : 0 ≤ t) (hd : 0 ≤ d)
    (hf : |f| ≤ A+B*t) : f^2*d ≤ 2*A^2*d+2*B^2*t^2*d := by
  have hs := (sq_le_sq₀ (abs_nonneg f) (by positivity : 0 ≤ A+B*t)).mpr hf
  rw [sq_abs] at hs
  have hq : f^2 ≤ 2*A^2+2*B^2*t^2 := by nlinarith [sq_nonneg (A-B*t)]
  nlinarith [mul_le_mul_of_nonneg_right hq hd]

theorem slabOrbitalResidual_square_integrable {rho H S freq : ℝ}
    (hrho : 0 ≤ rho) (hH : 0 ≤ H) (hS : 0 ≤ S) (hfreq : 0 < freq)
    (u : PlanarPosition) : Integrable (fun x => slabOrbitalResidual rho H S freq u x^2) := by
  let A := 2*slabUniformBound rho H S
  let B := 2*Real.pi*rho
  have hA : 0 ≤ A := by
    have h := slabPotential_abs_bound hrho hH hS (0 : Position)
    have := abs_nonneg (slabPotential rho H S 0)
    dsimp [A, slabUniformBound]
    linarith
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hmajor : Integrable (fun x : Position =>
      2*A^2*localizedDensity freq u x+2*B^2*(‖x‖^4*localizedDensity freq u x)) :=
    ((localizedDensity_integrable hfreq u).const_mul _).add
      ((localizedDensity_fourth_moment_translate hfreq u).1.const_mul _)
  apply hmajor.mono'
    ((((slabPotential_continuous hrho hH hS).sub continuous_const).sub
      (continuous_const.mul (positionSplitCoordinates.continuous.snd.pow 2))).mul
      (continuumLocalizedMode_C7 freq u).continuous |>.pow 2).aestronglyMeasurable
  filter_upwards [] with x
  change ‖slabOrbitalResidual rho H S freq u x^2‖ ≤ _
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  have h := square_times_density_bound hA hB (sq_nonneg ‖x‖)
    (localizedDensity_nonnegative freq u x) (slabResidualMultiplier_abs_bound hrho hH hS x)
  convert h using 1 <;> first | (with_reducible_and_instances rfl) | (dsimp [slabOrbitalResidual, localizedDensity, A, B] <;> ring)

theorem slabOrbitalResidual_square_bound_seventySecond {rho H S freq R : ℝ}
    (hrho : 0 ≤ rho) (hH : 0 < H) (hS : 0 ≤ S) (hfreq : 0 < freq)
    (hR : 0 < R) (hRH : R ≤ H/2) (hRS : R ≤ S) (u : PlanarPosition) :
    (∫ x, slabOrbitalResidual rho H S freq u x^2) ≤
      2*(6*Real.pi*rho*S^3/H)^2+
      2*(64*rho*S/H)^2*localizedDensityMoment freq u 4+
      2*(2*slabUniformBound rho H S)^2*(localizedDensityMoment freq u 72/R^72)+
      2*(2*Real.pi*rho)^2*(localizedDensityMoment freq u 72/R^68) := by
  let K := Metric.closedBall (0 : Position) R
  let a := 6*Real.pi*rho*S^3/H
  let b := 64*rho*S/H
  let A := 2*slabUniformBound rho H S
  let B := 2*Real.pi*rho
  have hK : MeasurableSet K := Metric.isClosed_closedBall.measurableSet
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hA : 0 ≤ A := by
    have h := slabPotential_abs_bound hrho hH.le hS (0 : Position)
    have := abs_nonneg (slabPotential rho H S 0)
    dsimp [A, slabUniformBound]
    linarith
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hi := slabOrbitalResidual_square_integrable hrho hH.le hS hfreq u
  have hd := localizedDensity_integrable hfreq u
  have h4 := (localizedDensity_fourth_moment_translate hfreq u).1
  have hout (x : Position) (hx : x ∉ K) : R ≤ ‖x‖ := by
    exact (lt_of_not_ge (by simpa only [K, Metric.mem_closedBall, dist_zero_right] using hx)).le
  have hinner (x : Position) (hx : x ∈ K) : |slabResidualMultiplier rho H S x| ≤ a+b*‖x‖^2 := by
    have hnorm : ‖x‖ ≤ R := by simpa only [K, Metric.mem_closedBall, dist_zero_right] using hx
    have hcoord (i : Fin 3) : |x i| ≤ R := by
      simpa only [Real.norm_eq_abs] using (PiLp.norm_apply_le x i).trans hnorm
    have hxy : (x 0)^2+(x 1)^2 ≤ ‖x‖^2 := by
      have he := positionSplitCoordinates_norm_sq x
      have hp : ‖(positionSplitCoordinates x).1‖^2 = (x 0)^2+(x 1)^2 := by
        rw [EuclideanSpace.norm_sq_eq]
        simp only [Fin.sum_univ_two, positionSplitCoordinates_fst_zero, positionSplitCoordinates_fst_one, Real.norm_eq_abs, sq_abs]
      rw [hp] at he
      nlinarith [sq_nonneg (x 2)]
    have h := slabPotential_interior_error hrho hH hS x
      ((hcoord 0).trans hRH) ((hcoord 1).trans hRH) ((hcoord 2).trans hRS)
    change |slabResidualMultiplier rho H S x| ≤ _ at h
    calc
      _ ≤ 64*rho*S*((x 0)^2+(x 1)^2)/H+6*Real.pi*rho*S^3/H := h
      _ = a+b*((x 0)^2+(x 1)^2) := by dsimp [a,b]; ring
      _ ≤ _ := add_le_add le_rfl (mul_le_mul_of_nonneg_left hxy hb)
  have hinnerSq (x : Position) (hx : x ∈ K) : slabOrbitalResidual rho H S freq u x^2 ≤
      2*a^2*localizedDensity freq u x+2*b^2*(‖x‖^4*localizedDensity freq u x) := by
    have h := square_times_density_bound ha hb (sq_nonneg ‖x‖)
      (localizedDensity_nonnegative freq u x) (hinner x hx)
    convert h using 1 <;> first | (with_reducible_and_instances rfl) | (dsimp [slabOrbitalResidual, localizedDensity] <;> ring)
  have houterSq (x : Position) : slabOrbitalResidual rho H S freq u x^2 ≤
      2*A^2*localizedDensity freq u x+2*B^2*(‖x‖^4*localizedDensity freq u x) := by
    have h := square_times_density_bound hA hB (sq_nonneg ‖x‖)
      (localizedDensity_nonnegative freq u x) (slabResidualMultiplier_abs_bound hrho hH.le hS x)
    convert h using 1 <;> first | (with_reducible_and_instances rfl) | (dsimp [slabOrbitalResidual, localizedDensity, A, B] <;> ring)
  have hinside := setIntegral_mono_on hi.integrableOn
    ((hd.const_mul (2*a^2)).add (h4.const_mul (2*b^2))).integrableOn hK hinnerSq
  have houtside := setIntegral_mono_on hi.integrableOn
    ((hd.const_mul (2*A^2)).add (h4.const_mul (2*B^2))).integrableOn hK.compl
    (fun x _ => houterSq x)
  simp only [Pi.add_apply] at hinside houtside
  rw [integral_add (hd.const_mul (2*a^2)).integrableOn (h4.const_mul (2*b^2)).integrableOn,
    integral_const_mul, integral_const_mul] at hinside
  rw [integral_add (hd.const_mul (2*A^2)).integrableOn (h4.const_mul (2*B^2)).integrableOn,
    integral_const_mul, integral_const_mul] at houtside
  have hmass : (∫ x in K, localizedDensity freq u x) ≤ 1 := by
    rw [← localizedDensity_mass hfreq u]
    exact integral_mono_measure Measure.restrict_le_self
      (Filter.Eventually.of_forall (localizedDensity_nonnegative freq u)) hd
  have hmoment : (∫ x in K, ‖x‖^4*localizedDensity freq u x) ≤ localizedDensityMoment freq u 4 :=
    integral_mono_measure Measure.restrict_le_self
      (Filter.Eventually.of_forall (fun x => mul_nonneg (pow_nonneg (norm_nonneg x) 4)
        (localizedDensity_nonnegative freq u x))) h4
  have ht0 := localizedDensity_mass_tail_seventySecond hfreq hR u hK hout
  have ht4 := localizedDensity_fourth_tail_seventySecond hfreq hR u hK hout
  have hsum := add_le_add (hinside.trans (add_le_add
    (mul_le_mul_of_nonneg_left hmass (by positivity))
    (mul_le_mul_of_nonneg_left hmoment (by positivity))))
    (houtside.trans (add_le_add (mul_le_mul_of_nonneg_left ht0 (by positivity))
      (mul_le_mul_of_nonneg_left ht4 (by positivity))))
  rw [integral_add_compl hK hi] at hsum
  simpa only [mul_one, a, b, A, B, add_assoc] using hsum

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_PlanarWellOverlap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A well at any center has an off-diagonal matrix bound from the actual
orbital overlap. This also controls the small depth counterterms. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

theorem planarWellMatrix_le_overlap (u v w : PlanarPosition) :
    |planarWellMatrix u v w| ≤ PlanarSobolev.wellBound * planarModeOverlap u v := by
  have hi := (planarModeOverlap_integrable u v).const_mul PlanarSobolev.wellBound
  have h := norm_integral_le_of_norm_le (f := fun r =>
    normalizedPlanarMode (r - u) * manufacturedPlanarWell (r - w) * normalizedPlanarMode (r - v))
    hi (Filter.Eventually.of_forall (fun r => by
    rw [norm_mul, norm_mul, Real.norm_of_nonneg (normalizedPlanarMode_positive _).le,
      Real.norm_of_nonneg (normalizedPlanarMode_positive _).le]
    have hp := mul_le_mul_of_nonneg_right (PlanarSobolev.wellBound_spec (r - w))
      (mul_nonneg (normalizedPlanarMode_positive (r - u)).le (normalizedPlanarMode_positive (r - v)).le)
    convert hp using 1
    all_goals try with_reducible_and_instances rfl
    ring))
  simpa only [Real.norm_eq_abs, integral_const_mul, planarWellMatrix, planarModeOverlap] using h

theorem planarWellMatrix_overlap_decay (u v w : PlanarPosition) :
    |planarWellMatrix u v w| ≤
      (PlanarSobolev.wellBound * planarOverlapConstant) * Real.exp (-(9 / 10 : ℝ) * ‖u - v‖) := by
  exact (planarWellMatrix_le_overlap u v w).trans ((mul_le_mul_of_nonneg_left
    (planarModeOverlap_decay u v) PlanarSobolev.wellBound_nonnegative).trans_eq (mul_assoc _ _ _).symm)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_LocalizedCountertermMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual counterterm matrix estimates: the onsite term is the required
negative direct-interaction sum; other diagonal terms have two tails and
off-diagonal terms have the actual overlap decay. -/

noncomputable section
open scoped BigOperators
namespace ContinuumCoulomb

theorem localizedCountertermMatrix_diagonal_error_eq (freq : ℝ) {m : ℕ}
    (u : Fin m → PlanarPosition) (i : Fin m) :
    localizedCountertermMatrix freq u i i + localizedOffsiteSum freq u i =
      ∑ k, if k = i then 0 else localizedCounterterm freq u k * planarWellMatrix (u i) (u i) (u k) := by
  classical
  have hpoint (k : Fin m) :
      localizedCounterterm freq u k * planarWellMatrix (u i) (u i) (u k) =
      (if k = i then localizedCounterterm freq u i * planarWellMatrix (u i) (u i) (u i) else 0) +
      (if k = i then 0 else localizedCounterterm freq u k * planarWellMatrix (u i) (u i) (u k)) := by
    by_cases hk : k = i
    · subst k
      simp only [ite_true, if_true, add_zero]
    · simp only [hk, ite_false, if_false, zero_add]
  have hs := Finset.sum_congr (s₁ := Finset.univ) rfl (fun k _ => hpoint k)
  unfold localizedCountertermMatrix
  rw [hs, Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true, if_true, localizedCounterterm_diagonal]
  ring

theorem localizedCountertermMatrix_diagonal_error_bound {freq D : ℝ} (hfreq : 0 < freq)
    {m : ℕ} (u : Fin m → PlanarPosition) (hsep : ∀ i j, i ≠ j → D ≤ ‖u i - u j‖) (i : Fin m) :
    |localizedCountertermMatrix freq u i i + localizedOffsiteSum freq u i| ≤
      (m : ℝ) ^ 2 * localizedCountertermBound freq * planarWellMatrixConstant *
        Real.exp (-(19 / 10 : ℝ) * D) := by
  rw [localizedCountertermMatrix_diagonal_error_eq]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ _k : Fin m, (m * localizedCountertermBound freq) *
        (planarWellMatrixConstant * Real.exp (-(19 / 10 : ℝ) * D)) := by
      apply Finset.sum_le_sum
      intro k _
      split_ifs with hk
      · rw [abs_zero]
        exact mul_nonneg (mul_nonneg (Nat.cast_nonneg m) (localizedCountertermBound_nonnegative freq))
          (mul_nonneg planarWellMatrixConstant_nonnegative (Real.exp_pos _).le)
      · rw [abs_mul, abs_of_nonneg (localizedCounterterm_nonnegative freq u k)]
        exact mul_le_mul (localizedCounterterm_bound hfreq u k)
          (planarWellMatrix_two_far _ _ _ (hsep i k (Ne.symm hk)) (hsep i k (Ne.symm hk)))
          (abs_nonneg _) (mul_nonneg (Nat.cast_nonneg m) (localizedCountertermBound_nonnegative freq))
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring

theorem localizedCountertermMatrix_offdiagonal_bound {freq : ℝ} (hfreq : 0 < freq)
    {m : ℕ} (u : Fin m → PlanarPosition) (i j : Fin m) :
    |localizedCountertermMatrix freq u i j| ≤
      (m : ℝ) ^ 2 * localizedCountertermBound freq *
        (PlanarSobolev.wellBound * planarOverlapConstant) * Real.exp (-(9 / 10 : ℝ) * ‖u i - u j‖) := by
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ _k : Fin m, (m * localizedCountertermBound freq) *
        ((PlanarSobolev.wellBound * planarOverlapConstant) * Real.exp (-(9 / 10 : ℝ) * ‖u i - u j‖)) := by
      apply Finset.sum_le_sum
      intro k _
      rw [abs_mul, abs_of_nonneg (localizedCounterterm_nonnegative freq u k)]
      exact mul_le_mul (localizedCounterterm_bound hfreq u k) (planarWellMatrix_overlap_decay _ _ _)
        (abs_nonneg _) (mul_nonneg (Nat.cast_nonneg m) (localizedCountertermBound_nonnegative freq))
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_LocalizedWellMatrix
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual three-dimensional well matrix elements equal the planar ones:
the transverse Gaussian contributes exactly its unit squared mass. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

theorem localizedWellIntegrand_split (freq : ℝ) (u v w : PlanarPosition) (x : Position) :
    localizedWellIntegrand freq u v w x =
      (normalizedPlanarMode ((positionSplitCoordinates x).1 - u) *
        manufacturedPlanarWell ((positionSplitCoordinates x).1 - w) *
        normalizedPlanarMode ((positionSplitCoordinates x).1 - v)) *
        verticalMode freq (positionSplitCoordinates x).2 ^ 2 := by
  unfold localizedWellIntegrand continuumLocalizedMode localizedMode
  ring

theorem localizedWellIntegrand_integrable {freq : ℝ} (hfreq : 0 < freq) (u v w : PlanarPosition) :
    Integrable (localizedWellIntegrand freq u v w) := by
  have hi : Integrable (fun p : SplitPosition =>
      (normalizedPlanarMode (p.1 - u) * manufacturedPlanarWell (p.1 - w) * normalizedPlanarMode (p.1 - v)) *
        verticalMode freq p.2 ^ 2) := by
    rw [Measure.volume_eq_prod]
    exact (planarWellMatrix_integrable u v w).mul_prod (verticalMode_square_integrable hfreq)
  have h := positionSplitCoordinates_measurePreserving.integrable_comp_of_integrable hi
  simpa only [Function.comp_def, ← localizedWellIntegrand_split] using h

theorem localizedWellIntegrand_integral {freq : ℝ} (hfreq : 0 < freq) (u v w : PlanarPosition) :
    (∫ x, localizedWellIntegrand freq u v w x) = planarWellMatrix u v w := by
  simp_rw [localizedWellIntegrand_split]
  rw [positionSplitCoordinates_integral (fun p =>
      (normalizedPlanarMode (p.1 - u) * manufacturedPlanarWell (p.1 - w) * normalizedPlanarMode (p.1 - v)) *
        verticalMode freq p.2 ^ 2), Measure.volume_eq_prod, integral_prod_mul
      (fun r => normalizedPlanarMode (r - u) * manufacturedPlanarWell (r - w) * normalizedPlanarMode (r - v))
      (fun z => verticalMode freq z ^ 2), verticalMode_normalized hfreq, mul_one]
  rfl

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_PlanarMultiwellMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The unperturbed shifted multiwell matrix: its leading off-diagonal
entry is the actual hopping, and every remaining term has two tail factors.
No independent matrix approximation is assumed. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb

theorem planarMultiwellMatrix_error_eq {m : ℕ} (u : Fin m → PlanarPosition) (i j : Fin m) :
    planarMultiwellMatrix u i j - planarHoppingMatrix u i j =
      ∑ k, if k ≠ i ∧ k ≠ j then planarWellMatrix (u i) (u j) (u k) else 0 := by
  classical
  have hpoint (k : Fin m) :
      (if k = j then 0 else planarWellMatrix (u i) (u j) (u k)) =
      (if k = i then (if i = j then 0 else planarWellMatrix (u i) (u j) (u i)) else 0) +
      (if k ≠ i ∧ k ≠ j then planarWellMatrix (u i) (u j) (u k) else 0) := by
    by_cases hki : k = i
    · subst k
      by_cases hij : i = j
      · subst j
        simp only [ite_true, if_true, ne_eq, not_true_eq_false, false_and, ite_false, if_false, add_zero]
      · simp only [hij, ite_false, if_false, ite_true, if_true, ne_eq, not_true_eq_false, false_and, add_zero]
    · by_cases hkj : k = j
      · subst k
        simp only [hki, ite_false, if_false, ite_true, if_true, ne_eq, not_true_eq_false, and_false, add_zero]
      · simp only [hki, hkj, ite_false, if_false, ne_eq, not_false_eq_true, and_self, ite_true, if_true, zero_add]
  have hsum := Finset.sum_congr (s₁ := Finset.univ) rfl (fun k _ => hpoint k)
  unfold planarMultiwellMatrix planarHoppingMatrix
  rw [hsum, Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true, if_true, planarWellMatrix_hopping]
  ring

theorem planarMultiwellMatrix_error_bound {D : ℝ} {m : ℕ}
    (u : Fin m → PlanarPosition) (hsep : ∀ i j, i ≠ j → D ≤ ‖u i - u j‖)
    (i j : Fin m) :
    |planarMultiwellMatrix u i j - planarHoppingMatrix u i j| ≤
      m * planarWellMatrixConstant * Real.exp (-(19 / 10 : ℝ) * D) := by
  rw [planarMultiwellMatrix_error_eq]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ _k : Fin m, planarWellMatrixConstant * Real.exp (-(19 / 10 : ℝ) * D) :=
      Finset.sum_le_sum (fun k _ => by
        split_ifs with hk
        · exact planarWellMatrix_two_far _ _ _ (hsep i k hk.1.symm) (hsep j k hk.2.symm)
        · rw [abs_zero]
          exact mul_nonneg planarWellMatrixConstant_nonnegative (Real.exp_pos _).le)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_LocalizedOneBody
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual differential action of the full multiwell operator on the
localized modes. Subtraction of the common ground energy leaves exactly the
sum of other wells, so its matrix is the checked hopping matrix plus the
explicit two-tail error. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb

theorem multiwellAction_localizedMode (freq : ℝ) {m : ℕ} (u : Fin m → PlanarPosition)
    (j : Fin m) (p : SplitPosition) :
    multiwellAction freq u (localizedMode freq (u j)) p - ((-1 / 2 : ℝ) + freq / 2) * localizedMode freq (u j) p =
      ∑ k, if k = j then 0 else manufacturedPlanarWell (p.1 - u k) * localizedMode freq (u j) p := by
  classical
  have hs : (∑ k, manufacturedPlanarWell (p.1 - u k)) =
      manufacturedPlanarWell (p.1 - u j) + (∑ k, if k = j then 0 else manufacturedPlanarWell (p.1 - u k)) := by
    calc
      _ = ∑ k, ((if k = j then manufacturedPlanarWell (p.1 - u j) else 0) +
          (if k = j then 0 else manufacturedPlanarWell (p.1 - u k))) := by
        apply Finset.sum_congr rfl
        intro k _
        by_cases hk : k = j <;> simp [hk]
      _ = _ := by rw [Finset.sum_add_distrib]; simp
  have he := localizedMode_eigen_equation freq (u j) p
  unfold localizedPotential at he
  unfold multiwellAction multiwellPotential
  rw [hs]
  have hm : (∑ k, if k = j then 0 else manufacturedPlanarWell (p.1 - u k)) * localizedMode freq (u j) p =
      ∑ k, if k = j then 0 else manufacturedPlanarWell (p.1 - u k) * localizedMode freq (u j) p := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k _
    split_ifs <;> simp only [zero_mul]
  rw [← hm]
  nlinarith only [he]

theorem localizedOneBodyIntegrand_eq (freq : ℝ) {m : ℕ} (u : Fin m → PlanarPosition)
    (i j : Fin m) (x : Position) :
    localizedOneBodyIntegrand freq u i j x =
      ∑ k, if k = j then 0 else localizedWellIntegrand freq (u i) (u j) (u k) x := by
  classical
  unfold localizedOneBodyIntegrand
  change continuumLocalizedMode freq (u i) x *
    (multiwellAction freq u (localizedMode freq (u j)) (positionSplitCoordinates x) -
      ((-1 / 2 : ℝ) + freq / 2) * localizedMode freq (u j) (positionSplitCoordinates x)) = _
  rw [multiwellAction_localizedMode, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  split_ifs
  · simp only [mul_zero]
  · unfold localizedWellIntegrand continuumLocalizedMode
    ring

theorem localizedOneBodyIntegrand_integrable {freq : ℝ} (hfreq : 0 < freq)
    {m : ℕ} (u : Fin m → PlanarPosition) (i j : Fin m) :
    Integrable (localizedOneBodyIntegrand freq u i j) := by
  classical
  change Integrable (fun x => localizedOneBodyIntegrand freq u i j x)
  simp_rw [localizedOneBodyIntegrand_eq]
  apply integrable_finsetSum
  intro k _
  by_cases hk : k = j
  · simp only [hk, ite_true, if_true]
    exact integrable_zero Position ℝ volume
  · simp only [hk, ite_false, if_false]
    exact localizedWellIntegrand_integrable hfreq _ _ _

theorem localizedOneBodyMatrix_eq {freq : ℝ} (hfreq : 0 < freq)
    {m : ℕ} (u : Fin m → PlanarPosition) (i j : Fin m) :
    localizedOneBodyMatrix freq u i j = planarMultiwellMatrix u i j := by
  classical
  unfold localizedOneBodyMatrix
  simp_rw [localizedOneBodyIntegrand_eq]
  rw [integral_finsetSum]
  · unfold planarMultiwellMatrix
    apply Finset.sum_congr rfl
    intro k _
    by_cases hk : k = j
    · simp only [hk, ite_true, if_true, integral_zero]
    · simp only [hk, ite_false, if_false]
      exact localizedWellIntegrand_integral hfreq _ _ _
  · intro k _
    by_cases hk : k = j
    · simp only [hk, ite_true, if_true]
      exact integrable_zero Position ℝ volume
    · simp only [hk, ite_false, if_false]
      exact localizedWellIntegrand_integrable hfreq _ _ _

theorem localizedOneBodyMatrix_error_bound {freq D : ℝ} (hfreq : 0 < freq)
    {m : ℕ} (u : Fin m → PlanarPosition) (hsep : ∀ i j, i ≠ j → D ≤ ‖u i - u j‖) (i j : Fin m) :
    |localizedOneBodyMatrix freq u i j - planarHoppingMatrix u i j| ≤
      m * planarWellMatrixConstant * Real.exp (-(19 / 10 : ℝ) * D) := by
  rw [localizedOneBodyMatrix_eq hfreq]
  exact planarMultiwellMatrix_error_bound u hsep i j

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_LocalizedCorrectedOneBody
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual one-body operator including well-depth counterterms. Its
shifted matrix is exactly the base multiwell matrix plus the weighted well
matrix divided by the physical scale. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb

theorem localizedCorrectedOneBodyIntegrand_eq (freq scale : ℝ) {m : ℕ}
    (u : Fin m → PlanarPosition) (i j : Fin m) (x : Position) :
    localizedCorrectedOneBodyIntegrand freq scale u i j x = localizedOneBodyIntegrand freq u i j x +
      scale⁻¹ * ∑ k, localizedCounterterm freq u k * localizedWellIntegrand freq (u i) (u j) (u k) x := by
  have hs : continuumLocalizedMode freq (u i) x *
      (scale⁻¹ * (∑ k, localizedCounterterm freq u k *
        manufacturedPlanarWell ((positionSplitCoordinates x).1 - u k)) * continuumLocalizedMode freq (u j) x) =
      scale⁻¹ * ∑ k, localizedCounterterm freq u k * localizedWellIntegrand freq (u i) (u j) (u k) x := by
    simp only [Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k _
    unfold localizedWellIntegrand
    ring
  unfold localizedCorrectedOneBodyIntegrand correctedMultiwellAction localizedOneBodyIntegrand
  change continuumLocalizedMode freq (u i) x *
      (multiwellAction freq u (localizedMode freq (u j)) (positionSplitCoordinates x) +
        scale⁻¹ * (∑ k, localizedCounterterm freq u k *
          manufacturedPlanarWell ((positionSplitCoordinates x).1 - u k)) * continuumLocalizedMode freq (u j) x -
        ((-1 / 2 : ℝ) + freq / 2) * continuumLocalizedMode freq (u j) x) = _
  nlinarith only [hs]

theorem localizedCorrectedOneBodyIntegrand_integrable {freq : ℝ} (hfreq : 0 < freq)
    (scale : ℝ) {m : ℕ} (u : Fin m → PlanarPosition) (i j : Fin m) :
    Integrable (localizedCorrectedOneBodyIntegrand freq scale u i j) := by
  have hi : Integrable (fun x => ∑ k, localizedCounterterm freq u k *
      localizedWellIntegrand freq (u i) (u j) (u k) x) :=
    integrable_finsetSum _ (fun k _ => (localizedWellIntegrand_integrable hfreq _ _ _).const_mul _)
  change Integrable (fun x => localizedCorrectedOneBodyIntegrand freq scale u i j x)
  simp_rw [localizedCorrectedOneBodyIntegrand_eq]
  exact (localizedOneBodyIntegrand_integrable hfreq u i j).add (hi.const_mul _)

theorem localizedCorrectedOneBodyMatrix_eq {freq : ℝ} (hfreq : 0 < freq)
    (scale : ℝ) {m : ℕ} (u : Fin m → PlanarPosition) (i j : Fin m) :
    localizedCorrectedOneBodyMatrix freq scale u i j =
      localizedOneBodyMatrix freq u i j + scale⁻¹ * localizedCountertermMatrix freq u i j := by
  have hi (k : Fin m) : Integrable (fun x => localizedCounterterm freq u k *
      localizedWellIntegrand freq (u i) (u j) (u k) x) :=
    (localizedWellIntegrand_integrable hfreq _ _ _).const_mul _
  unfold localizedCorrectedOneBodyMatrix
  simp_rw [localizedCorrectedOneBodyIntegrand_eq]
  rw [integral_add (localizedOneBodyIntegrand_integrable hfreq u i j)
      ((integrable_finsetSum Finset.univ (fun k _ => hi k)).const_mul _), integral_const_mul,
    integral_finsetSum Finset.univ (fun k _ => hi k)]
  simp only [integral_const_mul, localizedWellIntegrand_integral hfreq]
  rfl

theorem localizedCorrectedOneBodyMatrix_scaled {freq scale : ℝ} (hfreq : 0 < freq) (hscale : scale ≠ 0)
    {m : ℕ} (u : Fin m → PlanarPosition) (i j : Fin m) :
    scale * localizedCorrectedOneBodyMatrix freq scale u i j =
      scale * localizedOneBodyMatrix freq u i j + localizedCountertermMatrix freq u i j := by
  rw [localizedCorrectedOneBodyMatrix_eq hfreq, mul_add, ← mul_assoc, mul_inv_cancel₀ hscale, one_mul]

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_LocalizedWellResidual
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual other-well residual has exponentially small L2 mass.
The square of a nonpositive bounded well is controlled by its negative
well matrix element, so the checked two-tail estimate applies directly. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

theorem localizedWellAction_continuous (freq : ℝ) (u w : PlanarPosition) :
    Continuous (localizedWellAction freq u w) :=
  (manufacturedPlanarWell_C7.continuous.comp
    ((positionSplitCoordinates.continuous.fst).sub continuous_const)).mul
      (continuumLocalizedMode_C7 freq u).continuous

theorem localizedWellAction_memLp {freq : ℝ} (hfreq : 0 < freq) (u w : PlanarPosition) :
    MemLp (localizedWellAction freq u w) 2 := by
  apply (continuumLocalizedMode_memLp hfreq u).of_le_mul
    (c := PlanarSobolev.wellBound) (localizedWellAction_continuous freq u w).aestronglyMeasurable
  filter_upwards [] with x
  rw [localizedWellAction, norm_mul]
  exact mul_le_mul_of_nonneg_right (PlanarSobolev.wellBound_spec _) (norm_nonneg _)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_LocalizedMultiwellResidual
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! L2 bounds on the actual differential residuals of the localized modes.
The estimate is polynomial in the number of wells; it does not sum over a
many-electron occupation basis. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb

theorem localizedMultiwellResidual_eq (freq : ℝ) {m : ℕ}
    (u : Fin m → PlanarPosition) (j : Fin m) (x : Position) :
    localizedMultiwellResidual freq u j x =
      multiwellAction freq u (localizedMode freq (u j)) (positionSplitCoordinates x) -
        ((-1/2 : ℝ)+freq/2)*continuumLocalizedMode freq (u j) x := by
  rw [show continuumLocalizedMode freq (u j) x =
    localizedMode freq (u j) (positionSplitCoordinates x) from rfl,
    multiwellAction_localizedMode]
  rfl

theorem localizedMultiwellResidual_memLp {freq : ℝ} (hfreq : 0 < freq)
    {m : ℕ} (u : Fin m → PlanarPosition) (j : Fin m) :
    MemLp (localizedMultiwellResidual freq u j) 2 := by
  classical
  apply memLp_finsetSum
  intro k _
  by_cases hk : k = j
  · simp only [hk, ite_true, if_true]
    exact MemLp.zero
  · simp only [hk, ite_false, if_false]
    exact localizedWellAction_memLp hfreq _ _

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_ManufacturedOrbitalResidual
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The residual for the actual manufactured one-body operator is the sum
of the checked off-site, finite-slab, and cutoff/counterterm residuals. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

private theorem slab_residual_continuous {rho H S : ℝ} (hrho : 0 ≤ rho)
    (hH : 0 ≤ H) (hS : 0 ≤ S) (freq : ℝ) (u : PlanarPosition) :
    Continuous (slabOrbitalResidual rho H S freq u) :=
  (((slabPotential_continuous hrho hH hS).sub continuous_const).sub
    (continuous_const.mul (positionSplitCoordinates.continuous.snd.pow 2))).mul
    (continuumLocalizedMode_C7 freq u).continuous

private theorem well_residual_continuous (freq scale S : ℝ) {m : ℕ}
    (u : Fin m → PlanarPosition) (j : Fin m) :
    Continuous (wellFieldOrbitalResidual freq scale S u j) :=
  ((manufacturedWellField_C7 freq scale S u).continuous.sub
    ((planarWellSum_continuous u).comp positionSplitCoordinates.continuous.fst)).mul
    (continuumLocalizedMode_C7 freq (u j)).continuous

theorem manufacturedOrbitalResidual_memLp {rho H S freq : ℝ}
    (hrho : 0 ≤ rho) (hH : 0 ≤ H) (hS : 0 ≤ S) (hfreq : 0 < freq)
    (scale : ℝ) {m : ℕ} (u : Fin m → PlanarPosition) {δ : ℝ} (hδ : 0 ≤ δ)
    (hcoeff : ∀ i, 0 ≤ localizedCounterterm freq u i/scale ∧
      localizedCounterterm freq u i/scale ≤ δ) (j : Fin m) :
    MemLp (manufacturedOrbitalResidual rho H S freq scale u j) 2 := by
  have hs : MemLp (slabOrbitalResidual rho H S freq (u j)) 2 :=
    (memLp_two_iff_integrable_sq (slab_residual_continuous hrho hH hS freq (u j)).aestronglyMeasurable).mpr
      (slabOrbitalResidual_square_integrable hrho hH hS hfreq (u j))
  have hw : MemLp (wellFieldOrbitalResidual freq scale S u j) 2 :=
    (memLp_two_iff_integrable_sq (well_residual_continuous freq scale S u j).aestronglyMeasurable).mpr
      (wellFieldOrbitalResidual_square_integrable hfreq scale S u hδ hcoeff j)
  exact ((localizedMultiwellResidual_memLp hfreq u j).add hs).add hw

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_ManyBody_FiniteBoxMatrix
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite-box correction to the intended one-body matrix. The well-depth
counterterm remains part of the target matrix; only its vertical truncation
and the finite slab approximation contribute to this error. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

private theorem slabOrbitalResidual_continuous {rho H S : ℝ} (hrho : 0 ≤ rho)
    (hH : 0 ≤ H) (hS : 0 ≤ S) (freq : ℝ) (u : PlanarPosition) :
    Continuous (slabOrbitalResidual rho H S freq u) :=
  (((slabPotential_continuous hrho hH hS).sub continuous_const).sub
    (continuous_const.mul (positionSplitCoordinates.continuous.snd.pow 2))).mul
    (continuumLocalizedMode_C7 freq u).continuous

theorem finiteBoxOrbitalResidual_continuous {rho H S : ℝ} (hrho : 0 ≤ rho)
    (hH : 0 ≤ H) (hS : 0 ≤ S) (freq scale : ℝ) {m : ℕ}
    (u : Fin m → PlanarPosition) (j : Fin m) :
    Continuous (finiteBoxOrbitalResidual rho H S freq scale u j) :=
  (slabOrbitalResidual_continuous hrho hH hS freq (u j)).add
    (finiteWellOrbitalResidual_continuous freq scale S u j)

theorem finiteBoxOrbitalResidual_memLp {rho H S freq : ℝ}
    (hrho : 0 ≤ rho) (hH : 0 ≤ H) (hS : 0 < S) (hfreq : 0 < freq)
    (scale : ℝ) {m : ℕ} (u : Fin m → PlanarPosition) {δ : ℝ} (hδ : 0 ≤ δ)
    (hcoeff : ∀ i, 0 ≤ localizedCounterterm freq u i/scale ∧ localizedCounterterm freq u i/scale ≤ δ)
    (j : Fin m) : MemLp (finiteBoxOrbitalResidual rho H S freq scale u j) 2 := by
  have hs := (memLp_two_iff_integrable_sq
    (slabOrbitalResidual_continuous hrho hH hS.le freq (u j)).aestronglyMeasurable).mpr
    (slabOrbitalResidual_square_integrable hrho hH hS.le hfreq (u j))
  have hw := (memLp_two_iff_integrable_sq
    (finiteWellOrbitalResidual_continuous freq scale S u j).aestronglyMeasurable).mpr
    (finiteWellOrbitalResidual_square_bound hfreq hS scale u hδ hcoeff j).1
  exact hs.add hw

theorem finiteBoxOrbitalResidual_square_bound {rho H S freq r : ℝ}
    (hrho : 0 ≤ rho) (hH : 0 < H) (hS : 0 < S) (hfreq : 0 < freq)
    (hr : 0 < r) (hrH : r ≤ H/2) (hrS : r ≤ S)
    (scale : ℝ) {m : ℕ} (u : Fin m → PlanarPosition) {δ : ℝ} (hδ : 0 ≤ δ)
    (hcoeff : ∀ i, 0 ≤ localizedCounterterm freq u i/scale ∧ localizedCounterterm freq u i/scale ≤ δ)
    (j : Fin m) :
    (∫ x, finiteBoxOrbitalResidual rho H S freq scale u j x^2) ≤
      finiteBoxOrbitalSquaredError rho H S freq δ r u j := by
  have hs := slabOrbitalResidual_square_integrable hrho hH.le hS.le hfreq (u j)
  obtain ⟨hw,hwb⟩ := finiteWellOrbitalResidual_square_bound hfreq hS scale u hδ hcoeff j
  have h := integral_mono (finiteBoxOrbitalResidual_memLp hrho hH.le hS hfreq scale u hδ hcoeff j).integrable_sq
    ((hs.add hw).const_mul 2) (fun x => show
      finiteBoxOrbitalResidual rho H S freq scale u j x^2 ≤
        2*(slabOrbitalResidual rho H S freq (u j) x^2+finiteWellOrbitalResidual freq scale S u j x^2) from by
      dsimp [finiteBoxOrbitalResidual]
      nlinarith [sq_nonneg (slabOrbitalResidual rho H S freq (u j) x-finiteWellOrbitalResidual freq scale S u j x)])
  rw [integral_const_mul] at h
  simp only [Pi.add_apply] at h
  rw [integral_add hs hw] at h
  have hsb := slabOrbitalResidual_square_bound_seventySecond hrho hH hS.le hfreq hr hrH hrS (u j)
  unfold finiteBoxOrbitalSquaredError
  linarith

theorem manufacturedRawOneBodyMatrix_integrand (rho H S freq scale : ℝ) {m : ℕ}
    (u : Fin m → PlanarPosition) (i j : Fin m) (x : Position) :
    continuumLocalizedMode freq (u i) x*manufacturedOrbitalResidual rho H S freq scale u j x =
      localizedCorrectedOneBodyIntegrand freq scale u i j x+
        continuumLocalizedMode freq (u i) x*finiteBoxOrbitalResidual rho H S freq scale u j x := by
  have hc : countertermWellSum freq scale u (positionSplitCoordinates x).1-
      planarWellSum u (positionSplitCoordinates x).1 =
      scale⁻¹*∑ k, localizedCounterterm freq u k*manufacturedPlanarWell ((positionSplitCoordinates x).1-u k) := by
    rw [countertermWellSum_sub_eq,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    simp only [div_eq_mul_inv]
    ring
  rw [manufacturedOrbitalResidual,localizedMultiwellResidual_eq]
  unfold localizedCorrectedOneBodyIntegrand correctedMultiwellAction finiteBoxOrbitalResidual
    finiteWellOrbitalResidual wellFieldOrbitalResidual
  change _ = continuumLocalizedMode freq (u i) x*
    (multiwellAction freq u (localizedMode freq (u j)) (positionSplitCoordinates x)+
      scale⁻¹*(∑ k, localizedCounterterm freq u k*manufacturedPlanarWell ((positionSplitCoordinates x).1-u k))*
        continuumLocalizedMode freq (u j) x-((-1/2:ℝ)+freq/2)*continuumLocalizedMode freq (u j) x)+_
  linear_combination continuumLocalizedMode freq (u i) x*continuumLocalizedMode freq (u j) x*hc

theorem manufacturedRawOneBodyMatrix_error_integral {rho H S freq : ℝ}
    (hrho : 0 ≤ rho) (hH : 0 ≤ H) (hS : 0 < S) (hfreq : 0 < freq)
    (scale : ℝ) {m : ℕ} (u : Fin m → PlanarPosition) {δ : ℝ} (hδ : 0 ≤ δ)
    (hcoeff : ∀ i, 0 ≤ localizedCounterterm freq u i/scale ∧ localizedCounterterm freq u i/scale ≤ δ)
    (i j : Fin m) :
    |manufacturedRawOneBodyMatrix rho H S freq scale u i j-
      localizedCorrectedOneBodyMatrix freq scale u i j|^2 ≤
        (∫ x, finiteBoxOrbitalResidual rho H S freq scale u j x^2) := by
  have hm := continuumLocalizedMode_memLp hfreq (u i)
  have hf := finiteBoxOrbitalResidual_memLp hrho hH hS hfreq scale u hδ hcoeff j
  have hi : Integrable (fun x => continuumLocalizedMode freq (u i) x*
      finiteBoxOrbitalResidual rho H S freq scale u j x) := hm.integrable_mul hf
  have he : manufacturedRawOneBodyMatrix rho H S freq scale u i j-
      localizedCorrectedOneBodyMatrix freq scale u i j =
      ∫ x, continuumLocalizedMode freq (u i) x*finiteBoxOrbitalResidual rho H S freq scale u j x := by
    unfold manufacturedRawOneBodyMatrix
    simp_rw [manufacturedRawOneBodyMatrix_integrand]
    rw [integral_add (localizedCorrectedOneBodyIntegrand_integrable hfreq scale u i j) hi]
    change localizedCorrectedOneBodyMatrix freq scale u i j+_ -
      localizedCorrectedOneBodyMatrix freq scale u i j = _
    ring
  have hmass : (∫ x, continuumLocalizedMode freq (u i) x^2) = 1 := localizedDensity_mass hfreq (u i)
  have hpair := (weighted_source_pairing (fun _ => 1) _ _ measurable_const
    (continuumLocalizedMode_C7 freq (u i)).continuous.measurable
    (finiteBoxOrbitalResidual_continuous hrho hH hS.le freq scale u j).measurable
    (by simpa only [abs_one,one_mul] using hm.integrable_sq)
    (by simpa only [abs_one,one_mul] using hf.integrable_sq)).2
  simp only [abs_one,one_mul,hmass] at hpair
  rw [he]
  exact hpair


end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Nuclei_SlabResidualScale
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A polynomial choice of slab dimensions makes the actual orbital
residual small. The twenty-fourth moment absorbs the total slab mass. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

theorem slabDomain_volume {H S : ℝ} (hH : 0 ≤ H) (hS : 0 ≤ S) :
    volume.real (slabDomain H S) = 8*H^2*S := by
  have h := (slabProduct_measurePreserving H S).measureReal_preimage
    (s := Set.univ) MeasurableSet.univ.nullMeasurableSet
  rw [Set.preimage_univ, measureReal_restrict_apply_univ] at h
  rw [← h, Measure.real, slabProductMeasure, Measure.pi_univ, Fin.prod_univ_three,
    ENNReal.toReal_mul, ENNReal.toReal_mul]
  simp only [slabAxisMeasure, Measure.restrict_apply_univ, Real.volume_Icc]
  norm_num [slabSide, ENNReal.toReal_ofReal, hH, hS, Fin.ext_iff]
  ring

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Nuclei_SlabHighAspectRatio
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A slab aspect ratio compatible with the nuclear cubature scale.
The 72nd value moment permits horizontal radius T^10 at height T. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

theorem slabUniformBound_tenthPower {rho T : ℝ} (hrho : 0 ≤ rho) (hT : 1 ≤ T) :
    slabUniformBound rho (T^10) T ≤ slabGrowthConstant rho*T^21 := by
  rw [slabUniformBound, slabDomain_volume (by positivity) (by linarith)]
  have hp : 1 ≤ T^21 := one_le_pow₀ hT
  have h1 : rho*NeutralAtom.kernelBallMass 1 ≤ rho*|NeutralAtom.kernelBallMass 1| *T^21 := by
    calc
      _ ≤ rho*|NeutralAtom.kernelBallMass 1| := mul_le_mul_of_nonneg_left (le_abs_self _) hrho
      _ ≤ _ := le_mul_of_one_le_right (mul_nonneg hrho (abs_nonneg _)) hp
  dsimp [slabGrowthConstant]
  nlinarith only [h1]

private theorem div_pow_le_div_fourteenth {T C : ℝ} (hT : 1 ≤ T) (hC : 0 ≤ C)
    {k : ℕ} (hk : 14 ≤ k) : C/T^k ≤ C/T^14 :=
  div_le_div_of_nonneg_left hC (by positivity) (pow_le_pow_right₀ hT hk)

theorem slabSeventySecondTail_tenthPower_bound {rho T freq : ℝ}
    (hrho : 0 ≤ rho) (hT : 2 ≤ T) (u : PlanarPosition) :
    2*(6*Real.pi*rho*T^3/T^10)^2+
      2*(64*rho*T/T^10)^2*localizedDensityMoment freq u 4+
      2*(2*slabUniformBound rho (T^10) T)^2*(localizedDensityMoment freq u 72/T^72)+
      2*(2*Real.pi*rho)^2*(localizedDensityMoment freq u 72/T^68) ≤
      slabResidualSeventySecondBound rho freq u/T^14 := by
  have hTpos : 0 < T := by linarith
  have hT1 : 1 ≤ T := by linarith
  have hB0 : 0 ≤ slabUniformBound rho (T^10) T := by
    have h0 := slabPotential_abs_bound hrho (pow_nonneg hTpos.le 10) hTpos.le (0 : Position)
    exact (abs_nonneg _).trans h0
  have hB := (sq_le_sq₀ hB0 (by dsimp [slabGrowthConstant]; positivity)).mpr
    (slabUniformBound_tenthPower hrho hT1)
  have hBterm : 2*(2*slabUniformBound rho (T^10) T)^2*
      (localizedDensityMoment freq u 72/T^72) ≤
      8*(slabGrowthConstant rho)^2*localizedDensityMoment freq u 72/T^30 := by
    have hb := mul_le_mul_of_nonneg_right hB
      (show 0 ≤ 8*(localizedDensityMoment freq u 72/T^72) by
        exact mul_nonneg (by norm_num) (div_nonneg (localizedDensityMoment_nonnegative _ _ _)
          (pow_nonneg hTpos.le _)))
    convert hb using 1
    all_goals try with_reducible_and_instances rfl
    all_goals field_simp [ne_of_gt hTpos]
    all_goals ring
  have he1 : 2*(6*Real.pi*rho*T^3/T^10)^2 = 72*Real.pi^2*rho^2/T^14 := by
    field_simp [ne_of_gt hTpos]
    ring
  have he2 : 2*(64*rho*T/T^10)^2*localizedDensityMoment freq u 4 =
      8192*rho^2*localizedDensityMoment freq u 4/T^18 := by
    field_simp [ne_of_gt hTpos]
    ring
  have he4 : 2*(2*Real.pi*rho)^2*(localizedDensityMoment freq u 72/T^68) =
      8*Real.pi^2*rho^2*localizedDensityMoment freq u 72/T^68 := by ring
  rw [he1,he2,he4]
  have h2 := div_pow_le_div_fourteenth hT1
    (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ)≤8192) (sq_nonneg rho))
      (localizedDensityMoment_nonnegative freq u 4)) (by decide : 14 ≤ 18)
  have h3 := div_pow_le_div_fourteenth hT1
    (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ)≤8) (sq_nonneg (slabGrowthConstant rho)))
      (localizedDensityMoment_nonnegative freq u 72)) (by decide : 14 ≤ 30)
  have h4 := div_pow_le_div_fourteenth hT1
    (mul_nonneg (by positivity : 0 ≤ 8*Real.pi^2*rho^2)
      (localizedDensityMoment_nonnegative freq u 72)) (by decide : 14 ≤ 68)
  have hs := add_le_add (add_le_add (add_le_add (le_refl (72*Real.pi^2*rho^2/T^14)) h2) (hBterm.trans h3)) h4
  simpa only [slabResidualSeventySecondBound, add_div] using hs

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Nuclei_SlabBoxResidual
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Residual estimates for the exact half-cell boundaries of the centered
nuclear grid. The dimensions may vary over a factor-two interval. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

theorem slabUniformBound_box {rho T H S : ℝ} (hrho : 0 ≤ rho) (hT : 1 ≤ T)
    (hH0 : 0 ≤ H) (hS0 : 0 ≤ S) (hH : H ≤ 2*T^10) (hS : S ≤ 2*T) :
    slabUniformBound rho H S ≤ 8*slabUniformBound rho (T^10) T := by
  rw [slabUniformBound,slabUniformBound,slabDomain_volume hH0 hS0,
    slabDomain_volume (by positivity) (by linarith)]
  have hm : 0 ≤ rho*NeutralAtom.kernelBallMass 1 :=
    mul_nonneg hrho (NeutralAtom.kernelBallMass_nonneg 1)
  have hv : 8*H^2*S*rho ≤ 8*(2*T^10)^2*(2*T)*rho := by gcongr
  nlinarith only [hm,hv]

private theorem squared_eight {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h : a ≤ 8*b) : a^2 ≤ 64*b^2 := by
  have hs := (sq_le_sq₀ ha (by positivity : 0 ≤ 8*b)).mpr h
  nlinarith only [hs]

theorem slabSeventySecondTail_box_bound {rho T H S freq : ℝ}
    (hrho : 0 ≤ rho) (hT : 2 ≤ T)
    (hHlo : T^10 ≤ H) (hHhi : H ≤ 2*T^10)
    (hSlo : T ≤ S) (hShi : S ≤ 2*T) (u : PlanarPosition) :
    2*(6*Real.pi*rho*S^3/H)^2+
      2*(64*rho*S/H)^2*localizedDensityMoment freq u 4+
      2*(2*slabUniformBound rho H S)^2*(localizedDensityMoment freq u 72/T^72)+
      2*(2*Real.pi*rho)^2*(localizedDensityMoment freq u 72/T^68) ≤
      64*slabResidualSeventySecondBound rho freq u/T^14 := by
  have hT0 : 0 < T := by linarith
  have hH0 : 0 < H := (pow_pos hT0 10).trans_le hHlo
  have hS0 : 0 ≤ S := hT0.le.trans hSlo
  have hr1 : 6*Real.pi*rho*S^3/H ≤ 8*(6*Real.pi*rho*T^3/T^10) := by
    calc
      _ ≤ 6*Real.pi*rho*(2*T)^3/T^10 := by gcongr
      _ = _ := by ring
  have hr2 : 64*rho*S/H ≤ 8*(64*rho*T/T^10) := by
    calc
      _ ≤ 64*rho*(2*T)/T^10 := by gcongr
      _ = 2*(64*rho*T/T^10) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
  have hb0 : 0 ≤ slabUniformBound rho H S :=
    (abs_nonneg _).trans (slabPotential_abs_bound hrho hH0.le hS0 (0 : Position))
  have hb1 : 0 ≤ slabUniformBound rho (T^10) T :=
    (abs_nonneg _).trans (slabPotential_abs_bound hrho (by positivity) hT0.le (0 : Position))
  have h1 := squared_eight (by positivity) (by positivity) hr1
  have h2 := squared_eight (by positivity) (by positivity) hr2
  have h3 := squared_eight hb0 hb1
    (slabUniformBound_box hrho (by linarith) hH0.le hS0 hHhi hShi)
  have hm4 := localizedDensityMoment_nonnegative freq u 4
  have hm72 := localizedDensityMoment_nonnegative freq u 72
  have h2' := mul_le_mul_of_nonneg_right h2 hm4
  have h3' := mul_le_mul_of_nonneg_right h3
    (show 0 ≤ localizedDensityMoment freq u 72/T^72 by positivity)
  have h4 : 0 ≤ 2*(2*Real.pi*rho)^2*(localizedDensityMoment freq u 72/T^68) := by positivity
  calc
    _ ≤ 64*(2*(6*Real.pi*rho*T^3/T^10)^2+
        2*(64*rho*T/T^10)^2*localizedDensityMoment freq u 4+
        2*(2*slabUniformBound rho (T^10) T)^2*(localizedDensityMoment freq u 72/T^72)+
        2*(2*Real.pi*rho)^2*(localizedDensityMoment freq u 72/T^68)) := by
      nlinarith only [h1,h2',h3',h4]
    _ ≤ 64*(slabResidualSeventySecondBound rho freq u/T^14) :=
      mul_le_mul_of_nonneg_left (slabSeventySecondTail_tenthPower_bound hrho hT u) (by norm_num)
    _ = _ := by ring

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Nuclei_SlabPolynomialResidual
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform polynomial dependence of the finite-slab residual on the
actual well centers. All constants are chosen before the geometry. -/

noncomputable section
open scoped BigOperators
namespace ContinuumCoulomb

private theorem moment_translate_budget {M t L a : ℝ} {k j : ℕ}
    (hM : 0 ≤ M) (ht : 0 ≤ t) (hL : 1 ≤ L) (htL : t ≤ L)
    (ha : 0 ≤ a) (hkj : k ≤ j) :
    a*(M+t^k) ≤ a*(M+1)*L^j := by
  have hLj : 1 ≤ L^j := one_le_pow₀ hL
  have htj := (pow_le_pow_left₀ ht htL k).trans (pow_le_pow_right₀ hL hkj)
  calc
    _ ≤ a*(M*L^j+L^j) := mul_le_mul_of_nonneg_left
      (add_le_add (le_mul_of_one_le_right hM hLj) htj) ha
    _ = _ := by ring

theorem localized_slab_moments_polynomial {freq : ℝ} (hf : 0 < freq) (rho : ℝ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (L : ℝ), 1 ≤ L → ∀ u : PlanarPosition, ‖u‖ ≤ L →
      slabResidualSeventySecondBound rho freq u ≤ C*L^72 ∧
      localizedDensityMoment freq u 8 ≤ C*L^8 := by
  let M4 := localizedDensityMoment freq 0 4
  let M8 := localizedDensityMoment freq 0 8
  let M72 := localizedDensityMoment freq 0 72
  have h4 : 0 ≤ M4 := localizedDensityMoment_nonnegative _ _ _
  have h8 : 0 ≤ M8 := localizedDensityMoment_nonnegative _ _ _
  have h72 : 0 ≤ M72 := localizedDensityMoment_nonnegative _ _ _
  let B4 := 8*(M4+1)
  let B8 := 128*(M8+1)
  let B72 := (2:ℝ)^71*(M72+1)
  let C0 := 72*Real.pi^2*rho^2+8192*rho^2*B4+
    8*(slabGrowthConstant rho)^2*B72+8*Real.pi^2*rho^2*B72
  have hb4 : 0 ≤ B4 := by dsimp [B4]; positivity
  have hb8 : 0 ≤ B8 := by dsimp [B8]; positivity
  have hb72 : 0 ≤ B72 := by dsimp [B72]; positivity
  have hc0 : 0 ≤ C0 := by dsimp [C0]; positivity
  refine ⟨1+C0+B8,by linarith,fun L hL u hu => ?_⟩
  have hmu4 : localizedDensityMoment freq u 4 ≤ B4*L^72 :=
    (localizedDensity_fourth_moment_translate hf u).2.trans
      (moment_translate_budget h4 (norm_nonneg _) hL hu (by norm_num) (by decide : 4 ≤ 72))
  have hmu8 : localizedDensityMoment freq u 8 ≤ B8*L^8 :=
    (localizedDensity_eighth_moment_translate hf u).2.trans
      (moment_translate_budget h8 (norm_nonneg _) hL hu (by norm_num) (by decide : 8 ≤ 8))
  have hmu72 : localizedDensityMoment freq u 72 ≤ B72*L^72 :=
    (localizedDensity_seventySecond_moment_translate hf u).2.trans
      (moment_translate_budget h72 (norm_nonneg _) hL hu (by positivity) (by decide : 72 ≤ 72))
  constructor
  · have hc : 72*Real.pi^2*rho^2 ≤ 72*Real.pi^2*rho^2*L^72 :=
      le_mul_of_one_le_right (by positivity) (one_le_pow₀ hL)
    have hsum := add_le_add (add_le_add (add_le_add hc
      (mul_le_mul_of_nonneg_left hmu4 (by positivity : 0 ≤ 8192*rho^2)))
      (mul_le_mul_of_nonneg_left hmu72 (by positivity : 0 ≤ 8*(slabGrowthConstant rho)^2)))
      (mul_le_mul_of_nonneg_left hmu72 (by positivity : 0 ≤ 8*Real.pi^2*rho^2))
    calc
      slabResidualSeventySecondBound rho freq u ≤ C0*L^72 := by
        dsimp only [slabResidualSeventySecondBound,C0]
        nlinarith only [hsum]
      _ ≤ (1+C0+B8)*L^72 := mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  · exact hmu8.trans (mul_le_mul_of_nonneg_right (by linarith) (by positivity))

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_ManyBody_FiniteBoxScale
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The retained counterterm has only a vertical truncation error. The
seventy-second slab moment makes its matrix error small after amplification. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

theorem finiteBoxSquaredError_box {rho R H S freq δ : ℝ}
    (hrho : 0 ≤ rho) (hR : 2 ≤ R)
    (hHlo : R^50 ≤ H) (hHhi : H ≤ 2*R^50)
    (hSlo : R^5 ≤ S) (hShi : S ≤ 2*R^5)
    (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) {m : ℕ}
    (u : Fin m → PlanarPosition) (j : Fin m) :
    finiteBoxOrbitalSquaredError rho H S freq δ (R^5) u j ≤
      128*slabResidualSeventySecondBound rho freq (u j)/R^70+
        2^27*(m:ℝ)^2*PlanarSobolev.wellBound^2*
          (∫ x, ‖x‖^24*continuumLocalizedMode freq 0 x^2)/R^120 := by
  have hR0 : 0 < R := by linarith
  have hW := PlanarSobolev.wellBound_nonnegative
  have hT : 2 ≤ R^5 := hR.trans (le_self_pow₀ (by linarith) (by decide : 5 ≠ 0))
  have htail := slabSeventySecondTail_box_bound (freq := freq) hrho hT
    (by simpa only [← pow_mul] using hHlo) (by simpa only [← pow_mul] using hHhi)
    hSlo hShi (u j)
  have hM : 0 ≤ ∫ x : Position, ‖x‖^24*continuumLocalizedMode freq 0 x^2 :=
    integral_nonneg (fun x => mul_nonneg (by positivity) (sq_nonneg _))
  have hw : ((m:ℝ)*(δ+1)*PlanarSobolev.wellBound)^2/(S/2)^24*
      (∫ x, ‖x‖^24*continuumLocalizedMode freq 0 x^2) ≤
      2^26*(m:ℝ)^2*PlanarSobolev.wellBound^2*
        (∫ x, ‖x‖^24*continuumLocalizedMode freq 0 x^2)/R^120 := by
    calc
      _ ≤ ((m:ℝ)*2*PlanarSobolev.wellBound)^2/(R^5/2)^24*
          (∫ x, ‖x‖^24*continuumLocalizedMode freq 0 x^2) := by
        gcongr
        linarith
      _ = _ := by field_simp [ne_of_gt hR0]
  unfold finiteBoxOrbitalSquaredError
  rw [show (R^5)^14 = R^70 by rw [← pow_mul]] at htail
  have h := mul_le_mul_of_nonneg_left (add_le_add htail hw) (by norm_num : (0:ℝ) ≤ 2)
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  ring

theorem finiteBoxSquaredError_polynomial {freq rho : ℝ}
    (hf : 0 < freq) (hrho : 0 ≤ rho) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ R L H S δ : ℝ, 2 ≤ R → 1 ≤ L →
      R^50 ≤ H → H ≤ 2*R^50 → R^5 ≤ S → S ≤ 2*R^5 →
      0 ≤ δ → δ ≤ 1 → ∀ (m : ℕ) (u : Fin m → PlanarPosition),
      (∀ j, ‖u j‖ ≤ L) → ∀ j,
      finiteBoxOrbitalSquaredError rho H S freq δ (R^5) u j ≤
        C*(L^72/R^70+(m:ℝ)^2/R^120) := by
  obtain ⟨A,hA,hbound⟩ := localized_slab_moments_polynomial hf rho
  let B := (2:ℝ)^27*PlanarSobolev.wellBound^2*
    (∫ x : Position, ‖x‖^24*continuumLocalizedMode freq 0 x^2)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  let C := 1+128*A+B
  have hC : 1 ≤ C := by dsimp [C]; nlinarith
  refine ⟨C,hC,fun R L H S δ hR hL hHlo hHhi hSlo hShi hδ hδ1 m u hu j => ?_⟩
  apply (finiteBoxSquaredError_box hrho hR hHlo hHhi hSlo hShi hδ hδ1 u j).trans
  have hs := mul_le_mul_of_nonneg_left (hbound L hL (u j) (hu j)).1 (by norm_num : (0:ℝ) ≤ 128)
  have hs' := div_le_div_of_nonneg_right hs (show 0 ≤ R^70 by positivity)
  have hca : 128*A ≤ C := by dsimp [C]; linarith
  have hcb : B ≤ C := by dsimp [C]; nlinarith
  have h1 := mul_le_mul_of_nonneg_right hca (show 0 ≤ L^72/R^70 by positivity)
  have h2 := mul_le_mul_of_nonneg_right hcb (show 0 ≤ (m:ℝ)^2/R^120 by positivity)
  calc
    _ ≤ 128*(A*L^72)/R^70+
        2^27*(m:ℝ)^2*PlanarSobolev.wellBound^2*
          (∫ x, ‖x‖^24*continuumLocalizedMode freq 0 x^2)/R^120 := add_le_add hs' le_rfl
    _ = 128*A*(L^72/R^70)+B*((m:ℝ)^2/R^120) := by dsimp [B]; ring
    _ ≤ C*(L^72/R^70)+C*((m:ℝ)^2/R^120) := add_le_add h1 h2
    _ = _ := by ring

theorem exists_finiteBoxResidual_parameter_offset {freq rho : ℝ}
    (hf : 0 < freq) (hrho : 0 ≤ rho) :
    ∃ k₀ : ℕ, 1 ≤ k₀ ∧ ∀ r s k : ℕ, k₀+2*r+72*s ≤ k →
      ∀ N H S δ : ℝ, 2 ≤ N →
      (N^k)^50 ≤ H → H ≤ 2*(N^k)^50 →
      (N^k)^5 ≤ S → S ≤ 2*(N^k)^5 → 0 ≤ δ → δ ≤ 1 →
      ∀ (m : ℕ) (u : Fin m → PlanarPosition), (m:ℝ) ≤ N^r →
      (∀ j, ‖u j‖ ≤ N^s) → ∀ j,
      finiteBoxOrbitalSquaredError rho H S freq δ ((N^k)^5) u j ≤
        ((N^k)^32)⁻¹^2 := by
  obtain ⟨C,hC,hbound⟩ := finiteBoxSquaredError_polynomial hf hrho
  obtain ⟨q,hq,hconst⟩ := exists_polynomial_constant_bounds (by norm_num : (0:ℝ)<1) (2*C)
  refine ⟨q+1,by omega,fun r s k hk N H S δ hN hHlo hHhi hSlo hShi hδ hδ1 m u hm hu j => ?_⟩
  have hN0 : 0 < N := by linarith
  have hN1 : 1 ≤ N := by linarith
  have hR : 2 ≤ N^k := hN.trans (le_self_pow₀ hN1 (by omega))
  apply (hbound (N^k) (N^s) H S δ hR (one_le_pow₀ hN1)
    hHlo hHhi hSlo hShi hδ hδ1 m u hu j).trans
  have hR1 : 1 ≤ N^k := one_le_pow₀ hN1
  have hpow : (N^k)^70 ≤ (N^k)^120 := pow_le_pow_right₀ hR1 (by decide)
  have hm2 : (m:ℝ)^2 ≤ N^(2*r+72*s) := calc
    _ ≤ (N^r)^2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hm 2
    _ ≤ N^(2*r+72*s) := by
      rw [← pow_mul]
      exact pow_le_pow_right₀ hN1 (by omega)
  have hL : (N^s)^72 ≤ N^(2*r+72*s) := by
    rw [← pow_mul]
    exact pow_le_pow_right₀ hN1 (by omega)
  calc
    C*((N^s)^72/(N^k)^70+(m:ℝ)^2/(N^k)^120) ≤
        C*(N^(2*r+72*s)/(N^k)^70+N^(2*r+72*s)/(N^k)^70) := by gcongr
    _ = 2*C*N^(2*r+72*s)/(N^k)^70 := by ring
    _ ≤ N^q*N^(2*r+72*s)/(N^k)^70 := by
      gcongr
      exact (hconst N hN).2
    _ ≤ 1/(N^k)^64 := by
      rw [div_le_div_iff₀ (by positivity : 0 < (N^k)^70) (by positivity : 0 < (N^k)^64),
        one_mul,← pow_add,← pow_mul,← pow_add,← pow_mul]
      exact pow_le_pow_right₀ hN1 (by omega)
    _ = _ := by simp only [one_div,inv_pow,← pow_mul,Nat.mul_assoc]

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_ManyBody_FiniteCoefficientCorrection
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Entrywise perturbation bounds needed when applying the actual symmetric
Gram correction to the two- and four-index orbital coefficients. Polynomial
site-count losses suffice for the logarithmic spacing used here. -/

noncomputable section
open scoped BigOperators
namespace ContinuumCoulomb

theorem product_two_perturb {a b c d eta : ℝ}
    (hb : |b| ≤ 2) (hc : |c| ≤ 2)
    (he : 0 ≤ eta) (hac : |a - c| ≤ eta) (hbd : |b - d| ≤ eta) :
    |a * b - c * d| ≤ 4 * eta := by
  have hid : a * b - c * d = (a - c) * b + c * (b - d) := by ring
  rw [hid]
  calc
    _ ≤ |a - c| * |b| + |c| * |b - d| := by simpa only [abs_mul] using abs_add_le ((a-c)*b) (c*(b-d))
    _ ≤ eta * 2 + 2 * eta := add_le_add
      (mul_le_mul hac hb (abs_nonneg _) he)
      (mul_le_mul hc hbd (abs_nonneg _) (by norm_num))
    _ = _ := by ring

theorem finiteTwoIndexChange_identity {m : ℕ}
    (F : Fin m → Fin m → ℝ) (i j : Fin m) :
    finiteTwoIndexChange (fun a b => if a=b then 1 else 0) F i j = F i j := by
  classical
  simp only [finiteTwoIndexChange, ite_mul, mul_ite, one_mul, zero_mul, mul_zero,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true, if_true]

theorem finiteTwoIndexChange_bound {m : ℕ} (A : Fin m → Fin m → ℝ)
    (F : Fin m → Fin m → ℝ) {eta B : ℝ}
    (he : 0 ≤ eta) (_hB : 0 ≤ B) (hA : ∀ i j, |A i j| ≤ 2)
    (hnear : ∀ i j, |A i j - if i=j then 1 else 0| ≤ eta)
    (hF : ∀ i j, |F i j| ≤ B) (i j : Fin m) :
    |finiteTwoIndexChange A F i j - F i j| ≤ (m : ℝ)^2 * (4*eta*B) := by
  classical
  let I : Fin m → Fin m → ℝ := fun a b => if a=b then 1 else 0
  have hI (a b : Fin m) : |I a b| ≤ 2 := by dsimp [I]; split_ifs <;> norm_num
  have hc (p q : Fin m) : |(A i p*A j q-I i p*I j q)*F p q| ≤ 4*eta*B := by
    rw [abs_mul]
    exact mul_le_mul (product_two_perturb (hA j q) (hI i p) he (hnear i p) (hnear j q))
      (hF p q) (abs_nonneg _) (by positivity)
  rw [← finiteTwoIndexChange_identity F i j]
  change |finiteTwoIndexChange A F i j - finiteTwoIndexChange I F i j| ≤ _
  unfold finiteTwoIndexChange
  simp only [← Finset.sum_sub_distrib, ← sub_mul]
  calc
    _ ≤ ∑ p, ∑ q, |(A i p*A j q-I i p*I j q)*F p q| := by
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      exact Finset.sum_le_sum (fun p _ => Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ _p : Fin m, ∑ _q : Fin m, 4*eta*B :=
      Finset.sum_le_sum (fun p _ => Finset.sum_le_sum (fun q _ => hc p q))
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_ManyBody_GramCorrection
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Quantitative symmetric orthonormalization of a finite real Gram matrix.
The correction is the actual spectral inverse square root, with Euclidean
operator norm estimates independent of the ambient function space. -/

noncomputable section
open Matrix
open scoped BigOperators Matrix.Norms.L2Operator
namespace ContinuumCoulomb.GramCorrection

lemma inverseSqrt_bounds {a x : ℝ} (_ha : 0 ≤ a) (has : a ≤ 1 / 2)
    (hx : 1 - a ≤ x ∧ x ≤ 1 + a) :
    (Real.sqrt x)⁻¹ ≤ 2 ∧ |(Real.sqrt x)⁻¹ - 1| ≤ 2 * a := by
  have hxp : 0 < x := by linarith
  have hs : 0 < Real.sqrt x := Real.sqrt_pos.mpr hxp
  have hsq := Real.sq_sqrt hxp.le
  have hslo : (1 / 2 : ℝ) ≤ Real.sqrt x := by
    nlinarith [Real.sqrt_nonneg x]
  have hinv : (Real.sqrt x)⁻¹ ≤ 2 := by
    rw [← one_div]
    apply (div_le_iff₀ hs).mpr
    linarith
  refine ⟨hinv, ?_⟩
  have hid : ((Real.sqrt x)⁻¹ - 1) *
      (Real.sqrt x * (Real.sqrt x + 1)) = 1 - x := by
    calc
      _ = ((Real.sqrt x)⁻¹ * Real.sqrt x - Real.sqrt x) * (Real.sqrt x + 1) := by ring
      _ = (1 - Real.sqrt x) * (Real.sqrt x + 1) := by rw [inv_mul_cancel₀ hs.ne']
      _ = 1 - x := by nlinarith
  have hden : (1 / 2 : ℝ) ≤ Real.sqrt x * (Real.sqrt x + 1) := by
    nlinarith
  have habs : |1 - x| ≤ a := by rw [abs_le]; constructor <;> linarith [hx.1, hx.2]
  have hm : |(Real.sqrt x)⁻¹ - 1| * (Real.sqrt x * (Real.sqrt x + 1)) ≤ a := by
    rw [← abs_of_nonneg (by positivity : 0 ≤ Real.sqrt x * (Real.sqrt x + 1)), ← abs_mul, hid]
    exact habs
  nlinarith [mul_nonneg (abs_nonneg ((Real.sqrt x)⁻¹ - 1)) (sub_nonneg.mpr hden)]

variable {m : ℕ} {G : Matrix (Fin m) (Fin m) ℝ}

lemma eigenvalue_bounds (hG : G.IsHermitian) {delta : ℝ} (hdelta : 0 ≤ delta)
    (hdiag : ∀ i, G i i = 1) (hoff : ∀ i j, i ≠ j → |G i j| ≤ delta) (i : Fin m) :
    1 - m * delta ≤ hG.eigenvalues i ∧ hG.eigenvalues i ≤ 1 + m * delta := by
  let v : Fin m → ℝ := hG.eigenvectorBasis i
  have hnorm : ∑ j, v j ^ 2 = 1 := by
    have h := congrArg (fun t : ℝ => t ^ 2) (hG.eigenvectorBasis.orthonormal.1 i)
    simpa only [EuclideanSpace.norm_sq_eq, Real.norm_eq_abs, sq_abs, one_pow] using h
  have hval : hG.eigenvalues i = ∑ j, ∑ k, G j k * v j * v k := by
    rw [hG.eigenvalues_eq]
    simp only [RCLike.re_to_real, star_trivial, dotProduct, mulVec, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    dsimp [v]
    ring
  rw [hval]
  have hlo := dualMatrix_quadratic_lower G hdelta (fun j => (hdiag j).ge) hoff v
  have hhi := dualMatrix_quadratic_upper G hdelta (fun j => (hdiag j).le) hoff v
  rw [hnorm, mul_one] at hlo hhi
  exact ⟨hlo, hhi⟩

lemma correction_norm_bounds (hG : G.IsHermitian) {delta : ℝ} (hdelta : 0 ≤ delta)
    (hdiag : ∀ i, G i i = 1) (hoff : ∀ i j, i ≠ j → |G i j| ≤ delta)
    (hsmall : m * delta ≤ 1 / 2) :
    ‖correction hG‖ ≤ 2 ∧ ‖correction hG - 1‖ ≤ 2 * m * delta := by
  have ha : 0 ≤ (m : ℝ) * delta := mul_nonneg (Nat.cast_nonneg _) hdelta
  have hb (i : Fin m) := inverseSqrt_bounds ha hsmall (eigenvalue_bounds hG hdelta hdiag hoff i)
  have hnorm : ‖correction hG‖ ≤ 2 := by
    rw [correction, ← hG.cfc_eq]
    apply norm_cfc_le (by norm_num : (0 : ℝ) ≤ 2)
    intro x hx
    rw [hG.spectrum_real_eq_range_eigenvalues] at hx
    obtain ⟨i, rfl⟩ := hx
    rw [Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _))]
    exact (hb i).1
  refine ⟨hnorm, ?_⟩
  have hc : ContinuousOn (fun x : ℝ => (Real.sqrt x)⁻¹) (spectrum ℝ G) :=
    G.finite_real_spectrum.continuousOn _
  rw [correction, ← hG.cfc_eq, ← cfc_const_one ℝ G, ← cfc_sub _ _ G hc continuousOn_const]
  apply norm_cfc_le (by positivity : (0 : ℝ) ≤ 2 * m * delta)
  intro x hx
  rw [hG.spectrum_real_eq_range_eigenvalues] at hx
  obtain ⟨i, rfl⟩ := hx
  simpa only [Real.norm_eq_abs, mul_assoc] using (hb i).2

lemma entry_abs_le_norm (B : Matrix (Fin m) (Fin m) ℝ) (i j : Fin m) : |B i j| ≤ ‖B‖ := by
  let v : EuclideanSpace ℝ (Fin m) := PiLp.single 2 j 1
  let y : EuclideanSpace ℝ (Fin m) := Matrix.toEuclideanCLM (n := Fin m) (𝕜 := ℝ) B v
  have hy : y i = B i j := by
    change (B *ᵥ Pi.single j (1 : ℝ)) i = B i j
    rw [Matrix.mulVec_single_one]
    rfl
  calc
    |B i j| = ‖y i‖ := by rw [hy, Real.norm_eq_abs]
    _ ≤ ‖y‖ := PiLp.norm_apply_le y i
    _ ≤ ‖Matrix.toEuclideanCLM (n := Fin m) (𝕜 := ℝ) B‖ * ‖v‖ := (Matrix.toEuclideanCLM (n := Fin m) (𝕜 := ℝ) B).le_opNorm v
    _ = ‖B‖ := by rw [Matrix.l2_opNorm_toEuclideanCLM]; simp only [v, PiLp.norm_single, norm_one, mul_one]

lemma correction_entry_bounds (hG : G.IsHermitian) {delta : ℝ} (hdelta : 0 ≤ delta)
    (hdiag : ∀ i, G i i = 1) (hoff : ∀ i j, i ≠ j → |G i j| ≤ delta)
    (hsmall : m * delta ≤ 1 / 2) (i j : Fin m) :
    |correction hG i j - if i = j then 1 else 0| ≤ 2 * m * delta ∧
      |correction hG i j| ≤ 2 := by
  have hb := correction_norm_bounds hG hdelta hdiag hoff hsmall
  constructor
  · simpa only [Matrix.sub_apply, Matrix.one_apply] using
      (entry_abs_le_norm (correction hG - 1) i j).trans hb.2
  · exact (entry_abs_le_norm (correction hG) i j).trans hb.1

end ContinuumCoulomb.GramCorrection

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_ManyBody_OrthonormalLocalizedModes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual spectral inverse-square-root correction applied to the
manufactured orbitals. These are C1 decaying orthonormal spatial functions;
injectively occupied spatial/spin modes give actual normalized fermions. -/

noncomputable section
open MeasureTheory Matrix
open scoped BigOperators Matrix.Norms.L2Operator
namespace ContinuumCoulomb

theorem correctedLocalizedCoefficients_entries {D : ℝ} {m : ℕ} (u : Fin m → PlanarPosition)
    (hsep : ∀ i j, i ≠ j → D ≤ ‖u i-u j‖) (hs : m * localizedOverlapBound D ≤ 1/2) (i j : Fin m) :
    |correctedLocalizedCoefficients u i j - if i=j then 1 else 0| ≤ 2*m*localizedOverlapBound D ∧
      |correctedLocalizedCoefficients u i j| ≤ 2 :=
  GramCorrection.correction_entry_bounds (localizedModeGram_isHermitian u)
    (localizedOverlapBound_nonnegative D) (fun j => planarModeOverlap_diagonal (u j))
    (planarModeOverlap_offsite u hsep) hs i j

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_CorrectedNuclearError
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite basis correction of the actual nuclear error form. Only
polynomially many orbital matrix entries are summed. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

theorem localizedLinearOrbital_weighted_integrable (freq : ℝ) {m : ℕ}
    (u : Fin m → PlanarPosition) (F : Position → ℝ)
    (hI : ∀ i j, Integrable (fun x => F x*continuumLocalizedMode freq (u i) x*
      continuumLocalizedMode freq (u j) x)) (a b : Fin m → ℝ) :
    Integrable (fun x => F x*localizedLinearOrbital freq u a x*localizedLinearOrbital freq u b x) := by
  have hi (i j : Fin m) : Integrable (fun x => (a i*b j)*
      (F x*continuumLocalizedMode freq (u i) x*continuumLocalizedMode freq (u j) x)) :=
    (hI i j).const_mul _
  have he (x : Position) : F x*localizedLinearOrbital freq u a x*localizedLinearOrbital freq u b x =
      ∑ i, ∑ j, (a i*b j)*(F x*continuumLocalizedMode freq (u i) x*continuumLocalizedMode freq (u j) x) := by
    simp only [localizedLinearOrbital,Finset.mul_sum,Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  simp_rw [he]
  exact integrable_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hi i j))

theorem localizedLinearOrbital_weighted_pairing (freq : ℝ) {m : ℕ}
    (u : Fin m → PlanarPosition) (F : Position → ℝ)
    (hI : ∀ i j, Integrable (fun x => F x*continuumLocalizedMode freq (u i) x*
      continuumLocalizedMode freq (u j) x)) (a b : Fin m → ℝ) :
    (∫ x, F x*localizedLinearOrbital freq u a x*localizedLinearOrbital freq u b x) =
      ∑ i, ∑ j, (a i*b j)*(∫ x, F x*continuumLocalizedMode freq (u i) x*
        continuumLocalizedMode freq (u j) x) := by
  have hi (i j : Fin m) : Integrable (fun x => (a i*b j)*
      (F x*continuumLocalizedMode freq (u i) x*continuumLocalizedMode freq (u j) x)) :=
    (hI i j).const_mul _
  have he (x : Position) : F x*localizedLinearOrbital freq u a x*localizedLinearOrbital freq u b x =
      ∑ i, ∑ j, (a i*b j)*(F x*continuumLocalizedMode freq (u i) x*continuumLocalizedMode freq (u j) x) := by
    simp only [localizedLinearOrbital,Finset.mul_sum,Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  simp_rw [he]
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hi i j))]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finsetSum _ (fun j _ => hi i j)]
  simp only [integral_const_mul]

theorem correctedLocalizedMode_nuclear_error {freq D ε : ℝ} {m : ℕ}
    (u : Fin m → PlanarPosition) (hsep : ∀ i j, i ≠ j → D ≤ ‖u i-u j‖)
    (hs : m*localizedOverlapBound D ≤ 1/2) (F : Position → ℝ)
    (hI : ∀ i j, Integrable (fun x => F x*continuumLocalizedMode freq (u i) x*
      continuumLocalizedMode freq (u j) x))
    (herror : ∀ i j, |∫ x, F x*continuumLocalizedMode freq (u i) x*
      continuumLocalizedMode freq (u j) x| ≤ ε) (i j : Fin m) :
    Integrable (fun x => F x*correctedLocalizedMode freq u i x*correctedLocalizedMode freq u j x) ∧
      |∫ x, F x*correctedLocalizedMode freq u i x*correctedLocalizedMode freq u j x| ≤
        4*(m:ℝ)^2*ε := by
  refine ⟨localizedLinearOrbital_weighted_integrable freq u F hI _ _,?_⟩
  rw [correctedLocalizedMode,correctedLocalizedMode,localizedLinearOrbital_weighted_pairing freq u F hI]
  have hb (p q : Fin m) : |(correctedLocalizedCoefficients u i p*correctedLocalizedCoefficients u j q)*
      (∫ x, F x*continuumLocalizedMode freq (u p) x*continuumLocalizedMode freq (u q) x)| ≤ 4*ε := by
    rw [abs_mul,abs_mul]
    have hc := mul_le_mul (correctedLocalizedCoefficients_entries u hsep hs i p).2
      (correctedLocalizedCoefficients_entries u hsep hs j q).2 (abs_nonneg _) (by norm_num)
    have he := mul_le_mul hc (herror p q) (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 2*2)
    simpa only [show (2:ℝ)*2=4 by norm_num] using he
  calc
    _ ≤ ∑ p : Fin m, ∑ q : Fin m, |(correctedLocalizedCoefficients u i p*correctedLocalizedCoefficients u j q)*
        (∫ x, F x*continuumLocalizedMode freq (u p) x*continuumLocalizedMode freq (u q) x)| := by
      exact (Finset.abs_sum_le_sum_abs _ _).trans
        (Finset.sum_le_sum (fun p _ => Finset.abs_sum_le_sum_abs _ _))
    _ ≤ ∑ _p : Fin m, ∑ _q : Fin m, 4*ε :=
      Finset.sum_le_sum (fun p _ => Finset.sum_le_sum (fun q _ => hb p q))
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]; ring

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_LocalizedCorrectedMatrixError
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Quantitative comparison of the actual shifted and scaled one-body
matrix with the hopping and Coulomb occupancy counterterm matrix. -/

noncomputable section
open scoped BigOperators
namespace ContinuumCoulomb

theorem localizedCorrectedOneBodyMatrix_error {freq scale D : ℝ} (hfreq : 0 < freq)
    (hscale : scale ≠ 0) {m : ℕ} (u : Fin m → PlanarPosition)
    (hsep : ∀ i j, i ≠ j → D ≤ ‖u i-u j‖) (i j : Fin m) :
    |scale * localizedCorrectedOneBodyMatrix freq scale u i j - localizedOneBodyTarget scale freq u i j| ≤
      (|scale| * m * planarWellMatrixConstant +
        (m : ℝ)^2 * localizedCountertermBound freq * planarWellMatrixConstant) *
          Real.exp (-(19/10 : ℝ)*D) +
        (m : ℝ)^2 * localizedCountertermBound freq *
          (PlanarSobolev.wellBound * planarOverlapConstant) * Real.exp (-(9/10 : ℝ)*D) := by
  classical
  let e₁ := |scale| * m * planarWellMatrixConstant * Real.exp (-(19/10 : ℝ)*D)
  let e₂ := (m : ℝ)^2 * localizedCountertermBound freq * planarWellMatrixConstant *
    Real.exp (-(19/10 : ℝ)*D)
  let e₃ := (m : ℝ)^2 * localizedCountertermBound freq *
    (PlanarSobolev.wellBound * planarOverlapConstant) * Real.exp (-(9/10 : ℝ)*D)
  have he₂ : 0 ≤ e₂ := by
    dsimp [e₂]
    exact mul_nonneg (mul_nonneg (mul_nonneg (sq_nonneg _) (localizedCountertermBound_nonnegative freq))
      planarWellMatrixConstant_nonnegative) (Real.exp_pos _).le
  have he₃ : 0 ≤ e₃ := by
    dsimp [e₃]
    exact mul_nonneg (mul_nonneg (mul_nonneg (sq_nonneg _) (localizedCountertermBound_nonnegative freq))
      (mul_nonneg PlanarSobolev.wellBound_nonnegative planarOverlapConstant_nonnegative)) (Real.exp_pos _).le
  have hb : |scale * (localizedOneBodyMatrix freq u i j - planarHoppingMatrix u i j)| ≤ e₁ := by
    rw [abs_mul, localizedOneBodyMatrix_eq hfreq]
    exact (mul_le_mul_of_nonneg_left (planarMultiwellMatrix_error_bound u hsep i j) (abs_nonneg scale)).trans_eq
      (by dsimp [e₁]; ring)
  have hc : |localizedCountertermMatrix freq u i j +
      (if i=j then localizedOffsiteSum freq u i else 0)| ≤ e₂+e₃ := by
    by_cases hij : i=j
    · subst j
      simp only [ite_true, if_true]
      exact (localizedCountertermMatrix_diagonal_error_bound hfreq u hsep i).trans (le_add_of_nonneg_right he₃)
    · simp only [hij, ite_false, if_false, add_zero]
      have h := localizedCountertermMatrix_offdiagonal_bound hfreq u i j
      have h' : |localizedCountertermMatrix freq u i j| ≤ e₃ := h.trans (mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr (by linarith [hsep i j hij])) (by
          exact mul_nonneg (mul_nonneg (sq_nonneg _) (localizedCountertermBound_nonnegative freq))
            (mul_nonneg PlanarSobolev.wellBound_nonnegative planarOverlapConstant_nonnegative)))
      exact h'.trans (le_add_of_nonneg_left he₂)
  rw [localizedCorrectedOneBodyMatrix_scaled hfreq hscale]
  unfold localizedOneBodyTarget
  have hid : scale * localizedOneBodyMatrix freq u i j + localizedCountertermMatrix freq u i j -
      (scale * planarHoppingMatrix u i j - if i=j then localizedOffsiteSum freq u i else 0) =
      scale * (localizedOneBodyMatrix freq u i j - planarHoppingMatrix u i j) +
        (localizedCountertermMatrix freq u i j + if i=j then localizedOffsiteSum freq u i else 0) := by ring
  rw [hid]
  calc
    _ ≤ |scale*(localizedOneBodyMatrix freq u i j-planarHoppingMatrix u i j)| +
        |localizedCountertermMatrix freq u i j + if i=j then localizedOffsiteSum freq u i else 0| := abs_add_le _ _
    _ ≤ e₁+(e₂+e₃) := add_le_add hb hc
    _ = _ := by dsimp [e₁,e₂,e₃]; ring

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_ManyBody_FiniteOneBodyCorrection
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual corrected one-body matrix entries, including the singular nuclear
error. Finite change of basis preserves the quantitative entrywise estimates. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb

theorem finiteTwoIndexChange_error {m : ℕ} (A F T : Fin m → Fin m → ℝ)
    {ε : ℝ} (hA : ∀ i j, |A i j| ≤ 2)
    (herror : ∀ i j, |F i j-T i j| ≤ ε) (i j : Fin m) :
    |finiteTwoIndexChange A F i j-finiteTwoIndexChange A T i j| ≤ 4*(m:ℝ)^2*ε := by
  have hb (p q : Fin m) : |(A i p*A j q)*(F p q-T p q)| ≤ 4*ε := by
    rw [abs_mul,abs_mul]
    have hc := mul_le_mul (hA i p) (hA j q) (abs_nonneg _) (by norm_num)
    have he := mul_le_mul hc (herror p q) (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 2*2)
    simpa only [show (2:ℝ)*2=4 by norm_num] using he
  unfold finiteTwoIndexChange
  simp only [← Finset.sum_sub_distrib,← mul_sub]
  calc
    _ ≤ ∑ p, ∑ q, |(A i p*A j q)*(F p q-T p q)| :=
      (Finset.abs_sum_le_sum_abs _ _).trans
        (Finset.sum_le_sum (fun p _ => Finset.abs_sum_le_sum_abs _ _))
    _ ≤ ∑ _p : Fin m, ∑ _q : Fin m, 4*ε :=
      Finset.sum_le_sum (fun p _ => Finset.sum_le_sum (fun q _ => hb p q))
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]; ring

theorem integral_finite_bilinear {m : ℕ} (f r : Fin m → Position → ℝ)
    (hI : ∀ i j, Integrable (fun x => f i x*r j x)) (a b : Fin m → ℝ) :
    (∫ x, (∑ i, a i*f i x)*(∑ j, b j*r j x)) =
      ∑ i, ∑ j, (a i*b j)*(∫ x, f i x*r j x) := by
  have hi (i j : Fin m) : Integrable (fun x => (a i*b j)*(f i x*r j x)) :=
    (hI i j).const_mul _
  have he (x : Position) : (∑ i, a i*f i x)*(∑ j, b j*r j x) =
      ∑ i, ∑ j, (a i*b j)*(f i x*r j x) := by
    simp only [Finset.sum_mul,Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  simp_rw [he]
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hi i j))]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finsetSum _ (fun j _ => hi i j)]
  simp only [integral_const_mul]

theorem correctedManufacturedOneBodyMatrix_eq {rho H S freq : ℝ}
    (hrho : 0 ≤ rho) (hH : 0 ≤ H) (hS : 0 ≤ S) (hfreq : 0 < freq)
    (scale : ℝ) {m : ℕ} (u : Fin m → PlanarPosition) {δ : ℝ} (hδ : 0 ≤ δ)
    (hcoeff : ∀ i, 0 ≤ localizedCounterterm freq u i/scale ∧ localizedCounterterm freq u i/scale ≤ δ)
    (i j : Fin m) :
    correctedManufacturedOneBodyMatrix rho H S freq scale u i j =
      finiteTwoIndexChange (correctedLocalizedCoefficients u)
        (manufacturedRawOneBodyMatrix rho H S freq scale u) i j := by
  exact integral_finite_bilinear _ _ (fun p q =>
    (continuumLocalizedMode_memLp hfreq (u p)).integrable_mul
      (manufacturedOrbitalResidual_memLp hrho hH hS hfreq scale u hδ hcoeff q)) _ _

theorem correctedManufacturedOneBodyMatrix_error {rho H S freq D ε B : ℝ}
    (hrho : 0 ≤ rho) (hH : 0 < H) (hS : 0 < S) (hfreq : 0 < freq)
    (scale : ℝ) {m : ℕ} (u : Fin m → PlanarPosition) {δ : ℝ} (hδ : 0 ≤ δ)
    (hcoeff : ∀ i, 0 ≤ localizedCounterterm freq u i/scale ∧ localizedCounterterm freq u i/scale ≤ δ)
    (hsep : ∀ i j, i ≠ j → D ≤ ‖u i-u j‖) (hs : m*localizedOverlapBound D ≤ 1/2)
    (hε : 0 ≤ ε) (herror : ∀ j, (∫ x, finiteBoxOrbitalResidual rho H S freq scale u j x^2) ≤ ε^2)
    (hB : 0 ≤ B) (hbound : ∀ i j, |localizedCorrectedOneBodyMatrix freq scale u i j| ≤ B)
    (i j : Fin m) :
    |correctedManufacturedOneBodyMatrix rho H S freq scale u i j-
      localizedCorrectedOneBodyMatrix freq scale u i j| ≤
      4*(m:ℝ)^2*ε+(m:ℝ)^2*(4*(2*m*localizedOverlapBound D)*B) := by
  have ha := fun p q => (correctedLocalizedCoefficients_entries u hsep hs p q).2
  have hnear : 0 ≤ 2*(m:ℝ)*localizedOverlapBound D :=
    mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg m)) (localizedOverlapBound_nonnegative D)
  have he (p q : Fin m) : |manufacturedRawOneBodyMatrix rho H S freq scale u p q-
      localizedCorrectedOneBodyMatrix freq scale u p q| ≤ ε := by
    have hh := (manufacturedRawOneBodyMatrix_error_integral hrho hH.le hS hfreq scale u hδ hcoeff p q).trans (herror q)
    nlinarith [abs_nonneg (manufacturedRawOneBodyMatrix rho H S freq scale u p q-
      localizedCorrectedOneBodyMatrix freq scale u p q)]
  rw [correctedManufacturedOneBodyMatrix_eq hrho hH.le hS.le hfreq scale u hδ hcoeff]
  exact (abs_sub_le _ (finiteTwoIndexChange (correctedLocalizedCoefficients u)
    (localizedCorrectedOneBodyMatrix freq scale u) i j) _).trans (add_le_add
      (finiteTwoIndexChange_error _ _ _ ha he i j)
      (finiteTwoIndexChange_bound _ _ hnear hB ha
        (fun p q => (correctedLocalizedCoefficients_entries u hsep hs p q).1) hbound i j))

theorem correctedNuclearOneBodyMatrix_error {rho H S freq D ε ν B : ℝ}
    (hrho : 0 ≤ rho) (hH : 0 < H) (hS : 0 < S) (hfreq : 0 < freq)
    {scale : ℝ} (hscale : scale ≠ 0) {m : ℕ} (u : Fin m → PlanarPosition)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hcoeff : ∀ i, 0 ≤ localizedCounterterm freq u i/scale ∧ localizedCounterterm freq u i/scale ≤ δ)
    (hsep : ∀ i j, i ≠ j → D ≤ ‖u i-u j‖) (hs : m*localizedOverlapBound D ≤ 1/2)
    (hε : 0 ≤ ε) (herror : ∀ j, (∫ x, finiteBoxOrbitalResidual rho H S freq scale u j x^2) ≤ ε^2)
    (hB : 0 ≤ B) (hbound : ∀ i j, |localizedCorrectedOneBodyMatrix freq scale u i j| ≤ B)
    (F : Position → ℝ)
    (hI : ∀ i j, Integrable (fun x => F x*continuumLocalizedMode freq (u i) x*
      continuumLocalizedMode freq (u j) x))
    (hF : ∀ i j, |∫ x, F x*continuumLocalizedMode freq (u i) x*
      continuumLocalizedMode freq (u j) x| ≤ ν) (i j : Fin m) :
    |scale*correctedNuclearOneBodyMatrix rho H S freq scale u F i j-
      localizedOneBodyTarget scale freq u i j| ≤
      |scale| *(4*(m:ℝ)^2*ε+(m:ℝ)^2*(4*(2*m*localizedOverlapBound D)*B)+4*(m:ℝ)^2*ν)+
        (|scale| *m*planarWellMatrixConstant+
          (m:ℝ)^2*localizedCountertermBound freq*planarWellMatrixConstant)*Real.exp (-(19/10:ℝ)*D)+
        (m:ℝ)^2*localizedCountertermBound freq*
          (PlanarSobolev.wellBound*planarOverlapConstant)*Real.exp (-(9/10:ℝ)*D) := by
  have hm := correctedManufacturedOneBodyMatrix_error hrho hH hS hfreq
    scale u hδ hcoeff hsep hs hε herror hB hbound i j
  have hn := (correctedLocalizedMode_nuclear_error u hsep hs F hI hF i j).2
  have ht := localizedCorrectedOneBodyMatrix_error hfreq hscale u hsep i j
  have he : |correctedNuclearOneBodyMatrix rho H S freq scale u F i j-
      localizedCorrectedOneBodyMatrix freq scale u i j| ≤
      4*(m:ℝ)^2*ε+(m:ℝ)^2*(4*(2*m*localizedOverlapBound D)*B)+4*(m:ℝ)^2*ν := by
    unfold correctedNuclearOneBodyMatrix
    have hid : correctedManufacturedOneBodyMatrix rho H S freq scale u i j+
        (∫ x, F x*correctedLocalizedMode freq u i x*correctedLocalizedMode freq u j x)-
        localizedCorrectedOneBodyMatrix freq scale u i j =
        (correctedManufacturedOneBodyMatrix rho H S freq scale u i j-
          localizedCorrectedOneBodyMatrix freq scale u i j)+
          (∫ x, F x*correctedLocalizedMode freq u i x*correctedLocalizedMode freq u j x) := by ring
    rw [hid]
    exact (abs_add_le _ _).trans (add_le_add hm hn)
  calc
    _ ≤ |scale*(correctedNuclearOneBodyMatrix rho H S freq scale u F i j-
          localizedCorrectedOneBodyMatrix freq scale u i j)|+
          |scale*localizedCorrectedOneBodyMatrix freq scale u i j-localizedOneBodyTarget scale freq u i j| := by
      have hid : scale*correctedNuclearOneBodyMatrix rho H S freq scale u F i j-
          localizedOneBodyTarget scale freq u i j =
          scale*(correctedNuclearOneBodyMatrix rho H S freq scale u F i j-
            localizedCorrectedOneBodyMatrix freq scale u i j)+
            (scale*localizedCorrectedOneBodyMatrix freq scale u i j-localizedOneBodyTarget scale freq u i j) := by ring
      rw [hid]
      exact abs_add_le _ _
    _ ≤ _ := by
      rw [abs_mul]
      have hh := add_le_add (mul_le_mul_of_nonneg_left he (abs_nonneg scale)) ht
      convert hh using 1
      all_goals try with_reducible_and_instances rfl
      ring

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_LocalizedMatrixDecayBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The shifted one-body matrix is itself small. Retaining this decay is
necessary when estimating the Gram correction after physical amplification. -/

noncomputable section
open scoped BigOperators
namespace ContinuumCoulomb

theorem planarWellMatrix_uniform_bound (u v w : PlanarPosition) :
    |planarWellMatrix u v w| ≤ planarWellMatrixConstant := by
  simpa only [mul_zero,neg_zero,Real.exp_zero,mul_one] using
    planarWellMatrix_two_far (D := 0) u v w (norm_nonneg _) (norm_nonneg _)

theorem planarHoppingMatrix_decay {m : ℕ} (u : Fin m → PlanarPosition) {D : ℝ}
    (hsep : ∀ i j, i ≠ j → D ≤ ‖u i-u j‖) (i j : Fin m) :
    |planarHoppingMatrix u i j| ≤
      (PlanarSobolev.wellBound*planarOverlapConstant)*Real.exp (-(9/10:ℝ)*D) := by
  classical
  unfold planarHoppingMatrix
  by_cases hij : i=j
  · simp only [hij,ite_true, if_true,abs_zero]
    exact mul_nonneg (mul_nonneg PlanarSobolev.wellBound_nonnegative
      planarOverlapConstant_nonnegative) (Real.exp_pos _).le
  · simp only [hij,ite_false, if_false]
    rw [← planarWellMatrix_hopping]
    exact (planarWellMatrix_overlap_decay (u i) (u j) (u i)).trans
      (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith [hsep i j hij]))
        (mul_nonneg PlanarSobolev.wellBound_nonnegative planarOverlapConstant_nonnegative))

theorem localizedCorrectedOneBodyMatrix_decay {freq D δ : ℝ}
    (hf : 0 < freq) (hD : 0 ≤ D) (hδ : 0 ≤ δ) (scale : ℝ)
    {m : ℕ} (u : Fin m → PlanarPosition)
    (hsep : ∀ i j, i ≠ j → D ≤ ‖u i-u j‖)
    (hcoeff : ∀ i, 0 ≤ localizedCounterterm freq u i/scale ∧
      localizedCounterterm freq u i/scale ≤ δ) (i j : Fin m) :
    |localizedCorrectedOneBodyMatrix freq scale u i j| ≤
      (PlanarSobolev.wellBound*planarOverlapConstant+(m:ℝ)*planarWellMatrixConstant)*
        Real.exp (-(9/10:ℝ)*D)+(m:ℝ)*δ*planarWellMatrixConstant := by
  have hC := planarWellMatrixConstant_nonnegative
  have hb : |localizedOneBodyMatrix freq u i j| ≤
      (PlanarSobolev.wellBound*planarOverlapConstant+(m:ℝ)*planarWellMatrixConstant)*
        Real.exp (-(9/10:ℝ)*D) := by
    have hsmall := localizedOneBodyMatrix_error_bound hf u hsep i j
    have hh := planarHoppingMatrix_decay u hsep i j
    have hexp : Real.exp (-(19/10:ℝ)*D) ≤ Real.exp (-(9/10:ℝ)*D) :=
      Real.exp_le_exp.mpr (by linarith)
    calc
      _ ≤ |localizedOneBodyMatrix freq u i j-planarHoppingMatrix u i j|+
          |planarHoppingMatrix u i j| := by
        simpa only [sub_zero] using abs_sub_le (localizedOneBodyMatrix freq u i j) (planarHoppingMatrix u i j) 0
      _ ≤ (m:ℝ)*planarWellMatrixConstant*Real.exp (-(9/10:ℝ)*D)+
          (PlanarSobolev.wellBound*planarOverlapConstant)*Real.exp (-(9/10:ℝ)*D) :=
        add_le_add (hsmall.trans (mul_le_mul_of_nonneg_left hexp (by positivity))) hh
      _ = _ := by ring
  have he : scale⁻¹*localizedCountertermMatrix freq u i j =
      ∑ k, (localizedCounterterm freq u k/scale)*planarWellMatrix (u i) (u j) (u k) := by
    simp only [localizedCountertermMatrix,Finset.mul_sum,div_eq_mul_inv]
    apply Finset.sum_congr rfl
    intro k _
    ring
  have hc : |scale⁻¹*localizedCountertermMatrix freq u i j| ≤ (m:ℝ)*δ*planarWellMatrixConstant := by
    rw [he]
    calc
      _ ≤ ∑ k, |(localizedCounterterm freq u k/scale)*planarWellMatrix (u i) (u j) (u k)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _k : Fin m, δ*planarWellMatrixConstant := by
        apply Finset.sum_le_sum
        intro k _
        rw [abs_mul,abs_of_nonneg (hcoeff k).1]
        exact mul_le_mul (hcoeff k).2 (planarWellMatrix_uniform_bound _ _ _)
          (abs_nonneg _) hδ
      _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]; ring
  rw [localizedCorrectedOneBodyMatrix_eq hf]
  exact (abs_add_le _ _).trans (add_le_add hb hc)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Programs_PolynomialResidualBudget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A fixed polynomial scale absorbs the four residual contributions after
physical amplification. The exponent can be chosen before the source size. -/

noncomputable section
namespace ContinuumCoulomb

theorem logarithmic_separation_residual {N D : ℝ} (hN : 2 ≤ N) (k : ℕ)
    (hD : 25*(k:ℝ)*Real.log N ≤ D) :
    Real.exp (-(19/10:ℝ)*D) ≤ ((N^k)^40)⁻¹ := by
  have hN0 : 0 < N := by linarith
  have hklog : 0 ≤ (k:ℝ)*Real.log N :=
    mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by linarith))
  have he := Real.exp_le_exp.mpr
    (show -(19/10:ℝ)*D ≤ -40*(k:ℝ)*Real.log N by nlinarith only [hD,hklog])
  apply he.trans_eq
  rw [show -40*(k:ℝ)*Real.log N = -((40*k:ℕ):ℝ)*Real.log N by push_cast; ring,
    neg_mul,Real.exp_neg,Real.exp_nat_mul,Real.exp_log hN0]
  congr 1
  rw [← pow_mul]
  congr 1
  omega

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_OneBodyScaleBudget
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The amplified matrix error decays after retaining the smallness of
the shifted matrix in the change of basis. -/

noncomputable section
namespace ContinuumCoulomb

theorem logarithmic_separation_overlap {N D : ℝ} (hN : 2 ≤ N) (k : ℕ)
    (hD : 25*(k:ℝ)*Real.log N ≤ D) :
    Real.exp (-(9/10:ℝ)*D) ≤ ((N^k)^22)⁻¹ := by
  have hN0 : 0 < N := by linarith
  have hklog : 0 ≤ (k:ℝ)*Real.log N :=
    mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by linarith))
  have he := Real.exp_le_exp.mpr
    (show -(9/10:ℝ)*D ≤ -22*(k:ℝ)*Real.log N by nlinarith only [hD,hklog])
  apply he.trans_eq
  rw [show -22*(k:ℝ)*Real.log N = -((22*k:ℕ):ℝ)*Real.log N by push_cast; ring,
    neg_mul,Real.exp_neg,Real.exp_nat_mul,Real.exp_log hN0]
  congr 1
  rw [← pow_mul]
  congr 1
  omega

private theorem matrix_monomial_bound {R m c : ℝ} {p q : ℕ}
    (hR : 1 ≤ R) (hm : 0 ≤ m) (hc : 0 ≤ c) (hp : p ≤ 5) (hq : 2 ≤ q) :
    c*m^p/R^q ≤ c*(m+1)^5/R^2 := by
  have hR0 : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have hm5 : m^p ≤ (m+1)^5 := (pow_le_pow_left₀ hm (by linarith) p).trans
    (pow_le_pow_right₀ (by linarith) hp)
  exact div_le_div₀ (show 0 ≤ c*(m+1)^5 by positivity)
    (mul_le_mul_of_nonneg_left hm5 hc) (pow_pos hR0 _)
    (pow_le_pow_right₀ hR hq)

theorem one_body_scale_identity {R a d E P O W m : ℝ}
    (hR : R ≠ 0) (ha : a ≠ 0) :
    let δ := d*m/(a*R^30)
    let B := (W*O+m*P)/R^22+m*δ*P
    (a*R^30)*(4*m^2/R^32+m^2*(4*(2*m*(O/R^22))*B)+4*m^2*(E*(m+1)/R^32))+
      (a*R^30*m*P+m^2*d*P)/R^40+m^2*d*(W*O)/R^22 =
    (4*a)*m^2/R^2+(4*a*E)*m^3/R^2+(4*a*E)*m^2/R^2+
      (8*a*W*O^2)*m^3/R^14+(8*a*O*P)*m^4/R^14+
      (8*d*O*P)*m^5/R^22+(a*P)*m/R^10+(d*P)*m^2/R^40+
      (d*W*O)*m^2/R^22 := by
  dsimp only
  field_simp [hR,ha]
  ring

theorem one_body_scale_bound {R a d E P O W m : ℝ}
    (hR : 1 ≤ R) (ha : 0 < a) (hd : 0 ≤ d) (hE : 0 ≤ E)
    (hP : 0 ≤ P) (hO : 0 ≤ O) (hW : 0 ≤ W) (hm : 0 ≤ m) :
    let δ := d*m/(a*R^30)
    let B := (W*O+m*P)/R^22+m*δ*P
    (a*R^30)*(4*m^2/R^32+m^2*(4*(2*m*(O/R^22))*B)+4*m^2*(E*(m+1)/R^32))+
      (a*R^30*m*P+m^2*d*P)/R^40+m^2*d*(W*O)/R^22 ≤
    (4*a+8*a*E+8*a*W*O^2+8*a*O*P+8*d*O*P+a*P+d*P+d*W*O)*(m+1)^5/R^2 := by
  dsimp only
  rw [one_body_scale_identity (ne_of_gt (lt_of_lt_of_le zero_lt_one hR)) (ne_of_gt ha)]
  have h1 := matrix_monomial_bound (p := 2) (q := 2) hR hm (show 0 ≤ 4*a by positivity) (by decide) (by decide)
  have h2 := matrix_monomial_bound (p := 3) (q := 2) hR hm (show 0 ≤ 4*a*E by positivity) (by decide) (by decide)
  have h3 := matrix_monomial_bound (p := 2) (q := 2) hR hm (show 0 ≤ 4*a*E by positivity) (by decide) (by decide)
  have h4 := matrix_monomial_bound (p := 3) (q := 14) hR hm (show 0 ≤ 8*a*W*O^2 by positivity) (by decide) (by decide)
  have h5 := matrix_monomial_bound (p := 4) (q := 14) hR hm (show 0 ≤ 8*a*O*P by positivity) (by decide) (by decide)
  have h6 := matrix_monomial_bound (p := 5) (q := 22) hR hm (show 0 ≤ 8*d*O*P by positivity) (by decide) (by decide)
  have h7 := matrix_monomial_bound (p := 1) (q := 10) hR hm (show 0 ≤ a*P by positivity) (by decide) (by decide)
  have h8 := matrix_monomial_bound (p := 2) (q := 40) hR hm (show 0 ≤ d*P by positivity) (by decide) (by decide)
  have h9 := matrix_monomial_bound (p := 2) (q := 22) hR hm (show 0 ≤ d*W*O by positivity) (by decide) (by decide)
  have hsum := add_le_add (add_le_add (add_le_add (add_le_add (add_le_add
    (add_le_add (add_le_add (add_le_add h1 h2) h3) h4) h5) h6) h7) h8) h9
  simp only [pow_one] at hsum
  exact hsum.trans_eq (by ring)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_ScalarScaleBudgets
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fixed size-independent thresholds for the scalar conditions in the
manufactured continuum comparison. -/

noncomputable section
namespace ContinuumCoulomb

theorem exists_polynomial_ratio_offset (C : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ q : ℕ, 1 ≤ q ∧ ∀ r p k : ℕ, q+r+p ≤ k → ∀ N : ℝ, 2 ≤ N →
      C*N^r/(N^k)^2 ≤ ε/N^p := by
  obtain ⟨q,hq,hbound⟩ := exists_polynomial_constant_bounds hε C
  refine ⟨q,by omega,fun r p k hk N hN => ?_⟩
  have hN0 : 0 < N := by linarith
  have hN1 : 1 ≤ N := by linarith
  calc
    _ ≤ N^q*N^r/(N^k)^2 := by
      gcongr
      exact (hbound N hN).2
    _ ≤ 1/N^(q+p) := by
      rw [div_le_div_iff₀ (by positivity : 0 < (N^k)^2) (pow_pos hN0 _),
        one_mul,← pow_add,← pow_add,← pow_mul]
      exact pow_le_pow_right₀ hN1 (by omega)
    _ = (N^q)⁻¹/N^p := by rw [pow_add]; field_simp
    _ ≤ ε/N^p := div_le_div_of_nonneg_right (hbound N hN).1 (by positivity)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Reduction_ActualOneBodyScale
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual corrected nuclear entries at the physical amplification. The
Gram error uses the decaying shifted matrix, not a uniform operator bound. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

theorem correctedNuclearOneBodyMatrix_physical_scale
    {rho H S freq D R a E : ℝ} (hrho : 0 ≤ rho) (hH : 0 < H)
    (hS : 0 < S) (hf : 0 < freq) (hD : 0 ≤ D) (hR : 2 ≤ R)
    (ha : 0 < a) (hE : 0 ≤ E) {m : ℕ} (u : Fin m → PlanarPosition)
    (hsep : ∀ i j, i ≠ j → D ≤ ‖u i-u j‖)
    (hs : m*localizedOverlapBound D ≤ 1/2)
    (h19 : Real.exp (-(19/10:ℝ)*D) ≤ 1/R^40)
    (h9 : Real.exp (-(9/10:ℝ)*D) ≤ 1/R^22)
    (hcoeff : ∀ i, 0 ≤ localizedCounterterm freq u i/(a*R^30) ∧
      localizedCounterterm freq u i/(a*R^30) ≤ localizedCountertermBound freq*m/(a*R^30))
    (hbox : ∀ j, (∫ x, finiteBoxOrbitalResidual rho H S freq (a*R^30) u j x^2) ≤ (1/R^32)^2)
    (F : Position → ℝ)
    (hI : ∀ i j, Integrable (fun x => F x*continuumLocalizedMode freq (u i) x*
      continuumLocalizedMode freq (u j) x))
    (hF : ∀ i j, |∫ x, F x*continuumLocalizedMode freq (u i) x*
      continuumLocalizedMode freq (u j) x| ≤ E*((m:ℝ)+1)/R^32) (i j : Fin m) :
    |(a*R^30)*correctedNuclearOneBodyMatrix rho H S freq (a*R^30) u F i j-
        localizedOneBodyTarget (a*R^30) freq u i j| ≤
      (4*a+8*a*E+8*a*PlanarSobolev.wellBound*planarOverlapConstant^2+
        8*a*planarOverlapConstant*planarWellMatrixConstant+
        8*localizedCountertermBound freq*planarOverlapConstant*planarWellMatrixConstant+
        a*planarWellMatrixConstant+localizedCountertermBound freq*planarWellMatrixConstant+
        localizedCountertermBound freq*PlanarSobolev.wellBound*planarOverlapConstant)*
      ((m:ℝ)+1)^5/R^2 := by
  have hR0 : 0 < R := by linarith
  have hR1 : 1 ≤ R := by linarith
  have hscale : 0 < a*R^30 := by positivity
  have hd := localizedCountertermBound_nonnegative freq
  have hP := planarWellMatrixConstant_nonnegative
  have hO := planarOverlapConstant_nonnegative
  have hW := PlanarSobolev.wellBound_nonnegative
  let δ := localizedCountertermBound freq*(m:ℝ)/(a*R^30)
  let B := (PlanarSobolev.wellBound*planarOverlapConstant+(m:ℝ)*planarWellMatrixConstant)/R^22+
    (m:ℝ)*δ*planarWellMatrixConstant
  have hδ : 0 ≤ δ := by dsimp [δ]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hb (p q : Fin m) : |localizedCorrectedOneBodyMatrix freq (a*R^30) u p q| ≤ B := by
    apply (localizedCorrectedOneBodyMatrix_decay hf hD hδ (a*R^30) u hsep hcoeff p q).trans
    dsimp only [B]
    have h := mul_le_mul_of_nonneg_left h9
      (show 0 ≤ PlanarSobolev.wellBound*planarOverlapConstant+(m:ℝ)*planarWellMatrixConstant by positivity)
    exact add_le_add (by simpa only [mul_one_div] using h) le_rfl
  have hg : localizedOverlapBound D ≤ planarOverlapConstant/R^22 := by
    unfold localizedOverlapBound
    simpa only [mul_one_div] using mul_le_mul_of_nonneg_left h9 hO
  have he := correctedNuclearOneBodyMatrix_error hrho hH hS hf (ne_of_gt hscale) u hδ hcoeff
    hsep hs (show 0 ≤ 1/R^32 by positivity) hbox hB hb F hI hF i j
  apply he.trans
  apply le_trans _ (one_body_scale_bound hR1 ha hd hE hP hO hW (Nat.cast_nonneg m))
  dsimp only [B,δ]
  rw [abs_of_pos hscale]
  have hgm : (m:ℝ)^2*(4*(2*m*localizedOverlapBound D)*B) ≤
      (m:ℝ)^2*(4*(2*m*(planarOverlapConstant/R^22))*B) := by gcongr
  have hn := add_le_add (add_le_add
    (show 4*(m:ℝ)^2*(1/R^32) ≤ 4*(m:ℝ)^2/R^32 by exact le_of_eq (by ring)) hgm)
    (le_refl (4*(m:ℝ)^2*(E*((m:ℝ)+1)/R^32)))
  have ht := mul_le_mul_of_nonneg_left hn hscale.le
  have he19 := mul_le_mul_of_nonneg_left h19
    (show 0 ≤ a*R^30*m*planarWellMatrixConstant+(m:ℝ)^2*localizedCountertermBound freq*planarWellMatrixConstant by positivity)
  have he9 := mul_le_mul_of_nonneg_left h9
    (show 0 ≤ (m:ℝ)^2*localizedCountertermBound freq*(PlanarSobolev.wellBound*planarOverlapConstant) by positivity)
  have he19' : (a*R^30*m*planarWellMatrixConstant+(m:ℝ)^2*localizedCountertermBound freq*planarWellMatrixConstant)*
      Real.exp (-(19/10:ℝ)*D) ≤
      (a*R^30*m*planarWellMatrixConstant+(m:ℝ)^2*localizedCountertermBound freq*planarWellMatrixConstant)/R^40 := by
    simpa only [mul_one_div] using he19
  have he9' : ((m:ℝ)^2*localizedCountertermBound freq*(PlanarSobolev.wellBound*planarOverlapConstant))*
      Real.exp (-(9/10:ℝ)*D) ≤
      ((m:ℝ)^2*localizedCountertermBound freq*(PlanarSobolev.wellBound*planarOverlapConstant))/R^22 := by
    simpa only [mul_one_div] using he9
  exact add_le_add (add_le_add ht he19') he9'

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Reduction_ActualOneBodyParameters
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A fixed exponent closes the actual one-body matrix error, including
finite slab, nuclear quadrature, counterterms and orthonormalization. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

theorem exists_actual_oneBody_parameters_oai {rho freq a E : ℝ}
    (hrho : 0 ≤ rho) (hf : 0 < freq) (ha : 0 < a) (hE : 0 ≤ E) :
    ∃ k₀ : ℕ, 1 ≤ k₀ ∧ ∀ r s p k : ℕ, k₀+5*r+72*s+p ≤ k →
    ∀ N H S D : ℝ, 2 ≤ N →
      (N^k)^50 ≤ H → H ≤ 2*(N^k)^50 →
      (N^k)^5 ≤ S → S ≤ 2*(N^k)^5 → 25*(k:ℝ)*Real.log N ≤ D →
    ∀ (m : ℕ) (u : Fin m → PlanarPosition), (m:ℝ) ≤ N^r →
      (∀ j, ‖u j‖ ≤ N^s) → (∀ i j, i ≠ j → D ≤ ‖u i-u j‖) →
    ∀ F : Position → ℝ,
      (∀ i j, Integrable (fun x => F x*continuumLocalizedMode freq (u i) x*
        continuumLocalizedMode freq (u j) x)) →
      (∀ i j, |∫ x, F x*continuumLocalizedMode freq (u i) x*continuumLocalizedMode freq (u j) x| ≤
        E*((m:ℝ)+1)/(N^k)^32) → ∀ i j,
      |(a*(N^k)^30)*correctedNuclearOneBodyMatrix rho H S freq (a*(N^k)^30) u F i j-
        localizedOneBodyTarget (a*(N^k)^30) freq u i j| ≤ (N^p)⁻¹ := by
  let d := localizedCountertermBound freq
  let P := planarWellMatrixConstant
  let O := planarOverlapConstant
  let W := PlanarSobolev.wellBound
  let C := 4*a+8*a*E+8*a*W*O^2+8*a*O*P+8*d*O*P+a*P+d*P+d*W*O
  have hd : 0 ≤ d := localizedCountertermBound_nonnegative freq
  have hP : 0 ≤ P := planarWellMatrixConstant_nonnegative
  have hO : 0 ≤ O := planarOverlapConstant_nonnegative
  have hW : 0 ≤ W := PlanarSobolev.wellBound_nonnegative
  have hC : 0 ≤ C := by dsimp [C]; positivity
  obtain ⟨qB,hqB,hbox⟩ := exists_finiteBoxResidual_parameter_offset hf hrho
  obtain ⟨qδ,hqδ,hδbound⟩ := exists_polynomial_ratio_offset (d/a) (by norm_num : (0:ℝ)<1)
  obtain ⟨qG,hqG,hgram⟩ := exists_polynomial_ratio_offset O (by norm_num : (0:ℝ)<1/2)
  obtain ⟨qE,hqE,herr⟩ := exists_polynomial_ratio_offset (32*C) (by norm_num : (0:ℝ)<1)
  refine ⟨qB+qδ+qG+qE+1,by omega,?_⟩
  intro r s p k hk N H S D hN hHlo hHhi hSlo hShi hD m u hm hu hsep F hI hF i j
  have hN0 : 0 < N := by linarith
  have hN1 : 1 ≤ N := by linarith
  have hR : 2 ≤ N^k := hN.trans (le_self_pow₀ hN1 (by omega))
  have hR0 : 0 < N^k := by positivity
  have hR1 : 1 ≤ N^k := one_le_pow₀ hN1
  have hH : 0 < H := (pow_pos hR0 50).trans_le hHlo
  have hS : 0 < S := (pow_pos hR0 5).trans_le hSlo
  have hD0 : 0 ≤ D := (mul_nonneg (by positivity : 0 ≤ 25*(k:ℝ))
    (Real.log_nonneg hN1)).trans hD
  have hscale : 0 < a*(N^k)^30 := by positivity
  let δ := d*(m:ℝ)/(a*(N^k)^30)
  have hδ : 0 ≤ δ := by dsimp [δ]; positivity
  have hδ1 : δ ≤ 1 := by
    calc
      _ ≤ (d/a)*N^r/(N^k)^2 := by
        dsimp [δ]
        calc
          _ = (d/a)*(m:ℝ)/(N^k)^30 := by ring
          _ ≤ (d/a)*N^r/(N^k)^2 := by
            gcongr
            decide
      _ ≤ 1 := by simpa only [pow_zero,div_one] using hδbound r 0 k (by omega) N hN
  have hcoeff (i : Fin m) : 0 ≤ localizedCounterterm freq u i/(a*(N^k)^30) ∧
      localizedCounterterm freq u i/(a*(N^k)^30) ≤ δ := by
    refine ⟨div_nonneg (localizedCounterterm_nonnegative freq u i) hscale.le,?_⟩
    apply div_le_div_of_nonneg_right _ hscale.le
    simpa only [d,mul_comm] using localizedCounterterm_bound hf u i
  have h19 : Real.exp (-(19/10:ℝ)*D) ≤ 1/(N^k)^40 :=
    by simpa only [one_div] using logarithmic_separation_residual hN k hD
  have h9 : Real.exp (-(9/10:ℝ)*D) ≤ 1/(N^k)^22 :=
    by simpa only [one_div] using logarithmic_separation_overlap hN k hD
  have hs : (m:ℝ)*localizedOverlapBound D ≤ 1/2 := by
    calc
      _ ≤ O*N^r/(N^k)^22 := by
        unfold localizedOverlapBound
        calc
          _ ≤ (m:ℝ)*(O*(1/(N^k)^22)) := mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left h9 hO) (Nat.cast_nonneg m)
          _ = O*(m:ℝ)/(N^k)^22 := by ring
          _ ≤ _ := by gcongr
      _ ≤ O*N^r/(N^k)^2 := div_le_div_of_nonneg_left (by positivity) (by positivity)
        (pow_le_pow_right₀ hR1 (by decide : 2 ≤ 22))
      _ ≤ 1/2 := by simpa only [pow_zero,div_one] using hgram r 0 k (by omega) N hN
  have hhalf : (N^k)^5 ≤ H/2 := by
    have h2 : 2*(N^k)^5 ≤ (N^k)^50 := by
      calc
        _ ≤ (N^k)*(N^k)^5 := mul_le_mul_of_nonneg_right hR (by positivity)
        _ = (N^k)^6 := by ring
        _ ≤ _ := pow_le_pow_right₀ hR1 (by decide)
    linarith [h2.trans hHlo]
  have hb (j : Fin m) :
      (∫ x, finiteBoxOrbitalResidual rho H S freq (a*(N^k)^30) u j x^2) ≤ (1/(N^k)^32)^2 := by
    apply (finiteBoxOrbitalResidual_square_bound hrho hH hS hf
      (pow_pos hR0 5) hhalf hSlo (a*(N^k)^30) u hδ hcoeff j).trans
    simpa only [one_div] using hbox r s k (by omega) N H S δ hN
      hHlo hHhi hSlo hShi hδ hδ1 m u hm hu j
  have hmat := correctedNuclearOneBodyMatrix_physical_scale hrho hH hS hf hD0 hR ha hE
    u hsep hs h19 h9 hcoeff hb F hI hF i j
  change _ ≤ C*((m:ℝ)+1)^5/(N^k)^2 at hmat
  apply hmat.trans
  have hm1 : (m:ℝ)+1 ≤ 2*N^r := by linarith [one_le_pow₀ hN1 (n := r)]
  calc
    C*((m:ℝ)+1)^5/(N^k)^2 ≤ C*(2*N^r)^5/(N^k)^2 := by gcongr
    _ = (32*C)*N^(5*r)/(N^k)^2 := by ring
    _ ≤ _ := by simpa only [one_div,one_mul] using herr (5*r) p k (by omega) N hN

end ContinuumCoulomb

end

end OAI
end

theorem solution : type_of% @OAI.ContinuumCoulomb.exists_actual_oneBody_parameters_oai := @OAI.ContinuumCoulomb.exists_actual_oneBody_parameters_oai
