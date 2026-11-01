-- Prove2me | solution 1 for OAI.ContinuumCoulomb.manufactured_grid_witness
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T21:26:02.370833+00:00
-- url     : https://prove2.me/submissions/0e87fad0-9d91-4dca-b286-1d3b81e6f5da

import Mathlib
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
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
import Theorems.Thm_OAI_ContinuumCoulomb_manufactured_uniform_nuclear_absolute_form

section
-- module Solutions.OAIQ092_CC.CoulombRadii_Variational_Axis
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

theorem norm_sq_axis_shift (x : Position) (a : Fin 3) (t : ℝ) :
    ‖x+t • axis a‖^2 = ‖x‖^2 + 2*t*x a + t^2 := by
  rw [norm_add_sq_real]
  simp [axis, inner_smul_right, EuclideanSpace.inner_single_right, norm_smul,
    Real.norm_eq_abs, sq_abs]
  ring

theorem second_deriv_quadratic_rpow {q b p : ℝ} (hq : 0 < q) :
    deriv (deriv (fun t : ℝ => (q+2*t*b+t^2)^p)) 0 =
      p*(p-1)*q^(p-2)*(2*b)^2 + 2*p*q^(p-1) := by
  let Q : ℝ → ℝ := fun t => q+2*t*b+t^2
  have hQ (t : ℝ) : HasDerivAt Q (2*b+2*t) t := by
    convert (((hasDerivAt_const t q).add
      (((hasDerivAt_id t).const_mul 2).mul_const b)).add
      ((hasDerivAt_id t).pow 2)) using 1
    all_goals try with_reducible_and_instances rfl
    all_goals first | rfl | norm_num [Q]
  have hQ0 : Q 0 = q := by simp [Q]
  have hQe : ∀ᶠ t in 𝓝 (0 : ℝ), Q t ≠ 0 :=
    (hQ 0).continuousAt.eventually_ne (by simpa [hQ0] using ne_of_gt hq)
  have hder : deriv (fun t => Q t ^ p) =ᶠ[𝓝 0]
      fun t => p*Q t^(p-1)*(2*b+2*t) := by
    filter_upwards [hQe] with t ht
    convert ((hQ t).rpow_const (Or.inl ht)).deriv using 1
    all_goals try with_reducible_and_instances rfl
    ring
  rw [hder.deriv_eq]
  have hh := (((hQ 0).rpow_const (p := p-1)
      (Or.inl (by simpa [hQ0] using ne_of_gt hq))).const_mul p).mul
    ((hasDerivAt_const 0 (2*b)).add ((hasDerivAt_id 0).const_mul 2))
  have hh' : HasDerivAt (fun t => p*Q t^(p-1)*(2*b+2*t))
      (p*((2*b)*(p-1)*q^(p-1-1))*(2*b)+p*q^(p-1)*2) 0 := by
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    all_goals first | rfl | norm_num [Q]
  rw [hh'.deriv]
  rw [show p-1-1 = p-2 by ring]
  ring

open scoped Convolution
open ContinuousLinearMap

theorem hasCompactSupport_partial {f : Position → ℝ} (hf : HasCompactSupport f)
    (v : Position) : HasCompactSupport (dirPartial f v) := hf.fderiv_apply ℝ v

end NeutralAtom
end
end
end

end OAI
end

section
-- module Solutions.OAIQ092_CC.CoulombRadii_Variational_WeakLaplacian
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

theorem hasCompactSupport_coordinateLaplacian {f : Position → ℝ}
    (hf : HasCompactSupport f) : HasCompactSupport (coordinateLaplacian f) := by
  apply hf.mono'
  intro x hx
  by_contra hn
  exact hx (coordinateLaplacian_eq_zero_of_notMem_tsupport hn)

end NeutralAtom
end
end
end

end OAI
end

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

theorem laplacian_regularizedKernel {ε : ℝ} (hε : ε ≠ 0) (x : Position) :
    coordinateLaplacian (regularizedKernel ε) x = -regularizedCharge ε x := by
  have hq : 0 < ‖x‖^2+ε^2 := add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_ne_zero hε)
  have he : ∀ a : Fin 3, (fun t : ℝ => regularizedKernel ε (x+t • axis a)) =
      (fun t => ((‖x‖^2+ε^2)+2*t*x a+t^2)^(-1/2 : ℝ)) := by
    intro a
    ext t
    unfold regularizedKernel
    rw [norm_sq_axis_shift]
    congr 1
    ring
  unfold coordinateLaplacian
  simp_rw [he, second_deriv_quadratic_rpow hq]
  norm_num
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
  have hpow : (‖x‖^2+ε^2)^(-5/2 : ℝ)*(‖x‖^2+ε^2) =
      (‖x‖^2+ε^2)^(-3/2 : ℝ) := by
    rw [← Real.rpow_add_one hq.ne']
    norm_num
  calc
    _ = 3*(‖x‖^2+ε^2)^(-5/2 : ℝ)*(∑ a : Fin 3, (x a)^2) -
        3*(‖x‖^2+ε^2)^(-3/2 : ℝ) := by
      rw [Finset.mul_sum]
      congr 1
      all_goals ring_nf
    _ = _ := by
      rw [← EuclideanSpace.real_norm_sq_eq]
      unfold regularizedCharge
      rw [← hpow]
      ring

theorem hasDerivAt_chargePrimitive (r : ℝ) :
    HasDerivAt chargePrimitive (3*r^2*(1+r^2)^(-5/2 : ℝ)) r := by
  have hp : 0 < 1+r^2 := by positivity
  have hd := ((hasDerivAt_id r).pow 3).mul
    (((hasDerivAt_const r 1).add ((hasDerivAt_id r).pow 2)).rpow_const
      (p := (-3/2 : ℝ)) (Or.inl hp.ne'))
  unfold chargePrimitive
  apply hd.congr_deriv
  norm_num
  have he : (1+r^2)^(-5/2 : ℝ)*(1+r^2) = (1+r^2)^(-3/2 : ℝ) := by
    rw [← Real.rpow_add_one hp.ne']; norm_num
  norm_num at he
  rw [← he]
  ring

theorem chargePrimitive_eq_ratio {r : ℝ} (hr : 0 ≤ r) :
    chargePrimitive r = (1-(1+r^2)⁻¹)^(3/2 : ℝ) := by
  have hp : 0 < 1+r^2 := by positivity
  have hh : 1-(1+r^2)⁻¹ = r^2/(1+r^2) := by field_simp; ring
  rw [hh, Real.div_rpow (sq_nonneg _) hp.le]
  have hn : (r^2)^(3/2 : ℝ) = r^3 := by
    rw [← Real.rpow_natCast_mul hr]
    norm_num
  rw [hn]
  unfold chargePrimitive
  rw [show (-3/2:ℝ) = -(3/2:ℝ) by ring, Real.rpow_neg hp.le]
  rfl

theorem tendsto_chargePrimitive : Tendsto chargePrimitive atTop (𝓝 1) := by
  have hp : Tendsto (fun r : ℝ => 1+r^2) atTop atTop :=
    tendsto_atTop_add_const_left _ 1 (tendsto_pow_atTop (by norm_num : (2:ℕ) ≠ 0))
  have hi := tendsto_inv_atTop_zero.comp hp
  have hh := (tendsto_const_nhds.sub hi).rpow tendsto_const_nhds
    (Or.inl (by norm_num : (1:ℝ)-0 ≠ 0) : (1:ℝ)-0 ≠ 0 ∨ 0 < (3/2:ℝ))
  apply Filter.Tendsto.congr' _ (by simpa using hh)
  filter_upwards [eventually_ge_atTop (0:ℝ)] with r hr
  exact (chargePrimitive_eq_ratio hr).symm

theorem integrable_radial_regularizedCharge_one :
    IntegrableOn (fun r : ℝ => 3*r^2*(1+r^2)^(-5/2 : ℝ)) (Set.Ioi 0) := by
  exact integrableOn_Ioi_deriv_of_nonneg' (fun r _ => hasDerivAt_chargePrimitive r)
    (fun r _ => by positivity) tendsto_chargePrimitive

theorem integral_radial_regularizedCharge_one :
    (∫ r : ℝ in Set.Ioi 0, 3*r^2*(1+r^2)^(-5/2 : ℝ)) = 1 := by
  have hder := integral_Ioi_of_hasDerivAt_of_nonneg'
    (a := (0:ℝ)) (fun r _ => hasDerivAt_chargePrimitive r)
    (fun r _ => by positivity : ∀ r ∈ Set.Ioi (0:ℝ), 0 ≤ 3*r^2*(1+r^2)^(-5/2 : ℝ))
    tendsto_chargePrimitive
  simpa [chargePrimitive] using hder

theorem regularizedCharge_one_eq : regularizedCharge 1 =
    fun x : Position => 3*(1+‖x‖^2)^(-5/2 : ℝ) := by
  ext x
  simp [regularizedCharge, add_comm]

theorem integrable_regularizedCharge_one : Integrable (regularizedCharge 1) := by
  rw [regularizedCharge_one_eq, integrable_fun_norm_addHaar volume
    (f := fun r : ℝ => 3*(1+r^2)^(-5/2:ℝ))]
  simpa [finrank_euclideanSpace_fin, smul_eq_mul, mul_comm, mul_assoc,
    mul_left_comm] using integrable_radial_regularizedCharge_one

theorem integral_regularizedCharge_one : (∫ x, regularizedCharge 1 x) = 4*Real.pi := by
  rw [regularizedCharge_one_eq, integral_fun_norm_addHaar volume
    (fun r : ℝ => 3*(1+r^2)^(-5/2:ℝ))]
  simp only [finrank_euclideanSpace_fin, smul_eq_mul, nsmul_eq_mul]
  norm_num
  have hi : (∫ r : ℝ in Set.Ioi 0, r^2*(3*(1+r^2)^(-(5/2): ℝ))) = 1 := by
    simpa only [neg_div, mul_assoc, mul_comm, mul_left_comm] using
      integral_radial_regularizedCharge_one
  rw [hi]
  simp only [Measure.real, EuclideanSpace.volume_ball_fin_three, ENNReal.ofReal_one,
    one_pow, one_mul, ENNReal.toReal_ofReal (by positivity : 0 ≤ Real.pi*4/3)]
  ring

theorem regularizedCharge_smul {ε : ℝ} (hε : 0 < ε) (x : Position) :
    regularizedCharge ε (ε • x) = (ε^3)⁻¹*regularizedCharge 1 x := by
  unfold regularizedCharge
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hε]
  have he : (ε*‖x‖)^2+ε^2 = ε^2*(‖x‖^2+1) := by ring
  rw [he, Real.mul_rpow (sq_nonneg _) (by positivity)]
  have hp : (ε^2)^(-5/2:ℝ) = (ε^5)⁻¹ := by
    rw [← Real.rpow_natCast_mul hε.le]
    norm_num [Real.rpow_neg hε.le]
  rw [hp]
  norm_num
  field_simp

theorem integral_regularizedCharge_scale {ε : ℝ} (hε : 0 < ε) (φ : Position → ℝ) :
    (∫ x, regularizedCharge ε x*φ x) = ∫ x, regularizedCharge 1 x*φ (ε • x) := by
  have hs := Measure.integral_comp_smul_of_nonneg volume
    (fun x => regularizedCharge ε x*φ x) ε (hR := hε.le)
  simp only [finrank_euclideanSpace_fin, smul_eq_mul] at hs
  have ht : (∫ x, regularizedCharge ε (ε • x)*φ (ε • x)) =
      (ε^3)⁻¹*(∫ x, regularizedCharge 1 x*φ (ε • x)) := by
    simp_rw [regularizedCharge_smul hε, mul_assoc]
    exact integral_const_mul _ _
  rw [ht] at hs
  exact (mul_left_cancel₀ (inv_ne_zero (pow_ne_zero _ hε.ne')) hs).symm

theorem regularizedCharge_nonneg (ε : ℝ) (x : Position) :
    0 ≤ regularizedCharge ε x := by unfold regularizedCharge; positivity

theorem continuous_regularizedCharge_one : Continuous (regularizedCharge 1) := by
  rw [regularizedCharge_one_eq]
  apply Continuous.const_mul
  apply Continuous.rpow_const
  · fun_prop
  · intro x
    left
    positivity

theorem regularizedCharge_tendsto_dirac {ε : ℕ → ℝ}
    (hε : ∀ n, 0 < ε n) (hlim : Tendsto ε atTop (𝓝 0))
    {φ : Position → ℝ} (hφ : Continuous φ) (hφc : HasCompactSupport φ) :
    Tendsto (fun n => ∫ x, regularizedCharge (ε n) x*φ x)
      atTop (𝓝 (4*Real.pi*φ 0)) := by
  obtain ⟨C, hC⟩ := hφ.bounded_above_of_compact_support hφc
  have hD := tendsto_integral_of_dominated_convergence
    (μ := (volume : Measure Position)) (fun x => regularizedCharge 1 x*C)
    (F := fun n x => regularizedCharge 1 x*φ (ε n • x))
    (f := fun x => regularizedCharge 1 x*φ 0)
    (fun n => (continuous_regularizedCharge_one.mul
      (hφ.comp (show Continuous (fun x : Position => ε n • x) by fun_prop))).aestronglyMeasurable)
    (integrable_regularizedCharge_one.mul_const C)
    (fun n => Filter.Eventually.of_forall (fun x => by
      rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (regularizedCharge_nonneg 1 x)]
      exact mul_le_mul_of_nonneg_left (hC _) (regularizedCharge_nonneg 1 x)))
    (Filter.Eventually.of_forall (fun x => by
      have he : Tendsto (fun n => ε n • x) atTop (𝓝 (0 : Position)) := by
        simpa using hlim.smul_const x
      exact tendsto_const_nhds.mul (hφ.continuousAt.tendsto.comp he)))
  simp only [integral_mul_const, integral_regularizedCharge_one] at hD
  simpa only [integral_regularizedCharge_scale (hε _)] using hD

theorem locallyIntegrable_coulombKernel : LocallyIntegrable coulombKernel volume := by
  intro x
  refine ⟨Metric.ball 0 (‖x‖+1), IsOpen.mem_nhds Metric.isOpen_ball ?_,
    coulombKernel_integrableOn_ball _⟩
  simpa only [Metric.mem_ball, dist_zero_right] using lt_add_one ‖x‖

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

theorem regularizedKernel_integral_tendsto {ε : ℕ → ℝ}
    (hε : ∀ n, 0 < ε n) (hlim : Tendsto ε atTop (𝓝 0))
    {φ : Position → ℝ} (hφ : Continuous φ) (hφc : HasCompactSupport φ) :
    Tendsto (fun n => ∫ x, regularizedKernel (ε n) x*φ x)
      atTop (𝓝 (∫ x, coulombKernel x*φ x)) := by
  have hae : ∀ᵐ x : Position ∂volume, x ≠ 0 := volume.ae_ne 0
  have hb : Integrable (fun x => coulombKernel x*‖φ x‖) := by
    simpa only [smul_eq_mul] using
      locallyIntegrable_coulombKernel.integrable_smul_right_of_hasCompactSupport hφ.norm hφc.norm
  apply tendsto_integral_of_dominated_convergence (fun x => coulombKernel x*‖φ x‖)
  · intro n
    exact ((contDiff_regularizedKernel (hε n).ne').continuous.mul hφ).aestronglyMeasurable
  · exact hb
  · intro n
    filter_upwards [hae] with x hx
    rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (regularizedKernel_nonneg _ _)]
    exact mul_le_mul_of_nonneg_right (regularizedKernel_le hx) (norm_nonneg _)
  · filter_upwards [hae] with x hx
    exact (regularizedKernel_tendsto hlim hx).mul_const (φ x)

theorem coordinateLaplacian_translate (φ : Position → ℝ) (x y : Position) :
    coordinateLaplacian (fun z => φ (z+y)) x = coordinateLaplacian φ (x+y) := by
  unfold coordinateLaplacian
  simp only [add_right_comm _ _ y]

end NeutralAtom
end
end
end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_CoulombPoisson
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.Coulomb.complexWindow_apply _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The Coulomb fundamental solution with finite smoothness

The manufactured planar well in the unit-charge paper has bounded continuous
derivatives through a finite order. Its density synthesis therefore needs
the fundamental-solution identity for compactly supported C² functions.
This extends the smooth-test identity by the same regularized
kernel argument, using only two integrations by parts.
-/

noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology ContDiff
namespace ContinuumCoulomb
open NeutralAtom (dirPartial coordinateLaplacian axis)

theorem integral_mul_laplacian_C2 (f phi : Position → ℝ)
    (hf : ContDiff ℝ 2 f) (hphi : ContDiff ℝ 2 phi) (hc : HasCompactSupport phi) :
    (∫ x, f x * coordinateLaplacian phi x) = ∫ x, coordinateLaplacian f x * phi x := by
  have hp (g : Position → ℝ) (hg : ContDiff ℝ 2 g) (v : Position) :
      ContDiff ℝ 1 (dirPartial g v) :=
    (hg.fderiv_right (show (1 : WithTop ℕ∞) + 1 ≤ 2 by norm_num)).clm_apply contDiff_const
  have hpp (g : Position → ℝ) (hg : ContDiff ℝ 2 g) (v : Position) :
      Continuous (dirPartial (dirPartial g v) v) :=
    (((hp g hg v).fderiv_right (show (0 : WithTop ℕ∞) + 1 ≤ 1 by norm_num)).clm_apply
      contDiff_const).continuous
  have hpc (v : Position) : HasCompactSupport (dirPartial phi v) :=
    NeutralAtom.hasCompactSupport_partial hc v
  have hppc (v : Position) : HasCompactSupport (dirPartial (dirPartial phi v) v) :=
    NeutralAtom.hasCompactSupport_partial (hpc v) v
  have hleft (v : Position) : Integrable (fun x => f x * dirPartial (dirPartial phi v) v x) :=
    (hf.continuous.mul (hpp phi hphi v)).integrable_of_hasCompactSupport (hppc v).mul_left
  have hright (v : Position) : Integrable (fun x => dirPartial (dirPartial f v) v x * phi x) :=
    ((hpp f hf v).mul hphi.continuous).integrable_of_hasCompactSupport hc.mul_left
  have hcross (v : Position) : Integrable (fun x => dirPartial f v x * dirPartial phi v x) :=
    ((hp f hf v).continuous.mul (hp phi hphi v).continuous).integrable_of_hasCompactSupport
      (hpc v).mul_left
  have hfg (v : Position) : Integrable (fun x => f x * dirPartial phi v x) :=
    (hf.continuous.mul (hp phi hphi v).continuous).integrable_of_hasCompactSupport
      (hpc v).mul_left
  have hfpg (v : Position) : Integrable (fun x => dirPartial f v x * phi x) :=
    ((hp f hf v).continuous.mul hphi.continuous).integrable_of_hasCompactSupport hc.mul_left
  have hby (v : Position) :
      (∫ x, f x * dirPartial (dirPartial phi v) v x) =
        ∫ x, dirPartial (dirPartial f v) v x * phi x := by
    calc
      _ = -(∫ x, dirPartial f v x * dirPartial phi v x) :=
        integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
          (hcross v) (hleft v) (hfg v)
          (fun x _ => hf.differentiable (by norm_num) x)
          (fun x _ => (hp phi hphi v).differentiable (by norm_num) x)
      _ = _ := by
        have h : (∫ x, dirPartial f v x * dirPartial phi v x) =
            -(∫ x, dirPartial (dirPartial f v) v x * phi x) :=
          integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
            (hright v) (hcross v) (hfpg v)
            (fun x _ => (hp f hf v).differentiable (by norm_num) x)
            (fun x _ => hphi.differentiable (by norm_num) x)
        rw [h, neg_neg]
  have hphi_eq (x : Position) : coordinateLaplacian phi x =
      ∑ a : Fin 3, dirPartial (dirPartial phi (axis a)) (axis a) x :=
    NeutralAtom.coordinateLaplacian_eq_partials hphi.contDiffAt
  have hf_eq (x : Position) : coordinateLaplacian f x =
      ∑ a : Fin 3, dirPartial (dirPartial f (axis a)) (axis a) x :=
    NeutralAtom.coordinateLaplacian_eq_partials hf.contDiffAt
  simp_rw [hphi_eq, Finset.mul_sum]
  rw [integral_finsetSum _ (fun a _ => hleft (axis a))]
  simp_rw [hby]
  rw [← integral_finsetSum _ (fun a _ => hright (axis a))]
  simp_rw [hf_eq, Finset.sum_mul]

theorem coulomb_laplacian_C2 (phi : Position → ℝ)
    (hphi : ContDiff ℝ 2 phi) (hc : HasCompactSupport phi) :
    (∫ x, Coulomb.coulombKernel x * coordinateLaplacian phi x) =
      -(4 * Real.pi * phi 0) := by
  let epsilon : ℕ → ℝ := fun n => ((n : ℝ) + 1)⁻¹
  have hepsilon (n : ℕ) : 0 < epsilon n := by dsimp [epsilon]; positivity
  have hlim : Tendsto epsilon atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp
      (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
  have hl := NeutralAtom.regularizedKernel_integral_tendsto hepsilon hlim
    (NeutralAtom.continuous_coordinateLaplacian hphi)
    (NeutralAtom.hasCompactSupport_coordinateLaplacian hc)
  have hr := (NeutralAtom.regularizedCharge_tendsto_dirac hepsilon hlim hphi.continuous hc).neg
  have heq : (fun n => ∫ x, NeutralAtom.regularizedKernel (epsilon n) x *
      coordinateLaplacian phi x) =
      (fun n => -(∫ x, NeutralAtom.regularizedCharge (epsilon n) x * phi x)) := by
    funext n
    rw [integral_mul_laplacian_C2 _ _
      ((NeutralAtom.contDiff_regularizedKernel (hepsilon n).ne').of_le (by first | simp | exact_mod_cast le_top)) hphi hc]
    simp_rw [NeutralAtom.laplacian_regularizedKernel (hepsilon n).ne', neg_mul, integral_neg]
  rw [heq] at hl
  exact tendsto_nhds_unique hl hr

theorem coulomb_translated_laplacian_C2 (phi : Position → ℝ)
    (hphi : ContDiff ℝ 2 phi) (hc : HasCompactSupport phi) (a : Position) :
    (∫ x, Coulomb.coulombKernel (x - a) * coordinateLaplacian phi x) =
      -(4 * Real.pi * phi a) := by
  have ht : ContDiff ℝ 2 (fun z => phi (z + a)) := hphi.comp (contDiff_id.add contDiff_const)
  have htc : HasCompactSupport (fun z => phi (z + a)) :=
    hc.comp_homeomorph (Homeomorph.addRight a)
  have h := coulomb_laplacian_C2 _ ht htc
  simp only [NeutralAtom.coordinateLaplacian_translate, zero_add] at h
  rw [← integral_add_right_eq_self
    (fun x => Coulomb.coulombKernel (x - a) * coordinateLaplacian phi x) a]
  simpa only [add_sub_cancel_right] using h

/-- Exact Green identity, with the sign for an attractive positive density. -/
theorem manufacturedCharge_potential (V : Position → ℝ) (hV : ContDiff ℝ 2 V)
    (hc : HasCompactSupport V) (y : Position) :
    -(∫ x, Coulomb.coulombKernel (y - x) * manufacturedCharge V x) = V y := by
  have h := coulomb_translated_laplacian_C2 V hV hc y
  have heq : (fun x => Coulomb.coulombKernel (y - x) * manufacturedCharge V x) =
      (fun x => (Coulomb.coulombKernel (x - y) * coordinateLaplacian V x) / (4 * Real.pi)) := by
    funext x
    dsimp [manufacturedCharge, Coulomb.coulombKernel]
    rw [norm_sub_rev]
    ring
  rw [heq, integral_div, h]
  field_simp

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

lemma coulombKernel_ball_integral {R : ℝ} (hR : 0 ≤ R) :
    (∫ x : Space in Metric.ball 0 R, coulombKernel x) = 2 * Real.pi * R^2 := by
  have H := integral_fun_norm_addHaar (volume : Measure Space)
    (fun t : ℝ => if t < R then t⁻¹ else 0)
  have hleft : (∫ x : Space in Metric.ball 0 R, coulombKernel x) =
      ∫ x : Space, (if ‖x‖ < R then ‖x‖⁻¹ else 0) := by
    rw [← integral_indicator measurableSet_ball]
    simp only [Set.indicator, Metric.mem_ball, dist_zero_right, coulombKernel]
  rw [hleft, H]
  have hball : volume.real (Metric.ball (0 : Space) 1) = 4 * Real.pi / 3 := by
    rw [Measure.real, EuclideanSpace.volume_ball_fin_three]
    norm_num
    rw [ENNReal.toReal_ofReal (by positivity)]
    ring
  have hdim : Module.finrank ℝ Space = 3 := by simp [Space]
  simp only [hdim, hball, nsmul_eq_mul, smul_eq_mul]
  have hint : (∫ t in Ioi (0:ℝ), t^(3-1) * (if t < R then t⁻¹ else 0)) = ∫ t in Ioo 0 R, t := by
    calc
      _ = ∫ t in Ioi (0:ℝ), (Iio R).indicator (fun u : ℝ => u) t := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro t ht
        change 0 < t at ht
        by_cases h : t < R
        · simp only [h, ite_true, if_true, Set.indicator, mem_Iio]
          norm_num
          field_simp
        · simp [Set.indicator, h]
      _ = _ := by rw [integral_indicator measurableSet_Iio, Measure.restrict_restrict measurableSet_Iio, inter_comm, Ioi_inter_Iio]
  rw [hint, setIntegral_congr_set Ioo_ae_eq_Ioc, ← intervalIntegral.integral_of_le hR]
  norm_num [integral_id]
  ring

lemma truncatedCoulomb_integrable (R : ℝ) : Integrable (truncatedCoulomb R) :=
  (coulombKernel_integrableOn_ball R).integrable_indicator measurableSet_ball
lemma truncatedCoulomb_integral {R : ℝ} (hR : 0 ≤ R) :
    (∫ x, truncatedCoulomb R x) = 2*Real.pi*R^2 := by
  unfold truncatedCoulomb
  rw [integral_indicator measurableSet_ball, coulombKernel_ball_integral hR]

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

lemma coulomb_convolution_bound {f : Space → ℝ} (hf : Integrable f) (hm : Measurable f)
    {M R : ℝ} (hf0 : ∀ y, 0 ≤ f y) (hfM : ∀ y, f y ≤ M) (hR : 0 < R) (x : Space) :
    (∫ y, coulombKernel (x-y) * f y) ≤ 2*Real.pi*M*R^2 + R⁻¹ * ∫ y, f y := by
  have hnear := (truncatedCoulomb_integrable R).comp_sub_left x
  calc
    _ ≤ ∫ y, M * truncatedCoulomb R (x-y) + R⁻¹ * f y :=
      integral_mono (coulomb_convolution_integrable hf hm hf0 hfM hR x)
        ((hnear.const_mul M).add (hf.const_mul R⁻¹)) (coulomb_integrand_bound hf0 hfM hR x)
    _ = _ := by
      rw [integral_add (hnear.const_mul M) (hf.const_mul R⁻¹), integral_const_mul,
        integral_const_mul, integral_sub_left_eq_self, truncatedCoulomb_integral hR.le]
      ring

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
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
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

theorem manufacturedCharge_continuous (V : Position → ℝ) (hV : ContDiff ℝ 2 V) :
    Continuous (manufacturedCharge V) :=
  (NeutralAtom.continuous_coordinateLaplacian hV).div_const _

theorem manufacturedCharge_compact (V : Position → ℝ) (hc : HasCompactSupport V) :
    HasCompactSupport (manufacturedCharge V) := by
  exact (NeutralAtom.hasCompactSupport_coordinateLaplacian hc).comp_left
    (g := fun t : ℝ => t / (4 * Real.pi)) (by simp)

theorem manufacturedCharge_zero {V : Position → ℝ} {x : Position} (hx : x ∉ tsupport V) :
    manufacturedCharge V x = 0 := by
  simp only [manufacturedCharge, NeutralAtom.coordinateLaplacian_eq_zero_of_notMem_tsupport hx,
    zero_div]

/-- Equation (4) of the unit-charge manuscript, as an identity of the actual
three-dimensional Coulomb integrals at every evaluation point. -/
theorem synthesizedDensity_potential {rho H S : ℝ} (hrho : 0 ≤ rho)
    (hH : 0 ≤ H) (hS : 0 ≤ S) (V : Position → ℝ)
    (hV : ContDiff ℝ 2 V) (hc : HasCompactSupport V)
    (hbound : ∀ x, |manufacturedCharge V x| ≤ rho / 2) (y : Position) :
    -(∫ x, Coulomb.coulombKernel (y - x) * synthesizedDensity rho H S V x) =
      slabPotential rho H S y + V y := by
  have hslabMeas : Measurable (slabDensity rho H S) :=
    measurable_const.indicator (slabDomain_isClosed H S).measurableSet
  have hslabBound (x : Position) : ‖slabDensity rho H S x‖ ≤ rho := by
    by_cases hx : x ∈ slabDomain H S
    · simp only [slabDensity, Set.indicator_of_mem hx, Real.norm_eq_abs, abs_of_nonneg hrho]
      exact le_rfl
    · simp only [slabDensity, Set.indicator_of_notMem hx, norm_zero]
      exact hrho
  have hIslab := Coulomb.coulomb_signed_convolution_integrable
    (slabDensity_integrable hH hS rho) hslabMeas hslabBound y
  have hIcharge := Coulomb.coulomb_signed_convolution_integrable
    ((manufacturedCharge_continuous V hV).integrable_of_hasCompactSupport
      (manufacturedCharge_compact V hc))
    (manufacturedCharge_continuous V hV).measurable
    (fun x => by simpa only [Real.norm_eq_abs] using hbound x) y
  have heq : (fun x => Coulomb.coulombKernel (y - x) * synthesizedDensity rho H S V x) =
      (fun x => Coulomb.coulombKernel (y - x) * slabDensity rho H S x +
        Coulomb.coulombKernel (y - x) * manufacturedCharge V x) := by
    funext x
    simp only [synthesizedDensity, mul_add]
  rw [heq, integral_add hIslab hIcharge, neg_add]
  rw [manufacturedCharge_potential V hV hc y]
  rfl

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

theorem positionSplitCoordinates_norm_sq (x : Position) :
    ‖x‖ ^ 2 = ‖(positionSplitCoordinates x).1‖ ^ 2 +
      (positionSplitCoordinates x).2 ^ 2 := by
  change ‖x‖ ^ 2 = ‖(positionSplitIsometry x).fst‖ ^ 2 + (positionSplitIsometry x).snd ^ 2
  have h := WithLp.prod_norm_sq_eq_of_L2 (positionSplitIsometry x)
  rw [positionSplitIsometry.norm_map] at h
  simpa only [Real.norm_eq_abs, sq_abs] using h

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
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_LocalizedCoulombTranslation
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Direct Coulomb coefficients as actual translated-density profiles. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

theorem continuumLocalizedMode_translate (freq : ℝ) (u : PlanarPosition) (x : Position) :
    continuumLocalizedMode freq u x = continuumLocalizedMode freq 0 (x - planarCenter u) := by
  simp only [continuumLocalizedMode, localizedMode, map_sub, planarCenter,
    ContinuousLinearEquiv.apply_symm_apply, Prod.fst_sub, Prod.snd_sub, sub_zero]

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

theorem manufacturedPlanarWell_zero_of_norm_ge_one {x : PlanarPosition} (hx : 1 ≤ ‖x‖) :
    manufacturedPlanarWell x = 0 := by
  simp only [manufacturedPlanarWell, planarForcing_zero_of_norm_ge_one hx, neg_zero, zero_div]

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

theorem slabWellCutoff_outer {S : ℝ} (hS : 0 < S) {z : ℝ} (hz : S ≤ |z|) :
    slabWellCutoff S z = 0 := by
  apply verticalCutoffBump.zero_of_le_dist
  change 2 ≤ dist ((2/S)*z) 0
  rw [dist_zero_right, Real.norm_eq_abs, abs_mul, abs_of_pos (div_pos (by norm_num) hS)]
  have hm := mul_le_mul_of_nonneg_left hz (div_pos (by norm_num : (0:ℝ)<2) hS).le
  have he : (2/S)*S = (2:ℝ) := by field_simp
  exact he.symm.le.trans hm

theorem manufacturedWellField_outer (freq scale : ℝ) {S : ℝ} (hS : 0 < S)
    {m : ℕ} (u : Fin m → PlanarPosition) (x : Position)
    (hx : S ≤ |(positionSplitCoordinates x).2|) :
    manufacturedWellField freq scale S u x = 0 := by
  simp only [manufacturedWellField, slabWellCutoff_outer hS hx, zero_mul]

theorem countertermWellSum_zero_far (freq scale : ℝ) {m : ℕ}
    (u : Fin m → PlanarPosition) (r : PlanarPosition)
    (hr : ∀ i, 1 ≤ ‖r-u i‖) : countertermWellSum freq scale u r = 0 := by
  apply Finset.sum_eq_zero
  intro i _
  rw [manufacturedPlanarWell_zero_of_norm_ge_one (hr i), mul_zero]

theorem manufacturedWellField_support (freq scale : ℝ) {S R : ℝ}
    (hS : 0 < S) (hR : 0 ≤ R) {m : ℕ} (u : Fin m → PlanarPosition)
    (hu : ∀ i, ‖u i‖ ≤ R) :
    tsupport (manufacturedWellField freq scale S u) ⊆
      Metric.closedBall (0 : Position) (R+S+1) := by
  apply closure_minimal _ Metric.isClosed_closedBall
  intro x hx
  have hz : |(positionSplitCoordinates x).2| < S := by
    by_contra hn
    exact hx (manufacturedWellField_outer freq scale hS u x (le_of_not_gt hn))
  have hr : ‖(positionSplitCoordinates x).1‖ < R+1 := by
    by_contra hn
    apply hx
    unfold manufacturedWellField
    rw [countertermWellSum_zero_far freq scale u _ (fun i => ?_), mul_zero]
    have ht : ‖(positionSplitCoordinates x).1‖ ≤
        ‖(positionSplitCoordinates x).1-u i‖ + ‖u i‖ := by
      simpa only [sub_add_cancel] using norm_add_le ((positionSplitCoordinates x).1-u i) (u i)
    linarith [hu i, le_of_not_gt hn]
  rw [Metric.mem_closedBall, dist_zero_right]
  have hs := positionSplitCoordinates_norm_sq x
  have hr2 := (sq_le_sq₀ (norm_nonneg _) (by linarith : 0 ≤ R+1)).mpr hr.le
  have hz2 := (sq_le_sq₀ (abs_nonneg _) hS.le).mpr hz.le
  rw [sq_abs] at hz2
  nlinarith [norm_nonneg x]

theorem manufacturedWellField_compact (freq scale : ℝ) {S : ℝ} (hS : 0 < S)
    {m : ℕ} (u : Fin m → PlanarPosition) :
    HasCompactSupport (manufacturedWellField freq scale S u) := by
  let R : ℝ := ∑ i, ‖u i‖
  have hR : 0 ≤ R := Finset.sum_nonneg (fun i _ => norm_nonneg _)
  have hu (i : Fin m) : ‖u i‖ ≤ R :=
    Finset.single_le_sum (fun j _ => norm_nonneg _) (Finset.mem_univ i)
  exact (isCompact_closedBall (0 : Position) (R+S+1)).of_isClosed_subset
    (isClosed_tsupport _) (manufacturedWellField_support freq scale hS hR u hu)

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
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_OneElectronCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Volume- and kinetic-energy-preserving identification of one-electron
configuration space with physical three-dimensional space. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb

theorem oneElectronCoordinates_apply (x : Configuration 1) :
    oneElectronCoordinates x = Coulomb.position x 0 := rfl

theorem oneElectronCoordinates_integral (f : Position → ℝ) :
    (∫ x : Configuration 1, f (oneElectronCoordinates x)) = ∫ y, f y :=
  oneElectronCoordinates.measurePreserving.integral_comp
    oneElectronCoordinates.toHomeomorph.measurableEmbedding f

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
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Nuclei_Cubature
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Equal-mass two-point Gauss rule

The tensor product of this degree-three rule uses eight equal masses in each
three-dimensional cell. Exact moment identities and fourth-derivative estimates
control its error.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace ContinuumCoulomb

/-- Exactness for all four monomial moments needed in each coordinate. -/
theorem gaussTwoPoint_moment (k : ℕ) (hk : k ≤ 3) :
    gaussTwoPoint (fun x => x ^ k) = ∫ x : ℝ in (-1)..1, x ^ k := by
  interval_cases k
  · norm_num [gaussTwoPoint, integral_pow]
  · norm_num [gaussTwoPoint, integral_pow]
  · norm_num [gaussTwoPoint, integral_pow, gaussAbscissa_sq]
  · norm_num [gaussTwoPoint, integral_pow]
    ring

/-- Equal-weight quadrature integrates every cubic exactly. -/
theorem gaussTwoPoint_cubic (coefficient : Fin 4 → ℝ) :
    gaussTwoPoint (fun x => ∑ k : Fin 4, coefficient k * x ^ (k : ℕ)) =
      ∫ x : ℝ in (-1)..1, ∑ k : Fin 4, coefficient k * x ^ (k : ℕ) := by
  have hsum :
      gaussTwoPoint (fun x => ∑ k : Fin 4, coefficient k * x ^ (k : ℕ)) =
        ∑ k : Fin 4, coefficient k * gaussTwoPoint (fun x => x ^ (k : ℕ)) := by
    unfold gaussTwoPoint
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [hsum, intervalIntegral.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro k _
    rw [gaussTwoPoint_moment k (by omega), intervalIntegral.integral_const_mul]
  · intro k _
    exact (continuous_const.mul (continuous_id.pow (k : ℕ))).intervalIntegrable _ _

/-- Uniform cubic approximation controls the quadrature and integral errors
separately, using the positivity and total mass of the rule. -/
theorem gaussTwoPoint_remainder_bound
    (f : ℝ → ℝ) (coefficient : Fin 4 → ℝ) {epsilon : ℝ}
    (hf : ContinuousOn f (Set.Icc (-1) 1))
    (happrox : ∀ x ∈ Set.Icc (-1) 1,
      |f x - ∑ k : Fin 4, coefficient k * x ^ (k : ℕ)| ≤ epsilon) :
    |gaussTwoPoint f - ∫ x : ℝ in (-1)..1, f x| ≤ 4 * epsilon := by
  let p : ℝ → ℝ := fun x => ∑ k : Fin 4, coefficient k * x ^ (k : ℕ)
  have hp : Continuous p := by unfold p; fun_prop
  have hg0 := gaussAbscissa_pos.le
  have hg1 : gaussAbscissa ≤ 1 := by nlinarith [gaussAbscissa_sq]
  have hleft := happrox (-gaussAbscissa) ⟨by linarith, by linarith⟩
  have hright := happrox gaussAbscissa ⟨by linarith, hg1⟩
  have hint : |∫ x : ℝ in (-1)..1, (f x - p x)| ≤ 2 * epsilon := by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const
      (f := fun x => f x - p x) (a := -1) (b := 1) (C := epsilon) ?_
    · norm_num [Real.norm_eq_abs] at h
      simpa only [mul_comm] using h
    · intro x hx
      have hx' : -1 < x ∧ x ≤ 1 := by
        simpa only [Set.uIoc_of_le (by norm_num : (-1 : ℝ) ≤ 1), Set.mem_Ioc] using hx
      simpa only [Real.norm_eq_abs, p] using happrox x ⟨hx'.1.le, hx'.2⟩
  have hfi : IntervalIntegrable f volume (-1) 1 :=
    ContinuousOn.intervalIntegrable_of_Icc (by norm_num) hf
  have hpi : IntervalIntegrable p volume (-1) 1 := hp.intervalIntegrable _ _
  have heq : gaussTwoPoint f - (∫ x : ℝ in (-1)..1, f x) =
      (f (-gaussAbscissa) - p (-gaussAbscissa)) +
        (f gaussAbscissa - p gaussAbscissa) -
          (∫ x : ℝ in (-1)..1, f x - p x) := by
    rw [intervalIntegral.integral_sub hfi hpi]
    have h := gaussTwoPoint_cubic coefficient
    change p (-gaussAbscissa) + p gaussAbscissa = ∫ x : ℝ in (-1)..1, p x at h
    unfold gaussTwoPoint
    linarith
  rw [heq]
  calc
    _ ≤ |f (-gaussAbscissa) - p (-gaussAbscissa)| +
        |f gaussAbscissa - p gaussAbscissa| + |∫ x : ℝ in (-1)..1, f x - p x| :=
      (abs_sub _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ 4 * epsilon := by dsimp [p] at *; linarith

/-- A genuine fourth-derivative error bound for the normalized cell. The
coarse constant suffices for the manuscript's polynomial error budgets. -/
theorem gaussTwoPoint_C4_error (f : ℝ → ℝ) {C : ℝ} (hCnonneg : 0 ≤ C)
    (hf : ContDiffOn ℝ 4 f (Set.Icc (-1) 1))
    (hC : ∀ x ∈ Set.Icc (-1) 1,
      ‖iteratedDerivWithin 4 f (Set.Icc (-1) 1) x‖ ≤ C) :
    |gaussTwoPoint f - ∫ x : ℝ in (-1)..1, f x| ≤ (32 / 3 : ℝ) * C := by
  let d : Fin 4 → ℝ := fun k => taylorCoeffWithin f (k : ℕ) (Set.Icc (-1) 1) (-1)
  let coefficient : Fin 4 → ℝ :=
    ![d 0 + d 1 + d 2 + d 3, d 1 + 2 * d 2 + 3 * d 3, d 2 + 3 * d 3, d 3]
  have htaylor (x : ℝ) :
      taylorWithinEval f 3 (Set.Icc (-1) 1) (-1) x =
        ∑ k : Fin 4, coefficient k * x ^ (k : ℕ) := by
    rw [taylor_within_apply]
    norm_num [coefficient, d, taylorCoeffWithin, Fin.sum_univ_succ,
      Finset.sum_range_succ, smul_eq_mul]
    ring
  have happrox : ∀ x ∈ Set.Icc (-1) 1,
      |f x - ∑ k : Fin 4, coefficient k * x ^ (k : ℕ)| ≤ (8 / 3 : ℝ) * C := by
    intro x hx
    have h := taylor_mean_remainder_bound (n := 3) (by norm_num : (-1 : ℝ) ≤ 1)
      hf hx hC
    rw [htaylor x] at h
    norm_num [Real.norm_eq_abs, sub_neg_eq_add] at h
    have hp : (x + 1) ^ 4 ≤ (16 : ℝ) := by
      calc
        (x + 1) ^ 4 ≤ (2 : ℝ) ^ 4 :=
          pow_le_pow_left₀ (by linarith [hx.1]) (by linarith [hx.2]) 4
        _ = 16 := by norm_num
    have hm := mul_le_mul_of_nonneg_left hp hCnonneg
    nlinarith
  have h := gaussTwoPoint_remainder_bound f coefficient hf.continuousOn happrox
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  ring

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Nuclei_GaussTensorError
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Tensorizing the one-dimensional Gauss error without differentiating a
parameter integral. This is used for the transported nuclear cubature. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

theorem gaussTwoPoint_sub (f g : ℝ → ℝ) :
    gaussTwoPoint (fun x => f x-g x) = gaussTwoPoint f-gaussTwoPoint g := by
  unfold gaussTwoPoint
  ring

theorem gaussTwoPoint_comm (f : ℝ → ℝ → ℝ) :
    gaussTwoPoint (fun x => gaussTwoPoint (f x)) =
      gaussTwoPoint (fun y => gaussTwoPoint (fun x => f x y)) := by
  unfold gaussTwoPoint
  ring

theorem gaussTwoPoint_abs_bound (f : ℝ → ℝ) {E : ℝ}
    (h : ∀ x ∈ Set.Icc (-1) 1, |f x| ≤ E) : |gaussTwoPoint f| ≤ 2*E := by
  have hg : gaussAbscissa ≤ 1 := by nlinarith only [gaussAbscissa_sq,gaussAbscissa_pos]
  have hp := gaussAbscissa_pos.le
  have h₁ := h (-gaussAbscissa) ⟨by linarith,by linarith⟩
  have h₂ := h gaussAbscissa ⟨by linarith,hg⟩
  exact (abs_add_le _ _).trans (by linarith)

theorem gaussTwoPoint_integral_comm (f : ℝ → ℝ → ℝ)
    (hf : Continuous f.uncurry) :
    gaussTwoPoint (fun x => ∫ y : ℝ in (-1)..1, f x y) =
      ∫ y : ℝ in (-1)..1, gaussTwoPoint (fun x => f x y) := by
  have hc (x : ℝ) : Continuous (f x) := hf.comp (continuous_const.prodMk continuous_id)
  exact (intervalIntegral.integral_add (hc (-gaussAbscissa) |>.intervalIntegrable _ _)
    (hc gaussAbscissa |>.intervalIntegrable _ _)).symm

theorem gaussTwoPoint_integral_continuous {X : Type*} [TopologicalSpace X] (f : X → ℝ → ℝ)
    (hf : Continuous f.uncurry) :
    Continuous (fun x => ∫ y : ℝ in (-1)..1, f x y) :=
  intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hf _ _

theorem gaussTwoPoint_function_continuous {X : Type*} [TopologicalSpace X] (f : X → ℝ → ℝ)
    (hf : Continuous f.uncurry) : Continuous (fun x => gaussTwoPoint (f x)) :=
  (hf.comp (continuous_id.prodMk continuous_const)).add
    (hf.comp (continuous_id.prodMk continuous_const))

theorem interval_abs_bound {E : ℝ} (f : ℝ → ℝ)
    (h : ∀ x ∈ Set.Icc (-1) 1, |f x| ≤ E) :
    |∫ x : ℝ in (-1)..1, f x| ≤ 2*E := by
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const
    (f := f) (a := (-1:ℝ)) (b := 1) (C := E) (fun x hx => by
      have hx' : -1 < x ∧ x ≤ 1 := by
        simpa only [Set.uIoc_of_le (by norm_num : (-1:ℝ) ≤ 1),Set.mem_Ioc] using hx
      simpa only [Real.norm_eq_abs] using h x ⟨hx'.1.le,hx'.2⟩)
  norm_num [Real.norm_eq_abs] at hi
  simpa only [mul_comm] using hi

theorem gaussTensor2_error (f : ℝ → ℝ → ℝ) (hf : Continuous f.uncurry) {E : ℝ}
    (hx : ∀ y ∈ Set.Icc (-1) 1,
      |gaussTwoPoint (fun x => f x y)-(∫ x : ℝ in (-1)..1, f x y)| ≤ E)
    (hy : ∀ x ∈ Set.Icc (-1) 1,
      |gaussTwoPoint (f x)-(∫ y : ℝ in (-1)..1, f x y)| ≤ E) :
    |gaussTwoPoint (fun x => gaussTwoPoint (f x))-
      (∫ x : ℝ in (-1)..1, ∫ y : ℝ in (-1)..1, f x y)| ≤ 4*E := by
  let A := gaussTwoPoint (fun x => gaussTwoPoint (f x))
  let B := ∫ x : ℝ in (-1)..1, gaussTwoPoint (f x)
  let C := ∫ x : ℝ in (-1)..1, ∫ y : ℝ in (-1)..1, f x y
  have h₁ : |A-B| ≤ 2*E := by
    have hid : A-B = gaussTwoPoint (fun y => gaussTwoPoint (fun x => f x y)-
        (∫ x : ℝ in (-1)..1, f x y)) := by
      rw [gaussTwoPoint_sub,gaussTwoPoint_comm]
      dsimp only [A,B]
      rw [gaussTwoPoint_integral_comm (fun y x => f x y)
        (hf.comp continuous_swap)]
    rw [hid]
    exact gaussTwoPoint_abs_bound _ hx
  have h₂ : |B-C| ≤ 2*E := by
    rw [show B-C = ∫ x : ℝ in (-1)..1,
      gaussTwoPoint (f x)-(∫ y : ℝ in (-1)..1, f x y) from
      (intervalIntegral.integral_sub
        ((gaussTwoPoint_function_continuous f hf).intervalIntegrable _ _)
        ((gaussTwoPoint_integral_continuous f hf).intervalIntegrable _ _)).symm]
    exact interval_abs_bound _ hy
  exact (abs_sub_le A B C).trans (by linarith only [h₁,h₂])

theorem gaussTensor3_first_comm (f : ℝ → ℝ → ℝ → ℝ) :
    gaussTwoPoint (fun x => gaussTwoPoint (fun y => gaussTwoPoint (f x y))) =
      gaussTwoPoint (fun y => gaussTwoPoint (fun z => gaussTwoPoint (fun x => f x y z))) := by
  unfold gaussTwoPoint
  ring

theorem gaussTensor2_integral_comm (f : ℝ → ℝ → ℝ → ℝ)
    (hf : Continuous (fun p : ℝ × ℝ × ℝ => f p.1 p.2.1 p.2.2)) :
    gaussTwoPoint (fun y => gaussTwoPoint (fun z => ∫ x : ℝ in (-1)..1, f x y z)) =
      ∫ x : ℝ in (-1)..1, gaussTwoPoint (fun y => gaussTwoPoint (f x y)) := by
  have hz (y : ℝ) : Continuous (fun p : ℝ × ℝ => f p.2 y p.1) :=
    hf.comp (show Continuous (fun p : ℝ × ℝ => (p.2,y,p.1)) by fun_prop)
  have hg : Continuous (fun p : ℝ × ℝ => gaussTwoPoint (f p.2 p.1)) := by
    unfold gaussTwoPoint
    exact (hf.comp (show Continuous (fun p : ℝ × ℝ => (p.2,p.1,-gaussAbscissa)) by fun_prop)).add
      (hf.comp (show Continuous (fun p : ℝ × ℝ => (p.2,p.1,gaussAbscissa)) by fun_prop))
  calc
    _ = gaussTwoPoint (fun y => ∫ x : ℝ in (-1)..1, gaussTwoPoint (f x y)) := by
      congr 1
      funext y
      exact gaussTwoPoint_integral_comm _ (hz y)
    _ = _ := gaussTwoPoint_integral_comm _ hg

theorem gaussTensor3_error (f : ℝ → ℝ → ℝ → ℝ)
    (hf : Continuous (fun p : ℝ × ℝ × ℝ => f p.1 p.2.1 p.2.2)) {E : ℝ}
    (hx : ∀ y ∈ Set.Icc (-1) 1, ∀ z ∈ Set.Icc (-1) 1,
      |gaussTwoPoint (fun x => f x y z)-(∫ x : ℝ in (-1)..1, f x y z)| ≤ E)
    (hy : ∀ x ∈ Set.Icc (-1) 1, ∀ z ∈ Set.Icc (-1) 1,
      |gaussTwoPoint (fun y => f x y z)-(∫ y : ℝ in (-1)..1, f x y z)| ≤ E)
    (hz : ∀ x ∈ Set.Icc (-1) 1, ∀ y ∈ Set.Icc (-1) 1,
      |gaussTwoPoint (f x y)-(∫ z : ℝ in (-1)..1, f x y z)| ≤ E) :
    |gaussTwoPoint (fun x => gaussTwoPoint (fun y => gaussTwoPoint (f x y)))-
      (∫ x : ℝ in (-1)..1, ∫ y : ℝ in (-1)..1, ∫ z : ℝ in (-1)..1, f x y z)| ≤ 12*E := by
  let A := gaussTwoPoint (fun x => gaussTwoPoint (fun y => gaussTwoPoint (f x y)))
  let B := ∫ x : ℝ in (-1)..1, gaussTwoPoint (fun y => gaussTwoPoint (f x y))
  let C := ∫ x : ℝ in (-1)..1, ∫ y : ℝ in (-1)..1, ∫ z : ℝ in (-1)..1, f x y z
  have h₁ : |A-B| ≤ 4*E := by
    have hid : A-B = gaussTwoPoint (fun y => gaussTwoPoint (fun z =>
        gaussTwoPoint (fun x => f x y z)-(∫ x : ℝ in (-1)..1, f x y z))) := by
      simp_rw [gaussTwoPoint_sub]
      rw [gaussTensor2_integral_comm f hf,← gaussTensor3_first_comm]
    rw [hid]
    have h := gaussTwoPoint_abs_bound _ (fun y hy' => gaussTwoPoint_abs_bound _ (hx y hy'))
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    ring
  have hg : Continuous (fun p : ℝ × ℝ => gaussTwoPoint (f p.1 p.2)) := by
    unfold gaussTwoPoint
    exact (hf.comp (show Continuous (fun p : ℝ × ℝ => (p.1,p.2,-gaussAbscissa)) by fun_prop)).add
      (hf.comp (show Continuous (fun p : ℝ × ℝ => (p.1,p.2,gaussAbscissa)) by fun_prop))
  have hI : Continuous (fun p : ℝ × ℝ => ∫ z : ℝ in (-1)..1, f p.1 p.2 z) :=
    gaussTwoPoint_integral_continuous (fun (p : ℝ × ℝ) z => f p.1 p.2 z)
      (hf.comp (show Continuous (fun p : (ℝ × ℝ) × ℝ => (p.1.1,p.1.2,p.2)) by fun_prop))
  have h₂ : |B-C| ≤ 8*E := by
    have hb := gaussTwoPoint_function_continuous (fun x y => gaussTwoPoint (f x y)) hg
    have hc := gaussTwoPoint_integral_continuous
      (fun x y => ∫ z : ℝ in (-1)..1, f x y z) hI
    rw [show B-C = ∫ x : ℝ in (-1)..1,
      gaussTwoPoint (fun y => gaussTwoPoint (f x y))-
        (∫ y : ℝ in (-1)..1, ∫ z : ℝ in (-1)..1, f x y z) from
      (intervalIntegral.integral_sub (hb.intervalIntegrable _ _) (hc.intervalIntegrable _ _)).symm]
    have h := interval_abs_bound _ (fun x hx' =>
      gaussTensor2_error (f x)
        (hf.comp (show Continuous (fun p : ℝ × ℝ => (x,p.1,p.2)) by fun_prop)) (hy x hx') (hz x hx'))
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    ring
  exact (abs_sub_le A B C).trans (by linarith only [h₁,h₂])

theorem gaussTensor3_C4_error (f : ℝ → ℝ → ℝ → ℝ)
    (hf : Continuous (fun p : ℝ × ℝ × ℝ => f p.1 p.2.1 p.2.2)) {C : ℝ} (hC : 0 ≤ C)
    (hfx : ∀ y ∈ Set.Icc (-1) 1, ∀ z ∈ Set.Icc (-1) 1,
      ContDiffOn ℝ 4 (fun x => f x y z) (Set.Icc (-1) 1))
    (hfy : ∀ x ∈ Set.Icc (-1) 1, ∀ z ∈ Set.Icc (-1) 1,
      ContDiffOn ℝ 4 (fun y => f x y z) (Set.Icc (-1) 1))
    (hfz : ∀ x ∈ Set.Icc (-1) 1, ∀ y ∈ Set.Icc (-1) 1,
      ContDiffOn ℝ 4 (f x y) (Set.Icc (-1) 1))
    (hCx : ∀ y ∈ Set.Icc (-1) 1, ∀ z ∈ Set.Icc (-1) 1, ∀ x ∈ Set.Icc (-1) 1,
      ‖iteratedDerivWithin 4 (fun x => f x y z) (Set.Icc (-1) 1) x‖ ≤ C)
    (hCy : ∀ x ∈ Set.Icc (-1) 1, ∀ z ∈ Set.Icc (-1) 1, ∀ y ∈ Set.Icc (-1) 1,
      ‖iteratedDerivWithin 4 (fun y => f x y z) (Set.Icc (-1) 1) y‖ ≤ C)
    (hCz : ∀ x ∈ Set.Icc (-1) 1, ∀ y ∈ Set.Icc (-1) 1, ∀ z ∈ Set.Icc (-1) 1,
      ‖iteratedDerivWithin 4 (f x y) (Set.Icc (-1) 1) z‖ ≤ C) :
    |gaussTwoPoint (fun x => gaussTwoPoint (fun y => gaussTwoPoint (f x y)))-
      (∫ x : ℝ in (-1)..1, ∫ y : ℝ in (-1)..1, ∫ z : ℝ in (-1)..1, f x y z)| ≤ 128*C := by
  have h := gaussTensor3_error f hf
    (fun y hy z hz => gaussTwoPoint_C4_error _ hC (hfx y hy z hz) (hCx y hy z hz))
    (fun x hx z hz => gaussTwoPoint_C4_error _ hC (hfy x hx z hz) (hCy x hx z hz))
    (fun x hx y hy => gaussTwoPoint_C4_error _ hC (hfz x hx y hy) (hCz x hx y hy))
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  ring

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_CoulombKernelSmooth
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.Coulomb.complexWindow_apply _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Smoothness of the actual Coulomb kernel away from its pole, with
uniform derivative bounds on the fixed annulus used in cell estimates. -/

noncomputable section
open scoped ContDiff BigOperators Classical
namespace ContinuumCoulomb

theorem coulombKernel_contDiffAt {x : Position} (hx : x ≠ 0) :
    ContDiffAt ℝ ∞ Coulomb.coulombKernel x := by
  exact (contDiffAt_norm ℝ hx).inv (norm_ne_zero_iff.mpr hx)

theorem coulombKernel_iteratedFDeriv_continuousAt (k : ℕ) {x : Position} (hx : x ≠ 0) :
    ContinuousAt (iteratedFDeriv ℝ k Coulomb.coulombKernel) x :=
  ((coulombKernel_contDiffAt hx).differentiableAt_iteratedFDeriv (ENat.natCast_lt_of_coe_top_le_withTop le_rfl k)).continuousAt

theorem coulombKernel_fixed_annulus_bounds :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ k : Fin 5, ∀ x : Position, 1/2 ≤ ‖x‖ → ‖x‖ ≤ 2 →
      ‖iteratedFDeriv ℝ (k:ℕ) Coulomb.coulombKernel x‖ ≤ C := by
  let K := Metric.closedBall (0:Position) 2 \ Metric.ball 0 (1/2)
  have hK : IsCompact K := (isCompact_closedBall (0:Position) 2).diff Metric.isOpen_ball
  have hk (k : Fin 5) : ContinuousOn (iteratedFDeriv ℝ (k:ℕ) Coulomb.coulombKernel) K := by
    intro x hx
    apply (coulombKernel_iteratedFDeriv_continuousAt k ?_).continuousWithinAt
    intro he
    have hn := hx.2
    apply hn
    rw [he,Metric.mem_ball,dist_self]
    norm_num
  choose C hC using fun k : Fin 5 => hK.exists_bound_of_continuousOn (hk k)
  refine ⟨1+∑ k, |C k|,?_,fun k x hx₁ hx₂ => ?_⟩
  · exact le_add_of_nonneg_right (Finset.sum_nonneg (fun _ _ => abs_nonneg _))
  · have hx : x ∈ K := by
      refine ⟨?_,?_⟩
      · simpa only [Metric.mem_closedBall,dist_zero_right] using hx₂
      · simpa only [Metric.mem_ball,dist_zero_right,not_lt] using hx₁
    have hb := Finset.single_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin 5))) =>
      abs_nonneg (C j)) (Finset.mem_univ k)
    exact (hC k x hx).trans ((le_abs_self _).trans (by linarith))

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Reduction_Dilation
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Spatial dilation on the actual weak H¹ domain

The physical-energy amplification in both manuscripts changes coordinates
on the full fermionic form domain. Here weak derivatives are transformed
by changing variables in the compact-test identity, rather than assuming
pointwise differentiability of an arbitrary state.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb

theorem coulombKernel_smul (x : Position) {scale : ℝ} (hscale : 0 < scale) :
    Coulomb.coulombKernel (scale • x) = scale⁻¹ * Coulomb.coulombKernel x := by
  simp only [Coulomb.coulombKernel, norm_smul, Real.norm_eq_abs,
    abs_of_pos hscale, mul_inv_rev]
  ring

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_CoulombKernelHomogeneity
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.Coulomb.complexWindow_apply _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Derivatives through order four of the actual inverse-distance kernel
decay by the appropriate inverse power. -/

noncomputable section
open scoped ContDiff
namespace ContinuumCoulomb

theorem coulombKernel_iteratedFDeriv_scaling (k : ℕ) {c : ℝ} (hc : 0 < c)
    {x : Position} (hx : x ≠ 0) :
    c^k*‖iteratedFDeriv ℝ k Coulomb.coulombKernel (c • x)‖ =
      c⁻¹*‖iteratedFDeriv ℝ k Coulomb.coulombKernel x‖ := by
  let e : Position ≃L[ℝ] Position := ContinuousLinearEquiv.smulLeft (Units.mk0 c hc.ne')
  have he (z : Position) : e z = c • z := rfl
  have hd := e.iteratedFDerivWithin_comp_right Coulomb.coulombKernel uniqueDiffOn_univ
    (Set.mem_univ (e x)) k
  simp only [Set.preimage_univ,iteratedFDerivWithin_univ] at hd
  have hright : iteratedFDeriv ℝ k (Coulomb.coulombKernel ∘ e) x =
      c^k • iteratedFDeriv ℝ k Coulomb.coulombKernel (c • x) := by
    rw [hd]
    ext v
    simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply,
      smul_apply,ContinuousLinearEquiv.coe_coe,he]
    simpa only [Finset.prod_const,Finset.card_univ,Fintype.card_fin] using
      (iteratedFDeriv ℝ k Coulomb.coulombKernel (c • x)).map_smul_univ (fun _ => c) v
  have hfun : Coulomb.coulombKernel ∘ e = c⁻¹ • Coulomb.coulombKernel := by
    funext z
    exact coulombKernel_smul z hc
  rw [hfun,iteratedFDeriv_const_smul_apply
    ((coulombKernel_contDiffAt hx).of_le (ENat.natCast_lt_of_coe_top_le_withTop le_rfl k).le : ContDiffAt ℝ k Coulomb.coulombKernel x)] at hright
  have hn := congrArg norm hright.symm
  simpa only [norm_smul,Real.norm_eq_abs,abs_of_pos (pow_pos hc k),
    abs_of_pos (inv_pos.mpr hc)] using hn

theorem coulombKernel_derivative_decay :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ k : Fin 5, ∀ x : Position, x ≠ 0 →
      ‖iteratedFDeriv ℝ (k:ℕ) Coulomb.coulombKernel x‖*‖x‖^((k:ℕ)+1) ≤ C := by
  obtain ⟨C,hC,hbound⟩ := coulombKernel_fixed_annulus_bounds
  refine ⟨C,hC,fun k x hx => ?_⟩
  let y : Position := ‖x‖⁻¹ • x
  have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hy : ‖y‖ = 1 := by
    simp only [y,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hn)]
    exact inv_mul_cancel₀ hn.ne'
  have hyne : y ≠ 0 := by intro he; simp only [he,norm_zero] at hy; norm_num at hy
  have hxy : ‖x‖ • y = x := by
    simp only [y,smul_smul,mul_inv_cancel₀ hn.ne',one_smul]
  have h := coulombKernel_iteratedFDeriv_scaling k hn hyne
  rw [hxy] at h
  have hb := hbound k y (by rw [hy]; norm_num) (by rw [hy]; norm_num)
  calc
    _ = ‖x‖*(‖x‖^(k:ℕ)*‖iteratedFDeriv ℝ (k:ℕ) Coulomb.coulombKernel x‖) := by ring
    _ = ‖x‖*(‖x‖⁻¹*‖iteratedFDeriv ℝ (k:ℕ) Coulomb.coulombKernel y‖) := by rw [h]
    _ = ‖iteratedFDeriv ℝ (k:ℕ) Coulomb.coulombKernel y‖ := by
      rw [← mul_assoc,mul_inv_cancel₀ hn.ne',one_mul]
    _ ≤ C := hb

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_DirectionalFourthDerivative
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fourth derivatives along the affine coordinate lines used by cubature. -/

noncomputable section
namespace ContinuumCoulomb

/-- Local smoothness suffices; the function may be singular away from the line point. -/
theorem fourthDeriv_affine_line (f : Position → ℝ) (b v : Position) (t : ℝ)
    (hf : ContDiffAt ℝ 4 f (b+t • v)) :
    iteratedDeriv 4 (fun s : ℝ => f (b+s • v)) t =
      iteratedFDeriv ℝ 4 f (b+t • v) (fun _ => v) := by
  let L : ℝ →L[ℝ] Position := (ContinuousLinearMap.id ℝ ℝ).smulRight v
  let g : Position → ℝ := fun z => f (b+z)
  have hg : ContDiffAt ℝ 4 g (L t) :=
    hf.comp (L t) (contDiffAt_const.add contDiffAt_id)
  obtain ⟨U,hU,ht,hgU⟩ := hg.contDiffOn' le_rfl (by norm_num)
  have hgU : ContDiffOn ℝ 4 g U := by simpa using hgU
  have hpre : IsOpen (L ⁻¹' U) := hU.preimage L.continuous
  have hgt : ContDiffAt ℝ 4 (g ∘ L) t := hg.comp t L.contDiff.contDiffAt
  have h := L.iteratedFDerivWithin_comp_right hgU hU.uniqueDiffOn hpre.uniqueDiffOn ht
    (i := 4) le_rfl
  rw [iteratedFDerivWithin_eq_iteratedFDeriv hpre.uniqueDiffOn hgt ht,
    iteratedFDerivWithin_eq_iteratedFDeriv hU.uniqueDiffOn hg ht] at h
  change iteratedFDeriv ℝ 4 (g ∘ L) t (fun _ => 1) = _
  rw [h]
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply]
  have hL (s : ℝ) : L s = s • v := rfl
  simp only [hL,one_smul]
  change iteratedFDeriv ℝ 4 (fun z => f (b+z)) (t • v) (fun _ => v) = _
  rw [iteratedFDeriv_comp_add_left]

theorem fourthDeriv_affine_line_bound (f : Position → ℝ) (b v : Position) (t : ℝ)
    (hf : ContDiffAt ℝ 4 f (b+t • v)) :
    |iteratedDeriv 4 (fun s : ℝ => f (b+s • v)) t| ≤
      ‖iteratedFDeriv ℝ 4 f (b+t • v)‖*‖v‖^4 := by
  rw [fourthDeriv_affine_line f b v t hf,← Real.norm_eq_abs]
  simpa only [Finset.prod_const,Finset.card_univ,Fintype.card_fin] using
    (iteratedFDeriv ℝ 4 f (b+t • v)).le_opNorm (fun _ => v)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Nuclei_GaussPositionCell
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual eight equal masses on any translated cube, with a fourth-order
error bound from the ambient fourth Fréchet derivative. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

theorem cubePoint_contDiff (b : Position) (d : ℝ) :
    ContDiff ℝ 4 (fun p : ℝ × ℝ × ℝ => cubePoint b d p.1 p.2.1 p.2.2) := by
  unfold cubePoint
  fun_prop

private theorem fourthDerivWithin_line_bound (f : Position → ℝ) (b v : Position) (t : ℝ)
    (hf : ContDiffAt ℝ 4 f (b+t • v)) (ht : t ∈ Set.Icc (-1:ℝ) 1) :
    ‖iteratedDerivWithin 4 (fun s : ℝ => f (b+s • v)) (Set.Icc (-1) 1) t‖ ≤
      ‖iteratedFDeriv ℝ 4 f (b+t • v)‖*‖v‖^4 := by
  have hline : ContDiffAt ℝ 4 (fun s : ℝ => f (b+s • v)) t :=
    hf.comp t (show ContDiffAt ℝ 4 (fun s : ℝ => b+s • v) t by fun_prop)
  rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc (by norm_num))
    hline ht,Real.norm_eq_abs]
  exact fourthDeriv_affine_line_bound f b v t hf

private theorem cube_axis_fourth_bound (f : Position → ℝ) (b v : Position) (t d C : ℝ)
    (hf : ContDiffAt ℝ 4 f (b+t • v)) (ht : t ∈ Set.Icc (-1:ℝ) 1)
    (hD : ‖iteratedFDeriv ℝ 4 f (b+t • v)‖ ≤ C) (hv : ‖v‖ = d) :
    ‖iteratedDerivWithin 4 (fun s : ℝ => f (b+s • v)) (Set.Icc (-1) 1) t‖ ≤ C*d^4 := by
  apply (fourthDerivWithin_line_bound f b v t hf ht).trans
  rw [hv]
  exact mul_le_mul_of_nonneg_right hD (pow_nonneg (norm_nonneg v |>.trans_eq hv) _)

/-- A translated cell incurs at most `C*h^7`, so summing cell volumes leaves
an `h^4` global error. -/
theorem positionCellGauss_error (f : Position → ℝ) (hf : ContDiff ℝ 4 f)
    (b : Position) {h C : ℝ} (hh : 0 ≤ h) (hC : 0 ≤ C)
    (hD : ∀ x ∈ Set.Icc (-1:ℝ) 1, ∀ y ∈ Set.Icc (-1:ℝ) 1,
      ∀ z ∈ Set.Icc (-1:ℝ) 1,
      ‖iteratedFDeriv ℝ 4 f (cubePoint b (h/2) x y z)‖ ≤ C) :
    |positionCellGauss b h f-positionCellIntegral b h f| ≤ C*h^7 := by
  let d := h/2
  have hd : 0 ≤ d := by dsimp [d]; positivity
  have hv (i : Fin 3) : ‖d • (EuclideanSpace.single i 1 : Position)‖ = d := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hd,PiLp.norm_single]
    norm_num
  have hxline (x y z : ℝ) : cubePoint b d x y z =
      (b+y • (d • EuclideanSpace.single 1 1)+z • (d • EuclideanSpace.single 2 1))+
      x • (d • EuclideanSpace.single 0 1) := by unfold cubePoint; module
  have hyline (x y z : ℝ) : cubePoint b d x y z =
      (b+x • (d • EuclideanSpace.single 0 1)+z • (d • EuclideanSpace.single 2 1))+
      y • (d • EuclideanSpace.single 1 1) := by unfold cubePoint; module
  have hzline (x y z : ℝ) : cubePoint b d x y z =
      (b+x • (d • EuclideanSpace.single 0 1)+y • (d • EuclideanSpace.single 1 1))+
      z • (d • EuclideanSpace.single 2 1) := rfl
  have hc : Continuous (fun p : ℝ × ℝ × ℝ => f (cubePoint b d p.1 p.2.1 p.2.2)) :=
    hf.continuous.comp (cubePoint_contDiff b d).continuous
  have hfx (y z : ℝ) : ContDiff ℝ 4 (fun x => f (cubePoint b d x y z)) := by
    apply hf.comp
    unfold cubePoint
    fun_prop
  have hfy (x z : ℝ) : ContDiff ℝ 4 (fun y => f (cubePoint b d x y z)) := by
    apply hf.comp
    unfold cubePoint
    fun_prop
  have hfz (x y : ℝ) : ContDiff ℝ 4 (fun z => f (cubePoint b d x y z)) := by
    apply hf.comp
    unfold cubePoint
    fun_prop
  have hDx (y : ℝ) (hy : y ∈ Set.Icc (-1:ℝ) 1) (z : ℝ) (hz : z ∈ Set.Icc (-1:ℝ) 1)
      (x : ℝ) (hx : x ∈ Set.Icc (-1:ℝ) 1) :
      ‖iteratedDerivWithin 4 (fun x => f (cubePoint b d x y z)) (Set.Icc (-1) 1) x‖ ≤ C*d^4 := by
    simp_rw [hxline]
    exact cube_axis_fourth_bound f _ _ x d C hf.contDiffAt hx
      (by rw [← hxline]; exact hD x hx y hy z hz) (hv 0)
  have hDy (x : ℝ) (hx : x ∈ Set.Icc (-1:ℝ) 1) (z : ℝ) (hz : z ∈ Set.Icc (-1:ℝ) 1)
      (y : ℝ) (hy : y ∈ Set.Icc (-1:ℝ) 1) :
      ‖iteratedDerivWithin 4 (fun y => f (cubePoint b d x y z)) (Set.Icc (-1) 1) y‖ ≤ C*d^4 := by
    simp_rw [hyline]
    exact cube_axis_fourth_bound f _ _ y d C hf.contDiffAt hy
      (by rw [← hyline]; exact hD x hx y hy z hz) (hv 1)
  have hDz (x : ℝ) (hx : x ∈ Set.Icc (-1:ℝ) 1) (y : ℝ) (hy : y ∈ Set.Icc (-1:ℝ) 1)
      (z : ℝ) (hz : z ∈ Set.Icc (-1:ℝ) 1) :
      ‖iteratedDerivWithin 4 (fun z => f (cubePoint b d x y z)) (Set.Icc (-1) 1) z‖ ≤ C*d^4 := by
    simp_rw [hzline]
    exact cube_axis_fourth_bound f _ _ z d C hf.contDiffAt hz
      (by rw [← hzline]; exact hD x hx y hy z hz) (hv 2)
  have he := gaussTensor3_C4_error (fun x y z => f (cubePoint b d x y z)) hc
    (mul_nonneg hC (pow_nonneg hd 4))
    (fun y _ z _ => (hfx y z).contDiffOn)
    (fun x _ z _ => (hfy x z).contDiffOn)
    (fun x _ y _ => (hfz x y).contDiffOn) hDx hDy hDz
  change |d^3*_ - d^3*_| ≤ _
  rw [← mul_sub,abs_mul,abs_of_nonneg (pow_nonneg hd 3)]
  apply (mul_le_mul_of_nonneg_left he (pow_nonneg hd 3)).trans_eq
  dsimp [d]
  ring

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Nuclei_MoserFlux
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The explicit density homotopy and continuity equation used to transport
uniform slab density in the unit-charge construction. The identities describe
the explicit field and its density homotopy. -/

noncomputable section
open scoped BigOperators
namespace ContinuumCoulomb
open NeutralAtom (dirPartial coordinateLaplacian axis)

theorem homotopyDensity_bounds {rho : ℝ} (V : Position → ℝ)
    (hbound : ∀ x, |manufacturedCharge V x| ≤ rho / 2)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (x : Position) :
    rho / 2 ≤ homotopyDensity rho V t x ∧
      homotopyDensity rho V t x ≤ 3 * rho / 2 := by
  have hrho : 0 ≤ rho := by linarith [abs_nonneg (manufacturedCharge V x), hbound x]
  have hb := abs_le.mp (hbound x)
  have hlow := mul_le_mul_of_nonneg_left hb.1 ht0
  have hupp := mul_le_mul_of_nonneg_left hb.2 ht0
  have hscale := mul_le_mul_of_nonneg_right ht1 (by linarith : 0 ≤ rho / 2)
  dsimp [homotopyDensity]
  constructor <;> nlinarith

theorem homotopyDensity_pos {rho : ℝ} (hrho : 0 < rho) (V : Position → ℝ)
    (hbound : ∀ x, |manufacturedCharge V x| ≤ rho / 2)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (x : Position) :
    0 < homotopyDensity rho V t x :=
  (by positivity : (0 : ℝ) < rho / 2).trans_le
    (homotopyDensity_bounds V hbound ht0 ht1 x).1

theorem homotopyDensity_endpoints (rho : ℝ) (V : Position → ℝ) (x : Position) :
    homotopyDensity rho V 0 x = rho ∧
      homotopyDensity rho V 1 x = rho + manufacturedCharge V x := by
  simp only [homotopyDensity, zero_mul, one_mul, add_zero, and_self]

theorem homotopyDensity_time_deriv (rho : ℝ) (V : Position → ℝ) (t : ℝ) (x : Position) :
    deriv (fun s => homotopyDensity rho V s x) t = manufacturedCharge V x := by
  simpa only [homotopyDensity, one_mul, id_eq] using
    ((hasDerivAt_id t).mul_const (manufacturedCharge V x)).const_add rho |>.deriv

theorem moser_flux (rho : ℝ) (V : Position → ℝ) (t : ℝ) (x : Position)
    (hpos : homotopyDensity rho V t x ≠ 0) (a : Fin 3) :
    homotopyDensity rho V t x * moserVelocity rho V t x a =
      -(dirPartial V (axis a) x) / (4 * Real.pi) := by
  change homotopyDensity rho V t x *
    (-(dirPartial V (axis a) x) / (4 * Real.pi * homotopyDensity rho V t x)) = _
  field_simp [hpos]

/-- The continuity equation holds as an exact identity before any use of
flow transport or a numerical approximation to the flow. -/
theorem moser_continuity_equation {rho : ℝ} (hrho : 0 < rho)
    (V : Position → ℝ) (hV : ContDiff ℝ 2 V)
    (hbound : ∀ x, |manufacturedCharge V x| ≤ rho / 2)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (x : Position) :
    deriv (fun s => homotopyDensity rho V s x) t +
      (∑ a : Fin 3, dirPartial
        (fun y => homotopyDensity rho V t y * moserVelocity rho V t y a) (axis a) x) = 0 := by
  have hflux (a : Fin 3) :
      (fun y => homotopyDensity rho V t y * moserVelocity rho V t y a) =
      (fun y => -(4 * Real.pi)⁻¹ * dirPartial V (axis a) y) := by
    funext y
    rw [moser_flux rho V t y (homotopyDensity_pos hrho V hbound ht0 ht1 y).ne' a]
    ring
  have hp (a : Fin 3) : Differentiable ℝ (dirPartial V (axis a)) :=
    ((hV.fderiv_right (show (1 : WithTop ℕ∞) + 1 ≤ 2 by norm_num)).clm_apply
      contDiff_const).differentiable (by norm_num)
  rw [homotopyDensity_time_deriv]
  simp_rw [hflux]
  have hpartial (a : Fin 3) :
      dirPartial (fun y => -(4 * Real.pi)⁻¹ * dirPartial V (axis a) y) (axis a) x =
      -(4 * Real.pi)⁻¹ * dirPartial (dirPartial V (axis a)) (axis a) x := by
    change (fderiv ℝ (fun y => -(4 * Real.pi)⁻¹ * dirPartial V (axis a) y) x) (axis a) = _
    rw [fderiv_const_mul (hp a x)]
    rfl
  simp_rw [hpartial]
  rw [← Finset.mul_sum, ← NeutralAtom.coordinateLaplacian_eq_partials hV.contDiffAt]
  dsimp [manufacturedCharge]
  ring

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Nuclei_MoserRegularity
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite C⁶ regularity of the manufactured well gives the C⁴ transport
field required by the unit-charge cubature. No C∞ assumption is added. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb
open NeutralAtom (dirPartial coordinateLaplacian axis)

theorem manufacturedCharge_C4 (V : Position → ℝ) (hV : ContDiff ℝ 6 V) :
    ContDiff ℝ 4 (manufacturedCharge V) := by
  have hp (v : Position) : ContDiff ℝ 5 (dirPartial V v) :=
    (hV.fderiv_right (show (5 : WithTop ℕ∞) + 1 ≤ 6 by norm_num)).clm_apply contDiff_const
  have hpp (v : Position) : ContDiff ℝ 4 (dirPartial (dirPartial V v) v) :=
    ((hp v).fderiv_right (show (4 : WithTop ℕ∞) + 1 ≤ 5 by norm_num)).clm_apply contDiff_const
  have heq : coordinateLaplacian V = fun x =>
      ∑ a : Fin 3, dirPartial (dirPartial V (axis a)) (axis a) x :=
    funext (fun _ => NeutralAtom.coordinateLaplacian_eq_partials
      (hV.of_le (by norm_num : (2 : WithTop ℕ∞) ≤ 6)).contDiffAt)
  change ContDiff ℝ 4 (fun x => coordinateLaplacian V x / (4 * Real.pi))
  rw [heq]
  exact (ContDiff.sum (fun a _ => hpp (axis a))).div_const _

theorem homotopyDensity_joint_C4 (rho : ℝ) (V : Position → ℝ) (hV : ContDiff ℝ 6 V) :
    ContDiff ℝ 4 (fun p : ℝ × Position => homotopyDensity rho V p.1 p.2) :=
  contDiff_const.add (contDiff_fst.mul ((manufacturedCharge_C4 V hV).comp contDiff_snd))

theorem moserDomain_isOpen (rho : ℝ) (V : Position → ℝ) (hV : ContDiff ℝ 6 V) :
    IsOpen (moserDomain rho V) :=
  isOpen_ne.preimage (homotopyDensity_joint_C4 rho V hV).continuous

theorem moserVelocity_joint_C4 (rho : ℝ) (V : Position → ℝ) (hV : ContDiff ℝ 6 V) :
    ContDiffOn ℝ 4 (fun p : ℝ × Position => moserVelocity rho V p.1 p.2)
      (moserDomain rho V) := by
  apply (contDiffOn_piLp 2).mpr
  intro a
  have hp : ContDiff ℝ 4 (dirPartial V (axis a)) :=
    ((hV.fderiv_right (show (4 : WithTop ℕ∞) + 1 ≤ 6 by norm_num)).clm_apply contDiff_const)
  have hden : ContDiffOn ℝ 4
      (fun p : ℝ × Position => 4 * Real.pi * homotopyDensity rho V p.1 p.2)
      (moserDomain rho V) :=
    (contDiff_const.mul (homotopyDensity_joint_C4 rho V hV)).contDiffOn
  exact (hp.comp contDiff_snd).neg.contDiffOn.div hden (fun p hp =>
    mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero) hp)

theorem moserDomain_contains_time_slab {rho : ℝ} (hrho : 0 < rho)
    (V : Position → ℝ) (hbound : ∀ x, |manufacturedCharge V x| ≤ rho / 2) :
    Set.Icc (0 : ℝ) 1 ×ˢ (Set.univ : Set Position) ⊆ moserDomain rho V := by
  intro p hp
  exact (homotopyDensity_pos hrho V hbound hp.1.1 hp.1.2 p.2).ne'

/-- Actual spatial C⁴ regularity at each transport time, sufficient for
four differentiated flow equations and fourth-order cubature composition. -/
theorem moserVelocity_C4 {rho : ℝ} (hrho : 0 < rho)
    (V : Position → ℝ) (hV : ContDiff ℝ 6 V)
    (hbound : ∀ x, |manufacturedCharge V x| ≤ rho / 2)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : ContDiff ℝ 4 (moserVelocity rho V t) := by
  apply (contDiff_piLp 2).mpr
  intro a
  have hp : ContDiff ℝ 4 (dirPartial V (axis a)) :=
    ((hV.fderiv_right (show (4 : WithTop ℕ∞) + 1 ≤ 6 by norm_num)).clm_apply contDiff_const)
  have hdensity : ContDiff ℝ 4 (homotopyDensity rho V t) :=
    contDiff_const.add (contDiff_const.mul (manufacturedCharge_C4 V hV))
  exact hp.neg.div (contDiff_const.mul hdensity) (fun x =>
    mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero)
      (homotopyDensity_pos hrho V hbound ht0 ht1 x).ne')

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Nuclei_MoserInverse
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Backward stability gives the separation bound required for mapped
quadrature nodes. Compactly supported motion also preserves the enclosing slab. -/

noncomputable section
open scoped Topology NNReal
namespace ContinuumCoulomb

theorem moser_time_one_preserves_slab (V : Position → ℝ) {H S : ℝ}
    (hsupport : tsupport V ⊆ slabDomain H S) (G : Position → Position)
    (hbij : Function.Bijective G) (hfix : ∀ x, x ∉ tsupport V → G x = x) :
    G '' slabDomain H S = slabDomain H S := by
  apply Set.Subset.antisymm
  · rintro y ⟨x, hx, rfl⟩
    by_contra hy
    have hn : G x ∉ tsupport V := fun h => hy (hsupport h)
    have heq : x = G x := hbij.1 (hfix (G x) hn).symm
    exact hy (heq ▸ hx)
  · intro y hy
    obtain ⟨x, rfl⟩ := hbij.2 y
    refine ⟨x, ?_, rfl⟩
    by_contra hx
    have hn : x ∉ tsupport V := fun h => hx (hsupport h)
    exact hx ((hfix x hn) ▸ hy)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Nuclei_GaussEightNodes
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Identify tensor quadrature with the actual eight equal point masses and
with the already separated Gauss lattice used by the nuclear construction. -/

noncomputable section
open scoped BigOperators
namespace ContinuumCoulomb

theorem gaussTensor3_eq_node_sum (f : ℝ → ℝ → ℝ → ℝ) :
    gaussTwoPoint (fun x => gaussTwoPoint (fun y => gaussTwoPoint (f x y))) =
      ∑ v : Fin 3 → Fin 2, f (gaussNode (v 0)) (gaussNode (v 1)) (gaussNode (v 2)) := by
  have h := Fintype.sum_equiv gaussNodeTriple
    (fun v => f (gaussNode (v 0)) (gaussNode (v 1)) (gaussNode (v 2)))
    (fun p => f (gaussNode p.1) (gaussNode p.2.1) (gaussNode p.2.2)) (fun _ => rfl)
  rw [h]
  simp only [Fintype.sum_prod_type,Fin.sum_univ_two,gaussNode,Fin.isValue,ite_true, if_true]
  rfl

theorem positionCellGauss_eq_node_sum (b : Position) (h : ℝ) (f : Position → ℝ) :
    positionCellGauss b h f = (h^3/8)*∑ v : Fin 3 → Fin 2,
      f (cubePoint b (h/2) (gaussNode (v 0)) (gaussNode (v 1)) (gaussNode (v 2))) := by
  rw [positionCellGauss,gaussTensor3_eq_node_sum]
  congr 1
  ring

theorem cubePoint_gaussLatticePoint (h : ℝ) (k : Fin 3 → ℤ) (v : Fin 3 → Fin 2) :
    cubePoint (gaussCellCenter h k) (h/2) (gaussNode (v 0)) (gaussNode (v 1)) (gaussNode (v 2)) =
      gaussLatticePoint h (k,v) := by
  ext i
  fin_cases i <;> simp [cubePoint,gaussCellCenter,gaussLatticePoint] <;> ring

theorem gaussCell_quadrature_lattice (h : ℝ) (k : Fin 3 → ℤ) (f : Position → ℝ) :
    positionCellGauss (gaussCellCenter h k) h f =
      (h^3/8)*∑ v : Fin 3 → Fin 2, f (gaussLatticePoint h (k,v)) := by
  rw [positionCellGauss_eq_node_sum]
  simp only [cubePoint_gaussLatticePoint]

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Nuclei_GaussLocal
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Local versions of tensor cubature: regularity is only needed on the
integration cube, which may be far from a Coulomb singularity. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

theorem unitClamp_mem (x : ℝ) : unitClamp x ∈ Set.Icc (-1:ℝ) 1 := by
  constructor
  · exact le_max_left _ _
  · exact max_le (by norm_num) (min_le_left _ _)

theorem unitClamp_eq {x : ℝ} (hx : x ∈ Set.Icc (-1:ℝ) 1) : unitClamp x = x := by
  simp only [unitClamp,min_eq_right hx.2,max_eq_right hx.1]

theorem unitClamp_continuous : Continuous unitClamp :=
  continuous_const.max (continuous_const.min continuous_id)

theorem gaussTwoPoint_congr_on {f g : ℝ → ℝ}
    (h : Set.EqOn f g (Set.Icc (-1:ℝ) 1)) : gaussTwoPoint f = gaussTwoPoint g := by
  have ha : gaussAbscissa ≤ 1 := by nlinarith only [gaussAbscissa_sq,gaussAbscissa_pos]
  have hp := gaussAbscissa_pos.le
  unfold gaussTwoPoint
  rw [h (x := -gaussAbscissa) ⟨by linarith,by linarith⟩,
    h (x := gaussAbscissa) ⟨by linarith,ha⟩]

theorem unitInterval_integral_congr {f g : ℝ → ℝ}
    (h : Set.EqOn f g (Set.Icc (-1:ℝ) 1)) :
    (∫ x : ℝ in (-1)..1, f x) = ∫ x : ℝ in (-1)..1, g x := by
  apply intervalIntegral.integral_congr
  simpa only [Set.uIcc_of_le (by norm_num : (-1:ℝ) ≤ 1)] using h

theorem gaussTensor3_congr_on {f g : ℝ → ℝ → ℝ → ℝ}
    (h : ∀ x ∈ Set.Icc (-1:ℝ) 1, ∀ y ∈ Set.Icc (-1:ℝ) 1,
      ∀ z ∈ Set.Icc (-1:ℝ) 1, f x y z = g x y z) :
    gaussTwoPoint (fun x => gaussTwoPoint (fun y => gaussTwoPoint (f x y))) =
      gaussTwoPoint (fun x => gaussTwoPoint (fun y => gaussTwoPoint (g x y))) := by
  apply gaussTwoPoint_congr_on
  intro x hx
  apply gaussTwoPoint_congr_on
  intro y hy
  exact gaussTwoPoint_congr_on (h x hx y hy)

theorem unitCube_integral_congr {f g : ℝ → ℝ → ℝ → ℝ}
    (h : ∀ x ∈ Set.Icc (-1:ℝ) 1, ∀ y ∈ Set.Icc (-1:ℝ) 1,
      ∀ z ∈ Set.Icc (-1:ℝ) 1, f x y z = g x y z) :
    (∫ x : ℝ in (-1)..1, ∫ y : ℝ in (-1)..1, ∫ z : ℝ in (-1)..1, f x y z) =
      ∫ x : ℝ in (-1)..1, ∫ y : ℝ in (-1)..1, ∫ z : ℝ in (-1)..1, g x y z := by
  apply unitInterval_integral_congr
  intro x hx
  apply unitInterval_integral_congr
  intro y hy
  exact unitInterval_integral_congr (h x hx y hy)

theorem gaussTensor3_error_on_cube (f : ℝ → ℝ → ℝ → ℝ)
    (hf : ContinuousOn (fun p : ℝ × ℝ × ℝ => f p.1 p.2.1 p.2.2) unitCube3) {E : ℝ}
    (hx : ∀ y ∈ Set.Icc (-1) 1, ∀ z ∈ Set.Icc (-1) 1,
      |gaussTwoPoint (fun x => f x y z)-(∫ x : ℝ in (-1)..1, f x y z)| ≤ E)
    (hy : ∀ x ∈ Set.Icc (-1) 1, ∀ z ∈ Set.Icc (-1) 1,
      |gaussTwoPoint (fun y => f x y z)-(∫ y : ℝ in (-1)..1, f x y z)| ≤ E)
    (hz : ∀ x ∈ Set.Icc (-1) 1, ∀ y ∈ Set.Icc (-1) 1,
      |gaussTwoPoint (f x y)-(∫ z : ℝ in (-1)..1, f x y z)| ≤ E) :
    |gaussTwoPoint (fun x => gaussTwoPoint (fun y => gaussTwoPoint (f x y)))-
      (∫ x : ℝ in (-1)..1, ∫ y : ℝ in (-1)..1, ∫ z : ℝ in (-1)..1, f x y z)| ≤ 12*E := by
  let g : ℝ → ℝ → ℝ → ℝ := fun x y z => f (unitClamp x) (unitClamp y) (unitClamp z)
  have hg : Continuous (fun p : ℝ × ℝ × ℝ => g p.1 p.2.1 p.2.2) :=
    hf.comp_continuous
      ((unitClamp_continuous.comp continuous_fst).prodMk
        ((unitClamp_continuous.comp (continuous_fst.comp continuous_snd)).prodMk
          (unitClamp_continuous.comp (continuous_snd.comp continuous_snd))))
      (fun p => ⟨unitClamp_mem p.1,unitClamp_mem p.2.1,unitClamp_mem p.2.2⟩)
  have heq : ∀ x ∈ Set.Icc (-1:ℝ) 1, ∀ y ∈ Set.Icc (-1:ℝ) 1,
      ∀ z ∈ Set.Icc (-1:ℝ) 1, g x y z = f x y z := by
    intro x hx y hy z hz
    simp only [g,unitClamp_eq hx,unitClamp_eq hy,unitClamp_eq hz]
  have hxe : ∀ y ∈ Set.Icc (-1) 1, ∀ z ∈ Set.Icc (-1) 1,
      |gaussTwoPoint (fun x => g x y z)-(∫ x : ℝ in (-1)..1, g x y z)| ≤ E := by
    intro y hy z hz
    have he : Set.EqOn (fun x => g x y z) (fun x => f x y z) (Set.Icc (-1:ℝ) 1) :=
      fun x hx => heq x hx y hy z hz
    rw [gaussTwoPoint_congr_on he,unitInterval_integral_congr he]
    exact hx y hy z hz
  have hye : ∀ x ∈ Set.Icc (-1) 1, ∀ z ∈ Set.Icc (-1) 1,
      |gaussTwoPoint (fun y => g x y z)-(∫ y : ℝ in (-1)..1, g x y z)| ≤ E := by
    intro x hx z hz
    have he : Set.EqOn (fun y => g x y z) (fun y => f x y z) (Set.Icc (-1:ℝ) 1) :=
      fun y hy => heq x hx y hy z hz
    rw [gaussTwoPoint_congr_on he,unitInterval_integral_congr he]
    exact hy x hx z hz
  have hze : ∀ x ∈ Set.Icc (-1) 1, ∀ y ∈ Set.Icc (-1) 1,
      |gaussTwoPoint (g x y)-(∫ z : ℝ in (-1)..1, g x y z)| ≤ E := by
    intro x hx y hy
    have he : Set.EqOn (g x y) (f x y) (Set.Icc (-1:ℝ) 1) :=
      fun z hz => heq x hx y hy z hz
    rw [gaussTwoPoint_congr_on he,unitInterval_integral_congr he]
    exact hz x hx y hy
  have he := gaussTensor3_error g hg hxe hye hze
  rw [gaussTensor3_congr_on heq,unitCube_integral_congr heq] at he
  exact he

theorem gaussTensor3_C4_error_on_cube (f : ℝ → ℝ → ℝ → ℝ)
    (hf : ContinuousOn (fun p : ℝ × ℝ × ℝ => f p.1 p.2.1 p.2.2) unitCube3) {C : ℝ} (hC : 0 ≤ C)
    (hfx : ∀ y ∈ Set.Icc (-1) 1, ∀ z ∈ Set.Icc (-1) 1,
      ContDiffOn ℝ 4 (fun x => f x y z) (Set.Icc (-1) 1))
    (hfy : ∀ x ∈ Set.Icc (-1) 1, ∀ z ∈ Set.Icc (-1) 1,
      ContDiffOn ℝ 4 (fun y => f x y z) (Set.Icc (-1) 1))
    (hfz : ∀ x ∈ Set.Icc (-1) 1, ∀ y ∈ Set.Icc (-1) 1,
      ContDiffOn ℝ 4 (f x y) (Set.Icc (-1) 1))
    (hCx : ∀ y ∈ Set.Icc (-1) 1, ∀ z ∈ Set.Icc (-1) 1, ∀ x ∈ Set.Icc (-1) 1,
      ‖iteratedDerivWithin 4 (fun x => f x y z) (Set.Icc (-1) 1) x‖ ≤ C)
    (hCy : ∀ x ∈ Set.Icc (-1) 1, ∀ z ∈ Set.Icc (-1) 1, ∀ y ∈ Set.Icc (-1) 1,
      ‖iteratedDerivWithin 4 (fun y => f x y z) (Set.Icc (-1) 1) y‖ ≤ C)
    (hCz : ∀ x ∈ Set.Icc (-1) 1, ∀ y ∈ Set.Icc (-1) 1, ∀ z ∈ Set.Icc (-1) 1,
      ‖iteratedDerivWithin 4 (f x y) (Set.Icc (-1) 1) z‖ ≤ C) :
    |gaussTwoPoint (fun x => gaussTwoPoint (fun y => gaussTwoPoint (f x y)))-
      (∫ x : ℝ in (-1)..1, ∫ y : ℝ in (-1)..1, ∫ z : ℝ in (-1)..1, f x y z)| ≤ 128*C := by
  have h := gaussTensor3_error_on_cube f hf
    (fun y hy z hz => gaussTwoPoint_C4_error _ hC (hfx y hy z hz) (hCx y hy z hz))
    (fun x hx z hz => gaussTwoPoint_C4_error _ hC (hfy x hx z hz) (hCy x hx z hz))
    (fun x hx y hy => gaussTwoPoint_C4_error _ hC (hfz x hx y hy) (hCz x hx y hy))
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  ring


end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Nuclei_GaussLocalPositionCell
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The cell estimate requires smoothness only near the cell. -/
noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

private theorem fourthDerivWithin_line_bound_local (f : Position → ℝ) (b v : Position) (t : ℝ)
    (hf : ContDiffAt ℝ 4 f (b+t • v)) (ht : t ∈ Set.Icc (-1:ℝ) 1) :
    ‖iteratedDerivWithin 4 (fun s : ℝ => f (b+s • v)) (Set.Icc (-1) 1) t‖ ≤
      ‖iteratedFDeriv ℝ 4 f (b+t • v)‖*‖v‖^4 := by
  have hline : ContDiffAt ℝ 4 (fun s : ℝ => f (b+s • v)) t :=
    hf.comp t (show ContDiffAt ℝ 4 (fun s : ℝ => b+s • v) t by fun_prop)
  rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc (by norm_num))
    hline ht,Real.norm_eq_abs]
  exact fourthDeriv_affine_line_bound f b v t hf

private theorem cube_axis_fourth_bound_local (f : Position → ℝ) (b v : Position) (t d C : ℝ)
    (hf : ContDiffAt ℝ 4 f (b+t • v)) (ht : t ∈ Set.Icc (-1:ℝ) 1)
    (hD : ‖iteratedFDeriv ℝ 4 f (b+t • v)‖ ≤ C) (hv : ‖v‖ = d) :
    ‖iteratedDerivWithin 4 (fun s : ℝ => f (b+s • v)) (Set.Icc (-1) 1) t‖ ≤ C*d^4 := by
  apply (fourthDerivWithin_line_bound_local f b v t hf ht).trans
  rw [hv]
  exact mul_le_mul_of_nonneg_right hD (pow_nonneg (norm_nonneg v |>.trans_eq hv) _)

theorem positionCellGauss_error_local (f : Position → ℝ) (b : Position) {h C : ℝ} (hh : 0 ≤ h) (hC : 0 ≤ C)
    (hf : ∀ x ∈ Set.Icc (-1:ℝ) 1, ∀ y ∈ Set.Icc (-1:ℝ) 1,
      ∀ z ∈ Set.Icc (-1:ℝ) 1, ContDiffAt ℝ 4 f (cubePoint b (h/2) x y z))
    (hD : ∀ x ∈ Set.Icc (-1:ℝ) 1, ∀ y ∈ Set.Icc (-1:ℝ) 1,
      ∀ z ∈ Set.Icc (-1:ℝ) 1,
      ‖iteratedFDeriv ℝ 4 f (cubePoint b (h/2) x y z)‖ ≤ C) :
    |positionCellGauss b h f-positionCellIntegral b h f| ≤ C*h^7 := by
  let d := h/2
  have hd : 0 ≤ d := by dsimp [d]; positivity
  have hv (i : Fin 3) : ‖d • (EuclideanSpace.single i 1 : Position)‖ = d := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hd,PiLp.norm_single]
    norm_num
  have hxline (x y z : ℝ) : cubePoint b d x y z =
      (b+y • (d • EuclideanSpace.single 1 1)+z • (d • EuclideanSpace.single 2 1))+
      x • (d • EuclideanSpace.single 0 1) := by unfold cubePoint; module
  have hyline (x y z : ℝ) : cubePoint b d x y z =
      (b+x • (d • EuclideanSpace.single 0 1)+z • (d • EuclideanSpace.single 2 1))+
      y • (d • EuclideanSpace.single 1 1) := by unfold cubePoint; module
  have hzline (x y z : ℝ) : cubePoint b d x y z =
      (b+x • (d • EuclideanSpace.single 0 1)+y • (d • EuclideanSpace.single 1 1))+
      z • (d • EuclideanSpace.single 2 1) := rfl
  have hc : ContinuousOn (fun p : ℝ × ℝ × ℝ => f (cubePoint b d p.1 p.2.1 p.2.2)) unitCube3 := by
    intro p hp
    exact (ContinuousAt.comp (f := fun q : ℝ × ℝ × ℝ => cubePoint b d q.1 q.2.1 q.2.2)
      (hf p.1 hp.1 p.2.1 hp.2.1 p.2.2 hp.2.2).continuousAt
      (cubePoint_contDiff b d).continuous.continuousAt).continuousWithinAt
  have hfx (y : ℝ) (hy : y ∈ Set.Icc (-1:ℝ) 1) (z : ℝ) (hz : z ∈ Set.Icc (-1:ℝ) 1) :
      ContDiffOn ℝ 4 (fun x => f (cubePoint b d x y z)) (Set.Icc (-1) 1) := by
    intro x hx
    exact ((hf x hx y hy z hz).comp x
      (show ContDiffAt ℝ 4 (fun x => cubePoint b d x y z) x by unfold cubePoint; fun_prop)).contDiffWithinAt
  have hfy (x : ℝ) (hx : x ∈ Set.Icc (-1:ℝ) 1) (z : ℝ) (hz : z ∈ Set.Icc (-1:ℝ) 1) :
      ContDiffOn ℝ 4 (fun y => f (cubePoint b d x y z)) (Set.Icc (-1) 1) := by
    intro y hy
    exact ((hf x hx y hy z hz).comp y
      (show ContDiffAt ℝ 4 (fun y => cubePoint b d x y z) y by unfold cubePoint; fun_prop)).contDiffWithinAt
  have hfz (x : ℝ) (hx : x ∈ Set.Icc (-1:ℝ) 1) (y : ℝ) (hy : y ∈ Set.Icc (-1:ℝ) 1) :
      ContDiffOn ℝ 4 (fun z => f (cubePoint b d x y z)) (Set.Icc (-1) 1) := by
    intro z hz
    exact ((hf x hx y hy z hz).comp z
      (show ContDiffAt ℝ 4 (fun z => cubePoint b d x y z) z by unfold cubePoint; fun_prop)).contDiffWithinAt
  have hDx (y : ℝ) (hy : y ∈ Set.Icc (-1:ℝ) 1) (z : ℝ) (hz : z ∈ Set.Icc (-1:ℝ) 1)
      (x : ℝ) (hx : x ∈ Set.Icc (-1:ℝ) 1) :
      ‖iteratedDerivWithin 4 (fun x => f (cubePoint b d x y z)) (Set.Icc (-1) 1) x‖ ≤ C*d^4 := by
    simp_rw [hxline]
    exact cube_axis_fourth_bound_local f _ _ x d C (by rw [← hxline]; exact hf x hx y hy z hz) hx
      (by rw [← hxline]; exact hD x hx y hy z hz) (hv 0)
  have hDy (x : ℝ) (hx : x ∈ Set.Icc (-1:ℝ) 1) (z : ℝ) (hz : z ∈ Set.Icc (-1:ℝ) 1)
      (y : ℝ) (hy : y ∈ Set.Icc (-1:ℝ) 1) :
      ‖iteratedDerivWithin 4 (fun y => f (cubePoint b d x y z)) (Set.Icc (-1) 1) y‖ ≤ C*d^4 := by
    simp_rw [hyline]
    exact cube_axis_fourth_bound_local f _ _ y d C (by rw [← hyline]; exact hf x hx y hy z hz) hy
      (by rw [← hyline]; exact hD x hx y hy z hz) (hv 1)
  have hDz (x : ℝ) (hx : x ∈ Set.Icc (-1:ℝ) 1) (y : ℝ) (hy : y ∈ Set.Icc (-1:ℝ) 1)
      (z : ℝ) (hz : z ∈ Set.Icc (-1:ℝ) 1) :
      ‖iteratedDerivWithin 4 (fun z => f (cubePoint b d x y z)) (Set.Icc (-1) 1) z‖ ≤ C*d^4 := by
    simp_rw [hzline]
    exact cube_axis_fourth_bound_local f _ _ z d C (by rw [← hzline]; exact hf x hx y hy z hz) hz
      (by rw [← hzline]; exact hD x hx y hy z hz) (hv 2)
  have he := gaussTensor3_C4_error_on_cube (fun x y z => f (cubePoint b d x y z)) hc
    (mul_nonneg hC (pow_nonneg hd 4))
    hfx
    hfy
    hfz hDx hDy hDz
  change |d^3*_ - d^3*_| ≤ _
  rw [← mul_sub,abs_mul,abs_of_nonneg (pow_nonneg hd 3)]
  apply (mul_le_mul_of_nonneg_left he (pow_nonneg hd 3)).trans_eq
  dsimp [d]
  ring


end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Nuclei_MoserFlowRegularity
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite-dimensional flow regularity for the Moser trajectories. -/

noncomputable section
open scoped BigOperators NNReal
namespace ContinuumCoulomb

theorem moser_flow_C4 (hpublished : PublishedC4FlowInput) {rho : ℝ} (hrho : 0 < rho)
    (V : Position → ℝ) (hV : ContDiff ℝ 6 V)
    (hbound : ∀ x, |manufacturedCharge V x| ≤ rho/2)
    (G : Position → ℝ → Position) (hG : IsUnitTimeFlow (moserVelocity rho V) G) :
    (∀ t ∈ Set.Icc (0 : ℝ) 1, ContDiff ℝ 4 (fun x => G x t)) ∧
      (∀ x t, t ∈ Set.Icc (0 : ℝ) 1 →
        HasDerivWithinAt (fun s => flowJacobian G s x)
          (fieldDivergence (moserVelocity rho V t) (G x t) * flowJacobian G t x)
          (Set.Icc (0 : ℝ) 1) t) :=
  hpublished.regularity (moserDomain rho V) (moserDomain_isOpen rho V hV)
    (moserDomain_contains_time_slab hrho V hbound) (moserVelocity rho V)
    (moserVelocity_joint_C4 rho V hV) G hG

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Nuclei_MoserJacobian
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The continuity equation yields the density-Jacobian identity along the
flow. The proof uses finite-dimensional ODE regularity. -/

noncomputable section
open scoped BigOperators
namespace ContinuumCoulomb
open NeutralAtom (dirPartial axis)

private theorem linear_apply_coordinates (L : Position →L[ℝ] ℝ) (v : Position) :
    L v = ∑ a : Fin 3, v a * L (axis a) := by
  have he : v = ∑ a : Fin 3, v a • axis a := by
    ext b
    simp [axis, Pi.single_apply]
  calc
    L v = L (∑ a : Fin 3, v a • axis a) := congrArg L he
    _ = _ := by simp only [map_sum, map_smul, smul_eq_mul]

private theorem divergence_scalar_mul (f : Position → ℝ) (v : Position → Position)
    (hf : Differentiable ℝ f) (hv : Differentiable ℝ v) (x : Position) :
    (∑ a : Fin 3, dirPartial (fun y => f y * v y a) (axis a) x) =
      fderiv ℝ f x (v x) + f x * fieldDivergence v x := by
  have hcoord (a : Fin 3) : Differentiable ℝ (fun y => v y a) := by
    intro y
    exact ((PiLp.hasFDerivAt_apply 2 (v y) a).comp y (hv y).hasFDerivAt).differentiableAt
  have hp (a : Fin 3) : dirPartial (fun y => f y * v y a) (axis a) x =
      v x a * dirPartial f (axis a) x + f x * dirPartial (fun y => v y a) (axis a) x := by
    unfold dirPartial
    rw [fderiv_fun_mul (hf x) (hcoord a x)]
    simp only [add_apply, smul_apply, smul_eq_mul]
    ring
  simp_rw [hp]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum,
    linear_apply_coordinates (fderiv ℝ f x) (v x)]
  rfl

theorem moser_continuity_expanded {rho : ℝ} (hrho : 0 < rho)
    (V : Position → ℝ) (hV : ContDiff ℝ 6 V)
    (hbound : ∀ x, |manufacturedCharge V x| ≤ rho/2)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) (x : Position) :
    manufacturedCharge V x +
      t * fderiv ℝ (manufacturedCharge V) x (moserVelocity rho V t x) +
      homotopyDensity rho V t x * fieldDivergence (moserVelocity rho V t) x = 0 := by
  have hσ : Differentiable ℝ (manufacturedCharge V) :=
    (manufacturedCharge_C4 V hV).differentiable (by norm_num)
  have hρc : ContDiff ℝ 4 (homotopyDensity rho V t) :=
    contDiff_const.add (contDiff_const.mul (manufacturedCharge_C4 V hV))
  have hρ : Differentiable ℝ (homotopyDensity rho V t) :=
    hρc.differentiable (by norm_num)
  have hv := (moserVelocity_C4 hrho V hV hbound ht.1 ht.2).differentiable (by norm_num)
  have h := moser_continuity_equation hrho V (hV.of_le (by norm_num)) hbound ht.1 ht.2 x
  rw [homotopyDensity_time_deriv, divergence_scalar_mul _ _ hρ hv] at h
  have hd : fderiv ℝ (homotopyDensity rho V t) x = t • fderiv ℝ (manufacturedCharge V) x := by
    unfold homotopyDensity
    rw [fderiv_const_add, fderiv_const_mul (hσ x)]
  rw [hd, smul_apply, smul_eq_mul] at h
  simpa only [add_assoc] using h

theorem flowJacobian_zero (G : Position → ℝ → Position) (hG : ∀ x, G x 0 = x)
    (x : Position) : flowJacobian G 0 x = 1 := by
  have he : (fun y => G y 0) = id := funext hG
  simp [flowJacobian, he, ContinuousLinearMap.det]

/-- Density times the determinant of the actual flow derivative is exactly
constant, including the endpoint used by cubature. -/
theorem moser_density_jacobian (hpublished : PublishedC4FlowInput)
    {rho : ℝ} (hrho : 0 < rho) (V : Position → ℝ) (hV : ContDiff ℝ 6 V)
    (hbound : ∀ x, |manufacturedCharge V x| ≤ rho/2)
    (G : Position → ℝ → Position) (hG : IsUnitTimeFlow (moserVelocity rho V) G)
    (x : Position) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    homotopyDensity rho V t (G x t) * flowJacobian G t x = rho := by
  have hJ := (moser_flow_C4 hpublished hrho V hV hbound G hG).2
  let P : ℝ → ℝ := fun s => homotopyDensity rho V s (G x s) * flowJacobian G s x
  have hσ : Differentiable ℝ (manufacturedCharge V) :=
    (manufacturedCharge_C4 V hV).differentiable (by norm_num)
  have hP (s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) 1) :
      HasDerivWithinAt P 0 (Set.Icc (0 : ℝ) 1) s := by
    have hσG := (hσ (G x s)).hasFDerivAt.comp_hasDerivWithinAt s (hG.2 x s hs)
    have hρG := (((hasDerivAt_id s).hasDerivWithinAt.mul hσG).const_add rho)
    have hmul := hρG.mul (hJ x s hs)
    have hzero := moser_continuity_expanded hrho V hV hbound hs (G x s)
    convert hmul using 1 <;> first | rfl | (
      simp only [id_eq, one_mul, Function.comp_apply, Pi.mul_apply]
      dsimp only [homotopyDensity] at hzero ⊢
      linear_combination -(flowJacobian G s x) * hzero)
  have hn := norm_image_sub_le_of_norm_deriv_le_segment' hP
    (fun _ _ => (by simp : ‖(0 : ℝ)‖ ≤ 0)) t ht
  have he : P t = P 0 := by simpa only [zero_mul, norm_le_zero_iff, sub_eq_zero] using hn
  simpa only [P, (homotopyDensity_endpoints rho V (G x 0)).1,
    flowJacobian_zero G hG.1 x, mul_one] using he

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Nuclei_MoserTransport
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact change of variables from uniform slab density to the actual
manufactured density. The identity is for arbitrary scalar integrands,
including the Coulomb kernel used by the nuclear cubature. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

theorem moser_flowJacobian_pos (hpublished : PublishedC4FlowInput)
    {rho : ℝ} (hrho : 0 < rho) (V : Position → ℝ) (hV : ContDiff ℝ 6 V)
    (hbound : ∀ x, |manufacturedCharge V x| ≤ rho/2)
    (G : Position → ℝ → Position) (hG : IsUnitTimeFlow (moserVelocity rho V) G)
    (x : Position) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    0 < flowJacobian G t x := by
  have he := moser_density_jacobian hpublished hrho V hV hbound G hG x ht
  have hp : 0 < homotopyDensity rho V t (G x t) :=
    homotopyDensity_pos hrho V hbound ht.1 ht.2 _
  have hm : 0 < homotopyDensity rho V t (G x t) * flowJacobian G t x := by
    rw [he]
    exact hrho
  rcases mul_pos_iff.mp hm with h | h
  · exact h.2
  · exact False.elim (not_lt_of_ge hp.le h.1)

/-- The actual Moser map pushes uniform density to the synthesized
nonnegative nuclear density, with the entire slab preserved. -/
theorem moser_density_integral (hpublished : PublishedC4FlowInput)
    {rho H S : ℝ} (hrho : 0 < rho) (V : Position → ℝ) (hV : ContDiff ℝ 6 V)
    (hbound : ∀ x, |manufacturedCharge V x| ≤ rho/2)
    (hsupport : tsupport V ⊆ slabDomain H S)
    (G : Position → ℝ → Position) (hG : IsUnitTimeFlow (moserVelocity rho V) G)
    (hbij : Function.Bijective (fun x => G x 1))
    (hfix : ∀ x, x ∉ tsupport V → G x 1 = x) (f : Position → ℝ) :
    (∫ y in slabDomain H S, synthesizedDensity rho H S V y * f y) =
      rho * ∫ x in slabDomain H S, f (G x 1) := by
  have hs := (slabDomain_isClosed H S).measurableSet
  have h1 : (1 : ℝ) ∈ Set.Icc 0 1 := ⟨by norm_num, le_rfl⟩
  have hreg := (moser_flow_C4 hpublished hrho V hV hbound G hG).1 1 h1
  have himage := moser_time_one_preserves_slab V hsupport (fun x => G x 1) hbij hfix
  have hchange := integral_image_eq_integral_abs_det_fderiv_smul volume hs
    (fun x (_hx : x ∈ slabDomain H S) =>
      (hreg.differentiable (by norm_num) x).hasFDerivAt.hasFDerivWithinAt)
    hbij.1.injOn (fun y => synthesizedDensity rho H S V y * f y)
  rw [himage] at hchange
  rw [hchange, ← integral_const_mul]
  apply setIntegral_congr_fun hs
  intro x hx
  have hGx : G x 1 ∈ slabDomain H S := by
    rw [← himage]
    exact ⟨x, hx, rfl⟩
  have hJ := moser_density_jacobian hpublished hrho V hV hbound G hG x h1
  have hp := moser_flowJacobian_pos hpublished hrho V hV hbound G hG x h1
  change |flowJacobian G 1 x| * (synthesizedDensity rho H S V (G x 1) * f (G x 1)) = _
  rw [abs_of_pos hp]
  simp only [synthesizedDensity, slabDensity, Set.indicator_of_mem hGx] at hJ ⊢
  simp only [homotopyDensity, one_mul] at hJ
  calc
    flowJacobian G 1 x * ((rho + manufacturedCharge V (G x 1)) * f (G x 1)) =
      ((rho + manufacturedCharge V (G x 1)) * flowJacobian G 1 x) * f (G x 1) := by ring
    _ = rho * f (G x 1) := by rw [hJ]

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_CoulombInverseFifth
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The inverse-fifth-power tail is integrable in three dimensions, with the
exact inverse-square dependence needed when summing far-cell errors. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

private theorem inverseFifthRadial_weight {r : ℝ} (hr : 0 < r) (t : ℝ) :
    t^2*inverseFifthRadial r t = (Set.Ioi r).indicator (fun t => t^(-3:ℝ)) t := by
  by_cases ht : r < t
  · simp only [inverseFifthRadial,Set.indicator_of_mem (Set.mem_Ioi.mpr ht)]
    have hp : 0 < t := hr.trans ht
    rw [show (-3:ℝ) = 2+(-5) by norm_num,Real.rpow_add hp,Real.rpow_two]
  · simp [inverseFifthRadial,ht]

private theorem inverseFifthRadial_weight_integrable {r : ℝ} (hr : 0 < r) :
    IntegrableOn (fun t : ℝ => t^2*inverseFifthRadial r t) (Set.Ioi 0) := by
  have hi := integrableOn_Ioi_rpow_of_lt (by norm_num : (-3:ℝ) < -1) hr
  have h := (integrable_indicator_iff measurableSet_Ioi).mpr hi
  simpa only [inverseFifthRadial_weight hr] using h.integrableOn

private theorem inverseFifthRadial_weight_integral {r : ℝ} (hr : 0 < r) :
    (∫ t in Set.Ioi (0:ℝ), t^2*inverseFifthRadial r t) = 1/(2*r^2) := by
  simp_rw [inverseFifthRadial_weight hr]
  rw [integral_indicator measurableSet_Ioi,Measure.restrict_restrict measurableSet_Ioi,
    Set.Ioi_inter_Ioi,max_eq_left hr.le]
  have hi := integral_Ioi_rpow_of_lt (by norm_num : (-3:ℝ) < -1) hr
  convert hi using 1
  all_goals try with_reducible_and_instances rfl
  norm_num [Real.rpow_neg,Real.rpow_two]
  ring

theorem inverseFifthTail_integrable {r : ℝ} (hr : 0 < r) : Integrable (inverseFifthTail r) := by
  apply (integrable_fun_norm_addHaar (E := Position) volume (f := inverseFifthRadial r)).mpr
  simpa only [finrank_euclideanSpace_fin,Nat.reduceSub,smul_eq_mul] using
    inverseFifthRadial_weight_integrable hr

theorem inverseFifthTail_integral {r : ℝ} (hr : 0 < r) :
    (∫ x : Position, inverseFifthTail r x) = 2*Real.pi/r^2 := by
  change (∫ x : Position, inverseFifthRadial r ‖x‖) = _
  rw [integral_fun_norm_addHaar volume]
  simp only [finrank_euclideanSpace_fin,Nat.reduceSub,smul_eq_mul]
  rw [inverseFifthRadial_weight_integral hr]
  simp only [Measure.real,EuclideanSpace.volume_ball_fin_three,ENNReal.ofReal_one,one_pow,
    one_mul,ENNReal.toReal_ofReal (by positivity : 0 ≤ Real.pi*4/3),nsmul_eq_mul]
  norm_num [Position,finrank_euclideanSpace_fin]
  ring

theorem inverseFifthTail_of_gt {r : ℝ} (x : Position) (hx : r < ‖x‖) :
    inverseFifthTail r x = ‖x‖^(-5:ℝ) := by
  unfold inverseFifthTail inverseFifthRadial
  exact Set.indicator_of_mem (Set.mem_Ioi.mpr hx) _

theorem inverseFifthTail_nonneg (r : ℝ) (x : Position) : 0 ≤ inverseFifthTail r x := by
  by_cases hx : r < ‖x‖
  · rw [inverseFifthTail_of_gt x hx]
    exact Real.rpow_nonneg (norm_nonneg x) _
  · simp [inverseFifthTail,inverseFifthRadial,hx]

theorem inverseFifthTail_eq_inv_pow {r : ℝ} (x : Position) (hx : r < ‖x‖) :
    inverseFifthTail r x = 1/‖x‖^5 := by
  rw [inverseFifthTail_of_gt x hx]
  simp

theorem translatedInverseFifth_integrable (y : Position) {r : ℝ} (hr : 0 < r) :
    Integrable (fun x => inverseFifthTail r (y-x)) :=
  (volume.measurePreserving_sub_left y).integrable_comp_of_integrable
    (inverseFifthTail_integrable hr)

theorem translatedInverseFifth_integral (y : Position) {r : ℝ} (hr : 0 < r) :
    (∫ x, inverseFifthTail r (y-x)) = 2*Real.pi/r^2 := by
  rw [integral_sub_left_eq_self,inverseFifthTail_integral hr]

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Nuclei_MoserIntegrability
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.Coulomb.complexWindow_apply _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Integrability across the transported Coulomb pole follows from the
actual Jacobian identity, including a uniform lower bound on the Jacobian. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

theorem moser_flowJacobian_lower (hpublished : PublishedC4FlowInput)
    {rho : ℝ} (hrho : 0 < rho) (V : Position → ℝ) (hV : ContDiff ℝ 6 V)
    (hbound : ∀ x, |manufacturedCharge V x| ≤ rho/2)
    (G : Position → ℝ → Position) (hG : IsUnitTimeFlow (moserVelocity rho V) G)
    (x : Position) {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1) :
    (2/3:ℝ) ≤ flowJacobian G t x := by
  have he := moser_density_jacobian hpublished hrho V hV hbound G hG x ht
  have hp := moser_flowJacobian_pos hpublished hrho V hV hbound G hG x ht
  have hb := (homotopyDensity_bounds V hbound ht.1 ht.2 (G x t)).2
  have hm := mul_le_mul_of_nonneg_right hb hp.le
  nlinarith

theorem moser_integrableOn_comp (hpublished : PublishedC4FlowInput)
    {rho H S : ℝ} (hrho : 0 < rho) (V : Position → ℝ) (hV : ContDiff ℝ 6 V)
    (hbound : ∀ x, |manufacturedCharge V x| ≤ rho/2)
    (hsupport : tsupport V ⊆ slabDomain H S)
    (G : Position → ℝ → Position) (hG : IsUnitTimeFlow (moserVelocity rho V) G)
    (hbij : Function.Bijective (fun x => G x 1))
    (hfix : ∀ x, x ∉ tsupport V → G x 1 = x)
    (f : Position → ℝ) (hf : Measurable f) (hi : IntegrableOn f (slabDomain H S)) :
    IntegrableOn (fun x => f (G x 1)) (slabDomain H S) := by
  have h1 : (1:ℝ) ∈ Set.Icc 0 1 := ⟨by norm_num,le_rfl⟩
  have hreg := (moser_flow_C4 hpublished hrho V hV hbound G hG).1 1 h1
  have himage := moser_time_one_preserves_slab V hsupport (fun x => G x 1) hbij hfix
  have he := integrableOn_image_iff_integrableOn_abs_det_fderiv_smul
    (μ := volume) (slabDomain_isClosed H S).measurableSet
    (fun x (_hx : x ∈ slabDomain H S) =>
      (hreg.differentiable (by norm_num) x).hasFDerivAt.hasFDerivWithinAt)
    hbij.1.injOn f
  rw [himage] at he
  have hw := he.mp hi
  apply (hw.norm.const_mul (3/2:ℝ)).mono'
    ((hf.comp hreg.continuous.measurable).aestronglyMeasurable.restrict)
  exact Filter.Eventually.of_forall (fun x => by
    change ‖f (G x 1)‖ ≤ (3/2:ℝ)*‖|flowJacobian G 1 x| • f (G x 1)‖
    rw [norm_smul,Real.norm_of_nonneg (abs_nonneg _),
      abs_of_pos (moser_flowJacobian_pos hpublished hrho V hV hbound G hG x h1)]
    have hb := moser_flowJacobian_lower hpublished hrho V hV hbound G hG x h1
    nlinarith [norm_nonneg (f (G x 1))])

theorem moser_truncatedCoulomb_integrable (hpublished : PublishedC4FlowInput)
    {rho H S : ℝ} (hrho : 0 < rho) (V : Position → ℝ) (hV : ContDiff ℝ 6 V)
    (hbound : ∀ x, |manufacturedCharge V x| ≤ rho/2)
    (hsupport : tsupport V ⊆ slabDomain H S)
    (G : Position → ℝ → Position) (hG : IsUnitTimeFlow (moserVelocity rho V) G)
    (hbij : Function.Bijective (fun x => G x 1))
    (hfix : ∀ x, x ∉ tsupport V → G x 1 = x) (y : Position) (r : ℝ) :
    IntegrableOn (fun x => Coulomb.truncatedCoulomb r (y-G x 1)) (slabDomain H S) := by
  apply moser_integrableOn_comp hpublished hrho V hV hbound hsupport G hG hbij hfix
    (fun x => Coulomb.truncatedCoulomb r (y-x))
  · exact ((Coulomb.coulombKernel_measurable.indicator measurableSet_ball).comp
      (continuous_const.sub continuous_id).measurable)
  · exact ((Coulomb.truncatedCoulomb_integrable r).comp_sub_left y).integrableOn

theorem moser_coulomb_integrableOn (hpublished : PublishedC4FlowInput)
    {rho H S : ℝ} (hrho : 0 < rho) (hH : 0 ≤ H) (hS : 0 ≤ S)
    (V : Position → ℝ) (hV : ContDiff ℝ 6 V)
    (hbound : ∀ x, |manufacturedCharge V x| ≤ rho/2)
    (hsupport : tsupport V ⊆ slabDomain H S)
    (G : Position → ℝ → Position) (hG : IsUnitTimeFlow (moserVelocity rho V) G)
    (hbij : Function.Bijective (fun x => G x 1))
    (hfix : ∀ x, x ∉ tsupport V → G x 1 = x) (y : Position) :
    IntegrableOn (fun x => Coulomb.coulombKernel (y-G x 1)) (slabDomain H S) := by
  have ht := moser_truncatedCoulomb_integrable hpublished hrho V hV hbound hsupport
    G hG hbij hfix y 1
  have hc : IntegrableOn (fun _ : Position => (1:ℝ)) (slabDomain H S) :=
    integrableOn_const ((slabDomain_isCompact hH hS).measure_lt_top (μ := volume)).ne
  have hreg := (moser_flow_C4 hpublished hrho V hV hbound G hG).1 1 ⟨by norm_num,le_rfl⟩
  apply (ht.add hc).mono'
    ((Coulomb.coulombKernel_measurable.comp
      (continuous_const.sub hreg.continuous).measurable).aestronglyMeasurable.restrict)
  exact Filter.Eventually.of_forall (fun x => by
    change ‖Coulomb.coulombKernel (y-G x 1)‖ ≤ Coulomb.truncatedCoulomb 1 (y-G x 1)+1
    rw [Real.norm_of_nonneg (Coulomb.coulombKernel_nonneg _)]
    simpa only [one_mul,mul_one,inv_one] using
      Coulomb.coulomb_integrand_bound (f := fun _ => (1:ℝ))
        (fun _ => zero_le_one) (fun _ => le_rfl) (by norm_num : (0:ℝ) < 1) y (G x 1))

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

theorem slabTripleEquiv_apply (x : Position) : slabTripleEquiv x = (x 0, x 1, x 2) := rfl

theorem slabTripleEquiv_symm_apply (p : SlabTriple) :
    slabTripleEquiv.symm p = WithLp.toLp 2 ![p.1, p.2.1, p.2.2] := by
  ext a
  fin_cases a <;> rfl

theorem slabTripleEquiv_measurePreserving : MeasurePreserving slabTripleEquiv := by
  exact ((MeasurePreserving.id volume).prod
    (volume_preserving_piFinTwo (fun _ : Fin 2 => ℝ))).comp
      ((volume_preserving_piFinSuccAbove (fun _ : Fin 3 => ℝ) 0).comp
        (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin 3)))

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_CubeGeometry
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual Euclidean mesh cells: volume, radius, node containment, and
disjoint interiors. These retain the volume normalization of the Gauss rule. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb

theorem mem_positionCube {x b : Position} {h : ℝ} :
    x ∈ positionCube b h ↔ ∀ i, |x i-b i| ≤ h/2 := by
  change ((fun i => b i-h/2) ≤ WithLp.ofLp x ∧
    WithLp.ofLp x ≤ (fun i => b i+h/2)) ↔ _
  constructor
  · rintro ⟨hl,hu⟩ i
    exact abs_le.mpr ⟨by linarith [hl i],by linarith [hu i]⟩
  · intro hx
    constructor <;> intro i <;> have hi := abs_le.mp (hx i) <;> linarith

theorem mem_positionOpenCube {x b : Position} {h : ℝ} :
    x ∈ positionOpenCube b h ↔ ∀ i, |x i-b i| < h/2 := by
  change (∀ i ∈ Set.univ, x i ∈ Set.Ioo (b i-h/2) (b i+h/2)) ↔ _
  simp only [Set.mem_univ,true_implies,Set.mem_Ioo]
  constructor
  · intro hx i
    exact abs_lt.mpr ⟨by linarith [(hx i).1],by linarith [(hx i).2]⟩
  · intro hx i
    have hi := abs_lt.mp (hx i)
    constructor <;> linarith

theorem positionCube_isClosed (b : Position) (h : ℝ) : IsClosed (positionCube b h) :=
  isClosed_Icc.preimage (PiLp.continuous_ofLp 2 (fun _ : Fin 3 => ℝ))

theorem positionOpenCube_measurable (b : Position) (h : ℝ) :
    MeasurableSet (positionOpenCube b h) :=
  (MeasurableSet.univ_pi (fun _ => measurableSet_Ioo)).preimage
    (PiLp.continuous_ofLp 2 (fun _ : Fin 3 => ℝ)).measurable

theorem positionOpenCube_subset (b : Position) (h : ℝ) :
    positionOpenCube b h ⊆ positionCube b h := by
  intro x hx
  exact mem_positionCube.mpr (fun i => (mem_positionOpenCube.mp hx i).le)

theorem positionCube_volume (b : Position) {h : ℝ} (hh : 0 ≤ h) :
    volume.real (positionCube b h) = h^3 := by
  have he := (PiLp.volume_preserving_ofLp (Fin 3)).measure_preimage
    (s := Set.Icc (fun i => b i-h/2) (fun i => b i+h/2)) measurableSet_Icc.nullMeasurableSet
  unfold positionCube Measure.real
  rw [he,Real.volume_Icc_pi_toReal (by intro i; linarith)]
  simp only [show ∀ i : Fin 3, b i+h/2-(b i-h/2) = h by intro; ring]
  simp

theorem positionOpenCube_volume (b : Position) {h : ℝ} (hh : 0 ≤ h) :
    volume.real (positionOpenCube b h) = h^3 := by
  have he := (PiLp.volume_preserving_ofLp (Fin 3)).measure_preimage
    (s := Set.univ.pi (fun i => Set.Ioo (b i-h/2) (b i+h/2)))
    (MeasurableSet.univ_pi (fun _ => measurableSet_Ioo)).nullMeasurableSet
  unfold positionOpenCube Measure.real
  rw [he,Real.volume_pi_Ioo_toReal (by intro i; linarith)]
  simp only [show ∀ i : Fin 3, b i+h/2-(b i-h/2) = h by intro; ring]
  simp

theorem positionOpenCube_ae_eq (b : Position) (h : ℝ) :
    positionOpenCube b h =ᵐ[volume] positionCube b h := by
  have he := Measure.univ_pi_Ioo_ae_eq_Icc
    (μ := fun _ : Fin 3 => (volume : Measure ℝ))
    (f := fun i => b i-h/2) (g := fun i => b i+h/2)
  exact (PiLp.volume_preserving_ofLp (Fin 3)).quasiMeasurePreserving.ae he

theorem cubePoint_mem_positionCube (b : Position) {h : ℝ} (hh : 0 ≤ h)
    {x y z : ℝ} (hx : x ∈ Set.Icc (-1:ℝ) 1)
    (hy : y ∈ Set.Icc (-1:ℝ) 1) (hz : z ∈ Set.Icc (-1:ℝ) 1) :
    cubePoint b (h/2) x y z ∈ positionCube b h := by
  rw [mem_positionCube]
  intro i
  have he : cubePoint b (h/2) x y z i-b i = (h/2)*(![x,y,z] i) := by
    fin_cases i <;> simp [cubePoint] <;> ring
  rw [he,abs_mul,abs_of_nonneg (by positivity : 0 ≤ h/2)]
  apply (mul_le_mul_of_nonneg_left (show |![x,y,z] i| ≤ 1 from ?_) (by positivity)).trans_eq
    (mul_one _)
  fin_cases i
  · exact abs_le.mpr hx
  · exact abs_le.mpr hy
  · exact abs_le.mpr hz

theorem positionCube_norm_sub_le {b x : Position} {h : ℝ} (hh : 0 ≤ h)
    (hx : x ∈ positionCube b h) : ‖x-b‖ ≤ h := by
  have hi := mem_positionCube.mp hx
  have hs : ‖x-b‖^2 ≤ 3*(h/2)^2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    calc
      _ ≤ ∑ _i : Fin 3, (h/2)^2 := by
        apply Finset.sum_le_sum
        intro i _
        change (x i-b i)^2 ≤ _
        nlinarith [abs_le.mp (hi i),sq_abs (x i-b i)]
      _ = _ := by simp
  nlinarith [norm_nonneg (x-b)]

theorem positionCube_isCompact (b : Position) {h : ℝ} (hh : 0 ≤ h) :
    IsCompact (positionCube b h) := by
  apply (isCompact_closedBall b h).of_isClosed_subset (positionCube_isClosed b h)
  intro x hx
  exact positionCube_norm_sub_le hh hx

theorem positionCube_diameter_bound {b x y : Position} {h : ℝ} (hh : 0 ≤ h)
    (hx : x ∈ positionCube b h) (hy : y ∈ positionCube b h) : ‖x-y‖ ≤ 2*h := by
  have ht := norm_sub_le_norm_sub_add_norm_sub x b y
  rw [norm_sub_rev b y] at ht
  linarith [positionCube_norm_sub_le hh hx,positionCube_norm_sub_le hh hy]

theorem grid_openCubes_disjoint {h : ℝ} (hh : 0 < h) {k l : Fin 3 → ℤ} (hkl : k ≠ l) :
    Disjoint (positionOpenCube (gaussCellCenter h k) h)
      (positionOpenCube (gaussCellCenter h l) h) := by
  obtain ⟨i,hi⟩ := Function.ne_iff.mp hkl
  apply Set.disjoint_left.mpr
  intro x hx hy
  have hx := abs_lt.mp (mem_positionOpenCube.mp hx i)
  have hy := abs_lt.mp (mem_positionOpenCube.mp hy i)
  change -(h/2) < x i-h*(k i:ℝ) ∧ x i-h*(k i:ℝ) < h/2 at hx
  change -(h/2) < x i-h*(l i:ℝ) ∧ x i-h*(l i:ℝ) < h/2 at hy
  rcases lt_or_gt_of_ne hi with hi | hi
  · have hd : (k i:ℝ)+1 ≤ l i := by exact_mod_cast (show k i+1 ≤ l i by omega)
    nlinarith [mul_le_mul_of_nonneg_left hd hh.le]
  · have hd : (l i:ℝ)+1 ≤ k i := by exact_mod_cast (show l i+1 ≤ k i by omega)
    nlinarith [mul_le_mul_of_nonneg_left hd hh.le]

theorem grid_cell_integral_sum_le {ι : Type*} [Fintype ι]
    (index : ι → Fin 3 → ℤ) (hindex : Function.Injective index)
    {h : ℝ} (hh : 0 < h) (f : Position → ℝ) (hf : Integrable f)
    (hpos : ∀ x, 0 ≤ f x) :
    (∑ i, ∫ x in positionCube (gaussCellCenter h (index i)) h, f x) ≤ ∫ x, f x := by
  have he (i : ι) := setIntegral_congr_set
    (f := f) (positionOpenCube_ae_eq (gaussCellCenter h (index i)) h)
  simp_rw [← he]
  rw [← integral_iUnion_fintype
    (fun i => positionOpenCube_measurable (gaussCellCenter h (index i)) h)
    (fun i j hij => grid_openCubes_disjoint hh (fun he => hij (hindex he)))
    (fun _ => hf.integrableOn)]
  exact setIntegral_le_integral hf (Filter.Eventually.of_forall hpos)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_CubeIntegral
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The normalized tensor cell integral is the ordinary Euclidean volume
integral on the translated cube, with no change of volume convention. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

theorem cubeTripleBox_measurable (b : Position) (h : ℝ) :
    MeasurableSet (cubeTripleBox b h) :=
  measurableSet_Icc.prod (measurableSet_Icc.prod measurableSet_Icc)

theorem cubeTripleBox_preimage (b : Position) (h : ℝ) :
    slabTripleEquiv ⁻¹' cubeTripleBox b h = positionCube b h := by
  ext x
  simp only [Set.mem_preimage,cubeTripleBox,slabTripleEquiv_apply,Set.mem_prod,
    Set.mem_Icc,mem_positionCube]
  constructor
  · rintro ⟨h0,h1,h2⟩ i
    fin_cases i
    · change |x 0-b 0| ≤ h/2
      exact abs_le.mpr ⟨by linarith [h0.1],by linarith [h0.2]⟩
    · change |x 1-b 1| ≤ h/2
      exact abs_le.mpr ⟨by linarith [h1.1],by linarith [h1.2]⟩
    · change |x 2-b 2| ≤ h/2
      exact abs_le.mpr ⟨by linarith [h2.1],by linarith [h2.2]⟩
  · intro hx
    have h0 := abs_le.mp (hx 0)
    have h1 := abs_le.mp (hx 1)
    have h2 := abs_le.mp (hx 2)
    exact ⟨⟨by linarith,by linarith⟩,⟨by linarith,by linarith⟩,
      ⟨by linarith,by linarith⟩⟩

theorem cube_setIntegral_triple (b : Position) (h : ℝ) (f : Position → ℝ) :
    (∫ x in positionCube b h, f x) =
      ∫ p in cubeTripleBox b h, f (slabTripleEquiv.symm p) := by
  have hm := slabTripleEquiv_measurePreserving.restrict_preimage (cubeTripleBox_measurable b h)
  rw [cubeTripleBox_preimage] at hm
  simpa only [Function.comp_apply,MeasurableEquiv.symm_apply_apply] using
    hm.integral_comp' (f ∘ slabTripleEquiv.symm)

theorem centered_interval_integral (c h : ℝ) (f : ℝ → ℝ) :
    (h/2)*(∫ t : ℝ in (-1)..1, f (c+h/2*t)) =
      ∫ t : ℝ in (c-h/2)..(c+h/2), f t := by
  have he := intervalIntegral.smul_integral_comp_add_mul
    (f := f) (a := (-1:ℝ)) (b := 1) (h/2) c
  simpa only [smul_eq_mul,mul_neg_one,mul_one,← sub_eq_add_neg] using he

theorem centered_triple_integral (c₀ c₁ c₂ h : ℝ) (f : ℝ → ℝ → ℝ → ℝ) :
    (h/2)^3*(∫ x : ℝ in (-1)..1, ∫ y : ℝ in (-1)..1, ∫ z : ℝ in (-1)..1,
      f (c₀+h/2*x) (c₁+h/2*y) (c₂+h/2*z)) =
      ∫ x : ℝ in (c₀-h/2)..(c₀+h/2),
        ∫ y : ℝ in (c₁-h/2)..(c₁+h/2),
          ∫ z : ℝ in (c₂-h/2)..(c₂+h/2), f x y z := by
  let d := h/2
  have hz (x y : ℝ) : d*(∫ z : ℝ in (-1)..1, f x y (c₂+d*z)) =
      ∫ z : ℝ in (c₂-d)..(c₂+d), f x y z := centered_interval_integral c₂ h (f x y)
  have hy (x : ℝ) : d^2*(∫ y : ℝ in (-1)..1, ∫ z : ℝ in (-1)..1,
      f x (c₁+d*y) (c₂+d*z)) =
      ∫ y : ℝ in (c₁-d)..(c₁+d), ∫ z : ℝ in (c₂-d)..(c₂+d), f x y z := by
    calc
      _ = d*(∫ y : ℝ in (-1)..1, d*(∫ z : ℝ in (-1)..1, f x (c₁+d*y) (c₂+d*z))) := by
        rw [intervalIntegral.integral_const_mul]
        ring
      _ = d*(∫ y : ℝ in (-1)..1, ∫ z : ℝ in (c₂-d)..(c₂+d), f x (c₁+d*y) z) := by
        simp_rw [hz]
      _ = _ := centered_interval_integral c₁ h (fun y => ∫ z : ℝ in (c₂-d)..(c₂+d), f x y z)
  change d^3*_ = _
  calc
    _ = d*(∫ x : ℝ in (-1)..1, d^2*(∫ y : ℝ in (-1)..1,
        ∫ z : ℝ in (-1)..1, f (c₀+d*x) (c₁+d*y) (c₂+d*z))) := by
      rw [intervalIntegral.integral_const_mul]
      ring
    _ = d*(∫ x : ℝ in (-1)..1, ∫ y : ℝ in (c₁-d)..(c₁+d),
        ∫ z : ℝ in (c₂-d)..(c₂+d), f (c₀+d*x) y z) := by simp_rw [hy]
    _ = _ := centered_interval_integral c₀ h
      (fun x => ∫ y : ℝ in (c₁-d)..(c₁+d), ∫ z : ℝ in (c₂-d)..(c₂+d), f x y z)

theorem positionCellIntegral_eq_setIntegral (b : Position) {h : ℝ} (hh : 0 ≤ h)
    (f : Position → ℝ) (hf : IntegrableOn f (positionCube b h)) :
    positionCellIntegral b h f = ∫ x in positionCube b h, f x := by
  let F : SlabTriple → ℝ := fun p => f (slabTripleEquiv.symm p)
  have hm := slabTripleEquiv_measurePreserving.restrict_preimage (cubeTripleBox_measurable b h)
  rw [cubeTripleBox_preimage] at hm
  have hF : IntegrableOn F (cubeTripleBox b h) :=
    (hm.integrable_comp_emb slabTripleEquiv.measurableEmbedding).mp
      (by simpa only [IntegrableOn,F,Function.comp_def,MeasurableEquiv.symm_apply_apply] using hf)
  have ht : (∫ p in cubeTripleBox b h, F p) =
      ∫ x in Set.Icc (b 0-h/2) (b 0+h/2),
        ∫ y in Set.Icc (b 1-h/2) (b 1+h/2),
          ∫ z in Set.Icc (b 2-h/2) (b 2+h/2), F (x,y,z) := by
    rw [cubeTripleBox,Measure.volume_eq_prod] at hF ⊢
    rw [setIntegral_prod _ hF]
    apply integral_congr_ae
    have hFa := hF
    rw [IntegrableOn,← Measure.prod_restrict] at hFa
    filter_upwards [hFa.prod_right_ae] with x hx
    exact setIntegral_prod _ hx
  rw [cube_setIntegral_triple,ht]
  have hi (i : Fin 3) : b i-h/2 ≤ b i+h/2 := by linarith
  have he (x y z : ℝ) : cubePoint b (h/2) x y z =
      slabTripleEquiv.symm (b 0+h/2*x,b 1+h/2*y,b 2+h/2*z) := by
    rw [slabTripleEquiv_symm_apply]
    ext i
    fin_cases i <;> simp [cubePoint] <;> ring
  unfold positionCellIntegral
  simp_rw [he]
  rw [centered_triple_integral (b 0) (b 1) (b 2) h
    (fun x y z => f (slabTripleEquiv.symm (x,y,z)))]
  simp_rw [intervalIntegral.integral_of_le (hi _),← integral_Icc_eq_integral_Ioc]
  rfl

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_CenteredGrid
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A concrete finite family of lattice cubes tiles the enclosing rectangular
slab, including its boundary. -/

noncomputable section
open MeasureTheory
open scoped BigOperators Classical
namespace ContinuumCoulomb

theorem grid_cell_integral_sum_eq {ι : Type*} [Fintype ι]
    (index : ι → Fin 3 → ℤ) (hindex : Function.Injective index)
    {h : ℝ} (hh : 0 < h) {B : Set Position}
    (hcover : (⋃ i, positionCube (gaussCellCenter h (index i)) h) = B)
    (f : Position → ℝ) (hf : IntegrableOn f B) :
    (∑ i, ∫ x in positionCube (gaussCellCenter h (index i)) h, f x) = ∫ x in B, f x := by
  have he (i : ι) := positionOpenCube_ae_eq (gaussCellCenter h (index i)) h
  have hsets : (⋃ i, positionOpenCube (gaussCellCenter h (index i)) h) =ᵐ[volume]
      (⋃ i, positionCube (gaussCellCenter h (index i)) h) := by
    filter_upwards [ae_all_iff.mpr he] with x hx
    show (x ∈ ⋃ i, positionOpenCube (gaussCellCenter h (index i)) h) =
      (x ∈ ⋃ i, positionCube (gaussCellCenter h (index i)) h)
    simp only [Set.mem_iUnion]
    exact propext (exists_congr fun i => (hx i).to_iff)
  have hi (i : ι) : IntegrableOn f (positionOpenCube (gaussCellCenter h (index i)) h) := by
    apply hf.mono_set
    intro x hx
    rw [← hcover]
    exact Set.mem_iUnion.mpr ⟨i,positionOpenCube_subset _ _ hx⟩
  calc
    _ = ∑ i, ∫ x in positionOpenCube (gaussCellCenter h (index i)) h, f x := by
      apply Finset.sum_congr rfl
      intro i _
      exact (setIntegral_congr_set (he i)).symm
    _ = ∫ x in ⋃ i, positionOpenCube (gaussCellCenter h (index i)) h, f x :=
      (integral_iUnion_fintype (fun i => positionOpenCube_measurable _ _)
        (fun i j hij => grid_openCubes_disjoint hh (fun he => hij (hindex he))) hi).symm
    _ = ∫ x in ⋃ i, positionCube (gaussCellCenter h (index i)) h, f x :=
      setIntegral_congr_set hsets
    _ = _ := by rw [hcover]

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Nuclei_MoserGridPotential
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.Coulomb.complexWindow_apply _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact identification of the continuous part of the finite transported
cubature with the manufactured slab-plus-well potential. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb

theorem moser_grid_potential (hpublished : PublishedC4FlowInput)
    {rho H S h : ℝ} (hrho : 0 < rho) (hH : 0 ≤ H) (hS : 0 ≤ S) (hh : 0 < h)
    (V : Position → ℝ) (hV : ContDiff ℝ 6 V) (hc : HasCompactSupport V)
    (hbound : ∀ x, |manufacturedCharge V x| ≤ rho/2)
    (hsupport : tsupport V ⊆ slabDomain H S)
    (G : Position → ℝ → Position) (hG : IsUnitTimeFlow (moserVelocity rho V) G)
    (hbij : Function.Bijective (fun x => G x 1))
    (hfix : ∀ x, x ∉ tsupport V → G x 1 = x)
    {ι : Type*} [Fintype ι] (index : ι → Fin 3 → ℤ) (hindex : Function.Injective index)
    (hcover : (⋃ i, positionCube (gaussCellCenter h (index i)) h) = slabDomain H S)
    (y : Position) :
    -rho*(∑ i, positionCellIntegral (gaussCellCenter h (index i)) h
      (fun x => Coulomb.coulombKernel (y-G x 1))) = slabPotential rho H S y+V y := by
  have hsub (i : ι) : positionCube (gaussCellCenter h (index i)) h ⊆ slabDomain H S := by
    rw [← hcover]
    exact Set.subset_iUnion_of_subset i (fun _ hx => hx)
  have hi := moser_coulomb_integrableOn hpublished hrho hH hS V hV hbound hsupport G hG hbij hfix y
  have hsum : (∑ i, positionCellIntegral (gaussCellCenter h (index i)) h
      (fun x => Coulomb.coulombKernel (y-G x 1))) =
      ∫ x in slabDomain H S, Coulomb.coulombKernel (y-G x 1) := by
    simp_rw [positionCellIntegral_eq_setIntegral _ hh.le _ (hi.mono_set (hsub _))]
    exact grid_cell_integral_sum_eq index hindex hh hcover _ hi
  have htrans := moser_density_integral hpublished hrho V hV hbound hsupport G hG hbij hfix
    (fun x => Coulomb.coulombKernel (y-x))
  have he : (∫ x in slabDomain H S, synthesizedDensity rho H S V x*Coulomb.coulombKernel (y-x)) =
      ∫ x, Coulomb.coulombKernel (y-x)*synthesizedDensity rho H S V x := by
    calc
      _ = ∫ x in slabDomain H S, Coulomb.coulombKernel (y-x)*synthesizedDensity rho H S V x := by
        apply setIntegral_congr_fun (slabDomain_isClosed H S).measurableSet
        intro x _
        ring
      _ = _ := setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
        have hv : x ∉ tsupport V := fun h => hx (hsupport h)
        simp only [synthesizedDensity,slabDensity,Set.indicator_of_notMem hx,
          manufacturedCharge_zero hv,add_zero,mul_zero])
  calc
    _ = -(rho*(∫ x in slabDomain H S, Coulomb.coulombKernel (y-G x 1))) := by rw [hsum]; ring
    _ = -(∫ x in slabDomain H S, synthesizedDensity rho H S V x*Coulomb.coulombKernel (y-x)) :=
      congrArg Neg.neg htrans.symm
    _ = -(∫ x, Coulomb.coulombKernel (y-x)*synthesizedDensity rho H S V x) := congrArg Neg.neg he
    _ = _ := synthesizedDensity_potential hrho.le hH hS V (hV.of_le (by norm_num)) hc hbound y

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_CoulombFarCell
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fourth-order quadrature on a cube separated from an actual Coulomb pole. -/

noncomputable section
namespace ContinuumCoulomb

theorem translatedCoulomb_derivative_norm (k : ℕ) (y z : Position) :
    ‖iteratedFDeriv ℝ k (fun w => Coulomb.coulombKernel (y-w)) z‖ =
      ‖iteratedFDeriv ℝ k Coulomb.coulombKernel (y-z)‖ := by
  let e : Position ≃ₗᵢ[ℝ] Position := LinearIsometryEquiv.neg ℝ
  have he := e.norm_iteratedFDeriv_comp_right (fun w => Coulomb.coulombKernel (y+w)) z k
  change ‖iteratedFDeriv ℝ k (fun w => Coulomb.coulombKernel (y + -w)) z‖ =
    ‖iteratedFDeriv ℝ k (fun w => Coulomb.coulombKernel (y+w)) (-z)‖ at he
  rw [iteratedFDeriv_comp_add_left] at he
  simpa only [sub_eq_add_neg] using he

theorem coulomb_far_cell_error :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (y b : Position) (h r : ℝ), 0 ≤ h → 0 < r →
      (∀ x ∈ Set.Icc (-1:ℝ) 1, ∀ v ∈ Set.Icc (-1:ℝ) 1,
        ∀ z ∈ Set.Icc (-1:ℝ) 1, r ≤ ‖y-cubePoint b (h/2) x v z‖) →
      |positionCellGauss b h (fun w => Coulomb.coulombKernel (y-w))-
        positionCellIntegral b h (fun w => Coulomb.coulombKernel (y-w))| ≤
        C*h^7/r^5 := by
  obtain ⟨C,hC,hbound⟩ := coulombKernel_derivative_decay
  refine ⟨C,hC,fun y b h r hh hr hdist => ?_⟩
  have hne (x : ℝ) (hx : x ∈ Set.Icc (-1:ℝ) 1) (v : ℝ) (hv : v ∈ Set.Icc (-1:ℝ) 1)
      (z : ℝ) (hz : z ∈ Set.Icc (-1:ℝ) 1) : y-cubePoint b (h/2) x v z ≠ 0 :=
    norm_pos_iff.mp (hr.trans_le (hdist x hx v hv z hz))
  have hD (x : ℝ) (hx : x ∈ Set.Icc (-1:ℝ) 1) (v : ℝ) (hv : v ∈ Set.Icc (-1:ℝ) 1)
      (z : ℝ) (hz : z ∈ Set.Icc (-1:ℝ) 1) :
      ‖iteratedFDeriv ℝ 4 (fun w => Coulomb.coulombKernel (y-w))
        (cubePoint b (h/2) x v z)‖ ≤ C/r^5 := by
    rw [translatedCoulomb_derivative_norm]
    apply (le_div_iff₀ (pow_pos hr 5)).mpr
    have hp := hbound (4:Fin 5) _ (hne x hx v hv z hz)
    exact (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hr.le (hdist x hx v hv z hz) 5)
      (norm_nonneg _)).trans hp
  have he := positionCellGauss_error_local (fun w => Coulomb.coulombKernel (y-w)) b hh
    (div_nonneg (by linarith) (pow_nonneg hr.le 5))
    (fun x hx v hv z hz => (coulombKernel_contDiffAt (hne x hx v hv z hz)).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 4) |>.comp _
        (contDiffAt_const.sub contDiffAt_id)) hD
  apply he.trans_eq
  ring

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Nuclei_TransportedCoulombDerivative
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fourth derivatives of the Coulomb integrand after the Moser map. The
estimate is local at a point and needs no regularity across the pole. -/

noncomputable section
namespace ContinuumCoulomb

theorem fourth_composite_norm_bound (f : Position → ℝ) (G : Position → Position) (x : Position)
    (hf : ContDiffAt ℝ 4 f (G x)) (hG : ContDiff ℝ 4 G) {C D : ℝ}
    (hC : ∀ k : ℕ, k ≤ 4 → ‖iteratedFDeriv ℝ k f (G x)‖ ≤ C)
    (hD : ∀ k : ℕ, 1 ≤ k → k ≤ 4 → ‖iteratedFDeriv ℝ k G x‖ ≤ D^k) :
    ‖iteratedFDeriv ℝ 4 (f ∘ G) x‖ ≤ 24*C*D^4 := by
  obtain ⟨U,hU,hx,hfU⟩ := hf.contDiffOn' le_rfl (by norm_num)
  have hfU : ContDiffOn ℝ 4 f U := by simpa using hfU
  have hS : IsOpen (G ⁻¹' U) := hU.preimage hG.continuous
  have hc := norm_iteratedFDerivWithin_comp_le hfU hG.contDiffOn (n := 4) le_rfl
    hU.uniqueDiffOn hS.uniqueDiffOn (fun _ hy => hy) hx
    (fun k hk => by
      rw [iteratedFDerivWithin_eq_iteratedFDeriv hU.uniqueDiffOn (hf.of_le (by exact_mod_cast hk)) hx]
      exact hC k hk)
    (fun k hk hk' => by
      rw [iteratedFDerivWithin_eq_iteratedFDeriv (f := G) (x := x) (s := G ⁻¹' U) hS.uniqueDiffOn
        (hG.of_le (by exact_mod_cast hk')).contDiffAt hx]
      exact hD k hk hk')
  rw [iteratedFDerivWithin_eq_iteratedFDeriv (f := f ∘ G) (x := x) (s := G ⁻¹' U) hS.uniqueDiffOn (hf.comp x hG.contDiffAt) hx] at hc
  norm_num only [Nat.factorial] at hc
  exact hc

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_WellCover
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A cover of the actual well support by boxes whose total volume is
linear in the number of wells and the vertical cutoff radius. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb

theorem mem_wellCoverBox {u : PlanarPosition} {r S : ℝ} {x : Position} :
    x ∈ wellCoverBox u r S ↔ |x 0-u 0| ≤ r ∧ |x 1-u 1| ≤ r ∧ |x 2| ≤ S := by
  constructor
  · rintro ⟨hl,hu⟩
    have h0l := hl 0; have h0u := hu 0
    have h1l := hl 1; have h1u := hu 1
    have h2l := hl 2; have h2u := hu 2
    simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val] at *
    exact ⟨abs_le.mpr ⟨by linarith,by linarith⟩,
      abs_le.mpr ⟨by linarith,by linarith⟩,abs_le.mpr ⟨h2l,h2u⟩⟩
  · rintro ⟨h0,h1,h2⟩
    obtain ⟨h0l,h0u⟩ := abs_le.mp h0
    obtain ⟨h1l,h1u⟩ := abs_le.mp h1
    obtain ⟨h2l,h2u⟩ := abs_le.mp h2
    constructor <;> intro i <;> fin_cases i <;> simp <;> linarith

theorem wellCoverBox_isClosed (u : PlanarPosition) (r S : ℝ) :
    IsClosed (wellCoverBox u r S) :=
  isClosed_Icc.preimage (PiLp.continuous_ofLp 2 (fun _ : Fin 3 => ℝ))

theorem wellCoverBox_measure_ne_top (u : PlanarPosition) (r S : ℝ) :
    volume (wellCoverBox u r S) ≠ ⊤ := by
  unfold wellCoverBox
  rw [(PiLp.volume_preserving_ofLp (Fin 3)).measure_preimage measurableSet_Icc.nullMeasurableSet]
  exact isCompact_Icc.measure_ne_top

theorem wellCoverBox_volume (u : PlanarPosition) {r S : ℝ} (hr : 0 ≤ r) (hS : 0 ≤ S) :
    volume.real (wellCoverBox u r S) = 8*r^2*S := by
  unfold wellCoverBox Measure.real
  rw [(PiLp.volume_preserving_ofLp (Fin 3)).measure_preimage measurableSet_Icc.nullMeasurableSet]
  rw [Real.volume_Icc_pi_toReal (by intro i; fin_cases i <;> simp <;> linarith)]
  simp [Fin.prod_univ_succ]
  ring

theorem manufacturedWellField_support_cover (freq scale : ℝ) {S : ℝ} (hS : 0 < S)
    {m : ℕ} (u : Fin m → PlanarPosition) :
    tsupport (manufacturedWellField freq scale S u) ⊆ ⋃ i, wellCoverBox (u i) 1 S := by
  apply closure_minimal _ (isClosed_iUnion_of_finite (fun i => wellCoverBox_isClosed (u i) 1 S))
  intro x hx
  have hz : |(positionSplitCoordinates x).2| < S := by
    by_contra hn
    exact hx (manufacturedWellField_outer freq scale hS u x (le_of_not_gt hn))
  have hnear : ∃ i, ‖(positionSplitCoordinates x).1-u i‖ < 1 := by
    by_contra hn
    apply hx
    unfold manufacturedWellField
    rw [countertermWellSum_zero_far freq scale u _ (fun i =>
      le_of_not_gt (fun hi => hn ⟨i,hi⟩)),mul_zero]
  obtain ⟨i,hi⟩ := hnear
  apply Set.mem_iUnion.mpr
  refine ⟨i,mem_wellCoverBox.mpr ⟨?_,?_,?_⟩⟩
  · simpa only [Real.norm_eq_abs,PiLp.sub_apply,positionSplitCoordinates_fst_zero] using
      (PiLp.norm_apply_le ((positionSplitCoordinates x).1-u i) 0).trans hi.le
  · simpa only [Real.norm_eq_abs,PiLp.sub_apply,positionSplitCoordinates_fst_one] using
      (PiLp.norm_apply_le ((positionSplitCoordinates x).1-u i) 1).trans hi.le
  · simpa only [positionSplitCoordinates_snd] using hz.le

theorem wellCover_volume_bound {m : ℕ} (u : Fin m → PlanarPosition)
    {r S : ℝ} (hr : 0 ≤ r) (hS : 0 ≤ S) :
    volume.real (⋃ i, wellCoverBox (u i) r S) ≤ 8*m*r^2*S := by
  apply (measureReal_iUnion_fintype_le (fun i => wellCoverBox (u i) r S)).trans
  simp only [wellCoverBox_volume _ hr hS,Finset.sum_const,Finset.card_univ,
    Fintype.card_fin,nsmul_eq_mul]
  apply le_of_eq
  ring

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_ExceptionalCellVolume
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Cells meeting the well support have total volume O(m*S), rather than
the volume of the surrounding slab. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb

theorem cube_meets_wellCover_subset {b z : Position} {u : PlanarPosition}
    {h r S : ℝ} (hh : 0 ≤ h) (hz : z ∈ positionCube b h)
    (hzu : z ∈ wellCoverBox u r S) :
    positionCube b h ⊆ wellCoverBox u (r+2*h) (S+2*h) := by
  intro x hx
  have hd := positionCube_diameter_bound hh hx hz
  have hi (i : Fin 3) : |x i-z i| ≤ 2*h := by
    exact (PiLp.norm_apply_le (x-z) i).trans hd
  obtain ⟨hz0,hz1,hz2⟩ := mem_wellCoverBox.mp hzu
  apply mem_wellCoverBox.mpr
  refine ⟨?_,?_,?_⟩
  · linarith [abs_sub_le (x 0) (z 0) (u 0),hi 0]
  · linarith [abs_sub_le (x 1) (z 1) (u 1),hi 1]
  · have he := abs_sub_le (x 2) (z 2) 0
    simp only [sub_zero] at he
    linarith [hi 2]

theorem exceptional_cell_volume_bound {ι : Type*} [Fintype ι]
    (index : ι → Fin 3 → ℤ) (hindex : Function.Injective index)
    {h S : ℝ} (hh : 0 < h) (hh1 : h ≤ 1) (hS : 1 ≤ S)
    (freq scale : ℝ) {m : ℕ} (u : Fin m → PlanarPosition)
    (hmeet : ∀ i, ∃ z ∈ positionCube (gaussCellCenter h (index i)) h,
      z ∈ tsupport (manufacturedWellField freq scale S u)) :
    (Fintype.card ι:ℝ)*h^3 ≤ 216*m*S := by
  let A : ι → Set Position := fun i => positionOpenCube (gaussCellCenter h (index i)) h
  let B : Fin m → Set Position := fun j => wellCoverBox (u j) (1+2*h) (S+2*h)
  have hsub : (⋃ i, A i) ⊆ ⋃ j, B j := by
    intro x hx
    obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hx
    obtain ⟨z,hz,hzs⟩ := hmeet i
    obtain ⟨j,hj⟩ := Set.mem_iUnion.mp
      (manufacturedWellField_support_cover freq scale (by linarith : 0 < S) u hzs)
    exact Set.mem_iUnion.mpr ⟨j,cube_meets_wellCover_subset hh.le hz hj
      (positionOpenCube_subset _ _ hi)⟩
  have hBfinite : volume (⋃ j, B j) ≠ ⊤ := by
    apply ne_of_lt
    apply lt_of_le_of_lt (measure_iUnion_fintype_le volume B)
    exact ENNReal.sum_lt_top.mpr (fun j _ => (wellCoverBox_measure_ne_top (u j) _ _).lt_top)
  have hA : volume.real (⋃ i, A i) = (Fintype.card ι:ℝ)*h^3 := by
    rw [measureReal_iUnion_fintype
      (fun i j hij => grid_openCubes_disjoint hh (fun he => hij (hindex he)))
      (fun i => positionOpenCube_measurable _ _)
      (fun i => by
        rw [measure_congr (positionOpenCube_ae_eq (gaussCellCenter h (index i)) h)]
        exact (positionCube_isCompact _ hh.le).measure_ne_top)]
    simp only [positionOpenCube_volume _ hh.le,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  calc
    _ = volume.real (⋃ i, A i) := hA.symm
    _ ≤ volume.real (⋃ j, B j) := measureReal_mono hsub hBfinite
    _ ≤ 8*m*(1+2*h)^2*(S+2*h) :=
      wellCover_volume_bound u (by positivity) (by linarith)
    _ ≤ 8*m*9*(3*S) := by
      gcongr
      · nlinarith
      · linarith
    _ = _ := by ring

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Nuclei_NuclearGridPotential
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual equal-mass grid potential and its error against the
manufactured continuous potential, at every evaluation point. -/

noncomputable section
open MeasureTheory
open scoped BigOperators NNReal
namespace ContinuumCoulomb

theorem gridNuclearPotential_measurable {ι : Type*} [Fintype ι] (index : ι → Fin 3 → ℤ)
    (G : Position → Position) (rho h : ℝ) : Measurable (gridNuclearPotential index G rho h) := by
  apply Measurable.const_mul
  apply Finset.measurable_sum
  intro a _
  exact Coulomb.coulombKernel_measurable.comp (measurable_id.sub measurable_const)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_CompactCoulombSmooth
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.Coulomb.complexWindow_apply _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Smooth Coulomb fields of compact source pieces. Derivatives are moved
to the density, which avoids differentiating through the Coulomb pole. -/

noncomputable section
open MeasureTheory
open scoped Convolution
namespace ContinuumCoulomb

theorem potentialOf_eq_convolution (q : Position → ℝ) :
    NeutralAtom.potentialOf q =
      NeutralAtom.coulombKernel ⋆[ContinuousLinearMap.mul ℝ ℝ,volume] q := by
  funext y
  change (∫ x, NeutralAtom.coulombKernel (y-x)*q x) =
    ∫ x, NeutralAtom.coulombKernel x*q (y-x)
  rw [← integral_sub_left_eq_self (fun x => NeutralAtom.coulombKernel (y-x)*q x) volume y]
  simp only [sub_sub_cancel]

theorem compact_coulomb_C4 {q : Position → ℝ} (hq : ContDiff ℝ 4 q)
    (hc : HasCompactSupport q) : ContDiff ℝ 4 (NeutralAtom.potentialOf q) := by
  rw [potentialOf_eq_convolution]
  exact hc.contDiff_convolution_right (ContinuousLinearMap.mul ℝ ℝ)
    NeutralAtom.locallyIntegrable_coulombKernel hq

theorem compact_coulomb_partial {q : Position → ℝ} (hq : ContDiff ℝ 1 q)
    (hc : HasCompactSupport q) (v y : Position) :
    NeutralAtom.dirPartial (NeutralAtom.potentialOf q) v y =
      NeutralAtom.potentialOf (NeutralAtom.dirPartial q v) y := by
  have hd := hc.hasFDerivAt_convolution_right (ContinuousLinearMap.mul ℝ ℝ)
    NeutralAtom.locallyIntegrable_coulombKernel hq y
  have hi := (hc.fderiv ℝ).convolutionExists_right
    ((ContinuousLinearMap.mul ℝ ℝ).precompR Position)
    NeutralAtom.locallyIntegrable_coulombKernel (hq.continuous_fderiv (by norm_num)) y
  change fderiv ℝ (NeutralAtom.potentialOf q) y v = _
  rw [potentialOf_eq_convolution,hd.fderiv]
  change (∫ x, (ContinuousLinearMap.mul ℝ ℝ).precompR Position
    (NeutralAtom.coulombKernel x) (fderiv ℝ q (y-x))) v = _
  rw [ContinuousLinearMap.integral_apply hi v,potentialOf_eq_convolution]
  rfl

theorem compact_coulomb_bound {q : Position → ℝ} (hq : Continuous q)
    (hc : HasCompactSupport q) {M : ℝ} (hM : ∀ x, ‖q x‖ ≤ M) (y : Position) :
    ‖NeutralAtom.potentialOf q y‖ ≤ 2*Real.pi*M+∫ x, ‖q x‖ := by
  have he := Coulomb.coulomb_convolution_bound (hq.integrable_of_hasCompactSupport hc).norm
    hq.measurable.norm (fun x => norm_nonneg (q x)) hM (by norm_num : (0:ℝ) < 1) y
  have hn := norm_integral_le_integral_norm (μ := volume)
    (fun x => NeutralAtom.coulombKernel (y-x)*q x)
  simp only [norm_mul,Real.norm_of_nonneg (NeutralAtom.coulombKernel_nonneg _)] at hn
  apply hn.trans
  simpa only [one_pow,mul_one,inv_one,one_mul,Coulomb.coulombKernel,NeutralAtom.coulombKernel] using he

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_CoulombSourceCubature
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.Coulomb.complexWindow_apply _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A compact orbital source can be integrated before the nuclear cell rule.
On cells separated from its support, the inverse-fifth-power error survives
integration with only the source's L1 mass as a factor. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

theorem compact_coulomb_integrable {q : Position → ℝ} (hq : Continuous q)
    (hc : HasCompactSupport q) (y : Position) :
    Integrable (fun x => NeutralAtom.coulombKernel (y-x)*q x) := by
  have hi := hc.convolutionExists_right (ContinuousLinearMap.mul ℝ ℝ)
    NeutralAtom.locallyIntegrable_coulombKernel hq y
  change Integrable (fun x => NeutralAtom.coulombKernel x*q (y-x)) at hi
  simpa only [sub_sub_cancel] using hi.comp_sub_left y

theorem compact_coulomb_eval_eq (q : Position → ℝ) (y : Position) :
    NeutralAtom.potentialOf q y = ∫ x, q x*Coulomb.coulombKernel (x-y) := by
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [NeutralAtom.coulombKernel,Coulomb.coulombKernel,norm_sub_rev,mul_comm]

theorem compact_coulomb_eval_integrable {q : Position → ℝ} (hq : Continuous q)
    (hc : HasCompactSupport q) (y : Position) :
    Integrable (fun x => q x*Coulomb.coulombKernel (x-y)) := by
  convert compact_coulomb_integrable hq hc y using 1
  all_goals try with_reducible_and_instances rfl
  funext x
  simp only [NeutralAtom.coulombKernel,Coulomb.coulombKernel,norm_sub_rev,mul_comm]

theorem compact_coulomb_cell_gauss {q : Position → ℝ} (hq : Continuous q)
    (hc : HasCompactSupport q) (b : Position) (h : ℝ) :
    positionCellGauss b h (NeutralAtom.potentialOf q) =
      ∫ x, q x*positionCellGauss b h (fun y => Coulomb.coulombKernel (x-y)) := by
  simp only [positionCellGauss_eq_node_sum,compact_coulomb_eval_eq]
  rw [← integral_finsetSum Finset.univ (fun v _ => compact_coulomb_eval_integrable hq hc _),
    ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [← Finset.mul_sum]
  ring

theorem compact_coulomb_cell_integral {q : Position → ℝ}
    (hq : ContDiff ℝ 4 q) (hc : HasCompactSupport q) (b : Position)
    {h r : ℝ} (hh : 0 ≤ h) (hr : 0 < r)
    (hsep : ∀ x, q x ≠ 0 → ∀ y ∈ positionCube b h, r ≤ ‖y-x‖) :
    Integrable (fun x => q x * positionCellIntegral b h (fun y => Coulomb.coulombKernel (x-y))) ∧
    positionCellIntegral b h (NeutralAtom.potentialOf q) =
      ∫ x, q x * positionCellIntegral b h (fun y => Coulomb.coulombKernel (x-y)) := by
  have hvol : IntegrableOn (fun _ : Position => (1:ℝ)) (positionCube b h) :=
    integrableOn_const ((positionCube_isCompact b hh).measure_lt_top (μ := volume)).ne
  have hqI : Integrable q := hq.continuous.integrable_of_hasCompactSupport hc
  have hmajor := (hqI.norm.mul_prod hvol).const_mul r⁻¹
  have hi : Integrable (fun p : Position × Position =>
      q p.1 * NeutralAtom.coulombKernel (p.2-p.1))
      (volume.prod (volume.restrict (positionCube b h))) := by
    apply hmajor.mono' (by
      exact (hq.continuous.measurable.comp measurable_fst |>.mul
        (NeutralAtom.measurable_coulombKernel.comp (measurable_snd.sub measurable_fst))).aestronglyMeasurable)
    have hp : ∀ᵐ p : Position × Position ∂(volume.prod (volume.restrict (positionCube b h))), p.2 ∈ positionCube b h :=
      (Measure.ae_prod_iff_ae_ae ((positionCube_isClosed b h).measurableSet.preimage measurable_snd)).mpr
        (Filter.Eventually.of_forall (fun _ => ae_restrict_mem (positionCube_isClosed b h).measurableSet))
    filter_upwards [hp] with p hp
    change ‖q p.1 * NeutralAtom.coulombKernel (p.2-p.1)‖ ≤ r⁻¹*(‖q p.1‖*1)
    by_cases hq0 : q p.1 = 0
    · simp [hq0]
    have hd := hsep p.1 hq0 p.2 hp
    rw [norm_mul,Real.norm_of_nonneg (NeutralAtom.coulombKernel_nonneg _),mul_one]
    have hk : NeutralAtom.coulombKernel (p.2-p.1) ≤ r⁻¹ :=
      inv_anti₀ hr hd
    exact (mul_le_mul_of_nonneg_left hk (norm_nonneg _)).trans_eq (mul_comm _ _)
  have hinner (x : Position) :
      (∫ y in positionCube b h, q x*NeutralAtom.coulombKernel (y-x)) =
        q x*positionCellIntegral b h (fun y => Coulomb.coulombKernel (x-y)) := by
    rw [integral_const_mul]
    by_cases hqx : q x = 0
    · simp [hqx]
    have hk : IntegrableOn (fun y => Coulomb.coulombKernel (x-y)) (positionCube b h) := by
      apply (hvol.const_mul r⁻¹).mono' (by
        exact (Coulomb.coulombKernel_measurable.comp (measurable_const.sub measurable_id)).aestronglyMeasurable)
      filter_upwards [ae_restrict_mem (positionCube_isClosed b h).measurableSet] with y hy
      change ‖Coulomb.coulombKernel (x-y)‖ ≤ r⁻¹*1
      rw [Real.norm_of_nonneg (Coulomb.coulombKernel_nonneg _),mul_one]
      apply inv_anti₀ hr
      simpa only [norm_sub_rev] using hsep x hqx y hy
    rw [positionCellIntegral_eq_setIntegral b hh _ hk]
    congr 1
    apply setIntegral_congr_fun (positionCube_isClosed b h).measurableSet
    intro y _
    simp only [NeutralAtom.coulombKernel,Coulomb.coulombKernel,norm_sub_rev]
  refine ⟨?_,?_⟩
  · exact hi.integral_prod_left.congr (Filter.Eventually.of_forall hinner)
  · rw [positionCellIntegral_eq_setIntegral b hh _
      ((compact_coulomb_C4 hq hc).continuous.continuousOn.integrableOn_compact
        (positionCube_isCompact b hh))]
    change (∫ y in positionCube b h, ∫ x, NeutralAtom.coulombKernel (y-x)*q x) = _
    simp_rw [mul_comm (NeutralAtom.coulombKernel _) (q _)]
    rw [← integral_integral_swap hi]
    exact integral_congr_ae (Filter.Eventually.of_forall hinner)

theorem compact_coulomb_cell_gauss_integrable {q : Position → ℝ} (hq : Continuous q)
    (hc : HasCompactSupport q) (b : Position) (h : ℝ) :
    Integrable (fun x => q x*positionCellGauss b h (fun y => Coulomb.coulombKernel (x-y))) := by
  have hi := (integrable_finsetSum Finset.univ (fun (v : Fin 3 → Fin 2) _ =>
    compact_coulomb_eval_integrable hq hc
      (cubePoint b (h/2) (gaussNode (v 0)) (gaussNode (v 1)) (gaussNode (v 2))))).const_mul (h^3/8)
  convert hi using 1
  all_goals try with_reducible_and_instances rfl
  funext x
  rw [positionCellGauss_eq_node_sum,← Finset.mul_sum]
  ring

theorem compact_coulomb_far_cell_error :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (q : Position → ℝ), ContDiff ℝ 4 q → HasCompactSupport q →
      ∀ (b : Position) (h r : ℝ), 0 ≤ h → 0 < r →
      (∀ x, q x ≠ 0 → ∀ y ∈ positionCube b h, r ≤ ‖y-x‖) →
      |positionCellGauss b h (NeutralAtom.potentialOf q)-
        positionCellIntegral b h (NeutralAtom.potentialOf q)| ≤
        (C*h^7/r^5)*(∫ x, ‖q x‖) := by
  obtain ⟨C,hC,herror⟩ := coulomb_far_cell_error
  refine ⟨C,hC,fun q hq hc b h r hh hr hsep => ?_⟩
  have hI := compact_coulomb_cell_integral hq hc b hh hr hsep
  have hQ := compact_coulomb_cell_gauss_integrable hq.continuous hc b h
  rw [compact_coulomb_cell_gauss hq.continuous hc,hI.2,← integral_sub hQ hI.1]
  have hb := norm_integral_le_of_norm_le
    (((hq.continuous.integrable_of_hasCompactSupport hc : Integrable q).norm).mul_const (C*h^7/r^5))
    (Filter.Eventually.of_forall (fun x => show
      ‖q x*positionCellGauss b h (fun y => Coulomb.coulombKernel (x-y))-
        q x*positionCellIntegral b h (fun y => Coulomb.coulombKernel (x-y))‖ ≤
        ‖q x‖*(C*h^7/r^5) from by
      by_cases hx : q x = 0
      · simp only [hx,zero_mul,sub_self,norm_zero,le_refl]
      rw [← mul_sub,norm_mul,Real.norm_eq_abs]
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      apply herror x b h r hh hr
      intro a ha d hd e he
      simpa only [norm_sub_rev] using hsep x hx
        (cubePoint b (h/2) a d e) (cubePoint_mem_positionCube b hh ha hd he)))
  simpa only [Real.norm_eq_abs,integral_mul_const,mul_comm] using hb

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_CompactSourcePairing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fubini identities for nonnegative compact source densities and the
actual transported nuclear potential. No separation from a nuclear pole is
required for these identities. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

theorem compact_source_transport_integrable {q : Position → ℝ}
    (hq : ContDiff ℝ 4 q) (hc : HasCompactSupport q) (hpos : ∀ y, 0 ≤ q y)
    {S : Set Position} (hS : IsCompact S) {G : Position → Position} (hG : Continuous G) :
    Integrable (fun p : Position × Position => q p.2*Coulomb.coulombKernel (p.2-G p.1))
      ((volume.restrict S).prod volume) := by
  have hm : Measurable (fun p : Position × Position => q p.2*Coulomb.coulombKernel (p.2-G p.1)) :=
    (hq.continuous.measurable.comp measurable_snd).mul
      (Coulomb.coulombKernel_measurable.comp (measurable_snd.sub (hG.measurable.comp measurable_fst)))
  apply (integrable_prod_iff hm.aestronglyMeasurable).mpr
  refine ⟨Filter.Eventually.of_forall (fun x => compact_coulomb_eval_integrable hq.continuous hc (G x)),?_⟩
  have hi : IntegrableOn (fun x => NeutralAtom.potentialOf q (G x)) S :=
    ((compact_coulomb_C4 hq hc).continuous.comp hG).continuousOn.integrableOn_compact hS
  have he : (fun x => ∫ y, ‖q y*Coulomb.coulombKernel (y-G x)‖) =
      (fun x => NeutralAtom.potentialOf q (G x)) := by
    funext x
    rw [compact_coulomb_eval_eq]
    apply integral_congr_ae
    filter_upwards [] with y
    exact Real.norm_of_nonneg (mul_nonneg (hpos y) (Coulomb.coulombKernel_nonneg _))
  change Integrable (fun x => ∫ y, ‖q y*Coulomb.coulombKernel (y-G x)‖) (volume.restrict S)
  rw [he]
  exact hi

theorem compact_source_transport_pairing {q : Position → ℝ}
    (hq : ContDiff ℝ 4 q) (hc : HasCompactSupport q) (hpos : ∀ y, 0 ≤ q y)
    {S : Set Position} (hS : IsCompact S) {G : Position → Position} (hG : Continuous G) :
    (∫ x in S, NeutralAtom.potentialOf q (G x)) =
      ∫ y, q y*(∫ x in S, Coulomb.coulombKernel (y-G x)) := by
  have hi := compact_source_transport_integrable hq hc hpos hS hG
  simp_rw [compact_coulomb_eval_eq]
  rw [integral_integral_swap hi]
  apply integral_congr_ae
  filter_upwards [] with y
  exact integral_const_mul _ _

theorem gridNuclearPotential_pairing {q : Position → ℝ}
    (hq : Continuous q) (hc : HasCompactSupport q)
    {ι : Type*} [Fintype ι] (index : ι → Fin 3 → ℤ)
    (G : Position → Position) (rho h : ℝ) :
    (∫ y, gridNuclearPotential index G rho h y*q y) =
      -rho*∑ i, positionCellGauss (gaussCellCenter h (index i)) h
        (fun x => NeutralAtom.potentialOf q (G x)) := by
  have hi (a : ι × (Fin 3 → Fin 2)) : Integrable (fun y =>
      Coulomb.coulombKernel (y-G (gaussLatticePoint h (gridGaussIndex index a)))*q y) := by
    convert compact_coulomb_eval_integrable hq hc (G (gaussLatticePoint h (gridGaussIndex index a))) using 1
    all_goals try with_reducible_and_instances rfl
    funext y
    ring
  calc
    _ = -(rho*h^3/8)*∑ a : ι × (Fin 3 → Fin 2),
        NeutralAtom.potentialOf q (G (gaussLatticePoint h (gridGaussIndex index a))) := by
      simp only [gridNuclearPotential,mul_assoc,Finset.sum_mul]
      rw [integral_const_mul,integral_finsetSum Finset.univ (fun a _ => hi a)]
      congr 1
      apply Finset.sum_congr rfl
      intro a _
      rw [compact_coulomb_eval_eq]
      apply integral_congr_ae
      filter_upwards [] with y
      ring
    _ = _ := by
      simp only [gaussCell_quadrature_lattice,Fintype.sum_prod_type,gridGaussIndex,← Finset.mul_sum]
      ring

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_CompactNuclearPairing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Identification of the compact-source cubature error with the actual
nuclear matrix element, including the manufactured continuous potential. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

theorem gridNuclearPotential_mul_integrable {q : Position → ℝ}
    (hq : Continuous q) (hc : HasCompactSupport q)
    {ι : Type*} [Fintype ι] (index : ι → Fin 3 → ℤ)
    (G : Position → Position) (rho h : ℝ) :
    Integrable (fun y => gridNuclearPotential index G rho h y*q y) := by
  have hi (a : ι × (Fin 3 → Fin 2)) : Integrable (fun y =>
      Coulomb.coulombKernel (y-G (gaussLatticePoint h (gridGaussIndex index a)))*q y) := by
    convert compact_coulomb_eval_integrable hq hc (G (gaussLatticePoint h (gridGaussIndex index a))) using 1
    all_goals try with_reducible_and_instances rfl
    funext y
    ring
  convert (integrable_finsetSum Finset.univ (fun a _ => hi a)).const_mul (-(rho*h^3/8)) using 1
  all_goals try with_reducible_and_instances rfl
  funext y
  simp only [gridNuclearPotential,Finset.sum_mul,mul_assoc]

theorem manufactured_compact_nuclear_pairing (hpublished : PublishedC4FlowInput)
    {rho H S h : ℝ} (hrho : 0 < rho) (hH : 0 ≤ H) (hS : 0 ≤ S) (hh : 0 < h)
    (V : Position → ℝ) (hV : ContDiff ℝ 6 V) (hcV : HasCompactSupport V)
    (hcharge : ∀ x, |manufacturedCharge V x| ≤ rho/2)
    (hsupport : tsupport V ⊆ slabDomain H S)
    (G : Position → ℝ → Position) (hflow : IsUnitTimeFlow (moserVelocity rho V) G)
    (hbij : Function.Bijective (fun x => G x 1))
    (hfix : ∀ x, x ∉ tsupport V → G x 1 = x) (hG : Continuous (fun x => G x 1))
    {ι : Type*} [Fintype ι] (index : ι → Fin 3 → ℤ) (hindex : Function.Injective index)
    (hcover : (⋃ i, positionCube (gaussCellCenter h (index i)) h) = slabDomain H S)
    {q : Position → ℝ} (hq : ContDiff ℝ 4 q) (hcq : HasCompactSupport q)
    (hpos : ∀ y, 0 ≤ q y) :
    (∫ y, (gridNuclearPotential index (fun x => G x 1) rho h y-
        (slabPotential rho H S y+V y))*q y) =
      -rho*((∑ i, positionCellGauss (gaussCellCenter h (index i)) h
        (fun x => NeutralAtom.potentialOf q (G x 1)))-
        ∑ i, positionCellIntegral (gaussCellCenter h (index i)) h
        (fun x => NeutralAtom.potentialOf q (G x 1))) := by
  have hsub (i : ι) : positionCube (gaussCellCenter h (index i)) h ⊆ slabDomain H S := by
    rw [← hcover]
    exact Set.subset_iUnion_of_subset i (fun _ hx => hx)
  have hkernel (y : Position) := moser_coulomb_integrableOn hpublished hrho hH hS
    V hV hcharge hsupport G hflow hbij hfix y
  have hsum (f : Position → ℝ) (hf : IntegrableOn f (slabDomain H S)) :
      (∑ i, positionCellIntegral (gaussCellCenter h (index i)) h f) =
        ∫ x in slabDomain H S, f x := by
    simp_rw [positionCellIntegral_eq_setIntegral _ hh.le _ (hf.mono_set (hsub _))]
    exact grid_cell_integral_sum_eq index hindex hh hcover f hf
  have hpoint (y : Position) :
      -rho*(∫ x in slabDomain H S, Coulomb.coulombKernel (y-G x 1)) = slabPotential rho H S y+V y := by
    rw [← hsum _ (hkernel y)]
    exact moser_grid_potential hpublished hrho hH hS hh V hV hcV hcharge hsupport
      G hflow hbij hfix index hindex hcover y
  have hiPot : IntegrableOn (fun x => NeutralAtom.potentialOf q (G x 1)) (slabDomain H S) :=
    ((compact_coulomb_C4 hq hcq).continuous.comp hG).continuousOn.integrableOn_compact
      (slabDomain_isCompact hH hS)
  have hcontinuous : (∫ y, (slabPotential rho H S y+V y)*q y) =
      -rho*(∑ i, positionCellIntegral (gaussCellCenter h (index i)) h
        (fun x => NeutralAtom.potentialOf q (G x 1))) := by
    rw [hsum _ hiPot,compact_source_transport_pairing hq hcq hpos (slabDomain_isCompact hH hS) hG,
      ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with y
    rw [← hpoint y]
    ring
  have hPi : Integrable (fun y => (slabPotential rho H S y+V y)*q y) :=
    (((slabPotential_continuous hrho.le hH hS).add hV.continuous).mul hq.continuous).integrable_of_hasCompactSupport
      hcq.mul_left
  simp_rw [sub_mul]
  rw [integral_sub (gridNuclearPotential_mul_integrable hq.continuous hcq index (fun x => G x 1) rho h) hPi,
    gridNuclearPotential_pairing hq.continuous hcq,hcontinuous]
  ring

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_GaussianJetBounds
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform fourth-order bounds for the actual normalized transverse
Gaussian. Polynomial Gaussian moments bound each explicit derivative. -/

noncomputable section
namespace ContinuumCoulomb

theorem power_exponential_bound (k : ℕ) {a t : ℝ} (ha : 0 < a) (ht : 0 ≤ t) :
    t^k*Real.exp (-a*t) ≤ (k.factorial:ℝ)/a^k := by
  have hf : 0 < (k.factorial:ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos k)
  have he := Real.pow_div_factorial_le_exp (a*t) (mul_nonneg ha.le ht) k
  have hid : ((a*t)^k/(k.factorial:ℝ))*((k.factorial:ℝ)/a^k) = t^k := by
    rw [mul_pow]
    field_simp
  have hb := mul_le_mul_of_nonneg_right he (show 0 ≤ (k.factorial:ℝ)/a^k by positivity)
  rw [hid] at hb
  have hb' := mul_le_mul_of_nonneg_right hb (Real.exp_pos (-a*t)).le
  have hc : (Real.exp (a*t)*((k.factorial:ℝ)/a^k))*Real.exp (-a*t) = (k.factorial:ℝ)/a^k := by
    rw [mul_right_comm,← Real.exp_add]
    simp
  exact hb'.trans_eq hc

theorem verticalMode_monomial_bound {freq : ℝ} (hfreq : 0 < freq) (k : ℕ) (z : ℝ) :
    |z|^k*‖verticalMode freq z‖ ≤
      (1+(k.factorial:ℝ)/(freq/2)^k)/Real.sqrt (Real.sqrt (Real.pi/freq)) := by
  have hd : 0 < Real.sqrt (Real.sqrt (Real.pi/freq)) := by positivity
  have hp : |z|^k ≤ 1+z^(2*k) := by
    by_cases hz : |z| ≤ 1
    · have ht := pow_le_pow_left₀ (abs_nonneg z) hz k
      simp only [one_pow] at ht
      linarith [pow_nonneg (sq_nonneg z) k,show z^(2*k) = (z^2)^k by rw [pow_mul]]
    · have ht := pow_le_pow_right₀ (le_of_not_ge hz) (show k ≤ 2*k by omega)
      rw [pow_mul,sq_abs,← pow_mul] at ht
      linarith
  have hg := power_exponential_bound k (show 0 < freq/2 by positivity) (sq_nonneg z)
  have hh := mul_le_mul_of_nonneg_right hp (Real.exp_pos (-(freq/2)*z^2)).le
  have he : Real.exp (-(freq/2)*z^2) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg z])
  have hb : |z|^k*Real.exp (-(freq/2)*z^2) ≤ 1+(k.factorial:ℝ)/(freq/2)^k := by
    rw [add_mul,one_mul] at hh
    rw [← pow_mul] at hg
    linarith
  rw [Real.norm_of_nonneg (verticalMode_positive hfreq z).le,verticalMode]
  have harg : -freq*z^2/2 = -(freq/2)*z^2 := by ring
  rw [harg,← mul_div_assoc]
  exact div_le_div_of_nonneg_right hb hd.le

theorem verticalMode_third_hasDerivAt (freq z : ℝ) :
    HasDerivAt (deriv (deriv (verticalMode freq)))
      ((3*freq^2*z-freq^3*z^3)*verticalMode freq z) z := by
  rw [show deriv (deriv (verticalMode freq)) =
    (fun x => (freq^2*x^2-freq)*verticalMode freq x) from funext (verticalMode_second_deriv freq)]
  convert (((((hasDerivAt_id z).pow 2).const_mul (freq^2)).sub_const freq).mul
    (verticalMode_hasDerivAt freq z)) using 1 <;> first | (with_reducible_and_instances rfl) | ((try funext x) <;>
    ((try simp only [id_eq,Pi.mul_apply,Pi.pow_apply,Nat.cast_ofNat,Nat.reduceSub,pow_one,mul_one]); all_goals ring))

theorem verticalMode_third_deriv (freq z : ℝ) :
    deriv (deriv (deriv (verticalMode freq))) z =
      (3*freq^2*z-freq^3*z^3)*verticalMode freq z :=
  (verticalMode_third_hasDerivAt freq z).deriv

theorem verticalMode_fourth_hasDerivAt (freq z : ℝ) :
    HasDerivAt (deriv (deriv (deriv (verticalMode freq))))
      ((3*freq^2-6*freq^3*z^2+freq^4*z^4)*verticalMode freq z) z := by
  rw [show deriv (deriv (deriv (verticalMode freq))) =
    (fun x => (3*freq^2*x-freq^3*x^3)*verticalMode freq x) from funext (verticalMode_third_deriv freq)]
  convert ((((hasDerivAt_id z).const_mul (3*freq^2)).sub
    (((hasDerivAt_id z).pow 3).const_mul (freq^3))).mul
    (verticalMode_hasDerivAt freq z)) using 1 <;> first | (with_reducible_and_instances rfl) | ((try funext x) <;>
    ((try simp only [id_eq,Pi.sub_apply,Pi.mul_apply,Pi.pow_apply,Nat.cast_ofNat,Nat.reduceSub,mul_one]); all_goals ring))

theorem verticalMode_fourth_deriv (freq z : ℝ) :
    deriv (deriv (deriv (deriv (verticalMode freq)))) z =
      (3*freq^2-6*freq^3*z^2+freq^4*z^4)*verticalMode freq z :=
  (verticalMode_fourth_hasDerivAt freq z).deriv

private theorem verticalMode_iteratedDeriv (freq z : ℝ) (k : Fin 5) :
    iteratedDeriv k.val (verticalMode freq) z =
      (∑ j : Fin 5, verticalHermiteCoeffs freq k j*z^(j:ℕ))*verticalMode freq z := by
  fin_cases k <;>
    simp [verticalHermiteCoeffs,Fin.sum_univ_succ,iteratedDeriv_succ,iteratedDeriv_zero,
      verticalMode_deriv,verticalMode_second_deriv,verticalMode_third_deriv,verticalMode_fourth_deriv] <;> ring_nf <;> simp

theorem vertical_mode_jets_bounded {freq : ℝ} (hfreq : 0 < freq) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ k : ℕ, k ≤ 4 → ∀ z,
      ‖iteratedFDeriv ℝ k (verticalMode freq) z‖ ≤ B := by
  let P (k : Fin 5) : ℝ :=
    (1+(k.val.factorial:ℝ)/(freq/2)^k.val)/Real.sqrt (Real.sqrt (Real.pi/freq))
  have hP (k : Fin 5) : 0 ≤ P k := by dsimp [P]; positivity
  let M := ∑ k : Fin 5, P k
  have hM : 0 ≤ M := Finset.sum_nonneg (fun k _ => hP k)
  let A (k : Fin 5) : ℝ := ∑ j : Fin 5, |verticalHermiteCoeffs freq k j|
  have hA (k : Fin 5) : 0 ≤ A k := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  let B := M*(∑ k : Fin 5, A k)+1
  have hB : 1 ≤ B := by
    dsimp [B]
    have hs : 0 ≤ ∑ k : Fin 5, A k := Finset.sum_nonneg (fun k _ => hA k)
    nlinarith [mul_nonneg hM hs]
  refine ⟨B,hB,fun k hk z => ?_⟩
  let i : Fin 5 := ⟨k,by omega⟩
  have hm (j : Fin 5) : |z|^(j:ℕ)*‖verticalMode freq z‖ ≤ M :=
    (verticalMode_monomial_bound hfreq j.val z).trans
      (Finset.single_le_sum (fun j _ => hP j) (Finset.mem_univ j))
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  change ‖iteratedDeriv i.val (verticalMode freq) z‖ ≤ B
  rw [verticalMode_iteratedDeriv,norm_mul]
  calc
    _ ≤ (∑ j : Fin 5, ‖verticalHermiteCoeffs freq i j*z^(j:ℕ)‖)*‖verticalMode freq z‖ :=
      mul_le_mul_of_nonneg_right (norm_sum_le _ _) (norm_nonneg _)
    _ = ∑ j : Fin 5, |verticalHermiteCoeffs freq i j| *(|z|^(j:ℕ)*‖verticalMode freq z‖) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j _
      rw [norm_mul,Real.norm_eq_abs,norm_pow,Real.norm_eq_abs,mul_assoc]
    _ ≤ ∑ j : Fin 5, |verticalHermiteCoeffs freq i j| *M :=
      Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (hm j) (abs_nonneg _))
    _ = A i*M := (Finset.sum_mul _ _ _).symm
    _ ≤ (∑ j : Fin 5, A j)*M :=
      mul_le_mul_of_nonneg_right (Finset.single_le_sum (fun j _ => hA j) (Finset.mem_univ i)) hM
    _ ≤ B := by dsimp [B]; nlinarith

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_PlanarModeJets
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.planarHeatResolventPrimitive_zero _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform derivatives through order four of the manufactured planar
orbital. Derivatives are transferred to its fixed compact forcing. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

private theorem forcing_jet_compact (k : ℕ) (v : Fin k → PlanarPosition) :
    HasCompactSupport (fun x => iteratedFDeriv ℝ k planarForcing x v) :=
  (planarForcing_hasCompactSupport.iteratedFDeriv (𝕜 := ℝ) k).comp_left
    (g := fun T : ContinuousMultilinearMap ℝ (fun _ : Fin k => PlanarPosition) ℝ => T v)
    (by simp)

theorem planar_mode_jet_transfer : ∀ k : ℕ, k ≤ 4 → ∀ (v : Fin k → PlanarPosition) r,
    iteratedFDeriv ℝ k planarResolventMode r v =
      planarResolventOf (fun x => iteratedFDeriv ℝ k planarForcing x v) r := by
  intro k
  induction k with
  | zero =>
    intro _ v r
    simp only [iteratedFDeriv_zero_apply]
    rfl
  | succ k ih =>
    intro hk v r
    have hk7 : (k : WithTop ℕ∞) < 7 := by exact_mod_cast (show k < 7 by omega)
    have hm := planarResolventMode_C7.differentiable_iteratedFDeriv hk7
    have hf := planarForcing_C7.differentiable_iteratedFDeriv hk7
    have hr : ContDiff ℝ 1 (fun x => iteratedFDeriv ℝ k planarForcing x (Fin.tail v)) :=
      (ContinuousMultilinearMap.apply ℝ (fun _ : Fin k => PlanarPosition) ℝ (Fin.tail v)).contDiff.comp
        (planarForcing_C7.iteratedFDeriv_right (by exact_mod_cast (show 1+k ≤ 7 by omega)))
    rw [(hm r).iteratedFDeriv_succ_apply_left']
    have he : (fun x => iteratedFDeriv ℝ k planarResolventMode x (Fin.tail v)) =
        planarResolventOf (fun x => iteratedFDeriv ℝ k planarForcing x (Fin.tail v)) :=
      funext (ih (by omega) (Fin.tail v))
    rw [he]
    change planarPartial _ (v 0) r = _
    rw [planarResolventOf_partial hr (forcing_jet_compact k (Fin.tail v))]
    congr 1
    funext x
    exact ((hf x).iteratedFDeriv_succ_apply_left').symm

theorem planar_mode_jets_bounded :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ k : ℕ, k ≤ 4 → ∀ r,
      ‖iteratedFDeriv ℝ k planarResolventMode r‖ ≤ B := by
  have he (k : Fin 5) : ∃ A : ℝ, ∀ r,
      ‖iteratedFDeriv ℝ k.val planarForcing r‖ ≤ A :=
    (planarForcing_C7.continuous_iteratedFDeriv (by exact_mod_cast (show k.val ≤ 7 by omega))).bounded_above_of_compact_support
      (planarForcing_hasCompactSupport.iteratedFDeriv k.val)
  choose A hA using he
  let B := ∑ k : Fin 5, max (A k) 0
  have hB : 0 ≤ B := Finset.sum_nonneg (fun _ _ => le_max_right _ _)
  have hb (k : ℕ) (hk : k ≤ 4) (r : PlanarPosition) :
      ‖iteratedFDeriv ℝ k planarForcing r‖ ≤ B := by
    let j : Fin 5 := ⟨k,by omega⟩
    exact (hA j r).trans ((le_max_left _ _).trans
      (Finset.single_le_sum (fun _ _ => le_max_right _ _) (Finset.mem_univ j)))
  refine ⟨B+1,by linarith,fun k hk r => ?_⟩
  apply ContinuousMultilinearMap.opNorm_le_bound (by linarith)
  intro v
  rw [planar_mode_jet_transfer k hk]
  apply (planarResolventOf_bound (fun x => ?_) r).trans
  · exact mul_le_mul_of_nonneg_right (by linarith : B ≤ B+1)
      (Finset.prod_nonneg (fun _ _ => norm_nonneg _))
  · exact ((iteratedFDeriv ℝ k planarForcing x).le_opNorm v).trans
      (mul_le_mul_of_nonneg_right (hb k hk x) (Finset.prod_nonneg (fun _ _ => norm_nonneg _)))

theorem normalized_planar_mode_jets_bounded :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ k : ℕ, k ≤ 4 → ∀ r,
      ‖iteratedFDeriv ℝ k normalizedPlanarMode r‖ ≤ B := by
  obtain ⟨B,hB,hb⟩ := planar_mode_jets_bounded
  let a : ℝ := (Real.sqrt (∫ x, planarResolventMode x^2))⁻¹
  have he : normalizedPlanarMode = fun x => a • planarResolventMode x := by
    funext x
    simp only [normalizedPlanarMode,a,smul_eq_mul,div_eq_mul_inv,mul_comm]
  refine ⟨‖a‖*B+1,by nlinarith [mul_nonneg (norm_nonneg a) (show 0 ≤ B by linarith)],fun k hk r => ?_⟩
  rw [he,iteratedFDeriv_const_smul_apply'
    (planarResolventMode_C7.of_le (show (k : WithTop ℕ∞) ≤ 7 by exact_mod_cast (show k ≤ 7 by omega))).contDiffAt,
    norm_smul]
  exact (mul_le_mul_of_nonneg_left (hb k hk r) (norm_nonneg a)).trans (by linarith)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_OrbitalJetBounds
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform fourth-order bounds for the actual localized orbitals and
products used in the compressed nuclear coefficients. -/

noncomputable section
namespace ContinuumCoulomb

theorem fourJet_linear_comp {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (L : E →L[ℝ] F) (f : F → ℝ)
    (hf : ContDiff ℝ 4 f) {B D : ℝ} (hB : 0 ≤ B) (hD : 1 ≤ D) (hL : ‖L‖ ≤ D)
    (hb : ∀ k ≤ 4, ∀ x, ‖iteratedFDeriv ℝ k f x‖ ≤ B) {k : ℕ} (hk : k ≤ 4) (x : E) :
    ‖iteratedFDeriv ℝ k (f ∘ L) x‖ ≤ B*D^4 := by
  rw [L.iteratedFDeriv_comp_right hf x (by exact_mod_cast hk)]
  have h := (iteratedFDeriv ℝ k f (L x)).norm_compContinuousLinearMap_le (fun _ => L)
  simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin] at h
  calc
    _ ≤ ‖iteratedFDeriv ℝ k f (L x)‖*‖L‖^k := h
    _ ≤ B*D^k := mul_le_mul (hb k hk (L x))
      (pow_le_pow_left₀ (norm_nonneg L) hL k) (pow_nonneg (norm_nonneg L) k) hB
    _ ≤ B*D^4 := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hD hk) hB

theorem fourJet_mul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f g : E → ℝ} (hf : ContDiff ℝ 4 f) (hg : ContDiff ℝ 4 g)
    {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (ha : ∀ k ≤ 4, ∀ x, ‖iteratedFDeriv ℝ k f x‖ ≤ A)
    (hb : ∀ k ≤ 4, ∀ x, ‖iteratedFDeriv ℝ k g x‖ ≤ B)
    {k : ℕ} (hk : k ≤ 4) (x : E) :
    ‖iteratedFDeriv ℝ k (fun x => f x*g x) x‖ ≤ 16*A*B := by
  apply (norm_iteratedFDeriv_mul_le hf hg x (by exact_mod_cast hk)).trans
  calc
    _ ≤ ∑ i ∈ Finset.range (k+1), (k.choose i : ℝ)*A*B := by
      apply Finset.sum_le_sum
      intro i hi
      have hi' : i ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
      exact mul_le_mul (mul_le_mul_of_nonneg_left (ha i (hi'.trans hk) x) (Nat.cast_nonneg _))
        (hb (k-i) ((Nat.sub_le k i).trans hk) x) (norm_nonneg _)
        (mul_nonneg (Nat.cast_nonneg _) hA)
    _ = (2:ℝ)^k*A*B := by
      rw [← Finset.sum_mul,← Finset.sum_mul]
      congr 2
      exact_mod_cast Nat.sum_range_choose k
    _ ≤ 16*A*B := by
      apply mul_le_mul_of_nonneg_right _ hB
      apply mul_le_mul_of_nonneg_right _ hA
      exact (pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) hk).trans_eq (by norm_num)

theorem continuumLocalizedMode_jets_bounded {freq : ℝ} (hfreq : 0 < freq) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ u k, k ≤ 4 → ∀ x,
      ‖iteratedFDeriv ℝ k (continuumLocalizedMode freq u) x‖ ≤ B := by
  obtain ⟨A,hA,ha⟩ := normalized_planar_mode_jets_bounded
  obtain ⟨B,hB,hb⟩ := vertical_mode_jets_bounded hfreq
  let P := max 1 ‖wellPlanarProjection‖
  let Q := max 1 ‖wellVerticalProjection‖
  have hP : 1 ≤ P := le_max_left _ _
  have hQ : 1 ≤ Q := le_max_left _ _
  have hPA : 0 ≤ A*P^4 := by positivity
  have hQB : 0 ≤ B*Q^4 := by positivity
  refine ⟨16*(A*P^4)*(B*Q^4)+1,by nlinarith [mul_nonneg hPA hQB],?_⟩
  intro u k hk x
  let f : Position → ℝ := (fun r => normalizedPlanarMode (r-u)) ∘ wellPlanarProjection
  let g : Position → ℝ := verticalMode freq ∘ wellVerticalProjection
  have hf : ContDiff ℝ 4 f :=
    ((normalizedPlanarMode_C7.of_le (by norm_num)).comp (contDiff_id.sub contDiff_const)).comp
      wellPlanarProjection.contDiff
  have hg : ContDiff ℝ 4 g := ((verticalMode_smooth freq).of_le (by first | simp | exact_mod_cast le_top)).comp wellVerticalProjection.contDiff
  have hfa (j : ℕ) (hj : j ≤ 4) (y : Position) : ‖iteratedFDeriv ℝ j f y‖ ≤ A*P^4 := by
    apply fourJet_linear_comp wellPlanarProjection _
      ((normalizedPlanarMode_C7.of_le (by norm_num)).comp (contDiff_id.sub contDiff_const))
      (by linarith) hP (le_max_right _ _) _ hj y
    intro l hl r
    change ‖iteratedFDeriv ℝ l (fun x => normalizedPlanarMode (x-u)) r‖ ≤ A
    rw [iteratedFDeriv_comp_sub]
    exact ha l hl (r-u)
  have hgb (j : ℕ) (hj : j ≤ 4) (y : Position) : ‖iteratedFDeriv ℝ j g y‖ ≤ B*Q^4 :=
    fourJet_linear_comp wellVerticalProjection _ ((verticalMode_smooth freq).of_le (by first | simp | exact_mod_cast le_top))
      (by linarith) hQ (le_max_right _ _) hb hj y
  exact (fourJet_mul hf hg hPA hQB hfa hgb hk x).trans (by linarith)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_OrbitalCutoff
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Expanding smooth cutoffs for the actual orbitals. Their first four
jets are bounded independently of the radius and center. -/

noncomputable section
open MeasureTheory
open scoped ContDiff
namespace ContinuumCoulomb

theorem orbitalCutoff_smooth (R : ℝ) (u : PlanarPosition) :
    ContDiff ℝ ∞ (orbitalCutoff R u) :=
  orbitalCutoffBump.contDiff.comp ((contDiff_id.sub contDiff_const).const_smul _)

theorem orbitalCutoff_nonnegative (R : ℝ) (u : PlanarPosition) (x : Position) :
    0 ≤ orbitalCutoff R u x := orbitalCutoffBump.nonneg

theorem orbitalCutoff_le_one (R : ℝ) (u : PlanarPosition) (x : Position) :
    orbitalCutoff R u x ≤ 1 := orbitalCutoffBump.le_one

theorem orbitalCutoff_eq_one {R : ℝ} (hR : 0 < R) (u : PlanarPosition)
    {x : Position} (hx : ‖x-planarCenter u‖ ≤ R) : orbitalCutoff R u x = 1 := by
  apply orbitalCutoffBump.one_of_mem_closedBall
  change dist (R⁻¹ • (x-planarCenter u)) 0 ≤ 1
  rw [dist_zero_right,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hR)]
  rw [← div_eq_inv_mul]
  exact (div_le_one hR).mpr hx

theorem orbitalCutoff_support {R : ℝ} (hR : 0 < R) (u : PlanarPosition) :
    tsupport (orbitalCutoff R u) ⊆ Metric.closedBall (planarCenter u) (2*R) := by
  apply closure_minimal _ Metric.isClosed_closedBall
  intro x hx
  by_contra hn
  apply hx
  apply orbitalCutoffBump.zero_of_le_dist
  change 2 ≤ dist (R⁻¹ • (x-planarCenter u)) 0
  rw [dist_zero_right,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hR)]
  rw [← div_eq_inv_mul]
  have hh : 2*R < ‖x-planarCenter u‖ := by
    simpa only [Metric.mem_closedBall,dist_eq_norm,not_le] using hn
  exact (le_div_iff₀ hR).mpr hh.le

theorem orbitalCutoff_hasCompactSupport {R : ℝ} (hR : 0 < R) (u : PlanarPosition) :
    HasCompactSupport (orbitalCutoff R u) :=
  (isCompact_closedBall (planarCenter u) (2*R)).of_isClosed_subset (isClosed_tsupport _)
    (orbitalCutoff_support hR u)

theorem orbitalCutoff_jets_bounded :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ R, 1 ≤ R → ∀ u k, k ≤ 4 → ∀ x,
      ‖iteratedFDeriv ℝ k (orbitalCutoff R u) x‖ ≤ B := by
  obtain ⟨B,hB,hb⟩ := orbitalCutoffBump.hasCompactSupport.exists_bound_iteratedFDeriv
    (𝕜 := ℝ) orbitalCutoffBump.contDiff 4
  refine ⟨B+1,by linarith,?_⟩
  intro R hR u k hk x
  have hR0 : 0 < R := lt_of_lt_of_le zero_lt_one hR
  let L : Position →L[ℝ] Position := R⁻¹ • ContinuousLinearMap.id ℝ Position
  have hL : ‖L‖ ≤ 1 := by
    dsimp [L]
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hR0),ContinuousLinearMap.norm_id]
    simpa only [mul_one] using inv_le_one_of_one_le₀ hR
  change ‖iteratedFDeriv ℝ k (fun y => (orbitalCutoffBump ∘ L) (y-planarCenter u)) x‖ ≤ B+1
  rw [iteratedFDeriv_comp_sub]
  have h := fourJet_linear_comp L orbitalCutoffBump (orbitalCutoffBump.contDiff : ContDiff ℝ 4 (orbitalCutoffBump : Position → ℝ))
    hB (show (1:ℝ) ≤ 1 from le_rfl) hL hb hk (x-planarCenter u)
  simpa only [one_pow,mul_one] using h.trans (show B*1^4 ≤ B+1 by nlinarith)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_CompactOrbitalDensity
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compact cutoff densities for compressed nuclear matrix elements. The
fourth-order source bounds grow only cubically in the cutoff radius. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

theorem compactOrbitalDensity_nonnegative {freq : ℝ} (hfreq : 0 < freq)
    (R : ℝ) (u v : PlanarPosition) (x : Position) :
    0 ≤ compactOrbitalDensity freq R u v x :=
  mul_nonneg (orbitalCutoff_nonnegative R u x)
    (mul_nonneg (continuumLocalizedMode_positive hfreq u x).le
      (continuumLocalizedMode_positive hfreq v x).le)

theorem compactOrbitalDensity_C4 (freq R : ℝ) (u v : PlanarPosition) :
    ContDiff ℝ 4 (compactOrbitalDensity freq R u v) :=
  ((orbitalCutoff_smooth R u).of_le (by first | simp | exact_mod_cast le_top)).mul
    (((continuumLocalizedMode_C7 freq u).of_le (by norm_num)).mul
      ((continuumLocalizedMode_C7 freq v).of_le (by norm_num)))

theorem compactOrbitalDensity_support (freq : ℝ) {R : ℝ} (hR : 0 < R) (u v : PlanarPosition) :
    tsupport (compactOrbitalDensity freq R u v) ⊆ Metric.closedBall (planarCenter u) (2*R) :=
  tsupport_mul_subset_left.trans (orbitalCutoff_support hR u)

theorem compactOrbitalDensity_hasCompactSupport (freq : ℝ) {R : ℝ} (hR : 0 < R)
    (u v : PlanarPosition) : HasCompactSupport (compactOrbitalDensity freq R u v) :=
  (orbitalCutoff_hasCompactSupport hR u).mul_right

private theorem ball_supported_jet_integral {F : Type*} [NormedAddCommGroup F]
    {q : Position → F} {B R : ℝ}
    (hB : 0 ≤ B) (hR : 0 ≤ R) (u : PlanarPosition)
    (hs : tsupport q ⊆ Metric.closedBall (planarCenter u) (2*R))
    (hb : ∀ x, ‖q x‖ ≤ B) : (∫ x, ‖q x‖) ≤ 64*B*R^3 := by
  let S := Metric.closedBall (planarCenter u) (2*R)
  have he : (∫ x in S, ‖q x‖) = ∫ x, ‖q x‖ :=
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
      rw [image_eq_zero_of_notMem_tsupport (fun hsx => hx (hs hsx)),norm_zero])
  have h := norm_setIntegral_le_of_norm_le_const (μ := volume) (f := fun x => ‖q x‖)
    (s := S) (isCompact_closedBall _ _).measure_lt_top (fun x _ => by simpa using hb x)
  rw [he] at h
  have hvol : volume.real S = (2*R)^3*(Real.pi*4/3) := by
    simp only [S,Measure.real,EuclideanSpace.volume_closedBall_fin_three,
      ENNReal.toReal_mul,ENNReal.toReal_pow,ENNReal.toReal_ofReal (by positivity : 0 ≤ 2*R),
      ENNReal.toReal_ofReal (by positivity : 0 ≤ Real.pi*4/3)]
  rw [hvol] at h
  have hpi : Real.pi*4/3 ≤ 8 := by linarith [Real.pi_lt_four]
  calc
    _ ≤ ‖∫ x, ‖q x‖‖ := le_abs_self _
    _ ≤ B*((2*R)^3*(Real.pi*4/3)) := h
    _ ≤ B*((2*R)^3*8) := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hpi (by positivity)) hB
    _ = _ := by ring

theorem compactOrbitalDensity_jets_bounded {freq : ℝ} (hfreq : 0 < freq) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ R, 1 ≤ R → ∀ u v k, k ≤ 4 →
      (∀ x, ‖iteratedFDeriv ℝ k (compactOrbitalDensity freq R u v) x‖ ≤ B) ∧
      (∫ x, ‖iteratedFDeriv ℝ k (compactOrbitalDensity freq R u v) x‖) ≤ 64*B*R^3 := by
  obtain ⟨A,hA,ha⟩ := continuumLocalizedMode_jets_bounded hfreq
  obtain ⟨C,hC,hc⟩ := orbitalCutoff_jets_bounded
  let B := 16*C*(16*A*A)+1
  have hA0 : 0 ≤ A := by linarith
  have hC0 : 0 ≤ C := by linarith
  have hB : 1 ≤ B := by
    dsimp [B]
    have hn : 0 ≤ 16*C*(16*A*A) := by positivity
    linarith
  refine ⟨B,hB,fun R hR u v k hk => ?_⟩
  have hpair (j : ℕ) (hj : j ≤ 4) (x : Position) :
      ‖iteratedFDeriv ℝ j (fun y => continuumLocalizedMode freq u y*continuumLocalizedMode freq v y) x‖ ≤
        16*A*A :=
    fourJet_mul ((continuumLocalizedMode_C7 freq u).of_le (by norm_num))
      ((continuumLocalizedMode_C7 freq v).of_le (by norm_num)) hA0 hA0 (ha u) (ha v) hj x
  have hb (x : Position) : ‖iteratedFDeriv ℝ k (compactOrbitalDensity freq R u v) x‖ ≤ B := by
    exact (fourJet_mul ((orbitalCutoff_smooth R u).of_le (by first | simp | exact_mod_cast le_top))
      (((continuumLocalizedMode_C7 freq u).of_le (by norm_num)).mul
        ((continuumLocalizedMode_C7 freq v).of_le (by norm_num))) hC0 (by positivity)
      (hc R hR u) hpair hk x).trans (by dsimp [B]; linarith)
  refine ⟨hb,?_⟩
  apply ball_supported_jet_integral (by linarith) (by linarith) u _ hb
  exact (tsupport_iteratedFDeriv_subset k).trans
    (compactOrbitalDensity_support freq (by linarith) u v)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_CompactCoulombJets
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Derivatives through order four of a compact source's Coulomb field.
The pole stays in the integrable kernel; all derivatives land on the source. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

private theorem compact_derivative_eval {q : Position → ℝ} (hc : HasCompactSupport q)
    (k : ℕ) (v : Fin k → Position) :
    HasCompactSupport (fun x => iteratedFDeriv ℝ k q x v) := by
  exact (hc.iteratedFDeriv (𝕜 := ℝ) k).comp_left
    (g := fun T : ContinuousMultilinearMap ℝ (fun _ : Fin k => Position) ℝ => T v)
    (by simp)

theorem compact_coulomb_iteratedFDeriv {q : Position → ℝ}
    (hq : ContDiff ℝ 4 q) (hc : HasCompactSupport q) :
    ∀ k : ℕ, k ≤ 4 → ∀ (v : Fin k → Position) (y : Position),
      iteratedFDeriv ℝ k (NeutralAtom.potentialOf q) y v =
        NeutralAtom.potentialOf (fun x => iteratedFDeriv ℝ k q x v) y := by
  intro k
  induction k with
  | zero =>
    intro _ v y
    simp only [iteratedFDeriv_zero_apply]
  | succ k ih =>
    intro hk v y
    have hk4 : k < (4 : WithTop ℕ∞) := by exact_mod_cast (by omega : k < 4)
    have hp := (compact_coulomb_C4 hq hc).differentiable_iteratedFDeriv hk4
    have hq' := hq.differentiable_iteratedFDeriv hk4
    have hr : ContDiff ℝ 1 (fun x => iteratedFDeriv ℝ k q x (Fin.tail v)) :=
      (ContinuousMultilinearMap.apply ℝ (fun _ : Fin k => Position) ℝ (Fin.tail v)).contDiff.comp
        (hq.iteratedFDeriv_right (by exact_mod_cast (show 1+k ≤ 4 by omega)))
    have hs : HasCompactSupport (fun x => iteratedFDeriv ℝ k q x (Fin.tail v)) :=
      compact_derivative_eval hc k (Fin.tail v)
    rw [(hp y).iteratedFDeriv_succ_apply_left']
    have hid : (fun z => iteratedFDeriv ℝ k (NeutralAtom.potentialOf q) z (Fin.tail v)) =
        NeutralAtom.potentialOf (fun x => iteratedFDeriv ℝ k q x (Fin.tail v)) :=
      funext (ih (by omega) (Fin.tail v))
    rw [hid]
    change NeutralAtom.dirPartial _ (v 0) y = _
    rw [compact_coulomb_partial hr hs]
    congr 1
    funext x
    exact ((hq' x).iteratedFDeriv_succ_apply_left').symm

theorem compact_coulomb_jet_bound {q : Position → ℝ}
    (hq : ContDiff ℝ 4 q) (hc : HasCompactSupport q)
    {k : ℕ} (hk : k ≤ 4) {M : ℝ}
    (hM : ∀ x, ‖iteratedFDeriv ℝ k q x‖ ≤ M) (y : Position) :
    ‖iteratedFDeriv ℝ k (NeutralAtom.potentialOf q) y‖ ≤
      2*Real.pi*M+∫ x, ‖iteratedFDeriv ℝ k q x‖ := by
  let D := fun x => ‖iteratedFDeriv ℝ k q x‖
  have hd : Continuous D := (hq.continuous_iteratedFDeriv (by exact_mod_cast hk)).norm
  have hcD : HasCompactSupport D := (hc.iteratedFDeriv (𝕜 := ℝ) k).norm
  have hbound := compact_coulomb_bound hd hcD (fun x => by
    simpa only [D,Real.norm_of_nonneg (norm_nonneg _)] using hM x) y
  have hpot : 0 ≤ NeutralAtom.potentialOf D y :=
    integral_nonneg (fun x => mul_nonneg (NeutralAtom.coulombKernel_nonneg _) (norm_nonneg _))
  simp only [Real.norm_of_nonneg hpot] at hbound
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  apply ContinuousMultilinearMap.opNorm_le_bound (by positivity)
  intro v
  rw [compact_coulomb_iteratedFDeriv hq hc k hk]
  let P : ℝ := ∏ i, ‖v i‖
  have hP : 0 ≤ P := Finset.prod_nonneg (fun _ _ => norm_nonneg _)
  have hi : Integrable (fun x => NeutralAtom.coulombKernel (y-x)*D x) := by
    have hh := hcD.convolutionExists_right (ContinuousLinearMap.mul ℝ ℝ)
      NeutralAtom.locallyIntegrable_coulombKernel hd y
    change Integrable (fun x => NeutralAtom.coulombKernel x*D (y-x)) at hh
    simpa only [sub_sub_cancel] using hh.comp_sub_left y
  have hb := norm_integral_le_of_norm_le (hi.mul_const P) (Filter.Eventually.of_forall
    (fun x => show ‖NeutralAtom.coulombKernel (y-x)*iteratedFDeriv ℝ k q x v‖ ≤
        (NeutralAtom.coulombKernel (y-x)*D x)*P from by
      rw [norm_mul,Real.norm_of_nonneg (NeutralAtom.coulombKernel_nonneg _),mul_assoc]
      exact mul_le_mul_of_nonneg_left ((iteratedFDeriv ℝ k q x).le_opNorm v)
        (NeutralAtom.coulombKernel_nonneg _)))
  change ‖∫ x, NeutralAtom.coulombKernel (y-x)*iteratedFDeriv ℝ k q x v‖ ≤ _
  apply hb.trans
  rw [integral_mul_const]
  apply mul_le_mul_of_nonneg_right _ hP
  simpa only [D,norm_norm,NeutralAtom.potentialOf] using hbound

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_CompactSourceTransport
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Smooth compact orbital densities give a uniform transported-cell bound.
Cells on which the flow is the identity retain the sharper separated-source
bound, so only the compact exceptional region needs the uniform estimate. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

theorem compact_source_transported_cell_bound {q : Position → ℝ}
    (hq : ContDiff ℝ 4 q) (hc : HasCompactSupport q)
    {B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ k : ℕ, k ≤ 4 → ∀ x, ‖iteratedFDeriv ℝ k q x‖ ≤ B)
    (hi : ∀ k : ℕ, k ≤ 4 → (∫ x, ‖iteratedFDeriv ℝ k q x‖) ≤ B)
    (G : Position → Position) (hG : ContDiff ℝ 4 G) {D : ℝ} (_hD : 0 ≤ D)
    (hGD : ∀ x, ∀ k : ℕ, 1 ≤ k → k ≤ 4 → ‖iteratedFDeriv ℝ k G x‖ ≤ D^k)
    (b : Position) {h : ℝ} (hh : 0 ≤ h) :
    |positionCellGauss b h (fun x => NeutralAtom.potentialOf q (G x))-
      positionCellIntegral b h (fun x => NeutralAtom.potentialOf q (G x))| ≤
      24*((2*Real.pi+1)*B)*D^4*h^7 := by
  have hqC := compact_coulomb_C4 hq hc
  apply positionCellGauss_error _ (hqC.comp hG) b hh (by positivity)
  intro x _ y _ z _
  apply fourth_composite_norm_bound (NeutralAtom.potentialOf q) G _ hqC.contDiffAt hG
    (C := (2*Real.pi+1)*B) (D := D) ?_ (hGD _)
  intro k hk
  have ht := compact_coulomb_jet_bound hq hc hk (hb k hk) (G (cubePoint b (h/2) x y z))
  have hL := hi k hk
  nlinarith

private theorem cellGauss_congr_on_cube (b : Position) {h : ℝ} (hh : 0 ≤ h)
    (f g : Position → ℝ) (heq : ∀ x ∈ positionCube b h, f x = g x) :
    positionCellGauss b h f = positionCellGauss b h g := by
  unfold positionCellGauss
  congr 1
  apply gaussTensor3_congr_on
  intro x hx y hy z hz
  exact heq _ (cubePoint_mem_positionCube b hh hx hy hz)

private theorem cellIntegral_congr_on_cube (b : Position) {h : ℝ} (hh : 0 ≤ h)
    (f g : Position → ℝ) (heq : ∀ x ∈ positionCube b h, f x = g x) :
    positionCellIntegral b h f = positionCellIntegral b h g := by
  unfold positionCellIntegral
  congr 1
  apply unitCube_integral_congr
  intro x hx y hy z hz
  exact heq _ (cubePoint_mem_positionCube b hh hx hy hz)

theorem compact_source_unchanged_cell_bound :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (q : Position → ℝ), ContDiff ℝ 4 q → HasCompactSupport q →
      ∀ (G : Position → Position) (b : Position) (h r : ℝ), 0 ≤ h → 0 < r →
      (∀ x ∈ positionCube b h, G x = x) →
      (∀ x, q x ≠ 0 → ∀ y ∈ positionCube b h, r ≤ ‖y-x‖) →
      |positionCellGauss b h (fun x => NeutralAtom.potentialOf q (G x))-
        positionCellIntegral b h (fun x => NeutralAtom.potentialOf q (G x))| ≤
        (C*h^7/r^5)*(∫ x, ‖q x‖) := by
  obtain ⟨C,hC,hbound⟩ := compact_coulomb_far_cell_error
  refine ⟨C,hC,fun q hq hc G b h r hh hr hfix hsep => ?_⟩
  have heq (x : Position) (hx : x ∈ positionCube b h) :
      NeutralAtom.potentialOf q (G x) = NeutralAtom.potentialOf q x := by rw [hfix x hx]
  rw [cellGauss_congr_on_cube b hh _ _ heq,cellIntegral_congr_on_cube b hh _ _ heq]
  exact hbound q hq hc b h r hh hr hsep

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_InverseFifthCutoffGrid
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Far-grid inverse-fifth sums with the orbital cutoff radius retained.
The bound is independent of both box volume and mesh resolution. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

theorem inverseFifth_cutoff_cube_bound {h R : ℝ} (hh : 0 < h) (hR : 0 < R)
    (hhR : h ≤ R) (y b : Position) (hfar : 4*R ≤ ‖y-b‖) :
    h^3/‖y-b‖^5 ≤ 32*(∫ x in positionCube b h, inverseFifthTail R (y-x)) := by
  have hd : 0 < ‖y-b‖ := lt_of_lt_of_le (by positivity) hfar
  have hi := translatedInverseFifth_integrable y hR
  have he := setIntegral_mono_on
    (integrableOn_const (C := 1/‖y-b‖^5)
      ((positionCube_isCompact b hh.le).measure_lt_top (μ := volume)).ne)
    (hi.const_mul 32).integrableOn (positionCube_isClosed b h).measurableSet (fun x hx => ?_)
  · have hv : (volume.restrict (positionCube b h)).real Set.univ = h^3 := by
      simpa only [Measure.real,Measure.restrict_apply_univ] using positionCube_volume b hh.le
    simpa only [integral_const,smul_eq_mul,hv,integral_const_mul,
      div_eq_mul_inv,mul_one,one_mul] using he
  · have hn := positionCube_norm_sub_le hh.le hx
    have ha := norm_sub_le_norm_sub_add_norm_sub y x b
    have hu := (norm_sub_le_norm_sub_add_norm_sub y b x)
    rw [norm_sub_rev b x] at hu
    have hdx : R < ‖y-x‖ := by linarith
    have hupper : ‖y-x‖ ≤ 2*‖y-b‖ := by linarith
    rw [inverseFifthTail_eq_inv_pow _ hdx,mul_one_div]
    apply (div_le_div_iff₀ (pow_pos hd 5) (pow_pos (hR.trans hdx) 5)).mpr
    have hp := pow_le_pow_left₀ (norm_nonneg (y-x)) hupper 5
    nlinarith [show (2*‖y-b‖)^5 = 32*‖y-b‖^5 by ring]

theorem inverseFifth_cutoff_grid_sum {ι : Type*} [Fintype ι]
    (index : ι → Fin 3 → ℤ) (hindex : Function.Injective index)
    {h R : ℝ} (hh : 0 < h) (hR : 0 < R) (hhR : h ≤ R) (y : Position)
    (hfar : ∀ i, 4*R ≤ ‖y-gaussCellCenter h (index i)‖) :
    (∑ i, h^3/‖y-gaussCellCenter h (index i)‖^5) ≤ 64*Real.pi/R^2 := by
  calc
    _ ≤ ∑ i, 32*(∫ x in positionCube (gaussCellCenter h (index i)) h,
        inverseFifthTail R (y-x)) :=
      Finset.sum_le_sum (fun i _ => inverseFifth_cutoff_cube_bound hh hR hhR y _ (hfar i))
    _ = 32*(∑ i, ∫ x in positionCube (gaussCellCenter h (index i)) h,
        inverseFifthTail R (y-x)) := (Finset.mul_sum _ _ _).symm
    _ ≤ 32*(∫ x, inverseFifthTail R (y-x)) :=
      mul_le_mul_of_nonneg_left (grid_cell_integral_sum_le index hindex hh _
        (translatedInverseFifth_integrable y hR) (fun x => inverseFifthTail_nonneg R (y-x)))
        (by norm_num)
    _ = _ := by rw [translatedInverseFifth_integral y hR]; ring

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_CompactSourceGrid
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The fourth-order cell error for a compact orbital source, split into
cells near that source or the transport support and the remaining far cells. -/

noncomputable section
open MeasureTheory
open scoped Classical
namespace ContinuumCoulomb

theorem compact_source_grid_error :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (q : Position → ℝ), ContDiff ℝ 4 q → HasCompactSupport q →
      ∀ (B : ℝ), 0 ≤ B →
      (∀ k : ℕ, k ≤ 4 → ∀ x, ‖iteratedFDeriv ℝ k q x‖ ≤ B) →
      (∀ k : ℕ, k ≤ 4 → (∫ x, ‖iteratedFDeriv ℝ k q x‖) ≤ B) →
      ∀ (u : PlanarPosition) (R : ℝ), 0 < R →
      (∀ x, q x ≠ 0 → ‖x-planarCenter u‖ ≤ R) →
      ∀ (G : Position → Position), ContDiff ℝ 4 G →
      ∀ (E : Set Position), (∀ x, x ∉ E → G x = x) →
      ∀ (D : ℝ), 0 ≤ D →
      (∀ x, ∀ k : ℕ, 1 ≤ k → k ≤ 4 → ‖iteratedFDeriv ℝ k G x‖ ≤ D^k) →
      ∀ {ι : Type} [Fintype ι] (index : ι → Fin 3 → ℤ), Function.Injective index →
      ∀ (h : ℝ), 0 < h → h ≤ R →
      |(∑ i, positionCellGauss (gaussCellCenter h (index i)) h
          (fun x => NeutralAtom.potentialOf q (G x)))-
        (∑ i, positionCellIntegral (gaussCellCenter h (index i)) h
          (fun x => NeutralAtom.potentialOf q (G x)))| ≤
        24*((2*Real.pi+1)*B)*D^4*h^4*
          ((Fintype.card {i // sourceExceptionalCell E u R (gaussCellCenter h (index i)) h}:ℕ):ℝ)*h^3+
        2048*Real.pi*C*B*h^4/R^2 := by
  obtain ⟨C,hC,hfar⟩ := compact_source_unchanged_cell_bound
  refine ⟨C,hC,?_⟩
  intro q hq hc B hB hb hi u R hR hsupp G hG E hfix D hD hGD ι _ index hindex h hh hhR
  let p : ι → Prop := fun i => sourceExceptionalCell E u R (gaussCellCenter h (index i)) h
  let Q : ι → ℝ := fun i => positionCellGauss (gaussCellCenter h (index i)) h
    (fun x => NeutralAtom.potentialOf q (G x))
  let I : ι → ℝ := fun i => positionCellIntegral (gaussCellCenter h (index i)) h
    (fun x => NeutralAtom.potentialOf q (G x))
  have hnear : |(∑ i : {i // p i}, Q i.val)-(∑ i : {i // p i}, I i.val)| ≤
      24*((2*Real.pi+1)*B)*D^4*h^4*(Fintype.card {i // p i}:ℝ)*h^3 := by
    calc
      _ ≤ ∑ i : {i // p i}, |Q i.val-I i.val| := by
        rw [← Finset.sum_sub_distrib]
        exact Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : {i // p i}, 24*((2*Real.pi+1)*B)*D^4*h^7 :=
        Finset.sum_le_sum (fun i _ => compact_source_transported_cell_bound hq hc hB hb hi
          G hG hD hGD _ hh.le)
      _ = _ := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]; ring
  have hfi : Function.Injective (fun i : {i // ¬p i} => index i.val) :=
    fun i j hij => Subtype.ext (hindex hij)
  have hdist (i : {i // ¬p i}) : 4*R ≤ ‖planarCenter u-gaussCellCenter h (index i.val)‖ := by
    exact (lt_of_not_ge (fun he => i.property (Or.inr he))).le
  have hfs (i : {i // ¬p i}) :
      |Q i.val-I i.val| ≤
        (32*C*h^7/‖planarCenter u-gaussCellCenter h (index i.val)‖^5)*B := by
    let b := gaussCellCenter h (index i.val)
    have hd : 0 < ‖planarCenter u-b‖ := lt_of_lt_of_le (by positivity) (hdist i)
    have hf := hfar q hq hc G b h (‖planarCenter u-b‖/2) hh.le (by positivity)
      (fun x hx => hfix x (fun he => i.property (Or.inl ⟨x,hx,he⟩))) (fun x hx y hy => by
        have hs := hsupp x hx
        have hn := positionCube_norm_sub_le hh.le hy
        have ht := norm_sub_le_norm_sub_add_norm_sub (planarCenter u) x b
        have ht' := norm_sub_le_norm_sub_add_norm_sub x y b
        rw [norm_sub_rev (planarCenter u) x] at ht
        rw [norm_sub_rev x y] at ht'
        have := hdist i
        change 4*R ≤ ‖planarCenter u-b‖ at this
        linarith)
    have hm : (∫ x, ‖q x‖) ≤ B := by simpa only [norm_iteratedFDeriv_zero] using hi 0 (by omega)
    apply hf.trans
    have hfac : 0 ≤ C*h^7/(‖planarCenter u-b‖/2)^5 := by positivity
    apply (mul_le_mul_of_nonneg_left hm hfac).trans_eq
    change C*h^7/(‖planarCenter u-b‖/2)^5*B = (32*C*h^7/‖planarCenter u-b‖^5)*B
    field_simp
    ring
  have hfarSum : |(∑ i : {i // ¬p i}, Q i.val)-(∑ i : {i // ¬p i}, I i.val)| ≤
      2048*Real.pi*C*B*h^4/R^2 := by
    calc
      _ ≤ ∑ i : {i // ¬p i}, |Q i.val-I i.val| := by
        rw [← Finset.sum_sub_distrib]
        exact Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i : {i // ¬p i}, (32*C*h^7/‖planarCenter u-gaussCellCenter h (index i.val)‖^5)*B :=
        Finset.sum_le_sum (fun i _ => hfs i)
      _ = (32*C*B*h^4)*(∑ i : {i // ¬p i}, h^3/‖planarCenter u-gaussCellCenter h (index i.val)‖^5) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ ≤ (32*C*B*h^4)*(64*Real.pi/R^2) :=
        mul_le_mul_of_nonneg_left (inverseFifth_cutoff_grid_sum _ hfi hh hR hhR _ hdist) (by positivity)
      _ = _ := by ring
  have heQ := Fintype.sum_subtype_add_sum_subtype p Q
  have heI := Fintype.sum_subtype_add_sum_subtype p I
  change |(∑ i, Q i)-(∑ i, I i)| ≤ _
  rw [← heQ,← heI]
  have ht := abs_add_le ((∑ i : {i // p i}, Q i.val)-(∑ i : {i // p i}, I i.val))
    ((∑ i : {i // ¬p i}, Q i.val)-(∑ i : {i // ¬p i}, I i.val))
  have he : ((∑ i : {i // p i}, Q i.val)+(∑ i : {i // ¬p i}, Q i.val))-
      ((∑ i : {i // p i}, I i.val)+(∑ i : {i // ¬p i}, I i.val)) =
      ((∑ i : {i // p i}, Q i.val)-(∑ i : {i // p i}, I i.val))+
      ((∑ i : {i // ¬p i}, Q i.val)-(∑ i : {i // ¬p i}, I i.val)) := by ring
  rw [he]
  exact ht.trans (add_le_add hnear hfarSum)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_OrbitalCellVolume
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Mesh cells near one localized orbital occupy a volume bounded by its
cutoff radius, independently of the surrounding slab's horizontal area. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

theorem orbital_near_cell_volume {ι : Type*} [Fintype ι]
    (index : ι → Fin 3 → ℤ) (hindex : Function.Injective index)
    {h R : ℝ} (hh : 0 < h) (hR : 0 ≤ R) (u : PlanarPosition)
    (hnear : ∀ i, ‖gaussCellCenter h (index i)-planarCenter u‖ ≤ R) :
    (Fintype.card ι:ℝ)*h^3 ≤ 8*(R+2*h)^3 := by
  let A : ι → Set Position := fun i => positionOpenCube (gaussCellCenter h (index i)) h
  have hb (i : ι) : gaussCellCenter h (index i) ∈ wellCoverBox u R R := by
    apply mem_wellCoverBox.mpr
    have hc (j : Fin 3) := (PiLp.norm_apply_le
      (gaussCellCenter h (index i)-planarCenter u) j).trans (hnear i)
    have h0 : planarCenter u 0 = u 0 := by
      simpa only [planarCenter,ContinuousLinearEquiv.apply_symm_apply] using
        (positionSplitCoordinates_fst_zero (planarCenter u)).symm
    have h1 : planarCenter u 1 = u 1 := by
      simpa only [planarCenter,ContinuousLinearEquiv.apply_symm_apply] using
        (positionSplitCoordinates_fst_one (planarCenter u)).symm
    have h2 : planarCenter u 2 = 0 := by
      simpa only [planarCenter,ContinuousLinearEquiv.apply_symm_apply] using
        (positionSplitCoordinates_snd (planarCenter u)).symm
    exact ⟨by simpa only [PiLp.sub_apply,h0,Real.norm_eq_abs] using hc 0,
      by simpa only [PiLp.sub_apply,h1,Real.norm_eq_abs] using hc 1,
      by simpa only [PiLp.sub_apply,h2,sub_zero,Real.norm_eq_abs] using hc 2⟩
  have hsub : (⋃ i, A i) ⊆ wellCoverBox u (R+2*h) (R+2*h) := by
    intro x hx
    obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hx
    exact cube_meets_wellCover_subset hh.le
      (mem_positionCube.mpr (fun _ => by simp; positivity)) (hb i)
      (positionOpenCube_subset _ _ hi)
  have hA : volume.real (⋃ i, A i) = (Fintype.card ι:ℝ)*h^3 := by
    rw [measureReal_iUnion_fintype
      (fun i j hij => grid_openCubes_disjoint hh (fun he => hij (hindex he)))
      (fun i => positionOpenCube_measurable _ _)
      (fun i => by
        rw [measure_congr (positionOpenCube_ae_eq (gaussCellCenter h (index i)) h)]
        exact (positionCube_isCompact _ hh.le).measure_ne_top)]
    simp only [positionOpenCube_volume _ hh.le,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  calc
    _ = volume.real (⋃ i, A i) := hA.symm
    _ ≤ volume.real (wellCoverBox u (R+2*h) (R+2*h)) :=
      measureReal_mono hsub (wellCoverBox_measure_ne_top _ _ _)
    _ = 8*(R+2*h)^3 := by
      rw [wellCoverBox_volume u (by positivity) (by positivity)]
      ring

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Reduction_SourceExceptionalVolume
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exceptional cells for a compact orbital source consist of the
manufactured well support together with one neighborhood of the orbital. -/

noncomputable section
open MeasureTheory
open scoped Classical
namespace ContinuumCoulomb

theorem source_exceptional_volume {ι : Type*} [Fintype ι]
    (index : ι → Fin 3 → ℤ) (hindex : Function.Injective index)
    {h R S : ℝ} (hh : 0 < h) (hh1 : h ≤ 1) (hR : 0 ≤ R) (hS : 1 ≤ S)
    (freq scale : ℝ) {m : ℕ} (u : Fin m → PlanarPosition) (v : PlanarPosition) :
    (Fintype.card {i // sourceExceptionalCell (tsupport (manufacturedWellField freq scale S u))
      v R (gaussCellCenter h (index i)) h}:ℝ)*h^3 ≤
      216*m*S+8*(4*R+2*h)^3 := by
  let a : ι → Prop := fun i => ∃ z ∈ positionCube (gaussCellCenter h (index i)) h,
    z ∈ tsupport (manufacturedWellField freq scale S u)
  let b : ι → Prop := fun i => ‖planarCenter v-gaussCellCenter h (index i)‖ ≤ 4*R
  have ha := exceptional_cell_volume_bound (fun i : {i // a i} => index i.val)
    (fun i j he => Subtype.ext (hindex he)) hh hh1 hS freq scale u (fun i => i.property)
  have hb := orbital_near_cell_volume (fun i : {i // b i} => index i.val)
    (fun i j he => Subtype.ext (hindex he)) (R := 4*R) hh (mul_nonneg (by norm_num) hR) v
    (fun i => by simpa only [b,norm_sub_rev] using i.property)
  have hcard : Fintype.card {i // a i ∨ b i} ≤
      Fintype.card {i // a i}+Fintype.card {i // b i} := by
    simp only [Fintype.card_subtype]
    have he : (Finset.univ.filter (fun i => a i ∨ b i)) =
        (Finset.univ.filter a) ∪ (Finset.univ.filter b) := by
      ext i
      simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_union]
    rw [he]
    exact Finset.card_union_le _ _
  have hcardR : (Fintype.card {i // a i ∨ b i}:ℝ) ≤
      (Fintype.card {i // a i}:ℝ)+(Fintype.card {i // b i}:ℝ) := by exact_mod_cast hcard
  have hs := mul_le_mul_of_nonneg_right hcardR (pow_nonneg hh.le 3)
  have he : Fintype.card {i // sourceExceptionalCell (tsupport (manufacturedWellField freq scale S u))
      v R (gaussCellCenter h (index i)) h} = Fintype.card {i // a i ∨ b i} :=
    Fintype.card_congr (Equiv.subtypeEquivRight (fun _ => Iff.rfl))
  rw [he]
  nlinarith only [hs,ha,hb]

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_ManufacturedCompactQuadrature
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fourth-order quadrature for a compact orbital density under the actual
manufactured transport. The bound depends on the compact source radius and
the well-support volume, and is independent of the horizontal slab area. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

theorem manufactured_compact_source_quadrature :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (q : Position → ℝ), ContDiff ℝ 4 q → HasCompactSupport q →
      ∀ (B : ℝ), 0 ≤ B →
      (∀ k : ℕ, k ≤ 4 → ∀ x, ‖iteratedFDeriv ℝ k q x‖ ≤ B) →
      (∀ k : ℕ, k ≤ 4 → (∫ x, ‖iteratedFDeriv ℝ k q x‖) ≤ B) →
      ∀ (v : PlanarPosition) (R : ℝ), 1 ≤ R →
      (∀ x, q x ≠ 0 → ‖x-planarCenter v‖ ≤ R) →
      ∀ (freq scale S : ℝ), 1 ≤ S → ∀ (m : ℕ) (u : Fin m → PlanarPosition),
      ∀ (G : Position → Position), ContDiff ℝ 4 G →
      (∀ x, x ∉ tsupport (manufacturedWellField freq scale S u) → G x = x) →
      ∀ (D : ℝ), 0 ≤ D →
      (∀ x, ∀ k : ℕ, 1 ≤ k → k ≤ 4 → ‖iteratedFDeriv ℝ k G x‖ ≤ D^k) →
      ∀ {ι : Type} [Fintype ι] (index : ι → Fin 3 → ℤ), Function.Injective index →
      ∀ (h : ℝ), 0 < h → h ≤ 1 →
      |(∑ i, positionCellGauss (gaussCellCenter h (index i)) h
          (fun x => NeutralAtom.potentialOf q (G x)))-
        (∑ i, positionCellIntegral (gaussCellCenter h (index i)) h
          (fun x => NeutralAtom.potentialOf q (G x)))| ≤
        (24*((2*Real.pi+1)*B)*D^4*(216*m*S+1728*R^3)+2048*Real.pi*C*B)*h^4 := by
  classical
  obtain ⟨C,hC,hgrid⟩ := compact_source_grid_error
  refine ⟨C,hC,?_⟩
  intro q hq hc B hB hb hi v R hR hsupp freq scale S hS m u G hG hfix D hD hGD
    ι _ index hindex h hh hh1
  have hR0 : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have hg := hgrid q hq hc B hB hb hi v R hR0 hsupp G hG
    (tsupport (manufacturedWellField freq scale S u)) hfix D hD hGD
    index hindex h hh (hh1.trans hR)
  have hv := source_exceptional_volume index hindex hh hh1 hR0.le hS freq scale u v
  have hvol : (Fintype.card {i // sourceExceptionalCell
      (tsupport (manufacturedWellField freq scale S u)) v R (gaussCellCenter h (index i)) h}:ℝ)*h^3 ≤
      216*m*S+1728*R^3 := by
    apply hv.trans
    have hsize : (4*R+2*h)^3 ≤ (6*R)^3 := by
      apply pow_le_pow_left₀ (by positivity)
      linarith
    nlinarith only [hsize]
  have hnearterm := mul_le_mul_of_nonneg_left hvol
    (show 0 ≤ 24*((2*Real.pi+1)*B)*D^4*h^4 by positivity)
  have hRpow : 1 ≤ R^2 := one_le_pow₀ hR
  have hfar : 2048*Real.pi*C*B*h^4/R^2 ≤ 2048*Real.pi*C*B*h^4 := by
    exact div_le_self (by positivity) hRpow
  apply hg.trans
  nlinarith only [hnearterm,hfar]

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_CompactOrbitalQuadrature
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The transported fourth-order rule applied to the actual compact
orbital transition density, with all source bounds discharged. -/

noncomputable section
namespace ContinuumCoulomb

theorem manufactured_compact_orbital_quadrature {freq : ℝ} (hfreq : 0 < freq) :
    ∃ B C : ℝ, 1 ≤ B ∧ 1 ≤ C ∧
      ∀ (R : ℝ), 1 ≤ R → ∀ (v w : PlanarPosition),
      ∀ (scale S : ℝ), 1 ≤ S → ∀ (m : ℕ) (u : Fin m → PlanarPosition),
      ∀ (G : Position → Position), ContDiff ℝ 4 G →
      (∀ x, x ∉ tsupport (manufacturedWellField freq scale S u) → G x = x) →
      ∀ (D : ℝ), 0 ≤ D →
      (∀ x, ∀ k : ℕ, 1 ≤ k → k ≤ 4 → ‖iteratedFDeriv ℝ k G x‖ ≤ D^k) →
      ∀ {ι : Type} [Fintype ι] (index : ι → Fin 3 → ℤ), Function.Injective index →
      ∀ (h : ℝ), 0 < h → h ≤ 1 →
      |(∑ i, positionCellGauss (gaussCellCenter h (index i)) h
          (fun x => NeutralAtom.potentialOf (compactOrbitalDensity freq R v w) (G x)))-
        (∑ i, positionCellIntegral (gaussCellCenter h (index i)) h
          (fun x => NeutralAtom.potentialOf (compactOrbitalDensity freq R v w) (G x)))| ≤
        (24*((2*Real.pi+1)*(64*B*R^3))*D^4*(216*m*S+13824*R^3)+
          2048*Real.pi*C*(64*B*R^3))*h^4 := by
  obtain ⟨B,hB,hb⟩ := compactOrbitalDensity_jets_bounded hfreq
  obtain ⟨C,hC,hquad⟩ := manufactured_compact_source_quadrature
  refine ⟨B,C,hB,hC,?_⟩
  intro R hR v w scale S hS m u G hG hfix D hD hGD ι _ index hindex h hh hh1
  have hR0 : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have hBR : B ≤ 64*B*R^3 := by
    have hpow : 1 ≤ R^3 := one_le_pow₀ hR
    have hp := mul_le_mul_of_nonneg_left hpow (show 0 ≤ B by linarith)
    nlinarith
  have he := hquad (compactOrbitalDensity freq R v w)
    (compactOrbitalDensity_C4 freq R v w) (compactOrbitalDensity_hasCompactSupport freq hR0 v w)
    (64*B*R^3) (by positivity)
    (fun k hk x => ((hb R hR v w k hk).1 x).trans hBR)
    (fun k hk => (hb R hR v w k hk).2) v (2*R) (by linarith)
    (fun x hx => by
      simpa only [Metric.mem_closedBall,dist_eq_norm] using
        compactOrbitalDensity_support freq hR0 v w (subset_tsupport _ hx))
    freq scale S hS m u G hG hfix D hD hGD index hindex h hh hh1
  convert he using 1
  all_goals try with_reducible_and_instances rfl
  ring

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_CompactOrbitalNuclearError
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fourth-order nuclear replacement for the actual cutoff orbital
transition densities, with every analytic source estimate discharged. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

theorem manufactured_compact_orbital_nuclear_error (hpublished : PublishedC4FlowInput)
    {freq : ℝ} (hfreq : 0 < freq) :
    ∃ B C : ℝ, 1 ≤ B ∧ 1 ≤ C ∧
      ∀ (R : ℝ), 1 ≤ R → ∀ (v w : PlanarPosition),
      ∀ (rho H S scale : ℝ), 0 < rho → 0 ≤ H → 1 ≤ S →
      ∀ (m : ℕ) (u : Fin m → PlanarPosition),
      (∀ x, |manufacturedCharge (manufacturedWellField freq scale S u) x| ≤ rho/2) →
      tsupport (manufacturedWellField freq scale S u) ⊆ slabDomain H S →
      ∀ (G : Position → ℝ → Position),
      IsUnitTimeFlow (moserVelocity rho (manufacturedWellField freq scale S u)) G →
      Function.Bijective (fun x => G x 1) →
      ContDiff ℝ 4 (fun x => G x 1) →
      (∀ x, x ∉ tsupport (manufacturedWellField freq scale S u) → G x 1 = x) →
      ∀ (D : ℝ), 0 ≤ D →
      (∀ x, ∀ k : ℕ, 1 ≤ k → k ≤ 4 → ‖iteratedFDeriv ℝ k (fun x => G x 1) x‖ ≤ D^k) →
      ∀ {ι : Type} [Fintype ι] (index : ι → Fin 3 → ℤ), Function.Injective index →
      ∀ (h : ℝ), 0 < h → h ≤ 1 →
      (⋃ i, positionCube (gaussCellCenter h (index i)) h) = slabDomain H S →
      |∫ y, (gridNuclearPotential index (fun x => G x 1) rho h y-
          (slabPotential rho H S y+manufacturedWellField freq scale S u y))*
          compactOrbitalDensity freq R v w y| ≤
        rho*(24*((2*Real.pi+1)*(64*B*R^3))*D^4*(216*m*S+13824*R^3)+
          2048*Real.pi*C*(64*B*R^3))*h^4 := by
  obtain ⟨B,C,hB,hC,hq⟩ := manufactured_compact_orbital_quadrature hfreq
  refine ⟨B,C,hB,hC,?_⟩
  intro R hR v w rho H S scale hrho hH hS m u hcharge hsupp G hflow hbij hG hfix D hD hGD
    ι _ index hindex h hh hh1 hcover
  rw [manufactured_compact_nuclear_pairing hpublished hrho hH (by linarith) hh
    (manufacturedWellField freq scale S u) ((manufacturedWellField_C7 freq scale S u).of_le (by norm_num))
    (manufacturedWellField_compact freq scale (by linarith) u) hcharge hsupp G hflow hbij hfix hG.continuous
    index hindex hcover (compactOrbitalDensity_C4 freq R v w)
    (compactOrbitalDensity_hasCompactSupport freq (by linarith) v w)
    (compactOrbitalDensity_nonnegative hfreq R v w)]
  rw [abs_mul,abs_neg,abs_of_pos hrho]
  exact (mul_le_mul_of_nonneg_left
    (hq R hR v w scale S hS m u (fun x => G x 1) hG hfix D hD hGD index hindex h hh hh1)
    hrho.le).trans_eq (by ring)

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

/-- This moment absorbs the polynomial growth of the finite slab's global
potential bound when the horizontal radius is the fourth power of its thickness. -/
theorem localizedDensity_twentyFourth_moment_integrable {freq : ℝ} (hfreq : 0 < freq) :
    Integrable (fun x : Position => ‖x‖^24*localizedDensity freq 0 x) :=
  localizedDensity_even_moment_integrable hfreq 12

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_PlanarResolventTails
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.planarHeatResolventPrimitive_zero _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The same sharp exponential rate for compact forcing derivatives. The
heat-kernel proof is applied to the actual first/second derivative forcing,
without assuming differentiated resolvent asymptotics. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

theorem planarResolventOf_product_integrable {g : PlanarPosition → ℝ} {B : ℝ}
    (hg : Continuous g) (hB : ∀ x, ‖g x‖ ≤ B) (r : PlanarPosition) :
    Integrable (fun p : ℝ × PlanarPosition => planarResolventIntegrand p * g (r - p.2))
      ((volume.restrict (Set.Ioi (0 : ℝ))).prod (volume : Measure PlanarPosition)) := by
  apply planarResolventIntegrand_integrable.mul_bdd (c := B)
    ((hg.comp (continuous_const.sub continuous_snd)).aestronglyMeasurable)
  exact Filter.Eventually.of_forall (fun p => hB (r - p.2))

theorem planarResolventOf_bounded_heat_representation {g : PlanarPosition → ℝ} {B : ℝ}
    (hg : Continuous g) (hB : ∀ x, ‖g x‖ ≤ B) (r : PlanarPosition) :
    planarResolventOf g r = ∫ t in Set.Ioi (0 : ℝ), Real.exp (-t) *
      (∫ b, planarHeatKernel t b * g (r - b)) := by
  unfold planarResolventOf planarResolventKernel
  simp_rw [← integral_mul_const]
  rw [← integral_integral_swap (planarResolventOf_product_integrable hg hB r)]
  simp_rw [planarResolventIntegrand, mul_assoc, integral_const_mul]

theorem planar_supported_exponential_bound {g : PlanarPosition → ℝ} {B : ℝ}
    (hs : tsupport g ⊆ Metric.closedBall 0 1) (hB : ∀ x, ‖g x‖ ≤ B)
    (e s : PlanarPosition) : ‖g s‖ ≤ B * Real.exp (‖e‖ - inner ℝ e s) := by
  have hB₀ : 0 ≤ B := (norm_nonneg (g 0)).trans (hB 0)
  by_cases hg : g s = 0
  · rw [hg, norm_zero]
    exact mul_nonneg hB₀ (Real.exp_pos _).le
  have hsn : ‖s‖ ≤ 1 := by
    have h := hs (subset_tsupport g hg)
    simpa only [Metric.mem_closedBall, dist_zero_right] using h
  have hi : inner ℝ e s ≤ ‖e‖ := (real_inner_le_norm e s).trans
    (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hsn (norm_nonneg e))
  exact (hB s).trans (le_mul_of_one_le_right hB₀ (Real.one_le_exp (by linarith)))

theorem planarHeatOf_tilt_bound {g : PlanarPosition → ℝ} {B t : ℝ}
    (hs : tsupport g ⊆ Metric.closedBall 0 1) (hB : ∀ x, ‖g x‖ ≤ B)
    (ht : 0 < t) (e r : PlanarPosition) :
    ‖∫ b, planarHeatKernel t b * g (r - b)‖ ≤
      (B * Real.exp (‖e‖ - inner ℝ e r)) * Real.exp (t * ‖e‖ ^ 2) := by
  have hpt (b : PlanarPosition) : ‖planarHeatKernel t b * g (r - b)‖ ≤
      ((B * Real.exp (‖e‖ - inner ℝ e r)) * Real.exp (t * ‖e‖ ^ 2)) *
        planarHeatKernel t (b - (2 * t) • e) := by
    rw [norm_mul, Real.norm_of_nonneg (planarHeatKernel_positive ht b).le]
    calc
      _ ≤ planarHeatKernel t b * (B * Real.exp (‖e‖ - inner ℝ e (r - b))) :=
        mul_le_mul_of_nonneg_left (planar_supported_exponential_bound hs hB e (r - b))
          (planarHeatKernel_positive ht b).le
      _ = (B * Real.exp (‖e‖ - inner ℝ e r)) *
          (planarHeatKernel t b * Real.exp (inner ℝ e b)) := by
        rw [inner_sub_right, show ‖e‖ - (inner ℝ e r - inner ℝ e b) =
          (‖e‖ - inner ℝ e r) + inner ℝ e b by ring, Real.exp_add]
        ring
      _ = _ := by rw [planarHeatKernel_tilt ht]; ring
  have h := norm_integral_le_of_norm_le
    (((planarHeatKernel_integrable ht).comp_sub_right ((2 * t) • e)).const_mul
      ((B * Real.exp (‖e‖ - inner ℝ e r)) * Real.exp (t * ‖e‖ ^ 2)))
    (Filter.Eventually.of_forall hpt)
  simpa only [integral_const_mul, integral_sub_right_eq_self, planarHeatKernel_integral ht,
    mul_one] using h

theorem planarResolventOf_tilt_bound {g : PlanarPosition → ℝ} {B : ℝ}
    (hg : Continuous g) (hs : tsupport g ⊆ Metric.closedBall 0 1) (hB : ∀ x, ‖g x‖ ≤ B)
    (e r : PlanarPosition) (he : ‖e‖ < 1) :
    ‖planarResolventOf g r‖ ≤ B * Real.exp (‖e‖ - inner ℝ e r) / (1 - ‖e‖ ^ 2) := by
  have hc : 0 < 1 - ‖e‖ ^ 2 := by nlinarith [norm_nonneg e]
  have hi : IntegrableOn (fun t : ℝ => Real.exp (-(1 - ‖e‖ ^ 2) * t)) (Set.Ioi 0) :=
    exp_neg_integrableOn_Ioi 0 hc
  rw [planarResolventOf_bounded_heat_representation hg hB r]
  have h := norm_integral_le_of_norm_le
    (f := fun t : ℝ => Real.exp (-t) * (∫ b, planarHeatKernel t b * g (r - b)))
    (hi.const_mul (B * Real.exp (‖e‖ - inner ℝ e r))) (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      rw [norm_mul, Real.norm_of_nonneg (Real.exp_pos _).le]
      calc
        _ ≤ Real.exp (-t) * ((B * Real.exp (‖e‖ - inner ℝ e r)) * Real.exp (t * ‖e‖ ^ 2)) :=
          mul_le_mul_of_nonneg_left (planarHeatOf_tilt_bound hs hB ht e r) (Real.exp_pos _).le
        _ = (B * Real.exp (‖e‖ - inner ℝ e r)) * Real.exp (-(1 - ‖e‖ ^ 2) * t) := by
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
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_PlanarGradientMoments
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomially weighted square integrability of the actual orbital's
planar derivatives, using the published construction's compact forcing. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

private theorem planarResolventOf_half_envelope {g : PlanarPosition → ℝ} {B : ℝ}
    (hg : Continuous g) (hs : tsupport g ⊆ Metric.closedBall 0 1)
    (hB : ∀ x, ‖g x‖ ≤ B) (r : PlanarPosition) :
    ‖planarResolventOf g r‖ ≤ B*planarExponentialConstant (1/2)*Real.exp (-‖r‖/2) := by
  have hB0 : 0 ≤ B := (norm_nonneg (g 0)).trans (hB 0)
  by_cases hr : r = 0
  · subst r
    simp only [norm_zero,neg_zero,zero_div,Real.exp_zero,mul_one]
    apply (planarResolventOf_bound hB 0).trans
    apply le_mul_of_one_le_right hB0
    unfold planarExponentialConstant
    have he := Real.one_le_exp (by norm_num : (0:ℝ) ≤ 1/2)
    apply (le_div_iff₀ (by norm_num : (0:ℝ) < 1-(1/2)^2)).mpr
    nlinarith only [he]
  have hr0 : 0 < ‖r‖ := norm_pos_iff.mpr hr
  let e : PlanarPosition := ((1/2)/‖r‖) • r
  have he : ‖e‖ = 1/2 := by
    dsimp [e]
    rw [norm_smul,Real.norm_of_nonneg (by positivity)]
    field_simp
  have hi : inner ℝ e r = ‖r‖/2 := by
    dsimp [e]
    rw [real_inner_smul_left,real_inner_self_eq_norm_sq]
    field_simp
  have ht := planarResolventOf_tilt_bound hg hs hB e r (by rw [he]; norm_num)
  rw [he,hi] at ht
  convert ht using 1
  all_goals try with_reducible_and_instances rfl
  unfold planarExponentialConstant
  rw [show (1/2:ℝ)-‖r‖/2 = 1/2+(-‖r‖/2) by ring,Real.exp_add]
  ring

private theorem planarResolventOf_weighted_square_integrable {g : PlanarPosition → ℝ}
    (hg : Continuous g) (hc : HasCompactSupport g)
    (hs : tsupport g ⊆ Metric.closedBall 0 1) (k : ℕ) :
    Integrable (fun r : PlanarPosition => ‖r‖^k*planarResolventOf g r^2) := by
  obtain ⟨B,hB⟩ := hg.bounded_above_of_compact_support hc
  let C := (B*planarExponentialConstant (1/2))^2*((k.factorial:ℝ)/(1/2)^k)
  have hi := (planar_exp_norm_integrable (by norm_num : (0:ℝ)<1/2)).const_mul C
  apply hi.mono' (((continuous_norm.pow k).mul
    ((planarResolventOf_continuous hg hc).pow 2)).aestronglyMeasurable)
  filter_upwards [] with r
  change ‖‖r‖^k*planarResolventOf g r^2‖ ≤ C*Real.exp (-(1/2:ℝ)*‖r‖)
  rw [Real.norm_of_nonneg (mul_nonneg (pow_nonneg (norm_nonneg _) _) (sq_nonneg _))]
  have he := pow_le_pow_left₀ (norm_nonneg (planarResolventOf g r))
    (planarResolventOf_half_envelope hg hs hB r) 2
  rw [Real.norm_eq_abs,sq_abs] at he
  have hex : Real.exp (-‖r‖/2)^2 = Real.exp (-(1/2:ℝ)*‖r‖)*Real.exp (-(1/2:ℝ)*‖r‖) := by
    rw [pow_two]
    congr 1 <;> congr 1 <;> ring
  rw [mul_pow,hex] at he
  have hp := power_exponential_bound k (by norm_num : (0:ℝ)<1/2) (norm_nonneg r)
  have hm := mul_le_mul_of_nonneg_left he (pow_nonneg (norm_nonneg r) k)
  calc
    _ ≤ ‖r‖^k*((B*planarExponentialConstant (1/2))^2*
        (Real.exp (-(1/2:ℝ)*‖r‖)*Real.exp (-(1/2:ℝ)*‖r‖))) := hm
    _ = (B*planarExponentialConstant (1/2))^2*(‖r‖^k*Real.exp (-(1/2:ℝ)*‖r‖))*
        Real.exp (-(1/2:ℝ)*‖r‖) := by ring
    _ ≤ C*Real.exp (-(1/2:ℝ)*‖r‖) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp (sq_nonneg _)) (Real.exp_pos _).le

theorem normalizedPlanarMode_partial_moment_integrable (e : PlanarPosition) (k : ℕ) :
    Integrable (fun r => ‖r‖^k*planarPartial normalizedPlanarMode e r^2) := by
  have hi := planarResolventOf_weighted_square_integrable
    (planarPartial_continuous (planarForcing_C7.of_le (by norm_num)) e)
    (planarForcing_hasCompactSupport.fderiv_apply ℝ e)
    ((tsupport_fderiv_apply_subset ℝ e).trans planarForcing_support) k
  simp_rw [normalizedPlanarMode_partial,planarResolventMode_partial,mul_pow]
  convert hi.const_mul ((Real.sqrt (∫ s, planarResolventMode s^2))⁻¹^2) using 1
  all_goals try with_reducible_and_instances rfl
  funext r
  ring

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_LocalizedGradientMoments
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The spatial gradient of the actual localized orbital has a finite
24th moment. This supplies the Sobolev cutoff tail for nuclear replacement. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

private theorem verticalMode_deriv_moment_integrable {freq : ℝ} (hfreq : 0 < freq) (k : ℕ) :
    Integrable (fun z : ℝ => z^k*deriv (verticalMode freq) z^2) := by
  convert (verticalMode_moment_integrable hfreq (k+2)).const_mul (freq^2) using 1
  all_goals try with_reducible_and_instances rfl
  funext z
  rw [verticalMode_deriv,pow_add]
  ring

private theorem split_product_moment_integrable (k : ℕ) {f : PlanarPosition → ℝ} {g : ℝ → ℝ}
    (hf : Continuous f) (hg : Continuous g)
    (hf0 : Integrable (fun r => f r^2)) (hfk : Integrable (fun r => ‖r‖^(2*k)*f r^2))
    (hg0 : Integrable (fun z => g z^2)) (hgk : Integrable (fun z => z^(2*k)*g z^2)) :
    Integrable (fun p : SplitPosition => (‖p.1‖^2+p.2^2)^k*(f p.1*g p.2)^2) := by
  have hp := hfk.mul_prod hg0
  have hz := hf0.mul_prod hgk
  apply ((hp.add hz).const_mul ((2:ℝ)^(k-1))).mono'
    ((((continuous_fst.norm.pow 2).add (continuous_snd.pow 2)).pow k).mul
      (((hf.comp continuous_fst).mul (hg.comp continuous_snd)).pow 2)).aestronglyMeasurable
  filter_upwards [] with p
  change ‖(‖p.1‖^2+p.2^2)^k*(f p.1*g p.2)^2‖ ≤ _
  rw [Real.norm_of_nonneg (mul_nonneg (pow_nonneg (by positivity) _) (sq_nonneg _))]
  have h : (‖p.1‖^2+p.2^2)^k ≤ (2:ℝ)^(k-1)*(‖p.1‖^(2*k)+p.2^(2*k)) := by
    simpa only [← pow_mul] using add_pow_le (sq_nonneg ‖p.1‖) (sq_nonneg p.2) k
  convert mul_le_mul_of_nonneg_right h (sq_nonneg (f p.1*g p.2)) using 1
  all_goals try with_reducible_and_instances rfl
  simp only [mul_pow,Pi.add_apply]
  ring

theorem continuumLocalizedMode_deriv_even_moment_integrable {freq : ℝ} (hfreq : 0 < freq)
    (k : ℕ) (e : Position) :
    Integrable (fun x : Position => ‖x‖^(2*k)*(fderiv ℝ (continuumLocalizedMode freq 0) x e)^2) := by
  let v := positionSplitCoordinates e
  have hp := split_product_moment_integrable k
    (planarPartial_continuous (normalizedPlanarMode_C7.of_le (by norm_num)) v.1)
    (verticalMode_smooth freq).continuous
    (normalizedPlanarMode_partial_square_integrable v.1)
    (normalizedPlanarMode_partial_moment_integrable v.1 (2*k))
    (verticalMode_square_integrable hfreq) (verticalMode_moment_integrable hfreq (2*k))
  have hz := split_product_moment_integrable k normalizedPlanarMode_C7.continuous
    (((verticalMode_smooth freq).continuous_deriv (by simp)).mul_const v.2)
    normalizedPlanarMode_square_integrable (normalizedPlanarMode_norm_moment_integrable (2*k))
    (by simpa only [mul_pow] using (verticalMode_deriv_square_integrable hfreq).mul_const (v.2^2))
    (by simpa only [mul_pow,mul_assoc] using
      (verticalMode_deriv_moment_integrable hfreq (2*k)).mul_const (v.2^2))
  have hi : Integrable (fun p : SplitPosition => (‖p.1‖^2+p.2^2)^k*
      (fderiv ℝ (localizedMode freq 0) p v)^2) := by
    apply ((hp.add hz).const_mul 2).mono' (by
      exact ((((continuous_fst.norm.pow 2).add (continuous_snd.pow 2)).pow k).mul
        ((((localizedMode_C7 freq 0).continuous_fderiv (by norm_num)).clm_apply continuous_const).pow 2)).aestronglyMeasurable)
    filter_upwards [] with p
    change ‖(‖p.1‖^2+p.2^2)^k*(fderiv ℝ (localizedMode freq 0) p v)^2‖ ≤ _
    rw [Real.norm_of_nonneg (mul_nonneg (pow_nonneg (by positivity) _) (sq_nonneg _))]
    have h := sq_nonneg (planarPartial normalizedPlanarMode v.1 p.1*verticalMode freq p.2-
      normalizedPlanarMode p.1*(deriv (verticalMode freq) p.2*v.2))
    have hh : (fderiv ℝ (localizedMode freq 0) p v)^2 ≤
        2*((planarPartial normalizedPlanarMode v.1 p.1*verticalMode freq p.2)^2+
          (normalizedPlanarMode p.1*(deriv (verticalMode freq) p.2*v.2))^2) := by
      rw [localizedMode_fderiv,sub_zero]
      nlinarith only [h]
    convert mul_le_mul_of_nonneg_left hh (show 0 ≤ (‖p.1‖^2+p.2^2)^k by positivity) using 1
    all_goals try with_reducible_and_instances rfl
    simp only [Pi.add_apply]
    ring
  have ht := positionSplitCoordinates_measurePreserving.integrable_comp_of_integrable hi
  convert ht using 1
  all_goals try with_reducible_and_instances rfl
  funext x
  simp only [Function.comp_apply,continuumLocalizedMode_fderiv]
  rw [pow_mul,positionSplitCoordinates_norm_sq]

theorem continuumLocalizedMode_deriv_twentyFourth_moment_integrable {freq : ℝ}
    (hfreq : 0 < freq) (e : Position) :
    Integrable (fun x : Position => ‖x‖^24*(fderiv ℝ (continuumLocalizedMode freq 0) x e)^2) :=
  continuumLocalizedMode_deriv_even_moment_integrable hfreq 12 e

theorem continuumLocalizedMode_deriv_translate (freq : ℝ) (u : PlanarPosition) (x e : Position) :
    fderiv ℝ (continuumLocalizedMode freq u) x e =
      fderiv ℝ (continuumLocalizedMode freq 0) (x-planarCenter u) e := by
  rw [show continuumLocalizedMode freq u =
    (fun y => continuumLocalizedMode freq 0 (y-planarCenter u)) from
      funext (continuumLocalizedMode_translate freq u)]
  rw [fderiv_comp_sub]

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_OrbitalCutoffTail
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
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

theorem orbitalCutoff_fderiv_zero {R : ℝ} (hR : 0 < R) (u : PlanarPosition)
    {x : Position} (hx : ‖x-planarCenter u‖ < R) : fderiv ℝ (orbitalCutoff R u) x = 0 := by
  have he : orbitalCutoff R u =ᶠ[𝓝 x] (fun _ => (1:ℝ)) := by
    filter_upwards [Metric.isOpen_ball.mem_nhds (show x ∈ Metric.ball (planarCenter u) R from hx)] with y hy
    exact orbitalCutoff_eq_one hR u hy.le
  rw [he.fderiv_eq]
  exact fderiv_const_apply 1

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

private theorem centered_deriv_moment {freq : ℝ} (hfreq : 0 < freq) (u : PlanarPosition) (e : Position) :
    Integrable (fun x : Position => ‖x-planarCenter u‖^24*(fderiv ℝ (continuumLocalizedMode freq u) x e)^2) := by
  have hi := (continuumLocalizedMode_deriv_twentyFourth_moment_integrable hfreq e).comp_sub_right (planarCenter u)
  simpa only [continuumLocalizedMode_deriv_translate freq u] using hi

theorem orbitalCutoff_value_tail {freq R : ℝ} (hfreq : 0 < freq) (hR : 0 < R) (u : PlanarPosition) :
    Integrable (fun x => ((1-orbitalCutoff R u x)*continuumLocalizedMode freq u x)^2) ∧
      (∫ x, ((1-orbitalCutoff R u x)*continuumLocalizedMode freq u x)^2) ≤
        (∫ x, ‖x‖^24*continuumLocalizedMode freq 0 x^2)/R^24 := by
  have h := localized_weighted_coefficient_tail (a := fun x => 1-orbitalCutoff R u x) hR (show (0:ℝ) ≤ 1 by norm_num) (planarCenter u)
    (continuous_const.sub (orbitalCutoff_smooth R u).continuous) (continuumLocalizedMode_C7 freq u).continuous
    (fun x => by rw [abs_of_nonneg (sub_nonneg.mpr (orbitalCutoff_le_one R u x))]; linarith [orbitalCutoff_nonnegative R u x])
    (fun x hx => by rw [orbitalCutoff_eq_one hR u hx.le,sub_self]) (continuumLocalizedMode_centered_twentyFourth_moment_integrable hfreq u)
  refine ⟨h.1,?_⟩
  apply h.2.trans_eq
  simp_rw [continuumLocalizedMode_translate freq u]
  rw [integral_sub_right_eq_self (μ := volume) (fun x : Position => ‖x‖^24*continuumLocalizedMode freq 0 x^2) (planarCenter u)]
  ring

theorem orbitalCutoff_deriv_tail {freq : ℝ} (hfreq : 0 < freq) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ R, 1 ≤ R → ∀ (u : PlanarPosition) (e : Position),
      Integrable (fun x => (fderiv ℝ (orbitalCutoff R u) x e*continuumLocalizedMode freq u x)^2) ∧
      (∫ x, (fderiv ℝ (orbitalCutoff R u) x e*continuumLocalizedMode freq u x)^2) ≤
        (B*‖e‖)^2/R^24*(∫ x, ‖x‖^24*continuumLocalizedMode freq 0 x^2) := by
  obtain ⟨B,hB,hb⟩ := orbitalCutoff_jets_bounded
  refine ⟨B,hB,?_⟩
  intro R hR u e
  have hR0 : 0 < R := by linarith
  have hbound (x : Position) : |fderiv ℝ (orbitalCutoff R u) x e| ≤ B*‖e‖ := by
    have hd := hb R hR u 1 (by norm_num) x
    rw [norm_iteratedFDeriv_one] at hd
    exact ((fderiv ℝ (orbitalCutoff R u) x).le_opNorm e).trans
      (mul_le_mul_of_nonneg_right hd (norm_nonneg e))
  have h := localized_weighted_coefficient_tail hR0 (show 0 ≤ B*‖e‖ by positivity) (planarCenter u)
    (((orbitalCutoff_smooth R u).continuous_fderiv (by simp)).clm_apply continuous_const)
    (continuumLocalizedMode_C7 freq u).continuous hbound
    (fun x hx => by rw [orbitalCutoff_fderiv_zero hR0 u hx]; rfl) (continuumLocalizedMode_centered_twentyFourth_moment_integrable hfreq u)
  refine ⟨h.1,?_⟩
  apply h.2.trans_eq
  simp_rw [continuumLocalizedMode_translate freq u]
  rw [integral_sub_right_eq_self (μ := volume) (fun x : Position => ‖x‖^24*continuumLocalizedMode freq 0 x^2) (planarCenter u)]

theorem orbitalCutoff_deriv_remainder_tail {freq R : ℝ} (hfreq : 0 < freq) (hR : 0 < R)
    (u : PlanarPosition) (e : Position) :
    Integrable (fun x => ((1-orbitalCutoff R u x)*fderiv ℝ (continuumLocalizedMode freq u) x e)^2) ∧
      (∫ x, ((1-orbitalCutoff R u x)*fderiv ℝ (continuumLocalizedMode freq u) x e)^2) ≤
        (∫ x, ‖x‖^24*(fderiv ℝ (continuumLocalizedMode freq 0) x e)^2)/R^24 := by
  have h := localized_weighted_coefficient_tail (a := fun x => 1-orbitalCutoff R u x) hR (show (0:ℝ) ≤ 1 by norm_num) (planarCenter u)
    (continuous_const.sub (orbitalCutoff_smooth R u).continuous)
    (((continuumLocalizedMode_C7 freq u).continuous_fderiv (by norm_num)).clm_apply continuous_const)
    (fun x => by rw [abs_of_nonneg (sub_nonneg.mpr (orbitalCutoff_le_one R u x))]; linarith [orbitalCutoff_nonnegative R u x])
    (fun x hx => by rw [orbitalCutoff_eq_one hR u hx.le,sub_self]) (centered_deriv_moment hfreq u e)
  refine ⟨h.1,?_⟩
  apply h.2.trans_eq
  simp_rw [continuumLocalizedMode_deriv_translate freq u]
  rw [integral_sub_right_eq_self (μ := volume) (fun x : Position => ‖x‖^24*(fderiv ℝ (continuumLocalizedMode freq 0) x e)^2) (planarCenter u)]
  ring

theorem orbitalRemainder_C1 (freq R : ℝ) (u : PlanarPosition) :
    ContDiff ℝ 1 (orbitalRemainder freq R u) :=
  (contDiff_const.sub ((orbitalCutoff_smooth R u).of_le (by first | simp | exact_mod_cast le_top))).mul
    ((continuumLocalizedMode_C7 freq u).of_le (by norm_num))

theorem orbitalRemainder_deriv (freq R : ℝ) (u : PlanarPosition) (x e : Position) :
    fderiv ℝ (orbitalRemainder freq R u) x e =
      -(fderiv ℝ (orbitalCutoff R u) x e*continuumLocalizedMode freq u x)+
        (1-orbitalCutoff R u x)*fderiv ℝ (continuumLocalizedMode freq u) x e := by
  have hc := ((orbitalCutoff_smooth R u).differentiable (by simp) x).hasFDerivAt
  have hu := ((continuumLocalizedMode_C7 freq u).differentiable (by norm_num) x).hasFDerivAt
  have h := congrArg (fun L : Position →L[ℝ] ℝ => L e)
    (((hasFDerivAt_const (1:ℝ) x).sub hc).mul hu).fderiv
  change fderiv ℝ (orbitalRemainder freq R u) x e = _ at h
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  simp only [add_apply,smul_apply,sub_apply,zero_apply,smul_eq_mul,Pi.sub_apply]
  ring

theorem orbitalRemainder_deriv_tail {freq : ℝ} (hfreq : 0 < freq) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ R, 1 ≤ R → ∀ (u : PlanarPosition) (e : Position),
      Integrable (fun x => (fderiv ℝ (orbitalRemainder freq R u) x e)^2) ∧
      (∫ x, (fderiv ℝ (orbitalRemainder freq R u) x e)^2) ≤
        2*((B*‖e‖)^2*(∫ x, ‖x‖^24*continuumLocalizedMode freq 0 x^2)+
          (∫ x, ‖x‖^24*(fderiv ℝ (continuumLocalizedMode freq 0) x e)^2))/R^24 := by
  obtain ⟨B,hB,hb⟩ := orbitalCutoff_deriv_tail hfreq
  refine ⟨B,hB,?_⟩
  intro R hR u e
  obtain ⟨hi1,h1⟩ := hb R hR u e
  obtain ⟨hi2,h2⟩ := orbitalCutoff_deriv_remainder_tail (R := R) hfreq (by linarith) u e
  have hpoint (x : Position) : (fderiv ℝ (orbitalRemainder freq R u) x e)^2 ≤
      2*((fderiv ℝ (orbitalCutoff R u) x e*continuumLocalizedMode freq u x)^2+
        ((1-orbitalCutoff R u x)*fderiv ℝ (continuumLocalizedMode freq u) x e)^2) := by
    rw [orbitalRemainder_deriv]
    nlinarith [sq_nonneg (fderiv ℝ (orbitalCutoff R u) x e*continuumLocalizedMode freq u x+
      (1-orbitalCutoff R u x)*fderiv ℝ (continuumLocalizedMode freq u) x e)]
  have hi : Integrable (fun x => (fderiv ℝ (orbitalRemainder freq R u) x e)^2) := by
    apply ((hi1.add hi2).const_mul 2).mono' (by
      exact (((orbitalRemainder_C1 freq R u).continuous_fderiv (by norm_num)).clm_apply continuous_const).pow 2 |>.aestronglyMeasurable)
    filter_upwards [] with x
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact hpoint x
  refine ⟨hi,?_⟩
  have h := integral_mono hi ((hi1.add hi2).const_mul 2) hpoint
  rw [integral_const_mul] at h
  simp only [Pi.add_apply] at h
  rw [integral_add hi1 hi2] at h
  calc
    _ ≤ 2*((∫ x, (fderiv ℝ (orbitalCutoff R u) x e*continuumLocalizedMode freq u x)^2)+
        (∫ x, ((1-orbitalCutoff R u x)*fderiv ℝ (continuumLocalizedMode freq u) x e)^2)) := h
    _ ≤ 2*((B*‖e‖)^2/R^24*(∫ x, ‖x‖^24*continuumLocalizedMode freq 0 x^2)+
        (∫ x, ‖x‖^24*(fderiv ℝ (continuumLocalizedMode freq 0) x e)^2)/R^24) := by linarith
    _ = _ := by ring

theorem orbitalRemainder_memLp {freq R : ℝ} (hfreq : 0 < freq) (hR : 0 < R) (u : PlanarPosition) :
    MemLp (orbitalRemainder freq R u) 2 := by
  apply (memLp_two_iff_integrable_sq (orbitalRemainder_C1 freq R u).continuous.aestronglyMeasurable).mpr
  exact (orbitalCutoff_value_tail hfreq hR u).1

theorem orbitalRemainder_deriv_memLp {freq R : ℝ} (hfreq : 0 < freq) (hR : 1 ≤ R)
    (u : PlanarPosition) (e : Position) :
    MemLp (fun x => fderiv ℝ (orbitalRemainder freq R u) x e) 2 := by
  apply (memLp_two_iff_integrable_sq
    (((orbitalRemainder_C1 freq R u).continuous_fderiv (by norm_num)).clm_apply continuous_const).aestronglyMeasurable).mpr
  obtain ⟨B,_,hb⟩ := orbitalRemainder_deriv_tail hfreq
  exact (hb R hR u e).1

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_OrbitalGraphBounds
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform H1 graph bounds for actual orbitals and their removed tails. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

theorem positionGraphSquare_nonnegative (f : Position → ℝ) : 0 ≤ positionGraphSquare f :=
  add_nonneg (integral_nonneg (fun _ => sq_nonneg _))
    (Finset.sum_nonneg (fun _ _ => integral_nonneg (fun _ => sq_nonneg _)))

theorem continuumLocalizedMode_graph_uniform (freq : ℝ) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ u, positionGraphSquare (continuumLocalizedMode freq u) ≤ B := by
  refine ⟨positionGraphSquare (continuumLocalizedMode freq 0)+1,by
    linarith [positionGraphSquare_nonnegative (continuumLocalizedMode freq 0)],?_⟩
  intro u
  have he : positionGraphSquare (continuumLocalizedMode freq u) =
      positionGraphSquare (continuumLocalizedMode freq 0) := by
    unfold positionGraphSquare
    simp_rw [continuumLocalizedMode_translate freq u,continuumLocalizedMode_deriv_translate freq u]
    rw [integral_sub_right_eq_self (μ := volume) (fun x : Position => continuumLocalizedMode freq 0 x^2) (planarCenter u)]
    congr 1
    apply Finset.sum_congr rfl
    intro k _
    rw [integral_sub_right_eq_self (μ := volume) (fun x : Position => (fderiv ℝ (continuumLocalizedMode freq 0) x (EuclideanSpace.single k 1))^2) (planarCenter u)]
  rw [he]
  linarith

theorem orbitalRemainder_graph_bound {freq : ℝ} (hfreq : 0 < freq) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ R, 1 ≤ R → ∀ u,
      positionGraphSquare (orbitalRemainder freq R u) ≤ B/R^24 := by
  obtain ⟨D,_hD,hd⟩ := orbitalRemainder_deriv_tail hfreq
  let M := ∫ x, ‖x‖^24*continuumLocalizedMode freq 0 x^2
  let A (k : Fin 3) := ∫ x, ‖x‖^24*(fderiv ℝ (continuumLocalizedMode freq 0) x
    (EuclideanSpace.single k 1))^2
  let B := 1+M+∑ k : Fin 3, 2*(D^2*M+A k)
  have hM : 0 ≤ M := integral_nonneg (fun _ => mul_nonneg (by positivity) (sq_nonneg _))
  have hA (k : Fin 3) : 0 ≤ A k := integral_nonneg (fun _ => mul_nonneg (by positivity) (sq_nonneg _))
  have hsum : 0 ≤ ∑ k : Fin 3, 2*(D^2*M+A k) := Finset.sum_nonneg (fun k _ =>
    mul_nonneg (by norm_num) (add_nonneg (mul_nonneg (sq_nonneg D) hM) (hA k)))
  refine ⟨B,by dsimp [B]; linarith,?_⟩
  intro R hR u
  have hR0 : 0 < R := by linarith
  have hm : (∫ x, orbitalRemainder freq R u x^2) ≤ M/R^24 :=
    (orbitalCutoff_value_tail hfreq hR0 u).2
  have hgrad (k : Fin 3) :
      (∫ x, (fderiv ℝ (orbitalRemainder freq R u) x (EuclideanSpace.single k 1))^2) ≤
        2*(D^2*M+A k)/R^24 := by
    simpa only [PiLp.norm_single,norm_one,mul_one,M,A] using
      (hd R hR u (EuclideanSpace.single k 1)).2
  calc
    _ ≤ M/R^24+∑ k : Fin 3, 2*(D^2*M+A k)/R^24 := add_le_add hm (Finset.sum_le_sum (fun k _ => hgrad k))
    _ = (M+∑ k : Fin 3, 2*(D^2*M+A k))/R^24 := by rw [add_div,Finset.sum_div]
    _ ≤ B/R^24 := div_le_div_of_nonneg_right (by dsimp [B]; linarith) (by positivity)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_RealOneElectronState
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Real spatial functions embedded into the full spinful one-electron
weak-H1 space. This transfers nuclear form estimates to orbital products. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

theorem realOneElectronState_value (f : Position → ℝ) (hf : ContDiff ℝ 1 f)
    (hL2 : MemLp f 2) (hd : ∀ e : Position, MemLp (fun x => fderiv ℝ f x e) 2)
    (s : SpinConfiguration 1) (x : Configuration 1) :
    (realOneElectronState f hf hL2 hd).value s x = (f (oneElectronCoordinates x) : ℂ) := rfl

theorem realOneElectronState_gradient (f : Position → ℝ) (hf : ContDiff ℝ 1 f)
    (hL2 : MemLp f 2) (hd : ∀ e : Position, MemLp (fun x => fderiv ℝ f x e) 2)
    (s : SpinConfiguration 1) (a : Fin 1 × Fin 3) (x : Configuration 1) :
    (realOneElectronState f hf hL2 hd).gradient s a x =
      (fderiv ℝ f (oneElectronCoordinates x) (EuclideanSpace.single a.2 1) : ℂ) :=
  real_one_electron_partial hf a x

theorem real_nuclear_integrable_transfer (F : Position → ℝ)
    (hI : ∀ w : Coulomb.H1Vector 1, ∀ s : SpinConfiguration 1,
      Integrable (fun x => |F (Coulomb.position x 0)| * ‖w.value s x‖^2))
    (f : Position → ℝ) (hf : ContDiff ℝ 1 f) (hL2 : MemLp f 2)
    (hd : ∀ e : Position, MemLp (fun x => fderiv ℝ f x e) 2) :
    Integrable (fun y => |F y| * f y^2) := by
  have h := hI (realOneElectronState f hf hL2 hd) (fun _ => 0)
  simp only [realOneElectronState_value,Complex.norm_real,Real.norm_eq_abs,sq_abs,
    ← oneElectronCoordinates_apply] at h
  exact (oneElectronCoordinates.measurePreserving.integrable_comp_emb
    oneElectronCoordinates.toHomeomorph.measurableEmbedding).mp h

theorem real_nuclear_form_transfer (F : Position → ℝ) (B : ℝ)
    (hbound : ∀ w : Coulomb.H1Vector 1, ∀ s : SpinConfiguration 1,
      (∫ x, |F (Coulomb.position x 0)| * ‖w.value s x‖^2) ≤
        B*((∫ x, ‖w.value s x‖^2)+∑ k : Fin 3, ∫ x, ‖w.gradient s (0,k) x‖^2))
    (f : Position → ℝ) (hf : ContDiff ℝ 1 f) (hL2 : MemLp f 2)
    (hd : ∀ e : Position, MemLp (fun x => fderiv ℝ f x e) 2) :
    (∫ y, |F y| *f y^2) ≤ B*((∫ y, f y^2)+
      ∑ k : Fin 3, ∫ y, (fderiv ℝ f y (EuclideanSpace.single k 1))^2) := by
  have h := hbound (realOneElectronState f hf hL2 hd) (fun _ => 0)
  simp only [realOneElectronState_value,realOneElectronState_gradient,Complex.norm_real,
    Real.norm_eq_abs,sq_abs] at h
  have hp (x : Configuration 1) : Coulomb.position x 0 = oneElectronCoordinates x := rfl
  simp_rw [hp] at h
  have hF : (∫ x : Configuration 1, |F (oneElectronCoordinates x)| * f (oneElectronCoordinates x)^2) =
      ∫ y, |F y| * f y^2 := oneElectronCoordinates_integral (fun y => |F y| * f y^2)
  have hM : (∫ x : Configuration 1, f (oneElectronCoordinates x)^2) = ∫ y, f y^2 :=
    oneElectronCoordinates_integral (fun y => f y^2)
  have hD (k : Fin 3) : (∫ x : Configuration 1,
      (fderiv ℝ f (oneElectronCoordinates x) (EuclideanSpace.single k 1))^2) =
      ∫ y, (fderiv ℝ f y (EuclideanSpace.single k 1))^2 :=
    oneElectronCoordinates_integral (fun y => (fderiv ℝ f y (EuclideanSpace.single k 1))^2)
  rw [hF,hM] at h
  simp_rw [hD] at h
  exact h

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_OrbitalNuclearTail
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Removal of the compact cutoff in the nuclear matrix element. The
full weak-H1 absolute form estimate controls the removed orbital tail. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

theorem orbital_nuclear_cutoff_error {freq : ℝ} (hfreq : 0 < freq) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (B R : ℝ), 0 ≤ B → 1 ≤ R →
    ∀ (F : Position → ℝ), Measurable F →
    (∀ (w : Coulomb.H1Vector 1) (s : SpinConfiguration 1),
      Integrable (fun x => |F (Coulomb.position x 0)| * ‖w.value s x‖^2)) →
    (∀ (w : Coulomb.H1Vector 1) (s : SpinConfiguration 1),
      (∫ x, |F (Coulomb.position x 0)| * ‖w.value s x‖^2) ≤
        B*((∫ x, ‖w.value s x‖^2)+∑ k : Fin 3, ∫ x, ‖w.gradient s (0,k) x‖^2)) →
    ∀ u v : PlanarPosition,
      Integrable (fun x => F x*continuumLocalizedMode freq u x*continuumLocalizedMode freq v x) ∧
      Integrable (fun x => F x*compactOrbitalDensity freq R u v x) ∧
      |(∫ x, F x*continuumLocalizedMode freq u x*continuumLocalizedMode freq v x)-
        ∫ x, F x*compactOrbitalDensity freq R u v x| ≤ C*B/R^12 := by
  obtain ⟨T,hT,ht⟩ := orbitalRemainder_graph_bound hfreq
  obtain ⟨A,hA,ha⟩ := continuumLocalizedMode_graph_uniform freq
  let C := T+A
  have hT0 : 0 ≤ T := zero_le_one.trans hT
  have hA0 : 0 ≤ A := zero_le_one.trans hA
  have hC0 : 0 ≤ C := add_nonneg hT0 hA0
  refine ⟨C,by dsimp [C]; linarith,?_⟩
  intro B R hB hR F hF hI hbound u v
  have hR0 : 0 < R := by linarith
  have hu := (continuumLocalizedMode_C7 freq u).of_le (show (1 : WithTop ℕ∞) ≤ 7 by norm_num)
  have hv := (continuumLocalizedMode_C7 freq v).of_le (show (1 : WithTop ℕ∞) ≤ 7 by norm_num)
  have hrem := orbitalRemainder_C1 freq R u
  have hIr := real_nuclear_integrable_transfer F hI _ hrem
    (orbitalRemainder_memLp hfreq hR0 u) (orbitalRemainder_deriv_memLp hfreq hR u)
  have hIu := real_nuclear_integrable_transfer F hI _ hu
    (continuumLocalizedMode_memLp hfreq u) (continuumLocalizedMode_fderiv_memLp hfreq u)
  have hIv := real_nuclear_integrable_transfer F hI _ hv
    (continuumLocalizedMode_memLp hfreq v) (continuumLocalizedMode_fderiv_memLp hfreq v)
  have hbr : (∫ x, |F x| *orbitalRemainder freq R u x^2) ≤ B*(T/R^24) := by
    exact (real_nuclear_form_transfer F B hbound _ hrem
      (orbitalRemainder_memLp hfreq hR0 u) (orbitalRemainder_deriv_memLp hfreq hR u)).trans
      (mul_le_mul_of_nonneg_left (ht R hR u) hB)
  have hbv : (∫ x, |F x| *continuumLocalizedMode freq v x^2) ≤ B*A := by
    exact (real_nuclear_form_transfer F B hbound _ hv
      (continuumLocalizedMode_memLp hfreq v) (continuumLocalizedMode_fderiv_memLp hfreq v)).trans
      (mul_le_mul_of_nonneg_left (ha v) hB)
  obtain ⟨hir,hsq⟩ := weighted_source_pairing F _ _ hF hrem.continuous.measurable hv.continuous.measurable hIr hIv
  have hiuv := (weighted_source_pairing F _ _ hF hu.continuous.measurable hv.continuous.measurable hIu hIv).1
  have he (x : Position) : F x*compactOrbitalDensity freq R u v x =
      F x*continuumLocalizedMode freq u x*continuumLocalizedMode freq v x-
      F x*orbitalRemainder freq R u x*continuumLocalizedMode freq v x := by
    dsimp [compactOrbitalDensity,orbitalRemainder]
    ring
  have hic : Integrable (fun x => F x*compactOrbitalDensity freq R u v x) := by
    simp_rw [he]
    exact hiuv.sub hir
  refine ⟨hiuv,hic,?_⟩
  have heI : (∫ x, F x*continuumLocalizedMode freq u x*continuumLocalizedMode freq v x)-
      (∫ x, F x*compactOrbitalDensity freq R u v x) =
      ∫ x, F x*orbitalRemainder freq R u x*continuumLocalizedMode freq v x := by
    simp_rw [he]
    rw [integral_sub hiuv hir]
    ring
  rw [heI]
  apply (sq_le_sq₀ (abs_nonneg _) (div_nonneg (mul_nonneg hC0 hB) (pow_nonneg hR0.le 12))).mp
  have hp := mul_le_mul hbr hbv
    (integral_nonneg (fun x => mul_nonneg (abs_nonneg (F x)) (sq_nonneg _)))
    (mul_nonneg hB (div_nonneg hT0 (pow_nonneg hR0.le 24)))
  apply hsq.trans (hp.trans ?_)
  have hTA : T*A ≤ C^2 := by dsimp [C]; nlinarith [sq_nonneg T,sq_nonneg A]
  calc
    (B*(T/R^24))*(B*A) = (T*A)*B^2/(R^12)^2 := by rw [← pow_mul]; norm_num; ring
    _ ≤ C^2*B^2/(R^12)^2 := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hTA (sq_nonneg B)) (sq_nonneg _)
    _ = (C*B/R^12)^2 := by ring

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_ManufacturedOrbitalNuclearError
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual uncut orbital matrix elements of the manufactured grid potential.
The only external analytic input is the published C4 flow theorem. -/

noncomputable section
open MeasureTheory
open scoped NNReal
namespace ContinuumCoulomb

theorem manufactured_orbital_nuclear_error (hpublished : PublishedC4FlowInput) :
    ∃ rho : ℕ, 0 < rho ∧ ∃ L K : ℝ≥0, 0 < L ∧ 0 < K ∧ ∃ D : ℝ, 1 ≤ D ∧
    ∀ freq : ℝ, 0 < freq → ∃ A B C : ℝ, 1 ≤ A ∧ 1 ≤ B ∧ 1 ≤ C ∧
    ∀ (scale S : ℝ), 0 < scale → 1 ≤ S →
    ∀ (m : ℕ) (u : Fin m → PlanarPosition),
    (∀ i j, i ≠ j → 3 ≤ ‖u i-u j‖) →
    (∀ i, localizedCounterterm freq u i ≤ scale) →
    ∃ G : Position → ℝ → Position,
      IsUnitTimeFlow (moserVelocity rho (manufacturedWellField freq scale S u)) G ∧
      Function.Bijective (fun x => G x 1) ∧
      LipschitzWith L (fun x => G x 1) ∧ AntilipschitzWith K (fun x => G x 1) ∧
      (∀ x, x ∉ tsupport (manufacturedWellField freq scale S u) → G x 1 = x) ∧
      (∀ x, |manufacturedCharge (manufacturedWellField freq scale S u) x| ≤ (rho:ℝ)/2) ∧
      ContDiff ℝ 4 (fun x => G x 1) ∧
      (∀ k : ℕ, 1 ≤ k → k ≤ 4 → ∀ x, ‖iteratedFDeriv ℝ k (fun y => G y 1) x‖ ≤ L) ∧
    ∀ H : ℝ, 0 ≤ H → tsupport (manufacturedWellField freq scale S u) ⊆ slabDomain H S →
    ∀ {ι : Type} [Fintype ι] (index : ι → Fin 3 → ℤ), Function.Injective index →
    ∀ h : ℝ, 0 < h → h ≤ 1 → (m:ℝ)*S*h^2 ≤ 1 →
    (⋃ i, positionCube (gaussCellCenter h (index i)) h) = slabDomain H S →
      (∀ (n : ℕ) (w : Coulomb.H1Vector n) (s : SpinConfiguration n) (i : Fin n),
        Integrable (fun x => |gridNuclearPotential index (fun x => G x 1) rho h (Coulomb.position x i)-
          (slabPotential rho H S (Coulomb.position x i)+
            manufacturedWellField freq scale S u (Coulomb.position x i))| * ‖w.value s x‖^2) ∧
        (∫ x, |gridNuclearPotential index (fun x => G x 1) rho h (Coulomb.position x i)-
          (slabPotential rho H S (Coulomb.position x i)+
            manufacturedWellField freq scale S u (Coulomb.position x i))| * ‖w.value s x‖^2) ≤
        D*h^2*((∫ x, ‖w.value s x‖^2)+∑ k : Fin 3, ∫ x, ‖w.gradient s (i,k) x‖^2)) ∧
    ∀ R : ℝ, 1 ≤ R → ∀ v w : PlanarPosition,
      Integrable (fun y => (gridNuclearPotential index (fun x => G x 1) rho h y-
        (slabPotential rho H S y+manufacturedWellField freq scale S u y))*
        continuumLocalizedMode freq v y*continuumLocalizedMode freq w y) ∧
      |∫ y, (gridNuclearPotential index (fun x => G x 1) rho h y-
        (slabPotential rho H S y+manufacturedWellField freq scale S u y))*
        continuumLocalizedMode freq v y*continuumLocalizedMode freq w y| ≤
      rho*(24*((2*Real.pi+1)*(64*A*R^3))*(max 1 (L:ℝ))^4*(216*m*S+13824*R^3)+
        2048*Real.pi*B*(64*A*R^3))*h^4+C*h^2/R^12 := by
  obtain ⟨rho,hrho,L,K,hL,hK,D,hD,hfamily⟩ := manufactured_uniform_nuclear_absolute_form hpublished
  refine ⟨rho,hrho,L,K,hL,hK,D,hD,?_⟩
  intro freq hfreq
  obtain ⟨A,B,hA,hB,hcompact⟩ := manufactured_compact_orbital_nuclear_error hpublished hfreq
  obtain ⟨T,hT,htail⟩ := orbital_nuclear_cutoff_error hfreq
  let C := max 1 (T*D)
  have hC : 1 ≤ C := le_max_left _ _
  have hD0 : 0 ≤ D := zero_le_one.trans hD
  have hrhoR : (0:ℝ) < rho := by exact_mod_cast hrho
  refine ⟨A,B,C,hA,hB,hC,?_⟩
  intro scale S hscale hS m u hsep hcounter
  obtain ⟨G,hflow,hbij,hLip,hAnti,hfix,hcharge,hreg,hjets,hform⟩ :=
    hfamily freq scale S hscale hS m u hsep hcounter
  refine ⟨G,hflow,hbij,hLip,hAnti,hfix,hcharge,hreg,hjets,?_⟩
  intro H hH hsupp ι _ index hindex h hh hh1 hmesh hcover
  have hfull := hform H hH hsupp index hindex h hh hh1 hmesh hcover
  refine ⟨hfull,?_⟩
  intro R hR v w
  let F : Position → ℝ := fun y => gridNuclearPotential index (fun x => G x 1) rho h y-
    (slabPotential rho H S y+manufacturedWellField freq scale S u y)
  have hF : Measurable F := (gridNuclearPotential_measurable index (fun x => G x 1) rho h).sub
    (((slabPotential_continuous hrhoR.le hH (zero_le_one.trans hS)).add
      (manufacturedWellField_C7 freq scale S u).continuous).measurable)
  obtain ⟨hi,hic,he⟩ := htail (D*h^2) R (mul_nonneg hD0 (sq_nonneg h)) hR F hF
    (fun w s => (hfull 1 w s 0).1) (fun w s => (hfull 1 w s 0).2) v w
  refine ⟨hi,?_⟩
  have hmax : 1 ≤ max 1 (L:ℝ) := le_max_left _ _
  have hjet (x : Position) (k : ℕ) (hk : 1 ≤ k) (hk4 : k ≤ 4) :
      ‖iteratedFDeriv ℝ k (fun x => G x 1) x‖ ≤ (max 1 (L:ℝ))^k :=
    (hjets k hk hk4 x).trans ((le_max_right 1 (L:ℝ)).trans
      (by simpa only [pow_one] using pow_le_pow_right₀ hmax hk))
  have hc := hcompact R hR v w rho H S scale hrhoR hH hS m u hcharge hsupp
    G hflow hbij hreg hfix (max 1 (L:ℝ)) (zero_le_one.trans hmax) hjet
    index hindex h hh hh1 hcover
  have htriangle := abs_add_le
    ((∫ y, F y*continuumLocalizedMode freq v y*continuumLocalizedMode freq w y)-
      ∫ y, F y*compactOrbitalDensity freq R v w y)
    (∫ y, F y*compactOrbitalDensity freq R v w y)
  rw [sub_add_cancel] at htriangle
  have htailC : T*(D*h^2)/R^12 ≤ C*h^2/R^12 := by
    apply div_le_div_of_nonneg_right _ (by positivity)
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_right (le_max_right 1 (T*D)) (sq_nonneg h)
  exact htriangle.trans ((add_le_add (he.trans htailC) hc).trans_eq (add_comm _ _))

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Nuclei_NuclearQuadratureScale
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fourth-order cubature and the uncut orbital tail at the physical mesh
R^-10. Constants are independent of the slab width and the site positions. -/

noncomputable section
namespace ContinuumCoulomb

theorem nuclear_quadrature_physical_scale {R S a b c q m : ℝ}
    (hR : 1 ≤ R) (hS : S ≤ 2*R^5) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hc : 0 ≤ c) (_hq : 0 ≤ q) (hm : 0 ≤ m) :
    (a*m*S*R^3+b*R^6+c*R^3)*(1/R^10)^4+q*(1/R^10)^2/R^12 ≤
      (2*a*m+b+c+q)/R^32 := by
  have hR0 : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have hs : a*m*S*R^3 ≤ 2*a*m*R^8 := by
    calc
      _ ≤ a*m*(2*R^5)*R^3 := by gcongr
      _ = _ := by ring
  have he : (a*m*S*R^3+b*R^6+c*R^3)*(1/R^10)^4+q*(1/R^10)^2/R^12 =
      (a*m*S*R^3+b*R^6+c*R^3)/R^40+q/R^32 := by
    field_simp [ne_of_gt hR0]
  rw [he]
  calc
    _ ≤ (2*a*m*R^8+b*R^6+c*R^3)/R^40+q/R^32 := by gcongr
    _ = 2*a*m/R^32+b/R^34+c/R^37+q/R^32 := by
      field_simp [ne_of_gt hR0]
    _ ≤ 2*a*m/R^32+b/R^32+c/R^32+q/R^32 := by
      gcongr <;> norm_num
    _ = _ := by ring

theorem manufactured_orbital_quadrature_physical_scale
    {rho A B C L R S : ℝ} (hrho : 0 ≤ rho) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hC : 0 ≤ C) (hR : 1 ≤ R) (hS : S ≤ 2*R^5) (m : ℕ) :
    rho*(24*((2*Real.pi+1)*(64*A*R^3))*(max 1 L)^4*(216*m*S+13824*R^3)+
        2048*Real.pi*B*(64*A*R^3))*(1/R^10)^4+C*(1/R^10)^2/R^12 ≤
    (2*(rho*24*(2*Real.pi+1)*64*A*(max 1 L)^4*216)+
       rho*24*(2*Real.pi+1)*64*A*(max 1 L)^4*13824+
       rho*2048*Real.pi*B*64*A+C)*((m:ℝ)+1)/R^32 := by
  let a := rho*24*(2*Real.pi+1)*64*A*(max 1 L)^4*216
  let b := rho*24*(2*Real.pi+1)*64*A*(max 1 L)^4*13824
  let c := rho*2048*Real.pi*B*64*A
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have he := nuclear_quadrature_physical_scale hR hS ha hb hc hC (Nat.cast_nonneg m)
  have hnum : 2*a*(m:ℝ)+b+c+C ≤ (2*a+b+c+C)*((m:ℝ)+1) := by
    nlinarith [mul_nonneg hb (Nat.cast_nonneg m),mul_nonneg hc (Nat.cast_nonneg m),
      mul_nonneg hC (Nat.cast_nonneg m)]
  apply le_trans _ (div_le_div_of_nonneg_right hnum (by positivity))
  convert he using 1
  all_goals try with_reducible_and_instances rfl
  dsimp [a,b,c]
  ring

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_ManufacturedGridWitness
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! One actual transport supplies both the full weak-H1 error and the
uncut orbital entries, with uniform constants at the physical mesh. -/

noncomputable section
open MeasureTheory
open scoped NNReal
namespace ContinuumCoulomb

theorem manufactured_grid_witness_oai (hp : PublishedC4FlowInput) :
    ∃ rho : ℕ, 0 < rho ∧ ∃ L K : ℝ≥0, 0 < L ∧ 0 < K ∧ ∃ D : ℝ, 1 ≤ D ∧
    ∀ freq : ℝ, 0 < freq → ∃ E : ℝ, 1 ≤ E ∧
    ∀ R scale S H : ℝ, 2 ≤ R → 0 < scale → R^5 ≤ S → S ≤ 2*R^5 → 0 ≤ H →
    ∀ (m : ℕ) (u : Fin m → PlanarPosition), (m:ℝ) ≤ R^14 →
    (∀ i j, i ≠ j → 3 ≤ ‖u i-u j‖) →
    (∀ i, localizedCounterterm freq u i ≤ scale) →
    tsupport (manufacturedWellField freq scale S u) ⊆ slabDomain H S →
    ∀ {ι : Type} [Fintype ι] (index : ι → Fin 3 → ℤ), Function.Injective index →
    (⋃ i, positionCube (gaussCellCenter (1/R^10) (index i)) (1/R^10)) = slabDomain H S →
    ∃ G : Position → ℝ → Position,
      IsUnitTimeFlow (moserVelocity rho (manufacturedWellField freq scale S u)) G ∧
      Function.Bijective (fun x => G x 1) ∧
      LipschitzWith L (fun x => G x 1) ∧ AntilipschitzWith K (fun x => G x 1) ∧
      (∀ x, x ∉ tsupport (manufacturedWellField freq scale S u) → G x 1 = x) ∧
      (∀ x, |manufacturedCharge (manufacturedWellField freq scale S u) x| ≤ (rho:ℝ)/2) ∧
      ContDiff ℝ 4 (fun x => G x 1) ∧
      (∀ k : ℕ, 1 ≤ k → k ≤ 4 → ∀ x, ‖iteratedFDeriv ℝ k (fun y => G y 1) x‖ ≤ L) ∧
      let F : Position → ℝ := fun y => gridNuclearPotential index (fun x => G x 1) rho (1/R^10) y-
        (slabPotential rho H S y+manufacturedWellField freq scale S u y)
      (∀ (n : ℕ) (w : Coulomb.H1Vector n) (s : SpinConfiguration n) (i : Fin n),
        Integrable (fun x => |F (Coulomb.position x i)| *‖w.value s x‖^2) ∧
        (∫ x, |F (Coulomb.position x i)| *‖w.value s x‖^2) ≤
          (D/R^20)*((∫ x, ‖w.value s x‖^2)+∑ k : Fin 3, ∫ x, ‖w.gradient s (i,k) x‖^2)) ∧
      (∀ v w : PlanarPosition,
        Integrable (fun y => F y*continuumLocalizedMode freq v y*continuumLocalizedMode freq w y) ∧
        |∫ y, F y*continuumLocalizedMode freq v y*continuumLocalizedMode freq w y| ≤
          E*((m:ℝ)+1)/R^32) := by
  obtain ⟨rho,hrho,L,K,hL,hK,D,hD,hfamily⟩ := manufactured_orbital_nuclear_error hp
  refine ⟨rho,hrho,L,K,hL,hK,D,hD,?_⟩
  intro freq hf
  obtain ⟨A,B,C,hA,hB,hC,hgrid⟩ := hfamily freq hf
  let e := 2*((rho:ℝ)*24*(2*Real.pi+1)*64*A*(max 1 (L:ℝ))^4*216)+
    (rho:ℝ)*24*(2*Real.pi+1)*64*A*(max 1 (L:ℝ))^4*13824+
    (rho:ℝ)*2048*Real.pi*B*64*A+C
  refine ⟨max 1 e,le_max_left _ _,?_⟩
  intro R scale S H hR hscale hSlo hShi hH m u hm hsep hcounter hsupp ι _ index hi hcover
  have hR0 : 0 < R := by linarith
  have hR1 : 1 ≤ R := by linarith
  have hS : 1 ≤ S := (one_le_pow₀ hR1).trans hSlo
  obtain ⟨G,hflow,hbij,hLip,hAnti,hfix,hcharge,hreg,hjets,hform⟩ :=
    hgrid scale S hscale hS m u hsep hcounter
  refine ⟨G,hflow,hbij,hLip,hAnti,hfix,hcharge,hreg,hjets,?_⟩
  have hh : 0 < 1/R^10 := by positivity
  have hh1 : 1/R^10 ≤ 1 := (div_le_one (pow_pos hR0 _)).mpr (one_le_pow₀ hR1)
  have hmesh : (m:ℝ)*S*(1/R^10)^2 ≤ 1 := by
    calc
      _ ≤ R^14*(2*R^5)*(1/R^10)^2 := by gcongr
      _ = 2/R := by field_simp [ne_of_gt hR0]
      _ ≤ 1 := (div_le_one hR0).mpr hR
  obtain ⟨hfull,hentries⟩ := hform H hH hsupp index hi (1/R^10) hh hh1 hmesh hcover
  constructor
  · intro n w s i
    have h := hfull n w s i
    have he : D*(1/R^10)^2 = D/R^20 := by field_simp [ne_of_gt hR0]
    rw [he] at h
    exact h
  · intro v w
    obtain ⟨hi,he⟩ := hentries R hR1 v w
    refine ⟨hi,he.trans ?_⟩
    apply (manufactured_orbital_quadrature_physical_scale (Nat.cast_nonneg rho)
      (zero_le_one.trans hA) (zero_le_one.trans hB) (zero_le_one.trans hC) hR1 hShi m).trans
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_right 1 e) (by positivity)) (by positivity)

end ContinuumCoulomb

end

end OAI
end

theorem solution : type_of% @OAI.ContinuumCoulomb.manufactured_grid_witness_oai := @OAI.ContinuumCoulomb.manufactured_grid_witness_oai
