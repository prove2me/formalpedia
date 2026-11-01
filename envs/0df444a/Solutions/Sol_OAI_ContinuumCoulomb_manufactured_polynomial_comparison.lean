-- Prove2me | solution 1 for OAI.ContinuumCoulomb.manufactured_polynomial_comparison
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T22:01:04.341199+00:00
-- url     : https://prove2.me/submissions/697d0470-864e-4c4e-9f9b-81cb767544ac

import Mathlib
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Round
import Mathlib.Algebra.Ring.Int.Units
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
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.Convolution
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Operator.Compact
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.RCLike.Lemmas
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
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.VonNeumannAlgebra.Basic
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Combinatorics.Young.YoungDiagram
import Mathlib.Computability.TuringMachine.Computable
import Mathlib.Data.EReal.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Nodup
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Data.Nat.Size
import Mathlib.Data.Rat.Floor
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basis
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Logic.Equiv.Prod
import Mathlib.Logic.Equiv.Set
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.ExpDecay
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.MeasurableSpace.Embedding
import Mathlib.MeasureTheory.Measure.FiniteMeasure
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Order.Fin.Basic
import Mathlib.Order.Hom.PowersetCard
import Mathlib.Probability.Kernel.CondDistrib
import Mathlib.Probability.Kernel.Defs
import Mathlib.Probability.Moments.Variance
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Tactic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Algebra.LinearMapCompletion
import Mathlib.Topology.Algebra.Module.Determinant
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.Algebra.Star.Unitary
import Mathlib.Topology.Algebra.Support
import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.MetricSpace.Antilipschitz
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.UniformSpace.Cauchy
import Mathlib.Topology.UniformSpace.HeineCantor
import Definitions.Def_ContinuumCoulombHardness
import Definitions.Def_OAIQ092A010
import Theorems.Thm_OAI_ContinuumCoulomb_exists_actual_oneBody_parameters
import Theorems.Thm_OAI_ContinuumCoulomb_manufactured_grid_ground_bounds
import Theorems.Thm_OAI_ContinuumCoulomb_manufactured_grid_witness

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

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_LocalizedModes
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

theorem planarCenter_sub (u v : PlanarPosition) : planarCenter (u - v) = planarCenter u - planarCenter v := by
  change positionSplitCoordinates.symm (u - v, 0) =
    positionSplitCoordinates.symm (u, 0) - positionSplitCoordinates.symm (v, 0)
  rw [← map_sub]
  simp only [Prod.mk_sub_mk, sub_self]

theorem continuumLocalizedMode_translate (freq : ℝ) (u : PlanarPosition) (x : Position) :
    continuumLocalizedMode freq u x = continuumLocalizedMode freq 0 (x - planarCenter u) := by
  simp only [continuumLocalizedMode, localizedMode, map_sub, planarCenter,
    ContinuousLinearEquiv.apply_symm_apply, Prod.fst_sub, Prod.snd_sub, sub_zero]

theorem localizedDensity_translate (freq : ℝ) (u : PlanarPosition) (x : Position) :
    localizedDensity freq u x = localizedDensity freq 0 (x - planarCenter u) := by
  simp only [localizedDensity, continuumLocalizedMode_translate freq u]

theorem localizedDensity_potential_translate (freq : ℝ) (u : PlanarPosition) (x : Position) :
    NeutralAtom.potentialOf (localizedDensity freq u) x =
      NeutralAtom.potentialOf (localizedDensity freq 0) (x - planarCenter u) := by
  unfold NeutralAtom.potentialOf
  rw [← integral_add_right_eq_self
    (fun y => NeutralAtom.coulombKernel (x - y) * localizedDensity freq u y) (planarCenter u)]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun y => by
    dsimp only
    rw [localizedDensity_translate freq u, add_sub_cancel_right]
    congr 2
    abel)

theorem localizedCoulombProfileAt_eq (freq : ℝ) (u : PlanarPosition) :
    localizedCoulombProfileAt freq u = localizedCoulombCoeff freq 0 u := by
  unfold localizedCoulombProfileAt localizedCoulombCoeff
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun x =>
    congrArg (fun z => localizedDensity freq 0 x * z)
      (localizedDensity_potential_translate freq u x).symm)

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

theorem normalizedPlanarMode_isometry (L : PlanarPosition ≃ₗᵢ[ℝ] PlanarPosition)
    (r : PlanarPosition) : normalizedPlanarMode (L r) = normalizedPlanarMode r := by
  simp only [normalizedPlanarMode, planarResolventMode_isometry]

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_LocalizedCoulombRadial
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual direct Coulomb interaction depends only on planar separation. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

theorem liftPlanarIsometry_coordinates (L : PlanarPosition ≃ₗᵢ[ℝ] PlanarPosition) (x : Position) :
    positionSplitCoordinates (liftPlanarIsometry L x) =
      (L (positionSplitCoordinates x).1, (positionSplitCoordinates x).2) := by
  change WithLp.ofLp (positionSplitIsometry (positionSplitIsometry.symm
    ((LinearIsometryEquiv.withLpProdCongr 2 L (LinearIsometryEquiv.refl ℝ ℝ))
      (positionSplitIsometry x)))) = _
  rw [positionSplitIsometry.apply_symm_apply]
  rfl

theorem localizedDensity_liftPlanarIsometry (freq : ℝ)
    (L : PlanarPosition ≃ₗᵢ[ℝ] PlanarPosition) (u : PlanarPosition) (x : Position) :
    localizedDensity freq (L u) (liftPlanarIsometry L x) = localizedDensity freq u x := by
  simp only [localizedDensity, continuumLocalizedMode, localizedMode,
    liftPlanarIsometry_coordinates, ← L.map_sub, normalizedPlanarMode_isometry]

theorem localizedDensity_potential_liftPlanarIsometry (freq : ℝ)
    (L : PlanarPosition ≃ₗᵢ[ℝ] PlanarPosition) (u : PlanarPosition) (x : Position) :
    NeutralAtom.potentialOf (localizedDensity freq (L u)) (liftPlanarIsometry L x) =
      NeutralAtom.potentialOf (localizedDensity freq u) x := by
  unfold NeutralAtom.potentialOf
  rw [← MeasureTheory.integral_comp (liftPlanarIsometry L)
    (fun y => NeutralAtom.coulombKernel (liftPlanarIsometry L x - y) * localizedDensity freq (L u) y)]
  apply integral_congr_ae
  filter_upwards [] with y
  rw [localizedDensity_liftPlanarIsometry, ← (liftPlanarIsometry L).map_sub]
  simp only [NeutralAtom.coulombKernel, LinearIsometryEquiv.norm_map]

theorem localizedCoulombCoeff_isometry (freq : ℝ)
    (L : PlanarPosition ≃ₗᵢ[ℝ] PlanarPosition) (u v : PlanarPosition) :
    localizedCoulombCoeff freq (L u) (L v) = localizedCoulombCoeff freq u v := by
  unfold localizedCoulombCoeff
  rw [← MeasureTheory.integral_comp (liftPlanarIsometry L)
    (fun x => localizedDensity freq (L u) x * NeutralAtom.potentialOf (localizedDensity freq (L v)) x)]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [localizedDensity_liftPlanarIsometry, localizedDensity_potential_liftPlanarIsometry]

theorem localizedCoulombProfileAt_isometry (freq : ℝ)
    (L : PlanarPosition ≃ₗᵢ[ℝ] PlanarPosition) (u : PlanarPosition) :
    localizedCoulombProfileAt freq (L u) = localizedCoulombProfileAt freq u := by
  rw [localizedCoulombProfileAt_eq, localizedCoulombProfileAt_eq]
  simpa only [map_zero] using localizedCoulombCoeff_isometry freq L 0 u

theorem localizedCoulombProfileAt_norm (freq : ℝ) (u : PlanarPosition) :
    localizedCoulombProfileAt freq u = localizedCoulombProfile freq ‖u‖ := by
  have hn : ‖‖u‖ • planarAxis 0‖ = ‖u‖ := by
    rw [norm_smul, planarAxis_zero_norm, mul_one, Real.norm_of_nonneg (norm_nonneg u)]
  have h := localizedCoulombProfileAt_isometry freq
    ((ℝ ∙ (‖u‖ • planarAxis 0 - u))ᗮ.reflection) (‖u‖ • planarAxis 0)
  rw [Submodule.reflection_sub hn] at h
  exact h

theorem localizedCoulombCoeff_displacement (freq : ℝ) (u v : PlanarPosition) :
    localizedCoulombCoeff freq u v = localizedCoulombProfileAt freq (v - u) := by
  unfold localizedCoulombCoeff localizedCoulombProfileAt
  rw [← integral_add_right_eq_self
    (fun x => localizedDensity freq u x * NeutralAtom.potentialOf (localizedDensity freq v) x)
    (planarCenter u)]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [localizedDensity_translate freq u, add_sub_cancel_right, localizedDensity_potential_translate freq v]
  congr 2
  rw [planarCenter_sub]
  abel

theorem localizedCoulombCoeff_distance (freq : ℝ) (u v : PlanarPosition) :
    localizedCoulombCoeff freq u v = localizedCoulombProfile freq ‖u - v‖ := by
  rw [localizedCoulombCoeff_displacement, localizedCoulombProfileAt_norm, norm_sub_rev]

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_CoulombCalibration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform contact calibration for the actual Coulomb profile, with a
single polynomial scale also enforcing the many-site Gram bound. -/

noncomputable section
open scoped BigOperators
namespace ContinuumCoulomb

theorem localizedCoulombProfile_nonnegative (freq d : ℝ) : 0 ≤ localizedCoulombProfile freq d := by
  unfold localizedCoulombProfile
  rw [localizedCoulombProfileAt_eq]
  exact localizedCoulombCoeff_nonnegative freq _ _

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

theorem exists_logarithmic_scale_threshold (D : ℝ) :
    ∃ k₀ : ℕ, 1 ≤ k₀ ∧ ∀ k : ℕ, k₀ ≤ k → ∀ N : ℝ, 2 ≤ N →
      D ≤ 25*(k:ℝ)*Real.log N := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  obtain ⟨k₀,hk₀⟩ := exists_nat_ge (max 1 (D/(25*Real.log 2)))
  refine ⟨k₀,by exact_mod_cast (le_max_left _ _).trans hk₀,fun k hk N hN => ?_⟩
  have hquot : D/(25*Real.log 2) ≤ (k:ℝ) :=
    ((le_max_right _ _).trans hk₀).trans (by exact_mod_cast hk)
  have hD := (div_le_iff₀ (by positivity : 0 < 25*Real.log 2)).mp hquot
  have hlogs : Real.log 2 ≤ Real.log N := Real.log_le_log (by norm_num) hN
  calc
    D ≤ 25*(k:ℝ)*Real.log 2 := by nlinarith only [hD]
    _ ≤ _ := mul_le_mul_of_nonneg_left hlogs (by positivity)

theorem exists_centered_slab_threshold (C S₀ : ℝ) :
    ∃ k₀ : ℕ, 1 ≤ k₀ ∧ ∀ k : ℕ, k₀ ≤ k → ∀ N : ℝ, 2 ≤ N →
      ∀ H S : ℝ, (N^k)^50 ≤ H → (N^k)^5 ≤ S → S ≤ 2*(N^k)^5 →
        S₀ ≤ S ∧ 1 ≤ H ∧ C*S^3 ≤ H ∧ (N^k)^5 ≤ H/2 := by
  obtain ⟨q,hq,hbound⟩ := exists_polynomial_constant_bounds
    (show (0:ℝ)<1 by norm_num) (max S₀ (8*max C 0))
  refine ⟨q,by omega,fun k hk N hN H S hH hS hShi => ?_⟩
  have hN1 : 1 ≤ N := by linarith
  have hR1 : 1 ≤ N^k := one_le_pow₀ hN1
  have hS0 : 0 ≤ S := (pow_nonneg (by positivity : 0 ≤ N^k) 5).trans hS
  have hR2 : 2 ≤ N^k := hN.trans (le_self_pow₀ hN1 (by omega))
  have hmax : max S₀ (8*max C 0) ≤ N^k :=
    (hbound N hN).2.trans (pow_le_pow_right₀ hN1 hk)
  have hC : 8*max C 0 ≤ (N^k)^35 :=
    ((le_max_right _ _).trans hmax).trans (le_self_pow₀ hR1 (by decide))
  have hCH : C*S^3 ≤ (N^k)^50 := by
    calc
      _ ≤ max C 0*(2*(N^k)^5)^3 :=
        mul_le_mul (le_max_left _ _) (pow_le_pow_left₀ hS0 hShi 3)
          (pow_nonneg hS0 3) (le_max_right _ _)
      _ = (8*max C 0)*(N^k)^15 := by ring
      _ ≤ (N^k)^35*(N^k)^15 := mul_le_mul_of_nonneg_right hC (by positivity)
      _ = _ := by ring
  have htwo : 2*(N^k)^5 ≤ (N^k)^50 := by
    calc
      _ ≤ (N^k)*(N^k)^5 := mul_le_mul_of_nonneg_right hR2 (by positivity)
      _ = (N^k)^6 := by ring
      _ ≤ _ := pow_le_pow_right₀ hR1 (by decide)
  exact ⟨(le_max_left _ _).trans (hmax.trans ((le_self_pow₀ hR1 (by decide)).trans hS)),
    (one_le_pow₀ hR1).trans hH,hCH.trans hH,by linarith [htwo.trans hH]⟩

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_ManyBody_ComplementScaleBudget
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Physical amplification of the full complement error. The singular
nuclear form enters quadratically, as proved by the complement theorem. -/

noncomputable section
namespace ContinuumCoulomb

theorem singular_complement_scaled_identity {R a g : ℝ}
    (hR : R ≠ 0) (ha : a ≠ 0) (hg : g ≠ 0) (n K b : ℝ) :
    (a*R^30)*(3*((2*n*(R^19)⁻¹)^2+(a*R^30)⁻¹^2*(8*n^3*K)+
      (b/R^20)^2*(n+2*K)*n)/g) =
      (12*a*n^2/R^8+24*n^3*K/(a*R^30)+3*a*b^2*(n+2*K)*n/R^10)/g := by
  field_simp [hR,ha,hg]
  ring

theorem exists_complement_error_scale {a b : ℝ} (ha : 0 < a) :
    ∃ k₀ : ℕ, 1 ≤ k₀ ∧ ∀ r q s p k : ℕ, k₀+3*r+q+s+p ≤ k →
      ∀ N : ℝ, 2 ≤ N → ∀ n K g : ℝ, 0 ≤ n → n ≤ N^r → 0 ≤ K → K ≤ N^q →
      (N^s)⁻¹ ≤ g →
      (a*(N^k)^30)*(3*((2*n*((N^k)^19)⁻¹)^2+
        (a*(N^k)^30)⁻¹^2*(8*n^3*K)+(b/(N^k)^20)^2*(n+2*K)*n)/g) ≤
        (N^p)⁻¹ := by
  let C := 12*a+24/a+9*a*b^2
  obtain ⟨c,hc,hconst⟩ := exists_polynomial_constant_bounds
    (show (0:ℝ)<1 by norm_num) C
  refine ⟨c+1,by omega,fun r q s p k hk N hN n K g hn hnN hK hKN hg => ?_⟩
  have hN0 : 0 < N := by linarith
  have hN1 : 1 ≤ N := by linarith
  have hR0 : 0 < N^k := pow_pos hN0 _
  have hR1 : 1 ≤ N^k := one_le_pow₀ hN1
  have hg0 : 0 < g := (inv_pos.mpr (pow_pos hN0 s)).trans_le hg
  have hNs : 1/g ≤ N^s := by
    apply (div_le_iff₀ hg0).mpr
    have h := mul_le_mul_of_nonneg_left hg (pow_nonneg hN0.le s)
    simpa only [mul_inv_cancel₀ (ne_of_gt (pow_pos hN0 s))] using h
  let E := 3*r+q
  have hn2 : n^2 ≤ N^E := by
    calc
      _ ≤ (N^r)^2 := pow_le_pow_left₀ hn hnN 2
      _ = N^(r*2) := (pow_mul _ _ _).symm
      _ ≤ _ := pow_le_pow_right₀ hN1 (by dsimp [E]; omega)
  have hn3K : n^3*K ≤ N^E := by
    calc
      _ ≤ (N^r)^3*N^q := mul_le_mul (pow_le_pow_left₀ hn hnN 3) hKN hK (by positivity)
      _ = _ := by dsimp [E]; rw [← pow_mul,← pow_add]; congr 1; omega
  have hnK : (n+2*K)*n ≤ 3*N^E := by
    have hn' : n ≤ N^(r+q) := hnN.trans (pow_le_pow_right₀ hN1 (by omega))
    have hK' : K ≤ N^(r+q) := hKN.trans (pow_le_pow_right₀ hN1 (by omega))
    have hh : n+2*K ≤ 3*N^(r+q) := by linarith
    calc
      _ ≤ (3*N^(r+q))*N^r := mul_le_mul hh hnN hn (by positivity)
      _ = 3*N^(r+q+r) := by rw [pow_add]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (pow_le_pow_right₀ hN1 (by dsimp [E]; omega)) (by norm_num)
  have ht1 : 12*a*n^2/(N^k)^8 ≤ 12*a*N^E/(N^k)^8 := by gcongr
  have ht2 : 24*n^3*K/(a*(N^k)^30) ≤ (24/a)*N^E/(N^k)^8 := by
    calc
      _ = (24/a)*(n^3*K)/(N^k)^30 := by ring
      _ ≤ (24/a)*N^E/(N^k)^30 := by gcongr
      _ ≤ _ := div_le_div_of_nonneg_left (by positivity) (by positivity)
        (pow_le_pow_right₀ hR1 (by decide : 8 ≤ 30))
  have ht3 : 3*a*b^2*(n+2*K)*n/(N^k)^10 ≤ 9*a*b^2*N^E/(N^k)^8 := by
    calc
      _ = (3*a*b^2)*((n+2*K)*n)/(N^k)^10 := by ring
      _ ≤ (3*a*b^2)*(3*N^E)/(N^k)^10 := by gcongr
      _ = (9*a*b^2)*N^E/(N^k)^10 := by ring
      _ ≤ _ := div_le_div_of_nonneg_left (by positivity) (by positivity)
        (pow_le_pow_right₀ hR1 (by decide : 8 ≤ 10))
  rw [singular_complement_scaled_identity (ne_of_gt hR0) (ne_of_gt ha) (ne_of_gt hg0)]
  calc
    _ ≤ (C*N^E/(N^k)^8)/g := by
      apply div_le_div_of_nonneg_right _ hg0.le
      calc
        _ ≤ 12*a*N^E/(N^k)^8+(24/a)*N^E/(N^k)^8+9*a*b^2*N^E/(N^k)^8 :=
          add_le_add (add_le_add ht1 ht2) ht3
        _ = _ := by dsimp [C]; ring
    _ ≤ (C*N^E/(N^k)^8)*N^s := by
      simpa only [div_eq_mul_inv,one_mul] using
        mul_le_mul_of_nonneg_left hNs (show 0 ≤ C*N^E/(N^k)^8 by dsimp [C]; positivity)
    _ = C*N^(E+s)/(N^k)^8 := by rw [pow_add]; ring
    _ ≤ N^c*N^(E+s)/(N^k)^8 := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_right (hconst N hN).2 (by positivity)
    _ ≤ (N^p)⁻¹ := by
      rw [← pow_add,← pow_mul,inv_eq_one_div,
        div_le_div_iff₀ (pow_pos hN0 _) (pow_pos hN0 _),one_mul,← pow_add]
      exact pow_le_pow_right₀ hN1 (by dsimp [E]; omega)

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
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_ManufacturedComplementBudget
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit polynomial bounds for the actual kinetic budget and the
coercive complement allowance in the manufactured Hubbard comparison. -/

noncomputable section
namespace ContinuumCoulomb

theorem manufacturedKineticBudgetConstant_positive {freq rho : ℝ}
    (hf : 1 ≤ freq) (hrho : 0 ≤ rho) : 0 < manufacturedKineticBudgetConstant freq rho := by
  have hW := PlanarSobolev.wellBound_nonnegative
  have hA : 0 ≤ (-1/2:ℝ)+freq/2 := by linarith
  unfold manufacturedKineticBudgetConstant
  positivity

theorem manufactured_kinetic_complement_budgets {freq rho γ M η ε : ℝ}
    (hf : 1 ≤ freq) (hrho : 0 ≤ rho) (hγ : 0 < γ) (hγ1 : γ ≤ 1/4)
    (hM : 1 ≤ M) (hη : 0 ≤ η) (hη1 : η ≤ 1) (hε : ε ≤ 1) :
    M*((M+η)*PlanarSobolev.wellBound+6*Real.pi*rho+((-1/2:ℝ)+freq/2))+2*M*ε ≤
      manufacturedKineticBudgetConstant freq rho*M^2 ∧
    (γ/(16*manufacturedKineticBudgetConstant freq rho))/M^2 ≤
      (γ/8)/(2*(M*((M+η)*PlanarSobolev.wellBound+6*Real.pi*rho+
        ((-1/2:ℝ)+freq/2))+γ/8+1)) := by
  let A := 6*Real.pi*rho+((-1/2:ℝ)+freq/2)
  let C := manufacturedKineticBudgetConstant freq rho
  have hW := PlanarSobolev.wellBound_nonnegative
  have hA : 0 ≤ A := by
    have hE : 0 ≤ (-1/2:ℝ)+freq/2 := by linarith
    exact add_nonneg (mul_nonneg (mul_nonneg (by norm_num) Real.pi_pos.le) hrho) hE
  have hC : 0 < C := manufacturedKineticBudgetConstant_positive hf hrho
  have hM0 : 0 < M := lt_of_lt_of_le zero_lt_one hM
  have hT : M*((M+η)*PlanarSobolev.wellBound+A) ≤ (2*PlanarSobolev.wellBound+A)*M^2 := by
    have hsum : M+η ≤ 2*M := by linarith
    have hterm := add_le_add (mul_le_mul_of_nonneg_right hsum hW)
      (le_mul_of_one_le_right hA hM)
    have h := mul_le_mul_of_nonneg_left hterm hM0.le
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    ring
  have hK : 2*M*ε ≤ 2*M^2 := by
    have h := mul_le_mul_of_nonneg_left hε (show 0 ≤ 2*M by positivity)
    nlinarith [sq_nonneg (M-1)]
  have hγb : γ/8+1 ≤ 2*M^2 := by nlinarith [sq_nonneg (M-1)]
  have hden : 2*(M*((M+η)*PlanarSobolev.wellBound+A)+γ/8+1) ≤ 2*C*M^2 := by
    dsimp only [C,manufacturedKineticBudgetConstant,A] at *
    nlinarith only [hT,hγb]
  have hden0 : 0 < 2*(M*((M+η)*PlanarSobolev.wellBound+A)+γ/8+1) := by positivity
  constructor
  · dsimp only [manufacturedKineticBudgetConstant]
    dsimp only [A] at hT
    nlinarith only [hT,hK]
  · have hfinal : (γ/(16*C))/M^2 ≤ (γ/8)/(2*(M*((M+η)*PlanarSobolev.wellBound+A)+γ/8+1)) := by
      calc
        _ = (γ/8)/(2*C*M^2) := by field_simp; norm_num
        _ ≤ _ := div_le_div_of_nonneg_left (by positivity) hden0 hden
    convert hfinal using 1
    all_goals try with_reducible_and_instances rfl
    dsimp [A,C]
    ring

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_ManyBody_ComplementParameterBounds
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial particle counts meet the exact separation and coercivity
conditions used by the full manufactured-field comparison. -/

noncomputable section
namespace ContinuumCoulomb

theorem polynomial_count_le_exp_separation {N D : ℝ} (hN : 2 ≤ N)
    {r k : ℕ} (hrk : r ≤ k) (hD : 25*(k:ℝ)*Real.log N ≤ D) :
    N^r ≤ Real.exp ((19/320:ℝ)*D) := by
  have hN0 : 0 < N := by linarith
  have hlog : 0 ≤ Real.log N := Real.log_nonneg (by linarith)
  have hrlog : (r:ℝ)*Real.log N ≤ (k:ℝ)*Real.log N :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast hrk) hlog
  have hklog : 0 ≤ (k:ℝ)*Real.log N := mul_nonneg (Nat.cast_nonneg _) hlog
  calc
    _ = Real.exp ((r:ℝ)*Real.log N) := by rw [Real.exp_nat_mul,Real.exp_log hN0]
    _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith only [hrlog,hklog,hD])

theorem exists_manufactured_kinetic_exponent {freq rho γ : ℝ}
    (hf : 1 ≤ freq) (hrho : 0 ≤ rho) (hγ : 0 < γ) (hγ1 : γ ≤ 1/4) :
    ∃ q : ℕ, 1 ≤ q ∧ ∀ (N : ℝ), 2 ≤ N → ∀ (r : ℕ) (M η ε : ℝ),
      1 ≤ M → M ≤ N^r → 0 ≤ η → η ≤ 1 → ε ≤ 1 →
      M*((M+η)*PlanarSobolev.wellBound+6*Real.pi*rho+((-1/2:ℝ)+freq/2))+2*M*ε ≤
        N^(q+2*r) ∧
      2/N^(q+2*r) ≤ (γ/8)/(2*(M*((M+η)*PlanarSobolev.wellBound+6*Real.pi*rho+
        ((-1/2:ℝ)+freq/2))+γ/8+1)) := by
  let C := manufacturedKineticBudgetConstant freq rho
  let b := γ/(16*C)
  have hC : 0 < C := manufacturedKineticBudgetConstant_positive hf hrho
  have hb : 0 < b := by dsimp [b]; positivity
  obtain ⟨q,hq,hbound⟩ := exists_polynomial_constant_bounds (by positivity : 0 < b/2) C
  refine ⟨q,by omega,fun N hN r M η ε hM hMN hη hη1 hε => ?_⟩
  have hN0 : 0 < N := by linarith
  have hMp : 0 < M := lt_of_lt_of_le zero_lt_one hM
  have hM2 : M^2 ≤ N^(2*r) := by
    rw [show 2*r=r*2 by omega,pow_mul]
    exact pow_le_pow_left₀ hMp.le hMN 2
  obtain ⟨hkin,hgap⟩ := manufactured_kinetic_complement_budgets hf hrho hγ hγ1 hM hη hη1 hε
  constructor
  · apply hkin.trans
    change C*M^2 ≤ _
    calc
      _ ≤ N^q*N^(2*r) := mul_le_mul (hbound N hN).2 hM2 (sq_nonneg M) (by positivity)
      _ = _ := (pow_add _ _ _).symm
  · have hsmall : 2/(N^q) ≤ b := by
      have h := (hbound N hN).1
      change (N^q)⁻¹ ≤ b/2 at h
      change 2*(N^q)⁻¹ ≤ b
      linarith
    have hn : 2/N^(q+2*r) ≤ b/N^(2*r) := by
      calc
        _ = (2/N^q)/N^(2*r) := by rw [pow_add]; field_simp
        _ ≤ _ := div_le_div_of_nonneg_right hsmall (by positivity)
    apply hn.trans
    apply le_trans _ hgap
    change b/N^(2*r) ≤ b/M^2
    exact div_le_div_of_nonneg_left hb.le (pow_pos hMp 2) hM2

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_ManyBody_ComplementSmallness
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fixed exponent thresholds for the two smallness hypotheses in the
full-domain complement estimate. -/

noncomputable section
namespace ContinuumCoulomb

theorem exists_residual_complement_smallness {γ : ℝ} (hγ : 0 < γ) :
    ∃ q : ℕ, 1 ≤ q ∧ ∀ r k : ℕ, q+r ≤ k → ∀ N M : ℝ,
      2 ≤ N → 0 ≤ M → M ≤ N^r →
      M*((1/(N^k)^19)+(1/(N^k)^19)^2/(γ/4)) ≤ γ/8 := by
  obtain ⟨q,hq,hbound⟩ := exists_polynomial_ratio_offset (1+4/γ) (by positivity : 0 < γ/8)
  refine ⟨q,hq,fun r k hk N M hN hM hMN => ?_⟩
  have hN0 : 0 < N := by linarith
  have hR0 : 0 < N^k := by positivity
  have hR1 : 1 ≤ N^k := one_le_pow₀ (by linarith : 1 ≤ N)
  have h1 : M/(N^k)^19 ≤ N^r/(N^k)^2 := by
    gcongr
    decide
  have h2 : (4/γ)*M/(N^k)^38 ≤ (4/γ)*N^r/(N^k)^2 := by
    gcongr
    decide
  calc
    _ = M/(N^k)^19+(4/γ)*M/(N^k)^38 := by field_simp [ne_of_gt hγ]
    _ ≤ N^r/(N^k)^2+(4/γ)*N^r/(N^k)^2 := add_le_add h1 h2
    _ = (1+4/γ)*N^r/(N^k)^2 := by ring
    _ ≤ γ/8 := by simpa only [Nat.add_zero,pow_zero,div_one] using hbound r 0 k (by omega) N hN

theorem exists_nuclear_complement_smallness {a b B : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hB : 0 ≤ B) :
    ∃ q : ℕ, 1 ≤ q ∧ ∀ r u k : ℕ, q+3*r+u ≤ k → ∀ N M A : ℝ,
      2 ≤ N → 0 ≤ M → M ≤ N^r → |A| ≤ N^u →
      0 < b/(2*N^(2*r)) ∧
      (B/(N^k)^20)*M+|A/(a*(N^k)^30)|+b/(2*N^(2*r)) ≤ b/N^(2*r) := by
  obtain ⟨q,hq,hbound⟩ := exists_polynomial_ratio_offset (B+1/a) (by positivity : 0 < b/2)
  refine ⟨q,hq,fun r u k hk N M A hN hM hMN hA => ?_⟩
  have hN0 : 0 < N := by linarith
  have hN1 : 1 ≤ N := by linarith
  have hR0 : 0 < N^k := by positivity
  have hR1 : 1 ≤ N^k := one_le_pow₀ hN1
  have hr : N^r ≤ N^(r+u) := pow_le_pow_right₀ hN1 (by omega)
  have hu : N^u ≤ N^(r+u) := pow_le_pow_right₀ hN1 (by omega)
  have h1 : (B/(N^k)^20)*M ≤ B*N^(r+u)/(N^k)^2 := by
    calc
      _ = B*M/(N^k)^20 := by ring
      _ ≤ _ := by gcongr <;> first | exact hMN.trans hr | decide
  have h2 : |A/(a*(N^k)^30)| ≤ (1/a)*N^(r+u)/(N^k)^2 := by
    rw [abs_div,abs_of_pos (show 0 < a*(N^k)^30 by positivity)]
    calc
      _ = (1/a)*|A|/(N^k)^30 := by ring
      _ ≤ _ := by gcongr <;> first | exact hA.trans hu | decide
  have hsum : (B/(N^k)^20)*M+|A/(a*(N^k)^30)| ≤ (b/2)/N^(2*r) := by
    calc
      _ ≤ B*N^(r+u)/(N^k)^2+(1/a)*N^(r+u)/(N^k)^2 := add_le_add h1 h2
      _ = (B+1/a)*N^(r+u)/(N^k)^2 := by ring
      _ ≤ _ := hbound (r+u) (2*r) k (by omega) N hN
  refine ⟨by positivity,?_⟩
  calc
    _ ≤ (b/2)/N^(2*r)+b/(2*N^(2*r)) := add_le_add hsum le_rfl
    _ = _ := by ring

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.Laughlin_Operators_CAR
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockCoordinates_apply _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockCoordinates_assemble _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockOperator_add _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockOperator_coordinates _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockOperator_mul _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockOperator_smul _root_.OAI.ContinuumCoulomb.OccupationFock.sectorEquiv_apply _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock

theorem mixed_car {Q : ℕ} (i j : Fin (Q+1)) :
    annihilate i * create j + create j * annihilate i =
      (if i = j then (1 : ℂ) else 0) • (1 : Module.End ℂ (Space Q)) := by
  refine LinearMap.ext fun x => ?_
  change CliffordAlgebra.contractLeft (LinearMap.proj i : Module.Dual ℂ (Orbital Q))
      (ExteriorAlgebra.ι ℂ (mode j) * x) +
    ExteriorAlgebra.ι ℂ (mode j) * CliffordAlgebra.contractLeft (LinearMap.proj i : Module.Dual ℂ (Orbital Q)) x =
      (if i = j then (1 : ℂ) else 0) • x
  rw [CliffordAlgebra.contractLeft_ι_mul, sub_add_cancel]
  by_cases h : i = j
  · subst j
    simp [mode, LinearMap.proj]
  · simp [mode, LinearMap.proj, h]

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_ManyBody_HubbardOccupation
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockCoordinates_apply _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockCoordinates_assemble _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockOperator_add _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockOperator_coordinates _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockOperator_mul _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockOperator_smul _root_.OAI.ContinuumCoulomb.OccupationFock.sectorEquiv_apply _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual occupation-basis diagonal action for the global Hubbard model. -/

noncomputable section
namespace ContinuumCoulomb.HubbardGlobal
open Laughlin.Fock
open scoped BigOperators
variable {Q : ℕ}

theorem annihilate_unoccupied_wedge (i : Fin (Q + 1)) (n : ℕ)
    (w : Fin n → Fin (Q + 1)) (hi : ∀ k, w k ≠ i) :
    annihilate i (ExteriorAlgebra.ιMulti ℂ n (fun k => mode (w k))) = 0 := by
  induction n with
  | zero => simp [annihilate]
  | succ n ih =>
    rw [ExteriorAlgebra.ιMulti_succ_apply]
    change CliffordAlgebra.contractLeft (LinearMap.proj i)
      (ExteriorAlgebra.ι ℂ (mode (w 0)) *
        ExteriorAlgebra.ιMulti ℂ n (fun k => mode (w k.succ))) = 0
    rw [CliffordAlgebra.contractLeft_ι_mul]
    have hmode : (LinearMap.proj i : Orbital Q →ₗ[ℂ] ℂ) (mode (w 0)) = 0 := by
      simp [LinearMap.proj, mode, Ne.symm (hi 0)]
    have htail := ih (fun k => w k.succ) (fun k => hi k.succ)
    change CliffordAlgebra.contractLeft (LinearMap.proj i)
      (ExteriorAlgebra.ιMulti ℂ n (fun k => mode (w k.succ))) = 0 at htail
    rw [hmode, htail]
    simp

theorem annihilate_unoccupied_basis (i : Fin (Q + 1))
    (A : Finset (Fin (Q + 1))) (hi : i ∉ A) :
    annihilate i (fockBasis Q A) = 0 := by
  let S : Set.powersetCard (Fin (Q + 1)) A.card := ⟨A, rfl⟩
  have hn (k : Fin A.card) : Set.powersetCard.ofFinEmbEquiv.symm S k ≠ i := by
    intro h
    apply hi
    rw [← h]
    exact (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem S _).mp ⟨k, rfl⟩
  have h := annihilate_unoccupied_wedge i A.card
    (Set.powersetCard.ofFinEmbEquiv.symm S) hn
  change annihilate i ((Pi.basisFun ℂ (Fin (Q + 1))).ExteriorAlgebra S.val) = 0
  rw [ExteriorAlgebra.basis_apply_powersetCard]
  simpa only [ExteriorAlgebra.ιMulti_family, Function.comp_def, Pi.basisFun_apply, mode] using h

theorem fockBasis_singleton (i : Fin (Q + 1)) :
    fockBasis Q {i} = ExteriorAlgebra.ι ℂ (mode i) := by
  let S : Set.powersetCard (Fin (Q + 1)) 1 := ⟨{i}, Finset.card_singleton i⟩
  have hi : Set.powersetCard.ofFinEmbEquiv.symm S 0 = i := by
    have hm := (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem S
      (Set.powersetCard.ofFinEmbEquiv.symm S 0)).mp ⟨0, rfl⟩
    exact Finset.mem_singleton.mp hm
  change (Pi.basisFun ℂ (Fin (Q + 1))).ExteriorAlgebra S.val = _
  rw [ExteriorAlgebra.basis_apply_powersetCard]
  simp only [ExteriorAlgebra.ιMulti_family, ExteriorAlgebra.ιMulti_succ_apply,
    ExteriorAlgebra.ιMulti_zero_apply, mul_one, Function.comp_apply, hi]
  simp [Pi.basisFun_apply, mode]

theorem create_occupied_basis (i : Fin (Q + 1))
    (A : Finset (Fin (Q + 1))) (hi : i ∈ A) : create i (fockBasis Q A) = 0 := by
  have hd : ¬Disjoint ({i} : Finset (Fin (Q + 1))) A := by simpa using hi
  have h := ExteriorAlgebra.basis_mul_of_not_disjoint (Pi.basisFun ℂ (Fin (Q + 1)))
    (⟨{i}, Finset.card_singleton i⟩ : Set.powersetCard (Fin (Q + 1)) 1)
    (⟨A, rfl⟩ : Set.powersetCard (Fin (Q + 1)) A.card) hd
  change fockBasis Q {i} * fockBasis Q A = 0 at h
  rw [fockBasis_singleton] at h
  exact h

/-- Each actual number operator is diagonal in the full occupation
basis, including every spectator mode. -/
theorem number_basis (i : Fin (Q + 1)) (A : Finset (Fin (Q + 1))) :
    number i (fockBasis Q A) = if i ∈ A then fockBasis Q A else 0 := by
  by_cases hi : i ∈ A
  · have h := LinearMap.congr_fun (mixed_car i i) (fockBasis Q A)
    change annihilate i (create i (fockBasis Q A)) +
      create i (annihilate i (fockBasis Q A)) =
        (if i = i then (1 : ℂ) else 0) • fockBasis Q A at h
    simpa [hi, create_occupied_basis i A hi, number, transfer] using h
  · simpa [hi, number, transfer] using
      congrArg (create i) (annihilate_unoccupied_basis i A hi)

end ContinuumCoulomb.HubbardGlobal

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_ManyBody_HubbardExcitation
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockCoordinates_apply _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockCoordinates_assemble _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockOperator_add _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockOperator_coordinates _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockOperator_mul _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockOperator_smul _root_.OAI.ContinuumCoulomb.OccupationFock.sectorEquiv_apply _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual occupation-diagonal inverse and charge-selection rules. -/

noncomputable section
namespace ContinuumCoulomb.HubbardGlobal
open Laughlin.Fock
open scoped BigOperators

variable {Q : ℕ}

theorem fockDiagonal_basis (f : Finset (Fin (Q + 1)) → ℂ)
    (A : Finset (Fin (Q + 1))) :
    fockDiagonal f (fockBasis Q A) = f A • fockBasis Q A :=
  (fockBasis Q).constr_basis ℂ _ A

theorem fockDiagonal_coordinate (f : Finset (Fin (Q + 1)) → ℂ)
    (x : Space Q) (A : Finset (Fin (Q + 1))) :
    (fockBasis Q).repr (fockDiagonal f x) A = f A * (fockBasis Q).repr x A := by
  have h : ((fockBasis Q).coord A).comp (fockDiagonal f) =
      f A • (fockBasis Q).coord A := by
    apply (fockBasis Q).ext
    intro S
    change (fockBasis Q).repr (fockDiagonal f (fockBasis Q S)) A =
      f A * (fockBasis Q).repr (fockBasis Q S) A
    rw [fockDiagonal_basis, map_smul, Finsupp.smul_apply, smul_eq_mul]
    by_cases hSA : S = A
    · subst S
      simp
    · simp [Module.Basis.repr_self, hSA]
  exact LinearMap.congr_fun h x

end ContinuumCoulomb.HubbardGlobal

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_ManyBody_SpinEmbedding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The canonical, norm-preserving embedding of the spin sector in Fock space. -/

noncomputable section
namespace ContinuumCoulomb.HubbardGlobal
open Laughlin.Fock
open scoped BigOperators

/-- The ordered spin wedge is exactly a canonical occupation-basis
vector, with no arbitrary normalization or phase. -/
theorem spinWedge_eq_fockBasis (m : ℕ) (s : SourceSpinBasis (m + 1)) :
    spinWedge m s = fockBasis (2 * m + 1) (spinOccupationSet m s) := by
  let S := Set.powersetCard.ofFinEmbEquiv (spinModeOrderEmbedding m s)
  change wedgeModes (m + 1) (fun i => siteMode m i (s i)) =
    (Pi.basisFun ℂ (Fin ((2 * m + 1) + 1))).ExteriorAlgebra S.val
  rw [ExteriorAlgebra.basis_apply_powersetCard]
  simp only [ExteriorAlgebra.ιMulti_family, S, Equiv.symm_apply_apply]
  unfold wedgeModes
  congr 1
  funext i
  rw [Function.comp_apply, Pi.basisFun_apply]
  rfl

end ContinuumCoulomb.HubbardGlobal

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_ManyBody_FockNorm
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockCoordinates_assemble _root_.OAI.ContinuumCoulomb.OccupationFock.sectorEquiv_apply _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial operator bounds from the actual exterior occupation basis. -/

noncomputable section
namespace ContinuumCoulomb.HubbardGlobal
open Laughlin.Fock
open scoped BigOperators InnerProductSpace
variable {Q : ℕ}

/-- A creator sends an unoccupied canonical basis vector to the inserted
occupation with its actual exterior permutation sign. -/
theorem create_unoccupied_basis_signed (i : Fin (Q + 1))
    (A : Finset (Fin (Q + 1))) (hi : i ∉ A) :
    ∃ c : ℂ, (c = 1 ∨ c = -1) ∧
      create i (fockBasis Q A) = c • fockBasis Q (insert i A) := by
  let S : Set.powersetCard (Fin (Q + 1)) 1 := ⟨{i}, Finset.card_singleton i⟩
  let T : Set.powersetCard (Fin (Q + 1)) A.card := ⟨A, rfl⟩
  have hd : Disjoint S.val T.val := by simpa only [S, T, Finset.disjoint_singleton_left]
  have h := ExteriorAlgebra.basis_mul_of_disjoint
    (Pi.basisFun ℂ (Fin (Q + 1))) S T hd
  have hset : (Set.powersetCard.disjUnion hd).val = insert i A := by
    ext k
    simp [Set.powersetCard.disjUnion, S, T]
  change fockBasis Q {i} * fockBasis Q A =
    (Set.powersetCard.permOfDisjoint hd).sign •
      fockBasis Q (Set.powersetCard.disjUnion hd).val at h
  rw [fockBasis_singleton, hset] at h
  rcases Int.units_eq_one_or (Set.powersetCard.permOfDisjoint hd).sign with hs | hs
  · refine ⟨1, Or.inl rfl, ?_⟩
    simpa only [hs, one_smul, create, LinearMap.coe_mk, AddHom.coe_mk] using h
  · refine ⟨-1, Or.inr rfl, ?_⟩
    simpa only [hs, Units.neg_smul, one_smul, neg_smul,
      create, LinearMap.coe_mk, AddHom.coe_mk] using h

theorem creationCoefficient_signed (i : Fin (Q + 1))
    (A : Finset (Fin (Q + 1))) (hi : i ∉ A) :
    creationCoefficient i A = 1 ∨ creationCoefficient i A = -1 := by
  obtain ⟨c, hc, h⟩ := create_unoccupied_basis_signed i A hi
  have heq : creationCoefficient i A = c := by
    simp [creationCoefficient, h]
  simpa only [heq] using hc

theorem creationCoefficient_occupied (i : Fin (Q + 1))
    (A : Finset (Fin (Q + 1))) (hi : i ∈ A) : creationCoefficient i A = 0 := by
  simp [creationCoefficient, create_occupied_basis i A hi]

theorem create_basis (i : Fin (Q + 1)) (A : Finset (Fin (Q + 1))) :
    create i (fockBasis Q A) = creationCoefficient i A • fockBasis Q (insert i A) := by
  by_cases hi : i ∈ A
  · simp [create_occupied_basis i A hi, creationCoefficient_occupied i A hi]
  · obtain ⟨c, _, hc⟩ := create_unoccupied_basis_signed i A hi
    have heq : creationCoefficient i A = c := by simp [creationCoefficient, hc]
    rw [heq, hc]

theorem annihilate_create_unoccupied_basis (i : Fin (Q + 1))
    (A : Finset (Fin (Q + 1))) (hi : i ∉ A) :
    annihilate i (create i (fockBasis Q A)) = fockBasis Q A := by
  have h := LinearMap.congr_fun (mixed_car i i) (fockBasis Q A)
  change annihilate i (create i (fockBasis Q A)) +
    number i (fockBasis Q A) = (if i = i then (1 : ℂ) else 0) • fockBasis Q A at h
  simpa [number_basis, hi] using h

theorem annihilate_occupied_basis (i : Fin (Q + 1))
    (A : Finset (Fin (Q + 1))) (hi : i ∈ A) :
    annihilate i (fockBasis Q A) =
      creationCoefficient i (A.erase i) • fockBasis Q (A.erase i) := by
  have h := annihilate_create_unoccupied_basis i (A.erase i) (Finset.notMem_erase _ _)
  rw [create_basis, Finset.insert_erase hi, map_smul] at h
  have hc : creationCoefficient i (A.erase i) * creationCoefficient i (A.erase i) = 1 := by
    rcases creationCoefficient_signed i (A.erase i) (Finset.notMem_erase _ _) with hc | hc
    all_goals simp [hc]
  calc
    _ = creationCoefficient i (A.erase i) •
        (creationCoefficient i (A.erase i) • annihilate i (fockBasis Q A)) := by
      rw [smul_smul, hc, one_smul]
    _ = _ := congrArg (fun x => creationCoefficient i (A.erase i) • x) h

theorem create_coordinate (i : Fin (Q + 1)) (x : Space Q)
    (B : Finset (Fin (Q + 1))) :
    (fockBasis Q).repr (create i x) B =
      if i ∈ B then creationCoefficient i (B.erase i) * (fockBasis Q).repr x (B.erase i)
      else 0 := by
  classical
  have h : create i x = ∑ A, (fockBasis Q).repr x A • create i (fockBasis Q A) := by
    simp only [← map_smul]
    rw [← map_sum, (fockBasis Q).sum_repr]
  rw [h, map_sum, Finsupp.finsetSum_apply]
  simp only [create_basis, map_smul, Finsupp.smul_apply, smul_eq_mul]
  by_cases hi : i ∈ B
  · rw [ite_eq_left hi, Finset.sum_eq_single (B.erase i)]
    · simp [Finset.insert_erase hi, mul_comm]
    · intro A _ hA
      by_cases hiA : i ∈ A
      · simp [creationCoefficient_occupied i A hiA]
      · have hne : insert i A ≠ B := by
          intro hAB
          apply hA
          have he := congrArg (Finset.erase · i) hAB
          simpa only [Finset.erase_insert hiA] using he
        simp [Module.Basis.repr_self, hne]
    · simp
  · rw [ite_eq_right hi]
    apply Finset.sum_eq_zero
    intro A _
    have hne : insert i A ≠ B := by
      intro hAB
      exact hi (hAB ▸ Finset.mem_insert_self i A)
    simp [Module.Basis.repr_self, hne]

theorem annihilate_coordinate (i : Fin (Q + 1)) (x : Space Q)
    (B : Finset (Fin (Q + 1))) :
    (fockBasis Q).repr (annihilate i x) B =
      if i ∉ B then creationCoefficient i B * (fockBasis Q).repr x (insert i B)
      else 0 := by
  classical
  have h : annihilate i x =
      ∑ A, (fockBasis Q).repr x A • annihilate i (fockBasis Q A) := by
    simp only [← map_smul]
    rw [← map_sum, (fockBasis Q).sum_repr]
  rw [h, map_sum, Finsupp.finsetSum_apply]
  by_cases hi : i ∈ B
  · rw [ite_eq_right (not_not.mpr hi)]
    apply Finset.sum_eq_zero
    intro A _
    by_cases hiA : i ∈ A
    · rw [annihilate_occupied_basis i A hiA]
      have hne : A.erase i ≠ B := by
        intro he
        exact (Finset.notMem_erase i A) (he.symm ▸ hi)
      simp [Module.Basis.repr_self, hne]
    · simp [annihilate_unoccupied_basis i A hiA]
  · rw [ite_eq_left hi, Finset.sum_eq_single (insert i B)]
    · rw [annihilate_occupied_basis i (insert i B) (Finset.mem_insert_self _ _),
        Finset.erase_insert hi]
      simp [mul_comm]
    · intro A _ hA
      by_cases hiA : i ∈ A
      · rw [annihilate_occupied_basis i A hiA]
        have hne : A.erase i ≠ B := by
          intro he
          exact hA ((Finset.insert_erase hiA).symm.trans (congrArg (insert i) he))
        simp [Module.Basis.repr_self, hne]
      · simp [annihilate_unoccupied_basis i A hiA]
    · simp

theorem fockMass_create (i : Fin (Q + 1)) (x : Space Q) :
    fockMass (create i x) =
      ∑ A : {A : Finset (Fin (Q + 1)) // i ∉ A},
        Complex.normSq ((fockBasis Q).repr x A.val) := by
  classical
  have hpoint (B : Finset (Fin (Q + 1))) :
      Complex.normSq ((fockBasis Q).repr (create i x) B) =
        if i ∈ B then Complex.normSq ((fockBasis Q).repr x (B.erase i)) else 0 := by
    rw [create_coordinate]
    by_cases hi : i ∈ B
    · simp only [hi, ↓reduceIte]
      rcases creationCoefficient_signed i (B.erase i) (Finset.notMem_erase _ _) with hc | hc
      all_goals simp [hc]
    · simp [hi]
  unfold fockMass
  simp_rw [hpoint]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero,
    Finset.sum_subtype (p := fun A : Finset (Fin (Q + 1)) => i ∈ A) _ (by simp)]
  have h := (insertModeEquiv i).sum_comp
    (fun B => Complex.normSq ((fockBasis Q).repr x (B.val.erase i)))
  simp_rw [insertModeEquiv_erase] at h
  exact h.symm

theorem fockMass_annihilate (i : Fin (Q + 1)) (x : Space Q) :
    fockMass (annihilate i x) =
      ∑ A : {A : Finset (Fin (Q + 1)) // i ∈ A},
        Complex.normSq ((fockBasis Q).repr x A.val) := by
  classical
  have hpoint (B : Finset (Fin (Q + 1))) :
      Complex.normSq ((fockBasis Q).repr (annihilate i x) B) =
        if i ∉ B then Complex.normSq ((fockBasis Q).repr x (insert i B)) else 0 := by
    rw [annihilate_coordinate]
    by_cases hi : i ∉ B
    · simp only [hi]
      rcases creationCoefficient_signed i B hi with hc | hc
      all_goals simp [hc]
    · simp [hi]
  unfold fockMass
  simp_rw [hpoint]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero,
    Finset.sum_subtype (p := fun A : Finset (Fin (Q + 1)) => i ∉ A) _ (by simp)]
  have h := (insertModeEquiv i).symm.sum_comp
    (fun B => Complex.normSq ((fockBasis Q).repr x (insert i B.val)))
  simp_rw [insertModeEquiv_symm_insert] at h
  exact h.symm

theorem fockMass_create_le (i : Fin (Q + 1)) (x : Space Q) :
    fockMass (create i x) ≤ fockMass x := by
  classical
  rw [fockMass_create]
  have h := Fintype.sum_subtype_add_sum_subtype (fun A : Finset (Fin (Q + 1)) => i ∉ A)
    (fun A => Complex.normSq ((fockBasis Q).repr x A))
  have hnonneg : 0 ≤ ∑ A : {A : Finset (Fin (Q + 1)) // ¬i ∉ A},
      Complex.normSq ((fockBasis Q).repr x A.val) :=
    Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _
  change _ ≤ ∑ A, Complex.normSq ((fockBasis Q).repr x A)
  linarith

theorem fockMass_annihilate_le (i : Fin (Q + 1)) (x : Space Q) :
    fockMass (annihilate i x) ≤ fockMass x := by
  classical
  rw [fockMass_annihilate]
  have h := Fintype.sum_subtype_add_sum_subtype (fun A : Finset (Fin (Q + 1)) => i ∈ A)
    (fun A => Complex.normSq ((fockBasis Q).repr x A))
  have hnonneg : 0 ≤ ∑ A : {A : Finset (Fin (Q + 1)) // ¬i ∈ A},
      Complex.normSq ((fockBasis Q).repr x A.val) :=
    Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _
  change _ ≤ ∑ A, Complex.normSq ((fockBasis Q).repr x A)
  linarith

theorem fockCoordinates_norm_sq (x : Space Q) :
    ‖fockCoordinates Q x‖ ^ 2 = fockMass x := by
  simp only [EuclideanSpace.norm_sq_eq, fockCoordinates_apply,
    Complex.normSq_eq_norm_sq, fockMass]

theorem fockOperator_norm_le_one (T : Module.End ℂ (Space Q))
    (hT : ∀ x, fockMass (T x) ≤ fockMass x) : ‖fockOperator T‖ ≤ 1 := by
  apply (fockOperator T).opNorm_le_bound zero_le_one
  intro v
  obtain ⟨x, rfl⟩ := (fockCoordinates Q).surjective v
  rw [fockOperator_coordinates, one_mul]
  have h := hT x
  rw [← fockCoordinates_norm_sq, ← fockCoordinates_norm_sq] at h
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h

/-- Actual CAR creators and annihilators are contractions in the
canonical occupation norm, uniformly in the number of spectator modes. -/
theorem fockOperator_create_norm (i : Fin (Q + 1)) :
    ‖fockOperator (create i)‖ ≤ 1 :=
  fockOperator_norm_le_one _ (fockMass_create_le i)

theorem fockOperator_annihilate_norm (i : Fin (Q + 1)) :
    ‖fockOperator (annihilate i)‖ ≤ 1 :=
  fockOperator_norm_le_one _ (fockMass_annihilate_le i)

theorem fockOperator_sum {ι : Type*} (s : Finset ι)
    (T : ι → Module.End ℂ (Space Q)) :
    fockOperator (∑ i ∈ s, T i) = ∑ i ∈ s, fockOperator (T i) := by
  ext v
  obtain ⟨x, rfl⟩ := (fockCoordinates Q).surjective v
  simp only [fockOperator_coordinates, sum_apply,
    LinearMap.sum_apply, map_sum]

theorem fockOperator_transfer_norm (i j : Fin (Q + 1)) :
    ‖fockOperator (transfer i j)‖ ≤ 1 := by
  rw [transfer, fockOperator_mul]
  apply (ContinuousLinearMap.opNorm_comp_le _ _).trans
  exact (mul_le_mul (fockOperator_create_norm i) (fockOperator_annihilate_norm j)
    (norm_nonneg _) zero_le_one).trans_eq (one_mul _)

theorem fockOperator_bondTransfer_norm (i j : Fin (Q + 1)) :
    ‖fockOperator (bondTransfer i j)‖ ≤ 2 := by
  rw [bondTransfer, fockOperator_add]
  calc
    _ ≤ ‖fockOperator (transfer i j)‖ + ‖fockOperator (transfer j i)‖ := norm_add_le _ _
    _ ≤ 1 + 1 := add_le_add (fockOperator_transfer_norm i j) (fockOperator_transfer_norm j i)
    _ = 2 := by norm_num

theorem fockOperator_siteHopping_norm (m : ℕ) (i j : Fin (m + 1)) :
    ‖fockOperator (siteHopping m i j)‖ ≤ 4 := by
  change ‖fockOperator (_ + _)‖ ≤ _
  rw [fockOperator_add]
  calc
    _ ≤ ‖fockOperator (bondTransfer (siteMode m i 0) (siteMode m j 0))‖ +
        ‖fockOperator (bondTransfer (siteMode m i 1) (siteMode m j 1))‖ := norm_add_le _ _
    _ ≤ 2 + 2 := add_le_add
      (fockOperator_bondTransfer_norm (siteMode m i 0) (siteMode m j 0))
      (fockOperator_bondTransfer_norm (siteMode m i 1) (siteMode m j 1))
    _ = 4 := by norm_num

/-- The actual global hopping has an edge-sum bound, independent of
the exponentially large Fock-space dimension. -/
theorem fockOperator_graphHopping_norm {Edge : Type*} [Fintype Edge]
    (m : ℕ) (left right : Edge → Fin (m + 1)) (t : Edge → ℂ) :
    ‖fockOperator (graphHopping m left right t)‖ ≤ 4 * ∑ e, ‖t e‖ := by
  unfold graphHopping
  rw [fockOperator_sum]
  simp only [fockOperator_smul]
  calc
    _ ≤ ∑ e, ‖t e • fockOperator (siteHopping m (left e) (right e))‖ := norm_sum_le _ _
    _ ≤ ∑ e, ‖t e‖ * 4 := Finset.sum_le_sum fun e _ => by
      rw [norm_smul]
      exact mul_le_mul_of_nonneg_left
        (fockOperator_siteHopping_norm m (left e) (right e)) (norm_nonneg _)
    _ = _ := by rw [← Finset.sum_mul, mul_comm]

end ContinuumCoulomb.HubbardGlobal

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_ManyBody_FockEnergyError
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Operator errors control every normalized occupation-sector energy with
polynomial mode dependence. The tensor and exterior norms are identified. -/

noncomputable section
open MeasureTheory
open scoped BigOperators Classical
namespace ContinuumCoulomb
open Laughlin.Fock HubbardGlobal

theorem occupationInner_fockCoordinates {Q : ℕ} (x y : Space Q) :
    occupationInner Q x y = inner ℂ (fockCoordinates Q x) (fockCoordinates Q y) := by
  simp only [PiLp.inner_apply,RCLike.inner_apply',fockCoordinates_apply,
    occupationInner,occupationBasis,fockBasis,starRingEnd_apply]

theorem occupationNormSq_fockCoordinates {Q : ℕ} (x : Space Q) :
    occupationNormSq Q x = ‖fockCoordinates Q x‖^2 := by
  simp only [fockCoordinates_norm_sq,occupationNormSq,fockMass,occupationBasis,fockBasis,
    Complex.normSq_eq_norm_sq]

theorem occupationInner_operator_error {Q : ℕ} (T U : Module.End ℂ (Space Q))
    (ε : ℝ) (hε : ‖fockOperator (T-U)‖ ≤ ε) (x : Space Q) :
    |(occupationInner Q x (T x)).re-(occupationInner Q x (U x)).re| ≤
      ε*occupationNormSq Q x := by
  rw [occupationInner_fockCoordinates,occupationInner_fockCoordinates,
    ← Complex.sub_re,← inner_sub_right,← map_sub,← LinearMap.sub_apply,
    ← fockOperator_coordinates]
  calc
    _ ≤ ‖inner ℂ (fockCoordinates Q x) (fockOperator (T-U) (fockCoordinates Q x))‖ :=
      Complex.abs_re_le_norm _
    _ ≤ ‖fockCoordinates Q x‖*‖fockOperator (T-U) (fockCoordinates Q x)‖ :=
      norm_inner_le_norm _ _
    _ ≤ ‖fockCoordinates Q x‖*(ε*‖fockCoordinates Q x‖) := by
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      exact ((fockOperator (T-U)).le_opNorm _).trans
        (mul_le_mul_of_nonneg_right hε (norm_nonneg _))
    _ = _ := by rw [occupationNormSq_fockCoordinates]; ring

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_ManyBody_HalfFilledSector
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual half-filled occupation basis splits into spins and charge defects. -/

noncomputable section
namespace ContinuumCoulomb.HubbardGlobal
open Laughlin.Fock
open scoped BigOperators

theorem spinOccupationSet_card (m : ℕ) (s : SourceSpinBasis (m + 1)) :
    (spinOccupationSet m s).card = m + 1 :=
  (Set.powersetCard.ofFinEmbEquiv (spinModeOrderEmbedding m s)).property

end ContinuumCoulomb.HubbardGlobal

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_ManyBody_FockSector
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockCoordinates_assemble _root_.OAI.ContinuumCoulomb.OccupationFock.sectorEquiv_apply _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fixed-particle support and the true low/high Fock projections. -/

noncomputable section
namespace ContinuumCoulomb.HubbardGlobal
open Laughlin.Fock
open scoped BigOperators InnerProductSpace

variable {Q : ℕ}

theorem totalNumber_basis (A : Finset (Fin (Q + 1))) :
    totalNumber Q (fockBasis Q A) = (A.card : ℂ) • fockBasis Q A := by
  simp only [totalNumber, LinearMap.sum_apply, number_basis]
  have hpoint (i : Fin (Q + 1)) :
      (if i ∈ A then fockBasis Q A else 0) =
        (if i ∈ A then (1 : ℂ) else 0) • fockBasis Q A := by
    split_ifs <;> simp
  simp_rw [hpoint]
  rw [← Finset.sum_smul]
  simp

theorem totalNumber_eq_diagonal (Q : ℕ) :
    totalNumber Q = fockDiagonal (fun A => (A.card : ℂ)) := by
  apply (fockBasis Q).ext
  intro A
  rw [totalNumber_basis, fockDiagonal_basis]

theorem totalNumber_eigen_coordinate_zero (N : ℕ) (x : Space Q)
    (hx : totalNumber Q x = (N : ℂ) • x) (A : Finset (Fin (Q + 1)))
    (hA : A.card ≠ N) : (fockBasis Q).repr x A = 0 := by
  have h := congrArg (fun y => (fockBasis Q).repr y A) hx
  rw [totalNumber_eq_diagonal, fockDiagonal_coordinate, map_smul,
    Finsupp.smul_apply, smul_eq_mul] at h
  have hne : (A.card : ℂ) ≠ (N : ℂ) := by exact_mod_cast hA
  have hz : ((A.card : ℂ) - N) * (fockBasis Q).repr x A = 0 := by
    rw [sub_mul, h, sub_self]
  exact (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hne)

theorem isHalfFilled_of_totalNumber (m : ℕ) (x : Space (2 * m + 1))
    (hx : totalNumber (2 * m + 1) x = ((m + 1 : ℕ) : ℂ) • x) : IsHalfFilled m x :=
  totalNumber_eigen_coordinate_zero (m + 1) x hx

theorem totalNumber_spinWedge (m : ℕ) (s : SourceSpinBasis (m + 1)) :
    totalNumber (2 * m + 1) (spinWedge m s) =
      ((m + 1 : ℕ) : ℂ) • spinWedge m s := by
  rw [spinWedge_eq_fockBasis, totalNumber_basis, spinOccupationSet_card]

end ContinuumCoulomb.HubbardGlobal

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_ManyBody_SuperexchangeSpectrum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact spectral identification of the global Hubbard inverse term. -/

noncomputable section
namespace ContinuumCoulomb.HubbardGlobal
open Laughlin.Fock
open scoped BigOperators InnerProductSpace
variable {Edge : Type*} [Fintype Edge]

theorem fockOperator_diagonal_apply {Q : ℕ} (f : Finset (Fin (Q + 1)) → ℂ)
    (x : FockCoordinateSpace Q) (A : Finset (Fin (Q + 1))) :
    fockOperator (fockDiagonal f) x A = f A * x A := by
  obtain ⟨y, rfl⟩ := (fockCoordinates Q).surjective x
  rw [fockOperator_coordinates, fockCoordinates_apply, fockDiagonal_coordinate,
    fockCoordinates_apply]

end ContinuumCoulomb.HubbardGlobal

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_ManyBody_HubbardFermionSpectrum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The complete half-filled Fock variational problem has the concrete block form. -/

noncomputable section
namespace ContinuumCoulomb.HubbardGlobal
open Laughlin.Fock
open scoped BigOperators InnerProductSpace

theorem euclidean_real_inner {ι : Type*} [Fintype ι] (x y : EuclideanSpace ℂ ι) :
    ⟪x, y⟫_ℝ = (⟪x, y⟫_ℂ).re := by
  simp only [PiLp.inner_apply, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro s _
  rfl

end ContinuumCoulomb.HubbardGlobal

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_ManyBody_HubbardEnergyLower
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.OccupationFock.sectorEquiv_apply _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual half-filled Hubbard variational bottom bounds every sector
vector, including unnormalized projections of continuum states. -/

noncomputable section
open scoped BigOperators InnerProductSpace Classical
namespace ContinuumCoulomb.HubbardGlobal
open Laughlin.Fock
variable {Edge : Type*} [Fintype Edge]

theorem hubbardFermionForm_occupation (m : ℕ) (U : ℝ)
    (V : Fin (m+1) → Fin (m+1) → ℝ) (left right : Edge → Fin (m+1)) (t : Edge → ℝ)
    (x : Space (2*m+1)) :
    hubbardFermionForm m U V left right t x =
      (occupationInner (2*m+1) x
        ((chargePenaltyFock m U V+graphHopping m left right (fun e => (t e:ℂ))) x)).re := by
  rw [hubbardFermionForm,euclidean_real_inner,occupationInner_fockCoordinates]

theorem hubbardFermionForm_abs_bound (m : ℕ) (U : ℝ)
    (V : Fin (m+1) → Fin (m+1) → ℝ) (left right : Edge → Fin (m+1)) (t : Edge → ℝ)
    (x : Space (2*m+1)) :
    |hubbardFermionForm m U V left right t x| ≤
      ‖fockOperator (chargePenaltyFock m U V+graphHopping m left right (fun e => (t e:ℂ)))‖*
        fockMass x := by
  let T := chargePenaltyFock m U V+graphHopping m left right (fun e => (t e:ℂ))
  have he := occupationInner_operator_error T 0 ‖fockOperator T‖ (by simp) x
  have hm := occupationNormSq_fockCoordinates x
  rw [fockCoordinates_norm_sq] at hm
  have hz : occupationInner (2*m+1) x 0 = 0 := by simp [occupationInner]
  rw [hubbardFermionForm_occupation]
  simpa only [LinearMap.zero_apply,hz,Complex.zero_re,sub_zero,hm] using he

theorem hubbardFermionBottom_lower (m : ℕ) (U : ℝ)
    (V : Fin (m+1) → Fin (m+1) → ℝ) (left right : Edge → Fin (m+1)) (t : Edge → ℝ)
    (x : Space (2*m+1)) (hx : IsHalfFilled m x) :
    hubbardFermionBottom m U V left right t*fockMass x ≤
      hubbardFermionForm m U V left right t x := by
  have hb : BddBelow {e | ∃ y : Space (2*m+1), IsHalfFilled m y ∧ 0 < fockMass y ∧
      e = hubbardFermionForm m U V left right t y/fockMass y} := by
    refine ⟨-‖fockOperator (chargePenaltyFock m U V+
      graphHopping m left right (fun e => (t e:ℂ)))‖,?_⟩
    rintro e ⟨y,_hy,hpos,rfl⟩
    apply (le_div_iff₀ hpos).mpr
    have he := (abs_le.mp (hubbardFermionForm_abs_bound m U V left right t y)).1
    linarith
  have hm : 0 ≤ fockMass x := by rw [← fockCoordinates_norm_sq]; positivity
  rcases eq_or_lt_of_le hm with hz | hpos
  · have hnorm : ‖fockCoordinates (2*m+1) x‖ = 0 := by
      have h := fockCoordinates_norm_sq x
      rw [← hz] at h
      nlinarith [norm_nonneg (fockCoordinates (2*m+1) x)]
    have hzero : x=0 := (fockCoordinates (2*m+1)).injective (by simpa using norm_eq_zero.mp hnorm)
    subst x
    simp [hubbardFermionForm,fockMass]
  · exact (le_div_iff₀ hpos).mp (csInf_le hb ⟨x,hx,hpos,rfl⟩)

end ContinuumCoulomb.HubbardGlobal

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_ManyBody_HubbardVariationalWitness
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.MediatorGraph.basisEquiv_fresh _root_.OAI.ContinuumCoulomb.MediatorGraph.basisEquiv_old _root_.OAI.ContinuumCoulomb.qmaApplyMatrix_one _root_.OAI.ContinuumCoulomb.qmaHistoryFromVector_fin _root_.OAI.ContinuumCoulomb.qmaMask_apply _root_.OAI.ContinuumCoulomb.qmaPrefixMatrix_length _root_.OAI.ContinuumCoulomb.qmaPrefixMatrix_zero _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Near-minimizers of the actual half-filled Hubbard Rayleigh quotient
are represented by antisymmetric tensors, with no restriction to spin product
states or a proper subspace of the occupation sector. -/

noncomputable section
open scoped BigOperators Classical
namespace ContinuumCoulomb.HubbardGlobal
open Laughlin.Fock
variable {Edge : Type*} [Fintype Edge]

theorem exists_halfFilled_unit_mass (m : ℕ) :
    ∃ x : Space (2*m+1), IsHalfFilled m x ∧ fockMass x=1 := by
  let s : SourceSpinBasis (m+1) := fun _ => 0
  refine ⟨spinWedge m s,isHalfFilled_of_totalNumber m _ (totalNumber_spinWedge m s),?_⟩
  rw [spinWedge_eq_fockBasis]
  simp [fockMass,Module.Basis.repr_self,Finsupp.single_apply]

end ContinuumCoulomb.HubbardGlobal

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_ManyBody_HubbardBottomBounds
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial bounds on the actual half-filled Hubbard bottom. These
control its contribution to the full-continuum complement smallness test. -/

noncomputable section
open scoped BigOperators Classical
namespace ContinuumCoulomb.HubbardGlobal
open Laughlin.Fock

theorem chargePenalty_abs_bound {m : ℕ} (U : ℝ) (V : Fin m → Fin m → ℝ)
    (o : Fin m → Fin 3) :
    |chargePenalty U V o| ≤ (m:ℝ)*|U|/2+(1/2:ℝ)*∑ i, ∑ j, |V i j| := by
  have hd (i : Fin m) : |occupationDeviation o i| ≤ 1 := by
    unfold occupationDeviation
    generalize o i = t
    fin_cases t <;> norm_num
  have hd2 (i : Fin m) : occupationDeviation o i^2 ≤ 1 := by
    nlinarith [abs_le.mp (hd i)]
  have hs : (∑ i, occupationDeviation o i^2) ≤ (m:ℝ) := by
    simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one] using
      Finset.sum_le_sum (s := Finset.univ) (fun i _ => hd2 i)
  have hnonneg : 0 ≤ ∑ i, occupationDeviation o i^2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have ht : |∑ i, ∑ j, V i j*occupationDeviation o i*occupationDeviation o j| ≤ ∑ i, ∑ j, |V i j| := by
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply Finset.sum_le_sum
    intro i _
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply Finset.sum_le_sum
    intro j _
    rw [abs_mul,abs_mul]
    calc
      _ ≤ |V i j| * 1 * 1 := by gcongr <;> apply hd
      _ = _ := by ring
  calc
    _ ≤ |U/2*(∑ i, occupationDeviation o i^2)|+
        |(1/2:ℝ)*(∑ i, ∑ j, V i j*occupationDeviation o i*occupationDeviation o j)| := abs_add_le _ _
    _ ≤ |U|/2*(m:ℝ)+(1/2:ℝ)*∑ i, ∑ j, |V i j| := by
      rw [abs_mul,abs_mul,abs_of_nonneg hnonneg,abs_div,abs_of_pos (by norm_num : (0:ℝ)<2),
        abs_of_pos (by norm_num : (0:ℝ)<1/2)]
      exact add_le_add (mul_le_mul_of_nonneg_left hs (by positivity))
        (mul_le_mul_of_nonneg_left ht (by norm_num))
    _ = _ := by ring

theorem fockOperator_diagonal_norm {Q : ℕ} (f : Finset (Fin (Q+1)) → ℂ)
    {C : ℝ} (hC : 0 ≤ C) (hf : ∀ A, ‖f A‖ ≤ C) :
    ‖fockOperator (fockDiagonal f)‖ ≤ C := by
  apply ContinuousLinearMap.opNorm_le_bound _ hC
  intro x
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hC (norm_nonneg x))).mp
  rw [mul_pow,EuclideanSpace.norm_sq_eq,EuclideanSpace.norm_sq_eq,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro A _
  rw [fockOperator_diagonal_apply,norm_mul,mul_pow]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hf A) 2) (sq_nonneg _)

theorem chargePenaltyFock_norm (m : ℕ) (U : ℝ) (V : Fin (m+1) → Fin (m+1) → ℝ) :
    ‖fockOperator (chargePenaltyFock m U V)‖ ≤
      (m+1:ℝ)*|U|/2+(1/2:ℝ)*∑ i, ∑ j, |V i j| := by
  apply fockOperator_diagonal_norm _ (by positivity)
  intro A
  simpa only [Complex.norm_real,Real.norm_eq_abs,Nat.cast_add,Nat.cast_one] using
    chargePenalty_abs_bound U V (occupationAt m A)

theorem hubbardFermionBottom_abs_bound {Edge : Type*} [Fintype Edge]
    (m : ℕ) (U : ℝ) (V : Fin (m+1) → Fin (m+1) → ℝ)
    (left right : Edge → Fin (m+1)) (t : Edge → ℝ) :
    |hubbardFermionBottom m U V left right t| ≤
      (m+1:ℝ)*|U|/2+(1/2:ℝ)*∑ i, ∑ j, |V i j|+4*∑ e, |t e| := by
  let T := chargePenaltyFock m U V+graphHopping m left right (fun e => (t e:ℂ))
  have hop : ‖fockOperator T‖ ≤
      (m+1:ℝ)*|U|/2+(1/2:ℝ)*∑ i, ∑ j, |V i j|+4*∑ e, |t e| := by
    calc
      _ ≤ ‖fockOperator (chargePenaltyFock m U V)‖+
          ‖fockOperator (graphHopping m left right (fun e => (t e:ℂ)))‖ := by
        rw [show fockOperator T = fockOperator (chargePenaltyFock m U V)+
            fockOperator (graphHopping m left right (fun e => (t e:ℂ))) from fockOperator_add _ _]
        exact norm_add_le _ _
      _ ≤ _ := add_le_add (chargePenaltyFock_norm m U V) (by
        simpa only [Complex.norm_real,Real.norm_eq_abs] using
          fockOperator_graphHopping_norm m left right (fun e => (t e:ℂ)))
  obtain ⟨x,hx,hm⟩ := exists_halfFilled_unit_mass m
  have hset : Set.Nonempty {e | ∃ y : Space (2*m+1), IsHalfFilled m y ∧ 0 < fockMass y ∧
      e = hubbardFermionForm m U V left right t y/fockMass y} :=
    ⟨_,x,hx,by rw [hm]; norm_num,rfl⟩
  have hlo : -‖fockOperator T‖ ≤ hubbardFermionBottom m U V left right t := by
    apply le_csInf hset
    rintro e ⟨y,_hy,hy,rfl⟩
    apply (le_div_iff₀ hy).mpr
    have h := (abs_le.mp (hubbardFermionForm_abs_bound m U V left right t y)).1
    linarith only [h]
  have hhi := (hubbardFermionBottom_lower m U V left right t x hx).trans
    (le_abs_self _ |>.trans (hubbardFermionForm_abs_bound m U V left right t x))
  rw [hm,mul_one,mul_one] at hhi
  exact (abs_le.mpr ⟨hlo,hhi⟩).trans hop

end ContinuumCoulomb.HubbardGlobal

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
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_PlanarOverlap
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

theorem planarOverlapConstant_nonnegative : 0 ≤ planarOverlapConstant :=
  mul_nonneg (sq_nonneg _) (integral_nonneg (fun _ => (Real.exp_pos _).le))

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

theorem localizedOverlapBound_nonnegative (D : ℝ) : 0 ≤ localizedOverlapBound D :=
  mul_nonneg planarOverlapConstant_nonnegative (Real.exp_pos _).le

end ContinuumCoulomb

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
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_LocalizedFourIndex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Four-index Coulomb integrals of the actual localized orbitals. Each
unequal-index pair gives exponentially small Coulomb coefficients, uniformly
in the other pair. Diagonal pairs recover the actual direct interaction. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

theorem localizedFourIndexConstant_nonnegative (freq : ℝ) : 0 ≤ localizedFourIndexConstant freq :=
  mul_nonneg (localizedPotentialBound_nonnegative freq) planarOverlapConstant_nonnegative

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_PlanarWellMatrix
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

theorem planarWellMatrixConstant_nonnegative : 0 ≤ planarWellMatrixConstant :=
  mul_nonneg (mul_nonneg (sq_nonneg _) (Real.exp_pos _).le)
    (integral_nonneg (fun _ => abs_nonneg _))

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

theorem positionSplitCoordinates_fst_zero (x : Position) :
    (positionSplitCoordinates x).1 0 = x 0 := rfl

theorem positionSplitCoordinates_fst_one (x : Position) :
    (positionSplitCoordinates x).1 1 = x 1 := rfl

theorem positionSplitCoordinates_snd (x : Position) :
    (positionSplitCoordinates x).2 = x 2 := rfl

theorem manufacturedWellField_support_slab (freq scale : ℝ) {S R H : ℝ}
    (hS : 0 < S) (hH : R+1 ≤ H) {m : ℕ} (u : Fin m → PlanarPosition)
    (hu : ∀ i, ‖u i‖ ≤ R) :
    tsupport (manufacturedWellField freq scale S u) ⊆ slabDomain H S := by
  apply closure_minimal _ (slabDomain_isClosed H S)
  intro x hx
  have hz : |(positionSplitCoordinates x).2| ≤ S := by
    by_contra hn
    exact hx (manufacturedWellField_outer freq scale hS u x (le_of_not_ge hn))
  have hnear : ∃ i, ‖(positionSplitCoordinates x).1-u i‖ < 1 := by
    by_contra hn
    apply hx
    unfold manufacturedWellField
    rw [countertermWellSum_zero_far freq scale u _ (fun i =>
      le_of_not_gt (fun hi => hn ⟨i, hi⟩)), mul_zero]
  obtain ⟨i, hi⟩ := hnear
  have hr : ‖(positionSplitCoordinates x).1‖ ≤ H := by
    have ht : ‖(positionSplitCoordinates x).1‖ ≤
        ‖(positionSplitCoordinates x).1-u i‖ + ‖u i‖ := by
      simpa only [sub_add_cancel] using norm_add_le ((positionSplitCoordinates x).1-u i) (u i)
    linarith [hu i]
  have h0 := (PiLp.norm_apply_le (positionSplitCoordinates x).1 0).trans hr
  have h1 := (PiLp.norm_apply_le (positionSplitCoordinates x).1 1).trans hr
  exact ⟨by simpa only [Real.norm_eq_abs, positionSplitCoordinates_fst_zero] using h0,
    by simpa only [Real.norm_eq_abs, positionSplitCoordinates_fst_one] using h1,
    by simpa only [positionSplitCoordinates_snd] using hz⟩

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Nuclei_SlabSections
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

theorem manufacturedOrbitalSquaredError_box {rho T H S freq δ D : ℝ}
    (hrho : 0 ≤ rho) (hT : 2 ≤ T)
    (hHlo : T^10 ≤ H) (hHhi : H ≤ 2*T^10)
    (hSlo : T ≤ S) (hShi : S ≤ 2*T)
    {m : ℕ} (u : Fin m → PlanarPosition) (j : Fin m) :
    manufacturedOrbitalSquaredError rho H S freq δ D T u j ≤
      3*((m:ℝ)^2*(PlanarSobolev.wellBound*planarWellMatrixConstant)*Real.exp (-(19/10:ℝ)*D)+
        64*slabResidualSeventySecondBound rho freq (u j)/T^14+
        ((m:ℝ)*δ*PlanarSobolev.wellBound)^2+
        256*((m:ℝ)*(δ+1)*PlanarSobolev.wellBound)^2*localizedDensityMoment freq (u j) 8/T^8) := by
  have hT0 : 0 < T := by linarith
  have hm := localizedDensityMoment_nonnegative freq (u j) 8
  have htail := slabSeventySecondTail_box_bound (freq := freq) hrho hT hHlo hHhi hSlo hShi (u j)
  have hw : ((m:ℝ)*(δ+1)*PlanarSobolev.wellBound)^2*
      (localizedDensityMoment freq (u j) 8/(S/2)^8) ≤
      256*((m:ℝ)*(δ+1)*PlanarSobolev.wellBound)^2*localizedDensityMoment freq (u j) 8/T^8 := by
    calc
      _ ≤ ((m:ℝ)*(δ+1)*PlanarSobolev.wellBound)^2*
          (localizedDensityMoment freq (u j) 8/(T/2)^8) := by gcongr
      _ = _ := by field_simp [ne_of_gt hT0]; ring
  unfold manufacturedOrbitalSquaredError
  linarith

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

theorem manufacturedResidual_polynomial_geometry {freq : ℝ} (hf : 0 < freq)
    {rho : ℝ} (hrho : 0 ≤ rho) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (T L H S δ D : ℝ), 2 ≤ T → 1 ≤ L →
      T^10 ≤ H → H ≤ 2*T^10 → T ≤ S → S ≤ 2*T →
      ∀ (m : ℕ) (u : Fin m → PlanarPosition), (∀ j, ‖u j‖ ≤ L) →
      (∑ j, manufacturedOrbitalSquaredError rho H S freq δ D T u j) ≤
        3*m*((m:ℝ)^2*(PlanarSobolev.wellBound*planarWellMatrixConstant)*Real.exp (-(19/10:ℝ)*D)+
          64*C*L^72/T^14+((m:ℝ)*δ*PlanarSobolev.wellBound)^2+
          256*((m:ℝ)*(δ+1)*PlanarSobolev.wellBound)^2*C*L^8/T^8) := by
  obtain ⟨C,hC,hbound⟩ := localized_slab_moments_polynomial hf rho
  refine ⟨C,hC,fun T L H S δ D hT hL hHlo hHhi hSlo hShi m u hu => ?_⟩
  have hpoint (j : Fin m) : manufacturedOrbitalSquaredError rho H S freq δ D T u j ≤
      3*((m:ℝ)^2*(PlanarSobolev.wellBound*planarWellMatrixConstant)*Real.exp (-(19/10:ℝ)*D)+
        64*C*L^72/T^14+((m:ℝ)*δ*PlanarSobolev.wellBound)^2+
        256*((m:ℝ)*(δ+1)*PlanarSobolev.wellBound)^2*C*L^8/T^8) :=
    (manufacturedOrbitalSquaredError_box hrho hT
    hHlo hHhi hSlo hShi u j).trans (show _ ≤ _ from by
      obtain ⟨hs,hm⟩ := hbound L hL (u j) (hu j)
      have hs' : 64*slabResidualSeventySecondBound rho freq (u j)/T^14 ≤
          64*C*L^72/T^14 := by
        simpa only [mul_assoc] using div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hs (by norm_num : (0:ℝ) ≤ 64))
          (show 0 ≤ T^14 by positivity)
      have hm' : 256*((m:ℝ)*(δ+1)*PlanarSobolev.wellBound)^2*
          localizedDensityMoment freq (u j) 8/T^8 ≤
          256*((m:ℝ)*(δ+1)*PlanarSobolev.wellBound)^2*C*L^8/T^8 := by
        calc
          _ ≤ 256*((m:ℝ)*(δ+1)*PlanarSobolev.wellBound)^2*(C*L^8)/T^8 := by
            gcongr
          _ = _ := by ring
      linarith only [hs',hm'])
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun j _ => hpoint j)
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hsum
  convert hsum using 1
  all_goals try with_reducible_and_instances rfl
  ring

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Programs_PolynomialResidualBudget
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
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

theorem exists_four_residual_norm_offset (A B C D : ℝ)
    (_hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C) (_hD : 0 ≤ D) :
    ∃ k₀ : ℕ, 1 ≤ k₀ ∧ ∀ s k : ℕ, k₀+s ≤ k → ∀ N : ℝ, 2 ≤ N →
      A*N^s/(N^k)^40+B*N^s/(N^k)^70+C*N^s/(N^k)^60+D*N^s/(N^k)^40 ≤
        ((N^k)^19)⁻¹^2 := by
  obtain ⟨q,hq,hconst⟩ := exists_polynomial_constant_bounds
    (show (0:ℝ)<1 by norm_num) (A+B+C+D)
  refine ⟨q+1,by omega,fun s k hk N hN => ?_⟩
  have hN0 : 0 < N := by linarith
  have hN1 : 1 ≤ N := by linarith
  have hR : 1 ≤ N^k := one_le_pow₀ hN1
  have hB' : B*N^s/(N^k)^70 ≤ B*N^s/(N^k)^40 :=
    div_le_div_of_nonneg_left (by positivity) (by positivity)
      (pow_le_pow_right₀ hR (by decide : 40 ≤ 70))
  have hC' : C*N^s/(N^k)^60 ≤ C*N^s/(N^k)^40 :=
    div_le_div_of_nonneg_left (by positivity) (by positivity)
      (pow_le_pow_right₀ hR (by decide : 40 ≤ 60))
  calc
    _ ≤ A*N^s/(N^k)^40+B*N^s/(N^k)^40+C*N^s/(N^k)^40+D*N^s/(N^k)^40 :=
      add_le_add (add_le_add (add_le_add le_rfl hB') hC') le_rfl
    _ = (A+B+C+D)*N^s/(N^k)^40 := by ring
    _ ≤ N^q*N^s/(N^k)^40 := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_right (hconst N hN).2 (by positivity)
    _ ≤ 1/(N^k)^38 := by
      rw [div_le_div_iff₀ (pow_pos (pow_pos hN0 k) _) (pow_pos (pow_pos hN0 k) _),
        one_mul,← pow_add,← pow_mul,← pow_add,← pow_mul]
      exact pow_le_pow_right₀ hN1 (by omega)
    _ = _ := by simp only [one_div,inv_pow,← pow_mul,Nat.mul_assoc]

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_OneBodyScaleBudget
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

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_ManyBody_HubbardFormScale
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial accumulation of the actual one- and two-body entry errors. -/

noncomputable section
namespace ContinuumCoulomb

theorem localizedHubbardFormError_polynomial (m : ℕ) (freq D ε z : ℝ)
    (hz : Real.exp (-(9/10:ℝ)*D) ≤ z) :
    localizedHubbardFormError m freq D ε ≤
      4*(m+1:ℝ)^2*ε+
      (512*planarOverlapConstant*localizedPotentialBound freq+8*localizedFourIndexConstant freq)*
        (m+1:ℝ)^9*z := by
  have hO := planarOverlapConstant_nonnegative
  have hP := localizedPotentialBound_nonnegative freq
  have hC := localizedFourIndexConstant_nonnegative freq
  have hm : 1 ≤ (m+1:ℝ) := by have := Nat.cast_nonneg (α := ℝ) m; linarith
  have hpow : (m+1:ℝ)^4 ≤ (m+1:ℝ)^9 := pow_le_pow_right₀ hm (by decide)
  have hc := mul_le_mul_of_nonneg_left hpow
    (show 0 ≤ 8*localizedFourIndexConstant freq by positivity)
  have he := mul_le_mul_of_nonneg_left hz
    (show 0 ≤ 512*planarOverlapConstant*localizedPotentialBound freq*(m+1:ℝ)^9+
      8*localizedFourIndexConstant freq*(m+1:ℝ)^9 by positivity)
  have hid : localizedHubbardFormError m freq D ε =
      4*(m+1:ℝ)^2*ε+
      (512*planarOverlapConstant*localizedPotentialBound freq*(m+1:ℝ)^9+
        8*localizedFourIndexConstant freq*(m+1:ℝ)^4)*Real.exp (-(9/10:ℝ)*D) := by
    unfold localizedHubbardFormError localizedOverlapBound
    ring
  rw [hid]
  refine add_le_add le_rfl ?_
  calc
    _ ≤ (512*planarOverlapConstant*localizedPotentialBound freq*(m+1:ℝ)^9+
        8*localizedFourIndexConstant freq*(m+1:ℝ)^9)*Real.exp (-(9/10:ℝ)*D) :=
      mul_le_mul_of_nonneg_right (add_le_add le_rfl hc) (Real.exp_pos _).le
    _ ≤ _ := he.trans_eq (by ring)

theorem exists_hubbardForm_parameter_offset (freq : ℝ) :
    ∃ k₀ : ℕ, 1 ≤ k₀ ∧ ∀ r p k : ℕ, k₀+9*r+p ≤ k →
      ∀ N D : ℝ, 2 ≤ N → 25*(k:ℝ)*Real.log N ≤ D →
      ∀ m : ℕ, (m+1:ℝ) ≤ N^r →
      localizedHubbardFormError m freq D ((N^(2*r+p+3))⁻¹) ≤ (N^p)⁻¹ := by
  let C := 512*planarOverlapConstant*localizedPotentialBound freq+8*localizedFourIndexConstant freq
  have hC : 0 ≤ C := add_nonneg (mul_nonneg (mul_nonneg (by norm_num)
    planarOverlapConstant_nonnegative) (localizedPotentialBound_nonnegative freq))
    (mul_nonneg (by norm_num) (localizedFourIndexConstant_nonnegative freq))
  obtain ⟨q,hq,hbound⟩ := exists_polynomial_ratio_offset C (by norm_num : (0:ℝ)<1/2)
  refine ⟨q,hq,fun r p k hk N D hN hD m hm => ?_⟩
  have hN0 : 0 < N := by linarith
  have hN1 : 1 ≤ N := by linarith
  have hR1 : 1 ≤ N^k := one_le_pow₀ hN1
  have hfirst : 4*(m+1:ℝ)^2*(N^(2*r+p+3))⁻¹ ≤ (1/2:ℝ)/N^p := by
    calc
      _ ≤ 4*(N^r)^2*(N^(2*r+p+3))⁻¹ := by gcongr
      _ = (4/N^3)/N^p := by
        rw [pow_add,pow_add,show 2*r=r*2 by omega,pow_mul]
        field_simp
      _ ≤ _ := div_le_div_of_nonneg_right
        ((div_le_iff₀ (pow_pos hN0 3)).mpr (by nlinarith [pow_le_pow_left₀ (by norm_num : (0:ℝ)≤2) hN 3]))
        (by positivity)
  have hsecond : C*(m+1:ℝ)^9*((N^k)^22)⁻¹ ≤ (1/2:ℝ)/N^p := by
    calc
      _ ≤ C*N^(9*r)/(N^k)^2 := by
        rw [inv_eq_one_div,mul_one_div]
        gcongr
        · rw [show 9*r=r*9 by omega,pow_mul]
          exact pow_le_pow_left₀ (by positivity) hm 9
        · decide
      _ ≤ _ := hbound (9*r) p k hk N hN
  have he := localizedHubbardFormError_polynomial m freq D ((N^(2*r+p+3))⁻¹)
    (((N^k)^22)⁻¹) (logarithmic_separation_overlap hN k hD)
  exact he.trans ((add_le_add hfirst hsecond).trans_eq (by rw [one_div]; ring))

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_ManyBody_HubbardTolerance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Combining the two entrywise approximation budgets in the finite form. -/

noncomputable section
namespace ContinuumCoulomb

theorem localizedHubbardFormError_mono (m : ℕ) (freq D : ℝ) {ε ε' : ℝ}
    (h : ε ≤ ε') :
    localizedHubbardFormError m freq D ε ≤ localizedHubbardFormError m freq D ε' := by
  unfold localizedHubbardFormError
  exact add_le_add (mul_le_mul_of_nonneg_left h (sq_nonneg _)) le_rfl

theorem double_inverse_power_le {N : ℝ} (hN : 2 ≤ N) (j : ℕ) :
    (N^(j+1))⁻¹+(N^(j+1))⁻¹ ≤ (N^j)⁻¹ := by
  have hN0 : 0 < N := by linarith
  rw [pow_succ]
  have hh : 2/(N^j*N) ≤ 1/N^j :=
    (div_le_div_iff₀ (by positivity) (by positivity)).mpr (by nlinarith [pow_pos hN0 j])
  simpa only [div_eq_mul_inv,one_mul,two_mul] using hh

theorem exists_hubbardDouble_parameter_offset (freq : ℝ) :
    ∃ q : ℕ, 1 ≤ q ∧ ∀ r p k : ℕ, q+9*r+p ≤ k →
      ∀ N D : ℝ, 2 ≤ N → 25*(k:ℝ)*Real.log N ≤ D →
      ∀ m : ℕ, (m+1:ℝ) ≤ N^r →
      localizedHubbardFormError m freq D
        ((N^(2*r+p+6))⁻¹+(N^(2*r+p+6))⁻¹) ≤ (N^(p+2))⁻¹ := by
  obtain ⟨q,hq,hbound⟩ := exists_hubbardForm_parameter_offset freq
  refine ⟨q+2,by omega,fun r p k hk N D hN hD m hm => ?_⟩
  apply (localizedHubbardFormError_mono m freq D ?_).trans
    (hbound r (p+2) k (by omega) N D hN hD m hm)
  convert double_inverse_power_le hN (2*r+p+5) using 1
  all_goals try with_reducible_and_instances rfl

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_ManufacturedFrequency
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The frequency evaluated by the literal programs satisfies exactly the
oscillator/slab relation and lies in the uniform spectral-gap regime. -/

noncomputable section
namespace ContinuumCoulomb

theorem manufactured_frequency_relation (rho : ℕ) :
    (GaussianFrequency.frequency rho)^2 = 4*Real.pi*(rho:ℝ) := by
  unfold GaussianFrequency.frequency
  exact Real.sq_sqrt (by positivity)

theorem manufactured_frequency_ge_one {rho : ℕ} (hrho : 0 < rho) :
    1 ≤ GaussianFrequency.frequency rho := by
  have hr : (1:ℝ) ≤ rho := by exact_mod_cast Nat.succ_le_iff.mpr hrho
  have hp : (1:ℝ) ≤ 4*Real.pi := by linarith [Real.pi_gt_three]
  unfold GaussianFrequency.frequency
  apply Real.le_sqrt_of_sq_le
  simpa only [one_mul,one_pow] using mul_le_mul hp hr (by norm_num : (0:ℝ) ≤ 1) (by positivity : 0 ≤ 4*Real.pi)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_ManufacturedResidualMajorant
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A four-term majorant for the actual manufactured differential residual.
The denominator powers are the ones used by the fixed physical schedule. -/

noncomputable section
open scoped BigOperators
namespace ContinuumCoulomb

theorem manufacturedResidual_four_power_majorant {freq : ℝ} (hf : 0 < freq)
    {rho : ℝ} (hrho : 0 ≤ rho) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ R L H S D a d δ M : ℝ,
      2 ≤ R → 1 ≤ L → R^50 ≤ H → H ≤ 2*R^50 → R^5 ≤ S → S ≤ 2*R^5 →
      0 < a → 0 ≤ d → 0 ≤ δ → δ ≤ 1 → δ ≤ d*M/(a*R^30) →
      Real.exp (-(19/10:ℝ)*D) ≤ (R^40)⁻¹ →
      ∀ (m : ℕ) (u : Fin m → PlanarPosition), (m:ℝ) ≤ M → (∀ j, ‖u j‖ ≤ L) →
      4*(m:ℝ)^2*(∑ j, manufacturedOrbitalSquaredError rho H S freq δ D (R^5) u j) ≤
        12*(PlanarSobolev.wellBound*planarWellMatrixConstant)*M^5/R^40+
        768*C*M^3*L^72/R^70+
        (12*PlanarSobolev.wellBound^2*d^2/a^2)*M^7/R^60+
        12288*PlanarSobolev.wellBound^2*C*M^5*L^8/R^40 := by
  obtain ⟨C,hC,hbound⟩ := manufacturedResidual_polynomial_geometry hf hrho
  refine ⟨C,hC,fun R L H S D a d δ M hR hL hHlo hHhi hSlo hShi ha hd hδ hδ1 hδa he m u hm hu => ?_⟩
  have hR0 : 0 < R := by linarith
  have hM : 0 ≤ M := (Nat.cast_nonneg m).trans hm
  have hW := PlanarSobolev.wellBound_nonnegative
  have hP := planarWellMatrixConstant_nonnegative
  have hr5 : 2 ≤ R^5 := hR.trans (le_self_pow₀ (by linarith) (by decide))
  have hb := hbound (R^5) L H S δ D hr5 hL
    (by simpa only [← pow_mul] using hHlo) (by simpa only [← pow_mul] using hHhi)
    hSlo hShi m u hu
  have h1 : (m:ℝ)^2*(PlanarSobolev.wellBound*planarWellMatrixConstant)*
      Real.exp (-(19/10:ℝ)*D) ≤ M^2*(PlanarSobolev.wellBound*planarWellMatrixConstant)/R^40 := by
    calc
      _ ≤ M^2*(PlanarSobolev.wellBound*planarWellMatrixConstant)*(R^40)⁻¹ := by gcongr
      _ = _ := by rw [div_eq_mul_inv]
  have h3 : ((m:ℝ)*δ*PlanarSobolev.wellBound)^2 ≤
      (M*(d*M/(a*R^30))*PlanarSobolev.wellBound)^2 := by gcongr
  have h4 : 256*((m:ℝ)*(δ+1)*PlanarSobolev.wellBound)^2*C*L^8/(R^5)^8 ≤
      1024*M^2*PlanarSobolev.wellBound^2*C*L^8/R^40 := by
    calc
      _ ≤ 256*(M*2*PlanarSobolev.wellBound)^2*C*L^8/(R^5)^8 := by gcongr; linarith
      _ = _ := by rw [← pow_mul]; ring
  have h2 : 64*C*L^72/(R^5)^14 = 64*C*L^72/R^70 := by rw [← pow_mul]
  have hp := add_le_add (add_le_add (add_le_add h1 (le_of_eq h2)) h3) h4
  have hscaled := mul_le_mul_of_nonneg_left hb (show 0 ≤ 4*(m:ℝ)^2 by positivity)
  calc
    _ ≤ 12*(m:ℝ)^3*((m:ℝ)^2*(PlanarSobolev.wellBound*planarWellMatrixConstant)*
        Real.exp (-(19/10:ℝ)*D)+64*C*L^72/(R^5)^14+
        ((m:ℝ)*δ*PlanarSobolev.wellBound)^2+
        256*((m:ℝ)*(δ+1)*PlanarSobolev.wellBound)^2*C*L^8/(R^5)^8) := by
      convert hscaled using 1
      all_goals try with_reducible_and_instances rfl
      ring
    _ ≤ 12*M^3*(M^2*(PlanarSobolev.wellBound*planarWellMatrixConstant)/R^40+
        64*C*L^72/R^70+(M*(d*M/(a*R^30))*PlanarSobolev.wellBound)^2+
        1024*M^2*PlanarSobolev.wellBound^2*C*L^8/R^40) := by
      exact mul_le_mul (by gcongr) hp (by positivity) (by positivity)
    _ = _ := by
      field_simp [ne_of_gt ha,ne_of_gt hR0]
      ring

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_ManufacturedResidualParameters
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fixed polynomial exponents control the actual differential residual
uniformly in the source size, the site count and the coordinate extent. -/

noncomputable section
open scoped BigOperators
namespace ContinuumCoulomb

theorem exists_manufactured_residual_parameter_offset {freq rho a d : ℝ}
    (hf : 0 < freq) (hrho : 0 ≤ rho) (ha : 0 < a) (hd : 0 ≤ d) :
    ∃ k₀ : ℕ, 1 ≤ k₀ ∧ ∀ r s k : ℕ, k₀+7*r+72*s ≤ k → ∀ N : ℝ, 2 ≤ N →
      ∀ H S D δ : ℝ, (N^k)^50 ≤ H → H ≤ 2*(N^k)^50 →
        (N^k)^5 ≤ S → S ≤ 2*(N^k)^5 →
        25*(k:ℝ)*Real.log N ≤ D → 0 ≤ δ → δ ≤ d*N^r/(a*(N^k)^30) →
        ∀ (m : ℕ) (u : Fin m → PlanarPosition), (m:ℝ) ≤ N^r → (∀ j, ‖u j‖ ≤ N^s) →
        δ ≤ 1 ∧ 4*(m:ℝ)^2*(∑ j,
          manufacturedOrbitalSquaredError rho H S freq δ D ((N^k)^5) u j) ≤
          ((N^k)^19)⁻¹^2 := by
  obtain ⟨C,hC,hmajor⟩ := manufacturedResidual_four_power_majorant hf hrho
  let A := 12*(PlanarSobolev.wellBound*planarWellMatrixConstant)
  let B := 768*C
  let V := 12*PlanarSobolev.wellBound^2*d^2/a^2
  let W := 12288*PlanarSobolev.wellBound^2*C
  have hwell := PlanarSobolev.wellBound_nonnegative
  have hplanar := planarWellMatrixConstant_nonnegative
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hV : 0 ≤ V := by dsimp [V]; positivity
  have hW : 0 ≤ W := by dsimp [W]; positivity
  obtain ⟨k₁,hk₁,hsmall⟩ := exists_four_residual_norm_offset A B V W hA hB hV hW
  obtain ⟨q,_hq,hcoef⟩ := exists_polynomial_constant_bounds
    (show (0:ℝ)<1 by norm_num) (d/a)
  refine ⟨k₁+q+2,by omega,?_⟩
  intro r s k hk N hN H S D δ hHlo hHhi hSlo hShi hD hδ hδa m u hm hu
  let E := 7*r+72*s
  have hN0 : 0 < N := by linarith
  have hN1 : 1 ≤ N := by linarith
  have hk1 : 1 ≤ k := by omega
  have hR : 2 ≤ N^k := hN.trans (le_self_pow₀ hN1 (by omega))
  have hδ1 : δ ≤ 1 := by
    calc
      δ ≤ (d/a)*N^r/N^(k*30) := by
        convert hδa using 1
        all_goals try with_reducible_and_instances rfl
        rw [pow_mul]
        ring
      _ ≤ N^q*N^r/N^(k*30) := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        exact mul_le_mul_of_nonneg_right (hcoef N hN).2 (by positivity)
      _ ≤ 1 := by
        rw [div_le_one (pow_pos hN0 _),← pow_add]
        exact pow_le_pow_right₀ hN1 (by omega)
  refine ⟨hδ1,?_⟩
  have hmaj := hmajor (N^k) (N^s) H S D a d δ (N^r) hR (one_le_pow₀ hN1)
    hHlo hHhi hSlo hShi ha hd hδ hδ1 hδa (logarithmic_separation_residual hN k hD) m u hm hu
  change _ ≤ A*(N^r)^5/(N^k)^40+B*(N^r)^3*(N^s)^72/(N^k)^70+
    V*(N^r)^7/(N^k)^60+W*(N^r)^5*(N^s)^8/(N^k)^40 at hmaj
  have hp5 : (N^r)^5 ≤ N^E := by
    rw [← pow_mul]
    exact pow_le_pow_right₀ hN1 (by dsimp [E]; omega)
  have hp3 : (N^r)^3*(N^s)^72 ≤ N^E := by
    rw [← pow_mul,← pow_mul,← pow_add]
    exact pow_le_pow_right₀ hN1 (by dsimp [E]; omega)
  have hp7 : (N^r)^7 ≤ N^E := by
    rw [← pow_mul]
    exact pow_le_pow_right₀ hN1 (by dsimp [E]; omega)
  have hp58 : (N^r)^5*(N^s)^8 ≤ N^E := by
    rw [← pow_mul,← pow_mul,← pow_add]
    exact pow_le_pow_right₀ hN1 (by dsimp [E]; omega)
  have ht1 : A*(N^r)^5/(N^k)^40 ≤ A*N^E/(N^k)^40 := by gcongr
  have ht2 : B*(N^r)^3*(N^s)^72/(N^k)^70 ≤ B*N^E/(N^k)^70 := by
    rw [mul_assoc]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hp3 hB) (by positivity)
  have ht3 : V*(N^r)^7/(N^k)^60 ≤ V*N^E/(N^k)^60 := by gcongr
  have ht4 : W*(N^r)^5*(N^s)^8/(N^k)^40 ≤ W*N^E/(N^k)^40 := by
    rw [mul_assoc]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hp58 hW) (by positivity)
  exact hmaj.trans ((add_le_add (add_le_add (add_le_add ht1 ht2) ht3) ht4).trans
    (hsmall E k (by dsimp [E]; omega) N hN))

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Reduction_ActualResidualParameters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The counterterm size in the residual theorem is computed from the
actual orbital Coulomb sums; no independent coefficient bound is assumed. -/

noncomputable section
open scoped BigOperators
namespace ContinuumCoulomb

theorem actual_counterterm_scale_bound {freq N a : ℝ} (hf : 0 < freq)
    (hN : 0 < N) (ha : 0 < a) (r k : ℕ) {m : ℕ}
    (u : Fin m → PlanarPosition) (hm : (m:ℝ) ≤ N^r) (i : Fin m) :
    0 ≤ localizedCounterterm freq u i/(a*(N^k)^30) ∧
      localizedCounterterm freq u i/(a*(N^k)^30) ≤
        localizedCountertermBound freq*N^r/(a*(N^k)^30) := by
  refine ⟨div_nonneg (localizedCounterterm_nonnegative freq u i) (by positivity),?_⟩
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact (localizedCounterterm_bound hf u i).trans (by
    simpa only [mul_comm] using mul_le_mul_of_nonneg_right hm (localizedCountertermBound_nonnegative freq))

theorem exists_actual_manufactured_residual_parameters {freq rho a : ℝ}
    (hf : 0 < freq) (hrho : 0 ≤ rho) (ha : 0 < a) :
    ∃ k₀ : ℕ, 1 ≤ k₀ ∧ ∀ r s k : ℕ, k₀+7*r+72*s ≤ k → ∀ N : ℝ, 2 ≤ N →
      ∀ H S D : ℝ, (N^k)^50 ≤ H → H ≤ 2*(N^k)^50 →
        (N^k)^5 ≤ S → S ≤ 2*(N^k)^5 → 25*(k:ℝ)*Real.log N ≤ D →
      ∀ (m : ℕ) (u : Fin m → PlanarPosition), (m:ℝ) ≤ N^r → (∀ j, ‖u j‖ ≤ N^s) →
        let η := localizedCountertermBound freq*N^r/(a*(N^k)^30)
        (∀ i, 0 ≤ localizedCounterterm freq u i/(a*(N^k)^30) ∧
          localizedCounterterm freq u i/(a*(N^k)^30) ≤ η) ∧
        0 ≤ η ∧ η ≤ 1 ∧ 4*(m:ℝ)^2*(∑ j,
          manufacturedOrbitalSquaredError rho H S freq η D ((N^k)^5) u j) ≤
          ((N^k)^19)⁻¹^2 := by
  obtain ⟨k₀,hk₀,hbound⟩ := exists_manufactured_residual_parameter_offset hf hrho ha
    (localizedCountertermBound_nonnegative freq)
  refine ⟨k₀,hk₀,?_⟩
  intro r s k hk N hN H S D hHlo hHhi hSlo hShi hD m u hm hu
  have hN0 : 0 < N := by linarith
  dsimp only
  have hη : 0 ≤ localizedCountertermBound freq*N^r/(a*(N^k)^30) :=
    div_nonneg (mul_nonneg (localizedCountertermBound_nonnegative freq) (by positivity)) (by positivity)
  have hb := hbound r s k hk N hN H S D _ hHlo hHhi hSlo hShi hD hη le_rfl m u hm hu
  exact ⟨actual_counterterm_scale_bound hf hN0 ha r k u hm,hη,hb⟩

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_ManufacturedGridParameters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! One actual nuclear cloud simultaneously satisfies the full-domain form,
finite matrix, and differential-residual estimates at fixed polynomial scales. -/

noncomputable section
open MeasureTheory
open scoped NNReal
namespace ContinuumCoulomb

theorem manufactured_grid_parameters (hp : PublishedC4FlowInput) :
    ∃ rho : ℕ, 0 < rho ∧ ∃ L K : ℝ≥0, 0 < L ∧ 0 < K ∧ ∃ B : ℝ, 1 ≤ B ∧
    ∀ freq : ℝ, 0 < freq → ∃ q : ℕ, 1 ≤ q ∧
    ∀ r s p k : ℕ, q+7*r+72*s+p ≤ k →
    ∀ N H S D : ℝ, 2 ≤ N →
      (N^k)^50 ≤ H → H ≤ 2*(N^k)^50 →
      (N^k)^5 ≤ S → S ≤ 2*(N^k)^5 → 25*(k:ℝ)*Real.log N ≤ D →
    ∀ (m : ℕ) (u : Fin m → PlanarPosition), (m:ℝ) ≤ N^r →
      (∀ i, ‖u i‖ ≤ N^s) → (∀ i j, i ≠ j → D ≤ ‖u i-u j‖) →
    ∀ {ι : Type} [Fintype ι] (index : ι → Fin 3 → ℤ), Function.Injective index →
      (⋃ i, positionCube (gaussCellCenter (1/(N^k)^10) (index i)) (1/(N^k)^10)) = slabDomain H S →
    let scale := (8/(rho:ℝ))*(N^k)^30
    let η := localizedCountertermBound freq*N^r/scale
    (∀ i, 0 ≤ localizedCounterterm freq u i/scale ∧ localizedCounterterm freq u i/scale ≤ η) ∧
    0 ≤ η ∧ η ≤ 1 ∧
    4*(m:ℝ)^2*(∑ j, manufacturedOrbitalSquaredError rho H S freq η D ((N^k)^5) u j) ≤
      ((N^k)^19)⁻¹^2 ∧
    ∃ G : Position → ℝ → Position,
      IsUnitTimeFlow (moserVelocity rho (manufacturedWellField freq scale S u)) G ∧
      Function.Bijective (fun x => G x 1) ∧
      LipschitzWith L (fun x => G x 1) ∧ AntilipschitzWith K (fun x => G x 1) ∧
      (∀ x, x ∉ tsupport (manufacturedWellField freq scale S u) → G x 1 = x) ∧
      (∀ x, |manufacturedCharge (manufacturedWellField freq scale S u) x| ≤ (rho:ℝ)/2) ∧
      ContDiff ℝ 4 (fun x => G x 1) ∧
      (∀ k : ℕ, 1 ≤ k → k ≤ 4 → ∀ x, ‖iteratedFDeriv ℝ k (fun y => G y 1) x‖ ≤ L) ∧
      let F : Position → ℝ := fun y => gridNuclearPotential index (fun x => G x 1) rho (1/(N^k)^10) y-
        (slabPotential rho H S y+manufacturedWellField freq scale S u y)
      (∀ (n : ℕ) (w : Coulomb.H1Vector n) (t : SpinConfiguration n) (i : Fin n),
        Integrable (fun x => |F (Coulomb.position x i)| * ‖w.value t x‖^2) ∧
        (∫ x, |F (Coulomb.position x i)| * ‖w.value t x‖^2) ≤
          (B/(N^k)^20)*((∫ x, ‖w.value t x‖^2)+∑ j : Fin 3, ∫ x, ‖w.gradient t (i,j) x‖^2)) ∧
      (∀ i j, Integrable (fun x => F x*continuumLocalizedMode freq (u i) x*continuumLocalizedMode freq (u j) x)) ∧
      (∀ i j, |scale*correctedNuclearOneBodyMatrix rho H S freq scale u F i j-
        localizedOneBodyTarget scale freq u i j| ≤ (N^p)⁻¹) := by
  obtain ⟨rho,hrho,L,K,hL,hK,B,hB,hfamily⟩ := manufactured_grid_witness hp
  refine ⟨rho,hrho,L,K,hL,hK,B,hB,?_⟩
  intro freq hf
  obtain ⟨E,hE,hgrid⟩ := hfamily freq hf
  have hrhoR : (0:ℝ) < rho := by exact_mod_cast hrho
  have ha : (0:ℝ) < 8/(rho:ℝ) := by positivity
  obtain ⟨qR,hqR,hres⟩ := exists_actual_manufactured_residual_parameters hf hrhoR.le ha
  obtain ⟨qM,hqM,hmat⟩ := exists_actual_oneBody_parameters hrhoR.le hf ha (zero_le_one.trans hE)
  obtain ⟨qD,hqD,hsepD⟩ := exists_logarithmic_scale_threshold 3
  refine ⟨qR+qM+qD+1,by omega,?_⟩
  intro r s p k hk N H S D hN hHlo hHhi hSlo hShi hD m u hm hu hsep ι _ index hi hcover
  dsimp only
  have hN0 : 0 < N := by linarith
  have hN1 : 1 ≤ N := by linarith
  have hR : 2 ≤ N^k := hN.trans (le_self_pow₀ hN1 (by omega))
  have hR0 : 0 < N^k := by positivity
  have hS : 0 < S := (pow_pos hR0 5).trans_le hSlo
  have hH : 0 ≤ H := (pow_nonneg hR0.le 50).trans hHlo
  have hscale : 0 < (8/(rho:ℝ))*(N^k)^30 := by positivity
  obtain ⟨hcoeff,hη,hη1,herr⟩ := hres r s k (by omega) N hN H S D
    hHlo hHhi hSlo hShi hD m u hm hu
  refine ⟨hcoeff,hη,hη1,herr,?_⟩
  have hmR : (m:ℝ) ≤ (N^k)^14 := hm.trans (by
    rw [← pow_mul]
    exact pow_le_pow_right₀ hN1 (by omega))
  have h3 : 3 ≤ D := (hsepD k (by omega) N hN).trans hD
  have hcounter (i : Fin m) : localizedCounterterm freq u i ≤ (8/(rho:ℝ))*(N^k)^30 :=
    (div_le_one hscale).mp ((hcoeff i).2.trans hη1)
  have hbox : N^s+1 ≤ H := by
    calc
      _ ≤ 2*N^s := by linarith [one_le_pow₀ hN1 (n := s)]
      _ ≤ N^(s+1) := by rw [pow_succ]; nlinarith [mul_le_mul_of_nonneg_right hN (pow_nonneg hN0.le s)]
      _ ≤ (N^k)^50 := by rw [← pow_mul]; exact pow_le_pow_right₀ hN1 (by omega)
      _ ≤ H := hHlo
  have hsupp := manufacturedWellField_support_slab freq ((8/(rho:ℝ))*(N^k)^30) hS hbox u hu
  obtain ⟨G,hflow,hbij,hLip,hAnti,hfix,hcharge,hreg,hjets,hfull,hentries⟩ :=
    hgrid (N^k) ((8/(rho:ℝ))*(N^k)^30) S H hR hscale hSlo hShi hH m u hmR
      (fun i j hij => h3.trans (hsep i j hij)) hcounter hsupp index hi hcover
  refine ⟨G,hflow,hbij,hLip,hAnti,hfix,hcharge,hreg,hjets,hfull,?_,?_⟩
  · exact fun i j => (hentries (u i) (u j)).1
  · exact hmat r s p k (by omega) N H S D hN hHlo hHhi hSlo hShi hD m u hm hu hsep _
      (fun i j => (hentries (u i) (u j)).1) (fun i j => (hentries (u i) (u j)).2)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_ShiftedHubbardBounds
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual finite Hubbard energy, including its off-site shift and
form error, has polynomial size. No occupation-space dimension enters. -/

noncomputable section
open scoped BigOperators
namespace ContinuumCoulomb
open HubbardGlobal

theorem localizedOffsiteCoulomb_nonnegative {m : ℕ} (freq : ℝ)
    (u : Fin m → PlanarPosition) (i j : Fin m) : 0 ≤ localizedOffsiteCoulomb freq u i j := by
  unfold localizedOffsiteCoulomb
  split_ifs
  · exact le_rfl
  · exact localizedCoulombCoeff_nonnegative _ _ _

theorem localizedOffsiteCoulomb_le {m : ℕ} {freq : ℝ} (hf : 0 < freq)
    (u : Fin m → PlanarPosition) (i j : Fin m) :
    localizedOffsiteCoulomb freq u i j ≤ localizedPotentialBound freq := by
  unfold localizedOffsiteCoulomb
  split_ifs
  · exact localizedPotentialBound_nonnegative _
  · exact localizedCoulombCoeff_le hf _ _

theorem localizedOffsiteCoulomb_sum_le {m : ℕ} {freq : ℝ} (hf : 0 < freq)
    (u : Fin m → PlanarPosition) :
    (∑ i, ∑ j, localizedOffsiteCoulomb freq u i j) ≤ (m:ℝ)^2*localizedPotentialBound freq := by
  have h := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
    Finset.sum_le_sum (s := Finset.univ) (fun j _ => localizedOffsiteCoulomb_le hf u i j))
  simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,pow_two,mul_assoc] using h

theorem localizedHubbardFormError_nonnegative (m : ℕ) (freq D : ℝ) {ε : ℝ} (hε : 0 ≤ ε) :
    0 ≤ localizedHubbardFormError m freq D ε := by
  have hO := localizedOverlapBound_nonnegative D
  have hP := localizedPotentialBound_nonnegative freq
  have hC := localizedFourIndexConstant_nonnegative freq
  unfold localizedHubbardFormError
  positivity

theorem shifted_hubbard_abs_bound {Edge : Type*} [Fintype Edge]
    {freq D ε : ℝ} (hf : 0 < freq) (hε : 0 ≤ ε) (m : ℕ)
    (u : Fin (m+1) → PlanarPosition) (left right : Edge → Fin (m+1)) (t : Edge → ℝ)
    (he : localizedHubbardFormError m freq D ε ≤ 1) :
    |hubbardFermionBottom m (localizedCoulombProfile freq 0) (localizedOffsiteCoulomb freq u) left right t-
      (1/2:ℝ)*(∑ i, ∑ j, localizedOffsiteCoulomb freq u i j)-localizedHubbardFormError m freq D ε| ≤
      ((m+1:ℝ)/2+(m+1:ℝ)^2)*localizedPotentialBound freq+4*(∑ e, |t e|)+1 := by
  have hP := localizedPotentialBound_nonnegative freq
  have hU0 := localizedCoulombProfile_nonnegative freq 0
  have hU : localizedCoulombProfile freq 0 ≤ localizedPotentialBound freq := by
    simpa only [localizedCoulombCoeff_distance,sub_self,norm_zero] using
      localizedCoulombCoeff_le hf (0 : PlanarPosition) 0
  have hsum0 : 0 ≤ ∑ i, ∑ j, localizedOffsiteCoulomb freq u i j :=
    Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => localizedOffsiteCoulomb_nonnegative freq u i j))
  have hsum := localizedOffsiteCoulomb_sum_le hf u
  have he0 := localizedHubbardFormError_nonnegative m freq D hε
  have hh := hubbardFermionBottom_abs_bound m (localizedCoulombProfile freq 0)
    (localizedOffsiteCoulomb freq u) left right t
  simp_rw [abs_of_nonneg hU0,abs_of_nonneg (localizedOffsiteCoulomb_nonnegative freq u _ _)] at hh
  have hu := mul_le_mul_of_nonneg_left hU (show 0 ≤ (m+1:ℝ)/2 by positivity)
  have ht := (abs_sub
    (hubbardFermionBottom m (localizedCoulombProfile freq 0) (localizedOffsiteCoulomb freq u) left right t-
      (1/2:ℝ)*(∑ i, ∑ j, localizedOffsiteCoulomb freq u i j)) (localizedHubbardFormError m freq D ε)).trans
    (add_le_add (abs_sub _ _) (le_refl |localizedHubbardFormError m freq D ε|))
  rw [abs_of_nonneg he0,abs_of_nonneg (mul_nonneg (by norm_num) hsum0)] at ht
  simp only [Nat.cast_add,Nat.cast_one] at hsum
  nlinarith only [ht,hh,hu,hsum,he]

theorem exists_shifted_hubbard_polynomial_bound {freq : ℝ} (hf : 0 < freq) :
    ∃ q : ℕ, 1 ≤ q ∧ ∀ (r v : ℕ) (N : ℝ), 2 ≤ N →
    ∀ {Edge : Type} [Fintype Edge] (m : ℕ) (u : Fin (m+1) → PlanarPosition)
      (left right : Edge → Fin (m+1)) (t : Edge → ℝ) (D ε : ℝ),
      (m+1:ℝ) ≤ N^r → (∑ e, |t e|) ≤ N^v → 0 ≤ ε →
      localizedHubbardFormError m freq D ε ≤ 1 →
      |hubbardFermionBottom m (localizedCoulombProfile freq 0) (localizedOffsiteCoulomb freq u) left right t-
        (1/2:ℝ)*(∑ i, ∑ j, localizedOffsiteCoulomb freq u i j)-localizedHubbardFormError m freq D ε| ≤
        N^(q+2*r+v) := by
  let C := (3/2:ℝ)*localizedPotentialBound freq+5
  have hP := localizedPotentialBound_nonnegative freq
  obtain ⟨q,hq,hbound⟩ := exists_polynomial_constant_bounds (by norm_num : (0:ℝ)<1) C
  refine ⟨q,by omega,fun r v N hN Edge _ m u left right t D ε hm ht hε he => ?_⟩
  have hN1 : 1 ≤ N := by linarith
  have hM : 1 ≤ (m+1:ℝ) := by have := Nat.cast_nonneg (α := ℝ) m; linarith
  have hM2 : (m+1:ℝ) ≤ (m+1:ℝ)^2 := by nlinarith [sq_nonneg ((m+1:ℝ)-1)]
  have hpow : (m+1:ℝ)^2 ≤ N^(2*r+v) := by
    calc
      _ ≤ (N^r)^2 := pow_le_pow_left₀ (by positivity) hm 2
      _ ≤ N^(2*r+v) := by
        rw [← pow_mul]
        exact pow_le_pow_right₀ hN1 (by omega)
  have hfirst : ((m+1:ℝ)/2+(m+1:ℝ)^2)*localizedPotentialBound freq ≤
      ((3/2:ℝ)*localizedPotentialBound freq)*N^(2*r+v) := by
    calc
      _ ≤ ((3/2:ℝ)*(m+1:ℝ)^2)*localizedPotentialBound freq :=
        mul_le_mul_of_nonneg_right (by linarith only [hM2]) hP
      _ ≤ ((3/2:ℝ)*localizedPotentialBound freq)*N^(2*r+v) := by
        have h := mul_le_mul_of_nonneg_left hpow (show 0 ≤ (3/2:ℝ)*localizedPotentialBound freq by positivity)
        convert h using 1
        all_goals try with_reducible_and_instances rfl
        ring
  have ht' : (∑ e, |t e|) ≤ N^(2*r+v) := ht.trans (pow_le_pow_right₀ hN1 (by omega))
  have hone : 1 ≤ N^(2*r+v) := one_le_pow₀ hN1
  calc
    _ ≤ ((m+1:ℝ)/2+(m+1:ℝ)^2)*localizedPotentialBound freq+4*(∑ e, |t e|)+1 :=
      shifted_hubbard_abs_bound hf hε m u left right t he
    _ ≤ C*N^(2*r+v) := by dsimp [C]; nlinarith only [hfirst,ht',hone]
    _ ≤ N^q*N^(2*r+v) := mul_le_mul_of_nonneg_right (hbound N hN).2 (by positivity)
    _ = N^(q+2*r+v) := by rw [← pow_add]; congr 1; omega

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_ManufacturedScalarParameters
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A single polynomial exponent closes the numerical hypotheses of the
full-domain manufactured-grid comparison. -/

noncomputable section
open scoped BigOperators
namespace ContinuumCoulomb
open HubbardGlobal

theorem manufactured_scalar_parameters {freq rho a γ δ B : ℝ}
    (hf : 1 ≤ freq) (hrho : 0 ≤ rho) (ha : 0 < a)
    (hγ : 0 < γ) (hγ1 : γ ≤ 1/4) (hδ : 0 < δ) (hB : 0 ≤ B) :
    ∃ q qG : ℕ, 1 ≤ q ∧ 1 ≤ qG ∧
    ∀ r v p k : ℕ, q+9*r+v+p ≤ k → ∀ N D : ℝ,
      2 ≤ N → 25*(k:ℝ)*Real.log N ≤ D →
    ∀ {Edge : Type} [Fintype Edge] (m : ℕ) (u : Fin (m+1) → PlanarPosition)
      (left right : Edge → Fin (m+1)) (t : Edge → ℝ),
      (m+1:ℝ) ≤ N^r → (∑ e, |t e|) ≤ N^v →
    let scale := a*(N^k)^30
    let η := localizedCountertermBound freq*N^r/scale
    let ε := ((N^k)^19)⁻¹
    let tol := (N^(2*r+p+6))⁻¹
    let Eform := localizedHubbardFormError m freq D (tol+tol)
    let A := hubbardFermionBottom m (localizedCoulombProfile freq 0)
      (localizedOffsiteCoulomb freq u) left right t-
      (1/2:ℝ)*(∑ i, ∑ j, localizedOffsiteCoulomb freq u i j)-Eform
    let K := (m+1:ℝ)*(((m+1:ℝ)+η)*PlanarSobolev.wellBound+6*Real.pi*rho+
      ((-1/2:ℝ)+freq/2))+2*(m+1:ℝ)*ε
    let g₀ := (γ/8)/(2*((m+1:ℝ)*(((m+1:ℝ)+η)*PlanarSobolev.wellBound+
      6*Real.pi*rho+((-1/2:ℝ)+freq/2))+γ/8+1))
    let g := (N^(qG+2*r))⁻¹
    0 ≤ η ∧ η ≤ 1 ∧ η ≤ δ ∧
    (m+1:ℝ)*(ε+ε^2/(γ/4)) ≤ γ/8 ∧
    Eform ≤ (N^(p+2))⁻¹ ∧ 0 < g ∧
    (B/(N^k)^20)*(m+1:ℝ)+|A/scale|+g ≤ g₀ ∧
    scale*(3*((2*(m+1:ℝ)*ε)^2+scale⁻¹^2*(8*(m+1:ℝ)^3*K)+
      (B/(N^k)^20)^2*((m+1:ℝ)+2*K)*(m+1:ℝ))/g) ≤ (N^(p+2))⁻¹ := by
  have hfp : 0 < freq := lt_of_lt_of_le zero_lt_one hf
  let C := manufacturedKineticBudgetConstant freq rho
  let b := γ/(16*C)
  have hC : 0 < C := manufacturedKineticBudgetConstant_positive hf hrho
  have hb : 0 < b := by dsimp [b]; positivity
  obtain ⟨qη,hqη,heta⟩ := exists_polynomial_ratio_offset
    (localizedCountertermBound freq/a) (lt_min hδ zero_lt_one)
  obtain ⟨qR,hqR,hres⟩ := exists_residual_complement_smallness hγ
  obtain ⟨qF,hqF,hform⟩ := exists_hubbardDouble_parameter_offset freq
  obtain ⟨qG,hqG,hkin⟩ := exists_manufactured_kinetic_exponent hf hrho hγ hγ1
  obtain ⟨qA,hqA,habs⟩ := exists_shifted_hubbard_polynomial_bound hfp
  obtain ⟨qB,hqB,hsmall⟩ := exists_nuclear_complement_smallness ha hb hB
  obtain ⟨qI,hqI,herr⟩ := exists_complement_error_scale (b := B) ha
  refine ⟨qη+qR+qF+qB+qA+qI+2*qG+3,qG,by omega,hqG,?_⟩
  intro r v p k hk N D hN hD Edge _ m u left right t hm ht
  dsimp only
  let scale := a*(N^k)^30
  let η := localizedCountertermBound freq*N^r/scale
  let ε := ((N^k)^19)⁻¹
  let tol := (N^(2*r+p+6))⁻¹
  let Eform := localizedHubbardFormError m freq D (tol+tol)
  let A := hubbardFermionBottom m (localizedCoulombProfile freq 0)
    (localizedOffsiteCoulomb freq u) left right t-
    (1/2:ℝ)*(∑ i, ∑ j, localizedOffsiteCoulomb freq u i j)-Eform
  let K := (m+1:ℝ)*(((m+1:ℝ)+η)*PlanarSobolev.wellBound+6*Real.pi*rho+
    ((-1/2:ℝ)+freq/2))+2*(m+1:ℝ)*ε
  let g₀ := (γ/8)/(2*((m+1:ℝ)*(((m+1:ℝ)+η)*PlanarSobolev.wellBound+
    6*Real.pi*rho+((-1/2:ℝ)+freq/2))+γ/8+1))
  let g := (N^(qG+2*r))⁻¹
  have hN0 : 0 < N := by linarith
  have hN1 : 1 ≤ N := by linarith
  have hR0 : 0 < N^k := by positivity
  have hR1 : 1 ≤ N^k := one_le_pow₀ hN1
  have hM : 1 ≤ (m+1:ℝ) := by have := Nat.cast_nonneg (α := ℝ) m; linarith
  have hM0 : 0 ≤ (m+1:ℝ) := by positivity
  have he0 : 0 ≤ ε := by dsimp [ε]; positivity
  have he1 : ε ≤ 1 := by dsimp [ε]; exact inv_le_one_of_one_le₀ (one_le_pow₀ hR1)
  have hη0 : 0 ≤ η := by
    dsimp [η,scale]
    exact div_nonneg (mul_nonneg (localizedCountertermBound_nonnegative freq) (by positivity)) (by positivity)
  have hηmin : η ≤ min δ 1 := by
    calc
      _ = (localizedCountertermBound freq/a)*N^r/(N^k)^30 := by dsimp [η,scale]; ring
      _ ≤ (localizedCountertermBound freq/a)*N^r/(N^k)^2 := by
        gcongr
        · exact mul_nonneg (div_nonneg (localizedCountertermBound_nonnegative freq) ha.le) (pow_nonneg hN0.le r)
        · decide
      _ ≤ _ := by simpa only [Nat.add_zero,pow_zero,div_one] using heta r 0 k (by omega) N hN
  have hη1 : η ≤ 1 := hηmin.trans (min_le_right _ _)
  have hE : Eform ≤ (N^(p+2))⁻¹ := hform r p k (by omega) N D hN hD m hm
  have hE1 : Eform ≤ 1 := hE.trans (inv_le_one_of_one_le₀ (one_le_pow₀ hN1))
  have hA : |A| ≤ N^(qA+2*r+v) :=
    habs r v N hN m u left right t D (tol+tol) hm ht (by dsimp [tol]; positivity) hE1
  obtain ⟨hK,hg₀⟩ := hkin N hN r (m+1) η ε hM hm hη0 hη1 he1
  have hgap : b/N^(2*r) ≤ g₀ := by
    apply le_trans _ (manufactured_kinetic_complement_budgets hf hrho hγ hγ1 hM hη0 hη1 he1).2
    change b/N^(2*r) ≤ b/(m+1:ℝ)^2
    apply div_le_div_of_nonneg_left hb.le (by positivity)
    rw [show 2*r=r*2 by omega,pow_mul]
    exact pow_le_pow_left₀ hM0 hm 2
  have hsg := (hsmall r (qA+2*r+v) k (by omega) N (m+1) A hN hM0 hm hA).2
  have hsmall' : (B/(N^k)^20)*(m+1:ℝ)+|A/scale|+g ≤ g₀ := by
    change 2*g ≤ g₀ at hg₀
    change (B/(N^k)^20)*(m+1:ℝ)+|A/scale|+b/(2*N^(2*r)) ≤ b/N^(2*r) at hsg
    have hid : b/(2*N^(2*r))=(b/N^(2*r))/2 := by ring
    rw [hid] at hsg
    linarith only [hsg,hgap,hg₀]
  have hK0 : 0 ≤ K := by
    have hW := PlanarSobolev.wellBound_nonnegative
    have hE0 : 0 ≤ (-1/2:ℝ)+freq/2 := by linarith
    dsimp [K]
    positivity
  refine ⟨hη0,hη1,hηmin.trans (min_le_left _ _),?_,hE,by positivity,hsmall',?_⟩
  · simpa only [one_div] using hres r k (by omega) N (m+1) hN hM0 hm
  · exact herr r (qG+2*r) (qG+2*r) (p+2) k (by omega) N hN (m+1) K g
      hM0 hm hK0 hK le_rfl

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_ManufacturedPolynomialComparison
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform polynomial accuracy for the actual unit-charge cloud. All
infinite-dimensional estimates are derived from the cited published inputs. -/

noncomputable section
open MeasureTheory
open scoped BigOperators Classical NNReal
namespace ContinuumCoulomb
open HubbardGlobal

theorem manufactured_polynomial_comparison_oai
    (hflow : PublishedC4FlowInput)
    (hp : PlanarSobolev.ManufacturedPlanarGroundGap)
    (hv : PublishedVerticalOscillatorGap) (hdensity : PublishedSobolevSmoothDensity) :
    ∃ (rho : ℕ) (hrho : 0 < rho), ∃ L K : ℝ≥0, 0 < L ∧ 0 < K ∧
    let freq := GaussianFrequency.frequency rho
    ∃ q : ℕ, 1 ≤ q ∧ ∀ r s v p k : ℕ, q+9*r+72*s+v+p ≤ k →
    ∀ N H S D : ℝ, ∀ hN : 2 ≤ N,
      (N^k)^50 ≤ H → H ≤ 2*(N^k)^50 →
      (N^k)^5 ≤ S → S ≤ 2*(N^k)^5 → 25*(k:ℝ)*Real.log N ≤ D →
    ∀ (m n : ℕ) (u : Fin (m+1) → PlanarPosition), n+2=m+1 →
      (m+1:ℝ) ≤ N^r → (∀ i, ‖u i‖ ≤ N^s) →
      (∀ i j, i ≠ j → D ≤ ‖u i-u j‖) →
    ∀ {Edge : Type} [Fintype Edge] (left right : Edge → Fin (m+1)) (t : Edge → ℝ),
      (∑ e, |t e|) ≤ N^v →
      (∀ i j, ‖((((8/(rho:ℝ))*(N^k)^30)*planarHoppingMatrix u i j:ℝ):ℂ)-
        graphHoppingMatrix m left right (fun e => (t e:ℂ)) i j‖ ≤ (N^(2*r+p+6))⁻¹) →
    ∀ {ι : Type} [Fintype ι] [Nonempty ι] (index : ι → Fin 3 → ℤ)
      (hindex : Function.Injective index),
      (⋃ i, positionCube (gaussCellCenter (1/(N^k)^10) (index i)) (1/(N^k)^10)) = slabDomain H S →
    let scale := (8/(rho:ℝ))*(N^k)^30
    let center := scale^2*(n+2:ℝ)*(slabPotential rho H S 0+((-1/2:ℝ)+freq/2))+
      scale*(hubbardFermionBottom m (localizedCoulombProfile freq 0)
        (localizedOffsiteCoulomb freq u) left right t-
        (1/2:ℝ)*(∑ i, ∑ j, localizedOffsiteCoulomb freq u i j))
    ∃ (G : Position → ℝ → Position) (hbij : Function.Bijective (fun x => G x 1)),
      IsUnitTimeFlow (moserVelocity rho (manufacturedWellField freq scale S u)) G ∧
      LipschitzWith L (fun x => G x 1) ∧ AntilipschitzWith K (fun x => G x 1) ∧
      (∀ x, x ∉ tsupport (manufacturedWellField freq scale S u) → G x 1 = x) ∧
      (∀ x, |manufacturedCharge (manufacturedWellField freq scale S u) x| ≤ (rho:ℝ)/2) ∧
      ContDiff ℝ 4 (fun x => G x 1) ∧
      (∀ j : ℕ, 1 ≤ j → j ≤ 4 → ∀ x, ‖iteratedFDeriv ℝ j (fun y => G y 1) x‖ ≤ L) ∧
      (∀ i, localizedCounterterm freq u i ≤ scale) ∧
      ((center-scale*(N^p)⁻¹:ℝ):EReal) ≤
        formGroundEnergy (dilatedNuclei
          (gridNuclei index hindex (fun x => G x 1) hbij.injective (manufactured_mesh_positive hN k))
          scale (manufactured_scale_positive hrho hN k).ne') (n+2) ∧
      formGroundEnergy (dilatedNuclei
          (gridNuclei index hindex (fun x => G x 1) hbij.injective (manufactured_mesh_positive hN k))
          scale (manufactured_scale_positive hrho hN k).ne') (n+2) ≤
        ((center+scale*(N^p)⁻¹:ℝ):EReal) := by
  obtain ⟨rho,hrho,L,K,hL,hK,B,hB,hgrid⟩ := manufactured_grid_parameters hflow
  let freq := GaussianFrequency.frequency rho
  have hf : 1 ≤ freq := manufactured_frequency_ge_one hrho
  have hfp : 0 < freq := lt_of_lt_of_le zero_lt_one hf
  have hr : (0:ℝ) < rho := by exact_mod_cast hrho
  have ha : (0:ℝ) < 8/(rho:ℝ) := by positivity
  obtain ⟨qW,hqW,hwitness⟩ := hgrid freq hfp
  obtain ⟨γ,R,S₀,δ,C,hγ,hγ1,hR,hS₀,hδ,hC,hground⟩ :=
    manufactured_grid_ground_bounds hp hv hdensity hf hr.le (manufactured_frequency_relation rho)
  obtain ⟨qT,qG,hqT,_hqG,hscalar⟩ := manufactured_scalar_parameters hf hr.le ha hγ hγ1 hδ (zero_le_one.trans hB)
  obtain ⟨qD,hqD,hsepD⟩ := exists_logarithmic_scale_threshold R
  obtain ⟨qS,hqS,hslab⟩ := exists_centered_slab_threshold C S₀
  refine ⟨rho,hrho,L,K,hL,hK,qW+qT+qD+qS+7,by omega,?_⟩
  intro r s v p k hk N H S D hN hHlo hHhi hSlo hShi hD m n u hNe hm hu hsep
    Edge _ left right t ht hgraph ι _ _ index hindex hcover
  dsimp only
  let scale := (8/(rho:ℝ))*(N^k)^30
  let η := localizedCountertermBound freq*N^r/scale
  let ε := ((N^k)^19)⁻¹
  let tol := (N^(2*r+p+6))⁻¹
  let Eform := localizedHubbardFormError m freq D (tol+tol)
  let A := hubbardFermionBottom m (localizedCoulombProfile freq 0)
    (localizedOffsiteCoulomb freq u) left right t-
    (1/2:ℝ)*(∑ i, ∑ j, localizedOffsiteCoulomb freq u i j)-Eform
  let kin := (m+1:ℝ)*(((m+1:ℝ)+η)*PlanarSobolev.wellBound+6*Real.pi*rho+
    ((-1/2:ℝ)+freq/2))+2*(m+1:ℝ)*ε
  let g := (N^(qG+2*r))⁻¹
  let I := 3*((2*(m+1:ℝ)*ε)^2+scale⁻¹^2*(8*(m+1:ℝ)^3*kin)+
    (B/(N^k)^20)^2*((m+1:ℝ)+2*kin)*(m+1:ℝ))/g
  let center := scale^2*(n+2:ℝ)*(slabPotential rho H S 0+((-1/2:ℝ)+freq/2))+
    scale*(hubbardFermionBottom m (localizedCoulombProfile freq 0)
      (localizedOffsiteCoulomb freq u) left right t-
      (1/2:ℝ)*(∑ i, ∑ j, localizedOffsiteCoulomb freq u i j))
  have hN0 : 0 < N := by linarith
  have hN1 : 1 ≤ N := by linarith
  have hscale : 0 < scale := manufactured_scale_positive hrho hN k
  have hh : 0 < 1/(N^k)^10 := manufactured_mesh_positive hN k
  have he : 0 ≤ ε := by dsimp [ε]; positivity
  have htol : 0 ≤ tol := by dsimp [tol]; positivity
  have hmatch : (rho:ℝ)*(1/(N^k)^10)^3/8=scale⁻¹ := by
    dsimp [scale]
    field_simp
  obtain ⟨hcoeff,_hη0,_hη1,hres,G,hflow,hbij,hLip,hAnti,hfix,hcharge,hreg,hjets,hfull,hraw,hmatrix⟩ :=
    hwitness r s (2*r+p+6) k (by omega) N H S D hN hHlo hHhi hSlo hShi hD
      (m+1) u (by simpa only [Nat.cast_add,Nat.cast_one] using hm) hu hsep index hindex hcover
  obtain ⟨hη0,_hη1,hηδ,hresSmall,hE,hg,hsmall,hI⟩ :=
    hscalar r v p k (by omega) N D hN hD m u left right t hm ht
  obtain ⟨hS,hH,hCH,hrH⟩ := hslab k (by omega) N hN H S hHlo hSlo hShi
  have hsepR : R ≤ D := (hsepD k (by omega) N hN).trans hD
  have hcount : (m+1:ℝ) ≤ Real.exp ((19/320:ℝ)*D) :=
    hm.trans (polynomial_count_le_exp_separation hN (by omega : r ≤ k) hD)
  have hNeR : (n+2:ℝ)=(m+1:ℝ) := by exact_mod_cast hNe
  have hresSmall' : (n+1:ℝ)*(ε+ε^2/(γ/4)) ≤ γ/8 := by
    have hn : (n+1:ℝ) ≤ (m+1:ℝ) := by linarith only [hNeR]
    exact (mul_le_mul_of_nonneg_right hn (by positivity)).trans hresSmall
  have hB0 : 0 ≤ B/(N^k)^20 := div_nonneg (zero_le_one.trans hB) (by positivity)
  have hground' := hground m n D S H scale ((N^k)^5) ε η tol tol hsepR
    (by simpa only [Nat.cast_add,Nat.cast_one] using hcount) hS hH hCH hscale
    (by positivity) hrH hSlo he hη0 hηδ htol htol u hsep hcoeff hres hresSmall'
    index hindex (fun x => G x 1) hbij.injective (1/(N^k)^10) hh hmatch
    (B/(N^k)^20) hB0 (fun w s i => hfull (n+2) w s i) hraw hmatrix left right t (by simpa only [scale,tol,Complex.ofReal_mul] using hgraph) hNe g hg
  simp only [Nat.cast_add,Nat.cast_one,Nat.cast_ofNat,hNeR] at hground'
  have hbnds := hground' hsmall
  have hcenter : scale^2*(m+1:ℝ)*(slabPotential rho H S 0+((-1/2:ℝ)+freq/2))+
      scale*(hubbardFermionBottom m (localizedCoulombProfile freq 0)
        (localizedOffsiteCoulomb freq u) left right t-
        (1/2:ℝ)*(∑ i, ∑ j, localizedOffsiteCoulomb freq u i j)) = center := by
    dsimp only [center]
    rw [hNeR]
  rw [hcenter] at hbnds
  change ((center-scale*Eform-scale^2*I:ℝ):EReal) ≤ _ ∧ _ ≤ ((center+scale*Eform:ℝ):EReal) at hbnds
  have hpow : (N^(p+2))⁻¹+(N^(p+2))⁻¹ ≤ (N^p)⁻¹ := by
    apply (double_inverse_power_le hN (p+1)).trans
    exact inv_anti₀ (by positivity) (pow_le_pow_right₀ hN1 (by omega : p ≤ p+1))
  have htotal : scale*Eform+scale^2*I ≤ scale*(N^p)⁻¹ := by
    have hEI := add_le_add hE hI
    have hmul := mul_le_mul_of_nonneg_left (hEI.trans hpow) hscale.le
    change scale*(Eform+scale*I) ≤ _ at hmul
    nlinarith only [hmul]
  have hEonly : scale*Eform ≤ scale*(N^p)⁻¹ := by
    apply mul_le_mul_of_nonneg_left (hE.trans ?_) hscale.le
    exact inv_anti₀ (by positivity) (pow_le_pow_right₀ hN1 (by omega : p ≤ p+2))
  have hcounter (i : Fin (m+1)) : localizedCounterterm freq u i ≤ scale :=
    (div_le_one hscale).mp ((hcoeff i).2.trans _hη1)
  refine ⟨G,hbij,hflow,hLip,hAnti,hfix,hcharge,hreg,hjets,hcounter,?_,?_⟩
  · have hlo : center-scale*(N^p)⁻¹ ≤ center-scale*Eform-scale^2*I := by linarith only [htotal]
    exact (EReal.coe_le_coe_iff.mpr hlo).trans hbnds.1
  · have hup : center+scale*Eform ≤ center+scale*(N^p)⁻¹ := by linarith only [hEonly]
    exact hbnds.2.trans (EReal.coe_le_coe_iff.mpr hup)

end ContinuumCoulomb

end

end OAI
end

theorem solution : type_of% @OAI.ContinuumCoulomb.manufactured_polynomial_comparison_oai := @OAI.ContinuumCoulomb.manufactured_polynomial_comparison_oai
