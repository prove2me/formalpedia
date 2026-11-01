-- Prove2me | solution 1 for OAI.ContinuumCoulomb.unit_coulomb_qmaHard_of_two_inputs
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T21:29:18.354202+00:00
-- url     : https://prove2.me/submissions/1a6ae254-b121-49fe-9026-d31347056761

import Mathlib
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Pointwise.Set.Scalar
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
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.AffineMap
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Const
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convolution
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Operator.Compact
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.RCLike.Lemmas
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
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
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.GetD
import Mathlib.Data.List.Nodup
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.Data.Nat.Dist
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Data.Nat.Size
import Mathlib.Data.Rat.Cast.Order
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
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.MeasurableSpace.Embedding
import Mathlib.MeasureTheory.Measure.FiniteMeasure
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Tilted
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
import Mathlib.Topology.Compactness.Compact
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
import Theorems.Thm_OAI_ContinuumCoulomb_exists_source_unit_reduction_with_planar_gap

section
-- module Solutions.OAIQ092_CC.Analysis_FunctionalSpaces_Sobolev_Euclidean_L2Compactness_Smoothing
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength _root_.RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.L2Compactness.smoothBCF_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/

/-!
# `L²` compactness criterion: smoothing setup (Euclidean)

This file provides the basic “extend by zero + smooth by convolution” infrastructure used in the
Fréchet–Kolmogorov / Riesz–Kolmogorov approach to Euclidean Rellich–Kondrachov.

## Main results

- `RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.L2Compactness.extendByZeroL2`:
  extend `u : L²(volume.restrict K)` by zero to an element of `L²(volume)`.
- `RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.L2Compactness.smoothL2`:
  a smoothing operator obtained by convolution with a compactly supported continuous kernel `ψ`.
-/

namespace RellichKondrachov
namespace Analysis
namespace FunctionalSpaces
namespace Sobolev
namespace Euclidean
namespace L2Compactness

open scoped ENNReal MeasureTheory Topology Convolution Pointwise
open MeasureTheory Set

noncomputable section

section Volume

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

variable {K : Set E}

attribute [local instance] RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.L2Compactness.instMeasurableSpace_solutions_1
attribute [local instance] RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.L2Compactness.instBorelSpace_solutions_1
attribute [local instance] RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.L2Compactness.instOpensMeasurableSpace_solutions_1
local instance instMeasurableAdd_solutions_1_r1554e2_1 : MeasurableAdd E := by
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
lemma extendByZeroL2_ae_eq (hKm : MeasurableSet K)
    (u : MeasureTheory.Lp ℝ (2 : ℝ≥0∞) (volume.restrict K)) :
    (extendByZeroL2 (E := E) (K := K) hKm u : E → ℝ) =ᵐ[(volume : Measure E)]
      extendByZeroFun (E := E) (K := K) u := by
  classical
  simp [extendByZeroL2, MeasureTheory.MemLp.coeFn_toLp]

lemma extendByZeroL2_eq_extendByZeroₗᵢ (hKm : MeasurableSet K)
    (u : MeasureTheory.Lp ℝ (2 : ℝ≥0∞) (volume.restrict K)) :
    extendByZeroL2 (E := E) (K := K) hKm u =
      (MeasureTheory.Lp.extendByZeroₗᵢ (μ := (volume : Measure E)) (E := ℝ) (p := (2 : ℝ≥0∞))
        (s := K) hKm) u := by
  classical
  letI : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
  refine MeasureTheory.Lp.ext ?_
  have h1 :
      (extendByZeroL2 (E := E) (K := K) hKm u : E → ℝ) =ᵐ[(volume : Measure E)]
        extendByZeroFun (E := E) (K := K) u :=
    extendByZeroL2_ae_eq (E := E) (K := K) hKm u
  have h2 :
      ((MeasureTheory.Lp.extendByZeroₗᵢ (μ := (volume : Measure E)) (E := ℝ) (p := (2 : ℝ≥0∞))
        (s := K) hKm) u : E → ℝ) =ᵐ[(volume : Measure E)]
        extendByZeroFun (E := E) (K := K) u := by
    simp [extendByZeroFun]
    exact
      (MeasureTheory.Lp.extendByZeroₗᵢ_ae_eq (μ := (volume : Measure E)) (E := ℝ)
        (p := (2 : ℝ≥0∞)) (s := K) hKm u)
  exact h1.trans h2.symm

lemma norm_extendByZeroL2 (hKm : MeasurableSet K)
    (u : MeasureTheory.Lp ℝ (2 : ℝ≥0∞) (volume.restrict K)) :
    ‖extendByZeroL2 (E := E) (K := K) hKm u‖ = ‖u‖ := by
  classical
  letI : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
  calc
    ‖extendByZeroL2 (E := E) (K := K) hKm u‖ =
        ‖(MeasureTheory.Lp.extendByZeroₗᵢ (μ := (volume : Measure E)) (E := ℝ) (p := (2 : ℝ≥0∞))
          (s := K) hKm) u‖ := by
          simp [extendByZeroL2_eq_extendByZeroₗᵢ (E := E) (K := K) hKm u]
    _ = ‖u‖ :=
      (MeasureTheory.Lp.extendByZeroₗᵢ (μ := (volume : Measure E)) (E := ℝ) (p := (2 : ℝ≥0∞))
        (s := K) hKm).norm_map u
variable (ψ : E → ℝ)

lemma support_smoothFun_subset_add_tsupport
    (u : MeasureTheory.Lp ℝ (2 : ℝ≥0∞) (volume.restrict K)) :
    Function.support (smoothFun (E := E) (K := K) ψ u) ⊆ K + tsupport ψ := by
  classical
  have hsupp :
      Function.support (smoothFun (E := E) (K := K) ψ u) ⊆
        Function.support (extendByZeroFun (E := E) (K := K) u) + Function.support ψ := by
    simpa [smoothFun] using
      (support_convolution_subset (L := ContinuousLinearMap.lsmul ℝ ℝ) (μ := (volume : Measure E))
        (f := extendByZeroFun (E := E) (K := K) u) (g := ψ))
  have h1 : Function.support (extendByZeroFun (E := E) (K := K) u) ⊆ K := by
    simp [extendByZeroFun]
  have h2 : Function.support ψ ⊆ tsupport ψ := by
    simpa [tsupport] using (subset_closure : Function.support ψ ⊆ closure (Function.support ψ))
  exact hsupp.trans (add_subset_add h1 h2)

lemma smoothL2_ae_eq (hK : IsCompact K) (hKm : MeasurableSet K) (hψc : Continuous ψ)
    (hψcs : HasCompactSupport ψ)
    (u : MeasureTheory.Lp ℝ (2 : ℝ≥0∞) (volume.restrict K)) :
    (smoothL2 (E := E) (K := K) ψ hK hKm hψc hψcs u : E → ℝ) =ᵐ[(volume : Measure E)]
      smoothFun (E := E) (K := K) ψ u := by
  classical
  simp [smoothL2, MeasureTheory.MemLp.coeFn_toLp]
end Volume

end

end L2Compactness
end Euclidean
end Sobolev
end FunctionalSpaces
end Analysis
end RellichKondrachov
end

section
-- module Solutions.OAIQ092_CC.Analysis_FunctionalSpaces_Sobolev_Euclidean_Translation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/

/-!
# `RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.Translation`

Translation utilities for the Euclidean Sobolev model spaces.

This file is intentionally “pre-Rellich”: it provides the algebraic/measure-theoretic translation
operators and their interaction with the `C¹_c` graph embedding used to define `H¹`.

## Main results

- `translateC1c`: translation as a linear endomorphism of `C¹_c`.
- `translateL2`: translation as a linear isometry of `L²` (under an invariant measure).
- `translateL2_toL2` / `translateL2_toL2Grad`: translation commutes with `toL2` / `toL2Grad`.
- `grad_translate`: the Euclidean gradient commutes with translation.
-/

namespace RellichKondrachov
namespace Analysis
namespace FunctionalSpaces
namespace Sobolev
namespace Euclidean

open scoped ENNReal MeasureTheory Topology
open MeasureTheory

section Measure

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

attribute [local instance] RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.instMeasurableSpaceE_SobolevEuclideanTranslation
attribute [local instance] RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.instBorelSpaceE_SobolevEuclideanTranslation
local instance instOpensMeasurableSpaceE_SobolevEuclideanTranslation_r1554e2_1 : OpensMeasurableSpace E := by
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
attribute [local instance] RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.instMeasurableAddE_SobolevEuclideanTranslation
variable (μ : Measure E) [μ.IsAddRightInvariant]

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
lemma translateL2_ae_eq {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (a : E)
    (g : E →₂[μ] F) :
    (translateL2 (μ := μ) (F := F) a g : E → F) =ᵐ[μ] fun x => (g : E → F) (x + a) := by
  classical
  -- Reduce to `Lp.coeFn_compMeasurePreserving`.
  exact
    (MeasureTheory.Lp.coeFn_compMeasurePreserving (g := (g : MeasureTheory.Lp F (2 : ENNReal) μ))
      (hf := MeasureTheory.measurePreserving_add_right μ a))

end Measure

end Euclidean
end Sobolev
end FunctionalSpaces
end Analysis
end RellichKondrachov
end

section
-- module Solutions.OAIQ092_CC.Analysis_FunctionalSpaces_Sobolev_Euclidean_L2Compactness_Approximation
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength _root_.RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.L2Compactness.smoothBCF_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/

/-!
# `L²` compactness criterion: approximation-by-translation bounds (Euclidean)

This file will prove the key inequality used in the Fréchet–Kolmogorov approach: smoothing by a
probability kernel controls the `L²` error by the translation modulus.

## Main results (planned)

The principal statement will control `‖smoothL2 ψ u - extendByZeroL2 u‖₂` by an average (or sup) of
`‖translateL2 t (extendByZeroL2 u) - extendByZeroL2 u‖₂` over `t` in the support of `ψ`.
-/

namespace RellichKondrachov
namespace Analysis
namespace FunctionalSpaces
namespace Sobolev
namespace Euclidean
namespace L2Compactness

open scoped ENNReal MeasureTheory Topology Convolution
open MeasureTheory Set

noncomputable section

section Volume

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

attribute [local instance] RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.L2Compactness.instMeasurableSpace_solutions_2
attribute [local instance] RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.L2Compactness.instBorelSpace_solutions_2
local instance instOpensMeasurableSpace_solutions_2 : OpensMeasurableSpace E := by
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
local instance instMeasurableAdd_solutions_2 : MeasurableAdd E := by
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
local instance instMeasurableNeg_solutions : MeasurableNeg E := by
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

variable {K : Set E} (hK : IsCompact K) (hKm : MeasurableSet K)
variable (ψ : E → ℝ)

lemma kernelMeasure_univ (hψc : Continuous ψ) (hψcs : HasCompactSupport ψ) (hψ0 : ∀ x, 0 ≤ ψ x)
    (hψint : ∫ x, ψ x ∂(volume : Measure E) = 1) :
    kernelMeasure (E := E) ψ Set.univ = 1 := by
  have hψi : MeasureTheory.Integrable ψ (volume : Measure E) :=
    Continuous.integrable_of_hasCompactSupport (μ := (volume : Measure E)) hψc hψcs
  have hψae : (MeasureTheory.ae (volume : Measure E)).EventuallyLE 0 ψ :=
    Filter.Eventually.of_forall hψ0
  have hlin :
      (∫⁻ x, ENNReal.ofReal (ψ x) ∂(volume : Measure E)) =
        ENNReal.ofReal (∫ x, ψ x ∂(volume : Measure E)) := by
    symm
    exact MeasureTheory.ofReal_integral_eq_lintegral_ofReal hψi hψae
  -- `withDensity` on `univ` is the `lintegral` of the density.
  have hwd :
      kernelMeasure (E := E) ψ Set.univ =
        ∫⁻ x, ENNReal.ofReal (ψ x) ∂(volume : Measure E) := by
    simp [kernelMeasure, MeasureTheory.withDensity_apply, MeasurableSet.univ]
  -- Conclude using `∫ ψ = 1`.
  simpa [hψint] using (hwd.trans hlin)

theorem instIsProbabilityMeasure_kernelMeasure
    (hψc : Continuous ψ) (hψcs : HasCompactSupport ψ)
    (hψ0 : ∀ x, 0 ≤ ψ x)
    (hψint : ∫ x, ψ x ∂(volume : Measure E) = 1) :
    MeasureTheory.IsProbabilityMeasure (kernelMeasure (E := E) ψ) :=
  ⟨kernelMeasure_univ (E := E) (ψ := ψ) hψc hψcs hψ0 hψint⟩

lemma integral_kernelMeasure_eq_integral_smul (hψc : Continuous ψ) (hψ0 : ∀ x, 0 ≤ ψ x)
    (g : E → ℝ) :
    (∫ x, g x ∂kernelMeasure (E := E) ψ) =
      ∫ x, (ψ x) • (g x) ∂(volume : Measure E) := by
  have hmeas : Measurable fun x => ENNReal.ofReal (ψ x) :=
    (hψc.measurable.ennreal_ofReal : Measurable fun x => ENNReal.ofReal (ψ x))
  have htop :
      (MeasureTheory.ae (volume : Measure E)).Eventually
        (fun x => ENNReal.ofReal (ψ x) < ∞) :=
    Filter.Eventually.of_forall (fun _ => by simp)
  have hwd :=
    (integral_withDensity_eq_integral_toReal_smul (μ := (volume : Measure E))
      (f := fun x => ENNReal.ofReal (ψ x)) hmeas htop g)
  have hwd' :
      (∫ x, g x ∂kernelMeasure (E := E) ψ) =
        ∫ x, (ENNReal.ofReal (ψ x)).toReal • (g x) ∂(volume : Measure E) := by
    simpa [kernelMeasure] using hwd
  -- Simplify `toReal (ofReal _)` using `ψ ≥ 0`.
  refine hwd'.trans ?_
  refine integral_congr_ae ?_
  refine ae_of_all _ (fun x => ?_)
  have hx : (ENNReal.ofReal (ψ x)).toReal = ψ x :=
    ENNReal.toReal_ofReal (hψ0 x)
  -- After rewriting `toReal (ofReal _)`, both sides are definitional.
  simp [hx]

lemma integral_kernelMeasure_eq_integral_mul (hψc : Continuous ψ) (hψ0 : ∀ x, 0 ≤ ψ x)
    (g : E → ℝ) :
    (∫ x, g x ∂kernelMeasure (E := E) ψ) =
      ∫ x, (ψ x) * (g x) ∂(volume : Measure E) := by
  simpa [smul_eq_mul] using integral_kernelMeasure_eq_integral_smul (E := E) (ψ := ψ) hψc hψ0 g

lemma smoothFun_eq_integral_kernelMeasure (hψc : Continuous ψ) (hψ0 : ∀ x, 0 ≤ ψ x)
    (u : MeasureTheory.Lp ℝ (2 : ℝ≥0∞) (volume.restrict K)) (x : E) :
    smoothFun (E := E) (K := K) ψ u x =
      ∫ t, extendByZeroFun (E := E) (K := K) u (x - t) ∂kernelMeasure (E := E) ψ := by
  have hconv :
      smoothFun (E := E) (K := K) ψ u x =
        ∫ t, (extendByZeroFun (E := E) (K := K) u) (x - t) • (ψ t) ∂(volume : Measure E) := by
    simp [smoothFun, convolution_lsmul_swap]
  have hconv' :
      smoothFun (E := E) (K := K) ψ u x =
        ∫ t, (ψ t) * extendByZeroFun (E := E) (K := K) u (x - t) ∂(volume : Measure E) := by
    refine hconv.trans ?_
    refine integral_congr_ae ?_
    refine ae_of_all _ (fun t => ?_)
    -- In `ℝ`, scalar multiplication is multiplication, so we can commute the factors.
    change
      extendByZeroFun (E := E) (K := K) u (x - t) • ψ t =
        ψ t * extendByZeroFun (E := E) (K := K) u (x - t)
    rw [smul_eq_mul]
    simp [mul_comm]
  -- Rewrite the convolution integral as an integral against the density measure.
  have hwd :
      (∫ t, extendByZeroFun (E := E) (K := K) u (x - t) ∂kernelMeasure (E := E) ψ) =
        ∫ t, (ψ t) * extendByZeroFun (E := E) (K := K) u (x - t) ∂(volume : Measure E) := by
    exact integral_kernelMeasure_eq_integral_mul (E := E) (ψ := ψ) hψc hψ0
      (g := fun t => extendByZeroFun (E := E) (K := K) u (x - t))
  exact hconv'.trans hwd.symm

lemma sq_integral_le_integral_sq_of_isProbabilityMeasure {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [MeasureTheory.IsProbabilityMeasure μ] (f : α → ℝ)
    (hf : MeasureTheory.MemLp f 2 μ) :
    (∫ x, f x ∂μ) ^ 2 ≤ ∫ x, (f x) ^ 2 ∂μ := by
  have hvar := ProbabilityTheory.variance_nonneg (X := f) μ
  have hvar' :
      0 ≤ (∫ x, (f x) ^ 2 ∂μ) - (∫ x, f x ∂μ) ^ 2 := by
    simpa [ProbabilityTheory.variance_eq_sub (μ := μ) hf] using hvar
  linarith

private lemma norm_sq_eq_integral_sq (v : (E →₂[(volume : Measure E)] ℝ)) :
    ‖v‖ ^ 2 = ∫ x, (v x) ^ 2 ∂(volume : Measure E) := by
  have hn : ‖v‖ ^ 2 = RCLike.re (inner ℝ v v) :=
    norm_sq_eq_re_inner (𝕜 := ℝ) v
  -- Unfold the `L²` inner product as an integral; for `ℝ`, `re` is the identity.
  rw [hn]
  -- `L²` inner product is an integral of pointwise inner products.
  rw [MeasureTheory.L2.inner_def (𝕜 := ℝ) (μ := (volume : Measure E)) v v]
  -- For `ℝ`, `RCLike.re` is the identity and `inner` simplifies to a square.
  simp [pow_two]

lemma norm_sq_translateL2_sub_extendByZeroL2_eq_integral_sq (t : E)
    (u : MeasureTheory.Lp ℝ (2 : ℝ≥0∞) (volume.restrict K)) :
    ‖(translateL2 (μ := (volume : Measure E)) (-t))
        (extendByZeroL2 (E := E) (K := K) hKm u)
        - extendByZeroL2 (E := E) (K := K) hKm u‖ ^ 2 =
      ∫ x,
        (extendByZeroFun (E := E) (K := K) u (x - t) - extendByZeroFun (E := E) (K := K) u x) ^ 2
          ∂(volume : Measure E) := by
  classical
  let F : (E →₂[(volume : Measure E)] ℝ) := extendByZeroL2 (E := E) (K := K) hKm u
  let f : E → ℝ := extendByZeroFun (E := E) (K := K) u
  have hF_ae : (F : E → ℝ) =ᵐ[(volume : Measure E)] f :=
    extendByZeroL2_ae_eq (E := E) (K := K) (hKm := hKm) u
  -- Translate AE equality along `x ↦ x - t`.
  have hF_shift :
      (fun x : E => (F : E → ℝ) (x - t)) =ᵐ[(volume : Measure E)] fun x => f (x - t) := by
    have hmp :
        MeasureTheory.MeasurePreserving (fun x : E => x - t)
          (volume : Measure E) (volume : Measure E) :=
      MeasureTheory.measurePreserving_sub_right (μ := (volume : Measure E)) t
    exact (hmp.quasiMeasurePreserving.ae_eq_comp hF_ae)
  -- TranslateL2 gives `F(x - t)` a.e.
  have htrans :
      ((translateL2 (μ := (volume : Measure E)) (-t)) F : E → ℝ) =ᵐ[(volume : Measure E)]
        fun x => (F : E → ℝ) (x - t) := by
    simpa [sub_eq_add_neg] using (translateL2_ae_eq (μ := (volume : Measure E)) (-t) F)
  have htrans' :
      ((translateL2 (μ := (volume : Measure E)) (-t)) F : E → ℝ) =ᵐ[(volume : Measure E)]
        fun x => f (x - t) := by
    exact htrans.trans hF_shift
  have hdiff :
      (fun x => ((translateL2 (μ := (volume : Measure E)) (-t)) F - F) x) =ᵐ[(volume : Measure E)]
        fun x => f (x - t) - f x := by
    filter_upwards [MeasureTheory.Lp.coeFn_sub ((translateL2 (μ := (volume : Measure E)) (-t)) F) F,
      htrans', hF_ae] with x hxsub hx1 hx2
    -- `Lp.coeFn_sub` gives the pointwise relation between coercions of `Lp` subtraction.
    have hxsub' :
        ((translateL2 (μ := (volume : Measure E)) (-t)) F - F) x =
          ((translateL2 (μ := (volume : Measure E)) (-t)) F) x - F x := by
      simpa using hxsub
    -- Rewrite to the desired expression using the two pointwise identities.
    rw [hxsub', hx1, hx2]
  have hcalc :
      ‖(translateL2 (μ := (volume : Measure E)) (-t)) F - F‖ ^ 2 =
        ∫ x, (f (x - t) - f x) ^ 2 ∂(volume : Measure E) := by
    have h1 :=
      norm_sq_eq_integral_sq (E := E) (v := ((translateL2 (μ := (volume : Measure E)) (-t)) F - F))
    have h2 :
        ∫ x, (((translateL2 (μ := (volume : Measure E)) (-t)) F - F) x) ^ 2
            ∂(volume : Measure E) =
          ∫ x, (f (x - t) - f x) ^ 2 ∂(volume : Measure E) := by
      refine MeasureTheory.integral_congr_ae ?_
      exact hdiff.pow_const 2
    exact h1.trans h2
  simpa [F, f] using hcalc

private lemma kernelMeasure_le_smul_volume (hψc : Continuous ψ) (hψcs : HasCompactSupport ψ)
    (hψ0 : ∀ x, 0 ≤ ψ x) :
    ∃ c : ℝ≥0∞, c ≠ ⊤ ∧ kernelMeasure (E := E) ψ ≤ c • (volume : Measure E) := by
  classical
  obtain ⟨C, hC⟩ := hψcs.exists_bound_of_continuous hψc
  refine ⟨ENNReal.ofReal C, by simp, ?_⟩
  refine (Measure.le_iff).2 ?_
  intro s hs
  have hC0 : 0 ≤ C := le_trans (norm_nonneg (ψ 0)) (hC 0)
  have hψle : ∀ x, ENNReal.ofReal (ψ x) ≤ ENNReal.ofReal C := by
    intro x
    have hx : ψ x ≤ C := by
      have hx' : ‖ψ x‖ ≤ C := hC x
      -- `ψ ≥ 0`, so `‖ψ x‖ = ψ x`.
      simpa [Real.norm_eq_abs, abs_of_nonneg (hψ0 x)] using hx'
    exact ENNReal.ofReal_le_ofReal hx
  -- Unfold `withDensity` and bound the density by the constant `ENNReal.ofReal C`.
  simp [kernelMeasure, MeasureTheory.withDensity_apply, hs]
  have hle :
      (∫⁻ x in s, ENNReal.ofReal (ψ x) ∂(volume : Measure E)) ≤
        ∫⁻ x in s, ENNReal.ofReal C ∂(volume : Measure E) := by
    refine MeasureTheory.lintegral_mono ?_
    intro x
    exact hψle x
  refine hle.trans ?_
  simp

lemma smoothFun_sub_extendByZeroFun_sq_le_integral_sq
    (hψc : Continuous ψ) (hψcs : HasCompactSupport ψ)
    (hψ0 : ∀ x, 0 ≤ ψ x) (hψint : ∫ x, ψ x ∂(volume : Measure E) = 1) (hKm : MeasurableSet K)
    (u : MeasureTheory.Lp ℝ (2 : ℝ≥0∞) (volume.restrict K)) (x : E) :
    (smoothFun (E := E) (K := K) ψ u x - extendByZeroFun (E := E) (K := K) u x) ^ 2 ≤
      ∫ t,
        (extendByZeroFun (E := E) (K := K) u (x - t) - extendByZeroFun (E := E) (K := K) u x) ^ 2
          ∂kernelMeasure (E := E) ψ := by
  classical
  let μ : Measure E := kernelMeasure (E := E) ψ
  haveI : MeasureTheory.IsProbabilityMeasure μ :=
    instIsProbabilityMeasure_kernelMeasure (E := E) (ψ := ψ) hψc hψcs hψ0 hψint
  haveI : MeasureTheory.IsFiniteMeasure μ := by infer_instance
  rcases kernelMeasure_le_smul_volume (E := E) (ψ := ψ) hψc hψcs hψ0 with ⟨c, hc_top, hμle⟩
  let f : E → ℝ := extendByZeroFun (E := E) (K := K) u
  have hf_vol : MeasureTheory.MemLp f (2 : ℝ≥0∞) (volume : Measure E) := by
    -- Use the `L²` packaging of `extendByZeroFun` and the AE bridge.
    let F : (E →₂[(volume : Measure E)] ℝ) := extendByZeroL2 (E := E) (K := K) hKm u
    have hF : MeasureTheory.MemLp (fun x : E => (F : E → ℝ) x) (2 : ℝ≥0∞) (volume : Measure E) :=
      MeasureTheory.Lp.memLp F
    have hF_ae : (fun x : E => (F : E → ℝ) x) =ᵐ[(volume : Measure E)] f :=
      extendByZeroL2_ae_eq (E := E) (K := K) (hKm := hKm) u
    exact (MeasureTheory.memLp_congr_ae hF_ae).1 hF
  have hmp :
      MeasureTheory.MeasurePreserving (fun t : E => x - t)
        (volume : Measure E) (volume : Measure E) := by
    -- `t ↦ x - t = (-t) + x` is measure-preserving for Lebesgue (Haar) measure.
    have hneg :
        MeasureTheory.MeasurePreserving (Neg.neg : E → E)
          (volume : Measure E) (volume : Measure E) :=
      (volume : Measure E).measurePreserving_neg
    have hadd :
        MeasureTheory.MeasurePreserving (fun y : E => y + x)
          (volume : Measure E) (volume : Measure E) :=
      MeasureTheory.measurePreserving_add_right
        (μ := (volume : Measure E)) x
    have e : (fun t : E => x - t) = (fun y => y + x) ∘ Neg.neg := by
      funext t; simp [sub_eq_add_neg, add_comm]
    rw [e]; exact hadd.comp hneg
  have hf_shift_vol :
      MeasureTheory.MemLp (fun t : E => f (x - t))
        (2 : ℝ≥0∞) (volume : Measure E) :=
    hf_vol.comp_measurePreserving hmp
  have hf_shift :
      MeasureTheory.MemLp (fun t : E => f (x - t))
        (2 : ℝ≥0∞) μ := by
    exact MeasureTheory.MemLp.of_measure_le_smul
      (μ := (volume : Measure E)) (μ' := μ) (c := c)
      hc_top hμle hf_shift_vol
  have hf_const : MeasureTheory.MemLp (fun _ : E => f x) (2 : ℝ≥0∞) μ :=
    MeasureTheory.memLp_const (μ := μ) (c := f x)
  have hg : MeasureTheory.MemLp (fun t : E => f (x - t) - f x) (2 : ℝ≥0∞) μ :=
    hf_shift.sub hf_const
  have hsmooth :
      smoothFun (E := E) (K := K) ψ u x = ∫ t, f (x - t) ∂μ := by
    simpa [μ, f] using smoothFun_eq_integral_kernelMeasure (E := E) (K := K) (ψ := ψ) hψc hψ0 u x
  have hdiff :
      smoothFun (E := E) (K := K) ψ u x - f x = ∫ t, (f (x - t) - f x) ∂μ := by
    have hconst : (∫ _t : E, f x ∂μ) = f x := by
      simp [MeasureTheory.integral_const]
    have hint : MeasureTheory.Integrable (fun t : E => f (x - t)) μ :=
      hf_shift.integrable (by norm_num)
    have :
        (∫ t, f (x - t) ∂μ) - (∫ _t : E, f x ∂μ) =
          ∫ t, (f (x - t) - f x) ∂μ := by
      simpa using (MeasureTheory.integral_sub hint (MeasureTheory.integrable_const (f x))).symm
    simpa [hsmooth, hconst] using this
  -- Apply Jensen/variance inequality to `t ↦ f(x - t) - f(x)`.
  have hJ :=
    sq_integral_le_integral_sq_of_isProbabilityMeasure
      (μ := μ) (f := fun t : E => f (x - t) - f x) hg
  simpa [hdiff, μ, f] using hJ

lemma norm_sq_smoothL2_sub_extendByZeroL2_le_integral_norm_sq_translateL2_sub_extendByZeroL2
    (hψc : Continuous ψ) (hψcs : HasCompactSupport ψ) (hψ0 : ∀ x, 0 ≤ ψ x)
    (hψint : ∫ x, ψ x ∂(volume : Measure E) = 1)
    (u : MeasureTheory.Lp ℝ (2 : ℝ≥0∞) (volume.restrict K)) :
    ‖smoothL2 (E := E) (K := K) ψ hK hKm hψc hψcs u - extendByZeroL2 (E := E) (K := K) hKm u‖ ^ 2 ≤
      ∫ t,
        ‖(translateL2 (μ := (volume : Measure E)) (-t)) (extendByZeroL2 (E := E) (K := K) hKm u)
            - extendByZeroL2 (E := E) (K := K) hKm u‖ ^ 2
          ∂kernelMeasure (E := E) ψ := by
  classical
  let μ : Measure E := kernelMeasure (E := E) ψ
  haveI : MeasureTheory.IsProbabilityMeasure μ :=
    instIsProbabilityMeasure_kernelMeasure (E := E) (ψ := ψ) hψc hψcs hψ0 hψint
  haveI : MeasureTheory.IsFiniteMeasure μ := by infer_instance
  haveI : MeasureTheory.SFinite μ := by infer_instance
  let F : (E →₂[(volume : Measure E)] ℝ) := extendByZeroL2 (E := E) (K := K) hKm u
  let f : E → ℝ := extendByZeroFun (E := E) (K := K) u
  let S : (E →₂[(volume : Measure E)] ℝ) := smoothL2 (E := E) (K := K) ψ hK hKm hψc hψcs u
  have hS_ae :
      (S : E → ℝ) =ᵐ[(volume : Measure E)] smoothFun (E := E) (K := K) ψ u :=
    smoothL2_ae_eq (E := E) (K := K) (ψ := ψ) (hK := hK) (hKm := hKm) hψc hψcs u
  have hF_ae : (F : E → ℝ) =ᵐ[(volume : Measure E)] f :=
    extendByZeroL2_ae_eq (E := E) (K := K) (hKm := hKm) u
  have hSF_ae :
      (fun x : E => (S - F) x) =ᵐ[(volume : Measure E)] fun x =>
        smoothFun (E := E) (K := K) ψ u x - f x := by
    filter_upwards [MeasureTheory.Lp.coeFn_sub S F, hS_ae, hF_ae] with x hxsub hxS hxF
    have hxsub' : (S - F) x = S x - F x := by
      simpa using hxsub
    rw [hxsub', hxS, hxF]
  have hnorm_sq :
      ‖S - F‖ ^ 2 =
        ∫ x, (smoothFun (E := E) (K := K) ψ u x - f x) ^ 2 ∂(volume : Measure E) := by
    have h1 := norm_sq_eq_integral_sq (E := E) (v := (S - F))
    have h2 :
        (∫ x, ((S - F) x) ^ 2 ∂(volume : Measure E)) =
          ∫ x, (smoothFun (E := E) (K := K) ψ u x - f x) ^ 2 ∂(volume : Measure E) := by
      refine MeasureTheory.integral_congr_ae ?_
      exact hSF_ae.pow_const 2
    exact h1.trans h2
  have hLHS_int :
      MeasureTheory.Integrable (fun x : E => (smoothFun (E := E) (K := K) ψ u x - f x) ^ 2)
        (volume : Measure E) := by
    have hv_mem : MeasureTheory.MemLp (fun x : E => (S - F : E →₂[(volume : Measure E)] ℝ) x)
        (2 : ℝ≥0∞) (volume : Measure E) :=
      MeasureTheory.Lp.memLp (S - F)
    have hv_int :
        MeasureTheory.Integrable
          (fun x : E => ‖(S - F : E →₂[(volume : Measure E)] ℝ) x‖ ^ (2 : ℕ))
          (volume : Measure E) :=
      MeasureTheory.MemLp.integrable_norm_pow (μ := (volume : Measure E)) (f := fun x =>
        (S - F : E →₂[(volume : Measure E)] ℝ) x) (p := 2) hv_mem (by decide)
    -- Replace `‖·‖^2` by `(_)^2` in `ℝ`, then transport along the AE equality.
    have hv_sq :
        MeasureTheory.Integrable (fun x : E => ((S - F : E →₂[(volume : Measure E)] ℝ) x) ^ 2)
          (volume : Measure E) := by
      simpa [Real.norm_eq_abs, sq_abs] using hv_int
    exact hv_sq.congr (hSF_ae.pow_const 2)
  -- Show integrability on the product measure, so we can use Fubini/Tonelli for the translation
  -- error.
  let h : E × E → ℝ := fun z => (f (z.1 - z.2) - f z.1) ^ 2
  have hf_mem : MeasureTheory.MemLp f (2 : ℝ≥0∞) (volume : Measure E) := by
    -- Again use the AE bridge from the `L²` packaging.
    have hF : MeasureTheory.MemLp (fun x : E => (F : E → ℝ) x) (2 : ℝ≥0∞) (volume : Measure E) :=
      MeasureTheory.Lp.memLp F
    exact (MeasureTheory.memLp_congr_ae hF_ae).1 hF
  have hf_sq_int : MeasureTheory.Integrable (fun x : E => (f x) ^ 2) (volume : Measure E) := by
    have hf_int :
        MeasureTheory.Integrable (fun x : E => ‖f x‖ ^ (2 : ℕ)) (volume : Measure E) :=
      MeasureTheory.MemLp.integrable_norm_pow
        (μ := (volume : Measure E)) (f := f) (p := 2)
        hf_mem (by decide)
    simpa [Real.norm_eq_abs, sq_abs] using hf_int
  have hfst_map :
      MeasureTheory.Integrable (fun x : E => (f x) ^ 2)
        (Measure.map Prod.fst ((volume : Measure E).prod μ)) := by
    simpa [Measure.map_fst_prod] using hf_sq_int
  have hf_fst_sq_prod :
      MeasureTheory.Integrable (fun z : E × E => (f z.1) ^ 2) ((volume : Measure E).prod μ) :=
    (MeasureTheory.Integrable.comp_measurable (μ := (volume : Measure E).prod μ) (f := Prod.fst)
      (g := fun x : E => (f x) ^ 2) hfst_map measurable_fst)
  have hsub :
      MeasureTheory.MeasurePreserving
        (fun z : E × E => (z.1 - z.2, z.2))
        ((volume : Measure E).prod μ)
        ((volume : Measure E).prod μ) :=
    MeasureTheory.measurePreserving_sub_prod (μ := (volume : Measure E)) (ν := μ)
  have hf_shift_sq_prod :
      MeasureTheory.Integrable (fun z : E × E => (f (z.1 - z.2)) ^ 2)
        ((volume : Measure E).prod μ) := by
    have := (hsub.integrable_comp hf_fst_sq_prod.aestronglyMeasurable).2 hf_fst_sq_prod
    exact this
  have hdom :
      MeasureTheory.Integrable (fun z : E × E => (2 : ℝ) * ((f (z.1 - z.2)) ^ 2 + (f z.1) ^ 2))
        ((volume : Measure E).prod μ) := by
    simpa [mul_add, two_mul] using (hf_shift_sq_prod.add hf_fst_sq_prod).const_mul (2 : ℝ)
  have hf_fst_aesm :
      MeasureTheory.AEStronglyMeasurable (fun z : E × E => f z.1)
        ((volume : Measure E).prod μ) := by
    have hf_map :
        MeasureTheory.AEStronglyMeasurable f
          (Measure.map Prod.fst
            ((volume : Measure E).prod μ)) := by
      simpa [Measure.map_fst_prod] using hf_mem.1
    exact MeasureTheory.AEStronglyMeasurable.comp_measurable
      (μ := (volume : Measure E).prod μ) (f := Prod.fst)
      (g := f) hf_map measurable_fst
  have hf_shift_aesm :
      MeasureTheory.AEStronglyMeasurable
        (fun z : E × E => f (z.1 - z.2))
        ((volume : Measure E).prod μ) := by
    have := MeasureTheory.AEStronglyMeasurable.comp_measurePreserving (g := fun z : E × E => f z.1)
      hf_fst_aesm hsub
    exact this
  have h_aesm :
      MeasureTheory.AEStronglyMeasurable h ((volume : Measure E).prod μ) := by
    -- Build up AE-strong measurability from the two components.
    have hsub' :
        MeasureTheory.AEStronglyMeasurable (fun z : E × E => f (z.1 - z.2) - f z.1)
          ((volume : Measure E).prod μ) :=
      hf_shift_aesm.sub hf_fst_aesm
    exact (hsub'.pow 2)
  have hint_h : MeasureTheory.Integrable h ((volume : Measure E).prod μ) := by
    refine MeasureTheory.Integrable.mono (μ := (volume : Measure E).prod μ) hdom h_aesm ?_
    refine Filter.Eventually.of_forall ?_
    rintro ⟨x, t⟩
    have hineq :
        (f (x - t) - f x) ^ 2 ≤ (2 : ℝ) * ((f (x - t)) ^ 2 + (f x) ^ 2) := by
      -- `(a - b)^2 ≤ 2(a^2 + b^2)` as a special case of `add_sq_le`.
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
        (add_sq_le (a := f (x - t)) (b := -f x))
    have hnonneg : 0 ≤ (f (x - t) - f x) ^ 2 := by nlinarith
    have hsum_nonneg : 0 ≤ (f (x - t)) ^ 2 + (f x) ^ 2 := by nlinarith
    simpa [h, Real.norm_eq_abs, abs_of_nonneg hnonneg, abs_mul,
      abs_of_nonneg (show 0 ≤ (2 : ℝ) by norm_num),
      abs_of_nonneg hsum_nonneg] using hineq
  have hRHS_int :
      MeasureTheory.Integrable
        (fun x : E => ∫ t, (f (x - t) - f x) ^ 2 ∂μ) (volume : Measure E) := by
    simpa [h] using hint_h.integral_prod_left
  have hpoint :
      (fun x : E => (smoothFun (E := E) (K := K) ψ u x - f x) ^ 2)
        ≤ᶠ[MeasureTheory.ae (volume : Measure E)]
        fun x : E => ∫ t, (f (x - t) - f x) ^ 2 ∂μ := by
    refine Filter.Eventually.of_forall ?_
    intro x
    simpa [f, μ] using
      (smoothFun_sub_extendByZeroFun_sq_le_integral_sq (E := E) (K := K) (ψ := ψ)
        hψc hψcs hψ0 hψint hKm u x)
  have hinterm :
      ∫ x, (smoothFun (E := E) (K := K) ψ u x - f x) ^ 2 ∂(volume : Measure E) ≤
        ∫ x, (∫ t, (f (x - t) - f x) ^ 2 ∂μ) ∂(volume : Measure E) :=
    MeasureTheory.integral_mono_ae hLHS_int hRHS_int hpoint
  -- Swap the order of integration on the right-hand side.
  have hswap :
      (∫ x, (∫ t, (f (x - t) - f x) ^ 2 ∂μ) ∂(volume : Measure E)) =
        ∫ t, (∫ x, (f (x - t) - f x) ^ 2 ∂(volume : Measure E)) ∂μ := by
    simpa using (MeasureTheory.integral_integral_swap (μ := (volume : Measure E)) (ν := μ)
      (f := fun x t => (f (x - t) - f x) ^ 2) hint_h)
  -- Identify the inner `x` integral with the `L²` translation norm squared.
  have hinner :
      (fun t : E => ∫ x, (f (x - t) - f x) ^ 2 ∂(volume : Measure E)) =
        fun t : E =>
          ‖(translateL2 (μ := (volume : Measure E)) (-t)) F - F‖ ^ 2 := by
    funext t
    -- Use the previously proved integral identity.
    simpa [F, f] using
      (norm_sq_translateL2_sub_extendByZeroL2_eq_integral_sq
        (E := E) (K := K) (hKm := hKm) t u).symm
  have hRHS_rewrite :
      (∫ t, (∫ x, (f (x - t) - f x) ^ 2 ∂(volume : Measure E)) ∂μ) =
        ∫ t, ‖(translateL2 (μ := (volume : Measure E)) (-t)) F - F‖ ^ 2 ∂μ := by
    simp [hinner]
  -- Assemble everything.
  have hmain :
      ‖S - F‖ ^ 2 ≤
        ∫ t, ‖(translateL2 (μ := (volume : Measure E)) (-t)) F - F‖ ^ 2 ∂μ := by
    -- Convert `‖S-F‖²` to an `x`-integral and apply the integral inequality chain.
    have : ‖S - F‖ ^ 2 ≤ ∫ x, (∫ t, (f (x - t) - f x) ^ 2 ∂μ) ∂(volume : Measure E) := by
      simpa [hnorm_sq] using hinterm
    exact this.trans_eq (hswap.trans hRHS_rewrite)
  -- Restore the original statement.
  simpa [S, F, μ] using hmain


end Volume

end

end L2Compactness
end Euclidean
end Sobolev
end FunctionalSpaces
end Analysis
end RellichKondrachov
end

section
-- module Solutions.OAIQ092_CC.Analysis_FunctionalSpaces_Sobolev_Euclidean_L2Compactness_Compactness
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/

/-!
# `L²` compactness criterion: compact smoothing operator (Euclidean)

This file proves the compactness of the fixed-kernel smoothing operator used in the
Fréchet–Kolmogorov / Riesz–Kolmogorov approach to Euclidean Rellich–Kondrachov.

## Main results

- `Kψ`: the compact set `K + tsupport ψ` controlling supports of smoothed functions.
- `smoothBCF`: `smoothFun` packaged as a `BoundedContinuousFunction` on `Kψ`.
- `uniformContinuous_ψ`: `UniformContinuous ψ` from `Continuous ψ` + `HasCompactSupport ψ`.

The Arzelà–Ascoli compactness statement for `smoothBCF` lives in
`RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.L2Compactness.ArzelaAscoli`.

This is tracked under Beads `lean-103.5.2.26.5.3.2.2.1`.
-/

namespace RellichKondrachov
namespace Analysis
namespace FunctionalSpaces
namespace Sobolev
namespace Euclidean
namespace L2Compactness

open scoped ENNReal MeasureTheory Topology Convolution Pointwise
open MeasureTheory Set

noncomputable section

section Volume

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

variable {K : Set E}
variable {ψ : E → ℝ}

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
lemma uniformContinuous_ψ (hψc : Continuous ψ) (hψcs : HasCompactSupport ψ) :
    UniformContinuous ψ := by
  classical
  -- `HasCompactSupport` implies `ψ = 0` outside a compact set, hence `ψ → 0` along `cocompact`.
  refine
    Continuous.uniformContinuous_of_tendsto_cocompact (f := ψ) (x := (0 : ℝ)) hψc ?_
  -- Show `ψ → 0` along `cocompact` using the `ε`-ball characterization.
  refine (Metric.tendsto_nhds.2 ?_)
  intro ε hε
  refine Filter.mem_cocompact'.mpr ⟨tsupport ψ, hψcs, ?_⟩
  intro x hx
  -- If `ψ x` is `ε`-far from `0`, then `ψ x ≠ 0`, hence `x` belongs to the support and therefore
  -- to the topological support.
  have hx' : ¬ dist (ψ x) 0 < ε := by
    simpa [Set.mem_compl_iff, Set.mem_setOf_eq] using hx
  have hxε : ε ≤ dist (ψ x) 0 := le_of_not_gt (by simpa [gt_iff_lt] using hx')
  have hx0 : ψ x ≠ 0 := by
    intro hψ0
    have : dist (ψ x) 0 = 0 := by simp [hψ0]
    have : ε ≤ 0 := by simpa [this] using hxε
    exact not_lt_of_ge this hε
  have hx_supp : x ∈ Function.support ψ := by
    simpa [Function.support] using hx0
  have hx_tsupp : x ∈ tsupport ψ := by
    have : x ∈ closure (Function.support ψ) := subset_closure hx_supp
    simpa [tsupport] using this
  exact hx_tsupp

/-!
The remainder of the compactness proof (Arzelà–Ascoli on the family `smoothBCF '' closedBall`)
is tracked as part of `lean-103.5.2.26.5.3.2.2.1`.

We intentionally keep the helper lemmas above in this file so the final proof can stay short and
only reference re-usable bounds.
-/

end Volume

end

end L2Compactness
end Euclidean
end Sobolev
end FunctionalSpaces
end Analysis
end RellichKondrachov
end

section
-- module Solutions.OAIQ092_CC.Analysis_FunctionalSpaces_Sobolev_Euclidean_L2Compactness_ArzelaAscoli
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/

/-!
# `L²` compactness criterion: Arzelà–Ascoli for the smoothing operator (Euclidean)

This file proves the Arzelà–Ascoli step for the compact smoothing operator used in the
Fréchet–Kolmogorov / Riesz–Kolmogorov approach to Euclidean Rellich–Kondrachov.

## Main result

- `smoothBCF_image_closedBall_isCompact`:
  For a compact set `K` and a continuous compactly supported kernel `ψ`, the family
  `{ smoothFun ψ u | ‖u‖ ≤ R }` restricted to the compact set `K + tsupport ψ`
  has compact closure in `BoundedContinuousFunction`.

Tracking: Beads `lean-103.5.2.26.5.3.2.2.1.1`.
-/

namespace RellichKondrachov
namespace Analysis
namespace FunctionalSpaces
namespace Sobolev
namespace Euclidean
namespace L2Compactness

open scoped ENNReal MeasureTheory Topology Convolution Pointwise
open MeasureTheory Set

noncomputable section

section Volume

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

attribute [local instance] RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.L2Compactness.instMeasurableSpaceE_L2CompactnessArzelaAscoli
attribute [local instance] RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.L2Compactness.instBorelSpaceE_L2CompactnessArzelaAscoli
local instance instOpensMeasurableSpaceE_L2CompactnessArzelaAscoli : OpensMeasurableSpace E := by
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

variable {K : Set E} {ψ : E → ℝ}

local instance instMeasurableAddE_L2CompactnessArzelaAscoli_r1554e2_1 : MeasurableAdd E := by
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
local instance instMeasurableNegE_L2CompactnessArzelaAscoli_r1554e2_1 : MeasurableNeg E := by
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
private lemma smoothFun_eq_integral_restrict (hKm : MeasurableSet K)
    (u : MeasureTheory.Lp ℝ (2 : ℝ≥0∞) (volume.restrict K)) (x : E) :
    smoothFun (E := E) (K := K) ψ u x =
      ∫ t, u t * ψ (x - t) ∂(volume.restrict K) := by
  classical
  -- Unfold convolution, then restrict the integral using the indicator defining `extendByZeroFun`.
  have :
      smoothFun (E := E) (K := K) ψ u x =
        ∫ t, (extendByZeroFun (E := E) (K := K) u t) • ψ (x - t) ∂(volume : Measure E) := by
    simp [smoothFun, MeasureTheory.convolution_lsmul]
  have h_ind :
      (fun t : E => extendByZeroFun (E := E) (K := K) u t * ψ (x - t)) =
        K.indicator (fun t : E => u t * ψ (x - t)) := by
    funext t
    by_cases ht : t ∈ K <;> simp [extendByZeroFun, ht]
  -- Restrict to `K` using the indicator.
  simp [this, h_ind, MeasureTheory.integral_indicator hKm]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
private lemma isCompact_diffSet (hK : IsCompact K) (hψcs : HasCompactSupport ψ) :
    IsCompact
      ((fun p : E × E => p.1 - p.2) '' ((Kψ (K := K) (ψ := ψ)) ×ˢ K)) := by
  have hKψ : IsCompact (Kψ (K := K) (ψ := ψ)) := isCompact_Kψ (K := K) (ψ := ψ) hK hψcs
  have hprod : IsCompact ((Kψ (K := K) (ψ := ψ)) ×ˢ K) := hKψ.prod hK
  refine hprod.image ?_
  exact (continuous_fst.sub continuous_snd)

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
private lemma exists_norm_ψ_bound_on_diffSet (hK : IsCompact K) (hψc : Continuous ψ)
    (hψcs : HasCompactSupport ψ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ x : ↥(Kψ (K := K) (ψ := ψ)), ∀ t : E, t ∈ K → ‖ψ ((x : E) - t)‖ ≤ C := by
  classical
  let diffSet : Set E :=
    (fun p : E × E => p.1 - p.2) '' ((Kψ (K := K) (ψ := ψ)) ×ˢ K)
  have hdiff : IsCompact diffSet := isCompact_diffSet (E := E) (K := K) (ψ := ψ) hK hψcs
  by_cases hne : diffSet.Nonempty
  · -- Use the extreme value theorem on the continuous function `z ↦ ‖ψ z‖`.
    have hcont : Continuous (fun z : E => ‖ψ z‖) := hψc.norm
    rcases hdiff.exists_isMaxOn hne (hcont.continuousOn) with ⟨z0, hz0, hzmax⟩
    refine ⟨‖ψ z0‖, norm_nonneg _, ?_⟩
    intro x t ht
    have hx : (x : E) ∈ Kψ (K := K) (ψ := ψ) := x.2
    have hx_t : (x : E) - t ∈ diffSet := by
      refine ⟨((x : E), t), ?_, rfl⟩
      exact ⟨hx, ht⟩
    exact (isMaxOn_iff.1 hzmax) _ hx_t
  · -- `diffSet = ∅`: take the trivial bound.
    refine ⟨0, le_rfl, ?_⟩
    intro x t ht
    exfalso
    have hx : (x : E) ∈ Kψ (K := K) (ψ := ψ) := x.2
    have : (x : E) - t ∈ diffSet := by
      refine ⟨((x : E), t), ?_, rfl⟩
      exact ⟨hx, ht⟩
    exact hne ⟨(x : E) - t, this⟩

/-- Arzelà--Ascoli: smoothing maps `L²(K)` bounded sets into a precompact set
in `BCF(K + tsupport ψ)`. -/
theorem smoothBCF_image_closedBall_isCompact (hK : IsCompact K) (hKm : MeasurableSet K)
    (hψc : Continuous ψ) (hψcs : HasCompactSupport ψ) {R : ℝ} (hR : 0 ≤ R) :
    IsCompact
        (closure
          (smoothBCF (E := E) (K := K) (ψ := ψ) hK hKm hψc hψcs '' Metric.closedBall (0 : _)
            R)) := by
  classical
  -- Radius `0`: the image is a singleton, hence compact.
  by_cases hR0 : R = 0
  · subst hR0
    have hball :
        Metric.closedBall (0 : MeasureTheory.Lp ℝ (2 : ℝ≥0∞) (volume.restrict K)) 0 = {0} := by
      ext u
      simp
    -- Reduce to a singleton.
    simp [hball]
  · have hRpos : 0 < R := lt_of_le_of_ne hR (Ne.symm hR0)
    -- Compactness of the codomain.
    letI : CompactSpace ↥(Kψ (K := K) (ψ := ψ)) :=
      isCompact_iff_compactSpace.1 (isCompact_Kψ (K := K) (ψ := ψ) hK hψcs)
    let A :
        Set (BoundedContinuousFunction (↥(Kψ (K := K) (ψ := ψ))) ℝ) :=
      smoothBCF (E := E) (K := K) (ψ := ψ) hK hKm hψc hψcs '' Metric.closedBall (0 : _) R
    -- `volume.restrict K` is finite since `K` is compact.
    have hμK : (volume : Measure E) K < ∞ := hK.measure_lt_top (μ := (volume : Measure E))
    letI : Fact ((volume : Measure E) K < ∞) := ⟨hμK⟩
    haveI : IsFiniteMeasure (volume.restrict K) := by
      first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
    let μ : Measure E := (volume : Measure E).restrict K
    let mK : ℝ :=
      (MeasureTheory.measureUnivNNReal (volume.restrict K)) ^ ((2 : ℝ≥0∞).toReal⁻¹)
    have hmK : 0 ≤ mK := by
      have : 0 ≤ (MeasureTheory.measureUnivNNReal (volume.restrict K)) := by simp
      exact Real.rpow_nonneg this _
    -- Uniform bound on `ψ` over the relevant compact difference set.
    obtain ⟨Cψ, hCψ_nonneg, hψ_bound⟩ :=
      exists_norm_ψ_bound_on_diffSet (E := E) (K := K) (ψ := ψ) hK hψc hψcs
    -- A compact ball controlling all values.
    let s : Set ℝ := Metric.closedBall (0 : ℝ) (R * (mK * Cψ))
    have hs : IsCompact s := by
      simpa [s] using isCompact_closedBall (0 : ℝ) (R * (mK * Cψ))
    -- Pointwise compact range: each function in `A` takes values in `s`.
    have in_s :
        ∀ (f : BoundedContinuousFunction (↥(Kψ (K := K) (ψ := ψ))) ℝ) (x : ↥(Kψ (K := K) (ψ := ψ))),
          f ∈ A → f x ∈ s := by
      intro f x hfA
      rcases hfA with ⟨u, hu_ball, rfl⟩
      have hu_norm : ‖u‖ ≤ R := by
        simpa [Metric.mem_closedBall, dist_eq_norm] using hu_ball
      -- Build the `L²(K)` kernel element.
      have hker :
          MemLp (fun t : E => ψ ((x : E) - t)) (2 : ℝ≥0∞) (volume.restrict K) := by
        refine MemLp.of_bound (μ := (volume.restrict K))
          (hf := (hψc.aestronglyMeasurable.comp_measurable
            (measurable_const.sub measurable_id))) Cψ ?_
        filter_upwards
          [MeasureTheory.ae_restrict_mem
            (μ := (volume : Measure E)) hKm] with t ht
        exact hψ_bound x t ht
      let kx : MeasureTheory.Lp ℝ (2 : ℝ≥0∞) μ :=
        hker.toLp (fun t : E => ψ ((x : E) - t))
      have hkx_norm : ‖kx‖ ≤ mK * Cψ := by
        have h_ae :
            ∀ᵐ t ∂(volume.restrict K), ‖(fun t : E => ψ ((x : E) - t)) t‖ ≤ Cψ := by
          filter_upwards [MeasureTheory.ae_restrict_mem (μ := (volume : Measure E)) hKm] with t ht
          exact hψ_bound x t ht
        have := (MeasureTheory.Lp.norm_le_of_ae_bound
          (μ := (volume.restrict K)) (p := (2 : ℝ≥0∞))
          (f := kx) (hC := hCψ_nonneg) (by
            -- transport the bound through the `toLp` representative
            filter_upwards [h_ae,
              MeasureTheory.MemLp.coeFn_toLp
                (μ := (volume.restrict K)) (p := (2 : ℝ≥0∞))
                (f := fun t : E => ψ ((x : E) - t))
                hker] with t ht hrep
            simpa [kx, hrep] using ht))
        simpa [mK] using this
      -- Express the smoothing value as an `L²` inner product, then apply Cauchy–Schwarz.
      have hsmooth :
          smoothFun (E := E) (K := K) ψ u (x : E) =
            ∫ t, u t * kx t ∂(volume.restrict K) := by
        have h_ae :
            (fun t : E => u t * kx t) =ᵐ[volume.restrict K] fun t : E => u t * ψ ((x : E) - t) := by
          filter_upwards [MeasureTheory.MemLp.coeFn_toLp
            (μ := (volume.restrict K)) (p := (2 : ℝ≥0∞))
            (f := fun t : E => ψ ((x : E) - t))
            hker] with t ht
          simp [kx, ht]
        -- rewrite `smoothFun` as an integral on `volume.restrict K`
        rw [smoothFun_eq_integral_restrict
          (E := E) (K := K) (ψ := ψ) (hKm := hKm) u (x : E)]
        exact (MeasureTheory.integral_congr_ae h_ae.symm)
      have hsmooth' :
          smoothFun (E := E) (K := K) ψ u (x : E) =
            ∫ t, kx t * u t ∂(volume.restrict K) := by
        simp [hsmooth, mul_comm]
      have hinner :
          smoothFun (E := E) (K := K) ψ u (x : E) =
            inner ℝ (u : MeasureTheory.Lp ℝ (2 : ℝ≥0∞) μ) kx := by
        erw [MeasureTheory.L2.inner_def]; exact hsmooth'
      have habs :
          |smoothFun (E := E) (K := K) ψ u (x : E)| ≤ ‖u‖ * ‖kx‖ := by
        simpa [hinner] using
          (abs_real_inner_le_norm (u : MeasureTheory.Lp ℝ (2 : ℝ≥0∞) μ) kx)
      have habs' : |smoothFun (E := E) (K := K) ψ u (x : E)| ≤ R * (mK * Cψ) := by
        calc
          |smoothFun (E := E) (K := K) ψ u (x : E)|
              ≤ ‖u‖ * ‖kx‖ := habs
          _ ≤ R * (mK * Cψ) := by
            exact mul_le_mul hu_norm hkx_norm (norm_nonneg _) hR
      have : dist (smoothBCF (E := E) (K := K) (ψ := ψ) hK hKm hψc hψcs u x) 0 ≤ R * (mK * Cψ) := by
        simpa [smoothBCF_apply (E := E) (K := K) (ψ := ψ) hK hKm hψc hψcs u x,
          dist_eq_norm, Real.norm_eq_abs] using habs'
      simpa [s, Metric.mem_closedBall, dist_eq_norm] using this
    -- Equicontinuity for `A`.
    have H' : UniformEquicontinuous ((↑) : A → ↥(Kψ (K := K) (ψ := ψ)) → ℝ) := by
      rw [Metric.uniformEquicontinuous_iff]
      intro ε hε
      -- Handle the zero-measure case separately (then `mK = 0` and everything is constant).
      by_cases hmK0 : mK = 0
      · refine ⟨1, by norm_num, ?_⟩
        intro x y _ f
        -- With `mK = 0`, the range bound forces all values to be `0`.
        have hx0 : dist ((f : BoundedContinuousFunction (↥(Kψ (K := K) (ψ := ψ))) ℝ) x) 0 ≤
            R * (mK * Cψ) := by
          have :
              (f : BoundedContinuousFunction (↥(Kψ (K := K) (ψ := ψ))) ℝ) x ∈ s :=
            in_s (f := (f : BoundedContinuousFunction (↥(Kψ (K := K) (ψ := ψ))) ℝ)) x f.property
          simpa [s, Metric.mem_closedBall] using this
        have hy0 : dist ((f : BoundedContinuousFunction (↥(Kψ (K := K) (ψ := ψ))) ℝ) y) 0 ≤
            R * (mK * Cψ) := by
          have :
              (f : BoundedContinuousFunction (↥(Kψ (K := K) (ψ := ψ))) ℝ) y ∈ s :=
            in_s (f := (f : BoundedContinuousFunction (↥(Kψ (K := K) (ψ := ψ))) ℝ)) y f.property
          simpa [s, Metric.mem_closedBall] using this
        have hx0' :
            dist ((f : BoundedContinuousFunction (↥(Kψ (K := K) (ψ := ψ))) ℝ) x) 0 = 0 := by
          have : dist ((f : BoundedContinuousFunction (↥(Kψ (K := K) (ψ := ψ))) ℝ) x) 0 ≤ 0 := by
            simpa [hmK0] using hx0
          exact le_antisymm this dist_nonneg
        have hy0' :
            dist ((f : BoundedContinuousFunction (↥(Kψ (K := K) (ψ := ψ))) ℝ) y) 0 = 0 := by
          have : dist ((f : BoundedContinuousFunction (↥(Kψ (K := K) (ψ := ψ))) ℝ) y) 0 ≤ 0 := by
            simpa [hmK0] using hy0
          exact le_antisymm this dist_nonneg
        have hx : (f : BoundedContinuousFunction (↥(Kψ (K := K) (ψ := ψ))) ℝ) x = 0 :=
          dist_eq_zero.1 hx0'
        have hy : (f : BoundedContinuousFunction (↥(Kψ (K := K) (ψ := ψ))) ℝ) y = 0 :=
          dist_eq_zero.1 hy0'
        simpa [hx, hy] using hε
      · have hRmK_ne : R * mK ≠ 0 := mul_ne_zero hR0 hmK0
        let ε2 : ℝ := ε / 2
        have hε2pos : 0 < ε2 := by
          simpa [ε2] using half_pos hε
        let ε' : ℝ := ε2 / (R * mK)
        have hε'pos : 0 < ε' :=
          div_pos hε2pos (mul_pos hRpos (lt_of_le_of_ne hmK (Ne.symm hmK0)))
        have hε'lt : R * mK * ε' = ε2 := by
          dsimp [ε']
          field_simp [hRmK_ne, mul_assoc, mul_left_comm, mul_comm]
        -- Use uniform continuity of `ψ` to get `δ`.
        have hUC : UniformContinuous ψ := uniformContinuous_ψ (E := E) (ψ := ψ) hψc hψcs
        rcases (Metric.uniformContinuous_iff.1 hUC) ε' hε'pos with ⟨δ, hδpos, hδ⟩
        refine ⟨δ, hδpos, ?_⟩
        intro x y hxy f
        -- Work with the `smoothBCF` representative of `f`.
        rcases f.property with ⟨u, hu_ball, hu_eq⟩
        have hu_eq' :
            (f : BoundedContinuousFunction (↥(Kψ (K := K) (ψ := ψ))) ℝ) =
              smoothBCF (E := E) (K := K) (ψ := ψ) hK hKm hψc hψcs u := by
          simpa using hu_eq.symm
        have hu_norm : ‖u‖ ≤ R := by
          simpa [Metric.mem_closedBall, dist_eq_norm] using hu_ball
        -- Kernel elements at `x` and `y`.
        have hkerx :
            MemLp (fun t : E => ψ ((x : E) - t)) (2 : ℝ≥0∞) (volume.restrict K) := by
          refine MemLp.of_bound (μ := (volume.restrict K))
            (hf := (hψc.aestronglyMeasurable.comp_measurable
              (measurable_const.sub measurable_id))) Cψ ?_
          filter_upwards
            [MeasureTheory.ae_restrict_mem
              (μ := (volume : Measure E)) hKm] with t ht
          exact hψ_bound x t ht
        have hkery :
            MemLp (fun t : E => ψ ((y : E) - t)) (2 : ℝ≥0∞) (volume.restrict K) := by
          refine MemLp.of_bound (μ := (volume.restrict K))
            (hf := (hψc.aestronglyMeasurable.comp_measurable
              (measurable_const.sub measurable_id))) Cψ ?_
          filter_upwards [MeasureTheory.ae_restrict_mem (μ := (volume : Measure E)) hKm] with t ht
          exact hψ_bound y t ht
        let kx : MeasureTheory.Lp ℝ (2 : ℝ≥0∞) μ :=
          hkerx.toLp (fun t : E => ψ ((x : E) - t))
        let ky : MeasureTheory.Lp ℝ (2 : ℝ≥0∞) μ :=
          hkery.toLp (fun t : E => ψ ((y : E) - t))
        -- AE bound on `‖kx - ky‖` by `ε'`.
        have h_ae :
            ∀ᵐ t ∂(volume.restrict K), ‖(kx - ky) t‖ ≤ ε' := by
          filter_upwards [MeasureTheory.ae_restrict_mem (μ := (volume : Measure E)) hKm,
            MeasureTheory.MemLp.coeFn_toLp (μ := (volume.restrict K)) (p := (2 : ℝ≥0∞))
              (f := fun t : E => ψ ((x : E) - t)) hkerx,
            MeasureTheory.MemLp.coeFn_toLp (μ := (volume.restrict K)) (p := (2 : ℝ≥0∞))
              (f := fun t : E => ψ ((y : E) - t)) hkery,
            (MeasureTheory.Lp.coeFn_sub (μ := (volume.restrict K)) (p := (2 : ℝ≥0∞)) kx ky)] with
            t ht hx_t hy_t hsub
          have hxy' : dist ((x : E) - t) ((y : E) - t) < δ := by
            simpa [sub_eq_add_neg, add_assoc, Subtype.dist_eq] using hxy
          have hψxy : dist (ψ ((x : E) - t)) (ψ ((y : E) - t)) < ε' :=
            hδ (a := (x : E) - t) (b := (y : E) - t) hxy'
          have : ‖ψ ((x : E) - t) - ψ ((y : E) - t)‖ ≤ ε' := by
            simpa [dist_eq_norm, sub_eq_add_neg] using le_of_lt hψxy
          have hx' : kx t = ψ ((x : E) - t) := by simpa [kx] using hx_t
          have hy' : ky t = ψ ((y : E) - t) := by simpa [ky] using hy_t
          have hnorm : ‖kx t - ky t‖ ≤ ε' := by
            simpa [hx', hy'] using this
          have hsub' : (kx - ky) t = kx t - ky t := by
            simpa [Pi.sub_apply] using hsub
          simpa [hsub'.symm] using hnorm
        have hkdiff : ‖kx - ky‖ ≤ mK * ε' := by
          have := (MeasureTheory.Lp.norm_le_of_ae_bound (μ := (volume.restrict K)) (p := (2 : ℝ≥0∞))
            (f := (kx - ky : MeasureTheory.Lp ℝ (2 : ℝ≥0∞) μ)) (hC := le_of_lt hε'pos) h_ae)
          simpa [mK, mul_comm, mul_left_comm, mul_assoc] using this
        -- Bound the difference of values using Cauchy–Schwarz.
        have hdist :
            dist (smoothBCF (E := E) (K := K) (ψ := ψ) hK hKm hψc hψcs u x)
                (smoothBCF (E := E) (K := K) (ψ := ψ) hK hKm hψc hψcs u y)
              ≤ ‖u‖ * ‖kx - ky‖ := by
          -- Express each value as an inner product.
          have hx_val :
              smoothBCF (E := E) (K := K) (ψ := ψ) hK hKm hψc hψcs u x =
                inner ℝ (u : MeasureTheory.Lp ℝ (2 : ℝ≥0∞) μ) kx := by
            have hsmooth :
                smoothFun (E := E) (K := K) ψ u (x : E) =
                  ∫ t, u t * kx t ∂(volume.restrict K) := by
              have h_ae' :
                  (fun t : E => u t * kx t) =ᵐ[volume.restrict K]
                    fun t : E => u t * ψ ((x : E) - t) := by
                filter_upwards [MeasureTheory.MemLp.coeFn_toLp
                  (μ := (volume.restrict K)) (p := (2 : ℝ≥0∞))
                  (f := fun t : E => ψ ((x : E) - t))
                  hkerx] with t ht
                simp [kx, ht]
              rw [smoothFun_eq_integral_restrict
                (E := E) (K := K) (ψ := ψ) (hKm := hKm)
                u (x : E)]
              exact (MeasureTheory.integral_congr_ae h_ae'.symm)
            have hsmooth' :
                smoothFun (E := E) (K := K) ψ u (x : E) =
                  ∫ t, kx t * u t ∂(volume.restrict K) := by
              simp [hsmooth, mul_comm]
            erw [smoothBCF_apply (E := E) (K := K) (ψ := ψ) hK hKm hψc hψcs u x,
              MeasureTheory.L2.inner_def]; exact hsmooth'
          have hy_val :
              smoothBCF (E := E) (K := K) (ψ := ψ) hK hKm hψc hψcs u y =
                inner ℝ (u : MeasureTheory.Lp ℝ (2 : ℝ≥0∞) μ) ky := by
            have hsmooth :
                smoothFun (E := E) (K := K) ψ u (y : E) =
                  ∫ t, u t * ky t ∂(volume.restrict K) := by
              have h_ae' :
                  (fun t : E => u t * ky t) =ᵐ[volume.restrict K]
                    fun t : E => u t * ψ ((y : E) - t) := by
                filter_upwards [MeasureTheory.MemLp.coeFn_toLp
                  (μ := (volume.restrict K)) (p := (2 : ℝ≥0∞))
                  (f := fun t : E => ψ ((y : E) - t))
                  hkery] with t ht
                simp [ky, ht]
              rw [smoothFun_eq_integral_restrict
                (E := E) (K := K) (ψ := ψ) (hKm := hKm)
                u (y : E)]
              exact (MeasureTheory.integral_congr_ae h_ae'.symm)
            have hsmooth' :
                smoothFun (E := E) (K := K) ψ u (y : E) =
                  ∫ t, ky t * u t ∂(volume.restrict K) := by
              simp [hsmooth, mul_comm]
            erw [smoothBCF_apply (E := E) (K := K) (ψ := ψ) hK hKm hψc hψcs u y,
              MeasureTheory.L2.inner_def]; exact hsmooth'
          have :
              ‖smoothBCF (E := E) (K := K) (ψ := ψ) hK hKm hψc hψcs u x -
                  smoothBCF (E := E) (K := K) (ψ := ψ) hK hKm hψc hψcs u y‖ ≤
                ‖u‖ * ‖kx - ky‖ := by
            have :
                smoothBCF (E := E) (K := K) (ψ := ψ) hK hKm hψc hψcs u x -
                    smoothBCF (E := E) (K := K) (ψ := ψ) hK hKm hψc hψcs u y =
                  inner ℝ (u : MeasureTheory.Lp ℝ (2 : ℝ≥0∞) μ) (kx - ky) := by
              simp [hx_val, hy_val, inner_sub_right]
            have this' :
                smoothFun (E := E) (K := K) ψ u (x : E) - smoothFun (E := E) (K := K) ψ u (y : E) =
                  inner ℝ (u : MeasureTheory.Lp ℝ (2 : ℝ≥0∞) μ) (kx - ky) := by
              simpa [smoothBCF_apply (E := E) (K := K) (ψ := ψ) hK hKm hψc hψcs] using this
            have hCS :=
              (abs_real_inner_le_norm (u : MeasureTheory.Lp ℝ (2 : ℝ≥0∞) μ) (kx - ky))
            simpa [this', dist_eq_norm, Real.norm_eq_abs] using hCS
          simpa [dist_eq_norm] using this
        have hle :
            dist (smoothBCF (E := E) (K := K) (ψ := ψ) hK hKm hψc hψcs u x)
                (smoothBCF (E := E) (K := K) (ψ := ψ) hK hKm hψc hψcs u y)
              ≤ R * (mK * ε') := by
          calc
            dist (smoothBCF (E := E) (K := K) (ψ := ψ) hK hKm hψc hψcs u x)
                (smoothBCF (E := E) (K := K) (ψ := ψ) hK hKm hψc hψcs u y)
                ≤ ‖u‖ * ‖kx - ky‖ := hdist
            _ ≤ ‖u‖ * (mK * ε') := by
              exact mul_le_mul_of_nonneg_left hkdiff (norm_nonneg _)
            _ ≤ R * (mK * ε') := by
              have hmKε' : 0 ≤ mK * ε' := mul_nonneg hmK (le_of_lt hε'pos)
              exact mul_le_mul_of_nonneg_right hu_norm hmKε'
        have hRmkε' : R * (mK * ε') = ε2 := by
          have : R * mK * ε' = ε2 := by
            simpa [ε', mul_assoc] using hε'lt
          simpa [mul_assoc] using this
        have hle' :
            dist (smoothBCF (E := E) (K := K) (ψ := ψ) hK hKm hψc hψcs u x)
                (smoothBCF (E := E) (K := K) (ψ := ψ) hK hKm hψc hψcs u y) ≤ ε2 := by
          simpa [hRmkε'] using hle
        have hε2lt : ε2 < ε := by
          simpa [ε2] using half_lt_self hε
        have :
            dist (smoothBCF (E := E) (K := K) (ψ := ψ) hK hKm hψc hψcs u x)
                (smoothBCF (E := E) (K := K) (ψ := ψ) hK hKm hψc hψcs u y) < ε :=
          lt_of_le_of_lt hle' hε2lt
        simpa [hu_eq'] using this
    have H : Equicontinuous ((↑) : A → ↥(Kψ (K := K) (ψ := ψ)) → ℝ) := H'.equicontinuous
    -- Apply Arzelà–Ascoli.
    simpa [A, s] using
      (BoundedContinuousFunction.arzela_ascoli (α := ↥(Kψ (K := K) (ψ := ψ))) (β := ℝ)
        (s := s) hs A (fun f x hf => in_s f x hf) H)

end Volume

end

end L2Compactness
end Euclidean
end Sobolev
end FunctionalSpaces
end Analysis
end RellichKondrachov
end

section
-- module Solutions.OAIQ092_CC.Analysis_FunctionalSpaces_Sobolev_Euclidean_L2Compactness_Transfer
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/

/-!
# `L²` compactness criterion: transfer from `BCF` compactness to `L²` (Euclidean)

This file transfers the Arzelà–Ascoli compactness of the `BoundedContinuousFunction` packaging of
`smoothFun` on the compact set `K + tsupport ψ` to a compactness statement in `L²(volume)`.

## Main results

- `smoothL2_image_closedBall_isCompact`:
  For a compact set `K` and a continuous compactly supported kernel `ψ`, the family
  `{ smoothL2 ψ u | ‖u‖ ≤ R }` has compact closure in `L²(volume)`.

Tracking: Beads `lean-103.5.2.26.5.3.2.2.1.2`.
-/

namespace RellichKondrachov
namespace Analysis
namespace FunctionalSpaces
namespace Sobolev
namespace Euclidean
namespace L2Compactness

open scoped ENNReal MeasureTheory Topology Convolution Pointwise
open MeasureTheory Set

noncomputable section

section Volume

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

attribute [local instance] RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.L2Compactness.instMeasurableSpaceE_L2CompactnessTransfer
local instance instBorelSpaceE_L2CompactnessTransfer : BorelSpace E := ⟨rfl⟩
local instance instOpensMeasurableSpaceE_L2CompactnessTransfer : OpensMeasurableSpace E := by
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

variable {K : Set E} {ψ : E → ℝ}

local instance instMeasurableAddE_L2CompactnessTransfer_r1554e2_1 : MeasurableAdd E := by
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
local instance instMeasurableNegE_L2CompactnessTransfer_r1554e2_1 : MeasurableNeg E := by
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
theorem smoothL2_image_closedBall_isCompact (hK : IsCompact K) (hKm : MeasurableSet K)
    (hψc : Continuous ψ) (hψcs : HasCompactSupport ψ) {R : ℝ} (hR : 0 ≤ R) :
    IsCompact
        (closure
          (smoothL2 (E := E) (K := K) ψ hK hKm hψc hψcs '' Metric.closedBall (0 : _) R)) := by
  classical
  letI : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
  let s : Set E := Kψ (K := K) (ψ := ψ)
  have hs_compact : IsCompact s := isCompact_Kψ (K := K) (ψ := ψ) hK hψcs
  have hs : MeasurableSet s := hs_compact.measurableSet
  have hs_lt_top : (volume : Measure E) s < ∞ :=
    hs_compact.measure_lt_top (μ := (volume : Measure E))
  let μs : Measure E := (volume : Measure E).restrict s
  haveI : Fact ((volume : Measure E) s < ∞) := ⟨hs_lt_top⟩
  haveI : IsFiniteMeasure μs := by
    first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
  let mS : ℝ := (MeasureTheory.measureUnivNNReal μs) ^ ((2 : ℝ≥0∞).toReal⁻¹)
  have hmS : 0 ≤ mS := by
    have : 0 ≤ (MeasureTheory.measureUnivNNReal μs) := by simp
    exact Real.rpow_nonneg this _
  let U : Set (MeasureTheory.Lp ℝ (2 : ℝ≥0∞) (volume.restrict K)) :=
    Metric.closedBall (0 : _) R
  let A :
      Set (BoundedContinuousFunction (↥(Kψ (K := K) (ψ := ψ))) ℝ) :=
    smoothBCF (E := E) (K := K) (ψ := ψ) hK hKm hψc hψcs '' U
  let B : Set (E →₂[(volume : Measure E)] ℝ) :=
    smoothL2 (E := E) (K := K) ψ hK hKm hψc hψcs '' U
  have hA_compact : IsCompact (closure A) :=
    smoothBCF_image_closedBall_isCompact (E := E) (K := K) (ψ := ψ) hK hKm hψc hψcs (R := R) hR
  have hdist_smoothL2_le :
      ∀ u v : MeasureTheory.Lp ℝ (2 : ℝ≥0∞) (volume.restrict K),
        dist (smoothL2 (E := E) (K := K) ψ hK hKm hψc hψcs u)
            (smoothL2 (E := E) (K := K) ψ hK hKm hψc hψcs v) ≤
          mS *
            dist (smoothBCF (E := E) (K := K) (ψ := ψ) hK hKm hψc hψcs u)
                (smoothBCF (E := E) (K := K) (ψ := ψ) hK hKm hψc hψcs v) := by
    intro u v
    set Su :=
      smoothL2 (E := E) (K := K) ψ hK hKm hψc hψcs u
    set Sv :=
      smoothL2 (E := E) (K := K) ψ hK hKm hψc hψcs v
    set Bu :=
      smoothBCF (E := E) (K := K) (ψ := ψ) hK hKm hψc hψcs u
    set Bv :=
      smoothBCF (E := E) (K := K) (ψ := ψ) hK hKm hψc hψcs v
    have hBuBv : 0 ≤ ‖Bu - Bv‖ := norm_nonneg _
    -- Work on `F := Su - Sv` and restrict to the finite-measure set `s`.
    let F : (E →₂[(volume : Measure E)] ℝ) := Su - Sv
    let g : E → ℝ := fun x => (F : E → ℝ) x
    have hg : MeasureTheory.MemLp g (2 : ℝ≥0∞) (volume : Measure E) := MeasureTheory.Lp.memLp F
    have hg_restrict : MeasureTheory.MemLp g (2 : ℝ≥0∞) μs := hg.restrict s
    let Fs : MeasureTheory.Lp ℝ (2 : ℝ≥0∞) μs := hg_restrict.toLp g
    -- Show `Fs` is pointwise bounded by `‖Bu - Bv‖` on `μs`.
    have hF_ae :
        (g =ᵐ[μs] fun x : E =>
          smoothFun (E := E) (K := K) ψ u x -
            smoothFun (E := E) (K := K) ψ v x) := by
      have hsub :
          (F : E → ℝ) =ᵐ[(volume : Measure E)] (Su : E → ℝ) - (Sv : E → ℝ) := by
        simpa [F, g, Su, Sv] using
          (MeasureTheory.Lp.coeFn_sub (μ := (volume : Measure E)) Su Sv)
      have hu :
          (Su : E → ℝ) =ᵐ[(volume : Measure E)] smoothFun (E := E) (K := K) ψ u :=
        smoothL2_ae_eq (E := E) (K := K) (ψ := ψ) (hK := hK) (hKm := hKm) hψc hψcs u
      have hv :
          (Sv : E → ℝ) =ᵐ[(volume : Measure E)] smoothFun (E := E) (K := K) ψ v :=
        smoothL2_ae_eq (E := E) (K := K) (ψ := ψ) (hK := hK) (hKm := hKm) hψc hψcs v
      have hF :
          (F : E → ℝ) =ᵐ[(volume : Measure E)]
            fun x : E =>
              smoothFun (E := E) (K := K) ψ u x - smoothFun (E := E) (K := K) ψ v x := by
        exact hsub.trans (hu.sub hv)
      exact MeasureTheory.ae_restrict_of_ae (μ := (volume : Measure E)) (s := s) hF
    have hFs_ae : ((Fs : E → ℝ) =ᵐ[μs] g) := by
      simpa [Fs, g] using
        (MeasureTheory.MemLp.coeFn_toLp (μ := μs) (p := (2 : ℝ≥0∞)) (f := g) hg_restrict)
    have hbound :
        ∀ᵐ x ∂μs, ‖Fs x‖ ≤ ‖Bu - Bv‖ := by
      have hpoint :
          ∀ x : E, x ∈ s → ‖smoothFun (E := E) (K := K) ψ u x - smoothFun (E := E) (K := K) ψ v x‖ ≤
            ‖Bu - Bv‖ := by
        intro x hx
        let x' : ↥(Kψ (K := K) (ψ := ψ)) := ⟨x, hx⟩
        have hBu : Bu x' = smoothFun (E := E) (K := K) ψ u x := by
          simp [Bu, x']
        have hBv : Bv x' = smoothFun (E := E) (K := K) ψ v x := by
          simp [Bv, x']
        have : ‖(Bu - Bv) x'‖ ≤ ‖Bu - Bv‖ :=
          (Bu - Bv).norm_coe_le_norm x'
        simpa [hBu, hBv] using this
      filter_upwards
        [MeasureTheory.ae_restrict_mem (μ := (volume : Measure E)) hs,
          hFs_ae, hF_ae] with x hx hFs hF
      have := hpoint x hx
      -- rewrite through the AE equalities
      simpa [hFs, hF] using this
    have hnorm_Fs : ‖Fs‖ ≤ mS * ‖Bu - Bv‖ := by
      have := (MeasureTheory.Lp.norm_le_of_ae_bound (μ := μs) (p := (2 : ℝ≥0∞))
        (f := Fs) (hC := hBuBv) hbound)
      simpa [mS] using this
    -- Relate the `L²` norm on `volume` to the restricted norm on `μs` using extension-by-zero.
    have hsupport :
        ∀ x : E, x ∉ s →
          smoothFun (E := E) (K := K) ψ u x -
            smoothFun (E := E) (K := K) ψ v x = 0 := by
      intro x hx
      have hu_supp : Function.support (smoothFun (E := E) (K := K) ψ u) ⊆ s := by
        exact
          (support_smoothFun_subset_add_tsupport (E := E) (K := K) (ψ := ψ) u)
      have hv_supp : Function.support (smoothFun (E := E) (K := K) ψ v) ⊆ s := by
        exact
          (support_smoothFun_subset_add_tsupport (E := E) (K := K) (ψ := ψ) v)
      have hu0 : smoothFun (E := E) (K := K) ψ u x = 0 := by
        have : x ∉ Function.support (smoothFun (E := E) (K := K) ψ u) := fun hx' => hx (hu_supp hx')
        simpa [Function.support] using this
      have hv0 : smoothFun (E := E) (K := K) ψ v x = 0 := by
        have : x ∉ Function.support (smoothFun (E := E) (K := K) ψ v) := fun hx' => hx (hv_supp hx')
        simpa [Function.support] using this
      simp [hu0, hv0]
    have hF0 :
        ∀ᵐ x ∂(volume : Measure E), x ∉ s → g x = 0 := by
      have hF_ae_full :
          (g =ᵐ[(volume : Measure E)]
            fun x : E =>
              smoothFun (E := E) (K := K) ψ u x -
                smoothFun (E := E) (K := K) ψ v x) := by
        have hsub :
            (F : E → ℝ) =ᵐ[(volume : Measure E)] (Su : E → ℝ) - (Sv : E → ℝ) := by
          simpa [F, g, Su, Sv] using
            (MeasureTheory.Lp.coeFn_sub (μ := (volume : Measure E)) Su Sv)
        have hu :
            (Su : E → ℝ) =ᵐ[(volume : Measure E)] smoothFun (E := E) (K := K) ψ u :=
          smoothL2_ae_eq (E := E) (K := K) (ψ := ψ) (hK := hK) (hKm := hKm) hψc hψcs u
        have hv :
            (Sv : E → ℝ) =ᵐ[(volume : Measure E)] smoothFun (E := E) (K := K) ψ v :=
          smoothL2_ae_eq (E := E) (K := K) (ψ := ψ) (hK := hK) (hKm := hKm) hψc hψcs v
        have hF :
            (F : E → ℝ) =ᵐ[(volume : Measure E)]
              fun x : E =>
                smoothFun (E := E) (K := K) ψ u x - smoothFun (E := E) (K := K) ψ v x := by
          exact hsub.trans (hu.sub hv)
        simpa [g] using hF
      filter_upwards [hF_ae_full] with x hx
      intro hxnot
      have : smoothFun (E := E) (K := K) ψ u x - smoothFun (E := E) (K := K) ψ v x = 0 :=
        hsupport x hxnot
      simpa [hx] using this
    have hF_ind :
        (s.indicator g =ᵐ[(volume : Measure E)] g) := by
      filter_upwards [hF0] with x hx
      by_cases hxmem : x ∈ s
      · simp [g, hxmem]
      · have : g x = 0 := hx hxmem
        simp [g, hxmem, this]
    -- Conclude `‖F‖ = ‖Fs‖` using `extendByZeroₗᵢ` and the indicator identity.
    let Fext :
        MeasureTheory.Lp ℝ (2 : ℝ≥0∞) (volume : Measure E) :=
      (MeasureTheory.Lp.extendByZeroₗᵢ (μ := (volume : Measure E)) (E := ℝ) (p := (2 : ℝ≥0∞))
        (s := s) hs) Fs
    have hFext_ae :
        ((Fext : MeasureTheory.Lp ℝ (2 : ℝ≥0∞) (volume : Measure E)) :
            E → ℝ) =ᵐ[(volume : Measure E)]
          s.indicator fun x : E => (Fs : E → ℝ) x := by
      simpa [Fext] using
        (MeasureTheory.Lp.extendByZeroₗᵢ_ae_eq
          (μ := (volume : Measure E)) (p := (2 : ℝ≥0∞))
          (s := s) hs Fs)
    have hFs_on :
        ∀ᵐ x ∂(volume : Measure E), x ∈ s → (Fs : E → ℝ) x = g x := by
      -- rewrite the AE equality `Fs = g` on the restricted measure as an implication on `volume`
      have := (MeasureTheory.ae_restrict_iff' (μ := (volume : Measure E)) (s := s) hs).1 hFs_ae
      simpa [g] using this
    have hindicator :
        (s.indicator (fun x : E => (Fs : E → ℝ) x) =ᵐ[(volume : Measure E)] s.indicator g) := by
      filter_upwards [hFs_on] with x hx
      by_cases hxmem : x ∈ s
      · simp [hxmem, hx hxmem]
      · simp [hxmem]
    have hFext_ae' :
        (Fext : E → ℝ) =ᵐ[(volume : Measure E)] g := by
      exact hFext_ae.trans (hindicator.trans hF_ind)
    have hFext_eq : Fext = F := by
      refine MeasureTheory.Lp.ext ?_
      simpa [g, F] using hFext_ae'
    have hnorm_F : ‖F‖ ≤ mS * ‖Bu - Bv‖ := by
      -- use `‖F‖ = ‖Fs‖` via the isometry.
      have hnorm_ext : ‖Fext‖ = ‖Fs‖ := by
        simp [Fext]
      -- `Fext = F` and `Fs` is bounded.
      have : ‖Fext‖ ≤ mS * ‖Bu - Bv‖ := by
        simpa [hnorm_ext] using hnorm_Fs
      simpa [hFext_eq] using this
    -- Convert to the `dist` statement.
    simpa [Su, Sv, Bu, Bv, F, dist_eq_norm, mS, mul_assoc] using hnorm_F
  have hTB_B : TotallyBounded B := by
    -- Use a finite `BCF` ε-net for `A` with centers in the image, then transfer to `L²`.
    rw [Metric.totallyBounded_iff]
    intro ε hε
    by_cases hmS0 : mS = 0
    ·
      let c : (E →₂[(volume : Measure E)] ℝ) :=
        smoothL2 (E := E) (K := K) ψ hK hKm hψc hψcs (0 : _)
      refine ⟨{c}, by simp [c], ?_⟩
      intro w hw
      rcases hw with ⟨u, huU, rfl⟩
      have hle :=
        hdist_smoothL2_le u (0 : MeasureTheory.Lp ℝ (2 : ℝ≥0∞) (volume.restrict K))
      have hdist0 :
          dist (smoothL2 (E := E) (K := K) ψ hK hKm hψc hψcs u)
              c = 0 := by
        have :
            dist (smoothL2 (E := E) (K := K) ψ hK hKm hψc hψcs u) c ≤ 0 := by
          simpa [c, hmS0] using hle
        exact le_antisymm this dist_nonneg
      refine mem_iUnion.2 ?_
      refine ⟨c, mem_iUnion.2 ?_⟩
      refine ⟨by simp, ?_⟩
      -- membership in the open ball follows from `dist = 0` and `ε > 0`
      simpa [Metric.mem_ball, hdist0] using hε
    · have hmSpos : 0 < mS := lt_of_le_of_ne hmS (Ne.symm hmS0)
      let δ : ℝ := ε / mS
      have hδpos : 0 < δ := div_pos hε hmSpos
      obtain ⟨t, htAsub, htFin, htCover⟩ :=
        exists_finite_cover_balls_of_isCompact_closure (s := A) (ε := δ) hA_compact hδpos
      let tFin : Finset (BoundedContinuousFunction (↥(Kψ (K := K) (ψ := ψ))) ℝ) :=
        htFin.toFinset
      have htFin_mem :
          ∀ {f : BoundedContinuousFunction (↥(Kψ (K := K) (ψ := ψ))) ℝ}, f ∈ tFin ↔ f ∈ t := by
        intro f
        simp [tFin, htFin.mem_toFinset (a := f)]
      let ι : Type _ := { f // f ∈ tFin }
      have hrep :
          ∀ f : ι,
            ∃ u : MeasureTheory.Lp ℝ (2 : ℝ≥0∞) (volume.restrict K),
              u ∈ U ∧
                smoothBCF (E := E) (K := K) (ψ := ψ) hK hKm hψc hψcs u = f.1 := by
        intro f
        have hf_t : f.1 ∈ t := (htFin_mem (f := f.1)).1 f.2
        have hfA : f.1 ∈ A := htAsub hf_t
        rcases hfA with ⟨u, huU, huEq⟩
        exact ⟨u, huU, huEq⟩
      choose uOf huOfU huOfEq using hrep
      let tL2 : Set (E →₂[(volume : Measure E)] ℝ) :=
        Set.range fun f : ι => smoothL2 (E := E) (K := K) ψ hK hKm hψc hψcs (uOf f)
      have htL2_fin : tL2.Finite := Set.finite_range _
      refine ⟨tL2, htL2_fin, ?_⟩
      intro w hw
      rcases hw with ⟨u, huU, rfl⟩
      have hBu : (smoothBCF (E := E) (K := K) (ψ := ψ) hK hKm hψc hψcs u) ∈ A := by
        exact ⟨u, huU, rfl⟩
      have : smoothBCF (E := E) (K := K) (ψ := ψ) hK hKm hψc hψcs u ∈ ⋃ x ∈ t, Metric.ball x δ :=
        htCover hBu
      rcases mem_iUnion.1 this with ⟨f, hf⟩
      rcases mem_iUnion.1 hf with ⟨hf_t, hf_ball⟩
      have hf_tFin : f ∈ tFin := (htFin_mem (f := f)).2 hf_t
      let f' : ι := ⟨f, hf_tFin⟩
      have hf_ball' :
          dist (smoothBCF (E := E) (K := K) (ψ := ψ) hK hKm hψc hψcs u) f < δ := hf_ball
      have hdist :
          dist (smoothL2 (E := E) (K := K) ψ hK hKm hψc hψcs u)
              (smoothL2 (E := E) (K := K) ψ hK hKm hψc hψcs (uOf f')) < ε := by
        have hle := hdist_smoothL2_le u (uOf f')
        have hf_eq :
            smoothBCF (E := E) (K := K) (ψ := ψ) hK hKm hψc hψcs (uOf f') = f := by
          simpa [f'] using huOfEq f'
        have hdist' :
            dist (smoothBCF (E := E) (K := K) (ψ := ψ) hK hKm hψc hψcs u)
                (smoothBCF (E := E) (K := K) (ψ := ψ) hK hKm hψc hψcs (uOf f')) < δ := by
          simpa [hf_eq] using hf_ball'
        have : mS * dist (smoothBCF (E := E) (K := K) (ψ := ψ) hK hKm hψc hψcs u)
                (smoothBCF (E := E) (K := K) (ψ := ψ) hK hKm hψc hψcs (uOf f')) < ε := by
          have : mS * dist (smoothBCF (E := E) (K := K) (ψ := ψ) hK hKm hψc hψcs u)
                  (smoothBCF (E := E) (K := K) (ψ := ψ) hK hKm hψc hψcs (uOf f')) < mS * δ := by
            exact mul_lt_mul_of_pos_left hdist' hmSpos
          have hmul : mS * δ = ε := by
            have hmS_ne : mS ≠ 0 := ne_of_gt hmSpos
            calc
              mS * δ = mS * (ε / mS) := by simp [δ]
              _ = mS * ε / mS := (mul_div_assoc mS ε mS).symm
              _ = ε := by simpa using (mul_div_cancel_left₀ ε hmS_ne)
          simpa [hmul] using this
        exact lt_of_le_of_lt hle this
      refine mem_iUnion.2 ?_
      refine ⟨smoothL2 (E := E) (K := K) ψ hK hKm hψc hψcs (uOf f'), ?_⟩
      refine mem_iUnion.2 ?_
      refine ⟨?_, hdist⟩
      -- show the chosen center lies in `tL2`
      exact ⟨f', rfl⟩
  -- Compactness follows from total boundedness + completeness of `L²`.
  have hTB_closure : TotallyBounded (closure B) := hTB_B.closure
  have hcomplete : IsComplete (closure B) := isClosed_closure.isComplete
  have hcompact_closure : IsCompact (closure B) :=
    isCompact_iff_totallyBounded_isComplete.2 ⟨hTB_closure, hcomplete⟩
  simpa [B, U] using hcompact_closure

end Volume

end

end L2Compactness
end Euclidean
end Sobolev
end FunctionalSpaces
end Analysis
end RellichKondrachov
end

section
-- module Solutions.OAIQ092_CC.Analysis_FunctionalSpaces_Sobolev_Euclidean_L2Compactness_FrechetKolmogorov
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/

/-!
# `L²` compactness criterion: Fréchet–Kolmogorov (Euclidean, compact support case)

This file packages the final “precompactness via smoothing” step behind the Euclidean `L²`
compactness criterion used by the Rellich–Kondrachov stack:

- the **smoothing operator** `smoothL2 ψ` has compact image on `Metric.closedBall 0 R`;
- the **approximation inequality** bounds `‖smoothL2 ψ u - extendByZeroL2 u‖` by a translation
  error.

We state the criterion at the level needed by the project: families of `L²` functions with common
compact support (modeled as `Lp ℝ 2 (volume.restrict K)` and embedded into `L²(volume)` via
`extendByZeroL2`).

## Main results

- `norm_smoothL2_sub_extendByZeroL2_le_of_integral_translateL2_sub_extendByZeroL2_le`:
  if the translation error averaged against `kernelMeasure ψ` is ≤ `η²`, then smoothing approximates
  `extendByZeroL2` within `η`.
- `totallyBounded_extendByZeroL2_image_of_forall_exists_translationIntegral_small`:
  if a bounded family admits, at every scale `ε`, a kernel `ψ` for which the above translation error
  is uniformly small, then the embedded family is totally bounded in `L²(volume)`.
- `isCompact_closure_extendByZeroL2_image_of_forall_exists_translationIntegral_small`:
  the corresponding compact-closure statement.

Tracking: Beads `lean-103.5.2.26.5.3.2.2.3`.
-/

namespace RellichKondrachov
namespace Analysis
namespace FunctionalSpaces
namespace Sobolev
namespace Euclidean
namespace L2Compactness

open scoped ENNReal MeasureTheory Topology Convolution Pointwise
open MeasureTheory Set

noncomputable section

section Volume

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

variable {K : Set E} {ψ : E → ℝ}

attribute [local instance] RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.L2Compactness.instMeasurableSpaceE_L2CompactnessFrechetKolmogorov
attribute [local instance] RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.L2Compactness.instBorelSpaceE_L2CompactnessFrechetKolmogorov
local instance instOpensMeasurableSpaceE_L2CompactnessFrechetKolmogorov_r1554e2_1 :
    OpensMeasurableSpace E := by infer_instance
local instance instMeasurableAddE_L2CompactnessFrechetKolmogorov_r1554e2_1 : MeasurableAdd E := by
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
local instance instMeasurableNegE_L2CompactnessFrechetKolmogorov_r1554e2_1 : MeasurableNeg E := by
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
lemma norm_smoothL2_sub_extendByZeroL2_le_of_integral_translateL2_sub_extendByZeroL2_le
    (hK : IsCompact K) (hKm : MeasurableSet K)
    (hψc : Continuous ψ) (hψcs : HasCompactSupport ψ) (hψ0 : ∀ x, 0 ≤ ψ x)
    (hψint : ∫ x, ψ x ∂(volume : Measure E) = 1) {η : ℝ} (hη : 0 ≤ η)
    (u : MeasureTheory.Lp ℝ (2 : ℝ≥0∞) (volume.restrict K))
    (htrans :
      ∫ t,
          ‖(translateL2 (μ := (volume : Measure E)) (-t))
                (extendByZeroL2 (E := E) (K := K) hKm u)
              - extendByZeroL2 (E := E) (K := K) hKm u‖ ^ 2
        ∂kernelMeasure (E := E) ψ ≤ η ^ 2) :
    ‖smoothL2 (E := E) (K := K) ψ hK hKm hψc hψcs u
        - extendByZeroL2 (E := E) (K := K) hKm u‖ ≤ η := by
  have hsq :
      ‖smoothL2 (E := E) (K := K) ψ hK hKm hψc hψcs u
            - extendByZeroL2 (E := E) (K := K) hKm u‖ ^ 2 ≤ η ^ 2 := by
    refine (le_trans ?_ htrans)
    simpa using
      norm_sq_smoothL2_sub_extendByZeroL2_le_integral_norm_sq_translateL2_sub_extendByZeroL2
        (E := E) (K := K) (ψ := ψ) (hK := hK) (hKm := hKm) hψc hψcs hψ0 hψint u
  exact (sq_le_sq₀ (norm_nonneg _) hη).1 hsq

theorem totallyBounded_extendByZeroL2_image_of_forall_exists_translationIntegral_small
    (hK : IsCompact K) (hKm : MeasurableSet K) {R : ℝ} (hR : 0 ≤ R)
    {A : Set (MeasureTheory.Lp ℝ (2 : ℝ≥0∞) (volume.restrict K))}
    (hA : A ⊆ Metric.closedBall (0 : MeasureTheory.Lp ℝ (2 : ℝ≥0∞) (volume.restrict K)) R)
    (hApprox :
      ∀ ε : ℝ, 0 < ε →
        ∃ ψ : E → ℝ, Continuous ψ ∧ HasCompactSupport ψ ∧ (∀ x, 0 ≤ ψ x) ∧
          (∫ x, ψ x ∂(volume : Measure E) = 1) ∧
          ∀ u ∈ A,
            ∫ t,
                ‖(translateL2 (μ := (volume : Measure E)) (-t))
                      (extendByZeroL2 (E := E) (K := K) hKm u)
                    - extendByZeroL2 (E := E) (K := K) hKm u‖ ^ 2
              ∂kernelMeasure (E := E) ψ ≤ (ε / 2) ^ 2) :
    TotallyBounded (extendByZeroL2 (E := E) (K := K) hKm '' A) := by
  classical
  -- Use the finite `ε`-net characterization of total boundedness.
  refine (Metric.totallyBounded_iff).2 ?_
  intro ε hε
  have hε2 : 0 < ε / 2 := by linarith
  rcases hApprox ε hε with ⟨ψ, hψc, hψcs, hψ0, hψint, htrans⟩
  let B : Set (E →₂[(volume : Measure E)] ℝ) :=
    smoothL2 (E := E) (K := K) ψ hK hKm hψc hψcs '' Metric.closedBall (0 : _) R
  have hB_compact : IsCompact (closure B) :=
    smoothL2_image_closedBall_isCompact (E := E) (K := K) (ψ := ψ) hK hKm hψc hψcs (R := R) hR
  have hB_tot : TotallyBounded B :=
    (totallyBounded_closure).1 hB_compact.totallyBounded
  rcases Metric.finite_approx_of_totallyBounded hB_tot (ε / 2) hε2 with ⟨t, htB, htfin, hBcover⟩
  refine ⟨t, htfin, ?_⟩
  intro x hx
  rcases hx with ⟨u, huA, rfl⟩
  have huR : u ∈ Metric.closedBall (0 : _) R := hA huA
  have hSu_mem : smoothL2 (E := E) (K := K) ψ hK hKm hψc hψcs u ∈ B := ⟨u, huR, rfl⟩
  have hSu_cover :
      smoothL2 (E := E) (K := K) ψ hK hKm hψc hψcs u ∈
        ⋃ y, ⋃ (_ : y ∈ t), Metric.ball y (ε / 2) :=
    hBcover hSu_mem
  rcases Set.mem_iUnion.1 hSu_cover with ⟨y, hy⟩
  rcases Set.mem_iUnion.1 hy with ⟨hyT, hyBall⟩
  have hyDist : dist (smoothL2 (E := E) (K := K) ψ hK hKm hψc hψcs u) y < ε / 2 := by
    simpa [Metric.ball, Set.mem_setOf_eq] using hyBall
  have hdist_smooth_ext :
      dist (extendByZeroL2 (E := E) (K := K) hKm u)
          (smoothL2 (E := E) (K := K) ψ hK hKm hψc hψcs u) ≤ ε / 2 := by
    have hη : 0 ≤ ε / 2 := le_of_lt hε2
    have hnorm :
        ‖smoothL2 (E := E) (K := K) ψ hK hKm hψc hψcs u
            - extendByZeroL2 (E := E) (K := K) hKm u‖ ≤ ε / 2 :=
      norm_smoothL2_sub_extendByZeroL2_le_of_integral_translateL2_sub_extendByZeroL2_le
        (E := E) (K := K) (ψ := ψ) hK hKm hψc hψcs hψ0 hψint (η := ε / 2) hη u (htrans u huA)
    -- Switch to `dist` with the argument order used by `dist_triangle`.
    have hdist :
        dist (smoothL2 (E := E) (K := K) ψ hK hKm hψc hψcs u)
            (extendByZeroL2 (E := E) (K := K) hKm u) ≤ ε / 2 := by
      simpa [dist_eq_norm] using hnorm
    simpa [dist_comm] using hdist
  have hxDist : dist (extendByZeroL2 (E := E) (K := K) hKm u) y < ε := by
    have htri :=
      dist_triangle (extendByZeroL2 (E := E) (K := K) hKm u)
        (smoothL2 (E := E) (K := K) ψ hK hKm hψc hψcs u) y
    have hlt :
        dist (extendByZeroL2 (E := E) (K := K) hKm u)
              (smoothL2 (E := E) (K := K) ψ hK hKm hψc hψcs u)
            + dist (smoothL2 (E := E) (K := K) ψ hK hKm hψc hψcs u) y
          < ε / 2 + ε / 2 :=
      add_lt_add_of_le_of_lt hdist_smooth_ext hyDist
    have htmp :
        dist (extendByZeroL2 (E := E) (K := K) hKm u) y < ε / 2 + ε / 2 :=
      lt_of_le_of_lt htri hlt
    simpa [add_halves ε] using htmp
  have hxBall : extendByZeroL2 (E := E) (K := K) hKm u ∈ Metric.ball y ε := by
    simpa [Metric.ball, Set.mem_setOf_eq] using hxDist
  exact Set.mem_iUnion.2 ⟨y, Set.mem_iUnion.2 ⟨hyT, hxBall⟩⟩

theorem isCompact_closure_extendByZeroL2_image_of_forall_exists_translationIntegral_small
    (hK : IsCompact K) (hKm : MeasurableSet K) {R : ℝ} (hR : 0 ≤ R)
    {A : Set (MeasureTheory.Lp ℝ (2 : ℝ≥0∞) (volume.restrict K))}
    (hA : A ⊆ Metric.closedBall (0 : MeasureTheory.Lp ℝ (2 : ℝ≥0∞) (volume.restrict K)) R)
    (hApprox :
      ∀ ε : ℝ, 0 < ε →
        ∃ ψ : E → ℝ, Continuous ψ ∧ HasCompactSupport ψ ∧ (∀ x, 0 ≤ ψ x) ∧
          (∫ x, ψ x ∂(volume : Measure E) = 1) ∧
          ∀ u ∈ A,
            ∫ t,
                ‖(translateL2 (μ := (volume : Measure E)) (-t))
                      (extendByZeroL2 (E := E) (K := K) hKm u)
                    - extendByZeroL2 (E := E) (K := K) hKm u‖ ^ 2
              ∂kernelMeasure (E := E) ψ ≤ (ε / 2) ^ 2) :
    IsCompact (closure (extendByZeroL2 (E := E) (K := K) hKm '' A)) := by
  have ht :
      TotallyBounded (extendByZeroL2 (E := E) (K := K) hKm '' A) :=
    totallyBounded_extendByZeroL2_image_of_forall_exists_translationIntegral_small
      (E := E) (K := K) hK hKm hR hA hApprox
  exact (ht.closure).isCompact_of_isClosed isClosed_closure

end Volume

end

end L2Compactness
end Euclidean
end Sobolev
end FunctionalSpaces
end Analysis
end RellichKondrachov
end

section
-- module Solutions.OAIQ092_CC.Analysis_FunctionalSpaces_Sobolev_Euclidean_L2Compactness_Kernels
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/

/-!
# `L²` compactness criterion: existence of small-support probability kernels (Euclidean)

This file provides a “kernel factory” for the Euclidean Fréchet–Kolmogorov / Riesz–Kolmogorov
criterion: for any radius `δ > 0`, produce a continuous compactly supported function `ψ : E → ℝ`
such that:

- `ψ ≥ 0`,
- `tsupport ψ ⊆ Metric.ball 0 δ`,
- `∫ ψ = 1` (so `kernelMeasure ψ` is a probability measure).

The construction uses mathlib’s `exists_smooth_tsupport_subset` bump-function lemma and normalizes
by its (positive) integral.

Tracking: Beads `lean-103.5.2.26.5.3.2.2.5`.
-/

namespace RellichKondrachov
namespace Analysis
namespace FunctionalSpaces
namespace Sobolev
namespace Euclidean
namespace L2Compactness

open scoped ENNReal MeasureTheory Topology
open MeasureTheory Set

noncomputable section

section Volume

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

attribute [local instance] RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.L2Compactness.instMeasurableSpaceE_L2CompactnessKernels
attribute [local instance] RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.L2Compactness.instBorelSpaceE_L2CompactnessKernels
local instance instOpensMeasurableSpaceE_L2CompactnessKernels : OpensMeasurableSpace E := by
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

/-- For any `δ > 0`, there exists a continuous compactly supported kernel `ψ` supported in
`Metric.ball 0 δ`, with `ψ ≥ 0` and `∫ ψ = 1` (w.r.t. Lebesgue measure). -/
theorem exists_kernel_tsupport_subset_ball_integral_eq_one {δ : ℝ} (hδ : 0 < δ) :
    ∃ ψ : E → ℝ, Continuous ψ ∧ HasCompactSupport ψ ∧ (∀ x, 0 ≤ ψ x) ∧
      (∫ x, ψ x ∂(volume : Measure E) = 1) ∧ tsupport ψ ⊆ Metric.ball (0 : E) δ := by
  classical
  -- Start from a smooth bump supported in `ball 0 δ` with value `1` at `0`.
  have hs : (Metric.ball (0 : E) δ) ∈ 𝓝 (0 : E) := Metric.ball_mem_nhds _ hδ
  rcases exists_contDiff_tsupport_subset (n := ⊤)
    (E := E) (s := Metric.ball (0 : E) δ) (x := (0 : E)) hs with
    ⟨f, hf_tsupp, hf_cs, hf_smooth, hf_range, hf0⟩
  have hf_cont : Continuous f := hf_smooth.continuous
  have hf_nonneg : ∀ x, 0 ≤ f x := by
    intro x
    have hx : f x ∈ Set.Icc (0 : ℝ) 1 := hf_range ⟨x, rfl⟩
    exact hx.1
  have hf0_ne : f (0 : E) ≠ 0 := by
    -- `f 0 = 1`.
    simp [hf0]
  -- The integral is strictly positive (Lebesgue is an open-positive measure).
  have hIpos :
      0 < ∫ x, f x ∂(volume : Measure E) := by
    simpa using
      (Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero (μ := (volume : Measure E))
        hf_cont hf_cs hf_nonneg hf0_ne)
  set I : ℝ := ∫ x, f x ∂(volume : Measure E)
  have hI0 : I ≠ 0 := ne_of_gt hIpos
  have hIpos' : 0 < I := by simpa [I] using hIpos
  -- Normalize: `ψ = I⁻¹ • f`.
  let ψ : E → ℝ := fun x => I⁻¹ * f x
  have hψc : Continuous ψ := by
    exact (continuous_const.mul hf_cont)
  have hψcs : HasCompactSupport ψ := by
    exact
      (HasCompactSupport.smul_left (f := fun _x : E => I⁻¹) (f' := f) hf_cs)
  have hψ0 : ∀ x, 0 ≤ ψ x := by
    intro x
    have hInv : 0 ≤ I⁻¹ := by
      have : 0 ≤ I := le_of_lt hIpos'
      simpa using inv_nonneg.2 this
    simpa [ψ] using mul_nonneg hInv (hf_nonneg x)
  have hψint : ∫ x, ψ x ∂(volume : Measure E) = 1 := by
    have : (∫ x, ψ x ∂(volume : Measure E)) = I⁻¹ * I := by
      -- Pull out the constant scalar.
      simpa [ψ, I] using
        (MeasureTheory.integral_const_mul (μ := (volume : Measure E)) (r := I⁻¹) (f := f))
    simp [this, hI0]
  have hψ_tsupp : tsupport ψ ⊆ Metric.ball (0 : E) δ := by
    -- Scaling does not enlarge topological support; use the bump support inclusion.
    have hsub : tsupport ψ ⊆ tsupport f := by
      simpa [ψ, smul_eq_mul] using (tsupport_smul_subset_right (f := fun _x : E => I⁻¹) (g := f))
    exact hsub.trans hf_tsupp
  exact ⟨ψ, hψc, hψcs, hψ0, hψint, hψ_tsupp⟩

end Volume

end

end L2Compactness
end Euclidean
end Sobolev
end FunctionalSpaces
end Analysis
end RellichKondrachov
end

section
-- module Solutions.OAIQ092_CC.Analysis_FunctionalSpaces_Sobolev_Euclidean_L2Compactness_TranslationIntegral
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/

/-!
# `L²` compactness criterion: bounding the translation-integral by a translation modulus

This file provides a small but crucial bridge lemma used to connect a uniform translation modulus
on `L²(volume)` with the `kernelMeasure` translation-integral bound appearing in the
approximation-identity estimate.

The core observation is that if `ψ` is supported in a neighborhood where the translation modulus is
≤ `η`, then the averaged squared translation error against the probability measure
`kernelMeasure ψ` is ≤ `η²`.

Tracking: Beads `lean-103.5.2.26.5.3.2.2.4`.
-/

namespace RellichKondrachov
namespace Analysis
namespace FunctionalSpaces
namespace Sobolev
namespace Euclidean
namespace L2Compactness

open scoped ENNReal MeasureTheory Topology
open MeasureTheory Set

noncomputable section

section Volume

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

attribute [local instance] RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.L2Compactness.instMeasurableSpaceE_L2CompactnessTranslationIntegral
attribute [local instance] RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.L2Compactness.instBorelSpaceE_L2CompactnessTranslationIntegral
local instance instOpensMeasurableSpaceE_L2CompactnessTranslationIntegral :
    OpensMeasurableSpace E := by infer_instance

variable {ψ : E → ℝ}

local instance instMeasurableAddE_L2CompactnessTranslationIntegral_r1554e2_1 : MeasurableAdd E := by
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
local instance instMeasurableNegE_L2CompactnessTranslationIntegral_r1554e2_1 : MeasurableNeg E := by
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
private lemma kernelMeasure_compl_ball_eq_zero_of_tsupport_subset {δ : ℝ}
    (hψsupp : tsupport ψ ⊆ Metric.ball (0 : E) δ) :
    kernelMeasure (E := E) ψ ((Metric.ball (0 : E) δ)ᶜ) = 0 := by
  classical
  have hψzero : ∀ x : E, x ∈ (Metric.ball (0 : E) δ)ᶜ → ψ x = 0 := by
    intro x hx
    have hx' : x ∉ tsupport ψ := by
      intro hx_ts
      exact hx (hψsupp hx_ts)
    exact image_eq_zero_of_notMem_tsupport (f := ψ) hx'
  have hmeas : MeasurableSet ((Metric.ball (0 : E) δ)ᶜ) :=
    (measurableSet_ball : MeasurableSet (Metric.ball (0 : E) δ)).compl
  have hEq :
      Set.EqOn (fun x : E => ENNReal.ofReal (ψ x)) 0 ((Metric.ball (0 : E) δ)ᶜ) := by
    intro x hx
    simp [hψzero x hx]
  -- Expand `kernelMeasure` and note the density is identically `0` on the set.
  simp [kernelMeasure, MeasureTheory.withDensity_apply, hmeas,
    MeasureTheory.setLIntegral_eq_zero
      (μ := (volume : Measure E))
      (s := (Metric.ball (0 : E) δ)ᶜ) hmeas hEq]

theorem integral_norm_sq_translateL2_sub_le_sq_of_tsupport_subset_ball
    (hψc : Continuous ψ) (hψcs : HasCompactSupport ψ) (hψ0 : ∀ x, 0 ≤ ψ x)
    (hψint : ∫ x, ψ x ∂(volume : Measure E) = 1)
    {δ η : ℝ} (hη : 0 ≤ η) (hψsupp : tsupport ψ ⊆ Metric.ball (0 : E) δ)
    (F : (E →₂[(volume : Measure E)] ℝ))
    (hmod :
      ∀ t : E, t ∈ Metric.ball (0 : E) δ →
        ‖(translateL2 (μ := (volume : Measure E)) (-t)) F - F‖ ≤ η) :
    ∫ t,
        ‖(translateL2 (μ := (volume : Measure E)) (-t)) F - F‖ ^ 2
      ∂kernelMeasure (E := E) ψ ≤ η ^ 2 := by
  classical
  let μ : Measure E := kernelMeasure (E := E) ψ
  haveI : MeasureTheory.IsProbabilityMeasure μ :=
    ⟨kernelMeasure_univ (E := E) (ψ := ψ) hψc hψcs hψ0 hψint⟩
  have hμzero : μ ((Metric.ball (0 : E) δ)ᶜ) = 0 := by
    simpa [μ] using kernelMeasure_compl_ball_eq_zero_of_tsupport_subset (E := E) (ψ := ψ) hψsupp
  have hAE_ball : (Metric.ball (0 : E) δ) ∈ MeasureTheory.ae μ :=
    (MeasureTheory.mem_ae_iff.2 hμzero)
  -- On `Metric.ball 0 δ`, the squared translation error is bounded by `η²`.
  have hAE_bound :
      ∀ᵐ t : E ∂μ,
        ‖‖(translateL2 (μ := (volume : Measure E)) (-t)) F - F‖ ^ 2‖ ≤ η ^ 2 := by
    filter_upwards [hAE_ball] with t ht
    have hle : ‖(translateL2 (μ := (volume : Measure E)) (-t)) F - F‖ ≤ η := hmod t ht
    have hsq :
        ‖(translateL2 (μ := (volume : Measure E)) (-t)) F - F‖ ^ 2 ≤ η ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) hη).2 hle
    have hnonneg : 0 ≤ ‖(translateL2 (μ := (volume : Measure E)) (-t)) F - F‖ ^ 2 :=
      sq_nonneg _
    have hηnonneg : 0 ≤ η ^ 2 := sq_nonneg _
    simpa [Real.norm_eq_abs, abs_of_nonneg hnonneg, abs_of_nonneg hηnonneg] using hsq
  have hnorm_int :
      ‖∫ t,
            ‖(translateL2 (μ := (volume : Measure E)) (-t)) F - F‖ ^ 2
          ∂μ‖ ≤ η ^ 2 * μ.real Set.univ := by
    simpa using
      (MeasureTheory.norm_integral_le_of_norm_le_const (μ := μ)
        (f := fun t : E => ‖(translateL2 (μ := (volume : Measure E)) (-t)) F - F‖ ^ 2)
        (C := η ^ 2) hAE_bound)
  have hμreal : μ.real Set.univ = 1 := by
    -- `μ` is a probability measure.
    simp [MeasureTheory.measureReal_def]
  have hnonneg_int :
      0 ≤ ∫ t,
            ‖(translateL2 (μ := (volume : Measure E)) (-t)) F - F‖ ^ 2
          ∂μ := by
    refine MeasureTheory.integral_nonneg ?_
    intro t
    exact sq_nonneg _
  -- Use `|∫ f| = ∫ f` for a nonnegative integrand.
  have habs :
      |∫ t,
            ‖(translateL2 (μ := (volume : Measure E)) (-t)) F - F‖ ^ 2
          ∂μ| ≤ η ^ 2 := by
    have := hnorm_int
    -- Replace `‖·‖` by `abs` in `ℝ` and simplify `μ.real univ = 1`.
    simpa [Real.norm_eq_abs, hμreal, mul_one] using this
  simpa [abs_of_nonneg hnonneg_int, μ] using habs

end Volume

end

end L2Compactness
end Euclidean
end Sobolev
end FunctionalSpaces
end Analysis
end RellichKondrachov
end

section
-- module Solutions.OAIQ092_CC.Analysis_FunctionalSpaces_Sobolev_Euclidean_TranslationEstimate
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/

/-!
# `RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.TranslationEstimate`

Pointwise translation estimates for `C¹_c` functions on Euclidean spaces.

This file provides the key analytic inequality used later in the Euclidean Rellich step:
translation differences are controlled by the `L²`-gradient.

At this stage we only prove *pointwise* inequalities along the segment `t ↦ x + t • a`.
The measure-theoretic lifting to `L²` is tracked separately under `lean-103.5.2.26.5.3.2.3`.
-/

namespace RellichKondrachov
namespace Analysis
namespace FunctionalSpaces
namespace Sobolev
namespace Euclidean

open scoped ENNReal MeasureTheory Topology
open MeasureTheory Set

section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

attribute [local instance] RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.instMeasurableSpaceE_SobolevEuclideanTranslationEstimate
local instance instBorelSpaceE_SobolevEuclideanTranslationEstimate :
    BorelSpace E := ⟨rfl⟩
local instance instOpensMeasurableSpaceE_SobolevEuclideanTranslationEstimate :
    OpensMeasurableSpace E := by
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

/-! ## Derivative along a translated line -/

lemma hasDerivAt_line (x a : E) (t : ℝ) :
    HasDerivAt (line (x := x) (a := a)) a t := by
  -- `t ↦ t • a` has derivative `a`, and adding the constant `x` preserves the derivative.
  have hsmul : HasDerivAt (fun t : ℝ => t • a) a t := by
    simpa [one_smul] using (hasDerivAt_id t).smul_const a
  exact HasDerivAt.const_add x hsmul

lemma hasDerivAt_comp_line
    {f : E → ℝ} (hf : ContDiff ℝ 1 f) (x a : E) (t : ℝ) :
    HasDerivAt (fun t => f (line (x := x) (a := a) t))
      (fderiv ℝ f (line (x := x) (a := a) t) a) t := by
  have hf' : HasFDerivAt f (fderiv ℝ f (line (x := x) (a := a) t)) (line (x := x) (a := a) t) :=
    (hf.differentiable one_ne_zero).differentiableAt.hasFDerivAt
  exact
    HasFDerivAt.comp_hasDerivAt_of_eq t hf' (hasDerivAt_line (x := x) (a := a) t) rfl

lemma deriv_comp_line {f : E → ℝ} (hf : ContDiff ℝ 1 f) (x a : E) (t : ℝ) :
    deriv (fun t => f (line (x := x) (a := a) t)) t =
      fderiv ℝ f (line (x := x) (a := a) t) a :=
  (hasDerivAt_comp_line (hf := hf) (x := x) (a := a) t).deriv

/-! ## Pointwise translation bound via the gradient -/

section

variable [CompleteSpace E]

lemma enorm_fderiv_apply_le_enorm_grad_mul (f : E → ℝ) (x a : E) :
    ‖fderiv ℝ f x a‖ₑ ≤ ‖grad (E := E) f x‖ₑ * ‖a‖ₑ := by
  -- Use the operator norm bound, then identify `‖fderiv‖` with `‖grad‖` via the Riesz isometry.
  have h₁ :
      ‖fderiv ℝ f x a‖ₑ ≤ ‖fderiv ℝ f x‖ₑ * ‖a‖ₑ :=
    (ContinuousLinearMap.le_opNorm_enorm (f := fderiv ℝ f x) a)
  have h₂ : ‖grad (E := E) f x‖ₑ = ‖fderiv ℝ f x‖ₑ := by
    -- `grad f x = (toDual).symm (fderiv f x)` and `toDual.symm` is an isometry.
    simpa [grad] using
      (LinearIsometry.enorm_map
        (f := (InnerProductSpace.toDual ℝ E).symm.toLinearIsometry)
        (fderiv ℝ f x))
  -- Replace the operator norm by the gradient norm.
  simpa [h₂, mul_assoc, mul_left_comm, mul_comm] using h₁

lemma enorm_deriv_comp_line_le (x a : E) {f : E → ℝ} (hf : ContDiff ℝ 1 f) (t : ℝ) :
    ‖deriv (fun t => f (line (x := x) (a := a) t)) t‖ₑ ≤
      ‖a‖ₑ * ‖grad (E := E) f (line (x := x) (a := a) t)‖ₑ := by
  -- Reduce to the `fderiv` bound.
  have :=
    enorm_fderiv_apply_le_enorm_grad_mul
      (E := E) (f := f) (x := line (x := x) (a := a) t) (a := a)
  -- Rewrite `deriv` and commute the product.
  simpa [deriv_comp_line (hf := hf) (x := x) (a := a) t,
    mul_comm, mul_left_comm, mul_assoc] using this

attribute [local instance] RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.instMeasurableSpaceE_SobolevEuclideanTranslationEstimate
lemma enorm_sub_le_enorm_mul_lintegral_grad (x a : E) {f : E → ℝ} (hf : ContDiff ℝ 1 f) :
    ‖f (x + a) - f x‖ₑ ≤
      ‖a‖ₑ * ∫⁻ t in Icc (0 : ℝ) 1, ‖grad (E := E) f (x + t • a)‖ₑ := by
  -- Apply FTC along the segment `t ↦ x + t • a`, then bound the derivative pointwise.
  have hCont :
      ContDiffOn ℝ 1 (fun t : ℝ => f (x + t • a)) (Icc (0 : ℝ) 1) := by
    -- `t ↦ x + t • a` is `C^∞`; compose with `f`.
    have hInner : ContDiff ℝ ⊤ (fun t : ℝ => x + t • a) := by
      simpa [line] using
        (contDiff_const.add (contDiff_id.smul (contDiff_const : ContDiff ℝ ⊤ (fun _ : ℝ => a))))
    have hInner' : ContDiff ℝ 1 (fun t : ℝ => x + t • a) := hInner.of_le (by first | simp | exact_mod_cast le_top)
    exact (hf.comp hInner').contDiffOn
  have hFTC :
      ‖f (x + a) - f x‖ₑ ≤ ∫⁻ t in Icc (0 : ℝ) 1, ‖deriv (fun t : ℝ => f (x + t • a)) t‖ₑ := by
    simpa using
      (enorm_sub_le_lintegral_deriv_of_contDiffOn_Icc (f := fun t : ℝ => f (x + t • a))
        (a := (0 : ℝ)) (b := 1) hCont (by exact zero_le_one))
  refine hFTC.trans ?_
  have hDerivBound :
      (fun t : ℝ => ‖deriv (fun t : ℝ => f (x + t • a)) t‖ₑ)
        ≤ᵐ[Measure.restrict volume (Icc (0 : ℝ) 1)]
          fun t : ℝ => ‖a‖ₑ * ‖grad (E := E) f (x + t • a)‖ₑ := by
    -- Pointwise bound holds everywhere.
    refine (ae_of_all _ fun t => ?_)
    -- `deriv` along `t ↦ x + t•a` is controlled by the gradient.
    simpa [line, mul_assoc, mul_left_comm, mul_comm] using
      (enorm_deriv_comp_line_le (x := x) (a := a) (f := f) hf (t := t))
  -- Pull out the constant `‖a‖ₑ`.
  have :
      (∫⁻ t in Icc (0 : ℝ) 1, ‖deriv (fun t : ℝ => f (x + t • a)) t‖ₑ) ≤
        ∫⁻ t in Icc (0 : ℝ) 1, ‖a‖ₑ * ‖grad (E := E) f (x + t • a)‖ₑ := by
    exact lintegral_mono_ae hDerivBound
  refine this.trans ?_
  -- Pull out the constant factor.
  have hMeas :
      Measurable fun t : ℝ => ‖grad (E := E) f (x + t • a)‖ₑ := by
    -- `grad f` is continuous when `f` is `C¹`.
    have hgradCont : Continuous (grad (E := E) f) := continuous_grad (E := E) (f := f) (by
      -- `ContDiff` gives continuity of `grad`.
      exact hf)
    -- hence `t ↦ grad f (x + t•a)` is measurable; take `enorm`.
    exact (hgradCont.comp (by
      have : Continuous (fun t : ℝ => x + t • a) := by
        fun_prop
      exact this)).measurable.enorm
  -- Now finish: `∫⁻ t in Icc, ‖a‖ * g t = ‖a‖ * ∫⁻ t in Icc, g t`.
  exact le_of_eq <| by
    simpa [mul_assoc] using
      (MeasureTheory.lintegral_const_mul (μ := volume.restrict (Icc (0 : ℝ) 1)) (r := ‖a‖ₑ)
        (f := fun t : ℝ => ‖grad (E := E) f (x + t • a)‖ₑ) hMeas)

end

end

end Euclidean
end Sobolev
end FunctionalSpaces
end Analysis
end RellichKondrachov
end

section
-- module Solutions.OAIQ092_CC.Analysis_FunctionalSpaces_Sobolev_Euclidean_TranslationEstimateL2
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/

/-!
# `RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.TranslationEstimateL2`

`L²` translation estimates for Euclidean `C¹_c` functions (and derived `H¹`) under invariant
measures.

This file lifts the pointwise fundamental-theorem-of-calculus bound from
`Euclidean.TranslationEstimate` to an `L²` bound using Tonelli and the measure-preserving property
of translations.

## Main results

- `enorm_translateL2_sub_toL2_le`: for `f ∈ C¹_c`, `‖τ_a f - f‖₂ ≤ ‖a‖ · ‖∇f‖₂` (as an `ℝ≥0∞`
  inequality on `L²` norms), under a right-invariant measure.
-/

namespace RellichKondrachov
namespace Analysis
namespace FunctionalSpaces
namespace Sobolev
namespace Euclidean

open scoped ENNReal MeasureTheory Topology
open MeasureTheory Set

noncomputable section

section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

attribute [local instance] RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.instMeasurableSpaceE_SobolevEuclideanTranslationEstimateL2
local instance instBorelSpaceE_SobolevEuclideanTranslationEstimateL2 :
    BorelSpace E := ⟨rfl⟩
local instance instOpensMeasurableSpaceE_SobolevEuclideanTranslationEstimateL2 :
    OpensMeasurableSpace E := by
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
local instance instMeasurableAddE_SobolevEuclideanTranslationEstimateL2 : MeasurableAdd E := by
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

variable (μ : Measure E) [μ.IsAddRightInvariant] [IsFiniteMeasureOnCompacts μ] [SFinite μ]

private lemma holderConj_two_two : (2 : ℝ).HolderConjugate (2 : ℝ) := by
  refine (Real.holderConjugate_iff).2 ?_
  constructor
  · linarith
  · norm_num

private lemma lintegral_rpow_two_le_lintegral_rpow_two
    {g : ℝ → ℝ≥0∞} (hg : AEMeasurable g (μI : Measure ℝ)) :
    (∫⁻ t, g t ∂(μI : Measure ℝ)) ^ (2 : ℝ) ≤ ∫⁻ t, g t ^ (2 : ℝ) ∂(μI : Measure ℝ) := by
  -- Hölder with `g * 1` gives `∫ g ≤ (∫ g^2)^(1/2) * (∫ 1^2)^(1/2)`.
  have hHolder :
      (∫⁻ t, g t ∂(μI : Measure ℝ)) ≤
        (∫⁻ t, g t ^ (2 : ℝ) ∂(μI : Measure ℝ)) ^ (1 / (2 : ℝ)) *
          (∫⁻ _t : ℝ, (1 : ℝ≥0∞) ^ (2 : ℝ) ∂(μI : Measure ℝ)) ^ (1 / (2 : ℝ)) := by
    simpa [Pi.mul_apply] using
      (ENNReal.lintegral_mul_le_Lp_mul_Lq (μ := (μI : Measure ℝ)) holderConj_two_two
        hg (aemeasurable_const : AEMeasurable (fun _t : ℝ => (1 : ℝ≥0∞)) (μI : Measure ℝ)))
  have h1 : (∫⁻ _t : ℝ, (1 : ℝ≥0∞) ^ (2 : ℝ) ∂(μI : Measure ℝ)) ^ (1 / (2 : ℝ)) = (1 : ℝ≥0∞) := by
    -- `μI` has total mass `1`, and `1^2 = 1`.
    simp
  have h :
      (∫⁻ t, g t ∂(μI : Measure ℝ)) ≤
        (∫⁻ t, g t ^ (2 : ℝ) ∂(μI : Measure ℝ)) ^ (1 / (2 : ℝ)) := by
    simpa [h1, mul_one] using hHolder
  -- Raise to the power `2` and simplify `((A)^(1/2))^2 = A`.
  have h' :=
    ENNReal.rpow_le_rpow h (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)
  -- Rewrite the RHS using `rpow_mul`.
  simpa [ENNReal.rpow_mul] using (h'.trans_eq (by
    have : (1 / (2 : ℝ)) * (2 : ℝ) = (1 : ℝ) := by norm_num
    simpa [this] using
      (ENNReal.rpow_mul
        (∫⁻ t, g t ^ (2 : ℝ) ∂(μI : Measure ℝ))
        (1 / (2 : ℝ)) (2 : ℝ)).symm))

/-- `L²` translation estimate for `C¹_c` functions under a right-invariant measure. -/
lemma enorm_translateL2_sub_toL2_le (a : E) (f : ↥(C1c (E := E))) :
    ‖translateL2 (μ := μ) (F := ℝ) a (toL2 (μ := μ) (E := E) f) -
        toL2 (μ := μ) (E := E) f‖ₑ ≤
      ‖a‖ₑ * ‖toL2Grad (μ := μ) (E := E) f‖ₑ := by
  classical
  -- Reduce to an `eLpNorm` inequality on representatives.
  have hL2 :
      (‖translateL2 (μ := μ) (F := ℝ) a (toL2 (μ := μ) (E := E) f) -
          toL2 (μ := μ) (E := E) f‖ₑ : ℝ≥0∞) =
        MeasureTheory.eLpNorm (fun x : E => (f.1 (x + a) - f.1 x)) (2 : ℝ≥0∞) μ := by
    -- Both terms agree a.e. with the underlying pointwise translation.
    have h₁ :
        (translateL2 (μ := μ) (F := ℝ) a (toL2 (μ := μ) (E := E) f) : E → ℝ) =ᵐ[μ]
          fun x => f.1 (x + a) := by
      have hf :
          (toL2 (μ := μ) (E := E) f : E → ℝ) =ᵐ[μ] f.1 :=
        (memLp_of_mem_C1c (μ := μ) (E := E) f.2).coeFn_toLp
      have hf' :
          (fun x => (toL2 (μ := μ) (E := E) f : E → ℝ) (x + a)) =ᵐ[μ] fun x => f.1 (x + a) := by
        exact
          (Measure.QuasiMeasurePreserving.ae_eq_comp
            (MeasureTheory.measurePreserving_add_right μ a).quasiMeasurePreserving hf)
      exact (translateL2_ae_eq (μ := μ) (F := ℝ) a (toL2 (μ := μ) (E := E) f)).trans hf'
    have h₂ : (toL2 (μ := μ) (E := E) f : E → ℝ) =ᵐ[μ] fun x => f.1 x :=
      (memLp_of_mem_C1c (μ := μ) (E := E) f.2).coeFn_toLp
    have hsub :
        ((translateL2 (μ := μ) (F := ℝ) a (toL2 (μ := μ) (E := E) f) -
              toL2 (μ := μ) (E := E) f : E →₂[μ] ℝ) : E → ℝ) =ᵐ[μ]
          fun x => f.1 (x + a) - f.1 x := by
      filter_upwards [Lp.coeFn_sub
        (translateL2 (μ := μ) (F := ℝ) a (toL2 (μ := μ) (E := E) f))
        (toL2 (μ := μ) (E := E) f), h₁, h₂] with x hxsub hx1 hx2
      simpa [hx1, hx2, Pi.sub_apply] using hxsub
    -- Convert the `Lp` norm to `eLpNorm` and rewrite using a.e. equality.
    let d : E →₂[μ] ℝ :=
      translateL2 (μ := μ) (F := ℝ) a (toL2 (μ := μ) (E := E) f) - toL2 (μ := μ) (E := E) f
    have hd0 : (‖d‖ₑ : ℝ≥0∞) = MeasureTheory.eLpNorm (fun x : E => (d : E → ℝ) x) (2 : ℝ≥0∞) μ := by
      simp [MeasureTheory.Lp.enorm_def]
    have hd1 :
        MeasureTheory.eLpNorm (fun x : E => (d : E → ℝ) x) (2 : ℝ≥0∞) μ =
          MeasureTheory.eLpNorm (fun x : E => f.1 (x + a) - f.1 x) (2 : ℝ≥0∞) μ :=
      MeasureTheory.eLpNorm_congr_ae (μ := μ) (p := (2 : ℝ≥0∞)) (by simpa [d] using hsub)
    simpa [d] using hd0.trans hd1
  have hGrad :
      (‖toL2Grad (μ := μ) (E := E) f‖ₑ : ℝ≥0∞) =
        MeasureTheory.eLpNorm (fun x : E => grad (E := E) f.1 x) (2 : ℝ≥0∞) μ := by
    have h₁ :
        (toL2Grad (μ := μ) (E := E) f : E → E) =ᵐ[μ] fun x => grad (E := E) f.1 x :=
      (memLp_grad_of_mem_C1c (μ := μ) (E := E) f.2).coeFn_toLp
    have h0 :
        (‖toL2Grad (μ := μ) (E := E) f‖ₑ : ℝ≥0∞) =
          MeasureTheory.eLpNorm (fun x : E => (toL2Grad (μ := μ) (E := E) f : E → E) x)
            (2 : ℝ≥0∞) μ := by
      simp [MeasureTheory.Lp.enorm_def]
    have h1 :
        MeasureTheory.eLpNorm (fun x : E => (toL2Grad (μ := μ) (E := E) f : E → E) x)
            (2 : ℝ≥0∞) μ =
          MeasureTheory.eLpNorm (fun x : E => grad (E := E) f.1 x) (2 : ℝ≥0∞) μ :=
      MeasureTheory.eLpNorm_congr_ae (μ := μ) (p := (2 : ℝ≥0∞)) h₁
    exact h0.trans h1
  -- Prove the `eLpNorm` inequality by squaring, using Tonelli and measure-preserving translation.
  have hCore :
      MeasureTheory.eLpNorm (fun x : E => f.1 (x + a) - f.1 x) (2 : ℝ≥0∞) μ ≤
        ‖a‖ₑ * MeasureTheory.eLpNorm (fun x : E => grad (E := E) f.1 x) (2 : ℝ≥0∞) μ := by
    -- Expand the definition of `eLpNorm` at exponent `2`.
    have h2_ne0 : (2 : ℝ≥0∞) ≠ 0 := by simp
    have h2_netop : (2 : ℝ≥0∞) ≠ ∞ := by simp
    simp_rw [MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal
      h2_ne0 h2_netop, ENNReal.toReal_ofNat] at *
    -- It suffices to compare the squared integrals.
    have hsq :
        (∫⁻ x, ‖f.1 (x + a) - f.1 x‖ₑ ^ (2 : ℝ) ∂μ) ≤
          ‖a‖ₑ ^ (2 : ℝ) * (∫⁻ x, ‖grad (E := E) f.1 x‖ₑ ^ (2 : ℝ) ∂μ) := by
      -- Pointwise: Cauchy–Schwarz in `t`, then Tonelli in `(x,t)`.
      have hpt :
          ∀ x : E,
            ‖f.1 (x + a) - f.1 x‖ₑ ^ (2 : ℝ) ≤
              ‖a‖ₑ ^ (2 : ℝ) *
                ∫⁻ t, ‖grad (E := E) f.1 (x + t • a)‖ₑ ^ (2 : ℝ) ∂(μI : Measure ℝ) := by
        intro x
        have h0 := enorm_sub_le_enorm_mul_lintegral_grad (E := E) (x := x) (a := a) (f := f.1)
          (hf := f.2.1)
        -- Square both sides and apply Cauchy–Schwarz in `t`.
        have h1 :
            ‖f.1 (x + a) - f.1 x‖ₑ ^ (2 : ℝ) ≤
              (‖a‖ₑ * ∫⁻ t, ‖grad (E := E) f.1 (x + t • a)‖ₑ ∂(μI : Measure ℝ)) ^ (2 : ℝ) := by
          exact ENNReal.rpow_le_rpow h0 (by norm_num)
        have hcs :
            (∫⁻ t, ‖grad (E := E) f.1 (x + t • a)‖ₑ ∂(μI : Measure ℝ)) ^ (2 : ℝ) ≤
              ∫⁻ t, ‖grad (E := E) f.1 (x + t • a)‖ₑ ^ (2 : ℝ) ∂(μI : Measure ℝ) := by
          refine lintegral_rpow_two_le_lintegral_rpow_two (g := fun t : ℝ =>
            ‖grad (E := E) f.1 (x + t • a)‖ₑ) ?_
          -- measurability from continuity of `grad`.
          have hgrad : Continuous (grad (E := E) f.1) := continuous_grad (E := E) (f := f.1) f.2.1
          have hline : Continuous fun t : ℝ => x + t • a := by
            fun_prop
          exact (hgrad.comp hline).measurable.enorm.aemeasurable
        -- Combine and rewrite.
        calc
          ‖f.1 (x + a) - f.1 x‖ₑ ^ (2 : ℝ)
              ≤ (‖a‖ₑ * ∫⁻ t, ‖grad (E := E) f.1 (x + t • a)‖ₑ ∂(μI : Measure ℝ)) ^ (2 : ℝ) := h1
          _ = ‖a‖ₑ ^ (2 : ℝ) *
              (∫⁻ t, ‖grad (E := E) f.1 (x + t • a)‖ₑ
                ∂(μI : Measure ℝ)) ^ (2 : ℝ) := by
              simpa using
                (ENNReal.mul_rpow_of_nonneg ‖a‖ₑ
                  (∫⁻ t, ‖grad (E := E) f.1 (x + t • a)‖ₑ
                    ∂(μI : Measure ℝ))
                  (show (0 : ℝ) ≤ (2 : ℝ) by norm_num))
          _ ≤ ‖a‖ₑ ^ (2 : ℝ) *
              ∫⁻ t, ‖grad (E := E) f.1 (x + t • a)‖ₑ ^ (2 : ℝ)
                ∂(μI : Measure ℝ) := by
              gcongr
          _ = ‖a‖ₑ ^ (2 : ℝ) *
              ∫⁻ t, ‖grad (E := E) f.1 (x + t • a)‖ₑ ^ (2 : ℝ)
                ∂(μI : Measure ℝ) := rfl
      -- Integrate over `x` and apply Tonelli to swap integrals.
      let F : E × ℝ → ℝ≥0∞ :=
        fun z => ‖grad (E := E) f.1 (z.1 + z.2 • a)‖ₑ ^ (2 : ℝ)
      have hmeas :
          AEMeasurable
            F (μ.prod (μI : Measure ℝ)) := by
        have hgrad : Continuous (grad (E := E) f.1) := continuous_grad (E := E) (f := f.1) f.2.1
        have hcont : Continuous fun z : E × ℝ => z.1 + z.2 • a := by
          fun_prop
        have hbase : Measurable fun z : E × ℝ => ‖grad (E := E) f.1 (z.1 + z.2 • a)‖ₑ := by
          exact (hgrad.comp hcont).measurable.enorm
        have hpow : Measurable fun r : ℝ≥0∞ => r ^ (2 : ℝ) :=
          (ENNReal.continuous_rpow_const (y := (2 : ℝ))).measurable
        exact (hpow.comp hbase).aemeasurable
      have hTonelli :
          (∫⁻ x, ∫⁻ t, ‖grad (E := E) f.1 (x + t • a)‖ₑ ^ (2 : ℝ) ∂(μI : Measure ℝ) ∂μ) =
            ∫⁻ t, ∫⁻ x, ‖grad (E := E) f.1 (x + t • a)‖ₑ ^ (2 : ℝ) ∂μ ∂(μI : Measure ℝ) := by
        -- Tonelli in both orders, via the product measure.
        have hprod :
            (∫⁻ z, F z ∂μ.prod (μI : Measure ℝ)) =
              ∫⁻ x, ∫⁻ t, F (x, t) ∂(μI : Measure ℝ) ∂μ :=
          MeasureTheory.lintegral_prod (μ := μ) (ν := (μI : Measure ℝ)) F hmeas
        have hprod_symm :
            (∫⁻ z, F z ∂μ.prod (μI : Measure ℝ)) =
              ∫⁻ t, ∫⁻ x, F (x, t) ∂μ ∂(μI : Measure ℝ) :=
          MeasureTheory.lintegral_prod_symm (μ := μ) (ν := (μI : Measure ℝ)) F hmeas
        calc
          (∫⁻ x, ∫⁻ t, ‖grad (E := E) f.1 (x + t • a)‖ₑ ^ (2 : ℝ) ∂(μI : Measure ℝ) ∂μ)
              = ∫⁻ z, F z ∂μ.prod (μI : Measure ℝ) := by
                  simpa [F] using hprod.symm
          _ = ∫⁻ t, ∫⁻ x, F (x, t) ∂μ ∂(μI : Measure ℝ) := hprod_symm
          _ = ∫⁻ t, ∫⁻ x, ‖grad (E := E) f.1 (x + t • a)‖ₑ ^ (2 : ℝ) ∂μ ∂(μI : Measure ℝ) := by
                  simp [F]
      -- Now use measure-preserving translation in `x` and evaluate the `t`-integral.
      have hShift :
          (∫⁻ t, ∫⁻ x, ‖grad (E := E) f.1 (x + t • a)‖ₑ ^ (2 : ℝ) ∂μ ∂(μI : Measure ℝ)) =
            ∫⁻ t, (∫⁻ x, ‖grad (E := E) f.1 x‖ₑ ^ (2 : ℝ) ∂μ) ∂(μI : Measure ℝ) := by
        refine MeasureTheory.lintegral_congr fun t => ?_
        -- Change of variables `x ↦ x + t•a`.
        have hmeas' : Measurable fun x : E => ‖grad (E := E) f.1 x‖ₑ ^ (2 : ℝ) := by
          have hgrad : Continuous (grad (E := E) f.1) := continuous_grad (E := E) (f := f.1) f.2.1
          have hbase : Measurable fun x : E => ‖grad (E := E) f.1 x‖ₑ := hgrad.measurable.enorm
          have hpow : Measurable fun r : ℝ≥0∞ => r ^ (2 : ℝ) :=
            (ENNReal.continuous_rpow_const (y := (2 : ℝ))).measurable
          exact hpow.comp hbase
        simpa [Function.comp, add_assoc] using
          (MeasureTheory.measurePreserving_add_right μ (t • a)).lintegral_comp (μ := μ) (ν := μ)
            (f := fun x : E => ‖grad (E := E) f.1 x‖ₑ ^ (2 : ℝ)) hmeas'
      have hEval :
          (∫⁻ t, (∫⁻ x, ‖grad (E := E) f.1 x‖ₑ ^ (2 : ℝ) ∂μ) ∂(μI : Measure ℝ)) =
            (∫⁻ x, ‖grad (E := E) f.1 x‖ₑ ^ (2 : ℝ) ∂μ) := by
        -- `μI` has total mass `1`.
        simp [μI, Measure.restrict_apply, Real.volume_Icc]
      -- Put everything together.
      have hInt :
          (∫⁻ x, ‖f.1 (x + a) - f.1 x‖ₑ ^ (2 : ℝ) ∂μ) ≤
            ‖a‖ₑ ^ (2 : ℝ) * (∫⁻ x, ‖grad (E := E) f.1 x‖ₑ ^ (2 : ℝ) ∂μ) := by
        calc
          (∫⁻ x, ‖f.1 (x + a) - f.1 x‖ₑ ^ (2 : ℝ) ∂μ)
              ≤ ∫⁻ x, ‖a‖ₑ ^ (2 : ℝ) *
                    ∫⁻ t, ‖grad (E := E) f.1 (x + t • a)‖ₑ ^ (2 : ℝ) ∂(μI : Measure ℝ) ∂μ := by
                refine MeasureTheory.lintegral_mono ?_
                intro x
                exact hpt x
          _ = ‖a‖ₑ ^ (2 : ℝ) *
                (∫⁻ x, ∫⁻ t, ‖grad (E := E) f.1 (x + t • a)‖ₑ ^ (2 : ℝ) ∂(μI : Measure ℝ) ∂μ) := by
                -- Pull out the constant using `lintegral_const_mul''`.
                have hInner :
                    AEMeasurable
                      (fun x : E =>
                        ∫⁻ t, ‖grad (E := E) f.1 (x + t • a)‖ₑ ^ (2 : ℝ) ∂(μI : Measure ℝ)) μ := by
                  -- Measurability of the inner integral follows
                  -- from `hmeas` via
                  -- `AEMeasurable.lintegral_prod_right'`.
                  simpa [F] using (hmeas.lintegral_prod_right' (μ := μ) (ν := (μI : Measure ℝ)))
                simpa [mul_assoc] using
                  (MeasureTheory.lintegral_const_mul'' (μ := μ) (r := ‖a‖ₑ ^ (2 : ℝ))
                    (f := fun x : E =>
                      ∫⁻ t, ‖grad (E := E) f.1 (x + t • a)‖ₑ ^ (2 : ℝ) ∂(μI : Measure ℝ)) hInner)
          _ = ‖a‖ₑ ^ (2 : ℝ) *
                (∫⁻ t, ∫⁻ x, ‖grad (E := E) f.1 (x + t • a)‖ₑ ^ (2 : ℝ) ∂μ ∂(μI : Measure ℝ)) := by
                exact congrArg (fun z => ‖a‖ₑ ^ (2 : ℝ) * z) hTonelli
          _ = ‖a‖ₑ ^ (2 : ℝ) *
                (∫⁻ t, (∫⁻ x, ‖grad (E := E) f.1 x‖ₑ ^ (2 : ℝ) ∂μ) ∂(μI : Measure ℝ)) := by
                exact congrArg (fun z => ‖a‖ₑ ^ (2 : ℝ) * z) hShift
          _ = ‖a‖ₑ ^ (2 : ℝ) * (∫⁻ x, ‖grad (E := E) f.1 x‖ₑ ^ (2 : ℝ) ∂μ) := by
                exact congrArg (fun z => ‖a‖ₑ ^ (2 : ℝ) * z) hEval
      exact hInt
    -- Take the `1/2` power on both sides and simplify.
    have hsq' :
        (∫⁻ x, ‖f.1 (x + a) - f.1 x‖ₑ ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) ≤
          (‖a‖ₑ ^ (2 : ℝ) * ∫⁻ x, ‖grad (E := E) f.1 x‖ₑ ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) := by
      exact ENNReal.rpow_le_rpow hsq (by norm_num)
    -- Rewrite the RHS as `‖a‖ * (...)^(1/2)`.
    have hsq'' :
        (∫⁻ x, ‖f.1 (x + a) - f.1 x‖ₑ ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) ≤
          (‖a‖ₑ ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) *
            (∫⁻ x, ‖grad (E := E) f.1 x‖ₑ ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) := by
      simpa [ENNReal.mul_rpow_of_nonneg, show (0 : ℝ) ≤ (1 / (2 : ℝ)) by nlinarith,
        mul_assoc, mul_left_comm, mul_comm] using hsq'
    have hroot : (‖a‖ₑ ^ (2 : ℕ)) ^ ((2 : ℝ)⁻¹) = ‖a‖ₑ := by
      -- `(x^2)^(1/2) = x` in `ℝ≥0∞`, accounting for simp-normalization of `2` and `1/2`.
      have hnat : (‖a‖ₑ ^ (2 : ℕ)) = ‖a‖ₑ ^ (2 : ℝ) := by
        simp
      calc
        (‖a‖ₑ ^ (2 : ℕ)) ^ ((2 : ℝ)⁻¹) = (‖a‖ₑ ^ (2 : ℝ)) ^ ((2 : ℝ)⁻¹) :=
          congrArg (fun r : ℝ≥0∞ => r ^ ((2 : ℝ)⁻¹)) hnat
        _ = ‖a‖ₑ := by
          have := (ENNReal.rpow_mul ‖a‖ₑ (2 : ℝ) ((2 : ℝ)⁻¹)).symm
          have hmul : (2 : ℝ) * ((2 : ℝ)⁻¹) = (1 : ℝ) := by norm_num
          simpa [hmul, ENNReal.rpow_one] using this
    simpa [hroot, mul_assoc, mul_left_comm, mul_comm] using hsq''
  -- Finish: translate back to the original `L²` norms.
  -- (The final `simp` is safe since we have explicit `eLpNorm` equalities above.)
  simpa [hL2, hGrad] using hCore

/-- Real-norm form of `enorm_translateL2_sub_toL2_le`. -/
lemma norm_translateL2_sub_toL2_le (a : E) (f : ↥(C1c (E := E))) :
    ‖translateL2 (μ := μ) (F := ℝ) a (toL2 (μ := μ) (E := E) f) -
        toL2 (μ := μ) (E := E) f‖ ≤
      ‖a‖ * ‖toL2Grad (μ := μ) (E := E) f‖ := by
  have h := enorm_translateL2_sub_toL2_le (μ := μ) (E := E) a f
  have hA_ne_top :
      (‖translateL2 (μ := μ) (F := ℝ) a (toL2 (μ := μ) (E := E) f) -
            toL2 (μ := μ) (E := E) f‖ₑ : ℝ≥0∞) ≠ ∞ := by
    simp [enorm]
  have hGrad_ne_top :
      (‖toL2Grad (μ := μ) (E := E) f‖ₑ : ℝ≥0∞) ≠ ∞ := by
    simp [enorm]
  have hB_ne_top : (‖a‖ₑ * ‖toL2Grad (μ := μ) (E := E) f‖ₑ : ℝ≥0∞) ≠ ∞ := by
    refine ENNReal.mul_ne_top ?_ hGrad_ne_top
    simp [enorm]
  have h' :
      (‖translateL2 (μ := μ) (F := ℝ) a (toL2 (μ := μ) (E := E) f) -
            toL2 (μ := μ) (E := E) f‖ₑ).toReal ≤
        (‖a‖ₑ * ‖toL2Grad (μ := μ) (E := E) f‖ₑ).toReal := by
    exact (ENNReal.toReal_le_toReal hA_ne_top hB_ne_top).2 h
  simpa [ENNReal.toReal_mul, toReal_enorm'] using h'

end

end

end Euclidean
end Sobolev
end FunctionalSpaces
end Analysis
end RellichKondrachov
end

section
-- module Solutions.OAIQ092_CC.Analysis_FunctionalSpaces_Sobolev_Euclidean_TranslationEstimateH1
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/

/-!
# `RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.TranslationEstimateH1`

Extend Euclidean `L²` translation estimates from `C¹_c` to the closure-based Euclidean `H¹` space.

## Main results

- `norm_translateL2_sub_h1ToL2_le`: for `u ∈ H¹`, `‖τ_a u - u‖₂ ≤ ‖a‖ · ‖∇u‖₂`, where `∇u` is the
  `L²(E)` component in our `H¹ ⊆ L² × L²(E)` model.
-/

namespace RellichKondrachov
namespace Analysis
namespace FunctionalSpaces
namespace Sobolev
namespace Euclidean

open scoped ENNReal MeasureTheory Topology
open MeasureTheory Set

noncomputable section

section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

attribute [local instance] RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.instMeasurableSpaceE_SobolevEuclideanTranslationEstimateH1
local instance instBorelSpaceE_SobolevEuclideanTranslationEstimateH1_r1554e2_1 :
    BorelSpace E := ⟨rfl⟩
local instance instOpensMeasurableSpaceE_SobolevEuclideanTranslationEstimateH1_r1554e2_1 :
    OpensMeasurableSpace E := by
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
local instance instMeasurableAddE_SobolevEuclideanTranslationEstimateH1_r1554e2_1 : MeasurableAdd E := by
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
variable (μ : Measure E) [μ.IsAddRightInvariant] [IsFiniteMeasureOnCompacts μ] [SFinite μ]

/-- `H¹` translation estimate via closure: `‖τ_a u - u‖₂ ≤ ‖a‖ · ‖∇u‖₂`. -/
theorem norm_translateL2_sub_h1ToL2_le (a : E) (u : ↥(h1 (μ := μ) (E := E))) :
    ‖translateL2 (μ := μ) (F := ℝ) a (h1ToL2 (μ := μ) (E := E) u) -
        h1ToL2 (μ := μ) (E := E) u‖ ≤
      ‖a‖ * ‖h1ToL2Grad (μ := μ) (E := E) u‖ := by
  classical
  -- Work in the ambient space `L² × L²(E)`.
  let V : Type _ := (E →₂[μ] ℝ) × (E →₂[μ] E)
  let S : Set V :=
    {v |
      ‖translateL2 (μ := μ) (F := ℝ) a v.1 - v.1‖ ≤
        ‖a‖ * ‖v.2‖}
  have hS_closed : IsClosed S := by
    -- Closedness follows from continuity of both sides.
    have hf :
        Continuous fun v : V =>
          ‖translateL2 (μ := μ) (F := ℝ) a v.1 - v.1‖ := by
      -- `v ↦ v.1` is continuous, translation is continuous,
      -- subtraction is continuous, and norm is continuous.
      have hfst : Continuous fun v : V => v.1 := continuous_fst
      have htr :
          Continuous fun v : V =>
            translateL2 (μ := μ) (F := ℝ) a v.1 := by
        -- `translateL2` is a continuous linear isometry.
        exact (translateL2 (μ := μ) (F := ℝ) a).toContinuousLinearMap.continuous.comp hfst
      have hsub :
          Continuous fun v : V =>
            translateL2 (μ := μ) (F := ℝ) a v.1 - v.1 := by
        exact htr.sub hfst
      exact (continuous_norm.comp hsub)
    have hg :
        Continuous fun v : V =>
          ‖a‖ * ‖v.2‖ := by
      have hsnd : Continuous fun v : V => v.2 := continuous_snd
      have hnorm : Continuous fun v : V => ‖v.2‖ := continuous_norm.comp hsnd
      exact (continuous_const.mul hnorm)
    exact isClosed_le hf hg
  have hRange : (LinearMap.range (graph (μ := μ) (E := E)) : Set V) ⊆ S := by
    rintro v ⟨f, rfl⟩
    -- Reduce to the `C¹_c` estimate.
    simpa [S, graph, toL2Linear, toL2GradLinear] using
      norm_translateL2_sub_toL2_le (μ := μ) (E := E) a f
  have hClosure :
      closure (LinearMap.range (graph (μ := μ) (E := E)) : Set V) ⊆ S :=
    closure_minimal hRange hS_closed
  have hu :
      (u : V) ∈ closure (LinearMap.range (graph (μ := μ) (E := E)) : Set V) := by
    -- `u ∈ H¹` means `u` is in the topological closure of the range of `graph`.
    have hu0 :
        (u : V) ∈
          ((LinearMap.range (graph (μ := μ) (E := E))).topologicalClosure :
            Set V) := by
      have hu0 : (u : V) ∈ h1 (μ := μ) (E := E) := u.2
      dsimp [h1] at hu0
      exact hu0
    have hu1 :
        (u : V) ∈
          ((LinearMap.range (graph (μ := μ) (E := E))).topologicalClosure :
            Set V) := hu0
    rw [Submodule.topologicalClosure_coe] at hu1
    exact hu1
  have huS : (u : V) ∈ S := hClosure hu
  -- Unpack membership in `S` and rewrite in terms of the bundled maps `h1ToL2` and `h1ToL2Grad`.
  simpa [S, V, h1ToL2, h1ToL2Grad] using huS

end

end

end Euclidean
end Sobolev
end FunctionalSpaces
end Analysis
end RellichKondrachov
end

section
-- module Solutions.OAIQ092_CC.Analysis_FunctionalSpaces_Sobolev_Euclidean_Rellich
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/

set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# `RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.Rellich`

Euclidean Rellich–Kondrachov compactness for fixed compact support (Lebesgue `volume`).

This file discharges the “Euclidean heart” needed by the manifold Rellich glue:
for a fixed compact set `K ⊆ E`, the inclusion `H¹ → L²` is compact when restricted to the closed
subspace of `H¹` whose `L²` component is supported in `K` (a.e.).

The proof uses:

1. the Euclidean `H¹` translation estimate
   `‖τ_a u - u‖₂ ≤ ‖a‖ · ‖∇u‖₂` (`TranslationEstimateH1`);
2. the Fréchet–Kolmogorov / smoothing-based `L²` compactness criterion
   (`L2CompactnessCriterion`).

## Main definitions / results

- `RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.h1On`:
  the closed subspace of `H¹(volume)` whose `L²` component is supported in `K` (a.e.).
- `RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.h1OnToL2`:
  the restricted inclusion map `h1On K →L[ℝ] L²(volume)`.
- `RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.isCompactOperator_h1OnToL2`:
  compactness of the inclusion.

Tracking: Beads `lean-103.5.2.26.5.3.2.1`.
-/

namespace RellichKondrachov
namespace Analysis
namespace FunctionalSpaces
namespace Sobolev
namespace Euclidean

open scoped ENNReal MeasureTheory Topology
open MeasureTheory Set

noncomputable section

section Volume

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]

/-! ### Supported `H¹` subspace -/

/-! ### Euclidean Rellich on fixed compact support -/

attribute [local instance] RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.instMeasurableSpaceE_SobolevEuclideanRellich
attribute [local instance] RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.instBorelSpaceE_SobolevEuclideanRellich
local instance instOpensMeasurableSpaceE_SobolevEuclideanRellich_r1554e2_1 : OpensMeasurableSpace E := by
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
local instance instMeasurableAddE_SobolevEuclideanRellich_r1554e2_1 : MeasurableAdd E := by
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
local instance instMeasurableNegE_SobolevEuclideanRellich_r1554e2_1 : MeasurableNeg E := by
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
attribute [local instance] RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.instFactOneLeTwo_SobolevEuclideanRellich
set_option maxHeartbeats 2000000 in
/-- Euclidean Rellich–Kondrachov compactness (Lebesgue): on a fixed compact support `K`, the
inclusion `H¹ → L²` is a compact operator. -/
theorem isCompactOperator_h1OnToL2 {K : Set E} (_hK : IsCompact K) (hKm : MeasurableSet K) :
    IsCompactOperator (h1OnToL2 (E := E) K hKm) := by
  classical
  have hr : (0 : ℝ) < 1 := by norm_num
  let H1vol : Type _ := ↥(h1 (μ := (volume : Measure E)) (E := E))
  let T : ↥(h1On (E := E) K hKm) →L[ℝ] (E →₂[(volume : Measure E)] ℝ) :=
    h1OnToL2 (E := E) K hKm
  let A : Set (MeasureTheory.Lp ℝ (2 : ℝ≥0∞) ((volume : Measure E).restrict K)) :=
    {u |
      L2Compactness.extendByZeroL2 (E := E) (K := K) hKm u ∈
        T '' Metric.closedBall (0 : ↥(h1On (E := E) K hKm)) 1}
  let C : ℝ :=
    (h1ToL2 (μ := (volume : Measure E)) (E := E)).opNorm
  have hCnonneg : 0 ≤ C := by
    dsimp [C]
    exact (h1ToL2 (μ := (volume : Measure E)) (E := E)).opNorm_nonneg
  have hA_ball :
      A ⊆
        Metric.closedBall
          (0 : MeasureTheory.Lp ℝ (2 : ℝ≥0∞) ((volume : Measure E).restrict K))
          C := by
    intro u hu
    rcases hu with ⟨x, hx, hxEq⟩
    have hx' : ‖(x : H1vol)‖ ≤ (1 : ℝ) := by
      -- `h1On` inherits the ambient norm, so this is definitional.
      change ‖x‖ ≤ (1 : ℝ)
      exact (mem_closedBall_zero_iff (E := ↥(h1On K hKm))).mp hx
    have hTx' : ‖T x‖ ≤ C := by
      have hTx : ‖T x‖ ≤ C * ‖(x : H1vol)‖ := by
        have h :=
          (h1ToL2 (μ := (volume : Measure E)) (E := E)).le_opNorm (x : H1vol)
        exact h
      refine hTx.trans ?_
      have : C * ‖(x : H1vol)‖ ≤ C * (1 : ℝ) := mul_le_mul_of_nonneg_left hx' hCnonneg
      simpa [mul_one] using this
    have hnorm_ext :
        ‖L2Compactness.extendByZeroL2 (E := E) (K := K) hKm u‖ = ‖u‖ :=
      L2Compactness.norm_extendByZeroL2 (E := E) (K := K) hKm u
    have hu' : ‖u‖ ≤ C := by
      have : ‖L2Compactness.extendByZeroL2 (E := E) (K := K) hKm u‖ ≤ C := by
        simpa [hxEq] using hTx'
      simpa [hnorm_ext] using this
    simpa [Metric.closedBall, dist_eq_norm] using hu'
  have hApprox :
      ∀ ε : ℝ, 0 < ε →
        ∃ ψ : E → ℝ, Continuous ψ ∧ HasCompactSupport ψ ∧ (∀ x, 0 ≤ ψ x) ∧
          (∫ x, ψ x ∂(volume : Measure E) = 1) ∧
          ∀ u ∈ A,
            ∫ t,
                ‖(translateL2 (μ := (volume : Measure E)) (-t))
                      (L2Compactness.extendByZeroL2 (E := E) (K := K) hKm u)
                    - L2Compactness.extendByZeroL2 (E := E) (K := K) hKm u‖ ^ 2
              ∂L2Compactness.kernelMeasure (E := E) ψ ≤ (ε / 2) ^ 2 := by
    intro ε hε
    have hδ : 0 < ε / 2 := by linarith
    rcases
        L2Compactness.exists_kernel_tsupport_subset_ball_integral_eq_one
          (E := E) (δ := ε / 2) hδ with
      ⟨ψ, hψc, hψcs, hψ0, hψint, hψsupp⟩
    refine ⟨ψ, hψc, hψcs, hψ0, hψint, ?_⟩
    intro u huA
    rcases huA with ⟨x, hx, hxEq⟩
    have hxH1 : ‖(x : H1vol)‖ ≤ (1 : ℝ) := by
      change ‖x‖ ≤ (1 : ℝ)
      exact (mem_closedBall_zero_iff (E := ↥(h1On K hKm))).mp hx
    have hmod :
        ∀ t : E, t ∈ Metric.ball (0 : E) (ε / 2) →
          ‖(translateL2 (μ := (volume : Measure E)) (-t)) (T x) - T x‖ ≤ ε / 2 := by
      intro t ht
      have ht' : ‖t‖ ≤ ε / 2 := le_of_lt (by
        simpa [Metric.ball, dist_eq_norm, mem_setOf_eq] using ht)
      have hgrad_le :
          ‖h1ToL2Grad (μ := (volume : Measure E)) (E := E) (x : H1vol)‖ ≤ ‖(x : H1vol)‖ := by
        let V : Type _ := (E →₂[(volume : Measure E)] ℝ) × (E →₂[(volume : Measure E)] E)
        simpa [h1ToL2Grad, V] using (norm_snd_le (x := ((x : H1vol) : V)))
      have hgrad_le_one :
          ‖h1ToL2Grad (μ := (volume : Measure E)) (E := E) (x : H1vol)‖ ≤ (1 : ℝ) :=
        hgrad_le.trans hxH1
      have htr :=
        norm_translateL2_sub_h1ToL2_le (μ := (volume : Measure E)) (E := E) (-t) (x : H1vol)
      have htr' :
          ‖(translateL2 (μ := (volume : Measure E)) (-t))
                (h1ToL2 (μ := (volume : Measure E)) (E := E) (x : H1vol))
              - h1ToL2 (μ := (volume : Measure E)) (E := E) (x : H1vol)‖ ≤
            ‖t‖ * ‖h1ToL2Grad (μ := (volume : Measure E)) (E := E) (x : H1vol)‖ := by
        simpa [neg_neg] using htr
      have hle :
          ‖(translateL2 (μ := (volume : Measure E)) (-t)) (T x) - T x‖ ≤
            ‖t‖ * ‖h1ToL2Grad (μ := (volume : Measure E)) (E := E) (x : H1vol)‖ := by
        simpa [T, h1OnToL2, hxEq] using htr'
      refine hle.trans ?_
      have :
          ‖t‖ * ‖h1ToL2Grad (μ := (volume : Measure E)) (E := E) (x : H1vol)‖ ≤ (ε / 2) * 1 := by
        refine (mul_le_mul_of_nonneg_right ht' (norm_nonneg _)).trans ?_
        refine mul_le_mul_of_nonneg_left hgrad_le_one (by linarith)
      simpa [mul_one] using this
    have hη : 0 ≤ ε / 2 := le_of_lt hδ
    have hbound :=
      L2Compactness.integral_norm_sq_translateL2_sub_le_sq_of_tsupport_subset_ball
        (E := E) (ψ := ψ) hψc hψcs hψ0 hψint (δ := ε / 2) (η := ε / 2) hη hψsupp (T x) hmod
    simpa [hxEq] using hbound
  have hcomp : IsCompact (closure (T '' Metric.closedBall (0 : ↥(h1On (E := E) K hKm)) 1)) := by
    have hR : 0 ≤ C := hCnonneg
    have hA_eq :
        T '' Metric.closedBall (0 : ↥(h1On (E := E) K hKm)) 1 =
          L2Compactness.extendByZeroL2 (E := E) (K := K) hKm '' A := by
      ext y
      constructor
      · intro hy
        rcases hy with ⟨x, hx, rfl⟩
        have hxRange :
            (h1ToL2 (μ := (volume : Measure E)) (E := E) (x : H1vol)) ∈
              LinearMap.range
                ((MeasureTheory.Lp.extendByZeroₗᵢ
                      (μ := (volume : Measure E)) (E := ℝ)
                      (p := (2 : ℝ≥0∞)) (s := K) hKm).toLinearMap) := by
          -- Unfold membership in the defining `comap` without
          -- letting `simp` use `x.property`
          -- (which would rewrite the goal to `True`).
          have hxmem :
              (x : H1vol) ∈ h1On (E := E) K hKm := x.property
          dsimp [h1On] at hxmem
          change
              ((h1ToL2 (μ := (volume : Measure E)) (E := E)).toLinearMap
                    (x : H1vol)) ∈
                LinearMap.range
                  ((MeasureTheory.Lp.extendByZeroₗᵢ
                        (μ := (volume : Measure E)) (E := ℝ)
                        (p := (2 : ℝ≥0∞))
                        (s := K) hKm).toLinearMap)
          exact hxmem
        rcases hxRange with ⟨u, hu⟩
        have hu0 :
            (MeasureTheory.Lp.extendByZeroₗᵢ
                  (μ := (volume : Measure E)) (E := ℝ) (p := (2 : ℝ≥0∞)) (s := K) hKm) u =
              h1ToL2 (μ := (volume : Measure E)) (E := E) (x : H1vol) := by
          simpa using hu
        have hTx : T x = L2Compactness.extendByZeroL2 (E := E) (K := K) hKm u := by
          calc
            T x = h1ToL2 (μ := (volume : Measure E)) (E := E) (x : H1vol) := by
                  simp [T, h1OnToL2]
            _ = (MeasureTheory.Lp.extendByZeroₗᵢ
                  (μ := (volume : Measure E)) (E := ℝ) (p := (2 : ℝ≥0∞)) (s := K) hKm) u := by
                  simpa using hu0.symm
            _ = L2Compactness.extendByZeroL2 (E := E) (K := K) hKm u := by
                  simpa using
                    (L2Compactness.extendByZeroL2_eq_extendByZeroₗᵢ (E := E) (K := K) hKm u).symm
        refine ⟨u, ?_, hTx.symm⟩
        exact ⟨x, hx, hTx⟩
      · intro hy
        rcases hy with ⟨u, huA, rfl⟩
        exact huA
    have : IsCompact
        (closure (L2Compactness.extendByZeroL2 (E := E) (K := K) hKm '' A)) :=
    L2Compactness.isCompact_closure_extendByZeroL2_image_of_forall_exists_translationIntegral_small
      (E := E) (K := K) (hK := (_hK : IsCompact K))
      (hKm := hKm) hR hA_ball hApprox
    simpa [hA_eq] using this
  -- Use the topological definition of `IsCompactOperator` to avoid expensive normed-space
  -- characterizations.
  refine ⟨closure (T '' Metric.closedBall (0 : ↥(h1On (E := E) K hKm)) 1), hcomp, ?_⟩
  have hball :
      Metric.ball (0 : ↥(h1On (E := E) K hKm)) 1 ⊆
        T ⁻¹' closure (T '' Metric.closedBall (0 : ↥(h1On (E := E) K hKm)) 1) := by
    intro x hx
    refine subset_closure ?_
    refine ⟨x, ?_, rfl⟩
    exact Metric.ball_subset_closedBall hx
  exact Filter.mem_of_superset
    (Metric.ball_mem_nhds (x := (0 : ↥(h1On (E := E) K hKm))) (ε := (1 : ℝ)) hr) hball

/-!
### Codomain restriction and a compact map into `L²(volume.restrict K)`

The definition of `h1On` forces the image of `h1OnToL2` to lie in the (closed) range of the
extension-by-zero map from `volume.restrict K`. We record a codomain-restricted version and a
convenient compact map to the restricted `L²` space.
-/

end Volume

end

end Euclidean
end Sobolev
end FunctionalSpaces
end Analysis
end RellichKondrachov
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_RealMollification
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.complexMollification_im _root_.OAI.ContinuumCoulomb.complexMollification_re _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Smooth approximation of real L² functions on the actual configuration
space. Fatou and the contraction estimate suffice; no Sobolev density input
is used. This is the scalar approximation needed for the H=W discharge. -/

noncomputable section
open MeasureTheory Filter ContinuousLinearMap
open scoped Topology Convolution
namespace ContinuumCoulomb

private theorem l2_error_eventually_lt {n : ℕ}
    (u : Configuration n → ℝ) (v : ℕ → Configuration n → ℝ)
    (hu : MemLp u 2) (hv : ∀ k, MemLp (v k) 2)
    (ht : ∀ᵐ x, Tendsto (fun k => v k x) atTop (𝓝 (u x)))
    (hb : ∀ k, (∫ x, v k x ^ 2) ≤ ∫ x, u x ^ 2)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ k in atTop, (∫ x, (v k x-u x)^2) < ε := by
  by_contra h
  have hfreq : ∃ᶠ k in atTop, ε ≤ ∫ x, (v k x-u x)^2 := by
    simpa only [Filter.Frequently,not_le,not_not] using h
  obtain ⟨ns,hns,hbad⟩ := exists_seq_forall_of_frequently hfreq
  have hsum (k : ℕ) :
      (∫ x, (v k x+u x)^2)+(∫ x, (v k x-u x)^2) =
        2*(∫ x, v k x^2)+2*(∫ x, u x^2) := by
    calc
      _ = ∫ x, (v k x+u x)^2+(v k x-u x)^2 :=
        (integral_add ((hv k).add hu).integrable_sq ((hv k).sub hu).integrable_sq).symm
      _ = ∫ x, 2*v k x^2+2*u x^2 := by
        apply integral_congr_ae
        exact Eventually.of_forall (fun _ => by ring)
      _ = _ := by
        rw [integral_add ((hv k).integrable_sq.const_mul 2) (hu.integrable_sq.const_mul 2),
          integral_const_mul,integral_const_mul]
  have hlim : ∀ᵐ x, Tendsto (fun k => (v (ns k) x+u x)^2)
      atTop (𝓝 (4*u x^2)) := by
    filter_upwards [ht] with x hx
    have he : (u x+u x)^2 = 4*u x^2 := by ring
    simpa only [Function.comp_apply,he] using ((hx.comp hns).add_const (u x)).pow 2
  have hbound (k : ℕ) : (∫ x, (v (ns k) x+u x)^2) ≤
      4*(∫ x, u x^2)-ε := by
    have hs := hsum (ns k)
    have hb' := hb (ns k)
    have he := hbad k
    linarith
  have hf := Coulomb.ae_nonneg_fatou_integrable volume (fun x => 4*u x^2)
    (fun k x => (v (ns k) x+u x)^2) (4*(∫ x, u x^2)-ε)
    (fun k => ((hv (ns k)).add hu).integrable_sq)
    (fun k x => sq_nonneg (v (ns k) x+u x))
    (fun x => mul_nonneg (by norm_num) (sq_nonneg (u x)))
    hlim hbound
  rw [integral_const_mul] at hf
  linarith [hf.2]

theorem realMollification_error {n : ℕ} {u : Configuration n → ℝ}
    (hu : MemLp u 2) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ k in atTop, (∫ x, (realMollification u k x-u x)^2) < ε := by
  apply l2_error_eventually_lt u (realMollification u) hu
    (fun k => (realMollification_contraction hu k).1) ?_
    (fun k => (realMollification_contraction hu k).2) hε
  apply ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable
    (φ := fun k => Coulomb.hardyMollifier k) (K := 2)
    Coulomb.hardyMollifier_tendsto _ (hu.locallyIntegrable (by norm_num))
  apply Eventually.of_forall
  intro k
  simp only [Coulomb.hardyMollifier]
  simp only [mul_one_div,le_refl]

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_ComplexMollification
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Componentwise mollification preserves the actual complex weak derivatives.
All estimates here are unconditional. -/

noncomputable section
open MeasureTheory Filter ContinuousLinearMap
open scoped Topology Convolution
namespace ContinuumCoulomb

theorem complexMollification_error {n : ℕ} {u : Configuration n → ℂ}
    (hu : MemLp u 2) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ k in atTop, (∫ x, ‖u x-complexMollification u k x‖^2) < ε := by
  have hr := realMollification_error (re_memLp hu) (half_pos hε)
  have hi := realMollification_error (im_memLp hu) (half_pos hε)
  filter_upwards [hr,hi] with k hkr hki
  have he : (∫ x, ‖u x-complexMollification u k x‖^2) =
      (∫ x, (realMollification (fun y => (u y).re) k x-(u x).re)^2)+
      (∫ x, (realMollification (fun y => (u y).im) k x-(u x).im)^2) := by
    have hR : Integrable (fun x =>
        (realMollification (fun y => (u y).re) k x-(u x).re)^2) := by
      simpa only [Pi.sub_apply] using
        ((realMollification_contraction (re_memLp hu) k).1.sub (re_memLp hu)).integrable_sq
    have hI : Integrable (fun x =>
        (realMollification (fun y => (u y).im) k x-(u x).im)^2) := by
      simpa only [Pi.sub_apply] using
        ((realMollification_contraction (im_memLp hu) k).1.sub (im_memLp hu)).integrable_sq
    rw [← integral_add hR hI]
    apply integral_congr_ae
    apply Eventually.of_forall
    intro x
    dsimp only
    rw [Coulomb.complex_norm_sq_components]
    simp only [Complex.sub_re,Complex.sub_im,complexMollification_re,complexMollification_im]
    ring
  rw [he]
  linarith

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.KLS_Sobolev_TestFunctions
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.gaussianLineEquiv_apply _root_.OAI.LeanBlast.KLS.blMomentDeriv_zero _root_.OAI.LeanBlast.KLS.blMoment_zero _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set MeasureTheory InnerProductSpace
open scoped ContDiff

namespace LeanBlast.KLS

variable {n : ℕ} {f : Space n → ℝ}

theorem IsTestFunction.continuous (hf : IsTestFunction f) : Continuous f :=
  hf.1.continuous

theorem IsTestFunction.continuous_gradient (hf : IsTestFunction f) :
    Continuous (gradient f) := by
  exact (toDual ℝ (Space n)).symm.continuous.comp
    (hf.1.continuous_fderiv (by simp))

theorem IsTestFunction.hasCompactSupport_gradient (hf : IsTestFunction f) :
    HasCompactSupport (gradient f) := by
  exact (hf.2.fderiv ℝ).comp_left
    (g := (toDual ℝ (Space n)).symm) (by simp)

theorem IsTestFunction.integrable (hf : IsTestFunction f)
    (μ : Measure (Space n)) [IsFiniteMeasure μ] : Integrable f μ :=
  hf.continuous.integrable_of_hasCompactSupport hf.2

theorem IsTestFunction.integrable_sq (hf : IsTestFunction f)
    (μ : Measure (Space n)) [IsFiniteMeasure μ] :
    Integrable (fun x => (f x) ^ 2) μ := by
  have hsupport := HasCompactSupport.comp_left (f := f)
    (g := fun value : ℝ => value ^ 2) hf.2 (by simp)
  exact (hf.continuous.pow 2).integrable_of_hasCompactSupport hsupport

theorem IsTestFunction.integrable_gradient_sq (hf : IsTestFunction f)
    (μ : Measure (Space n)) [IsFiniteMeasure μ] :
    Integrable (fun x => ‖gradient f x‖ ^ 2) μ := by
  have hsupport := HasCompactSupport.comp_left (f := gradient f)
    (g := fun vector : Space n => ‖vector‖ ^ 2) hf.hasCompactSupport_gradient (by simp)
  exact (hf.continuous_gradient.norm.pow 2).integrable_of_hasCompactSupport hsupport

end LeanBlast.KLS

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.KLS_Measures_PotentialMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
open scoped ENNReal ContDiff

namespace LeanBlast.KLS

variable {n : ℕ}

theorem potentialPartition_pos {V : Space n → ℝ}
    (hV : Integrable (fun x => Real.exp (-V x))) : 0 < potentialPartition V :=
  integral_exp_pos hV

theorem isProbabilityMeasure_potentialMeasure {V : Space n → ℝ}
    (hV : Integrable (fun x => Real.exp (-V x))) :
    IsProbabilityMeasure (potentialMeasure V) :=
  isProbabilityMeasure_tilted hV

theorem integral_potentialMeasure (V g : Space n → ℝ) :
    (∫ x, g x ∂potentialMeasure V) =
      (∫ x, Real.exp (-V x) * g x) / potentialPartition V := by
  rw [potentialMeasure, integral_tilted]
  simp only [smul_eq_mul]
  simp_rw [div_mul_eq_mul_div]
  simpa only [div_eq_mul_inv, potentialPartition] using
    integral_mul_const (potentialPartition V)⁻¹ (fun x => Real.exp (-V x) * g x)

theorem integrable_potentialMeasure_iff {V : Space n → ℝ}
    (hV : Integrable (fun x => Real.exp (-V x))) (g : Space n → ℝ) :
    Integrable g (potentialMeasure V) ↔ Integrable (fun x => Real.exp (-V x) * g x) := by
  simpa only [potentialMeasure, smul_eq_mul] using integrable_tilted_iff hV g

theorem variance_eq_integral_sq_sub_sq (μ : Measure (Space n)) [IsProbabilityMeasure μ]
    {h : Space n → ℝ} (hh : Integrable h μ) (hh2 : Integrable (fun x => (h x) ^ 2) μ) :
    variance μ h = (∫ x, (h x) ^ 2 ∂μ) - (∫ x, h x ∂μ) ^ 2 := by
  unfold variance expectation
  have heq : (fun x => (h x - ∫ y, h y ∂μ) ^ 2) =
      fun x => ((h x) ^ 2 - (2 * ∫ y, h y ∂μ) * h x) + (∫ y, h y ∂μ) ^ 2 := by
    funext x
    ring
  rw [heq]
  rw [integral_add (f := fun x => h x ^ 2 - (2 * ∫ y, h y ∂μ) * h x)
    (g := fun _ => (∫ y, h y ∂μ) ^ 2)
    (hh2.sub (hh.const_mul _)) (integrable_const _)]
  rw [integral_sub (f := fun x => h x ^ 2) (g := fun x => (2 * ∫ y, h y ∂μ) * h x)
    hh2 (hh.const_mul _), integral_const_mul, integral_const]
  simp only [probReal_univ, one_smul]
  ring

end LeanBlast.KLS

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.KLS_Stein_SteinHessianDefs
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.gaussianLineEquiv_apply _root_.OAI.LeanBlast.KLS.blMomentDeriv_zero _root_.OAI.LeanBlast.KLS.blMoment_zero _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Matrix
open scoped BigOperators ContDiff

namespace LeanBlast.KLS

theorem hessianMatrix_isSymm {n : ℕ} {f : Space n → ℝ} {x : Space n}
    (hf : ContDiffAt ℝ 2 f x) : (hessianMatrix f x).IsSymm := by
  apply Matrix.IsSymm.ext
  intro i j
  exact (hf.isSymmSndFDerivAt (by norm_num)).eq _ _

end LeanBlast.KLS

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.KLS_Regularization_RegularPotential
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff

namespace LeanBlast.KLS

theorem IsRegularPotential.hessian_pos {n : ℕ} {V : Space n → ℝ} {t t' : ℝ}
    (hV : IsRegularPotential V t t') (x : Space n) {v : Space n} (hv : v ≠ 0) :
    0 < fderiv ℝ (fderiv ℝ V) x v v :=
  (mul_pos hV.lower_pos (sq_pos_of_pos (norm_pos_iff.mpr hv))).trans_le (hV.lower_bound x v)

end LeanBlast.KLS

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.KLS_Convexity_PrekopaLeindler
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal NNReal Pointwise Topology

namespace AsymptoticStatistics

private theorem prekopaLeindler_1d_levelInclusion
    {f g h : ℝ → ℝ≥0∞}
    {t : ℝ} (ht_pos : 0 < t) (ht_lt : t < 1)
    (h_le : ∀ x y : ℝ,
      f x ^ t * g y ^ (1 - t) ≤ h (t * x + (1 - t) * y))
    {α : ℝ≥0∞} (hα_pos : 0 < α) (hα_top : α ≠ ⊤) :
    t • {x | α < f x} + (1 - t) • {y | α < g y} ⊆ {z | α < h z} := by
  have h1t_pos : 0 < 1 - t := sub_pos.mpr ht_lt
  rintro z hz
  rw [Set.mem_add] at hz
  obtain ⟨_, hu, _, hv, rfl⟩ := hz
  rw [Set.mem_smul_set] at hu hv
  obtain ⟨x, hx, rfl⟩ := hu
  obtain ⟨y, hy, rfl⟩ := hv

  simp only [smul_eq_mul, Set.mem_ofPred_eq] at hx hy ⊢

  have h_alpha_split : α = α ^ t * α ^ (1 - t) := by
    rw [← ENNReal.rpow_add t (1 - t) hα_pos.ne' hα_top]
    have ht_one : t + (1 - t) = (1 : ℝ) := by ring
    rw [ht_one, ENNReal.rpow_one]

  have h1 : α ^ t < f x ^ t := ENNReal.rpow_lt_rpow hx ht_pos
  have h2 : α ^ (1 - t) < g y ^ (1 - t) := ENNReal.rpow_lt_rpow hy h1t_pos

  have h3 : α ^ t * α ^ (1 - t) < f x ^ t * g y ^ (1 - t) := ENNReal.mul_lt_mul h1 h2

  calc α = α ^ t * α ^ (1 - t) := h_alpha_split
    _ < f x ^ t * g y ^ (1 - t) := h3
    _ ≤ h (t * x + (1 - t) * y) := h_le x y

private lemma oneDim_brunn_minkowski_compact_le
    {K_A K_B : Set ℝ}
    (hA_compact : IsCompact K_A) (hB_compact : IsCompact K_B)
    (hA_ne : K_A.Nonempty) (hB_ne : K_B.Nonempty) :
    volume K_A + volume K_B ≤ volume (K_A + K_B) := by

  set a := sSup K_A with ha_def
  set b := sInf K_B with hb_def
  have ha_mem : a ∈ K_A := hA_compact.sSup_mem hA_ne
  have hb_mem : b ∈ K_B := hB_compact.sInf_mem hB_ne
  have hA_le_a : ∀ x ∈ K_A, x ≤ a :=
    fun x hx => le_csSup hA_compact.bddAbove hx
  have hB_ge_b : ∀ y ∈ K_B, b ≤ y :=
    fun y hy => csInf_le hB_compact.bddBelow hy

  set U : Set ℝ := K_A + {b} with hU_def
  set V : Set ℝ := {a} + K_B with hV_def

  have hU_sub_AB : U ⊆ K_A + K_B := by
    rintro _ ⟨x, hx, _, rfl, rfl⟩
    exact ⟨x, hx, b, hb_mem, rfl⟩
  have hV_sub_AB : V ⊆ K_A + K_B := by
    rintro _ ⟨_, rfl, y, hy, rfl⟩
    exact ⟨a, ha_mem, y, hy, rfl⟩

  have hU_vol : volume U = volume K_A := by
    rw [hU_def, Set.add_singleton, Set.image_add_right]
    exact MeasureTheory.measure_preimage_add_right volume (-b) K_A

  have hV_vol : volume V = volume K_B := by
    rw [hV_def, Set.singleton_add, Set.image_add_left]
    exact MeasureTheory.measure_preimage_add volume (-a) K_B

  have hU_sub_Iic : U ⊆ Set.Iic (a + b) := by
    rintro _ ⟨x, hx, _, rfl, rfl⟩
    have := hA_le_a x hx
    simp only [Set.mem_Iic]
    linarith

  have hV_sub_Ici : V ⊆ Set.Ici (a + b) := by
    rintro _ ⟨_, rfl, y, hy, rfl⟩
    have := hB_ge_b y hy
    simp only [Set.mem_Ici]
    linarith

  have h_inter_sub : U ∩ V ⊆ {a + b} := by
    rintro z ⟨hzU, hzV⟩
    have h1 := hU_sub_Iic hzU
    have h2 := hV_sub_Ici hzV
    simp only [Set.mem_Iic] at h1
    simp only [Set.mem_Ici] at h2
    simp only [Set.mem_singleton_iff]
    linarith

  have h_inter_zero : volume (U ∩ V) = 0 := by
    apply le_antisymm _ (by positivity)
    calc volume (U ∩ V)
        ≤ volume ({a + b} : Set ℝ) := MeasureTheory.measure_mono h_inter_sub
      _ = 0 := MeasureTheory.measure_singleton (a + b)

  have hV_meas : MeasurableSet V := by
    rw [hV_def, Set.singleton_add, Set.image_add_left]
    exact (hB_compact.measurableSet).preimage (measurable_const_add (-a))
  have h_inc_excl : volume (U ∪ V) + volume (U ∩ V) = volume U + volume V :=
    MeasureTheory.measure_union_add_inter U hV_meas

  have h_union_sub : U ∪ V ⊆ K_A + K_B := Set.union_subset hU_sub_AB hV_sub_AB
  have h_union_le : volume (U ∪ V) ≤ volume (K_A + K_B) :=
    MeasureTheory.measure_mono h_union_sub

  calc volume K_A + volume K_B
      = volume U + volume V := by rw [hU_vol, hV_vol]
    _ = volume (U ∪ V) + volume (U ∩ V) := h_inc_excl.symm
    _ = volume (U ∪ V) + 0 := by rw [h_inter_zero]
    _ = volume (U ∪ V) := add_zero _
    _ ≤ volume (K_A + K_B) := h_union_le

private theorem oneDim_brunn_minkowski_le
    {A B C : Set ℝ}
    (hA_meas : MeasurableSet A) (hB_meas : MeasurableSet B)
    (_hC_meas : MeasurableSet C)
    (hA_ne : A.Nonempty) (hB_ne : B.Nonempty)
    (hAB_sub : A + B ⊆ C) :
    volume A + volume B ≤ volume C := by

  by_cases hA_zero : volume A = 0
  · obtain ⟨a₀, ha₀⟩ := hA_ne
    have h_aB_sub_C : ({a₀} : Set ℝ) + B ⊆ C := fun z ⟨_, rfl, y, hy, hyz⟩ =>
      hAB_sub ⟨a₀, ha₀, y, hy, hyz⟩
    have h_aB_eq : volume (({a₀} : Set ℝ) + B) = volume B := by
      rw [Set.singleton_add, Set.image_add_left]
      exact MeasureTheory.measure_preimage_add volume (-a₀) B
    rw [hA_zero, zero_add]
    calc volume B = volume (({a₀} : Set ℝ) + B) := h_aB_eq.symm
      _ ≤ volume C := MeasureTheory.measure_mono h_aB_sub_C

  by_cases hB_zero : volume B = 0
  · obtain ⟨b₀, hb₀⟩ := hB_ne
    have h_Ab_sub_C : A + ({b₀} : Set ℝ) ⊆ C := fun z ⟨x, hx, _, rfl, hxz⟩ =>
      hAB_sub ⟨x, hx, b₀, hb₀, hxz⟩
    have h_Ab_eq : volume (A + ({b₀} : Set ℝ)) = volume A := by
      rw [Set.add_singleton, Set.image_add_right]
      exact MeasureTheory.measure_preimage_add_right volume (-b₀) A
    rw [hB_zero, add_zero]
    calc volume A = volume (A + ({b₀} : Set ℝ)) := h_Ab_eq.symm
      _ ≤ volume C := MeasureTheory.measure_mono h_Ab_sub_C

  by_cases hA_top : volume A = ⊤
  · obtain ⟨b₀, hb₀⟩ := hB_ne
    suffices h_C_top : volume C = ⊤ by
      rw [hA_top, h_C_top]; exact le_top
    apply top_le_iff.mp
    have h_inner :
        volume A = ⨆ (K : Set ℝ), ⨆ (_ : K ⊆ A), ⨆ (_ : IsCompact K), volume K :=
      MeasureTheory.Measure.InnerRegularWRT.measure_eq_iSup
        MeasureTheory.Measure.InnerRegular.innerRegular hA_meas
    calc (⊤ : ℝ≥0∞)
        = volume A := hA_top.symm
      _ = ⨆ (K : Set ℝ), ⨆ (_ : K ⊆ A), ⨆ (_ : IsCompact K), volume K := h_inner
      _ ≤ volume C := by
          refine iSup_le fun K_A => iSup_le fun hK_A_sub => iSup_le fun _ => ?_
          have h_KA_b0_sub : K_A + ({b₀} : Set ℝ) ⊆ C :=
            fun z ⟨x, hx, _, rfl, hxz⟩ => hAB_sub ⟨x, hK_A_sub hx, b₀, hb₀, hxz⟩
          have h_KA_b0_eq : volume (K_A + ({b₀} : Set ℝ)) = volume K_A := by
            rw [Set.add_singleton, Set.image_add_right]
            exact MeasureTheory.measure_preimage_add_right volume (-b₀) K_A
          calc volume K_A
              = volume (K_A + ({b₀} : Set ℝ)) := h_KA_b0_eq.symm
            _ ≤ volume C := MeasureTheory.measure_mono h_KA_b0_sub

  by_cases hB_top : volume B = ⊤
  · obtain ⟨a₀, ha₀⟩ := hA_ne
    suffices h_C_top : volume C = ⊤ by
      rw [hB_top, h_C_top]; exact le_top
    apply top_le_iff.mp
    have h_inner :
        volume B = ⨆ (K : Set ℝ), ⨆ (_ : K ⊆ B), ⨆ (_ : IsCompact K), volume K :=
      MeasureTheory.Measure.InnerRegularWRT.measure_eq_iSup
        MeasureTheory.Measure.InnerRegular.innerRegular hB_meas
    calc (⊤ : ℝ≥0∞)
        = volume B := hB_top.symm
      _ = ⨆ (K : Set ℝ), ⨆ (_ : K ⊆ B), ⨆ (_ : IsCompact K), volume K := h_inner
      _ ≤ volume C := by
          refine iSup_le fun K_B => iSup_le fun hK_B_sub => iSup_le fun _ => ?_
          have h_a0_KB_sub : ({a₀} : Set ℝ) + K_B ⊆ C :=
            fun z ⟨_, rfl, y, hy, hyz⟩ => hAB_sub ⟨a₀, ha₀, y, hK_B_sub hy, hyz⟩
          have h_a0_KB_eq : volume (({a₀} : Set ℝ) + K_B) = volume K_B := by
            rw [Set.singleton_add, Set.image_add_left]
            exact MeasureTheory.measure_preimage_add volume (-a₀) K_B
          calc volume K_B
              = volume (({a₀} : Set ℝ) + K_B) := h_a0_KB_eq.symm
            _ ≤ volume C := MeasureTheory.measure_mono h_a0_KB_sub

  apply ENNReal.le_of_forall_pos_le_add
  intro ε hε _hC_top

  set δ : ℝ≥0∞ := (ε : ℝ≥0∞) / 2 with hδ_def
  have hδ_pos : (0 : ℝ≥0∞) < δ := by
    rw [hδ_def]
    refine ENNReal.div_pos ?_ (by norm_num)
    exact_mod_cast hε.ne'
  have hδ_ne : δ ≠ 0 := hδ_pos.ne'
  have hδ_le : δ ≤ ε := by
    rw [hδ_def]; exact ENNReal.half_le_self

  obtain ⟨K_A, hK_A_sub, hK_A_compact, hK_A_lt⟩ :=
    hA_meas.exists_isCompact_lt_add hA_top hδ_ne
  obtain ⟨K_B, hK_B_sub, hK_B_compact, hK_B_lt⟩ :=
    hB_meas.exists_isCompact_lt_add hB_top hδ_ne

  rcases K_A.eq_empty_or_nonempty with hKA_empty | hKA_ne
  ·
    rw [hKA_empty, MeasureTheory.measure_empty, zero_add] at hK_A_lt

    have hA_le_ε : volume A ≤ (ε : ℝ≥0∞) := le_trans hK_A_lt.le hδ_le

    obtain ⟨a₀, ha₀⟩ := hA_ne
    have h_aB_sub_C : ({a₀} : Set ℝ) + B ⊆ C := fun z ⟨_, rfl, y, hy, hyz⟩ =>
      hAB_sub ⟨a₀, ha₀, y, hy, hyz⟩
    have h_aB_eq : volume (({a₀} : Set ℝ) + B) = volume B := by
      rw [Set.singleton_add, Set.image_add_left]
      exact MeasureTheory.measure_preimage_add volume (-a₀) B
    have hB_le_C : volume B ≤ volume C := by
      rw [← h_aB_eq]; exact MeasureTheory.measure_mono h_aB_sub_C
    calc volume A + volume B ≤ (ε : ℝ≥0∞) + volume C := add_le_add hA_le_ε hB_le_C
      _ = volume C + (ε : ℝ≥0∞) := add_comm _ _
  rcases K_B.eq_empty_or_nonempty with hKB_empty | hKB_ne
  ·
    rw [hKB_empty, MeasureTheory.measure_empty, zero_add] at hK_B_lt
    have hB_le_ε : volume B ≤ (ε : ℝ≥0∞) := le_trans hK_B_lt.le hδ_le
    obtain ⟨b₀, hb₀⟩ := hB_ne
    have h_Ab_sub_C : A + ({b₀} : Set ℝ) ⊆ C := fun z ⟨x, hx, _, rfl, hxz⟩ =>
      hAB_sub ⟨x, hx, b₀, hb₀, hxz⟩
    have h_Ab_eq : volume (A + ({b₀} : Set ℝ)) = volume A := by
      rw [Set.add_singleton, Set.image_add_right]
      exact MeasureTheory.measure_preimage_add_right volume (-b₀) A
    have hA_le_C : volume A ≤ volume C := by
      rw [← h_Ab_eq]; exact MeasureTheory.measure_mono h_Ab_sub_C
    exact add_le_add hA_le_C hB_le_ε
  ·
    have hKAB_sub : K_A + K_B ⊆ C :=
      fun z ⟨x, hx, y, hy, hxyz⟩ =>
        hAB_sub ⟨x, hK_A_sub hx, y, hK_B_sub hy, hxyz⟩
    have h_compact_bm := oneDim_brunn_minkowski_compact_le
      hK_A_compact hK_B_compact hKA_ne hKB_ne
    have h_KAKB_le_C : volume (K_A + K_B) ≤ volume C :=
      MeasureTheory.measure_mono hKAB_sub

    have h_2δ_le_ε : (2 : ℝ≥0∞) * δ ≤ (ε : ℝ≥0∞) := by
      rw [hδ_def]; exact ENNReal.mul_div_le
    calc volume A + volume B
        ≤ (volume K_A + δ) + (volume K_B + δ) := by gcongr
      _ = (volume K_A + volume K_B) + (δ + δ) := by ring
      _ = (volume K_A + volume K_B) + 2 * δ := by ring
      _ ≤ volume C + 2 * δ := by
          gcongr
          exact le_trans h_compact_bm h_KAKB_le_C
      _ ≤ volume C + (ε : ℝ≥0∞) := by gcongr

private theorem prekopaLeindler_1d_levelMeasureBound
    {f g h : ℝ → ℝ≥0∞}
    (hf_meas : Measurable f) (hg_meas : Measurable g) (hh_meas : Measurable h)
    {t : ℝ} (ht_pos : 0 < t) (ht_lt : t < 1)
    (h_le : ∀ x y : ℝ,
      f x ^ t * g y ^ (1 - t) ≤ h (t * x + (1 - t) * y))
    {α : ℝ≥0∞} (hα_pos : 0 < α) (hα_top : α ≠ ⊤)
    (hA_ne : ({x | α < f x} : Set ℝ).Nonempty)
    (hB_ne : ({y | α < g y} : Set ℝ).Nonempty) :
    ENNReal.ofReal t * volume {x | α < f x}
      + ENNReal.ofReal (1 - t) * volume {y | α < g y}
      ≤ volume {z | α < h z} := by
  have h1t_pos : 0 < 1 - t := sub_pos.mpr ht_lt
  set A : Set ℝ := {x | α < f x} with hA_def
  set B : Set ℝ := {y | α < g y} with hB_def
  set C : Set ℝ := {z | α < h z} with hC_def

  have hA_meas : MeasurableSet A := hf_meas measurableSet_Ioi
  have hB_meas : MeasurableSet B := hg_meas measurableSet_Ioi
  have hC_meas : MeasurableSet C := hh_meas measurableSet_Ioi

  have h_incl : t • A + (1 - t) • B ⊆ C :=
    prekopaLeindler_1d_levelInclusion ht_pos ht_lt h_le hα_pos hα_top

  have htA_meas : MeasurableSet (t • A) :=
    hA_meas.const_smul_of_ne_zero ht_pos.ne'
  have h1tB_meas : MeasurableSet ((1 - t) • B) :=
    hB_meas.const_smul_of_ne_zero h1t_pos.ne'

  have htA_ne : (t • A).Nonempty := Set.smul_set_nonempty.mpr hA_ne
  have h1tB_ne : ((1 - t) • B).Nonempty := Set.smul_set_nonempty.mpr hB_ne

  have h_bm : volume (t • A) + volume ((1 - t) • B) ≤ volume C :=
    oneDim_brunn_minkowski_le htA_meas h1tB_meas hC_meas htA_ne h1tB_ne h_incl

  have h_finrank : Module.finrank ℝ ℝ = 1 := CommSemiring.finrank_self ℝ
  have h_smul_t : volume (t • A) = ENNReal.ofReal t * volume A := by
    rw [Measure.addHaar_smul_of_nonneg volume ht_pos.le A, h_finrank, pow_one]
  have h_smul_1t : volume ((1 - t) • B) = ENNReal.ofReal (1 - t) * volume B := by
    rw [Measure.addHaar_smul_of_nonneg volume h1t_pos.le B, h_finrank, pow_one]
  rw [← h_smul_t, ← h_smul_1t]
  exact h_bm

private theorem lintegral_eq_lintegral_meas_lt_ennreal
    {f : ℝ → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ x, f x = ∫⁻ α in Ioi (0 : ℝ), volume {x | ENNReal.ofReal α < f x} := by

  set fN : ℕ → ℝ → ℝ≥0∞ := fun n x => f x ⊓ (n : ℝ≥0∞) with hfN_def
  have hfN_meas : ∀ n, Measurable (fN n) :=
    fun n => hf.inf measurable_const
  have hfN_lt_top : ∀ n x, fN n x ≠ ⊤ :=
    fun n x => ne_top_of_le_ne_top ENNReal.coe_ne_top inf_le_right
  have hfN_mono : Monotone fN := by
    intro m n hmn x
    exact inf_le_inf_left _ (by exact_mod_cast hmn)
  have hfN_iSup_eq : ∀ x, ⨆ n, fN n x = f x := fun x => by
    simp only [fN]
    rw [← inf_iSup_eq, ENNReal.iSup_natCast, inf_top_eq]

  have hLHS : ∫⁻ x, f x = ⨆ n, ∫⁻ x, fN n x := by
    rw [← MeasureTheory.lintegral_iSup hfN_meas hfN_mono]
    exact MeasureTheory.lintegral_congr fun x => (hfN_iSup_eq x).symm

  have h_per_n : ∀ n, ∫⁻ x, fN n x =
      ∫⁻ α in Ioi (0 : ℝ), volume {x | ENNReal.ofReal α < fN n x} := by
    intro n
    have h_eq : ∫⁻ x, fN n x = ∫⁻ x, ENNReal.ofReal ((fN n x).toReal) :=
      MeasureTheory.lintegral_congr fun x => (ENNReal.ofReal_toReal (hfN_lt_top n x)).symm
    rw [h_eq, MeasureTheory.lintegral_eq_lintegral_meas_lt volume
        (Filter.Eventually.of_forall fun _ => ENNReal.toReal_nonneg)
        ((hfN_meas n).ennreal_toReal.aemeasurable)]

    apply MeasureTheory.setLIntegral_congr_fun measurableSet_Ioi
    intro α hα
    have hα_nn : (0 : ℝ) ≤ α := le_of_lt hα
    change volume {x | α < (fN n x).toReal}
        = volume {x | ENNReal.ofReal α < fN n x}
    congr 1
    ext x
    simp only [Set.mem_ofPred_eq]
    refine ⟨fun h => ?_, fun h => ?_⟩
    · have := (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hα_nn).mpr h
      rwa [ENNReal.ofReal_toReal (hfN_lt_top n x)] at this
    · have h' : ENNReal.ofReal α < ENNReal.ofReal ((fN n x).toReal) := by
        rwa [ENNReal.ofReal_toReal (hfN_lt_top n x)]
      exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hα_nn).mp h'

  have h_set_mono : ∀ α : ℝ,
      Monotone fun n : ℕ => {x | ENNReal.ofReal α < fN n x} := by
    intro α m n hmn x hx
    exact lt_of_lt_of_le hx (hfN_mono hmn x)
  have h_set_iUnion : ∀ α : ℝ,
      ⋃ n : ℕ, {x | ENNReal.ofReal α < fN n x}
        = {x | ENNReal.ofReal α < f x} := by
    intro α
    ext x
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq]
    refine ⟨fun ⟨n, hn⟩ => lt_of_lt_of_le hn (le_trans inf_le_left le_rfl), ?_⟩
    intro hx
    rw [← hfN_iSup_eq x] at hx
    exact lt_iSup_iff.mp hx

  have h_meas_vol : ∀ n,
      Measurable fun α : ℝ => volume {x | ENNReal.ofReal α < fN n x} := by
    intro n

    have h_set_meas : MeasurableSet
        {p : ℝ × ℝ | ENNReal.ofReal p.1 < fN n p.2} :=
      measurableSet_lt (ENNReal.measurable_ofReal.comp measurable_fst)
        ((hfN_meas n).comp measurable_snd)

    exact measurable_measure_prodMk_left h_set_meas
  have hRHS : ∫⁻ α in Ioi (0 : ℝ), volume {x | ENNReal.ofReal α < f x}
        = ⨆ n, ∫⁻ α in Ioi (0 : ℝ), volume {x | ENNReal.ofReal α < fN n x} := by
    rw [show (fun α => volume {x | ENNReal.ofReal α < f x})
          = fun α => ⨆ n, volume {x | ENNReal.ofReal α < fN n x} from
        funext fun α => by rw [← h_set_iUnion α,
          (h_set_mono α).measure_iUnion]]
    exact MeasureTheory.lintegral_iSup (fun n => h_meas_vol n)
      (fun m n hmn α => MeasureTheory.measure_mono (h_set_mono α hmn))
  rw [hLHS, hRHS]
  exact iSup_congr h_per_n

private theorem ennreal_geom_mean_le_arith_mean2_weighted
    {t : ℝ} (ht_pos : 0 < t) (ht_lt : t < 1)
    (a b : ℝ≥0∞) :
    a ^ t * b ^ (1 - t) ≤ ENNReal.ofReal t * a + ENNReal.ofReal (1 - t) * b := by
  have h1t_pos : 0 < 1 - t := sub_pos.mpr ht_lt
  by_cases ha : a = ⊤
  · subst ha
    have h_rhs : ENNReal.ofReal t * ⊤ + ENNReal.ofReal (1 - t) * b = ⊤ := by
      have : ENNReal.ofReal t ≠ 0 := by
        rw [Ne, ENNReal.ofReal_eq_zero]; linarith
      simp [ENNReal.mul_top this]
    rw [h_rhs]; exact le_top
  by_cases hb : b = ⊤
  · subst hb
    have h_rhs : ENNReal.ofReal t * a + ENNReal.ofReal (1 - t) * ⊤ = ⊤ := by
      have : ENNReal.ofReal (1 - t) ≠ 0 := by
        rw [Ne, ENNReal.ofReal_eq_zero]; linarith
      simp [ENNReal.mul_top this]
    rw [h_rhs]; exact le_top

  set A : ℝ := a.toReal with hA_def
  set B : ℝ := b.toReal with hB_def
  have hA_nn : (0 : ℝ) ≤ A := ENNReal.toReal_nonneg
  have hB_nn : (0 : ℝ) ≤ B := ENNReal.toReal_nonneg
  have hofa : ENNReal.ofReal A = a := ENNReal.ofReal_toReal ha
  have hofb : ENNReal.ofReal B = b := ENNReal.ofReal_toReal hb
  have h_real : A ^ t * B ^ (1 - t) ≤ t * A + (1 - t) * B :=
    Real.geom_mean_le_arith_mean2_weighted ht_pos.le h1t_pos.le hA_nn hB_nn
      (by linarith)
  have hAt_nn : (0 : ℝ) ≤ A ^ t := Real.rpow_nonneg hA_nn t
  have hBt_nn : (0 : ℝ) ≤ B ^ (1 - t) := Real.rpow_nonneg hB_nn (1 - t)
  calc a ^ t * b ^ (1 - t)
      = ENNReal.ofReal A ^ t * ENNReal.ofReal B ^ (1 - t) := by rw [hofa, hofb]
    _ = ENNReal.ofReal (A ^ t) * ENNReal.ofReal (B ^ (1 - t)) := by
        rw [ENNReal.ofReal_rpow_of_nonneg hA_nn ht_pos.le,
            ENNReal.ofReal_rpow_of_nonneg hB_nn h1t_pos.le]
    _ = ENNReal.ofReal (A ^ t * B ^ (1 - t)) := by
        rw [← ENNReal.ofReal_mul hAt_nn]
    _ ≤ ENNReal.ofReal (t * A + (1 - t) * B) := ENNReal.ofReal_le_ofReal h_real
    _ = ENNReal.ofReal (t * A) + ENNReal.ofReal ((1 - t) * B) :=
        ENNReal.ofReal_add (mul_nonneg ht_pos.le hA_nn)
          (mul_nonneg h1t_pos.le hB_nn)
    _ = ENNReal.ofReal t * a + ENNReal.ofReal (1 - t) * b := by
        rw [ENNReal.ofReal_mul ht_pos.le, ENNReal.ofReal_mul h1t_pos.le,
            hofa, hofb]

private theorem prekopaLeindler_1d_arithBound
    {f g h : ℝ → ℝ≥0∞}
    (hf_meas : Measurable f) (hg_meas : Measurable g) (hh_meas : Measurable h)
    {t : ℝ} (ht_pos : 0 < t) (ht_lt : t < 1)
    (h_le : ∀ x y : ℝ,
      f x ^ t * g y ^ (1 - t) ≤ h (t * x + (1 - t) * y))
    (h_ess_eq : essSup f volume = essSup g volume) :
    ENNReal.ofReal t * (∫⁻ x, f x) + ENNReal.ofReal (1 - t) * (∫⁻ y, g y)
      ≤ ∫⁻ z, h z := by
  have h1t_pos : 0 < 1 - t := sub_pos.mpr ht_lt
  set M : ℝ≥0∞ := essSup f volume with hM_def

  have h_pos_meas : ∀ {φ : ℝ → ℝ≥0∞}, essSup φ volume = M →
      ∀ {β : ℝ≥0∞}, β < M → 0 < volume {x | β < φ x} := by
    intro φ hφ_ess β hβ
    by_contra h_neg
    rw [not_lt, nonpos_iff_eq_zero] at h_neg
    have h_ae : φ ≤ᵐ[volume] fun _ => β := by
      rw [Filter.EventuallyLE, MeasureTheory.ae_iff]
      simpa using h_neg
    have : essSup φ volume ≤ β := essSup_le_of_ae_le β h_ae
    rw [hφ_ess] at this
    exact absurd this (not_le.mpr hβ)

  have h_null_meas : ∀ {φ : ℝ → ℝ≥0∞}, essSup φ volume = M →
      ∀ {β : ℝ≥0∞}, M ≤ β → volume {x | β < φ x} = 0 := by
    intro φ hφ_ess β hβ
    have h_essSup_le : essSup φ volume ≤ β := hφ_ess.trans_le hβ

    have h_sub : {x | β < φ x} ⊆ {x | essSup φ volume < φ x} :=
      fun x hx => lt_of_le_of_lt h_essSup_le hx
    refine le_antisymm ?_ (by positivity)
    calc volume {x | β < φ x}
        ≤ volume {x | essSup φ volume < φ x} := MeasureTheory.measure_mono h_sub
      _ = 0 := meas_essSup_lt

  let volF : ℝ → ℝ≥0∞ := fun α => volume {x | ENNReal.ofReal α < f x}
  let volG : ℝ → ℝ≥0∞ := fun α => volume {y | ENNReal.ofReal α < g y}
  let volH : ℝ → ℝ≥0∞ := fun α => volume {z | ENNReal.ofReal α < h z}
  have hvolF_meas : Measurable volF :=
    measurable_measure_prodMk_left
      (measurableSet_lt (ENNReal.measurable_ofReal.comp measurable_fst)
        (hf_meas.comp measurable_snd))
  have hvolG_meas : Measurable volG :=
    measurable_measure_prodMk_left
      (measurableSet_lt (ENNReal.measurable_ofReal.comp measurable_fst)
        (hg_meas.comp measurable_snd))

  have h_pointwise : ∀ α : ℝ, 0 < α →
      ENNReal.ofReal t * volF α + ENNReal.ofReal (1 - t) * volG α ≤ volH α := by
    intro α hα
    have hα_pos_e : (0 : ℝ≥0∞) < ENNReal.ofReal α :=
      ENNReal.ofReal_pos.mpr hα
    have hα_top : ENNReal.ofReal α ≠ ⊤ := ENNReal.ofReal_ne_top
    by_cases hαM : ENNReal.ofReal α < M
    ·
      have hA_pos : 0 < volume {x | ENNReal.ofReal α < f x} :=
        h_pos_meas hM_def.symm hαM
      have hB_pos : 0 < volume {y | ENNReal.ofReal α < g y} :=
        h_pos_meas (h_ess_eq.symm.trans hM_def.symm) hαM
      have hA_ne : ({x | ENNReal.ofReal α < f x} : Set ℝ).Nonempty :=
        MeasureTheory.nonempty_of_measure_ne_zero hA_pos.ne'
      have hB_ne : ({y | ENNReal.ofReal α < g y} : Set ℝ).Nonempty :=
        MeasureTheory.nonempty_of_measure_ne_zero hB_pos.ne'
      exact prekopaLeindler_1d_levelMeasureBound hf_meas hg_meas hh_meas
        ht_pos ht_lt h_le hα_pos_e hα_top hA_ne hB_ne
    ·
      rw [not_lt] at hαM
      have hf_null : volF α = 0 := h_null_meas hM_def.symm hαM
      have hg_null : volG α = 0 := h_null_meas (h_ess_eq.symm.trans hM_def.symm) hαM
      change ENNReal.ofReal t * volF α + ENNReal.ofReal (1 - t) * volG α ≤ volH α
      rw [hf_null, hg_null, mul_zero, mul_zero, zero_add]
      positivity

  rw [lintegral_eq_lintegral_meas_lt_ennreal hf_meas,
      lintegral_eq_lintegral_meas_lt_ennreal hg_meas,
      lintegral_eq_lintegral_meas_lt_ennreal hh_meas]

  change ENNReal.ofReal t * (∫⁻ α in Ioi (0:ℝ), volF α)
       + ENNReal.ofReal (1 - t) * (∫⁻ α in Ioi (0:ℝ), volG α)
       ≤ ∫⁻ α in Ioi (0:ℝ), volH α

  rw [← MeasureTheory.lintegral_const_mul _ hvolF_meas,
      ← MeasureTheory.lintegral_const_mul _ hvolG_meas]

  rw [← MeasureTheory.lintegral_add_left (hvolF_meas.const_mul _)]

  exact MeasureTheory.setLIntegral_mono'
    measurableSet_Ioi (fun α hα => h_pointwise α hα)

private theorem prekopaLeindler_1d_essBdd
    {f g h : ℝ → ℝ≥0∞}
    (hf_meas : Measurable f) (hg_meas : Measurable g) (hh_meas : Measurable h)
    {t : ℝ} (ht_pos : 0 < t) (ht_lt : t < 1)
    (h_le : ∀ x y : ℝ,
      f x ^ t * g y ^ (1 - t) ≤ h (t * x + (1 - t) * y))
    (hMf_top : essSup f volume ≠ ⊤) (hMg_top : essSup g volume ≠ ⊤) :
    (∫⁻ x, f x) ^ t * (∫⁻ y, g y) ^ (1 - t) ≤ ∫⁻ z, h z := by
  have h1t_pos : 0 < 1 - t := sub_pos.mpr ht_lt
  set Mf := essSup f volume with hMf_def
  set Mg := essSup g volume with hMg_def

  by_cases hMf_zero : Mf = 0
  · have hf_int_zero : ∫⁻ x, f x = 0 := by
      rw [MeasureTheory.lintegral_eq_zero_iff hf_meas]
      filter_upwards [ENNReal.ae_le_essSup f] with x hx
      rw [← hMf_def, hMf_zero] at hx
      exact le_antisymm hx (by positivity)
    rw [hf_int_zero, ENNReal.zero_rpow_of_pos ht_pos, zero_mul]
    positivity

  by_cases hMg_zero : Mg = 0
  · have hg_int_zero : ∫⁻ y, g y = 0 := by
      rw [MeasureTheory.lintegral_eq_zero_iff hg_meas]
      filter_upwards [ENNReal.ae_le_essSup g] with y hy
      rw [← hMg_def, hMg_zero] at hy
      exact le_antisymm hy (by positivity)
    rw [hg_int_zero, ENNReal.zero_rpow_of_pos h1t_pos, mul_zero]
    positivity

  set c : ℝ≥0∞ := Mg / Mf with hc_def
  have hc_pos : (0 : ℝ≥0∞) < c := ENNReal.div_pos hMg_zero hMf_top
  have hc_top : c ≠ ⊤ := by
    rw [hc_def]
    exact (ENNReal.div_lt_top hMg_top hMf_zero).ne
  have hcMf_eq_Mg : c * Mf = Mg := by
    rw [hc_def, ENNReal.div_mul_cancel hMf_zero hMf_top]

  set f' : ℝ → ℝ≥0∞ := fun x => c * f x with hf'_def
  set h' : ℝ → ℝ≥0∞ := fun z => c ^ t * h z with hh'_def
  have hf'_meas : Measurable f' := hf_meas.const_mul c
  have hh'_meas : Measurable h' := hh_meas.const_mul (c ^ t)

  have hf'_essSup : essSup f' volume = Mg := by
    change essSup (fun x => c * f x) volume = Mg
    rw [ENNReal.essSup_const_mul, hcMf_eq_Mg]

  have h_le' : ∀ x y : ℝ,
      f' x ^ t * g y ^ (1 - t) ≤ h' (t * x + (1 - t) * y) := by
    intro x y
    change (c * f x) ^ t * g y ^ (1 - t) ≤ c ^ t * h (t * x + (1 - t) * y)
    rw [ENNReal.mul_rpow_of_nonneg _ _ ht_pos.le, mul_assoc]
    gcongr
    exact h_le x y

  have h_amgm := ennreal_geom_mean_le_arith_mean2_weighted ht_pos ht_lt
    (∫⁻ x, f' x) (∫⁻ y, g y)
  have h_arith := prekopaLeindler_1d_arithBound hf'_meas hg_meas hh'_meas
    ht_pos ht_lt h_le' (hf'_essSup.trans hMg_def.symm)
  have h_pl_rescaled :
      (∫⁻ x, f' x) ^ t * (∫⁻ y, g y) ^ (1 - t) ≤ ∫⁻ z, h' z :=
    le_trans h_amgm h_arith

  rw [show ∫⁻ x, f' x = c * ∫⁻ x, f x from
        MeasureTheory.lintegral_const_mul c hf_meas,
      show ∫⁻ z, h' z = c ^ t * ∫⁻ z, h z from
        MeasureTheory.lintegral_const_mul (c ^ t) hh_meas,
      ENNReal.mul_rpow_of_nonneg _ _ ht_pos.le, mul_assoc] at h_pl_rescaled

  have hct_ne_zero : c ^ t ≠ 0 := (ENNReal.rpow_pos hc_pos hc_top).ne'
  have hct_ne_top : c ^ t ≠ ⊤ :=
    (ENNReal.rpow_lt_top_of_nonneg ht_pos.le hc_top).ne

  rw [mul_comm (c ^ t) _, mul_comm (c ^ t) _] at h_pl_rescaled
  exact (ENNReal.mul_le_mul_iff_left hct_ne_zero hct_ne_top).mp h_pl_rescaled

theorem prekopaLeindler_1d
    {f g h : ℝ → ℝ≥0∞}
    (hf_meas : Measurable f) (hg_meas : Measurable g) (hh_meas : Measurable h)
    {t : ℝ} (ht_pos : 0 < t) (ht_lt : t < 1)
    (h_le : ∀ x y : ℝ,
      f x ^ t * g y ^ (1 - t) ≤ h (t * x + (1 - t) * y)) :
    (∫⁻ x, f x) ^ t * (∫⁻ y, g y) ^ (1 - t) ≤ ∫⁻ z, h z := by
  have h1t_pos : 0 < 1 - t := sub_pos.mpr ht_lt

  set fN : ℕ → ℝ → ℝ≥0∞ := fun n x => f x ⊓ (n : ℝ≥0∞) with hfN_def
  set gN : ℕ → ℝ → ℝ≥0∞ := fun n y => g y ⊓ (n : ℝ≥0∞) with hgN_def
  have hfN_meas : ∀ n, Measurable (fN n) := fun n => hf_meas.inf measurable_const
  have hgN_meas : ∀ n, Measurable (gN n) := fun n => hg_meas.inf measurable_const
  have hfN_essSup_top : ∀ n, essSup (fN n) volume ≠ ⊤ := fun n => by
    have h_le_n : essSup (fN n) volume ≤ (n : ℝ≥0∞) :=
      essSup_le_of_ae_le _ (Filter.Eventually.of_forall fun _ => inf_le_right)
    exact ne_of_lt (lt_of_le_of_lt h_le_n ENNReal.coe_lt_top)
  have hgN_essSup_top : ∀ n, essSup (gN n) volume ≠ ⊤ := fun n => by
    have h_le_n : essSup (gN n) volume ≤ (n : ℝ≥0∞) :=
      essSup_le_of_ae_le _ (Filter.Eventually.of_forall fun _ => inf_le_right)
    exact ne_of_lt (lt_of_le_of_lt h_le_n ENNReal.coe_lt_top)

  have h_le_N : ∀ n m, ∀ x y : ℝ,
      fN n x ^ t * gN m y ^ (1 - t) ≤ h (t * x + (1 - t) * y) := by
    intro n m x y
    calc fN n x ^ t * gN m y ^ (1 - t)
        ≤ f x ^ t * g y ^ (1 - t) := by
          gcongr <;> exact inf_le_left
      _ ≤ h (t * x + (1 - t) * y) := h_le x y

  have h_per_nm : ∀ n m,
      (∫⁻ x, fN n x) ^ t * (∫⁻ y, gN m y) ^ (1 - t) ≤ ∫⁻ z, h z := fun n m =>
    prekopaLeindler_1d_essBdd (hfN_meas n) (hgN_meas m) hh_meas ht_pos ht_lt
      (h_le_N n m) (hfN_essSup_top n) (hgN_essSup_top m)

  have hfN_mono : Monotone fun n => ∫⁻ x, fN n x := by
    intro n m hnm
    apply MeasureTheory.lintegral_mono
    intro x; exact inf_le_inf_left _ (by exact_mod_cast hnm)
  have hgN_mono : Monotone fun m => ∫⁻ y, gN m y := by
    intro n m hnm
    apply MeasureTheory.lintegral_mono
    intro y; exact inf_le_inf_left _ (by exact_mod_cast hnm)
  have hfN_iSup : ⨆ n, ∫⁻ x, fN n x = ∫⁻ x, f x := by
    rw [← MeasureTheory.lintegral_iSup hfN_meas (fun n m hnm x =>
      inf_le_inf_left _ (by exact_mod_cast hnm))]
    apply MeasureTheory.lintegral_congr
    intro x
    simp only [fN]
    rw [← inf_iSup_eq, ENNReal.iSup_natCast, inf_top_eq]
  have hgN_iSup : ⨆ m, ∫⁻ y, gN m y = ∫⁻ y, g y := by
    rw [← MeasureTheory.lintegral_iSup hgN_meas (fun n m hnm y =>
      inf_le_inf_left _ (by exact_mod_cast hnm))]
    apply MeasureTheory.lintegral_congr
    intro y
    simp only [gN]
    rw [← inf_iSup_eq, ENNReal.iSup_natCast, inf_top_eq]

  have h_rpow_iSup : ∀ (a : ℕ → ℝ≥0∞) (p : ℝ), 0 ≤ p → Monotone a →
      (⨆ n, a n) ^ p = ⨆ n, a n ^ p := by
    intro a p hp ha_mono
    have h_tendsto : Filter.Tendsto a Filter.atTop (𝓝 (⨆ n, a n)) :=
      tendsto_atTop_iSup ha_mono
    have h_tendsto_pow : Filter.Tendsto (fun n => a n ^ p) Filter.atTop
        (𝓝 ((⨆ n, a n) ^ p)) :=
      (ENNReal.continuous_rpow_const.tendsto _).comp h_tendsto
    have ha_pow_mono : Monotone (fun n => a n ^ p) := fun n m hnm =>
      ENNReal.rpow_le_rpow (ha_mono hnm) hp
    exact tendsto_nhds_unique h_tendsto_pow (tendsto_atTop_iSup ha_pow_mono)
  rw [← hfN_iSup, ← hgN_iSup]

  rw [h_rpow_iSup _ t ht_pos.le hfN_mono,
      h_rpow_iSup _ (1 - t) h1t_pos.le hgN_mono]

  rw [ENNReal.iSup_mul]
  refine iSup_le fun n => ?_
  rw [ENNReal.mul_iSup]
  refine iSup_le fun m => ?_

  exact h_per_nm n m

theorem prekopaLeindler.{u}
    {ι : Type u} [Fintype ι]
    {f g h : (ι → ℝ) → ℝ≥0∞}
    (hf_meas : Measurable f) (hg_meas : Measurable g) (hh_meas : Measurable h)
    {t : ℝ} (ht_pos : 0 < t) (ht_lt : t < 1)
    (h_le : ∀ x y : ι → ℝ,
      f x ^ t * g y ^ (1 - t) ≤ h (t • x + (1 - t) • y)) :
    (∫⁻ x, f x) ^ t * (∫⁻ y, g y) ^ (1 - t) ≤ ∫⁻ z, h z := by

  suffices H : ∀ (κ : Type u) [Fintype κ] (f g h : (κ → ℝ) → ℝ≥0∞),
      Measurable f → Measurable g → Measurable h →
      ∀ {s : ℝ}, 0 < s → s < 1 →
      (∀ x y : κ → ℝ, f x ^ s * g y ^ (1 - s) ≤ h (s • x + (1 - s) • y)) →
      (∫⁻ x, f x) ^ s * (∫⁻ y, g y) ^ (1 - s) ≤ ∫⁻ z, h z by
    exact H ι f g h hf_meas hg_meas hh_meas ht_pos ht_lt h_le
  intro κ _Fκ
  refine Fintype.induction_empty_option
    (P := fun κ [Fintype κ] => ∀ (f g h : (κ → ℝ) → ℝ≥0∞),
      Measurable f → Measurable g → Measurable h →
      ∀ {s : ℝ}, 0 < s → s < 1 →
      (∀ x y : κ → ℝ, f x ^ s * g y ^ (1 - s) ≤ h (s • x + (1 - s) • y)) →
      (∫⁻ x, f x) ^ s * (∫⁻ y, g y) ^ (1 - s) ≤ ∫⁻ z, h z) ?_ ?_ ?_ κ
  ·

    intro α β _Fβ e IH f g h hf hg hh s hs hs1 hle
    let : Fintype α := Fintype.ofEquiv β e.symm
    set ψ : (β → ℝ) ≃ᵐ (α → ℝ) :=
      MeasurableEquiv.piCongrLeft (fun _ : α => ℝ) e.symm with hψ_def

    have hψ_smul : ∀ x y : α → ℝ,
        ψ.symm (s • x + (1 - s) • y) = s • ψ.symm x + (1 - s) • ψ.symm y := fun _ _ => rfl

    have h_vol_fwd : (volume : Measure (β → ℝ)).map ψ = (volume : Measure (α → ℝ)) := by
      conv_lhs => rw [MeasureTheory.volume_pi]
      conv_rhs => rw [MeasureTheory.volume_pi]
      exact MeasureTheory.Measure.pi_map_piCongrLeft e.symm (fun _ : α => volume)
    have h_vol : (volume : Measure (α → ℝ)).map ψ.symm = (volume : Measure (β → ℝ)) := by
      rw [← h_vol_fwd, MeasurableEquiv.map_symm_map]

    have hf' : Measurable (f ∘ ψ.symm) := hf.comp ψ.symm.measurable
    have hg' : Measurable (g ∘ ψ.symm) := hg.comp ψ.symm.measurable
    have hh' : Measurable (h ∘ ψ.symm) := hh.comp ψ.symm.measurable
    have hle' : ∀ x y : α → ℝ,
        (f ∘ ψ.symm) x ^ s * (g ∘ ψ.symm) y ^ (1 - s)
        ≤ (h ∘ ψ.symm) (s • x + (1 - s) • y) := by
      intro x y
      change f (ψ.symm x) ^ s * g (ψ.symm y) ^ (1 - s) ≤ h (ψ.symm (s • x + (1 - s) • y))
      rw [hψ_smul x y]
      exact hle (ψ.symm x) (ψ.symm y)

    have hf_int : ∫⁻ y, f y = ∫⁻ x, f (ψ.symm x) := by
      conv_lhs => rw [show (volume : Measure (β → ℝ))
          = (volume : Measure (α → ℝ)).map ψ.symm from h_vol.symm]
      exact MeasureTheory.lintegral_map hf ψ.symm.measurable
    have hg_int : ∫⁻ y, g y = ∫⁻ x, g (ψ.symm x) := by
      conv_lhs => rw [show (volume : Measure (β → ℝ))
          = (volume : Measure (α → ℝ)).map ψ.symm from h_vol.symm]
      exact MeasureTheory.lintegral_map hg ψ.symm.measurable
    have hh_int : ∫⁻ y, h y = ∫⁻ x, h (ψ.symm x) := by
      conv_lhs => rw [show (volume : Measure (β → ℝ))
          = (volume : Measure (α → ℝ)).map ψ.symm from h_vol.symm]
      exact MeasureTheory.lintegral_map hh ψ.symm.measurable
    rw [hf_int, hg_int, hh_int]
    exact IH (f ∘ ψ.symm) (g ∘ ψ.symm) (h ∘ ψ.symm) hf' hg' hh' hs hs1 hle'
  ·

    intro f g h hf_meas hg_meas hh_meas s hs_pos hs_lt h_le
    have h_volume : (volume : Measure (PEmpty → ℝ))
        = Measure.dirac (fun a : PEmpty => isEmptyElim a) :=
      Measure.volume_pi_eq_dirac _
    rw [h_volume, lintegral_dirac' _ hf_meas, lintegral_dirac' _ hg_meas,
        lintegral_dirac' _ hh_meas]
    have h_pl := h_le (fun a => isEmptyElim a) (fun a => isEmptyElim a)
    have h_smul : s • (fun a : PEmpty => isEmptyElim a : PEmpty → ℝ)
                  + (1 - s) • (fun a : PEmpty => isEmptyElim a : PEmpty → ℝ)
                = (fun a : PEmpty => isEmptyElim a : PEmpty → ℝ) := by
      funext a; exact isEmptyElim a
    rwa [h_smul] at h_pl
  ·

    intro α _Fα IH f g h hf hg hh s hs hs1 hle
    let E : ((i : Option α) → ℝ) ≃ᵐ ((i : α) → ℝ) × ℝ :=
      MeasurableEquiv.piOptionEquivProd (fun _ : Option α => ℝ)

    have hE_none : ∀ (x' : α → ℝ) (u : ℝ),
        E.symm (x', u) none = u := fun _ _ => rfl
    have hE_some : ∀ (x' : α → ℝ) (u : ℝ) (a : α),
        E.symm (x', u) (some a) = x' a := fun _ _ _ => rfl

    have hE_smul : ∀ (x' y' : α → ℝ) (u v : ℝ),
        s • E.symm (x', u) + (1 - s) • E.symm (y', v)
        = E.symm (s • x' + (1 - s) • y', s * u + (1 - s) * v) := by
      intro x' y' u v
      funext i
      cases i with
      | none =>
        simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul]
        change s * u + (1 - s) * v = s * u + (1 - s) * v
        rfl
      | some a =>
        simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul]
        change s * x' a + (1 - s) * y' a = s * x' a + (1 - s) * y' a
        rfl

    have h_vol : ((volume : Measure (α → ℝ)).prod (volume : Measure ℝ)).map E.symm
        = (volume : Measure (Option α → ℝ)) := by
      conv_rhs => rw [MeasureTheory.volume_pi]
      conv_lhs => rw [show (volume : Measure (α → ℝ))
          = MeasureTheory.Measure.pi (fun _ : α => volume) from MeasureTheory.volume_pi]
      exact MeasureTheory.Measure.pi_map_piOptionEquivProd
        (fun _ : Option α => volume)

    set F : ℝ → ℝ≥0∞ := fun u => ∫⁻ x' : α → ℝ, f (E.symm (x', u)) with hF_def
    set G : ℝ → ℝ≥0∞ := fun v => ∫⁻ y' : α → ℝ, g (E.symm (y', v)) with hG_def
    set H_marg : ℝ → ℝ≥0∞ := fun w => ∫⁻ z' : α → ℝ, h (E.symm (z', w)) with hH_def

    have hf_comp : Measurable (fun p : (α → ℝ) × ℝ => f (E.symm p)) :=
      hf.comp E.symm.measurable
    have hg_comp : Measurable (fun p : (α → ℝ) × ℝ => g (E.symm p)) :=
      hg.comp E.symm.measurable
    have hh_comp : Measurable (fun p : (α → ℝ) × ℝ => h (E.symm p)) :=
      hh.comp E.symm.measurable
    have hF_meas : Measurable F := Measurable.lintegral_prod_left' hf_comp
    have hG_meas : Measurable G := Measurable.lintegral_prod_left' hg_comp
    have hH_marg_meas : Measurable H_marg := Measurable.lintegral_prod_left' hh_comp

    have h_FGH_le : ∀ u v : ℝ,
        F u ^ s * G v ^ (1 - s) ≤ H_marg (s * u + (1 - s) * v) := by
      intro u v
      have hf_slice : Measurable (fun x' : α → ℝ => f (E.symm (x', u))) :=
        hf.comp (E.symm.measurable.comp (measurable_id.prodMk measurable_const))
      have hg_slice : Measurable (fun y' : α → ℝ => g (E.symm (y', v))) :=
        hg.comp (E.symm.measurable.comp (measurable_id.prodMk measurable_const))
      have hh_slice : Measurable (fun z' : α → ℝ =>
          h (E.symm (z', s * u + (1 - s) * v))) :=
        hh.comp (E.symm.measurable.comp (measurable_id.prodMk measurable_const))
      have h_slice_le : ∀ x' y' : α → ℝ,
          f (E.symm (x', u)) ^ s * g (E.symm (y', v)) ^ (1 - s)
          ≤ h (E.symm (s • x' + (1 - s) • y', s * u + (1 - s) * v)) := by
        intro x' y'
        have h_pl := hle (E.symm (x', u)) (E.symm (y', v))
        rw [hE_smul] at h_pl
        exact h_pl
      exact IH _ _ _ hf_slice hg_slice hh_slice hs hs1 h_slice_le

    have h_1d := prekopaLeindler_1d hF_meas hG_meas hH_marg_meas hs hs1 h_FGH_le

    have h_int_split : ∀ (k : (Option α → ℝ) → ℝ≥0∞), Measurable k →
        ∫⁻ z, k z = ∫⁻ u : ℝ, ∫⁻ x' : α → ℝ, k (E.symm (x', u)) := by
      intro k hk
      conv_lhs => rw [show (volume : Measure (Option α → ℝ))
          = ((volume : Measure (α → ℝ)).prod (volume : Measure ℝ)).map E.symm
        from h_vol.symm]
      rw [MeasureTheory.lintegral_map hk E.symm.measurable]
      exact MeasureTheory.lintegral_prod_symm' _ (hk.comp E.symm.measurable)
    rw [h_int_split f hf, h_int_split g hg, h_int_split h hh]
    exact h_1d

end AsymptoticStatistics

end OAI
end

section
-- module Solutions.OAIQ092_CC.KLS_Convexity_Prekopa
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped ENNReal

namespace LeanBlast.KLS

theorem prekopaLeindler_space {n : ℕ} {f g h : Space n → ℝ≥0∞}
    (hf : Measurable f) (hg : Measurable g) (hh : Measurable h)
    {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1)
    (hfg : ∀ x y : Space n,
      f x ^ t * g y ^ (1 - t) ≤ h (t • x + (1 - t) • y)) :
    (∫⁻ x, f x) ^ t * (∫⁻ y, g y) ^ (1 - t) ≤ ∫⁻ z, h z := by
  have he := PiLp.volume_preserving_toLp (Fin n)
  have hp := AsymptoticStatistics.prekopaLeindler
    (hf.comp he.measurable) (hg.comp he.measurable) (hh.comp he.measurable)
    ht0 ht1 (fun x y => hfg (WithLp.toLp 2 x) (WithLp.toLp 2 y))
  simpa only [Function.comp_apply, he.lintegral_comp hf, he.lintegral_comp hg,
    he.lintegral_comp hh] using hp

end LeanBlast.KLS

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.KLS_Convexity_PrekopaReal
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.gaussianLineEquiv_apply _root_.OAI.LeanBlast.KLS.blMomentDeriv_zero _root_.OAI.LeanBlast.KLS.blMoment_zero _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped ENNReal

namespace LeanBlast.KLS

theorem prekopaLeindler_integral {n : ℕ} {f g h : Space n → ℝ}
    (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x) (hh0 : ∀ x, 0 ≤ h x)
    (hf : Measurable f) (hg : Measurable g) (hh : Measurable h)
    (hfi : Integrable f) (hgi : Integrable g) (hhi : Integrable h)
    {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1)
    (hfg : ∀ x y : Space n,
      f x ^ t * g y ^ (1 - t) ≤ h (t • x + (1 - t) • y)) :
    (∫ x, f x) ^ t * (∫ y, g y) ^ (1 - t) ≤ ∫ z, h z := by
  have hp := prekopaLeindler_space hf.ennreal_ofReal hg.ennreal_ofReal hh.ennreal_ofReal
    ht0 ht1 (fun x y => by
      rw [ENNReal.ofReal_rpow_of_nonneg (hf0 x) ht0.le,
        ENNReal.ofReal_rpow_of_nonneg (hg0 y) (sub_pos.mpr ht1).le,
        ← ENNReal.ofReal_mul (Real.rpow_nonneg (hf0 x) t)]
      exact ENNReal.ofReal_le_ofReal (hfg x y))
  rw [← ofReal_integral_eq_lintegral_ofReal hfi (ae_of_all _ hf0),
    ← ofReal_integral_eq_lintegral_ofReal hgi (ae_of_all _ hg0),
    ← ofReal_integral_eq_lintegral_ofReal hhi (ae_of_all _ hh0)] at hp
  rw [ENNReal.ofReal_rpow_of_nonneg (integral_nonneg hf0) ht0.le,
    ENNReal.ofReal_rpow_of_nonneg (integral_nonneg hg0) (sub_pos.mpr ht1).le,
    ← ENNReal.ofReal_mul (Real.rpow_nonneg (integral_nonneg hf0) t)] at hp
  exact (ENNReal.ofReal_le_ofReal_iff (integral_nonneg hh0)).mp hp

theorem concaveOn_log_integral {E : Type*} [AddCommGroup E] [Module ℝ E]
    {n : ℕ} {S : Set E} (hS : Convex ℝ S) (f : E → Space n → ℝ)
    (hf0 : ∀ u ∈ S, ∀ x, 0 ≤ f u x)
    (hf : ∀ u ∈ S, Measurable (f u))
    (hfi : ∀ u ∈ S, Integrable (f u))
    (hpos : ∀ u ∈ S, 0 < ∫ x, f u x)
    (hjoint : ∀ u ∈ S, ∀ v ∈ S, ∀ x y, ∀ t : ℝ, 0 < t → t < 1 →
      f u x ^ t * f v y ^ (1 - t) ≤ f (t • u + (1 - t) • v) (t • x + (1 - t) • y)) :
    ConcaveOn ℝ S (fun u => Real.log (∫ x, f u x)) := by
  refine ⟨hS, ?_⟩
  intro u hu v hv a b ha hb hab
  by_cases ha0 : a = 0
  · have hb1 : b = 1 := by linarith
    simp [ha0, hb1]
  by_cases hb0 : b = 0
  · have ha1 : a = 1 := by linarith
    simp [hb0, ha1]
  have ha' : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
  have hb' : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0)
  have hba : 1 - a = b := by linarith
  have huv : a • u + b • v ∈ S := hS hu hv ha hb hab
  have hp := prekopaLeindler_integral (hf0 u hu) (hf0 v hv) (hf0 _ huv)
    (hf u hu) (hf v hv) (hf _ huv) (hfi u hu) (hfi v hv) (hfi _ huv)
    ha' (by linarith) (by
      intro x y
      simpa only [hba] using hjoint u hu v hv x y a ha' (by linarith))
  rw [hba] at hp
  apply (Real.le_log_iff_exp_le (hpos _ huv)).mpr
  simpa only [smul_eq_mul, Real.rpow_def_of_pos (hpos u hu),
    Real.rpow_def_of_pos (hpos v hv), Real.exp_add, mul_comm] using hp

theorem concaveOn_log_integral_exp_neg {E : Type*} [AddCommGroup E] [Module ℝ E]
    {n : ℕ} {S : Set E} (hS : Convex ℝ S) (F : E × Space n → ℝ)
    (hF : ConvexOn ℝ (S ×ˢ (univ : Set (Space n))) F)
    (hmeas : ∀ u ∈ S, Measurable (fun x => Real.exp (-F (u, x))))
    (hint : ∀ u ∈ S, Integrable (fun x => Real.exp (-F (u, x)))) :
    ConcaveOn ℝ S (fun u => Real.log (∫ x, Real.exp (-F (u, x)))) := by
  apply concaveOn_log_integral hS (fun u x => Real.exp (-F (u, x)))
    (fun u hu x => (Real.exp_pos _).le) hmeas hint
  · intro u hu
    rw [integral_pos_iff_support_of_nonneg (fun x => (Real.exp_pos _).le) (hint u hu)]
    have hs : Function.support (fun x : Space n => Real.exp (-F (u, x))) = univ := by
      ext x
      simp [Function.mem_support, Real.exp_ne_zero]
    rw [hs]
    exact Measure.measure_univ_pos.mpr (NeZero.ne volume)
  · intro u hu v hv x y t ht0 ht1
    have hc := hF.2 (x := (u, x)) ⟨hu, mem_univ x⟩ (y := (v, y)) ⟨hv, mem_univ y⟩
      ht0.le (sub_pos.mpr ht1).le (by ring)
    rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.rpow_def_of_pos (Real.exp_pos _),
      Real.log_exp, Real.log_exp, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    change F (t • u + (1 - t) • v, t • x + (1 - t) • y) ≤
      t * F (u, x) + (1 - t) * F (v, y) at hc
    nlinarith only [hc]

end LeanBlast.KLS

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.KLS_Spectral_BrascampLiebMoments
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.gaussianLineEquiv_apply _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory Filter
open scoped Topology

namespace LeanBlast.KLS

section BoundedKernel

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
  {h q : α → ℝ} {B : ℝ}

private theorem boundedKernel_bound (Φ : ℝ → ℝ → ℝ → ℝ)
    (hΦ : Continuous (fun p : ℝ × ℝ × ℝ => Φ p.1 p.2.1 p.2.2)) (B : ℝ) :
    ∃ C : ℝ, ∀ t ∈ Icc (-1 : ℝ) 1, ∀ a ∈ Icc (-B) B, ∀ b ∈ Icc (-B) B,
      ‖Φ t a b‖ ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)).exists_bound_of_continuousOn
    hΦ.continuousOn
  exact ⟨C, fun t ht a ha b hb => hC (t, a, b) ⟨ht, ha, hb⟩⟩

theorem boundedKernel_integrable (Φ : ℝ → ℝ → ℝ → ℝ)
    (hΦ : Continuous (fun p : ℝ × ℝ × ℝ => Φ p.1 p.2.1 p.2.2))
    (hh : Measurable h) (hq : Measurable q)
    (hhB : ∀ x, |h x| ≤ B) (hqB : ∀ x, |q x| ≤ B)
    {t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1) :
    Integrable (fun x => Φ t (h x) (q x)) μ := by
  obtain ⟨C, hC⟩ := boundedKernel_bound Φ hΦ B
  apply (integrable_const C).mono'
    (hΦ.measurable.comp (measurable_const.prodMk (hh.prodMk hq))).aestronglyMeasurable
  exact ae_of_all _ fun x => hC t ht (h x) (abs_le.mp (hhB x)) (q x) (abs_le.mp (hqB x))

theorem boundedKernel_hasDerivAt_integral (Φ Φ' : ℝ → ℝ → ℝ → ℝ)
    (hΦ : Continuous (fun p : ℝ × ℝ × ℝ => Φ p.1 p.2.1 p.2.2))
    (hΦ' : Continuous (fun p : ℝ × ℝ × ℝ => Φ' p.1 p.2.1 p.2.2))
    (hd : ∀ t a b, HasDerivAt (fun s => Φ s a b) (Φ' t a b) t)
    (hh : Measurable h) (hq : Measurable q)
    (hhB : ∀ x, |h x| ≤ B) (hqB : ∀ x, |q x| ≤ B)
    {t : ℝ} (ht : t ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt (fun s => ∫ x, Φ s (h x) (q x) ∂μ)
      (∫ x, Φ' t (h x) (q x) ∂μ) t := by
  obtain ⟨C, hC⟩ := boundedKernel_bound Φ' hΦ' B
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := μ) (F := fun s x => Φ s (h x) (q x))
    (F' := fun s x => Φ' s (h x) (q x))
    (bound := fun _ : α => C) (Ioo_mem_nhds ht.1 ht.2) ?_
    (boundedKernel_integrable Φ hΦ hh hq hhB hqB ⟨ht.1.le, ht.2.le⟩) ?_ ?_
    (integrable_const C) ?_).2
  · exact Eventually.of_forall fun s =>
      (hΦ.measurable.comp (measurable_const.prodMk (hh.prodMk hq))).aestronglyMeasurable
  · exact (hΦ'.measurable.comp (measurable_const.prodMk (hh.prodMk hq))).aestronglyMeasurable
  · exact ae_of_all _ fun x s hs =>
      hC s ⟨hs.1.le, hs.2.le⟩ (h x) (abs_le.mp (hhB x)) (q x) (abs_le.mp (hqB x))
  · exact ae_of_all _ fun x s _ => hd s (h x) (q x)

end BoundedKernel

theorem continuous_blWeight :
    Continuous (fun p : ℝ × ℝ × ℝ => blWeight p.1 p.2.1 p.2.2) := by
  unfold blWeight
  fun_prop

theorem continuous_blWeightDeriv :
    Continuous (fun p : ℝ × ℝ × ℝ => blWeightDeriv p.1 p.2.1 p.2.2) := by
  unfold blWeightDeriv blWeight
  fun_prop

theorem continuous_blWeightSecond :
    Continuous (fun p : ℝ × ℝ × ℝ => blWeightSecond p.1 p.2.1 p.2.2) := by
  unfold blWeightSecond blWeight
  fun_prop

theorem hasDerivAt_blWeight (t a b : ℝ) :
    HasDerivAt (fun s => blWeight s a b) (blWeightDeriv t a b) t := by
  have h := ((((hasDerivAt_id' t).fun_neg.mul_const a).fun_sub
    (((hasDerivAt_id' t).fun_pow 2).div_const 2 |>.mul_const b))).exp
  convert h using 1 <;> first | (with_reducible_and_instances rfl) | (dsimp [blWeight, blWeightDeriv])
  ring

theorem hasDerivAt_blWeightDeriv (t a b : ℝ) :
    HasDerivAt (fun s => blWeightDeriv s a b) (blWeightSecond t a b) t := by
  have h := ((hasDerivAt_const t (-a)).fun_sub ((hasDerivAt_id' t).mul_const b)).fun_mul
    (hasDerivAt_blWeight t a b)
  convert h using 1 <;> first | (with_reducible_and_instances rfl) | (dsimp [blWeightSecond, blWeightDeriv])
  ring

section Moments

variable {n : ℕ} (μ : Measure (Space n)) [IsProbabilityMeasure μ]
  (h q : Space n → ℝ)

omit [IsProbabilityMeasure μ] in
theorem blMomentSecond_zero (hh2 : Integrable (fun x => h x ^ 2) μ) (hq : Integrable q μ) :
    blMomentSecond μ h q 0 = (∫ x, h x ^ 2 ∂μ) - ∫ x, q x ∂μ := by
  simp only [blMomentSecond, blWeightSecond, blWeight, neg_zero, zero_mul, add_zero, zero_pow (by norm_num : 2 ≠ 0),
    zero_div, sub_zero, Real.exp_zero, mul_one]
  exact integral_sub hh2 hq

variable {h q} {B : ℝ}

theorem hasDerivAt_blMoment (hh : Measurable h) (hq : Measurable q)
    (hhB : ∀ x, |h x| ≤ B) (hqB : ∀ x, |q x| ≤ B)
    {t : ℝ} (ht : t ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt (blMoment μ h q) (blMomentDeriv μ h q t) t :=
  boundedKernel_hasDerivAt_integral blWeight blWeightDeriv continuous_blWeight
    continuous_blWeightDeriv hasDerivAt_blWeight hh hq hhB hqB ht

theorem hasDerivAt_blMomentDeriv (hh : Measurable h) (hq : Measurable q)
    (hhB : ∀ x, |h x| ≤ B) (hqB : ∀ x, |q x| ≤ B)
    {t : ℝ} (ht : t ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt (blMomentDeriv μ h q) (blMomentSecond μ h q t) t :=
  boundedKernel_hasDerivAt_integral blWeightDeriv blWeightSecond continuous_blWeightDeriv
    continuous_blWeightSecond hasDerivAt_blWeightDeriv hh hq hhB hqB ht

theorem blMoment_pos (hh : Measurable h) (hq : Measurable q)
    (hhB : ∀ x, |h x| ≤ B) (hqB : ∀ x, |q x| ≤ B)
    {t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1) : 0 < blMoment μ h q t :=
  integral_exp_pos (boundedKernel_integrable blWeight continuous_blWeight hh hq hhB hqB ht)

theorem hasDerivAt_blLogMoment (hh : Measurable h) (hq : Measurable q)
    (hhB : ∀ x, |h x| ≤ B) (hqB : ∀ x, |q x| ≤ B)
    {t : ℝ} (ht : t ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt (blLogMoment μ h q) (blMomentDeriv μ h q t / blMoment μ h q t) t :=
  (hasDerivAt_blMoment μ hh hq hhB hqB ht).log
    (blMoment_pos μ hh hq hhB hqB ⟨ht.1.le, ht.2.le⟩).ne'

theorem hasDerivAt_deriv_blLogMoment_zero (hh : Measurable h) (hq : Measurable q)
    (hhB : ∀ x, |h x| ≤ B) (hqB : ∀ x, |q x| ≤ B) :
    HasDerivAt (deriv (blLogMoment μ h q)) (variance μ h - ∫ x, q x ∂μ) 0 := by
  have h0 : (0 : ℝ) ∈ Ioo (-1 : ℝ) 1 := by constructor <;> norm_num
  have hhint : Integrable h μ := boundedKernel_integrable (fun _ a _ => a)
    (by fun_prop) hh hq hhB hqB (t := 0) ⟨by norm_num, by norm_num⟩
  have hh2int : Integrable (fun x => h x ^ 2) μ := boundedKernel_integrable (fun _ a _ => a ^ 2)
    (by fun_prop) hh hq hhB hqB (t := 0) ⟨by norm_num, by norm_num⟩
  have hqint : Integrable q μ := boundedKernel_integrable (fun _ _ b => b)
    (by fun_prop) hh hq hhB hqB (t := 0) ⟨by norm_num, by norm_num⟩
  have hd := (hasDerivAt_blMomentDeriv μ hh hq hhB hqB h0).div
    (hasDerivAt_blMoment μ hh hq hhB hqB h0) (by simp)
  have hratio : HasDerivAt (fun t => blMomentDeriv μ h q t / blMoment μ h q t)
      (variance μ h - ∫ x, q x ∂μ) 0 := by
    convert hd using 1
    all_goals try with_reducible_and_instances rfl
    rw [blMomentSecond_zero μ h q hh2int hqint, blMoment_zero, blMomentDeriv_zero,
      variance_eq_integral_sq_sub_sq μ hhint hh2int]
    ring
  apply hratio.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds (by norm_num : (-1 : ℝ) < 0) (by norm_num : (0 : ℝ) < 1)] with t ht
  exact (hasDerivAt_blLogMoment μ hh hq hhB hqB ht).deriv

theorem variance_le_integral_of_concave_blLogMoment
    (hh : Measurable h) (hq : Measurable q)
    (hhB : ∀ x, |h x| ≤ B) (hqB : ∀ x, |q x| ≤ B)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hc : ConcaveOn ℝ (Ioo (-ε) ε) (blLogMoment μ h q)) :
    variance μ h ≤ ∫ x, q x ∂μ := by
  have hdiff : ∀ t ∈ Ioo (-ε) ε, DifferentiableAt ℝ (blLogMoment μ h q) t := by
    intro t ht
    exact (hasDerivAt_blLogMoment μ hh hq hhB hqB ⟨by linarith [ht.1], by linarith [ht.2]⟩).differentiableAt
  have hant := hc.antitoneOn_deriv hdiff
  have hnonpos := hant.derivWithin_nonpos (x := 0)
  have hd := (hasDerivAt_deriv_blLogMoment_zero μ hh hq hhB hqB).hasDerivWithinAt
    (s := Ioo (-ε) ε)
  rw [hd.derivWithin (isOpen_Ioo.uniqueDiffWithinAt ⟨by linarith, hε⟩)] at hnonpos
  linarith

end Moments

end LeanBlast.KLS

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.KLS_Convexity_HessianConvexity
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set

namespace LeanBlast.KLS

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem convexOn_of_second_fderiv_nonneg {f : E → ℝ} {s : Set E}
    (hf : ContDiff ℝ 2 f) (hs : Convex ℝ s)
    (hH : ∀ x ∈ s, ∀ v : E, 0 ≤ fderiv ℝ (fderiv ℝ f) x v v) :
    ConvexOn ℝ s f := by
  refine ⟨hs, ?_⟩
  intro x hx y hy a b ha hb hab
  let γ : ℝ → E := AffineMap.lineMap x y
  let F : ℝ → ℝ := fun t => f (γ t)
  let F' : ℝ → ℝ := fun t => fderiv ℝ f (γ t) (y - x)
  let F'' : ℝ → ℝ := fun t => fderiv ℝ (fderiv ℝ f) (γ t) (y - x) (y - x)
  have hγ (t : ℝ) : HasDerivAt γ (y - x) t := AffineMap.hasDerivAt_lineMap
  have hF (t : ℝ) : HasDerivAt F (F' t) t :=
    (hf.differentiable (by norm_num) (γ t)).hasFDerivAt.comp_hasDerivAt t (hγ t)
  have hD : Differentiable ℝ (fderiv ℝ f) :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have hF' (t : ℝ) : HasDerivAt F' (F'' t) t := by
    have h := ((hD (γ t)).hasFDerivAt.clm_apply
      (hasFDerivAt_const (y - x) (γ t))).comp_hasDerivAt t (hγ t)
    simpa only [F', F'', Function.comp_def, add_apply,
      ContinuousLinearMap.comp_apply, zero_apply,
      ContinuousLinearMap.flip_apply, map_zero, zero_add] using h
  have hc : ConvexOn ℝ (Icc (0 : ℝ) 1) F :=
    convexOn_of_hasDerivWithinAt2_nonneg (convex_Icc _ _)
      (fun t _ => (hF t).continuousAt.continuousWithinAt)
      (fun t _ => (hF t).hasDerivWithinAt)
      (fun t _ => (hF' t).hasDerivWithinAt)
      (fun t ht => hH (γ t) (hs.lineMap_mem hx hy (interior_subset ht)) (y - x))
  have h := hc.2 (show (0 : ℝ) ∈ Icc (0 : ℝ) 1 by constructor <;> norm_num)
    (show (1 : ℝ) ∈ Icc (0 : ℝ) 1 by constructor <;> norm_num) ha hb hab
  have hab' : 1 - b = a := by linarith
  simpa [F, γ, AffineMap.lineMap_apply_module, smul_eq_mul, hab'] using h

end LeanBlast.KLS

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.KLS_Spectral_BrascampLiebCurvature
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.gaussianLineEquiv_apply _root_.OAI.LeanBlast.KLS.blMomentDeriv_zero _root_.OAI.LeanBlast.KLS.blMoment_zero _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Matrix MeasureTheory InnerProductSpace
open scoped BigOperators ContDiff Topology Matrix.Norms.Elementwise

namespace LeanBlast.KLS

theorem bl_contDiff_gradient {n : ℕ} {f : Space n → ℝ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (gradient f) := by
  exact (toDual ℝ (Space n)).symm.contDiff.comp (hf.fderiv_right (by first | simp | exact_mod_cast le_top))

theorem bl_contDiff_hessianMatrix {n : ℕ} {f : Space n → ℝ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (hessianMatrix f) := by
  apply contDiff_pi.mpr
  intro i
  apply contDiff_pi.mpr
  intro j
  exact (((hf.fderiv_right (m := ∞) (by simp)).fderiv_right (m := ∞) (by simp)).clm_apply
    contDiff_const).clm_apply contDiff_const

section MatrixSmooth

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {ι : Type*} [Fintype ι] [DecidableEq ι]
  {A : E → Matrix ι ι ℝ}

theorem contDiff_matrix_det (hA : ContDiff ℝ ∞ A) :
    ContDiff ℝ ∞ (fun x => (A x).det) := by
  simp only [Matrix.det_apply']
  fun_prop

theorem contDiff_matrix_adjugate (hA : ContDiff ℝ ∞ A) :
    ContDiff ℝ ∞ (fun x => (A x).adjugate) := by
  apply contDiff_pi.mpr
  intro i
  apply contDiff_pi.mpr
  intro j
  simp only [Matrix.adjugate_apply]
  apply contDiff_matrix_det
  apply contDiff_pi.mpr
  intro a
  apply contDiff_pi.mpr
  intro b
  by_cases h : a = j
  · subst a
    simp only [Matrix.updateRow_self]
    exact contDiff_const
  · simp only [Matrix.updateRow_ne h]
    exact (contDiff_pi.mp (contDiff_pi.mp hA a)) b

theorem contDiff_matrix_inv (hA : ContDiff ℝ ∞ A) (hdet : ∀ x, (A x).det ≠ 0) :
    ContDiff ℝ ∞ (fun x => (A x)⁻¹) := by
  simp only [Matrix.inv_def, Ring.inverse_eq_inv]
  exact ((contDiff_matrix_det hA).inv hdet).smul (contDiff_matrix_adjugate hA)

end MatrixSmooth

theorem steinGamma_self_eq_dotProduct {n : ℕ} (V h : Space n → ℝ) (x : Space n) :
    steinGamma V h h x =
      (fun i => gradient h x i) ⬝ᵥ ((hessianMatrix V x)⁻¹ *ᵥ fun i => gradient h x i) := by
  simp [steinGamma, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]

theorem contDiff_steinGamma_self {n : ℕ} {V h : Space n → ℝ}
    (hV : ContDiff ℝ ∞ V) (hh : ContDiff ℝ ∞ h)
    (hpos : ∀ x, (hessianMatrix V x).PosDef) :
    ContDiff ℝ ∞ (steinGamma V h h) := by
  have hi : ContDiff ℝ ∞ (fun x => (hessianMatrix V x)⁻¹) :=
    contDiff_matrix_inv (bl_contDiff_hessianMatrix hV) fun x => (hpos x).det_pos.ne'
  have hg := bl_contDiff_gradient hh
  unfold steinGamma
  fun_prop

theorem hasCompactSupport_steinGamma_self {n : ℕ} (V : Space n → ℝ)
    {h : Space n → ℝ} (hh : IsTestFunction h) : HasCompactSupport (steinGamma V h h) := by
  apply HasCompactSupport.intro hh.hasCompactSupport_gradient.isCompact
  intro x hx
  have hzero : gradient h x = 0 := image_eq_zero_of_notMem_tsupport hx
  simp only [steinGamma, hzero, PiLp.zero_apply, zero_mul, Finset.sum_const_zero]

theorem sum_standardBasisVector {n : ℕ} (v : Space n) :
    (∑ i, v i • standardBasisVector i) = v := by
  simpa only [standardBasisVector, EuclideanSpace.basisFun_repr] using
    (EuclideanSpace.basisFun (Fin n) ℝ).sum_repr v

theorem second_fderiv_eq_hessianMatrix {n : ℕ} (V : Space n → ℝ) (x u v : Space n) :
    fderiv ℝ (fderiv ℝ V) x u v =
      (fun i => u i) ⬝ᵥ (hessianMatrix V x *ᵥ fun i => v i) := by
  calc
    _ = fderiv ℝ (fderiv ℝ V) x (∑ i, u i • standardBasisVector i)
      (∑ j, v j • standardBasisVector j) := by rw [sum_standardBasisVector, sum_standardBasisVector]
    _ = _ := by
      simp [map_sum, hessianMatrix, Matrix.mulVec, dotProduct, Finset.mul_sum,
        mul_comm, mul_left_comm]
      exact Finset.sum_comm

theorem fderiv_eq_gradient_dotProduct {n : ℕ} {h : Space n → ℝ} {x : Space n}
    (hh : DifferentiableAt ℝ h x) (v : Space n) :
    fderiv ℝ h x v = (fun i => gradient h x i) ⬝ᵥ (fun i => v i) := by
  rw [hh.hasGradientAt.fderiv_apply, EuclideanSpace.inner_eq_star_dotProduct]
  simp only [star_trivial, dotProduct_comm]

theorem quadratic_schur_positive {ι : Type*} [Fintype ι] [DecidableEq ι]
    {H : Matrix ι ι ℝ} (hH : H.PosDef) (g v : ι → ℝ) {δ : ℝ} (hδ : 0 < δ)
    (s : ℝ) (hsv : s ≠ 0 ∨ v ≠ 0) :
    0 < v ⬝ᵥ H *ᵥ v + 2 * s * (g ⬝ᵥ v) +
      (g ⬝ᵥ H⁻¹ *ᵥ g + δ) * s ^ 2 := by
  have hmul : H *ᵥ (H⁻¹ *ᵥ g) = g := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hH.det_pos.ne'),
      Matrix.one_mulVec]
  have hsym : Hᵀ = H := hH.isHermitian.eq
  have hcross : (H⁻¹ *ᵥ g) ⬝ᵥ H *ᵥ v = g ⬝ᵥ v := by
    rw [dotProduct_mulVec, ← Matrix.mulVec_transpose, hsym, hmul]
  have heq : v ⬝ᵥ H *ᵥ v + 2 * s * (g ⬝ᵥ v) +
      (g ⬝ᵥ H⁻¹ *ᵥ g + δ) * s ^ 2 =
      (v + s • (H⁻¹ *ᵥ g)) ⬝ᵥ H *ᵥ (v + s • (H⁻¹ *ᵥ g)) + δ * s ^ 2 := by
    rw [Matrix.mulVec_add, Matrix.mulVec_smul, hmul]
    simp only [add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul,
      smul_eq_mul, hcross]
    rw [dotProduct_comm v g, dotProduct_comm (H⁻¹ *ᵥ g) g]
    ring
  rw [heq]
  by_cases hs : s = 0
  · rcases hsv with hsv | hv
    · exact (hsv hs).elim
    · simpa [hs] using hH.dotProduct_mulVec_pos hv
  · have hnonneg := hH.posSemidef.dotProduct_mulVec_nonneg (v + s • (H⁻¹ *ᵥ g))
    have hpos : 0 < δ * s ^ 2 := mul_pos hδ (sq_pos_of_ne_zero hs)
    simpa only [star_trivial] using add_pos_of_nonneg_of_pos hnonneg hpos

end LeanBlast.KLS

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.KLS_Spectral_BrascampLiebPerturbation
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.gaussianLineEquiv_apply _root_.OAI.LeanBlast.KLS.blMomentDeriv_zero _root_.OAI.LeanBlast.KLS.blMoment_zero _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Matrix
open scoped BigOperators ContDiff Topology Matrix.Norms.Elementwise

namespace LeanBlast.KLS

section Calculus

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  (V h q : E → ℝ)

variable {V h q}

theorem contDiff_blPerturbation (hV : ContDiff ℝ ∞ V) (hh : ContDiff ℝ ∞ h)
    (hq : ContDiff ℝ ∞ q) : ContDiff ℝ ∞ (blPerturbation V h q) := by
  unfold blPerturbation
  fun_prop

theorem fderiv_blPerturbation_apply (hV : ContDiff ℝ ∞ V) (hh : ContDiff ℝ ∞ h)
    (hq : ContDiff ℝ ∞ q) (p w : ℝ × E) :
    fderiv ℝ (blPerturbation V h q) p w =
      fderiv ℝ V p.2 w.2 + p.1 * fderiv ℝ h p.2 w.2 +
        p.1 ^ 2 / 2 * fderiv ℝ q p.2 w.2 + w.1 * (h p.2 + p.1 * q p.2) := by
  have ht : HasFDerivAt (fun r : ℝ × E => r.1) (ContinuousLinearMap.fst ℝ ℝ E) p :=
    hasFDerivAt_fst
  have hx : HasFDerivAt (fun r : ℝ × E => r.2) (ContinuousLinearMap.snd ℝ ℝ E) p :=
    hasFDerivAt_snd
  have hv' := (hV.differentiable (by simp) p.2).hasFDerivAt.comp p hx
  have hh' := (hh.differentiable (by simp) p.2).hasFDerivAt.comp p hx
  have hq' := (hq.differentiable (by simp) p.2).hasFDerivAt.comp p hx
  have hd := (hv'.add (ht.mul hh')).add (((ht.pow 2).mul_const (2 : ℝ)⁻¹).mul hq')
  simp only [Pi.add_def, Pi.mul_def, Function.comp_def] at hd
  change (fderiv ℝ (fun r : ℝ × E => V r.2 + r.1 * h r.2 + r.1 ^ 2 / 2 * q r.2) p) w = _
  simp only [div_eq_mul_inv]
  rw [hd.fderiv]
  simp
  ring

theorem second_fderiv_blPerturbation_apply (hV : ContDiff ℝ ∞ V) (hh : ContDiff ℝ ∞ h)
    (hq : ContDiff ℝ ∞ q) (p w : ℝ × E) :
    fderiv ℝ (fderiv ℝ (blPerturbation V h q)) p w w =
      fderiv ℝ (fderiv ℝ V) p.2 w.2 w.2 +
      p.1 * fderiv ℝ (fderiv ℝ h) p.2 w.2 w.2 +
      p.1 ^ 2 / 2 * fderiv ℝ (fderiv ℝ q) p.2 w.2 w.2 +
      2 * w.1 * (fderiv ℝ h p.2 w.2 + p.1 * fderiv ℝ q p.2 w.2) +
      w.1 ^ 2 * q p.2 := by
  have hF := contDiff_blPerturbation hV hh hq
  have heval := (((hF.fderiv_right (m := ∞) (by simp)).differentiable (by simp) p).hasFDerivAt.clm_apply
    (hasFDerivAt_const w p)).fderiv
  have he : fderiv ℝ (fderiv ℝ (blPerturbation V h q)) p w w =
      fderiv ℝ (fun r => fderiv ℝ (blPerturbation V h q) r w) p w := by
    rw [heval]
    simp
  rw [he]
  simp_rw [fderiv_blPerturbation_apply hV hh hq]
  have ht : HasFDerivAt (fun r : ℝ × E => r.1) (ContinuousLinearMap.fst ℝ ℝ E) p :=
    hasFDerivAt_fst
  have hx : HasFDerivAt (fun r : ℝ × E => r.2) (ContinuousLinearMap.snd ℝ ℝ E) p :=
    hasFDerivAt_snd
  have hDV := ((((hV.fderiv_right (m := ∞) (by simp)).differentiable (by simp) p.2).hasFDerivAt.clm_apply
    (hasFDerivAt_const w.2 p.2))).comp p hx
  have hDh := ((((hh.fderiv_right (m := ∞) (by simp)).differentiable (by simp) p.2).hasFDerivAt.clm_apply
    (hasFDerivAt_const w.2 p.2))).comp p hx
  have hDq := ((((hq.fderiv_right (m := ∞) (by simp)).differentiable (by simp) p.2).hasFDerivAt.clm_apply
    (hasFDerivAt_const w.2 p.2))).comp p hx
  have hh' := (hh.differentiable (by simp) p.2).hasFDerivAt.comp p hx
  have hq' := (hq.differentiable (by simp) p.2).hasFDerivAt.comp p hx
  have hd := (((hDV.add (ht.mul hDh)).add (((ht.pow 2).mul_const (2 : ℝ)⁻¹).mul hDq)).add
    ((hh'.add (ht.mul hq')).const_mul w.1))
  simp only [Pi.add_def, Pi.mul_def, Function.comp_def] at hd
  simp only [div_eq_mul_inv]
  rw [hd.fderiv]
  simp
  ring

end Calculus

theorem second_fderiv_blPerturbation_zero_pos {n : ℕ} {V h : Space n → ℝ}
    (hV : ContDiff ℝ ∞ V) (hh : ContDiff ℝ ∞ h)
    (hpos : ∀ x, (hessianMatrix V x).PosDef) {δ : ℝ} (hδ : 0 < δ)
    (x : Space n) (w : ℝ × Space n) (hw : w ≠ 0) :
    0 < fderiv ℝ (fderiv ℝ (blPerturbation V h (fun y => steinGamma V h h y + δ)))
      (0, x) w w := by
  have hq : ContDiff ℝ ∞ (fun y => steinGamma V h h y + δ) :=
    (contDiff_steinGamma_self hV hh hpos).add contDiff_const
  rw [second_fderiv_blPerturbation_apply hV hh hq]
  simp only [zero_mul, zero_pow (by norm_num : 2 ≠ 0), zero_div, add_zero]
  rw [second_fderiv_eq_hessianMatrix,
    fderiv_eq_gradient_dotProduct (hh.differentiable (by simp) x), steinGamma_self_eq_dotProduct]
  have hw' : w.1 ≠ 0 ∨ (fun i => w.2 i) ≠ 0 := by
    by_cases hs : w.1 = 0
    · right
      intro hv
      apply hw
      apply Prod.ext hs
      ext i
      exact congrFun hv i
    · exact Or.inl hs
  convert quadratic_schur_positive (hpos x) (fun i => gradient h x i) (fun i => w.2 i) hδ w.1 hw' using 1
  all_goals try with_reducible_and_instances rfl
  ring

theorem exists_blPerturbation_convex {n : ℕ} {V h : Space n → ℝ}
    (hV : ContDiff ℝ ∞ V) (hh : IsTestFunction h)
    (hpos : ∀ x, (hessianMatrix V x).PosDef) {δ : ℝ} (hδ : 0 < δ) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧
      ConvexOn ℝ (Ioo (-ε) ε ×ˢ (univ : Set (Space n)))
        (blPerturbation V h (fun x => steinGamma V h h x + δ)) := by
  let q : Space n → ℝ := steinGamma V h h
  let F : ℝ × Space n → ℝ := blPerturbation V h (fun x => q x + δ)
  let S : Set (Space n) := tsupport h ∪ tsupport q
  have hq : ContDiff ℝ ∞ q := contDiff_steinGamma_self hV hh.1 hpos
  have hqc : HasCompactSupport q := hasCompactSupport_steinGamma_self V hh
  have hS : IsCompact S := hh.2.isCompact.union hqc.isCompact
  have hF : ContDiff ℝ ∞ F := contDiff_blPerturbation hV hh.1 (hq.add contDiff_const)
  have hF2 : Continuous (fderiv ℝ (fderiv ℝ F)) :=
    ((hF.fderiv_right (m := ∞) (by simp)).fderiv_right (m := ∞) (by simp)).continuous
  let Ψ : ℝ × (Space n × (ℝ × Space n)) → ℝ :=
    fun p => fderiv ℝ (fderiv ℝ F) (p.1, p.2.1) p.2.2 p.2.2
  have hΨ : Continuous Ψ := by
    have ha : Continuous (fun p : ℝ × (Space n × (ℝ × Space n)) => (p.1, p.2.1)) := by fun_prop
    have hb : Continuous (fun p : ℝ × (Space n × (ℝ × Space n)) => p.2.2) := by fun_prop
    exact ((hF2.comp ha).clm_apply hb).clm_apply hb
  have hopen : IsOpen {p | 0 < Ψ p} := isOpen_lt continuous_const hΨ
  have hprod : ({0} : Set ℝ) ×ˢ (S ×ˢ Metric.sphere (0 : ℝ × Space n) 1) ⊆
      {p | 0 < Ψ p} := by
    rintro ⟨t, x, w⟩ ⟨ht, _, hw⟩
    have ht0 : t = 0 := by simpa using ht
    subst t
    have hw0 : w ≠ 0 := by
      intro heq
      simp [heq] at hw
    exact second_fderiv_blPerturbation_zero_pos hV hh.1 hpos hδ x w hw0
  obtain ⟨U, W, hU, _, h0U, hKW, hUW⟩ := generalized_tube_lemma
    isCompact_singleton (hS.prod (isCompact_sphere (0 : ℝ × Space n) 1)) hopen hprod
  have hzU : (0 : ℝ) ∈ U := h0U (by simp)
  obtain ⟨r, hr, hrU⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hzU)
  let ε : ℝ := min r 1
  have hε : 0 < ε := lt_min hr (by norm_num)
  refine ⟨ε, hε, min_le_right _ _, ?_⟩
  have hFtwo : ContDiff ℝ 2 F := hF.of_le (WithTop.coe_le_coe.mpr le_top)
  apply convexOn_of_second_fderiv_nonneg hFtwo
    ((convex_Ioo _ _).prod convex_univ)
  rintro ⟨t, x⟩ ⟨ht, _⟩ w
  by_cases hx : x ∈ S
  · by_cases hw : w = 0
    · simp [hw]
    · let u : ℝ × Space n := ‖w‖⁻¹ • w
      have hn : 0 < ‖w‖ := norm_pos_iff.mpr hw
      have hu : u ∈ Metric.sphere (0 : ℝ × Space n) 1 := by
        change dist (‖w‖⁻¹ • w) 0 = 1
        rw [dist_zero_right, norm_smul, Real.norm_eq_abs,
          abs_of_pos (inv_pos.mpr hn), inv_mul_cancel₀ hn.ne']
      have htU : t ∈ U := hrU (by
        rw [Metric.mem_ball, Real.dist_eq, sub_zero]
        exact (abs_lt.mpr ht).trans_le (min_le_left r 1))
      have hp : 0 < Ψ (t, x, u) := hUW ⟨htU, hKW ⟨hx, hu⟩⟩
      change 0 < fderiv ℝ (fderiv ℝ F) (t, x) (‖w‖⁻¹ • w) (‖w‖⁻¹ • w) at hp
      simp only [map_smul, _root_.smul_apply, smul_eq_mul] at hp
      exact ((mul_pos_iff_of_pos_left (inv_pos.mpr hn)).mp
        ((mul_pos_iff_of_pos_left (inv_pos.mpr hn)).mp hp)).le
  · have hx' : x ∉ tsupport h ∧ x ∉ tsupport q := by simpa only [S, mem_union, not_or] using hx
    have hh0 : h =ᶠ[𝓝 x] 0 := notMem_tsupport_iff_eventuallyEq.mp hx'.1
    have hq0 : q =ᶠ[𝓝 x] 0 := notMem_tsupport_iff_eventuallyEq.mp hx'.2
    have hqc0 : (fun y => q y + δ) =ᶠ[𝓝 x] (fun _ => δ) := by
      filter_upwards [hq0] with y hy
      simp only [Pi.zero_apply] at hy
      simp only [hy, zero_add]
    have hh1 : fderiv ℝ h x = 0 := by simpa using hh0.fderiv_eq (𝕜 := ℝ)
    have hh2 : fderiv ℝ (fderiv ℝ h) x = 0 := by
      simpa using (hh0.fderiv (𝕜 := ℝ)).fderiv_eq (𝕜 := ℝ)
    have hq1 : fderiv ℝ (fun y => q y + δ) x = 0 := by
      simpa using hqc0.fderiv_eq (𝕜 := ℝ)
    have hq2 : fderiv ℝ (fderiv ℝ (fun y => q y + δ)) x = 0 := by
      simpa using (hqc0.fderiv (𝕜 := ℝ)).fderiv_eq (𝕜 := ℝ)
    change 0 ≤ fderiv ℝ (fderiv ℝ (blPerturbation V h (fun y => q y + δ))) (t, x) w w
    rw [second_fderiv_blPerturbation_apply hV hh.1 (hq.add contDiff_const)]
    simp only [hh1, hh2, hq1, hq2, _root_.zero_apply,
      mul_zero, add_zero, hqc0.eq_of_nhds]
    apply add_nonneg
    · rw [second_fderiv_eq_hessianMatrix]
      simpa only [star_trivial] using
        (hpos x).posSemidef.dotProduct_mulVec_nonneg (fun i => w.2 i)
    · positivity

end LeanBlast.KLS

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.KLS_Spectral_BrascampLieb
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.gaussianLineEquiv_apply _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped ContDiff

namespace LeanBlast.KLS

variable {n : ℕ}

theorem exp_neg_blPerturbation (V h q : Space n → ℝ) (t : ℝ) (x : Space n) :
    Real.exp (-blPerturbation V h q (t, x)) =
      Real.exp (-V x) * blWeight t (h x) (q x) := by
  rw [blWeight, ← Real.exp_add]
  congr 1
  dsimp [blPerturbation]
  ring

theorem blMoment_potentialMeasure (V h q : Space n → ℝ) (t : ℝ) :
    blMoment (potentialMeasure V) h q t =
      (∫ x, Real.exp (-blPerturbation V h q (t, x))) / potentialPartition V := by
  rw [blMoment, integral_potentialMeasure]
  simp_rw [exp_neg_blPerturbation]

theorem concaveOn_blLogMoment_of_convex {V h q : Space n → ℝ} {B ε : ℝ}
    (hV : Measurable V) (hVint : Integrable (fun x => Real.exp (-V x)))
    (hh : Measurable h) (hq : Measurable q)
    (hhB : ∀ x, |h x| ≤ B) (hqB : ∀ x, |q x| ≤ B) (hε1 : ε ≤ 1)
    (hc : ConvexOn ℝ (Ioo (-ε) ε ×ˢ (univ : Set (Space n)))
      (blPerturbation V h q)) :
    ConcaveOn ℝ (Ioo (-ε) ε) (blLogMoment (potentialMeasure V) h q) := by
  let : IsProbabilityMeasure (potentialMeasure V) := isProbabilityMeasure_potentialMeasure hVint
  have hint : ∀ t ∈ Ioo (-ε) ε, Integrable (fun x => Real.exp (-blPerturbation V h q (t, x))) := by
    intro t ht
    have hk : Integrable (fun x => blWeight t (h x) (q x)) (potentialMeasure V) :=
      boundedKernel_integrable blWeight continuous_blWeight hh hq hhB hqB
        ⟨by linarith [ht.1], by linarith [ht.2]⟩
    simpa only [exp_neg_blPerturbation] using (integrable_potentialMeasure_iff hVint _).mp hk
  have hm : ∀ t ∈ Ioo (-ε) ε, Measurable (fun x => Real.exp (-blPerturbation V h q (t, x))) := by
    intro t _
    dsimp [blPerturbation]
    fun_prop
  have hp := concaveOn_log_integral_exp_neg (convex_Ioo (-ε) ε) (blPerturbation V h q) hc hm hint
  refine (hp.add_const (-Real.log (potentialPartition V))).congr ?_
  intro t ht
  rw [blLogMoment, blMoment_potentialMeasure,
    Real.log_div (integral_exp_pos (hint t ht)).ne' (potentialPartition_pos hVint).ne']
  simp only [Pi.add_apply]
  ring

theorem brascamp_lieb {V h : Space n → ℝ}
    (hV : ContDiff ℝ ∞ V) (hVint : Integrable (fun x => Real.exp (-V x)))
    (hpos : ∀ x, (hessianMatrix V x).PosDef) (hh : IsTestFunction h) :
    variance (potentialMeasure V) h ≤
      ∫ x, steinGamma V h h x ∂potentialMeasure V := by
  let : IsProbabilityMeasure (potentialMeasure V) := isProbabilityMeasure_potentialMeasure hVint
  have hq := contDiff_steinGamma_self hV hh.1 hpos
  have hqc := hasCompactSupport_steinGamma_self V hh
  have hqint : Integrable (steinGamma V h h) (potentialMeasure V) :=
    hq.continuous.integrable_of_hasCompactSupport hqc
  obtain ⟨Bh, hBh⟩ := hh.2.exists_bound_of_continuous hh.continuous
  obtain ⟨Bq, hBq⟩ := hqc.exists_bound_of_continuous hq.continuous
  apply le_of_forall_pos_le_add
  intro δ hδ
  let B : ℝ := max Bh (Bq + |δ|)
  have hhB : ∀ x, |h x| ≤ B := by
    intro x
    have hb : |h x| ≤ Bh := by simpa only [Real.norm_eq_abs] using hBh x
    exact hb.trans (le_max_left _ _)
  have hqB : ∀ x, |steinGamma V h h x + δ| ≤ B := by
    intro x
    calc
      |steinGamma V h h x + δ| ≤ |steinGamma V h h x| + |δ| := abs_add_le _ _
      _ ≤ Bq + |δ| := by
        have hb : |steinGamma V h h x| ≤ Bq := by simpa only [Real.norm_eq_abs] using hBq x
        linarith
      _ ≤ B := le_max_right _ _
  obtain ⟨ε, hε, hε1, hc⟩ := exists_blPerturbation_convex hV hh hpos hδ
  have hqm : Measurable (fun x => steinGamma V h h x + δ) :=
    (hq.continuous.add continuous_const).measurable
  have hlog := concaveOn_blLogMoment_of_convex hV.continuous.measurable hVint
    hh.continuous.measurable hqm hhB hqB hε1 hc
  have hb := variance_le_integral_of_concave_blLogMoment (potentialMeasure V)
    hh.continuous.measurable hqm hhB hqB hε hε1 hlog
  calc
    variance (potentialMeasure V) h ≤
        ∫ x, (steinGamma V h h x + δ) ∂potentialMeasure V := hb
    _ = (∫ x, steinGamma V h h x ∂potentialMeasure V) + δ := by
      rw [integral_add hqint (integrable_const δ)]
      simp

end LeanBlast.KLS

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.KLS_Spectral_RegularPoincare
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Matrix
open scoped BigOperators ContDiff

namespace LeanBlast.KLS

theorem quadratic_inverse_upper_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    {H : Matrix ι ι ℝ} (hH : H.PosDef) {t : ℝ} (ht : 0 ≤ t)
    (hlower : ∀ v : ι → ℝ, t * (v ⬝ᵥ v) ≤ v ⬝ᵥ H *ᵥ v) (g : ι → ℝ) :
    t * (g ⬝ᵥ H⁻¹ *ᵥ g) ≤ g ⬝ᵥ g := by
  let v := H⁻¹ *ᵥ g
  have hmul : H *ᵥ v = g := by
    rw [show v = H⁻¹ *ᵥ g from rfl, Matrix.mulVec_mulVec,
      Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hH.det_pos.ne'), Matrix.one_mulVec]
  have hl : t * (v ⬝ᵥ v) ≤ g ⬝ᵥ v := by
    simpa only [hmul, dotProduct_comm v g] using hlower v
  have hsq : 0 ≤ (g - t • v) ⬝ᵥ (g - t • v) :=
    Finset.sum_nonneg fun i _ => mul_self_nonneg ((g - t • v) i)
  have heq : (g - t • v) ⬝ᵥ (g - t • v) =
      g ⬝ᵥ g - 2 * t * (g ⬝ᵥ v) + t ^ 2 * (v ⬝ᵥ v) := by
    simp only [sub_dotProduct, dotProduct_sub, smul_dotProduct, dotProduct_smul,
      smul_eq_mul, dotProduct_comm v g]
    ring
  rw [heq] at hsq
  change t * (g ⬝ᵥ v) ≤ g ⬝ᵥ g
  nlinarith [mul_le_mul_of_nonneg_left hl ht]

theorem IsRegularPotential.hessianMatrix_posDef {n : ℕ} {V : Space n → ℝ} {t t' : ℝ}
    (hV : IsRegularPotential V t t') (x : Space n) : (hessianMatrix V x).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
  · rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial]
    exact (hessianMatrix_isSymm
      ((hV.contDiff.of_le (WithTop.coe_le_coe.mpr le_top) : ContDiff ℝ 2 V).contDiffAt)).eq
  · intro v hv
    let w : Space n := WithLp.toLp 2 v
    have hw : w ≠ 0 := by
      intro heq
      apply hv
      funext i
      exact congrArg (fun u : Space n => u i) heq
    simpa only [second_fderiv_eq_hessianMatrix, w, PiLp.toLp_apply, star_trivial] using
      hV.hessian_pos x hw

theorem IsRegularPotential.steinGamma_self_le {n : ℕ} {V : Space n → ℝ} {t t' : ℝ}
    (hV : IsRegularPotential V t t') (h : Space n → ℝ) (x : Space n) :
    t * steinGamma V h h x ≤ ‖gradient h x‖ ^ 2 := by
  have hlower : ∀ v : Fin n → ℝ,
      t * (v ⬝ᵥ v) ≤ v ⬝ᵥ hessianMatrix V x *ᵥ v := by
    intro v
    have hv := hV.lower_bound x (WithLp.toLp 2 v)
    rw [EuclideanSpace.real_norm_sq_eq] at hv
    simpa only [second_fderiv_eq_hessianMatrix,
      PiLp.toLp_apply, dotProduct, pow_two] using hv
  have hb := quadratic_inverse_upper_bound (hV.hessianMatrix_posDef x) hV.lower_pos.le
    hlower (fun i => gradient h x i)
  rw [steinGamma_self_eq_dotProduct, EuclideanSpace.real_norm_sq_eq]
  simpa only [dotProduct, pow_two] using hb

theorem IsRegularPotential.poincare {n : ℕ} {V f : Space n → ℝ} {t t' : ℝ}
    (hV : IsRegularPotential V t t')
    (hVint : Integrable (fun x => Real.exp (-V x))) (hf : IsTestFunction f) :
    t * variance (potentialMeasure V) f ≤ dirichletEnergy (potentialMeasure V) f := by
  let : IsProbabilityMeasure (potentialMeasure V) := isProbabilityMeasure_potentialMeasure hVint
  have hqint : Integrable (steinGamma V f f) (potentialMeasure V) :=
    (contDiff_steinGamma_self hV.contDiff hf.1 hV.hessianMatrix_posDef).continuous.integrable_of_hasCompactSupport
      (hasCompactSupport_steinGamma_self V hf)
  calc
    t * variance (potentialMeasure V) f ≤
        t * (∫ x, steinGamma V f f x ∂potentialMeasure V) :=
      mul_le_mul_of_nonneg_left
        (brascamp_lieb hV.contDiff hVint hV.hessianMatrix_posDef hf) hV.lower_pos.le
    _ = ∫ x, t * steinGamma V f f x ∂potentialMeasure V := (integral_const_mul _ _).symm
    _ ≤ ∫ x, ‖gradient f x‖ ^ 2 ∂potentialMeasure V :=
      integral_mono (hqint.const_mul t) (hf.integrable_gradient_sq _) (hV.steinGamma_self_le f)
    _ = dirichletEnergy (potentialMeasure V) f := rfl

end LeanBlast.KLS

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_GaussianPoincare
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.gaussianLineEquiv_apply _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! One-dimensional Gaussian Poincare inequality derived from the
Brascamp–Lieb theorem. This is the spectral input needed for the
transverse oscillator; no spectral assertion is assumed here. -/

noncomputable section
open MeasureTheory
open scoped Topology ContDiff
namespace ContinuumCoulomb
open LeanBlast.KLS

private theorem gaussianPotential_derivative (freq : ℝ) :
    fderiv ℝ (gaussianPotential freq) =
      ⇑((2*freq) • (innerSL ℝ (E := Space 1))) := by
  funext x
  have h := ((hasStrictFDerivAt_norm_sq x).hasFDerivAt.const_mul freq).fderiv
  change fderiv ℝ (fun y : Space 1 => freq*‖y‖^2) x = _
  rw [h]
  ext v
  simp only [smul_apply,two_smul,add_apply,smul_eq_mul]
  ring

private theorem gaussianPotential_hessian (freq : ℝ) (x v : Space 1) :
    fderiv ℝ (fderiv ℝ (gaussianPotential freq)) x v v = (2*freq)*‖v‖^2 := by
  rw [gaussianPotential_derivative]
  rw [(((2*freq) • (innerSL ℝ (E := Space 1))).hasFDerivAt (x := x)).fderiv]
  change (2*freq)*inner ℝ v v = (2*freq)*‖v‖^2
  rw [real_inner_self_eq_norm_sq]

private theorem gaussianPotential_regular {freq : ℝ} (hf : 0 < freq) :
    IsRegularPotential (gaussianPotential freq) (2*freq) (2*freq) where
  contDiff := contDiff_const.mul (contDiff_norm_sq ℝ)
  lower_pos := by positivity
  le_upper := le_rfl
  lower_bound x v := (gaussianPotential_hessian freq x v).ge
  upper_bound x v := (gaussianPotential_hessian freq x v).le

private theorem gaussianPotential_integrable {freq : ℝ} (hf : 0 < freq) :
    Integrable (fun x => Real.exp (-gaussianPotential freq x)) := by
  have h := GaussianFourier.integrable_cexp_neg_mul_sq_norm_add
    (V := Space 1) (b := (freq:ℂ)) (by simpa using hf) 0 0
  have hc : Integrable (fun x : Space 1 => Complex.exp ((-freq*‖x‖^2:ℝ):ℂ)) := by
    simpa only [zero_mul,add_zero,Complex.ofReal_mul,Complex.ofReal_neg,
      Complex.ofReal_pow] using h
  simpa only [Complex.norm_exp,Complex.ofReal_re,gaussianPotential,neg_mul] using hc.norm

theorem gaussian_weight_integrable {freq : ℝ} (hf : 0 < freq) :
    Integrable (fun x : Space 1 => Real.exp (-(freq*‖x‖^2))) :=
  gaussianPotential_integrable hf

/-- Gaussian variance is bounded by its Dirichlet form with the exact
oscillator gap constant. -/
theorem gaussian_poincare_test {freq : ℝ} (hf : 0 < freq)
    (f : Space 1 → ℝ) (hs : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) :
    (2*freq)*variance (potentialMeasure (fun x : Space 1 => freq*‖x‖^2)) f ≤
      dirichletEnergy (potentialMeasure (fun x : Space 1 => freq*‖x‖^2)) f :=
  (gaussianPotential_regular hf).poincare (gaussianPotential_integrable hf) ⟨hs,hc⟩

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_GaussianLine
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Identifying the one-dimensional Euclidean Gaussian form with the real
line. This fixes the normalization and derivative constants for the oscillator. -/

noncomputable section
open MeasureTheory
open scoped Topology ContDiff
namespace ContinuumCoulomb
open LeanBlast.KLS

theorem gaussianLine_integral (f : ℝ → ℝ) :
    (∫ x : Space 1, f (gaussianLineEquiv x)) = ∫ y : ℝ, f y :=
  gaussianLineEquiv.measurePreserving.integral_comp
    gaussianLineEquiv.toHomeomorph.measurableEmbedding f

theorem gaussianLine_norm_sq (x : Space 1) : ‖x‖^2=(gaussianLineEquiv x)^2 := by
  rw [← gaussianLineEquiv.norm_map,Real.norm_eq_abs,sq_abs]

theorem gaussianLine_gradient_sq {f : ℝ → ℝ} (hf : Differentiable ℝ f) (x : Space 1) :
    ‖gradient (fun y => f (gaussianLineEquiv y)) x‖^2 =
      (deriv f (gaussianLineEquiv x))^2 := by
  have hd := ((hf (gaussianLineEquiv x)).hasDerivAt.hasFDerivAt.comp x
    gaussianLineEquiv.toContinuousLinearEquiv.toContinuousLinearMap.hasFDerivAt).fderiv
  change ‖(InnerProductSpace.toDual ℝ (Space 1)).symm
    (fderiv ℝ (f ∘ gaussianLineEquiv) x)‖^2 = _
  rw [hd]
  rw [(InnerProductSpace.toDual ℝ (Space 1)).symm.norm_map]
  have hder : (ContinuousLinearMap.toSpanSingleton ℝ (deriv f (gaussianLineEquiv x))).comp
      gaussianLineEquiv.toContinuousLinearEquiv.toContinuousLinearMap =
      deriv f (gaussianLineEquiv x) • gaussianLineEquiv.toContinuousLinearEquiv.toContinuousLinearMap := by
    ext y
    simp
    ring
  rw [hder,norm_smul,gaussianLineEquiv.norm_toContinuousLinearMap]
  simp [sq_abs]

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_GaussianScalar
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Normalized Gaussian variance and energy on the real line. -/

noncomputable section
open MeasureTheory
open scoped Topology ContDiff
namespace ContinuumCoulomb
open LeanBlast.KLS

theorem gaussianLine_expectation {freq : ℝ} (hf : 0 < freq) (f : ℝ → ℝ) :
    (∫ x : Space 1, f (gaussianLineEquiv x)
      ∂potentialMeasure (fun x : Space 1 => freq*‖x‖^2)) =
      ∫ z : ℝ, verticalMode freq z^2*f z := by
  rw [integral_potentialMeasure]
  have hw (x : Space 1) : Real.exp (-(freq*‖x‖^2)) =
      Real.exp (-freq*(gaussianLineEquiv x)^2) := by
    rw [gaussianLine_norm_sq]
    congr 1
    ring
  have hp : potentialPartition (fun x : Space 1 => freq*‖x‖^2) =
      Real.sqrt (Real.pi/freq) := by
    unfold potentialPartition
    simp_rw [hw]
    rw [gaussianLine_integral (fun z => Real.exp (-freq*z^2)),integral_gaussian]
  rw [hp]
  simp_rw [hw]
  rw [gaussianLine_integral (fun z => Real.exp (-freq*z^2)*f z),← integral_div]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun z => by
    dsimp only
    rw [verticalMode_square hf]
    ring

/-- The exact weighted Poincare constant for compact smooth real functions. -/
theorem gaussian_scalar_poincare_smooth {freq : ℝ} (hf : 0 < freq)
    (f : ℝ → ℝ) (hs : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) :
    (2*freq)*((∫ z : ℝ, verticalMode freq z^2*f z^2) -
      (∫ z : ℝ, verticalMode freq z^2*f z)^2) ≤
        ∫ z : ℝ, verticalMode freq z^2*(deriv f z)^2 := by
  let F : Space 1 → ℝ := fun x => f (gaussianLineEquiv x)
  have hF : IsTestFunction F := ⟨hs.comp gaussianLineEquiv.contDiff,
    hc.comp_homeomorph gaussianLineEquiv.toHomeomorph⟩
  let _ := isProbabilityMeasure_potentialMeasure (gaussian_weight_integrable hf)
  have h := gaussian_poincare_test hf F hF.1 hF.2
  rw [variance_eq_integral_sq_sub_sq _ (hF.integrable _) (hF.integrable_sq _)] at h
  change (2*freq)*((∫ x : Space 1, f (gaussianLineEquiv x)^2 ∂_) -
    (∫ x : Space 1, f (gaussianLineEquiv x) ∂_)^2) ≤
    (∫ x : Space 1, ‖gradient F x‖^2 ∂_) at h
  simp_rw [show ∀ x, ‖gradient F x‖^2 = (deriv f (gaussianLineEquiv x))^2 from
    gaussianLine_gradient_sq (hs.differentiable (by simp))] at h
  rw [gaussianLine_expectation hf (fun z => f z^2),gaussianLine_expectation hf f,
    gaussianLine_expectation hf (fun z => deriv f z^2)] at h
  exact h

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_ScalarMollification
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compact smooth approximation on the real line, including its derivative.
Only the one-dimensional approximation needed by the oscillator is built. -/

noncomputable section
open MeasureTheory Filter ContinuousLinearMap
open scoped Topology Convolution ContDiff
namespace ContinuumCoulomb

theorem scalarMollifier_tendsto :
    Tendsto (fun k => (scalarMollifier k).rOut) atTop (𝓝 0) := by
  have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul 2
  simpa only [scalarMollifier,mul_one_div,mul_zero] using h

theorem scalarMollification_smooth {f : ℝ → ℝ} (hf : Continuous f) (k : ℕ) :
    ContDiff ℝ ∞ (scalarMollification f k) :=
  (scalarMollifier k).hasCompactSupport_normed.contDiff_convolution_left
    (lsmul ℝ ℝ) (scalarMollifier k).contDiff_normed hf.locallyIntegrable

theorem scalarMollification_compact {f : ℝ → ℝ} (hf : HasCompactSupport f) (k : ℕ) :
    HasCompactSupport (scalarMollification f k) :=
  (scalarMollifier k).hasCompactSupport_normed.convolution (lsmul ℝ ℝ) hf

theorem scalarMollification_tendsto {f : ℝ → ℝ} (hf : Continuous f) (z : ℝ) :
    Tendsto (fun k => scalarMollification f k z) atTop (𝓝 (f z)) :=
  ContDiffBump.convolution_tendsto_right_of_continuous scalarMollifier_tendsto hf z

theorem scalarMollification_deriv {f : ℝ → ℝ}
    (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f) (k : ℕ) :
    deriv (scalarMollification f k) = scalarMollification (deriv f) k := by
  funext z
  have hs : ContDiff ℝ ∞ ((scalarMollifier k).normed volume) :=
    (scalarMollifier k).contDiff_normed
  exact (hc.hasDerivAt_convolution_right (lsmul ℝ ℝ)
    hs.continuous.locallyIntegrable hf z).deriv

theorem scalarMollification_bound {f : ℝ → ℝ} {C : ℝ}
    (hC : ∀ z, ‖f z‖ ≤ C) (k : ℕ) (z : ℝ) :
    ‖scalarMollification f k z‖ ≤ C := by
  have hs : ContDiff ℝ ∞ ((scalarMollifier k).normed volume) :=
    (scalarMollifier k).contDiff_normed
  have hi : Integrable ((scalarMollifier k).normed volume) :=
    hs.continuous.integrable_of_hasCompactSupport (scalarMollifier k).hasCompactSupport_normed
  have h := norm_integral_le_of_norm_le (hi.mul_const C)
    (Filter.Eventually.of_forall fun y => show
      ‖(scalarMollifier k).normed volume y * f (z-y)‖ ≤
        (scalarMollifier k).normed volume y*C by
      rw [norm_mul,Real.norm_eq_abs,abs_of_nonneg ((scalarMollifier k).nonneg_normed y)]
      exact mul_le_mul_of_nonneg_left (hC (z-y)) ((scalarMollifier k).nonneg_normed y))
  simpa only [scalarMollification,convolution,lsmul_apply,smul_eq_mul,
    integral_mul_const,(scalarMollifier k).integral_normed,one_mul] using h

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_GaussianMollification
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Passing the proved Gaussian Poincare inequality to compact C¹ tests. -/

noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff
namespace ContinuumCoulomb

theorem gaussian_mollification_power_tendsto {freq : ℝ} (hf : 0 < freq)
    (f : ℝ → ℝ) (hs : Continuous f) (hc : HasCompactSupport f) (p : ℕ) :
    Tendsto (fun k => ∫ z : ℝ, verticalMode freq z^2*(scalarMollification f k z)^p)
      atTop (𝓝 (∫ z : ℝ, verticalMode freq z^2*f z^p)) := by
  obtain ⟨C,hC⟩ := hs.bounded_above_of_compact_support hc
  apply tendsto_integral_of_dominated_convergence
    (fun z => verticalMode freq z^2*C^p)
  · intro k
    exact (((verticalMode_smooth freq).continuous.pow 2).mul
      ((scalarMollification_smooth hs k).continuous.pow p)).aestronglyMeasurable
  · exact (verticalMode_square_integrable hf).mul_const _
  · intro k
    apply Filter.Eventually.of_forall
    intro z
    have hb := pow_le_pow_left₀ (norm_nonneg (scalarMollification f k z))
      (scalarMollification_bound hC k z) p
    simpa only [norm_mul,norm_pow,Real.norm_eq_abs,sq_abs] using
      mul_le_mul_of_nonneg_left hb (sq_nonneg (verticalMode freq z))
  · exact Filter.Eventually.of_forall fun z =>
      ((scalarMollification_tendsto hs z).pow p).const_mul _

/-- The normalized Gaussian Poincare inequality on the exact C¹ test domain. -/
theorem gaussian_scalar_poincare {freq : ℝ} (hf : 0 < freq)
    (f : ℝ → ℝ) (hs : ContDiff ℝ 1 f) (hc : HasCompactSupport f) :
    (2*freq)*((∫ z : ℝ, verticalMode freq z^2*f z^2) -
      (∫ z : ℝ, verticalMode freq z^2*f z)^2) ≤
        ∫ z : ℝ, verticalMode freq z^2*(deriv f z)^2 := by
  have h2 := gaussian_mollification_power_tendsto hf f hs.continuous hc 2
  have h1 := gaussian_mollification_power_tendsto hf f hs.continuous hc 1
  simp only [pow_one] at h1
  have hd := gaussian_mollification_power_tendsto hf (deriv f)
    (hs.continuous_deriv (by norm_num)) hc.deriv 2
  apply le_of_tendsto_of_tendsto ((h2.sub (h1.pow 2)).const_mul (2*freq)) hd
  apply Filter.Eventually.of_forall
  intro k
  have h := gaussian_scalar_poincare_smooth hf (scalarMollification f k)
    (scalarMollification_smooth hs.continuous k) (scalarMollification_compact hc k)
  simpa only [scalarMollification_deriv hs hc] using h

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
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_PlanarLocalization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual compact localization on the planar Sobolev graph. Multiplication
by a compactly supported C¹ function is constructed on L² classes and their gradients,
then factored through the proved supported Rellich inclusion. -/

noncomputable section
open MeasureTheory
open scoped BigOperators Topology
namespace ContinuumCoulomb
namespace PlanarSobolev
open RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean

attribute [local instance] OAI.ContinuumCoulomb.PlanarSobolev.instLocalizationMeasurable
attribute [local instance] OAI.ContinuumCoulomb.PlanarSobolev.instLocalizationBorel
attribute [local instance] OAI.ContinuumCoulomb.PlanarSobolev.instLocalizationMeasure
theorem testLocalizedL2_compact (h : Test) : IsCompactOperator (testLocalizedL2 h) := by
  exact (isCompactOperator_h1OnToL2 h.property.2
    (isClosed_tsupport h.val).measurableSet).comp_clm (testSupportedMultiplier h)

theorem wellTest_operator : (testScalarField wellTest ℝ).operator = wellMultiplier := by
  apply ContinuousLinearMap.ext
  intro u
  apply Lp.ext
  filter_upwards [(testScalarField wellTest ℝ).applyLp_ae u, wellMultiply_ae u] with x h₁ h₂
  change (testScalarField wellTest ℝ).applyLp u x = wellMultiply u x
  rw [h₁, h₂]
  rfl

theorem wellMultiplier_compact :
    IsCompactOperator (wellMultiplier.comp (h1ToL2 (μ := volume) (E := PlanarPosition))) := by
  have he : testLocalizedL2 wellTest =
      wellMultiplier.comp (h1ToL2 (μ := volume) (E := PlanarPosition)) := by
    apply ContinuousLinearMap.ext
    intro u
    change (testScalarField wellTest ℝ).operator u.val.1 = wellMultiplier u.val.1
    rw [wellTest_operator]
  rw [← he]
  exact testLocalizedL2_compact wellTest

end PlanarSobolev
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

theorem form_smul (c : ℝ) (u : Target) : form (c • u) = c ^ 2 * form u := by
  change (1 / 2 : ℝ) * ‖c • u.2‖ ^ 2 + inner ℝ (c • u.1) (wellMultiplier (c • u.1)) = _
  rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, map_smul,
    real_inner_smul_left, real_inner_smul_right]
  unfold form
  ring

theorem mode_mass_positive : 0 < ‖mode.val.1‖ ^ 2 := by
  rw [mode_mass]
  exact planarResolventMode_square_integral_positive

end PlanarSobolev
end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_PlanarProjectionGap
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

end ContinuumCoulomb.PlanarSobolev

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_PlanarCompactnessEstimates
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compactness estimates for the actual manufactured planar well. They
reduce the positive gap to uniqueness of its attained ground vector. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb.PlanarSobolev

local instance instPlanarCompactnessEstimatesMeasurable_r1554e2_1 : MeasurableSpace PlanarPosition := borel PlanarPosition
local instance instPlanarCompactnessEstimatesBorel_r1554e2_1 : BorelSpace PlanarPosition := ⟨rfl⟩
local instance instPlanarCompactnessEstimatesMeasure_r1554e2_1 : MeasureSpace PlanarPosition := measureSpaceOfInnerProductSpace
theorem shiftedForm_parallelogram (u v : Target) :
    shiftedForm (u+v)+shiftedForm (u-v) = 2*shiftedForm u+2*shiftedForm v := by
  have hp := shiftedForm_add_smul u v 1
  have hm := shiftedForm_add_smul u v (-1)
  simp only [one_smul,one_mul,one_pow] at hp
  simp only [neg_one_smul,neg_one_mul,neg_one_sq,one_mul] at hm
  rw [sub_eq_add_neg]
  linarith

theorem shiftedForm_sub_le (u v : Sobolev) :
    shiftedForm (u-v).val ≤ 2*shiftedForm u.val+2*shiftedForm v.val := by
  have he := shiftedForm_parallelogram u.val v.val
  have hn := shiftedForm_nonnegative (u+v)
  change 0 ≤ shiftedForm (u.val+v.val) at hn
  change shiftedForm (u.val-v.val) ≤ _
  linarith

theorem shiftedForm_controls_norm (u : Sobolev) :
    ‖u‖^2 ≤ 2*shiftedForm u.val +
      2*‖u.val.1‖*‖wellMultiplier u.val.1‖ := by
  have hi := (abs_le.mp (abs_real_inner_le_norm u.val.1 (wellMultiplier u.val.1))).1
  change (max ‖u.val.1‖ ‖u.val.2‖)^2 ≤ _
  unfold shiftedForm form
  rcases le_total ‖u.val.1‖ ‖u.val.2‖ with h | h
  · rw [max_eq_right h]
    nlinarith [sq_nonneg ‖u.val.1‖]
  · rw [max_eq_left h]
    nlinarith [sq_nonneg ‖u.val.2‖]

theorem nearGround_norm_bound (u : Sobolev) (hm : ‖u.val.1‖ ≤ 1)
    (hs : shiftedForm u.val ≤ 1) : ‖u‖ ≤ 3+2*‖wellMultiplier‖ := by
  have he := shiftedForm_controls_norm u
  have hw := wellMultiplier.le_opNorm u.val.1
  have hW := norm_nonneg wellMultiplier
  have hmul : ‖u.val.1‖*‖wellMultiplier u.val.1‖ ≤ ‖wellMultiplier‖ := by
    calc
      _ ≤ 1*(‖wellMultiplier‖*1) := mul_le_mul hm
        (hw.trans (mul_le_mul_of_nonneg_left hm hW)) (norm_nonneg _) (by norm_num)
      _ = _ := by ring
  nlinarith [norm_nonneg u,sq_nonneg ‖wellMultiplier‖]

theorem nearGround_distance_bound (u v : Sobolev)
    (hu : ‖u.val.1‖ ≤ 1) (hv : ‖v.val.1‖ ≤ 1) :
    dist u v ^ 2 ≤ 4*shiftedForm u.val+4*shiftedForm v.val+
      4*dist (wellMultiplier u.val.1) (wellMultiplier v.val.1) := by
  have hs := shiftedForm_controls_norm (u-v)
  have hd := shiftedForm_sub_le u v
  have hm : ‖(u-v).val.1‖ ≤ 2 := (norm_sub_le _ _).trans (by linarith)
  have hmul := mul_le_mul_of_nonneg_right hm (norm_nonneg (wellMultiplier (u-v).val.1))
  rw [dist_eq_norm,dist_eq_norm,← map_sub]
  change ‖u-v‖^2 ≤ _
  change ‖u-v‖^2 ≤ 2*shiftedForm (u-v).val+
    2*‖u.val.1-v.val.1‖*‖wellMultiplier (u.val.1-v.val.1)‖ at hs
  change shiftedForm (u-v).val ≤ _ at hd
  change ‖u.val.1-v.val.1‖*‖wellMultiplier (u.val.1-v.val.1)‖ ≤
    2*‖wellMultiplier (u.val.1-v.val.1)‖ at hmul
  linarith

end ContinuumCoulomb.PlanarSobolev

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_PlanarWeakConstant
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.planarHeatResolventPrimitive_zero _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A locally integrable planar function with zero distributional gradient
is constant almost everywhere. This is the uniqueness step needed after the
ground-state transform; it uses actual compact mollifiers. -/

noncomputable section
open MeasureTheory Filter ContinuousLinearMap
open scoped Topology Convolution ContDiff
namespace ContinuumCoulomb

attribute [local instance] OAI.ContinuumCoulomb.instPlanarWeakConstantMeasurable
attribute [local instance] OAI.ContinuumCoulomb.instPlanarWeakConstantBorel
attribute [local instance] OAI.ContinuumCoulomb.instPlanarWeakConstantMeasure
theorem planarMollifier_tendsto :
    Tendsto (fun k => (planarMollifier k).rOut) atTop (𝓝 0) := by
  have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul 2
  simpa only [planarMollifier,mul_one_div,mul_zero] using h

private theorem planar_real_convolution_comm (f g : PlanarPosition → ℝ) :
    f ⋆ g = g ⋆ f := by
  ext x
  rw [convolution_eq_swap,convolution_def]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun _ => mul_comm _ _)

private theorem planar_reflected_derivative (κ : PlanarPosition → ℝ)
    (hκ : ContDiff ℝ ∞ κ) (x y e : PlanarPosition) :
    fderiv ℝ (fun z => κ (x-z)) y e = -(fderiv ℝ κ (x-y) e) := by
  have hd := ((hκ.differentiable (by simp) (x-y)).hasFDerivAt).comp y
    ((hasFDerivAt_id y).const_sub x)
  change HasFDerivAt (fun z => κ (x-z)) _ y at hd
  rw [hd.fderiv]
  simp

theorem planar_mollification_weak_zero (f : PlanarPosition → ℝ)
    (hf : LocallyIntegrable f)
    (hw : ∀ (φ : PlanarPosition → ℝ), ContDiff ℝ ∞ φ → HasCompactSupport φ →
      ∀ e, (∫ x, f x*fderiv ℝ φ x e) = 0) (k : ℕ) (x e : PlanarPosition) :
    fderiv ℝ ((planarMollifier k).normed volume ⋆ f) x e = 0 := by
  let κ := (planarMollifier k).normed volume
  have hκ : ContDiff ℝ ∞ κ := (planarMollifier k).contDiff_normed
  have hc : HasCompactSupport κ := (planarMollifier k).hasCompactSupport_normed
  have ht := hw (fun y => κ (x-y)) (hκ.comp (contDiff_const.sub contDiff_id))
    (hc.comp_homeomorph (Homeomorph.subLeft x)) e
  simp_rw [planar_reflected_derivative κ hκ x,mul_neg,integral_neg,neg_eq_zero] at ht
  rw [planar_real_convolution_comm κ f,
    (hc.hasFDerivAt_convolution_right (lsmul ℝ ℝ) hf (hκ.of_le (by first | simp | exact_mod_cast le_top)) x).fderiv,
    convolution_precompR_apply (lsmul ℝ ℝ) hf (hc.fderiv ℝ)
      (hκ.continuous_fderiv (by simp)) x e]
  simpa only [convolution_def,lsmul_apply,smul_eq_mul] using ht

theorem planar_weak_gradient_zero_constant (f : PlanarPosition → ℝ)
    (hf : LocallyIntegrable f)
    (hw : ∀ (φ : PlanarPosition → ℝ), ContDiff ℝ ∞ φ → HasCompactSupport φ →
      ∀ e, (∫ x, f x*fderiv ℝ φ x e) = 0) :
    ∃ c : ℝ, f =ᵐ[volume] fun _ => c := by
  let F (k : ℕ) : PlanarPosition → ℝ := (planarMollifier k).normed volume ⋆ f
  have hconst (k : ℕ) (x y : PlanarPosition) : F k x = F k y := by
    have hs : ContDiff ℝ ∞ (F k) :=
      (planarMollifier k).hasCompactSupport_normed.contDiff_convolution_left
        (lsmul ℝ ℝ) (planarMollifier k).contDiff_normed hf
    apply is_const_of_fderiv_eq_zero (hs.differentiable (by simp))
    intro z
    ext e
    exact planar_mollification_weak_zero f hf hw k z e
  have ht : ∀ᵐ x ∂volume, Tendsto (fun k => F k x) atTop (𝓝 (f x)) := by
    apply ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable
      (φ := planarMollifier) (K := 2) planarMollifier_tendsto _ hf
    exact Filter.Eventually.of_forall (fun k => by simp [planarMollifier,div_eq_mul_inv])
  obtain ⟨x,hx⟩ := ht.exists
  refine ⟨f x,?_⟩
  filter_upwards [ht] with y hy
  have he : (fun k => F k y) = (fun k => F k x) := funext (fun k => hconst k y x)
  rw [he] at hy
  exact tendsto_nhds_unique hy hx

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_PlanarDistributionAxes
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.planarHeatResolventPrimitive_zero _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The two coordinate distributional derivatives determine the full planar
weak gradient. -/

noncomputable section
open MeasureTheory
open scoped BigOperators ContDiff
namespace ContinuumCoulomb

attribute [local instance] OAI.ContinuumCoulomb.instPlanarDistributionAxesMeasurable
attribute [local instance] OAI.ContinuumCoulomb.instPlanarDistributionAxesBorel
attribute [local instance] OAI.ContinuumCoulomb.instPlanarDistributionAxesMeasure
theorem planar_axis_expansion (e : PlanarPosition) :
    e = ∑ a : Fin 2, e a • planarAxis a := by
  ext j
  fin_cases j <;> simp [planarAxis]

theorem planar_zero_axis_distribution_constant (f : PlanarPosition → ℝ)
    (hf : LocallyIntegrable f)
    (hw : ∀ (ψ : PlanarPosition → ℝ), ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      ∀ a : Fin 2, (∫ x, f x*planarPartial ψ (planarAxis a) x) = 0) :
    ∃ c : ℝ, f =ᵐ[volume] fun _ => c := by
  apply planar_weak_gradient_zero_constant f hf
  intro ψ hψ hc e
  have hi (a : Fin 2) : Integrable (fun x => f x*planarPartial ψ (planarAxis a) x) := by
    simpa only [smul_eq_mul] using hf.integrable_smul_right_of_hasCompactSupport
      (planarPartial_continuous (hψ.of_le (by first | simp | exact_mod_cast le_top)) _)
      (hc.fderiv_apply ℝ (planarAxis a))
  have he : (fun x => f x*fderiv ℝ ψ x e) =
      (fun x => ∑ a : Fin 2, e a*(f x*planarPartial ψ (planarAxis a) x)) := by
    funext x
    have hd : fderiv ℝ ψ x e = ∑ a : Fin 2, e a*planarPartial ψ (planarAxis a) x := by
      calc
        _ = fderiv ℝ ψ x (∑ a : Fin 2, e a • planarAxis a) :=
          congrArg (fderiv ℝ ψ x) (planar_axis_expansion e)
        _ = _ := by simp only [map_sum,map_smul,smul_eq_mul,planarPartial]
    rw [hd,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    ring
  rw [he,integral_finsetSum _ (fun a _ => (hi a).const_mul _)]
  simp_rw [integral_const_mul,hw ψ hψ hc,mul_zero]
  simp

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_PlanarNearGroundCompactness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compactness of normalized near-ground sequences for the actual well.
The positive free form makes compactness of the potential multiplier enough. -/

noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace ContinuumCoulomb.PlanarSobolev
open RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean

attribute [local instance] OAI.ContinuumCoulomb.PlanarSobolev.instPlanarNearGroundCompactnessMeasurable
attribute [local instance] OAI.ContinuumCoulomb.PlanarSobolev.instPlanarNearGroundCompactnessBorel
attribute [local instance] OAI.ContinuumCoulomb.PlanarSobolev.instPlanarNearGroundCompactnessMeasure
theorem nearGround_cauchy_of_potential_cauchy (u : ℕ → Sobolev)
    (hm : ∀ n, ‖(u n).val.1‖ ≤ 1)
    (hs : Tendsto (fun n => shiftedForm (u n).val) atTop (𝓝 0))
    (hw : CauchySeq (fun n => wellMultiplier (u n).val.1)) : CauchySeq u := by
  apply Metric.cauchySeq_iff.mpr
  intro ε hε
  have hδ : 0 < ε^2/16 := by positivity
  obtain ⟨N,hN⟩ := Metric.tendsto_atTop.mp hs (ε^2/16) hδ
  obtain ⟨M,hM⟩ := Metric.cauchySeq_iff.mp hw (ε^2/16) hδ
  refine ⟨max N M,fun n hn m hm' => ?_⟩
  have hn' : shiftedForm (u n).val < ε^2/16 := by
    have h := hN n ((le_max_left _ _).trans hn)
    simpa only [dist_zero_right,Real.norm_eq_abs,
      abs_of_nonneg (shiftedForm_nonnegative (u n))] using h
  have hm'' : shiftedForm (u m).val < ε^2/16 := by
    have h := hN m ((le_max_left _ _).trans hm')
    simpa only [dist_zero_right,Real.norm_eq_abs,
      abs_of_nonneg (shiftedForm_nonnegative (u m))] using h
  have hd := hM n ((le_max_right _ _).trans hn) m ((le_max_right _ _).trans hm')
  have he := nearGround_distance_bound (u n) (u m) (hm n) (hm m)
  nlinarith [(dist_nonneg : 0 ≤ dist (u n) (u m))]

theorem nearGround_subsequence (u : ℕ → Sobolev)
    (hm : ∀ n, ‖(u n).val.1‖ ≤ 1) (hb : ∀ n, shiftedForm (u n).val ≤ 1)
    (hs : Tendsto (fun n => shiftedForm (u n).val) atTop (𝓝 0)) :
    ∃ v : Sobolev, ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (u ∘ φ) atTop (𝓝 v) := by
  let W := wellMultiplier.comp (h1ToL2 (μ := volume) (E := PlanarPosition))
  obtain ⟨K,hK,hWK⟩ := wellMultiplier_compact.image_closedBall_subset_compact
    (3+2*‖wellMultiplier‖)
  have hmem (n : ℕ) : W (u n) ∈ K := by
    apply hWK
    refine ⟨u n,?_,rfl⟩
    rw [Metric.mem_closedBall,dist_zero_right]
    exact nearGround_norm_bound (u n) (hm n) (hb n)
  obtain ⟨w,_hw,φ,hφ,hlim⟩ := hK.tendsto_subseq hmem
  have hW : CauchySeq (fun n => wellMultiplier (u (φ n)).val.1) := hlim.cauchySeq
  have hc := nearGround_cauchy_of_potential_cauchy (u ∘ φ)
    (fun n => hm (φ n)) (hs.comp hφ.tendsto_atTop) hW
  obtain ⟨v,hv⟩ := cauchySeq_tendsto_of_complete hc
  exact ⟨v,φ,hφ,hv⟩

end ContinuumCoulomb.PlanarSobolev

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_PlanarGapFromUniqueness
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual planar well has a positive excitation gap once its zero-form
space is the line of the proved normalized ground mode. Compactness here is
proved directly, with no spectral or planar-gap input used. -/

noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace ContinuumCoulomb.PlanarSobolev
open RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean

attribute [local instance] OAI.ContinuumCoulomb.PlanarSobolev.instPlanarGapFromUniquenessMeasurable
attribute [local instance] OAI.ContinuumCoulomb.PlanarSobolev.instPlanarGapFromUniquenessBorel
attribute [local instance] OAI.ContinuumCoulomb.PlanarSobolev.instPlanarGapFromUniquenessMeasure
theorem normalized_gap_of_ground_uniqueness
    (hker : ∀ u : Sobolev, shiftedForm u.val = 0 →
      inner ℝ u.val.1 normalizedMode.val.1 = 0 → u = 0) :
    ∃ γ : ℝ, 0 < γ ∧ ∀ u : Sobolev, ‖u.val.1‖^2 = 1 →
      inner ℝ u.val.1 normalizedMode.val.1 = 0 → γ ≤ shiftedForm u.val := by
  by_contra h
  push Not at h
  have hex (n : ℕ) : ∃ u : Sobolev, ‖u.val.1‖^2 = 1 ∧
      inner ℝ u.val.1 normalizedMode.val.1 = 0 ∧
        shiftedForm u.val < 1/((n:ℝ)+1) :=
    h (1/((n:ℝ)+1)) (by positivity)
  choose u hm ho hs using hex
  have ht : Tendsto (fun n => shiftedForm (u n).val) atTop (𝓝 0) :=
    squeeze_zero (fun n => shiftedForm_nonnegative (u n)) (fun n => (hs n).le)
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hmass (n : ℕ) : ‖(u n).val.1‖ ≤ 1 := by
    nlinarith [hm n,norm_nonneg (u n).val.1]
  have hbound (n : ℕ) : shiftedForm (u n).val ≤ 1 := by
    apply (hs n).le.trans
    exact (div_le_one (by positivity)).mpr (by linarith [Nat.cast_nonneg (α := ℝ) n])
  obtain ⟨v,φ,hφ,hv⟩ := nearGround_subsequence u hmass hbound ht
  have hcv : Continuous (fun u : Sobolev => ‖u.val.1‖^2) :=
    (h1ToL2 (μ := volume) (E := PlanarPosition)).continuous.norm.pow 2
  have hmassv : ‖v.val.1‖^2 = 1 := by
    apply tendsto_nhds_unique (hcv.continuousAt.tendsto.comp hv)
    change Tendsto (fun n => ‖(u (φ n)).val.1‖^2) atTop (𝓝 1)
    simp_rw [hm]
    exact tendsto_const_nhds
  have hcs : Continuous (fun u : Sobolev => shiftedForm u.val) :=
    (form_continuous.comp continuous_subtype_val).add (continuous_const.mul hcv)
  have hzero : shiftedForm v.val = 0 :=
    tendsto_nhds_unique (hcs.continuousAt.tendsto.comp hv) (ht.comp hφ.tendsto_atTop)
  have hco : Continuous (fun u : Sobolev => inner ℝ u.val.1 normalizedMode.val.1) :=
    (h1ToL2 (μ := volume) (E := PlanarPosition)).continuous.inner continuous_const
  have hov : inner ℝ v.val.1 normalizedMode.val.1 = 0 := by
    apply tendsto_nhds_unique (hco.continuousAt.tendsto.comp hv)
    change Tendsto (fun n => inner ℝ (u (φ n)).val.1 normalizedMode.val.1) atTop (𝓝 0)
    simp_rw [ho]
    exact tendsto_const_nhds
  have hz := hker v hzero hov
  norm_num [hz] at hmassv

theorem shiftedForm_smul (c : ℝ) (u : Target) :
    shiftedForm (c • u) = c^2*shiftedForm u := by
  unfold shiftedForm
  rw [form_smul]
  change c^2*form u+(1/2:ℝ)*‖c • u.1‖^2 = _
  rw [norm_smul,mul_pow,Real.norm_eq_abs,sq_abs]
  ring

theorem planar_gap_of_ground_uniqueness
    (hker : ∀ u : Sobolev, shiftedForm u.val = 0 →
      inner ℝ u.val.1 normalizedMode.val.1 = 0 → u = 0) :
    ∃ γ : ℝ, 0 < γ ∧ ∀ u : Sobolev,
      inner ℝ u.val.1 normalizedMode.val.1 = 0 →
      ((-1/2:ℝ)+γ)*‖u.val.1‖^2 ≤ form u.val := by
  obtain ⟨γ,hγ,hgap⟩ := normalized_gap_of_ground_uniqueness hker
  refine ⟨γ,hγ,fun u ho => ?_⟩
  have h : γ*‖u.val.1‖^2 ≤ shiftedForm u.val := by
    by_cases hn : ‖u.val.1‖ = 0
    · simpa only [hn,zero_pow (by decide : (2:ℕ) ≠ 0),mul_zero] using shiftedForm_nonnegative u
    let v : Sobolev := ‖u.val.1‖⁻¹ • u
    have hm : ‖v.val.1‖^2 = 1 := by
      change ‖‖u.val.1‖⁻¹ • u.val.1‖^2 = 1
      rw [norm_smul,mul_pow,Real.norm_eq_abs,sq_abs,inv_pow]
      exact inv_mul_cancel₀ (pow_ne_zero 2 hn)
    have hov : inner ℝ v.val.1 normalizedMode.val.1 = 0 := by
      change inner ℝ (‖u.val.1‖⁻¹ • u.val.1) normalizedMode.val.1 = 0
      rw [real_inner_smul_left,ho,mul_zero]
    calc
      _ ≤ shiftedForm v.val*‖u.val.1‖^2 :=
        mul_le_mul_of_nonneg_right (hgap v hm hov) (sq_nonneg _)
      _ = shiftedForm u.val := by
        change shiftedForm (‖u.val.1‖⁻¹ • u.val)*‖u.val.1‖^2 = _
        rw [shiftedForm_smul]
        field_simp [hn]
  unfold shiftedForm at h
  linarith

end ContinuumCoulomb.PlanarSobolev

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_PlanarGroundIdentity
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact ground-state transform for the actual manufactured planar well. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb

theorem planarGroundQuotient_C1 {u : PlanarPosition → ℝ} (hu : ContDiff ℝ 1 u) :
    ContDiff ℝ 1 (planarGroundQuotient u) :=
  hu.div (planarResolventMode_C7.of_le (by norm_num))
    (fun x => (planarResolventMode_positive x).ne')

theorem planarGroundQuotient_compact {u : PlanarPosition → ℝ} (hc : HasCompactSupport u) :
    HasCompactSupport (planarGroundQuotient u) := by
  change HasCompactSupport (fun x => u x*(planarResolventMode x)⁻¹)
  exact hc.mul_right

theorem planarGroundQuotient_energy (u : PlanarPosition → ℝ)
    (hu : ContDiff ℝ 1 u) (hc : HasCompactSupport u) :
    (∑ a : Fin 2, ∫ x, planarResolventMode x^2 *
      planarPartial (planarGroundQuotient u) (planarAxis a) x^2) =
      2*planarTestForm manufacturedPlanarWell u + ∫ x, u x^2 := by
  let phi := planarResolventMode
  let v := planarGroundQuotient u
  have hp : ContDiff ℝ 2 phi := planarResolventMode_C7.of_le (by norm_num)
  have hv : ContDiff ℝ 1 v := planarGroundQuotient_C1 hu
  have hvc : HasCompactSupport v := planarGroundQuotient_compact hc
  have hfactor (x : PlanarPosition) : phi x*v x = u x := by
    dsimp [phi,v,planarGroundQuotient]
    field_simp [(planarResolventMode_positive x).ne']
  have hf : (fun x => phi x*v x) = u := funext hfactor
  have hB (x : PlanarPosition) : phi x*planarLaplacian phi x*v x^2 =
      (2*manufacturedPlanarWell x+1)*u x^2 := by
    rw [manufacturedPlanarWell_eigen_equation]
    calc
      _ = (2*manufacturedPlanarWell x+1)*(phi x*v x)^2 := by ring
      _ = _ := by rw [hfactor]
  have hc2 : HasCompactSupport (fun x => u x^2) :=
    hc.comp_left (g := fun t : ℝ => t^2) (by norm_num)
  have hiP : Integrable (fun x => manufacturedPlanarWell x*u x^2) :=
    (manufacturedPlanarWell_C7.continuous.mul (hu.continuous.pow 2)).integrable_of_hasCompactSupport
      hc2.mul_left
  have hiM : Integrable (fun x => u x^2) :=
    (hu.continuous.pow 2).integrable_of_hasCompactSupport hc2
  have hpot : (∫ x, (2*manufacturedPlanarWell x+1)*u x^2) =
      2*(∫ x, manufacturedPlanarWell x*u x^2)+(∫ x, u x^2) := by
    rw [show (fun x => (2*manufacturedPlanarWell x+1)*u x^2) =
      (fun x => 2*(manufacturedPlanarWell x*u x^2)+u x^2) from by funext x; ring]
    rw [integral_add (hiP.const_mul 2) hiM,integral_const_mul]
  calc
    _ = ∑ a : Fin 2, ∫ x, planarPartial (fun y => phi y*v y) (planarAxis a) x^2+
        phi x*planarPartial (planarPartial phi (planarAxis a)) (planarAxis a) x*v x^2 := by
      exact Finset.sum_congr rfl (fun a _ => (planar_ground_transform_direction phi v hp hv hvc _).symm)
    _ = (∑ a : Fin 2, ∫ x, planarPartial u (planarAxis a) x^2)+
        ∫ x, (2*manufacturedPlanarWell x+1)*u x^2 := by
      rw [planar_transform_energy_split phi v hp hv hvc,hf]
      simp_rw [hB]
    _ = _ := by
      rw [hpot]
      unfold planarTestForm
      ring

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_PlanarTestCauchy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The integral Cauchy–Schwarz estimate used in the planar ground-state
duality argument, on actual compact real test functions. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

private theorem planar_toLp_inner (f g : PlanarPosition → ℝ)
    (hf : MemLp f 2) (hg : MemLp g 2) :
    inner ℝ (hf.toLp f) (hg.toLp g) = ∫ x, f x*g x := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp,hg.coeFn_toLp] with x hx hy
  rw [hx,hy,RCLike.inner_apply,conj_trivial]
  ring

private theorem planar_toLp_sq (f : PlanarPosition → ℝ) (hf : MemLp f 2) :
    ‖hf.toLp f‖^2 = ∫ x, f x^2 := by
  rw [← real_inner_self_eq_norm_sq,planar_toLp_inner f f hf hf]
  simp only [pow_two]

theorem planar_test_cauchy_square (f g : PlanarPosition → ℝ)
    (hf : Continuous f) (hg : Continuous g)
    (hfc : HasCompactSupport f) (hgc : HasCompactSupport g) :
    (∫ x, f x*g x)^2 ≤ (∫ x, f x^2)*(∫ x, g x^2) := by
  have hfi : MemLp f 2 := hf.memLp_of_hasCompactSupport hfc
  have hgi : MemLp g 2 := hg.memLp_of_hasCompactSupport hgc
  have h := (sq_le_sq₀ (abs_nonneg (inner ℝ (hfi.toLp f) (hgi.toLp g)))
    (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr
      (abs_real_inner_le_norm (hfi.toLp f) (hgi.toLp g))
  simpa only [sq_abs,mul_pow,planar_toLp_inner,planar_toLp_sq] using h

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_PlanarGroundDuality
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A compact-test distributional gradient is controlled by the exact
ground-state energy. This estimate survives closure of the Sobolev graph. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb

theorem planar_ground_dual_bound (u ψ : PlanarPosition → ℝ)
    (hu : ContDiff ℝ 1 u) (huc : HasCompactSupport u)
    (hψ : ContDiff ℝ 1 ψ) (hψc : HasCompactSupport ψ) (a : Fin 2) :
    (∫ x, planarGroundQuotient u x*planarPartial ψ (planarAxis a) x)^2 ≤
      (∫ x, (ψ x/planarResolventMode x)^2)*
        (2*planarTestForm manufacturedPlanarWell u+∫ x, u x^2) := by
  let v := planarGroundQuotient u
  have hv : ContDiff ℝ 1 v := planarGroundQuotient_C1 hu
  have hvc : HasCompactSupport v := planarGroundQuotient_compact huc
  have hdc : HasCompactSupport (planarPartial v (planarAxis a)) :=
    hvc.fderiv_apply ℝ _
  have hd : Continuous (planarPartial v (planarAxis a)) := planarPartial_continuous hv _
  have hψd : Continuous (planarPartial ψ (planarAxis a)) := planarPartial_continuous hψ _
  have hiA : Integrable (fun x => planarPartial v (planarAxis a) x*ψ x) :=
    (hd.mul hψ.continuous).integrable_of_hasCompactSupport hdc.mul_right
  have hiB : Integrable (fun x => v x*planarPartial ψ (planarAxis a) x) :=
    (hv.continuous.mul hψd).integrable_of_hasCompactSupport hvc.mul_right
  have hiFG : Integrable (fun x => v x*ψ x) :=
    (hv.continuous.mul hψ.continuous).integrable_of_hasCompactSupport hvc.mul_right
  have hibp := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable hiA hiB hiFG
    (fun x _ => hv.differentiable (by norm_num) x)
    (fun x _ => hψ.differentiable (by norm_num) x)
  change (∫ x, v x*planarPartial ψ (planarAxis a) x) =
    -(∫ x, planarPartial v (planarAxis a) x*ψ x) at hibp
  let F := fun x => planarResolventMode x*planarPartial v (planarAxis a) x
  let G := fun x => ψ x/planarResolventMode x
  have hF : Continuous F := planarResolventMode_C7.continuous.mul hd
  have hG : Continuous G := hψ.continuous.div planarResolventMode_C7.continuous
    (fun x => (planarResolventMode_positive x).ne')
  have hFc : HasCompactSupport F := hdc.mul_left
  have hGc : HasCompactSupport G := planarGroundQuotient_compact hψc
  have he (x : PlanarPosition) : F x*G x = planarPartial v (planarAxis a) x*ψ x := by
    dsimp [F,G]
    field_simp [(planarResolventMode_positive x).ne']
  have hCS := planar_test_cauchy_square F G hF hG hFc hGc
  simp_rw [he] at hCS
  have hf2 : (∫ x, F x^2) =
      ∫ x, planarResolventMode x^2*planarPartial v (planarAxis a) x^2 := by
    simp only [F,mul_pow]
  rw [hf2] at hCS
  have hsingle : (∫ x, planarResolventMode x^2*planarPartial v (planarAxis a) x^2) ≤
      2*planarTestForm manufacturedPlanarWell u+∫ x, u x^2 := by
    rw [← planarGroundQuotient_energy u hu huc]
    apply Finset.single_le_sum (f := fun b : Fin 2 => ∫ x : PlanarPosition,
      planarResolventMode x^2*planarPartial v (planarAxis b) x^2)
    · intro b _
      exact integral_nonneg (fun x => mul_nonneg (sq_nonneg _) (sq_nonneg _))
    · exact Finset.mem_univ a
  have hn : 0 ≤ ∫ x, G x^2 := integral_nonneg (fun _ => sq_nonneg _)
  have hb := hCS.trans (mul_le_mul_of_nonneg_right hsingle hn)
  change (∫ x, v x*planarPartial ψ (planarAxis a) x)^2 ≤ _
  rw [hibp,neg_sq]
  exact hb.trans_eq (mul_comm _ _)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_PlanarSobolevDuality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Ground-state duality on the full closed planar Sobolev graph. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb.PlanarSobolev
open RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean

attribute [local instance] OAI.ContinuumCoulomb.PlanarSobolev.instPlanarSobolevDualityMeasurable
attribute [local instance] OAI.ContinuumCoulomb.PlanarSobolev.instPlanarSobolevDualityBorel
attribute [local instance] OAI.ContinuumCoulomb.PlanarSobolev.instPlanarSobolevDualityMeasure
theorem groundDualLp_inner (u : Lp ℝ 2 (volume : Measure PlanarPosition))
    (ψ : Test) (a : Fin 2) :
    inner ℝ u (groundDualLp ψ a) =
      ∫ x, (u x/planarResolventMode x)*planarPartial ψ.val (planarAxis a) x := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(groundDualWeight_memLp ψ a).coeFn_toLp] with x hx
  change inner ℝ (u x) ((groundDualWeight_memLp ψ a).toLp (groundDualWeight ψ a) x) = _
  rw [hx,RCLike.inner_apply,conj_trivial]
  unfold groundDualWeight
  ring

theorem graph_groundDualLp_inner (u ψ : Test) (a : Fin 2) :
    inner ℝ (graph (μ := volume) u).1 (groundDualLp ψ a) =
      ∫ x, planarGroundQuotient u.val x*planarPartial ψ.val (planarAxis a) x := by
  rw [groundDualLp_inner]
  apply integral_congr_ae
  filter_upwards [(memLp_of_mem_C1c (μ := volume) u.property).coeFn_toLp] with x hx
  change (toL2 (μ := volume) u x/planarResolventMode x)*_ = _
  change toL2 (μ := volume) u x = u.val x at hx
  rw [hx]
  rfl

theorem graph_ground_dual_bound (u ψ : Test) (a : Fin 2) :
    (inner ℝ (graph (μ := volume) u).1 (groundDualLp ψ a))^2 ≤
      originalIntegral (fun x => (ψ.val x/planarResolventMode x)^2)*
        (2*shiftedForm (graph (μ := volume) u)) := by
  have h := planar_ground_dual_bound u.val ψ.val u.property.1 u.property.2
    ψ.property.1 ψ.property.2 a
  change (originalIntegral (fun x => planarGroundQuotient u.val x*
    planarPartial ψ.val (planarAxis a) x))^2 ≤
    originalIntegral (fun x => (ψ.val x/planarResolventMode x)^2)*
      (2*planarTestForm manufacturedPlanarWell u.val+originalIntegral (fun x => u.val x^2)) at h
  rw [graph_groundDualLp_inner,shiftedForm,graph_form,graph_mass]
  simp_rw [planar_integral_change_borel (borel PlanarPosition) ⟨rfl⟩]
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  ring

theorem sobolev_ground_dual_bound (u : Sobolev) (ψ : Test) (a : Fin 2) :
    (inner ℝ u.val.1 (groundDualLp ψ a))^2 ≤
      originalIntegral (fun x => (ψ.val x/planarResolventMode x)^2)*(2*shiftedForm u.val) := by
  have hS : Continuous (fun v : Target => shiftedForm v) :=
    form_continuous.add (continuous_const.mul (continuous_fst.norm.pow 2))
  have hc : IsClosed {v : Target | (inner ℝ v.1 (groundDualLp ψ a))^2 ≤
      originalIntegral (fun x => (ψ.val x/planarResolventMode x)^2)*(2*shiftedForm v)} :=
    isClosed_le ((continuous_fst.inner continuous_const).pow 2)
      (continuous_const.mul (continuous_const.mul hS))
  apply closure_minimal (s := (LinearMap.range (graph (μ := volume) (E := PlanarPosition)) : Set Target))
    (t := {v : Target | (inner ℝ v.1 (groundDualLp ψ a))^2 ≤
      originalIntegral (fun x => (ψ.val x/planarResolventMode x)^2)*(2*shiftedForm v)}) ?_ hc u.property
  rintro _ ⟨f,rfl⟩
  exact graph_ground_dual_bound f ψ a

theorem zero_ground_form_axis_distribution (u : Sobolev) (hzero : shiftedForm u.val = 0)
    (ψ : PlanarPosition → ℝ) (hψ : ContDiff ℝ 1 ψ) (hψc : HasCompactSupport ψ) (a : Fin 2) :
    (∫ x, (u.val.1 x/planarResolventMode x)*planarPartial ψ (planarAxis a) x) = 0 := by
  let p : Test := ⟨ψ,hψ,hψc⟩
  have hb := sobolev_ground_dual_bound u p a
  rw [hzero,mul_zero,mul_zero] at hb
  have he : inner ℝ u.val.1 (groundDualLp p a) = 0 := by nlinarith [sq_nonneg (inner ℝ u.val.1 (groundDualLp p a))]
  rw [groundDualLp_inner] at he
  exact he

end ContinuumCoulomb.PlanarSobolev

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_PlanarGroundUniqueness
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniqueness and the actual manufactured planar ground gap, proved on the
full closed Sobolev graph without the published spectral hypothesis. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb.PlanarSobolev

attribute [local instance] OAI.ContinuumCoulomb.PlanarSobolev.instPlanarGroundUniquenessMeasurable
attribute [local instance] OAI.ContinuumCoulomb.PlanarSobolev.instPlanarGroundUniquenessBorel
attribute [local instance] OAI.ContinuumCoulomb.PlanarSobolev.instPlanarGroundUniquenessMeasure
theorem zero_ground_form_multiple (u : Sobolev) (hzero : shiftedForm u.val = 0) :
    ∃ c : ℝ, u.val.1 = c • mode.val.1 := by
  have hloc : LocallyIntegrable (fun x => u.val.1 x/planarResolventMode x) := by
    have hli : LocallyIntegrable (fun x : PlanarPosition => u.val.1 x) :=
      (Lp.memLp u.val.1).locallyIntegrable (by norm_num)
    have hi : Continuous (fun x : PlanarPosition => (planarResolventMode x)⁻¹) :=
      planarResolventMode_C7.continuous.inv₀
      (fun x => (planarResolventMode_positive x).ne')
    have hh : LocallyIntegrable (fun x : PlanarPosition => u.val.1 x*(planarResolventMode x)⁻¹) :=
      LocallyIntegrable.mul_continuous hi hli
    simpa only [div_eq_mul_inv] using hh
  obtain ⟨c,hc⟩ := planar_zero_axis_distribution_constant
    (fun x => u.val.1 x/planarResolventMode x) hloc (fun ψ hψ hψc a =>
      zero_ground_form_axis_distribution u hzero ψ (hψ.of_le (by first | simp | exact_mod_cast le_top)) hψc a)
  refine ⟨c,Lp.ext ?_⟩
  have hmode : mode.val.1 =ᵐ[volume] planarResolventMode := mode_memLp.coeFn_toLp
  filter_upwards [hc,hmode,Lp.coeFn_smul c mode.val.1] with x hx hm hs
  rw [hs]
  change u.val.1 x = c*mode.val.1 x
  rw [hm]
  exact (div_eq_iff (planarResolventMode_positive x).ne').mp hx

theorem zero_ground_form_orthogonal (u : Sobolev) (hzero : shiftedForm u.val = 0)
    (ho : inner ℝ u.val.1 normalizedMode.val.1 = 0) : u = 0 := by
  obtain ⟨c,hu⟩ := zero_ground_form_multiple u hzero
  rw [hu] at ho
  change inner ℝ (c • mode.val.1) ((Real.sqrt (‖mode.val.1‖^2))⁻¹ • mode.val.1) = 0 at ho
  rw [real_inner_smul_left,real_inner_smul_right,real_inner_self_eq_norm_sq] at ho
  have hcoef : (Real.sqrt (‖mode.val.1‖^2))⁻¹*‖mode.val.1‖^2 ≠ 0 :=
    mul_ne_zero (inv_ne_zero (Real.sqrt_pos.mpr mode_mass_positive).ne') mode_mass_positive.ne'
  have hc : c = 0 := (mul_eq_zero.mp ho).resolve_right hcoef
  have hu0 : u.val.1 = 0 := by simpa only [hc,zero_smul] using hu
  have hgrad : ‖u.val.2‖^2 = 0 := by
    simp only [shiftedForm,form,hu0,map_zero,inner_zero_left,norm_zero,zero_pow (by decide : (2:ℕ) ≠ 0),
      mul_zero,add_zero] at hzero
    linarith
  have hg0 : u.val.2 = 0 := norm_eq_zero.mp (sq_eq_zero_iff.mp hgrad)
  apply Subtype.ext
  exact Prod.ext hu0 hg0

/-- Positive gap above the actual manufactured well's attained ground mode. -/
theorem manufacturedPlanarWell_gap_proved :
    ∃ γ : ℝ, 0 < γ ∧ ∀ u : Sobolev,
      inner ℝ u.val.1 normalizedMode.val.1 = 0 →
      ((-1/2:ℝ)+γ)*‖u.val.1‖^2 ≤ form u.val :=
  planar_gap_of_ground_uniqueness zero_ground_form_orthogonal

end ContinuumCoulomb.PlanarSobolev

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_SobolevDensity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The whole-space H=W specialization required by the two continuum
reductions. The approximation is constructed by normalized smooth convolution,
with no published density hypothesis remaining. -/

noncomputable section
open MeasureTheory Filter
open scoped Topology BigOperators
namespace ContinuumCoulomb

theorem complexMollification_error_tendsto {n : ℕ} {u : Configuration n → ℂ}
    (hu : MemLp u 2) :
    Tendsto (fun k => ∫ x, ‖u x-complexMollification u k x‖^2) atTop (𝓝 0) := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    exact Eventually.of_forall (fun k => ha.trans_le (integral_nonneg (fun x => sq_nonneg _)))
  · intro a ha
    exact complexMollification_error hu ha

theorem mollifiedH1_gradient {n : ℕ} (u : Coulomb.H1Vector n) (k : ℕ)
    (s : SpinConfiguration n) (a : Fin n × Fin 3) (x : Configuration n) :
    (mollifiedH1 u k).gradient s a x = complexMollification (u.gradient s a) k x :=
  complexMollification_partial (u.value_L2 s) (u.partial_L2 s a)
    (EuclideanSpace.single a 1) (u.weak_partial s a) k x

theorem mollifiedH1_error_tendsto {n : ℕ} (u : Coulomb.H1Vector n) :
    Tendsto (fun k => h1GraphError u (mollifiedH1 u k)) atTop (𝓝 0) := by
  have hv := tendsto_finsetSum Finset.univ (fun s _ =>
    complexMollification_error_tendsto (u.value_L2 s))
  have hg := tendsto_finsetSum Finset.univ (fun s _ =>
    tendsto_finsetSum Finset.univ (fun a _ =>
      complexMollification_error_tendsto (u.partial_L2 s a)))
  unfold h1GraphError
  simp_rw [mollifiedH1_gradient]
  simpa only [mollifiedH1,classicalH1State,Finset.sum_const_zero,add_zero] using hv.add hg

/-- Meyers–Serrin, H=W, specialized to the full Euclidean weak-H1 space,
proved here by the explicit convolution sequence. -/
theorem publishedSobolevSmoothDensity : PublishedSobolevSmoothDensity := by
  intro n u ε hε
  have he := (tendsto_order.mp (mollifiedH1_error_tendsto u)).2 ε hε
  obtain ⟨k,hk⟩ := he.exists
  refine ⟨fun s => complexMollification (u.value s) k,
    fun s => complexMollification_smooth (u.value_L2 s) k,
    fun s => complexMollification_memLp (u.value_L2 s) k,?_,hk⟩
  intro s a
  have heq := complexMollification_partial (u.value_L2 s) (u.partial_L2 s a)
    (EuclideanSpace.single a 1) (u.weak_partial s a) k
  simp_rw [heq]
  exact complexMollification_memLp (u.partial_L2 s a) k

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

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_VerticalFactorization
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The oscillator ground-state transform on compact C¹ functions, with all
boundary terms discharged by compact support. -/

noncomputable section
open MeasureTheory
open scoped ContDiff
namespace ContinuumCoulomb

theorem vertical_cross_integrable (u : ℝ → ℝ) (hu : ContDiff ℝ 1 u)
    (hc : HasCompactSupport u) : Integrable (fun z => 2*z*u z*deriv u z) := by
  have hd := hu.continuous_deriv (by norm_num)
  exact (((continuous_const.mul continuous_id).mul hu.continuous).mul hd).integrable_of_hasCompactSupport
    hc.deriv.mul_left

theorem vertical_cross_identity (u : ℝ → ℝ) (hu : ContDiff ℝ 1 u)
    (hc : HasCompactSupport u) :
    (∫ z : ℝ, 2*z*u z*deriv u z) = -(∫ z : ℝ, u z^2) := by
  have hd (z : ℝ) : deriv (fun x => u x^2) z = 2*u z*deriv u z := by
    have h := (hu.differentiable (by norm_num) z).hasDerivAt
    have hh := h.fun_mul h
    have he : (fun x => u x*u x) = (fun x => u x^2) := by funext x; ring
    rw [he] at hh
    rw [hh.deriv]
    ring
  have hc2 : HasCompactSupport (fun z => u z^2) :=
    hc.comp_left (g := fun x : ℝ => x^2) (by norm_num)
  have hA : Integrable (fun z => fderiv ℝ (fun x => u x^2) z 1*z) := by
    have he : (fun z => fderiv ℝ (fun x => u x^2) z 1*z) =
        (fun z => 2*z*u z*deriv u z) := by
      funext z
      rw [fderiv_apply_one_eq_deriv,hd]
      ring
    rw [he]
    exact vertical_cross_integrable u hu hc
  have hB : Integrable (fun z => u z^2*fderiv ℝ (fun x : ℝ => x) z 1) := by
    have hcont : Continuous (fun z => u z^2) := by fun_prop
    have hi : Integrable (fun z => u z^2) := hcont.integrable_of_hasCompactSupport hc2
    simpa only [fderiv_apply_one_eq_deriv,deriv_id'',mul_one] using hi
  have hfg : Integrable (fun z => u z^2*z) :=
    ((hu.continuous.pow 2).mul continuous_id).integrable_of_hasCompactSupport hc2.mul_right
  have h := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable hA hB hfg
    (fun z _ => ((hu.pow 2).differentiable (by norm_num) z))
    (fun z _ => differentiableAt_id)
  simp only [fderiv_apply_one_eq_deriv,deriv_id'',mul_one,hd] at h
  have he : (∫ z : ℝ, 2*u z*deriv u z*z) = ∫ z : ℝ, 2*z*u z*deriv u z := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun z => by ring
  rw [he] at h
  linarith

theorem vertical_factorized_energy (freq : ℝ) (u : ℝ → ℝ)
    (hu : ContDiff ℝ 1 u) (hc : HasCompactSupport u) :
    (1/2:ℝ)*(∫ z : ℝ, (deriv u z+freq*z*u z)^2) =
      verticalForm freq u - (freq/2)*(∫ z : ℝ, u z^2) := by
  have hiD := vertical_deriv_square_integrable u hu hc
  have hiP := vertical_product_integrable (fun z => z^2) u
    (continuous_id.pow 2) hu.continuous hc
  have hiC := vertical_cross_integrable u hu hc
  have he : (fun z => (deriv u z+freq*z*u z)^2) =
      (fun z => (deriv u z)^2+freq^2*(z^2*u z^2)+freq*(2*z*u z*deriv u z)) := by
    funext z
    ring
  rw [he,integral_add (f := fun z => (deriv u z)^2+freq^2*(z^2*u z^2))
    (g := fun z => freq*(2*z*u z*deriv u z)) (hiD.add (hiP.const_mul _)) (hiC.const_mul _),
    integral_add (f := fun z => (deriv u z)^2) (g := fun z => freq^2*(z^2*u z^2))
      hiD (hiP.const_mul _),integral_const_mul,integral_const_mul,
    vertical_cross_identity u hu hc]
  unfold verticalForm
  ring

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_VerticalOscillatorGap
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Discharge of the published transverse-oscillator input. The normalized
Gaussian Poincare inequality and an exact compact-support integration by parts
give precisely the projection inequality used by the continuum reduction. -/

noncomputable section
open MeasureTheory
open scoped ContDiff
namespace ContinuumCoulomb

theorem vertical_quotient_deriv {freq : ℝ} (hf : 0 < freq)
    (u : ℝ → ℝ) (hu : ContDiff ℝ 1 u) (z : ℝ) :
    deriv (fun x => u x/verticalMode freq x) z =
      (deriv u z+freq*z*u z)/verticalMode freq z := by
  have hn := (verticalMode_positive hf z).ne'
  rw [((hu.differentiable (by norm_num) z).hasDerivAt.fun_div
    (verticalMode_hasDerivAt freq z) hn).deriv]
  field_simp [hn]
  ring

/-- The exact harmonic-oscillator projection inequality. -/
theorem publishedVerticalOscillatorGap : PublishedVerticalOscillatorGap := by
  intro freq hf u hu hc
  let v : ℝ → ℝ := fun z => u z/verticalMode freq z
  have hv : ContDiff ℝ 1 v := hu.div ((verticalMode_smooth freq).of_le (by first | simp | exact_mod_cast le_top))
    (fun z => (verticalMode_positive hf z).ne')
  have hvc : HasCompactSupport v := by
    change HasCompactSupport (fun z => u z*(verticalMode freq z)⁻¹)
    exact hc.mul_right
  have hm (z : ℝ) : verticalMode freq z^2*v z^2 = u z^2 := by
    dsimp [v]
    field_simp [(verticalMode_positive hf z).ne']
  have ha (z : ℝ) : verticalMode freq z^2*v z = u z*verticalMode freq z := by
    dsimp [v]
    field_simp [(verticalMode_positive hf z).ne']
  have hd (z : ℝ) : verticalMode freq z^2*(deriv v z)^2 =
      (deriv u z+freq*z*u z)^2 := by
    rw [show deriv v z = _ from vertical_quotient_deriv hf u hu z]
    field_simp [(verticalMode_positive hf z).ne']
  have h := gaussian_scalar_poincare hf v hv hvc
  simp_rw [hm,ha,hd] at h
  have he := vertical_factorized_energy freq u hu hc
  linarith

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Reduction_HardnessComposition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Promise-hardness transport through actual polynomial-time machine
composition, with both yes and no promise maps retained. -/

noncomputable section
namespace ContinuumCoulomb
open BinaryEncoding

theorem QMAHard.of_reduction {α β : Type}
    {ea : α → BitString} {eb : β → BitString}
    {P : PromiseProblem α} {Q : PromiseProblem β}
    (hP : QMAHard ea P) (F : PolynomialManyOne ea eb P Q) : QMAHard eb Q := by
  intro R hR
  rcases hP R hR with ⟨G⟩
  exact ⟨G.comp F⟩

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Reduction_TwoInputsHardness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Continuum Coulomb hardness under the flow and finite-spin hardness
hypotheses.
-/

noncomputable section
namespace ContinuumCoulomb

theorem unit_coulomb_qmaHard_of_two_inputs_oai
    (hcmp : PublishedCMPHardness) (hflow : PublishedC4FlowInput) :
    QMAHard unitCoulombCodec.encode unitCoulombPromise := by
  obtain ⟨s,_hs,hsource⟩ := hcmp
  obtain ⟨reduction⟩ := exists_source_unit_reduction_with_planar_gap hflow
    PlanarSobolev.manufacturedPlanarWell_gap_proved publishedVerticalOscillatorGap
    publishedSobolevSmoothDensity s
  exact hsource.of_reduction reduction

end ContinuumCoulomb

end

end OAI
end

theorem solution : type_of% @OAI.ContinuumCoulomb.unit_coulomb_qmaHard_of_two_inputs_oai := @OAI.ContinuumCoulomb.unit_coulomb_qmaHard_of_two_inputs_oai
