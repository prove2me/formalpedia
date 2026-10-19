-- Prove2me | solution 1 for MIPStarRE.LDT.Pasting.ldPasting
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T07:30:02.819433+00:00
-- url     : https://prove2.me/submissions/aee37e06-70b1-47c9-b92b-c23a7981a71b

/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE, with the
authors' permission. Vendored from https://github.com/LionSR/MIPStarRE
(commit 507e8122, 2026-08-25) by scripts/vendor-lidt.py; do not edit by hand.
Upstream path: MIPStarRE/LDT/Pasting/Bernoulli/Final.lean
-/
/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE, with the
authors' permission. Vendored from https://github.com/LionSR/MIPStarRE
(commit 507e8122, 2026-08-25) by scripts/vendor-lidt.py; do not edit by hand.
Upstream path: MIPStarRE/LDT/Pasting/Bernoulli/ScalarBounds.lean
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/LIDT/MIPStarRE/LDT/Pasting/Bernoulli/Final.lean (solution of MIPStarRE.LDT.Pasting.ldPasting);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Algebra.Algebra.Hom
import Mathlib.Algebra.Algebra.NonUnitalHom
import Mathlib.Algebra.Algebra.Spectrum.Basic
import Mathlib.Algebra.Algebra.Spectrum.Quasispectrum
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.GroupWithZero.Action
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.CharP.Defs
import Mathlib.Algebra.CharP.Invertible
import Mathlib.Algebra.CharZero.Defs
import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Field.IsField
import Mathlib.Algebra.Field.Rat
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.Group.Action.Pi
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Commute.Defs
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Finsupp
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Algebra.Group.Invertible.Basic
import Mathlib.Algebra.Group.Invertible.Defs
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Algebra.Group.Pi.Basic
import Mathlib.Algebra.Group.Subgroup.Defs
import Mathlib.Algebra.Group.Submonoid.Defs
import Mathlib.Algebra.Group.Subsemigroup.Defs
import Mathlib.Algebra.GroupWithZero.Action.Defs
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Algebra.GroupWithZero.Commute
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.GroupWithZero.Hom
import Mathlib.Algebra.GroupWithZero.Invertible
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.GroupWithZero.NeZero
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.GroupWithZero.Units.Lemmas
import Mathlib.Algebra.Module.BigOperators
import Mathlib.Algebra.Module.Defs
import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Algebra.Module.NatInt
import Mathlib.Algebra.Module.Pi
import Mathlib.Algebra.Module.Submodule.Defs
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Algebra.MonoidAlgebra.Defs
import Mathlib.Algebra.MonoidAlgebra.Module
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.MvPolynomial.Monad
import Mathlib.Algebra.MvPolynomial.Polynomial
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Algebra.NeZero
import Mathlib.Algebra.Notation.Defs
import Mathlib.Algebra.Notation.Indicator
import Mathlib.Algebra.Notation.Pi.Defs
import Mathlib.Algebra.Opposites
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Defs
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.Group.Unbundled.Basic
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Algebra.Order.GroupWithZero.Canonical
import Mathlib.Algebra.Order.GroupWithZero.Defs
import Mathlib.Algebra.Order.IsBotOne
import Mathlib.Algebra.Order.Module.Defs
import Mathlib.Algebra.Order.Monoid.Canonical.Defs
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Algebra.Order.Monoid.NatCast
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Algebra.Order.Monoid.Unbundled.Defs
import Mathlib.Algebra.Order.Monoid.Unbundled.ExistsOfLE
import Mathlib.Algebra.Order.Nonneg.Basic
import Mathlib.Algebra.Order.Nonneg.Module
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Basic
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Ring.Unbundled.Basic
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Order.Sub.Basic
import Mathlib.Algebra.Order.Sub.Defs
import Mathlib.Algebra.Order.SuccPred
import Mathlib.Algebra.Order.ZeroLEOne
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Defs
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.Polynomial.Eval.Coeff
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Commute
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Algebra.Ring.Hom.Defs
import Mathlib.Algebra.Ring.Int.Defs
import Mathlib.Algebra.Ring.Nat
import Mathlib.Algebra.Ring.Parity
import Mathlib.Algebra.Star.Basic
import Mathlib.Algebra.Star.Module
import Mathlib.Algebra.Star.SelfAdjoint
import Mathlib.Algebra.Star.StarProjection
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Instances
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.NonUnital
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unital
import Mathlib.Analysis.CStarAlgebra.Module.Constructions
import Mathlib.Analysis.CStarAlgebra.Module.Defs
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.Convex.Cone.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.LocallyConvex.WithSeminorms
import Mathlib.Analysis.Matrix.Hermitian
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.Analysis.Normed.Group.Defs
import Mathlib.Analysis.Normed.Group.Real
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.Normed.Lp.WithLp
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Complex.BigOperators
import Mathlib.Data.Countable.Defs
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.ENNReal.BigOperators
import Mathlib.Data.ENNReal.Inv
import Mathlib.Data.ENNReal.Operations
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finite.Defs
import Mathlib.Data.Finite.Prod
import Mathlib.Data.Finset.Attach
import Mathlib.Data.Finset.BooleanAlgebra
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Empty
import Mathlib.Data.Finset.Erase
import Mathlib.Data.Finset.Filter
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Lattice.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Lattice.Lemmas
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Range
import Mathlib.Data.Finsupp.Defs
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.CardEmbedding
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Fintype.OfMap
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sets
import Mathlib.Data.FunLike.Basic
import Mathlib.Data.FunLike.Embedding
import Mathlib.Data.FunLike.Equiv
import Mathlib.Data.Int.Cast.Basic
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.List.Nodup
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Basis
import Mathlib.Data.Matrix.Block
import Mathlib.Data.Matrix.Diagonal
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Multiset.Count
import Mathlib.Data.Multiset.Defs
import Mathlib.Data.Multiset.Filter
import Mathlib.Data.Multiset.MapFold
import Mathlib.Data.NNRat.Defs
import Mathlib.Data.NNReal.Defs
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Cast.Basic
import Mathlib.Data.Nat.Cast.Commute
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Cast.Order.Basic
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Data.Nat.Init
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Nat.SuccPred
import Mathlib.Data.Prod.Basic
import Mathlib.Data.Rat.Cast.CharZero
import Mathlib.Data.Rat.Cast.Defs
import Mathlib.Data.Rat.Cast.Lemmas
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Init
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Star
import Mathlib.Data.SProd
import Mathlib.Data.Set.CoeSort
import Mathlib.Data.Set.Defs
import Mathlib.Data.Set.Operations
import Mathlib.Data.SetLike.Basic
import Mathlib.Data.Subtype
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.Geometry.Convex.Cone.Pointed
import Mathlib.GroupTheory.GroupAction.Hom
import Mathlib.GroupTheory.GroupAction.Ring
import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Logic.Basic
import Mathlib.Logic.Embedding.Basic
import Mathlib.Logic.Equiv.Basic
import Mathlib.Logic.Equiv.Defs
import Mathlib.Logic.Equiv.Prod
import Mathlib.Logic.Function.Basic
import Mathlib.Logic.Function.Defs
import Mathlib.Logic.IsEmpty.Basic
import Mathlib.Logic.IsEmpty.Defs
import Mathlib.Logic.Nonempty
import Mathlib.Logic.Nontrivial.Defs
import Mathlib.Logic.Unique
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Instances
import Mathlib.MeasureTheory.Measure.Dirac
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.OuterMeasure.AE
import Mathlib.MeasureTheory.OuterMeasure.Defs
import Mathlib.Order.Basic
import Mathlib.Order.BoundedOrder.Basic
import Mathlib.Order.CompleteLattice.Defs
import Mathlib.Order.Defs.LinearOrder
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Order.Filter.Defs
import Mathlib.Order.Interval.Finset.Defs
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Order.Interval.Set.Defs
import Mathlib.Order.Lattice
import Mathlib.Order.Lattice.Nat
import Mathlib.Order.MinMax
import Mathlib.Order.Nat
import Mathlib.Order.Notation
import Mathlib.Order.RelClasses
import Mathlib.Order.SetNotation
import Mathlib.Probability.Distributions.Bernoulli
import Mathlib.Probability.Distributions.Binomial
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.Moments.Basic
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.LocalRing.Defs
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Basic
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.CancelDenoms.Core
import Mathlib.Tactic.FieldSimp.Lemmas
import Mathlib.Tactic.Linarith.Lemmas
import Mathlib.Tactic.Linarith.Preprocessing
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.NormNum.Result
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.Positivity.Core
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Ring.Common
import Mathlib.Tactic.Ring.RingNF
import Mathlib.Topology.Algebra.Field
import Mathlib.Topology.Algebra.Group.Defs
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Defs
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Topology.Algebra.InfiniteSum.SummationFilter
import Mathlib.Topology.Algebra.Module.ClosedSubmodule
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
import Mathlib.Topology.Algebra.Module.LocallyConvex
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.Algebra.Monoid.Defs
import Mathlib.Topology.Algebra.Ring.Basic
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.Algebra.Star
import Mathlib.Topology.Algebra.Star.Real
import Mathlib.Topology.Bases
import Mathlib.Topology.Basic
import Mathlib.Topology.Constructions
import Mathlib.Topology.Continuous
import Mathlib.Topology.ContinuousMap.ContinuousSqrt
import Mathlib.Topology.ContinuousOn
import Mathlib.Topology.Defs.Basic
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.EMetricSpace.Defs
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.MetricSpace.Defs
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.Metrizable.Basic
import Mathlib.Topology.Metrizable.Uniformity
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Order.Real
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.UniformSpace.Defs
import Mathlib.Topology.UniformSpace.Real
import Mathlib.Topology.UnitInterval
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Basic_ParametersBase
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Basic_AxisParallelLine
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Basic_DiagonalLine
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Basic_LinePolynomials
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Basic_LowDegreePolynomial
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_Quantum_FiniteMatrix_Basic
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_Quantum_FiniteMatrix_Order
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_Quantum_FiniteMatrix_TracePairing
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_Quantum_FiniteMatrix_BlockDiagonal
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_Quantum_FiniteMatrix_NormalizedTrace
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Basic_Distribution
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Basic_QuantumState
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Basic_SubMeasurementCore
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Basic_OperatorExpectations
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Basic_SubMeasurementFamilies
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Basic_ParametersFiniteAnswers
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Basic_PMFAverages
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Basic_OpFamily
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Test_Defs
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Test_StrategyCore
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Test_StrategyRole_Core
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_MainInductionStep_Defs
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_Quantum_Measurement
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Defs
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Basic_MeasurementLift
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Preliminaries_Defs
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Preliminaries_ComparisonCore
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Preliminaries_DistanceBounds
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Preliminaries_ConsistencyBridges
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichPrep_InnerProduct
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichMain_Completeness
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Preliminaries_BipartiteSelfConsistency_Core
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Preliminaries_CauchySchwarz
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Preliminaries_CompletionTransfer
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Preliminaries_Triangles_Core
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Basic_LinePolynomialEmbedding
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Test_StrategyPolynomialFamilies
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Test_StrategyRole_Algebra
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Test_StrategyFailures
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_Defs_Core
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_GlobalVariance_Defs_Core
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_CommutativityPoints_Defs
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Commutativity_Defs_Core
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Commutativity_Defs_Stability
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Commutativity_Defs_Normalization
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Commutativity_Scaffold_Core
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Commutativity_Scaffold_Products
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_CommutativityPoints_Approximation
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Commutativity_EvaluatedSliceBounds_PhaseOneThree
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Commutativity_EvaluatedSliceCommutation_Averages
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Commutativity_Transport_EvaluationSpecialization
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Commutativity_Transport_Pullback
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Preliminaries_Polynomials
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Preliminaries_PolynomialAgreement
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Commutativity_Transport_FullSlice_Averages
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Commutativity_Transport_FullSlice_Machinery_Marginalization_Core
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Commutativity_Transport_FullSlice_Machinery_Marginalization_Y
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Commutativity_Transport_FullSlice_Machinery_Normalization
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Commutativity_Transport_FullSlice_Bridges_Closeness
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Commutativity_Transport_FullSlice_Bridges_QSDD
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Commutativity_Transport_FullSlice_ZeroBounds
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Commutativity_Main_Auxiliary_HEvalTransport
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Commutativity_Main_Auxiliary_ScalarMarginalization
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_CommutativityPoints_SharedHelpers_SharedLine
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_CommutativityPoints_BridgeTheorems_DropBridges
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Commutativity_GCommStability_Scalar_RawSecond
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Commutativity_ScalarApproximation_PaperChainPhaseFive
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Commutativity_GCommStability_Scalar_First
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Commutativity_ScalarApproximation_ProcessedG_PhaseTwo
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Commutativity_ScalarApproximation_ProcessedG_MainChain
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Pasting_Defs_Tuples
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Pasting_Defs_Interpolation
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Pasting_Defs_Families
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Pasting_Sandwich_Switcheroo
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Pasting_Sandwich_GHatSandwich
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Pasting_Sandwich_PastedFamilies
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Pasting_Statements
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Pasting_SwitcherooSetup_Centers
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Pasting_SwitcherooSetup_Terms
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Pasting_SwitcherooContraction_Split
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Pasting_SwitcherooContraction_ScalarTerms
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Pasting_SwitcherooCompletion
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Pasting_CommutingWithG_Complete
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Pasting_GHatFacts
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_CommuteGHalfSandwich_Setup_Definitions
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_CommuteGHalfSandwich_Setup_StepLemmas_Split
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_CommuteGHalfSandwich_MoveChain_Base
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_CommuteGHalfSandwich_MoveChain_Lifting
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_CommuteGHalfSandwich_MoveChain_Chain
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_CommuteGHalfSandwich_MoveChain_FlatChain
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_CommuteGHalfSandwich_MoveChain_BackChain
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Pasting_Bernoulli_TruncatedSums
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Pasting_Bernoulli_Weights
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Pasting_Bernoulli_Scalar
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Pasting_Bernoulli_FromHToG_Core_BernoulliTail
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Pasting_Bernoulli_FromHToG_Core_FactBundles
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Pasting_Bernoulli_FromHToG_MoveLemmas_Basic
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Pasting_Bernoulli_FromHToG_AdjacentStages_StageA0M1
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Pasting_Bernoulli_FromHToG_AdjacentStages_Chain_HalfSandwich
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Pasting_Bernoulli_FromHToG_AdjacentStages_Chain_FinalMove
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Pasting_Bernoulli_FromHToG_PaperBounds
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Pasting_Bernoulli_MatrixChernoff
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_LdSandwichLineOnePoint_EndpointEquivs
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Pasting_Core_LdGbcon
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_LdSandwichLineOnePoint_Endpoint
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_LdSandwichLineOnePoint_PrefixMoved
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_LdSandwichLineOnePoint_CSSetup
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_LineInterpolation_Core
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_LineInterpolation_BadLine
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_LineInterpolation_BadMass
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_HBConsistency
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_HAConsistency
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Pasting_Bernoulli_DegreeZero
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_OverAllOutcomes_ErrorAndMass
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_OverAllOutcomes_NonglobalDecomposition
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_OverAllOutcomes_Final
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Pasting_Bernoulli_Final
import Theorems.Thm_MIPStarRE_LDT_Pasting_bipartiteConsError_uniform_le_one
import Theorems.Thm_MIPStarRE_LDT_Pasting_degreeZeroPastedPointConsistency
import Theorems.Thm_MIPStarRE_LDT_Pasting_ldPastingNontrivial
import Theorems.Thm_MIPStarRE_LDT_Pasting_one_le_ldPastingError_of_one_le_nu
import Theorems.Thm_MIPStarRE_LDT_Pasting_one_le_ldPastingNu_of_large_degreeRatio
import Theorems.Thm_MIPStarRE_LDT_Pasting_one_le_ldPastingNu_of_large_gamma
import Theorems.Thm_MIPStarRE_LDT_Pasting_one_le_ldPastingNu_of_large_zeta
import Theorems.Thm_MIPStarRE_LDT_ev_mono
import Theorems.Thm_MIPStarRE_LDT_leftTensor_le_one

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPStarRE.LDT.Pasting
section
open MIPStarRE.LDT
open scoped MatrixOrder Matrix ComplexOrder
set_option backward.isDefEq.respectTransparency false
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
/-- The scalar `κ` in a complete family is nonnegative. -/
lemma kappa_nonneg_of_complete
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    {kappa : Error}
    (hcomplete : family.Complete strategy.state kappa) :
    0 ≤ kappa := by
  have hmass_le_one : subMeasMass strategy.state family.averagedSubMeas.liftLeft ≤ 1 := by
    unfold subMeasMass SubMeas.liftLeft
    have hle : leftTensor (ι₂ := ι) (IdxPolyFamily.averagedSubMeas family).total ≤
        (1 : MIPStarRE.Quantum.Op (ι × ι)) := by
      exact leftTensor_le_one (ι₂ := ι) (IdxPolyFamily.averagedSubMeas family).total_le_one
    simpa [ev_one_of_isNormalized strategy.state strategy.isNormalized] using
      ev_mono strategy.state _ _ hle
  have hlower := hcomplete.averageCompleteness.lowerBound
  linarith
end
end MIPStarRE.LDT.Pasting

namespace MIPStarRE.LDT.Pasting
section
open MIPStarRE.LDT
open scoped MatrixOrder Matrix ComplexOrder
set_option backward.isDefEq.respectTransparency false
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
/-- The coefficient multiplying `κ` in the pasting error is nonnegative. -/
lemma ldPasting_kappa_coefficient_nonneg (params : Parameters) :
    0 ≤ (1 : Error) + 1 / (100 * (params.m : Error)) := by
  have hm_one : (1 : Error) ≤ (params.m : Error) := by exact_mod_cast params.hm
  have hm_pos : (0 : Error) < (params.m : Error) := lt_of_lt_of_le zero_lt_one hm_one
  have hden_pos : (0 : Error) < 100 * (params.m : Error) := by positivity
  have hfrac_nonneg : 0 ≤ (1 : Error) / (100 * (params.m : Error)) :=
    div_nonneg zero_le_one hden_pos.le
  linarith
end
end MIPStarRE.LDT.Pasting

namespace MIPStarRE.LDT.Pasting
section
open MIPStarRE.LDT
open scoped MatrixOrder Matrix ComplexOrder
set_option backward.isDefEq.respectTransparency false
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
/-- If `k = 0`, the exponential term alone gives the trivial pasting bound. -/
lemma one_le_ldPastingError_of_k_eq_zero
    (params : Parameters)
    (k : ℕ)
    (eps delta gamma kappa zeta : Error)
    (hkappa_nonneg : 0 ≤ kappa)
    (hk_zero : k = 0) :
    1 ≤ MainInductionStep.ldPastingInInductionError params k
      eps delta gamma kappa zeta := by
  subst k
  have hkappa_term_nonneg :
      0 ≤ kappa * (1 + 1 / (100 * (params.m : Error))) :=
    mul_nonneg hkappa_nonneg (ldPasting_kappa_coefficient_nonneg params)
  have hkappa_term_nonneg' :
      0 ≤ kappa * (1 + ((params.m : Error))⁻¹ * 100⁻¹) := by
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hkappa_term_nonneg
  simp [MainInductionStep.ldPastingInInductionError,
    MainInductionStep.ldPastingInInductionNu]
  nlinarith
end
end MIPStarRE.LDT.Pasting

namespace MIPStarRE.LDT.Pasting
section
open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder Matrix ComplexOrder
set_option backward.isDefEq.respectTransparency false
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
/-- Trivial consistency conclusion when the target pasting error is at least `1`.

The consistency defect of two submeasurements against a normalized bipartite
state is always at most `1`; hence a scalar lower bound
`1 ≤ ldPastingInInductionError ...` is enough to produce the final conclusion
with a distinguished trivial measurement. -/
lemma ldPasting_of_one_le_error
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma kappa zeta : Error)
    (family : IdxPolyFamily params ι)
    (k : ℕ)
    (herror :
      1 ≤ MainInductionStep.ldPastingInInductionError params k
        eps delta gamma kappa zeta) :
    ∃ H : Measurement (Polynomial params.next) ι,
      LdPastingConclusion params strategy family H eps delta gamma kappa zeta k := by
  let H : Measurement (Polynomial params.next) ι :=
    Measurement.trivialDistinguishedOutcome (fallbackInterpolatedPolynomial params)
  refine ⟨H, ?_⟩
  refine { pointConsistency := ?_ }
  exact ⟨le_trans
    (bipartiteConsError_uniform_le_one strategy.state strategy.isNormalized
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
      (polynomialEvaluationFamily params.next H.toSubMeas))
    herror⟩
end
end MIPStarRE.LDT.Pasting

namespace MIPStarRE.LDT.Pasting
section
open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder Matrix ComplexOrder
set_option backward.isDefEq.respectTransparency false
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
/-- Trivial consistency conclusion from the complementary scalar branches.

If `k` is positive, it suffices to show that the `ν` term in the pasting error
is at least `1`; if `k = 0`, the exponential term already gives the trivial
bound. -/
lemma ldPasting_of_one_le_nu_or_zero_k
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma kappa zeta : Error)
    (family : IdxPolyFamily params ι)
    (hcomplete : family.Complete strategy.state kappa)
    (k : ℕ)
    (hnu :
      1 ≤ k →
        1 ≤ MainInductionStep.ldPastingInInductionNu params k eps delta gamma zeta) :
    ∃ H : Measurement (Polynomial params.next) ι,
      LdPastingConclusion params strategy family H eps delta gamma kappa zeta k := by
  exact ldPasting_of_one_le_error params strategy eps delta gamma kappa zeta family k (by
    have hkappa_nonneg := kappa_nonneg_of_complete params strategy family hcomplete
    by_cases hk_pos : 1 ≤ k
    · exact one_le_ldPastingError_of_one_le_nu params k eps delta gamma kappa zeta
        hkappa_nonneg (hnu hk_pos)
    · have hk_zero : k = 0 := by omega
      exact one_le_ldPastingError_of_k_eq_zero params k eps delta gamma kappa zeta
        hkappa_nonneg hk_zero)
end
end MIPStarRE.LDT.Pasting

namespace MIPStarRE.LDT.Pasting
section
open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder Matrix ComplexOrder
set_option backward.isDefEq.respectTransparency false
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
/-- Complementary branch for `thm:ld-pasting` when `gamma > 1`.

Paper origin: `references/ldt-paper/ld-pasting.tex:52-55`, where this is one
of the large-error cases in which the final consistency bound is trivial.
This is one of the proved complementary cases for `thm:ld-pasting`. -/
theorem ldPastingLargeGammaBranch
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma kappa zeta : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (family : IdxPolyFamily params ι)
    (hcomplete : family.Complete strategy.state kappa)
    (hcons : family.ConsistentWithPoints strategy zeta)
    (_hself : family.StronglySelfConsistent strategy.state zeta)
    (_hbound : IdxPolyFamily.SliceBoundednessInput strategy family zeta)
    (k : ℕ)
    (_hk : 400 * params.m * params.d ≤ k)
    (hgamma : 1 < gamma) :
    ∃ H : Measurement (Polynomial params.next) ι,
      LdPastingConclusion params strategy family H eps delta gamma kappa zeta k := by
  exact ldPasting_of_one_le_nu_or_zero_k params strategy eps delta gamma kappa zeta
    family hcomplete k (fun hk_pos =>
      one_le_ldPastingNu_of_large_gamma params strategy eps delta gamma zeta
        hgood family hcons k hk_pos hgamma)
end
end MIPStarRE.LDT.Pasting

namespace MIPStarRE.LDT.Pasting
section
open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder Matrix ComplexOrder
set_option backward.isDefEq.respectTransparency false
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
/-- Complementary branch for `thm:ld-pasting` when `zeta > 1`.

Paper origin: `references/ldt-paper/ld-pasting.tex:52-55`, where this is one
of the large-error cases in which the final consistency bound is trivial.
This is one of the proved complementary cases for `thm:ld-pasting`. -/
theorem ldPastingLargeZetaBranch
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma kappa zeta : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (family : IdxPolyFamily params ι)
    (hcomplete : family.Complete strategy.state kappa)
    (_hcons : family.ConsistentWithPoints strategy zeta)
    (_hself : family.StronglySelfConsistent strategy.state zeta)
    (_hbound : IdxPolyFamily.SliceBoundednessInput strategy family zeta)
    (k : ℕ)
    (_hk : 400 * params.m * params.d ≤ k)
    (hzeta : 1 < zeta) :
    ∃ H : Measurement (Polynomial params.next) ι,
      LdPastingConclusion params strategy family H eps delta gamma kappa zeta k := by
  exact ldPasting_of_one_le_nu_or_zero_k params strategy eps delta gamma kappa zeta
    family hcomplete k (fun hk_pos =>
      one_le_ldPastingNu_of_large_zeta params strategy eps delta gamma zeta
        hgood k hk_pos hzeta)
end
end MIPStarRE.LDT.Pasting

namespace MIPStarRE.LDT.Pasting
section
open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder Matrix ComplexOrder
set_option backward.isDefEq.respectTransparency false
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
/-- Complementary branch for `thm:ld-pasting` when `d > q`.

Paper origin: `references/ldt-paper/ld-pasting.tex:52-55`, where this is the
large-error case `(d/q) ≥ 1`.  This is one of the proved complementary cases
for `thm:ld-pasting`. -/
theorem ldPastingLargeDegreeRatioBranch
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma kappa zeta : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (family : IdxPolyFamily params ι)
    (hcomplete : family.Complete strategy.state kappa)
    (hcons : family.ConsistentWithPoints strategy zeta)
    (_hself : family.StronglySelfConsistent strategy.state zeta)
    (_hbound : IdxPolyFamily.SliceBoundednessInput strategy family zeta)
    (k : ℕ)
    (_hk : 400 * params.m * params.d ≤ k)
    (hdq : params.q < params.d) :
    ∃ H : Measurement (Polynomial params.next) ι,
      LdPastingConclusion params strategy family H eps delta gamma kappa zeta k := by
  exact ldPasting_of_one_le_nu_or_zero_k params strategy eps delta gamma kappa zeta
    family hcomplete k (fun hk_pos =>
      one_le_ldPastingNu_of_large_degreeRatio params strategy eps delta gamma zeta
        hgood family hcons k hk_pos hdq)
end
end MIPStarRE.LDT.Pasting

namespace MIPStarRE.LDT.Pasting
section
open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder Matrix ComplexOrder
set_option backward.isDefEq.respectTransparency false
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
/-- Complementary branch for `thm:ld-pasting` when `k = 0`.

This branch is a boundary case for the reduction to the nontrivial theorem,
whose proof assumes `1 ≤ k`.  The scalar calculation showing that the
exponential term gives the trivial bound is proved in `ScalarBounds.lean`. -/
theorem ldPastingZeroKBranch
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma kappa zeta : Error)
    (_hgood : strategy.IsGood eps delta gamma)
    (family : IdxPolyFamily params ι)
    (hcomplete : family.Complete strategy.state kappa)
    (_hcons : family.ConsistentWithPoints strategy zeta)
    (_hself : family.StronglySelfConsistent strategy.state zeta)
    (_hbound : IdxPolyFamily.SliceBoundednessInput strategy family zeta)
    (k : ℕ)
    (_hk : 400 * params.m * params.d ≤ k)
    (hk_zero : k = 0) :
    ∃ H : Measurement (Polynomial params.next) ι,
      LdPastingConclusion params strategy family H eps delta gamma kappa zeta k := by
  exact ldPasting_of_one_le_error params strategy eps delta gamma kappa zeta family k (by
    exact one_le_ldPastingError_of_k_eq_zero params k eps delta gamma kappa zeta
      (kappa_nonneg_of_complete params strategy family hcomplete) hk_zero)
end
end MIPStarRE.LDT.Pasting

namespace MIPStarRE.LDT.Pasting
section
open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder Matrix ComplexOrder
set_option backward.isDefEq.respectTransparency false
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
/-- Degree-zero complementary branch for the unrestricted source theorem.

Paper origin: `references/ldt-paper/ld-pasting.tex:12-55`.  The paper's
large-error reduction names the cases
`eps, delta, gamma, zeta, d/q ≥ 1`; it does not explicitly add `0 < d` as a
hypothesis of `thm:ld-pasting`.  Thus the Lean theorem should not add `0 < d`
as an assumption of that cited theorem.

Issue #1622 recorded the need for a direct proof of this degree-zero branch; see
`docs/paper-gaps/issue-1622-ld-pasting-degree-zero.tex`.  The existing
nontrivial argument cannot simply be reused: its `hBConsistency` aggregation
passes from distinct sampled heights to independent sampled heights and absorbs
the resulting `k^2/q` loss through the displayed `(d/q)^(1/32)` term.  When
`d = 0`, that term is zero, so the branch requires a separate argument rather
than an additional hypothesis on `ldPasting`. -/
theorem ldPastingDegreeZeroBranch
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma kappa zeta : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (family : IdxPolyFamily params ι)
    (hcomplete : family.Complete strategy.state kappa)
    (hcons : family.ConsistentWithPoints strategy zeta)
    (_hself : family.StronglySelfConsistent strategy.state zeta)
    (_hbound : IdxPolyFamily.SliceBoundednessInput strategy family zeta)
    (k : ℕ)
    (_hk : 400 * params.m * params.d ≤ k)
    (hd_zero : params.d = 0)
    (_hk_pos : 1 ≤ k) :
    ∃ H : Measurement (Polynomial params.next) ι,
      LdPastingConclusion params strategy family H eps delta gamma kappa zeta k := by
  obtain ⟨H, _hHdef, hH⟩ :=
    degreeZeroPastedPointConsistency params strategy eps delta gamma kappa zeta
      hgood family hcomplete hcons hd_zero k
  exact ⟨H, { pointConsistency := hH }⟩
end
end MIPStarRE.LDT.Pasting

namespace MIPStarRE.LDT.Pasting
section
open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder Matrix ComplexOrder
set_option backward.isDefEq.respectTransparency false
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
/-- Projection from the restricted nontrivial construction.

The restricted construction theorem `ldPastingNontrivial` proves the nontrivial
analytic regime for the canonical pasted measurement.  This auxiliary statement
records the projection from the restricted construction theorem to the conclusion
needed by the unrestricted theorem, without changing the statement of
`thm:ld-pasting`. -/
theorem ldPastingNontrivialPublicBranch
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma kappa zeta : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (hgamma_le : gamma ≤ 1)
    (hzeta_le : zeta ≤ 1)
    (hdq_le : params.d ≤ params.q)
    (hd : 0 < params.d)
    (family : IdxPolyFamily params ι)
    (hcomplete : family.Complete strategy.state kappa)
    (hcons : family.ConsistentWithPoints strategy zeta)
    (hself : family.StronglySelfConsistent strategy.state zeta)
    (hbound : IdxPolyFamily.SliceBoundednessInput strategy family zeta)
    (k : ℕ)
    (hk_pos : 1 ≤ k)
    (hk : 400 * params.m * params.d ≤ k) :
    ∃ H : Measurement (Polynomial params.next) ι,
      LdPastingConclusion params strategy family H eps delta gamma kappa zeta k := by
  obtain ⟨H, _hHdef, hH⟩ :=
    ldPastingNontrivial params strategy eps delta gamma kappa zeta
      hgood hgamma_le hzeta_le hdq_le hd
      family hcomplete hcons hself hbound k hk_pos hk
  exact ⟨H, hH⟩
end
end MIPStarRE.LDT.Pasting

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPStarRE.LDT.Pasting
open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder Matrix ComplexOrder
set_option backward.isDefEq.respectTransparency false
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
theorem _root_.solution
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma kappa zeta : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (family : IdxPolyFamily params ι)
    (hcomplete : family.Complete strategy.state kappa)
    (hcons : family.ConsistentWithPoints strategy zeta)
    (hself : family.StronglySelfConsistent strategy.state zeta)
    (hbound : IdxPolyFamily.SliceBoundednessInput strategy family zeta)
    (k : ℕ)
    (hk : 400 * params.m * params.d ≤ k) :
    ∃ H : Measurement (Polynomial params.next) ι,
      LdPastingConclusion params strategy family H eps delta gamma kappa zeta k := by
  by_cases hgamma_le : gamma ≤ 1
  · by_cases hzeta_le : zeta ≤ 1
    · by_cases hdq_le : params.d ≤ params.q
      · by_cases hd : 0 < params.d
        · by_cases hk_pos : 1 ≤ k
          · exact ldPastingNontrivialPublicBranch params strategy eps delta gamma kappa zeta
              hgood hgamma_le hzeta_le hdq_le hd family hcomplete hcons hself hbound
              k hk_pos hk
          · have hk_zero : k = 0 := by omega
            exact ldPastingZeroKBranch params strategy eps delta gamma kappa zeta
              hgood family hcomplete hcons hself hbound k hk hk_zero
        · have hd_zero : params.d = 0 := Nat.eq_zero_of_not_pos hd
          by_cases hk_pos : 1 ≤ k
          · exact ldPastingDegreeZeroBranch params strategy eps delta gamma kappa zeta
              hgood family hcomplete hcons hself hbound k hk hd_zero hk_pos
          · have hk_zero : k = 0 := by omega
            exact ldPastingZeroKBranch params strategy eps delta gamma kappa zeta
              hgood family hcomplete hcons hself hbound k hk hk_zero
      · have hdq : params.q < params.d := by omega
        exact ldPastingLargeDegreeRatioBranch params strategy eps delta gamma kappa zeta
          hgood family hcomplete hcons hself hbound k hk hdq
    · have hzeta : 1 < zeta := lt_of_not_ge hzeta_le
      exact ldPastingLargeZetaBranch params strategy eps delta gamma kappa zeta
        hgood family hcomplete hcons hself hbound k hk hzeta
  · have hgamma : 1 < gamma := lt_of_not_ge hgamma_le
    exact ldPastingLargeGammaBranch params strategy eps delta gamma kappa zeta
      hgood family hcomplete hcons hself hbound k hk hgamma
end MIPStarRE.LDT.Pasting
