-- Prove2me | solution 1 for MIPStarRE.LDT.Pasting.fromHToG_SUS_context_avg_le_one
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T06:36:58.463599+00:00
-- url     : https://prove2.me/submissions/50e65622-1e89-4fad-b75a-691bdf48f531

/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE, with the
authors' permission. Vendored from https://github.com/LionSR/MIPStarRE
(commit 507e8122, 2026-08-25) by scripts/vendor-lidt.py; do not edit by hand.
Upstream path: MIPStarRE/LDT/Pasting/Bernoulli/FromHToG/PaperBounds/SandwichContext.lean
-/
/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE, with the
authors' permission. Vendored from https://github.com/LionSR/MIPStarRE
(commit 507e8122, 2026-08-25) by scripts/vendor-lidt.py; do not edit by hand.
Upstream path: MIPStarRE/LDT/Pasting/Bernoulli/TruncatedSums.lean
-/
/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE, with the
authors' permission. Vendored from https://github.com/LionSR/MIPStarRE
(commit 507e8122, 2026-08-25) by scripts/vendor-lidt.py; do not edit by hand.
Upstream path: MIPStarRE/LDT/Pasting/Bernoulli/Weights.lean
-/
/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE, with the
authors' permission. Vendored from https://github.com/LionSR/MIPStarRE
(commit 507e8122, 2026-08-25) by scripts/vendor-lidt.py; do not edit by hand.
Upstream path: MIPStarRE/LDT/Pasting/Bernoulli/FromHToG/Core/AveragesAndOps.lean
-/
/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE, with the
authors' permission. Vendored from https://github.com/LionSR/MIPStarRE
(commit 507e8122, 2026-08-25) by scripts/vendor-lidt.py; do not edit by hand.
Upstream path: MIPStarRE/LDT/Pasting/Bernoulli/FromHToG/MoveLemmas/Basic.lean
-/
/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE, with the
authors' permission. Vendored from https://github.com/LionSR/MIPStarRE
(commit 507e8122, 2026-08-25) by scripts/vendor-lidt.py; do not edit by hand.
Upstream path: MIPStarRE/LDT/Pasting/Bernoulli/FromHToG/MoveLemmas/TailStage.lean
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/LIDT/MIPStarRE/LDT/Pasting/Bernoulli/FromHToG/PaperBounds/SandwichContext.lean (solution of MIPStarRE.LDT.Pasting.fromHToG_SUS_context_avg_le_one);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Algebra.Algebra.Hom
import Mathlib.Algebra.Algebra.NonUnitalHom
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
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.QuadraticDiscriminant
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
import Mathlib.Topology.Algebra.Star.Real
import Mathlib.Topology.Bases
import Mathlib.Topology.Basic
import Mathlib.Topology.Constructions
import Mathlib.Topology.Continuous
import Mathlib.Topology.Defs.Basic
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
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Pasting_Bernoulli_TruncatedSums
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Pasting_Bernoulli_Weights
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Pasting_Bernoulli_Scalar
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Pasting_Bernoulli_FromHToG_Core_BernoulliTail
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Pasting_Bernoulli_FromHToG_Core_FactBundles
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Pasting_Bernoulli_FromHToG_MoveLemmas_Basic
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Pasting_Bernoulli_FromHToG_AdjacentStages_StageA0M1
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Pasting_Bernoulli_FromHToG_AdjacentStages_Chain_HalfSandwich
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Pasting_Bernoulli_FromHToG_AdjacentStages_Chain_FinalMove
import Theorems.Thm_MIPStarRE_LDT_Pasting_fromHToG_avgOver_head_ev_sandwich
import Theorems.Thm_MIPStarRE_LDT_Pasting_fromHToG_avgOver_tail_type_ev
import Theorems.Thm_MIPStarRE_LDT_Pasting_fromHToG_bool_type_filtered_outcome_sum
import Theorems.Thm_MIPStarRE_LDT_Pasting_fromHToG_ev_sum_isSome_sandwich_weight
import Theorems.Thm_MIPStarRE_LDT_Pasting_fromHToG_sum2_avgOver2
import Theorems.Thm_MIPStarRE_LDT_Pasting_fromHToG_sum_averagedSandwichByType_total_eq_one
import Theorems.Thm_MIPStarRE_LDT_Pasting_gHatIdxMeas_proj
import Theorems.Thm_MIPStarRE_LDT_Pasting_psd_contraction_comm_sandwich_le
import Theorems.Thm_MIPStarRE_LDT_SubMeas_total_nonneg
import Theorems.Thm_MIPStarRE_LDT_avgOver_congr
import Theorems.Thm_MIPStarRE_LDT_avgOver_uniform_prod
import Theorems.Thm_MIPStarRE_LDT_ev_add
import Theorems.Thm_MIPStarRE_LDT_ev_mono
import Theorems.Thm_MIPStarRE_LDT_ev_sum
import Theorems.Thm_MIPStarRE_LDT_leftTensor_finset_sum
import Theorems.Thm_MIPStarRE_LDT_leftTensor_mul_rightTensor_eq_opTensor
import Theorems.Thm_MIPStarRE_LDT_opTensor_mono_right
import Theorems.Thm_MIPStarRE_LDT_opTensor_mul
import Theorems.Thm_MIPStarRE_LDT_rightTensor_finset_sum
import Theorems.Thm_MIPStarRE_LDT_rightTensor_one

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPStarRE.LDT.Pasting
section
open MIPStarRE.LDT
open scoped BigOperators MatrixOrder Matrix ComplexOrder
set_option backward.isDefEq.respectTransparency false
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
/-- Each Boolean-type monomial commutes with the base operator `G`. -/
lemma gHatTypeOperator_commute_base
    (G : MIPStarRE.Quantum.Op ι) {k : ℕ} (τ : GHatType k) :
    Commute (gHatTypeOperator G τ) G := by
  have hcomm : Commute G (1 - G) := (Commute.one_right G).sub_right (Commute.refl G)
  have hleft : Commute (G ^ gHatTypeWeight τ) G := (Commute.refl G).pow_left _
  have hright : Commute ((1 - G) ^ (k - gHatTypeWeight τ)) G := hcomm.symm.pow_left _
  unfold gHatTypeOperator
  exact hleft.mul_left hright
end
end MIPStarRE.LDT.Pasting

namespace MIPStarRE.LDT.Pasting
section
open MIPStarRE.LDT
open scoped BigOperators MatrixOrder Matrix ComplexOrder
set_option backward.isDefEq.respectTransparency false
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
/-- Each Boolean-type monomial commutes with the complementary base operator `1 - G`. -/
lemma gHatTypeOperator_commute_one_sub_base
    (G : MIPStarRE.Quantum.Op ι) {k : ℕ} (τ : GHatType k) :
    Commute (gHatTypeOperator G τ) (1 - G) := by
  have hcomm : Commute G (1 - G) := (Commute.one_right G).sub_right (Commute.refl G)
  have hleft : Commute (G ^ gHatTypeWeight τ) (1 - G) := hcomm.pow_left _
  have hright : Commute ((1 - G) ^ (k - gHatTypeWeight τ)) (1 - G) :=
    (Commute.refl (1 - G)).pow_left _
  unfold gHatTypeOperator
  exact hleft.mul_left hright
end
end MIPStarRE.LDT.Pasting

namespace MIPStarRE.LDT.Pasting
section
open MIPStarRE.LDT
open scoped BigOperators MatrixOrder Matrix ComplexOrder
set_option backward.isDefEq.respectTransparency false
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
/-- The truncated type sum commutes with the base operator `G`. -/
lemma truncatedTypeSums_commute_base
    (G : MIPStarRE.Quantum.Op ι) (d prefixLen : ℕ)
    {tailLen : ℕ} (τtail : GHatType tailLen) :
    Commute (truncatedTypeSums G d prefixLen τtail) G := by
  unfold truncatedTypeSums
  refine Commute.sum_left Finset.univ _ G ?_
  intro τprefix _
  by_cases h : d + 1 ≤ gHatTypeWeight τprefix + gHatTypeWeight τtail
  · simpa [h] using gHatTypeOperator_commute_base G τprefix
  · simp [h]
end
end MIPStarRE.LDT.Pasting

namespace MIPStarRE.LDT.Pasting
section
open MIPStarRE.LDT
open scoped BigOperators MatrixOrder Matrix ComplexOrder
set_option backward.isDefEq.respectTransparency false
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
/-- The truncated type sum commutes with the complementary base operator `1 - G`. -/
lemma truncatedTypeSums_commute_one_sub_base
    (G : MIPStarRE.Quantum.Op ι) (d prefixLen : ℕ)
    {tailLen : ℕ} (τtail : GHatType tailLen) :
    Commute (truncatedTypeSums G d prefixLen τtail) (1 - G) := by
  unfold truncatedTypeSums
  refine Commute.sum_left Finset.univ _ (1 - G) ?_
  intro τprefix _
  by_cases h : d + 1 ≤ gHatTypeWeight τprefix + gHatTypeWeight τtail
  · simpa [h] using gHatTypeOperator_commute_one_sub_base G τprefix
  · simp [h]
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
/-- `fromHToGRecurrenceWeight` is Hermitian (source-style API). -/
theorem fromHToGRecurrenceWeight_isHermitian
    (params : Parameters)
    [FieldModel params.q]
    (family : IdxPolyFamily params ι)
    (prefixLen : ℕ)
    {tailLen : ℕ} (τtail : GHatType tailLen) :
    (fromHToGRecurrenceWeight params family prefixLen τtail)ᴴ =
      fromHToGRecurrenceWeight params family prefixLen τtail :=
  (fromHToGRecurrenceWeight_recurrence params family prefixLen τtail).1
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
/-- `fromHToGRecurrenceWeight` is positive semidefinite (source-style API). -/
theorem fromHToGRecurrenceWeight_nonneg
    (params : Parameters)
    [FieldModel params.q]
    (family : IdxPolyFamily params ι)
    (prefixLen : ℕ)
    {tailLen : ℕ} (τtail : GHatType tailLen) :
    0 ≤ fromHToGRecurrenceWeight params family prefixLen τtail :=
  (fromHToGRecurrenceWeight_recurrence params family prefixLen τtail).2.1
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
/-- `fromHToGRecurrenceWeight` is bounded above by the identity. -/
theorem fromHToGRecurrenceWeight_le_one
    (params : Parameters)
    [FieldModel params.q]
    (family : IdxPolyFamily params ι)
    (prefixLen : ℕ)
    {tailLen : ℕ} (τtail : GHatType tailLen) :
    fromHToGRecurrenceWeight params family prefixLen τtail ≤ 1 :=
  (fromHToGRecurrenceWeight_recurrence params family prefixLen τtail).2.2.1
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
/-- `fromHToGRecurrenceWeight` commutes with the averaged complete operator `G`. -/
lemma fromHToGRecurrenceWeight_commute_base
    (params : Parameters)
    [FieldModel params.q]
    (family : IdxPolyFamily params ι)
    (prefixLen : ℕ)
    {tailLen : ℕ} (τtail : GHatType tailLen) :
    Commute (fromHToGRecurrenceWeight params family prefixLen τtail)
      family.averagedSubMeas.total := by
  exact truncatedTypeSums_commute_base family.averagedSubMeas.total params.d prefixLen τtail
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
/-- `fromHToGRecurrenceWeight` commutes with `I - G`. -/
lemma fromHToGRecurrenceWeight_commute_one_sub_base
    (params : Parameters)
    [FieldModel params.q]
    (family : IdxPolyFamily params ι)
    (prefixLen : ℕ)
    {tailLen : ℕ} (τtail : GHatType tailLen) :
    Commute (fromHToGRecurrenceWeight params family prefixLen τtail)
      (1 - family.averagedSubMeas.total) := by
  exact truncatedTypeSums_commute_one_sub_base
    family.averagedSubMeas.total params.d prefixLen τtail
end
end MIPStarRE.LDT.Pasting

namespace MIPStarRE.LDT.Pasting
section
open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open scoped BigOperators MatrixOrder Matrix ComplexOrder
set_option backward.isDefEq.respectTransparency false
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
/-- Right tensor placement distributes over addition. -/
lemma fromHToG_rightTensor_add (A B : MIPStarRE.Quantum.Op ι) :
    rightTensor (ι₁ := ι) (A + B) =
      rightTensor (ι₁ := ι) A + rightTensor (ι₁ := ι) B := by
  simpa [Fintype.sum_bool] using
    (rightTensor_finset_sum (ι₁ := ι) (Finset.univ : Finset Bool)
      (fun b : Bool => if b then A else B)).symm
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
/-- If `A` is PSD and `B ≤ C`, then the corresponding bipartite scalar
expectations with left/right tensor placement are monotone in the right factor. -/
lemma fromHToG_ev_leftTensor_rightTensor_mono_right_of_nonneg_left
    (ψbi : QuantumState (ι × ι))
    {A B C : MIPStarRE.Quantum.Op ι}
    (hA : 0 ≤ A) (hBC : B ≤ C) :
    ev ψbi (leftTensor (ι₂ := ι) A * rightTensor (ι₁ := ι) B) ≤
      ev ψbi (leftTensor (ι₂ := ι) A * rightTensor (ι₁ := ι) C) := by
  apply ev_mono ψbi _ _
  rw [leftTensor_mul_rightTensor_eq_opTensor, leftTensor_mul_rightTensor_eq_opTensor]
  exact MIPStarRE.LDT.opTensor_mono_right hA hBC
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
/-- Paper `eq:S-sandwich` for the complete branch average `G`. -/
lemma fromHToGRecurrenceWeight_sandwich_base_le
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι)
    (prefixLen : ℕ) {tailLen : ℕ} (τtail : GHatType tailLen) :
    let S := fromHToGRecurrenceWeight params family prefixLen τtail
    S * family.averagedSubMeas.total * S ≤ family.averagedSubMeas.total := by
  dsimp
  exact psd_contraction_comm_sandwich_le
    (fromHToGRecurrenceWeight_nonneg params family prefixLen τtail)
    (fromHToGRecurrenceWeight_le_one params family prefixLen τtail)
    family.averagedSubMeas.total_nonneg
    (fromHToGRecurrenceWeight_commute_base params family prefixLen τtail)
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
/-- Paper `eq:S-sandwich` for the incomplete branch average `I - G`. -/
lemma fromHToGRecurrenceWeight_sandwich_one_sub_base_le
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι)
    (prefixLen : ℕ) {tailLen : ℕ} (τtail : GHatType tailLen) :
    let S := fromHToGRecurrenceWeight params family prefixLen τtail
    S * (1 - family.averagedSubMeas.total) * S ≤ 1 - family.averagedSubMeas.total := by
  dsimp
  exact psd_contraction_comm_sandwich_le
    (fromHToGRecurrenceWeight_nonneg params family prefixLen τtail)
    (fromHToGRecurrenceWeight_le_one params family prefixLen τtail)
    (sub_nonneg.mpr family.averagedSubMeas.total_le_one)
    (fromHToGRecurrenceWeight_commute_one_sub_base params family prefixLen τtail)
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
/-- Completed `ĝ` measurement outcomes are Hermitian.  This records the
positivity-to-Hermitian conversion used when orienting the adjoint
half-sandwich commutator in the `M₂ → M₃` move. -/
lemma fromHToG_gHatIdxMeas_outcome_isHermitian
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (x : Fq params) (g : GHatOutcome params) :
    ((gHatIdxMeas params family x).outcome g)ᴴ =
      (gHatIdxMeas params family x).outcome g := by
  exact (Matrix.nonneg_iff_posSemidef.mp
    ((gHatIdxMeas params family x).outcome_pos g)).isHermitian.eq
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
/-- Rewrite a nested finite sum as a sum over a product index. -/
lemma fromHToG_sum_product {α β : Type*} [Fintype α] [Fintype β]
    (F : α → β → Error) :
    (∑ a : α, ∑ b : β, F a b) = ∑ p : α × β, F p.1 p.2 := by
  rw [← Finset.univ_product_univ, Finset.sum_product]
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
/-- Fold a tail point/outcome average written directly with the sandwich-family
outcomes into `averagedSandwichByTypeSubMeas`. -/
lemma fromHToG_avgOver_tail_type_ev_sandwich
    (params : Parameters) [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι) (n : ℕ) (τ : GHatType n)
    (B : MIPStarRE.Quantum.Op ι) :
    avgOver (uniformDistribution (PointTuple params n)) (fun xs =>
      ∑ gs ∈ (Finset.univ : Finset (GHatTupleOutcome params n)) with
          gHatTupleType gs = τ,
        ev ψbi (leftTensor (ι₂ := ι)
          ((gHatSandwichFamily params family n xs).outcome gs) *
            rightTensor (ι₁ := ι) B)) =
      ev ψbi (leftTensor (ι₂ := ι)
        (averagedSandwichByTypeSubMeas params family n τ).total *
          rightTensor (ι₁ := ι) B) := by
  simpa [gHatSandwichFamily] using
    (fromHToG_avgOver_tail_type_ev params ψbi family n τ B)
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
/-- Fold the complete/incomplete head branch average with an `S · B · S`
sandwich into the stored exact branch averages. -/
lemma fromHToG_avgOver_head_branch_ev_sandwich
    (params : Parameters) [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι)
    (hcomplete : averageOperatorOverDistribution (uniformDistribution (Fq params))
      (fun x => (completePartSubMeas params family x).total) =
        family.averagedSubMeas.total)
    (hincomplete : averageOperatorOverDistribution (uniformDistribution (Fq params))
      (fun x => (incompletePartSubMeas params family x).total) =
        1 - family.averagedSubMeas.total)
    (b : Bool) (A S : MIPStarRE.Quantum.Op ι) :
    avgOver (uniformDistribution (Fq params)) (fun x =>
      let B := if b then (completePartSubMeas params family x).total
        else (incompletePartSubMeas params family x).total
      ev ψbi (leftTensor (ι₂ := ι) A * rightTensor (ι₁ := ι) (S * B * S))) =
      ev ψbi (leftTensor (ι₂ := ι) A *
        rightTensor (ι₁ := ι)
          (S * (if b then family.averagedSubMeas.total
            else 1 - family.averagedSubMeas.total) * S)) := by
  cases b
  · rw [fromHToG_avgOver_head_ev_sandwich]
    simp only [Bool.false_eq_true, if_false]
    rw [hincomplete]
  · rw [fromHToG_avgOver_head_ev_sandwich]
    simp only [if_true]
    rw [hcomplete]
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
omit [Fintype ι] [DecidableEq ι] in
theorem _root_.solution
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (params : Parameters) [FieldModel params.q]
    (ψbi : QuantumState (ι × ι)) (hnorm : ψbi.IsNormalized)
    (family : IdxPolyFamily params ι)
    (hcomplete : averageOperatorOverDistribution (uniformDistribution (Fq params))
      (fun x => (completePartSubMeas params family x).total) =
        family.averagedSubMeas.total)
    (hincomplete : averageOperatorOverDistribution (uniformDistribution (Fq params))
      (fun x => (incompletePartSubMeas params family x).total) =
        1 - family.averagedSubMeas.total)
    (ℓ n : ℕ) :
    avgOver (uniformDistribution (Fq params × PointTuple params n)) (fun q =>
      ∑ ogs : GHatOutcome params × GHatTupleOutcome params n,
        let S := fromHToGRecurrenceWeight params family ℓ
          (prependTypeBit ogs.1.isSome (gHatTupleType ogs.2))
        let U := (gHatIdxMeas params family q.1).outcome ogs.1
        let T := gHatHalfProductOutcomeOperator params family n q.2 ogs.2
        ev ψbi
          ((leftTensor (ι₂ := ι) T * rightTensor (ι₁ := ι) (S * U)) *
            (leftTensor (ι₂ := ι) T * rightTensor (ι₁ := ι) (S * U))ᴴ)) ≤ 1 := by
  classical
  let F : Bool → GHatType n → Fq params → PointTuple params n → Error := fun b τ x xs =>
    ∑ g ∈ (Finset.univ : Finset (GHatOutcome params)) with g.isSome = b,
      ∑ gs ∈ (Finset.univ : Finset (GHatTupleOutcome params n)) with
          gHatTupleType gs = τ,
        let S := fromHToGRecurrenceWeight params family ℓ (prependTypeBit b τ)
        let U := (gHatIdxMeas params family x).outcome g
        let T := gHatHalfProductOutcomeOperator params family n xs gs
        ev ψbi ((leftTensor (ι₂ := ι) T * rightTensor (ι₁ := ι) (S * U)) *
          (leftTensor (ι₂ := ι) T * rightTensor (ι₁ := ι) (S * U))ᴴ)
  have hsplit :
      avgOver (uniformDistribution (Fq params × PointTuple params n)) (fun q =>
        ∑ ogs : GHatOutcome params × GHatTupleOutcome params n,
          let S := fromHToGRecurrenceWeight params family ℓ
            (prependTypeBit ogs.1.isSome (gHatTupleType ogs.2))
          let U := (gHatIdxMeas params family q.1).outcome ogs.1
          let T := gHatHalfProductOutcomeOperator params family n q.2 ogs.2
          ev ψbi ((leftTensor (ι₂ := ι) T * rightTensor (ι₁ := ι) (S * U)) *
            (leftTensor (ι₂ := ι) T * rightTensor (ι₁ := ι) (S * U))ᴴ)) =
      ∑ b : Bool, ∑ τ : GHatType n,
        avgOver (uniformDistribution (Fq params)) (fun x =>
          avgOver (uniformDistribution (PointTuple params n)) (fun xs => F b τ x xs)) := by
    calc
      avgOver (uniformDistribution (Fq params × PointTuple params n)) (fun q =>
        ∑ ogs : GHatOutcome params × GHatTupleOutcome params n,
          let S := fromHToGRecurrenceWeight params family ℓ
            (prependTypeBit ogs.1.isSome (gHatTupleType ogs.2))
          let U := (gHatIdxMeas params family q.1).outcome ogs.1
          let T := gHatHalfProductOutcomeOperator params family n q.2 ogs.2
          ev ψbi ((leftTensor (ι₂ := ι) T * rightTensor (ι₁ := ι) (S * U)) *
            (leftTensor (ι₂ := ι) T * rightTensor (ι₁ := ι) (S * U))ᴴ))
        = avgOver (uniformDistribution (Fq params)) (fun x =>
        avgOver (uniformDistribution (PointTuple params n)) (fun xs =>
          ∑ ogs : GHatOutcome params × GHatTupleOutcome params n,
            let S := fromHToGRecurrenceWeight params family ℓ
              (prependTypeBit ogs.1.isSome (gHatTupleType ogs.2))
            let U := (gHatIdxMeas params family x).outcome ogs.1
            let T := gHatHalfProductOutcomeOperator params family n xs ogs.2
            ev ψbi ((leftTensor (ι₂ := ι) T * rightTensor (ι₁ := ι) (S * U)) *
              (leftTensor (ι₂ := ι) T * rightTensor (ι₁ := ι) (S * U))ᴴ))) := by
            simpa using (avgOver_uniform_prod (α := Fq params) (β := PointTuple params n)
              (f := fun x xs =>
                ∑ ogs : GHatOutcome params × GHatTupleOutcome params n,
                  let S := fromHToGRecurrenceWeight params family ℓ
                    (prependTypeBit ogs.1.isSome (gHatTupleType ogs.2))
                  let U := (gHatIdxMeas params family x).outcome ogs.1
                  let T := gHatHalfProductOutcomeOperator params family n xs ogs.2
                  ev ψbi ((leftTensor (ι₂ := ι) T * rightTensor (ι₁ := ι) (S * U)) *
                    (leftTensor (ι₂ := ι) T * rightTensor (ι₁ := ι) (S * U))ᴴ)))
      _ = avgOver (uniformDistribution (Fq params)) (fun x =>
            avgOver (uniformDistribution (PointTuple params n)) (fun xs =>
              ∑ b : Bool, ∑ τ : GHatType n,
                F b τ x xs)) := by
              refine avgOver_congr _ _ _ ?_
              intro x
              refine avgOver_congr _ _ _ ?_
              intro xs
              rw [(fromHToG_sum_product (fun g gs =>
                let S := fromHToGRecurrenceWeight params family ℓ
                  (prependTypeBit g.isSome (gHatTupleType gs))
                let U := (gHatIdxMeas params family x).outcome g
                let T := gHatHalfProductOutcomeOperator params family n xs gs
                ev ψbi ((leftTensor (ι₂ := ι) T * rightTensor (ι₁ := ι) (S * U)) *
                  (leftTensor (ι₂ := ι) T * rightTensor (ι₁ := ι) (S * U))ᴴ))).symm]
              symm
              exact fromHToG_bool_type_filtered_outcome_sum params
                (fun b τ g gs =>
                  let S := fromHToGRecurrenceWeight params family ℓ (prependTypeBit b τ)
                  let U := (gHatIdxMeas params family x).outcome g
                  let T := gHatHalfProductOutcomeOperator params family n xs gs
                  ev ψbi ((leftTensor (ι₂ := ι) T * rightTensor (ι₁ := ι) (S * U)) *
                    (leftTensor (ι₂ := ι) T * rightTensor (ι₁ := ι) (S * U))ᴴ))
      _ = ∑ b : Bool, ∑ τ : GHatType n,
            avgOver (uniformDistribution (Fq params)) (fun x =>
              avgOver (uniformDistribution (PointTuple params n)) (fun xs => F b τ x xs)) := by
              symm
              exact fromHToG_sum2_avgOver2
                (uniformDistribution (Fq params))
                (uniformDistribution (PointTuple params n)) F
  let branchRhs : Bool → GHatType n → Error := fun b τ =>
    ev ψbi (leftTensor (ι₂ := ι) (averagedSandwichByTypeSubMeas params family n τ).total *
      rightTensor (ι₁ := ι)
        (if b then family.averagedSubMeas.total else 1 - family.averagedSubMeas.total))
  have hbranchSum : ∀ b : Bool,
      ∑ τ : GHatType n,
        avgOver (uniformDistribution (Fq params)) (fun x =>
          avgOver (uniformDistribution (PointTuple params n)) (fun xs => F b τ x xs)) ≤
      ∑ τ : GHatType n, branchRhs b τ := by
    intro b
    refine Finset.sum_le_sum ?_
    intro τ _hτ
    let S := fromHToGRecurrenceWeight params family ℓ (prependTypeBit b τ)
    let Aτ := (averagedSandwichByTypeSubMeas params family n τ).total
    change avgOver (uniformDistribution (Fq params)) (fun x =>
        avgOver (uniformDistribution (PointTuple params n)) (fun xs => F b τ x xs)) ≤
      branchRhs b τ
    have hrew :
        avgOver (uniformDistribution (Fq params)) (fun x =>
          avgOver (uniformDistribution (PointTuple params n)) (fun xs => F b τ x xs)) =
        avgOver (uniformDistribution (Fq params)) (fun x =>
          avgOver (uniformDistribution (PointTuple params n)) (fun xs =>
            ∑ g ∈ (Finset.univ : Finset (GHatOutcome params)) with g.isSome = b,
              ∑ gs ∈ (Finset.univ : Finset (GHatTupleOutcome params n)) with
                  gHatTupleType gs = τ,
                let U := (gHatIdxMeas params family x).outcome g
                let T := gHatHalfProductOutcomeOperator params family n xs gs
                ev ψbi (leftTensor (ι₂ := ι) (T * Tᴴ) *
                  rightTensor (ι₁ := ι) (S * U * S)))) := by
      refine avgOver_congr _ _ _ ?_
      intro x
      refine avgOver_congr _ _ _ ?_
      intro xs
      dsimp [F, S]
      refine Finset.sum_congr rfl ?_
      intro g _hg
      refine Finset.sum_congr rfl ?_
      intro gs _hgs
      let U := (gHatIdxMeas params family x).outcome g
      let T := gHatHalfProductOutcomeOperator params family n xs gs
      have hUherm : Uᴴ = U := by
        simpa [U] using fromHToG_gHatIdxMeas_outcome_isHermitian params family x g
      have hUproj : U * U = U := by
        simpa [U] using gHatIdxMeas_proj params family x g
      have hSherm : Sᴴ = S :=
        fromHToGRecurrenceWeight_isHermitian params family ℓ (prependTypeBit b τ)
      calc
        ev ψbi ((leftTensor (ι₂ := ι) T * rightTensor (ι₁ := ι) (S * U)) *
            (leftTensor (ι₂ := ι) T * rightTensor (ι₁ := ι) (S * U))ᴴ)
          = ev ψbi (leftTensor (ι₂ := ι) (T * Tᴴ) *
              rightTensor (ι₁ := ι) ((S * U) * (Uᴴ * Sᴴ))) := by
              rw [leftTensor_mul_rightTensor_eq_opTensor]
              rw [conjTranspose_opTensor, opTensor_mul, Matrix.conjTranspose_mul]
              rw [show leftTensor (ι₂ := ι) (T * Tᴴ) *
                  rightTensor (ι₁ := ι) ((S * U) * (Uᴴ * Sᴴ)) =
                    opTensor (T * Tᴴ) ((S * U) * (Uᴴ * Sᴴ)) by
                rw [leftTensor_mul_rightTensor_eq_opTensor]]
        _ = ev ψbi (leftTensor (ι₂ := ι) (T * Tᴴ) *
              rightTensor (ι₁ := ι) (S * U * S)) := by
              have hright : (S * U) * (Uᴴ * Sᴴ) = S * U * S := by
                calc
                  (S * U) * (Uᴴ * Sᴴ) = S * U * (U * S) := by rw [hUherm, hSherm]
                  _ = S * (U * U) * S := by simp [mul_assoc]
                  _ = S * U * S := by rw [hUproj]
              simp [hright]
    rw [hrew]
    calc
      avgOver (uniformDistribution (Fq params)) (fun x =>
        avgOver (uniformDistribution (PointTuple params n)) (fun xs =>
          ∑ g ∈ (Finset.univ : Finset (GHatOutcome params)) with g.isSome = b,
            ∑ gs ∈ (Finset.univ : Finset (GHatTupleOutcome params n)) with
                gHatTupleType gs = τ,
              let U := (gHatIdxMeas params family x).outcome g
              let T := gHatHalfProductOutcomeOperator params family n xs gs
              ev ψbi (leftTensor (ι₂ := ι) (T * Tᴴ) *
                rightTensor (ι₁ := ι) (S * U * S))))
        = avgOver (uniformDistribution (Fq params)) (fun x =>
            avgOver (uniformDistribution (PointTuple params n)) (fun xs =>
              ∑ gs ∈ (Finset.univ : Finset (GHatTupleOutcome params n)) with
                  gHatTupleType gs = τ,
                let T := gHatHalfProductOutcomeOperator params family n xs gs
                let B := if b then (completePartSubMeas params family x).total
                  else (incompletePartSubMeas params family x).total
                ev ψbi (leftTensor (ι₂ := ι) (T * Tᴴ) *
                  rightTensor (ι₁ := ι) (S * B * S)))) := by
              refine avgOver_congr _ _ _ ?_
              intro x
              refine avgOver_congr _ _ _ ?_
              intro xs
              rw [Finset.sum_comm]
              refine Finset.sum_congr rfl ?_
              intro gs _hgs
              simpa [S] using
                (fromHToG_ev_sum_isSome_sandwich_weight params ψbi family x b
                  (gHatHalfProductOutcomeOperator params family n xs gs *
                    (gHatHalfProductOutcomeOperator params family n xs gs)ᴴ) S)
      _ = avgOver (uniformDistribution (Fq params)) (fun x =>
            ev ψbi (leftTensor (ι₂ := ι) Aτ *
              rightTensor (ι₁ := ι)
                (S * (if b then (completePartSubMeas params family x).total
                  else (incompletePartSubMeas params family x).total) * S))) := by
              refine avgOver_congr _ _ _ ?_
              intro x
              simpa [Aτ, S, gHatSandwichFamily] using
                (fromHToG_avgOver_tail_type_ev_sandwich params ψbi family n τ
                  (S * (if b then (completePartSubMeas params family x).total
                    else (incompletePartSubMeas params family x).total) * S))
      _ = ev ψbi (leftTensor (ι₂ := ι) Aτ *
            rightTensor (ι₁ := ι)
              (S * (if b then family.averagedSubMeas.total
                else 1 - family.averagedSubMeas.total) * S)) := by
              simpa [Aτ, S] using
                (fromHToG_avgOver_head_branch_ev_sandwich params ψbi family
                  hcomplete hincomplete b Aτ S)
      _ ≤ ev ψbi (leftTensor (ι₂ := ι) Aτ *
            rightTensor (ι₁ := ι)
              (if b then family.averagedSubMeas.total else 1 - family.averagedSubMeas.total)) := by
              have hAτ_nonneg : 0 ≤ Aτ := by
                simpa [Aτ] using
                  (averagedSandwichByTypeSubMeas params family n τ).total_nonneg
              cases b
              · simpa [S] using
                  fromHToG_ev_leftTensor_rightTensor_mono_right_of_nonneg_left ψbi hAτ_nonneg
                    (fromHToGRecurrenceWeight_sandwich_one_sub_base_le params family ℓ
                      (τtail := prependTypeBit false τ))
              · simpa [S] using
                  fromHToG_ev_leftTensor_rightTensor_mono_right_of_nonneg_left ψbi hAτ_nonneg
                    (fromHToGRecurrenceWeight_sandwich_base_le params family ℓ
                      (τtail := prependTypeBit true τ))
      _ = branchRhs b τ := by rfl
  rw [hsplit]
  calc
    ∑ b : Bool, ∑ τ : GHatType n,
        avgOver (uniformDistribution (Fq params)) (fun x =>
          avgOver (uniformDistribution (PointTuple params n)) (fun xs => F b τ x xs))
      ≤ ∑ b : Bool, ∑ τ : GHatType n, branchRhs b τ := by
            refine Finset.sum_le_sum ?_
            intro b _hb
            exact hbranchSum b
    _ = ∑ τ : GHatType n, ∑ b : Bool, branchRhs b τ := by
            rw [Finset.sum_comm]
    _ = ∑ τ : GHatType n,
          ev ψbi (leftTensor (ι₂ := ι)
            (averagedSandwichByTypeSubMeas params family n τ).total *
            rightTensor (ι₁ := ι)
              (family.averagedSubMeas.total + (1 - family.averagedSubMeas.total))) := by
            refine Finset.sum_congr rfl ?_
            intro τ _hτ
            rw [Fintype.sum_bool]
            dsimp [branchRhs]
            rw [← ev_add]
            apply congrArg (ev ψbi)
            calc
              leftTensor (ι₂ := ι)
                (averagedSandwichByTypeSubMeas params family n τ).total *
                  rightTensor (ι₁ := ι) family.averagedSubMeas.total +
                leftTensor (ι₂ := ι)
                  (averagedSandwichByTypeSubMeas params family n τ).total *
                  rightTensor (ι₁ := ι) (1 - family.averagedSubMeas.total)
                = leftTensor (ι₂ := ι)
                    (averagedSandwichByTypeSubMeas params family n τ).total *
                    (rightTensor (ι₁ := ι) family.averagedSubMeas.total +
                      rightTensor (ι₁ := ι) (1 - family.averagedSubMeas.total)) := by
                        rw [← mul_add]
              _ = leftTensor (ι₂ := ι)
                    (averagedSandwichByTypeSubMeas params family n τ).total *
                    rightTensor (ι₁ := ι)
                      (family.averagedSubMeas.total + (1 - family.averagedSubMeas.total)) := by
                        rw [fromHToG_rightTensor_add]
    _ = ∑ τ : GHatType n,
          ev ψbi (leftTensor (ι₂ := ι)
            (averagedSandwichByTypeSubMeas params family n τ).total) := by
            refine Finset.sum_congr rfl ?_
            intro τ _hτ
            have hone : family.averagedSubMeas.total +
                (1 - family.averagedSubMeas.total) = (1 : MIPStarRE.Quantum.Op ι) := by
              simp
            rw [hone, rightTensor_one, mul_one]
    _ = ev ψbi (leftTensor (ι₂ := ι)
          (∑ τ : GHatType n,
            (averagedSandwichByTypeSubMeas params family n τ).total)) := by
            rw [← ev_sum]
            rw [leftTensor_finset_sum]
    _ = ev ψbi (leftTensor (ι₂ := ι) (1 : MIPStarRE.Quantum.Op ι)) := by
          rw [fromHToG_sum_averagedSandwichByType_total_eq_one params family n]
    _ = 1 := by simpa [leftTensor] using ev_one_of_isNormalized ψbi hnorm
end MIPStarRE.LDT.Pasting
