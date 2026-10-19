-- Prove2me | solution 1 for MIPStarRE.LDT.Pasting.fromHToGAdjacentStage_paperMoveChain
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T07:07:17.112735+00:00
-- url     : https://prove2.me/submissions/d5d4032a-b7ba-4cd9-9c76-d65e5fd8720c

/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE, with the
authors' permission. Vendored from https://github.com/LionSR/MIPStarRE
(commit 507e8122, 2026-08-25) by scripts/vendor-lidt.py; do not edit by hand.
Upstream path: MIPStarRE/LDT/Pasting/Bernoulli/FromHToG/PaperMoveChain/Telescope.lean
-/
/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE, with the
authors' permission. Vendored from https://github.com/LionSR/MIPStarRE
(commit 507e8122, 2026-08-25) by scripts/vendor-lidt.py; do not edit by hand.
Upstream path: MIPStarRE/LDT/Preliminaries/CauchySchwarz.lean
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
Upstream path: MIPStarRE/LDT/Pasting/Bernoulli/FromHToG/PaperBounds/SandwichContext.lean
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/LIDT/MIPStarRE/LDT/Pasting/Bernoulli/FromHToG/PaperMoveChain/Telescope.lean (solution of MIPStarRE.LDT.Pasting.fromHToGAdjacentStage_paperMoveChain);
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
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Pasting_Bernoulli_FromHToG_PaperBounds
import Theorems.Thm_MIPStarRE_LDT_Measurement_outcome_hermitian
import Theorems.Thm_MIPStarRE_LDT_Measurement_outcome_le_one
import Theorems.Thm_MIPStarRE_LDT_Pasting_fromHToGAdjacentStageA0_eq_leftShape
import Theorems.Thm_MIPStarRE_LDT_Pasting_fromHToGAdjacentStageM1_eq_halfSandwichLeftShape
import Theorems.Thm_MIPStarRE_LDT_Pasting_fromHToGAdjacentStageM1_eq_rightShape
import Theorems.Thm_MIPStarRE_LDT_Pasting_fromHToGAdjacentStageM2M3_paperMove
import Theorems.Thm_MIPStarRE_LDT_Pasting_fromHToGAdjacentStageM2_eq_halfSandwichRightShape
import Theorems.Thm_MIPStarRE_LDT_Pasting_fromHToGAdjacentStageM3E_paperMove
import Theorems.Thm_MIPStarRE_LDT_Pasting_fromHToGStageMass_eq_adjacentStageA0
import Theorems.Thm_MIPStarRE_LDT_Pasting_fromHToG_headTail_adjoint_qSDDCore_bound
import Theorems.Thm_MIPStarRE_LDT_Pasting_fromHToG_selfConsistency_qSDDCore_bound
import Theorems.Thm_MIPStarRE_LDT_Pasting_gHatHalfProductTotalOperator_eq_one
import Theorems.Thm_MIPStarRE_LDT_Pasting_gHatIdxMeas_proj
import Theorems.Thm_MIPStarRE_LDT_Preliminaries_closenessOfIP
import Theorems.Thm_MIPStarRE_LDT_Preliminaries_closenessOfInnerProduct_right
import Theorems.Thm_MIPStarRE_LDT_avgOver_congr
import Theorems.Thm_MIPStarRE_LDT_leftTensor_finset_sum
import Theorems.Thm_MIPStarRE_LDT_leftTensor_le_one
import Theorems.Thm_MIPStarRE_LDT_leftTensor_mul_leftTensor
import Theorems.Thm_MIPStarRE_LDT_leftTensor_mul_rightTensor_eq_opTensor
import Theorems.Thm_MIPStarRE_LDT_leftTensor_nonneg
import Theorems.Thm_MIPStarRE_LDT_opTensor_mono_right
import Theorems.Thm_MIPStarRE_LDT_opTensor_mul
import Theorems.Thm_MIPStarRE_LDT_rightTensor_finset_sum
import Theorems.Thm_MIPStarRE_Quantum_kronecker_nonneg
import Theorems.Thm_MIPStarRE_Quantum_sq_le_self

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPStarRE.LDT.Preliminaries
section
open scoped BigOperators MatrixOrder Matrix ComplexOrder
open MIPStarRE.LDT
set_option backward.isDefEq.respectTransparency false
/-- `prop:closeness-of-ip` (`eq:closeness4`, adjoint version).

If `A† ≈_γ B†` and `Σ_a (Σ_b C_{a,b})†(Σ_b C_{a,b}) ≤ I`, then
`|𝔼_x Σ_{a,b} ⟨ψ| A_a C_{a,b} |ψ⟩ -
  𝔼_x Σ_{a,b} ⟨ψ| B_a C_{a,b} |ψ⟩| ≤ √γ`. -/
theorem closenessOfIPAdjoint
    {Question OutcomeA OutcomeB : Type*} {ι : Type*}
    [Fintype OutcomeA] [Fintype OutcomeB] [Fintype ι] [DecidableEq ι]
    (ψ : QuantumState ι) (hψ : ψ.IsNormalized)
    (𝒟 : Distribution Question)
    (h𝒟 : ∑ q ∈ 𝒟.support, 𝒟.weight q ≤ 1)
    (A B : Question → OutcomeA → MIPStarRE.Quantum.Op ι)
    (C : Question → OutcomeA → OutcomeB → MIPStarRE.Quantum.Op ι)
    (γ : Error)
    (hAB :
      avgOver 𝒟
        (fun q => qSDDCore ψ (fun a => (A q a)ᴴ) (fun a => (B q a)ᴴ)) ≤ γ)
    (hC :
      ∀ q,
        ∑ a : OutcomeA,
          (∑ b : OutcomeB, C q a b)ᴴ * (∑ b : OutcomeB, C q a b) ≤ 1) :
    |avgOver 𝒟 (fun q => ∑ a : OutcomeA, ∑ b : OutcomeB, ev ψ (A q a * C q a b)) -
        avgOver 𝒟 (fun q => ∑ a : OutcomeA, ∑ b : OutcomeB, ev ψ (B q a * C q a b))| ≤
      Real.sqrt γ := by
  simpa using closenessOfInnerProduct_right ψ hψ 𝒟 h𝒟 A B C γ hAB hC
end
end MIPStarRE.LDT.Preliminaries

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
open scoped BigOperators MatrixOrder Matrix ComplexOrder
set_option backward.isDefEq.respectTransparency false
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
/-- Conjugate transpose commutes with left tensor placement. -/
lemma fromHToG_leftTensor_conjTranspose (A : MIPStarRE.Quantum.Op ι) :
    (leftTensor (ι₂ := ι) A)ᴴ = leftTensor (ι₂ := ι) Aᴴ := by
  simp [leftTensor, Matrix.conjTranspose_kronecker]
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
lemma abs_sub_le_four (a b c d e : Error) :
    |a - e| ≤ |a - b| + |b - c| + |c - d| + |d - e| := by
  have h₁ : |a - e| ≤ |a - b| + |b - e| := abs_sub_le a b e
  have h₂ : |b - e| ≤ |b - c| + |c - e| := abs_sub_le b c e
  have h₃ : |c - e| ≤ |c - d| + |d - e| := abs_sub_le c d e
  linarith
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
/-- The total mass of the tail sandwich family is the identity. -/
lemma fromHToG_gHatSandwichFamily_total_eq_one
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (n : ℕ) (xs : PointTuple params n) :
    (gHatSandwichFamily params family n xs).total = 1 := by
  simp [gHatSandwichFamily, gHatHalfProductTotalOperator_eq_one]
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
/-- The tail sandwich outcomes sum to the identity. -/
lemma fromHToG_gHatSandwichFamily_sum_eq_one
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (n : ℕ) (xs : PointTuple params n) :
    (∑ gs : GHatTupleOutcome params n,
      (gHatSandwichFamily params family n xs).outcome gs) = 1 := by
  rw [(gHatSandwichFamily params family n xs).sum_eq_total]
  exact fromHToG_gHatSandwichFamily_total_eq_one params family n xs
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
    (ψbi : QuantumState (ι × ι))
    (hnorm : ψbi.IsNormalized)
    (family : IdxPolyFamily params ι)
    (gamma zeta : Error)
    (hgamma_nonneg : 0 ≤ gamma) (hzeta_nonneg : 0 ≤ zeta)
    (hfacts : GHatFactsStatement params ψbi family gamma zeta)
    (hhalf : ∀ j : ℕ, 2 ≤ j →
      CommuteGHalfSandwichStatement params ψbi family gamma zeta j)
    (hstageExact : FromHToGAdjacentStageExactFacts params ψbi family)
    (k ℓ : ℕ) (hℓ : ℓ < k) :
    |fromHToGStageMass params ψbi family k ℓ -
        fromHToGStageMass params ψbi family k (ℓ + 1)| ≤
      fromHToGRecurrenceError params gamma zeta k := by
  let A : Error := fromHToGStageMass params ψbi family k ℓ
  let E : Error := fromHToGStageMass params ψbi family k (ℓ + 1)
  let M₁ : Error := fromHToGAdjacentStageM1 params ψbi family k ℓ
  let M₂ : Error := fromHToGAdjacentStageM2 params ψbi family k ℓ
  let M₃ : Error := fromHToGAdjacentStageM3 params ψbi family k ℓ
  let M₄ : Error := fromHToGAdjacentStageM4 params ψbi family k ℓ
  let Collapsed : Error := fromHToGAdjacentStageCollapsed params ψbi family k ℓ
  have hA₁ : |A - M₁| ≤ Real.sqrt (2 * zeta) := by
    have hA_eq_A0 : A = fromHToGAdjacentStageA0 params ψbi family k ℓ := by
      simpa [A] using fromHToGStageMass_eq_adjacentStageA0 params ψbi family hℓ
    let n := k - (ℓ + 1)
    have hA0M1_secondRoot_le :
        avgOver (uniformDistribution (Fq params × PointTuple params n)) (fun q =>
          qSDDCore ψbi
            (fun g : GHatOutcome params =>
              leftTensor (ι₂ := ι) ((gHatIdxMeas params family q.1).outcome g))
            (fun g : GHatOutcome params =>
              rightTensor (ι₁ := ι) ((gHatIdxMeas params family q.1).outcome g))) ≤
          2 * zeta := by
      simpa [n] using
        fromHToG_selfConsistency_qSDDCore_bound params ψbi family zeta
          hfacts.completedSelfConsistency (n := n)
    have hA0M1_moveRight :
        |fromHToGAdjacentStageA0 params ψbi family k ℓ -
            fromHToGAdjacentStageM1 params ψbi family k ℓ| ≤ Real.sqrt (2 * zeta) := by
      let Aop : Fq params × PointTuple params n → GHatOutcome params →
          MIPStarRE.Quantum.Op (ι × ι) := fun q g =>
        leftTensor (ι₂ := ι) ((gHatIdxMeas params family q.1).outcome g)
      let Bop : Fq params × PointTuple params n → GHatOutcome params →
          MIPStarRE.Quantum.Op (ι × ι) := fun q g =>
        rightTensor (ι₁ := ι) ((gHatIdxMeas params family q.1).outcome g)
      let C : Fq params × PointTuple params n → GHatOutcome params →
          GHatTupleOutcome params n → MIPStarRE.Quantum.Op (ι × ι) := fun q g gs =>
        let S := fromHToGRecurrenceWeight params family ℓ
          (prependTypeBit g.isSome (gHatTupleType gs))
        let U := (gHatIdxMeas params family q.1).outcome g
        let T := gHatHalfProductOutcomeOperator params family n q.2 gs
        leftTensor (ι₂ := ι) (U * T * Tᴴ) * rightTensor (ι₁ := ι) S
      have hA0M1_firstRoot_le_one : ∀ q : Fq params × PointTuple params n,
          ∑ g : GHatOutcome params,
            (∑ gs : GHatTupleOutcome params n, C q g gs) *
              (∑ gs : GHatTupleOutcome params n, C q g gs)ᴴ ≤ 1 := by
        /- Paper lines 1472--1478: the first square root in
        `eq:call-again-later-part-tres` is exactly the `Ĥ ⊗ S²` term, so this
        should be discharged by rewriting `A0` as a suffix `Ĥ`, using
        `eq:S-bound`, and then applying submeasurement boundedness. -/
        intro q
        let tailBlock : GHatOutcome params → MIPStarRE.Quantum.Op (ι × ι) := fun g =>
          ∑ gs : GHatTupleOutcome params n,
            let S := fromHToGRecurrenceWeight params family ℓ
              (prependTypeBit g.isSome (gHatTupleType gs))
            let T := gHatHalfProductOutcomeOperator params family n q.2 gs
            leftTensor (ι₂ := ι) (T * Tᴴ) * rightTensor (ι₁ := ι) S
        have htail_expand : ∀ g : GHatOutcome params,
            ∑ gs : GHatTupleOutcome params n, C q g gs =
              leftTensor (ι₂ := ι) ((gHatIdxMeas params family q.1).outcome g) *
                tailBlock g := by
          intro g
          dsimp [tailBlock, C]
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl ?_
          intro gs _hgs
          calc
            leftTensor
                ((gHatIdxMeas params family q.1).outcome g *
                  gHatHalfProductOutcomeOperator params family n q.2 gs *
                    (gHatHalfProductOutcomeOperator params family n q.2 gs)ᴴ) *
                rightTensor
                  (fromHToGRecurrenceWeight params family ℓ
                    (prependTypeBit g.isSome (gHatTupleType gs)))
              = leftTensor
                  ((gHatIdxMeas params family q.1).outcome g *
                    (gHatHalfProductOutcomeOperator params family n q.2 gs *
                      (gHatHalfProductOutcomeOperator params family n q.2 gs)ᴴ)) *
                rightTensor
                  (fromHToGRecurrenceWeight params family ℓ
                    (prependTypeBit g.isSome (gHatTupleType gs))) := by
                        simp [mul_assoc]
            _ = (leftTensor (ι₂ := ι) ((gHatIdxMeas params family q.1).outcome g) *
                  leftTensor (ι₂ := ι)
                    (gHatHalfProductOutcomeOperator params family n q.2 gs *
                      (gHatHalfProductOutcomeOperator params family n q.2 gs)ᴴ)) *
                  rightTensor
                    (fromHToGRecurrenceWeight params family ℓ
                      (prependTypeBit g.isSome (gHatTupleType gs))) := by
                        rw [← leftTensor_mul_leftTensor]
            _ = leftTensor (ι₂ := ι) ((gHatIdxMeas params family q.1).outcome g) *
                  (leftTensor (ι₂ := ι)
                      (gHatHalfProductOutcomeOperator params family n q.2 gs *
                        (gHatHalfProductOutcomeOperator params family n q.2 gs)ᴴ) *
                    rightTensor
                      (fromHToGRecurrenceWeight params family ℓ
                        (prependTypeBit g.isSome (gHatTupleType gs)))) := by
                          simp [mul_assoc]
        have htail_pos : ∀ g : GHatOutcome params, 0 ≤ tailBlock g := by
          intro g
          dsimp [tailBlock]
          refine Finset.sum_nonneg ?_
          intro gs _hgs
          let S := fromHToGRecurrenceWeight params family ℓ
            (prependTypeBit g.isSome (gHatTupleType gs))
          let T := gHatHalfProductOutcomeOperator params family n q.2 gs
          have hTT_pos : 0 ≤ T * Tᴴ := by
            have hpos : 0 ≤ (Tᴴ)ᴴ * Tᴴ :=
              (CStarAlgebra.nonneg_iff_eq_star_mul_self).2 ⟨Tᴴ, rfl⟩
            simpa using hpos
          have hS_pos : 0 ≤ S :=
            fromHToGRecurrenceWeight_nonneg params family ℓ
              (prependTypeBit g.isSome (gHatTupleType gs))
          rw [leftTensor_mul_rightTensor_eq_opTensor]
          exact MIPStarRE.Quantum.kronecker_nonneg hTT_pos hS_pos
        have htail_le_one : ∀ g : GHatOutcome params, tailBlock g ≤ 1 := by
          intro g
          let sandTerm : GHatTupleOutcome params n → MIPStarRE.Quantum.Op (ι × ι) := fun gs =>
            let S := fromHToGRecurrenceWeight params family ℓ
              (prependTypeBit g.isSome (gHatTupleType gs))
            let T := gHatHalfProductOutcomeOperator params family n q.2 gs
            leftTensor (ι₂ := ι) (T * Tᴴ) * rightTensor (ι₁ := ι) S
          let sandLeft : GHatTupleOutcome params n → MIPStarRE.Quantum.Op (ι × ι) := fun gs =>
            let T := gHatHalfProductOutcomeOperator params family n q.2 gs
            leftTensor (ι₂ := ι) (T * Tᴴ)
          calc
            tailBlock g = ∑ gs : GHatTupleOutcome params n, sandTerm gs := by
              simp [tailBlock, sandTerm]
            _ ≤ ∑ gs : GHatTupleOutcome params n, sandLeft gs := by
                    refine Finset.sum_le_sum ?_
                    intro gs _hgs
                    let S := fromHToGRecurrenceWeight params family ℓ
                      (prependTypeBit g.isSome (gHatTupleType gs))
                    let T := gHatHalfProductOutcomeOperator params family n q.2 gs
                    have hTT_pos : 0 ≤ T * Tᴴ := by
                      have hpos : 0 ≤ (Tᴴ)ᴴ * Tᴴ :=
                        (CStarAlgebra.nonneg_iff_eq_star_mul_self).2 ⟨Tᴴ, rfl⟩
                      simpa using hpos
                    have hS_le : S ≤ 1 :=
                      fromHToGRecurrenceWeight_le_one params family ℓ
                        (prependTypeBit g.isSome (gHatTupleType gs))
                    dsimp [sandTerm, sandLeft]
                    rw [leftTensor_mul_rightTensor_eq_opTensor]
                    simpa [sandTerm, sandLeft, T, leftTensor, opTensor] using
                      MIPStarRE.LDT.opTensor_mono_right (A := T * Tᴴ) hTT_pos hS_le
            _ = leftTensor (ι₂ := ι)
                  (∑ gs : GHatTupleOutcome params n,
                    let T := gHatHalfProductOutcomeOperator params family n q.2 gs
                    T * Tᴴ) := by
                      simp [sandLeft, leftTensor_finset_sum]
            _ = 1 := by
                  have hsum :
                      (∑ gs : GHatTupleOutcome params n,
                        let T := gHatHalfProductOutcomeOperator params family n q.2 gs
                        T * Tᴴ) = 1 := by
                    simpa [gHatSandwichFamily] using
                      fromHToG_gHatSandwichFamily_sum_eq_one params family n q.2
                  rw [hsum]
                  simp [leftTensor]
        have htail_sq_le_self : ∀ g : GHatOutcome params,
            tailBlock g * tailBlock g ≤ tailBlock g := by
          intro g
          exact MIPStarRE.Quantum.sq_le_self (htail_pos g) (htail_le_one g)
        have hterm_le : ∀ g : GHatOutcome params,
            (∑ gs : GHatTupleOutcome params n, C q g gs) *
                (∑ gs : GHatTupleOutcome params n, C q g gs)ᴴ ≤
              leftTensor (ι₂ := ι) ((gHatIdxMeas params family q.1).outcome g) := by
          intro g
          let U := (gHatIdxMeas params family q.1).outcome g
          have hU_herm : (leftTensor (ι₂ := ι) U)ᴴ = leftTensor (ι₂ := ι) U := by
            simpa [U, leftTensor, opTensor,
              fromHToG_gHatIdxMeas_outcome_isHermitian params family q.1 g] using
              (conjTranspose_opTensor U (1 : MIPStarRE.Quantum.Op ι))
          have hU_pos : 0 ≤ leftTensor (ι₂ := ι) U := by
            exact leftTensor_nonneg (ι₂ := ι) ((gHatIdxMeas params family q.1).outcome_pos g)
          have hU_le : leftTensor (ι₂ := ι) U ≤ 1 := by
            exact leftTensor_le_one (ι₂ := ι) ((gHatIdxMeas params family q.1).outcome_le_one g)
          calc
            (∑ gs : GHatTupleOutcome params n, C q g gs) *
                (∑ gs : GHatTupleOutcome params n, C q g gs)ᴴ
              = leftTensor (ι₂ := ι) U * (tailBlock g * tailBlock g) *
                  leftTensor (ι₂ := ι) U := by
                  rw [htail_expand g, Matrix.conjTranspose_mul, hU_herm]
                  have htail_herm : (tailBlock g)ᴴ = tailBlock g := by
                    exact (Matrix.nonneg_iff_posSemidef.mp (htail_pos g)).isHermitian.eq
                  rw [htail_herm]
                  simp [mul_assoc, U]
            _ ≤ leftTensor (ι₂ := ι) U * tailBlock g * leftTensor (ι₂ := ι) U := by
                  exact IsSelfAdjoint.conjugate_le_conjugate (htail_sq_le_self g) hU_herm
            _ ≤ leftTensor (ι₂ := ι) U * 1 * leftTensor (ι₂ := ι) U := by
                  exact IsSelfAdjoint.conjugate_le_conjugate (htail_le_one g) hU_herm
            _ ≤ leftTensor (ι₂ := ι) U := by
                  calc
                    leftTensor (ι₂ := ι) U * 1 * leftTensor (ι₂ := ι) U
                      = leftTensor (ι₂ := ι) U * leftTensor (ι₂ := ι) U := by simp
                    _ ≤ leftTensor (ι₂ := ι) U := by
                      simpa [leftTensor_mul_leftTensor] using
                        MIPStarRE.Quantum.sq_le_self hU_pos hU_le
        calc
          ∑ g : GHatOutcome params,
              (∑ gs : GHatTupleOutcome params n, C q g gs) *
                (∑ gs : GHatTupleOutcome params n, C q g gs)ᴴ
            ≤ ∑ g : GHatOutcome params,
                leftTensor (ι₂ := ι) ((gHatIdxMeas params family q.1).outcome g) := by
                  exact Finset.sum_le_sum (fun g _hg => hterm_le g)
          _ = leftTensor (ι₂ := ι)
                (∑ g : GHatOutcome params, (gHatIdxMeas params family q.1).outcome g) := by
                  rw [← leftTensor_finset_sum (ι₂ := ι) Finset.univ
                    (fun g : GHatOutcome params => (gHatIdxMeas params family q.1).outcome g)]
          _ = 1 := by
                rw [(gHatIdxMeas params family q.1).sum_eq_total]
                rw [(gHatIdxMeas params family q.1).total_eq_one]
                simp [leftTensor]
      have hA0M1_cauchySchwarz := MIPStarRE.LDT.Preliminaries.closenessOfIP ψbi hnorm
        (uniformDistribution (Fq params × PointTuple params n))
        (uniformDistribution_weight_sum_le_one (Fq params × PointTuple params n))
        Aop Bop C (2 * zeta) (by simpa [Aop, Bop] using hA0M1_secondRoot_le)
        hA0M1_firstRoot_le_one
      simpa [Aop, Bop, C, fromHToGAdjacentStageA0_eq_leftShape,
        fromHToGAdjacentStageM1_eq_rightShape] using hA0M1_cauchySchwarz
    simpa [hA_eq_A0, M₁] using hA0M1_moveRight
  have h₁₂ : |M₁ - M₂| ≤ Real.sqrt (commuteGHalfSandwichError params gamma zeta k) := by
    /- Paper lines 1495--1550.  This is the first half-sandwich commutation:
    first rewrite `eq:move-g-over-there` into the source/target forms of
    `eq:commute-g-part-one`, then apply the Cauchy--Schwarz estimate
    `eq:call-this-later`, with the two square roots handled separately. -/
    let n := k - (ℓ + 1)
    by_cases hn0 : n = 0
    · have hM₁ : M₁ =
          avgOver (uniformDistribution (Fq params × PointTuple params n)) fun q =>
            ∑ g : GHatOutcome params, ∑ gs : GHatTupleOutcome params n,
              let S := fromHToGRecurrenceWeight params family ℓ
                (prependTypeBit g.isSome (gHatTupleType gs))
              let U := (gHatIdxMeas params family q.1).outcome g
              let T := gHatHalfProductOutcomeOperator params family n q.2 gs
              ev ψbi (leftTensor (ι₂ := ι) (U * T) *
                (leftTensor (ι₂ := ι) Tᴴ * rightTensor (ι₁ := ι) (S * U))) := by
        simpa [M₁, n] using
          fromHToGAdjacentStageM1_eq_halfSandwichLeftShape params ψbi family k ℓ
      have hM₂ : M₂ =
          avgOver (uniformDistribution (Fq params × PointTuple params n)) fun q =>
            ∑ g : GHatOutcome params, ∑ gs : GHatTupleOutcome params n,
              let S := fromHToGRecurrenceWeight params family ℓ
                (prependTypeBit g.isSome (gHatTupleType gs))
              let U := (gHatIdxMeas params family q.1).outcome g
              let T := gHatHalfProductOutcomeOperator params family n q.2 gs
              ev ψbi (leftTensor (ι₂ := ι) (T * U) *
                (leftTensor (ι₂ := ι) Tᴴ * rightTensor (ι₁ := ι) (S * U))) := by
        simpa only [M₂] using
          fromHToGAdjacentStageM2_eq_halfSandwichRightShape params ψbi family k ℓ
      have hM : M₁ = M₂ := by
        rw [hM₁, hM₂]
        rw [hn0]
        simp [gHatHalfProductOutcomeOperator]
      rw [hM, sub_self, abs_zero]
      exact Real.sqrt_nonneg _
    · have hnpos : 1 ≤ n := Nat.pos_iff_ne_zero.mpr hn0
      have hn : 2 ≤ n + 1 := Nat.succ_le_succ hnpos
      have hnk : n + 1 ≤ k := by
        dsimp [n]
        omega
      have hM₁_source : M₁ =
          avgOver (uniformDistribution (Fq params × PointTuple params n)) fun q =>
            ∑ g : GHatOutcome params, ∑ gs : GHatTupleOutcome params n,
              let S := fromHToGRecurrenceWeight params family ℓ
                (prependTypeBit g.isSome (gHatTupleType gs))
              let U := (gHatIdxMeas params family q.1).outcome g
              let T := gHatHalfProductOutcomeOperator params family n q.2 gs
              ev ψbi (leftTensor (ι₂ := ι) (U * T) *
                (leftTensor (ι₂ := ι) Tᴴ * rightTensor (ι₁ := ι) (S * U))) := by
        simpa [M₁, n] using
          fromHToGAdjacentStageM1_eq_halfSandwichLeftShape params ψbi family k ℓ
      have hM₂_target : M₂ =
          avgOver (uniformDistribution (Fq params × PointTuple params n)) fun q =>
            ∑ g : GHatOutcome params, ∑ gs : GHatTupleOutcome params n,
              let S := fromHToGRecurrenceWeight params family ℓ
                (prependTypeBit g.isSome (gHatTupleType gs))
              let U := (gHatIdxMeas params family q.1).outcome g
              let T := gHatHalfProductOutcomeOperator params family n q.2 gs
              ev ψbi (leftTensor (ι₂ := ι) (T * U) *
                (leftTensor (ι₂ := ι) Tᴴ * rightTensor (ι₁ := ι) (S * U))) := by
        simpa [M₂, n] using
          fromHToGAdjacentStageM2_eq_halfSandwichRightShape params ψbi family k ℓ
      have h₁₂_secondRoot_le_nu4 :
          avgOver (uniformDistribution (Fq params × PointTuple params n)) (fun q =>
            qSDDCore ψbi
              (fun ogs : GHatOutcome params × GHatTupleOutcome params n =>
                leftTensor (ι₂ := ι)
                  ((gHatHalfProductOutcomeOperator params family n q.2 ogs.2)ᴴ *
                    (gHatIdxMeas params family q.1).outcome ogs.1))
              (fun ogs : GHatOutcome params × GHatTupleOutcome params n =>
                leftTensor (ι₂ := ι)
                  ((gHatIdxMeas params family q.1).outcome ogs.1 *
                    (gHatHalfProductOutcomeOperator params family n q.2 ogs.2)ᴴ))) ≤
            commuteGHalfSandwichError params gamma zeta k := by
        simpa [n] using
          fromHToG_headTail_adjoint_qSDDCore_bound params ψbi family gamma zeta
            hgamma_nonneg hzeta_nonneg hhalf (n := n) (k := k) hn hnk
      have h₁₂_firstRoot_le_one :
          ∀ q : Fq params × PointTuple params n,
            ∑ ogs : GHatOutcome params × GHatTupleOutcome params n,
              (∑ _u : Unit,
                let S := fromHToGRecurrenceWeight params family ℓ
                  (prependTypeBit ogs.1.isSome (gHatTupleType ogs.2))
                let U := (gHatIdxMeas params family q.1).outcome ogs.1
                let T := gHatHalfProductOutcomeOperator params family n q.2 ogs.2
                leftTensor (ι₂ := ι) Tᴴ * rightTensor (ι₁ := ι) (S * U))ᴴ *
              (∑ _u : Unit,
                let S := fromHToGRecurrenceWeight params family ℓ
                  (prependTypeBit ogs.1.isSome (gHatTupleType ogs.2))
                let U := (gHatIdxMeas params family q.1).outcome ogs.1
                let T := gHatHalfProductOutcomeOperator params family n q.2 ogs.2
                leftTensor (ι₂ := ι) Tᴴ * rightTensor (ι₁ := ι) (S * U)) ≤ 1 := by
        /- Paper lines 1531--1550: the first square root in
        `eq:call-this-later` is rewritten to a suffix `Ĥ` term, bounded by
        `S ≤ I`, then by projectivity `U^2 = U`, and finally by the fact that
        both `ĝ` and `Ĥ` are submeasurements. -/
        intro q
        have hterm_le : ∀ ogs : GHatOutcome params × GHatTupleOutcome params n,
            (∑ _u : Unit,
              let S := fromHToGRecurrenceWeight params family ℓ
                (prependTypeBit ogs.1.isSome (gHatTupleType ogs.2))
              let U := (gHatIdxMeas params family q.1).outcome ogs.1
              let T := gHatHalfProductOutcomeOperator params family n q.2 ogs.2
              leftTensor (ι₂ := ι) Tᴴ * rightTensor (ι₁ := ι) (S * U))ᴴ *
            (∑ _u : Unit,
              let S := fromHToGRecurrenceWeight params family ℓ
                (prependTypeBit ogs.1.isSome (gHatTupleType ogs.2))
              let U := (gHatIdxMeas params family q.1).outcome ogs.1
              let T := gHatHalfProductOutcomeOperator params family n q.2 ogs.2
              leftTensor (ι₂ := ι) Tᴴ * rightTensor (ι₁ := ι) (S * U)) ≤
              leftTensor (ι₂ := ι)
                (gHatHalfProductOutcomeOperator params family n q.2 ogs.2 *
                  (gHatHalfProductOutcomeOperator params family n q.2 ogs.2)ᴴ) *
                rightTensor (ι₁ := ι) ((gHatIdxMeas params family q.1).outcome ogs.1) := by
          intro ogs
          let S := fromHToGRecurrenceWeight params family ℓ
            (prependTypeBit ogs.1.isSome (gHatTupleType ogs.2))
          let U := (gHatIdxMeas params family q.1).outcome ogs.1
          let T := gHatHalfProductOutcomeOperator params family n q.2 ogs.2
          have hTpos : 0 ≤ T * Tᴴ := by
            have hpos : 0 ≤ (Tᴴ)ᴴ * Tᴴ :=
              (CStarAlgebra.nonneg_iff_eq_star_mul_self).2 ⟨Tᴴ, rfl⟩
            simpa using hpos
          have hUherm : Uᴴ = U := by
            simpa [U] using fromHToG_gHatIdxMeas_outcome_isHermitian params family q.1 ogs.1
          have hSU_le : (S * U)ᴴ * (S * U) ≤ U := by
            have hSsq : S * S ≤ 1 := by
              exact le_trans (MIPStarRE.Quantum.sq_le_self
                (fromHToGRecurrenceWeight_nonneg params family ℓ
                  (prependTypeBit ogs.1.isSome (gHatTupleType ogs.2)))
                (fromHToGRecurrenceWeight_le_one params family ℓ
                  (prependTypeBit ogs.1.isSome (gHatTupleType ogs.2))))
                (fromHToGRecurrenceWeight_le_one params family ℓ
                  (prependTypeBit ogs.1.isSome (gHatTupleType ogs.2)))
            calc
              (S * U)ᴴ * (S * U) = U * (S * S) * U := by
                simp [Matrix.conjTranspose_mul, hUherm, S, U, mul_assoc,
                  fromHToGRecurrenceWeight_isHermitian]
              _ ≤ U * 1 * U := IsSelfAdjoint.conjugate_le_conjugate hSsq hUherm
              _ ≤ U := by
                have hUpos : 0 ≤ U := (gHatIdxMeas params family q.1).outcome_pos ogs.1
                have hUle : U ≤ 1 := (gHatIdxMeas params family q.1).outcome_le_one ogs.1
                simpa using MIPStarRE.Quantum.sq_le_self hUpos hUle
          calc
            (∑ _u : Unit, leftTensor (ι₂ := ι) Tᴴ * rightTensor (ι₁ := ι) (S * U))ᴴ *
                (∑ _u : Unit, leftTensor (ι₂ := ι) Tᴴ * rightTensor (ι₁ := ι) (S * U))
              = leftTensor (ι₂ := ι) (T * Tᴴ) *
                  rightTensor (ι₁ := ι) ((S * U)ᴴ * (S * U)) := by
                    rw [leftTensor_mul_rightTensor_eq_opTensor,
                      leftTensor_mul_rightTensor_eq_opTensor]
                    simp [conjTranspose_opTensor, opTensor_mul, Matrix.conjTranspose_mul,
                      hUherm, fromHToGRecurrenceWeight_isHermitian, S, U, mul_assoc]
            _ ≤ leftTensor (ι₂ := ι) (T * Tᴴ) * rightTensor (ι₁ := ι) U := by
                  rw [leftTensor_mul_rightTensor_eq_opTensor,
                    leftTensor_mul_rightTensor_eq_opTensor]
                  exact MIPStarRE.LDT.opTensor_mono_right hTpos hSU_le
        calc
          ∑ ogs : GHatOutcome params × GHatTupleOutcome params n,
              (∑ _u : Unit,
                let S := fromHToGRecurrenceWeight params family ℓ
                  (prependTypeBit ogs.1.isSome (gHatTupleType ogs.2))
                let U := (gHatIdxMeas params family q.1).outcome ogs.1
                let T := gHatHalfProductOutcomeOperator params family n q.2 ogs.2
                leftTensor (ι₂ := ι) Tᴴ * rightTensor (ι₁ := ι) (S * U))ᴴ *
              (∑ _u : Unit,
                let S := fromHToGRecurrenceWeight params family ℓ
                  (prependTypeBit ogs.1.isSome (gHatTupleType ogs.2))
                let U := (gHatIdxMeas params family q.1).outcome ogs.1
                let T := gHatHalfProductOutcomeOperator params family n q.2 ogs.2
                leftTensor (ι₂ := ι) Tᴴ * rightTensor (ι₁ := ι) (S * U))
            ≤ ∑ ogs : GHatOutcome params × GHatTupleOutcome params n,
                leftTensor (ι₂ := ι)
                  (gHatHalfProductOutcomeOperator params family n q.2 ogs.2 *
                    (gHatHalfProductOutcomeOperator params family n q.2 ogs.2)ᴴ) *
                  rightTensor (ι₁ := ι) ((gHatIdxMeas params family q.1).outcome ogs.1) := by
                exact Finset.sum_le_sum (fun ogs _ => hterm_le ogs)
          _ = 1 := by
                calc
                  ∑ ogs : GHatOutcome params × GHatTupleOutcome params n,
                      leftTensor (ι₂ := ι)
                        (gHatHalfProductOutcomeOperator params family n q.2 ogs.2 *
                          (gHatHalfProductOutcomeOperator params family n q.2 ogs.2)ᴴ) *
                        rightTensor (ι₁ := ι) ((gHatIdxMeas params family q.1).outcome ogs.1)
                    = ∑ g : GHatOutcome params, ∑ gs : GHatTupleOutcome params n,
                        leftTensor (ι₂ := ι)
                          (gHatHalfProductOutcomeOperator params family n q.2 gs *
                            (gHatHalfProductOutcomeOperator params family n q.2 gs)ᴴ) *
                          rightTensor (ι₁ := ι)
                            ((gHatIdxMeas params family q.1).outcome g) := by
                        rw [← Finset.univ_product_univ, Finset.sum_product]
                  _ = ∑ g : GHatOutcome params,
                        rightTensor (ι₁ := ι) ((gHatIdxMeas params family q.1).outcome g) := by
                        refine Finset.sum_congr rfl ?_
                        intro g _hg
                        rw [← Finset.sum_mul]
                        rw [leftTensor_finset_sum]
                        have hsum :
                            (∑ gs : GHatTupleOutcome params n,
                              let T := gHatHalfProductOutcomeOperator params family n q.2 gs
                              T * Tᴴ) = 1 := by
                          simpa [gHatSandwichFamily] using
                            fromHToG_gHatSandwichFamily_sum_eq_one params family n q.2
                        rw [hsum]
                        simp [leftTensor]
                  _ = 1 := by
                        rw [rightTensor_finset_sum]
                        rw [(gHatIdxMeas params family q.1).sum_eq_total]
                        rw [(gHatIdxMeas params family q.1).total_eq_one]
                        simp [rightTensor]
      have h₁₂_cauchySchwarz :
          |M₁ - M₂| ≤ Real.sqrt (commuteGHalfSandwichError params gamma zeta k) := by
        /- Paper lines 1506--1523.  Rewrite `hM₁_source` and `hM₂_target` as a
        product-index sum over `(g, gs)`, insert a dummy `Unit` outcome so that
        `closenessOfIPAdjoint` applies, use `h₁₂_secondRoot_le_nu4` for the
        commutator square, and discharge the context side condition using the
        bound sketched in `h₁₂_firstRoot_le_one`. -/
        let Aop : Fq params × PointTuple params n →
            GHatOutcome params × GHatTupleOutcome params n →
            MIPStarRE.Quantum.Op (ι × ι) := fun q ogs =>
          let U := (gHatIdxMeas params family q.1).outcome ogs.1
          let T := gHatHalfProductOutcomeOperator params family n q.2 ogs.2
          leftTensor (ι₂ := ι) (U * T)
        let Bop : Fq params × PointTuple params n →
            GHatOutcome params × GHatTupleOutcome params n →
            MIPStarRE.Quantum.Op (ι × ι) := fun q ogs =>
          let U := (gHatIdxMeas params family q.1).outcome ogs.1
          let T := gHatHalfProductOutcomeOperator params family n q.2 ogs.2
          leftTensor (ι₂ := ι) (T * U)
        let Cop : Fq params × PointTuple params n →
            GHatOutcome params × GHatTupleOutcome params n → Unit →
            MIPStarRE.Quantum.Op (ι × ι) := fun q ogs _ =>
          let S := fromHToGRecurrenceWeight params family ℓ
            (prependTypeBit ogs.1.isSome (gHatTupleType ogs.2))
          let U := (gHatIdxMeas params family q.1).outcome ogs.1
          let T := gHatHalfProductOutcomeOperator params family n q.2 ogs.2
          leftTensor (ι₂ := ι) Tᴴ * rightTensor (ι₁ := ι) (S * U)
        have hAB_adj :
            avgOver (uniformDistribution (Fq params × PointTuple params n)) (fun q =>
              qSDDCore ψbi (fun ogs => (Aop q ogs)ᴴ) (fun ogs => (Bop q ogs)ᴴ)) ≤
              commuteGHalfSandwichError params gamma zeta k := by
          simpa [Aop, Bop, fromHToG_leftTensor_conjTranspose, Matrix.conjTranspose_mul,
              fromHToG_gHatIdxMeas_outcome_isHermitian] using h₁₂_secondRoot_le_nu4
        have hC_adj : ∀ q : Fq params × PointTuple params n,
            ∑ ogs : GHatOutcome params × GHatTupleOutcome params n,
              (∑ u : Unit, Cop q ogs u)ᴴ * (∑ u : Unit, Cop q ogs u) ≤ 1 := by
          intro q
          simpa only [Cop] using h₁₂_firstRoot_le_one q
        have hcs := MIPStarRE.LDT.Preliminaries.closenessOfIPAdjoint ψbi hnorm
          (uniformDistribution (Fq params × PointTuple params n))
          (uniformDistribution_weight_sum_le_one (Fq params × PointTuple params n))
          Aop Bop Cop (commuteGHalfSandwichError params gamma zeta k)
          hAB_adj hC_adj
        have hM₁_prod : M₁ =
            avgOver (uniformDistribution (Fq params × PointTuple params n)) fun q =>
              ∑ ogs : GHatOutcome params × GHatTupleOutcome params n,
                let S := fromHToGRecurrenceWeight params family ℓ
                  (prependTypeBit ogs.1.isSome (gHatTupleType ogs.2))
                let U := (gHatIdxMeas params family q.1).outcome ogs.1
                let T := gHatHalfProductOutcomeOperator params family n q.2 ogs.2
                ev ψbi (leftTensor (ι₂ := ι) (U * T) *
                  (leftTensor (ι₂ := ι) Tᴴ * rightTensor (ι₁ := ι) (S * U))) := by
          rw [hM₁_source]
          refine avgOver_congr _ _ _ ?_
          intro q
          exact fromHToG_sum_product (fun g gs =>
            let S := fromHToGRecurrenceWeight params family ℓ
              (prependTypeBit g.isSome (gHatTupleType gs))
            let U := (gHatIdxMeas params family q.1).outcome g
            let T := gHatHalfProductOutcomeOperator params family n q.2 gs
            ev ψbi (leftTensor (ι₂ := ι) (U * T) *
              (leftTensor (ι₂ := ι) Tᴴ * rightTensor (ι₁ := ι) (S * U))))
        have hM₂_prod : M₂ =
            avgOver (uniformDistribution (Fq params × PointTuple params n)) fun q =>
              ∑ ogs : GHatOutcome params × GHatTupleOutcome params n,
                let S := fromHToGRecurrenceWeight params family ℓ
                  (prependTypeBit ogs.1.isSome (gHatTupleType ogs.2))
                let U := (gHatIdxMeas params family q.1).outcome ogs.1
                let T := gHatHalfProductOutcomeOperator params family n q.2 ogs.2
                ev ψbi (leftTensor (ι₂ := ι) (T * U) *
                  (leftTensor (ι₂ := ι) Tᴴ * rightTensor (ι₁ := ι) (S * U))) := by
          rw [hM₂_target]
          refine avgOver_congr _ _ _ ?_
          intro q
          exact fromHToG_sum_product (fun g gs =>
            let S := fromHToGRecurrenceWeight params family ℓ
              (prependTypeBit g.isSome (gHatTupleType gs))
            let U := (gHatIdxMeas params family q.1).outcome g
            let T := gHatHalfProductOutcomeOperator params family n q.2 gs
            ev ψbi (leftTensor (ι₂ := ι) (T * U) *
              (leftTensor (ι₂ := ι) Tᴴ * rightTensor (ι₁ := ι) (S * U))))
        simpa [Aop, Bop, Cop, hM₁_prod, hM₂_prod] using hcs
      exact h₁₂_cauchySchwarz
  have h₂₃ : |M₂ - M₃| ≤ Real.sqrt (commuteGHalfSandwichError params gamma zeta k) := by
    simpa [M₂, M₃] using
      fromHToGAdjacentStageM2M3_paperMove params ψbi hnorm family gamma zeta
        hgamma_nonneg hzeta_nonneg hhalf hstageExact k ℓ
  have hmove₂ : |M₃ - E| ≤ Real.sqrt (2 * zeta) := by
    simpa [M₃, E] using
      fromHToGAdjacentStageM3E_paperMove params ψbi hnorm family gamma zeta
        hfacts hstageExact k ℓ
  have hchain :
      |A - E| ≤ Real.sqrt (2 * zeta) +
          Real.sqrt (commuteGHalfSandwichError params gamma zeta k) +
          Real.sqrt (commuteGHalfSandwichError params gamma zeta k) +
          Real.sqrt (2 * zeta) := by
    have htel := abs_sub_le_four A M₁ M₂ M₃ E
    linarith
  calc
    |fromHToGStageMass params ψbi family k ℓ -
        fromHToGStageMass params ψbi family k (ℓ + 1)| = |A - E| := rfl
    _ ≤ Real.sqrt (2 * zeta) +
          Real.sqrt (commuteGHalfSandwichError params gamma zeta k) +
          Real.sqrt (commuteGHalfSandwichError params gamma zeta k) +
          Real.sqrt (2 * zeta) := hchain
    _ = fromHToGRecurrenceError params gamma zeta k := by
          simp [fromHToGRecurrenceError, Real.sqrt_eq_rpow]
          ring
end MIPStarRE.LDT.Pasting
