-- Prove2me | solution 1 for MIPStarRE.LDT.Pasting.commuteGHalfSandwich_flatChainStep
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T06:47:09.453839+00:00
-- url     : https://prove2.me/submissions/52b43cfe-46d3-4b7e-b5a0-db8d280ce407

/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE, with the
authors' permission. Vendored from https://github.com/LionSR/MIPStarRE
(commit 507e8122, 2026-08-25) by scripts/vendor-lidt.py; do not edit by hand.
Upstream path: MIPStarRE/LDT/Pasting/ComparisonLemmas/CommuteGHalfSandwich/MoveChain/FlatChainStep.lean
-/
/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE, with the
authors' permission. Vendored from https://github.com/LionSR/MIPStarRE
(commit 507e8122, 2026-08-25) by scripts/vendor-lidt.py; do not edit by hand.
Upstream path: MIPStarRE/LDT/Pasting/ComparisonLemmas/CommuteGHalfSandwich/MoveChain/Chain.lean
-/
/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE, with the
authors' permission. Vendored from https://github.com/LionSR/MIPStarRE
(commit 507e8122, 2026-08-25) by scripts/vendor-lidt.py; do not edit by hand.
Upstream path: MIPStarRE/LDT/Pasting/ComparisonLemmas/CommuteGHalfSandwich/MoveChain/FlatChain.lean
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/LIDT/MIPStarRE/LDT/Pasting/ComparisonLemmas/CommuteGHalfSandwich/MoveChain/FlatChainStep.lean (solution of MIPStarRE.LDT.Pasting.commuteGHalfSandwich_flatChainStep);
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
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Range
import Mathlib.Data.Finsupp.Defs
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.CardEmbedding
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.OfMap
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sets
import Mathlib.Data.FunLike.Basic
import Mathlib.Data.FunLike.Embedding
import Mathlib.Data.FunLike.Equiv
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
import Mathlib.Data.Set.Defs
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
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Order.Basic
import Mathlib.Order.Defs.LinearOrder
import Mathlib.Order.Defs.PartialOrder
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
import Mathlib.Probability.Distributions.Uniform
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
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_CommuteGHalfSandwich_MoveChain_Base
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_CommuteGHalfSandwich_MoveChain_Lifting
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_CommuteGHalfSandwich_MoveChain_Chain
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_CommuteGHalfSandwich_MoveChain_FlatChain
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_CommuteGHalfSandwich_MoveChain_BackChain
import Theorems.Thm_MIPStarRE_LDT_CommutativityPoints_sddOpRel_congr_outcome
import Theorems.Thm_MIPStarRE_LDT_Pasting_commuteGHalfSandwich_moveChain_step
import Theorems.Thm_MIPStarRE_LDT_Pasting_commuteGHalfSandwich_postMoveFlatStep
import Theorems.Thm_MIPStarRE_LDT_Pasting_commuteGHalfSandwich_step_commute
import Theorems.Thm_MIPStarRE_LDT_leftTensor_mul_leftTensor
import Theorems.Thm_MIPStarRE_LDT_leftTensor_one

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPStarRE.LDT.Pasting
section
open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder Matrix ComplexOrder
set_option backward.isDefEq.respectTransparency false
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
lemma commuteGHalfSandwich_moveChainFamily_last
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) :
    ∀ r q ogs,
      (commuteGHalfSandwich_moveChainFamily params family r (Fin.last r) q).outcome
        ogs =
        (commuteGHalfSandwich_moveFamily params family r q).outcome ogs
  | 0, q, ogs => by
      simp [commuteGHalfSandwich_moveChainFamily,
        commuteGHalfSandwich_moveSourceFamily, commuteGHalfSandwich_moveFamily,
        gHatHalfProductOutcomeOperator, gHatReverseHalfProductOutcomeOperator]
  | r + 1, q, ogs => by
      simp [commuteGHalfSandwich_moveChainFamily]
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
lemma commuteGHalfSandwich_postMoveFlatFamily_one_active
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (r : ℕ)
    (q : MoveQ params (r + 1))
    (ogs : MoveO params (r + 1)) :
    (commuteGHalfSandwich_postMoveFlatFamily params family (r + 1)
      ⟨1, by
        rw [commuteGHalfSandwich_postMoveFlatLength_eq]
        omega⟩ q).outcome
          ogs =
      (commuteGHalfSandwich_commuteFamily params family (r + 1) q).outcome ogs := by
  simp [commuteGHalfSandwich_postMoveFlatFamily]
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
    (params : Parameters) [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι)
    (gamma zeta : Error)
    (hsc : SDDRel ψbi
      (uniformDistribution (SliceQuestion params))
      (gHatSelfConsistencyLeftFamily params family)
      (gHatSelfConsistencyRightFamily params family)
      (gHatSelfConsistencyError zeta))
    (hcom : SDDOpRel ψbi
      (uniformDistribution (SlicePairQuestion params))
      (gHatPairProductLeft params family)
      (gHatPairProductRight params family)
      (gHatCommutationError params gamma zeta)) :
    ∀ r (i : Fin (commuteGHalfSandwich_flatChainLength r)),
      SDDOpRel ψbi
        (uniformDistribution (MoveQ params r))
        ((commuteGHalfSandwich_flatChainFamily params family r) i.castSucc)
        ((commuteGHalfSandwich_flatChainFamily params family r) i.succ)
        ((commuteGHalfSandwich_flatChainError params gamma zeta r) i)
  | 0, i => by
      fin_cases i
      let izero : Fin (commuteGHalfSandwich_postMoveFlatLength 0) :=
        ⟨0, by simp [commuteGHalfSandwich_postMoveFlatLength]⟩
      have hstep :=
        commuteGHalfSandwich_postMoveFlatStep params ψbi family gamma zeta hsc hcom 0
          izero
      have htransport :
          SDDOpRel ψbi (uniformDistribution (MoveQ params 0))
            (commuteGHalfSandwich_moveSourceFamily params family 0)
            (commuteGHalfSandwich_recursiveTargetFamily params family 0)
            (commuteGHalfSandwich_postMoveFlatError params gamma zeta 0 izero) :=
        CommutativityPoints.sddOpRel_congr_outcome ψbi
          (uniformDistribution (MoveQ params 0))
          (commuteGHalfSandwich_moveFamily params family 0)
          (commuteGHalfSandwich_recursiveTargetFamily params family 0)
          (commuteGHalfSandwich_moveSourceFamily params family 0)
          (commuteGHalfSandwich_recursiveTargetFamily params family 0)
          (commuteGHalfSandwich_postMoveFlatError params gamma zeta 0 izero)
          (fun q ogs => by
            simp [commuteGHalfSandwich_moveSourceFamily, commuteGHalfSandwich_moveFamily,
              gHatHalfProductOutcomeOperator, gHatReverseHalfProductOutcomeOperator,
              leftTensor_one, leftTensor_mul_leftTensor, mul_assoc])
          (fun _ _ => rfl)
          hstep
      -- Vendoring compile fix (Lean v4.33): `simp` must also unfold the chain length to
      -- decide the index conditions.
      simpa [commuteGHalfSandwich_flatChainFamily, commuteGHalfSandwich_flatChainError,
        commuteGHalfSandwich_flatChainLength,
        commuteGHalfSandwich_postMoveFlatLength, commuteGHalfSandwich_postMoveFlatFamily,
        commuteGHalfSandwich_moveChainFamily, izero] using
        htransport
  | r + 1, i => by
      by_cases hi : i.1 < r + 1
      · let imove : Fin (r + 1) := ⟨i.1, hi⟩
        have hmove := commuteGHalfSandwich_moveChain_step params ψbi family zeta hsc (r + 1) imove
        have hsrc_eq :
            ∀ q ogs,
              ((commuteGHalfSandwich_flatChainFamily params family (r + 1))
                  i.castSucc q).outcome
                ogs =
                ((commuteGHalfSandwich_moveChainFamily params family (r + 1))
                  imove.castSucc q).outcome ogs := by
          intro q ogs
          have hsrc_le : i.1 ≤ r + 1 := by omega
          conv_lhs => simp [commuteGHalfSandwich_flatChainFamily, hsrc_le]
          try rfl -- vendoring compile fix (Lean v4.33): the previous step may close the goal
        have htgt_eq :
            ∀ q ogs,
              ((commuteGHalfSandwich_flatChainFamily params family (r + 1))
                  i.succ q).outcome
                ogs =
                ((commuteGHalfSandwich_moveChainFamily params family (r + 1))
                  imove.succ q).outcome ogs := by
          intro q ogs
          have htgt_le : i.1 ≤ r := by omega
          conv_lhs => simp [commuteGHalfSandwich_flatChainFamily, htgt_le]
          try rfl -- vendoring compile fix (Lean v4.33): the previous step may close the goal
        simpa [commuteGHalfSandwich_flatChainError, hi] using
          (CommutativityPoints.sddOpRel_congr_outcome ψbi
            (uniformDistribution (SliceQuestion params × SliceQuestion params ×
                PointTuple params (r + 1)))
            ((commuteGHalfSandwich_moveChainFamily params family (r + 1)) imove.castSucc)
            ((commuteGHalfSandwich_moveChainFamily params family (r + 1)) imove.succ)
            ((commuteGHalfSandwich_flatChainFamily params family (r + 1)) i.castSucc)
            ((commuteGHalfSandwich_flatChainFamily params family (r + 1)) i.succ)
            (gHatSelfConsistencyError zeta)
            (fun q ogs => (hsrc_eq q ogs).symm)
            (fun q ogs => (htgt_eq q ogs).symm)
            hmove)
      · have hge : r + 1 ≤ i.1 := by omega
        by_cases hboundary : i.1 = r + 1
        · have hcomm1 := commuteGHalfSandwich_step_commute
            params ψbi family gamma zeta (r + 1) hcom
          have hsrc_eq :
              ∀ q ogs,
                ((commuteGHalfSandwich_flatChainFamily params family (r + 1))
                  i.castSucc q).outcome
                  ogs =
                  (commuteGHalfSandwich_moveFamily params family (r + 1) q).outcome ogs := by
            intro q ogs
            have hsrc_le : i.1 ≤ r + 1 := by omega
            conv_lhs => simp [commuteGHalfSandwich_flatChainFamily, hsrc_le]
            simpa [hboundary, Fin.last] using
              commuteGHalfSandwich_moveChainFamily_last params family (r + 1) q ogs
          have htgt_eq :
              ∀ q ogs,
                ((commuteGHalfSandwich_flatChainFamily params family (r + 1))
                  i.succ q).outcome
                  ogs =
                  (commuteGHalfSandwich_commuteFamily params family (r + 1) q).outcome ogs := by
            intro q ogs
            have htgt_not : ¬ i.1 ≤ r := by omega
            have hone_lt : 1 < commuteGHalfSandwich_postMoveFlatLength (r + 1) + 1 := by
              rw [commuteGHalfSandwich_postMoveFlatLength_eq]
              omega
            calc
              ((commuteGHalfSandwich_flatChainFamily params family (r + 1))
                  i.succ q).outcome ogs
                = (commuteGHalfSandwich_postMoveFlatFamily params family (r + 1)
                    ⟨i.1 - r, by
                      simpa [hboundary] using hone_lt⟩ q).outcome ogs := by
                        conv_lhs => simp [commuteGHalfSandwich_flatChainFamily, htgt_not]
              _ = (commuteGHalfSandwich_postMoveFlatFamily params family (r + 1)
                    ⟨1, by exact hone_lt⟩ q).outcome ogs := by
                    have hone :
                        (⟨i.1 - r, by simpa [hboundary] using hone_lt⟩ :
                          Fin (commuteGHalfSandwich_postMoveFlatLength (r + 1) + 1)) =
                          ⟨1, by exact hone_lt⟩ := by
                      apply Fin.ext
                      simp [hboundary]
                    exact congrArg
                      (fun idx => ((commuteGHalfSandwich_postMoveFlatFamily params family (r + 1))
                  idx q).outcome ogs)
                      hone
                  _ = (commuteGHalfSandwich_commuteFamily params family (r + 1) q).outcome
                    ogs := by
                    exact
                      commuteGHalfSandwich_postMoveFlatFamily_one_active
                        params family (r := r) q ogs
          simpa [commuteGHalfSandwich_flatChainError, hi, hboundary,
            commuteGHalfSandwich_postMoveFlatError] using
            (CommutativityPoints.sddOpRel_congr_outcome ψbi
              (uniformDistribution (SliceQuestion params × SliceQuestion params ×
                  PointTuple params (r + 1)))
              (commuteGHalfSandwich_moveFamily params family (r + 1))
              (commuteGHalfSandwich_commuteFamily params family (r + 1))
              ((commuteGHalfSandwich_flatChainFamily params family (r + 1)) i.castSucc)
              ((commuteGHalfSandwich_flatChainFamily params family (r + 1)) i.succ)
              (gHatCommutationError params gamma zeta)
              (fun q ogs => (hsrc_eq q ogs).symm)
              (fun q ogs => (htgt_eq q ogs).symm)
              hcomm1)
        · let j : Fin (commuteGHalfSandwich_postMoveFlatLength (r + 1)) :=
            ⟨i.1 - (r + 1), by
              have hi_lt : i.1 < (r + 1) + commuteGHalfSandwich_postMoveFlatLength (r + 1) := by
                exact i.2
              omega⟩
          have hsmall := commuteGHalfSandwich_postMoveFlatStep params ψbi family gamma zeta hsc
              hcom (r + 1) j
          have hsrc_eq :
              ∀ q ogs,
                ((commuteGHalfSandwich_flatChainFamily params family (r + 1))
                  i.castSucc q).outcome
                  ogs =
                  ((commuteGHalfSandwich_postMoveFlatFamily params family (r + 1))
                  j.castSucc q).outcome ogs := by
            intro q ogs
            have hsrc_not : ¬ i.1 ≤ r + 1 := by omega
            have hj_castSucc :
                (⟨i.1 - (r + 1), by
                    exact Nat.lt_trans j.2 (Nat.lt_succ_self _)⟩ :
                  Fin (commuteGHalfSandwich_postMoveFlatLength (r + 1) + 1)) = j.castSucc := by
              apply Fin.ext
              simp [j]
            conv_lhs => simp [commuteGHalfSandwich_flatChainFamily, hsrc_not]
            exact congrArg
              (fun idx => ((commuteGHalfSandwich_postMoveFlatFamily params family (r + 1))
                  idx q).outcome ogs)
              hj_castSucc
          have htgt_eq :
              ∀ q ogs,
                ((commuteGHalfSandwich_flatChainFamily params family (r + 1))
                  i.succ q).outcome
                  ogs =
                  ((commuteGHalfSandwich_postMoveFlatFamily params family (r + 1))
                    j.succ q).outcome ogs := by
            intro q ogs
            have htgt_not : ¬ i.1 ≤ r := by omega
            have hge2 : r + 2 ≤ i.1 := by omega
            have hval : i.1 - r = (i.1 - (r + 1)) + 1 := by
              omega
            have hj_succ :
                (⟨i.1 - r, by
                    rw [hval]
                    simpa [j] using j.succ.is_lt⟩ :
                  Fin (commuteGHalfSandwich_postMoveFlatLength (r + 1) + 1)) = j.succ := by
              apply Fin.ext
              simp [j, hval]
            conv_lhs => simp [commuteGHalfSandwich_flatChainFamily, htgt_not]
            exact congrArg
              (fun idx => ((commuteGHalfSandwich_postMoveFlatFamily params family (r + 1))
                  idx q).outcome ogs)
              hj_succ
          simpa [commuteGHalfSandwich_flatChainError, hi, hboundary, j] using
            (CommutativityPoints.sddOpRel_congr_outcome ψbi
              (uniformDistribution (SliceQuestion params × SliceQuestion params ×
                  PointTuple params (r + 1)))
              ((commuteGHalfSandwich_postMoveFlatFamily params family (r + 1)) j.castSucc)
              ((commuteGHalfSandwich_postMoveFlatFamily params family (r + 1)) j.succ)
              ((commuteGHalfSandwich_flatChainFamily params family (r + 1)) i.castSucc)
              ((commuteGHalfSandwich_flatChainFamily params family (r + 1)) i.succ)
              ((commuteGHalfSandwich_postMoveFlatError params gamma zeta (r + 1)) j)
              (fun q ogs => (hsrc_eq q ogs).symm)
              (fun q ogs => (htgt_eq q ogs).symm)
              hsmall)
end MIPStarRE.LDT.Pasting
