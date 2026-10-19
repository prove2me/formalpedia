-- Prove2me | solution 1 for MIPStarRE.LDT.Pasting.commutingWithGIncomplete_ofComplete
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T05:42:05.145069+00:00
-- url     : https://prove2.me/submissions/ad8b2d3e-ed86-49d5-ac76-18d02a1a7df4

/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE, with the
authors' permission. Vendored from https://github.com/LionSR/MIPStarRE
(commit 507e8122, 2026-08-25) by scripts/vendor-lidt.py; do not edit by hand.
Upstream path: MIPStarRE/LDT/Pasting/CommutingWithG/Incomplete.lean
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/LIDT/MIPStarRE/LDT/Pasting/CommutingWithG/Incomplete.lean (solution of MIPStarRE.LDT.Pasting.commutingWithGIncomplete_ofComplete);
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
import Mathlib.Algebra.Order.Nonneg.Basic
import Mathlib.Algebra.Order.Nonneg.Module
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Ring.Unbundled.Basic
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.Analysis.SpecialFunctions.Pow.Real
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
import Theorems.Thm_MIPStarRE_LDT_SubMeas_total_nonneg
import Theorems.Thm_MIPStarRE_LDT_avgOver_congr

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
    (family : IdxPolyFamily params ι)
    (gamma zeta : Error)
    (hcomm : CommutingWithGCompleteStatement params ψbi family gamma zeta) :
    CommutingWithGIncompleteStatement params ψbi family gamma zeta := by
  refine {
    pointWithIncompletePartCommutation := ?_
    incompletePartCommutation := ?_
  }
  · rcases hcomm.pointWithCompletePartCommutation with ⟨hcomplete_bound⟩
    refine ⟨?_⟩
    calc
      sddErrorOp ψbi
          (uniformDistribution (SlicePairQuestion params))
          (incompletePartPointProductLeft params family)
          (incompletePartPointProductRight params family)
        =
          sddErrorOp ψbi
            (uniformDistribution (SlicePairQuestion params))
            (completePartPointProductLeft params family)
            (completePartPointProductRight params family) := by
              unfold sddErrorOp
              apply avgOver_congr
              intro q
              unfold qSDDOp qSDDCore
              apply Finset.sum_congr rfl
              intro g _hg
              have hdiff :
                  (incompletePartPointProductLeft params family q).outcome g -
                      (incompletePartPointProductRight params family q).outcome g =
                    -((completePartPointProductLeft params family q).outcome g -
                      (completePartPointProductRight params family q).outcome g) := by
                let A : MIPStarRE.Quantum.Op ι := (family.meas q.1).outcome g
                let B : MIPStarRE.Quantum.Op ι :=
                  (postprocess ((family.meas q.2).toSubMeas) (fun _ => ())).total
                have hinner : A * (1 - B) - (1 - B) * A = -(A * B - B * A) := by
                  dsimp [A, B]
                  noncomm_ring
                ext i j
                rcases i with ⟨i₁, i₂⟩
                rcases j with ⟨j₁, j₂⟩
                by_cases h₂ : i₂ = j₂
                · have hentry := congrArg (fun X : MIPStarRE.Quantum.Op ι => X i₁ j₁) hinner
                  simpa [incompletePartPointProductLeft, incompletePartPointProductRight,
                    completePartPointProductLeft, completePartPointProductRight,
                    OpFamily.leftPlacedOpFamily, multiplyByTotalOnRight,
                    multiplyByTotalOnLeft, incompletePartSubMeas, completePartSubMeas,
                    sub_eq_add_neg, leftTensor, A, B, h₂] using hentry
                · simp [incompletePartPointProductLeft, incompletePartPointProductRight,
                    completePartPointProductLeft, completePartPointProductRight,
                    OpFamily.leftPlacedOpFamily, multiplyByTotalOnRight,
                    multiplyByTotalOnLeft, incompletePartSubMeas, completePartSubMeas,
                    sub_eq_add_neg, leftTensor, h₂]
              rw [hdiff]
              have hswap :
                  (((completePartPointProductRight params family q).outcome g)ᴴ -
                        ((completePartPointProductLeft params family q).outcome g)ᴴ) *
                      ((completePartPointProductRight params family q).outcome g -
                        (completePartPointProductLeft params family q).outcome g) =
                    (((completePartPointProductLeft params family q).outcome g)ᴴ -
                        ((completePartPointProductRight params family q).outcome g)ᴴ) *
                      ((completePartPointProductLeft params family q).outcome g -
                        (completePartPointProductRight params family q).outcome g) := by
                noncomm_ring
              simpa [sub_eq_add_neg] using congrArg (ev ψbi) hswap
      _ ≤ commutingWithGIncompleteError params gamma zeta := by
          simpa [commutingWithGIncompleteError] using hcomplete_bound
  · rcases hcomm.completePartCommutation with ⟨hcomplete_bound⟩
    refine ⟨?_⟩
    calc
      sddErrorOp ψbi
          (uniformDistribution (SlicePairQuestion params))
          (incompletePartTotalProductLeft params family)
          (incompletePartTotalProductRight params family)
        =
          sddErrorOp ψbi
            (uniformDistribution (SlicePairQuestion params))
            (completePartTotalProductLeft params family)
            (completePartTotalProductRight params family) := by
              unfold sddErrorOp
              apply avgOver_congr
              intro q
              unfold qSDDOp qSDDCore
              apply Finset.sum_congr rfl
              intro u _hu
              cases u
              have hq1 :
                  (postprocess ((family.meas q.1).toSubMeas) (fun _ => ())).outcome () =
                    (family.meas q.1).total := by
                calc
                  (postprocess ((family.meas q.1).toSubMeas) (fun _ => ())).outcome () =
                      (completePartSubMeas params family q.1).total := by
                    exact completePartSubMeas_outcome_unit
                      (params := params) (family := family) q.1
                  _ = (family.meas q.1).total := by
                    exact completePartSubMeas_total
                      (params := params) (family := family) q.1
              have hq2 :
                  (postprocess ((family.meas q.2).toSubMeas) (fun _ => ())).outcome () =
                    (family.meas q.2).total := by
                calc
                  (postprocess ((family.meas q.2).toSubMeas) (fun _ => ())).outcome () =
                      (completePartSubMeas params family q.2).total := by
                    exact completePartSubMeas_outcome_unit
                      (params := params) (family := family) q.2
                  _ = (family.meas q.2).total := by
                    exact completePartSubMeas_total
                      (params := params) (family := family) q.2
              have hdiff :
                  (incompletePartTotalProductLeft params family q).outcome () -
                      (incompletePartTotalProductRight params family q).outcome () =
                    (completePartTotalProductLeft params family q).outcome () -
                      (completePartTotalProductRight params family q).outcome () := by
                let A : MIPStarRE.Quantum.Op ι :=
                  (postprocess ((family.meas q.1).toSubMeas) (fun _ => ())).total
                let B : MIPStarRE.Quantum.Op ι :=
                  (postprocess ((family.meas q.2).toSubMeas) (fun _ => ())).total
                have hinner : (1 - A) * (1 - B) - (1 - B) * (1 - A) = A * B - B * A := by
                  dsimp [A, B]
                  noncomm_ring
                have hA : A = (family.meas q.1).total := by
                  dsimp [A]
                  exact completePartSubMeas_total
                    (params := params) (family := family) q.1
                have hB : B = (family.meas q.2).total := by
                  dsimp [B]
                  exact completePartSubMeas_total
                    (params := params) (family := family) q.2
                ext i j
                rcases i with ⟨i₁, i₂⟩
                rcases j with ⟨j₁, j₂⟩
                by_cases h₂ : i₂ = j₂
                · have hentry := congrArg (fun X : MIPStarRE.Quantum.Op ι => X i₁ j₁) hinner
                  simpa [incompletePartTotalProductLeft, incompletePartTotalProductRight,
                    completePartTotalProductLeft, completePartTotalProductRight,
                    OpFamily.leftPlacedOpFamily, multiplyByTotalOnRight,
                    multiplyByTotalOnLeft, incompletePartSubMeas, completePartSubMeas,
                    sub_eq_add_neg, leftTensor, A, B, hA, hB, hq1, hq2, h₂,
                    (family.meas q.1).sum_eq_total,
                    (family.meas q.2).sum_eq_total] using hentry
                · simp [incompletePartTotalProductLeft, incompletePartTotalProductRight,
                    completePartTotalProductLeft, completePartTotalProductRight,
                    OpFamily.leftPlacedOpFamily, multiplyByTotalOnRight,
                    multiplyByTotalOnLeft, incompletePartSubMeas, completePartSubMeas,
                    sub_eq_add_neg, leftTensor, h₂, (family.meas q.1).sum_eq_total]
              rw [hdiff]
      _ ≤ commutingWithGIncompleteError params gamma zeta := by
          simpa [commutingWithGIncompleteError] using hcomplete_bound
end MIPStarRE.LDT.Pasting
