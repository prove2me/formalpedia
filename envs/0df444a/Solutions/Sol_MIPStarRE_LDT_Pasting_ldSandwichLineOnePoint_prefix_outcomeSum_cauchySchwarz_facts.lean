-- Prove2me | solution 1 for MIPStarRE.LDT.Pasting.ldSandwichLineOnePoint_prefix_outcomeSum_cauchySchwarz_facts
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T06:41:52.750599+00:00
-- url     : https://prove2.me/submissions/30f17ac8-147f-4d01-a120-f423419361b0

/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE, with the
authors' permission. Vendored from https://github.com/LionSR/MIPStarRE
(commit 507e8122, 2026-08-25) by scripts/vendor-lidt.py; do not edit by hand.
Upstream path: MIPStarRE/LDT/Pasting/ComparisonLemmas/LdSandwichLineOnePoint/CauchySchwarz.lean
-/
/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE, with the
authors' permission. Vendored from https://github.com/LionSR/MIPStarRE
(commit 507e8122, 2026-08-25) by scripts/vendor-lidt.py; do not edit by hand.
Upstream path: MIPStarRE/LDT/Pasting/ComparisonLemmas/LdSandwichLineOnePoint/OutcomeLemmas.lean
-/
/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE, with the
authors' permission. Vendored from https://github.com/LionSR/MIPStarRE
(commit 507e8122, 2026-08-25) by scripts/vendor-lidt.py; do not edit by hand.
Upstream path: MIPStarRE/LDT/Pasting/ComparisonLemmas/LdSandwichLineOnePoint/CSSetup.lean
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/LIDT/MIPStarRE/LDT/Pasting/ComparisonLemmas/LdSandwichLineOnePoint/CauchySchwarz.lean (solution of MIPStarRE.LDT.Pasting.ldSandwichLineOnePoint_prefix_outcomeSum_cauchySchwarz_facts);
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
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_LdSandwichLineOnePoint_EndpointEquivs
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Pasting_Core_LdGbcon
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_LdSandwichLineOnePoint_Endpoint
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_LdSandwichLineOnePoint_PrefixMoved
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_LdSandwichLineOnePoint_CSSetup
import Theorems.Thm_MIPStarRE_LDT_Measurement_outcome_hermitian
import Theorems.Thm_MIPStarRE_LDT_Pasting_gHatHalfProductTotalOperator_eq_one
import Theorems.Thm_MIPStarRE_LDT_Pasting_gHatIdxMeas_proj
import Theorems.Thm_MIPStarRE_LDT_Pasting_gHatSandwichFamily_restrict_eval_outcome_some
import Theorems.Thm_MIPStarRE_LDT_SubMeas_outcome_hermitian
import Theorems.Thm_MIPStarRE_LDT_SubMeas_outcome_le_one
import Theorems.Thm_MIPStarRE_LDT_avgOver_congr
import Theorems.Thm_MIPStarRE_LDT_ev_sum
import Theorems.Thm_MIPStarRE_LDT_ev_zero
import Theorems.Thm_MIPStarRE_LDT_leftTensor_finset_sum
import Theorems.Thm_MIPStarRE_LDT_leftTensor_mul_opTensor
import Theorems.Thm_MIPStarRE_LDT_opTensor_le_leftTensor
import Theorems.Thm_MIPStarRE_LDT_opTensor_mul
import Theorems.Thm_MIPStarRE_LDT_opTensor_mul_leftTensor
import Theorems.Thm_MIPStarRE_LDT_opTensor_sum_left_univ
import Theorems.Thm_MIPStarRE_Quantum_sq_le_self

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
/-- Outcome expansion for the original-order prefix family at a concrete field value. -/
lemma ldSandwichLineOnePointPrefixOriginalFamily_outcome_some
    (params : Parameters)
    [FieldModel params.q]
    (family : IdxPolyFamily params ι)
    {k i : ℕ} (hi : i < k)
    (q : SandwichedLineQuestion params k)
    (a : Fq params) :
    (ldSandwichLineOnePointPrefixOriginalFamily params family hi q).outcome (some a) =
      ∑ gs : GHatTupleOutcome params (i + 1),
        if Option.map (fun g : Polynomial params => g q.1)
            (gs ⟨i, Nat.lt_succ_self i⟩) = some a then
          let half := gHatHalfProductOutcomeOperator params family (i + 1)
            (fun j => q.2 ⟨j.1, by omega⟩) gs
          half * halfᴴ
        else
          0 := by
  simpa [ldSandwichLineOnePointPrefixOriginalFamily] using
    gHatSandwichFamily_restrict_eval_outcome_some
      params family (fun j => q.2 ⟨j.1, by omega⟩)
      ⟨i, Nat.lt_succ_self i⟩ q.1 a
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
/-- Outcome expansion for the selected-first prefix family at a concrete field value. -/
lemma ldSandwichLineOnePointPrefixMovedFamily_outcome_some
    (params : Parameters)
    [FieldModel params.q]
    (family : IdxPolyFamily params ι)
    {k i : ℕ} (hi : i < k)
    (q : SandwichedLineQuestion params k)
    (a : Fq params) :
    (ldSandwichLineOnePointPrefixMovedFamily params family hi q).outcome (some a) =
      ∑ gs : GHatTupleOutcome params (i + 1),
        if Option.map (fun g : Polynomial params => g q.1) (gs 0) = some a then
          let xsTail : PointTuple params i := fun j => q.2 ⟨j.1, by omega⟩
          let xs : PointTuple params (i + 1) := Fin.cons (q.2 ⟨i, hi⟩) xsTail
          let half := gHatHalfProductOutcomeOperator params family (i + 1) xs gs
          half * halfᴴ
        else
          0 := by
  simpa [ldSandwichLineOnePointPrefixMovedFamily] using
    gHatSandwichFamily_restrict_eval_outcome_some
      params family (Fin.cons (q.2 ⟨i, hi⟩) (fun j => q.2 ⟨j.1, by omega⟩))
      0 q.1 a
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
/-- The adjoint-oriented estimate for the paper's `eq:add-in-the-bot` term.

The generic `closenessOfIP*` applications need the adjoint-oriented
$D D^\dagger$ square-distance term that appears in `ld-pasting.tex:980--985`
and is reused at lines `1005--1010`. -/
lemma ldSandwichLineOnePoint_prefix_outcomeSum_cauchySchwarz_adjointRawCore
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (gamma zeta : Error)
    {k i : ℕ} (hi : i < k) (_hi0 : i ≠ 0)
    (facts : LdSandwichLineOnePointAdjointRawCoreBound params strategy family gamma zeta hi) :
    avgOver (uniformDistribution (SandwichedLineQuestion params k))
      (fun q => qSDDCore strategy.state
        (fun gs : GHatTupleOutcome params (i + 1) =>
          (ldSandwichLineOnePointCS_Aord params family hi q gs)ᴴ)
        (fun gs : GHatTupleOutcome params (i + 1) =>
          (ldSandwichLineOnePointCS_Arot params family hi q gs)ᴴ)) ≤
      commuteGHalfSandwichError params gamma zeta (i + 1) := by
  exact facts.bound
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
    (family : IdxPolyFamily params ι)
    (gamma zeta : Error)
    {k i : ℕ} (hi : i < k) (hi0 : i ≠ 0)
    (facts : LdSandwichLineOnePointAdjointRawCoreBound params strategy family gamma zeta hi) :
    LdSandwichLineOnePointCSFacts params strategy family gamma zeta hi := by
  refine ⟨
    ldSandwichLineOnePoint_prefix_outcomeSum_cauchySchwarz_adjointRawCore
      params strategy family gamma zeta hi hi0 facts,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro q
    classical
    calc
      ∑ gs : GHatTupleOutcome params (i + 1),
          (∑ u : Unit, ldSandwichLineOnePointCS_Cfirst params strategy family hi q gs u)ᴴ *
            (∑ u : Unit, ldSandwichLineOnePointCS_Cfirst params strategy family hi q gs u)
          ≤ ∑ gs : GHatTupleOutcome params (i + 1),
              leftTensor (ι₂ := ι)
                (ldSandwichLineOnePointCS_orderedHalf params family hi q gs *
                  (ldSandwichLineOnePointCS_orderedHalf params family hi q gs)ᴴ) := by
            refine Finset.sum_le_sum ?_
            intro gs _hgs
            let O : MIPStarRE.Quantum.Op ι :=
              ldSandwichLineOnePointCS_orderedHalf params family hi q gs
            let R : MIPStarRE.Quantum.Op ι :=
              ldSandwichLineOnePointCS_rightComplement params strategy family q gs
            have hRle : Rᴴ * R ≤ 1 := by
              dsimp [R, ldSandwichLineOnePointCS_rightComplement]
              split
              · simp
              · rename_i a _ha
                let B : MIPStarRE.Quantum.Op ι :=
                  ((ldSandwichLineOnePointRightFamily params strategy family k i) q).outcome
                    (some a)
                have hBpos : 0 ≤ B := by
                  simpa [B] using
                    ((ldSandwichLineOnePointRightFamily params strategy family k i) q).outcome_pos
                      (some a)
                have hBle : B ≤ 1 := by
                  simpa [B] using
                    SubMeas.outcome_le_one
                      ((ldSandwichLineOnePointRightFamily params strategy family k i) q)
                      (some a)
                have hRpos : 0 ≤ (1 : MIPStarRE.Quantum.Op ι) - B := sub_nonneg.mpr hBle
                have hRle_one : (1 : MIPStarRE.Quantum.Op ι) - B ≤ 1 := by
                  simpa [sub_eq_add_neg] using sub_le_self (1 : MIPStarRE.Quantum.Op ι) hBpos
                have hRherm : ((1 : MIPStarRE.Quantum.Op ι) - B)ᴴ = 1 - B := by
                  simp [B, SubMeas.outcome_hermitian]
                calc
                  ((1 : MIPStarRE.Quantum.Op ι) - B)ᴴ * (1 - B)
                      = (1 - B) * (1 - B) := by rw [hRherm]
                  _ ≤ 1 - B := MIPStarRE.Quantum.sq_le_self hRpos hRle_one
                  _ ≤ 1 := hRle_one
            have hOpos : 0 ≤ O * Oᴴ := by
              simpa [O] using (Matrix.posSemidef_self_mul_conjTranspose O).nonneg
            calc
              (∑ u : Unit, ldSandwichLineOnePointCS_Cfirst params strategy family hi q gs u)ᴴ *
                  (∑ u : Unit, ldSandwichLineOnePointCS_Cfirst params strategy family hi q gs u)
                  = opTensor (O * Oᴴ) (Rᴴ * R) := by
                    simp [O, R, ldSandwichLineOnePointCS_Cfirst, opTensor_mul,
                      conjTranspose_opTensor]
              _ ≤ leftTensor (ι₂ := ι) (O * Oᴴ) := opTensor_le_leftTensor hOpos hRle
              _ = leftTensor (ι₂ := ι)
                    (ldSandwichLineOnePointCS_orderedHalf params family hi q gs *
                      (ldSandwichLineOnePointCS_orderedHalf params family hi q gs)ᴴ) := by
                    try rfl -- vendoring compile fix (Lean v4.33): the previous step may close the goal
      _ = 1 := by
            calc
              ∑ gs : GHatTupleOutcome params (i + 1),
                  leftTensor (ι₂ := ι)
                    (ldSandwichLineOnePointCS_orderedHalf params family hi q gs *
                      (ldSandwichLineOnePointCS_orderedHalf params family hi q gs)ᴴ)
                  = leftTensor (ι₂ := ι)
                      (∑ gs : GHatTupleOutcome params (i + 1),
                        ldSandwichLineOnePointCS_orderedHalf params family hi q gs *
                          (ldSandwichLineOnePointCS_orderedHalf params family hi q gs)ᴴ) := by
                    rw [← leftTensor_finset_sum (ι₂ := ι) Finset.univ]
              _ = leftTensor (ι₂ := ι) (1 : MIPStarRE.Quantum.Op ι) := by
                    congr 1
                    have hsum :=
                      (gHatSandwichFamily params family (i + 1)
                        (fun j => q.2 ⟨j.1, by omega⟩)).sum_eq_total
                    simpa [gHatSandwichFamily, ldSandwichLineOnePointCS_orderedHalf,
                      gHatHalfProductTotalOperator_eq_one] using hsum
              _ = 1 := by simp [leftTensor]
  · intro q
    classical
    calc
      ∑ gs : GHatTupleOutcome params (i + 1),
          (∑ u : Unit, ldSandwichLineOnePointCS_Csecond params strategy family hi q gs u) *
            (∑ u : Unit, ldSandwichLineOnePointCS_Csecond params strategy family hi q gs u)ᴴ
          ≤ ∑ gs : GHatTupleOutcome params (i + 1),
              leftTensor (ι₂ := ι)
                (ldSandwichLineOnePointCS_rotatedHalf params family hi q gs *
                  (ldSandwichLineOnePointCS_rotatedHalf params family hi q gs)ᴴ) := by
            refine Finset.sum_le_sum ?_
            intro gs _hgs
            let O : MIPStarRE.Quantum.Op ι :=
              ldSandwichLineOnePointCS_rotatedHalf params family hi q gs
            let R : MIPStarRE.Quantum.Op ι :=
              ldSandwichLineOnePointCS_rightComplement params strategy family q gs
            have hRle : R * Rᴴ ≤ 1 := by
              dsimp [R, ldSandwichLineOnePointCS_rightComplement]
              split
              · simp
              · rename_i a _ha
                let B : MIPStarRE.Quantum.Op ι :=
                  ((ldSandwichLineOnePointRightFamily params strategy family k i) q).outcome
                    (some a)
                have hBpos : 0 ≤ B := by
                  simpa [B] using
                    ((ldSandwichLineOnePointRightFamily params strategy family k i) q).outcome_pos
                      (some a)
                have hBle : B ≤ 1 := by
                  simpa [B] using
                    SubMeas.outcome_le_one
                      ((ldSandwichLineOnePointRightFamily params strategy family k i) q)
                      (some a)
                have hRpos : 0 ≤ (1 : MIPStarRE.Quantum.Op ι) - B := sub_nonneg.mpr hBle
                have hRle_one : (1 : MIPStarRE.Quantum.Op ι) - B ≤ 1 := by
                  simpa [sub_eq_add_neg] using sub_le_self (1 : MIPStarRE.Quantum.Op ι) hBpos
                have hRherm : ((1 : MIPStarRE.Quantum.Op ι) - B)ᴴ = 1 - B := by
                  simp [B, SubMeas.outcome_hermitian]
                calc
                  ((1 : MIPStarRE.Quantum.Op ι) - B) * ((1 : MIPStarRE.Quantum.Op ι) - B)ᴴ
                      = (1 - B) * (1 - B) := by rw [hRherm]
                  _ ≤ 1 - B := MIPStarRE.Quantum.sq_le_self hRpos hRle_one
                  _ ≤ 1 := hRle_one
            have hOpos : 0 ≤ O * Oᴴ := by
              simpa [O] using (Matrix.posSemidef_self_mul_conjTranspose O).nonneg
            calc
              (∑ u : Unit, ldSandwichLineOnePointCS_Csecond params strategy family hi q gs u) *
                  (∑ u : Unit,
                    ldSandwichLineOnePointCS_Csecond params strategy family hi q gs u)ᴴ
                  = opTensor (O * Oᴴ) (R * Rᴴ) := by
                    simp [O, R, ldSandwichLineOnePointCS_Csecond, opTensor_mul,
                      conjTranspose_opTensor]
              _ ≤ leftTensor (ι₂ := ι) (O * Oᴴ) := opTensor_le_leftTensor hOpos hRle
              _ = leftTensor (ι₂ := ι)
                    (ldSandwichLineOnePointCS_rotatedHalf params family hi q gs *
                      (ldSandwichLineOnePointCS_rotatedHalf params family hi q gs)ᴴ) := by
                    try rfl -- vendoring compile fix (Lean v4.33): the previous step may close the goal
      _ = 1 := by
            calc
              ∑ gs : GHatTupleOutcome params (i + 1),
                  leftTensor (ι₂ := ι)
                    (ldSandwichLineOnePointCS_rotatedHalf params family hi q gs *
                      (ldSandwichLineOnePointCS_rotatedHalf params family hi q gs)ᴴ)
                  = leftTensor (ι₂ := ι)
                      (∑ gs : GHatTupleOutcome params (i + 1),
                        ldSandwichLineOnePointCS_rotatedHalf params family hi q gs *
                          (ldSandwichLineOnePointCS_rotatedHalf params family hi q gs)ᴴ) := by
                    rw [← leftTensor_finset_sum (ι₂ := ι) Finset.univ]
              _ = leftTensor (ι₂ := ι) (1 : MIPStarRE.Quantum.Op ι) := by
                    congr 1
                    let xs : PointTuple params (i + 1) :=
                      (pointTupleLastFrontEquiv params i) (fun j => q.2 ⟨j.1, by omega⟩)
                    have hperm :
                        (∑ gs : GHatTupleOutcome params (i + 1),
                          ldSandwichLineOnePointCS_rotatedHalf params family hi q gs *
                            (ldSandwichLineOnePointCS_rotatedHalf params family hi q gs)ᴴ) =
                        ∑ gs : GHatTupleOutcome params (i + 1),
                          gHatHalfProductOutcomeOperator params family (i + 1) xs gs *
                            (gHatHalfProductOutcomeOperator params family (i + 1) xs gs)ᴴ := by
                      exact Fintype.sum_equiv (gHatTupleOutcomeLastFrontEquiv params i)
                        (fun gs : GHatTupleOutcome params (i + 1) =>
                          ldSandwichLineOnePointCS_rotatedHalf params family hi q gs *
                            (ldSandwichLineOnePointCS_rotatedHalf params family hi q gs)ᴴ)
                        (fun gs : GHatTupleOutcome params (i + 1) =>
                          gHatHalfProductOutcomeOperator params family (i + 1) xs gs *
                            (gHatHalfProductOutcomeOperator params family (i + 1) xs gs)ᴴ)
                        (by
                          intro gs
                          simp [xs, ldSandwichLineOnePointCS_rotatedHalf])
                    have hsum := (gHatSandwichFamily params family (i + 1) xs).sum_eq_total
                    rw [hperm]
                    simpa [gHatSandwichFamily, gHatHalfProductTotalOperator_eq_one] using hsum
              _ = 1 := by simp [leftTensor]
  · unfold ldSandwichLineOnePoint_prefix_sourceOutcomeSum
      ldSandwichLineOnePointCS_firstSourceRaw
    apply avgOver_congr
    intro q
    classical
    let evalOutcome : GHatTupleOutcome params (i + 1) → Option (Fq params) := fun gs =>
      Option.map (fun g : Polynomial params => g q.1)
        (gs ⟨i, Nat.lt_succ_self i⟩)
    let O : GHatTupleOutcome params (i + 1) → MIPStarRE.Quantum.Op ι := fun gs =>
      ldSandwichLineOnePointCS_orderedHalf params family hi q gs
    let R : Fq params → MIPStarRE.Quantum.Op ι := fun a =>
      1 - ((ldSandwichLineOnePointRightFamily params strategy family k i) q).outcome (some a)
    calc
      ∑ a : Fq params,
          ev strategy.state
            (opTensor
              ((ldSandwichLineOnePointPrefixOriginalFamily params family hi q).outcome (some a))
              (1 -
                (ldSandwichLineOnePointRightFamily params strategy family k i q).outcome (some a)))
          = ∑ a : Fq params,
              ev strategy.state
                (opTensor
                  (∑ gs : GHatTupleOutcome params (i + 1),
                    if evalOutcome gs = some a then O gs * (O gs)ᴴ else 0)
                  (R a)) := by
                simp [evalOutcome, O, R,
                  ldSandwichLineOnePointPrefixOriginalFamily_outcome_some params family hi q,
                  ldSandwichLineOnePointCS_orderedHalf]
      _ = ∑ a : Fq params, ∑ gs : GHatTupleOutcome params (i + 1),
              ev strategy.state
                (opTensor (if evalOutcome gs = some a then O gs * (O gs)ᴴ else 0) (R a)) := by
            refine Finset.sum_congr rfl ?_
            intro a _ha
            rw [opTensor_sum_left_univ, ev_sum]
      _ = ∑ gs : GHatTupleOutcome params (i + 1), ∑ a : Fq params,
              ev strategy.state
                (opTensor (if evalOutcome gs = some a then O gs * (O gs)ᴴ else 0) (R a)) := by
            rw [Finset.sum_comm]
      _ = ∑ gs : GHatTupleOutcome params (i + 1),
              ev strategy.state
                (opTensor (O gs * (O gs)ᴴ)
                  (ldSandwichLineOnePointCS_rightComplement params strategy family q gs)) := by
            refine Finset.sum_congr rfl ?_
            intro gs _hgs
            cases hgs : evalOutcome gs with
            | none =>
                simp [evalOutcome, R, ldSandwichLineOnePointCS_rightComplement, hgs,
                  opTensor, ev_zero]
            | some a0 =>
                rw [Finset.sum_eq_single a0]
                · simp [evalOutcome, R, ldSandwichLineOnePointCS_rightComplement, hgs]
                · intro b _hb hb_ne
                  simp [Ne.symm hb_ne, opTensor, ev_zero]
                · intro hnot
                  simp at hnot
      _ = ∑ gs : GHatTupleOutcome params (i + 1), ∑ u : Unit,
              ev strategy.state
                (ldSandwichLineOnePointCS_Aord params family hi q gs *
                  ldSandwichLineOnePointCS_Cfirst params strategy family hi q gs u) := by
            refine Finset.sum_congr rfl ?_
            intro gs _hgs
            rw [Fintype.sum_unique]
            change ev strategy.state
                (opTensor (O gs * (O gs)ᴴ)
                  (ldSandwichLineOnePointCS_rightComplement params strategy family q gs)) =
              ev strategy.state
                (opTensor (O gs) (1 : MIPStarRE.Quantum.Op ι) *
                  opTensor ((O gs)ᴴ)
                    (ldSandwichLineOnePointCS_rightComplement params strategy family q gs))
            rw [opTensor_mul]
            simp
  · unfold ldSandwichLineOnePoint_prefix_afterFirstCSOutcomeSum
      ldSandwichLineOnePointCS_firstTargetRaw
    apply avgOver_congr
    intro q
    classical
    let evalOutcome : GHatTupleOutcome params (i + 1) → Option (Fq params) := fun gs =>
      Option.map (fun g : Polynomial params => g q.1)
        (gs ⟨i, Nat.lt_succ_self i⟩)
    refine Finset.sum_congr rfl ?_
    intro gs _hgs
    cases hgs : evalOutcome gs with
    | none =>
        simp [evalOutcome, ldSandwichLineOnePointCS_Arot,
          ldSandwichLineOnePointCS_Cfirst, ldSandwichLineOnePointCS_orderedHalf,
          ldSandwichLineOnePointCS_rotatedHalf,
          ldSandwichLineOnePointCS_rightComplement, hgs, opTensor, ev_zero]
    | some a =>
        rw [Fintype.sum_unique]
        simp [evalOutcome, hgs, ldSandwichLineOnePointCS_Arot,
          ldSandwichLineOnePointCS_Cfirst, ldSandwichLineOnePointCS_orderedHalf,
          ldSandwichLineOnePointCS_rotatedHalf,
          ldSandwichLineOnePointCS_rightComplement, leftTensor_mul_opTensor]
  · unfold ldSandwichLineOnePoint_prefix_afterFirstCSOutcomeSum
      ldSandwichLineOnePointCS_secondSourceRaw
    apply avgOver_congr
    intro q
    classical
    let evalOutcome : GHatTupleOutcome params (i + 1) → Option (Fq params) := fun gs =>
      Option.map (fun g : Polynomial params => g q.1)
        (gs ⟨i, Nat.lt_succ_self i⟩)
    refine Finset.sum_congr rfl ?_
    intro gs _hgs
    cases hgs : evalOutcome gs with
    | none =>
        simp [evalOutcome, ldSandwichLineOnePointCS_Aord,
          ldSandwichLineOnePointCS_Csecond,
          ldSandwichLineOnePointCS_rightComplement, hgs, opTensor, ev_zero]
    | some a =>
        rw [Fintype.sum_unique]
        simp [evalOutcome, hgs, ldSandwichLineOnePointCS_Aord,
          ldSandwichLineOnePointCS_Csecond, ldSandwichLineOnePointCS_orderedHalf,
          ldSandwichLineOnePointCS_rotatedHalf,
          ldSandwichLineOnePointCS_rightComplement, opTensor_mul_leftTensor]
  · unfold ldSandwichLineOnePoint_prefix_movedOutcomeSum
      ldSandwichLineOnePointCS_secondTargetRaw
    apply avgOver_congr
    intro q
    classical
    let e : GHatTupleOutcome params (i + 1) ≃ GHatTupleOutcome params (i + 1) :=
      gHatTupleOutcomeLastFrontEquiv params i
    let xsMoved : PointTuple params (i + 1) :=
      Fin.cons (q.2 ⟨i, hi⟩) (fun j => q.2 ⟨j.1, by omega⟩)
    let movedEval : GHatTupleOutcome params (i + 1) → Option (Fq params) := fun gs =>
      Option.map (fun g : Polynomial params => g q.1) (gs 0)
    let movedHalf : GHatTupleOutcome params (i + 1) → MIPStarRE.Quantum.Op ι := fun gs =>
      gHatHalfProductOutcomeOperator params family (i + 1) xsMoved gs
    let R : Fq params → MIPStarRE.Quantum.Op ι := fun a =>
      1 - ((ldSandwichLineOnePointRightFamily params strategy family k i) q).outcome (some a)
    calc
      ∑ a : Fq params,
          ev strategy.state
            (opTensor
              ((ldSandwichLineOnePointPrefixMovedFamily params family hi q).outcome (some a))
              (1 -
                (ldSandwichLineOnePointRightFamily params strategy family k i q).outcome (some a)))
          = ∑ a : Fq params,
              ev strategy.state
                (opTensor
                  (∑ gs : GHatTupleOutcome params (i + 1),
                    if movedEval gs = some a then movedHalf gs * (movedHalf gs)ᴴ else 0)
                  (R a)) := by
                simp [movedEval, movedHalf, xsMoved, R,
                  ldSandwichLineOnePointPrefixMovedFamily_outcome_some params family hi q]
      _ = ∑ a : Fq params, ∑ gs : GHatTupleOutcome params (i + 1),
              ev strategy.state
                (opTensor (if movedEval gs = some a then movedHalf gs * (movedHalf gs)ᴴ else 0)
                  (R a)) := by
            refine Finset.sum_congr rfl ?_
            intro a _ha
            rw [opTensor_sum_left_univ, ev_sum]
      _ = ∑ gs : GHatTupleOutcome params (i + 1), ∑ a : Fq params,
              ev strategy.state
                (opTensor (if movedEval gs = some a then movedHalf gs * (movedHalf gs)ᴴ else 0)
                  (R a)) := by
            rw [Finset.sum_comm]
      _ = ∑ gs : GHatTupleOutcome params (i + 1),
              ev strategy.state
                (opTensor (movedHalf gs * (movedHalf gs)ᴴ)
                  (match movedEval gs with
                   | none => 0
                   | some a => R a)) := by
            refine Finset.sum_congr rfl ?_
            intro gs _hgs
            cases hgs : movedEval gs with
            | none =>
                simp [R, opTensor, ev_zero]
            | some a0 =>
                rw [Finset.sum_eq_single a0]
                · simp [R]
                · intro b _hb hb_ne
                  simp [Ne.symm hb_ne, opTensor, ev_zero]
                · intro hnot
                  simp at hnot
      _ = ∑ gs : GHatTupleOutcome params (i + 1),
              ev strategy.state
                (opTensor
                  (ldSandwichLineOnePointCS_rotatedHalf params family hi q gs *
                    (ldSandwichLineOnePointCS_rotatedHalf params family hi q gs)ᴴ)
                  (ldSandwichLineOnePointCS_rightComplement params strategy family q gs)) := by
            symm
            exact Fintype.sum_equiv e
              (fun gs : GHatTupleOutcome params (i + 1) =>
                ev strategy.state
                  (opTensor
                    (ldSandwichLineOnePointCS_rotatedHalf params family hi q gs *
                      (ldSandwichLineOnePointCS_rotatedHalf params family hi q gs)ᴴ)
                    (ldSandwichLineOnePointCS_rightComplement params strategy family q gs)))
              (fun gs : GHatTupleOutcome params (i + 1) =>
                ev strategy.state
                  (opTensor (movedHalf gs * (movedHalf gs)ᴴ)
                    (match movedEval gs with
                     | none => 0
                     | some a => R a)))
              (by
                intro gs
                unfold e movedHalf movedEval xsMoved R
                  ldSandwichLineOnePointCS_rotatedHalf
                  ldSandwichLineOnePointCS_rightComplement
                  gHatTupleOutcomeLastFrontEquiv pointTupleLastFrontEquiv
                rfl)
      _ = ∑ gs : GHatTupleOutcome params (i + 1), ∑ u : Unit,
              ev strategy.state
                (ldSandwichLineOnePointCS_Csecond params strategy family hi q gs u *
                  (ldSandwichLineOnePointCS_Arot params family hi q gs)ᴴ) := by
            refine Finset.sum_congr rfl ?_
            intro gs _hgs
            rw [Fintype.sum_unique]
            simp [ldSandwichLineOnePointCS_Arot, ldSandwichLineOnePointCS_Csecond,
              ldSandwichLineOnePointCS_rotatedHalf,
              ldSandwichLineOnePointCS_rightComplement, opTensor_mul_leftTensor]
end MIPStarRE.LDT.Pasting
