-- Prove2me | solution 1 for MIPStarRE.LDT.GlobalVariance.localVarianceDeviation_sum_le_localVarianceOfPointsError
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T04:35:11.042982+00:00
-- url     : https://prove2.me/submissions/c8e8b6bc-d65a-497c-9734-4861c6538889

/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE, with the
authors' permission. Vendored from https://github.com/LionSR/MIPStarRE
(commit 507e8122, 2026-08-25) by scripts/vendor-lidt.py; do not edit by hand.
Upstream path: MIPStarRE/LDT/GlobalVariance/Theorems/TransportChain/SumForm.lean
-/
/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE, with the
authors' permission. Vendored from https://github.com/LionSR/MIPStarRE
(commit 507e8122, 2026-08-25) by scripts/vendor-lidt.py; do not edit by hand.
Upstream path: MIPStarRE/LDT/Basic/Distribution.lean
-/
/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE, with the
authors' permission. Vendored from https://github.com/LionSR/MIPStarRE
(commit 507e8122, 2026-08-25) by scripts/vendor-lidt.py; do not edit by hand.
Upstream path: MIPStarRE/LDT/ExpansionHypercubeGraph/Defs/Core.lean
-/
/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE, with the
authors' permission. Vendored from https://github.com/LionSR/MIPStarRE
(commit 507e8122, 2026-08-25) by scripts/vendor-lidt.py; do not edit by hand.
Upstream path: MIPStarRE/LDT/GlobalVariance/Theorems/TransportChain/Core.lean
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/LIDT/MIPStarRE/LDT/GlobalVariance/Theorems/TransportChain/SumForm.lean (solution of MIPStarRE.LDT.GlobalVariance.localVarianceDeviation_sum_le_localVarianceOfPointsError);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Algebra.Algebra.Hom
import Mathlib.Algebra.Algebra.NonUnitalHom
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Algebra.Algebra.Spectrum.Basic
import Mathlib.Algebra.Algebra.Spectrum.Quasispectrum
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.GroupWithZero.Action
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
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
import Mathlib.Algebra.Group.AddChar
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Commute.Defs
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Fin.Basic
import Mathlib.Algebra.Group.Finsupp
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Algebra.Group.Invertible.Defs
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Algebra.Group.Pi.Basic
import Mathlib.Algebra.Group.Subgroup.Defs
import Mathlib.Algebra.Group.Submonoid.Defs
import Mathlib.Algebra.Group.Subsemigroup.Defs
import Mathlib.Algebra.Group.Units.Basic
import Mathlib.Algebra.Group.Units.Defs
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
import Mathlib.Algebra.Notation.Pi.Basic
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
import Mathlib.Algebra.Ring.CompTypeclasses
import Mathlib.Algebra.Ring.Defs
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
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unital
import Mathlib.Analysis.CStarAlgebra.Module.Constructions
import Mathlib.Analysis.CStarAlgebra.Module.Defs
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.Convex.Cone.Basic
import Mathlib.Analysis.Fourier.FiniteAbelian.Orthogonality
import Mathlib.Analysis.Fourier.ZMod
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
import Mathlib.Analysis.Real.Spectrum
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
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
import Mathlib.Data.Fin.SuccPred
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
import Mathlib.Data.Finsupp.Defs
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
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
import Mathlib.Data.Int.Cast.Basic
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.NodupEquivFin
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Sort
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Basis
import Mathlib.Data.Matrix.Block
import Mathlib.Data.Matrix.Diagonal
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Multiset.Bind
import Mathlib.Data.Multiset.Count
import Mathlib.Data.Multiset.Defs
import Mathlib.Data.Multiset.Filter
import Mathlib.Data.Multiset.MapFold
import Mathlib.Data.Multiset.ZeroCons
import Mathlib.Data.NNRat.Defs
import Mathlib.Data.NNReal.Defs
import Mathlib.Data.NNReal.Star
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Cast.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Cast.Order.Basic
import Mathlib.Data.Nat.Cast.Order.Ring
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
import Mathlib.Data.Set.Defs
import Mathlib.Data.Set.Operations
import Mathlib.Data.SetLike.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Defs
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.Geometry.Convex.Cone.Pointed
import Mathlib.GroupTheory.GroupAction.Hom
import Mathlib.GroupTheory.GroupAction.Ring
import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.LinearAlgebra.Matrix.CharP
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.UnitaryGroup
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
import Mathlib.NumberTheory.LegendreSymbol.AddCharacter
import Mathlib.Order.Basic
import Mathlib.Order.Defs.LinearOrder
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Order.Fin.Basic
import Mathlib.Order.Hom.Basic
import Mathlib.Order.Lattice
import Mathlib.Order.Lattice.Nat
import Mathlib.Order.MinMax
import Mathlib.Order.Monotone.Defs
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
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.NormNum.Result
import Mathlib.Tactic.Positivity.Core
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
import Mathlib.Topology.ContinuousOn
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
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Test_StrategyRole_Algebra
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Test_StrategyFailures
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_Defs_Core
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_GlobalVariance_Defs_Core
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Preliminaries_Polynomials
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Preliminaries_PolynomialAgreement
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_GlobalVariance_Defs_Operators
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_GlobalVariance_Defs_Families
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_Defs_Fourier
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_MatrixRealization_Core
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_MatrixRealization_TraceForms
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_Theorems_Foundations
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_Theorems_Matrix
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_Theorems_Results
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_GlobalVariance_Theorems_Averaging
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_GlobalVariance_Theorems_Statements
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_GlobalVariance_Theorems_AlgebraicIdentity
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_GlobalVariance_Theorems_CollisionExpansion
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_GlobalVariance_Theorems_SelfConsistencyTransport_PointLine
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_GlobalVariance_Theorems_TransportChain_Core
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_GlobalVariance_Theorems_SelfConsistencyTransportSum
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_GlobalVariance_Theorems_PolynomialSumBounds
import Theorems.Thm_MIPStarRE_LDT_Distribution_map_sum_smul
import Theorems.Thm_MIPStarRE_LDT_GlobalVariance_avgOver_transport_pointPair
import Theorems.Thm_MIPStarRE_LDT_GlobalVariance_axisParallelPointLineConsistency_weighted_leftToRightLineQuestion_sum
import Theorems.Thm_MIPStarRE_LDT_GlobalVariance_axisParallelPointLineConsistency_weighted_rightToLeftLineQuestion_sum
import Theorems.Thm_MIPStarRE_LDT_GlobalVariance_ev_adjoint_sub_swap
import Theorems.Thm_MIPStarRE_LDT_GlobalVariance_generalizeBDeviationAtPolynomial_polysum_le_error
import Theorems.Thm_MIPStarRE_LDT_GlobalVariance_generalizeBReversePointwiseBound_polysum_le_error
import Theorems.Thm_MIPStarRE_LDT_GlobalVariance_pointConditionedEventSelfConsistency_weighted_point_sum
import Theorems.Thm_MIPStarRE_LDT_avgOver_add
import Theorems.Thm_MIPStarRE_LDT_avgOver_congr
import Theorems.Thm_MIPStarRE_LDT_avgOver_const_mul
import Theorems.Thm_MIPStarRE_LDT_avgOver_mono
import Theorems.Thm_MIPStarRE_LDT_avgOver_sum
import Theorems.Thm_MIPStarRE_LDT_delta_nonneg_of_isGood
import Theorems.Thm_MIPStarRE_LDT_eps_nonneg_of_isGood
import Theorems.Thm_MIPStarRE_LDT_ev_sum_conjTranspose_mul_sum_le

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPStarRE.LDT.Distribution
section
open scoped BigOperators MatrixOrder Matrix ComplexOrder
set_option backward.isDefEq.respectTransparency false
/-- Averaging against a pushed-forward distribution is averaging the pulled-back
function against the original distribution. -/
theorem avgOver_map {α β : Type*} [DecidableEq β]
    (𝒟 : Distribution α) (e : α → β) (f : β → Error) :
    avgOver (𝒟.map e) f = avgOver 𝒟 (fun a => f (e a)) := by
  simpa [avgOver, smul_eq_mul] using
    Distribution.map_sum_smul (𝒟 := 𝒟) e f
end
end MIPStarRE.LDT.Distribution

namespace MIPStarRE.LDT.ExpansionHypercubeGraph
section
open MIPStarRE.LDT
open MIPStarRE.LDT.MakingMeasurementsProjective
open scoped BigOperators MatrixOrder Matrix ComplexOrder
set_option backward.isDefEq.respectTransparency false
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
/-- Averaging over `rerandomizeCoord` is the same as averaging over the uniform
sample space of a point, a coordinate, and a replacement coordinate value. -/
theorem avgOver_rerandomizeCoord_eq_uniform_sample (params : Parameters)
    (f : Point params × Point params → Error) :
    avgOver (rerandomizeCoord params) f =
      avgOver (uniformDistribution (RerandomizeCoordSample params))
        (fun sample => f (rerandomizeCoordSampleToPair params sample)) := by
  simpa [rerandomizeCoord] using
    Distribution.avgOver_map
      (uniformDistribution (RerandomizeCoordSample params))
      (rerandomizeCoordSampleToPair params) f
end
end MIPStarRE.LDT.ExpansionHypercubeGraph

namespace MIPStarRE.LDT.GlobalVariance
section
open MIPStarRE.LDT
open MIPStarRE.LDT.Preliminaries
open MIPStarRE.LDT.MakingMeasurementsProjective
open MIPStarRE.LDT.ExpansionHypercubeGraph
open scoped BigOperators MatrixOrder Matrix ComplexOrder
set_option backward.isDefEq.respectTransparency false
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
lemma avgOver_axisParallelTestSample_update_eq_rerandomizeCoord
    (params : Parameters) [FieldModel params.q]
    (f : Point params × Point params → Error) :
    avgOver (uniformDistribution (AxisParallelTestSample params × Fq params))
      (fun sx => f (sx.1.1, Function.update sx.1.1 sx.1.2 sx.2)) =
    avgOver (rerandomizeCoord params) f := by
  rw [avgOver_rerandomizeCoord_eq_uniform_sample]
  try rfl
end
end MIPStarRE.LDT.GlobalVariance

namespace MIPStarRE.LDT.GlobalVariance
section
open MIPStarRE.LDT
open MIPStarRE.LDT.Preliminaries
open MIPStarRE.LDT.MakingMeasurementsProjective
open MIPStarRE.LDT.ExpansionHypercubeGraph
open scoped BigOperators MatrixOrder Matrix ComplexOrder
set_option backward.isDefEq.respectTransparency false
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
/-- The post-triangle six-step transport error is absorbed by the paper's
`24(ε + δ + md/q)` slack from `lem:local-variance-of-points`.

This is only the scalar arithmetic after applying
`prop:triangle-inequality-for-approx_delta` with `k = 6` to the estimates at
`references/ldt-paper/expansion.tex`, lines 305--311; it does not assert the
transport estimates themselves. -/
lemma localVarianceTransportChainError_le_localVarianceOfPointsError
    (params : Parameters)
    [FieldModel params.q]
    {eps delta gamma : Error}
    (strategy : SymStrat params ι)
    (hgood : strategy.IsGood eps delta gamma) :
    localVarianceTransportChainError params eps delta ≤
      localVarianceOfPointsError params eps delta := by
  have heps_nonneg := eps_nonneg_of_isGood params strategy hgood
  have hdelta_nonneg := delta_nonneg_of_isGood params strategy hgood
  have hgen_nonneg : 0 ≤ generalizeBError params := by
    dsimp [generalizeBError]
    positivity
  dsimp [localVarianceTransportChainError, localVarianceOfPointsError]
  linarith
end
end MIPStarRE.LDT.GlobalVariance

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPStarRE.LDT.GlobalVariance
open MIPStarRE.LDT
open MIPStarRE.LDT.Preliminaries
open MIPStarRE.LDT.MakingMeasurementsProjective
open MIPStarRE.LDT.ExpansionHypercubeGraph
open scoped BigOperators MatrixOrder Matrix ComplexOrder
set_option backward.isDefEq.respectTransparency false
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
theorem _root_.solution
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta gamma : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (G : SubMeas (Polynomial params) ι) :
    (∑ g : Polynomial params,
      localVarianceDeviationAtPolynomial params strategy strategy.state G g) ≤
      localVarianceOfPointsError params eps delta := by
  classical
  let 𝒟 := uniformDistribution (TransportQuestion params)
  -- six operators, indexed additionally by polynomial g
  let A0 (g : Polynomial params) (q : TransportQuestion params) : MIPStarRE.Quantum.Op (ι × ι) :=
    weightedPointConditionedOperatorAtPolynomial params strategy G g (q.1.1.pointAt q.1.2)
  let A1 (g : Polynomial params) (q : TransportQuestion params) : MIPStarRE.Quantum.Op (ι × ι) :=
    weightedPointConditionedRightOperatorAtPolynomial params strategy G g (q.1.1.pointAt q.1.2)
  let A2 (g : Polynomial params) (q : TransportQuestion params) : MIPStarRE.Quantum.Op (ι × ι) :=
    weightedGeneralizeBLeftOperatorAtPolynomial params strategy G g (q.1.1, q.1.1.pointAt q.1.2)
  let A3 (g : Polynomial params) (q : TransportQuestion params) : MIPStarRE.Quantum.Op (ι × ι) :=
    weightedGeneralizeBRightOperatorAtPolynomial params strategy G g (q.1.1, q.1.1.pointAt q.1.2)
  let A4 (g : Polynomial params) (q : TransportQuestion params) : MIPStarRE.Quantum.Op (ι × ι) :=
    weightedGeneralizeBLeftOperatorAtPolynomial params strategy G g (q.1.1, q.1.1.pointAt q.2)
  let A5 (g : Polynomial params) (q : TransportQuestion params) : MIPStarRE.Quantum.Op (ι × ι) :=
    weightedPointConditionedRightOperatorAtPolynomial params strategy G g (q.1.1.pointAt q.2)
  let A6 (g : Polynomial params) (q : TransportQuestion params) : MIPStarRE.Quantum.Op (ι × ι) :=
    weightedPointConditionedOperatorAtPolynomial params strategy G g (q.1.1.pointAt q.2)
  -- the squared-expectation discrepancy for a single step and a single (g, q)
  let δ01 (g : Polynomial params) (q : TransportQuestion params) : Error :=
    ev strategy.state (((A0 g q - A1 g q)ᴴ) * (A0 g q - A1 g q))
  let δ12 (g : Polynomial params) (q : TransportQuestion params) : Error :=
    ev strategy.state (((A1 g q - A2 g q)ᴴ) * (A1 g q - A2 g q))
  let δ23 (g : Polynomial params) (q : TransportQuestion params) : Error :=
    ev strategy.state (((A2 g q - A3 g q)ᴴ) * (A2 g q - A3 g q))
  let δ34 (g : Polynomial params) (q : TransportQuestion params) : Error :=
    ev strategy.state (((A3 g q - A4 g q)ᴴ) * (A3 g q - A4 g q))
  let δ45 (g : Polynomial params) (q : TransportQuestion params) : Error :=
    ev strategy.state (((A4 g q - A5 g q)ᴴ) * (A4 g q - A5 g q))
  let δ56 (g : Polynomial params) (q : TransportQuestion params) : Error :=
    ev strategy.state (((A5 g q - A6 g q)ᴴ) * (A5 g q - A6 g q))
  -- Total-error per step (sum over g, average over q)
  let S01 : Error := ∑ g : Polynomial params, avgOver 𝒟 (δ01 g)
  let S12 : Error := ∑ g : Polynomial params, avgOver 𝒟 (δ12 g)
  let S23 : Error := ∑ g : Polynomial params, avgOver 𝒟 (δ23 g)
  let S34 : Error := ∑ g : Polynomial params, avgOver 𝒟 (δ34 g)
  let S45 : Error := ∑ g : Polynomial params, avgOver 𝒟 (δ45 g)
  let S56 : Error := ∑ g : Polynomial params, avgOver 𝒟 (δ56 g)
  -- Step 1 (A0→A1): at most 2δ, after reindexing to the point distribution
  have hS01 : S01 ≤ 2 * delta := by
    dsimp [S01, A0, A1, δ01]
    calc
      (∑ g, avgOver 𝒟
          (fun q => ev strategy.state
            (((weightedPointConditionedOperatorAtPolynomial params strategy G g
                  (q.1.1.pointAt q.1.2) -
                weightedPointConditionedRightOperatorAtPolynomial params strategy G g
                  (q.1.1.pointAt q.1.2))ᴴ) *
              (weightedPointConditionedOperatorAtPolynomial params strategy G g
                  (q.1.1.pointAt q.1.2) -
                weightedPointConditionedRightOperatorAtPolynomial params strategy G g
                  (q.1.1.pointAt q.1.2)))))
        = ∑ g, avgOver (uniformDistribution (Point params))
            (fun u =>
              let D := weightedPointConditionedOperatorAtPolynomial params strategy G g u -
                weightedPointConditionedRightOperatorAtPolynomial params strategy G g u
              ev strategy.state (Dᴴ * D)) := by
          refine Finset.sum_congr rfl fun g _ => ?_
          rw [avgOver_transport_leftPoint params (fun u =>
            let D := weightedPointConditionedOperatorAtPolynomial params strategy G g u -
              weightedPointConditionedRightOperatorAtPolynomial params strategy G g u
            ev strategy.state (Dᴴ * D))]
      _ ≤ 2 * delta :=
        pointConditionedEventSelfConsistency_weighted_point_sum
          params strategy eps delta gamma hgood G
  -- Step 2 (A1→A2): at most 2ε, after reindexing to the line-question distribution
  have hS12 : S12 ≤ 2 * eps := by
    dsimp [S12, A1, A2, δ12]
    calc
      (∑ g, avgOver 𝒟
          (fun q => ev strategy.state
            (((weightedPointConditionedRightOperatorAtPolynomial params strategy G g
                  (q.1.1.pointAt q.1.2) -
                weightedGeneralizeBLeftOperatorAtPolynomial params strategy G g
                  (q.1.1, q.1.1.pointAt q.1.2))ᴴ) *
              (weightedPointConditionedRightOperatorAtPolynomial params strategy G g
                  (q.1.1.pointAt q.1.2) -
                weightedGeneralizeBLeftOperatorAtPolynomial params strategy G g
                  (q.1.1, q.1.1.pointAt q.1.2)))))
        = ∑ g, avgOver (axisParallelLineQuestionDistribution params)
            (fun qu =>
              let D := weightedPointConditionedRightOperatorAtPolynomial
                  params strategy G g qu.2 -
                weightedGeneralizeBLeftOperatorAtPolynomial params strategy G g qu
              ev strategy.state (Dᴴ * D)) := by
          refine Finset.sum_congr rfl fun g _ => ?_
          rw [avgOver_transport_leftQuestion params (fun qu =>
            let D := weightedPointConditionedRightOperatorAtPolynomial
                params strategy G g qu.2 -
              weightedGeneralizeBLeftOperatorAtPolynomial params strategy G g qu
            ev strategy.state (Dᴴ * D))]
      _ ≤ 2 * eps :=
        axisParallelPointLineConsistency_weighted_rightToLeftLineQuestion_sum
          params strategy eps delta gamma hgood G
  -- Step 3 (A2→A3): at most generalizeBError (forward direction)
  have hS23 : S23 ≤ generalizeBError params := by
    dsimp [S23, A2, A3, δ23]
    calc
      (∑ g, avgOver 𝒟
          (fun q => ev strategy.state
            (((weightedGeneralizeBLeftOperatorAtPolynomial params strategy G g
                  (q.1.1, q.1.1.pointAt q.1.2) -
                weightedGeneralizeBRightOperatorAtPolynomial params strategy G g
                  (q.1.1, q.1.1.pointAt q.1.2))ᴴ) *
              (weightedGeneralizeBLeftOperatorAtPolynomial params strategy G g
                  (q.1.1, q.1.1.pointAt q.1.2) -
                weightedGeneralizeBRightOperatorAtPolynomial params strategy G g
                  (q.1.1, q.1.1.pointAt q.1.2)))))
        = ∑ g, avgOver (axisParallelLineQuestionDistribution params)
            (fun qu =>
              let D := weightedGeneralizeBLeftOperatorAtPolynomial params strategy G g qu -
                weightedGeneralizeBRightOperatorAtPolynomial params strategy G g qu
              ev strategy.state (Dᴴ * D)) := by
          refine Finset.sum_congr rfl fun g _ => ?_
          rw [avgOver_transport_leftQuestion params (fun qu =>
            let D := weightedGeneralizeBLeftOperatorAtPolynomial params strategy G g qu -
              weightedGeneralizeBRightOperatorAtPolynomial params strategy G g qu
            ev strategy.state (Dᴴ * D))]
      _ ≤ generalizeBError params :=
        generalizeBDeviationAtPolynomial_polysum_le_error params strategy G
  -- Step 4 (A3→A4): at most generalizeBError (reverse direction)
  have hS34 : S34 ≤ generalizeBError params := by
    dsimp [S34, A3, A4, δ34]
    calc
      (∑ g, avgOver 𝒟
          (fun q => ev strategy.state
            (((weightedGeneralizeBRightOperatorAtPolynomial params strategy G g
                  (q.1.1, q.1.1.pointAt q.1.2) -
                weightedGeneralizeBLeftOperatorAtPolynomial params strategy G g
                  (q.1.1, q.1.1.pointAt q.2))ᴴ) *
              (weightedGeneralizeBRightOperatorAtPolynomial params strategy G g
                  (q.1.1, q.1.1.pointAt q.1.2) -
                weightedGeneralizeBLeftOperatorAtPolynomial params strategy G g
                  (q.1.1, q.1.1.pointAt q.2)))))
        = ∑ g, avgOver 𝒟
            (fun q =>
              let D := weightedGeneralizeBRightOperatorAtPolynomial params strategy G g
                  (q.1.1, q.1.1.pointAt q.2) -
                weightedGeneralizeBLeftOperatorAtPolynomial params strategy G g
                  (q.1.1, q.1.1.pointAt q.2)
              ev strategy.state (Dᴴ * D)) := by
          refine Finset.sum_congr rfl fun g _ => ?_
          refine avgOver_congr 𝒟 _ _ (fun q => ?_)
          simp [weightedGeneralizeBRightOperatorAtPolynomial_point_eq
            params strategy G g q.1.1 (q.1.1.pointAt q.1.2) (q.1.1.pointAt q.2)]
      _ = ∑ g, avgOver (axisParallelLineQuestionDistribution params)
            (fun qu =>
              let D := weightedGeneralizeBRightOperatorAtPolynomial params strategy G g qu -
                weightedGeneralizeBLeftOperatorAtPolynomial params strategy G g qu
              ev strategy.state (Dᴴ * D)) := by
          refine Finset.sum_congr rfl fun g _ => ?_
          rw [avgOver_transport_rightQuestion params (fun qu =>
            let D := weightedGeneralizeBRightOperatorAtPolynomial params strategy G g qu -
              weightedGeneralizeBLeftOperatorAtPolynomial params strategy G g qu
            ev strategy.state (Dᴴ * D))]
      _ ≤ generalizeBError params :=
        generalizeBReversePointwiseBound_polysum_le_error params strategy G
  -- Step 5 (A4→A5): at most 2ε
  have hS45 : S45 ≤ 2 * eps := by
    dsimp [S45, A4, A5, δ45]
    calc
      (∑ g, avgOver 𝒟
          (fun q => ev strategy.state
            (((weightedGeneralizeBLeftOperatorAtPolynomial params strategy G g
                  (q.1.1, q.1.1.pointAt q.2) -
                weightedPointConditionedRightOperatorAtPolynomial params strategy G g
                  (q.1.1.pointAt q.2))ᴴ) *
              (weightedGeneralizeBLeftOperatorAtPolynomial params strategy G g
                  (q.1.1, q.1.1.pointAt q.2) -
                weightedPointConditionedRightOperatorAtPolynomial params strategy G g
                  (q.1.1.pointAt q.2)))))
        = ∑ g, avgOver (axisParallelLineQuestionDistribution params)
            (fun qu =>
              let D := weightedGeneralizeBLeftOperatorAtPolynomial params strategy G g qu -
                weightedPointConditionedRightOperatorAtPolynomial params strategy G g qu.2
              ev strategy.state (Dᴴ * D)) := by
          refine Finset.sum_congr rfl fun g _ => ?_
          rw [avgOver_transport_rightQuestion params (fun qu =>
            let D := weightedGeneralizeBLeftOperatorAtPolynomial params strategy G g qu -
              weightedPointConditionedRightOperatorAtPolynomial params strategy G g qu.2
            ev strategy.state (Dᴴ * D))]
      _ ≤ 2 * eps :=
        axisParallelPointLineConsistency_weighted_leftToRightLineQuestion_sum
          params strategy eps delta gamma hgood G
  -- Step 6 (A5→A6): at most 2δ
  have hS56 : S56 ≤ 2 * delta := by
    dsimp [S56, A5, A6, δ56]
    calc
      (∑ g, avgOver 𝒟
          (fun q => ev strategy.state
            (((weightedPointConditionedRightOperatorAtPolynomial params strategy G g
                  (q.1.1.pointAt q.2) -
                weightedPointConditionedOperatorAtPolynomial params strategy G g
                  (q.1.1.pointAt q.2))ᴴ) *
              (weightedPointConditionedRightOperatorAtPolynomial params strategy G g
                  (q.1.1.pointAt q.2) -
                weightedPointConditionedOperatorAtPolynomial params strategy G g
                  (q.1.1.pointAt q.2)))))
        = ∑ g, avgOver 𝒟
            (fun q => ev strategy.state
              (((weightedPointConditionedOperatorAtPolynomial params strategy G g
                    (q.1.1.pointAt q.2) -
                  weightedPointConditionedRightOperatorAtPolynomial params strategy G g
                    (q.1.1.pointAt q.2))ᴴ) *
                (weightedPointConditionedOperatorAtPolynomial params strategy G g
                    (q.1.1.pointAt q.2) -
                  weightedPointConditionedRightOperatorAtPolynomial params strategy G g
                    (q.1.1.pointAt q.2)))) := by
          refine Finset.sum_congr rfl fun g _ => ?_
          refine avgOver_congr 𝒟 _ _ (fun q => ?_)
          exact ev_adjoint_sub_swap strategy.state
            (weightedPointConditionedOperatorAtPolynomial params strategy G g
              (q.1.1.pointAt q.2))
            (weightedPointConditionedRightOperatorAtPolynomial params strategy G g
              (q.1.1.pointAt q.2))
      _ = ∑ g, avgOver (uniformDistribution (Point params))
            (fun u =>
              let D := weightedPointConditionedOperatorAtPolynomial params strategy G g u -
                weightedPointConditionedRightOperatorAtPolynomial params strategy G g u
              ev strategy.state (Dᴴ * D)) := by
          refine Finset.sum_congr rfl fun g _ => ?_
          rw [avgOver_transport_rightPoint params (fun u =>
            let D := weightedPointConditionedOperatorAtPolynomial params strategy G g u -
              weightedPointConditionedRightOperatorAtPolynomial params strategy G g u
            ev strategy.state (Dᴴ * D))]
      _ ≤ 2 * delta :=
        pointConditionedEventSelfConsistency_weighted_point_sum
          params strategy eps delta gamma hgood G
  -- Pointwise triangle inequality (via ev_sum_conjTranspose_mul_sum_le)
  have htri_pointwise (q : TransportQuestion params) (g : Polynomial params) :
      ev strategy.state (((A0 g q - A6 g q)ᴴ) * (A0 g q - A6 g q)) ≤
        6 * (δ01 g q + δ12 g q + δ23 g q + δ34 g q + δ45 g q + δ56 g q) := by
    have hsum : A0 g q - A6 g q =
        (A0 g q - A1 g q) + (A1 g q - A2 g q) + (A2 g q - A3 g q) +
        (A3 g q - A4 g q) + (A4 g q - A5 g q) + (A5 g q - A6 g q) := by
      abel
    rw [hsum]
    have h := ev_sum_conjTranspose_mul_sum_le strategy.state
      (fun (i : Fin 6) =>
        match i with
        | 0 => A0 g q - A1 g q
        | 1 => A1 g q - A2 g q
        | 2 => A2 g q - A3 g q
        | 3 => A3 g q - A4 g q
        | 4 => A4 g q - A5 g q
        | 5 => A5 g q - A6 g q)
    simpa [δ01, δ12, δ23, δ34, δ45, δ56, Fintype.card_fin, Fin.sum_univ_six] using h
  -- Sum over g and average over 𝒟
  have htotal :
      (∑ g : Polynomial params,
        avgOver 𝒟 (fun q =>
          ev strategy.state (((A0 g q - A6 g q)ᴴ) * (A0 g q - A6 g q)))) ≤
      6 * (S01 + S12 + S23 + S34 + S45 + S56) := by
    calc
      (∑ g, avgOver 𝒟 (fun q =>
          ev strategy.state (((A0 g q - A6 g q)ᴴ) * (A0 g q - A6 g q))))
        = avgOver 𝒟 (fun q =>
            ∑ g, ev strategy.state (((A0 g q - A6 g q)ᴴ) * (A0 g q - A6 g q))) := by
          rw [avgOver_sum]
      _ ≤ avgOver 𝒟 (fun q =>
            ∑ g, 6 * (δ01 g q + δ12 g q + δ23 g q + δ34 g q + δ45 g q + δ56 g q)) := by
          refine avgOver_mono 𝒟 _ _ (fun q => ?_)
          refine Finset.sum_le_sum fun g _ => htri_pointwise q g
      _ = avgOver 𝒟 (fun q =>
            6 * ∑ g, (δ01 g q + δ12 g q + δ23 g q + δ34 g q + δ45 g q + δ56 g q)) := by
          refine avgOver_congr 𝒟 _ _ (fun q => ?_)
          simp [Finset.mul_sum]
      _ = 6 * avgOver 𝒟 (fun q =>
            ∑ g, (δ01 g q + δ12 g q + δ23 g q + δ34 g q + δ45 g q + δ56 g q)) := by
          rw [avgOver_const_mul]
      _ = 6 * avgOver 𝒟 (fun q =>
            (∑ g, δ01 g q) + (∑ g, δ12 g q) + (∑ g, δ23 g q) +
            (∑ g, δ34 g q) + (∑ g, δ45 g q) + (∑ g, δ56 g q)) := by
          refine congrArg (fun t => 6 * t) (avgOver_congr 𝒟 _ _ (fun q => ?_))
          simp [Finset.sum_add_distrib]
      _ = 6 * (avgOver 𝒟 (fun q => ∑ g, δ01 g q) +
               avgOver 𝒟 (fun q => ∑ g, δ12 g q) +
               avgOver 𝒟 (fun q => ∑ g, δ23 g q) +
               avgOver 𝒟 (fun q => ∑ g, δ34 g q) +
               avgOver 𝒟 (fun q => ∑ g, δ45 g q) +
               avgOver 𝒟 (fun q => ∑ g, δ56 g q)) := by
          rw [avgOver_add, avgOver_add, avgOver_add, avgOver_add, avgOver_add]
      _ = 6 * (S01 + S12 + S23 + S34 + S45 + S56) := by
        simp [S01, S12, S23, S34, S45, S56, avgOver_sum]
  -- The whole left side reindexed to rerandomizeCoord
  have hlocal_sum :
      (∑ g : Polynomial params,
        localVarianceDeviationAtPolynomial params strategy strategy.state G g) ≤
      localVarianceTransportChainError params eps delta := by
    unfold localVarianceDeviationAtPolynomial
    -- reindex each per-g term from rerandomizeCoord to 𝒟
    have hreindex (g : Polynomial params) :
        avgOver (rerandomizeCoord params)
          (fun uv =>
            let D := weightedPointConditionedOperatorAtPolynomial params strategy G g uv.1 -
              weightedPointConditionedOperatorAtPolynomial params strategy G g uv.2
            ev strategy.state (Dᴴ * D)) =
        avgOver 𝒟 (fun q =>
          ev strategy.state (((A0 g q - A6 g q)ᴴ) * (A0 g q - A6 g q))) := by
      let f : Point params × Point params → Error := fun uv =>
        let D := weightedPointConditionedOperatorAtPolynomial params strategy G g uv.1 -
          weightedPointConditionedOperatorAtPolynomial params strategy G g uv.2
        ev strategy.state (Dᴴ * D)
      calc
        avgOver (rerandomizeCoord params) f
          = avgOver (uniformDistribution (AxisParallelTestSample params × Fq params))
              (fun sx => f (sx.1.1, Function.update sx.1.1 sx.1.2 sx.2)) := by
            rw [← avgOver_axisParallelTestSample_update_eq_rerandomizeCoord params f]
        _ = avgOver 𝒟 (fun q => f (q.1.1.pointAt q.1.2, q.1.1.pointAt q.2)) := by
            rw [← avgOver_transport_pointPair params f]
        _ = avgOver 𝒟 (fun q =>
            ev strategy.state (((A0 g q - A6 g q)ᴴ) * (A0 g q - A6 g q))) := by
          refine avgOver_congr 𝒟 _ _ (fun q => ?_)
          simp [A0, A6, f]
    calc
      (∑ g : Polynomial params,
        avgOver (rerandomizeCoord params)
          (fun uv =>
            let D := weightedPointConditionedOperatorAtPolynomial params strategy G g uv.1 -
              weightedPointConditionedOperatorAtPolynomial params strategy G g uv.2
            ev strategy.state (Dᴴ * D)))
        = ∑ g, avgOver 𝒟 (fun q =>
            ev strategy.state (((A0 g q - A6 g q)ᴴ) * (A0 g q - A6 g q))) :=
          Finset.sum_congr rfl fun g _ => hreindex g
      _ ≤ 6 * (S01 + S12 + S23 + S34 + S45 + S56) := htotal
      _ ≤ 6 * ((2 * delta) + (2 * eps) + generalizeBError params + generalizeBError params +
          (2 * eps) + (2 * delta)) := by
        gcongr
      _ = localVarianceTransportChainError params eps delta := by
        simp [localVarianceTransportChainError]
        ring
  -- absorb the transport-chain error into the public error
  exact le_trans hlocal_sum
    (localVarianceTransportChainError_le_localVarianceOfPointsError params strategy hgood)
end MIPStarRE.LDT.GlobalVariance
