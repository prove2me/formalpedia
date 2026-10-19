-- Prove2me | solution 1 for MIPStarRE.LDT.Commutativity.comMain_of_commutativityPoints
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T05:20:28.758832+00:00
-- url     : https://prove2.me/submissions/c184a0ca-16f2-45c9-9ac5-6328772c3b5e

/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE, with the
authors' permission. Vendored from https://github.com/LionSR/MIPStarRE
(commit 507e8122, 2026-08-25) by scripts/vendor-lidt.py; do not edit by hand.
Upstream path: MIPStarRE/LDT/Commutativity/Main/Results.lean
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
Upstream path: MIPStarRE/LDT/Basic/PMFAverages.lean
-/
/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE, with the
authors' permission. Vendored from https://github.com/LionSR/MIPStarRE
(commit 507e8122, 2026-08-25) by scripts/vendor-lidt.py; do not edit by hand.
Upstream path: MIPStarRE/LDT/Basic/PMFUniformAverages.lean
-/
/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE, with the
authors' permission. Vendored from https://github.com/LionSR/MIPStarRE
(commit 507e8122, 2026-08-25) by scripts/vendor-lidt.py; do not edit by hand.
Upstream path: MIPStarRE/LDT/Basic/DistributionUniformSums.lean
-/
/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE, with the
authors' permission. Vendored from https://github.com/LionSR/MIPStarRE
(commit 507e8122, 2026-08-25) by scripts/vendor-lidt.py; do not edit by hand.
Upstream path: MIPStarRE/LDT/Basic/DistributionAvg.lean
-/
/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE, with the
authors' permission. Vendored from https://github.com/LionSR/MIPStarRE
(commit 507e8122, 2026-08-25) by scripts/vendor-lidt.py; do not edit by hand.
Upstream path: MIPStarRE/LDT/Commutativity/Transport/EvaluationSpecialization.lean
-/
/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE, with the
authors' permission. Vendored from https://github.com/LionSR/MIPStarRE
(commit 507e8122, 2026-08-25) by scripts/vendor-lidt.py; do not edit by hand.
Upstream path: MIPStarRE/LDT/Commutativity/Transport/Pullback.lean
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/LIDT/MIPStarRE/LDT/Commutativity/Main/Results.lean (solution of MIPStarRE.LDT.Commutativity.comMain_of_commutativityPoints);
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
import Mathlib.Data.Finite.Defs
import Mathlib.Data.Finite.Prod
import Mathlib.Data.Finset.Attach
import Mathlib.Data.Finset.BooleanAlgebra
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Empty
import Mathlib.Data.Finset.Filter
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Lattice.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Prod
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
import Mathlib.Data.SProd
import Mathlib.Data.Set.Defs
import Mathlib.Data.SetLike.Basic
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.Geometry.Convex.Cone.Pointed
import Mathlib.GroupTheory.GroupAction.Hom
import Mathlib.GroupTheory.GroupAction.Ring
import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Logic.Basic
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
import Theorems.Thm_MIPStarRE_LDT_Commutativity_commDataProcessedG_of_commutativityPoints
import Theorems.Thm_MIPStarRE_LDT_Commutativity_fullSliceCommutation_of_evaluated_on_evaluated_questions
import Theorems.Thm_MIPStarRE_LDT_sddError_nonneg
import Theorems.Thm_PMF_uniformOfFintype_sum_equiv_fst_smul

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPStarRE.LDT
section
open scoped BigOperators MatrixOrder Matrix ComplexOrder
set_option backward.isDefEq.respectTransparency false
/-- On a finite ambient type, a summand that vanishes outside a distribution's
explicit support has the same total sum over all ambient values as over that support.

This is a project-local explicit-support adapter around Mathlib's `Finset.sum_subset`:
Mathlib supplies the finite-sum theorem, while this lemma packages the common shape used
when paper expressions sum over a whole question set but the repository stores a smaller
`Distribution.support`.  It is not intended to replace Mathlib probability theory. -/
theorem Distribution.sum_univ_eq_sum_support {α β : Type*} [Fintype α]
    [AddCommMonoid β] (𝒟 : Distribution α) (f : α → β)
    (hf : ∀ a, a ∉ 𝒟.support → f a = 0) :
    (∑ a : α, f a) = ∑ a ∈ 𝒟.support, f a := by
  classical
  simpa using
    (Finset.sum_subset (Finset.subset_univ 𝒟.support)
      (fun a _ ha => hf a ha)).symm
end
end MIPStarRE.LDT

namespace MIPStarRE.LDT.Distribution
section
open scoped BigOperators MatrixOrder Matrix ComplexOrder
set_option backward.isDefEq.respectTransparency false
/-- The associated PMF has zero mass outside the stored support of the project
distribution. -/
theorem toPMF_apply_of_notMem {α : Type*} (𝒟 : Distribution α)
    (h𝒟 : 𝒟.IsProbability) {a : α} (ha : a ∉ 𝒟.support) :
    𝒟.toPMF h𝒟 a = 0 := by
  rw [toPMF_apply, 𝒟.outsideSupport a ha]
  simp
end
end MIPStarRE.LDT.Distribution

namespace MIPStarRE.LDT.Distribution
section
open scoped BigOperators MatrixOrder Matrix ComplexOrder
set_option backward.isDefEq.respectTransparency false
/-- The project uniform distribution on a nonempty finite support is Mathlib's
uniform probability mass function on that support. -/
theorem uniformOnFinset_toPMF
    {α : Type*} (s : Finset α) (hs : s.Nonempty) :
    (uniformOnFinset s).toPMF (uniformOnFinset_isProbability s hs) =
      PMF.uniformOfFinset s hs := by
  ext a
  rw [toPMF_apply]
  rw [show (uniformOnFinset s).weight a =
      (PMF.uniformOfFinset s hs a).toReal by
        classical
        by_cases ha : a ∈ s
        · simp [uniformOnFinset_weight, PMF.uniformOfFinset_apply, ha,
            ENNReal.toReal_inv, ENNReal.toReal_natCast]
        · simp [uniformOnFinset_weight, PMF.uniformOfFinset_apply, ha]]
  exact ENNReal.ofReal_toReal ((PMF.uniformOfFinset s hs).apply_ne_top a)
end
end MIPStarRE.LDT.Distribution

namespace MIPStarRE.LDT
section
open scoped BigOperators MatrixOrder Matrix ComplexOrder
set_option backward.isDefEq.respectTransparency false
/-- The project uniform distribution on a nonempty finite type is Mathlib's
uniform probability mass function on that type. -/
theorem uniformDistribution_toPMF
    (α : Type*) [Fintype α] [DecidableEq α] [Nonempty α] :
    (uniformDistribution α).toPMF (uniformDistribution_isProbability α) =
      PMF.uniformOfFintype α := by
  simpa [uniformDistribution, PMF.uniformOfFintype] using
    Distribution.uniformOnFinset_toPMF (Finset.univ : Finset α) Finset.univ_nonempty
end
end MIPStarRE.LDT

namespace PMF
section
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
/-- Marginalize a uniform PMF-weighted sum along the second coordinate of a
product equivalence. -/
theorem uniformOfFintype_sum_equiv_snd_smul {γ α β M : Type*}
    [Fintype γ] [Nonempty γ]
    [Finite α] [Nonempty α]
    [Fintype β] [Nonempty β]
    [AddCommMonoid M] [Module MIPStarRE.LDT.Error M]
    (e : γ ≃ α × β) (f : β → M) :
    ∑ x : γ, (PMF.uniformOfFintype γ x).toReal • f (e x).2 =
      ∑ b : β, (PMF.uniformOfFintype β b).toReal • f b := by
  classical
  haveI := Fintype.ofFinite α
  simpa using
    (uniformOfFintype_sum_equiv_fst_smul
      (e := e.trans (Equiv.prodComm α β)) (f := f))
end
end PMF

namespace PMF
section
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
/-- A finite expectation against a uniform PMF marginalizes a function depending
only on the second coordinate of a product equivalence. -/
theorem realWeightedSum_uniformOfFintype_equiv_snd {γ α β M : Type*}
    [Fintype γ] [Nonempty γ]
    [Finite α] [Nonempty α]
    [Fintype β] [Nonempty β]
    [AddCommMonoid M] [Module MIPStarRE.LDT.Error M]
    (e : γ ≃ α × β) (f : β → M) :
    realWeightedSum (PMF.uniformOfFintype γ) (fun x => f (e x).2) =
      realWeightedSum (PMF.uniformOfFintype β) f := by
  simpa [realWeightedSum] using
    uniformOfFintype_sum_equiv_snd_smul (e := e) (f := f)
end
end PMF

namespace MIPStarRE.LDT.Distribution
section
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
/-- A module-valued finite weighted sum against a probabilistic project
distribution may be written with the real weights of the associated Mathlib
probability mass function, over the stored support. -/
theorem sum_smul_eq_toPMF_support_sum {α M : Type*}
    [AddCommMonoid M] [Module Error M]
    (𝒟 : Distribution α) (h𝒟 : 𝒟.IsProbability) (f : α → M) :
    ∑ a ∈ 𝒟.support, 𝒟.weight a • f a =
      ∑ a ∈ 𝒟.support, (𝒟.toPMF h𝒟 a).toReal • f a := by
  exact Finset.sum_congr rfl fun a _ => by
    rw [Distribution.toPMF_apply_toReal]
end
end MIPStarRE.LDT.Distribution

namespace MIPStarRE.LDT.Distribution
section
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
/-- A module-valued finite weighted sum against a probabilistic project
distribution may be written as a full finite sum with the real weights of the
associated Mathlib probability mass function. -/
theorem sum_smul_eq_toPMF_sum {α M : Type*} [Fintype α]
    [AddCommMonoid M] [Module Error M]
    (𝒟 : Distribution α) (h𝒟 : 𝒟.IsProbability) (f : α → M) :
    ∑ a ∈ 𝒟.support, 𝒟.weight a • f a =
      ∑ a : α, (𝒟.toPMF h𝒟 a).toReal • f a := by
  rw [Distribution.sum_smul_eq_toPMF_support_sum 𝒟 h𝒟 f]
  exact (Distribution.sum_univ_eq_sum_support 𝒟
    (fun a => (𝒟.toPMF h𝒟 a).toReal • f a)
    (by
      intro a ha
      rw [Distribution.toPMF_apply_of_notMem 𝒟 h𝒟 ha]
      simp)).symm
end
end MIPStarRE.LDT.Distribution

namespace MIPStarRE.LDT
section
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
/-- Module-valued finite-sum expression for the uniform distribution, stated
without measurable-space assumptions. -/
theorem uniformDistribution_sum_smul_eq_pmf_sum {α M : Type*}
    [Fintype α] [DecidableEq α] [Nonempty α]
    [AddCommMonoid M] [Module Error M] (f : α → M) :
    ∑ a ∈ (uniformDistribution α).support, (uniformDistribution α).weight a • f a =
      ∑ a : α, (PMF.uniformOfFintype α a).toReal • f a := by
  rw [Distribution.sum_smul_eq_toPMF_sum
    (uniformDistribution α) (uniformDistribution_isProbability α)]
  rw [uniformDistribution_toPMF]
end
end MIPStarRE.LDT

namespace MIPStarRE.LDT
section
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
/-- A function depending only on the second coordinate of a product equivalence
has the second-coordinate uniform module-valued marginal. -/
theorem uniformDistribution_sum_smul_equiv_snd {γ α β M : Type*}
    [Fintype γ] [DecidableEq γ] [Nonempty γ]
    [Finite α] [Nonempty α]
    [Fintype β] [DecidableEq β] [Nonempty β]
    [AddCommMonoid M] [Module Error M]
    (e : γ ≃ α × β) (f : β → M) :
    ∑ x ∈ (uniformDistribution γ).support,
        (uniformDistribution γ).weight x • f (e x).2 =
      ∑ b ∈ (uniformDistribution β).support, (uniformDistribution β).weight b • f b := by
  classical
  haveI := Fintype.ofFinite α
  rw [uniformDistribution_sum_smul_eq_pmf_sum (α := γ)]
  rw [uniformDistribution_sum_smul_eq_pmf_sum (α := β)]
  simpa [PMF.realWeightedSum] using
    PMF.realWeightedSum_uniformOfFintype_equiv_snd (e := e) (f := f)
end
end MIPStarRE.LDT

namespace MIPStarRE.LDT
section
open scoped BigOperators MatrixOrder Matrix ComplexOrder
set_option backward.isDefEq.respectTransparency false
/-- A function depending only on the second coordinate of a product equivalence
has the corresponding second-coordinate uniform marginal. -/
theorem avgOver_uniform_equiv_snd
    {γ α β : Type*}
    [Fintype γ] [DecidableEq γ] [Nonempty γ]
    [Finite α] [Nonempty α]
    [Fintype β] [DecidableEq β] [Nonempty β]
    (e : γ ≃ α × β) (f : β → Error) :
    avgOver (uniformDistribution γ) (fun x => f (e x).2) =
      avgOver (uniformDistribution β) f := by
  simpa [avgOver, smul_eq_mul] using
    (uniformDistribution_sum_smul_equiv_snd (M := Error) (e := e) (f := f))
end
end MIPStarRE.LDT

namespace MIPStarRE.LDT.Commutativity
section
open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder Matrix ComplexOrder
set_option backward.isDefEq.respectTransparency false
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
/-- The evaluated-from-full-slice SDD error equals the evaluated-slice
SDD error, because the postprocessed product equals the product of
postprocessed submeasurements at every question-outcome pair. -/
lemma evaluationSpecialization_sddErrorOp_eq
    (params : Parameters) [FieldModel params.q] (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι) :
    sddErrorOp strategy.state
      (uniformDistribution (EvaluatedSliceQuestion params))
      (evaluatedFromFullSliceProductLeft
        params strategy family)
      (evaluatedFromFullSliceProductRight
        params strategy family) =
    sddErrorOp strategy.state
      (uniformDistribution (EvaluatedSliceQuestion params))
      (evaluatedSliceProductLeft params strategy family)
      (evaluatedSliceProductRight
        params strategy family) := by
  simp only [sddErrorOp, qSDDOp, qSDDCore]
  simp_rw [evaluatedFromFullSliceProductLeft_outcome_eq,
      evaluatedFromFullSliceProductRight_outcome_eq]
end
end MIPStarRE.LDT.Commutativity

namespace MIPStarRE.LDT.Commutativity
section
open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder Matrix ComplexOrder
set_option backward.isDefEq.respectTransparency false
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
/-- Pulling a family on `FullSliceQuestion` back along
`fullSliceQuestionOfEvaluatedSlice` preserves the averaged `sddErrorOp`. -/
lemma sddErrorOp_pullback_fullSliceQuestion_eq
    (params : Parameters) [FieldModel params.q]
    (ψ : QuantumState (ι × ι))
    {Outcome : Type*} [Fintype Outcome]
    (A B : IdxOpFamily (FullSliceQuestion params) Outcome (ι × ι)) :
    sddErrorOp ψ
      (uniformDistribution (EvaluatedSliceQuestion params))
      (fun q => A (fullSliceQuestionOfEvaluatedSlice params q))
      (fun q => B (fullSliceQuestionOfEvaluatedSlice params q)) =
    sddErrorOp ψ
      (uniformDistribution (FullSliceQuestion params))
      A B := by
  let e := evaluatedSliceQuestionEquiv params
  unfold sddErrorOp
  simpa [e, evaluatedSliceQuestionEquiv, fullSliceQuestionOfEvaluatedSlice] using
    (avgOver_uniform_equiv_snd (e := e)
      (f := fun xy : FullSliceQuestion params => qSDDOp ψ (A xy) (B xy)))
end
end MIPStarRE.LDT.Commutativity

namespace MIPStarRE.LDT.Commutativity
section
open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder Matrix ComplexOrder
set_option backward.isDefEq.respectTransparency false
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
/-- Any `SDDOpRel` bound proved after pulling back along
`fullSliceQuestionOfEvaluatedSlice` descends to `FullSliceQuestion`. -/
lemma sddOpRel_of_pullback_fullSliceQuestion
    (params : Parameters) [FieldModel params.q]
    (ψ : QuantumState (ι × ι))
    {Outcome : Type*} [Fintype Outcome]
    (A B : IdxOpFamily (FullSliceQuestion params) Outcome (ι × ι))
    (δ : Error) :
    SDDOpRel ψ
      (uniformDistribution (EvaluatedSliceQuestion params))
      (fun q => A (fullSliceQuestionOfEvaluatedSlice params q))
      (fun q => B (fullSliceQuestionOfEvaluatedSlice params q))
      δ →
    SDDOpRel ψ
      (uniformDistribution (FullSliceQuestion params))
      A B
      δ := by
  intro ⟨h⟩
  constructor
  rw [← sddErrorOp_pullback_fullSliceQuestion_eq params ψ A B]
  exact h
end
end MIPStarRE.LDT.Commutativity

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPStarRE.LDT.Commutativity
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
    (gamma zeta : Error)
    (hnorm : strategy.state.IsNormalized)
    (hcomm :
      SDDOpRel strategy.state
        (uniformDistribution (MIPStarRE.LDT.GlobalVariance.PointPairQuestion params.next))
        (pointMeasurementProductLeft params.next strategy)
        (pointMeasurementProductRight params.next strategy)
        (commutativityPointsError params.next gamma))
    (hgamma_nonneg : 0 ≤ gamma)
    (family : IdxPolyFamily params ι)
    (hcons : family.ConsistentWithPoints strategy zeta)
    (hself : family.StronglySelfConsistent strategy.state zeta)
    (hbound : IdxPolyFamily.SliceBoundednessInput strategy family zeta) :
    ComMainConclusion params strategy family gamma zeta := by
  let hEval :=
    commDataProcessedG_of_commutativityPoints
      params strategy gamma zeta hnorm hcomm hgamma_nonneg family hcons hself hbound
  have hSpecialized :
      SDDOpRel strategy.state
        (uniformDistribution (EvaluatedSliceQuestion params))
        (evaluatedFromFullSliceProductLeft params strategy family)
        (evaluatedFromFullSliceProductRight params strategy family)
        (commDataProcessedGError params gamma zeta) := by
    constructor
    rw [evaluationSpecialization_sddErrorOp_eq]
    exact hEval.squaredDistanceBound
  have hzeta_nonneg : 0 ≤ zeta :=
    le_trans (sddError_nonneg _ _ _ _)
      hself.sliceSelfConsistency.squaredDistanceBound
  exact
    sddOpRel_of_pullback_fullSliceQuestion params strategy.state
      (fullSliceProductLeft params strategy family)
      (fullSliceProductRight params strategy family)
      (comMainError params gamma zeta)
      (fullSliceCommutation_of_evaluated_on_evaluated_questions
        params strategy family gamma zeta
        hnorm hgamma_nonneg hzeta_nonneg hself hSpecialized)
end MIPStarRE.LDT.Commutativity
