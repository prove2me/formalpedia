-- Prove2me | solution 1 for MIPStarRE.LDT.Commutativity.evaluatedSlice_scalar_chain_bound
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T05:10:40.876301+00:00
-- url     : https://prove2.me/submissions/6d5f6af2-830b-4039-8de2-1c85c1ccc8d9

/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE, with the
authors' permission. Vendored from https://github.com/LionSR/MIPStarRE
(commit 507e8122, 2026-08-25) by scripts/vendor-lidt.py; do not edit by hand.
Upstream path: MIPStarRE/LDT/Commutativity/ScalarApproximation/ProcessedG/MainChain.lean
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
Upstream path: MIPStarRE/LDT/Commutativity/Scaffold/Symmetry.lean
-/
/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE, with the
authors' permission. Vendored from https://github.com/LionSR/MIPStarRE
(commit 507e8122, 2026-08-25) by scripts/vendor-lidt.py; do not edit by hand.
Upstream path: MIPStarRE/LDT/Commutativity/EvaluatedSliceCommutation/Consequences.lean
-/
/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE, with the
authors' permission. Vendored from https://github.com/LionSR/MIPStarRE
(commit 507e8122, 2026-08-25) by scripts/vendor-lidt.py; do not edit by hand.
Upstream path: MIPStarRE/LDT/Commutativity/ScalarApproximation/ProcessedG/PhaseTwo.lean
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/LIDT/MIPStarRE/LDT/Commutativity/ScalarApproximation/ProcessedG/MainChain.lean (solution of MIPStarRE.LDT.Commutativity.evaluatedSlice_scalar_chain_bound);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Algebra.Algebra.Hom
import Mathlib.Algebra.Algebra.NonUnitalHom
import Mathlib.Algebra.Algebra.Spectrum.Quasispectrum
import Mathlib.Algebra.BigOperators.Field
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
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.MvPolynomial.Polynomial
import Mathlib.Algebra.MvPolynomial.Rename
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
import Mathlib.Data.Multiset.MapFold
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Cast.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Cast.Order.Basic
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Nat.Init
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Nat.SuccPred
import Mathlib.Data.Prod.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Star
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
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.CancelDenoms.Core
import Mathlib.Tactic.FieldSimp.Lemmas
import Mathlib.Tactic.Linarith.Lemmas
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
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_CommutativityPoints_SharedHelpers_SharedLine
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_CommutativityPoints_BridgeTheorems_DropBridges
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Commutativity_GCommStability_Scalar_RawSecond
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Commutativity_ScalarApproximation_PaperChainPhaseFive
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Commutativity_GCommStability_Scalar_First
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Commutativity_ScalarApproximation_ProcessedG_PhaseTwo
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Commutativity_ScalarApproximation_ProcessedG_MainChain
import Theorems.Thm_MIPStarRE_LDT_Commutativity_evaluatedSliceCommutation_avg_swap_terms
import Theorems.Thm_MIPStarRE_LDT_Commutativity_evaluatedSlice_phaseEight_tail_bound
import Theorems.Thm_MIPStarRE_LDT_Commutativity_evaluatedSlice_phaseFivePaper_avg_diff_eq_neg_orderedDefect
import Theorems.Thm_MIPStarRE_LDT_Commutativity_evaluatedSlice_phaseFivePaper_reindex_to_raw_defect
import Theorems.Thm_MIPStarRE_LDT_Commutativity_evaluatedSlice_phaseNine_tail_bound
import Theorems.Thm_MIPStarRE_LDT_Commutativity_evaluatedSlice_phaseOne_insert_bound
import Theorems.Thm_MIPStarRE_LDT_Commutativity_evaluatedSlice_phaseSixSeven_reverse_bound
import Theorems.Thm_MIPStarRE_LDT_Commutativity_evaluatedSlice_phaseTwo_avg_diff_eq_neg_questionDefect
import Theorems.Thm_MIPStarRE_LDT_Commutativity_evaluatedSlice_phaseTwo_questionDefect_avg_eq_stabilityDefect
import Theorems.Thm_MIPStarRE_LDT_Commutativity_gCommStabilityTwo_raw_scalar
import Theorems.Thm_MIPStarRE_LDT_Commutativity_gCommStability_scalar
import Theorems.Thm_MIPStarRE_LDT_Commutativity_leftRightTensor_prefix_pointMeasurement_normalization
import Theorems.Thm_MIPStarRE_LDT_Preliminaries_closenessOfIP
import Theorems.Thm_MIPStarRE_LDT_Preliminaries_consSubMeas
import Theorems.Thm_MIPStarRE_LDT_SubMeas_total_nonneg
import Theorems.Thm_MIPStarRE_LDT_avgOver_congr
import Theorems.Thm_MIPStarRE_LDT_avgOver_uniform_fst
import Theorems.Thm_MIPStarRE_LDT_consRel_symm_of_density_fixed
import Theorems.Thm_MIPStarRE_LDT_leftTensor_mul_rightTensor_eq_opTensor
import Theorems.Thm_MIPStarRE_LDT_opTensor_mul
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

namespace MIPStarRE.LDT
section
open scoped BigOperators MatrixOrder Matrix ComplexOrder
set_option backward.isDefEq.respectTransparency false
/-- Averaging a function depending only on the second coordinate marginalizes a uniform product. -/
theorem avgOver_uniform_snd {α β : Type*}
    [Fintype α] [DecidableEq α] [Nonempty α]
    [Fintype β] [DecidableEq β] [Nonempty β]
    (f : β → Error) :
    avgOver (uniformDistribution (α × β)) (fun ab => f ab.2) =
      avgOver (uniformDistribution β) f := by
  simpa using (avgOver_uniform_equiv_snd (e := Equiv.refl (α × β)) (f := f))
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
/-- The point-consistency relation written in local evaluated-point-family
notation. -/
lemma evaluatedPointFamily_pointConsistency
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (zeta : Error)
    (hcons : family.ConsistentWithPoints strategy zeta) :
    ConsRel strategy.state
      (uniformDistribution (Point params.next))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
      (evaluatedPointFamily params family)
      zeta := by
  simpa [evaluatedPointFamily] using hcons.pointConsistency
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
/-- The evaluated-point consistency relation with the two families swapped.
This is the orientation needed by `Preliminaries.consSubMeas`, whose
submeasurement input comes first. -/
lemma evaluatedPointFamily_pointConsistency_swapped
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (zeta : Error)
    (hcons : family.ConsistentWithPoints strategy zeta) :
    ConsRel strategy.state
      (uniformDistribution (Point params.next))
      (evaluatedPointFamily params family)
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
      zeta := by
  exact
    consRel_symm_of_density_fixed strategy.state strategy.densityFixed
      (uniformDistribution (Point params.next))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
      (evaluatedPointFamily params family)
      zeta
      (evaluatedPointFamily_pointConsistency params strategy family zeta hcons)
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
/-- Pull a single-point evaluated-family self-consistency bound up to the first
coordinate of an evaluated-slice question. -/
lemma evaluatedPointSelfConsistency_fst
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι)
    (zeta : Error)
    (hssc : SDDRel strategy.state
      (uniformDistribution (Point params.next))
      (evaluatedPointFamilyLeft params family)
      (evaluatedPointFamilyRight params family)
      zeta) :
    SDDRel strategy.state
      (uniformDistribution (EvaluatedSliceQuestion params))
      (fun q => evaluatedPointFamilyLeft params family q.1)
      (fun q => evaluatedPointFamilyRight params family q.1)
      zeta := by
  rcases hssc with ⟨h⟩
  constructor
  simpa [sddError] using
    (avgOver_uniform_fst (α := Point params.next) (β := Point params.next)
      (f := fun u =>
        qSDD strategy.state
          (evaluatedPointFamilyLeft params family u)
          (evaluatedPointFamilyRight params family u))).trans_le h
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
/-- Pull a single-point evaluated-family self-consistency bound up to the second
coordinate of an evaluated-slice question. -/
lemma evaluatedPointSelfConsistency_snd
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι)
    (zeta : Error)
    (hssc : SDDRel strategy.state
      (uniformDistribution (Point params.next))
      (evaluatedPointFamilyLeft params family)
      (evaluatedPointFamilyRight params family)
      zeta) :
    SDDRel strategy.state
      (uniformDistribution (EvaluatedSliceQuestion params))
      (fun q => evaluatedPointFamilyLeft params family q.2)
      (fun q => evaluatedPointFamilyRight params family q.2)
      zeta := by
  rcases hssc with ⟨h⟩
  constructor
  simpa [sddError] using
    (avgOver_uniform_snd (α := Point params.next) (β := Point params.next)
      (f := fun u =>
        qSDD strategy.state
          (evaluatedPointFamilyLeft params family u)
          (evaluatedPointFamilyRight params family u))).trans_le h
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
/-- Direct `√ζ` control of the phase-2 stability defect.

The remaining bridge from the explicit evaluated-slice difference to this
one-dimensional defect is pure finite reindexing and averaging: expand
`totalSandwichFamily`, decompose the sampled second point as `(v,y)`, collect the
postprocessing fiber `∑_b ∑_{g : g(v)=b}` into `∑_g`, and average the first
sampled point into `gCommStabilityR`. -/
lemma evaluatedSlice_phaseTwo_stability_defect_bound
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (zeta : Error)
    (hnorm : strategy.state.IsNormalized)
    (family : IdxPolyFamily params ι)
    (G : Fq params → SubMeas (Polynomial params) ι)
    (hG : ∀ x, G x = (family.meas x).toSubMeas)
    (hbound : IdxPolyFamily.SliceBoundednessInput strategy family zeta) :
    |avgOver (uniformDistribution (Fq params))
      (evaluatedSlicePhaseTwoStabilityDefect params strategy family G)| ≤ Real.sqrt zeta := by
  have hdef :
      evaluatedSlicePhaseTwoStabilityDefect params strategy family G =
        gCommStabilityScalarDefect params strategy family G := by
    funext y
    try rfl -- vendoring compile fix (Lean v4.33): the previous step may close the goal
  rw [hdef]
  exact gCommStability_scalar params strategy zeta hnorm family G hG hbound
end
end MIPStarRE.LDT.Commutativity

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPStarRE.LDT.Commutativity
open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open MIPStarRE.LDT.GlobalVariance (PointPairQuestion)
open scoped BigOperators MatrixOrder Matrix ComplexOrder
set_option backward.isDefEq.respectTransparency false
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
theorem _root_.solution
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (gamma zeta : Error)
    (_hnorm : strategy.state.IsNormalized)
    (_hcomm :
      SDDOpRel strategy.state
        (uniformDistribution (PointPairQuestion params.next))
        (pointMeasurementProductLeft params.next strategy)
        (pointMeasurementProductRight params.next strategy)
        (commutativityPointsError params.next gamma))
    (_hgamma_nonneg : 0 ≤ gamma)
    (family : IdxPolyFamily params ι)
    (G : Fq params → SubMeas (Polynomial params) ι)
    (_hG : ∀ x, G x = (family.meas x).toSubMeas)
    (_hcons : family.ConsistentWithPoints strategy zeta)
    (_hself : family.StronglySelfConsistent strategy.state zeta)
    (_hbound : IdxPolyFamily.SliceBoundednessInput strategy family zeta)
    (_hpostSSC : SDDRel strategy.state
      (uniformDistribution (Point params.next))
      (evaluatedPointFamilyLeft params family)
      (evaluatedPointFamilyRight params family)
      zeta) :
    2 *
      (avgOver (uniformDistribution (EvaluatedSliceQuestion params))
          (fun q => ∑ ab : EvaluatedSliceOutcome params,
            evaluatedSliceABATerm params strategy family q ab) -
        avgOver (uniformDistribution (EvaluatedSliceQuestion params))
          (fun q => ∑ ab : EvaluatedSliceOutcome params,
            evaluatedSliceABABTerm params strategy family q ab)) ≤
      commDataProcessedGError params gamma zeta := by
  -- Paper reference: commutativity-G.tex, proof of lem:comm-data-processed-g,
  -- equations (eq:gcom8) through the final displayed error estimate.
  -- Each step uses closenessOfIP, easyApproxFromApproxDelta, or the
  -- stability claims (clm:g-comm-stability, clm:g-comm-stability2).
  -- The algebraic qSDDOp expansions and stability families are defined
  -- in Commutativity/Defs.lean; the Cauchy-Schwarz bridges are in
  -- Preliminaries/CauchySchwarz.lean.
  have h𝒟 :
      ∑ q ∈ (uniformDistribution (EvaluatedSliceQuestion params)).support,
        (uniformDistribution (EvaluatedSliceQuestion params)).weight q ≤ 1 := by
    simpa using
      uniformDistribution_weight_sum_le_one (EvaluatedSliceQuestion params)
  have hpostSSC_fst :=
    evaluatedPointSelfConsistency_fst params strategy family zeta _hpostSSC
  have hpostSSC_snd :=
    evaluatedPointSelfConsistency_snd params strategy family zeta _hpostSSC
  let 𝒟 : Distribution (EvaluatedSliceQuestion params) :=
    uniformDistribution (EvaluatedSliceQuestion params)
  let avgABAB : EvaluatedSliceQuestion params → Error := fun q =>
    ∑ ab : EvaluatedSliceOutcome params,
      evaluatedSliceABABTerm params strategy family q ab
  let avgABA : EvaluatedSliceQuestion params → Error := fun q =>
    ∑ ab : EvaluatedSliceOutcome params,
      evaluatedSliceABATerm params strategy family q ab
  let avgBAB : EvaluatedSliceQuestion params → Error := fun q =>
    ∑ ab : EvaluatedSliceOutcome params,
      evaluatedSliceBABTerm params strategy family q ab
  let pointMeas : IdxMeas (Point params.next) (Fq params) ι :=
    fun u => by
      simpa [Parameters.next] using (strategy.pointMeasurement u).toMeasurement
  have hcons_swapped :=
    evaluatedPointFamily_pointConsistency_swapped params strategy family zeta _hcons
  have hconsSub :=
    MIPStarRE.LDT.Preliminaries.consSubMeas
      strategy.state
      (uniformDistribution (Point params.next))
      (evaluatedPointFamily params family)
      pointMeas
      zeta
      hcons_swapped
  have hcombined_snd :
      SDDRel strategy.state
        (uniformDistribution (EvaluatedSliceQuestion params))
        (fun q => evaluatedPointFamilyLeft params family q.2)
        (fun q =>
          (MIPStarRE.LDT.Preliminaries.totalSandwichFamily
            (evaluatedPointFamily params family)
            pointMeas q.2))
        (4 * zeta) := by
    rcases hconsSub.combinedControl with ⟨h⟩
    constructor
    simpa [sddError, qSDD, evaluatedPointFamilyLeft, IdxSubMeas.liftLeft,
      leftPlacedSubMeas] using
      (avgOver_uniform_snd (α := Point params.next) (β := Point params.next)
        (f := fun u =>
          qSDD strategy.state
            ((IdxSubMeas.liftLeft (evaluatedPointFamily params family)) u)
            ((MIPStarRE.LDT.Preliminaries.totalSandwichFamily
              (evaluatedPointFamily params family)
              pointMeas u)))).trans_le h
  have hcombined_fst :
      SDDRel strategy.state
        (uniformDistribution (EvaluatedSliceQuestion params))
        (fun q => evaluatedPointFamilyLeft params family q.1)
        (fun q =>
          (MIPStarRE.LDT.Preliminaries.totalSandwichFamily
            (evaluatedPointFamily params family)
            pointMeas q.1))
        (4 * zeta) := by
    rcases hconsSub.combinedControl with ⟨h⟩
    constructor
    simpa [sddError, qSDD, evaluatedPointFamilyLeft, IdxSubMeas.liftLeft,
      leftPlacedSubMeas] using
      (avgOver_uniform_fst (α := Point params.next) (β := Point params.next)
        (f := fun u =>
          qSDD strategy.state
            ((IdxSubMeas.liftLeft (evaluatedPointFamily params family)) u)
            ((MIPStarRE.LDT.Preliminaries.totalSandwichFamily
              (evaluatedPointFamily params family)
              pointMeas u)))).trans_le h
  let phase1Inserted : EvaluatedSliceQuestion params → Error := fun q =>
    ∑ b : Fq params, ∑ a : Fq params,
      ev strategy.state
        (leftTensor (ι₂ := ι)
            (((evaluatedSliceFirstFactor params family q).outcome a) *
              ((evaluatedSliceSecondFactor params family q).outcome b) *
              ((evaluatedSliceFirstFactor params family q).outcome a)) *
          ((MIPStarRE.LDT.Preliminaries.totalSandwichFamily
            (evaluatedPointFamily params family)
            (evaluatedSlicePointMeas params strategy) q.2).outcome b))
  let phase3Inserted : EvaluatedSliceQuestion params → Error := fun q =>
    ∑ a : Fq params, ∑ b : Fq params,
      ev strategy.state
        (leftTensor (ι₂ := ι)
            (((evaluatedSliceSecondFactor params family q).outcome b) *
              ((evaluatedSliceFirstFactor params family q).outcome a) *
              ((evaluatedSliceSecondFactor params family q).outcome b)) *
          ((MIPStarRE.LDT.Preliminaries.totalSandwichFamily
            (evaluatedPointFamily params family)
            (evaluatedSlicePointMeas params strategy) q.1).outcome a))
  let phase2Removed : EvaluatedSliceQuestion params → Error := fun q =>
    ∑ b : Fq params, ∑ a : Fq params,
      ev strategy.state
        (leftTensor (ι₂ := ι)
            (((evaluatedSliceFirstFactor params family q).outcome a) *
              ((evaluatedSliceSecondFactor params family q).outcome b) *
              ((evaluatedSliceFirstFactor params family q).outcome a)) *
          rightTensor (ι₁ := ι) ((evaluatedSlicePointMeas params strategy q.2).outcome b))
  -- Paper line 86: insert the first-coordinate point measurement after `gcom9`.
  -- Unfolding `totalSandwichFamily`, this is the average of
  -- `G^{u,x}_a G^{v,y}_b G^x ⊗ A^{v,y}_b A^{u,x}_a`.
  let phase3PaperInserted : EvaluatedSliceQuestion params → Error := fun q =>
    ∑ a : Fq params, ∑ b : Fq params,
      ev strategy.state
        ((leftTensor (ι₂ := ι)
            (((evaluatedSliceFirstFactor params family q).outcome a) *
              ((evaluatedSliceSecondFactor params family q).outcome b)) *
            rightTensor (ι₁ := ι)
              ((evaluatedSlicePointMeas params strategy q.2).outcome b)) *
          ((MIPStarRE.LDT.Preliminaries.totalSandwichFamily
            (evaluatedPointFamily params family)
            (evaluatedSlicePointMeas params strategy) q.1).outcome a))
  -- Paper line 87: swap the two right-register point measurements.
  let phase4PaperSwapped : EvaluatedSliceQuestion params → Error := fun q =>
    ∑ a : Fq params, ∑ b : Fq params,
      ev strategy.state
        (leftTensor (ι₂ := ι)
            (((evaluatedSliceFirstFactor params family q).outcome a) *
              ((evaluatedSliceSecondFactor params family q).outcome b) *
              (evaluatedSliceFirstFactor params family q).total) *
          rightTensor (ι₁ := ι)
            (((evaluatedSlicePointMeas params strategy q.1).outcome a) *
              ((evaluatedSlicePointMeas params strategy q.2).outcome b)))
  -- Paper line 87 after removing the trailing first-slice total `G^x`.
  let phase5PaperRemoved : EvaluatedSliceQuestion params → Error :=
    evaluatedSlicePhaseFivePaperRemoved params strategy family
  -- Paper lines 101--119 endpoints for the reverse insertions and tail.
  let phase7GonnaCite : EvaluatedSliceQuestion params → Error :=
    evaluatedSlicePhaseSevenGonnaCite params strategy family
  let phase8TailRight : EvaluatedSliceQuestion params → Error :=
    evaluatedSlicePhaseEightTailRight params strategy family
  -- Phase 1: `eq:gcom8 -> eq:apply-add-an-a-once`.
  have hphase1 :
      |avgOver 𝒟 avgABAB - avgOver 𝒟 phase1Inserted| ≤ 2 * Real.sqrt zeta := by
    simpa [𝒟, avgABAB, phase1Inserted] using
      evaluatedSlice_phaseOne_insert_bound
        params strategy zeta _hnorm family hcombined_snd
  -- Phase 2: remove the trailing `G^y` from the phase-1 inserted term via the
  -- direct boundedness estimate `gCommStability_scalar`.
  -- The analytic part is closed by `evaluatedSlice_phaseTwo_stability_defect_bound`,
  -- the sign/algebra expansion is proved by
  -- `evaluatedSlice_phaseTwo_avg_diff_eq_neg_questionDefect`, and the finite
  -- marginalization below identifies the question-level defect with
  -- `evaluatedSlicePhaseTwoStabilityDefect`: decompose the sampled second point as
  -- `(v,y)`, collapse the postprocessing fibers `∑_b ∑_{g : g(v)=b}` to `∑_g`,
  -- then average the first sampled point into `gCommStabilityR`.
  have hphase2 :
      |avgOver 𝒟 phase1Inserted - avgOver 𝒟 phase2Removed| ≤ Real.sqrt zeta := by
    have hdefect :=
      evaluatedSlice_phaseTwo_stability_defect_bound
        params strategy zeta _hnorm family G _hG _hbound
    have hsign :
        avgOver 𝒟 phase1Inserted - avgOver 𝒟 phase2Removed =
          -avgOver 𝒟 (evaluatedSlicePhaseTwoQuestionDefect params strategy family G) := by
      simpa [𝒟, phase1Inserted, phase2Removed] using
        evaluatedSlice_phaseTwo_avg_diff_eq_neg_questionDefect
          params strategy family G _hG
    have hbridge :
        avgOver 𝒟 (evaluatedSlicePhaseTwoQuestionDefect params strategy family G) =
          avgOver (uniformDistribution (Fq params))
            (evaluatedSlicePhaseTwoStabilityDefect params strategy family G) := by
      simpa [𝒟] using
        evaluatedSlice_phaseTwo_questionDefect_avg_eq_stabilityDefect
          params strategy family G
    have hrewrite :
        avgOver 𝒟 phase1Inserted - avgOver 𝒟 phase2Removed =
          -avgOver (uniformDistribution (Fq params))
            (evaluatedSlicePhaseTwoStabilityDefect params strategy family G) := by
      calc
        avgOver 𝒟 phase1Inserted - avgOver 𝒟 phase2Removed
            = -avgOver 𝒟
                (evaluatedSlicePhaseTwoQuestionDefect params strategy family G) := hsign
        _ = -avgOver (uniformDistribution (Fq params))
                (evaluatedSlicePhaseTwoStabilityDefect params strategy family G) := by
              rw [hbridge]
    calc
      |avgOver 𝒟 phase1Inserted - avgOver 𝒟 phase2Removed|
          = |-(avgOver (uniformDistribution (Fq params))
              (evaluatedSlicePhaseTwoStabilityDefect params strategy family G))| := by
              rw [hrewrite]
      _ = |avgOver (uniformDistribution (Fq params))
              (evaluatedSlicePhaseTwoStabilityDefect params strategy family G)| := by
              rw [abs_neg]
      _ ≤ Real.sqrt zeta := hdefect
  -- Paper line 86, first approximation: insert the first-coordinate
  -- `G^x \otimes A^{u,x}_a` endpoint into the post-`gcom9` expression.
  have hphase3paper :
      |avgOver 𝒟 phase2Removed - avgOver 𝒟 phase3PaperInserted| ≤
        2 * Real.sqrt zeta := by
    let A : EvaluatedSliceQuestion params → Fq params → MIPStarRE.Quantum.Op (ι × ι) :=
      fun q a => leftTensor (ι₂ := ι) ((evaluatedSliceFirstFactor params family q).outcome a)
    let B : EvaluatedSliceQuestion params → Fq params → MIPStarRE.Quantum.Op (ι × ι) :=
      fun q a =>
        ((MIPStarRE.LDT.Preliminaries.totalSandwichFamily
          (evaluatedPointFamily params family)
          (evaluatedSlicePointMeas params strategy) q.1).outcome a)
    let C : EvaluatedSliceQuestion params → Fq params → Fq params →
        MIPStarRE.Quantum.Op (ι × ι) :=
      fun q a b =>
        leftTensor (ι₂ := ι)
            (((evaluatedSliceFirstFactor params family q).outcome a) *
              ((evaluatedSliceSecondFactor params family q).outcome b)) *
          rightTensor (ι₁ := ι)
            ((evaluatedSlicePointMeas params strategy q.2).outcome b)
    have hAB :
        avgOver 𝒟 (fun q => qSDDCore strategy.state (A q) (B q)) ≤ 4 * zeta := by
      have hbound := hcombined_fst.squaredDistanceBound
      change avgOver 𝒟 (fun q => qSDDCore strategy.state (A q) (B q)) ≤
        4 * zeta at hbound
      exact hbound
    have hC :
        ∀ q, ∑ a : Fq params, (∑ b : Fq params, C q a b) * (∑ b : Fq params, C q a b)ᴴ ≤ 1 := by
      intro q
      simpa [C, evaluatedSlicePointMeas, Parameters.next] using
        (leftRightTensor_prefix_pointMeasurement_normalization
          (A := evaluatedSliceFirstFactor params family q)
          (B := evaluatedSliceSecondFactor params family q)
          (R := strategy.pointMeasurement q.2))
    have hremoved :
        avgOver 𝒟 phase2Removed =
          avgOver 𝒟 (fun q => ∑ a : Fq params, ∑ b : Fq params,
            ev strategy.state (C q a b * A q a)) := by
      apply avgOver_congr
      intro q
      dsimp [phase2Removed, A, C]
      rw [Finset.sum_comm]
      simp [opTensor_mul, mul_assoc]
    have hinserted :
        avgOver 𝒟 phase3PaperInserted =
          avgOver 𝒟 (fun q => ∑ a : Fq params, ∑ b : Fq params,
            ev strategy.state (C q a b * B q a)) := by
      try rfl -- vendoring compile fix (Lean v4.33): the previous step may close the goal
    have hclose :=
      MIPStarRE.LDT.Preliminaries.closenessOfIP
        strategy.state _hnorm 𝒟 h𝒟 A B C (4 * zeta) hAB hC
    calc
      |avgOver 𝒟 phase2Removed - avgOver 𝒟 phase3PaperInserted|
          = |avgOver 𝒟 (fun q => ∑ a : Fq params, ∑ b : Fq params,
              ev strategy.state (C q a b * A q a)) -
            avgOver 𝒟 (fun q => ∑ a : Fq params, ∑ b : Fq params,
              ev strategy.state (C q a b * B q a))| := by
              rw [hremoved, hinserted]
      _ ≤ Real.sqrt (4 * zeta) := hclose
      _ = 2 * Real.sqrt zeta := by
            rw [Real.sqrt_mul (show 0 ≤ (4 : Error) by positivity)]
            norm_num
  -- Paper line 87: commute the two right-register point measurements.
  -- The `6√(γ(m+1))` bound comes from `commutativityPoints` via `closenessOfIP`:
  -- the SDDOpRel error is `32·γ·(m+1)`, applying `closenessOfIP` gives
  -- `√(32·γ·(m+1))`, and `√32 ≤ 6` rounds up to match the paper's constant.
  have hphase4paper :
      |avgOver 𝒟 phase3PaperInserted - avgOver 𝒟 phase4PaperSwapped| ≤
        6 * Real.sqrt (gamma * (((params.m + 1 : ℕ)) : Error)) := by
    let C : EvaluatedSliceQuestion params → EvaluatedSliceOutcome params →
        MIPStarRE.Quantum.Op (ι × ι) :=
      evaluatedSlicePointSwapRightPrefix (ι := ι) params family (fun q =>
        (evaluatedSliceFirstFactor params family q).total)
    have hC :
        ∀ q, ∑ ab : EvaluatedSliceOutcome params, C q ab * (C q ab)ᴴ ≤ 1 := by
      simpa [C] using
        evaluatedSlice_pointSwap_right_prefix_normalization
          (ι := ι) params family
          (fun q => (evaluatedSliceFirstFactor params family q).total)
          (fun q => (evaluatedSliceFirstFactor params family q).total_nonneg)
          (fun q => (evaluatedSliceFirstFactor params family q).total_le_one)
    have hphase3_norm :
        avgOver 𝒟 phase3PaperInserted =
          avgOver 𝒟 (fun q => ∑ ab : EvaluatedSliceOutcome params,
            ev strategy.state
              (C q ab *
                rightTensor (ι₁ := ι)
                  (((evaluatedSlicePointMeas params strategy q.2).outcome ab.2) *
                    ((evaluatedSlicePointMeas params strategy q.1).outcome ab.1)))) := by
      apply avgOver_congr
      intro q
      calc
        phase3PaperInserted q =
            ∑ a : Fq params, ∑ b : Fq params,
              ev strategy.state
                (C q (a, b) *
                  rightTensor (ι₁ := ι)
                    (((evaluatedSlicePointMeas params strategy q.2).outcome b) *
                      ((evaluatedSlicePointMeas params strategy q.1).outcome a))) := by
              dsimp [phase3PaperInserted, C, evaluatedSlicePointSwapRightPrefix]
              refine Finset.sum_congr rfl ?_
              intro a _
              refine Finset.sum_congr rfl ?_
              intro b _
              congr 1
              simp [MIPStarRE.LDT.Preliminaries.totalSandwichFamily,
                evaluatedSliceFirstFactor, opTensor_mul, mul_assoc]
        _ = ∑ ab : EvaluatedSliceOutcome params,
              ev strategy.state
                (C q ab *
                  rightTensor (ι₁ := ι)
                    (((evaluatedSlicePointMeas params strategy q.2).outcome ab.2) *
                      ((evaluatedSlicePointMeas params strategy q.1).outcome ab.1))) := by
              simpa using
                (Fintype.sum_prod_type' (f := fun a : Fq params => fun b : Fq params =>
                  ev strategy.state
                    (C q (a, b) *
                      rightTensor (ι₁ := ι)
                        (((evaluatedSlicePointMeas params strategy q.2).outcome b) *
                          ((evaluatedSlicePointMeas params strategy q.1).outcome a))))).symm
    have hphase4_norm :
        avgOver 𝒟 phase4PaperSwapped =
          avgOver 𝒟 (fun q => ∑ ab : EvaluatedSliceOutcome params,
            ev strategy.state
              (C q ab *
                rightTensor (ι₁ := ι)
                  (((evaluatedSlicePointMeas params strategy q.1).outcome ab.1) *
                    ((evaluatedSlicePointMeas params strategy q.2).outcome ab.2)))) := by
      apply avgOver_congr
      intro q
      dsimp [phase4PaperSwapped, C, evaluatedSlicePointSwapRightPrefix]
      simpa using
        (Fintype.sum_prod_type' (f := fun a : Fq params => fun b : Fq params =>
          ev strategy.state
            (leftTensor (ι₂ := ι)
                (((evaluatedSliceFirstFactor params family q).outcome a) *
                  ((evaluatedSliceSecondFactor params family q).outcome b) *
                  (evaluatedSliceFirstFactor params family q).total) *
              rightTensor (ι₁ := ι)
                (((evaluatedSlicePointMeas params strategy q.1).outcome a) *
                  ((evaluatedSlicePointMeas params strategy q.2).outcome b))))).symm
    exact
      evaluatedSlice_pointSwap_right_bound_of_norms
        params strategy gamma _hnorm _hcomm C hC
        phase3PaperInserted phase4PaperSwapped hphase3_norm hphase4_norm
  -- Paper phase five: remove the trailing `G^x` total from the line-87 endpoint.
  -- The `√ζ + 6√(γ(m+1))` bound decomposes as:
  --   - `√ζ` from `gCommStabilityTwo_raw_scalar` (the boundedness part of
  --     `clm:g-comm-stability2`, corresponding to the paper's line 93 `≈_{√ζ}`)
  --   - `6√(γ(m+1))` from swapping the right-register point measurements
  --     inside the phase-5 defect (same `commutativityPoints` →
  --     `closenessOfIP` → `√32 ≤ 6` chain as Phase 4).
  -- The ordered defect is first swapped on the right register, then reindexed to
  -- `gCommStabilityTwoRawScalarDefect`, whose average is controlled by the new
  -- raw scalar stability theorem.
  have hphase5paper :
      |avgOver 𝒟 phase4PaperSwapped - avgOver 𝒟 phase5PaperRemoved| ≤
        Real.sqrt zeta + 6 * Real.sqrt (gamma * (((params.m + 1 : ℕ)) : Error)) := by
    let orderedDefect : EvaluatedSliceQuestion params → Error :=
      evaluatedSlicePhaseFivePaperOrderedDefect params strategy family G
    let swappedDefect : EvaluatedSliceQuestion params → Error :=
      evaluatedSlicePhaseFivePaperSwappedDefect params strategy family G
    have hsign :
        avgOver 𝒟 phase4PaperSwapped - avgOver 𝒟 phase5PaperRemoved =
          -avgOver 𝒟 orderedDefect := by
      simpa [𝒟, phase4PaperSwapped, phase5PaperRemoved, orderedDefect] using
        evaluatedSlice_phaseFivePaper_avg_diff_eq_neg_orderedDefect
          params strategy family G _hG
    have hraw : |avgOver 𝒟 swappedDefect| ≤ Real.sqrt zeta := by
      have hraw0 :=
        gCommStabilityTwo_raw_scalar
          params strategy zeta _hnorm family G _hG _hbound
      have hreindex :
          avgOver 𝒟 swappedDefect =
            avgOver (uniformDistribution (Fq params))
              (gCommStabilityTwoRawScalarDefect params strategy family G) := by
        simpa [𝒟, swappedDefect] using
          evaluatedSlice_phaseFivePaper_reindex_to_raw_defect
            params strategy family G _hG
      calc
        |avgOver 𝒟 swappedDefect|
            = |avgOver (uniformDistribution (Fq params))
                (gCommStabilityTwoRawScalarDefect params strategy family G)| := by
              rw [hreindex]
        _ ≤ Real.sqrt zeta := hraw0
    have hswap_defect :
        |avgOver 𝒟 orderedDefect - avgOver 𝒟 swappedDefect| ≤
          6 * Real.sqrt (gamma * (((params.m + 1 : ℕ)) : Error)) := by
      let C : EvaluatedSliceQuestion params → EvaluatedSliceOutcome params →
          MIPStarRE.Quantum.Op (ι × ι) :=
        evaluatedSlicePointSwapRightPrefix (ι := ι) params family (fun q =>
          (1 : MIPStarRE.Quantum.Op ι) - (G (pointHeight params q.1)).total)
      have hT_nonneg : ∀ q : EvaluatedSliceQuestion params,
          0 ≤ (1 : MIPStarRE.Quantum.Op ι) - (G (pointHeight params q.1)).total := by
        intro q
        exact sub_nonneg.mpr (G (pointHeight params q.1)).total_le_one
      have hT_le_one : ∀ q : EvaluatedSliceQuestion params,
          (1 : MIPStarRE.Quantum.Op ι) - (G (pointHeight params q.1)).total ≤ 1 := by
        intro q
        simpa using
          (sub_le_self (1 : MIPStarRE.Quantum.Op ι)
            (G (pointHeight params q.1)).total_nonneg)
      have hC :
          ∀ q, ∑ ab : EvaluatedSliceOutcome params, C q ab * (C q ab)ᴴ ≤ 1 := by
        simpa [C] using
          evaluatedSlice_pointSwap_right_prefix_normalization
            (ι := ι) params family
            (fun q => (1 : MIPStarRE.Quantum.Op ι) - (G (pointHeight params q.1)).total)
            hT_nonneg hT_le_one
      have hord_norm :
          avgOver 𝒟 orderedDefect =
            avgOver 𝒟 (fun q => ∑ ab : EvaluatedSliceOutcome params,
              ev strategy.state
                (C q ab *
                  rightTensor (ι₁ := ι)
                    (((evaluatedSlicePointMeas params strategy q.1).outcome ab.1) *
                      ((evaluatedSlicePointMeas params strategy q.2).outcome ab.2)))) := by
        apply avgOver_congr
        intro q
        dsimp [orderedDefect, evaluatedSlicePhaseFivePaperOrderedDefect, C,
          evaluatedSlicePointSwapRightPrefix]
        simpa using
          (Fintype.sum_prod_type' (f := fun a : Fq params => fun b : Fq params =>
            ev strategy.state
              (leftTensor (ι₂ := ι)
                  (((evaluatedSliceFirstFactor params family q).outcome a) *
                    ((evaluatedSliceSecondFactor params family q).outcome b) *
                    (1 - (G (pointHeight params q.1)).total)) *
                rightTensor (ι₁ := ι)
                  (((evaluatedSlicePointMeas params strategy q.1).outcome a) *
                    ((evaluatedSlicePointMeas params strategy q.2).outcome b))))).symm
      have hswap_norm :
          avgOver 𝒟 swappedDefect =
            avgOver 𝒟 (fun q => ∑ ab : EvaluatedSliceOutcome params,
              ev strategy.state
                (C q ab *
                  rightTensor (ι₁ := ι)
                    (((evaluatedSlicePointMeas params strategy q.2).outcome ab.2) *
                      ((evaluatedSlicePointMeas params strategy q.1).outcome ab.1)))) := by
        apply avgOver_congr
        intro q
        dsimp [swappedDefect, evaluatedSlicePhaseFivePaperSwappedDefect, C,
          evaluatedSlicePointSwapRightPrefix]
        simpa using
          (Fintype.sum_prod_type' (f := fun a : Fq params => fun b : Fq params =>
            ev strategy.state
              (leftTensor (ι₂ := ι)
                  (((evaluatedSliceFirstFactor params family q).outcome a) *
                    ((evaluatedSliceSecondFactor params family q).outcome b) *
                    (1 - (G (pointHeight params q.1)).total)) *
                rightTensor (ι₁ := ι)
                  (((evaluatedSlicePointMeas params strategy q.2).outcome b) *
                    ((evaluatedSlicePointMeas params strategy q.1).outcome a))))).symm
      have hswap :=
        evaluatedSlice_pointSwap_right_bound_of_norms
          params strategy gamma _hnorm _hcomm C hC
          swappedDefect orderedDefect hswap_norm hord_norm
      simpa [abs_sub_comm] using hswap
    have hordered_abs :
        |avgOver 𝒟 orderedDefect| ≤
          Real.sqrt zeta + 6 * Real.sqrt (gamma * (((params.m + 1 : ℕ)) : Error)) := by
      calc
        |avgOver 𝒟 orderedDefect|
            = |avgOver 𝒟 orderedDefect - 0| := by simp
        _ ≤ |avgOver 𝒟 orderedDefect - avgOver 𝒟 swappedDefect| +
              |avgOver 𝒟 swappedDefect - 0| :=
                abs_sub_le (avgOver 𝒟 orderedDefect) (avgOver 𝒟 swappedDefect) 0
        _ ≤ 6 * Real.sqrt (gamma * (((params.m + 1 : ℕ)) : Error)) + Real.sqrt zeta := by
                exact add_le_add hswap_defect (by simpa using hraw)
        _ = Real.sqrt zeta + 6 * Real.sqrt (gamma * (((params.m + 1 : ℕ)) : Error)) := by
                ring
    calc
      |avgOver 𝒟 phase4PaperSwapped - avgOver 𝒟 phase5PaperRemoved|
          = |-(avgOver 𝒟 orderedDefect)| := by
              rw [hsign]
      _ = |avgOver 𝒟 orderedDefect| := by rw [abs_neg]
      _ ≤ Real.sqrt zeta + 6 * Real.sqrt (gamma * (((params.m + 1 : ℕ)) : Error)) :=
              hordered_abs
  -- Paper lines 99--104: reverse the two `eq:add-an-a` insertions.
  have hphase67paper :
      |avgOver 𝒟 phase5PaperRemoved - avgOver 𝒟 phase7GonnaCite| ≤
        4 * Real.sqrt zeta := by
    simpa [𝒟, phase5PaperRemoved, phase7GonnaCite] using
      evaluatedSlice_phaseSixSeven_reverse_bound
        params strategy zeta _hnorm family hcombined_fst hcombined_snd
  -- Paper line 117--118: first postprocessed self-consistency tail move.
  have htail8 :
      |avgOver 𝒟 phase7GonnaCite - avgOver 𝒟 phase8TailRight| ≤ Real.sqrt zeta := by
    simpa [𝒟, phase7GonnaCite, phase8TailRight] using
      evaluatedSlice_phaseEight_tail_bound
        params strategy zeta _hnorm family hpostSSC_snd
  -- Paper line 118--119: move that same second-coordinate factor back to the left.
  have htail9 :
      |avgOver 𝒟 phase8TailRight - avgOver 𝒟 avgBAB| ≤ Real.sqrt zeta := by
    simpa [𝒟, phase8TailRight, avgBAB] using
      evaluatedSlice_phaseNine_tail_bound
        params strategy zeta _hnorm family hpostSSC_snd
  -- ── Final assembly (hassemble) ────────────────────────────────────────────
  -- The paper chain (commutativity-G.tex, lines 72–119) converts `ABAB` to `ABA`
  -- through ten approximation steps.  In the Lean development, the chain
  -- terminates at `BAB` after Phase 4, then we apply the exact swap-symmetry
  -- identity `avgBAB = avgABA`.  This identity is an equality, not an
  -- approximation: the uniform average over evaluated-slice questions is
  -- invariant under swapping the question coordinates `(q₁,q₂)↦(q₂,q₁)`, and
  -- the corresponding relabeling of outcomes `(a,b)↦(b,a)` transforms the
  -- `BAB` term into the `ABA` term.  See
  -- `EvaluatedSliceCommutation/Averages.lean` for the proof.
  have hassemble :
      2 * (avgOver 𝒟 avgABA - avgOver 𝒟 avgABAB) ≤
        commDataProcessedGError params gamma zeta := by
    have hswap := evaluatedSliceCommutation_avg_swap_terms params strategy family
    have hBABeqABA : avgOver 𝒟 avgBAB = avgOver 𝒟 avgABA := hswap.1
    have hγζ_chain :
        avgOver 𝒟 avgBAB - avgOver 𝒟 avgABAB ≤
          12 * Real.sqrt zeta +
            12 * Real.sqrt (gamma * (((params.m + 1 : ℕ)) : Error)) := by
      have h01 : avgOver 𝒟 phase1Inserted - avgOver 𝒟 avgABAB ≤
          2 * Real.sqrt zeta := by
        exact le_trans (le_abs_self _)
          ((abs_sub_comm (avgOver 𝒟 phase1Inserted) (avgOver 𝒟 avgABAB)).symm ▸ hphase1)
      have h12 : avgOver 𝒟 phase2Removed - avgOver 𝒟 phase1Inserted ≤
          Real.sqrt zeta := by
        exact le_trans (le_abs_self _)
          ((abs_sub_comm (avgOver 𝒟 phase2Removed) (avgOver 𝒟 phase1Inserted)).symm ▸ hphase2)
      have h23 : avgOver 𝒟 phase3PaperInserted - avgOver 𝒟 phase2Removed ≤
          2 * Real.sqrt zeta := by
        have h :=
          (abs_sub_comm (avgOver 𝒟 phase3PaperInserted)
            (avgOver 𝒟 phase2Removed)).symm ▸ hphase3paper
        exact le_trans (le_abs_self _) h
      have h34 : avgOver 𝒟 phase4PaperSwapped - avgOver 𝒟 phase3PaperInserted ≤
          6 * Real.sqrt (gamma * (((params.m + 1 : ℕ)) : Error)) := by
        have h :=
          (abs_sub_comm (avgOver 𝒟 phase4PaperSwapped)
            (avgOver 𝒟 phase3PaperInserted)).symm ▸ hphase4paper
        exact le_trans (le_abs_self _) h
      have h45 : avgOver 𝒟 phase5PaperRemoved - avgOver 𝒟 phase4PaperSwapped ≤
          Real.sqrt zeta + 6 * Real.sqrt (gamma * (((params.m + 1 : ℕ)) : Error)) := by
        have h :=
          (abs_sub_comm (avgOver 𝒟 phase5PaperRemoved)
            (avgOver 𝒟 phase4PaperSwapped)).symm ▸ hphase5paper
        exact le_trans (le_abs_self _) h
      have h57 : avgOver 𝒟 phase7GonnaCite - avgOver 𝒟 phase5PaperRemoved ≤
          4 * Real.sqrt zeta := by
        have h :=
          (abs_sub_comm (avgOver 𝒟 phase7GonnaCite)
            (avgOver 𝒟 phase5PaperRemoved)).symm ▸ hphase67paper
        exact le_trans (le_abs_self _) h
      have h78 : avgOver 𝒟 phase8TailRight - avgOver 𝒟 phase7GonnaCite ≤
          Real.sqrt zeta := by
        exact le_trans (le_abs_self _)
          ((abs_sub_comm (avgOver 𝒟 phase8TailRight) (avgOver 𝒟 phase7GonnaCite)).symm ▸ htail8)
      have h89 : avgOver 𝒟 avgBAB - avgOver 𝒟 phase8TailRight ≤
          Real.sqrt zeta := by
        exact le_trans (le_abs_self _)
          ((abs_sub_comm (avgOver 𝒟 avgBAB) (avgOver 𝒟 phase8TailRight)).symm ▸ htail9)
      linarith
    have hmain_one :
        2 * (avgOver 𝒟 avgABA - avgOver 𝒟 avgABAB) ≤
          24 * Real.sqrt zeta +
            24 * Real.sqrt (gamma * (((params.m + 1 : ℕ)) : Error)) := by
      have hrw : avgOver 𝒟 avgABA - avgOver 𝒟 avgABAB =
          avgOver 𝒟 avgBAB - avgOver 𝒟 avgABAB := by
        linarith
      rw [hrw]
      nlinarith
    have hgamma_nonneg : 0 ≤ gamma := by
      exact _hgamma_nonneg
    have hzeta_nonneg : 0 ≤ zeta :=
      le_trans (sddError_nonneg strategy.state
        (uniformDistribution (Point params.next))
        (evaluatedPointFamilyLeft params family)
        (evaluatedPointFamilyRight params family)) _hpostSSC.squaredDistanceBound
    have hm : 1 ≤ (params.m : Error) := by exact_mod_cast params.hm
    have hsqrtn_le :
        Real.sqrt ((((params.m + 1 : ℕ)) : Error)) ≤ 2 * (params.m : Error) := by
      rw [Real.sqrt_le_iff]
      constructor
      · nlinarith
      · norm_num
        nlinarith
    have hgamma_tail :
        Real.sqrt (gamma * (((params.m + 1 : ℕ)) : Error)) ≤
          2 * (params.m : Error) * Real.sqrt gamma := by
      rw [Real.sqrt_mul hgamma_nonneg]
      calc
        Real.sqrt gamma * Real.sqrt ((((params.m + 1 : ℕ)) : Error))
            ≤ Real.sqrt gamma * (2 * (params.m : Error)) := by
              exact mul_le_mul_of_nonneg_left hsqrtn_le (Real.sqrt_nonneg gamma)
        _ = 2 * (params.m : Error) * Real.sqrt gamma := by ring
    have htarget_sqrt :
        24 * Real.sqrt zeta +
            24 * Real.sqrt (gamma * (((params.m + 1 : ℕ)) : Error)) ≤
          48 * (params.m : Error) * (Real.sqrt gamma + Real.sqrt zeta) := by
      have hzpart : 24 * Real.sqrt zeta ≤
          48 * (params.m : Error) * Real.sqrt zeta := by
        have hzsqrt_nonneg : 0 ≤ Real.sqrt zeta := Real.sqrt_nonneg _
        nlinarith
      have hgpart : 24 * Real.sqrt (gamma * (((params.m + 1 : ℕ)) : Error)) ≤
          48 * (params.m : Error) * Real.sqrt gamma := by
        nlinarith
      nlinarith
    calc
      2 * (avgOver 𝒟 avgABA - avgOver 𝒟 avgABAB)
          ≤ 24 * Real.sqrt zeta +
            24 * Real.sqrt (gamma * (((params.m + 1 : ℕ)) : Error)) := hmain_one
      _ ≤ 48 * (params.m : Error) * (Real.sqrt gamma + Real.sqrt zeta) := htarget_sqrt
      _ = commDataProcessedGError params gamma zeta := by
        unfold commDataProcessedGError
        rw [Real.sqrt_eq_rpow gamma, Real.sqrt_eq_rpow zeta]
        try rfl -- vendoring compile fix (Lean v4.33): the previous step may close the goal
  simpa [𝒟, avgABA, avgABAB] using hassemble
end MIPStarRE.LDT.Commutativity
