-- Prove2me | solution 1 for MIPStarRE.LDT.Commutativity.fullSliceCommutation_of_evaluated_on_evaluated_questions
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T04:35:10.329906+00:00
-- url     : https://prove2.me/submissions/c08b7960-9c68-4abe-897c-4ed18c7e4d4c

/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE, with the
authors' permission. Vendored from https://github.com/LionSR/MIPStarRE
(commit 507e8122, 2026-08-25) by scripts/vendor-lidt.py; do not edit by hand.
Upstream path: MIPStarRE/LDT/Commutativity/Main/EvaluatedQuestions.lean
-/
/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE, with the
authors' permission. Vendored from https://github.com/LionSR/MIPStarRE
(commit 507e8122, 2026-08-25) by scripts/vendor-lidt.py; do not edit by hand.
Upstream path: MIPStarRE/LDT/Preliminaries/DistanceBounds.lean
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/LIDT/MIPStarRE/LDT/Commutativity/Main/EvaluatedQuestions.lean (solution of MIPStarRE.LDT.Commutativity.fullSliceCommutation_of_evaluated_on_evaluated_questions);
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
import Theorems.Thm_MIPStarRE_LDT_Commutativity_fullSliceCommutation_qSDDOp_avg_eq
import Theorems.Thm_MIPStarRE_LDT_Commutativity_fullSliceProductLeft_to_zero_le_one
import Theorems.Thm_MIPStarRE_LDT_Commutativity_fullSlice_closenessOfIP_CAB_hEval_sqrt
import Theorems.Thm_MIPStarRE_LDT_Commutativity_fullSlice_scalar_marginalize_x
import Theorems.Thm_MIPStarRE_LDT_Commutativity_fullSlice_scalar_marginalize_y
import Theorems.Thm_MIPStarRE_LDT_Commutativity_zero_to_fullSliceProductRight_le_one
import Theorems.Thm_MIPStarRE_LDT_Preliminaries_stateDependentDistanceOpRel_triangle

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPStarRE.LDT.Preliminaries
section
open scoped BigOperators MatrixOrder Matrix ComplexOrder
open MIPStarRE.LDT
set_option backward.isDefEq.respectTransparency false
/-- Monotonicity of `SDDOpRel` in the error bound. -/
lemma stateDependentDistanceOpRel_mono
    {Question Outcome : Type*} {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : QuantumState ι) (𝒟 : Distribution Question)
    (A B : IdxOpFamily Question Outcome ι) (δ δ' : Error)
    (hle : δ ≤ δ') :
    SDDOpRel ψ 𝒟 A B δ →
    SDDOpRel ψ 𝒟 A B δ' := by
  intro ⟨h⟩
  exact ⟨le_trans h hle⟩
end
end MIPStarRE.LDT.Preliminaries

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
    (params : Parameters) [FieldModel params.q] (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (gamma zeta : Error)
    (hnorm : strategy.state.IsNormalized)
    (hgamma_nonneg : 0 ≤ gamma) (hzeta_nonneg : 0 ≤ zeta)
    (hself : family.StronglySelfConsistent strategy.state zeta)
    (hEval :
      SDDOpRel strategy.state
        (uniformDistribution (EvaluatedSliceQuestion params))
        (evaluatedFromFullSliceProductLeft params strategy family)
        (evaluatedFromFullSliceProductRight params strategy family)
        (commDataProcessedGError params gamma zeta)) :
    SDDOpRel strategy.state
      (uniformDistribution (EvaluatedSliceQuestion params))
      (fun q => fullSliceProductLeft params strategy family
        (fullSliceQuestionOfEvaluatedSlice params q))
      (fun q => fullSliceProductRight params strategy family
        (fullSliceQuestionOfEvaluatedSlice params q))
      (comMainError params gamma zeta) := by
  /-
  Paper reference: `references/ldt-paper/commutativity-G.tex`,
  theorem `thm:com-main`, especially the passage from
  `eq:evaluate-gcom-at-points` to `eq:evaluate-gcom-at-points-part-dos`
  and the final displayed error estimate.

  The paper-faithful transport below passes from the full polynomial products
  down to the evaluated products on the sampled points.

  The paper first reduces to the small-parameter regime
  `γ ≤ 1`, `ζ ≤ 1`, and `d / q ≤ 1`; otherwise `comMainError` is already large
  enough while the unexpanded `sddErrorOp` is trivially bounded.

  In the small-parameter case, the proof uses two Schwartz-Zippel
  marginalizations together with `closenessOfIP` and the evaluated
  commutation estimate obtained from `hEval`, producing the displayed error
  chain that is then absorbed into `comMainError`.
  -/
  -- WLOG: reduce to the small-parameter regime (paper lines 260–276).
  -- When max(γ, ζ, d/q) ≥ 1, comMainError ≥ 30m ≥ 30 while
  -- sddErrorOp ≤ 4 by the sub-measurement bound, so the inequality
  -- holds trivially.
  by_cases hsmall :
      gamma ≤ 1 ∧ zeta ≤ 1 ∧
        (↑params.d : Error) / (↑params.q : Error) ≤ 1
  · -- Small-parameter case: γ, ζ, d/q ≤ 1.
    obtain ⟨hgamma_le, hzeta_le, hdq_le⟩ := hsmall
    -- Step 1: The Schwartz-Zippel transport.
    -- Bound the full-product sddErrorOp by corrections from:
    -- (a) The x switch-sandwich transport (`4√ζ`) and the y scalar
    --     marginalization (`2md/q + 4√ζ`)
    -- (b) The evaluated commutation via the strong `hEval` transport
    --     (≤ √(commDataProcessedGError))
    -- giving total ≤ 16√ζ + 4md/q + 2√(commDataProcessedGError).
    --
    -- Proof sketch:
    -- * Expand qSDDOp into quartic trace terms
    --   (BAB + ABA - BABA - ABAB) using projectivity
    -- * Use BAB = ABA and BABA = ABAB symmetry (swap x↔y, g↔h)
    -- * For each of ABA and ABAB, apply the marginalization chain
    --   to relate full-polynomial sums to evaluated sums
    -- * Use submeasurement bounds (Σ_g G^x_g ≤ I) to control
    --   quartic terms: ABA ≤ 1
    -- * The ABAB term uses hEval through closenessOfIP to obtain
    --   √(commDataProcessedGError)
    have hTransport :
        sddErrorOp strategy.state
          (uniformDistribution (EvaluatedSliceQuestion params))
          (fun q => fullSliceProductLeft params strategy family
            (fullSliceQuestionOfEvaluatedSlice params q))
          (fun q => fullSliceProductRight params strategy family
            (fullSliceQuestionOfEvaluatedSlice params q)) ≤
        16 * Real.sqrt zeta +
          4 * (↑params.m * ↑params.d / ↑params.q) +
          2 * Real.sqrt
            (commDataProcessedGError params gamma zeta) := by
      -- Compose the four scalar lemmas.  Paper chain:
      -- * `fullSliceCommutation_qSDDOp_avg_eq` rewrites the pulled-back
      --   `sddErrorOp` as `2 · (fullABA − fullABAB)` (paper lines 286-290).
      -- * Triangle on the real line:
      --     `|fullABA − fullABAB|
      --        ≤ |fullABA − evalABA| + |evalABA − evalABAB|
      --          + |evalABAB − fullABAB|`
      -- * `fullSlice_scalar_marginalize_x`: the first-term switch-sandwich
      --   comparison costs `4√ζ`.
      -- * `fullSlice_scalar_marginalize_y`: the paper-faithful second-term
      --   comparison splits into the proved x-prefix `md/q + √ζ`, the proved
      --   line-359 comparison `√ζ`, the proved line-360 comparison `√ζ`, and the proved
      --   y-tail `md/q + √ζ`, for a total of `2md/q + 4√ζ`.
      -- * `fullSlice_closenessOfIP_CAB_hEval_sqrt`: the direct evaluated-side
      --   route gives `|evalABA − evalABAB| ≤ √ν`.
      -- Summing gives `|fullABA − fullABAB| ≤ 8√ζ + 2(md/q) + √ν`,
      -- and multiplying by `2` produces `16√ζ + 4(md/q) + 2√ν`.
      have hExpand :=
        fullSliceCommutation_qSDDOp_avg_eq params strategy family
      have hMargX :=
        fullSlice_scalar_marginalize_x params strategy family zeta hnorm hself
      have hMargY :=
        fullSlice_scalar_marginalize_y params strategy family zeta hnorm hself
      have hClose :=
        fullSlice_closenessOfIP_CAB_hEval_sqrt params strategy family gamma zeta
          hnorm hEval
      -- Triangle inequality on the three intermediate quantities.
      have hTri :
          |fullSliceABAAvg params strategy family -
              fullSliceABABAvg params strategy family| ≤
            |fullSliceABAAvg params strategy family -
                evaluatedSliceABAAvg params strategy family| +
              |evaluatedSliceABAAvg params strategy family -
                  evaluatedSliceABABAvg params strategy family| +
              |evaluatedSliceABABAvg params strategy family -
                  fullSliceABABAvg params strategy family| := by
        have h1 :
            fullSliceABAAvg params strategy family -
                fullSliceABABAvg params strategy family =
              (fullSliceABAAvg params strategy family -
                  evaluatedSliceABAAvg params strategy family) +
                (evaluatedSliceABAAvg params strategy family -
                    evaluatedSliceABABAvg params strategy family) +
                (evaluatedSliceABABAvg params strategy family -
                    fullSliceABABAvg params strategy family) := by
          ring
        calc
          |fullSliceABAAvg params strategy family -
              fullSliceABABAvg params strategy family|
            = |(fullSliceABAAvg params strategy family -
                  evaluatedSliceABAAvg params strategy family) +
                (evaluatedSliceABAAvg params strategy family -
                    evaluatedSliceABABAvg params strategy family) +
                (evaluatedSliceABABAvg params strategy family -
                    fullSliceABABAvg params strategy family)| := by
                  rw [h1]
          _ ≤ |(fullSliceABAAvg params strategy family -
                  evaluatedSliceABAAvg params strategy family) +
                (evaluatedSliceABAAvg params strategy family -
                    evaluatedSliceABABAvg params strategy family)| +
                |evaluatedSliceABABAvg params strategy family -
                    fullSliceABABAvg params strategy family| :=
                abs_add_le _ _
          _ ≤ (|fullSliceABAAvg params strategy family -
                    evaluatedSliceABAAvg params strategy family| +
                  |evaluatedSliceABAAvg params strategy family -
                      evaluatedSliceABABAvg params strategy family|) +
                |evaluatedSliceABABAvg params strategy family -
                    fullSliceABABAvg params strategy family| := by
                gcongr
                exact abs_add_le _ _
      -- Symmetry of `abs`: `|evalABAB - fullABAB| = |fullABAB - evalABAB|`.
      have hMargY' :
          |evaluatedSliceABABAvg params strategy family -
              fullSliceABABAvg params strategy family| ≤
            2 * ((↑params.m : Error) * ↑params.d / ↑params.q) +
              4 * Real.sqrt zeta := by
        rw [abs_sub_comm]
        exact hMargY
      -- `sddErrorOp = 2 · (fullABA − fullABAB) ≤ 2 · |fullABA − fullABAB|`.
      have hTwoAbs :
          sddErrorOp strategy.state
            (uniformDistribution (EvaluatedSliceQuestion params))
            (fun q => fullSliceProductLeft params strategy family
              (fullSliceQuestionOfEvaluatedSlice params q))
            (fun q => fullSliceProductRight params strategy family
              (fullSliceQuestionOfEvaluatedSlice params q)) ≤
          2 *
            |fullSliceABAAvg params strategy family -
                fullSliceABABAvg params strategy family| := by
        rw [hExpand]
        have := le_abs_self
          (fullSliceABAAvg params strategy family -
            fullSliceABABAvg params strategy family)
        linarith
      calc
        sddErrorOp strategy.state
            (uniformDistribution (EvaluatedSliceQuestion params))
            (fun q => fullSliceProductLeft params strategy family
              (fullSliceQuestionOfEvaluatedSlice params q))
            (fun q => fullSliceProductRight params strategy family
              (fullSliceQuestionOfEvaluatedSlice params q))
          ≤ 2 *
              |fullSliceABAAvg params strategy family -
                  fullSliceABABAvg params strategy family| := hTwoAbs
        _ ≤ 2 *
              (|fullSliceABAAvg params strategy family -
                    evaluatedSliceABAAvg params strategy family| +
                |evaluatedSliceABAAvg params strategy family -
                    evaluatedSliceABABAvg params strategy family| +
                |evaluatedSliceABABAvg params strategy family -
                    fullSliceABABAvg params strategy family|) := by
              linarith [hTri]
        _ ≤ 2 *
              (4 * Real.sqrt zeta +
                Real.sqrt
                  (commDataProcessedGError params gamma zeta) +
                (2 * ((↑params.m : Error) * ↑params.d / ↑params.q) +
                  4 * Real.sqrt zeta)) := by
              linarith [hMargX, hMargY', hClose]
        _ = 16 * Real.sqrt zeta +
              4 * (↑params.m * ↑params.d / ↑params.q) +
              2 * Real.sqrt
                (commDataProcessedGError params gamma zeta) := by ring
    -- Step 2: Error arithmetic (using small-parameter hypotheses).
    -- Show:
    --   16√ζ + 4md/q + 2√(48m(√γ + √ζ))
    --     ≤ 30m(γ^¼ + ζ^¼ + (d/q)^¼)
    --
    -- Key estimates (all require γ, ζ, d/q ≤ 1):
    -- * 2√(48m(√γ + √ζ)) ≤ 2√(48m)(γ^¼ + ζ^¼) ≤ 14m(γ^¼ + ζ^¼)
    --   using √(a+b) ≤ √a + √b and √m ≤ m (for m ≥ 1)
    -- * 16√ζ ≤ 16m·ζ^¼ (ζ ≤ 1 ⇒ ζ^½ ≤ ζ^¼; m ≥ 1)
    -- * 4md/q ≤ 6m(d/q)^¼ (d/q ≤ 1 ⇒ x ≤ x^¼)
    -- * Total: 14m·γ^¼ + 30m·ζ^¼ + 6m·(d/q)^¼
    --         ≤ 30m(γ^¼ + ζ^¼ + (d/q)^¼)
    have hArith :
        16 * Real.sqrt zeta +
          4 * (↑params.m * ↑params.d / ↑params.q) +
          2 * Real.sqrt
            (commDataProcessedGError params gamma zeta) ≤
        comMainError params gamma zeta := by
      unfold commDataProcessedGError comMainError
      -- Useful numerical facts
      have hm_ge : (1 : Error) ≤ (params.m : Error) :=
        Nat.one_le_cast.mpr (Nat.succ_le_of_lt params.hm)
      have hq_pos : (0 : Error) < ↑params.q :=
        Nat.cast_pos.mpr params.hq
      have hdq_nn : 0 ≤ (↑params.d : Error) / ↑params.q :=
        div_nonneg (Nat.cast_nonneg _) hq_pos.le
      have hg4 : 0 ≤ Real.rpow gamma (1 / (4 : Error)) :=
        Real.rpow_nonneg hgamma_nonneg _
      have hz4 : 0 ≤ Real.rpow zeta (1 / (4 : Error)) :=
        Real.rpow_nonneg hzeta_nonneg _
      have hdq4 : 0 ≤ Real.rpow
          ((↑params.d : Error) / ↑params.q) (1 / (4 : Error)) :=
        Real.rpow_nonneg hdq_nn _
      -- Step 1: sqrt ζ ≤ ζ^(1/4)
      have h_sqrt_z : Real.sqrt zeta ≤
          Real.rpow zeta (1 / (4 : Error)) := by
        rw [Real.sqrt_eq_rpow]
        exact Real.rpow_le_rpow_of_exponent_ge'
          hzeta_nonneg hzeta_le (by norm_num) (by norm_num)
      -- Step 2: d/q ≤ (d/q)^(1/4)
      have h_dq : (↑params.d : Error) / ↑params.q ≤
          Real.rpow ((↑params.d : Error) / ↑params.q)
            (1 / (4 : Error)) := by
        conv_lhs =>
          rw [show (↑params.d : Error) / ↑params.q =
            Real.rpow ((↑params.d : Error) / ↑params.q) 1
            from (Real.rpow_one _).symm]
        exact Real.rpow_le_rpow_of_exponent_ge'
          hdq_nn hdq_le (by norm_num) (by norm_num)
      -- Step 3: (γ^(1/4))² = γ^(1/2) and (ζ^(1/4))² = ζ^(1/2)
      have hg4_sq :
          (Real.rpow gamma (1 / (4 : Error))) ^ (2 : ℕ) =
            Real.rpow gamma (1 / (2 : Error)) := by
        calc (Real.rpow gamma (1 / (4 : Error))) ^ (2 : ℕ)
            = (Real.rpow gamma (1 / (4 : Error))) ^
                (2 : Error) := by norm_num
          _ = Real.rpow gamma
                (1 / (4 : Error) * 2) := by
              symm; exact Real.rpow_mul hgamma_nonneg _ _
          _ = Real.rpow gamma
                (1 / (2 : Error)) := by norm_num
      have hz4_sq :
          (Real.rpow zeta (1 / (4 : Error))) ^ (2 : ℕ) =
            Real.rpow zeta (1 / (2 : Error)) := by
        calc (Real.rpow zeta (1 / (4 : Error))) ^ (2 : ℕ)
            = (Real.rpow zeta (1 / (4 : Error))) ^
                (2 : Error) := by norm_num
          _ = Real.rpow zeta
                (1 / (4 : Error) * 2) := by
              symm; exact Real.rpow_mul hzeta_nonneg _ _
          _ = Real.rpow zeta
                (1 / (2 : Error)) := by norm_num
      -- Step 4: √(48m(γ^½+ζ^½)) ≤ √(48m)·(γ^¼+ζ^¼)
      -- Using γ^½ = (γ^¼)² and a²+b² ≤ (a+b)²
      have hsqrt_cdpg :
          Real.sqrt (48 * ↑params.m *
            (Real.rpow gamma (1 / (2 : Error)) +
              Real.rpow zeta (1 / (2 : Error)))) ≤
          Real.sqrt (48 * ↑params.m) *
            (Real.rpow gamma (1 / (4 : Error)) +
              Real.rpow zeta (1 / (4 : Error))) := by
        rw [← hg4_sq, ← hz4_sq]
        have hsq_le :
            (Real.rpow gamma (1 / (4 : Error))) ^ (2 : ℕ) +
              (Real.rpow zeta (1 / (4 : Error))) ^ (2 : ℕ) ≤
            (Real.rpow gamma (1 / (4 : Error)) +
              Real.rpow zeta (1 / (4 : Error))) ^
                (2 : ℕ) := by
          nlinarith [hg4, hz4]
        calc Real.sqrt (48 * ↑params.m *
              ((Real.rpow gamma (1 / (4 : Error))) ^
                  (2 : ℕ) +
                (Real.rpow zeta (1 / (4 : Error))) ^
                  (2 : ℕ)))
            ≤ Real.sqrt (48 * ↑params.m *
                (Real.rpow gamma (1 / (4 : Error)) +
                  Real.rpow zeta
                    (1 / (4 : Error))) ^ (2 : ℕ)) := by
              apply Real.sqrt_le_sqrt
              exact mul_le_mul_of_nonneg_left hsq_le
                (by positivity)
          _ = Real.sqrt (48 * ↑params.m) *
                Real.sqrt
                  ((Real.rpow gamma (1 / (4 : Error)) +
                    Real.rpow zeta
                      (1 / (4 : Error))) ^
                    (2 : ℕ)) := by
              rw [Real.sqrt_mul (by positivity)]
          _ = Real.sqrt (48 * ↑params.m) *
                (Real.rpow gamma (1 / (4 : Error)) +
                  Real.rpow zeta
                    (1 / (4 : Error))) := by
              rw [Real.sqrt_sq (by linarith)]
      -- Step 5: 2·√(48m) ≤ 14m (since 192m ≤ 196m²
      --   for m ≥ 1)
      have hsqrt_48m :
          Real.sqrt (48 * ↑params.m) ≤
            7 * ↑params.m := by
        rw [show 7 * (↑params.m : Error) =
          Real.sqrt ((7 * ↑params.m) ^ 2) from
          (Real.sqrt_sq (by linarith)).symm]
        apply Real.sqrt_le_sqrt
        nlinarith [hm_ge]
      -- Combine the three parts
      have hA : 16 * Real.sqrt zeta ≤
          16 * ↑params.m *
            Real.rpow zeta (1 / (4 : Error)) := by
        nlinarith [h_sqrt_z, hm_ge, hz4]
      have hB :
          4 * (↑params.m * ↑params.d / ↑params.q) ≤
          6 * ↑params.m * Real.rpow
            ((↑params.d : Error) / ↑params.q)
            (1 / (4 : Error)) := by
        have hrw :
            ↑params.m * ↑params.d / ↑params.q =
              ↑params.m *
                ((↑params.d : Error) / ↑params.q) := by
          ring
        rw [hrw]
        nlinarith [h_dq, hm_ge, hdq4]
      have hC :
          2 * Real.sqrt (48 * ↑params.m *
            (Real.rpow gamma (1 / (2 : Error)) +
              Real.rpow zeta (1 / (2 : Error)))) ≤
          14 * ↑params.m *
            (Real.rpow gamma (1 / (4 : Error)) +
              Real.rpow zeta
                (1 / (4 : Error))) := by
        calc 2 * Real.sqrt (48 * ↑params.m *
              (Real.rpow gamma (1 / (2 : Error)) +
                Real.rpow zeta (1 / (2 : Error))))
            ≤ 2 * (Real.sqrt (48 * ↑params.m) *
                (Real.rpow gamma (1 / (4 : Error)) +
                  Real.rpow zeta
                    (1 / (4 : Error)))) :=
              mul_le_mul_of_nonneg_left hsqrt_cdpg
                (by norm_num)
          _ = 2 * Real.sqrt (48 * ↑params.m) *
                (Real.rpow gamma (1 / (4 : Error)) +
                  Real.rpow zeta
                    (1 / (4 : Error))) := by ring
          _ ≤ 14 * ↑params.m *
                (Real.rpow gamma (1 / (4 : Error)) +
                  Real.rpow zeta
                    (1 / (4 : Error))) := by
              exact mul_le_mul_of_nonneg_right
                (by linarith [hsqrt_48m])
                (by linarith)
      -- 14m·g4 + 30m·z4 + 6m·dq4 ≤ 30m·(g4+z4+dq4)
      nlinarith [hA, hB, hC, hg4, hz4, hdq4, hm_ge]
    exact ⟨le_trans hTransport hArith⟩
  · -- Large-parameter case: max(γ, ζ, d/q) > 1.
    -- The bound is trivial: sddErrorOp ≤ 4 (by the triangle
    -- inequality for vectors and the sub-measurement property;
    -- paper lines 263–271), while comMainError ≥ 30m ≥ 30 > 4
    -- (since rpow x (1/4) ≥ 1 when x ≥ 1, and m ≥ 1).
    have hleft :=
      fullSliceProductLeft_to_zero_le_one params strategy family hnorm
    have hright :=
      zero_to_fullSliceProductRight_le_one params strategy family hnorm
    have hfour :
        SDDOpRel strategy.state
          (uniformDistribution (EvaluatedSliceQuestion params))
          (fun q => fullSliceProductLeft params strategy family
            (fullSliceQuestionOfEvaluatedSlice params q))
          (fun q => fullSliceProductRight params strategy family
            (fullSliceQuestionOfEvaluatedSlice params q))
          4 := by
      have htri :=
        MIPStarRE.LDT.Preliminaries.stateDependentDistanceOpRel_triangle
          strategy.state
          (uniformDistribution (EvaluatedSliceQuestion params))
          (fun q => fullSliceProductLeft params strategy family
            (fullSliceQuestionOfEvaluatedSlice params q))
          (fun _ => zeroFullSliceOpFamily (ι := ι) params)
          (fun q => fullSliceProductRight params strategy family
            (fullSliceQuestionOfEvaluatedSlice params q))
          1 1 hleft hright
      refine MIPStarRE.LDT.Preliminaries.stateDependentDistanceOpRel_mono
        strategy.state
        (uniformDistribution (EvaluatedSliceQuestion params))
        (fun q => fullSliceProductLeft params strategy family
          (fullSliceQuestionOfEvaluatedSlice params q))
        (fun q => fullSliceProductRight params strategy family
          (fullSliceQuestionOfEvaluatedSlice params q))
        (2 * (1 + 1)) 4 ?_ htri
      norm_num
    have hcom_ge_four : 4 ≤ comMainError params gamma zeta := by
      unfold comMainError
      have hm_ge : (1 : Error) ≤ (params.m : Error) :=
        Nat.one_le_cast.mpr (Nat.succ_le_of_lt params.hm)
      have hq_pos : (0 : Error) < (params.q : Error) := Nat.cast_pos.mpr params.hq
      have hdq_nonneg : 0 ≤ (params.d : Error) / (params.q : Error) :=
        div_nonneg (Nat.cast_nonneg _) hq_pos.le
      have hnotsmall :
          1 < gamma ∨ 1 < zeta ∨ 1 < (params.d : Error) / (params.q : Error) := by
        have : ¬ (gamma ≤ 1 ∧ zeta ≤ 1 ∧
            (params.d : Error) / (params.q : Error) ≤ 1) := hsmall
        by_cases hg : gamma ≤ 1
        · by_cases hz : zeta ≤ 1
          · by_cases hdq : (params.d : Error) / (params.q : Error) ≤ 1
            · exact False.elim (this ⟨hg, hz, hdq⟩)
            · exact Or.inr <| Or.inr <| lt_of_not_ge hdq
          · exact Or.inr <| Or.inl <| lt_of_not_ge hz
        · exact Or.inl <| lt_of_not_ge hg
      have hsum_ge_one :
          1 ≤
            Real.rpow gamma (1 / (4 : Error)) +
              Real.rpow zeta (1 / (4 : Error)) +
              Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (4 : Error)) := by
        rcases hnotsmall with hg | hz | hdq
        · have hγ : 1 ≤ Real.rpow gamma (1 / (4 : Error)) := by
            simpa using Real.one_le_rpow hg.le (show (0 : Error) ≤ 1 / (4 : Error) by norm_num)
          have hζnn : 0 ≤ Real.rpow zeta (1 / (4 : Error)) := Real.rpow_nonneg hzeta_nonneg _
          have hdqnn :
              0 ≤ Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (4 : Error)) :=
            Real.rpow_nonneg hdq_nonneg _
          linarith
        · have hζ : 1 ≤ Real.rpow zeta (1 / (4 : Error)) := by
            simpa using Real.one_le_rpow hz.le (show (0 : Error) ≤ 1 / (4 : Error) by norm_num)
          have hγnn : 0 ≤ Real.rpow gamma (1 / (4 : Error)) := Real.rpow_nonneg hgamma_nonneg _
          have hdqnn :
              0 ≤ Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (4 : Error)) :=
            Real.rpow_nonneg hdq_nonneg _
          linarith
        · have hdq' :
              1 ≤ Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (4 : Error)) := by
            simpa using Real.one_le_rpow hdq.le (show (0 : Error) ≤ 1 / (4 : Error) by norm_num)
          have hγnn : 0 ≤ Real.rpow gamma (1 / (4 : Error)) := Real.rpow_nonneg hgamma_nonneg _
          have hζnn : 0 ≤ Real.rpow zeta (1 / (4 : Error)) := Real.rpow_nonneg hzeta_nonneg _
          linarith
      calc
        (4 : Error) ≤ 30 := by norm_num
        _ ≤ 30 * (params.m : Error) := by nlinarith
        _ ≤ 30 * (params.m : Error) *
            (Real.rpow gamma (1 / (4 : Error)) +
              Real.rpow zeta (1 / (4 : Error)) +
              Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (4 : Error))) := by
                nlinarith
    exact MIPStarRE.LDT.Preliminaries.stateDependentDistanceOpRel_mono
      strategy.state
      (uniformDistribution (EvaluatedSliceQuestion params))
      (fun q => fullSliceProductLeft params strategy family
        (fullSliceQuestionOfEvaluatedSlice params q))
      (fun q => fullSliceProductRight params strategy family
        (fullSliceQuestionOfEvaluatedSlice params q))
      4 (comMainError params gamma zeta) hcom_ge_four hfour
end MIPStarRE.LDT.Commutativity
