-- Prove2me | solution 1 for MIPStarRE.LDT.Pasting.commutativitySwitcheroo_ofCompleteSelfConsistency
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T05:51:25.778572+00:00
-- url     : https://prove2.me/submissions/ef643211-586c-4c73-b1ef-03b6b0c89ffe

/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE, with the
authors' permission. Vendored from https://github.com/LionSR/MIPStarRE
(commit 507e8122, 2026-08-25) by scripts/vendor-lidt.py; do not edit by hand.
Upstream path: MIPStarRE/LDT/Pasting/SwitcherooCompletion.lean
-/
/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE, with the
authors' permission. Vendored from https://github.com/LionSR/MIPStarRE
(commit 507e8122, 2026-08-25) by scripts/vendor-lidt.py; do not edit by hand.
Upstream path: MIPStarRE/LDT/Pasting/SwitcherooContraction/ScalarTerms.lean
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/LIDT/MIPStarRE/LDT/Pasting/SwitcherooCompletion.lean (solution of MIPStarRE.LDT.Pasting.commutativitySwitcheroo_ofCompleteSelfConsistency);
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
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_CommutativityPoints_Approximation
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
import Theorems.Thm_MIPStarRE_LDT_Pasting_switcherooAggregateFirstTerm_eq_leftSandwich
import Theorems.Thm_MIPStarRE_LDT_Pasting_switcherooAggregateFirstTerm_eq_split_by_g
import Theorems.Thm_MIPStarRE_LDT_Pasting_switcherooAggregateFourthTerm_split_close_once_commuted
import Theorems.Thm_MIPStarRE_LDT_Pasting_switcherooAggregateLeftFrontScalar_close_firstSplitScalar
import Theorems.Thm_MIPStarRE_LDT_Pasting_switcherooAggregateMixedScalar_close_leftFrontScalar
import Theorems.Thm_MIPStarRE_LDT_Pasting_switcherooAggregateOnceCommutedScalar_close_mixed
import Theorems.Thm_MIPStarRE_LDT_Pasting_switcherooAggregateTarget_eq_middleSandwich
import Theorems.Thm_MIPStarRE_LDT_Pasting_switcherooAggregateThirdTerm_eq_fourthTerm
import Theorems.Thm_MIPStarRE_LDT_Pasting_switcherooAggregate_qSDDOp_expand_avg
import Theorems.Thm_MIPStarRE_LDT_Pasting_switcheroo_first_term_close
import Theorems.Thm_MIPStarRE_LDT_Pasting_switcheroo_second_aggregate_term_close
import Theorems.Thm_MIPStarRE_LDT_postprocess_total

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
/-- Restate the first `sqrt chi` step using the named scalar expression. -/
lemma switcherooAggregateFourthTerm_close_once_commuted_scalar
    {Outcome : Type*} [Fintype Outcome]
    (params : Parameters) [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (hnorm : ψbi.IsNormalized)
    (family : IdxPolyFamily params ι)
    (M : IdxProjSubMeas (Fq params) Outcome ι)
    (chi : Error)
    (hcomm : SDDOpRel ψbi
      (uniformDistribution (SlicePairQuestion params))
      (switcherooPointProductLeft params family M)
      (switcherooPointProductRight params family M)
      chi) :
    |switcherooAggregateFourthTerm params ψbi family M -
        switcherooAggregateOnceCommutedScalar params ψbi family M| ≤
      Real.sqrt chi := by
  simpa [switcherooAggregateOnceCommutedScalar] using
    switcherooAggregateFourthTerm_split_close_once_commuted
      params ψbi hnorm family M chi hcomm
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
    {Outcome : Type*} [Fintype Outcome]
    (params : Parameters) [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (hnorm : ψbi.IsNormalized)
    (hfix : swapDensity ψbi.density = ψbi.density)
    (family : IdxPolyFamily params ι)
    (M : IdxProjSubMeas (Fq params) Outcome ι)
    (zeta omega chi : Error)
    (hselfG : GCompleteSelfConsistencyStatement params ψbi family zeta)
    (hselfM : SDDRel ψbi
      (uniformDistribution (SliceQuestion params))
      (switcherooSelfConsistencyLeft params M)
      (switcherooSelfConsistencyRight params M)
      omega)
    (hcomm : SDDOpRel ψbi
      (uniformDistribution (SlicePairQuestion params))
      (switcherooPointProductLeft params family M)
      (switcherooPointProductRight params family M)
      chi) :
    CommutativitySwitcherooStatement params ψbi family M zeta omega chi := by
  /-
  Paper reference: `lem:commutativity-switcheroo` in
  `references/ldt-paper/ld-pasting.tex`.
  This is the main aggregate-commutation step upgrading commutation with each
  `G^x_g` to commutation with the total `G^x`.

  The paper informally compares all four `qSDDOp` expansion terms to a single
  scalar center. In Lean it is cleaner to use two centers whose contributions
  cancel algebraically:

  * `G ⊗ M` for the first/third terms
  * `M ⊗ G` for the second/fourth terms

  This avoids inserting an extra symmetry assumption on `ψbi` at this stage.
  -/
  refine ⟨?_⟩
  let 𝒟x : Distribution (SliceQuestion params) :=
    uniformDistribution (SliceQuestion params)
  let firstTerm :=
    avgOver 𝒟x (fun x =>
      Preliminaries.leftSandwichExpectation ψbi 𝒟x M
        ((completePartSubMeas params family x).total))
  let secondTerm := switcherooAggregateSecondTerm params ψbi family M
  let thirdTerm := switcherooAggregateThirdTerm params ψbi family M
  let fourthTerm := switcherooAggregateFourthTerm params ψbi family M
  let centerGM := switcherooAggregateTarget params ψbi family M
  let centerMGComplete : Error :=
    avgOver 𝒟x (fun y =>
      Preliminaries.middleSandwichExpectation ψbi 𝒟x
        (completePartProjFamily params family) (((M y).toSubMeas).total))
  have hfirst : |firstTerm - centerGM| ≤ 2 * Real.sqrt omega := by
    simpa [firstTerm, centerGM, switcherooAggregateTarget_eq_middleSandwich] using
      switcheroo_first_term_close params ψbi hnorm family M omega hselfM
  have hsecond : |secondTerm - centerMGComplete| ≤ 2 * Real.sqrt zeta := by
    simpa [secondTerm, centerMGComplete, 𝒟x] using
      switcheroo_second_aggregate_term_close params ψbi hnorm family M zeta hselfG
  have hexpand := switcherooAggregate_qSDDOp_expand_avg params ψbi family M
  have hthird_eq : thirdTerm = fourthTerm := by
    simpa [thirdTerm, fourthTerm] using
      switcherooAggregateThirdTerm_eq_fourthTerm params ψbi family M
  have hcenter : centerMGComplete = centerGM := by
    simpa [centerGM, centerMGComplete] using
      switcherooCompletePartCenter_eq_target params ψbi hfix family M
  have hsecond' : |secondTerm - centerGM| ≤ 2 * Real.sqrt zeta := by
    simpa [hcenter] using hsecond
  have hfirst_eq :
      switcherooAggregateFirstTerm params ψbi family M = firstTerm := by
    simpa [firstTerm, completePartSubMeas, postprocess_total] using
      switcherooAggregateFirstTerm_eq_leftSandwich params ψbi family M
  have hstep1 :=
    switcherooAggregateFourthTerm_close_once_commuted_scalar
      params ψbi hnorm family M chi hcomm
  have hstep2 :
      |switcherooAggregateOnceCommutedScalar params ψbi family M -
          switcherooAggregateMixedScalar params ψbi family M| ≤ Real.sqrt zeta := by
    exact switcherooAggregateOnceCommutedScalar_close_mixed
      params ψbi hnorm family M zeta hselfG
  have hstep3 :
      |switcherooAggregateMixedScalar params ψbi family M -
          switcherooAggregateLeftFrontScalar params ψbi family M| ≤ Real.sqrt zeta := by
    exact switcherooAggregateMixedScalar_close_leftFrontScalar
      params ψbi hnorm family M zeta hselfG
  have hstep4 :=
    switcherooAggregateLeftFrontScalar_close_firstSplitScalar
      params ψbi hnorm family M chi hcomm
  have hstep5 :
      switcherooAggregateFirstSplitScalar params ψbi family M =
        switcherooAggregateFirstTerm params ψbi family M := by
    simpa [switcherooAggregateFirstSplitScalar, mul_assoc] using
      switcherooAggregateFirstTerm_eq_split_by_g params ψbi family M
  have hstep5' :
      |switcherooAggregateFirstSplitScalar params ψbi family M -
          switcherooAggregateFirstTerm params ψbi family M| ≤ 0 := by
    rw [hstep5]
    simp
  have hfourth_first :
      |switcherooAggregateFourthTerm params ψbi family M -
          switcherooAggregateFirstTerm params ψbi family M| ≤
        2 * Real.sqrt zeta + 2 * Real.sqrt chi := by
    calc
      |switcherooAggregateFourthTerm params ψbi family M -
          switcherooAggregateFirstTerm params ψbi family M|
        ≤ |switcherooAggregateFourthTerm params ψbi family M -
              switcherooAggregateOnceCommutedScalar params ψbi family M| +
            |switcherooAggregateOnceCommutedScalar params ψbi family M -
              switcherooAggregateMixedScalar params ψbi family M| +
            |switcherooAggregateMixedScalar params ψbi family M -
              switcherooAggregateLeftFrontScalar params ψbi family M| +
            |switcherooAggregateLeftFrontScalar params ψbi family M -
              switcherooAggregateFirstSplitScalar params ψbi family M| +
            |switcherooAggregateFirstSplitScalar params ψbi family M -
              switcherooAggregateFirstTerm params ψbi family M| := by
              nlinarith [abs_sub_le
                (switcherooAggregateFourthTerm params ψbi family M)
                (switcherooAggregateOnceCommutedScalar params ψbi family M)
                (switcherooAggregateFirstTerm params ψbi family M),
                abs_sub_le
                  (switcherooAggregateOnceCommutedScalar params ψbi family M)
                  (switcherooAggregateMixedScalar params ψbi family M)
                  (switcherooAggregateFirstTerm params ψbi family M),
                abs_sub_le
                  (switcherooAggregateMixedScalar params ψbi family M)
                  (switcherooAggregateLeftFrontScalar params ψbi family M)
                  (switcherooAggregateFirstTerm params ψbi family M),
                abs_sub_le
                  (switcherooAggregateLeftFrontScalar params ψbi family M)
                  (switcherooAggregateFirstSplitScalar params ψbi family M)
                  (switcherooAggregateFirstTerm params ψbi family M)]
      _ ≤ Real.sqrt chi + Real.sqrt zeta + Real.sqrt zeta + Real.sqrt chi + 0 := by
            nlinarith [hstep1, hstep2, hstep3, hstep4, hstep5']
      _ = 2 * Real.sqrt zeta + 2 * Real.sqrt chi := by ring
  have hfourth_first' :
      |fourthTerm - firstTerm| ≤ 2 * Real.sqrt zeta + 2 * Real.sqrt chi := by
    rw [← hfirst_eq]
    simpa [fourthTerm] using hfourth_first
  have hfourth : |fourthTerm - centerGM| ≤
      2 * Real.sqrt zeta + 2 * Real.sqrt chi + 2 * Real.sqrt omega := by
    calc
      |fourthTerm - centerGM| ≤ |fourthTerm - firstTerm| + |firstTerm - centerGM| := by
            simpa [add_comm, add_left_comm, add_assoc] using
              (abs_sub_le fourthTerm firstTerm centerGM)
      _ ≤ (2 * Real.sqrt zeta + 2 * Real.sqrt chi) + 2 * Real.sqrt omega := by
            exact add_le_add hfourth_first' hfirst
      _ = 2 * Real.sqrt zeta + 2 * Real.sqrt chi + 2 * Real.sqrt omega := by ring
  have hthird : |thirdTerm - centerGM| ≤
      2 * Real.sqrt zeta + 2 * Real.sqrt chi + 2 * Real.sqrt omega := by
    rw [hthird_eq]
    exact hfourth
  constructor
  unfold sddErrorOp
  rw [hexpand]
  have hdecomp :
      firstTerm + secondTerm - thirdTerm - fourthTerm ≤
        |firstTerm - centerGM| + |secondTerm - centerGM| +
          |thirdTerm - centerGM| + |fourthTerm - centerGM| := by
    have hfirst_le : firstTerm - centerGM ≤ |firstTerm - centerGM| := by
      exact le_abs_self _
    have hsecond_le : secondTerm - centerGM ≤ |secondTerm - centerGM| := by
      exact le_abs_self _
    have hthird_le : -(thirdTerm - centerGM) ≤ |thirdTerm - centerGM| := by
      exact neg_le_abs _
    have hfourth_le : -(fourthTerm - centerGM) ≤ |fourthTerm - centerGM| := by
      exact neg_le_abs _
    have hrewrite :
        firstTerm + secondTerm - thirdTerm - fourthTerm =
          (firstTerm - centerGM) + (secondTerm - centerGM) -
            (thirdTerm - centerGM) - (fourthTerm - centerGM) := by
      ring
    rw [hrewrite]
    nlinarith
  have hmain_eq :
      switcherooAggregateFirstTerm params ψbi family M + secondTerm - thirdTerm - fourthTerm =
        firstTerm + secondTerm - thirdTerm - fourthTerm := by
    exact congrArg (fun t => t + secondTerm - thirdTerm - fourthTerm) hfirst_eq
  calc
    switcherooAggregateFirstTerm params ψbi family M +
        switcherooAggregateSecondTerm params ψbi family M -
        switcherooAggregateThirdTerm params ψbi family M -
        switcherooAggregateFourthTerm params ψbi family M
      = firstTerm + secondTerm - thirdTerm - fourthTerm := by
          simpa [secondTerm, thirdTerm, fourthTerm] using hmain_eq
    _
      ≤ |firstTerm - centerGM| + |secondTerm - centerGM| +
          |thirdTerm - centerGM| + |fourthTerm - centerGM| := hdecomp
    _ ≤ 2 * Real.sqrt omega + 2 * Real.sqrt zeta +
          (2 * Real.sqrt zeta + 2 * Real.sqrt chi + 2 * Real.sqrt omega) +
          (2 * Real.sqrt zeta + 2 * Real.sqrt chi + 2 * Real.sqrt omega) := by
            nlinarith [hfirst, hsecond', hthird, hfourth]
    _ = commutativitySwitcherooError zeta omega chi := by
          simp [commutativitySwitcherooError, Real.sqrt_eq_rpow]
          ring
end MIPStarRE.LDT.Pasting
