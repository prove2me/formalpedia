-- Prove2me | solution 1 for MIPStarRE.LDT.SelfImprovement.addInU_selected_cs_chain_step1_abs_le_sqrt_two_delta
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T04:44:24.277493+00:00
-- url     : https://prove2.me/submissions/64f28c20-beba-4454-90cb-31e2e3e4219a

/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE, with the
authors' permission. Vendored from https://github.com/LionSR/MIPStarRE
(commit 507e8122, 2026-08-25) by scripts/vendor-lidt.py; do not edit by hand.
Upstream path: MIPStarRE/LDT/SelfImprovement/Theorems/Results/AddInUStep12/Selected.lean
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
Upstream path: MIPStarRE/LDT/Basic/DistributionAvg.lean
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/LIDT/MIPStarRE/LDT/SelfImprovement/Theorems/Results/AddInUStep12/Selected.lean (solution of MIPStarRE.LDT.SelfImprovement.addInU_selected_cs_chain_step1_abs_le_sqrt_two_delta);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Algebra.Algebra.Hom
import Mathlib.Algebra.Algebra.NonUnitalHom
import Mathlib.Algebra.Algebra.Spectrum.Basic
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
import Mathlib.Algebra.Field.Rat
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.Group.Action.Pi
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Commute.Defs
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Finsupp
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Algebra.Group.Idempotent
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
import Mathlib.Algebra.Star.Unitary
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
import Mathlib.Data.Finset.Erase
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
import Mathlib.LinearAlgebra.UnitaryGroup
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
import Mathlib.Order.Hom.Basic
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
import Mathlib.Tactic.NormNum.Eq
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
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_MainInductionStep_Defs
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_Quantum_Measurement
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Defs
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Statements
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Basic_MeasurementLift
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Preliminaries_Defs
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Preliminaries_ComparisonCore
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Preliminaries_DistanceBounds
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Preliminaries_ConsistencyBridges
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichPrep_InnerProduct
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichMain_Completeness
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Preliminaries_BipartiteSelfConsistency_Core
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Preliminaries_CauchySchwarz
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Projectivization
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Preliminaries_Triangles_Core
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Test_StrategyRole_Algebra
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Test_StrategyFailures
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_Defs_Core
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_GlobalVariance_Defs_Core
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Preliminaries_Polynomials
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Preliminaries_PolynomialAgreement
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_GlobalVariance_Defs_Operators
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_GlobalVariance_Defs_Families
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_SelfImprovement_Defs
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Statements
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Preliminaries_SelfConsistency_DataProcessing
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Thresholds_Final
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_AddInUDiagonalAndDefs_Selection
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_AddInUDiagonalAndDefs_Residual
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_AddInUDiagonalAndDefs_ScalarChain
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_AddInUStep12_Algebra
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_AddInUStep12_Selected
import Theorems.Thm_MIPStarRE_LDT_Preliminaries_closenessOfInnerProduct_right
import Theorems.Thm_MIPStarRE_LDT_SelfImprovement_addInU_pointMeasurement_snd_selfConsistency
import Theorems.Thm_MIPStarRE_LDT_SelfImprovement_addInU_selected_cs_chain_step1_diff_eq
import Theorems.Thm_MIPStarRE_LDT_avgOver_congr
import Theorems.Thm_MIPStarRE_LDT_ev_sub
import Theorems.Thm_MIPStarRE_LDT_ev_zero

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPStarRE.LDT.Distribution
section
open scoped BigOperators MatrixOrder Matrix ComplexOrder
set_option backward.isDefEq.respectTransparency false
/-- The scalar average is the weighted finite-sum linear map applied to a scalar
family. -/
theorem avgOver_eq_weightedSumLinearMap {α : Type*}
    (𝒟 : Distribution α) (f : α → Error) :
    avgOver 𝒟 f = 𝒟.weightedSumLinearMap Error f := by
  simp [avgOver, smul_eq_mul]
end
end MIPStarRE.LDT.Distribution

namespace MIPStarRE.LDT
section
open scoped BigOperators MatrixOrder Matrix ComplexOrder
set_option backward.isDefEq.respectTransparency false
/-- Averaging distributes over subtraction. -/
theorem avgOver_sub {α : Type*} (𝒟 : Distribution α) (f g : α → Error) :
    avgOver 𝒟 (fun a => f a - g a) =
      avgOver 𝒟 f - avgOver 𝒟 g := by
  change avgOver 𝒟 (f - g) = avgOver 𝒟 f - avgOver 𝒟 g
  simpa [Distribution.avgOver_eq_weightedSumLinearMap] using
    map_sub (𝒟.weightedSumLinearMap Error) f g
end
end MIPStarRE.LDT

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPStarRE.LDT.SelfImprovement
open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.GlobalVariance
open MIPStarRE.LDT.MakingMeasurementsProjective
open scoped BigOperators MatrixOrder Matrix ComplexOrder
set_option backward.isDefEq.respectTransparency false
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
theorem _root_.solution
    {Outcome : Type*} [Fintype Outcome]
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (M : IdxSubMeas (Point params) Outcome ι)
    (T : SubMeas (Polynomial params) ι)
    (S : AddInUSelection params Outcome)
    (delta : Error)
    (hssc : BipartiteSSCRel strategy.state (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement) delta) :
    |addInUSelectedCSChainQ0 params strategy M T S -
        addInUSelectedCSChainQ1 params strategy M T S| ≤
      Real.sqrt (2 * delta) := by
  classical
  have hSDD := addInU_pointMeasurement_snd_selfConsistency params strategy delta hssc
  let Aop : Point params × Point params → Fq params → MIPStarRE.Quantum.Op (ι × ι) :=
    fun uv a => leftTensor (ι₂ := ι)
      ((strategy.pointMeasurement uv.2).toSubMeas.outcome a)
  let Bop : Point params × Point params → Fq params → MIPStarRE.Quantum.Op (ι × ι) :=
    fun uv a => rightTensor (ι₁ := ι)
      ((strategy.pointMeasurement uv.2).toSubMeas.outcome a)
  let Cop : Point params × Point params → Fq params → Outcome × Polynomial params →
      MIPStarRE.Quantum.Op (ι × ι) :=
    fun uv a ah =>
      if ah ∈ (addInUSelectionPairs params S uv.1).filter (fun ah => ah.2 uv.2 = a) then
        opTensor ((M uv.1).outcome ah.1) (T.outcome ah.2) *
          rightTensor (ι₁ := ι)
            ((strategy.pointMeasurement uv.2).toSubMeas.outcome a)
      else 0
  have hOutcome_herm : ∀ (v : Point params) (a : Fq params),
      ((strategy.pointMeasurement v).toSubMeas.outcome a)ᴴ =
        (strategy.pointMeasurement v).toSubMeas.outcome a := fun v a =>
    (Matrix.nonneg_iff_posSemidef.mp
      ((strategy.pointMeasurement v).toSubMeas.outcome_pos a)).isHermitian.eq
  have hAop_herm : ∀ uv a, (Aop uv a)ᴴ = Aop uv a := by
    intro uv a
    change (leftTensor (ι₂ := ι)
        ((strategy.pointMeasurement uv.2).toSubMeas.outcome a))ᴴ =
      leftTensor (ι₂ := ι)
        ((strategy.pointMeasurement uv.2).toSubMeas.outcome a)
    rw [leftTensor_conjTranspose, hOutcome_herm uv.2 a]
  have hBop_herm : ∀ uv a, (Bop uv a)ᴴ = Bop uv a := by
    intro uv a
    change (rightTensor (ι₁ := ι)
        ((strategy.pointMeasurement uv.2).toSubMeas.outcome a))ᴴ =
      rightTensor (ι₁ := ι)
        ((strategy.pointMeasurement uv.2).toSubMeas.outcome a)
    rw [rightTensor_conjTranspose, hOutcome_herm uv.2 a]
  have hfun_A : ∀ uv : Point params × Point params,
      (fun a : Fq params => (Aop uv a)ᴴ) = Aop uv := by
    intro uv
    funext a
    exact hAop_herm uv a
  have hfun_B : ∀ uv : Point params × Point params,
      (fun a : Fq params => (Bop uv a)ᴴ) = Bop uv := by
    intro uv
    funext a
    exact hBop_herm uv a
  have hAB :
      avgOver (uniformDistribution (Point params × Point params)) (fun uv =>
        qSDDCore strategy.state
          (fun a : Fq params => (Aop uv a)ᴴ) (fun a : Fq params => (Bop uv a)ᴴ)) ≤
        2 * delta := by
    rcases hSDD with ⟨hsdd⟩
    refine le_trans ?_ hsdd
    refine le_of_eq ?_
    refine avgOver_congr _ _ _ ?_
    intro uv
    rw [hfun_A uv, hfun_B uv]
    try rfl -- vendoring compile fix (Lean v4.33): the previous step may close the goal
  have hsum_C : ∀ (uv : Point params × Point params) (a : Fq params),
      (∑ ah : Outcome × Polynomial params, Cop uv a ah) =
        ∑ ah ∈ (addInUSelectionPairs params S uv.1).filter (fun ah => ah.2 uv.2 = a),
          opTensor ((M uv.1).outcome ah.1) (T.outcome ah.2) *
            rightTensor (ι₁ := ι)
              ((strategy.pointMeasurement uv.2).toSubMeas.outcome a) := by
    intro uv a
    let s := (addInUSelectionPairs params S uv.1).filter (fun ah => ah.2 uv.2 = a)
    let f : Outcome × Polynomial params → MIPStarRE.Quantum.Op (ι × ι) := fun ah =>
      opTensor ((M uv.1).outcome ah.1) (T.outcome ah.2) *
        rightTensor (ι₁ := ι)
          ((strategy.pointMeasurement uv.2).toSubMeas.outcome a)
    have hfilter :
        (∑ ah : Outcome × Polynomial params, if ah ∈ s then f ah else 0) =
          ∑ ah ∈ s, f ah := by
      calc
        (∑ ah : Outcome × Polynomial params, if ah ∈ s then f ah else 0)
            = ∑ ah ∈ s, if ah ∈ s then f ah else 0 := by
                exact
                  (Finset.sum_subset (Finset.subset_univ s)
                    (fun ah _ hnot => by simp [hnot])).symm
        _ = ∑ ah ∈ s, f ah := by
              refine Finset.sum_congr rfl ?_
              intro ah hah
              simp [hah]
    simpa [Cop, s, f] using hfilter
  have hC : ∀ uv : Point params × Point params,
      (∑ a : Fq params,
          (∑ ah : Outcome × Polynomial params, Cop uv a ah)ᴴ *
            (∑ ah : Outcome × Polynomial params, Cop uv a ah)) ≤ 1 := by
    intro uv
    simpa [hsum_C uv] using addInU_selected_step1_C_contraction params strategy M T S uv
  have hcs := MIPStarRE.LDT.Preliminaries.closenessOfInnerProduct_right
    strategy.state strategy.isNormalized
    (uniformDistribution (Point params × Point params))
    (uniformDistribution_weight_sum_le_one (Point params × Point params))
    Aop Bop Cop (2 * delta) hAB hC
  have hcollapse :
      ∀ (uv : Point params × Point params)
        (D : (Point params × Point params) → Fq params →
          MIPStarRE.Quantum.Op (ι × ι)),
        (∑ a : Fq params, ∑ ah : Outcome × Polynomial params,
            ev strategy.state (D uv a * Cop uv a ah)) =
          ∑ ah ∈ addInUSelectionPairs params S uv.1,
            ev strategy.state
              (D uv (ah.2 uv.2) *
                (opTensor ((M uv.1).outcome ah.1) (T.outcome ah.2) *
                  rightTensor (ι₁ := ι)
                    ((strategy.pointMeasurement uv.2).toSubMeas.outcome (ah.2 uv.2)))) := by
    intro uv D
    rw [Finset.sum_comm]
    let s := addInUSelectionPairs params S uv.1
    let f : Outcome × Polynomial params → Error := fun ah =>
      ev strategy.state
        (D uv (ah.2 uv.2) *
          (opTensor ((M uv.1).outcome ah.1) (T.outcome ah.2) *
            rightTensor (ι₁ := ι)
              ((strategy.pointMeasurement uv.2).toSubMeas.outcome (ah.2 uv.2))))
    have hinner : ∀ ah : Outcome × Polynomial params,
        (∑ a : Fq params, ev strategy.state (D uv a * Cop uv a ah)) =
          if ah ∈ s then f ah else 0 := by
      intro ah
      by_cases hmem : ah ∈ s
      · rw [Finset.sum_eq_single (ah.2 uv.2)]
        · simp [Cop, s, f, hmem]
        · intro a _ ha
          have hnot : ah ∉ s.filter (fun bh => bh.2 uv.2 = a) := by
            intro hf
            exact ha (Eq.symm (Finset.mem_filter.mp hf).2)
          have hCop_zero : Cop uv a ah = 0 := by
            have hnot' :
                ¬ (ah ∈ addInUSelectionPairs params S uv.1 ∧ ah.2 uv.2 = a) := by
              intro hf
              exact hnot (Finset.mem_filter.mpr hf)
            simp [Cop, hnot']
          rw [hCop_zero, Matrix.mul_zero, ev_zero]
        · intro hmissing
          exact (hmissing (Finset.mem_univ _)).elim
      · have hzero : ∀ a : Fq params, ah ∉ s.filter (fun bh => bh.2 uv.2 = a) := by
          intro a hf
          exact hmem ((Finset.mem_filter.mp hf).1)
        calc
          ∑ a : Fq params, ev strategy.state (D uv a * Cop uv a ah)
              = ∑ a : Fq params, 0 := by
                  refine Finset.sum_congr rfl ?_
                  intro a _
                  have hCop_zero : Cop uv a ah = 0 := by
                    have hnot' :
                        ¬ (ah ∈ addInUSelectionPairs params S uv.1 ∧ ah.2 uv.2 = a) := by
                      intro hf
                      exact hzero a (Finset.mem_filter.mpr hf)
                    simp [Cop, hnot']
                  rw [hCop_zero, Matrix.mul_zero, ev_zero]
          _ = if ah ∈ s then f ah else 0 := by simp [hmem]
    calc
      ∑ ah : Outcome × Polynomial params,
          ∑ a : Fq params, ev strategy.state (D uv a * Cop uv a ah)
          = ∑ ah : Outcome × Polynomial params, if ah ∈ s then f ah else 0 := by
              refine Finset.sum_congr rfl ?_
              intro ah _
              exact hinner ah
      _ = ∑ ah ∈ s, f ah := by
            have hfilter :
                (∑ ah : Outcome × Polynomial params, if ah ∈ s then f ah else 0) =
                  ∑ ah ∈ s, f ah := by
              calc
                (∑ ah : Outcome × Polynomial params, if ah ∈ s then f ah else 0)
                    = ∑ ah ∈ s, if ah ∈ s then f ah else 0 := by
                        exact
                          (Finset.sum_subset (Finset.subset_univ s)
                            (fun ah _ hnot => by simp [hnot])).symm
                _ = ∑ ah ∈ s, f ah := by
                      refine Finset.sum_congr rfl ?_
                      intro ah hah
                      simp [hah]
            exact hfilter
  have hmatch_pointwise : ∀ uv : Point params × Point params,
      (∑ a : Fq params, ∑ ah : Outcome × Polynomial params,
          ev strategy.state (Aop uv a * Cop uv a ah)) -
        (∑ a : Fq params, ∑ ah : Outcome × Polynomial params,
          ev strategy.state (Bop uv a * Cop uv a ah)) =
      ∑ ah ∈ addInUSelectionPairs params S uv.1,
        let Av := pointConditionedOutcomeOperatorAtPolynomial params strategy ah.2 uv.2
        let Moh := (M uv.1).outcome ah.1
        ev strategy.state
          ((leftTensor (ι₂ := ι) Av - rightTensor (ι₁ := ι) Av) *
            (opTensor Moh (T.outcome ah.2) * rightTensor (ι₁ := ι) Av)) := by
    intro uv
    rw [hcollapse uv Aop, hcollapse uv Bop]
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl ?_
    intro ah _
    rw [← ev_sub]
    congr 1
    change
      leftTensor (ι₂ := ι)
          (pointConditionedOutcomeOperatorAtPolynomial params strategy ah.2 uv.2) *
          (opTensor ((M uv.1).outcome ah.1) (T.outcome ah.2) *
            rightTensor (ι₁ := ι)
              (pointConditionedOutcomeOperatorAtPolynomial params strategy ah.2 uv.2)) -
        rightTensor (ι₁ := ι)
          (pointConditionedOutcomeOperatorAtPolynomial params strategy ah.2 uv.2) *
          (opTensor ((M uv.1).outcome ah.1) (T.outcome ah.2) *
            rightTensor (ι₁ := ι)
              (pointConditionedOutcomeOperatorAtPolynomial params strategy ah.2 uv.2)) =
        (leftTensor (ι₂ := ι)
            (pointConditionedOutcomeOperatorAtPolynomial params strategy ah.2 uv.2) -
          rightTensor (ι₁ := ι)
            (pointConditionedOutcomeOperatorAtPolynomial params strategy ah.2 uv.2)) *
          (opTensor ((M uv.1).outcome ah.1) (T.outcome ah.2) *
            rightTensor (ι₁ := ι)
              (pointConditionedOutcomeOperatorAtPolynomial params strategy ah.2 uv.2))
    noncomm_ring
  have hmatch :
      avgOver (uniformDistribution (Point params × Point params)) (fun uv =>
        ∑ a : Fq params, ∑ ah : Outcome × Polynomial params,
          ev strategy.state (Aop uv a * Cop uv a ah)) -
      avgOver (uniformDistribution (Point params × Point params)) (fun uv =>
        ∑ a : Fq params, ∑ ah : Outcome × Polynomial params,
          ev strategy.state (Bop uv a * Cop uv a ah)) =
      addInUSelectedCSChainQ1 params strategy M T S -
        addInUSelectedCSChainQ0 params strategy M T S := by
    rw [addInU_selected_cs_chain_step1_diff_eq params strategy M T S]
    rw [← avgOver_sub]
    refine avgOver_congr _ _ _ ?_
    intro uv
    exact hmatch_pointwise uv
  rw [abs_sub_comm]
  rw [← hmatch]
  exact hcs
end MIPStarRE.LDT.SelfImprovement
