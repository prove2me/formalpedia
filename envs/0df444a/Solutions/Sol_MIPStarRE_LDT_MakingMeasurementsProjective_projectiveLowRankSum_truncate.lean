-- Prove2me | solution 1 for MIPStarRE.LDT.MakingMeasurementsProjective.projectiveLowRankSum_truncate
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T03:55:17.146592+00:00
-- url     : https://prove2.me/submissions/b5cc6c9e-aa90-4ca5-9bef-a700c8d61990

/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE, with the
authors' permission. Vendored from https://github.com/LionSR/MIPStarRE
(commit 507e8122, 2026-08-25) by scripts/vendor-lidt.py; do not edit by hand.
Upstream path: MIPStarRE/LDT/MakingMeasurementsProjective/QXPLayer/RankReduction/LowRank.lean
-/
/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE, with the
authors' permission. Vendored from https://github.com/LionSR/MIPStarRE
(commit 507e8122, 2026-08-25) by scripts/vendor-lidt.py; do not edit by hand.
Upstream path: MIPStarRE/LDT/Preliminaries/DistanceBounds.lean
-/
/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE, with the
authors' permission. Vendored from https://github.com/LionSR/MIPStarRE
(commit 507e8122, 2026-08-25) by scripts/vendor-lidt.py; do not edit by hand.
Upstream path: MIPStarRE/LDT/MakingMeasurementsProjective/QXPLayer/Core.lean
-/
/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE, with the
authors' permission. Vendored from https://github.com/LionSR/MIPStarRE
(commit 507e8122, 2026-08-25) by scripts/vendor-lidt.py; do not edit by hand.
Upstream path: MIPStarRE/LDT/Preliminaries/CompletionTransfer.lean
-/
/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE, with the
authors' permission. Vendored from https://github.com/LionSR/MIPStarRE
(commit 507e8122, 2026-08-25) by scripts/vendor-lidt.py; do not edit by hand.
Upstream path: MIPStarRE/Quantum/ProjectorONB.lean
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/LIDT/MIPStarRE/LDT/MakingMeasurementsProjective/QXPLayer/RankReduction/LowRank.lean (solution of MIPStarRE.LDT.MakingMeasurementsProjective.projectiveLowRankSum_truncate);
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
import Mathlib.Algebra.BigOperators.Group.Multiset.Defs
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
import Mathlib.Analysis.CStarAlgebra.Module.Constructions
import Mathlib.Analysis.CStarAlgebra.Module.Defs
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.Convex.Cone.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.LocallyConvex.WithSeminorms
import Mathlib.Analysis.Matrix.Hermitian
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Matrix.Spectrum
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
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Sigma
import Mathlib.Data.Finsupp.Defs
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sets
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.FunLike.Basic
import Mathlib.Data.FunLike.Equiv
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.List.Nodup
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Basis
import Mathlib.Data.Matrix.Block
import Mathlib.Data.Matrix.Diagonal
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Multiset.Bind
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
import Mathlib.Data.Sigma.Basic
import Mathlib.Data.ULift
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
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Logic.Basic
import Mathlib.Logic.Equiv.Defs
import Mathlib.Logic.Equiv.Prod
import Mathlib.Logic.Function.Defs
import Mathlib.Logic.IsEmpty.Basic
import Mathlib.Logic.IsEmpty.Defs
import Mathlib.Logic.Nonempty
import Mathlib.Logic.Nontrivial.Defs
import Mathlib.Logic.Unique
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Order.Basic
import Mathlib.Order.BooleanAlgebra.Defs
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
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_QXPLayer_Core
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Preliminaries_CompletionTransfer
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_Quantum_ProjectorONB
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_QXPLayer_RankReduction_Sigma
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_QXPLayer_RankReduction_LowRank
import Theorems.Thm_MIPStarRE_LDT_MakingMeasurementsProjective_Truncation_exists_large_subset_ordered
import Theorems.Thm_MIPStarRE_LDT_MakingMeasurementsProjective_Truncation_sum_small_le_four_sqrt
import Theorems.Thm_MIPStarRE_LDT_MakingMeasurementsProjective_projectiveLowRankSum_auxData_of_rank_bound
import Theorems.Thm_MIPStarRE_LDT_MakingMeasurementsProjective_projectiveLowRankSum_of_rank_bound
import Theorems.Thm_MIPStarRE_LDT_MakingMeasurementsProjective_sum_rank_le_scalar_mul_card_of_projectors_le
import Theorems.Thm_MIPStarRE_LDT_Preliminaries_stateDependentDistanceOpRel_triangle
import Theorems.Thm_MIPStarRE_LDT_ev_mono
import Theorems.Thm_MIPStarRE_LDT_ev_scale
import Theorems.Thm_MIPStarRE_Quantum_IsProj_trace_eq_rank
import Theorems.Thm_MIPStarRE_Quantum_ProjectorRangeONB_subprojector_diff_eq_compl
import Theorems.Thm_MIPStarRE_Quantum_ProjectorRangeONB_subprojector_isProj
import Theorems.Thm_MIPStarRE_Quantum_ProjectorRangeONB_subprojector_trace

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

namespace MIPStarRE.LDT.MakingMeasurementsProjective
noncomputable section
open scoped BigOperators MatrixOrder Matrix ComplexOrder
open MIPStarRE.LDT
set_option backward.isDefEq.respectTransparency false
universe uOutcome uι
/-- The truncation error is `√ζ`. -/
lemma spectralTruncationError_eq_sqrt (ζ : Error) :
    spectralTruncationError ζ = Real.sqrt ζ := by
  simp [spectralTruncationError, Real.sqrt_eq_rpow]
end
end MIPStarRE.LDT.MakingMeasurementsProjective

namespace MIPStarRE.LDT.Preliminaries
section
open scoped BigOperators MatrixOrder Matrix ComplexOrder
open MIPStarRE.LDT
set_option backward.isDefEq.respectTransparency false
/-- Triangle inequality for state-dependent operator distance. -/
lemma sddOpRel_triangle
    {Question Outcome : Type*} {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : QuantumState ι) (𝒟 : Distribution Question)
    (A B C : IdxOpFamily Question Outcome ι) (δ₁ δ₂ : Error) :
    SDDOpRel ψ 𝒟 A B δ₁ →
    SDDOpRel ψ 𝒟 B C δ₂ →
    SDDOpRel ψ 𝒟 A C (2 * (δ₁ + δ₂)) :=
  stateDependentDistanceOpRel_triangle ψ 𝒟 A B C δ₁ δ₂
end
end MIPStarRE.LDT.Preliminaries

namespace MIPStarRE.LDT.Preliminaries
section
open scoped BigOperators MatrixOrder Matrix ComplexOrder
open MIPStarRE.LDT
set_option backward.isDefEq.respectTransparency false
/-- Monotonicity for `SDDOpRel`. -/
lemma sddOpRel_mono
    {Question Outcome : Type*} {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : QuantumState ι) (𝒟 : Distribution Question)
    (A B : IdxOpFamily Question Outcome ι) (δ δ' : Error) :
    SDDOpRel ψ 𝒟 A B δ → δ ≤ δ' → SDDOpRel ψ 𝒟 A B δ' := by
  intro h hle
  exact stateDependentDistanceOpRel_mono ψ 𝒟 A B δ δ' hle h
end
end MIPStarRE.LDT.Preliminaries

namespace MIPStarRE.Quantum.ProjectorRangeONB
noncomputable section
open scoped BigOperators MatrixOrder Matrix ComplexOrder Matrix.Norms.L2Operator
set_option backward.isDefEq.respectTransparency false
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {P : Op ι} {hP : IsProj P} (b : ProjectorRangeONB P hP)
omit [DecidableEq ι] in
/-- The rank of a selected sum is exactly the number of selected ONB vectors. -/
lemma subprojector_rank (S : Finset (Fin P.rank)) :
    (b.subprojector S).rank = S.card := by
  have htrace_rank := IsProj.trace_eq_rank (b.subprojector S) (b.subprojector_isProj S)
  have htrace_card := b.subprojector_trace S
  have hcast : ((b.subprojector S).rank : ℂ) = (S.card : ℂ) := by
    rw [← htrace_rank, htrace_card]
  exact_mod_cast hcast
end
end MIPStarRE.Quantum.ProjectorRangeONB

namespace MIPStarRE.Quantum.ProjectorRangeONB
noncomputable section
open scoped BigOperators MatrixOrder Matrix ComplexOrder Matrix.Norms.L2Operator
set_option backward.isDefEq.respectTransparency false
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {P : Op ι} {hP : IsProj P} (b : ProjectorRangeONB P hP)
omit [DecidableEq ι] in
/-- A partial projector is dominated by the original projector. -/
lemma subprojector_le (S : Finset (Fin P.rank)) :
    b.subprojector S ≤ P := by
  rw [← sub_nonneg]
  rw [b.subprojector_diff_eq_compl S]
  exact (b.subprojector_isProj (Sᶜ : Finset (Fin P.rank))).nonneg
end
end MIPStarRE.Quantum.ProjectorRangeONB

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPStarRE.LDT.MakingMeasurementsProjective
open scoped BigOperators MatrixOrder Matrix ComplexOrder
open MIPStarRE.LDT
set_option backward.isDefEq.respectTransparency false
universe uOutcome uι
theorem _root_.solution {Outcome : Type uOutcome}
    {ι : Type uι} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    [Fintype Outcome] [Nonempty Outcome]
    (ψ : QuantumState ι) (hψ : ψ.IsNormalized)
    (A : Measurement Outcome ι) (ζ : Error)
    (hζ : 0 ≤ ζ) (hζ_le : ζ ≤ 1 / 4)
    (R : OpFamily Outcome ι)
    (hR : RoundingToProjectorsWitness ψ A ζ R)
    (source_almost_projective :
      ∑ a, ev ψ (A.outcome a - A.outcome a * A.outcome a) ≤ 2 * ζ) :
    ∃ data : QLayerData Outcome ι,
      RankReductionWitness ψ A ζ data := by
  classical
  let d : ℕ := Fintype.card ι
  let Idx : Type uOutcome := Σ a : Outcome, Fin (R.outcome a).rank
  letI : Fintype Idx := inferInstance
  letI : DecidableEq Idx := Classical.decEq Idx
  by_cases hr : Fintype.card Idx ≤ d
  · have hrank : ∑ a, (R.outcome a).rank ≤ Fintype.card ι := by
      simpa [Idx, d, Fintype.card_sigma] using hr
    exact projectiveLowRankSum_of_rank_bound ψ A ζ hζ R hR hrank source_almost_projective
  · have hcard_gt : d < Fintype.card Idx := Nat.lt_of_not_ge hr
    let onb : (a : Outcome) →
        MIPStarRE.Quantum.ProjectorRangeONB (R.outcome a) (hR.projective a) :=
      fun a => MIPStarRE.Quantum.IsProj.rangeONB (R.outcome a) (hR.projective a)
    let rankOne : Idx → MIPStarRE.Quantum.Op ι := fun x => (onb x.1).rankOne x.2
    let overlap : Idx → Error := fun x => ev ψ (rankOne x)
    have hd_le : d ≤ Fintype.card Idx := le_of_lt hcard_gt
    obtain ⟨Large, hLarge_card, hLarge_order⟩ :=
      Truncation.exists_large_subset_ordered (α := Idx) overlap hd_le
    let fiber : (a : Outcome) → Finset (Fin (R.outcome a).rank) := fun a =>
      (Finset.univ : Finset (Fin (R.outcome a).rank)).filter
        (fun i => (⟨a, i⟩ : Idx) ∈ Large)
    let Q : OpFamily Outcome ι :=
      { outcome := fun a => (onb a).subprojector (fiber a)
        total := ∑ a, (onb a).subprojector (fiber a) }
    have hRsum_le : (∑ a, R.outcome a) ≤
        (((1 : Error) + 2 * spectralTruncationError ζ) : ℂ) •
          (1 : MIPStarRE.Quantum.Op ι) := by
      simpa [hR.sum_eq_total] using hR.total_le
    have hspectral_sqrt : spectralTruncationError ζ = Real.sqrt ζ :=
      spectralTruncationError_eq_sqrt ζ
    have hr_bound : (Fintype.card Idx : Error) ≤ (1 + 2 * Real.sqrt ζ) * d := by
      have hcard_idx : Fintype.card Idx = ∑ a, (R.outcome a).rank := by
        simp [Idx, Fintype.card_sigma]
      have hRsum_le_for_rank : (∑ a, R.outcome a) ≤
          ((((1 : Error) + 2 * spectralTruncationError ζ : Error) : ℂ) •
            (1 : MIPStarRE.Quantum.Op ι)) := by
        simpa using hRsum_le
      have hrank_bound :=
        sum_rank_le_scalar_mul_card_of_projectors_le (R := R.outcome)
          (hproj := hR.projective)
          (c := 1 + 2 * spectralTruncationError ζ) hRsum_le_for_rank
      rw [show (Fintype.card Idx : Error) = ((∑ a, (R.outcome a).rank : ℕ) : Error) by
        exact_mod_cast hcard_idx]
      simpa [d, hspectral_sqrt] using hrank_bound
    have hLarge_sigma :
        Large = (Finset.univ : Finset Outcome).sigma (fun a => fiber a) := by
      ext x
      rcases x with ⟨a, i⟩
      constructor
      · intro h
        exact Finset.mem_sigma.mpr ⟨Finset.mem_univ a, by simp [fiber, h]⟩
      · intro h
        rcases Finset.mem_sigma.mp h with ⟨_, hi⟩
        simpa [fiber] using hi
    have hLarge_card_sum : Large.card = ∑ a, (fiber a).card := by
      rw [hLarge_sigma]
      change (Multiset.card (Multiset.sigma Finset.univ.val fun a => (fiber a).val)) =
        ∑ a, (fiber a).card
      rw [Multiset.card_sigma]
      try rfl -- vendoring compile fix (Lean v4.33): the previous step may close the goal
    have hrankQ : ∑ a, (Q.outcome a).rank ≤ Fintype.card ι := by
      have hsum_rank : ∑ a, (Q.outcome a).rank = ∑ a, (fiber a).card := by
        refine Finset.sum_congr rfl ?_
        intro a _
        simp [Q, MIPStarRE.Quantum.ProjectorRangeONB.subprojector_rank]
      calc
        ∑ a, (Q.outcome a).rank = ∑ a, (fiber a).card := hsum_rank
        _ = Large.card := hLarge_card_sum.symm
        _ = Fintype.card ι := by simpa [d] using hLarge_card
        _ ≤ Fintype.card ι := le_rfl
    have htotal_overlap : (∑ x : Idx, overlap x) ≤ 1 + 2 * Real.sqrt ζ := by
      have hoverlap_eq_ev_sum : (∑ x : Idx, overlap x) = ev ψ (∑ a, R.outcome a) := by
        simpa [Idx, overlap, rankOne] using
          (projectiveLowRankSum_truncationOverlap_eq_ev_sum
            (ψ := ψ) (R := R) (hproj := hR.projective) (onb := onb))
      have hev_le : ev ψ (∑ a, R.outcome a) ≤
          ev ψ ((((1 : Error) + 2 * spectralTruncationError ζ) : ℂ) •
            (1 : MIPStarRE.Quantum.Op ι)) := ev_mono ψ _ _ hRsum_le
      calc
        ∑ x : Idx, overlap x = ev ψ (∑ a, R.outcome a) := hoverlap_eq_ev_sum
        _ ≤ ev ψ ((((1 : Error) + 2 * spectralTruncationError ζ) : ℂ) •
            (1 : MIPStarRE.Quantum.Op ι)) := hev_le
        _ = 1 + 2 * Real.sqrt ζ := by
              have h :
                  ev ψ ((((1 : Error) + 2 * spectralTruncationError ζ : Error) : ℂ) •
                    (1 : MIPStarRE.Quantum.Op ι)) =
                    1 + 2 * Real.sqrt ζ := by
                calc
                  ev ψ ((((1 : Error) + 2 * spectralTruncationError ζ : Error) : ℂ) •
                      (1 : MIPStarRE.Quantum.Op ι))
                      = (1 + 2 * spectralTruncationError ζ) *
                          ev ψ (1 : MIPStarRE.Quantum.Op ι) :=
                        ev_scale ψ (1 + 2 * spectralTruncationError ζ)
                          (1 : MIPStarRE.Quantum.Op ι)
                  _ = 1 + 2 * Real.sqrt ζ := by
                        rw [ev_one_of_isNormalized ψ hψ, spectralTruncationError_eq_sqrt ζ]
                        ring
              simpa using h
    have hsmall : (∑ x ∈ (Largeᶜ : Finset Idx), overlap x) ≤ 4 * Real.sqrt ζ :=
      Truncation.sum_small_le_four_sqrt (α := Idx) Large
        (hL_card := hLarge_card) (hcard_gt := hcard_gt) (hr_bound := hr_bound)
        (hf_ordering := hLarge_order) (htotal := htotal_overlap)
        (hζ_nonneg := hζ) (hζ_le := hζ_le)
    have hLarge_compl_sigma :
        (Largeᶜ : Finset Idx) = (Finset.univ : Finset Outcome).sigma
          (fun a => (fiber a)ᶜ) := by
      ext x
      rcases x with ⟨a, i⟩
      constructor
      · intro h
        exact Finset.mem_sigma.mpr ⟨Finset.mem_univ a, by simpa [fiber] using h⟩
      · intro h
        rcases Finset.mem_sigma.mp h with ⟨_, hi⟩
        simpa [fiber] using hi
    have hqSDD_RQ : qSDDOp ψ R Q = ∑ x ∈ (Largeᶜ : Finset Idx), overlap x := by
      simpa [Q, Idx, overlap, rankOne] using
        (projectiveLowRankSum_qSDD_truncation_eq_compl_overlap
          (ψ := ψ) (R := R) (hproj := hR.projective) (onb := onb)
          (Large := Large) (fiber := fiber)
          (hLarge_compl_sigma := hLarge_compl_sigma))
    have hRQ : SDDOpRel ψ (uniformDistribution Unit) (constOpFamily R) (constOpFamily Q)
        (4 * spectralTruncationError ζ) := by
      have hcore : qSDDOp ψ R Q ≤ 4 * spectralTruncationError ζ := by
        calc
          qSDDOp ψ R Q = ∑ x ∈ (Largeᶜ : Finset Idx), overlap x := hqSDD_RQ
          _ ≤ 4 * Real.sqrt ζ := hsmall
          _ = 4 * spectralTruncationError ζ := by rw [hspectral_sqrt]
      constructor
      simpa [sddErrorOp, avgOver, uniformDistribution, constOpFamily] using hcore
    have hAQ : SDDOpRel ψ (uniformDistribution Unit)
        (constOpFamily (A.toSubMeas : OpFamily Outcome ι)) (constOpFamily Q)
        (roundingToProjectiveError ζ) := by
      have htri := MIPStarRE.LDT.Preliminaries.sddOpRel_triangle ψ (uniformDistribution Unit)
        (constOpFamily (A.toSubMeas : OpFamily Outcome ι)) (constOpFamily R) (constOpFamily Q)
        (2 * spectralTruncationError ζ) (4 * spectralTruncationError ζ)
        hR.closeness hRQ
      refine MIPStarRE.LDT.Preliminaries.sddOpRel_mono ψ (uniformDistribution Unit)
        (constOpFamily (A.toSubMeas : OpFamily Outcome ι)) (constOpFamily Q)
        (2 * (2 * spectralTruncationError ζ + 4 * spectralTruncationError ζ))
        (roundingToProjectiveError ζ) htri ?_
      dsimp [roundingToProjectiveError, spectralTruncationError]
      ring_nf
      exact le_rfl
    have hQtotal_le : Q.total ≤ (((1 : Error) + 2 * spectralTruncationError ζ) : ℂ) •
        (1 : MIPStarRE.Quantum.Op ι) := by
      have hpoint : ∀ a, Q.outcome a ≤ R.outcome a := by
        intro a
        simpa [Q] using (onb a).subprojector_le (fiber a)
      calc
        Q.total = ∑ a, Q.outcome a := rfl
        _ ≤ ∑ a, R.outcome a := Finset.sum_le_sum fun a _ => hpoint a
        _ ≤ (((1 : Error) + 2 * spectralTruncationError ζ) : ℂ) •
            (1 : MIPStarRE.Quantum.Op ι) := hRsum_le
    obtain ⟨auxSpace, t, _, hAuxDim⟩ :=
      projectiveLowRankSum_auxData_of_rank_bound
        (m := fun a : Outcome => (Q.outcome a).rank) hrankQ
    let data : QLayerData Outcome ι :=
      { auxSpace := auxSpace
        q := Q
        t := t }
    refine ⟨data, ?_⟩
    refine ⟨?_, ?_, ?_, source_almost_projective, ?_, ?_, ?_, ?_⟩
    · intro a
      simpa [Q, Qa, data] using (onb a).subprojector_isProj (fiber a)
    · intro a
      have hproj : MIPStarRE.Quantum.IsProj (Q.outcome a) := by
        simpa [Q] using (onb a).subprojector_isProj (fiber a)
      simpa [Qa, data] using hproj.nonneg
    · simp [Qa, QTotal, data, Q]
    · simpa [data] using hAQ
    · simpa [QTotal, data] using hQtotal_le
    · simpa [Qa, data] using hrankQ
    · simpa [data] using hAuxDim
end MIPStarRE.LDT.MakingMeasurementsProjective
