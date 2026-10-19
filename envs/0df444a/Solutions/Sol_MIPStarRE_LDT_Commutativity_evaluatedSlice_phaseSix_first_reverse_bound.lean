-- Prove2me | solution 1 for MIPStarRE.LDT.Commutativity.evaluatedSlice_phaseSix_first_reverse_bound
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T04:24:56.941793+00:00
-- url     : https://prove2.me/submissions/0df62d2a-baec-4496-91ee-e7955a55374c

/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE, with the
authors' permission. Vendored from https://github.com/LionSR/MIPStarRE
(commit 507e8122, 2026-08-25) by scripts/vendor-lidt.py; do not edit by hand.
Upstream path: MIPStarRE/LDT/Commutativity/ScalarApproximation/PaperChainPhaseSix.lean
-/
/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE, with the
authors' permission. Vendored from https://github.com/LionSR/MIPStarRE
(commit 507e8122, 2026-08-25) by scripts/vendor-lidt.py; do not edit by hand.
Upstream path: MIPStarRE/LDT/Preliminaries/CauchySchwarz.lean
-/
/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE, with the
authors' permission. Vendored from https://github.com/LionSR/MIPStarRE
(commit 507e8122, 2026-08-25) by scripts/vendor-lidt.py; do not edit by hand.
Upstream path: MIPStarRE/LDT/Commutativity/ScalarApproximation/PaperChainBasic/Normalization.lean
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/LIDT/MIPStarRE/LDT/Commutativity/ScalarApproximation/PaperChainPhaseSix.lean (solution of MIPStarRE.LDT.Commutativity.evaluatedSlice_phaseSix_first_reverse_bound);
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
import Theorems.Thm_MIPStarRE_LDT_Commutativity_leftRightTensor_prefix_pointMeasurement_adjoint_normalization
import Theorems.Thm_MIPStarRE_LDT_Preliminaries_closenessOfInnerProduct_right
import Theorems.Thm_MIPStarRE_LDT_Preliminaries_projSubMeas_outcome_mul_total_eq_outcome
import Theorems.Thm_MIPStarRE_LDT_ProjSubMeas_outcome_hermitian
import Theorems.Thm_MIPStarRE_LDT_SubMeas_total_nonneg
import Theorems.Thm_MIPStarRE_LDT_avgOver_congr
import Theorems.Thm_MIPStarRE_LDT_leftTensor_mul_leftTensor
import Theorems.Thm_MIPStarRE_LDT_leftTensor_mul_rightTensor_eq_opTensor
import Theorems.Thm_MIPStarRE_LDT_leftTensor_nonneg
import Theorems.Thm_MIPStarRE_LDT_opTensor_mul

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPStarRE.LDT.Preliminaries
section
open scoped BigOperators MatrixOrder Matrix ComplexOrder
open MIPStarRE.LDT
set_option backward.isDefEq.respectTransparency false
/-- `prop:closeness-of-ip` (`eq:closeness4`, adjoint version).

If `A† ≈_γ B†` and `Σ_a (Σ_b C_{a,b})†(Σ_b C_{a,b}) ≤ I`, then
`|𝔼_x Σ_{a,b} ⟨ψ| A_a C_{a,b} |ψ⟩ -
  𝔼_x Σ_{a,b} ⟨ψ| B_a C_{a,b} |ψ⟩| ≤ √γ`. -/
theorem closenessOfIPAdjoint
    {Question OutcomeA OutcomeB : Type*} {ι : Type*}
    [Fintype OutcomeA] [Fintype OutcomeB] [Fintype ι] [DecidableEq ι]
    (ψ : QuantumState ι) (hψ : ψ.IsNormalized)
    (𝒟 : Distribution Question)
    (h𝒟 : ∑ q ∈ 𝒟.support, 𝒟.weight q ≤ 1)
    (A B : Question → OutcomeA → MIPStarRE.Quantum.Op ι)
    (C : Question → OutcomeA → OutcomeB → MIPStarRE.Quantum.Op ι)
    (γ : Error)
    (hAB :
      avgOver 𝒟
        (fun q => qSDDCore ψ (fun a => (A q a)ᴴ) (fun a => (B q a)ᴴ)) ≤ γ)
    (hC :
      ∀ q,
        ∑ a : OutcomeA,
          (∑ b : OutcomeB, C q a b)ᴴ * (∑ b : OutcomeB, C q a b) ≤ 1) :
    |avgOver 𝒟 (fun q => ∑ a : OutcomeA, ∑ b : OutcomeB, ev ψ (A q a * C q a b)) -
        avgOver 𝒟 (fun q => ∑ a : OutcomeA, ∑ b : OutcomeB, ev ψ (B q a * C q a b))| ≤
      Real.sqrt γ := by
  simpa using closenessOfInnerProduct_right ψ hψ 𝒟 h𝒟 A B C γ hAB hC
end
end MIPStarRE.LDT.Preliminaries

namespace MIPStarRE.LDT.Commutativity
section
open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder Matrix ComplexOrder
set_option backward.isDefEq.respectTransparency false
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
/-- The total projector of a projective submeasurement absorbs each outcome on the left. -/
lemma projSubMeas_total_mul_outcome_eq_outcome
    {α : Type*} [Fintype α] (A : ProjSubMeas α ι) (a : α) :
    A.total * A.outcome a = A.outcome a := by
  have hright := MIPStarRE.LDT.Preliminaries.projSubMeas_outcome_mul_total_eq_outcome A a
  have htotal_herm : A.totalᴴ = A.total :=
    (Matrix.nonneg_iff_posSemidef.mp A.total_nonneg).isHermitian.eq
  have h := congrArg Matrix.conjTranspose hright
  simpa [Matrix.conjTranspose_mul, A.outcome_hermitian a, htotal_herm] using h
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
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (zeta : Error)
    (hnorm : strategy.state.IsNormalized)
    (family : IdxPolyFamily params ι)
    (hcombined_fst : SDDRel strategy.state
      (uniformDistribution (EvaluatedSliceQuestion params))
      (fun q => evaluatedPointFamilyLeft params family q.1)
      (fun q =>
        (MIPStarRE.LDT.Preliminaries.totalSandwichFamily
          (evaluatedPointFamily params family)
          (evaluatedSlicePointMeas params strategy) q.1))
      (4 * zeta)) :
    let 𝒟 := uniformDistribution (EvaluatedSliceQuestion params)
    let phase5PaperRemoved : EvaluatedSliceQuestion params → Error :=
      evaluatedSlicePhaseFivePaperRemoved params strategy family
    let phase6FirstRemoved : EvaluatedSliceQuestion params → Error :=
      evaluatedSlicePhaseSixFirstRemoved params strategy family
    |avgOver 𝒟 phase5PaperRemoved - avgOver 𝒟 phase6FirstRemoved| ≤
      2 * Real.sqrt zeta := by
  let 𝒟 : Distribution (EvaluatedSliceQuestion params) :=
    uniformDistribution (EvaluatedSliceQuestion params)
  let pointMeas : IdxMeas (Point params.next) (Fq params) ι :=
    evaluatedSlicePointMeas params strategy
  let phase5PaperRemoved : EvaluatedSliceQuestion params → Error :=
    evaluatedSlicePhaseFivePaperRemoved params strategy family
  let phase6FirstReverse : EvaluatedSliceQuestion params → Error :=
    evaluatedSlicePhaseSixFirstReverse params strategy family
  let phase6FirstRemoved : EvaluatedSliceQuestion params → Error :=
    evaluatedSlicePhaseSixFirstRemoved params strategy family
  have h𝒟 : ∑ q ∈ 𝒟.support, 𝒟.weight q ≤ 1 := by
    simpa [𝒟] using
      uniformDistribution_weight_sum_le_one (EvaluatedSliceQuestion params)
  let Aop : EvaluatedSliceQuestion params → Fq params → MIPStarRE.Quantum.Op (ι × ι) :=
    fun q a => leftTensor (ι₂ := ι) ((evaluatedSliceFirstFactor params family q).outcome a)
  let Bop : EvaluatedSliceQuestion params → Fq params → MIPStarRE.Quantum.Op (ι × ι) :=
    fun q a =>
      ((MIPStarRE.LDT.Preliminaries.totalSandwichFamily
        (evaluatedPointFamily params family)
        (evaluatedSlicePointMeas params strategy) q.1).outcome a)
  let C : EvaluatedSliceQuestion params → Fq params → Fq params →
      MIPStarRE.Quantum.Op (ι × ι) := fun q a b =>
    leftTensor (ι₂ := ι)
        (((evaluatedSliceFirstFactor params family q).outcome a) *
          ((evaluatedSliceSecondFactor params family q).outcome b)) *
      rightTensor (ι₁ := ι)
        ((evaluatedSlicePointMeas params strategy q.2).outcome b)
  have hAop_herm : ∀ q a, (Aop q a)ᴴ = Aop q a := by
    intro q a
    exact
      (Matrix.nonneg_iff_posSemidef.mp
        (leftTensor_nonneg (ι₂ := ι)
          ((evaluatedSliceFirstFactor params family q).outcome_pos a))).isHermitian.eq
  have hBop_herm : ∀ q a, (Bop q a)ᴴ = Bop q a := by
    intro q a
    exact
      (Matrix.nonneg_iff_posSemidef.mp
        ((MIPStarRE.LDT.Preliminaries.totalSandwichFamily
          (evaluatedPointFamily params family)
          (evaluatedSlicePointMeas params strategy) q.1).outcome_pos a)).isHermitian.eq
  have hAB :
      avgOver 𝒟 (fun q =>
        qSDDCore strategy.state (fun a => (Aop q a)ᴴ) (fun a => (Bop q a)ᴴ)) ≤
        4 * zeta := by
    calc
      avgOver 𝒟 (fun q =>
          qSDDCore strategy.state (fun a => (Aop q a)ᴴ) (fun a => (Bop q a)ᴴ))
          = avgOver 𝒟 (fun q => qSDDCore strategy.state (Aop q) (Bop q)) := by
            apply avgOver_congr
            intro q
            simp only [qSDDCore, hAop_herm q, hBop_herm q]
      _ ≤ 4 * zeta := by
          have hbound := hcombined_fst.squaredDistanceBound
          change avgOver 𝒟 (fun q => qSDDCore strategy.state (Aop q) (Bop q)) ≤
            4 * zeta at hbound
          exact hbound
  have hC :
      ∀ q,
        ∑ a : Fq params, (∑ b : Fq params, C q a b)ᴴ * (∑ b : Fq params, C q a b) ≤ 1 := by
    intro q
    simpa [C, evaluatedSlicePointMeas, Parameters.next] using
      (leftRightTensor_prefix_pointMeasurement_adjoint_normalization
        (A := evaluatedSliceFirstFactor params family q)
        (B := evaluatedSliceSecondFactor params family q)
        (R := strategy.pointMeasurement q.2))
  have hreverse_norm :
      avgOver 𝒟 phase6FirstReverse =
        avgOver 𝒟 (fun q => ∑ a : Fq params, ∑ b : Fq params,
          ev strategy.state (Aop q a * C q a b)) := by
    apply avgOver_congr
    intro q
    dsimp [phase6FirstReverse, evaluatedSlicePhaseSixFirstReverse, Aop, C]
    refine Finset.sum_congr rfl ?_
    intro a _
    refine Finset.sum_congr rfl ?_
    intro b _
    congr 1
    rw [← mul_assoc, leftTensor_mul_leftTensor, mul_assoc]
  have hpaper_norm :
      avgOver 𝒟 phase5PaperRemoved =
        avgOver 𝒟 (fun q => ∑ a : Fq params, ∑ b : Fq params,
          ev strategy.state (Bop q a * C q a b)) := by
    apply avgOver_congr
    intro q
    dsimp [phase5PaperRemoved, evaluatedSlicePhaseFivePaperRemoved, Bop, C]
    refine Finset.sum_congr rfl ?_
    intro a _
    refine Finset.sum_congr rfl ?_
    intro b _
    congr 1
    have htotal_left :
        (evaluatedSliceFirstFactor params family q).total *
            (evaluatedSliceFirstFactor params family q).outcome a =
          (evaluatedSliceFirstFactor params family q).outcome a := by
      simpa [evaluatedSliceFirstProj] using
        (projSubMeas_total_mul_outcome_eq_outcome
          (A := evaluatedSliceFirstProj params family q) a)
    have htotal_left' :
        (evaluatedPointFamily params family q.1).total *
            (evaluatedSliceFirstFactor params family q).outcome a =
          (evaluatedSliceFirstFactor params family q).outcome a := by
      simpa [evaluatedSliceFirstFactor] using htotal_left
    have htotal_prod :
        (evaluatedPointFamily params family q.1).total *
            ((evaluatedSliceFirstFactor params family q).outcome a *
              (evaluatedSliceSecondFactor params family q).outcome b) =
          (evaluatedSliceFirstFactor params family q).outcome a *
            (evaluatedSliceSecondFactor params family q).outcome b := by
      rw [← mul_assoc, htotal_left']
    calc
      leftTensor (ι₂ := ι)
            ((evaluatedSliceFirstFactor params family q).outcome a *
              (evaluatedSliceSecondFactor params family q).outcome b) *
          rightTensor (ι₁ := ι)
            ((evaluatedSlicePointMeas params strategy q.1).outcome a *
              (evaluatedSlicePointMeas params strategy q.2).outcome b)
        = opTensor
            ((evaluatedSliceFirstFactor params family q).outcome a *
              (evaluatedSliceSecondFactor params family q).outcome b)
            ((evaluatedSlicePointMeas params strategy q.1).outcome a *
              (evaluatedSlicePointMeas params strategy q.2).outcome b) := by
            rw [leftTensor_mul_rightTensor_eq_opTensor]
      _ = opTensor
            ((evaluatedPointFamily params family q.1).total *
              ((evaluatedSliceFirstFactor params family q).outcome a *
                (evaluatedSliceSecondFactor params family q).outcome b))
            ((evaluatedSlicePointMeas params strategy q.1).outcome a *
              (evaluatedSlicePointMeas params strategy q.2).outcome b) := by
            exact (congrArg
              (fun X => opTensor X
                ((evaluatedSlicePointMeas params strategy q.1).outcome a *
                  (evaluatedSlicePointMeas params strategy q.2).outcome b)) htotal_prod).symm
      _ = (leftTensor (ι₂ := ι) (evaluatedPointFamily params family q.1).total *
            rightTensor (ι₁ := ι)
              ((evaluatedSlicePointMeas params strategy q.1).outcome a)) *
          (leftTensor (ι₂ := ι)
              ((evaluatedSliceFirstFactor params family q).outcome a *
                (evaluatedSliceSecondFactor params family q).outcome b) *
            rightTensor (ι₁ := ι)
              ((evaluatedSlicePointMeas params strategy q.2).outcome b)) := by
            rw [leftTensor_mul_rightTensor_eq_opTensor,
              leftTensor_mul_rightTensor_eq_opTensor, opTensor_mul]
  have hproject :
      avgOver 𝒟 phase6FirstReverse = avgOver 𝒟 phase6FirstRemoved := by
    apply avgOver_congr
    intro q
    dsimp [phase6FirstReverse, phase6FirstRemoved,
      evaluatedSlicePhaseSixFirstReverse, evaluatedSlicePhaseSixFirstRemoved]
    refine Finset.sum_congr rfl ?_
    intro a _
    refine Finset.sum_congr rfl ?_
    intro b _
    have hAproj :
        (evaluatedSliceFirstFactor params family q).outcome a *
            (evaluatedSliceFirstFactor params family q).outcome a =
          (evaluatedSliceFirstFactor params family q).outcome a := by
      simpa [evaluatedSliceFirstFactor] using
        evaluatedPointFamily_outcome_proj params family q.1 a
    simp [hAproj]
  have hclose :=
    MIPStarRE.LDT.Preliminaries.closenessOfIPAdjoint
      strategy.state hnorm 𝒟 h𝒟 Aop Bop C (4 * zeta) hAB hC
  have hclose' :
      |avgOver 𝒟 phase6FirstReverse - avgOver 𝒟 phase5PaperRemoved| ≤
        2 * Real.sqrt zeta := by
    calc
      |avgOver 𝒟 phase6FirstReverse - avgOver 𝒟 phase5PaperRemoved|
          = |avgOver 𝒟 (fun q => ∑ a : Fq params, ∑ b : Fq params,
              ev strategy.state (Aop q a * C q a b)) -
            avgOver 𝒟 (fun q => ∑ a : Fq params, ∑ b : Fq params,
              ev strategy.state (Bop q a * C q a b))| := by
              rw [hreverse_norm, hpaper_norm]
      _ ≤ Real.sqrt (4 * zeta) := hclose
      _ = 2 * Real.sqrt zeta := by
            rw [Real.sqrt_mul (show 0 ≤ (4 : Error) by positivity)]
            norm_num
  calc
    |avgOver 𝒟 phase5PaperRemoved - avgOver 𝒟 phase6FirstRemoved|
        = |avgOver 𝒟 phase6FirstReverse - avgOver 𝒟 phase5PaperRemoved| := by
          rw [← hproject, abs_sub_comm]
    _ ≤ 2 * Real.sqrt zeta := hclose'
end MIPStarRE.LDT.Commutativity
