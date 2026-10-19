-- Prove2me | solution 1 for MIPStarRE.LDT.Pasting.ldDnoteq
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T04:36:49.506031+00:00
-- url     : https://prove2.me/submissions/390ff137-70f2-4e30-a7e9-2c21deb4ece0

/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE, with the
authors' permission. Vendored from https://github.com/LionSR/MIPStarRE
(commit 507e8122, 2026-08-25) by scripts/vendor-lidt.py; do not edit by hand.
Upstream path: MIPStarRE/LDT/Pasting/Core/DDistinct.lean
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
Upstream path: MIPStarRE/LDT/Pasting/Defs/Tuples.lean
-/
/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE, with the
authors' permission. Vendored from https://github.com/LionSR/MIPStarRE
(commit 507e8122, 2026-08-25) by scripts/vendor-lidt.py; do not edit by hand.
Upstream path: MIPStarRE/LDT/Basic/DistributionUniform.lean
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/LIDT/MIPStarRE/LDT/Pasting/Core/DDistinct.lean (solution of MIPStarRE.LDT.Pasting.ldDnoteq);
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
import Mathlib.Algebra.BigOperators.Intervals
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
import Mathlib.Algebra.Group.Invertible.Basic
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
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Defs
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
import Mathlib.Data.Finset.Lattice.Lemmas
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
import Mathlib.Data.Int.Cast.Basic
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
import Mathlib.Data.Nat.Factorial.BigOperators
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
import Theorems.Thm_PMF_totalVariationDistance_uniformOfFintype_uniformOfFinset_eq

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
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

namespace MIPStarRE.LDT
section
open scoped BigOperators MatrixOrder Matrix ComplexOrder
set_option backward.isDefEq.respectTransparency false
/-- On a finite ambient type, the local total-variation distance may be summed
over all points rather than over the union of the stored supports. -/
theorem totalVariationDistance_eq_univ_sum {α : Type*} [Fintype α] [DecidableEq α]
    (μ ν : Distribution α) :
    totalVariationDistance μ ν =
      (1 / 2) * ∑ a : α, |μ.weight a - ν.weight a| := by
  unfold totalVariationDistance
  congr 1
  exact Finset.sum_subset (Finset.subset_univ (μ.support ∪ ν.support)) (fun a _ ha => by
    have hμ : a ∉ μ.support := fun h => ha (Finset.mem_union_left ν.support h)
    have hν : a ∉ ν.support := fun h => ha (Finset.mem_union_right μ.support h)
    rw [μ.outsideSupport a hμ, ν.outsideSupport a hν, sub_self, abs_zero])
end
end MIPStarRE.LDT

namespace MIPStarRE.LDT
section
open scoped BigOperators MatrixOrder Matrix ComplexOrder
set_option backward.isDefEq.respectTransparency false
/-- For probability distributions on a finite ambient type, the local
total-variation distance is the half `L^1` distance between the associated
Mathlib probability mass functions. -/
theorem totalVariationDistance_eq_toPMF_sum {α : Type*} [Fintype α] [DecidableEq α]
    (μ ν : Distribution α) (hμ : μ.IsProbability) (hν : ν.IsProbability) :
    totalVariationDistance μ ν =
      (1 / 2) * ∑ a : α, |(μ.toPMF hμ a).toReal - (ν.toPMF hν a).toReal| := by
  rw [totalVariationDistance_eq_univ_sum]
  congr 1
  refine Finset.sum_congr rfl ?_
  intro a _
  rw [Distribution.toPMF_apply_toReal, Distribution.toPMF_apply_toReal]
end
end MIPStarRE.LDT

namespace MIPStarRE.LDT.Pasting
section
open MIPStarRE.LDT
open scoped BigOperators MatrixOrder Matrix ComplexOrder
set_option backward.isDefEq.respectTransparency false
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
/-- The number of injective `k`-tuples is the falling factorial `q(q-1) ... (q-k+1)`. -/
theorem distinctTupleSupport_card (params : Parameters) (k : ℕ) :
    (distinctTupleSupport params k).card = params.q.descFactorial k := by
  classical
  rw [← Fintype.card_coe]
  let e : { xs : PointTuple params k // Function.Injective xs } ≃ (Fin k ↪ Fq params) :=
    Equiv.subtypeInjectiveEquivEmbedding (Fin k) (Fq params)
  simpa [distinctTupleSupport, Finset.mem_filter] using
    (Fintype.card_congr e).trans Fintype.card_embedding_eq
end
end MIPStarRE.LDT.Pasting

namespace MIPStarRE.LDT.Pasting
section
open MIPStarRE.LDT
open scoped BigOperators MatrixOrder Matrix ComplexOrder
set_option backward.isDefEq.respectTransparency false
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
/-- If `k ≤ q`, there exists an injective `k`-tuple. -/
theorem distinctTupleSupport_nonempty_of_le
    (params : Parameters) (k : ℕ) (hk : k ≤ params.q) :
    (distinctTupleSupport params k).Nonempty := by
  classical
  refine ⟨fun i => ⟨i.1, Nat.lt_of_lt_of_le i.2 hk⟩, ?_⟩
  refine Finset.mem_filter.mpr ?_
  constructor
  · simp
  · intro i j hij
    exact Fin.ext (by simpa using congrArg Fin.val hij)
end
end MIPStarRE.LDT.Pasting

namespace MIPStarRE.LDT.Pasting
section
open MIPStarRE.LDT
open scoped BigOperators MatrixOrder Matrix ComplexOrder
set_option backward.isDefEq.respectTransparency false
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
/-- If `q < k`, no injective `k`-tuple of field elements exists. -/
theorem distinctTupleSupport_eq_empty_of_lt
    (params : Parameters) (k : ℕ) (hk : params.q < k) :
    distinctTupleSupport params k = ∅ := by
  apply Finset.card_eq_zero.mp
  rw [distinctTupleSupport_card]
  exact Nat.descFactorial_eq_zero_iff_lt.mpr hk
end
end MIPStarRE.LDT.Pasting

namespace MIPStarRE.LDT
section
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
/-- Total variation between the uniform distribution on a finite ambient type and
the uniform distribution on a nonempty finite subset.

This is the elementary finite identity
`TV(uniform α, uniform s) = 1 - |s| / |α|`.  The proof transports the project
`Distribution` statement to Mathlib's uniform probability mass functions. -/
theorem totalVariationDistance_uniformDistribution_uniformOnFinset_eq
    {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    (s : Finset α) (hs : s.Nonempty) :
    totalVariationDistance (uniformDistribution α) (Distribution.uniformOnFinset s) =
      1 - (s.card : Error) / (Fintype.card α : Error) := by
  rw [totalVariationDistance_eq_toPMF_sum]
  change PMF.totalVariationDistance
      ((uniformDistribution α).toPMF (uniformDistribution_isProbability α))
      ((Distribution.uniformOnFinset s).toPMF
        (Distribution.uniformOnFinset_isProbability s hs)) =
    1 - (s.card : Error) / (Fintype.card α : Error)
  rw [uniformDistribution_toPMF, Distribution.uniformOnFinset_toPMF]
  exact PMF.totalVariationDistance_uniformOfFintype_uniformOfFinset_eq s hs
end
end MIPStarRE.LDT

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPStarRE.LDT.Pasting
open MIPStarRE.LDT
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
theorem _root_.solution
    (params : Parameters) (k : ℕ) :
    totalVariationDistance (uniformDistribution (PointTuple params k))
        (distinctTupleDistribution params k)
      ≤ ((k : Error) ^ (2 : ℕ)) / (params.q : Error) := by
  classical
  let support : Finset (PointTuple params k) :=
    distinctTupleSupport params k
  have hsupport_card : support.card = params.q.descFactorial k := by
    simpa [support] using distinctTupleSupport_card params k
  have hq_ne : (params.q : Error) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt params.hq)
  by_cases hk : k ≤ params.q
  · have hsupport_nonempty : support.Nonempty := by
      simpa [support] using distinctTupleSupport_nonempty_of_le params k hk
    have htv_eq :
        totalVariationDistance (uniformDistribution (PointTuple params k))
            (distinctTupleDistribution params k)
          = 1 - (support.card : Error) / ((params.q : Error) ^ k) := by
      have htv :=
        totalVariationDistance_uniformDistribution_uniformOnFinset_eq
          (s := support) hsupport_nonempty
      simpa [distinctTupleDistribution, support, PointTuple, Fintype.card_fun,
        Fintype.card_fin] using htv
    have hratio_prod :
        (support.card : Error) / ((params.q : Error) ^ k)
          = ∏ i ∈ Finset.range k, (((params.q - i : ℕ) : Error) / params.q) := by
      rw [hsupport_card, Nat.descFactorial_eq_prod_range]
      rw [show ((∏ i ∈ Finset.range k, (params.q - i) : ℕ) : Error)
          = ∏ i ∈ Finset.range k, ((params.q - i : ℕ) : Error) by
            rw [Finset.prod_natCast]]
      simp_rw [div_eq_mul_inv]
      rw [Finset.prod_mul_distrib]
      simp
    have hfactor :
        ∀ i ∈ Finset.range k,
          (((params.q - i : ℕ) : Error) / params.q) = 1 - (i : Error) / params.q := by
      intro i hi
      have hi_le : i ≤ params.q := (Nat.le_of_lt (Finset.mem_range.mp hi)).trans hk
      rw [Nat.cast_sub hi_le]
      field_simp [hq_ne]
    have hfactor_nonneg :
        ∀ i ∈ Finset.range k, 0 ≤ 1 - (i : Error) / params.q := by
      intro i hi
      have hi_le : (i : Error) ≤ params.q := by
        exact_mod_cast (Nat.le_of_lt (Finset.mem_range.mp hi)).trans hk
      have hq_pos : 0 < (params.q : Error) := by positivity
      have hdiv_le_one : (i : Error) / params.q ≤ 1 := by
        have hfrac_le : (i : Error) / params.q ≤ (params.q : Error) / params.q := by
          exact div_le_div_of_nonneg_right hi_le (by positivity)
        have hqq : (params.q : Error) / params.q = 1 := by
          field_simp [hq_ne]
        rw [hqq] at hfrac_le
        exact hfrac_le
      nlinarith
    have hfactor_le_one :
        ∀ i ∈ Finset.range k, 1 - (i : Error) / params.q ≤ 1 := by
      intro i hi
      exact sub_le_self _ (by positivity)
    have hprefix_le_one :
        ∀ i ∈ Finset.range k,
          ∏ j ∈ Finset.range k with j < i, (1 - (j : Error) / params.q) ≤ 1 := by
      intro i hi
      calc
        ∏ j ∈ Finset.range k with j < i, (1 - (j : Error) / params.q)
          ≤ ∏ j ∈ Finset.range k with j < i, (1 : Error) := by
              exact Finset.prod_le_prod
                (fun j hj => hfactor_nonneg j (Finset.mem_filter.mp hj).1)
                (fun j hj => hfactor_le_one j (Finset.mem_filter.mp hj).1)
        _ = 1 := by simp
    have hsum_le :
        ∑ i ∈ Finset.range k,
          ((i : Error) / params.q)
            * ∏ j ∈ Finset.range k with j < i, (1 - (j : Error) / params.q)
          ≤ ∑ i ∈ Finset.range k, (i : Error) / params.q := by
      refine Finset.sum_le_sum ?_
      intro i hi
      have hi_nonneg : 0 ≤ (i : Error) / params.q := by positivity
      have hprefix_nonneg :
          0 ≤ ∏ j ∈ Finset.range k with j < i, (1 - (j : Error) / params.q) := by
        exact Finset.prod_nonneg fun j hj => hfactor_nonneg j (Finset.mem_filter.mp hj).1
      calc
        ((i : Error) / params.q)
            * ∏ j ∈ Finset.range k with j < i, (1 - (j : Error) / params.q)
          ≤ ((i : Error) / params.q) * 1 := by
              exact mul_le_mul_of_nonneg_left (hprefix_le_one i hi) hi_nonneg
        _ = (i : Error) / params.q := by ring
    have hcollision_le :
        1 - ∏ i ∈ Finset.range k, (1 - (i : Error) / params.q)
          ≤ ∑ i ∈ Finset.range k, (i : Error) / params.q := by
      have hprod_expand :=
        (Finset.prod_one_sub_ordered (s := Finset.range k)
          (f := fun i => (i : Error) / params.q))
      rw [hprod_expand]
      nlinarith
    have hsum_id :
        ∑ i ∈ Finset.range k, (i : Error) / params.q
          = (((k * (k - 1) / 2 : ℕ) : Error) / params.q) := by
      calc
        ∑ i ∈ Finset.range k, (i : Error) / params.q
          = (∑ i ∈ Finset.range k, (i : Error)) / params.q := by
              simp [div_eq_mul_inv, Finset.sum_mul]
        _ = (((k * (k - 1) / 2 : ℕ) : Error) / params.q) := by
              rw [← Nat.cast_sum]
              simp [Finset.sum_range_id]
    have hsum_sq :
        (((k * (k - 1) / 2 : ℕ) : Error) / params.q)
          ≤ ((k : Error) ^ (2 : ℕ)) / params.q := by
      have hnat : k * (k - 1) / 2 ≤ k * k := by
        refine le_trans (Nat.div_le_self _ _) ?_
        exact Nat.mul_le_mul_left k (Nat.sub_le _ _)
      have hcast : (((k * (k - 1) / 2 : ℕ) : Error)) ≤ (k : Error) * k := by
        exact_mod_cast hnat
      simpa [pow_two] using div_le_div_of_nonneg_right hcast (by positivity)
    rw [htv_eq]
    rw [hratio_prod]
    rw [Finset.prod_congr rfl hfactor]
    exact le_trans hcollision_le (by simpa [hsum_id] using hsum_sq)
  · have hkq : params.q < k := lt_of_not_ge hk
    have hsupport_empty : support = ∅ := by
      simpa [support] using distinctTupleSupport_eq_empty_of_lt params k hkq
    have htv_eq_half :
        totalVariationDistance (uniformDistribution (PointTuple params k))
            (distinctTupleDistribution params k)
          = 1 / 2 := by
      rw [totalVariationDistance]
      simp [uniformDistribution, distinctTupleDistribution, support, hsupport_empty]
    have hbound_ge_one : 1 ≤ ((k : Error) ^ (2 : ℕ)) / (params.q : Error) := by
      have hk_pos_nat : 0 < k := lt_trans params.hq hkq
      have hk_ge_q : (params.q : Error) ≤ k := by exact_mod_cast hkq.le
      have hk_sq_ge_q : (params.q : Error) ≤ (k : Error) ^ (2 : ℕ) := by
        have hk_sq_ge_k : (k : Error) ≤ (k : Error) ^ (2 : ℕ) := by
          have hk_one : (1 : Error) ≤ k := by exact_mod_cast hk_pos_nat
          nlinarith
        exact le_trans hk_ge_q hk_sq_ge_k
      calc
        1 = (params.q : Error) / params.q := by
              field_simp [hq_ne]
        _ ≤ ((k : Error) ^ (2 : ℕ)) / params.q := by
              exact div_le_div_of_nonneg_right hk_sq_ge_q (by positivity)
    rw [htv_eq_half]
    nlinarith [hbound_ge_one]
end MIPStarRE.LDT.Pasting
