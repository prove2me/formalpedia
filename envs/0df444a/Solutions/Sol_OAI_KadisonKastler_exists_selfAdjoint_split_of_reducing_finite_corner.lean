-- Prove2me | solution 1 for OAI.KadisonKastler.exists_selfAdjoint_split_of_reducing_finite_corner
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T08:51:52.715687+00:00
-- url     : https://prove2.me/submissions/e38b45fa-f2fe-421f-af93-26a19354c5a2

import Mathlib
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.Algebra.Group.Submonoid.Membership
import Mathlib.Algebra.GroupWithZero.Units.Fintype
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Algebra.Module.Torsion.Field
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Algebra.Star.StarAlgHom
import Mathlib.Algebra.Star.StarProjection
import Mathlib.Algebra.Star.Subalgebra
import Mathlib.Algebra.Star.UnitaryStarAlgAut
import Mathlib.Analysis.CStarAlgebra.ApproximateUnit
import Mathlib.Analysis.CStarAlgebra.Basic
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.CompletelyPositiveMap
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Isometric
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.CStarAlgebra.PositiveLinearMap
import Mathlib.Analysis.CStarAlgebra.Spectrum
import Mathlib.Analysis.CStarAlgebra.Unitary.Span
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Spectrum
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Fourier.FiniteAbelian.Orthogonality
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Completion
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.InnerProductSpace.WeakOperatorTopology
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.LocallyConvex.SeparatingDual
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.LocallyConvex.WeakDual
import Mathlib.Analysis.LocallyConvex.WeakSpace
import Mathlib.Analysis.Normed.Algebra.Basic
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Group.Quotient
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Module.Dual
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Analysis.Normed.Module.RCLike.Extend
import Mathlib.Analysis.Normed.Module.RieszLemma
import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Operator.Completeness
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Abs
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.PosPart.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.VonNeumannAlgebra.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.List.ChainOfFn
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Permutation
import Mathlib.Data.List.Sublists
import Mathlib.Data.Matrix.Basis
import Mathlib.Data.Matrix.Composition
import Mathlib.Data.Multiset.AddSub
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Data.Sym.Card
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Logic.Equiv.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Logic.Equiv.Set
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Inner
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lemmas
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.Order.Filter.AtTopBot.Prod
import Mathlib.Order.Filter.Ultrafilter.Basic
import Mathlib.Order.Zorn
import Mathlib.RingTheory.Congruence.Basic
import Mathlib.RingTheory.Congruence.Hom
import Mathlib.RingTheory.TwoSidedIdeal.Basic
import Mathlib.RingTheory.TwoSidedIdeal.Lattice
import Mathlib.Tactic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.DeriveCountable
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Module
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Algebra
import Mathlib.Topology.Algebra.Group.Pointwise
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Algebra.Module.Star
import Mathlib.Topology.Algebra.Star.Unitary
import Mathlib.Topology.Algebra.StarSubalgebra
import Mathlib.Topology.Bases
import Mathlib.Topology.ContinuousMap.Bounded.Star
import Mathlib.Topology.DenseEmbedding
import Mathlib.Topology.Instances.Complex
import Mathlib.Topology.Instances.Rat
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.Topology.MetricSpace.Polish
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.Metrizable.Basic
import Mathlib.Topology.Order
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.IsLUB
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.Sequences
import Mathlib.Topology.UniformSpace.UniformApproximation
import Definitions.Def_Q260K037
import Theorems.Thm_OAI_KadisonKastler_exists_selfAdjoint_split_of_II1_commutant
import Theorems.Thm_OAI_KadisonKastler_exists_selfAdjoint_split_of_finite_typeI_commutant
import Theorems.Thm_OAI_KadisonKastler_lift_reducing_spatial_split

section
-- module Solutions.OAIQ075_KS.KadisonKastler_CenterAlgebra
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexDecidableEq _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexFintype _root_.OAI.KadisonKastler.typeIIIInitialSpaceComplete _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Recovering scalar centre from central projections

The centre is represented as the intersection with the concrete commutant.
Spectral approximation in this von Neumann algebra reduces scalarity of its
whole algebra to triviality of its projections.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Spectral approximation upgrades trivial central projections to scalar
centre. No finiteness or trace is needed for this upgrade. -/
theorem scalar_center_of_trivial_central_projections (N : VonNeumannAlgebra H)
    (hproj : ∀ q : Algebra N, IsStarProjection q →
      (∀ a : Algebra N, a * q = q * a) → q = 0 ∨ q = 1)
    (c : Algebra N) (hc : ∀ a : Algebra N, a * c = c * a) :
    ∃ z : ℂ, c = z • (1 : Algebra N) := by
  let C := concreteCenter N
  let inc : Algebra C →⋆ₐ[ℂ] Algebra N := StarSubalgebra.inclusion (show
      C.toStarSubalgebra ≤ N.toStarSubalgebra from fun _ hx => hx.1)
  have hinj : Function.Injective inc := StarSubalgebra.inclusion_injective _
  let cC : Algebra C := ⟨c.val, c.property, by
    apply VonNeumannAlgebra.mem_commutant_iff.mpr
    intro a ha
    exact congrArg Subtype.val (hc ⟨a, ha⟩)⟩
  let p : Generator.Tracial.AlgebraProjection C := ⟨1, IsStarProjection.one _⟩
  have hmin : ∀ q : Generator.Tracial.AlgebraProjection C, q ≤ p → q.val = 0 ∨ q.val = p.val := by
    intro q _
    have hq : IsStarProjection (inc q.val) := q.property.map inc
    have hqc : ∀ a : Algebra N, a * inc q.val = inc q.val * a := by
      intro a
      apply Subtype.ext
      exact VonNeumannAlgebra.mem_commutant_iff.mp q.val.property.2 a.val a.property
    rcases hproj (inc q.val) hq hqc with h | h
    · left
      apply hinj
      change inc q.val = inc 0
      rw [map_zero]
      exact h
    · right
      apply hinj
      change inc q.val = inc 1
      rw [map_one]
      exact h
  obtain ⟨z, hz⟩ := Generator.Tracial.corner_scalar_of_projections p hmin cC
    (by change 1 * cC = cC; exact one_mul _) (by change cC * 1 = cC; exact mul_one _)
  refine ⟨z, ?_⟩
  have he := congrArg (fun x : Algebra C => (x : H →L[ℂ] H)) hz
  exact Subtype.ext he

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_RepresentedCorner
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Concrete compression to a common closed subspace

The corner acts on the subspace itself. Its operators are characterized by
membership of their extension by zero in the original von Neumann algebra.
This constructs the actual corner and proves that a common compression does
not increase Kadison--Kastler distance.
-/

namespace KadisonKastler

open scoped Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  (E : Submodule ℂ H) [CompleteSpace E]

variable [CompleteSpace H]

theorem cornerCompression_mem {M : VonNeumannAlgebra H} (hp : E.starProjection ∈ M)
    {T : H →L[ℂ] H} (hT : T ∈ M) :
    cornerCompression E T ∈ representedCorner E M hp := by
  rw [mem_representedCorner, cornerExtension_compression]
  exact M.mul_mem (M.mul_mem hp hT) hp

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_CornerFactorStructure
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Factor and finite-isometry structure of represented corners

Countable full matrix units identify the original algebra with the actual
amplification of its first corner. A central corner operator therefore
inflates to a central ambient operator. Finiteness of the first projection
also passes directly to the represented corner by extension by zero.
No trace or semifinite decomposition is assumed in these arguments.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {E : Submodule ℂ H} [CompleteSpace E]

omit [CompleteSpace H] in
/-- Extension by zero is faithful, even when the original representation is
not the standard tracial representation. -/
theorem cornerExtension_injective : Function.Injective (cornerExtension E) := by
  intro T S h
  have he := congrArg (cornerCompression E) h
  simpa only [cornerCompression_extension] using he

/-- A finite ambient projection makes the represented corner a finite algebra. -/
theorem finite_representedCorner_of_finite_projection (M : VonNeumannAlgebra H)
    (hE : E.starProjection ∈ M)
    (hfinite : FiniteProjectionIn M ⟨E.starProjection, hE⟩) :
    ∀ v : Algebra (representedCorner E M hE),
      star v * v = 1 → v * star v = 1 := by
  intro v hv
  let w : Algebra M := ⟨cornerExtension E (v : E →L[ℂ] E), v.property⟩
  have hv' : star (v : E →L[ℂ] E) * (v : E →L[ℂ] E) = 1 :=
    congrArg Subtype.val hv
  have hi : star w * w = (⟨E.starProjection, hE⟩ : Algebra M) := by
    apply Subtype.ext
    change star (cornerExtension E (v : E →L[ℂ] E)) *
      cornerExtension E (v : E →L[ℂ] E) = E.starProjection
    rw [← cornerExtension_star, ← cornerExtension_mul, hv', cornerExtension_one]
  have hs : (⟨E.starProjection, hE⟩ : Algebra M) * w = w := by
    apply Subtype.ext
    exact starProjection_mul_cornerExtension E (v : E →L[ℂ] E)
  have ho := congrArg Subtype.val (hfinite w hi hs)
  apply Subtype.ext
  apply cornerExtension_injective
  change cornerExtension E ((v : E →L[ℂ] E) * star (v : E →L[ℂ] E)) =
    cornerExtension E (1 : E →L[ℂ] E)
  rw [cornerExtension_mul, cornerExtension_star, cornerExtension_one]
  exact ho

omit [CompleteSpace H] in
/-- A nonzero corner projection gives a nonzero represented identity. -/
theorem representedCorner_nonzero_of_projection_ne_zero
    (hE : E.starProjection ≠ (0 : H →L[ℂ] H)) : (0 : E →L[ℂ] E) ≠ 1 := by
  intro h
  have he := congrArg (cornerExtension E) h
  exact hE (by simpa only [map_zero, cornerExtension_one] using he.symm)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_FactorCornerCentralProjection
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.partialSupportSpace_complete _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexDecidableEq _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # A central projection in a nonzero factor corner is trivial -/

namespace KadisonKastler

open Generator.Tracial

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

theorem factor_corner_central_projection (hM : ScalarCenter M)
    (p q : AlgebraProjection M) (hqp : q ≤ p)
    (hc : ∀ a : Algebra M, q.val * (p.val * a * p.val) =
      (p.val * a * p.val) * q.val) : q.val = 0 ∨ q = p := by
  classical
  by_cases hq : q.val = 0
  · exact Or.inl hq
  right
  by_contra hne
  let r := AlgebraProjection.remainder q p hqp
  have hr : r.val ≠ 0 := by
    intro h
    apply hne
    apply Subtype.ext
    exact (sub_eq_zero.mp h).symm
  have hf : ∀ c : Algebra M, (∀ a : Algebra M, a * c = c * a) →
      ∃ z : ℂ, c = z • (1 : Algebra M) := by
    intro c h
    obtain ⟨z, hz⟩ := hM c.val c.property
      (fun a ha => congrArg Subtype.val (h ⟨a, ha⟩))
    exact ⟨z, Subtype.ext hz⟩
  obtain ⟨v, hvs, hvt, hv0⟩ :=
    traceFree_exists_nonzero_partialIsometry_between_projections hf q r hq hr
  have hvq : v.val * q.val = v.val := (v.support_le_iff_mul q).mp hvs
  have hrv : r.val * v.val = v.val := (v.target_le_iff_mul r).mp hvt
  have hpr : p.val * r.val = r.val := AlgebraProjection.remainder_le q p hqp
  have hqp' : q.val * p.val = q.val := projection_mul_of_le hqp
  have hpv : p.val * v.val = v.val := by
    calc
      _ = p.val * (r.val * v.val) := by rw [hrv]
      _ = v.val := by rw [← mul_assoc, hpr, hrv]
  have hvp : v.val * p.val = v.val := by
    calc
      _ = (v.val * q.val) * p.val := by rw [hvq]
      _ = v.val := by rw [mul_assoc, hqp', hvq]
  have hqr : q.val * r.val = 0 := by
    change q.val * (p.val - q.val) = 0
    rw [mul_sub, hqp', q.property.isIdempotentElem.eq, sub_self]
  have hqv : q.val * v.val = 0 := by
    calc
      _ = q.val * (r.val * v.val) := by rw [hrv]
      _ = 0 := by rw [← mul_assoc, hqr, zero_mul]
  have hh := hc v.val
  rw [hpv, hvp, hqv, hvq] at hh
  apply hv0
  rw [← v.initial, ← hh, star_zero, zero_mul]

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_TypeIFactorStability
attribute [-instance] _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.matrixSiteBlockIndexDecidableEq _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexDecidableEq _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexFintype _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.typeIIIInitialSpaceComplete _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The type I branch and the projection dichotomy

The diffuse predicate is exactly the projection clause of
`Generator.IsII1Factor` and `TypeIIInfinityFactor`. Its alternative, for
a scalar-center algebra, is the existence of a minimal projection. This
dichotomy is proved directly. The separable type I branch uses the constructed
finite-group embedding.
-/

namespace KadisonKastler

open Generator.Tracial

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- A factor either has a minimal projection or every nonzero projection
has a proper nonzero subprojection. No spectral or classification input
is used in this alternative. -/
theorem isTypeIFactor_or_projectionDiffuse {M : VonNeumannAlgebra H}
    (hM : ScalarCenter M) : IsTypeIFactor M ∨ ProjectionDiffuse M := by
  classical
  by_cases htype : IsTypeIFactor M
  · exact Or.inl htype
  right
  intro p hp hp0
  by_contra hnone
  apply htype
  refine ⟨hM, ⟨⟨p, hp⟩, hp0, ?_⟩⟩
  intro q hqp
  by_cases hq0 : q.val = 0
  · exact Or.inl hq0
  right
  apply Subtype.ext
  by_contra hne
  apply hnone
  exact ⟨q.val, q.property, hq0, hne, hqp, projection_mul_of_le hqp⟩

/-- A nonzero finite factor without minimal projections is a II₁ factor.
Finiteness is only assumed for its identity
projection; the required isometry condition follows directly. -/
theorem isII1Factor_of_finite_of_not_typeI {M : VonNeumannAlgebra H}
    (hM : ScalarCenter M) (hnonzero : (0 : H →L[ℂ] H) ≠ 1)
    (hfinite : FiniteProjectionIn M 1) (htype : ¬ IsTypeIFactor M) :
    Generator.IsII1Factor M.toStarSubalgebra := by
  refine {
    nonzero := hnonzero
    weaklyClosed := Generator.Tracial.vonNeumann_wotClosed M
    factor := ?_
    finite := fun v hv => hfinite v hv (one_mul v)
    diffuse := (isTypeIFactor_or_projectionDiffuse hM).resolve_left htype }
  intro x hx
  obtain ⟨z, hz⟩ := hM x.val x.property (fun y hy =>
    congrArg Subtype.val (hx ⟨y, hy⟩))
  refine ⟨z, ?_⟩
  rw [Algebra.algebraMap_eq_smul_one]
  apply Subtype.ext
  exact hz

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_FiniteCommutantSpatialSplit
attribute [-instance] _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerOne _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.normUltraproductNontrivial _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.spatialHilbert_nontrivial _root_.OAI.KadisonKastler.tracialSequenceQuotientNontrivial _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.PopaCorner.instOne _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Spatial splitting for a finite factor commutant in every representation -/

namespace KadisonKastler

noncomputable section

open Generator

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [Nontrivial H]

theorem exists_selfAdjoint_split_of_finite_factor_commutant
    (M : VonNeumannAlgebra H) (hN : ScalarCenter M.commutant)
    (hfinite : FiniteProjectionIn M.commutant 1)
    (T : H →L[ℂ] H) (hTsa : IsSelfAdjoint T)
    (hT : ∀ a ∈ M, T * a - a * T ∈ M) :
    ∃ a : H →L[ℂ] H, a ∈ M ∧ IsSelfAdjoint a ∧ ‖a‖ ≤ ‖T‖ ∧
      T - a ∈ M.commutant := by
  by_cases ht : IsTypeIFactor M.commutant
  · exact exists_selfAdjoint_split_of_finite_typeI_commutant M ht hfinite T hTsa hT
  · exact exists_selfAdjoint_split_of_II1_commutant M
      (isII1Factor_of_finite_of_not_typeI hN zero_ne_one hfinite ht) T hTsa hT

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_GeneralCornerFactor
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexDecidableEq _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Scalar center for arbitrary represented factor corners -/

namespace KadisonKastler

noncomputable section

open Generator.Tracial

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (E : Submodule ℂ H) [CompleteSpace E]

theorem scalarCenter_representedCorner_general (N : VonNeumannAlgebra H)
    (hE : E.starProjection ∈ N) (hN : ScalarCenter N) :
    ScalarCenter (representedCorner E N hE) := by
  let Q := representedCorner E N hE
  let hp := isStarProjection_starProjection (U := E)
  let p : AlgebraProjection N := ⟨⟨E.starProjection, hE⟩,
    ⟨Subtype.ext hp.isIdempotentElem.eq, Subtype.ext hp.isSelfAdjoint.star_eq⟩⟩
  have hproj : ∀ q : Algebra Q, IsStarProjection q →
      (∀ a : Algebra Q, a * q = q * a) → q = 0 ∨ q = 1 := by
    intro q hq hc
    let q0 : Algebra N := ⟨cornerExtension E q.val, q.property⟩
    have hq0 : IsStarProjection q0 := by
      constructor
      · apply Subtype.ext
        change cornerExtension E q.val * cornerExtension E q.val = cornerExtension E q.val
        rw [← cornerExtension_mul]
        exact congrArg (cornerExtension E) (congrArg Subtype.val hq.isIdempotentElem.eq)
      · apply Subtype.ext
        change star (cornerExtension E q.val) = cornerExtension E q.val
        rw [← cornerExtension_star]
        exact congrArg (cornerExtension E) (congrArg Subtype.val hq.isSelfAdjoint.star_eq)
    let qP : AlgebraProjection N := ⟨q0, hq0⟩
    have hqp : qP ≤ p := by
      apply Subtype.ext
      exact starProjection_mul_cornerExtension E q.val
    have hc0 : ∀ a : Algebra N, qP.val * (p.val * a * p.val) =
        (p.val * a * p.val) * qP.val := by
      intro a
      let b : Algebra Q := ⟨cornerCompression E a.val, cornerCompression_mem E hE a.property⟩
      have hh := congrArg (fun x : Algebra Q => cornerExtension E x.val) (hc b)
      change cornerExtension E ((cornerCompression E a.val) * q.val) =
        cornerExtension E (q.val * cornerCompression E a.val) at hh
      rw [cornerExtension_mul, cornerExtension_mul, cornerExtension_compression] at hh
      exact Subtype.ext hh.symm
    rcases factor_corner_central_projection hN p qP hqp hc0 with hz | he
    · left
      apply Subtype.ext
      apply cornerExtension_injective
      exact congrArg Subtype.val hz
    · right
      apply Subtype.ext
      apply cornerExtension_injective
      change cornerExtension E q.val = cornerExtension E 1
      rw [cornerExtension_one]
      exact congrArg (fun a : AlgebraProjection N => a.val.val) he
  intro T hT hc
  obtain ⟨z, hz⟩ := scalar_center_of_trivial_central_projections Q hproj ⟨T, hT⟩
    (fun a => Subtype.ext (hc a.val a.property))
  exact ⟨z, congrArg Subtype.val hz⟩

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ReducingCommutantCorner
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instRing _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The commutant on a reducing subspace is the represented corner -/

namespace KadisonKastler

noncomputable section

open Generator Generator.Tracial

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (E : Submodule ℂ H) [CompleteSpace E]

omit [CompleteSpace H] in
theorem cornerExtension_mul_reducing (S : E →L[ℂ] E) (T : H →L[ℂ] H)
    (hT : E.starProjection * T = T * E.starProjection) :
    cornerExtension E (S * cornerCompression E T) = cornerExtension E S * T := by
  rw [cornerExtension_mul, cornerExtension_compression]
  calc
    cornerExtension E S * (E.starProjection * T * E.starProjection) =
        cornerExtension E S * T * E.starProjection := by
      rw [← mul_assoc, ← mul_assoc, cornerExtension_mul_starProjection]
    _ = cornerExtension E S * (E.starProjection * T) := by rw [mul_assoc, hT]
    _ = cornerExtension E S * T := by rw [← mul_assoc, cornerExtension_mul_starProjection]

omit [CompleteSpace H] in
theorem reducing_mul_cornerExtension (T : H →L[ℂ] H) (S : E →L[ℂ] E)
    (hT : E.starProjection * T = T * E.starProjection) :
    cornerExtension E (cornerCompression E T * S) = T * cornerExtension E S := by
  rw [cornerExtension_mul, cornerExtension_compression]
  calc
    E.starProjection * T * E.starProjection * cornerExtension E S =
        E.starProjection * T * cornerExtension E S := by
      rw [mul_assoc (E.starProjection * T), starProjection_mul_cornerExtension]
    _ = T * E.starProjection * cornerExtension E S := by rw [hT]
    _ = T * cornerExtension E S := by rw [mul_assoc, starProjection_mul_cornerExtension]

omit [CompleteSpace H] in
theorem commutes_corner_iff (T : H →L[ℂ] H) (S : E →L[ℂ] E)
    (hT : E.starProjection * T = T * E.starProjection) :
    Commute (cornerCompression E T) S ↔ Commute T (cornerExtension E S) := by
  constructor
  · intro h
    have hh := congrArg (cornerExtension E) h.eq
    rw [reducing_mul_cornerExtension E T S hT, cornerExtension_mul_reducing E S T hT] at hh
    exact hh
  · intro h
    apply cornerExtension_injective
    rw [reducing_mul_cornerExtension E T S hT, cornerExtension_mul_reducing E S T hT]
    exact h.eq

/-- The full commutant of the restricted algebra is exactly the corner
of the original commutant, with extension by zero identifying operators. -/
theorem commutant_reducingClosure (M : VonNeumannAlgebra H)
    (hE : E.starProjection ∈ M.commutant) :
    (generatedVonNeumannAlgebra (commutantReducingHom E M hE).range).commutant =
      representedCorner E M.commutant hE := by
  apply VonNeumannAlgebra.ext
  intro S
  rw [mem_representedCorner]
  constructor
  · intro hS
    apply VonNeumannAlgebra.mem_commutant_iff.mpr
    intro a ha
    have hc := VonNeumannAlgebra.mem_commutant_iff.mp hS
      (commutantReducingHom E M hE ⟨a, ha⟩)
      (subset_generatedVonNeumannAlgebra _ ⟨⟨a, ha⟩, rfl⟩)
    exact (commutes_corner_iff E a S
      (VonNeumannAlgebra.mem_commutant_iff.mp hE a ha).symm).mp hc
  · intro hS
    have hs : S ∈ Set.centralizer
        (Set.range (fun b : Algebra M => commutantReducingHom E M hE b)) := by
      rintro a ⟨b, rfl⟩
      exact ((commutes_corner_iff E b.val S
        (VonNeumannAlgebra.mem_commutant_iff.mp hE b.val b.property).symm).mpr
          (VonNeumannAlgebra.mem_commutant_iff.mp hS b.val b.property)).eq
    apply VonNeumannAlgebra.mem_commutant_iff.mpr
    intro a ha
    change a ∈ (generatedVonNeumannAlgebra
      (commutantReducingHom E M hE).range : Set (E →L[ℂ] E)) at ha
    rw [generatedVonNeumannAlgebra_coe] at ha
    exact (ha S hs).symm

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ReducingSpatialLift
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instRing _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Lifting a spatial split through a faithful reducing restriction -/

namespace KadisonKastler

noncomputable section

open Generator

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (E : Submodule ℂ H) [CompleteSpace E]
  (M : VonNeumannAlgebra H) (hE : E.starProjection ∈ M.commutant)
  (R : VonNeumannAlgebra E) (e : Algebra M ≃⋆ₐ[ℂ] Algebra R)
  (he : ∀ a : Algebra M, (e a).val = cornerCompression E a.val)

include hE he

theorem reducing_commutator_identity
    (T : H →L[ℂ] H) (hTE : E.starProjection * T = T * E.starProjection)
    (a : Algebra M) :
    cornerCompression E (T * a.val - a.val * T) =
      cornerCompression E T * (e a).val - (e a).val * cornerCompression E T := by
  rw [map_sub, cornerCompression_mul_of_invariant E T a.val
      (invariant_of_commutes_starProjection E a.val
        (VonNeumannAlgebra.mem_commutant_iff.mp hE a.val a.property).symm),
    cornerCompression_mul_of_invariant E a.val T
      (invariant_of_commutes_starProjection E T hTE), he]

theorem reducing_spatial_preserves
    (T : H →L[ℂ] H) (hTE : E.starProjection * T = T * E.starProjection)
    (hT : ∀ a ∈ M, T * a - a * T ∈ M) :
    ∀ b ∈ R, cornerCompression E T * b - b * cornerCompression E T ∈ R := by
  intro b hb
  obtain ⟨a, ha⟩ := e.surjective ⟨b, hb⟩
  have hv : (e a).val = b := congrArg Subtype.val ha
  rw [← hv, ← reducing_commutator_identity E M hE R e he T hTE a]
  rw [← he ⟨T * a.val - a.val * T, hT a.val a.property⟩]
  exact (e ⟨T * a.val - a.val * T, hT a.val a.property⟩).property

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_FiniteCornerSpatialSplit
attribute [-instance] _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Spatial splitting from one nonzero finite commutant corner -/

namespace KadisonKastler

noncomputable section

open Generator Generator.Tracial

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (E : Submodule ℂ H) [CompleteSpace E]

theorem exists_selfAdjoint_split_of_reducing_finite_corner_oai
    (M : VonNeumannAlgebra H) (hN : ScalarCenter M.commutant)
    (hE : E.starProjection ∈ M.commutant) (hE0 : E.starProjection ≠ 0)
    (hfinite : FiniteProjectionIn M.commutant ⟨E.starProjection, hE⟩)
    (T : H →L[ℂ] H) (hTsa : IsSelfAdjoint T)
    (hT : ∀ a ∈ M, T * a - a * T ∈ M)
    (hTE : E.starProjection * T = T * E.starProjection) :
    ∃ a : H →L[ℂ] H, a ∈ M ∧ IsSelfAdjoint a ∧ ‖a‖ ≤ ‖T‖ ∧
      T - a ∈ M.commutant := by
  let φ := commutantReducingHom E M hE
  let R := generatedVonNeumannAlgebra φ.range
  have hi : Function.Injective φ := commutantReducingHom_injective E M hE hE0 hN
  let e : Algebra M ≃⋆ₐ[ℂ] Algebra R := boundedWeakNormalEquiv M φ hi
    (commutantReducingHom_boundedWeakNormal E M hE)
  have he (a : Algebra M) : (e a).val = cornerCompression E a.val := rfl
  have hRT := reducing_spatial_preserves E M hE R e he T hTE hT
  have hR : ScalarCenter R.commutant := by
    rw [commutant_reducingClosure E M hE]
    exact scalarCenter_representedCorner_general E M.commutant hE hN
  have hRf : FiniteProjectionIn R.commutant 1 := by
    rw [commutant_reducingClosure E M hE]
    intro v hv _
    exact finite_representedCorner_of_finite_projection M.commutant hE hfinite v hv
  let : Nontrivial E := by
    have hn := representedCorner_nonzero_of_projection_ne_zero hE0
    by_contra h
    have : Subsingleton E := not_nontrivial_iff_subsingleton.mp h
    exact hn (Subsingleton.elim _ _)
  have hT0 : IsSelfAdjoint (cornerCompression E T) := by
    change star (cornerCompression E T) = cornerCompression E T
    rw [← cornerCompression_star, hTsa.star_eq]
  obtain ⟨c, hc, hcsa, hcn, hTc⟩ :=
    exists_selfAdjoint_split_of_finite_factor_commutant R hR hRf
      (cornerCompression E T) hT0 hRT
  obtain ⟨a, ha, hasa, han, hTa⟩ :=
    lift_reducing_spatial_split E M hE R e he T hTE hT c hc hcsa hTc
  exact ⟨a, ha, hasa, han.le.trans (hcn.trans (norm_cornerCompression_le E T)), hTa⟩

end

end KadisonKastler

end OAI
end

theorem solution.{u_1} : type_of% @OAI.KadisonKastler.exists_selfAdjoint_split_of_reducing_finite_corner_oai.{u_1} := @OAI.KadisonKastler.exists_selfAdjoint_split_of_reducing_finite_corner_oai.{u_1}
