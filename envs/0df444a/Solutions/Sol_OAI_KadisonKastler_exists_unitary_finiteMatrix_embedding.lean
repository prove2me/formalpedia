-- Prove2me | solution 1 for OAI.KadisonKastler.exists_unitary_finiteMatrix_embedding
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T07:51:48.993214+00:00
-- url     : https://prove2.me/submissions/169827b4-03ee-4482-99c7-d30e0df3e48c

import Mathlib
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Algebra.BigOperators.Expect
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
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Algebra.Star.StarAlgHom
import Mathlib.Algebra.Star.StarProjection
import Mathlib.Algebra.Star.Subalgebra
import Mathlib.Algebra.Star.UnitaryStarAlgAut
import Mathlib.Analysis.CStarAlgebra.Basic
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.CompletelyPositiveMap
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.CStarAlgebra.PositiveLinearMap
import Mathlib.Analysis.CStarAlgebra.Spectrum
import Mathlib.Analysis.CStarAlgebra.Unitary.Span
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Fourier.FiniteAbelian.Orthogonality
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
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Module.Dual
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Analysis.Normed.Module.RCLike.Extend
import Mathlib.Analysis.Normed.Module.RieszLemma
import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Abs
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.PosPart.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.VonNeumannAlgebra.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.EquivFin
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
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Logic.Equiv.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Inner
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lemmas
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Order.Filter.AtTopBot.Prod
import Mathlib.Order.Filter.Ultrafilter.Basic
import Mathlib.Order.Zorn
import Mathlib.RingTheory.Congruence.Basic
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
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Algebra.Star.Unitary
import Mathlib.Topology.Algebra.StarSubalgebra
import Mathlib.Topology.ContinuousMap.Bounded.Star
import Mathlib.Topology.DenseEmbedding
import Mathlib.Topology.Instances.Complex
import Mathlib.Topology.Instances.Rat
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.Order
import Mathlib.Topology.Order.IsLUB
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.Sequences
import Mathlib.Topology.UniformSpace.UniformApproximation
import Definitions.Def_StrongKadisonKastler
import Definitions.Def_Q260K068
import Theorems.Thm_OAI_KadisonKastler_exists_bounded_cocycle_of_equivariant_mean
import Theorems.Thm_OAI_KadisonKastler_exists_unitary_approx_of_nearInclusion
import Theorems.Thm_OAI_KadisonKastler_exists_unitary_boundary_intertwiner

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_SignedMatrixUnitaries
attribute [-instance] _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instFintypeSignedPermutation _root_.OAI.KadisonKastler.matrixSiteBlockIndexDecidableEq _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexDecidableEq _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexFintype _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.BoundedHochschild.KadisonRingrose.matrixSystemOfColumns_diagonal _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A finite group of signed permutation unitaries in a matrix system. -/

noncomputable section

open scoped BigOperators

namespace HochschildMatrixSystems
namespace MatrixSystem

variable {M : Type*} [CStarAlgebra M] {n : ℕ} (E : MatrixSystem M n)

lemma signedPermutation_flip (σ : Equiv.Perm (Fin n)) (j : Fin n) :
    E.signedPermutation σ (fun _ => false) -
      E.signedPermutation σ (fun k => decide (k = j)) = (2 : ℂ) • E.entry (σ j) j := by
  classical
  simp only [signedPermutation, ← Finset.sum_sub_distrib]
  rw [Finset.sum_eq_single j]
  · simp [signScalar, two_smul]
  · intro k _ hkj
    simp [signScalar, hkj]
  · simp

/-- Signed permutation unitaries linearly span every matrix entry. -/
lemma entry_mem_signedPermutation_span (i j : Fin n) :
    E.entry i j ∈ Submodule.span ℂ
      (Set.range (fun u : E.signedPermutationGroup => ((u : unitary M) : M))) := by
  classical
  let S := Submodule.span ℂ
    (Set.range (fun u : E.signedPermutationGroup => ((u : unitary M) : M)))
  have hmem (σ : Equiv.Perm (Fin n)) (s : Fin n → Bool) : E.signedPermutation σ s ∈ S :=
    Submodule.subset_span ⟨⟨E.signedPermutationUnitary σ s, ⟨(σ, s), rfl⟩⟩, rfl⟩
  have hh := S.sub_mem (hmem (Equiv.swap j i) (fun _ => false))
    (hmem (Equiv.swap j i) (fun k => decide (k = j)))
  rw [E.signedPermutation_flip, Equiv.swap_apply_left] at hh
  have h := S.smul_mem (2⁻¹ : ℂ) hh
  simpa only [smul_smul, inv_mul_cancel₀ (by norm_num : (2 : ℂ) ≠ 0), one_smul] using h

end MatrixSystem
end HochschildMatrixSystems

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_CocycleMetric
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedStarGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.normUltraproductNontrivial _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.spatialHilbert_nontrivial _root_.OAI.KadisonKastler.tracialSequenceQuotientNontrivial _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The complete metric space of uniformly bounded unitary families

The cocycle defect is continuous for the uniform norm. This supplies the
metric-space part of the boundary correction iteration.
-/

namespace KadisonKastler

open scoped BoundedContinuousFunction

noncomputable section

variable {G B : Type*} [Group G] [TopologicalSpace G] [DiscreteTopology G]
variable [CStarAlgebra B]

local instance instCompleteSpaceSubtypeBoundedContinuousFunctionMemSubmonoidUnitary_solutions_r4a7565_1 : CompleteSpace (unitary (G →ᵇ B)) := isClosed_unitary.completeSpace_coe
private theorem unitary_cocycle_error_difference_le
    (α : G →* (B ≃⋆ₐ[ℂ] B)) (V W : unitary (G →ᵇ B)) (g h : G) :
    ‖unitaryCocycleError α V (g, h) - unitaryCocycleError α W (g, h)‖ ≤
      3 * ‖V.val - W.val‖ := by
  let c := ‖V.val - W.val‖
  have he (g : G) : ‖V.val g - W.val g‖ ≤ c :=
    (V.val - W.val).norm_coe_le_norm g
  have hv : ‖α g (V.val h)‖ ≤ 1 :=
    norm_unitary_le_one (Unitary.map (StarMonoidHom.ofClass (α g)) (unitaryFamilyEval V h))
  have hw : ‖W.val g‖ ≤ 1 := norm_unitary_le_one (unitaryFamilyEval W g)
  have hα : ‖α g (V.val h - W.val h)‖ ≤ c := by
    have hi : ‖α g (V.val h - W.val h)‖ = ‖V.val h - W.val h‖ :=
      NonUnitalStarAlgHom.norm_map (α g).toStarAlgHom (α g).injective _
    rw [hi]
    exact he h
  change ‖(V.val g * α g (V.val h) - V.val (g * h)) -
    (W.val g * α g (W.val h) - W.val (g * h))‖ ≤ 3 * c
  have hid : (V.val g * α g (V.val h) - V.val (g * h)) -
      (W.val g * α g (W.val h) - W.val (g * h)) =
      (V.val g - W.val g) * α g (V.val h) +
        W.val g * α g (V.val h - W.val h) - (V.val (g * h) - W.val (g * h)) := by
    rw [map_sub]
    noncomm_ring
  rw [hid]
  calc
    _ ≤ ‖(V.val g - W.val g) * α g (V.val h)‖ +
        ‖W.val g * α g (V.val h - W.val h)‖ + ‖V.val (g * h) - W.val (g * h)‖ :=
      (norm_sub_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ c * 1 + 1 * c + c := by
      exact add_le_add (add_le_add
        ((norm_mul_le _ _).trans (mul_le_mul (he g) hv (norm_nonneg _) (norm_nonneg _)))
        ((norm_mul_le _ _).trans (mul_le_mul hw hα (norm_nonneg _) (by norm_num)))) (he _)
    _ = _ := by ring

theorem unitaryCocycleError_lipschitz (α : G →* (B ≃⋆ₐ[ℂ] B)) :
    LipschitzWith 3 (unitaryCocycleError α) := by
  apply LipschitzWith.of_dist_le_mul
  intro V W
  simp only [Subtype.dist_eq, dist_eq_norm]
  change ‖unitaryCocycleError α V - unitaryCocycleError α W‖ ≤
    (3 : ℝ) * ‖V.val - W.val‖
  apply (BoundedContinuousFunction.norm_le (by positivity)).mpr
  rintro ⟨g, h⟩
  exact unitary_cocycle_error_difference_le α V W g h

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_BoundaryBoundedTransport
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedStarGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Bounded transport fields and the correction step

For an action on a C-star algebra, the transport fields are actual bounded
unitary families.  An equivariant bimodule mean therefore gives the quadratic
step in the complete metric space of unitary families.
-/

namespace KadisonKastler

open scoped BoundedContinuousFunction CStarAlgebra

noncomputable section

variable {G B : Type*} [Group G] [TopologicalSpace G] [DiscreteTopology G]
variable [CStarAlgebra B]

local instance boundaryBoundedComplete_r4a7565_1 : CompleteSpace (unitary (G →ᵇ B)) :=
  isClosed_unitary.completeSpace_coe
attribute [local instance] OAI.KadisonKastler.boundaryBoundedStarOrder
/-- Each pointwise defect is bounded by its actual uniform norm. -/
theorem norm_unitaryCocycleError_le (α : G →* (B ≃⋆ₐ[ℂ] B))
    (V : unitary (G →ᵇ B)) (g h : G) :
    ‖V.val g * α g (V.val h) - V.val (g * h)‖ ≤ unitaryCocycleDefect α V :=
  (unitaryCocycleError α V).norm_coe_le_norm (g, h)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_FiniteGroupCorrection
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedStarGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.PopaCorner.instOne _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Correcting finite-group unitary representations

The normalized counting mean removes the averaging premise from the bounded
quadratic iteration. The constants are independent of the group's order.
-/

namespace KadisonKastler

open scoped BoundedContinuousFunction

noncomputable section

variable {G B : Type*} [Group G] [Fintype G] [TopologicalSpace G]
  [DiscreteTopology G] [CStarAlgebra B]

/-- A uniformly approximate finite-group representation is uniformly close to
an exact unitary representation in the same C-star algebra. -/
theorem exists_finiteGroup_representation (V : G → unitary B) {δ : ℝ}
    (hδ : 0 ≤ δ) (hsmall : δ ≤ 1 / 64)
    (hV : ∀ g h, ‖(V g : B) * V h - V (g * h)‖ ≤ δ) :
    ∃ W : G →* unitary B, ∀ g, ‖(W g : B) - V g‖ ≤ 2 * δ := by
  let α : G →* (B ≃⋆ₐ[ℂ] B) := 1
  let X := boundedUnitaryFamily V
  have hd : unitaryCocycleDefect α X ≤ δ := by
    apply (BoundedContinuousFunction.norm_le hδ).mpr
    rintro ⟨g, h⟩
    exact hV g h
  obtain ⟨Y, hY, hdist⟩ := exists_bounded_cocycle_of_equivariant_mean α
    finiteGroupBimoduleMean (fun g f => finiteGroupAverage_translate g f) X
    (hd.trans hsmall)
  have hlaw (g h : G) : Y.val g * Y.val h = Y.val (g * h) := hY g h
  let W : G →* unitary B :=
    { toFun := unitaryFamilyEval Y
      map_one' := by
        apply mul_left_cancel (a := unitaryFamilyEval Y 1)
        apply Subtype.ext
        change Y.val 1 * Y.val 1 = Y.val 1 * 1
        simpa only [one_mul, mul_one] using hlaw 1 1
      map_mul' g h := by
        apply Subtype.ext
        exact (hlaw g h).symm }
  refine ⟨W, fun g => ?_⟩
  have hn := (X.val - Y.val).norm_coe_le_norm g
  have hb : ‖X.val - Y.val‖ ≤ 2 * δ := by
    have he : ‖X.val - Y.val‖ ≤ 2 * unitaryCocycleDefect α X := by
      simpa only [Subtype.dist_eq, dist_eq_norm] using hdist
    exact he.trans (mul_le_mul_of_nonneg_left hd (by norm_num))
  change ‖Y.val g - X.val g‖ ≤ _
  rw [norm_sub_rev]
  exact hn.trans hb

/-- Nearby finite-group representations are conjugate by a near-identity
unitary, uniformly in the size of the group. -/
theorem exists_unitary_finiteGroup_intertwiner (U W : G →* unitary B)
    {δ : ℝ} (hsmall : δ < 1)
    (hclose : ∀ g, ‖(W g : B) - U g‖ ≤ δ) :
    ∃ u : unitary B, (∀ g, (u : B) * U g = (W g : B) * u) ∧
      ‖(u : B) - 1‖ ≤ 2 * δ := by
  let α : G →* (B ≃⋆ₐ[ℂ] B) := 1
  apply exists_unitary_boundary_intertwiner α finiteGroupBimoduleMean
    (fun g f => finiteGroupAverage_translate g f) (boundedUnitaryFamily W)
    (fun g h => ?_) U (fun _ _ => rfl) hsmall hclose
  change (W g : B) * (W h : B) = (W (g * h) : B)
  simp only [map_mul, Submonoid.coe_mul]

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_FiniteGroupEmbedding
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedStarGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.characterCommutantCStarAlgebra _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.generatedExtension_cstar _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.normUltraproductNontrivial _root_.OAI.KadisonKastler.operatorFieldAlgebraCStar _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.spatialHilbert_nontrivial _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.tracialSequenceQuotientNontrivial _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Moving a finite unitary group into a nearby closed algebra

Correct the unitary approximants inside the target algebra, then average an
intertwiner. Both operations have bounds independent of the group's order.
-/

namespace KadisonKastler

open scoped BoundedContinuousFunction

noncomputable section

variable {G A : Type*} [Group G] [Fintype G] [TopologicalSpace G]
  [DiscreteTopology G] [CStarAlgebra A]

omit [Fintype G] in
/-- The uniform multiplicative error of a unitary family close to a
representation is at most three times the uniform error. -/
theorem unitary_family_defect_le_of_close (U : G →* unitary A)
    (V : G → unitary A) {e : ℝ} (he : 0 ≤ e)
    (hV : ∀ g, ‖(V g : A) - U g‖ ≤ e) :
    ∀ g h, ‖(V g : A) * V h - V (g * h)‖ ≤ 3 * e := by
  let α : G →* (A ≃⋆ₐ[ℂ] A) := 1
  let X := boundedUnitaryFamily V
  let Y := boundedUnitaryFamily U
  have hz : unitaryCocycleError α Y = 0 := by
    ext ⟨g, h⟩
    change (U g : A) * U h - U (g * h) = 0
    simp only [map_mul, Submonoid.coe_mul, sub_self]
  have hXY : ‖X.val - Y.val‖ ≤ e :=
    (BoundedContinuousFunction.norm_le he).mpr hV
  have hLip := (unitaryCocycleError_lipschitz α).dist_le_mul X Y
  rw [dist_eq_norm, hz, sub_zero, Subtype.dist_eq, dist_eq_norm] at hLip
  have hd : unitaryCocycleDefect α X ≤ 3 * e :=
    hLip.trans (mul_le_mul_of_nonneg_left hXY (by norm_num))
  intro g h
  exact (norm_unitaryCocycleError_le α X g h).trans hd

/-- Uniform unitary approximants in a closed subalgebra give a near-identity
unitary moving the whole finite group into that subalgebra. -/
theorem exists_unitary_finiteGroup_embedding (S : StarSubalgebra ℂ A)
    [IsClosed (S : Set A)] (U : G →* unitary A) (V : G → unitary S)
    {e : ℝ} (he : 0 ≤ e) (hsmall : 3 * e ≤ 1 / 64)
    (hV : ∀ g, ‖(V g : A) - U g‖ ≤ e) :
    ∃ w : unitary A,
      (∀ g, (w : A) * U g * star (w : A) ∈ S) ∧ ‖(w : A) - 1‖ ≤ 14 * e := by
  let j := Unitary.map (StarMonoidHom.ofClass S.subtype)
  have hdef : ∀ g h, ‖(V g : S) * V h - V (g * h)‖ ≤ 3 * e :=
    unitary_family_defect_le_of_close U (fun g => j (V g)) he hV
  obtain ⟨W, hW⟩ := exists_finiteGroup_representation V (by positivity) hsmall hdef
  let W' : G →* unitary A := j.toMonoidHom.comp W
  have hclose (g : G) : ‖(W' g : A) - U g‖ ≤ 7 * e := by
    have h₁ := hW g
    change ‖(W' g : A) - V g‖ ≤ 2 * (3 * e) at h₁
    have ht := norm_sub_le_norm_sub_add_norm_sub (W' g : A) (V g : A) (U g : A)
    linarith [hV g]
  obtain ⟨w, hw, hn⟩ := exists_unitary_finiteGroup_intertwiner U W'
    (by linarith : 7 * e < 1) hclose
  refine ⟨w, fun g => ?_, by linarith⟩
  rw [hw g, mul_assoc, Unitary.mul_star_self_of_mem w.property, mul_one]
  exact (W g : S).property

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The one-sided finite-group embedding supplied by a strict near inclusion. -/
theorem exists_unitary_finiteGroup_embedding_of_nearInclusion
    {M N : VonNeumannAlgebra H} (U : G →* unitary (Algebra M)) {γ : ℝ}
    (hγ : 0 ≤ γ) (hsmall : γ ≤ 1 / 1152) (hnear : NearInclusion M N γ) :
    ∃ w : unitary (H →L[ℂ] H),
      (∀ g, unitaryConj w (U g : H →L[ℂ] H) ∈ N) ∧
      ‖(w : H →L[ℂ] H) - 1‖ ≤ 84 * γ := by
  let : IsClosed (N.toStarSubalgebra : Set (H →L[ℂ] H)) := isClosed_algebra N
  choose V hV using fun g => exists_unitary_approx_of_nearInclusion
    (by linarith : 2 * γ ≤ 1) hnear (U g)
  let U' : G →* unitary (H →L[ℂ] H) :=
    (Unitary.map (StarMonoidHom.ofClass M.toStarSubalgebra.subtype)).toMonoidHom.comp U
  obtain ⟨w, hw, hn⟩ := exists_unitary_finiteGroup_embedding N.toStarSubalgebra U' V
    (by positivity : 0 ≤ 6 * γ) (by linarith : 3 * (6 * γ) ≤ 1 / 64)
    (fun g => (hV g).le)
  exact ⟨w, hw, by linarith⟩

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_FiniteMatrixEmbedding
attribute [-instance] _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.idealStarAlgebraCStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.MatrixUnitSystem.initialHilbertSpace_complete _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildPatching.instFiniteBoundedWord _root_.OAI.HochschildPatching.instFiniteLinearLabel _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.KadisonKastler.FullMatrixCorner.finiteSignedGroup_finite _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.FullMatrixFrame.group_finite _root_.OAI.KadisonKastler.characterCommutantCStarAlgebra _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.generatedExtension_cstar _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.increasingUnionStage_finite _root_.OAI.KadisonKastler.matrixSignedGroup_finite _root_.OAI.KadisonKastler.matrixSiteBlockIndexDecidableEq _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.measurableOperatorSubalgebra_closed _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.operatorFieldAlgebraCStar _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexDecidableEq _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexFintype _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Embedding a nearby full matrix algebra

A finite signed permutation group spans the matrix entries. Correcting that
group therefore moves the whole matrix algebra into the neighbour. The
displacement bound is independent of the matrix size.
-/

namespace KadisonKastler

open scoped BigOperators

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M N : VonNeumannAlgebra H} {n : ℕ}

/-- A full matrix stage in a one-sided near inclusion is unitarily embedded
in the neighbouring algebra, with a dimension-independent bound. -/
theorem exists_unitary_matrixStage_embedding
    (E : Generator.MatrixUnitSystem (Fin n) (Algebra M)) {γ : ℝ}
    (hγ : 0 ≤ γ) (hsmall : γ ≤ 1 / 1152) (hnear : NearInclusion M N γ) :
    ∃ w : unitary (H →L[ℂ] H),
      (∀ x ∈ E.concreteAlgebra, unitaryConj w x ∈ N) ∧
      ‖(w : H →L[ℂ] H) - 1‖ ≤ 84 * γ := by
  let F := matrixSystemOfUnits E
  let G := F.signedPermutationGroup
  let : Fintype G := Fintype.ofFinite G
  let : TopologicalSpace G := ⊥
  let : DiscreteTopology G := ⟨rfl⟩
  let U : G →* unitary (Algebra M) := F.signedPermutationGroup.subtype
  obtain ⟨w, hw, hn⟩ := exists_unitary_finiteGroup_embedding_of_nearInclusion
    U hγ hsmall hnear
  let φ : Algebra M →⋆ₐ[ℂ] (H →L[ℂ] H) :=
    (Unitary.conjStarAlgAut ℂ (H →L[ℂ] H) w).toStarAlgHom.comp M.toStarSubalgebra.subtype
  let S : Submodule ℂ (Algebra M) :=
    N.toStarSubalgebra.toSubalgebra.toSubmodule.comap φ.toAlgHom.toLinearMap
  have hspan : Submodule.span ℂ
      (Set.range (fun g : G => (U g : Algebra M))) ≤ S := by
    apply Submodule.span_le.mpr
    rintro _ ⟨g, rfl⟩
    exact hw g
  have hentry (i j : Fin n) : φ (E.entry i j) ∈ N :=
    hspan (F.entry_mem_signedPermutation_span i j)
  refine ⟨w, ?_, hn⟩
  rintro x ⟨a, rfl⟩
  change φ (E.hom a) ∈ N
  rw [E.hom_apply, map_sum]
  apply N.toStarSubalgebra.sum_mem
  intro i _
  rw [map_sum]
  apply N.toStarSubalgebra.sum_mem
  intro j _
  change φ.toAlgHom.toLinearMap (a i j • E.entry i j) ∈ N
  rw [map_smul]
  exact N.toStarSubalgebra.smul_mem (hentry i j) _

/-- The preceding construction for an entire represented full matrix algebra. -/
theorem exists_unitary_finiteMatrix_embedding_oai
    (E : Generator.MatrixUnitSystem (Fin n) (Algebra M))
    (hE : Function.Surjective E.hom) {γ : ℝ}
    (hγ : 0 ≤ γ) (hsmall : γ ≤ 1 / 1152) (hnear : NearInclusion M N γ) :
    ∃ w : unitary (H →L[ℂ] H),
      (∀ x ∈ M, unitaryConj w x ∈ N) ∧ ‖(w : H →L[ℂ] H) - 1‖ ≤ 84 * γ := by
  obtain ⟨w, hw, hn⟩ := exists_unitary_matrixStage_embedding E hγ hsmall hnear
  refine ⟨w, ?_, hn⟩
  intro x hx
  obtain ⟨a, ha⟩ := hE ⟨x, hx⟩
  exact hw x ⟨a, congrArg Subtype.val ha⟩

end

end KadisonKastler

end OAI
end

theorem solution.{u_1} : type_of% @OAI.KadisonKastler.exists_unitary_finiteMatrix_embedding_oai.{u_1} := @OAI.KadisonKastler.exists_unitary_finiteMatrix_embedding_oai.{u_1}
