-- Prove2me | solution 1 for OAI.KadisonKastler.exists_unitary_invariantGroup_embedding_in_algebra
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T07:16:47.251302+00:00
-- url     : https://prove2.me/submissions/c5d1a3ed-5878-4035-98f5-269494bf816d

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
import Definitions.Def_Q260K029
import Theorems.Thm_OAI_KadisonKastler_ScalarInvariantMean_algebraMean_translate
import Theorems.Thm_OAI_KadisonKastler_exists_group_representation_of_mean
import Theorems.Thm_OAI_KadisonKastler_exists_unitary_approx_of_nearInclusion
import Theorems.Thm_OAI_KadisonKastler_exists_unitary_boundary_intertwiner

section
-- module Solutions.OAIQ075_KS.KadisonKastler_CocycleMetric
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedStarGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
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

local instance instCompleteSpaceSubtypeBoundedContinuousFunctionMemSubmonoidUnitary_solutions_r069434_1 : CompleteSpace (unitary (G →ᵇ B)) := isClosed_unitary.completeSpace_coe
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

local instance boundaryBoundedComplete_r069434_1 : CompleteSpace (unitary (G →ᵇ B)) :=
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
-- module Solutions.OAIQ075_KS.KadisonKastler_FiniteGroupEmbedding
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedStarGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
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

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_LocalizedGroupEmbedding
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.idealStarAlgebraCStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedStarGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerNormedAlgebra _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.characterCommutantCStarAlgebra _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.generatedExtension_cstar _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.operatorFieldAlgebraCStar _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instNormedAlgebraComplexSubtypeMemNonUnitalStarSubalgebra _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instNormedAlgebra _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Localized simultaneous group embeddings

Performing the final intertwining average and polar decomposition inside a
specified von Neumann algebra retains the location of the conjugating unitary.
-/

namespace KadisonKastler

open scoped BoundedContinuousFunction

noncomputable section

variable {G H : Type*} [Group G] [TopologicalSpace G] [DiscreteTopology G]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The embedding unitary lies in any ambient von Neumann algebra containing
both the original and the target algebra. -/
theorem exists_unitary_invariantGroup_embedding_in_algebra_oai
    (m : ScalarInvariantMean G) {M N J : VonNeumannAlgebra H}
    (hMJ : M ≤ J) (hNJ : N ≤ J)
    (U : G →* unitary (Algebra M)) {γ : ℝ}
    (hγ : 0 ≤ γ) (hsmall : γ ≤ 1 / 1152) (hnear : NearInclusion M N γ) :
    ∃ w : unitary (H →L[ℂ] H), (w : H →L[ℂ] H) ∈ J ∧
      (∀ g, unitaryConj w (U g : H →L[ℂ] H) ∈ N) ∧
      ‖(w : H →L[ℂ] H) - 1‖ ≤ 84 * γ := by
  choose V hV using fun g => exists_unitary_approx_of_nearInclusion
    (by linarith : 2 * γ ≤ 1) hnear (U g)
  let j := Unitary.map (StarMonoidHom.ofClass M.toStarSubalgebra.subtype)
  let U' : G →* unitary (H →L[ℂ] H) := j.toMonoidHom.comp U
  have hdef : ∀ g h, ‖(V g : Algebra N) * V h - V (g * h)‖ ≤ 18 * γ := by
    have hh := unitary_family_defect_le_of_close U' (fun g => ambientAlgebraUnitary (V g))
      (by positivity : 0 ≤ 6 * γ) (fun g => (hV g).le)
    intro g h
    exact (hh g h).trans_eq (by ring)
  obtain ⟨W, hW⟩ := exists_group_representation_of_mean (m.algebraBimoduleMean N)
    (m.algebraMean_translate N) V (by positivity : 0 ≤ 18 * γ)
    (by linarith : 18 * γ ≤ 1 / 64) hdef
  let jN := Unitary.map (StarMonoidHom.ofClass N.toStarSubalgebra.subtype)
  let W' : G →* unitary (H →L[ℂ] H) := jN.toMonoidHom.comp W
  have hclose (g : G) : ‖(W' g : H →L[ℂ] H) - U' g‖ ≤ 42 * γ := by
    have hh := hW g
    change ‖(W' g : H →L[ℂ] H) - V g‖ ≤ 2 * (18 * γ) at hh
    have ht := norm_sub_le_norm_sub_add_norm_sub (W' g : H →L[ℂ] H)
      (V g : H →L[ℂ] H) (U' g : H →L[ℂ] H)
    have hv := hV g
    change ‖(V g : H →L[ℂ] H) - U' g‖ < 6 * γ at hv
    linarith
  let jMJ := Unitary.map (StarMonoidHom.ofClass (StarSubalgebra.inclusion hMJ))
  let jNJ := Unitary.map (StarMonoidHom.ofClass (StarSubalgebra.inclusion hNJ))
  let UJ : G →* unitary (Algebra J) := jMJ.toMonoidHom.comp U
  let WJ : G →* unitary (Algebra J) := jNJ.toMonoidHom.comp W
  obtain ⟨wJ, hwJ, hn⟩ := exists_unitary_boundary_intertwiner
    (1 : G →* (Algebra J ≃⋆ₐ[ℂ] Algebra J)) (m.algebraBimoduleMean J)
    (m.algebraMean_translate J) (boundedUnitaryFamily WJ)
    (by intro g h; change (WJ g : Algebra J) * WJ h = WJ (g * h)
        simp only [map_mul, Submonoid.coe_mul]) UJ (fun _ _ => rfl)
    (by linarith : 42 * γ < 1) hclose
  let w := ambientAlgebraUnitary wJ
  have hnorm : ‖(w : H →L[ℂ] H) - 1‖ ≤ 84 * γ := by
    change ‖(wJ : Algebra J) - 1‖ ≤ _
    linarith
  refine ⟨w, wJ.val.property, fun g => ?_, hnorm⟩
  change (w : H →L[ℂ] H) * (U' g : H →L[ℂ] H) * star (w : H →L[ℂ] H) ∈ N
  have hi : (w : H →L[ℂ] H) * U' g = (W' g : H →L[ℂ] H) * w :=
    congrArg (fun x : Algebra J => (x : H →L[ℂ] H)) (hwJ g)
  rw [hi, mul_assoc, Unitary.mul_star_self_of_mem w.property, mul_one]
  exact (W g : Algebra N).property

end

end KadisonKastler

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.KadisonKastler.exists_unitary_invariantGroup_embedding_in_algebra_oai.{u_1, u_2} := @OAI.KadisonKastler.exists_unitary_invariantGroup_embedding_in_algebra_oai.{u_1, u_2}
