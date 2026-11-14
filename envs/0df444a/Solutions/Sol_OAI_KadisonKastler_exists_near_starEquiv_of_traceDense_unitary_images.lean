-- Prove2me | solution 1 for OAI.KadisonKastler.exists_near_starEquiv_of_traceDense_unitary_images
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T07:16:40.874207+00:00
-- url     : https://prove2.me/submissions/8dfcdb06-7e89-45bf-baf0-f83db5cdbadc

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
import Mathlib.Order.Filter.AtTopBot.Prod
import Mathlib.Order.Filter.Ultrafilter.Basic
import Mathlib.Order.Zorn
import Mathlib.RingTheory.Congruence.Basic
import Mathlib.Tactic
import Mathlib.Tactic.Abel
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
import Theorems.Thm_OAI_KadisonKastler_PreservesJordan_multiplicative_of_close_of_II1
import Theorems.Thm_OAI_KadisonKastler_exists_continuous_unital_transfer_of_traceDense
import Theorems.Thm_OAI_KadisonKastler_finiteFactor_isPrimeAlgebra
import Theorems.Thm_OAI_KadisonKastler_map_star_square_of_map_unitary
import Theorems.Thm_OAI_KadisonKastler_preservesJordan_of_map_unitary
import Theorems.Thm_OAI_KadisonKastler_unitary_transfer_bound_of_traceDense

section
-- module Solutions.OAIQ075_KS.KadisonKastler_Basic
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-!
# The concrete Kadison–Kastler distance

The distance is the operator-norm Hausdorff distance between the closed unit
balls of two concrete, unital von Neumann algebras.  All Hilbert spaces are
allowed, including the zero space. The elementary estimates belong to §2 of
*Universal strong Kadison–Kastler stability* (2026).
-/

namespace KadisonKastler

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem kkDistance_nonneg (M N : VonNeumannAlgebra H) : 0 ≤ kkDistance M N :=
  Metric.hausdorffDist_nonneg

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_Range
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-!
# The surjectivity step in the completely positive criterion

The first paragraph of Proposition 2.4 in the manuscript proves surjectivity
from a reverse unit-ball gap strictly below one. The normed-space argument
uses Riesz's lemma and requires no operator-algebra perturbation theorem.
-/

namespace KadisonKastler

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- A closed complex subspace that uniformly approximates the unit ball to
an error strictly below one must be the whole space. -/
theorem eq_top_of_unitBall_approx (V : Submodule ℂ E)
    (hclosed : IsClosed (V : Set E)) {c : ℝ} (hc : c < 1)
    (happrox : ∀ x : E, ‖x‖ ≤ 1 → ∃ y ∈ V, ‖x - y‖ ≤ c) : V = ⊤ := by
  by_contra hproper
  have hout : ∃ x : E, x ∉ V := by
    by_contra h
    push Not at h
    exact hproper (Submodule.eq_top_iff'.mpr h)
  obtain ⟨x, _, hx, hsep⟩ :=
    riesz_lemma_of_lt_one hclosed hout (show (c + 1) / 2 < 1 by linarith)
  obtain ⟨y, hy, hxy⟩ := happrox x hx.le
  have := hsep y hy
  linarith

variable {P Q : Type*} [NormedAddCommGroup P] [NormedSpace ℂ P]
  [NormedAddCommGroup Q] [NormedSpace ℂ Q]

/-- The reverse-gap argument for a continuous linear map with closed range.
The domain and codomain may have different norms and need not be algebras. -/
theorem surjective_of_closed_range_unitBall_approx (F : P →L[ℂ] Q)
    (hclosed : IsClosed (Set.range F)) {c : ℝ} (hc : c < 1)
    (happrox : ∀ y : Q, ‖y‖ ≤ 1 → ∃ x : P, ‖y - F x‖ ≤ c) :
    Function.Surjective F := by
  have htop : F.toLinearMap.range = ⊤ :=
    eq_top_of_unitBall_approx F.toLinearMap.range hclosed hc (by
      intro y hy
      obtain ⟨x, hx⟩ := happrox y hy
      exact ⟨F x, ⟨x, rfl⟩, hx⟩)
  exact LinearMap.range_eq_top.mp htop

/-- The range argument used in the manuscript's UCP criterion. Here `ρ`
and `ι` are isometric embeddings into one ambient operator space. The
reverse gap is expressed with arbitrary positive slack, so no nearest
point or compactness hypothesis is hidden in the statement. -/
theorem bijective_of_close_isometry_and_reverse_gap [CompleteSpace P]
    (ρ : P →L[ℂ] E) (ι : Q →L[ℂ] E) (F : P →L[ℂ] Q)
    (hρ : ∀ x, ‖ρ x‖ = ‖x‖) (hι : ∀ y, ‖ι y‖ = ‖y‖)
    {e g : ℝ} (he : 0 ≤ e) (he1 : e < 1) (hge : g + e < 1)
    (hclose : ∀ x, ‖ι (F x) - ρ x‖ ≤ e * ‖x‖)
    (hgap : ∀ y : Q, ‖y‖ ≤ 1 → ∀ r : ℝ, g < r →
      ∃ x : P, ‖x‖ ≤ 1 ∧ ‖ι y - ρ x‖ < r) :
    Function.Bijective F := by
  have hpos : 0 < 1 - e := sub_pos.mpr he1
  have hlower (x : P) : (1 - e) * ‖x‖ ≤ ‖F x‖ := by
    have ht := norm_add_le (ρ x - ι (F x)) (ι (F x))
    have hc := hclose x
    rw [norm_sub_rev] at hc
    rw [sub_add_cancel, hρ, hι] at ht
    nlinarith
  have hanti : AntilipschitzWith ⟨(1 - e)⁻¹, inv_nonneg.mpr hpos.le⟩ F := by
    apply F.antilipschitz_of_bound
    intro x
    change ‖x‖ ≤ (1 - e)⁻¹ * ‖F x‖
    exact (le_inv_mul_iff₀ hpos).mpr (hlower x)
  refine ⟨hanti.injective, ?_⟩
  apply surjective_of_closed_range_unitBall_approx F
    (hanti.isClosed_range F.uniformContinuous)
    (c := (g + 1 - e) / 2 + e) (by linarith)
  intro y hy
  obtain ⟨x, hx, hxy⟩ := hgap y hy ((g + 1 - e) / 2) (by linarith)
  refine ⟨x, ?_⟩
  calc
    ‖y - F x‖ = ‖ι y - ι (F x)‖ := by rw [← map_sub, hι]
    _ ≤ ‖ι y - ρ x‖ + ‖ρ x - ι (F x)‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ (g + 1 - e) / 2 + e := by
      have hc := hclose x
      rw [norm_sub_rev] at hc
      have hehx : e * ‖x‖ ≤ e := by nlinarith
      linarith

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_UnitaryImageLinearMap
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.idealStarAlgebraCStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.functionalSubspaceWeakScalarTower _root_.OAI.Generator.Tracial.insideAlgebra_complete _root_.OAI.Generator.Tracial.predualWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.boundedSequenceCStarAlgebra _root_.OAI.KadisonKastler.characterCommutantCStarAlgebra _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.generatedExtension_cstar _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.measurableOperatorSubalgebra_closed _root_.OAI.KadisonKastler.operatorFieldAlgebraCStar _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.varyingSequenceCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarModuleComplexTracialQuotient _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The linear map determined by unitary trace vectors

Once every unitary vector has a unitary image, the four-unitary
decomposition constructs a map on the whole algebra. A separating
embedding proves linearity and the quantitative operator-norm bound.
-/

namespace KadisonKastler

open scoped BigOperators

noncomputable section

variable {A B E : Type*} [CStarAlgebra A] [CStarAlgebra B]
  [AddCommGroup E] [Module ℂ E]

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M N : VonNeumannAlgebra H}

/-- The unitary approximation bound extends to all algebra elements,
with the factor two from the four-unitary decomposition. -/
theorem linear_transfer_norm_sub_le
    (θ : Algebra M →ₗ[ℂ] Algebra N) {C : ℝ}
    (hθ : ∀ u : unitary (Algebra M),
      ‖(θ u : H →L[ℂ] H) - (u : Algebra M)‖ ≤ C) (a : Algebra M) :
    ‖(θ a : H →L[ℂ] H) - (a : H →L[ℂ] H)‖ ≤ 2 * C * ‖a‖ := by
  let F : Algebra M →ₗ[ℂ] (H →L[ℂ] H) :=
    N.toStarSubalgebra.subtype.toLinearMap.comp θ - M.toStarSubalgebra.subtype.toLinearMap
  exact norm_le_twice_unitary_bound F hθ a

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_TraceUnitaryIsomorphism
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.idealStarAlgebraCStar _root_.OAI.CuntzPureness.ClosedStarIdeal.idealStarAlgebraCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.MatrixUnitSystem.initialHilbertSpace_complete _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerNormedAlgebra _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildNormalPart.cyclicSpace_complete _root_.OAI.HochschildNormalPart.normalVectors_complete _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.canonicalInitialSpaceComplete _root_.OAI.KadisonKastler.characterCommutantCStarAlgebra _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.finiteReducingSpaceComplete _root_.OAI.KadisonKastler.generatedExtension_complete _root_.OAI.KadisonKastler.generatedExtension_cstar _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instCompleteSpaceSubtypeMemSubmoduleComplexHilbertBasisInitialSpace _root_.OAI.KadisonKastler.measurableOperatorSubalgebra_closed _root_.OAI.KadisonKastler.operatorFieldAlgebraCStar _root_.OAI.KadisonKastler.partialSupportSpace_complete _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.typeIIIInitialSpaceComplete _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instNormedAlgebraComplexSubtypeMemNonUnitalStarSubalgebra _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseSpace_complete _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerSubmodule_complete _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.operatorRangeClosure_complete _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instNormedAlgebra _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The finite-factor isomorphism from boundary unitary images

The unitary image formula determines a continuous unital Jordan map.
The reverse distance gives surjectivity, and the two-by-two matrix
unitaries force its multiplicative orientation.
-/

namespace KadisonKastler

noncomputable section

variable {H E I : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  {M N : VonNeumannAlgebra H}

/-- A uniformly close unitary-image formula on a trace-dense family
produces a nearby star isomorphism between the finite factors. -/
theorem exists_near_starEquiv_of_traceDense_unitary_images_oai
    (hM : Generator.IsII1Factor M.toStarSubalgebra)
    (hN : Generator.IsII1Factor N.toStarSubalgebra)
    (τM : FaithfulTracialState (Algebra M)) (τN : FaithfulTracialState (Algebra N))
    (hτM : FiniteVectorTrace τM) (hτN : FiniteVectorTrace τN)
    (J : Algebra M →ₗ[ℂ] E) (K : Algebra N →ₗ[ℂ] E)
    (hJ : ∀ a, ‖J a‖ = traceTwoNorm τM a)
    (hK : ∀ a, ‖K a‖ = traceTwoNorm τN a)
    (ρ : I → unitary (Algebra M))
    (hρ : ∀ u : unitary (Algebra M), ∀ ε : ℝ, 0 < ε →
      ∃ i, traceTwoNorm τM ((u : Algebra M) - ρ i) < ε)
    (S : unitary (E →L[ℂ] E)) (hS1 : (S : E →L[ℂ] E) (J 1) = K 1)
    {C : ℝ} (hC : 0 ≤ C)
    (himages : ∀ i, ∃ v : unitary (Algebra N),
      K v = (S : E →L[ℂ] E) (J (ρ i)) ∧
      ‖(v : H →L[ℂ] H) - (ρ i : Algebra M)‖ ≤ C)
    (hsmall : 3 * (2 * C) + (2 * C) ^ 2 < 2)
    (hgap : kkDistance M N + 2 * C < 1) :
    ∃ θ : Algebra M ≃⋆ₐ[ℂ] Algebra N,
      (∀ a, K (θ a) = (S : E →L[ℂ] E) (J a)) ∧
      (∀ a, ‖(θ a : H →L[ℂ] H) - (a : H →L[ℂ] H)‖ ≤ 2 * C * ‖a‖) := by
  obtain ⟨F, hF1, hF, hFU⟩ := exists_continuous_unital_transfer_of_traceDense
    τM τN J K hJ hK hτN ρ hρ S hS1 (fun i => by
      obtain ⟨v, hv, _⟩ := himages i
      exact ⟨v, hv⟩)
  have hgroup (i : I) : ‖(F (ρ i) : H →L[ℂ] H) - (ρ i : Algebra M)‖ ≤ C := by
    obtain ⟨v, hv, hb⟩ := himages i
    have he : F (ρ i) = (v : Algebra N) :=
      traceHilbert_injective K hK ((hF (ρ i)).trans hv.symm)
    simpa only [he] using hb
  have hunit := unitary_transfer_bound_of_traceDense τM τN hτM hτN J K hJ hK
    S F.toLinearMap hF hFU ρ hρ hC hgroup
  have hclose := linear_transfer_norm_sub_le F.toLinearMap hunit
  have he : 0 ≤ 2 * C := by positivity
  have he1 : 2 * C < 1 := by linarith [kkDistance_nonneg M N]
  have hbij : Function.Bijective F := by
    apply bijective_of_close_isometry_and_reverse_gap
      (starAlgHomToContinuousLinearMap M.toStarSubalgebra.subtype)
      (starAlgHomToContinuousLinearMap N.toStarSubalgebra.subtype)
      F (fun _ => rfl) (fun _ => rfl) he he1 hgap hclose
    intro y hy r hr
    obtain ⟨x, hx, hxy⟩ := exists_unitBall_approx
      (M := N) (N := M) (x := (y : H →L[ℂ] H)) ⟨y.property, hy⟩
      (by simpa only [kkDistance_comm N M] using hr)
    exact ⟨⟨x, hx.1⟩, hx.2, hxy⟩
  have hmult := PreservesJordan.multiplicative_of_close_of_II1 hM F.toLinearMap
    M.toStarSubalgebra.subtype.toAlgHom N.toStarSubalgebra.subtype.toAlgHom
    (preservesJordan_of_map_unitary F hF1 hFU) hbij.2 (finiteFactor_isPrimeAlgebra hN)
    he (fun _ => rfl) hclose hsmall
  let φ : Algebra M →⋆ₐ[ℂ] Algebra N :=
    { toFun := F
      map_zero' := map_zero F
      map_add' := map_add F
      map_one' := hF1
      map_mul' := hmult
      commutes' := by
        intro z
        change F (z • 1) = z • 1
        rw [map_smul, hF1]
      map_star' := fun x => (map_star_square_of_map_unitary F hF1 hFU x).1 }
  exact ⟨StarAlgEquiv.ofBijective φ hbij, hF, hclose⟩

end

end KadisonKastler

end OAI
end

theorem solution.{u_1, u_2, u_3} : type_of% @OAI.KadisonKastler.exists_near_starEquiv_of_traceDense_unitary_images_oai.{u_1, u_2, u_3} := @OAI.KadisonKastler.exists_near_starEquiv_of_traceDense_unitary_images_oai.{u_1, u_2, u_3}
