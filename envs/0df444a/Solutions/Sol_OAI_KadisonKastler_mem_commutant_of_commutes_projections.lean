-- Prove2me | solution 1 for OAI.KadisonKastler.mem_commutant_of_commutes_projections
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T07:52:54.056089+00:00
-- url     : https://prove2.me/submissions/02dbf988-a850-498c-b220-eaf216f2ed0a

import Mathlib
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.InnerProductSpace.WeakOperatorTopology
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.PosPart.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.VonNeumannAlgebra.Basic
import Mathlib.Order.Filter.Ultrafilter.Basic
import Mathlib.Order.Zorn
import Mathlib.RingTheory.Congruence.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.NormNum
import Mathlib.Topology.Algebra.Algebra
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.Order
import Mathlib.Topology.Sequences
import Definitions.Def_OAIQ075A027
import Definitions.Def_Q260K000

section
-- module Solutions.OAIQ075_KS.KadisonKastler_VonNeumannProjectionCommutation
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.idealStarAlgebraCStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.projectionOrbitClosure_complete _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Testing commutation on the projections of a von Neumann algebra

Finite spectral sums approximate every self-adjoint element in norm.
Their commutation identities pass to the limit, and real/imaginary
decomposition gives the identity on the whole algebra.
-/

namespace KadisonKastler

noncomputable section

open Generator.Tracial
open scoped ComplexStarModule

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem commutes_vonNeumann_of_projections (N : VonNeumannAlgebra H)
    (C : H →L[ℂ] H) (hp : ∀ p : AlgebraProjection N, Commute C p.val.val) :
    ∀ a : N.toStarSubalgebra, Commute C a.val := by
  let K : Set N.toStarSubalgebra := {a | Commute C a.val}
  have hclosed : IsClosed K := isClosed_eq
    (continuous_const.mul continuous_subtype_val) (continuous_subtype_val.mul continuous_const)
  have hself (a : N.toStarSubalgebra) (ha : IsSelfAdjoint a) : a ∈ K := by
    rw [← hclosed.closure_eq]
    apply Metric.mem_closure_iff.mpr
    intro ε hε
    obtain ⟨Q, c, _, hclose⟩ := exists_finite_spectral_approximation
      (identityProjection N) a ha ε hε
    let b : N.toStarSubalgebra := ∑ i, (c i : ℂ) • (Q.piece i).val
    have hbval : b.val = ∑ i, (c i : ℂ) • (Q.piece i).val.val := by
      change N.toStarSubalgebra.subtype (∑ i, (c i : ℂ) • (Q.piece i).val) = _
      rw [map_sum]
      simp only [map_smul]
      rfl
    refine ⟨b, ?_, ?_⟩
    · change C * b.val = b.val * C
      simp only [hbval,
        Finset.mul_sum, Finset.sum_mul, mul_smul_comm, smul_mul_assoc]
      exact Finset.sum_congr rfl (fun i _ => congrArg (fun z => (c i : ℂ) • z) (hp (Q.piece i)).eq)
    · simpa only [dist_eq_norm, identityProjection, one_mul, mul_one, b] using hclose
  intro a
  have hr := hself (ℜ a) (ℜ a).property
  have hi := hself (ℑ a) (ℑ a).property
  have he : a.val = (ℜ a : N.toStarSubalgebra).val +
      Complex.I • (ℑ a : N.toStarSubalgebra).val :=
    congrArg Subtype.val (realPart_add_I_smul_imaginaryPart a).symm
  change C * a.val = a.val * C
  change C * (ℜ a : N.toStarSubalgebra).val = (ℜ a : N.toStarSubalgebra).val * C at hr
  change C * (ℑ a : N.toStarSubalgebra).val = (ℑ a : N.toStarSubalgebra).val * C at hi
  rw [he, mul_add, add_mul, mul_smul_comm, smul_mul_assoc, hr, hi]

theorem mem_commutant_of_commutes_projections_oai (N : VonNeumannAlgebra H)
    (C : H →L[ℂ] H) (hp : ∀ p : AlgebraProjection N, Commute C p.val.val) :
    C ∈ N.commutant := by
  apply VonNeumannAlgebra.mem_commutant_iff.mpr
  intro a ha
  exact (commutes_vonNeumann_of_projections N C hp ⟨a, ha⟩).eq.symm

end

end KadisonKastler

end OAI
end

theorem solution.{u_1} : type_of% @OAI.KadisonKastler.mem_commutant_of_commutes_projections_oai.{u_1} := @OAI.KadisonKastler.mem_commutant_of_commutes_projections_oai.{u_1}
