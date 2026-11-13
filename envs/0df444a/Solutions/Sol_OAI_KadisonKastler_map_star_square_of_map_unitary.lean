-- Prove2me | solution 1 for OAI.KadisonKastler.map_star_square_of_map_unitary
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T04:43:21.10762+00:00
-- url     : https://prove2.me/submissions/f0c8bd97-aa50-4899-9a0a-bc524524bfc8

import Mathlib
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Algebra.Module.Torsion.Field
import Mathlib.Algebra.Star.StarProjection
import Mathlib.Analysis.CStarAlgebra.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.InnerProductSpace.WeakOperatorTopology
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.Normed.Group.Bounded
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
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Module
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.NormNum
import Mathlib.Topology.Algebra.Algebra
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.Order
import Mathlib.Topology.Sequences
import Definitions.Def_OAIQ075A027
import Definitions.Def_Q260K002
import Definitions.Def_Q260K007

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ProjectionJordanMap
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Projection preservation from unitary preservation

Two scalar phases on a projection determine both its adjoint and its
square. Thus a unital complex-linear map preserving unitaries preserves
projections and orthogonal projection products, without an analytic
expansion of the exponential.
-/

namespace KadisonKastler

noncomputable section

variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]

private theorem phase_square_expansion (x : B) (z : ℂ) :
    star (1 - x + z • x) * (1 - x + z • x) =
      1 + ((z - 1) • x + (star z - 1) • star x +
        ((star z - 1) * (z - 1)) • (star x * x)) := by
  simp only [star_add, star_sub, star_one, star_smul,
    add_mul, mul_add, sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm,
    one_mul, mul_one]
  module

private theorem unitary_phase_equation
    (F : A →ₗ[ℂ] B) (hF1 : F 1 = 1)
    (hFu : ∀ u : unitary A, F u ∈ unitary B)
    (p : A) (hp : IsStarProjection p) (z : ℂ) (hz : star z * z = 1) :
    (z - 1) • F p + (star z - 1) • star (F p) +
      ((star z - 1) * (z - 1)) • (star (F p) * F p) = 0 := by
  have hu := Unitary.star_mul_self_of_mem (hFu (projectionPhaseUnitary p hp z hz))
  change star (F (1 - p + z • p)) * F (1 - p + z • p) = 1 at hu
  rw [map_add, map_sub, map_smul, hF1, phase_square_expansion] at hu
  exact add_left_cancel (show (1 : B) + _ = 1 + 0 by simpa only [add_zero] using hu)

/-- A unital complex-linear unitary-preserving map preserves projections. -/
theorem map_isStarProjection_of_map_unitary
    (F : A →ₗ[ℂ] B) (hF1 : F 1 = 1)
    (hFu : ∀ u : unitary A, F u ∈ unitary B)
    (p : A) (hp : IsStarProjection p) : IsStarProjection (F p) := by
  have hm := unitary_phase_equation F hF1 hFu p hp (-1) (by norm_num)
  have hi := unitary_phase_equation F hF1 hFu p hp Complex.I (by simp)
  have hm' : (-2 : ℂ) • F p + (-2 : ℂ) • star (F p) +
      (4 : ℂ) • (star (F p) * F p) = 0 := by
    have hminus : (-1 : ℂ) - 1 = -2 := by norm_num
    rw [star_neg, star_one, hminus] at hm
    have hfour : (-2 : ℂ) * (-2) = 4 := by norm_num
    rw [hfour] at hm
    exact hm
  have hIc : (star Complex.I - 1) * (Complex.I - 1) = (2 : ℂ) := by
    norm_num [Complex.star_def, Complex.ext_iff, Complex.mul_re, Complex.mul_im]
  have hi' : (Complex.I - 1) • F p + (-Complex.I - 1) • star (F p) +
      (2 : ℂ) • (star (F p) * F p) = 0 := by
    rw [hIc] at hi
    simpa only [show star Complex.I = -Complex.I by simp] using hi
  have hstar0 : Complex.I • (F p - star (F p)) = 0 := by
    calc
      _ = ((Complex.I - 1) • F p + (-Complex.I - 1) • star (F p) +
          (2 : ℂ) • (star (F p) * F p)) -
          (1 / 2 : ℂ) • ((-2 : ℂ) • F p + (-2 : ℂ) • star (F p) +
            (4 : ℂ) • (star (F p) * F p)) := by module
      _ = 0 := by rw [hi', hm']; simp
  have hstar : star (F p) = F p :=
    (sub_eq_zero.mp ((smul_eq_zero.mp hstar0).resolve_left Complex.I_ne_zero)).symm
  have hsq0 : (4 : ℂ) • (F p * F p - F p) = 0 := by
    rw [hstar] at hm'
    calc
      _ = (-2 : ℂ) • F p + (-2 : ℂ) • F p + (4 : ℂ) • (F p * F p) := by module
      _ = 0 := hm'
  exact ⟨sub_eq_zero.mp ((smul_eq_zero.mp hsq0).resolve_left (by norm_num)), hstar⟩

/-- Projection preservation also preserves orthogonality. -/
theorem map_projection_mul_eq_zero_of_map_unitary
    (F : A →ₗ[ℂ] B) (hF1 : F 1 = 1)
    (hFu : ∀ u : unitary A, F u ∈ unitary B)
    (p q : A) (hp : IsStarProjection p) (hq : IsStarProjection q) (hpq : p * q = 0) :
    F p * F q = 0 := by
  let : IsAddTorsionFree B := .of_isTorsionFree ℂ B
  have hFp := map_isStarProjection_of_map_unitary F hF1 hFu p hp
  have hFq := map_isStarProjection_of_map_unitary F hF1 hFu q hq
  have hsum := map_isStarProjection_of_map_unitary F hF1 hFu (p + q) (hp.add hq hpq)
  rw [map_add] at hsum
  have hprod : F p * (F p + F q) = F p := by
    apply (hFp.sub_iff_mul_eq_left hsum).mp
    simpa only [add_sub_cancel_left] using hFq
  rw [mul_add, hFp.isIdempotentElem.eq] at hprod
  exact add_left_cancel (show F p + F p * F q = F p + 0 by simpa only [add_zero] using hprod)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_SpectralJordanMap
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerNormedAlgebra _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.generatedExtension_cstar _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instNormedAlgebraComplexSubtypeMemNonUnitalStarSubalgebra _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instNormedAlgebra _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Jordan structure of a unitary-preserving map on a von Neumann algebra

Projection phases give exact algebraic identities on finite spectral
sums. Norm approximation by those sums then gives adjoint and square
preservation; complex polarization gives the Jordan identity.
-/

namespace KadisonKastler

open scoped BigOperators ComplexStarModule

noncomputable section

variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]

private theorem orthogonal_sum_square {I : Type*} [Fintype I]
    (p : I → A) (c : I → ℂ) (hp : ∀ i, p i * p i = p i)
    (hpq : ∀ i j, i ≠ j → p i * p j = 0) :
    (∑ i, c i • p i) * (∑ i, c i • p i) = ∑ i, (c i ^ 2) • p i := by
  classical
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  simp only [smul_mul_assoc, mul_smul_comm, smul_smul]
  rw [Finset.sum_eq_single i]
  · rw [hp i, pow_two]
  · intro j _ hji
    rw [hpq i j hji.symm, smul_zero]
  · intro hi
    exact (hi (Finset.mem_univ i)).elim

/-- Finite spectral sums retain adjoints and squares under the map. -/
theorem map_star_square_projection_sum {I : Type*} [Fintype I]
    (F : A →ₗ[ℂ] B) (hF1 : F 1 = 1)
    (hFu : ∀ u : unitary A, F u ∈ unitary B)
    (p : I → A) (c : I → ℂ) (hp : ∀ i, IsStarProjection (p i))
    (hpq : ∀ i j, i ≠ j → p i * p j = 0) :
    F (star (∑ i, c i • p i)) = star (F (∑ i, c i • p i)) ∧
      F ((∑ i, c i • p i) * (∑ i, c i • p i)) =
        F (∑ i, c i • p i) * F (∑ i, c i • p i) := by
  have hFp (i : I) := map_isStarProjection_of_map_unitary F hF1 hFu (p i) (hp i)
  constructor
  · simp only [star_sum, star_smul, map_sum, map_smul]
    apply Finset.sum_congr rfl
    intro i _
    rw [(hp i).isSelfAdjoint.star_eq, (hFp i).isSelfAdjoint.star_eq]
  · calc
      _ = F (∑ i, (c i ^ 2) • p i) := congrArg F
        (orthogonal_sum_square p c (fun i => (hp i).isIdempotentElem.eq) hpq)
      _ = ∑ i, (c i ^ 2) • F (p i) := by simp only [map_sum, map_smul]
      _ = (∑ i, c i • F (p i)) * (∑ i, c i • F (p i)) :=
        (orthogonal_sum_square (fun i => F (p i)) c
          (fun i => (hFp i).isIdempotentElem.eq)
          (fun i j hij => map_projection_mul_eq_zero_of_map_unitary F hF1 hFu
            (p i) (p j) (hp i) (hp j) (hpq i j hij))).symm
      _ = _ := by simp only [map_sum, map_smul]

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

/-- Normal elements are norm limits of finite spectral sums, so both
identities extend by continuity. -/
theorem map_star_square_normal_of_map_unitary
    (F : Algebra M →L[ℂ] B) (hF1 : F 1 = 1)
    (hFu : ∀ u : unitary (Algebra M), F u ∈ unitary B)
    (x : Algebra M) (hx : IsStarNormal x) :
    F (star x) = star (F x) ∧ F (x * x) = F x * F x := by
  let S : Set (Algebra M) := {x | F (star x) = star (F x) ∧ F (x * x) = F x * F x}
  have hclosed : IsClosed S := by
    apply IsClosed.inter
    · exact isClosed_eq (by fun_prop) (by fun_prop)
    · exact isClosed_eq (by fun_prop) (by fun_prop)
  have hxcl : x ∈ closure S := by
    apply Metric.mem_closure_iff.mpr
    intro ε hε
    let : IsStarNormal x := hx
    obtain ⟨Q, c, hc⟩ := Generator.Tracial.exists_normal_spectral_approximation x ε hε
    refine ⟨∑ i, c i • (Q.piece i).val, ?_, ?_⟩
    · exact map_star_square_projection_sum F.toLinearMap hF1 hFu
        (fun i => (Q.piece i).val) c (fun i => (Q.piece i).property) Q.orthogonal
    · simpa only [dist_eq_norm] using hc
  rwa [hclosed.closure_eq] at hxcl

private theorem complex_square_expansion (a b : A) :
    (a + Complex.I • b) * (a + Complex.I • b) =
      a * a + Complex.I • (a * b + b * a) - b * b := by
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, smul_smul,
    Complex.I_mul_I, neg_one_smul, smul_add]
  abel

private theorem map_jordan_of_three_squares (F : A →ₗ[ℂ] B) (a b : A)
    (ha : F (a * a) = F a * F a) (hb : F (b * b) = F b * F b)
    (hab : F ((a + b) * (a + b)) = F (a + b) * F (a + b)) :
    F (a * b + b * a) = F a * F b + F b * F a := by
  have he : (F a * F a + F (a * b + b * a)) + F b * F b =
      (F a * F a + (F a * F b + F b * F a)) + F b * F b := by
    calc
      _ = F ((a + b) * (a + b)) := by
        rw [show (a + b) * (a + b) = a * a + (a * b + b * a) + b * b by noncomm_ring]
        simp only [map_add, ha, hb]
      _ = F (a + b) * F (a + b) := hab
      _ = _ := by rw [map_add]; noncomm_ring
  exact add_left_cancel (add_right_cancel he)

/-- A continuous unital linear map preserving unitaries preserves all
adjoints and all squares on a von Neumann algebra. -/
theorem map_star_square_of_map_unitary_oai
    (F : Algebra M →L[ℂ] B) (hF1 : F 1 = 1)
    (hFu : ∀ u : unitary (Algebra M), F u ∈ unitary B) (x : Algebra M) :
    F (star x) = star (F x) ∧ F (x * x) = F x * F x := by
  let a : Algebra M := ℜ x
  let b : Algebra M := ℑ x
  have ha : IsSelfAdjoint a := (ℜ x).property
  have hb : IsSelfAdjoint b := (ℑ x).property
  have he : x = a + Complex.I • b := (realPart_add_I_smul_imaginaryPart x).symm
  have hfa := map_star_square_normal_of_map_unitary F hF1 hFu a ha.isStarNormal
  have hfb := map_star_square_normal_of_map_unitary F hF1 hFu b hb.isStarNormal
  have hfab := map_star_square_normal_of_map_unitary F hF1 hFu (a + b)
    (ha.add hb).isStarNormal
  have hcross : F (a * b + b * a) = F a * F b + F b * F a :=
    map_jordan_of_three_squares F.toLinearMap a b hfa.2 hfb.2 hfab.2
  constructor
  · rw [he]
    simp only [star_add, star_smul, map_add, map_smul, hfa.1, hfb.1]
  · rw [he, complex_square_expansion, map_sub, map_add, map_smul,
      hfa.2, hfb.2, hcross,
      map_add, map_smul, complex_square_expansion]

end

end KadisonKastler

end OAI
end

theorem solution.{u_2, u_3} : type_of% @OAI.KadisonKastler.map_star_square_of_map_unitary_oai.{u_2, u_3} := @OAI.KadisonKastler.map_star_square_of_map_unitary_oai.{u_2, u_3}
