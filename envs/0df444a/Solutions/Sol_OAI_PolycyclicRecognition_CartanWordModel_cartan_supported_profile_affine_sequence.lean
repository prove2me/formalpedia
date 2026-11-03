-- Prove2me | solution 1 for OAI.PolycyclicRecognition.CartanWordModel.cartan_supported_profile_affine_sequence
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-02T23:49:25.24451+00:00
-- url     : https://prove2.me/submissions/63c99781-35b5-4bc1-9f1c-ca7b7157133d

import Mathlib
import Definitions.Def_PolycyclicRecognition
import Definitions.Def_OAIQ093D006
import Definitions.Def_OAIQ093D015
import Theorems.Thm_OAI_PolycyclicRecognition_CartanWordModel_cartan_profile_increment_mem_template_sequence
import Theorems.Thm_OAI_PolycyclicRecognition_CartanWordModel_cartan_profile_segment_volume_sequence
import Theorems.Thm_OAI_PolycyclicRecognition_affine_of_horizontal_labels

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_ParametricLieWords
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Lie words as functions of their structure constants

The bilinear bracket itself varies in a finite-dimensional vector space.
Word evaluation is smooth jointly in that bracket and the input vectors, so
word identities and normalization equations persist under limits.
-/

noncomputable section

namespace PolycyclicRecognition

open Set

variable {V I : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  {n : ℕ∞}

/-- Alternation and Jacobi are closed conditions on the bracket. -/
theorem isClosed_setOf_isLieBracket :
    IsClosed {B : V →L[ℝ] V →L[ℝ] V | IsLieBracket B} := by
  simp only [IsLieBracket, ofPred_and, ofPred_forall]
  apply IsClosed.inter
  · apply isClosed_iInter
    intro x
    exact isClosed_eq (by fun_prop) continuous_const
  · apply isClosed_iInter
    intro x
    apply isClosed_iInter
    intro y
    apply isClosed_iInter
    intro z
    exact isClosed_eq (by fun_prop) (by fun_prop)

/-- A fixed word equation is closed even while both bracket and generators
vary. This is the normalization condition used by rescaled word bases. -/
theorem isClosed_bilinearWord_eq [Fintype I] (w : FreeMagma I) (v : V) :
    IsClosed {p : (V →L[ℝ] V →L[ℝ] V) × (I → V) |
      evalBilinearWord p.1 p.2 w = v} := by
  have hc : Continuous (fun p : (V →L[ℝ] V →L[ℝ] V) × (I → V) =>
      evalBilinearWord p.1 p.2 w) :=
    (contDiff_evalBilinearWord (n := 0) Prod.fst (fun p => p.2) contDiff_fst
      (fun i => (contDiff_apply ℝ V i).comp contDiff_snd) w).continuous
  exact isClosed_eq hc continuous_const

/-- All finite word-normalization equations hold on a closed parameter set. -/
theorem isClosed_wordNormalizations [Fintype I] {J : Type}
    (w : J → FreeMagma I) (v : J → V) :
    IsClosed {p : (V →L[ℝ] V →L[ℝ] V) × (I → V) |
      ∀ j, evalBilinearWord p.1 p.2 (w j) = v j} := by
  simp only [ofPred_forall]
  exact isClosed_iInter (fun j => isClosed_bilinearWord_eq (w j) (v j))

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CoordinateLieBrackets
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual Lie law in a chosen basis

Transport the original bracket to Euclidean coordinates, retaining its exact
word identities. A bound on basis structure constants gives a bound in the
finite-dimensional parameter space used for normalized-law compactness.
-/

noncomputable section

namespace PolycyclicRecognition

open Module

variable {L : Type} [LieRing L] [LieAlgebra ℝ L] {n : ℕ}
  (b : Basis (Fin n) ℝ L)

/-- The transported operation is a genuine Lie bracket, not only a bounded
bilinear operation. -/
theorem isLieBracket_basisBracket : IsLieBracket (basisBracket b) := by
  constructor
  · intro x
    simp
  · intro x y z
    simp only [basisBracket_apply, LinearEquiv.symm_apply_apply]
    rw [← map_add, ← leibniz_lie]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_CoordinateBilinearExpansion
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite-coordinate expansion of the transported Lie bracket -/

noncomputable section

namespace PolycyclicRecognition

open Module
open scoped BigOperators

/-- Every coordinate bracket is the finite linear combination of its
structure constants and elementary bilinear maps. -/
theorem basisBracket_eq_coordinate_sum
    {L : Type} [LieRing L] [LieAlgebra ℝ L] {n : ℕ}
    (b : Basis (Fin n) ℝ L) :
    basisBracket b = ∑ i, ∑ j, ∑ k,
      b.repr ⁅b i, b j⁆ k • coordinateBilinearUnit i j k := by
  ext x y k
  rw [basisBracket_apply]
  change b.repr ⁅b.equivFun.symm x, b.equivFun.symm y⁆ k = _
  rw [basis_bracket_coordinate]
  simp only [← Basis.equivFun_apply, LinearEquiv.apply_symm_apply]
  simp [Pi.smul_apply, Pi.single_apply, mul_comm, mul_assoc]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_LogDistortion
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Logarithmic distortion from polynomially corrected contraction

The nilpotent part of a real weight action introduces a polynomial factor.
It is absorbed by an additional logarithmic conjugating time. These lemmas
retain that factor instead of assuming a semisimple action.
-/

noncomputable section

open Filter
open scoped Topology

namespace PolycyclicRecognition

variable {G : Type} [Group G] [PseudoMetricSpace G] [IsIsometricSMul G G]

/-- Product lengths in a left invariant metric. -/
theorem dist_one_mul_le (a b : G) : dist 1 (a * b) ≤ dist 1 a + dist 1 b := by
  calc
    dist 1 (a * b) ≤ dist 1 a + dist a (a * b) := dist_triangle _ _ _
    _ = _ := by simpa only [mul_one] using congrArg (dist 1 a + ·) (dist_mul_left a 1 b)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_ContinuousFlowDistortion
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Continuous contracting flows

The local metric bounds in logarithmic distortion follow from continuity
and compactness. A continuous one-parameter homomorphism has at most linear
metric growth, so no differentiability estimate needs to be assumed here.
-/

noncomputable section

namespace PolycyclicRecognition

open Set Metric

variable {G : Type} [Group G] [PseudoMetricSpace G] [IsIsometricSMul G G]

theorem dist_one_pow_le (g : G) (n : ℕ) : dist 1 (g ^ n) ≤ (n : ℝ) * dist 1 g := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ]
    calc
      dist 1 (g ^ n * g) ≤ dist 1 (g ^ n) + dist 1 g := dist_one_mul_le _ _
      _ ≤ (n : ℝ) * dist 1 g + dist 1 g := add_le_add ih le_rfl
      _ = _ := by push_cast <;> ring

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_PolynomialGroupLaws
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.PolynomialCoordinateGroup.instBorelSpace _root_.OAI.PolycyclicRecognition.PolynomialCoordinateGroup.instGroup _root_.OAI.PolycyclicRecognition.PolynomialCoordinateGroup.instMeasurableSpace _root_.OAI.PolycyclicRecognition.PolynomialCoordinateGroup.instTopologicalSpace _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial group laws in a fixed coordinate space

The binary Dynkin coefficients are fixed once in the original nilpotent
group. Changing its basis changes only the bracket. The group identities and
the straight-line one-parameter identities are closed conditions on this
finite-dimensional bracket parameter.
-/

noncomputable section

namespace PolycyclicRecognition

open Set
open scoped BigOperators

variable {V P : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup P] [NormedSpace ℝ P]

/-- Exponential coordinates transfer the genuine group axioms, rather than
postulating them for a limiting polynomial. -/
theorem polynomialGroupLaws_of_exp {G : Type} [Group G]
    (m : V → V → V) (Exp : V → G) (hinj : Function.Injective Exp)
    (hzero : Exp 0 = 1) (hneg : ∀ x, Exp (-x) = (Exp x)⁻¹)
    (hadd : ∀ x (s t : ℝ), Exp ((s + t) • x) = Exp (s • x) * Exp (t • x))
    (hm : ∀ x y, Exp (m x y) = Exp x * Exp y) : PolynomialGroupLaws m := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro x y z
    apply hinj
    simp only [hm, mul_assoc]
  · intro x
    apply hinj
    rw [hm, hzero, one_mul]
  · intro x
    apply hinj
    rw [hm, hzero, mul_one]
  · intro x
    apply hinj
    rw [hm, hneg, inv_mul_cancel, hzero]
  · intro x s t
    apply hinj
    rw [hm, hadd]

/-- These group identities persist under convergence of the bracket data. -/
theorem isClosed_dynkinGroupLaws {c : ℕ} (a : DynkinCoefficients c 2) :
    IsClosed {B : V →L[ℝ] V →L[ℝ] V | PolynomialGroupLaws (dynkinProduct a B)} := by
  have hc (x y : V) : Continuous (fun B : V →L[ℝ] V →L[ℝ] V =>
      dynkinProduct a B x y) :=
    continuous_dynkinProduct a id (fun _ => x) (fun _ => y)
      continuous_id continuous_const continuous_const
  simp only [PolynomialGroupLaws, ofPred_and, ofPred_forall]
  apply IsClosed.inter
  · apply isClosed_iInter
    intro x
    apply isClosed_iInter
    intro y
    apply isClosed_iInter
    intro z
    exact isClosed_eq
      (continuous_dynkinProduct (V := V) a id _ _ continuous_id (hc x y) continuous_const)
      (continuous_dynkinProduct (V := V) a id _ _ continuous_id continuous_const (hc y z))
  refine (isClosed_iInter (fun x => isClosed_eq (hc 0 x) continuous_const)).inter ?_
  refine (isClosed_iInter (fun x => isClosed_eq (hc x 0) continuous_const)).inter ?_
  refine (isClosed_iInter (fun x => isClosed_eq (hc (-x) x) continuous_const)).inter ?_
  exact isClosed_iInter (fun x => isClosed_iInter (fun s =>
    isClosed_iInter (fun t => isClosed_eq (hc (s • x) (t • x)) continuous_const)))

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_NormalizedWordBrackets
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform normalized structure constants

In a maximizing word basis, the bracket of two basis words is either zero
or another word of the finite list. Basis exchange then bounds every scaled
bracket coefficient independently of the letter amplitudes.
-/

noncomputable section

namespace PolycyclicRecognition

open Module LieModule

variable {I L : Type} [LieRing L] [LieAlgebra ℝ L]
  [Fintype I] [DecidableEq I] [FiniteDimensional ℝ L]

omit [FiniteDimensional ℝ L] in
theorem repr_exponentialRescaleBasis_bracket {J : Type}
    (b : Basis J ℝ L) (cost : J → ℝ) (r : ℝ) (i j l : J) :
    (exponentialRescaleBasis b cost r).repr
      ⁅exponentialRescaleBasis b cost r i, exponentialRescaleBasis b cost r j⁆ l =
      b.repr ⁅b i, b j⁆ l * Real.exp (r * (cost i + cost j - cost l)) := by
  simp only [exponentialRescaleBasis, Basis.repr_unitsSMul, Basis.unitsSMul_apply,
    Units.smul_def, Units.val_mk0, Units.val_inv_eq_inv_val,
    smul_lie, lie_smul, map_smul, Finsupp.smul_apply, smul_eq_mul]
  rw [← Real.exp_neg]
  have he : Real.exp (-(r * cost l)) * Real.exp (r * cost i) * Real.exp (r * cost j) =
      Real.exp (r * (cost i + cost j - cost l)) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  calc
    _ = b.repr ⁅b i, b j⁆ l *
        (Real.exp (-(r * cost l)) * Real.exp (r * cost i) * Real.exp (r * cost j)) := by ring
    _ = _ := by rw [he]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_SupportTemplates
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finite_templateSymmetryGroup _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteRootOffsetConeIndex _root_.OAI.PolycyclicRecognition.instFiniteSubtypeLinearEquivRealIdMemSubgroupLinearSupportSymmetryGroup _root_.OAI.PolycyclicRecognition.instNonemptyRootOffsetConeIndex _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Support exponents of compact templates

The support exponent is the finite maximum of word-basis exponents, with
each letter allowed its own supporting point. Balance gives translation
invariance, and segments recover the support norm.
-/

noncomputable section

namespace PolycyclicRecognition.SupportDatum

open scoped BigOperators

variable {W I B : Type} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [FiniteDimensional ℝ W] [Fintype I] [Fintype B] [Nonempty B]
  (D : PolycyclicRecognition.SupportDatum W I B)

omit [Nonempty B] in
theorem basisTemplateSupport_translate {E : Set W} (hE : IsCompact E) (hne : E.Nonempty)
    (w : W) (b : B) :
    D.basisTemplateSupport ((fun x => x + w) '' E) b = D.basisTemplateSupport E b := by
  simp only [basisTemplateSupport, D.weightSupport_translate hE hne, mul_add,
    Finset.sum_add_distrib, D.balanced, add_zero]

theorem templateSupport_translate {E : Set W} (hE : IsCompact E) (hne : E.Nonempty)
    (w : W) : D.templateSupport ((fun x => x + w) '' E) = D.templateSupport E := by
  simp only [templateSupport, D.basisTemplateSupport_translate hE hne]

omit [FiniteDimensional ℝ W] in
theorem basisTemplateSupport_le (E : Set W) (b : B) :
    D.basisTemplateSupport E b ≤ D.templateSupport E :=
  Finset.le_sup' (f := D.basisTemplateSupport E) (Finset.mem_univ b)

omit [FiniteDimensional ℝ W] in
theorem templateSupport_le {E : Set W} {r : ℝ}
    (h : ∀ b, D.basisTemplateSupport E b ≤ r) : D.templateSupport E ≤ r :=
  Finset.sup'_le _ _ fun b _ => h b

omit [Nonempty B] in
/-- Nearby support positions change each letter exponent by at most the
operator norm of that letter times the error in position. -/
theorem weightSupport_le_of_nearby {E F : Set W} (hE : IsCompact E) (hneE : E.Nonempty)
    (hF : IsCompact F) {δ : ℝ}
    (hnear : ∀ x ∈ E, ∃ y ∈ F, ‖x - y‖ ≤ δ) (i : I) :
    D.weightSupport E i ≤ D.weightSupport F i + ‖(D.weight i).toContinuousLinearMap‖ * δ := by
  obtain ⟨x, hx, hsup⟩ := D.exists_weightSupport_point hE hneE i
  obtain ⟨y, hy, hxy⟩ := hnear x hx
  have hop := (D.weight i).toContinuousLinearMap.le_opNorm (x - y)
  change ‖D.weight i (x - y)‖ ≤ _ at hop
  rw [map_sub, Real.norm_eq_abs] at hop
  have hh := hop.trans (mul_le_mul_of_nonneg_left hxy
    (norm_nonneg (D.weight i).toContinuousLinearMap))
  have hy' := D.weight_le_weightSupport hF hy i
  rw [hsup]
  linarith [le_abs_self (D.weight i x - D.weight i y)]

omit [Nonempty B] in
theorem templateSupportConstant_nonneg : 0 ≤ D.templateSupportConstant :=
  Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg
    (fun _ _ => mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _)))

theorem templateSupport_le_of_nearby {E F : Set W} (hE : IsCompact E) (hneE : E.Nonempty)
    (hF : IsCompact F) {δ : ℝ} (hδ : 0 ≤ δ)
    (hnear : ∀ x ∈ E, ∃ y ∈ F, ‖x - y‖ ≤ δ) :
    D.templateSupport E ≤ D.templateSupport F + D.templateSupportConstant * δ := by
  apply D.templateSupport_le
  intro b
  have hc : (∑ i, (D.multiplicity b i : ℝ) * ‖(D.weight i).toContinuousLinearMap‖) ≤
      D.templateSupportConstant := by
    unfold templateSupportConstant
    exact Finset.single_le_sum
      (f := fun b => ∑ i, (D.multiplicity b i : ℝ) * ‖(D.weight i).toContinuousLinearMap‖)
      (fun b _ => Finset.sum_nonneg
        (fun _ _ => mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _))) (Finset.mem_univ b)
  calc
    D.basisTemplateSupport E b ≤
        ∑ i, (D.multiplicity b i : ℝ) *
          (D.weightSupport F i + ‖(D.weight i).toContinuousLinearMap‖ * δ) :=
      Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left
        (D.weightSupport_le_of_nearby hE hneE hF hnear i) (Nat.cast_nonneg _))
    _ = D.basisTemplateSupport F b +
        (∑ i, (D.multiplicity b i : ℝ) * ‖(D.weight i).toContinuousLinearMap‖) * δ := by
      simp only [basisTemplateSupport, mul_add, Finset.sum_add_distrib, Finset.sum_mul, mul_assoc]
    _ ≤ D.templateSupport F + D.templateSupportConstant * δ :=
      add_le_add (D.basisTemplateSupport_le F b) (mul_le_mul_of_nonneg_right hc hδ)

end PolycyclicRecognition.SupportDatum

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanBoxMaps
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Propagating root-action bounds through Cartan boxes

A Lie map which preserves the letter root spaces has a polynomial bound in
every maximizing box. The proof propagates the bounds on letters through
actual bracket words, then through their coordinate basis. This is the
algebraic step in the box-conjugation estimate.
-/

noncomputable section

namespace PolycyclicRecognition

open Module
open scoped BigOperators Manifold

variable {I L : Type} [LieRing L] [LieAlgebra ℝ L] [Fintype I] [DecidableEq I]

set_option maxHeartbeats 1000000 in
/-- Independent exponential scaling of letters multiplies a word by the
exponential of the sum of its letter exponents. -/
theorem evalBracketWord_exp_smul (X : I → L) (s : I → ℝ) (r : ℝ) (w : FreeMagma I) :
    evalBracketWord (fun i => Real.exp (r * s i) • X i) w =
      Real.exp (r * bracketWordExponent s w) • evalBracketWord X w := by
  induction w using FreeMagma.rec with
  | of i => simp only [evalBracketWord_of, bracketWordExponent_of]
  | mul u v hu hv =>
    change evalBracketWord (fun i => Real.exp (r * s i) • X i) (u * v) =
      Real.exp (r * bracketWordExponent s (u * v)) • evalBracketWord X (u * v)
    rw [evalBracketWord_mul, hu, hv, smul_lie, lie_smul, smul_smul,
      ← Real.exp_add, bracketWordExponent_mul, mul_add, evalBracketWord_mul]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_RescaledLieFamily
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.CartanFactorModel.realScaleProfile_apply _root_.OAI.PolycyclicRecognition.bracketWordDifferential_mul _root_.OAI.PolycyclicRecognition.exponentialRescaleBasis_zero _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual rescalings lie in a compact family of normalized Lie laws

Both the law and the generator vectors are transported by the same rescaled
word basis. Basis-word identities hold exactly, independently of the scale.
-/

noncomputable section

namespace PolycyclicRecognition

open Module LieModule

variable {I L : Type} [LieRing L] [LieAlgebra ℝ L]
  [Fintype I] [DecidableEq I]

/-- A selected rescaled word is exactly its coordinate unit vector. -/
theorem rescaledLieData_word (X : I → L) (S : Finset (FreeMagma I))
    (β : WordBasisSelections X S) (s : I → ℝ) (r : ℝ)
    (j : Fin (finrank ℝ L)) :
    evalBilinearWord (rescaledLieData X S β s r).1
      (rescaledLieData X S β s r).2 (β.val j) = Pi.single j 1 := by
  let b := exponentialRescaleBasis (WordBasisSelections.basis X S β)
    (fun j => bracketWordExponent s (β.val j)) r
  change evalBilinearWord (basisBracket b)
    (fun i => b.equivFun (Real.exp (r * s i) • X i)) (β.val j) = _
  rw [evalBilinearWord_basisBracket, evalBracketWord_exp_smul]
  have he : Real.exp (r * bracketWordExponent s (β.val j)) •
      evalBracketWord X (β.val j) = b j := by
    have hw := WordBasisSelections.eval_words X S β j
    change evalBracketWord X (β.val j) = _ at hw
    rw [hw]
    simp only [b, exponentialRescaleBasis, Basis.unitsSMul_apply,
      Units.smul_def, Units.val_mk0]
  rw [he]
  ext k
  simp [Pi.single_apply, eq_comm]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_NormalizedGroupLaws
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.PolynomialCoordinateGroup.instBorelSpace _root_.OAI.PolycyclicRecognition.PolynomialCoordinateGroup.instGroup _root_.OAI.PolycyclicRecognition.PolynomialCoordinateGroup.instMeasurableSpace _root_.OAI.PolycyclicRecognition.PolynomialCoordinateGroup.instTopologicalSpace _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.PolynomialCoordinateGroup.exp_mul _root_.OAI.PolycyclicRecognition.PolynomialCoordinateGroup.exp_neg _root_.OAI.PolycyclicRecognition.PolynomialCoordinateGroup.exp_zero _root_.OAI.PolycyclicRecognition.basisDynkinParameter_zero _root_.OAI.PolycyclicRecognition.dynkinRightTranslation_apply _root_.OAI.PolycyclicRecognition.dynkinRightTranslation_symm_apply _root_.OAI.PolycyclicRecognition.exponentialHomOfDynkin_apply_exp _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Compact polynomial group laws for the actual rescalings

One fixed binary Dynkin formula suffices for all coordinate bases of the
original group. Its group and one-parameter identities are proved in each
basis, and closedness preserves them in the compact normalized family.
-/

noncomputable section

namespace PolycyclicRecognition

open Module Set

variable {V I J : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] [Fintype I]

variable {L : Type} [LieRing L] [LieAlgebra ℝ L] {n : ℕ}
  {G : Type} [Group G]

/-- The binary polynomial in any basis is the genuine product in exponential
coordinates. No fresh Dynkin coefficients are chosen on rescaling. -/
theorem basis_polynomialGroupLaws (b : Basis (Fin n) ℝ L)
    (Exp : L → G) (hinj : Function.Injective Exp)
    (hzero : Exp 0 = 1) (hneg : ∀ x, Exp (-x) = (Exp x)⁻¹)
    (hadd : ∀ x (s t : ℝ), Exp ((s + t) • x) = Exp (s • x) * Exp (t • x))
    {c : ℕ} (a : DynkinCoefficients c 2)
    (hm : ∀ x y, Exp (finiteDynkinPolynomial a ![x, y]) = Exp x * Exp y) :
    PolynomialGroupLaws (dynkinProduct a (basisBracket b)) := by
  apply polynomialGroupLaws_of_exp _ (Exp ∘ b.equivFun.symm)
    (hinj.comp b.equivFun.symm.injective)
  · simpa using hzero
  · intro x
    simpa using hneg (b.equivFun.symm x)
  · intro x s t
    simpa using hadd (b.equivFun.symm x) s t
  · intro x y
    have he := basis_dynkinProduct b a (b.equivFun.symm x) (b.equivFun.symm y)
    simp only [LinearEquiv.apply_symm_apply] at he
    simp only [Function.comp_apply, he, LinearEquiv.symm_apply_apply]
    exact hm _ _

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_CoordinateConjugation
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Conjugation identities persist under coordinate limits

The exponential of the coordinate adjoint is the genuine logarithmic
conjugation map. This identity is closed in the bracket parameter and will
identify the columns of the limiting generator endpoint map.
-/

noncomputable section

namespace PolycyclicRecognition

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

/-- The logarithmic conjugation identity is a closed condition. -/
theorem isClosed_exponentialConjugationLaw {c : ℕ} (a : DynkinCoefficients c 2) :
    IsClosed {B : V →L[ℝ] V →L[ℝ] V |
      ExponentialConjugationLaw (dynkinProduct a B) B} := by
  let : NormedAlgebra ℚ (V →L[ℝ] V) := NormedAlgebra.restrictScalars ℚ ℝ _
  simp only [ExponentialConjugationLaw, Set.ofPred_forall]
  apply isClosed_iInter
  intro x
  apply isClosed_iInter
  intro y
  apply isClosed_iInter
  intro t
  have hc : Continuous (fun B : V →L[ℝ] V →L[ℝ] V =>
      dynkinProduct a B (t • x) y) :=
    continuous_dynkinProduct (V := V) a id _ _ continuous_id continuous_const continuous_const
  apply isClosed_eq
  · exact continuous_dynkinProduct (V := V) a id _ _
      continuous_id hc continuous_const
  · exact (NormedSpace.exp_continuous.comp
      ((ContinuousLinearMap.apply ℝ (V →L[ℝ] V) x).continuous.const_smul t)).clm_apply
        continuous_const

variable {L : Type} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]

attribute [local instance] OAI.PolycyclicRecognition.coordinateConjugationNormedAddCommGroup
attribute [local instance] OAI.PolycyclicRecognition.coordinateConjugationNormedSpace
/-- Coordinate change intertwines actual adjoint exponentials. -/
theorem basis_exp_adjoint {n : ℕ} (b : Module.Basis (Fin n) ℝ L)
    (x y : L) (t : ℝ) :
    b.equivFun (NormedSpace.exp (t • continuousAd x) y) =
      NormedSpace.exp (t • basisBracket b (b.equivFun x)) (b.equivFun y) := by
  let f : L →L[ℝ] (Fin n → ℝ) := b.equivFun.toContinuousLinearEquiv
  apply exp_intertwine_apply f
  intro z
  change b.equivFun (t • ⁅x, z⁆) =
    t • b.equivFun ⁅b.equivFun.symm (b.equivFun x), b.equivFun.symm (b.equivFun z)⁆
  simp only [map_smul, LinearEquiv.symm_apply_apply]

variable {G A : Type} [Group G] [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

attribute [local instance 100] LieRing.ofAssociativeRing

/-- The representation-derived conjugation formula transports to every
coordinate basis with the same binary Dynkin coefficients. -/
theorem basis_exponentialConjugationLaw {n c : ℕ} (b : Module.Basis (Fin n) ℝ L)
    (Exp : L → G) (hinj : Function.Injective Exp)
    (hneg : ∀ x, Exp (-x) = (Exp x)⁻¹)
    (a : DynkinCoefficients c 2)
    (hm : ∀ x y, Exp (finiteDynkinPolynomial a ![x, y]) = Exp x * Exp y)
    (j : L →ₗ⁅ℝ⁆ A) (ρ : G →* Aˣ) (hρ : Function.Injective ρ)
    (hmatch : ∀ x, ρ (Exp x) = algebraExpUnit (j x)) :
    ExponentialConjugationLaw (dynkinProduct a (basisBracket b)) (basisBracket b) := by
  have hp (x y : Fin n → ℝ) :
      Exp (b.equivFun.symm (dynkinProduct a (basisBracket b) x y)) =
        Exp (b.equivFun.symm x) * Exp (b.equivFun.symm y) := by
    have he := basis_dynkinProduct b a (b.equivFun.symm x) (b.equivFun.symm y)
    simp only [LinearEquiv.apply_symm_apply] at he
    rw [he, LinearEquiv.symm_apply_apply, hm]
  intro x y t
  apply hinj.comp b.equivFun.symm.injective
  change Exp (b.equivFun.symm _) = Exp (b.equivFun.symm _)
  rw [hp, hp, map_neg, hneg, map_smul]
  have hc := basis_exp_adjoint b (b.equivFun.symm x) (b.equivFun.symm y) t
  simp only [LinearEquiv.apply_symm_apply] at hc
  have he := congrArg b.equivFun.symm hc
  simp only [LinearEquiv.symm_apply_apply] at he
  rw [← he]
  exact (exp_ad_eq_group_conjugation Exp j ρ hρ hmatch _ _ t).symm

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_PolynomialCoordinateGroup
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.PolynomialCoordinateGroup.instBorelSpace _root_.OAI.PolycyclicRecognition.PolynomialCoordinateGroup.instMeasurableSpace _root_.OAI.PolycyclicRecognition.PolynomialCoordinateGroup.instTopologicalSpace _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The group carried by a polynomial coordinate law

This type keeps the group multiplication distinct from vector addition. The
exponential-coordinate bijection is the identity on underlying points.
-/

noncomputable section

namespace PolycyclicRecognition

variable {V I : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]

namespace PolynomialCoordinateGroup

variable (m : V → V → V) (h : PolynomialGroupLaws m)

theorem exp_add_smul (x : V) (s t : ℝ) :
    exp m h ((s + t) • x) = exp m h (s • x) * exp m h (t • x) :=
  (h.2.2.2.2 x s t).symm

end PolynomialCoordinateGroup

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_PolynomialCoordinateTopology
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The topology carried by an actual polynomial coordinate group -/

noncomputable section

namespace PolycyclicRecognition.PolynomialCoordinateGroup

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem isTopologicalGroup (m : V → V → V) (h : PolynomialGroupLaws m)
    (hc : Continuous (fun p : V × V => m p.1 p.2)) :
    IsTopologicalGroup (PolynomialCoordinateGroup m h) where
  continuous_mul := hc
  continuous_inv := by
    change Continuous (fun x : V => -x)
    exact continuous_neg

end PolycyclicRecognition.PolynomialCoordinateGroup

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_FlowLineDifferentiability
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instNonemptyBases _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_nonempty _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Almost-everywhere differentiability at base points of horizontal flows -/

noncomputable section

namespace PolycyclicRecognition

open Set Filter MeasureTheory MeasureTheory.Measure
open scoped NNReal

theorem ae_of_ae_right_translates
    {G T : Type} [Group G] [MeasurableSpace G] [MeasurableMul₂ G]
    [MeasurableSpace T] (μ : Measure G) [SFinite μ] [μ.IsMulRightInvariant]
    (ν : Measure T) [SFinite ν] [NeZero ν]
    (F : T → G) (hF : Measurable F) {p : G → Prop}
    (hp : MeasurableSet {g | p g})
    (h : ∀ g, ∀ᵐ t ∂ν, p (g * F t)) : ∀ᵐ g ∂μ, p g := by
  have hm : MeasurableSet {z : G × T | p (z.1 * F z.2)} :=
    hp.preimage (measurable_fst.mul (hF.comp measurable_snd))
  have hswap := (ae_ae_comm (μ := μ) (ν := ν) hm).mp (Eventually.of_forall h)
  obtain ⟨t, ht⟩ := hswap.exists
  have hh := (measurePreserving_mul_right μ (F t)⁻¹).quasiMeasurePreserving.ae ht
  simpa only [mul_assoc, inv_mul_cancel, mul_one] using hh

theorem ae_flowLine_differentiableAt_zero
    {G V W : Type} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
    (μ : Measure G) [SFinite μ] [μ.IsMulRightInvariant]
    (Exp : V → G) (hExp : Continuous Exp)
    (hadd : ∀ v (s t : ℝ), Exp ((s + t) • v) = Exp (s • v) * Exp (t • v))
    (v : V) (f : G → W) (hf : Continuous f) (Ω : Set G) (hΩ : IsOpen Ω)
    (C : ℝ≥0)
    (hlip : ∀ g, LipschitzOnWith C (fun t : ℝ => f (g * Exp (t • v)))
      {t | g * Exp (t • v) ∈ Ω}) :
    ∀ᵐ g ∂μ, g ∈ Ω → DifferentiableAt ℝ (fun t : ℝ => f (g * Exp (t • v))) 0 := by
  let curve := fun (g : G) (t : ℝ) => f (g * Exp (t • v))
  have hc : Continuous curve.uncurry := by
    change Continuous (fun z : G × ℝ => f (z.1 * Exp (z.2 • v)))
    fun_prop
  have hm : MeasurableSet {g : G | g ∈ Ω → DifferentiableAt ℝ (curve g) 0} := by
    have hd := measurableSet_of_differentiableAt_with_param ℝ hc
    have hd0 := hd.preimage (measurable_id.prodMk (measurable_const (a := (0 : ℝ))))
    convert hΩ.measurableSet.compl.union hd0 using 1
    all_goals try with_reducible_and_instances rfl
    ext g
    simp only [mem_union, mem_compl_iff, mem_preimage, mem_ofPred_eq,
      Function.id_def, imp_iff_not_or]
  apply ae_of_ae_right_translates μ volume (fun t : ℝ => Exp (t • v))
    ((hExp.comp (continuous_id.smul continuous_const)).measurable) hm
  intro g
  have ho : IsOpen {t : ℝ | g * Exp (t • v) ∈ Ω} :=
    hΩ.preimage (by fun_prop)
  filter_upwards [(hlip g).ae_differentiableWithinAt_of_mem (μ := volume)] with t ht htΩ
  have hd := (ht htΩ).differentiableAt (ho.mem_nhds htΩ)
  have hd' : DifferentiableAt ℝ (curve g) (t + 0) := by simpa [curve] using hd
  have hcomp := hd'.comp (0 : ℝ) (differentiableAt_id.const_add t)
  have heq : curve (g * Exp (t • v)) = fun s : ℝ => curve g (t + s) := by
    funext s
    dsimp [curve]
    rw [mul_assoc, ← hadd]
  rwa [heq]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_HorizontalFlowDerivative
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Measurable, locally bounded derivatives along horizontal flows -/

noncomputable section

namespace PolycyclicRecognition

open Set Filter MeasureTheory
open scoped NNReal

variable {G V W : Type} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]

omit [SecondCountableTopology G] in
theorem stronglyMeasurable_flowDeriv
    (f : G → W) (hf : Continuous f) (Exp : V → G) (hExp : Continuous Exp) (v : V) :
    StronglyMeasurable (flowDeriv f Exp v) := by
  have hc : Continuous (fun z : G × ℝ => f (z.1 * Exp (z.2 • v))) := by fun_prop
  exact (stronglyMeasurable_deriv_with_param
    (f := fun g t => f (g * Exp (t • v))) hc).comp_measurable
    (measurable_id.prodMk (measurable_const (a := (0 : ℝ))))

theorem ae_hasDerivAt_flowDeriv
    (μ : Measure G) [SFinite μ] [μ.IsMulRightInvariant]
    (Exp : V → G) (hExp : Continuous Exp)
    (hadd : ∀ v (s t : ℝ), Exp ((s + t) • v) = Exp (s • v) * Exp (t • v))
    (v : V) (f : G → W) (hf : Continuous f) (Ω : Set G) (hΩ : IsOpen Ω)
    (C : ℝ≥0)
    (hlip : ∀ g, LipschitzOnWith C (fun t : ℝ => f (g * Exp (t • v)))
      {t | g * Exp (t • v) ∈ Ω}) :
    ∀ᵐ g ∂μ, g ∈ Ω → HasDerivAt (fun t : ℝ => f (g * Exp (t • v)))
      (flowDeriv f Exp v g) 0 := by
  filter_upwards [ae_flowLine_differentiableAt_zero μ Exp hExp hadd v f hf Ω hΩ C hlip]
    with g hg hmem
  exact (hg hmem).hasDerivAt

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_FlowDerivativeIntegral
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Differentiating compactly supported pairings along horizontal flows -/

noncomputable section

namespace PolycyclicRecognition

open Set Filter MeasureTheory
open scoped Topology NNReal

theorem eventually_compact_right_flow_mem
    {G V : Type} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    {K Ω : Set G} (hK : IsCompact K) (hΩ : IsOpen Ω) (hKΩ : K ⊆ Ω)
    {Exp : V → G} (hExp : Continuous Exp) (hzero : Exp 0 = 1) (v : V) :
    ∀ᶠ t in 𝓝 (0 : ℝ), ∀ g ∈ K, g * Exp (t • v) ∈ Ω := by
  apply hK.eventually_forall_of_forall_eventually
  intro g hg
  have hc : Continuous (fun z : ℝ × G => z.2 * Exp (z.1 • v)) := by fun_prop
  exact hc.continuousAt.eventually (hΩ.mem_nhds (by simpa [hzero] using hKΩ hg))

variable {G V W : Type} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G] [T2Space G]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]

omit [T2Space G] in
theorem hasDerivAt_integral_right_flow
    (μ : Measure G) [SFinite μ] [IsFiniteMeasureOnCompacts μ] [μ.IsMulRightInvariant]
    (Exp : V → G) (hExp : Continuous Exp) (hzero : Exp 0 = 1)
    (hadd : ∀ v (s t : ℝ), Exp ((s + t) • v) = Exp (s • v) * Exp (t • v))
    (v : V) (f : G → W) (hf : Continuous f) (Ω : Set G) (hΩ : IsOpen Ω)
    (C : ℝ≥0)
    (hlip : ∀ g, LipschitzOnWith C (fun t : ℝ => f (g * Exp (t • v)))
      {t | g * Exp (t • v) ∈ Ω})
    (φ : G → ℝ) (hφ : Continuous φ) (hcφ : HasCompactSupport φ)
    (hsφ : tsupport φ ⊆ Ω) :
    HasDerivAt (fun t : ℝ => ∫ g, φ g • f (g * Exp (t • v)) ∂μ)
      (∫ g, φ g • flowDeriv f Exp v g ∂μ) 0 := by
  obtain ⟨s, hs, hstay⟩ := Filter.eventually_iff_exists_mem.mp
    (eventually_compact_right_flow_mem hcφ hΩ hsφ hExp hzero v)
  apply (hasDerivAt_integral_of_dominated_loc_of_lip (μ := μ)
    (F := fun (t : ℝ) (g : G) => φ g • f (g * Exp (t • v)))
    (F' := fun g => φ g • flowDeriv f Exp v g)
    (bound := fun g => ‖φ g‖ * (C : ℝ)) hs ?_ ?_ ?_ ?_ ?_ ?_).2
  · exact Eventually.of_forall (fun t => (hφ.smul (by fun_prop)).aestronglyMeasurable)
  · simp only [zero_smul, hzero, mul_one]
    have hc : Continuous (fun g : G => φ g • f g) := hφ.smul hf
    have hk : HasCompactSupport (fun g : G => φ g • f g) := hcφ.smul_right
    exact hc.integrable_of_hasCompactSupport hk
  · exact hφ.aestronglyMeasurable.smul
      (stronglyMeasurable_flowDeriv f hf Exp hExp v).aestronglyMeasurable
  · filter_upwards with g
    apply LipschitzOnWith.of_dist_le_mul
    intro t ht u hu
    by_cases hg : φ g = 0
    · simp [hg]
    · have hgK : g ∈ tsupport φ := subset_tsupport φ hg
      have hd := (hlip g).dist_le_mul t (hstay t ht g hgK) u (hstay u hu g hgK)
      rw [dist_eq_norm, ← smul_sub, norm_smul]
      simp only [Real.coe_nnabs, abs_mul, abs_norm, abs_of_nonneg C.coe_nonneg]
      calc
        ‖φ g‖ * ‖f (g * Exp (t • v)) - f (g * Exp (u • v))‖
          ≤ ‖φ g‖ * ((C : ℝ) * dist t u) := by
            gcongr
            simpa only [dist_eq_norm] using hd
        _ = ‖φ g‖ * (C : ℝ) * dist t u := (mul_assoc _ _ _).symm
  · exact (hφ.norm.integrable_of_hasCompactSupport hcφ.norm).mul_const C
  · filter_upwards [ae_hasDerivAt_flowDeriv μ Exp hExp hadd v f hf Ω hΩ C hlip]
      with g hg
    by_cases hz : φ g = 0
    · simpa [hz] using (hasDerivAt_const (0 : ℝ) (0 : W))
    · exact (hg (hsφ (subset_tsupport φ hz))).const_smul (φ g)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CompactFlowTest
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Differentiating translated compactly supported test functions -/

noncomputable section

namespace PolycyclicRecognition

open Set Filter MeasureTheory
open scoped Topology

theorem hasDerivAt_integral_translated_test
    {G W : Type} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    [MeasurableSpace G] [BorelSpace G] [T2Space G] [SecondCountableTopology G]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
    (μ : Measure G) [IsFiniteMeasureOnCompacts μ]
    (e : ℝ → G) (he : Continuous e) (he0 : e 0 = 1)
    (headd : ∀ s t, e (s + t) = e s * e t)
    (φ : G → ℝ) (hφ : Continuous φ) (hcφ : HasCompactSupport φ)
    (dφ : ℝ → G → ℝ) (hdφ : Continuous dφ.uncurry)
    (hderiv : ∀ t g, HasDerivAt (fun s => φ (g * e s)) (dφ t g) t)
    (f : G → W) (hf : Continuous f) :
    HasDerivAt (fun t => ∫ g, φ (g * e t) • f g ∂μ)
      (∫ g, dφ 0 g • f g ∂μ) 0 := by
  let K := (fun z : G × ℝ => z.1 * e (-z.2)) '' (tsupport φ ×ˢ Icc (-1 : ℝ) 1)
  have hK : IsCompact K := (hcφ.prod isCompact_Icc).image (by fun_prop)
  have hzero (g : G) (hg : g ∉ K) (t : ℝ) (ht : t ∈ Icc (-1 : ℝ) 1) :
      φ (g * e t) = 0 := by
    by_contra h
    apply hg
    refine ⟨(g * e t, t), ⟨subset_tsupport φ h, ht⟩, ?_⟩
    dsimp
    rw [mul_assoc, ← headd]
    simp [he0]
  have hd0 (g : G) (hg : g ∉ K) (t : ℝ) (ht : t ∈ Ioo (-1 : ℝ) 1) :
      dφ t g = 0 := by
    apply (hderiv t g).unique
    apply (hasDerivAt_const t (0 : ℝ)).congr_of_eventuallyEq
    filter_upwards [isOpen_Ioo.mem_nhds ht] with u hu
    exact hzero g hg u ⟨hu.1.le, hu.2.le⟩
  obtain ⟨D, hD⟩ := (isCompact_Icc.prod hK).exists_bound_of_continuousOn hdφ.continuousOn
  let bound : G → ℝ := K.indicator (fun g => D * ‖f g‖)
  have hbound : Integrable bound μ := by
    exact ((hf.norm.const_mul D).continuousOn.integrableOn_compact hK).integrable_indicator
      hK.measurableSet
  apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ)
    (F := fun (t : ℝ) (g : G) => φ (g * e t) • f g)
    (F' := fun t g => dφ t g • f g)
    (bound := bound) (s := Ioo (-1 : ℝ) 1) (Ioo_mem_nhds (by norm_num) (by norm_num))
    ?_ ?_ ?_ ?_ hbound ?_).2
  · exact Eventually.of_forall (fun t => ((hφ.comp (by fun_prop)).smul hf).aestronglyMeasurable)
  · simp only [he0, mul_one]
    have hc : Continuous (fun g : G => φ g • f g) := hφ.smul hf
    have hk : HasCompactSupport (fun g : G => φ g • f g) := hcφ.smul_right
    exact hc.integrable_of_hasCompactSupport hk
  · exact ((hdφ.comp (continuous_const.prodMk continuous_id)).smul hf).aestronglyMeasurable
  · filter_upwards with g t ht
    by_cases hg : g ∈ K
    · rw [norm_smul, show bound g = D * ‖f g‖ from indicator_of_mem hg _]
      exact mul_le_mul_of_nonneg_right (hD (t, g) ⟨⟨ht.1.le, ht.2.le⟩, hg⟩) (norm_nonneg _)
    · simp [hd0 g hg t ht, bound, indicator_of_notMem hg]
  · exact Eventually.of_forall (fun g t _ => (hderiv t g).smul_const (f g))

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_FlowIntegrationByParts
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Haar invariance identifies the weak horizontal derivative -/

noncomputable section

namespace PolycyclicRecognition

open Set MeasureTheory
open scoped NNReal

theorem integral_flowDeriv_smul_eq
    {G V W : Type} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G] [T2Space G]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
    (μ : Measure G) [SFinite μ] [IsFiniteMeasureOnCompacts μ] [μ.IsMulRightInvariant]
    (Exp : V → G) (hExp : Continuous Exp) (hzero : Exp 0 = 1)
    (hadd : ∀ v (s t : ℝ), Exp ((s + t) • v) = Exp (s • v) * Exp (t • v))
    (v : V) (f : G → W) (hf : Continuous f) (Ω : Set G) (hΩ : IsOpen Ω)
    (C : ℝ≥0)
    (hlip : ∀ g, LipschitzOnWith C (fun t : ℝ => f (g * Exp (t • v)))
      {t | g * Exp (t • v) ∈ Ω})
    (φ : G → ℝ) (hφ : Continuous φ) (hcφ : HasCompactSupport φ)
    (hsφ : tsupport φ ⊆ Ω)
    (dφ : ℝ → G → ℝ) (hdφ : Continuous dφ.uncurry)
    (hderiv : ∀ t g, HasDerivAt (fun s : ℝ => φ (g * Exp ((-s) • v))) (dφ t g) t) :
    (∫ g, φ g • flowDeriv f Exp v g ∂μ) = ∫ g, dφ 0 g • f g ∂μ := by
  have hleft := hasDerivAt_integral_right_flow μ Exp hExp hzero hadd v f hf Ω hΩ C hlip
    φ hφ hcφ hsφ
  have hright := hasDerivAt_integral_translated_test μ
    (fun t : ℝ => Exp ((-t) • v)) (by fun_prop) (by simpa using hzero)
    (fun s t => by simpa only [neg_add] using hadd v (-s) (-t))
    φ hφ hcφ dφ hdφ hderiv f hf
  apply hleft.unique
  convert hright using 1
  all_goals try with_reducible_and_instances rfl
  funext t
  rw [← integral_mul_right_eq_self (μ := μ)
    (fun g => φ g • f (g * Exp (t • v))) (Exp ((-t) • v))]
  apply integral_congr_ae
  filter_upwards with g
  simp only [mul_assoc, ← hadd, neg_add_cancel, zero_smul, hzero, mul_one]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_SmoothFlowTest
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The derivative of a smooth test function along a coordinate flow -/

noncomputable section

namespace PolycyclicRecognition

open Set
open scoped ContDiff

theorem exists_smooth_flow_test_derivative
    {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (m : V → V → V) (hm : ContDiff ℝ ∞ (fun z : V × V => m z.1 z.2))
    (hm0 : ∀ g, m g 0 = g)
    (φ : V → ℝ) (hφ : ContDiff ℝ ∞ φ) (v : V) :
    ∃ dφ : ℝ → V → ℝ, Continuous dφ.uncurry ∧
      (∀ t g, HasDerivAt (fun s : ℝ => φ (m g ((-s) • v))) (dφ t g) t) ∧
      ∀ g, dφ 0 g = -(fderiv ℝ φ g ((fderiv ℝ (m g) 0) v)) := by
  let ψ : ℝ × V → ℝ := fun z => φ (m z.2 ((-z.1) • v))
  have hψ : ContDiff ℝ ∞ ψ :=
    hφ.comp (hm.comp (contDiff_snd.prodMk (contDiff_fst.neg.smul contDiff_const)))
  let dφ : ℝ → V → ℝ := fun t g => (fderiv ℝ ψ (t, g)) (1, 0)
  have hd (t : ℝ) (g : V) :
      HasDerivAt (fun s : ℝ => φ (m g ((-s) • v))) (dφ t g) t := by
    exact (hψ.differentiable (by simp) (t, g)).hasFDerivAt.comp_hasDerivAt t
      ((hasDerivAt_id t).prodMk (hasDerivAt_const t g))
  refine ⟨dφ, ?_, hd, ?_⟩
  · exact (hψ.continuous_fderiv (by simp)).clm_apply continuous_const
  · intro g
    have hmg : DifferentiableAt ℝ (m g) 0 :=
      ((hm.comp (contDiff_const.prodMk contDiff_id)).differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)) 0
    have hin : HasDerivAt (fun s : ℝ => (-s) • v) (-v) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).neg.smul_const v)
    have hpath : HasDerivAt (fun s : ℝ => m g ((-s) • v))
        ((fderiv ℝ (m g) 0) (-v)) 0 := by
      have hh : HasFDerivAt (m g) (fderiv ℝ (m g) 0) ((- (0 : ℝ)) • v) := by
        simpa only [neg_zero, zero_smul] using hmg.hasFDerivAt
      exact hh.comp_hasDerivAt 0 hin
    have houter := ((hφ.differentiable (by simp)) (m g ((-(0 : ℝ)) • v))).hasFDerivAt.comp_hasDerivAt 0 hpath
    have heq : dφ 0 g = -(fderiv ℝ φ g ((fderiv ℝ (m g) 0) v)) := by
      apply (hd 0 g).unique
      simpa only [neg_zero, zero_smul, hm0, map_neg, Function.comp_def] using houter
    exact heq

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CoordinateFlowDerivative
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Weak derivatives in smooth polynomial group coordinates -/

noncomputable section

namespace PolycyclicRecognition

open Set MeasureTheory
open scoped NNReal ContDiff

theorem coordinateFlowDeriv_smul {V W : Type}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (m : V → V → V) (f : V → W) (c : ℝ) (v g : V) :
    coordinateFlowDeriv m f (c • v) g = c • coordinateFlowDeriv m f v g := by
  have heq : (fun t : ℝ => f (m g (t • (c • v)))) =
      (fun t : ℝ => f (m g ((c * t) • v))) := by
    funext t
    rw [smul_smul, mul_comm]
  unfold coordinateFlowDeriv
  rw [heq]
  simpa only [mul_zero] using deriv_comp_mul_left c (fun t : ℝ => f (m g (t • v))) 0

theorem stronglyMeasurable_coordinateFlowDeriv {V W : Type}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [MeasurableSpace V] [BorelSpace V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
    (m : V → V → V) (hm : Continuous (fun z : V × V => m z.1 z.2))
    (f : V → W) (hf : Continuous f) (v : V) :
    StronglyMeasurable (coordinateFlowDeriv m f v) := by
  have hc : Continuous (fun z : V × ℝ => f (m z.1 (z.2 • v))) :=
    hf.comp (hm.comp (continuous_fst.prodMk (continuous_snd.smul continuous_const)))
  exact (stronglyMeasurable_deriv_with_param
    (f := fun g t => f (m g (t • v))) hc).comp_measurable
    (measurable_id.prodMk (measurable_const (a := (0 : ℝ))))

theorem norm_coordinateFlowDeriv_le {V W : Type}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (m : V → V → V) (hm : Continuous (fun z : V × V => m z.1 z.2))
    (hm0 : ∀ g, m g 0 = g) (f : V → W) (Ω : Set V) (hΩ : IsOpen Ω)
    (v : V) (C : ℝ≥0)
    (hlip : ∀ g, LipschitzOnWith C (fun t : ℝ => f (m g (t • v)))
      {t | m g (t • v) ∈ Ω}) {g : V} (hg : g ∈ Ω) :
    ‖coordinateFlowDeriv m f v g‖ ≤ C := by
  apply norm_deriv_le_of_lipschitzOn _ (hlip g)
  apply (hΩ.preimage (hm.comp (continuous_const.prodMk
    (continuous_id.smul continuous_const)))).mem_nhds
  simpa [hm0] using hg

theorem locallyIntegrableOn_coordinateFlowDeriv {V W : Type}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
    (μ : Measure V) [IsFiniteMeasureOnCompacts μ]
    (m : V → V → V) (hm : Continuous (fun z : V × V => m z.1 z.2))
    (hm0 : ∀ g, m g 0 = g) (f : V → W) (hf : Continuous f)
    (Ω : Set V) (hΩ : IsOpen Ω) (v : V) (C : ℝ≥0)
    (hlip : ∀ g, LipschitzOnWith C (fun t : ℝ => f (m g (t • v)))
      {t | m g (t • v) ∈ Ω}) : LocallyIntegrableOn (coordinateFlowDeriv m f v) Ω μ := by
  apply (locallyIntegrableOn_iff hΩ.isLocallyClosed).mpr
  intro K hKΩ hK
  apply IntegrableOn.of_bound hK.measure_lt_top
    (stronglyMeasurable_coordinateFlowDeriv m hm f hf v).aestronglyMeasurable.restrict C
  filter_upwards [ae_restrict_mem hK.measurableSet] with g hg
  exact norm_coordinateFlowDeriv_le m hm hm0 f Ω hΩ v C hlip (hKΩ hg)

theorem coordinate_flow_integration_by_parts
    {V W : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
    (m : V → V → V) (hg : PolynomialGroupLaws m)
    (hm : ContDiff ℝ ∞ (fun z : V × V => m z.1 z.2))
    (μ : Measure (PolynomialCoordinateGroup m hg))
    [SFinite μ] [IsFiniteMeasureOnCompacts μ] [μ.IsMulRightInvariant]
    (f : V → W) (hf : Continuous f) (Ω : Set V) (hΩ : IsOpen Ω)
    (v : V) (C : ℝ≥0)
    (hlip : ∀ g, LipschitzOnWith C (fun t : ℝ => f (m g (t • v)))
      {t | m g (t • v) ∈ Ω})
    (φ : V → ℝ) (hφ : ContDiff ℝ ∞ φ) (hcφ : HasCompactSupport φ)
    (hsφ : tsupport φ ⊆ Ω) :
    (∫ g, φ g • coordinateFlowDeriv m f v g ∂μ) =
      -(∫ g, fderiv ℝ φ g ((fderiv ℝ (m g) 0) v) • f g ∂μ) := by
  let G := PolynomialCoordinateGroup m hg
  let e : V ≃ₜ G := PolynomialCoordinateGroup.expHomeomorph m hg
  let : IsTopologicalGroup G := PolynomialCoordinateGroup.isTopologicalGroup m hg hm.continuous
  let : SecondCountableTopology G := e.symm.isOpenEmbedding.secondCountableTopology
  let : T2Space G := e.symm.isEmbedding.t2Space
  obtain ⟨dφ, hdφ, hd, hd0⟩ := exists_smooth_flow_test_derivative m hm hg.2.2.1 φ hφ v
  have h := integral_flowDeriv_smul_eq (G := G) μ e e.continuous (by rfl)
    (PolynomialCoordinateGroup.exp_add_smul m hg) v f hf Ω hΩ C hlip
    φ hφ.continuous hcφ hsφ dφ hdφ hd
  change (∫ g : V, φ g • coordinateFlowDeriv m f v g ∂μ) = ∫ g : V, dφ 0 g • f g ∂μ at h
  calc
    _ = ∫ g : V, dφ 0 g • f g ∂μ := h
    _ = _ := by
      rw [← integral_neg]
      apply integral_congr_ae
      filter_upwards with g
      exact (congrArg (fun x : ℝ => x • f (show V from g))
        (hd0 (show V from g))).trans (neg_smul _ _)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_WeakDirectionalLinearity
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Linearity of locally bounded weak directional derivatives -/

noncomputable section

namespace PolycyclicRecognition

open Set Filter MeasureTheory
open scoped ContDiff

theorem integrable_test_smul_of_locallyIntegrableOn
    {E W : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    {μ : Measure E} {Ω : Set E} {f : E → W} (hf : LocallyIntegrableOn f Ω μ)
    {φ : E → ℝ} (hφ : Continuous φ) (hcφ : HasCompactSupport φ) (hsφ : tsupport φ ⊆ Ω) :
    Integrable (fun x => φ x • f x) μ := by
  have hi := (hf.integrableOn_compact_subset hsφ hcφ).continuousOn_smul hφ.continuousOn hcφ
  apply (integrableOn_iff_integrable_of_support_subset (s := tsupport φ) ?_).mp hi
  intro x hx
  by_contra hn
  have hz := image_eq_zero_of_notMem_tsupport hn
  simp [hz] at hx

theorem ae_add_of_weak_directional_derivatives
    {E V W : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
    (μ : Measure E) [IsFiniteMeasureOnCompacts μ]
    (Ω : Set E) (hΩ : IsOpen Ω) (q : V → E → W)
    (hq : ∀ v, LocallyIntegrableOn (q v) Ω μ)
    (Y : E → V →L[ℝ] E) (hY : Continuous Y) (f : E → W) (hf : Continuous f)
    (hweak : ∀ v (φ : E → ℝ), ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
      (∫ g, φ g • q v g ∂μ) = -(∫ g, fderiv ℝ φ g (Y g v) • f g ∂μ))
    (v w : V) : ∀ᵐ g ∂μ, g ∈ Ω → q (v + w) g = q v g + q w g := by
  have hr (φ : E → ℝ) (hφ : ContDiff ℝ ∞ φ) (hcφ : HasCompactSupport φ) (u : V) :
      Integrable (fun g => fderiv ℝ φ g (Y g u) • f g) μ := by
    apply Continuous.integrable_of_hasCompactSupport
    · exact ((hφ.continuous_fderiv (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).clm_apply (hY.clm_apply continuous_const)).smul hf
    · apply (hcφ.fderiv ℝ).mono'
      intro g hg
      apply subset_tsupport (fderiv ℝ φ)
      change fderiv ℝ φ g ≠ 0
      intro hz
      change (fderiv ℝ φ g (Y g u) • f g) ≠ 0 at hg
      exact hg (by simp [hz])
  have hz : ∀ᵐ g ∂μ, g ∈ Ω → (q (v + w) - (q v + q w)) g = 0 := by
    apply hΩ.ae_eq_zero_of_integral_contDiff_smul_eq_zero
      ((hq (v + w)).sub ((hq v).add (hq w)))
    intro φ hφ hcφ hsφ
    have hi u := integrable_test_smul_of_locallyIntegrableOn (hq u) hφ.continuous hcφ hsφ
    have hisum : Integrable (fun g => φ g • q v g + φ g • q w g) μ := (hi v).add (hi w)
    simp only [Pi.sub_apply, Pi.add_apply, smul_sub, smul_add]
    rw [integral_sub (hi _) hisum, integral_add (hi _) (hi _)]
    rw [hweak (v + w) φ hφ hcφ hsφ, hweak v φ hφ hcφ hsφ, hweak w φ hφ hcφ hsφ]
    simp only [map_add, add_smul]
    rw [integral_add (hr φ hφ hcφ v) (hr φ hφ hcφ w)]
    abel
  filter_upwards [hz] with g hg hgΩ
  exact sub_eq_zero.mp (hg hgΩ)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_CoordinateWeakLinearity
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.dynkinRightTranslation_apply _root_.OAI.PolycyclicRecognition.dynkinRightTranslation_symm_apply _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Almost-everywhere additivity of actual horizontal flow derivatives -/

noncomputable section

namespace PolycyclicRecognition

open Set MeasureTheory
open scoped NNReal ContDiff

theorem ae_horizontalFlowDeriv_add
    {H V W : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
    (m : V → V → V) (hg : PolynomialGroupLaws m)
    (hm : ContDiff ℝ ∞ (fun z : V × V => m z.1 z.2))
    (μ : Measure (PolynomialCoordinateGroup m hg))
    [SFinite μ] [IsFiniteMeasureOnCompacts μ] [μ.IsMulRightInvariant]
    (f : V → W) (hf : Continuous f) (Ω : Set V) (hΩ : IsOpen Ω)
    (D : H →L[ℝ] V) (C : H → ℝ≥0)
    (hlip : ∀ v g, LipschitzOnWith (C v) (fun t : ℝ => f (m g (t • D v)))
      {t | m g (t • D v) ∈ Ω})
    (v w : H) : ∀ᵐ (g : V) ∂μ, g ∈ Ω →
      coordinateFlowDeriv m f (D (v + w)) g =
        coordinateFlowDeriv m f (D v) g + coordinateFlowDeriv m f (D w) g := by
  let : IsFiniteMeasureOnCompacts (show Measure V from μ) :=
    inferInstanceAs (IsFiniteMeasureOnCompacts μ)
  have hY : Continuous (fun g => fderiv ℝ (m g) 0) :=
    Continuous.fderiv (f := m) hm continuous_const (by simp)
  exact ae_add_of_weak_directional_derivatives (show Measure V from μ) Ω hΩ
    (fun u => coordinateFlowDeriv m f (D u))
    (fun u => locallyIntegrableOn_coordinateFlowDeriv (show Measure V from μ)
      m hm.continuous hg.2.2.1 f hf Ω hΩ (D u) (C u) (hlip u))
    (fun g => (fderiv ℝ (m g) 0).comp D) (hY.clm_comp continuous_const) f hf
    (fun u φ hφ hcφ hsφ => coordinate_flow_integration_by_parts m hg hm μ
      f hf Ω hΩ (D u) (C u) (hlip u) φ hφ hcφ hsφ) v w

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_AffineLabels
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instNonemptyBases _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_nonempty _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# One global label from finite pointwise linear choices

The profile affinity criterion shows that a linear derivative
agrees at each vector with one of finitely many linear symmetry maps. The label
cannot depend on the vector: otherwise finitely many proper linear kernels
would cover the real vector space.
-/

namespace PolycyclicRecognition

universe u v

/-- A real linear map which agrees pointwise with a finite family of real linear
maps agrees with one member of the family everywhere. -/
theorem exists_eq_of_pointwise_linear_selection
    {ι : Type} [Finite ι] {W : Type} [AddCommGroup W] [Module ℝ W]
    (B : W →ₗ[ℝ] W) (A : ι → W →ₗ[ℝ] W)
    (hpointwise : ∀ w, ∃ i, B w = A i w) :
    ∃ i, B = A i := by
  classical
  by_contra hnone
  have hne (i : ι) : B ≠ A i := fun hi => hnone ⟨i, hi⟩
  have hproper (i : ι) : LinearMap.ker (B - A i) ≠ ⊤ := by
    intro hker
    apply hne i
    apply LinearMap.ext
    intro w
    have hmem : w ∈ LinearMap.ker (B - A i) := by
      rw [hker]
      trivial
    exact sub_eq_zero.mp (LinearMap.mem_ker.mp hmem)
  obtain ⟨w, hw⟩ :=
    Submodule.exists_forall_notMem_of_forall_ne_top (fun i => LinearMap.ker (B - A i)) hproper
  obtain ⟨i, hi⟩ := hpointwise w
  apply hw i
  exact LinearMap.mem_ker.mpr (sub_eq_zero.mpr hi)

end PolycyclicRecognition

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_ConvexOrbit
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # From convex orbit constraints to a single linear label -/

namespace PolycyclicRecognition

universe u v

/-- Strict convexity prevents a convex combination of points in a closed ball
from lying on the sphere unless it is one of the original points. This is
the finite-orbit selection step of the profile affinity argument. -/
theorem mem_of_mem_convexHull_of_norm_eq
    {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] [StrictConvexSpace ℝ W]
    {s : Set W} {x : W} {r : ℝ}
    (hs : ∀ y ∈ s, ‖y‖ ≤ r) (hx : x ∈ convexHull ℝ s) (hnorm : ‖x‖ = r) :
    x ∈ s := by
  by_cases hr : r = 0
  · have hs0 : s ⊆ {0} := by
      intro y hy
      exact norm_eq_zero.mp (le_antisymm ((hs y hy).trans_eq hr) (norm_nonneg y))
    have heq : convexHull ℝ s = s := by
      exact (Set.subsingleton_singleton.anti hs0).convex.convexHull_eq
    rwa [heq] at hx
  · have hball : convexHull ℝ s ⊆ Metric.closedBall (0 : W) r := by
      apply convexHull_min _ (convex_closedBall 0 r)
      intro y hy
      simpa only [Metric.mem_closedBall, dist_zero_right] using hs y hy
    have hsphere : x ∈ Metric.sphere (0 : W) r := by
      simpa only [Metric.mem_sphere, dist_zero_right] using hnorm
    have hext := StrictConvexSpace.sphere_subset_extremePoints_closedBall (0 : W) hr hsphere
    exact extremePoints_convexHull_subset
      (inter_extremePoints_subset_extremePoints_of_subset hball ⟨hx, hext⟩)


end PolycyclicRecognition

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_FiniteInvariantOrbit
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Selecting a label in a finite linear group

Embedding a vector in the Euclidean product of all its group translates
provides an invariant strictly convex norm without changing the topology or
norm instances on the original height space.
-/

noncomputable section

namespace PolycyclicRecognition

open Set

variable {W E : Type} [AddCommGroup W] [Module ℝ W]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (Γ : Subgroup (W ≃ₗ[ℝ] W)) [Fintype Γ] (e : W →ₗ[ℝ] E)

omit [Fintype Γ] in
theorem finiteOrbitEmbedding_injective (he : Function.Injective e) :
    Function.Injective (finiteOrbitEmbedding Γ e) := by
  intro w u h
  apply he
  have hh := congrArg (fun f : PiLp 2 (fun _ : Γ => E) => f 1) h
  simpa using hh

theorem finiteOrbitEmbedding_norm (g : Γ) (w : W) :
    ‖finiteOrbitEmbedding Γ e (g.val w)‖ = ‖finiteOrbitEmbedding Γ e w‖ := by
  rw [PiLp.norm_eq_of_L2, PiLp.norm_eq_of_L2]
  congr 1
  change (∑ k : Γ, ‖e ((k * g).val w)‖ ^ 2) = ∑ k : Γ, ‖e (k.val w)‖ ^ 2
  exact Fintype.sum_equiv (Equiv.mulRight g) _ _ (fun _ => rfl)

/-- A member of a finite linear group lying pointwise in the convex orbit
of a finite family is one of the members of that family. -/
theorem exists_eq_label_of_finite_group_convex_orbit
    {J : Type} [Finite J] (he : Function.Injective e)
    (B : Γ) (A : J → Γ)
    (hconv : ∀ w, B.val w ∈ convexHull ℝ (range fun j => (A j).val w)) :
    ∃ j, B = A j := by
  let L := finiteOrbitEmbedding Γ e
  have hinj : Function.Injective L := finiteOrbitEmbedding_injective Γ e he
  have hpoint (w : W) : ∃ j, B.val w = (A j).val w := by
    have hL : L (B.val w) ∈ convexHull ℝ (range fun j => L ((A j).val w)) := by
      have hh := mem_image_of_mem L (hconv w)
      rw [L.image_convexHull, ← range_comp] at hh
      exact hh
    have hm := mem_of_mem_convexHull_of_norm_eq
      (s := range fun j => L ((A j).val w))
      (r := ‖L w‖)
      (by rintro _ ⟨j, rfl⟩; exact (finiteOrbitEmbedding_norm Γ e (A j) w).le)
      hL (finiteOrbitEmbedding_norm Γ e B w)
    obtain ⟨j, hj⟩ := hm
    exact ⟨j, hinj hj.symm⟩
  obtain ⟨j, hj⟩ := exists_eq_of_pointwise_linear_selection B.val.toLinearMap
    (fun j => (A j).val.toLinearMap) hpoint
  refine ⟨j, Subtype.ext ?_⟩
  ext w
  exact LinearMap.congr_fun hj w

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_GradedCoordinateLimit
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instNonemptyBases _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_nonempty _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.CartanFactorModel.realScaleProfile_apply _root_.OAI.PolycyclicRecognition.bracketWordDifferential_mul _root_.OAI.PolycyclicRecognition.exponentialRescaleBasis_zero _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The limiting Lie law of maximizing word coordinates -/

noncomputable section

namespace PolycyclicRecognition

open Module LieModule Filter
open scoped BigOperators Topology

variable {L : Type} [LieRing L] [LieAlgebra ℝ L] {n : ℕ}

/-- Each normalized structure constant converges; the strict-degree terms
vanish and the degree-preserving terms stay unchanged. -/
theorem rescaled_structureCoefficient_tendsto
    (b : Basis (Fin n) ℝ L) (cost : Fin n → ℝ)
    (hweight : ∀ i j k, b.repr ⁅b i, b j⁆ k ≠ 0 → cost i + cost j ≤ cost k)
    (i j k : Fin n) :
    Tendsto (fun r : ℝ => (exponentialRescaleBasis b cost r).repr
      ⁅exponentialRescaleBasis b cost r i, exponentialRescaleBasis b cost r j⁆ k)
      atTop (𝓝 (if cost i + cost j = cost k then b.repr ⁅b i, b j⁆ k else 0)) := by
  simp_rw [repr_exponentialRescaleBasis_bracket]
  by_cases hz : b.repr ⁅b i, b j⁆ k = 0
  · simp only [hz, zero_mul, ite_self]
    exact tendsto_const_nhds
  by_cases he : cost i + cost j = cost k
  · simp only [he, sub_self, mul_zero, Real.exp_zero, mul_one]
    exact tendsto_const_nhds
  · have hlt : cost i + cost j - cost k < 0 := by
      have hw := hweight i j k hz
      exact sub_neg.mpr (lt_of_le_of_ne hw he)
    have ht := Real.tendsto_exp_atBot.comp ((tendsto_mul_const_atBot_of_neg hlt).mpr tendsto_id)
    simpa [he, Function.comp_def] using ht.const_mul (b.repr ⁅b i, b j⁆ k)

/-- Convergence holds in the finite-dimensional normed space of bilinear
maps, so polynomial expressions in the group law converge on compacts. -/
theorem basisBracket_rescale_tendsto
    (b : Basis (Fin n) ℝ L) (cost : Fin n → ℝ)
    (hweight : ∀ i j k, b.repr ⁅b i, b j⁆ k ≠ 0 → cost i + cost j ≤ cost k) :
    Tendsto (fun r : ℝ => basisBracket (exponentialRescaleBasis b cost r)) atTop
      (𝓝 (gradedCoordinateBracket b cost)) := by
  let : ContinuousAdd ((Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) :=
    @IsTopologicalAddGroup.toContinuousAdd
      ((Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] (Fin n → ℝ))
      inferInstance inferInstance inferInstance
  simp_rw [basisBracket_eq_coordinate_sum]
  unfold gradedCoordinateBracket
  apply tendsto_finsetSum
  intro i _
  apply tendsto_finsetSum
  intro j _
  apply tendsto_finsetSum
  intro k _
  exact (rescaled_structureCoefficient_tendsto b cost hweight i j k).smul tendsto_const_nhds

/-- The limiting bilinear operation satisfies the Lie identities. -/
theorem isLieBracket_gradedCoordinateBracket
    (b : Basis (Fin n) ℝ L) (cost : Fin n → ℝ)
    (hweight : ∀ i j k, b.repr ⁅b i, b j⁆ k ≠ 0 → cost i + cost j ≤ cost k) :
    IsLieBracket (gradedCoordinateBracket b cost) :=
  isClosed_setOf_isLieBracket.mem_of_tendsto (basisBracket_rescale_tendsto b cost hweight)
    (Eventually.of_forall (fun _ => isLieBracket_basisBracket _))

variable {I : Type} [Fintype I] [DecidableEq I]

/-- Maximality of the word-basis weight gives exactly the filtration
inequality on every nonzero structure constant. -/
theorem maximizing_word_basis_bracket_weight
    (X : I → L) {k : ℕ} (hk : lowerCentralSeries ℝ L L k = ⊥)
    (b₀ : Basis (Fin (finrank ℝ L)) ℝ L) (s : I → ℝ)
    (β : WordBasisSelections X (boundedBracketWords k))
    (hβ : IsMaximizingColumnBasis (wordListCoordinates X (boundedBracketWords k) b₀)
      (fun w => bracketWordExponent s w) β.val)
    (i j l : Fin (finrank ℝ L))
    (hnz : (WordBasisSelections.basis X (boundedBracketWords k) β).repr
      ⁅WordBasisSelections.basis X (boundedBracketWords k) β i,
        WordBasisSelections.basis X (boundedBracketWords k) β j⁆ l ≠ 0) :
    bracketWordExponent s (β.val i) + bracketWordExponent s (β.val j) ≤
      bracketWordExponent s (β.val l) := by
  let S := boundedBracketWords (I := I) k
  let b := WordBasisSelections.basis X S β
  have hbr : ⁅b i, b j⁆ ≠ 0 := by
    intro hz
    exact hnz (by change b.repr ⁅b i, b j⁆ l = 0; rw [hz]; simp)
  let w : S := ⟨(β.val i : FreeMagma I) * β.val j, by
    apply (mem_boundedBracketWords _ _).mpr
    by_contra hn
    have hh := evalBracketWord_eq_zero_of_depth X hk
      ((β.val i : FreeMagma I) * β.val j) (Nat.le_of_not_lt hn)
    have he : evalBracketWord X ((β.val i : FreeMagma I) * β.val j) = ⁅b i, b j⁆ := by
      rw [evalBracketWord_mul]
      exact congrArg₂ (fun x y : L => ⁅x, y⁆)
        (WordBasisSelections.eval_words X S β i) (WordBasisSelections.eval_words X S β j)
    exact hbr (he.symm.trans hh)⟩
  have he : evalBracketWord X w = ⁅b i, b j⁆ := by
    change ⁅evalBracketWord X (β.val i), evalBracketWord X (β.val j)⁆ = _
    exact congrArg₂ (fun x y : L => ⁅x, y⁆)
      (WordBasisSelections.eval_words X S β i) (WordBasisSelections.eval_words X S β j)
  have hc : columnCoordinates (wordListCoordinates X S b₀) β.val w l = b.repr ⁅b i, b j⁆ l := by
    rw [columnCoordinates_eq_wordBasis_repr, he]
    rfl
  have hw := weight_le_of_nonzero_coordinate (wordListCoordinates X S b₀)
    (fun w => bracketWordExponent s w) β.val hβ w l
    (columnCoordinates (wordListCoordinates X S b₀) β.val w)
    (columnCoordinates_repr _ _ hβ.1 w) (by rw [hc]; exact hnz)
  simpa only [w, bracketWordExponent_mul] using hw

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_GradedGeneratorLimit
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.PolynomialCoordinateGroup.instBorelSpace _root_.OAI.PolycyclicRecognition.PolynomialCoordinateGroup.instGroup _root_.OAI.PolycyclicRecognition.PolynomialCoordinateGroup.instMeasurableSpace _root_.OAI.PolycyclicRecognition.PolynomialCoordinateGroup.instTopologicalSpace _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_nonempty _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.CartanFactorModel.realScaleProfile_apply _root_.OAI.PolycyclicRecognition.exponentialRescaleBasis_zero _root_.OAI.PolycyclicRecognition.gradedGeneratorMap_apply _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Generating vectors and group laws survive the graded limit -/

noncomputable section

namespace PolycyclicRecognition

open Module LieModule Filter
open scoped Topology

variable {L I : Type} [LieRing L] [LieAlgebra ℝ L] [Fintype I] [DecidableEq I]

theorem rescaled_generator_tendsto
    {n : ℕ} (b : Basis (Fin n) ℝ L) (cost : Fin n → ℝ) (s : ℝ) (x : L)
    (hweight : ∀ j, b.repr x j ≠ 0 → s ≤ cost j) :
    Tendsto (fun r : ℝ => (exponentialRescaleBasis b cost r).equivFun
      (Real.exp (r * s) • x)) atTop (𝓝 (gradedGenerator b cost s x)) := by
  apply tendsto_pi_nhds.mpr
  intro j
  change Tendsto (fun r : ℝ => (exponentialRescaleBasis b cost r).repr
    (Real.exp (r * s) • x) j) atTop (𝓝 (if s = cost j then b.repr x j else 0))
  simp_rw [repr_exponentialRescaleBasis_smul]
  by_cases hz : b.repr x j = 0
  · simp only [hz, zero_mul, ite_self]
    exact tendsto_const_nhds
  by_cases he : s = cost j
  · simp only [he, sub_self, mul_zero, Real.exp_zero, mul_one]
    exact tendsto_const_nhds
  · have hlt : s - cost j < 0 := sub_neg.mpr (lt_of_le_of_ne (hweight j hz) he)
    have ht := Real.tendsto_exp_atBot.comp ((tendsto_mul_const_atBot_of_neg hlt).mpr tendsto_id)
    simpa [he, Function.comp_def] using ht.const_mul (b.repr x j)

/-- Basis maximality prevents a generator from having a nonzero coordinate
of lower degree. -/
theorem maximizing_word_basis_letter_weight
    (X : I → L) (S : Finset (FreeMagma I)) (hletters : ∀ i, FreeMagma.of i ∈ S)
    (b₀ : Basis (Fin (finrank ℝ L)) ℝ L) (s : I → ℝ)
    (β : WordBasisSelections X S)
    (hβ : IsMaximizingColumnBasis (wordListCoordinates X S b₀)
      (fun w => bracketWordExponent s w) β.val)
    (i : I) (j : Fin (finrank ℝ L))
    (hnz : (WordBasisSelections.basis X S β).repr (X i) j ≠ 0) :
    s i ≤ bracketWordExponent s (β.val j) := by
  let w : S := ⟨.of i, hletters i⟩
  have hc : columnCoordinates (wordListCoordinates X S b₀) β.val w j =
      (WordBasisSelections.basis X S β).repr (X i) j := by
    rw [columnCoordinates_eq_wordBasis_repr]
    rfl
  have hw := weight_le_of_nonzero_coordinate (wordListCoordinates X S b₀)
    (fun w => bracketWordExponent s w) β.val hβ w j
    (columnCoordinates (wordListCoordinates X S b₀) β.val w)
    (columnCoordinates_repr _ _ hβ.1 w) (by rw [hc]; exact hnz)
  simpa only [w, bracketWordExponent_of] using hw

/-- The actual rescaled bracket and all actual generators converge together. -/
theorem rescaledLieData_tendsto_graded
    (X : I → L) {k : ℕ} (hk : lowerCentralSeries ℝ L L k = ⊥)
    (hletters : ∀ i : I, FreeMagma.of i ∈ boundedBracketWords k)
    (b₀ : Basis (Fin (finrank ℝ L)) ℝ L) (s : I → ℝ)
    (β : WordBasisSelections X (boundedBracketWords k))
    (hβ : IsMaximizingColumnBasis (wordListCoordinates X (boundedBracketWords k) b₀)
      (fun w => bracketWordExponent s w) β.val) :
    let b := WordBasisSelections.basis X (boundedBracketWords k) β
    let cost := fun j => bracketWordExponent s (β.val j)
    Tendsto (rescaledLieData X (boundedBracketWords k) β s) atTop
      (𝓝 (gradedCoordinateBracket b cost, fun i => gradedGenerator b cost (s i) (X i))) := by
  dsimp only
  apply Tendsto.prodMk_nhds
  · exact basisBracket_rescale_tendsto _ _ (maximizing_word_basis_bracket_weight X hk b₀ s β hβ)
  · apply tendsto_pi_nhds.mpr
    intro i
    exact rescaled_generator_tendsto _ _ _ _
      (maximizing_word_basis_letter_weight X _ hletters b₀ s β hβ i)

/-- Every selected bracket word still evaluates to its coordinate unit in
the graded limit. Thus the limiting generators span the whole Lie algebra
under brackets; the limit has not lost any directions. -/
theorem graded_generators_word_normalization
    (X : I → L) {k : ℕ} (hk : lowerCentralSeries ℝ L L k = ⊥)
    (hletters : ∀ i : I, FreeMagma.of i ∈ boundedBracketWords k)
    (b₀ : Basis (Fin (finrank ℝ L)) ℝ L) (s : I → ℝ)
    (β : WordBasisSelections X (boundedBracketWords k))
    (hβ : IsMaximizingColumnBasis (wordListCoordinates X (boundedBracketWords k) b₀)
      (fun w => bracketWordExponent s w) β.val) :
    let b := WordBasisSelections.basis X (boundedBracketWords k) β
    let cost := fun j => bracketWordExponent s (β.val j)
    ∀ j, evalBilinearWord (gradedCoordinateBracket b cost)
      (fun i => gradedGenerator b cost (s i) (X i)) (β.val j) = Pi.single j 1 := by
  exact (isClosed_wordNormalizations (fun j => (β.val j : FreeMagma I))
    (fun j => (Pi.single j (1 : ℝ) : Fin (finrank ℝ L) → ℝ))).mem_of_tendsto
      (rescaledLieData_tendsto_graded X hk hletters b₀ s β hβ)
      (Eventually.of_forall (fun r => rescaledLieData_word X _ β s r))

/-- The fixed finite Dynkin product retains its exact group and straight-line
one-parameter identities in the limiting coordinate law. -/
theorem gradedCoordinateBracket_groupLaws
    {G : Type} [Group G] {n c : ℕ} (b : Basis (Fin n) ℝ L) (cost : Fin n → ℝ)
    (hweight : ∀ i j k, b.repr ⁅b i, b j⁆ k ≠ 0 → cost i + cost j ≤ cost k)
    (Exp : L → G) (hinj : Function.Injective Exp)
    (hzero : Exp 0 = 1) (hneg : ∀ x, Exp (-x) = (Exp x)⁻¹)
    (hadd : ∀ x (s t : ℝ), Exp ((s + t) • x) = Exp (s • x) * Exp (t • x))
    (a : DynkinCoefficients c 2)
    (hm : ∀ x y, Exp (finiteDynkinPolynomial a ![x, y]) = Exp x * Exp y) :
    PolynomialGroupLaws (dynkinProduct a (gradedCoordinateBracket b cost)) :=
  (isClosed_dynkinGroupLaws a).mem_of_tendsto (basisBracket_rescale_tendsto b cost hweight)
    (Eventually.of_forall (fun r =>
      basis_polynomialGroupLaws (exponentialRescaleBasis b cost r) Exp hinj hzero hneg hadd a hm))

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_PolynomialChartCoordinates
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.CartanFactorModel.realScaleProfile_apply _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial logarithm bounds for the actual scaled coordinate charts -/

noncomputable section

namespace PolycyclicRecognition

open Module
open scoped BigOperators

/-- Unit letter weights give the ordinary bracket length. -/
theorem bracketWordExponent_one {I : Type} [Fintype I] [DecidableEq I]
    (w : FreeMagma I) : bracketWordExponent (fun _ => 1) w = bracketWordLength w := by
  induction w using FreeMagma.rec with
  | of i => simp [bracketWordLength]
  | mul u v hu hv =>
      change bracketWordExponent (fun _ => 1) (u * v) = _
      rw [bracketWordExponent_mul, hu, hv]
      simp only [bracketWordLength, Nat.cast_add]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_WordChartHeight
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact height scaling in nilpotent word charts -/

noncomputable section

namespace PolycyclicRecognition

open Module
open scoped BigOperators

/-- A linear height that kills brackets scales exactly in the word-length
chart. This is independent of a choice of graded limit: all nontrivial
bracket words have zero height, while each letter has weight one. -/
theorem word_length_chart_height
    {I L W : Type} [Fintype I] [DecidableEq I]
    [LieRing L] [LieAlgebra ℝ L] [AddCommGroup W] [Module ℝ W]
    (X : I → L) (S : Finset (FreeMagma I)) (β : WordBasisSelections X S)
    (h : L →ₗ[ℝ] W) (hbracket : ∀ x y : L, h ⁅x, y⁆ = 0)
    {r : ℝ} (hr : 0 < r) (z : Fin (finrank ℝ L) → ℝ) :
    h ((exponentialRescaleBasis (WordBasisSelections.basis X S β)
      (fun j => (bracketWordLength (β.val j : FreeMagma I) : ℝ)) (Real.log r)).equivFun.symm z) =
      r • h ((WordBasisSelections.basis X S β).equivFun.symm z) := by
  let b := WordBasisSelections.basis X S β
  let br := exponentialRescaleBasis b
    (fun j => (bracketWordLength (β.val j : FreeMagma I) : ℝ)) (Real.log r)
  have hb (j : Fin (finrank ℝ L)) : h (br j) = r • h (b j) := by
    simp only [br, exponentialRescaleBasis, Basis.unitsSMul_apply,
      Units.smul_def, Units.val_mk0, map_smul]
    have he := WordBasisSelections.eval_words X S β j
    change evalBracketWord X (β.val j) = b j at he
    rw [← he]
    cases hw : (β.val j : FreeMagma I) with
    | of i => simp only [bracketWordLength, Nat.cast_one, mul_one, Real.exp_log hr]
    | mul u v =>
        change Real.exp (Real.log r * (bracketWordLength (u * v) : ℝ)) •
          h ⁅evalBracketWord X u, evalBracketWord X v⁆ =
            r • h ⁅evalBracketWord X u, evalBracketWord X v⁆
        rw [hbracket, smul_zero, smul_zero]
  change h (br.equivFun.symm z) = r • h (b.equivFun.symm z)
  rw [Basis.equivFun_symm_apply, map_sum, Basis.equivFun_symm_apply, map_sum,
    Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [map_smul, map_smul, hb, smul_comm]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_GradedHorizontalStructure
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_nonempty _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.CartanFactorModel.realScaleProfile_apply _root_.OAI.PolycyclicRecognition.bracketWordDifferential_mul _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The horizontal projection and conjugation law of the graded limit -/

noncomputable section
namespace PolycyclicRecognition

open Module Filter
open scoped Topology BigOperators

/-- A height that vanishes on brackets is unchanged by the horizontal
projection in a basis made of unit-cost words. -/
theorem gradedGenerator_word_height
    {L W I : Type} [LieRing L] [LieAlgebra ℝ L]
    [AddCommGroup W] [Module ℝ W] [Fintype I] [DecidableEq I]
    (X : I → L) (S : Finset (FreeMagma I)) (β : WordBasisSelections X S)
    (h : L →ₗ[ℝ] W) (hh : ∀ x y : L, h ⁅x, y⁆ = 0) (v : L) :
    let b := WordBasisSelections.basis X S β
    let cost := fun j => bracketWordExponent (fun _ : I => 1) (β.val j)
    h (b.equivFun.symm (gradedGenerator b cost 1 v)) = h v := by
  dsimp only
  let b := WordBasisSelections.basis X S β
  let cost := fun j => bracketWordExponent (fun _ : I => 1) (β.val j)
  have hhigh (j : Fin (finrank ℝ L)) (hj : (1 : ℝ) ≠ cost j) : h (b j) = 0 := by
    rw [← WordBasisSelections.eval_words X S β j]
    change h (evalBracketWord X (β.val j)) = 0
    cases hw : (β.val j : FreeMagma I) with
    | of i => exact (hj (by simp [cost, hw])).elim
    | mul u w => exact hh _ _
  conv_rhs => rw [← b.equivFun.symm_apply_apply v]
  rw [Basis.equivFun_symm_apply, Basis.equivFun_symm_apply, map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro j _
  simp only [map_smul]
  change (if (1 : ℝ) = cost j then b.repr v j else 0) • h (b j) = b.repr v j • h (b j)
  by_cases hj : (1 : ℝ) = cost j
  · rw [ite_eq_left hj]
  · rw [ite_eq_right hj, hhigh j hj, smul_zero, smul_zero]

attribute [local instance 100] LieRing.ofAssociativeRing

/-- The actual representation-derived conjugation identity is closed under
the graded rescaling. -/
theorem graded_exponentialConjugationLaw
    {L G A : Type} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
    [Group G] [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
    {n c : ℕ} (b : Basis (Fin n) ℝ L) (cost : Fin n → ℝ)
    (hweight : ∀ i j k, b.repr ⁅b i, b j⁆ k ≠ 0 → cost i + cost j ≤ cost k)
    (Exp : L → G) (hinj : Function.Injective Exp)
    (hneg : ∀ x, Exp (-x) = (Exp x)⁻¹)
    (a : DynkinCoefficients c 2)
    (hm : ∀ x y, Exp (finiteDynkinPolynomial a ![x, y]) = Exp x * Exp y)
    (j : L →ₗ⁅ℝ⁆ A) (ρ : G →* Aˣ) (hρ : Function.Injective ρ)
    (hmatch : ∀ x, ρ (Exp x) = algebraExpUnit (j x)) :
    ExponentialConjugationLaw (dynkinProduct a (gradedCoordinateBracket b cost))
      (gradedCoordinateBracket b cost) := by
  exact (isClosed_exponentialConjugationLaw a).mem_of_tendsto
    (basisBracket_rescale_tendsto b cost hweight)
    (Eventually.of_forall fun r => basis_exponentialConjugationLaw
      (exponentialRescaleBasis b cost r) Exp hinj hneg a hm j ρ hρ hmatch)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_MappedBasisBrackets
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Coordinate bracket preservation under a Lie-algebra identification -/

namespace PolycyclicRecognition

open Module

/-- Mapping both the vectors and their basis leaves the coordinate Lie
bracket unchanged. -/
theorem basisBracket_map_lieEquiv
    {L L' : Type} [LieRing L] [LieAlgebra ℝ L] [LieRing L'] [LieAlgebra ℝ L']
    {n : ℕ} (b : Basis (Fin n) ℝ L) (e : L ≃ₗ⁅ℝ⁆ L') :
    basisBracket (b.map e.toLinearEquiv) = basisBracket b := by
  apply ContinuousLinearMap.ext
  intro x
  apply ContinuousLinearMap.ext
  intro y
  simp only [basisBracket_apply, Basis.map_equivFun]
  change b.equivFun (e.symm ⁅e (b.equivFun.symm x), e (b.equivFun.symm y)⁆) = _
  rw [← e.map_lie, e.symm_apply_apply]

end PolycyclicRecognition

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_ExponentialRightHaar
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Right invariance of exponential-coordinate Haar measure

Negation preserves coordinate Lebesgue measure and corresponds to group
inversion. Thus the exponential-coordinate left Haar measure is also right
invariant, without a separate group nilpotence assertion.
-/

noncomputable section

namespace PolycyclicRecognition

open MeasureTheory

/-- Pull right translation back through the actual coordinate equivalence. -/
theorem coordinate_right_translation_preserving
    {V G : Type} [MeasurableSpace V] [Group G] [MeasurableSpace G]
    [MeasurableMul G] (ν : Measure V) (μ : Measure G) [μ.IsMulRightInvariant]
    (e : V ≃ᵐ G) (he : Measure.map e ν = μ)
    (m : V → V → V) (hm : ∀ x y, e (m x y) = e x * e y) (q : V) :
    MeasurePreserving (fun x => m x q) ν ν := by
  have hp : MeasurePreserving e ν μ := ⟨e.measurable, he⟩
  have h := (hp.symm e).comp ((measurePreserving_mul_right μ (e q)).comp hp)
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  funext x
  exact (e.symm_apply_eq.mpr (hm x q).symm).symm

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_BasisDynkinHaar
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_countable _root_.OAI.PolycyclicRecognition.finitelyGeneratedSubgroupIndex_countable _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.basisDynkinParameter_zero _root_.OAI.PolycyclicRecognition.chartExponentialFlow_zero _root_.OAI.PolycyclicRecognition.derivationSemidirectHom_apply _root_.OAI.PolycyclicRecognition.dynkinRightTranslation_apply _root_.OAI.PolycyclicRecognition.dynkinRightTranslation_symm_apply _root_.OAI.PolycyclicRecognition.exponentialHomOfDynkin_apply_exp _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Lebesgue invariance of actual rescaled Dynkin translations

Every coordinate basis is allowed. Hence the lemma applies directly to the
scale-dependent maximizing bases used by the occupation measures.
-/

noncomputable section

namespace PolycyclicRecognition

open MeasureTheory Module
open scoped Manifold

/-- The actual exponential-coordinate multiplication preserves coordinate
Lebesgue measure under right translations, in every basis. -/
theorem measurePreserving_basis_dynkin_right
    {E G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace G] [ChartedSpace E G] [Group G]
    [LieGroup (𝓘(ℝ, E)) ⊤ G] [T2Space G] [SimplyConnectedSpace G]
    [MeasurableSpace G] [BorelSpace G]
    (haar : NilpotentExponentialHaarInput E G)
    (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G) (hExp : IsGroupExponential Exp)
    (hnil : LieRing.IsNilpotent (GroupLieAlgebra (𝓘(ℝ, E)) G))
    {n c : ℕ} (b : Basis (Fin n) ℝ (GroupLieAlgebra (𝓘(ℝ, E)) G))
    (a : DynkinCoefficients c 2)
    (hm : ∀ x y, Exp (finiteDynkinPolynomial a ![x, y]) = Exp x * Exp y)
    (q : Fin n → ℝ) :
    MeasurePreserving (fun x => dynkinProduct a (basisBracket b) x q) volume volume := by
  let : IsTopologicalGroup G := topologicalGroup_of_lieGroup (𝓘(ℝ, E)) ⊤
  obtain ⟨⟨chart, hchart⟩, hhaar⟩ := haar.2 Exp hExp hnil
  let e : (Fin n → ℝ) ≃ₜ G :=
    b.equivFun.symm.toContinuousLinearEquiv.toHomeomorph.trans chart
  let : SecondCountableTopology G := e.symm.secondCountableTopology
  have he (x : Fin n → ℝ) : e x = Exp (b.equivFun.symm x) := hchart _
  have heq : (e : (Fin n → ℝ) → G) = Exp ∘ b.equivFun.symm := funext he
  let μ := Measure.map e volume
  have hμ : μ.IsHaarMeasure := by
    change (Measure.map e volume).IsHaarMeasure
    rw [heq]
    exact hhaar n b
  let := hμ
  have hneg (x : Fin n → ℝ) : e (-x) = (e x)⁻¹ := by
    rw [he, he]
    simpa using hExp.map_neg (b.equivFun.symm x)
  let : μ.IsMulRightInvariant := isMulRightInvariant_map_of_neg volume e
    e.continuous.measurable hneg
  apply coordinate_right_translation_preserving volume μ e.toMeasurableEquiv rfl
    (dynkinProduct a (basisBracket b)) _ q
  intro x y
  change e (dynkinProduct a (basisBracket b) x y) = e x * e y
  rw [he, he, he]
  have h := basis_dynkinProduct b a (b.equivFun.symm x) (b.equivFun.symm y)
  simp only [LinearEquiv.apply_symm_apply] at h
  rw [h, LinearEquiv.symm_apply_apply]
  exact hm _ _

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_SupportedProbabilityRestriction
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Viewing a supported probability as a probability on its compact support -/

noncomputable section

namespace PolycyclicRecognition

open MeasureTheory Set Filter
open scoped Topology

theorem supportedProbabilityRestriction_map
    {X : Type} [MeasurableSpace X] (μ : ProbabilityMeasure X)
    (K : Set X) (hK : MeasurableSet K) (hfull : ∀ᵐ x ∂(μ : Measure X), x ∈ K) :
    Measure.map Subtype.val (supportedProbabilityRestriction μ K hK hfull : Measure K) = μ := by
  exact (map_comap_subtype_coe hK _).trans
    (Measure.restrict_eq_self_of_ae_mem hfull)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_CellProfileRestriction
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Restricting profile samples to their actual carrying cell -/

noncomputable section
namespace PolycyclicRecognition

open MeasureTheory Filter Set
open scoped Topology

/-- Restricting a sample to a measurable set of full probability does not
change any pushed-forward profile law. -/
theorem map_supportedProbabilityRestriction
    {A X : Type} [MeasurableSpace A] [MeasurableSpace X]
    (μ : ProbabilityMeasure A) (C : Set A) (hC : MeasurableSet C)
    (hfull : ∀ᵐ a ∂(μ : Measure A), a ∈ C) (f : A → X) (hf : Measurable f) :
    ProbabilityMeasure.map (supportedProbabilityRestriction μ C hC hfull)
      (f := (fun a : C => f a.val)) (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability) = ProbabilityMeasure.map μ (f := f) (by first | exact hf.aemeasurable | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability) := by
  apply Subtype.ext
  have h := Measure.map_map (μ := (supportedProbabilityRestriction μ C hC hfull : Measure C))
    hf (measurable_subtype_coe : Measurable (Subtype.val : C → A))
  rw [supportedProbabilityRestriction_map] at h
  exact h.symm

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_CoordinateChartSampling
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The coordinate maps of the actual two-factor chart samples -/

noncomputable section

namespace PolycyclicRecognition

open Module
open scoped NNReal

/-- A Lie-algebra identification transports the same binary Dynkin formula. -/
theorem model_binary_dynkin
    {L L' N : Type} [LieRing L] [LieAlgebra ℝ L]
    [LieRing L'] [LieAlgebra ℝ L'] [Group N]
    (e : L ≃ₗ⁅ℝ⁆ L') (Exp : L' → N) {c : ℕ} (a : DynkinCoefficients c 2)
    (hm : ∀ x y, Exp (finiteDynkinPolynomial a ![x, y]) = Exp x * Exp y)
    (x y : L) :
    Exp (e (finiteDynkinPolynomial a ![x, y])) = Exp (e x) * Exp (e y) := by
  have he := congrArg Exp (finiteDynkinPolynomial_map e.toLieHom a ![x, y])
  have hv : (fun i => e.toLieHom (![x, y] i)) = ![e x, e y] := by
    funext i
    fin_cases i <;> rfl
  rw [hv] at he
  exact he.trans (hm (e x) (e y))

/-- The coordinate Dynkin product maps to the actual group product. -/
theorem exp_basis_dynkinProduct
    {L N : Type} [LieRing L] [LieAlgebra ℝ L] [Group N]
    {n c : ℕ} (b : Basis (Fin n) ℝ L) (Exp : L → N)
    (a : DynkinCoefficients c 2)
    (hm : ∀ x y, Exp (finiteDynkinPolynomial a ![x, y]) = Exp x * Exp y)
    (x y : Fin n → ℝ) :
    Exp (b.equivFun.symm (dynkinProduct a (basisBracket b) x y)) =
      Exp (b.equivFun.symm x) * Exp (b.equivFun.symm y) := by
  have h := basis_dynkinProduct b a (b.equivFun.symm x) (b.equivFun.symm y)
  simp only [LinearEquiv.apply_symm_apply] at h
  rw [h, LinearEquiv.symm_apply_apply, hm]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_BasisDerivativeField
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A finite basis assembles the actual horizontal derivative field -/

noncomputable section

namespace PolycyclicRecognition

open Set Filter MeasureTheory Module

theorem ae_eq_basisDerivativeField
    {I H G W : Type} [Fintype I] [AddCommGroup H] [Module ℝ H]
    [AddCommGroup W] [Module ℝ W] [MeasurableSpace G]
    (μ : Measure G) (Ω : Set G) (b : Basis I ℝ H) (q : H → G → W)
    (hadd : ∀ v w, ∀ᵐ g ∂μ, g ∈ Ω → q (v + w) g = q v g + q w g)
    (hsmul : ∀ (c : ℝ) v g, q (c • v) g = c • q v g) (v : H) :
    ∀ᵐ g ∂μ, g ∈ Ω → q v g = basisDerivativeField b q g v := by
  classical
  have hzero (g : G) : q 0 g = 0 := by simpa using hsmul 0 0 g
  have hsum (s : Finset I) : ∀ᵐ g ∂μ, g ∈ Ω →
      q (∑ i ∈ s, b.equivFun v i • b i) g =
        ∑ i ∈ s, b.equivFun v i • q (b i) g := by
    induction s using Finset.induction_on with
    | empty => exact Eventually.of_forall (fun g _ => by simp [hzero])
    | @insert i s hi ih =>
      filter_upwards [ih, hadd (b.equivFun v i • b i) (∑ j ∈ s, b.equivFun v j • b j)]
        with g hg ha hgΩ
      simp only [Finset.sum_insert hi]
      rw [ha hgΩ, hg hgΩ, hsmul]
  filter_upwards [hsum Finset.univ] with g hg hgΩ
  have hb : (∑ i, b.equivFun v i • b i) = v := by
    simpa only [Basis.equivFun_apply] using b.sum_repr v
  simpa only [hb, basisDerivativeField, Basis.constr_apply_fintype] using hg hgΩ

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_HorizontalLinearDerivative
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual almost-everywhere linear horizontal derivative -/

noncomputable section

namespace PolycyclicRecognition

open Set Filter MeasureTheory Module
open scoped NNReal ContDiff

theorem ae_horizontal_hasDerivAt_basisField
    {I H V W : Type} [Fintype I]
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
    (m : V → V → V) (hg : PolynomialGroupLaws m)
    (hm : ContDiff ℝ ∞ (fun z : V × V => m z.1 z.2))
    (μ : Measure (PolynomialCoordinateGroup m hg))
    [SFinite μ] [IsFiniteMeasureOnCompacts μ] [μ.IsMulRightInvariant]
    (f : V → W) (hf : Continuous f) (Ω : Set V) (hΩ : IsOpen Ω)
    (D : H →L[ℝ] V) (b : Basis I ℝ H) (C : H → ℝ≥0)
    (hlip : ∀ v g, LipschitzOnWith (C v) (fun t : ℝ => f (m g (t • D v)))
      {t | m g (t • D v) ∈ Ω}) (v : H) :
    ∀ᵐ (g : V) ∂μ, g ∈ Ω →
      HasDerivAt (fun t : ℝ => f (m g (t • D v)))
        (basisDerivativeField b (fun u => coordinateFlowDeriv m f (D u)) g v) 0 := by
  have hrepr := ae_eq_basisDerivativeField (show Measure V from μ) Ω b
    (fun u => coordinateFlowDeriv m f (D u))
    (ae_horizontalFlowDeriv_add m hg hm μ f hf Ω hΩ D C hlip)
    (fun c u g => by
      simpa only [map_smul] using coordinateFlowDeriv_smul m f c (D u) g) v
  let G := PolynomialCoordinateGroup m hg
  let e : V ≃ₜ G := PolynomialCoordinateGroup.expHomeomorph m hg
  let : IsTopologicalGroup G := PolynomialCoordinateGroup.isTopologicalGroup m hg hm.continuous
  let : SecondCountableTopology G := e.symm.isOpenEmbedding.secondCountableTopology
  have hd : ∀ᵐ (g : V) ∂μ, g ∈ Ω → HasDerivAt (fun t : ℝ => f (m g (t • D v)))
      (coordinateFlowDeriv m f (D v) g) 0 := by
    exact ae_hasDerivAt_flowDeriv (G := G) μ e e.continuous
      (PolynomialCoordinateGroup.exp_add_smul m hg) (D v) f hf Ω hΩ (C v) (hlip v)
  filter_upwards [hrepr, hd] with g hg hdg hgΩ
  exact (hdg hgΩ).congr_deriv (hg hgΩ)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_DenseConvexConstraints
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite convex-orbit constraints extend from dense directions -/

noncomputable section

namespace PolycyclicRecognition

open Set Filter
open scoped Topology

theorem isClosed_mem_finite_convexHull
    {X W I : Type} [TopologicalSpace X] [Finite I]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (f : X → W) (hf : Continuous f) (A : I → X → W) (hA : ∀ i, Continuous (A i)) :
    IsClosed {x | f x ∈ convexHull ℝ (range fun i => A i x)} := by
  rw [← isOpen_compl_iff]
  apply isOpen_iff_mem_nhds.mpr
  intro x hx
  obtain ⟨l, r, hr, hx'⟩ := geometric_hahn_banach_closed_point
    (convex_convexHull ℝ (range fun i => A i x))
    ((Set.finite_range (fun i => A i x)).isClosed_convexHull (𝕜 := ℝ)) hx
  have he : ∀ᶠ y in 𝓝 x, r < l (f y) :=
    (isOpen_lt continuous_const (l.continuous.comp hf)).mem_nhds hx'
  have ha : ∀ᶠ y in 𝓝 x, ∀ i, l (A i y) < r := by
    apply eventually_all.mpr
    intro i
    exact (isOpen_lt (l.continuous.comp (hA i)) continuous_const).mem_nhds
      (hr _ (subset_convexHull ℝ _ (mem_range_self i)))
  filter_upwards [he, ha] with y hy hay
  intro hmem
  have hbound : l (f y) ≤ r :=
    (convexHull_min (by rintro _ ⟨i, rfl⟩; exact (hay i).le)
      (convex_halfSpace_le l.toLinearMap.isLinear r)) hmem
  exact (not_lt_of_ge hbound) hy

theorem mem_finite_convexHull_of_dense
    {X W I : Type} [TopologicalSpace X] [Finite I]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (f : X → W) (hf : Continuous f) (A : I → X → W) (hA : ∀ i, Continuous (A i))
    {S : Set X} (hS : Dense S)
    (h : ∀ x ∈ S, f x ∈ convexHull ℝ (range fun i => A i x)) :
    ∀ x, f x ∈ convexHull ℝ (range fun i => A i x) := by
  have hsub : S ⊆ {x | f x ∈ convexHull ℝ (range fun i => A i x)} := h
  have hc := (isClosed_mem_finite_convexHull f hf A hA).closure_subset_iff.mpr hsub
  intro x
  exact hc (by rw [hS.closure_eq]; trivial)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_MeasurePreservingLimit
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_countable _root_.OAI.PolycyclicRecognition.finitelyGeneratedSubgroupIndex_countable _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Passing coordinate measure invariance to a limiting group law -/

noncomputable section

namespace PolycyclicRecognition

open Set Filter MeasureTheory
open scoped Topology ENNReal

/-- Fatou's lemma on open sets: a pointwise limit of measure preserving maps
cannot increase an outer regular target measure. -/
theorem map_le_of_measurePreserving_limit
    {X Y : Type} [MeasurableSpace X] [TopologicalSpace Y]
    [MeasurableSpace Y] [OpensMeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) [ν.OuterRegular]
    (g : X → Y) (hg : Measurable g) (gn : ℕ → X → Y)
    (hgn : ∀ n, MeasurePreserving (gn n) μ ν)
    (hlim : ∀ x, Tendsto (fun n => gn n x) atTop (𝓝 (g x))) :
    Measure.map g μ ≤ ν := by
  have hopen (U : Set Y) (hU : IsOpen U) : μ (g ⁻¹' U) ≤ ν U := by
    let χ : Y → ℝ≥0∞ := U.indicator (fun _ => 1)
    have hχ : Measurable χ := measurable_const.indicator hU.measurableSet
    have hpoint (x : X) : χ (g x) ≤ liminf (fun n => χ (gn n x)) atTop := by
      by_cases hx : g x ∈ U
      · refine le_liminf_of_le (by isBoundedDefault) ?_
        filter_upwards [(hlim x).eventually (hU.mem_nhds hx)] with n hn
        simp only [χ, indicator_of_mem hx, indicator_of_mem hn]
        exact le_rfl
      · simp only [χ, indicator_of_notMem hx, zero_le]
    calc
      μ (g ⁻¹' U) = ∫⁻ x, χ (g x) ∂μ := by
        simp only [χ, ← indicator_comp_right, Function.comp_def]
        exact (lintegral_indicator_one (hg hU.measurableSet)).symm
      _ ≤ ∫⁻ x, liminf (fun n => χ (gn n x)) atTop ∂μ := lintegral_mono hpoint
      _ ≤ liminf (fun n => ∫⁻ x, χ (gn n x) ∂μ) atTop :=
        lintegral_liminf_le (fun n => hχ.comp (hgn n).measurable)
      _ = ν U := by
        simp only [(hgn _).lintegral_comp hχ, liminf_const]
        exact lintegral_indicator_one hU.measurableSet
  apply Measure.le_iff.mpr
  intro A hA
  rw [Measure.map_apply hg hA, A.measure_eq_iInf_isOpen ν]
  exact le_iInf fun U => le_iInf fun hAU => le_iInf fun hU =>
    (measure_mono (preimage_mono hAU)).trans (hopen U hU)

/-- For homeomorphisms, applying the preceding estimate to both the map and
its inverse proves exact measure preservation of the pointwise limit. -/
theorem measurePreserving_homeomorph_limit
    {X : Type} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) [μ.OuterRegular] (e : X ≃ₜ X) (en : ℕ → X ≃ₜ X)
    (hen : ∀ n, MeasurePreserving (en n) μ μ)
    (hlim : ∀ x, Tendsto (fun n => en n x) atTop (𝓝 (e x)))
    (hlimInv : ∀ x, Tendsto (fun n => (en n).symm x) atTop (𝓝 (e.symm x))) :
    MeasurePreserving e μ μ := by
  have hforward := map_le_of_measurePreserving_limit μ μ e e.continuous.measurable
    (fun n => en n) hen hlim
  have hbackward := map_le_of_measurePreserving_limit μ μ e.symm
    e.symm.continuous.measurable (fun n => (en n).symm)
    (fun n => (hen n).symm (en n).toMeasurableEquiv) hlimInv
  refine ⟨e.continuous.measurable, le_antisymm hforward ?_⟩
  have h := Measure.map_mono hbackward e.continuous.measurable
  simpa only [Measure.map_map e.continuous.measurable e.symm.continuous.measurable,
    show (e : X → X) ∘ e.symm = id from funext e.apply_symm_apply,
    Measure.map_id] using h

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_GradedHaar
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_countable _root_.OAI.PolycyclicRecognition.finitelyGeneratedSubgroupIndex_countable _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.CartanFactorModel.realScaleProfile_apply _root_.OAI.PolycyclicRecognition.basisDynkinParameter_zero _root_.OAI.PolycyclicRecognition.chartExponentialFlow_zero _root_.OAI.PolycyclicRecognition.derivationSemidirectHom_apply _root_.OAI.PolycyclicRecognition.exponentialHomOfDynkin_apply_exp _root_.OAI.PolycyclicRecognition.exponentialRescaleBasis_zero _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Haar measure for the actual graded coordinate group -/

noncomputable section

namespace PolycyclicRecognition

open Module MeasureTheory Filter
open scoped Topology Manifold

theorem measurePreserving_graded_dynkin_right_of_rescaled
    {L G : Type} [LieRing L] [LieAlgebra ℝ L] [Group G]
    {n c : ℕ} (b : Basis (Fin n) ℝ L) (cost : Fin n → ℝ)
    (hweight : ∀ i j k, b.repr ⁅b i, b j⁆ k ≠ 0 → cost i + cost j ≤ cost k)
    (Exp : L → G) (hinj : Function.Injective Exp) (hzero : Exp 0 = 1)
    (hneg : ∀ x, Exp (-x) = (Exp x)⁻¹)
    (hadd : ∀ x (s t : ℝ), Exp ((s + t) • x) = Exp (s • x) * Exp (t • x))
    (a : DynkinCoefficients c 2)
    (hm : ∀ x y, Exp (finiteDynkinPolynomial a ![x, y]) = Exp x * Exp y)
    (hmeasure : ∀ r q, MeasurePreserving
      (fun x => dynkinProduct a (basisBracket (exponentialRescaleBasis b cost r)) x q)
      volume volume) (q : Fin n → ℝ) :
    MeasurePreserving (fun x => dynkinProduct a (gradedCoordinateBracket b cost) x q)
      volume volume := by
  let B := fun r => basisBracket (exponentialRescaleBasis b cost r)
  let B₀ := gradedCoordinateBracket b cost
  let hg := gradedCoordinateBracket_groupLaws b cost hweight Exp hinj hzero hneg hadd a hm
  let hgr := fun r => basis_polynomialGroupLaws
    (exponentialRescaleBasis b cost r) Exp hinj hzero hneg hadd a hm
  have hB : Tendsto (fun k : ℕ => B k) atTop (𝓝 B₀) :=
    (basisBracket_rescale_tendsto b cost hweight).comp tendsto_natCast_atTop_atTop
  have hlim (x y : Fin n → ℝ) :
      Tendsto (fun k : ℕ => dynkinProduct a (B k) x y) atTop
        (𝓝 (dynkinProduct a B₀ x y)) := by
    exact ((continuous_dynkinProduct a id (fun _ => x) (fun _ => y)
      continuous_id continuous_const continuous_const).tendsto B₀).comp hB
  exact measurePreserving_homeomorph_limit volume (dynkinRightTranslation a B₀ hg q)
    (fun k => dynkinRightTranslation a (B k) (hgr k) q)
    (fun k => hmeasure k q) (fun x => hlim x q) (fun x => hlim x (-q))

/-- The published exponential-Haar input gives the finite-scale invariance;
the limiting invariance follows from the actual rescaled brackets. -/
theorem measurePreserving_model_graded_dynkin_right
    {L : Type} [LieRing L] [LieAlgebra ℝ L]
    {E G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace G] [ChartedSpace E G] [Group G]
    [LieGroup (𝓘(ℝ, E)) ⊤ G] [T2Space G] [SimplyConnectedSpace G]
    [MeasurableSpace G] [BorelSpace G]
    (e : L ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, E)) G)
    (haar : NilpotentExponentialHaarInput E G)
    (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G) (hExp : IsGroupExponential Exp)
    (hnil : LieRing.IsNilpotent L) {n c : ℕ} (b : Basis (Fin n) ℝ L)
    (cost : Fin n → ℝ)
    (hweight : ∀ i j k, b.repr ⁅b i, b j⁆ k ≠ 0 → cost i + cost j ≤ cost k)
    (a : DynkinCoefficients c 2)
    (hm : ∀ x y, Exp (finiteDynkinPolynomial a ![x, y]) = Exp x * Exp y)
    (q : Fin n → ℝ) :
    MeasurePreserving (fun x => dynkinProduct a (gradedCoordinateBracket b cost) x q)
      volume volume := by
  have hnilG := e.nilpotent_iff_equiv_nilpotent.mp hnil
  obtain ⟨⟨chart, hchart⟩, _⟩ := haar.2 Exp hExp hnilG
  have hinj : Function.Injective Exp := by
    have he : Exp = chart := funext fun x => (hchart x).symm
    rw [he]
    exact chart.injective
  apply measurePreserving_graded_dynkin_right_of_rescaled b cost hweight
    (Exp ∘ e) (hinj.comp e.injective) (by simpa using hExp.map_zero)
    (fun x => by simpa using hExp.map_neg (e x))
    (fun x s t => by simpa using hExp.map_add_smul (e x) s t) a
    (model_binary_dynkin e Exp a hm) ?_ q
  intro r z
  have hp := measurePreserving_basis_dynkin_right haar Exp hExp hnilG
    ((exponentialRescaleBasis b cost r).map e.toLinearEquiv) a hm z
  simpa only [basisBracket_map_lieEquiv] using hp

/-- Lebesgue measure in polynomial exponential coordinates is Haar once
right translations preserve it. Inversion is coordinate negation. -/
theorem polynomialCoordinate_haar_of_right_translations
    {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasureSpace V] [BorelSpace V]
    [(volume : Measure V).IsAddHaarMeasure]
    (m : V → V → V) (h : PolynomialGroupLaws m)
    (hc : Continuous (fun p : V × V => m p.1 p.2))
    (hm : ∀ q, MeasurePreserving (fun x => m x q) volume volume) :
    let e := PolynomialCoordinateGroup.expHomeomorph m h
    let μ := Measure.map e volume
    μ.IsHaarMeasure ∧ μ.IsMulRightInvariant := by
  let G := PolynomialCoordinateGroup m h
  let e := PolynomialCoordinateGroup.expHomeomorph m h
  let μ := Measure.map e volume
  let : IsTopologicalGroup G := PolynomialCoordinateGroup.isTopologicalGroup m h hc
  have hp : MeasurePreserving e volume μ := ⟨e.continuous.measurable, rfl⟩
  have hr : μ.IsMulRightInvariant := by
    constructor
    intro q
    have he : (fun x : V => e (m x (e.symm q))) = (fun g : G => g * q) ∘ e := by
      funext x
      change m x (e.symm q) = m x q
      rfl
    have hh := hp.comp (hm (e.symm q))
    have hhmap := hh.map_eq
    change Measure.map (fun x => e (m x (e.symm q))) volume = μ at hhmap
    rw [he, ← Measure.map_map (measurable_mul_const q) e.continuous.measurable] at hhmap
    exact hhmap
  let : μ.IsMulRightInvariant := hr
  let : μ.IsInvInvariant := isInvInvariant_map_of_neg volume e e.continuous.measurable
    (fun _ => rfl)
  have hi : μ.inv = μ := Measure.inv_eq_self μ
  have hl : μ.IsMulLeftInvariant := by
    rw [← hi]
    first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
  let : μ.IsMulLeftInvariant := hl
  let : IsFiniteMeasureOnCompacts μ := Measure.IsFiniteMeasureOnCompacts.map volume e
  let : μ.IsOpenPosMeasure := e.continuous.isOpenPosMeasure_map e.surjective
  exact ⟨{}, hr⟩

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_ProfileDerivativeLabel
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteRootOffsetConeIndex _root_.OAI.PolycyclicRecognition.instNonemptyRootOffsetConeIndex _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Infinitesimal profile constraints give a finite height-symmetry label -/

noncomputable section

namespace PolycyclicRecognition

open Module Set

/-- A horizontal linear derivative factors through height and is a support
isometry once the convex-increment and segment-volume inequalities hold.
This first step lands in the full isometry group of the segment norm. -/
theorem derivative_eq_support_symmetry
    {V W I B J : Type} [AddCommGroup V] [Module ℝ V]
    [AddCommGroup W] [Module ℝ W] [FiniteDimensional ℝ W]
    [Fintype I] [Fintype B] [Nonempty B]
    (D : SupportDatum W I B) (π M : V →ₗ[ℝ] W) (hπ : Function.Surjective π)
    (A : J → linearSupportSymmetryGroup D)
    (hconv : ∀ v, M v ∈ convexHull ℝ (range fun j => (A j).val (π v)))
    (hlower : ∀ v, D.segmentSupport (π v) ≤ D.segmentSupport (M v)) :
    ∃ T : linearSupportSymmetryGroup D, M = T.val.toLinearMap.comp π := by
  let : Norm W := ⟨D.segmentSupport⟩
  let core : NormedSpace.Core ℝ W := D.normCore
  let : NormedAddCommGroup W := NormedAddCommGroup.ofCore core
  let : NormedSpace ℝ W := NormedSpace.ofCore core
  have hupper (v : V) : ‖M v‖ ≤ ‖π v‖ := by
    have hball : range (fun j => (A j).val (π v)) ⊆ Metric.closedBall 0 ‖π v‖ := by
      rintro _ ⟨j, rfl⟩
      rw [Metric.mem_closedBall, dist_zero_right]
      exact ((A j).property (π v)).le
    have hh := (convexHull_min hball (convex_closedBall (0 : W) ‖π v‖)) (hconv v)
    simpa only [Metric.mem_closedBall, dist_zero_right] using hh
  have hzero (v : V) (hv : π v = 0) : M v = 0 := by
    apply norm_eq_zero.mp
    apply le_antisymm _ (norm_nonneg _)
    simpa only [hv, norm_zero] using hupper v
  obtain ⟨σ, hσ⟩ := π.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hπ)
  have hπσ (w : W) : π (σ w) = w := LinearMap.congr_fun hσ w
  let T := M.comp σ
  have hfactor (v : V) : T (π v) = M v := by
    have hh := hzero (v - σ (π v)) (by rw [map_sub, hπσ, sub_self])
    rw [map_sub] at hh
    exact (sub_eq_zero.mp hh).symm
  have hnorm (w : W) : ‖T w‖ = ‖w‖ := by
    apply le_antisymm
    · simpa only [T, LinearMap.comp_apply, hπσ] using hupper (σ w)
    · change D.segmentSupport w ≤ D.segmentSupport (M (σ w))
      simpa only [hπσ] using hlower (σ w)
  have hinj : Function.Injective T := by
    intro w u h
    apply sub_eq_zero.mp
    apply norm_eq_zero.mp
    rw [← hnorm (w - u), map_sub, h, sub_self, norm_zero]
  have hsurj : Function.Surjective T := LinearMap.surjective_of_injective hinj
  let e := LinearEquiv.ofBijective T ⟨hinj, hsurj⟩
  refine ⟨⟨e, hnorm⟩, ?_⟩
  ext v
  exact (hfactor v).symm

/-- The convex orbit constraint selects a member of the original family,
even when that family is smaller than the full segment-norm isometry group. -/
theorem derivative_eq_one_of_labels
    {V W I B J : Type} [AddCommGroup V] [Module ℝ V]
    [AddCommGroup W] [Module ℝ W] [FiniteDimensional ℝ W]
    [Fintype I] [Fintype B] [Nonempty B] [Finite J]
    (D : SupportDatum W I B) (π M : V →ₗ[ℝ] W) (hπ : Function.Surjective π)
    (A : J → linearSupportSymmetryGroup D)
    (hconv : ∀ v, M v ∈ convexHull ℝ (range fun j => (A j).val (π v)))
    (hlower : ∀ v, D.segmentSupport (π v) ≤ D.segmentSupport (M v)) :
    ∃ j, M = (A j).val.toLinearMap.comp π := by
  obtain ⟨T, hT⟩ := derivative_eq_support_symmetry D π M hπ A hconv hlower
  let Γ := linearSupportSymmetryGroup D
  let : Fintype Γ := Fintype.ofFinite Γ
  let e : W ≃ₗ[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ W)) :=
    (Module.finBasis ℝ W).equivFun.trans (WithLp.linearEquiv 2 ℝ _).symm
  have hconvW (w : W) : T.val w ∈ convexHull ℝ (range fun j => (A j).val w) := by
    obtain ⟨v, hv⟩ := hπ w
    have hh := hconv v
    rw [hT] at hh
    change T.val (π v) ∈ convexHull ℝ (range fun j => (A j).val (π v)) at hh
    rwa [hv] at hh
  obtain ⟨j, hj⟩ := exists_eq_label_of_finite_group_convex_orbit Γ e.toLinearMap
    e.injective T A hconvW
  exact ⟨j, hj ▸ hT⟩

/-- In particular, a family of template-preserving labels stays in that
same family under the infinitesimal profile argument. -/
theorem derivative_eq_one_of_template_labels
    {V W I B J : Type} [AddCommGroup V] [Module ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
    [Fintype I] [Fintype B] [Nonempty B] [Finite J]
    (D : SupportDatum W I B) (π M : V →ₗ[ℝ] W) (hπ : Function.Surjective π)
    (A : J → templateSymmetryGroup D)
    (hconv : ∀ v, M v ∈ convexHull ℝ (range fun j => (A j).val (π v)))
    (hlower : ∀ v, D.segmentSupport (π v) ≤ D.segmentSupport (M v)) :
    ∃ j, M = (A j).val.toLinearMap.comp π := by
  exact derivative_eq_one_of_labels D π M hπ
    (fun j => ⟨(A j).val, templateSymmetry_mem_linearSupportSymmetry D (A j)⟩) hconv hlower

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_SegmentIncrementDerivative
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Closed increment constraints pass to one-sided derivatives -/

namespace PolycyclicRecognition

open Set Filter
open scoped Topology

/-- Only positive short segments are needed to constrain the derivative.
The derivative limit itself supplies all required convergence. -/
theorem derivative_mem_of_short_increments
    {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W]
    (f : ℝ → W) (w : W) (hderiv : HasDerivAt f w 0)
    (S : Set W) (hS : IsClosed S) {T₀ : ℝ} (hT₀ : 0 < T₀)
    (hinc : ∀ t : ℝ, 0 < t → t < T₀ → t⁻¹ • (f t - f 0) ∈ S) : w ∈ S := by
  apply hS.mem_of_tendsto hderiv.tendsto_slope_zero_right
  have hpos : ∀ᶠ t : ℝ in 𝓝[>] 0, 0 < t := self_mem_nhdsWithin
  have hsmall : ∀ᶠ t : ℝ in 𝓝[>] 0, t < T₀ :=
    (eventually_lt_nhds hT₀).filter_mono nhdsWithin_le_nhds
  filter_upwards [hpos, hsmall] with t ht htT
  simpa only [zero_add] using hinc t ht htT

end PolycyclicRecognition

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_SegmentVolumeDerivative
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finite_templateSymmetryGroup _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteRootOffsetConeIndex _root_.OAI.PolycyclicRecognition.instFiniteSubtypeLinearEquivRealIdMemSubgroupLinearSupportSymmetryGroup _root_.OAI.PolycyclicRecognition.instNonemptyRootOffsetConeIndex _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.CartanWordModel.supportDatum_weight _root_.OAI.PolycyclicRecognition.SupportDatum.transport_weight_apply _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Differentiating the segment-volume inequality -/

noncomputable section

namespace PolycyclicRecognition.SupportDatum

open Set Filter Metric
open scoped Topology

variable {W I B : Type} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [FiniteDimensional ℝ W] [Fintype I] [Fintype B] [Nonempty B]
  (D : PolycyclicRecognition.SupportDatum W I B)

/-- Differentiability controls the whole short one-sided segment, so the
segment-volume lower bound passes to its derivative without any extra
Hausdorff-convergence hypothesis. -/
theorem le_segmentSupport_derivative
    (f : ℝ → W) (hf : Continuous f) (w : W) (hderiv : HasDerivAt f w 0)
    (p : ℝ) {T₀ : ℝ} (hT₀ : 0 < T₀)
    (hvolume : ∀ T : ℝ, 0 < T → T < T₀ → T * p ≤ D.templateSupport (f '' Icc 0 T)) :
    p ≤ D.segmentSupport w := by
  apply le_of_forall_pos_le_add
  intro η hη
  let ε := η / (D.templateSupportConstant + 1)
  have hε : 0 < ε := div_pos hη (by linarith [D.templateSupportConstant_nonneg])
  obtain ⟨δ, hδ, hsmall⟩ := Metric.eventually_nhds_iff.mp (hderiv.isLittleO.def hε)
  let T := min (δ / 2) (T₀ / 2)
  have hT : 0 < T := lt_min (half_pos hδ) (half_pos hT₀)
  have hTδ : T < δ := (min_le_left _ _).trans_lt (half_lt_self hδ)
  have hTT₀ : T < T₀ := (min_le_right _ _).trans_lt (half_lt_self hT₀)
  let E := (fun z : W => z + f 0) '' segment ℝ 0 (T • w)
  have hseg : IsCompact (segment ℝ (0 : W) (T • w)) := by
    rw [segment_eq_image]
    exact isCompact_Icc.image ((continuous_const.sub continuous_id).smul continuous_const |>.add
      (continuous_id.smul continuous_const))
  have hsegne : (segment ℝ (0 : W) (T • w)).Nonempty := by
    rw [segment_eq_image]
    exact (nonempty_Icc.mpr (by norm_num : (0 : ℝ) ≤ 1)).image _
  have hE : IsCompact E := hseg.image (continuous_id.add_const (f 0))
  have hnear : ∀ x ∈ f '' Icc 0 T, ∃ y ∈ E, ‖x - y‖ ≤ ε * T := by
    rintro x ⟨t, ht, rfl⟩
    refine ⟨t • w + f 0, ⟨t • w, ?_, rfl⟩, ?_⟩
    · rw [segment_eq_image]
      refine ⟨t / T, ⟨div_nonneg ht.1 hT.le, (div_le_one hT).mpr ht.2⟩, ?_⟩
      simp only [smul_zero, zero_add, smul_smul]
      rw [div_mul_cancel₀ _ hT.ne']
    · have htδ : dist t 0 < δ := by
        rw [dist_zero_right, Real.norm_eq_abs, abs_of_nonneg ht.1]
        exact ht.2.trans_lt hTδ
      have hh := hsmall htδ
      simp only [sub_zero, Real.norm_eq_abs, abs_of_nonneg ht.1] at hh
      have he : f t - (t • w + f 0) = f t - f 0 - t • w := by abel
      rw [he]
      exact hh.trans (mul_le_mul_of_nonneg_left ht.2 hε.le)
  have hnonempty : (f '' Icc (0 : ℝ) T).Nonempty :=
    (nonempty_Icc.mpr hT.le).image f
  have hbound := D.templateSupport_le_of_nearby (isCompact_Icc.image hf) hnonempty
    hE (mul_nonneg hε.le hT.le) hnear
  have htarget : D.templateSupport E = T * D.segmentSupport w := by
    rw [D.templateSupport_translate hseg hsegne (f 0),
      D.templateSupport_segment, D.segmentSupport_smul_of_nonneg w hT.le]
  rw [htarget] at hbound
  have hscaled := (hvolume T hT hTT₀).trans hbound
  have hdivide : p ≤ D.segmentSupport w + D.templateSupportConstant * ε := by
    apply (mul_le_mul_iff_right₀ hT).mp
    nlinarith
  apply hdivide.trans
  apply add_le_add le_rfl
  dsimp [ε]
  rw [← mul_div_assoc]
  apply (div_le_iff₀ (by linarith [D.templateSupportConstant_nonneg])).mpr
  nlinarith [D.templateSupportConstant_nonneg]

end PolycyclicRecognition.SupportDatum

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_DenseDerivativeLabels
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteRootOffsetConeIndex _root_.OAI.PolycyclicRecognition.instNonemptyRootOffsetConeIndex _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Countably many directional derivatives determine one finite label -/

noncomputable section

namespace PolycyclicRecognition

open Set Filter MeasureTheory

namespace SupportDatum

variable {W I B : Type} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [FiniteDimensional ℝ W] [Fintype I] [Fintype B] [Nonempty B]

omit [Nonempty B] in
theorem continuous_basisSupport (D : SupportDatum W I B) (b : B) :
    Continuous (D.basisSupport b) := by
  apply continuous_finsetSum
  intro i _
  exact continuous_const.mul (continuous_const.max (D.weight i).continuous_of_finiteDimensional)

theorem continuous_segmentSupport (D : SupportDatum W I B) :
    Continuous D.segmentSupport :=
  Continuous.finset_sup'_apply Finset.univ_nonempty (fun b _ => D.continuous_basisSupport b)

end SupportDatum

theorem ae_template_label_of_dense_derivatives
    {H W Z I B J : Type} [NormedAddCommGroup H] [NormedSpace ℝ H] [FiniteDimensional ℝ H]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
    [MeasurableSpace Z] [Fintype I] [Fintype B] [Nonempty B] [Finite J]
    (μ : Measure Z) (Ω : Set Z) (D : SupportDatum W I B)
    (π : H →L[ℝ] W) (hπ : Function.Surjective π)
    (A : J → templateSymmetryGroup D) (M : Z → H →ₗ[ℝ] W)
    (curve : Z → H → ℝ → W)
    (hc : ∀ z ∈ Ω, ∀ v, Continuous (curve z v))
    (S : Set H) (hSc : S.Countable) (hSd : Dense S)
    (hderiv : ∀ v ∈ S, ∀ᵐ z ∂μ, z ∈ Ω → HasDerivAt (curve z v) (M z v) 0)
    (T : Z → H → ℝ) (hT : ∀ z ∈ Ω, ∀ v ∈ S, 0 < T z v)
    (hinc : ∀ z ∈ Ω, ∀ v ∈ S, ∀ t, 0 < t → t < T z v →
      t⁻¹ • (curve z v t - curve z v 0) ∈ convexHull ℝ (range fun j => (A j).val (π v)))
    (hvol : ∀ z ∈ Ω, ∀ v ∈ S, ∀ t, 0 < t → t < T z v →
      t * D.segmentSupport (π v) ≤ D.templateSupport (curve z v '' Icc 0 t)) :
    ∀ᵐ z ∂μ, z ∈ Ω → ∃ j, M z = (A j).val.toLinearMap.comp π.toLinearMap := by
  filter_upwards [(ae_ball_iff hSc).mpr hderiv] with z hz hzΩ
  have hconvS (v : H) (hv : v ∈ S) :
      M z v ∈ convexHull ℝ (range fun j => (A j).val (π v)) := by
    apply derivative_mem_of_short_increments (curve z v) (M z v) (hz v hv hzΩ)
      (convexHull ℝ (range fun j => (A j).val (π v)))
      ((Set.finite_range _).isClosed_convexHull (𝕜 := ℝ)) (hT z hzΩ v hv)
    exact hinc z hzΩ v hv
  have hlowS (v : H) (hv : v ∈ S) : D.segmentSupport (π v) ≤ D.segmentSupport (M z v) :=
    D.le_segmentSupport_derivative (curve z v) (hc z hzΩ v) (M z v) (hz v hv hzΩ)
      (D.segmentSupport (π v)) (hT z hzΩ v hv) (hvol z hzΩ v hv)
  have hconv := mem_finite_convexHull_of_dense (M z) (M z).continuous_of_finiteDimensional
    (fun j v => (A j).val (π v))
    (fun j => (A j).val.toLinearMap.continuous_of_finiteDimensional.comp π.continuous) hSd hconvS
  have hclosed : IsClosed {v : H | D.segmentSupport (π v) ≤ D.segmentSupport (M z v)} :=
    isClosed_le (D.continuous_segmentSupport.comp π.continuous)
      (D.continuous_segmentSupport.comp (M z).continuous_of_finiteDimensional)
  have hlow (v : H) : D.segmentSupport (π v) ≤ D.segmentSupport (M z v) := by
    apply hclosed.closure_subset_iff.mpr hlowS
    rw [hSd.closure_eq]
    trivial
  exact derivative_eq_one_of_template_labels D π.toLinearMap (M z) hπ A hconv hlow

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_MeasurableDerivativeLabels
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_countable _root_.OAI.PolycyclicRecognition.finitelyGeneratedSubgroupIndex_countable _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Measurable selection of the derivative's finite label -/

noncomputable section

namespace PolycyclicRecognition

open Set MeasureTheory Module

theorem exists_measurable_countable_choice
    {Z J : Type} [MeasurableSpace Z] [MeasurableSpace J] [Countable J] [Nonempty J]
    (P : J → Z → Prop) (hP : ∀ j, MeasurableSet {z | P j z}) :
    ∃ label : Z → J, Measurable label ∧ ∀ z, (∃ j, P j z) → P (label z) z := by
  classical
  obtain ⟨e, he⟩ := exists_surjective_nat J
  have hnone : MeasurableSet {z | ¬ ∃ j, P j z} := by
    have hh : MeasurableSet (⋃ j, {z | P j z}) := MeasurableSet.iUnion hP
    convert hh.compl using 1
    all_goals try with_reducible_and_instances rfl
    ext z
    simp only [mem_iUnion, mem_ofPred_eq, mem_compl_iff]
  let Q : ℕ → Z → Prop := fun n z => P (e n) z ∨ ¬ ∃ j, P j z
  have hQ (n : ℕ) : MeasurableSet {z | Q n z} := (hP (e n)).union hnone
  have hex (z : Z) : ∃ n, Q n z := by
    by_cases hz : ∃ j, P j z
    · obtain ⟨j, hj⟩ := hz
      obtain ⟨n, hn⟩ := he j
      exact ⟨n, Or.inl (hn ▸ hj)⟩
    · exact ⟨0, Or.inr hz⟩
  refine ⟨fun z => e (Nat.find (hex z)), Measurable.find
    (fun _ => measurable_const) hQ hex, ?_⟩
  intro z hz
  exact (Nat.find_spec (hex z)).resolve_right (not_not.mpr hz)

theorem exists_measurable_basis_derivative_label
    {I H W Z J : Type} [Fintype I] [Countable J] [Nonempty J]
    [AddCommGroup H] [Module ℝ H]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
    [MeasurableSpace W] [BorelSpace W]
    [MeasurableSpace Z] [MeasurableSpace J]
    (b : Basis I ℝ H) (q : H → Z → W) (hq : ∀ i, Measurable (q (b i)))
    (A : J → H →ₗ[ℝ] W) :
    ∃ label : Z → J, Measurable label ∧ ∀ z,
      (∃ j, basisDerivativeField b q z = A j) → basisDerivativeField b q z = A (label z) := by
  classical
  let P : J → Z → Prop := fun j z => ∀ i, q (b i) z = A j (b i)
  have hP (j : J) : MeasurableSet {z | P j z} := by
    have h : MeasurableSet (⋂ i, {z | q (b i) z = A j (b i)}) :=
      MeasurableSet.iInter (fun i => measurableSet_eq_fun (hq i) measurable_const)
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    ext z
    simp only [mem_iInter, mem_ofPred_eq, P]
  obtain ⟨label, hlabel, hchoose⟩ := exists_measurable_countable_choice P hP
  refine ⟨label, hlabel, ?_⟩
  intro z hz
  have hex : ∃ j, P j z := by
    obtain ⟨j, hj⟩ := hz
    refine ⟨j, fun i => ?_⟩
    have h := LinearMap.congr_fun hj (b i)
    simpa only [basisDerivativeField, Basis.constr_basis] using h
  apply b.ext
  intro i
  simpa only [basisDerivativeField, Basis.constr_basis] using hchoose z hex i

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_HorizontalProfileLabels
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_countable _root_.OAI.PolycyclicRecognition.finitelyGeneratedSubgroupIndex_countable _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteRootOffsetConeIndex _root_.OAI.PolycyclicRecognition.instNonemptyRootOffsetConeIndex _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The two segment inequalities give actual measurable horizontal labels -/

noncomputable section

namespace PolycyclicRecognition

open Set Filter MeasureTheory Module
open scoped NNReal ContDiff

theorem exists_measurable_horizontal_profile_label
    {K H V W I B J : Type} [Fintype K]
    [NormedAddCommGroup H] [NormedSpace ℝ H] [FiniteDimensional ℝ H]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
    [MeasurableSpace W] [BorelSpace W]
    [Fintype I] [Fintype B] [Nonempty B] [Finite J] [Nonempty J] [MeasurableSpace J]
    (m : V → V → V) (hg : PolynomialGroupLaws m)
    (hm : ContDiff ℝ ∞ (fun z : V × V => m z.1 z.2))
    (μ : Measure (PolynomialCoordinateGroup m hg))
    [SFinite μ] [IsFiniteMeasureOnCompacts μ] [μ.IsMulRightInvariant]
    (f : V → W) (hf : Continuous f) (Ω : Set V) (hΩ : IsOpen Ω)
    (D : H →L[ℝ] V) (b : Basis K ℝ H) (C : H → ℝ≥0)
    (hlip : ∀ v g, LipschitzOnWith (C v) (fun t : ℝ => f (m g (t • D v)))
      {t | m g (t • D v) ∈ Ω})
    (P : SupportDatum W I B) (π : H →L[ℝ] W) (hπ : Function.Surjective π)
    (A : J → templateSymmetryGroup P)
    (T : V → H → ℝ) (hT : ∀ z ∈ Ω, ∀ v, 0 < T z v)
    (hinc : ∀ z ∈ Ω, ∀ v, ∀ t, 0 < t → t < T z v →
      t⁻¹ • (f (m z (t • D v)) - f z) ∈ convexHull ℝ (range fun j => (A j).val (π v)))
    (hvol : ∀ z ∈ Ω, ∀ v, ∀ t, 0 < t → t < T z v →
      t * P.segmentSupport (π v) ≤ P.templateSupport ((fun t : ℝ => f (m z (t • D v))) '' Icc 0 t)) :
    ∃ label : V → J, Measurable label ∧ ∀ v, ∀ᵐ (g : V) ∂μ, g ∈ Ω →
      HasDerivAt (fun t : ℝ => f (m g (t • D v))) ((A (label g)).val (π v)) 0 := by
  let q : H → V → W := fun v => coordinateFlowDeriv m f (D v)
  let M : V → H →ₗ[ℝ] W := basisDerivativeField b q
  have hd (v : H) : ∀ᵐ (g : V) ∂μ, g ∈ Ω →
      HasDerivAt (fun t : ℝ => f (m g (t • D v))) (M g v) 0 :=
    ae_horizontal_hasDerivAt_basisField m hg hm μ f hf Ω hΩ D b C hlip v
  obtain ⟨S, hSc, hSd⟩ := TopologicalSpace.exists_countable_dense H
  have ha : ∀ᵐ (g : V) ∂μ, g ∈ Ω → ∃ j, M g = (A j).val.toLinearMap.comp π.toLinearMap := by
    apply ae_template_label_of_dense_derivatives (show Measure V from μ) Ω P π hπ A M
      (fun g v t => f (m g (t • D v))) (fun _ _ _ => hf.comp (hm.continuous.comp
        (continuous_const.prodMk (continuous_id.smul continuous_const))))
      S hSc hSd (fun v _ => hd v) T (fun z hz v _ => hT z hz v)
    · intro z hz v _ t ht htT
      simpa only [zero_smul, hg.2.2.1] using hinc z hz v t ht htT
    · intro z hz v _ t ht htT
      exact hvol z hz v t ht htT
  obtain ⟨label, hlabel, hchoose⟩ := exists_measurable_basis_derivative_label b q
    (fun i => (stronglyMeasurable_coordinateFlowDeriv m hm.continuous f hf (D (b i))).measurable)
    (fun j => (A j).val.toLinearMap.comp π.toLinearMap)
  refine ⟨label, hlabel, ?_⟩
  intro v
  filter_upwards [ha, hd v] with g hg hdg hgΩ
  have he := hchoose g (hg hgΩ)
  exact (hdg hgΩ).congr_deriv (LinearMap.congr_fun he v)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_ProfileAffinityCriterion
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteRootOffsetConeIndex _root_.OAI.PolycyclicRecognition.instNonemptyRootOffsetConeIndex _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The deterministic affinity criterion from the two segment inequalities -/

noncomputable section

namespace PolycyclicRecognition

open Set Filter MeasureTheory Module
open scoped NNReal ContDiff Topology

theorem affine_profile_of_segment_inequalities
    {H V W I B K J N L : Type}
    [NormedAddCommGroup H] [NormedSpace ℝ H] [FiniteDimensional ℝ H] [Fintype N]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V]
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
    [MeasurableSpace W] [BorelSpace W]
    [Fintype I] [Fintype B] [Nonempty B]
    [Fintype L] [Nonempty L] [MeasurableSpace L] [MeasurableSingletonClass L]
    {c : ℕ} (a : DynkinCoefficients c 2) (br : V →L[ℝ] V →L[ℝ] V)
    (hbr : IsLieBracket br) (hg : PolynomialGroupLaws (dynkinProduct a br))
    (hc : ExponentialConjugationLaw (dynkinProduct a br) br)
    (D : H →L[ℝ] V) (bH : Basis N ℝ H)
    (X : K → H) (b₀ : Basis J ℝ V) (w₀ : J → FreeMagma K)
    (hw₀ : ∀ j, evalBilinearWord br (fun k => D (X k)) (w₀ j) = b₀ j)
    (μ : Measure (PolynomialCoordinateGroup (dynkinProduct a br) hg))
    [μ.IsHaarMeasure] [μ.IsMulRightInvariant]
    (Ω : Set (PolynomialCoordinateGroup (dynkinProduct a br) hg)) (hΩ : IsOpen Ω) (hconn : IsPreconnected Ω) (hne : Ω.Nonempty)
    (f : V → W) (hf : Continuous f)
    (π : PolynomialCoordinateGroup (dynkinProduct a br) hg →* Multiplicative W)
    (p : V →L[ℝ] W) (hp : Function.Surjective (p.comp D))
    (hπExp : ∀ v, (π (PolynomialCoordinateGroup.exp _ hg v)).toAdd = p v)
    (P : SupportDatum W I B) (hweights : ∀ i, P.weight i ≠ 0)
    (σ : I → Bool) (hσ : (weightChamber (fun i => (P.weight i).toContinuousLinearMap) σ).Nonempty)
    (A : L → templateSymmetryGroup P) (C : H → ℝ≥0)
    (hlip : ∀ v g, LipschitzOnWith (C v)
      (fun t : ℝ => f (dynkinProduct a br g (t • D v)))
      {t | dynkinProduct a br g (t • D v) ∈ Ω})
    (hsegments : ∀ v (T : ℝ), 0 < T →
      ∀ g ∈ flowLineBase Ω (PolynomialCoordinateGroup.exp _ hg) (D v) T,
        T⁻¹ • (f (dynkinProduct a br g (T • D v)) - f g) ∈
            convexHull ℝ (range fun l => (A l).val (p (D v))) ∧
        T * P.segmentSupport (p (D v)) ≤ P.templateSupport
          ((fun t : ℝ => f (dynkinProduct a br g (t • D v))) '' Icc 0 T)) :
    ∃ l b, ∀ g ∈ Ω, f g = (A l).val ((π g).toAdd) + b := by
  classical
  let G := PolynomialCoordinateGroup (dynkinProduct a br) hg
  let e : V ≃ₜ G := PolynomialCoordinateGroup.expHomeomorph _ hg
  let : T2Space G := inferInstanceAs (T2Space V)
  let : LocallyCompactSpace G := inferInstanceAs (LocallyCompactSpace V)
  let : SecondCountableTopology G := inferInstanceAs (SecondCountableTopology V)
  let : IsTopologicalGroup G := PolynomialCoordinateGroup.isTopologicalGroup _ hg
    (continuous_dynkinProduct a (fun _ => br) Prod.fst Prod.snd
      continuous_const continuous_fst continuous_snd)
  have hm : ContDiff ℝ ∞ (fun z : V × V => dynkinProduct a br z.1 z.2) :=
    contDiff_dynkinProduct a (fun _ => br) Prod.fst Prod.snd
      contDiff_const contDiff_fst contDiff_snd
  have hlocal (g : V) (v : H) : ∃ T : ℝ, 0 < T ∧
      (g ∈ Ω → g ∈ flowLineBase Ω (PolynomialCoordinateGroup.exp _ hg) (D v) T) := by
    by_cases hgΩ : g ∈ Ω
    · have hevent : ∀ᶠ t : ℝ in 𝓝 0, dynkinProduct a br g (t • D v) ∈ Ω := by
        have hcont : Continuous (fun t : ℝ => dynkinProduct a br g (t • D v)) :=
          hm.continuous.comp (continuous_const.prodMk (continuous_id.smul continuous_const))
        have h0 : dynkinProduct a br g ((0 : ℝ) • D v) ∈ Ω := by
          simpa only [zero_smul, hg.2.2.1] using hgΩ
        exact hcont.continuousAt (hΩ.mem_nhds h0)
      obtain ⟨ε, hε, he⟩ := Metric.eventually_nhds_iff.mp hevent
      refine ⟨ε / 2, half_pos hε, fun _ t ht => he ?_⟩
      rw [Real.dist_eq, sub_zero, abs_of_nonneg ht.1]
      exact ht.2.trans_lt (half_lt_self hε)
    · exact ⟨1, zero_lt_one, fun h => (hgΩ h).elim⟩
  choose T hT hstay using hlocal
  obtain ⟨label, hlabel, hbase⟩ := exists_measurable_horizontal_profile_label
    (dynkinProduct a br) hg hm μ f hf Ω hΩ D bH C hlip P (p.comp D) hp A T
    (fun g _ v => hT g v)
    (fun g hgΩ v t ht htT =>
      (hsegments v t ht g (fun s hs => hstay g v hgΩ s ⟨hs.1, hs.2.trans htT.le⟩)).1)
    (fun g hgΩ v t ht htT =>
      (hsegments v t ht g (fun s hs => hstay g v hgΩ s ⟨hs.1, hs.2.trans htT.le⟩)).2)
  apply affine_of_horizontal_labels a br hbr hg hc D X b₀ w₀ hw₀ μ Ω hΩ hconn hne f hf
    π p hp hπExp P hweights σ hσ label hlabel A hbase C hlip
  intro v t ht g hgt
  exact (hsegments v t ht g hgt).2

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CoarseFlowBounds
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instNonemptyBases _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_nonempty _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform coarse bounds along actual one-parameter subgroups

Continuity and the homomorphism law suffice for the path-mesh estimates.
The additive constant accommodates short parameter intervals without an
extra Riemannian regularity assumption on the ambient metric.
-/

noncomputable section

namespace PolycyclicRecognition

open Set

variable {G : Type} [Group G] [PseudoMetricSpace G] [IsIsometricSMul G G]

theorem continuous_flow_coarse_bound (d : ℝ → G) (hd : Continuous d) (hzero : d 0 = 1)
    (hmul : ∀ s t, d (s + t) = d s * d t) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, dist 1 (d t) ≤ C * (1 + |t|) := by
  obtain ⟨C, hC⟩ := (isCompact_Icc : IsCompact (Icc (-1 : ℝ) 1)).bddAbove_image
    (continuous_const.dist hd).continuousOn
  have hC0 : 0 ≤ C := by
    have hh := hC (mem_image_of_mem (fun t => dist (1 : G) (d t))
      (show (0 : ℝ) ∈ Icc (-1 : ℝ) 1 by constructor <;> norm_num))
    simpa [hzero] using hh
  have hpower (s : ℝ) (n : ℕ) : d ((n : ℝ) * s) = d s ^ n := by
    induction n with
    | zero => simp [hzero]
    | succ n ih => rw [Nat.cast_succ, add_mul, one_mul, hmul, ih, pow_succ]
  refine ⟨C, hC0, ?_⟩
  intro t
  let n := ⌊|t|⌋₊ + 1
  have hn : 0 < (n : ℝ) := by exact_mod_cast (Nat.succ_pos ⌊|t|⌋₊)
  have htn : |t| ≤ (n : ℝ) := by simpa [n] using (Nat.lt_floor_add_one |t|).le
  have hnt : (n : ℝ) ≤ |t| + 1 := by
    simpa [n] using add_le_add_right (Nat.floor_le (abs_nonneg t)) 1
  have hsabs : |t / n| ≤ 1 := by
    rw [abs_div, abs_of_pos hn]
    exact (div_le_one hn).mpr htn
  have hs : t / n ∈ Icc (-1 : ℝ) 1 := abs_le.mp hsabs
  have hlocal : dist 1 (d (t / n)) ≤ C := hC (mem_image_of_mem _ hs)
  have he : d t = d (t / n) ^ n := by
    convert hpower (t / n) n using 1
    all_goals try with_reducible_and_instances rfl
    field_simp
  rw [he]
  exact (dist_one_pow_le _ _).trans ((mul_le_mul_of_nonneg_left hlocal hn.le).trans
    (by nlinarith))

/-- Differences along the flow have the same uniform bound. -/
theorem continuous_flow_coarse_dist (d : ℝ → G) (hd : Continuous d) (hzero : d 0 = 1)
    (hmul : ∀ s t, d (s + t) = d s * d t) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s t : ℝ, dist (d s) (d t) ≤ C * (1 + |t - s|) := by
  obtain ⟨C, hC, hb⟩ := continuous_flow_coarse_bound d hd hzero hmul
  refine ⟨C, hC, ?_⟩
  intro s t
  have he : d t = d s * d (t - s) := by rw [← hmul]; congr 1; ring
  rw [he]
  have he' : dist (d s) (d s * d (t - s)) = dist 1 (d (t - s)) := by
    simpa only [mul_one] using dist_mul_left (d s) 1 (d (t - s))
  rw [he']
  exact hb _

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_GradedFlowLimit
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Convergence of horizontal flows in graded coordinates -/

noncomputable section

namespace PolycyclicRecognition

open Filter Set Module
open scoped Topology

variable {n : ℕ}

/-- The polynomial flow depends continuously on its bracket and velocity
in the topology of uniform convergence on compact sets. -/
theorem continuous_dynkinFlowMap {c : ℕ} (a : DynkinCoefficients c 2) :
    Continuous (fun p : ((Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) × (Fin n → ℝ) => dynkinFlowMap (n := n) a p.1 p.2) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  change Continuous (fun z : (((Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) × (Fin n → ℝ)) × ((Fin n → ℝ) × ℝ) =>
    dynkinProduct a z.1.1 z.2.1 (z.2.2 • z.1.2))
  exact continuous_dynkinProduct (P := (((Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) × (Fin n → ℝ)) × ((Fin n → ℝ) × ℝ))
    a (fun z => z.1.1) (fun z => z.2.1) (fun z => z.2.2 • z.1.2)
    continuous_fst.fst continuous_snd.fst
    (continuous_snd.snd.smul continuous_fst.snd)

theorem dynkinFlowMap_tendsto {c : ℕ} (a : DynkinCoefficients c 2)
    {ι : Type} {l : Filter ι} {B : ι → (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)}
    {B₀ : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)} {v : ι → (Fin n → ℝ)} {v₀ : (Fin n → ℝ)}
    (hB : Tendsto B l (𝓝 B₀)) (hv : Tendsto v l (𝓝 v₀)) :
    Tendsto (fun i => dynkinFlowMap (n := n) a (B i) (v i)) l (𝓝 (dynkinFlowMap (n := n) a B₀ v₀)) := by
  have hp : Tendsto (fun i => (B i, v i)) l (𝓝 (B₀, v₀)) := hB.prodMk_nhds hv
  simpa only [Function.comp_def] using
    ((continuous_dynkinFlowMap (n := n) a).tendsto (B₀, v₀)).comp hp

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_RescaledProfiles
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Equicontinuity of actual rescaled map profiles -/

noncomputable section

namespace PolycyclicRecognition

open Module Filter
open scoped Topology NNReal

variable {G W Z : Type} [Group G] [PseudoMetricSpace G] [IsIsometricSMul G G]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

theorem rescaledMapProfile_dist_le {K : ℝ≥0} {J : G → W} (hJ : LipschitzWith K J)
    (x k : G) (r : ℝ) (φ : Z → G) (z w : Z) :
    dist (rescaledMapProfile J x k r φ z) (rescaledMapProfile J x k r φ w) ≤
      (K : ℝ) * (dist (φ z) (φ w) / Real.exp r) := by
  have hh := hJ.dist_le_mul (x * k * φ z) (x * k * φ w)
  rw [dist_mul_left] at hh
  have he : dist (rescaledMapProfile J x k r φ z) (rescaledMapProfile J x k r φ w) =
      dist (J (x * k * φ z)) (J (x * k * φ w)) / Real.exp r := by
    simp only [rescaledMapProfile, dist_eq_norm, ← smul_sub,
      sub_sub_sub_cancel_right, norm_smul, Real.norm_eq_abs,
      abs_inv, abs_of_pos (Real.exp_pos r), div_eq_mul_inv, mul_comm]
  rw [he]
  calc
    _ ≤ ((K : ℝ) * dist (φ z) (φ w)) / Real.exp r := div_le_div_of_nonneg_right hh (Real.exp_pos r).le
    _ = _ := by ring

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_SupportedGoodSetSelection
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Good profile neighborhoods selected from a supported weak limit -/

noncomputable section

namespace PolycyclicRecognition

open Filter MeasureTheory Set
open scoped Topology ENNReal

/-- Each open neighborhood of a supported profile has a fixed positive
mass along every sufficiently late member of the weakly convergent family. -/
theorem eventual_positive_mass_of_supported_weak_limit
    {X ι : Type} [TopologicalSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X] [HasOuterApproxClosed X]
    {l : Filter ι} [l.NeBot] {μs : ι → ProbabilityMeasure X} {μ : ProbabilityMeasure X}
    (hμ : Tendsto μs l (𝓝 μ)) {x : X} (hx : x ∈ (μ : Measure X).support)
    {U : Set X} (hU : IsOpen U) (hxU : x ∈ U) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ i in l, c ≤ ((μs i : Measure X) U).toReal := by
  have hp : 0 < (μ : Measure X) U :=
    (Measure.mem_support_iff_forall x).mp hx U (hU.mem_nhds hxU)
  have hfin : (μ : Measure X) U ≠ ∞ := measure_ne_top _ _
  have hr : 0 < ((μ : Measure X) U).toReal := ENNReal.toReal_pos hp.ne' hfin
  let c := ((μ : Measure X) U).toReal / 2
  have hc : 0 < c := half_pos hr
  have hlt : ENNReal.ofReal c < (μ : Measure X) U :=
    (ENNReal.ofReal_lt_iff_lt_toReal hc.le hfin).mpr (half_lt_self hr)
  have he := eventually_lt_of_lt_liminf
    (hlt.trans_le (ProbabilityMeasure.le_liminf_measure_open_of_tendsto hμ hU))
  refine ⟨c, hc, he.mono ?_⟩
  intro i hi
  exact ((ENNReal.ofReal_lt_iff_lt_toReal hc.le (measure_ne_top _ _)).mp hi).le

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_GradedHeight
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_nonempty _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original height is a homomorphism on the graded group -/

noncomputable section
namespace PolycyclicRecognition

open Module Filter
open scoped Topology

variable {L G W I : Type} [LieRing L] [LieAlgebra ℝ L]
  [Group G] [NormedAddCommGroup W] [NormedSpace ℝ W]
  [Fintype I] [DecidableEq I]

/-- Exact height additivity survives in every rescaled word chart. -/
theorem rescaledWordChartProduct_height
    (X : I → L) (S : Finset (FreeMagma I)) (β : WordBasisSelections X S)
    (h : L →ₗ[ℝ] W) (hh : ∀ x y : L, h ⁅x, y⁆ = 0)
    (Exp : L → G) (π : G →* Multiplicative W)
    (hπ : ∀ x, (π (Exp x)).toAdd = h x)
    {c : ℕ} (a : DynkinCoefficients c 2)
    (hm : ∀ x y, Exp (finiteDynkinPolynomial a ![x, y]) = Exp x * Exp y)
    (r : ℝ) (x y : Fin (finrank ℝ L) → ℝ) :
    let b := WordBasisSelections.basis X S β
    let cost := fun j => bracketWordExponent (fun _ : I => 1) (β.val j)
    h (b.equivFun.symm (dynkinProduct a
      (basisBracket (exponentialRescaleBasis b cost r)) x y)) =
        h (b.equivFun.symm x) + h (b.equivFun.symm y) := by
  dsimp only
  let b := WordBasisSelections.basis X S β
  let cost := fun j => bracketWordExponent (fun _ : I => 1) (β.val j)
  let br := exponentialRescaleBasis b cost r
  have hp (z : Fin (finrank ℝ L) → ℝ) :
      h (br.equivFun.symm z) = Real.exp r • h (b.equivFun.symm z) := by
    simpa only [br, cost, bracketWordExponent_one, Real.log_exp] using
      word_length_chart_height X S β h hh (Real.exp_pos r) z
  have he := congrArg (fun g : G => (π g).toAdd)
    (exp_basis_dynkinProduct br Exp a hm x y)
  simp only [map_mul, toAdd_mul, hπ, hp, ← smul_add] at he
  exact (smul_right_injective W (ne_of_gt (Real.exp_pos r))) he

/-- Passing the finite-scale identity to the limiting polynomial product
gives the actual height homomorphism, without a new input on the limit. -/
theorem gradedWordChartProduct_height
    (X : I → L) (S : Finset (FreeMagma I)) (β : WordBasisSelections X S)
    (h : L →ₗ[ℝ] W) (hh : ∀ x y : L, h ⁅x, y⁆ = 0)
    (Exp : L → G) (π : G →* Multiplicative W)
    (hπ : ∀ x, (π (Exp x)).toAdd = h x)
    {c : ℕ} (a : DynkinCoefficients c 2)
    (hm : ∀ x y, Exp (finiteDynkinPolynomial a ![x, y]) = Exp x * Exp y)
    (hweight : ∀ i j k,
      (WordBasisSelections.basis X S β).repr
        ⁅(WordBasisSelections.basis X S β) i, (WordBasisSelections.basis X S β) j⁆ k ≠ 0 →
      bracketWordExponent (fun _ : I => 1) (β.val i) +
        bracketWordExponent (fun _ : I => 1) (β.val j) ≤
          bracketWordExponent (fun _ : I => 1) (β.val k))
    (x y : Fin (finrank ℝ L) → ℝ) :
    let b := WordBasisSelections.basis X S β
    let cost := fun j => bracketWordExponent (fun _ : I => 1) (β.val j)
    h (b.equivFun.symm (dynkinProduct a (gradedCoordinateBracket b cost) x y)) =
      h (b.equivFun.symm x) + h (b.equivFun.symm y) := by
  dsimp only
  let b := WordBasisSelections.basis X S β
  let cost := fun j => bracketWordExponent (fun _ : I => 1) (β.val j)
  let p := h.comp b.equivFun.symm.toLinearMap
  have hprod := ((continuous_dynkinProduct a id (fun _ => x) (fun _ => y)
    continuous_id continuous_const continuous_const).tendsto
      (gradedCoordinateBracket b cost)).comp
        (basisBracket_rescale_tendsto b cost hweight)
  have hp := p.continuous_of_finiteDimensional.tendsto _ |>.comp hprod
  have he : (fun r : ℝ => p (dynkinProduct a
      (basisBracket (exponentialRescaleBasis b cost r)) x y)) =
      (fun _ => h (b.equivFun.symm x) + h (b.equivFun.symm y)) := by
    funext r
    exact rescaledWordChartProduct_height X S β h hh Exp π hπ a hm r x y
  dsimp only [Function.comp_def, id_eq] at hp
  rw [he] at hp
  exact tendsto_nhds_unique hp tendsto_const_nhds

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CoordinateProfileFlow
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual coordinate flows used by the profile cutoffs -/

noncomputable section

namespace PolycyclicRecognition

open Module MeasureTheory Filter
open scoped Manifold Topology NNReal

/-- The full rescaled flow converges as a continuous map, so the cutoff
construction applies simultaneously to every compact time interval. -/
theorem rescaled_horizontal_flow_tendsto
    {L : Type} [LieRing L] [LieAlgebra ℝ L] {n c : ℕ}
    (a : DynkinCoefficients c 2) (b : Basis (Fin n) ℝ L) (cost : Fin n → ℝ)
    (hweight : ∀ i j k, b.repr ⁅b i, b j⁆ k ≠ 0 → cost i + cost j ≤ cost k)
    (v : L) (hv : ∀ j, b.repr v j ≠ 0 → 1 ≤ cost j) :
    Tendsto (fun r => dynkinFlowMap a (basisBracket (exponentialRescaleBasis b cost r))
      ((exponentialRescaleBasis b cost r).equivFun (Real.exp r • v))) atTop
      (𝓝 (dynkinFlowMap a (gradedCoordinateBracket b cost) (gradedGenerator b cost 1 v))) := by
  apply dynkinFlowMap_tendsto a (basisBracket_rescale_tendsto b cost hweight)
  simpa only [mul_one] using rescaled_generator_tendsto b cost 1 v hv

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CoordinateFlowProfileIdentity
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact increments for the actual polynomial horizontal flow -/

noncomputable section

namespace PolycyclicRecognition

open Module
open scoped NNReal

theorem exp_basis_horizontal_flow
    {L D : Type} [LieRing L] [LieAlgebra ℝ L] [Group D] {n c : ℕ}
    (Exp : L → D) (b : Basis (Fin n) ℝ L) (a : DynkinCoefficients c 2)
    (hm : ∀ x y, Exp (finiteDynkinPolynomial a ![x, y]) = Exp x * Exp y)
    (r t : ℝ) (v : L) (z : Fin n → ℝ) :
    Exp (b.equivFun.symm (dynkinFlowMap a (basisBracket b) (b.equivFun (r • v)) (z, t))) =
      Exp (b.equivFun.symm z) * Exp ((r * t) • v) := by
  change Exp (b.equivFun.symm (dynkinProduct a (basisBracket b) z
    (t • b.equivFun (r • v)))) = _
  rw [exp_basis_dynkinProduct b Exp a hm]
  simp only [map_smul, LinearEquiv.symm_apply_apply, smul_smul, mul_comm t r]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_SupportedFlowLipschitz
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instNonemptyBases _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_nonempty _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Horizontal Lipschitz bounds for every supported profile -/

noncomputable section
namespace PolycyclicRecognition

open Set Filter MeasureTheory
open scoped Topology NNReal

/-- Uniformly converging observables retain every uniform asymptotic bound
on the support of a weak sample limit. -/
theorem le_on_support_of_ae_sample_bound
    {X A : Type} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    [HasOuterApproxClosed X] [MeasurableSpace A]
    (samples : ℕ → ProbabilityMeasure A) (sample : ℕ → A → X)
    (hsample : ∀ n, Measurable (sample n)) (ν : ProbabilityMeasure X)
    (hν : Tendsto (fun n => ProbabilityMeasure.map (samples n) (f := (sample n)) (by first | exact (hsample n).aemeasurable | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)) atTop (𝓝 ν))
    (obsn : ℕ → X → ℝ) (obs : X → ℝ) (hobs : Continuous obs)
    (hlim : TendstoUniformly obsn obs atTop)
    (ε : ℕ → ℝ) (hε : Tendsto ε atTop (𝓝 0)) (C : ℝ)
    (hbound : ∀ᶠ n in atTop, ∀ᵐ a ∂(samples n : Measure A),
      obsn n (sample n a) ≤ C + ε n)
    {f : X} (hf : f ∈ (ν : Measure X).support) : obs f ≤ C := by
  by_contra h
  have hgap : 0 < obs f - C := sub_pos.mpr (lt_of_not_ge h)
  let δ := (obs f - C) / 3
  have hδ : 0 < δ := div_pos hgap (by norm_num)
  let U := {x | C + 2 * δ < obs x}
  have hU : IsOpen U := isOpen_lt continuous_const hobs
  have hfU : f ∈ U := by dsimp [U, δ] <;> linarith
  obtain ⟨c, hc, hmass⟩ := eventual_positive_mass_of_supported_weak_limit hν hf hU hfU
  have herr := (Metric.tendstoUniformly_iff.mp hlim) δ hδ
  have heps := hε.eventually (gt_mem_nhds hδ)
  obtain ⟨n, hn, hb, he, hm⟩ := (hbound.and (herr.and (heps.and hmass))).exists
  have hempty : (samples n : Measure A) (sample n ⁻¹' U) = 0 := by
    have hnot : ∀ᵐ a ∂(samples n : Measure A), a ∉ sample n ⁻¹' U := by
      filter_upwards [hn] with a haBound
      intro ha
      have hd := hb (sample n a)
      have hd' : obs (sample n a) < obsn n (sample n a) + δ := by
        have ht := (abs_lt.mp (by simpa only [Real.dist_eq, abs_sub_comm] using hd)).1
        linarith
      change C + 2 * δ < obs (sample n a) at ha
      linarith
    simpa only [not_not, Set.ofPred_mem_eq] using ae_iff.mp hnot
  have hz : ((ProbabilityMeasure.map (samples n) (f := (sample n)) (by first | exact (hsample n).aemeasurable | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability) : Measure X) U).toReal = 0 := by
    change (Measure.map (sample n) (samples n : Measure A) U).toReal = 0
    rw [Measure.map_apply (hsample n) hU.measurableSet,
      hempty, ENNReal.toReal_zero]
  rw [hz] at hm
  exact (not_le_of_gt hc) hm

/-- The pointwise version of the almost-everywhere sample bound. -/
theorem le_on_support_of_uniform_sample_bound
    {X A : Type} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    [HasOuterApproxClosed X] [MeasurableSpace A]
    (samples : ℕ → ProbabilityMeasure A) (sample : ℕ → A → X)
    (hsample : ∀ n, Measurable (sample n)) (ν : ProbabilityMeasure X)
    (hν : Tendsto (fun n => ProbabilityMeasure.map (samples n) (f := (sample n)) (by first | exact (hsample n).aemeasurable | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)) atTop (𝓝 ν))
    (obsn : ℕ → X → ℝ) (obs : X → ℝ) (hobs : Continuous obs)
    (hlim : TendstoUniformly obsn obs atTop)
    (ε : ℕ → ℝ) (hε : Tendsto ε atTop (𝓝 0)) (C : ℝ)
    (hbound : ∀ᶠ n in atTop, ∀ a, obsn n (sample n a) ≤ C + ε n)
    {f : X} (hf : f ∈ (ν : Measure X).support) : obs f ≤ C := by
  exact le_on_support_of_ae_sample_bound samples sample hsample ν hν obsn obs hobs hlim
    ε hε C (hbound.mono fun _ hn => Filter.Eventually.of_forall hn) hf

theorem continuous_profileFlowDistance
    {V W : Type} [TopologicalSpace V] [LocallyCompactSpace V]
    [PseudoMetricSpace W] (S : Set C(V, W)) (z : V) (s t : ℝ) :
    Continuous (profileFlowDistance S z s t) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  change Continuous (fun p : C(V × ℝ, V) × S =>
    dist (p.2.val (p.1 (z, s))) (p.2.val (p.1 (z, t))))
  apply Continuous.dist
  · exact continuous_eval.comp ((continuous_subtype_val.comp continuous_snd).prodMk
      (continuous_eval.comp (continuous_fst.prodMk continuous_const)))
  · exact continuous_eval.comp ((continuous_subtype_val.comp continuous_snd).prodMk
      (continuous_eval.comp (continuous_fst.prodMk continuous_const)))

/-- A coarse Lipschitz bound with a vanishing additive error becomes an
exact Lipschitz bound along the limiting horizontal flow. -/
theorem lipschitz_supported_profile_flow
    {V W A : Type} [TopologicalSpace V] [LocallyCompactSpace V]
    [PseudoMetricSpace W] [MeasurableSpace A]
    (S : Set C(V, W)) (hS : IsCompact S)
    [MeasurableSpace S] [BorelSpace S] [HasOuterApproxClosed S]
    (samples : ℕ → ProbabilityMeasure A) (sample : ℕ → A → S)
    (hsample : ∀ n, Measurable (sample n)) (ν : ProbabilityMeasure S)
    (hν : Tendsto (fun n => ProbabilityMeasure.map (samples n) (f := (sample n)) (by first | exact (hsample n).aemeasurable | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)) atTop (𝓝 ν))
    (Fn : ℕ → C(V × ℝ, V)) (F : C(V × ℝ, V)) (hF : Tendsto Fn atTop (𝓝 F))
    (ε : ℕ → ℝ) (hε : Tendsto ε atTop (𝓝 0)) (C : ℝ≥0) (z : V)
    (hbound : ∀ᶠ n in atTop, ∀ a s t,
      dist ((sample n a).val (Fn n (z, s))) ((sample n a).val (Fn n (z, t))) ≤
        C * |s - t| + ε n)
    {f : S} (hf : f ∈ (ν : Measure S).support) :
    LipschitzWith C (fun t : ℝ => f.val (F (z, t))) := by
  let : CompactSpace S := isCompact_iff_compactSpace.mp hS
  apply LipschitzWith.of_dist_le_mul
  intro s t
  let obsn := fun n => profileFlowDistance S z s t (Fn n)
  let obs := profileFlowDistance S z s t F
  have ho : Tendsto obsn atTop (𝓝 obs) :=
    ((continuous_profileFlowDistance S z s t).tendsto F).comp hF
  have hu : TendstoUniformly (fun n g => obsn n g) obs atTop :=
    tendstoUniformlyOn_univ.mp
      ((ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn.mp ho)
        univ isCompact_univ)
  have hb := le_on_support_of_uniform_sample_bound samples sample hsample ν hν
    (fun n g => obsn n g) obs obs.continuous hu ε hε (C * |s - t|)
    (hbound.mono fun n hn a => hn a s t) hf
  simpa only [obs, profileFlowDistance, ContinuousMap.coe_mk, Real.dist_eq] using hb

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_RescaledFlowLipschitz
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.CartanFactorModel.realScaleProfile_apply _root_.OAI.PolycyclicRecognition.CartanFactorModel.sampledProbeProfile_apply _root_.OAI.PolycyclicRecognition.basisDynkinParameter_zero _root_.OAI.PolycyclicRecognition.dynkinRightTranslation_apply _root_.OAI.PolycyclicRecognition.dynkinRightTranslation_symm_apply _root_.OAI.PolycyclicRecognition.exponentialHomOfDynkin_apply_exp _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Coarse one-parameter bounds give Lipschitz limiting profiles -/

noncomputable section
namespace PolycyclicRecognition

open Module Filter MeasureTheory
open scoped Topology NNReal

theorem rescaled_profile_flow_dist_le
    {L D G W : Type} [LieRing L] [LieAlgebra ℝ L] [Group D]
    [Group G] [PseudoMetricSpace G] [IsIsometricSMul G G]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    {n c : ℕ} (Exp : L → D) (κ : D →* G) (b : Basis (Fin n) ℝ L)
    (a : DynkinCoefficients c 2)
    (hm : ∀ x y, Exp (finiteDynkinPolynomial a ![x, y]) = Exp x * Exp y)
    (v : L) {C : ℝ}
    (hcoarse : ∀ s t : ℝ, dist (κ (Exp (s • v))) (κ (Exp (t • v))) ≤
      C * (1 + |t - s|))
    {K : ℝ≥0} (J : G → W) (hJ : LipschitzWith K J)
    (x k : G) (r : ℝ) (z : Fin n → ℝ) (s t : ℝ) :
    let φ := fun y => κ (Exp (b.equivFun.symm y))
    let F := dynkinFlowMap a (basisBracket b) (b.equivFun (Real.exp r • v))
    dist (rescaledMapProfile J x k r φ (F (z, s)))
      (rescaledMapProfile J x k r φ (F (z, t))) ≤
        (K : ℝ) * C * |s - t| + (K : ℝ) * C / Real.exp r := by
  dsimp only
  have hb := rescaledMapProfile_dist_le hJ x k r
    (fun y => κ (Exp (b.equivFun.symm y)))
    (dynkinFlowMap a (basisBracket b) (b.equivFun (Real.exp r • v)) (z, s))
    (dynkinFlowMap a (basisBracket b) (b.equivFun (Real.exp r • v)) (z, t))
  simp only [exp_basis_horizontal_flow Exp b a hm, map_mul, dist_mul_left] at hb
  apply hb.trans
  calc
    _ ≤ (K : ℝ) * (C * (1 + |Real.exp r * t - Real.exp r * s|) / Real.exp r) :=
      mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_right (hcoarse _ _) (Real.exp_pos r).le) K.coe_nonneg
    _ = _ := by
      rw [← mul_sub, abs_mul, abs_of_pos (Real.exp_pos r), abs_sub_comm t s]
      field_simp
      ring

/-- All supported weak limits of the actual rescaled profiles are
Lipschitz along the graded flow. The constant is independent of the base
point and of the supported profile. -/
theorem lipschitz_supported_rescaled_flow
    {L D G W A : Type} [LieRing L] [LieAlgebra ℝ L] [Group D]
    [Group G] [PseudoMetricSpace G] [IsIsometricSMul G G]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [MeasurableSpace A]
    {n c : ℕ} (Exp : L → D) (κ : D →* G) (b : Basis (Fin n) ℝ L)
    (cost : Fin n → ℝ)
    (hweight : ∀ i j k, b.repr ⁅b i, b j⁆ k ≠ 0 → cost i + cost j ≤ cost k)
    (a : DynkinCoefficients c 2)
    (hm : ∀ x y, Exp (finiteDynkinPolynomial a ![x, y]) = Exp x * Exp y)
    (v : L) (hv : ∀ j, b.repr v j ≠ 0 → 1 ≤ cost j)
    (hd : Continuous (fun t : ℝ => κ (Exp (t • v))))
    (hd0 : κ (Exp ((0 : ℝ) • v)) = 1)
    (hmul : ∀ s t : ℝ, κ (Exp ((s + t) • v)) = κ (Exp (s • v)) * κ (Exp (t • v)))
    (scale : ℕ → ℝ) (hscale : Tendsto scale atTop atTop)
    {K : ℝ≥0} (J : ℕ → A → G → W) (hJ : ∀ n u, LipschitzWith K (J n u))
    (x suffix : ℕ → A → G)
    (S : Set C((Fin n → ℝ), W)) (hS : IsCompact S)
    [MeasurableSpace S] [BorelSpace S] [HasOuterApproxClosed S]
    (samples : ℕ → ProbabilityMeasure A) (profile : ℕ → A → S)
    (hp : ∀ n, Measurable (profile n)) (ν : ProbabilityMeasure S)
    (hν : Tendsto (fun n => ProbabilityMeasure.map (samples n) (f := (profile n)) (by first | exact (hp n).aemeasurable | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)) atTop (𝓝 ν))
    (hactual : ∀ i u z, (profile i u).val z =
      rescaledMapProfile (J i u) (x i u) (suffix i u) (scale i)
        (fun z => κ (Exp ((exponentialRescaleBasis b cost (scale i)).equivFun.symm z))) z) :
    ∃ C : ℝ≥0, ∀ (f : S), f ∈ (ν : Measure S).support → ∀ z,
      LipschitzWith C (fun t : ℝ => f.val
        (dynkinFlowMap a (gradedCoordinateBracket b cost) (gradedGenerator b cost 1 v) (z, t))) := by
  obtain ⟨C, hC, hcoarse⟩ := continuous_flow_coarse_dist _ hd hd0 hmul
  let C' : ℝ≥0 := ⟨K * C, mul_nonneg K.coe_nonneg hC⟩
  let Fn := fun i => dynkinFlowMap a (basisBracket (exponentialRescaleBasis b cost (scale i)))
    ((exponentialRescaleBasis b cost (scale i)).equivFun (Real.exp (scale i) • v))
  let F := dynkinFlowMap a (gradedCoordinateBracket b cost) (gradedGenerator b cost 1 v)
  have hF : Tendsto Fn atTop (𝓝 F) := (rescaled_horizontal_flow_tendsto a b cost hweight v hv).comp hscale
  let ε := fun i => (K : ℝ) * C / Real.exp (scale i)
  have hε : Tendsto ε atTop (𝓝 0) :=
    (Real.tendsto_exp_atTop.comp hscale).const_div_atTop _
  refine ⟨C', fun f hf z => ?_⟩
  apply lipschitz_supported_profile_flow S hS samples profile hp ν hν Fn F hF ε hε C' z ?_ hf
  apply Eventually.of_forall
  intro i u s t
  simp only [hactual]
  exact rescaled_profile_flow_dist_le Exp κ (exponentialRescaleBasis b cost (scale i))
    a hm v hcoarse (J i u) (hJ i u) (x i u) (suffix i u) (scale i) z s t

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanGradedGeometry
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.CartanFactorModel.heightRay_zero _root_.OAI.PolycyclicRecognition.CartanFactorModel.realScaleProfile_apply _root_.OAI.PolycyclicRecognition.CartanFactorModel.sampledProbeProfile_apply _root_.OAI.PolycyclicRecognition.basisDynkinParameter_zero _root_.OAI.PolycyclicRecognition.bracketWordDifferential_mul _root_.OAI.PolycyclicRecognition.cartanWeightDerivation_apply_root _root_.OAI.PolycyclicRecognition.chartExponentialFlow_zero _root_.OAI.PolycyclicRecognition.derivationSemidirectHom_apply _root_.OAI.PolycyclicRecognition.exponentialHomOfDynkin_apply_exp _root_.OAI.PolycyclicRecognition.exponentialRescaleBasis_zero _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.modelNilradicalLinearAction_apply _root_.OAI.PolycyclicRecognition.modelNilradicalRotation_apply _root_.OAI.PolycyclicRecognition.modelNilradicalRotation_mul _root_.OAI.PolycyclicRecognition.modelNilradicalRotation_one _root_.OAI.PolycyclicRecognition.nilshadowWeightDerivation_symm _root_.OAI.PolycyclicRecognition.nilshadowWeightOperator_symm _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual graded Cartan group's geometric data -/

noncomputable section
namespace PolycyclicRecognition

open Module LieAlgebra LieModule Filter MeasureTheory
open scoped Manifold Topology NNReal Matrix.Norms.Operator

attribute [local instance 100] LieRing.ofAssociativeRing

variable {EG G W I A : Type} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G] [IsIsometricSMul G G]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  {ExpG : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H ExpG)

set_option maxHeartbeats 1000000 in
include T in
omit [IsIsometricSMul G G] in
/-- The conjugation identity for the actual graded Cartan law is derived
from the published faithful realization and the original exponential. -/
theorem cartan_graded_conjugation
    (hExpG : IsGroupExponential ExpG)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (haarD : NilpotentExponentialHaarInput F.D.modelSpace F.D.carrier)
    {n c : ℕ} (b : Basis (Fin n) ℝ H) (cost : Fin n → ℝ)
    (hweight : ∀ i j k, b.repr ⁅b i, b j⁆ k ≠ 0 → cost i + cost j ≤ cost k)
    (coeff : DynkinCoefficients c 2)
    (hm : ∀ x y, F.ExpD (finiteDynkinPolynomial coeff ![x, y]) = F.ExpD x * F.ExpD y) :
    ExponentialConjugationLaw (dynkinProduct coeff (gradedCoordinateBracket b cost))
      (gradedCoordinateBracket b cost) := by
  obtain ⟨d, hd, ρ, j, hind, hmatch⟩ := realize ⟨a, ⟨T⟩⟩ ExpG hExpG
  let _ : NeZero d := ⟨Nat.ne_of_gt hd⟩
  have hρ : Function.Injective ρ := by
    intro g h he
    exact hind.injective (congrArg (fun u : (Matrix (Fin d) (Fin d) ℝ)ˣ =>
      (u : Matrix (Fin d) (Fin d) ℝ)) he)
  obtain ⟨⟨chartD, hchartD⟩, _⟩ := haarD.2 F.ExpD F.isExpD
    (F.D.tangent_nilpotent inferInstance)
  have hinj : Function.Injective (F.ExpD ∘ F.D.equiv) :=
    ((funext hchartD ▸ chartD.bijective).comp F.D.equiv.bijective).injective
  exact graded_exponentialConjugationLaw b cost hweight (F.ExpD ∘ F.D.equiv) hinj
    (fun x => by simp [F.isExpD.map_neg]) coeff
    (model_binary_dynkin F.D.equiv F.ExpD coeff hm) (j.comp H.incl)
    (ρ.comp F.inclusionD) (hρ.comp F.closedD.injective) (fun x => by
      change ρ (F.inclusionD (F.ExpD (F.D.equiv x))) = _
      rw [F.compatibleD, hmatch]
      rfl)

variable [NormedAddCommGroup W] [NormedSpace ℝ W] [Fintype I] [DecidableEq I]
  [MeasurableSpace A]

set_option maxHeartbeats 1000000 in
include T in
/-- Supported actual Cartan profiles have one horizontal Lipschitz bound
for each direction, uniform in the starting point and supported profile. -/
theorem lipschitz_supported_cartan_profiles
    (hExpG : IsGroupExponential ExpG)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (X : I → H) {d : ℕ} (hDnil : lowerCentralSeries ℝ H H d = ⊥)
    (bD₀ : Basis (Fin (finrank ℝ H)) ℝ H)
    (β : WordBasisSelections X (boundedBracketWords d))
    (hβ : IsMaximizingColumnBasis (wordListCoordinates X (boundedBracketWords d) bD₀)
      (fun w => bracketWordExponent (fun _ : I => 1) w) β.val)
    {c : ℕ} (coeff : DynkinCoefficients c 2)
    (hm : ∀ x y, F.ExpD (finiteDynkinPolynomial coeff ![x, y]) = F.ExpD x * F.ExpD y)
    (scale : ℕ → ℝ) (hscale : Tendsto scale atTop atTop)
    {K : ℝ≥0} (J : ℕ → A → G → W) (hJ : ∀ n u, LipschitzWith K (J n u))
    (x suffix : ℕ → A → G)
    (S : Set C((Fin (finrank ℝ H) → ℝ), W)) (hS : IsCompact S)
    [MeasurableSpace S] [BorelSpace S] [HasOuterApproxClosed S]
    (samples : ℕ → ProbabilityMeasure A) (profile : ℕ → A → S)
    (hp : ∀ n, Measurable (profile n)) (ν : ProbabilityMeasure S)
    (hν : Tendsto (fun n => ProbabilityMeasure.map (samples n) (f := (profile n)) (by first | exact (hp n).aemeasurable | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)) atTop (𝓝 ν))
    (hactual : ∀ i u z, (profile i u).val z =
      rescaledMapProfile (J i u) (x i u) (suffix i u) (scale i)
        (fun z => F.inclusionD (F.ExpD (F.D.equiv
          ((exponentialRescaleBasis (WordBasisSelections.basis X (boundedBracketWords d) β)
            (fun j => bracketWordExponent (fun _ : I => 1) (β.val j)) (scale i)).equivFun.symm z)))) z) :
    let b := WordBasisSelections.basis X (boundedBracketWords d) β
    let cost := fun j => bracketWordExponent (fun _ : I => 1) (β.val j)
    ∀ v : H, ∃ C : ℝ≥0, ∀ f : S, f ∈ (ν : Measure S).support → ∀ z,
      LipschitzWith C (fun t : ℝ => f.val
        (dynkinFlowMap coeff (gradedCoordinateBracket b cost) (gradedGenerator b cost 1 v) (z, t))) := by
  dsimp only
  intro v
  let b := WordBasisSelections.basis X (boundedBracketWords d) β
  let cost := fun j => bracketWordExponent (fun _ : I => 1) (β.val j)
  have hv : ∀ j, b.repr v j ≠ 0 → (1 : ℝ) ≤ cost j := by
    intro j _
    have hlen (w : FreeMagma I) : 1 ≤ bracketWordLength w := by
      induction w using FreeMagma.rec with
      | of i => simp [bracketWordLength]
      | mul u w hu hw => simp only [bracketWordLength]; omega
    dsimp [cost]
    rw [bracketWordExponent_one]
    exact_mod_cast hlen (β.val j)
  apply lipschitz_supported_rescaled_flow (F.ExpD ∘ F.D.equiv) F.inclusionD b cost
    (maximizing_word_basis_bracket_weight X hDnil bD₀ (fun _ => 1) β hβ)
    coeff (model_binary_dynkin F.D.equiv F.ExpD coeff hm) v hv
    ?_ ?_ ?_ scale hscale J hJ x suffix S hS samples profile hp ν hν hactual
  · simpa only [Function.comp_apply, F.compatibleD, SetLike.val_smul] using
      continuous_exp_line_of_published_realization T ExpG hExpG realize v
  · simp [F.isExpD.map_zero]
  · intro s t
    simp only [Function.comp_apply, map_smul, F.isExpD.map_add_smul, map_mul]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanSupportedCellLipschitz
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Supported Cartan profile bounds use only samples in the carrying cell -/

noncomputable section
namespace PolycyclicRecognition

open Module LieAlgebra LieModule Filter MeasureTheory Set
open scoped Manifold Topology NNReal Matrix.Norms.Operator

variable {EG G W I A : Type} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G] [IsIsometricSMul G G]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  {ExpG : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H ExpG)

variable [NormedAddCommGroup W] [NormedSpace ℝ W] [Fintype I] [DecidableEq I]
  [MeasurableSpace A]

set_option maxHeartbeats 1000000 in
include T in
theorem lipschitz_supported_cartan_profiles_on
    (hExpG : IsGroupExponential ExpG)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (X : I → H) {d : ℕ} (hDnil : lowerCentralSeries ℝ H H d = ⊥)
    (bD₀ : Basis (Fin (finrank ℝ H)) ℝ H)
    (β : WordBasisSelections X (boundedBracketWords d))
    (hβ : IsMaximizingColumnBasis (wordListCoordinates X (boundedBracketWords d) bD₀)
      (fun w => bracketWordExponent (fun _ : I => 1) w) β.val)
    {c : ℕ} (coeff : DynkinCoefficients c 2)
    (hm : ∀ x y, F.ExpD (finiteDynkinPolynomial coeff ![x, y]) = F.ExpD x * F.ExpD y)
    (scale : ℕ → ℝ) (hscale : Tendsto scale atTop atTop)
    {K : ℝ≥0} (J : ℕ → A → G → W) (hJ : ∀ n u, LipschitzWith K (J n u))
    (x suffix : ℕ → A → G)
    (S : Set C((Fin (finrank ℝ H) → ℝ), W)) (hS : IsCompact S)
    [MeasurableSpace S] [BorelSpace S] [HasOuterApproxClosed S]
    (samples : ℕ → ProbabilityMeasure A) (profile : ℕ → A → S)
    (hp : ∀ n, Measurable (profile n)) (ν : ProbabilityMeasure S)
    (hν : Tendsto (fun n => ProbabilityMeasure.map (samples n) (f := (profile n)) (by first | exact (hp n).aemeasurable | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)) atTop (𝓝 ν))
    (C : Set A) (hC : MeasurableSet C)
    (hfull : ∀ n, ∀ᵐ a ∂(samples n : Measure A), a ∈ C)
    (hactual : ∀ i u, u ∈ C → ∀ z, (profile i u).val z =
      rescaledMapProfile (J i u) (x i u) (suffix i u) (scale i)
        (fun z => F.inclusionD (F.ExpD (F.D.equiv
          ((exponentialRescaleBasis (WordBasisSelections.basis X (boundedBracketWords d) β)
            (fun j => bracketWordExponent (fun _ : I => 1) (β.val j)) (scale i)).equivFun.symm z)))) z) :
    let b := WordBasisSelections.basis X (boundedBracketWords d) β
    let cost := fun j => bracketWordExponent (fun _ : I => 1) (β.val j)
    ∀ v : H, ∃ C : ℝ≥0, ∀ f : S, f ∈ (ν : Measure S).support → ∀ z,
      LipschitzWith C (fun t : ℝ => f.val
        (dynkinFlowMap coeff (gradedCoordinateBracket b cost) (gradedGenerator b cost 1 v) (z, t))) := by
  let restricted := fun n => supportedProbabilityRestriction (samples n) C hC (hfull n)
  have hlim : Tendsto (fun n => ProbabilityMeasure.map (restricted n)
      (f := (fun a : C => profile n a.val)) (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)) atTop (𝓝 ν) := by
    simpa only [restricted, map_supportedProbabilityRestriction _ _ _ _ _ (hp _)] using hν
  exact lipschitz_supported_cartan_profiles T F hExpG realize X hDnil bD₀ β hβ coeff hm
    scale hscale (fun n (a : C) => J n a.val) (fun n a => hJ n a.val)
    (fun n (a : C) => x n a.val) (fun n (a : C) => suffix n a.val) S hS restricted
    (fun n (a : C) => profile n a.val)
    (fun n => (hp n).comp measurable_subtype_coe) ν hlim
    (fun n a z => hactual n a.val a.property z)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanProfileAffinity
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instDecidableEqConeMixedWords _root_.OAI.PolycyclicRecognition.CartanWordModel.instFintypeConeMixedWords _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_countable _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_nonempty _root_.OAI.PolycyclicRecognition.finitelyGeneratedSubgroupIndex_countable _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.instFiniteRootOffsetConeIndex _root_.OAI.PolycyclicRecognition.instNonemptyRootOffsetConeIndex _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.unitaryCentralFixed_complete _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.CartanFactorModel.heightRay_zero _root_.OAI.PolycyclicRecognition.CartanFactorModel.realScaleProfile_apply _root_.OAI.PolycyclicRecognition.CartanFactorModel.sampledProbeProfile_apply _root_.OAI.PolycyclicRecognition.basisDynkinParameter_zero _root_.OAI.PolycyclicRecognition.bracketWordDifferential_mul _root_.OAI.PolycyclicRecognition.cartanWeightDerivation_apply_root _root_.OAI.PolycyclicRecognition.chartExponentialFlow_zero _root_.OAI.PolycyclicRecognition.derivationSemidirectHom_apply _root_.OAI.PolycyclicRecognition.exponentialHomOfDynkin_apply_exp _root_.OAI.PolycyclicRecognition.exponentialRescaleBasis_zero _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.modelNilradicalLinearAction_apply _root_.OAI.PolycyclicRecognition.modelNilradicalRotation_apply _root_.OAI.PolycyclicRecognition.modelNilradicalRotation_mul _root_.OAI.PolycyclicRecognition.modelNilradicalRotation_one _root_.OAI.PolycyclicRecognition.nilshadowWeightDerivation_symm _root_.OAI.PolycyclicRecognition.nilshadowWeightOperator_symm _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Affinity of the actual supported Cartan profiles -/

noncomputable section

namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule MeasureTheory Filter Set
open scoped Manifold Topology NNReal

attribute [local instance] stationaryL2Action zeroMeanL2Action

variable {EG G W I : Type} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G]
  [IsTopologicalGroup G] [IsIsometricSMul G G] [ProperSpace G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  [MeasurableSpace W] [BorelSpace W] [SecondCountableTopology W]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H Exp)
  (hunimod : ∀ x : GroupLieAlgebra (𝓘(ℝ, EG)) G, LinearMap.trace ℝ _ (ad ℝ _ x) = 0)
  (eW : HeightSpace T.character ≃ₗ[ℝ] W) [Fintype I] [DecidableEq I]
  {Λ : ℝ≥0} [MeasurableSpace (NormalizedPair G Λ)] [BorelSpace (NormalizedPair G Λ)]

set_option maxHeartbeats 1000000 in
theorem cartan_supported_profile_affine_sequence_oai
    [Nonempty (Fin (finrank ℝ (cartanRootIdeal H)))]
    (hExp : IsGroupExponential Exp)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
    (haarD : NilpotentExponentialHaarInput F.D.modelSpace F.D.carrier)
    (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
    (dynkinD : NilpotentDynkinExpansionInput F.D.modelSpace F.D.carrier)
    (m : Measure G) [m.IsHaarMeasure] [m.IsMulRightInvariant]
    (π : G →* Multiplicative W)
    (hπExp : ∀ x, (π (Exp x)).toAdd = eW (heightProjection T.character x))
    (hdec : ErgodicDecompositionInput G (NormalizedPair G Λ))
    (hvan : ∀ (μ : Measure (NormalizedPair G Λ)) [IsProbabilityMeasure μ]
      [ErgodicSMul G (NormalizedPair G Λ) μ],
      ReducedCohomologyInput G (ZeroMeanL2 (W := W) μ))
    (hΛ : 0 < (Λ : ℝ)) {Kπ : ℝ≥0}
    (hπ : LipschitzWith Kπ (fun g => (π g).toAdd))
    (hpath : ∀ g : G, ∃ γ : ℝ → G, γ 0 = 1 ∧ γ 1 = g ∧
      ∀ t ∈ Icc (0 : ℝ) 1, ∀ u ∈ Icc (0 : ℝ) 1,
        dist (γ t) (γ u) ≤ dist 1 g * |t - u|)
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    {E : Set W} (hE : IsCompact E) (hne : E.Nonempty) (β γ : M.Bases)
    (hβ : IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
      (M.boxCost T hunimod eW E) β.val)
    {δ c lo hi : ℝ} (hδ : 0 < δ) (hc : 0 ≤ c) (hhi : 0 ≤ hi) (ht : 0 ≤ 1 - c * δ)
    (hcost : ∀ w : M.wordList,
      lo ≤ M.boxCost T hunimod eW E w ∧ M.boxCost T hunimod eW E w ≤ hi)
    (hgap : (M.bound : ℝ) * hi < c * lo)
    (X : I → H) {d : ℕ} (hDnil : lowerCentralSeries ℝ H H d = ⊥)
    (hDletters : ∀ i : I, FreeMagma.of i ∈ boundedBracketWords d)
    (bD₀ : Basis (Fin (finrank ℝ H)) ℝ H)
    (βD : WordBasisSelections X (boundedBracketWords d))
    (hβD : IsMaximizingColumnBasis (wordListCoordinates X (boundedBracketWords d) bD₀)
      (fun w => bracketWordExponent (fun _ : I => 1) w) βD.val)
    {c₀ : ℕ} (aN : DynkinCoefficients c₀ 2)
    (hmN : ∀ x y, F.ExpN (finiteDynkinPolynomial aN ![x, y]) = F.ExpN x * F.ExpN y)
    {cD : ℕ} (aD : DynkinCoefficients cD 2)
    (hmD : ∀ x y, F.ExpD (finiteDynkinPolynomial aD ![x, y]) = F.ExpD x * F.ExpD y)
    (scale : ℕ → ℝ) (hscale : Tendsto scale atTop atTop) (hmono : StrictMono scale) (hscale1 : ∀ n, 1 ≤ scale n)
    (ε : ℕ → ℝ) (hεpos : ∀ r, 0 ≤ ε r) (hε : Tendsto ε atTop (𝓝 0))
    (k : ℕ → cartanRootIdeal H)
    (hk : ∀ᶠ r : ℕ in atTop,
      ‖(exponentialRescaleBasis (WordBasisSelections.basis M.letter M.wordList β)
        (fun i => (1 + δ) * M.boxCost T hunimod eW E (β.val i)) (scale r)).equivFun (k r)‖ ≤
          Real.exp (scale r * ε r))
    (rem : RemezPolynomialInput) (hdim : 1 ≤ finrank ℝ (cartanRootIdeal H))
    (p : ℕ → NormalizedPair G Λ) (x : ℕ → G)
    (S : Set C((Fin (finrank ℝ H) → ℝ), W))
    (hS : IsCompact S)
    [MeasurableSpace S] [BorelSpace S] [HasOuterApproxClosed S]
    (profile : ℕ → (Fin (finrank ℝ (cartanRootIdeal H)) → ℝ) → S)
    (hp : ∀ n, Measurable (profile n))
    (hactual : ∀ n y, y ∈ Icc (fun _ : Fin (finrank ℝ (cartanRootIdeal H)) => (-1 : ℝ)) (fun _ => (1 : ℝ)) → ∀ z, (profile n y).val z =
      rescaledMapProfile (fun g => (π ((p n).val.1 g)).toAdd) (x n)
        (F.inclusionN (F.ExpN (F.N.equiv
          ((M.boxBasis T hunimod eW E β (scale n)).equivFun.symm y))) *
            F.inclusionN (F.ExpN (F.N.equiv (k n))))
        (max (Real.log (scale n)) 0)
        (fun z => F.inclusionD (F.ExpD (F.D.equiv
          ((exponentialRescaleBasis (WordBasisSelections.basis X (boundedBracketWords d) βD)
            (fun j => bracketWordExponent (fun _ : I => 1) (βD.val j))
            (max (Real.log (scale n)) 0)).equivFun.symm z)))) z)
    (ν : ProbabilityMeasure S)
    (hν : Tendsto (fun n => ProbabilityMeasure.map
      (cellProbabilityMeasure volume (Icc (fun _ => (-1 : ℝ)) (fun _ => (1 : ℝ)))
        (coordinate_cube_mass zero_lt_one).1 (coordinate_cube_mass zero_lt_one).2)
      (f := (profile n)) (by first | exact (hp n).aemeasurable | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)) atTop (𝓝 ν))
    (U : Set (Fin (finrank ℝ H) → ℝ)) (hU : IsOpen U)
    (hconn : IsPreconnected U) (hUne : U.Nonempty)
    (hUheight : ∀ z ∈ U, eW (heightProjection T.character
      ((WordBasisSelections.basis X (boundedBracketWords d) βD).equivFun.symm z :
        GroupLieAlgebra (𝓘(ℝ, EG)) G)) ∈ (fun w => (1 - c * δ) • w) '' E)
    (σ : Fin M.letterCount → Bool)
    (hσ : (weightChamber (fun i =>
      ((M.supportIn T hunimod eW).weight i).toContinuousLinearMap) σ).Nonempty) :
    ∀ (f : S), f ∈ (ν : Measure S).support →
      ∃ (A : templateSymmetryGroup (M.supportIn T hunimod eW)) (b : W),
        ∀ z ∈ U, f.val z = A.val (eW (heightProjection T.character
          ((WordBasisSelections.basis X (boundedBracketWords d) βD).equivFun.symm z :
            GroupLieAlgebra (𝓘(ℝ, EG)) G))) + b := by
  classical
  let bD := WordBasisSelections.basis X (boundedBracketWords d) βD
  let cost := fun j => bracketWordExponent (fun _ : I => 1) (βD.val j)
  let br := gradedCoordinateBracket bD cost
  let P := M.supportIn T hunimod eW
  let h : H →ₗ[ℝ] W := eW.toLinearMap.comp ((heightProjection T.character).comp H.subtype)
  let pH := (h.comp bD.equivFun.symm.toLinearMap).toContinuousLinearMap
  let D := ((gradedGeneratorLinearMap bD cost 1).comp bD.equivFun.symm.toLinearMap).toContinuousLinearMap
  have hh (v w : H) : h ⁅v, w⁆ = 0 := by
    change eW (heightProjection T.character (⁅v, w⁆ : H)) = 0
    rw [LieSubalgebra.coe_bracket, heightProjection_lie_eq_zero T.character T.character_lie,
      map_zero]
  have hweight := maximizing_word_basis_bracket_weight X hDnil bD₀ (fun _ => 1) βD hβD
  obtain ⟨⟨chartD, hchartD⟩, _⟩ := haarD.2 F.ExpD F.isExpD
    (F.D.tangent_nilpotent inferInstance)
  let ExpH := fun v : H => F.inclusionD (F.ExpD (F.D.equiv v))
  have hExpH (v : H) : ExpH v = Exp v := F.compatibleD v
  have hinj : Function.Injective ExpH := F.closedD.injective.comp
    (((funext hchartD ▸ chartD.bijective).comp F.D.equiv.bijective).injective)
  have hzero : ExpH 0 = 1 := by simp [ExpH, F.isExpD.map_zero]
  have hneg (v : H) : ExpH (-v) = (ExpH v)⁻¹ := by simp [ExpH, F.isExpD.map_neg]
  have hadd (v : H) (s t : ℝ) : ExpH ((s + t) • v) = ExpH (s • v) * ExpH (t • v) := by
    simp only [ExpH, map_smul, F.isExpD.map_add_smul, map_mul]
  have hmul (v w : H) : ExpH (finiteDynkinPolynomial aD ![v, w]) = ExpH v * ExpH w :=
    (congrArg F.inclusionD (model_binary_dynkin F.D.equiv F.ExpD aD hmD v w)).trans
      (map_mul F.inclusionD _ _)
  have hπH (v : H) : (π (ExpH v)).toAdd = h v := by
    rw [hExpH, hπExp]
    rfl
  have hg : PolynomialGroupLaws (dynkinProduct aD br) :=
    gradedCoordinateBracket_groupLaws bD cost hweight ExpH hinj hzero hneg hadd aD hmul
  have hconj := cartan_graded_conjugation T F hExp realize haarD bD cost hweight aD hmD
  have hheight (v w) : pH (dynkinProduct aD br v w) = pH v + pH w :=
    gradedWordChartProduct_height X (boundedBracketWords d) βD h hh ExpH π hπH aD hmul hweight v w
  let π₀ := polynomialCoordinateHeightHom (dynkinProduct aD br) hg pH hheight
  have hDheight (v : Fin (finrank ℝ H) → ℝ) : pH (D v) = h (bD.equivFun.symm v) :=
    gradedGenerator_word_height X (boundedBracketWords d) βD h hh (bD.equivFun.symm v)
  have hsurj : Function.Surjective (pH.comp D) := by
    intro w
    obtain ⟨v, hv⟩ := (eW.surjective.comp (cartan_height_surjective T H)) w
    refine ⟨bD.equivFun v, ?_⟩
    change pH (D (bD.equivFun v)) = w
    rw [hDheight, bD.equivFun.symm_apply_apply]
    exact hv
  let e := PolynomialCoordinateGroup.expHomeomorph (dynkinProduct aD br) hg
  let μ := Measure.map e volume
  have hmeasure := polynomialCoordinate_haar_of_right_translations (dynkinProduct aD br) hg
    (continuous_dynkinProduct aD (fun _ => br) Prod.fst Prod.snd
      continuous_const continuous_fst continuous_snd)
    (fun q => measurePreserving_model_graded_dynkin_right F.D.equiv haarD F.ExpD F.isExpD
      inferInstance bD cost hweight aD hmD q)
  have hhaar : μ.IsHaarMeasure := hmeasure.1
  have hright : μ.IsMulRightInvariant := hmeasure.2
  let : μ.IsHaarMeasure := hhaar
  let : μ.IsMulRightInvariant := hright
  let L := templateSymmetryGroup P
  let : Fintype L := Fintype.ofFinite L
  let : MeasurableSpace L := ⊤
  have hweights (i : Fin M.letterCount) : P.weight i ≠ 0 := by
    intro hz
    apply M.weight_nonzero i
    funext v
    have hv := congrArg (fun q : W →ₗ[ℝ] ℝ => q (eW (heightProjection T.character v))) hz
    simpa only [P, supportIn, SupportDatum.transport_weight_apply, supportDatum_weight,
      eW.symm_apply_apply, cartanHeightWeight_projection, LinearMap.zero_apply,
      Pi.zero_apply] using hv
  let logscale := fun n => max (Real.log (scale n)) 0
  have hlogscale : Tendsto logscale atTop atTop :=
    tendsto_atTop_mono (fun n => le_max_left _ _) (Real.tendsto_log_atTop.comp hscale)
  let samples : ProbabilityMeasure (Fin (finrank ℝ (cartanRootIdeal H)) → ℝ) := cellProbabilityMeasure volume
    (Icc (fun _ => (-1 : ℝ)) (fun _ => (1 : ℝ)))
    (coordinate_cube_mass zero_lt_one).1 (coordinate_cube_mass zero_lt_one).2
  let J := fun n (_ : Fin (finrank ℝ (cartanRootIdeal H)) → ℝ) (g : G) =>
    (π ((p n).val.1 g)).toAdd
  have hJ (n : ℕ) (y : Fin (finrank ℝ (cartanRootIdeal H)) → ℝ) :
      LipschitzWith (Kπ * Λ) (J n y) := hπ.comp (p n).property.1.1
  let suffixN : ℕ → (Fin (finrank ℝ (cartanRootIdeal H)) → ℝ) → G := fun n y => F.inclusionN (F.ExpN (F.N.equiv
    ((M.boxBasis T hunimod eW E β (scale n)).equivFun.symm y))) *
      F.inclusionN (F.ExpN (F.N.equiv (k n)))
  have hlip := lipschitz_supported_cartan_profiles_on T F hExp realize X hDnil bD₀ βD hβD
    aD hmD logscale hlogscale J hJ (fun n _ => x n) suffixN S hS (fun _ => samples)
    profile hp ν hν (Icc (fun _ : Fin (finrank ℝ (cartanRootIdeal H)) => (-1 : ℝ)) (fun _ => (1 : ℝ))) measurableSet_Icc
    (fun _ => ae_mem_cellProbabilityMeasure volume _ measurableSet_Icc _ _) hactual
  choose C hC using hlip
  have hDX (i : I) : D (bD.equivFun (X i)) = gradedGenerator bD cost 1 (X i) := by
    change gradedGenerator bD cost 1 (bD.equivFun.symm (bD.equivFun (X i))) = _
    rw [bD.equivFun.symm_apply_apply]
  have hwords (j : Fin (finrank ℝ H)) :
      evalBilinearWord br (fun i => D (bD.equivFun (X i))) (βD.val j) =
        Pi.basisFun ℝ (Fin (finrank ℝ H)) j := by
    simp only [hDX]
    simpa only [Pi.basisFun_apply] using
      graded_generators_word_normalization X hDnil hDletters bD₀ (fun _ => 1) βD hβD j
  intro f hf
  apply affine_profile_of_segment_inequalities aD br
    (isLieBracket_gradedCoordinateBracket bD cost hweight) hg hconj D (Pi.basisFun ℝ (Fin (finrank ℝ H)))
    (fun i => bD.equivFun (X i)) (Pi.basisFun ℝ (Fin (finrank ℝ H)))
    (fun j => (βD.val j : FreeMagma I)) hwords
    μ U hU hconn hUne f.val f.val.continuous π₀ pH hsurj (fun _ => rfl) P hweights σ hσ
    (fun A : L => A) (fun v => C (bD.equivFun.symm v))
    (fun v z => (hC (bD.equivFun.symm v) f hf z).lipschitzOnWith) ?_
  intro v₀ T₀ hT z hseg
  let v := bD.equivFun.symm v₀
  have hseg' : ∀ t ∈ Icc 0 T₀,
      dynkinFlowMap aD br (gradedGenerator bD cost 1 v) (z, t) ∈ U := hseg
  rw [hDheight]
  constructor
  · apply M.cartan_profile_increment_mem_template_sequence T F hunimod eW
      hExp realize haarN haarD dynkinN dynkinD m π hπExp hdec hvan hΛ hπ hpath
      b₀ hE hne β γ hβ hδ hc hhi ht hcost hgap X hDnil hDletters bD₀ βD hβD
      aN hmN aD hmD scale hscale hmono ε hεpos hε k hk
      (C := Icc (fun _ => (-1 : ℝ)) (fun _ => (1 : ℝ)))
      (measurableSet_Icc) (coordinate_cube_mass zero_lt_one).1 (coordinate_cube_mass zero_lt_one).2
      p x v S hS profile hp ?_ ν hν hU hUheight z hT hseg' hf
    intro n y hy z
    simpa only [max_eq_left ((hscale1 n).trans' zero_le_one)] using hactual n y hy z
  · exact M.cartan_profile_segment_volume_sequence T F hunimod eW
      hExp realize haarN haarD dynkinN dynkinD π hπExp hΛ hπ hpath b₀ hE hne β hβ
      hδ hc hhi ht hcost hgap X hDnil bD₀ βD hβD aN hmN aD hmD
      scale hscale hmono hscale1 ε hεpos hε k hk rem hdim p x S profile hp hactual
      ν hν v z T₀ hT U hU hUheight hseg' f hf

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

theorem solution : type_of% @OAI.PolycyclicRecognition.CartanWordModel.cartan_supported_profile_affine_sequence_oai := @OAI.PolycyclicRecognition.CartanWordModel.cartan_supported_profile_affine_sequence_oai
