-- Prove2me | solution 1 for OAI.PolycyclicRecognition.ComplexWeightFactorModel.exists_faithful_rotation_triangular_representation
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-03T01:07:31.553608+00:00
-- url     : https://prove2.me/submissions/88f324ec-901c-4897-96fa-9f58bdae54db

import Mathlib
import Definitions.Def_PolycyclicRecognition
import Definitions.Def_OAIQ093D023
import Theorems.Thm_OAI_PolycyclicRecognition_ComplexWeightFactorModel_exists_integrated_rotation_representation
import Theorems.Thm_OAI_PolycyclicRecognition_ComplexWeightFactorModel_rotationRepresentation_faithful

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_BasisQuotientLifts
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A basis adapted to specified quotient lifts -/

noncomputable section
namespace PolycyclicRecognition

open Module Set

variable {𝕜 : Type*} [Field 𝕜]

variable {V I J : Type*} [AddCommGroup V] [Module 𝕜 V] (U : Submodule 𝕜 V)
  (bU : Basis I 𝕜 U) (bQ : Basis J 𝕜 (V ⧸ U))
  (lift : J → V) (hlift : ∀ j, U.mkQ (lift j) = bQ j)

theorem basisWithQuotientLifts_repr_inr (v : V) (j : J) :
    (basisWithQuotientLifts U bU bQ lift hlift).repr v (Sum.inr j) =
      bQ.repr (U.mkQ v) j := by
  classical
  let b := basisWithQuotientLifts U bU bQ lift hlift
  have hf : b.coord (Sum.inr j) = (bQ.coord j).comp U.mkQ := by
    apply b.ext
    intro k
    cases k with
    | inl i =>
      change b.repr (b (Sum.inl i)) (Sum.inr j) = bQ.repr (U.mkQ (b (Sum.inl i))) j
      rw [Basis.repr_self]
      have hz : U.mkQ (b (Sum.inl i)) = 0 := by
        rw [basisWithQuotientLifts_inl]
        exact (Submodule.Quotient.mk_eq_zero U).mpr (bU i).property
      rw [hz, map_zero]
      simp
    | inr i =>
      change b.repr (b (Sum.inr i)) (Sum.inr j) = bQ.repr (U.mkQ (b (Sum.inr i))) j
      rw [Basis.repr_self, basisWithQuotientLifts_inr, hlift, Basis.repr_self]
      simp only [Finsupp.single_apply, Sum.inr.injEq]
  exact congrArg (fun f : V →ₗ[𝕜] 𝕜 => f v) hf

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_BoundedWordAlgebra
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite algebras from a bound on generator products

This is the finite-dimensionality step for the truncated enveloping algebra
used to extend a nilpotent representation by derivations.
-/

noncomputable section
namespace PolycyclicRecognition

open Set

variable {R A : Type*} [Field R] [Ring A] [Algebra R A]
  {ι : Type*} [Fintype ι] (j : ι → A) (c : ℕ)

theorem boundedWordProducts_finite : (boundedWordProducts j c).Finite :=
  Set.finite_range _

omit [Fintype ι] in
theorem list_prod_mem_boundedWordSpan
    (hnil : ∀ l : List ι, c < l.length → (l.map j).prod = 0) (l : List ι) :
    (l.map j).prod ∈ Submodule.span R (boundedWordProducts j c) := by
  by_cases hl : l.length ≤ c
  · apply Submodule.subset_span
    refine ⟨⟨⟨l.length, Nat.lt_succ_of_le hl⟩, l.get⟩, ?_⟩
    change (List.ofFn (j ∘ l.get)).prod = _
    rw [← List.map_ofFn, List.ofFn_get]
  · rw [hnil l (Nat.lt_of_not_ge hl)]
    exact Submodule.zero_mem _

omit [Fintype ι] in
theorem adjoin_le_boundedWordSpan
    (hnil : ∀ l : List ι, c < l.length → (l.map j).prod = 0) :
    (Algebra.adjoin R (Set.range j)).toSubmodule ≤
      Submodule.span R (boundedWordProducts j c) := by
  rw [Algebra.adjoin_eq_span]
  apply Submodule.span_le.mpr
  intro x hx
  have hword : ∃ l : List ι, (l.map j).prod = x := by
    induction hx using Submonoid.closure_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      exact ⟨[i], by simp⟩
    | one => exact ⟨[], by simp⟩
    | mul x y _ _ hx hy =>
      obtain ⟨l, rfl⟩ := hx
      obtain ⟨k, rfl⟩ := hy
      exact ⟨l ++ k, by simp⟩
  obtain ⟨l, rfl⟩ := hword
  exact list_prod_mem_boundedWordSpan j c hnil l

theorem finiteDimensional_of_bounded_generator_products
    (hgen : Algebra.adjoin R (Set.range j) = ⊤)
    (hnil : ∀ l : List ι, c < l.length → (l.map j).prod = 0) :
    FiniteDimensional R A := by
  have hspan : Submodule.span R (boundedWordProducts j c) = ⊤ := by
    apply top_unique
    have h := adjoin_le_boundedWordSpan (R := R) j c hnil
    rw [hgen] at h
    exact h
  apply Module.Finite.of_fg_top
  rw [← hspan]
  exact Submodule.fg_span (boundedWordProducts_finite j c)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_ChooseFaithfulMatrixRepresentation
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Choosing a faithful integration without expanding its source group -/

noncomputable section
namespace PolycyclicRecognition
open scoped Matrix.Norms.Operator
attribute [local instance 100] LieRing.ofAssociativeRing

variable {L Γ X Y : Type} [LieRing L] [LieAlgebra ℝ L]
  [Group Γ] [TopologicalSpace Γ]

theorem exists_faithful_matrix_integration
    (Q : ∀ m, (L →ₗ⁅ℝ⁆ Matrix (Fin m) (Fin m) ℝ) → Prop)
    (u : X → L) (v : Y → L) (f : X → Y → Γ)
    (hq : ∃ m, 0 < m ∧ ∃ j, Q m j)
    (hi : ∀ m j, Q m j →
      ∃ ρ : Γ →* (Matrix (Fin m) (Fin m) ℝ)ˣ, Continuous ρ ∧
        ∀ x y, ρ (f x y) = algebraExpUnit (j (u x)) * algebraExpUnit (j (v y)))
    (hf : ∀ m j, Q m j → ∀ ρ : Γ →* (Matrix (Fin m) (Fin m) ℝ)ˣ,
      (∀ x y, ρ (f x y) = algebraExpUnit (j (u x)) * algebraExpUnit (j (v y))) →
      Function.Injective ρ) :
    ∃ m, 0 < m ∧ ∃ j, Q m j ∧
      ∃ ρ : Γ →* (Matrix (Fin m) (Fin m) ℝ)ˣ, Continuous ρ ∧ Function.Injective ρ ∧
        ∀ x y, ρ (f x y) = algebraExpUnit (j (u x)) * algebraExpUnit (j (v y)) := by
  obtain ⟨m,hm,j,hj⟩ := hq
  obtain ⟨ρ,hρ,he⟩ := hi m j hj
  exact ⟨m,hm,j,hj,ρ,hρ,hf m j hj ρ he,he⟩

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_NilpotentPolynomialRepresentation
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.abelianRealCoordinates _root_.OAI.PolycyclicRecognition.abelianRealFiniteDimensional _root_.OAI.PolycyclicRecognition.abelianRealLieAbelian _root_.OAI.PolycyclicRecognition.abelianRealNormedLie _root_.OAI.PolycyclicRecognition.derivationLieSpaceFiniteDimensional _root_.OAI.PolycyclicRecognition.derivationLieSpaceRealNormed _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.polynomialLieIdealSubgroup_normal _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Nilpotence of the faithful polynomial representation

The representation is polynomial on every straight one-parameter subgroup.
The actual Lie differential therefore consists of nilpotent matrices.
-/

noncomputable section
namespace PolycyclicRecognition

open scoped Matrix.Norms.Operator
attribute [local instance 100] LieRing.ofAssociativeRing

variable {L : Type*} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  [P : PolynomialExponentialCoordinates L] {n m : ℕ}
  (b : Module.Basis (Fin n) ℝ L)
  (B : (Fin m → ℝ) ≃ₗ[ℝ] coordinateOrbitSpan (polynomialModelCoordinate b))

include b in
theorem exists_faithful_nilpotent_matrixLieRepresentation :
    ∃ (m : ℕ) (j : L →ₗ⁅ℝ⁆ Matrix (Fin m) (Fin m) ℝ),
      Function.Injective j ∧ ∀ x, IsNilpotent (j x) := by
  let := finiteDimensional_polynomialModelOrbit b
  let m := Module.finrank ℝ (coordinateOrbitSpan (polynomialModelCoordinate b))
  let B : (Fin m → ℝ) ≃ₗ[ℝ] coordinateOrbitSpan (polynomialModelCoordinate b) :=
    (Module.finBasis ℝ (coordinateOrbitSpan (polynomialModelCoordinate b))).equivFun.symm
  exact ⟨m, polynomialMatrixLieRepresentation b B,
    polynomialMatrixLieRepresentation_injective b B,
    polynomialMatrixLieRepresentation_nilpotent b B⟩

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_NilpotentFaithfulRepresentation
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.abelianRealCoordinates _root_.OAI.PolycyclicRecognition.abelianRealFiniteDimensional _root_.OAI.PolycyclicRecognition.abelianRealLieAbelian _root_.OAI.PolycyclicRecognition.abelianRealNormedLie _root_.OAI.PolycyclicRecognition.derivationLieSpaceFiniteDimensional _root_.OAI.PolycyclicRecognition.derivationLieSpaceRealNormed _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.polynomialLieIdealSubgroup_normal _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A faithful nilpotent matrix representation of a real nilpotent algebra

The coordinate model and its regular representation have both been constructed
without a published-input hypothesis. Engel gives a uniform product bound.
-/

noncomputable section
namespace PolycyclicRecognition

attribute [local instance 100] LieRing.ofAssociativeRing

theorem exists_faithful_nilpotent_representation (L : Type) [RealNormedLieAlgebra L]
    [FiniteDimensional ℝ L] (hnil : LieRing.IsNilpotent L) :
    ∃ (m c : ℕ) (j : L →ₗ⁅ℝ⁆ Matrix (Fin m) (Fin m) ℝ),
      Function.Injective j ∧ (∀ x, IsNilpotent (j x)) ∧
      ∀ l : List L, c ≤ l.length → (l.map j).prod = 0 := by
  obtain ⟨P⟩ := polynomialExponentialCoordinates_nilpotent L hnil
  let := P
  obtain ⟨m, j, hj, hn⟩ := exists_faithful_nilpotent_matrixLieRepresentation (Module.finBasis ℝ L)
  obtain ⟨c, hc⟩ := exists_vanishing_matrix_products_of_pointwise_nilpotent j hn
  exact ⟨m, c, j, hj, hn, hc⟩

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_TruncatedEnvelopingAlgebra
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The finite truncated enveloping algebra and its faithful generators

A given nilpotent representation bounds the truncation degree and certifies
injectivity. No PBW theorem or additional representation input is assumed.
-/

noncomputable section
namespace PolycyclicRecognition

open Module

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]

attribute [local instance 100] LieRing.ofAssociativeRing

local notation "U" => UniversalEnvelopingAlgebra R L
local notation "η" => UniversalEnvelopingAlgebra.ι R (L := L)

theorem truncatedEnvelopingProjection_eq_zero (c : ℕ) (u : U) :
    truncatedEnvelopingProjection c u = 0 ↔ u ∈ envelopingTruncationIdeal (R := R) c :=
  RingCon.eq _

theorem truncatedEnvelopingGenerator_prod_eq_zero (c : ℕ) (l : List L)
    (hl : c ≤ l.length) : (l.map (truncatedEnvelopingGenerator (R := R) c)).prod = 0 := by
  have h := (truncatedEnvelopingProjection_eq_zero c _).mpr
    (longWord_mem_envelopingTruncationIdeal (R := R) c l hl)
  simpa only [map_list_prod, List.map_map, Function.comp_def,
    truncatedEnvelopingGenerator, LieHom.coe_comp, AlgHom.coe_toLieHom] using h

theorem truncatedEnveloping_adjoin_basis {ι : Type*} [Fintype ι]
    (b : Basis ι R L) (c : ℕ) :
    Algebra.adjoin R (Set.range fun i => truncatedEnvelopingGenerator (R := R) c (b i)) = ⊤ := by
  classical
  let S := Algebra.adjoin R
    (Set.range fun i => truncatedEnvelopingGenerator (R := R) c (b i))
  have hgen (x : L) : truncatedEnvelopingGenerator (R := R) c x ∈ S := by
    rw [← b.sum_repr x]
    simp only [map_sum, map_smul]
    apply S.sum_mem
    intro i _
    apply S.smul_mem
    exact Algebra.subset_adjoin (s := Set.range fun i =>
      truncatedEnvelopingGenerator (R := R) c (b i)) ⟨i, rfl⟩
  apply top_unique
  intro z hz
  clear hz
  obtain ⟨u, rfl⟩ := truncatedEnvelopingProjection_surjective (R := R) (L := L) c z
  induction u using enveloping_induction with
  | hscalar r => exact S.algebraMap_mem r
  | hgen x => exact hgen x
  | hadd a b ha hb => exact S.add_mem ha hb
  | hmul a b ha hb => exact S.mul_mem ha hb

theorem truncatedEnvelopingGenerator_injective {A : Type*} [Ring A] [Algebra R A]
    (c : ℕ) (j : L →ₗ⁅R⁆ A) (hj : Function.Injective j)
    (hnil : ∀ l : List L, c ≤ l.length → (l.map j).prod = 0) :
    Function.Injective (truncatedEnvelopingGenerator (R := R) (L := L) c) := by
  let f : U →ₐ[R] A := UniversalEnvelopingAlgebra.lift R j
  have hk {u : U} (hu : u ∈ envelopingTruncationIdeal (R := R) c) : f u = 0 := by
    induction hu using TwoSidedIdeal.span_induction with
    | mem u hu =>
      obtain ⟨l, hl, rfl⟩ := hu
      dsimp only [f]
      simpa only [map_list_prod, List.map_map, Function.comp_def,
        UniversalEnvelopingAlgebra.lift_ι_apply] using hnil l hl
    | zero => exact map_zero f
    | add a b _ _ ha hb => rw [map_add, ha, hb, add_zero]
    | neg a _ ha => rw [map_neg, ha, neg_zero]
    | left_absorb a b _ hb => rw [map_mul, hb, mul_zero]
    | right_absorb b a _ ha => rw [map_mul, ha, zero_mul]
  intro x y hxy
  apply hj
  have hrel : (envelopingTruncationIdeal (R := R) c).ringCon (η x) (η y) :=
    (RingCon.eq _).mp hxy
  have hz := hk (((envelopingTruncationIdeal (R := R) c).rel_iff _ _).mp hrel)
  simpa only [map_sub, f, UniversalEnvelopingAlgebra.lift_ι_apply, sub_eq_zero] using hz

section FiniteDimensional
variable {K : Type*} [Field K] [LieAlgebra K L]

theorem finiteDimensional_truncatedEnvelopingAlgebra {ι : Type*} [Fintype ι]
    (b : Basis ι K L) (c : ℕ) : FiniteDimensional K (TruncatedEnvelopingAlgebra K L c) := by
  apply finiteDimensional_of_bounded_generator_products
    (fun i => truncatedEnvelopingGenerator (R := K) c (b i)) c
    (truncatedEnveloping_adjoin_basis b c)
  intro l hl
  have h := truncatedEnvelopingGenerator_prod_eq_zero (R := K) c (l.map b)
    (by simpa only [List.length_map] using hl.le)
  simpa only [List.map_map, Function.comp_def] using h

end FiniteDimensional
end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_TruncatedSemidirectRepresentation
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Representing a semidirect extension on the truncated enveloping algebra -/

noncomputable section
namespace PolycyclicRecognition

open LieAlgebra

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]

attribute [local instance 100] LieRing.ofAssociativeRing

local notation "Q" => TruncatedEnvelopingAlgebra R L

variable {H : Type*} [LieRing H] [LieAlgebra R H]

theorem truncatedSemidirectRepresentation_injective (c : ℕ)
    (ψ : H →ₗ⁅R⁆ LieDerivation R L L) (hψ : Function.Injective ψ)
    (hgen : Function.Injective (truncatedEnvelopingGenerator (R := R) (L := L) c)) :
    Function.Injective (truncatedSemidirectRepresentation c ψ) := by
  intro p q hpq
  have hl : p.left = q.left := by
    apply hgen
    have h := DFunLike.congr_fun hpq 1
    change truncatedEnvelopingGenerator c p.left * 1 +
      truncatedEnvelopingDerivation c (ψ p.right) 1 =
      truncatedEnvelopingGenerator c q.left * 1 +
      truncatedEnvelopingDerivation c (ψ q.right) 1 at h
    simpa only [mul_one, truncatedEnvelopingDerivation_one, add_zero] using h
  have hd : truncatedEnvelopingDerivation c (ψ p.right) =
      truncatedEnvelopingDerivation c (ψ q.right) := by
    change truncatedLeftRepresentation (R := R) c p.left +
      truncatedEnvelopingDerivation c (ψ p.right) =
      truncatedLeftRepresentation (R := R) c q.left +
      truncatedEnvelopingDerivation c (ψ q.right) at hpq
    rw [hl] at hpq
    exact add_left_cancel hpq
  have hr : p.right = q.right := by
    apply hψ
    apply LieDerivation.ext
    intro x
    apply hgen
    have h := DFunLike.congr_fun hd (truncatedEnvelopingGenerator c x)
    simpa only [truncatedEnvelopingDerivation_generator] using h
  exact SemiDirectSum.ext hl hr

theorem truncatedLeftRepresentation_nilpotent (c : ℕ) (x : L) :
    IsNilpotent (truncatedLeftRepresentation (R := R) c x) := by
  have hq : (truncatedEnvelopingGenerator (R := R) c x) ^ c = 0 := by
    simpa only [List.map_replicate, List.prod_replicate] using
      truncatedEnvelopingGenerator_prod_eq_zero (R := R) c (List.replicate c x)
        (by simp only [List.length_replicate, le_refl])
  refine ⟨c, ?_⟩
  change (Algebra.lmul R (Q c) (truncatedEnvelopingGenerator c x)) ^ c = 0
  rw [← map_pow, hq, map_zero]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_FaithfulTruncatedEnveloping
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.abelianRealFiniteDimensional _root_.OAI.PolycyclicRecognition.abelianRealLieAbelian _root_.OAI.PolycyclicRecognition.abelianRealNormedLie _root_.OAI.PolycyclicRecognition.derivationLieSpaceFiniteDimensional _root_.OAI.PolycyclicRecognition.derivationLieSpaceRealNormed _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.polynomialLieIdealSubgroup_normal _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A faithful nilpotent representation compatible with derivations

A faithful nilpotent representation determines a truncation degree.
The resulting finite representation carries the full derivation action,
as required for a solvable extension.
-/

noncomputable section
namespace PolycyclicRecognition

open Module

theorem exists_faithful_truncated_enveloping (L : Type) [RealNormedLieAlgebra L]
    [FiniteDimensional ℝ L] (hnil : LieRing.IsNilpotent L) :
    ∃ c : ℕ, FiniteDimensional ℝ (TruncatedEnvelopingAlgebra ℝ L c) ∧
      Function.Injective (truncatedEnvelopingGenerator (R := ℝ) (L := L) c) := by
  obtain ⟨m, c, j, hj, _, hc⟩ := exists_faithful_nilpotent_representation L hnil
  exact ⟨c, finiteDimensional_truncatedEnvelopingAlgebra (finBasis ℝ L) c,
    truncatedEnvelopingGenerator_injective c j hj hc⟩

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_FilteredPolynomialPerturbation
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial annihilators under a filtration-raising perturbation

If `D` preserves a finite descending filtration and `N` raises its level,
then a polynomial annihilating `D`, evaluated at `D + N`, raises its level.
Consequently a power of that polynomial annihilates `D + N`.
-/

noncomputable section
namespace PolycyclicRecognition

open Polynomial

variable {V : Type*} [AddCommGroup V] [Module ℝ V]
  (B : ℕ → Submodule ℝ V) (D N : Module.End ℝ V)
  (hB : Antitone B)
  (hD : ∀ k v, v ∈ B k → D v ∈ B k)
  (hN : ∀ k v, v ∈ B k → N v ∈ B (k + 1))

include hB hD hN

theorem filtered_sum_maps (k : ℕ) (v : V) (hv : v ∈ B k) : (D + N) v ∈ B k := by
  exact (B k).add_mem (hD k v hv) (hB (Nat.le_succ k) (hN k v hv))

theorem filtered_sum_pow_maps (a k : ℕ) (v : V) (hv : v ∈ B k) :
    ((D + N) ^ a) v ∈ B k := by
  induction a with
  | zero => simpa only [pow_zero, Module.End.one_apply] using hv
  | succ a ha =>
    rw [pow_succ', Module.End.mul_apply]
    exact filtered_sum_maps B D N hB hD hN k _ ha

theorem filtered_pow_difference (a k : ℕ) (v : V) (hv : v ∈ B k) :
    ((D + N) ^ a) v - (D ^ a) v ∈ B (k + 1) := by
  induction a with
  | zero => simpa only [pow_zero, sub_self] using (B (k + 1)).zero_mem
  | succ a ha =>
    rw [pow_succ', pow_succ', Module.End.mul_apply, Module.End.mul_apply,
      LinearMap.add_apply]
    have heq : D (((D + N) ^ a) v) + N (((D + N) ^ a) v) - D ((D ^ a) v) =
        D (((D + N) ^ a) v - (D ^ a) v) + N (((D + N) ^ a) v) := by
      rw [map_sub]
      abel
    rw [heq]
    exact (B (k + 1)).add_mem (hD _ _ ha)
      (hN _ _ (filtered_sum_pow_maps B D N hB hD hN a k v hv))

theorem filtered_polynomial_difference (p : ℝ[X]) (k : ℕ) (v : V) (hv : v ∈ B k) :
    aeval (D + N) p v - aeval D p v ∈ B (k + 1) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    simp only [map_add, LinearMap.add_apply]
    have heq : aeval (D + N) p v + aeval (D + N) q v -
        (aeval D p v + aeval D q v) =
        (aeval (D + N) p v - aeval D p v) + (aeval (D + N) q v - aeval D q v) := by abel
    rw [heq]
    exact (B (k + 1)).add_mem hp hq
  | monomial a r =>
    simp only [aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply]
    rw [← smul_sub]
    exact (B (k + 1)).smul_mem r (filtered_pow_difference B D N hB hD hN a k v hv)

theorem filtered_polynomial_annihilator (c : ℕ) (hzero : B 0 = ⊤) (hc : B c = ⊥)
    (p : ℝ[X]) (hp : aeval D p = 0) : aeval (D + N) (p ^ c) = 0 := by
  have hraise (k : ℕ) (v : V) (hv : v ∈ B k) : aeval (D + N) p v ∈ B (k + 1) := by
    simpa only [hp, LinearMap.zero_apply, sub_zero] using
      filtered_polynomial_difference B D N hB hD hN p k v hv
  have hpow (k : ℕ) (v : V) : ((aeval (D + N) p) ^ k) v ∈ B k := by
    induction k with
    | zero => rw [hzero]; trivial
    | succ k hk =>
      rw [pow_succ', Module.End.mul_apply]
      exact hraise k _ hk
  rw [map_pow]
  ext v
  have h := hpow c v
  rw [hc, Submodule.mem_bot] at h
  exact h

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_ComplexCartanJordan
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The semisimple Cartan operator preserves the original triangular flag -/

noncomputable section
namespace PolycyclicRecognition.ComplexCartan
open LieAlgebra LieModule Module

variable {L : Type*} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L]
  (H : LieSubalgebra ℂ L) [H.IsCartanSubalgebra]

set_option maxHeartbeats 1000000 in
theorem semisimpleOperator_apply (h : H) (χ : Weight ℂ H L) {x : L}
    (hx : x ∈ genWeightSpace L χ) : semisimpleOperator H h x = χ h • x :=
  weightOperator_apply H _ χ hx

set_option maxHeartbeats 1000000 in
/-- The root-space scalar operator is precisely the Jordan semisimple part. -/
theorem semisimpleOperator_jordan (h : H) :
    semisimpleOperator H h ∈ Algebra.adjoin ℂ {ad ℂ L (h : L)} ∧
      IsNilpotent (ad ℂ L (h : L) - semisimpleOperator H h) := by
  obtain ⟨N,hN,S,hS,hnil,hss,hsum⟩ := (ad ℂ L (h : L)).exists_isNilpotent_isSemisimple
  have hc : Commute (ad ℂ L (h : L)) S :=
    Algebra.commute_of_mem_adjoin_singleton_of_commute hS (Commute.refl _)
  have hd : IsNilpotent (ad ℂ L (h : L) - S) := by
    simpa only [hsum,add_sub_cancel_right] using hnil
  have he : S = semisimpleOperator H h := by
    ext x
    apply root_induction H (x := x)
    · intro χ v hv
      rw [semisimpleOperator_apply H h χ hv]
      have hv' : v ∈ (ad ℂ L (h : L)).maxGenEigenspace (χ h) :=
        genWeightSpace_le_genWeightSpaceOf L h χ hv
      exact End.apply_eq_of_mem_of_comm_of_isFinitelySemisimple_of_isNil
        hv' hc hss.isFinitelySemisimple hd
    · simp
    · intro u v hu hv
      simp only [map_add,hu,hv]
  exact ⟨he ▸ hS,he ▸ hd⟩

set_option maxHeartbeats 1000000 in
/-- The semisimple part preserves every upper triangular flag for the
original adjoint operator. -/
theorem semisimpleOperator_upper {n : ℕ} (b : Basis (Fin n) ℂ L) (h : H)
    (hh : (LinearMap.toMatrix b b (ad ℂ L (h : L))).IsUpperTriangular) :
    (LinearMap.toMatrix b b (semisimpleOperator H h)).IsUpperTriangular := by
  let F := LinearMap.toMatrixAlgEquiv b
  let A := Matrix.blockTriangularSubalgebra ℂ ℂ (id : Fin n → Fin n)
  have hle : Algebra.adjoin ℂ {ad ℂ L (h : L)} ≤ A.comap F.toAlgHom := by
    apply Algebra.adjoin_le
    intro f hf
    obtain rfl := Set.mem_singleton_iff.mp hf
    exact hh
  exact hle (semisimpleOperator_jordan H h).1

end PolycyclicRecognition.ComplexCartan

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_ImaginaryOperatorPolynomial
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.realImaginaryOperator_complexify _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The imaginary Cartan operator preserves the triangular flag

Polynomial interpolation on the finite set of Cartan eigenvalues realizes
the imaginary part as a polynomial in the Jordan semisimple operator.
-/

noncomputable section
namespace PolycyclicRecognition.ComplexCartan
open LieAlgebra LieModule Module

variable {L : Type*} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L]
  (H : LieSubalgebra ℂ L) [H.IsCartanSubalgebra]

/-- Interpolation is on eigenvalues, so coincident weights cause no choice
or distinctness assumption. -/
theorem imaginaryOperator_polynomial (h : H) :
    ∃ p : Polynomial ℂ, Polynomial.aeval (semisimpleOperator H h) p = imaginaryOperator H h := by
  classical
  let s : Finset ℂ := Finset.univ.image (fun χ : Weight ℂ H L => χ h)
  let p : Polynomial ℂ := Lagrange.interpolate s id imaginaryPart
  have hp (χ : Weight ℂ H L) : p.eval (χ h) = imaginaryPart (χ h) := by
    exact Lagrange.eval_interpolate_at_node imaginaryPart (fun _ _ _ _ he => he)
      (Finset.mem_image.mpr ⟨χ,Finset.mem_univ _,rfl⟩)
  refine ⟨p,?_⟩
  apply LinearMap.ext
  intro x
  apply root_induction H (x := x)
  · intro χ v hv
    rw [Module.End.aeval_apply_of_mem_apply_eq_smul (semisimpleOperator_apply H h χ hv),
      imaginaryOperator_apply H h χ hv,hp]
  · simp
  · intro v w hv hw
    simp only [map_add,hv,hw]

/-- The imaginary part is a polynomial in the original Cartan adjoint
operator, through its Jordan semisimple part. -/
theorem imaginaryOperator_adjoin (h : H) :
    imaginaryOperator H h ∈ Algebra.adjoin ℂ {ad ℂ L (h : L)} := by
  obtain ⟨p,hp⟩ := imaginaryOperator_polynomial H h
  have hle : Algebra.adjoin ℂ {semisimpleOperator H h} ≤
      Algebra.adjoin ℂ {ad ℂ L (h : L)} := by
    apply Algebra.adjoin_le
    intro x hx
    obtain rfl := Set.mem_singleton_iff.mp hx
    exact (semisimpleOperator_jordan H h).1
  rw [← hp]
  exact hle (p.aeval_mem_adjoin_singleton ℂ (semisimpleOperator H h))

/-- The imaginary semisimple operator preserves the same upper triangular
flag as the original adjoint action. -/
theorem imaginaryOperator_upper {n : ℕ} (b : Basis (Fin n) ℂ L) (h : H)
    (hh : (LinearMap.toMatrix b b (ad ℂ L (h : L))).IsUpperTriangular) :
    (LinearMap.toMatrix b b (imaginaryOperator H h)).IsUpperTriangular := by
  let F := LinearMap.toMatrixAlgEquiv b
  let A := Matrix.blockTriangularSubalgebra ℂ ℂ (id : Fin n → Fin n)
  have hle : Algebra.adjoin ℂ {ad ℂ L (h : L)} ≤ A.comap F.toAlgHom := by
    apply Algebra.adjoin_le
    intro f hf
    obtain rfl := Set.mem_singleton_iff.mp hf
    exact hh
  exact hle (imaginaryOperator_adjoin H h)

end PolycyclicRecognition.ComplexCartan

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_PolynomialRangeAgreement
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Transferring an annihilator from an operator agreeing on the range -/

noncomputable section
namespace PolycyclicRecognition

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A]

theorem aeval_mul_eq_of_mul_eq (a b : A) (h : a*b = b*b) (p : Polynomial R) :
    Polynomial.aeval a p * b = b * Polynomial.aeval b p := by
  induction p using Polynomial.induction_on with
  | C r =>
    simp only [Polynomial.aeval_C]
    exact Algebra.commutes r b
  | add p q hp hq => simp only [map_add,add_mul,mul_add,hp,hq]
  | monomial k r hk =>
    have he : Polynomial.C r * Polynomial.X^(k+1) =
        (Polynomial.C r * Polynomial.X^k) * Polynomial.X := by rw [pow_succ,mul_assoc]
    have ha : Polynomial.aeval a ((Polynomial.C r * Polynomial.X^k) * Polynomial.X) =
        Polynomial.aeval a (Polynomial.C r * Polynomial.X^k) * a := by
      rw [map_mul,Polynomial.aeval_X]
    have hb : Polynomial.aeval b ((Polynomial.C r * Polynomial.X^k) * Polynomial.X) =
        Polynomial.aeval b (Polynomial.C r * Polynomial.X^k) * b := by
      rw [map_mul,Polynomial.aeval_X]
    rw [he,ha,hb]
    calc
      (Polynomial.aeval a (Polynomial.C r * Polynomial.X^k) * a) * b =
          Polynomial.aeval a (Polynomial.C r * Polynomial.X^k) * (a*b) := mul_assoc _ _ _
      _ = Polynomial.aeval a (Polynomial.C r * Polynomial.X^k) * (b*b) := by rw [h]
      _ = (Polynomial.aeval a (Polynomial.C r * Polynomial.X^k) * b) * b :=
        (mul_assoc _ _ _).symm
      _ = (b * Polynomial.aeval b (Polynomial.C r * Polynomial.X^k)) * b := by rw [hk]
      _ = b * (Polynomial.aeval b (Polynomial.C r * Polynomial.X^k) * b) := mul_assoc _ _ _

theorem aeval_X_mul_eq_zero_of_mul_eq (a b : A) (h : a*b = b*b)
    (p : Polynomial R) (hp : Polynomial.aeval a p = 0) :
    Polynomial.aeval b (Polynomial.X*p) = 0 := by
  rw [map_mul,Polynomial.aeval_X,← aeval_mul_eq_of_mul_eq a b h p,hp,zero_mul]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_RealEigenAnnihilator
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A real split annihilator from spanning real eigenvectors -/

noncomputable section
namespace PolycyclicRecognition

open Polynomial Module

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
  (D : Module.End ℝ V)

theorem realEigenPolynomial_monic : (realEigenPolynomial D).Monic := by
  classical
  exact monic_prod_of_monic _ _ fun r _ => monic_X_sub_C (r : ℝ)

theorem realEigenPolynomial_splits : (realEigenPolynomial D).Splits := by
  classical
  exact Splits.prod fun r _ => Splits.X_sub_C (r : ℝ)

theorem realEigenPolynomial_annihilates (hspan : (⨆ r : ℝ, D.eigenspace r) = ⊤) :
    aeval D (realEigenPolynomial D) = 0 := by
  classical
  let : Fintype {r // D.HasUnifEigenvalue r 1} := inferInstanceAs (Fintype D.Eigenvalues)
  ext v
  have hv : v ∈ ⨆ r : ℝ, D.eigenspace r := by
    rw [hspan]
    trivial
  apply Submodule.iSup_induction (fun r : ℝ => D.eigenspace r)
    (motive := fun v => aeval D (realEigenPolynomial D) v = 0) hv
  · intro r v hvr
    by_cases hv0 : v = 0
    · simp [hv0]
    · have hr : D.HasEigenvalue r := D.hasEigenvalue_of_hasEigenvector ⟨hvr, hv0⟩
      have hz : (realEigenPolynomial D).eval r = 0 := by
        change (Polynomial.evalRingHom r) (∏ t : D.Eigenvalues, (X - C (t : ℝ))) = 0
        rw [map_prod]
        apply Finset.prod_eq_zero (Finset.mem_univ (⟨r, hr⟩ : D.Eigenvalues))
        simp
      rw [D.aeval_apply_of_mem_apply_eq_smul (Module.End.mem_eigenspace_iff.mp hvr), hz, zero_smul]
  · simp
  · intro u v hu hv
    simp only [map_add, hu, hv, add_zero]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_SplitLieQuotient
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Compatibility with OpenAI's Mathlib (d13f23b): a lemma it has and ours lacks. -/

theorem Module.End.map_genEigenspace_le {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    {N : Type*} [AddCommGroup N] [Module R N]
    {f : Module.End R M} {g : Module.End R N} (φ : M →ₗ[R] N) (hφ : g.comp φ = φ.comp f)
    (μ : R) (k : ℕ∞) :
    (f.genEigenspace μ k).map φ ≤ g.genEigenspace μ k := by
  rintro y ⟨x, hx, rfl⟩
  obtain ⟨l, hl, hx⟩ := Module.End.mem_genEigenspace.mp hx
  refine Module.End.mem_genEigenspace.mpr ⟨l, hl, ?_⟩
  simp only [LinearMap.mem_ker, Module.End.pow_apply] at hx ⊢
  suffices (⇑φ).Semiconj ⇑(f - μ • 1) ⇑(g - μ • 1) by rw [← this.iterate_right, hx, map_zero]
  intro; simpa using congr($hφ _).symm

namespace OAI

/-!
# Split Lie actions pass to invariant quotients

The simultaneous-basis form of Lie's theorem requires induction on a
quotient by a common eigenline. We prove the splitting hypothesis for
that quotient using images of the original generalized eigenspaces.
-/

namespace PolycyclicRecognition

open Module

variable {𝕜 : Type*} [Field 𝕜]

variable {L V : Type*} [LieRing L] [LieAlgebra 𝕜 L]
  [AddCommGroup V] [Module 𝕜 V] [LieRingModule L V] [LieModule 𝕜 L V]

/-- A quotient of a split Lie action remains split. The image of each
generalized eigenspace lies in the corresponding quotient eigenspace. -/
theorem quotient_isTriangularizable [LieModule.IsTriangularizable 𝕜 L V]
    (N : LieSubmodule 𝕜 L V) : LieModule.IsTriangularizable 𝕜 L (V ⧸ N) := by
  refine ⟨fun x => ?_⟩
  let q : V →ₗ[𝕜] V ⧸ N := N.toSubmodule.mkQ
  have hq : q.range = ⊤ := LinearMap.range_eq_top.mpr N.toSubmodule.mkQ_surjective
  have hcomm : (LieModule.toEnd 𝕜 L (V ⧸ N) x).comp q =
      q.comp (LieModule.toEnd 𝕜 L V x) := by
    ext v
    rfl
  apply le_antisymm le_top
  calc
    (⊤ : Submodule 𝕜 (V ⧸ N)) = (⊤ : Submodule 𝕜 V).map q := by
      rw [Submodule.map_top, hq]
    _ = (⨆ μ : 𝕜, (LieModule.toEnd 𝕜 L V x).maxGenEigenspace μ).map q := by
      rw [LieModule.IsTriangularizable.maxGenEigenspace_eq_top x]
    _ ≤ ⨆ μ : 𝕜, (LieModule.toEnd 𝕜 L (V ⧸ N) x).maxGenEigenspace μ := by
      rw [Submodule.map_iSup]
      exact iSup_mono fun μ => Module.End.map_genEigenspace_le q hcomm μ ⊤

end PolycyclicRecognition

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_TriangularHeight
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Diagonal adjoint characters and the zero-height case

Starting from an actual simultaneous upper triangular basis for the adjoint
action, the diagonal entries are linear characters and kill every bracket.
The resulting canonical height space is zero exactly when the Lie algebra is
nilpotent. This proves the algebraic zero-height branch used in the manuscript;
it does not assume nilpotence from vanishing height.
-/

namespace PolycyclicRecognition

open Module

namespace TriangularAdjoint

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] {n : ℕ}
variable (T : TriangularAdjoint L n)

variable [FiniteDimensional ℝ L]

omit [FiniteDimensional ℝ L] in
/-- An element of a nilpotent ideal acts nilpotently on the whole algebra:
its first adjoint image lies in the ideal, where subsequent powers vanish. -/
theorem ad_nilpotent_of_mem_nilpotent_ideal
    (I : LieIdeal ℝ L) [LieRing.IsNilpotent I] (x : L) (hx : x ∈ I) :
    IsNilpotent (LieAlgebra.ad ℝ L x) := by
  let xi : I := ⟨x, hx⟩
  let f : L →ₗ[ℝ] I := (LieAlgebra.ad ℝ L x).codRestrict I.toSubmodule
    (fun y => lie_mem_left ℝ L I x y hx)
  have hp (k : ℕ) (y : L) :
      ((LieAlgebra.ad ℝ L x) ^ (k + 1)) y =
        (((LieAlgebra.ad ℝ I xi) ^ k) (f y) : I) := by
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [pow_succ', Module.End.mul_apply, ih, pow_succ', Module.End.mul_apply]
      rfl
  obtain ⟨k, hk⟩ := LieAlgebra.nilpotent_ad_of_nilpotent_algebra (R := ℝ) (L := I)
  refine ⟨k + 1, ?_⟩
  ext y
  rw [hp, hk xi]
  rfl

omit [FiniteDimensional ℝ L] in
/-- The canonical character kernel contains every nilpotent Lie ideal. Together
with `kernelIdeal_nilpotent`, this identifies it as the nilradical. -/
theorem nilpotent_ideal_le_kernelIdeal
    (I : LieIdeal ℝ L) [LieRing.IsNilpotent I] : I ≤ T.kernelIdeal := by
  intro x hx
  apply (T.mem_kernelIdeal x).mpr
  intro i
  rw [T.character_eq_diag]
  apply upperTriangular_nilpotent_diag _ (T.upper x)
  exact (ad_nilpotent_of_mem_nilpotent_ideal I x hx).map
    (LinearMap.toMatrixAlgEquiv T.basis).toRingHom

end TriangularAdjoint
end PolycyclicRecognition

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_SimultaneousAdjointBasis
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The simultaneous-basis form of Lie's theorem

Mathlib's Lie theorem supplies a common eigenvector for a solvable split
action. We iterate it on invariant quotients and lift each quotient basis,
obtaining the single upper triangular basis required by `TriangularAdjoint`.
-/

noncomputable section

namespace PolycyclicRecognition

open Module Set

/-- A finite-dimensional split action of a solvable split Lie algebra has
a simultaneous upper triangular basis. -/
theorem exists_upperTriangular_lieModule_basis {𝕜 : Type*} [Field 𝕜] [CharZero 𝕜]
    (L V : Type*)
    [LieRing L] [LieAlgebra 𝕜 L] [LieAlgebra.IsSolvable L]
    [AddCommGroup V] [Module 𝕜 V] [LieRingModule L V] [LieModule 𝕜 L V]
    [FiniteDimensional 𝕜 V] [LieModule.IsTriangularizable 𝕜 L V] :
    ∃ (n : ℕ) (b : Basis (Fin n) 𝕜 V),
      ∀ x : L, (LinearMap.toMatrix b b (LieModule.toEnd 𝕜 L V x)).IsUpperTriangular := by
  classical
  by_cases hzero : finrank 𝕜 V = 0
  · refine ⟨finrank 𝕜 V, Module.finBasis 𝕜 V, ?_⟩
    intro x i j hij
    have := i.isLt
    omega
  have hpos : 0 < finrank 𝕜 V := Nat.pos_of_ne_zero hzero
  let : Nontrivial V := finrank_pos_iff.mp hpos
  obtain ⟨χ, hχ⟩ := LieModule.exists_nontrivial_weightSpace_of_isSolvable 𝕜 L V
  let := hχ
  obtain ⟨v, hv⟩ := exists_ne (0 : LieModule.weightSpace V χ)
  have hv0 : (v : V) ≠ 0 := by
    intro h
    exact hv (Subtype.ext h)
  have hvχ : ∀ x : L, ⁅x, (v : V)⁆ = χ x • (v : V) :=
    (LieModule.mem_weightSpace χ (v : V)).mp v.property
  let N : LieSubmodule 𝕜 L V :=
    { (𝕜 ∙ (v : V)) with
      lie_mem := by
        intro x w hw
        obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hw
        rw [lie_smul, hvχ]
        exact Submodule.smul_mem _ a
          (Submodule.smul_mem _ (χ x) (Submodule.mem_span_singleton_self (v : V))) }
  have hdimN : finrank 𝕜 N.toSubmodule = 1 := finrank_span_singleton hv0
  have hlt : finrank 𝕜 (V ⧸ N) < finrank 𝕜 V := by
    change finrank 𝕜 (V ⧸ N.toSubmodule) < finrank 𝕜 V
    have hd := N.toSubmodule.finrank_quotient_add_finrank
    rw [hdimN] at hd
    omega
  let : LieModule.IsTriangularizable 𝕜 L (V ⧸ N) := quotient_isTriangularizable (𝕜 := 𝕜) N
  obtain ⟨n, bQ, hQ⟩ := exists_upperTriangular_lieModule_basis (𝕜 := 𝕜) L (V ⧸ N)
  let bN : Basis (Fin 1) 𝕜 N.toSubmodule := FiniteDimensional.basisSingleton (Fin 1) hdimN
    ⟨v, Submodule.mem_span_singleton_self (v : V)⟩ (by
      intro h
      apply hv0
      exact congrArg Subtype.val h)
  choose lift hlift using fun i : Fin n => N.toSubmodule.mkQ_surjective (bQ i)
  let b := basisWithQuotientLifts N.toSubmodule bN bQ lift hlift
  let e : Fin 1 ⊕ Fin n ≃ Fin (1 + n) := finSumFinEquiv
  refine ⟨1 + n, b.reindex e, ?_⟩
  intro x i j hij
  obtain ⟨i, rfl⟩ := e.surjective i
  obtain ⟨j, rfl⟩ := e.surjective j
  simp only [LinearMap.toMatrix_apply, LieModule.toEnd_apply_apply]
  simp only [Basis.repr_reindex_apply, Basis.reindex_apply, Equiv.symm_apply_apply]
  dsimp only [b]
  cases i with
  | inl i =>
    cases j with
    | inl j =>
      have hi : (i : ℕ) = 0 := by omega
      have hj : (j : ℕ) = 0 := by omega
      have heq : i = j := Fin.ext (hi.trans hj.symm)
      exact (hij.ne (congrArg (fun a => e (Sum.inl a)) heq).symm).elim
    | inr j =>
      have hi : (i : ℕ) = 0 := by omega
      change 1 + (j : ℕ) < (i : ℕ) at hij
      omega
  | inr i =>
    cases j with
    | inl j =>
      rw [basisWithQuotientLifts_inl, basisWithQuotientLifts_repr_inr]
      have hz : N.toSubmodule.mkQ ⁅x, (bN j : V)⁆ = 0 :=
        (Submodule.Quotient.mk_eq_zero N.toSubmodule).mpr (N.lie_mem (bN j).property)
      rw [hz, map_zero, Finsupp.zero_apply]
    | inr j =>
      rw [basisWithQuotientLifts_inr, basisWithQuotientLifts_repr_inr]
      have hq : N.toSubmodule.mkQ ⁅x, lift j⁆ =
          (LieModule.toEnd 𝕜 L (V ⧸ N) x) (bQ j) := by
        change (LieModule.toEnd 𝕜 L (V ⧸ N) x) (N.toSubmodule.mkQ (lift j)) = _
        rw [hlift]
      rw [hq]
      change 1 + (j : ℕ) < 1 + (i : ℕ) at hij
      simpa only [LinearMap.toMatrix_apply, LieModule.toEnd_apply_apply] using
        hQ x (i := i) (j := j) (by change (j : ℕ) < (i : ℕ); omega)
termination_by finrank 𝕜 V

/-- Applying the proved simultaneous-basis theorem to the adjoint module
produces exactly the basis structure used by the height construction. -/
theorem nonempty_triangularAdjoint_of_split (L : Type*)
    [LieRing L] [LieAlgebra ℝ L] [LieAlgebra.IsSolvable L]
    [FiniteDimensional ℝ L] [LieModule.IsTriangularizable ℝ L L] :
    ∃ n : ℕ, Nonempty (TriangularAdjoint L n) := by
  obtain ⟨n, b, hb⟩ := exists_upperTriangular_lieModule_basis (𝕜 := ℝ) L L
  exact ⟨n, ⟨⟨b, hb⟩⟩⟩

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_ComplexTriangularPolynomial
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial calculus on a complex triangular flag -/

noncomputable section
namespace PolycyclicRecognition

theorem complex_matrix_aeval_upper {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (hA : A.IsUpperTriangular) (p : Polynomial ℂ) :
    (Polynomial.aeval A p).IsUpperTriangular := by
  have hle : Algebra.adjoin ℂ {A} ≤
      Matrix.blockTriangularSubalgebra ℂ ℂ (id : Fin n → Fin n) := by
    apply Algebra.adjoin_le
    intro B hB
    obtain rfl := Set.mem_singleton_iff.mp hB
    exact hA
  exact hle (p.aeval_mem_adjoin_singleton ℂ A)

theorem complex_matrix_aeval_diagonal {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (hA : A.IsUpperTriangular) (p : Polynomial ℂ) (i : Fin n) :
    Polynomial.aeval A p i i = p.eval (A i i) := by
  induction p using Polynomial.induction_on with
  | C a => simp [Matrix.algebraMap_eq_diagonal]
  | add p q hp hq => simp only [map_add, Matrix.add_apply, Polynomial.eval_add, hp, hq]
  | monomial k a hk =>
    rw [pow_succ, ← mul_assoc, map_mul, Polynomial.aeval_X,
      ComplexTriangularAdjoint.diagonal_mul _ _
        (complex_matrix_aeval_upper A hA _) hA,
      hk]
    simp only [Polynomial.eval_mul,Polynomial.eval_X]

theorem complex_upper_nilpotent_diagonal {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (hA : A.IsUpperTriangular) (hnil : IsNilpotent A) (i : Fin n) : A i i = 0 := by
  obtain ⟨k,hk⟩ := hnil
  apply IsNilpotent.eq_zero
  refine ⟨k,?_⟩
  rw [← ComplexTriangularAdjoint.diagonal_pow A hA k i,hk]
  rfl

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanModel
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The nilpotent ideal in the Cartan model

Nonzero generalized root vectors lie in the derived algebra. Their generated
ideal is nilpotent for an actual triangular adjoint representation, and its
sum with the Cartan subalgebra is the full Lie algebra.
-/

noncomputable section

namespace PolycyclicRecognition

open LieAlgebra LieModule

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L]
  (H : LieSubalgebra ℝ L) [H.IsCartanSubalgebra]

set_option maxHeartbeats 1000000 in
theorem cartanRootIdeal_le_derived : cartanRootIdeal H ≤ derivedSeries ℝ L 1 := by
  apply LieSubmodule.lieSpan_le.mpr
  rintro v ⟨χ, hχ, hv⟩
  apply nonzero_root_le_ideal H (derivedSeries ℝ L 1) _ χ hχ hv
  intro x y
  change ⁅x, y⁆ ∈ ⁅(⊤ : LieIdeal ℝ L), ⊤⁆
  exact LieSubmodule.lie_mem_lie (LieSubmodule.mem_top _) (LieSubmodule.mem_top _)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_RealSplitAnnihilator
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A real annihilating polynomial from a complex flag with real diagonal -/

noncomputable section
namespace PolycyclicRecognition
open Module
open scoped TensorProduct

theorem real_split_annihilator_of_complex_triangular
    {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    {n : ℕ} (A : Module.End ℝ V) (b : Basis (Fin n) ℂ (ℂ ⊗[ℝ] V))
    (hu : (LinearMap.toMatrix b b (A.baseChange ℂ)).IsUpperTriangular)
    (hr : ∀ i, (LinearMap.toMatrix b b (A.baseChange ℂ) i i).im = 0) :
    ∃ S : Finset ℝ,
      Polynomial.aeval A ((∏ a ∈ S, (Polynomial.X - Polynomial.C a)) ^ n) = 0 := by
  classical
  let M := LinearMap.toMatrix b b (A.baseChange ℂ)
  let d : Fin n → ℝ := fun i => (M i i).re
  let S := Finset.univ.image d
  let Q : Polynomial ℝ := ∏ a ∈ S, (Polynomial.X - Polynomial.C a)
  have hd (i : Fin n) : M i i = (d i : ℂ) := by
    apply Complex.ext
    · rfl
    · exact (hr i).trans (by simp)
  have hmap : Q.map (algebraMap ℝ ℂ) =
      ∏ a ∈ S, (Polynomial.X - Polynomial.C (a : ℂ)) := by
    simp only [Q,Polynomial.map_prod,Polynomial.map_sub,Polynomial.map_X,Polynomial.map_C]
    rfl
  have hdiv : M.charpoly ∣ (Q.map (algebraMap ℝ ℂ)) ^ n := by
    rw [Matrix.charpoly_of_isUpperTriangular M hu]
    have hh := prod_dvd_pow_card Finset.univ
      (fun i : Fin n => Polynomial.X - Polynomial.C (M i i))
      (Q.map (algebraMap ℝ ℂ)) (by
        intro i _
        rw [hd,hmap]
        exact Finset.dvd_prod_of_mem _ (Finset.mem_image_of_mem d (Finset.mem_univ i)))
    simpa only [Finset.card_univ,Fintype.card_fin] using hh
  have hm : Polynomial.aeval M ((Q.map (algebraMap ℝ ℂ)) ^ n) = 0 := by
    obtain ⟨p,hp⟩ := hdiv
    rw [hp,map_mul,Matrix.aeval_self_charpoly,zero_mul]
  have hc : Polynomial.aeval (A.baseChange ℂ) ((Q.map (algebraMap ℝ ℂ)) ^ n) = 0 := by
    apply (LinearMap.toMatrixAlgEquiv b).injective
    rw [← Polynomial.aeval_algHom_apply,map_zero]
    exact hm
  have ht : (Polynomial.aeval A (Q ^ n)).baseChange ℂ = 0 := by
    change (Module.End.baseChangeHom ℝ ℂ V) (Polynomial.aeval A (Q ^ n)) = 0
    rw [← Polynomial.aeval_algHom_apply,
      Polynomial.aeval_eq_aeval_map (IsScalarTower.algebraMap_eq ℝ ℂ _).symm]
    change Polynomial.aeval (A.baseChange ℂ) ((Q ^ n).map (algebraMap ℝ ℂ)) = 0
    simpa only [Polynomial.map_pow] using hc
  refine ⟨S,?_⟩
  apply LinearMap.ext
  intro v
  apply (Module.FaithfullyFlat.one_tmul_eq_zero_iff ℝ V (A := ℂ) _).mp
  exact (LinearMap.congr_fun ht ((1 : ℂ) ⊗ₜ[ℝ] v))

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanDecomposition
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instNonemptyBases _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_nonempty _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Cartan models for the real triangular adjoint action

The nilpotent ideal and Cartan subalgebra span the algebra, and the Cartan
subalgebra maps onto the actual canonical height quotient.
-/

noncomputable section

namespace PolycyclicRecognition

open LieAlgebra LieModule

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {n : ℕ} (T : TriangularAdjoint L n)

set_option maxHeartbeats 1000000 in
/-- Existence and the Lie-algebra assertions of the manuscript's Cartan
model lemma. All terms are constructed from the actual adjoint basis. -/
theorem exists_cartan_model :
    ∃ H : LieSubalgebra ℝ L, ∃ _ : H.IsCartanSubalgebra,
      LieRing.IsNilpotent (cartanRootIdeal H) ∧
      cartanRootIdeal H ≤ derivedSeries ℝ L 1 ∧
      (cartanRootIdeal H).toSubmodule ⊔ H.toSubmodule = ⊤ ∧
      Function.Surjective ((heightProjection T.character).comp H.subtype) := by
  obtain ⟨x, hx⟩ := exists_isCartanSubalgebra_engel ℝ L
  let := hx
  exact ⟨LieSubalgebra.engel ℝ x, hx, cartanRootIdeal_nilpotent _ T,
    cartanRootIdeal_le_derived _, triangular_cartan_spanning T _,
    cartan_height_surjective T _⟩

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanJordanDecomposition
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.CartanFactorModel.heightRay_zero _root_.OAI.PolycyclicRecognition.CartanWordModel.supportDatum_weight _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.nilshadowWeightDerivation_symm _root_.OAI.PolycyclicRecognition.nilshadowWeightOperator_symm _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Identifying the Cartan weight operator as the semisimple part

The polynomial Jordan decomposition shows that the weight operator preserves
every subspace preserved by the original adjoint operator. This will keep the
original triangular flag when the weight operator is subtracted.
-/

noncomputable section
namespace PolycyclicRecognition

open LieAlgebra LieModule Module

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {n : ℕ} (T : TriangularAdjoint L n)
  (H : LieSubalgebra ℝ L) [H.IsCartanSubalgebra]

set_option maxHeartbeats 1000000 in
theorem cartanWeightOperator_jordan (h : H) :
    cartanWeightOperator T H h ∈ Algebra.adjoin ℝ {ad ℝ L (h : L)} ∧
      IsNilpotent (ad ℝ L (h : L) - cartanWeightOperator T H h) := by
  obtain ⟨N, hN, S, hS, hnil, hss, hsum⟩ :=
    (ad ℝ L (h : L)).exists_isNilpotent_isSemisimple
  have hc : Commute (ad ℝ L (h : L)) S :=
    Algebra.commute_of_mem_adjoin_singleton_of_commute hS (Commute.refl _)
  have hd : IsNilpotent (ad ℝ L (h : L) - S) := by
    simpa only [hsum, add_sub_cancel_right] using hnil
  have heq : S = cartanWeightOperator T H h := by
    ext x
    apply cartan_root_induction T H (x := x)
    · intro χ v hv
      rw [cartanWeightOperator_apply_root T H h χ hv]
      have hv' : v ∈ (ad ℝ L (h : L)).maxGenEigenspace (χ h) :=
        genWeightSpace_le_genWeightSpaceOf L h χ hv
      exact End.apply_eq_of_mem_of_comm_of_isFinitelySemisimple_of_isNil
        hv' hc hss.isFinitelySemisimple hd
    · simp
    · intro u v hu hv
      simp only [map_add, hu, hv]
  exact ⟨heq ▸ hS, heq ▸ hd⟩

set_option maxHeartbeats 1000000 in
theorem cartanWeightOperator_upper (h : H) :
    (LinearMap.toMatrix T.basis T.basis (cartanWeightOperator T H h)).IsUpperTriangular := by
  let F := LinearMap.toMatrixAlgEquiv T.basis
  let A := Matrix.blockTriangularSubalgebra ℝ ℝ (id : Fin n → Fin n)
  have hle : Algebra.adjoin ℝ {ad ℝ L (h : L)} ≤ A.comap F.toAlgHom := by
    apply Algebra.adjoin_le
    intro f hf
    obtain rfl := Set.mem_singleton_iff.mp hf
    exact T.upper h
  exact hle (cartanWeightOperator_jordan T H h).1

set_option maxHeartbeats 1000000 in
/-- Removing the semisimple height action leaves a strictly triangular
operator in the original adjoint flag. -/
theorem heightReducedAdjoint_nilpotent (x : L) :
    IsNilpotent (ad ℝ L x - (heightSemisimpleAction T H x).toLinearMap) := by
  let h := cartanHeightSection T H (heightProjection T.character x)
  let u : L := x - (h : L)
  let N := ad ℝ L (h : L) - cartanWeightOperator T H h
  have hN : IsNilpotent N := (cartanWeightOperator_jordan T H h).2
  have hNu : (LinearMap.toMatrix T.basis T.basis N).IsUpperTriangular := by
    rw [show N = ad ℝ L (h : L) - cartanWeightOperator T H h from rfl, map_sub]
    exact (T.upper h).sub (cartanWeightOperator_upper T H h)
  have hNd (i : Fin n) : LinearMap.toMatrix T.basis T.basis N i i = 0 :=
    upperTriangular_nilpotent_diag _ hNu
      (hN.map (LinearMap.toMatrixAlgEquiv T.basis).toRingHom) i
  have huk : u ∈ T.kernelIdeal := by
    apply (Submodule.Quotient.mk_eq_zero _).mp
    change heightProjection T.character (x - (h : L)) = 0
    rw [map_sub, cartanHeightSection_height, sub_self]
  have hud (i : Fin n) : LinearMap.toMatrix T.basis T.basis (ad ℝ L u) i i = 0 := by
    rw [← T.character_eq_diag]
    exact (T.mem_kernelIdeal u).mp huk i
  have heq : ad ℝ L x - (heightSemisimpleAction T H x).toLinearMap = ad ℝ L u + N := by
    change ad ℝ L x - cartanWeightOperator T H h = ad ℝ L (x - (h : L)) + N
    rw [map_sub]
    dsimp only [N]
    abel
  rw [heq]
  obtain ⟨k, hk⟩ := upperTriangular_nilpotent_of_diag_zero
    (LinearMap.toMatrix T.basis T.basis (ad ℝ L u + N))
    (by rw [map_add]; exact (T.upper u).add hNu)
    (by intro i; simp only [map_add, Matrix.add_apply, hud, hNd, add_zero])
  refine ⟨k, (LinearMap.toMatrixAlgEquiv T.basis).injective ?_⟩
  rw [map_pow, map_zero]
  change (LinearMap.toMatrix T.basis T.basis (ad ℝ L u + N)) ^ k = 0
  exact hk

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Lattices_CartanNilshadow
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanRealShadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The nilpotent Lie algebra attached to the Cartan height action

The graph of minus the semisimple height action is a Lie subalgebra of the
affine derivation algebra. Its first coordinate is linearly the original Lie
algebra, while its bracket has the semisimple action removed.
-/

noncomputable section
namespace PolycyclicRecognition

open LieAlgebra Module

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {n : ℕ} (T : TriangularAdjoint L n)
  (H : LieSubalgebra ℝ L) [H.IsCartanSubalgebra]

set_option maxHeartbeats 1000000 in
private theorem nilpotent_of_square_eq_mul {V : Type*} [AddCommGroup V] [Module ℝ V]
    {A F : Module.End ℝ V} (hA : IsNilpotent A) (hFF : F * F = A * F) : IsNilpotent F := by
  have hp (k : ℕ) : F ^ (k + 1) = A ^ k * F := by
    induction k with
    | zero => simp
    | succ k hk =>
      calc
        F ^ (k + 1 + 1) = F ^ (k + 1) * F := pow_succ _ _
        _ = A ^ k * (F * F) := by rw [hk, mul_assoc]
        _ = A ^ (k + 1) * F := by rw [hFF, ← mul_assoc, pow_succ]
  obtain ⟨k, hk⟩ := hA
  exact ⟨k + 1, by rw [hp, hk, zero_mul]⟩

set_option maxHeartbeats 1000000 in
/-- The Cartan graph is nilpotent; no nilshadow theorem is assumed. -/
theorem cartanNilshadow_nilpotent : LieRing.IsNilpotent (CartanNilshadow T H) := by
  let e := cartanNilshadowEquiv T H
  apply (LieAlgebra.isNilpotent_iff_forall (R := ℝ)).mpr
  intro p
  obtain ⟨x, rfl⟩ := e.surjective p
  let F : Module.End ℝ L := e.symm.conjRingEquiv (ad ℝ (CartanNilshadow T H) (e x))
  let A : Module.End ℝ L := ad ℝ L x - (heightSemisimpleAction T H x).toLinearMap
  have hF (y : L) : F y = ⁅x, y⁆ - heightSemisimpleAction T H x y +
      heightSemisimpleAction T H y x := cartanNilshadow_bracket T H x y
  have hFh (y : L) : heightProjection T.character (F y) = 0 := by
    rw [hF, map_add, map_sub, T.height_lie, heightSemisimpleAction_height_zero,
      heightSemisimpleAction_height_zero, sub_self, add_zero]
  have hFr (y : L) (hy : heightProjection T.character y = 0) : F y = A y := by
    have hs : heightSemisimpleAction T H y = 0 := by
      change cartanWeightDerivationLinear T H
        (cartanHeightSection T H (heightProjection T.character y)) = 0
      rw [hy, map_zero, map_zero]
    rw [hF, hs, LieDerivation.zero_apply, add_zero]
    rfl
  have hFF : F * F = A * F := by
    ext y
    exact hFr (F y) (hFh y)
  obtain ⟨k, hk⟩ := nilpotent_of_square_eq_mul (heightReducedAdjoint_nilpotent T H x) hFF
  refine ⟨k, e.symm.conjRingEquiv.injective ?_⟩
  rw [map_pow, map_zero]
  exact hk

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Lattices_NilshadowWeightAction
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original solvable algebra as an extension of its nilshadow -/

noncomputable section
namespace PolycyclicRecognition

open LieAlgebra Module

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {n : ℕ} (T : TriangularAdjoint L n)
  (H : LieSubalgebra ℝ L) [H.IsCartanSubalgebra]

local notation "σ" => heightSemisimpleAction T H
local notation "e" => cartanNilshadowEquiv T H

theorem nilshadowWeightDerivation_equiv (x y : L) :
    nilshadowWeightDerivation T H x (e y) = e (σ x y) := by
  apply (e).symm.injective
  simp only [nilshadowWeightDerivation_symm, LinearEquiv.symm_apply_apply]

theorem nilshadowSemidirectEmbedding_injective :
    Function.Injective (nilshadowSemidirectEmbedding T H) := by
  intro x y h
  exact (e).injective (congrArg SemiDirectSum.left h)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_SolvableFaithfulRepresentation
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.CartanFactorModel.heightRay_zero _root_.OAI.PolycyclicRecognition.CartanWordModel.supportDatum_weight _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A faithful representation nilpotent on the canonical nilradical

The representation is obtained from the proved nilshadow and its finite
truncated enveloping algebra. Real triangularization is a separate step.
-/

noncomputable section
namespace PolycyclicRecognition

open Module LieAlgebra

attribute [local instance 100] LieRing.ofAssociativeRing

variable {L : Type} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {n : ℕ} (T : TriangularAdjoint L n)
  (H : LieSubalgebra ℝ L) [H.IsCartanSubalgebra]

local notation "K" => CartanNilshadow T H

theorem nilshadowWeightDerivation_eq_zero_of_mem_kernel (x : L) (hx : x ∈ T.kernelIdeal) :
    nilshadowWeightDerivation T H x = 0 := by
  have hσ : heightSemisimpleAction T H x = 0 := by
    change cartanWeightDerivationLinear T H
      (cartanHeightSection T H (heightProjection T.character x)) = 0
    have hz : heightProjection T.character x = 0 := (Submodule.Quotient.mk_eq_zero _).mpr hx
    rw [hz, map_zero, map_zero]
  apply LieDerivation.ext
  intro p
  apply (cartanNilshadowEquiv T H).symm.injective
  rw [nilshadowWeightDerivation_symm, hσ]
  simp

theorem solvableTruncatedRepresentation_nilpotent (c : ℕ) (x : L)
    (hx : x ∈ T.kernelIdeal) : IsNilpotent (solvableTruncatedRepresentation T H c x) := by
  change IsNilpotent (truncatedLeftRepresentation (R := ℝ) c (cartanNilshadowEquiv T H x) +
    truncatedEnvelopingDerivationRepresentation c (nilshadowWeightDerivation T H x))
  rw [nilshadowWeightDerivation_eq_zero_of_mem_kernel T H x hx, map_zero, add_zero]
  exact truncatedLeftRepresentation_nilpotent _ _

theorem solvableTruncatedRepresentation_injective (c : ℕ)
    (hgen : Function.Injective (truncatedEnvelopingGenerator (R := ℝ) (L := K) c)) :
    Function.Injective (solvableTruncatedRepresentation T H c) :=
  (truncatedSemidirectRepresentation_injective c _
    (show Function.Injective (nilshadowWeightAction T H).range.incl from
      Subtype.val_injective) hgen).comp
    (nilshadowSemidirectEmbedding_injective T H)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_SplitAnnihilator
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Split annihilators and real generalized eigenspaces

The usual finite-dimensional decomposition only needs a split annihilator,
rather than an algebraically closed scalar field. Restrictions retain the
same annihilator, so the argument also applies to invariant subspaces.
-/

noncomputable section
namespace PolycyclicRecognition

open Polynomial Module

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

theorem aeval_restrict_apply (f : Module.End ℝ V) (S : Submodule ℝ V)
    (hS : ∀ v ∈ S, f v ∈ S) (p : ℝ[X]) (v : S) :
    ((aeval (f.restrict hS) p v : S) : V) = aeval f p (v : V) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, LinearMap.add_apply, Submodule.coe_add, hp, hq]
  | monomial n a =>
    simp only [aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply,
      Submodule.coe_smul_of_tower]
    congr 1
    induction n with
    | zero => rfl
    | succ n hn =>
      rw [pow_succ', pow_succ', Module.End.mul_apply, Module.End.mul_apply]
      exact congrArg f hn

theorem aeval_restrict_eq_zero (f : Module.End ℝ V) (S : Submodule ℝ V)
    (hS : ∀ v ∈ S, f v ∈ S) (p : ℝ[X]) (hp : aeval f p = 0) :
    aeval (f.restrict hS) p = 0 := by
  ext v
  rw [aeval_restrict_apply, hp]
  rfl

theorem exists_eigenvalue_of_split_annihilator [FiniteDimensional ℝ V] [Nontrivial V]
    (f : Module.End ℝ V) (p : ℝ[X]) (hp0 : p ≠ 0) (hps : p.Splits)
    (hp : aeval f p = 0) : ∃ r : ℝ, f.HasEigenvalue r := by
  have hi := Algebra.IsIntegral.isIntegral (R := ℝ) f
  have hs : (minpoly ℝ f).Splits := hps.of_dvd hp0 (minpoly.dvd ℝ f hp)
  obtain ⟨r, hr⟩ := hs.exists_eval_eq_zero (ne_of_gt (minpoly.degree_pos hi))
  exact ⟨r, Module.End.hasEigenvalue_of_isRoot hr⟩

theorem iSup_maxGenEigenspace_eq_top_of_split_annihilator [FiniteDimensional ℝ V]
    (f : Module.End ℝ V) (p : ℝ[X]) (hp0 : p ≠ 0) (hps : p.Splits)
    (hp : aeval f p = 0) : ⨆ r : ℝ, f.maxGenEigenspace r = ⊤ := by
  suffices ∀ n, finrank ℝ V = n → ⨆ r : ℝ, f.maxGenEigenspace r = ⊤ by
    exact this _ rfl
  intro n hn
  induction n using Nat.strong_induction_on generalizing V with
  | h n ih =>
    rcases n with - | n
    · rw [← top_le_iff]
      simp only [Submodule.finrank_eq_zero.1 (Eq.trans (finrank_top _ _) hn), bot_le]
    · have : Nontrivial V := finrank_pos_iff.1 (by rw [hn]; exact Nat.zero_lt_succ n)
      obtain ⟨r, hr⟩ := exists_eigenvalue_of_split_annihilator f p hp0 hps hp
      let ES := f.genEigenspace r (finrank ℝ V)
      let ER := f.genEigenrange r (finrank ℝ V)
      have hER : ∀ v ∈ ER, f v ∈ ER := fun v hv =>
        Module.End.map_genEigenrange_le (Submodule.mem_map_of_mem hv)
      let f' : Module.End ℝ ER := f.restrict hER
      have hpos : 0 < finrank ℝ ES := by
        dsimp +instances only [ES]
        rw [hn]
        exact Module.End.pos_finrank_genEigenspace_of_hasEigenvalue hr (Nat.zero_lt_succ n)
      have hadd : finrank ℝ ER + finrank ℝ ES = finrank ℝ V := by
        dsimp +instances only [ER, ES]
        rw [Module.End.genEigenspace_nat, Module.End.genEigenrange_nat]
        exact LinearMap.finrank_range_add_finrank_ker _
      have hlt : finrank ℝ ER < n.succ := by omega
      have hspan : ⨆ r : ℝ, f'.maxGenEigenspace r = ⊤ :=
        ih (finrank ℝ ER) hlt f' (aeval_restrict_eq_zero f ER hER p hp) rfl
      have hspan' : ⨆ r : ℝ, (f'.maxGenEigenspace r).map ER.subtype = ER := by
        simp only [(Submodule.map_iSup _ _).symm, hspan, Submodule.map_subtype_top ER]
      have hmap : ∀ r, (f'.maxGenEigenspace r).map ER.subtype ≤ f.maxGenEigenspace r := by
        intro r
        rw [Module.End.maxGenEigenspace, Module.End.genEigenspace_restrict]
        apply Submodule.map_comap_le
      have hleR : ER ≤ ⨆ r : ℝ, f.maxGenEigenspace r := by
        rw [← hspan']
        exact iSup_mono hmap
      have hleS : ES ≤ ⨆ r : ℝ, f.maxGenEigenspace r :=
        ((f.genEigenspace r).mono le_top).trans (le_iSup f.maxGenEigenspace r)
      have hdis : Disjoint ER ES := Module.End.generalized_eigenvec_disjoint_range_ker f r
      rw [← top_le_iff, ← Submodule.eq_top_of_disjoint ER ES hadd.ge hdis]
      exact sup_le hleR hleS

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_WordLengthFiltration
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Word-length filtration for a nilpotent generated algebra

Left multiplication raises word length; a derivation carrying generators to
generators preserves it. This separates the nilpotent and semisimple parts
of the finite solvable representation.
-/

noncomputable section
namespace PolycyclicRecognition

variable {A ι : Type*} [Ring A] [Algebra ℝ A] (j : ι → A)

theorem wordLengthSpan_antitone : Antitone (wordLengthSpan j) := by
  intro k l hkl
  apply Submodule.span_mono
  rintro a ⟨w, hw, rfl⟩
  exact ⟨w, hkl.trans hw, rfl⟩

theorem wordLengthSpan_generator_mul (k : ℕ) (x : ι) {a : A}
    (ha : a ∈ wordLengthSpan j k) : j x * a ∈ wordLengthSpan j (k + 1) := by
  induction ha using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨l, hl, rfl⟩ := ha
    apply Submodule.subset_span
    exact ⟨x :: l, Nat.succ_le_succ hl, by simp⟩
  | zero => simpa only [mul_zero] using (wordLengthSpan j (k + 1)).zero_mem
  | add a b _ _ ha hb =>
    rw [mul_add]
    exact (wordLengthSpan j (k + 1)).add_mem ha hb
  | smul r a _ ha =>
    rw [Algebra.mul_smul_comm]
    exact (wordLengthSpan j (k + 1)).smul_mem r ha

theorem wordLengthSpan_zero_eq_top (hgen : Algebra.adjoin ℝ (Set.range j) = ⊤) :
    wordLengthSpan j 0 = ⊤ := by
  have hle : (Algebra.adjoin ℝ (Set.range j)).toSubmodule ≤ wordLengthSpan j 0 := by
    rw [Algebra.adjoin_eq_span]
    apply Submodule.span_le.mpr
    intro a ha
    have hw : ∃ l : List ι, (l.map j).prod = a := by
      induction ha using Submonoid.closure_induction with
      | mem a ha =>
        obtain ⟨x, rfl⟩ := ha
        exact ⟨[x], by simp⟩
      | one => exact ⟨[], by simp⟩
      | mul a b _ _ ha hb =>
        obtain ⟨v, rfl⟩ := ha
        obtain ⟨w, rfl⟩ := hb
        exact ⟨v ++ w, by simp⟩
    obtain ⟨l, rfl⟩ := hw
    exact Submodule.subset_span ⟨l, Nat.zero_le _, rfl⟩
  apply top_unique
  rw [hgen] at hle
  exact hle

theorem wordLengthSpan_eq_bot (c : ℕ)
    (hnil : ∀ l : List ι, c ≤ l.length → (l.map j).prod = 0) :
    wordLengthSpan j c = ⊥ := by
  apply eq_bot_iff.mpr
  apply Submodule.span_le.mpr
  rintro a ⟨l, hl, rfl⟩
  exact (Submodule.mem_bot ℝ).mpr (hnil l hl)

variable (D : Module.End ℝ A) (f : ι → ι)
  (hmul : ∀ a b, D (a * b) = a * D b + D a * b)
  (hone : D 1 = 0) (hgen : ∀ x, D (j x) = j (f x))

include f hmul hone hgen

theorem wordLengthSpan_prefix_derivative (k : ℕ) (p l : List ι)
    (h : k ≤ p.length + l.length) :
    (p.map j).prod * D (l.map j).prod ∈ wordLengthSpan j k := by
  induction l generalizing p with
  | nil =>
    simpa only [List.map_nil, List.prod_nil, hone, mul_zero] using (wordLengthSpan j k).zero_mem
  | cons x l ih =>
    simp only [List.map_cons, List.prod_cons, hmul, hgen, mul_add]
    apply (wordLengthSpan j k).add_mem
    · have hp : k ≤ (p ++ [x]).length + l.length := by
        simpa only [List.length_append, List.length_singleton, List.length_cons,
          List.length_nil, zero_add, Nat.add_assoc, Nat.add_comm 1] using h
      simpa only [List.map_append, List.prod_append, List.map_singleton,
        List.prod_singleton, mul_assoc] using ih (p ++ [x]) hp
    · apply Submodule.subset_span
      refine ⟨p ++ f x :: l, ?_, ?_⟩
      · simpa only [List.length_append, List.length_cons] using h
      · simp only [List.map_append, List.prod_append, List.map_cons, List.prod_cons]

theorem wordLengthSpan_derivative (k : ℕ) {a : A} (ha : a ∈ wordLengthSpan j k) :
    D a ∈ wordLengthSpan j k := by
  induction ha using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨l, hl, rfl⟩ := ha
    simpa only [List.map_nil, List.prod_nil, one_mul] using
      wordLengthSpan_prefix_derivative j D f hmul hone hgen k [] l (by simpa using hl)
  | zero => simpa only [map_zero] using (wordLengthSpan j k).zero_mem
  | add a b _ _ ha hb =>
    rw [map_add]
    exact (wordLengthSpan j k).add_mem ha hb
  | smul r a _ ha =>
    rw [map_smul]
    exact (wordLengthSpan j k).smul_mem r ha

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_SolvableWeightEigenvectors
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanRealShadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Real eigenvectors span the finite weight representation -/

noncomputable section
namespace PolycyclicRecognition

open Module LieAlgebra LieModule

variable {L : Type} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {n : ℕ} (T : TriangularAdjoint L n)
  (H : LieSubalgebra ℝ L) [H.IsCartanSubalgebra]

local notation "K" => CartanNilshadow T H
local notation "e" => cartanNilshadowEquiv T H
local notation "Q" c => TruncatedEnvelopingAlgebra ℝ K c

theorem solvableWeightDerivation_eigenspaces_span (c : ℕ) (x : L) :
    derivationEigenvectorSpan (truncatedEnvelopingDerivation c
      (nilshadowWeightDerivation T H x)) = ⊤ := by
  let D := truncatedEnvelopingDerivation c (nilshadowWeightDerivation T H x)
  let S := derivationEigenvectorSubalgebra D
    (truncatedEnvelopingDerivation_one c _)
    (truncatedEnvelopingDerivation_mul c _)
  have hgen (v : K) : truncatedEnvelopingGenerator (R := ℝ) c v ∈ S := by
    obtain ⟨v, rfl⟩ := (e).surjective v
    apply cartan_root_induction T H (x := v)
    · intro χ v hv
      apply Submodule.mem_iSup_of_mem (cartanHeightWeight T H χ (heightProjection T.character x))
      rw [Module.End.mem_eigenspace_iff]
      change truncatedEnvelopingDerivation c (nilshadowWeightDerivation T H x)
        (truncatedEnvelopingGenerator c (e v)) = _
      rw [truncatedEnvelopingDerivation_generator, nilshadowWeightDerivation_equiv,
        heightSemisimpleAction_apply_root T H x χ hv, map_smul, map_smul]
    · simpa only [map_zero] using S.zero_mem
    · intro v w hv hw
      simpa only [map_add] using S.add_mem hv hw
  have hle : (⊤ : Subalgebra ℝ (Q c)) ≤ S := by
    rw [← truncatedEnveloping_adjoin_basis (finBasis ℝ K) c]
    apply Algebra.adjoin_le
    rintro _ ⟨i, rfl⟩
    exact hgen _
  apply top_unique
  intro u _
  exact hle (by trivial)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_SolvableRepresentationAnnihilator
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanRealShadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Real split annihilators for the faithful solvable representation

The semisimple derivation preserves word length, while left multiplication
raises it. The finite word-length filtration therefore turns the split
annihilator of the derivation into one for their sum.
-/

noncomputable section
namespace PolycyclicRecognition

open Polynomial Module

variable {L : Type} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {n : ℕ} (T : TriangularAdjoint L n)
  (H : LieSubalgebra ℝ L) [H.IsCartanSubalgebra]

local notation "K" => CartanNilshadow T H
local notation "Q" c => TruncatedEnvelopingAlgebra ℝ K c

theorem solvableTruncatedRepresentation_split_annihilator (c : ℕ) (x : L) :
    ∃ p : ℝ[X], p.Monic ∧ p.Splits ∧
      aeval (solvableTruncatedRepresentation T H c x) p = 0 := by
  let := finiteDimensional_truncatedEnvelopingAlgebra (finBasis ℝ K) c
  let j := truncatedEnvelopingGenerator (R := ℝ) (L := K) c
  let δ := nilshadowWeightDerivation T H x
  let D := truncatedEnvelopingDerivation c δ
  let N := truncatedLeftRepresentation (R := ℝ) c (cartanNilshadowEquiv T H x)
  let B := wordLengthSpan j
  have hgen : Algebra.adjoin ℝ (Set.range j) = ⊤ := by
    apply top_unique
    rw [← truncatedEnveloping_adjoin_basis (finBasis ℝ K) c]
    apply Algebra.adjoin_mono
    rintro _ ⟨i, rfl⟩
    exact ⟨finBasis ℝ K i, rfl⟩
  have hD (k : ℕ) (v : Q c) (hv : v ∈ B k) : D v ∈ B k :=
    wordLengthSpan_derivative j D δ (truncatedEnvelopingDerivation_mul c δ)
      (truncatedEnvelopingDerivation_one c δ)
      (truncatedEnvelopingDerivation_generator c δ) k hv
  have hN (k : ℕ) (v : Q c) (hv : v ∈ B k) : N v ∈ B (k + 1) :=
    wordLengthSpan_generator_mul j k (cartanNilshadowEquiv T H x) hv
  let p := realEigenPolynomial D
  have hp : aeval D p = 0 := realEigenPolynomial_annihilates D
    (solvableWeightDerivation_eigenspaces_span T H c x)
  refine ⟨p ^ c, (realEigenPolynomial_monic D).pow c,
    (realEigenPolynomial_splits D).pow c, ?_⟩
  have heq : solvableTruncatedRepresentation T H c x = D + N := by
    change N + D = D + N
    exact add_comm _ _
  rw [heq]
  exact filtered_polynomial_annihilator B D N (wordLengthSpan_antitone j) hD hN c
    (wordLengthSpan_zero_eq_top j hgen)
    (wordLengthSpan_eq_bot j c (truncatedEnvelopingGenerator_prod_eq_zero c)) p hp

theorem solvableTruncatedRepresentation_genEigenspaces_span (c : ℕ) (x : L) :
    ⨆ r : ℝ, (solvableTruncatedRepresentation T H c x).maxGenEigenspace r = ⊤ := by
  let := finiteDimensional_truncatedEnvelopingAlgebra (finBasis ℝ K) c
  obtain ⟨p, hm, hs, hz⟩ := solvableTruncatedRepresentation_split_annihilator T H c x
  exact iSup_maxGenEigenspace_eq_top_of_split_annihilator _ p hm.ne_zero hs hz

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanRealDiagonal
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Removing the imaginary Cartan eigenvalues on the original flag -/

noncomputable section
namespace PolycyclicRecognition.ComplexCartan
open LieAlgebra LieModule Module

variable {L : Type*} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L]
  (H : LieSubalgebra ℂ L) [H.IsCartanSubalgebra]

set_option maxHeartbeats 1000000 in
theorem semisimpleOperator_diagonal {n : ℕ} (b : Basis (Fin n) ℂ L) (h : H)
    (hh : (LinearMap.toMatrix b b (ad ℂ L (h : L))).IsUpperTriangular) (i : Fin n) :
    LinearMap.toMatrix b b (semisimpleOperator H h) i i =
      LinearMap.toMatrix b b (ad ℂ L (h : L)) i i := by
  let F := LinearMap.toMatrixAlgEquiv b
  have hn : IsNilpotent (F (ad ℂ L (h : L)) - F (semisimpleOperator H h)) := by
    obtain ⟨k,hk⟩ := (semisimpleOperator_jordan H h).2
    refine ⟨k,?_⟩
    rw [← map_sub,← map_pow,hk,map_zero]
  have hz := complex_upper_nilpotent_diagonal _
    (hh.sub (semisimpleOperator_upper H b h hh)) hn i
  exact (sub_eq_zero.mp hz).symm

set_option maxHeartbeats 1000000 in
/-- Each diagonal eigenvalue of the semisimple operator is one of its
root-space eigenvalues, including when several roots have the same value. -/
theorem semisimpleOperator_diagonal_weight {n : ℕ} (b : Basis (Fin n) ℂ L) (h : H)
    (hh : (LinearMap.toMatrix b b (ad ℂ L (h : L))).IsUpperTriangular) (i : Fin n) :
    ∃ χ : Weight ℂ H L, LinearMap.toMatrix b b (semisimpleOperator H h) i i = χ h := by
  classical
  let Q : Polynomial ℂ := ∏ χ : Weight ℂ H L, (Polynomial.X - Polynomial.C (χ h))
  have hQ : Polynomial.aeval (semisimpleOperator H h) Q = 0 := by
    ext x
    apply root_induction H (p := fun v => Polynomial.aeval (semisimpleOperator H h) Q v = 0)
      (x := x)
    · intro χ v hv
      rw [Module.End.aeval_apply_of_mem_apply_eq_smul (semisimpleOperator_apply H h χ hv)]
      have hz : Q.eval (χ h) = 0 := by
        simp only [Q,Polynomial.eval_prod,Polynomial.eval_sub,Polynomial.eval_X,
          Polynomial.eval_C]
        exact Finset.prod_eq_zero (Finset.mem_univ χ) (sub_self _)
      rw [hz,zero_smul]
    · simp
    · intro v w hv hw
      simp only [map_add,hv,hw,add_zero]
  let F := LinearMap.toMatrixAlgEquiv b
  have hu : (F (semisimpleOperator H h)).IsUpperTriangular :=
    semisimpleOperator_upper H b h hh
  have hzero : Q.eval (F (semisimpleOperator H h) i i) = 0 := by
    rw [← complex_matrix_aeval_diagonal (F (semisimpleOperator H h)) hu Q i,
      Polynomial.aeval_algHom_apply, hQ, map_zero]
    rfl
  simp only [Q,Polynomial.eval_prod,Polynomial.eval_sub,Polynomial.eval_X,
    Polynomial.eval_C,Finset.prod_eq_zero_iff,Finset.mem_univ,true_and] at hzero
  obtain ⟨χ,hχ⟩ := hzero
  exact ⟨χ,sub_eq_zero.mp hχ⟩

set_option maxHeartbeats 1000000 in
/-- Polynomial interpolation removes exactly the imaginary diagonal part. -/
theorem imaginaryOperator_diagonal {n : ℕ} (b : Basis (Fin n) ℂ L) (h : H)
    (hh : (LinearMap.toMatrix b b (ad ℂ L (h : L))).IsUpperTriangular) (i : Fin n) :
    LinearMap.toMatrix b b (imaginaryOperator H h) i i =
      imaginaryPart (LinearMap.toMatrix b b (ad ℂ L (h : L)) i i) := by
  obtain ⟨χ,hχ⟩ := semisimpleOperator_diagonal_weight H b h hh i
  obtain ⟨p,hp⟩ := imaginaryOperator_polynomial H h
  have hpχ : p.eval (χ h) = imaginaryPart (χ h) := by
    obtain ⟨v,hv,hv0⟩ := χ.exists_ne_zero
    have he := congrArg (fun f : Module.End ℂ L => f v) hp
    rw [Module.End.aeval_apply_of_mem_apply_eq_smul (semisimpleOperator_apply H h χ hv),
      imaginaryOperator_apply H h χ hv] at he
    exact (smul_left_injective ℂ hv0) he
  let F := LinearMap.toMatrixAlgEquiv b
  change F (semisimpleOperator H h) i i = χ h at hχ
  calc
    F (imaginaryOperator H h) i i = Polynomial.aeval (F (semisimpleOperator H h)) p i i := by
      rw [Polynomial.aeval_algHom_apply,hp]
    _ = p.eval (F (semisimpleOperator H h) i i) :=
      complex_matrix_aeval_diagonal _ (semisimpleOperator_upper H b h hh) p i
    _ = imaginaryPart (F (semisimpleOperator H h) i i) := by rw [hχ,hpχ]
    _ = imaginaryPart (F (ad ℂ L (h : L)) i i) := by
      exact congrArg imaginaryPart (semisimpleOperator_diagonal H b h hh i)

end PolycyclicRecognition.ComplexCartan

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanRealShadowSolvable
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The real shadow retains its nilpotent kernel and is solvable -/

noncomputable section
namespace PolycyclicRecognition
open LieAlgebra

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {n : ℕ} (T : ComplexTriangularAdjoint L n)
  (H : LieSubalgebra ℝ L) [H.IsCartanSubalgebra]

set_option maxHeartbeats 1000000 in
theorem realShadowKernel_nilpotent : LieRing.IsNilpotent (realShadowKernel T H) :=
  (realShadowKernelEquiv T H).nilpotent_iff_equiv_nilpotent.mp T.kernelIdeal_nilpotent

set_option maxHeartbeats 1000000 in
/-- The real shadow is solvable because its derived algebra lies in the
unchanged nilpotent weight kernel. -/
theorem cartanRealShadow_solvable : LieAlgebra.IsSolvable (CartanRealShadow T H) := by
  let K := realShadowKernel T H
  let : LieRing.IsNilpotent K := realShadowKernel_nilpotent T H
  have hder : derivedSeries ℝ (CartanRealShadow T H) 1 ≤ K := by
    intro z hz
    change z ∈ (derivedSeries ℝ (CartanRealShadow T H) 1 : Submodule ℝ (CartanRealShadow T H)) at hz
    rw [coe_derivedSeries_one_eq] at hz
    apply (Submodule.span_le.mpr ?_) hz
    rintro _ ⟨p,q,rfl⟩
    change T.weightMap ((cartanRealShadowEquiv T H).symm ⁅p,q⁆) = 0
    obtain ⟨x,rfl⟩ := (cartanRealShadowEquiv T H).surjective p
    obtain ⟨y,rfl⟩ := (cartanRealShadowEquiv T H).surjective q
    exact cartanRealShadow_bracket_weight T H x y
  obtain ⟨k,hk⟩ := IsSolvable.solvable ℝ K
  have hK : derivedSeriesOfIdeal ℝ (CartanRealShadow T H) k K = ⊥ :=
    (LieIdeal.derivedSeries_eq_bot_iff K k).mp hk
  apply IsSolvable.mk (R := ℝ) (k := k+1)
  apply le_antisymm _ bot_le
  change derivedSeriesOfIdeal ℝ (CartanRealShadow T H) (k+1) ⊤ ≤ ⊥
  rw [derivedSeriesOfIdeal_add]
  exact (derivedSeriesOfIdeal_mono hder k).trans (le_of_eq hK)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_FaithfulTriangularRepresentation
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.abelianRealFiniteDimensional _root_.OAI.PolycyclicRecognition.abelianRealLieAbelian _root_.OAI.PolycyclicRecognition.abelianRealNormedLie _root_.OAI.PolycyclicRecognition.derivationLieSpaceFiniteDimensional _root_.OAI.PolycyclicRecognition.derivationLieSpaceRealNormed _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanRealShadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.polynomialLieIdealSubgroup_normal _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A faithful real triangular representation with nilpotent nilradical

The finite enveloping representation has real split annihilators. Applying
the already proved simultaneous-basis theorem therefore triangularizes it
over the real field, retaining injectivity and nilpotence on the nilradical.
This is the Lie-algebraic part of the Onshuus--Post realization.
-/

noncomputable section
namespace PolycyclicRecognition

open Module LieAlgebra

attribute [local instance 100] LieRing.ofAssociativeRing

variable {L : Type} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  [LieAlgebra.IsSolvable L] {n : ℕ} (T : TriangularAdjoint L n)
  (H : LieSubalgebra ℝ L) [H.IsCartanSubalgebra]

include H in
theorem exists_faithful_triangular_nilradical_representation :
    ∃ m : ℕ, ∃ j : L →ₗ⁅ℝ⁆ Matrix (Fin m) (Fin m) ℝ,
      Function.Injective j ∧ (∀ x, (j x).IsUpperTriangular) ∧
      ∀ x ∈ T.kernelIdeal, IsNilpotent (j x) := by
  let K := CartanNilshadow T H
  let bK := finBasis ℝ K
  let : NormedAddCommGroup K := NormedAddCommGroup.induced K _ bK.equivFun bK.equivFun.injective
  let : NormedSpace ℝ K := NormedSpace.induced ℝ K _ bK.equivFun
  let : RealNormedLieAlgebra K :=
    { (inferInstance : NormedAddCommGroup K), (inferInstance : LieRing K),
      (inferInstance : NormedSpace ℝ K), (inferInstance : LieAlgebra ℝ K) with }
  obtain ⟨c, hfin, hgen⟩ := exists_faithful_truncated_enveloping K (cartanNilshadow_nilpotent T H)
  let := hfin
  let Q := TruncatedEnvelopingAlgebra ℝ K c
  let ρ := solvableTruncatedRepresentation T H c
  let := LieRingModule.compLieHom Q ρ
  let := LieModule.compLieHom Q ρ
  let : LieModule.IsTriangularizable ℝ L Q :=
    ⟨solvableTruncatedRepresentation_genEigenspaces_span T H c⟩
  obtain ⟨m, b, hb⟩ := exists_upperTriangular_lieModule_basis (𝕜 := ℝ) L Q
  let j := (LinearMap.toMatrixAlgEquiv b).toLieEquiv.toLieHom.comp ρ
  refine ⟨m, j, ?_, ?_, ?_⟩
  · exact (LinearMap.toMatrixAlgEquiv b).injective.comp
      (solvableTruncatedRepresentation_injective T H c hgen)
  · exact hb
  · intro x hx
    exact (solvableTruncatedRepresentation_nilpotent T H c x hx).map
      (LinearMap.toMatrixAlgEquiv b).toRingHom

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_PositiveSizeTriangularRepresentation
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Positive-size padding for the triangular representation

A trivial one-dimensional summand handles zero-dimensional Lie algebras
without a separate group-realization case.
-/

noncomputable section
namespace PolycyclicRecognition

attribute [local instance 100] LieRing.ofAssociativeRing

theorem padTriangularMatrix_apply (m : ℕ) (A : Matrix (Fin m) (Fin m) ℝ)
    (i j : Fin m ⊕ Fin 1) :
    padTriangularMatrix m A (finSumFinEquiv i) (finSumFinEquiv j) =
      Matrix.fromBlocks A 0 0 0 i j := by
  simp [padTriangularMatrix, matrixTrivialSummand, Matrix.coe_reindexAlgEquiv]

theorem padTriangularMatrix_injective (m : ℕ) : Function.Injective (padTriangularMatrix m) := by
  intro A B h
  ext i j
  have h' := congrArg (fun M => M (finSumFinEquiv (Sum.inl i))
    (finSumFinEquiv (Sum.inl j))) h
  simpa only [padTriangularMatrix_apply, Matrix.fromBlocks_apply₁₁] using h'

theorem padTriangularMatrix_upper (m : ℕ) (A : Matrix (Fin m) (Fin m) ℝ)
    (hA : A.IsUpperTriangular) : (padTriangularMatrix m A).IsUpperTriangular := by
  intro i j hji
  obtain ⟨i, rfl⟩ := (finSumFinEquiv : Fin m ⊕ Fin 1 ≃ Fin (m + 1)).surjective i
  obtain ⟨j, rfl⟩ := (finSumFinEquiv : Fin m ⊕ Fin 1 ≃ Fin (m + 1)).surjective j
  rw [padTriangularMatrix_apply]
  cases i with
  | inl i =>
    cases j with
    | inl j => exact hA hji
    | inr j => simp
  | inr i => cases j <;> simp

theorem padTriangularMatrix_nilpotent (m : ℕ) (A : Matrix (Fin m) (Fin m) ℝ)
    (hA : A.IsUpperTriangular) (hn : IsNilpotent A) : IsNilpotent (padTriangularMatrix m A) := by
  apply upperTriangular_nilpotent_of_diag_zero _ (padTriangularMatrix_upper m A hA)
  intro i
  obtain ⟨i, rfl⟩ := (finSumFinEquiv : Fin m ⊕ Fin 1 ≃ Fin (m + 1)).surjective i
  rw [padTriangularMatrix_apply]
  cases i with
  | inl i => exact upperTriangular_nilpotent_diag A hA hn i
  | inr i => simp

theorem exists_positive_faithful_triangular_representation
    {L : Type} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
    [LieAlgebra.IsSolvable L] {n : ℕ} (T : TriangularAdjoint L n) :
    ∃ m : ℕ, 0 < m ∧ ∃ j : L →ₗ⁅ℝ⁆ Matrix (Fin m) (Fin m) ℝ,
      Function.Injective j ∧ (∀ x, (j x).IsUpperTriangular) ∧
      ∀ x ∈ T.kernelIdeal, IsNilpotent (j x) := by
  obtain ⟨H, hH, _⟩ := exists_cartan_model T
  let := hH
  obtain ⟨m, j, hj, hu, hn⟩ := exists_faithful_triangular_nilradical_representation T H
  exact ⟨m + 1, Nat.succ_pos m, (padTriangularMatrix m).comp j,
    (padTriangularMatrix_injective m).comp hj,
    fun x => padTriangularMatrix_upper m (j x) (hu x),
    fun x hx => padTriangularMatrix_nilpotent m (j x) (hu x) (hn x hx)⟩

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_RealShadowOperators
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.modelNilradicalLinearAction_apply _root_.OAI.PolycyclicRecognition.modelNilradicalRotation_apply _root_.OAI.PolycyclicRecognition.modelNilradicalRotation_mul _root_.OAI.PolycyclicRecognition.modelNilradicalRotation_one _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.realShadowCartanHom_apply _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The triangular operator underlying the real shadow adjoint action -/

noncomputable section
namespace PolycyclicRecognition
open LieAlgebra Module
open scoped TensorProduct

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {n : ℕ} (T : ComplexTriangularAdjoint L n)
  (H : LieSubalgebra ℝ L) [H.IsCartanSubalgebra]

namespace ComplexTriangularAdjoint

theorem weightCorrectedOperator_complexify (x : L) :
    (T.weightCorrectedOperator H x).baseChange ℂ = T.complexWeightCorrectedOperator H x := by
  apply LinearMap.ext
  intro z
  induction z using OAI.tensorInductionOn with
  | tmul c y =>
    change c ⊗ₜ[ℝ] (⁅x,y⁆ - realImaginaryOperator L H _ y) = _
    rw [TensorProduct.tmul_sub]
    change _ = ⁅(1 : ℂ) ⊗ₜ[ℝ] x,c ⊗ₜ[ℝ] y⁆ -
      ComplexCartan.imaginaryOperator (complexifiedSubalgebra L H) _ (c ⊗ₜ[ℝ] y)
    have he : c ⊗ₜ[ℝ] y = c • ((1 : ℂ) ⊗ₜ[ℝ] y) := by
      rw [TensorProduct.smul_tmul',smul_eq_mul,mul_one]
    rw [he,map_smul,← realImaginaryOperator_complexify,
      TensorProduct.smul_tmul',smul_eq_mul,mul_one]
    simp only [LieAlgebra.ExtendScalars.bracket_tmul,one_mul,
      TensorProduct.smul_tmul',smul_eq_mul,mul_one,LinearMap.comp_apply]
  | add z w hz hw => simp only [map_add,hz,hw]

theorem complexWeightCorrectedOperator_upper (x : L) :
    (LinearMap.toMatrix T.basis T.basis (T.complexWeightCorrectedOperator H x)).IsUpperTriangular := by
  unfold complexWeightCorrectedOperator
  rw [map_sub]
  apply (T.upper _).sub
  exact ComplexCartan.imaginaryOperator_upper (complexifiedSubalgebra L H) T.basis _
    (T.upper _)

/-- The corrected operator has real diagonal in the original complex flag. -/
theorem complexWeightCorrectedOperator_diagonal_im (x : L) (i : Fin n) :
    (LinearMap.toMatrix T.basis T.basis (T.complexWeightCorrectedOperator H x) i i).im = 0 := by
  let h := T.cartanWeightSection H (T.weightMap.rangeRestrict x)
  have he : T.weightMap (h : L) = T.weightMap x := T.cartanWeightSection_weight H _
  have hei := congrFun he i
  change LinearMap.toMatrix T.basis T.basis
      (ad ℂ (ℂ ⊗[ℝ] L) ((1 : ℂ) ⊗ₜ[ℝ] (h : L))) i i =
    LinearMap.toMatrix T.basis T.basis
      (ad ℂ (ℂ ⊗[ℝ] L) ((1 : ℂ) ⊗ₜ[ℝ] x)) i i at hei
  change (LinearMap.toMatrix T.basis T.basis
    (ad ℂ (ℂ ⊗[ℝ] L) ((1 : ℂ) ⊗ₜ[ℝ] x) -
      ComplexCartan.imaginaryOperator (complexifiedSubalgebra L H)
        (realCartanInComplex L H h)) i i).im = 0
  rw [map_sub,Matrix.sub_apply,
    ComplexCartan.imaginaryOperator_diagonal (complexifiedSubalgebra L H) T.basis _ (T.upper _)]
  change (_ - ComplexCartan.imaginaryPart
    (LinearMap.toMatrix T.basis T.basis
      (ad ℂ (ℂ ⊗[ℝ] L) ((1 : ℂ) ⊗ₜ[ℝ] (h : L))) i i)).im = 0
  rw [hei]
  simp [ComplexCartan.imaginaryPart]

end ComplexTriangularAdjoint
end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_RealShadowSplit
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Real triangularizability of the modified Lie algebra -/

noncomputable section
namespace PolycyclicRecognition
open LieAlgebra Module

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {n : ℕ} (T : ComplexTriangularAdjoint L n)
  (H : LieSubalgebra ℝ L) [H.IsCartanSubalgebra]

theorem realShadowAdjoint_apply (x y : L) :
    realShadowAdjoint T H x y =
      ⁅x,y⁆ - T.weightImaginaryAction H x y + T.weightImaginaryAction H y x :=
  cartanRealShadow_bracket T H x y

theorem realShadowAdjoint_weight (x y : L) :
    T.weightMap (realShadowAdjoint T H x y) = 0 :=
  cartanRealShadow_bracket_weight T H x y

theorem realShadowAdjoint_eq_on_kernel (x y : L) (hy : T.weightMap y = 0) :
    realShadowAdjoint T H x y = T.weightCorrectedOperator H x y := by
  rw [realShadowAdjoint_apply,T.weightImaginaryAction_kernel H y hy]
  simp only [LieDerivation.zero_apply,add_zero]
  rfl

theorem realShadowAdjoint_mul (x : L) :
    T.weightCorrectedOperator H x * realShadowAdjoint T H x =
      realShadowAdjoint T H x * realShadowAdjoint T H x := by
  ext y
  exact (realShadowAdjoint_eq_on_kernel T H x _ (realShadowAdjoint_weight T H x y)).symm

/-- The extra correction in the actual adjoint action vanishes on its image.
Thus one extra zero root transfers the real annihilator to that adjoint. -/
theorem realShadowAdjoint_split_annihilator (x : L) :
    ∃ S : Finset ℝ,
      Polynomial.aeval (realShadowAdjoint T H x)
        ((∏ a ∈ S, (Polynomial.X - Polynomial.C a)) ^ (n+1)) = 0 := by
  classical
  obtain ⟨S,hS⟩ := real_split_annihilator_of_complex_triangular
    (T.weightCorrectedOperator H x) T.basis
    (by rw [T.weightCorrectedOperator_complexify H]; exact T.complexWeightCorrectedOperator_upper H x)
    (by rw [T.weightCorrectedOperator_complexify H]; exact T.complexWeightCorrectedOperator_diagonal_im H x)
  let Q : Polynomial ℝ := ∏ a ∈ S, (Polynomial.X - Polynomial.C a)
  let P : Polynomial ℝ := ∏ a ∈ insert 0 S, (Polynomial.X - Polynomial.C a)
  have hz : Polynomial.aeval (realShadowAdjoint T H x) (Polynomial.X * Q^n) = 0 :=
    aeval_X_mul_eq_zero_of_mul_eq _ _ (realShadowAdjoint_mul T H x) _ hS
  have hQP : Q ∣ P := Finset.prod_dvd_prod_of_subset S (insert 0 S) _ (Finset.subset_insert _ _)
  have hXP : Polynomial.X ∣ P := by
    have hd := Finset.dvd_prod_of_mem (fun a : ℝ => (Polynomial.X : Polynomial ℝ) - Polynomial.C a)
      (Finset.mem_insert_self 0 S)
    change (Polynomial.X - Polynomial.C (0 : ℝ)) ∣ P at hd
    rw [Polynomial.C_0,sub_zero] at hd
    exact hd
  have hdiv : Polynomial.X * Q^n ∣ P^(n+1) := by
    simpa only [pow_succ'] using mul_dvd_mul hXP (pow_dvd_pow_of_dvd hQP n)
  exact ⟨insert 0 S,Polynomial.aeval_eq_zero_of_dvd_aeval_eq_zero hdiv hz⟩

theorem realShadowAdjoint_conjugate (x : L) :
    (cartanRealShadowEquiv T H).conjAlgEquiv ℝ (realShadowAdjoint T H x) =
      ad ℝ (CartanRealShadow T H) (cartanRealShadowEquiv T H x) := by
  apply LinearMap.ext
  intro p
  obtain ⟨y,rfl⟩ := (cartanRealShadowEquiv T H).surjective p
  simp only [LinearEquiv.conjAlgEquiv_apply,
    LinearMap.comp_apply,LinearEquiv.coe_coe,LinearEquiv.symm_apply_apply]
  exact (cartanRealShadowEquiv T H).apply_symm_apply _

/-- Every actual adjoint operator of the real shadow splits over the reals. -/
theorem cartanRealShadow_isTriangularizable :
    LieModule.IsTriangularizable ℝ (CartanRealShadow T H) (CartanRealShadow T H) where
  maxGenEigenspace_eq_top p := by
    obtain ⟨x,rfl⟩ := (cartanRealShadowEquiv T H).surjective p
    obtain ⟨S,hS⟩ := realShadowAdjoint_split_annihilator T H x
    apply iSup_maxGenEigenspace_eq_top_of_annihilating_product _ S (n+1)
    change Polynomial.aeval (ad ℝ (CartanRealShadow T H) (cartanRealShadowEquiv T H x)) _ = 0
    rw [← realShadowAdjoint_conjugate T H x,Polynomial.aeval_algHom_apply,hS,map_zero]

/-- A genuine simultaneous real upper triangular adjoint basis. -/
theorem nonempty_cartanRealShadow_triangularAdjoint :
    ∃ m : ℕ, Nonempty (TriangularAdjoint (CartanRealShadow T H) m) := by
  let := cartanRealShadow_solvable T H
  let := cartanRealShadow_isTriangularizable T H
  exact nonempty_triangularAdjoint_of_split (CartanRealShadow T H)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_RealShadowRepresentation
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A faithful triangular representation of the real shadow -/

noncomputable section
namespace PolycyclicRecognition
open scoped Matrix.Norms.Operator
attribute [local instance 100] LieRing.ofAssociativeRing

variable {L : Type} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {a : ℕ} (T : ComplexTriangularAdjoint L a)
  (H : LieSubalgebra ℝ L) [H.IsCartanSubalgebra]

/-- The nilpotent weight kernel acts by nilpotent matrices in a faithful
real triangular representation of the modified algebra. -/
theorem exists_realShadow_triangularRepresentation :
    ∃ m : ℕ, 0 < m ∧
      ∃ j : CartanRealShadow T H →ₗ⁅ℝ⁆ Matrix (Fin m) (Fin m) ℝ,
        Function.Injective j ∧ (∀ x, (j x).IsUpperTriangular) ∧
        ∀ x ∈ realShadowKernel T H, IsNilpotent (j x) := by
  let := cartanRealShadow_solvable T H
  let := realShadowKernel_nilpotent T H
  obtain ⟨n, ⟨A⟩⟩ := nonempty_cartanRealShadow_triangularAdjoint T H
  obtain ⟨m, hm, j, hj, hu, hn⟩ := exists_positive_faithful_triangular_representation A
  refine ⟨m, hm, j, hj, hu, fun x hx => hn x ?_⟩
  exact A.nilpotent_ideal_le_kernelIdeal (realShadowKernel T H) hx

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_RotationTriangularRepresentation
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A faithful triangular representation of the rotational group -/

noncomputable section
namespace PolycyclicRecognition
open scoped Manifold Matrix.Norms.Operator
attribute [local instance 100] LieRing.ofAssociativeRing

variable {E G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MetricSpace G] [ChartedSpace E G]
  [Group G] [LieGroup (𝓘(ℝ,E)) ⊤ G]
  {a : ℕ} {T : ComplexTriangularAdjoint (GroupLieAlgebra (𝓘(ℝ,E)) G) a}
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ,E)) G)} [H.IsCartanSubalgebra]
  {Exp : GroupLieAlgebra (𝓘(ℝ,E)) G → G}

namespace ComplexWeightFactorModel
variable (F : ComplexWeightFactorModel T H Exp) (hExp : IsGroupExponential Exp)
attribute [local instance] semidirectProductTopology

theorem exists_faithful_rotation_triangular_representation_oai :
    ∃ m : ℕ, 0 < m ∧
      ∃ j : CartanRealShadow T H →ₗ⁅ℝ⁆ Matrix (Fin m) (Fin m) ℝ,
        (Function.Injective j ∧ (∀ x, (j x).IsUpperTriangular) ∧
          (∀ x ∈ realShadowKernel T H, IsNilpotent (j x))) ∧
      ∃ ρ : F.SmoothRotationalModification hExp →* (Matrix (Fin m) (Fin m) ℝ)ˣ,
        Continuous ρ ∧ Function.Injective ρ ∧
        ∀ (x : T.kernelIdeal) (h : H),
          ρ (F.nilpotentFactorToRotation hExp (F.ExpN (F.N.equiv x)) *
            F.cartanFactorToRotation hExp (F.ExpD (F.D.equiv h))) =
            algebraExpUnit (j (cartanRealShadowEquiv T H x)) *
              algebraExpUnit (j (cartanRealShadowEquiv T H h)) := by
  refine exists_faithful_matrix_integration
    (fun _ j => Function.Injective j ∧ (∀ x, (j x).IsUpperTriangular) ∧
      (∀ x ∈ realShadowKernel T H, IsNilpotent (j x)))
    (fun x : T.kernelIdeal => cartanRealShadowEquiv T H x)
    (fun h : H => cartanRealShadowEquiv T H h)
    (fun x h => F.rotationExponentialProduct hExp (x,h))
    (exists_realShadow_triangularRepresentation T H) ?_ ?_
  · intro m j _
    exact F.exists_integrated_rotation_representation hExp j
  · intro m j hj ρ he
    exact F.rotationRepresentation_faithful hExp j hj.1 hj.2.1 ρ he

end ComplexWeightFactorModel
end PolycyclicRecognition

end

end OAI
end

theorem solution : type_of% @OAI.PolycyclicRecognition.ComplexWeightFactorModel.exists_faithful_rotation_triangular_representation_oai := @OAI.PolycyclicRecognition.ComplexWeightFactorModel.exists_faithful_rotation_triangular_representation_oai
