-- Prove2me | solution 1 for OAI.PolycyclicRecognition.CartanWordModel.exists_uniform_identical_neighbor_profiles
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-03T00:15:04.630476+00:00
-- url     : https://prove2.me/submissions/164388da-e9c0-43a3-a3bb-576bd9ac027b

import Mathlib
import Definitions.Def_PolycyclicRecognition
import Definitions.Def_OAIQ093D021
import Theorems.Thm_OAI_PolycyclicRecognition_CartanWordModel_cartan_supported_profile_affine_sequence
import Theorems.Thm_OAI_PolycyclicRecognition_CartanWordModel_exists_uniform_neighbor_label_threshold_m
import Theorems.Thm_OAI_PolycyclicRecognition_CartanWordModel_exists_uniform_polar_offset_threshold

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_ConeFacetTemplate
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A fixed polar template near a generator facet

The template radius is independent of the small chart enlargement. Only
its centre moves inward with that enlargement.
-/

noncomputable section
namespace PolycyclicRecognition

open Set

variable {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
  [FiniteDimensional ℝ W]

/-- The Euclidean contact point has strict slack in every other oriented
ray. This is the equality case of the Cauchy--Schwarz inequality. -/
theorem exists_weight_contact_point (α : W →L[ℝ] ℝ) (hα : α ≠ 0) :
    ∃ p : W, ‖p‖ = 1 ∧ α p = ‖α‖ ∧ ∀ β : W →L[ℝ] ℝ, β ≠ 0 →
      (¬ ∃ t : ℝ, 0 < t ∧ β = t • α) → β p < ‖β‖ := by
  let v := (InnerProductSpace.toDual ℝ W).symm α
  have hv : v ≠ 0 := by
    intro h
    apply hα
    simpa [v] using congrArg (InnerProductSpace.toDual ℝ W) h
  have hvnorm : ‖v‖ = ‖α‖ := (InnerProductSpace.toDual ℝ W).symm.norm_map α
  let p := ‖v‖⁻¹ • v
  have hp : ‖p‖ = 1 := by simp [p, norm_smul, norm_ne_zero_iff.mpr hv]
  have heval (β : W →L[ℝ] ℝ) (x : W) :
      inner ℝ ((InnerProductSpace.toDual ℝ W).symm β) x = β x :=
    InnerProductSpace.toDual_symm_apply
  refine ⟨p, hp, ?_, ?_⟩
  · rw [← heval α, show (InnerProductSpace.toDual ℝ W).symm α = v from rfl]
    simp only [p, real_inner_smul_right, real_inner_self_eq_norm_sq]
    rw [← hvnorm]
    field_simp
  · intro β hβ hnot
    let b := (InnerProductSpace.toDual ℝ W).symm β
    have hb : b ≠ 0 := by
      intro h
      apply hβ
      simpa [b] using congrArg (InnerProductSpace.toDual ℝ W) h
    have hbnorm : ‖b‖ = ‖β‖ := (InnerProductSpace.toDual ℝ W).symm.norm_map β
    have hneq : ‖p‖ • b ≠ ‖b‖ • p := by
      intro h
      have hrel : b = (‖b‖ / ‖v‖) • v := by
        simpa [hp, p, smul_smul, div_eq_mul_inv] using h
      apply hnot
      refine ⟨‖b‖ / ‖v‖, div_pos (norm_pos_iff.mpr hb) (norm_pos_iff.mpr hv), ?_⟩
      have hh := congrArg (InnerProductSpace.toDual ℝ W) hrel
      simpa [b, v] using hh
    have hh := inner_lt_norm_mul_iff_real.mpr hneq
    rw [hp, mul_one, hbnorm] at hh
    change inner ℝ ((InnerProductSpace.toDual ℝ W).symm β) p < ‖β‖ at hh
    rwa [heval β p] at hh

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_FiniteLieNorm
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Bracket bounds from finitely many structure constants

The norm is the coordinate maximum in a specified basis. Consequently the
bound applies uniformly to every rescaled word basis from the box calculus.
-/

noncomputable section

namespace PolycyclicRecognition

open Module
open scoped BigOperators

variable {L J : Type} [LieRing L] [LieAlgebra ℝ L] [Fintype J]
  (b : Basis J ℝ L)

/-- Bounding the finitely many basis brackets bounds the full bracket as a
bilinear map, in the coordinate maximum norm. -/
theorem norm_basis_bracket_le {C : ℝ} (hC : 0 ≤ C)
    (hbracket : ∀ i j l, |b.repr ⁅b i, b j⁆ l| ≤ C) (x y : L) :
    ‖b.equivFun ⁅x, y⁆‖ ≤
      ((Fintype.card J : ℝ) ^ 2 * C) * ‖b.equivFun x‖ * ‖b.equivFun y‖ := by
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro l
  change |b.repr ⁅x, y⁆ l| ≤ _
  rw [basis_bracket_coordinate b]
  calc
    _ ≤ ∑ i, ∑ j, |b.repr x i * b.repr y j * b.repr ⁅b i, b j⁆ l| :=
      (Finset.abs_sum_le_sum_abs _ _).trans
        (Finset.sum_le_sum (fun _ _ => Finset.abs_sum_le_sum_abs _ _))
    _ ≤ ∑ _i : J, ∑ _j : J, ‖b.equivFun x‖ * ‖b.equivFun y‖ * C := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      rw [abs_mul, abs_mul]
      have hx : |b.repr x i| ≤ ‖b.equivFun x‖ := norm_le_pi_norm (b.equivFun x) i
      have hy : |b.repr y j| ≤ ‖b.equivFun y‖ := norm_le_pi_norm (b.equivFun y) j
      exact mul_le_mul (mul_le_mul hx hy (abs_nonneg _) (norm_nonneg _))
        (hbracket i j l) (abs_nonneg _) (by positivity)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] <;> ring

theorem bracketWordLength_eq_nodes_add_one {I : Type} (w : FreeMagma I) :
    bracketWordLength w = bracketWordNodes w + 1 := by
  induction w using FreeMagma.rec with
  | of i => rfl
  | mul u v hu hv => simp only [bracketWordLength, bracketWordNodes, hu, hv]; omega

/-- Evaluation of each Lie word is bounded by the number of its brackets and
letters. This is uniform over a family with bounded structure constants. -/
theorem norm_basis_evalBracketWord_le {I : Type} (X : I → L)
    {C M : ℝ} (hC : 0 ≤ C) (hM : 0 ≤ M)
    (hbracket : ∀ i j l, |b.repr ⁅b i, b j⁆ l| ≤ C)
    (hX : ∀ i, ‖b.equivFun (X i)‖ ≤ M) (w : FreeMagma I) :
    ‖b.equivFun (evalBracketWord X w)‖ ≤
      ((Fintype.card J : ℝ) ^ 2 * C) ^ bracketWordNodes w * M ^ bracketWordLength w := by
  let K : ℝ := (Fintype.card J : ℝ) ^ 2 * C
  have hK : 0 ≤ K := by positivity
  induction w using FreeMagma.rec with
  | of i => simpa only [evalBracketWord, bracketWordNodes, bracketWordLength, pow_zero,
      pow_one, one_mul] using hX i
  | mul u v hu hv =>
    calc
      _ ≤ K * ‖b.equivFun (evalBracketWord X u)‖ * ‖b.equivFun (evalBracketWord X v)‖ :=
        norm_basis_bracket_le b hC hbracket _ _
      _ ≤ K * (K ^ bracketWordNodes u * M ^ bracketWordLength u) *
          (K ^ bracketWordNodes v * M ^ bracketWordLength v) := by
        exact mul_le_mul (mul_le_mul_of_nonneg_left hu hK) hv
          (norm_nonneg _) (by positivity)
      _ = _ := by simp only [bracketWordNodes, bracketWordLength, pow_add, pow_one] <;> ring

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_DynkinWords
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.CartanFactorModel.realScaleProfile_apply _root_.OAI.PolycyclicRecognition.basisDynkinParameter_zero _root_.OAI.PolycyclicRecognition.bracketWordDifferential_mul _root_.OAI.PolycyclicRecognition.dynkinRightTranslation_apply _root_.OAI.PolycyclicRecognition.dynkinRightTranslation_symm_apply _root_.OAI.PolycyclicRecognition.exponentialHomOfDynkin_apply_exp _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.OAI.PolycyclicRecognition.wordBasisOfDet_val _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Bounded finite Dynkin expansions

The analytic BCH input is separated from its elementary coordinate estimate.
A degree-`c` expansion in right-nested words, with uniformly bounded
coefficients, has polynomial growth in the number of input factors.
-/

noncomputable section

namespace PolycyclicRecognition

open Module
open scoped BigOperators

@[simp] theorem rightNestedWord_length {I : Type} (d : ℕ) (f : Fin (d + 1) → I) :
    bracketWordLength (rightNestedWord d f) = d + 1 := by
  rw [bracketWordLength_eq_nodes_add_one, rightNestedWord_nodes]

variable {L J : Type} [LieRing L] [LieAlgebra ℝ L] [Fintype J]

/-- All coefficient counting and bracket estimates are proved here; only the
identity identifying this polynomial with the group product is external. -/
theorem norm_finiteDynkinPolynomial_le (b : Basis J ℝ L) {c n : ℕ}
    (coeff : DynkinCoefficients c n) (hcoeff : ∀ d w, |coeff d w| ≤ (2 : ℝ) ^ c)
    (X : Fin n → L) {C M : ℝ} (hC : 0 ≤ C) (hM : 0 ≤ M)
    (hbracket : ∀ i j l, |b.repr ⁅b i, b j⁆ l| ≤ C)
    (hX : ∀ i, ‖b.equivFun (X i)‖ ≤ M) :
    ‖b.equivFun (finiteDynkinPolynomial coeff X)‖ ≤
      (c : ℝ) * 2 ^ c * (1 + (Fintype.card J : ℝ) ^ 2 * C) ^ c *
        (1 + M) ^ c * (1 + (n : ℝ)) ^ c := by
  let K : ℝ := (Fintype.card J : ℝ) ^ 2 * C
  let A : ℝ := 2 ^ c * (1 + K) ^ c * (1 + M) ^ c
  have hK : 0 ≤ K := by positivity
  have hA : 0 ≤ A := by positivity
  have hterm (d : Fin c) (w : Fin (d.val + 1) → Fin n) :
      ‖b.equivFun (coeff d w • evalBracketWord X (rightNestedWord d.val w))‖ ≤ A := by
    rw [map_smul, norm_smul, Real.norm_eq_abs]
    have hw := norm_basis_evalBracketWord_le b X hC hM hbracket hX
      (rightNestedWord d.val w)
    simp only [rightNestedWord_nodes, rightNestedWord_length] at hw
    have hkpow : K ^ d.val ≤ (1 + K) ^ c :=
      (pow_le_pow_left₀ hK (by linarith) d.val).trans
        (pow_le_pow_right₀ (by linarith) d.isLt.le)
    have hmpow : M ^ (d.val + 1) ≤ (1 + M) ^ c :=
      (pow_le_pow_left₀ hM (by linarith) (d.val + 1)).trans
        (pow_le_pow_right₀ (by linarith) d.isLt)
    have hw' : ‖b.equivFun (evalBracketWord X (rightNestedWord d.val w))‖ ≤
        (1 + K) ^ c * (1 + M) ^ c :=
      hw.trans (mul_le_mul hkpow hmpow (pow_nonneg hM _) (by positivity))
    have ht : |coeff d w| * ‖b.equivFun (evalBracketWord X (rightNestedWord d.val w))‖ ≤
        2 ^ c * ((1 + K) ^ c * (1 + M) ^ c) :=
      mul_le_mul (hcoeff d w) hw' (norm_nonneg _) (by positivity)
    simpa only [A, mul_assoc] using ht
  have hdegree (d : Fin c) :
      ‖b.equivFun (∑ w : Fin (d.val + 1) → Fin n,
        coeff d w • evalBracketWord X (rightNestedWord d.val w))‖ ≤
        A * (1 + (n : ℝ)) ^ c := by
    rw [map_sum]
    apply (norm_sum_le _ _).trans
    calc
      _ ≤ ∑ _w : Fin (d.val + 1) → Fin n, A :=
        Finset.sum_le_sum (fun w _ => hterm d w)
      _ = (n : ℝ) ^ (d.val + 1) * A := by simp
      _ ≤ (1 + (n : ℝ)) ^ c * A := by
        apply mul_le_mul_of_nonneg_right _ hA
        exact (pow_le_pow_left₀ (Nat.cast_nonneg _) (by linarith) (d.val + 1)).trans
          (pow_le_pow_right₀ (by have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith) d.isLt)
      _ = _ := mul_comm _ _
  unfold finiteDynkinPolynomial
  rw [map_sum]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ _d : Fin c, A * (1 + (n : ℝ)) ^ c := Finset.sum_le_sum (fun d _ => hdegree d)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; dsimp [A, K] <;> ring

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
/-- The algebraic structure-constant bound in the box-calculus lemma. -/
theorem exists_uniform_normalized_bracket_bound (X : I → L) {k : ℕ}
    (hk : lowerCentralSeries ℝ L L k = ⊥)
    (b₀ : Basis (Fin (finrank ℝ L)) ℝ L) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (s : I → ℝ)
      (β : WordBasisSelections X (boundedBracketWords k)),
      IsMaximizingColumnBasis (wordListCoordinates X (boundedBracketWords k) b₀)
        (fun w => bracketWordExponent s w) β.val →
      ∀ (i j l : Fin (finrank ℝ L)) (r : ℝ), 0 ≤ r →
        |(WordBasisSelections.basis X (boundedBracketWords k) β).repr
            ⁅WordBasisSelections.basis X (boundedBracketWords k) β i,
              WordBasisSelections.basis X (boundedBracketWords k) β j⁆ l *
          Real.exp (r * (bracketWordExponent s (β.val i) +
            bracketWordExponent s (β.val j) - bracketWordExponent s (β.val l)))| ≤ C := by
  let S := boundedBracketWords (I := I) k
  let v := wordListCoordinates X S b₀
  obtain ⟨C, hC, hbound⟩ := exists_uniform_normalized_coordinate_bound v
  refine ⟨C, hC, ?_⟩
  intro s β hβ i j l r hr
  let b := WordBasisSelections.basis X S β
  by_cases hz : ⁅b i, b j⁆ = 0
  · change |b.repr ⁅b i, b j⁆ l * _| ≤ C
    rw [hz, map_zero, Finsupp.zero_apply, zero_mul, abs_zero]
    exact hC
  · let w : S := ⟨(β.val i : FreeMagma I) * β.val j, by
      apply (mem_boundedBracketWords _ _).mpr
      by_contra hn
      have hzero := evalBracketWord_eq_zero_of_depth X hk
        ((β.val i : FreeMagma I) * β.val j) (Nat.le_of_not_lt hn)
      have he : evalBracketWord X ((β.val i : FreeMagma I) * β.val j) = ⁅b i, b j⁆ := by
        rw [evalBracketWord_mul]
        exact congrArg₂ (fun x y : L => ⁅x, y⁆)
          (WordBasisSelections.eval_words X S β i) (WordBasisSelections.eval_words X S β j)
      exact hz (he.symm.trans hzero)⟩
    have he : evalBracketWord X w = ⁅b i, b j⁆ := by
      change ⁅evalBracketWord X (β.val i), evalBracketWord X (β.val j)⁆ = _
      exact congrArg₂ (fun x y : L => ⁅x, y⁆)
        (WordBasisSelections.eval_words X S β i) (WordBasisSelections.eval_words X S β j)
    have hc : columnCoordinates v β.val w l = b.repr ⁅b i, b j⁆ l := by
      rw [columnCoordinates_eq_wordBasis_repr X S b₀ β w]
      change b.repr (evalBracketWord X w) l = _
      rw [he]
    have hw : bracketWordExponent s w =
        bracketWordExponent s (β.val i) + bracketWordExponent s (β.val j) :=
      bracketWordExponent_mul s _ _
    have h := hbound (fun w => bracketWordExponent s w) β.val hβ w l r hr
    simpa only [hc, hw] using h

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

omit [FiniteDimensional ℝ L] in
/-- Uniform boundedness holds for the structure constants of the actual
rescaled Lie bracket, not just for a formal coefficient expression. -/
theorem exists_uniform_rescaled_structureConstant_bound (X : I → L) {k : ℕ}
    (hk : lowerCentralSeries ℝ L L k = ⊥)
    (b₀ : Basis (Fin (finrank ℝ L)) ℝ L) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (s : I → ℝ)
      (β : WordBasisSelections X (boundedBracketWords k)),
      IsMaximizingColumnBasis (wordListCoordinates X (boundedBracketWords k) b₀)
        (fun w => bracketWordExponent s w) β.val →
      ∀ (r : ℝ), 0 ≤ r →
      let b := exponentialRescaleBasis
        (WordBasisSelections.basis X (boundedBracketWords k) β)
        (fun i => bracketWordExponent s (β.val i)) r
      ∀ i j l, |b.repr ⁅b i, b j⁆ l| ≤ C := by
  obtain ⟨C, hC, hbound⟩ := exists_uniform_normalized_bracket_bound X hk b₀
  refine ⟨C, hC, ?_⟩
  intro s β hβ r hr
  dsimp only
  intro i j l
  rw [repr_exponentialRescaleBasis_bracket]
  exact hbound s β hβ i j l r hr

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_SequenceSubexponentialOperations
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite algebra of losses along the profile-scale sequence -/

namespace PolycyclicRecognition

open Filter
open scoped Topology

variable {scale : ℕ → ℝ}

theorem HasSubexponentialUpperBoundSeq.pow {f : ℕ → ℝ}
    (hf : HasSubexponentialUpperBoundSeq scale f) (hs : Tendsto scale atTop atTop)
    (hf0 : ∀ᶠ n in atTop, 0 ≤ f n) (k : ℕ) :
    HasSubexponentialUpperBoundSeq scale (fun n => f n ^ k) := by
  induction k with
  | zero => simpa using sequence_subexponential_upper_const hs 1
  | succ k ih =>
    simpa only [pow_succ] using ih.mul hf (hf0.mono (fun _ h => pow_nonneg h k))

theorem HasSubexponentialUpperBoundSeq.add {f g : ℕ → ℝ}
    (hf : HasSubexponentialUpperBoundSeq scale f) (hg : HasSubexponentialUpperBoundSeq scale g)
    (hs : Tendsto scale atTop atTop) :
    HasSubexponentialUpperBoundSeq scale (fun n => f n + g n) := by
  intro ε hε
  filter_upwards [hf (ε / 2) (half_pos hε), hg (ε / 2) (half_pos hε),
    sequence_subexponential_upper_const hs 2 (ε / 2) (half_pos hε)] with n hn hm htwo
  have he : Real.exp (ε * scale n) =
      Real.exp (ε / 2 * scale n) * Real.exp (ε / 2 * scale n) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [he]
  nlinarith [Real.exp_pos (ε / 2 * scale n)]

end PolycyclicRecognition

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_SequenceSubexponentialRate
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A common vanishing rate for subexponential coordinate bounds -/

noncomputable section
namespace PolycyclicRecognition

open Filter
open scoped Topology

/-- A subexponential upper bound can be expressed by one nonnegative
vanishing exponential rate, including every initial scale. -/
theorem exists_sequence_subexponential_rate
    (scale R : ℕ → ℝ) (hs : ∀ n, 0 < scale n)
    (hR : HasSubexponentialUpperBoundSeq scale R) :
    ∃ ε : ℕ → ℝ, (∀ n, 0 ≤ ε n) ∧ Tendsto ε atTop (𝓝 0) ∧
      ∀ n, R n ≤ Real.exp (scale n * ε n) := by
  let ε := fun n => Real.log (max 1 (R n)) / scale n
  have hpos n : 0 < max 1 (R n) := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hε n : 0 ≤ ε n := div_nonneg (Real.log_nonneg (le_max_left _ _)) (hs n).le
  refine ⟨ε, hε, ?_, ?_⟩
  · apply tendsto_order.2
    constructor
    · intro a ha
      exact Eventually.of_forall (fun n => ha.trans_le (hε n))
    · intro a ha
      filter_upwards [hR (a / 2) (half_pos ha)] with n hn
      have hmax : max 1 (R n) ≤ Real.exp ((a / 2) * scale n) :=
        max_le (Real.one_le_exp (mul_nonneg (half_pos ha).le (hs n).le)) hn
      have hlog : Real.log (max 1 (R n)) ≤ (a / 2) * scale n :=
        (Real.log_le_iff_le_exp (hpos n)).mpr hmax
      exact ((div_le_iff₀ (hs n)).mpr hlog).trans_lt (half_lt_self ha)
  · intro n
    have he : scale n * ε n = Real.log (max 1 (R n)) := by
      dsimp only [ε]
      field_simp [(hs n).ne']
    rw [he, Real.exp_log (hpos n)]
    exact le_max_right _ _

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_NilpotentBoxes
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Products in actual nilpotent exponential boxes

The published finite BCH identity is transported to a chosen Lie-algebra
model. The uniform normalized structure constants then give the polynomial
product bound in the manuscript's box calculus, for every height scale and
letter support. No coordinate growth conclusion is assumed as an input.
-/

noncomputable section

namespace PolycyclicRecognition

open Module LieModule
open scoped BigOperators Manifold

variable {L : Type} [LieRing L] [LieAlgebra ℝ L]

variable {E G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace G] [ChartedSpace E G] [Group G]
  [LieGroup (𝓘(ℝ, E)) ⊤ G] [T2Space G]

/-- The polynomial product estimate in any basis with bounded brackets. -/
theorem product_mem_exponentialCoordinateBox
    (dynkin : NilpotentDynkinExpansionInput E G)
    (e : L ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, E)) G)
    (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G) (hExp : IsGroupExponential Exp)
    {c n : ℕ} (hc : lowerCentralSeries ℝ L L c = ⊥)
    {J : Type} [Fintype J] (b : Basis J ℝ L)
    {C R : ℝ} (hC : 0 ≤ C) (hR : 0 ≤ R)
    (hbracket : ∀ i j l, |b.repr ⁅b i, b j⁆ l| ≤ C)
    (g : Fin n → G) (hg : ∀ i, g i ∈ exponentialCoordinateBox (Exp ∘ e) b R) :
    (List.ofFn g).prod ∈ exponentialCoordinateBox (Exp ∘ e) b
      ((c : ℝ) * 2 ^ c * (1 + (Fintype.card J : ℝ) ^ 2 * C) ^ c *
        (1 + R) ^ c * (1 + (n : ℝ)) ^ c) := by
  choose X hX hbound using hg
  obtain ⟨coeff, hcoeff, hprod⟩ := model_finiteDynkinExpansion dynkin e Exp hExp hc n
  refine ⟨finiteDynkinPolynomial coeff X, ?_,
    norm_finiteDynkinPolynomial_le b coeff hcoeff X hC hR hbracket hbound⟩
  exact (hprod X).symm.trans (congrArg List.prod (congrArg List.ofFn (funext hX)))

variable {I : Type} [Fintype I] [DecidableEq I]

/-- Uniform polynomial multiplication in all maximizing scaled word boxes.
The constant depends only on the fixed finite Lie model. -/
theorem exists_uniform_word_box_product_bound
    (dynkin : NilpotentDynkinExpansionInput E G)
    (e : L ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, E)) G)
    (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G) (hExp : IsGroupExponential Exp)
    (X : I → L) {c : ℕ} (hc : lowerCentralSeries ℝ L L c = ⊥)
    (b₀ : Basis (Fin (finrank ℝ L)) ℝ L) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (s : I → ℝ)
      (β : WordBasisSelections X (boundedBracketWords c)),
      IsMaximizingColumnBasis (wordListCoordinates X (boundedBracketWords c) b₀)
        (fun w => bracketWordExponent s w) β.val →
      ∀ r : ℝ, 0 ≤ r → ∀ n : ℕ, ∀ R : ℝ, 0 ≤ R → ∀ g : Fin n → G,
      let b := exponentialRescaleBasis (WordBasisSelections.basis X (boundedBracketWords c) β)
        (fun i => bracketWordExponent s (β.val i)) r
      (∀ i, g i ∈ exponentialCoordinateBox (Exp ∘ e) b R) →
      (List.ofFn g).prod ∈ exponentialCoordinateBox (Exp ∘ e) b
        (C * (1 + (n : ℝ)) ^ c * (1 + R) ^ c) := by
  obtain ⟨K, hK, hbound⟩ := exists_uniform_rescaled_structureConstant_bound X hc b₀
  refine ⟨(c : ℝ) * 2 ^ c * (1 + (finrank ℝ L : ℝ) ^ 2 * K) ^ c,
    by positivity, ?_⟩
  intro s β hβ r hr n R hR g
  dsimp only
  intro hg
  have hp := product_mem_exponentialCoordinateBox dynkin e Exp hExp hc
    (exponentialRescaleBasis (WordBasisSelections.basis X (boundedBracketWords c) β)
      (fun i => bracketWordExponent s (β.val i)) r)
    hK hR (hbound s β hβ r hr) g hg
  simpa only [Fintype.card_fin, mul_assoc, mul_left_comm, mul_comm] using hp

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanGroupBoxes
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instDecidableEqConeMixedWords _root_.OAI.PolycyclicRecognition.CartanWordModel.instFintypeConeMixedWords _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual group boxes for the Cartan word model

The finite Cartan construction supplies the bases, bracket bounds, nilpotence
and support exponents used here. The only external group facts are the two
explicit published exponential inputs. In particular no box multiplication or
volume estimate is an assumption.
-/

noncomputable section

namespace PolycyclicRecognition.CartanWordModel

open Module LieModule MeasureTheory
open scoped Manifold

variable {L W : Type} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {H : LieSubalgebra ℝ L} [H.IsCartanSubalgebra] (M : CartanWordModel H)
  {a : ℕ} (T : TriangularAdjoint L a)
  (hunimod : ∀ x : L, LinearMap.trace ℝ L (LieAlgebra.ad ℝ L x) = 0)
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)

variable {EN N : Type} [NormedAddCommGroup EN] [NormedSpace ℝ EN]
  [FiniteDimensional ℝ EN] [TopologicalSpace N] [ChartedSpace EN N] [Group N]
  [LieGroup (𝓘(ℝ, EN)) ⊤ N] [T2Space N]
  (eN : cartanRootIdeal H ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, EN)) N)
  (Exp : GroupLieAlgebra (𝓘(ℝ, EN)) N → N) (hExp : IsGroupExponential Exp)

include hExp

set_option maxHeartbeats 1000000 in
/-- A uniform product estimate for the actual Cartan boxes. No assumptions
about compactness or convexity of the template are needed for this part. -/
theorem exists_groupBox_product_bound
    (dynkin : NilpotentDynkinExpansionInput EN N)
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (E : Set W) (β : M.Bases),
      IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
        (M.boxCost T hunimod eW E) β.val →
      ∀ r : ℝ, 0 ≤ r → ∀ n : ℕ, ∀ R : ℝ, 0 ≤ R → ∀ g : Fin n → N,
      (∀ i, g i ∈ M.groupBox T hunimod eW (Exp ∘ eN) E β r R) →
      (List.ofFn g).prod ∈ M.groupBox T hunimod eW (Exp ∘ eN) E β r
        (C * (1 + (n : ℝ)) ^ M.bound * (1 + R) ^ M.bound) := by
  obtain ⟨C, hC, hbound⟩ := exists_uniform_word_box_product_bound dynkin eN Exp hExp
    M.letter M.bound_zero b₀
  exact ⟨C, hC, fun E β hβ r hr n R hR g hg =>
    hbound ((M.supportIn T hunimod eW).weightSupport E) β hβ r hr n R hR g hg⟩

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_AffineSheetAgreement
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Local agreement identifies affine sheet profiles on the whole domain -/

noncomputable section
namespace PolycyclicRecognition

open Set Filter MeasureTheory
open scoped Topology

/-- A continuous image of a supported sample is supported by its image law. -/
theorem mem_support_map_of_continuous
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [MeasurableSpace X] [MeasurableSpace Y] [BorelSpace X] [BorelSpace Y]
    (μ : ProbabilityMeasure X) (f : X → Y) (hf : Continuous f)
    {x : X} (hx : x ∈ (μ : Measure X).support) :
    f x ∈ (ProbabilityMeasure.map μ (f := f) (by first | exact hf.measurable.aemeasurable | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability) : Measure Y).support := by
  apply (Measure.mem_support_iff_forall (f x)).mpr
  intro U hU
  obtain ⟨V, hVU, hV, hxV⟩ := mem_nhds_iff.mp hU
  apply lt_of_lt_of_le _ (measure_mono hVU)
  change 0 < Measure.map f (μ : Measure X) V
  rw [Measure.map_apply hf.measurable hV.measurableSet]
  exact (Measure.mem_support_iff_forall x).mp hx _
    (hf.continuousAt.preimage_mem_nhds (hV.mem_nhds hxV))

/-- Projection of a weak limit of sampled pairs is the weak limit of the
projected samples, with no change of sampling law. -/
theorem sampled_projection_tendsto
    {A X Y : Type} [MeasurableSpace A]
    [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (μ : ℕ → ProbabilityMeasure A) (p : ℕ → A → X) (hp : ∀ n, Measurable (p n))
    (ν : ProbabilityMeasure X)
    (hν : Tendsto (fun n => ProbabilityMeasure.map (μ n) (f := (p n)) (by first | exact (hp n).aemeasurable | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)) atTop (𝓝 ν))
    (f : X → Y) (hf : Continuous f) :
    Tendsto (fun n => ProbabilityMeasure.map (μ n) (f := (f ∘ p n)) (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)) atTop
      (𝓝 (ProbabilityMeasure.map ν (f := f) (by first | exact hf.measurable.aemeasurable | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability))) := by
  have ht := (ProbabilityMeasure.continuous_map hf).tendsto ν |>.comp hν
  apply ht.congr'
  filter_upwards [] with n
  apply Subtype.ext
  exact Measure.map_map hf.measurable (hp n)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_SequenceCellProfiles
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Good profiles in the original Haar cells

The good sets remain subsets of the original recurrence cells, and their
probability estimate is exactly a relative Haar-volume estimate.
-/

noncomputable section

namespace PolycyclicRecognition

open Set Filter MeasureTheory
open scoped Topology ENNReal

theorem cellProbabilityMeasure_apply_toReal
    {N : Type} [MeasurableSpace N] (μ : Measure N)
    (Q B : Set N) (hQ0 : μ Q ≠ 0) (hQfin : μ Q ≠ ∞) (hB : MeasurableSet B) :
    ((cellProbabilityMeasure μ Q hQ0 hQfin : Measure N) B).toReal =
      (μ (B ∩ Q)).toReal / (μ Q).toReal := by
  change (((μ Q)⁻¹ • μ.restrict Q) B).toReal = _
  rw [Measure.smul_apply, Measure.restrict_apply hB]
  simp only [smul_eq_mul, ENNReal.toReal_mul, ENNReal.toReal_inv, div_eq_inv_mul]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_CellProbabilityTransport
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Transporting normalized cell sampling through an injective chart -/

noncomputable section
namespace PolycyclicRecognition

open MeasureTheory Set
open scoped ENNReal

/-- Equal relative masses of chart images identify the normalized sampling
laws. This is used with the exact exponential-coordinate Jacobian. -/
theorem map_cellProbabilityMeasure_of_image_ratio
    {X Y : Type} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) (f : X → Y) (hf : Measurable f)
    (C : Set X) (hC0 : μ C ≠ 0) (hCfin : μ C ≠ ∞)
    (himage0 : ν (f '' C) ≠ 0) (himagefin : ν (f '' C) ≠ ∞)
    (hratio : ∀ A : Set X, (ν (f '' A)).toReal / (ν (f '' C)).toReal =
      (μ A).toReal / (μ C).toReal) :
    ProbabilityMeasure.map (cellProbabilityMeasure μ C hC0 hCfin) (f := f) (by first | exact hf.aemeasurable | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability) =
      cellProbabilityMeasure ν (f '' C) himage0 himagefin := by
  apply ProbabilityMeasure.toMeasure_injective
  apply Measure.ext
  intro B hB
  apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp
  change (Measure.map f (cellProbabilityMeasure μ C hC0 hCfin : Measure X) B).toReal = _
  rw [Measure.map_apply hf hB]
  rw [cellProbabilityMeasure_apply_toReal μ C (f ⁻¹' B) hC0 hCfin (hf hB),
    cellProbabilityMeasure_apply_toReal ν (f '' C) B himage0 himagefin hB]
  have himage : f '' (f ⁻¹' B ∩ C) = B ∩ f '' C := by
    ext y
    constructor
    · rintro ⟨x, ⟨hx, hxc⟩, rfl⟩
      exact ⟨hx, x, hxc, rfl⟩
    · rintro ⟨hy, x, hx, rfl⟩
      exact ⟨x, ⟨hy, hx⟩, rfl⟩
  rw [← himage]
  exact (hratio (f ⁻¹' B ∩ C)).symm

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_ExponentialGoodCells
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Relative mass is unchanged by the actual translated exponential chart -/

noncomputable section
namespace PolycyclicRecognition

open Module MeasureTheory Set
open scoped Manifold ENNReal

variable {L E G I : Type} [LieRing L] [LieAlgebra ℝ L]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace G] [ChartedSpace E G] [Group G]
  [LieGroup (𝓘(ℝ, E)) ⊤ G] [T2Space G] [SimplyConnectedSpace G]
  [MeasurableSpace G] [BorelSpace G]

/-- Both the good set and the original cell acquire exactly the same
Jacobian, including the deterministic right suffix. No density estimate is
lost when the independently sampled coordinate good set is put in the group. -/
theorem translated_exponential_cell_ratio
    (haar : NilpotentExponentialHaarInput E G)
    (e : L ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, E)) G) (hnil : LieRing.IsNilpotent L)
    (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G) (hExp : IsGroupExponential Exp)
    (chart : GroupLieAlgebra (𝓘(ℝ, E)) G ≃ₜ G) (hchart : ∀ x, chart x = Exp x)
    (X : I → L) (words : Finset (FreeMagma I))
    (b₀ : Basis (Fin (finrank ℝ L)) ℝ L) (β : WordBasisSelections X words)
    (cost : words → ℝ) (r : ℝ) (k : G)
    (A Q : Set (Fin (finrank ℝ L) → ℝ)) :
    let μ := Measure.map ((Exp ∘ e) ∘ b₀.equivFun.symm) volume
    let f := fun y => ((Exp ∘ e) ∘ (exponentialRescaleBasis
      (WordBasisSelections.basis X words β) (fun j => cost (β.val j)) r).equivFun.symm) y * k
    (μ (f '' A)).toReal / (μ (f '' Q)).toReal = (volume A).toReal / (volume Q).toReal := by
  let : IsTopologicalGroup G := topologicalGroup_of_lieGroup (𝓘(ℝ, E)) ⊤
  let μ := Measure.map ((Exp ∘ e) ∘ b₀.equivFun.symm) volume
  let : μ.IsMulRightInvariant := exponential_basis_measure_isRightInvariant haar e hnil Exp hExp b₀
  let g := (Exp ∘ e) ∘ (exponentialRescaleBasis
    (WordBasisSelections.basis X words β) (fun j => cost (β.val j)) r).equivFun.symm
  have himage (S : Set (Fin (finrank ℝ L) → ℝ)) :
      (fun y => g y * k) '' S = (fun y : G => y * k) '' (g '' S) :=
    image_comp (fun y : G => y * k) g S
  have hm (S : Set (Fin (finrank ℝ L) → ℝ)) :
      (μ ((fun y => g y * k) '' S)).toReal =
        (|(columnBasisMatrix (wordListCoordinates X words b₀) β.val).det| *
          Real.exp (r * columnBasisWeight cost β.val)) * (volume S).toReal := by
    rw [himage, measure_image_mul_right μ]
    dsimp only [μ, g]
    rw [exponential_rescaled_subset_measure e Exp chart hchart X words b₀ β cost r S]
    rw [ENNReal.toReal_mul, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (abs_nonneg _), ENNReal.toReal_ofReal (Real.exp_pos _).le]
  dsimp only
  change (μ ((fun y => g y * k) '' A)).toReal /
    (μ ((fun y => g y * k) '' Q)).toReal = _
  rw [hm, hm, mul_div_mul_left]
  exact mul_ne_zero (abs_ne_zero.mpr (wordBasis_det_ne_zero X words b₀ β)) (Real.exp_ne_zero _)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanCellTransport
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instDecidableEqConeMixedWords _root_.OAI.PolycyclicRecognition.CartanWordModel.instFintypeConeMixedWords _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Coordinate-cube sampling is the actual translated Cartan-cell law -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra MeasureTheory Set
open scoped Manifold ENNReal

variable {EG G W : Type} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {ExpG : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H ExpG)
  (hunimod : ∀ x : GroupLieAlgebra (𝓘(ℝ, EG)) G, LinearMap.trace ℝ _ (ad ℝ _ x) = 0)
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)

set_option maxHeartbeats 1000000 in
omit [SimplyConnectedSpace G] in
theorem map_cube_eq_translated_groupBox_probability
    (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
    (chartN : GroupLieAlgebra (𝓘(ℝ, F.N.modelSpace)) F.N.carrier ≃ₜ F.N.carrier)
    (hchartN : ∀ x, chartN x = F.ExpN x)
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (E : Set W) (β : M.Bases) (r : ℝ) (k : F.N.carrier) :
    let cube := Icc (fun _ : Fin (finrank ℝ (cartanRootIdeal H)) => (-1 : ℝ)) (fun _ => (1 : ℝ))
    let sample := fun y => ((F.ExpN ∘ F.N.equiv) ∘
      (M.boxBasis T hunimod eW E β r).equivFun.symm) y * k
    ProbabilityMeasure.map (cellProbabilityMeasure volume cube
      (coordinate_cube_mass zero_lt_one).1 (coordinate_cube_mass zero_lt_one).2) (f := sample) (measurableEmbedding_translated_exponential_basis F.N.equiv F.ExpN chartN hchartN (M.boxBasis T hunimod eW E β r) k).measurable.aemeasurable =
      M.translatedGroupBoxProbability T F hunimod eW haarN chartN hchartN b₀ E β r k := by
  dsimp only
  let b := M.boxBasis T hunimod eW E β r
  let sample := fun y => ((F.ExpN ∘ F.N.equiv) ∘ b.equivFun.symm) y * k
  let cube := Icc (fun _ : Fin (finrank ℝ (cartanRootIdeal H)) => (-1 : ℝ)) (fun _ => (1 : ℝ))
  let μ := Measure.map ((F.ExpN ∘ F.N.equiv) ∘ b₀.equivFun.symm) volume
  have heq : (fun y => y * k) '' M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) E β r 1 =
      sample '' cube := by
    rw [groupBox, exponentialCoordinateBox_eq_cube_image _ _ 1 zero_le_one, ← image_comp]
    rfl
  change ProbabilityMeasure.map (cellProbabilityMeasure volume cube _ _) (f := sample) (measurableEmbedding_translated_exponential_basis F.N.equiv F.ExpN chartN hchartN b k).measurable.aemeasurable =
    cellProbabilityMeasure μ ((fun y => y * k) ''
      M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) E β r 1) _ _
  have hprops := M.translated_groupBox_cell_properties T F hunimod eW haarN chartN hchartN
    b₀ E β r k
  have hzero : μ (sample '' cube) ≠ 0 := by simpa only [heq] using hprops.2.1
  have hfinite : μ (sample '' cube) ≠ ∞ := by simpa only [heq] using hprops.2.2
  have hmap := map_cellProbabilityMeasure_of_image_ratio volume μ sample
    (measurableEmbedding_translated_exponential_basis F.N.equiv F.ExpN chartN hchartN b k).measurable
    cube (coordinate_cube_mass zero_lt_one).1 (coordinate_cube_mass zero_lt_one).2 hzero hfinite
    (fun A => translated_exponential_cell_ratio haarN F.N.equiv (cartanRootIdeal_nilpotent H T)
      F.ExpN F.isExpN chartN hchartN M.letter M.wordList b₀ β
      (M.boxCost T hunimod eW E) r k A cube)
  simpa only [heq] using hmap

set_option maxHeartbeats 1000000 in
omit [SimplyConnectedSpace G] in
/-- A raw sheet-profile law can equivalently be sampled in the standard
coordinate cube. This transfers the coordinate affinity theorem to the
original Haar cell without changing either probability law. -/
theorem cube_profile_law_eq_cell_profile_law
    (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
    (chartN : GroupLieAlgebra (𝓘(ℝ, F.N.modelSpace)) F.N.carrier ≃ₜ F.N.carrier)
    (hchartN : ∀ x, chartN x = F.ExpN x)
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (E : Set W) (β : M.Bases) (r : ℝ) (k : F.N.carrier)
    {X : Type} [MeasurableSpace X] (profile : F.N.carrier → X) (hp : Measurable profile) :
    let cube := Icc (fun _ : Fin (finrank ℝ (cartanRootIdeal H)) => (-1 : ℝ)) (fun _ => (1 : ℝ))
    let sample := fun y => ((F.ExpN ∘ F.N.equiv) ∘
      (M.boxBasis T hunimod eW E β r).equivFun.symm) y * k
    ProbabilityMeasure.map (cellProbabilityMeasure volume cube
      (coordinate_cube_mass zero_lt_one).1 (coordinate_cube_mass zero_lt_one).2)
      (f := (profile ∘ sample)) (hp.comp (measurableEmbedding_translated_exponential_basis F.N.equiv F.ExpN chartN hchartN (M.boxBasis T hunimod eW E β r) k).measurable).aemeasurable = ProbabilityMeasure.map
        (M.translatedGroupBoxProbability T F hunimod eW haarN chartN hchartN b₀ E β r k) (f := profile) hp.aemeasurable := by
  dsimp only
  rw [← M.map_cube_eq_translated_groupBox_probability T F hunimod eW haarN chartN hchartN b₀ E β r k]
  apply ProbabilityMeasure.toMeasure_injective
  exact (Measure.map_map hp
    (measurableEmbedding_translated_exponential_basis F.N.equiv F.ExpN chartN hchartN
      (M.boxBasis T hunimod eW E β r) k).measurable).symm

set_option maxHeartbeats 1000000 in
omit [SimplyConnectedSpace G] in
/-- Right translation of a sheet changes its deterministic suffix and
preserves the original coordinate-cube sampling law exactly. -/
theorem translated_groupBox_profile_law_mul_right
    [IsTopologicalGroup F.N.carrier]
    (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
    (chartN : GroupLieAlgebra (𝓘(ℝ, F.N.modelSpace)) F.N.carrier ≃ₜ F.N.carrier)
    (hchartN : ∀ x, chartN x = F.ExpN x)
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (E : Set W) (β : M.Bases) (r : ℝ) (k₀ k : F.N.carrier)
    {X : Type} [MeasurableSpace X] (profile : F.N.carrier → X) (hp : Measurable profile) :
    ProbabilityMeasure.map
      (M.translatedGroupBoxProbability T F hunimod eW haarN chartN hchartN b₀ E β r k₀)
      (f := (fun q => profile (q * k))) (hp.comp (continuous_id.mul continuous_const).measurable).aemeasurable = ProbabilityMeasure.map
      (M.translatedGroupBoxProbability T F hunimod eW haarN chartN hchartN b₀ E β r (k₀ * k))
      (f := profile) hp.aemeasurable := by
  have h₀ := M.cube_profile_law_eq_cell_profile_law T F hunimod eW haarN chartN hchartN b₀
    E β r k₀ (fun q => profile (q * k)) (hp.comp (continuous_id.mul continuous_const).measurable)
  have h₁ := M.cube_profile_law_eq_cell_profile_law T F hunimod eW haarN chartN hchartN b₀
    E β r (k₀ * k) profile hp
  dsimp only at h₀ h₁
  rw [← h₀, ← h₁]
  congr 1
  funext y
  simp only [Function.comp_apply, mul_assoc]

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanCellPairLaws
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instDecidableEqConeMixedWords _root_.OAI.PolycyclicRecognition.CartanWordModel.instFintypeConeMixedWords _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Marginals of the actual neighboring-sheet sampling law -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra MeasureTheory Set Filter
open scoped Manifold Topology

variable {EG G W : Type} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {ExpG : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H ExpG)
  (hunimod : ∀ x : GroupLieAlgebra (𝓘(ℝ, EG)) G, LinearMap.trace ℝ _ (ad ℝ _ x) = 0)
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)

set_option maxHeartbeats 1000000 in
/-- A joint neighboring-sheet limit has precisely the two marginal limits
obtained by sampling the translated cells with suffixes `k₀` and `k₀ * k`.
Thus the single-sheet affinity theorem applies to both components. -/
theorem neighboring_cell_marginal_limits
    [IsTopologicalGroup F.N.carrier]
    (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
    (chartN : GroupLieAlgebra (𝓘(ℝ, F.N.modelSpace)) F.N.carrier ≃ₜ F.N.carrier)
    (hchartN : ∀ x, chartN x = F.ExpN x)
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (E : Set W) (β : M.Bases) (scale : ℕ → ℝ) (k₀ k : ℕ → F.N.carrier)
    {S : Type} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S] [BorelSpace (S × S)]
    (profile : ℕ → F.N.carrier → S) (hp : ∀ n, Measurable (profile n))
    (ν : ProbabilityMeasure (S × S))
    (hν : Tendsto (fun n => ProbabilityMeasure.map
      (M.translatedGroupBoxProbability T F hunimod eW haarN chartN hchartN b₀ E β (scale n) (k₀ n))
      (f := (fun q => (profile n q, profile n (q * k n)))) (((hp n).prodMk ((hp n).comp (continuous_id.mul continuous_const).measurable)).aemeasurable)) atTop (𝓝 ν)) :
    Tendsto (fun n => ProbabilityMeasure.map
      (M.translatedGroupBoxProbability T F hunimod eW haarN chartN hchartN b₀ E β (scale n) (k₀ n))
      (f := (profile n)) (by first | exact (hp n).aemeasurable | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)) atTop (𝓝 (ProbabilityMeasure.map ν (f := Prod.fst) (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability))) ∧
    Tendsto (fun n => ProbabilityMeasure.map
      (M.translatedGroupBoxProbability T F hunimod eW haarN chartN hchartN b₀ E β (scale n) (k₀ n * k n))
      (f := (profile n)) (by first | exact (hp n).aemeasurable | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)) atTop (𝓝 (ProbabilityMeasure.map ν (f := Prod.snd) (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability))) := by
  let μ := fun n => M.translatedGroupBoxProbability T F hunimod eW haarN chartN hchartN b₀
    E β (scale n) (k₀ n)
  let pair := fun n q => (profile n q, profile n (q * k n))
  have hp' n : Measurable (pair n) :=
    (hp n).prodMk ((hp n).comp (continuous_id.mul continuous_const).measurable)
  have hfst := sampled_projection_tendsto μ pair hp' ν hν Prod.fst continuous_fst
  have hsnd := sampled_projection_tendsto μ pair hp' ν hν Prod.snd continuous_snd
  refine ⟨hfst, ?_⟩
  convert hsnd using 1
  all_goals try with_reducible_and_instances rfl
  funext n
  exact (M.translated_groupBox_profile_law_mul_right T F hunimod eW haarN chartN hchartN
    b₀ E β (scale n) (k₀ n) (k n) (profile n) (hp n)).symm

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanCellProfileAffinity
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instDecidableEqConeMixedWords _root_.OAI.PolycyclicRecognition.CartanWordModel.instFintypeConeMixedWords _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_nonempty _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.instFiniteRootOffsetConeIndex _root_.OAI.PolycyclicRecognition.instNonemptyRootOffsetConeIndex _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.unitaryCentralFixed_complete _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Affinity of the profiles sampled from their actual translated Haar cells -/

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
theorem cartan_supported_cell_profile_affine_sequence
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
    (chartN : GroupLieAlgebra (𝓘(ℝ, F.N.modelSpace)) F.N.carrier ≃ₜ F.N.carrier)
    (hchartN : ∀ v, chartN v = F.ExpN v)
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
    (profile : ℕ → F.N.carrier → S)
    (hp : ∀ n, Measurable (profile n))
    (hactual : ∀ n q, q ∈ (fun v => v * F.ExpN (F.N.equiv (k n))) ''
      M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) E β (scale n) 1 → ∀ z,
      (profile n q).val z =
        rescaledMapProfile (fun g => (π ((p n).val.1 g)).toAdd) (x n) (F.inclusionN q)
        (max (Real.log (scale n)) 0)
        (fun z => F.inclusionD (F.ExpD (F.D.equiv
          ((exponentialRescaleBasis (WordBasisSelections.basis X (boundedBracketWords d) βD)
            (fun j => bracketWordExponent (fun _ : I => 1) (βD.val j))
            (max (Real.log (scale n)) 0)).equivFun.symm z)))) z)
    (ν : ProbabilityMeasure S)
    (hν : Tendsto (fun n => ProbabilityMeasure.map
      (M.translatedGroupBoxProbability T F hunimod eW haarN chartN hchartN b₀ E β
        (scale n) (F.ExpN (F.N.equiv (k n)))) (f := (profile n)) (by first | exact (hp n).aemeasurable | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)) atTop (𝓝 ν))
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
  let sample := fun n y => ((F.ExpN ∘ F.N.equiv) ∘
    (M.boxBasis T hunimod eW E β (scale n)).equivFun.symm) y * F.ExpN (F.N.equiv (k n))
  let cp := fun n y => profile n (sample n y)
  have hcp n : Measurable (cp n) := (hp n).comp
    (measurableEmbedding_translated_exponential_basis F.N.equiv F.ExpN chartN hchartN
      (M.boxBasis T hunimod eW E β (scale n)) (F.ExpN (F.N.equiv (k n)))).measurable
  have hmem n y (hy : y ∈ Icc (fun _ : Fin (finrank ℝ (cartanRootIdeal H)) => (-1 : ℝ))
      (fun _ => (1 : ℝ))) : sample n y ∈
      (fun v => v * F.ExpN (F.N.equiv (k n))) ''
        M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) E β (scale n) 1 := by
    refine ⟨((F.ExpN ∘ F.N.equiv) ∘ (M.boxBasis T hunimod eW E β (scale n)).equivFun.symm) y,
      ?_, rfl⟩
    rw [groupBox, exponentialCoordinateBox_eq_cube_image _ _ 1 zero_le_one]
    exact ⟨y, hy, rfl⟩
  have hlim : Tendsto (fun n => ProbabilityMeasure.map
      (cellProbabilityMeasure volume (Icc (fun _ => (-1 : ℝ)) (fun _ => (1 : ℝ)))
        (coordinate_cube_mass zero_lt_one).1 (coordinate_cube_mass zero_lt_one).2)
      (f := (cp n)) (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)) atTop (𝓝 ν) := by
    convert hν using 1
    all_goals try with_reducible_and_instances rfl
    funext n
    exact M.cube_profile_law_eq_cell_profile_law T F hunimod eW haarN chartN hchartN
      b₀ E β (scale n) (F.ExpN (F.N.equiv (k n))) (profile n) (hp n)
  apply M.cartan_supported_profile_affine_sequence T F hunimod eW hExp realize haarN haarD
    dynkinN dynkinD m π hπExp hdec hvan hΛ hπ hpath b₀ hE hne β γ hβ hδ hc hhi ht hcost hgap
    X hDnil hDletters bD₀ βD hβD aN hmN aD hmD scale hscale hmono hscale1 ε hεpos hε
    k hk rem hdim p x S hS cp hcp ?_ ν hlim U hU hconn hUne hUheight σ hσ
  intro n y hy z
  simpa only [cp, sample, Function.comp_apply, map_mul] using hactual n (sample n y) (hmem n y hy) z

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanNeighborProfileAffinity
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instDecidableEqConeMixedWords _root_.OAI.PolycyclicRecognition.CartanWordModel.instFintypeConeMixedWords _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_countable _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_nonempty _root_.OAI.PolycyclicRecognition.finitelyGeneratedSubgroupIndex_countable _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.instFiniteRootOffsetConeIndex _root_.OAI.PolycyclicRecognition.instNonemptyRootOffsetConeIndex _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.unitaryCentralFixed_complete _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The two affine profiles of the neighboring-sheet joint law -/

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
/-- Every supported neighboring pair is affine on the contracted profile
domain, using the exact two marginal cell laws. The labels are not assumed
to agree here; their equality is the shrinking-diagonal theorem. -/
theorem cartan_supported_neighbor_profiles_affine_sequence
    [IsTopologicalGroup F.N.carrier]
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
    (chartN : GroupLieAlgebra (𝓘(ℝ, F.N.modelSpace)) F.N.carrier ≃ₜ F.N.carrier)
    (hchartN : ∀ v, chartN v = F.ExpN v)
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
    (step : ℕ → F.N.carrier) (k' : ℕ → cartanRootIdeal H)
    (hk' : ∀ᶠ r : ℕ in atTop,
      ‖(exponentialRescaleBasis (WordBasisSelections.basis M.letter M.wordList β)
        (fun i => (1 + δ) * M.boxCost T hunimod eW E (β.val i)) (scale r)).equivFun (k' r)‖ ≤
          Real.exp (scale r * ε r))
    (hprod : ∀ n, F.ExpN (F.N.equiv (k' n)) = F.ExpN (F.N.equiv (k n)) * step n)
    (rem : RemezPolynomialInput) (hdim : 1 ≤ finrank ℝ (cartanRootIdeal H))
    (p : ℕ → NormalizedPair G Λ) (x : ℕ → G)
    (S : Set C((Fin (finrank ℝ H) → ℝ), W))
    (hS : IsCompact S)
    [MeasurableSpace S] [BorelSpace S] [BorelSpace (S × S)] [HasOuterApproxClosed S]
    (profile : ℕ → F.N.carrier → S)
    (hp : ∀ n, Measurable (profile n))
    (hactual : ∀ n q, q ∈ (fun v => v * F.ExpN (F.N.equiv (k n))) ''
      M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) E β (scale n) 1 ∪
      (fun v => v * F.ExpN (F.N.equiv (k' n))) ''
        M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) E β (scale n) 1 → ∀ z,
      (profile n q).val z =
        rescaledMapProfile (fun g => (π ((p n).val.1 g)).toAdd) (x n) (F.inclusionN q)
        (max (Real.log (scale n)) 0)
        (fun z => F.inclusionD (F.ExpD (F.D.equiv
          ((exponentialRescaleBasis (WordBasisSelections.basis X (boundedBracketWords d) βD)
            (fun j => bracketWordExponent (fun _ : I => 1) (βD.val j))
            (max (Real.log (scale n)) 0)).equivFun.symm z)))) z)
    (ν : ProbabilityMeasure (S × S))
    (hν : Tendsto (fun n => ProbabilityMeasure.map
      (M.translatedGroupBoxProbability T F hunimod eW haarN chartN hchartN b₀ E β
        (scale n) (F.ExpN (F.N.equiv (k n)))) (f := (fun q => (profile n q, profile n (q * step n)))) (((hp n).prodMk ((hp n).comp (continuous_id.mul continuous_const).measurable)).aemeasurable)) atTop (𝓝 ν))
    (U : Set (Fin (finrank ℝ H) → ℝ)) (hU : IsOpen U)
    (hconn : IsPreconnected U) (hUne : U.Nonempty)
    (hUheight : ∀ z ∈ U, eW (heightProjection T.character
      ((WordBasisSelections.basis X (boundedBracketWords d) βD).equivFun.symm z :
        GroupLieAlgebra (𝓘(ℝ, EG)) G)) ∈ (fun w => (1 - c * δ) • w) '' E)
    (σ : Fin M.letterCount → Bool)
    (hσ : (weightChamber (fun i =>
      ((M.supportIn T hunimod eW).weight i).toContinuousLinearMap) σ).Nonempty) :
    ∀ (f : S × S), f ∈ (ν : Measure (S × S)).support →
      ∃ (A₁ A₂ : templateSymmetryGroup (M.supportIn T hunimod eW)) (b₁ b₂ : W),
        ∀ z ∈ U,
          f.1.val z = A₁.val (eW (heightProjection T.character
            ((WordBasisSelections.basis X (boundedBracketWords d) βD).equivFun.symm z :
              GroupLieAlgebra (𝓘(ℝ, EG)) G))) + b₁ ∧
          f.2.val z = A₂.val (eW (heightProjection T.character
            ((WordBasisSelections.basis X (boundedBracketWords d) βD).equivFun.symm z :
              GroupLieAlgebra (𝓘(ℝ, EG)) G))) + b₂ := by
  obtain ⟨h₁, h₂⟩ := M.neighboring_cell_marginal_limits T F hunimod eW haarN chartN hchartN
    b₀ E β scale (fun n => F.ExpN (F.N.equiv (k n))) step profile hp ν hν
  have h₂' : Tendsto (fun n => ProbabilityMeasure.map
      (M.translatedGroupBoxProbability T F hunimod eW haarN chartN hchartN b₀ E β
        (scale n) (F.ExpN (F.N.equiv (k' n)))) (f := (profile n)) (by first | exact (hp n).aemeasurable | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)) atTop
      (𝓝 (ProbabilityMeasure.map ν (f := Prod.snd) (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability))) := by
    simpa only [← hprod] using h₂
  intro f hf
  obtain ⟨A₁, b₁, ha₁⟩ := M.cartan_supported_cell_profile_affine_sequence T F hunimod eW
    hExp realize haarN haarD dynkinN dynkinD m π hπExp hdec hvan hΛ hπ hpath
    chartN hchartN b₀ hE hne β γ hβ hδ hc hhi ht hcost hgap
    X hDnil hDletters bD₀ βD hβD aN hmN aD hmD scale hscale hmono hscale1 ε hεpos hε k hk
    rem hdim p x S hS profile hp (fun n q hq => hactual n q (Or.inl hq))
    (ProbabilityMeasure.map ν (f := Prod.fst) (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)) h₁ U hU hconn hUne hUheight σ hσ f.1
    (mem_support_map_of_continuous ν Prod.fst continuous_fst hf)
  obtain ⟨A₂, b₂, ha₂⟩ := M.cartan_supported_cell_profile_affine_sequence T F hunimod eW
    hExp realize haarN haarD dynkinN dynkinD m π hπExp hdec hvan hΛ hπ hpath
    chartN hchartN b₀ hE hne β γ hβ hδ hc hhi ht hcost hgap
    X hDnil hDletters bD₀ βD hβD aN hmN aD hmD scale hscale hmono hscale1 ε hεpos hε k' hk'
    rem hdim p x S hS profile hp (fun n q hq => hactual n q (Or.inr hq))
    (ProbabilityMeasure.map ν (f := Prod.snd) (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)) h₂' U hU hconn hUne hUheight σ hσ f.2
    (mem_support_map_of_continuous ν Prod.snd continuous_snd hf)
  exact ⟨A₁, A₂, b₁, b₂, fun z hz => ⟨ha₁ z hz, ha₂ z hz⟩⟩

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanNeighborSuffixRate
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instDecidableEqConeMixedWords _root_.OAI.PolycyclicRecognition.CartanWordModel.instFintypeConeMixedWords _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.CartanFactorModel.heightRay_zero _root_.OAI.PolycyclicRecognition.CartanFactorModel.realScaleProfile_apply _root_.OAI.PolycyclicRecognition.CartanFactorModel.sampledProbeProfile_apply _root_.OAI.PolycyclicRecognition.bracketWordDifferential_mul _root_.OAI.PolycyclicRecognition.cartanWeightDerivation_apply_root _root_.OAI.PolycyclicRecognition.cartanWeightDilation_apply _root_.OAI.PolycyclicRecognition.cartanWeightScale_add_apply _root_.OAI.PolycyclicRecognition.cartanWeightScale_zero_apply _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.integrateNilpotentLieEquiv_apply_exp _root_.OAI.PolycyclicRecognition.modelNilradicalLinearAction_apply _root_.OAI.PolycyclicRecognition.modelNilradicalRotation_apply _root_.OAI.PolycyclicRecognition.modelNilradicalRotation_mul _root_.OAI.PolycyclicRecognition.modelNilradicalRotation_one _root_.OAI.PolycyclicRecognition.nilshadowWeightDerivation_symm _root_.OAI.PolycyclicRecognition.nilshadowWeightOperator_symm _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # One logarithmic coordinate rate for both neighboring suffixes -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule Set Filter
open scoped Manifold Topology

variable {EG G W : Type} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H Exp)
  (hunimod : ∀ x : GroupLieAlgebra (𝓘(ℝ, EG)) G, LinearMap.trace ℝ _ (ad ℝ _ x) = 0)
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)

set_option maxHeartbeats 1000000 in
/-- The actual box product estimate supplies logarithms of the suffix and
its product with the neighboring step, with a single vanishing coordinate
rate. No separate product-suffix error estimate is assumed. -/
theorem exists_neighbor_suffix_coordinate_rate
    (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (E : Set W) (β : M.Bases)
    (hβ : IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
      (M.boxCost T hunimod eW E) β.val)
    (scale R : ℕ → ℝ) (hs : Tendsto scale atTop atTop) (hspos : ∀ n, 0 < scale n)
    (hR0 : ∀ n, 0 ≤ R n) (hR : HasSubexponentialUpperBoundSeq scale R)
    (k₀ k : ℕ → F.N.carrier)
    (hk₀ : ∀ n, k₀ n ∈ M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) E β (scale n) (R n))
    (hk : ∀ n, k n ∈ M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) E β (scale n) (R n)) :
    ∃ (v₀ v₁ : ℕ → cartanRootIdeal H) (ε : ℕ → ℝ),
      (∀ n, F.ExpN (F.N.equiv (v₀ n)) = k₀ n) ∧
      (∀ n, F.ExpN (F.N.equiv (v₁ n)) = k₀ n * k n) ∧
      (∀ n, 0 ≤ ε n) ∧ Tendsto ε atTop (𝓝 0) ∧
      ∀ n, ‖(M.boxBasis T hunimod eW E β (scale n)).equivFun (v₀ n)‖ ≤
          Real.exp (scale n * ε n) ∧
        ‖(M.boxBasis T hunimod eW E β (scale n)).equivFun (v₁ n)‖ ≤
          Real.exp (scale n * ε n) := by
  obtain ⟨C, hC, hproduct⟩ := M.exists_groupBox_product_bound T hunimod eW
    F.N.equiv F.ExpN F.isExpN dynkinN b₀
  let P := fun n => C * (1 + (2 : ℝ)) ^ M.bound * (1 + R n) ^ M.bound
  have hP0 n : 0 ≤ P n := by
    have := hR0 n
    dsimp only [P]
    positivity
  have hP : HasSubexponentialUpperBoundSeq scale P := by
    apply (sequence_subexponential_upper_const hs (C * (1 + (2 : ℝ)) ^ M.bound)).mul
      (((sequence_subexponential_upper_const hs 1).add hR hs).pow hs
        (Eventually.of_forall (fun n => by linarith [hR0 n])) M.bound)
    exact Eventually.of_forall (fun _ => mul_nonneg hC (by positivity))
  have hk₁ n : k₀ n * k n ∈
      M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) E β (scale n) (P n) := by
    have hg : ∀ i : Fin 2, ![k₀ n, k n] i ∈
        M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) E β (scale n) (R n) := by
      intro i
      fin_cases i
      · exact hk₀ n
      · exact hk n
    simpa [P, List.ofFn_succ] using
      hproduct E β hβ (scale n) (hspos n).le 2 (R n) (hR0 n) ![k₀ n, k n] hg
  choose v₀ hv₀ hb₀ using hk₀
  choose v₁ hv₁ hb₁ using hk₁
  obtain ⟨ε, hε0, hε, hb⟩ := exists_sequence_subexponential_rate scale
    (fun n => R n + P n) hspos (hR.add hP hs)
  refine ⟨v₀, v₁, ε, hv₀, hv₁, hε0, hε, ?_⟩
  intro n
  exact ⟨(hb₀ n).trans ((le_add_of_nonneg_right (hP0 n)).trans (hb n)),
    (hb₁ n).trans ((le_add_of_nonneg_left (hR0 n)).trans (hb n))⟩

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanNeighborBoxAffinity
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instDecidableEqConeMixedWords _root_.OAI.PolycyclicRecognition.CartanWordModel.instFintypeConeMixedWords _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_countable _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_nonempty _root_.OAI.PolycyclicRecognition.finitelyGeneratedSubgroupIndex_countable _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.instFiniteRootOffsetConeIndex _root_.OAI.PolycyclicRecognition.instNonemptyRootOffsetConeIndex _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.unitaryCentralFixed_complete _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Neighboring-sheet affinity directly from enlarged box membership -/

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
/-- Affinity on both neighboring sheets follows from the original enlarged
box bounds. Logarithmic suffixes and their common vanishing error envelope
are constructed by the box product estimate. -/
theorem cartan_neighbor_profiles_affine_of_boxes
    [IsTopologicalGroup F.N.carrier]
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
    (chartN : GroupLieAlgebra (𝓘(ℝ, F.N.modelSpace)) F.N.carrier ≃ₜ F.N.carrier)
    (hchartN : ∀ v, chartN v = F.ExpN v)
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
    (R : ℕ → ℝ) (hR0 : ∀ n, 0 ≤ R n)
    (hR : HasSubexponentialUpperBoundSeq scale R)
    (k₀ step : ℕ → F.N.carrier)
    (hk₀ : ∀ n, k₀ n ∈ M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv)
      ((fun w => (1 + δ) • w) '' E) β (scale n) (R n))
    (hstep : ∀ n, step n ∈ M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv)
      ((fun w => (1 + δ) • w) '' E) β (scale n) (R n))
    (rem : RemezPolynomialInput) (hdim : 1 ≤ finrank ℝ (cartanRootIdeal H))
    (p : ℕ → NormalizedPair G Λ) (x : ℕ → G)
    (S : Set C((Fin (finrank ℝ H) → ℝ), W))
    (hS : IsCompact S)
    [MeasurableSpace S] [BorelSpace S] [BorelSpace (S × S)] [HasOuterApproxClosed S]
    (profile : ℕ → F.N.carrier → S)
    (hp : ∀ n, Measurable (profile n))
    (hactual : ∀ n q, q ∈ (fun v => v * k₀ n) ''
      M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) E β (scale n) 1 ∪
      (fun v => v * k₀ n * step n) ''
        M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) E β (scale n) 1 → ∀ z,
      (profile n q).val z =
        rescaledMapProfile (fun g => (π ((p n).val.1 g)).toAdd) (x n) (F.inclusionN q)
        (max (Real.log (scale n)) 0)
        (fun z => F.inclusionD (F.ExpD (F.D.equiv
          ((exponentialRescaleBasis (WordBasisSelections.basis X (boundedBracketWords d) βD)
            (fun j => bracketWordExponent (fun _ : I => 1) (βD.val j))
            (max (Real.log (scale n)) 0)).equivFun.symm z)))) z)
    (ν : ProbabilityMeasure (S × S))
    (hν : Tendsto (fun n => ProbabilityMeasure.map
      (M.translatedGroupBoxProbability T F hunimod eW haarN chartN hchartN b₀ E β
        (scale n) (k₀ n)) (f := (fun q => (profile n q, profile n (q * step n)))) (((hp n).prodMk ((hp n).comp (continuous_id.mul continuous_const).measurable)).aemeasurable)) atTop (𝓝 ν))
    (U : Set (Fin (finrank ℝ H) → ℝ)) (hU : IsOpen U)
    (hconn : IsPreconnected U) (hUne : U.Nonempty)
    (hUheight : ∀ z ∈ U, eW (heightProjection T.character
      ((WordBasisSelections.basis X (boundedBracketWords d) βD).equivFun.symm z :
        GroupLieAlgebra (𝓘(ℝ, EG)) G)) ∈ (fun w => (1 - c * δ) • w) '' E)
    (σ : Fin M.letterCount → Bool)
    (hσ : (weightChamber (fun i =>
      ((M.supportIn T hunimod eW).weight i).toContinuousLinearMap) σ).Nonempty) :
    ∀ (f : S × S), f ∈ (ν : Measure (S × S)).support →
      ∃ (A₁ A₂ : templateSymmetryGroup (M.supportIn T hunimod eW)) (b₁ b₂ : W),
        ∀ z ∈ U,
          f.1.val z = A₁.val (eW (heightProjection T.character
            ((WordBasisSelections.basis X (boundedBracketWords d) βD).equivFun.symm z :
              GroupLieAlgebra (𝓘(ℝ, EG)) G))) + b₁ ∧
          f.2.val z = A₂.val (eW (heightProjection T.character
            ((WordBasisSelections.basis X (boundedBracketWords d) βD).equivFun.symm z :
              GroupLieAlgebra (𝓘(ℝ, EG)) G))) + b₂ := by
  let E' := (fun w => (1 + δ) • w) '' E
  have hcE (w : M.wordList) : M.boxCost T hunimod eW E' w =
      (1 + δ) * M.boxCost T hunimod eW E w :=
    M.boxCost_image_smul T hunimod eW hE hne (by linarith) w
  have hβ' : IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
      (M.boxCost T hunimod eW E') β.val := by
    refine ⟨hβ.1, ?_⟩
    intro β' hβ'
    simp only [columnBasisWeight, hcE, ← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (hβ.2 β' hβ') (by linarith)
  obtain ⟨v₀, v₁, ε, hv₀, hv₁, hε0, hε, hb⟩ :=
    M.exists_neighbor_suffix_coordinate_rate T F hunimod eW dynkinN b₀ E' β hβ'
      scale R hscale (fun n => zero_lt_one.trans_le (hscale1 n)) hR0 hR k₀ step hk₀ hstep
  have hb₀ : ∀ n,
      ‖(exponentialRescaleBasis (WordBasisSelections.basis M.letter M.wordList β)
        (fun i => (1 + δ) * M.boxCost T hunimod eW E (β.val i)) (scale n)).equivFun (v₀ n)‖ ≤
      Real.exp (scale n * ε n) := by
    intro n
    simpa only [boxBasis, hcE] using (hb n).1
  have hb₁ : ∀ n,
      ‖(exponentialRescaleBasis (WordBasisSelections.basis M.letter M.wordList β)
        (fun i => (1 + δ) * M.boxCost T hunimod eW E (β.val i)) (scale n)).equivFun (v₁ n)‖ ≤
      Real.exp (scale n * ε n) := by
    intro n
    simpa only [boxBasis, hcE] using (hb n).2
  apply M.cartan_supported_neighbor_profiles_affine_sequence T F hunimod eW hExp realize
    haarN haarD dynkinN dynkinD m π hπExp hdec hvan hΛ hπ hpath chartN hchartN
    b₀ hE hne β γ hβ hδ hc hhi ht hcost hgap X hDnil hDletters bD₀ βD hβD aN hmN aD hmD
    scale hscale hmono hscale1 ε hε0 hε v₀ (Eventually.of_forall hb₀) step v₁
    (Eventually.of_forall hb₁) (fun n => (hv₁ n).trans (by rw [hv₀]))
    rem hdim p x S hS profile hp ?_ ν ?_ U hU hconn hUne hUheight σ hσ
  · intro n q hq
    apply hactual n q
    simpa only [hv₀, hv₁, mul_assoc] using hq
  · simpa only [hv₀] using hν

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanFullCellAffinity
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instDecidableEqConeMixedWords _root_.OAI.PolycyclicRecognition.CartanWordModel.instFintypeConeMixedWords _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_countable _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_nonempty _root_.OAI.PolycyclicRecognition.finitelyGeneratedSubgroupIndex_countable _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.instFiniteRootOffsetConeIndex _root_.OAI.PolycyclicRecognition.instNonemptyRootOffsetConeIndex _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.unitaryCentralFixed_complete _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Neighboring-sheet affinity directly from enlarged box membership -/

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
/-- Both supported profiles are affine on the full inverse image of the
open contracted cell. Openness, convexity, and nonemptiness of that domain
are proved here from the surjective Cartan height map. -/
theorem cartan_neighbor_profiles_affine_on_contracted_cell
    [IsTopologicalGroup F.N.carrier]
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
    (chartN : GroupLieAlgebra (𝓘(ℝ, F.N.modelSpace)) F.N.carrier ≃ₜ F.N.carrier)
    (hchartN : ∀ v, chartN v = F.ExpN v)
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    {E : Set W} (hE : IsCompact E) (hconv : Convex ℝ E) (hint : (interior E).Nonempty) (β γ : M.Bases)
    (hβ : IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
      (M.boxCost T hunimod eW E) β.val)
    {δ c lo hi : ℝ} (hδ : 0 < δ) (hc : 0 ≤ c) (hhi : 0 ≤ hi) (ht : 0 < 1 - c * δ)
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
    (R : ℕ → ℝ) (hR0 : ∀ n, 0 ≤ R n)
    (hR : HasSubexponentialUpperBoundSeq scale R)
    (k₀ step : ℕ → F.N.carrier)
    (hk₀ : ∀ n, k₀ n ∈ M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv)
      ((fun w => (1 + δ) • w) '' E) β (scale n) (R n))
    (hstep : ∀ n, step n ∈ M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv)
      ((fun w => (1 + δ) • w) '' E) β (scale n) (R n))
    (rem : RemezPolynomialInput) (hdim : 1 ≤ finrank ℝ (cartanRootIdeal H))
    (p : ℕ → NormalizedPair G Λ) (x : ℕ → G)
    (S : Set C((Fin (finrank ℝ H) → ℝ), W))
    (hS : IsCompact S)
    [MeasurableSpace S] [BorelSpace S] [BorelSpace (S × S)] [HasOuterApproxClosed S]
    (profile : ℕ → F.N.carrier → S)
    (hp : ∀ n, Measurable (profile n))
    (hactual : ∀ n q, q ∈ (fun v => v * k₀ n) ''
      M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) E β (scale n) 1 ∪
      (fun v => v * k₀ n * step n) ''
        M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) E β (scale n) 1 → ∀ z,
      (profile n q).val z =
        rescaledMapProfile (fun g => (π ((p n).val.1 g)).toAdd) (x n) (F.inclusionN q)
        (max (Real.log (scale n)) 0)
        (fun z => F.inclusionD (F.ExpD (F.D.equiv
          ((exponentialRescaleBasis (WordBasisSelections.basis X (boundedBracketWords d) βD)
            (fun j => bracketWordExponent (fun _ : I => 1) (βD.val j))
            (max (Real.log (scale n)) 0)).equivFun.symm z)))) z)
    (ν : ProbabilityMeasure (S × S))
    (hν : Tendsto (fun n => ProbabilityMeasure.map
      (M.translatedGroupBoxProbability T F hunimod eW haarN chartN hchartN b₀ E β
        (scale n) (k₀ n)) (f := (fun q => (profile n q, profile n (q * step n)))) (((hp n).prodMk ((hp n).comp (continuous_id.mul continuous_const).measurable)).aemeasurable)) atTop (𝓝 ν))
    (σ : Fin M.letterCount → Bool)
    (hσ : (weightChamber (fun i =>
      ((M.supportIn T hunimod eW).weight i).toContinuousLinearMap) σ).Nonempty) :
    ∀ (f : S × S), f ∈ (ν : Measure (S × S)).support →
      ∃ (A₁ A₂ : templateSymmetryGroup (M.supportIn T hunimod eW)) (b₁ b₂ : W),
        ∀ z, eW (heightProjection T.character
          ((WordBasisSelections.basis X (boundedBracketWords d) βD).equivFun.symm z :
            GroupLieAlgebra (𝓘(ℝ, EG)) G)) ∈ (fun w => (1 - c * δ) • w) '' interior E →
          f.1.val z = A₁.val (eW (heightProjection T.character
            ((WordBasisSelections.basis X (boundedBracketWords d) βD).equivFun.symm z :
              GroupLieAlgebra (𝓘(ℝ, EG)) G))) + b₁ ∧
          f.2.val z = A₂.val (eW (heightProjection T.character
            ((WordBasisSelections.basis X (boundedBracketWords d) βD).equivFun.symm z :
              GroupLieAlgebra (𝓘(ℝ, EG)) G))) + b₂ := by
  let b := WordBasisSelections.basis X (boundedBracketWords d) βD
  let height : H →ₗ[ℝ] W := eW.toLinearMap.comp
    ((heightProjection T.character).comp H.incl.toLinearMap)
  let q := height.comp b.equivFun.symm.toLinearMap
  let U := q ⁻¹' ((fun w => (1 - c * δ) • w) '' interior E)
  have hq : Function.Surjective q := by
    intro w
    refine ⟨b.equivFun (cartanHeightSection T H (eW.symm w)), ?_⟩
    change eW (heightProjection T.character
      (b.equivFun.symm (b.equivFun (cartanHeightSection T H (eW.symm w))) :
        GroupLieAlgebra (𝓘(ℝ, EG)) G)) = w
    rw [LinearEquiv.symm_apply_apply, cartanHeightSection_height, eW.apply_symm_apply]
  have hU : IsOpen U := (isOpenMap_smul₀ ht.ne' _ isOpen_interior).preimage
    q.toContinuousLinearMap.continuous
  have hUconv : Convex ℝ U := (hconv.interior.smul (1 - c * δ)).linear_preimage q
  have hUne : U.Nonempty := by
    obtain ⟨w, hw⟩ := hint
    obtain ⟨z, hz⟩ := hq ((1 - c * δ) • w)
    exact ⟨z, w, hw, hz.symm⟩
  have haff := M.cartan_neighbor_profiles_affine_of_boxes T F hunimod eW
    hExp realize haarN haarD dynkinN dynkinD m π hπExp hdec hvan hΛ hπ hpath
    chartN hchartN b₀ hE (hint.mono interior_subset) β γ hβ hδ hc hhi ht.le hcost hgap
    X hDnil hDletters bD₀ βD hβD aN hmN aD hmD scale hscale hmono hscale1 R hR0 hR
    k₀ step hk₀ hstep rem hdim p x S hS profile hp hactual ν hν U hU
    hUconv.isPreconnected hUne
    (fun z hz => by
      obtain ⟨w, hw, he⟩ := hz
      exact ⟨w, interior_subset hw, he⟩) σ hσ
  exact haff

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanCommonCellAffinity
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_countable _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_nonempty _root_.OAI.PolycyclicRecognition.finitelyGeneratedSubgroupIndex_countable _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.instFiniteRootOffsetConeIndex _root_.OAI.PolycyclicRecognition.instNonemptyRootOffsetConeIndex _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.unitaryCentralFixed_complete _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Neighboring-sheet affinity directly from enlarged box membership -/

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
/-- Apply the proved uniform neighbor-label threshold to actual supported
profiles. The row is assembled from the original enlarged cells and the
published-input affinity theorem, including the raw-chart identities. -/
theorem cartan_neighbor_profiles_common_affine_of_threshold
    [IsTopologicalGroup F.N.carrier]
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
    (chartN : GroupLieAlgebra (𝓘(ℝ, F.N.modelSpace)) F.N.carrier ≃ₜ F.N.carrier)
    (hchartN : ∀ v, chartN v = F.ExpN v)
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    {E : Set W} (hE : IsCompact E) (hconv : Convex ℝ E) (hint : (interior E).Nonempty) (β γ : M.Bases)
    (hβ : IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
      (M.boxCost T hunimod eW E) β.val)
    {δ c lo hi : ℝ} (hδ : 0 < δ) (hc : 0 ≤ c) (hhi : 0 ≤ hi) (ht : 0 < 1 - c * δ)
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
    (R : ℕ → ℝ) (hR0 : ∀ n, 0 ≤ R n)
    (hR : HasSubexponentialUpperBoundSeq scale R)
    (k₀ step : ℕ → F.N.carrier)
    (hk₀ : ∀ n, k₀ n ∈ M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv)
      ((fun w => (1 + δ) • w) '' E) β (scale n) (R n))
    (hstep : ∀ n, step n ∈ M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv)
      ((fun w => (1 + δ) • w) '' E) β (scale n) (R n))
    (rem : RemezPolynomialInput) (hdim : 1 ≤ finrank ℝ (cartanRootIdeal H))
    (p : ℕ → NormalizedPair G Λ) (x : ℕ → G)
    (S : Set C((Fin (finrank ℝ H) → ℝ), W))
    (hS : IsCompact S)
    [MeasurableSpace S] [BorelSpace S] [BorelSpace (S × S)] [HasOuterApproxClosed S]
    (profile : ℕ → F.N.carrier → S)
    (hp : ∀ n, Measurable (profile n))
    (hactual : ∀ n q, q ∈ (fun v => v * k₀ n) ''
      M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) E β (scale n) 1 ∪
      (fun v => v * k₀ n * step n) ''
        M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) E β (scale n) 1 → ∀ z,
      (profile n q).val z =
        rescaledMapProfile (fun g => (π ((p n).val.1 g)).toAdd) (x n) (F.inclusionN q)
        (max (Real.log (scale n)) 0)
        (fun z => F.inclusionD (F.ExpD (F.D.equiv
          ((exponentialRescaleBasis (WordBasisSelections.basis X (boundedBracketWords d) βD)
            (fun j => bracketWordExponent (fun _ : I => 1) (βD.val j))
            (max (Real.log (scale n)) 0)).equivFun.symm z)))) z)
    (ν : ProbabilityMeasure (S × S))
    (hν : Tendsto (fun n => ProbabilityMeasure.map
      (M.translatedGroupBoxProbability T F hunimod eW haarN chartN hchartN b₀ E β
        (scale n) (k₀ n)) (f := (fun q => (profile n q, profile n (q * step n)))) (((hp n).prodMk ((hp n).comp (continuous_id.mul continuous_const).measurable)).aemeasurable)) atTop (𝓝 ν))
    (σ : Fin M.letterCount → Bool)
    (hσ : (weightChamber (fun i =>
      ((M.supportIn T hunimod eW).weight i).toContinuousLinearMap) σ).Nonempty)
    (pivot : Fin M.letterCount → H) (B : ℝ) (mode : Fin M.letterCount)
    (time : ℕ → ℝ)
    (htime : ∀ n, |time n| ≤ R n * Real.exp
      ((M.weight mode (pivot mode) + δ * B) * scale n))
    (hroot : ∀ n, F.inclusionN (step n) =
      Exp (time n • (M.letter mode : GroupLieAlgebra (𝓘(ℝ, EG)) G)))
    (hthreshold : ∀ D : AffineNeighborRow T M F hunimod eW π b₀ E β X βD
      haarN chartN hchartN pivot c B δ S (Λ := Λ), D.label₁ = D.label₂) :
    ∀ (f : S × S), f ∈ (ν : Measure (S × S)).support →
      ∃ (A : templateSymmetryGroup (M.supportIn T hunimod eW)) (b₁ b₂ : W),
        ∀ z, eW (heightProjection T.character
          ((WordBasisSelections.basis X (boundedBracketWords d) βD).equivFun.symm z :
            GroupLieAlgebra (𝓘(ℝ, EG)) G)) ∈ (fun w => (1 - c * δ) • w) '' interior E →
          f.1.val z = A.val (eW (heightProjection T.character
            ((WordBasisSelections.basis X (boundedBracketWords d) βD).equivFun.symm z :
              GroupLieAlgebra (𝓘(ℝ, EG)) G))) + b₁ ∧
          f.2.val z = A.val (eW (heightProjection T.character
            ((WordBasisSelections.basis X (boundedBracketWords d) βD).equivFun.symm z :
              GroupLieAlgebra (𝓘(ℝ, EG)) G))) + b₂ := by
  intro f hf
  obtain ⟨A₁, A₂, b₁, b₂, haff⟩ :=
    M.cartan_neighbor_profiles_affine_on_contracted_cell T F hunimod eW hExp realize
      haarN haarD dynkinN dynkinD m π hπExp hdec hvan hΛ hπ hpath chartN hchartN
      b₀ hE hconv hint β γ hβ hδ hc hhi ht hcost hgap X hDnil hDletters bD₀ βD hβD
      aN hmN aD hmD scale hscale hmono hscale1 R hR0 hR k₀ step hk₀ hstep
      rem hdim p x S hS profile hp hactual ν hν σ hσ f hf
  have hraw (n) (q : F.N.carrier)
      (hq : q ∈ (fun v => v * k₀ n) ''
        M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) E β (scale n) 1) (z) :
      let b := WordBasisSelections.basis X (boundedBracketWords d) βD
      let br := exponentialRescaleBasis b
        (fun l => bracketWordExponent (fun _ : I => 1) (βD.val l)) (Real.log (scale n))
      (profile n q).val z = rescaledMapProfile
        (fun g => (π ((p n).val.1 g)).toAdd) (x n) (F.inclusionN q)
        (Real.log (scale n)) (fun z => Exp (br.equivFun.symm z)) z ∧
      (profile n (q * step n)).val z = rescaledMapProfile
        (fun g => (π ((p n).val.1 g)).toAdd) (x n) (F.inclusionN (q * step n))
        (Real.log (scale n)) (fun z => Exp (br.equivFun.symm z)) z := by
    have htlog : max (Real.log (scale n)) 0 = Real.log (scale n) :=
      max_eq_left (Real.log_nonneg (hscale1 n))
    have hqstep : q * step n ∈ (fun v => v * k₀ n * step n) ''
        M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) E β (scale n) 1 := by
      obtain ⟨v, hv, rfl⟩ := hq
      exact ⟨v, hv, rfl⟩
    constructor
    · simpa only [htlog, F.compatibleD] using hactual n q (Or.inl hq) z
    · simpa only [htlog, F.compatibleD] using hactual n (q * step n) (Or.inr hqstep) z
  let row : AffineNeighborRow T M F hunimod eW π b₀ E β X βD
      haarN chartN hchartN pivot c B δ S (Λ := Λ) :=
    { scale := scale
      grows := hscale
      pair := p
      center := x
      radius := R
      radius_nonneg := hR0
      radius_subexponential := hR
      base := k₀
      step := step
      basis := fun _ => β
      base_mem := hk₀
      step_mem := hstep
      mode := mode
      time := time
      time_bound := htime
      root_step := hroot
      profile := fun n q => (profile n q, profile n (q * step n))
      measurable_profile := fun n => (hp n).prodMk
        ((hp n).comp (continuous_id.mul continuous_const).measurable)
      actual := hraw
      law := ν
      converges := hν
      point := f
      supported := hf
      label₁ := A₁
      label₂ := A₂
      offset₁ := b₁
      offset₂ := b₂
      affine₁ := fun z hz => (haff z hz).1
      affine₂ := fun z hz => (haff z hz).2 }
  have heq : A₁ = A₂ := hthreshold row
  refine ⟨A₁, b₁, b₂, ?_⟩
  simpa only [heq] using haff

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_WeightSamplingPolytope
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finite_templateSymmetryGroup _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteRootOffsetConeIndex _root_.OAI.PolycyclicRecognition.instFiniteSubtypeLinearEquivRealIdMemSubgroupLinearSupportSymmetryGroup _root_.OAI.PolycyclicRecognition.instNonemptyRootOffsetConeIndex _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The compact polyhedron used for sampling the nilpotent boxes -/

noncomputable section
namespace PolycyclicRecognition

open Set
open scoped BigOperators

variable {W I B : Type} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [FiniteDimensional ℝ W] [Fintype I] [Fintype B]

omit [FiniteDimensional ℝ W] in
/-- Each balanced positive-multiplicity basis controls the absolute value
of every generator weight, including its negative part. -/
theorem SupportDatum.abs_weight_le_basisSupport (D : SupportDatum W I B)
    (b : B) (i : I) (x : W) : |D.weight i x| ≤ D.basisSupport b x := by
  classical
  have hpos (y : W) : D.weight i y ≤ D.basisSupport b y := by
    have hn : (1 : ℝ) ≤ D.multiplicity b i := by exact_mod_cast D.positive b i
    calc
      D.weight i y ≤ max 0 (D.weight i y) := le_max_right _ _
      _ ≤ (D.multiplicity b i : ℝ) * max 0 (D.weight i y) :=
        le_mul_of_one_le_left (le_max_left _ _) hn
      _ ≤ D.basisSupport b y := by
        apply Finset.single_le_sum (s := Finset.univ) (f := fun j =>
          (D.multiplicity b j : ℝ) * max 0 (D.weight j y))
        · intro j _
          exact mul_nonneg (Nat.cast_nonneg _) (le_max_left _ _)
        · exact Finset.mem_univ i
  have hm := hpos (-x)
  rw [map_neg, D.basisSupport_neg] at hm
  exact abs_le.mpr ⟨by linarith, hpos x⟩

omit [FiniteDimensional ℝ W] [Fintype B] [Fintype I] in
theorem isClosed_weightSamplingPolytope (α : I → W →L[ℝ] ℝ) :
    IsClosed (weightSamplingPolytope α) := by
  simp only [weightSamplingPolytope, ofPred_forall]
  exact isClosed_iInter fun i => isClosed_le (α i).continuous continuous_const

omit [FiniteDimensional ℝ W] [Fintype B] [Fintype I] in
theorem convex_weightSamplingPolytope (α : I → W →L[ℝ] ℝ) :
    Convex ℝ (weightSamplingPolytope α) := by
  simp only [weightSamplingPolytope, ofPred_forall]
  exact convex_iInter fun i => convex_halfSpace_le (α i).toLinearMap.isLinear _

omit [FiniteDimensional ℝ W] [Fintype B] in
theorem isOpen_weightSamplingInterior (α : I → W →L[ℝ] ℝ) :
    IsOpen (weightSamplingInterior α) := by
  simp only [weightSamplingInterior, ofPred_forall]
  exact isOpen_iInter_of_finite fun i => isOpen_lt (α i).continuous continuous_const

omit [FiniteDimensional ℝ W] [Fintype B] in
theorem weightSamplingInterior_subset_interior (α : I → W →L[ℝ] ℝ) :
    weightSamplingInterior α ⊆ interior (weightSamplingPolytope α) := by
  apply interior_maximal
  · intro x hx i
    exact (hx i).le
  · exact isOpen_weightSamplingInterior α

omit [FiniteDimensional ℝ W] [Fintype B] [Fintype I] in
theorem closedBall_subset_weightSamplingPolytope (α : I → W →L[ℝ] ℝ) :
    Metric.closedBall (0 : W) 1 ⊆ weightSamplingPolytope α := by
  intro x hx i
  have hn : ‖x‖ ≤ 1 := by simpa using hx
  exact ((le_abs_self _).trans ((α i).le_opNorm x)).trans
    ((mul_le_mul_of_nonneg_left hn (norm_nonneg _)).trans_eq (mul_one _))

omit [FiniteDimensional ℝ W] [Fintype B] [Fintype I] in
theorem zero_mem_weightSamplingInterior (α : I → W →L[ℝ] ℝ)
    (hα : ∀ i, α i ≠ 0) : (0 : W) ∈ weightSamplingInterior α := by
  intro i
  simpa using norm_pos_iff.mpr (hα i)

/-- Positive balance and separation make the sampling polyhedron compact.
No boundedness assumption on the polyhedron is needed. -/
theorem SupportDatum.isCompact_weightSamplingPolytope (D : SupportDatum W I B) (b : B) :
    IsCompact (weightSamplingPolytope (fun i => (D.weight i).toContinuousLinearMap)) := by
  classical
  let α : W →ₗ[ℝ] (I → ℝ) := LinearMap.pi D.weight
  have hα : Function.Injective α := by
    apply LinearMap.ker_eq_bot.mp
    apply eq_bot_iff.mpr
    intro x hx
    apply D.separates x
    intro i
    exact congrFun hx i
  have hemb := LinearMap.isClosedEmbedding_of_injective (LinearMap.ker_eq_bot.mpr hα)
  let C : ℝ := ∑ i, (D.multiplicity b i : ℝ) * ‖(D.weight i).toContinuousLinearMap‖
  have hbound : weightSamplingPolytope (fun i => (D.weight i).toContinuousLinearMap) ⊆
      α ⁻¹' Icc (fun _ => -C) (fun _ => C) := by
    intro x hx
    have hs : D.basisSupport b x ≤ C := by
      apply Finset.sum_le_sum
      intro i _
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      exact max_le (norm_nonneg _) (hx i)
    constructor <;> intro i
    · exact neg_le_of_abs_le ((D.abs_weight_le_basisSupport b i x).trans hs)
    · exact le_of_abs_le ((D.abs_weight_le_basisSupport b i x).trans hs)
  exact (hemb.isCompact_preimage isCompact_Icc).of_isClosed_subset
    (isClosed_weightSamplingPolytope _) hbound

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanSamplingParameters
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_nonempty _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Concrete parameters for the neighboring-sheet sampling argument -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra Set

variable {L W : Type} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {H : LieSubalgebra ℝ L} [H.IsCartanSubalgebra] (M : CartanWordModel H)
  {a : ℕ} (T : TriangularAdjoint L a)
  (hunimod : ∀ x : L, LinearMap.trace ℝ L (ad ℝ L x) = 0)
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)

set_option maxHeartbeats 1000000 in
theorem isCompact_samplingPolytope : IsCompact (M.samplingPolytope T hunimod eW) := by
  exact (M.supportIn T hunimod eW).isCompact_weightSamplingPolytope (Classical.arbitrary M.Bases)

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_FixedWeightContact
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A common Euclidean contact point for every cone containing one root -/

noncomputable section
namespace PolycyclicRecognition

open Set

variable {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
  [FiniteDimensional ℝ W]

/-- All unit contact points for a nonzero functional coincide. -/
theorem weight_contact_unique (α : W →L[ℝ] ℝ) (hα : α ≠ 0)
    {p q : W} (hp : ‖p‖ = 1) (hq : ‖q‖ = 1)
    (hap : α p = ‖α‖) (haq : α q = ‖α‖) : p = q := by
  let v := (InnerProductSpace.toDual ℝ W).symm α
  have hv : ‖v‖ = ‖α‖ := (InnerProductSpace.toDual ℝ W).symm.norm_map α
  have hc (x : W) (hx : ‖x‖ = 1) (hax : α x = ‖α‖) : v = ‖α‖ • x := by
    have he : inner ℝ v x = ‖v‖ * ‖x‖ := by
      rw [show inner ℝ v x = α x from InnerProductSpace.toDual_symm_apply,
        hax, hv, hx, mul_one]
    simpa only [hx, one_smul, hv] using inner_eq_norm_mul_iff_real.mp he
  have he := congrArg (fun x : W => ‖α‖⁻¹ • x) ((hc p hp hap).symm.trans (hc q hq haq))
  simpa only [smul_smul, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hα), one_smul] using he


end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanPolarConeModels
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Published inputs for the finite polar-cone models

This record only groups the already stated nilpotent existence, integration
and exponential Haar inputs. It contains no metric or profile conclusion.
It is instantiated separately for each ray or two-ray cone used below.
-/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra
open scoped Manifold

variable {EG G : Type} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G]
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H Exp)
  (C : Set (H →ₗ[ℝ] ℝ))

variable [SimplyConnectedSpace G] {a : ℕ}
  (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  (hExp : IsGroupExponential Exp)
  (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
  (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
  (inputs : M.PolarConeModelInputs F C)

set_option maxHeartbeats 1000000 in
theorem PolarConeModelInputs.model_haarQ :
    NilpotentExponentialHaarInput
      (inputs.model M F C T hExp realize haarN).Q.modelSpace
      (inputs.model M F C T hExp realize haarN).Q.carrier :=
  inputs.haarQ _

set_option maxHeartbeats 1000000 in
theorem PolarConeModelInputs.model_haarI :
    NilpotentExponentialHaarInput
      (inputs.model M F C T hExp realize haarN).I.modelSpace
      (inputs.model M F C T hExp realize haarN).I.carrier :=
  inputs.haarI _

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanPublishedOffsetThreshold
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_nonempty _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.unitaryCentralFixed_complete _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform offsets from published finite-cone realization inputs -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule MeasureTheory Filter Set
open scoped Manifold Topology ENNReal NNReal BigOperators

attribute [local instance] stationaryL2Action zeroMeanL2Action

variable {EG G W I : Type} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G]
  [IsTopologicalGroup G] [IsIsometricSMul G G] [ProperSpace G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  [MeasurableSpace W] [BorelSpace W] [SecondCountableTopology W]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H) [Nonempty (Fin M.letterCount)]
  [Nonempty (Fin (finrank ℝ (cartanRootIdeal H)))]
  {Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H Exp)
  (hunimod : ∀ x : GroupLieAlgebra (𝓘(ℝ, EG)) G, LinearMap.trace ℝ _ (ad ℝ _ x) = 0)
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)
  [IsTopologicalGroup F.N.carrier] [SecondCountableTopology F.N.carrier]
  [IsTopologicalGroup F.D.carrier] [SecondCountableTopology F.D.carrier]
  [Fintype I] [DecidableEq I] {Λ : ℝ≥0}
  [MeasurableSpace (NormalizedPair G Λ)] [BorelSpace (NormalizedPair G Λ)]
  [MeasurableSpace C((Fin (finrank ℝ H) → ℝ), W)]
  [BorelSpace C((Fin (finrank ℝ H) → ℝ), W)]

local notation "Eall" => M.samplingPolytope T hunimod eW

set_option maxHeartbeats 1000000 in
/-- Construct the finite cone models before taking the common offset
threshold. No target model, Haar action or trace comparison is assumed. -/
theorem exists_published_polar_offset_threshold
    (hExp : IsGroupExponential Exp)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
    (haarD : NilpotentExponentialHaarInput F.D.modelSpace F.D.carrier)
    (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
    (dynkinD : NilpotentDynkinExpansionInput F.D.modelSpace F.D.carrier)
    (chartN : GroupLieAlgebra (𝓘(ℝ, F.N.modelSpace)) F.N.carrier ≃ₜ F.N.carrier)
    (hchartN : ∀ x, chartN x = F.ExpN x)
    (chartD : GroupLieAlgebra (𝓘(ℝ, F.D.modelSpace)) F.D.carrier ≃ₜ F.D.carrier)
    (hchartD : ∀ x, chartD x = F.ExpD x)
    (m : Measure G) [m.IsHaarMeasure] [m.IsMulRightInvariant]
    (νD : Measure F.D.carrier) [νD.IsHaarMeasure] [SFinite νD]
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
    (bN : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (γ : M.Bases)
    (hγ : IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList bN)
      (M.boxCost T hunimod eW Eall) γ.val)
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
    (rem : RemezPolynomialInput) (hdim : 1 ≤ finrank ℝ (cartanRootIdeal H))
    (pivot : Fin M.letterCount → H)
    (hcanonical : ∀ i, cartanHeightSection T H (heightProjection T.character (pivot i)) = pivot i)
    (hunit : ∀ i, ‖eW (heightProjection T.character (pivot i))‖ = 1)
    (hcontact : ∀ i, ((M.supportIn T hunimod eW).weight i).toContinuousLinearMap
      (eW (heightProjection T.character (pivot i))) =
        ‖((M.supportIn T hunimod eW).weight i).toContinuousLinearMap‖)
    (hpositive : ∀ i, 0 < M.weight i (pivot i))
    {lo hi c B : ℝ} (hc : 0 ≤ c) (hhi : 0 ≤ hi) (hB : 0 ≤ B)
    (hcost : ∀ w : M.wordList, lo ≤ M.boxCost T hunimod eW Eall w ∧
      M.boxCost T hunimod eW Eall w ≤ hi)
    (hgap : (M.bound : ℝ) * hi < c * lo)
    (σchamber : Fin M.letterCount → Bool)
    (hσchamber : (weightChamber (fun j =>
      ((M.supportIn T hunimod eW).weight j).toContinuousLinearMap) σchamber).Nonempty)
    (Profiles : Set C((Fin (finrank ℝ H) → ℝ), W))
    [MeasurableSpace Profiles] [BorelSpace Profiles] [BorelSpace (Profiles × Profiles)]
    (hnz : ∀ i, (M.supportIn T hunimod eW).weight i ≠ 0)
    (sourceInputs : ∀ (i : Fin M.letterCount)
      (s : rootOffsetConeIndex (M.supportIn T hunimod eW) i),
      M.PolarConeModelInputs F (heightConePreimage T eW
        (rootOffsetCone (M.supportIn T hunimod eW) hnz i s)))
    (sourceDynkin : ∀ (i : Fin M.letterCount)
      (s : rootOffsetConeIndex (M.supportIn T hunimod eW) i)
      (J : NilpotentLieModel (M.coneWordIdeal (heightConePreimage T eW
        (rootOffsetCone (M.supportIn T hunimod eW) hnz i s)))),
      NilpotentDynkinExpansionInput J.modelSpace J.carrier)
    (targetInputs : ∀ (i : Fin M.letterCount)
      (A : templateSymmetryGroup (M.supportIn T hunimod eW))
      (s : rootOffsetConeIndex (M.supportIn T hunimod eW) i),
      M.PolarConeModelInputs F (heightConePreimage T eW
        (transformedPolarCone (rootOffsetCone (M.supportIn T hunimod eW) hnz i s) A.val))) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
      ∀ row : AffineNeighborRow T M F hunimod eW π bN Eall γ X βD
        haarN chartN hchartN pivot c B δ Profiles (Λ := Λ),
      row.label₂ = row.label₁ → row.offset₁ = row.offset₂ := by
  let Ds := fun i s => (sourceInputs i s).model M F _ T hExp realize haarN
  let Dt := fun i A s => (targetInputs i A s).model M F _ T hExp realize haarN
  exact M.exists_uniform_polar_offset_threshold T F hunimod eW
    hExp realize haarN haarD dynkinN dynkinD chartN hchartN chartD hchartD m νD
    π hπExp hdec hvan hΛ hπ hpath bN γ hγ X hDnil hDletters bD₀ βD hβD
    aN hmN aD hmD rem hdim pivot hcanonical hunit hcontact hpositive
    hc hhi hB hcost hgap σchamber hσchamber Profiles hnz Ds
    (fun i s => sourceDynkin i s (Ds i s).I)
    (fun i s => (sourceInputs i s).model_haarI M F _ T hExp realize haarN)
    Dt
    (fun i A s => (targetInputs i A s).model_haarQ M F _ T hExp realize haarN)
    (fun i A s => (targetInputs i A s).model_haarI M F _ T hExp realize haarN)

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanUniformCommonAffinity
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_countable _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_nonempty _root_.OAI.PolycyclicRecognition.finitelyGeneratedSubgroupIndex_countable _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.instFiniteRootOffsetConeIndex _root_.OAI.PolycyclicRecognition.instNonemptyRootOffsetConeIndex _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.unitaryCentralFixed_complete _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Neighboring-sheet affinity directly from enlarged box membership -/

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
/-- A positive enlargement works for every original neighboring-cell law.
The common affine label is derived from the published analytic inputs and
the geometric reflection argument; no affinity or label premise remains. -/
theorem exists_uniform_neighbor_common_affinity
    [IsTopologicalGroup F.N.carrier]
    [SecondCountableTopology F.N.carrier] [SecondCountableTopology F.D.carrier]
    [IsTopologicalGroup F.D.carrier] [Nonempty (Fin M.letterCount)]
    [Nonempty (Fin (finrank ℝ (cartanRootIdeal H)))]
    (hExp : IsGroupExponential Exp) (hinj : Function.Injective Exp)
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
    (chartN : GroupLieAlgebra (𝓘(ℝ, F.N.modelSpace)) F.N.carrier ≃ₜ F.N.carrier)
    (hchartN : ∀ v, chartN v = F.ExpN v)
    (chartD : GroupLieAlgebra (𝓘(ℝ, F.D.modelSpace)) F.D.carrier ≃ₜ F.D.carrier)
    (hchartD : ∀ v, chartD v = F.ExpD v)
    (hbijN : Function.Bijective F.ExpN) (hbijD : Function.Bijective F.ExpD)
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    {E : Set W} (hE : IsCompact E) (hconv : Convex ℝ E) (hint : (interior E).Nonempty) (β γ : M.Bases)
    (hβ : IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
      (M.boxCost T hunimod eW E) β.val)
    {c lo hi : ℝ} (hc : 0 ≤ c) (hhi : 0 ≤ hi)
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
    (rem : RemezPolynomialInput) (hdim : 1 ≤ finrank ℝ (cartanRootIdeal H))
    (νD : Measure F.D.carrier) [νD.IsHaarMeasure] [SigmaFinite νD]
    (S : Set C((Fin (finrank ℝ H) → ℝ), W))
    (hS : IsCompact S)
    [MeasurableSpace S] [BorelSpace S] [BorelSpace (S × S)] [HasOuterApproxClosed S] [HasOuterApproxClosed (S × S)]
    (pivot : Fin M.letterCount → H)
    (hpivot : ∀ i, eW (heightProjection T.character (pivot i)) ∈ E)
    {J : Type} [Fintype J] (α : J → W →ₗ[ℝ] ℝ) (cap : J → ℝ)
    (hpoly : E = {w | ∀ j, α j w ≤ cap j})
    (hactive : ∀ i j, α j (eW (heightProjection T.character (pivot i))) = cap j →
      ∃ t : ℝ, 0 < t ∧ α j = t • (M.supportIn T hunimod eW).weight i)
    (B : ℝ) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
    ∀ (scale : ℕ → ℝ) (_hscale : Tendsto scale atTop atTop) (_hmono : StrictMono scale) (_hscale1 : ∀ n, 1 ≤ scale n)
    (R : ℕ → ℝ) (_hR0 : ∀ n, 0 ≤ R n)
    (_hR : HasSubexponentialUpperBoundSeq scale R)
    (k₀ step : ℕ → F.N.carrier)
    (_hk₀ : ∀ n, k₀ n ∈ M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv)
      ((fun w => (1 + δ) • w) '' E) β (scale n) (R n))
    (_hstep : ∀ n, step n ∈ M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv)
      ((fun w => (1 + δ) • w) '' E) β (scale n) (R n))
    (p : ℕ → NormalizedPair G Λ) (x : ℕ → G)
    (profile : ℕ → F.N.carrier → S)
    (_hp : ∀ n, Measurable (profile n))
    (_hactual : ∀ n q, q ∈ (fun v => v * k₀ n) ''
      M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) E β (scale n) 1 ∪
      (fun v => v * k₀ n * step n) ''
        M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) E β (scale n) 1 → ∀ z,
      (profile n q).val z =
        rescaledMapProfile (fun g => (π ((p n).val.1 g)).toAdd) (x n) (F.inclusionN q)
        (max (Real.log (scale n)) 0)
        (fun z => F.inclusionD (F.ExpD (F.D.equiv
          ((exponentialRescaleBasis (WordBasisSelections.basis X (boundedBracketWords d) βD)
            (fun j => bracketWordExponent (fun _ : I => 1) (βD.val j))
            (max (Real.log (scale n)) 0)).equivFun.symm z)))) z)
    (ν : ProbabilityMeasure (S × S))
    (_hν : Tendsto (fun n => ProbabilityMeasure.map
      (M.translatedGroupBoxProbability T F hunimod eW haarN chartN hchartN b₀ E β
        (scale n) (k₀ n)) (f := (fun q => (profile n q, profile n (q * step n)))) (((_hp n).prodMk ((_hp n).comp (continuous_id.mul continuous_const).measurable)).aemeasurable)) atTop (𝓝 ν))
    (σ : Fin M.letterCount → Bool)
    (_hσ : (weightChamber (fun i =>
      ((M.supportIn T hunimod eW).weight i).toContinuousLinearMap) σ).Nonempty)
    (mode : Fin M.letterCount)
    (time : ℕ → ℝ)
    (_htime : ∀ n, |time n| ≤ R n * Real.exp
      ((M.weight mode (pivot mode) + δ * B) * scale n))
    (_hroot : ∀ n, F.inclusionN (step n) =
      Exp (time n • (M.letter mode : GroupLieAlgebra (𝓘(ℝ, EG)) G))),
    ∀ (f : S × S), f ∈ (ν : Measure (S × S)).support →
      ∃ (A : templateSymmetryGroup (M.supportIn T hunimod eW)) (b₁ b₂ : W),
        ∀ z, eW (heightProjection T.character
          ((WordBasisSelections.basis X (boundedBracketWords d) βD).equivFun.symm z :
            GroupLieAlgebra (𝓘(ℝ, EG)) G)) ∈ (fun w => (1 - c * δ) • w) '' interior E →
          f.1.val z = A.val (eW (heightProjection T.character
            ((WordBasisSelections.basis X (boundedBracketWords d) βD).equivFun.symm z :
              GroupLieAlgebra (𝓘(ℝ, EG)) G))) + b₁ ∧
          f.2.val z = A.val (eW (heightProjection T.character
            ((WordBasisSelections.basis X (boundedBracketWords d) βD).equivFun.symm z :
              GroupLieAlgebra (𝓘(ℝ, EG)) G))) + b₂ := by
  obtain ⟨ε, hε, hlabel⟩ := M.exists_uniform_neighbor_label_threshold_m T F hunimod eW
    hExp hinj realize rem π hπ hπExp chartN hchartN chartD hchartD hbijN hbijD
    dynkinN dynkinD haarN haarD b₀ E hE hconv hint pivot hpivot α cap hpoly hactive
    β hβ X hDnil bD₀ βD hβD aN hmN hdim νD hpath hΛ c B S hS
  let δ₀ := min ε (1 / (2 * (c + 1)))
  refine ⟨δ₀, lt_min hε (by positivity), ?_⟩
  intro δ hδ hd scale hscale hmono hscale1 R hR0 hR k₀ step hk₀ hstep p x
    profile hp hactual ν hν σ hσ mode time htime hroot
  have hbound : δ * (2 * (c + 1)) ≤ 1 := by
    exact (le_div_iff₀ (by positivity : 0 < 2 * (c + 1))).mp
      (hd.trans (min_le_right ε _))
  have ht : 0 < 1 - c * δ := by nlinarith [mul_nonneg hc hδ.le]
  exact M.cartan_neighbor_profiles_common_affine_of_threshold T F hunimod eW
    hExp realize haarN haarD dynkinN dynkinD m π hπExp hdec hvan hΛ hπ hpath
    chartN hchartN b₀ hE hconv hint β γ hβ hδ hc hhi ht hcost hgap X hDnil
    hDletters bD₀ βD hβD aN hmN aD hmD scale hscale hmono hscale1 R hR0 hR
    k₀ step hk₀ hstep rem hdim p x S hS profile hp hactual ν hν σ hσ
    pivot B mode time htime hroot (hlabel δ hδ (hd.trans (min_le_left _ _)))

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanIdenticalNeighborProfiles
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_nonempty _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.unitaryCentralFixed_complete _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.CartanFactorModel.realScaleProfile_apply _root_.OAI.PolycyclicRecognition.basisDynkinParameter_zero _root_.OAI.PolycyclicRecognition.bracketWordDifferential_mul _root_.OAI.PolycyclicRecognition.cartanWeightDerivation_apply_root _root_.OAI.PolycyclicRecognition.chartExponentialFlow_zero _root_.OAI.PolycyclicRecognition.derivationSemidirectHom_apply _root_.OAI.PolycyclicRecognition.exponentialHomOfDynkin_apply_exp _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.modelNilradicalLinearAction_apply _root_.OAI.PolycyclicRecognition.modelNilradicalRotation_apply _root_.OAI.PolycyclicRecognition.modelNilradicalRotation_mul _root_.OAI.PolycyclicRecognition.modelNilradicalRotation_one _root_.OAI.PolycyclicRecognition.nilshadowWeightDerivation_symm _root_.OAI.PolycyclicRecognition.nilshadowWeightOperator_symm _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Identical affine limits of original neighboring samples -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule MeasureTheory Filter Set
open scoped Manifold Topology ENNReal NNReal BigOperators

attribute [local instance] stationaryL2Action zeroMeanL2Action

variable {EG G W I : Type} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G]
  [IsTopologicalGroup G] [IsIsometricSMul G G] [ProperSpace G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  [MeasurableSpace W] [BorelSpace W] [SecondCountableTopology W]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H) [Nonempty (Fin M.letterCount)]
  [Nonempty (Fin (finrank ℝ (cartanRootIdeal H)))]
  {Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H Exp)
  (hunimod : ∀ x : GroupLieAlgebra (𝓘(ℝ, EG)) G, LinearMap.trace ℝ _ (ad ℝ _ x) = 0)
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)
  [IsTopologicalGroup F.N.carrier] [SecondCountableTopology F.N.carrier]
  [IsTopologicalGroup F.D.carrier] [SecondCountableTopology F.D.carrier]
  [Fintype I] [DecidableEq I] {Λ : ℝ≥0}
  [MeasurableSpace (NormalizedPair G Λ)] [BorelSpace (NormalizedPair G Λ)]
  [MeasurableSpace C((Fin (finrank ℝ H) → ℝ), W)]
  [BorelSpace C((Fin (finrank ℝ H) → ℝ), W)]

local notation "Eall" => M.samplingPolytope T hunimod eW

set_option maxHeartbeats 1000000 in
/-- One threshold gives a single affine profile on both neighboring sheets.
The common label and both offsets are derived from the original sample law. -/
theorem exists_uniform_identical_neighbor_profiles_oai
    (hExp : IsGroupExponential Exp) (hinj : Function.Injective Exp)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
    (haarD : NilpotentExponentialHaarInput F.D.modelSpace F.D.carrier)
    (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
    (dynkinD : NilpotentDynkinExpansionInput F.D.modelSpace F.D.carrier)
    (chartN : GroupLieAlgebra (𝓘(ℝ, F.N.modelSpace)) F.N.carrier ≃ₜ F.N.carrier)
    (hchartN : ∀ x, chartN x = F.ExpN x)
    (chartD : GroupLieAlgebra (𝓘(ℝ, F.D.modelSpace)) F.D.carrier ≃ₜ F.D.carrier)
    (hchartD : ∀ x, chartD x = F.ExpD x)
    (m : Measure G) [m.IsHaarMeasure] [m.IsMulRightInvariant]
    (νD : Measure F.D.carrier) [νD.IsHaarMeasure] [SigmaFinite νD]
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
    (bN : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (γ : M.Bases)
    (hγ : IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList bN)
      (M.boxCost T hunimod eW Eall) γ.val)
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
    (rem : RemezPolynomialInput) (hdim : 1 ≤ finrank ℝ (cartanRootIdeal H))
    (pivot : Fin M.letterCount → H)
    (hcanonical : ∀ i, cartanHeightSection T H (heightProjection T.character (pivot i)) = pivot i)
    (hunit : ∀ i, ‖eW (heightProjection T.character (pivot i))‖ = 1)
    (hcontact : ∀ i, ((M.supportIn T hunimod eW).weight i).toContinuousLinearMap
      (eW (heightProjection T.character (pivot i))) =
        ‖((M.supportIn T hunimod eW).weight i).toContinuousLinearMap‖)
    (hpositive : ∀ i, 0 < M.weight i (pivot i))
    {lo hi c B : ℝ} (hc : 0 ≤ c) (hhi : 0 ≤ hi) (hB : 0 ≤ B)
    (hcost : ∀ w : M.wordList, lo ≤ M.boxCost T hunimod eW Eall w ∧
      M.boxCost T hunimod eW Eall w ≤ hi)
    (hgap : (M.bound : ℝ) * hi < c * lo)
    (σchamber : Fin M.letterCount → Bool)
    (hσchamber : (weightChamber (fun j =>
      ((M.supportIn T hunimod eW).weight j).toContinuousLinearMap) σchamber).Nonempty)
    (Profiles : Set C((Fin (finrank ℝ H) → ℝ), W))
    [MeasurableSpace Profiles] [BorelSpace Profiles] [BorelSpace (Profiles × Profiles)]
    (hProfiles : IsCompact Profiles)
    [HasOuterApproxClosed Profiles] [HasOuterApproxClosed (Profiles × Profiles)]
    (hnz : ∀ i, (M.supportIn T hunimod eW).weight i ≠ 0)
    (sourceInputs : ∀ (i : Fin M.letterCount)
      (s : rootOffsetConeIndex (M.supportIn T hunimod eW) i),
      M.PolarConeModelInputs F (heightConePreimage T eW
        (rootOffsetCone (M.supportIn T hunimod eW) hnz i s)))
    (sourceDynkin : ∀ (i : Fin M.letterCount)
      (s : rootOffsetConeIndex (M.supportIn T hunimod eW) i)
      (J : NilpotentLieModel (M.coneWordIdeal (heightConePreimage T eW
        (rootOffsetCone (M.supportIn T hunimod eW) hnz i s)))),
      NilpotentDynkinExpansionInput J.modelSpace J.carrier)
    (targetInputs : ∀ (i : Fin M.letterCount)
      (A : templateSymmetryGroup (M.supportIn T hunimod eW))
      (s : rootOffsetConeIndex (M.supportIn T hunimod eW) i),
      M.PolarConeModelInputs F (heightConePreimage T eW
        (transformedPolarCone (rootOffsetCone (M.supportIn T hunimod eW) hnz i s) A.val))) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
      ∀ row : NeighborSamplingRow T M F hunimod eW π bN Eall γ X βD
        haarN chartN hchartN pivot B δ Profiles (Λ := Λ),
      ∃ (A : templateSymmetryGroup (M.supportIn T hunimod eW)) (b : W),
        ∀ z, eW (heightProjection T.character
          ((WordBasisSelections.basis X (boundedBracketWords d) βD).equivFun.symm z :
            GroupLieAlgebra (𝓘(ℝ, EG)) G)) ∈ (fun w => (1 - c * δ) • w) '' interior Eall →
          row.point.1.val z = A.val (eW (heightProjection T.character
            ((WordBasisSelections.basis X (boundedBracketWords d) βD).equivFun.symm z :
              GroupLieAlgebra (𝓘(ℝ, EG)) G))) + b ∧
          row.point.2.val z = A.val (eW (heightProjection T.character
            ((WordBasisSelections.basis X (boundedBracketWords d) βD).equivFun.symm z :
              GroupLieAlgebra (𝓘(ℝ, EG)) G))) + b := by
  obtain ⟨δoff, hδoff, hoff⟩ := M.exists_published_polar_offset_threshold T F hunimod eW
    hExp realize haarN haarD dynkinN dynkinD chartN hchartN chartD hchartD m νD
    π hπExp hdec hvan hΛ hπ hpath bN γ hγ X hDnil hDletters bD₀ βD hβD
    aN hmN aD hmD rem hdim pivot hcanonical hunit hcontact hpositive
    hc hhi hB hcost hgap σchamber hσchamber Profiles hnz sourceInputs sourceDynkin targetInputs
  let α := fun j => ((M.supportIn T hunimod eW).weight j).toContinuousLinearMap
  have hnα : ∀ j, α j ≠ 0 := M.sampling_weight_ne_zero T hunimod eW
  have hconv : Convex ℝ Eall := convex_weightSamplingPolytope α
  have hint : (interior Eall).Nonempty :=
    ⟨0, weightSamplingInterior_subset_interior α (zero_mem_weightSamplingInterior α hnα)⟩
  have hpivot : ∀ i, eW (heightProjection T.character (pivot i)) ∈ Eall := by
    intro i
    exact closedBall_subset_weightSamplingPolytope α (by simpa using (hunit i).le)
  have hactive : ∀ i j, (M.supportIn T hunimod eW).weight j
      (eW (heightProjection T.character (pivot i))) = ‖α j‖ →
      ∃ t : ℝ, 0 < t ∧ (M.supportIn T hunimod eW).weight j =
        t • (M.supportIn T hunimod eW).weight i := by
    intro i j hj
    obtain ⟨p, hp, hpi, hstrict⟩ := exists_weight_contact_point (α i) (hnα i)
    have heq : eW (heightProjection T.character (pivot i)) = p :=
      weight_contact_unique (α i) (hnα i) (hunit i) hp (hcontact i) hpi
    have hray : ∃ t : ℝ, 0 < t ∧ α j = t • α i := by
      by_contra hn
      have hlt := hstrict (α j) (hnα j) hn
      rw [← heq] at hlt
      exact (ne_of_lt hlt) hj
    obtain ⟨t, ht, he⟩ := hray
    exact ⟨t, ht, congrArg ContinuousLinearMap.toLinearMap he⟩
  have hbijN : Function.Bijective F.ExpN := funext hchartN ▸ chartN.bijective
  have hbijD : Function.Bijective F.ExpD := funext hchartD ▸ chartD.bijective
  obtain ⟨δaff, hδaff, haff⟩ := M.exists_uniform_neighbor_common_affinity T F hunimod eW
    hExp hinj realize haarN haarD dynkinN dynkinD m π hπExp hdec hvan hΛ hπ hpath
    chartN hchartN chartD hchartD hbijN hbijD bN
    (M.isCompact_samplingPolytope T hunimod eW) hconv hint γ γ hγ
    hc hhi hcost hgap X hDnil hDletters bD₀ βD hβD aN hmN aD hmD rem hdim
    νD Profiles hProfiles pivot hpivot
    (fun j => (M.supportIn T hunimod eW).weight j) (fun j => ‖α j‖) rfl hactive B
  refine ⟨min δoff δaff, lt_min hδoff hδaff, ?_⟩
  intro δ hδ hd row
  obtain ⟨A, b₁, b₂, hab⟩ := haff δ hδ (hd.trans (min_le_right _ _))
    row.scale row.grows row.strict_mono row.scale_ge_one
    row.radius row.radius_nonneg row.radius_subexponential
    row.base row.step row.base_mem row.step_mem row.pair row.center
    row.profile row.measurable_profile row.actual row.law row.converges
    σchamber hσchamber row.mode row.time row.time_bound row.root_step row.point row.supported
  let aff := row.withAffinity T M F hunimod eW π bN Eall γ X βD
    haarN chartN hchartN pivot c B δ Profiles A b₁ b₂ hab
  have heq : b₁ = b₂ := hoff δ hδ (hd.trans (min_le_left _ _)) aff rfl
  refine ⟨A, b₁, ?_⟩
  intro z hz
  simpa only [heq] using hab z hz

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

theorem solution : type_of% @OAI.PolycyclicRecognition.CartanWordModel.exists_uniform_identical_neighbor_profiles_oai := @OAI.PolycyclicRecognition.CartanWordModel.exists_uniform_identical_neighbor_profiles_oai
