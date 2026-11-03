-- Prove2me | solution 1 for OAI.PolycyclicRecognition.CartanWordModel.exists_published_sublinear_height
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-03T00:08:30.0652+00:00
-- url     : https://prove2.me/submissions/3879c377-ec0c-4c07-8393-d348177cb1ad

import Mathlib
import Definitions.Def_PolycyclicRecognition
import Definitions.Def_OAIQ093D014
import Definitions.Def_OAIQ093D015
import Definitions.Def_OAIQ093D016
import Theorems.Thm_OAI_PolycyclicRecognition_CartanWordModel_exists_uniform_published_affine_mean_approximation
import Theorems.Thm_OAI_PolycyclicRecognition_CartanWordModel_exists_uniform_published_basepoint_comparison
import Theorems.Thm_OAI_PolycyclicRecognition_CartanWordModel_exists_uniform_published_suffix_concentration
import Theorems.Thm_OAI_PolycyclicRecognition_exists_bounded_box_profile_anchors

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

omit [T2Space G] in
/-- Inversion preserves every exponential coordinate box exactly. -/
theorem inv_mem_exponentialCoordinateBox
    (e : L ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, E)) G)
    (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G) (hExp : IsGroupExponential Exp)
    {J : Type} [Fintype J] (b : Basis J ℝ L) {R : ℝ} {g : G}
    (hg : g ∈ exponentialCoordinateBox (Exp ∘ e) b R) :
    g⁻¹ ∈ exponentialCoordinateBox (Exp ∘ e) b R := by
  obtain ⟨x, rfl, hx⟩ := hg
  refine ⟨-x, ?_, ?_⟩
  · simp only [Function.comp_apply, map_neg, hExp.map_neg]
  · simpa only [map_neg, norm_neg] using hx

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

set_option maxHeartbeats 1000000 in
omit [T2Space N] in
/-- Inversion requires no extra group input beyond the intrinsic exponential. -/
theorem groupBox_inv_mem (E : Set W) (β : M.Bases) (r R : ℝ) {g : N}
    (hg : g ∈ M.groupBox T hunimod eW (Exp ∘ eN) E β r R) :
    g⁻¹ ∈ M.groupBox T hunimod eW (Exp ∘ eN) E β r R :=
  inv_mem_exponentialCoordinateBox eN Exp hExp (M.boxBasis T hunimod eW E β r) hg

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_UniformProfileConcentration
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform concentration and independent suffix sampling -/

noncomputable section
namespace PolycyclicRecognition

open Filter MeasureTheory Set
open scoped Topology ENNReal

/-- If every deterministic choice has vanishing bad probability, the
bound is uniform over all permitted choices at each scale. -/
theorem eventually_uniform_lt_of_all_selections
    {A : ℕ → Type} [∀ n, Nonempty (A n)] (p : ∀ n, A n → ℝ≥0∞)
    (hp : ∀ a : ∀ n, A n, Tendsto (fun n => p n (a n)) atTop (𝓝 0))
    {η : ℝ≥0∞} (hη : 0 < η) :
    ∀ᶠ n in atTop, ∀ a, p n a < η := by
  classical
  let a : ∀ n, A n := fun n => if h : ∃ a, η ≤ p n a then h.choose else Classical.arbitrary _
  have ha := (hp a).eventually (gt_mem_nhds hη)
  filter_upwards [ha] with n hn b
  by_contra h
  have hex : ∃ b, η ≤ p n b := ⟨b, le_of_not_gt h⟩
  have hb : η ≤ p n (a n) := by
    dsimp only [a]
    rw [dite_eq_left hex]
    exact hex.choose_spec
  exact (not_le_of_gt hn) hb

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_SequenceScaleExtraction
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_nonempty _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Cofinal, strictly increasing scales with one fixed finite mode -/

noncomputable section
namespace PolycyclicRecognition

open Filter

/-- A divergent real scale can be made strictly increasing and at least one
by restricting the original sequence. -/
theorem exists_strictMono_scale_subsequence (scale : ℕ → ℝ)
    (hs : Tendsto scale atTop atTop) :
    ∃ u : ℕ → ℕ, StrictMono u ∧ StrictMono (scale ∘ u) ∧
      ∀ n, 1 ≤ scale (u n) := by
  classical
  obtain ⟨n₀, hn₀⟩ := (hs.eventually (eventually_ge_atTop (1 : ℝ))).exists
  have he (n : ℕ) : ∃ k : ℕ, n < k ∧ scale n < scale k :=
    ((eventually_gt_atTop n).and (hs.eventually (eventually_gt_atTop (scale n)))).exists
  choose next hnext hscale using he
  let u : ℕ → ℕ := Nat.rec n₀ (fun _ k => next k)
  have hu : StrictMono u := strictMono_nat_of_lt_succ fun n => hnext (u n)
  have hv : StrictMono (scale ∘ u) :=
    strictMono_nat_of_lt_succ fun n => hscale (u n)
  refine ⟨u, hu, hv, fun n => hn₀.trans ?_⟩
  exact hv.monotone (Nat.zero_le n)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_BasepointLabelStabilization
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_nonempty _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Removing the basepoint from stabilized labels -/

namespace PolycyclicRecognition

open Filter
open scoped Topology

/-- A label already stable in scale is independent of the center once
nearby-center comparisons hold along all diverging scales. -/
theorem stable_label_independent_of_center
    {P X L : Type} [PseudoMetricSpace X]
    (label : P → X → ℝ → L) {r₀ t η : ℝ} (ht : 0 < t) (hη : 0 < η)
    (hstable : ∀ p x r, r₀ ≤ r → label p x r = label p x r₀)
    (hcompare : ∀ (scale : ℕ → ℝ), Tendsto scale atTop atTop → StrictMono scale →
      (∀ n, 1 ≤ scale n) → (∀ n, 1 ≤ t * scale n) →
      ∀ p x y, (∀ n, dist x y ≤ η * scale n) →
        ∀ᶠ n in atTop, label p x (scale n) = label p y (t * scale n)) :
    ∀ p x y, label p x r₀ = label p y r₀ := by
  intro p x y
  let B := max 1 (max t⁻¹ (dist x y / η))
  let scale := fun n : ℕ => (n : ℝ) + B
  have hlow n : B ≤ scale n := le_add_of_nonneg_left (Nat.cast_nonneg n)
  have hgrow : Tendsto scale atTop atTop := tendsto_atTop_add_const_right _ B
    tendsto_natCast_atTop_atTop
  have hstrict : StrictMono scale := by
    intro i j hij
    have hh : (i : ℝ) < j := by exact_mod_cast hij
    dsimp only [scale]
    linarith only [hh]
  have h1 n : 1 ≤ scale n := (le_max_left _ _).trans (hlow n)
  have ht1 n : 1 ≤ t * scale n := by
    have hh : t⁻¹ ≤ scale n := ((le_max_left _ _).trans (le_max_right _ _)).trans (hlow n)
    have hh' := mul_le_mul_of_nonneg_left hh ht.le
    simpa only [mul_inv_cancel₀ ht.ne'] using hh'
  have hd n : dist x y ≤ η * scale n := by
    have hh : dist x y / η ≤ scale n :=
      ((le_max_right _ _).trans (le_max_right _ _)).trans (hlow n)
    exact (div_le_iff₀ hη).mp hh |>.trans_eq (mul_comm _ _)
  have he := hcompare scale hgrow hstrict h1 ht1 p x y hd
  have hsmall : Tendsto (fun n => t * scale n) atTop atTop := hgrow.const_mul_atTop ht
  obtain ⟨n, hn, hn', heq⟩ := ((hgrow.eventually_ge_atTop r₀).and
    ((hsmall.eventually_ge_atTop r₀).and he)).exists
  exact (hstable p x _ hn).symm.trans (heq.trans (hstable p y _ hn'))

/-- Uniform control in a scale parameter follows from tests along arbitrary
strictly increasing scales, with the same local-distance constraint. -/
theorem uniform_local_norm_bound_of_sequences
    {P X W : Type} [PseudoMetricSpace X] [NormedAddCommGroup W] [NormedSpace ℝ W]
    (error : P → X → X → W) {t η : ℝ} (ht : 0 < t)
    (hseq : ∀ (scale : ℕ → ℝ), Tendsto scale atTop atTop → StrictMono scale →
      (∀ n, 1 ≤ scale n) → (∀ n, 1 ≤ t * scale n) →
      ∀ (p : ℕ → P) (x y : ℕ → X), (∀ n, dist (x n) (y n) ≤ η * scale n) →
      Tendsto (fun n => (scale n)⁻¹ • error (p n) (x n) (y n)) atTop (𝓝 0)) :
    ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 1 ≤ R ∧ ∀ p x y r,
      R ≤ r → dist x y ≤ η * r → ‖error p x y‖ ≤ ε * r := by
  classical
  intro ε hε
  by_contra h
  push Not at h
  have hex (n : ℕ) := h (max 1 (max (n : ℝ) t⁻¹)) (le_max_left _ _)
  choose p x y r hr hd herr using hex
  have hr1 n : 1 ≤ r n := (le_max_left _ _).trans (hr n)
  have htr n : 1 ≤ t * r n := by
    have hh : t⁻¹ ≤ r n := ((le_max_right _ _).trans (le_max_right _ _)).trans (hr n)
    simpa only [mul_inv_cancel₀ ht.ne'] using mul_le_mul_of_nonneg_left hh ht.le
  have hrgrow : Tendsto r atTop atTop := tendsto_atTop_mono
    (fun n => ((le_max_left _ _).trans (le_max_right _ _)).trans (hr n))
    tendsto_natCast_atTop_atTop
  obtain ⟨u, hu, hru, _⟩ := exists_strictMono_scale_subsequence r hrgrow
  have hh := hseq (r ∘ u) (hrgrow.comp hu.tendsto_atTop) hru
    (fun n => hr1 (u n)) (fun n => htr (u n)) (p ∘ u) (x ∘ u) (y ∘ u)
    (fun n => hd (u n))
  obtain ⟨n, hn⟩ := ((tendsto_zero_iff_norm_tendsto_zero.mp hh).eventually
    (gt_mem_nhds hε)).exists
  have hp : 0 < r (u n) := zero_lt_one.trans_le (hr1 (u n))
  have hn' : ‖error (p (u n)) (x (u n)) (y (u n))‖ < ε * r (u n) := by
    have hnorm : ‖error (p (u n)) (x (u n)) (y (u n))‖ / r (u n) < ε := by
      simpa only [Function.comp_apply, norm_smul, Real.norm_eq_abs,
        abs_of_pos (inv_pos.mpr hp), inv_mul_eq_div] using hn
    exact (div_lt_iff₀ hp).mp hnorm
  exact (not_lt_of_ge (herr (u n)).le) hn'

end PolycyclicRecognition

end OAI
end

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
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_RescaledBasisChange
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exponential margins between two rescalings of the same basis -/

namespace PolycyclicRecognition

open Module

variable {L J : Type} [LieRing L] [LieAlgebra ℝ L]

/-- Exact coordinate change between two exponential rescalings. -/
theorem repr_change_exponentialRescaleBasis (b : Basis J ℝ L)
    (s t : J → ℝ) (r : ℝ) (x : L) (j : J) :
    (exponentialRescaleBasis b s r).repr x j =
      (exponentialRescaleBasis b t r).repr x j * Real.exp (r * (t j - s j)) := by
  simp only [exponentialRescaleBasis, Basis.repr_unitsSMul, Units.smul_def,
    Units.val_inv_eq_inv_val, Units.val_mk0, smul_eq_mul, ← Real.exp_neg]
  have he : Real.exp (-(r * t j)) * Real.exp (r * (t j - s j)) =
      Real.exp (-(r * s j)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [mul_right_comm, he]

/-- A common difference between the exponents gives an exponential gain
or loss in the whole coordinate maximum norm. -/
theorem norm_change_exponentialRescaleBasis_le [Fintype J]
    (b : Basis J ℝ L) (s t : J → ℝ) {r α : ℝ} (hr : 0 ≤ r)
    (hgap : ∀ j, t j - s j ≤ α) (x : L) :
    ‖(exponentialRescaleBasis b s r).equivFun x‖ ≤
      Real.exp (r * α) * ‖(exponentialRescaleBasis b t r).equivFun x‖ := by
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg (Real.exp_pos _).le (norm_nonneg _))).mpr
  intro j
  change |(exponentialRescaleBasis b s r).repr x j| ≤ _
  rw [repr_change_exponentialRescaleBasis, abs_mul, abs_of_pos (Real.exp_pos _)]
  calc
    _ ≤ ‖(exponentialRescaleBasis b t r).equivFun x‖ * Real.exp (r * α) :=
      mul_le_mul (norm_le_pi_norm ((exponentialRescaleBasis b t r).equivFun x) j)
        (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (hgap j) hr))
        (Real.exp_pos _).le (norm_nonneg _)
    _ = _ := mul_comm _ _

end PolycyclicRecognition

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_PolynomialChartCoordinates
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.CartanFactorModel.realScaleProfile_apply _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.rightNestedWord_length _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
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
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_WordExponentBounds
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Positive common widths for a finite bracket-word list -/

namespace PolycyclicRecognition

open scoped BigOperators

variable {I : Type} [Fintype I] [DecidableEq I]

/-- Every nonempty bracket word has strictly positive width if the letters do. -/
theorem bracketWordExponent_pos (s : I → ℝ) (hs : ∀ i, 0 < s i)
    (w : FreeMagma I) : 0 < bracketWordExponent s w := by
  induction w using FreeMagma.rec with
  | of i => simpa only [bracketWordExponent_of] using hs i
  | mul u v hu hv =>
    change 0 < bracketWordExponent s (u * v)
    rw [bracketWordExponent_mul]
    exact add_pos hu hv

end PolycyclicRecognition

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_FiniteAffineSelection
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instNonemptyBases _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_nonempty _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Canonical finite labels and separation from translated competitors -/

noncomputable section
namespace PolycyclicRecognition

open Filter Set
open scoped Topology

theorem minimizingFiniteLabel_le {L : Type} [Fintype L] [Nonempty L]
    (cost : L → ℝ) (a : L) : cost (minimizingFiniteLabel cost) ≤ cost a :=
  (Finset.exists_min_image Finset.univ cost Finset.univ_nonempty).choose_spec.2 a
    (Finset.mem_univ a)

/-- The canonical choices inherit any vanishing competitor bound. -/
theorem minimizingFiniteLabel_tendsto_zero
    {L : Type} [Fintype L] [Nonempty L] (cost : ℕ → L → ℝ)
    (hnonneg : ∀ n a, 0 ≤ cost n a)
    (a : ℕ → L) (ha : Tendsto (fun n => cost n (a n)) atTop (𝓝 0)) :
    Tendsto (fun n => cost n (minimizingFiniteLabel (cost n))) atTop (𝓝 0) :=
  squeeze_zero (fun n => hnonneg n _) (fun n => minimizingFiniteLabel_le (cost n) (a n)) ha

/-- Subtracting the value at the identity costs at most a factor of two
in the uniform norm. This removes arbitrary offsets from a comparison. -/
theorem linear_profile_distance_le_twice_affine
    {Z W : Type} [TopologicalSpace Z] [CompactSpace Z] [NormedAddCommGroup W]
    (A B : C(Z, W)) (z₀ : Z) (hA : A z₀ = 0) (hB : B z₀ = 0) (b c : W) :
    dist A B ≤ 2 * dist (A + ContinuousMap.const Z b) (B + ContinuousMap.const Z c) := by
  let D := dist (A + ContinuousMap.const Z b) (B + ContinuousMap.const Z c)
  have hoff : dist b c ≤ D := by
    simpa only [ContinuousMap.add_apply, ContinuousMap.const_apply, hA, hB, zero_add] using
      (A + ContinuousMap.const Z b).dist_apply_le_dist
        (g := B + ContinuousMap.const Z c) z₀
  apply (ContinuousMap.dist_le (mul_nonneg (by norm_num) dist_nonneg)).mpr
  intro z
  have hpoint : dist (A z + b) (B z + c) ≤ D :=
    (A + ContinuousMap.const Z b).dist_apply_le_dist
      (g := B + ContinuousMap.const Z c) z
  calc
    dist (A z) (B z) = dist (A z + b) (B z + b) := (dist_add_right _ _ _).symm
    _ ≤ dist (A z + b) (B z + c) + dist (B z + c) (B z + b) := dist_triangle _ _ _
    _ = dist (A z + b) (B z + c) + dist b c := by rw [dist_add_left, dist_comm c b]
    _ ≤ D + D := add_le_add hpoint hoff
    _ = 2 * D := by ring

/-- Finitely many distinct centered profiles have a uniform positive
separation, even after arbitrary offsets are added. -/
theorem exists_finite_affine_label_separation
    {Z W L : Type} [TopologicalSpace Z] [CompactSpace Z] [NormedAddCommGroup W]
    [Fintype L] [Nonempty L] (A : L → C(Z, W)) (hA : Function.Injective A)
    (z₀ : Z) (hzero : ∀ a, A a z₀ = 0) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ a a' b b',
      dist (A a + ContinuousMap.const Z b) (A a' + ContinuousMap.const Z b') < ε → a = a' := by
  classical
  let cost : L × L → ℝ := fun p => if p.1 = p.2 then 1 else dist (A p.1) (A p.2) / 3
  have hpos p : 0 < cost p := by
    dsimp only [cost]
    split_ifs with h
    · exact zero_lt_one
    · exact div_pos (dist_pos.mpr (fun he => h (hA he))) (by norm_num)
  let p := minimizingFiniteLabel cost
  refine ⟨cost p, hpos p, ?_⟩
  intro a a' b b' hd
  by_contra hne
  have hmin := minimizingFiniteLabel_le cost (a, a')
  have hdist := linear_profile_distance_le_twice_affine (A a) (A a') z₀
    (hzero a) (hzero a') b b'
  have he : cost (a, a') = dist (A a) (A a') / 3 := by simp [cost, hne]
  have hposdist : 0 < dist (A a) (A a') := dist_pos.mpr (fun h => hne (hA h))
  change cost p ≤ cost (a, a') at hmin
  rw [he] at hmin
  linarith

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_MeanProbabilityConverse
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Mean error implies convergence in probability -/

namespace PolycyclicRecognition

open MeasureTheory Filter Set
open scoped Topology ENNReal

/-- Markov's inequality gives the probability direction for an integrable
nonnegative profile error, without a global bound off its sampling cell. -/
theorem bad_probability_tendsto_zero_of_mean
    {X : Type} [MeasurableSpace X] (μ : ℕ → ProbabilityMeasure X)
    (f : ℕ → X → ℝ) (hi : ∀ n, Integrable (f n) (μ n : Measure X))
    (hf : ∀ n, 0 ≤ᵐ[(μ n : Measure X)] f n)
    (hm : Tendsto (fun n => ∫ x, f n x ∂(μ n : Measure X)) atTop (𝓝 0))
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n => (μ n : Measure X) {x | ε ≤ f n x}) atTop (𝓝 0) := by
  have hbound n : ((μ n : Measure X) {x | ε ≤ f n x}).toReal ≤
      (∫ x, f n x ∂(μ n : Measure X)) / ε := by
    apply (le_div_iff₀ hε).mpr
    simpa only [measureReal_def, mul_comm] using
      mul_meas_ge_le_integral_of_nonneg (hf n) (hi n) ε
  have hreal : Tendsto (fun n => ((μ n : Measure X) {x | ε ≤ f n x}).toReal) atTop (𝓝 0) :=
    squeeze_zero (fun _ => ENNReal.toReal_nonneg) hbound (by simpa using hm.div_const ε)
  simpa only [ENNReal.ofReal_toReal (measure_ne_top _ _), ENNReal.ofReal_zero] using
    ENNReal.tendsto_ofReal hreal

end PolycyclicRecognition

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_CompactSamplingMean
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Canonical affine choices for compactly carried sampling laws -/

noncomputable section
namespace PolycyclicRecognition

open MeasureTheory Filter Set
open scoped Topology

theorem integrable_continuous_of_ae_mem_compact
    {X E : Type} [TopologicalSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X]
    [NormedAddCommGroup E] (μ : Measure X) [IsFiniteMeasure μ]
    {C : Set X} (hC : IsCompact C) (hfull : ∀ᵐ x ∂μ, x ∈ C)
    {f : X → E} (hf : Continuous f) : Integrable f μ := by
  have hi := hf.continuousOn.integrableOn_compact (μ := μ) hC
  rwa [IntegrableOn, Measure.restrict_eq_self_of_ae_mem hfull] at hi

theorem canonicalAffineLabel_mean_tendsto_zero
    {X Y L : Type} [MeasurableSpace X] [PseudoMetricSpace Y]
    [Finite L] [Nonempty L]
    (μ : ℕ → Measure X) (f : ℕ → X → Y) (A : ℕ → L → Y)
    (h : ∃ a : ℕ → L, Tendsto (fun n => ∫ x, dist (f n x) (A n (a n)) ∂μ n)
      atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x,
      dist (f n x) (A n (canonicalAffineLabel (μ n) (f n) (A n))) ∂μ n)
      atTop (𝓝 0) := by
  obtain ⟨a, ha⟩ := h
  let : Fintype L := Fintype.ofFinite L
  exact minimizingFiniteLabel_tendsto_zero
    (fun n a => ∫ x, dist (f n x) (A n a) ∂μ n)
    (fun _ _ => integral_nonneg (fun _ => dist_nonneg)) a ha

/-- Compact support supplies the integrability required by Markov's
inequality, including for the canonical minimizing affine label. -/
theorem compact_profile_probability_of_mean
    {X Y : Type} [TopologicalSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X]
    [PseudoMetricSpace Y]
    (μ : ℕ → ProbabilityMeasure X) (C : ℕ → Set X)
    (hC : ∀ n, IsCompact (C n)) (hfull : ∀ n, ∀ᵐ x ∂(μ n : Measure X), x ∈ C n)
    (f : ℕ → X → Y) (hf : ∀ n, Continuous (f n)) (a : ℕ → Y)
    (hm : Tendsto (fun n => ∫ x, dist (f n x) (a n) ∂(μ n : Measure X)) atTop (𝓝 0))
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n => (μ n : Measure X) {x | ε ≤ dist (f n x) (a n)})
      atTop (𝓝 0) :=
  bad_probability_tendsto_zero_of_mean μ _
    (fun n => integrable_continuous_of_ae_mem_compact (μ n : Measure X) (hC n) (hfull n)
      ((hf n).dist continuous_const))
    (fun _ => Eventually.of_forall (fun _ => dist_nonneg)) hm hε

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_ThreeProbeConcentration
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Joint concentration of the three actual probe chains -/

noncomputable section
namespace PolycyclicRecognition

open MeasureTheory Filter Set
open scoped Topology ENNReal

/-- Concentration is transitive through the measured anchor profile. -/
theorem bad_distance_triangle_tendsto_zero
    {X S : Type} [MeasurableSpace X] [PseudoMetricSpace S]
    (μ : ℕ → Measure X) (f g h : ℕ → X → S)
    (hfg : ∀ ε : ℝ, 0 < ε →
      Tendsto (fun n => μ n {x | ε ≤ dist (f n x) (g n x)}) atTop (𝓝 0))
    (hgh : ∀ ε : ℝ, 0 < ε →
      Tendsto (fun n => μ n {x | ε ≤ dist (g n x) (h n x)}) atTop (𝓝 0))
    (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun n => μ n {x | ε ≤ dist (f n x) (h n x)}) atTop (𝓝 0) := by
  have hb (n : ℕ) : μ n {x | ε ≤ dist (f n x) (h n x)} ≤
      μ n {x | ε / 2 ≤ dist (f n x) (g n x)} +
        μ n {x | ε / 2 ≤ dist (g n x) (h n x)} := by
    apply (measure_mono (fun x hx => ?_)).trans (measure_union_le _ _)
    by_cases hf : ε / 2 ≤ dist (f n x) (g n x)
    · exact Or.inl hf
    · right
      have hh := dist_triangle (f n x) (g n x) (h n x)
      have hx' : ε ≤ dist (f n x) (h n x) := hx
      change ε / 2 ≤ dist (g n x) (h n x)
      linarith [lt_of_not_ge hf]
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le
    (g := fun _ : ℕ => (0 : ℝ≥0∞)) tendsto_const_nhds _ (fun _ => zero_le) hb
  simpa only [zero_add] using (hfg (ε / 2) (half_pos hε)).add (hgh (ε / 2) (half_pos hε))

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_DeterministicProbabilityComparison
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Deterministic affine comparisons extracted from probable comparisons -/

namespace PolycyclicRecognition

open MeasureTheory Filter Set
open scoped Topology ENNReal

/-- A constant event cannot have vanishing positive probability unless
its deterministic error tends to zero. -/
theorem deterministic_distance_tendsto_zero_of_probability
    {X Y : Type} [MeasurableSpace X] [PseudoMetricSpace Y]
    (μ : ℕ → ProbabilityMeasure X) (a b : ℕ → Y)
    (hp : ∀ ε : ℝ, 0 < ε → Tendsto (fun n =>
      (μ n : Measure X) {_x | ε ≤ dist (a n) (b n)}) atTop (𝓝 0)) :
    Tendsto (fun n => dist (a n) (b n)) atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hh := (hp ε hε).eventually (gt_mem_nhds (by norm_num : (0 : ℝ≥0∞) < 1))
  filter_upwards [hh] with n hn
  rw [Real.dist_eq, sub_zero, abs_of_nonneg dist_nonneg]
  by_contra h
  have he : {x : X | ε ≤ dist (a n) (b n)} = univ := by
    ext x
    simp only [mem_ofPred_eq, mem_univ, iff_true]
    exact le_of_not_gt h
  rw [he, measure_univ] at hn
  exact (lt_irrefl (1 : ℝ≥0∞)) hn

/-- Two deterministic approximants agree asymptotically when their
sampled profiles can be compared on a common probability law. -/
theorem deterministic_distance_tendsto_zero_of_coupled_profiles
    {X Y : Type} [MeasurableSpace X] [PseudoMetricSpace Y]
    (μ : ℕ → ProbabilityMeasure X) (a b : ℕ → Y) (f g : ℕ → X → Y)
    (hleft : ∀ ε : ℝ, 0 < ε → Tendsto (fun n =>
      (μ n : Measure X) {x | ε ≤ dist (a n) (f n x)}) atTop (𝓝 0))
    (hpair : ∀ ε : ℝ, 0 < ε → Tendsto (fun n =>
      (μ n : Measure X) {x | ε ≤ dist (f n x) (g n x)}) atTop (𝓝 0))
    (hright : ∀ ε : ℝ, 0 < ε → Tendsto (fun n =>
      (μ n : Measure X) {x | ε ≤ dist (g n x) (b n)}) atTop (𝓝 0)) :
    Tendsto (fun n => dist (a n) (b n)) atTop (𝓝 0) := by
  apply deterministic_distance_tendsto_zero_of_probability μ a b
  intro ε hε
  apply bad_distance_triangle_tendsto_zero (fun n => (μ n : Measure X))
    (fun n _ => a n) g (fun n _ => b n) _ hright ε hε
  exact fun η hη => bad_distance_triangle_tendsto_zero (fun n => (μ n : Measure X))
    (fun n _ => a n) f g hleft hpair η hη

end PolycyclicRecognition

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_RescaledAffineComparison
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Deterministic comparison through a change of scale

Two ordinary sampling laws need not agree. Their mixed comparison and the
exact change of coordinates suffice to compare the deterministic affine
approximations. Finite separation then identifies their linear parts.
-/

noncomputable section
namespace PolycyclicRecognition

open MeasureTheory Filter Set
open scoped Topology ENNReal

theorem bad_probability_tendsto_zero_of_dist_le
    {X Y Z : Type} [MeasurableSpace X] [PseudoMetricSpace Y] [PseudoMetricSpace Z]
    (μ : ℕ → Measure X) (f g : ℕ → X → Y) (u v : ℕ → X → Z)
    {K : ℝ} (hK : 0 < K)
    (hbound : ∀ n x, dist (u n x) (v n x) ≤ K * dist (f n x) (g n x))
    (hp : ∀ ε : ℝ, 0 < ε → Tendsto (fun n =>
      μ n {x | ε ≤ dist (f n x) (g n x)}) atTop (𝓝 0))
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n => μ n {x | ε ≤ dist (u n x) (v n x)}) atTop (𝓝 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le
    (g := fun _ : ℕ => (0 : ℝ≥0∞)) tendsto_const_nhds
    (hp (ε / K) (div_pos hε hK)) (fun _ => zero_le)
  intro n
  apply measure_mono
  intro x hx
  exact (div_le_iff₀ hK).mpr (by simpa only [mul_comm] using hx.trans (hbound n x))

/-- A mixed sampling comparison transports deterministic approximants
through any uniformly Lipschitz exact change of coordinates. -/
theorem deterministic_distance_tendsto_zero_of_rescaled_profiles
    {X Y : Type} [MeasurableSpace X] [PseudoMetricSpace Y]
    (μ ν : ℕ → ProbabilityMeasure X) (a b : ℕ → Y)
    (f g : ℕ → X → Y) (H : ℕ → Y → Y) {K : ℝ} (hK : 0 < K)
    (hH : ∀ n u v, dist (H n u) (H n v) ≤ K * dist u v)
    (hmatch : ∀ n x, f n x = H n (g n x))
    (hleft : ∀ ε : ℝ, 0 < ε → Tendsto (fun n =>
      (μ n : Measure X) {x | ε ≤ dist (a n) (f n x)}) atTop (𝓝 0))
    (hpair : ∀ ε : ℝ, 0 < ε → Tendsto (fun n =>
      (μ n : Measure X).prod (ν n : Measure X)
        {p | ε ≤ dist (f n p.1) (f n p.2)}) atTop (𝓝 0))
    (hright : ∀ ε : ℝ, 0 < ε → Tendsto (fun n =>
      (ν n : Measure X) {x | ε ≤ dist (g n x) (b n)}) atTop (𝓝 0)) :
    Tendsto (fun n => dist (a n) (H n (b n))) atTop (𝓝 0) := by
  let ρ n : ProbabilityMeasure (X × X) :=
    ⟨(μ n : Measure X).prod (ν n : Measure X), (by first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability))⟩
  apply deterministic_distance_tendsto_zero_of_coupled_profiles ρ a (fun n => H n (b n))
    (fun n p => f n p.1) (fun n p => f n p.2)
  · intro ε hε
    change Tendsto (fun n => (μ n : Measure X).prod (ν n : Measure X)
      {p | ε ≤ dist (a n) (f n p.1)}) atTop (𝓝 0)
    have he n : {p : X × X | ε ≤ dist (a n) (f n p.1)} =
        {x | ε ≤ dist (a n) (f n x)} ×ˢ univ := by ext p; simp
    simpa only [he, Measure.prod_prod, measure_univ, mul_one] using hleft ε hε
  · exact hpair
  · intro ε hε
    change Tendsto (fun n => (μ n : Measure X).prod (ν n : Measure X)
      {p | ε ≤ dist (f n p.2) (H n (b n))}) atTop (𝓝 0)
    have hh := bad_probability_tendsto_zero_of_dist_le
      (fun n => (ν n : Measure X)) g (fun n _ => b n)
      f (fun n _ => H n (b n)) hK
      (fun n x => by rw [hmatch n x]; exact hH n _ _) hright hε
    have he n : {p : X × X | ε ≤ dist (f n p.2) (H n (b n))} =
        univ ×ˢ {x | ε ≤ dist (f n x) (H n (b n))} := by ext p; simp
    simpa only [he, Measure.prod_prod, measure_univ, one_mul] using hh

theorem dist_rescaleCompactProfile_le
    {Z W : Type} [TopologicalSpace Z] [CompactSpace Z]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (t : ℝ) (φ : C(Z, Z)) (f g : C(Z, W)) :
    dist (rescaleCompactProfile t φ f) (rescaleCompactProfile t φ g) ≤
      |t| * dist f g := by
  apply (ContinuousMap.dist_le (mul_nonneg (abs_nonneg _) dist_nonneg)).mpr
  intro z
  change dist (t • f (φ z)) (t • g (φ z)) ≤ _
  rw [dist_smul₀, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (f.dist_apply_le_dist (g := g) (φ z)) (abs_nonneg _)

/-- A linear profile transforms exactly; only its constant offset changes. -/
theorem rescaleCompactProfile_affine
    {Z W : Type} [TopologicalSpace Z] [CompactSpace Z]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (t : ℝ) (φ : C(Z, Z)) (A : C(Z, W)) (b : W)
    (hA : ∀ z, t • A (φ z) = A z) :
    rescaleCompactProfile t φ (A + ContinuousMap.const Z b) =
      A + ContinuousMap.const Z (t • b) := by
  ext z
  change t • (A (φ z) + b) = A z + t • b
  rw [smul_add, hA]

/-- Vanishing affine discrepancy identifies finite labels and their offsets. -/
theorem affine_labels_and_offsets_of_distance_tendsto_zero
    {Z W L : Type} [TopologicalSpace Z] [CompactSpace Z]
    [NormedAddCommGroup W] [Fintype L] [Nonempty L]
    (A : L → C(Z, W)) (hA : Function.Injective A)
    (z₀ : Z) (hzero : ∀ a, A a z₀ = 0)
    (a a' : ℕ → L) (b b' : ℕ → W)
    (hd : Tendsto (fun n => dist (A (a n) + ContinuousMap.const Z (b n))
      (A (a' n) + ContinuousMap.const Z (b' n))) atTop (𝓝 0)) :
    (∀ᶠ n in atTop, a n = a' n) ∧
      Tendsto (fun n => dist (b n) (b' n)) atTop (𝓝 0) := by
  obtain ⟨ε, hε, hsep⟩ := exists_finite_affine_label_separation A hA z₀ hzero
  constructor
  · filter_upwards [hd.eventually (gt_mem_nhds hε)] with n hn
    exact hsep _ _ _ _ hn
  · apply squeeze_zero (fun _ => dist_nonneg) _ hd
    intro n
    simpa only [ContinuousMap.add_apply, ContinuousMap.const_apply, hzero, zero_add] using
      (A (a n) + ContinuousMap.const Z (b n)).dist_apply_le_dist
        (g := A (a' n) + ContinuousMap.const Z (b' n)) z₀

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_AffineScaleStabilization
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Stabilization of affine approximations across comparable scales -/

noncomputable section
namespace PolycyclicRecognition

open MeasureTheory Filter Set
open scoped Topology

/-- Mixed concentration and the exact chart transition stabilize the finite
labels. The offsets are compared in the physical source-scale normalization. -/
theorem affine_scale_labels_and_offsets
    {X Z W L : Type} [TopologicalSpace X] [T2Space X]
    [MeasurableSpace X] [BorelSpace X] [TopologicalSpace Z] [CompactSpace Z]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [Fintype L] [Nonempty L]
    (μ ν : ℕ → ProbabilityMeasure X) (C D : ℕ → Set X)
    (hC : ∀ n, IsCompact (C n)) (hD : ∀ n, IsCompact (D n))
    (hμ : ∀ n, ∀ᵐ x ∂(μ n : Measure X), x ∈ C n)
    (hν : ∀ n, ∀ᵐ x ∂(ν n : Measure X), x ∈ D n)
    (f g : ℕ → X → C(Z, W)) (hf : ∀ n, Continuous (f n)) (hg : ∀ n, Continuous (g n))
    (t : ℕ → ℝ) (φ : ℕ → C(Z, Z)) {K : ℝ} (hK : 0 < K)
    (ht : ∀ n, |t n| ≤ K)
    (hmatch : ∀ n x, f n x = rescaleCompactProfile (t n) (φ n) (g n x))
    (A : L → C(Z, W)) (hA : Function.Injective A)
    (z₀ : Z) (hzero : ∀ a, A a z₀ = 0)
    (htransition : ∀ n a z, t n • A a (φ n z) = A a z)
    (a a' : ℕ → L) (b b' : ℕ → W)
    (hleft : Tendsto (fun n => ∫ x, dist (f n x)
      (A (a n) + ContinuousMap.const Z (b n)) ∂(μ n : Measure X)) atTop (𝓝 0))
    (hright : Tendsto (fun n => ∫ x, dist (g n x)
      (A (a' n) + ContinuousMap.const Z (b' n)) ∂(ν n : Measure X)) atTop (𝓝 0))
    (hpair : ∀ ε : ℝ, 0 < ε → Tendsto (fun n =>
      (μ n : Measure X).prod (ν n : Measure X)
        {p | ε ≤ dist (f n p.1) (f n p.2)}) atTop (𝓝 0)) :
    (∀ᶠ n in atTop, a n = a' n) ∧
      Tendsto (fun n => dist (b n) (t n • b' n)) atTop (𝓝 0) := by
  have hd := deterministic_distance_tendsto_zero_of_rescaled_profiles μ ν
    (fun n => A (a n) + ContinuousMap.const Z (b n))
    (fun n => A (a' n) + ContinuousMap.const Z (b' n)) f g
    (fun n => rescaleCompactProfile (t n) (φ n)) hK
    (fun n u v => (dist_rescaleCompactProfile_le _ _ _ _).trans
      (mul_le_mul_of_nonneg_right (ht n) dist_nonneg)) hmatch
    (fun ε hε => by
      simpa only [dist_comm] using
        compact_profile_probability_of_mean μ C hC hμ f hf _ hleft hε)
    hpair
    (fun ε hε => compact_profile_probability_of_mean ν D hD hν g hg _ hright hε)
  have he n := rescaleCompactProfile_affine (t n) (φ n) (A (a' n)) (b' n)
    (htransition n (a' n))
  simp_rw [he] at hd
  exact affine_labels_and_offsets_of_distance_tendsto_zero A hA z₀ hzero a a' b _ hd

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_NormalizedCellDomination
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Domination of normalized cell laws under Haar-preserving maps -/

namespace PolycyclicRecognition

open MeasureTheory Set
open scoped ENNReal

/-- If the inverse image of the smaller cell lies in the sampling cell,
the pushed normalized sampling law dominates its normalized restriction.
The loss is exactly the ratio of the two Haar volumes. -/
theorem normalized_cell_transport_domination
    {X : Type} [MeasurableSpace X] (μ : Measure X)
    (C D : Set X) (hC : MeasurableSet C)
    (hC0 : μ C ≠ 0) (hCfin : μ C ≠ ∞)
    (hD0 : μ D ≠ 0) (hDfin : μ D ≠ ∞)
    (τ : X → X) (hτ : MeasurePreserving τ μ μ)
    (hcover : τ ⁻¹' C ⊆ D)
    (S : Set X) (hS : MeasurableSet S) :
    (cellProbabilityMeasure μ C hC0 hCfin : Measure X) S ≤
      (μ D / μ C) * (cellProbabilityMeasure μ D hD0 hDfin : Measure X) (τ ⁻¹' S) := by
  have hm : μ (S ∩ C) ≤ μ (τ ⁻¹' S ∩ D) := calc
    μ (S ∩ C) = μ (τ ⁻¹' (S ∩ C)) :=
      (hτ.measure_preimage (hS.inter hC).nullMeasurableSet).symm
    _ ≤ μ (τ ⁻¹' S ∩ D) := measure_mono (fun _ hx => ⟨hx.1, hcover hx.2⟩)
  change (((μ C)⁻¹ • μ.restrict C) S) ≤
    (μ D / μ C) * (((μ D)⁻¹ • μ.restrict D) (τ ⁻¹' S))
  rw [Measure.smul_apply, Measure.smul_apply, Measure.restrict_apply hS,
    Measure.restrict_apply (hτ.measurable hS)]
  change (μ C)⁻¹ * μ (S ∩ C) ≤
    (μ D / μ C) * ((μ D)⁻¹ * μ (τ ⁻¹' S ∩ D))
  calc
    _ ≤ (μ C)⁻¹ * μ (τ ⁻¹' S ∩ D) := mul_le_mul' le_rfl hm
    _ = _ := by
      rw [div_eq_mul_inv]
      have he : μ D * (μ C)⁻¹ * ((μ D)⁻¹ * μ (τ ⁻¹' S ∩ D)) =
          (μ C)⁻¹ * (μ D * (μ D)⁻¹) * μ (τ ⁻¹' S ∩ D) := by ac_rfl
      rw [he, ENNReal.mul_inv_cancel hD0 hDfin, mul_one]

end PolycyclicRecognition

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_DifferentCellDomination
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Density comparison with different starting and target cells -/

namespace PolycyclicRecognition

open MeasureTheory Set
open scoped ENNReal

/-- The starting law is arbitrary. Only the target-to-suffix volume ratio
enters the domination constant, including when the two scales differ. -/
theorem different_cell_pair_domination
    {X Y : Type} [MeasurableSpace X] [MeasurableSpace Y]
    (ν : ProbabilityMeasure X) (A : Set X)
    (hA : ∀ᵐ a ∂(ν : Measure X), a ∈ A)
    (μ : Measure Y) (C D : Set Y) (hC : MeasurableSet C)
    (hC0 : μ C ≠ 0) (hCfin : μ C ≠ ∞) (hD0 : μ D ≠ 0) (hDfin : μ D ≠ ∞)
    (τ : X → Y → Y)
    (hτ : ∀ a ∈ A, MeasurePreserving (τ a) μ μ)
    (hcover : ∀ a ∈ A, (τ a) ⁻¹' C ⊆ D)
    (hpair : Measurable (fun p : X × Y => (p.1, τ p.1 p.2)))
    (B : Set (X × Y)) (hB : MeasurableSet B) :
    (ν : Measure X).prod (cellProbabilityMeasure μ C hC0 hCfin : Measure Y) B ≤
      (μ D / μ C) * (ν : Measure X).prod
        (cellProbabilityMeasure μ D hD0 hDfin : Measure Y)
        ((fun p : X × Y => (p.1, τ p.1 p.2)) ⁻¹' B) := by
  let P := (fun p : X × Y => (p.1, τ p.1 p.2)) ⁻¹' B
  have hP : MeasurableSet P := hpair hB
  rw [Measure.prod_apply hB, Measure.prod_apply hP]
  calc
    _ ≤ ∫⁻ a, (μ D / μ C) *
        (cellProbabilityMeasure μ D hD0 hDfin : Measure Y) (Prod.mk a ⁻¹' P)
        ∂(ν : Measure X) := by
      apply lintegral_mono_ae
      filter_upwards [hA] with a ha
      exact normalized_cell_transport_domination μ C D hC hC0 hCfin hD0 hDfin
        (τ a) (hτ a ha) (hcover a ha) (Prod.mk a ⁻¹' B)
        ((measurable_const.prodMk measurable_id) hB)
    _ = _ := lintegral_const_mul _ (measurable_measure_prodMk_left hP)

end PolycyclicRecognition

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_IndependentSupportedSampling
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Independent suffix laws carried by the permitted boxes -/

noncomputable section
namespace PolycyclicRecognition

open MeasureTheory Filter Set
open scoped Topology ENNReal

/-- Sequential concentration for every permitted deterministic suffix
implies concentration for any independent laws carried by those sets. -/
theorem independent_supported_bad_probability_tendsto_zero
    {A K : ℕ → Type} [∀ n, MeasurableSpace (A n)] [∀ n, MeasurableSpace (K n)]
    (μ : ∀ n, ProbabilityMeasure (A n)) (ν : ∀ n, ProbabilityMeasure (K n))
    (D : ∀ n, Set (K n)) (hne : ∀ n, (D n).Nonempty)
    (hcarried : ∀ n, ∀ᵐ k ∂(ν n : Measure (K n)), k ∈ D n)
    (B : ∀ n, Set (A n × K n)) (hB : ∀ n, MeasurableSet (B n))
    (hp : ∀ k : ∀ n, K n, (∀ n, k n ∈ D n) →
      Tendsto (fun n => (μ n : Measure (A n)) ((fun a => (a, k n)) ⁻¹' B n))
        atTop (𝓝 0)) :
    Tendsto (fun n => (μ n : Measure (A n)).prod (ν n : Measure (K n)) (B n))
      atTop (𝓝 0) := by
  let : ∀ n, Nonempty (D n) := fun n => (hne n).to_subtype
  apply tendsto_order.mpr
  constructor
  · intro c hc
    exact False.elim ((not_lt_of_ge bot_le) hc)
  · intro c hc
    obtain ⟨d, hd0, hdc⟩ := exists_between hc
    have hb := eventually_uniform_lt_of_all_selections
      (fun n (k : D n) => (μ n : Measure (A n)) ((fun a => (a, k.val)) ⁻¹' B n))
      (fun k => hp (fun n => (k n).val) (fun n => (k n).property)) hd0
    filter_upwards [hb] with n hn
    apply lt_of_le_of_lt _ hdc
    rw [Measure.prod_apply_symm (hB n)]
    calc
      _ ≤ ∫⁻ _, d ∂(ν n : Measure (K n)) := by
        apply lintegral_mono_ae
        filter_upwards [hcarried n] with k hk
        exact (hn ⟨k, hk⟩).le
      _ = d := by simp

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_LinearProfilesOnBall
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite linear profiles tested on one fixed ball -/

noncomputable section
namespace PolycyclicRecognition

open Set

variable {V W : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

theorem linearMap_eq_of_eqOn_closedBall {R : ℝ} (hR : 0 < R)
    (f g : V →ₗ[ℝ] W) (h : EqOn f g (Metric.closedBall 0 R)) : f = g := by
  ext x
  let c := R / (‖x‖ + 1)
  have hc : 0 < c := div_pos hR (by positivity)
  have hx : c • x ∈ Metric.closedBall 0 R := by
    rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos hc]
    calc
      c * ‖x‖ ≤ c * (‖x‖ + 1) := mul_le_mul_of_nonneg_left (by linarith) hc.le
      _ = R := div_mul_cancel₀ _ (by positivity)
  have hh := h hx
  rw [map_smul, map_smul] at hh
  exact smul_right_injective W hc.ne' hh

theorem linearBallProfile_injective (q : V →L[ℝ] W) (hq : Function.Surjective q)
    {R : ℝ} (hR : 0 < R) : Function.Injective (fun A => linearBallProfile q A R) := by
  intro A B h
  have he : A.toLinearMap.comp q.toLinearMap = B.toLinearMap.comp q.toLinearMap :=
    linearMap_eq_of_eqOn_closedBall hR _ _ (fun z hz =>
      congrArg (fun f : C(Metric.closedBall (0 : V) R, W) => f ⟨z, hz⟩) h)
  ext w
  obtain ⟨v, rfl⟩ := hq w
  exact DFunLike.congr_fun he v

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_MixedCellConcentration
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Comparison of independently sampled cells at distinct scales -/

noncomputable section
namespace PolycyclicRecognition

open MeasureTheory Filter Set
open scoped Topology ENNReal

/-- A difference cover with bounded target volume ratio passes suffix
concentration to independent samples from two possibly different cells. -/
theorem mixed_cell_concentration
    {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul₂ G]
    (μ : Measure G) [μ.IsMulLeftInvariant]
    (A C D : ℕ → Set G) (hA : ∀ n, MeasurableSet (A n))
    (hC : ∀ n, MeasurableSet (C n)) (hD : ∀ n, MeasurableSet (D n))
    (hA0 : ∀ n, μ (A n) ≠ 0) (hAfin : ∀ n, μ (A n) ≠ ∞)
    (hC0 : ∀ n, μ (C n) ≠ 0) (hCfin : ∀ n, μ (C n) ≠ ∞)
    (hD0 : ∀ n, μ (D n) ≠ 0) (hDfin : ∀ n, μ (D n) ≠ ∞)
    (hcover : ∀ n a, a ∈ A n → ∀ b ∈ C n, a⁻¹ * b ∈ D n)
    {K : ℝ≥0∞} (hK : K ≠ ∞) (hratio : ∀ n, μ (D n) / μ (C n) ≤ K)
    (B : ℕ → Set (G × G)) (hB : ∀ n, MeasurableSet (B n))
    (hp : ∀ k : ℕ → G, (∀ n, k n ∈ D n) →
      Tendsto (fun n => (cellProbabilityMeasure μ (A n) (hA0 n) (hAfin n) : Measure G)
        {a | (a, a * k n) ∈ B n}) atTop (𝓝 0)) :
    Tendsto (fun n => (cellProbabilityMeasure μ (A n) (hA0 n) (hAfin n) : Measure G).prod
      (cellProbabilityMeasure μ (C n) (hC0 n) (hCfin n) : Measure G) (B n))
      atTop (𝓝 0) := by
  let μA n := cellProbabilityMeasure μ (A n) (hA0 n) (hAfin n)
  let μD n := cellProbabilityMeasure μ (D n) (hD0 n) (hDfin n)
  let P n := (fun p : G × G => (p.1, p.1 * p.2)) ⁻¹' B n
  have hmap : Measurable (fun p : G × G => (p.1, p.1 * p.2)) :=
    measurable_fst.prodMk (measurable_fst.mul measurable_snd)
  have hprob := independent_supported_bad_probability_tendsto_zero μA μD D
    (fun n => nonempty_of_measure_ne_zero (hD0 n))
    (fun n => ae_mem_cellProbabilityMeasure μ (D n) (hD n) (hD0 n) (hDfin n))
    P (fun n => hmap (hB n)) hp
  have hbound n := different_cell_pair_domination (μA n) (A n)
    (ae_mem_cellProbabilityMeasure μ (A n) (hA n) (hA0 n) (hAfin n))
    μ (C n) (D n) (hC n) (hC0 n) (hCfin n) (hD0 n) (hDfin n)
    (fun a k => a * k) (fun a _ => measurePreserving_mul_left μ a) (by
      intro a ha k hk
      have hb : a * k ∈ C n := hk
      simpa only [inv_mul_cancel_left] using hcover n a ha (a * k) hb)
    hmap (B n) (hB n)
  have hlim := ENNReal.Tendsto.const_mul hprob (Or.inr hK)
  simp only [mul_zero] at hlim
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
    (fun _ => bot_le)
  intro n
  exact (hbound n).trans (mul_le_mul' (hratio n) le_rfl)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_MixedScaleBasisBound
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Coordinate comparison from the actual exponential widths -/

namespace PolycyclicRecognition
open Module

/-- Only the products of physical scale and word cost matter for a box. -/
theorem norm_exponentialRescaleBasis_le_of_exponents_le
    {L J : Type} [LieRing L] [LieAlgebra ℝ L] [Fintype J]
    (b : Basis J ℝ L) (u v : J → ℝ) (r t : ℝ)
    (h : ∀ j, t * v j ≤ r * u j) (x : L) :
    ‖(exponentialRescaleBasis b u r).equivFun x‖ ≤
      ‖(exponentialRescaleBasis b v t).equivFun x‖ := by
  have hh := norm_change_exponentialRescaleBasis_le b (fun j => r * u j)
    (fun j => t * v j) zero_le_one (α := 0)
    (fun j => sub_nonpos.mpr (h j)) x
  simpa only [exponentialRescaleBasis, one_mul, mul_zero, Real.exp_zero] using hh

end PolycyclicRecognition

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_ProfilePointwiseBounds
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Anchor bounds and compact containment for sampled map profiles -/

noncomputable section

namespace PolycyclicRecognition

open Set
open scoped NNReal

variable {G W Z : Type} [Group G] [PseudoMetricSpace G] [IsIsometricSMul G G]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [Zero Z]

/-- The profile value at the identity is controlled by the suffix length. -/
theorem rescaledMapProfile_zero_norm_le
    {K : ℝ≥0} {J : G → W} (hJ : LipschitzWith K J)
    (x k : G) (r : ℝ) (φ : Z → G) (hφ : φ 0 = 1) :
    ‖rescaledMapProfile J x k r φ 0‖ ≤ (K : ℝ) * (dist 1 k / Real.exp r) := by
  have hh := hJ.dist_le_mul (x * k) x
  have he : dist (x * k) x = dist 1 k := by
    simpa only [mul_one, dist_comm] using dist_mul_left x k 1
  rw [he] at hh
  simp only [rescaledMapProfile, hφ, mul_one, norm_smul, Real.norm_eq_abs,
    abs_inv, abs_of_pos (Real.exp_pos r), ← dist_eq_norm]
  calc
    _ ≤ (Real.exp r)⁻¹ * ((K : ℝ) * dist 1 k) :=
      mul_le_mul_of_nonneg_left hh (inv_nonneg.mpr (Real.exp_pos r).le)
    _ = _ := by ring

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_SublinearScaleOffsets
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instNonemptyBases _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_nonempty _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Vanishing offsets from the local comparison of adjacent scales -/

namespace PolycyclicRecognition

open Filter
open scoped Topology

/-- The scale-comparison estimate in the height argument forces its offsets
to be uniformly sublinear. Only finitely many contractions are needed for
each prescribed error, so no regularity of the offset as a function of scale
is required. -/
theorem uniform_sublinear_of_contractive_increments
    {P W : Type} [NormedAddCommGroup W]
    (s : P → ℝ → W) {q C : ℝ} (hq : 0 < q) (hq1 : q < 1)
    (hbound : ∀ p r, 1 ≤ r → ‖s p r‖ ≤ C * r)
    (hincrement : ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 1 ≤ R ∧
      ∀ p r, R ≤ r → ‖s p r - s p (q * r)‖ ≤ ε * r) :
    ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 1 ≤ R ∧
      ∀ p r, R ≤ r → ‖s p r‖ ≤ ε * r := by
  intro ε hε
  let e := ε * (1 - q) / 2
  have he : 0 < e := div_pos (mul_pos hε (sub_pos.mpr hq1)) (by norm_num)
  obtain ⟨R, hR1, hinc⟩ := hincrement e he
  have hiter : ∀ k : ℕ, ∀ p r, R ≤ q ^ k * r →
      ‖s p r‖ ≤ (C * q ^ k + e / (1 - q)) * r := by
    intro k
    induction k with
    | zero =>
      intro p r hr
      have hr' : R ≤ r := by simpa using hr
      have hh := hbound p r (hR1.trans hr')
      have he' : 0 ≤ e / (1 - q) := div_nonneg he.le (sub_pos.mpr hq1).le
      simp only [pow_zero, mul_one]
      nlinarith [mul_nonneg he' (show 0 ≤ r by linarith)]
    | succ k ih =>
      intro p r hr
      have hrpos : 0 < r := pos_of_mul_pos_right
        (lt_of_lt_of_le (lt_of_lt_of_le zero_lt_one hR1) hr) (pow_nonneg hq.le _)
      have hpow : q ^ (k + 1) ≤ 1 := pow_le_one₀ hq.le hq1.le
      have hRr : R ≤ r := hr.trans ((mul_le_mul_of_nonneg_right hpow hrpos.le).trans_eq (one_mul r))
      have hsub : R ≤ q ^ k * (q * r) := by simpa only [pow_succ, mul_assoc] using hr
      calc
        ‖s p r‖ = ‖(s p r - s p (q * r)) + s p (q * r)‖ := by rw [sub_add_cancel]
        _ ≤ ‖s p r - s p (q * r)‖ + ‖s p (q * r)‖ := norm_add_le _ _
        _ ≤ e * r + (C * q ^ k + e / (1 - q)) * (q * r) :=
          add_le_add (hinc p r hRr) (ih p (q * r) hsub)
        _ = (C * q ^ (k + 1) + e / (1 - q)) * r := by
          rw [pow_succ]
          field_simp [(sub_pos.mpr hq1).ne'] <;> ring
  have hlim : Tendsto (fun k : ℕ => C * q ^ k) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hq.le hq1).const_mul C
  obtain ⟨k, hk⟩ := (hlim.eventually (gt_mem_nhds (half_pos hε))).exists
  refine ⟨max 1 (R / q ^ k), le_max_left _ _, ?_⟩
  intro p r hr
  have hr0 : 0 ≤ r := zero_le_one.trans ((le_max_left _ _).trans hr)
  have hkr : R ≤ q ^ k * r := by
    have hh := (div_le_iff₀ (pow_pos hq k)).mp ((le_max_right _ _).trans hr)
    simpa only [mul_comm] using hh
  have heq : e / (1 - q) = ε / 2 := by
    dsimp only [e]
    field_simp [(sub_pos.mpr hq1).ne']
  apply (hiter k p r hkr).trans
  rw [heq]
  exact mul_le_mul_of_nonneg_right (by linarith) hr0

end PolycyclicRecognition

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_ScaleLabelStabilization
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_nonempty _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Passing from adjacent-scale comparisons to uniform stabilization -/

namespace PolycyclicRecognition

open Filter
open scoped Topology

/-- Nearby-scale equality propagates along a finite geometric chain. -/
theorem scale_label_eq_of_nearby
    {P L : Type} (label : P → ℝ → L) {q R : ℝ} (hq : 1 < q) (hR : 0 < R)
    (hnear : ∀ p r t, R ≤ r → r ≤ t → t ≤ q * r → label p r = label p t) :
    ∀ p r, R ≤ r → label p r = label p R := by
  intro p r hr
  have hpow (n : ℕ) : R ≤ q ^ n * R := by
    simpa using mul_le_mul_of_nonneg_right (one_le_pow₀ hq.le) hR.le
  have hchain (n : ℕ) : label p (q ^ n * R) = label p R := by
    induction n with
    | zero => simp
    | succ n ih =>
        apply Eq.trans _ ih
        symm
        apply hnear p _ _ (hpow n)
        · rw [pow_succ]
          simpa only [one_mul, mul_one, mul_assoc, mul_comm, mul_left_comm] using
            mul_le_mul_of_nonneg_right hq.le
              (mul_nonneg (pow_nonneg (zero_lt_one.trans hq).le n) hR.le)
        · rw [pow_succ]
          ring_nf
          exact le_rfl
  obtain ⟨n, hn, hn'⟩ := exists_nat_pow_near ((one_le_div hR).mpr hr) hq
  have hlow : q ^ n * R ≤ r := (le_div_iff₀ hR).mp hn
  have hupp : r ≤ q * (q ^ n * R) := by
    have hh := (div_lt_iff₀ hR).mp hn'
    rw [pow_succ] at hh
    nlinarith
  exact (hnear p _ _ (hpow n) hlow hupp).symm.trans (hchain n)

/-- Sequential comparison at arbitrary increasing source and target scales
is enough for the uniform estimate used in the geometric telescoping step. -/
theorem uniform_nearby_bound_of_strict_sequences
    {P : Type} (err : P → ℝ → ℝ → ℝ) (q : ℝ)
    (hseq : ∀ (p : ℕ → P) (r t : ℕ → ℝ),
      Tendsto r atTop atTop → StrictMono r → StrictMono t →
      (∀ n, 1 ≤ r n) → (∀ n, r n ≤ t n) → (∀ n, t n ≤ q * r n) →
      Tendsto (fun n => err (p n) (r n) (t n)) atTop (𝓝 0)) :
    ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 1 ≤ R ∧
      ∀ p r t, R ≤ r → r ≤ t → t ≤ q * r → err p r t ≤ ε := by
  classical
  intro ε hε
  by_contra h
  push Not at h
  have hex (n : ℕ) := h (max 1 (n : ℝ)) (le_max_left _ _)
  choose p r t hr hrt ht he using hex
  have hr1 n : 1 ≤ r n := (le_max_left _ _).trans (hr n)
  have hrgrow : Tendsto r atTop atTop := tendsto_atTop_mono
    (fun n => (le_max_right _ _).trans (hr n)) tendsto_natCast_atTop_atTop
  obtain ⟨u, hu, hru, _⟩ := exists_strictMono_scale_subsequence r hrgrow
  have htgrow : Tendsto (t ∘ u) atTop atTop :=
    (tendsto_atTop_mono hrt hrgrow).comp hu.tendsto_atTop
  obtain ⟨v, hv, htv, _⟩ := exists_strictMono_scale_subsequence (t ∘ u) htgrow
  have hh := hseq (p ∘ u ∘ v) (r ∘ u ∘ v) (t ∘ u ∘ v)
    (hrgrow.comp (hu.comp hv).tendsto_atTop) (hru.comp hv) htv
    (fun n => hr1 (u (v n))) (fun n => hrt (u (v n))) (fun n => ht (u (v n)))
  obtain ⟨n, hn⟩ := (hh.eventually (gt_mem_nhds hε)).exists
  exact (not_lt_of_ge (he (u (v n))).le) hn

/-- Eventual equality along every scale sequence yields a single uniform
threshold for all maps and basepoints. -/
theorem uniform_nearby_labels_of_strict_sequences
    {P L : Type} (label : P → ℝ → L) (q : ℝ)
    (hseq : ∀ (p : ℕ → P) (r t : ℕ → ℝ),
      Tendsto r atTop atTop → StrictMono r → StrictMono t →
      (∀ n, 1 ≤ r n) → (∀ n, r n ≤ t n) → (∀ n, t n ≤ q * r n) →
      ∀ᶠ n in atTop, label (p n) (r n) = label (p n) (t n)) :
    ∃ R : ℝ, 1 ≤ R ∧ ∀ p r t, R ≤ r → r ≤ t → t ≤ q * r →
      label p r = label p t := by
  classical
  let err := fun p r t => if label p r = label p t then (0 : ℝ) else 1
  have he := uniform_nearby_bound_of_strict_sequences err q (by
    intro p r t hrg hr ht hr1 hrt htq
    apply tendsto_const_nhds.congr'
    filter_upwards [hseq p r t hrg hr ht hr1 hrt htq] with n hn
    simp only [err, hn, ite_true, if_true]) (1 / 2) (by norm_num)
  obtain ⟨R, hR, hb⟩ := he
  refine ⟨R, hR, ?_⟩
  intro p r t hr hrt htq
  have hh := hb p r t hr hrt htq
  by_contra hne
  simp [err, hne] at hh
  norm_num at hh

theorem physical_offset_increment_eq
    {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W]
    {r : ℝ} (hr : 0 < r) (t : ℝ) (b c : W) :
    ‖r • b - t • c‖ = r * dist b ((t / r) • c) := by
  have he : r * (t / r) = t := by field_simp
  calc
    _ = ‖r • (b - (t / r) • c)‖ := by rw [smul_sub, smul_smul, he]
    _ = _ := by rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr, dist_eq_norm]

/-- The normalized mean offsets vanish uniformly once their comparisons
at nearby scales vanish uniformly. -/
theorem uniform_zero_of_normalized_scale_increments
    {P W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W]
    (b : P → ℝ → W) {Q C : ℝ} (hQ : 1 < Q)
    (hbound : ∀ p r, 1 ≤ r → ‖b p r‖ ≤ C)
    (hnear : ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 1 ≤ R ∧
      ∀ p r t, R ≤ r → r ≤ t → t ≤ Q * r →
        dist (b p r) ((t / r) • b p t) ≤ ε) :
    ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 1 ≤ R ∧
      ∀ p r, R ≤ r → ‖b p r‖ ≤ ε := by
  let s := fun p r => r • b p r
  have hQ0 : 0 < Q := zero_lt_one.trans hQ
  have hq : 0 < Q⁻¹ := inv_pos.mpr hQ0
  have hq1 : Q⁻¹ < 1 := inv_lt_one_of_one_lt₀ hQ
  have hsbound p r (hr : 1 ≤ r) : ‖s p r‖ ≤ C * r := by
    change ‖r • b p r‖ ≤ C * r
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (zero_lt_one.trans_le hr), mul_comm C]
    exact mul_le_mul_of_nonneg_left (hbound p r hr) (zero_le_one.trans hr)
  have hinc : ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 1 ≤ R ∧
      ∀ p r, R ≤ r → ‖s p r - s p (Q⁻¹ * r)‖ ≤ ε * r := by
    intro ε hε
    obtain ⟨R, hR, hRnear⟩ := hnear ε hε
    refine ⟨max 1 (Q * R), le_max_left _ _, ?_⟩
    intro p r hr
    have hr0 : 0 < r := zero_lt_one.trans_le ((le_max_left _ _).trans hr)
    have hqr0 : 0 < Q⁻¹ * r := mul_pos hq hr0
    have hRqr : R ≤ Q⁻¹ * r := by
      have hh := mul_le_mul_of_nonneg_left ((le_max_right _ _).trans hr) hq.le
      simpa only [← mul_assoc, inv_mul_cancel₀ hQ0.ne', one_mul] using hh
    have hqrr : Q⁻¹ * r ≤ r := by nlinarith [mul_nonneg (sub_nonneg.mpr hq1.le) hr0.le]
    have hqr : Q * (Q⁻¹ * r) = r := by rw [← mul_assoc, mul_inv_cancel₀ hQ0.ne', one_mul]
    have hh := hRnear p (Q⁻¹ * r) r hRqr hqrr hqr.symm.le
    calc
      ‖s p r - s p (Q⁻¹ * r)‖ = ‖s p (Q⁻¹ * r) - s p r‖ := norm_sub_rev _ _
      _ = (Q⁻¹ * r) * dist (b p (Q⁻¹ * r)) ((r / (Q⁻¹ * r)) • b p r) :=
        physical_offset_increment_eq hqr0 r _ _
      _ ≤ (Q⁻¹ * r) * ε := mul_le_mul_of_nonneg_left hh hqr0.le
      _ ≤ ε * r := by nlinarith
  intro ε hε
  obtain ⟨R, hR, hRs⟩ := uniform_sublinear_of_contractive_increments s hq hq1 hsbound hinc ε hε
  refine ⟨R, hR, ?_⟩
  intro p r hr
  have hh := hRs p r hr
  change ‖r • b p r‖ ≤ ε * r at hh
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (zero_lt_one.trans_le (hR.trans hr))] at hh
  exact (mul_le_mul_iff_right₀ (zero_lt_one.trans_le (hR.trans hr))).mp (by
    simpa only [mul_comm] using hh)

/-- The two conclusions needed from adjacent-scale comparison: a uniform
stable label and a uniformly vanishing normalized offset. -/
theorem uniform_scale_stabilization_of_sequences
    {P L W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W]
    (label : P → ℝ → L) (b : P → ℝ → W) {Q C : ℝ} (hQ : 1 < Q)
    (hbound : ∀ p r, 1 ≤ r → ‖b p r‖ ≤ C)
    (hseq : ∀ (p : ℕ → P) (r t : ℕ → ℝ),
      Tendsto r atTop atTop → StrictMono r → StrictMono t →
      (∀ n, 1 ≤ r n) → (∀ n, r n ≤ t n) → (∀ n, t n ≤ Q * r n) →
      (∀ᶠ n in atTop, label (p n) (r n) = label (p n) (t n)) ∧
      Tendsto (fun n => dist (b (p n) (r n)) ((t n / r n) • b (p n) (t n)))
        atTop (𝓝 0)) :
    (∃ R : ℝ, 1 ≤ R ∧ ∀ p r, R ≤ r → label p r = label p R) ∧
    (∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 1 ≤ R ∧ ∀ p r, R ≤ r → ‖b p r‖ ≤ ε) := by
  obtain ⟨R, hR, hlabels⟩ := uniform_nearby_labels_of_strict_sequences label Q
    (fun p r t hrg hr ht hr1 hrt htQ => (hseq p r t hrg hr ht hr1 hrt htQ).1)
  refine ⟨⟨R, hR, scale_label_eq_of_nearby label hQ (zero_lt_one.trans_le hR) hlabels⟩, ?_⟩
  apply uniform_zero_of_normalized_scale_increments b hQ hbound
  exact uniform_nearby_bound_of_strict_sequences
    (fun p r t => dist (b p r) ((t / r) • b p t)) Q
    (fun p r t hrg hr ht hr1 hrt htQ => (hseq p r t hrg hr ht hr1 hrt htQ).2)

end PolycyclicRecognition

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
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_WordChartScaleTransition
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact coordinate and height identities between two chart scales -/

noncomputable section
namespace PolycyclicRecognition

open Module

variable {L J : Type} [LieRing L] [LieAlgebra ℝ L] [Finite J]

theorem basisScaleTransition_point (b : Basis J ℝ L) (cost : J → ℝ)
    (r t : ℝ) (z : J → ℝ) :
    (exponentialRescaleBasis b cost t).equivFun.symm (basisScaleTransition b cost r t z) =
      (exponentialRescaleBasis b cost r).equivFun.symm z :=
  (exponentialRescaleBasis b cost t).equivFun.symm_apply_apply _

/-- A bracket-killing height scales by the physical scale ratio, exactly. -/
theorem wordChartScaleTransition_height
    {I W : Type} [Fintype I] [DecidableEq I] [AddCommGroup W] [Module ℝ W]
    (X : I → L) (S : Finset (FreeMagma I)) (β : WordBasisSelections X S)
    (height : L →ₗ[ℝ] W) (hkill : ∀ x y : L, height ⁅x, y⁆ = 0)
    {r t : ℝ} (hr : 0 < r) (ht : 0 < t) (z : Fin (finrank ℝ L) → ℝ) :
    let b := WordBasisSelections.basis X S β
    let cost := fun j => (bracketWordLength (β.val j : FreeMagma I) : ℝ)
    height (b.equivFun.symm (basisScaleTransition b cost (Real.log r) (Real.log t) z)) =
      (r / t) • height (b.equivFun.symm z) := by
  dsimp only
  let b := WordBasisSelections.basis X S β
  let cost := fun j => (bracketWordLength (β.val j : FreeMagma I) : ℝ)
  have h₁ := word_length_chart_height X S β height hkill hr z
  have h₂ := word_length_chart_height X S β height hkill ht
    (basisScaleTransition b cost (Real.log r) (Real.log t) z)
  rw [basisScaleTransition_point] at h₂
  have hh := congrArg (fun w : W => t⁻¹ • w) (h₂.symm.trans h₁)
  simpa only [smul_smul, inv_mul_cancel₀ ht.ne', one_smul, div_eq_mul_inv, mul_comm] using hh

/-- If the two charts represent the same point, their actual profiles
agree after multiplication by the physical scale. -/
theorem scaled_profile_eq_of_chart_eq
    {G W Z : Type} [Group G] [PseudoMetricSpace G]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (map : G → W) (x k : G) {r t : ℝ} (hr : 0 < r) (ht : 0 < t)
    (φ ψ : Z → G) (z z' : Z) (hpoint : φ z = ψ z') :
    r • rescaledMapProfile map x k (Real.log r) φ z =
      t • rescaledMapProfile map x k (Real.log t) ψ z' := by
  simp only [rescaledMapProfile, Real.exp_log hr, Real.exp_log ht, smul_smul,
    mul_inv_cancel₀ hr.ne', mul_inv_cancel₀ ht.ne', one_smul, hpoint]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanScaleTransition
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instCompactSpaceElemProdContinuousMapNormalizedPair _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.CartanFactorModel.realScaleProfile_apply _root_.OAI.PolycyclicRecognition.bracketWordDifferential_mul _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact scale transport of the actual Cartan profiles on a fixed ball -/

noncomputable section
namespace PolycyclicRecognition

open Module
open scoped Manifold

variable {I L : Type} [Fintype I] [DecidableEq I] [LieRing L] [LieAlgebra ℝ L]

set_option maxHeartbeats 1000000 in
theorem wordBallScaleTransition_height
    {W : Type} [AddCommGroup W] [Module ℝ W]
    (X : I → L) (S : Finset (FreeMagma I)) (β : WordBasisSelections X S)
    (height : L →ₗ[ℝ] W) (hkill : ∀ x y : L, height ⁅x, y⁆ = 0)
    (R : ℝ) {r t : ℝ} (hr : 0 < r) (hrt : r ≤ t)
    (z : Metric.closedBall (0 : Fin (finrank ℝ L) → ℝ) R) :
    (t / r) • height ((WordBasisSelections.basis X S β).equivFun.symm
      (wordBallScaleTransition X S β R hr hrt z)) =
      height ((WordBasisSelections.basis X S β).equivFun.symm z) := by
  change (t / r) • height ((WordBasisSelections.basis X S β).equivFun.symm
    (basisScaleTransition _ _ (Real.log r) (Real.log t) z)) = _
  rw [wordChartScaleTransition_height X S β height hkill hr (hr.trans_le hrt), smul_smul]
  have he : t / r * (r / t) = 1 := by field_simp [hr.ne', (hr.trans_le hrt).ne']
  rw [he, one_smul]

section ActualProfile

variable {EG G W : Type} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [IsTopologicalGroup G]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  {Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H Exp)

set_option maxHeartbeats 1000000 in
omit [Fintype I] [DecidableEq I] in
theorem CartanFactorModel.wordBall_profile_scale_eq
    (hD : Continuous F.ExpD) (J : G → W) (hJ : Continuous J) (x : G)
    (X : I → H) (S : Finset (FreeMagma I)) (β : WordBasisSelections X S)
    (R : ℝ) {r t : ℝ} (hr : 1 ≤ r) (hrt : r ≤ t) (k : F.N.carrier) :
    let b := WordBasisSelections.basis X S β
    let cost := fun j => (bracketWordLength (β.val j : FreeMagma I) : ℝ)
    let profile := fun u => rescaledContinuousProfile J hJ x (F.inclusionN k)
      (max (Real.log u) 0)
      (F.profileChart (exponentialRescaleBasis b cost (max (Real.log u) 0)))
      (F.continuous_profileChart hD _)
    (profile r).restrict (Metric.closedBall 0 R) =
      rescaleCompactProfile (t / r)
        (wordBallScaleTransition X S β R (zero_lt_one.trans_le hr) hrt)
        ((profile t).restrict (Metric.closedBall 0 R)) := by
  dsimp only
  have hr0 : 0 < r := zero_lt_one.trans_le hr
  have ht0 : 0 < t := hr0.trans_le hrt
  have hlr : max (Real.log r) 0 = Real.log r := max_eq_left (Real.log_nonneg hr)
  have hlt : max (Real.log t) 0 = Real.log t := max_eq_left (Real.log_nonneg (hr.trans hrt))
  ext z
  change rescaledMapProfile J x (F.inclusionN k) (max (Real.log r) 0)
      (F.profileChart _) z.val =
    (t / r) • rescaledMapProfile J x (F.inclusionN k) (max (Real.log t) 0)
      (F.profileChart _) (wordBallScaleTransition X S β R hr0 hrt z).val
  rw [hlr, hlt]
  have hpoint : F.profileChart (exponentialRescaleBasis (WordBasisSelections.basis X S β)
      (fun j => (bracketWordLength (β.val j : FreeMagma I) : ℝ)) (Real.log r)) z.val =
    F.profileChart (exponentialRescaleBasis (WordBasisSelections.basis X S β)
      (fun j => (bracketWordLength (β.val j : FreeMagma I) : ℝ)) (Real.log t))
      (wordBallScaleTransition X S β R hr0 hrt z).val := by
    unfold CartanFactorModel.profileChart
    change F.inclusionD (F.ExpD (F.D.equiv _)) = F.inclusionD (F.ExpD (F.D.equiv
      ((exponentialRescaleBasis _ _ (Real.log t)).equivFun.symm
        (basisScaleTransition _ _ (Real.log r) (Real.log t) z.val))))
    rw [basisScaleTransition_point]
  have he := scaled_profile_eq_of_chart_eq J x (F.inclusionN k) hr0 ht0 _ _ _ _ hpoint
  have hh := congrArg (fun w : W => r⁻¹ • w) he
  have hcoeff : r⁻¹ * t = t / r := by ring
  simpa only [smul_smul, inv_mul_cancel₀ hr0.ne', one_smul, hcoeff] using hh

end ActualProfile
end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanActualScaleComparison
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instCompactSpaceElemProdContinuousMapNormalizedPair _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.CartanFactorModel.heightRay_zero _root_.OAI.PolycyclicRecognition.CartanFactorModel.realScaleProfile_apply _root_.OAI.PolycyclicRecognition.bracketWordDifferential_mul _root_.OAI.PolycyclicRecognition.exponentialRescaleBasis_zero _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.modelNilradicalLinearAction_apply _root_.OAI.PolycyclicRecognition.modelNilradicalRotation_apply _root_.OAI.PolycyclicRecognition.modelNilradicalRotation_mul _root_.OAI.PolycyclicRecognition.modelNilradicalRotation_one _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Comparing the actual Cartan profiles at two physical scales -/

noncomputable section
namespace PolycyclicRecognition

open Module MeasureTheory Filter Set
open scoped Manifold Topology

variable {EG G W I L : Type} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [IsTopologicalGroup G]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  {Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H Exp)
  [IsTopologicalGroup F.N.carrier] [Finite L] [Nonempty L] [Fintype I] [DecidableEq I]

set_option maxHeartbeats 1000000 in
omit [IsTopologicalGroup F.N.carrier] in
theorem CartanFactorModel.adjacent_scale_labels_of_approximation
    (hD : Continuous F.ExpD) (height : H →ₗ[ℝ] W)
    (hheight : Function.Surjective height) (hkill : ∀ u v : H, height ⁅u, v⁆ = 0)
    (labels : L → W ≃ₗ[ℝ] W) (hlabels : Function.Injective labels)
    (X : I → H) (S : Finset (FreeMagma I)) (β : WordBasisSelections X S)
    (μ ν : ℕ → ProbabilityMeasure F.N.carrier) (C D : ℕ → Set F.N.carrier)
    (hC : ∀ n, IsCompact (C n)) (hDset : ∀ n, IsCompact (D n))
    (hμ : ∀ n, ∀ᵐ k ∂(μ n : Measure F.N.carrier), k ∈ C n)
    (hν : ∀ n, ∀ᵐ k ∂(ν n : Measure F.N.carrier), k ∈ D n)
    (r t : ℕ → ℝ) (hr : ∀ n, 1 ≤ r n) (hrt : ∀ n, r n ≤ t n)
    {K : ℝ} (hK : 0 < K) (hbound : ∀ n, t n ≤ K * r n)
    (J : ℕ → G → W) (hJ : ∀ n, Continuous (J n)) (center : ℕ → G)
    (raw raw' : ℕ → F.N.carrier → C((Fin (finrank ℝ H) → ℝ), W))
    (hraw : ∀ n k z, raw n k z = rescaledMapProfile (J n) (center n) (F.inclusionN k)
      (max (Real.log (r n)) 0) (F.profileChart (exponentialRescaleBasis
        (WordBasisSelections.basis X S β)
        (fun j => (bracketWordLength (β.val j : FreeMagma I) : ℝ))
        (max (Real.log (r n)) 0))) z)
    (hraw' : ∀ n k z, raw' n k z = rescaledMapProfile (J n) (center n) (F.inclusionN k)
      (max (Real.log (t n)) 0) (F.profileChart (exponentialRescaleBasis
        (WordBasisSelections.basis X S β)
        (fun j => (bracketWordLength (β.val j : FreeMagma I) : ℝ))
        (max (Real.log (t n)) 0))) z)
    (R : ℝ) (hR : 0 < R) :
    let Z := Metric.closedBall (0 : Fin (finrank ℝ H) → ℝ) R
    let bD := WordBasisSelections.basis X S β
    let q := (height.comp bD.equivFun.symm.toLinearMap).toContinuousLinearMap
    let A := fun l => (⟨fun z => labels l (q z),
      (labels l).toContinuousLinearEquiv.continuous.comp q.continuous⟩ :
        C((Fin (finrank ℝ H) → ℝ), W)).restrict Z
    let b := fun n => ∫ k, raw n k 0 ∂(μ n : Measure F.N.carrier)
    let b' := fun n => ∫ k, raw' n k 0 ∂(ν n : Measure F.N.carrier)
    (∃ a : ℕ → L, Tendsto (fun n => ∫ k, dist ((raw n k).restrict Z)
      (A (a n) + ContinuousMap.const Z (b n)) ∂(μ n : Measure F.N.carrier)) atTop (𝓝 0)) →
    (∃ a : ℕ → L, Tendsto (fun n => ∫ k, dist ((raw' n k).restrict Z)
      (A (a n) + ContinuousMap.const Z (b' n)) ∂(ν n : Measure F.N.carrier)) atTop (𝓝 0)) →
    (∀ ε : ℝ, 0 < ε → Tendsto (fun n => (μ n : Measure F.N.carrier).prod
      (ν n : Measure F.N.carrier) {p | ε ≤ dist ((raw n p.1).restrict Z)
        ((raw n p.2).restrict Z)}) atTop (𝓝 0)) →
    let label := fun n => canonicalAffineLabel (μ n : Measure F.N.carrier)
      (fun k => (raw n k).restrict Z) (fun l => A l + ContinuousMap.const Z (b n))
    let label' := fun n => canonicalAffineLabel (ν n : Measure F.N.carrier)
      (fun k => (raw' n k).restrict Z) (fun l => A l + ContinuousMap.const Z (b' n))
    (∀ᶠ n in atTop, label n = label' n) ∧
      Tendsto (fun n => dist (b n) ((t n / r n) • b' n)) atTop (𝓝 0) := by
  classical
  dsimp only
  intro hmean hmean' hpair
  let Z := Metric.closedBall (0 : Fin (finrank ℝ H) → ℝ) R
  let bD := WordBasisSelections.basis X S β
  let q := (height.comp bD.equivFun.symm.toLinearMap).toContinuousLinearMap
  let A := fun l => (⟨fun z => labels l (q z),
    (labels l).toContinuousLinearEquiv.continuous.comp q.continuous⟩ :
      C((Fin (finrank ℝ H) → ℝ), W)).restrict Z
  let b := fun n => ∫ k, raw n k 0 ∂(μ n : Measure F.N.carrier)
  let b' := fun n => ∫ k, raw' n k 0 ∂(ν n : Measure F.N.carrier)
  let label := fun n => canonicalAffineLabel (μ n : Measure F.N.carrier)
    (fun k => (raw n k).restrict Z) (fun l => A l + ContinuousMap.const Z (b n))
  let label' := fun n => canonicalAffineLabel (ν n : Measure F.N.carrier)
    (fun k => (raw' n k).restrict Z) (fun l => A l + ContinuousMap.const Z (b' n))
  have hleft := canonicalAffineLabel_mean_tendsto_zero
    (fun n => (μ n : Measure F.N.carrier)) (fun n k => (raw n k).restrict Z)
    (fun n l => A l + ContinuousMap.const Z (b n)) hmean
  have hright := canonicalAffineLabel_mean_tendsto_zero
    (fun n => (ν n : Measure F.N.carrier)) (fun n k => (raw' n k).restrict Z)
    (fun n l => A l + ContinuousMap.const Z (b' n)) hmean'
  let cost := fun j => (bracketWordLength (β.val j : FreeMagma I) : ℝ)
  let φ := fun n => wordBallScaleTransition X S β R (zero_lt_one.trans_le (hr n)) (hrt n)
  have hprofile (s : ℕ → ℝ)
      (u : ℕ → F.N.carrier → C((Fin (finrank ℝ H) → ℝ), W))
      (hu : ∀ n k z, u n k z = rescaledMapProfile (J n) (center n) (F.inclusionN k)
        (max (Real.log (s n)) 0)
        (F.profileChart (exponentialRescaleBasis bD cost (max (Real.log (s n)) 0))) z) :
      ∀ n, Continuous (fun k => (u n k).restrict Z) := by
    intro n
    have he : u n = fun k => rescaledContinuousProfile (J n) (hJ n) (center n) (F.inclusionN k)
        (max (Real.log (s n)) 0)
        (F.profileChart (exponentialRescaleBasis bD cost (max (Real.log (s n)) 0)))
        (F.continuous_profileChart hD _) := by
      funext k
      ext z
      exact hu n k z
    rw [he]
    exact (ContinuousMap.continuous_restrict Z).comp
      ((continuous_rescaledContinuousProfile (J n) (hJ n) (center n)
        (max (Real.log (s n)) 0)
        (F.profileChart (exponentialRescaleBasis bD cost (max (Real.log (s n)) 0)))
        (F.continuous_profileChart hD _)).comp F.closedN.continuous)
  have hmatch n k : (raw n k).restrict Z = rescaleCompactProfile
      (t n / r n) (φ n) ((raw' n k).restrict Z) := by
    have he := F.wordBall_profile_scale_eq hD (J n) (hJ n) (center n) X S β R (hr n) (hrt n) k
    ext z
    have hh := congrArg (fun f : C(Z, W) => f z) he
    simpa only [rescaledContinuousProfile, ContinuousMap.coe_mk, rescaleCompactProfile,
      ContinuousMap.smul_apply, ContinuousMap.comp_apply, ContinuousMap.restrict_apply,
      ← hraw, ← hraw', φ, bD, cost] using hh
  have hq : Function.Surjective q := hheight.comp bD.equivFun.symm.surjective
  have hA : Function.Injective A := by
    intro l l' he
    apply hlabels
    have he' : linearBallProfile q (labels l).toContinuousLinearEquiv.toContinuousLinearMap R =
        linearBallProfile q (labels l').toContinuousLinearEquiv.toContinuousLinearMap R := by
      exact he
    have hh := linearBallProfile_injective q hq hR he'
    ext w
    exact DFunLike.congr_fun hh w
  let : Fintype L := Fintype.ofFinite L
  apply affine_scale_labels_and_offsets μ ν C D hC hDset hμ hν
    (fun n k => (raw n k).restrict Z) (fun n k => (raw' n k).restrict Z)
    (hprofile r raw hraw) (hprofile t raw' hraw')
    (fun n => t n / r n) φ hK
    (fun n => by
      rw [abs_of_pos (div_pos (zero_lt_one.trans_le ((hr n).trans (hrt n)))
        (zero_lt_one.trans_le (hr n)))]
      exact (div_le_iff₀ (zero_lt_one.trans_le (hr n))).mpr (hbound n))
    hmatch A hA ⟨0, Metric.mem_closedBall_self hR.le⟩
    (fun l => by simp [A, q]) _ label label' b b' hleft hright hpair
  intro n l z
  change (t n / r n) • labels l (q (φ n z)) = labels l (q z)
  rw [← map_smul]
  congr 1
  exact wordBallScaleTransition_height X S β height hkill R
    (zero_lt_one.trans_le (hr n)) (hrt n) z

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_ExponentialBoxRadiusVolume
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact radius dependence of the original coordinate Haar boxes -/

noncomputable section
namespace PolycyclicRecognition

open Module MeasureTheory Set
open scoped Manifold ENNReal

theorem exponential_box_radius_volume
    {L E G : Type} [LieRing L] [LieAlgebra ℝ L]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace G] [ChartedSpace E G] [Group G]
    [LieGroup (𝓘(ℝ, E)) ⊤ G] [MeasurableSpace G] [BorelSpace G]
    (e : L ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, E)) G)
    (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G)
    (chart : GroupLieAlgebra (𝓘(ℝ, E)) G ≃ₜ G) (hchart : ∀ x, chart x = Exp x)
    {n : ℕ} (b₀ b : Basis (Fin n) ℝ L) {R : ℝ} (hR : 0 ≤ R) :
    (Measure.map ((Exp ∘ e) ∘ b₀.equivFun.symm) volume)
      (exponentialCoordinateBox (Exp ∘ e) b R) =
      ENNReal.ofReal R ^ n *
        (Measure.map ((Exp ∘ e) ∘ b₀.equivFun.symm) volume)
          (exponentialCoordinateBox (Exp ∘ e) b 1) := by
  rw [exponentialCoordinateBox_eq_cube_image _ _ R hR,
    exponentialCoordinateBox_eq_cube_image _ _ 1 zero_le_one,
    exponential_basis_subset_measure e Exp chart hchart,
    exponential_basis_subset_measure e Exp chart hchart]
  have hcube : volume (Icc (fun _ : Fin n => -R) (fun _ => R)) =
      ENNReal.ofReal R ^ n * volume (Icc (fun _ : Fin n => (-1 : ℝ)) (fun _ => 1)) := by
    simp only [Real.volume_Icc_pi, sub_neg_eq_add, ← two_mul,
      Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), mul_pow]
    simp only [mul_one]
    exact mul_comm _ _
  rw [hcube]
  ac_rfl

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanBoxRadiusProbability
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instDecidableEqConeMixedWords _root_.OAI.PolycyclicRecognition.CartanWordModel.instFintypeConeMixedWords _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_countable _root_.OAI.PolycyclicRecognition.finitelyGeneratedSubgroupIndex_countable _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.CartanFactorModel.heightRay_zero _root_.OAI.PolycyclicRecognition.CartanFactorModel.realScaleProfile_apply _root_.OAI.PolycyclicRecognition.CartanFactorModel.sampledProbeProfile_apply _root_.OAI.PolycyclicRecognition.cartanWeightDerivation_apply_root _root_.OAI.PolycyclicRecognition.cartanWeightDilation_apply _root_.OAI.PolycyclicRecognition.cartanWeightScale_add_apply _root_.OAI.PolycyclicRecognition.cartanWeightScale_zero_apply _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.modelNilradicalLinearAction_apply _root_.OAI.PolycyclicRecognition.modelNilradicalRotation_apply _root_.OAI.PolycyclicRecognition.modelNilradicalRotation_mul _root_.OAI.PolycyclicRecognition.modelNilradicalRotation_one _root_.OAI.PolycyclicRecognition.nilshadowWeightDerivation_symm _root_.OAI.PolycyclicRecognition.nilshadowWeightOperator_symm _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Positive finite probabilities and exact ratios for larger Cartan boxes -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra MeasureTheory Set
open scoped Manifold ENNReal

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
theorem groupBox_radius_properties
    (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
    (chartN : GroupLieAlgebra (𝓘(ℝ, F.N.modelSpace)) F.N.carrier ≃ₜ F.N.carrier)
    (hchartN : ∀ x, chartN x = F.ExpN x)
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (E : Set W) (β : M.Bases) (r : ℝ) {R : ℝ} (hR : 0 < R) :
    let μ := Measure.map ((F.ExpN ∘ F.N.equiv) ∘ b₀.equivFun.symm) volume
    let Q := M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) E β r R
    let C := M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) E β r 1
    MeasurableSet Q ∧ μ Q ≠ 0 ∧ μ Q ≠ ∞ ∧
      μ Q / μ C = ENNReal.ofReal R ^ finrank ℝ (cartanRootIdeal H) := by
  dsimp only
  have hu := M.translated_groupBox_cell_properties T F hunimod eW
    haarN chartN hchartN b₀ E β r 1
  simp only [mul_one, image_id'] at hu
  have hv := exponential_box_radius_volume F.N.equiv F.ExpN chartN hchartN b₀
    (M.boxBasis T hunimod eW E β r) hR.le
  let μ := Measure.map ((F.ExpN ∘ F.N.equiv) ∘ b₀.equivFun.symm) volume
  change μ (M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) E β r R) =
    ENNReal.ofReal R ^ finrank ℝ (cartanRootIdeal H) *
      μ (M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) E β r 1) at hv
  have hme := measurableEmbedding_translated_exponential_basis F.N.equiv F.ExpN
    chartN hchartN (M.boxBasis T hunimod eW E β r) 1
  simp only [mul_one] at hme
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [groupBox, exponentialCoordinateBox_eq_cube_image _ _ R hR.le]
    exact hme.measurableSet_image.mpr measurableSet_Icc
  · rw [hv]
    exact mul_ne_zero (pow_ne_zero _ (ENNReal.ofReal_pos.mpr hR).ne') hu.2.1
  · rw [hv]
    exact ENNReal.mul_ne_top (by simp) hu.2.2
  · rw [hv, ENNReal.mul_div_cancel_right hu.2.1 hu.2.2]

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanCanonicalProfiles
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.CartanFactorModel.heightRay_zero _root_.OAI.PolycyclicRecognition.bracketWordDifferential_mul _root_.OAI.PolycyclicRecognition.chartExponentialFlow_zero _root_.OAI.PolycyclicRecognition.derivationSemidirectHom_apply _root_.OAI.PolycyclicRecognition.exponentialHomOfDynkin_apply_exp _root_.OAI.PolycyclicRecognition.exponentialRescaleBasis_zero _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.modelNilradicalLinearAction_apply _root_.OAI.PolycyclicRecognition.modelNilradicalRotation_apply _root_.OAI.PolycyclicRecognition.modelNilradicalRotation_mul _root_.OAI.PolycyclicRecognition.modelNilradicalRotation_one _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual profiles indexed by a real physical scale -/

noncomputable section
namespace PolycyclicRecognition

open Module MeasureTheory
open scoped Manifold NNReal

variable {EG G W I : Type} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [IsTopologicalGroup G]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [Fintype I] [DecidableEq I]
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  {Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H Exp)

set_option maxHeartbeats 1000000 in
/-- A normalized suffix bound gives the same bound on the mean offset. -/
theorem CartanFactorModel.realScaleProfile_mean_norm_le
    [IsIsometricSMul G G]
    (hD : Continuous F.ExpD) (J : G → W) {K : ℝ≥0} (hJ : LipschitzWith K J) (x : G)
    (X : I → H) (S : Finset (FreeMagma I)) (β : WordBasisSelections X S)
    {r C : ℝ} (hr : 1 ≤ r) (μ : ProbabilityMeasure F.N.carrier)
    (hbound : ∀ᵐ k ∂(μ : Measure F.N.carrier), dist 1 (F.inclusionN k) / r ≤ C) :
    ‖∫ k, F.realScaleProfile hD J hJ.continuous x X S β r k 0
      ∂(μ : Measure F.N.carrier)‖ ≤ (K : ℝ) * C := by
  have hnorm : ∀ᵐ k ∂(μ : Measure F.N.carrier),
      ‖F.realScaleProfile hD J hJ.continuous x X S β r k 0‖ ≤ (K : ℝ) * C := by
    filter_upwards [hbound] with k hk
    have hh := rescaledMapProfile_zero_norm_le hJ x (F.inclusionN k) (max (Real.log r) 0)
      (F.profileChart (exponentialRescaleBasis (WordBasisSelections.basis X S β)
        (fun j => bracketWordExponent (fun _ : I => 1) (β.val j)) (max (Real.log r) 0)))
      (by simp [CartanFactorModel.profileChart, F.isExpD.map_zero])
    rw [max_eq_left (Real.log_nonneg hr), Real.exp_log (zero_lt_one.trans_le hr)] at hh
    simpa only [realScaleProfile_apply, max_eq_left (Real.log_nonneg hr)] using
      hh.trans (mul_le_mul_of_nonneg_left hk K.coe_nonneg)
  simpa [measureReal_def] using norm_integral_le_of_norm_le_const hnorm

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanOrdinaryBoxCover
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instDecidableEqConeMixedWords _root_.OAI.PolycyclicRecognition.CartanWordModel.instFintypeConeMixedWords _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.CartanFactorModel.heightRay_zero _root_.OAI.PolycyclicRecognition.CartanFactorModel.realScaleProfile_apply _root_.OAI.PolycyclicRecognition.CartanFactorModel.sampledProbeProfile_apply _root_.OAI.PolycyclicRecognition.bracketWordDifferential_mul _root_.OAI.PolycyclicRecognition.cartanWeightDerivation_apply_root _root_.OAI.PolycyclicRecognition.chartExponentialFlow_zero _root_.OAI.PolycyclicRecognition.derivationSemidirectHom_apply _root_.OAI.PolycyclicRecognition.exponentialHomOfDynkin_apply_exp _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.nilshadowWeightDerivation_symm _root_.OAI.PolycyclicRecognition.nilshadowWeightOperator_symm _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Fixed larger boxes cover the differences of ordinary chart samples -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule Set
open scoped Manifold

variable {L W EN N : Type} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {H : LieSubalgebra ℝ L} [H.IsCartanSubalgebra] (M : CartanWordModel H)
  {a : ℕ} (T : TriangularAdjoint L a)
  (hunimod : ∀ x : L, LinearMap.trace ℝ _ (ad ℝ _ x) = 0)
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)
  [NormedAddCommGroup EN] [NormedSpace ℝ EN] [FiniteDimensional ℝ EN]
  [TopologicalSpace N] [ChartedSpace EN N] [Group N]
  [LieGroup (𝓘(ℝ, EN)) ⊤ N] [T2Space N]
  (eN : cartanRootIdeal H ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, EN)) N)
  (Exp : GroupLieAlgebra (𝓘(ℝ, EN)) N → N) (hExp : IsGroupExponential Exp)

set_option maxHeartbeats 1000000 in
omit [FiniteDimensional ℝ W] in
include hExp in
theorem exists_ordinary_box_difference_cover
    (dynkin : NilpotentDynkinExpansionInput EN N)
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H)) :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ (E : Set W) (β : M.Bases),
      IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
        (M.boxCost T hunimod eW E) β.val → ∀ r : ℝ, 0 ≤ r →
      ∀ x ∈ M.groupBox T hunimod eW (Exp ∘ eN) E β r 1,
      ∀ y ∈ M.groupBox T hunimod eW (Exp ∘ eN) E β r 1,
        x⁻¹ * y ∈ M.groupBox T hunimod eW (Exp ∘ eN) E β r D := by
  obtain ⟨C, _, hprod⟩ := M.exists_groupBox_product_bound T hunimod eW eN Exp hExp dynkin b₀
  let D := max 1 (C * (1 + (2 : ℝ)) ^ M.bound * (1 + (1 : ℝ)) ^ M.bound)
  refine ⟨D, le_max_left _ _, ?_⟩
  intro E β hβ r hr x hx y hy
  have hp := hprod E β hβ r hr 2 1 zero_le_one ![x⁻¹, y] (by
    intro i
    fin_cases i
    · exact M.groupBox_inv_mem T hunimod eW eN Exp hExp E β r 1 hx
    · exact hy)
  have hp' : x⁻¹ * y ∈ M.groupBox T hunimod eW (Exp ∘ eN) E β r
      (C * (1 + (2 : ℝ)) ^ M.bound * (1 + (1 : ℝ)) ^ M.bound) := by
    simpa using hp
  obtain ⟨v, hv, hb⟩ := hp'
  exact ⟨v, hv, hb.trans (le_max_right _ _)⟩

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanMixedScaleBoxes
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instDecidableEqConeMixedWords _root_.OAI.PolycyclicRecognition.CartanWordModel.instFintypeConeMixedWords _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The exact box inclusions needed for adjacent-scale comparisons -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule Set

variable {L W N : Type} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {H : LieSubalgebra ℝ L} [H.IsCartanSubalgebra] (M : CartanWordModel H)
  {a : ℕ} (T : TriangularAdjoint L a)
  (hunimod : ∀ x : L, LinearMap.trace ℝ _ (ad ℝ _ x) = 0)
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  (eW : HeightSpace T.character ≃ₗ[ℝ] W) (Exp : cartanRootIdeal H → N)

set_option maxHeartbeats 1000000 in
/-- Pointwise comparison of actual exponent widths gives inclusion of
exponential boxes, without an additional geometric assumption. -/
theorem groupBox_subset_of_exponent_le
    (E E' : Set W) (β : M.Bases) (r t R : ℝ)
    (h : ∀ w : M.wordList, r * M.boxCost T hunimod eW E w ≤
      t * M.boxCost T hunimod eW E' w) :
    M.groupBox T hunimod eW Exp E β r R ⊆
      M.groupBox T hunimod eW Exp E' β t R := by
  rintro q ⟨v, hv, hc⟩
  refine ⟨v, hv, le_trans ?_ hc⟩
  exact norm_exponentialRescaleBasis_le_of_exponents_le
    (WordBasisSelections.basis M.letter M.wordList β)
    (fun j => M.boxCost T hunimod eW E' (β.val j))
    (fun j => M.boxCost T hunimod eW E (β.val j)) t r (fun j => h (β.val j)) v

set_option maxHeartbeats 1000000 in
theorem groupBox_mono_scale
    (E : Set W) (β : M.Bases) {r t R : ℝ} (hrt : r ≤ t)
    (hcost : ∀ w : M.wordList, 0 ≤ M.boxCost T hunimod eW E w) :
    M.groupBox T hunimod eW Exp E β r R ⊆
      M.groupBox T hunimod eW Exp E β t R :=
  M.groupBox_subset_of_exponent_le T hunimod eW Exp E E β r t R
    (fun w => mul_le_mul_of_nonneg_right hrt (hcost w))

set_option maxHeartbeats 1000000 in
/-- Every nearby larger scale fits inside the fixed strict enlargement
at the smaller scale. The coordinate radius is unchanged. -/
theorem groupBox_scale_le_enlargement
    [FiniteDimensional ℝ W] {E : Set W} (hE : IsCompact E) (hne : E.Nonempty)
    (hcost : ∀ w : M.wordList, 0 ≤ M.boxCost T hunimod eW E w)
    (β : M.Bases) {r t δ R : ℝ} (hδ : 0 ≤ δ) (hrt : t ≤ (1 + δ) * r) :
    M.groupBox T hunimod eW Exp E β t R ⊆
      M.groupBox T hunimod eW Exp ((fun w => (1 + δ) • w) '' E) β r R := by
  apply M.groupBox_subset_of_exponent_le T hunimod eW Exp
  intro w
  rw [M.boxCost_image_smul T hunimod eW hE hne (by linarith)]
  calc
    t * M.boxCost T hunimod eW E w ≤ ((1 + δ) * r) * M.boxCost T hunimod eW E w :=
      mul_le_mul_of_nonneg_right hrt (hcost w)
    _ = r * ((1 + δ) * M.boxCost T hunimod eW E w) := by ring

open scoped Manifold

variable {EN : Type} [NormedAddCommGroup EN] [NormedSpace ℝ EN]
  [FiniteDimensional ℝ EN] [TopologicalSpace N] [ChartedSpace EN N] [Group N]
  [LieGroup (𝓘(ℝ, EN)) ⊤ N] [T2Space N]

set_option maxHeartbeats 1000000 in
/-- One radius covers the differences of a smaller-scale sample and a
larger-scale sample, uniformly in both scales. -/
theorem exists_mixed_scale_box_difference_cover
    (eN : cartanRootIdeal H ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, EN)) N)
    (ExpN : GroupLieAlgebra (𝓘(ℝ, EN)) N → N) (hExp : IsGroupExponential ExpN)
    (dynkin : NilpotentDynkinExpansionInput EN N)
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H)) :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ (E : Set W) (β : M.Bases),
      IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
        (M.boxCost T hunimod eW E) β.val →
      (∀ w : M.wordList, 0 ≤ M.boxCost T hunimod eW E w) →
      ∀ r t : ℝ, 0 ≤ t → r ≤ t →
      ∀ x ∈ M.groupBox T hunimod eW (ExpN ∘ eN) E β r 1,
      ∀ y ∈ M.groupBox T hunimod eW (ExpN ∘ eN) E β t 1,
        x⁻¹ * y ∈ M.groupBox T hunimod eW (ExpN ∘ eN) E β t D := by
  obtain ⟨D, hD, hc⟩ := M.exists_ordinary_box_difference_cover T hunimod eW eN ExpN hExp dynkin b₀
  refine ⟨D, hD, ?_⟩
  intro E β hβ hcost r t ht hrt x hx y hy
  exact hc E β hβ t ht x
    (M.groupBox_mono_scale T hunimod eW (ExpN ∘ eN) E β hrt hcost hx) y hy

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanUniformSuffixMetric
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instDecidableEqConeMixedWords _root_.OAI.PolycyclicRecognition.CartanWordModel.instFintypeConeMixedWords _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.CartanFactorModel.heightRay_zero _root_.OAI.PolycyclicRecognition.CartanFactorModel.realScaleProfile_apply _root_.OAI.PolycyclicRecognition.CartanFactorModel.sampledProbeProfile_apply _root_.OAI.PolycyclicRecognition.bracketWordDifferential_mul _root_.OAI.PolycyclicRecognition.cartanWeightDerivation_apply_root _root_.OAI.PolycyclicRecognition.chartExponentialFlow_zero _root_.OAI.PolycyclicRecognition.derivationSemidirectHom_apply _root_.OAI.PolycyclicRecognition.exponentialHomOfDynkin_apply_exp _root_.OAI.PolycyclicRecognition.exponentialRescaleBasis_zero _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.modelNilradicalLinearAction_apply _root_.OAI.PolycyclicRecognition.modelNilradicalRotation_apply _root_.OAI.PolycyclicRecognition.modelNilradicalRotation_mul _root_.OAI.PolycyclicRecognition.modelNilradicalRotation_one _root_.OAI.PolycyclicRecognition.nilshadowWeightDerivation_symm _root_.OAI.PolycyclicRecognition.nilshadowWeightOperator_symm _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A fixed metric bound for every allowed suffix family -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule Filter Set
open scoped Manifold Topology

variable {EG G W : Type} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G] [IsIsometricSMul G G]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H Exp)
  (hunimod : ∀ x : GroupLieAlgebra (𝓘(ℝ, EG)) G, LinearMap.trace ℝ _ (ad ℝ _ x) = 0)
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)

set_option maxHeartbeats 1000000 in
include T in
/-- The bound is fixed before the enlargement, the scale sequence, and
the subexponential radius. Thus compact profiles may be chosen before the
small enlargement required by the neighboring theorem. -/
theorem exists_uniform_suffix_metric_bound
    (hExp : IsGroupExponential Exp)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
    (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    {E : Set W} (hE : IsCompact E) (hne : E.Nonempty)
    (hweights : ∀ i, 0 < (M.supportIn T hunimod eW).weightSupport E i)
    (β : M.Bases)
    (hβ : IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
      (M.boxCost T hunimod eW E) β.val) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ δ : ℝ, 0 ≤ δ → δ ≤ 1 →
      ∀ (scale R : ℕ → ℝ), (∀ n, 1 ≤ scale n) →
      HasSubexponentialUpperBoundSeq scale R →
      ∀ᶠ n in atTop, ∀ k ∈ M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv)
        ((fun w => (1 + δ) • w) '' E) β (scale n) (R n),
      ∀ q ∈ (fun u => u * k) ''
        M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) E β (scale n) 1,
        dist 1 (F.inclusionN q) / scale n ≤ C := by
  let s := (M.supportIn T hunimod eW).weightSupport E
  let t := fun i => 2 * s i
  have ht i : 0 < t i := mul_pos (by norm_num) (hweights i)
  have hβt : IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
      (fun w => bracketWordExponent t w) β.val := by
    refine ⟨hβ.1, ?_⟩
    intro γ hγ
    simp only [columnBasisWeight, t, bracketWordExponent_const_mul, ← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (hβ.2 γ hγ) (by norm_num)
  obtain ⟨C, lo, hC, hlo, hanchor⟩ := exists_bounded_box_profile_anchors T M F
    hExp realize haarN dynkinN b₀ s t hweights ht
  refine ⟨C, hC, ?_⟩
  intro δ hδ hδ1 scale R hs1 hR
  have hs0 n : 0 ≤ scale n := zero_le_one.trans (hs1 n)
  obtain ⟨ε, _, hε, hRε⟩ := exists_sequence_subexponential_rate scale R
    (fun n => zero_lt_one.trans_le (hs1 n)) hR
  filter_upwards [hε.eventually (gt_mem_nhds hlo)] with n hn
  intro k hk q hq
  obtain ⟨u, hu, rfl⟩ := hq
  apply hanchor β β hβ hβt (scale n) (ε n) (hs1 n) hn.le u k hu
  obtain ⟨v, hv, hcoord⟩ := hk
  refine ⟨v, hv, le_trans ?_ (hRε n)⟩
  have hcost (w : M.wordList) : M.boxCost T hunimod eW ((fun w => (1 + δ) • w) '' E) w =
      (1 + δ) * M.boxCost T hunimod eW E w :=
    M.boxCost_image_smul T hunimod eW hE hne (by linarith) w
  change ‖(M.boxBasis T hunimod eW ((fun w => (1 + δ) • w) '' E) β (scale n)).equivFun v‖
    ≤ R n at hcoord
  simp only [boxBasis, hcost] at hcoord
  have hgain := norm_change_exponentialRescaleBasis_le
    (WordBasisSelections.basis M.letter M.wordList β)
    (fun j => 2 * M.boxCost T hunimod eW E (β.val j))
    (fun j => (1 + δ) * M.boxCost T hunimod eW E (β.val j)) (hs0 n) (α := 0)
    (fun j => by
      have hp : 0 ≤ M.boxCost T hunimod eW E (β.val j) :=
        (bracketWordExponent_pos s hweights _).le
      nlinarith [mul_le_mul_of_nonneg_right hδ1 hp]) v
  simp only [mul_zero, Real.exp_zero, one_mul] at hgain
  simpa only [t, bracketWordExponent_const_mul, boxCost, s] using hgain.trans hcoord

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanOrdinaryMetricBound
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instDecidableEqConeMixedWords _root_.OAI.PolycyclicRecognition.CartanWordModel.instFintypeConeMixedWords _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_nonempty _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.CartanFactorModel.heightRay_zero _root_.OAI.PolycyclicRecognition.CartanFactorModel.realScaleProfile_apply _root_.OAI.PolycyclicRecognition.CartanFactorModel.sampledProbeProfile_apply _root_.OAI.PolycyclicRecognition.bracketWordDifferential_mul _root_.OAI.PolycyclicRecognition.cartanWeightDerivation_apply_root _root_.OAI.PolycyclicRecognition.chartExponentialFlow_zero _root_.OAI.PolycyclicRecognition.derivationSemidirectHom_apply _root_.OAI.PolycyclicRecognition.exponentialHomOfDynkin_apply_exp _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.modelNilradicalLinearAction_apply _root_.OAI.PolycyclicRecognition.modelNilradicalRotation_apply _root_.OAI.PolycyclicRecognition.modelNilradicalRotation_mul _root_.OAI.PolycyclicRecognition.modelNilradicalRotation_one _root_.OAI.PolycyclicRecognition.nilshadowWeightDerivation_symm _root_.OAI.PolycyclicRecognition.nilshadowWeightOperator_symm _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform metric bounds for the ordinary Haar cells -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule Filter Set
open scoped Manifold Topology

variable {EG G W : Type} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G] [IsIsometricSMul G G]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H Exp)
  (hunimod : ∀ x : GroupLieAlgebra (𝓘(ℝ, EG)) G, LinearMap.trace ℝ _ (ad ℝ _ x) = 0)
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)

set_option maxHeartbeats 1000000 in
include T in
/-- The unit-radius ordinary cells have normalized diameter bounded at
all physical scales at least one. A constant scale sequence removes the
eventual quantifier from the suffix metric estimate. -/
theorem exists_ordinary_cell_metric_bound
    (hExp : IsGroupExponential Exp)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
    (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    {E : Set W} (hE : IsCompact E) (hne : E.Nonempty)
    (hweights : ∀ i, 0 < (M.supportIn T hunimod eW).weightSupport E i)
    (β : M.Bases)
    (hβ : IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
      (M.boxCost T hunimod eW E) β.val) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, 1 ≤ r →
      ∀ q ∈ M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) E β r 1,
        dist 1 (F.inclusionN q) / r ≤ C := by
  obtain ⟨C, hC, hmetric⟩ := M.exists_uniform_suffix_metric_bound T F hunimod eW
    hExp realize haarN dynkinN b₀ hE hne hweights β hβ
  refine ⟨C, hC, ?_⟩
  intro r hr q hq
  have hR : HasSubexponentialUpperBoundSeq (fun _ : ℕ => r) (fun _ => 0) :=
    fun ε _ => Eventually.of_forall (fun _ => (Real.exp_pos (ε * r)).le)
  obtain ⟨n, hn⟩ := (hmetric 0 le_rfl zero_le_one (fun _ => r) (fun _ => 0)
    (fun _ => hr) hR).exists
  have hk : (1 : F.N.carrier) ∈ M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv)
      ((fun w => (1 + (0 : ℝ)) • w) '' E) β r 0 :=
    ⟨0, by simp [F.isExpN.map_zero], by simp⟩
  exact hn 1 hk q ⟨q, hq, mul_one q⟩

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_ExponentialBoxCompact
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Compactness of exponential coordinate boxes -/

noncomputable section
namespace PolycyclicRecognition

open Module

variable {L V G : Type} [LieRing L] [LieAlgebra ℝ L]
  [AddCommGroup V] [Module ℝ V] [TopologicalSpace V] [T2Space V]
  [IsTopologicalAddGroup V] [ContinuousSMul ℝ V]
  [TopologicalSpace G]

theorem isCompact_exponentialCoordinateBox {n : ℕ}
    (e : L ≃ₗ[ℝ] V) (Exp : V → G) (chart : V ≃ₜ G)
    (hchart : ∀ x, chart x = Exp x) (b : Basis (Fin n) ℝ L)
    (R : ℝ) (hR : 0 ≤ R) :
    IsCompact (exponentialCoordinateBox (Exp ∘ e) b R) := by
  rw [exponentialCoordinateBox_eq_cube_image _ _ R hR]
  have hf : ((Exp ∘ e) ∘ b.equivFun.symm) =
      chart ∘ (b.map e).equivFun.symm := by
    funext t
    simp only [Function.comp_apply, hchart, Basis.map_equivFun]
    rfl
  rw [hf]
  exact isCompact_Icc.image
    (chart.continuous.comp (b.map e).equivFun.symm.toContinuousLinearEquiv.continuous)

end PolycyclicRecognition

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
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_WeightSamplingSupport
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instNonemptyBases _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_nonempty _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact positive widths of the sampling polytope -/

noncomputable section
namespace PolycyclicRecognition

open Set

/-- Every defining halfspace is attained at its Euclidean contact point. -/
theorem weightSampling_support_eq_norm
    {W I : Type} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    [FiniteDimensional ℝ W] [Fintype I]
    (α : I → W →L[ℝ] ℝ) (hC : IsCompact (weightSamplingPolytope α))
    (i : I) (hi : α i ≠ 0) :
    sSup (α i '' weightSamplingPolytope α) = ‖α i‖ := by
  obtain ⟨p, hp, hval, _⟩ := exists_weight_contact_point (α i) hi
  have hpC : p ∈ weightSamplingPolytope α :=
    closedBall_subset_weightSamplingPolytope α (by simpa using hp.le)
  apply le_antisymm
  · have himg : (α i '' weightSamplingPolytope α).Nonempty := ⟨α i p, p, hpC, rfl⟩
    apply csSup_le himg
    rintro _ ⟨x, hx, rfl⟩
    exact hx i
  · rw [← hval]
    exact le_csSup (hC.image (α i).continuous).bddAbove ⟨p, hpC, rfl⟩

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanSamplingParameters
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_nonempty _root_.OAI.PolycyclicRecognition.finite_templateSymmetryGroup _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.instFiniteRootOffsetConeIndex _root_.OAI.PolycyclicRecognition.instFiniteSubtypeLinearEquivRealIdMemSubgroupLinearSupportSymmetryGroup _root_.OAI.PolycyclicRecognition.instNonemptyRootOffsetConeIndex _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
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

set_option maxHeartbeats 1000000 in
theorem sampling_weightSupport_eq (i : Fin M.letterCount) :
    (M.supportIn T hunimod eW).weightSupport (M.samplingPolytope T hunimod eW) i =
      ‖((M.supportIn T hunimod eW).weight i).toContinuousLinearMap‖ :=
  weightSampling_support_eq_norm _ (M.isCompact_samplingPolytope T hunimod eW)
    i (M.sampling_weight_ne_zero T hunimod eW i)

set_option maxHeartbeats 1000000 in
theorem sampling_weightSupport_pos (i : Fin M.letterCount) :
    0 < (M.supportIn T hunimod eW).weightSupport (M.samplingPolytope T hunimod eW) i := by
  rw [M.sampling_weightSupport_eq T hunimod eW i]
  exact norm_pos_iff.mpr (M.sampling_weight_ne_zero T hunimod eW i)

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanPublishedMixedScaleConcentration
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_nonempty _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.unitaryCentralFixed_complete _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.CartanFactorModel.realScaleProfile_apply _root_.OAI.PolycyclicRecognition.basisDynkinParameter_zero _root_.OAI.PolycyclicRecognition.bracketWordDifferential_mul _root_.OAI.PolycyclicRecognition.cartanWeightDerivation_apply_root _root_.OAI.PolycyclicRecognition.chartExponentialFlow_zero _root_.OAI.PolycyclicRecognition.derivationSemidirectHom_apply _root_.OAI.PolycyclicRecognition.exponentialHomOfDynkin_apply_exp _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.modelNilradicalLinearAction_apply _root_.OAI.PolycyclicRecognition.modelNilradicalRotation_apply _root_.OAI.PolycyclicRecognition.modelNilradicalRotation_mul _root_.OAI.PolycyclicRecognition.modelNilradicalRotation_one _root_.OAI.PolycyclicRecognition.nilshadowWeightDerivation_symm _root_.OAI.PolycyclicRecognition.nilshadowWeightOperator_symm _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual Haar profile comparison across adjacent physical scales -/

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
/-- Ordinary samples at nearby scales have asymptotically identical
scale-r profiles. The suffix bounds and the target density constant are
constructed from the original boxes. -/
theorem exists_uniform_published_mixed_scale_concentration
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
        (transformedPolarCone (rootOffsetCone (M.supportIn T hunimod eW) hnz i s) A.val)))
    (hweightB : ∀ i, (M.supportIn T hunimod eW).weightSupport Eall i ≤ B)
    :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
      ∀ (scale : ℕ → ℝ) (_hgrows : Tendsto scale atTop atTop)
        (_hmono : StrictMono scale) (_hs1 : ∀ n, 1 ≤ scale n),
      ∀ Z : Set (Fin (finrank ℝ H) → ℝ), ∀ _ : CompactSpace Z,
      (∀ z ∈ Z, eW (heightProjection T.character
        ((WordBasisSelections.basis X (boundedBracketWords d) βD).equivFun.symm z :
          GroupLieAlgebra (𝓘(ℝ, EG)) G)) ∈ (fun w => (1 - c * δ) • w) '' interior Eall) →
      ∀ (targetScale : ℕ → ℝ),
      (∀ n, scale n ≤ targetScale n) →
      (∀ n, targetScale n ≤ (1 + δ) * scale n) →
      ∀ (pair : ℕ → NormalizedPair G Λ) (center : ℕ → G)
    (raw : ℕ → F.N.carrier → C((Fin (finrank ℝ H) → ℝ), W))
    (_hraw : ∀ n q z, raw n q z = rescaledMapProfile
      (fun g => (π ((pair n).val.1 g)).toAdd) (center n) (F.inclusionN q)
      (max (Real.log (scale n)) 0)
      (F.profileChart (exponentialRescaleBasis
        (WordBasisSelections.basis X (boundedBracketWords d) βD)
        (fun j => bracketWordExponent (fun _ : I => 1) (βD.val j))
        (max (Real.log (scale n)) 0))) z)
    {η : ℝ} (_hη : 0 < η),
    Tendsto (fun n => (M.translatedGroupBoxProbability T F hunimod eW
      haarN chartN hchartN bN Eall γ (scale n) 1 : Measure F.N.carrier).prod
      (M.translatedGroupBoxProbability T F hunimod eW
        haarN chartN hchartN bN Eall γ (targetScale n) 1 : Measure F.N.carrier)
      {p | η ≤ dist ((raw n p.2).restrict Z) ((raw n p.1).restrict Z)})
      atTop (𝓝 0) := by
  obtain ⟨δ₀, hδ₀, hconc⟩ := M.exists_uniform_published_suffix_concentration T F hunimod eW
    hExp hinj realize haarN haarD dynkinN dynkinD chartN hchartN chartD hchartD m νD
    π hπExp hdec hvan hΛ hπ hpath bN γ hγ X hDnil hDletters bD₀ βD hβD
    aN hmN aD hmD rem hdim pivot hcanonical hunit hcontact hpositive
    hc hhi hB hcost hgap σchamber hσchamber hnz
    sourceInputs sourceDynkin targetInputs hweightB
  obtain ⟨D, hD1, hcover⟩ := M.exists_mixed_scale_box_difference_cover T hunimod eW
    F.N.equiv F.ExpN F.isExpN dynkinN bN
  refine ⟨δ₀, hδ₀, ?_⟩
  intro δ hδ hd scale hgrows hmono hs1 Z hZ hZheight targetScale hscaleLe htargetLe pair center raw hraw η hη
  let := hZ
  let μ := Measure.map ((F.ExpN ∘ F.N.equiv) ∘ bN.equivFun.symm) volume
  let : μ.IsHaarMeasure := exponential_basis_measure_isHaar haarN F.N.equiv
    (cartanRootIdeal_nilpotent H T) F.ExpN F.isExpN bN
  let C n := M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) Eall γ (scale n) 1
  let C' n := M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) Eall γ (targetScale n) 1
  let Q n := M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) Eall γ (targetScale n) D
  have hCp n := M.groupBox_radius_properties T F hunimod eW haarN chartN hchartN
    bN Eall γ (scale n) zero_lt_one
  have hC'p n := M.groupBox_radius_properties T F hunimod eW haarN chartN hchartN
    bN Eall γ (targetScale n) zero_lt_one
  have hQp n := M.groupBox_radius_properties T F hunimod eW haarN chartN hchartN
    bN Eall γ (targetScale n) (zero_lt_one.trans_le hD1)
  let J := fun n g => (π ((pair n).val.1 g)).toAdd
  have hJ n : LipschitzWith (Kπ * Λ) (J n) := hπ.comp (pair n).property.1.1
  let r n := max (Real.log (scale n)) 0
  let φ := fun n => F.profileChart (exponentialRescaleBasis
    (WordBasisSelections.basis X (boundedBracketWords d) βD)
    (fun j => bracketWordExponent (fun _ : I => 1) (βD.val j)) (r n))
  have hφ n : Continuous (φ n) :=
    F.continuous_profileChart (funext hchartD ▸ chartD.continuous) _
  have hrawcont n : Continuous (raw n) := by
    have heq : raw n = fun q => rescaledContinuousProfile (J n) (hJ n).continuous
        (center n) (F.inclusionN q) (r n) (φ n) (hφ n) := by
      funext q
      ext z
      exact hraw n q z
    rw [heq]
    exact (continuous_rescaledContinuousProfile (J n) (hJ n).continuous
      (center n) (r n) (φ n) (hφ n)).comp F.closedN.continuous
  let bad n := {p : F.N.carrier × F.N.carrier |
    η ≤ dist ((raw n p.2).restrict Z) ((raw n p.1).restrict Z)}
  have hbad n : MeasurableSet (bad n) :=
    (isClosed_le continuous_const
      (((ContinuousMap.continuous_restrict Z).comp ((hrawcont n).comp continuous_snd)).dist
        ((ContinuousMap.continuous_restrict Z).comp ((hrawcont n).comp continuous_fst)))).measurableSet
  have hp (k : ℕ → F.N.carrier) (hk : ∀ n, k n ∈ Q n) :=
    hconc δ hδ hd scale hgrows hmono hs1 Z hZ hZheight pair center (fun _ => D)
      (fun _ => zero_le_one.trans hD1) (sequence_subexponential_upper_const hgrows D) k
      (fun n => M.groupBox_scale_le_enlargement T hunimod eW (F.ExpN ∘ F.N.equiv)
        (M.isCompact_samplingPolytope T hunimod eW)
        ⟨0, fun i => by simp only [map_zero]; exact norm_nonneg _⟩
        (fun w => (bracketWordExponent_pos _ (M.sampling_weightSupport_pos T hunimod eW) w).le)
        γ hδ.le (htargetLe n) (hk n)) raw hraw hη
  have hiid := mixed_cell_concentration μ C C' Q
    (fun n => (hCp n).1) (fun n => (hC'p n).1) (fun n => (hQp n).1)
    (fun n => (hCp n).2.1) (fun n => (hCp n).2.2.1)
    (fun n => (hC'p n).2.1) (fun n => (hC'p n).2.2.1)
    (fun n => (hQp n).2.1) (fun n => (hQp n).2.2.1)
    (fun n => hcover Eall γ hγ
      (fun w => (bracketWordExponent_pos _ (M.sampling_weightSupport_pos T hunimod eW) w).le)
      (scale n) (targetScale n) (zero_le_one.trans ((hs1 n).trans (hscaleLe n))) (hscaleLe n))
    (K := ENNReal.ofReal D ^ finrank ℝ (cartanRootIdeal H)) (by simp)
    (fun n => (hQp n).2.2.2.le) bad hbad (by
      intro k hk
      simpa only [translatedGroupBoxProbability, mul_one, image_id', μ, C, bad, mem_ofPred_eq] using hp k hk)
  simpa only [translatedGroupBoxProbability, mul_one, image_id', μ, C, C', bad] using hiid

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanPublishedScaleStabilization
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_nonempty _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.unitaryCentralFixed_complete _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Published-input comparison of canonical affine labels at adjacent scales -/

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
/-- The canonical ordinary-cell labels agree across nearby scales, and their
mean offsets agree after conversion to the source-scale normalization. -/
theorem exists_published_adjacent_scale_labels
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
        (transformedPolarCone (rootOffsetCone (M.supportIn T hunimod eW) hnz i s) A.val)))
    (hweightB : ∀ i, (M.supportIn T hunimod eW).weightSupport Eall i ≤ B)
    :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
      ∀ (scale : ℕ → ℝ) (_hgrows : Tendsto scale atTop atTop)
        (_hmono : StrictMono scale) (_hs1 : ∀ n, 1 ≤ scale n)
        (targetScale : ℕ → ℝ) (_htmono : StrictMono targetScale),
      (∀ n, scale n ≤ targetScale n) →
      (∀ n, targetScale n ≤ (1 + δ) * scale n) →
      ∀ R : ℝ, 0 < R →
      (∀ z ∈ Metric.closedBall (0 : Fin (finrank ℝ H) → ℝ) R,
        eW (heightProjection T.character
          ((WordBasisSelections.basis X (boundedBracketWords d) βD).equivFun.symm z :
            GroupLieAlgebra (𝓘(ℝ, EG)) G)) ∈
          (fun w => (1 - c * δ) • w) '' interior Eall) →
      ∀ (pair : ℕ → NormalizedPair G Λ) (center : ℕ → G)
        (raw raw' : ℕ → F.N.carrier → C((Fin (finrank ℝ H) → ℝ), W)),
      (∀ n k z, raw n k z = rescaledMapProfile
        (fun g => (π ((pair n).val.1 g)).toAdd) (center n) (F.inclusionN k)
        (max (Real.log (scale n)) 0)
        (F.profileChart (exponentialRescaleBasis
          (WordBasisSelections.basis X (boundedBracketWords d) βD)
          (fun j => bracketWordExponent (fun _ : I => 1) (βD.val j))
          (max (Real.log (scale n)) 0))) z) →
      (∀ n k z, raw' n k z = rescaledMapProfile
        (fun g => (π ((pair n).val.1 g)).toAdd) (center n) (F.inclusionN k)
        (max (Real.log (targetScale n)) 0)
        (F.profileChart (exponentialRescaleBasis
          (WordBasisSelections.basis X (boundedBracketWords d) βD)
          (fun j => bracketWordExponent (fun _ : I => 1) (βD.val j))
          (max (Real.log (targetScale n)) 0))) z) →
      let Z := Metric.closedBall (0 : Fin (finrank ℝ H) → ℝ) R
      let bD := WordBasisSelections.basis X (boundedBracketWords d) βD
      let q := ((eW.toLinearMap.comp (heightProjection T.character)).comp
        (H.subtype.comp bD.equivFun.symm.toLinearMap)).toContinuousLinearMap
      let A := fun L : templateSymmetryGroup (M.supportIn T hunimod eW) =>
        (⟨fun z => L.val (q z), L.val.toContinuousLinearEquiv.continuous.comp q.continuous⟩ :
          C((Fin (finrank ℝ H) → ℝ), W)).restrict Z
      let μ := fun n => M.translatedGroupBoxProbability T F hunimod eW
        haarN chartN hchartN bN Eall γ (scale n) 1
      let ν := fun n => M.translatedGroupBoxProbability T F hunimod eW
        haarN chartN hchartN bN Eall γ (targetScale n) 1
      let b := fun n => ∫ k, raw n k 0 ∂(μ n : Measure F.N.carrier)
      let b' := fun n => ∫ k, raw' n k 0 ∂(ν n : Measure F.N.carrier)
      let label := fun n => canonicalAffineLabel (μ n : Measure F.N.carrier)
        (fun k => (raw n k).restrict Z) (fun L => A L + ContinuousMap.const Z (b n))
      let label' := fun n => canonicalAffineLabel (ν n : Measure F.N.carrier)
        (fun k => (raw' n k).restrict Z) (fun L => A L + ContinuousMap.const Z (b' n))
      (∀ᶠ n in atTop, label n = label' n) ∧
        Tendsto (fun n => dist (b n) ((targetScale n / scale n) • b' n)) atTop (𝓝 0) := by
  classical
  obtain ⟨δ₁, hδ₁, hmean₁⟩ := M.exists_uniform_published_affine_mean_approximation T F hunimod eW
    hExp hinj realize haarN haarD dynkinN dynkinD chartN hchartN chartD hchartD m νD
    π hπExp hdec hvan hΛ hπ hpath bN γ hγ X hDnil hDletters bD₀ βD hβD
    aN hmN aD hmD rem hdim pivot hcanonical hunit hcontact hpositive
    hc hhi hB hcost hgap σchamber hσchamber hnz
    sourceInputs sourceDynkin targetInputs hweightB
  obtain ⟨δ₂, hδ₂, hmean₂⟩ := M.exists_uniform_published_affine_mean_approximation T F hunimod eW
    hExp hinj realize haarN haarD dynkinN dynkinD chartN hchartN chartD hchartD m νD
    π hπExp hdec hvan hΛ hπ hpath bN γ hγ X hDnil hDletters bD₀ βD hβD
    aN hmN aD hmD rem hdim pivot hcanonical hunit hcontact hpositive
    hc hhi hB hcost hgap σchamber hσchamber hnz
    sourceInputs sourceDynkin targetInputs hweightB
  obtain ⟨δ₃, hδ₃, hpair⟩ := M.exists_uniform_published_mixed_scale_concentration T F hunimod eW
    hExp hinj realize haarN haarD dynkinN dynkinD chartN hchartN chartD hchartD m νD
    π hπExp hdec hvan hΛ hπ hpath bN γ hγ X hDnil hDletters bD₀ βD hβD
    aN hmN aD hmD rem hdim pivot hcanonical hunit hcontact hpositive
    hc hhi hB hcost hgap σchamber hσchamber hnz
    sourceInputs sourceDynkin targetInputs hweightB
  refine ⟨min δ₁ (min δ₂ δ₃), lt_min hδ₁ (lt_min hδ₂ hδ₃), ?_⟩
  intro δ hδ hd scale hgrows hmono hs1 targetScale htmono hscaleLe hratio R hR hZheight
    pair center raw raw' hraw hraw'
  have ht1 : ∀ n, 1 ≤ targetScale n := fun n => (hs1 n).trans (hscaleLe n)
  have htgrow : Tendsto targetScale atTop atTop := tendsto_atTop_mono hscaleLe hgrows
  dsimp only
  let Z := Metric.closedBall (0 : Fin (finrank ℝ H) → ℝ) R
  let height : H →ₗ[ℝ] W := eW.toLinearMap.comp ((heightProjection T.character).comp H.subtype)
  have hheight : Function.Surjective height := eW.surjective.comp (cartan_height_surjective T H)
  have hkill (u v : H) : height ⁅u, v⁆ = 0 := by
    change eW (heightProjection T.character (⁅u, v⁆ : H)) = 0
    rw [LieSubalgebra.coe_bracket, heightProjection_lie_eq_zero T.character T.character_lie,
      map_zero]
  let μ := fun n => M.translatedGroupBoxProbability T F hunimod eW
    haarN chartN hchartN bN Eall γ (scale n) 1
  let ν := fun n => M.translatedGroupBoxProbability T F hunimod eW
    haarN chartN hchartN bN Eall γ (targetScale n) 1
  let C := fun n => M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) Eall γ (scale n) 1
  let D := fun n => M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) Eall γ (targetScale n) 1
  have hcompact (s : ℕ → ℝ) n : IsCompact
      (M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) Eall γ (s n) 1) :=
    isCompact_exponentialCoordinateBox F.N.equiv.toLinearEquiv F.ExpN chartN hchartN
      (M.boxBasis T hunimod eW Eall γ (s n)) 1 zero_le_one
  have hfull (s : ℕ → ℝ) n : ∀ᵐ k ∂(M.translatedGroupBoxProbability T F hunimod eW
      haarN chartN hchartN bN Eall γ (s n) 1 : Measure F.N.carrier),
      k ∈ M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) Eall γ (s n) 1 := by
    have hh := M.groupBox_radius_properties T F hunimod eW haarN chartN hchartN bN
      Eall γ (s n) zero_lt_one
    simpa only [translatedGroupBoxProbability, mul_one, image_id'] using
      ae_mem_cellProbabilityMeasure
        (Measure.map ((F.ExpN ∘ F.N.equiv) ∘ bN.equivFun.symm) volume)
        _ hh.1 hh.2.1 hh.2.2.1
  have hz : (0 : Fin (finrank ℝ H) → ℝ) ∈ Z := Metric.mem_closedBall_self hR.le
  have hh := F.adjacent_scale_labels_of_approximation
    (funext hchartD ▸ chartD.continuous) height hheight hkill
    (fun L : templateSymmetryGroup (M.supportIn T hunimod eW) => L.val) Subtype.val_injective
    X (boundedBracketWords d) βD μ ν C D (hcompact scale) (hcompact targetScale)
    (hfull scale) (hfull targetScale) scale targetScale hs1 hscaleLe
    (K := 1 + δ) (by linarith) hratio
    (fun n g => (π ((pair n).val.1 g)).toAdd)
    (fun n => (hπ.comp (pair n).property.1.1).continuous) center raw raw'
    (by simpa only [bracketWordExponent_one] using hraw)
    (by simpa only [bracketWordExponent_one] using hraw') R hR
    (hmean₁ δ hδ (hd.trans (min_le_left _ _)) scale hgrows hmono hs1 Z inferInstance hZheight hz pair center raw hraw)
    (hmean₂ δ hδ (hd.trans ((min_le_right _ _).trans (min_le_left _ _)))
      targetScale htgrow htmono ht1 Z inferInstance hZheight hz pair center raw' hraw')
    (fun ε hε => by
      simpa only [μ, ν, dist_comm] using
        hpair δ hδ (hd.trans ((min_le_right _ _).trans (min_le_right _ _)))
          scale hgrows hmono hs1 Z inferInstance hZheight targetScale hscaleLe hratio pair center raw hraw hε)
  simpa only [μ, ν, height, Z, LinearMap.comp_assoc] using hh

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanPublishedUniformScale
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_nonempty _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.unitaryCentralFixed_complete _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform scale stabilization and vanishing mean offsets -/

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
/-- The scale-stabilization lemma for the original Haar profiles, uniformly
over all normalized maps and centers, from the precise published inputs. -/
theorem exists_published_uniform_scale_stabilization
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
        (transformedPolarCone (rootOffsetCone (M.supportIn T hunimod eW) hnz i s) A.val)))
    (hweightB : ∀ i, (M.supportIn T hunimod eW).weightSupport Eall i ≤ B)
    :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
      ∀ R : ℝ, 0 < R →
      (∀ z ∈ Metric.closedBall (0 : Fin (finrank ℝ H) → ℝ) R,
        eW (heightProjection T.character
          ((WordBasisSelections.basis X (boundedBracketWords d) βD).equivFun.symm z :
            GroupLieAlgebra (𝓘(ℝ, EG)) G)) ∈
          (fun w => (1 - c * δ) • w) '' interior Eall) →
      let Z := Metric.closedBall (0 : Fin (finrank ℝ H) → ℝ) R
      let bD := WordBasisSelections.basis X (boundedBracketWords d) βD
      let q := ((eW.toLinearMap.comp (heightProjection T.character)).comp
        (H.subtype.comp bD.equivFun.symm.toLinearMap)).toContinuousLinearMap
      let A := fun L : templateSymmetryGroup (M.supportIn T hunimod eW) =>
        (⟨fun z => L.val (q z), L.val.toContinuousLinearEquiv.continuous.comp q.continuous⟩ :
          C((Fin (finrank ℝ H) → ℝ), W)).restrict Z
      let μ := fun r => M.translatedGroupBoxProbability T F hunimod eW
        haarN chartN hchartN bN Eall γ r 1
      let raw := fun (p : NormalizedPair G Λ × G) r =>
        F.realScaleProfile (funext hchartD ▸ chartD.continuous)
          (fun g => (π (p.1.val.1 g)).toAdd) (hπ.comp p.1.property.1.1).continuous
          p.2 X (boundedBracketWords d) βD r
      let b := fun p r => ∫ k, raw p r k 0 ∂(μ r : Measure F.N.carrier)
      let label := fun p r => canonicalAffineLabel (μ r : Measure F.N.carrier)
        (fun k => (raw p r k).restrict Z) (fun L => A L + ContinuousMap.const Z (b p r))
      (∃ R₀ : ℝ, 1 ≤ R₀ ∧ ∀ p r, R₀ ≤ r → label p r = label p R₀) ∧
      (∀ ε : ℝ, 0 < ε → ∃ R₀ : ℝ, 1 ≤ R₀ ∧ ∀ p r, R₀ ≤ r → ‖b p r‖ ≤ ε) := by
  obtain ⟨δ₀, hδ₀, hcompare⟩ := M.exists_published_adjacent_scale_labels T F hunimod eW
    hExp hinj realize haarN haarD dynkinN dynkinD chartN hchartN chartD hchartD m νD
    π hπExp hdec hvan hΛ hπ hpath bN γ hγ X hDnil hDletters bD₀ βD hβD
    aN hmN aD hmD rem hdim pivot hcanonical hunit hcontact hpositive
    hc hhi hB hcost hgap σchamber hσchamber hnz
    sourceInputs sourceDynkin targetInputs hweightB
  refine ⟨δ₀, hδ₀, ?_⟩
  intro δ hδ hd R hR hZheight
  dsimp only
  let Z := Metric.closedBall (0 : Fin (finrank ℝ H) → ℝ) R
  let bD := WordBasisSelections.basis X (boundedBracketWords d) βD
  let q := ((eW.toLinearMap.comp (heightProjection T.character)).comp
    (H.subtype.comp bD.equivFun.symm.toLinearMap)).toContinuousLinearMap
  let A := fun L : templateSymmetryGroup (M.supportIn T hunimod eW) =>
    (⟨fun z => L.val (q z), L.val.toContinuousLinearEquiv.continuous.comp q.continuous⟩ :
      C((Fin (finrank ℝ H) → ℝ), W)).restrict Z
  let μ := fun r => M.translatedGroupBoxProbability T F hunimod eW
    haarN chartN hchartN bN Eall γ r 1
  let J := fun (p : NormalizedPair G Λ × G) g => (π (p.1.val.1 g)).toAdd
  have hJ p : LipschitzWith (Kπ * Λ) (J p) := hπ.comp p.1.property.1.1
  let raw := fun (p : NormalizedPair G Λ × G) r =>
    F.realScaleProfile (funext hchartD ▸ chartD.continuous) (J p) (hJ p).continuous
      p.2 X (boundedBracketWords d) βD r
  let b := fun p r => ∫ k, raw p r k 0 ∂(μ r : Measure F.N.carrier)
  let label := fun p r => canonicalAffineLabel (μ r : Measure F.N.carrier)
    (fun k => (raw p r k).restrict Z) (fun L => A L + ContinuousMap.const Z (b p r))
  have hE := M.isCompact_samplingPolytope T hunimod eW
  have hne : (Eall).Nonempty := ⟨0, fun i => by simp only [map_zero]; exact norm_nonneg _⟩
  obtain ⟨C, _, hmetric⟩ := M.exists_ordinary_cell_metric_bound T F hunimod eW
    hExp realize haarN dynkinN bN hE hne (M.sampling_weightSupport_pos T hunimod eW) γ hγ
  have hfull r : ∀ᵐ k ∂(μ r : Measure F.N.carrier),
      k ∈ M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) Eall γ r 1 := by
    have hh := M.groupBox_radius_properties T F hunimod eW haarN chartN hchartN bN
      Eall γ r zero_lt_one
    simpa only [μ, translatedGroupBoxProbability, mul_one, image_id'] using
      ae_mem_cellProbabilityMeasure
        (Measure.map ((F.ExpN ∘ F.N.equiv) ∘ bN.equivFun.symm) volume)
        _ hh.1 hh.2.1 hh.2.2.1
  have hb p r (hr : 1 ≤ r) : ‖b p r‖ ≤ (Kπ * Λ : ℝ≥0) * C := by
    apply F.realScaleProfile_mean_norm_le (funext hchartD ▸ chartD.continuous)
      (J p) (hJ p) p.2 X (boundedBracketWords d) βD hr (μ r)
    filter_upwards [hfull r] with k hk
    exact hmetric r hr k hk
  apply uniform_scale_stabilization_of_sequences label b (Q := 1 + δ) (by linarith) hb
  intro p r t hrg hr ht hr1 hrt htQ
  have hh := hcompare δ hδ hd r hrg hr hr1 t ht hrt htQ R hR hZheight
    (fun n => (p n).1) (fun n => (p n).2)
    (fun n => raw (p n) (r n)) (fun n => raw (p n) (t n))
    (fun _ _ _ => rfl) (fun _ _ _ => rfl)
  exact hh

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_UniformBasepointHeight
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A uniform sublinear height error from stabilized basepoint labels -/

namespace PolycyclicRecognition
open Filter
open scoped Topology

/-- Scale stabilization and the proved basepoint comparison select one
linear label per map, uniformly at all centers. The error is sublinear
uniformly in the map and in the two centers. -/
theorem uniform_sublinear_height_of_stable_labels
    {P G L W : Type} [Group G] [PseudoMetricSpace G]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (label : P → G → ℝ → L) (A : L → W →L[ℝ] W)
    (J : P → G → W) (π : G → W)
    {r₀ t η : ℝ} (ht : 0 < t) (hη : 0 < η)
    (hstable : ∀ p x r, r₀ ≤ r → label p x r = label p x r₀)
    (hcompare : ∀ (scale : ℕ → ℝ), Tendsto scale atTop atTop → StrictMono scale →
      (∀ n, 1 ≤ scale n) → (∀ n, 1 ≤ t * scale n) →
      ∀ (p : ℕ → P) (x y : ℕ → G), (∀ n, dist (x n) (y n) ≤ η * scale n) →
      (∀ᶠ n in atTop, label (p n) (x n) (scale n) = label (p n) (y n) (t * scale n)) ∧
      Tendsto (fun n => (scale n)⁻¹ • (J (p n) (y n) - J (p n) (x n) -
        A (label (p n) (y n) (t * scale n)) (π ((x n)⁻¹ * y n)))) atTop (𝓝 0)) :
    ∃ a : P → L,
      (∀ p x r, r₀ ≤ r → label p x r = a p) ∧
      (∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 1 ≤ R ∧ ∀ p x y r,
        R ≤ r → dist x y ≤ η * r →
          ‖J p y - J p x - A (a p) (π (x⁻¹ * y))‖ ≤ ε * r) := by
  have hc := stable_label_independent_of_center label ht hη hstable
    (fun scale hg hs h1 ht1 p x y hd =>
      (hcompare scale hg hs h1 ht1 (fun _ => p) (fun _ => x) (fun _ => y) hd).1)
  let a := fun p => label p 1 r₀
  have ha p x r (hr : r₀ ≤ r) : label p x r = a p :=
    (hstable p x r hr).trans (hc p x 1)
  refine ⟨a, ha, ?_⟩
  apply uniform_local_norm_bound_of_sequences
    (fun p x y => J p y - J p x - A (a p) (π (x⁻¹ * y))) ht
  intro scale hg hs h1 ht1 p x y hd
  have hh := (hcompare scale hg hs h1 ht1 p x y hd).2
  apply hh.congr'
  filter_upwards [(hg.const_mul_atTop ht).eventually_ge_atTop r₀] with n hn
  rw [ha (p n) (y n) _ hn]

/-- A uniform error bound on expanding metric balls has the usual global
sublinear form, including an additive constant for the bounded initial range. -/
theorem uniform_sublinear_of_local_radius_bound
    {P X W : Type} [PseudoMetricSpace X] [NormedAddCommGroup W]
    (error : P → X → X → W) {η : ℝ} (hη : 0 < η)
    (hlocal : ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 1 ≤ R ∧ ∀ p x y r,
      R ≤ r → dist x y ≤ η * r → ‖error p x y‖ ≤ ε * r) :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧ ∀ p x y,
      ‖error p x y‖ ≤ ε * dist x y + C := by
  intro ε hε
  obtain ⟨R, hR, hb⟩ := hlocal (ε * η) (mul_pos hε hη)
  refine ⟨ε * η * R, mul_nonneg (mul_pos hε hη).le (zero_le_one.trans hR), ?_⟩
  intro p x y
  have hr : R ≤ R + dist x y / η := le_add_of_nonneg_right (div_nonneg dist_nonneg hη.le)
  have hd : dist x y ≤ η * (R + dist x y / η) := by
    have he : η * (dist x y / η) = dist x y := by field_simp
    rw [mul_add, he]
    exact le_add_of_nonneg_left (mul_nonneg hη.le (zero_le_one.trans hR))
  have he : ε * η * (R + dist x y / η) = ε * dist x y + ε * η * R := by
    field_simp
    ring
  exact (hb p x y _ hr hd).trans_eq he

end PolycyclicRecognition

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanPublishedSublinearHeight
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_nonempty _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.unitaryCentralFixed_complete _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.basisDynkinParameter_zero _root_.OAI.PolycyclicRecognition.bracketWordDifferential_mul _root_.OAI.PolycyclicRecognition.cartanWeightDerivation_apply_root _root_.OAI.PolycyclicRecognition.chartExponentialFlow_zero _root_.OAI.PolycyclicRecognition.derivationSemidirectHom_apply _root_.OAI.PolycyclicRecognition.exponentialHomOfDynkin_apply_exp _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.modelNilradicalLinearAction_apply _root_.OAI.PolycyclicRecognition.modelNilradicalRotation_apply _root_.OAI.PolycyclicRecognition.modelNilradicalRotation_mul _root_.OAI.PolycyclicRecognition.modelNilradicalRotation_one _root_.OAI.PolycyclicRecognition.nilshadowWeightDerivation_symm _root_.OAI.PolycyclicRecognition.nilshadowWeightOperator_symm _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform sublinear affine height from precisely published inputs -/

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
/-- The stabilized finite label is independent of the basepoint, and the
height error is sublinear uniformly over normalized maps and centers. -/
theorem exists_uniform_published_sublinear_height
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
        (transformedPolarCone (rootOffsetCone (M.supportIn T hunimod eW) hnz i s) A.val)))
    (hweightB : ∀ i, (M.supportIn T hunimod eW).weightSupport Eall i ≤ B)
    :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
      ∀ R : ℝ, 0 < R →
      (∀ z ∈ Metric.closedBall (0 : Fin (finrank ℝ H) → ℝ) R,
        eW (heightProjection T.character
          ((WordBasisSelections.basis X (boundedBracketWords d) βD).equivFun.symm z :
            GroupLieAlgebra (𝓘(ℝ, EG)) G)) ∈
          (fun w => (1 - c * δ) • w) '' interior Eall) →
      ∃ A : NormalizedPair G Λ → templateSymmetryGroup (M.supportIn T hunimod eW),
      ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, 0 ≤ B ∧ ∀ p x y,
        ‖(π (p.val.1 y)).toAdd - (π (p.val.1 x)).toAdd - (A p).val ((π (x⁻¹ * y)).toAdd)‖ ≤
          ε * dist x y + B := by
  classical
  obtain ⟨δ₁, hδ₁, hbase⟩ := M.exists_uniform_published_basepoint_comparison T F hunimod eW
    hExp hinj realize haarN haarD dynkinN dynkinD chartN hchartN chartD hchartD m νD
    π hπExp hdec hvan hΛ hπ hpath bN γ hγ X hDnil hDletters bD₀ βD hβD
    aN hmN aD hmD rem hdim pivot hcanonical hunit hcontact hpositive
    hc hhi hB hcost hgap σchamber hσchamber hnz sourceInputs sourceDynkin targetInputs hweightB
  obtain ⟨δ₂, hδ₂, hscale⟩ := M.exists_published_uniform_scale_stabilization T F hunimod eW
    hExp hinj realize haarN haarD dynkinN dynkinD chartN hchartN chartD hchartD m νD
    π hπExp hdec hvan hΛ hπ hpath bN γ hγ X hDnil hDletters bD₀ βD hβD
    aN hmN aD hmD rem hdim pivot hcanonical hunit hcontact hpositive
    hc hhi hB hcost hgap σchamber hσchamber hnz sourceInputs sourceDynkin targetInputs hweightB
  refine ⟨min (1 / 2) (min δ₁ δ₂), lt_min (by norm_num) (lt_min hδ₁ hδ₂), ?_⟩
  intro δ hδ hd R hR hZheight
  have hd1 : δ ≤ δ₁ := hd.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hd2 : δ ≤ δ₂ := hd.trans ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨η, hη, hcompare⟩ := hbase δ hδ hd1 R hR hZheight
  obtain ⟨r₀, hr₀, hstable⟩ := (hscale δ hδ hd2 R hR hZheight).1
  let Z := Metric.closedBall (0 : Fin (finrank ℝ H) → ℝ) R
  let bD := WordBasisSelections.basis X (boundedBracketWords d) βD
  let q := ((eW.toLinearMap.comp (heightProjection T.character)).comp
    (H.subtype.comp bD.equivFun.symm.toLinearMap)).toContinuousLinearMap
  let A := fun L : templateSymmetryGroup (M.supportIn T hunimod eW) =>
    L.val.toContinuousLinearEquiv.toContinuousLinearMap
  let μ := fun r => M.translatedGroupBoxProbability T F hunimod eW
    haarN chartN hchartN bN Eall γ r 1
  let J := fun (p : NormalizedPair G Λ) g => (π (p.val.1 g)).toAdd
  let raw := fun (p : NormalizedPair G Λ × G) r =>
    F.realScaleProfile (funext hchartD ▸ chartD.continuous) (J p.1)
      (hπ.comp p.1.property.1.1).continuous p.2 X (boundedBracketWords d) βD r
  let b := fun p r => ∫ k, raw p r k 0 ∂(μ r : Measure F.N.carrier)
  let label := fun (p : NormalizedPair G Λ) x r => canonicalAffineLabel (μ r : Measure F.N.carrier)
    (fun k => (raw (p, x) r k).restrict Z)
    (fun L => linearBallProfile q (A L) R + ContinuousMap.const Z (b (p, x) r))
  have hδ1 : δ < 1 := lt_of_le_of_lt (hd.trans (min_le_left _ _)) (by norm_num)
  have ht : 0 < 1 - δ / 2 := by linarith only [hδ1]
  obtain ⟨a, _, hbound⟩ := uniform_sublinear_height_of_stable_labels label A J
    (fun g => (π g).toAdd) ht hη (fun p x r hr => hstable (p, x) r hr) hcompare
  refine ⟨a, ?_⟩
  exact uniform_sublinear_of_local_radius_bound
    (fun p x y => J p y - J p x - A (a p) ((π (x⁻¹ * y)).toAdd)) hη hbound

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_SmallHeightSamplingBall
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A genuine coordinate ball inside the shrunken sampling domain -/

noncomputable section
namespace PolycyclicRecognition

open Set Filter
open scoped Topology

variable {U W I : Type} [NormedAddCommGroup U] [NormedSpace ℝ U]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [Fintype I]

/-- Continuity at zero supplies the positive sampling radius; it is not
an extra geometric hypothesis. -/
theorem exists_small_height_sampling_ball (q : U →L[ℝ] W)
    (α : I → W →L[ℝ] ℝ) (hα : ∀ i, α i ≠ 0)
    {a : ℝ} (ha : 0 < a) :
    ∃ R : ℝ, 0 < R ∧ ∀ z ∈ Metric.closedBall (0 : U) R,
      q z ∈ (fun w : W => a • w) '' interior (weightSamplingPolytope α) := by
  have hz : (0 : W) ∈ interior (weightSamplingPolytope α) :=
    weightSamplingInterior_subset_interior α (zero_mem_weightSamplingInterior α hα)
  have hc : Continuous (fun z : U => a⁻¹ • q z) := continuous_const.smul q.continuous
  have hn : (fun z : U => a⁻¹ • q z) ⁻¹' interior (weightSamplingPolytope α) ∈ 𝓝 0 := by
    apply hc.continuousAt.preimage_mem_nhds
    simpa using isOpen_interior.mem_nhds hz
  obtain ⟨r, hr, hsub⟩ := Metric.mem_nhds_iff.mp hn
  refine ⟨r / 2, by positivity, fun z hz => ⟨a⁻¹ • q z, hsub ?_, ?_⟩⟩
  · exact (Metric.mem_ball.mpr ((Metric.mem_closedBall.mp hz).trans_lt (by linarith)))
  · simp [smul_smul, ha.ne']

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanPublishedHeightSelection
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_nonempty _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.unitaryCentralFixed_complete _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Selecting the small sampling scale from the published inputs -/

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
theorem exists_published_sublinear_height_oai
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
        (transformedPolarCone (rootOffsetCone (M.supportIn T hunimod eW) hnz i s) A.val)))
    (hweightB : ∀ i, (M.supportIn T hunimod eW).weightSupport Eall i ≤ B)
    :
    ∃ A : NormalizedPair G Λ → templateSymmetryGroup (M.supportIn T hunimod eW),
      ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, 0 ≤ B ∧ ∀ p x y,
        ‖(π (p.val.1 y)).toAdd - (π (p.val.1 x)).toAdd - (A p).val ((π (x⁻¹ * y)).toAdd)‖ ≤
          ε * dist x y + B := by
  obtain ⟨δ₀, hδ₀, hs⟩ := M.exists_uniform_published_sublinear_height T F hunimod eW
    hExp hinj realize haarN haarD dynkinN dynkinD chartN hchartN chartD hchartD m νD
    π hπExp hdec hvan hΛ hπ hpath bN γ hγ X hDnil hDletters bD₀ βD hβD
    aN hmN aD hmD rem hdim pivot hcanonical hunit hcontact hpositive
    hc hhi hB hcost hgap σchamber hσchamber hnz sourceInputs sourceDynkin targetInputs hweightB
  let δ := min δ₀ (1 / (2 * (c + 1)))
  have hδ : 0 < δ := lt_min hδ₀ (by positivity)
  have hd : δ ≤ δ₀ := min_le_left _ _
  have hsmall : δ * (2 * (c + 1)) ≤ 1 :=
    (le_div_iff₀ (by positivity : 0 < 2 * (c + 1))).mp (min_le_right _ _)
  have hfactor : 0 < 1 - c * δ := by
    nlinarith only [hsmall, hδ, mul_nonneg hc hδ.le]
  let bD := WordBasisSelections.basis X (boundedBracketWords d) βD
  let q := ((eW.toLinearMap.comp (heightProjection T.character)).comp
    (H.subtype.comp bD.equivFun.symm.toLinearMap)).toContinuousLinearMap
  obtain ⟨R, hR, hZ⟩ := exists_small_height_sampling_ball q
    (fun i => ((M.supportIn T hunimod eW).weight i).toContinuousLinearMap)
    (M.sampling_weight_ne_zero T hunimod eW) hfactor
  exact hs δ hδ hd R hR hZ

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

theorem solution : type_of% @OAI.PolycyclicRecognition.CartanWordModel.exists_published_sublinear_height_oai := @OAI.PolycyclicRecognition.CartanWordModel.exists_published_sublinear_height_oai
