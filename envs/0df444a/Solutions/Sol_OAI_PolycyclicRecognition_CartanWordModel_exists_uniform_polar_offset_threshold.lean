-- Prove2me | solution 1 for OAI.PolycyclicRecognition.CartanWordModel.exists_uniform_polar_offset_threshold
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-02T23:02:13.637174+00:00
-- url     : https://prove2.me/submissions/03d43398-43a4-41d6-8e55-44475c55e281

import Mathlib
import Definitions.Def_PolycyclicRecognition
import Definitions.Def_OAIQ093D027
import Theorems.Thm_OAI_PolycyclicRecognition_CartanWordModel_exists_one_cone_offset_threshold

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

omit [FiniteDimensional ℝ W] in
theorem basisTemplateSupport_le (E : Set W) (b : B) :
    D.basisTemplateSupport E b ≤ D.templateSupport E :=
  Finset.le_sup' (f := D.basisTemplateSupport E) (Finset.mem_univ b)

end PolycyclicRecognition.SupportDatum

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_PositiveWeightCones
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The positive parts of the ray and two-generator cones -/

noncomputable section
namespace PolycyclicRecognition

open Set
open scoped BigOperators

variable {V : Type} [AddCommGroup V] [Module ℝ V]

theorem zero_not_mem_positiveWeightRay {α : V} (hα : α ≠ 0) :
    (0 : V) ∉ positiveWeightRay α := by
  rintro ⟨c, hc, he⟩
  exact (smul_ne_zero (ne_of_gt hc) hα) he.symm

theorem positiveWeightCone_add (α η : V) :
    ∀ x ∈ positiveWeightCone α η, ∀ y ∈ positiveWeightCone α η,
      x + y ∈ positiveWeightCone α η := by
  rintro x ⟨a, b, ha, hb, hab, rfl⟩ y ⟨c, d, hc, hd, hcd, rfl⟩
  refine ⟨a + c, b + d, add_nonneg ha hc, add_nonneg hb hd, by linarith, ?_⟩
  simp only [add_smul]
  abel

theorem zero_not_mem_positiveWeightCone {α η : V} (h : LinearIndependent ℝ ![α, η]) :
    (0 : V) ∉ positiveWeightCone α η := by
  rintro ⟨c, d, _, _, hcd, he⟩
  have hh := h.eq_of_pair (s := c) (t := d) (s' := 0) (t' := 0) (by simpa using he.symm)
  simp only [hh.1, hh.2, add_zero, lt_self_iff_false] at hcd

/-- Positive integral multiplicities on a ray give a positive ray character. -/
theorem positive_sum_on_weightRay {I : Type} [Fintype I]
    (α : V) (β : I → V) (c : I → ℕ)
    (hout : ∀ i, β i ∉ positiveWeightRay α → c i = 0)
    (i₀ : I) (h₀ : β i₀ ∈ positiveWeightRay α) (hc₀ : 0 < c i₀) :
    ∃ a : ℝ, 0 < a ∧ ∑ i, (c i : ℝ) • β i = a • α := by
  classical
  have hd (i) : ∃ d : ℝ, 0 ≤ d ∧
      (c i : ℝ) • β i = ((c i : ℝ) * d) • α ∧
      (β i ∈ positiveWeightRay α → 0 < d) := by
    by_cases hi : β i ∈ positiveWeightRay α
    · obtain ⟨d, hd, he⟩ := hi
      exact ⟨d, hd.le, by rw [he, smul_smul], fun _ => hd⟩
    · exact ⟨0, le_rfl, by simp [hout i hi], fun h => False.elim (hi h)⟩
  choose d hd he hp using hd
  refine ⟨∑ i, (c i : ℝ) * d i, ?_, ?_⟩
  · exact lt_of_lt_of_le (mul_pos (Nat.cast_pos.mpr hc₀) (hp i₀ h₀))
      (Finset.single_le_sum (fun i _ => mul_nonneg (Nat.cast_nonneg _) (hd i))
        (Finset.mem_univ i₀))
  · simp_rw [he]
    rw [Finset.sum_smul]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_IndependentWeightCone
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The closed cones used by the neighboring-offset argument

A ray and a cone on two independent weights are closed. We construct them
as actual proper cones, so polar separation requires no closedness input.
-/

noncomputable section
namespace PolycyclicRecognition

open Set
open scoped BigOperators

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
  {I : Type} [Fintype I]

theorem closedWeightRay_eq_insert {α : V} (hα : α ≠ 0) :
    (closedWeightRay α hα : Set V) = insert 0 (positiveWeightRay α) := by
  ext β
  change β ∈ closedWeightRay α hα ↔ β ∈ insert 0 (positiveWeightRay α)
  rw [mem_closedWeightRay]
  constructor
  · rintro ⟨c, hc, rfl⟩
    obtain rfl | hc := eq_or_lt_of_le hc
    · simp
    · exact mem_insert_of_mem _ ⟨c, hc, rfl⟩
  · rintro (rfl | ⟨c, hc, rfl⟩)
    · exact ⟨0, le_rfl, by simp⟩
    · exact ⟨c, hc.le, rfl⟩

theorem closedTwoWeightCone_eq_insert (α η : V) (h : LinearIndependent ℝ ![α, η]) :
    (closedTwoWeightCone α η h : Set V) = insert 0 (positiveWeightCone α η) := by
  ext β
  change β ∈ closedTwoWeightCone α η h ↔ β ∈ insert 0 (positiveWeightCone α η)
  rw [mem_closedTwoWeightCone]
  constructor
  · rintro ⟨c, d, hc, hd, rfl⟩
    by_cases he : c + d = 0
    · have hc0 : c = 0 := by linarith
      have hd0 : d = 0 := by linarith
      simp [hc0, hd0]
    · exact mem_insert_of_mem _ ⟨c, d, hc, hd, lt_of_le_of_ne (add_nonneg hc hd) (Ne.symm he), rfl⟩
  · rintro (rfl | ⟨c, d, hc, hd, _, he⟩)
    · exact ⟨0, 0, le_rfl, le_rfl, by simp⟩
    · exact ⟨c, d, hc, hd, he⟩

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_SupportDirectionCap
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instNonemptyBases _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_nonempty _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Separating one unsupported direction by a small cap

The cap preserves all the supports in a finite list of directions and
strictly lowers support in a direction outside their positive rays.
-/

noncomputable section

namespace PolycyclicRecognition

open Set

variable {W I : Type} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
  [FiniteDimensional ℝ W] [Fintype I]

/-- A compact convex truncation of the unit ball leaves the prescribed
support values unchanged but strictly lowers support in any additional
direction not on their positive rays. -/
theorem exists_support_direction_cap (v : I → W) (b : W) (hb : b ≠ 0)
    (hnot : ∀ i (r : ℝ), 0 < r → b ≠ r • v i) :
    ∃ E : Set W, IsCompact E ∧ E.Nonempty ∧ Convex ℝ E ∧
      E ⊆ Metric.closedBall 0 1 ∧
      (∀ i, ∃ x ∈ E, inner ℝ (v i) x = ‖v i‖) ∧
      ∃ c : ℝ, c < ‖b‖ ∧ ∀ x ∈ E, inner ℝ b x ≤ c := by
  classical
  let u : I → W := fun i => ‖v i‖⁻¹ • v i
  have hunorm (i : I) : ‖u i‖ ≤ 1 := by
    by_cases hv : v i = 0
    · simp [u, hv]
    · have hvn : ‖v i‖ ≠ 0 := norm_ne_zero_iff.mpr hv
      simp [u, norm_smul, hvn]
  have huinner (i : I) : inner ℝ (v i) (u i) = ‖v i‖ := by
    by_cases hv : v i = 0
    · simp [u, hv]
    · have hvn : ‖v i‖ ≠ 0 := norm_ne_zero_iff.mpr hv
      simp only [u, real_inner_smul_right, real_inner_self_eq_norm_sq]
      field_simp
  have hult (i : I) : inner ℝ b (u i) < ‖b‖ := by
    by_cases hv : v i = 0
    · simpa [u, hv] using norm_pos_iff.mpr hb
    · have hvn : ‖v i‖ ≠ 0 := norm_ne_zero_iff.mpr hv
      have hunit : ‖u i‖ = 1 := by
        simp [u, norm_smul, hvn]
      have hne : ‖u i‖ • b ≠ ‖b‖ • u i := by
        intro heq
        have heq' : b = (‖b‖ / ‖v i‖) • v i := by
          simpa only [hunit, one_smul, u, smul_smul, div_eq_mul_inv] using heq
        exact hnot i (‖b‖ / ‖v i‖)
          (div_pos (norm_pos_iff.mpr hb) (norm_pos_iff.mpr hv)) heq'
      simpa only [hunit, mul_one] using (inner_lt_norm_mul_iff_real.mpr hne)
  let x : Option I → W := fun i => i.elim 0 u
  let c : ℝ := Finset.univ.sup' Finset.univ_nonempty (fun i : Option I => inner ℝ b (x i))
  have hc0 : 0 ≤ c := by
    have hh := Finset.le_sup' (f := fun i : Option I => inner ℝ b (x i))
      (Finset.mem_univ none)
    simpa only [x, Option.elim_none, inner_zero_right] using hh
  have hcb : c < ‖b‖ := by
    rw [Finset.sup'_lt_iff]
    intro i _
    cases i with
    | none => simpa only [x, Option.elim_none, inner_zero_right] using norm_pos_iff.mpr hb
    | some i => exact hult i
  let E := Metric.closedBall (0 : W) 1 ∩ {y : W | inner ℝ b y ≤ c}
  have hclosed : IsClosed {y : W | inner ℝ b y ≤ c} :=
    isClosed_le (continuous_const.inner continuous_id) continuous_const
  have hcompact : IsCompact E := (isCompact_closedBall (0 : W) 1).inter_right hclosed
  have hconvex : Convex ℝ E := (convex_closedBall (0 : W) 1).inter
    (convex_halfSpace_le (innerSL ℝ b).toLinearMap.isLinear c)
  refine ⟨E, hcompact, ⟨0, ?_⟩, hconvex, inter_subset_left, ?_, c, hcb, ?_⟩
  · exact ⟨by simp, by simpa using hc0⟩
  · intro i
    refine ⟨u i, ⟨?_, ?_⟩, huinner i⟩
    · simpa only [Metric.mem_closedBall, dist_zero_right] using hunorm i
    · exact Finset.le_sup' (f := fun j : Option I => inner ℝ b (x j))
        (Finset.mem_univ (some i))
  · exact fun _ hy => hy.2

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_TemplateSupportOrder
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finite_templateSymmetryGroup _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteRootOffsetConeIndex _root_.OAI.PolycyclicRecognition.instFiniteSubtypeLinearEquivRealIdMemSubgroupLinearSupportSymmetryGroup _root_.OAI.PolycyclicRecognition.instNonemptyRootOffsetConeIndex _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Monotonicity and strictness of the weighted template support -/

noncomputable section

namespace PolycyclicRecognition.SupportDatum

open Set
open scoped BigOperators

variable {W I B : Type} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [FiniteDimensional ℝ W] [Fintype I] [Fintype B] [Nonempty B]
  (D : PolycyclicRecognition.SupportDatum W I B)

omit [Nonempty B] in
theorem weightSupport_eq_of_bound_and_attained {E : Set W} (hc : IsCompact E)
    (i : I) (r : ℝ) (hbound : ∀ x ∈ E, D.weight i x ≤ r)
    (hattained : ∃ x ∈ E, D.weight i x = r) : D.weightSupport E i = r := by
  obtain ⟨x, hx, heq⟩ := hattained
  apply le_antisymm
  · obtain ⟨y, hy, hsup⟩ := D.exists_weightSupport_point hc ⟨x, hx⟩ i
    rw [hsup]
    exact hbound y hy
  · rw [← heq]
    exact D.weight_le_weightSupport hc hx i

omit [Nonempty B] in
theorem weightSupport_mono {E F : Set W} (hE : IsCompact E) (hn : E.Nonempty)
    (hF : IsCompact F) (hEF : E ⊆ F) (i : I) :
    D.weightSupport E i ≤ D.weightSupport F i := by
  obtain ⟨x, hx, heq⟩ := D.exists_weightSupport_point hE hn i
  rw [heq]
  exact D.weight_le_weightSupport hF (hEF hx) i

omit [FiniteDimensional ℝ W] in
/-- Every word basis contains every generator with positive multiplicity,
so decreasing one support strictly decreases the entire finite maximum. -/
theorem templateSupport_lt_of_weightSupport {E F : Set W}
    (hle : ∀ i, D.weightSupport E i ≤ D.weightSupport F i)
    (hlt : ∃ i, D.weightSupport E i < D.weightSupport F i) :
    D.templateSupport E < D.templateSupport F := by
  obtain ⟨b, _, hb⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty
    (D.basisTemplateSupport E)
  change Finset.univ.sup' _ _ < _
  rw [hb]
  apply lt_of_lt_of_le _ (D.basisTemplateSupport_le F b)
  unfold basisTemplateSupport
  apply Finset.sum_lt_sum
  · intro i _
    exact mul_le_mul_of_nonneg_left (hle i) (Nat.cast_nonneg _)
  · obtain ⟨i, hi⟩ := hlt
    exact ⟨i, Finset.mem_univ i,
      mul_lt_mul_of_pos_left hi (Nat.cast_pos.mpr (D.positive b i))⟩

end PolycyclicRecognition.SupportDatum

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_TemplateWeightRays
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteRootOffsetConeIndex _root_.OAI.PolycyclicRecognition.instNonemptyRootOffsetConeIndex _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.CartanWordModel.supportDatum_weight _root_.OAI.PolycyclicRecognition.SupportDatum.transport_weight_apply _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Template symmetries preserve the positive generator-weight rays -/

noncomputable section

namespace PolycyclicRecognition

open Set

variable {W I B : Type} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
  [FiniteDimensional ℝ W] [Fintype I] [Fintype B] [Nonempty B]

/-- The cap argument from the support-symmetries lemma: pullback of every
nonzero generator weight is a positive multiple of another generator weight.
It uses preservation of all compact convex templates, not only segments. -/
theorem templateSymmetry_weight_ray
    (D : SupportDatum W I B) (A : templateSymmetryGroup D)
    (j : I) (hj : D.weight j ≠ 0) :
    ∃ (i : I) (r : ℝ), 0 < r ∧ (D.weight j).comp A.val.toLinearMap = r • D.weight i := by
  classical
  let v : I → W := fun i => (InnerProductSpace.toDual ℝ W).symm
    (D.weight i).toContinuousLinearMap
  let β : W →ₗ[ℝ] ℝ := (D.weight j).comp A.val.toLinearMap
  let b : W := (InnerProductSpace.toDual ℝ W).symm β.toContinuousLinearMap
  have hv (i : I) (x : W) : inner ℝ (v i) x = D.weight i x :=
    InnerProductSpace.toDual_symm_apply
  have hbval (x : W) : inner ℝ b x = D.weight j (A.val x) :=
    InnerProductSpace.toDual_symm_apply
  have hb : b ≠ 0 := by
    intro hb
    apply hj
    ext x
    have hh := hbval (A.val.symm x)
    simpa only [hb, inner_zero_left, LinearEquiv.apply_symm_apply, LinearMap.zero_apply]
      using hh.symm
  by_contra hn
  have hnot : ∀ i (r : ℝ), 0 < r → b ≠ r • v i := by
    intro i r hr heq
    apply hn
    refine ⟨i, r, hr, ?_⟩
    ext x
    change D.weight j (A.val x) = r * D.weight i x
    rw [← hbval, heq, real_inner_smul_left, hv]
  obtain ⟨E, hE, hne, hconv, hEK, hreach, c, hcb, hcap⟩ :=
    exists_support_direction_cap v b hb hnot
  let K := Metric.closedBall (0 : W) 1
  have hK : IsCompact K := isCompact_closedBall 0 1
  have hKne : K.Nonempty := ⟨0, by simp [K]⟩
  have hbound (i : I) (x : W) (hx : x ∈ K) : D.weight i x ≤ ‖v i‖ := by
    have hx' : ‖x‖ ≤ 1 := by simpa only [K, Metric.mem_closedBall, dist_zero_right] using hx
    rw [← hv]
    exact (real_inner_le_norm _ _).trans (by nlinarith [norm_nonneg (v i)])
  have hsupp (i : I) : D.weightSupport E i = D.weightSupport K i := by
    obtain ⟨x, hx, heq⟩ := hreach i
    have heq' : D.weight i x = ‖v i‖ := by rwa [hv] at heq
    have hsE := D.weightSupport_eq_of_bound_and_attained hE i ‖v i‖
      (fun y hy => hbound i y (hEK hy)) ⟨x, hx, heq'⟩
    have hsK := D.weightSupport_eq_of_bound_and_attained hK i ‖v i‖
      (hbound i) ⟨x, hEK hx, heq'⟩
    exact hsE.trans hsK.symm
  have hPE : D.templateSupport E = D.templateSupport K := by
    unfold SupportDatum.templateSupport
    congr 1
    funext k
    simp only [SupportDatum.basisTemplateSupport, hsupp]
  have hAE : IsCompact (A.val '' E) := hE.image A.val.continuous_of_finiteDimensional
  have hAK : IsCompact (A.val '' K) := hK.image A.val.continuous_of_finiteDimensional
  have hAEne : (A.val '' E).Nonempty := hne.image A.val
  have hle (i : I) : D.weightSupport (A.val '' E) i ≤ D.weightSupport (A.val '' K) i :=
    D.weightSupport_mono hAE hAEne hAK (image_mono hEK) i
  have hjE : D.weightSupport (A.val '' E) j ≤ c := by
    obtain ⟨_, ⟨x, hx, rfl⟩, heq⟩ := D.exists_weightSupport_point hAE hAEne j
    rw [heq, ← hbval]
    exact hcap x hx
  let u : W := ‖b‖⁻¹ • b
  have hbn : ‖b‖ ≠ 0 := norm_ne_zero_iff.mpr hb
  have huK : u ∈ K := by
    simp [u, K, Metric.mem_closedBall, dist_zero_right, norm_smul, hbn]
  have hbu : inner ℝ b u = ‖b‖ := by
    simp only [u, real_inner_smul_right, real_inner_self_eq_norm_sq]
    field_simp
  have hjK : ‖b‖ ≤ D.weightSupport (A.val '' K) j := by
    have hh := D.weight_le_weightSupport hAK (mem_image_of_mem A.val huK) j
    rw [← hbval, hbu] at hh
    exact hh
  have hstrict := D.templateSupport_lt_of_weightSupport hle
    ⟨j, hjE.trans_lt (hcb.trans_le hjK)⟩
  rw [A.property E hE hne hconv,
    A.property K hK hKne (convex_closedBall (0 : W) 1), hPE] at hstrict
  exact lt_irrefl _ hstrict

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_TemplateConeTraces
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteRootOffsetConeIndex _root_.OAI.PolycyclicRecognition.instNonemptyRootOffsetConeIndex _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Positive trace tests after a template symmetry

The pure-word multiplicities on a transformed cone give a positive test
on each of its original extreme rays. The inverse template symmetry
supplies actual generator weights on those rays.
-/

noncomputable section
namespace PolycyclicRecognition

open Set
open scoped BigOperators

theorem positive_sum_on_weightCone_of_scaled_extremes
    {V I : Type} [AddCommGroup V] [Module ℝ V] [Fintype I]
    (α η : V) (hind : LinearIndependent ℝ ![α, η]) (β : I → V) (c : I → ℕ)
    (hout : ∀ i, β i ∉ positiveWeightCone α η → c i = 0)
    (i₀ i₁ : I) {s t : ℝ} (hs : 0 < s) (ht : 0 < t)
    (h₀ : β i₀ = s • α) (h₁ : β i₁ = t • η)
    (hc₀ : 0 < c i₀) (hc₁ : 0 < c i₁) :
    ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ ∑ i, (c i : ℝ) • β i = a • α + b • η := by
  classical
  have hd (i) : ∃ a b : ℝ, 0 ≤ a ∧ 0 ≤ b ∧
      (c i : ℝ) • β i = ((c i : ℝ) * a) • α + ((c i : ℝ) * b) • η ∧
      (β i ∈ positiveWeightCone α η → β i = a • α + b • η) := by
    by_cases hi : β i ∈ positiveWeightCone α η
    · obtain ⟨a, b, ha, hb, _, he⟩ := hi
      exact ⟨a, b, ha, hb, by rw [he, smul_add, smul_smul, smul_smul], fun _ => he⟩
    · exact ⟨0, 0, le_rfl, le_rfl, by simp [hout i hi], fun h => False.elim (hi h)⟩
  choose a b ha hb he hp using hd
  have hm₀ : β i₀ ∈ positiveWeightCone α η := by
    exact ⟨s, 0, hs.le, le_rfl, by simpa, by simpa using h₀⟩
  have hm₁ : β i₁ ∈ positiveWeightCone α η := by
    exact ⟨0, t, le_rfl, ht.le, by simpa, by simpa using h₁⟩
  have hA : a i₀ = s := (hind.eq_of_pair (s := a i₀) (t := b i₀) (s' := s) (t' := 0)
    (by simpa [h₀] using (hp i₀ hm₀).symm)).1
  have hB : b i₁ = t := (hind.eq_of_pair (s := a i₁) (t := b i₁) (s' := 0) (t' := t)
    (by simpa [h₁] using (hp i₁ hm₁).symm)).2
  refine ⟨∑ i, (c i : ℝ) * a i, ∑ i, (c i : ℝ) * b i, ?_, ?_, ?_⟩
  · have hpos : 0 < (c i₀ : ℝ) * a i₀ := by
      rw [hA]
      exact mul_pos (Nat.cast_pos.mpr hc₀) hs
    exact hpos.trans_le (Finset.single_le_sum
      (fun i _ => mul_nonneg (Nat.cast_nonneg _) (ha i)) (Finset.mem_univ i₀))
  · have hpos : 0 < (c i₁ : ℝ) * b i₁ := by
      rw [hB]
      exact mul_pos (Nat.cast_pos.mpr hc₁) ht
    exact hpos.trans_le (Finset.single_le_sum
      (fun i _ => mul_nonneg (Nat.cast_nonneg _) (hb i)) (Finset.mem_univ i₁))
  · simp_rw [he]
    rw [Finset.sum_add_distrib, Finset.sum_smul, Finset.sum_smul]

variable {W I B : Type} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
  [FiniteDimensional ℝ W] [Fintype I] [Fintype B] [Nonempty B]
  (D : SupportDatum W I B) (A : templateSymmetryGroup D)

/-- Every source generator ray is attained by a target generator after pullback. -/
theorem templateSymmetry_weight_ray_surjective
    (j : I) (hj : D.weight j ≠ 0) :
    ∃ (i : I) (s : ℝ), 0 < s ∧
      (D.weight i).comp A.val.toLinearMap = s • D.weight j := by
  obtain ⟨i, r, hr, he⟩ := templateSymmetry_weight_ray D A⁻¹ j hj
  change (D.weight j).comp A.val.symm.toLinearMap = r • D.weight i at he
  refine ⟨i, r⁻¹, inv_pos.mpr hr, ?_⟩
  ext w
  have hw := LinearMap.congr_fun he (A.val w)
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply,
    LinearMap.smul_apply, smul_eq_mul] at hw ⊢
  rw [hw, ← mul_assoc, inv_mul_cancel₀ hr.ne', one_mul]

private theorem pulled_weight_ne_zero (hne : ∀ i, D.weight i ≠ 0) (i : I) :
    ((D.weight i).toContinuousLinearMap.comp A.val.toLinearMap.toContinuousLinearMap) ≠ 0 := by
  intro he
  apply hne i
  ext w
  have hw := congrArg (fun f : W →L[ℝ] ℝ => f (A.val.symm w)) he
  simpa using hw

/-- The actual positive multiplicities of the transformed ray quotient
give a positive multiple of the source ray when pulled back. -/
theorem transformed_ray_trace_pos_multiple
    (hne : ∀ i, D.weight i ≠ 0) (j : I)
    (c : I → ℕ)
    (hout : ∀ i, (D.weight i).toContinuousLinearMap ∉
      transformedPolarCone (closedWeightRay (D.weight j).toContinuousLinearMap
        (by simpa using hne j)) A.val → c i = 0)
    (hin : ∀ i, (D.weight i).toContinuousLinearMap ∈
      transformedPolarCone (closedWeightRay (D.weight j).toContinuousLinearMap
        (by simpa using hne j)) A.val → 0 < c i) :
    ∃ r : ℝ, 0 < r ∧
      (∑ i, (c i : ℝ) • (D.weight i).toContinuousLinearMap).comp
        A.val.toLinearMap.toContinuousLinearMap = r • (D.weight j).toContinuousLinearMap := by
  let α := (D.weight j).toContinuousLinearMap
  let β := fun i => (D.weight i).toContinuousLinearMap.comp
    A.val.toLinearMap.toContinuousLinearMap
  have hα : α ≠ 0 := by simpa [α] using hne j
  obtain ⟨i, s, hs, hsi⟩ := templateSymmetry_weight_ray_surjective D A j (hne j)
  have hi : β i ∈ positiveWeightRay α := by
    refine ⟨s, hs, ?_⟩
    exact congrArg LinearMap.toContinuousLinearMap hsi
  have hc : 0 < c i := hin i (by
    change β i ∈ (closedWeightRay α hα : Set _)
    rw [closedWeightRay_eq_insert]
    exact mem_insert_of_mem _ hi)
  have hout' : ∀ i, β i ∉ positiveWeightRay α → c i = 0 := by
    intro i h
    apply hout i
    change β i ∉ (closedWeightRay α hα : Set _)
    rw [closedWeightRay_eq_insert]
    rintro (hz | hm)
    · exact pulled_weight_ne_zero D A hne i hz
    · exact h hm
  obtain ⟨r, hr, he⟩ := positive_sum_on_weightRay α β c hout' i hi hc
  refine ⟨r, hr, ?_⟩
  ext w
  simpa [β, α, sum_apply] using
    congrArg (fun f : W →L[ℝ] ℝ => f w) he

/-- For two independent source generators the transformed quotient trace
has a strictly positive coefficient on each source extreme ray. -/
theorem transformed_two_ray_trace_pos_coefficients
    (hne : ∀ i, D.weight i ≠ 0) (j k : I)
    (hind : LinearIndependent ℝ
      ![(D.weight j).toContinuousLinearMap, (D.weight k).toContinuousLinearMap])
    (c : I → ℕ)
    (hout : ∀ i, (D.weight i).toContinuousLinearMap ∉
      transformedPolarCone (closedTwoWeightCone (D.weight j).toContinuousLinearMap
        (D.weight k).toContinuousLinearMap hind) A.val → c i = 0)
    (hin : ∀ i, (D.weight i).toContinuousLinearMap ∈
      transformedPolarCone (closedTwoWeightCone (D.weight j).toContinuousLinearMap
        (D.weight k).toContinuousLinearMap hind) A.val → 0 < c i) :
    ∃ r s : ℝ, 0 < r ∧ 0 < s ∧
      (∑ i, (c i : ℝ) • (D.weight i).toContinuousLinearMap).comp
        A.val.toLinearMap.toContinuousLinearMap =
      r • (D.weight j).toContinuousLinearMap + s • (D.weight k).toContinuousLinearMap := by
  let α := (D.weight j).toContinuousLinearMap
  let η := (D.weight k).toContinuousLinearMap
  let β := fun i => (D.weight i).toContinuousLinearMap.comp
    A.val.toLinearMap.toContinuousLinearMap
  obtain ⟨i₀, r, hr, h₀⟩ := templateSymmetry_weight_ray_surjective D A j (hne j)
  obtain ⟨i₁, s, hs, h₁⟩ := templateSymmetry_weight_ray_surjective D A k (hne k)
  have hβ₀ : β i₀ = r • α := congrArg LinearMap.toContinuousLinearMap h₀
  have hβ₁ : β i₁ = s • η := congrArg LinearMap.toContinuousLinearMap h₁
  have hi₀ : β i₀ ∈ positiveWeightCone α η :=
    ⟨r, 0, hr.le, le_rfl, by simpa, by simpa using hβ₀⟩
  have hi₁ : β i₁ ∈ positiveWeightCone α η :=
    ⟨0, s, le_rfl, hs.le, by simpa, by simpa using hβ₁⟩
  have hc (i : I) (hi : β i ∈ positiveWeightCone α η) : 0 < c i := hin i (by
    change β i ∈ (closedTwoWeightCone α η hind : Set _)
    rw [closedTwoWeightCone_eq_insert]
    exact mem_insert_of_mem _ hi)
  have hout' : ∀ i, β i ∉ positiveWeightCone α η → c i = 0 := by
    intro i h
    apply hout i
    change β i ∉ (closedTwoWeightCone α η hind : Set _)
    rw [closedTwoWeightCone_eq_insert]
    rintro (hz | hm)
    · exact pulled_weight_ne_zero D A hne i hz
    · exact h hm
  obtain ⟨u, v, hu, hv, he⟩ := positive_sum_on_weightCone_of_scaled_extremes α η hind
    β c hout' i₀ i₁ hr hs hβ₀ hβ₁ (hc i₀ hi₀) (hc i₁ hi₁)
  refine ⟨u, v, hu, hv, ?_⟩
  ext w
  simpa [β, α, η, sum_apply] using
    congrArg (fun f : W →L[ℝ] ℝ => f w) he

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_TemplateConeTraceSeparation
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteRootOffsetConeIndex _root_.OAI.PolycyclicRecognition.instNonemptyRootOffsetConeIndex _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual transformed pure-word traces determine the offset -/

noncomputable section
namespace PolycyclicRecognition

open Set
open scoped BigOperators

variable {W I B : Type} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
  [FiniteDimensional ℝ W] [Fintype I] [Fintype B] [Nonempty B]

/-- Apply the forward and reversed volume tests to the same transformed
ray quotient and to each independent two-ray quotient. The positive
pure-word multiplicities then force equality of the original offsets. -/
theorem eq_of_transformed_pure_word_trace_inequalities
    (D : SupportDatum W I B) (A : templateSymmetryGroup D)
    (hne : ∀ i, D.weight i ≠ 0) (j : I)
    (cRay : I → ℕ) (cTwo : I → I → ℕ)
    (houtRay : ∀ i, (D.weight i).toContinuousLinearMap ∉
      transformedPolarCone (closedWeightRay (D.weight j).toContinuousLinearMap
        (by simpa using hne j)) A.val → cRay i = 0)
    (hinRay : ∀ i, (D.weight i).toContinuousLinearMap ∈
      transformedPolarCone (closedWeightRay (D.weight j).toContinuousLinearMap
        (by simpa using hne j)) A.val → 0 < cRay i)
    (houtTwo : ∀ k (h : LinearIndependent ℝ
        ![(D.weight j).toContinuousLinearMap, (D.weight k).toContinuousLinearMap]),
      ∀ i, (D.weight i).toContinuousLinearMap ∉
        transformedPolarCone (closedTwoWeightCone (D.weight j).toContinuousLinearMap
          (D.weight k).toContinuousLinearMap h) A.val → cTwo k i = 0)
    (hinTwo : ∀ k (h : LinearIndependent ℝ
        ![(D.weight j).toContinuousLinearMap, (D.weight k).toContinuousLinearMap]),
      ∀ i, (D.weight i).toContinuousLinearMap ∈
        transformedPolarCone (closedTwoWeightCone (D.weight j).toContinuousLinearMap
          (D.weight k).toContinuousLinearMap h) A.val → 0 < cTwo k i)
    (x y : W)
    (hray : (∑ i, (cRay i : ℝ) • (D.weight i).toContinuousLinearMap) (y - x) ≤ 0)
    (hray' : (∑ i, (cRay i : ℝ) • (D.weight i).toContinuousLinearMap) (x - y) ≤ 0)
    (htwo : ∀ k, LinearIndependent ℝ
        ![(D.weight j).toContinuousLinearMap, (D.weight k).toContinuousLinearMap] →
      (∑ i, (cTwo k i : ℝ) • (D.weight i).toContinuousLinearMap) (y - x) ≤ 0)
    (htwo' : ∀ k, LinearIndependent ℝ
        ![(D.weight j).toContinuousLinearMap, (D.weight k).toContinuousLinearMap] →
      (∑ i, (cTwo k i : ℝ) • (D.weight i).toContinuousLinearMap) (x - y) ≤ 0) :
    x = y := by
  classical
  let w := A.val.symm (y - x)
  have hzero (ell : W →L[ℝ] ℝ) (hp : ell (y - x) ≤ 0) (hn : ell (x - y) ≤ 0) :
      ell (y - x) = 0 := by
    rw [map_sub] at hp hn ⊢
    linarith
  obtain ⟨r, hr, he⟩ := transformed_ray_trace_pos_multiple D A hne j cRay houtRay hinRay
  have hα : (D.weight j) w = 0 := by
    have hv := congrArg (fun f : W →L[ℝ] ℝ => f w) he
    have hz := hzero _ hray hray'
    simp only [ContinuousLinearMap.comp_apply, smul_apply,
      smul_eq_mul] at hv
    change (∑ i, (cRay i : ℝ) • (D.weight i).toContinuousLinearMap) (A.val w) =
      r * (D.weight j) w at hv
    have hw : A.val w = y - x := A.val.apply_symm_apply _
    rw [hw, hz] at hv
    exact (mul_eq_zero.mp hv.symm).resolve_left hr.ne'
  have hw : w = 0 := D.separates w (by
    intro k
    by_cases hind : LinearIndependent ℝ
        ![(D.weight j).toContinuousLinearMap, (D.weight k).toContinuousLinearMap]
    · obtain ⟨u, v, _, hvpos, he⟩ := transformed_two_ray_trace_pos_coefficients D A
        hne j k hind (cTwo k) (houtTwo k hind) (hinTwo k hind)
      have hv := congrArg (fun f : W →L[ℝ] ℝ => f w) he
      have hz := hzero _ (htwo k hind) (htwo' k hind)
      simp only [ContinuousLinearMap.comp_apply, add_apply,
        smul_apply, smul_eq_mul] at hv
      change (∑ i, (cTwo k i : ℝ) • (D.weight i).toContinuousLinearMap) (A.val w) =
        u * (D.weight j) w + v * (D.weight k) w at hv
      have hw : A.val w = y - x := A.val.apply_symm_apply _
      rw [hw, hz] at hv
      change 0 = u * (D.weight j) w + v * (D.weight k) w at hv
      rw [hα, mul_zero, zero_add] at hv
      exact (mul_eq_zero.mp hv.symm).resolve_left hvpos.ne'
    · have hαne : (D.weight j).toContinuousLinearMap ≠ 0 := by simpa using hne j
      obtain ⟨c, hc⟩ : ∃ c : ℝ,
          c • (D.weight j).toContinuousLinearMap = (D.weight k).toContinuousLinearMap := by
        simpa only [LinearIndependent.pair_iff' hαne, not_forall, not_not] using hind
      have hh := congrArg (fun f : W →L[ℝ] ℝ => f w) hc
      change c * (D.weight j) w = (D.weight k) w at hh
      rw [hα, mul_zero] at hh
      exact hh.symm)
  have he := congrArg A.val hw
  have hz : y - x = 0 := by simpa [w] using he
  exact (sub_eq_zero.mp hz).symm

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
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_WeightSamplingPolytope
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finite_templateSymmetryGroup _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteRootOffsetConeIndex _root_.OAI.PolycyclicRecognition.instFiniteSubtypeLinearEquivRealIdMemSubgroupLinearSupportSymmetryGroup _root_.OAI.PolycyclicRecognition.instNonemptyRootOffsetConeIndex _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
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
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanPolarConeKernel
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Removing the polar cone vertex without changing the mixed ideal

The polar template uses a closed cone containing zero. The cone quotient
must kill the zero generalized weight space to descend the overlapping
Cartan factors. Salience and the nonzero generator weights supply this
bridge for the same mixed ideal.
-/

noncomputable section
namespace PolycyclicRecognition

open Module LieAlgebra LieModule Set

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]

set_option maxHeartbeats 1000000 in
theorem closedWeightRay_salient {α : V} (hα : α ≠ 0) :
    (closedWeightRay α hα : ConvexCone ℝ V).Salient := by
  intro x hx hx0 hneg
  have hp : x ∈ positiveWeightRay α := by
    have hh : x ∈ (closedWeightRay α hα : Set V) := hx
    rw [closedWeightRay_eq_insert] at hh
    exact hh.resolve_left hx0
  have hn : -x ∈ positiveWeightRay α := by
    have hh : -x ∈ (closedWeightRay α hα : Set V) := hneg
    rw [closedWeightRay_eq_insert] at hh
    exact hh.resolve_left (neg_ne_zero.mpr hx0)
  exact zero_not_mem_positiveWeightRay hα (by
    simpa using positiveWeightRay_add α x hp (-x) hn)

set_option maxHeartbeats 1000000 in
theorem closedTwoWeightCone_salient (α η : V) (h : LinearIndependent ℝ ![α, η]) :
    (closedTwoWeightCone α η h : ConvexCone ℝ V).Salient := by
  intro x hx hx0 hneg
  have hp : x ∈ positiveWeightCone α η := by
    have hh : x ∈ (closedTwoWeightCone α η h : Set V) := hx
    rw [closedTwoWeightCone_eq_insert] at hh
    exact hh.resolve_left hx0
  have hn : -x ∈ positiveWeightCone α η := by
    have hh : -x ∈ (closedTwoWeightCone α η h : Set V) := hneg
    rw [closedTwoWeightCone_eq_insert] at hh
    exact hh.resolve_left (neg_ne_zero.mpr hx0)
  exact zero_not_mem_positiveWeightCone h (by
    simpa using positiveWeightCone_add α η x hp (-x) hn)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_TemplateOffsetCones
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The finite family of polar quotients that detects one root offset -/

noncomputable section
namespace PolycyclicRecognition

open Set
open scoped BigOperators

variable {W I B : Type} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
  [FiniteDimensional ℝ W] [Fintype I] [Fintype B]

theorem rootOffsetCone_salient (D : SupportDatum W I B) (hne : ∀ i, D.weight i ≠ 0)
    (j : I) (s : rootOffsetConeIndex D j) :
    (rootOffsetCone D hne j s : ConvexCone ℝ (StrongDual ℝ W)).Salient := by
  cases s with
  | none => exact closedWeightRay_salient (by simpa using hne j)
  | some k => exact closedTwoWeightCone_salient _ _ k.property

theorem weight_mem_rootOffsetCone (D : SupportDatum W I B) (hne : ∀ i, D.weight i ≠ 0)
    (j : I) (s : rootOffsetConeIndex D j) :
    (D.weight j).toContinuousLinearMap ∈ rootOffsetCone D hne j s := by
  cases s with
  | none =>
      exact (mem_closedWeightRay (by simpa using hne j) _).mpr
        ⟨1, zero_le_one, by simp⟩
  | some k =>
      exact (mem_closedTwoWeightCone _ _ k.property _).mpr
        ⟨1, 0, zero_le_one, le_rfl, by simp⟩

variable [Nonempty B]

/-- Forward and reverse volume inequalities for this finite family force
the two offsets to coincide. Each inequality uses its own actual quotient
trace, with positive multiplicity exactly on the transformed cone. -/
theorem eq_of_rootOffsetCone_trace_inequalities
    (D : SupportDatum W I B) (A : templateSymmetryGroup D)
    (hne : ∀ i, D.weight i ≠ 0) (j : I)
    (c : rootOffsetConeIndex D j → I → ℕ)
    (hout : ∀ s i, (D.weight i).toContinuousLinearMap ∉
      transformedPolarCone (rootOffsetCone D hne j s) A.val → c s i = 0)
    (hin : ∀ s i, (D.weight i).toContinuousLinearMap ∈
      transformedPolarCone (rootOffsetCone D hne j s) A.val → 0 < c s i)
    (x y : W)
    (hf : ∀ s, (∑ i, (c s i : ℝ) • (D.weight i).toContinuousLinearMap) (y - x) ≤ 0)
    (hr : ∀ s, (∑ i, (c s i : ℝ) • (D.weight i).toContinuousLinearMap) (x - y) ≤ 0) :
    x = y := by
  classical
  let cTwo : I → I → ℕ := fun k =>
    if h : LinearIndependent ℝ
        ![(D.weight j).toContinuousLinearMap, (D.weight k).toContinuousLinearMap]
    then c (some ⟨k, h⟩) else 0
  apply eq_of_transformed_pure_word_trace_inequalities D A hne j (c none) cTwo
    (hout none) (hin none) ?_ ?_ x y (hf none) (hr none) ?_ ?_
  · intro k hk i hi
    simpa only [cTwo, dite_eq_left hk] using hout (some ⟨k, hk⟩) i hi
  · intro k hk i hi
    simpa only [cTwo, dite_eq_left hk] using hin (some ⟨k, hk⟩) i hi
  · intro k hk
    simpa only [cTwo, dite_eq_left hk] using hf (some ⟨k, hk⟩)
  · intro k hk
    simpa only [cTwo, dite_eq_left hk] using hr (some ⟨k, hk⟩)

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
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanReverseNeighborLaw
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instDecidableEqConeMixedWords _root_.OAI.PolycyclicRecognition.CartanWordModel.instFintypeConeMixedWords _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.CartanFactorModel.heightRay_zero _root_.OAI.PolycyclicRecognition.CartanFactorModel.realScaleProfile_apply _root_.OAI.PolycyclicRecognition.CartanFactorModel.sampledProbeProfile_apply _root_.OAI.PolycyclicRecognition.bracketWordDifferential_mul _root_.OAI.PolycyclicRecognition.cartanWeightDerivation_apply_root _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.modelNilradicalLinearAction_apply _root_.OAI.PolycyclicRecognition.modelNilradicalRotation_apply _root_.OAI.PolycyclicRecognition.modelNilradicalRotation_mul _root_.OAI.PolycyclicRecognition.modelNilradicalRotation_one _root_.OAI.PolycyclicRecognition.nilshadowWeightDerivation_symm _root_.OAI.PolycyclicRecognition.nilshadowWeightOperator_symm _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Reversing the actual neighboring pair for the opposite offset inequality -/

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
  {Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H Exp)
  (hunimod : ∀ x : GroupLieAlgebra (𝓘(ℝ, EG)) G, LinearMap.trace ℝ _ (ad ℝ _ x) = 0)
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)

set_option maxHeartbeats 1000000 in
/-- Reversing the deterministic root step replaces the joint law by its
coordinate swap, using exactly the Haar cell based at `base * step`. -/
theorem reversed_neighbor_cell_limit
    [IsTopologicalGroup F.N.carrier]
    (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
    (chartN : GroupLieAlgebra (𝓘(ℝ, F.N.modelSpace)) F.N.carrier ≃ₜ F.N.carrier)
    (hchartN : ∀ x, chartN x = F.ExpN x)
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (E : Set W) (β : M.Bases) (scale : ℕ → ℝ) (base step : ℕ → F.N.carrier)
    {S : Type} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S] [BorelSpace (S × S)]
    (profile : ℕ → F.N.carrier → S) (hp : ∀ n, Measurable (profile n))
    (ν : ProbabilityMeasure (S × S))
    (hν : Tendsto (fun n => ProbabilityMeasure.map
      (M.translatedGroupBoxProbability T F hunimod eW haarN chartN hchartN b₀ E β (scale n) (base n))
      (f := (fun q => (profile n q, profile n (q * step n)))) (((hp n).prodMk ((hp n).comp (continuous_id.mul continuous_const).measurable)).aemeasurable)) atTop (𝓝 ν)) :
    Tendsto (fun n => ProbabilityMeasure.map
      (M.translatedGroupBoxProbability T F hunimod eW haarN chartN hchartN b₀ E β
        (scale n) (base n * step n))
      (f := (fun q => (profile n q, profile n (q * (step n)⁻¹)))) (((hp n).prodMk ((hp n).comp (continuous_id.mul continuous_const).measurable)).aemeasurable)) atTop
      (𝓝 (ProbabilityMeasure.map ν (f := Prod.swap) (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability))) := by
  let μ := fun n => M.translatedGroupBoxProbability T F hunimod eW haarN chartN hchartN b₀
    E β (scale n) (base n)
  let pair := fun n q => (profile n q, profile n (q * step n))
  have hp' n : Measurable (pair n) :=
    (hp n).prodMk ((hp n).comp (continuous_id.mul continuous_const).measurable)
  have he := sampled_projection_tendsto μ pair hp' ν hν Prod.swap continuous_swap
  convert he using 1
  all_goals try with_reducible_and_instances rfl
  funext n
  have hr := M.translated_groupBox_profile_law_mul_right T F hunimod eW
    haarN chartN hchartN b₀ E β (scale n) (base n) (step n)
    (fun q => (profile n q, profile n (q * (step n)⁻¹)))
    ((hp n).prodMk ((hp n).comp (continuous_id.mul continuous_const).measurable))
  simpa only [μ, pair, Function.comp_def, Prod.swap_prod_mk, mul_inv_cancel_right] using hr.symm

set_option maxHeartbeats 1000000 in
/-- Swapped supported profiles remain supported in the reversed law. -/
theorem swapped_pair_mem_support
    {S : Type} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S] [BorelSpace (S × S)]
    (ν : ProbabilityMeasure (S × S)) {f : S × S} (hf : f ∈ (ν : Measure (S × S)).support) :
    f.swap ∈ (ProbabilityMeasure.map ν (f := Prod.swap) (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability) : Measure (S × S)).support :=
  mem_support_map_of_continuous ν Prod.swap continuous_swap hf

set_option maxHeartbeats 1000000 in
/-- The inverse of an actual root step has the same generator and negated
parameter; the allowed amplitude is unchanged. -/
theorem inverse_root_step (hExp : IsGroupExponential Exp)
    (i : Fin M.letterCount) (step : F.N.carrier) (time : ℝ)
    (hstep : F.inclusionN step = Exp (time • (M.letter i : GroupLieAlgebra (𝓘(ℝ, EG)) G))) :
    F.inclusionN step⁻¹ = Exp ((-time) • (M.letter i : GroupLieAlgebra (𝓘(ℝ, EG)) G)) := by
  rw [map_inv, hstep, neg_smul, hExp.map_neg]

set_option maxHeartbeats 1000000 in
/-- The new base and the inverse step lie in the same enlarged box with
one common subexponential radius. This supplies the original box hypotheses
when the offset volume comparison is applied in reverse. -/
theorem exists_reverse_neighbor_radius
    (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (E : Set W) (β : M.Bases)
    (hβ : IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
      (M.boxCost T hunimod eW E) β.val)
    (scale R : ℕ → ℝ) (hs : Tendsto scale atTop atTop) (hs0 : ∀ n, 0 ≤ scale n)
    (hR0 : ∀ n, 0 ≤ R n) (hR : HasSubexponentialUpperBoundSeq scale R)
    (base step : ℕ → F.N.carrier)
    (hbase : ∀ n, base n ∈ M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) E β (scale n) (R n))
    (hstep : ∀ n, step n ∈ M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) E β (scale n) (R n)) :
    ∃ R' : ℕ → ℝ, (∀ n, R n ≤ R' n) ∧ (∀ n, 0 ≤ R' n) ∧
      HasSubexponentialUpperBoundSeq scale R' ∧ ∀ n,
      base n * step n ∈ M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) E β (scale n) (R' n) ∧
      (step n)⁻¹ ∈ M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) E β (scale n) (R' n) := by
  obtain ⟨C, hC, hprod⟩ := M.exists_groupBox_product_bound T hunimod eW
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
  refine ⟨fun n => R n + P n, fun n => le_add_of_nonneg_right (hP0 n),
    fun n => add_nonneg (hR0 n) (hP0 n), hR.add hP hs, ?_⟩
  intro n
  have hpair : ∀ i : Fin 2, ![base n, step n] i ∈
      M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) E β (scale n) (R n) := by
    intro i
    fin_cases i
    · exact hbase n
    · exact hstep n
  have hm : base n * step n ∈ M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv)
      E β (scale n) (P n) := by
    simpa [P, List.ofFn_succ] using hprod E β hβ (scale n) (hs0 n) 2 (R n) (hR0 n) _ hpair
  constructor
  · obtain ⟨v, hv, hb⟩ := hm
    exact ⟨v, hv, hb.trans (le_add_of_nonneg_left (hR0 n))⟩
  · obtain ⟨v, hv, hb⟩ := M.groupBox_inv_mem T hunimod eW F.N.equiv F.ExpN
      F.isExpN E β (scale n) (R n) (hstep n)
    exact ⟨v, hv, hb.trans (le_add_of_nonneg_right (hP0 n))⟩

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanNeighborRowReverse
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_nonempty _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.inversePairCoupling_finiteOnCompacts _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.CartanFactorModel.heightRay_zero _root_.OAI.PolycyclicRecognition.CartanFactorModel.realScaleProfile_apply _root_.OAI.PolycyclicRecognition.CartanFactorModel.sampledProbeProfile_apply _root_.OAI.PolycyclicRecognition.bracketWordDifferential_mul _root_.OAI.PolycyclicRecognition.cartanWeightDerivation_apply_root _root_.OAI.PolycyclicRecognition.chartExponentialFlow_zero _root_.OAI.PolycyclicRecognition.derivationSemidirectHom_apply _root_.OAI.PolycyclicRecognition.exponentialHomOfDynkin_apply_exp _root_.OAI.PolycyclicRecognition.exponentialRescaleBasis_zero _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.modelNilradicalLinearAction_apply _root_.OAI.PolycyclicRecognition.modelNilradicalRotation_apply _root_.OAI.PolycyclicRecognition.modelNilradicalRotation_mul _root_.OAI.PolycyclicRecognition.modelNilradicalRotation_one _root_.OAI.PolycyclicRecognition.nilshadowWeightDerivation_symm _root_.OAI.PolycyclicRecognition.nilshadowWeightOperator_symm _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Reversing the original affinity row -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule MeasureTheory Filter Set
open scoped Manifold Topology ENNReal NNReal

variable {EG G W I : Type} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {ExpG : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H ExpG)
  (hunimod : ∀ x : GroupLieAlgebra (𝓘(ℝ, EG)) G, LinearMap.trace ℝ _ (ad ℝ _ x) = 0)
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)
  [IsTopologicalGroup F.N.carrier]
  [SecondCountableTopology F.N.carrier]


variable [Fintype I] [DecidableEq I]


variable (π : G →* Multiplicative W)
  (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
  (cell : Set W) (βcell : M.Bases)
  (X : I → H) {d : ℕ} (βD : WordBasisSelections X (boundedBracketWords d))
  (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
  (chartN : GroupLieAlgebra (𝓘(ℝ, F.N.modelSpace)) F.N.carrier ≃ₜ F.N.carrier)
  (hchartN : ∀ x, chartN x = F.ExpN x)
  (pivot : Fin M.letterCount → H) (shrink B δ : ℝ)
  (S : Set C((Fin (finrank ℝ H) → ℝ), W))
  [MeasurableSpace S] [BorelSpace S] [BorelSpace (S × S)]
  {Λ : ℝ≥0}
  (D : AffineNeighborRow T M F hunimod eW π b₀ cell βcell X βD
    haarN chartN hchartN pivot shrink B δ S (Λ := Λ))

set_option maxHeartbeats 1000000 in
/-- The opposite trace inequality uses an actual row with the same root
and the two labels and offsets swapped. Only its subexponential radius changes. -/
theorem AffineNeighborRow.exists_reverse
    (hExp : IsGroupExponential ExpG)
    (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
    (hcell : IsCompact cell) (hne : cell.Nonempty)
    (hβ : IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
      (M.boxCost T hunimod eW cell) βcell.val)
    (hδ : 0 ≤ δ) (hs : ∀ n, 0 ≤ D.scale n) :
    ∃ R : AffineNeighborRow T M F hunimod eW π b₀ cell βcell X βD
      haarN chartN hchartN pivot shrink B δ S (Λ := Λ),
      R.scale = D.scale ∧ R.mode = D.mode ∧
      R.label₁ = D.label₂ ∧ R.label₂ = D.label₁ ∧
      R.offset₁ = D.offset₂ ∧ R.offset₂ = D.offset₁ := by
  let D' := D.fixedBasis T M F hunimod eW π b₀ cell βcell X βD
    haarN chartN hchartN pivot shrink B δ S hcell hne hβ hδ hs
  have hβ' := M.maximizing_box_basis_smul T hunimod eW b₀ hcell hne
    (show 0 ≤ 1 + δ by linarith) βcell hβ
  obtain ⟨R, hRR, hR0, hR, hbounds⟩ := M.exists_reverse_neighbor_radius T F hunimod eW
    dynkinN b₀ ((fun w => (1 + δ) • w) '' cell) βcell hβ' D'.scale D'.radius
    D'.grows hs D'.radius_nonneg D'.radius_subexponential D'.base D'.step
    D'.base_mem D'.step_mem
  let g := D'.gluedProfile T M F hunimod eW π b₀ cell βcell X βD
    haarN chartN hchartN pivot shrink B δ S
  obtain ⟨hg, hactual, hlaw⟩ := D'.gluedProfile_properties T M F hunimod eW π b₀
    cell βcell X βD haarN chartN hchartN pivot shrink B δ S
  have hreverse := M.reversed_neighbor_cell_limit T F hunimod eW haarN chartN hchartN
    b₀ cell βcell D'.scale D'.base D'.step g hg D'.law hlaw
  refine ⟨{
    scale := D'.scale
    grows := D'.grows
    pair := D'.pair
    center := D'.center
    radius := R
    radius_nonneg := hR0
    radius_subexponential := hR
    base := fun n => D'.base n * D'.step n
    step := fun n => (D'.step n)⁻¹
    basis := fun _ => βcell
    base_mem := fun n => (hbounds n).1
    step_mem := fun n => (hbounds n).2
    mode := D'.mode
    time := fun n => -D'.time n
    time_bound := ?_
    root_step := fun n => M.inverse_root_step F hExp D'.mode (D'.step n)
      (D'.time n) (D'.root_step n)
    profile := fun n q => (g n q, g n (q * (D'.step n)⁻¹))
    measurable_profile := fun n => (hg n).prodMk ((hg n).comp
      (continuous_id.mul continuous_const).measurable)
    actual := ?_
    law := ProbabilityMeasure.map D'.law (f := Prod.swap) (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
    converges := hreverse
    point := D'.point.swap
    supported := swapped_pair_mem_support D'.law D'.supported
    label₁ := D'.label₂
    label₂ := D'.label₁
    offset₁ := D'.offset₂
    offset₂ := D'.offset₁
    affine₁ := D'.affine₂
    affine₂ := D'.affine₁ }, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · intro n
    rw [abs_neg]
    exact (D'.time_bound n).trans
      (mul_le_mul_of_nonneg_right (hRR n) (Real.exp_pos _).le)
  · intro n q hq z
    obtain ⟨v, hv, rfl⟩ := hq
    constructor
    · apply hactual n _ (Or.inr ⟨v * D'.base n, ⟨v, hv, rfl⟩, mul_assoc _ _ _⟩) z
    · apply hactual n _ (Or.inl ?_) z
      refine ⟨v, hv, ?_⟩
      simp [mul_assoc]

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanNeighborRowOffsetsEqual
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_nonempty _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The finite polar tests determine both affine offsets -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule MeasureTheory Filter Set
open scoped Manifold Topology ENNReal NNReal BigOperators

variable {EG G W I : Type} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {ExpG : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H ExpG)
  (hunimod : ∀ x : GroupLieAlgebra (𝓘(ℝ, EG)) G, LinearMap.trace ℝ _ (ad ℝ _ x) = 0)
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)
  [IsTopologicalGroup F.N.carrier]
  [SecondCountableTopology F.N.carrier]


variable [Fintype I] [DecidableEq I]


variable (π : G →* Multiplicative W)
  (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
  (cell : Set W) (βcell : M.Bases)
  (X : I → H) {d : ℕ} (βD : WordBasisSelections X (boundedBracketWords d))
  (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
  (chartN : GroupLieAlgebra (𝓘(ℝ, F.N.modelSpace)) F.N.carrier ≃ₜ F.N.carrier)
  (hchartN : ∀ x, chartN x = F.ExpN x)
  (pivot : Fin M.letterCount → H) (shrink B δ : ℝ)
  (S : Set C((Fin (finrank ℝ H) → ℝ), W))
  [MeasurableSpace S] [BorelSpace S] [BorelSpace (S × S)]
  {Λ : ℝ≥0}
  (D : AffineNeighborRow T M F hunimod eW π b₀ cell βcell X βD
    haarN chartN hchartN pivot shrink B δ S (Λ := Λ))

set_option maxHeartbeats 1000000 in
/-- Apply each fixed quotient trace to the original row and to its actual
reversal. The ray and two-ray tests then force the offsets to agree. -/
theorem AffineNeighborRow.offsets_eq_of_cone_bounds
    (hExp : IsGroupExponential ExpG)
    (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
    (hcell : IsCompact cell) (hne : cell.Nonempty)
    (hβ : IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
      (M.boxCost T hunimod eW cell) βcell.val)
    (hδ : 0 ≤ δ) (hs : ∀ n, 0 ≤ D.scale n)
    (hlabels : D.label₂ = D.label₁)
    (hnz : ∀ i, (M.supportIn T hunimod eW).weight i ≠ 0)
    (coeff : rootOffsetConeIndex (M.supportIn T hunimod eW) D.mode →
      Fin M.letterCount → ℕ)
    (hout : ∀ s j, ((M.supportIn T hunimod eW).weight j).toContinuousLinearMap ∉
      transformedPolarCone (rootOffsetCone (M.supportIn T hunimod eW) hnz D.mode s)
        D.label₁.val → coeff s j = 0)
    (hin : ∀ s j, ((M.supportIn T hunimod eW).weight j).toContinuousLinearMap ∈
      transformedPolarCone (rootOffsetCone (M.supportIn T hunimod eW) hnz D.mode s)
        D.label₁.val → 0 < coeff s j)
    (hbound : ∀ s,
      ∀ R : AffineNeighborRow T M F hunimod eW π b₀ cell βcell X βD
        haarN chartN hchartN pivot shrink B δ S (Λ := Λ),
      R.mode = D.mode → R.label₁ = D.label₁ → R.label₂ = D.label₁ →
        (∑ j, (coeff s j : ℝ) • ((M.supportIn T hunimod eW).weight j).toContinuousLinearMap)
          (R.offset₂ - R.offset₁) ≤ 0) :
    D.offset₁ = D.offset₂ := by
  obtain ⟨R, _, hmode, hlabel₁, hlabel₂, hoffset₁, hoffset₂⟩ :=
    D.exists_reverse T M F hunimod eW π b₀ cell βcell X βD
      haarN chartN hchartN pivot shrink B δ S hExp dynkinN hcell hne hβ hδ hs
  apply eq_of_rootOffsetCone_trace_inequalities (M.supportIn T hunimod eW)
    D.label₁ hnz D.mode coeff hout hin D.offset₁ D.offset₂
  · intro s
    exact hbound s D rfl rfl hlabels
  · intro s
    simpa only [hoffset₁, hoffset₂] using
      hbound s R hmode (hlabel₁.trans hlabels) hlabel₂

set_option maxHeartbeats 1000000 in
/-- Finitely many cone and label thresholds give a single positive
threshold for all original neighboring rows. Cofinal restriction supplies
positive scales before reversal. -/
theorem exists_uniform_neighbor_offset_threshold
    [Nonempty (Fin M.letterCount)]
    (hExp : IsGroupExponential ExpG)
    (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
    (hcell : IsCompact cell) (hne : cell.Nonempty)
    (hβ : IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
      (M.boxCost T hunimod eW cell) βcell.val)
    (hnz : ∀ i, (M.supportIn T hunimod eW).weight i ≠ 0)
    (hcone : ∀ (i : Fin M.letterCount)
      (A : templateSymmetryGroup (M.supportIn T hunimod eW))
      (s : rootOffsetConeIndex (M.supportIn T hunimod eW) i),
      ∃ coeff : Fin M.letterCount → ℕ,
        (∀ j, ((M.supportIn T hunimod eW).weight j).toContinuousLinearMap ∉
          transformedPolarCone (rootOffsetCone (M.supportIn T hunimod eW) hnz i s) A.val →
            coeff j = 0) ∧
        (∀ j, ((M.supportIn T hunimod eW).weight j).toContinuousLinearMap ∈
          transformedPolarCone (rootOffsetCone (M.supportIn T hunimod eW) hnz i s) A.val →
            0 < coeff j) ∧
        ∃ ε : ℝ, 0 < ε ∧ ∀ ζ : ℝ, 0 < ζ → ζ ≤ ε →
          ∀ R : AffineNeighborRow T M F hunimod eW π b₀ cell βcell X βD
            haarN chartN hchartN pivot shrink B ζ S (Λ := Λ),
          R.mode = i → R.label₁ = A → R.label₂ = A →
            (∑ j, (coeff j : ℝ) • ((M.supportIn T hunimod eW).weight j).toContinuousLinearMap)
              (R.offset₂ - R.offset₁) ≤ 0) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ ζ : ℝ, 0 < ζ → ζ ≤ ε →
      ∀ R : AffineNeighborRow T M F hunimod eW π b₀ cell βcell X βD
        haarN chartN hchartN pivot shrink B ζ S (Λ := Λ),
      R.label₂ = R.label₁ → R.offset₁ = R.offset₂ := by
  classical
  choose coeff hout hin ε hε hbound using hcone
  let J := Σ i : Fin M.letterCount,
    (templateSymmetryGroup (M.supportIn T hunimod eW) ×
      rootOffsetConeIndex (M.supportIn T hunimod eW) i)
  let : Fintype J := Fintype.ofFinite J
  let : Nonempty J := ⟨⟨Classical.arbitrary _, 1, none⟩⟩
  let threshold : J → ℝ := fun j => ε j.1 j.2.1 j.2.2
  obtain ⟨j₀, _, hmin⟩ := Finset.exists_min_image Finset.univ threshold Finset.univ_nonempty
  refine ⟨threshold j₀, hε _ _ _, ?_⟩
  intro ζ hζ hζε R hlabels
  obtain ⟨u, hu, _, hs⟩ := exists_strictMono_scale_subsequence R.scale R.grows
  let R' := R.reindex T M F hunimod eW π b₀ cell βcell X βD
    haarN chartN hchartN pivot shrink B ζ S u hu
  apply R'.offsets_eq_of_cone_bounds T M F hunimod eW π b₀ cell βcell X βD
    haarN chartN hchartN pivot shrink B ζ S hExp dynkinN hcell hne hβ hζ.le
    (fun n => zero_le_one.trans (hs n)) hlabels hnz (coeff R'.mode R'.label₁)
    (hout R'.mode R'.label₁) (hin R'.mode R'.label₁)
  intro s Q hmode hlabel₁ hlabel₂
  exact hbound R'.mode R'.label₁ s ζ hζ
    (hζε.trans (hmin ⟨R'.mode, R'.label₁, s⟩ (Finset.mem_univ _))) Q hmode hlabel₁ hlabel₂

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanUniformOffsetThreshold
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_nonempty _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.unitaryCentralFixed_complete _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # One offset threshold for every original root neighbor -/

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
/-- The source and target cone models are fixed on a finite family. The
published estimates then give one threshold for all scales, maps and
supported neighboring profiles with a common affine label. -/
theorem exists_uniform_polar_offset_threshold_oai
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
    (Ds : ∀ (i : Fin M.letterCount) (s : rootOffsetConeIndex (M.supportIn T hunimod eW) i),
      M.MeasuredCone F (heightConePreimage T eW
        (rootOffsetCone (M.supportIn T hunimod eW) hnz i s)))
    (dynkinI : ∀ i s, NilpotentDynkinExpansionInput (Ds i s).I.modelSpace (Ds i s).I.carrier)
    (haarI : ∀ i s, NilpotentExponentialHaarInput (Ds i s).I.modelSpace (Ds i s).I.carrier)
    (Dt : ∀ (i : Fin M.letterCount) (A : templateSymmetryGroup (M.supportIn T hunimod eW))
      (s : rootOffsetConeIndex (M.supportIn T hunimod eW) i),
      M.MeasuredCone F (heightConePreimage T eW
        (transformedPolarCone (rootOffsetCone (M.supportIn T hunimod eW) hnz i s) A.val)))
    (haarQt : ∀ i A s, NilpotentExponentialHaarInput (Dt i A s).Q.modelSpace (Dt i A s).Q.carrier)
    (haarIt : ∀ i A s, NilpotentExponentialHaarInput (Dt i A s).I.modelSpace (Dt i A s).I.carrier) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
      ∀ row : AffineNeighborRow T M F hunimod eW π bN Eall γ X βD
        haarN chartN hchartN pivot c B δ Profiles (Λ := Λ),
      row.label₂ = row.label₁ → row.offset₁ = row.offset₂ := by
  have hE : IsCompact Eall := M.isCompact_samplingPolytope T hunimod eW
  have hne : (Eall).Nonempty := ⟨0, by
    intro j
    simpa only [map_zero] using norm_nonneg (((M.supportIn T hunimod eW).weight j).toContinuousLinearMap)⟩
  apply exists_uniform_neighbor_offset_threshold T M F hunimod eW π bN Eall γ X βD
    haarN chartN hchartN pivot c B Profiles hExp dynkinN hE hne hγ hnz
  intro i A s
  exact M.exists_one_cone_offset_threshold T F hunimod eW
    hExp realize haarN haarD dynkinN dynkinD chartN hchartN chartD hchartD m νD
    π hπExp hdec hvan hΛ hπ hpath bN γ hγ X hDnil hDletters bD₀ βD hβD
    aN hmN aD hmD rem hdim pivot i (hcanonical i) (hunit i) (hcontact i) (hpositive i)
    hc hhi hB hcost hgap σchamber hσchamber Profiles
    (rootOffsetCone (M.supportIn T hunimod eW) hnz i s)
    (rootOffsetCone_salient (M.supportIn T hunimod eW) hnz i s)
    (weight_mem_rootOffsetCone (M.supportIn T hunimod eW) hnz i s)
    A (Ds i s) (dynkinI i s) (haarI i s) (Dt i A s) (haarQt i A s) (haarIt i A s)

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

theorem solution : type_of% @OAI.PolycyclicRecognition.CartanWordModel.exists_uniform_polar_offset_threshold_oai := @OAI.PolycyclicRecognition.CartanWordModel.exists_uniform_polar_offset_threshold_oai
