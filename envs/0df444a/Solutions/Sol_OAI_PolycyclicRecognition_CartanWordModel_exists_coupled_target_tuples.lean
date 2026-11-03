-- Prove2me | solution 1 for OAI.PolycyclicRecognition.CartanWordModel.exists_coupled_target_tuples
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-02T22:26:11.649833+00:00
-- url     : https://prove2.me/submissions/c7761f56-3ce4-4ff5-9cca-01aa974dc375

import Mathlib
import Definitions.Def_PolycyclicRecognition
import Definitions.Def_OAIQ093D027

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
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanWordBasis
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A homogeneous bracket-word basis of the Cartan ideal

This supplies actual nonzero-root letters and strictly positive integral
letter multiplicities for the nilpotent box data.
-/

noncomputable section

namespace PolycyclicRecognition

open LieAlgebra LieModule Module
open scoped BigOperators

variable {L : Type} [LieRing L] [LieAlgebra ℝ L]
  (H : LieSubalgebra ℝ L) [H.IsCartanSubalgebra]

set_option maxHeartbeats 1000000 in
theorem cartanGeneratorPool_lieSpan [FiniteDimensional ℝ L]
    {n : ℕ} (T : TriangularAdjoint L n) :
    LieSubalgebra.lieSpan ℝ (cartanRootIdeal H) (cartanGeneratorPool H) = ⊤ := by
  let N := cartanRootIdeal H
  let U := LieSubalgebra.lieSpan ℝ N (cartanGeneratorPool H)
  have himage : N.incl '' cartanGeneratorPool H =
      {v | ∃ χ : Weight ℝ H L, χ.IsNonZero ∧ v ∈ rootSpace H χ} := by
    ext v
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hx
    · intro hv
      have hN : v ∈ N := LieSubmodule.subset_lieSpan hv
      exact ⟨⟨v, hN⟩, hv, rfl⟩
  have hmap : U.map N.incl = N.toLieSubalgebra := by
    rw [LieSubalgebra.map_lieSpan, himage]
    change cartanRootSubalgebra H = N.toLieSubalgebra
    apply SetLike.coe_injective
    exact congrArg (fun V : Submodule ℝ L => (V : Set L))
      (cartanRootSubalgebra_eq_ideal H T)
  apply top_unique
  intro v _
  have hv : (v : L) ∈ U.map N.incl := by rw [hmap]; exact v.property
  obtain ⟨w, hw, heq⟩ := hv
  have : w = v := Subtype.ext heq
  change v ∈ U
  exact this ▸ hw

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanWordModel
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instDecidableEqConeMixedWords _root_.OAI.PolycyclicRecognition.CartanWordModel.instFintypeConeMixedWords _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The finite Cartan word model

The support datum uses all ordered bases selected from a finite list that
contains every nonzero evaluated word. It is therefore attached to the Lie
algebra generators, rather than to an extra family of assumed bases.
-/

noncomputable section

namespace PolycyclicRecognition

open Module LieModule LieAlgebra

variable {L : Type} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  (H : LieSubalgebra ℝ L) [H.IsCartanSubalgebra]

namespace CartanWordModel

variable {H} (M : CartanWordModel H)

set_option maxHeartbeats 1000000 in
omit [FiniteDimensional ℝ L] in
/-- No nonzero direction has been omitted by the finite cutoff. -/
theorem mem_wordList_of_eval_ne_zero (w : FreeMagma (Fin M.letterCount))
    (hw : evalBracketWord M.letter w ≠ 0) : w ∈ M.wordList := by
  apply (mem_boundedBracketWords _ _).mpr
  by_contra hn
  exact hw (evalBracketWord_eq_zero_of_depth M.letter M.bound_zero w (Nat.le_of_not_lt hn))

end CartanWordModel
end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_RescaledGeneratorBounds
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform bounds for normalized generator vectors

The same maximizing-basis exchange estimate which bounds structure constants
also bounds all exponentially rescaled generator vectors. Thus both parts of
the normalized Lie-law data lie in fixed bounded coordinate sets.
-/

noncomputable section

namespace PolycyclicRecognition

open Module

variable {I L : Type} [LieRing L] [LieAlgebra ℝ L] [Fintype I] [DecidableEq I]

/-- Uniform boundedness of all rescaled letters in every maximizing word basis. -/
theorem exists_uniform_rescaled_generator_bound
    (X : I → L) (S : Finset (FreeMagma I))
    (hS : ∀ i, FreeMagma.of i ∈ S) (b₀ : Basis (Fin (finrank ℝ L)) ℝ L) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (s : I → ℝ) (β : WordBasisSelections X S),
      IsMaximizingColumnBasis (wordListCoordinates X S b₀)
        (fun w => bracketWordExponent s w) β.val →
      ∀ r : ℝ, 0 ≤ r → ∀ i,
      ‖(exponentialRescaleBasis (WordBasisSelections.basis X S β)
        (fun j => bracketWordExponent s (β.val j)) r).equivFun
          (Real.exp (r * s i) • X i)‖ ≤ C := by
  obtain ⟨C, hC, hb⟩ := exists_uniform_normalized_coordinate_bound (wordListCoordinates X S b₀)
  refine ⟨C, hC, ?_⟩
  intro s β hβ r hr i
  apply (pi_norm_le_iff_of_nonneg hC).mpr
  intro j
  change |(exponentialRescaleBasis (WordBasisSelections.basis X S β)
    (fun j => bracketWordExponent s (β.val j)) r).repr (Real.exp (r * s i) • X i) j| ≤ C
  rw [repr_exponentialRescaleBasis_smul]
  have hh := hb (fun w => bracketWordExponent s w) β.val hβ ⟨.of i, hS i⟩ j r hr
  rw [columnCoordinates_eq_wordBasis_repr X S b₀ β] at hh
  simpa only [bracketWordExponent_of, evalBracketWord_of, Basis.equivFun_apply] using hh

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
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_RescaledLieFamily
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instDecidableEqConeMixedWords _root_.OAI.PolycyclicRecognition.CartanWordModel.instFintypeConeMixedWords _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
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

namespace CartanWordModel

variable [FiniteDimensional ℝ L] {H : LieSubalgebra ℝ L} [H.IsCartanSubalgebra]

omit [FiniteDimensional ℝ L] in
/-- Every actual Cartan letter occurs in the finite word list. -/
theorem letter_mem_wordList (M : CartanWordModel H) (i : Fin M.letterCount) :
    FreeMagma.of i ∈ M.wordList := by
  apply M.mem_wordList_of_eval_ne_zero
  change M.letter i ≠ 0
  intro hi
  have h := M.letter_quotient i
  rw [hi, map_zero] at h
  exact M.abelianBasis.ne_zero i h.symm

end CartanWordModel
end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_PolynomialEndpointSchemes
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.basisDynkinParameter_zero _root_.OAI.PolycyclicRecognition.dynkinRightTranslation_apply _root_.OAI.PolycyclicRecognition.dynkinRightTranslation_symm_apply _root_.OAI.PolycyclicRecognition.exponentialHomOfDynkin_apply_exp _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Smooth generator endpoint maps for varying polynomial laws

Each scheme is a fixed finite expression in the bracket, generators, and
its variable amplitudes. Consequently it remains smooth outside the set of
valid group laws, as required for the parameter-preserving submersion theorem.
-/

noncomputable section

namespace PolycyclicRecognition

open Module

variable {V P I : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup P] [NormedSpace ℝ P]

theorem contDiff_polynomialListProduct_ofFn {c n : ℕ} {k : ℕ∞}
    (a : DynkinCoefficients c 2) (B : P → V →L[ℝ] V →L[ℝ] V)
    (X : P → Fin n → V) (hB : ContDiff ℝ k B)
    (hX : ∀ i, ContDiff ℝ k (fun p => X p i)) :
    ContDiff ℝ k (fun p => polynomialListProduct (dynkinProduct a (B p)) (List.ofFn (X p))) := by
  induction n with
  | zero => simpa [List.ofFn_zero, polynomialListProduct] using
      (contDiff_const : ContDiff ℝ k (fun _ : P => (0 : V)))
  | succ n ih =>
    simp only [List.ofFn_succ, polynomialListProduct]
    exact contDiff_dynkinProduct a B _ _ hB (hX 0)
      (ih (fun p i => X p i.succ) (fun i => hX i.succ))

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_PolynomialDifferential
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Formal partial derivatives are the actual differential -/

noncomputable section

namespace PolycyclicRecognition

open MvPolynomial
open scoped BigOperators

theorem hasFDerivAt_mvPolynomial_eval {m : ℕ} (p : MvPolynomial (Fin m) ℝ)
    (x : Fin m → ℝ) :
    HasFDerivAt (fun y => MvPolynomial.eval y p) (polynomialDifferential p x) x := by
  classical
  induction p using MvPolynomial.induction_on with
  | C c => simpa [polynomialDifferential, pderiv_C] using hasFDerivAt_const c x
  | add p q hp hq =>
      simp only [map_add]
      refine (hp.add hq).congr_fderiv ?_
      simp [polynomialDifferential, add_smul, Finset.sum_add_distrib]
  | mul_X p j hp =>
      simp only [map_mul, MvPolynomial.eval_X]
      refine (hp.mul (hasFDerivAt_apply j x)).congr_fderiv ?_
      ext v
      simp [polynomialDifferential, Pi.single_apply, add_mul,
        Finset.sum_add_distrib, Finset.mul_sum, apply_ite, ite_mul, mul_assoc]

theorem polynomialDifferential_basis {m : ℕ} (p : MvPolynomial (Fin m) ℝ)
    (x : Fin m → ℝ) (j : Fin m) :
    polynomialDifferential p x (Pi.single j 1) = MvPolynomial.eval x (pderiv j p) := by
  classical
  simp [polynomialDifferential, Pi.single_apply]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_PolynomialMinor
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial derivative minors and their uniform degree bounds -/

noncomputable section

namespace PolycyclicRecognition

open MvPolynomial Matrix
open scoped BigOperators

theorem totalDegree_pderiv_le {m : ℕ} (p : MvPolynomial (Fin m) ℝ) (j : Fin m) :
    (pderiv j p).totalDegree ≤ p.totalDegree - 1 := by
  classical
  unfold totalDegree
  apply Finset.sup_le
  intro s hs
  have hc : (pderiv j p).coeff s ≠ 0 := mem_support_iff.mp hs
  rw [coeff_pderiv] at hc
  have hp : s + Finsupp.single j 1 ∈ p.support :=
    mem_support_iff.mpr (left_ne_zero_of_mul hc)
  have hd := le_totalDegree hp
  rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl),
    Finsupp.sum_single_index (by rfl)] at hd
  change (s.sum fun _ e => e) ≤ p.totalDegree - 1
  omega

theorem totalDegree_polynomialJacobianMinor_le {n k D : ℕ}
    (p : Fin n → MvPolynomial (Fin (n + k)) ℝ)
    (hp : ∀ i, (p i).totalDegree ≤ D) :
    (polynomialJacobianMinor p).totalDegree ≤ n * (D - 1) := by
  classical
  unfold polynomialJacobianMinor
  rw [Matrix.det_apply]
  apply totalDegree_finsetSum_le
  intro σ _
  calc
    _ ≤ (∏ i, pderiv (Fin.castAdd k i) (p (σ i))).totalDegree :=
      totalDegree_smul_le _ _
    _ ≤ ∑ i : Fin n, (pderiv (Fin.castAdd k i) (p (σ i))).totalDegree :=
      totalDegree_finsetProd _ _
    _ ≤ n * (D - 1) := by
      calc
        _ ≤ ∑ _i : Fin n, (D - 1) := Finset.sum_le_sum (fun i _ =>
          (totalDegree_pderiv_le _ _).trans (Nat.sub_le_sub_right (hp (σ i)) 1))
        _ = _ := by simp

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_PolynomialFamilies
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Fixed-degree polynomial formulas in the independent amplitudes -/

noncomputable section

namespace PolycyclicRecognition

open MvPolynomial
open scoped BigOperators

theorem hasPolynomialFormula_const {P : Type} {m : ℕ} (c : P → ℝ) :
    HasPolynomialFormula (fun a (_ : Fin m → ℝ) => c a) :=
  ⟨0, fun a => ⟨C (c a), by simp, fun _ => by simp⟩⟩

theorem hasPolynomialFormula_coordinate {P : Type} {m : ℕ} (j : Fin m) :
    HasPolynomialFormula (fun (_ : P) (x : Fin m → ℝ) => x j) :=
  ⟨1, fun _ => ⟨X j, by simp, fun _ => by simp⟩⟩

theorem HasPolynomialFormula.add {P : Type} {m : ℕ} {f g : P → (Fin m → ℝ) → ℝ}
    (hf : HasPolynomialFormula f) (hg : HasPolynomialFormula g) :
    HasPolynomialFormula (fun a x => f a x + g a x) := by
  obtain ⟨D, hD⟩ := hf
  obtain ⟨E, hE⟩ := hg
  refine ⟨D + E, fun a => ?_⟩
  obtain ⟨p, hp, he⟩ := hD a
  obtain ⟨q, hq, he'⟩ := hE a
  exact ⟨p + q, (totalDegree_add p q).trans (max_le (by omega) (by omega)),
    fun x => by simp [he, he']⟩

theorem HasPolynomialFormula.mul {P : Type} {m : ℕ} {f g : P → (Fin m → ℝ) → ℝ}
    (hf : HasPolynomialFormula f) (hg : HasPolynomialFormula g) :
    HasPolynomialFormula (fun a x => f a x * g a x) := by
  obtain ⟨D, hD⟩ := hf
  obtain ⟨E, hE⟩ := hg
  refine ⟨D + E, fun a => ?_⟩
  obtain ⟨p, hp, he⟩ := hD a
  obtain ⟨q, hq, he'⟩ := hE a
  exact ⟨p * q, (totalDegree_mul p q).trans (Nat.add_le_add hp hq),
    fun x => by simp [he, he']⟩

theorem hasPolynomialFormula_sum {P I : Type} {m : ℕ}
    (s : Finset I) (f : I → P → (Fin m → ℝ) → ℝ)
    (hf : ∀ i ∈ s, HasPolynomialFormula (f i)) :
    HasPolynomialFormula (fun a x => ∑ i ∈ s, f i a x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hasPolynomialFormula_const (P := P) (m := m) (fun _ => 0)
  | @insert i s hi ih =>
      have h₁ := hf i (Finset.mem_insert_self i s)
      have h₂ := ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))
      simpa only [Finset.sum_insert hi] using h₁.add h₂

theorem HasPolynomialCoordinates.exists_uniform_polynomials
    {P : Type} {m n : ℕ} {f : P → (Fin m → ℝ) → (Fin n → ℝ)}
    (hf : HasPolynomialCoordinates f) :
    ∃ D : ℕ, ∃ q : P → Fin n → MvPolynomial (Fin m) ℝ,
      (∀ a i, (q a i).totalDegree ≤ D) ∧
      ∀ a x i, MvPolynomial.eval x (q a i) = f a x i := by
  classical
  choose d hd using hf
  choose q hq hvalue using (fun a i => hd i a)
  refine ⟨∑ i, d i, q, ?_, fun a x i => hvalue a i x⟩
  intro a i
  exact (hq a i).trans (Finset.single_le_sum (fun j _ => Nat.zero_le (d j)) (Finset.mem_univ i))

theorem hasPolynomialCoordinates_const {P : Type} {m n : ℕ} (v : P → Fin n → ℝ) :
    HasPolynomialCoordinates (fun a (_ : Fin m → ℝ) => v a) :=
  fun i => hasPolynomialFormula_const (fun a => v a i)

theorem HasPolynomialCoordinates.smul {P : Type} {m n : ℕ}
    {f : P → (Fin m → ℝ) → (Fin n → ℝ)} {t : P → (Fin m → ℝ) → ℝ}
    (hf : HasPolynomialCoordinates f) (ht : HasPolynomialFormula t) :
    HasPolynomialCoordinates (fun a x => t a x • f a x) :=
  fun i => ht.mul (hf i)

theorem bilinear_pi_expansion {n : ℕ}
    (B : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) (v w : Fin n → ℝ) :
    B v w = ∑ i : Fin n, ∑ j : Fin n,
      (v i * w j) • B (Pi.single i 1) (Pi.single j 1) := by
  calc
    B v w = B (∑ i, v i • Pi.single i 1) (∑ j, w j • Pi.single j 1) := by
      rw [← pi_eq_sum_univ' v, ← pi_eq_sum_univ' w]
    _ = _ := by
      simp only [map_sum, map_smul, sum_apply,
        smul_apply, Finset.smul_sum, smul_smul]
      rw [Finset.sum_comm]
      simp only [mul_comm]

theorem HasPolynomialCoordinates.bilinear {P : Type} {m n : ℕ}
    (B : P → (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] (Fin n → ℝ))
    {f g : P → (Fin m → ℝ) → (Fin n → ℝ)}
    (hf : HasPolynomialCoordinates f) (hg : HasPolynomialCoordinates g) :
    HasPolynomialCoordinates (fun a x => B a (f a x) (g a x)) := by
  intro l
  have he : (fun a x => B a (f a x) (g a x) l) =
      (fun a x => ∑ i : Fin n, ∑ j : Fin n,
        (f a x i * g a x j) * B a (Pi.single i 1) (Pi.single j 1) l) := by
    funext a x
    rw [bilinear_pi_expansion]
    simp
  rw [he]
  apply hasPolynomialFormula_sum
  intro i _
  apply hasPolynomialFormula_sum
  intro j _
  exact ((hf i).mul (hg j)).mul (hasPolynomialFormula_const
    (fun a => B a (Pi.single i 1) (Pi.single j 1) l))

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_PolynomialEndpointCoordinates
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.basisDynkinParameter_zero _root_.OAI.PolycyclicRecognition.dynkinRightTranslation_apply _root_.OAI.PolycyclicRecognition.dynkinRightTranslation_symm_apply _root_.OAI.PolycyclicRecognition.exponentialHomOfDynkin_apply_exp _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual generator endpoint schemes have uniformly bounded degree -/

noncomputable section

namespace PolycyclicRecognition

open scoped BigOperators

theorem hasPolynomialCoordinates_sum {P I : Type} {m n : ℕ}
    (s : Finset I) (f : I → P → (Fin m → ℝ) → (Fin n → ℝ))
    (hf : ∀ i ∈ s, HasPolynomialCoordinates (f i)) :
    HasPolynomialCoordinates (fun a x => ∑ i ∈ s, f i a x) := by
  intro l
  simpa only [Finset.sum_apply] using hasPolynomialFormula_sum s
    (fun i a x => f i a x l) (fun i hi => hf i hi l)

theorem hasPolynomialCoordinates_evalBilinearWord
    {P I : Type} {m n : ℕ}
    (B : P → (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] (Fin n → ℝ))
    (X : P → (Fin m → ℝ) → I → (Fin n → ℝ))
    (hX : ∀ i, HasPolynomialCoordinates (fun a x => X a x i)) (w : FreeMagma I) :
    HasPolynomialCoordinates (fun a x => evalBilinearWord (B a) (X a x) w) := by
  induction w using FreeMagma.rec with
  | of i => exact hX i
  | mul u v hu hv => exact hu.bilinear B hv

theorem hasPolynomialCoordinates_bilinearDynkin
    {P : Type} {m n c l : ℕ} (a : DynkinCoefficients c l)
    (B : P → (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] (Fin n → ℝ))
    (X : P → (Fin m → ℝ) → Fin l → (Fin n → ℝ))
    (hX : ∀ i, HasPolynomialCoordinates (fun b x => X b x i)) :
    HasPolynomialCoordinates (fun b x => bilinearDynkinPolynomial a (B b) (X b x)) := by
  apply hasPolynomialCoordinates_sum
  intro d _
  apply hasPolynomialCoordinates_sum
  intro w _
  exact (hasPolynomialCoordinates_evalBilinearWord B X hX _).smul
    (hasPolynomialFormula_const (fun _ => a d w))

theorem hasPolynomialCoordinates_dynkinProduct
    {P : Type} {m n c : ℕ} (a : DynkinCoefficients c 2)
    (B : P → (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] (Fin n → ℝ))
    {f g : P → (Fin m → ℝ) → (Fin n → ℝ)}
    (hf : HasPolynomialCoordinates f) (hg : HasPolynomialCoordinates g) :
    HasPolynomialCoordinates (fun b x => dynkinProduct a (B b) (f b x) (g b x)) := by
  apply hasPolynomialCoordinates_bilinearDynkin a B (fun b x => ![f b x, g b x])
  intro i
  fin_cases i
  · exact hf
  · exact hg

theorem hasPolynomialCoordinates_listProduct
    {P : Type} {m n c l : ℕ} (a : DynkinCoefficients c 2)
    (B : P → (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] (Fin n → ℝ))
    (X : P → (Fin m → ℝ) → Fin l → (Fin n → ℝ))
    (hX : ∀ i, HasPolynomialCoordinates (fun b x => X b x i)) :
    HasPolynomialCoordinates (fun b x =>
      polynomialListProduct (dynkinProduct a (B b)) (List.ofFn (X b x))) := by
  induction l with
  | zero => simpa [polynomialListProduct] using
      hasPolynomialCoordinates_const (m := m) (fun _ : P => (0 : Fin n → ℝ))
  | succ l ih =>
    simp only [List.ofFn_succ, polynomialListProduct]
    exact hasPolynomialCoordinates_dynkinProduct a B (hX 0)
      (ih (fun b x i => X b x i.succ) (fun i => hX i.succ))

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_SurjectiveColumns
attribute [-instance] _root_.GeneratesNS.fintype_closedBall _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A surjective differential has a fixed nonzero column minor -/

noncomputable section

namespace PolycyclicRecognition

open Module Set

theorem exists_nonsingular_column_minor {n m : ℕ}
    (A : (Fin m → ℝ) →ₗ[ℝ] (Fin n → ℝ)) (hA : Function.Surjective A) :
    ∃ j : Fin n → Fin m, Function.Injective j ∧
      (Matrix.of fun i k => A (Pi.single (j k) 1) i).det ≠ 0 := by
  classical
  let v : Fin m → (Fin n → ℝ) := fun i => A (Pi.single i 1)
  have hspan : ⊤ ≤ Submodule.span ℝ (range v) := by
    intro y _
    obtain ⟨x, rfl⟩ := hA y
    rw [pi_eq_sum_univ' x, map_sum]
    apply Submodule.sum_mem
    intro i _
    rw [map_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (mem_range_self i))
  let J := (linearIndepOn_empty ℝ (id : (Fin n → ℝ) → (Fin n → ℝ))).extend (empty_subset (range v))
  let b : Basis J ℝ (Fin n → ℝ) := Basis.ofSpan hspan
  let : Fintype J := Fintype.ofFinite _
  let e : J ≃ Fin n := Fintype.equivFinOfCardEq (by simpa using (finrank_eq_card_basis b).symm)
  let b' := b.reindex e
  have hb (k : Fin n) : ∃ i, v i = b' k := by
    simpa only [b', Basis.coe_reindex, Function.comp_apply, Set.mem_range] using
      (Basis.ofSpan_subset hspan (show b (e.symm k) ∈ range b from ⟨_, rfl⟩))
  choose j hj using hb
  refine ⟨j, ?_, ?_⟩
  · intro x y hxy
    apply b'.injective
    rw [← hj x, ← hj y, hxy]
  · have he : (Matrix.of fun i k => A (Pi.single (j k) 1) i) =
        LinearMap.toMatrix' b'.equivFun.symm.toLinearMap := by
      ext i k
      rw [LinearMap.toMatrix'_apply]
      change A (Pi.single (j k) 1) i = b'.equivFun.symm (Pi.single k 1) i
      have hs : b'.equivFun.symm (Pi.single k 1) = b' k := by
        apply b'.equivFun.injective
        simp
      rw [hs]
      exact congrFun (hj k) i
    rw [he, LinearMap.det_toMatrix']
    exact b'.equivFun.symm.isUnit_det'.ne_zero

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_AlternatingPolynomialCoordinates
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial and smooth coordinates for the alternating product

These coordinates keep the two embedding maps among the coefficient
parameters. The input chart can be any fixed continuous linear equivalence.
-/

noncomputable section
namespace PolycyclicRecognition

open scoped BigOperators

theorem hasPolynomialCoordinates_linear {P : Type} {m n : ℕ}
    (L : P → (Fin m → ℝ) →L[ℝ] (Fin n → ℝ)) :
    HasPolynomialCoordinates (fun p x => L p x) := by
  have he (p : P) (x : Fin m → ℝ) :
      L p x = ∑ i, x i • L p (Pi.single i 1) := by
    conv_lhs => rw [pi_eq_sum_univ' x]
    simp only [map_sum, map_smul]
  intro j
  have hj : (fun p x => L p x j) =
      (fun p x => ∑ i, x i * L p (Pi.single i 1) j) := by
    funext p x
    rw [he p x]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [hj]
  apply hasPolynomialFormula_sum
  intro i _
  exact (hasPolynomialFormula_coordinate i).mul
    (hasPolynomialFormula_const (fun p => L p (Pi.single i 1) j))

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_AutocorrelationRecurrence
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The positive autocorrelation behind backward recurrence -/

noncomputable section

namespace PolycyclicRecognition

open MeasureTheory Set
open scoped ENNReal

variable {G : Type} [Group G] [MeasurableSpace G]
  [MeasurableMul₂ G] [MeasurableInv G]

theorem measurable_rightInverseAverage (σ : Measure G) [SFinite σ]
    {f : G → ℝ≥0∞} (hf : Measurable f) :
    Measurable (rightInverseAverage σ f) := by
  apply Measurable.lintegral_prod_right (f := fun x s : G => f (x * s⁻¹))
  exact hf.comp (measurable_fst.mul measurable_snd.inv)

omit [MeasurableMul₂ G] [MeasurableInv G] in
theorem rightInverseAverage_le_one (σ : Measure G) [IsProbabilityMeasure σ]
    {f : G → ℝ≥0∞} (hf : ∀ x, f x ≤ 1) (x : G) :
    rightInverseAverage σ f x ≤ 1 := by
  calc
    _ ≤ ∫⁻ _ : G, (1 : ℝ≥0∞) ∂σ := lintegral_mono (fun s => hf (x * s⁻¹))
    _ = 1 := by simp

omit [MeasurableMul₂ G] [MeasurableInv G] in
/-- The averaged indicator vanishes outside the product of its original
set and a set carrying the increment law. This is the support bound used
in Cauchy--Schwarz. -/
theorem rightInverseAverage_indicator_eq_zero
    (σ : Measure G) (A K R : Set G) (hK : ∀ᵐ s ∂σ, s ∈ K)
    (hAR : ∀ a ∈ A, ∀ s ∈ K, a * s ∈ R) {x : G} (hx : x ∉ R) :
    rightInverseAverage σ (A.indicator (fun _ => (1 : ℝ≥0∞))) x = 0 := by
  apply lintegral_eq_zero_of_ae_eq_zero
  filter_upwards [hK] with s hs
  apply indicator_of_notMem
  intro hxs
  apply hx
  simpa only [inv_mul_cancel_right] using hAR (x * s⁻¹) hxs s hs

/-- The transition law obtained from two independent copies of the same
increment has nonnegative quadratic form. The square identity is exact and
uses right Haar invariance and Tonelli, with no symmetry assumption on σ. -/
theorem right_autocorrelation_eq_square
    (μ σ : Measure G) [SFinite μ] [SFinite σ] [μ.IsMulRightInvariant]
    (f : G → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ x, f x * (∫⁻ s, rightInverseAverage σ f (x * s) ∂σ) ∂μ) =
      ∫⁻ z, rightInverseAverage σ f z ^ 2 ∂μ := by
  have hA := measurable_rightInverseAverage σ hf
  have hprod : Measurable (fun p : G × G => f p.1 * rightInverseAverage σ f (p.1 * p.2)) :=
    (hf.comp measurable_fst).mul (hA.comp (measurable_fst.mul measurable_snd))
  calc
    _ = ∫⁻ x, ∫⁻ s, f x * rightInverseAverage σ f (x * s) ∂σ ∂μ := by
      apply lintegral_congr
      intro x
      exact (lintegral_const_mul _ (hA.comp (measurable_const.mul measurable_id))).symm
    _ = ∫⁻ s, ∫⁻ x, f x * rightInverseAverage σ f (x * s) ∂μ ∂σ :=
      lintegral_lintegral_swap hprod.aemeasurable
    _ = ∫⁻ s, ∫⁻ z, f (z * s⁻¹) * rightInverseAverage σ f z ∂μ ∂σ := by
      apply lintegral_congr
      intro s
      have h := lintegral_mul_right_eq_self (μ := μ)
        (fun z => f (z * s⁻¹) * rightInverseAverage σ f z) s
      simpa only [mul_inv_cancel_right] using h
    _ = ∫⁻ z, ∫⁻ s, f (z * s⁻¹) * rightInverseAverage σ f z ∂σ ∂μ := by
      apply lintegral_lintegral_swap
      exact ((hf.comp (measurable_snd.mul measurable_fst.inv)).mul
        (hA.comp measurable_snd)).aemeasurable
    _ = _ := by
      apply lintegral_congr
      intro z
      have hz : Measurable (fun s => f (z * s⁻¹)) :=
        hf.comp (measurable_const.mul measurable_inv)
      rw [lintegral_mul_const _ hz]
      simp only [pow_two, rightInverseAverage]

/-- The first averaged function has the same total mass as the original
one. This is the second input to the recurrence lower bound. -/
theorem lintegral_rightInverseAverage
    (μ σ : Measure G) [SFinite μ] [IsProbabilityMeasure σ] [μ.IsMulRightInvariant]
    (f : G → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ z, rightInverseAverage σ f z ∂μ) = ∫⁻ z, f z ∂μ := by
  change (∫⁻ z, ∫⁻ s, f (z * s⁻¹) ∂σ ∂μ) = _
  have hm : Measurable (fun p : G × G => f (p.1 * p.2⁻¹)) :=
    hf.comp (measurable_fst.mul measurable_snd.inv)
  rw [lintegral_lintegral_swap (f := fun z s : G => f (z * s⁻¹)) hm.aemeasurable]
  simp only [lintegral_mul_right_eq_self, lintegral_const, measure_univ, mul_one]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_RecurrenceIntegralBounds
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Quantitative integral bounds used by backward recurrence -/

noncomputable section

namespace PolycyclicRecognition

open MeasureTheory Set Filter

/-- Cauchy--Schwarz against the constant function, proved directly by the
nonnegativity of variance. The measure need only have positive finite mass. -/
theorem sq_integral_le_mass_mul_integral_sq
    {X : Type} [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]
    (hM : 0 < μ.real univ) (f : X → ℝ) (hf : Integrable f μ)
    (hf2 : Integrable (fun x => f x ^ 2) μ) :
    (∫ x, f x ∂μ) ^ 2 ≤ μ.real univ * ∫ x, f x ^ 2 ∂μ := by
  let M := μ.real univ
  let I := ∫ x, f x ∂μ
  let a := I / M
  have ha : a * M = I := div_mul_cancel₀ I hM.ne'
  have hi : Integrable (fun x => f x ^ 2 - (2 * a) * f x) μ :=
    hf2.sub (hf.const_mul _)
  have heq : (∫ x, (f x - a) ^ 2 ∂μ) =
      (∫ x, f x ^ 2 ∂μ) - (2 * a) * I + a ^ 2 * M := by
    calc
      _ = ∫ x, (f x ^ 2 - (2 * a) * f x) + a ^ 2 ∂μ := by
        apply integral_congr_ae
        exact Eventually.of_forall (fun x => by ring)
      _ = _ := by
        rw [integral_add hi (integrable_const _), integral_sub hf2 (hf.const_mul _),
          integral_const_mul, integral_const]
        simp only [smul_eq_mul, M, I]
        ring
  have hpos : 0 ≤ (∫ x, f x ^ 2 ∂μ) - (2 * a) * I + a ^ 2 * M := by
    rw [← heq]
    exact integral_nonneg (fun x => sq_nonneg (f x - a))
  have halg : M * ((∫ x, f x ^ 2 ∂μ) - (2 * a) * I + a ^ 2 * M) =
      M * (∫ x, f x ^ 2 ∂μ) - I ^ 2 := by
    calc
      _ = M * (∫ x, f x ^ 2 ∂μ) - 2 * (a * M) * I + (a * M) ^ 2 := by ring
      _ = _ := by rw [ha]; ring
  have hnonneg := mul_nonneg hM.le hpos
  rw [halg] at hnonneg
  exact sub_nonneg.mp hnonneg

/-- A bounded transition function can carry a large integral only if its
superlevel set has large measure. -/
theorem integral_le_superlevel_mass_add
    {X : Type} [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]
    (f : X → ℝ) (hf : Measurable f) (hbound : ∀ x, 0 ≤ f x ∧ f x ≤ 1)
    {t : ℝ} (ht : 0 ≤ t) :
    (∫ x, f x ∂μ) ≤ μ.real {x | t ≤ f x} + t * μ.real univ := by
  let S := {x | t ≤ f x}
  have hS : MeasurableSet S := measurableSet_le measurable_const hf
  have hfi : Integrable f μ := Integrable.of_bound hf.aestronglyMeasurable 1
    (Eventually.of_forall (fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hbound x).1]
      exact (hbound x).2))
  have hI : Integrable (S.indicator (fun _ : X => (1 : ℝ))) μ :=
    (integrable_const (1 : ℝ)).indicator hS
  have hle : (∫ x, f x ∂μ) ≤ ∫ x, S.indicator (fun _ => (1 : ℝ)) x + t ∂μ := by
    apply integral_mono hfi (hI.add (integrable_const t))
    intro x
    change f x ≤ S.indicator (fun _ => (1 : ℝ)) x + t
    by_cases hx : x ∈ S
    · rw [indicator_of_mem hx]
      linarith [(hbound x).2]
    · rw [indicator_of_notMem hx]
      have hn : ¬ t ≤ f x := hx
      simpa only [zero_add] using (lt_of_not_ge hn).le
  rw [integral_add hI (integrable_const t), integral_indicator_const (1 : ℝ) hS,
    integral_const] at hle
  simpa only [smul_eq_mul, mul_one, mul_comm _ t] using hle

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_AutocorrelationLowerBound
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The quantitative lower bound for a two-sample return -/

noncomputable section

namespace PolycyclicRecognition

open MeasureTheory Set Filter
open scoped ENNReal

/-- A function with values in `[0,1]`, supported in a finite-volume region,
has square integral at least its squared mass divided by that volume. -/
theorem sq_mass_le_region_mul_square_mass
    {X : Type} [MeasurableSpace X] (μ : Measure X)
    (f : X → ℝ≥0∞) (hf : Measurable f) (hb : ∀ x, f x ≤ 1)
    (R : Set X) (hRfin : μ R ≠ ∞) (hRpos : 0 < (μ R).toReal)
    (hsupp : ∀ x, x ∉ R → f x = 0) :
    (∫⁻ x, f x ∂μ).toReal ^ 2 ≤ (μ R).toReal * (∫⁻ x, f x ^ 2 ∂μ).toReal := by
  let ν := μ.restrict R
  let : IsFiniteMeasure ν := ⟨by simpa only [ν, Measure.restrict_apply_univ] using hRfin.lt_top⟩
  have hfn (x : X) : f x ≠ ∞ := (hb x).trans_lt (by simp) |>.ne
  have hr (x : X) : 0 ≤ (f x).toReal ∧ (f x).toReal ≤ 1 :=
    ⟨ENNReal.toReal_nonneg, by simpa using ENNReal.toReal_mono (by simp) (hb x)⟩
  have hfi : Integrable (fun x => (f x).toReal) ν :=
    Integrable.of_bound hf.ennreal_toReal.aestronglyMeasurable 1
      (Eventually.of_forall (fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hr x).1]
        exact (hr x).2))
  have hfi2 : Integrable (fun x => (f x).toReal ^ 2) ν :=
    Integrable.of_bound (hf.ennreal_toReal.pow_const 2).aestronglyMeasurable 1
      (Eventually.of_forall (fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        nlinarith [(hr x).1, (hr x).2]))
  have hregion : Function.support f ⊆ R := by
    intro x hx
    by_contra hn
    exact hx (hsupp x hn)
  have hregion2 : Function.support (fun x => f x ^ 2) ⊆ R := by
    intro x hx
    by_contra hn
    exact hx (by simp [hsupp x hn])
  have hI : (∫ x, (f x).toReal ∂ν) = (∫⁻ x, f x ∂μ).toReal := by
    rw [integral_toReal hf.aemeasurable (Eventually.of_forall (fun x => (hfn x).lt_top))]
    congr 1
    exact setLIntegral_eq_of_support_subset hregion
  have hI2 : (∫ x, (f x).toReal ^ 2 ∂ν) = (∫⁻ x, f x ^ 2 ∂μ).toReal := by
    simp_rw [← ENNReal.toReal_pow]
    rw [integral_toReal (hf.pow_const 2).aemeasurable
      (Eventually.of_forall (fun x => by exact ENNReal.pow_ne_top (hfn x) |>.lt_top))]
    congr 1
    exact setLIntegral_eq_of_support_subset hregion2
  have h := sq_integral_le_mass_mul_integral_sq ν
    (by simpa only [measureReal_def, ν, Measure.restrict_apply_univ] using hRpos)
    (fun x => (f x).toReal) hfi hfi2
  simpa only [hI, hI2, measureReal_def, ν, Measure.restrict_apply_univ] using h

/-- The mean probability of returning to `A` after a difference of two
independent increments has the required quadratic lower bound. The region
`R` can be the compact product `Q * support σ` in the application. -/
theorem return_correlation_lower_bound
    {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]
    (μ σ : Measure G) [SFinite μ] [IsProbabilityMeasure σ] [μ.IsMulRightInvariant]
    (A K R : Set G) (hA : MeasurableSet A) (hK : ∀ᵐ s ∂σ, s ∈ K)
    (hRfin : μ R ≠ ∞) (hRpos : 0 < (μ R).toReal)
    (hAR : ∀ a ∈ A, ∀ s ∈ K, a * s ∈ R) :
    (μ A).toReal ^ 2 ≤ (μ R).toReal *
      (∫⁻ x in A, ∫⁻ s₁, ∫⁻ s₂,
        A.indicator (fun _ => (1 : ℝ≥0∞)) (x * s₁ * s₂⁻¹) ∂σ ∂σ ∂μ).toReal := by
  let f := A.indicator (fun _ => (1 : ℝ≥0∞))
  have hf : Measurable f := measurable_const.indicator hA
  have hb : ∀ x, f x ≤ 1 := indicator_le_self' (fun _ _ => bot_le)
  have h := sq_mass_le_region_mul_square_mass μ (rightInverseAverage σ f)
    (measurable_rightInverseAverage σ hf) (rightInverseAverage_le_one σ hb)
    R hRfin hRpos (fun x hx => rightInverseAverage_indicator_eq_zero σ A K R hK hAR hx)
  rw [lintegral_rightInverseAverage μ σ f hf, lintegral_indicator_const hA, one_mul,
    ← right_autocorrelation_eq_square μ σ f hf] at h
  have heq : (fun x => f x * (∫⁻ s, rightInverseAverage σ f (x * s) ∂σ)) =
      A.indicator (fun x => ∫⁻ s₁, ∫⁻ s₂, f (x * s₁ * s₂⁻¹) ∂σ ∂σ) := by
    funext x
    by_cases hx : x ∈ A <;> simp [f, hx, rightInverseAverage]
  rw [heq, lintegral_indicator hA] at h
  exact h

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_SubexponentialBounds
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The finite algebra of subexponential losses -/

namespace PolycyclicRecognition

open Filter
open scoped Topology

theorem subexponential_lower_const {c : ℝ} (hc : 0 < c) :
    HasSubexponentialLowerBound (fun _ => c) := by
  intro ε hε
  have ht := Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.const_mul_atTop hε)
  have he := ht.eventually (gt_mem_nhds hc)
  simpa only [Function.comp_def, id_eq, neg_mul] using he.mono (fun _ h => h.le)

end PolycyclicRecognition

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_BackwardRecurrenceStep
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # One quantitative step of backward recurrence -/

noncomputable section

namespace PolycyclicRecognition

open MeasureTheory Set Filter
open scoped ENNReal

variable {G : Type} [Group G] [MeasurableSpace G]
  [MeasurableMul₂ G] [MeasurableInv G]

theorem measurable_twoSampleReturn (σ : Measure G) [SFinite σ]
    {A : Set G} (hA : MeasurableSet A) : Measurable (twoSampleReturn σ A) := by
  have hchi : Measurable (A.indicator (fun _ => (1 : ℝ≥0∞))) :=
    measurable_const.indicator hA
  have hm := measurable_rightInverseAverage σ hchi
  exact Measurable.lintegral_prod_right (f := fun x s : G =>
    rightInverseAverage σ (A.indicator (fun _ => (1 : ℝ≥0∞))) (x * s))
    (hm.comp (measurable_fst.mul measurable_snd))

omit [MeasurableMul₂ G] [MeasurableInv G] in
theorem twoSampleReturn_le_one (σ : Measure G) [IsProbabilityMeasure σ]
    (A : Set G) (x : G) : twoSampleReturn σ A x ≤ 1 := by
  calc
    _ ≤ ∫⁻ _ : G, ∫⁻ _ : G, (1 : ℝ≥0∞) ∂σ ∂σ := by
      apply lintegral_mono
      intro s
      apply lintegral_mono
      intro t
      exact indicator_le_self' (fun _ _ => bot_le) _
    _ = 1 := by simp

/-- Discarding points with small return probability retains a definite
quadratic fraction of the original set. This is the backward construction
used to keep every intermediate sheet in the prescribed good set. -/
theorem exists_backward_recurrence_step
    (μ σ : Measure G) [SFinite μ] [IsProbabilityMeasure σ] [μ.IsMulRightInvariant]
    (A Q K R : Set G) (hA : MeasurableSet A) (hQfin : μ Q ≠ ∞)
    (hAQ : A ⊆ Q) (hApos : 0 < (μ A).toReal) (hQpos : 0 < (μ Q).toReal)
    (hK : ∀ᵐ s ∂σ, s ∈ K) (hRfin : μ R ≠ ∞) (hRpos : 0 < (μ R).toReal)
    (hAR : ∀ a ∈ A, ∀ s ∈ K, a * s ∈ R)
    {D : ℝ} (hD : 0 < D) (hvol : (μ R).toReal ≤ D * (μ Q).toReal) :
    ∃ B : Set G, MeasurableSet B ∧ B ⊆ A ∧ 0 < (μ B).toReal ∧
      (μ A).toReal ^ 2 / (2 * D * (μ Q).toReal) ≤ (μ B).toReal ∧
      ∀ x ∈ B, (μ A).toReal / (2 * D * (μ Q).toReal) ≤
        (twoSampleReturn σ A x).toReal := by
  let ν := μ.restrict A
  have hAfin : μ A ≠ ∞ := (lt_of_le_of_lt (measure_mono hAQ) hQfin.lt_top).ne
  let : IsFiniteMeasure ν := ⟨by simpa only [ν, Measure.restrict_apply_univ] using hAfin.lt_top⟩
  let p : G → ℝ := fun x => (twoSampleReturn σ A x).toReal
  have hpm : Measurable p := (measurable_twoSampleReturn σ hA).ennreal_toReal
  have hp (x : G) : 0 ≤ p x ∧ p x ≤ 1 :=
    ⟨ENNReal.toReal_nonneg, by simpa using ENNReal.toReal_mono (by simp) (twoSampleReturn_le_one σ A x)⟩
  have hI : (∫ x, p x ∂ν) = (∫⁻ x in A, twoSampleReturn σ A x ∂μ).toReal := by
    exact integral_toReal (measurable_twoSampleReturn σ hA).aemeasurable
      (Eventually.of_forall (fun x => (twoSampleReturn_le_one σ A x).trans_lt (by simp)))
  have hlow : (μ A).toReal ^ 2 ≤ (D * (μ Q).toReal) * ∫ x, p x ∂ν := by
    have h := return_correlation_lower_bound μ σ A K R hA hK hRfin hRpos hAR
    change (μ A).toReal ^ 2 ≤ (μ R).toReal *
      (∫⁻ x in A, twoSampleReturn σ A x ∂μ).toReal at h
    rw [← hI] at h
    exact h.trans (mul_le_mul_of_nonneg_right hvol (integral_nonneg (fun x => (hp x).1)))
  let M := D * (μ Q).toReal
  have hM : 0 < M := mul_pos hD hQpos
  let t := (μ A).toReal / (2 * M)
  let B := A ∩ {x | t ≤ p x}
  have hlevel : MeasurableSet {x | t ≤ p x} := measurableSet_le measurable_const hpm
  have hBm : MeasurableSet B := hA.inter hlevel
  have hmass : ν.real {x | t ≤ p x} = (μ B).toReal := by
    simp only [measureReal_def, ν, Measure.restrict_apply hlevel, B, inter_comm]
  have hu := integral_le_superlevel_mass_add ν p hpm hp (div_nonneg hApos.le (by positivity : 0 ≤ 2 * M))
  change (∫ x, p x ∂ν) ≤ ν.real {x | t ≤ p x} + t * ν.real univ at hu
  rw [hmass, show ν.real univ = (μ A).toReal by simp [measureReal_def, ν]] at hu
  have htM : t * M = (μ A).toReal / 2 := by dsimp [t]; field_simp
  have hmul : M * (∫ x, p x ∂ν) ≤ M * (μ B).toReal + (μ A).toReal ^ 2 / 2 := by
    calc
      _ ≤ M * ((μ B).toReal + t * (μ A).toReal) := mul_le_mul_of_nonneg_left hu hM.le
      _ = M * (μ B).toReal + (t * M) * (μ A).toReal := by ring
      _ = _ := by rw [htM]; ring
  have hbnd : (μ A).toReal ^ 2 / (2 * M) ≤ (μ B).toReal := by
    apply (div_le_iff₀ (mul_pos (by norm_num) hM)).mpr
    change (μ A).toReal ^ 2 ≤ M * (∫ x, p x ∂ν) at hlow
    nlinarith [hlow, hmul]
  have hBpos : 0 < (μ B).toReal :=
    (div_pos (sq_pos_of_pos hApos) (mul_pos (by norm_num) hM)).trans_le hbnd
  refine ⟨B, hBm, inter_subset_left, hBpos, ?_, ?_⟩
  · simpa only [M, mul_assoc] using hbnd
  · intro x hx
    have hx' : t ≤ p x := hx.2
    simpa only [t, p, M, mul_assoc] using hx'

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_BackwardSwitchProbability
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Probability of retaining every intermediate sheet -/

noncomputable section

namespace PolycyclicRecognition

open MeasureTheory Set
open scoped ENNReal NNReal

variable {G : Type} [Group G] [MeasurableSpace G]

theorem switchThresholdProduct_ne_top (τ : ℕ → ℝ≥0) (n k : ℕ) :
    switchThresholdProduct τ n k ≠ ∞ := by
  induction k generalizing n with
  | zero => simp [switchThresholdProduct]
  | succ k ih => exact ENNReal.mul_ne_top ENNReal.coe_ne_top (ih (n + 1))

theorem switchThresholdProduct_pos (τ : ℕ → ℝ≥0) (n k : ℕ)
    (hτ : ∀ j, n ≤ j → j < n + k → 0 < τ j) :
    0 < switchThresholdProduct τ n k := by
  induction k generalizing n with
  | zero => simp [switchThresholdProduct]
  | succ k ih =>
    apply ENNReal.mul_pos
    · exact_mod_cast (hτ n le_rfl (by omega)).ne'
    · exact (ih (n + 1) (fun j hj hj' => hτ j (by omega) (by omega))).ne'

/-- Independent sampling multiplies the conditional return bounds. The
sets may differ at each stage, which is essential for backward recurrence. -/
theorem switchThresholdProduct_le_survival
    (σ : ℕ → Measure G) (S : ℕ → Set G) (τ : ℕ → ℝ≥0)
    (n k : ℕ)
    (hreturn : ∀ j, j < n + k → ∀ x ∈ S j,
      (τ j : ℝ≥0∞) ≤ twoSampleReturn (σ j) (S (j + 1)) x)
    {x : G} (hx : x ∈ S n) :
    switchThresholdProduct τ n k ≤ survivingSwitchProbability σ S n k x := by
  induction k generalizing n x with
  | zero => rfl
  | succ k ih =>
    let P := switchThresholdProduct τ (n + 1) k
    have hP : P ≠ ∞ := switchThresholdProduct_ne_top τ (n + 1) k
    have hnext (y : G) (hy : y ∈ S (n + 1)) :
        P ≤ survivingSwitchProbability σ S (n + 1) k y := by
      apply ih (n + 1) (fun j hj => hreturn j (by omega)) hy
    have hbound : P * twoSampleReturn (σ n) (S (n + 1)) x ≤
        survivingSwitchProbability σ S n (k + 1) x := by
      calc
        _ = ∫⁻ s₁, ∫⁻ s₂,
            P * (S (n + 1)).indicator (fun _ => (1 : ℝ≥0∞)) (x * s₁ * s₂⁻¹)
              ∂σ n ∂σ n := by
          rw [twoSampleReturn, ← lintegral_const_mul' P _ hP]
          apply lintegral_congr
          intro s₁
          exact (lintegral_const_mul' P _ hP).symm
        _ ≤ _ := by
          apply lintegral_mono
          intro s₁
          apply lintegral_mono
          intro s₂
          by_cases hy : x * s₁ * s₂⁻¹ ∈ S (n + 1)
          · simpa only [indicator_of_mem hy, mul_one] using hnext _ hy
          · simp only [indicator_of_notMem hy, mul_zero, le_refl]
    change (τ n : ℝ≥0∞) * P ≤ _
    calc
      _ = P * (τ n : ℝ≥0∞) := mul_comm _ _
      _ ≤ P * twoSampleReturn (σ n) (S (n + 1)) x :=
        mul_le_mul' le_rfl (hreturn n (by omega) x hx)
      _ ≤ _ := hbound

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_BackwardRecurrenceSets
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Nested positive-measure sets for a fixed sequence of switches -/

noncomputable section

namespace PolycyclicRecognition

open MeasureTheory Set
open scoped ENNReal

/-- Iterating the quantitative return estimate backwards produces the
nested sets used in the segment-volume argument. The number and order of
the increment laws are fixed before this construction. -/
theorem exists_backward_recurrence_sets
    {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]
    (μ : Measure G) [SFinite μ] [μ.IsMulRightInvariant]
    (σ : ℕ → Measure G) [∀ j, IsProbabilityMeasure (σ j)]
    (Q : Set G) (hQfin : μ Q ≠ ∞) (hQpos : 0 < (μ Q).toReal)
    (K R : ℕ → Set G) (hK : ∀ j, ∀ᵐ s ∂σ j, s ∈ K j)
    (hRfin : ∀ j, μ (R j) ≠ ∞) (hRpos : ∀ j, 0 < (μ (R j)).toReal)
    (hQR : ∀ j, ∀ a ∈ Q, ∀ s ∈ K j, a * s ∈ R j)
    (D : ℕ → ℝ) (hD : ∀ j, 0 < D j)
    (hvol : ∀ j, (μ (R j)).toReal ≤ D j * (μ Q).toReal)
    (h : ℕ) (A : Set G) (hA : MeasurableSet A) (hAQ : A ⊆ Q)
    (hApos : 0 < (μ A).toReal) :
    ∃ S : ℕ → Set G, S h = A ∧
      (∀ j, j ≤ h → MeasurableSet (S j) ∧ S j ⊆ A ∧ 0 < (μ (S j)).toReal) ∧
      ∀ j, j < h → S j ⊆ S (j + 1) ∧
        (μ (S (j + 1))).toReal ^ 2 / (2 * D j * (μ Q).toReal) ≤ (μ (S j)).toReal ∧
        ∀ x ∈ S j, (μ (S (j + 1))).toReal / (2 * D j * (μ Q).toReal) ≤
          (twoSampleReturn (σ j) (S (j + 1)) x).toReal := by
  induction h generalizing A with
  | zero =>
    refine ⟨fun _ => A, rfl, ?_, ?_⟩
    · intro j hj
      exact ⟨hA, Subset.rfl, hApos⟩
    · intro j hj
      omega
  | succ h ih =>
    obtain ⟨B, hBm, hBA, hBpos, hmass, hreturn⟩ :=
      exists_backward_recurrence_step μ (σ h) A Q (K h) (R h) hA hQfin hAQ hApos hQpos
        (hK h) (hRfin h) (hRpos h) (fun a ha => hQR h a (hAQ ha)) (hD h) (hvol h)
    obtain ⟨S, hSh, hprop, hstep⟩ := ih B hBm (hBA.trans hAQ) hBpos
    let S' := fun j => if j ≤ h then S j else A
    have hlow (j : ℕ) (hj : j ≤ h) : S' j = S j := by simp only [S', hj, ite_true, if_true]
    have hlast : S' (h + 1) = A := by simp only [S', show ¬ h + 1 ≤ h by omega, ite_false, if_false]
    refine ⟨S', hlast, ?_, ?_⟩
    · intro j hj
      by_cases hjh : j ≤ h
      · rw [hlow j hjh]
        exact ⟨(hprop j hjh).1, (hprop j hjh).2.1.trans hBA, (hprop j hjh).2.2⟩
      · have heq : j = h + 1 := by omega
        rw [heq, hlast]
        exact ⟨hA, Subset.rfl, hApos⟩
    · intro j hj
      by_cases hjh : j < h
      · rw [hlow j (by omega), hlow (j + 1) (by omega)]
        exact hstep j hjh
      · have heq : j = h := by omega
        rw [heq, hlow h le_rfl, hlast, hSh]
        exact ⟨hBA, hmass, hreturn⟩

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_BackwardRecurrenceProbability
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Positive probability of all prescribed returns -/

noncomputable section

namespace PolycyclicRecognition

open MeasureTheory Set
open scoped ENNReal NNReal

/-- Backward recurrence and independent sampling together. The thresholds
are the actual normalized masses of the subsequent retained sets. -/
theorem exists_backward_recurrence_probability
    {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]
    (μ : Measure G) [SFinite μ] [μ.IsMulRightInvariant]
    (σ : ℕ → Measure G) [∀ j, IsProbabilityMeasure (σ j)]
    (Q : Set G) (hQfin : μ Q ≠ ∞) (hQpos : 0 < (μ Q).toReal)
    (K R : ℕ → Set G) (hK : ∀ j, ∀ᵐ s ∂σ j, s ∈ K j)
    (hRfin : ∀ j, μ (R j) ≠ ∞) (hRpos : ∀ j, 0 < (μ (R j)).toReal)
    (hQR : ∀ j, ∀ a ∈ Q, ∀ s ∈ K j, a * s ∈ R j)
    (D : ℕ → ℝ) (hD : ∀ j, 0 < D j)
    (hvol : ∀ j, (μ (R j)).toReal ≤ D j * (μ Q).toReal)
    (h : ℕ) (A : Set G) (hA : MeasurableSet A) (hAQ : A ⊆ Q)
    (hApos : 0 < (μ A).toReal) :
    ∃ S : ℕ → Set G, S h = A ∧
      (∀ j, j ≤ h → MeasurableSet (S j) ∧ S j ⊆ A ∧ 0 < (μ (S j)).toReal) ∧
      (∀ j, j < h → S j ⊆ S (j + 1) ∧
        (μ (S (j + 1))).toReal ^ 2 / (2 * D j * (μ Q).toReal) ≤ (μ (S j)).toReal) ∧
      let τ := fun j => Real.toNNReal ((μ (S (j + 1))).toReal / (2 * D j * (μ Q).toReal))
      0 < switchThresholdProduct τ 0 h ∧
        ∀ x ∈ S 0, switchThresholdProduct τ 0 h ≤ survivingSwitchProbability σ S 0 h x := by
  obtain ⟨S, hlast, hsets, hstep⟩ := exists_backward_recurrence_sets μ σ Q hQfin hQpos
    K R hK hRfin hRpos hQR D hD hvol h A hA hAQ hApos
  refine ⟨S, hlast, hsets, fun j hj => ⟨(hstep j hj).1, (hstep j hj).2.1⟩, ?_⟩
  let τ := fun j => Real.toNNReal ((μ (S (j + 1))).toReal / (2 * D j * (μ Q).toReal))
  have hpos (j : ℕ) (hj : j < h) :
      0 < (μ (S (j + 1))).toReal / (2 * D j * (μ Q).toReal) :=
    div_pos (hsets (j + 1) (by omega)).2.2
      (mul_pos (mul_pos (by norm_num) (hD j)) hQpos)
  have hτ (j : ℕ) (hj : j < h) : 0 < τ j := by
    exact Real.toNNReal_pos.mpr (hpos j hj)
  refine ⟨switchThresholdProduct_pos τ 0 h (fun j _ hj => hτ j (by omega)), ?_⟩
  intro x hx
  apply switchThresholdProduct_le_survival σ S τ 0 h _ hx
  intro j hj y hy
  have hjh : j < h := by omega
  have hr := (hstep j hjh).2.2 y hy
  have hfin : twoSampleReturn (σ j) (S (j + 1)) y ≠ ∞ :=
    (twoSampleReturn_le_one (σ j) (S (j + 1)) y).trans_lt (by simp) |>.ne
  have hr' := ENNReal.ofReal_le_ofReal hr
  rw [ENNReal.ofReal_toReal hfin] at hr'
  exact hr'

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_BackwardRecurrenceFamily
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Backward recurrence for a varying family of Haar boxes -/

noncomputable section

namespace PolycyclicRecognition

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology

/-- The elementary change from Haar mass to relative Haar mass in the
quadratic recurrence. -/
theorem normalized_backward_mass_bound {a b q D : ℝ} (hq : 0 < q) (hD : 0 < D)
    (h : b ^ 2 / (2 * D * q) ≤ a) :
    (b / q) ^ 2 / (2 * D) ≤ a / q := by
  have heq : (b / q) ^ 2 / (2 * D) = (b ^ 2 / (2 * D * q)) / q := by
    field_simp
  rw [heq]
  exact div_le_div_of_nonneg_right h hq.le

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_ParameterSplit
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Splitting the independent parameter cube preserves volume -/

namespace PolycyclicRecognition

open MeasureTheory

theorem measurePreserving_finAppend (n k : ℕ) :
    MeasurePreserving (fun p : (Fin n → ℝ) × (Fin k → ℝ) => Fin.append p.1 p.2)
      volume volume := by
  have h₁ := volume_measurePreserving_sumPiEquivProdPi_symm
    (fun _ : Fin n ⊕ Fin k => ℝ)
  have h₂ := volume_measurePreserving_piCongrLeft
    (fun _ : Fin (n + k) => ℝ) finSumFinEquiv
  convert h₂.comp h₁ using 1
  all_goals try with_reducible_and_instances rfl
  ext p i
  obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective i
  simp only [Function.comp_apply]
  rw [MeasurableEquiv.piCongrLeft_apply_apply]
  cases j with
  | inl j =>
      change Fin.append p.1 p.2 (Fin.castAdd k j) = p.1 j
      simp
  | inr j =>
      change Fin.append p.1 p.2 (Fin.natAdd n j) = p.2 j
      simp

end PolycyclicRecognition

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_PolynomialMinorDifferential
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A polynomial minor is the determinant of the actual slice derivative -/

noncomputable section

namespace PolycyclicRecognition

open MvPolynomial Matrix
open scoped BigOperators

theorem appendParameterLinear_apply (n k : ℕ) (v : Fin n → ℝ) :
    appendParameterLinear n k v = Fin.append v 0 := by
  ext i
  refine Fin.addCases ?_ ?_ i <;> intro j <;> simp [appendParameterLinear]

theorem hasFDerivAt_finAppend {n k : ℕ} (v : Fin n → ℝ) (z : Fin k → ℝ) :
    HasFDerivAt (fun w => Fin.append w z) (appendParameterLinear n k) v := by
  convert (appendParameterLinear n k).hasFDerivAt.add_const (Fin.append 0 z) using 1
  all_goals try with_reducible_and_instances rfl
  ext w i
  refine Fin.addCases ?_ ?_ i <;> intro j <;>
    simp [appendParameterLinear_apply]

theorem hasFDerivAt_polynomialSlice {n k : ℕ}
    (p : Fin n → MvPolynomial (Fin (n + k)) ℝ) (v : Fin n → ℝ) (z : Fin k → ℝ) :
    HasFDerivAt (fun w i => MvPolynomial.eval (Fin.append w z) (p i))
      (polynomialSliceDifferential p v z) v := by
  exact (hasFDerivAt_pi.mpr (fun i => hasFDerivAt_mvPolynomial_eval (p i) (Fin.append v z))).comp v
    (hasFDerivAt_finAppend v z)

theorem eval_polynomialJacobianMinor {n k : ℕ}
    (p : Fin n → MvPolynomial (Fin (n + k)) ℝ) (v : Fin n → ℝ) (z : Fin k → ℝ) :
    MvPolynomial.eval (Fin.append v z) (polynomialJacobianMinor p) =
      (polynomialSliceDifferential p v z).det := by
  classical
  rw [polynomialJacobianMinor, RingHom.map_det]
  change _ = (polynomialSliceDifferential p v z).toLinearMap.det
  rw [← LinearMap.det_toMatrix']
  congr 1
  ext i j
  rw [LinearMap.toMatrix'_apply]
  change MvPolynomial.eval (Fin.append v z) (pderiv (Fin.castAdd k j) (p i)) =
    polynomialDifferential (p i) (Fin.append v z) (appendParameterLinear n k (Pi.single j 1))
  have he : appendParameterLinear n k (Pi.single j 1) = Pi.single (Fin.castAdd k j) 1 := by
    rw [appendParameterLinear_apply]
    ext a
    refine Fin.addCases ?_ ?_ a <;> intro b <;> simp [Pi.single_apply]
    intro h
    have hh := congrArg Fin.val h
    simp only [Fin.val_natAdd, Fin.val_castAdd] at hh
    omega
  rw [he, polynomialDifferential_basis]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_CoordinateMinorPermutation
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Reordering an actual nonzero minor into the sliced coordinates -/

noncomputable section

namespace PolycyclicRecognition

open Set MeasureTheory

theorem exists_fin_equiv_extending_injection {n m : ℕ}
    (j : Fin n → Fin m) (hj : Function.Injective j) :
    ∃ k : ℕ, ∃ e : Fin (n + k) ≃ Fin m, ∀ i, e (Fin.castAdd k i) = j i := by
  classical
  let s : Set (Fin m) := range j
  let k := Fintype.card ↥(sᶜ)
  let ec : ↥(sᶜ) ≃ Fin k := Fintype.equivFin _
  let e : Fin (n + k) ≃ Fin m := finSumFinEquiv.symm.trans
    (((Equiv.ofInjective j hj).sumCongr ec.symm).trans (Equiv.Set.sumCompl (range j)))
  refine ⟨k, e, fun i => ?_⟩
  simp [e]

theorem reindexParameters_norm {l m : ℕ} (e : Fin l ≃ Fin m) (x : Fin l → ℝ) :
    ‖reindexParameters e x‖ = ‖x‖ := by
  have h := (IsometryEquiv.piCongrLeft' (Y := fun _ : Fin l => ℝ) e).isometry.dist_eq x 0
  change dist (reindexParameters e x) (reindexParameters e 0) = dist x 0 at h
  simpa only [map_zero, dist_zero_right] using h

theorem measurePreserving_reindexParameters {l m : ℕ} (e : Fin l ≃ Fin m) :
    MeasurePreserving (reindexParameters e) volume volume := by
  convert volume_measurePreserving_piCongrLeft (fun _ : Fin m => ℝ) e using 1
  all_goals try with_reducible_and_instances rfl
  ext x i
  obtain ⟨j, rfl⟩ := e.surjective i
  rw [MeasurableEquiv.piCongrLeft_apply_apply, reindexParameters_apply_equiv]

theorem HasPolynomialFormula.reindex {P : Type} {l m : ℕ}
    {f : P → (Fin m → ℝ) → ℝ} (hf : HasPolynomialFormula f) (e : Fin l ≃ Fin m) :
    HasPolynomialFormula (fun a x => f a (reindexParameters e x)) := by
  obtain ⟨D, hD⟩ := hf
  refine ⟨D, fun a => ?_⟩
  obtain ⟨p, hp, he⟩ := hD a
  refine ⟨MvPolynomial.rename e.symm p, (MvPolynomial.totalDegree_rename_le _ _).trans hp, ?_⟩
  intro x
  rw [MvPolynomial.eval_rename]
  exact he _

theorem reindexParameters_single {l m : ℕ} (e : Fin l ≃ Fin m) (j : Fin l) :
    reindexParameters e (Pi.single j 1) = Pi.single (e j) 1 := by
  classical
  ext i
  obtain ⟨i, rfl⟩ := e.surjective i
  simp [Pi.single_apply, e.injective.eq_iff]

/-- The selected column determinant is the derivative determinant after reordering. -/
theorem det_reindexed_slice {n k m : ℕ} (e : Fin (n + k) ≃ Fin m)
    (f : (Fin m → ℝ) → (Fin n → ℝ)) (v : Fin n → ℝ) (z : Fin k → ℝ)
    (hf : DifferentiableAt ℝ f (reindexParameters e (Fin.append v z))) :
    (fderiv ℝ (fun w => f (reindexParameters e (Fin.append w z))) v).det =
      (Matrix.of fun i j => fderiv ℝ f (reindexParameters e (Fin.append v z))
        (Pi.single (e (Fin.castAdd k j)) 1) i).det := by
  have hd := hf.hasFDerivAt.comp v
    ((reindexParameters e).hasFDerivAt.comp v (hasFDerivAt_finAppend v z))
  change HasFDerivAt (fun w => f (reindexParameters e (Fin.append w z))) _ v at hd
  rw [hd.fderiv]
  change (ContinuousLinearMap.comp _ _).toLinearMap.det = _
  rw [← LinearMap.det_toMatrix']
  congr 1
  ext i j
  rw [LinearMap.toMatrix'_apply]
  change fderiv ℝ f _ (reindexParameters e (appendParameterLinear n k (Pi.single j 1))) i = _
  have ha : appendParameterLinear n k (Pi.single j 1) = Pi.single (Fin.castAdd k j) 1 := by
    ext a
    refine Fin.addCases ?_ ?_ a <;> intro b <;> simp [appendParameterLinear, Pi.single_apply]
    intro h
    have hh := congrArg Fin.val h
    simp only [Fin.val_natAdd, Fin.val_castAdd] at hh
    omega
  rw [ha, reindexParameters_single]
  rfl

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_PolynomialLargeValueSet
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_countable _root_.OAI.PolycyclicRecognition.finitelyGeneratedSubgroupIndex_countable _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Keeping compact parameter mass away from a polynomial zero set -/

noncomputable section

namespace PolycyclicRecognition

open Set Metric MeasureTheory
open scoped ENNReal

theorem exists_compact_large_polynomial_values
    (rem : RemezPolynomialInput) (n D : ℕ) (hn : 1 ≤ n) (hD : 1 ≤ D) :
    ∃ A : ℝ, 0 < A ∧
      ∀ (p : MvPolynomial (Fin n) ℝ), p.totalDegree ≤ D →
      ∀ (R c : ℝ), 1 ≤ R → 0 < c →
      ∀ x₀ ∈ closedBall 0 R, c ≤ |MvPolynomial.eval x₀ p| →
      ∀ E : Set (Fin n → ℝ), MeasurableSet E → E ⊆ closedBall 0 R →
      0 < (volume E).toReal →
      let η := (c / 2) / (2 * A * (1 + R) ^ n / (volume E).toReal) ^ (n * D)
      ∃ K : Set (Fin n → ℝ), K ⊆ E ∧ IsCompact K ∧
        (volume E).toReal / 4 < (volume K).toReal ∧
        ∀ x ∈ K, η ≤ |MvPolynomial.eval x p| := by
  obtain ⟨A, hA, hrem⟩ := rem n D hn hD
  refine ⟨A, hA, ?_⟩
  intro p hp R c hR hc x₀ hx₀ hx₀c E hE hER hm
  let m := (volume E).toReal
  let a := 2 * A * (1 + R) ^ n / m
  let η := (c / 2) / a ^ (n * D)
  have ha : 0 < a := by dsimp [a, m] <;> positivity
  have hη : 0 < η := by dsimp [η] <;> positivity
  have hEfinite : volume E ≠ ∞ :=
    measure_ne_top_of_subset hER (isCompact_closedBall (0 : Fin n → ℝ) R).measure_ne_top
  let B := E ∩ {x | |MvPolynomial.eval x p| < η}
  let G := E ∩ {x | η ≤ |MvPolynomial.eval x p|}
  have hB : MeasurableSet B := hE.inter
    (isOpen_lt p.continuous_eval.abs continuous_const).measurableSet
  have hG : MeasurableSet G := hE.inter
    (isClosed_le continuous_const p.continuous_eval.abs).measurableSet
  have hBfinite : volume B ≠ ∞ := measure_ne_top_of_subset inter_subset_left hEfinite
  have hGfinite : volume G ≠ ∞ := measure_ne_top_of_subset inter_subset_left hEfinite
  have hBmass : (volume B).toReal ≤ m / 2 := by
    by_contra h
    have hlarge : m / 2 < (volume B).toReal := lt_of_not_ge h
    have hBpos : 0 < (volume B).toReal := (by dsimp [m]; positivity : 0 < m / 2).trans hlarge
    have hpoint := hrem p hp R hR B hB (inter_subset_left.trans hER) hBpos
      η hη.le (fun x hx => hx.2.le) x₀ hx₀
    have hquot : A * (1 + R) ^ n / (volume B).toReal ≤ a := by
      dsimp [a]
      apply (div_le_div_iff₀ hBpos hm).mpr
      have hnonneg : 0 ≤ A * (1 + R) ^ n := by positivity
      nlinarith
    have hpow : (A * (1 + R) ^ n / (volume B).toReal) ^ (n * D) ≤ a ^ (n * D) :=
      pow_le_pow_left₀ (by positivity) hquot (n * D)
    have he : a ^ (n * D) * η = c / 2 := by
      dsimp [η]
      field_simp
    have hlast : c ≤ c / 2 := calc
      c ≤ |MvPolynomial.eval x₀ p| := hx₀c
      _ ≤ (A * (1 + R) ^ n / (volume B).toReal) ^ (n * D) * η := hpoint
      _ ≤ a ^ (n * D) * η := mul_le_mul_of_nonneg_right hpow hη.le
      _ = c / 2 := he
    linarith
  have hEG : E = B ∪ G := by
    ext x
    simp only [B, G, mem_union, mem_inter_iff, mem_ofPred_eq]
    constructor
    · intro hx
      rcases lt_or_ge |MvPolynomial.eval x p| η with h | h
      · exact Or.inl ⟨hx, h⟩
      · exact Or.inr ⟨hx, h⟩
    · rintro (⟨hx, _⟩ | ⟨hx, _⟩) <;> exact hx
  have hGmass : m / 2 ≤ (volume G).toReal := by
    have hu := measureReal_union_le (μ := volume) B G
    rw [← hEG] at hu
    change m ≤ (volume B).toReal + (volume G).toReal at hu
    linarith
  have hstrict : ENNReal.ofReal (m / 4) < volume G := by
    apply (ENNReal.toReal_lt_toReal (by simp) hGfinite).mp
    rw [ENNReal.toReal_ofReal (by positivity)]
    linarith
  obtain ⟨K, hKG, hK, hKmass⟩ := hG.exists_lt_isCompact hstrict
  refine ⟨K, hKG.trans inter_subset_left, hK, ?_, fun x hx => (hKG hx).2⟩
  have hh := (ENNReal.toReal_lt_toReal (by simp) hK.measure_ne_top).mpr hKmass
  simpa only [ENNReal.toReal_ofReal (by positivity : 0 ≤ m / 4)] using hh

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_SectionVolume
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Retaining parameter volume on one coordinate slice -/

namespace PolycyclicRecognition

open MeasureTheory Set
open scoped ENNReal

/-- Fubini gives a large section without choosing a measurable family of
representatives for the image of the parameter set. -/
theorem exists_section_measure_gt
    {V Z : Type} [MeasurableSpace V] [MeasurableSpace Z]
    (μ : Measure V) (ν : Measure Z) [SFinite μ] [SFinite ν]
    {K : Set (V × Z)} (hK : MeasurableSet K)
    {Q : Set Z} (hQ : MeasurableSet Q)
    (hKQ : ∀ p ∈ K, p.2 ∈ Q) (t : ℝ≥0∞)
    (hmass : t * ν Q < (μ.prod ν) K) :
    ∃ z ∈ Q, t < μ {v | (v, z) ∈ K} := by
  by_contra h
  have hbound (z : Z) : μ {v | (v, z) ∈ K} ≤ Q.indicator (fun _ => t) z := by
    by_cases hz : z ∈ Q
    · rw [indicator_of_mem hz]
      exact le_of_not_gt (fun ht => h ⟨z, hz, ht⟩)
    · have hempty : {v | (v, z) ∈ K} = ∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        intro v hv
        exact hz (hKQ (v, z) hv)
      rw [hempty, measure_empty, indicator_of_notMem hz]
  have he : (μ.prod ν) K ≤ t * ν Q := by
    rw [Measure.prod_apply_symm hK]
    calc
      _ ≤ ∫⁻ z, Q.indicator (fun _ => t) z ∂ν := lintegral_mono hbound
      _ = t * ν Q := by rw [lintegral_indicator hQ]; simp
  exact not_lt_of_ge he hmass

end PolycyclicRecognition

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_CompactSectionVolume
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_countable _root_.OAI.PolycyclicRecognition.finitelyGeneratedSubgroupIndex_countable _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Compact coordinate sections with quantitative retained volume -/

noncomputable section

namespace PolycyclicRecognition

open Set MeasureTheory
open scoped ENNReal

theorem isCompact_coordinate_section
    {V Z : Type} [TopologicalSpace V] [TopologicalSpace Z] [T1Space Z]
    {K : Set (V × Z)} (hK : IsCompact K) (z : Z) :
    IsCompact {v | (v, z) ∈ K} := by
  have he : {v | (v, z) ∈ K} =
      Prod.fst '' (K ∩ Prod.snd ⁻¹' {z}) := by
    ext v
    constructor
    · intro hv
      exact ⟨(v, z), ⟨hv, rfl⟩, rfl⟩
    · rintro ⟨⟨w, y⟩, ⟨hw, hy⟩, rfl⟩
      simp only [mem_preimage, mem_singleton_iff] at hy
      change (w, z) ∈ K
      simpa only [hy] using hw
  rw [he]
  exact (hK.inter_right (isClosed_singleton.preimage continuous_snd)).image continuous_fst

theorem exists_compact_section_volume_gt
    (n k : ℕ) {K : Set ((Fin n → ℝ) × (Fin k → ℝ))}
    (hK : IsCompact K) {Q : Set (Fin k → ℝ)} (hQ : IsCompact Q)
    (hKQ : ∀ p ∈ K, p.2 ∈ Q)
    {t q : ℝ} (ht : 0 ≤ t) (hq : (volume Q).toReal ≤ q)
    (hmass : t * q < (volume K).toReal) :
    ∃ z ∈ Q, IsCompact {v | (v, z) ∈ K} ∧
      t < (volume {v | (v, z) ∈ K}).toReal := by
  have hlt : ENNReal.ofReal t * volume Q < volume K := by
    apply (ENNReal.toReal_lt_toReal
      (ENNReal.mul_ne_top (by simp) hQ.measure_ne_top) hK.measure_ne_top).mp
    simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal ht]
    exact (mul_le_mul_of_nonneg_left hq ht).trans_lt hmass
  obtain ⟨z, hz, hvolume⟩ := exists_section_measure_gt volume volume hK.measurableSet
    hQ.measurableSet hKQ (ENNReal.ofReal t) hlt
  have hsection := isCompact_coordinate_section hK z
  refine ⟨z, hz, hsection, ?_⟩
  have hh := (ENNReal.toReal_lt_toReal (by simp) hsection.measure_ne_top).mpr hvolume
  simpa only [ENNReal.toReal_ofReal ht] using hh

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_InjectivePatchVolume
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Volume lower bounds from a controlled finite injective cover

This is the change-of-variables step for measurable polynomial parameters.
The parameter set itself need not contain an open set. When it is compact,
the image used below is a compact witness for inner volume.
-/

noncomputable section

namespace PolycyclicRecognition

open MeasureTheory Set
open scoped ENNReal NNReal BigOperators

theorem volume_image_lower_of_finite_injective_cover
    {V I : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V]
    (μ : Measure V) [μ.IsAddHaarMeasure]
    (f : V → V) (df : V → V →L[ℝ] V)
    {K : Set V} (hK : MeasurableSet K) (s : Finset I) (U : I → Set V)
    (hU : ∀ i ∈ s, MeasurableSet (U i))
    (hcover : K ⊆ ⋃ i ∈ s, U i)
    (hdf : ∀ x ∈ K, HasFDerivAt f (df x) x)
    (hinj : ∀ i ∈ s, Set.InjOn f (K ∩ U i))
    (η : ℝ≥0) (hdet : ∀ x ∈ K, (η : ℝ) ≤ |(df x).det|) :
    (η : ℝ≥0∞) * μ K ≤ (s.card : ℝ≥0∞) * μ (f '' K) := by
  classical
  have hcover' : K ⊆ ⋃ i ∈ s, K ∩ U i := by
    intro x hx
    obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp (hcover hx)
    exact mem_iUnion₂.mpr ⟨i, hi, hx, hxi⟩
  have hmass : μ K ≤ ∑ i ∈ s, μ (K ∩ U i) :=
    (measure_mono hcover').trans (measure_biUnion_finset_le s (fun i => K ∩ U i))
  calc
    (η : ℝ≥0∞) * μ K ≤ η * ∑ i ∈ s, μ (K ∩ U i) := mul_le_mul' le_rfl hmass
    _ = ∑ i ∈ s, (η : ℝ≥0∞) * μ (K ∩ U i) := by rw [Finset.mul_sum]
    _ ≤ ∑ _i ∈ s, μ (f '' K) := by
      apply Finset.sum_le_sum
      intro i hi
      calc
        (η : ℝ≥0∞) * μ (K ∩ U i) = ∫⁻ _x in K ∩ U i, (η : ℝ≥0∞) ∂μ := by simp
        _ ≤ ∫⁻ x in K ∩ U i, ENNReal.ofReal |(df x).det| ∂μ := by
          apply setLIntegral_mono' (hK.inter (hU i hi))
          intro x hx
          rw [← ENNReal.ofReal_coe_nnreal]
          exact ENNReal.ofReal_le_ofReal (hdet x hx.1)
        _ = μ (f '' (K ∩ U i)) :=
          lintegral_abs_det_fderiv_eq_addHaar_image μ (hK.inter (hU i hi))
            (fun x hx => (hdf x hx.1).hasFDerivWithinAt) (hinj i hi)
        _ ≤ μ (f '' K) := measure_mono (image_mono inter_subset_left)
    _ = (s.card : ℝ≥0∞) * μ (f '' K) := by simp

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_CoordinateMesh
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A polynomial-size coordinate mesh for a bounded parameter cube -/

noncomputable section

namespace PolycyclicRecognition

theorem exists_coordinate_mesh (n : ℕ) {R ρ : ℝ} (hR : 0 ≤ R) (hρ : 0 < ρ) :
    ∃ k : ℕ, (k : ℝ) ≤ 2 * R / ρ + 2 ∧
      ∃ c : (Fin n → Fin k) → (Fin n → ℝ),
        (∀ i, ‖c i‖ ≤ R + ρ) ∧
        ∀ x : Fin n → ℝ, ‖x‖ ≤ R → ∃ i, dist x (c i) ≤ ρ := by
  let k := ⌈2 * R / ρ⌉₊ + 1
  have hratio : 0 ≤ 2 * R / ρ := div_nonneg (by positivity) hρ.le
  have hk : (k : ℝ) ≤ 2 * R / ρ + 2 := by
    dsimp only [k]
    have h := Nat.ceil_lt_add_one hratio
    push_cast
    linarith
  let c := fun i : Fin n → Fin k => fun j => -R + ρ * (i j : ℕ)
  refine ⟨k, hk, c, ?_, ?_⟩
  · intro i
    apply (pi_norm_le_iff_of_nonneg (by positivity : 0 ≤ R + ρ)).mpr
    intro j
    rw [Real.norm_eq_abs, abs_le]
    have hji : (i j : ℕ) ≤ ⌈2 * R / ρ⌉₊ := Nat.le_of_lt_succ (i j).isLt
    have hj : ((i j : ℕ) : ℝ) ≤ (⌈2 * R / ρ⌉₊ : ℝ) := by exact_mod_cast hji
    have hc := Nat.ceil_lt_add_one hratio
    have hp : ρ * ((i j : ℕ) : ℝ) ≤ 2 * R + ρ := by
      have ht := mul_le_mul_of_nonneg_left (hj.trans hc.le) hρ.le
      have he : ρ * (2 * R / ρ + 1) = 2 * R + ρ := by field_simp
      rwa [he] at ht
    dsimp only [c]
    constructor
    · nlinarith [show (0 : ℝ) ≤ ((i j : ℕ) : ℝ) from Nat.cast_nonneg _]
    · linarith
  · intro x hx
    have hxj := (pi_norm_le_iff_of_nonneg hR).mp hx
    let i : Fin n → Fin k := fun j => ⟨⌊(x j + R) / ρ⌋₊, by
      have hj : (x j + R) / ρ ≤ 2 * R / ρ := by
        apply div_le_div_of_nonneg_right _ hρ.le
        have := (abs_le.mp (by simpa only [Real.norm_eq_abs] using hxj j)).2
        linarith
      exact Nat.lt_succ_of_le ((Nat.floor_mono hj).trans (Nat.floor_le_ceil _))⟩
    refine ⟨i, ?_⟩
    rw [dist_eq_norm]
    apply (pi_norm_le_iff_of_nonneg hρ.le).mpr
    intro j
    have hlow : -R ≤ x j := (abs_le.mp (by simpa only [Real.norm_eq_abs] using hxj j)).1
    have hnonneg : 0 ≤ (x j + R) / ρ := div_nonneg (by linarith) hρ.le
    have hlo := (le_div_iff₀ hρ).mp (Nat.floor_le hnonneg)
    have hhi := (div_lt_iff₀ hρ).mp (Nat.lt_floor_add_one ((x j + R) / ρ))
    change ‖x j - (-R + ρ * (⌊(x j + R) / ρ⌋₊ : ℝ))‖ ≤ ρ
    rw [Real.norm_eq_abs, abs_le]
    constructor <;> nlinarith

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_DeterminantLowerNorm
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Quantitative invertibility from a determinant lower bound

Compactness bounds the adjugate on the unit ball. Homogeneity then gives
the polynomial loss needed to choose injective patches for polynomial maps.
-/

noncomputable section

namespace PolycyclicRecognition

open Set Metric Matrix
open scoped Matrix.Norms.Operator

theorem exists_adjugate_norm_bound (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (A : Matrix (Fin n) (Fin n) ℝ) (L : ℝ),
      0 < L → ‖A‖ ≤ L → ‖A.adjugate‖ ≤ C * L ^ (n - 1) := by
  have hc : Continuous (fun A : Matrix (Fin n) (Fin n) ℝ => A.adjugate) :=
    continuous_id.matrix_adjugate
  obtain ⟨C, hC, hbound⟩ := (isCompact_closedBall (0 : Matrix (Fin n) (Fin n) ℝ) 1).image hc
    |>.isBounded.exists_pos_norm_le
  refine ⟨C, hC, fun A L hL hA => ?_⟩
  have hunit : L⁻¹ • A ∈ closedBall (0 : Matrix (Fin n) (Fin n) ℝ) 1 := by
    rw [mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hL)]
    exact (inv_mul_le_iff₀ hL).mpr (by simpa using hA)
  have h := hbound _ ⟨L⁻¹ • A, hunit, rfl⟩
  dsimp only at h
  rw [Matrix.adjugate_smul, Fintype.card_fin, norm_smul, Real.norm_eq_abs,
    abs_of_pos (pow_pos (inv_pos.mpr hL) _), inv_pow] at h
  have he := (inv_mul_le_iff₀ (pow_pos hL (n - 1))).mp h
  simpa only [mul_comm] using he

/-- The adjugate identity bounds below the action of the original matrix. -/
theorem determinant_mul_norm_le_adjugate_mul_norm {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ) :
    |A.det| * ‖v‖ ≤ ‖A.adjugate‖ * ‖A *ᵥ v‖ := by
  have he : A.adjugate *ᵥ (A *ᵥ v) = A.det • v := by
    rw [Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec]
  have hb := Matrix.linfty_opNorm_mulVec A.adjugate (A *ᵥ v)
  rw [he, norm_smul, Real.norm_eq_abs] at hb
  exact hb

/-- Uniform lower norm control for all matrices with bounded norm and a
prescribed positive determinant lower bound. -/
theorem exists_determinant_lower_norm_bound (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (A : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) (L η : ℝ),
      0 < L → ‖A‖ ≤ L → η ≤ |A.det| → ∀ v,
      η * ‖v‖ ≤ (C * L ^ (n - 1)) * ‖A v‖ := by
  obtain ⟨C, hC, hbound⟩ := exists_adjugate_norm_bound n
  refine ⟨C, hC, fun A L η hL hA hη v => ?_⟩
  let M := LinearMap.toMatrix' A.toLinearMap
  have hM : ‖M‖ ≤ L := by simpa only [M, Matrix.linfty_opNorm_toMatrix] using hA
  have hb := determinant_mul_norm_le_adjugate_mul_norm M v
  dsimp only [M] at hb
  rw [LinearMap.det_toMatrix', LinearMap.toMatrix'_mulVec] at hb
  exact (mul_le_mul_of_nonneg_right hη (norm_nonneg v)).trans
    (hb.trans (mul_le_mul_of_nonneg_right (hbound M L hL hM) (norm_nonneg (A v))))

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_DerivativeOscillation
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Injectivity on convex patches with controlled derivative oscillation -/

namespace PolycyclicRecognition

open Set

theorem injOn_of_derivative_oscillation
    {V W : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (f : V → W) (df : V → V →L[ℝ] W) (A : V →L[ℝ] W)
    {S : Set V} (hS : Convex ℝ S)
    (hf : ∀ x ∈ S, HasFDerivAt f (df x) x)
    {η D ε : ℝ} (hD : 0 ≤ D) (hgap : D * ε < η)
    (hA : ∀ v, η * ‖v‖ ≤ D * ‖A v‖)
    (hosc : ∀ x ∈ S, ‖df x - A‖ ≤ ε) : Set.InjOn f S := by
  intro x hx y hy hxy
  have he := hS.norm_image_sub_le_of_norm_hasFDerivWithin_le
    (f := fun z => f z - A z) (f' := fun z => df z - A)
    (fun z hz => ((hf z hz).sub A.hasFDerivAt).hasFDerivWithinAt)
    hosc hx hy
  have hn : ‖A (y - x)‖ ≤ ε * ‖y - x‖ := by
    rw [map_sub, norm_sub_rev]
    simpa only [hxy, sub_sub_sub_cancel_left] using he
  have hb := (hA (y - x)).trans (mul_le_mul_of_nonneg_left hn hD)
  have hz : ‖y - x‖ = 0 := by nlinarith [norm_nonneg (y - x)]
  exact (sub_eq_zero.mp (norm_eq_zero.mp hz)).symm

end PolycyclicRecognition

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_QuantitativeInjectiveCover
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Quantitative injective patches near nondegenerate derivatives -/

noncomputable section

namespace PolycyclicRecognition

open Set Metric

theorem exists_quantitative_injective_cover (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (f : (Fin n → ℝ) → (Fin n → ℝ))
        (df : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] (Fin n → ℝ))
        (R L η : ℝ), 0 ≤ R → 1 ≤ L → 0 < η →
      (∀ z, ‖z‖ ≤ R + 2 → HasFDerivAt f (df z) z) →
      (∀ z, ‖z‖ ≤ R + 2 → ‖df z‖ ≤ L) →
      (∀ z w, ‖z‖ ≤ R + 2 → ‖w‖ ≤ R + 2 →
        ‖df z - df w‖ ≤ L * dist z w) →
      ∃ (ρ : ℝ) (k : ℕ) (c : (Fin n → Fin k) → (Fin n → ℝ)),
        ρ = min 1 (η / (8 * (C * L ^ (n - 1)) * L)) ∧ 0 < ρ ∧
        (k : ℝ) ≤ 2 * R / ρ + 2 ∧
        (∀ z, ‖z‖ ≤ R → ∃ i, z ∈ closedBall (c i) ρ) ∧
        ∀ i, Set.InjOn f
          ({z | ‖z‖ ≤ R ∧ η ≤ |(df z).det|} ∩ closedBall (c i) ρ) := by
  obtain ⟨C, hC, hbound⟩ := exists_determinant_lower_norm_bound n
  refine ⟨C, hC, ?_⟩
  intro f df R L η hR hL hη hf hdf hosc
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL
  let D := C * L ^ (n - 1)
  have hD : 0 < D := mul_pos hC (pow_pos hLpos _)
  let ρ := min 1 (η / (8 * D * L))
  have hρ : 0 < ρ := lt_min zero_lt_one (div_pos hη (by positivity))
  have hρone : ρ ≤ 1 := min_le_left _ _
  have hgap : D * (2 * L * ρ) < η := by
    have hρle : ρ ≤ η / (8 * D * L) := min_le_right _ _
    have hh := (le_div_iff₀ (show 0 < 8 * D * L by positivity)).mp hρle
    nlinarith
  obtain ⟨k, hk, c, hc, hcover⟩ := exists_coordinate_mesh n hR hρ
  refine ⟨ρ, k, c, rfl, hρ, hk, ?_, ?_⟩
  · intro z hz
    obtain ⟨i, hi⟩ := hcover z hz
    exact ⟨i, hi⟩
  · intro i
    by_cases hempty : ({z | ‖z‖ ≤ R ∧ η ≤ |(df z).det|} ∩ closedBall (c i) ρ).Nonempty
    · obtain ⟨z₀, hz₀, hz₀ball⟩ := hempty
      have hbig (z : Fin n → ℝ) (hz : z ∈ closedBall (c i) ρ) : ‖z‖ ≤ R + 2 := by
        have he : ‖z‖ ≤ ‖z - c i‖ + ‖c i‖ := by
          simpa only [dist_eq_norm, sub_zero] using dist_triangle z (c i) 0
        have hd : ‖z - c i‖ ≤ ρ := hz
        have hh := hc i
        linarith
      have hi : Set.InjOn f (closedBall (c i) ρ) := by
        apply injOn_of_derivative_oscillation f df (df z₀) (convex_closedBall _ _)
          (fun z hz => hf z (hbig z hz)) hD.le hgap
        · exact hbound (df z₀) L η hLpos (hdf z₀ (hbig z₀ hz₀ball)) hz₀.2
        · intro z hz
          have hd : dist z z₀ ≤ 2 * ρ := by
            calc
              dist z z₀ ≤ dist z (c i) + dist (c i) z₀ := dist_triangle _ _ _
              _ ≤ ρ + ρ := add_le_add hz
                (by simpa only [dist_comm] using (mem_closedBall.mp hz₀ball))
              _ = 2 * ρ := by ring
          exact (hosc z z₀ (hbig z hz) (hbig z₀ hz₀ball)).trans
            (by nlinarith [mul_le_mul_of_nonneg_left hd hLpos.le])
      exact hi.mono inter_subset_right
    · simpa only [not_nonempty_iff_eq_empty.mp hempty] using (Set.injOn_empty f)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_CompactImageVolume
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_countable _root_.OAI.PolycyclicRecognition.finitelyGeneratedSubgroupIndex_countable _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Quantitative compact image volume away from the critical set -/

noncomputable section

namespace PolycyclicRecognition

open Set Metric MeasureTheory
open scoped ENNReal NNReal

theorem exists_compact_image_volume_bound (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (f : (Fin n → ℝ) → (Fin n → ℝ))
        (df : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] (Fin n → ℝ))
        (R L η : ℝ), 0 ≤ R → 1 ≤ L → 0 < η →
      (∀ z, ‖z‖ ≤ R + 2 → HasFDerivAt f (df z) z) →
      (∀ z, ‖z‖ ≤ R + 2 → ‖df z‖ ≤ L) →
      (∀ z w, ‖z‖ ≤ R + 2 → ‖w‖ ≤ R + 2 →
        ‖df z - df w‖ ≤ L * dist z w) →
      ∀ K : Set (Fin n → ℝ), IsCompact K →
      (∀ z ∈ K, ‖z‖ ≤ R ∧ η ≤ |(df z).det|) →
      let ρ := min 1 (η / (8 * (C * L ^ (n - 1)) * L))
      IsCompact (f '' K) ∧
        η * (volume K).toReal ≤ (2 * R / ρ + 2) ^ n * (volume (f '' K)).toReal := by
  classical
  obtain ⟨C, hC, hcover⟩ := exists_quantitative_injective_cover n
  refine ⟨C, hC, ?_⟩
  intro f df R L η hR hL hη hf hdf hosc K hK hgood
  obtain ⟨ρ, k, c, hρeq, hρ, hk, hcov, hinj⟩ := hcover f df R L η hR hL hη hf hdf hosc
  have hcont : ContinuousOn f K := fun z hz =>
    (hf z (by have := (hgood z hz).1; linarith)).continuousAt.continuousWithinAt
  have himage : IsCompact (f '' K) := hK.image_of_continuousOn hcont
  have hinjK (i : Fin n → Fin k) : Set.InjOn f (K ∩ closedBall (c i) ρ) := by
    intro z hz w hw he
    exact hinj i ⟨hgood z hz.1, hz.2⟩ ⟨hgood w hw.1, hw.2⟩ he
  have hb := volume_image_lower_of_finite_injective_cover volume f df hK.measurableSet
    (Finset.univ : Finset (Fin n → Fin k)) (fun i => closedBall (c i) ρ)
    (fun _ _ => measurableSet_closedBall) (fun z hz => by
      obtain ⟨i, hi⟩ := hcov z (hgood z hz).1
      exact mem_iUnion₂.mpr ⟨i, Finset.mem_univ _, hi⟩)
    (fun z hz => hf z (by have := (hgood z hz).1; linarith))
    (fun i _ => hinjK i)
    (Real.toNNReal η) (fun z hz => by simpa [Real.coe_toNNReal η hη.le] using (hgood z hz).2)
  have ht := ENNReal.toReal_mono
    (ENNReal.mul_ne_top (by simp) himage.measure_ne_top) hb
  have hr : η * (volume K).toReal ≤ (k : ℝ) ^ n * (volume (f '' K)).toReal := by
    simpa only [ENNReal.toReal_mul, ENNReal.coe_toReal, Real.coe_toNNReal η hη.le,
      Finset.card_univ, Fintype.card_fun, Fintype.card_fin, ENNReal.toReal_natCast,
      ENNReal.toReal_pow, Nat.cast_pow] using ht
  have hpow : (k : ℝ) ^ n ≤ (2 * R / ρ + 2) ^ n :=
    pow_le_pow_left₀ (Nat.cast_nonneg k) hk n
  subst ρ
  exact ⟨himage, hr.trans (mul_le_mul_of_nonneg_right hpow ENNReal.toReal_nonneg)⟩

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_SmoothPolynomialFamilyImage
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Measurable images in a compact smooth polynomial family

Smoothness supplies all local differential bounds. The polynomial formulas
supply the actual minor and its fixed degree. Only scalar Remez is external.
-/

noncomputable section

namespace PolycyclicRecognition

open Set Metric MeasureTheory

theorem contDiff_finAppend (n k : ℕ) {q : ℕ∞} :
    ContDiff ℝ q (fun p : (Fin n → ℝ) × (Fin k → ℝ) => Fin.append p.1 p.2) := by
  apply contDiff_pi.mpr
  intro i
  refine Fin.addCases ?_ ?_ i <;> intro j
  · simpa only [Fin.append_left, Function.comp_def] using
      (contDiff_apply ℝ ℝ j).comp (contDiff_fst (E := Fin n → ℝ) (F := Fin k → ℝ))
  · simpa only [Fin.append_right, Function.comp_def] using
      (contDiff_apply ℝ ℝ j).comp (contDiff_snd (E := Fin n → ℝ) (F := Fin k → ℝ))

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_ConvergingPolynomialImage
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A noncritical limit supplies the minor bound for all late parameters -/

noncomputable section

namespace PolycyclicRecognition

open Set Metric MeasureTheory Filter
open scoped Topology

theorem continuous_det_clm {P : Type} [TopologicalSpace P] {n : ℕ}
    {d : P → (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)} (hd : Continuous d) :
    Continuous (fun p => (d p).det) := by
  have hm : Continuous (fun p => LinearMap.toMatrix' (d p).toLinearMap) := by
    apply continuous_matrix
    intro i j
    simp only [LinearMap.toMatrix'_apply]
    exact (continuous_apply i).comp (hd.clm_apply continuous_const)
  simpa only [LinearMap.det_toMatrix'] using hm.matrix_det

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_DifferenceAmplitudeWord
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Two independent interval samples per generator switch -/

noncomputable section

namespace PolycyclicRecognition

open Module

theorem contDiff_differenceAmplitudeWord {I : Type} [Fintype I] {n m c : ℕ}
    (a : DynkinCoefficients c 2) (letters : Fin m → I) {q : ℕ∞} :
    ContDiff ℝ q (fun z :
      (((Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) × (I → Fin n → ℝ)) ×
        (Fin (m + m) → ℝ) => differenceAmplitudeWordEndpoint a letters z.1 z.2) := by
  change ContDiff ℝ q (fun z :
      (((Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) × (I → Fin n → ℝ)) ×
        (Fin (m + m) → ℝ) => polynomialListProduct (dynkinProduct a z.1.1)
          (List.ofFn fun j =>
            (z.2 (Fin.castAdd m j) - z.2 (Fin.natAdd m j)) • z.1.2 (letters j)))
  apply contDiff_polynomialListProduct_ofFn
  · exact contDiff_fst.fst
  · intro j
    exact (((contDiff_apply ℝ ℝ (Fin.castAdd m j)).comp contDiff_snd).sub
      ((contDiff_apply ℝ ℝ (Fin.natAdd m j)).comp contDiff_snd)).smul
      ((contDiff_apply ℝ (Fin n → ℝ) (letters j)).comp contDiff_fst.snd)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_BundleWordCoordinates
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Fixed source bundles in joint independent coordinates -/

noncomputable section
namespace PolycyclicRecognition

open scoped BigOperators

theorem hasPolynomialCoordinates_linear_pi_output {P : Type} {h n m k : ℕ}
    (T : (Fin h → Fin n → ℝ) →L[ℝ] (Fin k → ℝ))
    (f : P → (Fin m → ℝ) → Fin h → Fin n → ℝ)
    (hf : ∀ i j, HasPolynomialFormula (fun p x => f p x i j)) :
    HasPolynomialCoordinates (fun p x => T (f p x)) := by
  have he (v : Fin h → Fin n → ℝ) :
      v = ∑ i : Fin h, ∑ j : Fin n, v i j • Pi.single i (Pi.single j 1) := by
    funext i j
    simp [Finset.sum_apply, Pi.single_apply, ite_apply]
  intro k
  have he' : (fun p x => T (f p x) k) = (fun p x =>
      ∑ i : Fin h, ∑ j : Fin n, f p x i j * T (Pi.single i (Pi.single j 1)) k) := by
    funext p x
    conv_lhs => rw [he (f p x)]
    simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [he']
  apply hasPolynomialFormula_sum
  intro i _
  apply hasPolynomialFormula_sum
  intro j _
  exact (hf i j).mul (hasPolynomialFormula_const (fun _ => T (Pi.single i (Pi.single j 1)) k))

theorem hasPolynomialCoordinates_bundleWordEndpoint {I : Type} {n m h c M N : ℕ}
    (a : DynkinCoefficients c 2) (letters : Fin m → I)
    (input : (Fin M → ℝ) ≃L[ℝ] (Fin h → Fin (m + m) → ℝ))
    (output : (Fin N → ℝ) ≃L[ℝ] (Fin h → Fin n → ℝ)) :
    HasPolynomialCoordinates (bundleWordEndpoint (n := n) a letters input output) := by
  apply hasPolynomialCoordinates_linear_pi_output output.symm.toContinuousLinearMap
  intro i
  have ht := hasPolynomialCoordinates_linear (fun _ : WordLawData I n =>
    (differenceParameters m).comp ((ContinuousLinearMap.proj i).comp input.toContinuousLinearMap))
  have hf : HasPolynomialCoordinates (fun p : WordLawData I n => fun t : Fin M → ℝ =>
      differenceAmplitudeWordEndpoint a letters p (input t i)) := by
    unfold differenceAmplitudeWordEndpoint amplitudeWordEndpoint
    apply hasPolynomialCoordinates_listProduct a Prod.fst
    intro j
    exact (hasPolynomialCoordinates_const (fun p : WordLawData I n => p.2 (letters j))).smul (ht j)
  exact hf

theorem contDiff_bundleWordEndpoint {I : Type} [Fintype I] {n m h c M N : ℕ} {q : ℕ∞}
    (a : DynkinCoefficients c 2) (letters : Fin m → I)
    (input : (Fin M → ℝ) ≃L[ℝ] (Fin h → Fin (m + m) → ℝ))
    (output : (Fin N → ℝ) ≃L[ℝ] (Fin h → Fin n → ℝ)) :
    ContDiff ℝ q (fun z : WordLawData I n × (Fin M → ℝ) =>
      bundleWordEndpoint a letters input output z.1 z.2) := by
  unfold bundleWordEndpoint differenceAmplitudeWordEndpoint amplitudeWordEndpoint
  apply output.symm.contDiff.comp
  apply contDiff_pi.mpr
  intro j
  apply contDiff_polynomialListProduct_ofFn a
    (fun z : WordLawData I n × (Fin M → ℝ) => z.1.1) _ contDiff_fst.fst
  intro k
  have ht : ContDiff ℝ q (fun z : WordLawData I n × (Fin M → ℝ) =>
      differenceParameters m (input z.2 j) k) :=
    (contDiff_apply ℝ ℝ k).comp ((differenceParameters m).contDiff.comp
      ((contDiff_apply ℝ (Fin (m + m) → ℝ) j).comp (input.contDiff.comp contDiff_snd)))
  exact ht.smul ((contDiff_apply ℝ (Fin n → ℝ) (letters k)).comp contDiff_fst.snd)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_BundleParameterCharts
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual global interval coordinates, grouped into source bundles -/

noncomputable section
namespace PolycyclicRecognition

theorem bundleParameterChart_left (h m : ℕ) (t : Fin (h * m + h * m) → ℝ)
    (i : Fin h) (j : Fin m) :
    bundleParameterChart h m t i (Fin.castAdd m j) =
      t (Fin.castAdd (h * m) (finProdFinEquiv (i, j))) := by
  simp [bundleParameterChart, bundleParameterIndex]

theorem bundleParameterChart_right (h m : ℕ) (t : Fin (h * m + h * m) → ℝ)
    (i : Fin h) (j : Fin m) :
    bundleParameterChart h m t i (Fin.natAdd m j) =
      t (Fin.natAdd (h * m) (finProdFinEquiv (i, j))) := by
  simp only [bundleParameterChart, rectangularCoordinateChart_apply, bundleParameterIndex,
    Equiv.trans_apply, Equiv.prodCongr_apply, Prod.map_apply, Equiv.refl_apply,
    finSumFinEquiv_symm_apply_natAdd, Equiv.prodSumDistrib_apply_right,
    Equiv.sumCongr_apply, Sum.map_inr, finSumFinEquiv_apply_right]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_BundleWordRank
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Independent full-rank source bundles give a full-rank tuple map -/

noncomputable section
namespace PolycyclicRecognition

open Module

theorem pi_map_submersive {ι V W : Type} [Fintype ι]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W]
    (f : V → W) (z : ι → V) (hd : ∀ i, DifferentiableAt ℝ f (z i))
    (hs : ∀ i, Function.Surjective (fderiv ℝ f (z i))) :
    Function.Surjective (fderiv ℝ (fun x : ι → V => fun i => f (x i)) z) := by
  have hder : HasFDerivAt (fun x : ι → V => fun i => f (x i))
      (ContinuousLinearMap.pi (fun i => (fderiv ℝ f (z i)).comp (ContinuousLinearMap.proj i))) z :=
    hasFDerivAt_pi.mpr (fun i => (hd i).hasFDerivAt.comp z ((ContinuousLinearMap.proj i : (ι → V) →L[ℝ] V).hasFDerivAt))
  rw [hder.fderiv]
  intro w
  choose v hv using (fun i => hs i (w i))
  exact ⟨v, funext hv⟩

theorem bundleWordEndpoint_submersive {I : Type} [Fintype I] {n m h c M N : ℕ}
    (a : DynkinCoefficients c 2) (letters : Fin m → I)
    (input : (Fin M → ℝ) ≃L[ℝ] (Fin h → Fin (m + m) → ℝ))
    (output : (Fin N → ℝ) ≃L[ℝ] (Fin h → Fin n → ℝ))
    (p : WordLawData I n) (t₀ : Fin (m + m) → ℝ)
    (hs : Function.Surjective (fderiv ℝ (differenceAmplitudeWordEndpoint a letters p) t₀)) :
    Function.Surjective (fderiv ℝ (bundleWordEndpoint a letters input output p)
      (input.symm (fun _ => t₀))) := by
  let f := differenceAmplitudeWordEndpoint a letters p
  let z := fun _ : Fin h => t₀
  have hdf : Differentiable ℝ f :=
    ((contDiff_differenceAmplitudeWord (q := 1) a letters).comp
      (contDiff_const.prodMk contDiff_id)).differentiable one_ne_zero
  have hs' := pi_map_submersive f z (fun i => hdf _) (fun _ => hs)
  have hd : DifferentiableAt ℝ (fun x : Fin h → Fin (m + m) → ℝ => fun i => f (x i)) z :=
    (differentiable_pi.mpr (fun i => hdf.comp (ContinuousLinearMap.proj i).differentiable)) z
  have hd' : HasFDerivAt (fun x : Fin h → Fin (m + m) → ℝ => fun i => f (x i))
      (fderiv ℝ (fun x : Fin h → Fin (m + m) → ℝ => fun i => f (x i)) z)
      (input (input.symm z)) := by
    simpa only [ContinuousLinearEquiv.apply_symm_apply] using hd.hasFDerivAt
  have h₁ := hd'.comp (input.symm z) input.hasFDerivAt
  have h₂ := output.symm.hasFDerivAt.comp (input.symm z) h₁
  change HasFDerivAt (bundleWordEndpoint a letters input output p) _ (input.symm z) at h₂
  rw [h₂.fderiv]
  exact output.symm.surjective.comp (hs'.comp input.surjective)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_SequenceSubexponential
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Subexponential estimates along the actual sequence of profile scales -/

noncomputable section

namespace PolycyclicRecognition

open Filter
open scoped Topology

theorem HasSubexponentialLowerBound.along_sequence {f : ℝ → ℝ}
    (hf : HasSubexponentialLowerBound f) {scale : ℕ → ℝ}
    (hs : Tendsto scale atTop atTop) : HasSubexponentialLowerBoundSeq scale (f ∘ scale) :=
  fun ε hε => hs.eventually (hf ε hε)

theorem HasSubexponentialLowerBoundSeq.eventually_pos {scale f : ℕ → ℝ}
    (hf : HasSubexponentialLowerBoundSeq scale f) : ∀ᶠ n in atTop, 0 < f n :=
  (hf 1 zero_lt_one).mono (fun _ h => (Real.exp_pos _).trans_le h)

theorem HasSubexponentialLowerBoundSeq.mono {scale f g : ℕ → ℝ}
    (hf : HasSubexponentialLowerBoundSeq scale f) (hfg : f ≤ᶠ[atTop] g) :
    HasSubexponentialLowerBoundSeq scale g := by
  intro ε hε
  filter_upwards [hf ε hε, hfg] with n hn hfg
  exact hn.trans hfg

theorem HasSubexponentialLowerBoundSeq.mul {scale f g : ℕ → ℝ}
    (hf : HasSubexponentialLowerBoundSeq scale f) (hg : HasSubexponentialLowerBoundSeq scale g) :
    HasSubexponentialLowerBoundSeq scale (fun n => f n * g n) := by
  intro ε hε
  filter_upwards [hf (ε / 2) (half_pos hε), hg (ε / 2) (half_pos hε)] with n hn hm
  calc
    Real.exp (-ε * scale n) = Real.exp (-(ε / 2) * scale n) *
        Real.exp (-(ε / 2) * scale n) := by rw [← Real.exp_add]; congr 1; ring
    _ ≤ f n * g n := mul_le_mul hn hm (Real.exp_pos _).le ((Real.exp_pos _).trans_le hn).le

theorem HasSubexponentialLowerBoundSeq.div {scale f g : ℕ → ℝ}
    (hf : HasSubexponentialLowerBoundSeq scale f) (hg : HasSubexponentialUpperBoundSeq scale g)
    (hg0 : ∀ᶠ n in atTop, 0 < g n) :
    HasSubexponentialLowerBoundSeq scale (fun n => f n / g n) := by
  intro ε hε
  filter_upwards [hf (ε / 2) (half_pos hε), hg (ε / 2) (half_pos hε), hg0] with n hn hm h0
  calc
    Real.exp (-ε * scale n) = Real.exp (-(ε / 2) * scale n) /
        Real.exp (ε / 2 * scale n) := by rw [← Real.exp_sub]; congr 1; ring
    _ ≤ f n / g n := div_le_div₀ ((Real.exp_pos _).trans_le hn).le hn h0 hm

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_GrowingPositiveParameters
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_countable _root_.OAI.PolycyclicRecognition.finitelyGeneratedSubgroupIndex_countable _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Positive parameter sets on growing input cubes -/

noncomputable section

namespace PolycyclicRecognition

open Set Metric MeasureTheory Filter
open scoped Topology ENNReal NNReal

theorem exists_positive_parameter_sets_growing_sequence {m : ℕ} (R : ℕ → ℝ)
    (scale : ℕ → ℝ) (hR : ∀ r, 0 < R r)
    (E : ℕ → Set (Fin m → ℝ)) (hE : ∀ r, MeasurableSet (E r))
    (hER : ∀ r, E r ⊆ closedBall 0 (R r))
    (hmlower : HasSubexponentialLowerBoundSeq scale (fun r => (volume (E r)).toReal)) :
    ∃ F : ℕ → Set (Fin m → ℝ),
      (∀ r, MeasurableSet (F r)) ∧ (∀ r, F r ⊆ closedBall 0 (R r)) ∧
      (∀ r, 0 < (volume (F r)).toReal) ∧
      HasSubexponentialLowerBoundSeq scale (fun r => (volume (F r)).toReal) ∧
      ∀ᶠ r in atTop, F r = E r := by
  classical
  let F := fun r => if 0 < (volume (E r)).toReal then E r else closedBall 0 (R r)
  have heq : ∀ᶠ r in atTop, F r = E r :=
    hmlower.eventually_pos.mono (fun _ h => ite_eq_left h)
  have hball (r : ℕ) : 0 < (volume (closedBall (0 : Fin m → ℝ) (R r))).toReal := by
    have hr := hR r
    rw [Real.volume_pi_closedBall _ (hR r).le, ENNReal.toReal_ofReal (by positivity)]
    positivity
  refine ⟨F, ?_, ?_, ?_, ?_, heq⟩
  · intro r
    dsimp [F]
    split_ifs
    · exact hE r
    · exact measurableSet_closedBall
  · intro r
    dsimp [F]
    split_ifs
    · exact hER r
    · exact Subset.rfl
  · intro r
    dsimp [F]
    split_ifs with h
    · exact h
    · exact hball r
  · apply hmlower.mono
    exact heq.mono (fun _ h => le_of_eq (congrArg (fun s => (volume s).toReal) h.symm))

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_PolynomialCoefficientContinuity
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instNonemptyBases _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_nonempty _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Coefficients of a continuous bounded-degree polynomial family

Each coefficient is a fixed finite linear combination of evaluations on
the finite-dimensional space of bounded-degree polynomials. This supplies
uniform coefficient bounds from compact parameter sets, even when the
input cubes have growing radii.
-/

noncomputable section
namespace PolycyclicRecognition

open Module MvPolynomial

theorem boundedDegreeCoefficient_mem_span_evaluations {m : ℕ}
    (D : ℕ) (s : Fin m →₀ ℕ) :
    (lcoeff ℝ s).comp (restrictTotalDegree (Fin m) ℝ D).subtype ∈
      Submodule.span ℝ (Set.range (boundedDegreeEvaluation (m := m) D)) := by
  apply FiniteDimensional.mem_span_of_iInf_ker_le_ker
  intro p hp
  have he (x : Fin m → ℝ) : eval x p.val = 0 := by
    have hx := (Submodule.mem_iInf _).mp hp x
    exact hx
  have hz : p.val = 0 := MvPolynomial.funext (fun x => by simpa using he x)
  change p.val.coeff s = 0
  rw [hz]
  rfl

theorem continuous_polynomial_coefficients {P : Type} [TopologicalSpace P] {m : ℕ}
    (p : P → MvPolynomial (Fin m) ℝ) (D : ℕ)
    (hD : ∀ a, (p a).totalDegree ≤ D)
    (heval : ∀ x : Fin m → ℝ, Continuous (fun a => eval x (p a)))
    (s : Fin m →₀ ℕ) : Continuous (fun a => (p a).coeff s) := by
  classical
  obtain ⟨t, ht⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp
    (boundedDegreeCoefficient_mem_span_evaluations D s)
  have hrep (a : P) : (p a).coeff s =
      ∑ x ∈ t.support, t x * eval x (p a) := by
    have hp : p a ∈ restrictTotalDegree (Fin m) ℝ D :=
      (mem_restrictTotalDegree _ _ _).mpr (hD a)
    have h := congrArg (fun L : restrictTotalDegree (Fin m) ℝ D →ₗ[ℝ] ℝ => L ⟨p a, hp⟩) ht
    simpa [Finsupp.linearCombination_apply, Finsupp.sum, boundedDegreeEvaluation] using h.symm
  simp_rw [hrep]
  apply continuous_finsetSum
  intro x _
  exact continuous_const.mul (heval x)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_UniformPolynomialGrowth
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform polynomial growth over compact coefficient families -/

noncomputable section
namespace PolycyclicRecognition

open MvPolynomial Set
open scoped BigOperators

theorem norm_monomial_value_le {m D : ℕ} (s : Fin m →₀ ℕ)
    (hs : ∀ i, s i ≤ D) (x : Fin m → ℝ) :
    |∏ i, x i ^ s i| ≤ (1 + ‖x‖) ^ (m * D) := by
  rw [Finset.abs_prod]
  calc
    ∏ i, |x i ^ s i| ≤ ∏ _i : Fin m, (1 + ‖x‖) ^ D := by
      apply Finset.prod_le_prod (fun _ _ => abs_nonneg _)
      intro i _
      rw [abs_pow]
      exact (pow_le_pow_left₀ (abs_nonneg _) ((norm_le_pi_norm x i).trans
        (by linarith [norm_nonneg x])) _).trans
          (pow_le_pow_right₀ (by linarith [norm_nonneg x]) (hs i))
    _ = (1 + ‖x‖) ^ (m * D) := by simp [← pow_mul, Nat.mul_comm]

theorem polynomial_support_subset_bounded_exponents {m D : ℕ}
    (p : MvPolynomial (Fin m) ℝ) (hp : p.totalDegree ≤ D) :
    p.support ⊆ (finite_bounded_exponents m D).toFinset := by
  intro s hs
  simp only [Finite.mem_toFinset]
  intro i
  exact ((le_degreeOf_of_mem_support i hs).trans (degreeOf_le_totalDegree _ i)).trans hp

theorem continuous_polynomial_evaluation_of_coefficients
    {P : Type} [TopologicalSpace P] {m : ℕ}
    (p : P → MvPolynomial (Fin m) ℝ) (D : ℕ)
    (hD : ∀ a, (p a).totalDegree ≤ D)
    (hc : ∀ s, Continuous (fun a => (p a).coeff s)) (x : Fin m → ℝ) :
    Continuous (fun a => eval x (p a)) := by
  classical
  let T := (finite_bounded_exponents m D).toFinset
  have he (a : P) : eval x (p a) = ∑ s ∈ T, (p a).coeff s * ∏ i, x i ^ s i := by
    rw [eval_eq']
    apply Finset.sum_subset (polynomial_support_subset_bounded_exponents (p a) (hD a))
    intro s _ hs
    have hz : (p a).coeff s = 0 := notMem_support_iff.mp hs
    rw [hz, zero_mul]
  simp_rw [he]
  exact continuous_finsetSum _ (fun s _ => (hc s).mul continuous_const)

theorem exists_uniform_polynomial_growth
    {P : Type} [TopologicalSpace P] {m : ℕ}
    (p : P → MvPolynomial (Fin m) ℝ) (D : ℕ)
    (hD : ∀ a, (p a).totalDegree ≤ D)
    (heval : ∀ x : Fin m → ℝ, Continuous (fun a => eval x (p a)))
    (S : Set P) (hS : IsCompact S) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ a ∈ S, ∀ x : Fin m → ℝ,
      |eval x (p a)| ≤ C * (1 + ‖x‖) ^ (m * D) := by
  classical
  let T := (finite_bounded_exponents m D).toFinset
  have hb (s : Fin m →₀ ℕ) : ∃ B : ℝ, 0 ≤ B ∧ ∀ a ∈ S, |(p a).coeff s| ≤ B := by
    obtain ⟨B, hB⟩ := hS.exists_bound_of_continuousOn
      (continuous_polynomial_coefficients p D hD heval s).continuousOn
    exact ⟨max B 0, le_max_right _ _, fun a ha => (hB a ha).trans (le_max_left _ _)⟩
  choose B hB hbound using hb
  let C := max 1 (∑ s ∈ T, B s)
  refine ⟨C, le_max_left _ _, ?_⟩
  intro a ha x
  have hsub : (p a).support ⊆ T :=
    polynomial_support_subset_bounded_exponents (p a) (hD a)
  rw [eval_eq']
  calc
    |∑ s ∈ (p a).support, (p a).coeff s * ∏ i, x i ^ s i| ≤
        ∑ s ∈ (p a).support, |(p a).coeff s * ∏ i, x i ^ s i| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ s ∈ (p a).support, B s * (1 + ‖x‖) ^ (m * D) := by
      apply Finset.sum_le_sum
      intro s hs
      rw [abs_mul]
      apply mul_le_mul (hbound s a ha) (norm_monomial_value_le s ?_ x) (abs_nonneg _) (hB s)
      intro i
      exact ((le_degreeOf_of_mem_support i hs).trans (degreeOf_le_totalDegree _ i)).trans (hD a)
    _ ≤ ∑ s ∈ T, B s * (1 + ‖x‖) ^ (m * D) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun s _ _ =>
        mul_nonneg (hB s) (pow_nonneg (by linarith [norm_nonneg x]) _))
    _ = (∑ s ∈ T, B s) * (1 + ‖x‖) ^ (m * D) := by rw [Finset.sum_mul]
    _ ≤ C * (1 + ‖x‖) ^ (m * D) :=
      mul_le_mul_of_nonneg_right (le_max_right _ _) (pow_nonneg (by linarith [norm_nonneg x]) _)

theorem exists_uniform_finite_polynomial_growth
    {P J : Type} [TopologicalSpace P] [Fintype J] {m : ℕ}
    (p : J → P → MvPolynomial (Fin m) ℝ) (D : ℕ)
    (hD : ∀ j a, (p j a).totalDegree ≤ D)
    (heval : ∀ j (x : Fin m → ℝ), Continuous (fun a => eval x (p j a)))
    (S : Set P) (hS : IsCompact S) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ j a, a ∈ S → ∀ x : Fin m → ℝ,
      |eval x (p j a)| ≤ C * (1 + ‖x‖) ^ (m * D) := by
  choose C hC hb using (fun j => exists_uniform_polynomial_growth (p j) D (hD j) (heval j) S hS)
  have hC0 : ∀ i, 0 ≤ C i := fun i => (hC i).trans' zero_le_one
  refine ⟨1 + ∑ j, C j, le_add_of_nonneg_right (Finset.sum_nonneg (fun i _ => hC0 i)), ?_⟩
  intro j a ha x
  apply (hb j a ha x).trans
  apply mul_le_mul_of_nonneg_right _ (pow_nonneg (by linarith [norm_nonneg x]) _)
  have hj := Finset.single_le_sum (fun i _ => hC0 i) (Finset.mem_univ j)
  linarith

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_PolynomialDerivativeGrowth
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Derivative bounds on growing polynomial input cubes -/

noncomputable section
namespace PolycyclicRecognition

open MvPolynomial Set Metric
open scoped BigOperators

theorem continuous_pderiv_evaluation {P : Type} [TopologicalSpace P] {m : ℕ}
    (p : P → MvPolynomial (Fin m) ℝ) (D : ℕ)
    (hD : ∀ a, (p a).totalDegree ≤ D)
    (heval : ∀ x, Continuous (fun a => eval x (p a))) (j : Fin m) (x : Fin m → ℝ) :
    Continuous (fun a => eval x (pderiv j (p a))) := by
  apply continuous_polynomial_evaluation_of_coefficients (fun a => pderiv j (p a)) D
    (fun a => (totalDegree_pderiv_le (p a) j).trans ((Nat.sub_le _ _).trans (hD a)))
  intro s
  simp only [coeff_pderiv]
  exact (continuous_polynomial_coefficients p D hD heval _).mul continuous_const

theorem norm_clm_pi_domain_le {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {m : ℕ} (L : (Fin m → ℝ) →L[ℝ] V) {B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ j, ‖L (Pi.single j 1)‖ ≤ B) : ‖L‖ ≤ (m : ℝ) * B := by
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (Nat.cast_nonneg _) hB)
  intro x
  have he : L x = ∑ j, x j • L (Pi.single j 1) := by
    conv_lhs => rw [pi_eq_sum_univ' x]
    simp only [map_sum, map_smul]
  rw [he]
  calc
    ‖∑ j, x j • L (Pi.single j 1)‖ ≤ ∑ j, ‖x j • L (Pi.single j 1)‖ := norm_sum_le _ _
    _ ≤ ∑ _j : Fin m, ‖x‖ * B := by
      apply Finset.sum_le_sum
      intro j _
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul (norm_le_pi_norm x j) (hb j) (norm_nonneg _) (norm_nonneg _)
    _ = (m : ℝ) * B * ‖x‖ := by simp <;> ring

@[simp] theorem polynomialMapDifferential_basis {m n : ℕ}
    (p : Fin n → MvPolynomial (Fin m) ℝ) (x : Fin m → ℝ) (i : Fin n) (j : Fin m) :
    polynomialMapDifferential p x (Pi.single j 1) i = eval x (pderiv j (p i)) :=
  polynomialDifferential_basis (p i) x j

theorem norm_polynomialMapDifferential_le {m n : ℕ}
    (p : Fin n → MvPolynomial (Fin m) ℝ) (x : Fin m → ℝ) {B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ i j, |eval x (pderiv j (p i))| ≤ B) :
    ‖polynomialMapDifferential p x‖ ≤ (m : ℝ) * B := by
  apply norm_clm_pi_domain_le _ hB
  intro j
  apply (pi_norm_le_iff_of_nonneg hB).mpr
  intro i
  simpa only [polynomialMapDifferential_basis, Real.norm_eq_abs] using hb i j

theorem norm_polynomialDifferential_le {m : ℕ}
    (p : MvPolynomial (Fin m) ℝ) (x : Fin m → ℝ) {B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ j, |eval x (pderiv j p)| ≤ B) :
    ‖polynomialDifferential p x‖ ≤ (m : ℝ) * B := by
  apply norm_clm_pi_domain_le _ hB
  intro j
  simpa only [polynomialDifferential_basis, Real.norm_eq_abs] using hb j

theorem uniform_polynomial_map_derivative_bounds
    {P : Type} [TopologicalSpace P] {m n : ℕ}
    (p : P → Fin n → MvPolynomial (Fin m) ℝ) (D : ℕ)
    (hD : ∀ a i, (p a i).totalDegree ≤ D)
    (heval : ∀ i x, Continuous (fun a => eval x (p a i)))
    (S : Set P) (hS : IsCompact S) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ a ∈ S, ∀ R : ℝ, 0 ≤ R →
      (∀ x, ‖x‖ ≤ R → ‖polynomialMapDifferential (p a) x‖ ≤ C * (1 + R) ^ (m * D)) ∧
      ∀ x y, ‖x‖ ≤ R → ‖y‖ ≤ R →
        ‖polynomialMapDifferential (p a) x - polynomialMapDifferential (p a) y‖ ≤
          C * (1 + R) ^ (m * D) * dist x y := by
  let p₁ := fun j : Fin n × Fin m => fun a => pderiv j.2 (p a j.1)
  have hD₁ (j : Fin n × Fin m) (a : P) : (p₁ j a).totalDegree ≤ D :=
    (totalDegree_pderiv_le (p a j.1) j.2).trans ((Nat.sub_le _ _).trans (hD a j.1))
  have he₁ (j : Fin n × Fin m) (x : Fin m → ℝ) :
      Continuous (fun a => eval x (p₁ j a)) :=
    continuous_pderiv_evaluation (fun a => p a j.1) D (fun a => hD a j.1)
      (heval j.1) j.2 x
  obtain ⟨C₁, hC₁, hb₁⟩ := exists_uniform_finite_polynomial_growth p₁ D hD₁ he₁ S hS
  let p₂ := fun j : (Fin n × Fin m) × Fin m => fun a => pderiv j.2 (p₁ j.1 a)
  have hD₂ (j : (Fin n × Fin m) × Fin m) (a : P) : (p₂ j a).totalDegree ≤ D :=
    (totalDegree_pderiv_le (p₁ j.1 a) j.2).trans ((Nat.sub_le _ _).trans (hD₁ j.1 a))
  have he₂ (j : (Fin n × Fin m) × Fin m) (x : Fin m → ℝ) :
      Continuous (fun a => eval x (p₂ j a)) :=
    continuous_pderiv_evaluation (p₁ j.1) D (hD₁ j.1) (he₁ j.1) j.2 x
  obtain ⟨C₂, hC₂, hb₂⟩ := exists_uniform_finite_polynomial_growth p₂ D hD₂ he₂ S hS
  let C := max 1 (max ((m : ℝ) * C₁) ((m : ℝ) ^ 2 * C₂))
  have hc₁ : (m : ℝ) * C₁ ≤ C := (le_max_left _ _).trans (le_max_right _ _)
  have hc₂ : (m : ℝ) ^ 2 * C₂ ≤ C := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨C, le_max_left _ _, ?_⟩
  intro a ha R hR
  have hpow : 0 ≤ (1 + R) ^ (m * D) := pow_nonneg (by linarith) _
  have hb₁R (i : Fin n) (j : Fin m) (x : Fin m → ℝ) (hx : ‖x‖ ≤ R) :
      |eval x (pderiv j (p a i))| ≤ C₁ * (1 + R) ^ (m * D) :=
    (hb₁ (i, j) a ha x).trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by positivity) (by linarith) _) (by linarith))
  have hb₂R (i : Fin n) (j k : Fin m) (x : Fin m → ℝ) (hx : ‖x‖ ≤ R) :
      |eval x (pderiv k (pderiv j (p a i)))| ≤ C₂ * (1 + R) ^ (m * D) :=
    (hb₂ ((i, j), k) a ha x).trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by positivity) (by linarith) _) (by linarith))
  constructor
  · intro x hx
    calc
      _ ≤ (m : ℝ) * (C₁ * (1 + R) ^ (m * D)) :=
        norm_polynomialMapDifferential_le _ _ (mul_nonneg (by linarith) hpow) (fun i j => hb₁R i j x hx)
      _ ≤ C * (1 + R) ^ (m * D) := by
        rw [← mul_assoc]
        exact mul_le_mul_of_nonneg_right hc₁ hpow
  · intro x y hx hy
    have hscalar (i : Fin n) (j : Fin m) :
        |eval x (pderiv j (p a i)) - eval y (pderiv j (p a i))| ≤
          (m : ℝ) * (C₂ * (1 + R) ^ (m * D)) * dist x y := by
      have h := (convex_closedBall (0 : Fin m → ℝ) R).norm_image_sub_le_of_norm_hasFDerivWithin_le
        (fun u _ => (hasFDerivAt_mvPolynomial_eval (pderiv j (p a i)) u).hasFDerivWithinAt)
        (fun u hu => norm_polynomialDifferential_le _ _ (mul_nonneg (by linarith) hpow)
          (fun k => hb₂R i j k u (by simpa only [mem_closedBall, dist_zero_right] using hu)))
        (show y ∈ closedBall 0 R by simpa using hy) (show x ∈ closedBall 0 R by simpa using hx)
      simpa only [Real.norm_eq_abs, dist_eq_norm] using h
    have hB : 0 ≤ (m : ℝ) * (C₂ * (1 + R) ^ (m * D)) * dist x y := by positivity
    calc
      _ ≤ (m : ℝ) * ((m : ℝ) * (C₂ * (1 + R) ^ (m * D)) * dist x y) := by
        apply norm_clm_pi_domain_le _ hB
        intro j
        apply (pi_norm_le_iff_of_nonneg hB).mpr
        intro i
        simpa only [sub_apply, Pi.sub_apply,
          polynomialMapDifferential_basis, Real.norm_eq_abs] using hscalar i j
      _ = ((m : ℝ) ^ 2 * C₂) * (1 + R) ^ (m * D) * dist x y := by ring
      _ ≤ C * (1 + R) ^ (m * D) * dist x y :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc₂ hpow) dist_nonneg

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_PolynomialSliceGrowth
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Growing-cube bounds for the actual derivative minors -/

noncomputable section
namespace PolycyclicRecognition

open Set Metric MvPolynomial

theorem norm_finAppend_le {n k : ℕ} {v : Fin n → ℝ} {z : Fin k → ℝ} {R : ℝ}
    (hR : 0 ≤ R) (hv : ‖v‖ ≤ R) (hz : ‖z‖ ≤ R) : ‖Fin.append v z‖ ≤ R := by
  apply (pi_norm_le_iff_of_nonneg hR).mpr
  intro i
  refine Fin.addCases ?_ ?_ i
  · intro j
    simpa only [Fin.append_left] using (norm_le_pi_norm v j).trans hv
  · intro j
    simpa only [Fin.append_right] using (norm_le_pi_norm z j).trans hz

theorem norm_appendParameterLinear_le (n k : ℕ) : ‖appendParameterLinear n k‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro v
  rw [one_mul, appendParameterLinear_apply]
  exact norm_finAppend_le (norm_nonneg _) le_rfl (by simp)

theorem dist_finAppend_same {n k : ℕ} (v w : Fin n → ℝ) (z : Fin k → ℝ) :
    dist (Fin.append v z) (Fin.append w z) = dist v w := by
  have h := (Fin.appendIsometry (α := ℝ) n k).isometry.dist_eq (v, z) (w, z)
  change dist (Fin.append v z) (Fin.append w z) = dist (v, z) (w, z) at h
  simpa only [Prod.dist_eq, dist_self, max_eq_left dist_nonneg] using h

theorem uniform_polynomial_slice_derivative_bounds
    {P : Type} [TopologicalSpace P] {n k : ℕ}
    (p : P → Fin n → MvPolynomial (Fin (n + k)) ℝ) (D : ℕ)
    (hD : ∀ a i, (p a i).totalDegree ≤ D)
    (heval : ∀ i x, Continuous (fun a => eval x (p a i)))
    (S : Set P) (hS : IsCompact S) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ a ∈ S, ∀ R : ℝ, 0 ≤ R →
      (∀ v z, ‖v‖ ≤ R → ‖z‖ ≤ R →
        ‖polynomialSliceDifferential (p a) v z‖ ≤ C * (1 + R) ^ ((n + k) * D)) ∧
      ∀ v w z, ‖v‖ ≤ R → ‖w‖ ≤ R → ‖z‖ ≤ R →
        ‖polynomialSliceDifferential (p a) v z - polynomialSliceDifferential (p a) w z‖ ≤
          C * (1 + R) ^ ((n + k) * D) * dist v w := by
  obtain ⟨C, hC, hbound⟩ := uniform_polynomial_map_derivative_bounds p D hD heval S hS
  refine ⟨C, hC, ?_⟩
  intro a ha R hR
  obtain ⟨hb, hl⟩ := hbound a ha R hR
  have hnorm (A : (Fin (n + k) → ℝ) →L[ℝ] (Fin n → ℝ)) :
      ‖A.comp (appendParameterLinear n k)‖ ≤ ‖A‖ := by
    calc
      _ ≤ ‖A‖ * ‖appendParameterLinear n k‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ ‖A‖ * 1 := mul_le_mul_of_nonneg_left (norm_appendParameterLinear_le n k) (norm_nonneg _)
      _ = ‖A‖ := mul_one _
  constructor
  · intro v z hv hz
    exact (hnorm _).trans (hb _ (norm_finAppend_le hR hv hz))
  · intro v w z hv hw hz
    have he : polynomialSliceDifferential (p a) v z - polynomialSliceDifferential (p a) w z =
        (polynomialMapDifferential (p a) (Fin.append v z) -
          polynomialMapDifferential (p a) (Fin.append w z)).comp (appendParameterLinear n k) := by
      ext x i
      rfl
    rw [he]
    exact (hnorm _).trans (by simpa only [dist_finAppend_same] using
      (hl _ _ (norm_finAppend_le hR hv hz) (norm_finAppend_le hR hw hz)))

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

theorem sequence_subexponential_lower_const (hs : Tendsto scale atTop atTop)
    {c : ℝ} (hc : 0 < c) : HasSubexponentialLowerBoundSeq scale (fun _ => c) := by
  simpa only [Function.comp_def] using (subexponential_lower_const hc).along_sequence hs

theorem HasSubexponentialLowerBoundSeq.min {f g : ℕ → ℝ}
    (hf : HasSubexponentialLowerBoundSeq scale f) (hg : HasSubexponentialLowerBoundSeq scale g) :
    HasSubexponentialLowerBoundSeq scale (fun n => min (f n) (g n)) := by
  intro ε hε
  filter_upwards [hf ε hε, hg ε hε] with n hn hm
  exact le_min hn hm

theorem HasSubexponentialLowerBoundSeq.inv {f : ℕ → ℝ}
    (hf : HasSubexponentialLowerBoundSeq scale f) :
    HasSubexponentialUpperBoundSeq scale (fun n => (f n)⁻¹) := by
  intro ε hε
  filter_upwards [hf ε hε] with n hn
  calc
    (f n)⁻¹ ≤ (Real.exp (-ε * scale n))⁻¹ := by
      simpa only [one_div] using one_div_le_one_div_of_le (Real.exp_pos _) hn
    _ = Real.exp (ε * scale n) := by rw [← Real.exp_neg]; congr 1; ring

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
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_SequencePolynomialValues
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Subexponential mass with a subexponential polynomial minor bound -/

noncomputable section

namespace PolycyclicRecognition

open Set Metric MeasureTheory Filter
open scoped Topology

theorem exists_subexponential_large_polynomial_values_sequence
    (scale : ℕ → ℝ) (hscale : Tendsto scale atTop atTop)
    (rem : RemezPolynomialInput) (n D : ℕ) (hn : 1 ≤ n) (hD : 1 ≤ D)
    (p : ℕ → MvPolynomial (Fin n) ℝ) (hp : ∀ r, (p r).totalDegree ≤ D)
    (R c : ℕ → ℝ) (hR : ∀ r, 1 ≤ R r) (hc : ∀ r, 0 < c r)
    (hRupper : HasSubexponentialUpperBoundSeq scale R)
    (hclower : HasSubexponentialLowerBoundSeq scale c)
    (x₀ : ℕ → Fin n → ℝ) (hx₀ : ∀ r, x₀ r ∈ closedBall 0 (R r))
    (hvalue : ∀ r, c r ≤ |MvPolynomial.eval (x₀ r) (p r)|)
    (E : ℕ → Set (Fin n → ℝ)) (hE : ∀ r, MeasurableSet (E r))
    (hER : ∀ r, E r ⊆ closedBall 0 (R r))
    (hm : ∀ r, 0 < (volume (E r)).toReal)
    (hmlower : HasSubexponentialLowerBoundSeq scale (fun r => (volume (E r)).toReal)) :
    ∃ (η : ℕ → ℝ) (K : ℕ → Set (Fin n → ℝ)),
      (∀ r, 0 < η r) ∧ HasSubexponentialLowerBoundSeq scale η ∧
      (∀ r, K r ⊆ E r) ∧ (∀ r, IsCompact (K r)) ∧
      (∀ r, 0 < (volume (K r)).toReal) ∧
      HasSubexponentialLowerBoundSeq scale (fun r => (volume (K r)).toReal) ∧
      ∀ r x, x ∈ K r → η r ≤ |MvPolynomial.eval x (p r)| := by
  classical
  obtain ⟨A, hA, hselect⟩ := exists_compact_large_polynomial_values rem n D hn hD
  let m := fun r => (volume (E r)).toReal
  let a := fun r => 2 * A * (1 + R r) ^ n / m r
  let η := fun r => (c r / 2) / a r ^ (n * D)
  have ha (r : ℕ) : 0 < a r := by
    have h := hR r
    have h' := hm r
    dsimp [a, m]
    positivity
  have hη (r : ℕ) : 0 < η r := div_pos (div_pos (hc r) (by norm_num)) (pow_pos (ha r) (n * D))
  have hs (r : ℕ) := hselect (p r) (hp r) (R r) (c r) (hR r) (hc r)
    (x₀ r) (hx₀ r) (hvalue r) (E r) (hE r) (hER r) (hm r)
  choose K hKE hK hmass hgood using hs
  have hR0 : ∀ᶠ r in atTop, 0 ≤ 1 + R r := Eventually.of_forall (fun r => by have := hR r; linarith)
  have haUpper : HasSubexponentialUpperBoundSeq scale a := by
    have hpowers := ((sequence_subexponential_upper_const hscale 1).add hRupper hscale).pow hscale hR0 n
    have hnum := (sequence_subexponential_upper_const hscale (2 * A)).mul hpowers
      (Eventually.of_forall (fun _ => by positivity))
    have hh := hnum.mul hmlower.inv (Eventually.of_forall (fun r => by
      have := hR r
      positivity))
    simpa only [a, m, div_eq_mul_inv] using hh
  have hηlower : HasSubexponentialLowerBoundSeq scale η :=
    (hclower.div (sequence_subexponential_upper_const hscale 2) (Eventually.of_forall (by intro r; norm_num))).div
      (haUpper.pow hscale (Eventually.of_forall (fun r => (ha r).le)) (n * D))
      (Eventually.of_forall (fun r => pow_pos (ha r) (n * D)))
  have hKlower : HasSubexponentialLowerBoundSeq scale (fun r => (volume (K r)).toReal) := by
    apply (hmlower.div (sequence_subexponential_upper_const hscale 4) (Eventually.of_forall (by intro r; norm_num))).mono
    exact Eventually.of_forall (fun r => (hmass r).le)
  exact ⟨η, K, hη, hηlower, hKE, hK,
    fun r => (div_pos (hm r) (by norm_num : (0 : ℝ) < 4)).trans (hmass r),
    hKlower, hgood⟩

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_SequenceCompactImage
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Subexponential volume of compact noncritical parameter images -/

noncomputable section

namespace PolycyclicRecognition

open Set MeasureTheory Filter
open scoped Topology

theorem subexponential_compact_image_sequence
    (scale : ℕ → ℝ) (hscale : Tendsto scale atTop atTop)
    (n : ℕ) (f : ℕ → (Fin n → ℝ) → (Fin n → ℝ))
    (df : ℕ → (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] (Fin n → ℝ))
    (R L η : ℕ → ℝ) (hR : ∀ r, 0 ≤ R r) (hL : ∀ r, 1 ≤ L r)
    (hη : ∀ r, 0 < η r)
    (hRupper : HasSubexponentialUpperBoundSeq scale R) (hLupper : HasSubexponentialUpperBoundSeq scale L)
    (hηlower : HasSubexponentialLowerBoundSeq scale η)
    (hf : ∀ r z, ‖z‖ ≤ R r + 2 → HasFDerivAt (f r) (df r z) z)
    (hdf : ∀ r z, ‖z‖ ≤ R r + 2 → ‖df r z‖ ≤ L r)
    (hosc : ∀ r z w, ‖z‖ ≤ R r + 2 → ‖w‖ ≤ R r + 2 →
      ‖df r z - df r w‖ ≤ L r * dist z w)
    (K : ℕ → Set (Fin n → ℝ)) (hK : ∀ r, IsCompact (K r))
    (hgood : ∀ r z, z ∈ K r → ‖z‖ ≤ R r ∧ η r ≤ |(df r z).det|)
    (hKlower : HasSubexponentialLowerBoundSeq scale (fun r => (volume (K r)).toReal)) :
    (∀ r, IsCompact (f r '' K r)) ∧
      HasSubexponentialLowerBoundSeq scale (fun r => (volume (f r '' K r)).toReal) := by
  obtain ⟨C, hC, hb⟩ := exists_compact_image_volume_bound n
  let D := fun r => 8 * (C * L r ^ (n - 1)) * L r
  let ρ := fun r => min 1 (η r / D r)
  have hL0 : ∀ᶠ r in atTop, 0 ≤ L r := Eventually.of_forall (fun r => le_trans zero_le_one (hL r))
  have hD : ∀ r, 0 < D r := by
    intro r
    have hLp : 0 < L r := lt_of_lt_of_le zero_lt_one (hL r)
    dsimp [D]
    positivity
  have hDupper : HasSubexponentialUpperBoundSeq scale D := by
    have hp := hLupper.pow hscale hL0 (n - 1)
    have hcp := (sequence_subexponential_upper_const hscale C).mul hp (Eventually.of_forall (fun _ => hC.le))
    have h8 := (sequence_subexponential_upper_const hscale 8).mul hcp (Eventually.of_forall (by intro r; norm_num))
    exact h8.mul hLupper (Eventually.of_forall (by
      intro r
      have hLp : 0 ≤ L r := le_trans zero_le_one (hL r)
      positivity))
  have hρlower : HasSubexponentialLowerBoundSeq scale ρ :=
    (sequence_subexponential_lower_const hscale zero_lt_one).min
      (hηlower.div hDupper (Eventually.of_forall hD))
  have hρpos (r : ℕ) : 0 < ρ r := lt_min zero_lt_one (div_pos (hη r) (hD r))
  let B := fun r => (2 * R r / ρ r + 2) ^ n
  have hBupper : HasSubexponentialUpperBoundSeq scale B := by
    have h2R := (sequence_subexponential_upper_const hscale 2).mul hRupper
      (Eventually.of_forall (by intro r; norm_num))
    have hquot := h2R.mul hρlower.inv (Eventually.of_forall (fun r => mul_nonneg (by norm_num) (hR r)))
    have hsum := hquot.add (sequence_subexponential_upper_const hscale 2) hscale
    simpa only [B, div_eq_mul_inv] using hsum.pow hscale (Eventually.of_forall (by
      intro r
      have h := hR r
      have h' := hρpos r
      positivity)) n
  have hBpos (r : ℕ) : 0 < B r := by
    have h := hR r
    have h' := hρpos r
    dsimp [B]
    positivity
  have hresult (r : ℕ) := hb (f r) (df r) (R r) (L r) (η r)
    (hR r) (hL r) (hη r) (hf r) (hdf r) (hosc r) (K r) (hK r) (hgood r)
  refine ⟨fun r => (hresult r).1, ?_⟩
  apply ((hηlower.mul hKlower).div hBupper (Eventually.of_forall hBpos)).mono
  apply Eventually.of_forall
  intro r
  apply (div_le_iff₀ (hBpos r)).mpr
  simpa only [B, ρ, D, mul_comm] using (hresult r).2

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_SequenceCompactSections
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # One compact slice retains subexponential volume -/

noncomputable section

namespace PolycyclicRecognition

open Set Metric MeasureTheory Filter
open scoped Topology

theorem exists_subexponential_compact_sections_sequence
    (scale : ℕ → ℝ) (hscale : Tendsto scale atTop atTop)
    (n k : ℕ) (R : ℕ → ℝ) (hR : ∀ r, 1 ≤ R r)
    (hRupper : HasSubexponentialUpperBoundSeq scale R)
    (K : ℕ → Set ((Fin n → ℝ) × (Fin k → ℝ)))
    (hK : ∀ r, IsCompact (K r))
    (hKR : ∀ r p, p ∈ K r → ‖p.2‖ ≤ R r)
    (hKpos : ∀ r, 0 < (volume (K r)).toReal)
    (hKlower : HasSubexponentialLowerBoundSeq scale (fun r => (volume (K r)).toReal)) :
    ∃ z : ℕ → Fin k → ℝ,
      (∀ r, ‖z r‖ ≤ R r) ∧
      (∀ r, IsCompact {v | (v, z r) ∈ K r}) ∧
      HasSubexponentialLowerBoundSeq scale (fun r => (volume {v | (v, z r) ∈ K r}).toReal) := by
  classical
  let q := fun r => (2 * R r) ^ k
  let t := fun r => (volume (K r)).toReal / (2 * q r)
  have hqpos (r : ℕ) : 0 < q r := by have := hR r; dsimp [q] <;> positivity
  have htpos (r : ℕ) : 0 < t r := div_pos (hKpos r) (mul_pos (by norm_num) (hqpos r))
  have hs (r : ℕ) : ∃ z ∈ closedBall 0 (R r),
      IsCompact {v | (v, z) ∈ K r} ∧ t r < (volume {v | (v, z) ∈ K r}).toReal := by
    apply exists_compact_section_volume_gt n k (q := q r) (hK r) (isCompact_closedBall _ _)
      (fun p hp => by simpa only [mem_closedBall, dist_zero_right] using hKR r p hp)
      (htpos r).le
    · rw [Real.volume_pi_closedBall _ (by have := hR r; linarith),
        ENNReal.toReal_ofReal (by have := hR r; positivity)]
      simp only [Fintype.card_fin, q, le_refl]
    · have he : t r * q r = (volume (K r)).toReal / 2 := by
        dsimp [t]
        field_simp [ne_of_gt (hqpos r)]
      rw [he]
      linarith [hKpos r]
  choose z hz hzc hmass using hs
  have hqUpper : HasSubexponentialUpperBoundSeq scale q :=
    ((sequence_subexponential_upper_const hscale 2).mul hRupper (Eventually.of_forall (by intro r; norm_num))).pow hscale
      (Eventually.of_forall (fun r => by have := hR r; positivity)) k
  have htLower : HasSubexponentialLowerBoundSeq scale t := hKlower.div
    ((sequence_subexponential_upper_const hscale 2).mul hqUpper (Eventually.of_forall (by intro r; norm_num)))
    (Eventually.of_forall (fun r => mul_pos (by norm_num) (hqpos r)))
  exact ⟨z, fun r => by simpa only [mem_closedBall, dist_zero_right] using hz r,
    hzc, htLower.mono (Eventually.of_forall (fun r => (hmass r).le))⟩

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_SequencePolynomialImage
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_countable _root_.OAI.PolycyclicRecognition.finitelyGeneratedSubgroupIndex_countable _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Compact image-volume witnesses for arbitrary measurable parameters

The domain can have more coordinates than the range. The scalar polynomial
is an actual derivative minor. Remez, inner regularity, Fubini, and the
quantitative injective patch estimate provide the compact image witnesses.
-/

noncomputable section

namespace PolycyclicRecognition

open Set Metric MeasureTheory Filter
open scoped Topology

theorem exists_subexponential_polynomial_image_sequence
    (scale : ℕ → ℝ) (hscale : Tendsto scale atTop atTop)
    (rem : RemezPolynomialInput) (n k D : ℕ) (hn : 1 ≤ n) (hD : 1 ≤ D)
    (f : ℕ → (Fin (n + k) → ℝ) → (Fin n → ℝ))
    (df : ℕ → (Fin n → ℝ) → (Fin k → ℝ) → (Fin n → ℝ) →L[ℝ] (Fin n → ℝ))
    (p : ℕ → MvPolynomial (Fin (n + k)) ℝ)
    (hp : ∀ r, (p r).totalDegree ≤ D)
    (hminor : ∀ r v z, MvPolynomial.eval (Fin.append v z) (p r) = (df r v z).det)
    (R L c : ℕ → ℝ) (hR : ∀ r, 1 ≤ R r) (hL : ∀ r, 1 ≤ L r)
    (hc : ∀ r, 0 < c r)
    (hRupper : HasSubexponentialUpperBoundSeq scale R) (hLupper : HasSubexponentialUpperBoundSeq scale L)
    (hclower : HasSubexponentialLowerBoundSeq scale c)
    (hf : ∀ r z, ‖z‖ ≤ R r → ∀ v, ‖v‖ ≤ R r + 2 →
      HasFDerivAt (fun w => f r (Fin.append w z)) (df r v z) v)
    (hdf : ∀ r z, ‖z‖ ≤ R r → ∀ v, ‖v‖ ≤ R r + 2 → ‖df r v z‖ ≤ L r)
    (hosc : ∀ r z, ‖z‖ ≤ R r → ∀ v w, ‖v‖ ≤ R r + 2 → ‖w‖ ≤ R r + 2 →
      ‖df r v z - df r w z‖ ≤ L r * dist v w)
    (x₀ : ℕ → Fin (n + k) → ℝ) (hx₀ : ∀ r, x₀ r ∈ closedBall 0 (R r))
    (hvalue : ∀ r, c r ≤ |MvPolynomial.eval (x₀ r) (p r)|)
    (E : ℕ → Set (Fin (n + k) → ℝ)) (hE : ∀ r, MeasurableSet (E r))
    (hER : ∀ r, E r ⊆ closedBall 0 (R r))
    (hm : ∀ r, 0 < (volume (E r)).toReal)
    (hmlower : HasSubexponentialLowerBoundSeq scale (fun r => (volume (E r)).toReal)) :
    ∃ C : ℕ → Set (Fin n → ℝ),
      (∀ r, IsCompact (C r)) ∧ (∀ r, C r ⊆ f r '' E r) ∧
      HasSubexponentialLowerBoundSeq scale (fun r => (volume (C r)).toReal) := by
  obtain ⟨η, K, hη, hηlower, hKE, hK, hKpos, hKlower, hgood⟩ :=
    exists_subexponential_large_polynomial_values_sequence scale hscale rem (n + k) D (by omega) hD
      p hp R c hR hc hRupper hclower x₀ hx₀ hvalue E hE hER hm hmlower
  let e := Fin.appendIsometry (α := ℝ) n k
  let K' := fun r => e ⁻¹' K r
  have hK' (r : ℕ) : IsCompact (K' r) := e.toHomeomorph.isCompact_preimage.mpr (hK r)
  have hK'mass (r : ℕ) : volume (K' r) = volume (K r) :=
    (measurePreserving_finAppend n k).measure_preimage (hK r).measurableSet.nullMeasurableSet
  have hbound (r : ℕ) (v : (Fin n → ℝ) × (Fin k → ℝ)) (hv : v ∈ K' r) :
      ‖v‖ ≤ R r := by
    have hb := hER r (hKE r hv)
    have hd := e.dist_eq v 0
    have he0 : e 0 = 0 := by
      ext i
      refine Fin.addCases ?_ ?_ i <;> intro j <;> simp [e]
    rw [he0, dist_zero_right, dist_zero_right] at hd
    simpa only [mem_closedBall, dist_zero_right, hd] using hb
  obtain ⟨z, hz, hs, hsmass⟩ := exists_subexponential_compact_sections_sequence scale hscale n k R hR hRupper
    K' hK' (fun r v hv => (norm_snd_le v).trans (hbound r v hv))
    (fun r => by rw [hK'mass]; exact hKpos r)
    (by simpa only [hK'mass] using hKlower)
  have himage := subexponential_compact_image_sequence scale hscale n
    (fun r v => f r (Fin.append v (z r))) (fun r v => df r v (z r))
    R L η (fun r => (hR r).trans' zero_le_one) hL hη hRupper hLupper hηlower
    (fun r => hf r (z r) (hz r)) (fun r => hdf r (z r) (hz r))
    (fun r => hosc r (z r) (hz r))
    (fun r => {v | (v, z r) ∈ K' r}) hs (fun r v hv => by
      refine ⟨(norm_fst_le (v, z r)).trans (hbound r (v, z r) hv), ?_⟩
      rw [← hminor]
      exact hgood r _ hv) hsmass
  refine ⟨fun r => (fun v => f r (Fin.append v (z r))) '' {v | (v, z r) ∈ K' r},
    himage.1, ?_, himage.2⟩
  intro r y hy
  obtain ⟨v, hv, rfl⟩ := hy
  exact ⟨Fin.append v (z r), hKE r hv, rfl⟩

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_GrowingPolynomialImage
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial image volume on subexponentially growing cubes -/

noncomputable section
namespace PolycyclicRecognition

open Set Metric MeasureTheory Filter
open scoped Topology

theorem compact_polynomial_family_image_growing_sequence
    {P : Type} [TopologicalSpace P]
    (scale : ℕ → ℝ) (hscale : Tendsto scale atTop atTop)
    (rem : RemezPolynomialInput) (n k : ℕ) (hn : 1 ≤ n)
    (f : P × (Fin (n + k) → ℝ) → (Fin n → ℝ)) (hf : Continuous f)
    (hpoly : HasPolynomialCoordinates (fun a x => f (a, x)))
    (S : Set P) (hS : IsCompact S) (b : ℕ → P) (hb : ∀ r, b r ∈ S)
    (R : ℕ → ℝ) (hR : ∀ r, 1 ≤ R r) (hRupper : HasSubexponentialUpperBoundSeq scale R)
    (c : ℝ) (hc : 0 < c) (v₀ : Fin n → ℝ) (z₀ : Fin k → ℝ)
    (hanchor : ∀ r, Fin.append v₀ z₀ ∈ closedBall 0 (R r))
    (hdet : ∀ a ∈ S, c ≤ |(fderiv ℝ (fun v => f (a, Fin.append v z₀)) v₀).det|)
    (E : ℕ → Set (Fin (n + k) → ℝ)) (hE : ∀ r, MeasurableSet (E r))
    (hER : ∀ r, E r ⊆ closedBall 0 (R r))
    (hm : ∀ r, 0 < (volume (E r)).toReal)
    (hmlower : HasSubexponentialLowerBoundSeq scale (fun r => (volume (E r)).toReal)) :
    ∃ C : ℕ → Set (Fin n → ℝ),
      (∀ r, IsCompact (C r)) ∧ (∀ r, C r ⊆ (fun x => f (b r, x)) '' E r) ∧
      HasSubexponentialLowerBoundSeq scale (fun r => (volume (C r)).toReal) := by
  obtain ⟨D, p, hp, hvalue⟩ := hpoly.exists_uniform_polynomials
  have heval (i : Fin n) (x : Fin (n + k) → ℝ) :
      Continuous (fun a => MvPolynomial.eval x (p a i)) := by
    have harg : Continuous (fun a : P => (a, x)) := continuous_id.prodMk continuous_const
    have h : Continuous (fun a : P => f (a, x) i) := (continuous_apply i).comp (hf.comp harg)
    simpa only [hvalue] using h
  obtain ⟨A, hA, hbounds⟩ := uniform_polynomial_slice_derivative_bounds p D hp heval S hS
  let L := fun r => A * (R r + 3) ^ ((n + k) * D)
  have hL (r : ℕ) : 1 ≤ L r := by
    have hpow : 1 ≤ (R r + 3) ^ ((n + k) * D) := one_le_pow₀ (by linarith [hR r])
    exact one_le_mul_of_one_le_of_one_le hA hpow
  have hRadd : HasSubexponentialUpperBoundSeq scale (fun r => R r + 3) :=
    hRupper.add (sequence_subexponential_upper_const hscale 3) hscale
  have hLupper : HasSubexponentialUpperBoundSeq scale L :=
    (sequence_subexponential_upper_const hscale A).mul
      (hRadd.pow hscale (Eventually.of_forall (fun r => by linarith [hR r])) _)
      (Eventually.of_forall (fun _ => hA.trans' zero_le_one))
  let df := fun r v z => fderiv ℝ (fun w => f (b r, Fin.append w z)) v
  have hdfpoly (a : P) (v : Fin n → ℝ) (z : Fin k → ℝ) :
      fderiv ℝ (fun w => f (a, Fin.append w z)) v = polynomialSliceDifferential (p a) v z := by
    have he : (fun w i => MvPolynomial.eval (Fin.append w z) (p a i)) =
        (fun w => f (a, Fin.append w z)) := by
      funext w i
      exact hvalue a (Fin.append w z) i
    have h := hasFDerivAt_polynomialSlice (p a) v z
    rw [he] at h
    exact h.fderiv
  have hminor (r : ℕ) (v : Fin n → ℝ) (z : Fin k → ℝ) :
      MvPolynomial.eval (Fin.append v z) (polynomialJacobianMinor (p (b r))) = (df r v z).det := by
    rw [eval_polynomialJacobianMinor, ← hdfpoly]
  have hder (r : ℕ) (v : Fin n → ℝ) (z : Fin k → ℝ) :
      HasFDerivAt (fun w => f (b r, Fin.append w z)) (df r v z) v := by
    rw [show df r v z = polynomialSliceDifferential (p (b r)) v z from hdfpoly _ _ _]
    convert hasFDerivAt_polynomialSlice (p (b r)) v z using 1
    all_goals try with_reducible_and_instances rfl
    funext w i
    exact (hvalue (b r) (Fin.append w z) i).symm
  apply exists_subexponential_polynomial_image_sequence scale hscale rem n k (max 1 (n * (D - 1)))
    hn (le_max_left _ _) (fun r x => f (b r, x)) df
    (fun r => polynomialJacobianMinor (p (b r)))
    (fun r => (totalDegree_polynomialJacobianMinor_le _ (hp (b r))).trans (le_max_right _ _))
    hminor R L (fun _ => c) hR hL (fun _ => hc) hRupper hLupper
    (sequence_subexponential_lower_const hscale hc)
    (fun r z _ v _ => hder r v z) (fun r z hz v hv => ?_)
    (fun r z hz v w hv hw => ?_) (fun _ => Fin.append v₀ z₀) hanchor
    (fun r => by rw [hminor]; exact hdet (b r) (hb r)) E hE hER hm hmlower
  · change ‖fderiv ℝ (fun w => f (b r, Fin.append w z)) v‖ ≤ L r
    rw [hdfpoly]
    have h := (hbounds (b r) (hb r) (R r + 2) (by linarith [hR r])).1 v z hv (by linarith)
    simpa only [L, show 1 + (R r + 2) = R r + 3 by ring] using h
  · change ‖fderiv ℝ (fun u => f (b r, Fin.append u z)) v -
      fderiv ℝ (fun u => f (b r, Fin.append u z)) w‖ ≤ L r * dist v w
    rw [hdfpoly, hdfpoly]
    have h := (hbounds (b r) (hb r) (R r + 2) (by linarith [hR r])).2 v w z hv hw (by linarith)
    simpa only [L, show 1 + (R r + 2) = R r + 3 by ring] using h

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_GrowingConvergingPolynomialImage
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Converging polynomial image volume on growing cubes -/

noncomputable section

namespace PolycyclicRecognition

open Set Metric MeasureTheory Filter
open scoped Topology

theorem converging_polynomial_family_image_growing_sequence
    {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (scale : ℕ → ℝ) (hscale : Tendsto scale atTop atTop)
    (rem : RemezPolynomialInput) (n k : ℕ) (hn : 1 ≤ n)
    (f : P × (Fin (n + k) → ℝ) → (Fin n → ℝ))
    (hf : ContDiff ℝ 2 f)
    (hpoly : HasPolynomialCoordinates (fun a x => f (a, x)))
    (S : Set P) (hS : IsCompact S) (b : ℕ → P) (hb : ∀ r, b r ∈ S)
    (b₀ : P) (hb₀ : b₀ ∈ S) (hlim : Tendsto b atTop (𝓝 b₀))
    (R : ℕ → ℝ) (hR : ∀ r, 1 ≤ R r)
    (hRupper : HasSubexponentialUpperBoundSeq scale R)
    (v₀ : Fin n → ℝ) (z₀ : Fin k → ℝ)
    (hanchor : ∀ r, Fin.append v₀ z₀ ∈ closedBall 0 (R r))
    (hdet : (fderiv ℝ (fun v => f (b₀, Fin.append v z₀)) v₀).det ≠ 0)
    (E : ℕ → Set (Fin (n + k) → ℝ)) (hE : ∀ r, MeasurableSet (E r))
    (hER : ∀ r, E r ⊆ closedBall 0 (R r))
    (hm : ∀ r, 0 < (volume (E r)).toReal)
    (hmlower : HasSubexponentialLowerBoundSeq scale (fun r => (volume (E r)).toReal)) :
    ∃ C : ℕ → Set (Fin n → ℝ),
      (∀ r, IsCompact (C r)) ∧
      (∀ᶠ r in atTop, C r ⊆ (fun x => f (b r, x)) '' E r) ∧
      HasSubexponentialLowerBoundSeq scale (fun r => (volume (C r)).toReal) := by
  classical
  let d := fun a => fderiv ℝ (fun v => f (a, Fin.append v z₀)) v₀
  have hd : Continuous d := by
    have hg : ContDiff ℝ 2 (fun p : P × (Fin n → ℝ) => f (p.1, Fin.append p.2 z₀)) :=
      hf.comp (contDiff_fst.prodMk
        ((contDiff_finAppend n k).comp (contDiff_snd.prodMk contDiff_const)))
    have hh : ContDiff ℝ 1 d := ContDiff.fderiv hg (contDiff_const (c := v₀)) (by norm_num)
    exact hh.continuous
  let D := fun a => |(d a).det|
  have hD : Continuous D := (continuous_det_clm hd).abs
  have hDpos : 0 < D b₀ := abs_pos.mpr hdet
  let c := D b₀ / 2
  have hc : 0 < c := half_pos hDpos
  let T := S ∩ {a | c ≤ D a}
  have hT : IsCompact T := hS.inter_right (isClosed_le continuous_const hD)
  have hb₀T : b₀ ∈ T := ⟨hb₀, (half_le_self hDpos.le)⟩
  have hlate : ∀ᶠ r in atTop, b r ∈ T := by
    have hh := (hD.continuousAt.tendsto.comp hlim).eventually
      (Ioi_mem_nhds (show c < D b₀ from half_lt_self hDpos))
    filter_upwards [hh] with r hr
    exact ⟨hb r, hr.le⟩
  let b' := fun r => if b r ∈ T then b r else b₀
  have hb' : ∀ r, b' r ∈ T := by
    intro r
    dsimp [b']
    split_ifs with h
    · exact h
    · exact hb₀T
  obtain ⟨C, hC, hCE, hClower⟩ := compact_polynomial_family_image_growing_sequence
    scale hscale rem n k hn f hf.continuous hpoly T hT b' hb' R hR hRupper c hc v₀ z₀ hanchor
    (fun a ha => ha.2) E hE hER hm hmlower
  refine ⟨C, hC, ?_, hClower⟩
  filter_upwards [hlate] with r hr
  simpa only [b', ite_eq_left hr] using hCE r

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_GrowingSubmersivePolynomialImage
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_countable _root_.OAI.PolycyclicRecognition.finitelyGeneratedSubgroupIndex_countable _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Submersive polynomial images on growing input cubes -/

noncomputable section

namespace PolycyclicRecognition

open Set Metric MeasureTheory Filter
open scoped Topology

theorem converging_submersive_polynomial_image_growing_sequence
    {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] {m n : ℕ}
    (scale : ℕ → ℝ) (hscale : Tendsto scale atTop atTop)
    (rem : RemezPolynomialInput) (hn : 1 ≤ n)
    (f : P × (Fin m → ℝ) → (Fin n → ℝ)) (hf : ContDiff ℝ 2 f)
    (hpoly : HasPolynomialCoordinates (fun a x => f (a, x)))
    (S : Set P) (hS : IsCompact S) (b : ℕ → P) (hb : ∀ r, b r ∈ S)
    (b₀ : P) (hb₀ : b₀ ∈ S) (hlim : Tendsto b atTop (𝓝 b₀))
    (R : ℕ → ℝ) (hR : ∀ r, 1 ≤ R r)
    (hRupper : HasSubexponentialUpperBoundSeq scale R)
    (t₀ : Fin m → ℝ) (ht₀ : ∀ r, ‖t₀‖ ≤ R r)
    (hs : Function.Surjective (fderiv ℝ (fun x => f (b₀, x)) t₀))
    (E : ℕ → Set (Fin m → ℝ)) (hE : ∀ r, MeasurableSet (E r))
    (hER : ∀ r, E r ⊆ closedBall 0 (R r))
    (hm : ∀ r, 0 < (volume (E r)).toReal)
    (hmlower : HasSubexponentialLowerBoundSeq scale (fun r => (volume (E r)).toReal)) :
    ∃ C : ℕ → Set (Fin n → ℝ),
      (∀ r, IsCompact (C r)) ∧
      (∀ᶠ r in atTop, C r ⊆ (fun x => f (b r, x)) '' E r) ∧
      HasSubexponentialLowerBoundSeq scale (fun r => (volume (C r)).toReal) := by
  classical
  obtain ⟨j, hj, hminor⟩ := exists_nonsingular_column_minor
    (fderiv ℝ (fun x => f (b₀, x)) t₀).toLinearMap hs
  obtain ⟨k, e, he⟩ := exists_fin_equiv_extending_injection j hj
  let u₀ := reindexParameters e.symm t₀
  let v₀ := fun i : Fin n => u₀ (Fin.castAdd k i)
  let z₀ := fun i : Fin k => u₀ (Fin.natAdd n i)
  have hu : Fin.append v₀ z₀ = u₀ := by
    ext i
    refine Fin.addCases ?_ ?_ i <;> intro i <;> simp [v₀, z₀]
  have hback : reindexParameters e (Fin.append v₀ z₀) = t₀ := by
    rw [hu]
    ext i
    simp [u₀]
  let g := fun p : P × (Fin (n + k) → ℝ) => f (p.1, reindexParameters e p.2)
  have hg : ContDiff ℝ 2 g :=
    hf.comp (contDiff_fst.prodMk ((reindexParameters e).contDiff.comp contDiff_snd))
  have hgpoly : HasPolynomialCoordinates (fun a x => g (a, x)) :=
    fun i => (hpoly i).reindex e
  have hd : (fderiv ℝ (fun v => g (b₀, Fin.append v z₀)) v₀).det ≠ 0 := by
    have hfd : DifferentiableAt ℝ (fun x => f (b₀, x))
        (reindexParameters e (Fin.append v₀ z₀)) := by
      rw [hback]
      exact ((hf.comp (contDiff_const.prodMk contDiff_id)).differentiable (by norm_num)).differentiableAt
    rw [show (fun v => g (b₀, Fin.append v z₀)) =
      (fun v => f (b₀, reindexParameters e (Fin.append v z₀))) from rfl,
      det_reindexed_slice e (fun x => f (b₀, x)) v₀ z₀ hfd, hback]
    simpa only [he, ContinuousLinearMap.coe_coe] using hminor
  let E' := fun r => reindexParameters e ⁻¹' E r
  have hE' : ∀ r, MeasurableSet (E' r) :=
    fun r => (hE r).preimage (reindexParameters e).continuous.measurable
  have hvol (r : ℕ) : volume (E' r) = volume (E r) :=
    (measurePreserving_reindexParameters e).measure_preimage (hE r).nullMeasurableSet
  have hER' (r : ℕ) : E' r ⊆ closedBall 0 (R r) := by
    intro x hx
    have hh := hER r hx
    simpa only [mem_closedBall, dist_zero_right, reindexParameters_norm] using hh
  have hanchor (r : ℕ) : Fin.append v₀ z₀ ∈ closedBall 0 (R r) := by
    rw [hu, mem_closedBall, dist_zero_right, reindexParameters_norm]
    exact ht₀ r
  obtain ⟨C, hC, hCE, hClower⟩ := converging_polynomial_family_image_growing_sequence
    scale hscale rem n k hn g hg hgpoly S hS b hb b₀ hb₀ hlim R hR hRupper v₀ z₀ hanchor hd
    E' hE' hER' (fun r => by rw [hvol]; exact hm r) (by simpa only [hvol] using hmlower)
  refine ⟨C, hC, ?_, hClower⟩
  filter_upwards [hCE] with r hr
  rintro y hy
  obtain ⟨x, hx, rfl⟩ := hr hy
  exact ⟨reindexParameters e x, hx, rfl⟩

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_GrowingEventualPolynomialImage
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Growing-cube image volume for successful measurable parameters -/

noncomputable section

namespace PolycyclicRecognition

open Set Metric MeasureTheory Filter
open scoped Topology ENNReal NNReal

theorem converging_submersive_polynomial_image_growing_eventual_sequence
    {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] {m n : ℕ}
    (scale : ℕ → ℝ) (hscale : Tendsto scale atTop atTop)
    (rem : RemezPolynomialInput) (hn : 1 ≤ n)
    (f : P × (Fin m → ℝ) → (Fin n → ℝ)) (hf : ContDiff ℝ 2 f)
    (hpoly : HasPolynomialCoordinates (fun a x => f (a, x)))
    (S : Set P) (hS : IsCompact S) (b : ℕ → P) (hb : ∀ r, b r ∈ S)
    (b₀ : P) (hb₀ : b₀ ∈ S) (hlim : Tendsto b atTop (𝓝 b₀))
    (R : ℕ → ℝ) (hR : ∀ r, 1 ≤ R r)
    (hRupper : HasSubexponentialUpperBoundSeq scale R)
    (t₀ : Fin m → ℝ) (ht₀ : ∀ r, ‖t₀‖ ≤ R r)
    (hs : Function.Surjective (fderiv ℝ (fun x => f (b₀, x)) t₀))
    (E : ℕ → Set (Fin m → ℝ)) (hE : ∀ r, MeasurableSet (E r))
    (hER : ∀ r, E r ⊆ closedBall 0 (R r))
    (hmlower : HasSubexponentialLowerBoundSeq scale (fun r => (volume (E r)).toReal)) :
    ∃ C : ℕ → Set (Fin n → ℝ),
      (∀ r, IsCompact (C r)) ∧
      (∀ᶠ r in atTop, C r ⊆ (fun x => f (b r, x)) '' E r) ∧
      HasSubexponentialLowerBoundSeq scale (fun r => (volume (C r)).toReal) := by
  obtain ⟨E', hE', hER', hm', hlower', heq⟩ :=
    exists_positive_parameter_sets_growing_sequence R scale
      (fun r => lt_of_lt_of_le zero_lt_one (hR r)) E hE hER hmlower
  obtain ⟨C, hC, hCE, hlower⟩ := converging_submersive_polynomial_image_growing_sequence
    scale hscale rem hn f hf hpoly S hS b hb b₀ hb₀ hlim R hR hRupper t₀ ht₀ hs E' hE' hER' hm' hlower'
  refine ⟨C, hC, ?_, hlower⟩
  filter_upwards [hCE, heq] with r hr he
  simpa only [he] using hr

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_BundleWordImage
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Correlated successful parameters for the joint source-bundle map -/

noncomputable section
namespace PolycyclicRecognition

open Set Metric MeasureTheory Filter
open scoped Topology

theorem bundle_word_image_sequence {I : Type} [Fintype I] {n m h c M N : ℕ}
    (scale : ℕ → ℝ) (hscale : Tendsto scale atTop atTop)
    (rem : RemezPolynomialInput) (hN : 1 ≤ N)
    (a : DynkinCoefficients c 2) (letters : Fin m → I)
    (input : (Fin M → ℝ) ≃L[ℝ] (Fin h → Fin (m + m) → ℝ))
    (output : (Fin N → ℝ) ≃L[ℝ] (Fin h → Fin n → ℝ))
    (p : ℕ → WordLawData I n) (p₀ : WordLawData I n) (hlim : Tendsto p atTop (𝓝 p₀))
    (t₀ : Fin (m + m) → ℝ)
    (hs : Function.Surjective (fderiv ℝ (differenceAmplitudeWordEndpoint a letters p₀) t₀))
    (R : ℕ → ℝ) (hR : ∀ r, 1 ≤ R r) (hRupper : HasSubexponentialUpperBoundSeq scale R)
    (hanchor : ∀ r, ‖input.symm (fun _ => t₀)‖ ≤ R r)
    (A : ℕ → Set (Fin M → ℝ)) (hA : ∀ r, MeasurableSet (A r))
    (hAR : ∀ r, A r ⊆ closedBall 0 (R r))
    (hAlower : HasSubexponentialLowerBoundSeq scale (fun r => (volume (A r)).toReal)) :
    ∃ C : ℕ → Set (Fin N → ℝ), (∀ r, IsCompact (C r)) ∧
      (∀ᶠ r in atTop, C r ⊆ bundleWordEndpoint a letters input output (p r) '' A r) ∧
      HasSubexponentialLowerBoundSeq scale (fun r => (volume (C r)).toReal) := by
  exact converging_submersive_polynomial_image_growing_eventual_sequence scale hscale rem hN
    (fun z => bundleWordEndpoint a letters input output z.1 z.2)
    (contDiff_bundleWordEndpoint a letters input output)
    (hasPolynomialCoordinates_bundleWordEndpoint a letters input output)
    (insert p₀ (range p)) hlim.isCompact_insert_range p
    (fun r => mem_insert_of_mem _ (mem_range_self r)) p₀ (mem_insert _ _) hlim R hR hRupper
    (input.symm (fun _ => t₀)) hanchor
    (bundleWordEndpoint_submersive a letters input output p₀ t₀ hs) A hA hAR hAlower

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_HaarPrefixCoordinates
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.sourceBundleStateEquiv_apply _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Product Haar measure in increment and endpoint coordinates

The change `(u₁, …, uₕ) ↦ (u₁, u₁u₂, …, u₁⋯uₕ)` preserves product
Haar measure. Its inverse is the successive-difference map used in the
endpoint-tuple volume argument.
-/

noncomputable section
namespace PolycyclicRecognition

open MeasureTheory

variable {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]

theorem prefixCoordinateEquiv_zero (n : ℕ) (u : Fin (n + 1) → G) :
    prefixCoordinateEquiv (n + 1) u 0 = u 0 := by
  simp [prefixCoordinateEquiv, prefixShear]
  rfl

theorem prefixCoordinateEquiv_succ (n : ℕ) (u : Fin (n + 1) → G) (i : Fin n) :
    prefixCoordinateEquiv (n + 1) u i.succ =
      u 0 * prefixCoordinateEquiv n (fun j => u j.succ) i := by
  simp [prefixCoordinateEquiv, prefixShear]
  rfl

theorem measurePreserving_prefixCoordinateEquiv (μ : Measure G)
    [SigmaFinite μ] [μ.IsMulLeftInvariant] (n : ℕ) :
    MeasurePreserving (prefixCoordinateEquiv n) (Measure.pi fun _ => μ) (Measure.pi fun _ => μ) := by
  induction n with
  | zero => exact MeasurePreserving.id _
  | succ n ih =>
    let split := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => G) 0
    have hs : MeasurePreserving split (Measure.pi fun _ => μ)
        (μ.prod (Measure.pi fun _ : Fin n => μ)) := measurePreserving_piFinSuccAbove _ 0
    have ht := (MeasurePreserving.id μ).prod ih
    have hu : MeasurePreserving (prefixShear n)
        (μ.prod (Measure.pi fun _ : Fin n => μ))
        (μ.prod (Measure.pi fun _ : Fin n => μ)) := by
      change MeasurePreserving (fun p : G × (Fin n → G) => (p.1, fun i => p.1 * p.2 i))
        (μ.prod (Measure.pi fun _ : Fin n => μ)) (μ.prod (Measure.pi fun _ : Fin n => μ))
      apply MeasurePreserving.skew_product (g := fun (g : G) (p : Fin n → G) => fun i => g * p i)
        (MeasurePreserving.id μ)
      · exact measurable_pi_iff.mpr (fun i =>
          measurable_fst.mul ((measurable_pi_apply i).comp measurable_snd))
      · exact Filter.Eventually.of_forall (fun g =>
          map_mul_left_eq_self (Measure.pi fun _ : Fin n => μ) (fun _ => g))
    exact hs.symm.comp (hu.comp (ht.comp hs))

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_SourceBundleStates
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Passing bundle products to conjugated successive source states -/

noncomputable section
namespace PolycyclicRecognition

open MeasureTheory Set

variable {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]

theorem measurePreserving_sourceBundleStateEquiv (μ : Measure G)
    [SigmaFinite μ] [μ.IsMulLeftInvariant]
    (h : ℕ) (x : G) (φ : Fin h → G ≃ᵐ G)
    (hφ : ∀ i, MeasurePreserving (φ i) μ μ) :
    MeasurePreserving (sourceBundleStateEquiv h x φ)
      (Measure.pi fun _ => μ) (Measure.pi fun _ => μ) :=
  (measurePreserving_mul_left (Measure.pi fun _ : Fin h => μ) (fun _ => x)).comp
    ((measurePreserving_prefixCoordinateEquiv μ h).comp
      (measurePreserving_pi (fun _ => μ) (fun _ => μ) hφ))

theorem sourceBundleStateEquiv_image_measure (μ : Measure G)
    [SigmaFinite μ] [μ.IsMulLeftInvariant]
    (h : ℕ) (x : G) (φ : Fin h → G ≃ᵐ G)
    (hφ : ∀ i, MeasurePreserving (φ i) μ μ) (S : Set (Fin h → G)) :
    (Measure.pi fun _ : Fin h => μ) (sourceBundleStateEquiv h x φ '' S) =
      (Measure.pi fun _ : Fin h => μ) S := by
  let e := sourceBundleStateEquiv h x φ
  have he := (measurePreserving_sourceBundleStateEquiv μ h x φ hφ).map_eq
  have hv := congrArg (fun ν : Measure (Fin h → G) => ν (e '' S)) he
  rw [e.measurableEmbedding.map_apply, Set.preimage_image_eq _ e.injective] at hv
  exact hv.symm

theorem continuous_prefixCoordinateEquiv [TopologicalSpace G] [IsTopologicalGroup G]
    (h : ℕ) : Continuous (prefixCoordinateEquiv (G := G) h) := by
  induction h with
  | zero => exact continuous_id
  | succ h ih =>
    apply continuous_pi
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa only [prefixCoordinateEquiv_zero] using (continuous_apply (0 : Fin (h + 1)))
    · have he : (fun u : Fin (h + 1) → G => prefixCoordinateEquiv (h + 1) u j.succ) =
          (fun u => u 0 * prefixCoordinateEquiv h (fun k => u k.succ) j) := by
        funext u
        exact prefixCoordinateEquiv_succ h u j
      rw [he]
      exact (continuous_apply 0).mul ((continuous_apply j).comp
        (ih.comp (continuous_pi (fun k => continuous_apply k.succ))))

theorem continuous_sourceBundleStateEquiv [TopologicalSpace G] [IsTopologicalGroup G]
    (h : ℕ) (x : G) (φ : Fin h → G ≃ᵐ G) (hφ : ∀ i, Continuous (φ i)) :
    Continuous (sourceBundleStateEquiv h x φ) := by
  have hC : Continuous (fun u : Fin h → G => fun i => φ i (u i)) :=
    continuous_pi (fun i => (hφ i).comp (continuous_apply i))
  have hP := (continuous_prefixCoordinateEquiv h).comp hC
  exact continuous_pi (fun i => continuous_const.mul ((continuous_apply i).comp hP))

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_IndependentSwitchParameters
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The measurable event of successful independent switch parameters -/

noncomputable section

namespace PolycyclicRecognition

open MeasureTheory Set
open scoped ENNReal

universe u

variable {G : Type} [Group G] [MeasurableSpace G]

theorem measurableSet_switchSuccessful [MeasurableMul₂ G] [MeasurableInv G]
    (S : ℕ → Set G) (hS : ∀ j, MeasurableSet (S j)) (n k : ℕ) :
    MeasurableSet {p : G × SwitchParameters G k | SwitchSuccessful S n k p.1 p.2} := by
  induction k generalizing n with
  | zero => exact MeasurableSet.univ
  | succ k ih =>
    have hm : Measurable (fun p : G × SwitchParameters G (k + 1) =>
        p.1 * p.2.1 * p.2.2.1⁻¹) :=
      (measurable_fst.mul measurable_snd.fst).mul measurable_snd.snd.fst.inv
    exact (hS (n + 1) |>.preimage hm).inter
      ((ih (n + 1)).preimage (hm.prodMk measurable_snd.snd.snd))

theorem measurableSet_switchSuccessful_fixed [MeasurableMul₂ G] [MeasurableInv G]
    (S : ℕ → Set G) (hS : ∀ j, MeasurableSet (S j)) (n k : ℕ) (x : G) :
    MeasurableSet {p : SwitchParameters G k | SwitchSuccessful S n k x p} :=
  (measurableSet_switchSuccessful S hS n k).preimage (measurable_const.prodMk measurable_id)

/-- The recursive survival integral equals the probability of the actual
measurable successful-parameter event under the independent product law. -/
theorem switchParameterLaw_success [MeasurableMul₂ G] [MeasurableInv G]
    (σ : ℕ → Measure G) [∀ j, IsProbabilityMeasure (σ j)]
    (S : ℕ → Set G) (hS : ∀ j, MeasurableSet (S j)) (n k : ℕ) (x : G) :
    switchParameterLaw σ n k {p | SwitchSuccessful S n k x p} =
      survivingSwitchProbability σ S n k x := by
  induction k generalizing n x with
  | zero =>
    change (Measure.dirac PUnit.unit) univ = 1
    exact Measure.dirac_apply_of_mem (Set.mem_univ _)
  | succ k ih =>
    rw [← lintegral_indicator_one (measurableSet_switchSuccessful_fixed S hS n (k + 1) x)]
    let f : SwitchParameters G (k + 1) → ℝ≥0∞ :=
      {p | SwitchSuccessful S n (k + 1) x p}.indicator (fun _ => 1)
    have hf : Measurable f := measurable_const.indicator
      (measurableSet_switchSuccessful_fixed S hS n (k + 1) x)
    change (∫⁻ p, f p ∂(σ n).prod ((σ n).prod (switchParameterLaw σ (n + 1) k))) = _
    rw [lintegral_prod f hf.aemeasurable]
    change (∫⁻ s₁, ∫⁻ p, f (s₁, p) ∂(σ n).prod (switchParameterLaw σ (n + 1) k) ∂σ n) = _
    apply lintegral_congr
    intro s₁
    have hf₁ : Measurable (fun p : G × SwitchParameters G k => f (s₁, p)) :=
      hf.comp (measurable_const.prodMk measurable_id)
    rw [lintegral_prod (fun p : G × SwitchParameters G k => f (s₁, p)) hf₁.aemeasurable]
    apply lintegral_congr
    intro s₂
    by_cases hy : x * s₁ * s₂⁻¹ ∈ S (n + 1)
    · have he : (fun p => f (s₁, s₂, p)) =
          {p | SwitchSuccessful S (n + 1) k (x * s₁ * s₂⁻¹) p}.indicator (fun _ => 1) := by
        funext p
        change {q | SwitchSuccessful S n (k + 1) x q}.indicator (fun _ => (1 : ℝ≥0∞))
          (s₁, s₂, p) =
            {q | SwitchSuccessful S (n + 1) k (x * s₁ * s₂⁻¹) q}.indicator (fun _ => 1) p
        by_cases hp : SwitchSuccessful S (n + 1) k (x * s₁ * s₂⁻¹) p
        · rw [indicator_of_mem (s := {q : SwitchParameters G (k + 1) |
              SwitchSuccessful S n (k + 1) x q}) (show SwitchSuccessful S n (k + 1) x (s₁, s₂, p) from
            ⟨hy, hp⟩), indicator_of_mem (s := {q : SwitchParameters G k |
              SwitchSuccessful S (n + 1) k (x * s₁ * s₂⁻¹) q}) hp]
        · have hn : ¬ SwitchSuccessful S n (k + 1) x (s₁, s₂, p) := fun h => hp h.2
          rw [indicator_of_notMem (s := {q : SwitchParameters G (k + 1) |
              SwitchSuccessful S n (k + 1) x q}) hn,
            indicator_of_notMem (s := {q : SwitchParameters G k |
              SwitchSuccessful S (n + 1) k (x * s₁ * s₂⁻¹) q}) hp]
      rw [he]
      change (∫⁻ p, {p | SwitchSuccessful S (n + 1) k (x * s₁ * s₂⁻¹) p}.indicator 1 p
        ∂switchParameterLaw σ (n + 1) k) = _
      rw [lintegral_indicator_one
        (measurableSet_switchSuccessful_fixed S hS (n + 1) k (x * s₁ * s₂⁻¹)), ih]
      exact (indicator_of_mem hy _).symm
    · have he : (fun p => f (s₁, s₂, p)) = fun _ => 0 := by
        funext p
        simp only [f, SwitchSuccessful, hy, false_and, mem_ofPred_eq,
          not_false_eq_true, indicator_of_notMem]
      rw [he, lintegral_zero]
      exact (indicator_of_notMem hy _).symm

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_FiniteSwitchEvents
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Successful switch events only use the prescribed finite list of sheets -/

noncomputable section

namespace PolycyclicRecognition

open MeasureTheory Set

variable {G : Type} [Group G] [MeasurableSpace G]

omit [MeasurableSpace G] in
theorem switchSuccessful_mono (S R : ℕ → Set G) (n k : ℕ)
    (hsub : ∀ j, n < j → j ≤ n + k → S j ⊆ R j)
    (x : G) (p : SwitchParameters G k)
    (hp : SwitchSuccessful S n k x p) : SwitchSuccessful R n k x p := by
  induction k generalizing n x with
  | zero => trivial
  | succ k ih =>
    exact ⟨hsub (n + 1) (by omega) (by omega) hp.1,
      ih (n + 1) (fun j hj hj' => hsub j (by omega) (by omega)) _ p.2.2 hp.2⟩

omit [MeasurableSpace G] in
theorem switchSuccessful_congr (S R : ℕ → Set G) (n k : ℕ)
    (heq : ∀ j, n < j → j ≤ n + k → S j = R j)
    (x : G) (p : SwitchParameters G k) :
    SwitchSuccessful S n k x p ↔ SwitchSuccessful R n k x p := by
  induction k generalizing n x with
  | zero => rfl
  | succ k ih =>
    change (_ ∈ S (n + 1) ∧ _) ↔ (_ ∈ R (n + 1) ∧ _)
    rw [heq (n + 1) (by omega) (by omega)]
    exact and_congr_right (fun _ => ih (n + 1)
      (fun j hj hj' => heq j (by omega) (by omega)) _ p.2.2)

theorem survivingSwitchProbability_congr (σ : ℕ → Measure G)
    (S R : ℕ → Set G) (n k : ℕ)
    (heq : ∀ j, n < j → j ≤ n + k → S j = R j) (x : G) :
    survivingSwitchProbability σ S n k x = survivingSwitchProbability σ R n k x := by
  induction k generalizing n x with
  | zero => rfl
  | succ k ih =>
    simp only [survivingSwitchProbability]
    apply lintegral_congr
    intro s₁
    apply lintegral_congr
    intro s₂
    rw [heq (n + 1) (by omega) (by omega)]
    exact congrFun (indicator_congr (fun y _ =>
      ih (n + 1) (fun j hj hj' => heq j (by omega) (by omega)) y)) _

/-- No measurability conditions on unused sheets are needed. -/
theorem switchParameterLaw_success_finite [MeasurableMul₂ G] [MeasurableInv G]
    (σ : ℕ → Measure G) [∀ j, IsProbabilityMeasure (σ j)]
    (S : ℕ → Set G) (n k : ℕ)
    (hS : ∀ j, n < j → j ≤ n + k → MeasurableSet (S j)) (x : G) :
    MeasurableSet {p : SwitchParameters G k | SwitchSuccessful S n k x p} ∧
      switchParameterLaw σ n k {p | SwitchSuccessful S n k x p} =
        survivingSwitchProbability σ S n k x := by
  let R := fun j => if n < j ∧ j ≤ n + k then S j else ∅
  have hR (j : ℕ) : MeasurableSet (R j) := by
    by_cases hj : n < j ∧ j ≤ n + k
    · simpa [R, hj] using hS j hj.1 hj.2
    · simp [R, hj]
  have heq (j : ℕ) (hj : n < j) (hj' : j ≤ n + k) : S j = R j := by
    simp [R, hj, hj']
  have hsets : {p : SwitchParameters G k | SwitchSuccessful S n k x p} =
      {p | SwitchSuccessful R n k x p} := by
    ext p
    exact switchSuccessful_congr S R n k heq x p
  constructor
  · exact hsets.symm ▸ measurableSet_switchSuccessful_fixed R hR n k x
  · calc
      _ = switchParameterLaw σ n k {p | SwitchSuccessful R n k x p} :=
        congrArg (switchParameterLaw σ n k) hsets
      _ = survivingSwitchProbability σ R n k x := switchParameterLaw_success σ R hR n k x
      _ = _ := (survivingSwitchProbability_congr σ S R n k heq x).symm

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_SwitchParameterPullback
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Pulling the successful event back to the original independent samples -/

noncomputable section

namespace PolycyclicRecognition

open MeasureTheory Set

theorem measurePreserving_mapSwitchParameters {A B : Type}
    [MeasurableSpace A] [MeasurableSpace B]
    (f : ℕ → A → B) (τ : ℕ → Measure A) (σ : ℕ → Measure B)
    [∀ j, IsProbabilityMeasure (τ j)] [∀ j, IsProbabilityMeasure (σ j)]
    (hf : ∀ j, MeasurePreserving (f j) (τ j) (σ j)) (n k : ℕ) :
    MeasurePreserving (mapSwitchParameters f n k)
      (switchParameterLaw τ n k) (switchParameterLaw σ n k) := by
  induction k generalizing n with
  | zero =>
    refine ⟨measurable_const, ?_⟩
    simp [mapSwitchParameters, switchParameterLaw]
  | succ k ih => exact (hf n).prod ((hf n).prod (ih (n + 1)))

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_VectorSwitchParameters
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite vectors of independent pairs and the recursive switch law -/

noncomputable section

namespace PolycyclicRecognition

open MeasureTheory

theorem measurePreserving_vectorSwitchParameters {A : Type} [MeasurableSpace A]
    (τ : Measure A) [IsProbabilityMeasure τ] (n k : ℕ) :
    MeasurePreserving (vectorSwitchParameters (A := A) k)
      (Measure.pi (fun _ : Fin k => τ.prod τ)) (switchParameterLaw (fun _ => τ) n k) := by
  induction k generalizing n with
  | zero =>
    refine ⟨measurable_const, ?_⟩
    simp [vectorSwitchParameters, switchParameterLaw]
  | succ k ih =>
    have hhead := measurePreserving_piFinSuccAbove (fun _ : Fin (k + 1) => τ.prod τ) 0
    have htail := (MeasurePreserving.id (τ.prod τ)).prod (ih (n + 1))
    have hassoc := measurePreserving_prodAssoc τ τ (switchParameterLaw (fun _ => τ) (n + 1) k)
    change MeasurePreserving _ _ (τ.prod (τ.prod (switchParameterLaw (fun _ => τ) (n + 1) k)))
    convert hassoc.comp (htail.comp hhead) using 1
    all_goals try with_reducible_and_instances rfl
    funext p
    simp [vectorSwitchParameters, Function.comp_def, MeasurableEquiv.piFinSuccAbove_apply]
    rfl

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_FlatSwitchSamples
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_countable _root_.OAI.PolycyclicRecognition.finitelyGeneratedSubgroupIndex_countable _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The recursive independent sampling law on the flat parameter cube -/

noncomputable section

namespace PolycyclicRecognition

open MeasureTheory

theorem measurePreserving_finAppend_law (τ : Measure ℝ) [SigmaFinite τ] (n k : ℕ) :
    MeasurePreserving (fun p : (Fin n → ℝ) × (Fin k → ℝ) => Fin.append p.1 p.2)
      ((Measure.pi (fun _ => τ)).prod (Measure.pi (fun _ => τ)))
      (Measure.pi (fun _ => τ)) := by
  have h₁ := measurePreserving_sumPiEquivProdPi_symm (fun _ : Fin n ⊕ Fin k => τ)
  have h₂ := measurePreserving_piCongrLeft (fun _ : Fin (n + k) => τ) finSumFinEquiv
  convert h₂.comp h₁ using 1
  all_goals try with_reducible_and_instances rfl
  ext p i
  obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective i
  simp only [Function.comp_apply]
  rw [MeasurableEquiv.piCongrLeft_apply_apply]
  cases j with
  | inl j =>
    change Fin.append p.1 p.2 (Fin.castAdd k j) = p.1 j
    simp
  | inr j =>
    change Fin.append p.1 p.2 (Fin.natAdd n j) = p.2 j
    simp

theorem measurePreserving_flatSamplePairs (τ : Measure ℝ) [SigmaFinite τ] (m : ℕ) :
    MeasurePreserving (flatSamplePairs m)
      (Measure.pi (fun _ => τ)) (Measure.pi (fun _ : Fin m => τ.prod τ)) := by
  let e := (Fin.appendIsometry (α := ℝ) m m).toHomeomorph.toMeasurableEquiv
  have he : MeasurePreserving e
      ((Measure.pi (fun _ => τ)).prod (Measure.pi (fun _ => τ)))
      (Measure.pi (fun _ => τ)) := measurePreserving_finAppend_law τ m m
  have hp := (measurePreserving_arrowProdEquivProdArrow ℝ ℝ (Fin m)
    (fun _ => τ) (fun _ => τ)).symm (MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ (Fin m))
  convert hp.comp (he.symm e) using 1
  all_goals try with_reducible_and_instances rfl
  ext t j <;> rfl

theorem measurePreserving_flatSwitchSamples (τ : Measure ℝ) [IsProbabilityMeasure τ]
    (n m : ℕ) :
    MeasurePreserving (flatSwitchSamples m)
      (Measure.pi (fun _ => τ)) (switchParameterLaw (fun _ => τ) n m) :=
  (measurePreserving_vectorSwitchParameters τ n m).comp (measurePreserving_flatSamplePairs τ m)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_UniformIntervalSamples
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_countable _root_.OAI.PolycyclicRecognition.finitelyGeneratedSubgroupIndex_countable _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform interval sampling has a fixed density on the full parameter cube -/

noncomputable section

namespace PolycyclicRecognition

open Set Metric MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal

theorem uniformIntervalLaw_isProbability {R : ℝ} (hR : 0 < R) :
    IsProbabilityMeasure (uniformIntervalLaw R) := by
  apply cond_isProbabilityMeasure_of_finite
  · simpa only [Real.volume_closedBall, ne_eq, ENNReal.ofReal_eq_zero] using
      (not_le.mpr (mul_pos (by norm_num : (0 : ℝ) < 2) hR))
  · rw [Real.volume_closedBall]
    exact ENNReal.ofReal_ne_top

theorem uniformIntervalLaw_pi_eq {R : ℝ} (hR : 0 < R) (m : ℕ) :
    Measure.pi (fun _ : Fin m => uniformIntervalLaw R) =
      (ENNReal.ofReal (2 * R))⁻¹ ^ m • volume.restrict (closedBall (0 : Fin m → ℝ) R) := by
  let _ := uniformIntervalLaw_isProbability hR
  apply Measure.pi_eq
  intro s hs
  rw [Measure.smul_apply, Measure.restrict_apply (MeasurableSet.univ_pi hs)]
  have hint : univ.pi s ∩ closedBall (0 : Fin m → ℝ) R =
      univ.pi (fun i => s i ∩ closedBall 0 R) := by
    rw [closedBall_pi _ hR.le]
    ext x
    simp only [mem_inter_iff, Set.mem_pi, mem_univ, forall_const, Pi.zero_apply]
    exact ⟨fun h i => ⟨h.1 i, h.2 i⟩, fun h => ⟨fun i => (h i).1, fun i => (h i).2⟩⟩
  rw [hint, volume_pi_pi]
  simp only [uniformIntervalLaw, ProbabilityTheory.cond, Measure.smul_apply,
    Measure.restrict_apply (hs _), smul_eq_mul, Real.volume_closedBall]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

theorem uniformIntervalLaw_pi_le {R : ℝ} (hR : 0 < R) (m : ℕ) :
    Measure.pi (fun _ : Fin m => uniformIntervalLaw R) ≤
      (ENNReal.ofReal (2 * R))⁻¹ ^ m • (volume : Measure (Fin m → ℝ)) := by
  rw [uniformIntervalLaw_pi_eq hR]
  intro s
  simp only [Measure.smul_apply, smul_eq_mul]
  gcongr
  exact Measure.restrict_le_self

theorem uniformIntervalLaw_pi_ae_mem {R : ℝ} (hR : 0 < R) (m : ℕ) :
    ∀ᵐ x : Fin m → ℝ ∂Measure.pi (fun _ => uniformIntervalLaw R), x ∈ closedBall 0 R := by
  rw [uniformIntervalLaw_pi_eq hR]
  exact Measure.ae_smul_measure (ae_restrict_mem measurableSet_closedBall) _

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_SampledSuccessfulVolume
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual successful interval parameters have subexponential volume -/

noncomputable section

namespace PolycyclicRecognition

open Set Metric MeasureTheory Filter
open scoped Topology

theorem measurePreserving_sampledSwitchParameters {G : Type} [MeasurableSpace G]
    (f : ℕ → ℝ → G) (τ : Measure ℝ) [IsProbabilityMeasure τ]
    (σ : ℕ → Measure G) [∀ j, IsProbabilityMeasure (σ j)]
    (hf : ∀ j, MeasurePreserving (f j) τ (σ j)) (m : ℕ) :
    MeasurePreserving (sampledSwitchParameters f m)
      (Measure.pi (fun _ => τ)) (switchParameterLaw σ 0 m) :=
  (measurePreserving_mapSwitchParameters f (fun _ => τ) σ hf 0 m).comp
    (measurePreserving_flatSwitchSamples τ 0 m)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_SwitchEndpoints
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The polynomial difference word is the endpoint of the successful switches -/

noncomputable section

namespace PolycyclicRecognition

variable {G : Type} [Group G]

omit [Group G] in
theorem mapSwitchParameters_vector (f : ℕ → ℝ → G) (n m : ℕ) (p : Fin m → ℝ × ℝ) :
    mapSwitchParameters f n m (vectorSwitchParameters m p) =
      vectorSwitchParameters m (fun j => (f (n + j.val) (p j).1, f (n + j.val) (p j).2)) := by
  induction m generalizing n with
  | zero => rfl
  | succ m ih =>
    simp only [vectorSwitchParameters, mapSwitchParameters, Fin.val_zero, Nat.add_zero]
    rw [ih]
    simp only [Fin.val_succ, Nat.add_assoc, Nat.add_comm 1]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_SuccessfulWordPaths
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Prescribed word paths through the successful sheets -/

noncomputable section

namespace PolycyclicRecognition

variable {G : Type} [Group G]

theorem WordSheetsGood.start {A : Set G} {n : G} {u : List G}
    (h : WordSheetsGood A n u) : n ∈ A := by
  cases u with
  | nil => exact h
  | cons g u => exact h.1

/-- The independent-switch event is exactly the good-sheet condition used
by the geometric word paths, after adjoining the initial good sheet. -/
theorem wordSheetsGood_of_switchSuccessful (A : Set G) (m : ℕ)
    (p : Fin m → G × G) (n : G) (hn : n ∈ A) (j : ℕ)
    (hs : SwitchSuccessful (fun _ => A) j m n (vectorSwitchParameters m p)) :
    WordSheetsGood A n (List.ofFn (fun i => (p i).1 * (p i).2⁻¹)) := by
  induction m generalizing j n with
  | zero => exact hn
  | succ m ih =>
    rw [List.ofFn_succ]
    refine ⟨hn, ?_⟩
    have hs' : n * (p 0).1 * (p 0).2⁻¹ ∈ A ∧
        SwitchSuccessful (fun _ => A) (j + 1) m (n * (p 0).1 * (p 0).2⁻¹)
          (vectorSwitchParameters m (fun i => p i.succ)) := hs
    simpa only [mul_assoc] using ih (fun i => p i.succ) (n * (p 0).1 * (p 0).2⁻¹)
      hs'.1 (j + 1) hs'.2

/-- Apply the successful-event interpretation to the original real samples. -/
theorem wordSheetsGood_sampled (A : Set G) (f : ℕ → ℝ → G)
    (hf : ∀ j s t, f j s * (f j t)⁻¹ = f j (s - t)) (m : ℕ)
    (t : Fin (m + m) → ℝ) (n : G) (hn : n ∈ A)
    (hs : SwitchSuccessful (fun _ => A) 0 m n (sampledSwitchParameters f m t)) :
    WordSheetsGood A n (List.ofFn (fun j : Fin m =>
      f j.val (t (Fin.castAdd m j) - t (Fin.natAdd m j)))) := by
  unfold sampledSwitchParameters flatSwitchSamples at hs
  rw [mapSwitchParameters_vector] at hs
  have hh := wordSheetsGood_of_switchSuccessful A m
    (fun j => (f (0 + j.val) (flatSamplePairs m t j).1,
      f (0 + j.val) (flatSamplePairs m t j).2)) n hn 0 hs
  simpa only [Nat.zero_add, flatSamplePairs, hf] using hh

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_GroupedGoodWords
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Successful switch words remain good at every bundle boundary -/

namespace PolycyclicRecognition

variable {G : Type} [Group G]

theorem wordSheetsGood_append_iff (A : Set G) (x : G) (u v : List G) :
    WordSheetsGood A x (u ++ v) ↔
      WordSheetsGood A x u ∧ WordSheetsGood A (x * u.prod) v := by
  induction u generalizing x with
  | nil =>
    simp only [List.nil_append, List.prod_nil, mul_one, WordSheetsGood]
    exact ⟨fun h => ⟨h.start, h⟩, fun h => h.2⟩
  | cons g u ih =>
    simp only [List.cons_append, WordSheetsGood, List.prod_cons, ← mul_assoc, ih]
    tauto

theorem WordSheetsGood.grouped {A : Set G} {x : G} {u : List (List G)}
    (h : WordSheetsGood A x u.flatten) : WordSheetsGood A x (u.map List.prod) := by
  induction u generalizing x with
  | nil => exact h
  | cons v u ih =>
    rw [List.flatten_cons] at h
    obtain ⟨hv, hu⟩ := (wordSheetsGood_append_iff A x v u.flatten).mp h
    exact ⟨hv.start, ih hu⟩

omit [Group G] in
theorem ofFn_eq_flatten_bundles {h m : ℕ} (u : Fin (h * m) → G) :
    List.ofFn u = (List.ofFn (fun i : Fin h =>
      List.ofFn (fun j : Fin m => u (finProdFinEquiv (i, j))))).flatten := by
  rw [List.ofFn_mul]
  congr 1
  apply congrArg List.ofFn
  funext i
  apply congrArg List.ofFn
  funext j
  congr 1
  apply Fin.ext
  simp [finProdFinEquiv, Nat.mul_comm, Nat.add_comm]

theorem WordSheetsGood.bundle_products {A : Set G} {x : G} {h m : ℕ}
    {u : Fin (h * m) → G} (hg : WordSheetsGood A x (List.ofFn u)) :
    WordSheetsGood A x (List.ofFn (fun i : Fin h =>
      (List.ofFn (fun j : Fin m => u (finProdFinEquiv (i, j)))).prod)) := by
  rw [ofFn_eq_flatten_bundles] at hg
  simpa only [List.map_ofFn, Function.comp_def] using hg.grouped

variable [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]

theorem WordSheetsGood.prefix_states {A : Set G} {x : G} {h : ℕ}
    {u : Fin h → G} (hg : WordSheetsGood A x (List.ofFn u)) :
    ∀ i, x * prefixCoordinateEquiv h u i ∈ A := by
  induction h generalizing x with
  | zero => intro i; exact Fin.elim0 i
  | succ h ih =>
    rw [List.ofFn_succ] at hg
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · rw [prefixCoordinateEquiv_zero]
      exact hg.2.start
    · rw [prefixCoordinateEquiv_succ, ← mul_assoc]
      exact ih hg.2 j

end PolycyclicRecognition

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_SequenceBackwardAsymptotics
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Subexponential mass and success probability in backward recurrence -/

namespace PolycyclicRecognition

open Filter
open scoped Topology NNReal ENNReal

/-- A fixed number of backward recurrence steps retains subexponential
normalized mass. Both the initial mass and the enlargements may vary with
the scale. -/
theorem subexponential_backward_masses_sequence
    (scale : ℕ → ℝ) (hscale : Tendsto scale atTop atTop) (h : ℕ) (a D : ℕ → ℕ → ℝ)
    (hlast : HasSubexponentialLowerBoundSeq scale (a h))
    (hD : ∀ j, j < h → HasSubexponentialUpperBoundSeq scale (D j))
    (hDpos : ∀ j, j < h → ∀ᶠ r in atTop, 0 < D j r)
    (hstep : ∀ j, j < h → ∀ᶠ r in atTop,
      a (j + 1) r ^ 2 / (2 * D j r) ≤ a j r) :
    ∀ j, j ≤ h → HasSubexponentialLowerBoundSeq scale (a j) := by
  induction h with
  | zero =>
    intro j hj
    have : j = 0 := by omega
    simpa only [this] using hlast
  | succ h ih =>
    have hah : HasSubexponentialLowerBoundSeq scale (a h) := by
      have hnum := hlast.mul hlast
      have hden := (sequence_subexponential_upper_const hscale 2).mul (hD h (by omega))
        (Eventually.of_forall (fun _ => by norm_num))
      have hp : ∀ᶠ r in atTop, 0 < 2 * D h r :=
        (hDpos h (by omega)).mono (fun _ hr => mul_pos (by norm_num) hr)
      have hl := hnum.div hden hp
      apply hl.mono
      filter_upwards [hstep h (by omega)] with r hr
      simpa only [pow_two] using hr
    intro j hj
    by_cases he : j = h + 1
    · simpa only [he] using hlast
    · exact ih hah (fun k hk => hD k (by omega))
        (fun k hk => hDpos k (by omega)) (fun k hk => hstep k (by omega)) j (by omega)

/-- A fixed ordered product of transition probabilities retains a
subexponential lower bound. -/
theorem subexponential_switch_product_sequence
    (scale : ℕ → ℝ) (hscale : Tendsto scale atTop atTop) (τ : ℕ → ℕ → ℝ≥0) (n k : ℕ)
    (hτ : ∀ j, n ≤ j → j < n + k →
      HasSubexponentialLowerBoundSeq scale (fun r => (τ j r : ℝ))) :
    HasSubexponentialLowerBoundSeq scale (fun r => (switchThresholdProduct (fun j => τ j r) n k).toReal) := by
  induction k generalizing n with
  | zero => simpa only [switchThresholdProduct, ENNReal.toReal_one] using
      sequence_subexponential_lower_const hscale (by norm_num : (0 : ℝ) < 1)
  | succ k ih =>
    have htail := ih (n + 1) (fun j hj hj' => hτ j (by omega) (by omega))
    have hhead := hτ n le_rfl (by omega)
    simpa only [switchThresholdProduct, ENNReal.toReal_mul, ENNReal.coe_toReal] using
      hhead.mul htail

/-- The normalized masses supplied by recurrence give the required lower
bound on each threshold, with the same enlargement factors. -/
theorem subexponential_backward_thresholds_sequence
    (scale : ℕ → ℝ) (hscale : Tendsto scale atTop atTop) (h : ℕ) (a D : ℕ → ℕ → ℝ)
    (hlast : HasSubexponentialLowerBoundSeq scale (a h))
    (hD : ∀ j, j < h → HasSubexponentialUpperBoundSeq scale (D j))
    (hDpos : ∀ j, j < h → ∀ᶠ r in atTop, 0 < D j r)
    (hstep : ∀ j, j < h → ∀ᶠ r in atTop,
      a (j + 1) r ^ 2 / (2 * D j r) ≤ a j r) :
    ∀ j, j < h → HasSubexponentialLowerBoundSeq scale (fun r => a (j + 1) r / (2 * D j r)) := by
  intro j hj
  apply (subexponential_backward_masses_sequence scale hscale h a D hlast hD hDpos hstep (j + 1) (by omega)).div
  · exact (sequence_subexponential_upper_const hscale 2).mul (hD j hj)
      (Eventually.of_forall (fun _ => by norm_num))
  · exact (hDpos j hj).mono (fun _ hr => mul_pos (by norm_num) hr)

end PolycyclicRecognition

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_SequenceBackwardRecurrence
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Successful parameter volume along the profile-scale sequence -/

noncomputable section

namespace PolycyclicRecognition

open Set Metric MeasureTheory Filter
open scoped Topology ENNReal NNReal

theorem exists_subexponential_backward_recurrence_sequence
    {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]
    (scale : ℕ → ℝ) (hscale : Tendsto scale atTop atTop)
    (μ : Measure G) [SFinite μ] [μ.IsMulRightInvariant]
    (σ : ℕ → ℕ → Measure G) [∀ r j, IsProbabilityMeasure (σ r j)]
    (Q A : ℕ → Set G) (K R : ℕ → ℕ → Set G) (D : ℕ → ℕ → ℝ)
    (hQfin : ∀ r, μ (Q r) ≠ ∞) (hQpos : ∀ r, 0 < (μ (Q r)).toReal)
    (hK : ∀ r j, ∀ᵐ s ∂σ r j, s ∈ K r j)
    (hRfin : ∀ r j, μ (R r j) ≠ ∞) (hRpos : ∀ r j, 0 < (μ (R r j)).toReal)
    (hQR : ∀ r j, ∀ a ∈ Q r, ∀ s ∈ K r j, a * s ∈ R r j)
    (hD : ∀ r j, 0 < D r j)
    (hvol : ∀ r j, (μ (R r j)).toReal ≤ D r j * (μ (Q r)).toReal)
    (h : ℕ) (hA : ∀ r, MeasurableSet (A r)) (hAQ : ∀ r, A r ⊆ Q r)
    (hApos : ∀ r, 0 < (μ (A r)).toReal)
    (hAlower : HasSubexponentialLowerBoundSeq scale (fun r => (μ (A r)).toReal / (μ (Q r)).toReal))
    (hDupper : ∀ j, j < h → HasSubexponentialUpperBoundSeq scale (fun r => D r j)) :
    ∃ S : ℕ → ℕ → Set G,
      (∀ r, S r h = A r) ∧
      (∀ r j, j ≤ h → MeasurableSet (S r j) ∧ S r j ⊆ A r ∧ 0 < (μ (S r j)).toReal) ∧
      HasSubexponentialLowerBoundSeq scale (fun r => (μ (S r 0)).toReal / (μ (Q r)).toReal) ∧
      let τ := fun r j => Real.toNNReal ((μ (S r (j + 1))).toReal /
        (2 * D r j * (μ (Q r)).toReal))
      HasSubexponentialLowerBoundSeq scale (fun r => (switchThresholdProduct (τ r) 0 h).toReal) ∧
        ∀ r x, x ∈ S r 0 →
          switchThresholdProduct (τ r) 0 h ≤ survivingSwitchProbability (σ r) (S r) 0 h x := by
  choose S hS using fun r => exists_backward_recurrence_probability μ (σ r) (Q r)
    (hQfin r) (hQpos r) (K r) (R r) (hK r) (hRfin r) (hRpos r) (hQR r)
    (D r) (hD r) (hvol r) h (A r) (hA r) (hAQ r) (hApos r)
  let a := fun j r => (μ (S r j)).toReal / (μ (Q r)).toReal
  have hlast : HasSubexponentialLowerBoundSeq scale (a h) := by
    simpa only [a, (hS _).1] using hAlower
  have hsteps (j : ℕ) (hj : j < h) : ∀ᶠ r in atTop,
      a (j + 1) r ^ 2 / (2 * D r j) ≤ a j r := by
    exact Eventually.of_forall (fun r => normalized_backward_mass_bound (hQpos r) (hD r j)
      ((hS r).2.2.1 j hj).2)
  have hpos (j : ℕ) (_ : j < h) : ∀ᶠ r in atTop, 0 < D r j :=
    Eventually.of_forall (fun r => hD r j)
  have hmasses := subexponential_backward_masses_sequence scale hscale h a (fun j r => D r j)
    hlast hDupper hpos hsteps
  have hthresholds := subexponential_backward_thresholds_sequence scale hscale h a (fun j r => D r j)
    hlast hDupper hpos hsteps
  let τ := fun r j => Real.toNNReal ((μ (S r (j + 1))).toReal /
    (2 * D r j * (μ (Q r)).toReal))
  have hτ (j : ℕ) (hj : j < h) :
      HasSubexponentialLowerBoundSeq scale (fun r => (τ r j : ℝ)) := by
    apply (hthresholds j hj).mono
    apply Eventually.of_forall
    intro r
    have heq : (τ r j : ℝ) = a (j + 1) r / (2 * D r j) := by
      have hp : 0 ≤ (μ (S r (j + 1))).toReal / (2 * D r j * (μ (Q r)).toReal) :=
        div_nonneg ENNReal.toReal_nonneg
          (mul_pos (mul_pos (by norm_num) (hD r j)) (hQpos r)).le
      change (Real.toNNReal ((μ (S r (j + 1))).toReal /
        (2 * D r j * (μ (Q r)).toReal)) : ℝ) =
        ((μ (S r (j + 1))).toReal / (μ (Q r)).toReal) / (2 * D r j)
      rw [Real.coe_toNNReal _ hp]
      ring
    exact heq.ge
  refine ⟨S, fun r => (hS r).1, fun r => (hS r).2.1, hmasses 0 (Nat.zero_le _), ?_⟩
  refine ⟨subexponential_switch_product_sequence scale hscale (fun j r => τ r j) 0 h (fun j _ hj => hτ j (by omega)), ?_⟩
  exact fun r x hx => (hS r).2.2.2.2 x hx

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_SequenceSuccessfulParameterMass
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Successful parameter volume along the profile-scale sequence -/

noncomputable section

namespace PolycyclicRecognition

open Set Metric MeasureTheory Filter
open scoped Topology ENNReal NNReal

theorem exists_subexponential_successful_parameters_sequence
    {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]
    (scale : ℕ → ℝ) (hscale : Tendsto scale atTop atTop)
    (μ : Measure G) [SFinite μ] [μ.IsMulRightInvariant]
    (σ : ℕ → ℕ → Measure G) [∀ r j, IsProbabilityMeasure (σ r j)]
    (Q A : ℕ → Set G) (K R : ℕ → ℕ → Set G) (D : ℕ → ℕ → ℝ)
    (hQfin : ∀ r, μ (Q r) ≠ ∞) (hQpos : ∀ r, 0 < (μ (Q r)).toReal)
    (hK : ∀ r j, ∀ᵐ s ∂σ r j, s ∈ K r j)
    (hRfin : ∀ r j, μ (R r j) ≠ ∞) (hRpos : ∀ r j, 0 < (μ (R r j)).toReal)
    (hQR : ∀ r j, ∀ a ∈ Q r, ∀ s ∈ K r j, a * s ∈ R r j)
    (hD : ∀ r j, 0 < D r j)
    (hvol : ∀ r j, (μ (R r j)).toReal ≤ D r j * (μ (Q r)).toReal)
    (h : ℕ) (hA : ∀ r, MeasurableSet (A r)) (hAQ : ∀ r, A r ⊆ Q r)
    (hApos : ∀ r, 0 < (μ (A r)).toReal)
    (hAlower : HasSubexponentialLowerBoundSeq scale (fun r => (μ (A r)).toReal / (μ (Q r)).toReal))
    (hDupper : ∀ j, j < h → HasSubexponentialUpperBoundSeq scale (fun r => D r j)) :
    ∃ (x : ℕ → G) (E : ℕ → Set (SwitchParameters G h)),
      (∀ r, x r ∈ A r) ∧ (∀ r, MeasurableSet (E r)) ∧
      HasSubexponentialLowerBoundSeq scale (fun r => (switchParameterLaw (σ r) 0 h (E r)).toReal) ∧
      ∀ r p, p ∈ E r → SwitchSuccessful (fun _ => A r) 0 h (x r) p := by
  obtain ⟨S, hlast, hS, _, hprob, hlower⟩ := exists_subexponential_backward_recurrence_sequence
    scale hscale μ σ Q A K R D hQfin hQpos hK hRfin hRpos hQR hD hvol h hA hAQ hApos hAlower hDupper
  have hnonempty (r : ℕ) : (S r 0).Nonempty :=
    nonempty_of_measure_ne_zero (ne_of_gt (ENNReal.toReal_pos_iff.mp ((hS r 0 (Nat.zero_le h)).2.2)).1)
  choose x hx using hnonempty
  let E := fun r => {p : SwitchParameters G h | SwitchSuccessful (S r) 0 h (x r) p}
  have hevent (r : ℕ) := switchParameterLaw_success_finite (σ r) (S r) 0 h
    (fun j _ hj => (hS r j (by simpa using hj)).1) (x r)
  refine ⟨x, E, fun r => (hS r 0 (Nat.zero_le h)).2.1 (hx r), fun r => (hevent r).1, ?_, ?_⟩
  · apply hprob.mono
    apply Eventually.of_forall
    intro r
    apply ENNReal.toReal_mono (measure_ne_top _ _)
    rw [(hevent r).2]
    exact hlower r (x r) (hx r)
  · intro r p hp
    exact switchSuccessful_mono (S r) (fun _ => A r) 0 h
      (fun j _ hj => (hS r j (by simpa using hj)).2.1) (x r) p hp

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_SequenceParameterDensity
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Successful parameter volume along the profile-scale sequence -/

noncomputable section

namespace PolycyclicRecognition

open Set Metric MeasureTheory Filter
open scoped Topology ENNReal NNReal

theorem subexponential_volume_of_probability_sequence
    {A : Type} [MeasurableSpace A]
    (scale : ℕ → ℝ)
    (μ ν : ℕ → Measure A) (E : ℕ → Set A) (D : ℕ → ℝ≥0)
    (hfinite : ∀ r, μ r (E r) ≠ ∞)
    (hdom : ∀ r, ν r ≤ (D r : ℝ≥0∞) • μ r)
    (hprob : HasSubexponentialLowerBoundSeq scale (fun r => (ν r (E r)).toReal))
    (hD : HasSubexponentialUpperBoundSeq scale (fun r => (D r : ℝ)))
    (hpos : ∀ᶠ r in atTop, 0 < D r) :
    HasSubexponentialLowerBoundSeq scale (fun r => (μ r (E r)).toReal) := by
  have hdiv := hprob.div hD hpos
  apply hdiv.mono
  filter_upwards [hpos] with r hr
  apply (div_le_iff₀ (show 0 < (D r : ℝ) from hr)).mpr
  have hbound := ENNReal.toReal_mono
    (ENNReal.mul_ne_top ENNReal.coe_ne_top (hfinite r)) (hdom r (E r))
  simpa only [Measure.smul_apply, smul_eq_mul, ENNReal.toReal_mul,
    ENNReal.coe_toReal, mul_comm] using hbound

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_SequenceUniformInterval
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Successful parameter volume along the profile-scale sequence -/

noncomputable section

namespace PolycyclicRecognition

open Set Metric MeasureTheory Filter
open scoped Topology ENNReal NNReal

theorem subexponential_volume_of_uniform_samples_sequence {R : ℝ}
    (scale : ℕ → ℝ) (hscale : Tendsto scale atTop atTop) (hR : 0 < R) (m : ℕ)
    (E : ℕ → Set (Fin m → ℝ)) (hER : ∀ r, E r ⊆ closedBall 0 R)
    (hprob : HasSubexponentialLowerBoundSeq scale
      (fun r => (Measure.pi (fun _ : Fin m => uniformIntervalLaw R) (E r)).toReal)) :
    HasSubexponentialLowerBoundSeq scale (fun r => (volume (E r)).toReal) := by
  let d : ℝ≥0 := ((ENNReal.ofReal (2 * R))⁻¹ ^ m).toNNReal
  have htop : (ENNReal.ofReal (2 * R))⁻¹ ^ m ≠ ∞ := by
    apply ENNReal.pow_ne_top
    exact ENNReal.inv_ne_top.mpr (by positivity)
  have hd : (d : ℝ≥0∞) = (ENNReal.ofReal (2 * R))⁻¹ ^ m := ENNReal.coe_toNNReal htop
  apply subexponential_volume_of_probability_sequence scale (fun _ => volume)
    (fun _ => Measure.pi (fun _ : Fin m => uniformIntervalLaw R)) E (fun _ => d)
    (fun r => ne_top_of_le_ne_top (measure_closedBall_lt_top.ne) (measure_mono (hER r)))
    (fun _ => by rw [hd]; exact uniformIntervalLaw_pi_le hR m) hprob
    (sequence_subexponential_upper_const hscale _) (Eventually.of_forall fun _ => ?_)
  exact ENNReal.toNNReal_pos (pow_ne_zero _ (ENNReal.inv_ne_zero.mpr ENNReal.ofReal_ne_top)) htop

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_SequenceSampledSuccessfulVolume
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_countable _root_.OAI.PolycyclicRecognition.finitelyGeneratedSubgroupIndex_countable _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Successful parameter volume along the profile-scale sequence -/

noncomputable section

namespace PolycyclicRecognition

open Set Metric MeasureTheory Filter
open scoped Topology ENNReal NNReal

theorem exists_sampled_success_volume_sequence {G : Type} [Group G] [MeasurableSpace G]
    {R : ℝ} (hR : 0 < R) (m : ℕ)
    (scale : ℕ → ℝ) (hscale : Tendsto scale atTop atTop)
    (f : ℕ → ℕ → ℝ → G) (σ : ℕ → ℕ → Measure G)
    [∀ r j, IsProbabilityMeasure (σ r j)]
    (hf : ∀ r j, MeasurePreserving (f r j) (uniformIntervalLaw R) (σ r j))
    (x : ℕ → G) (A : ℕ → Set G) (E : ℕ → Set (SwitchParameters G m))
    (hE : ∀ r, MeasurableSet (E r))
    (hprob : HasSubexponentialLowerBoundSeq scale (fun r => (switchParameterLaw (σ r) 0 m (E r)).toReal))
    (hsuccess : ∀ r p, p ∈ E r → SwitchSuccessful (fun _ => A r) 0 m (x r) p) :
    ∃ F : ℕ → Set (Fin (m + m) → ℝ),
      (∀ r, MeasurableSet (F r)) ∧ (∀ r, F r ⊆ closedBall 0 R) ∧
      HasSubexponentialLowerBoundSeq scale (fun r => (volume (F r)).toReal) ∧
      ∀ r t, t ∈ F r → SwitchSuccessful (fun _ => A r) 0 m (x r)
        (sampledSwitchParameters (f r) m t) := by
  let _ := uniformIntervalLaw_isProbability hR
  let F := fun r => sampledSwitchParameters (f r) m ⁻¹' E r ∩ closedBall 0 R
  have hmap (r : ℕ) := measurePreserving_sampledSwitchParameters (f r)
    (uniformIntervalLaw R) (σ r) (hf r) m
  have hvol (r : ℕ) : Measure.pi (fun _ : Fin (m + m) => uniformIntervalLaw R) (F r) =
      switchParameterLaw (σ r) 0 m (E r) := by
    change Measure.pi _ (_ ∩ _) = _
    rw [measure_inter_conull (show Measure.pi (fun _ : Fin (m + m) => uniformIntervalLaw R)
        (closedBall (0 : Fin (m + m) → ℝ) R)ᶜ = 0 from
      mem_ae_iff.mp (uniformIntervalLaw_pi_ae_mem hR (m + m)))]
    exact (hmap r).measure_preimage (hE r).nullMeasurableSet
  refine ⟨F, fun r => ((hE r).preimage (hmap r).measurable).inter measurableSet_closedBall,
    fun _ => inter_subset_right, ?_, ?_⟩
  · apply subexponential_volume_of_uniform_samples_sequence scale hscale hR (m + m) F (fun _ => inter_subset_right)
    simpa only [hvol] using hprob
  · intro r t ht
    exact hsuccess r _ ht.1

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_LinearHaarCoordinates
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Fixed linear coordinates preserve subexponential volume rates -/

noncomputable section
namespace PolycyclicRecognition

open MeasureTheory Filter Set
open scoped ENNReal Topology

variable {V W : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasureSpace V] [BorelSpace V] [Measure.IsAddHaarMeasure (volume : Measure V)]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  [MeasureSpace W] [BorelSpace W] [Measure.IsAddHaarMeasure (volume : Measure W)]

omit [FiniteDimensional ℝ W] in
theorem linear_equiv_volume_image_factor (e : V ≃L[ℝ] W) :
    ∃ c : ℝ, 0 < c ∧ ∀ S : Set V,
      volume (e '' S) = ENNReal.ofReal c * volume S := by
  let c := Measure.addHaarScalarFactor (Measure.map e.symm volume) (volume : Measure V)
  have hc : 0 < c := Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure _ _
  refine ⟨c, hc, ?_⟩
  intro S
  have hm := Measure.isAddLeftInvariant_eq_smul_of_regular
    (Measure.map e.symm volume) (volume : Measure V)
  have he := congrArg (fun μ : Measure V => μ S) hm
  change (Measure.map e.toHomeomorph.symm volume) S = _ at he
  rw [e.toHomeomorph.symm.measurableEmbedding.map_apply,
    e.toHomeomorph.preimage_symm, Measure.smul_apply, ENNReal.smul_def,
    smul_eq_mul] at he
  simpa only [c, ENNReal.ofReal_coe_nnreal, ContinuousLinearEquiv.coe_toHomeomorph] using he

omit [FiniteDimensional ℝ W] in
theorem HasSubexponentialLowerBoundSeq.linear_image {scale : ℕ → ℝ}
    (hscale : Tendsto scale atTop atTop) (e : V ≃L[ℝ] W)
    {A : ℕ → Set V}
    (hA : HasSubexponentialLowerBoundSeq scale (fun r => (volume (A r)).toReal)) :
    HasSubexponentialLowerBoundSeq scale (fun r => (volume (e '' A r)).toReal) := by
  obtain ⟨c, hc, hm⟩ := linear_equiv_volume_image_factor e
  have he (r : ℕ) : (volume (e '' A r)).toReal = c * (volume (A r)).toReal := by
    rw [hm, ENNReal.toReal_mul, ENNReal.toReal_ofReal hc.le]
  simpa only [he] using (sequence_subexponential_lower_const hscale hc).mul hA

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_TranslatedBoxMass
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Volume ratios for translated exponential boxes -/

noncomputable section

namespace PolycyclicRecognition

open Module MeasureTheory Set
open scoped Manifold ENNReal

variable {L E G : Type} [LieRing L] [LieAlgebra ℝ L]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace G] [ChartedSpace E G] [Group G]
  [LieGroup (𝓘(ℝ, E)) ⊤ G] [MeasurableSpace G] [BorelSpace G]

/-- Enlarging the radius of a fixed exponential box multiplies its Haar
volume by exactly the corresponding power, independently of the scale. -/
theorem exponential_box_radius_measure
    (e : L ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, E)) G)
    (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G)
    (chart : GroupLieAlgebra (𝓘(ℝ, E)) G ≃ₜ G) (hchart : ∀ x, chart x = Exp x)
    {n : ℕ} (b₀ b : Basis (Fin n) ℝ L) {R : ℝ} (hR : 0 ≤ R) :
    (Measure.map ((Exp ∘ e) ∘ b₀.equivFun.symm) volume)
      (exponentialCoordinateBox (Exp ∘ e) b R) =
      ENNReal.ofReal (R ^ n) *
        (Measure.map ((Exp ∘ e) ∘ b₀.equivFun.symm) volume)
          (exponentialCoordinateBox (Exp ∘ e) b 1) := by
  rw [exponentialCoordinateBox_eq_cube_image (Exp ∘ e) b R hR,
    exponentialCoordinateBox_eq_cube_image (Exp ∘ e) b 1 zero_le_one]
  rw [exponential_basis_subset_measure e Exp chart hchart b₀ b,
    exponential_basis_subset_measure e Exp chart hchart b₀ b]
  rw [Real.volume_Icc_pi, Real.volume_Icc_pi]
  simp only [sub_neg_eq_add, ← two_mul, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, mul_one]
  rw [ENNReal.ofReal_pow hR, ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), mul_pow]
  ring

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

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_RescaledWordEndpoints
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.basisDynkinParameter_zero _root_.OAI.PolycyclicRecognition.dynkinRightTranslation_apply _root_.OAI.PolycyclicRecognition.dynkinRightTranslation_symm_apply _root_.OAI.PolycyclicRecognition.exponentialHomOfDynkin_apply_exp _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual group endpoints in rescaled logarithmic coordinates -/

noncomputable section

namespace PolycyclicRecognition

open Module

variable {L G I : Type} [LieRing L] [LieAlgebra ℝ L] [Group G] {n c m : ℕ}

theorem exp_basis_listProduct (b : Basis (Fin n) ℝ L) (Exp : L → G)
    (hzero : Exp 0 = 1) (a : DynkinCoefficients c 2)
    (hm : ∀ x y, Exp (finiteDynkinPolynomial a ![x, y]) = Exp x * Exp y)
    (xs : List (Fin n → ℝ)) :
    Exp (b.equivFun.symm (polynomialListProduct (dynkinProduct a (basisBracket b)) xs)) =
      (xs.map (fun x => Exp (b.equivFun.symm x))).prod := by
  induction xs with
  | nil => simpa [polynomialListProduct] using hzero
  | cons x xs ih =>
    simp only [polynomialListProduct, List.map_cons, List.prod_cons]
    have he := basis_dynkinProduct b a (b.equivFun.symm x)
      (b.equivFun.symm (polynomialListProduct (dynkinProduct a (basisBracket b)) xs))
    simp only [LinearEquiv.apply_symm_apply] at he
    rw [he, LinearEquiv.symm_apply_apply, hm, ih]

theorem exp_rescaled_differenceWord (b : Basis (Fin n) ℝ L) (Exp : L → G)
    (hzero : Exp 0 = 1) (a : DynkinCoefficients c 2)
    (hm : ∀ x y, Exp (finiteDynkinPolynomial a ![x, y]) = Exp x * Exp y)
    (X : I → L) (s : I → ℝ) (r : ℝ) (letters : Fin m → I)
    (t : Fin (m + m) → ℝ) :
    Exp (b.equivFun.symm (differenceAmplitudeWordEndpoint a letters
      (basisBracket b, fun i => b.equivFun (Real.exp (r * s i) • X i)) t)) =
      (List.ofFn (fun j => Exp
        ((t (Fin.castAdd m j) - t (Fin.natAdd m j)) •
          (Real.exp (r * s (letters j)) • X (letters j))))).prod := by
  unfold differenceAmplitudeWordEndpoint amplitudeWordEndpoint
  rw [exp_basis_listProduct b Exp hzero a hm, List.map_ofFn]
  simp only [Function.comp_def, differenceParameters_apply, map_smul, LinearEquiv.symm_apply_apply]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_TupleMeasureScaling
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Independent coordinate changes and their product-volume multiplier -/

noncomputable section
namespace PolycyclicRecognition

open MeasureTheory Set
open scoped ENNReal NNReal BigOperators

theorem measure_pi_smul {I : Type} [Fintype I]
    {X : I → Type} [∀ i, MeasurableSpace (X i)]
    (μ : ∀ i, Measure (X i)) [∀ i, SigmaFinite (μ i)] (c : I → ℝ≥0) :
    Measure.pi (fun i => c i • μ i) = (∏ i, c i) • Measure.pi μ := by
  apply Measure.pi_eq
  intro s _
  simp only [Measure.smul_apply, Measure.pi_pi, ENNReal.smul_def, smul_eq_mul, ENNReal.ofNNReal_finsetProd,
    Finset.prod_mul_distrib]

theorem map_pi_of_coordinate_scaling {I : Type} [Fintype I]
    {X Y : I → Type} [∀ i, MeasurableSpace (X i)] [∀ i, MeasurableSpace (Y i)]
    (μ : ∀ i, Measure (X i)) (ν : ∀ i, Measure (Y i))
    [∀ i, SigmaFinite (μ i)] [∀ i, SigmaFinite (ν i)]
    (f : ∀ i, X i → Y i) (hf : ∀ i, Measurable (f i))
    (c : I → ℝ≥0) (hmap : ∀ i, Measure.map (f i) (μ i) = c i • ν i) :
    Measure.map (fun x i => f i (x i)) (Measure.pi μ) = (∏ i, c i) • Measure.pi ν := by
  let : ∀ i, SigmaFinite (Measure.map (f i) (μ i)) := fun i => by
    rw [hmap i]
    first | exact Measure.isProbabilityMeasure_map (by first | exact (hf i).aemeasurable) | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
  rw [Measure.pi_map_pi (fun i => (hf i).aemeasurable)]
  simp_rw [hmap]
  exact measure_pi_smul ν c

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_ExponentialTupleCoordinates
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_countable _root_.OAI.PolycyclicRecognition.finitelyGeneratedSubgroupIndex_countable _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact product volume under independent exponential coordinate charts -/

noncomputable section
namespace PolycyclicRecognition

open Module MeasureTheory Set
open scoped Manifold ENNReal NNReal BigOperators

variable {L : Type} [LieRing L] [LieAlgebra ℝ L]
  {E G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace G] [ChartedSpace E G] [Group G]
  [LieGroup (𝓘(ℝ, E)) ⊤ G] [MeasurableSpace G] [BorelSpace G]

omit [MeasurableSpace G] [BorelSpace G] in
theorem exponentialBasisHomeomorph_apply {n : ℕ}
    (e : L ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, E)) G)
    (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G)
    (chart : GroupLieAlgebra (𝓘(ℝ, E)) G ≃ₜ G) (hchart : ∀ x, chart x = Exp x)
    (b : Basis (Fin n) ℝ L) (x : Fin n → ℝ) :
    exponentialBasisHomeomorph e chart b x = Exp (e (b.equivFun.symm x)) := hchart _

theorem map_exponentialBasisHomeomorph_inverse {n : ℕ}
    (e : L ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, E)) G)
    (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G)
    (chart : GroupLieAlgebra (𝓘(ℝ, E)) G ≃ₜ G) (hchart : ∀ x, chart x = Exp x)
    (b₀ b : Basis (Fin n) ℝ L) :
    Measure.map (exponentialBasisHomeomorph e chart b).symm
      (Measure.map ((Exp ∘ e) ∘ b₀.equivFun.symm) volume) =
        basisVolumeMultiplier b₀ b • (volume : Measure (Fin n → ℝ)) := by
  ext S hS
  rw [Measure.map_apply (exponentialBasisHomeomorph e chart b).symm.measurable hS,
    Measure.smul_apply]
  have hpre : (exponentialBasisHomeomorph e chart b).symm ⁻¹' S =
      ((Exp ∘ e) ∘ b.equivFun.symm) '' S := by
    rw [(exponentialBasisHomeomorph e chart b).preimage_symm]
    congr 1
    funext x
    exact exponentialBasisHomeomorph_apply e Exp chart hchart b x
  rw [hpre, exponential_basis_subset_measure e Exp chart hchart]
  rw [ENNReal.smul_def, smul_eq_mul, ← ENNReal.ofReal_coe_nnreal]
  rfl

theorem map_exponential_tuple_coordinates {n h : ℕ}
    (e : L ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, E)) G)
    (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G)
    (chart : GroupLieAlgebra (𝓘(ℝ, E)) G ≃ₜ G) (hchart : ∀ x, chart x = Exp x)
    (b₀ : Basis (Fin n) ℝ L) (b : Fin h → Basis (Fin n) ℝ L) :
    Measure.map (fun u i => (exponentialBasisHomeomorph e chart (b i)).symm (u i))
      (Measure.pi (fun _ : Fin h => Measure.map ((Exp ∘ e) ∘ b₀.equivFun.symm) volume)) =
        (∏ i, basisVolumeMultiplier b₀ (b i)) •
          (volume : Measure (Fin h → Fin n → ℝ)) := by
  let μ := Measure.map ((Exp ∘ e) ∘ b₀.equivFun.symm) volume
  have he : ((Exp ∘ e) ∘ b₀.equivFun.symm) = exponentialBasisHomeomorph e chart b₀ := by
    funext x
    exact (exponentialBasisHomeomorph_apply e Exp chart hchart b₀ x).symm
  let : SigmaFinite μ := by
    dsimp only [μ]
    rw [he]
    exact (exponentialBasisHomeomorph e chart b₀).measurableEmbedding.sigmaFinite_map
  exact map_pi_of_coordinate_scaling (fun _ : Fin h => μ) (fun _ : Fin h => volume)
    (fun i => (exponentialBasisHomeomorph e chart (b i)).symm)
    (fun i => (exponentialBasisHomeomorph e chart (b i)).symm.measurable)
    (fun i => basisVolumeMultiplier b₀ (b i))
    (fun i => map_exponentialBasisHomeomorph_inverse e Exp chart hchart b₀ (b i))

theorem exponential_tuple_subset_measure {n h : ℕ}
    (e : L ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, E)) G)
    (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G)
    (chart : GroupLieAlgebra (𝓘(ℝ, E)) G ≃ₜ G) (hchart : ∀ x, chart x = Exp x)
    (b₀ : Basis (Fin n) ℝ L) (b : Fin h → Basis (Fin n) ℝ L) (S : Set (Fin h → G)) :
    (Measure.pi (fun _ : Fin h => Measure.map ((Exp ∘ e) ∘ b₀.equivFun.symm) volume)) S =
      ENNReal.ofReal (∏ i, |(b₀.toMatrix (b i)).det|) *
        volume (exponentialTupleCoordinates e chart b '' S) := by
  let : SecondCountableTopology G := (exponentialBasisHomeomorph e chart b₀).symm.secondCountableTopology
  let f := exponentialTupleCoordinates e chart b
  have hm := map_exponential_tuple_coordinates e Exp chart hchart b₀ b
  change Measure.map f _ = _ at hm
  have hv := congrArg (fun μ : Measure (Fin h → Fin n → ℝ) => μ (f '' S)) hm
  rw [f.measurableEmbedding.map_apply, Set.preimage_image_eq _ f.injective,
    Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at hv
  rw [hv]
  congr 1
  rw [← ENNReal.ofReal_coe_nnreal]
  congr 1
  exact map_prod NNReal.toRealHom (fun i => basisVolumeMultiplier b₀ (b i)) Finset.univ

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_RescaledTupleVolume
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.CartanFactorModel.realScaleProfile_apply _root_.OAI.PolycyclicRecognition.bracketWordDifferential_mul _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact normalization of correlated tuple volume

The domain is an arbitrary tuple set. Its coordinates need not be
independent after the successful parameters have been retained.
-/

noncomputable section
namespace PolycyclicRecognition

open Module MeasureTheory Set Filter
open scoped Manifold ENNReal Topology BigOperators

variable {L I : Type} [LieRing L] [LieAlgebra ℝ L]

variable {E G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace G] [ChartedSpace E G] [Group G]
  [LieGroup (𝓘(ℝ, E)) ⊤ G] [MeasurableSpace G] [BorelSpace G]

theorem exponential_rescaled_tuple_subset_measure {h : ℕ}
    (e : L ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, E)) G)
    (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G)
    (chart : GroupLieAlgebra (𝓘(ℝ, E)) G ≃ₜ G) (hchart : ∀ x, chart x = Exp x)
    (X : I → L) (words : Finset (FreeMagma I))
    (b₀ : Basis (Fin (finrank ℝ L)) ℝ L)
    (β : Fin h → WordBasisSelections X words) (cost : Fin h → words → ℝ)
    (r : ℝ) (S : Set (Fin h → G)) :
    (Measure.pi (fun _ : Fin h => Measure.map ((Exp ∘ e) ∘ b₀.equivFun.symm) volume)) S =
      ENNReal.ofReal (∏ i, |(columnBasisMatrix (wordListCoordinates X words b₀) (β i).val).det|) *
        ENNReal.ofReal (Real.exp (r * ∑ i, columnBasisWeight (cost i) (β i).val)) *
        volume (exponentialTupleCoordinates e chart (rescaledTupleBases X words β cost r) '' S) := by
  rw [exponential_tuple_subset_measure e Exp chart hchart b₀
    (rescaledTupleBases X words β cost r) S]
  have hd (i : Fin h) : |(b₀.toMatrix (rescaledTupleBases X words β cost r i)).det| =
      |(columnBasisMatrix (wordListCoordinates X words b₀) (β i).val).det| *
        Real.exp (r * columnBasisWeight (cost i) (β i).val) := by
    change |(b₀.toMatrix (exponentialRescaleBasis
      (WordBasisSelections.basis X words (β i))
      (fun j => cost i ((β i).val j)) r)).det| = _
    rw [← scaledColumnMatrix_eq_basis_toMatrix, det_scaledColumnMatrix,
      abs_mul, abs_of_pos (Real.exp_pos _)]
    exact mul_comm _ _
  rw [Finset.prod_congr rfl (fun i _ => hd i)]
  rw [Finset.prod_mul_distrib, ← Real.exp_sum, ← Finset.mul_sum,
    ENNReal.ofReal_mul (Finset.prod_nonneg (fun i _ => abs_nonneg _)), mul_assoc]


theorem rescaled_tuple_image_volume_lower_sequence {h : ℕ}
    (scale : ℕ → ℝ) (hscale : Tendsto scale atTop atTop)
    (e : L ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, E)) G)
    (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G)
    (chart : GroupLieAlgebra (𝓘(ℝ, E)) G ≃ₜ G) (hchart : ∀ x, chart x = Exp x)
    (X : I → L) (words : Finset (FreeMagma I))
    (b₀ : Basis (Fin (finrank ℝ L)) ℝ L)
    (β : Fin h → WordBasisSelections X words) (cost : Fin h → words → ℝ)
    (C : ℕ → Set (Fin h → Fin (finrank ℝ L) → ℝ))
    (hlower : HasSubexponentialLowerBoundSeq scale (fun n => (volume (C n)).toReal)) :
    HasSubexponentialLowerBoundSeq scale (fun n =>
      ((Measure.pi (fun _ : Fin h => Measure.map ((Exp ∘ e) ∘ b₀.equivFun.symm) volume))
        ((exponentialTupleCoordinates e chart (rescaledTupleBases X words β cost (scale n))).symm '' C n)).toReal /
          Real.exp (scale n * ∑ i, columnBasisWeight (cost i) (β i).val)) := by
  let d := ∏ i, |(columnBasisMatrix (wordListCoordinates X words b₀) (β i).val).det|
  have hd : 0 < d := Finset.prod_pos (fun i _ => abs_pos.mpr (wordBasis_det_ne_zero X words b₀ (β i)))
  have he (n : ℕ) :
      ((Measure.pi (fun _ : Fin h => Measure.map ((Exp ∘ e) ∘ b₀.equivFun.symm) volume))
        ((exponentialTupleCoordinates e chart (rescaledTupleBases X words β cost (scale n))).symm '' C n)).toReal /
          Real.exp (scale n * ∑ i, columnBasisWeight (cost i) (β i).val) = d * (volume (C n)).toReal := by
    rw [exponential_rescaled_tuple_subset_measure e Exp chart hchart X words b₀ β cost (scale n)]
    have hi : exponentialTupleCoordinates e chart (rescaledTupleBases X words β cost (scale n)) ''
        ((exponentialTupleCoordinates e chart (rescaledTupleBases X words β cost (scale n))).symm '' C n) = C n := by
      exact (exponentialTupleCoordinates e chart (rescaledTupleBases X words β cost (scale n))).image_symm_image (C n)
    rw [hi, ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal hd.le,
      ENNReal.toReal_ofReal (Real.exp_pos _).le]
    field_simp
  simpa only [he] using (sequence_subexponential_lower_const hscale hd).mul hlower

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_SourceBundleHaarImage
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_countable _root_.OAI.PolycyclicRecognition.finitelyGeneratedSubgroupIndex_countable _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.CartanFactorModel.realScaleProfile_apply _root_.OAI.PolycyclicRecognition.basisDynkinParameter_zero _root_.OAI.PolycyclicRecognition.bracketWordDifferential_mul _root_.OAI.PolycyclicRecognition.dynkinRightTranslation_apply _root_.OAI.PolycyclicRecognition.dynkinRightTranslation_symm_apply _root_.OAI.PolycyclicRecognition.exponentialHomOfDynkin_apply_exp _root_.OAI.PolycyclicRecognition.exponentialRescaleBasis_zero _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Joint source-bundle Haar volume before conjugation

The polynomial image is taken in the product of all bundle coordinates.
Thus a correlated restriction of the common parameter set is retained.
-/

noncomputable section
namespace PolycyclicRecognition

open Module MeasureTheory Filter Set
open scoped Manifold Topology

variable {L I : Type} [LieRing L] [LieAlgebra ℝ L] [Fintype I]
  {E G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace G] [ChartedSpace E G] [Group G]
  [LieGroup (𝓘(ℝ, E)) ⊤ G] [MeasurableSpace G] [BorelSpace G]

theorem source_bundle_haar_image_sequence {m h c M N : ℕ}
    (lie : L ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, E)) G)
    (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G)
    (chart : GroupLieAlgebra (𝓘(ℝ, E)) G ≃ₜ G) (hchart : ∀ x, chart x = Exp x)
    (hzero : Exp 0 = 1) (a : DynkinCoefficients c 2)
    (hm : ∀ x y, Exp (finiteDynkinPolynomial a ![x, y]) = Exp x * Exp y)
    (X : I → L) (words : Finset (FreeMagma I))
    (b₀ : Basis (Fin (finrank ℝ L)) ℝ L) (β : WordBasisSelections X words)
    (cost : words → ℝ) (s : I → ℝ) (letters : Fin m → I)
    (input : (Fin M → ℝ) ≃L[ℝ] (Fin h → Fin (m + m) → ℝ))
    (output : (Fin N → ℝ) ≃L[ℝ] (Fin h → Fin (finrank ℝ L) → ℝ))
    (scale : ℕ → ℝ) (hscale : Tendsto scale atTop atTop)
    (rem : RemezPolynomialInput) (hN : 1 ≤ N)
    (p₀ : WordLawData I (finrank ℝ L))
    (hlim : Tendsto (fun r =>
      let b := exponentialRescaleBasis (WordBasisSelections.basis X words β)
        (fun j => cost (β.val j)) (scale r)
      (basisBracket b, fun i => b.equivFun (Real.exp (scale r * s i) • X i))) atTop (𝓝 p₀))
    (t₀ : Fin (m + m) → ℝ)
    (hs : Function.Surjective (fderiv ℝ (differenceAmplitudeWordEndpoint a letters p₀) t₀))
    (R : ℕ → ℝ) (hR : ∀ r, 1 ≤ R r) (hRupper : HasSubexponentialUpperBoundSeq scale R)
    (hanchor : ∀ r, ‖input.symm (fun _ => t₀)‖ ≤ R r)
    (A : ℕ → Set (Fin M → ℝ)) (hA : ∀ r, MeasurableSet (A r))
    (hAR : ∀ r, A r ⊆ Metric.closedBall 0 (R r))
    (hAlower : HasSubexponentialLowerBoundSeq scale (fun r => (volume (A r)).toReal)) :
    ∃ C : ℕ → Set (Fin h → G), (∀ r, IsCompact (C r)) ∧
      (∀ᶠ r in atTop, C r ⊆ sourceBundleProduct lie Exp X s letters input (scale r) '' A r) ∧
      HasSubexponentialLowerBoundSeq scale (fun r =>
        ((Measure.pi (fun _ : Fin h => Measure.map ((Exp ∘ lie) ∘ b₀.equivFun.symm) volume)) (C r)).toReal /
          Real.exp (scale r * ((h : ℝ) * columnBasisWeight cost β.val))) := by
  let b := fun r => exponentialRescaleBasis (WordBasisSelections.basis X words β)
    (fun j => cost (β.val j)) (scale r)
  let p : ℕ → WordLawData I (finrank ℝ L) := fun r =>
    (basisBracket (b r), fun i => (b r).equivFun (Real.exp (scale r * s i) • X i))
  obtain ⟨K, hK, hKA, hKlower⟩ := bundle_word_image_sequence scale hscale rem hN a letters
    input output p p₀ hlim t₀ hs R hR hRupper hanchor A hA hAR hAlower
  let T := fun r => exponentialTupleCoordinates lie chart (fun _ : Fin h => b r)
  let C := fun r => (T r).symm '' (output '' K r)
  have hC (r : ℕ) : IsCompact (C r) :=
    ((hK r).image output.continuous).image (T r).symm.continuous
  refine ⟨C, hC, ?_, ?_⟩
  · filter_upwards [hKA] with r hr
    rintro y ⟨z, ⟨w, hw, rfl⟩, rfl⟩
    obtain ⟨t, ht, htw⟩ := hr hw
    refine ⟨t, ht, ?_⟩
    rw [← htw]
    funext j
    change _ = exponentialBasisHomeomorph lie chart (b r)
      (output (bundleWordEndpoint a letters input output (p r) t) j)
    rw [bundleWordEndpoint, ContinuousLinearEquiv.apply_symm_apply,
      exponentialBasisHomeomorph_apply lie Exp chart hchart]
    exact (exp_rescaled_differenceWord (b r) (Exp ∘ lie) (by simpa using hzero) a
      (model_binary_dynkin lie Exp a hm) X s (scale r) letters (input t j)).symm
  · have hvol := rescaled_tuple_image_volume_lower_sequence scale hscale lie Exp chart hchart
      X words b₀ (fun _ : Fin h => β) (fun _ => cost) (fun r => output '' K r)
      (hKlower.linear_image hscale output)
    change HasSubexponentialLowerBoundSeq scale (fun r =>
      ((Measure.pi (fun _ : Fin h => Measure.map ((Exp ∘ lie) ∘ b₀.equivFun.symm) volume)) (C r)).toReal /
        Real.exp (scale r * ∑ _i : Fin h, columnBasisWeight cost β.val)) at hvol
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using hvol

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_RecurrentSourceBundles
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.CartanFactorModel.realScaleProfile_apply _root_.OAI.PolycyclicRecognition.basisDynkinParameter_zero _root_.OAI.PolycyclicRecognition.bracketWordDifferential_mul _root_.OAI.PolycyclicRecognition.dynkinRightTranslation_apply _root_.OAI.PolycyclicRecognition.dynkinRightTranslation_symm_apply _root_.OAI.PolycyclicRecognition.exponentialHomOfDynkin_apply_exp _root_.OAI.PolycyclicRecognition.exponentialRescaleBasis_zero _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Backward recurrence produces the actual joint source-bundle volume

All bundle schemes and their number are fixed before the successful
parameter set is selected. The image is taken before conjugating bundles.
-/

noncomputable section
namespace PolycyclicRecognition

open Module MeasureTheory Filter Set Metric
open scoped Manifold Topology ENNReal NNReal

variable {L I : Type} [LieRing L] [LieAlgebra ℝ L] [Fintype I]
  {E G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace G] [ChartedSpace E G] [Group G]
  [LieGroup (𝓘(ℝ, E)) ⊤ G] [MeasurableSpace G] [BorelSpace G]
  [MeasurableMul₂ G] [MeasurableInv G]

theorem recurrent_source_bundle_haar_image_sequence {m h c : ℕ}
    (lie : L ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, E)) G)
    (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G)
    (chart : GroupLieAlgebra (𝓘(ℝ, E)) G ≃ₜ G) (hchart : ∀ x, chart x = Exp x)
    (hzero : Exp 0 = 1) (a : DynkinCoefficients c 2)
    (hm : ∀ x y, Exp (finiteDynkinPolynomial a ![x, y]) = Exp x * Exp y)
    (X : I → L) (words : Finset (FreeMagma I))
    (b₀ : Basis (Fin (finrank ℝ L)) ℝ L) (β : WordBasisSelections X words)
    (cost : words → ℝ) (s : I → ℝ) (letters : Fin m → I)
    (scale : ℕ → ℝ) (hscale : Tendsto scale atTop atTop)
    (rem : RemezPolynomialInput) (hN : 1 ≤ h * finrank ℝ L)
    (p₀ : WordLawData I (finrank ℝ L))
    (hlim : Tendsto (fun r =>
      let b := exponentialRescaleBasis (WordBasisSelections.basis X words β)
        (fun j => cost (β.val j)) (scale r)
      (basisBracket b, fun i => b.equivFun (Real.exp (scale r * s i) • X i))) atTop (𝓝 p₀))
    (t₀ : Fin (m + m) → ℝ)
    (hs : Function.Surjective (fderiv ℝ (differenceAmplitudeWordEndpoint a letters p₀) t₀))
    (ρ : ℝ) (hρ : 1 ≤ ρ)
    (μ : Measure G) [SFinite μ] [μ.IsMulRightInvariant]
    (sample : ℕ → ℕ → ℝ → G) (σ : ℕ → ℕ → Measure G)
    [∀ r j, IsProbabilityMeasure (σ r j)]
    (hsample : ∀ r j, MeasurePreserving (sample r j) (uniformIntervalLaw ρ) (σ r j))
    (Q Good : ℕ → Set G) (K V : ℕ → ℕ → Set G) (D : ℕ → ℕ → ℝ)
    (hQfin : ∀ r, μ (Q r) ≠ ∞) (hQpos : ∀ r, 0 < (μ (Q r)).toReal)
    (hK : ∀ r j, ∀ᵐ v ∂σ r j, v ∈ K r j)
    (hVfin : ∀ r j, μ (V r j) ≠ ∞) (hVpos : ∀ r j, 0 < (μ (V r j)).toReal)
    (hQV : ∀ r j, ∀ x ∈ Q r, ∀ v ∈ K r j, x * v ∈ V r j)
    (hD : ∀ r j, 0 < D r j)
    (hdenom : ∀ r j, (μ (V r j)).toReal ≤ D r j * (μ (Q r)).toReal)
    (hGood : ∀ r, MeasurableSet (Good r)) (hGoodQ : ∀ r, Good r ⊆ Q r)
    (hGoodpos : ∀ r, 0 < (μ (Good r)).toReal)
    (hGoodlower : HasSubexponentialLowerBoundSeq scale
      (fun r => (μ (Good r)).toReal / (μ (Q r)).toReal))
    (hDupper : ∀ j, j < h * m → HasSubexponentialUpperBoundSeq scale (fun r => D r j)) :
    ∃ (x : ℕ → G) (C : ℕ → Set (Fin h → G)),
      (∀ r, x r ∈ Good r) ∧ (∀ r, IsCompact (C r)) ∧
      HasSubexponentialLowerBoundSeq scale (fun r =>
        ((Measure.pi (fun _ : Fin h => Measure.map ((Exp ∘ lie) ∘ b₀.equivFun.symm) volume)) (C r)).toReal /
          Real.exp (scale r * ((h : ℝ) * columnBasisWeight cost β.val))) ∧
      ∀ᶠ r in atTop, ∀ y ∈ C r, ∃ t : Fin (h * m + h * m) → ℝ,
        t ∈ closedBall 0 ρ ∧
        SwitchSuccessful (fun _ => Good r) 0 (h * m) (x r)
          (sampledSwitchParameters (sample r) (h * m) t) ∧
        sourceBundleProduct lie Exp X s letters (bundleParameterChart h m) (scale r) t = y := by
  obtain ⟨x, B, hx, hB, hprob, hsuccess⟩ := exists_subexponential_successful_parameters_sequence
    scale hscale μ σ Q Good K V D hQfin hQpos hK hVfin hVpos hQV hD hdenom (h * m)
    hGood hGoodQ hGoodpos hGoodlower hDupper
  obtain ⟨A, hA, hAρ, hAlower, hAsuccess⟩ := exists_sampled_success_volume_sequence
    (zero_lt_one.trans_le hρ) (h * m) scale hscale sample σ hsample x Good B hB hprob hsuccess
  let R := 1 + ρ + ‖(bundleParameterChart h m).symm (fun _ => t₀)‖
  have hR : 1 ≤ R := by dsimp [R] <;> linarith [norm_nonneg ((bundleParameterChart h m).symm (fun _ => t₀))]
  have hρR : ρ ≤ R := by dsimp [R] <;> linarith [norm_nonneg ((bundleParameterChart h m).symm (fun _ => t₀))]
  have hanchor : ‖(bundleParameterChart h m).symm (fun _ => t₀)‖ ≤ R := by dsimp [R] <;> linarith
  obtain ⟨C, hC, hCA, hClower⟩ := source_bundle_haar_image_sequence lie Exp chart hchart
    hzero a hm X words b₀ β cost s letters (bundleParameterChart h m) (bundleOutputChart h _)
    scale hscale rem hN p₀ hlim t₀ hs (fun _ => R) (fun _ => hR)
    (sequence_subexponential_upper_const hscale R) (fun _ => hanchor) A hA
    (fun r => (hAρ r).trans (closedBall_subset_closedBall hρR)) hAlower
  refine ⟨x, C, hx, hC, hClower, ?_⟩
  filter_upwards [hCA] with r hr
  intro y hy
  obtain ⟨t, ht, hty⟩ := hr hy
  exact ⟨t, hAρ r ht, hAsuccess r t ht, hty⟩

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_SuccessfulBundleStates
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Successful global switches give good conjugated bundle-end states -/

noncomputable section
namespace PolycyclicRecognition

open Module Set
open scoped Manifold

variable {L I : Type} [LieRing L] [LieAlgebra ℝ L] [Fintype I]
  {E G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace G] [ChartedSpace E G] [Group G]
  [LieGroup (𝓘(ℝ, E)) ⊤ G] [MeasurableSpace G] [BorelSpace G]
  [MeasurableMul₂ G] [MeasurableInv G]

omit [Fintype I] [BorelSpace G] in
theorem successful_sourceBundleStates_good {m h : ℕ}
    (lie : L ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, E)) G)
    (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G)
    (X : I → L) (s : I → ℝ) (letters : Fin m → I) (r : ℝ)
    (φ : Fin h → G ≃* G) (sample : ℕ → ℝ → G)
    (hsub : ∀ j u v, sample j u * (sample j v)⁻¹ = sample j (u - v))
    (hsample : ∀ (i : Fin h) (j : Fin m) t,
      sample (finProdFinEquiv (i, j)).val t = φ i
        (Exp (lie (t • (Real.exp (r * s (letters j)) • X (letters j))))))
    (Good : Set G) (x : G) (hx : x ∈ Good)
    (t : Fin (h * m + h * m) → ℝ)
    (hs : SwitchSuccessful (fun _ => Good) 0 (h * m) x
      (sampledSwitchParameters sample (h * m) t)) :
    ∀ i : Fin h, x * prefixCoordinateEquiv h
      (fun j => φ j (sourceBundleProduct lie Exp X s letters (bundleParameterChart h m) r t j)) i ∈ Good := by
  have hg := (wordSheetsGood_sampled Good sample hsub (h * m) t x hx hs).bundle_products
  have he (i : Fin h) :
      (List.ofFn (fun j : Fin m => sample (finProdFinEquiv (i, j)).val
        (t (Fin.castAdd (h * m) (finProdFinEquiv (i, j))) -
          t (Fin.natAdd (h * m) (finProdFinEquiv (i, j)))))).prod =
        φ i (sourceBundleProduct lie Exp X s letters (bundleParameterChart h m) r t i) := by
    simp only [sourceBundleProduct, bundleParameterChart_left, bundleParameterChart_right,
      map_list_prod, List.map_ofFn, Function.comp_def, hsample]
  have he' : (fun i : Fin h =>
      (List.ofFn (fun j : Fin m => sample (finProdFinEquiv (i, j)).val
        (t (Fin.castAdd (h * m) (finProdFinEquiv (i, j))) -
          t (Fin.natAdd (h * m) (finProdFinEquiv (i, j)))))).prod) =
        fun i => φ i (sourceBundleProduct lie Exp X s letters (bundleParameterChart h m) r t i) :=
    funext he
  rw [he'] at hg
  exact hg.prefix_states

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_GoodSourceBundleImage
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The joint volume of good bundle-end states

The successful parameter set can be correlated.  Haar preservation is
applied to its image, after the joint polynomial image estimate.
-/

noncomputable section
namespace PolycyclicRecognition

open Module MeasureTheory Filter Set Metric
open scoped Manifold Topology

variable {L I : Type} [LieRing L] [LieAlgebra ℝ L]
  {E G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace G] [ChartedSpace E G] [Group G]
  [LieGroup (𝓘(ℝ, E)) ⊤ G] [MeasurableSpace G] [BorelSpace G]
  [MeasurableMul₂ G] [MeasurableInv G]

theorem good_source_bundle_image {m h : ℕ}
    (lie : L ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, E)) G)
    (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G)
    (X : I → L) (s : I → ℝ) (letters : Fin m → I)
    (scale : ℕ → ℝ) (p : ℝ)
    (μ : Measure G) [SigmaFinite μ] [μ.IsMulLeftInvariant]
    (φ : ℕ → Fin h → G ≃ₜ* G)
    (hφ : ∀ r i, MeasurePreserving (φ r i) μ μ)
    (sample : ℕ → ℕ → ℝ → G)
    (hsub : ∀ r j u v, sample r j u * (sample r j v)⁻¹ = sample r j (u - v))
    (hsample : ∀ r (i : Fin h) (j : Fin m) t,
      sample r (finProdFinEquiv (i, j)).val t = φ r i
        (Exp (lie (t • (Real.exp (scale r * s (letters j)) • X (letters j))))))
    (Good : ℕ → Set G) (x : ℕ → G) (hx : ∀ r, x r ∈ Good r)
    (C : ℕ → Set (Fin h → G)) (hC : ∀ r, IsCompact (C r))
    (hvol : HasSubexponentialLowerBoundSeq scale (fun r =>
      ((Measure.pi fun _ : Fin h => μ) (C r)).toReal / Real.exp (scale r * p)))
    (ρ : ℝ)
    (hreach : ∀ᶠ r in atTop, ∀ y ∈ C r, ∃ t : Fin (h * m + h * m) → ℝ,
      t ∈ closedBall 0 ρ ∧
      SwitchSuccessful (fun _ => Good r) 0 (h * m) (x r)
        (sampledSwitchParameters (sample r) (h * m) t) ∧
      sourceBundleProduct lie Exp X s letters (bundleParameterChart h m) (scale r) t = y) :
    let S := fun r => sourceBundleStateEquiv h (x r)
      (fun i => (φ r i).toHomeomorph.toMeasurableEquiv) '' C r
    (∀ r, IsCompact (S r)) ∧
      HasSubexponentialLowerBoundSeq scale (fun r =>
        ((Measure.pi fun _ : Fin h => μ) (S r)).toReal / Real.exp (scale r * p)) ∧
      ∀ᶠ r in atTop, ∀ v ∈ S r, (∀ i, v i ∈ Good r) ∧
        ∃ t : Fin (h * m + h * m) → ℝ, t ∈ closedBall 0 ρ ∧
          SwitchSuccessful (fun _ => Good r) 0 (h * m) (x r)
            (sampledSwitchParameters (sample r) (h * m) t) ∧
          v = sourceBundleStateEquiv h (x r)
            (fun i => (φ r i).toHomeomorph.toMeasurableEquiv)
            (sourceBundleProduct lie Exp X s letters (bundleParameterChart h m) (scale r) t) := by
  let : IsTopologicalGroup G := topologicalGroup_of_lieGroup (𝓘(ℝ, E)) ⊤
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · intro r
    exact (hC r).image (continuous_sourceBundleStateEquiv h (x r) _
      (fun i => (φ r i).continuous))
  · have he (r : ℕ) := sourceBundleStateEquiv_image_measure μ h (x r)
      (fun i => (φ r i).toHomeomorph.toMeasurableEquiv) (hφ r) (C r)
    simpa only [he] using hvol
  · filter_upwards [hreach] with r hr
    rintro v ⟨y, hy, rfl⟩
    obtain ⟨t, ht, hs, rfl⟩ := hr y hy
    refine ⟨?_, t, ht, hs, rfl⟩
    exact successful_sourceBundleStates_good lie Exp X s letters (scale r)
      (fun i => (φ r i).toMulEquiv) (sample r) (hsub r) (hsample r) (Good r) (x r) (hx r) t hs

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_RootIntervalSampling
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual independent interval laws for the root increments -/

noncomputable section

namespace PolycyclicRecognition

open MeasureTheory

variable {L N I : Type} [AddCommGroup L] [Module ℝ L] [Group N]

omit [Group N] in
theorem rootIntervalSample_letter (Exp : L → N) {m : ℕ} (letters : Fin m → I)
    (X : I → L) (s : I → ℝ) (r : ℝ) (j : Fin m) (t : ℝ) :
    rootIntervalSample Exp letters X s r j.val t =
      Exp (t • (Real.exp (r * s (letters j)) • X (letters j))) := by
  simp [rootIntervalSample, rootIntervalDirection, j.isLt]

/-- Two independent interval samples differ by the single intended root
increment. There is no need to retain a profile at their intermediate product. -/
theorem rootIntervalSample_sub (Exp : L → N)
    (hneg : ∀ v, Exp (-v) = (Exp v)⁻¹)
    (hadd : ∀ (v : L) (u t : ℝ), Exp ((u + t) • v) = Exp (u • v) * Exp (t • v))
    {m : ℕ} (letters : Fin m → I) (X : I → L) (s : I → ℝ) (r : ℝ) (j : ℕ) (u t : ℝ) :
    rootIntervalSample Exp letters X s r j u * (rootIntervalSample Exp letters X s r j t)⁻¹ =
      rootIntervalSample Exp letters X s r j (u - t) := by
  unfold rootIntervalSample
  rw [← hneg, ← neg_smul, ← hadd, sub_eq_add_neg]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_RootIntervalSupports
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Compact supports of the actual root interval laws -/

noncomputable section

namespace PolycyclicRecognition

open MeasureTheory Set Metric

variable {L N I : Type} [AddCommGroup L] [Module ℝ L]
  [MeasurableSpace N] [TopologicalSpace N] [BorelSpace N] [T2Space N]

omit [MeasurableSpace N] [BorelSpace N] [T2Space N] in
theorem isCompact_rootIntervalSupport (Exp : L → N)
    (hcont : ∀ v : L, Continuous (fun t : ℝ => Exp (t • v)))
    {m : ℕ} (letters : Fin m → I) (X : I → L) (s : I → ℝ) (r R : ℝ) (j : ℕ) :
    IsCompact (rootIntervalSupport Exp letters X s r R j) :=
  (isCompact_closedBall (0 : ℝ) R).image (hcont _)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CoupledRootIntervals
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Conjugated interval laws used by second-sheet source switches -/

noncomputable section
namespace PolycyclicRecognition

open MeasureTheory Set Metric

variable {L N I : Type} [AddCommGroup L] [Module ℝ L] [Group N]
  [TopologicalSpace N] [IsTopologicalGroup N] [MeasurableSpace N] [BorelSpace N] [T2Space N]

omit [MeasurableSpace N] [BorelSpace N] [T2Space N] in
theorem continuous_coupledRootIntervalSample (Exp : L → N)
    (hc : ∀ v : L, Continuous (fun t : ℝ => Exp (t • v)))
    {m : ℕ} (letters : Fin m → I) (X : I → L) (s : I → ℝ)
    (r : ℝ) (k : ℕ → N) (j : ℕ) :
    Continuous (coupledRootIntervalSample Exp letters X s r k j) :=
  (continuous_const.mul (hc _)).mul continuous_const

omit [T2Space N] in
theorem measurePreserving_coupledRootIntervalSample (Exp : L → N)
    (hc : ∀ v : L, Continuous (fun t : ℝ => Exp (t • v)))
    {m : ℕ} (letters : Fin m → I) (X : I → L) (s : I → ℝ)
    (r ρ : ℝ) (k : ℕ → N) (j : ℕ) :
    MeasurePreserving (coupledRootIntervalSample Exp letters X s r k j)
      (uniformIntervalLaw ρ) (coupledRootIntervalLaw Exp letters X s r ρ k j) :=
  ⟨(continuous_coupledRootIntervalSample Exp hc letters X s r k j).measurable, rfl⟩

omit [T2Space N] in
theorem coupledRootIntervalLaw_isProbability (Exp : L → N)
    (hc : ∀ v : L, Continuous (fun t : ℝ => Exp (t • v)))
    {m : ℕ} (letters : Fin m → I) (X : I → L) (s : I → ℝ)
    (r : ℝ) {ρ : ℝ} (hρ : 0 < ρ) (k : ℕ → N) (j : ℕ) :
    IsProbabilityMeasure (coupledRootIntervalLaw Exp letters X s r ρ k j) := by
  let := uniformIntervalLaw_isProbability hρ
  unfold coupledRootIntervalLaw
  exact Measure.isProbabilityMeasure_map
    (continuous_coupledRootIntervalSample Exp hc letters X s r k j).aemeasurable

theorem coupledRootIntervalLaw_ae_mem_support (Exp : L → N)
    (hc : ∀ v : L, Continuous (fun t : ℝ => Exp (t • v)))
    {m : ℕ} (letters : Fin m → I) (X : I → L) (s : I → ℝ)
    (r ρ : ℝ) (k : ℕ → N) (j : ℕ) :
    ∀ᵐ u ∂coupledRootIntervalLaw Exp letters X s r ρ k j,
      u ∈ (fun v => k j * v * (k j)⁻¹) '' rootIntervalSupport Exp letters X s r ρ j := by
  have hcompact : IsCompact ((fun v => k j * v * (k j)⁻¹) ''
      rootIntervalSupport Exp letters X s r ρ j) :=
    (isCompact_rootIntervalSupport Exp hc letters X s r ρ j).image
    ((continuous_const.mul continuous_id).mul continuous_const)
  apply (ae_map_iff (continuous_coupledRootIntervalSample Exp hc letters X s r k j).measurable.aemeasurable
    hcompact.measurableSet).mpr
  exact (ProbabilityTheory.ae_cond_mem measurableSet_closedBall).mono
    (fun t ht => ⟨rootIntervalSample Exp letters X s r j t, ⟨t, ht, rfl⟩, rfl⟩)

omit [TopologicalSpace N] [IsTopologicalGroup N] [MeasurableSpace N] [BorelSpace N] [T2Space N] in
theorem coupledRootIntervalSample_sub (Exp : L → N)
    (hneg : ∀ v, Exp (-v) = (Exp v)⁻¹)
    (hadd : ∀ (v : L) (u t : ℝ), Exp ((u + t) • v) = Exp (u • v) * Exp (t • v))
    {m : ℕ} (letters : Fin m → I) (X : I → L) (s : I → ℝ)
    (r : ℝ) (k : ℕ → N) (j : ℕ) (u t : ℝ) :
    coupledRootIntervalSample Exp letters X s r k j u *
      (coupledRootIntervalSample Exp letters X s r k j t)⁻¹ =
        coupledRootIntervalSample Exp letters X s r k j (u - t) := by
  have he := rootIntervalSample_sub Exp hneg hadd letters X s r j u t
  dsimp only [coupledRootIntervalSample]
  rw [← he]
  group

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_CoupledBundleStates
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual bundle conjugations preserve joint Haar volume -/

noncomputable section
namespace PolycyclicRecognition

open MeasureTheory Set

variable {N : Type} [Group N] [TopologicalSpace N] [IsTopologicalGroup N]

variable [MeasurableSpace N] [BorelSpace N]

theorem measurePreserving_innerContinuousMulEquiv
    (μ : Measure N) [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant] (k : N) :
    MeasurePreserving (innerContinuousMulEquiv k) μ μ :=
  (measurePreserving_mul_right μ k⁻¹).comp (measurePreserving_mul_left μ k)

omit [TopologicalSpace N] [IsTopologicalGroup N] [MeasurableSpace N] [BorelSpace N] in
theorem bundleConjugator_mem {h m : ℕ} (k : Fin h → N) {S : Set N}
    (h1 : (1 : N) ∈ S) (hk : ∀ i, k i ∈ S) (j : ℕ) : bundleConjugator m k j ∈ S := by
  unfold bundleConjugator
  split_ifs
  · exact hk _
  · exact h1

variable {L I : Type} [AddCommGroup L] [Module ℝ L]

omit [TopologicalSpace N] [IsTopologicalGroup N] [MeasurableSpace N] [BorelSpace N] in
theorem coupledRootIntervalSample_bundle (Exp : L → N) {h m : ℕ}
    (letters : Fin m → I) (X : I → L) (s : I → ℝ) (r : ℝ) (k : Fin h → N)
    (i : Fin h) (j : Fin m) (t : ℝ) :
    coupledRootIntervalSample Exp
      (fun q : Fin (h * m) => letters (finProdFinEquiv.symm q).2) X s r
      (bundleConjugator m k) (finProdFinEquiv (i, j)).val t =
      k i * Exp (t • (Real.exp (r * s (letters j)) • X (letters j))) * (k i)⁻¹ := by
  dsimp only [coupledRootIntervalSample]
  rw [bundleConjugator_apply, rootIntervalSample_letter]
  simp only [Equiv.symm_apply_apply]

section Lie

open Filter Metric
open scoped Manifold Topology

variable {L₀ I₀ EN : Type} [LieRing L₀] [LieAlgebra ℝ L₀]
  [NormedAddCommGroup EN] [NormedSpace ℝ EN] [FiniteDimensional ℝ EN]
  [ChartedSpace EN N] [LieGroup (𝓘(ℝ, EN)) ⊤ N]
  [T2Space N] [SecondCountableTopology N]

omit [T2Space N] in
/-- The second-sheet conjugations are the actual inner automorphisms.
The joint lower volume is retained when passing to all successive states. -/
theorem good_coupled_source_bundle_image {h m : ℕ}
    (lie : L₀ ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, EN)) N)
    (Exp : GroupLieAlgebra (𝓘(ℝ, EN)) N → N) (hExp : IsGroupExponential Exp)
    (X : I₀ → L₀) (s : I₀ → ℝ) (letters : Fin m → I₀)
    (scale : ℕ → ℝ) (p : ℝ)
    (μ : Measure N) [SigmaFinite μ] [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant]
    (k : ℕ → Fin h → N) (Good : ℕ → Set N) (x : ℕ → N)
    (hx : ∀ n, x n ∈ Good n) (C : ℕ → Set (Fin h → N))
    (hC : ∀ n, IsCompact (C n))
    (hvol : HasSubexponentialLowerBoundSeq scale (fun n =>
      ((Measure.pi fun _ : Fin h => μ) (C n)).toReal / Real.exp (scale n * p)))
    (ρ : ℝ)
    (hreach : ∀ᶠ n in atTop, ∀ y ∈ C n, ∃ t : Fin (h * m + h * m) → ℝ,
      t ∈ closedBall 0 ρ ∧
      SwitchSuccessful (fun _ => Good n) 0 (h * m) (x n)
        (sampledSwitchParameters
          (coupledRootIntervalSample (Exp ∘ lie)
            (fun q : Fin (h * m) => letters (finProdFinEquiv.symm q).2)
            X s (scale n) (bundleConjugator m (k n))) (h * m) t) ∧
      sourceBundleProduct lie Exp X s letters (bundleParameterChart h m) (scale n) t = y) :
    let S := fun n => sourceBundleStateEquiv h (x n)
      (fun i => (innerContinuousMulEquiv (k n i)).toHomeomorph.toMeasurableEquiv) '' C n
    (∀ n, IsCompact (S n)) ∧
      HasSubexponentialLowerBoundSeq scale (fun n =>
        ((Measure.pi fun _ : Fin h => μ) (S n)).toReal / Real.exp (scale n * p)) ∧
      ∀ᶠ n in atTop, ∀ v ∈ S n, (∀ i, v i ∈ Good n) ∧
        ∃ t : Fin (h * m + h * m) → ℝ, t ∈ closedBall 0 ρ ∧
          SwitchSuccessful (fun _ => Good n) 0 (h * m) (x n)
            (sampledSwitchParameters
              (coupledRootIntervalSample (Exp ∘ lie)
                (fun q : Fin (h * m) => letters (finProdFinEquiv.symm q).2)
                X s (scale n) (bundleConjugator m (k n))) (h * m) t) ∧
          v = sourceBundleStateEquiv h (x n)
            (fun i => (innerContinuousMulEquiv (k n i)).toHomeomorph.toMeasurableEquiv)
            (sourceBundleProduct lie Exp X s letters (bundleParameterChart h m) (scale n) t) := by
  apply good_source_bundle_image lie Exp X s letters scale p μ
    (fun n i => innerContinuousMulEquiv (k n i))
    (fun n i => measurePreserving_innerContinuousMulEquiv μ (k n i))
    (fun n => coupledRootIntervalSample (Exp ∘ lie)
      (fun q : Fin (h * m) => letters (finProdFinEquiv.symm q).2)
      X s (scale n) (bundleConjugator m (k n)))
    ?_ ?_ Good x hx C hC hvol ρ hreach
  · intro n j u v
    apply coupledRootIntervalSample_sub
    · intro z
      simp only [Function.comp_apply, map_neg, hExp.map_neg]
    · intro z a b
      simpa only [Function.comp_apply, map_smul] using hExp.map_add_smul (lie z) a b
  · intro n i j t
    simpa only [innerContinuousMulEquiv_apply, Function.comp_apply] using
      coupledRootIntervalSample_bundle (Exp ∘ lie) letters X s (scale n) (k n) i j t

end Lie

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_MeasurePacking
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Counting separated endpoints using Haar volume

Disjoint fixed-radius balls around separated endpoints have the same positive
Haar mass. A polynomial-volume region containing their thickening therefore
gives a polynomial cardinal bound. This is the counting step of the path
packing lemma, separated from its Lie-coordinate estimate.
-/

namespace PolycyclicRecognition

open MeasureTheory MeasureTheory.Measure Metric Set
open scoped ENNReal

variable {G : Type} [Group G] [MetricSpace G] [MeasurableSpace G]
  [BorelSpace G] [MeasurableMul G] [IsIsometricSMul G G]

/-- The same maximal-packing argument applies to arbitrary endpoint sets. A
bound on their finite separated subsets already supplies a finite net; no
measurability or compactness of the endpoint set is needed. -/
theorem finite_separated_cover_set_of_bound {X : Type} [PseudoMetricSpace X]
    (S : Set X) {r : ℝ} (hr : 0 ≤ r) (N : ℕ)
    (hbound : ∀ t : Finset X, (↑t : Set X) ⊆ S →
      (∀ x ∈ t, ∀ y ∈ t, x ≠ y → r < dist x y) → t.card ≤ N) :
    ∃ t : Finset X, (↑t : Set X) ⊆ S ∧
      (∀ x ∈ t, ∀ y ∈ t, x ≠ y → r < dist x y) ∧ t.card ≤ N ∧
      ∀ x ∈ S, ∃ y ∈ t, dist x y ≤ r := by
  classical
  let P (k : ℕ) := ∃ t : Finset X, (↑t : Set X) ⊆ S ∧
    (∀ x ∈ t, ∀ y ∈ t, x ≠ y → r < dist x y) ∧ t.card = k
  have hP0 : P 0 := ⟨∅, by simp, by simp, by simp⟩
  obtain ⟨t, hts, hsep, hcard⟩ := Nat.findGreatest_spec (Nat.zero_le N) hP0
  have hmax (u : Finset X) (hu : (↑u : Set X) ⊆ S)
      (husep : ∀ x ∈ u, ∀ y ∈ u, x ≠ y → r < dist x y) : u.card ≤ t.card := by
    rw [hcard]
    exact Nat.le_findGreatest (hbound u hu husep) ⟨u, hu, husep, rfl⟩
  refine ⟨t, hts, hsep, hbound t hts hsep, ?_⟩
  intro x hx
  by_contra hno
  have hfar : ∀ y ∈ t, r < dist x y := by
    intro y hy
    exact lt_of_not_ge (fun h => hno ⟨y, hy, h⟩)
  have hxt : x ∉ t := by
    intro hxt
    exact (not_lt_of_ge hr) (by simpa only [dist_self] using hfar x hxt)
  have hins : (↑(insert x t) : Set X) ⊆ S := by
    intro y hy
    rcases Finset.mem_insert.mp hy with hxy | hyt
    · exact hxy ▸ hx
    · exact hts hyt
  have hsepins : ∀ a ∈ insert x t, ∀ b ∈ insert x t, a ≠ b → r < dist a b := by
    intro a ha b hb hab
    rcases Finset.mem_insert.mp ha with hax | hat
    · subst a
      rcases Finset.mem_insert.mp hb with hbx | hbt
      · exact (hab hbx.symm).elim
      · exact hfar b hbt
    · rcases Finset.mem_insert.mp hb with hbx | hbt
      · subst b
        simpa only [dist_comm] using hfar a hat
      · exact hsep a hat b hbt hab
  have h := hmax (insert x t) hins hsepins
  rw [Finset.card_insert_of_notMem hxt] at h
  omega

end PolycyclicRecognition

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_LowerPacking
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Lower packing bounds from Haar volume

A totally bounded endpoint set has a finite separated net. Its volume is
at most the cardinality of that net times the mass of a fixed-radius ball.
This is the lower packing estimate used after stationary mesh selection.
-/

noncomputable section

open Metric Set MeasureTheory
open scoped ENNReal

namespace PolycyclicRecognition

/-- A totally bounded set admits a finite separated net with its centers
inside the set. The set itself need not be closed or measurable. -/
theorem exists_separated_net_of_totallyBounded
    {X : Type} [PseudoMetricSpace X] {S : Set X} (hS : TotallyBounded S)
    {r : ℝ} (hr : 0 < r) :
    ∃ t : Finset X, (↑t : Set X) ⊆ S ∧
      (∀ x ∈ t, ∀ y ∈ t, x ≠ y → r < dist x y) ∧
      ∀ x ∈ S, ∃ y ∈ t, dist x y ≤ r := by
  classical
  obtain ⟨U, _hUS, hUfin, hUcover⟩ := finite_approx_of_totallyBounded hS (r / 3) (by positivity)
  let u := hUfin.toFinset
  have hbound (t : Finset X) (ht : (↑t : Set X) ⊆ S)
      (hsep : ∀ x ∈ t, ∀ y ∈ t, x ≠ y → r < dist x y) : t.card ≤ u.card := by
    have hchoice (x : {x // x ∈ t}) : ∃ y : {y // y ∈ u}, dist x.val y.val < r / 3 := by
      obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.mp (hUcover (ht x.property))
      exact ⟨⟨y, hUfin.mem_toFinset.mpr hy⟩, Metric.mem_ball.mp hxy⟩
    choose c hc using hchoice
    have hinj : Function.Injective c := by
      intro x y hxy
      apply Subtype.ext
      by_contra hne
      have hdist : dist x.val y.val < r := by
        calc
          dist x.val y.val ≤ dist x.val (c x).val + dist (c x).val y.val := dist_triangle _ _ _
          _ = dist x.val (c x).val + dist y.val (c y).val := by rw [hxy, dist_comm (c y).val]
          _ < r := by linarith [hc x, hc y]
      exact (not_lt_of_ge hdist.le) (hsep x.val x.property y.val y.property hne)
    simpa only [Fintype.card_coe] using Fintype.card_le_of_injective c hinj
  obtain ⟨t, ht, hsep, _hcard, hcover⟩ :=
    finite_separated_cover_set_of_bound S hr.le u.card hbound
  exact ⟨t, ht, hsep, hcover⟩

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_FixedSlicePacking
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Lower packing on a fixed Cartan slice

A finite net in the ambient group pulls back to a cover of the nilpotent
parameter set. Conjugation preserving Haar makes the mass of every pulled-back
ball independent of the slice position. This is the fixed-position part of
the manuscript's lower packing argument, with no assumption on an image's
absolute continuity or multiplicity.
-/

noncomputable section

namespace PolycyclicRecognition

open MeasureTheory Metric Set
open scoped ENNReal

/-- A net of an image gives a lower cardinality bound whenever the preimage
of each covering ball has uniformly bounded mass. The source set need not be
measurable. -/
theorem exists_separated_image_net_volume_bound
    {N G : Type} [MeasurableSpace N] [PseudoMetricSpace G]
    (μ : Measure N) (f : N → G) {S : Set N}
    (hS : TotallyBounded (f '' S)) {r : ℝ} (hr : 0 < r) (C : ℝ≥0∞)
    (hball : ∀ y ∈ f '' S, μ (f ⁻¹' closedBall y r) ≤ C) :
    ∃ t : Finset G, (↑t : Set G) ⊆ f '' S ∧
      (∀ x ∈ t, ∀ y ∈ t, x ≠ y → r < dist x y) ∧
      μ S ≤ (t.card : ℝ≥0∞) * C := by
  classical
  obtain ⟨t, ht, hsep, hcover⟩ := exists_separated_net_of_totallyBounded hS hr
  refine ⟨t, ht, hsep, ?_⟩
  calc
    μ S ≤ μ (⋃ y ∈ t, f ⁻¹' closedBall y r) := measure_mono (by
      intro x hx
      obtain ⟨y, hy, hxy⟩ := hcover (f x) ⟨x, hx, rfl⟩
      exact mem_iUnion₂.mpr ⟨y, hy, hxy⟩)
    _ ≤ ∑ y ∈ t, μ (f ⁻¹' closedBall y r) := measure_biUnion_finset_le _ _
    _ ≤ ∑ _y ∈ t, C := Finset.sum_le_sum (fun y hy => hball y (ht hy))
    _ = (t.card : ℝ≥0∞) * C := by simp [nsmul_eq_mul]

variable {N D G : Type} [Group N] [Group D] [Group G]
  [MeasurableSpace N] [MetricSpace G] [IsIsometricSMul G G]
  (ι : N →* G) (κ : D →* G) (φ : D →* MulAut N)

omit [MeasurableSpace N] in
/-- Compute the entire fiber of an ambient ball on a fixed slice. The
identity-neighborhood in the nilpotent group is conjugated, then translated. -/
theorem fixedSlice_ball_preimage
    (hconj : ∀ d n, ι (φ d n) = κ d * ι n * (κ d)⁻¹)
    (x : G) (d : D) (v : N) (r : ℝ) :
    (fun u : N => x * ι u * κ d) ⁻¹' closedBall (x * ι v * κ d) r =
      (fun n => v * φ d n) '' (ι ⁻¹' closedBall (1 : G) r) := by
  ext u
  constructor
  · intro hu
    let n := φ d⁻¹ (v⁻¹ * u)
    have hn : φ d n = v⁻¹ * u := by simp [n]
    refine ⟨n, ?_, ?_⟩
    · change dist (ι n) 1 ≤ r
      have he : (x * ι v * κ d) * ι n = x * ι u * κ d := by
        have hc := hconj d n
        rw [hn] at hc
        have hh : κ d * ι n = ι (v⁻¹ * u) * κ d := by
          rw [hc]
          simp only [mul_assoc, inv_mul_cancel, mul_one]
        calc
          (x * ι v * κ d) * ι n = x * ι v * (κ d * ι n) := by simp only [mul_assoc]
          _ = x * ι v * (ι (v⁻¹ * u) * κ d) := by rw [hh]
          _ = x * ι u * κ d := by simp [mul_assoc]
      have hd := dist_mul_left (x * ι v * κ d) (ι n) 1
      rw [he, mul_one] at hd
      exact hd ▸ hu
    · simp [hn]
  · rintro ⟨n, hn, rfl⟩
    change dist (x * ι (v * φ d n) * κ d) (x * ι v * κ d) ≤ r
    rw [map_mul, hconj]
    have he : x * (ι v * (κ d * ι n * (κ d)⁻¹)) * κ d =
        (x * ι v * κ d) * ι n := by group
    rw [he]
    calc
      dist ((x * ι v * κ d) * ι n) (x * ι v * κ d) = dist (ι n) 1 := by
        simpa only [mul_one] using dist_mul_left (x * ι v * κ d) (ι n) 1
      _ ≤ r := hn

variable [MeasurableMul N]

/-- Haar mass of a slice ball depends only on its radius. In particular it
does not grow with the Cartan position or the center of the ball. -/
theorem fixedSlice_ball_measure
    (μ : Measure N) [μ.IsMulLeftInvariant]
    (hφ : ∀ d, MeasurePreserving (φ d) μ μ)
    (hconj : ∀ d n, ι (φ d n) = κ d * ι n * (κ d)⁻¹)
    (x : G) (d : D) (v : N) (r : ℝ) :
    μ ((fun u : N => x * ι u * κ d) ⁻¹' closedBall (x * ι v * κ d) r) =
      μ (ι ⁻¹' closedBall (1 : G) r) := by
  rw [fixedSlice_ball_preimage ι κ φ hconj]
  let e : N ≃ᵐ N :=
    { toEquiv :=
        { toFun := fun n => v * φ d n
          invFun := fun n => φ d⁻¹ (v⁻¹ * n)
          left_inv := by intro n; simp
          right_inv := by intro n; simp }
      measurable_toFun := (measurable_const_mul v).comp (hφ d).measurable
      measurable_invFun := (hφ d⁻¹).measurable.comp (measurable_const_mul v⁻¹) }
  have hmp : MeasurePreserving e μ μ := (measurePreserving_mul_left μ v).comp (hφ d)
  change μ (e '' _) = _
  have hm := hmp.measure_preimage_equiv (e '' (ι ⁻¹' closedBall (1 : G) r))
  rw [Set.preimage_image_eq _ e.injective] at hm
  exact hm.symm

variable [TopologicalSpace N] [ContinuousMul G]

omit [IsIsometricSMul G G] [MeasurableMul N] [ContinuousMul G] in
/-- A closed subgroup realization gives a finite packing constant at every
fixed radius, since the ambient metric is proper. -/
theorem fixedSlice_packing_constant_lt_top
    [ProperSpace G] (μ : Measure N) [IsFiniteMeasureOnCompacts μ]
    (hι : Topology.IsClosedEmbedding ι) (r : ℝ) :
    μ (ι ⁻¹' closedBall (1 : G) r) < ⊤ :=
  (hι.isProperMap.isCompact_preimage (isCompact_closedBall 1 r)).measure_lt_top

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_HaarMeasureTransfer
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Transfer of an invariant automorphism to the section-coordinate Haar measure -/

namespace PolycyclicRecognition

open MeasureTheory

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G] [LocallyCompactSpace G] [SecondCountableTopology G]

/-- A map preserving one Haar measure preserves every Haar normalization.
This permits use of the Haar measure constructed from ideal-section coordinates. -/
theorem measurePreserving_of_haarMeasure (μ ν : Measure G)
    [μ.IsHaarMeasure] [ν.IsHaarMeasure] (f : G → G)
    (hf : MeasurePreserving f μ μ) : MeasurePreserving f ν ν := by
  rw [Measure.isMulLeftInvariant_eq_smul ν μ]
  refine ⟨hf.measurable, ?_⟩
  rw [Measure.map_smul, hf.map_eq]

end PolycyclicRecognition

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_NormalizedPairPacking
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.inversePairCoupling_finiteOnCompacts _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.normalizedPairAction _root_.OAI.PolycyclicRecognition.normalizedPairContinuousAction _root_.OAI.PolycyclicRecognition.normalizedPair_polishSpace _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.normalizedPair_smul_fst _root_.OAI.PolycyclicRecognition.normalizedPair_smul_snd _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Separation and paths under an actual normalized pair -/

noncomputable section

namespace PolycyclicRecognition

open Metric
open scoped NNReal

variable {G : Type} [Group G] [MetricSpace G] {Λ : ℝ≥0}

/-- The lower metric inequality turns this fixed source separation into
unit separation in the image. -/
theorem normalizedPair_image_dist_gt_one (p : NormalizedPair G Λ)
    (hΛ : 0 < (Λ : ℝ)) {x y : G}
    (hxy : (Λ : ℝ) * ((Λ : ℝ) + 1) < dist x y) :
    1 < dist (p.val.1 x) (p.val.1 y) := by
  have hi : 0 < (Λ : ℝ)⁻¹ := inv_pos.mpr hΛ
  calc
    1 = (Λ : ℝ)⁻¹ * ((Λ : ℝ) * ((Λ : ℝ) + 1)) - Λ := by field_simp <;> ring
    _ < (Λ : ℝ)⁻¹ * dist x y - Λ := sub_lt_sub_right (mul_lt_mul_of_pos_left hxy hi) _
    _ ≤ _ := p.property.1.2.2.1 x y

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_NormalizedTuplePacking
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.inversePairCoupling_finiteOnCompacts _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.normalizedPairAction _root_.OAI.PolycyclicRecognition.normalizedPairContinuousAction _root_.OAI.PolycyclicRecognition.normalizedPair_polishSpace _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A normalized quasi-isometry preserves separated tuple counts -/

noncomputable section
namespace PolycyclicRecognition

open Metric Filter
open scoped NNReal Topology

variable {G : Type} [Group G] [MetricSpace G] {Λ : ℝ≥0}

theorem normalizedPair_tuple_dist_gt_one {h : ℕ} (p : NormalizedPair G Λ)
    (hΛ : 0 < (Λ : ℝ)) {u v : Fin h → G}
    (huv : (Λ : ℝ) * ((Λ : ℝ) + 1) < dist u v) :
    1 < dist (fun i => p.val.1 (u i)) (fun i => p.val.1 (v i)) := by
  have hρ : 0 ≤ (Λ : ℝ) * ((Λ : ℝ) + 1) := by positivity
  have hi : ∃ i, (Λ : ℝ) * ((Λ : ℝ) + 1) < dist (u i) (v i) := by
    by_contra hn
    push Not at hn
    exact (not_le_of_gt huv) ((dist_pi_le_iff hρ).mpr hn)
  obtain ⟨i, hi⟩ := hi
  exact (normalizedPair_image_dist_gt_one p hΛ hi).trans_le
    (dist_le_pi_dist (fun i : Fin h => p.val.1 (u i)) (fun i : Fin h => p.val.1 (v i)) i)

variable [DecidableEq G]

theorem normalizedPair_tuple_image_card_separated {h : ℕ} (p : NormalizedPair G Λ)
    (hΛ : 0 < (Λ : ℝ)) (s : Finset (Fin h → G))
    (hsep : ∀ x ∈ s, ∀ y ∈ s, x ≠ y → (Λ : ℝ) * ((Λ : ℝ) + 1) < dist x y) :
    let t := s.image (fun u i => p.val.1 (u i))
    t.card = s.card ∧ ∀ x ∈ t, ∀ y ∈ t, x ≠ y → 1 ≤ dist x y := by
  classical
  dsimp only
  constructor
  · apply Finset.card_image_iff.mpr
    intro x hx y hy he
    by_contra hne
    have hd := normalizedPair_tuple_dist_gt_one p hΛ (hsep x hx y hy hne)
    dsimp only at he
    rw [he, dist_self] at hd
    linarith
  · intro x hx y hy hxy
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hy
    have huv : u ≠ v := fun he => hxy (congrArg (fun w i => p.val.1 (w i)) he)
    exact (normalizedPair_tuple_dist_gt_one p hΛ (hsep u hu v hv huv)).le

theorem normalizedPair_tuple_count_rate {h : ℕ} (p : ℕ → NormalizedPair G Λ)
    (hΛ : 0 < (Λ : ℝ)) (s : ℕ → Finset (Fin h → G))
    (hsep : ∀ n, ∀ x ∈ s n, ∀ y ∈ s n, x ≠ y →
      (Λ : ℝ) * ((Λ : ℝ) + 1) < dist x y)
    {scale : ℕ → ℝ} {a : ℝ}
    (hcount : HasSubexponentialLowerBoundSeq scale
      (fun n => ((s n).card : ℝ) / Real.exp (scale n * a))) :
    let t := fun n => (s n).image (fun u i => (p n).val.1 (u i))
    (∀ n, ∀ x ∈ t n, ∀ y ∈ t n, x ≠ y → 1 ≤ dist x y) ∧
      HasSubexponentialLowerBoundSeq scale
        (fun n => ((t n).card : ℝ) / Real.exp (scale n * a)) := by
  classical
  have ht (n : ℕ) := normalizedPair_tuple_image_card_separated (p n) hΛ (s n) (hsep n)
  exact ⟨fun n => (ht n).2, by simpa only [(ht _).1] using hcount⟩

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_TupleFixedSlicePacking
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Fixed-slice lower packing for correlated tuples

An ambient product ball pulls back to a product of fixed-slice balls.  The
set to be packed need not be a product set.
-/

noncomputable section
namespace PolycyclicRecognition

open MeasureTheory Metric Set Filter
open scoped ENNReal Topology

theorem lower_count_rate_of_volume
    {scale : ℕ → ℝ} (hs : Tendsto scale atTop atTop)
    (A : ℕ → ℝ≥0∞) (N : ℕ → ℕ) (C : ℝ≥0∞) (hC : C ≠ ⊤) {p : ℝ}
    (hvol : HasSubexponentialLowerBoundSeq scale
      (fun n => (A n).toReal / Real.exp (scale n * p)))
    (hbound : ∀ n, A n ≤ (N n : ℝ≥0∞) * C) :
    HasSubexponentialLowerBoundSeq scale
      (fun n => (N n : ℝ) / Real.exp (scale n * p)) := by
  have hc : 0 < C.toReal + 1 := by positivity
  apply (hvol.div (sequence_subexponential_upper_const hs (C.toReal + 1))
    (Eventually.of_forall (fun _ => hc))).mono
  apply Eventually.of_forall
  intro n
  have hb := ENNReal.toReal_mono
    (ENNReal.mul_ne_top (by simp) hC) (hbound n)
  simp only [ENNReal.toReal_mul, ENNReal.toReal_natCast] at hb
  dsimp only
  rw [div_right_comm]
  apply div_le_div_of_nonneg_right _ (Real.exp_pos _).le
  apply (div_le_iff₀ hc).mpr
  have hN : 0 ≤ (N n : ℝ) := Nat.cast_nonneg _
  nlinarith

variable {N D G : Type} [Group N] [Group D] [Group G]
  [TopologicalSpace N] [MeasurableSpace N] [MeasurableMul N]
  [MetricSpace G] [IsTopologicalGroup G] [IsIsometricSMul G G]
  (ι : N →* G) (κ : D →* G) (φ : D →* MulAut N)
  (μ : Measure N) [SigmaFinite μ] [μ.IsMulLeftInvariant]

omit [TopologicalSpace N] [IsTopologicalGroup G] in
theorem tuple_fixedSlice_ball_measure {h : ℕ}
    (hφ : ∀ d, MeasurePreserving (φ d) μ μ)
    (hconj : ∀ d n, ι (φ d n) = κ d * ι n * (κ d)⁻¹)
    (x : Fin h → G) (d : Fin h → D) (v : Fin h → N) {r : ℝ} (hr : 0 ≤ r) :
    (Measure.pi fun _ : Fin h => μ)
      ((fun u : Fin h → N => fun i => x i * ι (u i) * κ (d i)) ⁻¹'
        closedBall (fun i => x i * ι (v i) * κ (d i)) r) =
      μ (ι ⁻¹' closedBall (1 : G) r) ^ h := by
  have he : (fun u : Fin h → N => fun i => x i * ι (u i) * κ (d i)) ⁻¹'
      closedBall (fun i => x i * ι (v i) * κ (d i)) r =
      Set.pi univ (fun i =>
        (fun u : N => x i * ι u * κ (d i)) ⁻¹' closedBall (x i * ι (v i) * κ (d i)) r) := by
    ext u
    simp only [mem_preimage, mem_closedBall, dist_pi_le_iff hr, Set.mem_pi, mem_univ,
      forall_const]
  rw [he, Measure.pi_pi]
  simp_rw [fixedSlice_ball_measure ι κ φ μ hφ hconj]
  simp

theorem exists_tuple_fixedSlice_separated_net {h : ℕ}
    (hφ : ∀ d, MeasurePreserving (φ d) μ μ)
    (hconj : ∀ d n, ι (φ d n) = κ d * ι n * (κ d)⁻¹)
    (hι : Continuous ι) (x : Fin h → G) (d : Fin h → D)
    {S : Set (Fin h → N)} (hS : IsCompact S) {r : ℝ} (hr : 0 < r) :
    ∃ t : Finset (Fin h → G),
      (↑t : Set (Fin h → G)) ⊆ (fun u => fun i => x i * ι (u i) * κ (d i)) '' S ∧
      (∀ a ∈ t, ∀ b ∈ t, a ≠ b → r < dist a b) ∧
      (Measure.pi fun _ : Fin h => μ) S ≤
        (t.card : ℝ≥0∞) * μ (ι ⁻¹' closedBall (1 : G) r) ^ h := by
  apply exists_separated_image_net_volume_bound (Measure.pi fun _ : Fin h => μ) _
    (hS.image (continuous_pi (fun i =>
      (continuous_const.mul (hι.comp (continuous_apply i))).mul continuous_const))).totallyBounded hr
  rintro y ⟨v, _, rfl⟩
  exact (tuple_fixedSlice_ball_measure ι κ φ μ hφ hconj x d v hr.le).le

theorem exists_tuple_fixedSlice_count_rate {h : ℕ} [ProperSpace G]
    [IsFiniteMeasureOnCompacts μ]
    (hφ : ∀ d, MeasurePreserving (φ d) μ μ)
    (hconj : ∀ d n, ι (φ d n) = κ d * ι n * (κ d)⁻¹)
    (hι : Topology.IsClosedEmbedding ι)
    {scale : ℕ → ℝ} (hs : Tendsto scale atTop atTop)
    (x : ℕ → Fin h → G) (d : ℕ → Fin h → D)
    (S : ℕ → Set (Fin h → N)) (hS : ∀ n, IsCompact (S n))
    {p : ℝ} (hvol : HasSubexponentialLowerBoundSeq scale
      (fun n => ((Measure.pi fun _ : Fin h => μ) (S n)).toReal / Real.exp (scale n * p)))
    {r : ℝ} (hr : 0 < r) :
    ∃ t : ℕ → Finset (Fin h → G),
      (∀ n, (↑(t n) : Set (Fin h → G)) ⊆
        (fun u => fun i => x n i * ι (u i) * κ (d n i)) '' S n) ∧
      (∀ n, ∀ a ∈ t n, ∀ b ∈ t n, a ≠ b → r < dist a b) ∧
      HasSubexponentialLowerBoundSeq scale
        (fun n => ((t n).card : ℝ) / Real.exp (scale n * p)) := by
  choose t ht hsep hbound using fun n =>
    exists_tuple_fixedSlice_separated_net ι κ φ μ hφ hconj hι.continuous (x n) (d n) (hS n) hr
  refine ⟨t, ht, hsep, lower_count_rate_of_volume hs _ _ _ ?_ hvol hbound⟩
  exact ENNReal.pow_ne_top (fixedSlice_packing_constant_lt_top ι μ hι r).ne

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanResidualAction
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial bounds for the residual Cartan action

On an actual generalized root space, subtracting its scalar character leaves
an operator nilpotent in a uniform dimension bound. Its exponential therefore
has polynomial growth in the Cartan parameter. This supplies the residual
operator estimate used in box conjugation.
-/

noncomputable section

namespace PolycyclicRecognition

open LieAlgebra LieModule Module

set_option maxHeartbeats 1000000 in
/-- Split an arbitrary scalar character from an operator exponential. -/
theorem exp_eq_scalar_smul_residual
    {A : Type} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
    (a : ℝ) (X : A) :
    NormedSpace.exp X = Real.exp a • NormedSpace.exp (X - a • 1) := by
  let : NormedAlgebra ℚ A := NormedAlgebra.restrictScalars ℚ ℝ A
  have hc : Commute (a • (1 : A)) (X - a • 1) := by
    simpa only [Algebra.algebraMap_eq_smul_one] using
      Algebra.commute_algebraMap_left a (X - a • 1)
  have he : NormedSpace.exp (a • (1 : A)) = Real.exp a • (1 : A) := by
    simpa only [Real.exp_eq_exp_ℝ, Algebra.algebraMap_eq_smul_one] using
      (NormedSpace.algebraMap_exp_comm (𝕂 := ℝ) (𝔸 := A) a).symm
  conv_lhs => rw [show X = a • 1 + (X - a • 1) by module]
  rw [NormedSpace.exp_add_of_commute hc, he, smul_mul_assoc, one_mul]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanResidualBounds
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.CartanFactorModel.heightRay_zero _root_.OAI.PolycyclicRecognition.CartanFactorModel.realScaleProfile_apply _root_.OAI.PolycyclicRecognition.CartanFactorModel.sampledProbeProfile_apply _root_.OAI.PolycyclicRecognition.cartanWeightDerivation_apply_root _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.nilshadowWeightDerivation_symm _root_.OAI.PolycyclicRecognition.nilshadowWeightOperator_symm _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Bounds for the actual residual automorphism

We identify the residual automorphism on a nonzero root with the analytic
exponential already estimated there. This removes a separate bound premise
for the automorphisms constructed from the Cartan action.
-/

noncomputable section

namespace PolycyclicRecognition

open Module LieAlgebra LieModule
open scoped BigOperators

variable {L : Type} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {n : ℕ} (T : TriangularAdjoint L n)
  (H : LieSubalgebra ℝ L) [H.IsCartanSubalgebra] (χ : Weight ℝ H L) (hχ : χ.IsNonZero)

attribute [local instance] OAI.PolycyclicRecognition.instNormedAddCommGroupSubtypeMemLieSubmoduleRealLieSubalgebraRootSpaceCoeWeight_solutions_1
attribute [local instance] OAI.PolycyclicRecognition.instNormedSpaceRealSubtypeMemLieSubmoduleLieSubalgebraRootSpaceCoeWeight_solutions_1
local instance instNontrivialSubtypeMemLieSubmoduleRealLieSubalgebraRootSpaceCoeWeight_solutions_1_r927516_1 : Nontrivial (rootSpace H χ) :=
  (LieSubmodule.nontrivial_iff_ne_bot ℝ H L).mpr χ.genWeightSpace_ne_bot
set_option maxHeartbeats 1000000 in
/-- Inclusion intertwines the root residual operator and the actual ideal
derivation. -/
theorem rootInIdeal_residual_apply (h : H) (v : rootSpace H χ) :
    CartanWordModel.rootInIdeal χ hχ ((rootAction H χ h - χ h • 1) v) =
      cartanIdealResidualDerivation T H h (CartanWordModel.rootInIdeal χ hχ v) := by
  apply Subtype.ext
  change (((rootAction H χ h - χ h • 1) v : rootSpace H χ) : L) =
    cartanResidualDerivation T H h (v : L)
  rw [cartanResidualDerivation_apply_root T H h χ v.property]
  rfl

set_option maxHeartbeats 1000000 in
theorem rootInIdeal_residual_pow (h : H) (k : ℕ) (v : rootSpace H χ) :
    CartanWordModel.rootInIdeal χ hχ (((rootAction H χ h - χ h • 1) ^ k) v) =
      ((cartanIdealResidualDerivation T H h).toLinearMap ^ k)
        (CartanWordModel.rootInIdeal χ hχ v) := by
  induction k generalizing v with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ, mul_apply_eq_comp, ih, rootInIdeal_residual_apply,
      pow_succ, Module.End.mul_apply]
    rfl

set_option maxHeartbeats 1000000 in
include T hχ in
/-- The ambient dimension also truncates the analytic root operator. -/
theorem rootResidual_pow_ambient_dim (h : H) :
    (rootAction H χ h - χ h • 1) ^ finrank ℝ L = 0 := by
  apply ContinuousLinearMap.ext
  intro v
  have hinj : Function.Injective (CartanWordModel.rootInIdeal χ hχ) := by
    intro x y hxy
    exact Subtype.ext (congrArg (fun z : cartanRootIdeal H => (z : L)) hxy)
  apply hinj
  rw [rootInIdeal_residual_pow T H χ hχ h (finrank ℝ L) v,
    cartanIdealResidualDerivation_pow_eq_zero T H h]
  simp

set_option maxHeartbeats 1000000 in
/-- The polynomial Lie automorphism agrees with the analytic root residual
exponential, so the earlier operator norm bounds apply to this automorphism. -/
theorem rootInIdeal_residual_exp (h : H) (v : rootSpace H χ) :
    CartanWordModel.rootInIdeal χ hχ ((NormedSpace.exp (rootAction H χ h - χ h • 1)) v) =
      cartanIdealResidualAutomorphism T H h (CartanWordModel.rootInIdeal χ hχ v) := by
  rw [exp_eq_finite_sum_of_pow_eq_zero _ (rootResidual_pow_ambient_dim T H χ hχ h),
    cartanIdealResidualAutomorphism_apply]
  simp only [sum_apply, smul_apply, map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro k _
  rw [rootInIdeal_residual_pow]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_RootRepresentation
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Root distortion in a faithful integrated representation

The conjugation identity is proved from a Lie homomorphism into a normed
algebra and the ordinary exponential matching identities. It is not an
additional geometric hypothesis.
-/

noncomputable section

namespace PolycyclicRecognition

open LieAlgebra LieModule

attribute [local instance 100] LieRing.ofAssociativeRing
attribute [local instance] rootNormedAddCommGroup rootNormedSpace rootNontrivial

variable {L : Type} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {A : Type} [NormedRing A] [NormedAlgebra ℝ A]
  (H : LieSubalgebra ℝ L) [H.IsCartanSubalgebra] (χ : Weight ℝ H L)
  (j : L →ₗ⁅ℝ⁆ A)

theorem representedRootVector_intertwines (h : H) (v : rootSpace H χ) :
    representedRootVector H χ j (rootAction H χ h v) =
      adjointOperator (j h) (representedRootVector H χ j v) := by
  change j ⁅(h : L), (v : L)⁆ = j h * j v - j v * j h
  rw [j.map_lie, Ring.lie_def]

variable [CompleteSpace A]

/-- The restricted root action exponentiates to actual matrix conjugation. -/
theorem represented_root_flow (h : H) (t : ℝ) (v : rootSpace H χ) :
    representedRootVector H χ j ((NormedSpace.exp (t • rootAction H χ h)) v) =
      NormedSpace.exp (t • j h) * j v * NormedSpace.exp (-(t • j h)) := by
  have hi := exp_intertwine_apply (representedRootVector H χ j)
    (t • rootAction H χ h) (t • adjointOperator (j h)) (by
      intro v
      simp only [smul_apply, map_smul, representedRootVector_intertwines]) v
  rw [exp_smul_adjointOperator_apply] at hi
  exact hi

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanAdjointAction
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The full exponential Cartan action

The scalar dilation and the polynomial residual automorphism together give
the exponential of the actual adjoint action on every nonzero root. In a
compatible faithful representation this is conjugation, not an independently
assumed action on the nilpotent ideal.
-/

noncomputable section

namespace PolycyclicRecognition

open Module LieAlgebra LieModule

variable {L : Type} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {n : ℕ} (T : TriangularAdjoint L n)
  (H : LieSubalgebra ℝ L) [H.IsCartanSubalgebra]

variable (χ : Weight ℝ H L) (hχ : χ.IsNonZero)

attribute [local instance] OAI.PolycyclicRecognition.instNormedAddCommGroupSubtypeMemLieSubmoduleRealLieSubalgebraRootSpaceCoeWeight_solutions_2
attribute [local instance] OAI.PolycyclicRecognition.instNormedSpaceRealSubtypeMemLieSubmoduleLieSubalgebraRootSpaceCoeWeight_solutions_2
local instance instNontrivialSubtypeMemLieSubmoduleRealLieSubalgebraRootSpaceCoeWeight_solutions_2_r927516_1 : Nontrivial (rootSpace H χ) :=
  (LieSubmodule.nontrivial_iff_ne_bot ℝ H L).mpr χ.genWeightSpace_ne_bot
set_option maxHeartbeats 1000000 in
/-- The full action is the analytic adjoint exponential on each nonzero root. -/
theorem rootInIdeal_adjoint_exp (h : H) (v : rootSpace H χ) :
    CartanWordModel.rootInIdeal χ hχ ((NormedSpace.exp (rootAction H χ h)) v) =
      cartanIdealAdjointAutomorphism T H h (CartanWordModel.rootInIdeal χ hχ v) := by
  rw [exp_eq_scalar_smul_residual (χ h) (rootAction H χ h),
    smul_apply, map_smul, rootInIdeal_residual_exp T H χ hχ h v]
  apply Subtype.ext
  change Real.exp (χ h) •
      (cartanIdealResidualAutomorphism T H h (CartanWordModel.rootInIdeal χ hχ v) : L) =
    cartanWeightScale T H h _
  exact (cartanWeightScale_apply_root T H h χ
    (cartanIdealResidualAutomorphism_root_mem T H h χ _ v.property)).symm

section Representation

variable {A : Type} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

attribute [local instance 100] LieRing.ofAssociativeRing

attribute [local instance] OAI.PolycyclicRecognition.instNormedAddCommGroupSubtypeMemLieSubmoduleRealLieSubalgebraRootSpaceCoeWeight_solutions_2
attribute [local instance] OAI.PolycyclicRecognition.instNormedSpaceRealSubtypeMemLieSubmoduleLieSubalgebraRootSpaceCoeWeight_solutions_2
local instance instNontrivialSubtypeMemLieSubmoduleRealLieSubalgebraRootSpaceCoeWeight_solutions_2_r927516_2 : Nontrivial (rootSpace H χ) :=
  (LieSubmodule.nontrivial_iff_ne_bot ℝ H L).mpr χ.genWeightSpace_ne_bot
set_option maxHeartbeats 1000000 in
/-- The constructed action agrees with conjugation in a compatible algebra
representation on every generating root. -/
theorem represented_adjoint_root (j : L →ₗ⁅ℝ⁆ A) (h : H) (v : rootSpace H χ) :
    j (cartanIdealAdjointAutomorphism T H h (CartanWordModel.rootInIdeal χ hχ v) : L) =
      NormedSpace.exp (j h) * j v * NormedSpace.exp (-j h) := by
  rw [← rootInIdeal_adjoint_exp T H χ hχ h v]
  have hh := represented_root_flow H χ j h 1 v
  simp only [one_smul] at hh
  exact hh

set_option maxHeartbeats 1000000 in
omit hχ χ in
/-- Lie generation extends the root calculation to every vector in the
nilpotent ideal. -/
theorem represented_adjoint_ideal (j : L →ₗ⁅ℝ⁆ A) (h : H) (x : cartanRootIdeal H) :
    j (cartanIdealAdjointAutomorphism T H h x : L) =
      NormedSpace.exp (j h) * j x * NormedSpace.exp (-j h) := by
  let u := algebraExpUnit (j h)
  change j (cartanIdealAdjointAutomorphism T H h x : L) =
    (u : A) * j x * (↑(u⁻¹) : A)
  have hx : x ∈ LieSubalgebra.lieSpan ℝ (cartanRootIdeal H) (cartanGeneratorPool H) := by
    rw [cartanGeneratorPool_lieSpan H T]
    trivial
  have hmul (a b : A) :
      ((u : A) * a * (↑(u⁻¹) : A)) * ((u : A) * b * (↑(u⁻¹) : A)) =
        (u : A) * (a * b) * (↑(u⁻¹) : A) := by
    calc
      _ = (u : A) * a * ((↑(u⁻¹) : A) * u) * b * (↑(u⁻¹) : A) := by
        simp only [mul_assoc]
      _ = _ := by simp only [Units.inv_mul, mul_one, mul_assoc]
  induction hx using LieSubalgebra.lieSpan_induction with
  | mem x hx =>
    obtain ⟨ψ, hψ, hx⟩ := hx
    have he : CartanWordModel.rootInIdeal ψ hψ ⟨x, hx⟩ = x := Subtype.ext rfl
    have hh := represented_adjoint_root T H ψ hψ j h ⟨x, hx⟩
    rw [he] at hh
    exact hh
  | zero => simp only [map_zero, ZeroMemClass.coe_zero, mul_zero, zero_mul]
  | add x y _ _ hx hy =>
    simpa only [map_add, AddMemClass.coe_add, mul_add, add_mul] using congrArg₂ (· + ·) hx hy
  | smul a x _ hx =>
    simpa only [map_smul, SetLike.val_smul, smul_mul_assoc, mul_smul_comm,
      RingHom.id_apply] using congrArg (a • ·) hx
  | lie x y _ _ hx hy =>
    rw [LieEquiv.map_lie]
    change j ⁅(cartanIdealAdjointAutomorphism T H h x : L),
      (cartanIdealAdjointAutomorphism T H h y : L)⁆ =
        (u : A) * j ⁅(x : L), (y : L)⁆ * (↑(u⁻¹) : A)
    rw [j.map_lie, j.map_lie, hx, hy]
    simp only [Ring.lie_def, mul_sub, sub_mul, hmul]

end Representation

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanActualConjugation
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instDecidableEqConeMixedWords _root_.OAI.PolycyclicRecognition.CartanWordModel.instFintypeConeMixedWords _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual Cartan conjugation and shifted boxes

The full Lie action integrates to the nilpotent group. A faithful compatible
representation identifies this automorphism with ambient conjugation. The
resulting box estimate retains the polynomial residual factor and the exact
canonical-height translation.
-/

noncomputable section

namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule
open scoped Manifold

variable {L : Type} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {H : LieSubalgebra ℝ L} [H.IsCartanSubalgebra] (M : CartanWordModel H)
  {n : ℕ} (T : TriangularAdjoint L n)
  {EN N : Type} [NormedAddCommGroup EN] [NormedSpace ℝ EN]
  [FiniteDimensional ℝ EN] [TopologicalSpace N] [ChartedSpace EN N] [Group N]
  [LieGroup (𝓘(ℝ, EN)) ⊤ N] [T2Space N]
  (eN : cartanRootIdeal H ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, EN)) N)
  (Exp : GroupLieAlgebra (𝓘(ℝ, EN)) N → N) (hExp : IsGroupExponential Exp)
  (hbij : Function.Bijective Exp) (dynkin : NilpotentDynkinExpansionInput EN N)

section Representation

variable {A G : Type} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A] [Group G]

attribute [local instance 100] LieRing.ofAssociativeRing

set_option maxHeartbeats 1000000 in
/-- Compatibility of exponentials in a faithful representation identifies
the constructed automorphism with actual ambient conjugation. -/
theorem adjointGroupAutomorphism_eq_conjugation
    (j : L →ₗ⁅ℝ⁆ A) (ρ : G →* Aˣ) (hρ : Function.Injective ρ)
    (ι : N →* G) (d : H → G)
    (hN : ∀ x : cartanRootIdeal H, ρ (ι (Exp (eN x))) = algebraExpUnit (j x))
    (hd : ∀ h, ρ (d h) = algebraExpUnit (j h)) (h : H) (g : N) :
    ι (M.adjointGroupAutomorphism T eN Exp hExp hbij dynkin h g) =
      d h * ι g * (d h)⁻¹ := by
  obtain ⟨x, rfl⟩ := (hbij.comp eN.bijective).surjective g
  apply hρ
  change ρ (ι (integrateNilpotentLieEquiv eN Exp hbij dynkin hExp M.bound_zero
    (cartanIdealAdjointAutomorphism T H h) (Exp (eN x)))) = _
  rw [integrateNilpotentLieEquiv_apply_exp, hN, map_mul, map_mul, map_inv, hd]
  change algebraExpUnit (j (cartanIdealAdjointAutomorphism T H h x : L)) =
    algebraExpUnit (j h) * ρ (ι (Exp (eN x))) * (algebraExpUnit (j h))⁻¹
  rw [hN]
  rw [represented_adjoint_ideal T H j h x]
  exact algebraExpUnit_conj (algebraExpUnit (j h)) (j x)

end Representation

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanSourceIntervals
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instDecidableEqConeMixedWords _root_.OAI.PolycyclicRecognition.CartanWordModel.instFintypeConeMixedWords _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Source generator intervals fit in the containing template box -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra

variable {L W : Type} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {H : LieSubalgebra ℝ L} [H.IsCartanSubalgebra] (M : CartanWordModel H)
  {a : ℕ} (T : TriangularAdjoint L a)
  (hunimod : ∀ x : L, LinearMap.trace ℝ L (ad ℝ L x) = 0)
  [NormedAddCommGroup W] [NormedSpace ℝ W] (eW : HeightSpace T.character ≃ₗ[ℝ] W)

set_option maxHeartbeats 1000000 in
theorem exists_source_interval_box_bound
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (E : Set W) (β : M.Bases),
      IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
        (M.boxCost T hunimod eW E) β.val →
      ∀ (s : Fin M.letterCount → ℝ),
        (∀ i, s i ≤ (M.supportIn T hunimod eW).weightSupport E i) →
      ∀ {N : Type} (Exp : cartanRootIdeal H → N) (r R : ℝ), 0 ≤ r → 0 ≤ R →
      ∀ (i : Fin M.letterCount) (t : ℝ), |t| ≤ R →
        Exp (t • (Real.exp (r * s i) • M.letter i)) ∈
          M.groupBox T hunimod eW Exp E β r (C * R) := by
  obtain ⟨C, hC, hgen⟩ := exists_uniform_rescaled_generator_bound M.letter M.wordList
    M.letter_mem_wordList b₀
  refine ⟨C, hC, ?_⟩
  intro E β hβ s hs N Exp r R hr hR i t ht
  let w := (M.supportIn T hunimod eW).weightSupport E
  let q := Real.exp (r * (s i - w i))
  have hq0 : 0 < q := Real.exp_pos _
  have hq1 : q ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    exact mul_nonpos_of_nonneg_of_nonpos hr (sub_nonpos.mpr (hs i))
  have hvec : ‖(M.boxBasis T hunimod eW E β r).equivFun
      (Real.exp (r * w i) • M.letter i)‖ ≤ C :=
    hgen w β hβ r hr i
  have he : t • (Real.exp (r * s i) • M.letter i) =
      (t * q) • (Real.exp (r * w i) • M.letter i) := by
    have hscalar : Real.exp (r * s i) = q * Real.exp (r * w i) := by
      dsimp only [q]
      rw [← Real.exp_add]
      congr 1
      ring
    simpa only [smul_smul, mul_assoc] using
      congrArg (fun a : ℝ => (t * a) • M.letter i) hscalar
  refine ⟨t • (Real.exp (r * s i) • M.letter i), rfl, ?_⟩
  rw [he, map_smul, norm_smul, Real.norm_eq_abs, abs_mul, abs_of_pos hq0, mul_assoc]
  have hb : q * ‖(M.boxBasis T hunimod eW E β r).equivFun
      (Real.exp (r * w i) • M.letter i)‖ ≤ C := by
    exact (mul_le_mul hq1 hvec (norm_nonneg _) zero_le_one).trans_eq (one_mul C)
  calc
    _ ≤ R * C := mul_le_mul ht hb (mul_nonneg hq0.le (norm_nonneg _)) hR
    _ = C * R := mul_comm _ _

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_SequenceCartanConjugationBoxes
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instDecidableEqConeMixedWords _root_.OAI.PolycyclicRecognition.CartanWordModel.instFintypeConeMixedWords _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.CartanFactorModel.heightRay_zero _root_.OAI.PolycyclicRecognition.CartanFactorModel.realScaleProfile_apply _root_.OAI.PolycyclicRecognition.CartanFactorModel.sampledProbeProfile_apply _root_.OAI.PolycyclicRecognition.bracketWordDifferential_mul _root_.OAI.PolycyclicRecognition.cartanWeightDerivation_apply_root _root_.OAI.PolycyclicRecognition.cartanWeightDilation_apply _root_.OAI.PolycyclicRecognition.cartanWeightScale_add_apply _root_.OAI.PolycyclicRecognition.cartanWeightScale_zero_apply _root_.OAI.PolycyclicRecognition.chartExponentialFlow_zero _root_.OAI.PolycyclicRecognition.derivationSemidirectHom_apply _root_.OAI.PolycyclicRecognition.exponentialHomOfDynkin_apply_exp _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.integrateNilpotentLieEquiv_apply_exp _root_.OAI.PolycyclicRecognition.nilshadowWeightDerivation_symm _root_.OAI.PolycyclicRecognition.nilshadowWeightOperator_symm _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The two conjugations in a coupled recurrence remain in one source box -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra Filter Set
open scoped Manifold Topology

variable {L W : Type} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {H : LieSubalgebra ℝ L} [H.IsCartanSubalgebra] (M : CartanWordModel H)
  {a : ℕ} (T : TriangularAdjoint L a)
  (hunimod : ∀ x : L, LinearMap.trace ℝ L (ad ℝ L x) = 0)
  [NormedAddCommGroup W] [NormedSpace ℝ W] (eW : HeightSpace T.character ≃ₗ[ℝ] W)
  {EN N : Type} [NormedAddCommGroup EN] [NormedSpace ℝ EN]
  [FiniteDimensional ℝ EN] [TopologicalSpace N] [ChartedSpace EN N] [Group N]
  [LieGroup (𝓘(ℝ, EN)) ⊤ N] [T2Space N]
  (eN : cartanRootIdeal H ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, EN)) N)
  (Exp : GroupLieAlgebra (𝓘(ℝ, EN)) N → N) (hExp : IsGroupExponential Exp)

set_option maxHeartbeats 1000000 in
include hExp in
theorem exists_sequence_double_conjugate_box
    (dynkin : NilpotentDynkinExpansionInput EN N)
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (E : Set W) (β : M.Bases)
    (hβ : IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
      (M.boxCost T hunimod eW E) β.val)
    (scale R : ℕ → ℝ) (hs : Tendsto scale atTop atTop)
    (hscale : ∀ n, 0 ≤ scale n) (hR0 : ∀ n, 0 ≤ R n)
    (hR : HasSubexponentialUpperBoundSeq scale R) :
    ∃ V : ℕ → ℝ, (∀ n, 0 ≤ V n) ∧ HasSubexponentialUpperBoundSeq scale V ∧
      ∀ n (k₀ k g : N),
        k₀ ∈ M.groupBox T hunimod eW (Exp ∘ eN) E β (scale n) (R n) →
        k ∈ M.groupBox T hunimod eW (Exp ∘ eN) E β (scale n) (R n) →
        g ∈ M.groupBox T hunimod eW (Exp ∘ eN) E β (scale n) (R n) →
        k₀ * (k * g * k⁻¹) * k₀⁻¹ ∈
          M.groupBox T hunimod eW (Exp ∘ eN) E β (scale n) (V n) := by
  obtain ⟨C, hC, hprod⟩ := M.exists_groupBox_product_bound T hunimod eW eN Exp hExp dynkin b₀
  let V := fun n => C * 6 ^ M.bound * (1 + R n) ^ M.bound
  have hp := ((sequence_subexponential_upper_const hs 1).add hR hs).pow hs
    (Eventually.of_forall (fun n => by linarith [hR0 n])) M.bound
  refine ⟨V, fun n => by have := hR0 n; dsimp [V] <;> positivity,
    (sequence_subexponential_upper_const hs (C * 6 ^ M.bound)).mul hp
      (Eventually.of_forall (fun _ => by positivity)), ?_⟩
  intro n k₀ k g hk₀ hk hg
  have hki := M.groupBox_inv_mem T hunimod eW eN Exp hExp E β (scale n) (R n) hk
  have hk₀i := M.groupBox_inv_mem T hunimod eW eN Exp hExp E β (scale n) (R n) hk₀
  have hv := hprod E β hβ (scale n) (hscale n) 5 (R n) (hR0 n)
    ![k₀, k, g, k⁻¹, k₀⁻¹] (by intro i; fin_cases i <;> assumption)
  simpa only [List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.head_cons, mul_one, mul_assoc,
    Nat.cast_ofNat, V, show (1 : ℝ) + 5 = 6 from by norm_num] using hv

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_ExponentialBoxMass
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Positive finite mass of the unit box in an arbitrary exponential basis -/

noncomputable section
namespace PolycyclicRecognition

open Module MeasureTheory Set
open scoped Manifold ENNReal

variable {L E G : Type} [LieRing L] [LieAlgebra ℝ L]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace G] [ChartedSpace E G] [Group G]
  [LieGroup (𝓘(ℝ, E)) ⊤ G] [MeasurableSpace G] [BorelSpace G]

theorem exponential_box_unit_mass
    (e : L ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, E)) G)
    (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G)
    (chart : GroupLieAlgebra (𝓘(ℝ, E)) G ≃ₜ G) (hchart : ∀ x, chart x = Exp x)
    {n : ℕ} (b₀ b : Basis (Fin n) ℝ L) :
    let μ := Measure.map ((Exp ∘ e) ∘ b₀.equivFun.symm) volume
    μ (exponentialCoordinateBox (Exp ∘ e) b 1) ≠ ∞ ∧
      0 < (μ (exponentialCoordinateBox (Exp ∘ e) b 1)).toReal := by
  have hd : (b₀.toMatrix b).det ≠ 0 := by
    have hh := congrArg Matrix.det (b₀.toMatrix_mul_toMatrix_flip b)
    rw [Matrix.det_mul, Matrix.det_one] at hh
    intro hz
    rw [hz, zero_mul] at hh
    exact zero_ne_one hh
  have he : (Measure.map ((Exp ∘ e) ∘ b₀.equivFun.symm) volume)
      (exponentialCoordinateBox (Exp ∘ e) b 1) =
      ENNReal.ofReal |(b₀.toMatrix b).det| * ENNReal.ofReal 2 ^ n := by
    rw [exponentialCoordinateBox_eq_cube_image _ _ 1 zero_le_one,
      exponential_basis_subset_measure e Exp chart hchart, Real.volume_Icc_pi]
    simp <;> norm_num
  dsimp only
  rw [he]
  constructor
  · exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
  · rw [ENNReal.toReal_mul, ENNReal.toReal_pow,
      ENNReal.toReal_ofReal (abs_nonneg _), ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 2)]
    exact mul_pos (abs_pos.mpr hd) (pow_pos (by norm_num) _)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_SequenceCartanRecurrenceBoxes
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instDecidableEqConeMixedWords _root_.OAI.PolycyclicRecognition.CartanWordModel.instFintypeConeMixedWords _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.CartanFactorModel.heightRay_zero _root_.OAI.PolycyclicRecognition.CartanFactorModel.realScaleProfile_apply _root_.OAI.PolycyclicRecognition.CartanFactorModel.sampledProbeProfile_apply _root_.OAI.PolycyclicRecognition.bracketWordDifferential_mul _root_.OAI.PolycyclicRecognition.cartanWeightDerivation_apply_root _root_.OAI.PolycyclicRecognition.cartanWeightDilation_apply _root_.OAI.PolycyclicRecognition.cartanWeightScale_add_apply _root_.OAI.PolycyclicRecognition.cartanWeightScale_zero_apply _root_.OAI.PolycyclicRecognition.chartExponentialFlow_zero _root_.OAI.PolycyclicRecognition.derivationSemidirectHom_apply _root_.OAI.PolycyclicRecognition.exponentialHomOfDynkin_apply_exp _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.integrateNilpotentLieEquiv_apply_exp _root_.OAI.PolycyclicRecognition.nilshadowWeightDerivation_symm _root_.OAI.PolycyclicRecognition.nilshadowWeightOperator_symm _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Subexponential denominators for the actual translated recurrence boxes -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra MeasureTheory Filter Set
open scoped Manifold ENNReal Topology

variable {L W : Type} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {H : LieSubalgebra ℝ L} [H.IsCartanSubalgebra] (M : CartanWordModel H)
  {a : ℕ} (T : TriangularAdjoint L a)
  (hunimod : ∀ x : L, LinearMap.trace ℝ L (ad ℝ L x) = 0)
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)
  {EN N : Type} [NormedAddCommGroup EN] [NormedSpace ℝ EN]
  [FiniteDimensional ℝ EN] [TopologicalSpace N] [ChartedSpace EN N] [Group N]
  [LieGroup (𝓘(ℝ, EN)) ⊤ N] [T2Space N] [SimplyConnectedSpace N]
  [MeasurableSpace N] [BorelSpace N]
  (eN : cartanRootIdeal H ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, EN)) N)
  (Exp : GroupLieAlgebra (𝓘(ℝ, EN)) N → N) (hExp : IsGroupExponential Exp)
  (haar : NilpotentExponentialHaarInput EN N) (dynkin : NilpotentDynkinExpansionInput EN N)

set_option maxHeartbeats 1000000 in
include hExp haar dynkin in
theorem exists_sequence_recurrence_enlargement
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (E : Set W) (β : M.Bases)
    (hβ : IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
      (M.boxCost T hunimod eW E) β.val)
    (scale R : ℕ → ℝ) (hs : Tendsto scale atTop atTop)
    (hscale : ∀ n, 0 ≤ scale n) (hR0 : ∀ n, 0 ≤ R n)
    (hR : HasSubexponentialUpperBoundSeq scale R) :
    let μ := Measure.map ((Exp ∘ eN) ∘ b₀.equivFun.symm) volume
    let B := fun n => M.groupBox T hunimod eW (Exp ∘ eN) E β (scale n)
    ∃ V : ℕ → ℝ, (∀ n, 1 ≤ V n) ∧ HasSubexponentialUpperBoundSeq scale V ∧
      HasSubexponentialUpperBoundSeq scale (fun n => V n ^ finrank ℝ (cartanRootIdeal H)) ∧
      ∀ n (k : N),
        μ ((fun y => y * k) '' B n 1) ≠ ∞ ∧
        0 < (μ ((fun y => y * k) '' B n 1)).toReal ∧
        μ ((fun y => y * k) '' B n (V n)) ≠ ∞ ∧
        0 < (μ ((fun y => y * k) '' B n (V n))).toReal ∧
        (μ ((fun y => y * k) '' B n (V n))).toReal =
          V n ^ finrank ℝ (cartanRootIdeal H) * (μ ((fun y => y * k) '' B n 1)).toReal ∧
        ∀ v : N, k * v * k⁻¹ ∈ B n (R n) →
          ∀ x ∈ (fun y => y * k) '' B n 1, x * v ∈ (fun y => y * k) '' B n (V n) := by
  let : IsTopologicalGroup N := topologicalGroup_of_lieGroup (𝓘(ℝ, EN)) ⊤
  have hnil : LieRing.IsNilpotent (cartanRootIdeal H) :=
    (LieModule.isNilpotent_iff ℝ _ _).mpr ⟨M.bound, M.bound_zero⟩
  obtain ⟨⟨chart, hchart⟩, _⟩ := haar.2 Exp hExp (eN.nilpotent_iff_equiv_nilpotent.mp hnil)
  let μ := Measure.map ((Exp ∘ eN) ∘ b₀.equivFun.symm) volume
  let : μ.IsMulRightInvariant := exponential_basis_measure_isRightInvariant haar eN hnil Exp hExp b₀
  obtain ⟨C, hC, hprod⟩ := M.exists_groupBox_product_bound T hunimod eW eN Exp hExp dynkin b₀
  let V := fun n => 1 + C * 3 ^ M.bound * (2 + R n) ^ M.bound
  have hV1 (n : ℕ) : 1 ≤ V n := by
    have := hR0 n
    dsimp [V]
    exact le_add_of_nonneg_right (by positivity)
  have hV : HasSubexponentialUpperBoundSeq scale V := by
    have hp := ((sequence_subexponential_upper_const hs 2).add hR hs).pow hs
      (Eventually.of_forall (fun n => by linarith [hR0 n])) M.bound
    exact (sequence_subexponential_upper_const hs 1).add
      ((sequence_subexponential_upper_const hs (C * 3 ^ M.bound)).mul hp
        (Eventually.of_forall (fun _ => by positivity))) hs
  dsimp only
  refine ⟨V, hV1, hV, hV.pow hs (Eventually.of_forall (fun n => (hV1 n).trans' zero_le_one)) _, ?_⟩
  intro n k
  have hunit := exponential_box_unit_mass eN Exp chart hchart b₀ (M.boxBasis T hunimod eW E β (scale n))
  have hmass : μ ((fun y => y * k) '' M.groupBox T hunimod eW (Exp ∘ eN) E β (scale n) (V n)) =
      ENNReal.ofReal (V n ^ finrank ℝ (cartanRootIdeal H)) *
        μ ((fun y => y * k) '' M.groupBox T hunimod eW (Exp ∘ eN) E β (scale n) 1) := by
    rw [measure_image_mul_right μ, measure_image_mul_right μ]
    exact exponential_box_radius_measure eN Exp chart hchart b₀
      (M.boxBasis T hunimod eW E β (scale n)) ((hV1 n).trans' zero_le_one)
  have hunit' : μ ((fun y => y * k) '' M.groupBox T hunimod eW (Exp ∘ eN) E β (scale n) 1) ≠ ∞ ∧
      0 < (μ ((fun y => y * k) '' M.groupBox T hunimod eW (Exp ∘ eN) E β (scale n) 1)).toReal := by
    rw [measure_image_mul_right μ]
    exact hunit
  have hp : 0 < V n ^ finrank ℝ (cartanRootIdeal H) := pow_pos (zero_lt_one.trans_le (hV1 n)) _
  have hreal : (μ ((fun y => y * k) '' M.groupBox T hunimod eW (Exp ∘ eN) E β (scale n) (V n))).toReal =
      V n ^ finrank ℝ (cartanRootIdeal H) *
        (μ ((fun y => y * k) '' M.groupBox T hunimod eW (Exp ∘ eN) E β (scale n) 1)).toReal := by
    rw [hmass, ENNReal.toReal_mul, ENNReal.toReal_ofReal hp.le]
  refine ⟨hunit'.1, hunit'.2, ?_, ?_, hreal, ?_⟩
  · rw [hmass]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hunit'.1
  · rw [hreal]
    exact mul_pos hp hunit'.2
  intro v hv x hx
  obtain ⟨y, hy, rfl⟩ := hx
  have hy' : y ∈ M.groupBox T hunimod eW (Exp ∘ eN) E β (scale n) (1 + R n) := by
    obtain ⟨w, hw, hb⟩ := hy
    exact ⟨w, hw, hb.trans (by linarith [hR0 n])⟩
  have hv' : k * v * k⁻¹ ∈ M.groupBox T hunimod eW (Exp ∘ eN) E β (scale n) (1 + R n) := by
    obtain ⟨w, hw, hb⟩ := hv
    exact ⟨w, hw, hb.trans (by linarith)⟩
  have hb := hprod E β hβ (scale n) (hscale n) 2 (1 + R n) (by linarith [hR0 n])
    ![y, k * v * k⁻¹] (by intro i; fin_cases i; exact hy'; exact hv')
  have hb' : y * (k * v * k⁻¹) ∈ M.groupBox T hunimod eW (Exp ∘ eN) E β (scale n) (V n) := by
    simp only [List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil,
      Matrix.cons_val_zero, mul_one] at hb
    obtain ⟨w, hw, hwbound⟩ := hb
    change (Exp ∘ eN) w = y * (k * v * k⁻¹) at hw
    refine ⟨w, hw, hwbound.trans ?_⟩
    dsimp [V]
    norm_num
    ring_nf
    linarith
  refine ⟨y * (k * v * k⁻¹), hb', ?_⟩
  group

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanCoupledRecurrenceCells
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instDecidableEqConeMixedWords _root_.OAI.PolycyclicRecognition.CartanWordModel.instFintypeConeMixedWords _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.CartanFactorModel.heightRay_zero _root_.OAI.PolycyclicRecognition.CartanFactorModel.realScaleProfile_apply _root_.OAI.PolycyclicRecognition.CartanFactorModel.sampledProbeProfile_apply _root_.OAI.PolycyclicRecognition.bracketWordDifferential_mul _root_.OAI.PolycyclicRecognition.cartanWeightDerivation_apply_root _root_.OAI.PolycyclicRecognition.chartExponentialFlow_zero _root_.OAI.PolycyclicRecognition.derivationSemidirectHom_apply _root_.OAI.PolycyclicRecognition.exponentialHomOfDynkin_apply_exp _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.nilshadowWeightDerivation_symm _root_.OAI.PolycyclicRecognition.nilshadowWeightOperator_symm _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Recurrence cells for the actual conjugated source intervals -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra MeasureTheory Filter Set Metric
open scoped Manifold Topology ENNReal

variable {L W : Type} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {H : LieSubalgebra ℝ L} [H.IsCartanSubalgebra] (M : CartanWordModel H)
  {a : ℕ} (T : TriangularAdjoint L a)
  (hunimod : ∀ x : L, LinearMap.trace ℝ L (ad ℝ L x) = 0)
  [NormedAddCommGroup W] [NormedSpace ℝ W] (eW : HeightSpace T.character ≃ₗ[ℝ] W)
  {EN N : Type} [NormedAddCommGroup EN] [NormedSpace ℝ EN]
  [FiniteDimensional ℝ EN] [TopologicalSpace N] [ChartedSpace EN N] [Group N]
  [LieGroup (𝓘(ℝ, EN)) ⊤ N] [T2Space N] [SimplyConnectedSpace N]
  [MeasurableSpace N] [BorelSpace N]
  (eN : cartanRootIdeal H ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, EN)) N)
  (Exp : GroupLieAlgebra (𝓘(ℝ, EN)) N → N) (hExp : IsGroupExponential Exp)
  (haar : NilpotentExponentialHaarInput EN N) (dynkin : NilpotentDynkinExpansionInput EN N)

set_option maxHeartbeats 1000000 in
include hExp haar dynkin in
/-- The initial cell translation and the inside-sheet conjugation are both
controlled in the containing template. The denominator is an exact radius
power, and is subexponential. No independence after restriction is used. -/
theorem exists_coupled_interval_recurrence_cells
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (E : Set W) (β : M.Bases)
    (hβ : IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
      (M.boxCost T hunimod eW E) β.val)
    (s : Fin M.letterCount → ℝ)
    (hs : ∀ i, s i ≤ (M.supportIn T hunimod eW).weightSupport E i)
    {m : ℕ} (letters : Fin m → Fin M.letterCount)
    (scale R : ℕ → ℝ) (hscale : Tendsto scale atTop atTop)
    (hscale0 : ∀ n, 0 ≤ scale n) (hR0 : ∀ n, 0 ≤ R n)
    (hR : HasSubexponentialUpperBoundSeq scale R)
    (ρ : ℝ) (hρ : 0 ≤ ρ) (k₀ : ℕ → N) (k : ℕ → ℕ → N)
    (hk₀ : ∀ n, k₀ n ∈ M.groupBox T hunimod eW (Exp ∘ eN) E β (scale n) (R n))
    (hk : ∀ n j, k n j ∈ M.groupBox T hunimod eW (Exp ∘ eN) E β (scale n) (R n)) :
    let μ := Measure.map ((Exp ∘ eN) ∘ b₀.equivFun.symm) volume
    let Q := fun n => (fun y => y * k₀ n) ''
      M.groupBox T hunimod eW (Exp ∘ eN) E β (scale n) 1
    ∃ V D : ℕ → ℝ, (∀ n, 1 ≤ V n) ∧
      HasSubexponentialUpperBoundSeq scale D ∧ (∀ n, 0 < D n) ∧
      let Q' := fun n => (fun y => y * k₀ n) ''
        M.groupBox T hunimod eW (Exp ∘ eN) E β (scale n) (V n)
      (∀ n, μ (Q n) ≠ ∞ ∧ 0 < (μ (Q n)).toReal ∧
        μ (Q' n) ≠ ∞ ∧ 0 < (μ (Q' n)).toReal ∧
        (μ (Q' n)).toReal = D n * (μ (Q n)).toReal) ∧
      ∀ n j, ∀ x ∈ Q n,
        ∀ u ∈ rootIntervalSupport (Exp ∘ eN) letters M.letter s (scale n) ρ j,
          x * (k n j * u * (k n j)⁻¹) ∈ Q' n := by
  obtain ⟨C, hC, hinterval⟩ := M.exists_source_interval_box_bound T hunimod eW b₀
  let R' := fun n => R n + C * ρ
  have hR'0 : ∀ n, 0 ≤ R' n := fun n => add_nonneg (hR0 n) (mul_nonneg hC hρ)
  have hR' : HasSubexponentialUpperBoundSeq scale R' :=
    hR.add (sequence_subexponential_upper_const hscale (C * ρ)) hscale
  have hmono (n : ℕ) {r₁ r₂ : ℝ} (hr : r₁ ≤ r₂) :
      M.groupBox T hunimod eW (Exp ∘ eN) E β (scale n) r₁ ⊆
        M.groupBox T hunimod eW (Exp ∘ eN) E β (scale n) r₂ := by
    rintro z ⟨v, hv, hb⟩
    exact ⟨v, hv, hb.trans hr⟩
  have hpad (n j : ℕ) {u : N}
      (hu : u ∈ rootIntervalSupport (Exp ∘ eN) letters M.letter s (scale n) ρ j) :
      u ∈ M.groupBox T hunimod eW (Exp ∘ eN) E β (scale n) (R' n) := by
    obtain ⟨t, ht, rfl⟩ := hu
    by_cases hj : j < m
    · rw [rootIntervalSample_letter (Exp ∘ eN) letters M.letter s (scale n) ⟨j, hj⟩]
      exact hmono n (le_add_of_nonneg_left (hR0 n))
        (hinterval E β hβ s hs (Exp ∘ eN) (scale n) ρ (hscale0 n) hρ
          (letters ⟨j, hj⟩) t (by simpa [Real.dist_eq] using ht))
    · have he : rootIntervalSample (Exp ∘ eN) letters M.letter s (scale n) j t = 1 := by
        simp [rootIntervalSample, rootIntervalDirection, hj, hExp.map_zero]
      rw [he]
      exact ⟨0, by simp [hExp.map_zero], by simpa using hR'0 n⟩
  obtain ⟨A, hA0, hA, hconj⟩ := M.exists_sequence_double_conjugate_box T hunimod eW eN Exp
    hExp dynkin b₀ E β hβ scale R' hscale hscale0 hR'0 hR'
  obtain ⟨V, hV, _, hD, hcells⟩ := M.exists_sequence_recurrence_enlargement T hunimod eW
    eN Exp hExp haar dynkin b₀ E β hβ scale A hscale hscale0 hA0 hA
  dsimp only
  refine ⟨V, fun n => V n ^ finrank ℝ (cartanRootIdeal H), hV, hD,
    fun n => pow_pos (zero_lt_one.trans_le (hV n)) _, ?_, ?_⟩
  · intro n
    exact ⟨(hcells n (k₀ n)).1, (hcells n (k₀ n)).2.1,
      (hcells n (k₀ n)).2.2.1, (hcells n (k₀ n)).2.2.2.1,
      (hcells n (k₀ n)).2.2.2.2.1⟩
  · intro n j x hx u hu
    apply (hcells n (k₀ n)).2.2.2.2.2 _ _ x hx
    exact hconj n (k₀ n) (k n j) u
      (hmono n (le_add_of_nonneg_right (mul_nonneg hC hρ)) (hk₀ n))
      (hmono n (le_add_of_nonneg_right (mul_nonneg hC hρ)) (hk n j)) (hpad n j hu)

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanCoupledSourceImage
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instDecidableEqConeMixedWords _root_.OAI.PolycyclicRecognition.CartanWordModel.instFintypeConeMixedWords _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_countable _root_.OAI.PolycyclicRecognition.finitelyGeneratedSubgroupIndex_countable _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Joint source-bundle images for the actual coupled recurrence

The interval laws and all recurrence denominators are constructed here.
Only the good-profile mass and the full normalized source-map submersion
remain to be supplied by the profile selection.
-/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra MeasureTheory Filter Set Metric
open scoped Manifold Topology ENNReal

variable {L W : Type} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {H : LieSubalgebra ℝ L} [H.IsCartanSubalgebra] (M : CartanWordModel H)
  {a : ℕ} (T : TriangularAdjoint L a)
  (hunimod : ∀ x : L, LinearMap.trace ℝ L (ad ℝ L x) = 0)
  [NormedAddCommGroup W] [NormedSpace ℝ W] (eW : HeightSpace T.character ≃ₗ[ℝ] W)
  {EN N : Type} [NormedAddCommGroup EN] [NormedSpace ℝ EN]
  [FiniteDimensional ℝ EN] [TopologicalSpace N] [ChartedSpace EN N] [Group N]
  [LieGroup (𝓘(ℝ, EN)) ⊤ N] [T2Space N] [SimplyConnectedSpace N]
  [MeasurableSpace N] [BorelSpace N]
  (eN : cartanRootIdeal H ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, EN)) N)
  (Exp : GroupLieAlgebra (𝓘(ℝ, EN)) N → N) (hExp : IsGroupExponential Exp)
  (haar : NilpotentExponentialHaarInput EN N) (dynkin : NilpotentDynkinExpansionInput EN N)

set_option maxHeartbeats 1000000 in
include hExp haar dynkin in
theorem coupled_source_bundle_haar_image_sequence
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (E source : Set W) (β γ : M.Bases)
    (hβ : IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
      (M.boxCost T hunimod eW E) β.val)
    (s : Fin M.letterCount → ℝ)
    (hs : ∀ i, s i ≤ (M.supportIn T hunimod eW).weightSupport E i)
    {m h c : ℕ} (letters : Fin m → Fin M.letterCount)
    (aN : DynkinCoefficients c 2)
    (hm : ∀ x y, Exp (finiteDynkinPolynomial aN ![x, y]) = Exp x * Exp y)
    (scale R : ℕ → ℝ) (hscale : Tendsto scale atTop atTop)
    (hscale0 : ∀ n, 0 ≤ scale n) (hR0 : ∀ n, 0 ≤ R n)
    (hR : HasSubexponentialUpperBoundSeq scale R)
    (ρ : ℝ) (hρ : 1 ≤ ρ) (k₀ : ℕ → N) (k : ℕ → ℕ → N)
    (hk₀ : ∀ n, k₀ n ∈ M.groupBox T hunimod eW (Exp ∘ eN) E β (scale n) (R n))
    (hk : ∀ n j, k n j ∈ M.groupBox T hunimod eW (Exp ∘ eN) E β (scale n) (R n))
    (rem : RemezPolynomialInput) (hN : 1 ≤ h * finrank ℝ (cartanRootIdeal H))
    (p₀ : WordLawData (Fin M.letterCount) (finrank ℝ (cartanRootIdeal H)))
    (hlim : Tendsto (fun r =>
      let b := M.boxBasis T hunimod eW source γ (scale r)
      (basisBracket b, fun i => b.equivFun (Real.exp (scale r * s i) • M.letter i))) atTop (𝓝 p₀))
    (t₀ : Fin (m + m) → ℝ)
    (hsub : Function.Surjective (fderiv ℝ (differenceAmplitudeWordEndpoint aN letters p₀) t₀))
    (Good : ℕ → Set N) (hGood : ∀ n, MeasurableSet (Good n)) :
    let μ := Measure.map ((Exp ∘ eN) ∘ b₀.equivFun.symm) volume
    let Q := fun n => (fun y => y * k₀ n) '' M.groupBox T hunimod eW (Exp ∘ eN) E β (scale n) 1
    let allLetters := fun j : Fin (h * m) => letters (finProdFinEquiv.symm j).2
    let sample := fun n => coupledRootIntervalSample (Exp ∘ eN) allLetters M.letter s (scale n) (k n)
    (∀ n, Good n ⊆ Q n) → (∀ n, 0 < (μ (Good n)).toReal) →
    HasSubexponentialLowerBoundSeq scale (fun n => (μ (Good n)).toReal / (μ (Q n)).toReal) →
    ∃ (x : ℕ → N) (C : ℕ → Set (Fin h → N)),
      (∀ n, x n ∈ Good n) ∧ (∀ n, IsCompact (C n)) ∧
      HasSubexponentialLowerBoundSeq scale (fun n =>
        ((Measure.pi fun _ : Fin h => μ) (C n)).toReal /
          Real.exp (scale n * ((h : ℝ) * columnBasisWeight (M.boxCost T hunimod eW source) γ.val))) ∧
      ∀ᶠ n in atTop, ∀ y ∈ C n, ∃ t : Fin (h * m + h * m) → ℝ,
        t ∈ closedBall 0 ρ ∧
        SwitchSuccessful (fun _ => Good n) 0 (h * m) (x n)
          (sampledSwitchParameters (sample n) (h * m) t) ∧
        sourceBundleProduct eN Exp M.letter s letters (bundleParameterChart h m) (scale n) t = y := by
  dsimp only
  intro hGoodQ hGoodpos hGoodlower
  let : IsTopologicalGroup N := topologicalGroup_of_lieGroup (𝓘(ℝ, EN)) ⊤
  have hnil : LieRing.IsNilpotent (cartanRootIdeal H) :=
    (LieModule.isNilpotent_iff ℝ _ _).mpr ⟨M.bound, M.bound_zero⟩
  obtain ⟨⟨chart, hchart⟩, _⟩ := haar.2 Exp hExp (eN.nilpotent_iff_equiv_nilpotent.mp hnil)
  let coords := exponentialBasisHomeomorph eN chart b₀
  let : LocallyCompactSpace N := coords.symm.isOpenEmbedding.locallyCompactSpace
  let : SecondCountableTopology N := coords.symm.secondCountableTopology
  let μ := Measure.map ((Exp ∘ eN) ∘ b₀.equivFun.symm) volume
  let : μ.IsHaarMeasure := exponential_basis_measure_isHaar haar eN hnil Exp hExp b₀
  let : μ.IsMulRightInvariant := exponential_basis_measure_isRightInvariant haar eN hnil Exp hExp b₀
  have hc (v : cartanRootIdeal H) : Continuous (fun t : ℝ => (Exp ∘ eN) (t • v)) := by
    have he (t : ℝ) : (Exp ∘ eN) (t • v) = chart (t • eN v) := by
      simp only [Function.comp_apply, map_smul, hchart]
    simp_rw [he]
    exact chart.continuous.comp (continuous_id.smul continuous_const)
  let allLetters := fun j : Fin (h * m) => letters (finProdFinEquiv.symm j).2
  let sample := fun n => coupledRootIntervalSample (Exp ∘ eN) allLetters M.letter s (scale n) (k n)
  let σ := fun n => coupledRootIntervalLaw (Exp ∘ eN) allLetters M.letter s (scale n) ρ (k n)
  let K := fun n j => (fun u => k n j * u * (k n j)⁻¹) ''
    rootIntervalSupport (Exp ∘ eN) allLetters M.letter s (scale n) ρ j
  let Q := fun n => (fun y => y * k₀ n) '' M.groupBox T hunimod eW (Exp ∘ eN) E β (scale n) 1
  let : ∀ n j, IsProbabilityMeasure (σ n j) := fun n j =>
    coupledRootIntervalLaw_isProbability (Exp ∘ eN) hc allLetters M.letter s (scale n)
      (zero_lt_one.trans_le hρ) (k n) j
  obtain ⟨V, D, _, hDupper, hDpos, hcells, hcontain⟩ := M.exists_coupled_interval_recurrence_cells
    T hunimod eW eN Exp hExp haar dynkin b₀ E β hβ s hs allLetters scale R hscale hscale0
    hR0 hR ρ (zero_le_one.trans hρ) k₀ k hk₀ hk
  let Q' := fun n => (fun y => y * k₀ n) '' M.groupBox T hunimod eW (Exp ∘ eN) E β (scale n) (V n)
  exact recurrent_source_bundle_haar_image_sequence eN Exp chart hchart hExp.map_zero aN hm
    M.letter M.wordList b₀ γ (M.boxCost T hunimod eW source) s letters scale hscale rem hN p₀ hlim
    t₀ hsub ρ hρ μ sample σ
    (fun n j => measurePreserving_coupledRootIntervalSample (Exp ∘ eN) hc allLetters M.letter s (scale n) ρ (k n) j)
    Q Good K (fun n _ => Q' n) (fun n _ => D n)
    (fun n => (hcells n).1) (fun n => (hcells n).2.1)
    (fun n j => coupledRootIntervalLaw_ae_mem_support (Exp ∘ eN) hc allLetters M.letter s (scale n) ρ (k n) j)
    (fun n _ => (hcells n).2.2.1) (fun n _ => (hcells n).2.2.2.1)
    (fun n j x hx u hu => by
      obtain ⟨v, hv, rfl⟩ := hu
      exact hcontain n j x hx v hv)
    (fun n _ => hDpos n) (fun n _ => (hcells n).2.2.2.2.le)
    hGood hGoodQ hGoodpos hGoodlower (fun _ _ => hDupper)

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanJacobian
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instDecidableEqConeMixedWords _root_.OAI.PolycyclicRecognition.CartanWordModel.instFintypeConeMixedWords _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_nonempty _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.CartanFactorModel.heightRay_zero _root_.OAI.PolycyclicRecognition.CartanFactorModel.realScaleProfile_apply _root_.OAI.PolycyclicRecognition.CartanFactorModel.sampledProbeProfile_apply _root_.OAI.PolycyclicRecognition.bracketWordDifferential_mul _root_.OAI.PolycyclicRecognition.cartanWeightDerivation_apply_root _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.nilshadowWeightDerivation_symm _root_.OAI.PolycyclicRecognition.nilshadowWeightOperator_symm _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The Jacobian of actual Cartan conjugation

The nilpotent residual exponential has determinant one. The scalar weight
factors multiply to one by the already proved trace balance. Consequently
conjugation on the nilpotent Cartan ideal preserves coordinate volume.
-/

noncomputable section

namespace PolycyclicRecognition

open Module LieAlgebra LieModule
open scoped BigOperators

variable {L : Type} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {H : LieSubalgebra ℝ L} [H.IsCartanSubalgebra]
  {n : ℕ} (T : TriangularAdjoint L n)

set_option maxHeartbeats 1000000 in
/-- The nonsemisimple part of the actual Cartan action has Jacobian one. -/
theorem det_cartanIdealResidualAutomorphism (h : H) :
    LinearMap.det (cartanIdealResidualAutomorphism T H h).toLinearEquiv.toLinearMap = 1 := by
  let : Module ℚ (cartanRootIdeal H) := Module.compHom _ (algebraMap ℚ ℝ)
  exact det_nilpotent_exp (cartanIdealResidualDerivation T H h).toLinearMap
    ⟨finrank ℝ L, cartanIdealResidualDerivation_pow_eq_zero T H h⟩

namespace CartanWordModel

variable (M : CartanWordModel H)

set_option maxHeartbeats 1000000 in
/-- The diagonal scalar action has Jacobian given by the total word weight. -/
theorem det_idealWeightDilation (β : M.Bases) (h : H) :
    LinearMap.det (cartanIdealWeightDilation T H h).toLinearEquiv.toLinearMap =
      Real.exp (∑ j, bracketWordExponent (fun i => M.weight i h) (β.val j)) := by
  let b := WordBasisSelections.basis M.letter M.wordList β
  let F := (cartanIdealWeightDilation T H h).toLinearEquiv.toLinearMap
  let v := fun j => Real.exp (bracketWordExponent (fun i => M.weight i h) (β.val j))
  have hb (j) : F (b j) = v j • b j := by
    have hh := M.idealWeightDilation_word T h (β.val j)
    have he := WordBasisSelections.eval_words M.letter M.wordList β j
    change evalBracketWord M.letter (β.val j) = b j at he
    rw [he] at hh
    exact hh
  have hm : LinearMap.toMatrix b b F = Matrix.diagonal v := by
    ext i j
    simp only [LinearMap.toMatrix_apply, hb, map_smul, Finsupp.smul_apply,
      Basis.repr_self, Finsupp.single_apply, smul_eq_mul, Matrix.diagonal_apply]
    split_ifs <;> simp_all
  rw [← LinearMap.det_toMatrix b, hm, Matrix.det_diagonal, Real.exp_sum]

set_option maxHeartbeats 1000000 in
include M in
/-- Unimodularity makes all word-basis scalar Jacobians equal to one. -/
theorem det_idealWeightDilation_eq_one
    (hunimod : ∀ x : L, LinearMap.trace ℝ L (ad ℝ L x) = 0) (h : H) :
    LinearMap.det (cartanIdealWeightDilation T H h).toLinearEquiv.toLinearMap = 1 := by
  let β : M.Bases := Classical.choice inferInstance
  rw [M.det_idealWeightDilation T β h]
  have ht := trace_cartan_word_basis H M.letter M.weight M.letter_root
    (WordBasisSelections.basis M.letter M.wordList β)
    (WordBasisSelections.words M.letter M.wordList β)
    (WordBasisSelections.eval_words M.letter M.wordList β) h
  have hz := trace_cartanRootIdeal_eq_zero T H hunimod h
  have hs : (∑ j, bracketWordExponent (fun i => M.weight i h) (β.val j)) = 0 := by
    rw [ht] at hz
    simp only [bracketWordExponent]
    rw [Finset.sum_comm]
    simpa only [Nat.cast_sum, Finset.sum_mul, WordBasisSelections.words] using hz
  rw [hs, Real.exp_zero]

set_option maxHeartbeats 1000000 in
include M in
/-- The full actual Cartan action, rather than only its scalar part, has
Jacobian one on the nilpotent ideal. -/
theorem det_idealAdjointAutomorphism_eq_one
    (hunimod : ∀ x : L, LinearMap.trace ℝ L (ad ℝ L x) = 0) (h : H) :
    LinearMap.det (cartanIdealAdjointAutomorphism T H h).toLinearEquiv.toLinearMap = 1 := by
  change LinearMap.det ((cartanIdealWeightDilation T H h).toLinearEquiv.toLinearMap.comp
    (cartanIdealResidualAutomorphism T H h).toLinearEquiv.toLinearMap) = 1
  rw [LinearMap.det_comp, M.det_idealWeightDilation_eq_one T hunimod,
    det_cartanIdealResidualAutomorphism, mul_one]

end CartanWordModel
end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanHaarConjugation
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instDecidableEqConeMixedWords _root_.OAI.PolycyclicRecognition.CartanWordModel.instFintypeConeMixedWords _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A common Haar measure for Cartan boxes and conjugation

The determinant computation gives exact invariance under the actual Cartan
adjoint automorphisms. The same measure retains the explicit weighted-box
volume, so the lower packing argument and box rates use compatible measures.
-/

noncomputable section

namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule MeasureTheory
open scoped Manifold

variable {L : Type} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {H : LieSubalgebra ℝ L} [H.IsCartanSubalgebra] (M : CartanWordModel H)
  {a : ℕ} (T : TriangularAdjoint L a)
  (hunimod : ∀ x : L, LinearMap.trace ℝ L (ad ℝ L x) = 0)
  {EN N : Type} [NormedAddCommGroup EN] [NormedSpace ℝ EN]
  [FiniteDimensional ℝ EN] [TopologicalSpace N] [ChartedSpace EN N] [Group N]
  [LieGroup (𝓘(ℝ, EN)) ⊤ N] [T2Space N]
  [hNsc : SimplyConnectedSpace N] [MeasurableSpace N] [BorelSpace N]
  (eN : cartanRootIdeal H ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, EN)) N)
  (Exp : GroupLieAlgebra (𝓘(ℝ, EN)) N → N) (hExp : IsGroupExponential Exp)
  (hbij : Function.Bijective Exp) (dynkin : NilpotentDynkinExpansionInput EN N)
  (haar : NilpotentExponentialHaarInput EN N)

include hunimod haar hNsc

set_option maxHeartbeats 1000000 in
/-- One Haar measure has both the exact word-box formula and invariance
under every Cartan adjoint action. -/
theorem exists_haar_adjoint_invariant_weighted_boxes
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H)) :
    ∃ μ : Measure N, μ.IsHaarMeasure ∧
      (∀ h : H, MeasurePreserving (M.adjointGroupAutomorphism T eN Exp hExp hbij dynkin h) μ μ) ∧
      ∀ (cost : M.wordList → ℝ) (β : M.Bases) (r R : ℝ), 0 ≤ R →
        μ (exponentialCoordinateBox (Exp ∘ eN)
          (exponentialRescaleBasis (WordBasisSelections.basis M.letter M.wordList β)
            (fun i => cost (β.val i)) r) R) =
          ENNReal.ofReal |(columnBasisMatrix (wordListCoordinates M.letter M.wordList b₀) β.val).det| *
            ENNReal.ofReal (Real.exp (r * columnBasisWeight cost β.val)) *
              ENNReal.ofReal (2 * R) ^ finrank ℝ (cartanRootIdeal H) := by
  let _ : SimplyConnectedSpace N := hNsc
  have hn : LieRing.IsNilpotent (cartanRootIdeal H) :=
    (LieModule.isNilpotent_iff ℝ _ _).mpr ⟨M.bound, M.bound_zero⟩
  obtain ⟨⟨chart, hc⟩, hhaar⟩ := haar.2 Exp hExp (eN.nilpotent_iff_equiv_nilpotent.mp hn)
  let b := b₀.map eN.toLinearEquiv
  let f := (Exp ∘ eN) ∘ b₀.equivFun.symm
  have hf : f = Exp ∘ b.equivFun.symm := by
    funext t
    change Exp (eN (b₀.equivFun.symm t)) = Exp ((b₀.map eN.toLinearEquiv).equivFun.symm t)
    rw [Basis.map_equivFun]
    rfl
  refine ⟨Measure.map f volume, ?_, ?_, ?_⟩
  · rw [hf]
    exact hhaar _ b
  · intro h
    exact exponentialConjugate_measurePreserving eN Exp hbij chart hc b₀
      (cartanIdealAdjointAutomorphism T H h) (M.det_idealAdjointAutomorphism_eq_one T hunimod h)
  · intro cost β r R hR
    exact exponentialCoordinate_weighted_box_measure eN Exp chart hc b₀ M.letter M.wordList
      cost β r R hR

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanWordLogarithms
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Cartan logarithms of bounded words

The Cartan group is nilpotent. The finite Dynkin identity therefore gives a
polynomial bound on the logarithm of every prefix of a bounded word. We also
record the exact semidirect-product word formula used to apply the controlled
Cartan estimates to such prefixes.
-/

noncomputable section

namespace PolycyclicRecognition

open Module LieModule
open scoped Manifold

variable {L : Type} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  (H : LieSubalgebra ℝ L) [H.IsCartanSubalgebra]
  {ED D : Type} [NormedAddCommGroup ED] [NormedSpace ℝ ED]
  [FiniteDimensional ℝ ED] [TopologicalSpace D] [ChartedSpace ED D] [Group D]
  [LieGroup (𝓘(ℝ, ED)) ⊤ D] [T2Space D]
  (eD : H ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, ED)) D)
  (ExpD : GroupLieAlgebra (𝓘(ℝ, ED)) D → D) (hbijD : Function.Bijective ExpD)

set_option maxHeartbeats 1000000 in
omit [FiniteDimensional ℝ L] [H.IsCartanSubalgebra] [T2Space D] in
theorem exp_cartanLog (d : D) : ExpD (eD (cartanLog H eD ExpD hbijD d)) = d := by
  unfold cartanLog
  rw [eD.apply_symm_apply]
  exact (Equiv.ofBijective ExpD hbijD).apply_symm_apply d

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanSemidirectWords
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instDecidableEqConeMixedWords _root_.OAI.PolycyclicRecognition.CartanWordModel.instFintypeConeMixedWords _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Controlled words in the actual semidirect product

Nilpotent Cartan increments give polynomial bounds on every Cartan prefix.
The exact semidirect-product formula then reduces its nilpotent coordinate
to the controlled product estimate. No polynomial bound on prefixes is left
as an assumption of this theorem.
-/

noncomputable section

namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule
open scoped Manifold

variable {L : Type} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {H : LieSubalgebra ℝ L} [H.IsCartanSubalgebra] (M : CartanWordModel H)
  {n : ℕ} (T : TriangularAdjoint L n)
  (hunimod : ∀ x : L, LinearMap.trace ℝ L (ad ℝ L x) = 0)
  {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)
  {EN N : Type} [NormedAddCommGroup EN] [NormedSpace ℝ EN]
  [FiniteDimensional ℝ EN] [TopologicalSpace N] [ChartedSpace EN N] [Group N]
  [LieGroup (𝓘(ℝ, EN)) ⊤ N] [T2Space N]
  (eN : cartanRootIdeal H ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, EN)) N)
  (ExpN : GroupLieAlgebra (𝓘(ℝ, EN)) N → N) (hExpN : IsGroupExponential ExpN)
  (hbijN : Function.Bijective ExpN) (dynkinN : NilpotentDynkinExpansionInput EN N)
  {ED D : Type} [NormedAddCommGroup ED] [NormedSpace ℝ ED]
  [FiniteDimensional ℝ ED] [TopologicalSpace D] [ChartedSpace ED D] [Group D]
  [LieGroup (𝓘(ℝ, ED)) ⊤ D] [T2Space D]
  (eD : H ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, ED)) D)
  (ExpD : GroupLieAlgebra (𝓘(ℝ, ED)) D → D) (hExpD : IsGroupExponential ExpD)
  (hbijD : Function.Bijective ExpD) (dynkinD : NilpotentDynkinExpansionInput ED D)
  (φ : D →* MulAut N)

section Representation

variable {A G : Type} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A] [Group G]

attribute [local instance 100] LieRing.ofAssociativeRing

set_option maxHeartbeats 1000000 in
omit [T2Space D] in
/-- The required semidirect action identity follows from compatible
exponentials in an ambient faithful representation. -/
theorem action_eq_adjoint_of_representation
    (j : L →ₗ⁅ℝ⁆ A) (ρ : G →* Aˣ) (hρ : Function.Injective ρ)
    (ιN : N →* G) (hιN : Function.Injective ιN) (ιD : D →* G)
    (hconj : ∀ d g, ιN (φ d g) = ιD d * ιN g * (ιD d)⁻¹)
    (hN : ∀ x : cartanRootIdeal H, ρ (ιN (ExpN (eN x))) = algebraExpUnit (j x))
    (hD : ∀ h : H, ρ (ιD (ExpD (eD h))) = algebraExpUnit (j h)) (d : D) :
    φ d = M.adjointGroupAutomorphism T eN ExpN hExpN hbijN dynkinN
      (cartanLog H eD ExpD hbijD d) := by
  apply MulEquiv.ext
  intro g
  apply hιN
  rw [hconj]
  have hh := M.adjointGroupAutomorphism_eq_conjugation T eN ExpN hExpN hbijN dynkinN
    j ρ hρ ιN (fun h => ιD (ExpD (eD h))) hN hD (cartanLog H eD ExpD hbijD d) g
  simpa only [exp_cartanLog] using hh.symm

end Representation

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_ExponentialRepresentationInput
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instDecidableEqConeMixedWords _root_.OAI.PolycyclicRecognition.CartanWordModel.instFintypeConeMixedWords _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exponential compatibility in the published faithful realization

Onshuus–Post (2022), Proposition 2.4 and proof, give a faithful inducing
linear Lie realization of a simply connected real triangular group.
Lee, *Introduction to Smooth Manifolds*, second edition (2013), Theorem 8.44
(p.195) and Proposition 20.8(g) (p.520), give its Lie algebra map and
exponential compatibility. Only these properties are retained below.

https://doi.org/10.1112/blms.12574
https://doi.org/10.1007/978-1-4419-9982-5

The action and all bounds remain proved consequences, not part of the input.
-/

noncomputable section

namespace PolycyclicRecognition

open scoped Manifold Matrix.Norms.Operator

attribute [local instance 100] LieRing.ofAssociativeRing

variable {EG G : Type} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G]

variable [SimplyConnectedSpace G]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {ExpG : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H ExpG)

/-- The published representation identifies the actual factor action with
the explicit full Cartan adjoint automorphism. -/
theorem cartan_action_eq_adjoint_of_published_realization
    (hExpG : IsGroupExponential ExpG)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (hbijN : Function.Bijective F.ExpN) (hbijD : Function.Bijective F.ExpD)
    (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
    (d : F.D.carrier) :
    F.action d = M.adjointGroupAutomorphism T F.N.equiv F.ExpN F.isExpN hbijN dynkinN
      (cartanLog H F.D.equiv F.ExpD hbijD d) := by
  obtain ⟨m, hm, ρ, j, hind, hExp⟩ := realize ⟨a, ⟨T⟩⟩ ExpG hExpG
  let _ : NeZero m := ⟨Nat.ne_of_gt hm⟩
  have hρ : Function.Injective ρ := by
    intro g h he
    exact hind.injective (congrArg (fun u : (Matrix (Fin m) (Fin m) ℝ)ˣ =>
      (u : Matrix (Fin m) (Fin m) ℝ)) he)
  exact M.action_eq_adjoint_of_representation T F.N.equiv F.ExpN F.isExpN hbijN dynkinN
    F.D.equiv F.ExpD hbijD F.action j ρ hρ F.inclusionN F.closedN.injective F.inclusionD
    F.conjugation (fun x => by rw [F.compatibleN, hExp])
    (fun x => by rw [F.compatibleD, hExp]) d

open Module LieAlgebra LieModule

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanFactorHaarInvariance
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instDecidableEqConeMixedWords _root_.OAI.PolycyclicRecognition.CartanWordModel.instFintypeConeMixedWords _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_countable _root_.OAI.PolycyclicRecognition.finitelyGeneratedSubgroupIndex_countable _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual Cartan factor action preserves the chosen Haar measure -/

noncomputable section
namespace PolycyclicRecognition.CartanFactorModel

open Module LieAlgebra MeasureTheory Set
open scoped Manifold NNReal

variable {EG G : Type} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H Exp)

include T M

set_option maxHeartbeats 1000000 in
/-- Trace zero and the published realization imply that the original
factor action preserves every Haar normalization, including the measure
constructed in ideal/quotient section coordinates. -/
theorem action_preserves_haar
    (hExp : IsGroupExponential Exp)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
    (haarD : NilpotentExponentialHaarInput F.D.modelSpace F.D.carrier)
    (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
    (hunimod : ∀ x : GroupLieAlgebra (𝓘(ℝ, EG)) G, LinearMap.trace ℝ _ (ad ℝ _ x) = 0)
    (μ : Measure F.N.carrier) [μ.IsHaarMeasure] (d : F.D.carrier) :
    MeasurePreserving (F.action d) μ μ := by
  classical
  let _ : IsTopologicalGroup F.N.carrier := topologicalGroup_of_lieGroup (𝓘(ℝ, F.N.modelSpace)) ⊤
  obtain ⟨⟨chartN, hchartN⟩, _⟩ := haarN.2 F.ExpN F.isExpN
    (F.N.tangent_nilpotent (cartanRootIdeal_nilpotent H T))
  obtain ⟨⟨chartD, hchartD⟩, _⟩ := haarD.2 F.ExpD F.isExpD
    (F.D.tangent_nilpotent inferInstance)
  let b := (finBasis ℝ (cartanRootIdeal H)).map F.N.equiv.toLinearEquiv
  let coordinates := b.equivFun.symm.toContinuousLinearEquiv.toHomeomorph.trans chartN
  let _ : LocallyCompactSpace F.N.carrier := coordinates.symm.isOpenEmbedding.locallyCompactSpace
  let _ : SecondCountableTopology F.N.carrier := coordinates.symm.secondCountableTopology
  have hbijN : Function.Bijective F.ExpN := funext hchartN ▸ chartN.bijective
  have hbijD : Function.Bijective F.ExpD := funext hchartD ▸ chartD.bijective
  obtain ⟨ν, hν, hinv, _⟩ := M.exists_haar_adjoint_invariant_weighted_boxes T hunimod
    F.N.equiv F.ExpN F.isExpN hbijN dynkinN haarN (finBasis ℝ (cartanRootIdeal H))
  let _ : ν.IsHaarMeasure := hν
  apply measurePreserving_of_haarMeasure ν μ (F.action d)
  rw [cartan_action_eq_adjoint_of_published_realization T M F hExp realize hbijN hbijD dynkinN d]
  exact hinv _

end PolycyclicRecognition.CartanFactorModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanSourceTuplePacking
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instDecidableEqConeMixedWords _root_.OAI.PolycyclicRecognition.CartanWordModel.instFintypeConeMixedWords _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.inversePairCoupling_finiteOnCompacts _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.normalizedPairAction _root_.OAI.PolycyclicRecognition.normalizedPairContinuousAction _root_.OAI.PolycyclicRecognition.normalizedPair_polishSpace _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual target tuple counts from source Cartan-fiber volume -/

noncomputable section
namespace PolycyclicRecognition.CartanFactorModel

open Module LieAlgebra MeasureTheory Set Filter
open scoped Manifold NNReal Topology

variable {EG G : Type} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G]
  [IsIsometricSMul G G] [ProperSpace G]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H Exp)

set_option maxHeartbeats 1000000 in
include T M in
theorem exists_target_source_tuple_count {h : ℕ}
    (hExp : IsGroupExponential Exp)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
    (haarD : NilpotentExponentialHaarInput F.D.modelSpace F.D.carrier)
    (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
    (hunimod : ∀ z : GroupLieAlgebra (𝓘(ℝ, EG)) G, LinearMap.trace ℝ _ (ad ℝ _ z) = 0)
    (μ : Measure F.N.carrier) [μ.IsHaarMeasure]
    {Λ : ℝ≥0} (hΛ : 0 < (Λ : ℝ)) (p : ℕ → NormalizedPair G Λ)
    {scale : ℕ → ℝ} (hs : Tendsto scale atTop atTop)
    (x : ℕ → G) (d : ℕ → F.D.carrier)
    (S : ℕ → Set (Fin h → F.N.carrier)) (hS : ∀ n, IsCompact (S n))
    {b : ℝ} (hvol : HasSubexponentialLowerBoundSeq scale
      (fun n => ((Measure.pi fun _ : Fin h => μ) (S n)).toReal / Real.exp (scale n * b))) :
    ∃ t : ℕ → Finset (Fin h → G),
      (∀ n, (↑(t n) : Set (Fin h → G)) ⊆
        (fun u => fun i => (p n).val.1 (x n * F.inclusionN (u i) * F.inclusionD (d n))) '' S n) ∧
      (∀ n, ∀ u ∈ t n, ∀ v ∈ t n, u ≠ v → 1 ≤ dist u v) ∧
      HasSubexponentialLowerBoundSeq scale
        (fun n => ((t n).card : ℝ) / Real.exp (scale n * b)) := by
  classical
  let : IsTopologicalGroup G := topologicalGroup_of_lieGroup (𝓘(ℝ, EG)) ⊤
  let : IsTopologicalGroup F.N.carrier := topologicalGroup_of_lieGroup (𝓘(ℝ, F.N.modelSpace)) ⊤
  let : SecondCountableTopology F.N.carrier := F.closedN.isEmbedding.secondCountableTopology
  let : LocallyCompactSpace F.N.carrier := F.closedN.locallyCompactSpace
  obtain ⟨u, hu, hsep, hcount⟩ := exists_tuple_fixedSlice_count_rate
    F.inclusionN F.inclusionD F.action μ
    (F.action_preserves_haar T M hExp realize haarN haarD dynkinN hunimod μ)
    F.conjugation F.closedN hs (fun n _ => x n) (fun n _ => d n) S hS hvol
    (show 0 < (Λ : ℝ) * ((Λ : ℝ) + 1) by positivity)
  let t := fun n => (u n).image (fun v i => (p n).val.1 (v i))
  obtain ⟨htsep, htcount⟩ := normalizedPair_tuple_count_rate p hΛ u hsep hcount
  refine ⟨t, ?_, htsep, htcount⟩
  intro n y hy
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hy
  obtain ⟨w, hw, rfl⟩ := hu n hv
  exact ⟨w, hw, rfl⟩

end PolycyclicRecognition.CartanFactorModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanCoupledTargetTuples
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instDecidableEqConeMixedWords _root_.OAI.PolycyclicRecognition.CartanWordModel.instFintypeConeMixedWords _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.inversePairCoupling_finiteOnCompacts _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Separated target tuples from the actual coupled source recurrence

Successful parameters survive the passage from the joint source image to
good source states and then to separated target tuples.
-/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra MeasureTheory Filter Set Metric
open scoped Manifold Topology NNReal ENNReal

variable {EG G W : Type} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G]
  [IsIsometricSMul G G] [ProperSpace G]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {ExpG : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H ExpG)
  (hunimod : ∀ x : GroupLieAlgebra (𝓘(ℝ, EG)) G, LinearMap.trace ℝ _ (ad ℝ _ x) = 0)
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)
  [IsTopologicalGroup F.N.carrier] [SecondCountableTopology F.N.carrier]

set_option maxHeartbeats 1000000 in
theorem exists_coupled_target_tuples_oai
    (hExpG : IsGroupExponential ExpG)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
    (haarD : NilpotentExponentialHaarInput F.D.modelSpace F.D.carrier)
    (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (E source : Set W) (β γ : M.Bases)
    (hβ : IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
      (M.boxCost T hunimod eW E) β.val)
    (s : Fin M.letterCount → ℝ)
    (hs : ∀ i, s i ≤ (M.supportIn T hunimod eW).weightSupport E i)
    {m h c : ℕ} (letters : Fin m → Fin M.letterCount)
    (aN : DynkinCoefficients c 2)
    (hm : ∀ x y, F.ExpN (finiteDynkinPolynomial aN ![x, y]) = F.ExpN x * F.ExpN y)
    (scale R : ℕ → ℝ) (hscale : Tendsto scale atTop atTop)
    (hscale0 : ∀ n, 0 ≤ scale n) (hR0 : ∀ n, 0 ≤ R n)
    (hR : HasSubexponentialUpperBoundSeq scale R)
    (ρ : ℝ) (hρ : 1 ≤ ρ) (k₀ : ℕ → F.N.carrier) (k : ℕ → Fin h → F.N.carrier)
    (hk₀ : ∀ n, k₀ n ∈ M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) E β (scale n) (R n))
    (hk : ∀ n i, k n i ∈ M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) E β (scale n) (R n))
    (rem : RemezPolynomialInput) (hN : 1 ≤ h * finrank ℝ (cartanRootIdeal H))
    (p₀ : WordLawData (Fin M.letterCount) (finrank ℝ (cartanRootIdeal H)))
    (hlim : Tendsto (fun r =>
      let b := M.boxBasis T hunimod eW source γ (scale r)
      (basisBracket b, fun i => b.equivFun (Real.exp (scale r * s i) • M.letter i))) atTop (𝓝 p₀))
    (t₀ : Fin (m + m) → ℝ)
    (hsub : Function.Surjective (fderiv ℝ (differenceAmplitudeWordEndpoint aN letters p₀) t₀))
    (Good : ℕ → Set F.N.carrier) (hGood : ∀ n, MeasurableSet (Good n))
    {Λ : ℝ≥0} (hΛ : 0 < (Λ : ℝ)) (p : ℕ → NormalizedPair G Λ)
    (base : ℕ → G) (pivot : ℕ → F.D.carrier) :
    let μ := Measure.map ((F.ExpN ∘ F.N.equiv) ∘ b₀.equivFun.symm) volume
    let Q := fun n => (fun y => y * k₀ n) ''
      M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) E β (scale n) 1
    let allLetters := fun j : Fin (h * m) => letters (finProdFinEquiv.symm j).2
    let sample := fun n => coupledRootIntervalSample (F.ExpN ∘ F.N.equiv)
      allLetters M.letter s (scale n) (bundleConjugator m (k n))
    (∀ n, Good n ⊆ Q n) → (∀ n, 0 < (μ (Good n)).toReal) →
    HasSubexponentialLowerBoundSeq scale (fun n => (μ (Good n)).toReal / (μ (Q n)).toReal) →
    ∃ (initial : ℕ → F.N.carrier) (S : ℕ → Set (Fin h → F.N.carrier))
      (t : ℕ → Finset (Fin h → G)),
      (∀ n, initial n ∈ Good n) ∧ (∀ n, IsCompact (S n)) ∧
      (∀ n, (↑(t n) : Set (Fin h → G)) ⊆ (fun v => fun i =>
        basedImage (p n).val.1 (base n * F.inclusionN (initial n) * F.inclusionD (pivot n))
          (base n * F.inclusionN (v i) * F.inclusionD (pivot n))) '' S n) ∧
      (∀ n u, u ∈ t n → ∀ v, v ∈ t n → u ≠ v → 1 ≤ dist u v) ∧
      HasSubexponentialLowerBoundSeq scale (fun n => ((t n).card : ℝ) /
        Real.exp (scale n * ((h : ℝ) * columnBasisWeight (M.boxCost T hunimod eW source) γ.val))) ∧
      ∀ᶠ n in atTop, ∀ v ∈ S n, (∀ i, v i ∈ Good n) ∧
        ∃ z : Fin (h * m + h * m) → ℝ, z ∈ closedBall 0 ρ ∧
          SwitchSuccessful (fun _ => Good n) 0 (h * m) (initial n)
            (sampledSwitchParameters (sample n) (h * m) z) ∧
          v = sourceBundleStateEquiv h (initial n)
            (fun i => (innerContinuousMulEquiv (k n i)).toHomeomorph.toMeasurableEquiv)
            (sourceBundleProduct F.N.equiv F.ExpN M.letter s letters
              (bundleParameterChart h m) (scale n) z) := by
  dsimp only
  intro hGoodQ hGoodpos hGoodlower
  let : LocallyCompactSpace F.N.carrier := F.closedN.locallyCompactSpace
  let μ := Measure.map ((F.ExpN ∘ F.N.equiv) ∘ b₀.equivFun.symm) volume
  let : μ.IsHaarMeasure := exponential_basis_measure_isHaar haarN F.N.equiv
    (cartanRootIdeal_nilpotent H T) F.ExpN F.isExpN b₀
  let : μ.IsMulRightInvariant := exponential_basis_measure_isRightInvariant haarN F.N.equiv
    (cartanRootIdeal_nilpotent H T) F.ExpN F.isExpN b₀
  have h1 n : (1 : F.N.carrier) ∈
      M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) E β (scale n) (R n) := by
    refine ⟨0, ?_, ?_⟩
    · simp only [Function.comp_apply, map_zero, F.isExpN.map_zero]
    · simpa only [map_zero, norm_zero] using hR0 n
  obtain ⟨initial, C, hi, hC, hvol, hreach⟩ := M.coupled_source_bundle_haar_image_sequence
    T hunimod eW F.N.equiv F.ExpN F.isExpN haarN dynkinN b₀ E source β γ hβ s hs letters aN hm
    scale R hscale hscale0 hR0 hR ρ hρ k₀ (fun n => bundleConjugator m (k n)) hk₀
    (fun n j => bundleConjugator_mem (k n) (h1 n) (hk n) j)
    rem hN p₀ hlim t₀ hsub Good hGood hGoodQ hGoodpos hGoodlower
  let S := fun n => sourceBundleStateEquiv h (initial n)
    (fun i => (innerContinuousMulEquiv (k n i)).toHomeomorph.toMeasurableEquiv) '' C n
  obtain ⟨hS, hSvol, hSreach⟩ := good_coupled_source_bundle_image F.N.equiv F.ExpN F.isExpN
    M.letter s letters scale _ μ k Good initial hi C hC hvol ρ hreach
  let : IsTopologicalGroup G := topologicalGroup_of_lieGroup (𝓘(ℝ, EG)) ⊤
  let origin := fun n => base n * F.inclusionN (initial n) * F.inclusionD (pivot n)
  let p' := fun n => normalizedTranslate (origin n) (p n)
  obtain ⟨t, ht, htsep, htcount⟩ := F.exists_target_source_tuple_count T M hExpG realize
    haarN haarD dynkinN hunimod μ hΛ p' hscale (fun n => (origin n)⁻¹ * base n) pivot S hS hSvol
  refine ⟨initial, S, t, hi, hS, ?_, htsep, htcount, hSreach⟩
  intro n y hy
  obtain ⟨v, hv, rfl⟩ := ht n hy
  refine ⟨v, hv, ?_⟩
  funext i
  simp only [p', normalizedTranslate, translatePair, ContinuousMap.coe_mk, basedImage]
  simp only [mul_assoc, mul_inv_cancel_left, origin]

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

theorem solution : type_of% @OAI.PolycyclicRecognition.CartanWordModel.exists_coupled_target_tuples_oai := @OAI.PolycyclicRecognition.CartanWordModel.exists_coupled_target_tuples_oai
