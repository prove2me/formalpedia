-- Prove2me | solution 1 for OAI.PolycyclicRecognition.CartanWordModel.exists_boundary_family_with_compact_shadow
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-02T22:49:21.399339+00:00
-- url     : https://prove2.me/submissions/8cbfd996-ab45-4d76-a290-1b3a98b8305f

import Mathlib
import Definitions.Def_PolycyclicRecognition
import Definitions.Def_OAIQ093D027
import Theorems.Thm_OAI_PolycyclicRecognition_CartanWordModel_centered_ray_quotient_compact_limits
import Theorems.Thm_OAI_PolycyclicRecognition_CartanWordModel_ideal_fiber_quotient_difference_tendsto_one
import Theorems.Thm_OAI_PolycyclicRecognition_CartanWordModel_negative_chain_quotient_difference_tendsto_one

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
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
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

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_FiniteDynkinDifference
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.CartanFactorModel.realScaleProfile_apply _root_.OAI.PolycyclicRecognition.basisDynkinParameter_zero _root_.OAI.PolycyclicRecognition.bracketWordDifferential_mul _root_.OAI.PolycyclicRecognition.dynkinRightTranslation_apply _root_.OAI.PolycyclicRecognition.dynkinRightTranslation_symm_apply _root_.OAI.PolycyclicRecognition.exponentialHomOfDynkin_apply_exp _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.OAI.PolycyclicRecognition.wordBasisOfDet_val _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Difference bounds for the actual finite Dynkin polynomial

The middle input in a conjugation product vanishes at time zero. These
bounds retain that factor rather than losing it in an absolute polynomial
estimate; this gives polynomial coarse speed for Cartan-fiber paths.
-/

noncomputable section
namespace PolycyclicRecognition

open Module
open scoped BigOperators

variable {L J I : Type} [LieRing L] [LieAlgebra ℝ L] [Fintype J]
  (b : Basis J ℝ L)

/-- A bracket word is Lipschitz on a coordinate ball, with one fewer
power of its radius than the absolute word bound. -/
theorem norm_basis_evalBracketWord_sub_le
    (X Y : I → L) {C M D : ℝ} (hC : 0 ≤ C) (hM : 0 ≤ M) (hD : 0 ≤ D)
    (hbracket : ∀ i j k, |b.repr ⁅b i, b j⁆ k| ≤ C)
    (hX : ∀ i, ‖b.equivFun (X i)‖ ≤ M) (hY : ∀ i, ‖b.equivFun (Y i)‖ ≤ M)
    (hXY : ∀ i, ‖b.equivFun (X i - Y i)‖ ≤ D) (w : FreeMagma I) :
    ‖b.equivFun (evalBracketWord X w - evalBracketWord Y w)‖ ≤
      (bracketWordLength w : ℝ) * ((Fintype.card J : ℝ) ^ 2 * C) ^ bracketWordNodes w *
        M ^ bracketWordNodes w * D := by
  let K := (Fintype.card J : ℝ) ^ 2 * C
  have hK : 0 ≤ K := by positivity
  induction w using FreeMagma.rec with
  | of i => simpa [evalBracketWord, bracketWordLength, bracketWordNodes] using hXY i
  | mul u v hu hv =>
    have hxv := norm_basis_evalBracketWord_le b X hC hM hbracket hX v
    have hyu := norm_basis_evalBracketWord_le b Y hC hM hbracket hY u
    have he : ⁅evalBracketWord X u, evalBracketWord X v⁆ -
        ⁅evalBracketWord Y u, evalBracketWord Y v⁆ =
        ⁅evalBracketWord X u - evalBracketWord Y u, evalBracketWord X v⁆ +
          ⁅evalBracketWord Y u, evalBracketWord X v - evalBracketWord Y v⁆ := by
      simp only [sub_lie, lie_sub]
      abel
    change ‖b.equivFun (⁅evalBracketWord X u, evalBracketWord X v⁆ -
      ⁅evalBracketWord Y u, evalBracketWord Y v⁆)‖ ≤ _
    rw [he, map_add]
    calc
      _ ≤ ‖b.equivFun ⁅evalBracketWord X u - evalBracketWord Y u, evalBracketWord X v⁆‖ +
          ‖b.equivFun ⁅evalBracketWord Y u, evalBracketWord X v - evalBracketWord Y v⁆‖ :=
        norm_add_le _ _
      _ ≤ K * ‖b.equivFun (evalBracketWord X u - evalBracketWord Y u)‖ *
          ‖b.equivFun (evalBracketWord X v)‖ +
          K * ‖b.equivFun (evalBracketWord Y u)‖ *
            ‖b.equivFun (evalBracketWord X v - evalBracketWord Y v)‖ :=
        add_le_add (norm_basis_bracket_le b hC hbracket _ _)
          (norm_basis_bracket_le b hC hbracket _ _)
      _ ≤ K * ((bracketWordLength u : ℝ) * K ^ bracketWordNodes u * M ^ bracketWordNodes u * D) *
          (K ^ bracketWordNodes v * M ^ bracketWordLength v) +
          K * (K ^ bracketWordNodes u * M ^ bracketWordLength u) *
            ((bracketWordLength v : ℝ) * K ^ bracketWordNodes v * M ^ bracketWordNodes v * D) := by
        gcongr
      _ = _ := by
        simp only [bracketWordLength, bracketWordNodes, bracketWordLength_eq_nodes_add_one,
          Nat.cast_add, Nat.cast_one, pow_add, pow_one]
        ring

/-- Fixed finite Dynkin coefficients give a uniform polynomial Lipschitz
bound on coordinate balls. No extra group-law or analytic input is used. -/
theorem exists_finiteDynkinPolynomial_difference_bound
    {c n : ℕ} (a : DynkinCoefficients c n) {C : ℝ} (hC : 0 ≤ C)
    (hbracket : ∀ i j k, |b.repr ⁅b i, b j⁆ k| ≤ C) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (X Y : Fin n → L) (M D : ℝ), 0 ≤ M → 0 ≤ D →
      (∀ i, ‖b.equivFun (X i)‖ ≤ M) → (∀ i, ‖b.equivFun (Y i)‖ ≤ M) →
      (∀ i, ‖b.equivFun (X i - Y i)‖ ≤ D) →
      ‖b.equivFun (finiteDynkinPolynomial a X - finiteDynkinPolynomial a Y)‖ ≤
        A * (1 + M) ^ c * D := by
  let K := (Fintype.card J : ℝ) ^ 2 * C
  have hK : 0 ≤ K := by positivity
  let A := ∑ d : Fin c, ∑ w : Fin (d.val + 1) → Fin n,
    |a d w| * (d.val + 1) * K ^ d.val
  have hA : 0 ≤ A := by dsimp [A] <;> positivity
  refine ⟨A, hA, ?_⟩
  intro X Y M D hM hD hX hY hXY
  have he : finiteDynkinPolynomial a X - finiteDynkinPolynomial a Y =
      ∑ d : Fin c, ∑ w : Fin (d.val + 1) → Fin n,
        a d w • (evalBracketWord X (rightNestedWord d.val w) -
          evalBracketWord Y (rightNestedWord d.val w)) := by
    simp only [finiteDynkinPolynomial, Finset.sum_sub_distrib, smul_sub]
  have hterm (d : Fin c) (w : Fin (d.val + 1) → Fin n) :
      ‖b.equivFun (a d w • (evalBracketWord X (rightNestedWord d.val w) -
        evalBracketWord Y (rightNestedWord d.val w)))‖ ≤
        (|a d w| * (d.val + 1) * K ^ d.val) * (1 + M) ^ c * D := by
    rw [map_smul, norm_smul, Real.norm_eq_abs]
    have hh := norm_basis_evalBracketWord_sub_le b X Y hC hM hD hbracket hX hY hXY
      (rightNestedWord d.val w)
    simp only [rightNestedWord_length, rightNestedWord_nodes, Nat.cast_add, Nat.cast_one] at hh
    have hp : M ^ d.val ≤ (1 + M) ^ c :=
      (pow_le_pow_left₀ hM (by linarith) _).trans
        (pow_le_pow_right₀ (by linarith) d.isLt.le)
    calc
      _ ≤ |a d w| * ((d.val + 1) * K ^ d.val * M ^ d.val * D) :=
        mul_le_mul_of_nonneg_left hh (abs_nonneg _)
      _ ≤ |a d w| * ((d.val + 1) * K ^ d.val * (1 + M) ^ c * D) := by gcongr
      _ = _ := by ring
  rw [he, map_sum]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ d : Fin c, ∑ w : Fin (d.val + 1) → Fin n,
        (|a d w| * (d.val + 1) * K ^ d.val) * (1 + M) ^ c * D := by
      apply Finset.sum_le_sum
      intro d _
      rw [map_sum]
      exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun w _ => hterm d w))
    _ = _ := by simp only [A, Finset.sum_mul]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_GeodesicWords
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Word decompositions by sampling minimizing paths

This supplies the bounded-step word decomposition used in the stationary
estimate from actual metric paths. The number of steps is at most distance
plus one.
-/

noncomputable section

namespace PolycyclicRecognition

open Metric Set

/-- Subdivision of a minimizing path gives a word in the unit ball, with
length at most distance plus one. -/
theorem wordFactorization_of_minimizing_paths
    {G : Type} [Group G] [MetricSpace G] [IsIsometricSMul G G]
    (hpath : ∀ g : G, ∃ γ : ℝ → G, γ 0 = 1 ∧ γ 1 = g ∧
      ∀ t ∈ Icc (0 : ℝ) 1, ∀ u ∈ Icc (0 : ℝ) 1,
        dist (γ t) (γ u) ≤ dist 1 g * |t - u|) (g : G) :
    ∃ w : List G, (∀ q ∈ w, q ∈ closedBall 1 1) ∧ w.prod = g ∧
      (w.length : ℝ) ≤ dist 1 g + 1 := by
  obtain ⟨γ, h0, h1, hγ⟩ := hpath g
  let n := ⌊dist 1 g⌋₊ + 1
  have hn : 0 < n := Nat.succ_pos _
  have hnr : 0 < (n : ℝ) := by exact_mod_cast hn
  have hlen : dist 1 g ≤ (n : ℝ) := by
    simpa [n] using (Nat.lt_floor_add_one (dist 1 g)).le
  let v : ℕ → G := fun k => γ ((k : ℝ) / n)
  let w := (List.range n).map (fun k => (v k)⁻¹ * v (k + 1))
  refine ⟨w, ?_, ?_, ?_⟩
  · intro q hq
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hq
    have hk' : k < n := List.mem_range.mp hk
    have hkn : (k : ℝ) ≤ n := by exact_mod_cast hk'.le
    have hks : ((k + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast hk'
    have ht : (k : ℝ) / n ∈ Icc (0 : ℝ) 1 :=
      ⟨by positivity, (div_le_one hnr).mpr hkn⟩
    have hu : ((k + 1 : ℕ) : ℝ) / n ∈ Icc (0 : ℝ) 1 :=
      ⟨by positivity, (div_le_one hnr).mpr hks⟩
    have hdiff : |(k : ℝ) / n - ((k + 1 : ℕ) : ℝ) / n| = 1 / n := by
      rw [abs_of_nonpos (sub_nonpos.mpr (div_le_div_of_nonneg_right (by simp) hnr.le))]
      push_cast
      ring
    have hd : dist 1 ((v k)⁻¹ * v (k + 1)) = dist (v k) (v (k + 1)) := by
      simpa using (dist_mul_left (v k) (1 : G) ((v k)⁻¹ * v (k + 1))).symm
    rw [mem_closedBall, dist_comm, hd]
    refine (hγ _ ht _ hu).trans ?_
    rw [hdiff, mul_one_div]
    exact (div_le_one hnr).mpr hlen
  · have hp := List.prod_range_div' n (fun k => (v k)⁻¹)
    have hv0 : v 0 = 1 := by simp [v, h0]
    have hvn : v n = g := by simp [v, h1, hnr.ne']
    simpa [w, div_eq_mul_inv, hv0, hvn] using hp
  · simpa [w, n, Nat.cast_add, Nat.cast_one] using
      add_le_add_right (Nat.floor_le (dist_nonneg (x := (1 : G)) (y := g))) 1

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
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_ChainProducts
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instNonemptyBases _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_nonempty _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial coordinates for nilpotent chains

Every bounded-step chain is an actual product of its group increments.
Compactness bounds the increment logarithms in a global exponential chart.
The finite Dynkin identity then bounds all endpoint coordinates polynomially
in the number of steps. No geometric growth estimate is assumed.
-/

noncomputable section

namespace PolycyclicRecognition

open Module LieModule
open scoped Manifold

variable {G W : Type} [Group G] [MetricSpace G] [IsIsometricSMul G G]
  [NormedAddCommGroup W]

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [ChartedSpace E G] [LieGroup (𝓘(ℝ, E)) ⊤ G]
  [ProperSpace G]

/-- The finite list of basis brackets always has a common bound. -/
theorem exists_basis_structureConstant_bound {L : Type} [LieRing L] [LieAlgebra ℝ L]
    {J : Type} [Fintype J] (b : Basis J ℝ L) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ i j l, |b.repr ⁅b i, b j⁆ l| ≤ C := by
  obtain ⟨C, hC⟩ := (Set.finite_range (fun p : J × J × J =>
    |b.repr ⁅b p.1, b p.2.1⁆ p.2.2|)).bddAbove
  exact ⟨max C 0, le_max_right _ _, fun i j l =>
    (hC ⟨(i, j, l), rfl⟩).trans (le_max_left _ _)⟩

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_NilpotentConjugationCoordinates
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.basisDynkinParameter_zero _root_.OAI.PolycyclicRecognition.chartExponentialFlow_zero _root_.OAI.PolycyclicRecognition.derivationSemidirectHom_apply _root_.OAI.PolycyclicRecognition.dynkinRightTranslation_apply _root_.OAI.PolycyclicRecognition.dynkinRightTranslation_symm_apply _root_.OAI.PolycyclicRecognition.exponentialHomOfDynkin_apply_exp _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.integrateNilpotentLieEquiv_apply_exp _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial speed of a conjugated nilpotent one-parameter subgroup -/

noncomputable section
namespace PolycyclicRecognition

open Module LieModule
open scoped Manifold Topology

variable {E G J : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace G] [ChartedSpace E G] [Group G]
  [LieGroup (𝓘(ℝ, E)) ⊤ G] [T2Space G] [Fintype J]

/-- In a nilpotent group, conjugating a fixed exponential line by a ray
costs a polynomial in the ray parameter, retaining its linear time factor. -/
theorem exists_nilpotent_conjugation_coordinate_bound
    (dynkin : NilpotentDynkinExpansionInput E G)
    (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G) (hExp : IsGroupExponential Exp)
    (chart : GroupLieAlgebra (𝓘(ℝ, E)) G ≃ₜ G) (hchart : ∀ x, chart x = Exp x)
    {c : ℕ} (hc : lowerCentralSeries ℝ (GroupLieAlgebra (𝓘(ℝ, E)) G)
      (GroupLieAlgebra (𝓘(ℝ, E)) G) c = ⊥)
    (b : Basis J ℝ (GroupLieAlgebra (𝓘(ℝ, E)) G))
    (u v : GroupLieAlgebra (𝓘(ℝ, E)) G) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (n : ℕ) (s : ℝ), |s| ≤ 1 →
      ‖b.equivFun (chart.symm
        (Exp (-(n : ℝ) • v) * Exp (s • u) * Exp ((n : ℝ) • v)))‖ ≤
          A * (1 + n) ^ c * |s| := by
  obtain ⟨coeff, _, hprod⟩ := dynkin Exp hExp c hc 3
  obtain ⟨C, hC, hbr⟩ := exists_basis_structureConstant_bound b
  obtain ⟨B, hB, hdiff⟩ := exists_finiteDynkinPolynomial_difference_bound b coeff hC hbr
  let U := ‖b.equivFun u‖
  let V := ‖b.equivFun v‖
  have hU : 0 ≤ U := norm_nonneg _
  have hV : 0 ≤ V := norm_nonneg _
  refine ⟨B * (1 + U + V) ^ c * U, by positivity, ?_⟩
  intro n s hs
  let X : Fin 3 → GroupLieAlgebra (𝓘(ℝ, E)) G := ![-(n : ℝ) • v, s • u, (n : ℝ) • v]
  let Y : Fin 3 → GroupLieAlgebra (𝓘(ℝ, E)) G := ![-(n : ℝ) • v, 0, (n : ℝ) • v]
  let M := (n : ℝ) * V + U
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hM : 0 ≤ M := by dsimp [M] <;> positivity
  have hX (i : Fin 3) : ‖b.equivFun (X i)‖ ≤ M := by
    fin_cases i <;> simp [X, map_smul, norm_smul, Real.norm_eq_abs]
    · change (n : ℝ) * V ≤ M
      dsimp [M] <;> linarith
    · change |s| * U ≤ M
      dsimp [M] <;> nlinarith
    · change (n : ℝ) * V ≤ M
      dsimp [M] <;> linarith
  have hY (i : Fin 3) : ‖b.equivFun (Y i)‖ ≤ M := by
    fin_cases i
    · simpa [X, Y] using hX 0
    · simpa [Y] using hM
    · simpa [X, Y] using hX 2
  have hXY (i : Fin 3) : ‖b.equivFun (X i - Y i)‖ ≤ U * |s| := by
    fin_cases i
    · simpa [X, Y] using mul_nonneg hU (abs_nonneg s)
    · simp [X, Y, U, norm_smul, Real.norm_eq_abs, mul_comm]
    · simpa [X, Y] using mul_nonneg hU (abs_nonneg s)
  have hYzero : finiteDynkinPolynomial coeff Y = 0 := by
    apply chart.injective
    rw [hchart, hchart, hExp.map_zero]
    have hy := (hprod Y).symm
    simpa [Y, List.ofFn_succ, neg_smul, hExp.map_neg, hExp.map_zero] using hy
  have hproduct : Exp (-(n : ℝ) • v) * Exp (s • u) * Exp ((n : ℝ) • v) =
      Exp (finiteDynkinPolynomial coeff X) := by
    simpa [X, List.ofFn_succ, mul_assoc] using hprod X
  have hh := hdiff X Y M (U * |s|) hM (mul_nonneg hU (abs_nonneg s)) hX hY hXY
  rw [hYzero, sub_zero] at hh
  have hp : (1 + M) ^ c ≤ ((1 + U + V) * (1 + (n : ℝ))) ^ c := by
    apply pow_le_pow_left₀ (by positivity)
    dsimp [M]
    nlinarith
  rw [hproduct, ← hchart, chart.symm_apply_apply]
  apply hh.trans
  calc
    B * (1 + M) ^ c * (U * |s|) ≤ B * ((1 + U + V) * (1 + (n : ℝ))) ^ c * (U * |s|) := by
      gcongr
    _ = _ := by rw [mul_pow]; ring

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_CoarseNegativeQuotient
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Quotient asymptotics of actual negative-height chains

Sublinear height error preserves a linear negative margin on a linear ball.
Polynomial metric factor bounds and compact unit increments then give
asymptotic equality of the projected endpoints.
-/

noncomputable section
namespace PolycyclicRecognition

open Module LieModule Filter Set
open scoped Manifold Topology

/-- A continuous linear functional preserves a global sublinear error.
The constant is chosen before the scale, including for the zero functional. -/
theorem scalar_sublinear_error
    {X W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W]
    (length : X → ℝ) (hlen : ∀ x, 0 ≤ length x)
    (u v : X → W) (α : W →L[ℝ] ℝ)
    (hsub : ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, 0 ≤ B ∧ ∀ x,
      ‖u x - v x‖ ≤ ε * length x + B) :
    ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, 0 ≤ B ∧ ∀ x,
      |α (u x) - α (v x)| ≤ ε * length x + B := by
  intro ε hε
  have hd : 0 < ‖α‖ + 1 := by positivity
  obtain ⟨B, hB, hb⟩ := hsub (ε / (‖α‖ + 1)) (div_pos hε hd)
  refine ⟨‖α‖ * B, by positivity, ?_⟩
  intro x
  have hcoef : ‖α‖ * (ε / (‖α‖ + 1)) ≤ ε := by
    rw [← mul_div_assoc]
    apply (div_le_iff₀ hd).mpr
    nlinarith
  calc
    _ = ‖α (u x - v x)‖ := by rw [map_sub, Real.norm_eq_abs]
    _ ≤ ‖α‖ * ‖u x - v x‖ := α.le_opNorm _
    _ ≤ ‖α‖ * ((ε / (‖α‖ + 1)) * length x + B) :=
      mul_le_mul_of_nonneg_left (hb x) (norm_nonneg _)
    _ = (‖α‖ * (ε / (‖α‖ + 1))) * length x + ‖α‖ * B := by ring
    _ ≤ ε * length x + ‖α‖ * B :=
      add_le_add (mul_le_mul_of_nonneg_right hcoef (hlen x)) le_rfl

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
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_ControlledChainWords
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Bounded-step words near a coarse chain

Sampling a coarse path gives finitely many jumps. Replacing each jump by a
short word in the unit ball gives a controlled word whose every prefix stays
near a sampled vertex. The minimizing-path hypothesis is the same concrete
metric hypothesis used by `GeodesicWords` and the stationary sublinearity bridge.
-/

namespace PolycyclicRecognition

open Metric Set

variable {G : Type} [Group G] [MetricSpace G] [IsIsometricSMul G G]

/-- A unit-step word has distance at most its length from the identity. -/
theorem dist_one_list_prod_le_length (w : List G)
    (hw : ∀ g ∈ w, g ∈ closedBall (1 : G) 1) :
    dist (1 : G) w.prod ≤ w.length := by
  induction w with
  | nil => simp
  | cons g w ih =>
    have hg : dist (1 : G) g ≤ 1 := by
      simpa only [mem_closedBall, dist_comm] using hw g (by simp)
    have ht := ih (fun x hx => hw x (by simp [hx]))
    calc
      dist (1 : G) (g :: w).prod ≤ dist (1 : G) g + dist g (g * w.prod) :=
        dist_triangle _ _ _
      _ = dist (1 : G) g + dist (1 : G) w.prod := by
        congr 1
        simpa only [mul_one] using dist_mul_left g (1 : G) w.prod
      _ ≤ 1 + (w.length : ℝ) := add_le_add hg ht
      _ = _ := by simp <;> ring

/-- Replacing the jumps of a finite chain by unit-step words preserves the
endpoint, has controlled total length, and stays within one jump bound of
the sampled chain at every prefix. -/
theorem exists_word_near_chain
    (hpath : ∀ g : G, ∃ γ : ℝ → G, γ 0 = 1 ∧ γ 1 = g ∧
      ∀ t ∈ Icc (0 : ℝ) 1, ∀ u ∈ Icc (0 : ℝ) 1,
        dist (γ t) (γ u) ≤ dist 1 g * |t - u|)
    (v : ℕ → G) (hv0 : v 0 = 1) {D : ℝ} (hD : 0 ≤ D) (n : ℕ)
    (hstep : ∀ i < n, dist (v i) (v (i + 1)) ≤ D) :
    ∃ w : List G, (∀ g ∈ w, g ∈ closedBall (1 : G) 1) ∧ w.prod = v n ∧
      (w.length : ℝ) ≤ (n : ℝ) * (D + 1) ∧
      ∀ j : ℕ, ∃ i ≤ n, dist (w.take j).prod (v i) ≤ D + 1 := by
  induction n with
  | zero =>
    refine ⟨[], by simp, by simpa using hv0.symm, by simp, ?_⟩
    intro j
    exact ⟨0, le_rfl, by simp [hv0] <;> linarith⟩
  | succ n ih =>
    obtain ⟨w, hw, hprod, hlen, hnear⟩ := ih (fun i hi => hstep i (Nat.lt_succ_of_lt hi))
    obtain ⟨u, hu, huProd, huLen⟩ :=
      wordFactorization_of_minimizing_paths hpath ((v n)⁻¹ * v (n + 1))
    have hd : dist (1 : G) ((v n)⁻¹ * v (n + 1)) = dist (v n) (v (n + 1)) := by
      simpa only [mul_one, mul_inv_cancel_left] using
        (dist_mul_left (v n) (1 : G) ((v n)⁻¹ * v (n + 1))).symm
    have hlenU : (u.length : ℝ) ≤ D + 1 := by linarith [hstep n (Nat.lt_succ_self n)]
    refine ⟨w ++ u, ?_, ?_, ?_, ?_⟩
    · intro g hg
      rcases List.mem_append.mp hg with hg | hg
      · exact hw g hg
      · exact hu g hg
    · rw [List.prod_append, hprod, huProd, mul_inv_cancel_left]
    · simp only [List.length_append, Nat.cast_add, Nat.cast_succ]
      nlinarith
    · intro j
      by_cases hj : j ≤ w.length
      · rw [List.take_append_of_le_length hj]
        obtain ⟨i, hi, hdist⟩ := hnear j
        exact ⟨i, hi.trans (Nat.le_succ n), hdist⟩
      · have hj' : w.length ≤ j := by omega
        rw [List.take_append, List.take_of_length_le hj', List.prod_append, hprod]
        refine ⟨n, Nat.le_succ n, ?_⟩
        calc
          dist (v n * (u.take (j - w.length)).prod) (v n) =
              dist (1 : G) (u.take (j - w.length)).prod := by
            simpa only [mul_one, dist_comm] using
              dist_mul_left (v n) (u.take (j - w.length)).prod (1 : G)
          _ ≤ ((u.take (j - w.length)).length : ℝ) :=
            dist_one_list_prod_le_length _ (fun g hg => hu g (List.mem_of_mem_take hg))
          _ ≤ (u.length : ℝ) := by exact_mod_cast List.length_take_le' (j - w.length) u
          _ ≤ D + 1 := hlenU

end PolycyclicRecognition

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_CoarsePathWords
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Subdividing coarse paths into bounded-increment words

A path with speed `L` and additive error `κ` admits a unit-step word of
length at most `(L + 1) * (κ + 2)`. Its prefixes remain within `κ + 2` of
points on the path. In the application `L = O(r)` and `κ = O(log r)`, so this
loss is polynomial and its extra height error is sublinear.
-/

noncomputable section

namespace PolycyclicRecognition

open Metric Set

variable {G : Type} [Group G] [MetricSpace G] [IsIsometricSMul G G]

/-- A coarse path has a polynomially controlled unit-step word, with every
prefix close to an actual point on that same path. -/
theorem exists_word_near_coarse_path
    (hpath : ∀ g : G, ∃ γ : ℝ → G, γ 0 = 1 ∧ γ 1 = g ∧
      ∀ t ∈ Icc (0 : ℝ) 1, ∀ u ∈ Icc (0 : ℝ) 1,
        dist (γ t) (γ u) ≤ dist 1 g * |t - u|)
    {g : G} (γ : Path (1 : G) g) {L κ : ℝ} (hL : 0 ≤ L) (hκ : 0 ≤ κ)
    (hγ : PathMetricBound γ L κ) :
    ∃ w : List G, (∀ x ∈ w, x ∈ closedBall (1 : G) 1) ∧ w.prod = g ∧
      (w.length : ℝ) ≤ (L + 1) * (κ + 2) ∧
      ∀ j : ℕ, ∃ t : unitInterval, dist (w.take j).prod (γ t) ≤ κ + 2 := by
  let n := ⌊L⌋₊ + 1
  have hn : 0 < n := Nat.succ_pos _
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hLn : L ≤ (n : ℝ) := by simpa only [n, Nat.cast_add, Nat.cast_one] using
    (Nat.lt_floor_add_one L).le
  have hnL : (n : ℝ) ≤ L + 1 := by simpa only [n, Nat.cast_add, Nat.cast_one] using
    (add_le_add (Nat.floor_le hL) (show (1 : ℝ) ≤ 1 from le_rfl))
  let v : ℕ → G := fun i => γ (subdivisionPoint n hn i)
  have hv0 : v 0 = 1 := by simp [v]
  have hvn : v n = g := by simp [v]
  have hstep (i : ℕ) (hi : i < n) : dist (v i) (v (i + 1)) ≤ 1 + κ := by
    have hdiff : |(i : ℝ) / n - ((i + 1 : ℕ) : ℝ) / n| = 1 / n := by
      rw [abs_of_nonpos (sub_nonpos.mpr (div_le_div_of_nonneg_right
        (by exact_mod_cast Nat.le_succ i) hn'.le))]
      push_cast
      ring
    calc
      _ ≤ L * |(subdivisionPoint n hn i : ℝ) - subdivisionPoint n hn (i + 1)| + κ := hγ _ _
      _ = L / n + κ := by
        rw [subdivisionPoint_coe n hn hi.le,
          subdivisionPoint_coe n hn (Nat.succ_le_of_lt hi), hdiff, mul_one_div]
      _ ≤ 1 + κ := add_le_add ((div_le_one hn').mpr hLn) le_rfl
  obtain ⟨w, hw, hprod, hlen, hnear⟩ := exists_word_near_chain hpath v hv0
    (show 0 ≤ 1 + κ by linarith) n hstep
  refine ⟨w, hw, hprod.trans hvn, ?_, ?_⟩
  · calc
      (w.length : ℝ) ≤ (n : ℝ) * (κ + 2) := by convert hlen using 1 <;> first | rfl | ring
      _ ≤ (L + 1) * (κ + 2) := mul_le_mul_of_nonneg_right hnL (by linarith)
  · intro j
    obtain ⟨i, _, hi⟩ := hnear j
    exact ⟨subdivisionPoint n hn i, by convert hi using 1; ring⟩

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_NegativePathWords
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_nonempty _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Unit-step words remain in the negative halfspace

This is the concrete subdivision needed for quotient-boundary independence.
The logarithmic mesh error is absorbed into half of the negative height gap.
-/

noncomputable section
namespace PolycyclicRecognition

open Filter Metric Set
open scoped Topology

variable {G : Type} [Group G] [MetricSpace G] [IsTopologicalGroup G]
  [IsIsometricSMul G G]

omit [IsTopologicalGroup G] in
/-- Integer points of an actual one-parameter subgroup lie in a linear
ball. This supplies the absolute radius of the negative-height ray pivots. -/
theorem one_parameter_nat_dist_le
    (d : ℝ → G) (hzero : d 0 = 1) (hmul : ∀ s t, d (s + t) = d s * d t)
    (n : ℕ) : dist 1 (d n) ≤ (n : ℝ) * dist 1 (d 1) := by
  have he : d (n : ℝ) = d 1 ^ n := by
    induction n with
    | zero => simpa only [Nat.cast_zero, pow_zero] using hzero
    | succ n ih => rw [Nat.cast_succ, hmul, ih, pow_succ]
  rw [he]
  exact dist_one_pow_le _ _

omit [IsTopologicalGroup G] in
/-- Retain the actual prefixes of an eventually specified unit-step word.
Their absolute radius follows by adding the radius of the starting point. -/
theorem exists_negative_word_prefix_chains
    (height : G → ℝ) (base target : ℕ → G) {C D gap : ℝ} {q : ℕ}
    (hbase : ∀ n : ℕ, dist 1 (base n) ≤ D * n)
    (hwords : ∀ᶠ n : ℕ in atTop, ∃ w : List G,
      (∀ g ∈ w, g ∈ closedBall (1 : G) 1) ∧ w.prod = (base n)⁻¹ * target n ∧
      (w.length : ℝ) ≤ C * (1 + n) ^ q ∧ ∀ i : ℕ,
        height (base n * (w.take i).prod) ≤ -gap * n ∧
        dist (base n) (base n * (w.take i).prod) ≤ C * n) :
    ∃ (m : ℕ → ℕ) (z : ℕ → ℕ → G),
      (∀ n, z n 0 = base n) ∧
      (∀ᶠ n in atTop, z n (m n) = target n) ∧
      (∀ᶠ n in atTop, (m n : ℝ) ≤ C * (1 + n) ^ q) ∧
      (∀ᶠ n in atTop, ∀ i ≤ m n, height (z n i) ≤ -gap * n) ∧
      (∀ᶠ n in atTop, ∀ i ≤ m n, dist 1 (z n i) ≤ (D + C) * n) ∧
      ∀ᶠ n in atTop, ∀ i < m n, dist (z n i) (z n (i + 1)) ≤ 1 := by
  classical
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.mp hwords
  let w : ℕ → List G := fun n => if hn : n₀ ≤ n then (hn₀ n hn).choose else []
  have hw (n : ℕ) (hn : n₀ ≤ n) :
      (∀ g ∈ w n, g ∈ closedBall (1 : G) 1) ∧ (w n).prod = (base n)⁻¹ * target n ∧
      ((w n).length : ℝ) ≤ C * (1 + n) ^ q ∧ ∀ i : ℕ,
        height (base n * ((w n).take i).prod) ≤ -gap * n ∧
        dist (base n) (base n * ((w n).take i).prod) ≤ C * n := by
    simpa only [w, dite_eq_left hn] using (hn₀ n hn).choose_spec
  let z := fun n i => base n * ((w n).take i).prod
  refine ⟨fun n => (w n).length, z, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n
    simp [z]
  · filter_upwards [eventually_ge_atTop n₀] with n hn
    simp only [z, List.take_length, (hw n hn).2.1, mul_inv_cancel_left]
  · filter_upwards [eventually_ge_atTop n₀] with n hn
    exact (hw n hn).2.2.1
  · filter_upwards [eventually_ge_atTop n₀] with n hn
    exact fun i _ => ((hw n hn).2.2.2 i).1
  · filter_upwards [eventually_ge_atTop n₀] with n hn
    intro i _
    have htri := dist_triangle (1 : G) (base n) (z n i)
    have hi := ((hw n hn).2.2.2 i).2
    have hb := hbase n
    dsimp only [z] at htri ⊢
    linarith
  · filter_upwards [eventually_ge_atTop n₀] with n hn
    intro i hi
    change dist (base n * ((w n).take i).prod) (base n * ((w n).take (i + 1)).prod) ≤ 1
    rw [List.prod_take_succ _ _ hi, dist_mul_left]
    have he : dist ((w n).take i).prod (((w n).take i).prod * (w n)[i]) =
        dist (1 : G) (w n)[i] := by
      simpa only [mul_one] using dist_mul_left ((w n).take i).prod (1 : G) (w n)[i]
    rw [he]
    simpa only [mem_closedBall, dist_comm] using (hw n hn).1 _ (List.getElem_mem hi)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_ExponentialCoarseMetric
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform coarse metric bounds for exponential lines -/

noncomputable section
namespace PolycyclicRecognition

open Set Metric

variable {V G : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] [Group G] [MetricSpace G] [IsIsometricSMul G G]

/-- Continuity on one fixed unit ball and the one-parameter identity give
one uniform coarse metric bound for all exponential directions. -/
theorem continuous_radial_exponential_metric_bound
    (Exp : V → G) (hcont : Continuous Exp) (hzero : Exp 0 = 1)
    (hmul : ∀ v : V, ∀ s t : ℝ, Exp ((s + t) • v) = Exp (s • v) * Exp (t • v)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v : V, dist 1 (Exp v) ≤ C * (1 + ‖v‖) := by
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : V) 1).exists_bound_of_continuousOn
    ((continuous_const : Continuous (fun _ : V => (1 : G))).dist hcont).continuousOn
  let B := max C 0
  have hB : 0 ≤ B := le_max_right _ _
  refine ⟨B, hB, ?_⟩
  intro v
  let n := ⌊‖v‖⌋₊ + 1
  have hn : 0 < (n : ℝ) := by exact_mod_cast (Nat.succ_pos ⌊‖v‖⌋₊)
  have hvn : ‖v‖ ≤ (n : ℝ) := by simpa only [n, Nat.cast_add, Nat.cast_one] using
    (Nat.lt_floor_add_one ‖v‖).le
  have hnv : (n : ℝ) ≤ ‖v‖ + 1 := by
    have hh := Nat.floor_le (norm_nonneg v)
    dsimp [n]
    push_cast
    linarith
  let w := (n : ℝ)⁻¹ • v
  have hw : w ∈ closedBall (0 : V) 1 := by
    rw [mem_closedBall, dist_zero_right]
    dsimp [w]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hn)]
    exact (inv_mul_le_iff₀ hn).mpr (by simpa using hvn)
  have hlocal : dist 1 (Exp w) ≤ B := by
    have hh := (hC w hw).trans (le_max_left C 0)
    simpa only [Real.norm_eq_abs, abs_of_nonneg dist_nonneg] using hh
  have hpow : ∀ k : ℕ, Exp ((k : ℝ) • w) = Exp w ^ k := by
    intro k
    induction k with
    | zero => simp [hzero]
    | succ k ih => rw [Nat.cast_succ, hmul, ih, one_smul, pow_succ]
  have hv : (n : ℝ) • w = v := by
    dsimp [w]
    rw [smul_smul, mul_inv_cancel₀ (ne_of_gt hn), one_smul]
  conv_lhs => rw [← hv, hpow n]
  apply (dist_one_pow_le _ _).trans
  calc
    _ ≤ (n : ℝ) * B := mul_le_mul_of_nonneg_left hlocal hn.le
    _ ≤ B * (1 + ‖v‖) := by nlinarith

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_NilpotentConjugationMetric
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.chartExponentialFlow_zero _root_.OAI.PolycyclicRecognition.derivationSemidirectHom_apply _root_.OAI.PolycyclicRecognition.exponentialHomOfDynkin_apply_exp _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.integrateNilpotentLieEquiv_apply_exp _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial coarse speed of right-translated nilpotent lines -/

noncomputable section
namespace PolycyclicRecognition

open Module LieModule
open scoped Manifold Topology

variable {E D G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace D] [ChartedSpace E D] [Group D]
  [LieGroup (𝓘(ℝ, E)) ⊤ D] [T2Space D]
  [Group G] [MetricSpace G] [IsIsometricSMul G G]

/-- In any continuously embedded nilpotent factor, right translation by
a ray has polynomial coarse speed on each fixed exponential line. -/
theorem exists_nilpotent_right_translate_coarse_metric
    (κ : D →* G) (hκ : Continuous κ)
    (dynkin : NilpotentDynkinExpansionInput E D)
    (Exp : GroupLieAlgebra (𝓘(ℝ, E)) D → D) (hExp : IsGroupExponential Exp)
    (chart : GroupLieAlgebra (𝓘(ℝ, E)) D ≃ₜ D) (hchart : ∀ x, chart x = Exp x)
    {c : ℕ} (hc : lowerCentralSeries ℝ (GroupLieAlgebra (𝓘(ℝ, E)) D)
      (GroupLieAlgebra (𝓘(ℝ, E)) D) c = ⊥)
    {m : ℕ} (b : Basis (Fin m) ℝ (GroupLieAlgebra (𝓘(ℝ, E)) D))
    (u v : GroupLieAlgebra (𝓘(ℝ, E)) D) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (n : ℕ) (s t : ℝ), |t - s| ≤ 1 →
      dist (κ (Exp (s • u) * Exp ((n : ℝ) • v)))
        (κ (Exp (t • u) * Exp ((n : ℝ) • v))) ≤
          C * (1 + n) ^ c * |t - s| + C := by
  let Φ : (Fin m → ℝ) → G := fun w => κ (Exp (b.equivFun.symm w))
  have hcont : Continuous Φ := by
    have he : Exp = chart := (funext hchart).symm
    exact hκ.comp ((he ▸ chart.continuous).comp b.equivFun.symm.toContinuousLinearEquiv.continuous)
  have hzero : Φ 0 = 1 := by simp [Φ, hExp.map_zero]
  have hmul (w : Fin m → ℝ) (s t : ℝ) : Φ ((s + t) • w) = Φ (s • w) * Φ (t • w) := by
    simp only [Φ, map_smul, hExp.map_add_smul, map_mul]
  obtain ⟨B, hB, hmetric⟩ := continuous_radial_exponential_metric_bound Φ hcont hzero hmul
  obtain ⟨A, hA, hcoords⟩ := exists_nilpotent_conjugation_coordinate_bound
    dynkin Exp hExp chart hchart hc b u v
  let C := B * (A + 1)
  have hC : 0 ≤ C := by dsimp [C] <;> positivity
  refine ⟨C, hC, ?_⟩
  intro n s t hst
  let d := Exp ((n : ℝ) • v)
  have hprod : Exp (s • u) * Exp ((t - s) • u) = Exp (t • u) := by
    rw [← hExp.map_add_smul, show s + (t - s) = t by ring]
  have hdiff : (Exp (s • u))⁻¹ * Exp (t • u) = Exp ((t - s) • u) := by
    rw [← hprod, inv_mul_cancel_left]
  have hrel : (κ (Exp (s • u) * d))⁻¹ * κ (Exp (t • u) * d) =
      κ (Exp (-(n : ℝ) • v) * Exp ((t - s) • u) * d) := by
    rw [← map_inv, ← map_mul, mul_inv_rev]
    have hd : d⁻¹ = Exp (-(n : ℝ) • v) := by
      dsimp [d]
      rw [neg_smul, hExp.map_neg]
    rw [hd]
    simpa only [mul_assoc] using congrArg (fun q => κ (Exp (-(n : ℝ) • v) * q * d)) hdiff
  have hdist : dist (κ (Exp (s • u) * d)) (κ (Exp (t • u) * d)) =
      dist 1 ((κ (Exp (s • u) * d))⁻¹ * κ (Exp (t • u) * d)) := by
    simpa only [mul_one, mul_inv_cancel_left] using
      dist_mul_left (κ (Exp (s • u) * d)) (1 : G)
        ((κ (Exp (s • u) * d))⁻¹ * κ (Exp (t • u) * d))
  rw [hdist, hrel]
  let g := Exp (-(n : ℝ) • v) * Exp ((t - s) • u) * d
  have hg : Φ (b.equivFun (chart.symm g)) = κ g := by
    simp only [Φ, b.equivFun.symm_apply_apply]
    rw [← hchart, chart.apply_symm_apply]
  have hm := hmetric (b.equivFun (chart.symm g))
  rw [hg] at hm
  have hc' := hcoords n (t - s) hst
  change ‖b.equivFun (chart.symm g)‖ ≤ A * (1 + n) ^ c * |t - s| at hc'
  apply hm.trans
  have hBA : B * A ≤ C := by dsimp [C] <;> nlinarith
  have hBC : B ≤ C := by dsimp [C] <;> nlinarith
  have hp : 0 ≤ (1 + (n : ℝ)) ^ c := by positivity
  calc
    _ ≤ B * (1 + A * (1 + (n : ℝ)) ^ c * |t - s|) := by gcongr
    _ ≤ C * (1 + (n : ℝ)) ^ c * |t - s| + C := by
      nlinarith [mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hBA hp) (abs_nonneg (t - s))]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_PolynomialNegativePaths
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomially subdivided paths at negative height -/

noncomputable section
namespace PolycyclicRecognition

open Filter Metric Set
open scoped Topology

variable {G : Type} [Group G] [MetricSpace G] [IsTopologicalGroup G]
  [IsIsometricSMul G G]

/-- A polynomial coarse speed with a constant mesh error suffices for
polynomially many unit steps. Negative linear height survives subdivision. -/
theorem polynomial_negative_path_chains
    (hpath : ∀ g : G, ∃ γ : ℝ → G, γ 0 = 1 ∧ γ 1 = g ∧
      ∀ t ∈ Icc (0 : ℝ) 1, ∀ u ∈ Icc (0 : ℝ) 1,
        dist (γ t) (γ u) ≤ dist 1 g * |t - u|)
    (height : G → ℝ) {K C R a : ℝ} {q : ℕ}
    (hK : 0 ≤ K) (hC : 0 ≤ C) (hR : 0 ≤ R) (ha : 0 < a)
    (hheight : ∀ x y, |height x - height y| ≤ K * dist x y)
    (source target : ℕ → G)
    (hsource : ∀ n, dist 1 (source n) ≤ R * n)
    (hγ : ∀ᶠ n : ℕ in atTop, ∃ γ : Path (source n) (target n),
      PathMetricBound γ (C * (1 + n) ^ q) C ∧
      (∀ t, height (γ t) ≤ -a * n) ∧ (∀ t, dist 1 (γ t) ≤ R * n)) :
    ∃ B : ℝ, 0 ≤ B ∧ ∃ (m : ℕ → ℕ) (z : ℕ → ℕ → G),
      (∀ n, z n 0 = source n) ∧
      (∀ᶠ n in atTop, z n (m n) = target n) ∧
      (∀ᶠ n in atTop, (m n : ℝ) ≤ B * (1 + n) ^ q) ∧
      (∀ᶠ n in atTop, ∀ i ≤ m n, height (z n i) ≤ -(a / 2) * n) ∧
      (∀ᶠ n in atTop, ∀ i ≤ m n, dist 1 (z n i) ≤ B * n) ∧
      ∀ᶠ n in atTop, ∀ i < m n, dist (z n i) (z n (i + 1)) ≤ 1 := by
  let B := (C + 1) * (C + 2) + 3 * R + C + 2
  have hB : 0 ≤ B := by dsimp [B] <;> positivity
  have herr : ∀ᶠ n : ℕ in atTop, K * (C + 2) ≤ (a / 2) * n := by
    have ht : Tendsto (fun n : ℕ => (a / 2) * (n : ℝ)) atTop atTop :=
      (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop).const_mul_atTop
        (by linarith)
    exact ht.eventually (eventually_ge_atTop _)
  have hwords : ∀ᶠ n : ℕ in atTop, ∃ w : List G,
      (∀ g ∈ w, g ∈ closedBall (1 : G) 1) ∧
      w.prod = (source n)⁻¹ * target n ∧
      (w.length : ℝ) ≤ (B - R) * (1 + n) ^ q ∧ ∀ i : ℕ,
        height (source n * (w.take i).prod) ≤ -(a / 2) * n ∧
        dist (source n) (source n * (w.take i).prod) ≤ (B - R) * n := by
    filter_upwards [hγ, herr, eventually_ge_atTop (1 : ℕ)] with n hn he hn1
    obtain ⟨γ, hmetric, hnegative, hradius⟩ := hn
    let η : Path (1 : G) ((source n)⁻¹ * target n) := {
      toFun := fun t => (source n)⁻¹ * γ t
      continuous_toFun := continuous_const.mul γ.continuous
      source' := by simp
      target' := by simp }
    have hη : PathMetricBound η (C * (1 + n) ^ q) C := by
      intro s t
      change dist ((source n)⁻¹ * γ s) ((source n)⁻¹ * γ t) ≤ _
      rw [dist_mul_left]
      exact hmetric s t
    obtain ⟨w, hw, hp, hlen, hnear⟩ := exists_word_near_coarse_path hpath η
      (by positivity) hC hη
    have hpow : 1 ≤ (1 + (n : ℝ)) ^ q := one_le_pow₀ (by have := Nat.cast_nonneg (α := ℝ) n; linarith)
    have hcoef : (C + 1) * (C + 2) ≤ B - R := by dsimp [B] <;> nlinarith
    refine ⟨w, hw, hp, hlen.trans ?_, ?_⟩
    · calc
        (C * (1 + (n : ℝ)) ^ q + 1) * (C + 2) ≤
            ((C + 1) * (1 + (n : ℝ)) ^ q) * (C + 2) := by gcongr; nlinarith
        _ = ((C + 1) * (C + 2)) * (1 + (n : ℝ)) ^ q := by ring
        _ ≤ (B - R) * (1 + (n : ℝ)) ^ q := by gcongr
    · intro i
      obtain ⟨t, ht⟩ := hnear i
      have hdist : dist (source n * (w.take i).prod) (γ t) ≤ C + 2 := by
        have hh := dist_mul_left (source n) (w.take i).prod (η t)
        change dist (source n * (w.take i).prod) (source n * ((source n)⁻¹ * γ t)) = _ at hh
        rw [mul_inv_cancel_left] at hh
        rwa [hh]
      constructor
      · have hsigned := (le_abs_self (height (source n * (w.take i).prod) - height (γ t))).trans
          ((hheight _ _).trans (mul_le_mul_of_nonneg_left hdist hK))
        have hneg := hnegative t
        nlinarith
      · have hs := hsource n
        have hr := hradius t
        have htri := dist_triangle (source n) (γ t) (source n * (w.take i).prod)
        have hrad := dist_triangle (source n) (1 : G) (γ t)
        rw [dist_comm (γ t)] at htri
        rw [dist_comm (source n) (1 : G)] at hrad
        have hn1' : (1 : ℝ) ≤ n := by exact_mod_cast hn1
        have hCR : 0 ≤ C + 2 := by linarith
        have hh := mul_le_mul_of_nonneg_left hn1' hCR
        have hcoeff : 2 * R + C + 2 ≤ B - R := by dsimp [B] <;> nlinarith
        have hh' := mul_le_mul_of_nonneg_right hcoeff (Nat.cast_nonneg (α := ℝ) n)
        nlinarith
  obtain ⟨m, z, hz0, hzend, hlen, hheight', hball, hsteps⟩ :=
    exists_negative_word_prefix_chains height source target hsource hwords
  refine ⟨B, hB, m, z, hz0, hzend, ?_, hheight', ?_, hsteps⟩
  · filter_upwards [hlen] with n hn
    exact hn.trans (mul_le_mul_of_nonneg_right (by linarith) (by positivity))
  · filter_upwards [hball] with n hn
    simpa only [add_sub_cancel] using hn

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_NilpotentNegativePaths
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.chartExponentialFlow_zero _root_.OAI.PolycyclicRecognition.derivationSemidirectHom_apply _root_.OAI.PolycyclicRecognition.exponentialHomOfDynkin_apply_exp _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Negative-height paths in the nilpotent Cartan factor -/

noncomputable section
namespace PolycyclicRecognition

open Module LieModule Filter Set
open scoped Manifold Topology

variable {E D G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace D] [ChartedSpace E D] [Group D]
  [LieGroup (𝓘(ℝ, E)) ⊤ D] [T2Space D]
  [Group G] [MetricSpace G] [IsIsometricSMul G G]

/-- A fixed Cartan displacement can be moved along a negative ray by
paths in a linear ball. Their coarse speeds grow only polynomially. -/
theorem exists_nilpotent_negative_paths
    (κ : D →* G) (hκ : Continuous κ)
    (dynkin : NilpotentDynkinExpansionInput E D)
    (Exp : GroupLieAlgebra (𝓘(ℝ, E)) D → D) (hExp : IsGroupExponential Exp)
    (chart : GroupLieAlgebra (𝓘(ℝ, E)) D ≃ₜ D) (hchart : ∀ x, chart x = Exp x)
    {c : ℕ} (hc : lowerCentralSeries ℝ (GroupLieAlgebra (𝓘(ℝ, E)) D)
      (GroupLieAlgebra (𝓘(ℝ, E)) D) c = ⊥)
    {m : ℕ} (b : Basis (Fin m) ℝ (GroupLieAlgebra (𝓘(ℝ, E)) D))
    (η : G →* Multiplicative ℝ)
    (ℓ : GroupLieAlgebra (𝓘(ℝ, E)) D →ₗ[ℝ] ℝ)
    (hη : ∀ w, (η (κ (Exp w))).toAdd = ℓ w)
    (u v : GroupLieAlgebra (𝓘(ℝ, E)) D) (hv : ℓ v < 0) :
    ∃ C R : ℝ, 0 ≤ C ∧ 0 ≤ R ∧
      (∀ n : ℕ, dist 1 (κ (Exp ((n : ℝ) • v))) ≤ R * n) ∧
      ∀ᶠ n : ℕ in atTop,
        ∃ γ : Path (κ (Exp ((n : ℝ) • v))) (κ (Exp u) * κ (Exp ((n : ℝ) • v))),
          PathMetricBound γ (C * (1 + n) ^ c) C ∧
          (∀ t, (η (γ t)).toAdd ≤ (ℓ v / 2) * n) ∧
          ∀ t, dist 1 (γ t) ≤ R * n := by
  let _ : IsTopologicalGroup D := topologicalGroup_of_lieGroup (𝓘(ℝ, E)) ⊤
  have hExpCont : Continuous Exp := by
    rw [← show chart = Exp from funext hchart]
    exact chart.continuous
  let Φ : (Fin m → ℝ) → G := fun w => κ (Exp (b.equivFun.symm w))
  obtain ⟨B, hB, hrad⟩ := continuous_radial_exponential_metric_bound Φ
    (hκ.comp (hExpCont.comp b.equivFun.symm.toContinuousLinearEquiv.continuous))
    (by simp [Φ, hExp.map_zero])
    (fun w s t => by simp only [Φ, map_smul, hExp.map_add_smul, map_mul])
  have hbound (w : GroupLieAlgebra (𝓘(ℝ, E)) D) :
      dist 1 (κ (Exp w)) ≤ B * (1 + ‖b.equivFun w‖) := by
    simpa only [Φ, b.equivFun.symm_apply_apply] using hrad (b.equivFun w)
  obtain ⟨C, hC, hmetric⟩ := exists_nilpotent_right_translate_coarse_metric
    κ hκ dynkin Exp hExp chart hchart hc b u v
  let R := B * (2 + ‖b.equivFun u‖ + ‖b.equivFun v‖)
  have hR : 0 ≤ R := by dsimp [R] <;> positivity
  have hbase (n : ℕ) : dist 1 (κ (Exp ((n : ℝ) • v))) ≤ R * n := by
    have hh := one_parameter_nat_dist_le (fun t : ℝ => κ (Exp (t • v)))
      (by simp [hExp.map_zero]) (fun s t => by rw [hExp.map_add_smul, map_mul]) n
    have h1 : dist 1 (κ (Exp v)) ≤ R := by
      have hb := hbound v
      change dist 1 (κ (Exp v)) ≤ B * (2 + ‖b.equivFun u‖ + ‖b.equivFun v‖)
      nlinarith [norm_nonneg (b.equivFun u)]
    have hh' : dist 1 (κ (Exp ((n : ℝ) • v))) ≤ (n : ℝ) * dist 1 (κ (Exp v)) := by
      simpa only [one_smul] using hh
    exact (hh'.trans (mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg (α := ℝ) n))).trans_eq (mul_comm _ _)
  refine ⟨C, R, hC, hR, hbase, ?_⟩
  have herr : ∀ᶠ n : ℕ in atTop, |ℓ u| ≤ (-ℓ v / 2) * n := by
    have ht := (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop).const_mul_atTop
      (show 0 < -ℓ v / 2 by linarith)
    exact ht.eventually (eventually_ge_atTop _)
  filter_upwards [herr, eventually_ge_atTop (1 : ℕ)] with n he hn1
  let γ : Path (κ (Exp ((n : ℝ) • v))) (κ (Exp u) * κ (Exp ((n : ℝ) • v))) := {
    toFun := fun t => κ (Exp ((t : ℝ) • u) * Exp ((n : ℝ) • v))
    continuous_toFun := hκ.comp ((hExpCont.comp (continuous_subtype_val.smul continuous_const)).mul continuous_const)
    source' := by simp [hExp.map_zero]
    target' := by simp }
  refine ⟨γ, ?_, ?_, ?_⟩
  · intro s t
    change dist (κ (Exp ((s : ℝ) • u) * Exp ((n : ℝ) • v)))
      (κ (Exp ((t : ℝ) • u) * Exp ((n : ℝ) • v))) ≤ _
    have hs : |(t : ℝ) - s| ≤ 1 := abs_le.mpr ⟨by linarith [s.property.2, t.property.1],
      by linarith [s.property.1, t.property.2]⟩
    simpa only [abs_sub_comm] using hmetric n s t hs
  · intro t
    change (η (κ (Exp ((t : ℝ) • u) * Exp ((n : ℝ) • v)))).toAdd ≤ _
    rw [map_mul, map_mul, toAdd_mul, hη, hη, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
    have htu : (t : ℝ) * ℓ u ≤ |ℓ u| := by
      calc
        _ ≤ |(t : ℝ) * ℓ u| := le_abs_self _
        _ = (t : ℝ) * |ℓ u| := by rw [abs_mul, abs_of_nonneg t.property.1]
        _ ≤ |ℓ u| := by nlinarith [t.property.2, abs_nonneg (ℓ u)]
    nlinarith
  · intro t
    change dist 1 (κ (Exp ((t : ℝ) • u) * Exp ((n : ℝ) • v))) ≤ _
    rw [map_mul]
    have htri := dist_triangle (1 : G) (κ (Exp ((t : ℝ) • u)))
      (κ (Exp ((t : ℝ) • u)) * κ (Exp ((n : ℝ) • v)))
    have hd : dist (κ (Exp ((t : ℝ) • u)))
        (κ (Exp ((t : ℝ) • u)) * κ (Exp ((n : ℝ) • v))) =
        dist 1 (κ (Exp ((n : ℝ) • v))) := by
      simpa only [mul_one] using dist_mul_left (κ (Exp ((t : ℝ) • u))) (1 : G) _
    rw [hd] at htri
    have hu := hbound ((t : ℝ) • u)
    have hnv := hbound ((n : ℝ) • v)
    rw [map_smul, norm_smul, Real.norm_eq_abs, abs_of_nonneg t.property.1] at hu
    rw [map_smul, norm_smul, Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg n)] at hnv
    have htu : (t : ℝ) * ‖b.equivFun u‖ ≤ ‖b.equivFun u‖ := mul_le_of_le_one_left (norm_nonneg _) t.property.2
    have hn1' : (1 : ℝ) ≤ n := by exact_mod_cast hn1
    have hbu := mul_le_mul_of_nonneg_left htu hB
    have hbu' := mul_le_mul_of_nonneg_left hn1' (mul_nonneg hB (norm_nonneg (b.equivFun u)))
    have hb' := mul_le_mul_of_nonneg_left hn1' hB
    change _ ≤ B * (2 + ‖b.equivFun u‖ + ‖b.equivFun v‖) * n
    nlinarith

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_OrbitFiberAsymptotics
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Combining the two stabilizer invariances for boundary descent -/

noncomputable section
namespace PolycyclicRecognition

open Filter
open scoped Topology

section RelativeLimits

variable {Q : Type} [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q]

/-- Asymptotic equality in a topological group is transitive. -/
theorem relative_limit_trans {f g h : ℕ → Q}
    (hfg : Tendsto (fun n => (f n)⁻¹ * g n) atTop (𝓝 1))
    (hgh : Tendsto (fun n => (g n)⁻¹ * h n) atTop (𝓝 1)) :
    Tendsto (fun n => (f n)⁻¹ * h n) atTop (𝓝 1) := by
  simpa only [mul_assoc, mul_inv_cancel_left, one_mul] using hfg.mul hgh

end RelativeLimits

/-- The two actual stabilizer invariances imply asymptotic equality on
every fiber of the orbit map. No boundary limit is assumed. -/
theorem orbit_fiber_asymptotic_of_stabilizer
    {G S Q I D : Type} [Group G] [One S]
    [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q]
    (act : G →* Equiv.Perm S) (ι : I → G) (κ : D → G)
    (hstab : ∀ g, act g 1 = 1 ↔ ∃ i d, ι i * κ d = g)
    (f : G → ℕ → Q)
    (hI : ∀ g i, Tendsto (fun n => (f g n)⁻¹ * f (g * ι i) n) atTop (𝓝 1))
    (hD : ∀ g d, Tendsto (fun n => (f g n)⁻¹ * f (g * κ d) n) atTop (𝓝 1)) :
    ∀ g g', act g 1 = act g' 1 →
      Tendsto (fun n => (f g n)⁻¹ * f g' n) atTop (𝓝 1) := by
  intro g g' heq
  have hs : act (g⁻¹ * g') 1 = 1 := by
    rw [map_mul, map_inv, Equiv.Perm.mul_apply, ← heq]
    exact (act g).symm_apply_apply 1
  obtain ⟨i, d, hid⟩ := (hstab _).mp hs
  have hgg' : (g * ι i) * κ d = g' := by
    rw [mul_assoc, hid, mul_inv_cancel_left]
  have ht := relative_limit_trans (hI g i) (hD (g * ι i) d)
  simpa only [hgg'] using ht

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_TranslatedNegativeChains
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Negative chains based at arbitrary group elements -/

noncomputable section
namespace PolycyclicRecognition

open Filter
open scoped Topology

variable {G : Type} [Group G] [MetricSpace G] [IsIsometricSMul G G]

/-- A fixed left translate preserves a negative linear height margin,
linear radius, and all unit-step bounds. -/
theorem left_translate_negative_chains
    (η : G →* Multiplicative ℝ) (m : ℕ → ℕ) (z : ℕ → ℕ → G)
    {R gap : ℝ} (hR : 0 ≤ R) (hgap : 0 < gap)
    (hnegative : ∀ᶠ n : ℕ in atTop, ∀ i ≤ m n, (η (z n i)).toAdd ≤ -gap * n)
    (hball : ∀ᶠ n : ℕ in atTop, ∀ i ≤ m n, dist 1 (z n i) ≤ R * n)
    (hstep : ∀ᶠ n : ℕ in atTop, ∀ i < m n, dist (z n i) (z n (i + 1)) ≤ 1)
    (g : G) :
    ∃ B : ℝ, 0 ≤ B ∧
      (∀ᶠ n : ℕ in atTop, ∀ i ≤ m n, (η (g * z n i)).toAdd ≤ -(gap / 2) * n) ∧
      (∀ᶠ n : ℕ in atTop, ∀ i ≤ m n, dist 1 (g * z n i) ≤ B * n) ∧
      ∀ᶠ n : ℕ in atTop, ∀ i < m n, dist (g * z n i) (g * z n (i + 1)) ≤ 1 := by
  refine ⟨R + dist 1 g, add_nonneg hR dist_nonneg, ?_, ?_, ?_⟩
  · have herr : ∀ᶠ n : ℕ in atTop, (η g).toAdd ≤ (gap / 2) * n := by
      have ht := (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop).const_mul_atTop
        (show 0 < gap / 2 by linarith)
      exact ht.eventually (eventually_ge_atTop _)
    filter_upwards [hnegative, herr] with n hn he
    intro i hi
    rw [map_mul, toAdd_mul]
    have hh := hn i hi
    nlinarith
  · filter_upwards [hball, eventually_ge_atTop (1 : ℕ)] with n hn hn1
    intro i hi
    have ht := dist_triangle (1 : G) g (g * z n i)
    have hd : dist g (g * z n i) = dist 1 (z n i) := by
      simpa only [mul_one] using dist_mul_left g (1 : G) (z n i)
    rw [hd] at ht
    have hn1' : (1 : ℝ) ≤ n := by exact_mod_cast hn1
    have hh := mul_le_mul_of_nonneg_left hn1' (show 0 ≤ dist 1 g from dist_nonneg)
    have hb := hn i hi
    nlinarith
  · filter_upwards [hstep] with n hn
    intro i hi
    rw [dist_mul_left]
    exact hn i hi

/-- Apply a negative-chain contraction criterion after a fixed left
translation, retaining the actual endpoint sequences. -/
theorem translated_negative_chain_endpoint_limit
    {Q : Type} [Group Q] [TopologicalSpace Q]
    (η : G →* Multiplicative ℝ) (observe : G → Q)
    (m : ℕ → ℕ) (z : ℕ → ℕ → G) {R gap : ℝ} (hR : 0 ≤ R) (hgap : 0 < gap)
    (hnegative : ∀ᶠ n : ℕ in atTop, ∀ i ≤ m n, (η (z n i)).toAdd ≤ -gap * n)
    (hball : ∀ᶠ n : ℕ in atTop, ∀ i ≤ m n, dist 1 (z n i) ≤ R * n)
    (hstep : ∀ᶠ n : ℕ in atTop, ∀ i < m n, dist (z n i) (z n (i + 1)) ≤ 1)
    (base target : ℕ → G) (hbase : ∀ n, z n 0 = base n)
    (htarget : ∀ᶠ n in atTop, z n (m n) = target n)
    (g : G)
    (criterion : ∀ (z' : ℕ → ℕ → G) (R' gap' : ℝ), 0 ≤ R' → 0 < gap' →
      (∀ᶠ n : ℕ in atTop, ∀ i ≤ m n, (η (z' n i)).toAdd ≤ -gap' * n) →
      (∀ᶠ n : ℕ in atTop, ∀ i ≤ m n, dist 1 (z' n i) ≤ R' * n) →
      (∀ᶠ n : ℕ in atTop, ∀ i < m n, dist (z' n i) (z' n (i + 1)) ≤ 1) →
      Tendsto (fun n => (observe (z' n 0))⁻¹ * observe (z' n (m n))) atTop (𝓝 1)) :
    Tendsto (fun n => (observe (g * base n))⁻¹ * observe (g * target n)) atTop (𝓝 1) := by
  obtain ⟨B, hB, hn, hb, hs⟩ := left_translate_negative_chains η m z hR hgap
    hnegative hball hstep g
  have ht := criterion (fun n i => g * z n i) B (gap / 2) hB
    (div_pos hgap (by norm_num)) hn hb hs
  apply ht.congr'
  filter_upwards [htarget] with n he
  exact congrArg₂ (fun x y => (observe x)⁻¹ * observe y)
    (congrArg (g * ·) (hbase n)) (congrArg (g * ·) he)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_BoundaryShadowDescent
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instNonemptyBases _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_nonempty _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Descending centered ray limits to boundary maps with compact shadows -/

noncomputable section
namespace PolycyclicRecognition

open Filter Set
open scoped Topology

/-- Continuous fixed-element actions transport normalized ray limits.
Asymptotic equality on the actual source fibers then gives a well-defined
boundary map and the same common compact shadow. -/
theorem boundary_shadow_of_centered_limits
    {G S Q : Type} [Group G] [Group Q] [TopologicalSpace Q]
    [T2Space Q] [IsTopologicalGroup Q]
    (act : G →* Equiv.Perm Q) (hact : ∀ g, Continuous (act g))
    (q : G → S) (hq : Function.Surjective q) (F : G → G) (ray : ℕ → G)
    (K : Set Q) (k : G → Q) (hkK : ∀ x, k x ∈ K)
    (hk : ∀ x, Tendsto (fun n => act ((F x)⁻¹ * F (x * ray n)) 1)
      atTop (𝓝 (k x)))
    (hfiber : ∀ x y, q x = q y →
      Tendsto (fun n => (act (F (x * ray n)) 1)⁻¹ * act (F (y * ray n)) 1)
        atTop (𝓝 (1 : Q))) :
    ∃ B : S → Q, ∀ x,
      Tendsto (fun n => act (F (x * ray n)) 1) atTop (𝓝 (B (q x))) ∧
      ∃ z ∈ K, B (q x) = act (F x) z := by
  classical
  let b : G → Q := fun x => act (F x) (k x)
  have hb (x : G) : Tendsto (fun n => act (F (x * ray n)) 1) atTop (𝓝 (b x)) := by
    have ht := ((hact (F x)).tendsto (k x)).comp (hk x)
    have he (n : ℕ) : act (F x) (act ((F x)⁻¹ * F (x * ray n)) 1) =
        act (F (x * ray n)) 1 := by
      rw [← Equiv.Perm.mul_apply, ← map_mul, mul_inv_cancel_left]
    simpa only [Function.comp_def, he] using ht
  have heq (x y : G) (hxy : q x = q y) : b x = b y := by
    have he := tendsto_nhds_unique ((hb x).inv.mul (hb y)) (hfiber x y hxy)
    exact inv_mul_eq_one.mp he
  choose s hs using hq
  let B : S → Q := fun z => b (s z)
  have hdesc (x : G) : B (q x) = b x := heq _ _ (hs _)
  refine ⟨B, ?_⟩
  intro x
  refine ⟨?_, k x, hkK x, hdesc x⟩
  simpa only [hdesc] using hb x

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_RayTangentContraction
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instDecidableEqConeMixedWords _root_.OAI.PolycyclicRecognition.CartanWordModel.instFintypeConeMixedWords _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Ray contraction in the actual tangent coordinate basis -/
noncomputable section
namespace PolycyclicRecognition

open Module LieAlgebra LieModule Set
open scoped Manifold

namespace CartanWordModel
variable {L : Type} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {H : LieSubalgebra ℝ L} [H.IsCartanSubalgebra] (M : CartanWordModel H)
  {a : ℕ} (T : TriangularAdjoint L a)

theorem coneAdjoint_projection
    (C : Set (H →ₗ[ℝ] ℝ)) (hadd : ∀ x ∈ C, ∀ y ∈ C, x + y ∈ C)
    (h : H) (x : cartanRootIdeal H) :
    M.coneAdjointAutomorphism T C hadd h (M.coneProjection C x) =
      M.coneProjection C (cartanIdealAdjointAutomorphism T H h x) := rfl

end CartanWordModel
end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanRayFactorContraction
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instDecidableEqConeMixedWords _root_.OAI.PolycyclicRecognition.CartanWordModel.instFintypeConeMixedWords _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Compact increments and contraction for the actual Cartan factors -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule Set
open scoped Manifold

variable {EG G : Type} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {ExpG : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H ExpG)

variable (α₀ : H →ₗ[ℝ] ℝ)
  (Q : NilpotentLieModel ((cartanRootIdeal H) ⧸ M.coneWordIdeal (positiveWeightRay α₀)))
  (ExpQ : GroupLieAlgebra (𝓘(ℝ, Q.modelSpace)) Q.carrier → Q.carrier)
  (hbijQ : Function.Bijective ExpQ)
  (chartQ : GroupLieAlgebra (𝓘(ℝ, Q.modelSpace)) Q.carrier ≃ₜ Q.carrier)
  (hchartQ : ∀ v, chartQ v = ExpQ v)
  (hbijN : Function.Bijective F.ExpN) (hbijD : Function.Bijective F.ExpD)
  (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
  (π : F.N.carrier →* Q.carrier)
  (hπ : ∀ x : cartanRootIdeal H,
    π (F.ExpN (F.N.equiv x)) = ExpQ (Q.equiv (M.coneProjection (positiveWeightRay α₀) x)))
  (α : F.D.carrier →* MulAut Q.carrier)
  (hα : ∀ d n, α d (π n) = π (F.action d n))
  (hφ : ∀ d, F.action d = M.adjointGroupAutomorphism T F.N.equiv F.ExpN F.isExpN
    hbijN dynkinN (cartanLog H F.D.equiv F.ExpD hbijD d))

set_option maxHeartbeats 1000000 in
include hπ hα hφ in
/-- The quotient action of each actual Cartan factor is the exponential
of its induced Lie action, with the actual Cartan logarithm. -/
theorem factor_quotient_action_eq_exponential (d : F.D.carrier) (q : Q.carrier) :
    α d q = exponentialConjugate Q.equiv ExpQ hbijQ
      (M.coneAdjointAutomorphism T (positiveWeightRay α₀) (positiveWeightRay_add α₀)
        (cartanLog H F.D.equiv F.ExpD hbijD d)) q := by
  obtain ⟨v, hv⟩ := hbijQ.surjective q
  obtain ⟨w, hw⟩ := Q.equiv.surjective v
  obtain ⟨x, hx⟩ := M.coneProjection_surjective (positiveWeightRay α₀) w
  have hq : ExpQ (Q.equiv (M.coneProjection (positiveWeightRay α₀) x)) = q :=
    (congrArg ExpQ ((congrArg Q.equiv hx).trans hw)).trans hv
  rw [← hq]
  let h := cartanLog H F.D.equiv F.ExpD hbijD d
  have he : F.action d (F.ExpN (F.N.equiv x)) =
      F.ExpN (F.N.equiv (cartanIdealAdjointAutomorphism T H h x)) := by
    exact (congrArg (fun a : MulAut F.N.carrier => a (F.ExpN (F.N.equiv x)))
      (hφ d)).trans (integrateNilpotentLieEquiv_apply_exp F.N.equiv F.ExpN hbijN dynkinN
        F.isExpN M.bound_zero (cartanIdealAdjointAutomorphism T H h) x)
  calc
    α d (ExpQ (Q.equiv (M.coneProjection (positiveWeightRay α₀) x))) =
        α d (π (F.ExpN (F.N.equiv x))) := congrArg (α d) (hπ x).symm
    _ = π (F.action d (F.ExpN (F.N.equiv x))) := hα d _
    _ = π (F.ExpN (F.N.equiv (cartanIdealAdjointAutomorphism T H h x))) := congrArg π he
    _ = ExpQ (Q.equiv (M.coneProjection (positiveWeightRay α₀)
        (cartanIdealAdjointAutomorphism T H h x))) := hπ _
    _ = _ := by
      have hp := M.coneAdjoint_projection T (positiveWeightRay α₀)
        (positiveWeightRay_add α₀) h x
      exact (congrArg (fun v => ExpQ (Q.equiv v)) hp).symm.trans
        (exponentialConjugate_apply_exp Q.equiv ExpQ hbijQ
          (M.coneAdjointAutomorphism T (positiveWeightRay α₀)
            (positiveWeightRay_add α₀) h) (M.coneProjection (positiveWeightRay α₀) x)).symm

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanRayFactorPaths
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.CartanFactorModel.heightRay_zero _root_.OAI.PolycyclicRecognition.CartanFactorModel.realScaleProfile_apply _root_.OAI.PolycyclicRecognition.CartanFactorModel.sampledProbeProfile_apply _root_.OAI.PolycyclicRecognition.cartanWeightDerivation_apply_root _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.modelNilradicalLinearAction_apply _root_.OAI.PolycyclicRecognition.modelNilradicalRotation_apply _root_.OAI.PolycyclicRecognition.modelNilradicalRotation_mul _root_.OAI.PolycyclicRecognition.modelNilradicalRotation_one _root_.OAI.PolycyclicRecognition.nilshadowWeightDerivation_symm _root_.OAI.PolycyclicRecognition.nilshadowWeightOperator_symm _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual negative chains between Cartan-factor representatives -/

noncomputable section
namespace PolycyclicRecognition.CartanFactorModel

open Module LieModule Filter Set
open scoped Manifold Topology

variable {EG G W : Type} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [IsIsometricSMul G G]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  {ExpG : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H ExpG)

set_option maxHeartbeats 1000000 in
/-- Every fixed Cartan-factor displacement admits actual unit-step chains
along the chosen negative ray, with polynomial length and linear radius. -/
theorem exists_negative_height_cartan_fiber_chains
    (eW : HeightSpace T.character ≃ₗ[ℝ] W)
    (height : G →* Multiplicative W)
    (hheight : ∀ x, (height (ExpG x)).toAdd = eW (heightProjection T.character x))
    (chartD : GroupLieAlgebra (𝓘(ℝ, F.D.modelSpace)) F.D.carrier ≃ₜ F.D.carrier)
    (hchartD : ∀ x, chartD x = F.ExpD x)
    (dynkinD : NilpotentDynkinExpansionInput F.D.modelSpace F.D.carrier)
    {Kheight : ℝ} (hKheight : 0 ≤ Kheight)
    (hLip : ∀ x y, ‖(height x).toAdd - (height y).toAdd‖ ≤ Kheight * dist x y)
    (hpath : ∀ g : G, ∃ γ : ℝ → G, γ 0 = 1 ∧ γ 1 = g ∧
      ∀ t ∈ Icc (0 : ℝ) 1, ∀ u ∈ Icc (0 : ℝ) 1,
        dist (γ t) (γ u) ≤ dist 1 g * |t - u|)
    (β : W →L[ℝ] ℝ) (v₀ : W) (hv₀ : β v₀ < 0) (d : F.D.carrier) :
    let ray := fun n : ℕ => ExpG ((n : ℝ) •
      (cartanHeightSection T H (eW.symm v₀) : GroupLieAlgebra (𝓘(ℝ, EG)) G))
    ∃ (q : ℕ) (R : ℝ), 0 ≤ R ∧ ∃ (m : ℕ → ℕ) (z : ℕ → ℕ → G),
      (∀ n, z n 0 = ray n) ∧
      (∀ᶠ n in atTop, z n (m n) = F.inclusionD d * ray n) ∧
      (∀ᶠ n in atTop, (m n : ℝ) ≤ R * (1 + n) ^ q) ∧
      (∀ᶠ n in atTop, ∀ i ≤ m n, β ((height (z n i)).toAdd) ≤ (β v₀ / 4) * n) ∧
      (∀ᶠ n in atTop, ∀ i ≤ m n, dist 1 (z n i) ≤ R * n) ∧
      ∀ᶠ n in atTop, ∀ i < m n, dist (z n i) (z n (i + 1)) ≤ 1 := by
  let _ : IsTopologicalGroup G := topologicalGroup_of_lieGroup (𝓘(ℝ, EG)) ⊤
  dsimp only
  let h₀ := cartanHeightSection T H (eW.symm v₀)
  let v := F.D.equiv h₀
  let u := chartD.symm d
  let η : G →* Multiplicative ℝ := β.toLinearMap.toAddMonoidHom.toMultiplicative.comp height
  let ℓ := β.toLinearMap.comp (eW.toLinearMap.comp
    ((heightProjection T.character).comp (H.subtype.comp F.D.equiv.symm.toLinearMap)))
  have hη (w) : (η (F.inclusionD (F.ExpD w))).toAdd = ℓ w := by
    change β ((height (F.inclusionD (F.ExpD w))).toAdd) = _
    have he := F.compatibleD (F.D.equiv.symm w)
    rw [F.D.equiv.apply_symm_apply] at he
    rw [he, hheight]
    rfl
  have hℓv : ℓ v = β v₀ := by simp [ℓ, v, h₀]
  have hnil := F.D.tangent_nilpotent (inferInstance : LieRing.IsNilpotent H)
  obtain ⟨q, hq⟩ := (LieModule.isNilpotent_iff ℝ _ _).mp hnil
  obtain ⟨C, R, hC, hR, hsource, hpaths⟩ := exists_nilpotent_negative_paths
    F.inclusionD F.closedD.continuous dynkinD F.ExpD F.isExpD chartD hchartD hq
    (finBasis ℝ _) η ℓ hη u v (by rwa [hℓv])
  have hscalar (x y : G) : |(η x).toAdd - (η y).toAdd| ≤ (‖β‖ * Kheight) * dist x y := by
    change |β ((height x).toAdd) - β ((height y).toAdd)| ≤ _
    calc
      _ = ‖β ((height x).toAdd - (height y).toAdd)‖ := by rw [map_sub, Real.norm_eq_abs]
      _ ≤ ‖β‖ * ‖(height x).toAdd - (height y).toAdd‖ := β.le_opNorm _
      _ ≤ ‖β‖ * (Kheight * dist x y) := mul_le_mul_of_nonneg_left (hLip x y) (norm_nonneg _)
      _ = _ := by ring
  obtain ⟨B, hB, m, z, hz0, hzend, hcount, hnegative, hball, hsteps⟩ :=
    polynomial_negative_path_chains hpath (fun g => (η g).toAdd)
      (mul_nonneg (norm_nonneg _) hKheight) hC hR
      (show 0 < -ℓ v / 2 by rw [hℓv]; linarith) hscalar
      (fun n => F.inclusionD (F.ExpD ((n : ℝ) • v)))
      (fun n => F.inclusionD (F.ExpD u) * F.inclusionD (F.ExpD ((n : ℝ) • v)))
      hsource (hpaths.mono fun n hn => by
        obtain ⟨γ, hm, hh, hr⟩ := hn
        exact ⟨γ, hm, fun t => by have ht := hh t; linarith, hr⟩)
  have hbase (n : ℕ) : F.inclusionD (F.ExpD ((n : ℝ) • v)) =
      ExpG ((n : ℝ) • (h₀ : GroupLieAlgebra (𝓘(ℝ, EG)) G)) := by
    change F.inclusionD (F.ExpD ((n : ℝ) • F.D.equiv h₀)) = _
    rw [← map_smul, F.compatibleD]
    rfl
  have hend : F.ExpD u = d := by
    change F.ExpD (chartD.symm d) = d
    rw [← hchartD, chartD.apply_symm_apply]
  refine ⟨q, B, hB, m, z, fun n => (hz0 n).trans (hbase n), ?_, hcount, ?_, hball, hsteps⟩
  · filter_upwards [hzend] with n hn
    exact hn.trans (congrArg₂ (fun x y => F.inclusionD x * y) hend (hbase n))
  · filter_upwards [hnegative] with n hn
    intro i hi
    have hh := hn i hi
    change β ((height (z n i)).toAdd) ≤ _ at hh
    rw [hℓv] at hh
    linarith

end PolycyclicRecognition.CartanFactorModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanFactorAsymptotics
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instDecidableEqConeMixedWords _root_.OAI.PolycyclicRecognition.CartanWordModel.instFintypeConeMixedWords _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.CartanFactorModel.heightRay_zero _root_.OAI.PolycyclicRecognition.CartanFactorModel.realScaleProfile_apply _root_.OAI.PolycyclicRecognition.CartanFactorModel.sampledProbeProfile_apply _root_.OAI.PolycyclicRecognition.cartanWeightDerivation_apply_root _root_.OAI.PolycyclicRecognition.chartExponentialFlow_zero _root_.OAI.PolycyclicRecognition.derivationSemidirectHom_apply _root_.OAI.PolycyclicRecognition.exponentialHomOfDynkin_apply_exp _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.modelNilradicalLinearAction_apply _root_.OAI.PolycyclicRecognition.modelNilradicalRotation_apply _root_.OAI.PolycyclicRecognition.modelNilradicalRotation_mul _root_.OAI.PolycyclicRecognition.modelNilradicalRotation_one _root_.OAI.PolycyclicRecognition.nilshadowWeightDerivation_symm _root_.OAI.PolycyclicRecognition.nilshadowWeightOperator_symm _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Cartan-factor asymptotics in the constructed ray quotient -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule Filter Set
open scoped Manifold Topology

variable {EG G W : Type} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [IsIsometricSMul G G] [ProperSpace G]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {ExpG : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H ExpG)
  (hunimod : ∀ x : GroupLieAlgebra (𝓘(ℝ, EG)) G, LinearMap.trace ℝ _ (ad ℝ _ x) = 0)
  (eW : HeightSpace T.character ≃ₗ[ℝ] W) (height : G →* Multiplicative W)
  (hheight : ∀ x, (height (ExpG x)).toAdd = eW (heightProjection T.character x))
  (chartN : GroupLieAlgebra (𝓘(ℝ, F.N.modelSpace)) F.N.carrier ≃ₜ F.N.carrier)
  (hchartN : ∀ x, chartN x = F.ExpN x)
  (chartD : GroupLieAlgebra (𝓘(ℝ, F.D.modelSpace)) F.D.carrier ≃ₜ F.D.carrier)
  (hchartD : ∀ x, chartD x = F.ExpD x)
  (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
  (dynkinD : NilpotentDynkinExpansionInput F.D.modelSpace F.D.carrier)

set_option maxHeartbeats 1000000 in
include hunimod hheight dynkinD in
/-- A fixed source Cartan-factor displacement has asymptotically equal
images in the target ray quotient along a negative ray. The connecting
polynomial chains are constructed from the finite BCH law. -/
theorem cartan_fiber_quotient_difference_tendsto_one
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (γ₀ : M.Bases)
    (hφ : ∀ d, F.action d = M.adjointGroupAutomorphism T F.N.equiv F.ExpN F.isExpN
      (by rw [← show chartN = F.ExpN from funext hchartN]; exact chartN.bijective) dynkinN
      (cartanLog H F.D.equiv F.ExpD
        (by rw [← show chartD = F.ExpD from funext hchartD]; exact chartD.bijective) d))
    (hpath : ∀ g : G, ∃ γ : ℝ → G, γ 0 = 1 ∧ γ 1 = g ∧
      ∀ t ∈ Icc (0 : ℝ) 1, ∀ u ∈ Icc (0 : ℝ) 1,
        dist (γ t) (γ u) ≤ dist 1 g * |t - u|)
    {Kheight : ℝ} (hKheight : 0 ≤ Kheight)
    (hLip : ∀ x y, ‖(height x).toAdd - (height y).toAdd‖ ≤ Kheight * dist x y)
    (αW : W →L[ℝ] ℝ)
    (Q : NilpotentLieModel ((cartanRootIdeal H) ⧸ M.coneWordIdeal
      (positiveWeightRay (αW.toLinearMap.comp
        (eW.toLinearMap.comp ((heightProjection T.character).comp H.subtype))))))
    (ExpQ : GroupLieAlgebra (𝓘(ℝ, Q.modelSpace)) Q.carrier → Q.carrier)
    (hExpQ : IsGroupExponential ExpQ)
    (chartQ : GroupLieAlgebra (𝓘(ℝ, Q.modelSpace)) Q.carrier ≃ₜ Q.carrier)
    (hchartQ : ∀ v, chartQ v = ExpQ v)
    (dynkinQ : NilpotentDynkinExpansionInput Q.modelSpace Q.carrier)
    (π : F.N.carrier →* Q.carrier) (hπcont : Continuous π)
    (hπ : ∀ x : cartanRootIdeal H, π (F.ExpN (F.N.equiv x)) =
      ExpQ (Q.equiv (M.coneProjection (positiveWeightRay (αW.toLinearMap.comp
        (eW.toLinearMap.comp ((heightProjection T.character).comp H.subtype)))) x)))
    (α : F.D.carrier →* MulAut Q.carrier) (act : G →* Equiv.Perm Q.carrier)
    (hα : ∀ d n, α d (π n) = π (F.action d n))
    (hact : ∀ u d q, act (F.inclusionN u * F.inclusionD d) q = π u * α d q)
    (A : W →L[ℝ] W) (f : G → G) {L error : ℝ} (hL : 0 ≤ L)
    (hf : ∀ x y, dist (f x) (f y) ≤ L * dist x y + error)
    (hsub : ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, 0 ≤ B ∧ ∀ g,
      ‖(height (f g)).toAdd - A ((height g).toAdd)‖ ≤ ε * dist 1 g + B)
    (v₀ : W) (hv₀ : αW (A v₀) < 0)
    (d₀ : F.D.carrier) (g₀ : G) :
    let d := fun n : ℕ => ExpG ((n : ℝ) •
      (cartanHeightSection T H (eW.symm v₀) : GroupLieAlgebra (𝓘(ℝ, EG)) G))
    Tendsto (fun n => (act (f (g₀ * d n)) 1)⁻¹ *
      act (f (g₀ * (F.inclusionD d₀ * d n))) 1)
      atTop (𝓝 (1 : Q.carrier)) := by
  let β := αW.comp A
  obtain ⟨q, R, hR, m, z, hz0, hzend, hcount, hnegative, hball, hsteps⟩ :=
    F.exists_negative_height_cartan_fiber_chains T eW height hheight chartD hchartD
      dynkinD hKheight hLip hpath β v₀ hv₀ d₀
  have hscalar := scalar_sublinear_error (fun g : G => dist 1 g) (fun _ => dist_nonneg)
    (fun g => (height (f g)).toAdd) (fun g => A ((height g).toAdd)) αW hsub
  have hneg : ∀ᶠ n : ℕ in atTop, ∀ i ≤ m n,
      β ((height (z n i)).toAdd) ≤ -(-β v₀ / 4) * n := by
    filter_upwards [hnegative] with n hn
    intro i hi
    have hh := hn i hi
    linarith
  have hgap : 0 < -β v₀ / 4 := div_pos (neg_pos.mpr hv₀) (by norm_num)
  let η : G →* Multiplicative ℝ := β.toLinearMap.toAddMonoidHom.toMultiplicative.comp height
  apply translated_negative_chain_endpoint_limit η (fun g => act (f g) 1)
    m z hR hgap hneg hball hsteps _ _ hz0 hzend g₀
  intro z' R' gap' hR' hgap' hn hb hs
  exact M.negative_chain_quotient_difference_tendsto_one
    T F hunimod eW height hheight chartN hchartN chartD hchartD dynkinN dynkinD
    b₀ γ₀ hφ hpath hKheight hLip αW Q ExpQ hExpQ chartQ hchartQ dynkinQ
    π hπcont hπ α act hα hact (fun g => β ((height g).toAdd)) f hL hf hscalar m z'
    hR' hgap' q hcount hb hn hs

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanBoundaryOrbitFibers
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Asymptotic equality on fibers of the actual boundary orbit -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule Filter Set
open scoped Manifold Topology

variable {EG G W : Type} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [IsIsometricSMul G G] [ProperSpace G]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {ExpG : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H ExpG)
  (hunimod : ∀ x : GroupLieAlgebra (𝓘(ℝ, EG)) G, LinearMap.trace ℝ _ (ad ℝ _ x) = 0)
  (eW : HeightSpace T.character ≃ₗ[ℝ] W) (height : G →* Multiplicative W)
  (hheight : ∀ x, (height (ExpG x)).toAdd = eW (heightProjection T.character x))
  (chartN : GroupLieAlgebra (𝓘(ℝ, F.N.modelSpace)) F.N.carrier ≃ₜ F.N.carrier)
  (hchartN : ∀ x, chartN x = F.ExpN x)
  (chartD : GroupLieAlgebra (𝓘(ℝ, F.D.modelSpace)) F.D.carrier ≃ₜ F.D.carrier)
  (hchartD : ∀ x, chartD x = F.ExpD x)
  (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
  (dynkinD : NilpotentDynkinExpansionInput F.D.modelSpace F.D.carrier)

set_option maxHeartbeats 1000000 in
include hunimod hheight dynkinD in
/-- The ideal and Cartan-factor path estimates imply asymptotic equality
for all representatives of the same source boundary point. The source
stabilizer and projection kernel are the actual algebraic constructions. -/
theorem orbit_fiber_quotient_difference_tendsto_one
    [SimplyConnectedSpace G]
    (hExpG : IsGroupExponential ExpG)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
    (haarD : NilpotentExponentialHaarInput F.D.modelSpace F.D.carrier)
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (γ₀ : M.Bases)
    (hφ : ∀ d, F.action d = M.adjointGroupAutomorphism T F.N.equiv F.ExpN F.isExpN
      (by rw [← show chartN = F.ExpN from funext hchartN]; exact chartN.bijective) dynkinN
      (cartanLog H F.D.equiv F.ExpD
        (by rw [← show chartD = F.ExpD from funext hchartD]; exact chartD.bijective) d))
    (hpath : ∀ g : G, ∃ γ : ℝ → G, γ 0 = 1 ∧ γ 1 = g ∧
      ∀ t ∈ Icc (0 : ℝ) 1, ∀ u ∈ Icc (0 : ℝ) 1,
        dist (γ t) (γ u) ≤ dist 1 g * |t - u|)
    {Kheight : ℝ} (hKheight : 0 ≤ Kheight)
    (hLip : ∀ x y, ‖(height x).toAdd - (height y).toAdd‖ ≤ Kheight * dist x y)
    (αW : W →L[ℝ] ℝ)
    (Q : NilpotentLieModel ((cartanRootIdeal H) ⧸ M.coneWordIdeal
      (positiveWeightRay (αW.toLinearMap.comp
        (eW.toLinearMap.comp ((heightProjection T.character).comp H.subtype))))))
    (ExpQ : GroupLieAlgebra (𝓘(ℝ, Q.modelSpace)) Q.carrier → Q.carrier)
    (hExpQ : IsGroupExponential ExpQ)
    (chartQ : GroupLieAlgebra (𝓘(ℝ, Q.modelSpace)) Q.carrier ≃ₜ Q.carrier)
    (hchartQ : ∀ v, chartQ v = ExpQ v)
    (dynkinQ : NilpotentDynkinExpansionInput Q.modelSpace Q.carrier)
    (π : F.N.carrier →* Q.carrier) (hπcont : Continuous π)
    (hπ : ∀ x : cartanRootIdeal H, π (F.ExpN (F.N.equiv x)) =
      ExpQ (Q.equiv (M.coneProjection (positiveWeightRay (αW.toLinearMap.comp
        (eW.toLinearMap.comp ((heightProjection T.character).comp H.subtype)))) x)))
    (α : F.D.carrier →* MulAut Q.carrier) (act : G →* Equiv.Perm Q.carrier)
    (hα : ∀ d n, α d (π n) = π (F.action d n))
    (hact : ∀ u d q, act (F.inclusionN u * F.inclusionD d) q = π u * α d q)
    (A : W →L[ℝ] W) (f : G → G) {L error : ℝ} (hL : 0 ≤ L)
    (hf : ∀ x y, dist (f x) (f y) ≤ L * dist x y + error)
    (hsub : ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, 0 ≤ B ∧ ∀ g,
      ‖(height (f g)).toAdd - A ((height g).toAdd)‖ ≤ ε * dist 1 g + B)
    (v₀ : W) (hv₀ : αW (A v₀) < 0)
    {S : Type} [Group S] (πS : F.N.carrier →* S) (actS : G →* Equiv.Perm S)
    (hkerS : (πS.ker : Set F.N.carrier) = F.ExpN '' (F.N.equiv ''
      (M.coneWordIdeal (positiveWeightRay ((αW.comp A).toLinearMap.comp
        (eW.toLinearMap.comp ((heightProjection T.character).comp H.subtype)))) :
        Set (cartanRootIdeal H))))
    (hstab : ∀ g, actS g 1 = 1 ↔ ∃ n d,
      n ∈ πS.ker ∧ F.inclusionN n * F.inclusionD d = g)
    (g g' : G) (hg : actS g 1 = actS g' 1) :
    let d := fun n : ℕ => ExpG ((n : ℝ) •
      (cartanHeightSection T H (eW.symm v₀) : GroupLieAlgebra (𝓘(ℝ, EG)) G))
    Tendsto (fun n => (act (f (g * d n)) 1)⁻¹ * act (f (g' * d n)) 1)
      atTop (𝓝 (1 : Q.carrier)) := by
  let _ : IsTopologicalGroup Q.carrier := topologicalGroup_of_lieGroup (𝓘(ℝ, Q.modelSpace)) ⊤
  let β := αW.comp A
  let I := M.coneWordIdeal (positiveWeightRay (β.toLinearMap.comp
    (eW.toLinearMap.comp ((heightProjection T.character).comp H.subtype))))
  let ι : I → G := fun x => F.inclusionN (F.ExpN (F.N.equiv (x : cartanRootIdeal H)))
  have hstab' (k : G) : actS k 1 = 1 ↔ ∃ (x : I) (d : F.D.carrier), ι x * F.inclusionD d = k := by
    rw [hstab]
    constructor
    · rintro ⟨n, d, hn, he⟩
      have hn' : n ∈ F.ExpN '' (F.N.equiv '' (I : Set (cartanRootIdeal H))) := by
        rw [← hkerS]
        exact hn
      obtain ⟨v, ⟨x, hx, hv⟩, hn''⟩ := hn'
      subst v
      subst n
      exact ⟨⟨x, hx⟩, d, he⟩
    · rintro ⟨x, d, he⟩
      refine ⟨F.ExpN (F.N.equiv (x : cartanRootIdeal H)), d, ?_, he⟩
      change F.ExpN (F.N.equiv (x : cartanRootIdeal H)) ∈ (πS.ker : Set F.N.carrier)
      rw [hkerS]
      exact ⟨F.N.equiv (x : cartanRootIdeal H), ⟨x, x.property, rfl⟩, rfl⟩
  let ray := fun n : ℕ => ExpG ((n : ℝ) •
    (cartanHeightSection T H (eW.symm v₀) : GroupLieAlgebra (𝓘(ℝ, EG)) G))
  apply orbit_fiber_asymptotic_of_stabilizer actS ι F.inclusionD hstab'
    (fun k n => act (f (k * ray n)) 1) ?_ ?_ g g' hg
  · intro k x
    have hh := M.ideal_fiber_quotient_difference_tendsto_one
      T F hunimod eW height hheight chartN hchartN chartD hchartD dynkinN dynkinD
      hExpG realize haarN haarD b₀ γ₀ hφ hpath hKheight hLip
      αW Q ExpQ hExpQ chartQ hchartQ dynkinQ π hπcont hπ α act hα hact
      A f hL hf hsub v₀ hv₀ x k
    simpa only [ray, ι, mul_assoc] using hh
  · intro k d
    have hh := M.cartan_fiber_quotient_difference_tendsto_one
      T F hunimod eW height hheight chartN hchartN chartD hchartD dynkinN dynkinD
      b₀ γ₀ hφ hpath hKheight hLip
      αW Q ExpQ hExpQ chartQ hchartQ dynkinQ π hπcont hπ α act hα hact
      A f hL hf hsub v₀ hv₀ d k
    simpa only [ray, mul_assoc] using hh

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanRayActionTopology
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instDecidableEqConeMixedWords _root_.OAI.PolycyclicRecognition.CartanWordModel.instFintypeConeMixedWords _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Continuity of the actual ray quotient action -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule Set
open scoped Manifold

variable {EG G : Type} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {ExpG : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H ExpG)

variable (α₀ : H →ₗ[ℝ] ℝ)
  (Q : NilpotentLieModel ((cartanRootIdeal H) ⧸ M.coneWordIdeal (positiveWeightRay α₀)))
  (ExpQ : GroupLieAlgebra (𝓘(ℝ, Q.modelSpace)) Q.carrier → Q.carrier)
  (hbijQ : Function.Bijective ExpQ)
  (chartQ : GroupLieAlgebra (𝓘(ℝ, Q.modelSpace)) Q.carrier ≃ₜ Q.carrier)
  (hchartQ : ∀ v, chartQ v = ExpQ v)
  (hbijN : Function.Bijective F.ExpN) (hbijD : Function.Bijective F.ExpD)
  (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
  (π : F.N.carrier →* Q.carrier)
  (hπ : ∀ x : cartanRootIdeal H,
    π (F.ExpN (F.N.equiv x)) = ExpQ (Q.equiv (M.coneProjection (positiveWeightRay α₀) x)))
  (α : F.D.carrier →* MulAut Q.carrier)
  (hα : ∀ d n, α d (π n) = π (F.action d n))
  (hφ : ∀ d, F.action d = M.adjointGroupAutomorphism T F.N.equiv F.ExpN F.isExpN
    hbijN dynkinN (cartanLog H F.D.equiv F.ExpD hbijD d))

set_option maxHeartbeats 1000000 in
include hbijQ hchartQ hπ hα hφ in
/-- Each actual Cartan factor acts continuously on the ray quotient.
This follows from its previously identified exponential conjugation. -/
theorem continuous_ray_factor_action (d : F.D.carrier) : Continuous (α d) := by
  have heq : (α d : Q.carrier → Q.carrier) = exponentialConjugate Q.equiv ExpQ hbijQ
      (M.coneAdjointAutomorphism T (positiveWeightRay α₀) (positiveWeightRay_add α₀)
        (cartanLog H F.D.equiv F.ExpD hbijD d)) := by
    funext q
    exact M.factor_quotient_action_eq_exponential T F α₀ Q ExpQ hbijQ
      hbijN hbijD dynkinN π hπ α hα hφ d q
  rw [heq]
  exact continuous_exponentialConjugate Q.equiv ExpQ hbijQ chartQ hchartQ _

set_option maxHeartbeats 1000000 in
include hbijQ hchartQ hπ hα hφ in
/-- Every fixed ambient group element acts continuously; no continuity
assumption on a chosen factorization is needed. -/
theorem continuous_ambient_ray_action
    (act : G →* Equiv.Perm Q.carrier)
    (hact : ∀ u d q, act (F.inclusionN u * F.inclusionD d) q = π u * α d q)
    (g : G) : Continuous (act g) := by
  let _ : IsTopologicalGroup Q.carrier := topologicalGroup_of_lieGroup (𝓘(ℝ, Q.modelSpace)) ⊤
  obtain ⟨⟨u, d⟩, he⟩ := F.surjective g
  have heq : (act g : Q.carrier → Q.carrier) = fun q => π u * α d q := by
    funext q
    rw [← he]
    exact hact u d q
  rw [heq]
  exact continuous_const.mul (M.continuous_ray_factor_action T F α₀ Q ExpQ hbijQ
    chartQ hchartQ hbijN hbijD dynkinN π hπ α hα hφ d)

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CenteredHeightError
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Sublinear height errors after changing the basepoint -/

noncomputable section
namespace PolycyclicRecognition

variable {G W : Type} [Group G] [MetricSpace G] [IsIsometricSMul G G]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- Centering also preserves the coarse Lipschitz constants exactly. -/
theorem centered_coarse_lipschitz (f : G → G) {L C : ℝ}
    (hf : ∀ a b, dist (f a) (f b) ≤ L * dist a b + C) (x a b : G) :
    dist ((f x)⁻¹ * f (x * a)) ((f x)⁻¹ * f (x * b)) ≤ L * dist a b + C := by
  rw [dist_mul_left]
  simpa only [dist_mul_left] using hf (x * a) (x * b)

omit [IsIsometricSMul G G] in
/-- Uniform centered height control supplies the absolute sublinear
estimate used in representative independence. -/
theorem absolute_height_sublinear_of_centered_uniform
    (π : G →* Multiplicative W) (A : W →L[ℝ] W) (f : G → G)
    (hsub : ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, 0 ≤ B ∧ ∀ x g,
      ‖(π ((f x)⁻¹ * f (x * g))).toAdd - A ((π g).toAdd)‖ ≤ ε * dist 1 g + B) :
    ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, 0 ≤ B ∧ ∀ g,
      ‖(π (f g)).toAdd - A ((π g).toAdd)‖ ≤ ε * dist 1 g + B := by
  intro ε hε
  obtain ⟨B, hB, hb⟩ := hsub ε hε
  refine ⟨B + ‖(π (f 1)).toAdd‖, by positivity, ?_⟩
  intro g
  have hh := hb 1 g
  simp only [one_mul, map_mul, map_inv, toAdd_mul, toAdd_inv] at hh
  calc
    _ = ‖(-(π (f 1)).toAdd + (π (f g)).toAdd - A ((π g).toAdd)) + (π (f 1)).toAdd‖ := by
      congr 1
      abel
    _ ≤ ‖-(π (f 1)).toAdd + (π (f g)).toAdd - A ((π g).toAdd)‖ + ‖(π (f 1)).toAdd‖ := norm_add_le _ _
    _ ≤ (ε * dist 1 g + B) + ‖(π (f 1)).toAdd‖ := add_le_add hh le_rfl
    _ = _ := by ring

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanBoundaryFamilyShadow
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.CartanFactorModel.heightRay_zero _root_.OAI.PolycyclicRecognition.CartanFactorModel.realScaleProfile_apply _root_.OAI.PolycyclicRecognition.CartanFactorModel.sampledProbeProfile_apply _root_.OAI.PolycyclicRecognition.cartanWeightDerivation_apply_root _root_.OAI.PolycyclicRecognition.chartExponentialFlow_zero _root_.OAI.PolycyclicRecognition.derivationSemidirectHom_apply _root_.OAI.PolycyclicRecognition.exponentialHomOfDynkin_apply_exp _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.modelNilradicalLinearAction_apply _root_.OAI.PolycyclicRecognition.modelNilradicalRotation_apply _root_.OAI.PolycyclicRecognition.modelNilradicalRotation_mul _root_.OAI.PolycyclicRecognition.modelNilradicalRotation_one _root_.OAI.PolycyclicRecognition.nilshadowWeightDerivation_symm _root_.OAI.PolycyclicRecognition.nilshadowWeightOperator_symm _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A common compact shadow for a family with fixed linear height label -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule Filter Set
open scoped Manifold Topology

variable {EG G W P : Type} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [IsIsometricSMul G G] [ProperSpace G]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {ExpG : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H ExpG)
  (hunimod : ∀ x : GroupLieAlgebra (𝓘(ℝ, EG)) G, LinearMap.trace ℝ _ (ad ℝ _ x) = 0)
  (eW : HeightSpace T.character ≃ₗ[ℝ] W) (height : G →* Multiplicative W)
  (hheight : ∀ x, (height (ExpG x)).toAdd = eW (heightProjection T.character x))
  (chartN : GroupLieAlgebra (𝓘(ℝ, F.N.modelSpace)) F.N.carrier ≃ₜ F.N.carrier)
  (hchartN : ∀ x, chartN x = F.ExpN x)
  (chartD : GroupLieAlgebra (𝓘(ℝ, F.D.modelSpace)) F.D.carrier ≃ₜ F.D.carrier)
  (hchartD : ∀ x, chartD x = F.ExpD x)
  (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
  (dynkinD : NilpotentDynkinExpansionInput F.D.modelSpace F.D.carrier)

set_option maxHeartbeats 1000000 in
include hunimod hheight dynkinD in
/-- The common centered sublinear estimate supplies one compact boundary
shadow for the entire fixed-label family, uniformly over its basepoints. -/
theorem exists_boundary_family_with_compact_shadow_oai
    [SimplyConnectedSpace G]
    (hExpG : IsGroupExponential ExpG)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
    (haarD : NilpotentExponentialHaarInput F.D.modelSpace F.D.carrier)
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (γ₀ : M.Bases)
    (hφ : ∀ d, F.action d = M.adjointGroupAutomorphism T F.N.equiv F.ExpN F.isExpN
      (by rw [← show chartN = F.ExpN from funext hchartN]; exact chartN.bijective) dynkinN
      (cartanLog H F.D.equiv F.ExpD
        (by rw [← show chartD = F.ExpD from funext hchartD]; exact chartD.bijective) d))
    (hpath : ∀ g : G, ∃ γ : ℝ → G, γ 0 = 1 ∧ γ 1 = g ∧
      ∀ t ∈ Icc (0 : ℝ) 1, ∀ u ∈ Icc (0 : ℝ) 1,
        dist (γ t) (γ u) ≤ dist 1 g * |t - u|)
    {Kheight : ℝ} (hKheight : 0 ≤ Kheight)
    (hLip : ∀ x y, ‖(height x).toAdd - (height y).toAdd‖ ≤ Kheight * dist x y)
    (αW : W →L[ℝ] ℝ)
    (Q : NilpotentLieModel ((cartanRootIdeal H) ⧸ M.coneWordIdeal
      (positiveWeightRay (αW.toLinearMap.comp
        (eW.toLinearMap.comp ((heightProjection T.character).comp H.subtype))))))
    (ExpQ : GroupLieAlgebra (𝓘(ℝ, Q.modelSpace)) Q.carrier → Q.carrier)
    (hExpQ : IsGroupExponential ExpQ)
    (chartQ : GroupLieAlgebra (𝓘(ℝ, Q.modelSpace)) Q.carrier ≃ₜ Q.carrier)
    (hchartQ : ∀ v, chartQ v = ExpQ v)
    (dynkinQ : NilpotentDynkinExpansionInput Q.modelSpace Q.carrier)
    (π : F.N.carrier →* Q.carrier) (hπcont : Continuous π)
    (hπ : ∀ x : cartanRootIdeal H, π (F.ExpN (F.N.equiv x)) =
      ExpQ (Q.equiv (M.coneProjection (positiveWeightRay (αW.toLinearMap.comp
        (eW.toLinearMap.comp ((heightProjection T.character).comp H.subtype)))) x)))
    (α : F.D.carrier →* MulAut Q.carrier) (act : G →* Equiv.Perm Q.carrier)
    (hα : ∀ d n, α d (π n) = π (F.action d n))
    (hact : ∀ u d q, act (F.inclusionN u * F.inclusionD d) q = π u * α d q)
    (A : W →L[ℝ] W) (f : P → G → G) {L error : ℝ} (hL : 0 ≤ L)
    (hf : ∀ p x y, dist (f p x) (f p y) ≤ L * dist x y + error)
    (hsub : ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, 0 ≤ B ∧ ∀ p x g,
      ‖(height ((f p x)⁻¹ * f p (x * g))).toAdd - A ((height g).toAdd)‖ ≤ ε * dist 1 g + B)
    (v₀ : W) (hv₀ : αW (A v₀) < 0)
    {S : Type} [Group S] (πS : F.N.carrier →* S) (actS : G →* Equiv.Perm S)
    (hkerS : (πS.ker : Set F.N.carrier) = F.ExpN '' (F.N.equiv ''
      (M.coneWordIdeal (positiveWeightRay ((αW.comp A).toLinearMap.comp
        (eW.toLinearMap.comp ((heightProjection T.character).comp H.subtype)))) :
        Set (cartanRootIdeal H))))
    (hstab : ∀ g, actS g 1 = 1 ↔ ∃ n d,
      n ∈ πS.ker ∧ F.inclusionN n * F.inclusionD d = g)
    (hcover : Function.Surjective (fun g => actS g 1)) :
    let ray := fun n : ℕ => ExpG ((n : ℝ) •
      (cartanHeightSection T H (eW.symm v₀) : GroupLieAlgebra (𝓘(ℝ, EG)) G))
    ∃ (B : P → S → Q.carrier) (K : Set Q.carrier), IsCompact K ∧ ∀ p x,
      Tendsto (fun n => act (f p (x * ray n)) 1) atTop (𝓝 (B p (actS x 1))) ∧
      ∃ z ∈ K, B p (actS x 1) = act (f p x) z := by
  classical
  let _ : IsTopologicalGroup Q.carrier := topologicalGroup_of_lieGroup (𝓘(ℝ, Q.modelSpace)) ⊤
  let centered := fun (p : P × G) g => (f p.1 p.2)⁻¹ * f p.1 (p.2 * g)
  have hcenter (p : P × G) : centered p 1 = 1 := by simp [centered]
  have hcoarse (p : P × G) x y :
      dist (centered p x) (centered p y) ≤ L * dist x y + error :=
    centered_coarse_lipschitz (f p.1) (hf p.1) p.2 x y
  have hsub' : ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, 0 ≤ B ∧ ∀ p g,
      ‖(height (centered p g)).toAdd - A ((height g).toAdd)‖ ≤ ε * dist 1 g + B := by
    intro ε hε
    obtain ⟨B, hB, hb⟩ := hsub ε hε
    exact ⟨B, hB, fun p g => hb p.1 p.2 g⟩
  obtain ⟨k, K, hK, hkK, hk⟩ := M.centered_ray_quotient_compact_limits
    T F hunimod eW height hheight chartN hchartN chartD hchartD dynkinN dynkinD
    b₀ γ₀ hφ hpath hKheight hLip αW Q ExpQ hExpQ chartQ hchartQ dynkinQ
    π hπcont hπ α act hα hact hExpG A centered hcenter hL hcoarse hsub' v₀ hv₀
  have habsolute p := absolute_height_sublinear_of_centered_uniform height A (f p)
    (by
      intro ε hε
      obtain ⟨B, hB, hb⟩ := hsub ε hε
      exact ⟨B, hB, fun x g => hb p x g⟩)
  let αH := αW.toLinearMap.comp
    (eW.toLinearMap.comp ((heightProjection T.character).comp H.subtype))
  have hbijN : Function.Bijective F.ExpN := by
    rw [← show chartN = F.ExpN from funext hchartN]
    exact chartN.bijective
  have hbijD : Function.Bijective F.ExpD := by
    rw [← show chartD = F.ExpD from funext hchartD]
    exact chartD.bijective
  have hbijQ : Function.Bijective ExpQ := by
    rw [← show chartQ = ExpQ from funext hchartQ]
    exact chartQ.bijective
  have hcontinuous := M.continuous_ambient_ray_action T F αH Q ExpQ hbijQ chartQ hchartQ
    hbijN hbijD dynkinN π hπ α hα hφ act hact
  have hex p := boundary_shadow_of_centered_limits act hcontinuous
    (fun g => actS g 1) hcover (f p)
    (fun n : ℕ => ExpG ((n : ℝ) •
      (cartanHeightSection T H (eW.symm v₀) : GroupLieAlgebra (𝓘(ℝ, EG)) G)))
    K (fun x => k (p, x)) (fun x => hkK (p, x)) (fun x => hk (p, x))
    (fun x y he => M.orbit_fiber_quotient_difference_tendsto_one
      T F hunimod eW height hheight chartN hchartN chartD hchartD dynkinN dynkinD
      hExpG realize haarN haarD b₀ γ₀ hφ hpath hKheight hLip
      αW Q ExpQ hExpQ chartQ hchartQ dynkinQ π hπcont hπ α act hα hact
      A (f p) hL (hf p) (habsolute p) v₀ hv₀ πS actS hkerS hstab x y he)
  choose B hB using hex
  exact ⟨B, K, hK, hB⟩

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

theorem solution : type_of% @OAI.PolycyclicRecognition.CartanWordModel.exists_boundary_family_with_compact_shadow_oai := @OAI.PolycyclicRecognition.CartanWordModel.exists_boundary_family_with_compact_shadow_oai
