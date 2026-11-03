-- Prove2me | solution 1 for OAI.PolycyclicRecognition.CartanWordModel.exists_uniform_intrinsic_bridge_lifts
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-03T00:15:57.162379+00:00
-- url     : https://prove2.me/submissions/016c21bf-ec2d-4a31-8a72-2d4b6158db2e

import Mathlib
import Definitions.Def_PolycyclicRecognition
import Definitions.Def_OAIQ093D027
import Theorems.Thm_OAI_PolycyclicRecognition_CartanWordModel_exists_uniform_sequence_metric_factor_bounds_m

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

variable {𝕜 : Type} [Field 𝕜]

variable {V I J : Type} [AddCommGroup V] [Module 𝕜 V] (U : Submodule 𝕜 V)
  (bU : Basis I 𝕜 U) (bQ : Basis J 𝕜 (V ⧸ U))
  (lift : J → V) (hlift : ∀ j, U.mkQ (lift j) = bQ j)

theorem basisWithQuotientLifts_repr_inl (v : U) (i : I) :
    (basisWithQuotientLifts U bU bQ lift hlift).repr (v : V) (Sum.inl i) = bU.repr v i := by
  classical
  let b := basisWithQuotientLifts U bU bQ lift hlift
  have hf : (b.coord (Sum.inl i)).comp U.subtype = bU.coord i := by
    apply bU.ext
    intro j
    change b.repr (bU j : V) (Sum.inl i) = bU.repr (bU j) i
    rw [← basisWithQuotientLifts_inl U bU bQ lift hlift j]
    simp only [b, Basis.repr_self, Finsupp.single_apply, Sum.inl.injEq]
  exact congrArg (fun f : U →ₗ[𝕜] 𝕜 => f v) hf

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
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_FactorProductPacking
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Packing through a possibly noninjective factor map

Left translations on a semidirect product act separately on its two factor
coordinates. Their product measure is preserved when the action preserves
the first factor's measure. Disjointness is tested after projection to the
ambient metric group, so no injectivity of that projection is required.
-/

noncomputable section

namespace PolycyclicRecognition

open MeasureTheory Metric Set
open scoped ENNReal

variable {N D G : Type} [Group N] [Group D] [Group G]
  [MeasurableSpace N] [MeasurableSpace D] [MeasurableMul N] [MeasurableMul D]

omit [MeasurableSpace N] [MeasurableSpace D] [MeasurableMul N] [MeasurableMul D] in
/-- The product-coordinate map intertwines translations and ambient multiplication. -/
theorem factorTranslate_projection (φ : D →* MulAut N)
    (ι : N →* G) (κ : D →* G)
    (hc : ∀ d n, ι (φ d n) = κ d * ι n * (κ d)⁻¹) (p z : N × D) :
    ι (factorTranslate φ p z).1 * κ (factorTranslate φ p z).2 =
      (ι p.1 * κ p.2) * (ι z.1 * κ z.2) := by
  simp only [factorTranslate, map_mul, hc]
  group

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_FactorBridgeComposition
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact composition of a probe path and its bridge -/

namespace PolycyclicRecognition

variable {N D G : Type} [Group N] [Group D] [Group G]

theorem factorTranslate_assoc (φ : D →* MulAut N) (p q z : N × D) :
    factorTranslate φ (factorTranslate φ p q) z =
      factorTranslate φ p (factorTranslate φ q z) := by
  apply Prod.ext
  · simp only [factorTranslate, map_mul, MulAut.mul_apply]
    exact mul_assoc _ _ _
  · exact mul_assoc _ _ _

theorem factor_bridge_projection (φ : D →* MulAut N) (ι : N →* G) (κ : D →* G)
    (hc : ∀ d n, ι (φ d n) = κ d * ι n * (κ d)⁻¹)
    (u₂ ub : N) (d₂ db : D) (g : G) (hg : ι ub * κ db = g) :
    ι (u₂ * φ d₂ ub) * κ (d₂ * db) = (ι u₂ * κ d₂) * g := by
  exact (factorTranslate_projection φ ι κ hc (u₂, d₂) (ub, db)).trans (by rw [hg])

theorem factor_bridge_right_coordinate (φ : D →* MulAut N)
    (u₂ ub : N) (d₂ db : D) (z : N × D) :
    (u₂ * φ d₂ ub) * φ (d₂ * db) z.1 = u₂ * φ d₂ (ub * φ db z.1) := by
  exact congrArg Prod.fst (factorTranslate_assoc φ (u₂, d₂) (ub, db) z)

/-- Composition preserves a uniform right-cell restriction after the
bridge's exponential error has been absorbed. -/
theorem exists_thickened_factor_bridge {V I Q : Type}
    (φ : D →* MulAut N) (ι : N →* G) (κ : D →* G)
    (hc : ∀ d n, ι (φ d n) = κ d * ι n * (κ d)⁻¹)
    (Exp : V → N) (ExpI : I → N) (qsec : Q → N)
    (small : V → Prop) (ideal : I → Prop) (DB DF : D → Prop)
    (cell : Set (N × D)) (u₂ : N) (d₂ : D) (g : G)
    (habsorb : ∀ v, small v → ∃ i q,
      u₂ * φ d₂ (Exp v) = ExpI i * qsec q ∧ ideal i)
    (hD : ∀ d, DB d → DF (d₂ * d))
    (hbridge : ∃ ub db, ι ub * κ db = g ∧ ∀ z ∈ cell,
      (∃ v, Exp v = ub * φ db z.1 ∧ small v) ∧ DB (db * z.2)) :
    ∃ u d, ι u * κ d = (ι u₂ * κ d₂) * g ∧ ∀ z ∈ cell,
      (∃ i q, u * φ d z.1 = ExpI i * qsec q ∧ ideal i) ∧ DF (d * z.2) := by
  obtain ⟨ub, db, hg, hb⟩ := hbridge
  refine ⟨u₂ * φ d₂ ub, d₂ * db,
    factor_bridge_projection φ ι κ hc u₂ ub d₂ db g hg, ?_⟩
  intro z hz
  obtain ⟨⟨v, hv, hs⟩, hd⟩ := hb z hz
  obtain ⟨i, q, he, hi⟩ := habsorb v hs
  refine ⟨⟨i, q, ?_, hi⟩, ?_⟩
  · rw [factor_bridge_right_coordinate, ← hv]
    exact he
  · simpa only [mul_assoc] using hD (db * z.2) hd

end PolycyclicRecognition

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_WordBasisCoordinates
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Maximizing actual word bases

Invertible selections from the coordinate matrix are exactly the actual word
bases. Thus the finite maximizing-basis argument applies to the Lie word list.
-/

noncomputable section

namespace PolycyclicRecognition

open Module

variable {I L : Type} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  (X : I → L) (S : Finset (FreeMagma I))
  (b₀ : Basis (Fin (finrank ℝ L)) ℝ L)

/-- Maximizing over actual bases also maximizes over every invertible column
selection. This connects the intrinsic list to the box coordinate estimates. -/
theorem exists_maximizing_wordBasis [Nonempty (WordBasisSelections X S)]
    (cost : S → ℝ) : ∃ β : WordBasisSelections X S,
      IsMaximizingColumnBasis (wordListCoordinates X S b₀) cost β.val := by
  classical
  obtain ⟨β, _, hβ⟩ := Finset.exists_max_image Finset.univ
    (fun β : WordBasisSelections X S => columnBasisWeight cost β.val) Finset.univ_nonempty
  refine ⟨β, wordBasis_det_ne_zero X S b₀ β, ?_⟩
  intro w hw
  simpa only [wordBasisOfDet_val] using
    hβ (wordBasisOfDet X S b₀ w hw) (Finset.mem_univ _)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_WordExponents
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Additive exponents of bracket words

Letter amplitudes add through every bracket. The sum in a word basis is the
letter-count expression used by the support datum.
-/

namespace PolycyclicRecognition

open scoped BigOperators

variable {I J : Type} [Fintype I] [DecidableEq I]

theorem sum_bracketWordExponent [Fintype J] (s : I → ℝ) (words : J → FreeMagma I) :
    ∑ j, bracketWordExponent s (words j) =
      ∑ i, ((∑ j, bracketWordCount (words j) i : ℕ) : ℝ) * s i := by
  simp only [bracketWordExponent, Nat.cast_sum, Finset.sum_mul]
  exact Finset.sum_comm

end PolycyclicRecognition

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
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_IdealSectionBoxCoordinates
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.exponentialQuotientSection_apply _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact linear coordinates for an ideal and its quotient

Pure quotient lifts have weight zero. In the adapted basis, projection
retains exactly those coordinates, and inclusion of the ideal retains
exactly the weighted ideal coordinates. This is the linear part of the
section-coordinate box comparison.
-/

noncomputable section
namespace PolycyclicRecognition

open Module

variable {V I J : Type} [LieRing V] [LieAlgebra ℝ V]
  (U : LieIdeal ℝ V) (bI : Basis I ℝ U) (bQ : Basis J ℝ (V ⧸ U.toSubmodule))
  (lift : J → V) (hlift : ∀ j, U.toSubmodule.mkQ (lift j) = bQ j)

theorem quotientLinearSection_repr_inl (q : V ⧸ U.toSubmodule) (i : I) :
    (basisWithQuotientLifts U.toSubmodule bI bQ lift hlift).repr
      (quotientLinearSection U bQ lift q) (Sum.inl i) = 0 := by
  let b := basisWithQuotientLifts U.toSubmodule bI bQ lift hlift
  have he : (b.coord (Sum.inl i)).comp (quotientLinearSection U bQ lift) = 0 := by
    apply bQ.ext
    intro j
    simp only [LinearMap.comp_apply, quotientLinearSection, Basis.constr_basis,
      LinearMap.zero_apply]
    change b.repr (lift j) (Sum.inl i) = 0
    have hj : lift j = b (Sum.inr j) :=
      (basisWithQuotientLifts_inr U.toSubmodule bI bQ lift hlift j).symm
    rw [hj, Basis.repr_self]
    simp
  exact congrArg (fun f : (V ⧸ U.toSubmodule) →ₗ[ℝ] ℝ => f q) he

theorem quotientLinearSection_repr_inr (q : V ⧸ U.toSubmodule) (j : J) :
    (basisWithQuotientLifts U.toSubmodule bI bQ lift hlift).repr
      (quotientLinearSection U bQ lift q) (Sum.inr j) = bQ.repr q j := by
  rw [basisWithQuotientLifts_repr_inr, quotientLinearSection_rightInverse U bQ lift hlift]

variable [Fintype I] [Fintype J]

/-- Inclusion of the ideal is an isometry for the weighted coordinate norms. -/
theorem ideal_scaled_coordinates_le_iff (s : I → ℝ) (r R : ℝ) (hR : 0 ≤ R) (u : U) :
    ‖(exponentialRescaleBasis
      (basisWithQuotientLifts U.toSubmodule bI bQ lift hlift)
      (Sum.elim s (fun _ => 0)) r).equivFun (u : V)‖ ≤ R ↔
    ‖(exponentialRescaleBasis bI s r).equivFun u‖ ≤ R := by
  rw [pi_norm_le_iff_of_nonneg hR, pi_norm_le_iff_of_nonneg hR]
  constructor
  · intro h i
    have hi := h (Sum.inl i)
    simpa only [Basis.equivFun_apply, exponentialRescaleBasis, Basis.repr_unitsSMul,
      Units.smul_def, Units.val_inv_eq_inv_val, Units.val_mk0, Sum.elim_inl,
      basisWithQuotientLifts_repr_inl] using hi
  · intro h k
    cases k with
    | inl i =>
      simpa only [Basis.equivFun_apply, exponentialRescaleBasis, Basis.repr_unitsSMul,
        Units.smul_def, Units.val_inv_eq_inv_val, Units.val_mk0, Sum.elim_inl,
        basisWithQuotientLifts_repr_inl] using h i
    | inr j =>
      have hz : U.toSubmodule.mkQ (u : V) = 0 :=
        (Submodule.Quotient.mk_eq_zero U.toSubmodule).mpr u.property
      simpa only [Basis.equivFun_apply, exponentialRescaleBasis, Basis.repr_unitsSMul,
        Units.smul_def, Units.val_inv_eq_inv_val, Units.val_mk0, Sum.elim_inr,
        basisWithQuotientLifts_repr_inr, hz, map_zero, Finsupp.zero_apply,
        smul_zero, norm_zero] using hR

/-- Projection to the quotient never enlarges the adapted coordinate bound. -/
theorem quotient_scaled_coordinates_le (s : I → ℝ) (r R : ℝ) (hR : 0 ≤ R)
    (v : V) (hv : ‖(exponentialRescaleBasis
      (basisWithQuotientLifts U.toSubmodule bI bQ lift hlift)
      (Sum.elim s (fun _ => 0)) r).equivFun v‖ ≤ R) :
    ‖bQ.equivFun (U.toSubmodule.mkQ v)‖ ≤ R := by
  apply (pi_norm_le_iff_of_nonneg hR).mpr
  intro j
  have hj := (pi_norm_le_iff_of_nonneg hR).mp hv (Sum.inr j)
  simpa only [Basis.equivFun_apply, exponentialRescaleBasis, Basis.repr_unitsSMul,
    Units.smul_def, Units.val_inv_eq_inv_val, Units.val_mk0, Sum.elim_inr,
    mul_zero, Real.exp_zero, inv_one, one_smul, basisWithQuotientLifts_repr_inr] using hj

/-- A quotient log ball lifts into the zero-width part of every adapted box. -/
theorem section_scaled_coordinates_le (s : I → ℝ) (r R : ℝ) (hR : 0 ≤ R)
    (q : V ⧸ U.toSubmodule) (hq : ‖bQ.equivFun q‖ ≤ R) :
    ‖(exponentialRescaleBasis
      (basisWithQuotientLifts U.toSubmodule bI bQ lift hlift)
      (Sum.elim s (fun _ => 0)) r).equivFun (quotientLinearSection U bQ lift q)‖ ≤ R := by
  apply (pi_norm_le_iff_of_nonneg hR).mpr
  intro k
  cases k with
  | inl i =>
    simpa only [Basis.equivFun_apply, exponentialRescaleBasis, Basis.repr_unitsSMul,
      Units.smul_def, Units.val_inv_eq_inv_val, Units.val_mk0, Sum.elim_inl,
      quotientLinearSection_repr_inl, smul_zero, norm_zero] using hR
  | inr j =>
    have hj := (pi_norm_le_iff_of_nonneg hR).mp hq j
    simpa only [Basis.equivFun_apply, exponentialRescaleBasis, Basis.repr_unitsSMul,
      Units.smul_def, Units.val_inv_eq_inv_val, Units.val_mk0, Sum.elim_inr,
      mul_zero, Real.exp_zero, inv_one, one_smul, quotientLinearSection_repr_inr] using hj

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_NilpotentSectionRemainder
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.CartanFactorModel.realScaleProfile_apply _root_.OAI.PolycyclicRecognition.basisDynkinParameter_zero _root_.OAI.PolycyclicRecognition.dynkinRightTranslation_apply _root_.OAI.PolycyclicRecognition.dynkinRightTranslation_symm_apply _root_.OAI.PolycyclicRecognition.exponentialHomOfDynkin_apply_exp _root_.OAI.PolycyclicRecognition.exponentialQuotientSection_apply _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial bounds for the actual ideal section remainder

The remainder of an exponential after removing its pure quotient section
is computed with the finite BCH formula. Its ideal coordinates have a
polynomial bound in the original logarithm. No box comparison is assumed.
-/

noncomputable section
namespace PolycyclicRecognition

open Module Set
open scoped BigOperators

variable {V I J : Type} [LieRing V] [LieAlgebra ℝ V] [Fintype I] [Fintype J]
  (U : LieIdeal ℝ V) (bI : Basis I ℝ U) (bQ : Basis J ℝ (V ⧸ U.toSubmodule))
  (lift : J → V) (hlift : ∀ j, U.toSubmodule.mkQ (lift j) = bQ j)

/-- Removing all ideal coordinates is a contraction in the adapted norm. -/
theorem quotient_section_coordinate_norm_le (v : V) :
    ‖(basisWithQuotientLifts U.toSubmodule bI bQ lift hlift).equivFun
      (quotientLinearSection U bQ lift (U.toSubmodule.mkQ v))‖ ≤
    ‖(basisWithQuotientLifts U.toSubmodule bI bQ lift hlift).equivFun v‖ := by
  let b := basisWithQuotientLifts U.toSubmodule bI bQ lift hlift
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
  intro k
  cases k with
  | inl i =>
    change ‖b.repr (quotientLinearSection U bQ lift (U.toSubmodule.mkQ v)) (Sum.inl i)‖ ≤ _
    rw [quotientLinearSection_repr_inl]
    simpa only [norm_zero] using norm_nonneg (b.equivFun v)
  | inr j =>
    have hh := norm_le_pi_norm (b.equivFun v) (Sum.inr j)
    change ‖b.repr v (Sum.inr j)‖ ≤ _ at hh
    change ‖b.repr (quotientLinearSection U bQ lift (U.toSubmodule.mkQ v)) (Sum.inr j)‖ ≤ _
    rw [quotientLinearSection_repr_inr]
    rwa [basisWithQuotientLifts_repr_inr] at hh

variable {N Q : Type} [Group N] [Group Q]
  (ExpN : V → N) (ExpQ : (V ⧸ U.toSubmodule) → Q) (π : N →* Q)
  (hπ : ∀ v, π (ExpN v) = ExpQ (U.toSubmodule.mkQ v))
  (hinjQ : Function.Injective ExpQ) (hzeroQ : ExpQ 0 = 1)
  (hneg : ∀ v, ExpN (-v) = (ExpN v)⁻¹)
  {c : ℕ} (coeff : DynkinCoefficients c 2)
  (hcoeff : ∀ d w, |coeff d w| ≤ (2 : ℝ) ^ c)
  (hmul : ∀ v w, ExpN (finiteDynkinPolynomial coeff ![v, w]) = ExpN v * ExpN w)

omit [Fintype J] in
include hlift hπ hinjQ hzeroQ hneg hmul in
/-- This is the actual kernel coordinate, not a freely selected small lift. -/
theorem section_remainder_mem_ideal (v : V) :
    finiteDynkinPolynomial coeff
      ![v, -quotientLinearSection U bQ lift (U.toSubmodule.mkQ v)] ∈ U := by
  let w := quotientLinearSection U bQ lift (U.toSubmodule.mkQ v)
  have hproj : π (ExpN w) = π (ExpN v) := by
    rw [hπ, hπ, quotientLinearSection_rightInverse U bQ lift hlift]
  apply (Submodule.Quotient.mk_eq_zero U.toSubmodule).mp
  apply hinjQ
  change ExpQ (U.toSubmodule.mkQ (finiteDynkinPolynomial coeff ![v, -w])) = ExpQ 0
  rw [hzeroQ, ← hπ, hmul, hneg, map_mul, map_inv]
  change π (ExpN v) * (π (ExpN w))⁻¹ = 1
  rw [hproj, mul_inv_cancel]

include hπ hinjQ hzeroQ hneg hcoeff hmul in
/-- The same fixed polynomial controls the ideal remainder of every log. -/
theorem section_remainder_polynomial_bound (C : ℝ) (hC : 0 ≤ C)
    (hbr : ∀ i j k, |(basisWithQuotientLifts U.toSubmodule bI bQ lift hlift).repr
      ⁅basisWithQuotientLifts U.toSubmodule bI bQ lift hlift i,
        basisWithQuotientLifts U.toSubmodule bI bQ lift hlift j⁆ k| ≤ C) :
    ∀ R : ℝ, 0 ≤ R → ∀ v : V,
      ‖(basisWithQuotientLifts U.toSubmodule bI bQ lift hlift).equivFun v‖ ≤ R →
      ∃ u : U,
        ExpN (u : V) = ExpN v *
          (ExpN (quotientLinearSection U bQ lift (U.toSubmodule.mkQ v)))⁻¹ ∧
        ‖bI.equivFun u‖ ≤ sectionDynkinConstant (Fintype.card (I ⊕ J)) c C * (1 + R) ^ c := by
  let b := basisWithQuotientLifts U.toSubmodule bI bQ lift hlift
  let K := sectionDynkinConstant (Fintype.card (I ⊕ J)) c C
  have hK : 0 ≤ K := by dsimp [K, sectionDynkinConstant] <;> positivity
  intro R hR v hv
  let w := quotientLinearSection U bQ lift (U.toSubmodule.mkQ v)
  let z := finiteDynkinPolynomial coeff ![v, -w]
  have hz : z ∈ U := section_remainder_mem_ideal U bQ lift hlift ExpN ExpQ π
    hπ hinjQ hzeroQ hneg coeff hmul v
  let u : U := ⟨z, hz⟩
  have hw : ‖b.equivFun w‖ ≤ R :=
    (quotient_section_coordinate_norm_le U bI bQ lift hlift v).trans hv
  have hvec : ∀ k : Fin 2, ‖b.equivFun (![v, -w] k)‖ ≤ R := by
    intro k
    fin_cases k
    · exact hv
    · change ‖b.equivFun (-w)‖ ≤ R
      simpa only [map_neg, norm_neg] using hw
  have hb := norm_finiteDynkinPolynomial_le b coeff hcoeff ![v, -w] hC hR hbr hvec
  have hbound : ‖b.equivFun z‖ ≤ K * (1 + R) ^ c := by
    exact hb.trans_eq (by dsimp [K, sectionDynkinConstant] <;> norm_num <;> ring)
  refine ⟨u, ?_, ?_⟩
  · change ExpN z = _
    rw [hmul, hneg]
  · have hh := (ideal_scaled_coordinates_le_iff U bI bQ lift hlift (fun _ => 0)
        0 (K * (1 + R) ^ c) (mul_nonneg hK (pow_nonneg (by linarith) _)) u).mp
    simpa only [exponentialRescaleBasis_zero] using
      hh (by simpa only [exponentialRescaleBasis_zero] using hbound)

include hπ hinjQ hzeroQ hneg hcoeff hmul in
/-- Factor a pure section followed by an arbitrary small logarithmic error.
Both new coordinates have polynomial bounds, even when the new quotient
coordinate leaves a subexponential ball. -/
theorem section_error_factorization_bound (C : ℝ) (hC : 0 ≤ C)
    (hbr : ∀ i j k, |(basisWithQuotientLifts U.toSubmodule bI bQ lift hlift).repr
      ⁅basisWithQuotientLifts U.toSubmodule bI bQ lift hlift i,
        basisWithQuotientLifts U.toSubmodule bI bQ lift hlift j⁆ k| ≤ C) :
    ∀ R : ℝ, 0 ≤ R →
      ∀ (q : V ⧸ U.toSubmodule) (e : V),
        ‖bQ.equivFun q‖ ≤ R →
        ‖(basisWithQuotientLifts U.toSubmodule bI bQ lift hlift).equivFun e‖ ≤ R →
        ∃ (u : U) (q' : V ⧸ U.toSubmodule),
          ExpN (quotientLinearSection U bQ lift q) * ExpN e =
            ExpN (u : V) * ExpN (quotientLinearSection U bQ lift q') ∧
          ‖bI.equivFun u‖ ≤
            (sectionDynkinConstant (Fintype.card (I ⊕ J)) c C *
              (1 + sectionDynkinConstant (Fintype.card (I ⊕ J)) c C) ^ c) *
                (1 + R) ^ (c * c) := by
  let b := basisWithQuotientLifts U.toSubmodule bI bQ lift hlift
  let K₀ := sectionDynkinConstant (Fintype.card (I ⊕ J)) c C
  have hK₀ : 0 ≤ K₀ := by dsimp [K₀, sectionDynkinConstant] <;> positivity
  have hrem := section_remainder_polynomial_bound
    U bI bQ lift hlift ExpN ExpQ π hπ hinjQ hzeroQ hneg coeff hcoeff hmul C hC hbr
  intro R hR q e hq he
  let v := finiteDynkinPolynomial coeff ![quotientLinearSection U bQ lift q, e]
  have hs : ‖b.equivFun (quotientLinearSection U bQ lift q)‖ ≤ R := by
    simpa only [exponentialRescaleBasis_zero] using
      section_scaled_coordinates_le U bI bQ lift hlift (fun _ => 0) 0 R hR q hq
  have hv : ‖b.equivFun v‖ ≤ K₀ * (1 + R) ^ c := by
    have hvec : ∀ k : Fin 2,
        ‖b.equivFun (![quotientLinearSection U bQ lift q, e] k)‖ ≤ R := by
      intro k
      fin_cases k
      · exact hs
      · exact he
    exact (norm_finiteDynkinPolynomial_le b coeff hcoeff _ hC hR hbr hvec).trans_eq
      (by dsimp [K₀, sectionDynkinConstant] <;> norm_num <;> ring)
  obtain ⟨u, hu, hbound⟩ := hrem (K₀ * (1 + R) ^ c)
    (mul_nonneg hK₀ (pow_nonneg (by linarith) _)) v hv
  refine ⟨u, U.toSubmodule.mkQ v, ?_, ?_⟩
  · rw [hu]
    simp only [mul_assoc, inv_mul_cancel, mul_one]
    exact (hmul _ _).symm
  · have hbase : 1 + K₀ * (1 + R) ^ c ≤ (1 + K₀) * (1 + R) ^ c := by
      have hp : 1 ≤ (1 + R) ^ c := one_le_pow₀ (by linarith)
      nlinarith
    calc
      _ ≤ K₀ * (1 + K₀ * (1 + R) ^ c) ^ c := hbound
      _ ≤ K₀ * ((1 + K₀) * (1 + R) ^ c) ^ c := by gcongr
      _ = _ := by rw [mul_pow, ← pow_mul]; ring

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_SectionWeightedBoxes
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform weighted-box comparison in ideal section coordinates -/

noncomputable section
namespace PolycyclicRecognition

open Module Set

variable {V I J : Type} [LieRing V] [LieAlgebra ℝ V] [Fintype I] [Fintype J]
  (U : LieIdeal ℝ V) (bI : Basis I ℝ U) (bQ : Basis J ℝ (V ⧸ U.toSubmodule))
  (lift : J → V) (hlift : ∀ j, U.toSubmodule.mkQ (lift j) = bQ j)

omit [Fintype I] [Fintype J] in
/-- Only ideal coordinates are rescaled; the quotient lifts have zero width. -/
theorem basisWithQuotientLifts_rescale (cost : I → ℝ) (r : ℝ) :
    basisWithQuotientLifts U.toSubmodule (exponentialRescaleBasis bI cost r) bQ lift hlift =
      exponentialRescaleBasis (basisWithQuotientLifts U.toSubmodule bI bQ lift hlift)
        (Sum.elim cost (fun _ => 0)) r := by
  apply Basis.eq_of_apply_eq
  intro k
  cases k with
  | inl i =>
    simp only [basisWithQuotientLifts_inl, exponentialRescaleBasis, Basis.unitsSMul_apply,
      Units.smul_def, Units.val_mk0, Sum.elim_inl, SetLike.val_smul]
  | inr j =>
    simp only [basisWithQuotientLifts_inr, exponentialRescaleBasis, Basis.unitsSMul_apply,
      Units.smul_def, Units.val_mk0, Sum.elim_inr, mul_zero, Real.exp_zero, one_smul]

variable {N Q : Type} [Group N] [Group Q]
  (ExpN : V → N) (ExpQ : (V ⧸ U.toSubmodule) → Q) (π : N →* Q)
  (hπ : ∀ v, π (ExpN v) = ExpQ (U.toSubmodule.mkQ v))
  (hinjQ : Function.Injective ExpQ) (hzeroQ : ExpQ 0 = 1)
  (hneg : ∀ v, ExpN (-v) = (ExpN v)⁻¹)
  {c : ℕ} (coeff : DynkinCoefficients c 2)
  (hcoeff : ∀ d w, |coeff d w| ≤ (2 : ℝ) ^ c)
  (hmul : ∀ v w, ExpN (finiteDynkinPolynomial coeff ![v, w]) = ExpN v * ExpN w)
  (cost : I → ℝ) (C : ℝ) (hC : 0 ≤ C)

local notation "B" => basisWithQuotientLifts U.toSubmodule bI bQ lift hlift
local notation "Br" => (fun r : ℝ => exponentialRescaleBasis B (Sum.elim cost (fun _ => 0)) r)
local notation "K" => sectionDynkinConstant (Fintype.card (I ⊕ J)) c C

include hπ hinjQ hzeroQ hneg hcoeff hmul hC in
/-- A full weighted box has bounded quotient logarithm and polynomially
bounded ideal coordinate, with a constant uniform in the height scale. -/
theorem weighted_section_box_factorization
    (hbr : ∀ r : ℝ, 0 ≤ r → ∀ i j k, |(Br r).repr ⁅Br r i, Br r j⁆ k| ≤ C)
    (r R : ℝ) (hr : 0 ≤ r) (hR : 0 ≤ R) {n : N}
    (hn : n ∈ exponentialCoordinateBox ExpN (Br r) R) :
    ∃ (u : U) (q : V ⧸ U.toSubmodule),
      n = ExpN (u : V) * ExpN (quotientLinearSection U bQ lift q) ∧
      ‖(exponentialRescaleBasis bI cost r).equivFun u‖ ≤ K * (1 + R) ^ c ∧
      ‖bQ.equivFun q‖ ≤ R := by
  obtain ⟨v, rfl, hv⟩ := hn
  have hb : ∀ i j k, |(basisWithQuotientLifts U.toSubmodule
      (exponentialRescaleBasis bI cost r) bQ lift hlift).repr
      ⁅basisWithQuotientLifts U.toSubmodule (exponentialRescaleBasis bI cost r) bQ lift hlift i,
        basisWithQuotientLifts U.toSubmodule (exponentialRescaleBasis bI cost r) bQ lift hlift j⁆ k| ≤ C := by
    simpa only [basisWithQuotientLifts_rescale] using hbr r hr
  obtain ⟨u, hu, hbound⟩ := section_remainder_polynomial_bound U
    (exponentialRescaleBasis bI cost r) bQ lift hlift ExpN ExpQ π hπ hinjQ hzeroQ
    hneg coeff hcoeff hmul C hC hb R hR v
    (by simpa only [basisWithQuotientLifts_rescale] using hv)
  refine ⟨u, U.toSubmodule.mkQ v, ?_, hbound, ?_⟩
  · rw [hu]
    simp only [mul_assoc, inv_mul_cancel, mul_one]
  · exact quotient_scaled_coordinates_le U bI bQ lift hlift cost r R hR v hv

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_IdealProductCoordinates
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.basisDynkinParameter_zero _root_.OAI.PolycyclicRecognition.dynkinRightTranslation_apply _root_.OAI.PolycyclicRecognition.dynkinRightTranslation_symm_apply _root_.OAI.PolycyclicRecognition.exponentialHomOfDynkin_apply_exp _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Multiplying the two ideal factors in the section error estimate -/

noncomputable section
namespace PolycyclicRecognition

open Module

variable {V I J N : Type} [LieRing V] [LieAlgebra ℝ V] [Fintype I] [Fintype J]
  [Group N]
  (U : LieIdeal ℝ V) (bI : Basis I ℝ U) (bQ : Basis J ℝ (V ⧸ U.toSubmodule))
  (lift : J → V) (hlift : ∀ j, U.toSubmodule.mkQ (lift j) = bQ j)

omit [Fintype I] [Fintype J] in
/-- The restricted bracket has the same bound as the ambient adapted basis. -/
theorem ideal_basis_bracket_bound {C : ℝ}
    (hbr : ∀ i j k, |(basisWithQuotientLifts U.toSubmodule bI bQ lift hlift).repr
      ⁅basisWithQuotientLifts U.toSubmodule bI bQ lift hlift i,
        basisWithQuotientLifts U.toSubmodule bI bQ lift hlift j⁆ k| ≤ C) :
    ∀ i j k, |bI.repr ⁅bI i, bI j⁆ k| ≤ C := by
  intro i j k
  have hh := hbr (Sum.inl i) (Sum.inl j) (Sum.inl k)
  simp only [basisWithQuotientLifts_inl] at hh
  change |(basisWithQuotientLifts U.toSubmodule bI bQ lift hlift).repr
    ((⁅bI i, bI j⁆ : U) : V) (Sum.inl k)| ≤ C at hh
  rwa [basisWithQuotientLifts_repr_inl] at hh

variable (ExpN : V → N) {c : ℕ} (coeff : DynkinCoefficients c 2)
  (hcoeff : ∀ d w, |coeff d w| ≤ (2 : ℝ) ^ c)
  (hmul : ∀ v w, ExpN (finiteDynkinPolynomial coeff ![v, w]) = ExpN v * ExpN w)

include hcoeff hmul in
/-- The ambient product of ideal exponentials remains in the ideal, with
an explicit polynomial coordinate bound in its own basis. -/
theorem ideal_product_coordinate_bound (C : ℝ) (hC : 0 ≤ C)
    (hbr : ∀ i j k, |bI.repr ⁅bI i, bI j⁆ k| ≤ C)
    {R : ℝ} (hR : 0 ≤ R) (u v : U)
    (hu : ‖bI.equivFun u‖ ≤ R) (hv : ‖bI.equivFun v‖ ≤ R) :
    ∃ w : U, ExpN (w : V) = ExpN (u : V) * ExpN (v : V) ∧
      ‖bI.equivFun w‖ ≤ sectionDynkinConstant (Fintype.card I) c C * (1 + R) ^ c := by
  let w := finiteDynkinPolynomial coeff ![u, v]
  have hvec : ∀ k : Fin 2, ‖bI.equivFun (![u, v] k)‖ ≤ R := by
    intro k
    fin_cases k
    · exact hu
    · exact hv
  refine ⟨w, ?_, ?_⟩
  · have he := finiteDynkinPolynomial_map U.incl coeff ![u, v]
    have hfun : (fun i : Fin 2 => U.incl (![u, v] i)) = ![(u : V), (v : V)] := by
      funext i
      fin_cases i <;> rfl
    rw [hfun] at he
    change ExpN (U.incl w) = _
    rw [he, hmul]
  · exact (norm_finiteDynkinPolynomial_le bI coeff hcoeff _ hC hR hbr hvec).trans_eq
      (by dsimp [sectionDynkinConstant] <;> norm_num <;> ring)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_PositiveWidthAbsorption
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.CartanFactorModel.realScaleProfile_apply _root_.OAI.PolycyclicRecognition.exponentialRescaleBasis_zero _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Absorption of small exponential errors by positive ideal widths -/

noncomputable section
namespace PolycyclicRecognition

open Module Filter
open scoped Topology

variable {V J : Type} [LieRing V] [LieAlgebra ℝ V] [Fintype J]

/-- Positive coordinate widths give a uniform exponential gain, without
any norm on the abstract Lie algebra. -/
theorem positive_width_coordinate_bound (b : Basis J ℝ V) (cost : J → ℝ)
    {lo r : ℝ} (hlo : ∀ j, lo ≤ cost j) (hr : 0 ≤ r) (v : V) :
    ‖(exponentialRescaleBasis b cost r).equivFun v‖ ≤
      Real.exp (-lo * r) * ‖b.equivFun v‖ := by
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg (Real.exp_pos _).le (norm_nonneg _))).mpr
  intro j
  change |(exponentialRescaleBasis b cost r).repr v j| ≤ _
  simp only [exponentialRescaleBasis, Basis.repr_unitsSMul, Units.smul_def,
    Units.val_inv_eq_inv_val, Units.val_mk0, smul_eq_mul, ← Real.exp_neg,
    abs_mul, abs_of_pos (Real.exp_pos _)]
  apply mul_le_mul _ (norm_le_pi_norm (b.equivFun v) j) (abs_nonneg _) (Real.exp_pos _).le
  exact Real.exp_le_exp.mpr (by nlinarith [hlo j])

/-- A fixed polynomial in a small exponential error is still absorbed by
positive widths. The threshold depends on the polynomial degree. -/
theorem eventually_positive_width_absorbs_polynomial
    (b : Basis J ℝ V) (cost : J → ℝ) {lo α K : ℝ} (p : ℕ)
    (hcost : ∀ j, lo ≤ cost j) (hK : 0 ≤ K) (hα : 0 ≤ α)
    (hgap : (p : ℝ) * α < lo) (ε : ℝ → ℝ) (hε : Tendsto ε atTop (𝓝 0)) :
    ∀ᶠ r in atTop, ∀ v : V,
      ‖b.equivFun v‖ ≤ K * (1 + Real.exp ((α + ε r) * r)) ^ p →
        ‖(exponentialRescaleBasis b cost r).equivFun v‖ ≤ 1 := by
  let θ := (lo - (p : ℝ) * α) / (2 * ((p : ℝ) + 1))
  have hp : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  have hθ : 0 < θ := div_pos (sub_pos.mpr hgap) (by positivity)
  have hθeq : θ * (2 * ((p : ℝ) + 1)) = lo - (p : ℝ) * α := by
    dsimp [θ]
    field_simp
  have hsmall : (p : ℝ) * (α + θ) - lo < 0 := by nlinarith
  have ht : Tendsto (fun r : ℝ => ((p : ℝ) * (α + θ) - lo) * r) atTop atBot :=
    (tendsto_const_mul_atBot_of_neg hsmall).mpr tendsto_id
  have hlim : Tendsto (fun r : ℝ => (K * 2 ^ p) *
      Real.exp (((p : ℝ) * (α + θ) - lo) * r)) atTop (𝓝 0) := by
    simpa only [mul_zero, Function.comp_apply] using (Real.tendsto_exp_atBot.comp ht).const_mul (K * 2 ^ p)
  filter_upwards [hε.eventually (eventually_lt_nhds hθ),
    hlim.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)),
    eventually_ge_atTop (0 : ℝ)] with r he hbound hr v hv
  have hexp : 1 ≤ Real.exp ((α + θ) * r) := Real.one_le_exp (by positivity)
  have hbase : 1 + Real.exp ((α + ε r) * r) ≤ 2 * Real.exp ((α + θ) * r) := by
    have hh : Real.exp ((α + ε r) * r) ≤ Real.exp ((α + θ) * r) :=
      Real.exp_le_exp.mpr (by nlinarith)
    linarith
  calc
    _ ≤ Real.exp (-lo * r) * ‖b.equivFun v‖ :=
      positive_width_coordinate_bound b cost hcost hr v
    _ ≤ Real.exp (-lo * r) * (K * (2 * Real.exp ((α + θ) * r)) ^ p) := by
      exact mul_le_mul_of_nonneg_left (hv.trans
        (mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (by positivity) hbase p) hK)) (Real.exp_pos _).le
    _ = (K * 2 ^ p) * Real.exp (((p : ℝ) * (α + θ) - lo) * r) := by
      rw [mul_pow, ← Real.exp_nat_mul]
      calc
        _ = (K * 2 ^ p) * (Real.exp (-lo * r) * Real.exp ((p : ℝ) * ((α + θ) * r))) := by ring
        _ = _ := by rw [← Real.exp_add]; congr 2; ring
    _ ≤ 1 := hbound.le

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

theorem HasSubexponentialUpperBound.mul {f g : ℝ → ℝ}
    (hf : HasSubexponentialUpperBound f) (hg : HasSubexponentialUpperBound g)
    (hf0 : ∀ᶠ r in atTop, 0 ≤ f r) :
    HasSubexponentialUpperBound (fun r => f r * g r) := by
  intro ε hε
  filter_upwards [hf (ε / 2) (by positivity), hg (ε / 2) (by positivity), hf0] with r hr hs h0
  calc
    f r * g r ≤ f r * Real.exp (ε / 2 * r) := mul_le_mul_of_nonneg_left hs h0
    _ ≤ Real.exp (ε / 2 * r) * Real.exp (ε / 2 * r) :=
      mul_le_mul_of_nonneg_right hr (Real.exp_pos _).le
    _ = Real.exp (ε * r) := by rw [← Real.exp_add]; congr 1; ring

end PolycyclicRecognition

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_SubexponentialOperations
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Powers, sums, minima and reciprocals of subexponential bounds -/

namespace PolycyclicRecognition

open Filter
open scoped Topology

theorem HasSubexponentialUpperBound.pow {f : ℝ → ℝ}
    (hf : HasSubexponentialUpperBound f) (hf0 : ∀ᶠ r in atTop, 0 ≤ f r) (n : ℕ) :
    HasSubexponentialUpperBound (fun r => f r ^ n) := by
  induction n with
  | zero => simpa using subexponential_upper_const 1
  | succ n ih =>
    simpa only [pow_succ] using ih.mul hf (hf0.mono (fun _ h => pow_nonneg h n))

theorem HasSubexponentialUpperBound.add {f g : ℝ → ℝ}
    (hf : HasSubexponentialUpperBound f) (hg : HasSubexponentialUpperBound g) :
    HasSubexponentialUpperBound (fun r => f r + g r) := by
  intro ε hε
  filter_upwards [hf (ε / 2) (by positivity), hg (ε / 2) (by positivity),
    subexponential_upper_const 2 (ε / 2) (by positivity)] with r hr hs htwo
  have he : Real.exp (ε * r) = Real.exp (ε / 2 * r) * Real.exp (ε / 2 * r) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [he]
  nlinarith [Real.exp_pos (ε / 2 * r)]

end PolycyclicRecognition

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_SectionErrorAbsorption
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.CartanFactorModel.realScaleProfile_apply _root_.OAI.PolycyclicRecognition.basisDynkinParameter_zero _root_.OAI.PolycyclicRecognition.dynkinRightTranslation_apply _root_.OAI.PolycyclicRecognition.dynkinRightTranslation_symm_apply _root_.OAI.PolycyclicRecognition.exponentialHomOfDynkin_apply_exp _root_.OAI.PolycyclicRecognition.exponentialQuotientSection_apply _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Small logarithmic errors in ideal-section coordinates -/

noncomputable section
namespace PolycyclicRecognition

open Module Set Filter
open scoped Topology

variable {V I J N Q : Type} [LieRing V] [LieAlgebra ℝ V] [Fintype I] [Fintype J]
  [Group N] [Group Q]
  (U : LieIdeal ℝ V) (bI : Basis I ℝ U) (bQ : Basis J ℝ (V ⧸ U.toSubmodule))
  (lift : J → V) (hlift : ∀ j, U.toSubmodule.mkQ (lift j) = bQ j)
  (ExpN : V → N) (ExpQ : (V ⧸ U.toSubmodule) → Q) (π : N →* Q)
  (hπ : ∀ v, π (ExpN v) = ExpQ (U.toSubmodule.mkQ v))
  (hinjQ : Function.Injective ExpQ) (hzeroQ : ExpQ 0 = 1)
  (hneg : ∀ v, ExpN (-v) = (ExpN v)⁻¹)
  {c : ℕ} (coeff : DynkinCoefficients c 2)
  (hcoeff : ∀ d w, |coeff d w| ≤ (2 : ℝ) ^ c)
  (hmul : ∀ v w, ExpN (finiteDynkinPolynomial coeff ![v, w]) = ExpN v * ExpN w)

local notation "B" => basisWithQuotientLifts U.toSubmodule bI bQ lift hlift
local notation "K" => sectionDynkinConstant (Fintype.card (I ⊕ J)) c

include hπ hinjQ hzeroQ hneg hcoeff hmul in
/-- The ideal error created by a pure section followed by a small ambient
error is absorbed by every strictly positive ideal width. -/
theorem section_error_absorbed (C : ℝ) (hC : 0 ≤ C)
    (hbr : ∀ i j k, |(B).repr ⁅B i, B j⁆ k| ≤ C)
    (cost : I → ℝ) {lo α : ℝ} (hcost : ∀ i, lo ≤ cost i) (hα : 0 ≤ α)
    (hgap : ((c * c : ℕ) : ℝ) * α < lo)
    (ε : ℝ → ℝ) (hε : Tendsto ε atTop (𝓝 0)) :
    ∀ᶠ r in atTop, ∀ (q : V ⧸ U.toSubmodule) (e : V),
      ‖bQ.equivFun q‖ ≤ Real.exp ((α + ε r) * r) →
      ‖(B).equivFun e‖ ≤ Real.exp ((α + ε r) * r) →
      ∃ (u : U) (q' : V ⧸ U.toSubmodule),
        ExpN (quotientLinearSection U bQ lift q) * ExpN e =
          ExpN (u : V) * ExpN (quotientLinearSection U bQ lift q') ∧
        ‖(exponentialRescaleBasis bI cost r).equivFun u‖ ≤ 1 := by
  have hK : 0 ≤ K C * (1 + K C) ^ c := by
    dsimp [sectionDynkinConstant]
    positivity
  have habs := eventually_positive_width_absorbs_polynomial bI cost (c * c)
    hcost hK hα hgap ε hε
  filter_upwards [habs] with r hr q e hq he
  obtain ⟨u, q', hfact, hu⟩ := section_error_factorization_bound U bI bQ lift hlift
    ExpN ExpQ π hπ hinjQ hzeroQ hneg coeff hcoeff hmul C hC hbr
    (Real.exp ((α + ε r) * r)) (Real.exp_pos _).le q e hq he
  exact ⟨u, q', hfact, hr u hu⟩

include hπ hinjQ hzeroQ hneg hcoeff hmul in
/-- One positive threshold works for all error envelopes. It depends only
on the least ideal width, the BCH degree and the fixed error exponent. -/
theorem exists_section_error_absorption_threshold (C : ℝ) (hC : 0 ≤ C)
    (hbr : ∀ i j k, |(B).repr ⁅B i, B j⁆ k| ≤ C)
    (cost : I → ℝ) {lo M : ℝ} (hlo : 0 < lo) (hcost : ∀ i, lo ≤ cost i)
    (hM : 0 < M) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
      ∀ ε : ℝ → ℝ, Tendsto ε atTop (𝓝 0) →
      ∀ᶠ r in atTop, ∀ (q : V ⧸ U.toSubmodule) (e : V),
        ‖bQ.equivFun q‖ ≤ Real.exp ((M * δ + ε r) * r) →
        ‖(B).equivFun e‖ ≤ Real.exp ((M * δ + ε r) * r) →
        ∃ (u : U) (q' : V ⧸ U.toSubmodule),
          ExpN (quotientLinearSection U bQ lift q) * ExpN e =
            ExpN (u : V) * ExpN (quotientLinearSection U bQ lift q') ∧
          ‖(exponentialRescaleBasis bI cost r).equivFun u‖ ≤ 1 := by
  let D := (((c * c : ℕ) : ℝ) + 1) * M
  have hD : 0 < D := by dsimp [D] <;> positivity
  let δ₀ := lo / (2 * D)
  have hδ₀ : 0 < δ₀ := div_pos hlo (by positivity)
  have heq : (2 * D) * δ₀ = lo := mul_div_cancel₀ lo (ne_of_gt (by positivity))
  refine ⟨δ₀, hδ₀, ?_⟩
  intro δ hδ hδle ε hε
  apply section_error_absorbed U bI bQ lift hlift ExpN ExpQ π hπ hinjQ hzeroQ hneg
    coeff hcoeff hmul C hC hbr cost hcost (mul_nonneg hM.le hδ.le) _ ε hε
  have hle := mul_le_mul_of_nonneg_left hδle hD.le
  have hp : (0 : ℝ) ≤ (c * c : ℕ) := Nat.cast_nonneg _
  have hsmall : ((c * c : ℕ) : ℝ) * (M * δ) ≤ D * δ := by
    dsimp [D]
    nlinarith [mul_pos hM hδ]
  nlinarith

/-- Polynomial losses in the adapted box comparison are subexponential. -/
theorem section_box_subexponential_envelope (C : ℝ) (hC : 0 ≤ C)
    (R : ℝ → ℝ) (hR : ∀ r, 0 ≤ R r) (hRsub : HasSubexponentialUpperBound R) :
    HasSubexponentialUpperBound (fun r => K C * (1 + R r) ^ c) := by
  have hp := ((subexponential_upper_const 1).add hRsub).pow
    (Eventually.of_forall (fun r => by linarith [hR r])) c
  exact (subexponential_upper_const (K C)).mul hp
    (Eventually.of_forall (fun _ => by dsimp [sectionDynkinConstant] <;> positivity))

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_SequenceRealExtension
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instNonemptyBases _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_nonempty _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Extending a scale sequence without regularity assumptions

The geometric box lemmas use real scales. Arbitrary data on a strictly
increasing scale sequence extend by zero off that sequence, preserving
vanishing errors and subexponential upper bounds.
-/

noncomputable section
namespace PolycyclicRecognition

open Filter
open scoped Topology

theorem sequenceRealExtension_apply (scale : ℕ → ℝ) (hs : StrictMono scale)
    (f : ℕ → ℝ) (n : ℕ) : sequenceRealExtension scale f (scale n) = f n := by
  classical
  have h : ∃ k, scale k = scale n := ⟨n, rfl⟩
  rw [sequenceRealExtension, dite_eq_left h, hs.injective h.choose_spec]

theorem sequenceRealExtension_nonneg (scale f : ℕ → ℝ) (hf : ∀ n, 0 ≤ f n) :
    ∀ r, 0 ≤ sequenceRealExtension scale f r := by
  classical
  intro r
  unfold sequenceRealExtension
  split_ifs with h
  · exact hf _
  · exact le_rfl

/-- A vanishing sequence of errors remains vanishing on the real scale. -/
theorem tendsto_sequenceRealExtension_zero (scale : ℕ → ℝ) (hs : StrictMono scale)
    (f : ℕ → ℝ) (hf : Tendsto f atTop (𝓝 0)) :
    Tendsto (sequenceRealExtension scale f) atTop (𝓝 0) := by
  classical
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hf ε hε
  refine ⟨scale N, ?_⟩
  intro r hr
  unfold sequenceRealExtension
  split_ifs with h
  · have hn : N ≤ h.choose := hs.le_iff_le.mp (by rwa [h.choose_spec])
    exact hN _ hn
  · simpa using hε

/-- A sequential subexponential envelope is enough for the real-scale
box estimates. Its zero extension imposes no restriction between samples. -/
theorem HasSubexponentialUpperBoundSeq.realExtension
    {scale f : ℕ → ℝ} (hf : HasSubexponentialUpperBoundSeq scale f)
    (hs : StrictMono scale) : HasSubexponentialUpperBound (sequenceRealExtension scale f) := by
  classical
  intro ε hε
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hf ε hε)
  filter_upwards [eventually_ge_atTop (scale N)] with r hr
  unfold sequenceRealExtension
  split_ifs with h
  · have hn : N ≤ h.choose := hs.le_iff_le.mp (by rwa [h.choose_spec])
    simpa only [h.choose_spec] using hN _ hn
  · exact (Real.exp_pos _).le

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

end PolycyclicRecognition.SupportDatum

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanBoxExponents
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instDecidableEqConeMixedWords _root_.OAI.PolycyclicRecognition.CartanWordModel.instFintypeConeMixedWords _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_nonempty _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact box exponents for the Cartan word model

The compact-template support equals the maximum of the determinant exponents
of the actual word boxes. This connects the Lie-algebra construction to the
Euclidean coordinate-volume formula.
-/

noncomputable section

namespace PolycyclicRecognition.CartanWordModel

open Module MeasureTheory
open scoped BigOperators

variable {L W : Type} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {H : LieSubalgebra ℝ L} [H.IsCartanSubalgebra] (M : CartanWordModel H)
  {n : ℕ} (T : TriangularAdjoint L n)
  (hunimod : ∀ x : L, LinearMap.trace ℝ L (LieAlgebra.ad ℝ L x) = 0)
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  (e : HeightSpace T.character ≃ₗ[ℝ] W)

set_option maxHeartbeats 1000000 in
/-- The determinant exponent of each basis is its template support sum. -/
theorem columnBasisWeight_boxCost (E : Set W) (β : M.Bases) :
    columnBasisWeight (M.boxCost T hunimod e E) β.val =
      (M.supportIn T hunimod e).basisTemplateSupport E β := by
  unfold columnBasisWeight boxCost
  rw [sum_bracketWordExponent]
  rfl

set_option maxHeartbeats 1000000 in
/-- Maximizing the finite word-box determinant gives exactly `P(E)`. -/
theorem exists_maximizing_box_basis
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (E : Set W) : ∃ β : M.Bases,
      IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
        (M.boxCost T hunimod e E) β.val ∧
      columnBasisWeight (M.boxCost T hunimod e E) β.val =
        (M.supportIn T hunimod e).templateSupport E := by
  obtain ⟨β, hβ⟩ := exists_maximizing_wordBasis M.letter M.wordList b₀
    (M.boxCost T hunimod e E)
  refine ⟨β, hβ, le_antisymm ?_ ?_⟩
  · rw [M.columnBasisWeight_boxCost]
    exact (M.supportIn T hunimod e).basisTemplateSupport_le E β
  · apply (M.supportIn T hunimod e).templateSupport_le
    intro γ
    rw [← M.columnBasisWeight_boxCost T hunimod e E γ]
    exact hβ.2 γ.val (wordBasis_det_ne_zero M.letter M.wordList b₀ γ)

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_TemplateBoxEnvelopes
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instDecidableEqConeMixedWords _root_.OAI.PolycyclicRecognition.CartanWordModel.instFintypeConeMixedWords _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finite_templateSymmetryGroup _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.instFiniteRootOffsetConeIndex _root_.OAI.PolycyclicRecognition.instFiniteSubtypeLinearEquivRealIdMemSubgroupLinearSupportSymmetryGroup _root_.OAI.PolycyclicRecognition.instNonemptyRootOffsetConeIndex _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A single box envelope for vanishing template thickenings -/

noncomputable section
namespace PolycyclicRecognition

open Module LieModule Set Filter Metric
open scoped Topology Pointwise

namespace SupportDatum

variable {W I B : Type} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [FiniteDimensional ℝ W] [Fintype I] [Fintype B] [Nonempty B]
  (D : SupportDatum W I B)

omit [Nonempty B] in
/-- Thickening the height template changes each weight by at most its
operator norm times the thickening radius. -/
theorem weightSupport_thickening_le {E : Set W} (hE : IsCompact E) (hne : E.Nonempty)
    {ε : ℝ} (hε : 0 ≤ ε) (i : I) :
    D.weightSupport (E + closedBall 0 ε) i ≤
      D.weightSupport E i + ‖(D.weight i).toContinuousLinearMap‖ * ε := by
  have hne' : (E + closedBall (0 : W) ε).Nonempty := by
    obtain ⟨x, hx⟩ := hne
    exact ⟨x + 0, add_mem_add hx (by simpa using hε)⟩
  apply D.weightSupport_le_of_nearby (hE.add (isCompact_closedBall 0 ε)) hne' hE
  rintro x ⟨y, hy, z, hz, rfl⟩
  refine ⟨y, hy, ?_⟩
  simpa only [add_sub_cancel_left, mem_closedBall, dist_zero_right] using hz

end SupportDatum

theorem bracketWordExponent_le_add_of_le {I : Type} [Fintype I] [DecidableEq I]
    (s t u : I → ℝ) (h : ∀ i, s i ≤ t i + u i) (w : FreeMagma I) :
    bracketWordExponent s w ≤ bracketWordExponent t w + bracketWordExponent u w := by
  rw [← bracketWordExponent_add]
  exact Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (h i) (Nat.cast_nonneg _))

namespace CartanWordModel

variable {L W : Type} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {H : LieSubalgebra ℝ L} [H.IsCartanSubalgebra] (M : CartanWordModel H)
  {a : ℕ} (T : TriangularAdjoint L a)
  (hunimod : ∀ x : L, LinearMap.trace ℝ L (LieAlgebra.ad ℝ L x) = 0)
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)

/-- The finite word list has one constant for all compact templates. -/
theorem exists_boxCost_thickening_constant :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {E : Set W}, IsCompact E → E.Nonempty →
      ∀ {ε : ℝ}, 0 ≤ ε → ∀ w : M.wordList,
        M.boxCost T hunimod eW (E + closedBall 0 ε) w ≤
          M.boxCost T hunimod eW E w + C * ε := by
  let D := M.supportIn T hunimod eW
  let c := fun w : M.wordList =>
    ∑ i, (bracketWordCount (w : FreeMagma (Fin M.letterCount)) i : ℝ) *
      ‖(D.weight i).toContinuousLinearMap‖
  let C := ∑ w, c w
  have hc (w : M.wordList) : 0 ≤ c w :=
    Finset.sum_nonneg (fun i _ => mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _))
  have hC : 0 ≤ C := Finset.sum_nonneg (fun w _ => hc w)
  have hcC (w : M.wordList) : c w ≤ C :=
    Finset.single_le_sum (fun w _ => hc w) (Finset.mem_univ w)
  refine ⟨C, hC, ?_⟩
  intro E hE hne ε hε w
  have hh := bracketWordExponent_le_add_of_le
    (D.weightSupport (E + closedBall 0 ε)) (D.weightSupport E)
    (fun i => ‖(D.weight i).toContinuousLinearMap‖ * ε)
    (D.weightSupport_thickening_le hE hne hε) w.val
  have he : bracketWordExponent (fun i => ‖(D.weight i).toContinuousLinearMap‖ * ε) w.val =
      c w * ε := by simp only [bracketWordExponent, c, Finset.sum_mul, mul_assoc]
  change bracketWordExponent (D.weightSupport (E + closedBall 0 ε)) w.val ≤
    bracketWordExponent (D.weightSupport E) w.val + C * ε
  rw [he] at hh
  exact hh.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_right (hcC w) hε))

end CartanWordModel
end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanRootWidths
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instDecidableEqConeMixedWords _root_.OAI.PolycyclicRecognition.CartanWordModel.instFintypeConeMixedWords _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finite_templateSymmetryGroup _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.instFiniteRootOffsetConeIndex _root_.OAI.PolycyclicRecognition.instFiniteSubtypeLinearEquivRealIdMemSubgroupLinearSupportSymmetryGroup _root_.OAI.PolycyclicRecognition.instNonemptyRootOffsetConeIndex _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.CartanFactorModel.heightRay_zero _root_.OAI.PolycyclicRecognition.CartanFactorModel.realScaleProfile_apply _root_.OAI.PolycyclicRecognition.CartanFactorModel.sampledProbeProfile_apply _root_.OAI.PolycyclicRecognition.bracketWordDifferential_mul _root_.OAI.PolycyclicRecognition.cartanWeightDerivation_apply_root _root_.OAI.PolycyclicRecognition.exponentialRescaleBasis_zero _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.nilshadowWeightDerivation_symm _root_.OAI.PolycyclicRecognition.nilshadowWeightOperator_symm _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Root-space widths inside actual word boxes

A nonzero coordinate of a root vector can occur only at a word of the same
weight. Its word exponent dominates the support of that root. Consequently
rescaling a letter-root vector never enlarges its coordinates in the scaled
word box. This includes zero-weight bracket directions.
-/

noncomputable section

namespace PolycyclicRecognition

open Module LieModule LieAlgebra
open scoped BigOperators

set_option maxHeartbeats 1000000 in
private theorem basis_repr_map_of_diagonal
    {V J : Type} [AddCommGroup V] [Module ℝ V] [DecidableEq J]
    (b : Basis J ℝ V) (f : V →ₗ[ℝ] V) (a : J → ℝ)
    (hf : ∀ j, f (b j) = a j • b j) (v : V) (j : J) :
    b.repr (f v) j = a j * b.repr v j := by
  have he : (b.coord j).comp f = a j • b.coord j := by
    apply b.ext
    intro i
    simp only [LinearMap.comp_apply, hf, map_smul, smul_eq_mul,
      Basis.coord_apply, Basis.repr_self_apply, LinearMap.smul_apply]
    split_ifs with hij
    · subst i; rfl
    · simp
  exact congrArg (fun g : V →ₗ[ℝ] ℝ => g v) he

namespace CartanWordModel

variable {L W : Type} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {H : LieSubalgebra ℝ L} [H.IsCartanSubalgebra] (M : CartanWordModel H)
  {n : ℕ} (T : TriangularAdjoint L n)

include T

set_option maxHeartbeats 1000000 in
/-- A root vector has nonzero word coordinates only in its own weight. -/
theorem wordWeight_eq_of_repr_ne_zero (β : M.Bases) (χ : Weight ℝ H L)
    (v : cartanRootIdeal H) (hv : (v : L) ∈ rootSpace H χ)
    (j : Fin (finrank ℝ (cartanRootIdeal H)))
    (hj : (WordBasisSelections.basis M.letter M.wordList β).repr v j ≠ 0) (h : H) :
    bracketWordExponent (fun i => M.weight i h) (β.val j) = χ h := by
  let b := WordBasisSelections.basis M.letter M.wordList β
  let F := cartanIdealWeightDilation T H h
  have hf (k : Fin (finrank ℝ (cartanRootIdeal H))) :
      F (b k) = Real.exp (bracketWordExponent (fun i => M.weight i h) (β.val k)) • b k := by
    have hk := WordBasisSelections.eval_words M.letter M.wordList β k
    change evalBracketWord M.letter (β.val k) = b k at hk
    rw [← hk]
    exact M.idealWeightDilation_word T h (β.val k)
  have hv' : F v = Real.exp (χ h) • v := by
    apply Subtype.ext
    exact cartanWeightScale_apply_root T H h χ hv
  have hc := basis_repr_map_of_diagonal b F.toLinearEquiv.toLinearMap
    (fun k => Real.exp (bracketWordExponent (fun i => M.weight i h) (β.val k))) hf v j
  change b.repr (F v) j = _ at hc
  rw [hv', map_smul, Finsupp.smul_apply, smul_eq_mul] at hc
  exact Real.exp_injective (mul_right_cancel₀ hj hc).symm

variable (hunimod : ∀ x : L, LinearMap.trace ℝ L (ad ℝ L x) = 0)
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)

set_option maxHeartbeats 1000000 in
/-- The exponent of a word of a letter's weight is at least that letter's
support, since separate letter supports dominate evaluation at one point. -/
theorem letter_support_le_wordCost {E : Set W} (hE : IsCompact E) (hne : E.Nonempty)
    (i : Fin M.letterCount) (z : M.wordList)
    (hz : ∀ h : H, bracketWordExponent (fun k => M.weight k h) z = M.weight i h) :
    (M.supportIn T hunimod eW).weightSupport E i ≤ M.boxCost T hunimod eW E z := by
  let D := M.supportIn T hunimod eW
  obtain ⟨w, hw, hs⟩ := D.exists_weightSupport_point hE hne i
  have he := hz (cartanHeightSection T H (eW.symm w))
  change bracketWordExponent (fun k => D.weight k w) z = D.weight i w at he
  change D.weightSupport E i ≤ bracketWordExponent (D.weightSupport E) z
  rw [hs, ← he]
  exact Finset.sum_le_sum (fun k _ => mul_le_mul_of_nonneg_left
    (D.weight_le_weightSupport hE hw k) (Nat.cast_nonneg _))

set_option maxHeartbeats 1000000 in
/-- Nonzero coordinates of an arbitrary vector in a letter's root space
occur only at word exponents dominating that letter's support. -/
theorem letter_support_le_wordCost_of_repr_ne_zero
    {E : Set W} (hE : IsCompact E) (hne : E.Nonempty) (β : M.Bases)
    (i : Fin M.letterCount) (v : cartanRootIdeal H)
    (hv : (v : L) ∈ rootSpace H (M.weight i))
    (j : Fin (finrank ℝ (cartanRootIdeal H)))
    (hj : (WordBasisSelections.basis M.letter M.wordList β).repr v j ≠ 0) :
    (M.supportIn T hunimod eW).weightSupport E i ≤ M.boxCost T hunimod eW E (β.val j) :=
  M.letter_support_le_wordCost T hunimod eW hE hne i (β.val j)
    (M.wordWeight_eq_of_repr_ne_zero T β (M.weight i) v hv j hj)

set_option maxHeartbeats 1000000 in
/-- The normalized coordinates of a letter-root vector are bounded by its
unscaled coordinates, uniformly over templates and scales. -/
theorem norm_scaled_root_le {E : Set W} (hE : IsCompact E) (hne : E.Nonempty)
    (β : M.Bases) (i : Fin M.letterCount) (v : cartanRootIdeal H)
    (hv : (v : L) ∈ rootSpace H (M.weight i)) {r : ℝ} (hr : 0 ≤ r) :
    ‖(M.boxBasis T hunimod eW E β r).equivFun
      (Real.exp (r * (M.supportIn T hunimod eW).weightSupport E i) • v)‖ ≤
        ‖(WordBasisSelections.basis M.letter M.wordList β).equivFun v‖ := by
  let b := WordBasisSelections.basis M.letter M.wordList β
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
  intro j
  change ‖(M.boxBasis T hunimod eW E β r).repr
    (Real.exp (r * (M.supportIn T hunimod eW).weightSupport E i) • v) j‖ ≤ ‖b.equivFun v‖
  have hb : |b.repr v j| ≤ ‖b.equivFun v‖ := by
    simpa only [Real.norm_eq_abs, Basis.equivFun_apply] using norm_le_pi_norm (b.equivFun v) j
  simp only [boxBasis, exponentialRescaleBasis, Basis.repr_unitsSMul, map_smul,
    Finsupp.smul_apply, Units.smul_def, Units.val_inv_eq_inv_val, Units.val_mk0,
    smul_eq_mul, Real.norm_eq_abs]
  change |Real.exp (r * (M.supportIn T hunimod eW).weightSupport E i) *
    ((Real.exp (r * M.boxCost T hunimod eW E (β.val j)))⁻¹ * b.repr v j)| ≤ _
  rw [← mul_assoc, mul_comm (Real.exp (r * (M.supportIn T hunimod eW).weightSupport E i))]
  by_cases hj : b.repr v j = 0
  · simp only [hj, mul_zero, abs_zero]
    exact norm_nonneg _
  · have hc := M.letter_support_le_wordCost_of_repr_ne_zero T hunimod eW hE hne β i v hv j hj
    have hexp : Real.exp (r * ((M.supportIn T hunimod eW).weightSupport E i -
        M.boxCost T hunimod eW E (β.val j))) ≤ 1 :=
      Real.exp_le_one_iff.mpr (mul_nonpos_of_nonneg_of_nonpos hr (sub_nonpos.mpr hc))
    rw [← Real.exp_neg, ← Real.exp_add]
    have he : -(r * M.boxCost T hunimod eW E (β.val j)) +
        r * (M.supportIn T hunimod eW).weightSupport E i =
        r * ((M.supportIn T hunimod eW).weightSupport E i -
          M.boxCost T hunimod eW E (β.val j)) := by ring
    rw [he, abs_mul, abs_of_pos (Real.exp_pos _)]
    exact (mul_le_mul_of_nonneg_right hexp (abs_nonneg _)).trans (by simpa using hb)

set_option maxHeartbeats 1000000 in
omit T hunimod eW [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] in
/-- The finitely many unscaled word bases have one common comparison
constant with fixed coordinates on a nonzero root space. -/
theorem exists_root_wordBasis_bound (χ : LieModule.Weight ℝ H L) (hχ : χ.IsNonZero) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (β : M.Bases) (v : LieAlgebra.rootSpace H χ),
      ‖(WordBasisSelections.basis M.letter M.wordList β).equivFun
        (rootInIdeal χ hχ v)‖ ≤
      C * ‖(Module.finBasis ℝ (LieAlgebra.rootSpace H χ)).equivFun v‖ := by
  let a := (Module.finBasis ℝ (LieAlgebra.rootSpace H χ)).equivFun
  let f := fun β : M.Bases =>
    (((WordBasisSelections.basis M.letter M.wordList β).equivFun.toLinearMap.comp
      (rootInIdeal χ hχ)).comp a.symm.toLinearMap).toContinuousLinearMap
  let C := ∑ β : M.Bases, ‖f β‖
  have hC : 0 ≤ C := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  refine ⟨C, hC, ?_⟩
  intro β v
  have hβ : ‖f β‖ ≤ C := Finset.single_le_sum (fun _ _ => norm_nonneg _) (Finset.mem_univ β)
  have he : f β (a v) = (WordBasisSelections.basis M.letter M.wordList β).equivFun
      (rootInIdeal χ hχ v) := by
    change (WordBasisSelections.basis M.letter M.wordList β).equivFun
      (rootInIdeal χ hχ (a.symm (a v))) = _
    rw [LinearEquiv.symm_apply_apply]
  rw [← he]
  exact (ContinuousLinearMap.le_opNorm (f β) (a v)).trans
    (mul_le_mul_of_nonneg_right hβ (norm_nonneg _))

end CartanWordModel
end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanBoxMaps
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instDecidableEqConeMixedWords _root_.OAI.PolycyclicRecognition.CartanWordModel.instFintypeConeMixedWords _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
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

namespace CartanWordModel

variable [FiniteDimensional ℝ L]
  {H : LieSubalgebra ℝ L} [H.IsCartanSubalgebra] (M : CartanWordModel H)
  {n : ℕ} (T : TriangularAdjoint L n)
  (hunimod : ∀ x : L, LinearMap.trace ℝ L (LieAlgebra.ad ℝ L x) = 0)
  {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)

set_option maxHeartbeats 1000000 in
omit T hunimod eW [FiniteDimensional ℝ L] [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] in
theorem word_degrees_le (w : M.wordList) :
    bracketWordNodes (w : FreeMagma (Fin M.letterCount)) ≤ M.wordDegreeBound ∧
      bracketWordLength (w : FreeMagma (Fin M.letterCount)) ≤ M.wordDegreeBound := by
  have h : bracketWordLength (w : FreeMagma (Fin M.letterCount)) ≤ M.wordDegreeBound :=
    Finset.single_le_sum (f := fun w : M.wordList => bracketWordLength (w : FreeMagma (Fin M.letterCount)))
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ w)
  exact ⟨(by rw [bracketWordLength_eq_nodes_add_one] at h; omega), h⟩

end CartanWordModel
end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_NilpotentExponential
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Exponential coordinates for upper unipotent matrices

The analytic matrix exponential is a finite polynomial on nilpotent matrices.
This bridges the ordered-product bounds to actual exponential increments,
rather than a separately stipulated polynomial group law.
-/

namespace PolycyclicRecognition

open scoped BigOperators

section Algebra

variable {A : Type} [NormedRing A] [NormedAlgebra ℝ A]

/-- The polynomial exponential gives a uniform increment bound on any fixed
bounded set of nilpotent logarithms. -/
theorem norm_exp_sub_one_le_of_pow_eq_zero [NormOneClass A]
    (x : A) {c : ℕ} (hx : x ^ (c + 1) = 0)
    {M : ℝ} (hM : 0 ≤ M) (hbound : ‖x‖ ≤ M) :
    ‖NormedSpace.exp x - 1‖ ≤ (c : ℝ) * (1 + M) ^ c := by
  rw [exp_eq_finite_sum_of_pow_eq_zero x hx, Finset.sum_range_succ']
  simp only [Nat.factorial_zero, Nat.cast_one, inv_one, pow_zero, one_smul,
    add_sub_cancel_right]
  calc
    _ ≤ ∑ k ∈ Finset.range c, ‖((k + 1).factorial : ℝ)⁻¹ • x ^ (k + 1)‖ := norm_sum_le _ _
    _ ≤ ∑ _k ∈ Finset.range c, (1 + M) ^ c := by
      apply Finset.sum_le_sum
      intro k hk
      have hf : (1 : ℝ) ≤ (k + 1).factorial := by
        exact_mod_cast Nat.succ_le_of_lt (Nat.factorial_pos (k + 1))
      have hi : ‖((k + 1).factorial : ℝ)⁻¹‖ ≤ 1 := by
        rw [Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (by linarith))]
        exact inv_le_one_of_one_le₀ hf
      calc
        _ = ‖((k + 1).factorial : ℝ)⁻¹‖ * ‖x ^ (k + 1)‖ := norm_smul _ _
        _ ≤ 1 * ‖x ^ (k + 1)‖ := mul_le_mul_of_nonneg_right hi (norm_nonneg _)
        _ ≤ (1 + M) ^ (k + 1) := by
          rw [one_mul]
          exact (norm_pow_le _ _).trans
            (pow_le_pow_left₀ (norm_nonneg _) (by linarith) (k + 1))
        _ ≤ (1 + M) ^ c := pow_le_pow_right₀ (by linarith) (Finset.mem_range.mp hk)
    _ = _ := by simp

end Algebra

end PolycyclicRecognition

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_NilpotentFlow
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Nilpotent corrections in a contracting weight flow

The nilpotent part of the infinitesimal action gives a polynomial bound
for its actual analytic exponential. Coupled with scalar exponential
contraction, it gives logarithmic metric distortion of the weight chart.
-/

noncomputable section

namespace PolycyclicRecognition

/-- The actual exponential of a nilpotent operator has polynomial growth
in its real parameter, with an explicit uniform coefficient. -/
theorem norm_exp_smul_nilpotent_le
    {A : Type} [NormedRing A] [NormedAlgebra ℝ A] [NormOneClass A]
    (N : A) {c : ℕ} (hN : N ^ (c + 1) = 0) {t : ℝ} (ht : 0 ≤ t) :
    ‖NormedSpace.exp (t • N)‖ ≤
      ((c : ℝ) + 1) * (1 + ‖N‖) ^ c * (1 + t) ^ c := by
  have hpow : (t • N) ^ (c + 1) = 0 := by simp [smul_pow, hN]
  have hbound : ‖NormedSpace.exp (t • N) - 1‖ ≤
      (c : ℝ) * (1 + t * ‖N‖) ^ c := by
    apply norm_exp_sub_one_le_of_pow_eq_zero _ hpow (by positivity)
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht]
  have hbase : 1 + t * ‖N‖ ≤ (1 + ‖N‖) * (1 + t) := by
    nlinarith [norm_nonneg N]
  have hpoly : (1 + t * ‖N‖) ^ c ≤ (1 + ‖N‖) ^ c * (1 + t) ^ c := by
    simpa only [mul_pow] using pow_le_pow_left₀ (by positivity) hbase c
  have hone : 1 ≤ (1 + ‖N‖) ^ c * (1 + t) ^ c :=
    one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by linarith [norm_nonneg N]))
      (one_le_pow₀ (by linarith))
  calc
    ‖NormedSpace.exp (t • N)‖ ≤ ‖NormedSpace.exp (t • N) - 1‖ + ‖(1 : A)‖ :=
      norm_le_norm_sub_add _ _
    _ ≤ (c : ℝ) * (1 + t * ‖N‖) ^ c + 1 := by simpa only [norm_one] using add_le_add hbound le_rfl
    _ ≤ (c : ℝ) * ((1 + ‖N‖) ^ c * (1 + t) ^ c) +
        ((1 + ‖N‖) ^ c * (1 + t) ^ c) := by
      exact add_le_add (mul_le_mul_of_nonneg_left hpoly (Nat.cast_nonneg _)) hone
    _ = _ := by ring

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

variable {L : Type} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  (H : LieSubalgebra ℝ L) [H.IsCartanSubalgebra] (χ : Weight ℝ H L)

local instance instNontrivialSubtypeMemLieSubmoduleRealLieSubalgebraRootSpaceCoeWeight_solutions : Nontrivial (rootSpace H χ) :=
  (LieSubmodule.nontrivial_iff_ne_bot ℝ H L).mpr χ.genWeightSpace_ne_bot

attribute [local instance] OAI.PolycyclicRecognition.instNormedAddCommGroupSubtypeMemLieSubmoduleRealLieSubalgebraRootSpaceCoeWeight_solutions
attribute [local instance] OAI.PolycyclicRecognition.instNormedSpaceRealSubtypeMemLieSubmoduleLieSubalgebraRootSpaceCoeWeight_solutions
set_option maxHeartbeats 1000000 in
/-- The nilpotence exponent is uniformly bounded by the root-space dimension. -/
theorem rootAction_residual_pow_eq_zero (h : H) :
    (rootAction H χ h - χ h • 1) ^ finrank ℝ (rootSpace H χ) = 0 := by
  let A : Module.End ℝ (rootSpace H χ) := toEnd ℝ H (rootSpace H χ) h - χ h • 1
  have hn : _root_.IsNilpotent A := isNilpotent_toEnd_sub_algebraMap L (χ : H → ℝ) h
  have hp : A ^ finrank ℝ (rootSpace H χ) = 0 := by
    simpa only [hn.charpoly_eq_X_pow_finrank, map_pow, Polynomial.aeval_X] using
      A.aeval_self_charpoly
  have hm := congrArg (Module.End.toContinuousLinearMap (𝕜 := ℝ) (rootSpace H χ)) hp
  simpa only [A, map_pow, map_sub, map_smul, map_one, map_zero, rootAction] using hm

set_option maxHeartbeats 1000000 in
/-- One polynomial controls the residual operator for every Cartan parameter. -/
theorem exists_rootResidual_exp_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ h : H,
      ‖NormedSpace.exp (rootAction H χ h - χ h • 1)‖ ≤
        C * (1 + ‖(Module.finBasis ℝ H).equivFun h‖) ^ finrank ℝ (rootSpace H χ) := by
  let d := finrank ℝ (rootSpace H χ)
  let b := Module.finBasis ℝ H
  let f := ((rootResidualLinear H χ).comp b.equivFun.symm.toLinearMap).toContinuousLinearMap
  let K := ‖f‖
  have hK : 0 ≤ K := norm_nonneg f
  refine ⟨((d : ℝ) + 1) * (1 + K) ^ d * 2 ^ d, by positivity, ?_⟩
  intro h
  have hb : ‖rootAction H χ h - χ h • 1‖ ≤ K * ‖(Module.finBasis ℝ H).equivFun h‖ := by
    have hf : f (b.equivFun h) = rootAction H χ h - χ h • 1 := by
      change rootResidualLinear H χ (b.equivFun.symm (b.equivFun h)) = _
      rw [LinearEquiv.symm_apply_apply]
      rfl
    simpa only [hf] using f.le_opNorm (b.equivFun h)
  have hp : (rootAction H χ h - χ h • 1) ^ (d + 1) = 0 := by
    rw [pow_succ, rootAction_residual_pow_eq_zero, zero_mul]
  have he := norm_exp_smul_nilpotent_le (rootAction H χ h - χ h • 1) hp (t := 1) zero_le_one
  simp only [one_smul, one_add_one_eq_two] at he
  calc
    _ ≤ ((d : ℝ) + 1) * (1 + ‖rootAction H χ h - χ h • 1‖) ^ d * 2 ^ d := he
    _ ≤ ((d : ℝ) + 1) * ((1 + K) * (1 + ‖(Module.finBasis ℝ H).equivFun h‖)) ^ d * 2 ^ d := by
      gcongr
      nlinarith [norm_nonneg (b.equivFun h)]
    _ = _ := by rw [mul_pow]; ring

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanResidualBounds
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instDecidableEqConeMixedWords _root_.OAI.PolycyclicRecognition.CartanWordModel.instFintypeConeMixedWords _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
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
local instance instNontrivialSubtypeMemLieSubmoduleRealLieSubalgebraRootSpaceCoeWeight_solutions_1_rbdbbfb_1 : Nontrivial (rootSpace H χ) :=
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

set_option maxHeartbeats 1000000 in
/-- A common polynomial bound in every unscaled word basis. -/
theorem exists_residual_root_wordBasis_bound (M : CartanWordModel H) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (β : M.Bases) (h : H) (v : rootSpace H χ),
      ‖(WordBasisSelections.basis M.letter M.wordList β).equivFun
        (cartanIdealResidualAutomorphism T H h (CartanWordModel.rootInIdeal χ hχ v))‖ ≤
      C * (1 + ‖(Module.finBasis ℝ H).equivFun h‖) ^ finrank ℝ (rootSpace H χ) *
        ‖(rootCoordinates H χ) v‖ := by
  obtain ⟨C₁, hC₁, h₁⟩ := M.exists_root_wordBasis_bound χ hχ
  obtain ⟨C₂, hC₂, h₂⟩ := exists_rootResidual_exp_bound H χ
  refine ⟨C₁ * C₂, mul_nonneg hC₁ hC₂.le, ?_⟩
  intro β h v
  rw [← rootInIdeal_residual_exp T H χ hχ h v]
  apply (h₁ β _).trans
  change C₁ * ‖(NormedSpace.exp (rootAction H χ h - χ h • 1)) v‖ ≤ _
  calc
    _ ≤ C₁ * (‖NormedSpace.exp (rootAction H χ h - χ h • 1)‖ * ‖v‖) :=
      mul_le_mul_of_nonneg_left (ContinuousLinearMap.le_opNorm _ _) hC₁
    _ ≤ C₁ * (C₂ * (1 + ‖(Module.finBasis ℝ H).equivFun h‖) ^
        finrank ℝ (rootSpace H χ) * ‖v‖) := by
      gcongr
      exact h₂ h
    _ = _ := by
      have hn : ‖v‖ = ‖(rootCoordinates H χ) v‖ := rfl
      rw [hn]
      ring

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanConjugationBounds
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instDecidableEqConeMixedWords _root_.OAI.PolycyclicRecognition.CartanWordModel.instFintypeConeMixedWords _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform box bounds for the actual residual Cartan action

The finitely many letter-root bounds give one polynomial in the Cartan
coordinate norm. Propagating this through bracket words gives the residual
part of the box-conjugation estimate, without an assumed operator bound.
-/

noncomputable section

namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule
open scoped BigOperators Manifold

variable {L : Type} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {H : LieSubalgebra ℝ L} [H.IsCartanSubalgebra] (M : CartanWordModel H)
  {n : ℕ} (T : TriangularAdjoint L n)

set_option maxHeartbeats 1000000 in
/-- A polynomial bound on one letter, uniform over the finite word bases. -/
theorem exists_residual_letter_bound (i : Fin M.letterCount) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (β : M.Bases) (h : H),
      ‖(WordBasisSelections.basis M.letter M.wordList β).equivFun
        (cartanIdealResidualAutomorphism T H h (M.letter i))‖ ≤
      C * (1 + ‖(Module.finBasis ℝ H).equivFun h‖) ^
        finrank ℝ (rootSpace H (M.weight i)) := by
  let v : rootSpace H (M.weight i) := ⟨(M.letter i : L), M.letter_root i⟩
  have he : rootInIdeal (M.weight i) (M.weight_nonzero i) v = M.letter i := Subtype.ext rfl
  obtain ⟨C, hC, hb⟩ := exists_residual_root_wordBasis_bound T H
    (M.weight i) (M.weight_nonzero i) M
  refine ⟨C * ‖(rootCoordinates H (M.weight i)) v‖, mul_nonneg hC (norm_nonneg _), ?_⟩
  intro β h
  have hh := hb β h v
  rw [he] at hh
  simpa only [mul_assoc, mul_comm, mul_left_comm] using hh

set_option maxHeartbeats 1000000 in
/-- One polynomial simultaneously bounds every letter image in every
unscaled word basis. -/
theorem exists_residual_letters_bound :
    ∃ (C : ℝ) (p : ℕ), 0 ≤ C ∧ ∀ (β : M.Bases) (h : H) (i : Fin M.letterCount),
      ‖(WordBasisSelections.basis M.letter M.wordList β).equivFun
        (cartanIdealResidualAutomorphism T H h (M.letter i))‖ ≤
      C * (1 + ‖(Module.finBasis ℝ H).equivFun h‖) ^ p := by
  choose C hC hb using M.exists_residual_letter_bound T
  let p := ∑ i : Fin M.letterCount, finrank ℝ (rootSpace H (M.weight i))
  let A := ∑ i, C i
  have hA : 0 ≤ A := Finset.sum_nonneg (fun i _ => hC i)
  refine ⟨A, p, hA, ?_⟩
  intro β h i
  apply (hb i β h).trans
  have hi : C i ≤ A := Finset.single_le_sum (fun i _ => hC i) (Finset.mem_univ i)
  have hd : finrank ℝ (rootSpace H (M.weight i)) ≤ p :=
    Finset.single_le_sum (f := fun i => finrank ℝ (rootSpace H (M.weight i)))
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  exact mul_le_mul hi (pow_le_pow_right₀ (by linarith [norm_nonneg ((Module.finBasis ℝ H).equivFun h)]) hd)
    (pow_nonneg (by positivity) _) hA

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanControlledAction
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instDecidableEqConeMixedWords _root_.OAI.PolycyclicRecognition.CartanWordModel.instFintypeConeMixedWords _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finite_templateSymmetryGroup _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.instFiniteRootOffsetConeIndex _root_.OAI.PolycyclicRecognition.instFiniteSubtypeLinearEquivRealIdMemSubgroupLinearSupportSymmetryGroup _root_.OAI.PolycyclicRecognition.instNonemptyRootOffsetConeIndex _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.CartanFactorModel.heightRay_zero _root_.OAI.PolycyclicRecognition.CartanFactorModel.realScaleProfile_apply _root_.OAI.PolycyclicRecognition.CartanFactorModel.sampledProbeProfile_apply _root_.OAI.PolycyclicRecognition.bracketWordDifferential_mul _root_.OAI.PolycyclicRecognition.cartanWeightDerivation_apply_root _root_.OAI.PolycyclicRecognition.exponentialRescaleBasis_zero _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.nilshadowWeightDerivation_symm _root_.OAI.PolycyclicRecognition.nilshadowWeightOperator_symm _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Cartan actions whose heights stay in a template

The normalized width of a root controls every exponential whose exponent is
below that width. Consequently a Cartan action with height in the scaled
template sends a fixed coordinate box into the template box with polynomial
loss in its Cartan logarithm. This is the increment estimate for controlled
paths.
-/

noncomputable section

namespace PolycyclicRecognition

open Module LieAlgebra LieModule
open scoped BigOperators Manifold

set_option maxHeartbeats 1000000 in
private theorem norm_map_between_bases_le
    {V I J : Type} [AddCommGroup V] [Module ℝ V] [Fintype I] [Fintype J]
    (a : Basis I ℝ V) (b : Basis J ℝ V) (F : V →ₗ[ℝ] V) {K : ℝ}
    (hF : ∀ i, ‖b.equivFun (F (a i))‖ ≤ K) (v : V) :
    ‖b.equivFun (F v)‖ ≤ (Fintype.card I : ℝ) * K * ‖a.equivFun v‖ := by
  conv_lhs => rw [← a.sum_repr v]
  rw [map_sum, map_sum]
  apply (norm_sum_le _ _).trans
  calc
    (∑ i, ‖b.equivFun (F (a.repr v i • a i))‖) ≤
        ∑ _i : I, ‖a.equivFun v‖ * K := by
      apply Finset.sum_le_sum
      intro i _
      rw [map_smul, map_smul, norm_smul, Real.norm_eq_abs]
      exact mul_le_mul (norm_le_pi_norm (a.equivFun v) i) (hF i)
        (norm_nonneg _) (norm_nonneg _)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] <;> ring

namespace CartanWordModel

variable {L : Type} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {H : LieSubalgebra ℝ L} [H.IsCartanSubalgebra] (M : CartanWordModel H)
  {n : ℕ} (T : TriangularAdjoint L n)
  (hunimod : ∀ x : L, LinearMap.trace ℝ L (ad ℝ L x) = 0)
  {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)

set_option maxHeartbeats 1000000 in
/-- Any smaller root exponent satisfies the normalized width estimate. -/
theorem norm_scaled_root_le_of_exponent_le
    {E : Set W} (hE : IsCompact E) (hne : E.Nonempty) (β : M.Bases)
    (i : Fin M.letterCount) (v : cartanRootIdeal H) (hv : (v : L) ∈ rootSpace H (M.weight i))
    {r t : ℝ} (hr : 0 ≤ r)
    (ht : t ≤ r * (M.supportIn T hunimod eW).weightSupport E i) :
    ‖(M.boxBasis T hunimod eW E β r).equivFun (Real.exp t • v)‖ ≤
      ‖(WordBasisSelections.basis M.letter M.wordList β).equivFun v‖ := by
  let s := r * (M.supportIn T hunimod eW).weightSupport E i
  have he : Real.exp t • v = Real.exp (t - s) • (Real.exp s • v) := by
    rw [smul_smul, ← Real.exp_add, sub_add_cancel]
  rw [he, map_smul, norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  have hexp : Real.exp (t - s) ≤ 1 := Real.exp_le_one_iff.mpr (sub_nonpos.mpr ht)
  exact (mul_le_of_le_one_left (norm_nonneg _) hexp).trans
    (M.norm_scaled_root_le T hunimod eW hE hne β i v hv hr)

set_option maxHeartbeats 1000000 in
/-- Height containment absorbs the entire scalar part of each letter image. -/
theorem norm_adjoint_letter_le
    {E : Set W} (hE : IsCompact E) (hne : E.Nonempty) (β : M.Bases)
    {r : ℝ} (hr : 0 ≤ r) (h : H) (w : W) (hw : w ∈ E)
    (hh : eW (heightProjection T.character (h : L)) = r • w) (i : Fin M.letterCount) :
    ‖(M.boxBasis T hunimod eW E β r).equivFun
      (cartanIdealAdjointAutomorphism T H h (M.letter i))‖ ≤
    ‖(WordBasisSelections.basis M.letter M.wordList β).equivFun
      (cartanIdealResidualAutomorphism T H h (M.letter i))‖ := by
  have hv := cartanIdealResidualAutomorphism_root_mem T H h (M.weight i)
    (M.letter i) (M.letter_root i)
  have he : cartanIdealAdjointAutomorphism T H h (M.letter i) =
      Real.exp (M.weight i h) • cartanIdealResidualAutomorphism T H h (M.letter i) := by
    apply Subtype.ext
    exact cartanWeightScale_apply_root T H h (M.weight i) hv
  rw [he]
  apply M.norm_scaled_root_le_of_exponent_le T hunimod eW hE hne β i _ hv hr
  have hweight : M.weight i h = r * (M.supportIn T hunimod eW).weight i w := by
    have heq := congrArg ((M.supportIn T hunimod eW).weight i) hh
    simpa only [supportIn, SupportDatum.transport, supportDatum_weight,
      LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply,
      cartanHeightWeight_projection, map_smul, smul_eq_mul] using heq
  rw [hweight]
  exact mul_le_mul_of_nonneg_left
    ((M.supportIn T hunimod eW).weight_le_weightSupport hE hw i) hr

omit T hunimod eW [FiniteDimensional ℝ L]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] in
set_option maxHeartbeats 1000000 in
/-- A bound on generator images controls the map from any word basis to a
basis with bounded structure constants. -/
theorem norm_wordBasis_lieMap_le
    (γ : M.Bases)
    (b : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (F : cartanRootIdeal H →ₗ⁅ℝ⁆ cartanRootIdeal H) {K A : ℝ} (hK : 0 ≤ K) (hA : 0 ≤ A)
    (hbracket : ∀ i j k, |b.repr ⁅b i, b j⁆ k| ≤ K)
    (hletter : ∀ i, ‖b.equivFun (F (M.letter i))‖ ≤ A) (v : cartanRootIdeal H) :
    ‖b.equivFun (F v)‖ ≤
      (finrank ℝ (cartanRootIdeal H) : ℝ) *
        (1 + (finrank ℝ (cartanRootIdeal H) : ℝ) ^ 2 * K) ^ M.wordDegreeBound *
        (1 + A) ^ M.wordDegreeBound *
          ‖(WordBasisSelections.basis M.letter M.wordList γ).equivFun v‖ := by
  let d := finrank ℝ (cartanRootIdeal H)
  let Q := 1 + (d : ℝ) ^ 2 * K
  have hword (w : M.wordList) :
      ‖b.equivFun (F (evalBracketWord M.letter w))‖ ≤
        Q ^ M.wordDegreeBound * (1 + A) ^ M.wordDegreeBound := by
    rw [evalBracketWord_map]
    apply (norm_basis_evalBracketWord_le b (fun i => F (M.letter i)) hK hA hbracket hletter w).trans
    simp only [Fintype.card_fin]
    have hd := M.word_degrees_le w
    apply mul_le_mul
    · exact (pow_le_pow_left₀ (by positivity)
        (show (d : ℝ) ^ 2 * K ≤ Q by dsimp [Q] <;> linarith) _).trans
        (pow_le_pow_right₀ (by
          dsimp [Q]
          exact le_add_of_nonneg_right (mul_nonneg (sq_nonneg _) hK)) hd.1)
    · exact (pow_le_pow_left₀ hA (by linarith : A ≤ 1 + A) _).trans
        (pow_le_pow_right₀ (by linarith) hd.2)
    · positivity
    · positivity
  have hb (i : Fin d) :
      ‖b.equivFun (F (WordBasisSelections.basis M.letter M.wordList γ i))‖ ≤
        Q ^ M.wordDegreeBound * (1 + A) ^ M.wordDegreeBound := by
    have he := WordBasisSelections.eval_words M.letter M.wordList γ i
    change evalBracketWord M.letter (γ.val i) = _ at he
    rw [← he]
    exact hword (γ.val i)
  have hs := norm_map_between_bases_le (WordBasisSelections.basis M.letter M.wordList γ) b
    F.toLinearMap hb v
  simp only [Fintype.card_fin] at hs
  change ‖b.equivFun (F v)‖ ≤ (d : ℝ) *
    (Q ^ M.wordDegreeBound * (1 + A) ^ M.wordDegreeBound) *
      ‖(WordBasisSelections.basis M.letter M.wordList γ).equivFun v‖ at hs
  simpa only [Q, d, mul_assoc] using hs

set_option maxHeartbeats 1000000 in
/-- Uniform polynomial coordinate control for Cartan actions with height
inside a scaled template. The input basis is unscaled and need not maximize. -/
theorem exists_controlled_adjoint_bound
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H)) :
    ∃ (A : ℝ) (p : ℕ), 0 ≤ A ∧ ∀ {E : Set W}, IsCompact E → E.Nonempty →
      ∀ β : M.Bases,
      IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
        (M.boxCost T hunimod eW E) β.val →
      ∀ (γ : M.Bases) (r : ℝ), 0 ≤ r → ∀ (h : H) (w : W), w ∈ E →
      eW (heightProjection T.character (h : L)) = r • w → ∀ v : cartanRootIdeal H,
      ‖(M.boxBasis T hunimod eW E β r).equivFun (cartanIdealAdjointAutomorphism T H h v)‖ ≤
        A * (1 + ‖(Module.finBasis ℝ H).equivFun h‖) ^ p *
          ‖(WordBasisSelections.basis M.letter M.wordList γ).equivFun v‖ := by
  obtain ⟨C, p, hC, hletters⟩ := M.exists_residual_letters_bound T
  obtain ⟨K, hK, hbracket⟩ := exists_uniform_rescaled_structureConstant_bound
    M.letter M.bound_zero b₀
  let d := finrank ℝ (cartanRootIdeal H)
  let Q := 1 + (d : ℝ) ^ 2 * K
  refine ⟨(d : ℝ) * Q ^ M.wordDegreeBound * (1 + C) ^ M.wordDegreeBound,
    p * M.wordDegreeBound, by dsimp [Q] <;> positivity, ?_⟩
  intro E hE hne β hβ γ r hr h w hw hh v
  let q := 1 + ‖(Module.finBasis ℝ H).equivFun h‖
  have hq : 1 ≤ q := le_add_of_nonneg_right (norm_nonneg _)
  have hqp : 1 ≤ q ^ p := one_le_pow₀ hq
  have hF (i : Fin M.letterCount) :
      ‖(M.boxBasis T hunimod eW E β r).equivFun
        (cartanIdealAdjointAutomorphism T H h (M.letter i))‖ ≤ C * q ^ p :=
    (M.norm_adjoint_letter_le T hunimod eW hE hne β hr h w hw hh i).trans (hletters β h i)
  have hb := M.norm_wordBasis_lieMap_le γ (M.boxBasis T hunimod eW E β r)
    (cartanIdealAdjointAutomorphism T H h).toLieHom hK (by positivity : 0 ≤ C * q ^ p)
    (hbracket ((M.supportIn T hunimod eW).weightSupport E) β hβ r hr) hF v
  apply hb.trans
  have hs : 1 + C * q ^ p ≤ (1 + C) * q ^ p := by nlinarith
  calc
    _ ≤ (d : ℝ) * Q ^ M.wordDegreeBound * ((1 + C) * q ^ p) ^ M.wordDegreeBound *
        ‖(WordBasisSelections.basis M.letter M.wordList γ).equivFun v‖ := by
      dsimp only [Q, d]
      gcongr
    _ = _ := by rw [mul_pow, ← pow_mul]; ring

end CartanWordModel
end PolycyclicRecognition

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
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanFactorHeight
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Canonical height of the constructed Cartan factors

The nilpotent root factor has zero height. The Cartan logarithm records the
height of every lifted prefix exactly, not just up to bounded error.
-/

noncomputable section

namespace PolycyclicRecognition.CartanFactorModel

open scoped Manifold

variable {EG G : Type} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  {ExpG : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H ExpG)
  {W : Type} [AddCommGroup W] [Module ℝ W]
  (q : HeightSpace T.character ≃ₗ[ℝ] W) (π : G →* Multiplicative W)
  (hπExp : ∀ x, (π (ExpG x)).toAdd = q (heightProjection T.character x))

set_option maxHeartbeats 1000000 in
include hπExp in
/-- Cartan logarithmic coordinates recover the actual ambient height. -/
theorem inclusionD_height
    (hbij : Function.Bijective F.ExpD) (d : F.D.carrier) :
    (π (F.inclusionD d)).toAdd = q (heightProjection T.character
      (cartanLog H F.D.equiv F.ExpD hbij d : GroupLieAlgebra (𝓘(ℝ, EG)) G)) := by
  have h := F.compatibleD (cartanLog H F.D.equiv F.ExpD hbij d)
  rw [exp_cartanLog H F.D.equiv F.ExpD hbij d] at h
  rw [h, hπExp]

end PolycyclicRecognition.CartanFactorModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanSmallHeight
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instDecidableEqConeMixedWords _root_.OAI.PolycyclicRecognition.CartanWordModel.instFintypeConeMixedWords _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_nonempty _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.CartanFactorModel.heightRay_zero _root_.OAI.PolycyclicRecognition.CartanFactorModel.realScaleProfile_apply _root_.OAI.PolycyclicRecognition.CartanFactorModel.sampledProbeProfile_apply _root_.OAI.PolycyclicRecognition.bracketWordDifferential_mul _root_.OAI.PolycyclicRecognition.cartanWeightDerivation_apply_root _root_.OAI.PolycyclicRecognition.exponentialRescaleBasis_zero _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.nilshadowWeightDerivation_symm _root_.OAI.PolycyclicRecognition.nilshadowWeightOperator_symm _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Conjugating a small error by a Cartan factor of small height

The full logarithm of the Cartan factor may be polynomially large. Only its
height contributes to the exponential factor; the residual action contributes
a fixed polynomial. This distinction is needed for thickened probe endpoints.
-/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule Set Metric Filter
open scoped Topology
open scoped Pointwise

variable {L W : Type} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {H : LieSubalgebra ℝ L} [H.IsCartanSubalgebra] (M : CartanWordModel H)
  {n : ℕ} (T : TriangularAdjoint L n)
  (hunimod : ∀ x : L, LinearMap.trace ℝ L (ad ℝ L x) = 0)
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)

set_option maxHeartbeats 1000000 in
/-- The estimate is uniform over all input word bases. The output uses
one fixed zero-template basis. -/
theorem exists_small_height_adjoint_bound
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (β : M.Bases)
    (hβ : IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
      (M.boxCost T hunimod eW {0}) β.val) :
    ∃ (A K : ℝ) (p : ℕ), 0 ≤ A ∧ 0 ≤ K ∧
      ∀ (γ : M.Bases) (h : H) (v : cartanRootIdeal H),
        ‖(M.boxBasis T hunimod eW {0} β 1).equivFun
          (cartanIdealAdjointAutomorphism T H h v)‖ ≤
        A * (1 + ‖(finBasis ℝ H).equivFun h‖) ^ p *
          Real.exp (K * ‖eW (heightProjection T.character (h : L))‖) *
            ‖(WordBasisSelections.basis M.letter M.wordList γ).equivFun v‖ := by
  obtain ⟨A, p, hA, haction⟩ := M.exists_controlled_adjoint_bound T hunimod eW b₀
  obtain ⟨D, hD, hcompare⟩ := exists_word_box_comparison_constant M.letter M.wordList b₀
  obtain ⟨K, hK, hcost⟩ := M.exists_boxCost_thickening_constant T hunimod eW
  refine ⟨D * A, K, p, mul_nonneg hD hA, hK, ?_⟩
  intro γ h v
  let w := eW (heightProjection T.character (h : L))
  let E : Set W := ({0} : Set W) + closedBall 0 ‖w‖
  have hE : IsCompact E := isCompact_singleton.add (isCompact_closedBall 0 ‖w‖)
  have hw : w ∈ E := by
    have hh : w ∈ closedBall (0 : W) ‖w‖ := by simp
    simpa only [zero_add] using add_mem_add (mem_singleton (0 : W)) hh
  have hne : E.Nonempty := ⟨w, hw⟩
  obtain ⟨βh, hβh, _⟩ := M.exists_maximizing_box_basis T hunimod eW b₀ E
  have ha := haction hE hne βh hβh γ 1 (by norm_num) h w hw (by simp [w]) v
  have hc := hcompare (M.boxCost T hunimod eW {0}) (M.boxCost T hunimod eW E)
    β βh hβ (r := 1) (ε := K * ‖w‖) (by norm_num)
    (hcost isCompact_singleton (singleton_nonempty (0 : W)) (norm_nonneg w))
    (cartanIdealAdjointAutomorphism T H h v)
  change ‖(M.boxBasis T hunimod eW {0} β 1).equivFun
      (cartanIdealAdjointAutomorphism T H h v)‖ ≤ _ at hc
  rw [mul_one] at hc
  calc
    _ ≤ D * Real.exp (K * ‖w‖) *
        ‖(M.boxBasis T hunimod eW E βh 1).equivFun
          (cartanIdealAdjointAutomorphism T H h v)‖ := hc
    _ ≤ D * Real.exp (K * ‖w‖) *
        (A * (1 + ‖(finBasis ℝ H).equivFun h‖) ^ p *
          ‖(WordBasisSelections.basis M.letter M.wordList γ).equivFun v‖) :=
      mul_le_mul_of_nonneg_left ha (mul_nonneg hD (Real.exp_pos _).le)
    _ = _ := by dsimp [w] <;> ring

set_option maxHeartbeats 1000000 in
include hunimod in
/-- The output can use the fixed adapted ideal-section basis. Its
coordinate change only changes the constant, not the height exponent. -/
theorem exists_small_height_adjoint_bound_in_basis
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    {J : Type} [Fintype J] (b : Basis J ℝ (cartanRootIdeal H)) :
    ∃ (A K : ℝ) (p : ℕ), 0 ≤ A ∧ 0 ≤ K ∧
      ∀ (γ : M.Bases) (h : H) (v : cartanRootIdeal H),
        ‖b.equivFun (cartanIdealAdjointAutomorphism T H h v)‖ ≤
        A * (1 + ‖(finBasis ℝ H).equivFun h‖) ^ p *
          Real.exp (K * ‖eW (heightProjection T.character (h : L))‖) *
            ‖(WordBasisSelections.basis M.letter M.wordList γ).equivFun v‖ := by
  obtain ⟨β, hβ, _⟩ := M.exists_maximizing_box_basis T hunimod eW b₀ {0}
  obtain ⟨A, K, p, hA, hK, hbound⟩ :=
    M.exists_small_height_adjoint_bound T hunimod eW b₀ β hβ
  let bZ := M.boxBasis T hunimod eW {0} β 1
  let f := (b.equivFun.toLinearMap.comp bZ.equivFun.symm.toLinearMap).toContinuousLinearMap
  have hf (v : cartanRootIdeal H) : ‖b.equivFun v‖ ≤ ‖f‖ * ‖bZ.equivFun v‖ := by
    simpa only [f, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_comp,
      Function.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply] using
      f.le_opNorm (bZ.equivFun v)
  refine ⟨‖f‖ * A, K, p, mul_nonneg (norm_nonneg _) hA, hK, ?_⟩
  intro γ h v
  calc
    _ ≤ ‖f‖ * ‖bZ.equivFun (cartanIdealAdjointAutomorphism T H h v)‖ := hf _
    _ ≤ ‖f‖ * (A * (1 + ‖(finBasis ℝ H).equivFun h‖) ^ p *
        Real.exp (K * ‖eW (heightProjection T.character (h : L))‖) *
          ‖(WordBasisSelections.basis M.letter M.wordList γ).equivFun v‖) :=
      mul_le_mul_of_nonneg_left (hbound γ h v) (norm_nonneg _)
    _ = _ := by ring

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_WeightedSectionError
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The ideal coordinate after a small ambient logarithmic error

This is the last assertion of the manuscript's strict-width absorption
lemma. The error factor is computed by BCH; its ideal part is absorbed by
positive widths before multiplying the two ideal factors.
-/

noncomputable section
namespace PolycyclicRecognition

open Module Set Filter
open scoped Topology

theorem HasSubexponentialUpperBound.eventually_le_perturbed_exp
    {R : ℝ → ℝ} (hR : HasSubexponentialUpperBound R)
    {α : ℝ} (hα : 0 < α) {ε : ℝ → ℝ} (hε : Tendsto ε atTop (𝓝 0)) :
    ∀ᶠ r in atTop, R r ≤ Real.exp ((α + ε r) * r) := by
  filter_upwards [hR (α / 2) (by positivity),
    hε.eventually (eventually_gt_nhds (show -(α / 2) < 0 by linarith)),
    eventually_ge_atTop (0 : ℝ)] with r hr he hr0
  exact hr.trans (Real.exp_le_exp.mpr (by nlinarith))

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanUniformSmallHeight
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instDecidableEqConeMixedWords _root_.OAI.PolycyclicRecognition.CartanWordModel.instFintypeConeMixedWords _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.CartanFactorModel.heightRay_zero _root_.OAI.PolycyclicRecognition.CartanFactorModel.realScaleProfile_apply _root_.OAI.PolycyclicRecognition.CartanFactorModel.sampledProbeProfile_apply _root_.OAI.PolycyclicRecognition.cartanWeightDerivation_apply_root _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.nilshadowWeightDerivation_symm _root_.OAI.PolycyclicRecognition.nilshadowWeightOperator_symm _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Small-height control chosen before the probe path constants -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule Set Metric Filter
open scoped Topology
open scoped Pointwise

variable {L W : Type} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {H : LieSubalgebra ℝ L} [H.IsCartanSubalgebra] (M : CartanWordModel H)
  {n : ℕ} (T : TriangularAdjoint L n)
  (hunimod : ∀ x : L, LinearMap.trace ℝ L (ad ℝ L x) = 0)
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)

set_option maxHeartbeats 1000000 in
include hunimod in
theorem exists_uniform_small_height_adjoint_sequence_bound
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    {J : Type} [Fintype J] (b : Basis J ℝ (cartanRootIdeal H))
    : ∃ B : ℝ, 0 < B ∧ ∀ (scale RH RE : ℕ → ℝ),
      Tendsto scale atTop atTop → (∀ n, 0 ≤ RH n) →
      HasSubexponentialUpperBoundSeq scale RH →
      HasSubexponentialUpperBoundSeq scale RE →
      ∀ δ : ℝ, 0 < δ → ∀ᶠ n in atTop,
        ∀ (γ : M.Bases) (h : H) (v : cartanRootIdeal H),
          ‖(finBasis ℝ H).equivFun h‖ ≤ RH n →
          ‖eW (heightProjection T.character (h : L))‖ ≤ δ * scale n →
          ‖(WordBasisSelections.basis M.letter M.wordList γ).equivFun v‖ ≤
            RE n * Real.exp (δ * scale n) →
          ‖b.equivFun (cartanIdealAdjointAutomorphism T H h v)‖ ≤
            Real.exp (B * δ * scale n) := by
  obtain ⟨A, K, p, hA, hK, hbound⟩ :=
    M.exists_small_height_adjoint_bound_in_basis T hunimod eW b₀ b
  refine ⟨K + 2, by linarith, ?_⟩
  intro scale RH RE hs hRH0 hRH hRE
  let R := fun n => A * (1 + RH n) ^ p * RE n
  have hR : HasSubexponentialUpperBoundSeq scale R :=
    ((sequence_subexponential_upper_const hs A).mul
      (((sequence_subexponential_upper_const hs 1).add hRH hs).pow hs
        (Eventually.of_forall (fun n => by linarith [hRH0 n])) p)
      (Eventually.of_forall (fun _ => hA))).mul hRE
      (Eventually.of_forall (fun n => mul_nonneg hA (pow_nonneg (by linarith [hRH0 n]) _)))
  intro δ hδ
  filter_upwards [hR δ hδ] with n hn γ h v hh hw hv
  have hpow : (1 + ‖(finBasis ℝ H).equivFun h‖) ^ p ≤ (1 + RH n) ^ p :=
    pow_le_pow_left₀ (by positivity) (by linarith) p
  have he : Real.exp (K * ‖eW (heightProjection T.character (h : L))‖) ≤
      Real.exp (K * (δ * scale n)) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hw hK)
  have hr0 : 0 ≤ A * (1 + RH n) ^ p * Real.exp (K * (δ * scale n)) := by
    exact mul_nonneg (mul_nonneg hA (pow_nonneg (by linarith [hRH0 n]) _))
      (Real.exp_nonneg _)
  calc
    _ ≤ A * (1 + ‖(finBasis ℝ H).equivFun h‖) ^ p *
        Real.exp (K * ‖eW (heightProjection T.character (h : L))‖) *
          ‖(WordBasisSelections.basis M.letter M.wordList γ).equivFun v‖ := hbound γ h v
    _ ≤ A * (1 + RH n) ^ p * Real.exp (K * (δ * scale n)) *
        (RE n * Real.exp (δ * scale n)) := by
      apply mul_le_mul _ hv (norm_nonneg _) hr0
      exact mul_le_mul (mul_le_mul_of_nonneg_left hpow hA) he
        (Real.exp_nonneg _) (mul_nonneg hA (pow_nonneg (by linarith [hRH0 n]) _))
    _ = R n * Real.exp ((K + 1) * δ * scale n) := by
      dsimp [R]
      rw [show (K + 1) * δ * scale n = K * (δ * scale n) + δ * scale n by ring,
        Real.exp_add]
      ring
    _ ≤ Real.exp (δ * scale n) * Real.exp ((K + 1) * δ * scale n) :=
      mul_le_mul_of_nonneg_right hn (Real.exp_nonneg _)
    _ = Real.exp ((K + 2) * δ * scale n) := by
      rw [← Real.exp_add]
      congr 1
      ring


end PolycyclicRecognition.CartanWordModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_UniformWeightedSectionError
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.CartanFactorModel.realScaleProfile_apply _root_.OAI.PolycyclicRecognition.basisDynkinParameter_zero _root_.OAI.PolycyclicRecognition.dynkinRightTranslation_apply _root_.OAI.PolycyclicRecognition.dynkinRightTranslation_symm_apply _root_.OAI.PolycyclicRecognition.exponentialHomOfDynkin_apply_exp _root_.OAI.PolycyclicRecognition.exponentialQuotientSection_apply _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # An absorption threshold independent of the path envelopes -/

noncomputable section
namespace PolycyclicRecognition

open Module Set Filter
open scoped Topology

variable {V I J N Q : Type} [LieRing V] [LieAlgebra ℝ V] [Fintype I] [Fintype J]
  [Group N] [Group Q]
  (U : LieIdeal ℝ V) (bI : Basis I ℝ U) (bQ : Basis J ℝ (V ⧸ U.toSubmodule))
  (lift : J → V) (hlift : ∀ j, U.toSubmodule.mkQ (lift j) = bQ j)
  (ExpN : V → N) (ExpQ : (V ⧸ U.toSubmodule) → Q) (π : N →* Q)
  (hπ : ∀ v, π (ExpN v) = ExpQ (U.toSubmodule.mkQ v))
  (hinjQ : Function.Injective ExpQ) (hzeroQ : ExpQ 0 = 1)
  (hneg : ∀ v, ExpN (-v) = (ExpN v)⁻¹)
  {c : ℕ} (coeff : DynkinCoefficients c 2)
  (hcoeff : ∀ d w, |coeff d w| ≤ (2 : ℝ) ^ c)
  (hmul : ∀ v w, ExpN (finiteDynkinPolynomial coeff ![v, w]) = ExpN v * ExpN w)

local notation "B" => basisWithQuotientLifts U.toSubmodule bI bQ lift hlift

include hπ hinjQ hzeroQ hneg hcoeff hmul in
/-- Choose the small bridge threshold before the subexponential path envelope.
This order is needed when the path constants are only fixed after choosing the
contact pivot. -/
theorem weighted_section_error_absorbed_uniform
    (cost : I → ℝ) {lo M : ℝ} (hlo : 0 < lo)
    (hcost : ∀ i, lo ≤ cost i) (hM : 0 < M)
    (C : ℝ) (hC : 0 ≤ C)
    (hbr : ∀ r : ℝ, 0 ≤ r → ∀ i j k,
      |(exponentialRescaleBasis B (Sum.elim cost (fun _ => 0)) r).repr
        ⁅exponentialRescaleBasis B (Sum.elim cost (fun _ => 0)) r i,
          exponentialRescaleBasis B (Sum.elim cost (fun _ => 0)) r j⁆ k| ≤ C)
    : ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ (R : ℝ → ℝ),
      (∀ r, 0 ≤ R r) → HasSubexponentialUpperBound R →
      ∃ S : ℝ → ℝ, HasSubexponentialUpperBound S ∧
        ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
        ∀ ε : ℝ → ℝ, Tendsto ε atTop (𝓝 0) →
        ∀ᶠ r in atTop, ∀ (n : N) (e : V),
          n ∈ exponentialCoordinateBox ExpN
            (exponentialRescaleBasis B (Sum.elim cost (fun _ => 0)) r) (R r) →
          ‖(B).equivFun e‖ ≤ Real.exp ((M * δ + ε r) * r) →
          ∃ (u : U) (q : V ⧸ U.toSubmodule),
            n * ExpN e = ExpN (u : V) * ExpN (quotientLinearSection U bQ lift q) ∧
            ‖(exponentialRescaleBasis bI cost r).equivFun u‖ ≤ S r := by
  have hraw : ∀ i j k, |(B).repr ⁅(B) i, (B) j⁆ k| ≤ C := by
    simpa only [exponentialRescaleBasis_zero] using hbr 0 le_rfl
  obtain ⟨δ₀, hδ₀, habs⟩ := exists_section_error_absorption_threshold U bI bQ lift hlift
    ExpN ExpQ π hπ hinjQ hzeroQ hneg coeff hcoeff hmul C hC hraw cost hlo hcost hM
  refine ⟨δ₀, hδ₀, ?_⟩
  intro R hR hRsub
  let K₀ := sectionDynkinConstant (Fintype.card (I ⊕ J)) c C
  let K₁ := sectionDynkinConstant (Fintype.card I) c C
  let R₀ := fun r => K₀ * (1 + R r) ^ c
  let S := fun r => K₁ * (1 + (R₀ r + 1)) ^ c
  have hK₀ : 0 ≤ K₀ := by dsimp [K₀, sectionDynkinConstant] <;> positivity
  have hR₀ (r) : 0 ≤ R₀ r := mul_nonneg hK₀ (pow_nonneg (by linarith [hR r]) _)
  have hR₀sub : HasSubexponentialUpperBound R₀ :=
    section_box_subexponential_envelope (I := I) (J := J) (c := c) C hC R hR hRsub
  have hS : HasSubexponentialUpperBound S := by
    have hp := ((subexponential_upper_const 1).add
      (hR₀sub.add (subexponential_upper_const 1))).pow
      (Eventually.of_forall (fun r => by linarith [hR₀ r])) c
    exact (subexponential_upper_const K₁).mul hp
      (Eventually.of_forall (fun _ => by dsimp [K₁, sectionDynkinConstant] <;> positivity))
  refine ⟨S, hS, ?_⟩
  intro δ hδ hδle ε hε
  filter_upwards [habs δ hδ hδle ε hε,
    hRsub.eventually_le_perturbed_exp (mul_pos hM hδ) hε,
    eventually_ge_atTop (0 : ℝ)] with r hr hlarge hr0 n e hn he
  obtain ⟨u₀, q₀, hn, hu₀, hq₀⟩ := weighted_section_box_factorization U bI bQ lift hlift
    ExpN ExpQ π hπ hinjQ hzeroQ hneg coeff hcoeff hmul cost C hC hbr r (R r) hr0 (hR r) hn
  obtain ⟨u₁, q₁, heq, hu₁⟩ := hr q₀ e (hq₀.trans hlarge) he
  have hbrI : ∀ i j k, |(exponentialRescaleBasis bI cost r).repr
      ⁅exponentialRescaleBasis bI cost r i, exponentialRescaleBasis bI cost r j⁆ k| ≤ C := by
    apply ideal_basis_bracket_bound U (exponentialRescaleBasis bI cost r) bQ lift hlift
    simpa only [basisWithQuotientLifts_rescale] using hbr r hr0
  obtain ⟨u, hu, hub⟩ := ideal_product_coordinate_bound U
    (exponentialRescaleBasis bI cost r) ExpN coeff hcoeff hmul C hC hbrI
    (show 0 ≤ R₀ r + 1 by linarith [hR₀ r]) u₀ u₁
    (hu₀.trans (le_add_of_nonneg_right zero_le_one))
    (hu₁.trans (le_add_of_nonneg_left (hR₀ r)))
  refine ⟨u, q₁, ?_, hub⟩
  rw [hn, mul_assoc, heq, ← mul_assoc, ← hu]


include hπ hinjQ hzeroQ hneg hcoeff hmul in
/-- The same threshold is uniform over the scale sequence and every
subexponential input envelope. -/
theorem weighted_section_error_absorbed_sequence_uniform
    (cost : I → ℝ) {lo M : ℝ} (hlo : 0 < lo)
    (hcost : ∀ i, lo ≤ cost i) (hM : 0 < M)
    (C : ℝ) (hC : 0 ≤ C)
    (hbr : ∀ r : ℝ, 0 ≤ r → ∀ i j k,
      |(exponentialRescaleBasis B (Sum.elim cost (fun _ => 0)) r).repr
        ⁅exponentialRescaleBasis B (Sum.elim cost (fun _ => 0)) r i,
          exponentialRescaleBasis B (Sum.elim cost (fun _ => 0)) r j⁆ k| ≤ C) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ (scale : ℕ → ℝ), StrictMono scale →
      Tendsto scale atTop atTop → ∀ (R : ℕ → ℝ), (∀ n, 0 ≤ R n) →
      HasSubexponentialUpperBoundSeq scale R →
      ∃ S : ℕ → ℝ, HasSubexponentialUpperBoundSeq scale S ∧
        ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
        ∀ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) →
        ∀ᶠ n in atTop, ∀ (u : N) (e : V),
          u ∈ exponentialCoordinateBox ExpN
            (exponentialRescaleBasis B (Sum.elim cost (fun _ => 0)) (scale n)) (R n) →
          ‖(B).equivFun e‖ ≤ Real.exp ((M * δ + ε n) * scale n) →
          ∃ (i : U) (q : V ⧸ U.toSubmodule),
            u * ExpN e = ExpN (i : V) * ExpN (quotientLinearSection U bQ lift q) ∧
            ‖(exponentialRescaleBasis bI cost (scale n)).equivFun i‖ ≤ S n := by
  obtain ⟨δ₀, hδ₀, habs⟩ := weighted_section_error_absorbed_uniform U bI bQ lift hlift
    ExpN ExpQ π hπ hinjQ hzeroQ hneg coeff hcoeff hmul cost hlo hcost hM C hC hbr
  refine ⟨δ₀, hδ₀, ?_⟩
  intro scale hs hscale R hR hRsub
  obtain ⟨S, hS, he⟩ := habs (sequenceRealExtension scale R)
    (sequenceRealExtension_nonneg scale R hR) (hRsub.realExtension hs)
  refine ⟨S ∘ scale, hS.along_sequence hscale, ?_⟩
  intro δ hδ hδle ε hε
  have hh := hscale.eventually (he δ hδ hδle (sequenceRealExtension scale ε)
    (tendsto_sequenceRealExtension_zero scale hs ε hε))
  simpa only [sequenceRealExtension_apply scale hs, Function.comp_apply] using hh

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanUniformBridgeAbsorption
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instDecidableEqConeMixedWords _root_.OAI.PolycyclicRecognition.CartanWordModel.instFintypeConeMixedWords _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A bridge absorption threshold fixed before paths and scales -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule Filter Set
open scoped Topology

variable {L W : Type} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {H : LieSubalgebra ℝ L} [H.IsCartanSubalgebra] (M : CartanWordModel H)
  {a : ℕ} (T : TriangularAdjoint L a)
  (hunimod : ∀ x : L, LinearMap.trace ℝ L (ad ℝ L x) = 0)
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)
  (C : Set (H →ₗ[ℝ] ℝ))

local notation "U" => M.coneWordIdeal C

set_option maxHeartbeats 1000000 in
include hunimod in
theorem exists_uniform_conjugated_bridge_ideal_bound
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    {I J : Type} [Fintype I] [Fintype J]
    (bI : Basis I ℝ U) (bQ : Basis J ℝ ((cartanRootIdeal H) ⧸ (M.coneWordIdeal C).toSubmodule))
    (lift : J → cartanRootIdeal H) (hlift : ∀ j, (M.coneWordIdeal C).toSubmodule.mkQ (lift j) = bQ j)
    {N Q : Type} [Group N] [Group Q]
    (ExpN : cartanRootIdeal H → N) (ExpQ : ((cartanRootIdeal H) ⧸ (M.coneWordIdeal C).toSubmodule) → Q)
    (π : N →* Q) (hπ : ∀ v, π (ExpN v) = ExpQ ((M.coneWordIdeal C).toSubmodule.mkQ v))
    (hinjQ : Function.Injective ExpQ) (hzeroQ : ExpQ 0 = 1)
    (hneg : ∀ v, ExpN (-v) = (ExpN v)⁻¹)
    {c : ℕ} (coeff : DynkinCoefficients c 2)
    (hcoeff : ∀ d w, |coeff d w| ≤ (2 : ℝ) ^ c)
    (hmul : ∀ v w, ExpN (finiteDynkinPolynomial coeff ![v, w]) = ExpN v * ExpN w)
    (cost : I → ℝ) {lo : ℝ} (hlo : 0 < lo) (hcost : ∀ i, lo ≤ cost i)
    (K : ℝ) (hK : 0 ≤ K)
    (hbr : ∀ r : ℝ, 0 ≤ r → ∀ i j k,
      |(exponentialRescaleBasis (basisWithQuotientLifts (M.coneWordIdeal C).toSubmodule bI bQ lift hlift)
        (Sum.elim cost (fun _ => 0)) r).repr
          ⁅exponentialRescaleBasis (basisWithQuotientLifts (M.coneWordIdeal C).toSubmodule bI bQ lift hlift)
              (Sum.elim cost (fun _ => 0)) r i,
            exponentialRescaleBasis (basisWithQuotientLifts (M.coneWordIdeal C).toSubmodule bI bQ lift hlift)
              (Sum.elim cost (fun _ => 0)) r j⁆ k| ≤ K)
    : ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ (scale RN RH RE : ℕ → ℝ),
      StrictMono scale → Tendsto scale atTop atTop →
      (∀ n, 0 ≤ RN n) → (∀ n, 0 ≤ RH n) →
      HasSubexponentialUpperBoundSeq scale RN →
      HasSubexponentialUpperBoundSeq scale RH →
      HasSubexponentialUpperBoundSeq scale RE →
      ∃ S : ℕ → ℝ, HasSubexponentialUpperBoundSeq scale S ∧
        ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
        ∀ᶠ n in atTop, ∀ (u : N) (γ : M.Bases) (h : H) (v : cartanRootIdeal H),
          u ∈ exponentialCoordinateBox ExpN
            (exponentialRescaleBasis
              (basisWithQuotientLifts (M.coneWordIdeal C).toSubmodule bI bQ lift hlift)
              (Sum.elim cost (fun _ => 0)) (scale n)) (RN n) →
          ‖(finBasis ℝ H).equivFun h‖ ≤ RH n →
          ‖eW (heightProjection T.character (h : L))‖ ≤ δ * scale n →
          ‖(WordBasisSelections.basis M.letter M.wordList γ).equivFun v‖ ≤
            RE n * Real.exp (δ * scale n) →
          ∃ (i : U) (q : (cartanRootIdeal H) ⧸ (M.coneWordIdeal C).toSubmodule),
            u * ExpN (cartanIdealAdjointAutomorphism T H h v) =
              ExpN (i : cartanRootIdeal H) * ExpN (quotientLinearSection U bQ lift q) ∧
            ‖(exponentialRescaleBasis bI cost (scale n)).equivFun i‖ ≤ S n := by
  let b := basisWithQuotientLifts (M.coneWordIdeal C).toSubmodule bI bQ lift hlift
  obtain ⟨A, hA, haction⟩ := M.exists_uniform_small_height_adjoint_sequence_bound
    T hunimod eW b₀ b
  obtain ⟨δ₀, hδ₀, habs⟩ := weighted_section_error_absorbed_sequence_uniform
    U bI bQ lift hlift ExpN ExpQ π hπ hinjQ hzeroQ hneg coeff hcoeff hmul
    cost hlo hcost hA K hK hbr
  refine ⟨δ₀, hδ₀, ?_⟩
  intro scale RN RH RE hs hscale hRN0 hRH0 hRN hRH hRE
  obtain ⟨S, hS, he⟩ := habs scale hs hscale RN hRN0 hRN
  refine ⟨S, hS, ?_⟩
  intro δ hδ hδle
  have hzero : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0) := tendsto_const_nhds
  filter_upwards [haction scale RH RE hscale hRH0 hRH hRE δ hδ,
    he δ hδ hδle (fun _ => 0) hzero] with n ha hb
  intro u γ h v hu hh hw hv
  apply hb u (cartanIdealAdjointAutomorphism T H h v) hu
  simpa only [zero_add, add_zero, mul_assoc] using ha γ h v hh hw hv

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_ExponentialBridgeComposition
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exponential error bounds in the composition of two factor lifts -/

namespace PolycyclicRecognition

theorem exists_thickened_factor_bridge_of_bounds
    {N D G V I Q : Type} [Group N] [Group D] [Group G]
    (φ : D →* MulAut N) (ι : N →* G) (κ : D →* G)
    (hc : ∀ d n, ι (φ d n) = κ d * ι n * (κ d)⁻¹)
    (Exp : V → N) (ExpI : I → N) (qsec : Q → N)
    (vnorm : V → ℝ) (dnorm : D → ℝ) (ideal : I → Prop) (DF Extra : D → Prop)
    (cell : Set (N × D)) (u₂ : N) (d₂ : D) (g : G)
    (RE RB A δ r : ℝ) (hRE : 0 ≤ RE) (hδ : 0 ≤ δ) (hr : 0 ≤ r)
    (habsorb : ∀ v, vnorm v ≤ RE * Real.exp (((A + 1) * δ) * r) →
      ∃ i q, u₂ * φ d₂ (Exp v) = ExpI i * qsec q ∧ ideal i)
    (hD : ∀ d, dnorm d ≤ RB → DF (d₂ * d))
    (hbridge : ∃ ub db, ι ub * κ db = g ∧ Extra db ∧ ∀ z ∈ cell,
      (∃ v, Exp v = ub * φ db z.1 ∧ vnorm v ≤ RE * Real.exp (A * δ * r)) ∧
        dnorm (db * z.2) ≤ RB) :
    ∃ u d, ι u * κ d = (ι u₂ * κ d₂) * g ∧ ∀ z ∈ cell,
      (∃ i q, u * φ d z.1 = ExpI i * qsec q ∧ ideal i) ∧ DF (d * z.2) := by
  apply exists_thickened_factor_bridge φ ι κ hc Exp ExpI qsec
    (fun v => vnorm v ≤ RE * Real.exp (((A + 1) * δ) * r)) ideal
    (fun d => dnorm d ≤ RB) DF cell u₂ d₂ g habsorb hD
  obtain ⟨ub, db, hg, _, hb⟩ := hbridge
  refine ⟨ub, db, hg, ?_⟩
  intro z hz
  obtain ⟨⟨v, hv, hvbound⟩, hdb⟩ := hb z hz
  refine ⟨⟨v, hv, hvbound.trans ?_⟩, hdb⟩
  apply mul_le_mul_of_nonneg_left _ hRE
  apply Real.exp_le_exp.mpr
  nlinarith [mul_nonneg hδ hr]

end PolycyclicRecognition

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_SequenceCartanProducts
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.chartExponentialFlow_zero _root_.OAI.PolycyclicRecognition.derivationSemidirectHom_apply _root_.OAI.PolycyclicRecognition.exponentialHomOfDynkin_apply_exp _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Products of the Cartan factors of two probe paths -/

noncomputable section
namespace PolycyclicRecognition

open Module LieModule Filter
open scoped Manifold Topology

variable {L : Type} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  (H : LieSubalgebra ℝ L) [H.IsCartanSubalgebra]
  {ED D : Type} [NormedAddCommGroup ED] [NormedSpace ℝ ED]
  [FiniteDimensional ℝ ED] [TopologicalSpace D] [ChartedSpace ED D] [Group D]
  [LieGroup (𝓘(ℝ, ED)) ⊤ D] [T2Space D]
  (eD : H ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, ED)) D)
  (ExpD : GroupLieAlgebra (𝓘(ℝ, ED)) D → D) (hbijD : Function.Bijective ExpD)

set_option maxHeartbeats 1000000 in
/-- A common subexponential box contains the products of every allowed
pair of Cartan factors, including the final right-cell increment. -/
theorem exists_sequence_cartan_product_bound
    (hExpD : IsGroupExponential ExpD) (dynkinD : NilpotentDynkinExpansionInput ED D)
    (scale R₁ R₂ : ℕ → ℝ) (hs : Tendsto scale atTop atTop)
    (hR₁0 : ∀ n, 0 ≤ R₁ n) (hR₂0 : ∀ n, 0 ≤ R₂ n)
    (hR₁ : HasSubexponentialUpperBoundSeq scale R₁)
    (hR₂ : HasSubexponentialUpperBoundSeq scale R₂) :
    ∃ R : ℕ → ℝ, (∀ n, 0 ≤ R n) ∧ HasSubexponentialUpperBoundSeq scale R ∧
      ∀ n (d e : D),
        ‖(finBasis ℝ H).equivFun (cartanLog H eD ExpD hbijD d)‖ ≤ R₁ n →
        ‖(finBasis ℝ H).equivFun (cartanLog H eD ExpD hbijD e)‖ ≤ R₂ n →
        ‖(finBasis ℝ H).equivFun (cartanLog H eD ExpD hbijD (d * e))‖ ≤ R n := by
  obtain ⟨c, hc⟩ := LieModule.IsNilpotent.nilpotent ℝ H H
  obtain ⟨K, hK, hbracket⟩ := exists_basis_structureConstant_bound (finBasis ℝ H)
  let A : ℝ := (c : ℝ) * 2 ^ c * (1 + (finrank ℝ H : ℝ) ^ 2 * K) ^ c
  have hA : 0 ≤ A := by dsimp [A] <;> positivity
  let R := fun n => A * (1 + (R₁ n + R₂ n)) ^ c * (1 + (2 : ℝ)) ^ c
  have hsum : HasSubexponentialUpperBoundSeq scale (fun n => 1 + (R₁ n + R₂ n)) :=
    (sequence_subexponential_upper_const hs 1).add (hR₁.add hR₂ hs) hs
  have hsum0 : ∀ n, 0 ≤ 1 + (R₁ n + R₂ n) := fun n => by
    linarith [hR₁0 n, hR₂0 n]
  refine ⟨R, fun n => mul_nonneg (mul_nonneg hA (pow_nonneg (hsum0 n) _))
    (by positivity), ?_, ?_⟩
  · exact ((sequence_subexponential_upper_const hs A).mul
      (hsum.pow hs (Eventually.of_forall hsum0) c) (Eventually.of_forall (fun _ => hA))).mul
      (sequence_subexponential_upper_const hs ((1 + (2 : ℝ)) ^ c))
      (Eventually.of_forall (fun n => mul_nonneg hA (pow_nonneg (hsum0 n) _)))
  intro n d e hd he
  have hmem (j : Fin 2) : ![d, e] j ∈ exponentialCoordinateBox (ExpD ∘ eD)
      (finBasis ℝ H) (R₁ n + R₂ n) := by
    fin_cases j
    · exact ⟨cartanLog H eD ExpD hbijD d, exp_cartanLog H eD ExpD hbijD d,
        hd.trans (le_add_of_nonneg_right (hR₂0 n))⟩
    · exact ⟨cartanLog H eD ExpD hbijD e, exp_cartanLog H eD ExpD hbijD e,
        he.trans (le_add_of_nonneg_left (hR₁0 n))⟩
  obtain ⟨v, hv, hnorm⟩ := product_mem_exponentialCoordinateBox dynkinD eD ExpD hExpD hc
    (finBasis ℝ H) hK (add_nonneg (hR₁0 n) (hR₂0 n)) hbracket ![d, e] hmem
  have hv' : ExpD (eD v) = d * e := by simpa using hv
  rw [← hv', cartanLog_exp]
  simpa [R, A] using hnorm

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanUniformBridgeGeometry
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instDecidableEqConeMixedWords _root_.OAI.PolycyclicRecognition.CartanWordModel.instFintypeConeMixedWords _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Thickened bridge bounds with a preassigned smallness threshold -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule Metric Set Filter
open scoped Manifold Topology

variable {EG G : Type} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [IsIsometricSMul G G] [ProperSpace G]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {ExpG : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H ExpG)
  (hunimod : ∀ x : GroupLieAlgebra (𝓘(ℝ, EG)) G,
    LinearMap.trace ℝ _ (ad ℝ _ x) = 0)
  {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  (eW : HeightSpace T.character ≃ₗ[ℝ] W) (π : G →* Multiplicative W)
  (hπExp : ∀ x, (π (ExpG x)).toAdd = eW (heightProjection T.character x))
  (chartN : GroupLieAlgebra (𝓘(ℝ, F.N.modelSpace)) F.N.carrier ≃ₜ F.N.carrier)
  (hchartN : ∀ x, chartN x = F.ExpN x)
  (chartD : GroupLieAlgebra (𝓘(ℝ, F.D.modelSpace)) F.D.carrier ≃ₜ F.D.carrier)
  (hchartD : ∀ x, chartD x = F.ExpD x)
  (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
  (dynkinD : NilpotentDynkinExpansionInput F.D.modelSpace F.D.carrier)
  (hbijN : Function.Bijective F.ExpN) (hbijD : Function.Bijective F.ExpD)

set_option maxHeartbeats 1000000 in
omit [IsIsometricSMul G G] [ProperSpace G] in
private theorem assemble_uniform_bridge_point
    (hφ : ∀ d, F.action d = M.adjointGroupAutomorphism T F.N.equiv F.ExpN F.isExpN
      hbijN dynkinN (cartanLog H F.D.equiv F.ExpD hbijD d))
    {J K QI : Type} [Fintype J] [Fintype K] [Fintype QI]
    (b : Basis J ℝ (cartanRootIdeal H)) (C : Set (H →ₗ[ℝ] ℝ))
    (bI : Basis K ℝ (M.coneWordIdeal C))
    (bQ : Basis QI ℝ (cartanRootIdeal H ⧸ (M.coneWordIdeal C).toSubmodule))
    (lift : QI → cartanRootIdeal H)
    (cost : K → ℝ) (cell : Set (F.N.carrier × F.D.carrier))
    (u₂ : F.N.carrier) (d₂ : F.D.carrier) (g : G) (RE RB A δ r S RD : ℝ)
    (hRE : 0 ≤ RE) (hδ : 0 ≤ δ) (hr : 0 ≤ r)
    (habs : ∀ v, ‖b.equivFun v‖ ≤ RE * Real.exp (((A + 1) * δ) * r) →
      ∃ (i : M.coneWordIdeal C) (q : (cartanRootIdeal H) ⧸ (M.coneWordIdeal C).toSubmodule),
        u₂ * F.ExpN (F.N.equiv (cartanIdealAdjointAutomorphism T H
          (cartanLog H F.D.equiv F.ExpD hbijD d₂) v)) =
          F.ExpN (F.N.equiv (i : cartanRootIdeal H)) *
            F.ExpN (F.N.equiv (quotientLinearSection (M.coneWordIdeal C) bQ lift q)) ∧
        ‖(exponentialRescaleBasis bI cost r).equivFun i‖ ≤ S)
    (hprod : ∀ d, ‖(finBasis ℝ H).equivFun (cartanLog H F.D.equiv F.ExpD hbijD d)‖ ≤ RB →
      ‖(finBasis ℝ H).equivFun (cartanLog H F.D.equiv F.ExpD hbijD (d₂ * d))‖ ≤ RD)
    (hbridge : ∃ ub db, F.inclusionN ub * F.inclusionD db = g ∧ ∀ z ∈ cell,
      (∃ v, F.ExpN (F.N.equiv v) = ub * F.action db z.1 ∧
        ‖b.equivFun v‖ ≤ RE * Real.exp (A * δ * r)) ∧
      ‖(finBasis ℝ H).equivFun (cartanLog H F.D.equiv F.ExpD hbijD (db * z.2))‖ ≤ RB) :
    ∃ u d, F.inclusionN u * F.inclusionD d = (F.inclusionN u₂ * F.inclusionD d₂) * g ∧
      ∀ z ∈ cell,
        (∃ (i : M.coneWordIdeal C) (q : (cartanRootIdeal H) ⧸ (M.coneWordIdeal C).toSubmodule),
          u * F.action d z.1 = F.ExpN (F.N.equiv (i : cartanRootIdeal H)) *
            F.ExpN (F.N.equiv (quotientLinearSection (M.coneWordIdeal C) bQ lift q)) ∧
          ‖(exponentialRescaleBasis bI cost r).equivFun i‖ ≤ max S 0) ∧
        ‖(finBasis ℝ H).equivFun (cartanLog H F.D.equiv F.ExpD hbijD (d * z.2))‖ ≤ RD := by
  apply exists_thickened_factor_bridge_of_bounds F.action F.inclusionN F.inclusionD F.conjugation
    (F.ExpN ∘ F.N.equiv) (fun i : M.coneWordIdeal C => F.ExpN (F.N.equiv (i : cartanRootIdeal H)))
    (fun q => F.ExpN (F.N.equiv (quotientLinearSection (M.coneWordIdeal C) bQ lift q)))
    (fun v => ‖b.equivFun v‖)
    (fun d => ‖(finBasis ℝ H).equivFun (cartanLog H F.D.equiv F.ExpD hbijD d)‖)
    (fun i => ‖(exponentialRescaleBasis bI cost r).equivFun i‖ ≤ max S 0)
    (fun d => ‖(finBasis ℝ H).equivFun (cartanLog H F.D.equiv F.ExpD hbijD d)‖ ≤ RD)
    (fun _ => True) cell u₂ d₂ g RE RB A δ r hRE hδ hr
  · intro v hv
    obtain ⟨i, q, he, hi⟩ := habs v hv
    refine ⟨i, q, ?_, hi.trans (le_max_left _ _)⟩
    have ha : F.action d₂ (F.ExpN (F.N.equiv v)) =
        F.ExpN (F.N.equiv (cartanIdealAdjointAutomorphism T H
          (cartanLog H F.D.equiv F.ExpD hbijD d₂) v)) := by
      rw [hφ]
      exact integrateNilpotentLieEquiv_apply_exp F.N.equiv F.ExpN hbijN dynkinN F.isExpN
        M.bound_zero _ v
    rw [Function.comp_apply, ha]
    exact he
  · exact hprod
  · obtain ⟨u, d, he, hb⟩ := hbridge
    exact ⟨u, d, he, trivial, hb⟩

set_option maxHeartbeats 1000000 in
include hunimod hπExp hchartN hchartD dynkinN dynkinD in
theorem exists_uniform_thickened_bridge_lifts
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (γ₀ : M.Bases) {cell : Set (F.N.carrier × F.D.carrier)} (hcell : IsCompact cell)
    (hφ : ∀ d, F.action d = M.adjointGroupAutomorphism T F.N.equiv F.ExpN F.isExpN
      hbijN dynkinN
      (cartanLog H F.D.equiv F.ExpD
        hbijD d))
    (hpath : ∀ g : G, ∃ γ : ℝ → G, γ 0 = 1 ∧ γ 1 = g ∧
      ∀ t ∈ Icc (0 : ℝ) 1, ∀ u ∈ Icc (0 : ℝ) 1,
        dist (γ t) (γ u) ≤ dist 1 g * |t - u|)
    {Kπ : ℝ} (hKπ : 0 ≤ Kπ)
    (hLip : ∀ x y, ‖(π x).toAdd - (π y).toAdd‖ ≤ Kπ * dist x y)
    (C : Set (H →ₗ[ℝ] ℝ))
    {I J : Type} [Fintype I] [Fintype J]
    (bI : Basis I ℝ (M.coneWordIdeal C))
    (bQ : Basis J ℝ ((cartanRootIdeal H) ⧸ (M.coneWordIdeal C).toSubmodule))
    (lift : J → cartanRootIdeal H)
    (hlift : ∀ j, (M.coneWordIdeal C).toSubmodule.mkQ (lift j) = bQ j)
    {Q : Type} [Group Q]
    (ExpQ : ((cartanRootIdeal H) ⧸ (M.coneWordIdeal C).toSubmodule) → Q)
    (πQ : F.N.carrier →* Q)
    (hπQ : ∀ v, πQ (F.ExpN (F.N.equiv v)) = ExpQ ((M.coneWordIdeal C).toSubmodule.mkQ v))
    (hinjQ : Function.Injective ExpQ) (hzeroQ : ExpQ 0 = 1)
    {c : ℕ} (coeff : DynkinCoefficients c 2)
    (hcoeff : ∀ d w, |coeff d w| ≤ (2 : ℝ) ^ c)
    (hmul : ∀ v w, F.ExpN (F.N.equiv (finiteDynkinPolynomial coeff ![v, w])) =
      F.ExpN (F.N.equiv v) * F.ExpN (F.N.equiv w))
    (cost : I → ℝ) {lo : ℝ} (hlo : 0 < lo) (hcost : ∀ i, lo ≤ cost i)
    (K : ℝ) (hK : 0 ≤ K)
    (hbr : ∀ r : ℝ, 0 ≤ r → ∀ i j k,
      |(exponentialRescaleBasis
        (basisWithQuotientLifts (M.coneWordIdeal C).toSubmodule bI bQ lift hlift)
        (Sum.elim cost (fun _ => 0)) r).repr
          ⁅exponentialRescaleBasis
            (basisWithQuotientLifts (M.coneWordIdeal C).toSubmodule bI bQ lift hlift)
            (Sum.elim cost (fun _ => 0)) r i,
           exponentialRescaleBasis
            (basisWithQuotientLifts (M.coneWordIdeal C).toSubmodule bI bQ lift hlift)
            (Sum.elim cost (fun _ => 0)) r j⁆ k| ≤ K)
    : ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ (scale RN RH : ℕ → ℝ),
      StrictMono scale → Tendsto scale atTop atTop →
      (∀ n, 0 ≤ scale n) → (∀ n, 0 ≤ RN n) → (∀ n, 0 ≤ RH n) →
      HasSubexponentialUpperBoundSeq scale RN → HasSubexponentialUpperBoundSeq scale RH →
      ∃ S RD : ℕ → ℝ,
        (∀ n, 0 ≤ S n) ∧ (∀ n, 0 ≤ RD n) ∧
        HasSubexponentialUpperBoundSeq scale S ∧ HasSubexponentialUpperBoundSeq scale RD ∧
        ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
      ∀ᶠ n in atTop, ∀ (u₂ : F.N.carrier) (d₂ : F.D.carrier) (g : G),
        u₂ ∈ exponentialCoordinateBox (F.ExpN ∘ F.N.equiv)
          (exponentialRescaleBasis
            (basisWithQuotientLifts (M.coneWordIdeal C).toSubmodule bI bQ lift hlift)
            (Sum.elim cost (fun _ => 0)) (scale n)) (RN n) →
        ‖(finBasis ℝ H).equivFun (cartanLog H F.D.equiv F.ExpD
          hbijD d₂)‖ ≤ RH n →
        ‖(π (F.inclusionD d₂)).toAdd‖ ≤ δ * scale n →
        dist 1 g ≤ δ * scale n →
        ∃ (u : F.N.carrier) (d : F.D.carrier),
          F.inclusionN u * F.inclusionD d = (F.inclusionN u₂ * F.inclusionD d₂) * g ∧
          ∀ z ∈ cell,
            (∃ (i : M.coneWordIdeal C)
              (q : (cartanRootIdeal H) ⧸ (M.coneWordIdeal C).toSubmodule),
              u * F.action d z.1 = F.ExpN (F.N.equiv (i : cartanRootIdeal H)) *
                F.ExpN (F.N.equiv (quotientLinearSection (M.coneWordIdeal C) bQ lift q)) ∧
              ‖(exponentialRescaleBasis bI cost (scale n)).equivFun i‖ ≤ S n) ∧
            ‖(finBasis ℝ H).equivFun (cartanLog H F.D.equiv F.ExpD
              hbijD
              (d * z.2))‖ ≤ RD n := by
  let b := WordBasisSelections.basis M.letter M.wordList γ₀
  obtain ⟨A, hA, hmetric⟩ := M.exists_uniform_sequence_metric_factor_bounds_m
    T F hunimod eW π hπExp chartN hchartN chartD hchartD dynkinN dynkinD
    b₀ γ₀ b hcell hφ hpath hKπ hLip
  have hneg (v : cartanRootIdeal H) :
      F.ExpN (F.N.equiv (-v)) = (F.ExpN (F.N.equiv v))⁻¹ := by
    rw [map_neg, F.isExpN.map_neg]
  obtain ⟨δa, hδa, habs⟩ := M.exists_uniform_conjugated_bridge_ideal_bound
    T hunimod eW C b₀ bI bQ lift hlift (F.ExpN ∘ F.N.equiv) ExpQ πQ hπQ hinjQ
    hzeroQ hneg coeff hcoeff hmul cost hlo hcost K hK hbr
  let δ₀ := min 1 (δa / (A + 1))
  have hA1 : 0 < A + 1 := by linarith
  refine ⟨δ₀, lt_min zero_lt_one (div_pos hδa hA1), ?_⟩
  intro scale RN RH hs hscale hscale0 hRN0 hRH0 hRN hRH
  obtain ⟨RE, RB, hRE0, hRB0, hRE, hRB, hbridge⟩ := hmetric scale hscale hscale0
  obtain ⟨S, hS, habs⟩ := habs scale RN RH RE hs hscale hRN0 hRH0 hRN hRH hRE
  obtain ⟨RD, hRD0, hRD, hprod⟩ := exists_sequence_cartan_product_bound H F.D.equiv F.ExpD
    hbijD F.isExpD dynkinD scale RH RB hscale hRH0 hRB0 hRH hRB
  let S' := fun n => max (S n) 0
  have hS' : HasSubexponentialUpperBoundSeq scale S' := by
    intro ε hε
    filter_upwards [hS ε hε] with n hn
    exact max_le hn (Real.exp_nonneg _)
  refine ⟨S', RD, fun _ => le_max_right _ _, hRD0, hS', hRD, ?_⟩
  intro δ hδ hδle
  have hδ1 : δ ≤ 1 := hδle.trans (min_le_left _ _)
  have hδa' : (A + 1) * δ ≤ δa := by
    have hh := (le_div_iff₀ hA1).mp (hδle.trans (min_le_right _ _))
    nlinarith
  filter_upwards [habs ((A + 1) * δ) (mul_pos hA1 hδ) hδa'] with n hn
  intro u₂ d₂ g hu₂ hd₂ hh₂ hg
  have hheight : ‖eW (heightProjection T.character
      (cartanLog H F.D.equiv F.ExpD hbijD d₂ : GroupLieAlgebra (𝓘(ℝ, EG)) G))‖ ≤
      ((A + 1) * δ) * scale n := by
    rw [← F.inclusionD_height T eW π hπExp hbijD]
    exact hh₂.trans (mul_le_mul_of_nonneg_right (by nlinarith) (hscale0 n))
  apply assemble_uniform_bridge_point T M F dynkinN hbijN hbijD hφ b C bI bQ lift cost
    cell u₂ d₂ g (RE n) (RB n) A δ (scale n) (S n) (RD n) (hRE0 n) hδ.le (hscale0 n)
  · exact fun v hv => hn u₂ γ₀ (cartanLog H F.D.equiv F.ExpD hbijD d₂) v
      hu₂ hd₂ hheight hv
  · exact fun d hd => hprod n d₂ d hd₂ hd
  · obtain ⟨u, d, he, _, hb⟩ := hbridge δ hδ hδ1 n g hg
    exact ⟨u, d, he, hb⟩

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanUniformIntrinsicBridge
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instDecidableEqConeMixedWords _root_.OAI.PolycyclicRecognition.CartanWordModel.instFintypeConeMixedWords _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.CartanFactorModel.heightRay_zero _root_.OAI.PolycyclicRecognition.CartanFactorModel.realScaleProfile_apply _root_.OAI.PolycyclicRecognition.CartanFactorModel.sampledProbeProfile_apply _root_.OAI.PolycyclicRecognition.basisDynkinParameter_zero _root_.OAI.PolycyclicRecognition.cartanWeightDerivation_apply_root _root_.OAI.PolycyclicRecognition.dynkinRightTranslation_apply _root_.OAI.PolycyclicRecognition.dynkinRightTranslation_symm_apply _root_.OAI.PolycyclicRecognition.exponentialHomOfDynkin_apply_exp _root_.OAI.PolycyclicRecognition.exponentialQuotientSection_apply _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.modelNilradicalLinearAction_apply _root_.OAI.PolycyclicRecognition.modelNilradicalRotation_apply _root_.OAI.PolycyclicRecognition.modelNilradicalRotation_mul _root_.OAI.PolycyclicRecognition.modelNilradicalRotation_one _root_.OAI.PolycyclicRecognition.nilshadowWeightDerivation_symm _root_.OAI.PolycyclicRecognition.nilshadowWeightOperator_symm _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Intrinsic bridge absorption with the correct order of constants -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule Metric Set Filter
open scoped Manifold Topology

variable {EG G : Type} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [IsIsometricSMul G G] [ProperSpace G]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {ExpG : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H ExpG)
  (hunimod : ∀ x : GroupLieAlgebra (𝓘(ℝ, EG)) G,
    LinearMap.trace ℝ _ (ad ℝ _ x) = 0)
  {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  (eW : HeightSpace T.character ≃ₗ[ℝ] W) (π : G →* Multiplicative W)
  (hπExp : ∀ x, (π (ExpG x)).toAdd = eW (heightProjection T.character x))
  (chartN : GroupLieAlgebra (𝓘(ℝ, F.N.modelSpace)) F.N.carrier ≃ₜ F.N.carrier)
  (hchartN : ∀ x, chartN x = F.ExpN x)
  (chartD : GroupLieAlgebra (𝓘(ℝ, F.D.modelSpace)) F.D.carrier ≃ₜ F.D.carrier)
  (hchartD : ∀ x, chartD x = F.ExpD x)
  (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
  (dynkinD : NilpotentDynkinExpansionInput F.D.modelSpace F.D.carrier)
  (hbijN : Function.Bijective F.ExpN) (hbijD : Function.Bijective F.ExpD)

set_option maxHeartbeats 1000000 in
include hunimod hπExp hchartN hchartD dynkinN dynkinD in
theorem exists_uniform_intrinsic_bridge_lifts_oai
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (γ₀ : M.Bases) {cell : Set (F.N.carrier × F.D.carrier)} (hcell : IsCompact cell)
    (hφ : ∀ d, F.action d = M.adjointGroupAutomorphism T F.N.equiv F.ExpN F.isExpN
      hbijN dynkinN
      (cartanLog H F.D.equiv F.ExpD
        hbijD d))
    (hpath : ∀ g : G, ∃ γ : ℝ → G, γ 0 = 1 ∧ γ 1 = g ∧
      ∀ t ∈ Icc (0 : ℝ) 1, ∀ u ∈ Icc (0 : ℝ) 1,
        dist (γ t) (γ u) ≤ dist 1 g * |t - u|)
    {Kπ : ℝ} (hKπ : 0 ≤ Kπ)
    (hLip : ∀ x y, ‖(π x).toAdd - (π y).toAdd‖ ≤ Kπ * dist x y)
    (C : Set (H →ₗ[ℝ] ℝ))
    {I J : Type} [Fintype I] [Fintype J]
    (bI : Basis I ℝ (M.coneWordIdeal C))
    (bQ : Basis J ℝ ((cartanRootIdeal H) ⧸ (M.coneWordIdeal C).toSubmodule))
    (lift : J → cartanRootIdeal H)
    (hlift : ∀ j, (M.coneWordIdeal C).toSubmodule.mkQ (lift j) = bQ j)
    {Q : Type} [Group Q]
    (ExpQ : ((cartanRootIdeal H) ⧸ (M.coneWordIdeal C).toSubmodule) → Q)
    (πQ : F.N.carrier →* Q)
    (hπQ : ∀ v, πQ (F.ExpN (F.N.equiv v)) = ExpQ ((M.coneWordIdeal C).toSubmodule.mkQ v))
    (hinjQ : Function.Injective ExpQ) (hzeroQ : ExpQ 0 = 1)
    (cost : I → ℝ) {lo : ℝ} (hlo : 0 < lo) (hcost : ∀ i, lo ≤ cost i)
    (K : ℝ) (hK : 0 ≤ K)
    (hbr : ∀ r : ℝ, 0 ≤ r → ∀ i j k,
      |(exponentialRescaleBasis
        (basisWithQuotientLifts (M.coneWordIdeal C).toSubmodule bI bQ lift hlift)
        (Sum.elim cost (fun _ => 0)) r).repr
          ⁅exponentialRescaleBasis
            (basisWithQuotientLifts (M.coneWordIdeal C).toSubmodule bI bQ lift hlift)
            (Sum.elim cost (fun _ => 0)) r i,
           exponentialRescaleBasis
            (basisWithQuotientLifts (M.coneWordIdeal C).toSubmodule bI bQ lift hlift)
            (Sum.elim cost (fun _ => 0)) r j⁆ k| ≤ K)
    : ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ (scale RN RH : ℕ → ℝ),
      StrictMono scale → Tendsto scale atTop atTop →
      (∀ n, 0 ≤ scale n) → (∀ n, 0 ≤ RN n) → (∀ n, 0 ≤ RH n) →
      HasSubexponentialUpperBoundSeq scale RN → HasSubexponentialUpperBoundSeq scale RH →
      ∃ S RD : ℕ → ℝ,
        (∀ n, 0 ≤ S n) ∧ (∀ n, 0 ≤ RD n) ∧
        HasSubexponentialUpperBoundSeq scale S ∧ HasSubexponentialUpperBoundSeq scale RD ∧
        ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
      ∀ᶠ n in atTop, ∀ (u₂ : F.N.carrier) (d₂ : F.D.carrier) (g : G),
        u₂ ∈ exponentialCoordinateBox (F.ExpN ∘ F.N.equiv)
          (exponentialRescaleBasis
            (basisWithQuotientLifts (M.coneWordIdeal C).toSubmodule bI bQ lift hlift)
            (Sum.elim cost (fun _ => 0)) (scale n)) (RN n) →
        ‖(finBasis ℝ H).equivFun (cartanLog H F.D.equiv F.ExpD
          hbijD d₂)‖ ≤ RH n →
        ‖(π (F.inclusionD d₂)).toAdd‖ ≤ δ * scale n →
        dist 1 g ≤ δ * scale n →
        ∃ (u : F.N.carrier) (d : F.D.carrier),
          F.inclusionN u * F.inclusionD d = (F.inclusionN u₂ * F.inclusionD d₂) * g ∧
          ∀ z ∈ cell,
            (∃ (i : M.coneWordIdeal C)
              (q : (cartanRootIdeal H) ⧸ (M.coneWordIdeal C).toSubmodule),
              u * F.action d z.1 = F.ExpN (F.N.equiv (i : cartanRootIdeal H)) *
                F.ExpN (F.N.equiv (quotientLinearSection (M.coneWordIdeal C) bQ lift q)) ∧
              ‖(exponentialRescaleBasis bI cost (scale n)).equivFun i‖ ≤ S n) ∧
            ‖(finBasis ℝ H).equivFun (cartanLog H F.D.equiv F.ExpD
              hbijD
              (d * z.2))‖ ≤ RD n := by
  obtain ⟨coeff, hcoeff, hprod⟩ := model_finiteDynkinExpansion dynkinN F.N.equiv
    F.ExpN F.isExpN M.bound_zero 2
  have hmul (v w : cartanRootIdeal H) :
      F.ExpN (F.N.equiv (finiteDynkinPolynomial coeff ![v, w])) =
        F.ExpN (F.N.equiv v) * F.ExpN (F.N.equiv w) := by
    simpa using (hprod ![v, w]).symm
  exact M.exists_uniform_thickened_bridge_lifts T F hunimod eW π hπExp
    chartN hchartN chartD hchartD dynkinN dynkinD hbijN hbijD
    b₀ γ₀ hcell hφ hpath hKπ hLip C bI bQ lift hlift ExpQ πQ hπQ hinjQ hzeroQ
    coeff hcoeff hmul cost hlo hcost K hK hbr


end PolycyclicRecognition.CartanWordModel

end

end OAI
end

theorem solution : type_of% @OAI.PolycyclicRecognition.CartanWordModel.exists_uniform_intrinsic_bridge_lifts_oai := @OAI.PolycyclicRecognition.CartanWordModel.exists_uniform_intrinsic_bridge_lifts_oai
