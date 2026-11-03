-- Prove2me | solution 1 for OAI.PolycyclicRecognition.CartanWordModel.uniform_transversal_traces_of_boundary_comparisons
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-03T00:59:16.501926+00:00
-- url     : https://prove2.me/submissions/0c9f5f0f-8fd9-4433-bae2-21b299a8d9e1

import Mathlib
import Definitions.Def_PolycyclicRecognition
import Definitions.Def_OAIQ093D022

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

variable {L J : Type*} [LieRing L] [LieAlgebra ℝ L] [Fintype J]
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

theorem bracketWordLength_eq_nodes_add_one {I : Type*} (w : FreeMagma I) :
    bracketWordLength w = bracketWordNodes w + 1 := by
  induction w using FreeMagma.rec with
  | of i => rfl
  | mul u v hu hv => simp only [bracketWordLength, bracketWordNodes, hu, hv]; omega

/-- Evaluation of each Lie word is bounded by the number of its brackets and
letters. This is uniform over a family with bounded structure constants. -/
theorem norm_basis_evalBracketWord_le {I : Type*} (X : I → L)
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

@[simp] theorem rightNestedWord_length {I : Type*} (d : ℕ) (f : Fin (d + 1) → I) :
    bracketWordLength (rightNestedWord d f) = d + 1 := by
  rw [bracketWordLength_eq_nodes_add_one, rightNestedWord_nodes]

variable {L J : Type*} [LieRing L] [LieAlgebra ℝ L] [Fintype J]

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
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_PolynomialTripling
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instNonemptyBases _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_nonempty _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial upper growth supplies arbitrarily large tripling scales

Only an upper polynomial estimate is needed for the Haar averaging step:
there are arbitrarily large radii where tripling the radius has bounded
volume ratio. No full volume asymptotic or lower polynomial estimate is used.
-/

namespace PolycyclicRecognition

open Filter
open scoped Topology

/-- A positive sequence tending to zero cannot increase at every step. -/
theorem exists_adjacent_nonincrease_of_tendsto_zero
    (a : ℕ → ℝ) (ha : 0 < a 0) (hlim : Tendsto a atTop (𝓝 0)) :
    ∃ n, a (n + 1) ≤ a n := by
  by_contra! h
  have hmono : Monotone a := monotone_nat_of_le_succ (fun n => (h n).le)
  obtain ⟨n, hn⟩ := (hlim.eventually (eventually_lt_nhds ha)).exists
  exact (hmono (Nat.zero_le n)).not_gt hn

/-- An exponential upper bound forces one adjacent growth ratio below any
fixed larger exponential rate. -/
theorem exists_geometric_growth_ratio
    (v : ℕ → ℝ) {C B : ℝ} (hB : 0 < B)
    (hv : ∀ n, 0 ≤ v n) (hv0 : 0 < v 0)
    (hbound : ∀ n, v n ≤ C * B ^ n) :
    ∃ n, v (n + 1) ≤ (2 * B) * v n := by
  let a := fun n => v n / (2 * B) ^ n
  have ha (n : ℕ) : 0 ≤ a n := div_nonneg (hv n) (pow_pos (by positivity) n).le
  have hab (n : ℕ) : a n ≤ C * (1 / 2 : ℝ) ^ n := by
    dsimp only [a]
    calc
      v n / (2 * B) ^ n ≤ (C * B ^ n) / (2 * B) ^ n :=
        div_le_div_of_nonneg_right (hbound n) (pow_pos (by positivity) n).le
      _ = C * (B / (2 * B)) ^ n := by rw [div_pow]; ring
      _ = C * (1 / 2 : ℝ) ^ n := by congr 2; field_simp
  have hgeo : Tendsto (fun n : ℕ => C * (1 / 2 : ℝ) ^ n) atTop (𝓝 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num))
  have hlim : Tendsto a atTop (𝓝 0) := squeeze_zero ha hab hgeo
  obtain ⟨n, hn⟩ := exists_adjacent_nonincrease_of_tendsto_zero a (by simpa [a] using hv0) hlim
  have hden : 0 < (2 * B) ^ (n + 1) := pow_pos (by positivity) _
  have hp : (2 * B) ^ (n + 1) = (2 * B) ^ n * (2 * B) := pow_succ _ _
  have hh := (div_le_iff₀ hden).mp hn
  dsimp only [a] at hh
  rw [hp] at hh
  have he : (v n / (2 * B) ^ n) * ((2 * B) ^ n * (2 * B)) = (2 * B) * v n := by
    field_simp
  rw [he] at hh
  exact ⟨n, hh⟩

/-- Positive polynomial volume growth admits a tripling estimate at some
radius above every prescribed threshold. -/
theorem polynomial_tripling_at_arbitrarily_large_radii
    (v : ℝ → ℝ) {C : ℝ} (d : ℕ)
    (hv : ∀ r, 1 ≤ r → 0 < v r)
    (hbound : ∀ r, 1 ≤ r → v r ≤ C * r ^ d) :
    ∀ R : ℝ, ∃ T : ℝ, R ≤ T ∧ 1 ≤ T ∧ v (3 * T) ≤ (2 * (3 : ℝ) ^ d) * v T := by
  intro R
  let r := max R 1
  have hr : 1 ≤ r := le_max_right _ _
  have hn (n : ℕ) : 1 ≤ (3 : ℝ) ^ n * r := by
    have hp : 1 ≤ (3 : ℝ) ^ n := one_le_pow₀ (by norm_num)
    nlinarith
  obtain ⟨n, hratio⟩ := exists_geometric_growth_ratio (fun n => v ((3 : ℝ) ^ n * r))
    (C := C * r ^ d) (B := (3 : ℝ) ^ d) (by positivity)
    (fun n => (hv _ (hn n)).le) (by simpa using hv r hr) (by
      intro n
      calc
        v ((3 : ℝ) ^ n * r) ≤ C * ((3 : ℝ) ^ n * r) ^ d := hbound _ (hn n)
        _ = (C * r ^ d) * ((3 : ℝ) ^ d) ^ n := by rw [mul_pow, ← pow_mul, Nat.mul_comm n d, pow_mul]; ring)
  refine ⟨(3 : ℝ) ^ n * r, (le_max_left R 1).trans (by nlinarith [hn n, one_le_pow₀ (show (1 : ℝ) ≤ 3 by norm_num) (n := n)]), hn n, ?_⟩
  simpa only [pow_succ, mul_assoc, mul_left_comm, mul_comm] using hratio

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

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L]

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace G] [ChartedSpace E G] [Group G]
  [LieGroup (𝓘(ℝ, E)) ⊤ G] [T2Space G]

/-- The polynomial product estimate in any basis with bounded brackets. -/
theorem product_mem_exponentialCoordinateBox
    (dynkin : NilpotentDynkinExpansionInput E G)
    (e : L ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, E)) G)
    (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G) (hExp : IsGroupExponential Exp)
    {c n : ℕ} (hc : lowerCentralSeries ℝ L L c = ⊥)
    {J : Type*} [Fintype J] (b : Basis J ℝ L)
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
attribute [-simp] _root_.OAI.PolycyclicRecognition.chartExponentialFlow_zero _root_.OAI.PolycyclicRecognition.derivationSemidirectHom_apply _root_.OAI.PolycyclicRecognition.exponentialHomOfDynkin_apply_exp _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.integrateNilpotentLieEquiv_apply_exp _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
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

variable {G W : Type*} [Group G] [MetricSpace G] [IsIsometricSMul G G]
  [NormedAddCommGroup W]

/-- The increments telescope to the relative endpoint, with their actual
lengths controlled by the chain steps. -/
theorem BoundedHeightChain.exists_increment_list {π : G → W} {L M : ℝ}
    {m : ℕ} {x y : G} (h : BoundedHeightChain π L M m x y) :
    ∃ l : List G, l.length = m ∧ (∀ g ∈ l, dist (1 : G) g ≤ L) ∧ l.prod = x⁻¹ * y := by
  induction h with
  | nil x hx => exact ⟨[], rfl, by simp, by simp⟩
  | @cons m x y z hx hxy tail ih =>
    obtain ⟨l, hlen, hl, hprod⟩ := ih
    refine ⟨(x⁻¹ * y) :: l, by simp [hlen], ?_, ?_⟩
    · intro g hg
      rcases List.mem_cons.mp hg with rfl | hg
      · have hd := dist_mul_left x⁻¹ x y
        simpa only [inv_mul_cancel] using hd.trans_le hxy
      · exact hl g hg
    · simp only [List.prod_cons, hprod, mul_assoc, mul_inv_cancel_left]

omit [Group G] [IsIsometricSMul G G] in
/-- Append one final bounded step. -/
theorem BoundedHeightChain.snoc {π : G → W} {L M : ℝ}
    {m : ℕ} {x y z : G} (h : BoundedHeightChain π L M m x y)
    (hz : ‖π z‖ ≤ M) (hyz : dist y z ≤ L) :
    BoundedHeightChain π L M (m + 1) x z := by
  induction h with
  | nil x hx => exact .cons hx hyz (.nil z hz)
  | cons hx hxy _ ih => exact .cons hx hxy (ih hyz)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [ChartedSpace E G] [LieGroup (𝓘(ℝ, E)) ⊤ G]
  [ProperSpace G]

omit [IsIsometricSMul G G] [LieGroup (𝓘(ℝ, E)) ⊤ G] in
/-- Compact metric balls have bounded logarithms in any fixed exponential
coordinate basis. -/
theorem exists_bound_increment_log
    (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G)
    (chart : GroupLieAlgebra (𝓘(ℝ, E)) G ≃ₜ G) (hchart : ∀ x, chart x = Exp x)
    {J : Type*} [Fintype J] (b : Basis J ℝ (GroupLieAlgebra (𝓘(ℝ, E)) G))
    (L : ℝ) : ∃ R : ℝ, 0 ≤ R ∧ ∀ g, dist (1 : G) g ≤ L →
      ∃ x, Exp x = g ∧ ‖b.equivFun x‖ ≤ R := by
  have hc : Continuous (fun g => b.equivFun (chart.symm g)) :=
    b.equivFun.toContinuousLinearEquiv.continuous.comp chart.symm.continuous
  obtain ⟨R, hR⟩ := (isCompact_closedBall (1 : G) L).exists_bound_of_continuousOn
    hc.continuousOn
  refine ⟨max R 0, le_max_right _ _, ?_⟩
  intro g hg
  refine ⟨chart.symm g, ?_, ?_⟩
  · rw [← hchart, chart.apply_symm_apply]
  · exact (hR g (by simpa only [Metric.mem_closedBall, dist_comm] using hg)).trans
      (le_max_left _ _)

/-- The finite list of basis brackets always has a common bound. -/
theorem exists_basis_structureConstant_bound {L : Type*} [LieRing L] [LieAlgebra ℝ L]
    {J : Type*} [Fintype J] (b : Basis J ℝ L) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ i j l, |b.repr ⁅b i, b j⁆ l| ≤ C := by
  obtain ⟨C, hC⟩ := (Set.finite_range (fun p : J × J × J =>
    |b.repr ⁅b p.1, b p.2.1⁆ p.2.2|)).bddAbove
  exact ⟨max C 0, le_max_right _ _, fun i j l =>
    (hC ⟨(i, j, l), rfl⟩).trans (le_max_left _ _)⟩

/-- Bounded-step chains in the nilpotent group have polynomial logarithmic
coordinate size. The height function imposes no extra restriction here. -/
theorem exists_polynomial_chain_coordinate_bound
    (dynkin : NilpotentDynkinExpansionInput E G)
    (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G) (hExp : IsGroupExponential Exp)
    (chart : GroupLieAlgebra (𝓘(ℝ, E)) G ≃ₜ G) (hchart : ∀ x, chart x = Exp x)
    {c : ℕ} (hzero : lowerCentralSeries ℝ (GroupLieAlgebra (𝓘(ℝ, E)) G)
      (GroupLieAlgebra (𝓘(ℝ, E)) G) c = ⊥)
    {J : Type*} [Fintype J] (b : Basis J ℝ (GroupLieAlgebra (𝓘(ℝ, E)) G))
    (L : ℝ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (π : G → W) (M : ℝ) (m : ℕ) (x y : G),
      BoundedHeightChain π L M m x y →
      ∃ z, Exp z = x⁻¹ * y ∧ ‖b.equivFun z‖ ≤ A * (1 + (m : ℝ)) ^ c := by
  obtain ⟨R, hR, hlog⟩ := exists_bound_increment_log Exp chart hchart b L
  obtain ⟨C, hC, hbracket⟩ := exists_basis_structureConstant_bound b
  let A : ℝ := (c : ℝ) * 2 ^ c * (1 + (Fintype.card J : ℝ) ^ 2 * C) ^ c * (1 + R) ^ c
  refine ⟨A, by dsimp [A] <;> positivity, ?_⟩
  intro π M m x y hxy
  obtain ⟨l, hlen, hl, hprod⟩ := hxy.exists_increment_list
  have hg (i : Fin l.length) : l.get i ∈ exponentialCoordinateBox Exp b R :=
    hlog _ (hl _ (List.get_mem _ _))
  have hp := product_mem_exponentialCoordinateBox dynkin
    (LieEquiv.refl : GroupLieAlgebra (𝓘(ℝ, E)) G ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, E)) G) Exp hExp hzero b hC hR hbracket
    l.get hg
  rw [List.ofFn_get, hprod, hlen] at hp
  exact hp

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_HaarAveraging
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Averaging translated masses

The boundary argument averages a Radon measure over Haar translates.  The
identities below use genuine measures and measurable multiplication, including
the Tonelli step.  Invariance is required only of Haar measure, not of the
measure whose translated masses are being compared.
-/

namespace PolycyclicRecognition

open MeasureTheory MeasureTheory.Measure Set
open scoped ENNReal

variable {G : Type*} [Group G] [MeasurableSpace G]
  [MeasurableMul₂ G] [MeasurableInv G]

/-- Tonelli's identity for the average mass of translates. -/
theorem average_translate_eq (μ ρ : Measure G) [SFinite μ] [SFinite ρ]
    {E S : Set G} (hE : MeasurableSet E) :
    (∫⁻ z in S, ρ (leftTranslate E z) ∂μ) =
      ∫⁻ y, μ (S ∩ {z | z⁻¹ * y ∈ E}) ∂ρ := by
  have hm : Measurable (fun p : G × G => p.1⁻¹ * p.2) :=
    measurable_fst.inv.mul measurable_snd
  calc
    (∫⁻ z in S, ρ (leftTranslate E z) ∂μ) =
        ∫⁻ z in S, ∫⁻ y, E.indicator (fun _ => (1 : ℝ≥0∞)) (z⁻¹ * y) ∂ρ ∂μ := by
      congr 1
      funext z
      symm
      have hf : Measurable (fun y : G => z⁻¹ * y) :=
        measurable_const.mul measurable_id
      calc
        _ = 1 * ρ ((fun y : G => z⁻¹ * y) ⁻¹' E) :=
          lintegral_indicator_const_comp hf hE 1
        _ = ρ (leftTranslate E z) := by
          rw [one_mul]
          congr 1
    _ = ∫⁻ y, ∫⁻ z in S, E.indicator (fun _ => (1 : ℝ≥0∞)) (z⁻¹ * y) ∂μ ∂ρ :=
      lintegral_lintegral_swap ((measurable_const.indicator hE).comp hm).aemeasurable
    _ = ∫⁻ y, μ (S ∩ {z | z⁻¹ * y ∈ E}) ∂ρ := by
      congr 1
      funext y
      rw [lintegral_indicator_const_comp (f := fun z : G => z⁻¹ * y)
        (measurable_id.inv.mul measurable_const) hE 1]
      simp only [one_mul]
      have hs : MeasurableSet ((fun z : G => z⁻¹ * y) ⁻¹' E) :=
        hE.preimage (measurable_id.inv.mul measurable_const)
      rw [Measure.restrict_apply hs]
      congr 1
      ext z
      exact and_comm

/-- Unimodularity identifies the total mass of the averaging kernel. -/
theorem translate_kernel_mass (μ : Measure G) [IsInvInvariant μ] [IsMulRightInvariant μ]
    (E : Set G) (y : G) : μ {z | z⁻¹ * y ∈ E} = μ E := by
  change μ (Inv.inv ⁻¹' ((fun z => z * y) ⁻¹' E)) = μ E
  rw [measure_preimage_inv, measure_preimage_mul_right]

/-- The set-theoretic sandwich underlying the Haar averaging estimate.
`inner` consists of points whose entire averaging kernel lies in `S`, while
outside `outer` the kernel misses `S`. -/
theorem average_translate_sandwich
    (μ ρ : Measure G) [SFinite μ] [SFinite ρ]
    [IsInvInvariant μ] [IsMulRightInvariant μ]
    {E S inner outer : Set G} (hE : MeasurableSet E)
    (hi : MeasurableSet inner) (ho : MeasurableSet outer)
    (hin : ∀ y ∈ inner, ∀ z, z⁻¹ * y ∈ E → z ∈ S)
    (hout : ∀ y, ∀ z ∈ S, z⁻¹ * y ∈ E → y ∈ outer) :
    μ E * ρ inner ≤ (∫⁻ z in S, ρ (leftTranslate E z) ∂μ) ∧
      (∫⁻ z in S, ρ (leftTranslate E z) ∂μ) ≤ μ E * ρ outer := by
  rw [average_translate_eq μ ρ hE]
  constructor
  · calc
      μ E * ρ inner = ∫⁻ y, inner.indicator (fun _ => μ E) y ∂ρ := by
        rw [lintegral_indicator_const hi]
      _ ≤ _ := lintegral_mono fun y => by
        by_cases hy : y ∈ inner
        · rw [indicator_of_mem hy]
          have heq : S ∩ {z | z⁻¹ * y ∈ E} = {z | z⁻¹ * y ∈ E} :=
            inter_eq_right.mpr (fun z hz => hin y hy z hz)
          rw [heq, translate_kernel_mass]
        · rw [indicator_of_notMem hy]
          exact bot_le
  · calc
      _ ≤ ∫⁻ y, outer.indicator (fun _ => μ E) y ∂ρ := lintegral_mono fun y => by
        by_cases hy : y ∈ outer
        · rw [indicator_of_mem hy, ← translate_kernel_mass μ E y]
          exact measure_mono inter_subset_right
        · rw [indicator_of_notMem hy]
          have heq : S ∩ {z | z⁻¹ * y ∈ E} = ∅ := by
            apply eq_empty_iff_forall_notMem.mpr
            rintro z ⟨hz, he⟩
            exact hy (hout y z hz he)
          rw [heq, measure_empty]
      _ = μ E * ρ outer := lintegral_indicator_const ho _

/-- The metric version of the Tonelli sandwich. It uses the triangle
inequality for group length; commutativity is not required. -/
theorem ball_average_sandwich
    (μ ρ : Measure G) [SFinite μ] [SFinite ρ]
    [IsInvInvariant μ] [IsMulRightInvariant μ]
    (ℓ : GroupSeminorm G) (hℓ : Measurable ℓ)
    {E : Set G} (hE : MeasurableSet E) {R T : ℝ} (hR : ∀ e ∈ E, ℓ e ≤ R) :
    μ E * ρ (lengthBall ℓ (T - R)) ≤
        (∫⁻ z in lengthBall ℓ T, ρ (leftTranslate E z) ∂μ) ∧
      (∫⁻ z in lengthBall ℓ T, ρ (leftTranslate E z) ∂μ) ≤
        μ E * ρ (lengthBall ℓ (T + R)) := by
  apply average_translate_sandwich μ ρ hE
    (hℓ measurableSet_Iio) (hℓ measurableSet_Iio)
  · intro y hy z hz
    have he := hR (z⁻¹ * y) hz
    have hh := map_mul_le_add ℓ y (z⁻¹ * y)⁻¹
    rw [map_inv_eq_map] at hh
    simp only [mul_inv_rev, inv_inv, mul_inv_cancel_left] at hh
    change ℓ y < T - R at hy
    change ℓ z < T
    linarith
  · intro y z hz he
    have hh := map_mul_le_add ℓ z (z⁻¹ * y)
    rw [mul_inv_cancel_left] at hh
    have he' := hR (z⁻¹ * y) he
    change ℓ z < T at hz
    change ℓ y < T + R
    linarith

omit [MeasurableMul₂ G] [MeasurableInv G] in
/-- Integrating a uniform upper bound on all translated masses. -/
theorem average_translate_le (μ ρ : Measure G) {E S : Set G}
    {a K : ℝ≥0∞} (h : ∀ z, ρ (leftTranslate E z) ≤ K * a) :
    (∫⁻ z in S, ρ (leftTranslate E z) ∂μ) ≤ K * a * μ S := by
  calc
    _ ≤ ∫⁻ _ in S, K * a ∂μ := lintegral_mono h
    _ = _ := by rw [setLIntegral_const]

omit [MeasurableMul₂ G] [MeasurableInv G] in
/-- Integrating a uniform lower bound on all translated masses. -/
theorem le_mul_average_translate (μ ρ : Measure G) {E S : Set G}
    {a K : ℝ≥0∞} (hK : K ≠ ∞) (h : ∀ z, a ≤ K * ρ (leftTranslate E z)) :
    a * μ S ≤ K * (∫⁻ z in S, ρ (leftTranslate E z) ∂μ) := by
  calc
    _ = ∫⁻ _ in S, a ∂μ := (setLIntegral_const _ _).symm
    _ ≤ ∫⁻ z in S, K * ρ (leftTranslate E z) ∂μ := lintegral_mono h
    _ = _ := lintegral_const_mul' K _ hK

/-- Comparing two compact shapes needs only one finite ball of positive
measure and its volume growth bound. The radius may depend on both shapes. -/
theorem translated_mass_comparison_at_radius
    (μ ρ : Measure G) [SFinite μ] [SFinite ρ]
    [IsInvInvariant μ] [IsMulRightInvariant μ]
    (ℓ : GroupSeminorm G) (hℓ : Measurable ℓ)
    {E F : Set G} (hE : MeasurableSet E) (hF : MeasurableSet F)
    {T : ℝ} (hET : ∀ e ∈ E, ℓ e ≤ T) (hFT : ∀ f ∈ F, ℓ f ≤ T)
    {a b K D : ℝ≥0∞} (hK : K ≠ ∞)
    (ha : ∀ z, a ≤ K * ρ (leftTranslate E z))
    (hb : ∀ z, ρ (leftTranslate F z) ≤ K * b)
    (hvol0 : μ (lengthBall ℓ T) ≠ 0) (hvoltop : μ (lengthBall ℓ T) ≠ ∞)
    (hgrowth : μ (lengthBall ℓ (3 * T)) ≤ D * μ (lengthBall ℓ T)) :
    a * μ F ≤ (K * K * D) * b * μ E := by
  have h₁ := le_mul_average_translate (S := lengthBall ℓ T) μ ρ hK ha
  have h₂ := (ball_average_sandwich (T := T) μ ρ ℓ hℓ hE hET).2
  have h₃ := (ball_average_sandwich (T := 3 * T) μ ρ ℓ hℓ hF hFT).1
  have ht : 3 * T - T = T + T := by ring
  rw [ht] at h₃
  have h₄ := average_translate_le (S := lengthBall ℓ (3 * T)) μ ρ hb
  apply (ENNReal.mul_le_mul_iff_right hvol0 hvoltop).mp
  calc
    μ (lengthBall ℓ T) * (a * μ F) = μ F * (a * μ (lengthBall ℓ T)) := by ac_rfl
    _ ≤ μ F * (K * (∫⁻ z in lengthBall ℓ T, ρ (leftTranslate E z) ∂μ)) :=
      mul_le_mul_right h₁ _
    _ ≤ μ F * (K * (μ E * ρ (lengthBall ℓ (T + T)))) :=
      mul_le_mul_right (mul_le_mul_right h₂ K) _
    _ = K * μ E * (μ F * ρ (lengthBall ℓ (T + T))) := by ac_rfl
    _ ≤ K * μ E * (∫⁻ z in lengthBall ℓ (3 * T), ρ (leftTranslate F z) ∂μ) :=
      mul_le_mul_right h₃ _
    _ ≤ K * μ E * (K * b * μ (lengthBall ℓ (3 * T))) := mul_le_mul_right h₄ _
    _ = (K * K * b * μ E) * μ (lengthBall ℓ (3 * T)) := by ac_rfl
    _ ≤ (K * K * b * μ E) * (D * μ (lengthBall ℓ T)) := mul_le_mul_right hgrowth _
    _ = μ (lengthBall ℓ T) * ((K * K * D) * b * μ E) := by ac_rfl

end PolycyclicRecognition

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_HaarAveragingScales
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instNonemptyBases _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_nonempty _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Haar averaging along arbitrarily large good volume scales -/

namespace PolycyclicRecognition

open MeasureTheory MeasureTheory.Measure Set
open scoped ENNReal NNReal

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]

/-- One sufficiently large good radius for each pair of compact sets is
enough; the tripling bound need not hold at every large radius. -/
theorem haar_averaging_at_unbounded_scales
    (μ ρ : Measure G) [SFinite μ] [SFinite ρ]
    [IsInvInvariant μ] [IsMulRightInvariant μ]
    (ℓ : GroupSeminorm G) (hℓ : Measurable ℓ)
    {J : Type*} (E : J → Set G) (a : J → ℝ≥0∞)
    (hE : ∀ j, MeasurableSet (E j))
    (hbounded : ∀ j, ∃ R : ℝ, ∀ e ∈ E j, ℓ e ≤ R)
    {K D : ℝ≥0∞} (hK : K ≠ ∞)
    (hlower : ∀ j z, a j ≤ K * ρ (leftTranslate (E j) z))
    (hupper : ∀ j z, ρ (leftTranslate (E j) z) ≤ K * a j)
    (hballs : ∀ R : ℝ, ∃ T : ℝ, R ≤ T ∧
      μ (lengthBall ℓ T) ≠ 0 ∧ μ (lengthBall ℓ T) ≠ ∞ ∧
      μ (lengthBall ℓ (3 * T)) ≤ D * μ (lengthBall ℓ T)) :
    ∀ j k, a j * μ (E k) ≤ (K * K * D) * a k * μ (E j) := by
  intro j k
  obtain ⟨Rj, hj⟩ := hbounded j
  obtain ⟨Rk, hk⟩ := hbounded k
  obtain ⟨T, hT, hT0, hTfinite, htripling⟩ := hballs (max Rj Rk)
  exact translated_mass_comparison_at_radius μ ρ ℓ hℓ (hE j) (hE k)
    (fun e he => (hj e he).trans ((le_max_left _ _).trans hT))
    (fun e he => (hk e he).trans ((le_max_right _ _).trans hT))
    hK (hlower j) (hupper k) hT0 hTfinite htripling

/-- Compact boundary sets admit the same averaging comparison from
arbitrarily large radii with a common volume tripling bound. -/
theorem haar_averaging_compact_at_unbounded_scales
    [MetricSpace G] [BorelSpace G] [IsIsometricSMul G G]
    (μ ρ : Measure G) [SFinite μ] [SFinite ρ]
    [IsInvInvariant μ] [IsMulRightInvariant μ]
    {J : Type*} (E : J → Set G) (a : J → ℝ≥0∞)
    (hE : ∀ j, IsCompact (E j)) {K D : ℝ≥0∞} (hK : K ≠ ∞)
    (hlower : ∀ j z, a j ≤ K * ρ (leftTranslate (E j) z))
    (hupper : ∀ j z, ρ (leftTranslate (E j) z) ≤ K * a j)
    (hballs : ∀ R : ℝ, ∃ T : ℝ, R ≤ T ∧
      μ (Metric.ball 1 T) ≠ 0 ∧ μ (Metric.ball 1 T) ≠ ∞ ∧
      μ (Metric.ball 1 (3 * T)) ≤ D * μ (Metric.ball 1 T)) :
    ∀ j k, a j * μ (E k) ≤ (K * K * D) * a k * μ (E j) := by
  let ℓ : GroupSeminorm G := distanceLength
  have hℓ : Continuous ℓ := continuous_const.dist continuous_id
  have hb (r : ℝ) : lengthBall ℓ r = Metric.ball 1 r := by
    ext x
    change dist 1 x < r ↔ dist x 1 < r
    rw [dist_comm]
  refine haar_averaging_at_unbounded_scales μ ρ ℓ hℓ.measurable E a
    (fun j => (hE j).measurableSet) ?_ hK hlower hupper ?_
  · intro j
    obtain ⟨R, hR⟩ := (hE j).bddAbove_image hℓ.continuousOn
    exact ⟨R, fun e he => hR (mem_image_of_mem ℓ he)⟩
  · intro R
    simpa only [hb] using hballs R

/-- An upper polynomial volume bound and positivity/finiteness of balls
suffice for the compact Haar-averaging comparison. -/
theorem haar_averaging_compact_of_polynomial_volume
    [MetricSpace G] [BorelSpace G] [IsIsometricSMul G G]
    (μ ρ : Measure G) [SFinite μ] [SFinite ρ]
    [IsInvInvariant μ] [IsMulRightInvariant μ]
    {J : Type*} (E : J → Set G) (a : J → ℝ≥0∞)
    (hE : ∀ j, IsCompact (E j)) {K : ℝ≥0∞} (hK : K ≠ ∞)
    (hlower : ∀ j z, a j ≤ K * ρ (leftTranslate (E j) z))
    (hupper : ∀ j z, ρ (leftTranslate (E j) z) ≤ K * a j)
    (hballs : ∀ T : ℝ, 1 ≤ T → μ (Metric.ball 1 T) ≠ 0 ∧ μ (Metric.ball 1 T) ≠ ∞)
    {C : ℝ} (d : ℕ)
    (hvolume : ∀ T : ℝ, 1 ≤ T → (μ (Metric.ball 1 T)).toReal ≤ C * T ^ d) :
    ∀ j k, a j * μ (E k) ≤
      (K * K * ENNReal.ofReal (2 * (3 : ℝ) ^ d)) * a k * μ (E j) := by
  apply haar_averaging_compact_at_unbounded_scales μ ρ E a hE hK hlower hupper
  intro R
  obtain ⟨T, hRT, hT, htripling⟩ := polynomial_tripling_at_arbitrarily_large_radii
    (fun T => (μ (Metric.ball 1 T)).toReal) d
    (fun T hT => ENNReal.toReal_pos (hballs T hT).1 (hballs T hT).2) hvolume R
  refine ⟨T, hRT, (hballs T hT).1, (hballs T hT).2, ?_⟩
  have h3 : 1 ≤ 3 * T := by linarith
  apply (ENNReal.toReal_le_toReal (hballs (3 * T) h3).2
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hballs T hT).2)).mp
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity : 0 ≤ 2 * (3 : ℝ) ^ d)]
    using htripling

end PolycyclicRecognition

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_NilpotentHaarInput
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_countable _root_.OAI.PolycyclicRecognition.finitelyGeneratedSubgroupIndex_countable _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exponential-coordinate Haar measure

E. Le Donne, *Metric Lie Groups*, Graduate Texts in Mathematics 306,
Springer (2025), Theorem 9.4.7 (exponential coordinates) and Corollary 9.4.21.
https://doi.org/10.1007/978-3-031-98832-5_9

A global exponential chart identifies Haar measure on a simply connected
nilpotent Lie group with Lebesgue measure. The Euclidean determinant formula
then gives the volume of weighted boxes, including their scale factors.
-/

noncomputable section

namespace PolycyclicRecognition

open Module MeasureTheory
open scoped Manifold

variable (E G : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace G] [ChartedSpace E G] [Group G]
  [LieGroup (𝓘(ℝ, E)) ⊤ G]

variable {E G} [T2Space G] [SimplyConnectedSpace G] [MeasurableSpace G] [BorelSpace G]

/-- Normalize Haar measure using one exponential coordinate basis. -/
theorem exists_haar_exponential_cube_volume
    (haarInput : NilpotentExponentialHaarInput E G)
    (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G) (hExp : IsGroupExponential Exp)
    (hnil : LieRing.IsNilpotent (GroupLieAlgebra (𝓘(ℝ, E)) G))
    {n : ℕ} (b : Basis (Fin n) ℝ (GroupLieAlgebra (𝓘(ℝ, E)) G)) :
    ∃ (chart : GroupLieAlgebra (𝓘(ℝ, E)) G ≃ₜ G) (μ : Measure G),
      (∀ x, chart x = Exp x) ∧ μ.IsHaarMeasure ∧
      ∀ R : ℝ, 0 ≤ R → μ (exponentialCoordinateBox Exp b R) = ENNReal.ofReal (2 * R) ^ n := by
  obtain ⟨⟨chart, hchart⟩, hhaar⟩ := haarInput.2 Exp hExp hnil
  let f := Exp ∘ b.equivFun.symm
  let e : (Fin n → ℝ) ≃ₜ G :=
    b.equivFun.symm.toContinuousLinearEquiv.toHomeomorph.trans chart
  have hf : f = e := by
    funext t
    exact (hchart (b.equivFun.symm t)).symm
  have hmeas : MeasurableEmbedding f := by rw [hf]; exact e.measurableEmbedding
  refine ⟨chart, Measure.map f volume, hchart, hhaar n b, ?_⟩
  intro R hR
  rw [exponentialCoordinateBox_eq_cube_image Exp b R hR]
  change (Measure.map f volume) (f '' _) = _
  rw [hmeas.map_apply, Set.preimage_image_eq _ hmeas.injective, Real.volume_Icc_pi]
  simp only [sub_neg_eq_add, ← two_mul, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_NilpotentBallVolume
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.chartExponentialFlow_zero _root_.OAI.PolycyclicRecognition.derivationSemidirectHom_apply _root_.OAI.PolycyclicRecognition.exponentialHomOfDynkin_apply_exp _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.integrateNilpotentLieEquiv_apply_exp _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial volume upper bounds for nilpotent metric balls

Linear bounded-step chains, the finite Dynkin formula and exponential Haar
coordinates give the only volume estimate used by boundary averaging.
-/

noncomputable section

namespace PolycyclicRecognition

open Module LieModule MeasureTheory MeasureTheory.Measure Metric
open scoped Manifold ENNReal

/-- A finite sequence with controlled vertices and steps gives the inductive
chain used by the coordinate estimates. -/
theorem boundedHeightChain_of_sequence
    {X W : Type*} [MetricSpace X] [NormedAddCommGroup W]
    (π : X → W) (p : ℕ → X) {L M : ℝ} (n : ℕ)
    (hheight : ∀ i ≤ n, ‖π (p i)‖ ≤ M)
    (hstep : ∀ i < n, dist (p i) (p (i + 1)) ≤ L) :
    BoundedHeightChain π L M n (p 0) (p n) := by
  induction n with
  | zero => exact .nil _ (hheight 0 le_rfl)
  | succ n ih =>
    exact (ih (fun i hi => hheight i (hi.trans (Nat.le_succ n)))
      (fun i hi => hstep i (hi.trans (Nat.lt_succ_self n)))).snoc
      (hheight _ le_rfl) (hstep n (Nat.lt_succ_self n))

variable {G E : Type*} [Group G] [MetricSpace G] [IsIsometricSMul G G]
  [ProperSpace G] [MeasurableSpace G] [BorelSpace G]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [ChartedSpace E G] [LieGroup (𝓘(ℝ, E)) ⊤ G]

omit [MeasurableSpace G] [BorelSpace G] in
/-- Every large metric ball is contained in one polynomially growing
exponential coordinate cube. -/
theorem exists_polynomial_ball_coordinate_bound
    (chains : LinearMetricChains G)
    (dynkin : NilpotentDynkinExpansionInput E G)
    (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G) (hExp : IsGroupExponential Exp)
    (chart : GroupLieAlgebra (𝓘(ℝ, E)) G ≃ₜ G) (hchart : ∀ x, chart x = Exp x)
    {c : ℕ} (hzero : lowerCentralSeries ℝ (GroupLieAlgebra (𝓘(ℝ, E)) G)
      (GroupLieAlgebra (𝓘(ℝ, E)) G) c = ⊥)
    {J : Type*} [Fintype J] (b : Basis J ℝ (GroupLieAlgebra (𝓘(ℝ, E)) G)) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ R : ℝ, 1 ≤ R →
      ball (1 : G) R ⊆ exponentialCoordinateBox Exp b (D * R ^ c) := by
  obtain ⟨A, hA, hcoord⟩ := exists_polynomial_chain_coordinate_bound (W := ℝ)
    dynkin Exp hExp chart hchart hzero b chains.step
  have hs := chains.slope_nonneg
  have he := chains.error_nonneg
  let D := A * (1 + chains.slope + chains.error) ^ c
  refine ⟨D, by dsimp [D] <;> positivity, ?_⟩
  intro R hR g hg
  obtain ⟨n, p, hp0, hpn, hn, hp⟩ := chains.chain 1 g
  have hchain := boundedHeightChain_of_sequence (fun _ : G => (0 : ℝ)) p (M := 0) n
    (by intro i hi; simp) hp
  rw [hp0, hpn] at hchain
  obtain ⟨v, hv, hbound⟩ := hcoord (fun _ : G => (0 : ℝ)) 0 n 1 g hchain
  refine ⟨v, by simpa only [inv_one, one_mul] using hv, hbound.trans ?_⟩
  have hdist : dist (1 : G) g ≤ R := by simpa only [mem_ball, dist_comm] using hg.le
  have hn' : (n : ℝ) ≤ chains.slope * R + chains.error :=
    hn.trans (add_le_add (mul_le_mul_of_nonneg_left hdist chains.slope_nonneg) le_rfl)
  have hlen : 1 + (n : ℝ) ≤ (1 + chains.slope + chains.error) * R := by
    nlinarith [chains.error_nonneg, mul_nonneg chains.error_nonneg (sub_nonneg.mpr hR)]
  have hpow := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ 1 + n) hlen c
  have hh := mul_le_mul_of_nonneg_left hpow hA
  simpa only [mul_pow, D, mul_assoc] using hh

variable [SimplyConnectedSpace G]

/-- The concrete exponential Haar measure has polynomial ball-volume upper
growth. The exponent need not be the sharp homogeneous dimension. -/
theorem exists_haar_polynomial_ball_volume
    (chains : LinearMetricChains G)
    (dynkin : NilpotentDynkinExpansionInput E G)
    (haar : NilpotentExponentialHaarInput E G)
    (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G) (hExp : IsGroupExponential Exp)
    (hnil : LieRing.IsNilpotent (GroupLieAlgebra (𝓘(ℝ, E)) G)) :
    ∃ (μ : Measure G) (C : ℝ) (d : ℕ), μ.IsHaarMeasure ∧ 0 ≤ C ∧
      ∀ R : ℝ, 1 ≤ R → (μ (ball 1 R)).toReal ≤ C * R ^ d := by
  let b := Module.finBasis ℝ (GroupLieAlgebra (𝓘(ℝ, E)) G)
  obtain ⟨chart, μ, hchart, hμ, hvol⟩ := exists_haar_exponential_cube_volume haar Exp hExp hnil b
  let := hμ
  obtain ⟨c, hc⟩ := (LieModule.isNilpotent_iff ℝ
    (GroupLieAlgebra (𝓘(ℝ, E)) G) (GroupLieAlgebra (𝓘(ℝ, E)) G)).mp hnil
  obtain ⟨D, hD, hball⟩ := exists_polynomial_ball_coordinate_bound chains dynkin Exp hExp
    chart hchart hc b
  let n := finrank ℝ (GroupLieAlgebra (𝓘(ℝ, E)) G)
  refine ⟨μ, (2 * D) ^ n, c * n, hμ, by positivity, ?_⟩
  intro R hR
  have hDR : 0 ≤ D * R ^ c := mul_nonneg hD (pow_nonneg (by linarith) _)
  have hmass := measure_mono (μ := μ) (hball R hR)
  rw [hvol _ hDR] at hmass
  have hfinite : ENNReal.ofReal (2 * (D * R ^ c)) ^ n ≠ ∞ := by finiteness
  have hh := ENNReal.toReal_mono hfinite hmass
  simp only [ENNReal.toReal_pow, ENNReal.toReal_ofReal (mul_nonneg (show (0 : ℝ) ≤ 2 by norm_num) hDR)] at hh
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  simp only [mul_pow, pow_mul]
  ring

/-- Haar normalization only changes the polynomial coefficient. -/
theorem haar_polynomial_ball_volume
    [SecondCountableTopology G]
    (chains : LinearMetricChains G)
    (dynkin : NilpotentDynkinExpansionInput E G)
    (haar : NilpotentExponentialHaarInput E G)
    (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G) (hExp : IsGroupExponential Exp)
    (hnil : LieRing.IsNilpotent (GroupLieAlgebra (𝓘(ℝ, E)) G))
    (μ : Measure G) [μ.IsHaarMeasure] :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ d : ℕ,
      ∀ R : ℝ, 1 ≤ R → (μ (ball 1 R)).toReal ≤ C * R ^ d := by
  let : IsTopologicalGroup G := topologicalGroup_of_lieGroup (𝓘(ℝ, E)) ⊤
  obtain ⟨ν, C, d, hν, hC, hvol⟩ := exists_haar_polynomial_ball_volume chains dynkin haar Exp hExp hnil
  let := hν
  have heq := isMulLeftInvariant_eq_smul μ ν
  refine ⟨(haarScalarFactor μ ν : ℝ) * C, mul_nonneg (NNReal.coe_nonneg _) hC, d, ?_⟩
  intro R hR
  have hm := congrArg (fun τ : Measure G => τ (ball 1 R)) heq
  change μ (ball 1 R) = (haarScalarFactor μ ν) • ν (ball 1 R) at hm
  rw [hm]
  change ((haarScalarFactor μ ν : ℝ≥0∞) * ν (ball 1 R)).toReal ≤ _
  rw [ENNReal.toReal_mul, ENNReal.coe_toReal]
  exact (mul_le_mul_of_nonneg_left (hvol R hR) (NNReal.coe_nonneg _)).trans_eq (by ring)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_NilpotentHaarSymmetry
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_countable _root_.OAI.PolycyclicRecognition.finitelyGeneratedSubgroupIndex_countable _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Inversion and right invariance of any nilpotent Haar normalization -/

noncomputable section
namespace PolycyclicRecognition

open Module MeasureTheory MeasureTheory.Measure
open scoped Manifold

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace G] [ChartedSpace E G] [Group G]
  [LieGroup (𝓘(ℝ, E)) ⊤ G] [T2Space G] [SimplyConnectedSpace G]
  [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]

/-- Negation in exponential coordinates and uniqueness of Haar measure
prove inversion invariance for every Haar normalization. -/
theorem nilpotent_haar_isInvInvariant
    (haar : NilpotentExponentialHaarInput E G)
    (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G) (hExp : IsGroupExponential Exp)
    (hnil : LieRing.IsNilpotent (GroupLieAlgebra (𝓘(ℝ, E)) G))
    (μ : Measure G) [μ.IsHaarMeasure] : μ.IsInvInvariant := by
  let : IsTopologicalGroup G := topologicalGroup_of_lieGroup (𝓘(ℝ, E)) ⊤
  let : LocallyCompactSpace G := Manifold.locallyCompact_of_finiteDimensional (𝓘(ℝ, E))
  obtain ⟨⟨chart, hchart⟩, hhaar⟩ := haar.2 Exp hExp hnil
  let b := Module.finBasis ℝ (GroupLieAlgebra (𝓘(ℝ, E)) G)
  let f := Exp ∘ b.equivFun.symm
  let ν := Measure.map f volume
  let : ν.IsHaarMeasure := hhaar _ b
  have hf : Measurable f := by
    have he : f = chart ∘ b.equivFun.symm := by
      funext x
      exact (hchart _).symm
    rw [he]
    exact (chart.continuous.comp b.equivFun.symm.toContinuousLinearEquiv.continuous).measurable
  let : ν.IsInvInvariant := isInvInvariant_map_of_neg volume f hf (by
    intro x
    simp only [f, Function.comp_apply, map_neg, hExp.map_neg])
  have heq : μ = haarScalarFactor μ ν • ν := isMulLeftInvariant_eq_smul μ ν
  constructor
  change Measure.map Inv.inv μ = μ
  calc
    Measure.map Inv.inv μ = Measure.map Inv.inv (haarScalarFactor μ ν • ν) :=
      congrArg (Measure.map Inv.inv) heq
    _ = haarScalarFactor μ ν • Measure.map Inv.inv ν :=
      Measure.map_smul _ _ _
    _ = haarScalarFactor μ ν • ν := by rw [map_inv_eq_self]
    _ = μ := heq.symm

/-- Inversion changes left Haar invariance into right invariance. -/
theorem nilpotent_haar_isMulRightInvariant
    (haar : NilpotentExponentialHaarInput E G)
    (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G) (hExp : IsGroupExponential Exp)
    (hnil : LieRing.IsNilpotent (GroupLieAlgebra (𝓘(ℝ, E)) G))
    (μ : Measure G) [μ.IsHaarMeasure] : μ.IsMulRightInvariant := by
  let : IsTopologicalGroup G := topologicalGroup_of_lieGroup (𝓘(ℝ, E)) ⊤
  let : μ.IsInvInvariant := nilpotent_haar_isInvInvariant haar Exp hExp hnil μ
  have hi : μ.inv = μ := Measure.inv_eq_self μ
  rw [← hi]
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_BoundaryHeight
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Scalar and vector boundary height estimates

Haar-volume distortion on ray quotients yields additive trace bounds after
taking logarithms. Finitely many spanning traces then bound the full height
error. A linear coefficient compatible with a sublinear error is unique.
-/

namespace PolycyclicRecognition

/-- Uniform multiplicative comparison of positive quantities bounds the
difference of their logarithms. -/
theorem abs_log_sub_le_of_comparison {a b K : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hK : 0 < K) (hab : a ≤ K * b) (hba : b ≤ K * a) :
    |Real.log a - Real.log b| ≤ Real.log K := by
  apply abs_sub_le_iff.mpr
  constructor
  · have h := Real.log_le_log ha hab
    rw [Real.log_mul hK.ne' hb.ne'] at h
    linarith
  · have h := Real.log_le_log hb hba
    rw [Real.log_mul hK.ne' ha.ne'] at h
    linarith

end PolycyclicRecognition

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_BoundaryImageMass
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Absolute boundary masses from compact image sandwiches -/

noncomputable section
namespace PolycyclicRecognition

open MeasureTheory Set
open scoped ENNReal

/-- A bounded change of scalar height changes its exponential mass by one
uniform multiplicative constant. -/
theorem exponential_mass_bounds_of_abs_sub_le
    {a b K C : ℝ} {m : ℝ≥0∞} (hK : 0 ≤ K)
    (hab : |a - b| ≤ C)
    (hlower : ENNReal.ofReal (Real.exp a) ≤ ENNReal.ofReal K * m)
    (hupper : m ≤ ENNReal.ofReal K * ENNReal.ofReal (Real.exp a)) :
    ENNReal.ofReal (Real.exp b) ≤ ENNReal.ofReal (K * Real.exp C) * m ∧
      m ≤ ENNReal.ofReal (K * Real.exp C) * ENNReal.ofReal (Real.exp b) := by
  have ha : a ≤ C + b := by have := le_abs_self (a - b); linarith
  have hb : b ≤ C + a := by have := neg_le_abs (a - b); linarith
  have ha' : ENNReal.ofReal (Real.exp a) ≤
      ENNReal.ofReal (Real.exp C) * ENNReal.ofReal (Real.exp b) := by
    rw [← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add]
    exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ha)
  have hb' : ENNReal.ofReal (Real.exp b) ≤
      ENNReal.ofReal (Real.exp C) * ENNReal.ofReal (Real.exp a) := by
    rw [← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add]
    exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr hb)
  rw [ENNReal.ofReal_mul hK]
  constructor
  · have hh := mul_le_mul' (le_refl (ENNReal.ofReal (Real.exp C))) hlower
    exact hb'.trans (by simpa only [mul_assoc, mul_left_comm, mul_comm] using hh)
  · have hh := mul_le_mul' (le_refl (ENNReal.ofReal K)) ha'
    exact hupper.trans (by simpa only [mul_assoc] using hh)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_BoundaryTranslateMass
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform translated masses from the nilpotent leaf bound -/

noncomputable section
namespace PolycyclicRecognition

open Set MeasureTheory
open scoped ENNReal

/-- The preimage description of a translate agrees with its multiplication
image, including for nonmeasurable sets. -/
theorem leftTranslate_eq_mul_image
    {S : Type*} [Group S] [MeasurableSpace S] [MeasurableMul₂ S] [MeasurableInv S]
    (E : Set S) (z : S) : leftTranslate E z = (fun x => z * x) '' E := by
  ext y
  constructor
  · intro hy
    exact ⟨z⁻¹ * y, hy, by simp⟩
  · rintro ⟨x, hx, rfl⟩
    simpa only [leftTranslate, mem_ofPred_eq, inv_mul_cancel_left] using hx

/-- Pulling Haar measure back by a boundary homeomorphism measures precisely
its image sets; absolute continuity is unnecessary. -/
theorem boundary_pullback_measure_apply
    {S T : Type*} [TopologicalSpace S] [TopologicalSpace T]
    [MeasurableSpace S] [MeasurableSpace T] [BorelSpace S] [BorelSpace T]
    (B : S ≃ₜ T) (μ : Measure T) (E : Set S) :
    Measure.map B.symm μ E = μ (B '' E) := by
  rw [B.symm.measurableEmbedding.map_apply, B.preimage_symm]

/-- Every source quotient translation lifts to a nilpotent element. The leaf
bound then makes all translates of a fixed Cartan image have comparable mass.
The comparison constant is uniform in both the map and the Cartan parameter. -/
theorem boundary_translated_mass_bounds
    {P G N S T D : Type*} [Group G] [Group N] [Group S]
    [TopologicalSpace S] [TopologicalSpace T]
    [MeasurableSpace S] [MeasurableSpace T] [BorelSpace S] [BorelSpace T]
    [MeasurableMul₂ S] [MeasurableInv S]
    (act : G →* Equiv.Perm S) (ι : N →* G) (π : N →* S)
    (hπ : Function.Surjective π) (hact : ∀ n x, act (ι n) x = π n * x)
    (B : P → S ≃ₜ T) (μ : Measure T) (f : P → G → G) (height : G → ℝ)
    (d : D → G) (U : Set S) {K C : ℝ} (hK : 0 < K)
    (hmass : ∀ p x,
      ENNReal.ofReal (Real.exp (height (f p x))) ≤
        ENNReal.ofReal K * μ (B p '' (act x '' U)) ∧
      μ (B p '' (act x '' U)) ≤
        ENNReal.ofReal K * ENNReal.ofReal (Real.exp (height (f p x))))
    (hleaf : ∀ p n j, |height (f p (ι n * d j)) - height (f p (d j))| ≤ C) :
    ∃ K' : ℝ, 0 < K' ∧ ∀ p j z,
      ENNReal.ofReal (Real.exp (height (f p (d j)))) ≤
        ENNReal.ofReal K' * (Measure.map (B p).symm μ) (leftTranslate (act (d j) '' U) z) ∧
      (Measure.map (B p).symm μ) (leftTranslate (act (d j) '' U) z) ≤
        ENNReal.ofReal K' * ENNReal.ofReal (Real.exp (height (f p (d j)))) := by
  refine ⟨K * Real.exp C, mul_pos hK (Real.exp_pos _), ?_⟩
  intro p j z
  obtain ⟨n, rfl⟩ := hπ z
  have hset : leftTranslate (act (d j) '' U) (π n) = act (ι n * d j) '' U := by
    rw [leftTranslate_eq_mul_image, image_image]
    congr 1
    funext u
    simp only [map_mul, Equiv.Perm.mul_apply, hact]
  rw [boundary_pullback_measure_apply, hset]
  exact exponential_mass_bounds_of_abs_sub_le hK.le (hleaf p n j)
    (hmass p (ι n * d j)).1 (hmass p (ι n * d j)).2

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_NilpotentBoundaryAveraging
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.chartExponentialFlow_zero _root_.OAI.PolycyclicRecognition.derivationSemidirectHom_apply _root_.OAI.PolycyclicRecognition.exponentialHomOfDynkin_apply_exp _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.integrateNilpotentLieEquiv_apply_exp _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Boundary trace comparison on actual nilpotent groups

This proves the averaging step from the explicit published exponential inputs
and the already chosen proper chain metric. No doubling premise is retained.
-/

noncomputable section
namespace PolycyclicRecognition

open Module MeasureTheory MeasureTheory.Measure Metric
open scoped Manifold ENNReal NNReal

variable {G E J P : Type*} [Group G] [MetricSpace G] [IsIsometricSMul G G]
  [ProperSpace G] [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [ChartedSpace E G] [LieGroup (𝓘(ℝ, E)) ⊤ G] [SimplyConnectedSpace G]

/-- Uniform translated boundary masses determine their exponential volume
characters, with a bound independent of the compact sets' diameters. -/
theorem trace_bound_of_nilpotent_boundary_masses
    (chains : LinearMetricChains G)
    (dynkin : NilpotentDynkinExpansionInput E G)
    (haar : NilpotentExponentialHaarInput E G)
    (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G) (hExp : IsGroupExponential Exp)
    (hnil : LieRing.IsNilpotent (GroupLieAlgebra (𝓘(ℝ, E)) G))
    (μ : Measure G) (ρ : P → Measure G) [μ.IsHaarMeasure] [∀ p, SFinite (ρ p)]
    (sets : J → Set G) (source : J → ℝ) (target : P → J → ℝ)
    (hsets : ∀ j, IsCompact (sets j)) {c K : ℝ} (hc : 0 < c) (hK : 0 < K)
    (hvolume : ∀ j, μ (sets j) = ENNReal.ofReal (c * Real.exp (source j)))
    (hlower : ∀ p j z, ENNReal.ofReal (Real.exp (target p j)) ≤
      ENNReal.ofReal K * ρ p (leftTranslate (sets j) z))
    (hupper : ∀ p j z, ρ p (leftTranslate (sets j) z) ≤
      ENNReal.ofReal K * ENNReal.ofReal (Real.exp (target p j))) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ p j j₀,
      |(target p j - target p j₀) - (source j - source j₀)| ≤ B := by
  let : IsTopologicalGroup G := topologicalGroup_of_lieGroup (𝓘(ℝ, E)) ⊤
  let : μ.IsInvInvariant := nilpotent_haar_isInvInvariant haar Exp hExp hnil μ
  let : μ.IsMulRightInvariant := nilpotent_haar_isMulRightInvariant haar Exp hExp hnil μ
  obtain ⟨C, _, d, hvol⟩ := haar_polynomial_ball_volume chains dynkin haar Exp hExp hnil μ
  let D : ℝ := 2 * (3 : ℝ) ^ d
  have hD : 0 < D := by dsimp [D] <;> positivity
  have hcmp (p : P) := haar_averaging_compact_of_polynomial_volume μ (ρ p) sets
    (fun j => ENNReal.ofReal (Real.exp (target p j))) hsets ENNReal.ofReal_ne_top
    (hlower p) (hupper p) (fun R hR =>
      ⟨(measure_ball_pos μ 1 (by linarith : 0 < R)).ne', measure_ball_ne_top⟩) d hvol
  have hreal (p : P) (j k : J) :
      Real.exp (target p j) * Real.exp (source k) ≤
        (K * K * D) * (Real.exp (target p k) * Real.exp (source j)) := by
    have h := hcmp p j k
    rw [hvolume j, hvolume k] at h
    change ENNReal.ofReal (Real.exp (target p j)) *
        ENNReal.ofReal (c * Real.exp (source k)) ≤
      (ENNReal.ofReal K * ENNReal.ofReal K * ENNReal.ofReal D) *
        ENNReal.ofReal (Real.exp (target p k)) *
        ENNReal.ofReal (c * Real.exp (source j)) at h
    have h' := ENNReal.toReal_mono (by finiteness) h
    simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.exp_pos _).le,
      ENNReal.toReal_ofReal hK.le, ENNReal.toReal_ofReal hD.le,
      ENNReal.toReal_ofReal (mul_pos hc (Real.exp_pos _)).le] at h'
    apply (mul_le_mul_iff_right₀ hc).mp
    first | (convert h' using 1 <;> first | (with_reducible_and_instances rfl) | ring) | exact (le_of_eq (by ring)).trans (h'.trans (le_of_eq (by ring)))
  refine ⟨max 0 (Real.log (K * K * D)), le_max_left _ _, ?_⟩
  intro p j j₀
  have h := abs_log_sub_le_of_comparison
    (mul_pos (Real.exp_pos (target p j)) (Real.exp_pos (source j₀)))
    (mul_pos (Real.exp_pos (target p j₀)) (Real.exp_pos (source j)))
    (by positivity : 0 < K * K * D) (hreal p j j₀) (hreal p j₀ j)
  simp only [Real.log_mul (Real.exp_ne_zero _) (Real.exp_ne_zero _), Real.log_exp] at h
  apply (show |(target p j - target p j₀) - (source j - source j₀)| ≤
      Real.log (K * K * D) from ?_).trans (le_max_right _ _)
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  ring

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_BoundaryAveragedTrace
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The transversal trace bound from actual boundary maps and leaf bounds -/

noncomputable section
namespace PolycyclicRecognition

open MeasureTheory Set
open scoped Manifold ENNReal

variable {P G N S T D ES : Type*} [Group G] [Group N] [Group S]
  [MetricSpace S] [IsIsometricSMul S S] [ProperSpace S]
  [MeasurableSpace S] [BorelSpace S] [SecondCountableTopology S]
  [NormedAddCommGroup ES] [NormedSpace ℝ ES] [FiniteDimensional ℝ ES]
  [ChartedSpace ES S] [LieGroup (𝓘(ℝ, ES)) ⊤ S] [SimplyConnectedSpace S]
  [TopologicalSpace T] [MeasurableSpace T] [BorelSpace T]

/-- Boundary image masses and the leaf-height estimate imply a uniform
transversal trace comparison. The actual homeomorphisms supply the measures;
the nilpotent exponential inputs discharge all metric-volume obligations. -/
theorem boundary_averaged_transversal_trace
    (chains : LinearMetricChains S)
    (dynkin : NilpotentDynkinExpansionInput ES S)
    (haar : NilpotentExponentialHaarInput ES S)
    (Exp : GroupLieAlgebra (𝓘(ℝ, ES)) S → S) (hExp : IsGroupExponential Exp)
    (hnil : LieRing.IsNilpotent (GroupLieAlgebra (𝓘(ℝ, ES)) S))
    (μS : Measure S) [μS.IsHaarMeasure] (μT : Measure T) [SFinite μT]
    (act : G →* Equiv.Perm S) (hcont : ∀ x, Continuous (act x))
    (ι : N →* G) (π : N →* S) (hπ : Function.Surjective π)
    (hact : ∀ n x, act (ι n) x = π n * x)
    (B : P → S ≃ₜ T) (f : P → G → G) (height : G → ℝ)
    (d : D → G) (source : D → ℝ) (U : Set S) (hU : IsCompact U)
    {c K C : ℝ} (hc : 0 < c) (hK : 0 < K)
    (hsource : ∀ j, μS (act (d j) '' U) = ENNReal.ofReal (c * Real.exp (source j)))
    (hmass : ∀ p x,
      ENNReal.ofReal (Real.exp (height (f p x))) ≤
        ENNReal.ofReal K * μT (B p '' (act x '' U)) ∧
      μT (B p '' (act x '' U)) ≤
        ENNReal.ofReal K * ENNReal.ofReal (Real.exp (height (f p x))))
    (hleaf : ∀ p n j, |height (f p (ι n * d j)) - height (f p (d j))| ≤ C) :
    ∃ bound : ℝ, 0 ≤ bound ∧ ∀ p j j₀,
      |(height (f p (d j)) - height (f p (d j₀))) - (source j - source j₀)| ≤ bound := by
  let : IsTopologicalGroup S := topologicalGroup_of_lieGroup (𝓘(ℝ, ES)) ⊤
  obtain ⟨K', hK', hmass'⟩ := boundary_translated_mass_bounds act ι π hπ hact
    B μT f height d U hK hmass hleaf
  exact trace_bound_of_nilpotent_boundary_masses chains dynkin haar Exp hExp hnil
    μS (fun p => Measure.map (B p).symm μT) (fun j => act (d j) '' U)
    source (fun p j => height (f p (d j))) (fun j => hU.image (hcont (d j))) hc hK'
    hsource (fun p j z => (hmass' p j z).1) (fun p j z => (hmass' p j z).2)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_LieModelMetric
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Compatible metrics for the solvable Lie model

The metric existence input is the precise specialization of Cornulier–de
la Harpe, *Metric Geometry of Locally Compact Groups*, EMS Tracts in
Mathematics 25 (2016), Proposition 4.B.9, p.108: a second-countable locally
compact group is compactly generated if and only if it admits a proper
compatible left-invariant large-scale-geodesic metric.

We prove compact generation from a compact identity neighborhood and
connectedness. The metric-existence input is separate from Dekimpe's
lattice-realization theorem and contains no recognition assertion.
-/

noncomputable section

namespace PolycyclicRecognition

open Set Filter Topology
open scoped Manifold

namespace ProperChainMetric

variable {G : Type*} [Group G] [TopologicalSpace G] (d : ProperChainMetric G)

theorem proper_compatibleMetric : letI := d.compatibleMetric; ProperSpace G := by
  rw [d.compatibleMetric_eq]
  exact d.proper

theorem isometric_compatibleMetric : letI := d.compatibleMetric; IsIsometricSMul G G := by
  rw [d.compatibleMetric_eq]
  exact d.leftInvariant

end ProperChainMetric

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_BoundaryPublishedMetricAveraging
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The published proper chain metric discharges the averaging metric -/

noncomputable section
namespace PolycyclicRecognition

open MeasureTheory Set
open scoped Manifold ENNReal

variable {P G N T D ES : Type*} {S : Type} [Group G] [Group N] [Group S]
  [TopologicalSpace S] [T2Space S]
  [MeasurableSpace S] [BorelSpace S] [SecondCountableTopology S]
  [NormedAddCommGroup ES] [NormedSpace ℝ ES] [FiniteDimensional ℝ ES]
  [ChartedSpace ES S] [LieGroup (𝓘(ℝ, ES)) ⊤ S] [SimplyConnectedSpace S]
  [TopologicalSpace T] [MeasurableSpace T] [BorelSpace T]

/-- Only the existing proper chain metric input is needed on this connected
nilpotent quotient; its topology is preserved before applying averaging. -/
theorem boundary_averaged_trace_of_published_metric
    (metricInput : GeodesicMetricExistenceInput)
    (dynkin : NilpotentDynkinExpansionInput ES S)
    (haar : NilpotentExponentialHaarInput ES S)
    (Exp : GroupLieAlgebra (𝓘(ℝ, ES)) S → S) (hExp : IsGroupExponential Exp)
    (hnil : LieRing.IsNilpotent (GroupLieAlgebra (𝓘(ℝ, ES)) S))
    (μS : Measure S) [μS.IsHaarMeasure] (μT : Measure T) [SFinite μT]
    (act : G →* Equiv.Perm S) (hcont : ∀ x, Continuous (act x))
    (ι : N →* G) (π : N →* S) (hπ : Function.Surjective π)
    (hact : ∀ n x, act (ι n) x = π n * x)
    (B : P → S ≃ₜ T) (f : P → G → G) (height : G → ℝ)
    (d : D → G) (source : D → ℝ) (U : Set S) (hU : IsCompact U)
    {c K C : ℝ} (hc : 0 < c) (hK : 0 < K)
    (hsource : ∀ j, μS (act (d j) '' U) = ENNReal.ofReal (c * Real.exp (source j)))
    (hmass : ∀ p x,
      ENNReal.ofReal (Real.exp (height (f p x))) ≤
        ENNReal.ofReal K * μT (B p '' (act x '' U)) ∧
      μT (B p '' (act x '' U)) ≤
        ENNReal.ofReal K * ENNReal.ofReal (Real.exp (height (f p x))))
    (hleaf : ∀ p n j, |height (f p (ι n * d j)) - height (f p (d j))| ≤ C) :
    ∃ bound : ℝ, 0 ≤ bound ∧ ∀ p j j₀,
      |(height (f p (d j)) - height (f p (d j₀))) - (source j - source j₀)| ≤ bound := by
  let : IsTopologicalGroup S := topologicalGroup_of_lieGroup (𝓘(ℝ, ES)) ⊤
  let : LocallyCompactSpace S := Manifold.locallyCompact_of_finiteDimensional (𝓘(ℝ, ES))
  let dS : ProperChainMetric S := Classical.choice
    (metricInput S (exists_compact_generating_set S))
  let : MetricSpace S := dS.compatibleMetric
  let : ProperSpace S := dS.proper_compatibleMetric
  let : IsIsometricSMul S S := dS.isometric_compatibleMetric
  exact boundary_averaged_transversal_trace dS.chains_compatibleMetric dynkin haar Exp hExp hnil
    μS μT act hcont ι π hπ hact B f height d source U hU hc hK hsource hmass hleaf

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_BoundaryVolumeAveraging
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Averaging the constructed boundary volume comparison -/

noncomputable section
namespace PolycyclicRecognition

open Set MeasureTheory TopologicalSpace
open scoped Manifold ENNReal

variable {G U W P N D ES : Type*} {S : Type} [Group G] [Group S] [Group U] [Group N]
  [TopologicalSpace S] [T2Space S] [MeasurableSpace S] [BorelSpace S]
  [SecondCountableTopology S]
  [TopologicalSpace U] [MeasurableSpace U] [BorelSpace U]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  [NormedAddCommGroup ES] [NormedSpace ℝ ES] [FiniteDimensional ℝ ES]
  [ChartedSpace ES S] [LieGroup (𝓘(ℝ, ES)) ⊤ S] [SimplyConnectedSpace S]
  {actS : G →* Equiv.Perm S} {actT : G →* Equiv.Perm U}
  {αS αT : W →L[ℝ] ℝ} {height : G →* Multiplicative W} {f : P → G → G}
  (C : BoundaryVolumeComparison actS actT αS αT height f)

/-- No metric or doubling condition on the boundary is assumed: the existing
published metric input and nilpotent exponential inputs supply them. -/
theorem BoundaryVolumeComparison.averaged_trace [SFinite C.targetMeasure]
    (metricInput : GeodesicMetricExistenceInput)
    (dynkin : NilpotentDynkinExpansionInput ES S)
    (haar : NilpotentExponentialHaarInput ES S)
    (Exp : GroupLieAlgebra (𝓘(ℝ, ES)) S → S) (hExp : IsGroupExponential Exp)
    (hnil : LieRing.IsNilpotent (GroupLieAlgebra (𝓘(ℝ, ES)) S))
    (hcont : ∀ x, Continuous (actS x))
    (ι : N →* G) (π : N →* S) (hπ : Function.Surjective π)
    (hact : ∀ n x, actS (ι n) x = π n * x)
    (d : D → G) {L : ℝ}
    (hleaf : ∀ p n j,
      |C.targetRate * αT (height (f p (ι n * d j))).toAdd -
        C.targetRate * αT (height (f p (d j))).toAdd| ≤ L) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ p j j₀,
      |(C.targetRate * αT (height (f p (d j))).toAdd -
          C.targetRate * αT (height (f p (d j₀))).toAdd) -
        (C.sourceRate * αS (height (d j)).toAdd -
          C.sourceRate * αS (height (d j₀)).toAdd)| ≤ B := by
  let : C.sourceMeasure.IsHaarMeasure := C.sourceHaar
  have hfin : C.sourceMeasure (C.window : Set S) ≠ ⊤ := C.window.isCompact.measure_ne_top
  have hpos : C.sourceMeasure (C.window : Set S) ≠ 0 :=
    (Measure.measure_pos_of_nonempty_interior C.sourceMeasure C.window.interior_nonempty).ne'
  let c := (C.sourceMeasure (C.window : Set S)).toReal
  have hc : 0 < c := ENNReal.toReal_pos hpos hfin
  have hsource (j : D) : C.sourceMeasure (actS (d j) '' (C.window : Set S)) =
      ENNReal.ofReal (c * Real.exp (C.sourceRate * αS (height (d j)).toAdd)) := by
    rw [C.source_volume, ← ENNReal.ofReal_toReal hfin,
      ← ENNReal.ofReal_mul (Real.exp_nonneg _)]
    congr 1
    exact mul_comm _ _
  exact boundary_averaged_trace_of_published_metric metricInput dynkin haar Exp hExp hnil
    C.sourceMeasure C.targetMeasure actS hcont ι π hπ hact C.boundary f
    (fun x => C.targetRate * αT (height x).toAdd) d
    (fun j => C.sourceRate * αS (height (d j)).toAdd) C.window C.window.isCompact
    hc C.constant_pos hsource C.mass hleaf

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

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L]
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
    {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
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

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {n : ℕ} (T : TriangularAdjoint L n)
  (H : LieSubalgebra ℝ L) [H.IsCartanSubalgebra] (χ : Weight ℝ H L) (hχ : χ.IsNonZero)

attribute [local instance] OAI.PolycyclicRecognition.instNormedAddCommGroupSubtypeMemLieSubmoduleRealLieSubalgebraRootSpaceCoeWeight_solutions_1
attribute [local instance] OAI.PolycyclicRecognition.instNormedSpaceRealSubtypeMemLieSubmoduleLieSubalgebraRootSpaceCoeWeight_solutions_1
local instance instNontrivialSubtypeMemLieSubmoduleRealLieSubalgebraRootSpaceCoeWeight_solutions_1_rdd6c21_1 : Nontrivial (rootSpace H χ) :=
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

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]
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

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {n : ℕ} (T : TriangularAdjoint L n)
  (H : LieSubalgebra ℝ L) [H.IsCartanSubalgebra]

variable (χ : Weight ℝ H L) (hχ : χ.IsNonZero)

attribute [local instance] OAI.PolycyclicRecognition.instNormedAddCommGroupSubtypeMemLieSubmoduleRealLieSubalgebraRootSpaceCoeWeight_solutions_2
attribute [local instance] OAI.PolycyclicRecognition.instNormedSpaceRealSubtypeMemLieSubmoduleLieSubalgebraRootSpaceCoeWeight_solutions_2
local instance instNontrivialSubtypeMemLieSubmoduleRealLieSubalgebraRootSpaceCoeWeight_solutions_2_rdd6c21_1 : Nontrivial (rootSpace H χ) :=
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

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

attribute [local instance 100] LieRing.ofAssociativeRing

attribute [local instance] OAI.PolycyclicRecognition.instNormedAddCommGroupSubtypeMemLieSubmoduleRealLieSubalgebraRootSpaceCoeWeight_solutions_2
attribute [local instance] OAI.PolycyclicRecognition.instNormedSpaceRealSubtypeMemLieSubmoduleLieSubalgebraRootSpaceCoeWeight_solutions_2
local instance instNontrivialSubtypeMemLieSubmoduleRealLieSubalgebraRootSpaceCoeWeight_solutions_2_rdd6c21_2 : Nontrivial (rootSpace H χ) :=
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

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {H : LieSubalgebra ℝ L} [H.IsCartanSubalgebra] (M : CartanWordModel H)
  {n : ℕ} (T : TriangularAdjoint L n)
  {EN N : Type*} [NormedAddCommGroup EN] [NormedSpace ℝ EN]
  [FiniteDimensional ℝ EN] [TopologicalSpace N] [ChartedSpace EN N] [Group N]
  [LieGroup (𝓘(ℝ, EN)) ⊤ N] [T2Space N]
  (eN : cartanRootIdeal H ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, EN)) N)
  (Exp : GroupLieAlgebra (𝓘(ℝ, EN)) N → N) (hExp : IsGroupExponential Exp)
  (hbij : Function.Bijective Exp) (dynkin : NilpotentDynkinExpansionInput EN N)

section Representation

variable {A G : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A] [Group G]

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

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  (H : LieSubalgebra ℝ L) [H.IsCartanSubalgebra]
  {ED D : Type*} [NormedAddCommGroup ED] [NormedSpace ℝ ED]
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

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {H : LieSubalgebra ℝ L} [H.IsCartanSubalgebra] (M : CartanWordModel H)
  {n : ℕ} (T : TriangularAdjoint L n)
  (hunimod : ∀ x : L, LinearMap.trace ℝ L (ad ℝ L x) = 0)
  {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)
  {EN N : Type*} [NormedAddCommGroup EN] [NormedSpace ℝ EN]
  [FiniteDimensional ℝ EN] [TopologicalSpace N] [ChartedSpace EN N] [Group N]
  [LieGroup (𝓘(ℝ, EN)) ⊤ N] [T2Space N]
  (eN : cartanRootIdeal H ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, EN)) N)
  (ExpN : GroupLieAlgebra (𝓘(ℝ, EN)) N → N) (hExpN : IsGroupExponential ExpN)
  (hbijN : Function.Bijective ExpN) (dynkinN : NilpotentDynkinExpansionInput EN N)
  {ED D : Type*} [NormedAddCommGroup ED] [NormedSpace ℝ ED]
  [FiniteDimensional ℝ ED] [TopologicalSpace D] [ChartedSpace ED D] [Group D]
  [LieGroup (𝓘(ℝ, ED)) ⊤ D] [T2Space D]
  (eD : H ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, ED)) D)
  (ExpD : GroupLieAlgebra (𝓘(ℝ, ED)) D → D) (hExpD : IsGroupExponential ExpD)
  (hbijD : Function.Bijective ExpD) (dynkinD : NilpotentDynkinExpansionInput ED D)
  (φ : D →* MulAut N)

section Representation

variable {A G : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A] [Group G]

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
variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
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

variable {EG G : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
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

variable {EG G : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
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

variable {EG G : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
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
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanRayBoundaryModel
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Concrete ray quotients and their ambient actions

The model is chosen from the previously stated nilpotent existence,
integration, and Haar inputs. Its action, section, topology and contraction
are proved properties of that choice.
-/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule Set Filter TopologicalSpace Topology
open scoped Manifold Topology

variable {EG G : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G]
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {ExpG : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H ExpG)
  (α₀ : H →ₗ[ℝ] ℝ)

namespace RayBoundaryModel

variable {M F α₀} (R : M.RayBoundaryModel F α₀)

variable {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  [SimplyConnectedSpace G]
  (hExpG : IsGroupExponential ExpG)
  (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
  (hbijN : Function.Bijective F.ExpN) (hbijD : Function.Bijective F.ExpD)
  (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)

set_option maxHeartbeats 1000000 in
include T hExpG realize hbijN hbijD dynkinN in
theorem continuous_action (g : G) : Continuous (R.action g) := by
  exact M.continuous_ambient_ray_action T F α₀ R.cone.Q R.cone.maps.expQ
    (by rw [← show R.cone.maps.chartQ = R.cone.maps.expQ from
      funext R.cone.maps.chartQ_eq]; exact R.cone.maps.chartQ.bijective)
    R.cone.maps.chartQ R.cone.maps.chartQ_eq hbijN hbijD dynkinN
    R.cone.maps.quotient R.cone.maps.quotient_exp R.factorAction R.equivariant
    (fun d => cartan_action_eq_adjoint_of_published_realization
      T M F hExpG realize hbijN hbijD dynkinN d) R.action R.action_eq g

end RayBoundaryModel

open scoped Matrix.Norms.Operator
attribute [local instance 100] LieRing.ofAssociativeRing

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanBoundaryAveraging
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_countable _root_.OAI.PolycyclicRecognition.finitelyGeneratedSubgroupIndex_countable _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Transversal estimates from the actual boundary comparison and leaf bound -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule Set MeasureTheory
open scoped Manifold

variable {EG G W P : Type} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  {M : CartanWordModel H}
  {ExpG : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} {F : CartanFactorModel H ExpG}
  {eW : HeightSpace T.character ≃ₗ[ℝ] W} {αS αT : W →L[ℝ] ℝ}
  (RS : M.RayBoundaryModel F (αS.toLinearMap.comp
    (eW.toLinearMap.comp ((heightProjection T.character).comp H.subtype))))
  (RT : M.RayBoundaryModel F (αT.toLinearMap.comp
    (eW.toLinearMap.comp ((heightProjection T.character).comp H.subtype))))
  (height : G →* Multiplicative W) (f : P → G → G)
  (C : RayBoundaryComparison RS RT height f)

set_option maxHeartbeats 1000000 in
/-- The normality identity changes the right-leaf estimate into the left
translations used for Haar averaging. All boundary metric and polynomial
volume assumptions are supplied by the existing published inputs. -/
theorem RayBoundaryComparison.transversal_trace_of_leaf_bound
    (hExpG : IsGroupExponential ExpG)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (hbijN : Function.Bijective F.ExpN) (hbijD : Function.Bijective F.ExpD)
    (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
    (metricInput : GeodesicMetricExistenceInput)
    (dynkinS : NilpotentDynkinExpansionInput RS.cone.Q.modelSpace RS.cone.Q.carrier)
    (haarS : NilpotentExponentialHaarInput RS.cone.Q.modelSpace RS.cone.Q.carrier)
    {L : ℝ}
    (hleaf : ∀ p x (n : F.N.carrier),
      ‖(height (f p (x * F.inclusionN n))).toAdd - (height (f p x)).toAdd‖ ≤ L) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ p d d₀,
      |(C.targetRate * αT (height (f p (F.inclusionD d))).toAdd -
          C.targetRate * αT (height (f p (F.inclusionD d₀))).toAdd) -
        (C.sourceRate * αS (height (F.inclusionD d)).toAdd -
          C.sourceRate * αS (height (F.inclusionD d₀)).toAdd)| ≤ B := by
  let : IsTopologicalGroup RT.cone.Q.carrier :=
    topologicalGroup_of_lieGroup (𝓘(ℝ, RT.cone.Q.modelSpace)) ⊤
  let : LocallyCompactSpace RT.cone.Q.carrier :=
    Manifold.locallyCompact_of_finiteDimensional (𝓘(ℝ, RT.cone.Q.modelSpace))
  let : SecondCountableTopology
      (GroupLieAlgebra (𝓘(ℝ, RT.cone.Q.modelSpace)) RT.cone.Q.carrier) :=
    (finBasis ℝ _).equivFunL.toHomeomorph.secondCountableTopology
  let : SecondCountableTopology
      (GroupLieAlgebra (𝓘(ℝ, RS.cone.Q.modelSpace)) RS.cone.Q.carrier) :=
    (finBasis ℝ _).equivFunL.toHomeomorph.secondCountableTopology
  let : SecondCountableTopology RT.cone.Q.carrier :=
    RT.cone.maps.chartQ.symm.isEmbedding.secondCountableTopology
  let : SecondCountableTopology RS.cone.Q.carrier :=
    RS.cone.maps.chartQ.symm.isEmbedding.secondCountableTopology
  let : C.targetMeasure.IsHaarMeasure := C.targetHaar
  have hscalar (p : P) (n : F.N.carrier) (d : F.D.carrier) :
      |C.targetRate * αT (height (f p (F.inclusionN n * F.inclusionD d))).toAdd -
        C.targetRate * αT (height (f p (F.inclusionD d))).toAdd| ≤
        C.targetRate * ‖αT‖ * L := by
    have hswap : F.inclusionD d * F.inclusionN (F.action d⁻¹ n) =
        F.inclusionN n * F.inclusionD d := by
      rw [F.conjugation, map_inv, inv_inv]
      group
    have hh := hleaf p (F.inclusionD d) (F.action d⁻¹ n)
    rw [hswap] at hh
    rw [← mul_sub, ← map_sub, abs_mul, abs_of_pos C.targetRate_pos]
    change C.targetRate * ‖αT ((height (f p (F.inclusionN n * F.inclusionD d))).toAdd -
      (height (f p (F.inclusionD d))).toAdd)‖ ≤ _
    calc
      _ ≤ C.targetRate * (‖αT‖ * ‖(height (f p (F.inclusionN n * F.inclusionD d))).toAdd -
          (height (f p (F.inclusionD d))).toAdd‖) :=
        mul_le_mul_of_nonneg_left (αT.le_opNorm _) C.targetRate_pos.le
      _ ≤ C.targetRate * (‖αT‖ * L) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hh (norm_nonneg _)) C.targetRate_pos.le
      _ = _ := (mul_assoc _ _ _).symm
  have hπsurj : Function.Surjective RS.cone.maps.quotient :=
    fun q => ⟨RS.cone.maps.sectionMap q, RS.cone.maps.section_rightInverse q⟩
  have hact n x : RS.action (F.inclusionN n) x = RS.cone.maps.quotient n * x := by
    simpa only [map_one, mul_one, MulAut.one_apply] using RS.action_eq n 1 x
  exact C.averaged_trace metricInput dynkinS haarS RS.cone.maps.expQ RS.cone.maps.isExpQ
    (RS.cone.Q.tangent_nilpotent (M.coneQuotient_nilpotent _))
    (RS.continuous_action T hExpG realize hbijN hbijD dynkinN)
    F.inclusionN RS.cone.maps.quotient hπsurj hact F.inclusionD hscalar

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanBoundaryBoundedHeight
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_nonempty _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.instFiniteRootOffsetConeIndex _root_.OAI.PolycyclicRecognition.instNonemptyRootOffsetConeIndex _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Bounded affine height from the actual boundary comparisons -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule Set
open scoped Manifold BigOperators

variable {EG G W : Type} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {ExpG : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H ExpG)
  (hunimod : ∀ x : GroupLieAlgebra (𝓘(ℝ, EG)) G, LinearMap.trace ℝ _ (ad ℝ _ x) = 0)
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)

variable {P : Type} [SimplyConnectedSpace G] [IsIsometricSMul G G]
  (height : G →* Multiplicative W) (f : P → G → G)
  (A : templateSymmetryGroup (M.supportIn T hunimod eW))
  (RS : ∀ i, M.RayBoundaryModel F ((((M.supportIn T hunimod eW).weight i).comp A.val.toLinearMap).comp (eW.toLinearMap.comp ((heightProjection T.character).comp H.subtype))))
  (RT : ∀ i, M.RayBoundaryModel F (((M.supportIn T hunimod eW).weight i).comp (eW.toLinearMap.comp ((heightProjection T.character).comp H.subtype))))
  (C : ∀ i, BoundaryVolumeComparison (RS i).action (RT i).action
    ((((M.supportIn T hunimod eW).weight i).toContinuousLinearMap).comp A.val.toContinuousLinearEquiv.toContinuousLinearMap)
    ((M.supportIn T hunimod eW).weight i).toContinuousLinearMap height f)
  (hExpG : IsGroupExponential ExpG)
  (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
  (hbijN : Function.Bijective F.ExpN)
  (chartD : GroupLieAlgebra (𝓘(ℝ, F.D.modelSpace)) F.D.carrier ≃ₜ F.D.carrier)
  (hchartD : ∀ x, chartD x = F.ExpD x)
  (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
  (metricInput : GeodesicMetricExistenceInput)
  (dynkinS : ∀ i, NilpotentDynkinExpansionInput (RS i).cone.Q.modelSpace (RS i).cone.Q.carrier)
  (haarS : ∀ i, NilpotentExponentialHaarInput (RS i).cone.Q.modelSpace (RS i).cone.Q.carrier)

set_option maxHeartbeats 1000000 in
include C hExpG realize hbijN chartD hchartD dynkinN metricInput dynkinS haarS in
omit [IsIsometricSMul G G] in
/-- Finitely many boundary characters give one common transversal bound. -/
theorem uniform_transversal_traces_of_boundary_comparisons_oai
    {L : ℝ} (hleaf : ∀ p x (n : F.N.carrier),
      ‖(height (f p (x * F.inclusionN n))).toAdd - (height (f p x)).toAdd‖ ≤ L) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ p d i,
      |(C i).targetRate * (M.supportIn T hunimod eW).weight i ((height (f p (F.inclusionD d))).toAdd - (height (f p 1)).toAdd) -
        (C i).sourceRate * (M.supportIn T hunimod eW).weight i (A.val (height (F.inclusionD d)).toAdd)| ≤ B := by
  have hbijD : Function.Bijective F.ExpD := by
    rw [← show chartD = F.ExpD from funext hchartD]
    exact chartD.bijective
  have htrace (i : Fin M.letterCount) := RayBoundaryComparison.transversal_trace_of_leaf_bound
    (eW := eW)
    (αS := (((M.supportIn T hunimod eW).weight i).toContinuousLinearMap).comp
      A.val.toContinuousLinearEquiv.toContinuousLinearMap)
    (αT := ((M.supportIn T hunimod eW).weight i).toContinuousLinearMap)
    T (RS i) (RT i) height f (C i) hExpG realize hbijN hbijD dynkinN
    metricInput (dynkinS i) (haarS i) hleaf
  choose bound hbound hb using htrace
  refine ⟨∑ i, bound i, Finset.sum_nonneg (fun i _ => hbound i), ?_⟩
  intro p d i
  have hh := hb i p d (1 : F.D.carrier)
  have hi : |(C i).targetRate * (M.supportIn T hunimod eW).weight i ((height (f p (F.inclusionD d))).toAdd -
      (height (f p 1)).toAdd) -
      (C i).sourceRate * (M.supportIn T hunimod eW).weight i (A.val (height (F.inclusionD d)).toAdd)| ≤ bound i := by
    simpa only [map_one, toAdd_one, map_zero, mul_zero, sub_zero, map_sub, mul_sub,
      LinearMap.coe_toContinuousLinearMap', ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe, LinearEquiv.coe_toContinuousLinearEquiv'] using hh
  exact hi.trans (Finset.single_le_sum (fun j _ => hbound j) (Finset.mem_univ i))

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

theorem solution : type_of% @OAI.PolycyclicRecognition.CartanWordModel.uniform_transversal_traces_of_boundary_comparisons_oai := @OAI.PolycyclicRecognition.CartanWordModel.uniform_transversal_traces_of_boundary_comparisons_oai
