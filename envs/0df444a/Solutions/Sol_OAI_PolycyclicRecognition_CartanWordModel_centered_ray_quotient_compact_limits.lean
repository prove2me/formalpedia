-- Prove2me | solution 1 for OAI.PolycyclicRecognition.CartanWordModel.centered_ray_quotient_compact_limits
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-02T22:47:32.356805+00:00
-- url     : https://prove2.me/submissions/19c3dec2-fc97-4f77-b1d2-476aae416443

import Mathlib
import Definitions.Def_PolycyclicRecognition
import Definitions.Def_OAIQ093D027
import Theorems.Thm_OAI_PolycyclicRecognition_CartanWordModel_exists_metric_cartan_factor_bound

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_CocycleGrowth
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Sublinear cocycle bounds from compact coboundary approximation

Compact-uniform approximation by coboundaries makes an isometric cocycle
sublinear on words of linearly bounded length.
-/

namespace PolycyclicRecognition

variable {G E : Type} [Group G] [NormedAddCommGroup E]
  [DistribMulAction G E] [IsIsometricSMul G E]

omit [Group G] [DistribMulAction G E] [IsIsometricSMul G E] in
/-- A global sublinear estimate is uniform after division by scale on every
linearly growing metric ball. The additive error is chosen before the scale. -/
theorem uniform_sublinear_on_balls {b : G → E} (length : G → ℝ)
    (hsub : ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, 0 ≤ B ∧ ∀ g, ‖b g‖ ≤ ε * length g + B)
    {R : ℝ} (hR : 0 ≤ R) : ∀ ε : ℝ, 0 < ε →
      ∃ r₀ : ℝ, 0 ≤ r₀ ∧ ∀ r, r₀ ≤ r → ∀ g, length g ≤ R * r → ‖b g‖ ≤ ε * r := by
  intro ε hε
  have hden : 0 < 2 * (R + 1) := by linarith
  let δ := ε / (2 * (R + 1))
  have hδ : 0 < δ := div_pos hε hden
  obtain ⟨B, hB, hb⟩ := hsub δ hδ
  refine ⟨2 * B / ε, by positivity, ?_⟩
  intro r hr g hg
  have hr0 : 0 ≤ r := (by positivity : 0 ≤ 2 * B / ε).trans hr
  have hBr : 2 * B ≤ r * ε := (div_le_iff₀ hε).mp hr
  have hcoef : δ * R ≤ ε / 2 := by
    dsimp [δ]
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hden).mpr
    nlinarith
  calc
    ‖b g‖ ≤ δ * length g + B := hb g
    _ ≤ δ * (R * r) + B := add_le_add (mul_le_mul_of_nonneg_left hg hδ.le) le_rfl
    _ = (δ * R) * r + B := by ring
    _ ≤ (ε / 2) * r + B := add_le_add (mul_le_mul_of_nonneg_right hcoef hr0) le_rfl
    _ ≤ ε * r := by nlinarith

end PolycyclicRecognition

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
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanRootWidths
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instDecidableEqConeMixedWords _root_.OAI.PolycyclicRecognition.CartanWordModel.instFintypeConeMixedWords _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
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

namespace CartanWordModel

variable {L W : Type} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {H : LieSubalgebra ℝ L} [H.IsCartanSubalgebra] (M : CartanWordModel H)
  {n : ℕ} (T : TriangularAdjoint L n)

include T

variable (hunimod : ∀ x : L, LinearMap.trace ℝ L (ad ℝ L x) = 0)
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)

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
local instance instNontrivialSubtypeMemLieSubmoduleRealLieSubalgebraRootSpaceCoeWeight_solutions_1_r382d2b_1 : Nontrivial (rootSpace H χ) :=
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
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_MixedWordIdeal
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The mixed-word ideal used by the cone quotients -/

noncomputable section
namespace PolycyclicRecognition

open Set

variable {I L : Type} [LieRing L] [LieAlgebra ℝ L]

/-- The quotient by the mixed-word ideal is spanned by pure words. -/
theorem quotient_mixedWordIdeal_span_pure (X : I → L) (outside : I → Prop)
    (hgen : LieSubalgebra.lieSpan ℝ L (range X) = ⊤) :
    let J := (mixedWordIdeal X outside hgen).toSubmodule
    Submodule.span ℝ (J.mkQ '' (evalBracketWord X '' {w | ¬IsMixedWord outside w})) = ⊤ := by
  dsimp only
  let J := (mixedWordIdeal X outside hgen).toSubmodule
  let P := Submodule.span ℝ (J.mkQ '' (evalBracketWord X '' {w | ¬IsMixedWord outside w}))
  apply top_unique
  intro q hq
  clear hq
  obtain ⟨x, rfl⟩ := J.mkQ_surjective q
  have hx : x ∈ Submodule.span ℝ (range (evalBracketWord X)) := by
    rw [span_evalBracketWord, hgen]
    trivial
  change J.mkQ x ∈ P
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨w, rfl⟩ := hx
    by_cases hw : IsMixedWord outside w
    · have hz : J.mkQ (evalBracketWord X w) = 0 :=
        (Submodule.Quotient.mk_eq_zero J).mpr (eval_mixed_mem_span X outside hw)
      rw [hz]
      exact P.zero_mem
    · exact Submodule.subset_span ⟨_, ⟨w, hw, rfl⟩, rfl⟩
  | zero => simpa only [map_zero] using P.zero_mem
  | add x y _ _ hx hy => simpa only [map_add] using P.add_mem hx hy
  | smul r x _ hx => simpa only [map_smul] using P.smul_mem r hx

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_QuotientWordBasis
attribute [-instance] _root_.GeneratesNS.fintype_closedBall _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Pure word bases of the mixed-word quotient

An inside generator is retained in every pure word basis. The proof uses
its actual coordinate in the original abelianization, descended through
the mixed-word ideal.
-/

noncomputable section
namespace PolycyclicRecognition

open Module Set
open scoped BigOperators

variable {I L : Type} [LieRing L] [LieAlgebra ℝ L]

theorem exists_pure_quotient_word_basis [FiniteDimensional ℝ L]
    (X : I → L) (outside : I → Prop)
    (hgen : LieSubalgebra.lieSpan ℝ L (range X) = ⊤) :
    let J := (mixedWordIdeal X outside hgen).toSubmodule
    ∃ (b : Basis (Fin (finrank ℝ (L ⧸ J))) ℝ (L ⧸ J))
      (words : Fin (finrank ℝ (L ⧸ J)) → FreeMagma I),
      (∀ j, ¬IsMixedWord outside (words j)) ∧
      (∀ j, J.mkQ (evalBracketWord X (words j)) = b j) := by
  dsimp only
  let J := (mixedWordIdeal X outside hgen).toSubmodule
  let S := J.mkQ '' (evalBracketWord X '' {w | ¬IsMixedWord outside w})
  have hS : ⊤ ≤ Submodule.span ℝ S :=
    (quotient_mixedWordIdeal_span_pure X outside hgen).ge
  let K := (linearIndepOn_empty ℝ (id : (L ⧸ J) → (L ⧸ J))).extend
    (empty_subset S)
  let b₀ : Basis K ℝ (L ⧸ J) := Basis.ofSpan hS
  let : Fintype K := Fintype.ofFinite _
  let e : K ≃ Fin (finrank ℝ (L ⧸ J)) :=
    Fintype.equivFinOfCardEq (Module.finrank_eq_card_basis b₀).symm
  let b := b₀.reindex e
  have hw (j) : ∃ w, ¬IsMixedWord outside w ∧ J.mkQ (evalBracketWord X w) = b j := by
    have hj := Basis.ofSpan_subset hS (show b₀ (e.symm j) ∈ range b₀ from ⟨_, rfl⟩)
    obtain ⟨_, ⟨w, hp, rfl⟩, he⟩ := hj
    exact ⟨w, hp, by simpa only [b, Basis.coe_reindex, Function.comp_apply] using he⟩
  choose words hp he using hw
  exact ⟨b, words, hp, he⟩

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
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanControlledAction
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instDecidableEqConeMixedWords _root_.OAI.PolycyclicRecognition.CartanWordModel.instFintypeConeMixedWords _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.CartanFactorModel.realScaleProfile_apply _root_.OAI.PolycyclicRecognition.CartanFactorModel.sampledProbeProfile_apply _root_.OAI.PolycyclicRecognition.bracketWordDifferential_mul _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
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

end CartanWordModel
end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_ConeQuotientBounds
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instDecidableEqConeMixedWords _root_.OAI.PolycyclicRecognition.CartanWordModel.instFintypeConeMixedWords _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_nonempty _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.CartanFactorModel.heightRay_zero _root_.OAI.PolycyclicRecognition.CartanFactorModel.realScaleProfile_apply _root_.OAI.PolycyclicRecognition.CartanFactorModel.sampledProbeProfile_apply _root_.OAI.PolycyclicRecognition.cartanWeightDerivation_apply_root _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.nilshadowWeightDerivation_symm _root_.OAI.PolycyclicRecognition.nilshadowWeightOperator_symm _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Polynomial residual bounds on the actual cone quotient

The nilpotent residual part of the Cartan action has polynomial coordinate
growth. Passing to a quotient costs a fixed coordinate constant, obtained
from lifts of a basis. These are estimates for the constructed action,
with no quotient-contraction hypothesis.
-/

noncomputable section

namespace PolycyclicRecognition

open Module LieAlgebra LieModule
open scoped BigOperators

/-- A coordinate bound passes to an invariant quotient, with a constant
depending only on the two bases and the quotient map. -/
theorem exists_quotient_coordinate_bound
    {V I J : Type} [AddCommGroup V] [Module ℝ V] [Fintype I] [Fintype J]
    (a : Basis I ℝ V) (S : Submodule ℝ V) (b : Basis J ℝ (V ⧸ S)) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (F : V →ₗ[ℝ] V) (hF : ∀ v ∈ S, F v ∈ S)
      (A : ℝ), 0 ≤ A → (∀ v, ‖a.equivFun (F v)‖ ≤ A * ‖a.equivFun v‖) →
      ∀ z, ‖b.equivFun (S.mapQ S F hF z)‖ ≤ K * A * ‖b.equivFun z‖ := by
  classical
  choose v hv using fun j => S.mkQ_surjective (b j)
  let q : (I → ℝ) →ₗ[ℝ] (J → ℝ) :=
    b.equivFun.toLinearMap.comp (S.mkQ.comp a.equivFun.symm.toLinearMap)
  let Q := q.toContinuousLinearMap
  let K := ‖Q‖ * ∑ j, ‖a.equivFun (v j)‖
  have hq (x : V) : ‖b.equivFun (S.mkQ x)‖ ≤ ‖Q‖ * ‖a.equivFun x‖ := by
    simpa only [Q, q, LinearMap.coe_comp, Function.comp_apply,
      LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply,
      LinearMap.coe_toContinuousLinearMap'] using Q.le_opNorm (a.equivFun x)
  refine ⟨K, by dsimp [K] <;> positivity, ?_⟩
  intro F hF A hA hbound z
  conv_lhs => rw [← b.sum_repr z]
  rw [map_sum, map_sum]
  apply (norm_sum_le _ _).trans
  calc
    (∑ j, ‖b.equivFun (S.mapQ S F hF (b.repr z j • b j))‖) ≤
        ∑ j, ‖b.equivFun z‖ * (‖Q‖ * (A * ‖a.equivFun (v j)‖)) := by
      apply Finset.sum_le_sum
      intro j _
      rw [map_smul, map_smul, norm_smul]
      have hcoord : ‖b.repr z j‖ ≤ ‖b.equivFun z‖ :=
        norm_le_pi_norm (b.equivFun z) j
      have himage : ‖b.equivFun (S.mapQ S F hF (b j))‖ ≤
          ‖Q‖ * (A * ‖a.equivFun (v j)‖) := by
        rw [← hv j]
        exact (hq (F (v j))).trans
          (mul_le_mul_of_nonneg_left (hbound (v j)) (norm_nonneg Q))
      exact mul_le_mul hcoord himage (norm_nonneg _) (norm_nonneg _)
    _ = K * A * ‖b.equivFun z‖ := by
      simp only [K, Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j _
      ring

namespace CartanWordModel

variable {L : Type} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {H : LieSubalgebra ℝ L} [H.IsCartanSubalgebra] (M : CartanWordModel H)
  {n : ℕ} (T : TriangularAdjoint L n)

/-- The residual action has a polynomial bound in any fixed unscaled word
basis. No unimodularity assumption is needed for this estimate. -/
theorem exists_residual_coordinate_bound (β : M.Bases) :
    ∃ (A : ℝ) (p : ℕ), 0 ≤ A ∧ ∀ (h : H) (v : cartanRootIdeal H),
      ‖(WordBasisSelections.basis M.letter M.wordList β).equivFun
        (cartanIdealResidualAutomorphism T H h v)‖ ≤
      A * (1 + ‖(Module.finBasis ℝ H).equivFun h‖) ^ p *
        ‖(WordBasisSelections.basis M.letter M.wordList β).equivFun v‖ := by
  obtain ⟨C, p, hC, hletters⟩ := M.exists_residual_letters_bound T
  let b := WordBasisSelections.basis M.letter M.wordList β
  obtain ⟨K, hK, hbracket⟩ := exists_basis_structureConstant_bound b
  let d := finrank ℝ (cartanRootIdeal H)
  let Q := 1 + (d : ℝ) ^ 2 * K
  refine ⟨(d : ℝ) * Q ^ M.wordDegreeBound * (1 + C) ^ M.wordDegreeBound,
    p * M.wordDegreeBound, by dsimp [Q] <;> positivity, ?_⟩
  intro h v
  let q := 1 + ‖(Module.finBasis ℝ H).equivFun h‖
  have hq : 1 ≤ q := le_add_of_nonneg_right (norm_nonneg _)
  have hqp : 1 ≤ q ^ p := one_le_pow₀ hq
  have hb := M.norm_wordBasis_lieMap_le β b
    (cartanIdealResidualAutomorphism T H h).toLieHom hK
    (by positivity : 0 ≤ C * q ^ p) hbracket (hletters β h) v
  apply hb.trans
  have hs : 1 + C * q ^ p ≤ (1 + C) * q ^ p := by nlinarith
  calc
    _ ≤ (d : ℝ) * Q ^ M.wordDegreeBound * ((1 + C) * q ^ p) ^ M.wordDegreeBound *
        ‖b.equivFun v‖ := by
      dsimp only [Q, d]
      gcongr
    _ = _ := by rw [mul_pow, ← pow_mul]; ring

/-- The induced residual action on every cone quotient has polynomial
coordinate growth in the Cartan parameter. -/
theorem exists_cone_residual_coordinate_bound
    (C : Set (H →ₗ[ℝ] ℝ)) (hadd : ∀ x ∈ C, ∀ y ∈ C, x + y ∈ C)
    {J : Type} [Fintype J]
    (b : Basis J ℝ ((cartanRootIdeal H) ⧸ M.coneWordIdeal C)) :
    ∃ (A : ℝ) (p : ℕ), 0 ≤ A ∧ ∀ (h : H) (v : (cartanRootIdeal H) ⧸ M.coneWordIdeal C),
      ‖b.equivFun ((M.coneWordIdeal C).toSubmodule.mapQ (M.coneWordIdeal C).toSubmodule
        (cartanIdealResidualAutomorphism T H h).toLinearEquiv.toLinearMap
        (M.coneWordIdeal_residual_mem T C hadd h) v)‖ ≤
      A * (1 + ‖(Module.finBasis ℝ H).equivFun h‖) ^ p * ‖b.equivFun v‖ := by
  let β : M.Bases := Classical.choice inferInstance
  let a := WordBasisSelections.basis M.letter M.wordList β
  obtain ⟨A, p, hA, hbound⟩ := M.exists_residual_coordinate_bound T β
  obtain ⟨K, hK, hquot⟩ := exists_quotient_coordinate_bound a (M.coneWordIdeal C).toSubmodule b
  refine ⟨K * A, p, mul_nonneg hK hA, ?_⟩
  intro h v
  simpa only [mul_assoc] using hquot
    (cartanIdealResidualAutomorphism T H h).toLinearEquiv.toLinearMap
    (M.coneWordIdeal_residual_mem T C hadd h)
    (A * (1 + ‖(Module.finBasis ℝ H).equivFun h‖) ^ p) (by positivity) (hbound h) v

end CartanWordModel
end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_DynkinSummableProducts
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.CartanFactorModel.realScaleProfile_apply _root_.OAI.PolycyclicRecognition.basisDynkinParameter_zero _root_.OAI.PolycyclicRecognition.bracketWordDifferential_mul _root_.OAI.PolycyclicRecognition.dynkinRightTranslation_apply _root_.OAI.PolycyclicRecognition.dynkinRightTranslation_symm_apply _root_.OAI.PolycyclicRecognition.exponentialHomOfDynkin_apply_exp _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.OAI.PolycyclicRecognition.wordBasisOfDet_val _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite BCH products controlled by the sum of input sizes

The coefficient bound in the existing finite Dynkin input also controls
products by the sum of the logarithmic input norms. In particular the
bound tends to zero with that sum, independently of the number of factors.
This is the estimate needed for contracting quotient trajectories in
exponential coordinates; no Riemannian metric comparison is assumed.
-/

noncomputable section

namespace PolycyclicRecognition

open Module LieModule
open scoped BigOperators Manifold

variable {L J : Type} [LieRing L] [LieAlgebra ℝ L] [Fintype J]

/-- Keep the individual letter sizes when estimating a right-nested word. -/
theorem norm_rightNestedWord_le_product (b : Basis J ℝ L)
    {I : Type} (X : I → L) {C : ℝ} (hC : 0 ≤ C)
    (hbracket : ∀ i j k, |b.repr ⁅b i, b j⁆ k| ≤ C)
    (d : ℕ) (w : Fin (d + 1) → I) :
    ‖b.equivFun (evalBracketWord X (rightNestedWord d w))‖ ≤
      ((Fintype.card J : ℝ) ^ 2 * C) ^ d * ∏ i, ‖b.equivFun (X (w i))‖ := by
  let K := (Fintype.card J : ℝ) ^ 2 * C
  have hK : 0 ≤ K := by positivity
  induction d with
  | zero => simp [rightNestedWord]
  | succ d ih =>
    calc
      _ ≤ K * ‖b.equivFun (X (w 0))‖ *
          ‖b.equivFun (evalBracketWord X (rightNestedWord d (fun i => w i.succ)))‖ :=
        norm_basis_bracket_le b hC hbracket _ _
      _ ≤ K * ‖b.equivFun (X (w 0))‖ *
          (K ^ d * ∏ i : Fin (d + 1), ‖b.equivFun (X (w i.succ))‖) := by
        exact mul_le_mul_of_nonneg_left (ih (fun i => w i.succ)) (by positivity)
      _ = _ := by
        conv_rhs => rw [Fin.prod_univ_succ]
        dsimp [K]
        rw [pow_succ]
        ring

/-- The finite Dynkin polynomial is bounded by a polynomial in the sum
of input norms, with zero constant term. -/
theorem norm_finiteDynkinPolynomial_le_sum (b : Basis J ℝ L) {c n : ℕ}
    (coeff : DynkinCoefficients c n) (hcoeff : ∀ d w, |coeff d w| ≤ (2 : ℝ) ^ c)
    (X : Fin n → L) {C : ℝ} (hC : 0 ≤ C)
    (hbracket : ∀ i j k, |b.repr ⁅b i, b j⁆ k| ≤ C) :
    ‖b.equivFun (finiteDynkinPolynomial coeff X)‖ ≤
      (c : ℝ) * 2 ^ c * (1 + (Fintype.card J : ℝ) ^ 2 * C) ^ c *
        (∑ i, ‖b.equivFun (X i)‖) * (1 + ∑ i, ‖b.equivFun (X i)‖) ^ c := by
  let K := (Fintype.card J : ℝ) ^ 2 * C
  let S := ∑ i, ‖b.equivFun (X i)‖
  have hK : 0 ≤ K := by positivity
  have hS : 0 ≤ S := Finset.sum_nonneg (fun i _ => norm_nonneg _)
  have hdegree (d : Fin c) :
      ‖b.equivFun (∑ w : Fin (d.val + 1) → Fin n,
        coeff d w • evalBracketWord X (rightNestedWord d.val w))‖ ≤
      2 ^ c * (1 + K) ^ c * S * (1 + S) ^ c := by
    rw [map_sum]
    apply (norm_sum_le _ _).trans
    calc
      _ ≤ ∑ w : Fin (d.val + 1) → Fin n,
          2 ^ c * K ^ d.val * ∏ i, ‖b.equivFun (X (w i))‖ := by
        apply Finset.sum_le_sum
        intro w _
        rw [map_smul, norm_smul, Real.norm_eq_abs]
        have hb := norm_rightNestedWord_le_product b X hC hbracket d.val w
        have ht := mul_le_mul (hcoeff d w) hb (norm_nonneg _) (by positivity : 0 ≤ (2 : ℝ) ^ c)
        simpa only [K, mul_assoc] using ht
      _ = 2 ^ c * K ^ d.val * S ^ (d.val + 1) := by
        rw [← Finset.mul_sum,
          ← Fintype.sum_pow (fun i : Fin n => ‖b.equivFun (X i)‖) (d.val + 1)]
      _ ≤ 2 ^ c * (1 + K) ^ c * (S * (1 + S) ^ c) := by
        apply mul_le_mul
        · apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact (pow_le_pow_left₀ hK (by linarith) d.val).trans
            (pow_le_pow_right₀ (by linarith) d.isLt.le)
        · rw [pow_succ, mul_comm]
          apply mul_le_mul_of_nonneg_left _ hS
          exact (pow_le_pow_left₀ hS (by linarith) d.val).trans
            (pow_le_pow_right₀ (by linarith) d.isLt.le)
        · positivity
        · positivity
      _ = _ := by ring
  unfold finiteDynkinPolynomial
  rw [map_sum]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ _d : Fin c, 2 ^ c * (1 + K) ^ c * S * (1 + S) ^ c :=
      Finset.sum_le_sum (fun d _ => hdegree d)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      dsimp [K, S]
      ring

section ExponentialProducts

variable {E G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace G] [ChartedSpace E G] [Group G]
  [LieGroup (𝓘(ℝ, E)) ⊤ G] [T2Space G]

/-- Actual finite products of exponentials have a logarithm controlled by
the total input size, independently of the number of factors. -/
theorem exists_product_log_with_sum_bound
    (dynkin : NilpotentDynkinExpansionInput E G)
    (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G) (hExp : IsGroupExponential Exp)
    {c n : ℕ} (hc : lowerCentralSeries ℝ (GroupLieAlgebra (𝓘(ℝ, E)) G)
      (GroupLieAlgebra (𝓘(ℝ, E)) G) c = ⊥)
    (b : Basis J ℝ (GroupLieAlgebra (𝓘(ℝ, E)) G))
    {C : ℝ} (hC : 0 ≤ C)
    (hbracket : ∀ i j k, |b.repr ⁅b i, b j⁆ k| ≤ C)
    (X : Fin n → GroupLieAlgebra (𝓘(ℝ, E)) G) :
    ∃ z, (List.ofFn (fun i => Exp (X i))).prod = Exp z ∧
      ‖b.equivFun z‖ ≤
        (c : ℝ) * 2 ^ c * (1 + (Fintype.card J : ℝ) ^ 2 * C) ^ c *
          (∑ i, ‖b.equivFun (X i)‖) * (1 + ∑ i, ‖b.equivFun (X i)‖) ^ c := by
  obtain ⟨coeff, hcoeff, hprod⟩ := dynkin Exp hExp c hc n
  exact ⟨finiteDynkinPolynomial coeff X, hprod X,
    norm_finiteDynkinPolynomial_le_sum b coeff hcoeff X hC hbracket⟩

end ExponentialProducts
end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_BoundaryLimits
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Limits of contracting boundary trajectories

Polynomial times exponential decay is summable. Metric trajectories with a
common increment bound converge uniformly, with a common tail bound and compact
normalized shadow. Asymptotic representatives of a quotient point have equal
limits and determine a continuous boundary map.
-/

noncomputable section

namespace PolycyclicRecognition

open Filter Metric
open scoped Topology

/-- The summable increment profile appearing in the ray-boundary proof. -/
theorem summable_polynomial_exp_decay (C : ℝ) (M : ℕ) {c : ℝ} (hc : 0 < c) :
    Summable (fun n : ℕ => C * (1 + (n : ℝ)) ^ M * Real.exp (-c * n)) := by
  have hr : ‖Real.exp (-c)‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_lt_one_iff.mpr (neg_neg_of_pos hc)
  have hs := (summable_pow_mul_geometric_of_norm_lt_one M hr).comp_injective
    (show Function.Injective (fun n : ℕ => n + 1) from fun _ _ h => Nat.add_right_cancel h)
  have ht := hs.mul_left (C * Real.exp c)
  convert ht using 1
  all_goals try with_reducible_and_instances rfl
  funext n
  simp only [Function.comp_apply, Nat.cast_add, Nat.cast_one, ← Real.exp_nat_mul]
  calc
    C * (1 + (n : ℝ)) ^ M * Real.exp (-c * n) =
        C * ((n : ℝ) + 1) ^ M * Real.exp (c + ((n : ℝ) + 1) * (-c)) := by
      congr 2 <;> ring
    _ = C * Real.exp c * (((n : ℝ) + 1) ^ M * Real.exp (((n : ℝ) + 1) * (-c))) := by
      rw [Real.exp_add]
      ring

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_DynkinProductTails
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_countable _root_.OAI.PolycyclicRecognition.finitelyGeneratedSubgroupIndex_countable _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Convergence of products with summable logarithmic increments

Finite BCH gives a common bound on every tail product in terms of the
sum of its logarithmic increments. The global exponential chart then
gives convergence, without identifying its coordinate metric with a
left invariant metric.
-/

noncomputable section

namespace PolycyclicRecognition

open Module LieModule Filter Metric
open scoped BigOperators Manifold Topology

variable {E G J : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace G] [ChartedSpace E G] [Group G]
  [LieGroup (𝓘(ℝ, E)) ⊤ G] [T2Space G] [Fintype J]

omit [FiniteDimensional ℝ E] [LieGroup (𝓘(ℝ, E)) ⊤ G] [T2Space G] in
theorem exponentialPartialProduct_add
    (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G)
    (X : ℕ → GroupLieAlgebra (𝓘(ℝ, E)) G) (n m : ℕ) :
    exponentialPartialProduct Exp X (n + m) =
      exponentialPartialProduct Exp X n *
        exponentialPartialProduct Exp (fun k => X (n + k)) m := by
  simp only [exponentialPartialProduct, List.ofFn_add, List.prod_append]
  congr 2

/-- Summability controls the logarithm of every finite tail product,
uniformly in the number of tail factors. -/
theorem exists_tail_product_log_bound
    (dynkin : NilpotentDynkinExpansionInput E G)
    (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G) (hExp : IsGroupExponential Exp)
    {c : ℕ} (hc : lowerCentralSeries ℝ (GroupLieAlgebra (𝓘(ℝ, E)) G)
      (GroupLieAlgebra (𝓘(ℝ, E)) G) c = ⊥)
    (b : Basis J ℝ (GroupLieAlgebra (𝓘(ℝ, E)) G))
    {C : ℝ} (hC : 0 ≤ C) (hbracket : ∀ i j k, |b.repr ⁅b i, b j⁆ k| ≤ C)
    (X : ℕ → GroupLieAlgebra (𝓘(ℝ, E)) G) (d : ℕ → ℝ) (hd : Summable d)
    (hX : ∀ n, ‖b.equivFun (X n)‖ ≤ d n) (n m : ℕ) :
    ∃ z, exponentialPartialProduct Exp (fun k => X (n + k)) m = Exp z ∧
      ‖b.equivFun z‖ ≤
        (c : ℝ) * 2 ^ c * (1 + (Fintype.card J : ℝ) ^ 2 * C) ^ c *
          (∑' k, d (n + k)) * (1 + ∑' k, d (n + k)) ^ c := by
  obtain ⟨z, hz, hb⟩ := exists_product_log_with_sum_bound dynkin Exp hExp hc b hC hbracket
    (fun i : Fin m => X (n + i))
  have hnonneg (k : ℕ) : 0 ≤ d k := (norm_nonneg _).trans (hX k)
  have hsum : (∑ i : Fin m, ‖b.equivFun (X (n + i))‖) ≤ ∑' k, d (n + k) := by
    calc
      _ ≤ ∑ i : Fin m, d (n + i) := Finset.sum_le_sum (fun i _ => hX (n + i))
      _ = ∑ k ∈ Finset.range m, d (n + k) :=
        Fin.sum_univ_eq_sum_range (fun k => d (n + k)) m
      _ ≤ _ := Summable.sum_le_tsum _ (fun k _ => hnonneg (n + k))
        (hd.comp_injective (fun a b h => Nat.add_left_cancel h))
  refine ⟨z, hz, hb.trans ?_⟩
  have hsum0 : 0 ≤ ∑ i : Fin m, ‖b.equivFun (X (n + i))‖ :=
    Finset.sum_nonneg (fun i _ => norm_nonneg _)
  have ht0 : 0 ≤ ∑' k, d (n + k) := tsum_nonneg (fun k => hnonneg (n + k))
  gcongr

/-- The common bound for all finite tail products tends to zero. -/
theorem dynkin_tail_bound_tendsto_zero
    (A : ℝ) (c : ℕ) (d : ℕ → ℝ) :
    Tendsto (fun n => A * (∑' k, d (n + k)) * (1 + ∑' k, d (n + k)) ^ c)
      atTop (𝓝 0) := by
  have ht : Tendsto (fun n : ℕ => ∑' k, d (n + k)) atTop (𝓝 0) := by
    simpa only [Nat.add_comm] using tendsto_sum_nat_add d
  simpa using (tendsto_const_nhds.mul ht).mul ((tendsto_const_nhds.add ht).pow c)

/-- Actual ordered products with summable logarithmic increments converge
in the global exponential chart. The proof uses the common finite-tail
bound and compactness in coordinates, not a metric invariance assumption. -/
theorem exponentialPartialProduct_tendsto_of_summable
    (dynkin : NilpotentDynkinExpansionInput E G)
    (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G) (hExp : IsGroupExponential Exp)
    (chart : GroupLieAlgebra (𝓘(ℝ, E)) G ≃ₜ G) (hchart : ∀ v, chart v = Exp v)
    {c : ℕ} (hc : lowerCentralSeries ℝ (GroupLieAlgebra (𝓘(ℝ, E)) G)
      (GroupLieAlgebra (𝓘(ℝ, E)) G) c = ⊥)
    (b : Basis J ℝ (GroupLieAlgebra (𝓘(ℝ, E)) G))
    {C : ℝ} (hC : 0 ≤ C) (hbracket : ∀ i j k, |b.repr ⁅b i, b j⁆ k| ≤ C)
    (X : ℕ → GroupLieAlgebra (𝓘(ℝ, E)) G) (d : ℕ → ℝ) (hd : Summable d)
    (hX : ∀ n, ‖b.equivFun (X n)‖ ≤ d n) :
    ∃ g : G, Tendsto (exponentialPartialProduct Exp X) atTop (𝓝 g) := by
  let : IsTopologicalGroup G := topologicalGroup_of_lieGroup (𝓘(ℝ, E)) ⊤
  let A := (c : ℝ) * 2 ^ c * (1 + (Fintype.card J : ℝ) ^ 2 * C) ^ c
  let B := fun n => A * (∑' k, d (n + k)) * (1 + ∑' k, d (n + k)) ^ c
  have htail (n m : ℕ) : ∃ z,
      exponentialPartialProduct Exp (fun k => X (n + k)) m = Exp z ∧
        ‖b.equivFun z‖ ≤ B n :=
    exists_tail_product_log_bound dynkin Exp hExp hc b hC hbracket X d hd hX n m
  have hB : Tendsto B atTop (𝓝 0) := dynkin_tail_bound_tendsto_zero A c d
  choose z hz hzb using fun m => htail 0 m
  have hz' (m : ℕ) : exponentialPartialProduct Exp X m = Exp (z m) := by
    simpa only [zero_add] using hz m
  have hbounded (m : ℕ) : b.equivFun (z m) ∈ closedBall 0 (B 0) := by
    simpa only [mem_closedBall, dist_zero_right] using hzb m
  obtain ⟨a, _, r, hr, hconv⟩ := (isCompact_closedBall (0 : J → ℝ) (B 0)).tendsto_subseq hbounded
  let g := Exp (b.equivFun.symm a)
  have hExpcont : Continuous Exp := by
    have heq : (chart : GroupLieAlgebra (𝓘(ℝ, E)) G → G) = Exp := funext hchart
    rw [← heq]
    exact chart.continuous
  have hsubseq : Tendsto (fun n => exponentialPartialProduct Exp X (r n)) atTop (𝓝 g) := by
    have ht := (hExpcont.comp b.equivFun.symm.toContinuousLinearEquiv.continuous).tendsto a |>.comp hconv
    simpa only [Function.comp_def, LinearEquiv.coe_toContinuousLinearEquiv',
      LinearEquiv.symm_apply_apply, g, ← hz'] using ht
  choose w hw hwb using fun n => htail n (r n - n)
  have hwzero : Tendsto (fun n => b.equivFun (w n)) atTop (𝓝 0) :=
    squeeze_zero_norm hwb hB
  have hwExp : Tendsto (fun n => Exp (w n)) atTop (𝓝 (1 : G)) := by
    have ht := (hExpcont.comp b.equivFun.symm.toContinuousLinearEquiv.continuous).tendsto 0 |>.comp hwzero
    simpa only [Function.comp_def, LinearEquiv.coe_toContinuousLinearEquiv',
      LinearEquiv.symm_apply_apply, map_zero, hExp.map_zero] using ht
  have hidentity (n : ℕ) : exponentialPartialProduct Exp X n =
      exponentialPartialProduct Exp X (r n) * (Exp (w n))⁻¹ := by
    apply eq_mul_inv_iff_mul_eq.mpr
    have hh := exponentialPartialProduct_add Exp X n (r n - n)
    have hn : n ≤ r n := hr.id_le n
    rw [Nat.add_sub_of_le hn, hw n] at hh
    exact hh.symm
  refine ⟨g, ?_⟩
  have ht := hsubseq.mul hwExp.inv
  simpa only [inv_one, mul_one, ← hidentity] using ht

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_QuotientChainDecay
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Contracting quotient increments along the actual factor lifts -/

noncomputable section
namespace PolycyclicRecognition

open Module LieModule Filter Set
open scoped Manifold Topology

/-- The quotient increment is the actual Cartan action on the relative
ambient increment. Dependence on the nilpotent factor cancels exactly. -/
theorem factor_quotient_increment
    {N D G Q : Type} [Group N] [Group D] [Group G] [Group Q]
    (ι : N →* G) (κ : D →* G) (π : N →* Q)
    (α : D →* MulAut Q) (act : G →* Equiv.Perm Q)
    (hact : ∀ n d q, act (ι n * κ d) q = π n * α d q)
    (x y : G) (u : N) (d : D) (hx : ι u * κ d = x) :
    (act x 1)⁻¹ * act y 1 = α d (act (x⁻¹ * y) 1) := by
  have he : act y 1 = act x (act (x⁻¹ * y) 1) := by
    rw [← Equiv.Perm.mul_apply, ← map_mul, mul_inv_cancel_left]
  rw [he, ← hx, hact, hact, map_one, mul_one, inv_mul_cancel_left]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_FactorQuotientIncrementBounds
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Summable bounds for the actual projected ray increments -/

noncomputable section
namespace PolycyclicRecognition

open Set

/-- Polynomial Cartan coordinates and negative linear height turn the
compact-set contraction into the summable bound used for ray trajectories. -/
theorem factor_quotient_increment_polynomial_exp_bound
    {N D G Q V : Type} [Group N] [Group D] [Group G] [Group Q]
    [SeminormedAddCommGroup V]
    (ι : N →* G) (κ : D →* G) (π : N →* Q)
    (α : D →* MulAut Q) (act : G →* Equiv.Perm Q)
    (hact : ∀ u d q, act (ι u * κ d) q = π u * α d q)
    (log : Q → V) (size height : D → ℝ) (K : Set Q)
    {A rate B gap : ℝ} (hA : 0 ≤ A) (hrate : 0 < rate) (hB : 0 ≤ B) (hgap : 0 < gap)
    (p degree : ℕ)
    (hcontract : ∀ d, height d ≤ 0 → ∀ q ∈ K,
      ‖log (α d q)‖ ≤ A * (1 + size d) ^ p * Real.exp (rate * height d))
    (n : ℕ) (x y : G) (u : N) (d : D) (hlift : ι u * κ d = x)
    (hsize0 : 0 ≤ size d) (hsize : size d ≤ B * (1 + (n : ℝ)) ^ degree)
    (hheight : height d ≤ -gap * n) (hstep : act (x⁻¹ * y) 1 ∈ K) :
    ‖log ((act x 1)⁻¹ * act y 1)‖ ≤
      (A * (1 + B) ^ p) * (1 + (n : ℝ)) ^ (degree * p) * Real.exp (-(rate * gap) * n) := by
  rw [factor_quotient_increment ι κ π α act hact x y u d hlift]
  have hneg : height d ≤ 0 := hheight.trans
    (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hgap.le) (Nat.cast_nonneg n))
  have hb : 1 + size d ≤ (1 + B) * (1 + (n : ℝ)) ^ degree := by
    have hp : 1 ≤ (1 + (n : ℝ)) ^ degree := one_le_pow₀ (by linarith [Nat.cast_nonneg (α := ℝ) n])
    nlinarith
  have hpoly : (1 + size d) ^ p ≤ (1 + B) ^ p * (1 + (n : ℝ)) ^ (degree * p) := by
    calc
      _ ≤ ((1 + B) * (1 + (n : ℝ)) ^ degree) ^ p := pow_le_pow_left₀ (by linarith) hb _
      _ = _ := by rw [mul_pow, ← pow_mul]
  have hexp : Real.exp (rate * height d) ≤ Real.exp (-(rate * gap) * n) := by
    apply Real.exp_le_exp.mpr
    have hh := mul_le_mul_of_nonneg_left hheight hrate.le
    nlinarith
  calc
    _ ≤ A * (1 + size d) ^ p * Real.exp (rate * height d) := hcontract d hneg _ hstep
    _ ≤ A * ((1 + B) ^ p * (1 + (n : ℝ)) ^ (degree * p)) *
        Real.exp (-(rate * gap) * n) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hpoly hA) hexp
        (Real.exp_nonneg _) (by positivity)
    _ = _ := by ring

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_UniformDynkinProducts
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instNonemptyBases _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_nonempty _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Uniform convergence in exponential coordinates

Compact coordinate balls give a uniform modulus for right multiplication
by a small exponential. Combining it with the common BCH tail estimate
gives uniform convergence of families of contracting products. No
invariance of the coordinate metric is asserted or used.
-/

noncomputable section

namespace PolycyclicRecognition

open Module LieModule Filter Metric
open scoped BigOperators Manifold Topology

/-- Right multiplication by a point tending to the identity approaches the
identity map uniformly on each bounded coordinate ball. -/
theorem exists_coordinate_mul_modulus
    {V G : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    (e : V ≃ₜ G) (he : e 0 = 1) (R : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x : V, ‖x‖ ≤ R → ∀ y : V, ‖y‖ < δ →
      dist (e.symm (e x * e y)) x < ε := by
  let K : Set V := closedBall 0 R
  let : CompactSpace K := isCompact_iff_compactSpace.mp (isCompact_closedBall (0 : V) R)
  let F : V → K → V := fun y x => e.symm (e x.val * e y)
  have hF : Continuous (Function.uncurry F) :=
    e.symm.continuous.comp ((e.continuous.comp continuous_snd.subtype_val).mul
      (e.continuous.comp continuous_fst))
  have hu := Continuous.tendstoUniformly F hF 0
  have hn := (Metric.tendstoUniformly_iff.mp hu) ε hε
  obtain ⟨δ, hδ, hb⟩ := Metric.mem_nhds_iff.mp hn
  refine ⟨δ, hδ, ?_⟩
  intro x hx y hy
  let x' : K := ⟨x, by simpa only [K, mem_closedBall, dist_zero_right] using hx⟩
  have hh := hb (show y ∈ ball 0 δ by simpa only [mem_ball, dist_zero_right] using hy) x'
  simpa only [F, he, mul_one, e.symm_apply_apply, dist_comm] using hh

/-- Pointwise limits of a uniformly Cauchy family of sequences are uniform
limits. The tail estimate is only needed in the forward direction. -/
theorem tendstoUniformly_of_uniform_forward_cauchy
    {P V : Type} [PseudoMetricSpace V] (f : P → ℕ → V) (b : P → V)
    (hlim : ∀ p, Tendsto (f p) atTop (𝓝 (b p)))
    (hc : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ p n, N ≤ n → ∀ m, n ≤ m →
      dist (f p n) (f p m) < ε) :
    TendstoUniformly (fun n p => f p n) b atTop := by
  apply Metric.tendstoUniformly_iff.mpr
  intro ε hε
  obtain ⟨N, hN⟩ := hc (ε / 2) (half_pos hε)
  filter_upwards [eventually_ge_atTop N] with n hn p
  have hh : dist (f p n) (b p) ≤ ε / 2 := by
    apply le_of_tendsto (tendsto_const_nhds.dist (hlim p))
    filter_upwards [eventually_ge_atTop n] with m hm
    exact (hN p n hn m hm).le
  exact (dist_comm _ _).trans_le hh |>.trans_lt (half_lt_self hε)

section ActualProducts

variable {E G J P : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace G] [ChartedSpace E G] [Group G]
  [LieGroup (𝓘(ℝ, E)) ⊤ G] [T2Space G] [Fintype J]

/-- A common summable logarithmic increment bound gives uniform convergence
in any fixed global exponential coordinates. This applies simultaneously
to the normalized trajectories for an entire quasi-isometry family. -/
theorem exists_uniform_limit_of_summable_log_products
    (dynkin : NilpotentDynkinExpansionInput E G)
    (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G) (hExp : IsGroupExponential Exp)
    (chart : GroupLieAlgebra (𝓘(ℝ, E)) G ≃ₜ G) (hchart : ∀ v, chart v = Exp v)
    {c : ℕ} (hc : lowerCentralSeries ℝ (GroupLieAlgebra (𝓘(ℝ, E)) G)
      (GroupLieAlgebra (𝓘(ℝ, E)) G) c = ⊥)
    (b : Basis J ℝ (GroupLieAlgebra (𝓘(ℝ, E)) G))
    {C : ℝ} (hC : 0 ≤ C) (hbracket : ∀ i j k, |b.repr ⁅b i, b j⁆ k| ≤ C)
    (X : P → ℕ → GroupLieAlgebra (𝓘(ℝ, E)) G) (d : ℕ → ℝ) (hd : Summable d)
    (hX : ∀ p n, ‖b.equivFun (X p n)‖ ≤ d n) :
    ∃ g : P → G,
      (∀ p, Tendsto (exponentialPartialProduct Exp (X p)) atTop (𝓝 (g p))) ∧
      TendstoUniformly
        (fun n p => b.equivFun (chart.symm (exponentialPartialProduct Exp (X p) n)))
        (fun p => b.equivFun (chart.symm (g p))) atTop := by
  let : IsTopologicalGroup G := topologicalGroup_of_lieGroup (𝓘(ℝ, E)) ⊤
  let e : (J → ℝ) ≃ₜ G := b.equivFun.symm.toContinuousLinearEquiv.toHomeomorph.trans chart
  have he (v : J → ℝ) : e v = Exp (b.equivFun.symm v) := hchart _
  have he0 : e 0 = 1 := by rw [he, map_zero, hExp.map_zero]
  have heExp (v : GroupLieAlgebra (𝓘(ℝ, E)) G) : e.symm (Exp v) = b.equivFun v := by
    have hh : Exp v = e (b.equivFun v) := by rw [he, b.equivFun.symm_apply_apply]
    rw [hh, e.symm_apply_apply]
  have heInv (g : G) : e.symm g = b.equivFun (chart.symm g) := rfl
  let A := (c : ℝ) * 2 ^ c * (1 + (Fintype.card J : ℝ) ^ 2 * C) ^ c
  let B := fun n => A * (∑' k, d (n + k)) * (1 + ∑' k, d (n + k)) ^ c
  have hB : Tendsto B atTop (𝓝 0) := dynkin_tail_bound_tendsto_zero A c d
  have htail (p : P) (n m : ℕ) : ∃ z,
      exponentialPartialProduct Exp (fun k => X p (n + k)) m = Exp z ∧
        ‖b.equivFun z‖ ≤ B n :=
    exists_tail_product_log_bound dynkin Exp hExp hc b hC hbracket (X p) d hd (hX p) n m
  choose g hg using fun p => exponentialPartialProduct_tendsto_of_summable
    dynkin Exp hExp chart hchart hc b hC hbracket (X p) d hd (hX p)
  refine ⟨g, hg, ?_⟩
  have hprefix (p : P) (n : ℕ) : ‖e.symm (exponentialPartialProduct Exp (X p) n)‖ ≤ B 0 := by
    obtain ⟨z, hz, hbound⟩ := htail p 0 n
    have hz' : exponentialPartialProduct Exp (X p) n = Exp z := by simpa only [zero_add] using hz
    rw [hz', heExp]
    exact hbound
  have huniform : TendstoUniformly
      (fun n p => e.symm (exponentialPartialProduct Exp (X p) n)) (fun p => e.symm (g p)) atTop := by
    apply tendstoUniformly_of_uniform_forward_cauchy
    · intro p
      exact e.symm.continuous.tendsto (g p) |>.comp (hg p)
    · intro ε hε
      obtain ⟨δ, hδ, hmul⟩ := exists_coordinate_mul_modulus e he0 (B 0) hε
      obtain ⟨N, hN⟩ := eventually_atTop.mp (hB.eventually (eventually_lt_nhds hδ))
      refine ⟨N, ?_⟩
      intro p n hn m hnm
      obtain ⟨z, hz, hbound⟩ := htail p n (m - n)
      have hfactor := exponentialPartialProduct_add Exp (X p) n (m - n)
      rw [Nat.add_sub_of_le hnm, hz] at hfactor
      have hh := hmul (e.symm (exponentialPartialProduct Exp (X p) n)) (hprefix p n)
        (b.equivFun z) (hbound.trans_lt (hN n hn))
      rw [e.apply_symm_apply, he, b.equivFun.symm_apply_apply, ← hfactor] at hh
      exact (dist_comm _ _).trans_lt hh
  simpa only [heInv] using huniform

end ActualProducts
end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_BoundaryFromLogProducts
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instNonemptyBases _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_nonempty _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Boundary limits from contracting logarithmic increments

The actual finite BCH estimate constructs uniform normalized limits in
a common compact set. Continuous trajectories then define a continuous
boundary map on an actual quotient whenever trajectories in a common
fiber are asymptotic. Only that geometric fiber condition remains an
input here; no boundary map or compact shadow is assumed.
-/

noncomputable section

namespace PolycyclicRecognition

open Module LieModule Filter Metric
open scoped BigOperators Manifold Topology

variable {E G J P : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace G] [ChartedSpace E G] [Group G]
  [LieGroup (𝓘(ℝ, E)) ⊤ G] [T2Space G] [Fintype J]

/-- The normalized product limits of a whole contracting family lie in
one compact set, while convergence is uniform in exponential coordinates. -/
theorem exists_compact_uniform_log_product_limit
    (dynkin : NilpotentDynkinExpansionInput E G)
    (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G) (hExp : IsGroupExponential Exp)
    (chart : GroupLieAlgebra (𝓘(ℝ, E)) G ≃ₜ G) (hchart : ∀ v, chart v = Exp v)
    {c : ℕ} (hc : lowerCentralSeries ℝ (GroupLieAlgebra (𝓘(ℝ, E)) G)
      (GroupLieAlgebra (𝓘(ℝ, E)) G) c = ⊥)
    (b : Basis J ℝ (GroupLieAlgebra (𝓘(ℝ, E)) G))
    {C : ℝ} (hC : 0 ≤ C) (hbracket : ∀ i j k, |b.repr ⁅b i, b j⁆ k| ≤ C)
    (X : P → ℕ → GroupLieAlgebra (𝓘(ℝ, E)) G) (d : ℕ → ℝ) (hd : Summable d)
    (hX : ∀ p n, ‖b.equivFun (X p n)‖ ≤ d n) :
    ∃ (g : P → G) (K : Set G), IsCompact K ∧ (∀ p, g p ∈ K) ∧
      (∀ p, Tendsto (exponentialPartialProduct Exp (X p)) atTop (𝓝 (g p))) ∧
      TendstoUniformly
        (fun n p => b.equivFun (chart.symm (exponentialPartialProduct Exp (X p) n)))
        (fun p => b.equivFun (chart.symm (g p))) atTop := by
  obtain ⟨g, hg, hu⟩ := exists_uniform_limit_of_summable_log_products
    dynkin Exp hExp chart hchart hc b hC hbracket X d hd hX
  let R := (c : ℝ) * 2 ^ c * (1 + (Fintype.card J : ℝ) ^ 2 * C) ^ c *
    (∑' k, d k) * (1 + ∑' k, d k) ^ c
  let k : (J → ℝ) → G := fun v => chart (b.equivFun.symm v)
  have hk : Continuous k := chart.continuous.comp b.equivFun.symm.toContinuousLinearEquiv.continuous
  have hcoords : Continuous (fun q : G => b.equivFun (chart.symm q)) :=
    b.equivFun.toContinuousLinearEquiv.continuous.comp chart.symm.continuous
  have hbound (p : P) (n : ℕ) :
      ‖b.equivFun (chart.symm (exponentialPartialProduct Exp (X p) n))‖ ≤ R := by
    obtain ⟨z, hz, hzbound⟩ := exists_tail_product_log_bound
      dynkin Exp hExp hc b hC hbracket (X p) d hd (hX p) 0 n
    have hz' : exponentialPartialProduct Exp (X p) n = Exp z := by
      simpa only [zero_add] using hz
    rw [hz', ← hchart, chart.symm_apply_apply]
    simpa only [zero_add, R] using hzbound
  refine ⟨g, k '' closedBall 0 R, (isCompact_closedBall (0 : J → ℝ) R).image hk, ?_, hg, hu⟩
  intro p
  have hlim := (hcoords.norm.tendsto (g p)).comp (hg p)
  have hnorm : ‖b.equivFun (chart.symm (g p))‖ ≤ R :=
    le_of_tendsto hlim (Filter.Eventually.of_forall (hbound p))
  refine ⟨b.equivFun (chart.symm (g p)), ?_, ?_⟩
  · simpa only [mem_closedBall, dist_zero_right] using hnorm
  · simp only [k, b.equivFun.symm_apply_apply, chart.apply_symm_apply]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_FactorTrajectoryIncrements
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual ray trajectories have summable logarithmic increments -/

noncomputable section
namespace PolycyclicRecognition

open Module LieModule Set
open scoped Manifold

/-- Uniform negative heights and polynomial Cartan coordinates give
the actual logarithmic increments needed by the boundary-limit theorem. -/
theorem factor_trajectory_summable_log_increments
    {P N D G E Q J : Type} [Group N] [Group D] [Group G]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace Q] [ChartedSpace E Q] [Group Q]
    [LieGroup (𝓘(ℝ, E)) ⊤ Q] [Fintype J]
    (ι : N →* G) (κ : D →* G) (π : N →* Q)
    (α : D →* MulAut Q) (act : G →* Equiv.Perm Q)
    (hact : ∀ u d q, act (ι u * κ d) q = π u * α d q)
    (Exp : GroupLieAlgebra (𝓘(ℝ, E)) Q → Q)
    (chart : GroupLieAlgebra (𝓘(ℝ, E)) Q ≃ₜ Q) (hchart : ∀ v, chart v = Exp v)
    (b : Basis J ℝ (GroupLieAlgebra (𝓘(ℝ, E)) Q))
    (size height : D → ℝ) (K : Set Q)
    {A rate B gap : ℝ} (hA : 0 ≤ A) (hrate : 0 < rate) (hB : 0 ≤ B) (hgap : 0 < gap)
    (p degree : ℕ)
    (hcontract : ∀ d, height d ≤ 0 → ∀ q ∈ K,
      ‖b.equivFun (chart.symm (α d q))‖ ≤ A * (1 + size d) ^ p * Real.exp (rate * height d))
    (y : P → ℕ → G) (u : P → ℕ → N) (d : P → ℕ → D)
    (hlift : ∀ x n, ι (u x n) * κ (d x n) = y x n)
    (hsize0 : ∀ x n, 0 ≤ size (d x n))
    (hsize : ∀ x n, size (d x n) ≤ B * (1 + (n : ℝ)) ^ degree)
    (hheight : ∀ x n, height (d x n) ≤ -gap * n)
    (hstep : ∀ x n, act ((y x n)⁻¹ * y x (n + 1)) 1 ∈ K) :
    ∃ (X : P → ℕ → GroupLieAlgebra (𝓘(ℝ, E)) Q) (a : ℕ → ℝ),
      Summable a ∧ (∀ x n, ‖b.equivFun (X x n)‖ ≤ a n) ∧
      ∀ x n, act (y x (n + 1)) 1 = act (y x n) 1 * Exp (X x n) := by
  let X := fun x n => chart.symm ((act (y x n) 1)⁻¹ * act (y x (n + 1)) 1)
  let a := fun n : ℕ => (A * (1 + B) ^ p) * (1 + (n : ℝ)) ^ (degree * p) *
    Real.exp (-(rate * gap) * n)
  refine ⟨X, a, summable_polynomial_exp_decay _ _ (mul_pos hrate hgap), ?_, ?_⟩
  · intro x n
    exact factor_quotient_increment_polynomial_exp_bound ι κ π α act hact
      (fun q => b.equivFun (chart.symm q)) size height K hA hrate hB hgap p degree
      hcontract n (y x n) (y x (n + 1)) (u x n) (d x n) (hlift x n)
      (hsize0 x n) (hsize x n) (hheight x n) (hstep x n)
  · intro x n
    dsimp only [X]
    rw [← hchart, chart.apply_symm_apply, mul_inv_cancel_left]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_TrajectoryProductLimits
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.chartExponentialFlow_zero _root_.OAI.PolycyclicRecognition.derivationSemidirectHom_apply _root_.OAI.PolycyclicRecognition.exponentialHomOfDynkin_apply_exp _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.integrateNilpotentLieEquiv_apply_exp _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Common compact limits of normalized quotient trajectories -/

noncomputable section
namespace PolycyclicRecognition

open Module LieModule Filter Set
open scoped Manifold Topology

/-- The actual trajectory, normalized at its first point, equals the
ordered product of its logarithmic increments. A common summable bound
therefore gives uniform coordinate convergence and a common compact limit set. -/
theorem trajectory_compact_uniform_limit_of_log_increments
    {P E Q J : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace Q] [ChartedSpace E Q] [Group Q]
    [LieGroup (𝓘(ℝ, E)) ⊤ Q] [T2Space Q] [Fintype J]
    (dynkin : NilpotentDynkinExpansionInput E Q)
    (Exp : GroupLieAlgebra (𝓘(ℝ, E)) Q → Q) (hExp : IsGroupExponential Exp)
    (chart : GroupLieAlgebra (𝓘(ℝ, E)) Q ≃ₜ Q) (hchart : ∀ v, chart v = Exp v)
    (hnil : LieRing.IsNilpotent (GroupLieAlgebra (𝓘(ℝ, E)) Q))
    (b : Basis J ℝ (GroupLieAlgebra (𝓘(ℝ, E)) Q))
    (f : P → ℕ → Q) (X : P → ℕ → GroupLieAlgebra (𝓘(ℝ, E)) Q)
    (a : ℕ → ℝ) (ha : Summable a) (hX : ∀ p n, ‖b.equivFun (X p n)‖ ≤ a n)
    (hstep : ∀ p n, f p (n + 1) = f p n * Exp (X p n)) :
    ∃ (g : P → Q) (K : Set Q), IsCompact K ∧ (∀ p, g p ∈ K) ∧
      (∀ p, Tendsto (fun n => (f p 0)⁻¹ * f p n) atTop (𝓝 (g p))) ∧
      TendstoUniformly (fun n p => b.equivFun (chart.symm ((f p 0)⁻¹ * f p n)))
        (fun p => b.equivFun (chart.symm (g p))) atTop := by
  obtain ⟨c, hc⟩ := (LieModule.isNilpotent_iff ℝ _ _).mp hnil
  obtain ⟨B, hB, hbracket⟩ := exists_basis_structureConstant_bound b
  obtain ⟨g, K, hK, hgK, hg, hu⟩ := exists_compact_uniform_log_product_limit
    dynkin Exp hExp chart hchart hc b hB hbracket X a ha hX
  have hfactor (p : P) (n : ℕ) : f p n = f p 0 * exponentialPartialProduct Exp (X p) n := by
    induction n with
    | zero => simp [exponentialPartialProduct]
    | succ n ih =>
      rw [hstep, ih, exponentialPartialProduct_add Exp (X p) n 1]
      simp [exponentialPartialProduct, mul_assoc]
  have he (p : P) (n : ℕ) : (f p 0)⁻¹ * f p n = exponentialPartialProduct Exp (X p) n := by
    rw [hfactor p n, inv_mul_cancel_left]
  refine ⟨g, K, hK, hgK, ?_, ?_⟩
  · intro p
    simpa only [he] using hg p
  · simpa only [he] using hu

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
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_CoarseRayFactorBounds
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform factor bounds along centered coarse rays -/

noncomputable section
namespace PolycyclicRecognition

/-- A common sublinear height estimate makes every centered coarse ray
uniformly negative after one shift. Actual metric factorization then gives
uniform polynomial Cartan coordinates and bounded relative increments. -/
theorem centered_coarse_ray_factor_bounds
    {P S N D G : Type} [MetricSpace S] [One S]
    [Group N] [Group D] [Group G] [MetricSpace G] [IsIsometricSMul G G]
    (ι : N →* G) (κ : D →* G) (size height : D → ℝ)
    (sourceHeight : S → ℝ) (targetHeight : G → ℝ)
    (f : P → S → G) (hcenter : ∀ p, f p 1 = 1)
    {L error R gap step B : ℝ} (hL : 0 ≤ L) (hR : 0 ≤ R) (hgap : 0 < gap) (hB : 0 ≤ B)
    (hf : ∀ p x y, dist (f p x) (f p y) ≤ L * dist x y + error)
    (hsub : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧ ∀ p x,
      |targetHeight (f p x) - sourceHeight x| ≤ ε * dist 1 x + C)
    (ray : ℕ → S) (hray : ∀ n, dist 1 (ray n) ≤ R * n)
    (hnegative : ∀ n, sourceHeight (ray n) ≤ -gap * n)
    (hstep : ∀ n, dist (ray n) (ray (n + 1)) ≤ step)
    (degree : ℕ)
    (hfactor : ∀ g : G, ∃ u d, ι u * κ d = g ∧ 0 ≤ size d ∧
      size d ≤ B * (3 + dist 1 g) ^ degree ∧ height d = targetHeight g) :
    ∃ (n₀ : ℕ) (C : ℝ), 0 ≤ C ∧ ∃ (u : P → ℕ → N) (d : P → ℕ → D),
      (∀ p n, ι (u p n) * κ (d p n) = f p (ray (n + n₀)) ∧
        0 ≤ size (d p n) ∧ size (d p n) ≤ C * (1 + (n : ℝ)) ^ degree ∧
        height (d p n) ≤ -(gap / 2) * n) ∧
      ∀ p n, dist (f p (ray (n + n₀))) (f p (ray (n + 1 + n₀))) ≤ L * step + error := by
  classical
  have hs : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧ ∀ z : P × S,
      ‖targetHeight (f z.1 z.2) - sourceHeight z.2‖ ≤ ε * dist 1 z.2 + C := by
    intro ε hε
    obtain ⟨C, hC, hc⟩ := hsub ε hε
    exact ⟨C, hC, fun z => by simpa only [Real.norm_eq_abs] using hc z.1 z.2⟩
  obtain ⟨r₀, _, hsmall⟩ := uniform_sublinear_on_balls (fun z : P × S => dist 1 z.2)
    hs hR (gap / 2) (half_pos hgap)
  let n₀ := ⌈r₀⌉₊
  have hn₀ : r₀ ≤ (n₀ : ℝ) := Nat.le_ceil r₀
  let T := 3 + L * R * (n₀ + 1) + |error|
  have hT : 0 ≤ T := by dsimp [T] <;> positivity
  choose u d hd using fun p n => hfactor (f p (ray (n + n₀)))
  refine ⟨n₀, B * T ^ degree, by positivity, u, d, ?_, ?_⟩
  · intro p n
    obtain ⟨he, h0, hb, hh⟩ := hd p n
    refine ⟨he, h0, hb.trans ?_, ?_⟩
    · have hdist : dist 1 (f p (ray (n + n₀))) ≤ L * (R * (n + n₀)) + error := by
        have hl := hf p 1 (ray (n + n₀))
        rw [hcenter] at hl
        have hh := hl.trans (add_le_add (mul_le_mul_of_nonneg_left (hray (n + n₀)) hL) (le_refl error))
        simpa only [Nat.cast_add] using hh
      have ht : 3 + dist 1 (f p (ray (n + n₀))) ≤ T * (1 + (n : ℝ)) := by
        have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
        have hn₀' : (0 : ℝ) ≤ n₀ := Nat.cast_nonneg n₀
        have hLR := mul_nonneg hL hR
        have hcross := mul_nonneg hLR (mul_nonneg hn₀' hn)
        have he' := le_abs_self error
        change 3 + dist 1 (f p (ray (n + n₀))) ≤
          (3 + L * R * ((n₀ : ℝ) + 1) + |error|) * (1 + n)
        nlinarith [abs_nonneg error]
      calc
        B * (3 + dist 1 (f p (ray (n + n₀)))) ^ degree ≤
            B * (T * (1 + (n : ℝ))) ^ degree := by gcongr
        _ = (B * T ^ degree) * (1 + (n : ℝ)) ^ degree := by rw [mul_pow]; ring
    · rw [hh]
      have hn : r₀ ≤ ((n + n₀ : ℕ) : ℝ) := hn₀.trans (by exact_mod_cast Nat.le_add_left n₀ n)
      have herr := hsmall ((n + n₀ : ℕ) : ℝ) hn (p, ray (n + n₀)) (hray (n + n₀))
      rw [Real.norm_eq_abs] at herr
      have hupper := le_abs_self (targetHeight (f p (ray (n + n₀))) - sourceHeight (ray (n + n₀)))
      have hneg := hnegative (n + n₀)
      push_cast at herr hneg
      nlinarith [Nat.cast_nonneg (α := ℝ) n₀]
  · intro p n
    have hs' : dist (ray (n + n₀)) (ray (n + 1 + n₀)) ≤ step := by
      simpa only [Nat.add_right_comm n 1 n₀] using hstep (n + n₀)
    exact (hf p _ _).trans (add_le_add (mul_le_mul_of_nonneg_left hs' hL) (le_refl error))

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_CoarseRayQuotientLimits
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Common compact limits for centered coarse rays -/

noncomputable section
namespace PolycyclicRecognition

open Module LieModule Set Filter
open scoped Manifold Topology Pointwise

/-- The actual factor bounds and compact-set contraction give a common
compact limit set for every ray in a centered coarse family. -/
theorem centered_coarse_ray_quotient_limits
    {P S N D G E Q J : Type} [MetricSpace S] [One S]
    [Group N] [Group D] [Group G] [MetricSpace G] [IsIsometricSMul G G]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace Q] [ChartedSpace E Q] [Group Q]
    [LieGroup (𝓘(ℝ, E)) ⊤ Q] [T2Space Q] [Fintype J]
    (ι : N →* G) (κ : D →* G) (π : N →* Q)
    (α : D →* MulAut Q) (act : G →* Equiv.Perm Q)
    (hact : ∀ u d q, act (ι u * κ d) q = π u * α d q)
    (dynkin : NilpotentDynkinExpansionInput E Q)
    (Exp : GroupLieAlgebra (𝓘(ℝ, E)) Q → Q) (hExp : IsGroupExponential Exp)
    (chart : GroupLieAlgebra (𝓘(ℝ, E)) Q ≃ₜ Q) (hchart : ∀ v, chart v = Exp v)
    (hnil : LieRing.IsNilpotent (GroupLieAlgebra (𝓘(ℝ, E)) Q))
    (b : Basis J ℝ (GroupLieAlgebra (𝓘(ℝ, E)) Q))
    (size height : D → ℝ) (sourceHeight : S → ℝ) (targetHeight : G → ℝ)
    (f : P → S → G) (hcenter : ∀ p, f p 1 = 1)
    {L error R gap B rate : ℝ}
    (hL : 0 ≤ L) (hR : 0 ≤ R) (hgap : 0 < gap) (hB : 0 ≤ B) (hrate : 0 < rate)
    (hf : ∀ p x y, dist (f p x) (f p y) ≤ L * dist x y + error)
    (hsub : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧ ∀ p x,
      |targetHeight (f p x) - sourceHeight x| ≤ ε * dist 1 x + C)
    (ray : ℕ → S) {step : ℝ} (hray : ∀ n, dist 1 (ray n) ≤ R * n)
    (hnegative : ∀ n, sourceHeight (ray n) ≤ -gap * n)
    (hstep : ∀ n, dist (ray n) (ray (n + 1)) ≤ step)
    (degree p : ℕ)
    (hfactor : ∀ g : G, ∃ u d, ι u * κ d = g ∧ 0 ≤ size d ∧
      size d ≤ B * (3 + dist 1 g) ^ degree ∧ height d = targetHeight g)
    (horbit : ∀ r : ℝ, ∃ K : Set Q, IsCompact K ∧ ∀ g, dist 1 g ≤ r → act g 1 ∈ K)
    (hcontract : ∀ K : Set Q, IsCompact K → ∃ A : ℝ, 0 ≤ A ∧
      ∀ d, height d ≤ 0 → ∀ q ∈ K,
        ‖b.equivFun (chart.symm (α d q))‖ ≤ A * (1 + size d) ^ p * Real.exp (rate * height d)) :
    ∃ (g : P → Q) (K : Set Q), IsCompact K ∧ (∀ x, g x ∈ K) ∧
      ∀ x, Tendsto (fun n => act (f x (ray n)) 1) atTop (𝓝 (g x)) := by
  let _ : IsTopologicalGroup Q := topologicalGroup_of_lieGroup (𝓘(ℝ, E)) ⊤
  obtain ⟨n₀, C, hC, u, d, hlifts, hsteps⟩ := centered_coarse_ray_factor_bounds
    ι κ size height sourceHeight targetHeight f hcenter hL hR hgap hB hf hsub
    ray hray hnegative hstep degree hfactor
  let y := fun x n => f x (ray (n + n₀))
  obtain ⟨K, hK, hKcover⟩ := horbit (L * step + error)
  obtain ⟨A, hA, hAc⟩ := hcontract K hK
  have hinc (x : P) (n : ℕ) : act ((y x n)⁻¹ * y x (n + 1)) 1 ∈ K := by
    apply hKcover
    have hd : dist 1 ((y x n)⁻¹ * y x (n + 1)) = dist (y x n) (y x (n + 1)) := by
      simpa only [mul_one, mul_inv_cancel_left] using
        (dist_mul_left (y x n) (1 : G) ((y x n)⁻¹ * y x (n + 1))).symm
    rw [hd]
    exact hsteps x n
  obtain ⟨X, a, ha, hX, hXstep⟩ := factor_trajectory_summable_log_increments
    ι κ π α act hact Exp chart hchart b size height K hA hrate hC (half_pos hgap)
    p degree hAc y u d (fun x n => (hlifts x n).1) (fun x n => (hlifts x n).2.1)
    (fun x n => (hlifts x n).2.2.1) (fun x n => (hlifts x n).2.2.2) hinc
  obtain ⟨g, K', hK', hgK', hg, _⟩ := trajectory_compact_uniform_limit_of_log_increments
    dynkin Exp hExp chart hchart hnil b (fun x n => act (y x n) 1) X a ha hX hXstep
  obtain ⟨K₀, hK₀, hK₀cover⟩ := horbit (L * (R * n₀) + error)
  have hy0 (x : P) : act (y x 0) 1 ∈ K₀ := by
    apply hK₀cover
    have hh := hf x 1 (ray n₀)
    rw [hcenter] at hh
    change dist 1 (f x (ray (0 + n₀))) ≤ _
    rw [zero_add]
    exact hh.trans (add_le_add (mul_le_mul_of_nonneg_left (hray n₀) hL) le_rfl)
  refine ⟨fun x => act (y x 0) 1 * g x, K₀ * K', hK₀.mul hK', ?_, ?_⟩
  · intro x
    exact Set.mul_mem_mul (hy0 x) (hgK' x)
  · intro x
    have hc : Tendsto (fun _ : ℕ => act (y x 0) 1) atTop (𝓝 (act (y x 0) 1)) :=
      tendsto_const_nhds
    have ht := hc.mul (hg x)
    have ht' : Tendsto (fun n => act (y x n) 1) atTop
        (𝓝 (act (y x 0) 1 * g x)) := by
      simpa only [mul_inv_cancel_left] using ht
    exact (tendsto_add_atTop_iff_nat n₀).mp ht'

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
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_NegativePathWords
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
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
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_RayQuotientContraction
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instDecidableEqConeMixedWords _root_.OAI.PolycyclicRecognition.CartanWordModel.instFintypeConeMixedWords _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.CartanFactorModel.heightRay_zero _root_.OAI.PolycyclicRecognition.CartanFactorModel.realScaleProfile_apply _root_.OAI.PolycyclicRecognition.CartanFactorModel.sampledProbeProfile_apply _root_.OAI.PolycyclicRecognition.bracketWordDifferential_mul _root_.OAI.PolycyclicRecognition.cartanWeightDerivation_apply_root _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.nilshadowWeightDerivation_symm _root_.OAI.PolycyclicRecognition.nilshadowWeightOperator_symm _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Contraction on the constructed positive-ray quotient

This proves the linear logarithmic estimate underlying
`boundary.tex`, equation (quotient-contraction). The basis is made of actual
pure bracket words in the quotient by the mixed-word ideal. Its scalar
weights are positive multiples of the chosen ray, while its residual
Cartan action has the already-proved polynomial bound.
-/

noncomputable section

namespace PolycyclicRecognition

open Module LieAlgebra LieModule
open scoped BigOperators

/-- A pure word in positive multiples of one form has a strictly positive
multiple of that form as its total exponent. -/
theorem pure_ray_word_exponent
    {I V : Type} [Fintype I] [DecidableEq I] [AddCommGroup V] [Module ℝ V]
    (α : V →ₗ[ℝ] ℝ) (weight : I → V →ₗ[ℝ] ℝ) (w : FreeMagma I)
    (hw : ¬IsMixedWord (fun i => weight i ∉ positiveWeightRay α) w) :
    ∃ c : ℝ, 0 < c ∧ ∀ v, bracketWordExponent (fun i => weight i v) w = c * α v := by
  induction w using FreeMagma.rec with
  | of i =>
    obtain ⟨c, hc, he⟩ := Classical.not_not.mp hw
    refine ⟨c, hc, ?_⟩
    intro v
    simp only [bracketWordExponent_of, he, LinearMap.smul_apply, smul_eq_mul]
  | mul u v hu hv =>
    obtain ⟨a, ha, he⟩ := hu (fun h => hw (Or.inl h))
    obtain ⟨b, hb, hf⟩ := hv (fun h => hw (Or.inr h))
    refine ⟨a + b, add_pos ha hb, ?_⟩
    intro x
    change bracketWordExponent (fun i => weight i x) (u * v) = _
    rw [bracketWordExponent_mul, he, hf, add_mul]

/-- A finite family of positive numbers has one strictly positive lower
bound, including when the index type is empty. -/
theorem exists_pos_le_finite_family {J : Type} [Fintype J]
    (a : J → ℝ) (ha : ∀ j, 0 < a j) :
    ∃ c : ℝ, 0 < c ∧ ∀ j, c ≤ a j := by
  classical
  let S : Finset ℝ := insert 1 (Finset.univ.image a)
  have hS : S.Nonempty := ⟨1, Finset.mem_insert_self _ _⟩
  refine ⟨S.min' hS, (Finset.lt_min'_iff _ _).mpr ?_, ?_⟩
  · intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact zero_lt_one
    · obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hx
      exact ha j
  · intro j
    exact Finset.min'_le _ _ (Finset.mem_insert_of_mem (Finset.mem_image.mpr
      ⟨j, Finset.mem_univ j, rfl⟩))

namespace CartanWordModel

variable {L : Type} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {H : LieSubalgebra ℝ L} [H.IsCartanSubalgebra] (M : CartanWordModel H)
  {n : ℕ} (T : TriangularAdjoint L n)

/-- The exact dilation contracts a pure-word ray quotient basis at a
common exponential rate in every nonpositive ray direction. -/
theorem exists_ray_dilation_bound
    (α : H →ₗ[ℝ] ℝ) {J : Type} [Fintype J]
    (b : Basis J ℝ ((cartanRootIdeal H) ⧸ M.coneWordIdeal (positiveWeightRay α)))
    (words : J → FreeMagma (Fin M.letterCount))
    (hpure : ∀ j, ¬IsMixedWord
      (fun i => (M.weight i : H →ₗ[ℝ] ℝ) ∉ positiveWeightRay α) (words j))
    (hb : ∀ j, (M.coneWordIdeal (positiveWeightRay α)).toSubmodule.mkQ
      (evalBracketWord M.letter (words j)) = b j) :
    ∃ c : ℝ, 0 < c ∧ ∀ (h : H), α h ≤ 0 →
      ∀ v : (cartanRootIdeal H) ⧸ M.coneWordIdeal (positiveWeightRay α),
      ‖b.equivFun ((M.coneWordIdeal (positiveWeightRay α)).toSubmodule.mapQ
        (M.coneWordIdeal (positiveWeightRay α)).toSubmodule
        (cartanIdealWeightDilation T H h).toLinearEquiv.toLinearMap
        (M.coneWordIdeal_dilation_mem T (positiveWeightRay α) h) v)‖ ≤
        Real.exp (c * α h) * ‖b.equivFun v‖ := by
  classical
  choose a ha he using fun j => pure_ray_word_exponent α
    (fun i => (M.weight i : H →ₗ[ℝ] ℝ)) (words j) (hpure j)
  obtain ⟨c, hc, hca⟩ := exists_pos_le_finite_family a ha
  refine ⟨c, hc, ?_⟩
  intro h hh v
  let S := (M.coneWordIdeal (positiveWeightRay α)).toSubmodule
  let D := S.mapQ S (cartanIdealWeightDilation T H h).toLinearEquiv.toLinearMap
    (M.coneWordIdeal_dilation_mem T (positiveWeightRay α) h)
  have hD (j : J) : D (b j) = Real.exp (a j * α h) • b j := by
    rw [← hb j]
    change S.mkQ (cartanIdealWeightDilation T H h
      (evalBracketWord M.letter (words j))) = _
    have hexp := he j h
    change bracketWordExponent (fun i => M.weight i h) (words j) = _ at hexp
    rw [M.idealWeightDilation_word T h, hexp, map_smul]
  have hcoord (j : J) : b.repr (D v) j = Real.exp (a j * α h) * b.repr v j := by
    have heq : (b.coord j).comp D = Real.exp (a j * α h) • b.coord j := by
      apply b.ext
      intro k
      by_cases hkj : k = j
      · subst k
        simp [hD]
      · simp [hD, Basis.coord_apply, hkj]
    exact DFunLike.congr_fun heq v
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro j
  change ‖b.repr (D v) j‖ ≤ _
  rw [hcoord, norm_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact mul_le_mul (Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_right (hca j) hh))
    (norm_le_pi_norm (b.equivFun v) j) (norm_nonneg _) (Real.exp_pos _).le

/-- The actual Cartan action on the quotient by the positive-ray
mixed-word ideal has polynomial times exponential contraction. -/
theorem exists_ray_quotient_contraction (α : H →ₗ[ℝ] ℝ) :
    ∃ (b : Basis
        (Fin (finrank ℝ ((cartanRootIdeal H) ⧸ M.coneWordIdeal (positiveWeightRay α))))
        ℝ ((cartanRootIdeal H) ⧸ M.coneWordIdeal (positiveWeightRay α)))
      (A : ℝ) (p : ℕ) (c : ℝ),
      0 ≤ A ∧ 0 < c ∧ ∀ (h : H), α h ≤ 0 →
        ∀ v : (cartanRootIdeal H) ⧸ M.coneWordIdeal (positiveWeightRay α),
        ‖b.equivFun (M.coneAdjointAutomorphism T (positiveWeightRay α)
          (positiveWeightRay_add α) h v)‖ ≤
        A * (1 + ‖(Module.finBasis ℝ H).equivFun h‖) ^ p *
          Real.exp (c * α h) * ‖b.equivFun v‖ := by
  obtain ⟨b, words, hpure, hb⟩ := exists_pure_quotient_word_basis M.letter
    (fun i => (M.weight i : H →ₗ[ℝ] ℝ) ∉ positiveWeightRay α) M.generates
  obtain ⟨c, hc, hdilation⟩ := M.exists_ray_dilation_bound T α b words hpure hb
  obtain ⟨A, p, hA, hresidual⟩ := M.exists_cone_residual_coordinate_bound T
    (positiveWeightRay α) (positiveWeightRay_add α) b
  refine ⟨b, A, p, c, hA, hc, ?_⟩
  intro h hh v
  let S := (M.coneWordIdeal (positiveWeightRay α)).toSubmodule
  let R := S.mapQ S (cartanIdealResidualAutomorphism T H h).toLinearEquiv.toLinearMap
    (M.coneWordIdeal_residual_mem T (positiveWeightRay α) (positiveWeightRay_add α) h)
  have hfactor : M.coneAdjointAutomorphism T (positiveWeightRay α)
      (positiveWeightRay_add α) h v =
      S.mapQ S (cartanIdealWeightDilation T H h).toLinearEquiv.toLinearMap
        (M.coneWordIdeal_dilation_mem T (positiveWeightRay α) h) (R v) := by
    obtain ⟨x, rfl⟩ := S.mkQ_surjective v
    rfl
  rw [hfactor]
  apply (hdilation h hh (R v)).trans
  calc
    _ ≤ Real.exp (c * α h) *
        (A * (1 + ‖(Module.finBasis ℝ H).equivFun h‖) ^ p * ‖b.equivFun v‖) :=
      mul_le_mul_of_nonneg_left (hresidual h v) (Real.exp_pos _).le
    _ = _ := by ring_nf; rfl

end CartanWordModel
end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_RayGroupContraction
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instDecidableEqConeMixedWords _root_.OAI.PolycyclicRecognition.CartanWordModel.instFintypeConeMixedWords _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Logarithmic contraction of the actual quotient-group action

The Lie-coordinate estimate is transported through the actual bijective
exponential. Compact subsets have bounded logarithmic coordinates. The
action is the exponential conjugate already identified with the descended
Cartan action in `ConeQuotientHaarAction`.
-/

noncomputable section

namespace PolycyclicRecognition

open Module LieAlgebra LieModule Set
open scoped Manifold

section Logarithm

variable {V E G : Type} [LieRing V] [LieAlgebra ℝ V]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace G] [ChartedSpace E G] [Group G] [LieGroup (𝓘(ℝ, E)) ⊤ G]
  (e : V ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, E)) G)
  (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G) (hbij : Function.Bijective Exp)

theorem exp_exponentialLog (g : G) :
    Exp (e (exponentialLog e Exp hbij g)) = g :=
  (Equiv.ofBijective (Exp ∘ e) (hbij.comp e.bijective)).apply_symm_apply g

/-- Conjugation through the exponential acts on its logarithm by the
specified Lie automorphism, exactly. -/
theorem exponentialLog_conjugate (F : V ≃ₗ⁅ℝ⁆ V) (g : G) :
    exponentialLog e Exp hbij (exponentialConjugate e Exp hbij F g) =
      F (exponentialLog e Exp hbij g) := by
  conv_lhs => rw [← exp_exponentialLog e Exp hbij g]
  rw [exponentialConjugate_apply_exp, exponentialLog_exp]

/-- Compact sets in the group have uniformly bounded logarithms in each
finite coordinate basis, using the actual exponential homeomorphism. -/
theorem exists_bound_exponentialLog
    (chart : GroupLieAlgebra (𝓘(ℝ, E)) G ≃ₜ G) (hchart : ∀ v, chart v = Exp v)
    {J : Type} [Fintype J] (b : Basis J ℝ V)
    {K : Set G} (hK : IsCompact K) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ g ∈ K, ‖b.equivFun (exponentialLog e Exp hbij g)‖ ≤ R := by
  let a := (e.toLinearEquiv.symm.trans b.equivFun).toContinuousLinearEquiv
  have hlog (g : G) : exponentialLog e Exp hbij g = e.symm (chart.symm g) := by
    apply e.injective
    apply hbij.injective
    simp only [LieEquiv.coe_coe, LieEquiv.apply_symm_apply]
    rw [exp_exponentialLog e Exp hbij g, ← hchart, chart.apply_symm_apply]
  have hc : Continuous (fun g => b.equivFun (exponentialLog e Exp hbij g)) := by
    simp_rw [hlog]
    exact a.continuous.comp chart.symm.continuous
  obtain ⟨R, hR⟩ := hK.exists_bound_of_continuousOn hc.continuousOn
  exact ⟨max R 0, le_max_right _ _, fun g hg => (hR g hg).trans (le_max_left _ _)⟩

end Logarithm

namespace CartanWordModel

variable {L : Type} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {H : LieSubalgebra ℝ L} [H.IsCartanSubalgebra] (M : CartanWordModel H)
  {n : ℕ} (T : TriangularAdjoint L n)

/-- Every fixed compact set of the actual ray quotient contracts at the
polynomial-exponential rate in logarithmic coordinates. -/
theorem exists_ray_group_compact_contraction
    (α : H →ₗ[ℝ] ℝ)
    (Q : NilpotentLieModel ((cartanRootIdeal H) ⧸ M.coneWordIdeal (positiveWeightRay α)))
    (Exp : GroupLieAlgebra (𝓘(ℝ, Q.modelSpace)) Q.carrier → Q.carrier)
    (hbij : Function.Bijective Exp)
    (chart : GroupLieAlgebra (𝓘(ℝ, Q.modelSpace)) Q.carrier ≃ₜ Q.carrier)
    (hchart : ∀ v, chart v = Exp v) :
    ∃ (b : Basis
        (Fin (finrank ℝ ((cartanRootIdeal H) ⧸ M.coneWordIdeal (positiveWeightRay α))))
        ℝ ((cartanRootIdeal H) ⧸ M.coneWordIdeal (positiveWeightRay α)))
      (p : ℕ) (c : ℝ), 0 < c ∧
      ∀ K : Set Q.carrier, IsCompact K → ∃ A : ℝ, 0 ≤ A ∧
        ∀ (h : H), α h ≤ 0 → ∀ g ∈ K,
        ‖b.equivFun (exponentialLog Q.equiv Exp hbij
          (exponentialConjugate Q.equiv Exp hbij
            (M.coneAdjointAutomorphism T (positiveWeightRay α)
              (positiveWeightRay_add α) h) g))‖ ≤
        A * (1 + ‖(Module.finBasis ℝ H).equivFun h‖) ^ p * Real.exp (c * α h) := by
  obtain ⟨b, A, p, c, hA, hc, hbound⟩ := M.exists_ray_quotient_contraction T α
  refine ⟨b, p, c, hc, ?_⟩
  intro K hK
  obtain ⟨R, hR, hlog⟩ := exists_bound_exponentialLog Q.equiv Exp hbij chart hchart b hK
  refine ⟨A * R, mul_nonneg hA hR, ?_⟩
  intro h hh g hg
  rw [exponentialLog_conjugate]
  apply (hbound h hh (exponentialLog Q.equiv Exp hbij g)).trans
  calc
    _ ≤ A * (1 + ‖(Module.finBasis ℝ H).equivFun h‖) ^ p * Real.exp (c * α h) * R := by
      gcongr
      exact hlog g hg
    _ = _ := by ring

end CartanWordModel
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

section Coordinates
variable {V E G J : Type} [LieRing V] [LieAlgebra ℝ V]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace G] [ChartedSpace E G] [Group G] [LieGroup (𝓘(ℝ, E)) ⊤ G]
  [Fintype J]

theorem mapped_basis_exponentialLog
    (e : V ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, E)) G)
    (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G) (hbij : Function.Bijective Exp)
    (chart : GroupLieAlgebra (𝓘(ℝ, E)) G ≃ₜ G) (hchart : ∀ v, chart v = Exp v)
    (b : Basis J ℝ V) (g : G) :
    (b.map e.toLinearEquiv).equivFun (chart.symm g) =
      b.equivFun (exponentialLog e Exp hbij g) := by
  rw [Basis.map_equivFun]
  change b.equivFun (e.symm (chart.symm g)) = _
  congr 1
  apply e.injective
  apply hbij.injective
  change Exp (e (e.symm (chart.symm g))) = Exp (e (exponentialLog e Exp hbij g))
  rw [e.apply_symm_apply]
  exact ((hchart _).symm.trans (chart.apply_symm_apply g)).trans
    (exp_exponentialLog e Exp hbij g).symm
end Coordinates

/-- Pull back a compact-set contraction estimate along actual factor
coordinates. The coordinate identity is retained pointwise. -/
theorem exists_compact_contraction_pullback
    {V D Q E J : Type} [TopologicalSpace Q]
    [AddCommGroup E] [Module ℝ E] [Fintype J]
    (log : D → V) (size height : V → ℝ) (coords : Q → E)
    (action : V → Q → Q) (actual : D → Q → Q)
    (he : ∀ d q, actual d q = action (log d) q)
    (hb : ∃ (b : Basis J ℝ E) (p : ℕ) (rate : ℝ), 0 < rate ∧
      ∀ K : Set Q, IsCompact K → ∃ A : ℝ, 0 ≤ A ∧
        ∀ v, height v ≤ 0 → ∀ q ∈ K, ‖b.equivFun (coords (action v q))‖ ≤
          A * (1 + size v) ^ p * Real.exp (rate * height v)) :
    ∃ (b : Basis J ℝ E) (p : ℕ) (rate : ℝ), 0 < rate ∧
      ∀ K : Set Q, IsCompact K → ∃ A : ℝ, 0 ≤ A ∧
        ∀ d, height (log d) ≤ 0 → ∀ q ∈ K, ‖b.equivFun (coords (actual d q))‖ ≤
          A * (1 + size (log d)) ^ p * Real.exp (rate * height (log d)) := by
  obtain ⟨b, p, rate, hr, hbound⟩ := hb
  refine ⟨b, p, rate, hr, ?_⟩
  intro K hK
  obtain ⟨A, hA, hh⟩ := hbound K hK
  refine ⟨A, hA, ?_⟩
  intro d hd q hq
  rw [he]
  exact hh (log d) hd q hq

namespace CartanWordModel
variable {L : Type} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {H : LieSubalgebra ℝ L} [H.IsCartanSubalgebra] (M : CartanWordModel H)
  {a : ℕ} (T : TriangularAdjoint L a)

theorem coneAdjoint_projection
    (C : Set (H →ₗ[ℝ] ℝ)) (hadd : ∀ x ∈ C, ∀ y ∈ C, x + y ∈ C)
    (h : H) (x : cartanRootIdeal H) :
    M.coneAdjointAutomorphism T C hadd h (M.coneProjection C x) =
      M.coneProjection C (cartanIdealAdjointAutomorphism T H h x) := rfl

theorem exists_ray_tangent_compact_contraction
    (α : H →ₗ[ℝ] ℝ)
    (Q : NilpotentLieModel ((cartanRootIdeal H) ⧸ M.coneWordIdeal (positiveWeightRay α)))
    (Exp : GroupLieAlgebra (𝓘(ℝ, Q.modelSpace)) Q.carrier → Q.carrier)
    (hbij : Function.Bijective Exp)
    (chart : GroupLieAlgebra (𝓘(ℝ, Q.modelSpace)) Q.carrier ≃ₜ Q.carrier)
    (hchart : ∀ v, chart v = Exp v) :
    ∃ (b : Basis
        (Fin (finrank ℝ ((cartanRootIdeal H) ⧸ M.coneWordIdeal (positiveWeightRay α))))
        ℝ (GroupLieAlgebra (𝓘(ℝ, Q.modelSpace)) Q.carrier)) (p : ℕ) (rate : ℝ),
      0 < rate ∧ ∀ K : Set Q.carrier, IsCompact K → ∃ A : ℝ, 0 ≤ A ∧
        ∀ h : H, α h ≤ 0 → ∀ q ∈ K,
          ‖b.equivFun (chart.symm (exponentialConjugate Q.equiv Exp hbij
            (M.coneAdjointAutomorphism T (positiveWeightRay α)
              (positiveWeightRay_add α) h) q))‖ ≤
            A * (1 + ‖(finBasis ℝ H).equivFun h‖) ^ p * Real.exp (rate * α h) := by
  obtain ⟨b, p, rate, hrate, hb⟩ := M.exists_ray_group_compact_contraction
    T α Q Exp hbij chart hchart
  refine ⟨b.map Q.equiv.toLinearEquiv, p, rate, hrate, ?_⟩
  intro K hK
  obtain ⟨A, hA, hbound⟩ := hb K hK
  refine ⟨A, hA, ?_⟩
  intro h hh q hq
  rw [mapped_basis_exponentialLog Q.equiv Exp hbij chart hchart b]
  exact hbound h hh q hq
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

set_option maxHeartbeats 1000000 in
/-- Compact ambient increments have compact quotient images. This uses
compact lifts of the actual factors, so no continuity of an arbitrarily
chosen factorization or permutation-valued action is assumed. -/
theorem exists_compact_factor_quotient_orbit
    {Q : Type} [Group Q] [TopologicalSpace Q]
    (π : F.N.carrier →* Q) (hπ : Continuous π)
    (α : F.D.carrier →* MulAut Q) (act : G →* Equiv.Perm Q)
    (hact : ∀ u d q, act (F.inclusionN u * F.inclusionD d) q = π u * α d q)
    {K : Set G} (hK : IsCompact K) :
    ∃ C : Set Q, IsCompact C ∧ ∀ g ∈ K, act g 1 ∈ C := by
  obtain ⟨B, hB, hcover⟩ := F.compactLifts K hK
  refine ⟨(fun p : F.N.carrier × F.D.carrier => π p.1) '' B,
    hB.image (hπ.comp continuous_fst), ?_⟩
  intro g hg
  obtain ⟨⟨u, d⟩, hp, he⟩ := hcover hg
  refine ⟨(u, d), hp, ?_⟩
  rw [← he, hact, map_one, mul_one]

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

set_option maxHeartbeats 1000000 in
include hbijQ hchartQ hπ hα hφ in
/-- The contraction estimate is expressed directly in a basis of the
actual tangent algebra and in the actual Cartan factor coordinates. -/
theorem exists_ray_factor_compact_contraction :
    ∃ (b : Basis
        (Fin (finrank ℝ ((cartanRootIdeal H) ⧸ M.coneWordIdeal (positiveWeightRay α₀))))
        ℝ (GroupLieAlgebra (𝓘(ℝ, Q.modelSpace)) Q.carrier)) (p : ℕ) (rate : ℝ),
      0 < rate ∧ ∀ K : Set Q.carrier, IsCompact K → ∃ A : ℝ, 0 ≤ A ∧
        ∀ d : F.D.carrier,
          α₀ (cartanLog H F.D.equiv F.ExpD hbijD d) ≤ 0 → ∀ q ∈ K,
          ‖b.equivFun (chartQ.symm (α d q))‖ ≤
            A * (1 + ‖(finBasis ℝ H).equivFun
              (cartanLog H F.D.equiv F.ExpD hbijD d)‖) ^ p *
              Real.exp (rate * α₀ (cartanLog H F.D.equiv F.ExpD hbijD d)) := by
  exact exists_compact_contraction_pullback
    (cartanLog H F.D.equiv F.ExpD hbijD)
    (fun h => ‖(finBasis ℝ H).equivFun h‖) α₀ chartQ.symm
    (fun h q => exponentialConjugate Q.equiv ExpQ hbijQ
      (M.coneAdjointAutomorphism T (positiveWeightRay α₀) (positiveWeightRay_add α₀) h) q)
    (fun d q => α d q)
    (M.factor_quotient_action_eq_exponential T F α₀ Q ExpQ hbijQ
      hbijN hbijD dynkinN π hπ α hα hφ)
    (M.exists_ray_tangent_compact_contraction T α₀ Q ExpQ hbijQ chartQ hchartQ)

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanRayCompactLimits
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instDecidableEqConeMixedWords _root_.OAI.PolycyclicRecognition.CartanWordModel.instFintypeConeMixedWords _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.CartanFactorModel.heightRay_zero _root_.OAI.PolycyclicRecognition.CartanFactorModel.realScaleProfile_apply _root_.OAI.PolycyclicRecognition.CartanFactorModel.sampledProbeProfile_apply _root_.OAI.PolycyclicRecognition.cartanWeightDerivation_apply_root _root_.OAI.PolycyclicRecognition.chartExponentialFlow_zero _root_.OAI.PolycyclicRecognition.derivationSemidirectHom_apply _root_.OAI.PolycyclicRecognition.exponentialHomOfDynkin_apply_exp _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.modelNilradicalLinearAction_apply _root_.OAI.PolycyclicRecognition.modelNilradicalRotation_apply _root_.OAI.PolycyclicRecognition.modelNilradicalRotation_mul _root_.OAI.PolycyclicRecognition.modelNilradicalRotation_one _root_.OAI.PolycyclicRecognition.nilshadowWeightDerivation_symm _root_.OAI.PolycyclicRecognition.nilshadowWeightOperator_symm _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Common compact shadows of actual centered Cartan rays -/

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
/-- Uniform sublinear height control on a centered family gives a common
compact limit set for its actual projected canonical rays. All polynomial
factor bounds and quotient contraction estimates are derived here. -/
theorem centered_ray_quotient_compact_limits_oai
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
    (hExpG : IsGroupExponential ExpG)
    (A : W →L[ℝ] W) (f : P → G → G) (hcenter : ∀ x, f x 1 = 1)
    {L error : ℝ} (hL : 0 ≤ L)
    (hf : ∀ p x y, dist (f p x) (f p y) ≤ L * dist x y + error)
    (hsub : ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, 0 ≤ B ∧ ∀ p g,
      ‖(height (f p g)).toAdd - A ((height g).toAdd)‖ ≤ ε * dist 1 g + B)
    (v₀ : W) (hv₀ : αW (A v₀) < 0) :
    let ray := fun n : ℕ => ExpG ((n : ℝ) •
      (cartanHeightSection T H (eW.symm v₀) : GroupLieAlgebra (𝓘(ℝ, EG)) G))
    ∃ (g : P → Q.carrier) (K : Set Q.carrier), IsCompact K ∧ (∀ p, g p ∈ K) ∧
      ∀ p, Tendsto (fun n => act (f p (ray n)) 1) atTop (𝓝 (g p)) := by
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
  let logD := cartanLog H F.D.equiv F.ExpD hbijD
  let h₀ := (cartanHeightSection T H (eW.symm v₀) : GroupLieAlgebra (𝓘(ℝ, EG)) G)
  let ray := fun n : ℕ => ExpG ((n : ℝ) • h₀)
  let R := dist (1 : G) (ExpG h₀)
  let β := αW.comp A
  have hray (n : ℕ) : dist 1 (ray n) ≤ R * n := by
    have hh := one_parameter_nat_dist_le (fun t => ExpG (t • h₀))
      (by simpa only [zero_smul] using hExpG.map_zero) (hExpG.map_add_smul h₀) n
    simpa only [one_smul, mul_comm] using hh
  have hnegative (n : ℕ) : β ((height (ray n)).toAdd) ≤ -(-β v₀) * n := by
    have hh : (height (ray n)).toAdd = (n : ℝ) • v₀ := by
      change (height (ExpG ((n : ℝ) • h₀))).toAdd = _
      rw [hheight]
      simp [h₀]
    rw [hh, map_smul, smul_eq_mul]
    nlinarith
  have hsteps (n : ℕ) : dist (ray n) (ray (n + 1)) ≤ R := by
    have he : ray (n + 1) = ray n * ExpG h₀ := by
      dsimp only [ray]
      rw [Nat.cast_add, Nat.cast_one, hExpG.map_add_smul, one_smul]
    rw [he]
    have hd : dist (ray n) (ray n * ExpG h₀) = R := by
      simpa only [mul_one] using dist_mul_left (ray n) (1 : G) (ExpG h₀)
    exact hd.le
  have hscalar := scalar_sublinear_error (fun x : P × G => dist 1 x.2)
    (fun _ => dist_nonneg) (fun x => (height (f x.1 x.2)).toAdd)
    (fun x => A ((height x.2).toAdd)) αW (by
      intro ε hε
      obtain ⟨B, hB, hb⟩ := hsub ε hε
      exact ⟨B, hB, fun x => hb x.1 x.2⟩)
  obtain ⟨B, degree, hB, hfactor⟩ := M.exists_metric_cartan_factor_bound
    T F hunimod eW height hheight chartN hchartN chartD hchartD dynkinN dynkinD
    b₀ γ₀ hφ hpath hKheight hLip
  obtain ⟨b, p, rate, hrate, hcontract⟩ := M.exists_ray_factor_compact_contraction
    T F αH Q ExpQ hbijQ chartQ hchartQ hbijN hbijD dynkinN π hπ α hα hφ
  have hnil := Q.tangent_nilpotent (M.coneQuotient_nilpotent (positiveWeightRay αH))
  apply centered_coarse_ray_quotient_limits F.inclusionN F.inclusionD π α act hact
    dynkinQ ExpQ hExpQ chartQ hchartQ hnil b
    (fun d => ‖(finBasis ℝ H).equivFun (logD d)‖) (fun d => αH (logD d))
    (fun x => β ((height x).toAdd)) (fun x => αW ((height x).toAdd))
    f hcenter hL (show 0 ≤ R from dist_nonneg) (neg_pos.mpr hv₀) hB hrate hf
    ?_ ray hray hnegative hsteps degree p ?_ ?_ hcontract
  · intro ε hε
    obtain ⟨B, hB, hb⟩ := hscalar ε hε
    exact ⟨B, hB, fun x y => hb (x, y)⟩
  · intro g
    obtain ⟨u, d, he, hh, hb⟩ := hfactor g
    refine ⟨u, d, he, norm_nonneg _, hb, ?_⟩
    change αW (eW (heightProjection T.character (logD d))) = _
    rw [← F.inclusionD_height T eW height hheight hbijD d, hh]
  · intro r
    obtain ⟨K, hK, hKcover⟩ := exists_compact_factor_quotient_orbit F π hπcont α act hact
      (isCompact_closedBall (1 : G) r)
    exact ⟨K, hK, fun g hg => hKcover g (by simpa only [Metric.mem_closedBall, dist_comm] using hg)⟩

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

theorem solution : type_of% @OAI.PolycyclicRecognition.CartanWordModel.centered_ray_quotient_compact_limits_oai := @OAI.PolycyclicRecognition.CartanWordModel.centered_ray_quotient_compact_limits_oai
