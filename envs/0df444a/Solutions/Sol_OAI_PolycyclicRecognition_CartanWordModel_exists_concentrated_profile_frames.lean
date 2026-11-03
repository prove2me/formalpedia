-- Prove2me | solution 1 for OAI.PolycyclicRecognition.CartanWordModel.exists_concentrated_profile_frames
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-02T23:53:05.00225+00:00
-- url     : https://prove2.me/submissions/5aa6e1c6-ae02-4053-8920-32038a77a69f

import Mathlib
import Definitions.Def_PolycyclicRecognition
import Definitions.Def_OAIQ093D006
import Definitions.Def_OAIQ093D013
import Definitions.Def_OAIQ093D015
import Theorems.Thm_OAI_PolycyclicRecognition_CartanWordModel_exists_compact_template_profile_paths
import Theorems.Thm_OAI_PolycyclicRecognition_CartanWordModel_select_linked_profiles_of_published_inputs

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_GradedGeneratorLimit
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
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
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
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

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_GradedHeight
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
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

/-- The rescaled coordinates of a scaled pivot retain exactly its height. -/
theorem word_length_chart_pivot_height
    (X : I → L) (S : Finset (FreeMagma I)) (β : WordBasisSelections X S)
    (height : L →ₗ[ℝ] W) (hkill : ∀ x y : L, height ⁅x, y⁆ = 0)
    {r : ℝ} (hr : 0 < r) (pivot : L) :
    let b := WordBasisSelections.basis X S β
    let cost := fun j => bracketWordExponent (fun _ : I => 1) (β.val j)
    let br := exponentialRescaleBasis b cost (Real.log r)
    height (b.equivFun.symm (br.equivFun (r • pivot))) = height pivot := by
  dsimp only
  let b := WordBasisSelections.basis X S β
  let br := exponentialRescaleBasis b
    (fun j => bracketWordExponent (fun _ : I => 1) (β.val j)) (Real.log r)
  have he : height (br.equivFun.symm (br.equivFun (r • pivot))) =
      r • height (b.equivFun.symm (br.equivFun (r • pivot))) := by
    simpa only [b, br, bracketWordExponent_one] using
      word_length_chart_height X S β height hkill hr (br.equivFun (r • pivot))
  rw [LinearEquiv.symm_apply_apply, map_smul] at he
  exact ((smul_right_injective W hr.ne') he).symm

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_WordPivotCoordinates
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.CartanFactorModel.realScaleProfile_apply _root_.OAI.PolycyclicRecognition.bracketWordDifferential_mul _root_.OAI.PolycyclicRecognition.exponentialRescaleBasis_zero _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Compact coordinates for the actual rescaled contact pivot -/

noncomputable section
namespace PolycyclicRecognition

open Module Set Filter
open scoped Topology

/-- The pivot coordinate moves with the weighted chart. It stays in one
compact part of the height domain and has exactly the original height. -/
theorem exists_compact_word_pivot_coordinates
    {L W I : Type} [LieRing L] [LieAlgebra ℝ L]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    [Fintype I] [DecidableEq I]
    (X : I → L) (S : Finset (FreeMagma I)) (β : WordBasisSelections X S)
    (h : L →ₗ[ℝ] W) (hh : ∀ x y : L, h ⁅x, y⁆ = 0)
    (scale : ℕ → ℝ) (hscale : Tendsto scale atTop atTop) (hs0 : ∀ n, 0 < scale n)
    (pivot : L) (V : Set W) (hV : IsOpen V) (hp : h pivot ∈ V) :
    let b := WordBasisSelections.basis X S β
    let cost := fun j => bracketWordExponent (fun _ : I => 1) (β.val j)
    let br := fun n => exponentialRescaleBasis b cost (Real.log (scale n))
    ∃ Q : Set (Fin (finrank ℝ L) → ℝ), IsCompact Q ∧
      Q ⊆ {z | h (b.equivFun.symm z) ∈ V} ∧
      (∀ᶠ n in atTop, (br n).equivFun (scale n • pivot) ∈ Q) ∧
      ∀ n, h (b.equivFun.symm ((br n).equivFun (scale n • pivot))) = h pivot := by
  dsimp only
  let b := WordBasisSelections.basis X S β
  let cost := fun j => bracketWordExponent (fun _ : I => 1) (β.val j)
  let br := fun n => exponentialRescaleBasis b cost (Real.log (scale n))
  let q : (Fin (finrank ℝ L) → ℝ) →ₗ[ℝ] W := h.comp b.equivFun.symm.toLinearMap
  let U := {z | q z ∈ V}
  have hU : IsOpen U := hV.preimage q.continuous_of_finiteDimensional
  have hcost (j) (_ : b.repr pivot j ≠ 0) : (1 : ℝ) ≤ cost j := by
    have hlen (w : FreeMagma I) : 1 ≤ bracketWordLength w := by
      induction w using FreeMagma.rec with
      | of i => simp [bracketWordLength]
      | mul u w hu hw => simp only [bracketWordLength]; omega
    dsimp only [cost]
    rw [bracketWordExponent_one]
    exact_mod_cast hlen (β.val j)
  have hlim : Tendsto (fun n => (br n).equivFun (scale n • pivot)) atTop
      (𝓝 (gradedGenerator b cost 1 pivot)) := by
    have hraw := (rescaled_generator_tendsto b cost 1 pivot hcost).comp
      (Real.tendsto_log_atTop.comp hscale)
    simpa only [Function.comp_def, mul_one, Real.exp_log (hs0 _)] using hraw
  have hinside : gradedGenerator b cost 1 pivot ∈ U := by
    change h (b.equivFun.symm (gradedGenerator b cost 1 pivot)) ∈ V
    rw [gradedGenerator_word_height X S β h hh]
    exact hp
  obtain ⟨Q, hQ, hQi, hQU⟩ := exists_compact_subset hU hinside
  refine ⟨Q, hQ, hQU, hlim.eventually (mem_interior_iff_mem_nhds.mp hQi), ?_⟩
  intro n
  exact word_length_chart_pivot_height X S β h hh (hs0 n) pivot

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_CoarsePathConcatenation
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Coarse metric bounds under path concatenation

The additive error is retained explicitly. This allows logarithmic-diameter
switches and coarse-speed one-parameter legs to use a fixed finite mesh.
-/

namespace PolycyclicRecognition

open scoped unitInterval

variable {X : Type} [PseudoMetricSpace X] {x y z : X}

theorem PathMetricBound.mono {p : Path x y} {L κ L' κ' : ℝ}
    (h : PathMetricBound p L κ) (hL : L ≤ L') (hκ : κ ≤ κ') :
    PathMetricBound p L' κ' := by
  intro s t
  exact (h s t).trans (add_le_add (mul_le_mul_of_nonneg_right hL (abs_nonneg _)) hκ)

theorem PathMetricBound.cast {p : Path x y} {L κ : ℝ} (h : PathMetricBound p L κ)
    {x' y' : X} (hx : x' = x) (hy : y' = y) : PathMetricBound (p.cast hx hy) L κ := h

end PolycyclicRecognition

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_BasedImagePaths
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Image paths centered at their actual common starting point -/

noncomputable section

namespace PolycyclicRecognition

open scoped NNReal

variable {G W : Type} [Group G] [MetricSpace G]
  [IsTopologicalGroup G] [IsIsometricSMul G G]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

omit [IsTopologicalGroup G] in
theorem basedImage_dist (F : G → G) (a g h : G) :
    dist (basedImage F a g) (basedImage F a h) = dist (F g) (F h) :=
  dist_mul_left _ _ _

omit [IsTopologicalGroup G] [IsIsometricSMul G G] [MetricSpace G] [NormedSpace ℝ W] in
theorem basedImage_height (π : G →* Multiplicative W) (F : G → G) (a g : G) :
    (π (basedImage F a g)).toAdd = (π (F g)).toAdd - (π (F a)).toAdd := by
  simp only [basedImage, map_mul, map_inv, toAdd_mul, toAdd_inv]
  abel

/-- Centering the image gives a path based at the identity, preserves all
relative heights, and multiplies both coarse metric constants by the same
Lipschitz constant. -/
theorem basedImage_map_path (F : G → G) {K : ℝ≥0} (hF : LipschitzWith K F)
    {a g : G} (γ : Path a g) {L κ : ℝ} (hγ : PathMetricBound γ L κ) :
    ∃ η : Path (1 : G) (basedImage F a g),
      (∀ t, η t = basedImage F a (γ t)) ∧ PathMetricBound η (K * L) (K * κ) := by
  have hc : Continuous (basedImage F a) := continuous_const.mul hF.continuous
  let η : Path (1 : G) (basedImage F a g) := (γ.map hc).cast (by simp [basedImage]) rfl
  refine ⟨η, (fun _ => rfl), ?_⟩
  intro s t
  change dist (basedImage F a (γ s)) (basedImage F a (γ t)) ≤ _
  rw [basedImage_dist]
  calc
    _ ≤ (K : ℝ) * dist (γ s) (γ t) := hF.dist_le_mul _ _
    _ ≤ (K : ℝ) * (L * |(s : ℝ) - t| + κ) :=
      mul_le_mul_of_nonneg_left (hγ s t) K.coe_nonneg
    _ = _ := by ring

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_SupportStrictInterior
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finite_templateSymmetryGroup _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteRootOffsetConeIndex _root_.OAI.PolycyclicRecognition.instFiniteSubtypeLinearEquivRealIdMemSubgroupLinearSupportSymmetryGroup _root_.OAI.PolycyclicRecognition.instNonemptyRootOffsetConeIndex _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.CartanWordModel.supportDatum_weight _root_.OAI.PolycyclicRecognition.SupportDatum.transport_weight_apply _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Strict switching heights beyond a compact probe template -/

noncomputable section
namespace PolycyclicRecognition.SupportDatum

open Set Filter Metric
open scoped Topology

variable {W I B : Type} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [FiniteDimensional ℝ W] [Fintype I] [Fintype B]
  (D : PolycyclicRecognition.SupportDatum W I B)

theorem exists_weightSupport_lt_on_open
    {E U : Set W} (hE : IsCompact E) (hne : E.Nonempty)
    (hU : IsOpen U) (hEU : E ⊆ U) (i : I) (hnz : D.weight i ≠ 0) :
    ∃ w ∈ U, D.weightSupport E i < D.weight i w := by
  obtain ⟨x, hx, hsup⟩ := D.exists_weightSupport_point hE hne i
  have hex : ∃ v : W, D.weight i v ≠ 0 := by
    by_contra! h
    apply hnz
    ext v
    exact h v
  obtain ⟨v, hv⟩ := hex
  let u := (D.weight i v)⁻¹ • v
  have hu : D.weight i u = 1 := by simp [u, hv]
  have hc : Continuous (fun a : ℝ => x + a • u) :=
    continuous_const.add (continuous_id.smul continuous_const)
  have ht : Tendsto (fun a : ℝ => x + a • u) (𝓝 0) (𝓝 x) := by
    simpa only [zero_smul, add_zero] using hc.tendsto 0
  have he : ∀ᶠ a : ℝ in 𝓝 0, x + a • u ∈ U := ht (hU.mem_nhds (hEU hx))
  obtain ⟨ε, hε, he⟩ := Metric.eventually_nhds_iff.mp he
  have hin : x + (ε / 2) • u ∈ U := he (by
    rw [Real.dist_eq, sub_zero, abs_of_pos (half_pos hε)]
    exact half_lt_self hε)
  refine ⟨_, hin, ?_⟩
  rw [hsup, map_add, map_smul, hu, smul_eq_mul, mul_one]
  linarith

end PolycyclicRecognition.SupportDatum

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanLinkedProbeChains
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instDecidableEqConeMixedWords _root_.OAI.PolycyclicRecognition.CartanWordModel.instFintypeConeMixedWords _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Consecutive actual chains with one vanishing prefix bound -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule Filter
open scoped Manifold Topology

variable {EG G W : Type} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H) [Nonempty (Fin M.letterCount)]
  {Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H Exp)
  (hunimod : ∀ x : GroupLieAlgebra (𝓘(ℝ, EG)) G,
    LinearMap.trace ℝ _ (ad ℝ _ x) = 0)
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)

set_option maxHeartbeats 1000000 in
omit [SimplyConnectedSpace G] [FiniteDimensional ℝ W] [Nonempty (Fin M.letterCount)] in
/-- Each linked chain is the original chain left-translated by its actual
initial vertex; this identity keeps the common profile centering unchanged. -/
theorem LinkedProbeChains.exp_eq_start_mul
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (E : Fin 3 → Set W) (γ : M.Bases) (t : Fin M.letterCount → ℝ) (scale : ℕ → ℝ)
    {Y : ℕ → Type} [∀ n, MeasurableSpace (Y n)]
    (probe : Fin 3 → ∀ n, Y n → F.N.carrier)
    (P : ∀ k, M.BoxProbeChains T F hunimod eW b₀ (E k) γ t scale (probe k))
    (origin base : ∀ n, Y n → cartanRootIdeal H) (ε : ℕ → ℝ)
    (Q : M.LinkedProbeChains T F hunimod eW b₀ E γ t scale probe P origin base ε)
    (k : Fin 3) (n : ℕ) (y : Y n) (j : Fin ((P k).length + 1)) :
    F.ExpN (F.N.equiv (Q.vertex k n y j)) =
      F.ExpN (F.N.equiv (Q.vertex k n y 0)) *
        F.ExpN (F.N.equiv ((P k).vertex n y j)) := by
  fin_cases k
  · change F.ExpN (F.N.equiv (Q.vertex 0 n y j)) =
      F.ExpN (F.N.equiv (Q.vertex 0 n y 0)) * F.ExpN (F.N.equiv ((P 0).vertex n y j))
    rw [Q.first_exp, Q.first_start]
  · change F.ExpN (F.N.equiv (Q.vertex 1 n y j)) =
      F.ExpN (F.N.equiv (Q.vertex 1 n y 0)) * F.ExpN (F.N.equiv ((P 1).vertex n y j))
    rw [Q.second_exp, Q.second_start]
  · change F.ExpN (F.N.equiv (Q.vertex 2 n y j)) =
      F.ExpN (F.N.equiv (Q.vertex 2 n y 0)) * F.ExpN (F.N.equiv ((P 2).vertex n y j))
    rw [Q.third_exp, Q.third_start]

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanMappedTemplatePaths
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instDecidableEqConeMixedWords _root_.OAI.PolycyclicRecognition.CartanWordModel.instFintypeConeMixedWords _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual image paths from the selected affine profiles -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule Set Filter
open scoped Manifold Topology NNReal

variable {EG G W I : Type} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G] [IsIsometricSMul G G]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] [Fintype I] [DecidableEq I]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H) [Nonempty (Fin M.letterCount)]
  {Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H Exp)
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)

set_option maxHeartbeats 1000000 in
/-- Good profiles on all selected prefixes give paths in the actual target
space, centered at the image of the starting point. Their height region is
the affine image of the translated template, with the offset cancelled. -/
theorem exists_mapped_template_profile_paths
    (hExp : IsGroupExponential Exp)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (haarD : NilpotentExponentialHaarInput F.D.modelSpace F.D.carrier)
    (dynkinD : NilpotentDynkinExpansionInput F.D.modelSpace F.D.carrier)
    (π : G →* Multiplicative W)
    (hπ : ∀ x, (π (Exp x)).toAdd = eW (heightProjection T.character x))
    {K : ℝ≥0} (hLip : LipschitzWith K (fun g : G => (π g).toAdd))
    (X : I → H) {d : ℕ} (hDnil : lowerCentralSeries ℝ H H d = ⊥)
    (bD₀ : Basis (Fin (finrank ℝ H)) ℝ H)
    (βD : WordBasisSelections X (boundedBracketWords d))
    (hβD : IsMaximizingColumnBasis (wordListCoordinates X (boundedBracketWords d) bD₀)
      (fun w => bracketWordExponent (fun _ : I => 1) w) βD.val)
    (scale : ℕ → ℝ) (hscale : Tendsto scale atTop atTop) (hscale0 : ∀ n, 0 < scale n)
    (hunimod : ∀ x : GroupLieAlgebra (𝓘(ℝ, EG)) G,
      LinearMap.trace ℝ _ (ad ℝ _ x) = 0)
    (pivot : H) (E V : Set W) (hEc : IsCompact E) (hE : Convex ℝ E)
    (hpivot : eW (heightProjection T.character pivot) ∈ E)
    (hV : IsOpen V) (hVconv : Convex ℝ V) (hEV : E ⊆ V)
    {B : ℝ} (hB : 0 ≤ B) :
    let b := WordBasisSelections.basis X (boundedBracketWords d) βD
    let cost := fun j => bracketWordExponent (fun _ : I => 1) (βD.val j)
    let br := fun n => exponentialRescaleBasis b cost (Real.log (scale n))
    let h : H →ₗ[ℝ] W := eW.toLinearMap.comp
      ((heightProjection T.character).comp H.incl.toLinearMap)
    ∃ (Q : Set (Fin (finrank ℝ H) → ℝ)) (C : ℝ),
      IsCompact Q ∧ Q ⊆ {z | h (b.equivFun.symm z) ∈ V} ∧ 0 ≤ C ∧
      ∀ᶠ n in atTop, ∀ (N : ℕ) (x : G) (vertex : Fin (N + 1) → G)
        (mode : Fin N → Fin M.letterCount) (coeff : Fin N → ℝ),
        (∀ j, vertex j.succ = vertex j.castSucc *
          Exp (coeff j • (M.letter (mode j) : GroupLieAlgebra (𝓘(ℝ, EG)) G))) →
        (∀ j, |coeff j| ≤ B * Real.exp (scale n *
          (M.supportIn T hunimod eW).weightSupport E (mode j))) →
        ∀ (f : G → G) (Λ : ℝ≥0), LipschitzWith Λ f →
        ∀ (A : W →ₗ[ℝ] W) (offset : W) (ε : ℝ),
        (∀ i z, z ∈ Q →
          ‖rescaledMapProfile (fun g => (π (f g)).toAdd) x (vertex i)
              (Real.log (scale n)) (fun z => Exp ((br n).equivFun.symm z)) z -
            (A (h (b.equivFun.symm z)) + offset)‖ ≤ ε) →
        let start := x * vertex 0 * Exp (scale n • (pivot : GroupLieAlgebra (𝓘(ℝ, EG)) G))
        let finish := x * vertex (Fin.last N) * Exp (scale n • (pivot : GroupLieAlgebra (𝓘(ℝ, EG)) G))
        ∃ path : Path (1 : G) (basedImage f start finish),
          PathMetricBound path ((Λ * (C * scale n)) * 2 ^ N)
            ((Λ * (C * (1 + Real.log (2 + scale n)))) * 2 ^ N) ∧
          ∀ t, ∃ z ∈ (fun w => A (w - h pivot)) '' E,
            ‖(π (path t)).toAdd - scale n • z‖ ≤
              2 * scale n * ε + (K * Λ) * (C * Real.log (2 + scale n)) := by
  let : IsTopologicalGroup G := topologicalGroup_of_lieGroup (𝓘(ℝ, EG)) ⊤
  dsimp only
  obtain ⟨Q, C, hQ, hQV, hC, hpaths⟩ := M.exists_compact_template_profile_paths T F eW
    hExp realize haarD dynkinD π hπ X hDnil bD₀ βD hβD scale hscale hscale0
    hunimod pivot E V hEc hE hpivot hV hVconv hEV hB
  refine ⟨Q, C, hQ, hQV, hC, ?_⟩
  filter_upwards [hpaths] with n hn
  intro N x vertex mode coeff hstep hamp f Λ hf A offset ε hgood
  obtain ⟨path, hmetric, hheight⟩ := hn N x vertex mode coeff hstep hamp
    (fun g => (π (f g)).toAdd) (K * Λ) (hLip.comp hf) A offset ε hgood
  obtain ⟨mapped, hmapped, hbound⟩ := basedImage_map_path f hf path hmetric
  refine ⟨mapped, ?_, ?_⟩
  · convert hbound using 1 <;> first | (with_reducible_and_instances rfl) | ring
  · intro t
    obtain ⟨w, hw, hh⟩ := hheight t
    refine ⟨A (w - _), ⟨w, hw, rfl⟩, ?_⟩
    rw [hmapped, basedImage_height]
    exact hh

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanUniformImagePaths
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instDecidableEqConeMixedWords _root_.OAI.PolycyclicRecognition.CartanWordModel.instFintypeConeMixedWords _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.CartanFactorModel.heightRay_zero _root_.OAI.PolycyclicRecognition.CartanFactorModel.realScaleProfile_apply _root_.OAI.PolycyclicRecognition.CartanFactorModel.sampledProbeProfile_apply _root_.OAI.PolycyclicRecognition.bracketWordDifferential_mul _root_.OAI.PolycyclicRecognition.cartanWeightDerivation_apply_root _root_.OAI.PolycyclicRecognition.chartExponentialFlow_zero _root_.OAI.PolycyclicRecognition.derivationSemidirectHom_apply _root_.OAI.PolycyclicRecognition.exponentialHomOfDynkin_apply_exp _root_.OAI.PolycyclicRecognition.exponentialRescaleBasis_zero _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.modelNilradicalLinearAction_apply _root_.OAI.PolycyclicRecognition.modelNilradicalRotation_apply _root_.OAI.PolycyclicRecognition.modelNilradicalRotation_mul _root_.OAI.PolycyclicRecognition.modelNilradicalRotation_one _root_.OAI.PolycyclicRecognition.nilshadowWeightDerivation_symm _root_.OAI.PolycyclicRecognition.nilshadowWeightOperator_symm _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform constants for the selected bounded-length paths -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule Set Filter
open scoped Manifold Topology NNReal

variable {EG G W I : Type} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G] [IsIsometricSMul G G]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] [Fintype I] [DecidableEq I]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H) [Nonempty (Fin M.letterCount)]
  {Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H Exp)
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)

set_option maxHeartbeats 1000000 in
/-- One pair of path constants works for every chain of bounded length.
It controls both coarse metric bounds and the logarithmic height error. -/
theorem exists_bounded_mapped_template_profile_paths
    (hExp : IsGroupExponential Exp)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (haarD : NilpotentExponentialHaarInput F.D.modelSpace F.D.carrier)
    (dynkinD : NilpotentDynkinExpansionInput F.D.modelSpace F.D.carrier)
    (π : G →* Multiplicative W)
    (hπ : ∀ x, (π (Exp x)).toAdd = eW (heightProjection T.character x))
    {K : ℝ≥0} (hLip : LipschitzWith K (fun g : G => (π g).toAdd))
    (X : I → H) {d : ℕ} (hDnil : lowerCentralSeries ℝ H H d = ⊥)
    (bD₀ : Basis (Fin (finrank ℝ H)) ℝ H)
    (βD : WordBasisSelections X (boundedBracketWords d))
    (hβD : IsMaximizingColumnBasis (wordListCoordinates X (boundedBracketWords d) bD₀)
      (fun w => bracketWordExponent (fun _ : I => 1) w) βD.val)
    (scale : ℕ → ℝ) (hscale : Tendsto scale atTop atTop) (hscale0 : ∀ n, 0 < scale n)
    (hunimod : ∀ x : GroupLieAlgebra (𝓘(ℝ, EG)) G,
      LinearMap.trace ℝ _ (ad ℝ _ x) = 0)
    (pivot : H) (E V : Set W) (hEc : IsCompact E) (hE : Convex ℝ E)
    (hpivot : eW (heightProjection T.character pivot) ∈ E)
    (hV : IsOpen V) (hVconv : Convex ℝ V) (hEV : E ⊆ V)
    {B : ℝ} (hB : 0 ≤ B) (N₀ : ℕ) (Λ : ℝ≥0) :
    let b := WordBasisSelections.basis X (boundedBracketWords d) βD
    let cost := fun j => bracketWordExponent (fun _ : I => 1) (βD.val j)
    let br := fun n => exponentialRescaleBasis b cost (Real.log (scale n))
    let h : H →ₗ[ℝ] W := eW.toLinearMap.comp
      ((heightProjection T.character).comp H.incl.toLinearMap)
    ∃ (Q : Set (Fin (finrank ℝ H) → ℝ)) (C : ℝ),
      IsCompact Q ∧ Q ⊆ {z | h (b.equivFun.symm z) ∈ V} ∧ 0 ≤ C ∧
      ∀ᶠ n in atTop, ∀ (N : ℕ), N ≤ N₀ → ∀ (x : G) (vertex : Fin (N + 1) → G)
        (mode : Fin N → Fin M.letterCount) (coeff : Fin N → ℝ),
        (∀ j, vertex j.succ = vertex j.castSucc *
          Exp (coeff j • (M.letter (mode j) : GroupLieAlgebra (𝓘(ℝ, EG)) G))) →
        (∀ j, |coeff j| ≤ B * Real.exp (scale n *
          (M.supportIn T hunimod eW).weightSupport E (mode j))) →
        ∀ (f : G → G), LipschitzWith Λ f →
        ∀ (A : W →ₗ[ℝ] W) (offset : W) (ε : ℝ),
        (∀ i z, z ∈ Q →
          ‖rescaledMapProfile (fun g => (π (f g)).toAdd) x (vertex i)
              (Real.log (scale n)) (fun z => Exp ((br n).equivFun.symm z)) z -
            (A (h (b.equivFun.symm z)) + offset)‖ ≤ ε) →
        let start := x * vertex 0 * Exp (scale n • (pivot : GroupLieAlgebra (𝓘(ℝ, EG)) G))
        let finish := x * vertex (Fin.last N) * Exp (scale n • (pivot : GroupLieAlgebra (𝓘(ℝ, EG)) G))
        ∃ path : Path (1 : G) (basedImage f start finish),
          PathMetricBound path (C * scale n)
            (C * (1 + Real.log (2 + scale n))) ∧
          ∀ t, ∃ z ∈ (fun w => A (w - h pivot)) '' E,
            ‖(π (path t)).toAdd - scale n • z‖ ≤
              2 * scale n * ε + C * (1 + Real.log (2 + scale n)) := by
  dsimp only
  obtain ⟨Q, C, hQ, hQV, hC, hpaths⟩ := M.exists_mapped_template_profile_paths T F eW
    hExp realize haarD dynkinD π hπ hLip X hDnil bD₀ βD hβD scale hscale hscale0
    hunimod pivot E V hEc hE hpivot hV hVconv hEV hB
  let L := max ((Λ : ℝ) * C * 2 ^ N₀) ((K : ℝ) * Λ * C)
  have hL : 0 ≤ L := (by positivity : 0 ≤ (Λ : ℝ) * C * 2 ^ N₀).trans
    (le_max_left _ _)
  refine ⟨Q, L, hQ, hQV, hL, ?_⟩
  filter_upwards [hpaths] with n hn
  intro N hN x vertex mode coeff hstep hamp f hf A offset ε hgood
  obtain ⟨path, hm, hh⟩ := hn N x vertex mode coeff hstep hamp f Λ hf A offset ε hgood
  have hpow : (2 : ℝ) ^ N ≤ 2 ^ N₀ := pow_le_pow_right₀ (by norm_num) hN
  have hcoef : (Λ : ℝ) * C * 2 ^ N ≤ L :=
    (mul_le_mul_of_nonneg_left hpow (mul_nonneg Λ.coe_nonneg hC)).trans
      (le_max_left _ _)
  have hlog : 0 ≤ Real.log (2 + scale n) := Real.log_nonneg (by linarith [hscale0 n])
  have hsum : 0 ≤ 1 + Real.log (2 + scale n) := by linarith
  refine ⟨path, hm.mono ?_ ?_, ?_⟩
  · calc
      _ = ((Λ : ℝ) * C * 2 ^ N) * scale n := by ring
      _ ≤ L * scale n := mul_le_mul_of_nonneg_right hcoef (hscale0 n).le
  · calc
      _ = ((Λ : ℝ) * C * 2 ^ N) * (1 + Real.log (2 + scale n)) := by ring
      _ ≤ L * (1 + Real.log (2 + scale n)) := mul_le_mul_of_nonneg_right hcoef hsum
  · intro t
    obtain ⟨z, hz, he⟩ := hh t
    refine ⟨z, hz, he.trans (add_le_add le_rfl ?_)⟩
    calc
      _ = ((K : ℝ) * Λ * C) * Real.log (2 + scale n) := by ring
      _ ≤ L * Real.log (2 + scale n) :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) hlog
      _ ≤ L * (1 + Real.log (2 + scale n)) := by nlinarith

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanThreeTemplatePaths
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instDecidableEqConeMixedWords _root_.OAI.PolycyclicRecognition.CartanWordModel.instFintypeConeMixedWords _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # One compact profile domain for the three probe chains -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule Set Filter
open scoped Manifold Topology NNReal

variable {EG G W I : Type} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G] [IsIsometricSMul G G]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] [Fintype I] [DecidableEq I]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H) [Nonempty (Fin M.letterCount)]
  {Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H Exp)
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)

set_option maxHeartbeats 1000000 in
/-- The first, anchor and within-tile chains share one compact set of
profile coordinates and one pair of metric and height constants. -/
theorem exists_three_template_profile_paths
    (hExp : IsGroupExponential Exp)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (haarD : NilpotentExponentialHaarInput F.D.modelSpace F.D.carrier)
    (dynkinD : NilpotentDynkinExpansionInput F.D.modelSpace F.D.carrier)
    (π : G →* Multiplicative W)
    (hπ : ∀ x, (π (Exp x)).toAdd = eW (heightProjection T.character x))
    {K : ℝ≥0} (hLip : LipschitzWith K (fun g : G => (π g).toAdd))
    (X : I → H) {d : ℕ} (hDnil : lowerCentralSeries ℝ H H d = ⊥)
    (bD₀ : Basis (Fin (finrank ℝ H)) ℝ H)
    (βD : WordBasisSelections X (boundedBracketWords d))
    (hβD : IsMaximizingColumnBasis (wordListCoordinates X (boundedBracketWords d) bD₀)
      (fun w => bracketWordExponent (fun _ : I => 1) w) βD.val)
    (scale : ℕ → ℝ) (hscale : Tendsto scale atTop atTop) (hscale0 : ∀ n, 0 < scale n)
    (hunimod : ∀ x : GroupLieAlgebra (𝓘(ℝ, EG)) G,
      LinearMap.trace ℝ _ (ad ℝ _ x) = 0)
    (pivot : H) (E : Fin 3 → Set W) (V : Set W) (hEc : ∀ k, IsCompact (E k))
    (hE : ∀ k, Convex ℝ (E k))
    (hpivot : ∀ k, eW (heightProjection T.character pivot) ∈ E k)
    (hV : IsOpen V) (hVconv : Convex ℝ V) (hEV : ∀ k, E k ⊆ V)
    {B : ℝ} (hB : 0 ≤ B) (N₀ : ℕ) (Λ : ℝ≥0) :
    let b := WordBasisSelections.basis X (boundedBracketWords d) βD
    let cost := fun j => bracketWordExponent (fun _ : I => 1) (βD.val j)
    let br := fun n => exponentialRescaleBasis b cost (Real.log (scale n))
    let h : H →ₗ[ℝ] W := eW.toLinearMap.comp
      ((heightProjection T.character).comp H.incl.toLinearMap)
    ∃ (Q : Set (Fin (finrank ℝ H) → ℝ)) (C : ℝ),
      IsCompact Q ∧ Q ⊆ {z | h (b.equivFun.symm z) ∈ V} ∧ 0 ≤ C ∧
      ∀ᶠ n in atTop, ∀ (k : Fin 3) (N : ℕ), N ≤ N₀ → ∀ (x : G) (vertex : Fin (N + 1) → G)
        (mode : Fin N → Fin M.letterCount) (coeff : Fin N → ℝ),
        (∀ j, vertex j.succ = vertex j.castSucc *
          Exp (coeff j • (M.letter (mode j) : GroupLieAlgebra (𝓘(ℝ, EG)) G))) →
        (∀ j, |coeff j| ≤ B * Real.exp (scale n *
          (M.supportIn T hunimod eW).weightSupport (E k) (mode j))) →
        ∀ (f : G → G), LipschitzWith Λ f →
        ∀ (A : W →ₗ[ℝ] W) (offset : W) (ε : ℝ),
        (∀ i z, z ∈ Q →
          ‖rescaledMapProfile (fun g => (π (f g)).toAdd) x (vertex i)
              (Real.log (scale n)) (fun z => Exp ((br n).equivFun.symm z)) z -
            (A (h (b.equivFun.symm z)) + offset)‖ ≤ ε) →
        let start := x * vertex 0 * Exp (scale n • (pivot : GroupLieAlgebra (𝓘(ℝ, EG)) G))
        let finish := x * vertex (Fin.last N) * Exp (scale n • (pivot : GroupLieAlgebra (𝓘(ℝ, EG)) G))
        ∃ path : Path (1 : G) (basedImage f start finish),
          PathMetricBound path (C * scale n)
            (C * (1 + Real.log (2 + scale n))) ∧
          ∀ t, ∃ z ∈ (fun w => A (w - h pivot)) '' E k,
            ‖(π (path t)).toAdd - scale n • z‖ ≤
              2 * scale n * ε + C * (1 + Real.log (2 + scale n)) := by
  classical
  dsimp only
  have hall := fun k : Fin 3 => M.exists_bounded_mapped_template_profile_paths T F eW
    hExp realize haarD dynkinD π hπ hLip X hDnil bD₀ βD hβD scale hscale hscale0
    hunimod pivot (E k) V (hEc k) (hE k) (hpivot k) hV hVconv (hEV k) hB N₀ Λ
  dsimp only at hall
  choose Q L hQ hQV hL hpaths using hall
  let Qall := ⋃ k : Fin 3, Q k
  let Lall := ∑ k : Fin 3, L k
  have hLall : 0 ≤ Lall := Finset.sum_nonneg (fun k _ => hL k)
  have hLle (k : Fin 3) : L k ≤ Lall :=
    Finset.single_le_sum (fun j _ => hL j) (Finset.mem_univ k)
  have hev := (Filter.eventually_all).mpr hpaths
  refine ⟨Qall, Lall, isCompact_iUnion hQ, ?_, hLall, ?_⟩
  · intro z hz
    obtain ⟨k, hk⟩ := mem_iUnion.mp hz
    exact hQV k hk
  · filter_upwards [hev] with n hn
    intro k N hN x vertex mode coeff hstep hamp f hf A offset ε hgood
    obtain ⟨path, hm, hh⟩ := hn k N hN x vertex mode coeff hstep hamp f hf A offset ε
      (fun i z hz => hgood i z (mem_iUnion.mpr ⟨k, hz⟩))
    have hlog : 0 ≤ 1 + Real.log (2 + scale n) := by
      have := Real.log_nonneg (show 1 ≤ 2 + scale n by linarith [hscale0 n])
      linarith
    refine ⟨path, hm.mono (mul_le_mul_of_nonneg_right (hLle k) (hscale0 n).le)
      (mul_le_mul_of_nonneg_right (hLle k) hlog), ?_⟩
    intro t
    obtain ⟨z, hz, he⟩ := hh t
    exact ⟨z, hz, he.trans (add_le_add le_rfl
      (mul_le_mul_of_nonneg_right (hLle k) hlog))⟩

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanSelectedProbePaths
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instDecidableEqConeMixedWords _root_.OAI.PolycyclicRecognition.CartanWordModel.instFintypeConeMixedWords _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Image paths for the selected actual probe chains -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule Set Filter
open scoped Manifold Topology NNReal

variable {EG G W I : Type} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G] [IsIsometricSMul G G]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] [Fintype I] [DecidableEq I]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H) [Nonempty (Fin M.letterCount)]
  {Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H Exp)
  (hunimod : ∀ x : GroupLieAlgebra (𝓘(ℝ, EG)) G,
    LinearMap.trace ℝ _ (ad ℝ _ x) = 0)
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)

omit [SimplyConnectedSpace G] [IsIsometricSMul G G] [Fintype I] [DecidableEq I]
    [FiniteDimensional ℝ W] [Nonempty (Fin M.letterCount)] in
set_option maxHeartbeats 1000000 in
/-- Inclusion into the ambient group retains the exact generator edge of
the measured box chain, also after left translation by an anchor. -/
theorem BoxProbeChains.ambient_step
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (E : Set W) (γ : M.Bases) (t : Fin M.letterCount → ℝ) (scale : ℕ → ℝ)
    {Y : ℕ → Type} [∀ n, MeasurableSpace (Y n)]
    (probe : ∀ n, Y n → F.N.carrier)
    (P : M.BoxProbeChains T F hunimod eW b₀ E γ t scale probe)
    (n : ℕ) (y : Y n) (g : G) (j : Fin P.length) :
    g * F.inclusionN (F.ExpN (F.N.equiv (P.vertex n y j.succ))) =
      (g * F.inclusionN (F.ExpN (F.N.equiv (P.vertex n y j.castSucc)))) *
        Exp (P.coefficient n y j • (M.letter (P.mode n j) :
          GroupLieAlgebra (𝓘(ℝ, EG)) G)) := by
  have h := congrArg F.inclusionN (P.vertex_step n y j)
  rw [map_mul, F.compatibleN (P.coefficient n y j • M.letter (P.mode n j))] at h
  exact (congrArg (g * ·) h).trans (mul_assoc _ _ _).symm

set_option maxHeartbeats 1000000 in
/-- One compact profile domain works for all three actual box chains and
for arbitrary measurable anchor choices. On a retained good probe, the
paths start at the corresponding anchors and end at the actual samplers.
The only profile premise is the prefix estimate supplied by selection. -/
theorem exists_selected_probe_paths
    (hExp : IsGroupExponential Exp)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (haarD : NilpotentExponentialHaarInput F.D.modelSpace F.D.carrier)
    (dynkinD : NilpotentDynkinExpansionInput F.D.modelSpace F.D.carrier)
    (π : G →* Multiplicative W)
    (hπ : ∀ x, (π (Exp x)).toAdd = eW (heightProjection T.character x))
    {K : ℝ≥0} (hLip : LipschitzWith K (fun g : G => (π g).toAdd))
    (X : I → H) {d : ℕ} (hDnil : lowerCentralSeries ℝ H H d = ⊥)
    (bD₀ : Basis (Fin (finrank ℝ H)) ℝ H)
    (βD : WordBasisSelections X (boundedBracketWords d))
    (hβD : IsMaximizingColumnBasis (wordListCoordinates X (boundedBracketWords d) bD₀)
      (fun w => bracketWordExponent (fun _ : I => 1) w) βD.val)
    (scale : ℕ → ℝ) (hscale : Tendsto scale atTop atTop) (hscale0 : ∀ n, 0 < scale n)
    (pivot : H) (E : Fin 3 → Set W) (V : Set W) (hEc : ∀ k, IsCompact (E k))
    (hE : ∀ k, Convex ℝ (E k))
    (hpivot : ∀ k, eW (heightProjection T.character pivot) ∈ E k)
    (hV : IsOpen V) (hVconv : Convex ℝ V) (hEV : ∀ k, E k ⊆ V)
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (γ : M.Bases) (t : Fin M.letterCount → ℝ)
    {Y : ℕ → Type} [∀ n, MeasurableSpace (Y n)]
    (probe : Fin 3 → ∀ n, Y n → F.N.carrier)
    (P : ∀ k, M.BoxProbeChains T F hunimod eW b₀ (E k) γ t scale (probe k))
    (Λ : ℝ≥0) :
    let b := WordBasisSelections.basis X (boundedBracketWords d) βD
    let cost := fun j => bracketWordExponent (fun _ : I => 1) (βD.val j)
    let br := fun n => exponentialRescaleBasis b cost (Real.log (scale n))
    let h : H →ₗ[ℝ] W := eW.toLinearMap.comp
      ((heightProjection T.character).comp H.incl.toLinearMap)
    ∃ (Q : Set (Fin (finrank ℝ H) → ℝ)) (C : ℝ),
      IsCompact Q ∧ Q ⊆ {z | h (b.equivFun.symm z) ∈ V} ∧ 0 ≤ C ∧
      ∀ᶠ n in atTop, ∀ (k : Fin 3) (y : Y n) (x anchor : G)
        (f : G → G), LipschitzWith Λ f →
        ∀ (A : W →ₗ[ℝ] W) (offset : W) (ε : ℝ),
        (∀ j z, z ∈ Q →
          ‖rescaledMapProfile (fun g => (π (f g)).toAdd) x
              (anchor * F.inclusionN (F.ExpN (F.N.equiv ((P k).vertex n y j))))
              (Real.log (scale n)) (fun z => Exp ((br n).equivFun.symm z)) z -
            (A (h (b.equivFun.symm z)) + offset)‖ ≤ ε) →
        ∃ path : Path (1 : G) (basedImage f
            (x * anchor * Exp (scale n • (pivot : GroupLieAlgebra (𝓘(ℝ, EG)) G)))
            (x * (anchor * F.inclusionN (probe k n y)) *
              Exp (scale n • (pivot : GroupLieAlgebra (𝓘(ℝ, EG)) G)))),
          PathMetricBound path (C * scale n) (C * (1 + Real.log (2 + scale n))) ∧
          ∀ s, ∃ z ∈ (fun w => A (w - h pivot)) '' E k,
            ‖(π (path s)).toAdd - scale n • z‖ ≤
              2 * scale n * ε + C * (1 + Real.log (2 + scale n)) := by
  classical
  dsimp only
  let B := ∑ k : Fin 3, (P k).amplitude
  let N₀ := ∑ k : Fin 3, (P k).length
  have hB : 0 ≤ B := Finset.sum_nonneg (fun k _ => le_trans zero_le_one (P k).amplitude_ge_one)
  have hBk (k : Fin 3) : (P k).amplitude ≤ B :=
    Finset.single_le_sum (fun j _ => le_trans zero_le_one (P j).amplitude_ge_one)
      (Finset.mem_univ k)
  have hNk (k : Fin 3) : (P k).length ≤ N₀ :=
    Finset.single_le_sum (f := fun k : Fin 3 => (P k).length)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)
  obtain ⟨Q, C, hQ, hQV, hC, he⟩ := M.exists_three_template_profile_paths T F eW
    hExp realize haarD dynkinD π hπ hLip X hDnil bD₀ βD hβD scale hscale hscale0
    hunimod pivot E V hEc hE hpivot hV hVconv hEV hB N₀ Λ
  refine ⟨Q, C, hQ, hQV, hC, he.mono ?_⟩
  intro n hn k y x anchor f hf A offset ε hgood
  let vertex := fun j => anchor * F.inclusionN (F.ExpN (F.N.equiv ((P k).vertex n y j)))
  have hamp (j) : |(P k).coefficient n y j| ≤ B * Real.exp (scale n *
      (M.supportIn T hunimod eW).weightSupport (E k) ((P k).mode n j)) :=
    ((P k).coefficient_bound n y j).trans
      (mul_le_mul_of_nonneg_right (hBk k) (Real.exp_pos _).le)
  have hz : vertex 0 = anchor := by
    simp only [vertex, (P k).vertex_zero, map_zero, F.isExpN.map_zero, map_one, mul_one]
  have hend : vertex (Fin.last (P k).length) = anchor * F.inclusionN (probe k n y) :=
    congrArg (fun z => anchor * F.inclusionN z) ((P k).vertex_last n y)
  have hp := hn k (P k).length (hNk k) x vertex ((P k).mode n)
    ((P k).coefficient n y) (BoxProbeChains.ambient_step T M F hunimod eW b₀ (E k) γ t scale
      (probe k) (P k) n y anchor) hamp f hf A offset ε hgood
  obtain ⟨path, hm, hh⟩ := hp
  have he : basedImage f
      (x * anchor * Exp (scale n • (pivot : GroupLieAlgebra (𝓘(ℝ, EG)) G)))
      (x * (anchor * F.inclusionN (probe k n y)) *
        Exp (scale n • (pivot : GroupLieAlgebra (𝓘(ℝ, EG)) G))) =
      basedImage f (x * vertex 0 * Exp (scale n • (pivot : GroupLieAlgebra (𝓘(ℝ, EG)) G)))
        (x * vertex (Fin.last (P k).length) *
          Exp (scale n • (pivot : GroupLieAlgebra (𝓘(ℝ, EG)) G))) := by
    rw [hz, hend]
  exact ⟨path.cast rfl he, hm.cast rfl he, hh⟩

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanLinkedProbePaths
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instDecidableEqConeMixedWords _root_.OAI.PolycyclicRecognition.CartanWordModel.instFintypeConeMixedWords _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Image paths from the actual linked profile bounds -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule Set Filter
open scoped Manifold Topology NNReal

variable {EG G W I : Type} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G] [IsIsometricSMul G G] [IsTopologicalGroup G]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] [Fintype I] [DecidableEq I]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H) [Nonempty (Fin M.letterCount)]
  {Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H Exp)
  (hunimod : ∀ x : GroupLieAlgebra (𝓘(ℝ, EG)) G,
    LinearMap.trace ℝ _ (ad ℝ _ x) = 0)
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)

/- The original sampling center is retained throughout all three paths. -/
set_option maxHeartbeats 1000000 in
theorem exists_linked_probe_paths
    (hExp : IsGroupExponential Exp)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (haarD : NilpotentExponentialHaarInput F.D.modelSpace F.D.carrier)
    (dynkinD : NilpotentDynkinExpansionInput F.D.modelSpace F.D.carrier)
    (π : G →* Multiplicative W)
    (hπ : ∀ x, (π (Exp x)).toAdd = eW (heightProjection T.character x))
    {K : ℝ≥0} (hLip : LipschitzWith K (fun g : G => (π g).toAdd))
    (X : I → H) {d : ℕ} (hDnil : lowerCentralSeries ℝ H H d = ⊥)
    (bD₀ : Basis (Fin (finrank ℝ H)) ℝ H)
    (βD : WordBasisSelections X (boundedBracketWords d))
    (hβD : IsMaximizingColumnBasis (wordListCoordinates X (boundedBracketWords d) bD₀)
      (fun w => bracketWordExponent (fun _ : I => 1) w) βD.val)
    (scale : ℕ → ℝ) (hscale : Tendsto scale atTop atTop) (hscale0 : ∀ n, 0 < scale n)
    (pivot : H) (E : Fin 3 → Set W) (V : Set W) (hEc : ∀ k, IsCompact (E k))
    (hE : ∀ k, Convex ℝ (E k))
    (hpivot : ∀ k, eW (heightProjection T.character pivot) ∈ E k)
    (hV : IsOpen V) (hVconv : Convex ℝ V) (hEV : ∀ k, E k ⊆ V)
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (γ : M.Bases) (t : Fin M.letterCount → ℝ)
    {Y : ℕ → Type} [∀ n, MeasurableSpace (Y n)]
    (probe : Fin 3 → ∀ n, Y n → F.N.carrier)
    (P : ∀ k, M.BoxProbeChains T F hunimod eW b₀ (E k) γ t scale (probe k))
    (origin base : ∀ n, Y n → cartanRootIdeal H) (η : ℕ → ℝ)
    (D : M.LinkedProbeChains T F hunimod eW b₀ E γ t scale probe P origin base η)
    (sampleBasis : ℕ → Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (hExpD : Continuous F.ExpD) (Λ : ℝ≥0) :
    let b := WordBasisSelections.basis X (boundedBracketWords d) βD
    let cost := fun j => bracketWordExponent (fun _ : I => 1) (βD.val j)
    let br := fun n => exponentialRescaleBasis b cost (Real.log (scale n))
    let h : H →ₗ[ℝ] W := eW.toLinearMap.comp
      ((heightProjection T.character).comp H.incl.toLinearMap)
    ∃ (Q : Set (Fin (finrank ℝ H) → ℝ)) (C : ℝ),
      IsCompact Q ∧ Q ⊆ {z | h (b.equivFun.symm z) ∈ V} ∧ 0 ≤ C ∧
      ∀ᶠ n in atTop, ∀ (k : Fin 3) (y : Y n) (x : G)
        (sample : Fin (finrank ℝ (cartanRootIdeal H)) → ℝ)
        (f : G → G) (hf : LipschitzWith Λ f),
        ∀ (A : W →ₗ[ℝ] W) (offset : W) (ε : ℝ),
        (∀ j z, z ∈ Q →
          ‖F.sampledProbeProfile hExpD (fun g => (π (f g)).toAdd)
              ((hLip.comp hf).continuous) x (Real.log (scale n))
              (sampleBasis n) (br n) sample (D.vertex k n y j) z -
            (A (h (b.equivFun.symm z)) + offset)‖ ≤ ε) →
        ∃ path : Path (1 : G) (basedImage f
            (x * F.sampledProbeSuffix (sampleBasis n) sample (D.vertex k n y 0) *
              Exp (scale n • (pivot : GroupLieAlgebra (𝓘(ℝ, EG)) G)))
            (x * F.sampledProbeSuffix (sampleBasis n) sample
                (D.vertex k n y (Fin.last (P k).length)) *
              Exp (scale n • (pivot : GroupLieAlgebra (𝓘(ℝ, EG)) G)))),
          PathMetricBound path (C * scale n) (C * (1 + Real.log (2 + scale n))) ∧
          ∀ s, ∃ z ∈ (fun w => A (w - h pivot)) '' E k,
            ‖(π (path s)).toAdd - scale n • z‖ ≤
              2 * scale n * ε + C * (1 + Real.log (2 + scale n)) := by
  dsimp only
  obtain ⟨Q, C, hQ, hQV, hC, he⟩ := M.exists_selected_probe_paths T F hunimod eW
    hExp realize haarD dynkinD π hπ hLip X hDnil bD₀ βD hβD scale hscale hscale0
    pivot E V hEc hE hpivot hV hVconv hEV b₀ γ t probe P Λ
  refine ⟨Q, C, hQ, hQV, hC, he.mono ?_⟩
  intro n hn k y x sample f hf A offset ε hgood
  let anchor := F.sampledProbeSuffix (sampleBasis n) sample (D.vertex k n y 0)
  have hexp (j : Fin ((P k).length + 1)) :
      anchor * F.inclusionN (F.ExpN (F.N.equiv ((P k).vertex n y j))) =
        F.sampledProbeSuffix (sampleBasis n) sample (D.vertex k n y j) := by
    have h := congrArg F.inclusionN
      (LinkedProbeChains.exp_eq_start_mul T M F hunimod eW b₀ E γ t scale probe P origin base η D k n y j)
    rw [map_mul] at h
    simp only [anchor, CartanFactorModel.sampledProbeSuffix, map_mul]
    rw [h, mul_assoc]
  have hp := hn k y x anchor f hf A offset ε (fun j z hz => ?_)
  · obtain ⟨path, hm, hh⟩ := hp
    have hend : basedImage f
        (x * F.sampledProbeSuffix (sampleBasis n) sample (D.vertex k n y 0) *
          Exp (scale n • (pivot : GroupLieAlgebra (𝓘(ℝ, EG)) G)))
        (x * F.sampledProbeSuffix (sampleBasis n) sample
            (D.vertex k n y (Fin.last (P k).length)) *
          Exp (scale n • (pivot : GroupLieAlgebra (𝓘(ℝ, EG)) G))) =
      basedImage f (x * anchor * Exp (scale n • (pivot : GroupLieAlgebra (𝓘(ℝ, EG)) G)))
        (x * (anchor * F.inclusionN (probe k n y)) *
          Exp (scale n • (pivot : GroupLieAlgebra (𝓘(ℝ, EG)) G))) := by
      have hl := hexp (Fin.last (P k).length)
      rw [(P k).vertex_last] at hl
      rw [← hl]
    exact ⟨path.cast rfl hend, hm.cast rfl hend, hh⟩
  · have hg := hgood j z hz
    rw [CartanFactorModel.sampledProbeProfile_apply] at hg
    simp only [F.compatibleD] at hg
    have hx := hexp j
    simp only [CartanFactorModel.sampledProbeSuffix, map_mul] at hx
    rw [← hx] at hg
    exact hg

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanPivotProbePaths
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instDecidableEqConeMixedWords _root_.OAI.PolycyclicRecognition.CartanWordModel.instFintypeConeMixedWords _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Image paths from the actual linked profile bounds -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule Set Filter
open scoped Manifold Topology NNReal

variable {EG G W I : Type} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G] [IsIsometricSMul G G] [IsTopologicalGroup G]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] [Fintype I] [DecidableEq I]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H) [Nonempty (Fin M.letterCount)]
  {Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H Exp)
  (hunimod : ∀ x : GroupLieAlgebra (𝓘(ℝ, EG)) G,
    LinearMap.trace ℝ _ (ad ℝ _ x) = 0)
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)

set_option maxHeartbeats 1000000 in
/-- The compact profile restriction can also contain the contact pivot.
This gives the base and terminal profile bounds on the same set used by every path. -/
theorem exists_linked_probe_paths_with_pivot
    (hExp : IsGroupExponential Exp)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (haarD : NilpotentExponentialHaarInput F.D.modelSpace F.D.carrier)
    (dynkinD : NilpotentDynkinExpansionInput F.D.modelSpace F.D.carrier)
    (π : G →* Multiplicative W)
    (hπ : ∀ x, (π (Exp x)).toAdd = eW (heightProjection T.character x))
    {K : ℝ≥0} (hLip : LipschitzWith K (fun g : G => (π g).toAdd))
    (X : I → H) {d : ℕ} (hDnil : lowerCentralSeries ℝ H H d = ⊥)
    (bD₀ : Basis (Fin (finrank ℝ H)) ℝ H)
    (βD : WordBasisSelections X (boundedBracketWords d))
    (hβD : IsMaximizingColumnBasis (wordListCoordinates X (boundedBracketWords d) bD₀)
      (fun w => bracketWordExponent (fun _ : I => 1) w) βD.val)
    (scale : ℕ → ℝ) (hscale : Tendsto scale atTop atTop) (hscale0 : ∀ n, 0 < scale n)
    (pivot : H) (E : Fin 3 → Set W) (V : Set W) (hEc : ∀ k, IsCompact (E k))
    (hE : ∀ k, Convex ℝ (E k))
    (hpivot : ∀ k, eW (heightProjection T.character pivot) ∈ E k)
    (hV : IsOpen V) (hVconv : Convex ℝ V) (hEV : ∀ k, E k ⊆ V)
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (γ : M.Bases) (t : Fin M.letterCount → ℝ)
    {Y : ℕ → Type} [∀ n, MeasurableSpace (Y n)]
    (probe : Fin 3 → ∀ n, Y n → F.N.carrier)
    (P : ∀ k, M.BoxProbeChains T F hunimod eW b₀ (E k) γ t scale (probe k))
    (origin base : ∀ n, Y n → cartanRootIdeal H) (η : ℕ → ℝ)
    (D : M.LinkedProbeChains T F hunimod eW b₀ E γ t scale probe P origin base η)
    (sampleBasis : ℕ → Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (hExpD : Continuous F.ExpD) (Λ : ℝ≥0) :
    let b := WordBasisSelections.basis X (boundedBracketWords d) βD
    let cost := fun j => bracketWordExponent (fun _ : I => 1) (βD.val j)
    let br := fun n => exponentialRescaleBasis b cost (Real.log (scale n))
    let h : H →ₗ[ℝ] W := eW.toLinearMap.comp
      ((heightProjection T.character).comp H.incl.toLinearMap)
    ∃ (Q : Set (Fin (finrank ℝ H) → ℝ)) (C : ℝ),
      IsCompact Q ∧ Q ⊆ {z | h (b.equivFun.symm z) ∈ V} ∧
      (∀ᶠ n in atTop, (br n).equivFun (scale n • pivot) ∈ Q) ∧ 0 ≤ C ∧
      ∀ᶠ n in atTop, ∀ (k : Fin 3) (y : Y n) (x : G)
        (sample : Fin (finrank ℝ (cartanRootIdeal H)) → ℝ)
        (f : G → G) (hf : LipschitzWith Λ f),
        ∀ (A : W →ₗ[ℝ] W) (offset : W) (ε : ℝ),
        (∀ j z, z ∈ Q →
          ‖F.sampledProbeProfile hExpD (fun g => (π (f g)).toAdd)
              ((hLip.comp hf).continuous) x (Real.log (scale n))
              (sampleBasis n) (br n) sample (D.vertex k n y j) z -
            (A (h (b.equivFun.symm z)) + offset)‖ ≤ ε) →
        ∃ path : Path (1 : G) (basedImage f
            (x * F.sampledProbeSuffix (sampleBasis n) sample (D.vertex k n y 0) *
              Exp (scale n • (pivot : GroupLieAlgebra (𝓘(ℝ, EG)) G)))
            (x * F.sampledProbeSuffix (sampleBasis n) sample
                (D.vertex k n y (Fin.last (P k).length)) *
              Exp (scale n • (pivot : GroupLieAlgebra (𝓘(ℝ, EG)) G)))),
          PathMetricBound path (C * scale n) (C * (1 + Real.log (2 + scale n))) ∧
          ∀ s, ∃ z ∈ (fun w => A (w - h pivot)) '' E k,
            ‖(π (path s)).toAdd - scale n • z‖ ≤
              2 * scale n * ε + C * (1 + Real.log (2 + scale n)) := by
  dsimp only
  obtain ⟨Q, C, hQ, hQV, hC, he⟩ := M.exists_linked_probe_paths T F hunimod eW
    hExp realize haarD dynkinD π hπ hLip X hDnil bD₀ βD hβD scale hscale hscale0
    pivot E V hEc hE hpivot hV hVconv hEV b₀ γ t probe P origin base η D
    sampleBasis hExpD Λ
  let b := WordBasisSelections.basis X (boundedBracketWords d) βD
  let h : H →ₗ[ℝ] W := eW.toLinearMap.comp
    ((heightProjection T.character).comp H.incl.toLinearMap)
  have hkill (x y : H) : h ⁅x, y⁆ = 0 := by
    change eW (heightProjection T.character ⁅(x : GroupLieAlgebra (𝓘(ℝ, EG)) G), y⁆) = 0
    rw [T.height_lie, map_zero]
  obtain ⟨Q₀, hQ₀, hQ₀V, hp, _⟩ := exists_compact_word_pivot_coordinates
    X (boundedBracketWords d) βD h hkill scale hscale hscale0 pivot V hV
    (hEV 0 (hpivot 0))
  refine ⟨Q ∪ Q₀, C, hQ.union hQ₀, Set.union_subset hQV hQ₀V,
    hp.mono (fun _ hn => Set.mem_union_right _ hn), hC, ?_⟩
  filter_upwards [he] with n hn
  intro k y x sample f hf A offset ε hgood
  exact hn k y x sample f hf A offset ε (fun j z hz => hgood j z (Set.mem_union_left _ hz))

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanProbeInteriorHeights
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finite_templateSymmetryGroup _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.instFiniteRootOffsetConeIndex _root_.OAI.PolycyclicRecognition.instFiniteSubtypeLinearEquivRealIdMemSubgroupLinearSupportSymmetryGroup _root_.OAI.PolycyclicRecognition.instNonemptyRootOffsetConeIndex _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.CartanFactorModel.heightRay_zero _root_.OAI.PolycyclicRecognition.CartanFactorModel.realScaleProfile_apply _root_.OAI.PolycyclicRecognition.CartanFactorModel.sampledProbeProfile_apply _root_.OAI.PolycyclicRecognition.cartanWeightDerivation_apply_root _root_.OAI.PolycyclicRecognition.cartanWeightDilation_apply _root_.OAI.PolycyclicRecognition.cartanWeightScale_add_apply _root_.OAI.PolycyclicRecognition.cartanWeightScale_zero_apply _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.nilshadowWeightDerivation_symm _root_.OAI.PolycyclicRecognition.nilshadowWeightOperator_symm _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Switching heights for every actual compact probe template -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra Set

variable {L W : Type} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {H : LieSubalgebra ℝ L} [H.IsCartanSubalgebra] (M : CartanWordModel H)
  {a : ℕ} (T : TriangularAdjoint L a)
  (hunimod : ∀ x : L, LinearMap.trace ℝ L (ad ℝ L x) = 0)
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)

set_option maxHeartbeats 1000000 in
theorem exists_probe_switching_height
    (b : Basis (Fin (finrank ℝ H)) ℝ H)
    {E V : Set W} (hE : IsCompact E) (hne : E.Nonempty)
    (hV : IsOpen V) (hEV : E ⊆ V) (i : Fin M.letterCount) :
    ∃ z : Fin (finrank ℝ H) → ℝ,
      eW (heightProjection T.character (b.equivFun.symm z : L)) ∈ V ∧
      (M.supportIn T hunimod eW).weightSupport E i < M.weight i (b.equivFun.symm z) := by
  have hnz : (M.supportIn T hunimod eW).weight i ≠ 0 := by
    intro hz
    apply M.weight_nonzero i
    funext h
    have he := congrArg (fun f : W →ₗ[ℝ] ℝ =>
      f (eW (heightProjection T.character (h : L)))) hz
    simpa [supportIn, SupportDatum.transport, supportDatum_weight,
      cartanHeightWeight_projection] using he
  obtain ⟨w, hw, hs⟩ := (M.supportIn T hunimod eW).exists_weightSupport_lt_on_open
    hE hne hV hEV i hnz
  obtain ⟨v, hv⟩ := (eW.surjective.comp (cartan_height_surjective T H)) w
  change eW (heightProjection T.character (v : L)) = w at hv
  refine ⟨b.equivFun v, ?_, ?_⟩
  · simpa only [LinearEquiv.symm_apply_apply, hv] using hw
  · simp only [LinearEquiv.symm_apply_apply]
    have he : (M.supportIn T hunimod eW).weight i w = M.weight i v := by
      rw [← hv]
      simp [supportIn, SupportDatum.transport, supportDatum_weight,
        cartanHeightWeight_projection]
    exact hs.trans_eq he

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanConcentratedPaths
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_countable _root_.OAI.PolycyclicRecognition.finitelyGeneratedSubgroupIndex_countable _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.instFiniteRootOffsetConeIndex _root_.OAI.PolycyclicRecognition.instNonemptyRootOffsetConeIndex _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.unitaryCentralFixed_complete _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Good linked probes from the published concentration inputs -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule MeasureTheory Filter Set TopologicalSpace
open scoped Manifold Topology NNReal ENNReal

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

variable [MeasurableSpace C((Fin (finrank ℝ H) → ℝ), W)]
  [BorelSpace C((Fin (finrank ℝ H) → ℝ), W)]

set_option maxHeartbeats 1000000 in
theorem exists_concentrated_linked_paths
    {K : ℕ → Type} [∀ n, TopologicalSpace (K n)] [∀ n, CompactSpace (K n)]
    [∀ n, T2Space (K n)] [∀ n, MeasurableSpace (K n)] [∀ n, BorelSpace (K n)]
    [∀ n, Nonempty (K n)]
    [Nonempty (Fin M.letterCount)]
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
    (hweights : ∀ i, 0 < (M.supportIn T hunimod eW).weightSupport E i)
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
    (Eprobe : Fin 3 → Set W)
    (probe : Fin 3 → ∀ n, K n → F.N.carrier)
    (P : ∀ k, M.BoxProbeChains T F hunimod eW b₀ (Eprobe k) β
      (fun i => (1 + δ) * (M.supportIn T hunimod eW).weightSupport E i) scale (probe k))
    (origin base : ℕ → cartanRootIdeal H)
    (D : M.LinkedProbeChains T F hunimod eW b₀ Eprobe β
      (fun i => (1 + δ) * (M.supportIn T hunimod eW).weightSupport E i)
      scale probe P (fun n _ => origin n) (fun n _ => base n) ε)
    (rem : RemezPolynomialInput) (hdim : 1 ≤ finrank ℝ (cartanRootIdeal H))
    (p : ℕ → NormalizedPair G Λ) (x : ℕ → G)
    (hN : Continuous F.ExpN) (hD : Continuous F.ExpD)
    (pivot : H) (V : Set W) (hV : IsOpen V) (hVconv : Convex ℝ V)
    (hEc : ∀ k, IsCompact (Eprobe k)) (hEconv : ∀ k, Convex ℝ (Eprobe k))
    (hpivot : ∀ k, eW (heightProjection T.character pivot) ∈ Eprobe k)
    (hEV : ∀ k, Eprobe k ⊆ V)
    (hVheight : V ⊆ (fun w => (1 - c * δ) • w) '' E)
    (σ : Fin M.letterCount → Bool)
    (hσ : (weightChamber (fun i =>
      ((M.supportIn T hunimod eW).weight i).toContinuousLinearMap) σ).Nonempty) :
    let b := WordBasisSelections.basis X (boundedBracketWords d) βD
    let cost := fun j => bracketWordExponent (fun _ : I => 1) (βD.val j)
    let br := fun n => exponentialRescaleBasis b cost (Real.log (scale n))
    let h : H →ₗ[ℝ] W := eW.toLinearMap.comp
      ((heightProjection T.character).comp H.incl.toLinearMap)
    ∃ (Z : Set (Fin (finrank ℝ H) → ℝ)) (C : ℝ),
      IsCompact Z ∧ Z ⊆ {z | h (b.equivFun.symm z) ∈ V} ∧ 0 ≤ C ∧
      (∀ᶠ n in atTop, (br n).equivFun (scale n • pivot) ∈ Z) ∧
      ∀ [CompactSpace Z]
    (ν : ∀ n, ProbabilityMeasure (K n))
    [∀ n, (ν n : Measure (K n)).InnerRegular]
    [MeasurableSpace C(Z, W)] [BorelSpace C(Z, W)]
    [BorelSpace (C(Z, W) × C(Z, W))] [HasOuterApproxClosed (C(Z, W) × C(Z, W))]
    (limitLaw : ProbabilityMeasure (C(Z, W) × C(Z, W)))
    (A : W →ₗ[ℝ] W) (b : Bool → W) (f : C(Z, W) × C(Z, W))
    (_hf : f ∈ (limitLaw : Measure _).support)
    (_haffine : ∀ s z, (if s then f.2 else f.1) z =
      A (eW (heightProjection T.character
        ((WordBasisSelections.basis X (boundedBracketWords d) βD).equivFun.symm z.val :
          GroupLieAlgebra (𝓘(ℝ, EG)) G))) + b s)
    (_hlim :
      let J := fun n g => (π ((p n).val.1 g)).toAdd
      let hJ := fun n => (hπ.comp (p n).property.1.1).continuous
      let r := fun n => max (Real.log (scale n)) 0
      let bN := fun n => M.boxBasis T hunimod eW E β (scale n)
      let bD := fun n => exponentialRescaleBasis
        (WordBasisSelections.basis X (boundedBracketWords d) βD)
        (fun j => bracketWordExponent (fun _ : I => 1) (βD.val j)) (r n)
      Tendsto (fun n => ProbabilityMeasure.map
        (cellProbabilityMeasure volume
          (Icc (fun _ : Fin (finrank ℝ (cartanRootIdeal H)) => (-1 : ℝ)) (fun _ => (1 : ℝ)))
          (coordinate_cube_mass zero_lt_one).1 (coordinate_cube_mass zero_lt_one).2)
        (f := (fun y =>
          ((F.sampledProbeProfile hD (J n) (hJ n) (x n) (r n) (bN n) (bD n) y
            (origin n)).restrict Z,
           (F.sampledProbeProfile hD (J n) (hJ n) (x n) (r n) (bN n) (bD n) y
            (base n)).restrict Z))) (((F.measurable_fixed_sampledProbeProfile hN hD (J n) (hJ n) (x n) (r n) (bN n) (bD n) (origin n) Z).prodMk (F.measurable_fixed_sampledProbeProfile hN hD (J n) (hJ n) (x n) (r n) (bN n) (bD n) (base n) Z)).aemeasurable)) atTop (𝓝 limitLaw)),
    let J := fun n g => (π ((p n).val.1 g)).toAdd
    let hJ := fun n => (hπ.comp (p n).property.1.1).continuous
    let r := fun n => max (Real.log (scale n)) 0
    let bN := fun n => M.boxBasis T hunimod eW E β (scale n)
    let bD := fun n => exponentialRescaleBasis
      (WordBasisSelections.basis X (boundedBracketWords d) βD)
      (fun j => bracketWordExponent (fun _ : I => 1) (βD.val j)) (r n)
    let q := fun z : Z => eW (heightProjection T.character
      ((WordBasisSelections.basis X (boundedBracketWords d) βD).equivFun.symm z.val :
        GroupLieAlgebra (𝓘(ℝ, EG)) G))
    ∃ (η : ℕ → ℝ) (sample : ℕ → (Fin (finrank ℝ (cartanRootIdeal H)) → ℝ))
      (good : ∀ n, Set (K n)),
      (∀ n, 0 < η n) ∧ Tendsto η atTop (𝓝 0) ∧
      (∀ n, IsCompact (good n) ∧ MeasurableSet (good n) ∧
        (1 / 4 : ℝ≥0∞) < (ν n : Measure (K n)) (good n)) ∧
      ∀ᶠ n in atTop,
        sample n ∈ Icc (fun _ => (-1 : ℝ)) (fun _ => (1 : ℝ)) ∧
        (∀ (s : Bool) (z : Z),
          ‖F.sampledProbeProfile hD (J n) (hJ n) (x n) (r n) (bN n) (bD n) (sample n)
            (if s then base n else origin n) z - (A (q z) + b s)‖ < η n) ∧
        (∀ y ∈ good n, ∀ (k : Fin 3) (j : Fin ((P k).length + 1)) (z : Z),
          ‖F.sampledProbeProfile hD (J n) (hJ n) (x n) (r n) (bN n) (bD n) (sample n)
            (D.vertex k n y j) z - (A (q z) + b (k != 0))‖ < 2 * η n) ∧
        ∀ y ∈ good n, ∀ k : Fin 3,
          ∃ path : Path (1 : G) (basedImage (p n).val.1
              (x n * F.sampledProbeSuffix (bN n) (sample n) (D.vertex k n y 0) *
                Exp (scale n • (pivot : GroupLieAlgebra (𝓘(ℝ, EG)) G)))
              (x n * F.sampledProbeSuffix (bN n) (sample n)
                  (D.vertex k n y (Fin.last (P k).length)) *
                Exp (scale n • (pivot : GroupLieAlgebra (𝓘(ℝ, EG)) G)))),
            PathMetricBound path (C * scale n) (C * (1 + Real.log (2 + scale n))) ∧
            ∀ t, ∃ w ∈ (fun z => A (z - h pivot)) '' Eprobe k,
              ‖(π (path t)).toAdd - scale n • w‖ ≤
                4 * scale n * η n + C * (1 + Real.log (2 + scale n)) := by
  dsimp only
  let b := WordBasisSelections.basis X (boundedBracketWords d) βD
  let cost := fun j => bracketWordExponent (fun _ : I => 1) (βD.val j)
  let br := fun n => exponentialRescaleBasis b cost (Real.log (scale n))
  let h : H →ₗ[ℝ] W := eW.toLinearMap.comp
    ((heightProjection T.character).comp H.incl.toLinearMap)
  let U := {z | h (b.equivFun.symm z) ∈ V}
  have hU : IsOpen U := hV.preimage
    (h.comp b.equivFun.symm.toLinearMap).continuous_of_finiteDimensional
  have hconn : IsPreconnected U :=
    (hVconv.linear_preimage (h.comp b.equivFun.symm.toLinearMap)).isPreconnected
  have hUne : U.Nonempty := ⟨b.equivFun pivot, by
    change eW (heightProjection T.character (b.equivFun.symm (b.equivFun pivot) :
      GroupLieAlgebra (𝓘(ℝ, EG)) G)) ∈ V
    rw [LinearEquiv.symm_apply_apply]
    exact hEV 0 (hpivot 0)⟩
  have hUheight : ∀ z ∈ U, eW (heightProjection T.character
      (b.equivFun.symm z : GroupLieAlgebra (𝓘(ℝ, EG)) G)) ∈
      (fun w => (1 - c * δ) • w) '' E := fun _ hz => hVheight hz
  have hinterior (k : Fin 3) (i : Fin M.letterCount) : ∃ z ∈ U,
      (M.supportIn T hunimod eW).weightSupport (Eprobe k) i <
        M.weight i (b.equivFun.symm z) :=
    M.exists_probe_switching_height T hunimod eW b (hEc k) ⟨_, hpivot k⟩ hV (hEV k) i
  obtain ⟨Z, C, hZ, hZV, hp, hC, hpaths⟩ :=
    M.exists_linked_probe_paths_with_pivot T F hunimod eW hExp realize haarD dynkinD
      π hπExp hπ X hDnil bD₀ βD hβD scale hscale
      (fun n => lt_of_lt_of_le zero_lt_one (hscale1 n)) pivot Eprobe V hEc hEconv
      hpivot hV hVconv hEV b₀ β
      (fun i => (1 + δ) * (M.supportIn T hunimod eW).weightSupport E i)
      probe P (fun n _ => origin n) (fun n _ => base n) ε D
      (fun n => M.boxBasis T hunimod eW E β (scale n)) hD Λ
  refine ⟨Z, C, hZ, hZV, hC, hp, ?_⟩
  intro instZ ν instν instMeas instBorel instProd instOuter limitLaw A bval f hf haffine hlim
  obtain ⟨η, sample, good, hη0, hη, hg, he⟩ :=
    M.select_linked_profiles_of_published_inputs T F hunimod eW hExp realize haarN haarD
      dynkinN dynkinD m π hπExp hdec hvan hΛ hπ hpath b₀ hE hne β γ hβ hweights
      hδ hc hhi ht hcost hgap X hDnil hDletters bD₀ βD hβD aN hmN aD hmD
      scale hscale hmono hscale1 ε hεpos hε Eprobe probe P origin base D rem hdim p x
      hN hD U hU hconn hUne hUheight σ hσ hinterior Z hZV ν limitLaw A bval f hf haffine hlim
  refine ⟨η, sample, good, hη0, hη, hg, ?_⟩
  filter_upwards [he, hpaths] with n hn hnpaths
  refine ⟨hn.1, hn.2.1, hn.2.2, ?_⟩
  intro y hy k
  have hr : max (Real.log (scale n)) 0 = Real.log (scale n) :=
    max_eq_left (Real.log_nonneg (hscale1 n))
  have hgood (j : Fin ((P k).length + 1)) (z) (hz : z ∈ Z) :
      ‖F.sampledProbeProfile hD (fun g => (π ((p n).val.1 g)).toAdd)
        ((hπ.comp (p n).property.1.1).continuous) (x n) (Real.log (scale n))
        (M.boxBasis T hunimod eW E β (scale n)) (br n) (sample n)
        (D.vertex k n y j) z - (A (eW (heightProjection T.character
          (b.equivFun.symm z : GroupLieAlgebra (𝓘(ℝ, EG)) G))) + bval (k != 0))‖ ≤ 2 * η n := by
    simpa only [hr] using (hn.2.2 y hy k j ⟨z, hz⟩).le
  obtain ⟨path, hm, hh⟩ := hnpaths k y (x n) (sample n) (p n).val.1 (p n).property.1.1
    A (bval (k != 0)) (2 * η n) hgood
  refine ⟨?_, ?_, ?_⟩
  · simpa only [hr] using path
  · exact hm
  · intro t
    obtain ⟨w, hw, hb⟩ := hh t
    exact ⟨w, hw, by nlinarith [hb]⟩

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanSampledProbeFrames
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original center and exact group frames of a sampled profile -/

noncomputable section
namespace PolycyclicRecognition

open Module LieAlgebra
open scoped Manifold

variable {EG G W : Type} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [IsTopologicalGroup G]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  {Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H Exp)

set_option maxHeartbeats 1000000 in
omit [IsTopologicalGroup G] in
/-- The chart point corresponding to a physical Cartan vector is exact even
when the logarithmic rescaling basis moves with the scale. -/
theorem CartanFactorModel.profileChart_coordinates
    (bD : Basis (Fin (finrank ℝ H)) ℝ H) (v : H) :
    F.profileChart bD (bD.equivFun v) = F.inclusionD (F.ExpD (F.D.equiv v)) := by
  simp only [profileChart, LinearEquiv.symm_apply_apply]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanProfilePivot
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_nonempty _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A total profile base point at the moving physical pivot -/

noncomputable section
namespace PolycyclicRecognition

open Module LieAlgebra Set Filter
open scoped Manifold Topology

variable {EG G W I : Type} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [IsTopologicalGroup G]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [Fintype I] [DecidableEq I]
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  {Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H Exp)

set_option maxHeartbeats 1000000 in
omit [IsTopologicalGroup G] in
/-- Only the finite initial segment uses a fallback. Eventually the total
subtype-valued base point is the exact physical pivot, with its unchanged
height. No extra base point membership hypothesis is needed for small scales. -/
theorem CartanFactorModel.exists_profile_pivot
    (X : I → H) (S : Finset (FreeMagma I)) (β : WordBasisSelections X S)
    (h : H →ₗ[ℝ] W) (hh : ∀ x y : H, h ⁅x, y⁆ = 0)
    (scale : ℕ → ℝ) (hs0 : ∀ n, 0 < scale n) (pivot : H)
    (Z : Set (Fin (finrank ℝ H) → ℝ))
    (hp : ∀ᶠ n in atTop,
      (exponentialRescaleBasis (WordBasisSelections.basis X S β)
        (fun j => bracketWordExponent (fun _ : I => 1) (β.val j))
        (Real.log (scale n))).equivFun (scale n • pivot) ∈ Z) :
    let b := WordBasisSelections.basis X S β
    let br := fun n => exponentialRescaleBasis b
      (fun j => bracketWordExponent (fun _ : I => 1) (β.val j)) (Real.log (scale n))
    ∃ z₀ : ℕ → Z, ∀ᶠ n in atTop,
      (z₀ n).val = (br n).equivFun (scale n • pivot) ∧
      F.profileChart (br n) (z₀ n).val =
        Exp (scale n • (pivot : GroupLieAlgebra (𝓘(ℝ, EG)) G)) ∧
      h (b.equivFun.symm (z₀ n).val) = h pivot := by
  classical
  dsimp only
  let b := WordBasisSelections.basis X S β
  let br := fun n => exponentialRescaleBasis b
    (fun j => bracketWordExponent (fun _ : I => 1) (β.val j)) (Real.log (scale n))
  have hne : Nonempty Z := by
    obtain ⟨n, hn⟩ := hp.exists
    exact ⟨⟨(br n).equivFun (scale n • pivot), hn⟩⟩
  let z₀ : ℕ → Z := fun n =>
    if hz : (br n).equivFun (scale n • pivot) ∈ Z
    then ⟨(br n).equivFun (scale n • pivot), hz⟩ else Classical.choice hne
  refine ⟨z₀, ?_⟩
  filter_upwards [hp] with n hn
  have hz : (z₀ n).val = (br n).equivFun (scale n • pivot) := by
    dsimp only [z₀]
    split
    · rfl
    · rename_i hz
      exact (hz hn).elim
  refine ⟨hz, ?_, ?_⟩
  · rw [hz, F.profileChart_coordinates]
    exact F.compatibleD _
  · rw [hz]
    exact word_length_chart_pivot_height X S β h hh (hs0 n) pivot

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanConcentratedFrames
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_countable _root_.OAI.PolycyclicRecognition.finitelyGeneratedSubgroupIndex_countable _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.instFiniteRootOffsetConeIndex _root_.OAI.PolycyclicRecognition.instNonemptyRootOffsetConeIndex _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.unitaryCentralFixed_complete _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Concentrated profiles at the actual moving contact pivot -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule MeasureTheory Filter Set TopologicalSpace
open scoped Manifold Topology NNReal ENNReal

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

variable [MeasurableSpace C((Fin (finrank ℝ H) → ℝ), W)]
  [BorelSpace C((Fin (finrank ℝ H) → ℝ), W)]

set_option maxHeartbeats 1000000 in
theorem exists_concentrated_profile_frames_oai
    {K : ℕ → Type} [∀ n, TopologicalSpace (K n)] [∀ n, CompactSpace (K n)]
    [∀ n, T2Space (K n)] [∀ n, MeasurableSpace (K n)] [∀ n, BorelSpace (K n)]
    [∀ n, Nonempty (K n)]
    [Nonempty (Fin M.letterCount)]
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
    (hweights : ∀ i, 0 < (M.supportIn T hunimod eW).weightSupport E i)
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
    (Eprobe : Fin 3 → Set W)
    (probe : Fin 3 → ∀ n, K n → F.N.carrier)
    (P : ∀ k, M.BoxProbeChains T F hunimod eW b₀ (Eprobe k) β
      (fun i => (1 + δ) * (M.supportIn T hunimod eW).weightSupport E i) scale (probe k))
    (origin base : ℕ → cartanRootIdeal H)
    (D : M.LinkedProbeChains T F hunimod eW b₀ Eprobe β
      (fun i => (1 + δ) * (M.supportIn T hunimod eW).weightSupport E i)
      scale probe P (fun n _ => origin n) (fun n _ => base n) ε)
    (rem : RemezPolynomialInput) (hdim : 1 ≤ finrank ℝ (cartanRootIdeal H))
    (p : ℕ → NormalizedPair G Λ) (x : ℕ → G)
    (hN : Continuous F.ExpN) (hD : Continuous F.ExpD)
    (pivot : H) (V : Set W) (hV : IsOpen V) (hVconv : Convex ℝ V)
    (hEc : ∀ k, IsCompact (Eprobe k)) (hEconv : ∀ k, Convex ℝ (Eprobe k))
    (hpivot : ∀ k, eW (heightProjection T.character pivot) ∈ Eprobe k)
    (hEV : ∀ k, Eprobe k ⊆ V)
    (hVheight : V ⊆ (fun w => (1 - c * δ) • w) '' E)
    (σ : Fin M.letterCount → Bool)
    (hσ : (weightChamber (fun i =>
      ((M.supportIn T hunimod eW).weight i).toContinuousLinearMap) σ).Nonempty) :
    let b := WordBasisSelections.basis X (boundedBracketWords d) βD
    let cost := fun j => bracketWordExponent (fun _ : I => 1) (βD.val j)
    let br := fun n => exponentialRescaleBasis b cost (Real.log (scale n))
    let h : H →ₗ[ℝ] W := eW.toLinearMap.comp
      ((heightProjection T.character).comp H.incl.toLinearMap)
    ∃ (Z : Set (Fin (finrank ℝ H) → ℝ)) (C : ℝ),
      IsCompact Z ∧ Z ⊆ {z | h (b.equivFun.symm z) ∈ V} ∧ 0 ≤ C ∧
      ∃ z₀ : ℕ → Z,
      (∀ᶠ n in atTop,
        F.profileChart (br n) (z₀ n).val =
          Exp (scale n • (pivot : GroupLieAlgebra (𝓘(ℝ, EG)) G)) ∧
        h (b.equivFun.symm (z₀ n).val) = h pivot) ∧
      ∀ [CompactSpace Z]
    (ν : ∀ n, ProbabilityMeasure (K n))
    [∀ n, (ν n : Measure (K n)).InnerRegular]
    [MeasurableSpace C(Z, W)] [BorelSpace C(Z, W)]
    [BorelSpace (C(Z, W) × C(Z, W))] [HasOuterApproxClosed (C(Z, W) × C(Z, W))]
    (limitLaw : ProbabilityMeasure (C(Z, W) × C(Z, W)))
    (A : W →ₗ[ℝ] W) (bval : Bool → W) (f : C(Z, W) × C(Z, W))
    (_hf : f ∈ (limitLaw : Measure _).support)
    (_haffine : ∀ s z, (if s then f.2 else f.1) z =
      A (eW (heightProjection T.character
        ((WordBasisSelections.basis X (boundedBracketWords d) βD).equivFun.symm z.val :
          GroupLieAlgebra (𝓘(ℝ, EG)) G))) + bval s)
    (_hlim :
      let J := fun n g => (π ((p n).val.1 g)).toAdd
      let hJ := fun n => (hπ.comp (p n).property.1.1).continuous
      let r := fun n => max (Real.log (scale n)) 0
      let bN := fun n => M.boxBasis T hunimod eW E β (scale n)
      let bD := fun n => exponentialRescaleBasis
        (WordBasisSelections.basis X (boundedBracketWords d) βD)
        (fun j => bracketWordExponent (fun _ : I => 1) (βD.val j)) (r n)
      Tendsto (fun n => ProbabilityMeasure.map
        (cellProbabilityMeasure volume
          (Icc (fun _ : Fin (finrank ℝ (cartanRootIdeal H)) => (-1 : ℝ)) (fun _ => (1 : ℝ)))
          (coordinate_cube_mass zero_lt_one).1 (coordinate_cube_mass zero_lt_one).2)
        (f := (fun y =>
          ((F.sampledProbeProfile hD (J n) (hJ n) (x n) (r n) (bN n) (bD n) y
            (origin n)).restrict Z,
           (F.sampledProbeProfile hD (J n) (hJ n) (x n) (r n) (bN n) (bD n) y
            (base n)).restrict Z))) (((F.measurable_fixed_sampledProbeProfile hN hD (J n) (hJ n) (x n) (r n) (bN n) (bD n) (origin n) Z).prodMk (F.measurable_fixed_sampledProbeProfile hN hD (J n) (hJ n) (x n) (r n) (bN n) (bD n) (base n) Z)).aemeasurable)) atTop (𝓝 limitLaw)),
    let chart := fun n (z : Z) => F.profileChart (br n) z.val
    let q := fun z : Z => h (b.equivFun.symm z.val)
    ∃ (η : ℕ → ℝ) (sample : ℕ → (Fin (finrank ℝ (cartanRootIdeal H)) → ℝ))
      (good : ∀ n, Set (K n)),
      (∀ n, 0 < η n) ∧ Tendsto η atTop (𝓝 0) ∧
      (∀ n, IsCompact (good n) ∧ MeasurableSet (good n) ∧
        (1 / 4 : ℝ≥0∞) < (ν n : Measure (K n)) (good n)) ∧
      ∀ᶠ n in atTop,
        (∀ s : Bool,
          ‖rescaledMapProfile (fun g => (π ((p n).val.1 g)).toAdd) (x n)
            (F.sampledProbeSuffix (M.boxBasis T hunimod eW E β (scale n)) (sample n)
              (if s then base n else origin n)) (Real.log (scale n))
            (chart n) (z₀ n) - (A (q (z₀ n)) + bval s)‖ < η n) ∧
        (∀ y ∈ good n, ∀ (k : Fin 3) (j : Fin ((P k).length + 1)),
          ‖rescaledMapProfile (fun g => (π ((p n).val.1 g)).toAdd) (x n)
            (F.sampledProbeSuffix (M.boxBasis T hunimod eW E β (scale n)) (sample n)
              (D.vertex k n y j)) (Real.log (scale n))
            (chart n) (z₀ n) - (A (q (z₀ n)) + bval (k != 0))‖ < 2 * η n) ∧
        ∀ y ∈ good n, ∀ k : Fin 3,
          ∃ path : Path (1 : G) (basedImage (p n).val.1
              (x n * F.sampledProbeSuffix (M.boxBasis T hunimod eW E β (scale n))
                (sample n) (D.vertex k n y 0) * chart n (z₀ n))
              (x n * F.sampledProbeSuffix (M.boxBasis T hunimod eW E β (scale n))
                (sample n) (D.vertex k n y (Fin.last (P k).length)) * chart n (z₀ n))),
            PathMetricBound path (C * scale n) (C * (1 + Real.log (2 + scale n))) ∧
            ∀ t, ∃ w ∈ (fun z => A (z - h pivot)) '' Eprobe k,
              ‖(π (path t)).toAdd - scale n • w‖ ≤
                4 * scale n * η n + C * (1 + Real.log (2 + scale n)) := by
  dsimp only
  let b := WordBasisSelections.basis X (boundedBracketWords d) βD
  let br := fun n => exponentialRescaleBasis b
    (fun j => bracketWordExponent (fun _ : I => 1) (βD.val j)) (Real.log (scale n))
  let h : H →ₗ[ℝ] W := eW.toLinearMap.comp
    ((heightProjection T.character).comp H.incl.toLinearMap)
  obtain ⟨Z, C, hZ, hZV, hC, hp, hselect⟩ :=
    M.exists_concentrated_linked_paths T F hunimod eW hExp realize haarN haarD
      dynkinN dynkinD m π hπExp hdec hvan hΛ hπ hpath b₀ hE hne β γ hβ hweights
      hδ hc hhi ht hcost hgap X hDnil hDletters bD₀ βD hβD aN hmN aD hmD
      scale hscale hmono hscale1 ε hεpos hε Eprobe probe P origin base D rem hdim p x
      hN hD pivot V hV hVconv hEc hEconv hpivot hEV hVheight σ hσ
  have hkill (u v : H) : h ⁅u, v⁆ = 0 := by
    change eW (heightProjection T.character
      ⁅(u : GroupLieAlgebra (𝓘(ℝ, EG)) G), v⁆) = 0
    rw [T.height_lie, map_zero]
  obtain ⟨z₀, hz₀⟩ := F.exists_profile_pivot X (boundedBracketWords d) βD h hkill
    scale (fun n => lt_of_lt_of_le zero_lt_one (hscale1 n)) pivot Z hp
  refine ⟨Z, C, hZ, hZV, hC, z₀, hz₀.mono (fun _ hn => hn.2), ?_⟩
  intro instZ ν instν instMeas instBorel instProd instOuter limitLaw A bval f hf haffine hlim
  obtain ⟨η, sample, good, hη0, hη, hg, he⟩ := hselect ν limitLaw A bval f hf haffine hlim
  refine ⟨η, sample, good, hη0, hη, hg, ?_⟩
  filter_upwards [he, hz₀] with n hn hzn
  have hr : max (Real.log (scale n)) 0 = Real.log (scale n) :=
    max_eq_left (Real.log_nonneg (hscale1 n))
  refine ⟨?_, ?_, ?_⟩
  · intro s
    have hs := hn.2.1 s (z₀ n)
    simpa only [hr, CartanFactorModel.sampledProbeProfile_apply,
      CartanFactorModel.sampledProbeSuffix, map_mul, CartanFactorModel.profileChart, rescaledMapProfile,
      h, LinearMap.comp_apply, LieHom.coe_toLinearMap, LieSubalgebra.coe_incl, LinearEquiv.coe_coe] using hs
  · intro y hy k j
    have hj := hn.2.2.1 y hy k j (z₀ n)
    simpa only [hr, CartanFactorModel.sampledProbeProfile_apply,
      CartanFactorModel.sampledProbeSuffix, map_mul, CartanFactorModel.profileChart, rescaledMapProfile,
      h, LinearMap.comp_apply, LieHom.coe_toLinearMap, LieSubalgebra.coe_incl, LinearEquiv.coe_coe] using hj
  · intro y hy k
    obtain ⟨path, hm, hh⟩ := hn.2.2.2 y hy k
    have hend :
        basedImage (p n).val.1
          (x n * F.sampledProbeSuffix (M.boxBasis T hunimod eW E β (scale n))
            (sample n) (D.vertex k n y 0) * F.profileChart (br n) (z₀ n).val)
          (x n * F.sampledProbeSuffix (M.boxBasis T hunimod eW E β (scale n))
            (sample n) (D.vertex k n y (Fin.last (P k).length)) *
              F.profileChart (br n) (z₀ n).val) =
        basedImage (p n).val.1
          (x n * F.sampledProbeSuffix (M.boxBasis T hunimod eW E β (scale n))
            (sample n) (D.vertex k n y 0) *
              Exp (scale n • (pivot : GroupLieAlgebra (𝓘(ℝ, EG)) G)))
          (x n * F.sampledProbeSuffix (M.boxBasis T hunimod eW E β (scale n))
            (sample n) (D.vertex k n y (Fin.last (P k).length)) *
              Exp (scale n • (pivot : GroupLieAlgebra (𝓘(ℝ, EG)) G))) := by
      rw [hzn.2.1]
    refine ⟨path.cast rfl hend, hm, ?_⟩
    exact hh

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

theorem solution : type_of% @OAI.PolycyclicRecognition.CartanWordModel.exists_concentrated_profile_frames_oai := @OAI.PolycyclicRecognition.CartanWordModel.exists_concentrated_profile_frames_oai
