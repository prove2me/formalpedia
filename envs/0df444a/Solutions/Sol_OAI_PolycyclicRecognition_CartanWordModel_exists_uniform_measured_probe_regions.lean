-- Prove2me | solution 1 for OAI.PolycyclicRecognition.CartanWordModel.exists_uniform_measured_probe_regions
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-02T23:02:12.334702+00:00
-- url     : https://prove2.me/submissions/d1693be6-deda-4763-9731-e4934a605f7e

import Mathlib
import Definitions.Def_PolycyclicRecognition
import Definitions.Def_OAIQ093D027
import Theorems.Thm_OAI_PolycyclicRecognition_CartanWordModel_exists_controlled_profile_quotient_restriction
import Theorems.Thm_OAI_PolycyclicRecognition_CartanWordModel_exists_uniform_profile_bridge_restrictions_of_basis

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
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_MaximizingCoordinateCriterion
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The converse basis-exchange criterion

An invertible selected basis is maximizing if every nonzero coordinate of
each available vector lies in a basis direction of at least its weight.
The determinant permutation supplies the required matching for any rival
basis. This is used to extend an ideal basis by zero-width pure words.
-/

noncomputable section
namespace PolycyclicRecognition

open scoped BigOperators

theorem maximizingColumnBasis_of_coordinate_support {I : Type} {n : ℕ}
    (v : I → Fin n → ℝ) (w : I → ℝ) (b : Fin n → I)
    (hb : (columnBasisMatrix v b).det ≠ 0)
    (hcoord : ∀ y j, columnCoordinates v b y j ≠ 0 → w y ≤ w (b j)) :
    IsMaximizingColumnBasis v w b := by
  classical
  refine ⟨hb, ?_⟩
  intro d hd
  let A := (columnBasisMatrix v b)⁻¹ * columnBasisMatrix v d
  have hA : A.det ≠ 0 := by
    rw [Matrix.det_mul, Matrix.det_nonsing_inv, Ring.inverse_eq_inv]
    exact mul_ne_zero (inv_ne_zero hb) hd
  have hsum : (∑ σ : Equiv.Perm (Fin n),
      Equiv.Perm.sign σ • ∏ i, A (σ i) i) ≠ 0 := by
    rw [← Matrix.det_apply]
    exact hA
  obtain ⟨σ, _, hσ⟩ := Finset.exists_ne_zero_of_sum_ne_zero hsum
  have hentries (i : Fin n) : A (σ i) i ≠ 0 := by
    intro hz
    have hp : (∏ j, A (σ j) j) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ i) hz
    exact hσ (by rw [hp, smul_zero])
  have hc (i : Fin n) : w (d i) ≤ w (b (σ i)) := by
    apply hcoord
    have he : columnCoordinates v b (d i) (σ i) = A (σ i) i := by
      simp only [columnCoordinates, A, Matrix.mul_apply, Matrix.mulVec, dotProduct,
        columnBasisMatrix]
    rw [he]
    exact hentries i
  change (∑ i, w (d i)) ≤ ∑ i, w (b i)
  exact (Finset.sum_le_sum (fun i _ => hc i)).trans_eq (Equiv.sum_comp σ (fun i => w (b i)))

end PolycyclicRecognition

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

variable (E G : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
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
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_MixedWordBoxModel
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The concrete nilpotent box model of a cone ideal

The finite mixed words generate the ideal even as a vector space. Using
them as an alphabet allows the existing box calculus to apply directly.
Flattening this alphabet retains the original word and its exact width.
-/

noncomputable section
namespace PolycyclicRecognition

open Module LieModule LieAlgebra
open scoped BigOperators

theorem eval_substituteBracketWord {I J V : Type} [LieRing V] [LieAlgebra ℝ V]
    (X : J → V) (f : I → FreeMagma J) (w : FreeMagma I) :
    evalBracketWord X (substituteBracketWord f w) =
      evalBracketWord (fun i => evalBracketWord X (f i)) w := by
  induction w using FreeMagma.rec with
  | of i => rfl
  | mul u v hu hv =>
    change ⁅evalBracketWord X (substituteBracketWord f u),
      evalBracketWord X (substituteBracketWord f v)⁆ =
      ⁅evalBracketWord (fun i => evalBracketWord X (f i)) u,
        evalBracketWord (fun i => evalBracketWord X (f i)) v⁆
    rw [hu, hv]

theorem exponent_substituteBracketWord {I J : Type} [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] (s : J → ℝ) (f : I → FreeMagma J) (w : FreeMagma I) :
    bracketWordExponent s (substituteBracketWord f w) =
      bracketWordExponent (fun i => bracketWordExponent s (f i)) w := by
  induction w using FreeMagma.rec with
  | of i => simp only [substituteBracketWord, bracketWordExponent_of]
  | mul u v hu hv =>
    change bracketWordExponent s (substituteBracketWord f u * substituteBracketWord f v) =
      bracketWordExponent (fun i => bracketWordExponent s (f i)) (u * v)
    simp only [bracketWordExponent_mul, hu, hv]

theorem bracketWordExponent_nonneg {I : Type} [Fintype I] [DecidableEq I]
    (s : I → ℝ) (hs : ∀ i, 0 ≤ s i) (w : FreeMagma I) :
    0 ≤ bracketWordExponent s w := by
  exact Finset.sum_nonneg fun i _ => mul_nonneg (Nat.cast_nonneg _) (hs i)

theorem bracketWordExponent_pos_of_mixed {I : Type} [Fintype I] [DecidableEq I]
    (s : I → ℝ) (outside : I → Prop) (hs : ∀ i, 0 ≤ s i)
    (hpos : ∀ i, outside i → 0 < s i) (w : FreeMagma I)
    (hw : IsMixedWord outside w) : 0 < bracketWordExponent s w := by
  induction w using FreeMagma.rec with
  | of i => simpa only [bracketWordExponent_of] using hpos i hw
  | mul u v hu hv =>
    change 0 < bracketWordExponent s (u * v)
    rw [bracketWordExponent_mul]
    rcases hw with hw | hw
    · exact add_pos_of_pos_of_nonneg (hu hw) (bracketWordExponent_nonneg s hs v)
    · exact add_pos_of_nonneg_of_pos (bracketWordExponent_nonneg s hs u) (hv hw)

namespace CartanWordModel

variable {L : Type} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {H : LieSubalgebra ℝ L} [H.IsCartanSubalgebra] (M : CartanWordModel H)

theorem coneOriginalWord_mixed (C : Set (H →ₗ[ℝ] ℝ))
    (w : FreeMagma (M.coneMixedWords C)) :
    IsMixedWord (fun i => (M.weight i : H →ₗ[ℝ] ℝ) ∉ C) (M.coneOriginalWord C w) := by
  induction w using FreeMagma.rec with
  | of i => exact i.property
  | mul u v hu _ => exact Or.inl hu

theorem coneOriginalWord_eval (C : Set (H →ₗ[ℝ] ℝ))
    (w : FreeMagma (M.coneMixedWords C)) :
    evalBracketWord M.letter (M.coneOriginalWord C w) =
      ((evalBracketWord (M.coneMixedVector C) w : M.coneWordIdeal C) :
        cartanRootIdeal H) := by
  rw [coneOriginalWord, eval_substituteBracketWord]
  exact (evalBracketWord_map (M.coneWordIdeal C).incl (M.coneMixedVector C) w).symm

theorem coneIdealWordCost_eq_original (C : Set (H →ₗ[ℝ] ℝ))
    (s : Fin M.letterCount → ℝ) (w : FreeMagma (M.coneMixedWords C)) :
    M.coneIdealWordCost C s w = bracketWordExponent s (M.coneOriginalWord C w) :=
  (exponent_substituteBracketWord s _ w).symm

theorem coneIdealWordCost_pos (C : Set (H →ₗ[ℝ] ℝ))
    (s : Fin M.letterCount → ℝ) (hs : ∀ i, 0 ≤ s i)
    (hpos : ∀ i, (M.weight i : H →ₗ[ℝ] ℝ) ∉ C → 0 < s i)
    (w : FreeMagma (M.coneMixedWords C)) : 0 < M.coneIdealWordCost C s w := by
  rw [M.coneIdealWordCost_eq_original]
  exact bracketWordExponent_pos_of_mixed s _ hs hpos _ (M.coneOriginalWord_mixed C w)

end CartanWordModel
end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_ConeIdealBasisExchange
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Original-word coordinate exchange inside the cone ideal -/

noncomputable section
namespace PolycyclicRecognition

open Module LieAlgebra LieModule

theorem bracketWordExponent_eq_zero_of_pure {I : Type} [Fintype I] [DecidableEq I]
    (s : I → ℝ) (outside : I → Prop) (hs : ∀ i, ¬outside i → s i = 0)
    (w : FreeMagma I) (hw : ¬IsMixedWord outside w) : bracketWordExponent s w = 0 := by
  induction w using FreeMagma.rec with
  | of i => exact (bracketWordExponent_of s i).trans (hs i hw)
  | mul u v hu hv =>
    change bracketWordExponent s (u * v) = 0
    rw [bracketWordExponent_mul, hu (fun h => hw (Or.inl h)),
      hv (fun h => hw (Or.inr h)), add_zero]

namespace CartanWordModel

variable {L : Type} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {H : LieSubalgebra ℝ L} [H.IsCartanSubalgebra] (M : CartanWordModel H)
  (C : Set (H →ₗ[ℝ] ℝ))

theorem coneIdeal_leaf_mem_of_ne_zero (w : M.coneMixedWords C)
    (hw : M.coneMixedVector C w ≠ 0) : FreeMagma.of w ∈ M.coneIdealWordList C := by
  apply (mem_boundedBracketWords _ _).mpr
  change 0 < M.coneIdealWordBound C
  by_contra hn
  have hh := evalBracketWord_eq_zero_of_depth (M.coneMixedVector C)
    (M.coneIdealWordBound_zero C) (FreeMagma.of w)
    (by simpa only [bracketWordDepth] using Nat.le_of_not_gt hn)
  exact hw hh

/-- Exchange applies to every original mixed word, even though the ideal
box is built using the nested finite alphabet. -/
theorem coneIdeal_width_le_of_coordinate_ne_zero
    (b₀ : Basis (Fin (finrank ℝ (M.coneWordIdeal C))) ℝ (M.coneWordIdeal C))
    (s : Fin M.letterCount → ℝ) (β : M.ConeIdealBases C)
    (hβ : M.IsMaximizingConeIdealBasis C b₀ s β) (w : M.coneMixedWords C)
    (j : Fin (finrank ℝ (M.coneWordIdeal C)))
    (hj : (WordBasisSelections.basis (M.coneMixedVector C) (M.coneIdealWordList C) β).repr
      (M.coneMixedVector C w) j ≠ 0) :
    bracketWordExponent s w.val.val ≤ M.coneIdealWordCost C s (β.val j) := by
  have hw : M.coneMixedVector C w ≠ 0 := by
    intro hz
    apply hj
    rw [hz, map_zero, Finsupp.zero_apply]
  let z : M.coneIdealWordList C := ⟨FreeMagma.of w, M.coneIdeal_leaf_mem_of_ne_zero C w hw⟩
  let v := wordListCoordinates (M.coneMixedVector C) (M.coneIdealWordList C) b₀
  have hc : columnCoordinates v β.val z j ≠ 0 := by
    rw [columnCoordinates_eq_wordBasis_repr]
    exact hj
  have hh := weight_le_of_nonzero_coordinate v
    (fun z : M.coneIdealWordList C => M.coneIdealWordCost C s z) β.val hβ z j
    (columnCoordinates v β.val z) (columnCoordinates_repr v β.val hβ.1 z) hc
  simpa only [z, coneIdealWordCost, bracketWordExponent_of] using hh

end CartanWordModel
end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_ConeAdaptedMaximalBasis
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The ideal and ambient boxes have the same maximal width exponent -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule Set
open scoped BigOperators

variable {L : Type} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {H : LieSubalgebra ℝ L} [H.IsCartanSubalgebra] (M : CartanWordModel H)
  (C : Set (H →ₗ[ℝ] ℝ))

/-- Completing a maximal mixed-word ideal basis by pure quotient words
gives a maximal ambient word basis, with exactly the same total width. -/
theorem exists_cone_adapted_maximal_basis_data
    (bN : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (bI : Basis (Fin (finrank ℝ (M.coneWordIdeal C))) ℝ (M.coneWordIdeal C))
    (s : Fin M.letterCount → ℝ) (hs : ∀ i, 0 ≤ s i)
    (hzero : ∀ i, (M.weight i : H →ₗ[ℝ] ℝ) ∈ C → s i = 0)
    (β : M.ConeIdealBases C) (hβ : M.IsMaximizingConeIdealBasis C bI s β) :
    ∃ (bQ : Basis (Fin (finrank ℝ (cartanRootIdeal H ⧸ (M.coneWordIdeal C).toSubmodule)))
        ℝ (cartanRootIdeal H ⧸ (M.coneWordIdeal C).toSubmodule))
      (q : Fin (finrank ℝ (cartanRootIdeal H ⧸ (M.coneWordIdeal C).toSubmodule)) →
        FreeMagma (Fin M.letterCount)),
      (∀ j, ¬IsMixedWord (fun i => (M.weight i : H →ₗ[ℝ] ℝ) ∉ C) (q j)) ∧
      ∃ hq : ∀ j, (M.coneWordIdeal C).toSubmodule.mkQ (evalBracketWord M.letter (q j)) = bQ j,
      ∃ (e : (Fin (finrank ℝ (M.coneWordIdeal C)) ⊕
        Fin (finrank ℝ (cartanRootIdeal H ⧸ (M.coneWordIdeal C).toSubmodule))) ≃
          Fin (finrank ℝ (cartanRootIdeal H))) (γ : M.Bases),
      WordBasisSelections.basis M.letter M.wordList γ =
        (basisWithQuotientLifts (M.coneWordIdeal C).toSubmodule
          (WordBasisSelections.basis (M.coneMixedVector C) (M.coneIdealWordList C) β)
          bQ (fun j => evalBracketWord M.letter (q j)) hq).reindex e ∧
      (∀ k, bracketWordExponent s (γ.val k) =
        Sum.elim (fun j => M.coneIdealWordCost C s (β.val j)) (fun _ => 0) (e.symm k)) ∧
      IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList bN)
        (fun w => bracketWordExponent s w) γ.val ∧
      columnBasisWeight (fun w : M.wordList => bracketWordExponent s w) γ.val =
        columnBasisWeight (fun w : M.coneIdealWordList C => M.coneIdealWordCost C s w) β.val := by
  classical
  let U := (M.coneWordIdeal C).toSubmodule
  let b := WordBasisSelections.basis (M.coneMixedVector C) (M.coneIdealWordList C) β
  have hquot : ∃ (bQ : Basis (Fin (finrank ℝ (cartanRootIdeal H ⧸ U)))
      ℝ (cartanRootIdeal H ⧸ U))
      (q : Fin (finrank ℝ (cartanRootIdeal H ⧸ U)) → FreeMagma (Fin M.letterCount)),
      (∀ j, ¬IsMixedWord (fun i => (M.weight i : H →ₗ[ℝ] ℝ) ∉ C) (q j)) ∧
      (∀ j, U.mkQ (evalBracketWord M.letter (q j)) = bQ j) :=
    exists_pure_quotient_word_basis M.letter
      (fun i => (M.weight i : H →ₗ[ℝ] ℝ) ∉ C) M.generates
  obtain ⟨bQ, q, hpure, hq⟩ := hquot
  let W := Fin (finrank ℝ (M.coneWordIdeal C)) ⊕ Fin (finrank ℝ (cartanRootIdeal H ⧸ U))
  let B : Basis W ℝ (cartanRootIdeal H) :=
    basisWithQuotientLifts U b bQ (fun j => evalBracketWord M.letter (q j)) hq
  let words : W → FreeMagma (Fin M.letterCount) :=
    Sum.elim (fun j => M.coneOriginalWord C (β.val j)) q
  have heval (k : W) : evalBracketWord M.letter (words k) = B k := by
    cases k with
    | inl j =>
      change evalBracketWord M.letter (M.coneOriginalWord C (β.val j)) = _
      rw [M.coneOriginalWord_eval]
      rw [show B (Sum.inl j) = (b j : cartanRootIdeal H) from
        basisWithQuotientLifts_inl U b bQ _ hq j]
      exact congrArg Subtype.val
        (WordBasisSelections.eval_words (M.coneMixedVector C) (M.coneIdealWordList C) β j)
    | inr j => exact (basisWithQuotientLifts_inr U b bQ _ hq j).symm
  have hmem (k : W) : words k ∈ M.wordList :=
    M.mem_wordList_of_eval_ne_zero _ (fun hz => B.ne_zero k ((heval k).symm.trans hz))
  let e : W ≃ Fin (finrank ℝ (cartanRootIdeal H)) :=
    Fintype.equivFinOfCardEq (Module.finrank_eq_card_basis B).symm
  let γ : M.Bases := ⟨fun k => ⟨words (e.symm k), hmem (e.symm k)⟩,
    B.reindex e, fun k => (heval (e.symm k)).trans (B.reindex_apply e k).symm⟩
  have hγ : WordBasisSelections.basis M.letter M.wordList γ = B.reindex e := by
    apply Basis.eq_of_apply_eq
    intro k
    exact (WordBasisSelections.eval_words M.letter M.wordList γ k).symm.trans
      ((heval (e.symm k)).trans (B.reindex_apply e k).symm)
  have hqzero (j) : bracketWordExponent s (q j) = 0 :=
    bracketWordExponent_eq_zero_of_pure s _ (fun i hi => hzero i (not_not.mp hi)) _ (hpure j)
  have hsupport (w : M.wordList) (k : Fin (finrank ℝ (cartanRootIdeal H)))
      (hk : (WordBasisSelections.basis M.letter M.wordList γ).repr
        (evalBracketWord M.letter w) k ≠ 0) :
      bracketWordExponent s w ≤ bracketWordExponent s (γ.val k) := by
    rw [hγ, Basis.repr_reindex_apply] at hk
    by_cases hw : IsMixedWord (fun i => (M.weight i : H →ₗ[ℝ] ℝ) ∉ C) w
    · let wm : M.coneMixedWords C := ⟨w, hw⟩
      cases he : e.symm k with
      | inl i =>
        rw [he] at hk
        change B.repr (M.coneMixedVector C wm : cartanRootIdeal H) (Sum.inl i) ≠ 0 at hk
        have hki : b.repr (M.coneMixedVector C wm) i ≠ 0 := by
          simpa only [B, ← basisWithQuotientLifts_repr_inl U b bQ _ hq
            (M.coneMixedVector C wm) i] using hk
        have hle := M.coneIdeal_width_le_of_coordinate_ne_zero C bI s β hβ wm i hki
        change bracketWordExponent s w ≤ bracketWordExponent s (words (e.symm k))
        rw [he]
        exact hle.trans_eq (M.coneIdealWordCost_eq_original C s (β.val i))
      | inr i =>
        rw [he] at hk
        have hz : U.mkQ (evalBracketWord M.letter w) = 0 :=
          (Submodule.Quotient.mk_eq_zero U).mpr (eval_mixed_mem_span M.letter _ hw)
        have hc := basisWithQuotientLifts_repr_inr U b bQ _ hq (evalBracketWord M.letter w) i
        change B.repr (evalBracketWord M.letter w) (Sum.inr i) = _ at hc
        rw [hc, hz, map_zero, Finsupp.zero_apply] at hk
        exact (hk rfl).elim
    · rw [bracketWordExponent_eq_zero_of_pure s _
        (fun i hi => hzero i (not_not.mp hi)) w hw]
      exact bracketWordExponent_nonneg s hs (γ.val k)
  have hcost (k) : bracketWordExponent s (γ.val k) =
      Sum.elim (fun j => M.coneIdealWordCost C s (β.val j)) (fun _ => 0) (e.symm k) := by
    change bracketWordExponent s (words (e.symm k)) = _
    cases he : e.symm k with
    | inl j => exact (M.coneIdealWordCost_eq_original C s (β.val j)).symm
    | inr j => exact hqzero j
  refine ⟨bQ, q, hpure, hq, e, γ, hγ, hcost, ?_, ?_⟩
  · apply maximizingColumnBasis_of_coordinate_support _ _ _
      (wordBasis_det_ne_zero M.letter M.wordList bN γ)
    intro w k hk
    rw [columnCoordinates_eq_wordBasis_repr M.letter M.wordList bN γ w] at hk
    exact hsupport w k hk
  · change (∑ k, bracketWordExponent s (words (e.symm k))) = _
    calc
      _ = ∑ w : W, bracketWordExponent s (words w) :=
        Equiv.sum_comp e.symm (fun w => bracketWordExponent s (words w))
      _ = _ := by
        rw [Fintype.sum_sum_type]
        simp only [words, Sum.elim_inl, Sum.elim_inr, hqzero, Finset.sum_const_zero,
          add_zero, ← M.coneIdealWordCost_eq_original]
        rfl

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_ConeIdealStrictWidth
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Strict width absorbs the inside-letter conjugation flow

The flow here is the finite exponential of the actual restricted adjoint.
No box inclusion is an input. A positive width gap absorbs its polynomial
growth uniformly over every point of the smaller box.
-/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module Filter
open scoped Topology

variable {L : Type} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {H : LieSubalgebra ℝ L} [H.IsCartanSubalgebra] (M : CartanWordModel H)
  (C : Set (H →ₗ[ℝ] ℝ))

theorem exists_positive_coneIdeal_width (s : Fin M.letterCount → ℝ)
    (hs : ∀ i, 0 ≤ s i)
    (hpos : ∀ i, (M.weight i : H →ₗ[ℝ] ℝ) ∉ C → 0 < s i) :
    ∃ lo : ℝ, 0 < lo ∧ ∀ w : M.coneIdealWordList C, lo ≤ M.coneIdealWordCost C s w := by
  classical
  cases isEmpty_or_nonempty (M.coneIdealWordList C) with
  | inl he => exact ⟨1, zero_lt_one, fun w => isEmptyElim w⟩
  | inr he =>
    obtain ⟨w, _, hw⟩ := Finset.exists_min_image Finset.univ
      (fun w : M.coneIdealWordList C => M.coneIdealWordCost C s w) Finset.univ_nonempty
    exact ⟨_, M.coneIdealWordCost_pos C s hs hpos w, fun v => hw v (Finset.mem_univ v)⟩

end PolycyclicRecognition.CartanWordModel

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

end PolycyclicRecognition

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

theorem exponentialRescaleBasis_reindex {V I J : Type} [LieRing V] [LieAlgebra ℝ V]
    (b : Basis I ℝ V) (cost : I → ℝ) (e : I ≃ J) (r : ℝ) :
    exponentialRescaleBasis (b.reindex e) (fun j => cost (e.symm j)) r =
      (exponentialRescaleBasis b cost r).reindex e := by
  apply Basis.eq_of_apply_eq
  intro j
  simp only [exponentialRescaleBasis, Basis.unitsSMul_apply, Basis.reindex_apply]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_ConeAdaptedPathBasis
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # One adapted basis for path lifting and ideal bridge absorption

The maximizing ambient word basis and the ideal/quotient basis describe
exactly the same boxes. Keeping this identification prevents a change of
coordinates from introducing an extra exponential error in the bridge.
-/

noncomputable section
namespace PolycyclicRecognition

open Module LieModule Set

variable {V I J : Type} [LieRing V] [LieAlgebra ℝ V] [Fintype I] [Fintype J]

/-- Reindexing a finite basis preserves its coordinate supremum norm. -/
theorem norm_basis_equivFun_reindex (b : Basis I ℝ V) (e : I ≃ J) (v : V) :
    ‖(b.reindex e).equivFun v‖ = ‖b.equivFun v‖ := by
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
    intro j
    simpa only [Basis.equivFun_apply, Basis.repr_reindex_apply] using
      norm_le_pi_norm (b.equivFun v) (e.symm j)
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
    intro i
    simpa only [Basis.equivFun_apply, Basis.repr_reindex_apply,
      Equiv.symm_apply_apply] using
      norm_le_pi_norm ((b.reindex e).equivFun v) (e i)

/-- Consequently the actual exponential coordinate boxes are unchanged. -/
theorem exponentialCoordinateBox_reindex {N : Type} (Exp : V → N)
    (b : Basis I ℝ V) (e : I ≃ J) (R : ℝ) :
    exponentialCoordinateBox Exp (b.reindex e) R = exponentialCoordinateBox Exp b R := by
  ext n
  simp only [exponentialCoordinateBox, norm_basis_equivFun_reindex]

namespace CartanWordModel

variable {L W : Type} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {H : LieSubalgebra ℝ L} [H.IsCartanSubalgebra] (M : CartanWordModel H)
  (C : Set (H →ₗ[ℝ] ℝ))
  {a : ℕ} (T : TriangularAdjoint L a)
  (hunimod : ∀ x : L, LinearMap.trace ℝ L (LieAlgebra.ad ℝ L x) = 0)
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)

/-- The same ideal-maximizing choice supplies an ambient path box, an exact
ideal/quotient coordinate identification and a uniform bracket bound. -/
theorem exists_cone_adapted_path_basis
    (bN : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (bI : Basis (Fin (finrank ℝ (M.coneWordIdeal C))) ℝ (M.coneWordIdeal C))
    (E : Set W)
    (hs : ∀ i, 0 ≤ (M.supportIn T hunimod eW).weightSupport E i)
    (hzero : ∀ i, (M.weight i : H →ₗ[ℝ] ℝ) ∈ C →
      (M.supportIn T hunimod eW).weightSupport E i = 0)
    (β : M.ConeIdealBases C)
    (hβ : M.IsMaximizingConeIdealBasis C bI
      ((M.supportIn T hunimod eW).weightSupport E) β) :
    ∃ (bQ : Basis (Fin (finrank ℝ (cartanRootIdeal H ⧸ (M.coneWordIdeal C).toSubmodule)))
        ℝ (cartanRootIdeal H ⧸ (M.coneWordIdeal C).toSubmodule))
      (lift : Fin (finrank ℝ (cartanRootIdeal H ⧸ (M.coneWordIdeal C).toSubmodule)) →
        cartanRootIdeal H),
      ∃ hlift : ∀ j, (M.coneWordIdeal C).toSubmodule.mkQ (lift j) = bQ j,
      ∃ γ : M.Bases,
        IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList bN)
          (M.boxCost T hunimod eW E) γ.val ∧
        (∀ {N : Type} (Exp : cartanRootIdeal H → N) (r R : ℝ),
          M.groupBox T hunimod eW Exp E γ r R =
          exponentialCoordinateBox Exp
            (exponentialRescaleBasis
              (basisWithQuotientLifts (M.coneWordIdeal C).toSubmodule
                (WordBasisSelections.basis (M.coneMixedVector C) (M.coneIdealWordList C) β)
                bQ lift hlift)
              (Sum.elim
                (fun j => M.coneIdealWordCost C
                  ((M.supportIn T hunimod eW).weightSupport E) (β.val j))
                (fun _ => 0)) r) R) ∧
        ∃ K : ℝ, 0 ≤ K ∧ ∀ r : ℝ, 0 ≤ r →
          let B := exponentialRescaleBasis
            (basisWithQuotientLifts (M.coneWordIdeal C).toSubmodule
              (WordBasisSelections.basis (M.coneMixedVector C) (M.coneIdealWordList C) β)
              bQ lift hlift)
            (Sum.elim
              (fun j => M.coneIdealWordCost C
                ((M.supportIn T hunimod eW).weightSupport E) (β.val j))
              (fun _ => 0)) r
          ∀ i j k, |B.repr ⁅B i, B j⁆ k| ≤ K := by
  obtain ⟨bQ, q, _hpure, hq, e, γ, hγ, hcost, hmax, _hsum⟩ :=
    M.exists_cone_adapted_maximal_basis_data C bN bI
      ((M.supportIn T hunimod eW).weightSupport E) hs hzero β hβ
  obtain ⟨K, hK, hbound⟩ := exists_uniform_rescaled_structureConstant_bound
    M.letter M.bound_zero bN
  let B := basisWithQuotientLifts (M.coneWordIdeal C).toSubmodule
    (WordBasisSelections.basis (M.coneMixedVector C) (M.coneIdealWordList C) β)
    bQ (fun j => evalBracketWord M.letter (q j)) hq
  let cost : (Fin (finrank ℝ (M.coneWordIdeal C)) ⊕
      Fin (finrank ℝ (cartanRootIdeal H ⧸ (M.coneWordIdeal C).toSubmodule))) → ℝ := Sum.elim
    (fun j => M.coneIdealWordCost C
      ((M.supportIn T hunimod eW).weightSupport E) (β.val j)) (fun _ => (0 : ℝ))
  have heq (r : ℝ) : M.boxBasis T hunimod eW E γ r =
      (exponentialRescaleBasis B cost r).reindex e := by
    change exponentialRescaleBasis (WordBasisSelections.basis M.letter M.wordList γ)
      (fun j => bracketWordExponent ((M.supportIn T hunimod eW).weightSupport E)
        (γ.val j)) r = _
    rw [hγ]
    simp_rw [hcost]
    exact exponentialRescaleBasis_reindex B cost e r
  refine ⟨bQ, (fun j => evalBracketWord M.letter (q j)), hq, γ, hmax, ?_, K, hK, ?_⟩
  · intro N Exp r R
    change exponentialCoordinateBox Exp (M.boxBasis T hunimod eW E γ r) R = _
    rw [heq, exponentialCoordinateBox_reindex]
  · intro r hr
    dsimp only
    intro i j k
    have hh := hbound ((M.supportIn T hunimod eW).weightSupport E) γ hmax r hr
      (e i) (e j) (e k)
    change |(M.boxBasis T hunimod eW E γ r).repr
      ⁅M.boxBasis T hunimod eW E γ r (e i), M.boxBasis T hunimod eW E γ r (e j)⁆
        (e k)| ≤ K at hh
    rw [heq] at hh
    simpa only [Basis.reindex_apply, Basis.repr_reindex_apply,
      Equiv.symm_apply_apply] using hh

end CartanWordModel
end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_ExponentialQuotientSection
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The selected pure-word section in actual exponential coordinates -/

noncomputable section
namespace PolycyclicRecognition

open Module

variable {V J EN EQ N Q : Type} [LieRing V] [LieAlgebra ℝ V] [Fintype J]
  [AddCommGroup EN] [Module ℝ EN] [TopologicalSpace EN]
  [IsTopologicalAddGroup EN] [ContinuousSMul ℝ EN]
  [AddCommGroup EQ] [Module ℝ EQ] [TopologicalSpace EQ] [T2Space EQ]
  [IsTopologicalAddGroup EQ] [ContinuousSMul ℝ EQ] [FiniteDimensional ℝ EQ]
  [TopologicalSpace N] [TopologicalSpace Q] [Group N] [Group Q]
  (U : LieIdeal ℝ V) (bQ : Basis J ℝ (V ⧸ U.toSubmodule))
  (lift : J → V) (hlift : ∀ j, U.toSubmodule.mkQ (lift j) = bQ j)
  (eN : V ≃ₗ[ℝ] EN) (eQ : (V ⧸ U.toSubmodule) ≃ₗ[ℝ] EQ)
  (chartN : EN ≃ₜ N) (chartQ : EQ ≃ₜ Q)

include hlift in
omit [Fintype J] in
/-- Factoring off the selected pure-word section gives exactly the kernel
residual used by quotient integration. -/
theorem exponentialQuotientSection_residual (π : N →* Q)
    (hπ : ∀ v, π (chartN (eN v)) = chartQ (eQ (U.toSubmodule.mkQ v)))
    (hzeroQ : chartQ (eQ 0) = 1)
    (u : U) (q : V ⧸ U.toSubmodule) :
    ((quotientSectionResidual π
      (exponentialQuotientSection U bQ lift eN eQ chartN chartQ)
      (exponentialQuotientSection_rightInverse U bQ lift hlift eN eQ chartN chartQ π hπ)
      (chartN (eN (u : V)) * chartN (eN (quotientLinearSection U bQ lift q)))) : N) =
      chartN (eN (u : V)) := by
  have hu : π (chartN (eN (u : V))) = 1 := by
    rw [hπ]
    have hz : U.toSubmodule.mkQ (u : V) = 0 :=
      (Submodule.Quotient.mk_eq_zero U.toSubmodule).mpr u.property
    rw [hz, hzeroQ]
  have hq : π (chartN (eN (quotientLinearSection U bQ lift q))) = chartQ (eQ q) := by
    rw [hπ, quotientLinearSection_rightInverse U bQ lift hlift]
  change (chartN (eN (u : V)) * chartN (eN (quotientLinearSection U bQ lift q))) *
    (exponentialQuotientSection U bQ lift eN eQ chartN chartQ
      (π (chartN (eN (u : V)) * chartN (eN (quotientLinearSection U bQ lift q)))))⁻¹ = _
  rw [map_mul, hu, hq, one_mul, exponentialQuotientSection_apply, mul_inv_cancel_right]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_ProbeSectionRestrictions
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The two probe restrictions in the same section coordinates

The first path controls the quotient orbit point in the base frame. The
absorbed bridge controls the ideal residual in the tile-anchor frame.
These restrictions apply simultaneously to each point of the right cell.
-/

noncomputable section
namespace PolycyclicRecognition

open Module Set
open scoped Pointwise

variable {V J EN EQ N Q D G : Type} [LieRing V] [LieAlgebra ℝ V] [Fintype J]
  [AddCommGroup EN] [Module ℝ EN] [TopologicalSpace EN]
  [IsTopologicalAddGroup EN] [ContinuousSMul ℝ EN]
  [AddCommGroup EQ] [Module ℝ EQ] [TopologicalSpace EQ] [T2Space EQ]
  [IsTopologicalAddGroup EQ] [ContinuousSMul ℝ EQ] [FiniteDimensional ℝ EQ]
  [TopologicalSpace N] [TopologicalSpace Q] [Group N] [Group Q] [Group D] [Group G]
  (U : LieIdeal ℝ V) (bQ : Basis J ℝ (V ⧸ U.toSubmodule))
  (lift : J → V) (hlift : ∀ j, U.toSubmodule.mkQ (lift j) = bQ j)
  (eN : V ≃ₗ[ℝ] EN) (eQ : (V ⧸ U.toSubmodule) ≃ₗ[ℝ] EQ)
  (chartN : EN ≃ₜ N) (chartQ : EQ ≃ₜ Q)
  (π : N →* Q) (hπ : ∀ v, π (chartN (eN v)) = chartQ (eQ (U.toSubmodule.mkQ v)))

omit [Fintype J] in
/-- An actual ideal-times-section factorization places its residual in the
intrinsic kernel region. This is the ideal restriction used in packing. -/
theorem exponential_section_residual_mem
    (hzeroQ : chartQ (eQ 0) = 1) (I : Set U) {n : N}
    (hn : ∃ i ∈ I, ∃ q : V ⧸ U.toSubmodule,
      n = chartN (eN (i : V)) * chartN (eN (quotientLinearSection U bQ lift q))) :
    quotientSectionResidual π
      (exponentialQuotientSection U bQ lift eN eQ chartN chartQ)
      (exponentialQuotientSection_rightInverse U bQ lift hlift eN eQ chartN chartQ π hπ) n ∈
        exponentialIdealKernelRegion U π (chartN ∘ eN) I := by
  obtain ⟨i, hi, q, rfl⟩ := hn
  exact ⟨i, hi,
    exponentialQuotientSection_residual U bQ lift hlift eN eQ chartN chartQ π hπ hzeroQ i q⟩

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_SequenceQuotientVolume
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_countable _root_.OAI.PolycyclicRecognition.finitelyGeneratedSubgroupIndex_countable _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.chartExponentialFlow_zero _root_.OAI.PolycyclicRecognition.derivationSemidirectHom_apply _root_.OAI.PolycyclicRecognition.exponentialHomOfDynkin_apply_exp _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.integrateNilpotentLieEquiv_apply_exp _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Quotient log boxes in the chosen Haar normalization

The quotient Jacobian and the packing argument use the same Haar measure.
Uniqueness of Haar measure transfers the exponential cube formula to that
normalization, including along an arbitrary sequence of profile scales.
-/

noncomputable section
namespace PolycyclicRecognition

open Module MeasureTheory Filter
open scoped Manifold Topology ENNReal NNReal

variable {E Q L : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace Q] [ChartedSpace E Q] [Group Q]
  [LieGroup (𝓘(ℝ, E)) ⊤ Q] [T2Space Q] [SimplyConnectedSpace Q]
  [MeasurableSpace Q] [BorelSpace Q] [LieRing L] [LieAlgebra ℝ L]

/-- The logarithmic cube formula for any actual Lie-algebra model and any
Haar normalization. The constant is independent of the cube radius. -/
theorem haar_model_cube_volume
    (haar : NilpotentExponentialHaarInput E Q)
    (Exp : GroupLieAlgebra (𝓘(ℝ, E)) Q → Q) (hExp : IsGroupExponential Exp)
    (e : L ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, E)) Q) (hnil : LieRing.IsNilpotent L)
    {n : ℕ} (b : Basis (Fin n) ℝ L) (μ : Measure Q) [μ.IsHaarMeasure] :
    ∃ c : ℝ≥0, 0 < c ∧ ∀ R : ℝ, 0 ≤ R →
      μ (exponentialCoordinateBox (Exp ∘ e) b R) =
        (c : ℝ≥0∞) * ENNReal.ofReal (2 * R) ^ n := by
  let : IsTopologicalGroup Q := topologicalGroup_of_lieGroup (𝓘(ℝ, E)) ⊤
  obtain ⟨chart, ν, _, hν, hvol⟩ := exists_haar_exponential_cube_volume haar Exp hExp
    (e.nilpotent_iff_equiv_nilpotent.mp hnil) (b.map e.toLinearEquiv)
  let coordinates : (Fin n → ℝ) ≃ₜ Q :=
    (b.map e.toLinearEquiv).equivFun.symm.toContinuousLinearEquiv.toHomeomorph.trans chart
  let : LocallyCompactSpace Q := coordinates.symm.isOpenEmbedding.locallyCompactSpace
  let : SecondCountableTopology Q := coordinates.symm.secondCountableTopology
  have : ν.IsHaarMeasure := hν
  have hbox (R : ℝ) : exponentialCoordinateBox (Exp ∘ e) b R =
      exponentialCoordinateBox Exp (b.map e.toLinearEquiv) R := by
    ext q
    constructor
    · rintro ⟨v, rfl, hv⟩
      refine ⟨e v, rfl, ?_⟩
      change ‖(b.map e.toLinearEquiv).equivFun (e.toLinearEquiv v)‖ ≤ R
      simpa only [Basis.map_equivFun, LinearEquiv.trans_apply,
        LinearEquiv.symm_apply_apply] using hv
    · rintro ⟨v, rfl, hv⟩
      refine ⟨e.symm v, by simp, ?_⟩
      change ‖b.equivFun (e.toLinearEquiv.symm v)‖ ≤ R
      simpa only [Basis.map_equivFun, LinearEquiv.trans_apply] using hv
  refine ⟨Measure.haarScalarFactor μ ν, Measure.haarScalarFactor_pos_of_isHaarMeasure μ ν,
    ?_⟩
  intro R hR
  rw [hbox]
  conv_lhs => rw [Measure.isMulLeftInvariant_eq_smul μ ν]
  rw [Measure.smul_apply, hvol R hR]
  rfl

/-- Subexponential radii have finite, subexponential Haar volume in the
normalization already used for the quotient action. -/
theorem haar_model_sequence_boxes
    (haar : NilpotentExponentialHaarInput E Q)
    (Exp : GroupLieAlgebra (𝓘(ℝ, E)) Q → Q) (hExp : IsGroupExponential Exp)
    (e : L ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, E)) Q) (hnil : LieRing.IsNilpotent L)
    {n : ℕ} (b : Basis (Fin n) ℝ L) (μ : Measure Q) [μ.IsHaarMeasure]
    (scale R : ℕ → ℝ) (hs : Tendsto scale atTop atTop)
    (hR0 : ∀ j, 0 ≤ R j) (hR : HasSubexponentialUpperBoundSeq scale R) :
    (∀ j, μ (exponentialCoordinateBox (Exp ∘ e) b (R j)) ≠ ⊤) ∧
      HasSubexponentialUpperBoundSeq scale (fun j =>
        (μ (exponentialCoordinateBox (Exp ∘ e) b (R j))).toReal) := by
  obtain ⟨c, _, hvol⟩ := haar_model_cube_volume haar Exp hExp e hnil b μ
  have htwo := (sequence_subexponential_upper_const hs 2).mul hR
    (Eventually.of_forall (fun _ => by norm_num))
  have hp := htwo.pow hs
    (Eventually.of_forall (fun j => mul_nonneg (by norm_num) (hR0 j))) n
  have hc := (sequence_subexponential_upper_const hs (c : ℝ)).mul hp
    (Eventually.of_forall (fun _ => c.coe_nonneg))
  constructor
  · intro j
    rw [hvol _ (hR0 j)]
    exact ENNReal.mul_ne_top ENNReal.coe_ne_top
      (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
  · intro ε hε
    filter_upwards [hc ε hε] with j hj
    rw [hvol _ (hR0 j), ENNReal.toReal_mul, ENNReal.coe_toReal,
      ENNReal.toReal_pow, ENNReal.toReal_ofReal
        (mul_nonneg (by norm_num) (hR0 j))]
    exact hj

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
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanLogRegionVolume
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The Cartan log restriction has subexponential Haar volume -/

noncomputable section
namespace PolycyclicRecognition

open Module LieModule MeasureTheory Set Filter
open scoped Manifold Topology

variable {L : Type} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  (H : LieSubalgebra ℝ L) [H.IsCartanSubalgebra]
  {E D : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace D] [ChartedSpace E D] [Group D]
  [LieGroup (𝓘(ℝ, E)) ⊤ D] [T2Space D] [SimplyConnectedSpace D]
  [MeasurableSpace D] [BorelSpace D]

set_option maxHeartbeats 1000000 in
/-- The coordinate restriction produced by the actual path lifts is an
exponential box. Its volume is finite and subexponential in any Haar
normalization, with no separate volume hypothesis. -/
theorem cartan_log_regions_volume
    (haar : NilpotentExponentialHaarInput E D)
    (Exp : GroupLieAlgebra (𝓘(ℝ, E)) D → D) (hExp : IsGroupExponential Exp)
    (e : H ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, E)) D) (hbij : Function.Bijective Exp)
    (μ : Measure D) [μ.IsHaarMeasure]
    (scale R : ℕ → ℝ) (hs : Tendsto scale atTop atTop)
    (hR0 : ∀ n, 0 ≤ R n) (hR : HasSubexponentialUpperBoundSeq scale R) :
    let B := fun n => {d : D | ‖(finBasis ℝ H).equivFun (cartanLog H e Exp hbij d)‖ ≤ R n}
    (∀ n, μ (B n) ≠ ⊤) ∧
      HasSubexponentialUpperBoundSeq scale (fun n => (μ (B n)).toReal) := by
  have hnil : LieRing.IsNilpotent H := by infer_instance
  have hbox (n : ℕ) :
      {d : D | ‖(finBasis ℝ H).equivFun (cartanLog H e Exp hbij d)‖ ≤ R n} =
        exponentialCoordinateBox (Exp ∘ e) (finBasis ℝ H) (R n) := by
    ext d
    constructor
    · intro hd
      exact ⟨cartanLog H e Exp hbij d, exp_cartanLog H e Exp hbij d, hd⟩
    · rintro ⟨v, rfl, hv⟩
      change ‖(finBasis ℝ H).equivFun (cartanLog H e Exp hbij (Exp (e v)))‖ ≤ R n
      rw [cartanLog_exp]
      exact hv
  simpa only [hbox] using
    haar_model_sequence_boxes haar Exp hExp e hnil (finBasis ℝ H) μ scale R hs hR0 hR

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanFactorLogVolume
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The log-region volume theorem for the actual Cartan factor -/

noncomputable section
namespace PolycyclicRecognition

open Module MeasureTheory Set Filter
open scoped Manifold Topology

variable {EG G : Type} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G]
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  {ExpG : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H ExpG)

set_option maxHeartbeats 1000000 in
theorem CartanFactorModel.log_regions_volume
    (haar : NilpotentExponentialHaarInput F.D.modelSpace F.D.carrier)
    (hbij : Function.Bijective F.ExpD)
    (μ : Measure F.D.carrier) [μ.IsHaarMeasure]
    (scale R : ℕ → ℝ) (hs : Tendsto scale atTop atTop)
    (hR0 : ∀ n, 0 ≤ R n) (hR : HasSubexponentialUpperBoundSeq scale R) :
    let B := fun n => {d : F.D.carrier |
      ‖(finBasis ℝ H).equivFun (cartanLog H F.D.equiv F.ExpD hbij d)‖ ≤ R n}
    (∀ n, μ (B n) ≠ ⊤) ∧
      HasSubexponentialUpperBoundSeq scale (fun n => (μ (B n)).toReal) :=
  cartan_log_regions_volume (L := GroupLieAlgebra (𝓘(ℝ, EG)) G)
    (E := F.D.modelSpace) (D := F.D.carrier) H haar F.ExpD F.isExpD
    F.D.equiv hbij μ scale R hs hR0 hR

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_WeightedHaarVolume
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_countable _root_.OAI.PolycyclicRecognition.finitelyGeneratedSubgroupIndex_countable _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.CartanFactorModel.realScaleProfile_apply _root_.OAI.PolycyclicRecognition.chartExponentialFlow_zero _root_.OAI.PolycyclicRecognition.derivationSemidirectHom_apply _root_.OAI.PolycyclicRecognition.exponentialHomOfDynkin_apply_exp _root_.OAI.PolycyclicRecognition.exponentialRescaleBasis_zero _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.integrateNilpotentLieEquiv_apply_exp _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Weighted ideal-box volumes in a chosen Haar normalization -/

noncomputable section
namespace PolycyclicRecognition

open Module MeasureTheory Filter Set
open scoped Manifold Topology ENNReal NNReal BigOperators

variable {L : Type} [LieRing L] [LieAlgebra ℝ L]

/-- The basis rescaling contributes exactly the sum of its coordinate
weights to the exponential volume rate. -/
theorem det_exponentialRescaleBasis {n : ℕ} (b : Basis (Fin n) ℝ L)
    (cost : Fin n → ℝ) (r : ℝ) :
    (b.toMatrix (exponentialRescaleBasis b cost r)).det = Real.exp (r * ∑ j, cost j) := by
  have hm : b.toMatrix (exponentialRescaleBasis b cost r) =
      Matrix.of (fun i j => Real.exp (r * cost j) * b.toMatrix b i j) := by
    ext i j
    simp only [Basis.toMatrix_apply, exponentialRescaleBasis, Basis.unitsSMul_apply,
      Units.smul_def, Units.val_mk0, map_smul, Finsupp.smul_apply, smul_eq_mul,
      Matrix.of_apply]
  rw [hm, Matrix.det_mul_row, ← Real.exp_sum]
  simp only [Basis.toMatrix_self, Matrix.det_one, mul_one]
  rw [Finset.mul_sum]

variable {E G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace G] [ChartedSpace E G] [Group G]
  [LieGroup (𝓘(ℝ, E)) ⊤ G] [T2Space G] [SimplyConnectedSpace G]
  [MeasurableSpace G] [BorelSpace G]

/-- The same Haar normalization can be used for section coordinates and
weighted ideal boxes. The constant is fixed for all scales and radii. -/
theorem haar_model_weighted_box_volume
    (haar : NilpotentExponentialHaarInput E G)
    (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G) (hExp : IsGroupExponential Exp)
    (e : L ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, E)) G) (hnil : LieRing.IsNilpotent L)
    {n : ℕ} (b : Basis (Fin n) ℝ L) (cost : Fin n → ℝ)
    (μ : Measure G) [μ.IsHaarMeasure] :
    ∃ c : ℝ≥0, 0 < c ∧ ∀ r R : ℝ, 0 ≤ R →
      μ (exponentialCoordinateBox (Exp ∘ e) (exponentialRescaleBasis b cost r) R) =
        (c : ℝ≥0∞) * ENNReal.ofReal (Real.exp (r * ∑ j, cost j)) *
          ENNReal.ofReal (2 * R) ^ n := by
  let _ : IsTopologicalGroup G := topologicalGroup_of_lieGroup (𝓘(ℝ, E)) ⊤
  obtain ⟨⟨chart, hchart⟩, hhaar⟩ := haar.2 Exp hExp (e.nilpotent_iff_equiv_nilpotent.mp hnil)
  let ν := Measure.map ((Exp ∘ e) ∘ b.equivFun.symm) volume
  have hν : ν.IsHaarMeasure := by
    have he : ((Exp ∘ e) ∘ b.equivFun.symm) = Exp ∘ (b.map e.toLinearEquiv).equivFun.symm := by
      funext z
      rw [Basis.map_equivFun]
      rfl
    dsimp only [ν]
    rw [he]
    exact hhaar n _
  let _ : ν.IsHaarMeasure := hν
  let coordinates := (b.map e.toLinearEquiv).equivFun.symm.toContinuousLinearEquiv.toHomeomorph.trans chart
  let _ : LocallyCompactSpace G := coordinates.symm.isOpenEmbedding.locallyCompactSpace
  let _ : SecondCountableTopology G := coordinates.symm.secondCountableTopology
  refine ⟨Measure.haarScalarFactor μ ν, Measure.haarScalarFactor_pos_of_isHaarMeasure μ ν, ?_⟩
  intro r R hR
  conv_lhs => rw [Measure.isMulLeftInvariant_eq_smul μ ν]
  rw [Measure.smul_apply]
  have hvol : ν (exponentialCoordinateBox (Exp ∘ e) (exponentialRescaleBasis b cost r) R) =
      ENNReal.ofReal (Real.exp (r * ∑ j, cost j)) * ENNReal.ofReal (2 * R) ^ n := by
    rw [exponentialCoordinateBox_eq_cube_image _ _ R hR]
    rw [exponential_basis_subset_measure e Exp chart hchart b,
      det_exponentialRescaleBasis, abs_of_pos (Real.exp_pos _), Real.volume_Icc_pi]
    simp only [sub_neg_eq_add, ← two_mul, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [hvol]
  exact mul_assoc _ _ _ |>.symm

/-- Only the sum of the ideal widths contributes to the exponential rate;
the radius loss has a common subexponential volume bound. -/
theorem haar_model_sequence_weighted_boxes
    (haar : NilpotentExponentialHaarInput E G)
    (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G) (hExp : IsGroupExponential Exp)
    (e : L ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, E)) G) (hnil : LieRing.IsNilpotent L)
    {n : ℕ} (b : Basis (Fin n) ℝ L) (cost : Fin n → ℝ)
    (μ : Measure G) [μ.IsHaarMeasure]
    (scale R : ℕ → ℝ) (hs : Tendsto scale atTop atTop)
    (hR0 : ∀ j, 0 ≤ R j) (hR : HasSubexponentialUpperBoundSeq scale R) :
    ∃ V : ℕ → ℝ, (∀ j, 0 ≤ V j) ∧ HasSubexponentialUpperBoundSeq scale V ∧
      ∀ j, μ (exponentialCoordinateBox (Exp ∘ e)
        (exponentialRescaleBasis b cost (scale j)) (R j)) ≠ ⊤ ∧
        (μ (exponentialCoordinateBox (Exp ∘ e)
          (exponentialRescaleBasis b cost (scale j)) (R j))).toReal =
            V j * Real.exp ((∑ k, cost k) * scale j) := by
  obtain ⟨c, _, hvol⟩ := haar_model_weighted_box_volume haar Exp hExp e hnil b cost μ
  let V := fun j => (c : ℝ) * (2 * R j) ^ n
  have htwo := (sequence_subexponential_upper_const hs 2).mul hR
    (Eventually.of_forall (fun _ => by norm_num))
  have hp := htwo.pow hs (Eventually.of_forall (fun j => mul_nonneg (by norm_num) (hR0 j))) n
  have hV := (sequence_subexponential_upper_const hs (c : ℝ)).mul hp
    (Eventually.of_forall (fun _ => c.coe_nonneg))
  refine ⟨V, fun j => mul_nonneg c.coe_nonneg (pow_nonneg (mul_nonneg (by norm_num) (hR0 j)) _), hV, ?_⟩
  intro j
  rw [hvol _ _ (hR0 j)]
  constructor
  · exact ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.ofReal_ne_top)
      (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
  · rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.coe_toReal,
      ENNReal.toReal_ofReal (Real.exp_pos _).le, ENNReal.toReal_pow,
      ENNReal.toReal_ofReal (mul_nonneg (by norm_num) (hR0 j))]
    dsimp only [V]
    rw [mul_comm (∑ k, cost k) (scale j)]
    ring

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_ProbeKernelVolume
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The ideal restriction has its intrinsic weighted Haar volume -/

noncomputable section
namespace PolycyclicRecognition

open Module MeasureTheory Set Filter
open scoped Manifold Topology ENNReal BigOperators

variable {V I N Q : Type} [LieRing V] [LieAlgebra ℝ V]
  [Group I] [Group N] [Group Q] [TopologicalSpace I] [TopologicalSpace N]
  [IsTopologicalGroup I] [IsTopologicalGroup N]
  (U : LieIdeal ℝ V) (π : N →* Q) (ι : I →* N)
  (hι : Topology.IsClosedEmbedding ι) (hrange : range ι = (π.ker : Set N))
  (ExpI : U → I) (ExpN : V → N) (hcompat : ∀ u : U, ι (ExpI u) = ExpN u)

include hcompat

omit [IsTopologicalGroup I] [IsTopologicalGroup N] in
/-- The ideal region used for the target-cell restriction is the image of
the actual intrinsic ideal set, not a possibly larger preimage region. -/
theorem exponentialIdealKernelRegion_eq_image (A : Set U) :
    exponentialIdealKernelRegion U π ExpN A =
      kernelRealization π ι hι hrange '' (ExpI '' A) := by
  ext n
  constructor
  · rintro ⟨u, hu, hn⟩
    refine ⟨ExpI u, ⟨u, hu, rfl⟩, ?_⟩
    apply Subtype.ext
    change ι (ExpI u) = (n : N)
    exact (hcompat u).trans hn.symm
  · rintro ⟨_, ⟨u, hu, rfl⟩, rfl⟩
    exact ⟨u, hu, (hcompat u)⟩

variable [MeasurableSpace I] [MeasurableSpace N] [BorelSpace I] [BorelSpace N]

omit [IsTopologicalGroup I] [IsTopologicalGroup N] in
/-- Transport through the kernel homeomorphism preserves the exact ideal
volume, for the same kernel measure used by quotient integration. -/
theorem exponentialIdealKernelRegion_measure (μ : Measure I) (A : Set U) :
    (Measure.map (kernelRealization π ι hι hrange) μ)
      (exponentialIdealKernelRegion U π ExpN A) = μ (ExpI '' A) := by
  rw [exponentialIdealKernelRegion_eq_image U π ι hι hrange ExpI ExpN hcompat]
  have he : MeasurableEmbedding (kernelRealization π ι hι hrange : I → π.ker) :=
    (kernelRealization π ι hι hrange).toHomeomorph.measurableEmbedding
  rw [he.map_apply,
    preimage_image_eq _ (kernelRealization π ι hι hrange).injective]

section Weighted

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [ChartedSpace E I] [LieGroup (𝓘(ℝ, E)) ⊤ I]
  [T2Space I] [SimplyConnectedSpace I]

omit hcompat [IsTopologicalGroup I] [IsTopologicalGroup N] in
/-- The actual kernel region in the target packing has the expected ideal
exponent and a subexponential radius loss, in its transported Haar measure. -/
theorem exists_exponential_kernel_box_volumes
    (haar : NilpotentExponentialHaarInput E I)
    (groupExp : GroupLieAlgebra (𝓘(ℝ, E)) I → I) (hExp : IsGroupExponential groupExp)
    (e : U ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, E)) I) (hnil : LieRing.IsNilpotent U)
    (hc : ∀ u : U, ι (groupExp (e u)) = ExpN u)
    {m : ℕ} (b : Basis (Fin m) ℝ U) (cost : Fin m → ℝ)
    (μ : Measure I) [μ.IsHaarMeasure]
    (scale R : ℕ → ℝ) (hs : Tendsto scale atTop atTop)
    (hR0 : ∀ n, 0 ≤ R n) (hR : HasSubexponentialUpperBoundSeq scale R) :
    let μK := Measure.map (kernelRealization π ι hι hrange) μ
    let regions := fun n => exponentialIdealKernelRegion U π ExpN
      {u : U | ‖(exponentialRescaleBasis b cost (scale n)).equivFun u‖ ≤ R n}
    ∃ V : ℕ → ℝ, (∀ n, 0 ≤ V n) ∧ HasSubexponentialUpperBoundSeq scale V ∧
      ∀ n, μK (regions n) ≠ ⊤ ∧
        (μK (regions n)).toReal = V n * Real.exp ((∑ j, cost j) * scale n) := by
  dsimp only
  obtain ⟨V, hV0, hV, hvol⟩ := haar_model_sequence_weighted_boxes haar groupExp hExp e hnil
    b cost μ scale R hs hR0 hR
  refine ⟨V, hV0, hV, ?_⟩
  intro n
  have heq : (Measure.map (kernelRealization π ι hι hrange) μ)
      (exponentialIdealKernelRegion U π ExpN
        {u : U | ‖(exponentialRescaleBasis b cost (scale n)).equivFun u‖ ≤ R n}) =
      μ (exponentialCoordinateBox (groupExp ∘ e) (exponentialRescaleBasis b cost (scale n)) (R n)) := by
    rw [exponentialIdealKernelRegion_measure U π ι hι hrange (groupExp ∘ e) ExpN hc]
    congr 1
    ext z
    simp only [mem_image, mem_ofPred_eq, exponentialCoordinateBox]
    exact exists_congr (fun u => and_comm)
  rw [heq]
  exact hvol n

end Weighted

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanKernelRegionVolume
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Kernel-box volume for the actual Cartan ideal coordinates -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieModule LieAlgebra MeasureTheory Set Filter
open scoped Manifold Topology BigOperators

variable {EG G : Type} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G]
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {ExpG : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H ExpG)

set_option maxHeartbeats 1000000 in
theorem exists_cone_kernel_box_volumes
    (C : Set (H →ₗ[ℝ] ℝ)) {Q : Type} [Group Q] (π : F.N.carrier →* Q)
    (I : NilpotentLieModel (M.coneWordIdeal C))
    (ExpI : GroupLieAlgebra (𝓘(ℝ, I.modelSpace)) I.carrier → I.carrier)
    (hExpI : IsGroupExponential ExpI)
    (haarI : NilpotentExponentialHaarInput I.modelSpace I.carrier)
    (ι : I.carrier →* F.N.carrier) (hι : Topology.IsClosedEmbedding ι)
    (hrange : range ι = (π.ker : Set F.N.carrier))
    (hIExp : ∀ i : M.coneWordIdeal C,
      ι (ExpI (I.equiv i)) = F.ExpN (F.N.equiv (i : cartanRootIdeal H)))
    (μI : Measure I.carrier) [μI.IsHaarMeasure]
    (s : Fin M.letterCount → ℝ) (β : M.ConeIdealBases C)
    (scale R : ℕ → ℝ) (hscale : Tendsto scale atTop atTop)
    (hR0 : ∀ n, 0 ≤ R n) (hR : HasSubexponentialUpperBoundSeq scale R) :
    let μK := Measure.map (kernelRealization π ι hι hrange) μI
    let RI := fun n => exponentialIdealKernelRegion (M.coneWordIdeal C) π
      (F.ExpN ∘ F.N.equiv) {i | ‖(M.coneIdealBoxBasis C s β (scale n)).equivFun i‖ ≤ R n}
    ∃ V : ℕ → ℝ, (∀ n, 0 ≤ V n) ∧ HasSubexponentialUpperBoundSeq scale V ∧
      ∀ n, μK (RI n) ≠ ⊤ ∧ (μK (RI n)).toReal = V n *
        Real.exp ((∑ j, M.coneIdealWordCost C s (β.val j)) * scale n) :=
  exists_exponential_kernel_box_volumes (M.coneWordIdeal C) π ι hι hrange
    (F.ExpN ∘ F.N.equiv) haarI ExpI hExpI I.equiv (M.coneIdeal_nilpotent C) hIExp
    (WordBasisSelections.basis (M.coneMixedVector C) (M.coneIdealWordList C) β)
    (fun j => M.coneIdealWordCost C s (β.val j)) μI scale R hscale hR0 hR

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanProbeCoordinateRegions
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Measured ideal and Cartan regions for fixed exponential coordinates -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieModule LieAlgebra MeasureTheory Set Filter
open scoped Manifold Topology BigOperators

variable {EG G : Type} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G]
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {ExpG : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H ExpG)

set_option maxHeartbeats 1000000 in
theorem exists_ideal_cartan_probe_regions
    (C : Set (H →ₗ[ℝ] ℝ))
    (Q : NilpotentLieModel ((cartanRootIdeal H) ⧸ M.coneWordIdeal C))
    (chartN : GroupLieAlgebra (𝓘(ℝ, F.N.modelSpace)) F.N.carrier ≃ₜ F.N.carrier)
    (hchartN : ∀ v, chartN v = F.ExpN v)
    (chartQ : GroupLieAlgebra (𝓘(ℝ, Q.modelSpace)) Q.carrier ≃ₜ Q.carrier)
    (πQ : F.N.carrier →* Q.carrier)
    (hπQ : ∀ v, πQ (chartN (F.N.equiv v)) =
      chartQ (Q.equiv ((M.coneWordIdeal C).toSubmodule.mkQ v)))
    (hzeroQ : chartQ (Q.equiv 0) = 1)
    (bQ : Basis (Fin (finrank ℝ (cartanRootIdeal H ⧸ (M.coneWordIdeal C).toSubmodule)))
      ℝ (cartanRootIdeal H ⧸ (M.coneWordIdeal C).toSubmodule))
    (lift : Fin (finrank ℝ (cartanRootIdeal H ⧸ (M.coneWordIdeal C).toSubmodule)) →
      cartanRootIdeal H)
    (hlift : ∀ j, (M.coneWordIdeal C).toSubmodule.mkQ (lift j) = bQ j)
    (I : NilpotentLieModel (M.coneWordIdeal C))
    (ExpI : GroupLieAlgebra (𝓘(ℝ, I.modelSpace)) I.carrier → I.carrier)
    (hExpI : IsGroupExponential ExpI)
    (haarI : NilpotentExponentialHaarInput I.modelSpace I.carrier)
    (ιI : I.carrier →* F.N.carrier) (hιI : Topology.IsClosedEmbedding ιI)
    (hrange : range ιI = (πQ.ker : Set F.N.carrier))
    (hIExp : ∀ i : M.coneWordIdeal C,
      ιI (ExpI (I.equiv i)) = F.ExpN (F.N.equiv (i : cartanRootIdeal H)))
    (μI : Measure I.carrier) [μI.IsHaarMeasure]
    (ν : Measure F.D.carrier) [ν.IsHaarMeasure]
    (haarD : NilpotentExponentialHaarInput F.D.modelSpace F.D.carrier)
    (hbijD : Function.Bijective F.ExpD)
    (s : Fin M.letterCount → ℝ) (β : M.ConeIdealBases C)
    (scale S RD : ℕ → ℝ) (hscale : Tendsto scale atTop atTop)
    (hS0 : ∀ n, 0 ≤ S n) (hRD0 : ∀ n, 0 ≤ RD n)
    (hS : HasSubexponentialUpperBoundSeq scale S)
    (hRD : HasSubexponentialUpperBoundSeq scale RD) :
    let μK := Measure.map (kernelRealization πQ ιI hιI hrange) μI
    ∃ (σ : C(Q.carrier, F.N.carrier)) (hσ : ∀ q, πQ (σ q) = q)
      (RI : ℕ → Set πQ.ker) (BD : ℕ → Set F.D.carrier) (V : ℕ → ℝ),
      (∀ n, μK (RI n) ≠ ⊤ ∧ ν (BD n) ≠ ⊤) ∧
      HasSubexponentialUpperBoundSeq scale V ∧ (∀ n, 0 ≤ V n) ∧
      HasSubexponentialUpperBoundSeq scale (fun n => (ν (BD n)).toReal) ∧
      (∀ n, (μK (RI n)).toReal = V n *
        Real.exp ((∑ j, M.coneIdealWordCost C s (β.val j)) * scale n)) ∧
      ∀ n u d,
        (∃ (i : M.coneWordIdeal C) (q : cartanRootIdeal H ⧸ (M.coneWordIdeal C).toSubmodule),
          u = F.ExpN (F.N.equiv (i : cartanRootIdeal H)) *
            F.ExpN (F.N.equiv (quotientLinearSection (M.coneWordIdeal C) bQ lift q)) ∧
          ‖(M.coneIdealBoxBasis C s β (scale n)).equivFun i‖ ≤ S n) →
        ‖(finBasis ℝ H).equivFun (cartanLog H F.D.equiv F.ExpD hbijD d)‖ ≤ RD n →
        quotientSectionResidual πQ σ hσ u ∈ RI n ∧ d ∈ BD n := by
  dsimp only
  let RI := fun n => exponentialIdealKernelRegion (M.coneWordIdeal C) πQ
    (F.ExpN ∘ F.N.equiv) {i | ‖(M.coneIdealBoxBasis C s β (scale n)).equivFun i‖ ≤ S n}
  let BD := fun n => {d : F.D.carrier |
    ‖(finBasis ℝ H).equivFun (cartanLog H F.D.equiv F.ExpD hbijD d)‖ ≤ RD n}
  obtain ⟨V, hV0, hV, hIvol⟩ := M.exists_cone_kernel_box_volumes F C πQ
    I ExpI hExpI haarI ιI hιI hrange hIExp μI s β scale S hscale hS0 hS
  have hBDvol := F.log_regions_volume haarD hbijD ν scale RD hscale hRD0 hRD
  have hBD := hBDvol.1
  have hDvol := hBDvol.2
  let σ := exponentialQuotientSection (M.coneWordIdeal C) bQ lift
    F.N.equiv.toLinearEquiv Q.equiv.toLinearEquiv chartN chartQ
  have hσ : ∀ q, πQ (σ q) = q :=
    exponentialQuotientSection_rightInverse (M.coneWordIdeal C) bQ lift hlift
      F.N.equiv.toLinearEquiv Q.equiv.toLinearEquiv chartN chartQ πQ hπQ
  refine ⟨σ, hσ, RI, BD, V, fun n => ⟨(hIvol n).1, hBD n⟩,
    hV, hV0, hDvol, fun n => (hIvol n).2, ?_⟩
  rintro n u d ⟨i, q, he, hi⟩ hd
  refine ⟨?_, hd⟩
  have he' : u = chartN (F.N.equiv (i : cartanRootIdeal H)) *
      chartN (F.N.equiv (quotientLinearSection (M.coneWordIdeal C) bQ lift q)) := by
    simpa only [hchartN] using he
  have hr := exponential_section_residual_mem (M.coneWordIdeal C) bQ lift hlift
    F.N.equiv.toLinearEquiv Q.equiv.toLinearEquiv chartN chartQ πQ hπQ hzeroQ
    {i : M.coneWordIdeal C | ‖(M.coneIdealBoxBasis C s β (scale n)).equivFun i‖ ≤ S n}
    ⟨i, hi, q, he'⟩
  simpa only [RI, σ, Function.comp_def, hchartN, LieEquiv.coe_toLinearEquiv] using hr

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_MeasuredRegionsFromCoordinates
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Measured ideal and Cartan regions for fixed exponential coordinates -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieModule LieAlgebra MeasureTheory Set Filter
open scoped Manifold Topology BigOperators

variable {EG G : Type} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G]
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {ExpG : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H ExpG)

theorem exists_measured_probe_regions_from_coordinates
    (C : Set (H →ₗ[ℝ] ℝ))
    (Q : NilpotentLieModel ((cartanRootIdeal H) ⧸ M.coneWordIdeal C))
    (chartN : GroupLieAlgebra (𝓘(ℝ, F.N.modelSpace)) F.N.carrier ≃ₜ F.N.carrier)
    (hchartN : ∀ v, chartN v = F.ExpN v)
    (chartQ : GroupLieAlgebra (𝓘(ℝ, Q.modelSpace)) Q.carrier ≃ₜ Q.carrier)
    (πQ : F.N.carrier →* Q.carrier)
    (hπQ : ∀ v, πQ (chartN (F.N.equiv v)) =
      chartQ (Q.equiv ((M.coneWordIdeal C).toSubmodule.mkQ v)))
    (hzeroQ : chartQ (Q.equiv 0) = 1)
    (bQ : Basis (Fin (finrank ℝ (cartanRootIdeal H ⧸ (M.coneWordIdeal C).toSubmodule)))
      ℝ (cartanRootIdeal H ⧸ (M.coneWordIdeal C).toSubmodule))
    (lift : Fin (finrank ℝ (cartanRootIdeal H ⧸ (M.coneWordIdeal C).toSubmodule)) →
      cartanRootIdeal H)
    (hlift : ∀ j, (M.coneWordIdeal C).toSubmodule.mkQ (lift j) = bQ j)
    (I : NilpotentLieModel (M.coneWordIdeal C))
    (ExpI : GroupLieAlgebra (𝓘(ℝ, I.modelSpace)) I.carrier → I.carrier)
    (hExpI : IsGroupExponential ExpI)
    (haarI : NilpotentExponentialHaarInput I.modelSpace I.carrier)
    (ιI : I.carrier →* F.N.carrier) (hιI : Topology.IsClosedEmbedding ιI)
    (hrange : range ιI = (πQ.ker : Set F.N.carrier))
    (hIExp : ∀ i : M.coneWordIdeal C,
      ιI (ExpI (I.equiv i)) = F.ExpN (F.N.equiv (i : cartanRootIdeal H)))
    (μI : Measure I.carrier) [μI.IsHaarMeasure]
    (ν : Measure F.D.carrier) [ν.IsHaarMeasure]
    (haarD : NilpotentExponentialHaarInput F.D.modelSpace F.D.carrier)
    (hbijD : Function.Bijective F.ExpD)
    (s : Fin M.letterCount → ℝ) (β : M.ConeIdealBases C)
    (scale S RD : ℕ → ℝ) (hscale : Tendsto scale atTop atTop)
    (hS0 : ∀ n, 0 ≤ S n) (hRD0 : ∀ n, 0 ≤ RD n)
    (hS : HasSubexponentialUpperBoundSeq scale S)
    (hRD : HasSubexponentialUpperBoundSeq scale RD)
    (μQ : Measure Q.carrier) (RQ : ℕ → Set Q.carrier)
    (hRQ : ∀ n, μQ (RQ n) ≠ ⊤)
    (hRQvol : HasSubexponentialUpperBoundSeq scale (fun n => (μQ (RQ n)).toReal)) :
    let μK := Measure.map (kernelRealization πQ ιI hιI hrange) μI
    let P := ∑ j, M.coneIdealWordCost C s (β.val j)
    ∃ R : MeasuredProbeRegions πQ μQ μK ν scale P,
      R.quotientRegion = RQ ∧ ∀ n u d,
        (∃ (i : M.coneWordIdeal C) (q : cartanRootIdeal H ⧸ (M.coneWordIdeal C).toSubmodule),
          u = F.ExpN (F.N.equiv (i : cartanRootIdeal H)) *
            F.ExpN (F.N.equiv (quotientLinearSection (M.coneWordIdeal C) bQ lift q)) ∧
          ‖(M.coneIdealBoxBasis C s β (scale n)).equivFun i‖ ≤ S n) →
        ‖(finBasis ℝ H).equivFun (cartanLog H F.D.equiv F.ExpD hbijD d)‖ ≤ RD n →
        quotientSectionResidual πQ R.sectionMap R.section_rightInverse u ∈ R.idealRegion n ∧
          d ∈ R.cartanRegion n := by
  dsimp only
  have hregions := M.exists_ideal_cartan_probe_regions F C Q chartN hchartN chartQ πQ
    hπQ hzeroQ bQ lift hlift I ExpI hExpI haarI ιI hιI hrange hIExp μI ν haarD hbijD
    s β scale S RD hscale hS0 hRD0 hS hRD
  let σ := Classical.choose hregions
  have hr₁ := Classical.choose_spec hregions
  let hσ := Classical.choose hr₁
  have hr₂ := Classical.choose_spec hr₁
  let RI := Classical.choose hr₂
  have hr₃ := Classical.choose_spec hr₂
  let BD := Classical.choose hr₃
  have hr₄ := Classical.choose_spec hr₃
  let V := Classical.choose hr₄
  have hregion := Classical.choose_spec hr₄
  have hfinite := hregion.1
  have hV := hregion.2.1
  have hV0 := hregion.2.2.1
  have hDvol := hregion.2.2.2.1
  have hIvol := hregion.2.2.2.2.1
  have hcoord := hregion.2.2.2.2.2
  let R : MeasuredProbeRegions πQ μQ
      (Measure.map (kernelRealization πQ ιI hιI hrange) μI) ν scale
      (∑ j, M.coneIdealWordCost C s (β.val j)) :=
    { sectionMap := σ
      section_rightInverse := hσ
      quotientRegion := RQ
      idealRegion := RI
      cartanRegion := BD
      idealLoss := V
      quotient_finite := hRQ
      ideal_finite := fun n => (hfinite n).1
      cartan_finite := fun n => (hfinite n).2
      quotient_subexponential := hRQvol
      ideal_subexponential := hV
      idealLoss_nonneg := hV0
      cartan_subexponential := hDvol
      ideal_volume := hIvol }
  exact ⟨R, rfl, hcoord⟩

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_ProbeImageBridge
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The bridge between the two actual probe images -/

noncomputable section
namespace PolycyclicRecognition

open Filter
open scoped Topology NNReal

variable {G W Z V : Type} [Group G]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  [AddCommGroup V] [Module ℝ V]

section Metric

variable [MetricSpace G] [IsIsometricSMul G G]

/-- Left invariance identifies the bridge length with endpoint distance. -/
theorem dist_one_inv_mul_eq (a b : G) : dist 1 (a⁻¹ * b) = dist a b := by
  simpa only [inv_mul_cancel] using dist_mul_left a⁻¹ a b

end Metric

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_ProbeRestrictionComposition
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Combining the two restrictions on the same probe endpoint -/

noncomputable section
namespace PolycyclicRecognition

/-- Change the cell predicate without changing the chosen pair of lifts. -/
theorem map_cell_lift_conditions {N D Z : Type} {cell : Set Z}
    {S : N → D → Prop} {P Q : N → D → Z → Prop}
    (h : ∃ u d, S u d ∧ ∀ z ∈ cell, P u d z)
    (hmap : ∀ u d z, z ∈ cell → P u d z → Q u d z) :
    ∃ u d, S u d ∧ ∀ z ∈ cell, Q u d z := by
  obtain ⟨u, d, he, hP⟩ := h
  exact ⟨u, d, he, fun z hz => hmap u d z hz (hP z hz)⟩

variable {N D G Q : Type} [Group G] [MetricSpace G] [IsIsometricSMul G G]

/-- The first path's quotient condition and the bridged second path's
coordinate conditions hold together for one lift of the first endpoint. -/
theorem exists_two_frame_probe_lift
    (project : N → D → G) (act : G → Q → Q) (oneQ : Q)
    (cell : Set (N × D)) (region : Set Q)
    (base anchor first second : G) (r : ℝ)
    (B : N → D → Prop) (C : D → N × D → Prop)
    (P : N → D → N × D → Prop)
    (hfirst : ∃ u d, project u d = base⁻¹ * first ∧ B u d ∧
      ∀ z ∈ cell, act ((base⁻¹ * first) * project z.1 z.2) oneQ ∈ region ∧ C d z)
    (hsecond : ∀ bridge : G, dist 1 bridge ≤ r →
      ∃ u d, project u d = (anchor⁻¹ * second) * bridge ∧ ∀ z ∈ cell, P u d z)
    (hdist : dist second first ≤ r) :
    ∃ u d, project u d = anchor⁻¹ * first ∧ ∀ z ∈ cell,
      act (base⁻¹ * (first * project z.1 z.2)) oneQ ∈ region ∧ P u d z := by
  obtain ⟨_, _, _, _, hquot⟩ := hfirst
  have hd : dist 1 (second⁻¹ * first) ≤ r := by
    rw [dist_one_inv_mul_eq]
    exact hdist
  obtain ⟨u, d, he, hcoord⟩ := hsecond (second⁻¹ * first) hd
  refine ⟨u, d, ?_, ?_⟩
  · simpa only [mul_assoc, mul_inv_cancel_left] using he
  · intro z hz
    exact ⟨by simpa only [mul_assoc] using (hquot z hz).1, hcoord z hz⟩

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanMeasuredRegionsFromLifts
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Measured ideal and Cartan regions for fixed exponential coordinates -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieModule LieAlgebra MeasureTheory Set Filter
open scoped Manifold Topology BigOperators

variable {EG G : Type} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G]
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {ExpG : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H ExpG)

set_option maxHeartbeats 1000000 in
theorem measured_probe_regions_of_uniform_lifts
    (C : Set (H →ₗ[ℝ] ℝ))
    (Q : NilpotentLieModel ((cartanRootIdeal H) ⧸ M.coneWordIdeal C))
    (chartN : GroupLieAlgebra (𝓘(ℝ, F.N.modelSpace)) F.N.carrier ≃ₜ F.N.carrier)
    (hchartN : ∀ v, chartN v = F.ExpN v)
    (chartQ : GroupLieAlgebra (𝓘(ℝ, Q.modelSpace)) Q.carrier ≃ₜ Q.carrier)
    (πQ : F.N.carrier →* Q.carrier)
    (hπQ : ∀ v, πQ (chartN (F.N.equiv v)) =
      chartQ (Q.equiv ((M.coneWordIdeal C).toSubmodule.mkQ v)))
    (hzeroQ : chartQ (Q.equiv 0) = 1)
    (bQ : Basis (Fin (finrank ℝ (cartanRootIdeal H ⧸ (M.coneWordIdeal C).toSubmodule)))
      ℝ (cartanRootIdeal H ⧸ (M.coneWordIdeal C).toSubmodule))
    (lift : Fin (finrank ℝ (cartanRootIdeal H ⧸ (M.coneWordIdeal C).toSubmodule)) →
      cartanRootIdeal H)
    (hlift : ∀ j, (M.coneWordIdeal C).toSubmodule.mkQ (lift j) = bQ j)
    (I : NilpotentLieModel (M.coneWordIdeal C))
    (ExpI : GroupLieAlgebra (𝓘(ℝ, I.modelSpace)) I.carrier → I.carrier)
    (hExpI : IsGroupExponential ExpI)
    (haarI : NilpotentExponentialHaarInput I.modelSpace I.carrier)
    (ιI : I.carrier →* F.N.carrier) (hιI : Topology.IsClosedEmbedding ιI)
    (hrange : range ιI = (πQ.ker : Set F.N.carrier))
    (hIExp : ∀ i : M.coneWordIdeal C,
      ιI (ExpI (I.equiv i)) = F.ExpN (F.N.equiv (i : cartanRootIdeal H)))
    (μI : Measure I.carrier) [μI.IsHaarMeasure]
    (ν : Measure F.D.carrier) [ν.IsHaarMeasure]
    (haarD : NilpotentExponentialHaarInput F.D.modelSpace F.D.carrier)
    (hbijD : Function.Bijective F.ExpD)
    (s : Fin M.letterCount → ℝ) (β : M.ConeIdealBases C)
    {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W]
    (π : G →* Multiplicative W) (act : G →* Equiv.Perm Q.carrier)
    (cell : Set (F.N.carrier × F.D.carrier)) (E₁ E₂ : Set W)
    (μQ : Measure Q.carrier) (δ₀ : ℝ)
    (hdata : ∀ (scale η : ℕ → ℝ),
        StrictMono scale → Tendsto scale atTop atTop →
        (∀ n, 1 ≤ scale n) → (∀ n, 0 ≤ η n) → Tendsto η atTop (𝓝 0) →
        ∀ A B : ℝ, 0 ≤ A → 0 ≤ B →
      ∃ (RQ : ℕ → Set Q.carrier) (S RD : ℕ → ℝ),
        (∀ n, μQ (RQ n) ≠ ⊤) ∧
        HasSubexponentialUpperBoundSeq scale (fun n => (μQ (RQ n)).toReal) ∧
        (∀ n, 0 ≤ S n) ∧ (∀ n, 0 ≤ RD n) ∧
        HasSubexponentialUpperBoundSeq scale S ∧ HasSubexponentialUpperBoundSeq scale RD ∧
        ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
        ∀ᶠ n in atTop, ∀ (base anchor first second : G)
          (path₁ : Path (1 : G) (base⁻¹ * first))
          (path₂ : Path (1 : G) (anchor⁻¹ * second)),
          PathMetricBound path₁ (A * scale n) (B * (1 + Real.log (2 + scale n))) →
          PathMetricBound path₂ (A * scale n) (B * (1 + Real.log (2 + scale n))) →
          (∀ t, ∃ w ∈ E₁, ‖(π (path₁ t)).toAdd - scale n • w‖ ≤
            2 * scale n * η n + A * (1 + Real.log (2 + scale n))) →
          (∀ t, ∃ w ∈ E₂, ‖(π (path₂ t)).toAdd - scale n • w‖ ≤
            2 * scale n * η n + A * (1 + Real.log (2 + scale n))) →
          ‖(π (anchor⁻¹ * second)).toAdd‖ ≤ δ * scale n →
          dist second first ≤ δ * scale n →
          ∃ (u : F.N.carrier) (d : F.D.carrier),
            F.inclusionN u * F.inclusionD d = anchor⁻¹ * first ∧
            ∀ z ∈ cell,
              act (base⁻¹ * (first * (F.inclusionN z.1 * F.inclusionD z.2))) 1 ∈ RQ n ∧
              (∃ (i : M.coneWordIdeal C)
                (q : (cartanRootIdeal H) ⧸ (M.coneWordIdeal C).toSubmodule),
                u * F.action d z.1 = F.ExpN (F.N.equiv (i : cartanRootIdeal H)) *
                  F.ExpN (F.N.equiv (quotientLinearSection (M.coneWordIdeal C) bQ lift q)) ∧
                ‖(M.coneIdealBoxBasis C
                  s β (scale n)).equivFun i‖ ≤ S n) ∧
              ‖(finBasis ℝ H).equivFun (cartanLog H F.D.equiv F.ExpD
                hbijD (d * z.2))‖ ≤ RD n) :
    ∀ (scale η : ℕ → ℝ),
      StrictMono scale → Tendsto scale atTop atTop →
      (∀ n, 1 ≤ scale n) → (∀ n, 0 ≤ η n) → Tendsto η atTop (𝓝 0) →
      ∀ A B : ℝ, 0 ≤ A → 0 ≤ B →
      ∃ R : MeasuredProbeRegions πQ μQ (Measure.map (kernelRealization πQ ιI hιI hrange) μI) ν scale (∑ j, M.coneIdealWordCost C s (β.val j)),
        ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
        ∀ᶠ n in atTop, R.ControlsTwoPaths
          (fun u d => F.inclusionN u * F.inclusionD d) F.action (fun g q => act g q)
          π cell E₁ E₂ η A B δ n := by
  intro scale η hmono hscale hscale1 hη0 hη A B hA hB
  obtain ⟨RQ, S, RD, hRQ, hRQvol, hS0, hRD0, hS, hRD, hrestrict⟩ :=
    hdata scale η hmono hscale hscale1 hη0 hη A B hA hB
  obtain ⟨R, hRQeq, hcoord⟩ :=
    M.exists_measured_probe_regions_from_coordinates F C Q chartN hchartN chartQ πQ
      hπQ hzeroQ bQ lift hlift I ExpI hExpI haarI ιI hιI hrange hIExp μI ν haarD hbijD
      s β scale S RD hscale hS0 hRD0 hS hRD
      μQ RQ hRQ hRQvol
  refine ⟨R, ?_⟩
  intro δ hδ hδle
  filter_upwards [hrestrict δ hδ hδle] with n hn
  intro base anchor first second path₁ path₂ hm₁ hm₂ hh₁ hh₂ hsmall hdist
  exact map_cell_lift_conditions
    (hn base anchor first second path₁ path₂ hm₁ hm₂ hh₁ hh₂ hsmall hdist)
    (fun u d z _ hz => ⟨by simpa only [hRQeq] using hz.1,
      hcoord n (u * F.action d z.1) (d * z.2) hz.2.1 hz.2.2⟩)

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanUniformProfileBridge
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The profile bridge threshold precedes path length and error choices -/

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
theorem exists_uniform_profile_bridge_restrictions
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (γ₀ : M.Bases)
    {cell : Set (F.N.carrier × F.D.carrier)} (hcell : IsCompact cell)
    (hφ : ∀ d, F.action d = M.adjointGroupAutomorphism T F.N.equiv F.ExpN F.isExpN
      hbijN dynkinN (cartanLog H F.D.equiv F.ExpD hbijD d))
    (hpath : ∀ g : G, ∃ γ : ℝ → G, γ 0 = 1 ∧ γ 1 = g ∧
      ∀ t ∈ Icc (0 : ℝ) 1, ∀ u ∈ Icc (0 : ℝ) 1,
        dist (γ t) (γ u) ≤ dist 1 g * |t - u|)
    {Kπ : ℝ} (hKπ : 0 ≤ Kπ)
    (hLip : ∀ x y, ‖(π x).toAdd - (π y).toAdd‖ ≤ Kπ * dist x y)
    (C : Set (H →ₗ[ℝ] ℝ))
    (bI₀ : Basis (Fin (finrank ℝ (M.coneWordIdeal C))) ℝ (M.coneWordIdeal C))
    {E : Set W} (hE : IsCompact E) (hne : E.Nonempty)
    (hs : ∀ i, 0 ≤ (M.supportIn T hunimod eW).weightSupport E i)
    (hzero : ∀ i, (M.weight i : H →ₗ[ℝ] ℝ) ∈ C →
      (M.supportIn T hunimod eW).weightSupport E i = 0)
    (hpos : ∀ i, (M.weight i : H →ₗ[ℝ] ℝ) ∉ C →
      0 < (M.supportIn T hunimod eW).weightSupport E i)
    (β : M.ConeIdealBases C)
    (hβ : M.IsMaximizingConeIdealBasis C bI₀
      ((M.supportIn T hunimod eW).weightSupport E) β)
    {Q : Type} [Group Q]
    (ExpQ : ((cartanRootIdeal H) ⧸ (M.coneWordIdeal C).toSubmodule) → Q)
    (πQ : F.N.carrier →* Q)
    (hπQ : ∀ v, πQ (F.ExpN (F.N.equiv v)) =
      ExpQ ((M.coneWordIdeal C).toSubmodule.mkQ v))
    (hinjQ : Function.Injective ExpQ) (hzeroQ : ExpQ 0 = 1)
    :
    ∃ (bQ : Basis (Fin (finrank ℝ (cartanRootIdeal H ⧸ (M.coneWordIdeal C).toSubmodule)))
        ℝ (cartanRootIdeal H ⧸ (M.coneWordIdeal C).toSubmodule))
      (lift : Fin (finrank ℝ (cartanRootIdeal H ⧸ (M.coneWordIdeal C).toSubmodule)) →
        cartanRootIdeal H),
      ∃ _hlift : ∀ j, (M.coneWordIdeal C).toSubmodule.mkQ (lift j) = bQ j,
      ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ (scale η : ℕ → ℝ),
        StrictMono scale → Tendsto scale atTop atTop →
        (∀ n, 1 ≤ scale n) → (∀ n, 0 ≤ η n) → Tendsto η atTop (𝓝 0) →
        ∀ A B : ℝ, 0 ≤ A → 0 ≤ B →
        ∃ S RD : ℕ → ℝ,
          (∀ n, 0 ≤ S n) ∧ (∀ n, 0 ≤ RD n) ∧
          HasSubexponentialUpperBoundSeq scale S ∧ HasSubexponentialUpperBoundSeq scale RD ∧
          ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
        ∀ᶠ n in atTop, ∀ {endpoint : G} (path : Path (1 : G) endpoint) (bridge : G),
          PathMetricBound path (A * scale n) (B * (1 + Real.log (2 + scale n))) →
          (∀ t, ∃ w ∈ E, ‖(π (path t)).toAdd - scale n • w‖ ≤
            2 * scale n * η n + A * (1 + Real.log (2 + scale n))) →
          ‖(π endpoint).toAdd‖ ≤ δ * scale n →
          dist 1 bridge ≤ δ * scale n →
          ∃ (u : F.N.carrier) (d : F.D.carrier),
            F.inclusionN u * F.inclusionD d = endpoint * bridge ∧
            ∀ z ∈ cell,
              (∃ (i : M.coneWordIdeal C)
                (q : (cartanRootIdeal H) ⧸ (M.coneWordIdeal C).toSubmodule),
                u * F.action d z.1 = F.ExpN (F.N.equiv (i : cartanRootIdeal H)) *
                  F.ExpN (F.N.equiv (quotientLinearSection (M.coneWordIdeal C) bQ lift q)) ∧
                ‖(M.coneIdealBoxBasis C
                  ((M.supportIn T hunimod eW).weightSupport E) β (scale n)).equivFun i‖ ≤ S n) ∧
              ‖(finBasis ℝ H).equivFun (cartanLog H F.D.equiv F.ExpD
                hbijD (d * z.2))‖ ≤ RD n := by
  obtain ⟨bQ, lift, hlift, γ, hγ, hbox, K, hK, hbr⟩ :=
    M.exists_cone_adapted_path_basis C T hunimod eW b₀ bI₀ E hs hzero β hβ
  obtain ⟨lo, hlo, hcost⟩ := M.exists_positive_coneIdeal_width C
    ((M.supportIn T hunimod eW).weightSupport E) hs hpos
  refine ⟨bQ, lift, hlift, ?_⟩
  exact M.exists_uniform_profile_bridge_restrictions_of_basis T F hunimod eW π hπExp
    chartN hchartN chartD hchartD dynkinN dynkinD hbijN hbijD
    b₀ γ₀ hcell hφ hpath hKπ hLip C hE hne β bQ lift hlift γ hγ
    (hbox (F.ExpN ∘ F.N.equiv)) K hK hbr hlo (fun j => hcost (β.val j))
    ExpQ πQ hπQ hinjQ hzeroQ



end PolycyclicRecognition.CartanWordModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanUniformTwoPathRestrictions
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform smallness threshold for the two probe paths -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule Metric Set Filter
open scoped Manifold Topology
open MeasureTheory

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
theorem exists_uniform_two_path_probe_restrictions
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (γ₀ : M.Bases) {cell : Set (F.N.carrier × F.D.carrier)} (hcell : IsCompact cell)
    (hφ : ∀ d, F.action d = M.adjointGroupAutomorphism T F.N.equiv F.ExpN F.isExpN
      hbijN dynkinN (cartanLog H F.D.equiv F.ExpD hbijD d))
    (hpath : ∀ g : G, ∃ γ : ℝ → G, γ 0 = 1 ∧ γ 1 = g ∧
      ∀ t ∈ Icc (0 : ℝ) 1, ∀ u ∈ Icc (0 : ℝ) 1,
        dist (γ t) (γ u) ≤ dist 1 g * |t - u|)
    {Kπ : ℝ} (hKπ : 0 ≤ Kπ)
    (hLip : ∀ x y, ‖(π x).toAdd - (π y).toAdd‖ ≤ Kπ * dist x y)
    (C : Set (H →ₗ[ℝ] ℝ))
    (Q : NilpotentLieModel ((cartanRootIdeal H) ⧸ M.coneWordIdeal C))
    (ExpQ : GroupLieAlgebra (𝓘(ℝ, Q.modelSpace)) Q.carrier → Q.carrier)
    (hExpQ : IsGroupExponential ExpQ) (hbijQ : Function.Bijective ExpQ)
    (haarQ : NilpotentExponentialHaarInput Q.modelSpace Q.carrier)
    (πQ : F.N.carrier →* Q.carrier)
    (hπQ : ∀ v, πQ (F.ExpN (F.N.equiv v)) = ExpQ (Q.equiv (M.coneProjection C v)))
    (μQ : Measure Q.carrier) [μQ.IsHaarMeasure]
    (α : F.D.carrier →* MulAut Q.carrier) (act : G →* Equiv.Perm Q.carrier)
    (hact : ∀ u d q, act (F.inclusionN u * F.inclusionD d) q = πQ u * α d q)
    (E₁ E₂ : Set W) (hE₁ : IsCompact E₁) (hne₁ : E₁.Nonempty)
    (hE₂ : IsCompact E₂) (hne₂ : E₂.Nonempty)
    (β₁ : M.Bases)
    (hβ₁ : IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
      (M.boxCost T hunimod eW E₁) β₁.val)
    (hz₁ : ∀ i, (M.weight i : H →ₗ[ℝ] ℝ) ∈ C →
      (M.supportIn T hunimod eW).weightSupport E₁ i = 0)
    (bI₀ : Basis (Fin (finrank ℝ (M.coneWordIdeal C))) ℝ (M.coneWordIdeal C))
    (β₂ : M.ConeIdealBases C)
    (hβ₂ : M.IsMaximizingConeIdealBasis C bI₀
      ((M.supportIn T hunimod eW).weightSupport E₂) β₂)
    (hs₂ : ∀ i, 0 ≤ (M.supportIn T hunimod eW).weightSupport E₂ i)
    (hz₂ : ∀ i, (M.weight i : H →ₗ[ℝ] ℝ) ∈ C →
      (M.supportIn T hunimod eW).weightSupport E₂ i = 0)
    (hp₂ : ∀ i, (M.weight i : H →ₗ[ℝ] ℝ) ∉ C →
      0 < (M.supportIn T hunimod eW).weightSupport E₂ i)
    :
    ∃ (bQ : Basis (Fin (finrank ℝ (cartanRootIdeal H ⧸ (M.coneWordIdeal C).toSubmodule)))
        ℝ (cartanRootIdeal H ⧸ (M.coneWordIdeal C).toSubmodule))
      (lift : Fin (finrank ℝ (cartanRootIdeal H ⧸ (M.coneWordIdeal C).toSubmodule)) →
        cartanRootIdeal H),
      (∀ j, (M.coneWordIdeal C).toSubmodule.mkQ (lift j) = bQ j) ∧
      ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ (scale η : ℕ → ℝ),
        StrictMono scale → Tendsto scale atTop atTop →
        (∀ n, 1 ≤ scale n) → (∀ n, 0 ≤ η n) → Tendsto η atTop (𝓝 0) →
        ∀ A B : ℝ, 0 ≤ A → 0 ≤ B →
      ∃ (RQ : ℕ → Set Q.carrier) (S RD : ℕ → ℝ),
        (∀ n, μQ (RQ n) ≠ ⊤) ∧
        HasSubexponentialUpperBoundSeq scale (fun n => (μQ (RQ n)).toReal) ∧
        (∀ n, 0 ≤ S n) ∧ (∀ n, 0 ≤ RD n) ∧
        HasSubexponentialUpperBoundSeq scale S ∧ HasSubexponentialUpperBoundSeq scale RD ∧
        ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
        ∀ᶠ n in atTop, ∀ (base anchor first second : G)
          (path₁ : Path (1 : G) (base⁻¹ * first))
          (path₂ : Path (1 : G) (anchor⁻¹ * second)),
          PathMetricBound path₁ (A * scale n) (B * (1 + Real.log (2 + scale n))) →
          PathMetricBound path₂ (A * scale n) (B * (1 + Real.log (2 + scale n))) →
          (∀ t, ∃ w ∈ E₁, ‖(π (path₁ t)).toAdd - scale n • w‖ ≤
            2 * scale n * η n + A * (1 + Real.log (2 + scale n))) →
          (∀ t, ∃ w ∈ E₂, ‖(π (path₂ t)).toAdd - scale n • w‖ ≤
            2 * scale n * η n + A * (1 + Real.log (2 + scale n))) →
          ‖(π (anchor⁻¹ * second)).toAdd‖ ≤ δ * scale n →
          dist second first ≤ δ * scale n →
          ∃ (u : F.N.carrier) (d : F.D.carrier),
            F.inclusionN u * F.inclusionD d = anchor⁻¹ * first ∧
            ∀ z ∈ cell,
              act (base⁻¹ * (first * (F.inclusionN z.1 * F.inclusionD z.2))) 1 ∈ RQ n ∧
              (∃ (i : M.coneWordIdeal C)
                (q : (cartanRootIdeal H) ⧸ (M.coneWordIdeal C).toSubmodule),
                u * F.action d z.1 = F.ExpN (F.N.equiv (i : cartanRootIdeal H)) *
                  F.ExpN (F.N.equiv (quotientLinearSection (M.coneWordIdeal C) bQ lift q)) ∧
                ‖(M.coneIdealBoxBasis C
                  ((M.supportIn T hunimod eW).weightSupport E₂) β₂ (scale n)).equivFun i‖ ≤ S n) ∧
              ‖(finBasis ℝ H).equivFun (cartanLog H F.D.equiv F.ExpD
                hbijD (d * z.2))‖ ≤ RD n := by
  obtain ⟨bQ, lift, hlift, δ₀, hδ₀, hsecond⟩ :=
    M.exists_uniform_profile_bridge_restrictions T F hunimod eW π hπExp
      chartN hchartN chartD hchartD dynkinN dynkinD hbijN hbijD
      b₀ γ₀ hcell hφ hpath hKπ hLip C bI₀ hE₂ hne₂ hs₂ hz₂ hp₂ β₂ hβ₂
      (ExpQ ∘ Q.equiv) πQ hπQ (hbijQ.injective.comp Q.equiv.injective)
      (by simp only [Function.comp_apply, map_zero, hExpQ.map_zero])
  refine ⟨bQ, lift, hlift, δ₀, hδ₀, ?_⟩
  intro scale η hmono hscale hscale1 hη0 hη A B hA hB
  obtain ⟨RQ, _RD₁, hRQ, hRQvol, _hRD₁0, _hRD₁, hfirst⟩ :=
    M.exists_controlled_profile_quotient_restriction T F hunimod eW π hπExp
      chartN hchartN chartD hchartD dynkinN dynkinD b₀ γ₀ hcell hφ hpath hKπ hLip
      hE₁ hne₁ β₁ hβ₁ scale η hscale hscale1 hη0 hη A B hA hB C hz₁
      Q ExpQ hExpQ haarQ πQ hπQ (finBasis ℝ _) μQ α act hact
  obtain ⟨S, RD, hS0, hRD0, hS, hRD, hsecond⟩ :=
    hsecond scale η hmono hscale hscale1 hη0 hη A B hA hB
  refine ⟨RQ, S, RD, hRQ, hRQvol, hS0, hRD0, hS, hRD, ?_⟩
  intro δ hδ hδle
  filter_upwards [hsecond δ hδ hδle] with n hn
  intro base anchor first second path₁ path₂ hm₁ hm₂ hh₁ hh₂ hsmall hdist
  exact exists_two_frame_probe_lift
    (fun u d => F.inclusionN u * F.inclusionD d) (fun g q => act g q) 1
    cell (RQ n) base anchor first second (δ * scale n) _ _ _
    (hfirst n path₁ hm₁ hh₁)
    (fun bridge hbridge => hn path₂ bridge hm₂ hh₂ hsmall hbridge) hdist


end PolycyclicRecognition.CartanWordModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanUniformMeasuredRegions
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Measured probe regions with the threshold fixed before the paths -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule Metric Set Filter
open scoped Manifold Topology
open MeasureTheory

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
theorem exists_uniform_measured_probe_regions_oai
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (γ₀ : M.Bases) {cell : Set (F.N.carrier × F.D.carrier)} (hcell : IsCompact cell)
    (hφ : ∀ d, F.action d = M.adjointGroupAutomorphism T F.N.equiv F.ExpN F.isExpN
      hbijN dynkinN (cartanLog H F.D.equiv F.ExpD hbijD d))
    (hpath : ∀ g : G, ∃ γ : ℝ → G, γ 0 = 1 ∧ γ 1 = g ∧
      ∀ t ∈ Icc (0 : ℝ) 1, ∀ u ∈ Icc (0 : ℝ) 1,
        dist (γ t) (γ u) ≤ dist 1 g * |t - u|)
    {Kπ : ℝ} (hKπ : 0 ≤ Kπ)
    (hLip : ∀ x y, ‖(π x).toAdd - (π y).toAdd‖ ≤ Kπ * dist x y)
    (C : Set (H →ₗ[ℝ] ℝ))
    (Q : NilpotentLieModel ((cartanRootIdeal H) ⧸ M.coneWordIdeal C))
    (ExpQ : GroupLieAlgebra (𝓘(ℝ, Q.modelSpace)) Q.carrier → Q.carrier)
    (hExpQ : IsGroupExponential ExpQ) (hbijQ : Function.Bijective ExpQ)
    (haarQ : NilpotentExponentialHaarInput Q.modelSpace Q.carrier)
    (πQ : F.N.carrier →* Q.carrier)
    (hπQ : ∀ v, πQ (F.ExpN (F.N.equiv v)) = ExpQ (Q.equiv (M.coneProjection C v)))
    (chartQ : GroupLieAlgebra (𝓘(ℝ, Q.modelSpace)) Q.carrier ≃ₜ Q.carrier)
    (hchartQ : ∀ v, chartQ v = ExpQ v)
    (μQ : Measure Q.carrier) [μQ.IsHaarMeasure]
    (α : F.D.carrier →* MulAut Q.carrier) (act : G →* Equiv.Perm Q.carrier)
    (hact : ∀ u d q, act (F.inclusionN u * F.inclusionD d) q = πQ u * α d q)
    (I : NilpotentLieModel (M.coneWordIdeal C))
    (ExpI : GroupLieAlgebra (𝓘(ℝ, I.modelSpace)) I.carrier → I.carrier)
    (hExpI : IsGroupExponential ExpI)
    (haarI : NilpotentExponentialHaarInput I.modelSpace I.carrier)
    (ιI : I.carrier →* F.N.carrier) (hιI : Topology.IsClosedEmbedding ιI)
    (hrange : range ιI = (πQ.ker : Set F.N.carrier))
    (hIExp : ∀ i : M.coneWordIdeal C,
      ιI (ExpI (I.equiv i)) = F.ExpN (F.N.equiv (i : cartanRootIdeal H)))
    (μI : Measure I.carrier) [μI.IsHaarMeasure]
    (ν : Measure F.D.carrier) [ν.IsHaarMeasure]
    (haarD : NilpotentExponentialHaarInput F.D.modelSpace F.D.carrier)
    (E₁ E₂ : Set W) (hE₁ : IsCompact E₁) (hne₁ : E₁.Nonempty)
    (hE₂ : IsCompact E₂) (hne₂ : E₂.Nonempty)
    (β₁ : M.Bases)
    (hβ₁ : IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
      (M.boxCost T hunimod eW E₁) β₁.val)
    (hz₁ : ∀ i, (M.weight i : H →ₗ[ℝ] ℝ) ∈ C →
      (M.supportIn T hunimod eW).weightSupport E₁ i = 0)
    (bI₀ : Basis (Fin (finrank ℝ (M.coneWordIdeal C))) ℝ (M.coneWordIdeal C))
    (β₂ : M.ConeIdealBases C)
    (hβ₂ : M.IsMaximizingConeIdealBasis C bI₀
      ((M.supportIn T hunimod eW).weightSupport E₂) β₂)
    (hs₂ : ∀ i, 0 ≤ (M.supportIn T hunimod eW).weightSupport E₂ i)
    (hz₂ : ∀ i, (M.weight i : H →ₗ[ℝ] ℝ) ∈ C →
      (M.supportIn T hunimod eW).weightSupport E₂ i = 0)
    (hp₂ : ∀ i, (M.weight i : H →ₗ[ℝ] ℝ) ∉ C →
      0 < (M.supportIn T hunimod eW).weightSupport E₂ i)
    :
    let μK := Measure.map (kernelRealization πQ ιI hιI hrange) μI
    let P₂ := ∑ j, M.coneIdealWordCost C
      ((M.supportIn T hunimod eW).weightSupport E₂) (β₂.val j)
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ (scale η : ℕ → ℝ),
      StrictMono scale → Tendsto scale atTop atTop →
      (∀ n, 1 ≤ scale n) → (∀ n, 0 ≤ η n) → Tendsto η atTop (𝓝 0) →
      ∀ A B : ℝ, 0 ≤ A → 0 ≤ B →
      ∃ R : MeasuredProbeRegions πQ μQ μK ν scale P₂,
        ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
        ∀ᶠ n in atTop, R.ControlsTwoPaths
          (fun u d => F.inclusionN u * F.inclusionD d) F.action (fun g q => act g q)
          π cell E₁ E₂ η A B δ n := by
  dsimp only
  obtain ⟨bQ, lift, hlift, δ₀, hδ₀, hdata⟩ :=
    M.exists_uniform_two_path_probe_restrictions T F hunimod eW π hπExp chartN hchartN
      chartD hchartD dynkinN dynkinD hbijN hbijD b₀ γ₀ hcell hφ hpath hKπ hLip
      C Q ExpQ hExpQ hbijQ haarQ πQ hπQ μQ α act hact E₁ E₂ hE₁ hne₁ hE₂ hne₂
      β₁ hβ₁ hz₁ bI₀ β₂ hβ₂ hs₂ hz₂ hp₂
  have hqcompat (v : cartanRootIdeal H) : πQ (chartN (F.N.equiv v)) =
      chartQ (Q.equiv ((M.coneWordIdeal C).toSubmodule.mkQ v)) :=
    (congrArg πQ (hchartN (F.N.equiv v))).trans ((hπQ v).trans (hchartQ _).symm)
  have hzQ : chartQ (Q.equiv 0) = 1 :=
    (congrArg chartQ (map_zero Q.equiv)).trans
      ((hchartQ 0).trans hExpQ.map_zero)
  refine ⟨δ₀, hδ₀, ?_⟩
  exact M.measured_probe_regions_of_uniform_lifts F C Q chartN hchartN chartQ πQ
    hqcompat hzQ bQ lift hlift I ExpI hExpI haarI ιI hιI hrange hIExp μI ν haarD hbijD
    ((M.supportIn T hunimod eW).weightSupport E₂) β₂ π act cell E₁ E₂ μQ δ₀ hdata



end PolycyclicRecognition.CartanWordModel

end

end OAI
end

theorem solution : type_of% @OAI.PolycyclicRecognition.CartanWordModel.exists_uniform_measured_probe_regions_oai := @OAI.PolycyclicRecognition.CartanWordModel.exists_uniform_measured_probe_regions_oai
