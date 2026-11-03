-- Prove2me | solution 1 for OAI.PolycyclicRecognition.CartanWordModel.PolarTiledSamplerData.count_le_offset_rate
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-02T22:19:19.549818+00:00
-- url     : https://prove2.me/submissions/e0675136-5764-42de-ac20-edf1cae1f532

import Mathlib
import Definitions.Def_PolycyclicRecognition
import Definitions.Def_OAIQ093D027
import Definitions.Def_OAIQ093D020

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

variable {𝕜 : Type*} [Field 𝕜]

variable {V I J : Type*} [AddCommGroup V] [Module 𝕜 V] (U : Submodule 𝕜 V)
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

theorem maximizingColumnBasis_of_coordinate_support {I : Type*} {n : ℕ}
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

variable {I L : Type*} [LieRing L] [LieAlgebra ℝ L]

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

variable {I L : Type*} [LieRing L] [LieAlgebra ℝ L]

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

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
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

variable {I L : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
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

variable {I J : Type*} [Fintype I] [DecidableEq I]

theorem sum_bracketWordExponent [Fintype J] (s : I → ℝ) (words : J → FreeMagma I) :
    ∑ j, bracketWordExponent s (words j) =
      ∑ i, ((∑ j, bracketWordCount (words j) i : ℕ) : ℝ) * s i := by
  simp only [bracketWordExponent, Nat.cast_sum, Finset.sum_mul]
  exact Finset.sum_comm

end PolycyclicRecognition

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

theorem eval_substituteBracketWord {I J V : Type*} [LieRing V] [LieAlgebra ℝ V]
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

theorem exponent_substituteBracketWord {I J : Type*} [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] (s : J → ℝ) (f : I → FreeMagma J) (w : FreeMagma I) :
    bracketWordExponent s (substituteBracketWord f w) =
      bracketWordExponent (fun i => bracketWordExponent s (f i)) w := by
  induction w using FreeMagma.rec with
  | of i => simp only [substituteBracketWord, bracketWordExponent_of]
  | mul u v hu hv =>
    change bracketWordExponent s (substituteBracketWord f u * substituteBracketWord f v) =
      bracketWordExponent (fun i => bracketWordExponent s (f i)) (u * v)
    simp only [bracketWordExponent_mul, hu, hv]

theorem bracketWordExponent_nonneg {I : Type*} [Fintype I] [DecidableEq I]
    (s : I → ℝ) (hs : ∀ i, 0 ≤ s i) (w : FreeMagma I) :
    0 ≤ bracketWordExponent s w := by
  exact Finset.sum_nonneg fun i _ => mul_nonneg (Nat.cast_nonneg _) (hs i)

namespace CartanWordModel

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {H : LieSubalgebra ℝ L} [H.IsCartanSubalgebra] (M : CartanWordModel H)

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

end CartanWordModel
end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_ConeIdealBoxCalculus
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Product and Haar estimates for the actual cone ideal boxes -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieModule MeasureTheory
open scoped Manifold BigOperators

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {H : LieSubalgebra ℝ L} [H.IsCartanSubalgebra] (M : CartanWordModel H)
  (C : Set (H →ₗ[ℝ] ℝ))

theorem coneIdealWordCost_smul (s : Fin M.letterCount → ℝ) (t : ℝ)
    (w : FreeMagma (M.coneMixedWords C)) :
    M.coneIdealWordCost C (fun i => t * s i) w = t * M.coneIdealWordCost C s w := by
  rw [M.coneIdealWordCost_eq_original, M.coneIdealWordCost_eq_original]
  simp only [bracketWordExponent, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem maximizing_coneIdealBasis_smul
    (b₀ : Basis (Fin (finrank ℝ (M.coneWordIdeal C))) ℝ (M.coneWordIdeal C))
    (s : Fin M.letterCount → ℝ) (β : M.ConeIdealBases C)
    (hβ : M.IsMaximizingConeIdealBasis C b₀ s β) {t : ℝ} (ht : 0 ≤ t) :
    M.IsMaximizingConeIdealBasis C b₀ (fun i => t * s i) β := by
  refine ⟨hβ.1, ?_⟩
  intro d hd
  simp only [columnBasisWeight, M.coneIdealWordCost_smul, ← Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left (hβ.2 d hd) ht

end PolycyclicRecognition.CartanWordModel

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

theorem bracketWordExponent_eq_zero_of_pure {I : Type*} [Fintype I] [DecidableEq I]
    (s : I → ℝ) (outside : I → Prop) (hs : ∀ i, ¬outside i → s i = 0)
    (w : FreeMagma I) (hw : ¬IsMixedWord outside w) : bracketWordExponent s w = 0 := by
  induction w using FreeMagma.rec with
  | of i => exact (bracketWordExponent_of s i).trans (hs i hw)
  | mul u v hu hv =>
    change bracketWordExponent s (u * v) = 0
    rw [bracketWordExponent_mul, hu (fun h => hw (Or.inl h)),
      hv (fun h => hw (Or.inr h)), add_zero]

namespace CartanWordModel

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
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

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
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

/-- The adapted ambient basis has exactly the maximal ideal width sum. -/
theorem exists_cone_adapted_maximal_basis
    (bN : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (bI : Basis (Fin (finrank ℝ (M.coneWordIdeal C))) ℝ (M.coneWordIdeal C))
    (s : Fin M.letterCount → ℝ) (hs : ∀ i, 0 ≤ s i)
    (hzero : ∀ i, (M.weight i : H →ₗ[ℝ] ℝ) ∈ C → s i = 0)
    (β : M.ConeIdealBases C) (hβ : M.IsMaximizingConeIdealBasis C bI s β) :
    ∃ γ : M.Bases,
      IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList bN)
        (fun w => bracketWordExponent s w) γ.val ∧
      columnBasisWeight (fun w : M.wordList => bracketWordExponent s w) γ.val =
        columnBasisWeight (fun w : M.coneIdealWordList C => M.coneIdealWordCost C s w) β.val := by
  obtain ⟨_, _, _, _, _, γ, _, _, hmax, hsum⟩ :=
    M.exists_cone_adapted_maximal_basis_data C bN bI s hs hzero β hβ
  exact ⟨γ, hmax, hsum⟩

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_ConePolarTemplate
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instNonemptyBases _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_nonempty _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polar templates and their exact vanishing directions

The compact unit slice of the negative polar has support zero on the cone
and strictly positive support at every functional outside the cone. These
are the widths used in the cone-ideal covering argument.
-/

noncomputable section
namespace PolycyclicRecognition

open Set Metric
open scoped Pointwise

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [FiniteDimensional ℝ W]

omit [FiniteDimensional ℝ W] in
theorem zero_mem_conePolarTemplate (C : ProperCone ℝ (StrongDual ℝ W)) :
    (0 : W) ∈ conePolarTemplate C := by
  simp [conePolarTemplate]

theorem isCompact_conePolarTemplate (C : ProperCone ℝ (StrongDual ℝ W)) :
    IsCompact (conePolarTemplate C) := by
  have hc : IsClosed {x : W | ∀ β ∈ C, β x ≤ 0} := by
    simp only [ofPred_forall]
    exact isClosed_iInter fun β => isClosed_iInter fun _ =>
      isClosed_le β.continuous continuous_const
  exact (isCompact_closedBall (0 : W) 1).of_isClosed_subset
    ((isClosed_le continuous_norm continuous_const).inter hc) (fun x hx => by
      simpa only [mem_closedBall, dist_zero_right] using hx.1)

omit [FiniteDimensional ℝ W] in
theorem convex_conePolarTemplate (C : ProperCone ℝ (StrongDual ℝ W)) :
    Convex ℝ (conePolarTemplate C) := by
  intro x hx y hy a b ha hb hab
  refine ⟨?_, ?_⟩
  · calc
      ‖a • x + b • y‖ ≤ ‖a • x‖ + ‖b • y‖ := norm_add_le _ _
      _ = a * ‖x‖ + b * ‖y‖ := by simp [norm_smul, Real.norm_eq_abs, abs_of_nonneg ha, abs_of_nonneg hb]
      _ ≤ a * 1 + b * 1 := add_le_add (mul_le_mul_of_nonneg_left hx.1 ha)
        (mul_le_mul_of_nonneg_left hy.1 hb)
      _ = 1 := by linarith
  · intro β hβ
    simpa only [map_add, map_smul, smul_eq_mul, add_zero] using
      add_le_add (mul_nonpos_of_nonneg_of_nonpos ha (hx.2 β hβ))
        (mul_nonpos_of_nonneg_of_nonpos hb (hy.2 β hβ))

/-- Separation and rescaling supply a point with strictly positive evaluation. -/
theorem exists_pos_on_conePolarTemplate (C : ProperCone ℝ (StrongDual ℝ W))
    {β : StrongDual ℝ W} (hβ : β ∉ C) :
    ∃ x ∈ conePolarTemplate C, 0 < β x := by
  obtain ⟨f, hf, hneg⟩ := C.hyperplane_separation_point hβ
  obtain ⟨w, hw⟩ := (topDualPairing ℝ W).flip.toContPerfPair.surjective f
  have heval (α : StrongDual ℝ W) : α w = f α := congrArg (fun g => g α) hw
  let c : ℝ := (‖w‖ + 1)⁻¹
  have hden : 0 < ‖w‖ + 1 := by positivity
  have hc : 0 < c := inv_pos.mpr hden
  refine ⟨c • (-w), ⟨?_, ?_⟩, ?_⟩
  · rw [norm_smul, norm_neg, Real.norm_eq_abs, abs_of_pos hc]
    change (‖w‖ + 1)⁻¹ * ‖w‖ ≤ 1
    exact (inv_mul_le_iff₀ hden).mpr (by linarith)
  · intro α hα
    rw [map_smul, map_neg, smul_eq_mul, heval]
    exact mul_nonpos_of_nonneg_of_nonpos hc.le (neg_nonpos.mpr (hf α hα))
  · rw [map_smul, map_neg, smul_eq_mul, heval]
    exact mul_pos hc (neg_pos.mpr hneg)

theorem conePolarWidth_nonneg (C : ProperCone ℝ (StrongDual ℝ W))
    (β : StrongDual ℝ W) : 0 ≤ conePolarWidth C β := by
  apply le_csSup ((isCompact_conePolarTemplate C).image β.continuous).bddAbove
  exact ⟨0, zero_mem_conePolarTemplate C, β.map_zero⟩

theorem conePolarWidth_eq_zero (C : ProperCone ℝ (StrongDual ℝ W))
    {β : StrongDual ℝ W} (hβ : β ∈ C) : conePolarWidth C β = 0 := by
  apply le_antisymm _ (conePolarWidth_nonneg C β)
  change sSup (β '' conePolarTemplate C) ≤ 0
  have hne : (β '' conePolarTemplate C).Nonempty :=
    ⟨β 0, 0, zero_mem_conePolarTemplate C, rfl⟩
  apply csSup_le hne
  rintro _ ⟨x, hx, rfl⟩
  exact hx.2 β hβ

theorem conePolarWidth_pos (C : ProperCone ℝ (StrongDual ℝ W))
    {β : StrongDual ℝ W} (hβ : β ∉ C) : 0 < conePolarWidth C β := by
  obtain ⟨x, hx, hpos⟩ := exists_pos_on_conePolarTemplate C hβ
  exact hpos.trans_le (le_csSup
    ((isCompact_conePolarTemplate C).image β.continuous).bddAbove ⟨x, hx, rfl⟩)

/-- Dilating the polar template multiplies every supporting width by the
same scalar, so a maximizing word basis works for every positive radius. -/
theorem conePolarWidth_smul (C : ProperCone ℝ (StrongDual ℝ W))
    (β : StrongDual ℝ W) {a : ℝ} (ha : 0 ≤ a) :
    sSup (β '' ((fun x : W => a • x) '' conePolarTemplate C)) =
      a * conePolarWidth C β := by
  have hcompact := isCompact_conePolarTemplate C
  have hne : (conePolarTemplate C).Nonempty := ⟨0, zero_mem_conePolarTemplate C⟩
  obtain ⟨x, hx, heq⟩ := hcompact.exists_sSup_image_eq hne β.continuous.continuousOn
  have him := hcompact.image (show Continuous (fun x : W => a • x) from continuous_const.smul continuous_id)
  apply le_antisymm
  · apply csSup_le ((hne.image _).image β)
    rintro _ ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    rw [map_smul, smul_eq_mul]
    exact mul_le_mul_of_nonneg_left
      (le_csSup (hcompact.image β.continuous).bddAbove ⟨y, hy, rfl⟩) ha
  · change a * sSup (β '' conePolarTemplate C) ≤ _
    rw [heq]
    exact le_csSup (him.image β.continuous).bddAbove
      ⟨a • x, ⟨x, hx, rfl⟩, by simp⟩

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

variable {W I B : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
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

variable {L W : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
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

set_option maxHeartbeats 1000000 in
/-- Every maximizing basis has the same template exponent, including ties. -/
theorem columnBasisWeight_eq_templateSupport_of_maximizing
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (E : Set W) (β : M.Bases)
    (hβ : IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
      (M.boxCost T hunimod e E) β.val) :
    columnBasisWeight (M.boxCost T hunimod e E) β.val =
      (M.supportIn T hunimod e).templateSupport E := by
  obtain ⟨γ, _, hγ⟩ := M.exists_maximizing_box_basis T hunimod e b₀ E
  apply le_antisymm
  · rw [M.columnBasisWeight_boxCost]
    exact (M.supportIn T hunimod e).basisTemplateSupport_le E β
  · rw [← hγ]
    exact hβ.2 γ.val (wordBasis_det_ne_zero M.letter M.wordList b₀ γ)

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanConeIdealExponent
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_nonempty _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The ideal exponent is the full template support exponent -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieModule LieAlgebra Set
open scoped BigOperators

variable {L W : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {H : LieSubalgebra ℝ L} [H.IsCartanSubalgebra] (M : CartanWordModel H)
  {a : ℕ} (T : TriangularAdjoint L a)
  (hunimod : ∀ x : L, LinearMap.trace ℝ L (ad ℝ L x) = 0)
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)

set_option maxHeartbeats 1000000 in
/-- If the cone widths vanish, the pure quotient words contribute zero.
Completing a maximal ideal basis therefore gives exactly `P(E)`. -/
theorem sum_coneIdealCost_eq_templateSupport
    (C : Set (H →ₗ[ℝ] ℝ))
    (bN : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (bI : Basis (Fin (finrank ℝ (M.coneWordIdeal C))) ℝ (M.coneWordIdeal C))
    (E : Set W)
    (hs : ∀ i, 0 ≤ (M.supportIn T hunimod eW).weightSupport E i)
    (hz : ∀ i, (M.weight i : H →ₗ[ℝ] ℝ) ∈ C →
      (M.supportIn T hunimod eW).weightSupport E i = 0)
    (β : M.ConeIdealBases C)
    (hβ : M.IsMaximizingConeIdealBasis C bI
      ((M.supportIn T hunimod eW).weightSupport E) β) :
    (∑ j, M.coneIdealWordCost C ((M.supportIn T hunimod eW).weightSupport E) (β.val j)) =
      (M.supportIn T hunimod eW).templateSupport E := by
  obtain ⟨γ, hγ, hsum⟩ := M.exists_cone_adapted_maximal_basis C bN bI
    ((M.supportIn T hunimod eW).weightSupport E) hs hz β hβ
  have he := M.columnBasisWeight_eq_templateSupport_of_maximizing T hunimod eW bN E γ hγ
  exact hsum.symm.trans he

set_option maxHeartbeats 1000000 in
/-- The target ideal exponent agrees with the source template exponent
under the actual finite template-symmetry label. -/
theorem sum_coneIdealCost_image_templateSymmetry [FiniteDimensional ℝ W]
    (C : Set (H →ₗ[ℝ] ℝ))
    (bN : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (bI : Basis (Fin (finrank ℝ (M.coneWordIdeal C))) ℝ (M.coneWordIdeal C))
    (E : Set W) (hE : IsCompact E) (hne : E.Nonempty) (hconv : Convex ℝ E)
    (A : templateSymmetryGroup (M.supportIn T hunimod eW))
    (hs : ∀ i, 0 ≤ (M.supportIn T hunimod eW).weightSupport (A.val '' E) i)
    (hz : ∀ i, (M.weight i : H →ₗ[ℝ] ℝ) ∈ C →
      (M.supportIn T hunimod eW).weightSupport (A.val '' E) i = 0)
    (β : M.ConeIdealBases C)
    (hβ : M.IsMaximizingConeIdealBasis C bI
      ((M.supportIn T hunimod eW).weightSupport (A.val '' E)) β) :
    (∑ j, M.coneIdealWordCost C
      ((M.supportIn T hunimod eW).weightSupport (A.val '' E)) (β.val j)) =
      (M.supportIn T hunimod eW).templateSupport E :=
  (M.sum_coneIdealCost_eq_templateSupport T hunimod eW C bN bI (A.val '' E) hs hz β hβ).trans
    (A.property E hE hne hconv)

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanPolarProbeTemplates
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finite_templateSymmetryGroup _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.instFiniteRootOffsetConeIndex _root_.OAI.PolycyclicRecognition.instFiniteSubtypeLinearEquivRealIdMemSubgroupLinearSupportSymmetryGroup _root_.OAI.PolycyclicRecognition.instNonemptyRootOffsetConeIndex _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual polar-template widths for the three probe boxes -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra Set

variable {L W : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {H : LieSubalgebra ℝ L} [H.IsCartanSubalgebra] (M : CartanWordModel H)
  {a : ℕ} (T : TriangularAdjoint L a)
  (hunimod : ∀ x : L, LinearMap.trace ℝ L (ad ℝ L x) = 0)
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)

set_option maxHeartbeats 1000000 in
theorem weight_mem_heightConePreimage_iff (K : ProperCone ℝ (StrongDual ℝ W))
    (i : Fin M.letterCount) :
    (M.weight i : H →ₗ[ℝ] ℝ) ∈ heightConePreimage T eW K ↔
      ((M.supportIn T hunimod eW).weight i).toContinuousLinearMap ∈ K := Iff.rfl

set_option maxHeartbeats 1000000 in
/-- The support exponents of the normalized probe templates are exactly
the polar widths multiplied by their radii. -/
theorem weightSupport_polar_smul (K : ProperCone ℝ (StrongDual ℝ W))
    {c : ℝ} (hc : 0 ≤ c) (i : Fin M.letterCount) :
    (M.supportIn T hunimod eW).weightSupport
      ((fun x : W => c • x) '' conePolarTemplate K) i =
      c * conePolarWidth K ((M.supportIn T hunimod eW).weight i).toContinuousLinearMap :=
  conePolarWidth_smul K ((M.supportIn T hunimod eW).weight i).toContinuousLinearMap hc

set_option maxHeartbeats 1000000 in
theorem polar_width_nonneg (K : ProperCone ℝ (StrongDual ℝ W))
    (i : Fin M.letterCount) :
    0 ≤ conePolarWidth K ((M.supportIn T hunimod eW).weight i).toContinuousLinearMap :=
  conePolarWidth_nonneg K _

set_option maxHeartbeats 1000000 in
theorem polar_width_zero (K : ProperCone ℝ (StrongDual ℝ W))
    (i : Fin M.letterCount) (hi : (M.weight i : H →ₗ[ℝ] ℝ) ∈ heightConePreimage T eW K) :
    conePolarWidth K ((M.supportIn T hunimod eW).weight i).toContinuousLinearMap = 0 :=
  conePolarWidth_eq_zero K ((M.weight_mem_heightConePreimage_iff T hunimod eW K i).mp hi)

set_option maxHeartbeats 1000000 in
/-- The normalized source templates satisfy every compactness, convexity
and zero-width condition required by the actual three-chain construction. -/
theorem polar_probe_template_properties (K : ProperCone ℝ (StrongDual ℝ W))
    {c : ℝ} (hc : 0 ≤ c) :
    let E := (fun x : W => c • x) '' conePolarTemplate K
    IsCompact E ∧ Convex ℝ E ∧ (0 : W) ∈ E ∧
      (∀ i, 0 ≤ (M.supportIn T hunimod eW).weightSupport E i) ∧
      ∀ i, (M.weight i : H →ₗ[ℝ] ℝ) ∈ heightConePreimage T eW K →
        (M.supportIn T hunimod eW).weightSupport E i = 0 := by
  dsimp only
  refine ⟨(isCompact_conePolarTemplate K).image (continuous_const.smul continuous_id),
    ?_, ⟨0, zero_mem_conePolarTemplate K, smul_zero c⟩, ?_, ?_⟩
  · rintro _ ⟨u, hu, rfl⟩ _ ⟨v, hv, rfl⟩ a b ha hb hab
    refine ⟨a • u + b • v, convex_conePolarTemplate K hu hv ha hb hab, ?_⟩
    simp only [smul_add, smul_smul, mul_comm c]
  · intro i
    rw [M.weightSupport_polar_smul T hunimod eW K hc]
    exact mul_nonneg hc (M.polar_width_nonneg T hunimod eW K i)
  · intro i hi
    rw [M.weightSupport_polar_smul T hunimod eW K hc,
      M.polar_width_zero T hunimod eW K i hi, mul_zero]

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanTransformedPolarTemplates
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_nonempty _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.instFiniteRootOffsetConeIndex _root_.OAI.PolycyclicRecognition.instNonemptyRootOffsetConeIndex _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual target templates in the offset comparison

The target cone is the inverse image under precomposition by the affine
label. Its vanishing widths and positive ideal widths are consequences of
the source polar template, without requiring the label to preserve a ball.
-/

noncomputable section
namespace PolycyclicRecognition

open Set

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [FiniteDimensional ℝ W]

set_option maxHeartbeats 1000000 in
/-- The exact support width of a transformed and dilated polar template. -/
theorem transformedPolar_width (K : ProperCone ℝ (StrongDual ℝ W))
    (A : W ≃ₗ[ℝ] W) (β : StrongDual ℝ W) {c : ℝ} (hc : 0 ≤ c) :
    sSup (β '' (A '' ((fun x : W => c • x) '' conePolarTemplate K))) =
      c * conePolarWidth K (β.comp A.toLinearMap.toContinuousLinearMap) := by
  rw [image_image]
  exact conePolarWidth_smul K (β.comp A.toLinearMap.toContinuousLinearMap) hc

end PolycyclicRecognition

namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra Set
open scoped BigOperators

variable {L W : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {H : LieSubalgebra ℝ L} [H.IsCartanSubalgebra] (M : CartanWordModel H)
  {a : ℕ} (T : TriangularAdjoint L a)
  (hunimod : ∀ x : L, LinearMap.trace ℝ L (ad ℝ L x) = 0)
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)

set_option maxHeartbeats 1000000 in
theorem weightSupport_transformed_polar (K : ProperCone ℝ (StrongDual ℝ W))
    (A : W ≃ₗ[ℝ] W) {c : ℝ} (hc : 0 ≤ c) (i : Fin M.letterCount) :
    (M.supportIn T hunimod eW).weightSupport
      (A '' ((fun x : W => c • x) '' conePolarTemplate K)) i =
      c * conePolarWidth K
        (((M.supportIn T hunimod eW).weight i).toContinuousLinearMap.comp
          A.toLinearMap.toContinuousLinearMap) :=
  transformedPolar_width K A
    ((M.supportIn T hunimod eW).weight i).toContinuousLinearMap hc

set_option maxHeartbeats 1000000 in
/-- Both target path templates have zero quotient widths and strictly
positive widths outside the pulled-back cone. -/
theorem transformed_polar_width_properties (K : ProperCone ℝ (StrongDual ℝ W))
    (A : W ≃ₗ[ℝ] W) {c : ℝ} (hc : 0 < c) :
    let E := A '' ((fun x : W => c • x) '' conePolarTemplate K)
    let C := heightConePreimage T eW (transformedPolarCone K A)
    IsCompact E ∧ Convex ℝ E ∧ (0 : W) ∈ E ∧
      (∀ i, 0 ≤ (M.supportIn T hunimod eW).weightSupport E i) ∧
      (∀ i, (M.weight i : H →ₗ[ℝ] ℝ) ∈ C →
        (M.supportIn T hunimod eW).weightSupport E i = 0) ∧
      (∀ i, (M.weight i : H →ₗ[ℝ] ℝ) ∉ C →
        0 < (M.supportIn T hunimod eW).weightSupport E i) := by
  dsimp only
  obtain ⟨hcompact, hconv, hzero, _, _⟩ :=
    M.polar_probe_template_properties T hunimod eW K hc.le
  refine ⟨hcompact.image A.continuous_of_finiteDimensional,
    hconv.linear_image A.toLinearMap, ⟨0, hzero, A.map_zero⟩, ?_, ?_, ?_⟩
  · intro i
    rw [M.weightSupport_transformed_polar T hunimod eW K A hc.le i]
    exact mul_nonneg hc.le (conePolarWidth_nonneg K _)
  · intro i hi
    have hi' := (M.weight_mem_heightConePreimage_iff T hunimod eW
      (transformedPolarCone K A) i).mp hi
    change (((M.supportIn T hunimod eW).weight i).toContinuousLinearMap.comp
      A.toLinearMap.toContinuousLinearMap) ∈ K at hi'
    rw [M.weightSupport_transformed_polar T hunimod eW K A hc.le i,
      conePolarWidth_eq_zero K hi', mul_zero]
  · intro i hi
    have hi' : (((M.supportIn T hunimod eW).weight i).toContinuousLinearMap.comp
        A.toLinearMap.toContinuousLinearMap) ∉ K := by
      intro h
      exact hi ((M.weight_mem_heightConePreimage_iff T hunimod eW
        (transformedPolarCone K A) i).mpr h)
    rw [M.weightSupport_transformed_polar T hunimod eW K A hc.le i]
    exact mul_pos hc (conePolarWidth_pos K hi')

set_option maxHeartbeats 1000000 in
/-- The target ideal volume exponent equals the original polar-template
exponent under an actual template-symmetry label. -/
theorem transformed_polar_ideal_exponent (K : ProperCone ℝ (StrongDual ℝ W))
    (A : templateSymmetryGroup (M.supportIn T hunimod eW))
    (bN : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (bI : Basis (Fin (finrank ℝ
      (M.coneWordIdeal (heightConePreimage T eW (transformedPolarCone K A.val)))))
      ℝ (M.coneWordIdeal (heightConePreimage T eW (transformedPolarCone K A.val))))
    {c : ℝ} (hc : 0 < c)
    (β : M.ConeIdealBases (heightConePreimage T eW (transformedPolarCone K A.val)))
    (hβ : M.IsMaximizingConeIdealBasis
      (heightConePreimage T eW (transformedPolarCone K A.val)) bI
      ((M.supportIn T hunimod eW).weightSupport
        (A.val '' ((fun x : W => c • x) '' conePolarTemplate K))) β) :
    (∑ j, M.coneIdealWordCost
      (heightConePreimage T eW (transformedPolarCone K A.val))
      ((M.supportIn T hunimod eW).weightSupport
        (A.val '' ((fun x : W => c • x) '' conePolarTemplate K))) (β.val j)) =
      (M.supportIn T hunimod eW).templateSupport
        ((fun x : W => c • x) '' conePolarTemplate K) := by
  obtain ⟨hcompact, hconv, hzero, _, _⟩ :=
    M.polar_probe_template_properties T hunimod eW K hc.le
  obtain ⟨_, _, _, hs, hz, _⟩ :=
    M.transformed_polar_width_properties T hunimod eW K A.val hc
  exact M.sum_coneIdealCost_image_templateSymmetry T hunimod eW _ bN bI _
    hcompact ⟨0, hzero⟩ hconv A hs hz β hβ

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanPolarOffsetExponents
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_nonempty _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact cancellation of the polar source and target exponents -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra Set
open scoped BigOperators

variable {L W : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {H : LieSubalgebra ℝ L} [H.IsCartanSubalgebra] (M : CartanWordModel H)
  {a : ℕ} (T : TriangularAdjoint L a)
  (hunimod : ∀ x : L, LinearMap.trace ℝ L (ad ℝ L x) = 0)
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)

set_option maxHeartbeats 1000000 in
theorem sum_polar_ideal_cost_smul (K : ProperCone ℝ (StrongDual ℝ W))
    (β : M.ConeIdealBases (heightConePreimage T eW K)) {c : ℝ} (hc : 0 ≤ c) :
    (∑ j, M.coneIdealWordCost (heightConePreimage T eW K)
      ((M.supportIn T hunimod eW).weightSupport
        ((fun x : W => c • x) '' conePolarTemplate K)) (β.val j)) =
      c * ∑ j, M.coneIdealWordCost (heightConePreimage T eW K)
        (M.polarProbeWidths T hunimod eW K) (β.val j) := by
  have he : (M.supportIn T hunimod eW).weightSupport
      ((fun x : W => c • x) '' conePolarTemplate K) =
      fun i => c * M.polarProbeWidths T hunimod eW K i := by
    funext i
    exact M.weightSupport_polar_smul T hunimod eW K hc i
  rw [he]
  simp only [M.coneIdealWordCost_smul, Finset.mul_sum]

set_option maxHeartbeats 1000000 in
/-- The common source maximizing basis computes every polar radius. -/
theorem polar_templateSupport_eq (K : ProperCone ℝ (StrongDual ℝ W))
    (bN : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (bI : Basis (Fin (finrank ℝ (M.coneWordIdeal (heightConePreimage T eW K))))
      ℝ (M.coneWordIdeal (heightConePreimage T eW K)))
    (β : M.ConeIdealBases (heightConePreimage T eW K))
    (hβ : M.IsMaximizingConeIdealBasis (heightConePreimage T eW K) bI
      (M.polarProbeWidths T hunimod eW K) β) {c : ℝ} (hc : 0 ≤ c) :
    (M.supportIn T hunimod eW).templateSupport
      ((fun x : W => c • x) '' conePolarTemplate K) =
      c * ∑ j, M.coneIdealWordCost (heightConePreimage T eW K)
        (M.polarProbeWidths T hunimod eW K) (β.val j) := by
  obtain ⟨_, _, _, hs, hz⟩ := M.polar_probe_template_properties T hunimod eW K hc
  have he : (M.supportIn T hunimod eW).weightSupport
      ((fun x : W => c • x) '' conePolarTemplate K) =
      fun i => c * M.polarProbeWidths T hunimod eW K i := by
    funext i
    exact M.weightSupport_polar_smul T hunimod eW K hc i
  have hβc : M.IsMaximizingConeIdealBasis (heightConePreimage T eW K) bI
      ((M.supportIn T hunimod eW).weightSupport
        ((fun x : W => c • x) '' conePolarTemplate K)) β := by
    rw [he]
    exact M.maximizing_coneIdealBasis_smul _ bI _ β hβ hc
  rw [← M.sum_coneIdealCost_eq_templateSupport T hunimod eW _ bN bI _ hs hz β hβc]
  exact M.sum_polar_ideal_cost_smul T hunimod eW K β hc

set_option maxHeartbeats 1000000 in
/-- Source radius `2ε/3`, target radius `ε/3`, and the actual tiling rate
have exactly matching exponents. The target cone and its dimension may differ. -/
theorem polar_offset_exponent_balance (K : ProperCone ℝ (StrongDual ℝ W))
    (A : templateSymmetryGroup (M.supportIn T hunimod eW))
    (bN : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (bI : Basis (Fin (finrank ℝ (M.coneWordIdeal (heightConePreimage T eW K))))
      ℝ (M.coneWordIdeal (heightConePreimage T eW K)))
    (β : M.ConeIdealBases (heightConePreimage T eW K))
    (hβ : M.IsMaximizingConeIdealBasis (heightConePreimage T eW K) bI
      (M.polarProbeWidths T hunimod eW K) β)
    (bI' : Basis (Fin (finrank ℝ
      (M.coneWordIdeal (heightConePreimage T eW (transformedPolarCone K A.val)))))
      ℝ (M.coneWordIdeal (heightConePreimage T eW (transformedPolarCone K A.val))))
    (β' : M.ConeIdealBases (heightConePreimage T eW (transformedPolarCone K A.val)))
    {ε : ℝ} (hε : 0 < ε)
    (hβ' : M.IsMaximizingConeIdealBasis
      (heightConePreimage T eW (transformedPolarCone K A.val)) bI'
      ((M.supportIn T hunimod eW).weightSupport
        (A.val '' ((fun x : W => (ε / 3) • x) '' conePolarTemplate K))) β') :
    (M.supportIn T hunimod eW).templateSupport
      ((fun x : W => (2 * ε / 3) • x) '' conePolarTemplate K) -
      (∑ j, M.coneIdealWordCost
        (heightConePreimage T eW (transformedPolarCone K A.val))
        ((M.supportIn T hunimod eW).weightSupport
          (A.val '' ((fun x : W => (ε / 3) • x) '' conePolarTemplate K))) (β'.val j)) =
      (ε / 3) * ∑ j, M.coneIdealWordCost (heightConePreimage T eW K)
        (M.polarProbeWidths T hunimod eW K) (β.val j) := by
  rw [M.transformed_polar_ideal_exponent T hunimod eW K A bN bI' (by positivity) β' hβ',
    M.polar_templateSupport_eq T hunimod eW K bN bI β hβ (by positivity),
    M.polar_templateSupport_eq T hunimod eW K bN bI β hβ (by positivity)]
  ring

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanTiledOffsetRates
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_nonempty _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Matching the actual source partition count to the target exponent -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule Set Metric
open scoped Manifold Pointwise

variable {EG G W I : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
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
  (K : ProperCone ℝ (StrongDual ℝ W))
  [Group I] [TopologicalSpace I] [IsTopologicalGroup I]
  [MeasurableSpace I] [BorelSpace I] [SecondCountableTopology I]


local notation "C" => heightConePreimage T eW K

omit [SimplyConnectedSpace G] [Nonempty (Fin M.letterCount)]
    [IsTopologicalGroup I] [BorelSpace I] [SecondCountableTopology I] in
set_option maxHeartbeats 1000000 in
/-- The stored tile count has exactly the source-minus-target exponent,
including when the transformed cone has a different ideal dimension. -/
theorem PolarTiledSamplerData.count_le_offset_rate_oai
    (ExpI : M.coneWordIdeal C → I) (ι : I →* F.N.carrier)
    (bN : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (bI : Basis (Fin (finrank ℝ (M.coneWordIdeal C))) ℝ (M.coneWordIdeal C))
    {ε : ℝ} (hε : 0 < ε) (β : M.ConeIdealBases C)
    (hβ : M.IsMaximizingConeIdealBasis C bI (M.polarProbeWidths T hunimod eW K) β)
    (R : ℝ) (scale : ℕ → ℝ) (φ : ℕ → I ≃ₜ* I)
    (D : M.PolarTiledSamplerData T F hunimod eW K ExpI ι bN ε β R scale φ)
    (A : templateSymmetryGroup (M.supportIn T hunimod eW))
    (bI' : Basis (Fin (finrank ℝ
      (M.coneWordIdeal (heightConePreimage T eW (transformedPolarCone K A.val)))))
      ℝ (M.coneWordIdeal (heightConePreimage T eW (transformedPolarCone K A.val))))
    (β' : M.ConeIdealBases (heightConePreimage T eW (transformedPolarCone K A.val)))
    (hβ' : M.IsMaximizingConeIdealBasis
      (heightConePreimage T eW (transformedPolarCone K A.val)) bI'
      ((M.supportIn T hunimod eW).weightSupport
        (A.val '' normalizedPolarTemplates K ε 2)) β') (n : ℕ) :
    (D.tiles n : ℝ) ≤ R ^ finrank ℝ (M.coneWordIdeal C) * Real.exp (scale n *
      ((M.supportIn T hunimod eW).templateSupport (normalizedPolarTemplates K ε 0) -
        ∑ j, M.coneIdealWordCost
          (heightConePreimage T eW (transformedPolarCone K A.val))
          ((M.supportIn T hunimod eW).weightSupport
            (A.val '' normalizedPolarTemplates K ε 2)) (β'.val j))) := by
  have hb := M.polar_offset_exponent_balance T hunimod eW K A bN bI β hβ bI' β' hε hβ'
  change (M.supportIn T hunimod eW).templateSupport (normalizedPolarTemplates K ε 0) -
    (∑ j, M.coneIdealWordCost
      (heightConePreimage T eW (transformedPolarCone K A.val))
      ((M.supportIn T hunimod eW).weightSupport
        (A.val '' normalizedPolarTemplates K ε 2)) (β'.val j)) = _ at hb
  rw [hb]
  exact D.count n

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

theorem solution.{u_1, u_2, u_3, u_4} : type_of% @OAI.PolycyclicRecognition.CartanWordModel.PolarTiledSamplerData.count_le_offset_rate_oai.{u_1, u_2, u_3, u_4} := @OAI.PolycyclicRecognition.CartanWordModel.PolarTiledSamplerData.count_le_offset_rate_oai.{u_1, u_2, u_3, u_4}
