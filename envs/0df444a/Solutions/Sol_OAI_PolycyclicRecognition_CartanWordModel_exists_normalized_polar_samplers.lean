-- Prove2me | solution 1 for OAI.PolycyclicRecognition.CartanWordModel.exists_normalized_polar_samplers
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-02T22:55:37.774049+00:00
-- url     : https://prove2.me/submissions/6662aeb5-69b2-4d4b-8d68-93eaf91239e6

import Mathlib
import Definitions.Def_PolycyclicRecognition
import Definitions.Def_OAIQ093D027
import Definitions.Def_OAIQ093D020
import Theorems.Thm_OAI_PolycyclicRecognition_CartanWordModel_exists_polar_tiled_probe_chains_from_box

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
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_MixedWordBasis
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite mixed-word spanning pools for the cone ideals -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule Set

variable {L : Type} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {H : LieSubalgebra ℝ L} [H.IsCartanSubalgebra] (M : CartanWordModel H)

theorem coneWordIdeal_eq_span_finite_mixed (C : Set (H →ₗ[ℝ] ℝ)) :
    (M.coneWordIdeal C).toSubmodule =
      Submodule.span ℝ (range (fun w : M.coneMixedWords C => evalBracketWord M.letter w.val)) := by
  classical
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨w, hw, rfl⟩
    by_cases hz : evalBracketWord M.letter w = 0
    · rw [hz]
      exact Submodule.zero_mem _
    · exact Submodule.subset_span
        ⟨⟨⟨w, M.mem_wordList_of_eval_ne_zero w hz⟩, hw⟩, rfl⟩
  · apply Submodule.span_le.mpr
    rintro _ ⟨w, rfl⟩
    exact eval_mixed_mem_span M.letter _ w.property

theorem coneMixedVector_span (C : Set (H →ₗ[ℝ] ℝ)) :
    Submodule.span ℝ (range (M.coneMixedVector C)) = ⊤ := by
  let I := (M.coneWordIdeal C).toSubmodule
  apply Submodule.map_injective_of_injective I.subtype_injective
  rw [Submodule.map_span, Submodule.map_top, I.range_subtype]
  change _ = (M.coneWordIdeal C).toSubmodule
  conv_rhs => rw [M.coneWordIdeal_eq_span_finite_mixed C]
  congr 1
  ext v
  constructor
  · rintro ⟨_, ⟨w, rfl⟩, rfl⟩
    exact ⟨w, rfl⟩
  · rintro ⟨w, rfl⟩
    exact ⟨M.coneMixedVector C w, ⟨w, rfl⟩, rfl⟩

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_RescaledWordSums
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exponential bounds for actual finite word expansions

The maximizing-basis exchange estimate controls every word in the finite
list. A common surplus or deficit in the coefficients passes to the norm
of the whole sum, uniformly over the selected maximizing basis.
-/

noncomputable section

namespace PolycyclicRecognition

open Module
open scoped BigOperators

variable {I L : Type} [LieRing L] [LieAlgebra ℝ L]

/-- All words, rather than just the original letters, have uniformly bounded
coordinates after normalization by their own weight. -/
theorem exists_uniform_rescaled_word_bound
    (X : I → L) (S : Finset (FreeMagma I))
    (b₀ : Basis (Fin (finrank ℝ L)) ℝ L) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (cost : S → ℝ) (β : WordBasisSelections X S),
      IsMaximizingColumnBasis (wordListCoordinates X S b₀) cost β.val →
      ∀ r : ℝ, 0 ≤ r → ∀ w : S,
      ‖(exponentialRescaleBasis (WordBasisSelections.basis X S β)
        (fun j => cost (β.val j)) r).equivFun
          (Real.exp (r * cost w) • evalBracketWord X w)‖ ≤ C := by
  obtain ⟨C, hC, hb⟩ := exists_uniform_normalized_coordinate_bound
    (wordListCoordinates X S b₀)
  refine ⟨C, hC, ?_⟩
  intro cost β hβ r hr w
  apply (pi_norm_le_iff_of_nonneg hC).mpr
  intro j
  change |(exponentialRescaleBasis (WordBasisSelections.basis X S β)
    (fun j => cost (β.val j)) r).repr
      (Real.exp (r * cost w) • evalBracketWord X w) j| ≤ C
  rw [repr_exponentialRescaleBasis_smul]
  have h := hb cost β.val hβ w j r hr
  rw [columnCoordinates_eq_wordBasis_repr X S b₀ β] at h
  exact h

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

theorem coneMixedVector_generates (C : Set (H →ₗ[ℝ] ℝ)) :
    LieSubalgebra.lieSpan ℝ (M.coneWordIdeal C) (Set.range (M.coneMixedVector C)) = ⊤ := by
  apply top_unique
  have hle : Submodule.span ℝ (Set.range (M.coneMixedVector C)) ≤
      (LieSubalgebra.lieSpan ℝ (M.coneWordIdeal C)
        (Set.range (M.coneMixedVector C))).toSubmodule :=
    Submodule.span_le.mpr LieSubalgebra.subset_lieSpan
  rw [M.coneMixedVector_span C] at hle
  exact hle

instance instNonemptyConeIdealBases (C : Set (H →ₗ[ℝ] ℝ)) : Nonempty (M.ConeIdealBases C) :=
  nonempty_wordBasisSelections (M.coneMixedVector C)
    (M.coneIdealWordBound_zero C) (M.coneMixedVector_generates C)

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
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_ConeIdealBoxCalculus
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_nonempty _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
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

variable {L : Type} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {H : LieSubalgebra ℝ L} [H.IsCartanSubalgebra] (M : CartanWordModel H)
  (C : Set (H →ₗ[ℝ] ℝ))

theorem exists_maximizing_coneIdealBasis
    (b₀ : Basis (Fin (finrank ℝ (M.coneWordIdeal C))) ℝ (M.coneWordIdeal C))
    (s : Fin M.letterCount → ℝ) :
    ∃ β, M.IsMaximizingConeIdealBasis C b₀ s β :=
  exists_maximizing_wordBasis _ _ b₀ _

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

variable {E G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace G] [ChartedSpace E G] [Group G]
  [LieGroup (𝓘(ℝ, E)) ⊤ G] [T2Space G]
  (e : M.coneWordIdeal C ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, E)) G)
  (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G) (hExp : IsGroupExponential Exp)

include hExp in
theorem exists_coneIdealBox_product_bound (dynkin : NilpotentDynkinExpansionInput E G)
    (b₀ : Basis (Fin (finrank ℝ (M.coneWordIdeal C))) ℝ (M.coneWordIdeal C)) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (s : Fin M.letterCount → ℝ) (β : M.ConeIdealBases C),
      M.IsMaximizingConeIdealBasis C b₀ s β →
      ∀ r : ℝ, 0 ≤ r → ∀ n : ℕ, ∀ R : ℝ, 0 ≤ R → ∀ g : Fin n → G,
      (∀ i, g i ∈ M.coneIdealBox C (Exp ∘ e) s β r R) →
      (List.ofFn g).prod ∈ M.coneIdealBox C (Exp ∘ e) s β r
        (K * (1 + (n : ℝ)) ^ M.coneIdealWordBound C *
          (1 + R) ^ M.coneIdealWordBound C) := by
  obtain ⟨K, hK, hb⟩ := exists_uniform_word_box_product_bound dynkin e Exp hExp
    (M.coneMixedVector C) (M.coneIdealWordBound_zero C) b₀
  exact ⟨K, hK, fun s β hβ r hr n R hR g hg =>
    hb (fun w => bracketWordExponent s w.val.val) β hβ r hr n R hR g hg⟩

omit [T2Space G] in
include hExp in
theorem coneIdealBox_inv_mem (s : Fin M.letterCount → ℝ) (β : M.ConeIdealBases C)
    (r R : ℝ) {g : G} (hg : g ∈ M.coneIdealBox C (Exp ∘ e) s β r R) :
    g⁻¹ ∈ M.coneIdealBox C (Exp ∘ e) s β r R :=
  inv_mem_exponentialCoordinateBox e Exp hExp (M.coneIdealBoxBasis C s β r) hg

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
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanBoxMaps
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
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

set_option maxHeartbeats 1000000 in
/-- A bound on the images of basis vectors bounds the full linear map in
the coordinate maximum norm. -/
theorem norm_basis_linearMap_le {J : Type} [Fintype J] (b : Basis J ℝ L)
    (F : L →ₗ[ℝ] L) {K : ℝ}
    (hF : ∀ j, ‖b.equivFun (F (b j))‖ ≤ K) (v : L) :
    ‖b.equivFun (F v)‖ ≤ (Fintype.card J : ℝ) * K * ‖b.equivFun v‖ := by
  conv_lhs => rw [← b.sum_repr v]
  rw [map_sum, map_sum]
  apply (norm_sum_le _ _).trans
  calc
    (∑ j, ‖b.equivFun (F (b.repr v j • b j))‖) ≤
        ∑ _j : J, ‖b.equivFun v‖ * K := by
      apply Finset.sum_le_sum
      intro j _
      rw [map_smul, map_smul, norm_smul, Real.norm_eq_abs]
      exact mul_le_mul (norm_le_pi_norm (b.equivFun v) j) (hF j)
        (norm_nonneg _) (norm_nonneg _)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] <;> ring

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_ConeIdealInsideAdjoint
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform ideal-box bounds for an inside adjoint

An inside letter has width zero. Adjoining it to a mixed word leaves the
width unchanged, so maximizing-basis exchange bounds its adjoint uniformly
in every rescaled ideal box.
-/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieModule LieAlgebra

variable {L : Type} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {H : LieSubalgebra ℝ L} [H.IsCartanSubalgebra] (M : CartanWordModel H)
  (C : Set (H →ₗ[ℝ] ℝ))

theorem coneIdealLetterAdjoint_nilpotent (i : Fin M.letterCount) :
    (M.coneIdealLetterAdjoint C i) ^ M.bound = 0 := by
  let D := M.coneIdealLetterAdjoint C i
  have hiter (j : ℕ) (v : M.coneWordIdeal C) :
      ((D ^ j) v : cartanRootIdeal H) =
        (toEnd ℝ (cartanRootIdeal H) (cartanRootIdeal H) (M.letter i))^[j] v := by
    induction j with
    | zero => rfl
    | succ j hj =>
      rw [pow_succ', Module.End.mul_apply, Function.iterate_succ_apply']
      change ⁅M.letter i, ((D ^ j) v : cartanRootIdeal H)⁆ = _
      rw [hj]
      rfl
  apply LinearMap.ext
  intro v
  apply Subtype.ext
  change ((D ^ M.bound) v : cartanRootIdeal H) = 0
  rw [hiter]
  have hz := iterate_toEnd_mem_lowerCentralSeries ℝ (cartanRootIdeal H)
    (cartanRootIdeal H) (M.letter i) (v : cartanRootIdeal H) M.bound
  rw [M.bound_zero] at hz
  exact hz

/-- A uniform bound for the actual restricted adjoint in all maximizing
ideal-box coordinates. The letter need only have zero prescribed width. -/
theorem exists_uniform_coneIdealLetterAdjoint_bound
    (b₀ : Basis (Fin (finrank ℝ (M.coneWordIdeal C))) ℝ (M.coneWordIdeal C)) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (s : Fin M.letterCount → ℝ) (β : M.ConeIdealBases C),
      M.IsMaximizingConeIdealBasis C b₀ s β →
      ∀ (i : Fin M.letterCount), s i = 0 → ∀ r : ℝ, 0 ≤ r →
      ∀ v : M.coneWordIdeal C,
      ‖(M.coneIdealBoxBasis C s β r).equivFun (M.coneIdealLetterAdjoint C i v)‖ ≤
        A * ‖(M.coneIdealBoxBasis C s β r).equivFun v‖ := by
  obtain ⟨K, hK, hword⟩ := exists_uniform_rescaled_word_bound
    (M.coneMixedVector C) (M.coneIdealWordList C) b₀
  refine ⟨(finrank ℝ (M.coneWordIdeal C) : ℝ) * K,
    mul_nonneg (Nat.cast_nonneg _) hK, ?_⟩
  intro s β hβ i hi r hr v
  let b := WordBasisSelections.basis (M.coneMixedVector C) (M.coneIdealWordList C) β
  let br := M.coneIdealBoxBasis C s β r
  let D := M.coneIdealLetterAdjoint C i
  have hbr (j) : br j = Real.exp (r * M.coneIdealWordCost C s (β.val j)) • b j := by
    simp only [br, coneIdealBoxBasis, exponentialRescaleBasis, Basis.unitsSMul_apply,
      Units.smul_def, Units.val_mk0, b]
  have hb (j : Fin (finrank ℝ (M.coneWordIdeal C))) :
      ‖br.equivFun (D (br j))‖ ≤ K := by
    by_cases hz : D (b j) = 0
    · have he : D (br j) = 0 := by
        rw [hbr, map_smul, hz, smul_zero]
      rw [he, map_zero, norm_zero]
      exact hK
    · let u := M.coneOriginalWord C (β.val j)
      have hbu : evalBracketWord M.letter u = (b j : cartanRootIdeal H) := by
        rw [M.coneOriginalWord_eval]
        exact congrArg Subtype.val
          (WordBasisSelections.eval_words (M.coneMixedVector C) (M.coneIdealWordList C) β j)
      have hnonzero : evalBracketWord M.letter (FreeMagma.of i * u) ≠ 0 := by
        rw [evalBracketWord_mul, evalBracketWord_of, hbu]
        exact fun h => hz (Subtype.ext h)
      let w : M.coneMixedWords C :=
        ⟨⟨FreeMagma.of i * u, M.mem_wordList_of_eval_ne_zero _ hnonzero⟩,
          Or.inr (M.coneOriginalWord_mixed C (β.val j))⟩
      have hw : M.coneMixedVector C w = D (b j) := by
        apply Subtype.ext
        change evalBracketWord M.letter (FreeMagma.of i * u) = _
        rw [evalBracketWord_mul, evalBracketWord_of, hbu]
        rfl
      have hmem : FreeMagma.of w ∈ M.coneIdealWordList C := by
        apply (mem_boundedBracketWords _ _).mpr
        change 0 < M.coneIdealWordBound C
        by_contra hn
        have hh := evalBracketWord_eq_zero_of_depth (M.coneMixedVector C)
          (M.coneIdealWordBound_zero C) (FreeMagma.of w)
          (by simpa only [bracketWordDepth] using Nat.le_of_not_gt hn)
        exact hz (hw.symm.trans hh)
      have hcost : M.coneIdealWordCost C s (FreeMagma.of w) =
          M.coneIdealWordCost C s (β.val j) := by
        change bracketWordExponent
          (fun z : M.coneMixedWords C => bracketWordExponent s z.val.val)
          (FreeMagma.of w) = _
        rw [bracketWordExponent_of]
        change bracketWordExponent s (FreeMagma.of i * u) = _
        rw [bracketWordExponent_mul, bracketWordExponent_of, hi, zero_add,
          M.coneIdealWordCost_eq_original]
      have hh := hword (fun z => M.coneIdealWordCost C s z) β hβ r hr
        ⟨FreeMagma.of w, hmem⟩
      change ‖br.equivFun (Real.exp (r * M.coneIdealWordCost C s (FreeMagma.of w)) •
        M.coneMixedVector C w)‖ ≤ K at hh
      rw [hcost, hw] at hh
      rw [hbr, map_smul]
      exact hh
  simpa only [Fintype.card_fin] using norm_basis_linearMap_le br D hb v

end PolycyclicRecognition.CartanWordModel

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
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_NilpotentConjugationDecay
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exponential slack survives polynomial nilpotent conjugation

Choosing the chart margin larger than the nilpotence degree times the
expanded-box exponent allows an operator-norm argument for interior slack.
-/

noncomputable section

namespace PolycyclicRecognition

open Filter
open scoped Topology

/-- A uniformly nilpotent operator can grow exponentially more slowly than
its input contracts. Its exponential still sends that input to zero. -/
theorem nilpotent_exp_apply_tendsto_zero_of_exponent_gap
    {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V] [Nontrivial V]
    (N : ℝ → V →L[ℝ] V) (v : ℝ → V) {m : ℕ}
    (hnil : ∀ r, (N r) ^ (m + 1) = 0)
    {A B α β : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hα : 0 ≤ α)
    (hgap : (m : ℝ) * α < β)
    (hN : ∀ᶠ r : ℝ in atTop, ‖N r‖ ≤ A * Real.exp (α * r))
    (hv : ∀ᶠ r : ℝ in atTop, ‖v r‖ ≤ B * Real.exp (-β * r)) :
    Tendsto (fun r => NormedSpace.exp (N r) (v r)) atTop (𝓝 0) := by
  let C := ((m : ℝ) + 1) * (1 + A) ^ m * 2 ^ m * B
  have hC : 0 ≤ C := by positivity
  have hbound (r : ℝ) (hr : 0 ≤ r)
      (hNr : ‖N r‖ ≤ A * Real.exp (α * r))
      (hvr : ‖v r‖ ≤ B * Real.exp (-β * r)) :
      ‖NormedSpace.exp (N r) (v r)‖ ≤ C * Real.exp (((m : ℝ) * α - β) * r) := by
    have hexp : 1 ≤ Real.exp (α * r) := Real.one_le_exp (mul_nonneg hα hr)
    have hbase : 1 + ‖N r‖ ≤ (1 + A) * Real.exp (α * r) := by
      nlinarith [hNr]
    have he := norm_exp_smul_nilpotent_le (N r) (hnil r) (t := 1) zero_le_one
    simp only [one_smul, one_add_one_eq_two] at he
    calc
      _ ≤ ‖NormedSpace.exp (N r)‖ * ‖v r‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ (((m : ℝ) + 1) * (1 + ‖N r‖) ^ m * 2 ^ m) *
          (B * Real.exp (-β * r)) := mul_le_mul he hvr (norm_nonneg _) (by positivity)
      _ ≤ (((m : ℝ) + 1) * ((1 + A) * Real.exp (α * r)) ^ m * 2 ^ m) *
          (B * Real.exp (-β * r)) := by gcongr
      _ = _ := by
        rw [mul_pow, ← Real.exp_nat_mul]
        calc
          _ = C * (Real.exp ((m : ℝ) * (α * r)) * Real.exp (-β * r)) := by dsimp [C] <;> ring
          _ = _ := by rw [← Real.exp_add]; congr 2; ring
  have hlim : Tendsto (fun r : ℝ => C * Real.exp (((m : ℝ) * α - β) * r)) atTop (𝓝 0) := by
    have ht : Tendsto (fun r : ℝ => ((m : ℝ) * α - β) * r) atTop atBot :=
      (tendsto_const_mul_atBot_of_neg (sub_neg.mpr hgap)).mpr tendsto_id
    simpa using tendsto_const_nhds.mul (Real.tendsto_exp_atBot.comp ht)
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero' (Filter.Eventually.of_forall (fun _ => norm_nonneg _)) _ hlim
  filter_upwards [eventually_ge_atTop (0 : ℝ), hN, hv] with r hr hNr hvr
  exact hbound r hr hNr hvr

/-- The same exponential gap absorbs a common subexponential envelope in
both the conjugating operator and the translated vector. -/
theorem nilpotent_exp_apply_tendsto_zero_of_subexponential_bounds
    {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V] [Nontrivial V]
    (N : ℝ → V →L[ℝ] V) (v : ℝ → V) {m : ℕ}
    (hnil : ∀ r, (N r) ^ (m + 1) = 0)
    {A B α β : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hα : 0 ≤ α)
    (hgap : (m : ℝ) * α < β)
    (ε : ℝ → ℝ) (hε : Tendsto ε atTop (𝓝 0))
    (hN : ∀ᶠ r : ℝ in atTop, ‖N r‖ ≤ A * Real.exp ((α + ε r) * r))
    (hv : ∀ᶠ r : ℝ in atTop, ‖v r‖ ≤ B * Real.exp ((-β + ε r) * r)) :
    Tendsto (fun r => NormedSpace.exp (N r) (v r)) atTop (𝓝 0) := by
  let δ := (β - (m : ℝ) * α) / (2 * ((m : ℝ) + 1))
  have hδ : 0 < δ := div_pos (sub_pos.mpr hgap) (by positivity)
  have hδε : ∀ᶠ r : ℝ in atTop, ε r < δ := hε.eventually (eventually_lt_nhds hδ)
  have hδeq : δ * (2 * ((m : ℝ) + 1)) = β - (m : ℝ) * α := by
    dsimp [δ]
    field_simp
  have hgap' : (m : ℝ) * (α + δ) < β - δ := by nlinarith
  apply nilpotent_exp_apply_tendsto_zero_of_exponent_gap N v hnil hA hB
    (by positivity : 0 ≤ α + δ) hgap'
  · filter_upwards [hN, hδε, eventually_ge_atTop (0 : ℝ)] with r hr he hr0
    exact hr.trans (mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (by nlinarith)) hA)
  · filter_upwards [hv, hδε, eventually_ge_atTop (0 : ℝ)] with r hr he hr0
    exact hr.trans (mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (by nlinarith)) hB)

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
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_NilpotentCoordinateFlow
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Nilpotent linear flows in changing box coordinates -/

noncomputable section
namespace PolycyclicRecognition

open Module Filter
open scoped Topology BigOperators

variable {V : Type} [AddCommGroup V] [Module ℝ V] {n : ℕ}

theorem coordinateEnd_pow_apply (b : Basis (Fin n) ℝ V) (D : Module.End ℝ V)
    (k : ℕ) (v : V) : (coordinateEnd b D ^ k) (b.equivFun v) = b.equivFun ((D ^ k) v) := by
  induction k with
  | zero => rfl
  | succ k hk =>
    rw [pow_succ', pow_succ', mul_apply_eq_comp, Module.End.mul_apply,
      hk, coordinateEnd_apply, LinearEquiv.symm_apply_apply]

theorem coordinateEnd_pow_zero (b : Basis (Fin n) ℝ V) (D : Module.End ℝ V)
    {k : ℕ} (hD : D ^ k = 0) : coordinateEnd b D ^ k = 0 := by
  apply ContinuousLinearMap.ext
  intro x
  obtain ⟨v, rfl⟩ := b.equivFun.surjective x
  simp only [coordinateEnd_pow_apply, hD, LinearMap.zero_apply, map_zero,
    zero_apply]

theorem finiteEndFlow_smul (D : Module.End ℝ V) (k : ℕ) (a t : ℝ) (v : V) :
    finiteEndFlow (a • D) k t v = finiteEndFlow D k (a * t) v := by
  simp only [finiteEndFlow, smul_pow, LinearMap.smul_apply, smul_smul, mul_pow]
  apply Finset.sum_congr rfl
  intro p _
  congr 1
  ring

theorem coordinate_finiteEndFlow (b : Basis (Fin n) ℝ V) (D : Module.End ℝ V)
    {k : ℕ} (hD : D ^ k = 0) (t : ℝ) (v : V) :
    b.equivFun (finiteEndFlow D k t v) =
      NormedSpace.exp (t • coordinateEnd b D) (b.equivFun v) := by
  have hzero : (t • coordinateEnd b D) ^ k = 0 := by
    rw [smul_pow, coordinateEnd_pow_zero b D hD, smul_zero]
  rw [exp_eq_finite_sum_of_pow_eq_zero _ hzero]
  simp only [finiteEndFlow, map_sum, map_smul, sum_apply,
    smul_apply, smul_pow, coordinateEnd_pow_apply, smul_smul]

/-- Uniformity over the shrinking input ball follows from the same
nilpotent exponential estimate, by choosing a violating vector if one exists. -/
theorem eventually_uniform_nilpotent_exp_ball [Nonempty (Fin n)]
    (D : ℝ → (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) (t : ℝ → ℝ) {m : ℕ}
    (hD : ∀ r, D r ^ (m + 1) = 0) {A α η : ℝ}
    (hA : 0 ≤ A) (hα : 0 ≤ α) (hgap : (m : ℝ) * α < η)
    (ε : ℝ → ℝ) (hε : Tendsto ε atTop (𝓝 0))
    (hbound : ∀ᶠ r in atTop, ‖D r‖ ≤ A)
    (ht : ∀ᶠ r in atTop, |t r| ≤ Real.exp ((α + ε r) * r)) :
    ∀ᶠ r in atTop, ∀ v : Fin n → ℝ, ‖v‖ ≤ Real.exp (-η * r) →
      ‖NormedSpace.exp (t r • D r) v‖ ≤ 1 := by
  classical
  let P := fun r (v : Fin n → ℝ) =>
    ‖v‖ ≤ Real.exp (-η * r) ∧ 1 < ‖NormedSpace.exp (t r • D r) v‖
  let v : ℝ → Fin n → ℝ := fun r => if h : ∃ x, P r x then h.choose else 0
  have hv (r : ℝ) : ‖v r‖ ≤ Real.exp (-η * r) := by
    dsimp only [v]
    split_ifs with h
    · exact h.choose_spec.1
    · simpa only [norm_zero] using (Real.exp_pos (-η * r)).le
  have hn (r : ℝ) : (t r • D r) ^ (m + 1) = 0 := by
    rw [smul_pow, hD, smul_zero]
  have hb : ∀ᶠ r in atTop, ‖t r • D r‖ ≤ A * Real.exp ((α + |ε r|) * r) := by
    filter_upwards [hbound, ht, eventually_ge_atTop (0 : ℝ)] with r hr ht hr0
    rw [norm_smul, Real.norm_eq_abs]
    apply (mul_le_mul ht hr (norm_nonneg _) (Real.exp_pos _).le).trans
    rw [mul_comm _ A]
    apply mul_le_mul_of_nonneg_left _ hA
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right
      (by linarith [le_abs_self (ε r)]) hr0)
  have hv' : ∀ᶠ r in atTop, ‖v r‖ ≤ 1 * Real.exp ((-η + |ε r|) * r) := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with r hr
    rw [one_mul]
    exact (hv r).trans (Real.exp_le_exp.mpr (by nlinarith [abs_nonneg (ε r)]))
  have hlim := nilpotent_exp_apply_tendsto_zero_of_subexponential_bounds
    (fun r => t r • D r) v hn hA zero_le_one hα hgap
    (fun r => |ε r|) (by simpa using hε.abs) hb hv'
  have hsmall : ∀ᶠ r in atTop, ‖NormedSpace.exp (t r • D r) (v r)‖ < 1 := by
    exact hlim.norm.eventually (eventually_lt_nhds (by simp))
  filter_upwards [hsmall] with r hr x hx
  by_contra h
  have hex : ∃ x, P r x := ⟨x, hx, lt_of_not_ge h⟩
  have hp : P r (v r) := by simpa only [v, dite_eq_left hex] using hex.choose_spec
  exact (not_lt_of_ge hp.2.le) hr

end PolycyclicRecognition

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

theorem norm_coneIdealBoxBasis_strict_width
    (s : Fin M.letterCount → ℝ) (β : M.ConeIdealBases C)
    {a b lo r : ℝ} (hab : a ≤ b) (hr : 0 ≤ r)
    (hlo : ∀ w : M.coneIdealWordList C, lo ≤ M.coneIdealWordCost C s w)
    (v : M.coneWordIdeal C) :
    ‖(M.coneIdealBoxBasis C (fun i => b * s i) β r).equivFun v‖ ≤
      Real.exp (-((b - a) * lo) * r) *
        ‖(M.coneIdealBoxBasis C (fun i => a * s i) β r).equivFun v‖ := by
  unfold coneIdealBoxBasis
  rw [mul_comm (-((b - a) * lo)) r]
  apply norm_change_exponentialRescaleBasis_le _ _ _ hr _ v
  intro j
  rw [M.coneIdealWordCost_smul, M.coneIdealWordCost_smul]
  have hh := mul_le_mul_of_nonpos_left (hlo (β.val j)) (sub_nonpos.mpr hab)
  nlinarith

/-- For a fixed strict width gap, all logarithmic conjugating times below
the corresponding exponential threshold send the whole unit box into the
larger unit box. Negative times are included. -/
theorem coneIdealLetterFlow_absorbed
    (b₀ : Basis (Fin (finrank ℝ (M.coneWordIdeal C))) ℝ (M.coneWordIdeal C))
    (s : Fin M.letterCount → ℝ) (β : M.ConeIdealBases C)
    (hβ : M.IsMaximizingConeIdealBasis C b₀ s β)
    (i : Fin M.letterCount) (hi : s i = 0)
    {a b lo α : ℝ} (ha : 0 ≤ a) (hab : a < b) (hα : 0 ≤ α)
    (hlo : ∀ w : M.coneIdealWordList C, lo ≤ M.coneIdealWordCost C s w)
    (hgap : (M.bound : ℝ) * α < (b - a) * lo)
    (t ε : ℝ → ℝ) (hε : Tendsto ε atTop (𝓝 0))
    (ht : ∀ᶠ r in atTop, |t r| ≤ Real.exp ((α + ε r) * r)) :
    ∀ᶠ r in atTop, ∀ v : M.coneWordIdeal C,
      ‖(M.coneIdealBoxBasis C (fun j => a * s j) β r).equivFun v‖ ≤ 1 →
      ‖(M.coneIdealBoxBasis C (fun j => b * s j) β r).equivFun
        (M.coneIdealLetterFlow C i (t r) v)‖ ≤ 1 := by
  cases isEmpty_or_nonempty (Fin (finrank ℝ (M.coneWordIdeal C))) with
  | inl he =>
    exact Filter.Eventually.of_forall fun r v _ => by
      have hz := Subsingleton.elim
        ((M.coneIdealBoxBasis C (fun j => b * s j) β r).equivFun
          (M.coneIdealLetterFlow C i (t r) v))
        (0 : Fin (finrank ℝ (M.coneWordIdeal C)) → ℝ)
      rw [hz, norm_zero]
      exact zero_le_one
  | inr he =>
    obtain ⟨A, hA, hbound⟩ := M.exists_uniform_coneIdealLetterAdjoint_bound C b₀
    let br := fun r => M.coneIdealBoxBasis C (fun j => b * s j) β r
    let D := M.coneIdealLetterAdjoint C i
    have hpow : D ^ (M.bound + 1) = 0 := by
      rw [pow_succ, M.coneIdealLetterAdjoint_nilpotent, zero_mul]
    have hDr (r : ℝ) : coordinateEnd (br r) D ^ (M.bound + 1) = 0 :=
      coordinateEnd_pow_zero (br r) D hpow
    have hbd : ∀ᶠ r in atTop, ‖coordinateEnd (br r) D‖ ≤ A := by
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with r hr
      apply ContinuousLinearMap.opNorm_le_bound _ hA
      intro x
      have hh := hbound (fun j => b * s j) β
        (M.maximizing_coneIdealBasis_smul C b₀ s β hβ (ha.trans hab.le))
        i (by rw [hi, mul_zero]) r hr ((br r).equivFun.symm x)
      change ‖(br r).equivFun (D ((br r).equivFun.symm x))‖ ≤
        A * ‖(br r).equivFun ((br r).equivFun.symm x)‖ at hh
      simpa only [coordinateEnd_apply, LinearEquiv.apply_symm_apply] using hh
    have hsmall := eventually_uniform_nilpotent_exp_ball
      (fun r => coordinateEnd (br r) D) t hDr hA hα hgap ε hε hbd ht
    filter_upwards [hsmall, eventually_ge_atTop (0 : ℝ)] with r hsmall hr v hv
    have hvr : ‖(br r).equivFun v‖ ≤ Real.exp (-((b - a) * lo) * r) := by
      exact (M.norm_coneIdealBoxBasis_strict_width C s β hab.le hr hlo v).trans
        (by simpa only [mul_one] using
          mul_le_mul_of_nonneg_left hv (Real.exp_pos (-((b - a) * lo) * r)).le)
    have hh := hsmall ((br r).equivFun v) hvr
    rw [← coordinate_finiteEndFlow (br r) D (M.coneIdealLetterAdjoint_nilpotent C i)] at hh
    exact hh

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_ConeIdealGroupConjugation
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Strict-width inclusions for actual group conjugation -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieModule LieAlgebra Filter
open scoped Topology

variable {L : Type} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {H : LieSubalgebra ℝ L} [H.IsCartanSubalgebra] (M : CartanWordModel H)
  (C : Set (H →ₗ[ℝ] ℝ))

variable {G A : Type} [Group G] [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

attribute [local instance 100] LieRing.ofAssociativeRing

variable
  (Exp : cartanRootIdeal H → G) (j : cartanRootIdeal H →ₗ⁅ℝ⁆ A)
  (ρ : G →* Aˣ) (hρ : Function.Injective ρ)
  (hmatch : ∀ x, ρ (Exp x) = algebraExpUnit (j x))

attribute [local instance] OAI.PolycyclicRecognition.CartanWordModel.instNormedAddCommGroupSubtypeMemLieIdealRealCartanRootIdeal
attribute [local instance] OAI.PolycyclicRecognition.CartanWordModel.instNormedSpaceRealSubtypeMemLieIdealCartanRootIdeal
include hρ hmatch in
/-- The flow in the width estimate is precisely conjugation by the
corresponding generator exponential in the actual group. -/
theorem coneIdealLetterFlow_exp_conjugation (i : Fin M.letterCount)
    (t : ℝ) (v : M.coneWordIdeal C) :
    Exp (M.coneIdealLetterFlow C i t v : cartanRootIdeal H) =
      Exp (t • M.letter i) * Exp (v : cartanRootIdeal H) * (Exp (t • M.letter i))⁻¹ := by
  let D := toEnd ℝ (cartanRootIdeal H) (cartanRootIdeal H) (M.letter i)
  have hD : D ^ M.bound = 0 := by
    apply LinearMap.ext
    intro x
    rw [Module.End.pow_apply, LinearMap.zero_apply]
    have hx := iterate_toEnd_mem_lowerCentralSeries ℝ (cartanRootIdeal H)
      (cartanRootIdeal H) (M.letter i) x M.bound
    rw [M.bound_zero] at hx
    exact hx
  have hm := finiteEndFlow_map (M.coneWordIdeal C).incl.toLinearMap
    (M.coneIdealLetterAdjoint C i) D (fun _ => rfl) M.bound t v
  change Exp ((M.coneWordIdeal C).incl (finiteEndFlow
    (M.coneIdealLetterAdjoint C i) M.bound t v)) = _
  calc
    _ = Exp (finiteEndFlow D M.bound t (v : cartanRootIdeal H)) := congrArg Exp hm
    _ = _ := by
      rw [finiteEndFlow_eq_exp D hD]
      exact exp_ad_eq_group_conjugation Exp j ρ hρ hmatch (M.letter i) v t

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_ConeIdealInnerAutomorphism
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The ambient nilpotent inner action on the cone ideal

Every ambient adjoint restricts to a nilpotent derivation of the actual
ideal. Its finite exponential is a Lie automorphism with determinant one.
-/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieModule LieAlgebra

variable {L : Type} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {H : LieSubalgebra ℝ L} [H.IsCartanSubalgebra] (M : CartanWordModel H)
  (C : Set (H →ₗ[ℝ] ℝ))

theorem coneIdealInnerAutomorphism_letter (i : Fin M.letterCount) (t : ℝ)
    (v : M.coneWordIdeal C) :
    M.coneIdealInnerAutomorphism C (t • M.letter i) v =
      M.coneIdealLetterFlow C i t v := by
  rw [M.coneIdealInnerAutomorphism_apply]
  change finiteEndFlow (toEnd ℝ (cartanRootIdeal H) (M.coneWordIdeal C)
    (t • M.letter i)) M.bound 1 v = _
  rw [map_smul, finiteEndFlow_smul, mul_one]
  rfl

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_ConePolarTemplate
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instNonemptyBases _root_.OAI.PolycyclicRecognition.CartanWordModel.instNonemptyConeIdealBases _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_nonempty _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
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

variable {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W]
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
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_SequenceRealExtension
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instNonemptyBases _root_.OAI.PolycyclicRecognition.CartanWordModel.instNonemptyConeIdealBases _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_nonempty _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
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

/-- The same extension transports the exponentially bounded inside-letter
parameters, together with their actual vanishing errors. -/
theorem sequenceRealExtension_eventually_abs_le_exp
    (scale : ℕ → ℝ) (hs : StrictMono scale) (t ε : ℕ → ℝ) (a : ℝ)
    (ht : ∀ᶠ n in atTop, |t n| ≤ Real.exp ((a + ε n) * scale n)) :
    ∀ᶠ r in atTop, |sequenceRealExtension scale t r| ≤
      Real.exp ((a + sequenceRealExtension scale ε r) * r) := by
  classical
  obtain ⟨N, hN⟩ := eventually_atTop.mp ht
  filter_upwards [eventually_ge_atTop (scale N)] with r hr
  by_cases h : ∃ n, scale n = r
  · obtain ⟨n, rfl⟩ := h
    rw [sequenceRealExtension_apply scale hs, sequenceRealExtension_apply scale hs]
    exact hN n (hs.le_iff_le.mp hr)
  · simp only [sequenceRealExtension, dite_eq_right h, abs_zero]
    exact (Real.exp_pos _).le

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
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_SectionWeightedBoxes
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.CartanFactorModel.realScaleProfile_apply _root_.OAI.PolycyclicRecognition.basisDynkinParameter_zero _root_.OAI.PolycyclicRecognition.dynkinRightTranslation_apply _root_.OAI.PolycyclicRecognition.dynkinRightTranslation_symm_apply _root_.OAI.PolycyclicRecognition.exponentialHomOfDynkin_apply_exp _root_.OAI.PolycyclicRecognition.exponentialQuotientSection_apply _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
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

variable {V I J : Type} [LieRing V] [LieAlgebra ℝ V] [Fintype I] [Fintype J]
  (U : LieIdeal ℝ V) (bI : Basis I ℝ U) (bQ : Basis J ℝ (V ⧸ U.toSubmodule))
  (lift : J → V) (hlift : ∀ j, U.toSubmodule.mkQ (lift j) = bQ j)

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

include hcoeff hmul hC in
/-- Conversely, the product of a weighted ideal box and a bounded pure
quotient section lies in the full box with one uniform polynomial loss. -/
theorem weighted_section_box_product
    (hbr : ∀ r : ℝ, 0 ≤ r → ∀ i j k, |(Br r).repr ⁅Br r i, Br r j⁆ k| ≤ C)
    (r R : ℝ) (hr : 0 ≤ r) (hR : 0 ≤ R)
    (u : U) (q : V ⧸ U.toSubmodule)
    (hu : ‖(exponentialRescaleBasis bI cost r).equivFun u‖ ≤ R)
    (hq : ‖bQ.equivFun q‖ ≤ R) :
    ExpN (u : V) * ExpN (quotientLinearSection U bQ lift q) ∈
      exponentialCoordinateBox ExpN (Br r) (K * (1 + R) ^ c) := by
  let v := finiteDynkinPolynomial coeff ![(u : V), quotientLinearSection U bQ lift q]
  refine ⟨v, hmul _ _, ?_⟩
  have hi := (ideal_scaled_coordinates_le_iff U bI bQ lift hlift cost r R hR u).mpr hu
  have hs := section_scaled_coordinates_le U bI bQ lift hlift cost r R hR q hq
  have hvec : ∀ k : Fin 2,
      ‖(Br r).equivFun (![(u : V), quotientLinearSection U bQ lift q] k)‖ ≤ R := by
    intro k
    fin_cases k
    · exact hi
    · exact hs
  exact (norm_finiteDynkinPolynomial_le (Br r) coeff hcoeff _ hC hR (hbr r hr) hvec).trans_eq
    (by dsimp [sectionDynkinConstant] <;> norm_num <;> ring)

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
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_FiniteTranslateCover
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_countable _root_.OAI.PolycyclicRecognition.finitelyGeneratedSubgroupIndex_countable _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite translate coverings from a Haar-volume ratio -/

noncomputable section
namespace PolycyclicRecognition

open MeasureTheory Set
open scoped ENNReal Pointwise

variable {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul G]

theorem disjoint_translate_card_mul_le (μ : Measure G) [μ.IsMulLeftInvariant]
    (S Q R : Set G) (hQ : MeasurableSet Q)
    (hcontain : ∀ a ∈ S, a • Q ⊆ R)
    (t : Finset G) (ht : (t : Set G) ⊆ S)
    (hdisj : (t : Set G).PairwiseDisjoint (fun a => a • Q)) :
    (t.card : ℝ≥0∞) * μ Q ≤ μ R := by
  calc
    (t.card : ℝ≥0∞) * μ Q = μ (⋃ a ∈ t, a • Q) := by
      rw [measure_biUnion_finset hdisj (fun a _ => hQ.const_smul a)]
      simp only [measure_smul, Finset.sum_const, nsmul_eq_mul]
    _ ≤ μ R := measure_mono (iUnion₂_subset fun a ha => hcontain a (ht ha))

/-- A finite maximal disjoint family exists because every such family has
cardinality bounded by the containing region's volume. Its doubled tiles
cover every allowed anchor. -/
theorem exists_finite_translate_cover (μ : Measure G) [μ.IsMulLeftInvariant]
    (S Q R : Set G) (hQ : MeasurableSet Q)
    (hQ0 : μ Q ≠ 0) (hQtop : μ Q ≠ ⊤) (hRtop : μ R ≠ ⊤)
    (hcontain : ∀ a ∈ S, a • Q ⊆ R) :
    ∃ t : Finset G, (t : Set G) ⊆ S ∧
      (t : Set G).PairwiseDisjoint (fun a => a • Q) ∧
      (t.card : ℝ≥0∞) * μ Q ≤ μ R ∧
      S ⊆ ⋃ a ∈ t, a • (Q * Q⁻¹) := by
  classical
  obtain ⟨N, hN⟩ := exists_nat_ge ((μ R).toReal / (μ Q).toReal)
  have hbound (t : Finset G) (ht : (t : Set G) ⊆ S)
      (hd : (t : Set G).PairwiseDisjoint (fun a => a • Q)) : t.card ≤ N := by
    have hc := disjoint_translate_card_mul_le μ S Q R hQ hcontain t ht hd
    have hr := ENNReal.toReal_mono hRtop hc
    have hr' : (t.card : ℝ) * (μ Q).toReal ≤ (μ R).toReal := by
      simpa only [ENNReal.toReal_mul, ENNReal.toReal_natCast] using hr
    have hh := (le_div_iff₀ (ENNReal.toReal_pos hQ0 hQtop)).mpr hr'
    exact_mod_cast hh.trans hN
  let P (k : ℕ) := ∃ t : Finset G, (t : Set G) ⊆ S ∧
    (t : Set G).PairwiseDisjoint (fun a => a • Q) ∧ t.card = k
  have hP0 : P 0 := ⟨∅, by simp, by simp, by simp⟩
  obtain ⟨t, hts, hd, hcard⟩ := Nat.findGreatest_spec (Nat.zero_le N) hP0
  have hmax (u : Finset G) (hu : (u : Set G) ⊆ S)
      (hud : (u : Set G).PairwiseDisjoint (fun a => a • Q)) : u.card ≤ t.card := by
    rw [hcard]
    exact Nat.le_findGreatest (hbound u hu hud) ⟨u, hu, hud, rfl⟩
  refine ⟨t, hts, hd, disjoint_translate_card_mul_le μ S Q R hQ hcontain t hts hd, ?_⟩
  intro x hx
  have hinter : ∃ a ∈ t, ¬Disjoint (x • Q) (a • Q) := by
    by_contra hn
    have hxdisj : ∀ a ∈ t, Disjoint (x • Q) (a • Q) := by simpa using hn
    have hxt : x ∉ t := by
      intro hxt
      obtain ⟨q, hq⟩ := nonempty_of_measure_ne_zero hQ0
      have hpoint : x * q ∈ x • Q := mem_smul_set.mpr ⟨q, hq, rfl⟩
      exact Set.disjoint_left.mp (hxdisj x hxt) hpoint hpoint
    have hi : ((insert x t : Finset G) : Set G) ⊆ S := by
      intro a ha
      rcases Finset.mem_insert.mp ha with rfl | ha
      · exact hx
      · exact hts ha
    have hdi : ((insert x t : Finset G) : Set G).PairwiseDisjoint (fun a => a • Q) := by
      intro a ha b hb hab
      rcases Finset.mem_insert.mp ha with hax | hat
      · subst a
        rcases Finset.mem_insert.mp hb with hbx | hbt
        · exact (hab hbx.symm).elim
        · exact hxdisj b hbt
      · rcases Finset.mem_insert.mp hb with hbx | hbt
        · subst b
          exact (hxdisj a hat).symm
        · exact hd hat hbt hab
    have hh := hmax (insert x t) hi hdi
    rw [Finset.card_insert_of_notMem hxt] at hh
    omega
  obtain ⟨a, ha, hint⟩ := hinter
  obtain ⟨z, hzx, hza⟩ := Set.not_disjoint_iff.mp hint
  obtain ⟨q, hq, hqz⟩ := mem_smul_set.mp hzx
  obtain ⟨p, hp, hpz⟩ := mem_smul_set.mp hza
  have he : x = a * (p * q⁻¹) := by
    have hh : x * q = a * p := hqz.trans hpz.symm
    calc
      x = (x * q) * q⁻¹ := by group
      _ = (a * p) * q⁻¹ := by rw [hh]
      _ = a * (p * q⁻¹) := mul_assoc _ _ _
  refine mem_iUnion.mpr ⟨a, mem_iUnion.mpr ⟨ha, ?_⟩⟩
  exact mem_smul_set.mpr ⟨p * q⁻¹, Set.mul_mem_mul hp (Set.inv_mem_inv.mpr hq), he.symm⟩

theorem measurable_partition_of_finite_cover {X : Type} [MeasurableSpace X] {n : ℕ}
    (S : Set X) (hS : MeasurableSet S) (U : Fin n → Set X)
    (hU : ∀ i, MeasurableSet (U i)) (hcover : S ⊆ ⋃ i, U i) :
    ∃ T : Fin n → Set X, (∀ i, MeasurableSet (T i)) ∧
      Pairwise (fun i j => Disjoint (T i) (T j)) ∧
      (⋃ i, T i) = S ∧ ∀ i, T i ⊆ S ∩ U i := by
  let f := fun i => S ∩ U i
  refine ⟨disjointed f, ?_, disjoint_disjointed f, ?_, disjointed_subset f⟩
  · intro i
    rw [disjointed_eq_inter_compl]
    exact (hS.inter (hU i)).inter
      (MeasurableSet.iInter fun j => MeasurableSet.iInter fun _ => (hS.inter (hU j)).compl)
  · rw [iUnion_disjointed]
    change (⋃ i, S ∩ U i) = S
    rw [← inter_iUnion, inter_eq_left.mpr hcover]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_FiniteConjugateTiling
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Measurable tilings by conjugated small boxes -/

noncomputable section
namespace PolycyclicRecognition

open MeasureTheory Set
open scoped ENNReal Pointwise

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [MeasurableSpace G] [BorelSpace G]

/-- A measure-preserving group automorphism can distort tiles without
altering the cardinality bound. The doubled small box suffices for a
measurable partition of the large box. -/
theorem finite_conjugate_tiling (μ : Measure G) [μ.IsMulLeftInvariant]
    (e : G ≃ₜ* G) (he : MeasurePreserving e μ μ)
    (S B Bplus R : Set G) (hS : MeasurableSet S)
    (hB : IsCompact B) (hBplus : IsCompact Bplus)
    (hB0 : μ B ≠ 0) (hBtop : μ B ≠ ⊤) (hRtop : μ R ≠ ⊤)
    (hcontain : S * (e '' B) ⊆ R) (hdouble : B * B⁻¹ ⊆ Bplus) :
    ∃ (n : ℕ) (anchor : Fin n → G) (tile : Fin n → Set G),
      (∀ i, anchor i ∈ S) ∧
      (∀ i, MeasurableSet (tile i)) ∧
      Pairwise (fun i j => Disjoint (tile i) (tile j)) ∧
      (⋃ i, tile i) = S ∧
      (∀ i, tile i ⊆ anchor i • (e '' Bplus)) ∧
      (n : ℝ≥0∞) * μ B ≤ μ R := by
  classical
  have hmeas : MeasurableSet (e '' B) := (hB.image e.continuous).isClosed.measurableSet
  have hvol : μ (e '' B) = μ B := by
    calc
      μ (e '' B) = (Measure.map e μ) (e '' B) := by rw [he.map_eq]
      _ = μ (e ⁻¹' (e '' B)) := Measure.map_apply e.continuous.measurable hmeas
      _ = μ B := by rw [Set.preimage_image_eq _ e.injective]
  obtain ⟨t, ht, _hdisj, hcount, hcover⟩ := exists_finite_translate_cover μ
    S (e '' B) R hmeas (hvol ▸ hB0) (hvol ▸ hBtop) hRtop (by
      intro a ha x hx
      obtain ⟨b, hb, rfl⟩ := mem_smul_set.mp hx
      exact hcontain (Set.mul_mem_mul ha hb))
  let f : Fin (Fintype.card t) ≃ t := (Fintype.equivFin t).symm
  let anchor : Fin (Fintype.card t) → G := fun i => (f i).val
  let U : Fin (Fintype.card t) → Set G := fun i => anchor i • (e '' Bplus)
  have hU : ∀ i, MeasurableSet (U i) := fun i =>
    ((hBplus.image e.continuous).isClosed.measurableSet).const_smul (anchor i)
  have hdouble' : (e '' B) * (e '' B)⁻¹ ⊆ e '' Bplus := by
    rw [← Set.image_inv, ← Set.image_mul]
    exact Set.image_mono hdouble
  have hc : S ⊆ ⋃ i, U i := by
    intro x hx
    obtain ⟨a, ha⟩ := mem_iUnion.mp (hcover hx)
    obtain ⟨hat, hxa⟩ := mem_iUnion.mp ha
    let i := f.symm ⟨a, hat⟩
    refine mem_iUnion.mpr ⟨i, ?_⟩
    have hai : anchor i = a := congrArg Subtype.val (f.apply_symm_apply ⟨a, hat⟩)
    change x ∈ anchor i • (e '' Bplus)
    rw [hai]
    exact Set.smul_set_mono hdouble' hxa
  obtain ⟨tile, htile, hd, hu, hsub⟩ :=
    measurable_partition_of_finite_cover S hS U hU hc
  refine ⟨Fintype.card t, anchor, tile, (fun i => ht (f i).property),
    htile, hd, hu, (fun i => (hsub i).trans inter_subset_right), ?_⟩
  simpa only [Fintype.card_coe, hvol] using hcount

end PolycyclicRecognition

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
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_ConeIdealTiling
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite tilings of actual ideal boxes with exact volume bounds -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieModule MeasureTheory Set
open scoped Manifold ENNReal Pointwise

variable {L : Type} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {H : LieSubalgebra ℝ L} [H.IsCartanSubalgebra] (M : CartanWordModel H)
  (C : Set (H →ₗ[ℝ] ℝ))
  {E G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace G] [ChartedSpace E G] [Group G]
  [LieGroup (𝓘(ℝ, E)) ⊤ G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
  (e : M.coneWordIdeal C ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, E)) G)
  (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G) (hExp : IsGroupExponential Exp)

include hExp in
/-- Uniformly bounded-radius enlarged boxes suffice for the maximal-packing
construction, even after a Haar-preserving automorphism of the small box.
The hypothesis on its image is the strict-width inclusion proved separately. -/
theorem exists_coneIdeal_tiling_radius (dynkin : NilpotentDynkinExpansionInput E G)
    (chart : GroupLieAlgebra (𝓘(ℝ, E)) G ≃ₜ G) (hchart : ∀ x, chart x = Exp x)
    (b₀ : Basis (Fin (finrank ℝ (M.coneWordIdeal C))) ℝ (M.coneWordIdeal C)) :
    ∃ R : ℝ, 0 < R ∧ ∀ (s₁ s₂ : Fin M.letterCount → ℝ) (β : M.ConeIdealBases C),
      M.IsMaximizingConeIdealBasis C b₀ s₁ β →
      M.IsMaximizingConeIdealBasis C b₀ s₂ β → ∀ r : ℝ, 0 ≤ r →
      ∀ (μ : Measure G), μ.IsHaarMeasure →
      ∀ F : G ≃ₜ* G, MeasurePreserving F μ μ →
      F '' M.coneIdealBox C (Exp ∘ e) s₂ β r 1 ⊆
        M.coneIdealBox C (Exp ∘ e) s₁ β r 1 →
      μ (M.coneIdealBox C (Exp ∘ e) s₂ β r 1) ≠ 0 →
      ∃ (n : ℕ) (anchor : Fin n → G) (tile : Fin n → Set G),
        (∀ i, anchor i ∈ M.coneIdealBox C (Exp ∘ e) s₁ β r 1) ∧
        (∀ i, MeasurableSet (tile i)) ∧
        Pairwise (fun i j => Disjoint (tile i) (tile j)) ∧
        (⋃ i, tile i) = M.coneIdealBox C (Exp ∘ e) s₁ β r 1 ∧
        (∀ i, tile i ⊆ anchor i • (F '' M.coneIdealBox C (Exp ∘ e) s₂ β r R)) ∧
        (n : ℝ≥0∞) * μ (M.coneIdealBox C (Exp ∘ e) s₂ β r 1) ≤
          μ (M.coneIdealBox C (Exp ∘ e) s₁ β r R) := by
  let : IsTopologicalGroup G := topologicalGroup_of_lieGroup (𝓘(ℝ, E)) ⊤
  obtain ⟨K, _hK, hprod⟩ := M.exists_coneIdealBox_product_bound C e Exp hExp dynkin b₀
  let R := max 1 (K * (1 + (2 : ℝ)) ^ M.coneIdealWordBound C *
    (1 + (1 : ℝ)) ^ M.coneIdealWordBound C)
  have hR : 0 < R := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hmul (s : Fin M.letterCount → ℝ) (β : M.ConeIdealBases C)
      (hβ : M.IsMaximizingConeIdealBasis C b₀ s β) (r : ℝ) (hr : 0 ≤ r)
      {a b : G} (ha : a ∈ M.coneIdealBox C (Exp ∘ e) s β r 1)
      (hb : b ∈ M.coneIdealBox C (Exp ∘ e) s β r 1) :
      a * b ∈ M.coneIdealBox C (Exp ∘ e) s β r R := by
    have hh := hprod s β hβ r hr 2 1 zero_le_one ![a, b] (by
      intro i
      fin_cases i
      · exact ha
      · exact hb)
    simp only [List.ofFn_succ, Fin.isValue, Matrix.cons_val_zero,
      List.ofFn_zero, List.prod_cons, List.prod_nil, mul_one] at hh
    obtain ⟨v, hv, hnorm⟩ := hh
    exact ⟨v, hv, hnorm.trans (le_max_right _ _)⟩
  refine ⟨R, hR, ?_⟩
  intro s₁ s₂ β hβ₁ hβ₂ r hr μ hμ F hF hsmall hpos
  let : μ.IsHaarMeasure := hμ
  have hcompact (s : Fin M.letterCount → ℝ) (R' : ℝ) (hR' : 0 ≤ R') :
      IsCompact (M.coneIdealBox C (Exp ∘ e) s β r R') :=
    isCompact_exponentialCoordinateBox e.toLinearEquiv Exp chart hchart
      (M.coneIdealBoxBasis C s β r) R' hR'
  apply finite_conjugate_tiling μ F hF
    (M.coneIdealBox C (Exp ∘ e) s₁ β r 1)
    (M.coneIdealBox C (Exp ∘ e) s₂ β r 1)
    (M.coneIdealBox C (Exp ∘ e) s₂ β r R)
    (M.coneIdealBox C (Exp ∘ e) s₁ β r R)
    (hcompact s₁ 1 zero_le_one).isClosed.measurableSet
    (hcompact s₂ 1 zero_le_one) (hcompact s₂ R hR.le) hpos
    (ne_of_lt (hcompact s₂ 1 zero_le_one).measure_lt_top)
    (ne_of_lt (hcompact s₁ R hR.le).measure_lt_top)
  · rintro _ ⟨a, ha, b, hb, rfl⟩
    exact hmul s₁ β hβ₁ r hr ha (hsmall hb)
  · rintro _ ⟨a, ha, b, hb, rfl⟩
    apply hmul s₂ β hβ₂ r hr ha
    simpa only [inv_inv] using M.coneIdealBox_inv_mem C e Exp hExp s₂ β r 1
      (Set.mem_inv.mp hb)

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_ExponentialVolumeRatio
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact exponential cardinality bounds from a box volume ratio -/

namespace PolycyclicRecognition

open scoped ENNReal

/-- The fixed determinant and coordinate-cube factors cancel exactly.
This includes zero-dimensional ideals. -/
theorem card_le_of_exponential_box_volume {n d : ℕ} {D R p q : ℝ}
    (hD : 0 < D) (hR : 0 ≤ R)
    (h : (n : ℝ≥0∞) *
        (ENNReal.ofReal D * ENNReal.ofReal (Real.exp q) * ENNReal.ofReal 2 ^ d) ≤
      ENNReal.ofReal D * ENNReal.ofReal (Real.exp p) * ENNReal.ofReal (2 * R) ^ d) :
    (n : ℝ) ≤ R ^ d * Real.exp (p - q) := by
  have htop : ENNReal.ofReal D * ENNReal.ofReal (Real.exp p) *
      ENNReal.ofReal (2 * R) ^ d ≠ ⊤ := by finiteness
  have ht := ENNReal.toReal_mono htop h
  simp only [ENNReal.toReal_mul, ENNReal.toReal_natCast, ENNReal.toReal_pow,
    ENNReal.toReal_ofReal hD.le, ENNReal.toReal_ofReal (Real.exp_pos _).le,
    ENNReal.toReal_ofReal (show (0 : ℝ) ≤ 2 by norm_num),
    ENNReal.toReal_ofReal (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hR)] at ht
  have hf : 0 < D * Real.exp q * 2 ^ d := by positivity
  apply (mul_le_mul_iff_left₀ hf).mp
  calc
    (n : ℝ) * (D * Real.exp q * 2 ^ d) ≤ D * Real.exp p * (2 * R) ^ d := ht
    _ = (R ^ d * Real.exp (p - q)) * (D * Real.exp q * 2 ^ d) := by
      rw [mul_pow, Real.exp_sub]
      field_simp

end PolycyclicRecognition

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_ConeIdealMeasuredTiling
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The exact exponential bound for ideal-box tilings -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module MeasureTheory Set
open scoped Manifold ENNReal Pointwise

variable {L : Type} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {H : LieSubalgebra ℝ L} [H.IsCartanSubalgebra] (M : CartanWordModel H)
  (C : Set (H →ₗ[ℝ] ℝ))
  {E G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace G] [ChartedSpace E G] [Group G]
  [LieGroup (𝓘(ℝ, E)) ⊤ G] [T2Space G] [SimplyConnectedSpace G]
  [MeasurableSpace G] [BorelSpace G]
  (e : M.coneWordIdeal C ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, E)) G)
  (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G) (hExp : IsGroupExponential Exp)

include hExp in
/-- A single Haar normalization supplies both the ambient-inner invariance
and the exact tiling exponent. The radius is independent of the widths,
scale, maximizing basis and automorphism. -/
theorem exists_coneIdeal_measured_tiling
    (haar : NilpotentExponentialHaarInput E G)
    (dynkin : NilpotentDynkinExpansionInput E G)
    (b₀ : Basis (Fin (finrank ℝ (M.coneWordIdeal C))) ℝ (M.coneWordIdeal C)) :
    ∃ (μ : Measure G) (hbij : Function.Bijective Exp) (R : ℝ),
      μ.IsHaarMeasure ∧ 0 < R ∧
      (∀ x : cartanRootIdeal H,
        MeasurePreserving (exponentialConjugate e Exp hbij (M.coneIdealInnerAutomorphism C x)) μ μ) ∧
      ∀ (s₁ s₂ : Fin M.letterCount → ℝ) (β : M.ConeIdealBases C),
        M.IsMaximizingConeIdealBasis C b₀ s₁ β →
        M.IsMaximizingConeIdealBasis C b₀ s₂ β → ∀ r : ℝ, 0 ≤ r →
        ∀ F : G ≃ₜ* G, MeasurePreserving F μ μ →
        F '' M.coneIdealBox C (Exp ∘ e) s₂ β r 1 ⊆
          M.coneIdealBox C (Exp ∘ e) s₁ β r 1 →
        ∃ (n : ℕ) (anchor : Fin n → G) (tile : Fin n → Set G),
          (∀ i, anchor i ∈ M.coneIdealBox C (Exp ∘ e) s₁ β r 1) ∧
          (∀ i, MeasurableSet (tile i)) ∧
          Pairwise (fun i j => Disjoint (tile i) (tile j)) ∧
          (⋃ i, tile i) = M.coneIdealBox C (Exp ∘ e) s₁ β r 1 ∧
          (∀ i, tile i ⊆ anchor i • (F '' M.coneIdealBox C (Exp ∘ e) s₂ β r R)) ∧
          (n : ℝ) ≤ R ^ finrank ℝ (M.coneWordIdeal C) *
            Real.exp (r * (columnBasisWeight (fun w : M.coneIdealWordList C =>
              M.coneIdealWordCost C s₁ w) β.val -
                columnBasisWeight (fun w : M.coneIdealWordList C =>
                  M.coneIdealWordCost C s₂ w) β.val)) := by
  obtain ⟨μ, hbij, hμ, hinv, hvol⟩ :=
    M.exists_coneIdeal_inner_invariant_haar C e Exp hExp haar b₀
  have hnil := e.nilpotent_iff_equiv_nilpotent.mp (M.coneIdeal_nilpotent C)
  obtain ⟨⟨chart, hchart⟩, _⟩ := haar.2 Exp hExp hnil
  obtain ⟨R, hR, htiles⟩ := M.exists_coneIdeal_tiling_radius C e Exp hExp dynkin chart hchart b₀
  refine ⟨μ, hbij, R, hμ, hR, hinv, ?_⟩
  intro s₁ s₂ β hβ₁ hβ₂ r hr F hF hsmall
  have hdet : 0 < |(columnBasisMatrix
      (wordListCoordinates (M.coneMixedVector C) (M.coneIdealWordList C) b₀) β.val).det| :=
    abs_pos.mpr (wordBasis_det_ne_zero _ _ b₀ β)
  have hpos : μ (M.coneIdealBox C (Exp ∘ e) s₂ β r 1) ≠ 0 := by
    rw [hvol s₂ β r 1 zero_le_one]
    simp only [mul_one]
    positivity
  obtain ⟨n, anchor, tile, ha, ht, hd, hu, hs, hn⟩ :=
    htiles s₁ s₂ β hβ₁ hβ₂ r hr μ hμ F hF hsmall hpos
  refine ⟨n, anchor, tile, ha, ht, hd, hu, hs, ?_⟩
  rw [hvol s₂ β r 1 zero_le_one, hvol s₁ β r R hR.le] at hn
  simp only [mul_one] at hn
  have hc := card_le_of_exponential_box_volume hdet hR.le hn
  simpa only [mul_sub] using hc

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_ConeProbeIntrinsicTiles
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Intrinsic ideal increments of the three actual probe sheets -/

namespace PolycyclicRecognition

open Set
open scoped Pointwise

variable {I N : Type} [Group I] [Group N]

/-- The intrinsic inverse flow is precisely conjugation back by the
normalized neighbor step. -/
theorem intrinsic_probe_inverse_flow (ι : I →* N) (φ : MulAut I) (k : N)
    (hφ : ∀ z, ι (φ z) = k * ι z * k⁻¹) (i : I) :
    k⁻¹ * ι i * k = ι (φ.symm i) := by
  have h := hφ (φ.symm i)
  rw [φ.apply_symm_apply] at h
  rw [h]
  simp [mul_assoc]

/-- The tile covering gives an actual small ideal coordinate, without
choosing a second preimage of a point under the ambient inclusion. -/
theorem intrinsic_probe_tile_mem (φ : MulAut I) (a i : I) (B : Set I)
    (hi : i ∈ a • (φ '' B)) : φ.symm (a⁻¹ * i) ∈ B := by
  obtain ⟨_, ⟨z, hz, rfl⟩, he⟩ := hi
  have hi' : i = a * φ z := he.symm
  rw [hi', inv_mul_cancel_left, φ.symm_apply_apply]
  exact hz

end PolycyclicRecognition

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanPivotCancellation
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Cancellation of the scalar height action at the probe pivot

After conjugating back by the Cartan pivot, only its polynomial residual
action remains. The root-space calculation is extended to the generated
nilpotent ideal, so mixed bracket words are included.
-/

noncomputable section
namespace PolycyclicRecognition

open Module LieAlgebra LieModule

variable {L : Type} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {a : ℕ} (T : TriangularAdjoint L a)
  (H : LieSubalgebra ℝ L) [H.IsCartanSubalgebra]

set_option maxHeartbeats 1000000 in
theorem cartanIdealWeightDilation_apply_root (h : H) (χ : Weight ℝ H L)
    (v : cartanRootIdeal H) (hv : (v : L) ∈ rootSpace H χ) :
    cartanIdealWeightDilation T H h v = Real.exp (χ h) • v := by
  apply Subtype.ext
  exact cartanWeightScale_apply_root T H h χ hv

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_NormalizedProbeGenerator
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instDecidableEqConeMixedWords _root_.OAI.PolycyclicRecognition.CartanWordModel.instFintypeConeMixedWords _root_.OAI.PolycyclicRecognition.CartanWordModel.instNonemptyConeIdealBases _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Normalizing the neighboring generator at a contact-facet pivot -/

noncomputable section
namespace PolycyclicRecognition

open Module LieAlgebra

variable {L J : Type} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  [Fintype J] {a : ℕ} (T : TriangularAdjoint L a)
  {H : LieSubalgebra ℝ L} [H.IsCartanSubalgebra] (M : CartanWordModel H)

/-- Exact normalized logarithm of one of the actual homogeneous generators. -/
theorem normalized_probe_generator (h : H) (i : Fin M.letterCount) (t : ℝ) :
    cartanIdealWeightDilation T H (-h) (t • M.letter i) =
      (Real.exp (-M.weight i h) * t) • M.letter i := by
  rw [map_smul, cartanIdealWeightDilation_apply_root T H (-h) (M.weight i)
    (M.letter i) (M.letter_root i), smul_smul, map_neg]
  congr 1
  ring

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_ProbeTileSelector
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_countable _root_.OAI.PolycyclicRecognition.finitelyGeneratedSubgroupIndex_countable _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Borel selection of the actual finite probe tiles -/

noncomputable section
namespace PolycyclicRecognition

open Set

/-- A measurable finite partition gives a measurable tile index on its
covered set. Empty tiles and an empty covered set cause no difficulty. -/
theorem exists_measurable_probe_tile_index
    {X : Type} [MeasurableSpace X] {m : ℕ}
    (U : Set X) (tile : Fin m → Set X)
    (hm : ∀ j, MeasurableSet (tile j))
    (hd : Pairwise (fun j k => Disjoint (tile j) (tile k)))
    (hcover : (⋃ j, tile j) = U) :
    ∃ index : U → Fin m, Measurable index ∧
      (∀ x, x.val ∈ tile (index x)) ∧
      ∀ j, index ⁻¹' {j} = Subtype.val ⁻¹' tile j := by
  classical
  have hex (x : U) : ∃ j, x.val ∈ tile j :=
    mem_iUnion.mp (hcover.symm ▸ x.property)
  choose index hindex using hex
  have hiff (x : U) (j : Fin m) : index x = j ↔ x.val ∈ tile j := by
    constructor
    · rintro rfl
      exact hindex x
    · intro hx
      by_contra hne
      exact Set.disjoint_left.mp (hd hne) (hindex x) hx
  have heq (j : Fin m) : index ⁻¹' {j} = Subtype.val ⁻¹' tile j := by
    ext x
    exact hiff x j
  refine ⟨index, measurable_to_countable' (fun j => ?_), hindex, heq⟩
  rw [heq]
  exact measurable_subtype_coe (hm j)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_TiledProbeSamplers
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_countable _root_.OAI.PolycyclicRecognition.finitelyGeneratedSubgroupIndex_countable _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The three measurable samplers from an actual ideal tiling -/

noncomputable section
namespace PolycyclicRecognition

open Set
open scoped Pointwise

variable {I N Z : Type} [Group I] [TopologicalSpace I] [IsTopologicalGroup I]
  [MeasurableSpace I] [BorelSpace I] [Group N] [TopologicalSpace N]
  [IsTopologicalGroup N] [MeasurableSpace N] [BorelSpace N]
  [SecondCountableTopology I] [SecondCountableTopology N]
  [MeasurableSpace Z]

/-- A finite measurable tiling supplies the actual first-sheet, reverse-anchor,
and within-tile samplers. Their group increments are the original endpoints,
so choosing a tile never replaces a counted point by another representative. -/
theorem exists_measurable_tiled_probe_samplers
    (ι : I →* N) (hι : Measurable ι) (φ : I ≃ₜ* I) (k : N)
    (hφ : ∀ z, ι (φ z) = k * ι z * k⁻¹)
    (σ : Z → N) (hσ : Measurable σ)
    (U Banchor Bsmall : Set I) {m : ℕ} (anchor : Fin m → I)
    (tile : Fin m → Set I) (hm : ∀ j, MeasurableSet (tile j))
    (hd : Pairwise (fun j l => Disjoint (tile j) (tile l)))
    (hu : (⋃ j, tile j) = U)
    (ha : ∀ j, φ.symm (anchor j) ∈ Banchor)
    (ht : ∀ j, tile j ⊆ anchor j • (φ '' Bsmall)) :
    ∃ (index : U → Fin m) (probe : Fin 3 → Z × U → N),
      Measurable index ∧ (∀ j, Measurable (probe j)) ∧
      (∀ y, probe 0 y = ι y.2.val * σ y.1) ∧
      (∀ y, probe 1 y = ι (φ.symm (anchor (index y.2)))) ∧
      (∀ y, probe 2 y = ι (φ.symm ((anchor (index y.2))⁻¹ * y.2.val))) ∧
      (∀ y, probe 1 y ∈ ι '' Banchor) ∧
      (∀ y, probe 2 y ∈ ι '' Bsmall) ∧
      (∀ (S : MulAut N) n y,
        n * S (probe 0 y) = coneProbeFirst S n (ι y.2.val) (σ y.1)) ∧
      (∀ (S : MulAut N) n y,
        (n * S k) * S (probe 1 y) =
          coneProbeSecond S n (ι (anchor (index y.2))) k) ∧
      ∀ (S : MulAut N) n y,
        coneProbeSecond S n (ι (anchor (index y.2))) k * S (probe 2 y) =
          coneProbeSecond S n (ι y.2.val) k := by
  obtain ⟨index, hindex, hmem, _⟩ := exists_measurable_probe_tile_index U tile hm hd hu
  let selected : Z × U → I := fun y => anchor (index y.2)
  have hselected : Measurable selected :=
    (measurable_of_countable anchor).comp (hindex.comp measurable_snd)
  have hcoord : Measurable (fun y : Z × U => y.2.val) :=
    measurable_subtype_coe.comp measurable_snd
  let probe : Fin 3 → Z × U → N := ![
    fun y => ι y.2.val * σ y.1,
    fun y => ι (φ.symm (selected y)),
    fun y => ι (φ.symm ((selected y)⁻¹ * y.2.val))]
  have hp : ∀ j, Measurable (probe j) := by
    intro j
    fin_cases j
    · exact (hι.comp hcoord).mul (hσ.comp measurable_fst)
    · exact hι.comp (φ.symm.continuous.measurable.comp hselected)
    · exact hι.comp (φ.symm.continuous.measurable.comp (hselected.inv.mul hcoord))
  have hback (z : I) : ι (φ.symm z) = k⁻¹ * ι z * k := by
    have hh := hφ (φ.symm z)
    rw [φ.apply_symm_apply] at hh
    rw [hh]
    simp [mul_assoc]
  refine ⟨index, probe, hindex, hp, fun _ => rfl, fun _ => rfl, fun _ => rfl,
    ?_, ?_, ?_, ?_, ?_⟩
  · intro y
    exact ⟨φ.symm (anchor (index y.2)), ha _, rfl⟩
  · intro y
    exact ⟨φ.symm ((anchor (index y.2))⁻¹ * y.2.val),
      intrinsic_probe_tile_mem φ.toMulEquiv _ _ _ (ht _ (hmem y.2)), rfl⟩
  · intro S n y
    rfl
  · intro S n y
    change (n * S k) * S (ι (φ.symm (anchor (index y.2)))) = _
    rw [hback]
    simp [coneProbeSecond, map_mul, mul_assoc]
  · intro S n y
    change coneProbeSecond S n (ι (anchor (index y.2))) k *
      S (ι (φ.symm ((anchor (index y.2))⁻¹ * y.2.val))) = _
    rw [hback]
    simp [coneProbeSecond, map_mul, mul_assoc]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanNormalizedNeighborStep
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instDecidableEqConeMixedWords _root_.OAI.PolycyclicRecognition.CartanWordModel.instFintypeConeMixedWords _root_.OAI.PolycyclicRecognition.CartanWordModel.instNonemptyConeIdealBases _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original neighboring step in the inward-pivot coordinates

This identifies the actual inside-letter flow used by the polar partition.
Its exponential rate is proportional to the enlargement parameter; the
original subexponential radius is absorbed in one vanishing rate.
-/

noncomputable section
namespace PolycyclicRecognition

open Module LieAlgebra Filter
open scoped Manifold Topology

set_option maxHeartbeats 1000000 in
theorem normalized_neighbor_amplitude_le {t R q B c δ r : ℝ}
    (ht : |t| ≤ R * Real.exp ((q + δ * B) * r)) :
    |Real.exp (-((1 - c * δ) * q * r)) * t| ≤
      R * Real.exp ((δ * (B + c * q)) * r) := by
  rw [abs_mul, abs_of_pos (Real.exp_pos _)]
  calc
    _ ≤ Real.exp (-((1 - c * δ) * q * r)) *
        (R * Real.exp ((q + δ * B) * r)) :=
      mul_le_mul_of_nonneg_left ht (Real.exp_pos _).le
    _ = R * Real.exp (-((1 - c * δ) * q * r) + (q + δ * B) * r) := by
      rw [Real.exp_add]
      ring
    _ = _ := by congr 2; ring

namespace CartanWordModel

variable {EG G : Type} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H Exp)

set_option maxHeartbeats 1000000 in
/-- Pulling the given group step back by the actual dilation gives precisely
the exponential of the rescaled original letter. -/
theorem normalized_neighbor_step
    (S : H → MulAut F.N.carrier)
    (hS : ∀ h v, S h (F.ExpN (F.N.equiv v)) =
      F.ExpN (F.N.equiv (cartanIdealWeightDilation T H h v)))
    (h : H) (i : Fin M.letterCount) (time : ℝ) (step : F.N.carrier)
    (hstep : F.inclusionN step = Exp (time •
      (M.letter i : GroupLieAlgebra (𝓘(ℝ, EG)) G))) :
    (S h).symm step = F.ExpN (F.N.equiv
      ((Real.exp (-M.weight i h) * time) • M.letter i)) := by
  have hs : step = F.ExpN (F.N.equiv (time • M.letter i)) :=
    F.closedN.injective (hstep.trans (F.compatibleN (time • M.letter i)).symm)
  apply (S h).injective
  rw [MulEquiv.apply_symm_apply, hS, hs]
  have hn := normalized_probe_generator T M h i time
  rw [← hn]
  have hid : cartanIdealWeightDilation T H h
      (cartanIdealWeightDilation T H (-h) (time • M.letter i)) = time • M.letter i :=
    (cartanIdealWeightDilation T H h).right_inv _
  rw [hid]

set_option maxHeartbeats 1000000 in
/-- The actual normalized neighbor step satisfies the small-rate bound
required by the inside-letter tiling, with no extra amplitude hypothesis. -/
theorem exists_normalized_neighbor_rate
    (S : H → MulAut F.N.carrier)
    (hS : ∀ h v, S h (F.ExpN (F.N.equiv v)) =
      F.ExpN (F.N.equiv (cartanIdealWeightDilation T H h v)))
    (i : Fin M.letterCount) (pivot : H) (c B δ : ℝ)
    (scale R time : ℕ → ℝ) (hscale : ∀ n, 0 < scale n)
    (hR : HasSubexponentialUpperBoundSeq scale R)
    (step : ℕ → F.N.carrier)
    (hstep : ∀ n, F.inclusionN (step n) = Exp (time n •
      (M.letter i : GroupLieAlgebra (𝓘(ℝ, EG)) G)))
    (htime : ∀ n, |time n| ≤ R n * Real.exp
      ((M.weight i pivot + δ * B) * scale n)) :
    ∃ η : ℕ → ℝ, (∀ n, 0 ≤ η n) ∧ Tendsto η atTop (𝓝 0) ∧
      ∀ n, let h := (scale n * (1 - c * δ)) • pivot
        let t := Real.exp (-M.weight i h) * time n
        (S h).symm (step n) = F.ExpN (F.N.equiv (t • M.letter i)) ∧
          |t| ≤ Real.exp (((B + c * M.weight i pivot) * δ + η n) * scale n) := by
  obtain ⟨η, hη0, hη, hrad⟩ := exists_sequence_subexponential_rate scale R hscale hR
  refine ⟨η, hη0, hη, ?_⟩
  intro n
  dsimp only
  refine ⟨M.normalized_neighbor_step T F S hS _ i _ _ (hstep n), ?_⟩
  have he : M.weight i ((scale n * (1 - c * δ)) • pivot) =
      (1 - c * δ) * M.weight i pivot * scale n := by
    rw [map_smul, smul_eq_mul]
    ring
  rw [he]
  calc
    _ ≤ R n * Real.exp ((δ * (B + c * M.weight i pivot)) * scale n) :=
      normalized_neighbor_amplitude_le (htime n)
    _ ≤ Real.exp (scale n * η n) *
        Real.exp ((δ * (B + c * M.weight i pivot)) * scale n) :=
      mul_le_mul_of_nonneg_right (hrad n) (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

end CartanWordModel
end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanSectionProbeBox
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.CartanFactorModel.heightRay_zero _root_.OAI.PolycyclicRecognition.CartanFactorModel.realScaleProfile_apply _root_.OAI.PolycyclicRecognition.CartanFactorModel.sampledProbeProfile_apply _root_.OAI.PolycyclicRecognition.basisDynkinParameter_zero _root_.OAI.PolycyclicRecognition.bracketWordDifferential_mul _root_.OAI.PolycyclicRecognition.cartanWeightDerivation_apply_root _root_.OAI.PolycyclicRecognition.cartanWeightDilation_apply _root_.OAI.PolycyclicRecognition.cartanWeightScale_add_apply _root_.OAI.PolycyclicRecognition.cartanWeightScale_zero_apply _root_.OAI.PolycyclicRecognition.chartExponentialFlow_zero _root_.OAI.PolycyclicRecognition.derivationSemidirectHom_apply _root_.OAI.PolycyclicRecognition.dynkinRightTranslation_apply _root_.OAI.PolycyclicRecognition.dynkinRightTranslation_symm_apply _root_.OAI.PolycyclicRecognition.exponentialHomOfDynkin_apply_exp _root_.OAI.PolycyclicRecognition.exponentialQuotientSection_apply _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.integrateNilpotentLieEquiv_apply_exp _root_.OAI.PolycyclicRecognition.nilshadowWeightDerivation_symm _root_.OAI.PolycyclicRecognition.nilshadowWeightOperator_symm _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The source ideal-section probes lie in one ambient word box -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule Set
open scoped Manifold

variable {L W : Type} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {H : LieSubalgebra ℝ L} [H.IsCartanSubalgebra] (M : CartanWordModel H)
  (C : Set (H →ₗ[ℝ] ℝ)) {a : ℕ} (T : TriangularAdjoint L a)
  (hunimod : ∀ x : L, LinearMap.trace ℝ L (ad ℝ L x) = 0)
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)
  {EN N : Type} [NormedAddCommGroup EN] [NormedSpace ℝ EN]
  [FiniteDimensional ℝ EN] [TopologicalSpace N] [ChartedSpace EN N] [Group N]
  [LieGroup (𝓘(ℝ, EN)) ⊤ N] [T2Space N]

set_option maxHeartbeats 1000000 in
/-- In the adapted maximal basis an intrinsic ideal box is contained in
the ambient word box with exactly the same radius and exponents. -/
theorem exists_ideal_probe_box
    (bN : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (bI : Basis (Fin (finrank ℝ (M.coneWordIdeal C))) ℝ (M.coneWordIdeal C))
    (E : Set W) (hs : ∀ i, 0 ≤ (M.supportIn T hunimod eW).weightSupport E i)
    (hzero : ∀ i, (M.weight i : H →ₗ[ℝ] ℝ) ∈ C →
      (M.supportIn T hunimod eW).weightSupport E i = 0)
    (β : M.ConeIdealBases C)
    (hβ : M.IsMaximizingConeIdealBasis C bI
      ((M.supportIn T hunimod eW).weightSupport E) β) :
    ∃ γ : M.Bases,
      IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList bN)
        (M.boxCost T hunimod eW E) γ.val ∧
      ∀ {X : Type} (Exp : cartanRootIdeal H → X) (r R : ℝ), 0 ≤ R →
        M.coneIdealBox C (fun v => Exp v.val)
          ((M.supportIn T hunimod eW).weightSupport E) β r R ⊆
            M.groupBox T hunimod eW Exp E γ r R := by
  obtain ⟨bQ, lift, hlift, γ, hγ, hbox, _⟩ :=
    M.exists_cone_adapted_path_basis C T hunimod eW bN bI E hs hzero β hβ
  refine ⟨γ, hγ, ?_⟩
  intro X Exp r R hR x hx
  obtain ⟨v, hv, hb⟩ := hx
  rw [hbox]
  refine ⟨v.val, hv, ?_⟩
  exact (ideal_scaled_coordinates_le_iff (M.coneWordIdeal C)
    (WordBasisSelections.basis (M.coneMixedVector C) (M.coneIdealWordList C) β)
    bQ lift hlift _ r R hR v).mpr hb

set_option maxHeartbeats 1000000 in
/-- Completing a maximal ideal basis by pure quotient words places every
unit ideal-section probe in one fixed-radius full word box. The radius
is uniform in the scale, by the actual finite Dynkin product formula. -/
theorem exists_section_probe_box
    (eN : cartanRootIdeal H ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, EN)) N)
    (ExpN : GroupLieAlgebra (𝓘(ℝ, EN)) N → N) (hExpN : IsGroupExponential ExpN)
    (dynkinN : NilpotentDynkinExpansionInput EN N)
    (bN : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (bI : Basis (Fin (finrank ℝ (M.coneWordIdeal C))) ℝ (M.coneWordIdeal C))
    (E : Set W) (hs : ∀ i, 0 ≤ (M.supportIn T hunimod eW).weightSupport E i)
    (hzero : ∀ i, (M.weight i : H →ₗ[ℝ] ℝ) ∈ C →
      (M.supportIn T hunimod eW).weightSupport E i = 0)
    (β : M.ConeIdealBases C)
    (hβ : M.IsMaximizingConeIdealBasis C bI
      ((M.supportIn T hunimod eW).weightSupport E) β) :
    ∃ (bQ : Basis (Fin (finrank ℝ (cartanRootIdeal H ⧸ (M.coneWordIdeal C).toSubmodule)))
        ℝ (cartanRootIdeal H ⧸ (M.coneWordIdeal C).toSubmodule))
      (lift : Fin (finrank ℝ (cartanRootIdeal H ⧸ (M.coneWordIdeal C).toSubmodule)) →
        cartanRootIdeal H),
      (∀ j, (M.coneWordIdeal C).toSubmodule.mkQ (lift j) = bQ j) ∧
      ∃ (γ : M.Bases) (R : ℝ), 0 ≤ R ∧
        IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList bN)
          (M.boxCost T hunimod eW E) γ.val ∧
        ∀ r : ℝ, 0 ≤ r → ∀ (i : M.coneWordIdeal C)
          (q : cartanRootIdeal H ⧸ (M.coneWordIdeal C).toSubmodule),
          ‖(M.coneIdealBoxBasis C ((M.supportIn T hunimod eW).weightSupport E) β r).equivFun i‖ ≤ 1 →
          ‖bQ.equivFun q‖ ≤ 1 →
          ExpN (eN (i : cartanRootIdeal H)) *
            ExpN (eN (quotientLinearSection (M.coneWordIdeal C) bQ lift q)) ∈
              M.groupBox T hunimod eW (ExpN ∘ eN) E γ r R := by
  obtain ⟨bQ, lift, hlift, γ, hγ, hbox, K, hK, hbr⟩ :=
    M.exists_cone_adapted_path_basis C T hunimod eW bN bI E hs hzero β hβ
  obtain ⟨coeff, hcoeff, hprod⟩ := model_finiteDynkinExpansion dynkinN eN ExpN hExpN M.bound_zero 2
  have hmul (v w : cartanRootIdeal H) :
      ExpN (eN (finiteDynkinPolynomial coeff ![v, w])) = ExpN (eN v) * ExpN (eN w) := by
    simpa using (hprod ![v, w]).symm
  let R := sectionDynkinConstant
    (Fintype.card (Fin (finrank ℝ (M.coneWordIdeal C)) ⊕
      Fin (finrank ℝ (cartanRootIdeal H ⧸ (M.coneWordIdeal C).toSubmodule)))) M.bound K *
        (1 + (1 : ℝ)) ^ M.bound
  have hR : 0 ≤ R := by dsimp [R, sectionDynkinConstant] <;> positivity
  refine ⟨bQ, lift, hlift, γ, R, hR, hγ, ?_⟩
  intro r hr i q hi hq
  rw [hbox]
  exact weighted_section_box_product (M.coneWordIdeal C)
    (WordBasisSelections.basis (M.coneMixedVector C) (M.coneIdealWordList C) β)
    bQ lift hlift (ExpN ∘ eN) coeff hcoeff hmul
    (fun j => M.coneIdealWordCost C ((M.supportIn T hunimod eW).weightSupport E) (β.val j))
    K hK hbr r 1 hr zero_le_one i q hi hq

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanTiledProbeBoxes
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_countable _root_.OAI.PolycyclicRecognition.finitelyGeneratedSubgroupIndex_countable _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual tiled probes in the three Cartan template boxes -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule Set Metric
open scoped Manifold Pointwise

variable {L W : Type} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {H : LieSubalgebra ℝ L} [H.IsCartanSubalgebra] (M : CartanWordModel H)
  (C : Set (H →ₗ[ℝ] ℝ)) {a : ℕ} (T : TriangularAdjoint L a)
  (hunimod : ∀ x : L, LinearMap.trace ℝ L (ad ℝ L x) = 0)
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)
  {EN N I : Type} [NormedAddCommGroup EN] [NormedSpace ℝ EN]
  [FiniteDimensional ℝ EN] [TopologicalSpace N] [ChartedSpace EN N] [Group N]
  [LieGroup (𝓘(ℝ, EN)) ⊤ N] [T2Space N]
  [MeasurableSpace N] [BorelSpace N] [SecondCountableTopology N]
  [Group I] [TopologicalSpace I] [IsTopologicalGroup I]
  [MeasurableSpace I] [BorelSpace I] [SecondCountableTopology I]

set_option maxHeartbeats 1000000 in
/-- The ideal-section sampler and both reverse-flow samplers lie in the
three actual ambient word boxes. Their bases and the first radius are
chosen uniformly before the scale, partition and flow. -/
theorem exists_tiled_probe_boxes
    (eN : cartanRootIdeal H ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, EN)) N)
    (ExpN : GroupLieAlgebra (𝓘(ℝ, EN)) N → N) (hExpN : IsGroupExponential ExpN)
    (chartN : GroupLieAlgebra (𝓘(ℝ, EN)) N ≃ₜ N) (hchartN : ∀ v, chartN v = ExpN v)
    (dynkinN : NilpotentDynkinExpansionInput EN N)
    (ExpI : M.coneWordIdeal C → I) (ι : I →* N) (hι : Measurable ι)
    (hcompat : ∀ v, ι (ExpI v) = ExpN (eN (v : cartanRootIdeal H)))
    (bN : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (bI : Basis (Fin (finrank ℝ (M.coneWordIdeal C))) ℝ (M.coneWordIdeal C))
    (E : Fin 3 → Set W)
    (hs : ∀ j i, 0 ≤ (M.supportIn T hunimod eW).weightSupport (E j) i)
    (hzero : ∀ j i, (M.weight i : H →ₗ[ℝ] ℝ) ∈ C →
      (M.supportIn T hunimod eW).weightSupport (E j) i = 0)
    (β : Fin 3 → M.ConeIdealBases C)
    (hβ : ∀ j, M.IsMaximizingConeIdealBasis C bI
      ((M.supportIn T hunimod eW).weightSupport (E j)) (β j)) :
    ∃ (bQ : Basis (Fin (finrank ℝ (cartanRootIdeal H ⧸ (M.coneWordIdeal C).toSubmodule)))
        ℝ (cartanRootIdeal H ⧸ (M.coneWordIdeal C).toSubmodule))
      (lift : Fin (finrank ℝ (cartanRootIdeal H ⧸ (M.coneWordIdeal C).toSubmodule)) →
        cartanRootIdeal H) (γ : Fin 3 → M.Bases) (R₀ : ℝ),
      (∀ j, (M.coneWordIdeal C).toSubmodule.mkQ (lift j) = bQ j) ∧ 0 ≤ R₀ ∧
      (∀ j, IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList bN)
        (M.boxCost T hunimod eW (E j)) (γ j).val) ∧
      ∀ r : ℝ, 0 ≤ r → ∀ R : ℝ, 0 ≤ R →
      let U := M.coneIdealBox C ExpI
        ((M.supportIn T hunimod eW).weightSupport (E 0)) (β 0) r 1
      let Banchor := M.coneIdealBox C ExpI
        ((M.supportIn T hunimod eW).weightSupport (E 1)) (β 1) r 1
      let Bsmall := M.coneIdealBox C ExpI
        ((M.supportIn T hunimod eW).weightSupport (E 2)) (β 2) r R
      let Z := closedBall (0 : Fin (finrank ℝ
        (cartanRootIdeal H ⧸ (M.coneWordIdeal C).toSubmodule)) → ℝ) 1
      let σ : Z → N := fun q => ExpN (eN
        (quotientLinearSection (M.coneWordIdeal C) bQ lift (bQ.equivFun.symm q.val)))
      ∀ (φ : I ≃ₜ* I) (k : N), (∀ z, ι (φ z) = k * ι z * k⁻¹) →
      ∀ (m : ℕ) (anchor : Fin m → I) (tile : Fin m → Set I),
      (∀ j, MeasurableSet (tile j)) →
      Pairwise (fun j l => Disjoint (tile j) (tile l)) → (⋃ j, tile j) = U →
      (∀ j, φ.symm (anchor j) ∈ Banchor) →
      (∀ j, tile j ⊆ anchor j • (φ '' Bsmall)) →
      ∃ (index : U → Fin m) (probe : Fin 3 → Z × U → N),
        Measurable index ∧ (∀ j, Measurable (probe j)) ∧
        (∀ j y, probe j y ∈ M.groupBox T hunimod eW (ExpN ∘ eN)
          (E j) (γ j) r (![R₀, 1, R] j)) ∧
        (∀ y, probe 0 y = ι y.2.val * σ y.1) ∧
        (∀ y, probe 1 y = ι (φ.symm (anchor (index y.2)))) ∧
        ∀ y, probe 2 y = ι (φ.symm ((anchor (index y.2))⁻¹ * y.2.val)) := by
  let : IsTopologicalGroup N := topologicalGroup_of_lieGroup (𝓘(ℝ, EN)) ⊤
  obtain ⟨bQ, lift, hlift, γ₀, R₀, hR₀, hγ₀, hfirst⟩ :=
    M.exists_section_probe_box C T hunimod eW eN ExpN hExpN dynkinN
      bN bI (E 0) (hs 0) (hzero 0) (β 0) (hβ 0)
  obtain ⟨γ₁, hγ₁, hanchor⟩ := M.exists_ideal_probe_box C T hunimod eW
    bN bI (E 1) (hs 1) (hzero 1) (β 1) (hβ 1)
  obtain ⟨γ₂, hγ₂, hsmall⟩ := M.exists_ideal_probe_box C T hunimod eW
    bN bI (E 2) (hs 2) (hzero 2) (β 2) (hβ 2)
  refine ⟨bQ, lift, ![γ₀, γ₁, γ₂], R₀, hlift, hR₀, ?_, ?_⟩
  · intro j
    fin_cases j
    · exact hγ₀
    · exact hγ₁
    · exact hγ₂
  intro r hr R hR
  dsimp only
  let U := M.coneIdealBox C ExpI
    ((M.supportIn T hunimod eW).weightSupport (E 0)) (β 0) r 1
  let Banchor := M.coneIdealBox C ExpI
    ((M.supportIn T hunimod eW).weightSupport (E 1)) (β 1) r 1
  let Bsmall := M.coneIdealBox C ExpI
    ((M.supportIn T hunimod eW).weightSupport (E 2)) (β 2) r R
  let Z := closedBall (0 : Fin (finrank ℝ
    (cartanRootIdeal H ⧸ (M.coneWordIdeal C).toSubmodule)) → ℝ) 1
  let σ : Z → N := fun q => ExpN (eN
    (quotientLinearSection (M.coneWordIdeal C) bQ lift (bQ.equivFun.symm q.val)))
  have hσ : Measurable σ := by
    let : MeasurableSpace (GroupLieAlgebra (𝓘(ℝ, EN)) N) := borel _
    let : BorelSpace (GroupLieAlgebra (𝓘(ℝ, EN)) N) := ⟨rfl⟩
    let F := eN.toLinearMap.comp ((quotientLinearSection (M.coneWordIdeal C) bQ lift).comp
      bQ.equivFun.symm.toLinearMap)
    have he : σ = fun q : Z => chartN (F q.val) := by
      funext q
      exact (hchartN _).symm
    rw [he]
    exact chartN.continuous.measurable.comp
      (F.continuous_of_finiteDimensional.measurable.comp measurable_subtype_coe)
  intro φ k hφ m anchor tile hm hd hu ha ht
  obtain ⟨index, probe, hi, hp, hp₀, hp₁, hp₂, hpa, hps, _⟩ :=
    exists_measurable_tiled_probe_samplers ι hι φ k hφ σ hσ U Banchor Bsmall
      anchor tile hm hd hu ha ht
  have hincl (j : Fin 3) (radius : ℝ) (hincl :
      M.coneIdealBox C (fun v => ExpN (eN (v : cartanRootIdeal H)))
        ((M.supportIn T hunimod eW).weightSupport (E j)) (β j) r radius ⊆
      M.groupBox T hunimod eW (ExpN ∘ eN) (E j) (![γ₀, γ₁, γ₂] j) r radius)
      {z : I} (hz : z ∈ M.coneIdealBox C ExpI
        ((M.supportIn T hunimod eW).weightSupport (E j)) (β j) r radius) :
      ι z ∈ M.groupBox T hunimod eW (ExpN ∘ eN) (E j) (![γ₀, γ₁, γ₂] j) r radius := by
    obtain ⟨v, hv, hb⟩ := hz
    apply hincl
    exact ⟨v, (hcompat v).symm.trans (congrArg ι hv), hb⟩
  refine ⟨index, probe, hi, hp, ?_, hp₀, hp₁, hp₂⟩
  intro j y
  fin_cases j
  · change probe 0 y ∈ M.groupBox T hunimod eW (ExpN ∘ eN) (E 0) γ₀ r R₀
    rw [hp₀]
    obtain ⟨v, hv, hb⟩ := y.2.property
    rw [← hv, hcompat]
    exact hfirst r hr v (bQ.equivFun.symm y.1.val) hb (by
      rw [LinearEquiv.apply_symm_apply]
      exact mem_closedBall_zero_iff.mp y.1.property)
  · change probe 1 y ∈ M.groupBox T hunimod eW (ExpN ∘ eN) (E 1) γ₁ r 1
    obtain ⟨z, hz, he⟩ := hpa y
    rw [← he]
    exact hincl 1 1 (hanchor (ExpN ∘ eN) r 1 zero_le_one) hz
  · change probe 2 y ∈ M.groupBox T hunimod eW (ExpN ∘ eN) (E 2) γ₂ r R
    obtain ⟨z, hz, he⟩ := hps y
    rw [← he]
    exact hincl 2 R (hsmall (ExpN ∘ eN) r R hR) hz

set_option maxHeartbeats 1000000 in
theorem nonempty_tiledProbeBoxData
    (eN : cartanRootIdeal H ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, EN)) N)
    (ExpN : GroupLieAlgebra (𝓘(ℝ, EN)) N → N) (hExpN : IsGroupExponential ExpN)
    (chartN : GroupLieAlgebra (𝓘(ℝ, EN)) N ≃ₜ N) (hchartN : ∀ v, chartN v = ExpN v)
    (dynkinN : NilpotentDynkinExpansionInput EN N)
    (ExpI : M.coneWordIdeal C → I) (ι : I →* N) (hι : Measurable ι)
    (hcompat : ∀ v, ι (ExpI v) = ExpN (eN (v : cartanRootIdeal H)))
    (bN : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (bI : Basis (Fin (finrank ℝ (M.coneWordIdeal C))) ℝ (M.coneWordIdeal C))
    (E : Fin 3 → Set W)
    (hs : ∀ j i, 0 ≤ (M.supportIn T hunimod eW).weightSupport (E j) i)
    (hzero : ∀ j i, (M.weight i : H →ₗ[ℝ] ℝ) ∈ C →
      (M.supportIn T hunimod eW).weightSupport (E j) i = 0)
    (β : Fin 3 → M.ConeIdealBases C)
    (hβ : ∀ j, M.IsMaximizingConeIdealBasis C bI
      ((M.supportIn T hunimod eW).weightSupport (E j)) (β j)) :
    Nonempty (M.TiledProbeBoxData C T hunimod eW eN ExpN ExpI ι bN E β) := by
  obtain ⟨bQ, lift, γ, R₀, hlift, hR₀, hγ, hselect⟩ :=
    M.exists_tiled_probe_boxes C T hunimod eW eN ExpN hExpN chartN hchartN dynkinN
      ExpI ι hι hcompat bN bI E hs hzero β hβ
  exact ⟨⟨bQ, lift, γ, R₀, hlift, hR₀, hγ, hselect⟩⟩

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

variable {L W : Type} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
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
theorem polar_width_pos (K : ProperCone ℝ (StrongDual ℝ W))
    (i : Fin M.letterCount) (hi : (M.weight i : H →ₗ[ℝ] ℝ) ∉ heightConePreimage T eW K) :
    0 < conePolarWidth K ((M.supportIn T hunimod eW).weight i).toContinuousLinearMap :=
  conePolarWidth_pos K (fun h => hi ((M.weight_mem_heightConePreimage_iff T hunimod eW K i).mpr h))

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

set_option maxHeartbeats 1000000 in
/-- One actual mixed-word basis maximizes every nonnegative multiple of
the polar template, including all three radii in the strict-width tiling. -/
theorem exists_polar_probe_basis (K : ProperCone ℝ (StrongDual ℝ W))
    (bI : Basis (Fin (finrank ℝ (M.coneWordIdeal (heightConePreimage T eW K))))
      ℝ (M.coneWordIdeal (heightConePreimage T eW K))) :
    ∃ β : M.ConeIdealBases (heightConePreimage T eW K),
      M.IsMaximizingConeIdealBasis (heightConePreimage T eW K) bI
        (fun i => conePolarWidth K
          ((M.supportIn T hunimod eW).weight i).toContinuousLinearMap) β ∧
      ∀ c : ℝ, 0 ≤ c → M.IsMaximizingConeIdealBasis (heightConePreimage T eW K) bI
        ((M.supportIn T hunimod eW).weightSupport
          ((fun x : W => c • x) '' conePolarTemplate K)) β := by
  obtain ⟨β, hβ⟩ := M.exists_maximizing_coneIdealBasis (heightConePreimage T eW K) bI
    (fun i => conePolarWidth K ((M.supportIn T hunimod eW).weight i).toContinuousLinearMap)
  refine ⟨β, hβ, ?_⟩
  intro c hc
  have he : (M.supportIn T hunimod eW).weightSupport
      ((fun x : W => c • x) '' conePolarTemplate K) =
      fun i => c * conePolarWidth K ((M.supportIn T hunimod eW).weight i).toContinuousLinearMap := by
    funext i
    exact M.weightSupport_polar_smul T hunimod eW K hc i
  rw [he]
  exact M.maximizing_coneIdealBasis_smul (heightConePreimage T eW K) bI _ β hβ hc

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanPolarFixedSection
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_countable _root_.OAI.PolycyclicRecognition.finitelyGeneratedSubgroupIndex_countable _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.CartanFactorModel.heightRay_zero _root_.OAI.PolycyclicRecognition.CartanFactorModel.realScaleProfile_apply _root_.OAI.PolycyclicRecognition.CartanFactorModel.sampledProbeProfile_apply _root_.OAI.PolycyclicRecognition.cartanWeightDerivation_apply_root _root_.OAI.PolycyclicRecognition.chartExponentialFlow_zero _root_.OAI.PolycyclicRecognition.derivationSemidirectHom_apply _root_.OAI.PolycyclicRecognition.exponentialHomOfDynkin_apply_exp _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.modelNilradicalLinearAction_apply _root_.OAI.PolycyclicRecognition.modelNilradicalRotation_apply _root_.OAI.PolycyclicRecognition.modelNilradicalRotation_mul _root_.OAI.PolycyclicRecognition.modelNilradicalRotation_one _root_.OAI.PolycyclicRecognition.nilshadowWeightDerivation_symm _root_.OAI.PolycyclicRecognition.nilshadowWeightOperator_symm _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polar probes with a fixed quotient section -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule Set Metric
open scoped Manifold Pointwise

variable {EG G W I : Type} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
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

set_option maxHeartbeats 1000000 in
omit [SimplyConnectedSpace G] [Nonempty (Fin M.letterCount)] in
theorem nonempty_polar_tiled_probe_box
    (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
    (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
    (ExpI : M.coneWordIdeal C → I) (ι : I →* F.N.carrier) (hι : Measurable ι)
    (hcompat : ∀ v, ι (ExpI v) = F.ExpN (F.N.equiv (v : cartanRootIdeal H)))
    (bN : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (bI : Basis (Fin (finrank ℝ (M.coneWordIdeal C))) ℝ (M.coneWordIdeal C))
    {ε : ℝ} (hε : 0 < ε) (β : M.ConeIdealBases C)
    (hβ : M.IsMaximizingConeIdealBasis C bI (M.polarProbeWidths T hunimod eW K) β)
    : Nonempty (M.TiledProbeBoxData C T hunimod eW F.N.equiv F.ExpN ExpI ι bN
      (normalizedPolarTemplates K ε) (fun _ => β)) := by
  classical
  let E := normalizedPolarTemplates K ε
  have hrad (j : Fin 3) : 0 ≤ threePolarRadii ε j ∧ threePolarRadii ε j ≤ ε := by
    fin_cases j <;> dsimp [threePolarRadii] <;> constructor <;> linarith
  have hprop (j : Fin 3) := M.polar_probe_template_properties T hunimod eW K (hrad j).1
  have hw (j : Fin 3) : (M.supportIn T hunimod eW).weightSupport (E j) =
      fun i => threePolarRadii ε j * M.polarProbeWidths T hunimod eW K i := by
    funext i
    exact M.weightSupport_polar_smul T hunimod eW K (hrad j).1 i
  have hβ' (j : Fin 3) : M.IsMaximizingConeIdealBasis C bI
      ((M.supportIn T hunimod eW).weightSupport (E j)) β := by
    rw [hw]
    exact M.maximizing_coneIdealBasis_smul C bI _ β hβ (hrad j).1
  obtain ⟨⟨chartN, hchartN⟩, _⟩ := haarN.2 F.ExpN F.isExpN
    (F.N.tangent_nilpotent (cartanRootIdeal_nilpotent H T))
  let coordinates := ((bN.map F.N.equiv.toLinearEquiv).equivFun.symm.toContinuousLinearEquiv.toHomeomorph).trans chartN
  let : SecondCountableTopology F.N.carrier := coordinates.symm.secondCountableTopology
  exact M.nonempty_tiledProbeBoxData C T hunimod eW F.N.equiv F.ExpN F.isExpN
    chartN hchartN dynkinN ExpI ι hι hcompat bN bI E
    (fun j => (hprop j).2.2.2.1) (fun j => (hprop j).2.2.2.2) (fun _ => β) hβ'

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_ConeIdealFlowTiling
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.CartanFactorModel.realScaleProfile_apply _root_.OAI.PolycyclicRecognition.CartanFactorModel.sampledProbeProfile_apply _root_.OAI.PolycyclicRecognition.chartExponentialFlow_zero _root_.OAI.PolycyclicRecognition.derivationSemidirectHom_apply _root_.OAI.PolycyclicRecognition.exponentialHomOfDynkin_apply_exp _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual inside-letter automorphism in strict-width tilings -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieModule MeasureTheory Set Filter
open scoped Manifold Topology Pointwise

variable {L : Type} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {H : LieSubalgebra ℝ L} [H.IsCartanSubalgebra] (M : CartanWordModel H)
  (C : Set (H →ₗ[ℝ] ℝ))
  {E G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace G] [ChartedSpace E G] [Group G]
  [LieGroup (𝓘(ℝ, E)) ⊤ G] [T2Space G]
  (e : M.coneWordIdeal C ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, E)) G)
  (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G) (hExp : IsGroupExponential Exp)
  (hbij : Function.Bijective Exp)
  (chart : GroupLieAlgebra (𝓘(ℝ, E)) G ≃ₜ G) (hchart : ∀ x, chart x = Exp x)
  (dynkin : NilpotentDynkinExpansionInput E G)

theorem coneIdealLetterAutomorphism_apply_exp (i : Fin M.letterCount) (t : ℝ)
    (v : M.coneWordIdeal C) :
    M.coneIdealLetterAutomorphism C e Exp hExp hbij chart hchart dynkin i t (Exp (e v)) =
      Exp (e (M.coneIdealLetterFlow C i t v)) := by
  change exponentialConjugate e Exp hbij (M.coneIdealInnerAutomorphism C (t • M.letter i))
    (Exp (e v)) = _
  rw [exponentialConjugate_apply_exp, M.coneIdealInnerAutomorphism_letter]

/-- The smallness threshold comes from the positive mixed-word widths.
No image inclusion is assumed for the automorphism used in the tiling. -/
theorem exists_coneIdealLetterAutomorphism_threshold
    (b₀ : Basis (Fin (finrank ℝ (M.coneWordIdeal C))) ℝ (M.coneWordIdeal C))
    (s : Fin M.letterCount → ℝ) (hs : ∀ i, 0 ≤ s i)
    (hpos : ∀ i, (M.weight i : H →ₗ[ℝ] ℝ) ∉ C → 0 < s i)
    (β : M.ConeIdealBases C) (hβ : M.IsMaximizingConeIdealBasis C b₀ s β)
    (i : Fin M.letterCount) (hi : s i = 0)
    {a b U : ℝ} (ha : 0 ≤ a) (hab : a < b) (hU : 0 < U) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
      ∀ t ε : ℝ → ℝ, Tendsto ε atTop (𝓝 0) →
      (∀ᶠ r in atTop, |t r| ≤ Real.exp ((U * δ + ε r) * r)) →
      ∀ᶠ r in atTop,
        (M.coneIdealLetterAutomorphism C e Exp hExp hbij chart hchart dynkin i (t r)) ''
          M.coneIdealBox C (Exp ∘ e) (fun l => a * s l) β r 1 ⊆
        M.coneIdealBox C (Exp ∘ e) (fun l => b * s l) β r 1 := by
  obtain ⟨lo, hlo, hw⟩ := M.exists_positive_coneIdeal_width C s hs hpos
  let gap := (b - a) * lo
  let D := ((M.bound : ℝ) + 1) * U
  have hg : 0 < gap := mul_pos (sub_pos.mpr hab) hlo
  have hD : 0 < D := mul_pos (by positivity) hU
  let δ₀ := gap / (2 * D)
  have hδ₀ : 0 < δ₀ := div_pos hg (by positivity)
  have heq : δ₀ * (2 * D) = gap := div_mul_cancel₀ gap (ne_of_gt (by positivity))
  refine ⟨δ₀, hδ₀, ?_⟩
  intro δ hδ hδle t ε hε ht
  have hgap : (M.bound : ℝ) * (U * δ) < (b - a) * lo := by
    have hstep := mul_le_mul_of_nonneg_left hδle hD.le
    calc
      _ ≤ D * δ := by dsimp [D] <;> nlinarith [mul_pos hU hδ]
      _ ≤ D * δ₀ := hstep
      _ < gap := by nlinarith
  filter_upwards [M.coneIdealLetterFlow_absorbed C b₀ s β hβ i hi ha hab
    (mul_nonneg hU.le hδ.le) hw hgap t ε hε ht] with r hr
  rintro _ ⟨g, ⟨v, rfl, hv⟩, rfl⟩
  refine ⟨M.coneIdealLetterFlow C i (t r) v, ?_, hr v hv⟩
  exact (M.coneIdealLetterAutomorphism_apply_exp C e Exp hExp hbij chart hchart dynkin
    i (t r) v).symm

variable [SimplyConnectedSpace G] [MeasurableSpace G] [BorelSpace G]

omit hbij in
/-- Strict width gives measurable tilings for the actual integrated letter
flow, with the exact exponential cardinality bound. The small-box inclusion
is derived from the nilpotent flow estimate. -/
theorem exists_strict_width_coneIdeal_tiling
    (haar : NilpotentExponentialHaarInput E G)
    (b₀ : Basis (Fin (finrank ℝ (M.coneWordIdeal C))) ℝ (M.coneWordIdeal C))
    (s : Fin M.letterCount → ℝ) (hs : ∀ i, 0 ≤ s i)
    (hpos : ∀ i, (M.weight i : H →ₗ[ℝ] ℝ) ∉ C → 0 < s i)
    (β : M.ConeIdealBases C) (hβ : M.IsMaximizingConeIdealBasis C b₀ s β)
    (i : Fin M.letterCount) (hi : s i = 0)
    {a b U : ℝ} (ha : 0 ≤ a) (hab : a < b) (hU : 0 < U) :
    ∃ (μ : Measure G) (hbij : Function.Bijective Exp) (R δ₀ : ℝ),
      μ.IsHaarMeasure ∧ 0 < R ∧ 0 < δ₀ ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
      ∀ t ε : ℝ → ℝ, Tendsto ε atTop (𝓝 0) →
      (∀ᶠ r in atTop, |t r| ≤ Real.exp ((U * δ + ε r) * r)) →
      ∀ᶠ r in atTop,
        ∃ (n : ℕ) (anchor : Fin n → G) (tile : Fin n → Set G),
          (∀ j, anchor j ∈ M.coneIdealBox C (Exp ∘ e) (fun l => b * s l) β r 1) ∧
          (∀ j, MeasurableSet (tile j)) ∧
          Pairwise (fun j k => Disjoint (tile j) (tile k)) ∧
          (⋃ j, tile j) = M.coneIdealBox C (Exp ∘ e) (fun l => b * s l) β r 1 ∧
          (∀ j, tile j ⊆ anchor j •
            ((M.coneIdealLetterAutomorphism C e Exp hExp hbij chart hchart dynkin i (t r)) ''
              M.coneIdealBox C (Exp ∘ e) (fun l => a * s l) β r R)) ∧
          (n : ℝ) ≤ R ^ finrank ℝ (M.coneWordIdeal C) *
            Real.exp (r * (columnBasisWeight (fun w : M.coneIdealWordList C =>
              M.coneIdealWordCost C (fun l => b * s l) w) β.val -
                columnBasisWeight (fun w : M.coneIdealWordList C =>
                  M.coneIdealWordCost C (fun l => a * s l) w) β.val)) := by
  obtain ⟨μ, hbij, R, hμ, hR, hinv, htiles⟩ :=
    M.exists_coneIdeal_measured_tiling C e Exp hExp haar dynkin b₀
  obtain ⟨δ₀, hδ₀, hsmall⟩ := M.exists_coneIdealLetterAutomorphism_threshold C e Exp hExp
    hbij chart hchart dynkin b₀ s hs hpos β hβ i hi ha hab hU
  refine ⟨μ, hbij, R, δ₀, hμ, hR, hδ₀, ?_⟩
  intro δ hδ hδle t ε hε ht
  filter_upwards [hsmall δ hδ hδle t ε hε ht, eventually_ge_atTop (0 : ℝ)] with r hr hr0
  exact htiles (fun l => b * s l) (fun l => a * s l) β
    (M.maximizing_coneIdealBasis_smul C b₀ s β hβ (ha.trans hab.le))
    (M.maximizing_coneIdealBasis_smul C b₀ s β hβ ha) r hr0
    (M.coneIdealLetterAutomorphism C e Exp hExp hbij chart hchart dynkin i (t r))
    (hinv (t r • M.letter i)) hr

omit hbij in
/-- The same tiling also bounds every anchor after conjugating back by the
inside-letter flow. Both strict width gaps use one positive threshold. -/
theorem exists_strict_width_tiling_with_anchors
    (haar : NilpotentExponentialHaarInput E G)
    (b₀ : Basis (Fin (finrank ℝ (M.coneWordIdeal C))) ℝ (M.coneWordIdeal C))
    (s : Fin M.letterCount → ℝ) (hs : ∀ i, 0 ≤ s i)
    (hpos : ∀ i, (M.weight i : H →ₗ[ℝ] ℝ) ∉ C → 0 < s i)
    (β : M.ConeIdealBases C) (hβ : M.IsMaximizingConeIdealBasis C b₀ s β)
    (i : Fin M.letterCount) (hi : s i = 0)
    {a b c U : ℝ} (ha : 0 ≤ a) (hab : a < b) (hbc : b < c) (hU : 0 < U) :
    ∃ (μ : Measure G) (hbij : Function.Bijective Exp) (R δ₀ : ℝ),
      μ.IsHaarMeasure ∧ 0 < R ∧ 0 < δ₀ ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
      ∀ t ε : ℝ → ℝ, Tendsto ε atTop (𝓝 0) →
      (∀ᶠ r in atTop, |t r| ≤ Real.exp ((U * δ + ε r) * r)) →
      ∀ᶠ r in atTop,
        ∃ (n : ℕ) (anchor : Fin n → G) (tile : Fin n → Set G),
          (∀ j, anchor j ∈ M.coneIdealBox C (Exp ∘ e) (fun l => b * s l) β r 1) ∧
          (∀ j, M.coneIdealLetterAutomorphism C e Exp hExp hbij chart hchart dynkin i (-t r)
            (anchor j) ∈ M.coneIdealBox C (Exp ∘ e) (fun l => c * s l) β r 1) ∧
          (∀ j, MeasurableSet (tile j)) ∧
          Pairwise (fun j k => Disjoint (tile j) (tile k)) ∧
          (⋃ j, tile j) = M.coneIdealBox C (Exp ∘ e) (fun l => b * s l) β r 1 ∧
          (∀ j, tile j ⊆ anchor j •
            ((M.coneIdealLetterAutomorphism C e Exp hExp hbij chart hchart dynkin i (t r)) ''
              M.coneIdealBox C (Exp ∘ e) (fun l => a * s l) β r R)) ∧
          (n : ℝ) ≤ R ^ finrank ℝ (M.coneWordIdeal C) *
            Real.exp (r * (columnBasisWeight (fun w : M.coneIdealWordList C =>
              M.coneIdealWordCost C (fun l => b * s l) w) β.val -
                columnBasisWeight (fun w : M.coneIdealWordList C =>
                  M.coneIdealWordCost C (fun l => a * s l) w) β.val)) := by
  obtain ⟨μ, hbij, R, δ₁, hμ, hR, hδ₁, htiles⟩ :=
    M.exists_strict_width_coneIdeal_tiling C e Exp hExp chart hchart dynkin
      haar b₀ s hs hpos β hβ i hi ha hab hU
  obtain ⟨δ₂, hδ₂, hlarge⟩ := M.exists_coneIdealLetterAutomorphism_threshold C e Exp hExp
    hbij chart hchart dynkin b₀ s hs hpos β hβ i hi (ha.trans hab.le) hbc hU
  refine ⟨μ, hbij, R, min δ₁ δ₂, hμ, hR, lt_min hδ₁ hδ₂, ?_⟩
  intro δ hδ hδle t ε hε ht
  have hneg : ∀ᶠ r in atTop, |(-t r)| ≤ Real.exp ((U * δ + ε r) * r) := by
    simpa only [abs_neg] using ht
  filter_upwards [htiles δ hδ (hδle.trans (min_le_left _ _)) t ε hε ht,
    hlarge δ hδ (hδle.trans (min_le_right _ _)) (fun r => -t r) ε hε hneg] with r hr hn
  obtain ⟨n, anchor, tile, ha, hm, hd, hu, ht, hc⟩ := hr
  refine ⟨n, anchor, tile, ha, ?_, hm, hd, hu, ht, hc⟩
  intro j
  exact hn ⟨anchor j, ha j, rfl⟩

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_ConeIdealFlowConjugation
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The intrinsic tiling flow is ambient conjugation -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieModule LieAlgebra
open scoped Manifold

variable {L : Type} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {H : LieSubalgebra ℝ L} [H.IsCartanSubalgebra] (M : CartanWordModel H)
  (C : Set (H →ₗ[ℝ] ℝ))
  {E I N A : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace I] [ChartedSpace E I] [Group I]
  [LieGroup (𝓘(ℝ, E)) ⊤ I] [T2Space I] [Group N]
  [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

attribute [local instance 100] LieRing.ofAssociativeRing

variable
  (e : M.coneWordIdeal C ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, E)) I)
  (ExpI : GroupLieAlgebra (𝓘(ℝ, E)) I → I) (hExpI : IsGroupExponential ExpI)
  (hbij : Function.Bijective ExpI)
  (chart : GroupLieAlgebra (𝓘(ℝ, E)) I ≃ₜ I) (hchart : ∀ x, chart x = ExpI x)
  (dynkin : NilpotentDynkinExpansionInput E I)
  (ι : I →* N) (ExpN : cartanRootIdeal H → N)
  (hcompat : ∀ v : M.coneWordIdeal C, ι (ExpI (e v)) = ExpN v)
  (j : cartanRootIdeal H →ₗ⁅ℝ⁆ A) (ρ : N →* Aˣ) (hρ : Function.Injective ρ)
  (hmatch : ∀ x, ρ (ExpN x) = algebraExpUnit (j x))

include hcompat hρ hmatch in
/-- The same integrated automorphism used to partition the intrinsic ideal
is conjugation by the actual ambient generator, after its inclusion in `N`. -/
theorem coneIdealLetterAutomorphism_conjugation (i : Fin M.letterCount) (t : ℝ)
    (z : I) :
    ι (M.coneIdealLetterAutomorphism C e ExpI hExpI hbij chart hchart dynkin i t z) =
      ExpN (t • M.letter i) * ι z * (ExpN (t • M.letter i))⁻¹ := by
  obtain ⟨v, rfl⟩ := (hbij.comp e.bijective).surjective z
  change ι (M.coneIdealLetterAutomorphism C e ExpI hExpI hbij chart hchart dynkin i t
    (ExpI (e v))) = ExpN (t • M.letter i) * ι (ExpI (e v)) * _
  rw [M.coneIdealLetterAutomorphism_apply_exp, hcompat, hcompat]
  exact M.coneIdealLetterFlow_exp_conjugation C ExpN j ρ hρ hmatch i t v

include hcompat hρ hmatch in
/-- The reverse-time flow in the anchor estimate is exactly the inverse of
the automorphism in the tile covering. -/
theorem coneIdealLetterAutomorphism_neg_apply (hι : Function.Injective ι)
    (i : Fin M.letterCount) (t : ℝ) (z : I) :
    M.coneIdealLetterAutomorphism C e ExpI hExpI hbij chart hchart dynkin i (-t) z =
      (M.coneIdealLetterAutomorphism C e ExpI hExpI hbij chart hchart dynkin i t).symm z := by
  have hneg : ExpN ((-t) • M.letter i) = (ExpN (t • M.letter i))⁻¹ := by
    apply hρ
    rw [map_inv, hmatch, hmatch, neg_smul, map_neg, algebraExpUnit_neg]
  apply hι
  rw [M.coneIdealLetterAutomorphism_conjugation C e ExpI hExpI hbij chart hchart
    dynkin ι ExpN hcompat j ρ hρ hmatch, hneg, inv_inv]
  exact intrinsic_probe_inverse_flow ι
    (M.coneIdealLetterAutomorphism C e ExpI hExpI hbij chart hchart dynkin i t).toMulEquiv
    (ExpN (t • M.letter i))
    (M.coneIdealLetterAutomorphism_conjugation C e ExpI hExpI hbij chart hchart
      dynkin ι ExpN hcompat j ρ hρ hmatch i t) z

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_SequenceConeIdealFlowTiling
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Strict-width tilings on the actual profile scales -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieModule MeasureTheory Set Filter
open scoped Manifold Topology Pointwise

variable {L : Type} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {H : LieSubalgebra ℝ L} [H.IsCartanSubalgebra] (M : CartanWordModel H)
  (C : Set (H →ₗ[ℝ] ℝ))
  {E G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace G] [ChartedSpace E G] [Group G]
  [LieGroup (𝓘(ℝ, E)) ⊤ G] [T2Space G]
  (e : M.coneWordIdeal C ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, E)) G)
  (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G) (hExp : IsGroupExponential Exp)
  (hbij : Function.Bijective Exp)
  (chart : GroupLieAlgebra (𝓘(ℝ, E)) G ≃ₜ G) (hchart : ∀ x, chart x = Exp x)
  (dynkin : NilpotentDynkinExpansionInput E G)

variable [SimplyConnectedSpace G] [MeasurableSpace G] [BorelSpace G]

omit hbij in
/-- Actual flow tilings along any strictly increasing profile scale sequence,
with the same threshold, cardinality and reverse-anchor estimates. -/
theorem exists_strict_width_sequence_tiling_with_anchors
    (haar : NilpotentExponentialHaarInput E G)
    (b₀ : Basis (Fin (finrank ℝ (M.coneWordIdeal C))) ℝ (M.coneWordIdeal C))
    (s : Fin M.letterCount → ℝ) (hs : ∀ i, 0 ≤ s i)
    (hpos : ∀ i, (M.weight i : H →ₗ[ℝ] ℝ) ∉ C → 0 < s i)
    (β : M.ConeIdealBases C) (hβ : M.IsMaximizingConeIdealBasis C b₀ s β)
    (i : Fin M.letterCount) (hi : s i = 0)
    {a b c U : ℝ} (ha : 0 ≤ a) (hab : a < b) (hbc : b < c) (hU : 0 < U) :
    ∃ (μ : Measure G) (hbij : Function.Bijective Exp) (R δ₀ : ℝ),
      μ.IsHaarMeasure ∧ 0 < R ∧ 0 < δ₀ ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
      ∀ (scale : ℕ → ℝ), StrictMono scale → Tendsto scale atTop atTop →
      ∀ t ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) →
      (∀ᶠ m in atTop, |t m| ≤ Real.exp ((U * δ + ε m) * (scale m))) →
      ∀ᶠ m in atTop,
        ∃ (n : ℕ) (anchor : Fin n → G) (tile : Fin n → Set G),
          (∀ j, anchor j ∈ M.coneIdealBox C (Exp ∘ e) (fun l => b * s l) β (scale m) 1) ∧
          (∀ j, M.coneIdealLetterAutomorphism C e Exp hExp hbij chart hchart dynkin i (-t m)
            (anchor j) ∈ M.coneIdealBox C (Exp ∘ e) (fun l => c * s l) β (scale m) 1) ∧
          (∀ j, MeasurableSet (tile j)) ∧
          Pairwise (fun j k => Disjoint (tile j) (tile k)) ∧
          (⋃ j, tile j) = M.coneIdealBox C (Exp ∘ e) (fun l => b * s l) β (scale m) 1 ∧
          (∀ j, tile j ⊆ anchor j •
            ((M.coneIdealLetterAutomorphism C e Exp hExp hbij chart hchart dynkin i (t m)) ''
              M.coneIdealBox C (Exp ∘ e) (fun l => a * s l) β (scale m) R)) ∧
          (n : ℝ) ≤ R ^ finrank ℝ (M.coneWordIdeal C) *
            Real.exp ((scale m) * (columnBasisWeight (fun w : M.coneIdealWordList C =>
              M.coneIdealWordCost C (fun l => b * s l) w) β.val -
                columnBasisWeight (fun w : M.coneIdealWordList C =>
                  M.coneIdealWordCost C (fun l => a * s l) w) β.val)) := by
  obtain ⟨μ, hbij, R, δ₀, hμ, hR, hδ₀, htiles⟩ :=
    M.exists_strict_width_tiling_with_anchors C e Exp hExp chart hchart dynkin
      haar b₀ s hs hpos β hβ i hi ha hab hbc hU
  refine ⟨μ, hbij, R, δ₀, hμ, hR, hδ₀, ?_⟩
  intro δ hδ hδle scale hmono hscale t ε hε ht
  have hεreal := tendsto_sequenceRealExtension_zero scale hmono ε hε
  have htreal := sequenceRealExtension_eventually_abs_le_exp scale hmono t ε (U * δ) ht
  have hh := hscale.eventually (htiles δ hδ hδle
    (sequenceRealExtension scale t) (sequenceRealExtension scale ε) hεreal htreal)
  simpa only [sequenceRealExtension_apply scale hmono] using hh

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanPolarFlowTiling
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finite_templateSymmetryGroup _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.instFiniteRootOffsetConeIndex _root_.OAI.PolycyclicRecognition.instFiniteSubtypeLinearEquivRealIdMemSubgroupLinearSupportSymmetryGroup _root_.OAI.PolycyclicRecognition.instNonemptyRootOffsetConeIndex _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Strict-width tiling for the actual polar probe templates -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieModule LieAlgebra MeasureTheory Set Filter
open scoped Manifold Topology Pointwise BigOperators

variable {L W : Type} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {H : LieSubalgebra ℝ L} [H.IsCartanSubalgebra] (M : CartanWordModel H)
  {d : ℕ} (T : TriangularAdjoint L d)
  (hunimod : ∀ x : L, LinearMap.trace ℝ L (ad ℝ L x) = 0)
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  (eW : HeightSpace T.character ≃ₗ[ℝ] W) (K : ProperCone ℝ (StrongDual ℝ W))

local notation "C" => heightConePreimage T eW K
local notation "s" => M.polarProbeWidths T hunimod eW K

variable {EI I N A : Type} [NormedAddCommGroup EI] [NormedSpace ℝ EI]
  [FiniteDimensional ℝ EI] [TopologicalSpace I] [ChartedSpace EI I] [Group I]
  [LieGroup (𝓘(ℝ, EI)) ⊤ I] [T2Space I] [SimplyConnectedSpace I]
  [MeasurableSpace I] [BorelSpace I] [Group N]
  [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

attribute [local instance 100] LieRing.ofAssociativeRing

set_option maxHeartbeats 1000000 in
/-- The source tiling has the exact three polar radii. Its reverse anchors
use the inverse of the actual conjugating automorphism, and its number of
tiles has exponent `(b-a)` times the fixed polar ideal exponent. -/
theorem exists_polar_flow_tiling
    (eI : M.coneWordIdeal C ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, EI)) I)
    (ExpI : GroupLieAlgebra (𝓘(ℝ, EI)) I → I) (hExpI : IsGroupExponential ExpI)
    (chartI : GroupLieAlgebra (𝓘(ℝ, EI)) I ≃ₜ I) (hchartI : ∀ v, chartI v = ExpI v)
    (dynkinI : NilpotentDynkinExpansionInput EI I)
    (haarI : NilpotentExponentialHaarInput EI I)
    (ι : I →* N) (hι : Function.Injective ι)
    (ExpN : cartanRootIdeal H → N)
    (hcompat : ∀ v : M.coneWordIdeal C, ι (ExpI (eI v)) = ExpN v)
    (j : cartanRootIdeal H →ₗ⁅ℝ⁆ A) (ρ : N →* Aˣ) (hρ : Function.Injective ρ)
    (hmatch : ∀ x, ρ (ExpN x) = algebraExpUnit (j x))
    (bI : Basis (Fin (finrank ℝ (M.coneWordIdeal C))) ℝ (M.coneWordIdeal C))
    (i : Fin M.letterCount) (hi : (M.weight i : H →ₗ[ℝ] ℝ) ∈ C)
    {a b c U : ℝ} (ha : 0 ≤ a) (hab : a < b) (hbc : b < c) (hU : 0 < U) :
    ∃ (β : M.ConeIdealBases C) (μ : Measure I) (hbij : Function.Bijective ExpI) (R δ₀ : ℝ),
      M.IsMaximizingConeIdealBasis C bI s β ∧ μ.IsHaarMeasure ∧ 0 < R ∧ 0 < δ₀ ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
      ∀ (scale : ℕ → ℝ), StrictMono scale → Tendsto scale atTop atTop →
      ∀ time ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) →
      (∀ᶠ n in atTop, |time n| ≤ Real.exp ((U * δ + ε n) * scale n)) →
      ∀ᶠ n in atTop,
        let φ := M.coneIdealLetterAutomorphism C eI ExpI hExpI hbij chartI hchartI dynkinI i (time n)
        ∃ (m : ℕ) (anchor : Fin m → I) (tile : Fin m → Set I),
          (∀ z, ι (φ z) = ExpN (time n • M.letter i) * ι z * (ExpN (time n • M.letter i))⁻¹) ∧
          (∀ l, anchor l ∈ M.coneIdealBox C (ExpI ∘ eI)
            ((M.supportIn T hunimod eW).weightSupport
              ((fun x : W => b • x) '' conePolarTemplate K)) β (scale n) 1) ∧
          (∀ l, φ.symm (anchor l) ∈ M.coneIdealBox C (ExpI ∘ eI)
            ((M.supportIn T hunimod eW).weightSupport
              ((fun x : W => c • x) '' conePolarTemplate K)) β (scale n) 1) ∧
          (∀ l, MeasurableSet (tile l)) ∧
          Pairwise (fun l q => Disjoint (tile l) (tile q)) ∧
          (⋃ l, tile l) = M.coneIdealBox C (ExpI ∘ eI)
            ((M.supportIn T hunimod eW).weightSupport
              ((fun x : W => b • x) '' conePolarTemplate K)) β (scale n) 1 ∧
          (∀ l, tile l ⊆ anchor l • (φ '' M.coneIdealBox C (ExpI ∘ eI)
            ((M.supportIn T hunimod eW).weightSupport
              ((fun x : W => a • x) '' conePolarTemplate K)) β (scale n) R)) ∧
          (m : ℝ) ≤ R ^ finrank ℝ (M.coneWordIdeal C) * Real.exp (scale n *
            ((b - a) * ∑ l, M.coneIdealWordCost C s (β.val l))) := by
  obtain ⟨β, hβ, _⟩ := M.exists_polar_probe_basis T hunimod eW K bI
  obtain ⟨μ, hbij, R, δ₀, hμ, hR, hδ₀, htiles⟩ :=
    M.exists_strict_width_sequence_tiling_with_anchors C eI ExpI hExpI chartI hchartI
      dynkinI haarI bI s (M.polar_width_nonneg T hunimod eW K)
      (M.polar_width_pos T hunimod eW K) β hβ i
      (M.polar_width_zero T hunimod eW K i hi) ha hab hbc hU
  refine ⟨β, μ, hbij, R, δ₀, hβ, hμ, hR, hδ₀, ?_⟩
  intro δ hδ hδle scale hmono hscale time ε hε ht
  have hw (v : ℝ) (hv : 0 ≤ v) :
      (M.supportIn T hunimod eW).weightSupport
        ((fun x : W => v • x) '' conePolarTemplate K) = fun i => v * s i := by
    funext l
    exact M.weightSupport_polar_smul T hunimod eW K hv l
  have hexp : columnBasisWeight
      (fun w : M.coneIdealWordList C => M.coneIdealWordCost C (fun l => b * s l) w) β.val -
      columnBasisWeight
      (fun w : M.coneIdealWordList C => M.coneIdealWordCost C (fun l => a * s l) w) β.val =
      (b - a) * ∑ l, M.coneIdealWordCost C s (β.val l) := by
    simp only [columnBasisWeight, M.coneIdealWordCost_smul, ← Finset.mul_sum, sub_mul]
  filter_upwards [htiles δ hδ hδle scale hmono hscale time ε hε ht] with n hn
  dsimp only
  obtain ⟨m, anchor, tile, han, hrev, hm, hd, hu, hsmall, hcount⟩ := hn
  refine ⟨m, anchor, tile, ?_, ?_, ?_, hm, hd, ?_, ?_, ?_⟩
  · exact M.coneIdealLetterAutomorphism_conjugation C eI ExpI hExpI hbij chartI hchartI
      dynkinI ι ExpN hcompat j ρ hρ hmatch i (time n)
  · simpa only [hw b (ha.trans hab.le)] using han
  · intro l
    rw [hw c (ha.trans (hab.le.trans hbc.le))]
    rw [← M.coneIdealLetterAutomorphism_neg_apply C eI ExpI hExpI hbij chartI hchartI
      dynkinI ι ExpN hcompat j ρ hρ hmatch hι]
    exact hrev l
  · simpa only [hw b (ha.trans hab.le)] using hu
  · simpa only [hw a ha] using hsmall
  · simpa only [hexp] using hcount

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanPolarTiledSamplers
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_nonempty _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Counted polar samplers from the actual inside-letter flow -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule Set Metric Filter MeasureTheory
open scoped Manifold Pointwise Topology

variable {EG G W EI I A : Type} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
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
  [NormedAddCommGroup EI] [NormedSpace ℝ EI] [FiniteDimensional ℝ EI]
  [ChartedSpace EI I] [LieGroup (𝓘(ℝ, EI)) ⊤ I] [SimplyConnectedSpace I] [T2Space I]
  [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

attribute [local instance 100] LieRing.ofAssociativeRing

local notation "C" => heightConePreimage T eW K

set_option maxHeartbeats 1000000 in
/-- The published exponential inputs and the proved inside-letter tiling give
actual counted samplers after deleting a finite initial segment of the scales.
No partition, anchor, chain, or exceptional-scale replacement is assumed. -/
theorem exists_polar_tiled_samplers
    (hExp : IsGroupExponential Exp)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
    (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
    (eI : M.coneWordIdeal C ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, EI)) I)
    (ExpI : GroupLieAlgebra (𝓘(ℝ, EI)) I → I) (hExpI : IsGroupExponential ExpI)
    (chartI : GroupLieAlgebra (𝓘(ℝ, EI)) I ≃ₜ I) (hchartI : ∀ v, chartI v = ExpI v)
    (dynkinI : NilpotentDynkinExpansionInput EI I)
    (haarI : NilpotentExponentialHaarInput EI I)
    (ι : I →* F.N.carrier) (hι : Function.Injective ι) (hιm : Measurable ι)
    (hcompat : ∀ v : M.coneWordIdeal C,
      ι (ExpI (eI v)) = F.ExpN (F.N.equiv (v : cartanRootIdeal H)))
    (j : cartanRootIdeal H →ₗ⁅ℝ⁆ A) (ρ : F.N.carrier →* Aˣ) (hρ : Function.Injective ρ)
    (hmatch : ∀ x, ρ (F.ExpN (F.N.equiv x)) = algebraExpUnit (j x))
    (bN : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (bI : Basis (Fin (finrank ℝ (M.coneWordIdeal C))) ℝ (M.coneWordIdeal C))
    (i : Fin M.letterCount) (hi : (M.weight i : H →ₗ[ℝ] ℝ) ∈ C)
    {ε U : ℝ} (hε : 0 < ε) (hU : 0 < U) :
    ∃ (β : M.ConeIdealBases C) (μ : MeasureTheory.Measure I)
      (hbij : Function.Bijective ExpI)
      (bQ : Basis (Fin (finrank ℝ (cartanRootIdeal H ⧸ (M.coneWordIdeal C).toSubmodule)))
        ℝ (cartanRootIdeal H ⧸ (M.coneWordIdeal C).toSubmodule))
      (lift : Fin (finrank ℝ (cartanRootIdeal H ⧸ (M.coneWordIdeal C).toSubmodule)) →
        cartanRootIdeal H) (R δ₀ : ℝ),
      (∀ j, (M.coneWordIdeal C).toSubmodule.mkQ (lift j) = bQ j) ∧
      M.IsMaximizingConeIdealBasis C bI (M.polarProbeWidths T hunimod eW K) β ∧
      μ.IsHaarMeasure ∧ 0 < R ∧ 0 < δ₀ ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
      ∀ (scale : ℕ → ℝ), StrictMono scale → Filter.Tendsto scale Filter.atTop Filter.atTop →
      (∀ n, 0 ≤ scale n) →
      ∀ time η : ℕ → ℝ, Filter.Tendsto η Filter.atTop (nhds 0) →
      (∀ᶠ n in Filter.atTop, |time n| ≤ Real.exp ((U * δ + η n) * scale n)) →
      ∃ n₀ : ℕ,
        let r := fun n => scale (n + n₀)
        let φ := fun n => M.coneIdealLetterAutomorphism C eI ExpI hExpI hbij chartI
          hchartI dynkinI i (time (n + n₀))
        ∃ D : M.PolarTiledSamplerData T F hunimod eW K (ExpI ∘ eI) ι bN ε β R r φ,
          D.chain.bQ = bQ ∧ D.chain.lift = lift := by
  classical
  obtain ⟨β, μ, hbij, R, δ₀, hβ, hμ, hR, hδ₀, ht⟩ :=
    M.exists_polar_flow_tiling T hunimod eW K eI ExpI hExpI chartI hchartI dynkinI haarI
      ι hι (F.ExpN ∘ F.N.equiv) hcompat j ρ hρ hmatch bI i hi
      (by positivity : 0 ≤ ε / 3) (by linarith : ε / 3 < 2 * ε / 3)
      (by linarith : 2 * ε / 3 < ε) hU
  let box := Classical.choice (M.nonempty_polar_tiled_probe_box T F hunimod eW K
    haarN dynkinN (ExpI ∘ eI) ι hιm hcompat bN bI hε β hβ)
  refine ⟨β, μ, hbij, box.bQ, box.lift, R, δ₀, box.lifts, hβ, hμ, hR, hδ₀, ?_⟩
  intro δ hδ hd scale hs hscale hr time η hη htime
  have he := ht δ hδ hd scale hs hscale time η hη htime
  obtain ⟨n₀, hn₀⟩ := Filter.eventually_atTop.mp he
  let r := fun n => scale (n + n₀)
  let φ := fun n => M.coneIdealLetterAutomorphism C eI ExpI hExpI hbij chartI
    hchartI dynkinI i (time (n + n₀))
  have htiles (n : ℕ) := hn₀ (n + n₀) (Nat.le_add_left n₀ n)
  dsimp only at htiles
  choose m anchor tile hc ha hrev hm hdis hcover hsmall hcount using htiles
  have hcover' (n) : (⋃ l, tile n l) = M.coneIdealBox C (ExpI ∘ eI)
      ((M.supportIn T hunimod eW).weightSupport (normalizedPolarTemplates K ε 0)) β (r n) 1 :=
    hcover n
  have hrev' (n) (l) : (φ n).symm (anchor n l) ∈ M.coneIdealBox C (ExpI ∘ eI)
      ((M.supportIn T hunimod eW).weightSupport (normalizedPolarTemplates K ε 1)) β (r n) 1 :=
    hrev n l
  have hsmall' (n) (l) : tile n l ⊆ anchor n l • ((φ n) '' M.coneIdealBox C (ExpI ∘ eI)
      ((M.supportIn T hunimod eW).weightSupport (normalizedPolarTemplates K ε 2)) β (r n) R) :=
    hsmall n l
  obtain ⟨ambient, chain, hchainQ, hchainLift⟩ :=
    M.exists_polar_tiled_probe_chains_from_box T F hunimod eW K
    hExp realize haarN dynkinN (ExpI ∘ eI) ι bN hε β box r
    (fun n => hr (n + n₀)) R hR.le φ
    (fun n => F.ExpN (F.N.equiv (time (n + n₀) • M.letter i))) hc m anchor tile hm hdis
    hcover' hrev' hsmall'
  refine ⟨n₀, {
    tiles := m
    anchor := anchor
    tile := tile
    measurable := hm
    disjoint := hdis
    cover := hcover'
    reverse_anchor := hrev'
    small_tile := hsmall'
    count := ?_
    ambient := ambient
    chain := chain }, hchainQ, hchainLift⟩
  intro n
  have hid : 2 * ε / 3 - ε / 3 = ε / 3 := by ring
  simpa only [hid] using hcount n

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanNormalizedPolarSamplers
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original neighboring step supplies the polar tiling flow -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule Set Metric Filter MeasureTheory
open scoped Manifold Pointwise Topology

variable {EG G W EI I : Type} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
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
  [NormedAddCommGroup EI] [NormedSpace ℝ EI] [FiniteDimensional ℝ EI]
  [ChartedSpace EI I] [LieGroup (𝓘(ℝ, EI)) ⊤ I] [SimplyConnectedSpace I] [T2Space I]

attribute [local instance 100] LieRing.ofAssociativeRing

local notation "C" => heightConePreimage T eW K

open scoped Matrix.Norms.Operator

set_option maxHeartbeats 1000000 in
/-- The original neighboring amplitude gives the actual normalized tiling
flow. Its rate and conjugation identity are proved, and the quotient section
is fixed before the scale, neighboring step and tail are chosen. -/
theorem exists_normalized_polar_samplers_oai
    (hExp : IsGroupExponential Exp)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
    (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
    (eI : M.coneWordIdeal C ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, EI)) I)
    (ExpI : GroupLieAlgebra (𝓘(ℝ, EI)) I → I) (hExpI : IsGroupExponential ExpI)
    (chartI : GroupLieAlgebra (𝓘(ℝ, EI)) I ≃ₜ I) (hchartI : ∀ v, chartI v = ExpI v)
    (dynkinI : NilpotentDynkinExpansionInput EI I)
    (haarI : NilpotentExponentialHaarInput EI I)
    (ι : I →* F.N.carrier) (hι : Function.Injective ι) (hιm : Measurable ι)
    (hcompat : ∀ v : M.coneWordIdeal C,
      ι (ExpI (eI v)) = F.ExpN (F.N.equiv (v : cartanRootIdeal H)))
    (bN : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (bI : Basis (Fin (finrank ℝ (M.coneWordIdeal C))) ℝ (M.coneWordIdeal C))
    (i : Fin M.letterCount) (hi : (M.weight i : H →ₗ[ℝ] ℝ) ∈ C)
    (pivot : H) (hpivot : 0 < M.weight i pivot)
    (c B ε : ℝ) (hc : 0 ≤ c) (hB : 0 ≤ B) (hε : 0 < ε) :
    ∃ (β : M.ConeIdealBases C) (μI : MeasureTheory.Measure I)
      (hbij : Function.Bijective ExpI)
      (bQ : Basis (Fin (finrank ℝ (cartanRootIdeal H ⧸ (M.coneWordIdeal C).toSubmodule)))
        ℝ (cartanRootIdeal H ⧸ (M.coneWordIdeal C).toSubmodule))
      (lift : Fin (finrank ℝ (cartanRootIdeal H ⧸ (M.coneWordIdeal C).toSubmodule)) →
        cartanRootIdeal H) (Rbox δ₀ : ℝ),
      (∀ j, (M.coneWordIdeal C).toSubmodule.mkQ (lift j) = bQ j) ∧
      M.IsMaximizingConeIdealBasis C bI (M.polarProbeWidths T hunimod eW K) β ∧
      μI.IsHaarMeasure ∧ 0 < Rbox ∧ 0 < δ₀ ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
      ∀ (scale : ℕ → ℝ), StrictMono scale → Tendsto scale atTop atTop →
      (∀ n, 0 < scale n) →
      ∀ (radius time : ℕ → ℝ), HasSubexponentialUpperBoundSeq scale radius →
      (∀ n, |time n| ≤ radius n * Real.exp
        ((M.weight i pivot + δ * B) * scale n)) →
      ∀ (S : H → MulAut F.N.carrier),
      (∀ h v, S h (F.ExpN (F.N.equiv v)) =
        F.ExpN (F.N.equiv (cartanIdealWeightDilation T H h v))) →
      ∀ (step : ℕ → F.N.carrier),
      (∀ n, F.inclusionN (step n) = Exp (time n •
        (M.letter i : GroupLieAlgebra (𝓘(ℝ, EG)) G))) →
      ∃ n₀ : ℕ,
        let r := fun n => scale (n + n₀)
        let h := fun n => (r n * (1 - c * δ)) • pivot
        let tn := fun n => Real.exp (-M.weight i (h n)) * time (n + n₀)
        let φ := fun n => M.coneIdealLetterAutomorphism C eI ExpI hExpI hbij chartI
          hchartI dynkinI i (tn n)
        ∃ D : M.PolarTiledSamplerData T F hunimod eW K (ExpI ∘ eI) ι bN ε β Rbox r φ,
          D.chain.bQ = bQ ∧ D.chain.lift = lift ∧
          ∀ n z, ι (φ n z) =
            (S (h n)).symm (step (n + n₀)) * ι z *
              ((S (h n)).symm (step (n + n₀)))⁻¹ := by
  obtain ⟨m, hm, ρ, j, hind, hmatch⟩ := realize ⟨a, ⟨T⟩⟩ Exp hExp
  let : NeZero m := ⟨Nat.ne_of_gt hm⟩
  have hρ : Function.Injective ρ := by
    intro g h he
    exact hind.injective (congrArg (fun u : (Matrix (Fin m) (Fin m) ℝ)ˣ =>
      (u : Matrix (Fin m) (Fin m) ℝ)) he)
  let jN := j.comp (cartanRootIdeal H).incl
  let ρN := ρ.comp F.inclusionN
  have hρN : Function.Injective ρN := hρ.comp F.closedN.injective
  have hN (v : cartanRootIdeal H) :
      ρN (F.ExpN (F.N.equiv v)) = algebraExpUnit (jN v) := by
    change ρ (F.inclusionN (F.ExpN (F.N.equiv v))) = algebraExpUnit (j v)
    rw [F.compatibleN, hmatch]
  let U := B + c * M.weight i pivot + 1
  have hU : 0 < U := by
    have hmul := mul_nonneg hc hpivot.le
    dsimp only [U]
    linarith
  obtain ⟨β, μI, hbij, bQ, lift, Rbox, δ₀, hlift, hβ, hμI, hRbox, hδ₀, htile⟩ :=
    M.exists_polar_tiled_samplers T F hunimod eW K hExp realize haarN dynkinN
      eI ExpI hExpI chartI hchartI dynkinI haarI ι hι hιm hcompat
      jN ρN hρN hN bN bI i hi hε hU
  refine ⟨β, μI, hbij, bQ, lift, Rbox, δ₀, hlift, hβ, hμI, hRbox, hδ₀, ?_⟩
  intro δ hδ hd scale hs hscale hs0 radius time hrad ht S hS step hstep
  obtain ⟨η, _, hη, hn⟩ := M.exists_normalized_neighbor_rate T F S hS i pivot c B δ
    scale radius time hs0 hrad step hstep ht
  let h := fun n => (scale n * (1 - c * δ)) • pivot
  let tn := fun n => Real.exp (-M.weight i (h n)) * time n
  have htn : ∀ᶠ n in atTop, |tn n| ≤ Real.exp ((U * δ + η n) * scale n) := by
    apply Eventually.of_forall
    intro n
    exact (hn n).2.trans (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right
      (by dsimp only [U] <;> nlinarith) (hs0 n).le))
  obtain ⟨n₀, D, hQ, hl⟩ := htile δ hδ hd scale hs hscale (fun n => (hs0 n).le)
    tn η hη htn
  refine ⟨n₀, D, hQ, hl, ?_⟩
  intro n z
  have hconj := M.coneIdealLetterAutomorphism_conjugation C eI ExpI hExpI hbij
    chartI hchartI dynkinI ι (F.ExpN ∘ F.N.equiv) hcompat jN ρN hρN hN
    i (tn (n + n₀)) z
  change ι (M.coneIdealLetterAutomorphism C eI ExpI hExpI hbij chartI hchartI
    dynkinI i (tn (n + n₀)) z) = _
  have he := congrArg (fun v : F.N.carrier => v * ι z * v⁻¹) (hn (n + n₀)).1
  exact hconj.trans he.symm

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

theorem solution : type_of% @OAI.PolycyclicRecognition.CartanWordModel.exists_normalized_polar_samplers_oai := @OAI.PolycyclicRecognition.CartanWordModel.exists_normalized_polar_samplers_oai
