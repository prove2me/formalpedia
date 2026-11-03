-- Prove2me | solution 1 for OAI.PolycyclicRecognition.CartanWordModel.good_affine_templates_support_le_m
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-02T23:54:01.675713+00:00
-- url     : https://prove2.me/submissions/a2ac502c-d19a-41d1-aa43-81f55ad2ecf8

import Mathlib
import Definitions.Def_PolycyclicRecognition
import Definitions.Def_OAIQ093D015
import Theorems.Thm_OAI_PolycyclicRecognition_CartanWordModel_exists_coupled_target_tuples
import Theorems.Thm_OAI_PolycyclicRecognition_CartanWordModel_exists_good_conjugated_word_paths
import Theorems.Thm_OAI_PolycyclicRecognition_CartanWordModel_exists_source_target_comparison_schemes_m
import Theorems.Thm_OAI_PolycyclicRecognition_CartanWordModel_source_target_product_exponent_le_m

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

omit [Nonempty B] in
theorem basisTemplateSupport_translate {E : Set W} (hE : IsCompact E) (hne : E.Nonempty)
    (w : W) (b : B) :
    D.basisTemplateSupport ((fun x => x + w) '' E) b = D.basisTemplateSupport E b := by
  simp only [basisTemplateSupport, D.weightSupport_translate hE hne, mul_add,
    Finset.sum_add_distrib, D.balanced, add_zero]

theorem templateSupport_translate {E : Set W} (hE : IsCompact E) (hne : E.Nonempty)
    (w : W) : D.templateSupport ((fun x => x + w) '' E) = D.templateSupport E := by
  simp only [templateSupport, D.basisTemplateSupport_translate hE hne]

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
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_CoarsePathConcatenation
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
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

private theorem pathMetricBound_trans_ordered {p : Path x y} {q : Path y z} {L κ : ℝ}
    (hκ : 0 ≤ κ) (hp : PathMetricBound p L κ) (hq : PathMetricBound q L κ)
    (s t : unitInterval) (hst : (s : ℝ) ≤ t) :
    dist ((p.trans q) s) ((p.trans q) t) ≤ (2 * L) * |(s : ℝ) - t| + 2 * κ := by
  rw [Path.trans_apply, Path.trans_apply]
  split_ifs with hs ht ht
  · calc
      _ ≤ L * |2 * (s : ℝ) - 2 * t| + κ := hp _ _
      _ ≤ _ := by
        rw [show 2 * (s : ℝ) - 2 * t = 2 * ((s : ℝ) - t) by ring,
          abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
        nlinarith
  · calc
      _ ≤ dist (p _) y + dist y (q _) := dist_triangle _ y _
      _ ≤ (L * |2 * (s : ℝ) - 1| + κ) +
          (L * |0 - (2 * (t : ℝ) - 1)| + κ) := by
        apply add_le_add
        · simpa using hp _ 1
        · simpa only [Path.source, Set.Icc.coe_zero] using
            hq 0 ⟨2 * (t : ℝ) - 1, unitInterval.two_mul_sub_one_mem_iff.mpr
              ⟨(not_le.mp ht).le, t.property.2⟩⟩
      _ = _ := by
        rw [abs_of_nonpos (by linarith : 2 * (s : ℝ) - 1 ≤ 0),
          abs_of_nonpos (by linarith : 0 - (2 * (t : ℝ) - 1) ≤ 0),
          abs_of_nonpos (sub_nonpos.mpr hst)]
        ring
  · exfalso
    exact hs (hst.trans ht)
  · calc
      _ ≤ L * |(2 * (s : ℝ) - 1) - (2 * (t : ℝ) - 1)| + κ := hq _ _
      _ ≤ _ := by
        rw [show (2 * (s : ℝ) - 1) - (2 * (t : ℝ) - 1) =
            2 * ((s : ℝ) - t) by ring, abs_mul,
          abs_of_pos (by norm_num : (0 : ℝ) < 2)]
        nlinarith

/-- Concatenation doubles the common speed and additive error. For a fixed
number of pieces these constants stay independent of the height scale. -/
theorem PathMetricBound.trans {p : Path x y} {q : Path y z} {L κ : ℝ}
    (hκ : 0 ≤ κ) (hp : PathMetricBound p L κ) (hq : PathMetricBound q L κ) :
    PathMetricBound (p.trans q) (2 * L) (2 * κ) := by
  intro s t
  rcases le_total (s : ℝ) t with hst | hts
  · exact pathMetricBound_trans_ordered hκ hp hq s t hst
  · simpa only [dist_comm, abs_sub_comm] using
      pathMetricBound_trans_ordered hκ hp hq t s hts

theorem path_trans_range_mem {S : Set X} {p : Path x y} {q : Path y z}
    (hp : ∀ t, p t ∈ S) (hq : ∀ t, q t ∈ S) : ∀ t, (p.trans q) t ∈ S := by
  intro t
  rw [Path.trans_apply]
  split_ifs
  · exact hp _
  · exact hq _

end PolycyclicRecognition

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_CenteredSourceTerminals
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.inversePairCoupling_finiteOnCompacts _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.normalizedPair_polishSpace _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The source terminal set for a tuple centered at its initial image -/

noncomputable section
namespace PolycyclicRecognition

open Set
open scoped NNReal

variable {N G : Type} [TopologicalSpace N] [Group G] [MetricSpace G]
  [IsTopologicalGroup G] [IsIsometricSMul G G]

omit [IsIsometricSMul G G] in
theorem isCompact_relativeTupleTerminals {h : ℕ} (ι : N → G) (hι : Continuous ι)
    (origin base pivot : G) (last : Fin h) {S : Set (Fin h → N)} (hS : IsCompact S) :
    IsCompact (relativeTupleTerminals ι origin base pivot last S) :=
  hS.image (continuous_const.mul ((continuous_const.mul
    (hι.comp (continuous_apply last))).mul continuous_const))

omit [TopologicalSpace N] in
/-- A source terminal relative to the original starting point maps to
the terminal coordinate of the centered tuple under the normalized pair. -/
theorem centered_image_terminal_mem {h : ℕ} {Λ : ℝ≥0}
    (p : NormalizedPair G Λ) (ι : N → G) (origin base pivot : G)
    (last : Fin h) (S : Set (Fin h → N)) {y : Fin h → G}
    (hy : y ∈ (fun v : Fin h → N => fun i =>
      basedImage p.val.1 origin (base * ι (v i) * pivot)) '' S) :
    ∃ z ∈ relativeTupleTerminals ι origin base pivot last S,
      y last = (normalizedTranslate origin p).val.1 z := by
  obtain ⟨v, hv, rfl⟩ := hy
  refine ⟨origin⁻¹ * (base * ι (v last) * pivot), ⟨v, hv, rfl⟩, ?_⟩
  simp only [normalizedTranslate, translatePair, ContinuousMap.coe_mk,
    mul_inv_cancel_left, basedImage]

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

end PolycyclicRecognition

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

set_option maxHeartbeats 1000000 in
theorem wordPrefix_succ {G : Type} [Monoid G] (u : ℕ → G) (m : ℕ) :
    wordPrefix u (m + 1) = wordPrefix u m * u m := by
  unfold wordPrefix
  rw [List.ofFn_succ', List.prod_concat]
  rfl

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanWordLifts
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Lifting actual ambient word paths to the Cartan factors

One compact set of factor increments lifts every word over a compact ambient
increment set. The lift reproduces every prefix exactly, so height control
can be applied to the actual ambient path.
-/

noncomputable section

namespace PolycyclicRecognition

set_option maxHeartbeats 1000000 in
@[simp] theorem map_wordPrefix {A B : Type} [Monoid A] [Monoid B]
    (f : A →* B) (u : ℕ → A) (m : ℕ) :
    f (wordPrefix u m) = wordPrefix (fun i => f (u i)) m := by
  induction m with
  | zero => simp only [wordPrefix_zero, map_one]
  | succ m ih => simp only [wordPrefix_succ, map_mul, ih]

open scoped Manifold

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_SemidirectPrefixTuples
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact accumulated lifts of a finite tuple of transitions -/

noncomputable section
namespace PolycyclicRecognition

theorem wordPrefix_succ_left {A : Type} [Monoid A] (u : ℕ → A) (n : ℕ) :
    wordPrefix u (n + 1) = u 0 * wordPrefix (fun j => u (j + 1)) n := by
  unfold wordPrefix
  rw [List.ofFn_succ, List.prod_cons]
  rfl

variable {N D G : Type} [Group N] [Group D] [Group G]

variable [MeasurableSpace N] [MeasurableMul₂ N] [MeasurableInv N]

theorem prefixCoordinateEquiv_eq_wordPrefix (u : ℕ → N) (h : ℕ) (i : Fin h) :
    prefixCoordinateEquiv h (fun j => u j.val) i = wordPrefix u (i.val + 1) := by
  induction h generalizing u with
  | zero => exact Fin.elim0 i
  | succ h ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [prefixCoordinateEquiv_zero, Fin.val_zero, wordPrefix_succ_left,
        wordPrefix_zero, mul_one]
    · rw [prefixCoordinateEquiv_succ]
      change u 0 * prefixCoordinateEquiv h (fun k => u (k.val + 1)) j = _
      rw [ih (fun k => u (k + 1)) j]
      exact (wordPrefix_succ_left u (j.val + 1)).symm

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_SuccessfulBlockPaths
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Paths for individual blocks of a successful sampled word

The initial point of each block is the exact product of all preceding
blocks. This is needed when successive blocks use different profile labels.
-/

namespace PolycyclicRecognition

variable {G : Type} [Group G]

/-- Restrict successful sheets to any complete block, retaining its true
starting state rather than restarting the full word at the identity. -/
theorem WordSheetsGood.ofFn_block {A : Set G} {x : G} {h : ℕ}
    (u : ℕ → List G)
    (hg : WordSheetsGood A x (List.ofFn (fun j : Fin h => u j.val)).flatten)
    (i : Fin h) :
    WordSheetsGood A (x * wordPrefix (fun j => (u j).prod) i.val) (u i.val) := by
  induction h generalizing x u with
  | zero => exact Fin.elim0 i
  | succ h ih =>
    rw [List.ofFn_succ, List.flatten_cons] at hg
    obtain ⟨hfirst, htail⟩ := (wordSheetsGood_append_iff A x _ _).mp hg
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa only [Fin.val_zero, wordPrefix_zero, mul_one] using hfirst
    · simp only [Fin.val_succ, wordPrefix_succ_left, ← mul_assoc]
      exact ih (fun k => u (k + 1)) htail j

end PolycyclicRecognition

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_GoodFiniteWordVertices
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual good vertices of a successful finite block -/

noncomputable section
namespace PolycyclicRecognition

variable {G : Type} [Group G]

theorem WordSheetsGood.take_prod_mem {A : Set G} {x : G} {u : List G}
    (hg : WordSheetsGood A x u) (j : ℕ) : x * (u.take j).prod ∈ A := by
  induction u generalizing x j with
  | nil => simpa only [List.take_nil, List.prod_nil, mul_one] using hg.start
  | cons a u ih =>
    cases j with
    | zero => simpa only [List.take_zero, List.prod_nil, mul_one] using hg.1
    | succ j =>
      simpa only [List.take_succ_cons, List.prod_cons, ← mul_assoc] using ih hg.2 j

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
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_SequenceSubsequences
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Passing all profile data to the same sequence of good scales -/

namespace PolycyclicRecognition

open Filter

/-- Subexponential losses are unchanged on a subsequence tending to infinity. -/
theorem HasSubexponentialLowerBoundSeq.comp {scale f : ℕ → ℝ} {v : ℕ → ℕ}
    (hf : HasSubexponentialLowerBoundSeq scale f) (hv : Tendsto v atTop atTop) :
    HasSubexponentialLowerBoundSeq (scale ∘ v) (f ∘ v) :=
  fun ε hε => hv.eventually (hf ε hε)

theorem HasSubexponentialUpperBoundSeq.comp {scale f : ℕ → ℝ} {v : ℕ → ℕ}
    (hf : HasSubexponentialUpperBoundSeq scale f) (hv : Tendsto v atTop atTop) :
    HasSubexponentialUpperBoundSeq (scale ∘ v) (f ∘ v) :=
  fun ε hε => hv.eventually (hf ε hε)

end PolycyclicRecognition

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_GoodProfileFlow
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Good profile control along the actual converging horizontal flow -/

noncomputable section

namespace PolycyclicRecognition

open Set Filter
open scoped Topology

/-- Recover the physical-scale image height from the actual normalized
profile, with its prescribed common center. -/
theorem height_bound_of_rescaled_profile
    {G W Z : Type} [Group G] [NormedAddCommGroup W] [NormedSpace ℝ W]
    (J : G → W) (x n : G) (s : ℝ) (φ : Z → G) (z : Z) (w : W) {ε : ℝ}
    (h : ‖rescaledMapProfile J x n s φ z - w‖ ≤ ε) :
    ‖J (x * n * φ z) - J x - Real.exp s • w‖ ≤ Real.exp s * ε := by
  have he : J (x * n * φ z) - J x - Real.exp s • w =
      Real.exp s • (rescaledMapProfile J x n s φ z - w) := by
    simp only [rescaledMapProfile, smul_sub, smul_smul,
      mul_inv_cancel₀ (Real.exp_ne_zero s), one_smul]
  rw [he, norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos s)]
  exact mul_le_mul_of_nonneg_left h (Real.exp_pos s).le

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_CenteredProfilePaths
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Centering profile-controlled paths at their actual initial image -/

namespace PolycyclicRecognition

open Set

variable {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- Centering costs only the profile error at the initial point. -/
theorem norm_centered_sub_smul_le {u a c w w₀ : W} {r B B₀ : ℝ}
    (hu : ‖u - c - r • w‖ ≤ B) (ha : ‖a - c - r • w₀‖ ≤ B₀) :
    ‖u - a - r • (w - w₀)‖ ≤ B + B₀ := by
  have he : u - a - r • (w - w₀) = (u - c - r • w) - (a - c - r • w₀) := by
    rw [smul_sub]
    abel
  rw [he]
  exact (norm_sub_le _ _).trans (add_le_add hu ha)

end PolycyclicRecognition

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_CenteredImagePaths
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Centered image paths for the two probe sheets -/

noncomputable section
namespace PolycyclicRecognition

open Set
open scoped NNReal

section Metric

variable {X G : Type} [PseudoMetricSpace X] [Group G] [PseudoMetricSpace G]
  [IsTopologicalGroup G] [IsIsometricSMul G G]

/-- Quasi-isometry Lipschitz control transfers to the centered path with
the same scaling of both the speed and the additive error. -/
theorem centeredImagePath_metric_bound (f : X → G) {K : ℝ≥0} (hf : LipschitzWith K f)
    {a b : X} (γ : Path a b) {L κ : ℝ} (hγ : PathMetricBound γ L κ) :
    PathMetricBound (centeredImagePath f hf.continuous γ) (K * L) (K * κ) := by
  intro s t
  change dist ((f a)⁻¹ * f (γ s)) ((f a)⁻¹ * f (γ t)) ≤ _
  rw [dist_mul_left]
  calc
    _ ≤ K * dist (γ s) (γ t) := hf.dist_le_mul _ _
    _ ≤ K * (L * |(s : ℝ) - t| + κ) :=
      mul_le_mul_of_nonneg_left (hγ s t) K.coe_nonneg
    _ = _ := by ring

end Metric

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_CoarsePathRadius
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Radius control for logarithmic-error paths

The support-path parameter bounds imply a single linear ambient ball bound
for every sample, uniformly at all scales at least one.
-/

namespace PolycyclicRecognition

variable {X : Type} [PseudoMetricSpace X] {x y : X}

/-- A coarse path stays within its speed plus its additive error of its source. -/
theorem PathMetricBound.dist_source_le {p : Path x y} {L κ : ℝ}
    (h : PathMetricBound p L κ) (hL : 0 ≤ L) (t : unitInterval) :
    dist x (p t) ≤ L + κ := by
  have hb := h 0 t
  rw [Path.source, Set.Icc.coe_zero, zero_sub, abs_neg,
    abs_of_nonneg t.property.1] at hb
  exact hb.trans (by nlinarith [t.property.2])

end PolycyclicRecognition

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_ShortSheetBridges
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Short bridges between the two sheets at a common pivot -/

noncomputable section
namespace PolycyclicRecognition

open Set
open scoped NNReal

theorem exists_short_path_of_minimizing_paths
    {G : Type} [Group G] [MetricSpace G] [IsTopologicalGroup G] [IsIsometricSMul G G]
    (hpath : ∀ g : G, ∃ γ : ℝ → G, γ 0 = 1 ∧ γ 1 = g ∧
      ∀ t ∈ Icc (0 : ℝ) 1, ∀ u ∈ Icc (0 : ℝ) 1,
        dist (γ t) (γ u) ≤ dist 1 g * |t - u|) (a b : G) :
    ∃ γ : Path a b, PathMetricBound γ (dist a b) 0 := by
  obtain ⟨f, hf0, hf1, hf⟩ := hpath (a⁻¹ * b)
  have hd : dist (1 : G) (a⁻¹ * b) = dist a b := by
    simpa only [mul_one, mul_inv_cancel_left] using
      (dist_mul_left a (1 : G) (a⁻¹ * b)).symm
  have hlip : LipschitzWith ⟨dist a b, dist_nonneg⟩ (fun t : unitInterval => f t) := by
    apply LipschitzWith.of_dist_le_mul
    intro s t
    change dist (f s) (f t) ≤ dist a b * dist s t
    rw [Subtype.dist_eq, Real.dist_eq, ← hd]
    exact hf s s.property t t.property
  let γ : Path a b := {
    toFun := fun t => a * f t
    continuous_toFun := continuous_const.mul hlip.continuous
    source' := by simp only [Icc.coe_zero, hf0, mul_one]
    target' := by simp only [Icc.coe_one, hf1, mul_inv_cancel_left] }
  refine ⟨γ, ?_⟩
  intro s t
  change dist (a * f s) (a * f t) ≤ _
  rw [dist_mul_left, add_zero]
  simpa only [hd] using hf s s.property t t.property

/-- Adding the two pivot bridges preserves the template, with only the
Lipschitz image of their lengths added to the height error. -/
theorem exists_bridged_profile_path
    {X W : Type} [PseudoMetricSpace X] [NormedAddCommGroup W] [NormedSpace ℝ W]
    (hpath : ∀ a b : X, ∃ γ : Path a b, PathMetricBound γ (dist a b) 0)
    {a a' b' b : X} (middle : Path a' b')
    {L κ δ B r : ℝ} (hκ : 0 ≤ κ) (hδ : 0 ≤ δ) (hB : 0 ≤ B)
    (hm : PathMetricBound middle L κ) (ha : dist a a' ≤ δ) (hb : dist b' b ≤ δ)
    (J : X → W) {K : ℝ≥0} (hJ : LipschitzWith K J)
    (E : Set W) (hE0 : (0 : W) ∈ E)
    (himage : ∀ t, ∃ w ∈ E, ‖J (middle t) - J a' - r • w‖ ≤ B) :
    ∃ γ : Path a b, PathMetricBound γ (4 * (max L 0 + δ)) (4 * κ) ∧
      ∀ t, ∃ w ∈ E, ‖J (γ t) - J a - r • w‖ ≤ B + 2 * K * δ := by
  obtain ⟨first, hfirst⟩ := hpath a a'
  obtain ⟨last, hlast⟩ := hpath b' b
  let C := max L 0 + δ
  have hC : 0 ≤ C := add_nonneg (le_max_right _ _) hδ
  have hfirst' : PathMetricBound first C κ := hfirst.mono
    (ha.trans (le_add_of_nonneg_left (le_max_right _ _))) hκ
  have hlast' : PathMetricBound last C κ := hlast.mono
    (hb.trans (le_add_of_nonneg_left (le_max_right _ _))) hκ
  have hm' : PathMetricBound middle C κ := hm.mono
    ((le_max_left _ _).trans (le_add_of_nonneg_right hδ)) le_rfl
  have hfm := hfirst'.trans hκ hm'
  have hlast'' : PathMetricBound last (2 * C) (2 * κ) :=
    hlast'.mono (by linarith) (by linarith)
  have hbound := hfm.trans (by linarith : 0 ≤ 2 * κ) hlast''
  let S := {z : X | ∃ w ∈ E, ‖J z - J a - r • w‖ ≤ B + 2 * K * δ}
  have hshift : ‖J a' - J a‖ ≤ K * δ := by
    rw [← dist_eq_norm]
    exact (hJ.dist_le_mul a' a).trans
      (mul_le_mul_of_nonneg_left (by simpa only [dist_comm] using ha) K.coe_nonneg)
  have hmiddle : ∀ t, middle t ∈ S := by
    intro t
    obtain ⟨w, hw, he⟩ := himage t
    refine ⟨w, hw, ?_⟩
    calc
      ‖J (middle t) - J a - r • w‖ ≤ ‖J (middle t) - J a' - r • w‖ + ‖J a' - J a‖ := by
        convert norm_add_le (J (middle t) - J a' - r • w) (J a' - J a) using 1
        all_goals try with_reducible_and_instances rfl
        congr 1
        abel
      _ ≤ B + K * δ := add_le_add he hshift
      _ ≤ B + 2 * K * δ := by nlinarith [mul_nonneg K.coe_nonneg hδ]
  have hfirstS : ∀ t, first t ∈ S := by
    intro t
    refine ⟨0, hE0, ?_⟩
    rw [smul_zero, sub_zero, ← dist_eq_norm]
    have hd := hfirst.dist_source_le (dist_nonneg (x := a) (y := a')) t
    have hd' : dist (first t) a ≤ δ := by
      rw [dist_comm]
      exact hd.trans (by simpa only [add_zero] using ha)
    have he := (hJ.dist_le_mul (first t) a).trans
      (mul_le_mul_of_nonneg_left hd' K.coe_nonneg)
    exact he.trans (by nlinarith [mul_nonneg K.coe_nonneg hδ])
  have hlastS : ∀ t, last t ∈ S := by
    intro t
    obtain ⟨w, hw, he⟩ := himage 1
    rw [Path.target] at he
    have hd := (hlast.dist_source_le (dist_nonneg (x := b') (y := b)) t).trans
      (by simpa only [add_zero] using hb)
    have hdiff : ‖J (last t) - J b'‖ ≤ K * δ := by
      rw [← dist_eq_norm]
      exact (hJ.dist_le_mul (last t) b').trans
        (mul_le_mul_of_nonneg_left (by simpa only [dist_comm] using hd) K.coe_nonneg)
    refine ⟨w, hw, ?_⟩
    calc
      ‖J (last t) - J a - r • w‖ ≤
          ‖J (last t) - J b'‖ + ‖J b' - J a' - r • w‖ + ‖J a' - J a‖ := by
        calc
          _ = ‖(J (last t) - J b') + (J b' - J a' - r • w) + (J a' - J a)‖ := by congr 1; abel
          _ ≤ _ := (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
      _ ≤ K * δ + B + K * δ := add_le_add (add_le_add hdiff he) hshift
      _ = B + 2 * K * δ := by ring
  refine ⟨(first.trans middle).trans last, ?_,
    path_trans_range_mem (path_trans_range_mem hfirstS hmiddle) hlastS⟩
  have hL : 4 * (max L 0 + δ) = 2 * (2 * C) := by dsimp only [C] <;> ring
  have hκ' : 4 * κ = 2 * (2 * κ) := by ring
  rw [hL, hκ']
  exact hbound

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_SourceBundleBlockPaths
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact source-bundle boundaries and their individual paths -/

noncomputable section
namespace PolycyclicRecognition

open Set
open scoped Manifold

variable {L I : Type} [LieRing L] [LieAlgebra ℝ L]
  {E N : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace N] [ChartedSpace E N] [Group N]
  [LieGroup (𝓘(ℝ, E)) ⊤ N]

/-- The product of each actual sampled block is its prescribed conjugated
source-bundle product. -/
theorem sampledBlockWord_source_product {h m : ℕ}
    (lie : L ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, E)) N)
    (Exp : GroupLieAlgebra (𝓘(ℝ, E)) N → N)
    (X : I → L) (s : I → ℝ) (letters : Fin m → I) (r : ℝ)
    (φ : Fin h → N ≃* N) (sample : ℕ → ℝ → N)
    (hsample : ∀ (i : Fin h) (j : Fin m) t,
      sample (finProdFinEquiv (i, j)).val t = φ i
        (Exp (lie (t • (Real.exp (r * s (letters j)) • X (letters j))))))
    (t : Fin (h * m + h * m) → ℝ) (i : Fin h) :
    (sampledBlockWord sample t i).prod =
      φ i (sourceBundleProduct lie Exp X s letters (bundleParameterChart h m) r t i) := by
  simp only [sampledBlockWord, sourceBundleProduct, bundleParameterChart_left,
    bundleParameterChart_right, map_list_prod, List.map_ofFn, Function.comp_def, hsample]

section BoundaryCoordinates

variable [MeasurableSpace N] [MeasurableMul₂ N] [MeasurableInv N]

omit [TopologicalSpace N] in
theorem sourceBundleBoundary_succ {h : ℕ} (n : N) (φ : Fin h → N ≃* N)
    (v : Fin h → N) (i : Fin h) :
    sourceBundleBoundary n φ v (i.val + 1) =
      n * prefixCoordinateEquiv h (fun j => φ j (v j)) i := by
  let u := fun k => if hk : k < h then φ ⟨k, hk⟩ (v ⟨k, hk⟩) else 1
  change n * wordPrefix u (i.val + 1) = _
  rw [← prefixCoordinateEquiv_eq_wordPrefix u h i]
  have he : (fun j : Fin h => u j.val) = fun j => φ j (v j) := by
    funext j
    simp only [u, dite_eq_left j.isLt]
  rw [he]

omit [TopologicalSpace N] in
/-- The paths' boundary coordinates coincide with the coordinates of the
Haar-preserving source-state map. -/
theorem sourceBundleBoundary_eq_stateEquiv {h : ℕ} (n : N) (φ : Fin h → N ≃* N)
    (ψ : Fin h → N ≃ᵐ N) (hψ : ∀ i z, ψ i z = φ i z) (v : Fin h → N) (i : Fin h) :
    sourceBundleBoundary n φ v (i.val + 1) = sourceBundleStateEquiv h n ψ v i := by
  rw [sourceBundleBoundary_succ, sourceBundleStateEquiv_apply]
  apply congrArg (fun u : Fin h → N => n * prefixCoordinateEquiv h u i)
  funext j
  exact (hψ j (v j)).symm

end BoundaryCoordinates

theorem sampledBlockProducts_source_product {h m : ℕ}
    (lie : L ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, E)) N)
    (Exp : GroupLieAlgebra (𝓘(ℝ, E)) N → N)
    (X : I → L) (s : I → ℝ) (letters : Fin m → I) (r : ℝ)
    (φ : Fin h → N ≃* N) (sample : ℕ → ℝ → N)
    (hsample : ∀ (i : Fin h) (j : Fin m) t,
      sample (finProdFinEquiv (i, j)).val t = φ i
        (Exp (lie (t • (Real.exp (r * s (letters j)) • X (letters j))))))
    (t : Fin (h * m + h * m) → ℝ) :
    sampledBlockProducts sample t = fun k => if hk : k < h then
      φ ⟨k, hk⟩ (sourceBundleProduct lie Exp X s letters (bundleParameterChart h m) r t ⟨k, hk⟩)
        else 1 := by
  funext k
  unfold sampledBlockProducts
  split_ifs with hk
  · exact sampledBlockWord_source_product lie Exp X s letters r φ sample hsample t ⟨k, hk⟩
  · rfl

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_SuccessfulSourceWord
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Good conjugated words furnished by the successful bundle parameters -/

noncomputable section
namespace PolycyclicRecognition

open Set
open scoped Manifold

variable {L I : Type} [LieRing L] [LieAlgebra ℝ L]
  {E N : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace N] [ChartedSpace E N] [Group N]
  [LieGroup (𝓘(ℝ, E)) ⊤ N]

/-- Each global successful parameter gives exactly the good word needed
by the profile path construction on its own bundle sheet. -/
theorem successful_sourceBundle_word_good {h m : ℕ}
    (lie : L ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, E)) N)
    (Exp : GroupLieAlgebra (𝓘(ℝ, E)) N → N)
    (X : I → L) (s : I → ℝ) (letters : Fin m → I) (r : ℝ)
    (φ : Fin h → N ≃* N) (sample : ℕ → ℝ → N)
    (hsub : ∀ j u v, sample j u * (sample j v)⁻¹ = sample j (u - v))
    (hsample : ∀ (i : Fin h) (j : Fin m) t,
      sample (finProdFinEquiv (i, j)).val t = φ i
        (Exp (lie (t • (Real.exp (r * s (letters j)) • X (letters j))))))
    (Good : Set N) (initial : N) (hi : initial ∈ Good)
    (t : Fin (h * m + h * m) → ℝ)
    (hs : SwitchSuccessful (fun _ => Good) 0 (h * m) initial
      (sampledSwitchParameters sample (h * m) t)) (i : Fin h) :
    WordSheetsGood Good
      (sourceBundleBoundary initial φ
        (sourceBundleProduct lie Exp X s letters (bundleParameterChart h m) r t) i.val)
      (List.ofFn (fun j : Fin m => φ i (Exp (lie
        ((t (Fin.castAdd (h * m) (finProdFinEquiv (i, j))) -
          t (Fin.natAdd (h * m) (finProdFinEquiv (i, j)))) •
            (Real.exp (r * s (letters j)) • X (letters j))))))) := by
  let w : ℕ → List N := fun j =>
    if hj : j < h then sampledBlockWord sample t ⟨j, hj⟩ else []
  have hw : (fun j => (w j).prod) = sampledBlockProducts sample t := by
    funext j
    dsimp only [w, sampledBlockProducts]
    split_ifs <;> rfl
  have hg := wordSheetsGood_sampled Good sample hsub (h * m) t initial hi hs
  rw [ofFn_eq_flatten_bundles] at hg
  have hg' : WordSheetsGood Good initial (List.ofFn (fun j : Fin h => w j.val)).flatten := by
    simpa only [w, sampledBlockWord, dite_eq_left (Fin.isLt _)] using hg
  have hb := hg'.ofFn_block w i
  rw [hw, show w i.val = sampledBlockWord sample t i by simp only [w, dite_eq_left i.isLt]] at hb
  have hproducts := sampledBlockProducts_source_product lie Exp X s letters r φ sample hsample t
  change WordSheetsGood Good (initial * wordPrefix _ i.val) _
  rw [← hproducts]
  simpa only [sampledBlockWord, hsample] using hb

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_ProfileChainHeightBounds
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Relative image heights from a common affine profile along the chain -/

noncomputable section
namespace PolycyclicRecognition

variable {G W Z V : Type} [Group G]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  [AddCommGroup V] [Module ℝ V]

/-- Two different sheets can be centered at the same original image.
Their common affine offset cancels from the relative height estimate. -/
theorem relative_height_of_common_affine_profiles
    (J : G → W) (x k l : G) (r : ℝ) (φ : Z → G)
    (q : Z → V) (A : V →ₗ[ℝ] W) (b : W) (z z₀ : Z)
    {ε ε₀ : ℝ}
    (hz : ‖rescaledMapProfile J x k r φ z - (A (q z) + b)‖ ≤ ε)
    (hz₀ : ‖rescaledMapProfile J x l r φ z₀ - (A (q z₀) + b)‖ ≤ ε₀) :
    ‖J (x * k * φ z) - J (x * l * φ z₀) -
      Real.exp r • A (q z - q z₀)‖ ≤ Real.exp r * (ε + ε₀) := by
  have hh := norm_centered_sub_smul_le
    (height_bound_of_rescaled_profile J x k r φ z (A (q z) + b) hz)
    (height_bound_of_rescaled_profile J x l r φ z₀ (A (q z₀) + b) hz₀)
  simpa only [map_sub, add_sub_add_right_eq_sub, mul_add] using hh

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_SheetEndpointHeight
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.CartanFactorModel.realScaleProfile_apply _root_.OAI.PolycyclicRecognition.CartanFactorModel.sampledProbeProfile_apply _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Small endpoint heights at the common facet pivot -/

noncomputable section
namespace PolycyclicRecognition

open Set
open scoped NNReal

/-- At one chart point only the common limiting value matters. In
particular, the offset and linear part of the affine profile cancel. -/
theorem common_profile_endpoint_height
    {G W Z : Type} [Group G] [NormedAddCommGroup W] [NormedSpace ℝ W]
    (J : G → W) (x k l d : G) (r : ℝ) (φ : Z → G) (z₀ : Z) (c : W)
    (hd : φ z₀ = d) {ε : ℝ}
    (hk : ‖rescaledMapProfile J x k r φ z₀ - c‖ ≤ ε)
    (hl : ‖rescaledMapProfile J x l r φ z₀ - c‖ ≤ ε) :
    ‖J (x * l * d) - J (x * k * d)‖ ≤ 2 * Real.exp r * ε := by
  have he := relative_height_of_common_affine_profiles J x l k r φ
    (fun _ : Z => (0 : W)) (0 : W →ₗ[ℝ] W) c z₀ z₀ (by simpa using hl) (by simpa using hk)
  simpa only [hd, sub_self, map_zero, smul_zero, sub_zero, mul_add,
    two_mul, add_mul] using he

/-- A short bridge at each endpoint adds twice its Lipschitz image to the
endpoint height error. This is separate from control of the whole path. -/
theorem endpoint_height_of_short_bridges
    {X W : Type} [PseudoMetricSpace X] [NormedAddCommGroup W]
    (J : X → W) {K : ℝ≥0} (hJ : LipschitzWith K J)
    {a a' b' b : X} {δ B : ℝ}
    (ha : dist a a' ≤ δ) (hb : dist b' b ≤ δ)
    (hmid : ‖J b' - J a'‖ ≤ B) :
    ‖J b - J a‖ ≤ B + 2 * K * δ := by
  have hleft : ‖J a' - J a‖ ≤ K * δ := by
    rw [← dist_eq_norm]
    exact (hJ.dist_le_mul a' a).trans
      (mul_le_mul_of_nonneg_left (by simpa only [dist_comm] using ha) K.coe_nonneg)
  have hright : ‖J b - J b'‖ ≤ K * δ := by
    rw [← dist_eq_norm]
    exact (hJ.dist_le_mul b b').trans
      (mul_le_mul_of_nonneg_left (by simpa only [dist_comm] using hb) K.coe_nonneg)
  calc
    ‖J b - J a‖ = ‖(J b - J b') + (J b' - J a') + (J a' - J a)‖ := by congr 1; abel
    _ ≤ ‖J b - J b'‖ + ‖J b' - J a'‖ + ‖J a' - J a‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ K * δ + B + K * δ := add_le_add (add_le_add hright hmid) hleft
    _ = B + 2 * K * δ := by ring

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_BridgedProfileBounds
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # One common error for path lifting and endpoint accumulation -/

noncomputable section
namespace PolycyclicRecognition

open Set
open scoped NNReal

/-- Normalize the two pivot-bridge errors into the same tolerance used by
the Cartan tuple lifting theorem. The endpoint bound has no logarithmic term. -/
theorem exists_bridged_profile_bounds
    {X W : Type} [PseudoMetricSpace X] [NormedAddCommGroup W] [NormedSpace ℝ W]
    (hpath : ∀ a b : X, ∃ γ : Path a b, PathMetricBound γ (dist a b) 0)
    {a a' b' b : X} (middle : Path a' b')
    {C r δ ε : ℝ} (hC : 0 ≤ C) (hr : 1 ≤ r) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hε : 0 ≤ ε)
    (hm : PathMetricBound middle (C * r) (C * (1 + Real.log (2 + r))))
    (ha : dist a a' ≤ δ * r) (hb : dist b' b ≤ δ * r)
    (J : X → W) {K : ℝ≥0} (hJ : LipschitzWith K J)
    (E : Set W) (hE0 : (0 : W) ∈ E)
    (himage : ∀ t, ∃ w ∈ E, ‖J (middle t) - J a' - r • w‖ ≤
      2 * r * ε + C * (1 + Real.log (2 + r)))
    (hend : ‖J b' - J a'‖ ≤ 2 * r * ε) :
    let η := 2 * ε + 2 * K * δ
    let A := 4 * (C + 1)
    ∃ γ : Path a b,
      PathMetricBound γ (A * r) (A * (1 + Real.log (2 + r))) ∧
      (∀ t, ∃ w ∈ E, ‖J (γ t) - J a - r • w‖ ≤
        2 * r * η + A * (1 + Real.log (2 + r))) ∧
      ‖J b - J a‖ ≤ η * r := by
  dsimp only
  have hr0 : 0 ≤ r := by linarith
  have hlog : 0 ≤ 1 + Real.log (2 + r) := by
    have := Real.log_nonneg (show 1 ≤ 2 + r by linarith)
    linarith
  have hκ := mul_nonneg hC hlog
  have hB : 0 ≤ 2 * r * ε + C * (1 + Real.log (2 + r)) := by positivity
  obtain ⟨path, hmetric, hheight⟩ := exists_bridged_profile_path hpath middle hκ
    (mul_nonneg hδ hr0) hB hm ha hb J hJ E hE0 himage
  have hsmall := endpoint_height_of_short_bridges J hJ ha hb hend
  refine ⟨path, hmetric.mono ?_ ?_, ?_, ?_⟩
  · rw [max_eq_left (mul_nonneg hC hr0)]
    nlinarith [mul_le_mul_of_nonneg_right hδ1 hr0]
  · nlinarith
  · intro t
    obtain ⟨w, hw, he⟩ := hheight t
    refine ⟨w, hw, he.trans ?_⟩
    have hη : 0 ≤ 2 * ε + 2 * K * δ := by positivity
    have heq : 2 * r * ε + C * (1 + Real.log (2 + r)) + 2 * K * (δ * r) =
        r * (2 * ε + 2 * K * δ) + C * (1 + Real.log (2 + r)) := by ring
    rw [heq]
    nlinarith [mul_nonneg hr0 hη]
  · convert hsmall using 1; ring

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_CenteredTuplePaths
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Centering every transition of the actual image tuple -/

noncomputable section
namespace PolycyclicRecognition

open Set
open scoped NNReal

variable {X G : Type} [Group G]

variable [TopologicalSpace X] [TopologicalSpace G] [IsTopologicalGroup G]

variable {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W]

theorem centeredTuplePath_height_bound
    (f : X → G) (hf : Continuous f) (v : ℕ → X) {h : ℕ}
    (path : ∀ j : Fin h, Path (v j.val) (v (j.val + 1)))
    (π : G →* Multiplicative W) (E : Fin h → Set W) (r B : ℝ)
    (hheight : ∀ j t, ∃ w ∈ E j,
      ‖(π (f (path j t))).toAdd - (π (f (v j.val))).toAdd - r • w‖ ≤ B) :
    ∀ j t, ∃ w ∈ E j, ‖(π (centeredTuplePath f hf v path j t)).toAdd - r • w‖ ≤ B := by
  intro j t
  obtain ⟨w, hw, he⟩ := hheight j t
  refine ⟨w, hw, ?_⟩
  change ‖(π ((f (v j.val))⁻¹ * f (path j t))).toAdd - r • w‖ ≤ B
  rw [map_mul, map_inv, toAdd_mul, toAdd_inv]
  simpa only [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using he

end PolycyclicRecognition

namespace PolycyclicRecognition

open scoped NNReal

variable {X G : Type} [PseudoMetricSpace X] [Group G] [PseudoMetricSpace G]
  [IsTopologicalGroup G] [IsIsometricSMul G G]

theorem centeredTuplePath_metric_bound
    (f : X → G) {K : ℝ≥0} (hf : LipschitzWith K f) (v : ℕ → X) {h : ℕ}
    (path : ∀ j : Fin h, Path (v j.val) (v (j.val + 1))) (L κ : ℝ)
    (hmetric : ∀ j, PathMetricBound (path j) L κ) :
    ∀ j, PathMetricBound (centeredTuplePath f hf.continuous v path j) (K * L) (K * κ) :=
  fun j => centeredImagePath_metric_bound f hf (path j) (hmetric j)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_FiniteSupportChainPaths
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Controlled image paths along the selected finite generator chains -/

noncomputable section
namespace PolycyclicRecognition

open Set
open scoped NNReal

/-- Concatenate the actual selected edges. Both the metric constants and
the common image restriction are retained with a fixed finite loss. -/
theorem exists_finite_chain_path
    {X : Type} [PseudoMetricSpace X] (L κ : ℝ) (hL : 0 ≤ L) (hκ : 0 ≤ κ)
    (S : Set X) :
    ∀ (N : ℕ) (vertex : Fin (N + 1) → X)
      (edge : ∀ j : Fin N, Path (vertex j.castSucc) (vertex j.succ)),
      vertex 0 ∈ S →
      (∀ j, PathMetricBound (edge j) L κ) →
      (∀ j t, edge j t ∈ S) →
      ∃ path : Path (vertex 0) (vertex (Fin.last N)),
        PathMetricBound path (L * 2 ^ N) (κ * 2 ^ N) ∧ ∀ t, path t ∈ S := by
  intro N
  induction N with
  | zero =>
      intro vertex edge hzero hbound hmem
      refine ⟨Path.refl (vertex 0), ?_, ?_⟩
      · intro s t
        simp only [Path.refl_apply, dist_self, pow_zero, mul_one]
        positivity
      · intro t
        exact hzero
  | succ N ih =>
      intro vertex edge hzero hbound hmem
      obtain ⟨path, hp, hpath⟩ := ih (fun j => vertex j.castSucc)
        (fun j => edge j.castSucc) hzero (fun j => hbound j.castSucc)
        (fun j => hmem j.castSucc)
      have hpow : (1 : ℝ) ≤ 2 ^ N := one_le_pow₀ (by norm_num)
      have he : PathMetricBound (edge (Fin.last N)) (L * 2 ^ N) (κ * 2 ^ N) :=
        (hbound _).mono (le_mul_of_one_le_right hL hpow) (le_mul_of_one_le_right hκ hpow)
      refine ⟨path.trans (edge (Fin.last N)), ?_, path_trans_range_mem hpath (hmem _)⟩
      have hb := hp.trans (mul_nonneg hκ (pow_nonneg (by norm_num) _)) he
      have hL' : L * 2 ^ (N + 1) = 2 * (L * 2 ^ N) := by rw [pow_succ]; ring
      have hκ' : κ * 2 ^ (N + 1) = 2 * (κ * 2 ^ N) := by rw [pow_succ]; ring
      rw [hL', hκ']
      exact hb

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_ReachableTuplePaths
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Transfer paths of the retained successful states to their image tuples -/

noncomputable section
namespace PolycyclicRecognition

open Set
open scoped NNReal

variable {N G W T : Type} [Group N] [Group G] [PseudoMetricSpace G]
  [IsTopologicalGroup G] [IsIsometricSMul G G]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- Successful parameters may be correlated. Only their actual reachable
states and paths are used when constructing all image-tuple transitions. -/
theorem reachable_image_tuple_paths
    {h : ℕ} (ι : N →* G) (f : G → G) {Λ : ℝ≥0} (hf : LipschitzWith Λ f)
    (π : G →* Multiplicative W) (x d : G) (initial : N)
    (S : Set (Fin h → N)) (P : T → Prop) (boundary : T → ℕ → N)
    (hzero : ∀ t, P t → boundary t 0 = initial)
    (hreach : ∀ v ∈ S, ∃ t, P t ∧ ∀ i : Fin h, boundary t (i.val + 1) = v i)
    (E : Fin h → Set W) (r L κ B D : ℝ)
    (hpaths : ∀ t, P t → ∀ j : Fin h,
      ∃ γ : Path (x * ι (boundary t j.val) * d) (x * ι (boundary t (j.val + 1)) * d),
        PathMetricBound γ L κ ∧
        (∀ u, ∃ w ∈ E j, ‖(π (f (γ u))).toAdd -
          (π (f (x * ι (boundary t j.val) * d))).toAdd - r • w‖ ≤ B) ∧
        ‖(π (f (x * ι (boundary t (j.val + 1)) * d))).toAdd -
          (π (f (x * ι (boundary t j.val) * d))).toAdd‖ ≤ D) :
    ∀ y ∈ (fun v : Fin h → N => fun i =>
        (f (x * ι initial * d))⁻¹ * f (x * ι (v i) * d)) '' S,
      ∃ paths : ∀ j : Fin h, Path (1 : G)
          ((basedTuplePosition y j.val)⁻¹ * basedTuplePosition y (j.val + 1)),
        (∀ j, PathMetricBound (paths j) (Λ * L) (Λ * κ)) ∧
        (∀ j u, ∃ w ∈ E j, ‖(π (paths j u)).toAdd - r • w‖ ≤ B) ∧
        ∀ j : Fin h,
          ‖(π ((basedTuplePosition y j.val)⁻¹ * basedTuplePosition y (j.val + 1))).toAdd‖ ≤ D := by
  rintro y ⟨v, hv, hy⟩
  obtain ⟨t, ht, hcoords⟩ := hreach v hv
  let vertex := fun j => x * ι (boundary t j) * d
  have heq : (fun i : Fin h => (f (x * ι initial * d))⁻¹ * f (x * ι (v i) * d)) =
      centeredVertexTuple f vertex h := by
    funext i
    dsimp only [centeredVertexTuple, vertex]
    rw [hzero t ht, hcoords i]
  have hy' : y = centeredVertexTuple f vertex h := hy.symm.trans heq
  clear hy heq
  subst y
  choose path hmetric hheight hend using hpaths t ht
  refine ⟨centeredTuplePath f hf.continuous vertex path,
    centeredTuplePath_metric_bound f hf vertex path L κ hmetric,
    centeredTuplePath_height_bound f hf.continuous vertex path π E r B hheight, ?_⟩
  intro j
  rw [centeredVertexTuple_transition, map_mul, map_inv, toAdd_mul, toAdd_inv]
  simpa only [vertex, sub_eq_add_neg, add_comm] using hend j

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_SourceBundleTerminalPaths
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A single source terminal path through the successful bundle boundaries -/

noncomputable section
namespace PolycyclicRecognition

open Set
open scoped NNReal

variable {N G W : Type} [Group N] [Group G] [PseudoMetricSpace G]
  [IsTopologicalGroup G] [IsIsometricSMul G G]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- All source bundle boundaries have the same height. Their common
template therefore survives concatenation without a sum of templates. -/
theorem exists_source_bundle_terminal_path
    (ι : N →* G) (π : G →* Multiplicative W) (hN : ∀ n, π (ι n) = 1)
    {h : ℕ} (initial : N) (φ : Fin h → N ≃* N) (products : Fin h → N)
    (x d : G) (E : Set W) (hE0 : (0 : W) ∈ E)
    (r L κ B : ℝ) (hL : 0 ≤ L) (hκ : 0 ≤ κ) (hB : 0 ≤ B)
    (path : ∀ j : Fin h,
      Path (x * ι (sourceBundleBoundary initial φ products j.val) * d)
        (x * ι (sourceBundleBoundary initial φ products (j.val + 1)) * d))
    (hmetric : ∀ j, PathMetricBound (path j) L κ)
    (hheight : ∀ j t, ∃ w ∈ E,
      ‖(π (path j t)).toAdd -
          (π (x * ι (sourceBundleBoundary initial φ products j.val) * d)).toAdd -
        r • w‖ ≤ B) :
    ∃ γ : Path (1 : G)
        ((x * ι initial * d)⁻¹ * (x * ι (sourceBundleBoundary initial φ products h) * d)),
      PathMetricBound γ (L * 2 ^ h) (κ * 2 ^ h) ∧
      ∀ t, ∃ w ∈ E, ‖(π (γ t)).toAdd - r • w‖ ≤ B := by
  let vertex := fun j : Fin (h + 1) => x * ι (sourceBundleBoundary initial φ products j.val) * d
  let region := {g : G | ∃ w ∈ E, ‖(π g).toAdd - (π (vertex 0)).toAdd - r • w‖ ≤ B}
  have hv (j : Fin (h + 1)) : π (vertex j) = π (vertex 0) := by
    simp only [vertex, map_mul, hN, mul_one]
  have hedge (j : Fin h) : ∀ t, path j t ∈ region := by
    intro t
    obtain ⟨w, hw, he⟩ := hheight j t
    refine ⟨w, hw, ?_⟩
    rwa [show π (x * ι (sourceBundleBoundary initial φ products j.val) * d) =
      π (vertex 0) from hv j.castSucc] at he
  have hzero : vertex 0 ∈ region := by
    refine ⟨0, hE0, ?_⟩
    simpa only [sub_self, smul_zero, sub_zero, norm_zero] using hB
  obtain ⟨p, hp, hregion⟩ := exists_finite_chain_path L κ hL hκ region h vertex path hzero
    hmetric hedge
  let centered := centeredImagePath (id : G → G) continuous_id p
  have hm : PathMetricBound centered (L * 2 ^ h) (κ * 2 ^ h) := by
    simpa only [NNReal.coe_one, one_mul] using
      centeredImagePath_metric_bound (id : G → G) LipschitzWith.id p hp
  have hend : (x * ι initial * d)⁻¹ * (x * ι (sourceBundleBoundary initial φ products h) * d) =
      (vertex 0)⁻¹ * vertex (Fin.last h) := by
    simp only [vertex, Fin.val_zero, Fin.val_last, sourceBundleBoundary_zero]
  refine ⟨centered.cast rfl hend, hm, ?_⟩
  intro t
  obtain ⟨w, hw, he⟩ := hregion t
  refine ⟨w, hw, ?_⟩
  change ‖(π ((vertex 0)⁻¹ * p t)).toAdd - r • w‖ ≤ B
  rw [map_mul, map_inv, toAdd_mul, toAdd_inv]
  simpa only [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using he

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
/-- The root ideal lies in the canonical height kernel, hence so does its
entire integrated group. -/
theorem inclusionN_height_eq_one
    (hbij : Function.Bijective F.ExpN) (n : F.N.carrier) :
    π (F.inclusionN n) = 1 := by
  obtain ⟨x, rfl⟩ := (hbij.comp F.N.equiv.bijective).surjective n
  change π (F.inclusionN (F.ExpN (F.N.equiv x))) = 1
  rw [F.compatibleN]
  change (π (ExpG x)).toAdd = 0
  rw [hπExp]
  have hz : heightProjection T.character (x : GroupLieAlgebra (𝓘(ℝ, EG)) G) = 0 :=
    (Submodule.Quotient.mk_eq_zero _).mpr (cartanRootIdeal_le_kernel H T x.property)
  rw [hz, map_zero]

end PolycyclicRecognition.CartanFactorModel

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
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanSuccessfulBundlePaths
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instDecidableEqConeMixedWords _root_.OAI.PolycyclicRecognition.CartanWordModel.instFintypeConeMixedWords _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.CartanFactorModel.heightRay_zero _root_.OAI.PolycyclicRecognition.CartanFactorModel.realScaleProfile_apply _root_.OAI.PolycyclicRecognition.CartanFactorModel.sampledProbeProfile_apply _root_.OAI.PolycyclicRecognition.bracketWordDifferential_mul _root_.OAI.PolycyclicRecognition.cartanWeightDerivation_apply_root _root_.OAI.PolycyclicRecognition.chartExponentialFlow_zero _root_.OAI.PolycyclicRecognition.derivationSemidirectHom_apply _root_.OAI.PolycyclicRecognition.exponentialHomOfDynkin_apply_exp _root_.OAI.PolycyclicRecognition.exponentialRescaleBasis_zero _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.modelNilradicalLinearAction_apply _root_.OAI.PolycyclicRecognition.modelNilradicalRotation_apply _root_.OAI.PolycyclicRecognition.modelNilradicalRotation_mul _root_.OAI.PolycyclicRecognition.modelNilradicalRotation_one _root_.OAI.PolycyclicRecognition.nilshadowWeightDerivation_symm _root_.OAI.PolycyclicRecognition.nilshadowWeightOperator_symm _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual profile paths for the successful coupled source bundles -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule Set Filter
open scoped Manifold Topology NNReal

variable {EG G W I : Type} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G] [IsIsometricSMul G G]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [Fintype I] [DecidableEq I]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H) [Nonempty (Fin M.letterCount)]
  {Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H Exp)
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)

set_option maxHeartbeats 1000000 in
theorem exists_successful_bundle_profile_paths
    (hExp : IsGroupExponential Exp)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (haarD : NilpotentExponentialHaarInput F.D.modelSpace F.D.carrier)
    (dynkinD : NilpotentDynkinExpansionInput F.D.modelSpace F.D.carrier)
    (π : G →* Multiplicative W)
    (hπ : ∀ x, (π (Exp x)).toAdd = eW (heightProjection T.character x))
    (X : I → H) {d : ℕ} (hDnil : lowerCentralSeries ℝ H H d = ⊥)
    (bD₀ : Basis (Fin (finrank ℝ H)) ℝ H)
    (βD : WordBasisSelections X (boundedBracketWords d))
    (hβD : IsMaximizingColumnBasis (wordListCoordinates X (boundedBracketWords d) bD₀)
      (fun w => bracketWordExponent (fun _ : I => 1) w) βD.val)
    (scale : ℕ → ℝ) (hscale : Tendsto scale atTop atTop) (hscale0 : ∀ n, 0 < scale n)
    (pivot : H) (v : Fin M.letterCount → H)
    (E V : Set W) (hE : Convex ℝ E) (hpivot : eW (heightProjection T.character pivot) ∈ E)
    (hV : IsOpen V) (hVconv : Convex ℝ V) (hEV : E ⊆ V)
    (hv : ∀ i, eW (heightProjection T.character (pivot + v i : H)) ∈ E)
    (s : Fin M.letterCount → ℝ)
    (hs : ∀ i, cartanHeightWeight T H (M.weight i)
      (eW.symm (eW (heightProjection T.character (pivot + v i : H)))) = s i)
    {m h : ℕ} (letters : Fin m → Fin M.letterCount) (ρ : ℝ) (hρ : 0 ≤ ρ) :
    let b := WordBasisSelections.basis X (boundedBracketWords d) βD
    let cost := fun j => bracketWordExponent (fun _ : I => 1) (βD.val j)
    let br := fun n => exponentialRescaleBasis b cost (Real.log (scale n))
    let height : H →ₗ[ℝ] W := eW.toLinearMap.comp
      ((heightProjection T.character).comp H.incl.toLinearMap)
    ∃ (Q : Set (Fin (finrank ℝ H) → ℝ)) (C : ℝ),
      IsCompact Q ∧ Q ⊆ {z | height (b.equivFun.symm z) ∈ V} ∧ 0 ≤ C ∧
      (∀ᶠ n in atTop, (br n).equivFun (scale n • pivot) ∈ Q) ∧
      ∀ᶠ n in atTop, ∀ (Good : Set F.N.carrier) (x : G) (initial : F.N.carrier)
        (k : Fin h → F.N.carrier) (t : Fin (h * m + h * m) → ℝ),
        let allLetters := fun j : Fin (h * m) => letters (finProdFinEquiv.symm j).2
        let sample := coupledRootIntervalSample (F.ExpN ∘ F.N.equiv)
          allLetters M.letter s (scale n) (bundleConjugator m k)
        let φ := fun i => MulAut.conj (k i)
        let products := sourceBundleProduct F.N.equiv F.ExpN M.letter s letters
          (bundleParameterChart h m) (scale n) t
        let boundary := sourceBundleBoundary initial φ products
        initial ∈ Good → ‖t‖ ≤ ρ →
        SwitchSuccessful (fun _ => Good) 0 (h * m) initial
          (sampledSwitchParameters sample (h * m) t) →
        ∀ (i : Fin h) (J : G → W) (K : ℝ≥0), LipschitzWith K J →
        ∀ (A : W →ₗ[ℝ] W) (offset : W) (ε : ℝ),
        (∀ q ∈ Good, ∀ z ∈ Q, height (b.equivFun.symm z) ∈ E →
          ‖rescaledMapProfile J x (F.inclusionN (q * k i)) (Real.log (scale n))
              (fun z => Exp ((br n).equivFun.symm z)) z -
            (A (height (b.equivFun.symm z)) + offset)‖ ≤ ε) →
        ∃ path : Path
            (x * F.inclusionN (boundary i.val * k i) *
              Exp (scale n • (pivot : GroupLieAlgebra (𝓘(ℝ, EG)) G)))
            (x * F.inclusionN (boundary (i.val + 1) * k i) *
              Exp (scale n • (pivot : GroupLieAlgebra (𝓘(ℝ, EG)) G))),
          PathMetricBound path ((C * scale n) * 2 ^ m)
            ((C * (1 + Real.log (2 + scale n))) * 2 ^ m) ∧
          ‖J (x * F.inclusionN (boundary (i.val + 1) * k i) *
              Exp (scale n • (pivot : GroupLieAlgebra (𝓘(ℝ, EG)) G))) -
            J (x * F.inclusionN (boundary i.val * k i) *
              Exp (scale n • (pivot : GroupLieAlgebra (𝓘(ℝ, EG)) G)))‖ ≤
            2 * scale n * ε ∧
          ∀ u, ∃ w ∈ E,
            ‖J (path u) - J (x * F.inclusionN (boundary i.val * k i) *
                Exp (scale n • (pivot : GroupLieAlgebra (𝓘(ℝ, EG)) G))) -
              scale n • A (w - height pivot)‖ ≤
                2 * scale n * ε + K * (C * Real.log (2 + scale n)) := by
  classical
  dsimp only
  obtain ⟨Q, C, hQ, hQV, hC, hpivotQ, hp⟩ := M.exists_good_conjugated_word_paths
    T F eW hExp realize haarD dynkinD π hπ X hDnil bD₀ βD hβD scale hscale hscale0
    pivot v E V hE hpivot hV hVconv hEV hv s hs (B := 2 * ρ) (by positivity)
  refine ⟨Q, C, hQ, hQV, hC, hpivotQ, ?_⟩
  filter_upwards [hp, hpivotQ] with n hn hnQ
  intro Good x initial k t hi ht hsuccess i J K hJ A offset ε hgood
  let allLetters := fun j : Fin (h * m) => letters (finProdFinEquiv.symm j).2
  let sample := coupledRootIntervalSample (F.ExpN ∘ F.N.equiv)
    allLetters M.letter s (scale n) (bundleConjugator m k)
  let φ := fun i => MulAut.conj (k i)
  let products := sourceBundleProduct F.N.equiv F.ExpN M.letter s letters
    (bundleParameterChart h m) (scale n) t
  let boundary := sourceBundleBoundary initial φ products
  let diff := fun j : Fin m => t (Fin.castAdd (h * m) (finProdFinEquiv (i, j))) -
    t (Fin.natAdd (h * m) (finProdFinEquiv (i, j)))
  let coeff := fun j => diff j * Real.exp (scale n * s (letters j))
  let word := fun j => k i * F.ExpN (F.N.equiv (coeff j • M.letter (letters j))) * (k i)⁻¹
  have hsample (i : Fin h) (j : Fin m) (u : ℝ) :
      sample (finProdFinEquiv (i, j)).val u = φ i
        (F.ExpN (F.N.equiv (u • (Real.exp (scale n * s (letters j)) • M.letter (letters j))))) :=
    coupledRootIntervalSample_bundle (F.ExpN ∘ F.N.equiv) letters M.letter s (scale n) k i j u
  have hsub (j : ℕ) (u v : ℝ) : sample j u * (sample j v)⁻¹ = sample j (u - v) := by
    apply coupledRootIntervalSample_sub
    · intro w
      simp only [Function.comp_apply, map_neg, F.isExpN.map_neg]
    · intro w u v
      simpa only [Function.comp_apply, map_smul] using F.isExpN.map_add_smul (F.N.equiv w) u v
  have hg : WordSheetsGood Good (boundary i.val) (List.ofFn word) := by
    have hg := successful_sourceBundle_word_good F.N.equiv F.ExpN M.letter s letters
      (scale n) φ sample hsub hsample Good initial hi t hsuccess i
    simpa only [word, coeff, diff, smul_smul, φ, MulAut.conj_apply] using hg
  have hcoeff (j : Fin m) : |coeff j| ≤ 2 * ρ * Real.exp (scale n * s (letters j)) := by
    have h₁ := (norm_le_pi_norm t (Fin.castAdd (h * m) (finProdFinEquiv (i, j)))).trans ht
    have h₂ := (norm_le_pi_norm t (Fin.natAdd (h * m) (finProdFinEquiv (i, j)))).trans ht
    rw [Real.norm_eq_abs] at h₁ h₂
    have hd : |diff j| ≤ 2 * ρ := by
      exact (abs_sub _ _).trans (by linarith)
    dsimp only [coeff]
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul_of_nonneg_right hd (Real.exp_pos _).le
  obtain ⟨path, hmetric, hrange⟩ := hn m letters coeff hcoeff Good x (k i) (boundary i.val)
    hg J K hJ A offset ε hgood
  have hword : sampledBlockWord sample t i = List.ofFn word := by
    simp only [sampledBlockWord, hsample, word, coeff, diff, smul_smul, φ, MulAut.conj_apply]
  have hblock := sampledBlockWord_source_product F.N.equiv F.ExpN M.letter s letters
    (scale n) φ sample hsample t i
  have hnext : boundary (i.val + 1) = boundary i.val * (List.ofFn word).prod := by
    dsimp only [boundary, sourceBundleBoundary, products]
    rw [wordPrefix_succ, dite_eq_left i.isLt, ← hblock, hword]
    simp only [mul_assoc]
  have hend : x * F.inclusionN (boundary (i.val + 1) * k i) *
      Exp (scale n • (pivot : GroupLieAlgebra (𝓘(ℝ, EG)) G)) =
        x * F.inclusionN (boundary i.val * (List.ofFn word).prod * k i) *
          Exp (scale n • (pivot : GroupLieAlgebra (𝓘(ℝ, EG)) G)) := by rw [hnext]
  have hfinish : boundary (i.val + 1) ∈ Good := by
    rw [hnext]
    simpa only [List.take_of_length_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top : (List.ofFn word).length ≤ m)] using
      hg.take_prod_mem m
  let b := WordBasisSelections.basis X (boundedBracketWords d) βD
  let cost := fun j => bracketWordExponent (fun _ : I => 1) (βD.val j)
  let br := exponentialRescaleBasis b cost (Real.log (scale n))
  let z₀ := br.equivFun (scale n • pivot)
  have hz₀ : z₀ ∈ Q := hnQ
  let height : H →ₗ[ℝ] W := eW.toLinearMap.comp
    ((heightProjection T.character).comp H.incl.toLinearMap)
  have hkill (u w : H) : height ⁅u, w⁆ = 0 := by
    change eW (heightProjection T.character ⁅(u : GroupLieAlgebra (𝓘(ℝ, EG)) G), w⁆) = 0
    rw [T.height_lie, map_zero]
  have hz₀E : height (b.equivFun.symm z₀) ∈ E := by
    rw [word_length_chart_pivot_height X (boundedBracketWords d) βD height hkill (hscale0 n)]
    exact hpivot
  have hφ₀ : Exp ((br.equivFun.symm z₀ : H) : GroupLieAlgebra (𝓘(ℝ, EG)) G) =
      Exp (scale n • (pivot : GroupLieAlgebra (𝓘(ℝ, EG)) G)) := by
    simp only [z₀, LinearEquiv.symm_apply_apply, SetLike.val_smul]
  have hendpoint := common_profile_endpoint_height J x
    (F.inclusionN (boundary i.val * k i)) (F.inclusionN (boundary (i.val + 1) * k i))
    (Exp (scale n • (pivot : GroupLieAlgebra (𝓘(ℝ, EG)) G)))
    (Real.log (scale n))
    (fun z => Exp ((br.equivFun.symm z : H) : GroupLieAlgebra (𝓘(ℝ, EG)) G)) z₀
    _ hφ₀ (hgood _ hg.start z₀ hz₀ hz₀E) (hgood _ hfinish z₀ hz₀ hz₀E)
  rw [Real.exp_log (hscale0 n)] at hendpoint
  refine ⟨path.cast rfl hend, hmetric, hendpoint, ?_⟩
  intro u
  exact hrange u

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanCommonBundlePaths
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instDecidableEqConeMixedWords _root_.OAI.PolycyclicRecognition.CartanWordModel.instFintypeConeMixedWords _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.CartanFactorModel.heightRay_zero _root_.OAI.PolycyclicRecognition.CartanFactorModel.realScaleProfile_apply _root_.OAI.PolycyclicRecognition.CartanFactorModel.sampledProbeProfile_apply _root_.OAI.PolycyclicRecognition.bracketWordDifferential_mul _root_.OAI.PolycyclicRecognition.cartanWeightDerivation_apply_root _root_.OAI.PolycyclicRecognition.chartExponentialFlow_zero _root_.OAI.PolycyclicRecognition.derivationSemidirectHom_apply _root_.OAI.PolycyclicRecognition.exponentialHomOfDynkin_apply_exp _root_.OAI.PolycyclicRecognition.exponentialRescaleBasis_zero _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.modelNilradicalLinearAction_apply _root_.OAI.PolycyclicRecognition.modelNilradicalRotation_apply _root_.OAI.PolycyclicRecognition.modelNilradicalRotation_mul _root_.OAI.PolycyclicRecognition.modelNilradicalRotation_one _root_.OAI.PolycyclicRecognition.nilshadowWeightDerivation_symm _root_.OAI.PolycyclicRecognition.nilshadowWeightOperator_symm _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Common-pivot paths for the actual successful source bundles

The chart is selected before the good sets. Both endpoint bridges use the
same root displacement, and their error tends to zero with that displacement.
-/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule Set Filter
open scoped Manifold Topology NNReal

variable {EG G W I : Type} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G] [IsIsometricSMul G G]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [Fintype I] [DecidableEq I]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H) [Nonempty (Fin M.letterCount)]
  {Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H Exp)
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)

set_option maxHeartbeats 1000000 in
theorem exists_common_bundle_profile_paths
    (hExp : IsGroupExponential Exp)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (haarD : NilpotentExponentialHaarInput F.D.modelSpace F.D.carrier)
    (dynkinD : NilpotentDynkinExpansionInput F.D.modelSpace F.D.carrier)
    (π : G →* Multiplicative W)
    (hπ : ∀ x, (π (Exp x)).toAdd = eW (heightProjection T.character x))
    (X : I → H) {d : ℕ} (hDnil : lowerCentralSeries ℝ H H d = ⊥)
    (bD₀ : Basis (Fin (finrank ℝ H)) ℝ H)
    (βD : WordBasisSelections X (boundedBracketWords d))
    (hβD : IsMaximizingColumnBasis (wordListCoordinates X (boundedBracketWords d) bD₀)
      (fun w => bracketWordExponent (fun _ : I => 1) w) βD.val)
    (scale : ℕ → ℝ) (hscale : Tendsto scale atTop atTop) (hscale0 : ∀ n, 0 < scale n)
    (pivot : H) (v : Fin M.letterCount → H)
    (E V : Set W) (hE : Convex ℝ E) (hpivot : eW (heightProjection T.character pivot) ∈ E)
    (hV : IsOpen V) (hVconv : Convex ℝ V) (hEV : E ⊆ V)
    (hv : ∀ i, eW (heightProjection T.character (pivot + v i : H)) ∈ E)
    (s : Fin M.letterCount → ℝ)
    (hs : ∀ i, cartanHeightWeight T H (M.weight i)
      (eW.symm (eW (heightProjection T.character (pivot + v i : H)))) = s i)
    {m h : ℕ} (letters : Fin m → Fin M.letterCount) (ρ : ℝ) (hρ : 0 ≤ ρ) :
    let b := WordBasisSelections.basis X (boundedBracketWords d) βD
    let cost := fun j => bracketWordExponent (fun _ : I => 1) (βD.val j)
    let br := fun n => exponentialRescaleBasis b cost (Real.log (scale n))
    let height : H →ₗ[ℝ] W := eW.toLinearMap.comp
      ((heightProjection T.character).comp H.incl.toLinearMap)
    ∃ (Q : Set (Fin (finrank ℝ H) → ℝ)) (C : ℝ),
      IsCompact Q ∧ Q ⊆ {z | height (b.equivFun.symm z) ∈ V} ∧ 0 ≤ C ∧
      ∀ (J : ℕ → G → W) (K : ℝ≥0), (∀ n, LipschitzWith K (J n)) →
      ∀ (Good : ℕ → Set F.N.carrier) (x : ℕ → G)
        (k : ℕ → Fin h → F.N.carrier) (A : Fin h → W →ₗ[ℝ] W)
        (offset : Fin h → W) (ε δ : ℕ → ℝ),
      (∀ n, 0 ≤ ε n) → Tendsto ε atTop (𝓝 0) →
      (∀ n, 0 ≤ δ n) → Tendsto δ atTop (𝓝 0) →
      (∀ᶠ n in atTop, ∀ i : Fin h,
        dist (Exp (scale n • (pivot : GroupLieAlgebra (𝓘(ℝ, EG)) G)))
          (F.inclusionN (k n i) *
            Exp (scale n • (pivot : GroupLieAlgebra (𝓘(ℝ, EG)) G))) ≤ δ n * scale n) →
      (∀ᶠ n in atTop, ∀ i (q : F.N.carrier), q ∈ Good n → ∀ z ∈ Q, height (b.equivFun.symm z) ∈ E →
        ‖rescaledMapProfile (J n) (x n) (F.inclusionN (q * k n i))
            (Real.log (scale n)) (fun z => Exp ((br n).equivFun.symm z)) z -
          (A i (height (b.equivFun.symm z)) + offset i)‖ ≤ ε n) →
      (hpath : ∀ g : G, ∃ γ : ℝ → G, γ 0 = 1 ∧ γ 1 = g ∧
        ∀ t ∈ Icc (0 : ℝ) 1, ∀ u ∈ Icc (0 : ℝ) 1,
          dist (γ t) (γ u) ≤ dist 1 g * |t - u|) →
      ∃ (D : ℝ) (η : ℕ → ℝ), 0 ≤ D ∧
        (∀ n, 0 ≤ η n) ∧ Tendsto η atTop (𝓝 0) ∧
        ∀ᶠ n in atTop, ∀ (initial : F.N.carrier)
          (t : Fin (h * m + h * m) → ℝ),
          let allLetters := fun j : Fin (h * m) => letters (finProdFinEquiv.symm j).2
          let sample := coupledRootIntervalSample (F.ExpN ∘ F.N.equiv)
            allLetters M.letter s (scale n) (bundleConjugator m (k n))
          let products := sourceBundleProduct F.N.equiv F.ExpN M.letter s letters
            (bundleParameterChart h m) (scale n) t
          let boundary := sourceBundleBoundary initial (fun i => MulAut.conj (k n i)) products
          initial ∈ Good n → ‖t‖ ≤ ρ →
          SwitchSuccessful (fun _ => Good n) 0 (h * m) initial
            (sampledSwitchParameters sample (h * m) t) →
          ∀ i : Fin h, ∃ path : Path
              (x n * F.inclusionN (boundary i.val) *
                Exp (scale n • (pivot : GroupLieAlgebra (𝓘(ℝ, EG)) G)))
              (x n * F.inclusionN (boundary (i.val + 1)) *
                Exp (scale n • (pivot : GroupLieAlgebra (𝓘(ℝ, EG)) G))),
            PathMetricBound path (D * scale n) (D * (1 + Real.log (2 + scale n))) ∧
            (∀ u, ∃ w ∈ (fun z => A i (z - height pivot)) '' E,
              ‖J n (path u) - J n (x n * F.inclusionN (boundary i.val) *
                Exp (scale n • (pivot : GroupLieAlgebra (𝓘(ℝ, EG)) G))) -
                scale n • w‖ ≤
                  2 * scale n * η n + D * (1 + Real.log (2 + scale n))) ∧
            ‖J n (x n * F.inclusionN (boundary (i.val + 1)) *
                Exp (scale n • (pivot : GroupLieAlgebra (𝓘(ℝ, EG)) G))) -
              J n (x n * F.inclusionN (boundary i.val) *
                Exp (scale n • (pivot : GroupLieAlgebra (𝓘(ℝ, EG)) G)))‖ ≤ η n * scale n := by
  classical
  let : IsTopologicalGroup G := topologicalGroup_of_lieGroup (𝓘(ℝ, EG)) ⊤
  dsimp only
  obtain ⟨Q, C, hQ, hQV, hC, _, hp⟩ := M.exists_successful_bundle_profile_paths
    T F eW hExp realize haarD dynkinD π hπ X hDnil bD₀ βD hβD scale hscale hscale0
    pivot v E V hE hpivot hV hVconv hEV hv s hs letters ρ hρ
  refine ⟨Q, C, hQ, hQV, hC, ?_⟩
  intro J K hJ Good x k A offset ε δ hε0 hε hδ0 hδ hbridge hgood hpath
  let C' : ℝ := max (C * 2 ^ m) (K * C)
  have hC' : 0 ≤ C' := (mul_nonneg hC (by positivity)).trans (le_max_left _ _)
  let η := fun n => 2 * ε n + 2 * K * δ n
  refine ⟨4 * (C' + 1), η, by positivity, fun n =>
    add_nonneg (mul_nonneg (by norm_num) (hε0 n))
      (mul_nonneg (by positivity) (hδ0 n)), ?_, ?_⟩
  · have he : Tendsto (fun n => 2 * ε n) atTop (𝓝 (2 * 0)) := tendsto_const_nhds.mul hε
    have hd : Tendsto (fun n => 2 * (K : ℝ) * δ n) atTop (𝓝 (2 * K * 0)) :=
      tendsto_const_nhds.mul hδ
    simpa only [mul_zero, add_zero] using he.add hd
  have hscale1 := hscale.eventually (eventually_ge_atTop 1)
  have hδ1 : ∀ᶠ n in atTop, δ n ≤ 1 := hδ.eventually (eventually_le_nhds (by norm_num))
  filter_upwards [hp, hbridge, hgood, hscale1, hδ1] with n hn hb hg hr hd
  intro initial t hi ht hsuccess i
  obtain ⟨path, hm, hend, himage⟩ := hn (Good n) (x n) initial (k n) t hi ht hsuccess
    i (J n) K (hJ n) (A i) (offset i) (ε n) (hg i)
  let pivotG := Exp (scale n • (pivot : GroupLieAlgebra (𝓘(ℝ, EG)) G))
  let products := sourceBundleProduct F.N.equiv F.ExpN M.letter s letters
    (bundleParameterChart h m) (scale n) t
  let boundary := sourceBundleBoundary initial (fun i => MulAut.conj (k n i)) products
  have hlog : 0 ≤ 1 + Real.log (2 + scale n) := by
    have := Real.log_nonneg (show 1 ≤ 2 + scale n by linarith)
    linarith
  have hm' : PathMetricBound path (C' * scale n) (C' * (1 + Real.log (2 + scale n))) := by
    apply hm.mono
    · calc (C * scale n) * 2 ^ m = (C * 2 ^ m) * scale n := by ring
           _ ≤ C' * scale n := mul_le_mul_of_nonneg_right (le_max_left _ _) (by linarith)
    · calc (C * (1 + Real.log (2 + scale n))) * 2 ^ m =
              (C * 2 ^ m) * (1 + Real.log (2 + scale n)) := by ring
           _ ≤ C' * (1 + Real.log (2 + scale n)) :=
             mul_le_mul_of_nonneg_right (le_max_left _ _) hlog
  have hdist (q : F.N.carrier) :
      dist (x n * F.inclusionN q * pivotG)
        (x n * F.inclusionN (q * k n i) * pivotG) ≤ δ n * scale n := by
    simpa only [map_mul, mul_assoc, dist_mul_left] using hb i
  have himage' : ∀ u, ∃ w ∈ (fun z => A i (z -
      eW (heightProjection T.character pivot))) '' E,
      ‖J n (path u) - J n (x n * F.inclusionN (boundary i.val * k n i) * pivotG) -
        scale n • w‖ ≤ 2 * scale n * ε n + C' * (1 + Real.log (2 + scale n)) := by
    intro u
    obtain ⟨w, hw, he⟩ := himage u
    refine ⟨A i (w - eW (heightProjection T.character pivot)), ⟨w, hw, rfl⟩, he.trans ?_⟩
    have hlog0 : 0 ≤ Real.log (2 + scale n) := Real.log_nonneg (by linarith)
    calc 2 * scale n * ε n + K * (C * Real.log (2 + scale n)) =
          2 * scale n * ε n + (K * C) * Real.log (2 + scale n) := by ring
         _ ≤ 2 * scale n * ε n + C' * (1 + Real.log (2 + scale n)) := by
           gcongr
           · exact le_max_right _ _
           · linarith
  have hzero : (0 : W) ∈ (fun z => A i (z - eW (heightProjection T.character pivot))) '' E :=
    ⟨eW (heightProjection T.character pivot), hpivot, by simp only [sub_self, map_zero]⟩
  exact exists_bridged_profile_bounds (exists_short_path_of_minimizing_paths hpath) path
    hC' hr (hδ0 n) hd (hε0 n) hm' (hdist (boundary i.val))
    (by rw [dist_comm]; exact hdist (boundary (i.val + 1)))
    (J n) (hJ n) _ hzero himage' hend

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanSourceProfile
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.CartanFactorModel.heightRay_zero _root_.OAI.PolycyclicRecognition.CartanFactorModel.realScaleProfile_apply _root_.OAI.PolycyclicRecognition.CartanFactorModel.sampledProbeProfile_apply _root_.OAI.PolycyclicRecognition.bracketWordDifferential_mul _root_.OAI.PolycyclicRecognition.cartanWeightDerivation_apply_root _root_.OAI.PolycyclicRecognition.exponentialRescaleBasis_zero _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.modelNilradicalLinearAction_apply _root_.OAI.PolycyclicRecognition.modelNilradicalRotation_apply _root_.OAI.PolycyclicRecognition.modelNilradicalRotation_mul _root_.OAI.PolycyclicRecognition.modelNilradicalRotation_one _root_.OAI.PolycyclicRecognition.nilshadowWeightDerivation_symm _root_.OAI.PolycyclicRecognition.nilshadowWeightOperator_symm _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The source height has the exact identity profile on every nilpotent sheet -/

noncomputable section
namespace PolycyclicRecognition

open Module
open scoped Manifold

set_option maxHeartbeats 1000000 in
theorem rescaled_height_profile_eq
    {G W Z : Type} [Group G] [PseudoMetricSpace G]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (π : G →* Multiplicative W) (x k : G) (r : ℝ) (hk : π k = 1)
    (φ : Z → G) (q : Z → W) (hφ : ∀ z, (π (φ z)).toAdd = Real.exp r • q z) (z : Z) :
    rescaledMapProfile (fun g => (π g).toAdd) x k r φ z = q z := by
  simp only [rescaledMapProfile, map_mul, hk, mul_one, toAdd_mul, hφ,
    add_sub_cancel_left, smul_smul, inv_mul_cancel₀ (Real.exp_ne_zero r), one_smul]

namespace CartanFactorModel

variable {EG G W I : Type} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [Fintype I] [DecidableEq I]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  {Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H Exp)
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)

set_option maxHeartbeats 1000000 in
theorem source_height_profile_eq
    (π : G →* Multiplicative W)
    (hπ : ∀ y, (π (Exp y)).toAdd = eW (heightProjection T.character y))
    (hbijN : Function.Bijective F.ExpN)
    (X : I → H) (S : Finset (FreeMagma I)) (β : WordBasisSelections X S)
    {r : ℝ} (hr : 0 < r) (x : G) (n : F.N.carrier)
    (z : Fin (finrank ℝ H) → ℝ) :
    let b := WordBasisSelections.basis X S β
    let cost := fun j => bracketWordExponent (fun _ : I => 1) (β.val j)
    let br := exponentialRescaleBasis b cost (Real.log r)
    let height : H →ₗ[ℝ] W := eW.toLinearMap.comp
      ((heightProjection T.character).comp H.incl.toLinearMap)
    rescaledMapProfile (fun g => (π g).toAdd) x (F.inclusionN n) (Real.log r)
      (fun w => Exp ((br.equivFun.symm w : H) : GroupLieAlgebra (𝓘(ℝ, EG)) G)) z =
      height (b.equivFun.symm z) := by
  dsimp only
  let height : H →ₗ[ℝ] W := eW.toLinearMap.comp
    ((heightProjection T.character).comp H.incl.toLinearMap)
  have hkill (y w : H) : height ⁅y, w⁆ = 0 := by
    change eW (heightProjection T.character ⁅(y : GroupLieAlgebra (𝓘(ℝ, EG)) G), w⁆) = 0
    rw [T.height_lie, map_zero]
  apply rescaled_height_profile_eq π x (F.inclusionN n) (Real.log r)
    (F.inclusionN_height_eq_one T eW π hπ hbijN n)
  intro w
  rw [hπ, Real.exp_log hr]
  simpa [bracketWordExponent_one, height] using word_length_chart_height X S β height hkill hr w

end CartanFactorModel
end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanSourceBundleTerminals
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instDecidableEqConeMixedWords _root_.OAI.PolycyclicRecognition.CartanWordModel.instFintypeConeMixedWords _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.CartanFactorModel.heightRay_zero _root_.OAI.PolycyclicRecognition.CartanFactorModel.realScaleProfile_apply _root_.OAI.PolycyclicRecognition.CartanFactorModel.sampledProbeProfile_apply _root_.OAI.PolycyclicRecognition.bracketWordDifferential_mul _root_.OAI.PolycyclicRecognition.cartanWeightDerivation_apply_root _root_.OAI.PolycyclicRecognition.chartExponentialFlow_zero _root_.OAI.PolycyclicRecognition.derivationSemidirectHom_apply _root_.OAI.PolycyclicRecognition.exponentialHomOfDynkin_apply_exp _root_.OAI.PolycyclicRecognition.exponentialRescaleBasis_zero _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.modelNilradicalLinearAction_apply _root_.OAI.PolycyclicRecognition.modelNilradicalRotation_apply _root_.OAI.PolycyclicRecognition.modelNilradicalRotation_mul _root_.OAI.PolycyclicRecognition.modelNilradicalRotation_one _root_.OAI.PolycyclicRecognition.nilshadowWeightDerivation_symm _root_.OAI.PolycyclicRecognition.nilshadowWeightOperator_symm _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Source terminal paths from the actual successful coupled states

The source identity profile removes every source good-profile hypothesis.
Only successful recurrence parameters and the proved pivot bridge rate remain.
-/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule Set Filter
open scoped Manifold Topology NNReal

variable {EG G W I : Type} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G] [IsIsometricSMul G G]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [Fintype I] [DecidableEq I]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H) [Nonempty (Fin M.letterCount)]
  {Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H Exp)
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)

set_option maxHeartbeats 1000000 in
theorem exists_source_bundle_terminal_bounds
    (hExp : IsGroupExponential Exp)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (haarD : NilpotentExponentialHaarInput F.D.modelSpace F.D.carrier)
    (dynkinD : NilpotentDynkinExpansionInput F.D.modelSpace F.D.carrier)
    (π : G →* Multiplicative W)
    (hπ : ∀ x, (π (Exp x)).toAdd = eW (heightProjection T.character x))
    (X : I → H) {d : ℕ} (hDnil : lowerCentralSeries ℝ H H d = ⊥)
    (bD₀ : Basis (Fin (finrank ℝ H)) ℝ H)
    (βD : WordBasisSelections X (boundedBracketWords d))
    (hβD : IsMaximizingColumnBasis (wordListCoordinates X (boundedBracketWords d) bD₀)
      (fun w => bracketWordExponent (fun _ : I => 1) w) βD.val)
    (scale : ℕ → ℝ) (hscale : Tendsto scale atTop atTop) (hscale0 : ∀ n, 0 < scale n)
    (pivot : H) (v : Fin M.letterCount → H)
    (E V : Set W) (hE : Convex ℝ E) (hpivot : eW (heightProjection T.character pivot) ∈ E)
    (hV : IsOpen V) (hVconv : Convex ℝ V) (hEV : E ⊆ V)
    (hv : ∀ i, eW (heightProjection T.character (pivot + v i : H)) ∈ E)
    (s : Fin M.letterCount → ℝ)
    (hs : ∀ i, cartanHeightWeight T H (M.weight i)
      (eW.symm (eW (heightProjection T.character (pivot + v i : H)))) = s i)
    {m h : ℕ} (letters : Fin m → Fin M.letterCount) (ρ : ℝ) (hρ : 0 ≤ ρ)

    (hh : 0 < h) (hbijN : Function.Bijective F.ExpN)
    {Kπ : ℝ≥0} (hLip : LipschitzWith Kπ (fun g => (π g).toAdd))
    (hpath : ∀ g : G, ∃ γ : ℝ → G, γ 0 = 1 ∧ γ 1 = g ∧
      ∀ t ∈ Icc (0 : ℝ) 1, ∀ u ∈ Icc (0 : ℝ) 1,
        dist (γ t) (γ u) ≤ dist 1 g * |t - u|)
    (Good : ℕ → Set F.N.carrier) (x : ℕ → G) (k : ℕ → Fin h → F.N.carrier)
    (initial : ℕ → F.N.carrier) (hinitial : ∀ n, initial n ∈ Good n)
    (S : ℕ → Set (Fin h → F.N.carrier))
    (δ : ℕ → ℝ) (hδ0 : ∀ n, 0 ≤ δ n) (hδ : Tendsto δ atTop (𝓝 0))
    (hbridge : ∀ᶠ n in atTop, ∀ i : Fin h,
      dist (Exp (scale n • (pivot : GroupLieAlgebra (𝓘(ℝ, EG)) G)))
        (F.inclusionN (k n i) * Exp (scale n • (pivot : GroupLieAlgebra (𝓘(ℝ, EG)) G))) ≤
          δ n * scale n)
    (hreach : ∀ᶠ n in atTop, ∀ v ∈ S n,
      ∃ t : Fin (h * m + h * m) → ℝ, ‖t‖ ≤ ρ ∧
        SwitchSuccessful (fun _ => Good n) 0 (h * m) (initial n)
          (sampledSwitchParameters
            (coupledRootIntervalSample (F.ExpN ∘ F.N.equiv)
              (fun j : Fin (h * m) => letters (finProdFinEquiv.symm j).2)
              M.letter s (scale n) (bundleConjugator m (k n))) (h * m) t) ∧
        ∀ i : Fin h, v i = sourceBundleBoundary (initial n)
          (fun i => MulAut.conj (k n i))
          (sourceBundleProduct F.N.equiv F.ExpN M.letter s letters
            (bundleParameterChart h m) (scale n) t) (i.val + 1)) :
    let height : H →ₗ[ℝ] W := eW.toLinearMap.comp
      ((heightProjection T.character).comp H.incl.toLinearMap)
    let E₀ := (fun w => w - height pivot) '' E
    let pivotG := fun n => Exp (scale n • (pivot : GroupLieAlgebra (𝓘(ℝ, EG)) G))
    let origin := fun n => x n * F.inclusionN (initial n) * pivotG n
    let last : Fin h := ⟨h - 1, by omega⟩
    let terminals := fun n => relativeTupleTerminals F.inclusionN
      (origin n) (x n) (pivotG n) last (S n)
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ z ∈ terminals n,
      ∃ path : Path (1 : G) z,
        PathMetricBound path (C * scale n) (C * (1 + Real.log (2 + scale n))) ∧
        ∀ u, ∃ w ∈ E₀, ‖(π (path u)).toAdd - scale n • w‖ ≤
          ε * scale n + C * (1 + Real.log (2 + scale n)) := by
  classical
  let : IsTopologicalGroup G := topologicalGroup_of_lieGroup (𝓘(ℝ, EG)) ⊤
  dsimp only
  obtain ⟨Q, C, _, _, _, hc⟩ := M.exists_common_bundle_profile_paths
    T F eW hExp realize haarD dynkinD π hπ X hDnil bD₀ βD hβD scale hscale hscale0
    pivot v E V hE hpivot hV hVconv hEV hv s hs letters ρ hρ
  have hgood : ∀ᶠ n in atTop, ∀ i (q : F.N.carrier), q ∈ Good n → ∀ z ∈ Q,
      (eW.toLinearMap.comp ((heightProjection T.character).comp H.incl.toLinearMap))
        ((WordBasisSelections.basis X (boundedBracketWords d) βD).equivFun.symm z) ∈ E →
      ‖rescaledMapProfile (fun g => (π g).toAdd) (x n) (F.inclusionN (q * k n i))
          (Real.log (scale n))
          (fun z => Exp (((exponentialRescaleBasis
            (WordBasisSelections.basis X (boundedBracketWords d) βD)
            (fun j => bracketWordExponent (fun _ : I => 1) (βD.val j))
            (Real.log (scale n))).equivFun.symm z : H) : GroupLieAlgebra (𝓘(ℝ, EG)) G)) z -
        ((LinearMap.id : W →ₗ[ℝ] W)
          ((eW.toLinearMap.comp ((heightProjection T.character).comp H.incl.toLinearMap))
            ((WordBasisSelections.basis X (boundedBracketWords d) βD).equivFun.symm z)) + 0)‖ ≤ 0 := by
    filter_upwards [] with n i q _ z _ _
    rw [F.source_height_profile_eq T eW π hπ hbijN X (boundedBracketWords d) βD
      (hscale0 n) (x n) (q * k n i) z]
    simp only [LinearMap.id_coe, id_eq, add_zero, sub_self, norm_zero, le_refl]
  obtain ⟨D, η, hD, hη0, hη, hp⟩ := hc (fun _ g => (π g).toAdd) Kπ (fun _ => hLip)
    Good x k (fun _ => LinearMap.id) (fun _ => 0) (fun _ => 0) δ
    (fun _ => le_rfl) tendsto_const_nhds hδ0 hδ hbridge hgood hpath
  let D' := D * 2 ^ h
  have hD' : 0 ≤ D' := mul_nonneg hD (by positivity)
  have hDD : D ≤ D' := le_mul_of_one_le_right hD (by exact_mod_cast Nat.one_le_two_pow)
  refine ⟨D', hD', ?_⟩
  intro ε hε
  have hηsmall : ∀ᶠ n in atTop, 2 * η n ≤ ε :=
    (tendsto_const_nhds.mul hη).eventually (eventually_le_nhds (by simpa using hε))
  filter_upwards [hp, hreach, hηsmall] with n hn hr he
  rintro z ⟨w, hw, rfl⟩
  obtain ⟨t, ht, hsuccess, heq⟩ := hr w hw
  have paths := hn (initial n) t (hinitial n) ht hsuccess
  choose path hmetric hheight _ using paths
  let height : H →ₗ[ℝ] W := eW.toLinearMap.comp
    ((heightProjection T.character).comp H.incl.toLinearMap)
  have hE₀ : (0 : W) ∈ (fun w => w - height pivot) '' E :=
    ⟨height pivot, hpivot, sub_self _⟩
  have hlog : 0 ≤ 1 + Real.log (2 + scale n) := by
    have := Real.log_nonneg (show 1 ≤ 2 + scale n by linarith [hscale0 n])
    linarith
  obtain ⟨γ, hγ, hγheight⟩ := exists_source_bundle_terminal_path F.inclusionN π
    (F.inclusionN_height_eq_one T eW π hπ hbijN) (initial n)
    (fun i => MulAut.conj (k n i)) _ (x n)
    (Exp (scale n • (pivot : GroupLieAlgebra (𝓘(ℝ, EG)) G))) _ hE₀
    (scale n) (D * scale n) (D * (1 + Real.log (2 + scale n)))
    (2 * scale n * η n + D * (1 + Real.log (2 + scale n)))
    (mul_nonneg hD (hscale0 n).le) (mul_nonneg hD hlog)
    (add_nonneg (mul_nonneg (mul_nonneg (by norm_num) (hscale0 n).le) (hη0 n))
      (mul_nonneg hD hlog)) path hmetric hheight
  have hlast : (⟨h - 1, by omega⟩ : Fin h).val + 1 = h := by dsimp; omega
  have hterminal := heq ⟨h - 1, by omega⟩
  rw [hlast] at hterminal
  refine ⟨γ.cast rfl ?_, ?_, ?_⟩
  · dsimp only
    rw [hterminal]
  · change PathMetricBound γ (D' * scale n) (D' * (1 + Real.log (2 + scale n)))
    simpa only [D', mul_right_comm D (scale n) (2 ^ h),
      mul_right_comm D (1 + Real.log (2 + scale n)) (2 ^ h)] using hγ
  · intro u
    obtain ⟨w, hw, hh⟩ := hγheight u
    refine ⟨w, hw, hh.trans ?_⟩
    calc 2 * scale n * η n + D * (1 + Real.log (2 + scale n)) =
          (2 * η n) * scale n + D * (1 + Real.log (2 + scale n)) := by ring
         _ ≤ ε * scale n + D' * (1 + Real.log (2 + scale n)) :=
           add_le_add (mul_le_mul_of_nonneg_right he (hscale0 n).le)
             (mul_le_mul_of_nonneg_right hDD hlog)

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanTargetBundlePaths
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instDecidableEqConeMixedWords _root_.OAI.PolycyclicRecognition.CartanWordModel.instFintypeConeMixedWords _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.inversePairCoupling_finiteOnCompacts _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual centered target geometry of successful coupled bundles -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule Set Filter
open scoped Manifold Topology NNReal

variable {EG G W I : Type} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G] [IsIsometricSMul G G]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [Fintype I] [DecidableEq I]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H) [Nonempty (Fin M.letterCount)]
  {Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H Exp)
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)

set_option maxHeartbeats 1000000 in
theorem exists_target_bundle_geometry
    (hExp : IsGroupExponential Exp)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (haarD : NilpotentExponentialHaarInput F.D.modelSpace F.D.carrier)
    (dynkinD : NilpotentDynkinExpansionInput F.D.modelSpace F.D.carrier)
    (π : G →* Multiplicative W)
    (hπ : ∀ x, (π (Exp x)).toAdd = eW (heightProjection T.character x))
    (X : I → H) {d : ℕ} (hDnil : lowerCentralSeries ℝ H H d = ⊥)
    (bD₀ : Basis (Fin (finrank ℝ H)) ℝ H)
    (βD : WordBasisSelections X (boundedBracketWords d))
    (hβD : IsMaximizingColumnBasis (wordListCoordinates X (boundedBracketWords d) bD₀)
      (fun w => bracketWordExponent (fun _ : I => 1) w) βD.val)
    (scale : ℕ → ℝ) (hscale : Tendsto scale atTop atTop) (hscale0 : ∀ n, 0 < scale n)
    (pivot : H) (v : Fin M.letterCount → H)
    (E V : Set W) (hE : Convex ℝ E) (hpivot : eW (heightProjection T.character pivot) ∈ E)
    (hV : IsOpen V) (hVconv : Convex ℝ V) (hEV : E ⊆ V)
    (hv : ∀ i, eW (heightProjection T.character (pivot + v i : H)) ∈ E)
    (s : Fin M.letterCount → ℝ)
    (hs : ∀ i, cartanHeightWeight T H (M.weight i)
      (eW.symm (eW (heightProjection T.character (pivot + v i : H)))) = s i)
    {m h : ℕ} (letters : Fin m → Fin M.letterCount) (ρ : ℝ) (hρ : 0 ≤ ρ) :
    let b := WordBasisSelections.basis X (boundedBracketWords d) βD
    let cost := fun j => bracketWordExponent (fun _ : I => 1) (βD.val j)
    let br := fun n => exponentialRescaleBasis b cost (Real.log (scale n))
    let height : H →ₗ[ℝ] W := eW.toLinearMap.comp
      ((heightProjection T.character).comp H.incl.toLinearMap)
    ∃ Q : Set (Fin (finrank ℝ H) → ℝ),
      IsCompact Q ∧ Q ⊆ {z | height (b.equivFun.symm z) ∈ V} ∧
      ∀ {Λ Kπ : ℝ≥0} (p : ℕ → NormalizedPair G Λ),
      LipschitzWith Kπ (fun g => (π g).toAdd) →
      ∀ (Good : ℕ → Set F.N.carrier) (x : ℕ → G)
        (k : ℕ → Fin h → F.N.carrier) (A : Fin h → W →ₗ[ℝ] W)
        (offset : Fin h → W) (ε δ : ℕ → ℝ)
        (initial : ℕ → F.N.carrier) (S : ℕ → Set (Fin h → F.N.carrier)),
      (∀ n, initial n ∈ Good n) →
      (∀ n, 0 ≤ ε n) → Tendsto ε atTop (𝓝 0) →
      (∀ n, 0 ≤ δ n) → Tendsto δ atTop (𝓝 0) →
      (∀ᶠ n in atTop, ∀ i : Fin h,
        dist (Exp (scale n • (pivot : GroupLieAlgebra (𝓘(ℝ, EG)) G)))
          (F.inclusionN (k n i) * Exp (scale n • (pivot : GroupLieAlgebra (𝓘(ℝ, EG)) G))) ≤
            δ n * scale n) →
      (∀ᶠ n in atTop, ∀ i (q : F.N.carrier), q ∈ Good n → ∀ z ∈ Q, height (b.equivFun.symm z) ∈ E →
        ‖rescaledMapProfile (fun g => (π ((p n).val.1 g)).toAdd) (x n)
            (F.inclusionN (q * k n i)) (Real.log (scale n))
            (fun z => Exp ((br n).equivFun.symm z)) z -
          (A i (height (b.equivFun.symm z)) + offset i)‖ ≤ ε n) →
      (∀ᶠ n in atTop, ∀ v ∈ S n,
        ∃ t : Fin (h * m + h * m) → ℝ, ‖t‖ ≤ ρ ∧
          SwitchSuccessful (fun _ => Good n) 0 (h * m) (initial n)
            (sampledSwitchParameters
              (coupledRootIntervalSample (F.ExpN ∘ F.N.equiv)
                (fun j : Fin (h * m) => letters (finProdFinEquiv.symm j).2)
                M.letter s (scale n) (bundleConjugator m (k n))) (h * m) t) ∧
          ∀ i : Fin h, v i = sourceBundleBoundary (initial n)
            (fun i => MulAut.conj (k n i))
            (sourceBundleProduct F.N.equiv F.ExpN M.letter s letters
              (bundleParameterChart h m) (scale n) t) (i.val + 1)) →
      (hpath : ∀ g : G, ∃ γ : ℝ → G, γ 0 = 1 ∧ γ 1 = g ∧
        ∀ t ∈ Icc (0 : ℝ) 1, ∀ u ∈ Icc (0 : ℝ) 1,
          dist (γ t) (γ u) ≤ dist 1 g * |t - u|) →
      ∃ (D : ℝ) (η : ℕ → ℝ), 0 ≤ D ∧ (∀ n, 0 ≤ η n) ∧
        Tendsto η atTop (𝓝 0) ∧
        ∀ᶠ n in atTop, ∀ y ∈ (fun v : Fin h → F.N.carrier => fun i =>
            basedImage (p n).val.1
              (x n * F.inclusionN (initial n) *
                Exp (scale n • (pivot : GroupLieAlgebra (𝓘(ℝ, EG)) G)))
              (x n * F.inclusionN (v i) *
                Exp (scale n • (pivot : GroupLieAlgebra (𝓘(ℝ, EG)) G)))) '' S n,
          ∃ paths : ∀ i : Fin h, Path (1 : G)
              ((basedTuplePosition y i.val)⁻¹ * basedTuplePosition y (i.val + 1)),
            (∀ i, PathMetricBound (paths i) (D * scale n)
              (D * (1 + Real.log (2 + scale n)))) ∧
            (∀ i u, ∃ w ∈ (fun z => A i (z - height pivot)) '' E,
              ‖(π (paths i u)).toAdd - scale n • w‖ ≤
                2 * scale n * η n + D * (1 + Real.log (2 + scale n))) ∧
            ∀ i : Fin h,
              ‖(π ((basedTuplePosition y i.val)⁻¹ * basedTuplePosition y (i.val + 1))).toAdd‖ ≤
                η n * scale n := by
  classical
  let : IsTopologicalGroup G := topologicalGroup_of_lieGroup (𝓘(ℝ, EG)) ⊤
  dsimp only
  obtain ⟨Q, C, hQ, hQV, _, hp⟩ := M.exists_common_bundle_profile_paths
    T F eW hExp realize haarD dynkinD π hπ X hDnil bD₀ βD hβD scale hscale hscale0
    pivot v E V hE hpivot hV hVconv hEV hv s hs letters ρ hρ
  refine ⟨Q, hQ, hQV, ?_⟩
  intro Λ Kπ p hLip Good x k A offset ε δ initial S hi hε0 hε hδ0 hδ hb hg hr hpath
  obtain ⟨D, η, hD, hη0, hη, hpaths⟩ := hp (fun n g => (π ((p n).val.1 g)).toAdd)
    (Kπ * Λ) (fun n => hLip.comp (p n).property.1.1) Good x k A offset ε δ
    hε0 hε hδ0 hδ hb hg hpath
  let D' := max D (Λ * D)
  have hD' : 0 ≤ D' := hD.trans (le_max_left _ _)
  refine ⟨D', η, hD', hη0, hη, ?_⟩
  filter_upwards [hpaths, hr] with n hn hr
  have hlog : 0 ≤ 1 + Real.log (2 + scale n) := by
    have := Real.log_nonneg (show 1 ≤ 2 + scale n by linarith [hscale0 n])
    linarith
  have ht := reachable_image_tuple_paths F.inclusionN (p n).val.1 (p n).property.1.1 π
    (x n) (Exp (scale n • (pivot : GroupLieAlgebra (𝓘(ℝ, EG)) G))) (initial n) (S n)
    (fun t : Fin (h * m + h * m) → ℝ => ‖t‖ ≤ ρ ∧
      SwitchSuccessful (fun _ => Good n) 0 (h * m) (initial n)
        (sampledSwitchParameters
          (coupledRootIntervalSample (F.ExpN ∘ F.N.equiv)
            (fun j : Fin (h * m) => letters (finProdFinEquiv.symm j).2)
            M.letter s (scale n) (bundleConjugator m (k n))) (h * m) t))
    (fun t => sourceBundleBoundary (initial n) (fun i => MulAut.conj (k n i))
      (sourceBundleProduct F.N.equiv F.ExpN M.letter s letters
        (bundleParameterChart h m) (scale n) t))
    (fun _ _ => sourceBundleBoundary_zero _ _ _) ?_
    (fun i => (fun z => A i (z - eW (heightProjection T.character pivot))) '' E)
    (scale n) (D * scale n) (D * (1 + Real.log (2 + scale n)))
    (2 * scale n * η n + D * (1 + Real.log (2 + scale n))) (η n * scale n)
    (fun t ht i => hn (initial n) t (hi n) ht.1 ht.2 i)
  · intro y hy
    obtain ⟨paths, hm, hh, he⟩ := ht y hy
    refine ⟨paths, ?_, ?_, he⟩
    · intro i
      apply (hm i).mono
      · calc Λ * (D * scale n) = (Λ * D) * scale n := by ring
             _ ≤ D' * scale n := mul_le_mul_of_nonneg_right (le_max_right _ _) (hscale0 n).le
      · calc Λ * (D * (1 + Real.log (2 + scale n))) =
                (Λ * D) * (1 + Real.log (2 + scale n)) := by ring
             _ ≤ D' * (1 + Real.log (2 + scale n)) :=
               mul_le_mul_of_nonneg_right (le_max_right _ _) hlog
    · intro i u
      obtain ⟨w, hw, he⟩ := hh i u
      refine ⟨w, hw, he.trans ?_⟩
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_right (le_max_left _ _) hlog)
  · intro v hv
    obtain ⟨t, ht, hs, he⟩ := hr v hv
    exact ⟨t, ⟨ht, hs⟩, fun i => (he i).symm⟩

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanCoupledProfileComparison
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_nonempty _root_.OAI.PolycyclicRecognition.finite_templateSymmetryGroup _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.instFiniteRootOffsetConeIndex _root_.OAI.PolycyclicRecognition.instFiniteSubtypeLinearEquivRealIdMemSubgroupLinearSupportSymmetryGroup _root_.OAI.PolycyclicRecognition.instNonemptyRootOffsetConeIndex _root_.OAI.PolycyclicRecognition.inversePairCoupling_finiteOnCompacts _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual coupled source-to-target profile comparison

A positive common good set supplies all tuples and all their paths. No
independence of the bundles, terminal-cover bound, or volume estimate is a premise.
-/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule MeasureTheory Filter Set
open scoped Manifold Topology ENNReal NNReal

variable {EG G W I : Type} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G]
  [ProperSpace G] [IsIsometricSMul G G]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H) [Nonempty (Fin M.letterCount)]
  {ExpG : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H ExpG)
  (hunimod : ∀ x : GroupLieAlgebra (𝓘(ℝ, EG)) G, LinearMap.trace ℝ _ (ad ℝ _ x) = 0)
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)
  [IsTopologicalGroup F.N.carrier]
  [SecondCountableTopology F.N.carrier] [SecondCountableTopology F.D.carrier]
  [IsTopologicalGroup F.D.carrier]


variable [Fintype I] [DecidableEq I]

set_option maxHeartbeats 1000000 in
theorem exists_coupled_profile_comparison_region
    (hExpG : IsGroupExponential ExpG) (hinjG : Function.Injective ExpG)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (rem : RemezPolynomialInput)
    (π : G →* Multiplicative W) {Kπ : ℝ≥0}
    (hLip : LipschitzWith Kπ (fun g => (π g).toAdd))
    (hπExp : ∀ x, (π (ExpG x)).toAdd = eW (heightProjection T.character x))
    (chartN : GroupLieAlgebra (𝓘(ℝ, F.N.modelSpace)) F.N.carrier ≃ₜ F.N.carrier)
    (hchartN : ∀ x, chartN x = F.ExpN x)
    (chartD : GroupLieAlgebra (𝓘(ℝ, F.D.modelSpace)) F.D.carrier ≃ₜ F.D.carrier)
    (hchartD : ∀ x, chartD x = F.ExpD x)
    (hbijN : Function.Bijective F.ExpN) (hbijD : Function.Bijective F.ExpD)
    (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
    (dynkinD : NilpotentDynkinExpansionInput F.D.modelSpace F.D.carrier)
    (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
    (haarD : NilpotentExponentialHaarInput F.D.modelSpace F.D.carrier)
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (E V cell E₁ E₂ : Set W) (hEc : IsCompact E) (hE : Convex ℝ E)
    (pivot : H) (hpivot : eW (heightProjection T.character pivot) ∈ E)
    (hV : IsOpen V) (hVconv : Convex ℝ V) (hEV : E ⊆ V)
    (v : Fin M.letterCount → H)
    (hv : ∀ i, eW (heightProjection T.character (pivot + v i : H)) ∈ E)
    (s : Fin M.letterCount → ℝ)
    (hs : ∀ i, cartanHeightWeight T H (M.weight i)
      (eW.symm (eW (heightProjection T.character (pivot + v i : H)))) = s i)
    (hsCell : ∀ i, s i ≤ (M.supportIn T hunimod eW).weightSupport cell i)
    (β β₁ β₂ βcell γ : M.Bases)
    (hβ₁ : IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
      (M.boxCost T hunimod eW E₁) β₁.val)
    (hβ₂ : IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
      (M.boxCost T hunimod eW E₂) β₂.val)
    (hβcell : IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
      (M.boxCost T hunimod eW cell) βcell.val)
    (hγ : IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
      (M.boxCost T hunimod eW E) γ.val)
    (hE₁ : IsCompact E₁) (hE₂ : IsCompact E₂) (h01 : (0 : W) ∈ E₁) (h02 : (0 : W) ∈ E₂)
    (hP₁ : (M.supportIn T hunimod eW).templateSupport E₁ =
      (M.supportIn T hunimod eW).templateSupport E)
    (hP₂ : (M.supportIn T hunimod eW).templateSupport E₂ =
      (M.supportIn T hunimod eW).templateSupport E)
    (X : I → H) {d : ℕ} (hDnil : lowerCentralSeries ℝ H H d = ⊥)
    (bD₀ : Basis (Fin (finrank ℝ H)) ℝ H)
    (βD : WordBasisSelections X (boundedBracketWords d))
    (hβD : IsMaximizingColumnBasis (wordListCoordinates X (boundedBracketWords d) bD₀)
      (fun w => bracketWordExponent (fun _ : I => 1) w) βD.val)
    {m h cN : ℕ} (letters : Fin m → Fin M.letterCount) (hh : 0 < h)
    (aN : DynkinCoefficients cN 2)
    (hm : ∀ x y, F.ExpN (finiteDynkinPolynomial aN ![x, y]) = F.ExpN x * F.ExpN y)
    (hdim : 1 ≤ finrank ℝ (cartanRootIdeal H))
    (scale : ℕ → ℝ) (hscale : Tendsto scale atTop atTop) (hscale1 : ∀ n, 1 ≤ scale n)
    (sourceLimit : WordLawData (Fin M.letterCount) (finrank ℝ (cartanRootIdeal H)))
    (hsourceLimit : Tendsto (fun n =>
      let b := M.boxBasis T hunimod eW E γ (scale n)
      (basisBracket b, fun i => b.equivFun (Real.exp (scale n * s i) • M.letter i)))
      atTop (𝓝 sourceLimit))
    (t₀ : Fin (m + m) → ℝ)
    (hsourceSub : Function.Surjective
      (fderiv ℝ (differenceAmplitudeWordEndpoint aN letters sourceLimit) t₀))
    (targetLimit : AlternatingLawData (finrank ℝ (cartanRootIdeal H)))
    (htargetLimit : Tendsto (fun n =>
      let b := M.boxBasis T hunimod eW (E₁ ∪ E₂) β (scale n)
      let b₁ := M.boxBasis T hunimod eW E₁ β₁ (scale n)
      let b₂ := M.boxBasis T hunimod eW E₂ β₂ (scale n)
      (basisBracket b, boxCoordinateChange b b₁, boxCoordinateChange b b₂))
      atTop (𝓝 targetLimit))
    (z₀ : Fin h → (Fin (finrank ℝ (cartanRootIdeal H)) → ℝ) ×
      (Fin (finrank ℝ (cartanRootIdeal H)) → ℝ))
    (htargetSub : Function.Surjective
      (fderiv ℝ (alternatingCoordinateProduct aN targetLimit.1 targetLimit.2.1 targetLimit.2.2) z₀))
    (ν : Measure F.D.carrier) [ν.IsHaarMeasure] [SigmaFinite ν]
    (ρ : ℝ) (hρ : 1 ≤ ρ)
    (A : Fin (h * 2) → W →ₗ[ℝ] W) (offset : Fin (h * 2) → W)
    (himage : ∀ i, (fun w => A i (w - eW (heightProjection T.character pivot))) '' E =
      alternatingCoordinateFamily h E₁ E₂ i)
    (hpath : ∀ g : G, ∃ γ : ℝ → G, γ 0 = 1 ∧ γ 1 = g ∧
      ∀ t ∈ Icc (0 : ℝ) 1, ∀ u ∈ Icc (0 : ℝ) 1,
        dist (γ t) (γ u) ≤ dist 1 g * |t - u|) :
    let b := WordBasisSelections.basis X (boundedBracketWords d) βD
    let br := fun n => exponentialRescaleBasis b
      (fun j => bracketWordExponent (fun _ : I => 1) (βD.val j)) (Real.log (scale n))
    let height : H →ₗ[ℝ] W := eW.toLinearMap.comp
      ((heightProjection T.character).comp H.incl.toLinearMap)
    ∃ Q : Set (Fin (finrank ℝ H) → ℝ), IsCompact Q ∧
      Q ⊆ {z | height (b.equivFun.symm z) ∈ V} ∧
      ∀ {Λ : ℝ≥0}, 0 < (Λ : ℝ) → ∀ (p : ℕ → NormalizedPair G Λ) (x : ℕ → G)
        (R : ℕ → ℝ) (k₀ : ℕ → F.N.carrier) (k : ℕ → Fin (h * 2) → F.N.carrier)
        (Good : ℕ → Set F.N.carrier) (ε δ : ℕ → ℝ),
        (∀ n, 0 ≤ R n) → HasSubexponentialUpperBoundSeq scale R →
        (∀ n, k₀ n ∈ M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) cell βcell (scale n) (R n)) →
        (∀ n i, k n i ∈ M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) cell βcell (scale n) (R n)) →
        (∀ n, MeasurableSet (Good n)) →
        (∀ n, Good n ⊆ (fun y => y * k₀ n) ''
          M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) cell βcell (scale n) 1) →
        (∀ n, 0 < ((Measure.map ((F.ExpN ∘ F.N.equiv) ∘ b₀.equivFun.symm) volume) (Good n)).toReal) →
        HasSubexponentialLowerBoundSeq scale (fun n =>
          ((Measure.map ((F.ExpN ∘ F.N.equiv) ∘ b₀.equivFun.symm) volume) (Good n)).toReal /
          ((Measure.map ((F.ExpN ∘ F.N.equiv) ∘ b₀.equivFun.symm) volume)
            ((fun y => y * k₀ n) '' M.groupBox T hunimod eW
              (F.ExpN ∘ F.N.equiv) cell βcell (scale n) 1)).toReal) →
        (∀ n, 0 ≤ ε n) → Tendsto ε atTop (𝓝 0) →
        (∀ n, 0 ≤ δ n) → Tendsto δ atTop (𝓝 0) →
        (∀ᶠ n in atTop, ∀ i,
          dist (ExpG (scale n • (pivot : GroupLieAlgebra (𝓘(ℝ, EG)) G)))
            (F.inclusionN (k n i) * ExpG (scale n • (pivot : GroupLieAlgebra (𝓘(ℝ, EG)) G))) ≤
              δ n * scale n) →
        (∀ᶠ n in atTop, ∀ i (q : F.N.carrier), q ∈ Good n → ∀ z ∈ Q, height (b.equivFun.symm z) ∈ E →
          ‖rescaledMapProfile (fun g => (π ((p n).val.1 g)).toAdd) (x n)
              (F.inclusionN (q * k n i)) (Real.log (scale n))
              (fun z => ExpG ((br n).equivFun.symm z)) z -
            (A i (height (b.equivFun.symm z)) + offset i)‖ ≤ ε n) →
        columnBasisWeight (M.boxCost T hunimod eW (E₁ ∪ E₂)) β.val ≤
          (M.supportIn T hunimod eW).templateSupport E := by
  classical
  let : IsTopologicalGroup G := topologicalGroup_of_lieGroup (𝓘(ℝ, EG)) ⊤
  dsimp only
  have hscale0 n : 0 < scale n := lt_of_lt_of_le zero_lt_one (hscale1 n)
  obtain ⟨Q, hQ, hQV, hgeom⟩ := M.exists_target_bundle_geometry T F eW hExpG realize
    haarD dynkinD π hπExp X hDnil bD₀ βD hβD scale hscale hscale0
    pivot v E V hE hpivot hV hVconv hEV hv s hs (h := h * 2) letters ρ (by linarith)
  refine ⟨Q, hQ, hQV, ?_⟩
  intro Λ hΛ p x R k₀ k Good ε δ hR0 hR hk₀ hk hGood hGoodQ hGoodpos hGoodmass
    hε0 hε hδ0 hδ hbridge hgood
  let pivotD := fun n => F.ExpD (F.D.equiv (scale n • pivot))
  have hpivotD n : F.inclusionD (pivotD n) =
      ExpG (scale n • (pivot : GroupLieAlgebra (𝓘(ℝ, EG)) G)) := F.compatibleD _
  obtain ⟨initial, S, t, hi, hS, ht, hsep, hcount, hreach⟩ := M.exists_coupled_target_tuples
    T F hunimod eW hExpG realize haarN haarD dynkinN b₀ cell E βcell γ hβcell s hsCell
    letters aN hm scale R hscale (fun n => (hscale0 n).le) hR0 hR ρ hρ k₀ k hk₀ hk rem
    (Nat.succ_le_of_lt (Nat.mul_pos (by omega) (by omega)))
    sourceLimit hsourceLimit t₀ hsourceSub Good hGood hΛ p x pivotD
    hGoodQ hGoodpos hGoodmass
  have hboundary : ∀ᶠ n in atTop, ∀ v ∈ S n,
      ∃ z : Fin ((h * 2) * m + (h * 2) * m) → ℝ, ‖z‖ ≤ ρ ∧
        SwitchSuccessful (fun _ => Good n) 0 ((h * 2) * m) (initial n)
          (sampledSwitchParameters
            (coupledRootIntervalSample (F.ExpN ∘ F.N.equiv)
              (fun j : Fin ((h * 2) * m) => letters (finProdFinEquiv.symm j).2)
              M.letter s (scale n) (bundleConjugator m (k n))) ((h * 2) * m) z) ∧
        ∀ i : Fin (h * 2), v i = sourceBundleBoundary (initial n)
          (fun i => MulAut.conj (k n i))
          (sourceBundleProduct F.N.equiv F.ExpN M.letter s letters
            (bundleParameterChart (h * 2) m) (scale n) z) (i.val + 1) := by
    filter_upwards [hreach] with n hn
    intro v hv
    obtain ⟨_, z, hz, hs, he⟩ := hn v hv
    refine ⟨z, by simpa only [Metric.mem_closedBall, dist_zero_right] using hz, hs, ?_⟩
    intro i
    rw [he]
    exact (sourceBundleBoundary_eq_stateEquiv (initial n) (fun i => MulAut.conj (k n i))
      (fun i => (innerContinuousMulEquiv (k n i)).toHomeomorph.toMeasurableEquiv)
      (fun _ _ => rfl) _ i).symm
  obtain ⟨D, η, hD, hη0, hη, htarget⟩ := hgeom p hLip Good x k A offset ε δ initial S
    hi hε0 hε hδ0 hδ hbridge hgood hboundary hpath
  obtain ⟨Cs, hCs, hsource⟩ := M.exists_source_bundle_terminal_bounds T F eW
    hExpG realize haarD dynkinD π hπExp X hDnil bD₀ βD hβD scale hscale hscale0
    pivot v E V hE hpivot hV hVconv hEV hv s hs letters ρ (by linarith)
    (by omega) hbijN hLip hpath Good x k initial hi S δ hδ0 hδ hbridge hboundary
  let pivotG := fun n => ExpG (scale n • (pivot : GroupLieAlgebra (𝓘(ℝ, EG)) G))
  let origin := fun n => x n * F.inclusionN (initial n) * pivotG n
  let last : Fin (h * 2) := ⟨h * 2 - 1, by omega⟩
  let terminals := fun n => relativeTupleTerminals F.inclusionN (origin n) (x n) (pivotG n) last (S n)
  let E₀ := (fun w => w - eW (heightProjection T.character pivot)) '' E
  have hE₀ : IsCompact E₀ := hEc.image (continuous_id.sub continuous_const)
  have h0E₀ : (0 : W) ∈ E₀ := ⟨_, hpivot, sub_self _⟩
  have hnum : HasSubexponentialLowerBoundSeq scale (fun n => ((t n).card : ℝ) /
      Real.exp (scale n * ((h : ℝ) * columnBasisWeight (M.boxCost T hunimod eW E₁) β₁.val +
        (h : ℝ) * columnBasisWeight (M.boxCost T hunimod eW E₂) β₂.val))) := by
    have he : ((h * 2 : ℕ) : ℝ) * columnBasisWeight (M.boxCost T hunimod eW E) γ.val =
        (h : ℝ) * columnBasisWeight (M.boxCost T hunimod eW E₁) β₁.val +
          (h : ℝ) * columnBasisWeight (M.boxCost T hunimod eW E₂) β₂.val := by
      rw [M.columnBasisWeight_eq_templateSupport_of_maximizing T hunimod eW b₀ E γ hγ,
        M.columnBasisWeight_eq_templateSupport_of_maximizing T hunimod eW b₀ E₁ β₁ hβ₁,
        M.columnBasisWeight_eq_templateSupport_of_maximizing T hunimod eW b₀ E₂ β₂ hβ₂,
        hP₁, hP₂]
      push_cast
      ring
    simpa only [he] using hcount
  have hle := M.source_target_product_exponent_le_m T F hunimod eW hExpG hinjG realize rem
    π hLip.continuous hπExp chartN hchartN chartD hchartD hbijN hbijD dynkinN dynkinD
    haarN haarD b₀ β β₁ β₂ (E₁ ∪ E₂) E₁ E₂ hh aN hm hdim scale η hscale hscale1 hη0 hη
    hpath hLip D D hD hD targetLimit htargetLimit z₀ htargetSub hE₁ hE₂ h01 h02 hβ₁ hβ₂ ν
    t ?_ hsep hnum E₀ hE₀ ⟨0, h0E₀⟩ terminals
    (fun n => (isCompact_relativeTupleTerminals F.inclusionN F.closedN.continuous
      (origin n) (x n) (pivotG n) last (hS n)).totallyBounded) hCs hsource
    (fun n => normalizedTranslate (origin n) (p n)) (fun _ => 1) ?_
  · have he : (M.supportIn T hunimod eW).templateSupport E₀ =
        (M.supportIn T hunimod eW).templateSupport E := by
      simpa only [E₀, sub_eq_add_neg] using
        (M.supportIn T hunimod eW).templateSupport_translate hEc ⟨_, hpivot⟩
          (-eW (heightProjection T.character pivot))
    exact he ▸ hle
  · filter_upwards [htarget] with n hn
    intro y hy
    have hymem := ht n hy
    simp only [hpivotD] at hymem
    obtain ⟨paths, hm, hh, he⟩ := hn y hymem
    refine ⟨paths, hm, ?_, he⟩
    intro i u
    obtain ⟨w, hw, he⟩ := hh i u
    exact ⟨w, (himage i).subset hw, he⟩
  · filter_upwards [] with n
    intro y hy
    have hymem := ht n hy
    simp only [hpivotD] at hymem
    obtain ⟨z, hz, he⟩ := centered_image_terminal_mem (p n) F.inclusionN
      (origin n) (x n) (pivotG n) last (S n) hymem
    exact ⟨z, hz, by simpa only [one_mul] using he⟩

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanTemplateSupports
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instDecidableEqConeMixedWords _root_.OAI.PolycyclicRecognition.CartanWordModel.instFintypeConeMixedWords _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finite_templateSymmetryGroup _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.instFiniteRootOffsetConeIndex _root_.OAI.PolycyclicRecognition.instFiniteSubtypeLinearEquivRealIdMemSubgroupLinearSupportSymmetryGroup _root_.OAI.PolycyclicRecognition.instNonemptyRootOffsetConeIndex _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.CartanFactorModel.heightRay_zero _root_.OAI.PolycyclicRecognition.CartanFactorModel.realScaleProfile_apply _root_.OAI.PolycyclicRecognition.CartanFactorModel.sampledProbeProfile_apply _root_.OAI.PolycyclicRecognition.cartanWeightDerivation_apply_root _root_.OAI.PolycyclicRecognition.cartanWeightDilation_apply _root_.OAI.PolycyclicRecognition.cartanWeightScale_add_apply _root_.OAI.PolycyclicRecognition.cartanWeightScale_zero_apply _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.nilshadowWeightDerivation_symm _root_.OAI.PolycyclicRecognition.nilshadowWeightOperator_symm _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual supporting Cartan directions for compact height templates -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Set

set_option maxHeartbeats 1000000 in
/-- All the independently supported generator exponents are realized by
actual Cartan vectors whose heights stay in the given compact template. -/
theorem exists_cartan_template_supports
    {L W : Type} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
    {H : LieSubalgebra ℝ L} [H.IsCartanSubalgebra]
    (M : CartanWordModel H) {n : ℕ} (T : TriangularAdjoint L n)
    (hunimod : ∀ x : L, LinearMap.trace ℝ L (LieAlgebra.ad ℝ L x) = 0)
    (eW : HeightSpace T.character ≃ₗ[ℝ] W)
    (E : Set W) (hE : IsCompact E) (hne : E.Nonempty) :
    ∃ v : Fin M.letterCount → H,
      (∀ i, eW (heightProjection T.character (v i : L)) ∈ E) ∧
      M.templateSupportExponent v = (M.supportIn T hunimod eW).weightSupport E := by
  classical
  choose w hw hs using fun i => (M.supportIn T hunimod eW).exists_weightSupport_point hE hne i
  let v : Fin M.letterCount → H := fun i => cartanHeightSection T H (eW.symm (w i))
  have hv i : eW (heightProjection T.character (v i : L)) = w i := by simp [v]
  refine ⟨v, fun i => hv i ▸ hw i, ?_⟩
  funext i
  rw [hs i]
  change M.weight i (v i) = cartanHeightWeight T H (M.weight i) (eW.symm (w i))
  rfl

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanGoodTemplateComparison
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_nonempty _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.instFiniteRootOffsetConeIndex _root_.OAI.PolycyclicRecognition.instNonemptyRootOffsetConeIndex _root_.OAI.PolycyclicRecognition.inversePairCoupling_finiteOnCompacts _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.CartanFactorModel.heightRay_zero _root_.OAI.PolycyclicRecognition.CartanFactorModel.realScaleProfile_apply _root_.OAI.PolycyclicRecognition.CartanFactorModel.sampledProbeProfile_apply _root_.OAI.PolycyclicRecognition.basisDynkinParameter_zero _root_.OAI.PolycyclicRecognition.bracketWordDifferential_mul _root_.OAI.PolycyclicRecognition.cartanWeightDerivation_apply_root _root_.OAI.PolycyclicRecognition.chartExponentialFlow_zero _root_.OAI.PolycyclicRecognition.derivationSemidirectHom_apply _root_.OAI.PolycyclicRecognition.exponentialHomOfDynkin_apply_exp _root_.OAI.PolycyclicRecognition.exponentialRescaleBasis_zero _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.modelNilradicalLinearAction_apply _root_.OAI.PolycyclicRecognition.modelNilradicalRotation_apply _root_.OAI.PolycyclicRecognition.modelNilradicalRotation_mul _root_.OAI.PolycyclicRecognition.modelNilradicalRotation_one _root_.OAI.PolycyclicRecognition.nilshadowWeightDerivation_symm _root_.OAI.PolycyclicRecognition.nilshadowWeightOperator_symm _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Template comparison for the diagonal's actual positive good sets

The good sets have subexponential relative Haar mass and affine errors
vanishing on every prescribed compact. They need not occupy a fixed
positive fraction of the original sampling probability.
-/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule MeasureTheory Filter Set
open scoped Manifold Topology ENNReal NNReal

variable {EG G W I : Type} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G]
  [ProperSpace G] [IsIsometricSMul G G]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H) [Nonempty (Fin M.letterCount)]
  {ExpG : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H ExpG)
  (hunimod : ∀ x : GroupLieAlgebra (𝓘(ℝ, EG)) G, LinearMap.trace ℝ _ (ad ℝ _ x) = 0)
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)
  [IsTopologicalGroup F.N.carrier]
  [SecondCountableTopology F.N.carrier] [SecondCountableTopology F.D.carrier]
  [IsTopologicalGroup F.D.carrier]


variable [Fintype I] [DecidableEq I]

set_option maxHeartbeats 1000000 in
theorem good_affine_templates_support_le_m_oai
    (hExpG : IsGroupExponential ExpG) (hinjG : Function.Injective ExpG)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (rem : RemezPolynomialInput)
    (π : G →* Multiplicative W) {Kπ : ℝ≥0}
    (hLip : LipschitzWith Kπ (fun g => (π g).toAdd))
    (hπExp : ∀ x, (π (ExpG x)).toAdd = eW (heightProjection T.character x))
    (chartN : GroupLieAlgebra (𝓘(ℝ, F.N.modelSpace)) F.N.carrier ≃ₜ F.N.carrier)
    (hchartN : ∀ x, chartN x = F.ExpN x)
    (chartD : GroupLieAlgebra (𝓘(ℝ, F.D.modelSpace)) F.D.carrier ≃ₜ F.D.carrier)
    (hchartD : ∀ x, chartD x = F.ExpD x)
    (hbijN : Function.Bijective F.ExpN) (hbijD : Function.Bijective F.ExpD)
    (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
    (dynkinD : NilpotentDynkinExpansionInput F.D.modelSpace F.D.carrier)
    (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
    (haarD : NilpotentExponentialHaarInput F.D.modelSpace F.D.carrier)
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))

    (E cell : Set W) (hE : IsCompact E) (hEconv : Convex ℝ E)
    (hcell : IsCompact cell) (hEcell : E ⊆ cell)
    (pivot : H) (hpivot : eW (heightProjection T.character pivot) ∈ E)
    (A₁ A₂ : templateSymmetryGroup (M.supportIn T hunimod eW)) (offset₁ offset₂ : W)
    (βcell : M.Bases)
    (hβcell : IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
      (M.boxCost T hunimod eW cell) βcell.val)
    (X : I → H) {d : ℕ} (hDnil : lowerCentralSeries ℝ H H d = ⊥)
    (bD₀ : Basis (Fin (finrank ℝ H)) ℝ H)
    (βD : WordBasisSelections X (boundedBracketWords d))
    (hβD : IsMaximizingColumnBasis (wordListCoordinates X (boundedBracketWords d) bD₀)
      (fun w => bracketWordExponent (fun _ : I => 1) w) βD.val)

    {cN : ℕ} (aN : DynkinCoefficients cN 2)
    (hm : ∀ x y, F.ExpN (finiteDynkinPolynomial aN ![x, y]) = F.ExpN x * F.ExpN y)
    (hdim : 1 ≤ finrank ℝ (cartanRootIdeal H))
    (scale : ℕ → ℝ) (hscale : Tendsto scale atTop atTop) (hscale1 : ∀ n, 1 ≤ scale n)
    (ν : Measure F.D.carrier) [ν.IsHaarMeasure] [SigmaFinite ν]
    (hpath : ∀ g : G, ∃ γ : ℝ → G, γ 0 = 1 ∧ γ 1 = g ∧
      ∀ t ∈ Icc (0 : ℝ) 1, ∀ u ∈ Icc (0 : ℝ) 1,
        dist (γ t) (γ u) ≤ dist 1 g * |t - u|)
    {Λ : ℝ≥0} (hΛ : 0 < (Λ : ℝ)) (p : ℕ → NormalizedPair G Λ) (x : ℕ → G)
    (R : ℕ → ℝ) (k₀ k : ℕ → F.N.carrier) (δ : ℕ → ℝ)
    (hR0 : ∀ n, 0 ≤ R n) (hR : HasSubexponentialUpperBoundSeq scale R)
    (hk₀ : ∀ n, k₀ n ∈ M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) cell βcell (scale n) (R n))
    (hk : ∀ n, k n ∈ M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) cell βcell (scale n) (R n))
    (hδ0 : ∀ n, 0 ≤ δ n) (hδ : Tendsto δ atTop (𝓝 0))
    (hbridge : ∀ᶠ n in atTop,
      dist (ExpG (scale n • (pivot : GroupLieAlgebra (𝓘(ℝ, EG)) G)))
        (F.inclusionN (k n) * ExpG (scale n • (pivot : GroupLieAlgebra (𝓘(ℝ, EG)) G))) ≤
          δ n * scale n)
    (hgood : ∀ Q : Set (Fin (finrank ℝ H) → ℝ), IsCompact Q →
      ∃ (Good : ℕ → Set F.N.carrier) (ε : ℕ → ℝ),
        (∀ n, MeasurableSet (Good n)) ∧
        (∀ n, Good n ⊆ (fun y => y * k₀ n) ''
          M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) cell βcell (scale n) 1) ∧
        (∀ n, 0 < ((Measure.map ((F.ExpN ∘ F.N.equiv) ∘ b₀.equivFun.symm) volume)
          (Good n)).toReal) ∧
        HasSubexponentialLowerBoundSeq scale (fun n =>
          ((Measure.map ((F.ExpN ∘ F.N.equiv) ∘ b₀.equivFun.symm) volume) (Good n)).toReal /
          ((Measure.map ((F.ExpN ∘ F.N.equiv) ∘ b₀.equivFun.symm) volume)
            ((fun y => y * k₀ n) '' M.groupBox T hunimod eW
              (F.ExpN ∘ F.N.equiv) cell βcell (scale n) 1)).toReal) ∧
        (∀ n, 0 ≤ ε n) ∧ Tendsto ε atTop (𝓝 0) ∧
        let b := WordBasisSelections.basis X (boundedBracketWords d) βD
        let br := fun n => exponentialRescaleBasis b
          (fun j => bracketWordExponent (fun _ : I => 1) (βD.val j)) (Real.log (scale n))
        let height : H →ₗ[ℝ] W := eW.toLinearMap.comp
          ((heightProjection T.character).comp H.incl.toLinearMap)
        ∀ᶠ n in atTop, ∀ q ∈ Good n, ∀ z ∈ Q, height (b.equivFun.symm z) ∈ E →
          ‖rescaledMapProfile (fun g => (π ((p n).val.1 g)).toAdd) (x n)
            (F.inclusionN q) (Real.log (scale n))
            (fun z => ExpG ((br n).equivFun.symm z)) z -
            (A₁.val (height (b.equivFun.symm z)) + offset₁)‖ ≤ ε n ∧
          ‖rescaledMapProfile (fun g => (π ((p n).val.1 g)).toAdd) (x n)
            (F.inclusionN (q * k n)) (Real.log (scale n))
            (fun z => ExpG ((br n).equivFun.symm z)) z -
            (A₂.val (height (b.equivFun.symm z)) + offset₂)‖ ≤ ε n) :
    (M.supportIn T hunimod eW).templateSupport
      ((A₁.val '' ((fun w => w - eW (heightProjection T.character pivot)) '' E)) ∪
        (A₂.val '' ((fun w => w - eW (heightProjection T.character pivot)) '' E))) ≤
      (M.supportIn T hunimod eW).templateSupport E := by
  classical
  let height : H →ₗ[ℝ] W := eW.toLinearMap.comp
    ((heightProjection T.character).comp H.incl.toLinearMap)
  let E₀ := (fun w => w - height pivot) '' E
  let E₁ := A₁.val '' E₀
  let E₂ := A₂.val '' E₀
  have hE₀ : IsCompact E₀ := hE.image (continuous_id.sub continuous_const)
  have hE₀conv : Convex ℝ E₀ := hEconv.affine_image
    ((AffineMap.id ℝ W) - AffineMap.const ℝ W (height pivot))
  have h0 : (0 : W) ∈ E₀ := ⟨height pivot, hpivot, sub_self _⟩
  have hE₁ : IsCompact E₁ := hE₀.image A₁.val.continuous_of_finiteDimensional
  have hE₂ : IsCompact E₂ := hE₀.image A₂.val.continuous_of_finiteDimensional
  have h01 : (0 : W) ∈ E₁ := ⟨0, h0, map_zero _⟩
  have h02 : (0 : W) ∈ E₂ := ⟨0, h0, map_zero _⟩
  have hP : (M.supportIn T hunimod eW).templateSupport E₀ =
      (M.supportIn T hunimod eW).templateSupport E := by
    simpa only [E₀, sub_eq_add_neg] using
      (M.supportIn T hunimod eW).templateSupport_translate hE ⟨_, hpivot⟩ (-height pivot)
  have hP₁ : (M.supportIn T hunimod eW).templateSupport E₁ =
      (M.supportIn T hunimod eW).templateSupport E :=
    (A₁.property E₀ hE₀ ⟨0, h0⟩ hE₀conv).trans hP
  have hP₂ : (M.supportIn T hunimod eW).templateSupport E₂ =
      (M.supportIn T hunimod eW).templateSupport E :=
    (A₂.property E₀ hE₀ ⟨0, h0⟩ hE₀conv).trans hP
  obtain ⟨β, hβ, hβweight⟩ := M.exists_maximizing_box_basis T hunimod eW b₀ (E₁ ∪ E₂)
  obtain ⟨β₁, hβ₁, _⟩ := M.exists_maximizing_box_basis T hunimod eW b₀ E₁
  obtain ⟨β₂, hβ₂, _⟩ := M.exists_maximizing_box_basis T hunimod eW b₀ E₂
  obtain ⟨γ, hγ, _⟩ := M.exists_maximizing_box_basis T hunimod eW b₀ E
  obtain ⟨u, hu, h, hh, target, z₀, ht, htsub, m, letters, source, t₀, hs, hssub⟩ :=
    M.exists_source_target_comparison_schemes_m T F hunimod eW hExpG realize haarN b₀ aN hm
      E E₁ E₂ hE₁ ⟨0, h01⟩ hE₂ ⟨0, h02⟩ β β₁ β₂ γ hβ hβ₁ hβ₂ hγ scale
      (fun n => le_trans zero_le_one (hscale1 n)) hdim
  obtain ⟨support, hsupport, hsupportWeight⟩ :=
    M.exists_cartan_template_supports T hunimod eW E hE ⟨_, hpivot⟩
  let v := fun i => support i - pivot
  let s := (M.supportIn T hunimod eW).weightSupport E
  have hv i : eW (heightProjection T.character (pivot + v i : H)) ∈ E := by
    simpa only [v, add_sub_cancel] using hsupport i
  have hvs i : cartanHeightWeight T H (M.weight i)
      (eW.symm (eW (heightProjection T.character (pivot + v i : H)))) = s i := by
    rw [show pivot + v i = support i by dsimp [v]; abel, eW.symm_apply_apply,
      cartanHeightWeight_projection]
    exact congrFun hsupportWeight i
  have hsCell i : s i ≤ (M.supportIn T hunimod eW).weightSupport cell i := by
    dsimp only [s]
    rw [← hsupportWeight]
    have ht := (M.supportIn T hunimod eW).weight_le_weightSupport hcell
      (hEcell (hsupport i)) i
    simpa only [templateSupportExponent, supportIn, SupportDatum.transport_weight_apply, supportDatum_weight,
      eW.symm_apply_apply, cartanHeightWeight_projection] using ht
  let kb := fun n => alternatingCoordinateFamily h (1 : F.N.carrier) (k (u n))
  let As := alternatingCoordinateFamily h A₁.val.toLinearMap A₂.val.toLinearMap
  let bs := alternatingCoordinateFamily h offset₁ offset₂
  have hk1 n : (1 : F.N.carrier) ∈ M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv)
      cell βcell (scale (u n)) (R (u n)) := by
    refine ⟨0, ?_, ?_⟩
    · simp only [Function.comp_apply, map_zero, F.isExpN.map_zero]
    · simpa only [map_zero, norm_zero] using hR0 (u n)
  have hkb n i : kb n i ∈ M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv)
      cell βcell (scale (u n)) (R (u n)) := by
    dsimp only [kb, alternatingCoordinateFamily]
    split_ifs
    · exact hk1 n
    · exact hk (u n)
  have himage i : (fun w => As i (w - height pivot)) '' E =
      alternatingCoordinateFamily h E₁ E₂ i := by
    dsimp only [As, alternatingCoordinateFamily]
    split_ifs <;> simp only [E₁, E₂, E₀, image_image, LinearEquiv.coe_coe]
  have hb : ∀ᶠ n in atTop, ∀ i,
      dist (ExpG (scale (u n) • (pivot : GroupLieAlgebra (𝓘(ℝ, EG)) G)))
        (F.inclusionN (kb n i) * ExpG (scale (u n) • (pivot : GroupLieAlgebra (𝓘(ℝ, EG)) G))) ≤
          δ (u n) * scale (u n) := by
    filter_upwards [hu.tendsto_atTop.eventually hbridge] with n hn i
    dsimp only [kb, alternatingCoordinateFamily]
    split_ifs
    · simpa only [map_one, one_mul, dist_self] using
        mul_nonneg (hδ0 (u n)) (le_trans zero_le_one (hscale1 (u n)))
    · exact hn
  obtain ⟨Q, hQ, _, hcompare⟩ := M.exists_coupled_profile_comparison_region T F hunimod eW
    hExpG hinjG realize rem π hLip hπExp chartN hchartN chartD hchartD hbijN hbijD
    dynkinN dynkinD haarN haarD b₀ E univ cell E₁ E₂ hE hEconv pivot hpivot
    isOpen_univ convex_univ (subset_univ _) v hv s hvs hsCell β β₁ β₂ βcell γ
    hβ₁ hβ₂ hβcell hγ hE₁ hE₂ h01 h02 hP₁ hP₂ X hDnil bD₀ βD hβD letters hh aN hm
    hdim (scale ∘ u) (hscale.comp hu.tendsto_atTop) (fun n => hscale1 (u n))
    source hs t₀ hssub target ht z₀ htsub ν 1 le_rfl As bs himage hpath
  obtain ⟨Good, ε, hGood, hGoodQ, hGoodpos, hGoodmass, hε0, hε, happ⟩ := hgood Q hQ
  change (M.supportIn T hunimod eW).templateSupport (E₁ ∪ E₂) ≤ _
  rw [← hβweight]
  apply hcompare hΛ (p ∘ u) (x ∘ u) (R ∘ u) (k₀ ∘ u) kb (Good ∘ u) (ε ∘ u) (δ ∘ u)
    (fun n => hR0 (u n)) (hR.comp hu.tendsto_atTop) (fun n => hk₀ (u n)) hkb
    (fun n => hGood (u n)) (fun n => hGoodQ (u n)) (fun n => hGoodpos (u n))
    (hGoodmass.comp hu.tendsto_atTop) (fun n => hε0 (u n)) (hε.comp hu.tendsto_atTop)
    (fun n => hδ0 (u n)) (hδ.comp hu.tendsto_atTop) hb
  filter_upwards [hu.tendsto_atTop.eventually happ] with n hn
  intro i q hq z hz hze
  have hboth := hn q hq z hz hze
  dsimp only [kb, As, bs, alternatingCoordinateFamily]
  split_ifs
  · simpa only [mul_one, LinearEquiv.coe_coe, Function.comp_apply] using hboth.1
  · exact hboth.2

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

theorem solution : type_of% @OAI.PolycyclicRecognition.CartanWordModel.good_affine_templates_support_le_m_oai := @OAI.PolycyclicRecognition.CartanWordModel.good_affine_templates_support_le_m_oai
