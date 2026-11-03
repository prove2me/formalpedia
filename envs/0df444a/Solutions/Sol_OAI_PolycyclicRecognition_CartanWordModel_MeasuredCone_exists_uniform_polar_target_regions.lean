-- Prove2me | solution 1 for OAI.PolycyclicRecognition.CartanWordModel.MeasuredCone.exists_uniform_polar_target_regions
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-02T22:39:48.698945+00:00
-- url     : https://prove2.me/submissions/c7e2fdb6-2bf7-44dd-8bfa-cc3aa8ae2a90

import Mathlib
import Definitions.Def_PolycyclicRecognition
import Definitions.Def_OAIQ093D027
import Theorems.Thm_OAI_PolycyclicRecognition_CartanWordModel_exists_uniform_measured_probe_regions

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
local instance instNontrivialSubtypeMemLieSubmoduleRealLieSubalgebraRootSpaceCoeWeight_solutions_1_r16bd14_1 : Nontrivial (rootSpace H χ) :=
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
local instance instNontrivialSubtypeMemLieSubmoduleRealLieSubalgebraRootSpaceCoeWeight_solutions_2_r16bd14_1 : Nontrivial (rootSpace H χ) :=
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
local instance instNontrivialSubtypeMemLieSubmoduleRealLieSubalgebraRootSpaceCoeWeight_solutions_2_r16bd14_2 : Nontrivial (rootSpace H χ) :=
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
attribute [-simp] _root_.OAI.PolycyclicRecognition.CartanFactorModel.realScaleProfile_apply _root_.OAI.PolycyclicRecognition.bracketWordDifferential_mul _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.OAI.PolycyclicRecognition.wordBasisOfDet_val _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
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

variable [DecidableEq I]

omit [DecidableEq I] in
/-- An inside abelian coordinate vanishes on the entire mixed-word ideal. -/
theorem inside_abelian_coordinate_kills_mixed
    {Q : Type} [AddCommGroup Q] [Module ℝ Q]
    (X : I → L) (outside : I → Prop)
    (q : L →ₗ[ℝ] Q) (hq : ∀ x y : L, q ⁅x, y⁆ = 0)
    (bq : Basis I ℝ Q) (hX : ∀ i, q (X i) = bq i)
    (i : I) (hi : ¬outside i) :
    mixedWordSpan X outside ≤ LinearMap.ker ((bq.coord i).comp q) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨w, hw, rfl⟩
  change bq.repr (q (evalBracketWord X w)) i = 0
  cases w with
  | of j =>
    have hij : i ≠ j := fun he => hi (he ▸ hw)
    simp [evalBracketWord, hX, hij]
  | mul u v => simp [evalBracketWord, hq]

omit [DecidableEq I] in
/-- Every retained generator occurs as a one-letter word in any pure
word basis of the quotient. -/
theorem mandatory_inside_letter_in_quotient
    {Q K : Type} [AddCommGroup Q] [Module ℝ Q]
    (X : I → L) (outside : I → Prop)
    (hgen : LieSubalgebra.lieSpan ℝ L (range X) = ⊤)
    (q : L →ₗ[ℝ] Q) (hq : ∀ x y : L, q ⁅x, y⁆ = 0)
    (bq : Basis I ℝ Q) (hX : ∀ i, q (X i) = bq i)
    (b : Basis K ℝ (L ⧸ (mixedWordIdeal X outside hgen).toSubmodule))
    (words : K → FreeMagma I)
    (hwords : ∀ j, (mixedWordIdeal X outside hgen).toSubmodule.mkQ
      (evalBracketWord X (words j)) = b j)
    (i : I) (hi : ¬outside i) : ∃ j, words j = .of i := by
  let J := (mixedWordIdeal X outside hgen).toSubmodule
  let f := (bq.coord i).comp q
  let fQ := J.liftQ f (inside_abelian_coordinate_kills_mixed X outside q hq bq hX i hi)
  by_contra hn
  have hn' : ∀ j, words j ≠ .of i := fun j h => hn ⟨j, h⟩
  have hf : fQ = 0 := b.ext fun j => by
    rw [← hwords j]
    change f (evalBracketWord X (words j)) = 0
    cases hw : words j with
    | of k =>
      have hki : k ≠ i := fun h => hn' j (hw.trans (congrArg FreeMagma.of h))
      simp [f, evalBracketWord, hX, Basis.coord_apply, hki]
    | mul u v => simp [f, evalBracketWord, hq]
  have h := congrArg (fun F : (L ⧸ J) →ₗ[ℝ] ℝ => F (J.mkQ (X i))) hf
  change f (X i) = 0 at h
  simp [f, hX, Basis.coord_apply] at h

theorem positive_inside_quotient_word_counts
    [Fintype I] {Q K : Type} [Fintype K] [AddCommGroup Q] [Module ℝ Q]
    (X : I → L) (outside : I → Prop)
    (hgen : LieSubalgebra.lieSpan ℝ L (range X) = ⊤)
    (q : L →ₗ[ℝ] Q) (hq : ∀ x y : L, q ⁅x, y⁆ = 0)
    (bq : Basis I ℝ Q) (hX : ∀ i, q (X i) = bq i)
    (b : Basis K ℝ (L ⧸ (mixedWordIdeal X outside hgen).toSubmodule))
    (words : K → FreeMagma I)
    (hwords : ∀ j, (mixedWordIdeal X outside hgen).toSubmodule.mkQ
      (evalBracketWord X (words j)) = b j)
    (i : I) (hi : ¬outside i) : 0 < ∑ j, bracketWordCount (words j) i := by
  obtain ⟨j, hj⟩ := mandatory_inside_letter_in_quotient X outside hgen q hq bq hX
    b words hwords i hi
  have hle := Finset.single_le_sum (fun j (_ : j ∈ (Finset.univ : Finset K)) =>
    Nat.zero_le (bracketWordCount (words j) i)) (Finset.mem_univ j)
  rw [hj] at hle
  simp only [bracketWordCount, ite_true, if_true] at hle
  exact lt_of_lt_of_le Nat.zero_lt_one hle

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanConeIdeal
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instDecidableEqConeMixedWords _root_.OAI.PolycyclicRecognition.CartanWordModel.instFintypeConeMixedWords _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The mixed-word ideal contains every outside generalized weight space -/

noncomputable section
namespace PolycyclicRecognition

open Module LieAlgebra LieModule Set

namespace CartanWordModel

variable {L : Type} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {H : LieSubalgebra ℝ L} [H.IsCartanSubalgebra] (M : CartanWordModel H)

set_option maxHeartbeats 1000000 in
/-- For a pointed positive cone, the zero generalized weight space is
removed in the quotient. Here the allowed set omits the cone vertex. -/
theorem zero_genWeightSpace_le_coneWordIdeal
    (C : Set (H →ₗ[ℝ] ℝ)) (hadd : ∀ x ∈ C, ∀ y ∈ C, x + y ∈ C)
    (hzero : (0 : H →ₗ[ℝ] ℝ) ∉ C) :
    (genWeightSpace (cartanRootIdeal H) (0 : H → ℝ)).toSubmodule ≤
      (M.coneWordIdeal C).toSubmodule :=
  M.outside_genWeightSpace_le_coneWordIdeal C hadd 0 hzero

set_option maxHeartbeats 1000000 in
/-- In particular the Cartan/root intersection is killed by the cone
quotient, so the later action can descend through the factorization of G. -/
theorem cartan_intersection_mem_coneWordIdeal
    (C : Set (H →ₗ[ℝ] ℝ)) (hadd : ∀ x ∈ C, ∀ y ∈ C, x + y ∈ C)
    (hzero : (0 : H →ₗ[ℝ] ℝ) ∉ C) (v : cartanRootIdeal H) (hv : (v : L) ∈ H) :
    v ∈ M.coneWordIdeal C := by
  let ι : (cartanRootIdeal H) →ₗ⁅ℝ,H⁆ L := ((cartanRootIdeal H).restr H).incl
  have hroot : v ∈ genWeightSpace (cartanRootIdeal H) (0 : H → ℝ) := by
    rw [← comap_genWeightSpace_eq_of_injective (f := ι)
      ((cartanRootIdeal H).restr H).injective_incl]
    exact toLieSubmodule_le_rootSpace_zero ℝ L H hv
  exact M.zero_genWeightSpace_le_coneWordIdeal C hadd hzero hroot

end CartanWordModel
end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanConeTrace
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instDecidableEqConeMixedWords _root_.OAI.PolycyclicRecognition.CartanWordModel.instFintypeConeMixedWords _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The positive trace character of a Cartan cone quotient

The coefficients come from an actual pure-word basis of the quotient.
The abelianization coordinates prove strict positivity for every inside
generator, including the extremal generators of a ray or a two-ray cone.
-/

noncomputable section
namespace PolycyclicRecognition

open Module LieAlgebra LieModule Set
open scoped BigOperators

set_option maxHeartbeats 1000000 in
theorem bracketWordCount_eq_zero_of_pure
    {I : Type} [DecidableEq I] (outside : I → Prop)
    {w : FreeMagma I} (hw : ¬IsMixedWord outside w) {i : I} (hi : outside i) :
    bracketWordCount w i = 0 := by
  induction w using FreeMagma.rec with
  | of j =>
    have hij : i ≠ j := fun h => hw (h ▸ hi)
    simp [bracketWordCount, hij]
  | mul u v hu hv =>
    exact Nat.add_eq_zero_iff.mpr ⟨hu (fun h => hw (Or.inl h)), hv (fun h => hw (Or.inr h))⟩

namespace CartanWordModel

variable {L : Type} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {H : LieSubalgebra ℝ L} [H.IsCartanSubalgebra] (M : CartanWordModel H)

set_option maxHeartbeats 1000000 in
/-- Trace on a pure-word quotient basis is the sum of the actual word
weights; generalized eigenspaces retain the nilpotent parts of the action. -/
theorem trace_cone_word_basis
    (C : Set (H →ₗ[ℝ] ℝ)) (hadd : ∀ x ∈ C, ∀ y ∈ C, x + y ∈ C)
    {J : Type} [Fintype J]
    (b : Basis J ℝ ((cartanRootIdeal H) ⧸ M.coneCartanSubmodule C hadd))
    (words : J → FreeMagma (Fin M.letterCount))
    (hwords : ∀ j, (M.coneWordIdeal C).toSubmodule.mkQ
      (evalBracketWord M.letter (words j)) = b j) (h : H) :
    LinearMap.trace ℝ ((cartanRootIdeal H) ⧸ M.coneCartanSubmodule C hadd)
      (toEnd ℝ H _ h) =
        ∑ i, ((∑ j, bracketWordCount (words j) i : ℕ) : ℝ) * M.weight i h := by
  let Q := (cartanRootIdeal H) ⧸ M.coneCartanSubmodule C hadd
  let q := LieSubmodule.Quotient.mk' (M.coneCartanSubmodule C hadd)
  let α := fun i => (M.weight i : H →ₗ[ℝ] ℝ)
  have hm (j : J) : b j ∈ genWeightSpace Q (bracketWordWeight α (words j)) := by
    rw [← hwords j]
    exact map_genWeightSpace_le q ⟨_,
      cartan_word_mem_genWeight H M.letter M.weight M.letter_root (words j), rfl⟩
  let ψ : J → Weight ℝ H Q := fun j =>
    { toFun := bracketWordWeight α (words j)
      genWeightSpace_ne_bot' := by
        intro hz
        have hh := hm j
        rw [hz] at hh
        exact b.ne_zero j hh }
  have ht := trace_eq_sum_of_generalizedWeight_basis b ψ hm h
  change LinearMap.trace ℝ Q (toEnd ℝ H Q h) =
    ∑ j, bracketWordWeight α (words j) h at ht
  rw [ht]
  simp_rw [bracketWordWeight_eq_count, Nat.cast_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  rfl

set_option maxHeartbeats 1000000 in
/-- The quotient trace is an integral combination of inside generator
weights, with strictly positive coefficients for every inside generator. -/
theorem exists_positive_cone_trace_coefficients
    (C : Set (H →ₗ[ℝ] ℝ)) (hadd : ∀ x ∈ C, ∀ y ∈ C, x + y ∈ C) :
    ∃ c : Fin M.letterCount → ℕ,
      (∀ i, (M.weight i : H →ₗ[ℝ] ℝ) ∉ C → c i = 0) ∧
      (∀ i, (M.weight i : H →ₗ[ℝ] ℝ) ∈ C → 0 < c i) ∧
      ∀ h : H, LinearMap.trace ℝ
        ((cartanRootIdeal H) ⧸ M.coneCartanSubmodule C hadd) (toEnd ℝ H _ h) =
          ∑ i, (c i : ℝ) * M.weight i h := by
  classical
  let outside := fun i => (M.weight i : H →ₗ[ℝ] ℝ) ∉ C
  obtain ⟨b, words, hpure, hwords⟩ :=
    exists_pure_quotient_word_basis M.letter outside M.generates
  refine ⟨fun i => ∑ j, bracketWordCount (words j) i, ?_, ?_, ?_⟩
  · intro i hi
    exact Finset.sum_eq_zero (fun j _ => bracketWordCount_eq_zero_of_pure outside (hpure j) hi)
  · intro i hi
    let N := (lowerCentralSeries ℝ (cartanRootIdeal H) (cartanRootIdeal H) 1).toSubmodule
    apply positive_inside_quotient_word_counts M.letter outside M.generates N.mkQ ?_
      M.abelianBasis M.letter_quotient b words hwords i (not_not.mpr hi)
    intro x y
    apply (Submodule.Quotient.mk_eq_zero N).mpr
    change ⁅x, y⁆ ∈ lowerCentralSeries ℝ (cartanRootIdeal H) (cartanRootIdeal H) (0 + 1)
    rw [lowerCentralSeries_succ, lowerCentralSeries_zero]
    exact LieSubmodule.lie_mem_lie (LieSubmodule.mem_top x) (LieSubmodule.mem_top y)
  · exact M.trace_cone_word_basis C hadd b words hwords

end CartanWordModel
end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_ConeQuotientJacobian
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instDecidableEqConeMixedWords _root_.OAI.PolycyclicRecognition.CartanWordModel.instFintypeConeMixedWords _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.stationaryL2SMulComm _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.CartanFactorModel.heightRay_zero _root_.OAI.PolycyclicRecognition.CartanFactorModel.realScaleProfile_apply _root_.OAI.PolycyclicRecognition.CartanFactorModel.sampledProbeProfile_apply _root_.OAI.PolycyclicRecognition.bracketWordDifferential_mul _root_.OAI.PolycyclicRecognition.cartanWeightDerivation_apply_root _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.nilshadowWeightDerivation_symm _root_.OAI.PolycyclicRecognition.nilshadowWeightOperator_symm _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The Jacobian of the induced Cartan action on a cone quotient -/

noncomputable section
namespace PolycyclicRecognition

open Module LieAlgebra LieModule Set
open scoped BigOperators

/-- A quotient of a unipotent operator is unipotent. This supplies the
determinant-one part of the quotient action without diagonalizability. -/
theorem quotient_unipotent
    {V : Type} [AddCommGroup V] [Module ℝ V]
    (J : Submodule ℝ V) (F : V →ₗ[ℝ] V) (hF : ∀ x ∈ J, F x ∈ J)
    (hu : _root_.IsNilpotent (F - 1)) :
    _root_.IsNilpotent (J.mapQ J F hF - 1) := by
  have hsub : ∀ x ∈ J, (F - 1) x ∈ J := fun x hx => J.sub_mem (hF x hx) hx
  have he : J.mapQ J F hF - 1 = J.mapQ J (F - 1) hsub := by
    apply LinearMap.ext
    intro x
    obtain ⟨v, rfl⟩ := J.mkQ_surjective x
    simp
  obtain ⟨k, hk⟩ := hu
  refine ⟨k, ?_⟩
  rw [he, ← J.mapQ_pow hsub]
  apply LinearMap.ext
  intro x
  obtain ⟨v, rfl⟩ := J.mkQ_surjective x
  simp [hk]

namespace CartanWordModel

variable {L : Type} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {H : LieSubalgebra ℝ L} [H.IsCartanSubalgebra] (M : CartanWordModel H)
  {n : ℕ} (T : TriangularAdjoint L n)

/-- The quotient scalar Jacobian is the exponential of the total retained
word weight. -/
theorem det_cone_dilation_word_basis
    (C : Set (H →ₗ[ℝ] ℝ)) (h : H) {J : Type} [Fintype J]
    (b : Basis J ℝ ((cartanRootIdeal H) ⧸ M.coneWordIdeal C))
    (words : J → FreeMagma (Fin M.letterCount))
    (hb : ∀ j, (M.coneWordIdeal C).toSubmodule.mkQ (evalBracketWord M.letter (words j)) = b j) :
    LinearMap.det ((M.coneWordIdeal C).toSubmodule.mapQ (M.coneWordIdeal C).toSubmodule
      (cartanIdealWeightDilation T H h).toLinearEquiv.toLinearMap
      (M.coneWordIdeal_dilation_mem T C h)) =
        Real.exp (∑ j, bracketWordExponent (fun i => M.weight i h) (words j)) := by
  classical
  let I := (M.coneWordIdeal C).toSubmodule
  let F := I.mapQ I (cartanIdealWeightDilation T H h).toLinearEquiv.toLinearMap
    (M.coneWordIdeal_dilation_mem T C h)
  let w := fun j => Real.exp (bracketWordExponent (fun i => M.weight i h) (words j))
  have hF (j) : F (b j) = w j • b j := by
    rw [← hb j]
    change I.mkQ (cartanIdealWeightDilation T H h (evalBracketWord M.letter (words j))) = _
    rw [M.idealWeightDilation_word T h, map_smul]
  have hm : LinearMap.toMatrix b b F = Matrix.diagonal w := by
    ext i j
    simp only [LinearMap.toMatrix_apply, hF, map_smul, Finsupp.smul_apply,
      Basis.repr_self, Finsupp.single_apply, smul_eq_mul, Matrix.diagonal_apply]
    split_ifs <;> simp_all
  rw [← LinearMap.det_toMatrix b, hm, Matrix.det_diagonal, Real.exp_sum]

theorem det_cone_residual_eq_one
    (C : Set (H →ₗ[ℝ] ℝ)) (hadd : ∀ x ∈ C, ∀ y ∈ C, x + y ∈ C) (h : H) :
    LinearMap.det ((M.coneWordIdeal C).toSubmodule.mapQ (M.coneWordIdeal C).toSubmodule
      (cartanIdealResidualAutomorphism T H h).toLinearEquiv.toLinearMap
      (M.coneWordIdeal_residual_mem T C hadd h)) = 1 := by
  apply det_eq_one_of_sub_one_nilpotent
  apply quotient_unipotent
  let : Module ℚ (cartanRootIdeal H) := Module.compHom _ (algebraMap ℚ ℝ)
  have hn : _root_.IsNilpotent (cartanIdealResidualDerivation T H h).toLinearMap :=
    ⟨finrank ℝ L, cartanIdealResidualDerivation_pow_eq_zero T H h⟩
  exact hn.isNilpotent_exp_sub_one

/-- The full induced action has Jacobian equal to the exponential of its
actual quotient trace, including all nonsemisimple corrections. -/
theorem det_cone_adjoint_eq_exp_trace
    (C : Set (H →ₗ[ℝ] ℝ)) (hadd : ∀ x ∈ C, ∀ y ∈ C, x + y ∈ C) (h : H) :
    LinearMap.det ((M.coneWordIdeal C).toSubmodule.mapQ (M.coneWordIdeal C).toSubmodule
      (cartanIdealAdjointAutomorphism T H h).toLinearEquiv.toLinearMap
      (M.coneWordIdeal_adjoint_mem T C hadd h)) =
    Real.exp (LinearMap.trace ℝ ((cartanRootIdeal H) ⧸ M.coneCartanSubmodule C hadd)
      (toEnd ℝ H _ h)) := by
  classical
  let I := (M.coneWordIdeal C).toSubmodule
  have heq : I.mapQ I (cartanIdealAdjointAutomorphism T H h).toLinearEquiv.toLinearMap
      (M.coneWordIdeal_adjoint_mem T C hadd h) =
      (I.mapQ I (cartanIdealWeightDilation T H h).toLinearEquiv.toLinearMap
        (M.coneWordIdeal_dilation_mem T C h)).comp
      (I.mapQ I (cartanIdealResidualAutomorphism T H h).toLinearEquiv.toLinearMap
        (M.coneWordIdeal_residual_mem T C hadd h)) := by
    apply LinearMap.ext
    intro x
    obtain ⟨v, rfl⟩ := I.mkQ_surjective x
    rfl
  obtain ⟨b, words, _hpure, hb⟩ := exists_pure_quotient_word_basis M.letter
    (fun i => (M.weight i : H →ₗ[ℝ] ℝ) ∉ C) M.generates
  rw [heq, LinearMap.det_comp, M.det_cone_residual_eq_one T C hadd h, mul_one,
    M.det_cone_dilation_word_basis T C h b words hb]
  apply congrArg Real.exp
  rw [M.trace_cone_word_basis C hadd b words hb h]
  simp only [bracketWordExponent, Nat.cast_sum, Finset.sum_mul]
  rw [Finset.sum_comm]

end CartanWordModel
end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_ExponentialHaarMultiplier
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_countable _root_.OAI.PolycyclicRecognition.finitelyGeneratedSubgroupIndex_countable _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The exact Haar multiplier of an exponential-coordinate automorphism -/

noncomputable section
namespace PolycyclicRecognition

open Module MeasureTheory
open scoped Manifold

variable {L : Type} [LieRing L] [LieAlgebra ℝ L]
  {E G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace G] [ChartedSpace E G] [Group G]
  [LieGroup (𝓘(ℝ, E)) ⊤ G] [MeasurableSpace G] [BorelSpace G]
  (e : L ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, E)) G)
  (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G) (hbij : Function.Bijective Exp)
  (chart : GroupLieAlgebra (𝓘(ℝ, E)) G ≃ₜ G) (hchart : ∀ x, chart x = Exp x)
  {n : ℕ} (b : Basis (Fin n) ℝ L)

include hchart in
/-- The pushforward multiplier is the reciprocal absolute determinant.
Consequently the multiplier of image volumes is the absolute determinant. -/
theorem exponentialConjugate_map_measure (F : L ≃ₗ⁅ℝ⁆ L) :
    Measure.map (exponentialConjugate e Exp hbij F)
      (Measure.map ((Exp ∘ e) ∘ b.equivFun.symm) volume) =
    ENNReal.ofReal |(LinearMap.det F.toLinearEquiv.toLinearMap)⁻¹| •
      Measure.map ((Exp ∘ e) ∘ b.equivFun.symm) volume := by
  let A : (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ) :=
    (b.equivFun.symm.trans F.toLinearEquiv).trans b.equivFun
  let f : (Fin n → ℝ) ≃ₜ G :=
    (b.equivFun.symm.trans e.toLinearEquiv).toContinuousLinearEquiv.toHomeomorph.trans chart
  have hf : (f : (Fin n → ℝ) → G) = (Exp ∘ e) ∘ b.equivFun.symm := by
    funext t
    exact hchart _
  have hAdet : LinearMap.det A.toLinearMap = LinearMap.det F.toLinearEquiv.toLinearMap := by
    have hd := congrArg Units.val (LinearEquiv.det_conj F.toLinearEquiv b.equivFun)
    simpa only [LinearEquiv.coe_det] using hd
  have hA : Measure.map A volume = ENNReal.ofReal |(LinearMap.det A.toLinearMap)⁻¹| • volume :=
    Real.map_linearMap_volume_pi_eq_smul_volume_pi A.isUnit_det'.ne_zero
  have hsem : Function.Semiconj f A (exponentialConjugate e Exp hbij F) := by
    intro t
    rw [hf]
    change Exp (e (b.equivFun.symm (A t))) = _
    simp only [A, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
    exact (exponentialConjugate_apply_exp e Exp hbij F (b.equivFun.symm t)).symm
  have heq : (exponentialConjugate e Exp hbij F : G → G) = f ∘ A ∘ f.symm := by
    funext g
    obtain ⟨t, rfl⟩ := f.surjective g
    simpa only [Function.comp_apply, f.symm_apply_apply] using (hsem t).symm
  have hmeas : Measurable (exponentialConjugate e Exp hbij F) := by
    rw [heq]
    exact f.continuous.measurable.comp
      (A.toContinuousLinearEquiv.continuous.measurable.comp f.symm.continuous.measurable)
  have hcomp : (exponentialConjugate e Exp hbij F) ∘ f = f ∘ A :=
    funext (fun t => (hsem t).symm)
  have hAmeas : Measurable (A : (Fin n → ℝ) → (Fin n → ℝ)) :=
    A.toContinuousLinearEquiv.continuous.measurable
  rw [← hf, Measure.map_map hmeas f.continuous.measurable, hcomp,
    ← Measure.map_map f.continuous.measurable hAmeas,
    hA, Measure.map_smul, hAdet]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_ConeQuotientAutomorphism
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instDecidableEqConeMixedWords _root_.OAI.PolycyclicRecognition.CartanWordModel.instFintypeConeMixedWords _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The quotient Lie automorphism and its exponential Haar multiplier -/

noncomputable section
namespace PolycyclicRecognition

open Module LieAlgebra LieModule Set MeasureTheory
open scoped Manifold

namespace CartanWordModel

variable {L : Type} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {H : LieSubalgebra ℝ L} [H.IsCartanSubalgebra] (M : CartanWordModel H)
  {n : ℕ} (T : TriangularAdjoint L n)

theorem det_coneAdjointAutomorphism
    (C : Set (H →ₗ[ℝ] ℝ)) (hadd : ∀ x ∈ C, ∀ y ∈ C, x + y ∈ C) (h : H) :
    LinearMap.det (M.coneAdjointAutomorphism T C hadd h).toLinearEquiv.toLinearMap =
      Real.exp (LinearMap.trace ℝ ((cartanRootIdeal H) ⧸ M.coneCartanSubmodule C hadd)
        (toEnd ℝ H _ h)) :=
  M.det_cone_adjoint_eq_exp_trace T C hadd h

end CartanWordModel
end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_FactorQuotientAction
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The quotient action descends through overlapping group factors

The factors need not form a direct or injective semidirect decomposition.
The only overlap condition is that the nilpotent quotient kills it.
-/

noncomputable section
namespace PolycyclicRecognition

variable {N D Q G : Type} [Group N] [Group D] [Group Q] [Group G]

/-- Killing the overlap makes the affine action well-defined on the ambient
group, even when multiplication of the two factors is not injective. -/
theorem exists_descended_factor_quotient_action
    (ι : N →* G) (κ : D →* G) (hι : Function.Injective ι)
    (a : D →* MulAut N)
    (hconj : ∀ d n, ι (a d n) = κ d * ι n * (κ d)⁻¹)
    (hsurj : Function.Surjective (fun p : N × D => ι p.1 * κ p.2))
    (π : N →* Q) (s : Q → N) (hs : Function.RightInverse s π)
    (ha : ∀ d n, a d n ∈ π.ker ↔ n ∈ π.ker)
    (hoverlap : ∀ n d, ι n = κ d → π n = 1) :
    ∃ act : G →* Equiv.Perm Q,
      (∀ n d q, act (ι n * κ d) q = π n * descendQuotientAction π s hs a ha d q) ∧
      (∀ g, act g 1 = 1 ↔ ∃ n d, n ∈ π.ker ∧ ι n * κ d = g) ∧
      ∀ g h, act (g * h) 1 = act g (act h 1) := by
  have hcompat (d) : ι.comp (a d).toMonoidHom = (MulAut.conj (κ d)).toMonoidHom.comp ι := by
    ext n
    exact hconj d n
  let σ : (N ⋊[a] D) →* G := SemidirectProduct.lift ι κ hcompat
  have hσ : Function.Surjective σ := by
    intro g
    obtain ⟨⟨n, d⟩, h⟩ := hsurj g
    exact ⟨⟨n, d⟩, h⟩
  let ρ := factorQuotientAction π s hs a ha
  have hker : σ.ker ≤ ρ.ker := by
    intro p hp
    have hp' : ι p.left * κ p.right = 1 := hp
    have hn : ι p.left = κ (p.right⁻¹) := by
      simpa only [mul_assoc, mul_inv_cancel, mul_one, one_mul, map_inv] using
        congrArg (fun x => x * (κ p.right)⁻¹) hp'
    have hπn : π p.left = 1 := hoverlap _ _ hn
    have hk : κ p.right = ι (p.left⁻¹) := by
      simpa only [map_inv, inv_mul_cancel_left, mul_one] using
        congrArg (fun x => (ι p.left)⁻¹ * x) hp'
    have had (x : N) : a p.right x = p.left⁻¹ * x * p.left := by
      apply hι
      rw [hconj, hk]
      simp only [map_mul, map_inv, inv_inv]
    apply Equiv.ext
    intro q
    obtain ⟨x, rfl⟩ := hs.surjective q
    change π p.left * descendQuotientAction π s hs a ha p.right (π x) = π x
    rw [descendQuotientAction_project, had]
    simp only [map_mul, map_inv, hπn, inv_one, one_mul, mul_one]
  let act := σ.liftOfSurjective hσ ⟨ρ, hker⟩
  have hact (p : N ⋊[a] D) : act (σ p) = ρ p :=
    σ.liftOfRightInverse_comp_apply _ _ _ p
  have hformula (n : N) (d : D) (q : Q) :
      act (ι n * κ d) q = π n * descendQuotientAction π s hs a ha d q := by
    exact congrArg (fun f : Equiv.Perm Q => f q) (hact ⟨n, d⟩)
  refine ⟨act, hformula, ?_, ?_⟩
  · intro g
    constructor
    · intro hg
      obtain ⟨⟨n, d⟩, he⟩ := hsurj g
      refine ⟨n, d, ?_, he⟩
      rw [← he, hformula, map_one, mul_one] at hg
      exact hg
    · rintro ⟨n, d, hn, rfl⟩
      rw [hformula, map_one, mul_one]
      exact hn
  · intro g h
    exact congrArg (fun f : Equiv.Perm Q => f 1) (act.map_mul g h)

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

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_ExponentialHaarImage
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Image volumes under exponential-coordinate automorphisms -/

noncomputable section
namespace PolycyclicRecognition

open Module MeasureTheory
open scoped Manifold

variable {L : Type} [LieRing L] [LieAlgebra ℝ L]
  {E G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace G] [ChartedSpace E G] [Group G]
  [LieGroup (𝓘(ℝ, E)) ⊤ G] [MeasurableSpace G] [BorelSpace G]
  (e : L ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, E)) G)
  (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G) (hbij : Function.Bijective Exp)
  (chart : GroupLieAlgebra (𝓘(ℝ, E)) G ≃ₜ G) (hchart : ∀ x, chart x = Exp x)
  {n : ℕ} (b : Basis (Fin n) ℝ L)

include hchart in
/-- A positive exponential determinant is the image-volume multiplier.
This identity holds for arbitrary sets, using the measurable embedding. -/
theorem exponentialConjugate_image_measure
    (F : L ≃ₗ⁅ℝ⁆ L) (d : ℝ)
    (hd : LinearMap.det F.toLinearEquiv.toLinearMap = Real.exp d) (S : Set G) :
    (Measure.map ((Exp ∘ e) ∘ b.equivFun.symm) volume)
      (exponentialConjugate e Exp hbij F '' S) =
    ENNReal.ofReal (Real.exp d) *
      (Measure.map ((Exp ∘ e) ∘ b.equivFun.symm) volume) S := by
  let A : (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ) :=
    (b.equivFun.symm.trans F.toLinearEquiv).trans b.equivFun
  let f : (Fin n → ℝ) ≃ₜ G :=
    (b.equivFun.symm.trans e.toLinearEquiv).toContinuousLinearEquiv.toHomeomorph.trans chart
  let g : G ≃ₜ G := (f.symm.trans A.toContinuousLinearEquiv.toHomeomorph).trans f
  let μ := Measure.map ((Exp ∘ e) ∘ b.equivFun.symm) volume
  have hf : (f : (Fin n → ℝ) → G) = (Exp ∘ e) ∘ b.equivFun.symm := by
    funext t
    exact hchart _
  have hg : (g : G → G) = exponentialConjugate e Exp hbij F := by
    funext x
    obtain ⟨v, rfl⟩ := f.surjective x
    change f (A (f.symm (f v))) = _
    rw [f.symm_apply_apply, hf]
    simp only [A, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply, Function.comp_apply]
    change Exp (e (F (b.equivFun.symm v))) = _
    exact (exponentialConjugate_apply_exp e Exp hbij F (b.equivFun.symm v)).symm
  have hm := exponentialConjugate_map_measure e Exp hbij chart hchart b F
  rw [← hg, hd, ← Real.exp_neg, abs_of_pos (Real.exp_pos _)] at hm
  have hv := congrArg (fun ν : Measure G => ν (g '' S)) hm
  rw [g.measurableEmbedding.map_apply, Set.preimage_image_eq _ g.injective,
    Measure.smul_apply, smul_eq_mul] at hv
  have hmul : ENNReal.ofReal (Real.exp d) * ENNReal.ofReal (Real.exp (-d)) = 1 := by
    rw [← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add, add_neg_cancel,
      Real.exp_zero, ENNReal.ofReal_one]
  rw [← hg]
  change μ (g '' S) = ENNReal.ofReal (Real.exp d) * μ S
  calc
    μ (g '' S) = 1 * μ (g '' S) := (one_mul _).symm
    _ = (ENNReal.ofReal (Real.exp d) * ENNReal.ofReal (Real.exp (-d))) * μ (g '' S) := by rw [hmul]
    _ = ENNReal.ofReal (Real.exp d) * μ S := by rw [mul_assoc, ← hv]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_ConeQuotientHaar
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instDecidableEqConeMixedWords _root_.OAI.PolycyclicRecognition.CartanWordModel.instFintypeConeMixedWords _root_.OAI.PolycyclicRecognition.CartanWordModel.instNonemptyConeIdealBases _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The exact positive character of quotient Haar measure -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule MeasureTheory
open scoped Manifold

variable {L : Type} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {H : LieSubalgebra ℝ L} [H.IsCartanSubalgebra] (M : CartanWordModel H)
  {n : ℕ} (T : TriangularAdjoint L n)

/-- A single Haar measure has the quotient Jacobian character for every
Cartan parameter. The character coefficients are positive exactly on the
retained generators. -/
theorem exists_cone_haar_multiplier
    (C : Set (H →ₗ[ℝ] ℝ)) (hadd : ∀ x ∈ C, ∀ y ∈ C, x + y ∈ C)
    (Q : NilpotentLieModel ((cartanRootIdeal H) ⧸ M.coneWordIdeal C))
    (ExpQ : GroupLieAlgebra (𝓘(ℝ, Q.modelSpace)) Q.carrier → Q.carrier)
    (hExpQ : IsGroupExponential ExpQ) (hbij : Function.Bijective ExpQ)
    (haar : NilpotentExponentialHaarInput Q.modelSpace Q.carrier) :
    ∃ (μ : Measure Q.carrier) (c : Fin M.letterCount → ℕ), μ.IsHaarMeasure ∧
      (∀ i, (M.weight i : H →ₗ[ℝ] ℝ) ∉ C → c i = 0) ∧
      (∀ i, (M.weight i : H →ₗ[ℝ] ℝ) ∈ C → 0 < c i) ∧
      (∀ h : H, Measure.map
        (exponentialConjugate Q.equiv ExpQ hbij (M.coneAdjointAutomorphism T C hadd h)) μ =
        ENNReal.ofReal (Real.exp (-(∑ i, (c i : ℝ) * M.weight i h))) • μ) ∧
      ∀ (h : H) (S : Set Q.carrier),
        μ (exponentialConjugate Q.equiv ExpQ hbij (M.coneAdjointAutomorphism T C hadd h) '' S) =
        ENNReal.ofReal (Real.exp (∑ i, (c i : ℝ) * M.weight i h)) * μ S := by
  obtain ⟨⟨chart, hchart⟩, hhaar⟩ :=
    haar.2 ExpQ hExpQ (Q.tangent_nilpotent (M.coneQuotient_nilpotent C))
  let b := Module.finBasis ℝ ((cartanRootIdeal H) ⧸ M.coneWordIdeal C)
  let μ := Measure.map ((ExpQ ∘ Q.equiv) ∘ b.equivFun.symm) volume
  obtain ⟨c, hout, hin, htrace⟩ := M.exists_positive_cone_trace_coefficients C hadd
  refine ⟨μ, c, ?_, hout, hin, ?_, ?_⟩
  · have hf : (ExpQ ∘ Q.equiv) ∘ b.equivFun.symm =
        ExpQ ∘ (b.map Q.equiv.toLinearEquiv).equivFun.symm := by
      funext x
      rw [Basis.map_equivFun]
      rfl
    dsimp only [μ]
    rw [hf]
    exact hhaar _ (b.map Q.equiv.toLinearEquiv)
  · intro h
    have hd := M.det_coneAdjointAutomorphism T C hadd h
    rw [htrace] at hd
    have hm := exponentialConjugate_map_measure Q.equiv ExpQ hbij chart hchart b
      (M.coneAdjointAutomorphism T C hadd h)
    rw [hd, ← Real.exp_neg, abs_of_pos (Real.exp_pos _)] at hm
    exact hm
  · intro h S
    have hd := M.det_coneAdjointAutomorphism T C hadd h
    rw [htrace] at hd
    exact exponentialConjugate_image_measure Q.equiv ExpQ hbij chart hchart b
      (M.coneAdjointAutomorphism T C hadd h) _ hd S

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanConeAction
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instDecidableEqConeMixedWords _root_.OAI.PolycyclicRecognition.CartanWordModel.instFintypeConeMixedWords _root_.OAI.PolycyclicRecognition.CartanWordModel.instNonemptyConeIdealBases _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The cone quotient action for the actual overlapping Cartan factors -/

noncomputable section
namespace PolycyclicRecognition

open Module LieAlgebra LieModule Set
open scoped Manifold

namespace CartanWordModel

variable {L : Type} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {H : LieSubalgebra ℝ L} [H.IsCartanSubalgebra] (M : CartanWordModel H)
  {a : ℕ} (T : TriangularAdjoint L a)
  {EN N Q : Type} [NormedAddCommGroup EN] [NormedSpace ℝ EN]
  [FiniteDimensional ℝ EN] [TopologicalSpace N] [ChartedSpace EN N] [Group N]
  [LieGroup (𝓘(ℝ, EN)) ⊤ N] [T2Space N] [Group Q]
  (eN : cartanRootIdeal H ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, EN)) N)
  (ExpN : GroupLieAlgebra (𝓘(ℝ, EN)) N → N)
  (hExpN : IsGroupExponential ExpN) (hbij : Function.Bijective ExpN)
  (dynkin : NilpotentDynkinExpansionInput EN N)

set_option maxHeartbeats 1000000 in
omit M T hExpN dynkin [FiniteDimensional ℝ L] [T2Space N] in
include hbij in
/-- In exponential coordinates the actual quotient kernel is exactly the
given linear ideal. -/
theorem mem_kernel_exp_iff
    (I : LieIdeal ℝ (cartanRootIdeal H)) (π : N →* Q)
    (hker : (π.ker : Set N) = ExpN '' (eN '' (I : Set (cartanRootIdeal H))))
    (v : cartanRootIdeal H) : ExpN (eN v) ∈ π.ker ↔ v ∈ I := by
  change ExpN (eN v) ∈ (π.ker : Set N) ↔ v ∈ I
  rw [hker]
  constructor
  · rintro ⟨_, ⟨w, hw, rfl⟩, he⟩
    exact eN.injective (hbij.injective he) ▸ hw
  · intro hv
    exact ⟨eN v, ⟨v, hv, rfl⟩, rfl⟩

set_option maxHeartbeats 1000000 in
/-- The genuine adjoint group automorphism preserves the actual quotient
kernel. No extra invariance hypothesis about the group is required. -/
theorem cone_kernel_adjoint_invariant
    (C : Set (H →ₗ[ℝ] ℝ)) (hadd : ∀ x ∈ C, ∀ y ∈ C, x + y ∈ C)
    (π : N →* Q)
    (hker : (π.ker : Set N) = ExpN '' (eN '' (M.coneWordIdeal C : Set (cartanRootIdeal H))))
    (h : H) (g : N) :
    M.adjointGroupAutomorphism T eN ExpN hExpN hbij dynkin h g ∈ π.ker ↔ g ∈ π.ker := by
  obtain ⟨v, rfl⟩ := (hbij.comp eN.bijective).surjective g
  change integrateNilpotentLieEquiv eN ExpN hbij dynkin hExpN M.bound_zero
    (cartanIdealAdjointAutomorphism T H h) (ExpN (eN v)) ∈ π.ker ↔ _
  rw [integrateNilpotentLieEquiv_apply_exp]
  change ExpN (eN (cartanIdealAdjointAutomorphism T H h v)) ∈ π.ker ↔
    ExpN (eN v) ∈ π.ker
  rw [mem_kernel_exp_iff eN ExpN hbij (M.coneWordIdeal C) π hker,
    mem_kernel_exp_iff eN ExpN hbij (M.coneWordIdeal C) π hker]
  exact M.coneWordIdeal_adjoint_mem_iff T C hadd h v

end CartanWordModel

section ActualFactors

variable {EG G Q : Type} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [Group Q]
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {ExpG : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H ExpG)

set_option maxHeartbeats 1000000 in
/-- The already proved exact overlap of the actual factors is killed by
the cone quotient, because its logarithm is in the zero weight space. -/
theorem cartan_factor_overlap_killed
    (C : Set (H →ₗ[ℝ] ℝ)) (hadd : ∀ x ∈ C, ∀ y ∈ C, x + y ∈ C)
    (hzero : (0 : H →ₗ[ℝ] ℝ) ∉ C)
    (π : F.N.carrier →* Q)
    (hπ : ∀ v : cartanRootIdeal H,
      π (F.ExpN (F.N.equiv v)) = 1 ↔ v ∈ M.coneWordIdeal C)
    (n : F.N.carrier) (d : F.D.carrier) (he : F.inclusionN n = F.inclusionD d) :
    π n = 1 := by
  have hg : F.inclusionN n ∈ Set.range F.inclusionN ∩ Set.range F.inclusionD :=
    ⟨⟨n, rfl⟩, ⟨d, he.symm⟩⟩
  rw [F.overlap] at hg
  obtain ⟨v, ⟨hvN, hvH⟩, hv⟩ := hg
  let x : cartanRootIdeal H := ⟨v, hvN⟩
  have hn : F.ExpN (F.N.equiv x) = n :=
    F.closedN.injective ((F.compatibleN x).trans hv)
  rw [← hn]
  exact (hπ x).mpr (M.cartan_intersection_mem_coneWordIdeal C hadd hzero x hvH)

variable {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {A : Type} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

attribute [local instance 100] LieRing.ofAssociativeRing

set_option maxHeartbeats 1000000 in
include T in
/-- Faithful exponential compatibility identifies the actual factor action
with the adjoint automorphism, so its cone kernel invariance is derived. -/
theorem cartan_factor_cone_kernel_invariant
    (j : GroupLieAlgebra (𝓘(ℝ, EG)) G →ₗ⁅ℝ⁆ A) (ρ : G →* Aˣ)
    (hρ : Function.Injective ρ)
    (hN : ∀ x : cartanRootIdeal H,
      ρ (F.inclusionN (F.ExpN (F.N.equiv x))) = algebraExpUnit (j x))
    (hD : ∀ h : H, ρ (F.inclusionD (F.ExpD (F.D.equiv h))) = algebraExpUnit (j h))
    (hNbij : Function.Bijective F.ExpN) (hDsurj : Function.Surjective F.ExpD)
    (dynkin : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
    (C : Set (H →ₗ[ℝ] ℝ)) (hadd : ∀ x ∈ C, ∀ y ∈ C, x + y ∈ C)
    (π : F.N.carrier →* Q)
    (hker : (π.ker : Set F.N.carrier) =
      F.ExpN '' (F.N.equiv '' (M.coneWordIdeal C : Set (cartanRootIdeal H))))
    (d : F.D.carrier) (n : F.N.carrier) : F.action d n ∈ π.ker ↔ n ∈ π.ker := by
  obtain ⟨h, rfl⟩ := (hDsurj.comp F.D.equiv.surjective) d
  have he : F.action (F.ExpD (F.D.equiv h)) n =
      M.adjointGroupAutomorphism T F.N.equiv F.ExpN F.isExpN hNbij dynkin h n := by
    apply F.closedN.injective
    rw [F.conjugation]
    exact (M.adjointGroupAutomorphism_eq_conjugation T F.N.equiv F.ExpN F.isExpN hNbij
      dynkin j ρ hρ F.inclusionN (fun h => F.inclusionD (F.ExpD (F.D.equiv h))) hN hD h n).symm
  change F.action (F.ExpD (F.D.equiv h)) n ∈ π.ker ↔ n ∈ π.ker
  rw [he]
  exact M.cone_kernel_adjoint_invariant T F.N.equiv F.ExpN F.isExpN hNbij dynkin C hadd π hker h n

end ActualFactors
end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanConeAmbientAction
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instDecidableEqConeMixedWords _root_.OAI.PolycyclicRecognition.CartanWordModel.instFintypeConeMixedWords _root_.OAI.PolycyclicRecognition.CartanWordModel.instNonemptyConeIdealBases _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The ambient action on the actual cone quotient

The algebraic ideal and its integrated kernel determine the action and its
stabilizer. No injective product decomposition of the ambient group is used.
-/

noncomputable section
namespace PolycyclicRecognition

open Module LieAlgebra LieModule Set
open scoped Manifold

variable {EG G Q : Type} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [Group Q]
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {ExpG : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H ExpG)
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {A : Type} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

attribute [local instance 100] LieRing.ofAssociativeRing

set_option maxHeartbeats 1000000 in
include T in
/-- The constructed nilpotent quotient carries the ambient action in the
cone-quotient lemma, with exact equivariance and stabilizer. -/
theorem exists_cartan_cone_ambient_action
    (j : GroupLieAlgebra (𝓘(ℝ, EG)) G →ₗ⁅ℝ⁆ A) (ρ : G →* Aˣ)
    (hρ : Function.Injective ρ)
    (hN : ∀ x : cartanRootIdeal H,
      ρ (F.inclusionN (F.ExpN (F.N.equiv x))) = algebraExpUnit (j x))
    (hD : ∀ h : H, ρ (F.inclusionD (F.ExpD (F.D.equiv h))) = algebraExpUnit (j h))
    (hNbij : Function.Bijective F.ExpN) (hDsurj : Function.Surjective F.ExpD)
    (dynkin : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
    (C : Set (H →ₗ[ℝ] ℝ)) (hadd : ∀ x ∈ C, ∀ y ∈ C, x + y ∈ C)
    (hzero : (0 : H →ₗ[ℝ] ℝ) ∉ C)
    (π : F.N.carrier →* Q) (s : Q → F.N.carrier) (hs : Function.RightInverse s π)
    (hker : (π.ker : Set F.N.carrier) =
      F.ExpN '' (F.N.equiv '' (M.coneWordIdeal C : Set (cartanRootIdeal H)))) :
    ∃ (α : F.D.carrier →* MulAut Q) (act : G →* Equiv.Perm Q),
      (∀ d n, α d (π n) = π (F.action d n)) ∧
      (∀ n d q, act (F.inclusionN n * F.inclusionD d) q = π n * α d q) ∧
      (∀ g, act g 1 = 1 ↔ ∃ n d, n ∈ π.ker ∧ F.inclusionN n * F.inclusionD d = g) ∧
      ∀ g h, act (g * h) 1 = act g (act h 1) := by
  have ha := cartan_factor_cone_kernel_invariant M F T j ρ hρ hN hD hNbij hDsurj
    dynkin C hadd π hker
  have hkill : ∀ n d, F.inclusionN n = F.inclusionD d → π n = 1 := by
    apply cartan_factor_overlap_killed M F C hadd hzero π
    intro v
    exact CartanWordModel.mem_kernel_exp_iff F.N.equiv F.ExpN hNbij (M.coneWordIdeal C) π hker v
  obtain ⟨act, hact, hstab, heq⟩ := exists_descended_factor_quotient_action
    F.inclusionN F.inclusionD F.closedN.injective F.action F.conjugation F.surjective
    π s hs ha hkill
  exact ⟨descendQuotientAction π s hs F.action ha, act,
    descendQuotientAction_project π s hs F.action ha, hact, hstab, heq⟩

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
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanSemidirectWords
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instDecidableEqConeMixedWords _root_.OAI.PolycyclicRecognition.CartanWordModel.instFintypeConeMixedWords _root_.OAI.PolycyclicRecognition.CartanWordModel.instNonemptyConeIdealBases _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
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
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_RayTangentContraction
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instDecidableEqConeMixedWords _root_.OAI.PolycyclicRecognition.CartanWordModel.instFintypeConeMixedWords _root_.OAI.PolycyclicRecognition.CartanWordModel.instNonemptyConeIdealBases _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
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
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_ConeHeightMultiplier
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instDecidableEqConeMixedWords _root_.OAI.PolycyclicRecognition.CartanWordModel.instFintypeConeMixedWords _root_.OAI.PolycyclicRecognition.CartanWordModel.instNonemptyConeIdealBases _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The quotient Haar character in canonical height coordinates -/

noncomputable section
namespace PolycyclicRecognition

open Module LieAlgebra LieModule MeasureTheory Set
open scoped Manifold BigOperators

namespace CartanWordModel

variable {L W : Type} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {H : LieSubalgebra ℝ L} [H.IsCartanSubalgebra] (M : CartanWordModel H)
  {a : ℕ} (T : TriangularAdjoint L a)
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)

/-- The positive trace coefficients give the exact Haar multiplier as a
linear functional on the already chosen canonical height space. -/
theorem exists_cone_haar_height_multiplier
    (C : Set (H →ₗ[ℝ] ℝ)) (hadd : ∀ x ∈ C, ∀ y ∈ C, x + y ∈ C)
    (Q : NilpotentLieModel ((cartanRootIdeal H) ⧸ M.coneWordIdeal C))
    (ExpQ : GroupLieAlgebra (𝓘(ℝ, Q.modelSpace)) Q.carrier → Q.carrier)
    (hExpQ : IsGroupExponential ExpQ) (hbij : Function.Bijective ExpQ)
    (haar : NilpotentExponentialHaarInput Q.modelSpace Q.carrier) :
    ∃ (μ : Measure Q.carrier) (ell : W →ₗ[ℝ] ℝ) (c : Fin M.letterCount → ℕ),
      μ.IsHaarMeasure ∧
      (∀ i, (M.weight i : H →ₗ[ℝ] ℝ) ∉ C → c i = 0) ∧
      (∀ i, (M.weight i : H →ₗ[ℝ] ℝ) ∈ C → 0 < c i) ∧
      ell = (∑ i, (c i : ℝ) • cartanHeightWeight T H (M.weight i)).comp
        eW.symm.toLinearMap ∧
      ∀ (h : H) (S : Set Q.carrier),
        μ (exponentialConjugate Q.equiv ExpQ hbij
          (M.coneAdjointAutomorphism T C hadd h) '' S) =
        ENNReal.ofReal (Real.exp (ell (eW (heightProjection T.character (h : L))))) * μ S := by
  obtain ⟨μ, c, hμ, hout, hin, _, hvol⟩ :=
    M.exists_cone_haar_multiplier T C hadd Q ExpQ hExpQ hbij haar
  let ell := (∑ i, (c i : ℝ) • cartanHeightWeight T H (M.weight i)).comp eW.symm.toLinearMap
  refine ⟨μ, ell, c, hμ, hout, hin, rfl, ?_⟩
  intro h S
  have heval : ell (eW (heightProjection T.character (h : L))) =
      ∑ i, (c i : ℝ) * M.weight i h := by
    simp only [ell, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.symm_apply_apply, LinearMap.sum_apply, LinearMap.smul_apply,
      smul_eq_mul, cartanHeightWeight_projection]
  rw [heval]
  exact hvol h S

end CartanWordModel

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanConeHaarAction
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instDecidableEqConeMixedWords _root_.OAI.PolycyclicRecognition.CartanWordModel.instFintypeConeMixedWords _root_.OAI.PolycyclicRecognition.CartanWordModel.instNonemptyConeIdealBases _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual cone Haar action for the offset trace tests -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule Set Filter MeasureTheory
open scoped Pointwise BigOperators
open scoped Manifold Topology

variable {EG G : Type} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {ExpG : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H ExpG)

variable (C : Set (H →ₗ[ℝ] ℝ))
  (hadd : ∀ x ∈ C, ∀ y ∈ C, x + y ∈ C)
  (Q : NilpotentLieModel ((cartanRootIdeal H) ⧸ M.coneWordIdeal C))
  (ExpQ : GroupLieAlgebra (𝓘(ℝ, Q.modelSpace)) Q.carrier → Q.carrier)
  (hbijQ : Function.Bijective ExpQ)
  (chartQ : GroupLieAlgebra (𝓘(ℝ, Q.modelSpace)) Q.carrier ≃ₜ Q.carrier)
  (hchartQ : ∀ v, chartQ v = ExpQ v)
  (hbijN : Function.Bijective F.ExpN) (hbijD : Function.Bijective F.ExpD)
  (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
  (π : F.N.carrier →* Q.carrier)
  (hπ : ∀ x : cartanRootIdeal H,
    π (F.ExpN (F.N.equiv x)) = ExpQ (Q.equiv (M.coneProjection C x)))
  (α : F.D.carrier →* MulAut Q.carrier)
  (hα : ∀ d n, α d (π n) = π (F.action d n))
  (hφ : ∀ d, F.action d = M.adjointGroupAutomorphism T F.N.equiv F.ExpN F.isExpN
    hbijN dynkinN (cartanLog H F.D.equiv F.ExpD hbijD d))


set_option maxHeartbeats 1000000 in
include hπ hα hφ in
/-- The quotient action of each actual Cartan factor is the exponential
of its induced Lie action, with the actual Cartan logarithm. -/
theorem factor_cone_quotient_action_eq_exponential (d : F.D.carrier) (q : Q.carrier) :
    α d q = exponentialConjugate Q.equiv ExpQ hbijQ
      (M.coneAdjointAutomorphism T C hadd
        (cartanLog H F.D.equiv F.ExpD hbijD d)) q := by
  obtain ⟨v, hv⟩ := hbijQ.surjective q
  obtain ⟨w, hw⟩ := Q.equiv.surjective v
  obtain ⟨x, hx⟩ := M.coneProjection_surjective C w
  have hq : ExpQ (Q.equiv (M.coneProjection C x)) = q :=
    (congrArg ExpQ ((congrArg Q.equiv hx).trans hw)).trans hv
  rw [← hq]
  let h := cartanLog H F.D.equiv F.ExpD hbijD d
  have he : F.action d (F.ExpN (F.N.equiv x)) =
      F.ExpN (F.N.equiv (cartanIdealAdjointAutomorphism T H h x)) := by
    exact (congrArg (fun a : MulAut F.N.carrier => a (F.ExpN (F.N.equiv x)))
      (hφ d)).trans (integrateNilpotentLieEquiv_apply_exp F.N.equiv F.ExpN hbijN dynkinN
        F.isExpN M.bound_zero (cartanIdealAdjointAutomorphism T H h) x)
  calc
    α d (ExpQ (Q.equiv (M.coneProjection C x))) =
        α d (π (F.ExpN (F.N.equiv x))) := congrArg (α d) (hπ x).symm
    _ = π (F.action d (F.ExpN (F.N.equiv x))) := hα d _
    _ = π (F.ExpN (F.N.equiv (cartanIdealAdjointAutomorphism T H h x))) := congrArg π he
    _ = ExpQ (Q.equiv (M.coneProjection C
        (cartanIdealAdjointAutomorphism T H h x))) := hπ _
    _ = _ := by
      have hp := M.coneAdjoint_projection T C
        hadd h x
      exact (congrArg (fun v => ExpQ (Q.equiv v)) hp).symm.trans
        (exponentialConjugate_apply_exp Q.equiv ExpQ hbijQ
          (M.coneAdjointAutomorphism T C
            hadd h) (M.coneProjection C x)).symm


set_option maxHeartbeats 1000000 in
include hbijQ hπ hα hφ hadd in
/-- The quotient Haar character is the actual ambient height character.
The nilpotent factor contributes only a Haar-preserving translation. -/
theorem exists_cone_action_haar_height_multiplier
    {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W]
    (eW : HeightSpace T.character ≃ₗ[ℝ] W) (height : G →* Multiplicative W)
    (hheight : ∀ x, (height (ExpG x)).toAdd = eW (heightProjection T.character x))
    (hExpQ : IsGroupExponential ExpQ)
    (haar : NilpotentExponentialHaarInput Q.modelSpace Q.carrier)
    (act : G →* Equiv.Perm Q.carrier)
    (hact : ∀ u d q, act (F.inclusionN u * F.inclusionD d) q = π u * α d q) :
    ∃ (μ : Measure Q.carrier) (ell : W →ₗ[ℝ] ℝ) (c : Fin M.letterCount → ℕ),
      μ.IsHaarMeasure ∧
      (∀ i, (M.weight i : H →ₗ[ℝ] ℝ) ∉ C → c i = 0) ∧
      (∀ i, (M.weight i : H →ₗ[ℝ] ℝ) ∈ C → 0 < c i) ∧
      ell = (∑ i, (c i : ℝ) • cartanHeightWeight T H (M.weight i)).comp
        eW.symm.toLinearMap ∧
      ∀ (g : G) (E : Set Q.carrier), μ (act g '' E) =
        ENNReal.ofReal (Real.exp (ell (height g).toAdd)) * μ E := by
  let _ : IsTopologicalGroup Q.carrier := topologicalGroup_of_lieGroup (𝓘(ℝ, Q.modelSpace)) ⊤
  obtain ⟨μ, ell, c, hμ, hout, hin, hell, hvol⟩ := M.exists_cone_haar_height_multiplier T eW
    C hadd Q ExpQ hExpQ hbijQ haar
  let : μ.IsHaarMeasure := hμ
  refine ⟨μ, ell, c, hμ, hout, hin, hell, ?_⟩
  intro g E
  obtain ⟨⟨u, d⟩, rfl⟩ := F.surjective g
  let h := cartanLog H F.D.equiv F.ExpD hbijD d
  have hαeq : (fun q => α d q) = exponentialConjugate Q.equiv ExpQ hbijQ
      (M.coneAdjointAutomorphism T C hadd h) := by
    funext q
    exact M.factor_cone_quotient_action_eq_exponential T F C hadd Q ExpQ hbijQ
      hbijN hbijD dynkinN π hπ α hα hφ d q
  have hset : act (F.inclusionN u * F.inclusionD d) '' E = π u • (α d '' E) := by
    rw [← Set.image_smul, Set.image_image]
    congr 1
    funext q
    exact hact u d q
  have hh : (height (F.inclusionN u * F.inclusionD d)).toAdd =
      eW (heightProjection T.character (h : GroupLieAlgebra (𝓘(ℝ, EG)) G)) := by
    rw [map_mul, F.inclusionN_height_eq_one T eW height hheight hbijN, one_mul]
    exact F.inclusionD_height T eW height hheight hbijD d
  rw [hset, measure_smul, hh]
  have himage : α d '' E = exponentialConjugate Q.equiv ExpQ hbijQ
      (M.coneAdjointAutomorphism T C hadd h) '' E :=
    congrArg (fun k : Q.carrier → Q.carrier => k '' E) hαeq
  rw [himage]
  exact hvol h E

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanIntegratedAction
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instDecidableEqConeMixedWords _root_.OAI.PolycyclicRecognition.CartanWordModel.instFintypeConeMixedWords _root_.OAI.PolycyclicRecognition.CartanWordModel.instNonemptyConeIdealBases _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The Cartan action, assembled from actual conjugation

The action laws are derived from a faithful ambient inclusion. They are not
assumed for the logarithmically parameterized adjoint automorphisms.
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
  (ExpN : GroupLieAlgebra (𝓘(ℝ, EN)) N → N) (hExpN : IsGroupExponential ExpN)
  (hbijN : Function.Bijective ExpN) (dynkinN : NilpotentDynkinExpansionInput EN N)
  {ED D : Type} [NormedAddCommGroup ED] [NormedSpace ℝ ED]
  [FiniteDimensional ℝ ED] [TopologicalSpace D] [ChartedSpace ED D] [Group D]
  [LieGroup (𝓘(ℝ, ED)) ⊤ D]
  (eD : H ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, ED)) D)
  (ExpD : GroupLieAlgebra (𝓘(ℝ, ED)) D → D) (hbijD : Function.Bijective ExpD)
  {A G : Type} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A] [Group G]

attribute [local instance 100] LieRing.ofAssociativeRing

set_option maxHeartbeats 1000000 in
/-- Pointwise adjoint automorphisms acquire the exact group action law
because their images under the injective inclusion are conjugations. -/
theorem exists_integrated_cartan_action
    (j : L →ₗ⁅ℝ⁆ A) (ρ : G →* Aˣ) (hρ : Function.Injective ρ)
    (ιN : N →* G) (hιN : Function.Injective ιN) (ιD : D →* G)
    (hN : ∀ x : cartanRootIdeal H, ρ (ιN (ExpN (eN x))) = algebraExpUnit (j x))
    (hD : ∀ h : H, ρ (ιD (ExpD (eD h))) = algebraExpUnit (j h)) :
    ∃ φ : D →* MulAut N,
      (∀ d, φ d = M.adjointGroupAutomorphism T eN ExpN hExpN hbijN dynkinN
        (cartanLog H eD ExpD hbijD d)) ∧
      ∀ d g, ιN (φ d g) = ιD d * ιN g * (ιD d)⁻¹ := by
  let a : D → MulAut N := fun d => M.adjointGroupAutomorphism T eN ExpN
    hExpN hbijN dynkinN (cartanLog H eD ExpD hbijD d)
  have ha (d : D) (g : N) : ιN (a d g) = ιD d * ιN g * (ιD d)⁻¹ := by
    have h := M.adjointGroupAutomorphism_eq_conjugation T eN ExpN hExpN hbijN dynkinN
      j ρ hρ ιN (fun h => ιD (ExpD (eD h))) hN hD (cartanLog H eD ExpD hbijD d) g
    simpa only [exp_cartanLog] using h
  exact ⟨conjugationLift ιN ιD hιN a ha, fun _ => rfl, ha⟩

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
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.instFiniteRootOffsetConeIndex _root_.OAI.PolycyclicRecognition.instNonemptyRootOffsetConeIndex _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
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

variable {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W]
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

variable {L W : Type} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
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
/-- One target ideal basis maximizes every radius used by the path comparison. -/
theorem exists_transformed_polar_probe_basis (K : ProperCone ℝ (StrongDual ℝ W))
    (A : W ≃ₗ[ℝ] W)
    (bI : Basis (Fin (finrank ℝ
      (M.coneWordIdeal (heightConePreimage T eW (transformedPolarCone K A)))) )
      ℝ (M.coneWordIdeal (heightConePreimage T eW (transformedPolarCone K A)))) :
    ∃ β : M.ConeIdealBases (heightConePreimage T eW (transformedPolarCone K A)),
      ∀ c : ℝ, 0 ≤ c →
        M.IsMaximizingConeIdealBasis (heightConePreimage T eW (transformedPolarCone K A)) bI
          ((M.supportIn T hunimod eW).weightSupport
            (A '' ((fun x : W => c • x) '' conePolarTemplate K))) β := by
  let C := heightConePreimage (H := H) T eW (transformedPolarCone K A)
  let s := fun i => conePolarWidth K
    (((M.supportIn T hunimod eW).weight i).toContinuousLinearMap.comp
      A.toLinearMap.toContinuousLinearMap)
  obtain ⟨β, hβ⟩ := M.exists_maximizing_coneIdealBasis C bI s
  refine ⟨β, ?_⟩
  intro c hc
  have he : (M.supportIn T hunimod eW).weightSupport
      (A '' ((fun x : W => c • x) '' conePolarTemplate K)) = fun i => c * s i := by
    funext i
    exact M.weightSupport_transformed_polar T hunimod eW K A hc i
  rw [he]
  exact M.maximizing_coneIdealBasis_smul C bI s β hβ hc

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanPolarConeKernel
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.instFiniteRootOffsetConeIndex _root_.OAI.PolycyclicRecognition.instNonemptyRootOffsetConeIndex _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.CartanFactorModel.heightRay_zero _root_.OAI.PolycyclicRecognition.cartanWeightDerivation_apply_root _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.nilshadowWeightDerivation_symm _root_.OAI.PolycyclicRecognition.nilshadowWeightOperator_symm _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Removing the polar cone vertex without changing the mixed ideal

The polar template uses a closed cone containing zero. The cone quotient
must kill the zero generalized weight space to descend the overlapping
Cartan factors. Salience and the nonzero generator weights supply this
bridge for the same mixed ideal.
-/

noncomputable section
namespace PolycyclicRecognition

open Module LieAlgebra LieModule Set

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]

set_option maxHeartbeats 1000000 in
theorem transformedPolarCone_salient [FiniteDimensional ℝ V]
    (K : ProperCone ℝ (StrongDual ℝ V)) (A : V ≃ₗ[ℝ] V)
    (hK : (K : ConvexCone ℝ (StrongDual ℝ V)).Salient) :
    (transformedPolarCone K A : ConvexCone ℝ (StrongDual ℝ V)).Salient := by
  intro β hβ hne hneg
  have hcomp : β.comp A.toLinearMap.toContinuousLinearMap ≠ 0 := by
    intro hz
    apply hne
    ext x
    have hx := congrArg (fun f : StrongDual ℝ V => f (A.symm x)) hz
    simpa using hx
  apply hK _ hβ hcomp
  change -(β.comp A.toLinearMap.toContinuousLinearMap) ∈ K
  change (-β).comp A.toLinearMap.toContinuousLinearMap ∈ K at hneg
  simpa only [ContinuousLinearMap.neg_comp] using hneg

namespace CartanWordModel

variable {L W : Type} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {H : LieSubalgebra ℝ L} [H.IsCartanSubalgebra] (M : CartanWordModel H)
  {a : ℕ} (T : TriangularAdjoint L a)
  (hunimod : ∀ x : L, LinearMap.trace ℝ L (ad ℝ L x) = 0)
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)

set_option maxHeartbeats 1000000 in
theorem coneWordIdeal_eq_of_generator_membership
    (C D : Set (H →ₗ[ℝ] ℝ))
    (he : ∀ i, (M.weight i : H →ₗ[ℝ] ℝ) ∈ C ↔ (M.weight i : H →ₗ[ℝ] ℝ) ∈ D) :
    M.coneWordIdeal C = M.coneWordIdeal D := by
  have hp : (fun i => (M.weight i : H →ₗ[ℝ] ℝ) ∉ C) =
      (fun i => (M.weight i : H →ₗ[ℝ] ℝ) ∉ D) := funext fun i => propext (not_congr (he i))
  simp only [coneWordIdeal, hp]

set_option maxHeartbeats 1000000 in
theorem heightConePreimage_add (K : ProperCone ℝ (StrongDual ℝ W))
    {χ ψ : H →ₗ[ℝ] ℝ} (hχ : χ ∈ heightConePreimage T eW K)
    (hψ : ψ ∈ heightConePreimage T eW K) : χ + ψ ∈ heightConePreimage T eW K := by
  change ((χ.comp (cartanHeightSection T H)).comp eW.symm.toLinearMap).toContinuousLinearMap +
    ((ψ.comp (cartanHeightSection T H)).comp eW.symm.toLinearMap).toContinuousLinearMap ∈ K
  exact K.add_mem hχ hψ

set_option maxHeartbeats 1000000 in
theorem positiveHeightConePreimage_add (K : ProperCone ℝ (StrongDual ℝ W))
    (hK : (K : ConvexCone ℝ (StrongDual ℝ W)).Salient)
    {χ ψ : H →ₗ[ℝ] ℝ} (hχ : χ ∈ positiveHeightConePreimage T eW K)
    (hψ : ψ ∈ positiveHeightConePreimage T eW K) :
    χ + ψ ∈ positiveHeightConePreimage T eW K := by
  let f := ((χ.comp (cartanHeightSection T H)).comp eW.symm.toLinearMap).toContinuousLinearMap
  let g := ((ψ.comp (cartanHeightSection T H)).comp eW.symm.toLinearMap).toContinuousLinearMap
  change f + g ∈ K ∧ f + g ≠ 0
  refine ⟨K.add_mem hχ.1 hψ.1, ?_⟩
  intro he
  have hg : g = -f := eq_neg_of_add_eq_zero_left (by simpa [add_comm] using he)
  exact hK f hχ.1 hχ.2 (hg ▸ hψ.1)

set_option maxHeartbeats 1000000 in
theorem zero_not_mem_positiveHeightConePreimage (K : ProperCone ℝ (StrongDual ℝ W)) :
    (0 : H →ₗ[ℝ] ℝ) ∉ positiveHeightConePreimage T eW K := by
  simp [positiveHeightConePreimage]

set_option maxHeartbeats 1000000 in
include hunimod in
/-- Removing the vertex does not remove any of the nonzero generator weights. -/
theorem coneWordIdeal_positiveHeight_eq (K : ProperCone ℝ (StrongDual ℝ W)) :
    M.coneWordIdeal (positiveHeightConePreimage T eW K) =
      M.coneWordIdeal (heightConePreimage T eW K) := by
  apply M.coneWordIdeal_eq_of_generator_membership
  intro i
  change (((M.supportIn T hunimod eW).weight i).toContinuousLinearMap ∈ K ∧
    ((M.supportIn T hunimod eW).weight i).toContinuousLinearMap ≠ 0) ↔
      ((M.supportIn T hunimod eW).weight i).toContinuousLinearMap ∈ K
  exact ⟨And.left, fun h => ⟨h, M.sampling_weight_ne_zero T hunimod eW i⟩⟩

end CartanWordModel
end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanPolarConeAction
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.instFiniteRootOffsetConeIndex _root_.OAI.PolycyclicRecognition.instNonemptyRootOffsetConeIndex _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The ambient action and Haar trace for the actual closed polar cone -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule Set MeasureTheory
open scoped Manifold BigOperators

variable {EG G W Q : Type} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [Group Q]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H Exp)
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  (hunimod : ∀ x : GroupLieAlgebra (𝓘(ℝ, EG)) G, LinearMap.trace ℝ _ (ad ℝ _ x) = 0)
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)
  {A : Type} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

attribute [local instance 100] LieRing.ofAssociativeRing

set_option maxHeartbeats 1000000 in
theorem factor_action_eq_adjoint
    (j : GroupLieAlgebra (𝓘(ℝ, EG)) G →ₗ⁅ℝ⁆ A) (ρ : G →* Aˣ)
    (hρ : Function.Injective ρ)
    (hN : ∀ x : cartanRootIdeal H,
      ρ (F.inclusionN (F.ExpN (F.N.equiv x))) = algebraExpUnit (j x))
    (hD : ∀ h : H, ρ (F.inclusionD (F.ExpD (F.D.equiv h))) = algebraExpUnit (j h))
    (hNbij : Function.Bijective F.ExpN) (hDbij : Function.Bijective F.ExpD)
    (dynkin : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier) :
    ∀ d, F.action d = M.adjointGroupAutomorphism T F.N.equiv F.ExpN F.isExpN
      hNbij dynkin (cartanLog H F.D.equiv F.ExpD hDbij d) := by
  obtain ⟨φ, hφ, hconj⟩ := M.exists_integrated_cartan_action T F.N.equiv F.ExpN F.isExpN
    hNbij dynkin F.D.equiv F.ExpD hDbij j ρ hρ F.inclusionN F.closedN.injective
    F.inclusionD hN hD
  intro d
  refine Eq.trans ?_ (hφ d)
  apply MulEquiv.ext
  intro n
  apply F.closedN.injective
  exact (F.conjugation d n).trans (hconj d n).symm

set_option maxHeartbeats 1000000 in
omit [FiniteDimensional ℝ W] in
theorem sum_height_weights_transport (c : Fin M.letterCount → ℕ) :
    (∑ i, (c i : ℝ) • cartanHeightWeight T H (M.weight i)).comp eW.symm.toLinearMap =
      ∑ i, (c i : ℝ) • (M.supportIn T hunimod eW).weight i := by
  ext w
  simp only [LinearMap.comp_apply, LinearMap.sum_apply, LinearMap.smul_apply,
    smul_eq_mul, supportIn, SupportDatum.transport, supportDatum_weight]

set_option maxHeartbeats 1000000 in
include hunimod in
/-- Salience removes the cone vertex at the generators, giving the actual
ambient action without a false zero-exclusion assumption on a closed cone. -/
theorem exists_polar_cone_ambient_action
    (j : GroupLieAlgebra (𝓘(ℝ, EG)) G →ₗ⁅ℝ⁆ A) (ρ : G →* Aˣ)
    (hρ : Function.Injective ρ)
    (hN : ∀ x : cartanRootIdeal H,
      ρ (F.inclusionN (F.ExpN (F.N.equiv x))) = algebraExpUnit (j x))
    (hD : ∀ h : H, ρ (F.inclusionD (F.ExpD (F.D.equiv h))) = algebraExpUnit (j h))
    (hNbij : Function.Bijective F.ExpN) (hDsurj : Function.Surjective F.ExpD)
    (dynkin : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
    (K : ProperCone ℝ (StrongDual ℝ W))
    (hK : (K : ConvexCone ℝ (StrongDual ℝ W)).Salient)
    (π : F.N.carrier →* Q) (s : Q → F.N.carrier) (hs : Function.RightInverse s π)
    (hker : (π.ker : Set F.N.carrier) = F.ExpN ''
      (F.N.equiv '' (M.coneWordIdeal (heightConePreimage T eW K) : Set (cartanRootIdeal H)))) :
    ∃ (α : F.D.carrier →* MulAut Q) (act : G →* Equiv.Perm Q),
      (∀ d n, α d (π n) = π (F.action d n)) ∧
      (∀ n d q, act (F.inclusionN n * F.inclusionD d) q = π n * α d q) ∧
      (∀ g, act g 1 = 1 ↔ ∃ n d, n ∈ π.ker ∧ F.inclusionN n * F.inclusionD d = g) ∧
      ∀ g h, act (g * h) 1 = act g (act h 1) := by
  have hker' : (π.ker : Set F.N.carrier) = F.ExpN ''
      (F.N.equiv '' (M.coneWordIdeal (positiveHeightConePreimage T eW K) :
        Set (cartanRootIdeal H))) := by
    rw [M.coneWordIdeal_positiveHeight_eq T hunimod eW K]
    exact hker
  exact exists_cartan_cone_ambient_action M F T j ρ hρ hN hD hNbij hDsurj dynkin
    (positiveHeightConePreimage T eW K)
    (fun _ hx _ hy => positiveHeightConePreimage_add T eW K hK hx hy)
    (zero_not_mem_positiveHeightConePreimage T eW K) π s hs hker'

set_option maxHeartbeats 1000000 in
/-- The descended action comes with its genuine Haar measure and the exact
positive generator multiplicities used by the offset trace separation. -/
theorem exists_polar_cone_action_haar
    (j : GroupLieAlgebra (𝓘(ℝ, EG)) G →ₗ⁅ℝ⁆ A) (ρ : G →* Aˣ)
    (hρ : Function.Injective ρ)
    (hN : ∀ x : cartanRootIdeal H,
      ρ (F.inclusionN (F.ExpN (F.N.equiv x))) = algebraExpUnit (j x))
    (hD : ∀ h : H, ρ (F.inclusionD (F.ExpD (F.D.equiv h))) = algebraExpUnit (j h))
    (hNbij : Function.Bijective F.ExpN) (hDbij : Function.Bijective F.ExpD)
    (dynkin : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
    (K : ProperCone ℝ (StrongDual ℝ W))
    (hK : (K : ConvexCone ℝ (StrongDual ℝ W)).Salient)
    (Q₀ : NilpotentLieModel ((cartanRootIdeal H) ⧸
      M.coneWordIdeal (heightConePreimage T eW K)))
    (ExpQ : GroupLieAlgebra (𝓘(ℝ, Q₀.modelSpace)) Q₀.carrier → Q₀.carrier)
    (hExpQ : IsGroupExponential ExpQ) (hbijQ : Function.Bijective ExpQ)
    (haarQ : NilpotentExponentialHaarInput Q₀.modelSpace Q₀.carrier)
    (π : F.N.carrier →* Q₀.carrier) (s : Q₀.carrier → F.N.carrier)
    (hs : Function.RightInverse s π)
    (hker : (π.ker : Set F.N.carrier) = F.ExpN ''
      (F.N.equiv '' (M.coneWordIdeal (heightConePreimage T eW K) : Set (cartanRootIdeal H))))
    (hπ : ∀ v, π (F.ExpN (F.N.equiv v)) =
      ExpQ (Q₀.equiv (M.coneProjection (heightConePreimage T eW K) v)))
    (height : G →* Multiplicative W)
    (hheight : ∀ v, (height (Exp v)).toAdd = eW (heightProjection T.character v)) :
    ∃ (α : F.D.carrier →* MulAut Q₀.carrier) (act : G →* Equiv.Perm Q₀.carrier)
      (μ : Measure Q₀.carrier) (c : Fin M.letterCount → ℕ),
      μ.IsHaarMeasure ∧
      (∀ d n, α d (π n) = π (F.action d n)) ∧
      (∀ n d q, act (F.inclusionN n * F.inclusionD d) q = π n * α d q) ∧
      (∀ i, ((M.supportIn T hunimod eW).weight i).toContinuousLinearMap ∉ K → c i = 0) ∧
      (∀ i, ((M.supportIn T hunimod eW).weight i).toContinuousLinearMap ∈ K → 0 < c i) ∧
      ∀ g E, μ (act g '' E) = ENNReal.ofReal (Real.exp
        ((∑ i, (c i : ℝ) • ((M.supportIn T hunimod eW).weight i).toContinuousLinearMap)
          (height g).toAdd)) * μ E := by
  obtain ⟨α, act, hα, hact, _, _⟩ := M.exists_polar_cone_ambient_action F T hunimod eW
    j ρ hρ hN hD hNbij hDbij.surjective dynkin K hK π s hs hker
  have hadd : ∀ x ∈ heightConePreimage (H := H) T eW K,
      ∀ y ∈ heightConePreimage T eW K, x + y ∈ heightConePreimage T eW K :=
    fun _ hx _ hy => heightConePreimage_add T eW K hx hy
  obtain ⟨μ, ell, c, hμ, hout, hin, hell, hvol⟩ :=
    M.exists_cone_action_haar_height_multiplier T F (heightConePreimage T eW K) hadd
      Q₀ ExpQ hbijQ hNbij hDbij dynkin π hπ α hα
      (M.factor_action_eq_adjoint F T j ρ hρ hN hD hNbij hDbij dynkin)
      eW height hheight hExpQ haarQ act hact
  have hell' : ell = ∑ i, (c i : ℝ) • (M.supportIn T hunimod eW).weight i := by
    rw [hell, M.sum_height_weights_transport T hunimod eW c]
  refine ⟨α, act, μ, c, hμ, hα, hact, ?_, ?_, ?_⟩
  · intro i hi
    apply hout i
    intro h
    exact hi ((M.weight_mem_heightConePreimage_iff T hunimod eW K i).mp h)
  · intro i hi
    exact hin i ((M.weight_mem_heightConePreimage_iff T hunimod eW K i).mpr hi)
  · intro g E
    have heval : ell (height g).toAdd =
        (∑ i, (c i : ℝ) • ((M.supportIn T hunimod eW).weight i).toContinuousLinearMap)
          (height g).toAdd := by
      rw [hell']
      simp only [LinearMap.sum_apply, LinearMap.smul_apply, sum_apply, smul_apply]
      rfl
    rw [hvol, heval]

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_ExponentialRepresentationInput
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instDecidableEqConeMixedWords _root_.OAI.PolycyclicRecognition.CartanWordModel.instFintypeConeMixedWords _root_.OAI.PolycyclicRecognition.CartanWordModel.instNonemptyConeIdealBases _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
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
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanPublishedPolarAction
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.instFiniteRootOffsetConeIndex _root_.OAI.PolycyclicRecognition.instNonemptyRootOffsetConeIndex _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polar quotient actions from the precise published realization -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule Set MeasureTheory
open scoped Manifold BigOperators

variable {EG G W : Type} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H Exp)
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  (hunimod : ∀ x : GroupLieAlgebra (𝓘(ℝ, EG)) G, LinearMap.trace ℝ _ (ad ℝ _ x) = 0)
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)

attribute [local instance 100] LieRing.ofAssociativeRing
open scoped Matrix.Norms.Operator

set_option maxHeartbeats 1000000 in
/-- The published faithful exponential realization constructs the actual
polar quotient action and its Haar multiplier for the already constructed
cone model. It contributes no metric or chosen-height compatibility. -/
theorem MeasuredCone.polar_action_haar_of_published_realization
    (hExp : IsGroupExponential Exp)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (hNbij : Function.Bijective F.ExpN) (hDbij : Function.Bijective F.ExpD)
    (dynkin : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
    (K : ProperCone ℝ (StrongDual ℝ W))
    (hK : (K : ConvexCone ℝ (StrongDual ℝ W)).Salient)
    (D : M.MeasuredCone F (heightConePreimage T eW K))
    (haarQ : NilpotentExponentialHaarInput D.Q.modelSpace D.Q.carrier)
    (height : G →* Multiplicative W)
    (hheight : ∀ v, (height (Exp v)).toAdd = eW (heightProjection T.character v)) :
    ∃ (α : F.D.carrier →* MulAut D.Q.carrier) (act : G →* Equiv.Perm D.Q.carrier)
      (μ : Measure D.Q.carrier) (c : Fin M.letterCount → ℕ),
      μ.IsHaarMeasure ∧
      (∀ d n, α d (D.maps.quotient n) = D.maps.quotient (F.action d n)) ∧
      (∀ n d q, act (F.inclusionN n * F.inclusionD d) q = D.maps.quotient n * α d q) ∧
      (∀ i, ((M.supportIn T hunimod eW).weight i).toContinuousLinearMap ∉ K → c i = 0) ∧
      (∀ i, ((M.supportIn T hunimod eW).weight i).toContinuousLinearMap ∈ K → 0 < c i) ∧
      ∀ g E, μ (act g '' E) = ENNReal.ofReal (Real.exp
        ((∑ i, (c i : ℝ) • ((M.supportIn T hunimod eW).weight i).toContinuousLinearMap)
          (height g).toAdd)) * μ E := by
  obtain ⟨m, hm, ρ, j, hind, hmatch⟩ := realize ⟨a, ⟨T⟩⟩ Exp hExp
  let _ : NeZero m := ⟨Nat.ne_of_gt hm⟩
  have hρ : Function.Injective ρ := by
    intro g h he
    exact hind.injective (congrArg (fun u : (Matrix (Fin m) (Fin m) ℝ)ˣ =>
      (u : Matrix (Fin m) (Fin m) ℝ)) he)
  have hN (x : cartanRootIdeal H) :
      ρ (F.inclusionN (F.ExpN (F.N.equiv x))) = algebraExpUnit (j x) := by
    rw [F.compatibleN, hmatch]
  have hD (h : H) :
      ρ (F.inclusionD (F.ExpD (F.D.equiv h))) = algebraExpUnit (j h) := by
    rw [F.compatibleD, hmatch]
  have hbijQ : Function.Bijective D.maps.expQ :=
    funext D.maps.chartQ_eq ▸ D.maps.chartQ.bijective
  exact M.exists_polar_cone_action_haar F T hunimod eW j ρ hρ hN hD hNbij hDbij
    dynkin K hK D.Q D.maps.expQ D.maps.isExpQ hbijQ haarQ D.maps.quotient
    D.maps.sectionMap D.maps.section_rightInverse D.maps.kernel_eq D.maps.quotient_exp
    height hheight

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanPublishedPolarRegions
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.instFiniteRootOffsetConeIndex _root_.OAI.PolycyclicRecognition.instNonemptyRootOffsetConeIndex _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual target regions and Haar trace for a transformed polar cone -/

noncomputable section
namespace PolycyclicRecognition

namespace CartanWordModel

open Module LieAlgebra LieModule Set MeasureTheory Metric Filter
open scoped Manifold BigOperators Topology

variable {EG G W : Type} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G]
  [IsIsometricSMul G G] [ProperSpace G]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H Exp)
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  (hunimod : ∀ x : GroupLieAlgebra (𝓘(ℝ, EG)) G, LinearMap.trace ℝ _ (ad ℝ _ x) = 0)
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)

set_option maxHeartbeats 1000000 in
/-- The transformed polar geometry supplies a maximizing ideal basis and
a path threshold for an already specified compatible quotient action. -/
theorem MeasuredCone.uniform_polar_regions_of_action
    (hExp : IsGroupExponential Exp)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (hNbij : Function.Bijective F.ExpN) (hDbij : Function.Bijective F.ExpD)
    (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
    (dynkinD : NilpotentDynkinExpansionInput F.D.modelSpace F.D.carrier)
    (chartN : GroupLieAlgebra (𝓘(ℝ, F.N.modelSpace)) F.N.carrier ≃ₜ F.N.carrier)
    (hchartN : ∀ v, chartN v = F.ExpN v)
    (chartD : GroupLieAlgebra (𝓘(ℝ, F.D.modelSpace)) F.D.carrier ≃ₜ F.D.carrier)
    (hchartD : ∀ v, chartD v = F.ExpD v)
    (height : G →* Multiplicative W)
    (hheight : ∀ v, (height (Exp v)).toAdd = eW (heightProjection T.character v))
    (hpath : ∀ g : G, ∃ γ : ℝ → G, γ 0 = 1 ∧ γ 1 = g ∧
      ∀ t ∈ Icc (0 : ℝ) 1, ∀ u ∈ Icc (0 : ℝ) 1,
        dist (γ t) (γ u) ≤ dist 1 g * |t - u|)
    {Lheight : ℝ} (hLheight : 0 ≤ Lheight)
    (hLip : ∀ x y, ‖(height x).toAdd - (height y).toAdd‖ ≤ Lheight * dist x y)
    (K : ProperCone ℝ (StrongDual ℝ W)) (A : W ≃ₗ[ℝ] W)
    (D : M.MeasuredCone F (heightConePreimage T eW (transformedPolarCone K A)))
    (haarQ : NilpotentExponentialHaarInput D.Q.modelSpace D.Q.carrier)
    (haarI : NilpotentExponentialHaarInput D.I.modelSpace D.I.carrier)
    (haarD : NilpotentExponentialHaarInput F.D.modelSpace F.D.carrier)
    (ν : Measure F.D.carrier) [ν.IsHaarMeasure]
    (bN : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (bI : Basis (Fin (finrank ℝ
      (M.coneWordIdeal (heightConePreimage T eW (transformedPolarCone K A)))))
      ℝ (M.coneWordIdeal (heightConePreimage T eW (transformedPolarCone K A))))
    (γ₀ : M.Bases) {cell : Set (F.N.carrier × F.D.carrier)} (hcell : IsCompact cell)
    {ε : ℝ} (hε : 0 < ε)
    (μQ : Measure D.Q.carrier) [μQ.IsHaarMeasure]
    (α : F.D.carrier →* MulAut D.Q.carrier) (act : G →* Equiv.Perm D.Q.carrier)
    (hact : ∀ n d q, act (F.inclusionN n * F.inclusionD d) q = D.maps.quotient n * α d q) :
    let C := heightConePreimage T eW (transformedPolarCone K A)
    let E₁ := A '' normalizedPolarTemplates K ε 0
    let E₂ := A '' normalizedPolarTemplates K ε 2
    ∃ β₂ : M.ConeIdealBases C,
      M.IsMaximizingConeIdealBasis C bI ((M.supportIn T hunimod eW).weightSupport E₂) β₂ ∧
      ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ (scale η : ℕ → ℝ),
        StrictMono scale → Tendsto scale atTop atTop → (∀ n, 1 ≤ scale n) →
        (∀ n, 0 ≤ η n) → Tendsto η atTop (𝓝 0) →
        ∀ Cp Clog : ℝ, 0 ≤ Cp → 0 ≤ Clog →
        ∃ R : MeasuredProbeRegions D.maps.quotient μQ
          (D.kernelMeasure M F C) ν scale
          (∑ j, M.coneIdealWordCost C
            ((M.supportIn T hunimod eW).weightSupport E₂) (β₂.val j)),
          ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
          ∀ᶠ n in atTop, R.ControlsTwoPaths
            (fun u d => F.inclusionN u * F.inclusionD d) F.action (fun g q => act g q)
            height cell E₁ E₂ η Cp Clog δ n := by
  dsimp only
  let C := heightConePreimage (H := H) T eW (transformedPolarCone K A)
  let E₁ := A '' normalizedPolarTemplates K ε 0
  let E₂ := A '' normalizedPolarTemplates K ε 2
  let : D.measures.measureI.IsHaarMeasure := D.measures.haarI
  obtain ⟨β₂, hβ₂all⟩ := M.exists_transformed_polar_probe_basis T hunimod eW K A bI
  have hβ₂ : M.IsMaximizingConeIdealBasis C bI
      ((M.supportIn T hunimod eW).weightSupport E₂) β₂ :=
    hβ₂all (ε / 3) (by positivity)
  obtain ⟨hE₁, _, hz₁, _, hzero₁, _⟩ :=
    M.transformed_polar_width_properties T hunimod eW K A
      (c := 2 * ε / 3) (by positivity)
  obtain ⟨hE₂, _, hz₂, hs₂, hzero₂, hpos₂⟩ :=
    M.transformed_polar_width_properties T hunimod eW K A
      (c := ε / 3) (by positivity)
  obtain ⟨β₁, hβ₁, _⟩ := M.exists_maximizing_box_basis T hunimod eW bN E₁
  have hφ (d : F.D.carrier) : F.action d =
      M.adjointGroupAutomorphism T F.N.equiv F.ExpN F.isExpN hNbij dynkinN
        (cartanLog H F.D.equiv F.ExpD hDbij d) :=
    cartan_action_eq_adjoint_of_published_realization T M F hExp realize hNbij hDbij dynkinN d
  have factory : ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ (scale η : ℕ → ℝ),
        StrictMono scale → Tendsto scale atTop atTop → (∀ n, 1 ≤ scale n) →
        (∀ n, 0 ≤ η n) → Tendsto η atTop (𝓝 0) →
        ∀ Cp Clog : ℝ, 0 ≤ Cp → 0 ≤ Clog →
        ∃ R : MeasuredProbeRegions D.maps.quotient μQ
          (D.kernelMeasure M F C) ν scale
          (∑ j, M.coneIdealWordCost C
            ((M.supportIn T hunimod eW).weightSupport E₂) (β₂.val j)),
          ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
          ∀ᶠ n in atTop, R.ControlsTwoPaths
            (fun u d => F.inclusionN u * F.inclusionD d) F.action (fun g q => act g q)
            height cell E₁ E₂ η Cp Clog δ n := by
    exact exists_uniform_measured_probe_regions
      (EG := EG) (G := G) (W := W) T M F hunimod eW
      height hheight chartN hchartN chartD hchartD dynkinN dynkinD hNbij hDbij
      bN γ₀ hcell hφ hpath hLheight hLip C D.Q D.maps.expQ D.maps.isExpQ
      (funext D.maps.chartQ_eq ▸ D.maps.chartQ.bijective) haarQ D.maps.quotient
      D.maps.quotient_exp D.maps.chartQ D.maps.chartQ_eq μQ α act hact
      D.I D.maps.expI D.maps.isExpI haarI D.maps.inclusion D.maps.inclusion_closed
      D.maps.inclusion_range D.maps.inclusion_exp D.measures.measureI ν haarD
      E₁ E₂ hE₁ ⟨0, hz₁⟩ hE₂ ⟨0, hz₂⟩ β₁ hβ₁ hzero₁ bI β₂ hβ₂ hs₂ hzero₂ hpos₂
  obtain ⟨δ₀, hδ₀, hregions⟩ := factory
  exact ⟨β₂, hβ₂, δ₀, hδ₀, hregions⟩

set_option maxHeartbeats 1000000 in
/-- The action, its positive pure-word trace, the maximizing target basis,
and the uniform path-restriction regions all belong to one actual target
quotient. The region threshold is fixed before the scale or concentration
errors are chosen. -/
theorem MeasuredCone.exists_uniform_polar_target_regions_oai
    (hExp : IsGroupExponential Exp)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (hNbij : Function.Bijective F.ExpN) (hDbij : Function.Bijective F.ExpD)
    (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
    (dynkinD : NilpotentDynkinExpansionInput F.D.modelSpace F.D.carrier)
    (chartN : GroupLieAlgebra (𝓘(ℝ, F.N.modelSpace)) F.N.carrier ≃ₜ F.N.carrier)
    (hchartN : ∀ v, chartN v = F.ExpN v)
    (chartD : GroupLieAlgebra (𝓘(ℝ, F.D.modelSpace)) F.D.carrier ≃ₜ F.D.carrier)
    (hchartD : ∀ v, chartD v = F.ExpD v)
    (height : G →* Multiplicative W)
    (hheight : ∀ v, (height (Exp v)).toAdd = eW (heightProjection T.character v))
    (hpath : ∀ g : G, ∃ γ : ℝ → G, γ 0 = 1 ∧ γ 1 = g ∧
      ∀ t ∈ Icc (0 : ℝ) 1, ∀ u ∈ Icc (0 : ℝ) 1,
        dist (γ t) (γ u) ≤ dist 1 g * |t - u|)
    {Lheight : ℝ} (hLheight : 0 ≤ Lheight)
    (hLip : ∀ x y, ‖(height x).toAdd - (height y).toAdd‖ ≤ Lheight * dist x y)
    (K : ProperCone ℝ (StrongDual ℝ W)) (A : W ≃ₗ[ℝ] W)
    (hK : (K : ConvexCone ℝ (StrongDual ℝ W)).Salient)
    (D : M.MeasuredCone F (heightConePreimage T eW (transformedPolarCone K A)))
    (haarQ : NilpotentExponentialHaarInput D.Q.modelSpace D.Q.carrier)
    (haarI : NilpotentExponentialHaarInput D.I.modelSpace D.I.carrier)
    (haarD : NilpotentExponentialHaarInput F.D.modelSpace F.D.carrier)
    (ν : Measure F.D.carrier) [ν.IsHaarMeasure]
    (bN : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (bI : Basis (Fin (finrank ℝ
      (M.coneWordIdeal (heightConePreimage T eW (transformedPolarCone K A)))))
      ℝ (M.coneWordIdeal (heightConePreimage T eW (transformedPolarCone K A))))
    (γ₀ : M.Bases) {cell : Set (F.N.carrier × F.D.carrier)} (hcell : IsCompact cell)
    {ε : ℝ} (hε : 0 < ε) :
    let C := heightConePreimage (H := H) T eW (transformedPolarCone K A)
    let E₁ := A '' normalizedPolarTemplates K ε 0
    let E₂ := A '' normalizedPolarTemplates K ε 2
    ∃ (α : F.D.carrier →* MulAut D.Q.carrier) (act : G →* Equiv.Perm D.Q.carrier)
      (μQ : Measure D.Q.carrier) (c : Fin M.letterCount → ℕ)
      (β₂ : M.ConeIdealBases C),
      μQ.IsHaarMeasure ∧
      (∀ n d q, act (F.inclusionN n * F.inclusionD d) q = D.maps.quotient n * α d q) ∧
      (∀ i, ((M.supportIn T hunimod eW).weight i).toContinuousLinearMap ∉
        transformedPolarCone K A → c i = 0) ∧
      (∀ i, ((M.supportIn T hunimod eW).weight i).toContinuousLinearMap ∈
        transformedPolarCone K A → 0 < c i) ∧
      (∀ g E, μQ (act g '' E) = ENNReal.ofReal (Real.exp
        ((∑ i, (c i : ℝ) • ((M.supportIn T hunimod eW).weight i).toContinuousLinearMap)
          (height g).toAdd)) * μQ E) ∧
      M.IsMaximizingConeIdealBasis C bI ((M.supportIn T hunimod eW).weightSupport E₂) β₂ ∧
      ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ (scale η : ℕ → ℝ),
        StrictMono scale → Tendsto scale atTop atTop → (∀ n, 1 ≤ scale n) →
        (∀ n, 0 ≤ η n) → Tendsto η atTop (𝓝 0) →
        ∀ Cp Clog : ℝ, 0 ≤ Cp → 0 ≤ Clog →
        ∃ R : MeasuredProbeRegions D.maps.quotient μQ
          (D.kernelMeasure M F C) ν scale
          (∑ j, M.coneIdealWordCost C
            ((M.supportIn T hunimod eW).weightSupport E₂) (β₂.val j)),
          ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
          ∀ᶠ n in atTop, R.ControlsTwoPaths
            (fun u d => F.inclusionN u * F.inclusionD d) F.action (fun g q => act g q)
            height cell E₁ E₂ η Cp Clog δ n := by
  dsimp only
  obtain ⟨α, act, μQ, c, hμQ, _, hact, hout, hin, hHaar⟩ :=
    MeasuredCone.polar_action_haar_of_published_realization
      (EG := EG) (G := G) (W := W)
      M F T hunimod eW hExp realize hNbij hDbij dynkinN (transformedPolarCone K A)
      (transformedPolarCone_salient K A hK) D haarQ height hheight
  let : μQ.IsHaarMeasure := hμQ
  obtain ⟨β₂, hβ₂, δ₀, hδ₀, hregions⟩ :=
    D.uniform_polar_regions_of_action M F T hunimod eW
      hExp realize hNbij hDbij dynkinN dynkinD chartN hchartN chartD hchartD
      height hheight hpath hLheight hLip K A haarQ haarI haarD ν bN bI γ₀ hcell hε
      μQ α act hact
  exact ⟨α, act, μQ, c, β₂, hμQ, hact, hout, hin, hHaar, hβ₂, δ₀, hδ₀, hregions⟩

end CartanWordModel
end PolycyclicRecognition

end

end OAI
end

theorem solution : type_of% @OAI.PolycyclicRecognition.CartanWordModel.MeasuredCone.exists_uniform_polar_target_regions_oai := @OAI.PolycyclicRecognition.CartanWordModel.MeasuredCone.exists_uniform_polar_target_regions_oai
