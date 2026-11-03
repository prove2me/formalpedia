-- Prove2me | solution 1 for OAI.PolycyclicRecognition.cartan_unitary_reduced_vanishing
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-03T00:30:13.616703+00:00
-- url     : https://prove2.me/submissions/093e2779-b6d9-4f80-a39a-463acb1f3e4f

import Mathlib
import Definitions.Def_PolycyclicRecognition
import Definitions.Def_OAIQ093D022
import Theorems.Thm_OAI_PolycyclicRecognition_cartan_cocycle_approximation
import Theorems.Thm_OAI_PolycyclicRecognition_cartan_cocycle_polynomial_boxes
import Theorems.Thm_OAI_PolycyclicRecognition_cartan_cover_controlled_pairs
import Theorems.Thm_OAI_PolycyclicRecognition_exponentialLinearRealizationInput_intrinsic

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

variable {G E : Type*} [Group G] [NormedAddCommGroup E]
  [DistribMulAction G E] [IsIsometricSMul G E]

theorem norm_isometric_action (g : G) (v : E) : ‖g • v‖ = ‖v‖ := by
  simpa only [smul_zero, dist_zero_right] using dist_smul g v (0 : E)

omit [IsIsometricSMul G E] in
/-- Coboundary correction preserves the cocycle identity. -/
theorem IsCocycle.corrected {b : G → E} (hb : IsCocycle b) (φ : E) :
    IsCocycle (fun g => b g + g • φ - φ) := by
  intro g h
  dsimp only
  rw [hb g h, mul_smul, smul_sub, smul_add]
  abel

theorem IsCocycle.norm_word_le {b : G → E} (hb : IsCocycle b)
    (Q : Set G) {ε : ℝ} (hQ : ∀ g ∈ Q, ‖b g‖ ≤ ε)
    (l : List G) (hl : ∀ g ∈ l, g ∈ Q) : ‖b l.prod‖ ≤ (l.length : ℝ) * ε := by
  induction l with
  | nil => simp [hb.map_one]
  | cons g l ih =>
    have htail : ∀ h ∈ l, h ∈ Q := fun h hh => hl h (by simp [hh])
    calc
      ‖b (g :: l).prod‖ = ‖b g + g • b l.prod‖ := by rw [List.prod_cons, hb g l.prod]
      _ ≤ ‖b g‖ + ‖g • b l.prod‖ := norm_add_le _ _
      _ = ‖b g‖ + ‖b l.prod‖ := by rw [norm_isometric_action]
      _ ≤ ε + (l.length : ℝ) * ε := add_le_add (hQ g (hl g (by simp))) (ih htail)
      _ = ((g :: l).length : ℝ) * ε := by simp [add_mul] <;> ring

/-- The error of removing a coboundary is at most twice the vector norm,
uniformly over the acting group. -/
theorem norm_le_corrected_add (b : G → E) (φ : E) (g : G) :
    ‖b g‖ ≤ ‖b g + g • φ - φ‖ + 2 * ‖φ‖ := by
  have heq : b g = (b g + g • φ - φ) - g • φ + φ := by abel
  calc
    ‖b g‖ = ‖(b g + g • φ - φ) - g • φ + φ‖ := congrArg norm heq
    _ ≤ ‖(b g + g • φ - φ) - g • φ‖ + ‖φ‖ := norm_add_le _ _
    _ ≤ (‖b g + g • φ - φ‖ + ‖g • φ‖) + ‖φ‖ :=
      add_le_add (norm_sub_le _ _) le_rfl
    _ = _ := by rw [norm_isometric_action]; ring

/-- The concrete word estimate used after reduced cohomology vanishing. The
approximating vector is fixed before the word length tends to infinity. -/
theorem IsCocycle.norm_word_le_of_coboundary {b : G → E} (hb : IsCocycle b)
    (Q : Set G) (φ : E) {ε : ℝ}
    (hQ : ∀ g ∈ Q, ‖b g + g • φ - φ‖ ≤ ε)
    (l : List G) (hl : ∀ g ∈ l, g ∈ Q) :
    ‖b l.prod‖ ≤ (l.length : ℝ) * ε + 2 * ‖φ‖ :=
  (norm_le_corrected_add b φ l.prod).trans
    (add_le_add ((hb.corrected φ).norm_word_le Q hQ l hl) le_rfl)

end PolycyclicRecognition

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_UnitaryCocycle
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Concrete cocycles for bundled unitary representations

The bundled form lets central restriction and quotient descent use their
actual representations without changing ambient scalar-action instances.
-/

noncomputable section

namespace PolycyclicRecognition

variable {G E F : Type*} [Group G]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

theorem IsUnitaryCocycle.map_one {ρ : G →* (E ≃ₗᵢ[ℝ] E)}
    {b : G → E} (hb : IsUnitaryCocycle ρ b) : b 1 = 0 := by
  have h := hb 1 1
  rw [one_mul, ρ.map_one] at h
  change b 1 = b 1 + b 1 at h
  apply add_left_cancel (a := b 1)
  simpa only [add_zero] using h.symm

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_CocycleCombing
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Sublinear cocycles from a nilpotent subgroup and bounded combing

The geometric premise is an explicit product of a bounded number of compact
factors and subgroup factors, with a linear bound on their total subgroup
length. No cohomological conclusion is included in this premise.
-/

noncomputable section

namespace PolycyclicRecognition

open Set

variable {G H E : Type*} [Group G] [Group H]

variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {ρ : G →* (E ≃ₗᵢ[ℝ] E)} {b : G → E}

theorem IsUnitaryCocycle.norm_mul_le (hb : IsUnitaryCocycle ρ b) (g h : G) :
    ‖b (g * h)‖ ≤ ‖b g‖ + ‖b h‖ := by
  rw [hb g h]
  exact (norm_add_le _ _).trans_eq (congrArg (fun t => ‖b g‖ + t) ((ρ g).norm_map _))

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_ConeFacetTemplate
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A fixed polar template near a generator facet

The template radius is independent of the small chart enlargement. Only
its centre moves inward with that enlargement.
-/

noncomputable section
namespace PolycyclicRecognition

open Set

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
  [FiniteDimensional ℝ W]

/-- The Euclidean contact point has strict slack in every other oriented
ray. This is the equality case of the Cauchy--Schwarz inequality. -/
theorem exists_weight_contact_point (α : W →L[ℝ] ℝ) (hα : α ≠ 0) :
    ∃ p : W, ‖p‖ = 1 ∧ α p = ‖α‖ ∧ ∀ β : W →L[ℝ] ℝ, β ≠ 0 →
      (¬ ∃ t : ℝ, 0 < t ∧ β = t • α) → β p < ‖β‖ := by
  let v := (InnerProductSpace.toDual ℝ W).symm α
  have hv : v ≠ 0 := by
    intro h
    apply hα
    simpa [v] using congrArg (InnerProductSpace.toDual ℝ W) h
  have hvnorm : ‖v‖ = ‖α‖ := (InnerProductSpace.toDual ℝ W).symm.norm_map α
  let p := ‖v‖⁻¹ • v
  have hp : ‖p‖ = 1 := by simp [p, norm_smul, norm_ne_zero_iff.mpr hv]
  have heval (β : W →L[ℝ] ℝ) (x : W) :
      inner ℝ ((InnerProductSpace.toDual ℝ W).symm β) x = β x :=
    InnerProductSpace.toDual_symm_apply
  refine ⟨p, hp, ?_, ?_⟩
  · rw [← heval α, show (InnerProductSpace.toDual ℝ W).symm α = v from rfl]
    simp only [p, real_inner_smul_right, real_inner_self_eq_norm_sq]
    rw [← hvnorm]
    field_simp
  · intro β hβ hnot
    let b := (InnerProductSpace.toDual ℝ W).symm β
    have hb : b ≠ 0 := by
      intro h
      apply hβ
      simpa [b] using congrArg (InnerProductSpace.toDual ℝ W) h
    have hbnorm : ‖b‖ = ‖β‖ := (InnerProductSpace.toDual ℝ W).symm.norm_map β
    have hneq : ‖p‖ • b ≠ ‖b‖ • p := by
      intro h
      have hrel : b = (‖b‖ / ‖v‖) • v := by
        simpa [hp, p, smul_smul, div_eq_mul_inv] using h
      apply hnot
      refine ⟨‖b‖ / ‖v‖, div_pos (norm_pos_iff.mpr hb) (norm_pos_iff.mpr hv), ?_⟩
      have hh := congrArg (InnerProductSpace.toDual ℝ W) hrel
      simpa [b, v] using hh
    have hh := inner_lt_norm_mul_iff_real.mpr hneq
    rw [hp, mul_one, hbnorm] at hh
    change inner ℝ ((InnerProductSpace.toDual ℝ W).symm β) p < ‖β‖ at hh
    rwa [heval β p] at hh

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_CocycleHaarAverage
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The defect of a Haar-weighted cocycle average

This is the analytic step of controlled Følner averaging. The weight and
its translates are ordinary scalar functions; their difference, rather than
an assumed cohomology conclusion, bounds the averaged affine displacement.
-/

noncomputable section
namespace PolycyclicRecognition

open MeasureTheory

variable {G E : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {ρ : G →* (E ≃ₗᵢ[ℝ] E)} {b : G → E}
  (μ : Measure G) [μ.IsMulLeftInvariant]

theorem IsUnitaryCocycle.haar_weighted_average
    (hb : IsUnitaryCocycle ρ b) (f : G → ℝ)
    (hf : Integrable f μ) (hfb : Integrable (fun x => f x • b x) μ)
    (hmass : ∫ x, f x ∂μ = 1) (q : G)
    (hqfb : Integrable (fun x => f (q⁻¹ * x) • b x) μ) :
    b q + ρ q (∫ x, f x • b x ∂μ) - (∫ x, f x • b x ∂μ) =
      ∫ x, (f (q⁻¹ * x) - f x) • b x ∂μ := by
  have hlinear : Integrable (fun x => ρ q (f x • b x)) μ :=
    (ρ q).toContinuousLinearEquiv.toContinuousLinearMap.integrable_comp hfb
  have hid : ∫ x, f x • b (q * x) ∂μ =
      b q + ρ q (∫ x, f x • b x ∂μ) := by
    simp_rw [hb q, smul_add, ← map_smul]
    rw [integral_add (hf.smul_const (b q)) hlinear, integral_smul_const, hmass, one_smul]
    exact congrArg (fun v => b q + v)
      ((ρ q).toLinearIsometry.integral_comp_comm (fun x => f x • b x))
  have htranslate : ∫ x, f x • b (q * x) ∂μ =
      ∫ x, f (q⁻¹ * x) • b x ∂μ := by
    simpa only [inv_mul_cancel_left] using
      integral_mul_left_eq_self (μ := μ) (fun x => f (q⁻¹ * x) • b x) q
  rw [← hid, htranslate, ← integral_sub hqfb hfb]
  exact integral_congr_ae (Filter.Eventually.of_forall (fun x => (sub_smul _ _ _).symm))

theorem IsUnitaryCocycle.norm_haar_weighted_average_le
    (hb : IsUnitaryCocycle ρ b) (f : G → ℝ)
    (hf : Integrable f μ) (hfb : Integrable (fun x => f x • b x) μ)
    (hmass : ∫ x, f x ∂μ = 1) (q : G)
    (hqfb : Integrable (fun x => f (q⁻¹ * x) • b x) μ)
    (hdf : Integrable (fun x => |f (q⁻¹ * x) - f x|) μ)
    {M : ℝ} (hM : ∀ x, f (q⁻¹ * x) - f x ≠ 0 → ‖b x‖ ≤ M) :
    ‖b q + ρ q (∫ x, f x • b x ∂μ) - (∫ x, f x • b x ∂μ)‖ ≤
      M * ∫ x, |f (q⁻¹ * x) - f x| ∂μ := by
  rw [hb.haar_weighted_average μ f hf hfb hmass q hqfb, ← integral_const_mul]
  apply (norm_integral_le_integral_norm _).trans
  apply integral_mono_ae
    (by simpa only [Pi.sub_apply, ← sub_smul] using (hqfb.sub hfb).norm) (hdf.const_mul M)
  apply Filter.Eventually.of_forall
  intro x
  dsimp only
  by_cases hx : f (q⁻¹ * x) - f x = 0
  · simp only [hx, zero_smul, norm_zero, abs_zero, mul_zero, le_refl]
  · rw [norm_smul, Real.norm_eq_abs, mul_comm M]
    exact mul_le_mul_of_nonneg_left (hM x hx) (abs_nonneg _)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_ControlledReiterCocycles
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instNonemptyBases _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_nonempty _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Controlled scalar averages turn sublinear cocycles into coboundaries

The geometric data are compactly supported probability densities with
translation error of order inverse scale and support of order scale.
They contain no representation or cohomology hypotheses.
-/

noncomputable section
namespace PolycyclicRecognition

open MeasureTheory Filter

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G]

variable (μ : Measure G) [μ.IsMulLeftInvariant] [IsFiniteMeasureOnCompacts μ]
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {ρ : G →* (E ≃ₗᵢ[ℝ] E)} {b : G → E}

theorem ControlledReiterFamily.almost_coboundary
    {length : G → ℝ} (F : ControlledReiterFamily μ length)
    (hbc : Continuous b) (hb : IsUnitaryCocycle ρ b)
    (hsub : ∀ δ : ℝ, 0 < δ → ∃ B : ℝ, 0 ≤ B ∧
      ∀ g, ‖b g‖ ≤ δ * length g + B)
    (Q : Set G) (hQ : IsCompact Q) {ε : ℝ} (hε : 0 < ε) :
    ∃ φ : E, ∀ q ∈ Q, ‖b q + ρ q φ - φ‖ ≤ ε := by
  obtain ⟨A, C, hA, hC, hcontrol⟩ := F.control Q hQ
  let δ := ε / (2 * (A * C + 1))
  have hδ : 0 < δ := div_pos hε (by positivity)
  obtain ⟨B, hB, hbound⟩ := hsub δ hδ
  have hsmall : δ * A * C ≤ ε / 2 := by
    have he : δ * (2 * (A * C + 1)) = ε :=
      div_mul_cancel₀ _ (by positivity)
    nlinarith
  obtain ⟨n, hn, hcn⟩ := ((F.scale_tendsto.eventually
    (eventually_ge_atTop (2 * B * C / ε))).and hcontrol).exists
  let f := F.weight n
  have hf : Continuous f := F.continuous_weight n
  have hfc : HasCompactSupport f := F.compact_support n
  have hfi : Integrable f μ := hf.integrable_of_hasCompactSupport hfc
  have hfbi : Integrable (fun x => f x • b x) μ :=
    (hf.smul hbc).integrable_of_hasCompactSupport hfc.smul_right
  refine ⟨∫ x, f x • b x ∂μ, fun q hq => ?_⟩
  have hft : Continuous (fun x => f (q⁻¹ * x)) := hf.comp (continuous_const.mul continuous_id)
  have hftc : HasCompactSupport (fun x => f (q⁻¹ * x)) :=
    hfc.comp_homeomorph (Homeomorph.mulLeft q⁻¹)
  have hftbi : Integrable (fun x => f (q⁻¹ * x) • b x) μ :=
    (hft.smul hbc).integrable_of_hasCompactSupport hftc.smul_right
  have hdfi : Integrable (fun x => |f (q⁻¹ * x) - f x|) μ :=
    (hft.sub hf).abs.integrable_of_hasCompactSupport (hftc.sub hfc).abs
  obtain ⟨hsupport, herror⟩ := hcn q hq
  have hlocal (x : G) (hx : f (q⁻¹ * x) - f x ≠ 0) :
      ‖b x‖ ≤ δ * (A * F.scale n) + B :=
    (hbound x).trans (add_le_add
      (mul_le_mul_of_nonneg_left (hsupport x hx) hδ.le) le_rfl)
  have h := hb.norm_haar_weighted_average_le μ f hfi hfbi (F.mass n) q hftbi hdfi hlocal
  have hR := F.scale_pos n
  have hBR : B * C / F.scale n ≤ ε / 2 := by
    apply (div_le_iff₀ hR).2
    have ht := (div_le_iff₀ hε).1 hn
    nlinarith
  calc
    _ ≤ (δ * (A * F.scale n) + B) *
        (∫ x, |f (q⁻¹ * x) - f x| ∂μ) := h
    _ ≤ (δ * (A * F.scale n) + B) * (C / F.scale n) :=
      mul_le_mul_of_nonneg_left herror (by positivity)
    _ = δ * A * C + B * C / F.scale n := by field_simp
    _ ≤ ε := by linarith

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

variable {I L : Type*} [LieRing L] [LieAlgebra ℝ L]
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
theorem repr_exponentialRescaleBasis_bracket {J : Type*}
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

variable {I : Type*} [Fintype I] [DecidableEq I]

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
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_NilpotentChartCountability
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_countable _root_.OAI.PolycyclicRecognition.finitelyGeneratedSubgroupIndex_countable _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Countability and Haar measure on the chosen nilpotent factors -/

noncomputable section
namespace PolycyclicRecognition.NilpotentLieModel

open Module MeasureTheory
open scoped Manifold

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] (N : NilpotentLieModel L)

/-- The actual exponential chart transports the countable topology of a
finite-dimensional real vector space to the selected factor. -/
theorem secondCountable_of_chart
    (chart : GroupLieAlgebra (𝓘(ℝ, N.modelSpace)) N.carrier ≃ₜ N.carrier) :
    SecondCountableTopology N.carrier := by
  let : SecondCountableTopology (GroupLieAlgebra (𝓘(ℝ, N.modelSpace)) N.carrier) :=
    (finBasis ℝ _).equivFunL.toHomeomorph.secondCountableTopology
  exact chart.symm.isEmbedding.secondCountableTopology

end PolycyclicRecognition.NilpotentLieModel

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

variable {G W : Type*} [Group G] [MetricSpace G] [IsIsometricSMul G G]
  [NormedAddCommGroup W]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [ChartedSpace E G] [LieGroup (𝓘(ℝ, E)) ⊤ G]
  [ProperSpace G]

/-- The finite list of basis brackets always has a common bound. -/
theorem exists_basis_structureConstant_bound {L : Type*} [LieRing L] [LieAlgebra ℝ L]
    {J : Type*} [Fintype J] (b : Basis J ℝ L) :
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
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanGroupBoxes
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instDecidableEqConeMixedWords _root_.OAI.PolycyclicRecognition.CartanWordModel.instFintypeConeMixedWords _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual group boxes for the Cartan word model

The finite Cartan construction supplies the bases, bracket bounds, nilpotence
and support exponents used here. The only external group facts are the two
explicit published exponential inputs. In particular no box multiplication or
volume estimate is an assumption.
-/

noncomputable section

namespace PolycyclicRecognition.CartanWordModel

open Module LieModule MeasureTheory
open scoped Manifold

variable {L W : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {H : LieSubalgebra ℝ L} [H.IsCartanSubalgebra] (M : CartanWordModel H)
  {a : ℕ} (T : TriangularAdjoint L a)
  (hunimod : ∀ x : L, LinearMap.trace ℝ L (LieAlgebra.ad ℝ L x) = 0)
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)

variable {EN N : Type*} [NormedAddCommGroup EN] [NormedSpace ℝ EN]
  [FiniteDimensional ℝ EN] [TopologicalSpace N] [ChartedSpace EN N] [Group N]
  [LieGroup (𝓘(ℝ, EN)) ⊤ N] [T2Space N]
  (eN : cartanRootIdeal H ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, EN)) N)
  (Exp : GroupLieAlgebra (𝓘(ℝ, EN)) N → N) (hExp : IsGroupExponential Exp)

include hExp

set_option maxHeartbeats 1000000 in
/-- A uniform product estimate for the actual Cartan boxes. No assumptions
about compactness or convexity of the template are needed for this part. -/
theorem exists_groupBox_product_bound
    (dynkin : NilpotentDynkinExpansionInput EN N)
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (E : Set W) (β : M.Bases),
      IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
        (M.boxCost T hunimod eW E) β.val →
      ∀ r : ℝ, 0 ≤ r → ∀ n : ℕ, ∀ R : ℝ, 0 ≤ R → ∀ g : Fin n → N,
      (∀ i, g i ∈ M.groupBox T hunimod eW (Exp ∘ eN) E β r R) →
      (List.ofFn g).prod ∈ M.groupBox T hunimod eW (Exp ∘ eN) E β r
        (C * (1 + (n : ℝ)) ^ M.bound * (1 + R) ^ M.bound) := by
  obtain ⟨C, hC, hbound⟩ := exists_uniform_word_box_product_bound dynkin eN Exp hExp
    M.letter M.bound_zero b₀
  exact ⟨C, hC, fun E β hβ r hr n R hR g hg =>
    hbound ((M.supportIn T hunimod eW).weightSupport E) β hβ r hr n R hR g hg⟩

end PolycyclicRecognition.CartanWordModel

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
    {V J : Type*} [AddCommGroup V] [Module ℝ V] [DecidableEq J]
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

variable {L W : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
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

variable {I L : Type*} [LieRing L] [LieAlgebra ℝ L] [Fintype I] [DecidableEq I]

namespace CartanWordModel

variable [FiniteDimensional ℝ L]
  {H : LieSubalgebra ℝ L} [H.IsCartanSubalgebra] (M : CartanWordModel H)
  {n : ℕ} (T : TriangularAdjoint L n)
  (hunimod : ∀ x : L, LinearMap.trace ℝ L (LieAlgebra.ad ℝ L x) = 0)
  {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
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

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]

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
    {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [NormOneClass A]
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

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
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

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {n : ℕ} (T : TriangularAdjoint L n)
  (H : LieSubalgebra ℝ L) [H.IsCartanSubalgebra] (χ : Weight ℝ H L) (hχ : χ.IsNonZero)

attribute [local instance] OAI.PolycyclicRecognition.instNormedAddCommGroupSubtypeMemLieSubmoduleRealLieSubalgebraRootSpaceCoeWeight_solutions_1
attribute [local instance] OAI.PolycyclicRecognition.instNormedSpaceRealSubtypeMemLieSubmoduleLieSubalgebraRootSpaceCoeWeight_solutions_1
local instance instNontrivialSubtypeMemLieSubmoduleRealLieSubalgebraRootSpaceCoeWeight_solutions_1_r5db84d_1 : Nontrivial (rootSpace H χ) :=
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

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
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
local instance instNontrivialSubtypeMemLieSubmoduleRealLieSubalgebraRootSpaceCoeWeight_solutions_2_r5db84d_1 : Nontrivial (rootSpace H χ) :=
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
local instance instNontrivialSubtypeMemLieSubmoduleRealLieSubalgebraRootSpaceCoeWeight_solutions_2_r5db84d_2 : Nontrivial (rootSpace H χ) :=
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
    {V I J : Type*} [AddCommGroup V] [Module ℝ V] [Fintype I] [Fintype J]
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

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {H : LieSubalgebra ℝ L} [H.IsCartanSubalgebra] (M : CartanWordModel H)
  {n : ℕ} (T : TriangularAdjoint L n)
  (hunimod : ∀ x : L, LinearMap.trace ℝ L (ad ℝ L x) = 0)
  {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
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
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanControlledProducts
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instDecidableEqConeMixedWords _root_.OAI.PolycyclicRecognition.CartanWordModel.instFintypeConeMixedWords _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.CartanFactorModel.heightRay_zero _root_.OAI.PolycyclicRecognition.CartanFactorModel.realScaleProfile_apply _root_.OAI.PolycyclicRecognition.CartanFactorModel.sampledProbeProfile_apply _root_.OAI.PolycyclicRecognition.bracketWordDifferential_mul _root_.OAI.PolycyclicRecognition.cartanWeightDerivation_apply_root _root_.OAI.PolycyclicRecognition.chartExponentialFlow_zero _root_.OAI.PolycyclicRecognition.derivationSemidirectHom_apply _root_.OAI.PolycyclicRecognition.exponentialHomOfDynkin_apply_exp _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.nilshadowWeightDerivation_symm _root_.OAI.PolycyclicRecognition.nilshadowWeightOperator_symm _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial bounds for products of controlled Cartan increments

Each increment begins in a fixed nilpotent coordinate box. Its Cartan height
lies in a scaled template, and its Cartan logarithm has a polynomial bound.
The resulting product remains in the template box with polynomial radius.
All constants are uniform over templates, maximizing bases and scales.
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
  (Exp : GroupLieAlgebra (𝓘(ℝ, EN)) N → N) (hExp : IsGroupExponential Exp)
  (hbij : Function.Bijective Exp) (dynkin : NilpotentDynkinExpansionInput EN N)

set_option maxHeartbeats 1000000 in
/-- A controlled Cartan action takes an unscaled box into the template box. -/
theorem exists_controlled_adjoint_group_bound
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H)) :
    ∃ (A : ℝ) (p : ℕ), 0 ≤ A ∧ ∀ {E : Set W}, IsCompact E → E.Nonempty →
      ∀ β : M.Bases,
      IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
        (M.boxCost T hunimod eW E) β.val →
      ∀ (γ : M.Bases) (r : ℝ), 0 ≤ r → ∀ (h : H) (w : W), w ∈ E →
      eW (heightProjection T.character (h : L)) = r • w → ∀ (R : ℝ) (g : N),
      g ∈ exponentialCoordinateBox (Exp ∘ eN)
        (WordBasisSelections.basis M.letter M.wordList γ) R →
      M.adjointGroupAutomorphism T eN Exp hExp hbij dynkin h g ∈
        M.groupBox T hunimod eW (Exp ∘ eN) E β r
          (A * (1 + ‖(Module.finBasis ℝ H).equivFun h‖) ^ p * R) := by
  obtain ⟨A, p, hA, hb⟩ := M.exists_controlled_adjoint_bound T hunimod eW b₀
  refine ⟨A, p, hA, ?_⟩
  intro E hE hne β hβ γ r hr h w hw hh R g hg
  obtain ⟨x, rfl, hx⟩ := hg
  refine ⟨cartanIdealAdjointAutomorphism T H h x, ?_, ?_⟩
  · exact (integrateNilpotentLieEquiv_apply_exp eN Exp hbij dynkin hExp M.bound_zero
      (cartanIdealAdjointAutomorphism T H h) x).symm
  · exact (hb hE hne β hβ γ r hr h w hw hh x).trans
      (mul_le_mul_of_nonneg_left hx (mul_nonneg hA (pow_nonneg (by positivity) _)))

set_option maxHeartbeats 1000000 in
/-- Polynomial Cartan logarithms give a polynomial radius for the full
product, even when the height template and scale vary. -/
theorem exists_controlled_product_bound
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    {B R : ℝ} (hB : 0 ≤ B) (hR : 0 ≤ R) (k : ℕ) :
    ∃ (C : ℝ) (q : ℕ), 0 ≤ C ∧ ∀ {E : Set W}, IsCompact E → E.Nonempty →
      ∀ β : M.Bases,
      IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
        (M.boxCost T hunimod eW E) β.val →
      ∀ (γ : M.Bases) (r : ℝ), 0 ≤ r → ∀ (m : ℕ) (h : Fin m → H) (w : Fin m → W),
      (∀ i, w i ∈ E) →
      (∀ i, eW (heightProjection T.character (h i : L)) = r • w i) →
      (∀ i, ‖(Module.finBasis ℝ H).equivFun (h i)‖ ≤ B * (1 + (m : ℝ)) ^ k) →
      ∀ g : Fin m → N,
      (∀ i, g i ∈ exponentialCoordinateBox (Exp ∘ eN)
        (WordBasisSelections.basis M.letter M.wordList γ) R) →
      (List.ofFn (fun i => M.adjointGroupAutomorphism T eN Exp hExp hbij dynkin (h i) (g i))).prod ∈
        M.groupBox T hunimod eW (Exp ∘ eN) E β r (C * (1 + (m : ℝ)) ^ q) := by
  obtain ⟨A, p, hA, hact⟩ :=
    M.exists_controlled_adjoint_group_bound T hunimod eW eN Exp hExp hbij dynkin b₀
  obtain ⟨C, hC, hprod⟩ := M.exists_groupBox_product_bound T hunimod eW eN Exp hExp dynkin b₀
  let D := A * (1 + B) ^ p * R
  have hD : 0 ≤ D := by dsimp [D] <;> positivity
  refine ⟨C * (1 + D) ^ M.bound, M.bound + (k * p) * M.bound, by positivity, ?_⟩
  intro E hE hne β hβ γ r hr m h w hw hh hlog g hg
  let s : ℝ := 1 + (m : ℝ)
  have hs : 1 ≤ s := le_add_of_nonneg_right (Nat.cast_nonneg _)
  have hsp : 1 ≤ s ^ k := one_le_pow₀ hs
  have hinc (i : Fin m) : M.adjointGroupAutomorphism T eN Exp hExp hbij dynkin (h i) (g i) ∈
      M.groupBox T hunimod eW (Exp ∘ eN) E β r (D * s ^ (k * p)) := by
    obtain ⟨x, hx, hbound⟩ := hact hE hne β hβ γ r hr (h i) (w i) (hw i) (hh i) R (g i) (hg i)
    refine ⟨x, hx, hbound.trans ?_⟩
    have hi : 1 + ‖(Module.finBasis ℝ H).equivFun (h i)‖ ≤ (1 + B) * s ^ k := by
      have hi := hlog i
      change ‖(Module.finBasis ℝ H).equivFun (h i)‖ ≤ B * s ^ k at hi
      nlinarith
    calc
      _ ≤ A * ((1 + B) * s ^ k) ^ p * R := by gcongr
      _ = _ := by rw [mul_pow, ← pow_mul]; ring
  obtain ⟨x, hx, hbound⟩ := hprod E β hβ r hr m (D * s ^ (k * p))
    (mul_nonneg hD (pow_nonneg (by linarith) _))
    (fun i => M.adjointGroupAutomorphism T eN Exp hExp hbij dynkin (h i) (g i)) hinc
  refine ⟨x, hx, hbound.trans ?_⟩
  have hsp' : 1 ≤ s ^ (k * p) := one_le_pow₀ hs
  have hsum : 1 + D * s ^ (k * p) ≤ (1 + D) * s ^ (k * p) := by nlinarith
  calc
    _ ≤ C * s ^ M.bound * ((1 + D) * s ^ (k * p)) ^ M.bound := by gcongr
    _ = _ := by rw [mul_pow, ← pow_mul, pow_add]; ring

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanWordLogarithms
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.chartExponentialFlow_zero _root_.OAI.PolycyclicRecognition.derivationSemidirectHom_apply _root_.OAI.PolycyclicRecognition.exponentialHomOfDynkin_apply_exp _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
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
theorem wordPrefix_succ {G : Type*} [Monoid G] (u : ℕ → G) (m : ℕ) :
    wordPrefix u (m + 1) = wordPrefix u m * u m := by
  unfold wordPrefix
  rw [List.ofFn_succ', List.prod_concat]
  rfl

set_option maxHeartbeats 1000000 in
theorem semidirect_wordPrefix_right {N D : Type*} [Group N] [Group D]
    (φ : D →* MulAut N) (u : ℕ → N) (v : ℕ → D) (m : ℕ) :
    (wordPrefix (fun i => (⟨u i, v i⟩ : N ⋊[φ] D)) m).right = wordPrefix v m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [wordPrefix_succ, SemidirectProduct.mul_right, ih, wordPrefix_succ]

set_option maxHeartbeats 1000000 in
/-- The nilpotent component of a semidirect word is the ordered product of
the nilpotent increments acted on by the actual Cartan prefixes. -/
theorem semidirect_wordPrefix_left {N D : Type*} [Group N] [Group D]
    (φ : D →* MulAut N) (u : ℕ → N) (v : ℕ → D) (m : ℕ) :
    (wordPrefix (fun i => (⟨u i, v i⟩ : N ⋊[φ] D)) m).left =
      wordPrefix (fun i => φ (wordPrefix v i) (u i)) m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [wordPrefix_succ, SemidirectProduct.mul_left, ih,
      semidirect_wordPrefix_right, wordPrefix_succ]

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

set_option maxHeartbeats 1000000 in
/-- Bounded Cartan increments have polynomial logarithmic coordinates.
The nilpotence bound comes from the Cartan subalgebra itself. -/
theorem exists_cartan_word_log_bound
    (hExpD : IsGroupExponential ExpD) (dynkinD : NilpotentDynkinExpansionInput ED D)
    {R : ℝ} (hR : 0 ≤ R) :
    ∃ (A : ℝ) (c : ℕ), 0 ≤ A ∧ ∀ (u : ℕ → D) (m : ℕ),
      (∀ i < m, u i ∈ exponentialCoordinateBox (ExpD ∘ eD) (finBasis ℝ H) R) →
      ‖(finBasis ℝ H).equivFun (cartanLog H eD ExpD hbijD (wordPrefix u m))‖ ≤
        A * (1 + (m : ℝ)) ^ c := by
  obtain ⟨c, hc⟩ := LieModule.IsNilpotent.nilpotent ℝ H H
  obtain ⟨K, hK, hbracket⟩ := exists_basis_structureConstant_bound (finBasis ℝ H)
  let A : ℝ := (c : ℝ) * 2 ^ c *
    (1 + (finrank ℝ H : ℝ) ^ 2 * K) ^ c * (1 + R) ^ c
  refine ⟨A, c, by dsimp [A] <;> positivity, ?_⟩
  intro u m hu
  obtain ⟨x, hx, hbound⟩ := product_mem_exponentialCoordinateBox dynkinD eD ExpD hExpD hc
    (finBasis ℝ H) hK hR hbracket (fun i : Fin m => u i.val) (fun i => hu i.val i.isLt)
  change ExpD (eD x) = wordPrefix u m at hx
  rw [← hx, cartanLog_exp]
  simpa only [Fintype.card_fin, A] using hbound

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_CocycleCompactWords
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Height and cocycle bounds on compact words -/

noncomputable section
namespace PolycyclicRecognition

theorem norm_height_wordPrefix_le {G W : Type*} [Group G]
    [NormedAddCommGroup W] (π : G →* Multiplicative W)
    (u : ℕ → G) (m : ℕ) {R : ℝ}
    (hu : ∀ i < m, ‖(π (u i)).toAdd‖ ≤ R) :
    ‖(π (wordPrefix u m)).toAdd‖ ≤ (m : ℝ) * R := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [wordPrefix_succ, map_mul]
    change ‖(π (wordPrefix u m)).toAdd + (π (u m)).toAdd‖ ≤ _
    calc
      _ ≤ ‖(π (wordPrefix u m)).toAdd‖ + ‖(π (u m)).toAdd‖ := norm_add_le _ _
      _ ≤ (m : ℝ) * R + R :=
        add_le_add (ih (fun i hi => hu i (Nat.lt_succ_of_lt hi))) (hu m (Nat.lt_succ_self m))
      _ = _ := by push_cast <;> ring

variable {G D E : Type*} [Group G] [Group D]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {ρ : G →* (E ≃ₗᵢ[ℝ] E)} {b : G → E}

theorem IsUnitaryCocycle.norm_mapped_wordPrefix_le_of_coboundary
    (hb : IsUnitaryCocycle ρ b) (i : D →* G) (Q : Set D) (φ : E) {δ : ℝ}
    (hQ : ∀ d ∈ Q, ‖b (i d) + ρ (i d) φ - φ‖ ≤ δ)
    (u : ℕ → D) (m : ℕ) (hu : ∀ j < m, u j ∈ Q) :
    ‖b (i (wordPrefix u m))‖ ≤ (m : ℝ) * δ + 2 * ‖φ‖ := by
  let := unitaryDistribMulAction ρ
  let : IsIsometricSMul G E := ⟨fun g => (ρ g).isometry⟩
  have h := IsCocycle.norm_word_le_of_coboundary hb (i '' Q) φ
    (by rintro g ⟨d, hd, rfl⟩; exact hQ d hd)
    ((List.ofFn (fun j : Fin m => u j.val)).map i) (by
      intro g hg
      obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hg
      obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hd
      exact ⟨u j, hu j j.isLt, rfl⟩)
  simpa only [List.length_map, List.length_ofFn, ← map_list_prod, wordPrefix] using h

omit [InnerProductSpace ℝ E] in
theorem sublinear_of_compact_word_estimates (b : G → E) (K : Set G)
    (hsub : ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, 0 ≤ B ∧ ∀ (u : ℕ → G) (m : ℕ),
      (∀ i < m, u i ∈ K) → ‖b (wordPrefix u m)‖ ≤ ε * (m : ℝ) + B)
    (length : G → ℝ) (hlen : ∀ g, 0 ≤ length g) {a : ℝ} (ha : 0 ≤ a)
    (hword : ∀ g, ∃ l : List G, (∀ q ∈ l, q ∈ K) ∧ l.prod = g ∧
      (l.length : ℝ) ≤ a * length g + a) :
    ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, 0 ≤ B ∧ ∀ g, ‖b g‖ ≤ ε * length g + B := by
  classical
  intro ε hε
  let δ := ε / (a + 1)
  have hδ : 0 < δ := div_pos hε (by positivity)
  obtain ⟨B, hB, hb⟩ := hsub δ hδ
  have hcoef : δ * a ≤ ε := by
    have he : δ * (a + 1) = ε := div_mul_cancel₀ _ (by positivity)
    nlinarith
  refine ⟨δ * a + B, by positivity, fun g => ?_⟩
  obtain ⟨l, hl, he, hn⟩ := hword g
  let u : ℕ → G := fun i => if h : i < l.length then l[i] else 1
  have hprod : wordPrefix u l.length = g := by
    rw [wordPrefix, show List.ofFn (fun i : Fin l.length => u i.val) = l from ?_, he]
    simpa only [u, dite_eq_left, Fin.isLt] using (List.ofFn_getElem (xs := l))
  have hbound := hb u l.length (fun i hi => by
    simpa only [u, dite_eq_left hi] using hl l[i] (List.getElem_mem hi))
  rw [hprod] at hbound
  calc
    ‖b g‖ ≤ δ * (l.length : ℝ) + B := hbound
    _ ≤ δ * (a * length g + a) + B :=
      add_le_add (mul_le_mul_of_nonneg_left hn hδ.le) le_rfl
    _ = (δ * a) * length g + (δ * a + B) := by ring
    _ ≤ ε * length g + (δ * a + B) :=
      add_le_add (mul_le_mul_of_nonneg_right hcoef (hlen g)) le_rfl

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_MetricChainWords
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Bounded words from the published large-scale chain metric -/

noncomputable section
namespace PolycyclicRecognition

open Metric Set

/-- Consecutive group differences telescope to the original element. The
published chain metric suffices; minimizing paths are unnecessary. -/
theorem LinearMetricChains.wordFactorization
    {G : Type*} [Group G] [MetricSpace G] [IsIsometricSMul G G]
    (C : LinearMetricChains G) (g : G) :
    ∃ w : List G, (∀ q ∈ w, q ∈ closedBall 1 C.step) ∧ w.prod = g ∧
      (w.length : ℝ) ≤ C.slope * dist 1 g + C.error := by
  obtain ⟨n, p, hp0, hpn, hn, hp⟩ := C.chain 1 g
  let w := (List.range n).map (fun k => (p k)⁻¹ * p (k + 1))
  refine ⟨w, ?_, ?_, ?_⟩
  · intro q hq
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hq
    rw [mem_closedBall, dist_comm, dist_one_groupDifference]
    exact hp k (List.mem_range.mp hk)
  · have he := List.prod_range_div' n (fun k => (p k)⁻¹)
    simpa only [w, div_eq_mul_inv, inv_inv, hp0, hpn, inv_one, one_mul] using he
  · simpa only [w, List.length_map, List.length_range] using hn

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
@[simp] theorem map_wordPrefix {A B : Type*} [Monoid A] [Monoid B]
    (f : A →* B) (u : ℕ → A) (m : ℕ) :
    f (wordPrefix u m) = wordPrefix (fun i => f (u i)) m := by
  induction m with
  | zero => simp only [wordPrefix_zero, map_one]
  | succ m ih => simp only [wordPrefix_succ, map_mul, ih]

set_option maxHeartbeats 1000000 in
/-- A fixed set of possible lifts supplies compatible lifts of every finite
word, with all prefix equalities retained. -/
theorem exists_lifted_word_prefixes {A B : Type*} [Monoid A] [Monoid B]
    (f : A →* B) (C : Set A) (K : Set B) (hK : K ⊆ f '' C)
    (u : ℕ → B) (m : ℕ) (hu : ∀ i < m, u i ∈ K) :
    ∃ v : ℕ → A, (∀ i < m, v i ∈ C) ∧
      ∀ j ≤ m, f (wordPrefix v j) = wordPrefix u j := by
  choose w hwC hwf using (fun i : Fin m => hK (hu i.val i.isLt))
  let v : ℕ → A := fun i => if h : i < m then w ⟨i, h⟩ else 1
  have hvC (i : ℕ) (hi : i < m) : v i ∈ C := by
    simpa only [v, dite_eq_left hi] using hwC ⟨i, hi⟩
  have hvf (i : ℕ) (hi : i < m) : f (v i) = u i := by
    simpa only [v, dite_eq_left hi] using hwf ⟨i, hi⟩
  refine ⟨v, hvC, ?_⟩
  intro j hj
  induction j with
  | zero => simp only [wordPrefix_zero, map_one]
  | succ j ih =>
    rw [wordPrefix_succ, map_mul, ih (Nat.le_of_succ_le hj),
      hvf j (Nat.lt_of_succ_le hj), wordPrefix_succ]

open scoped Manifold

variable {EG G : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G]
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  {ExpG : GroupLieAlgebra (𝓘(ℝ, EG)) G → G}
  (F : CartanFactorModel H ExpG)

set_option maxHeartbeats 1000000 in
/-- The actual ambient compact increments lift into one compact factor set,
uniformly over word length. All intermediate positions are reproduced. -/
theorem exists_compact_cartan_word_lifts {K : Set G} (hK : IsCompact K) :
    ∃ C : Set (F.N.carrier × F.D.carrier), IsCompact C ∧
      ∀ (u : ℕ → G) (m : ℕ), (∀ i < m, u i ∈ K) →
      ∃ (v : ℕ → F.N.carrier) (w : ℕ → F.D.carrier),
        (∀ i < m, (v i, w i) ∈ C) ∧
        ∀ j ≤ m, F.inclusionN
            (wordPrefix (fun i => (⟨v i, w i⟩ : F.N.carrier ⋊[F.action] F.D.carrier)) j).left *
          F.inclusionD (wordPrefix w j) = wordPrefix u j := by
  obtain ⟨C, hC, hcover⟩ := F.compactLifts K hK
  let q := cartanMultiplication F.inclusionN F.inclusionD F.action F.conjugation
  let C' : Set (F.N.carrier ⋊[F.action] F.D.carrier) :=
    {z | (z.left, z.right) ∈ C}
  have hcover' : K ⊆ q '' C' := by
    intro g hg
    obtain ⟨⟨n, d⟩, hnd, hprod⟩ := hcover hg
    exact ⟨⟨n, d⟩, hnd, hprod⟩
  refine ⟨C, hC, ?_⟩
  intro u m hu
  obtain ⟨z, hz, hprefix⟩ := exists_lifted_word_prefixes q C' K hcover' u m hu
  refine ⟨fun i => (z i).left, fun i => (z i).right, hz, ?_⟩
  intro j hj
  have he : (fun i => (⟨(z i).left, (z i).right⟩ : F.N.carrier ⋊[F.action] F.D.carrier)) = z := by
    funext i
    exact SemidirectProduct.ext rfl rfl
  rw [← semidirect_wordPrefix_right F.action (fun i => (z i).left)
    (fun i => (z i).right) j, he]
  exact hprefix j hj

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_CocyclePullbackSublinear
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Pulling compact-word sublinearity to a proper chain metric -/

noncomputable section
namespace PolycyclicRecognition

open Metric Set

variable {G H E : Type*} [Group G] [Group H] [TopologicalSpace G]
  [MetricSpace H] [IsIsometricSMul H H] [ProperSpace H] [NormedAddCommGroup E]

/-- A continuous homomorphism maps a compact generating ball to a compact
set. Its pulled-back cocycle inherits the metric sublinearity estimate. -/
theorem sublinear_comp_of_compact_word_estimates
    (f : H →* G) (hf : Continuous f) (b : G → E) (C : LinearMetricChains H)
    (hsub : ∀ K : Set G, IsCompact K →
      ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, 0 ≤ B ∧ ∀ (u : ℕ → G) (m : ℕ),
        (∀ i < m, u i ∈ K) → ‖b (wordPrefix u m)‖ ≤ ε * (m : ℝ) + B) :
    ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, 0 ≤ B ∧ ∀ h, ‖b (f h)‖ ≤ ε * dist 1 h + B := by
  let K : Set H := closedBall 1 C.step
  have hK : IsCompact K := isCompact_closedBall 1 C.step
  have hs : ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, 0 ≤ B ∧ ∀ (u : ℕ → H) (m : ℕ),
      (∀ i < m, u i ∈ K) → ‖(b ∘ f) (wordPrefix u m)‖ ≤ ε * (m : ℝ) + B := by
    intro ε hε
    obtain ⟨B, hB, hb⟩ := hsub (f '' K) (hK.image hf) ε hε
    refine ⟨B, hB, fun u m hu => ?_⟩
    simpa only [Function.comp_apply, map_wordPrefix] using
      hb (fun i => f (u i)) m (fun i hi => ⟨u i, hu i hi, rfl⟩)
  apply sublinear_of_compact_word_estimates (b ∘ f) K hs (fun h => dist 1 h)
    (fun _ => dist_nonneg) (a := C.slope + C.error) (add_nonneg C.slope_nonneg C.error_nonneg)
  intro h
  obtain ⟨l, hl, he, hn⟩ := C.wordFactorization h
  refine ⟨l, hl, he, hn.trans ?_⟩
  nlinarith [C.slope_nonneg, C.error_nonneg,
    mul_nonneg C.error_nonneg (dist_nonneg (x := (1 : H)) (y := h))]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_InvariantMetrization
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instNonemptyBases _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_nonempty _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A compatible left-invariant metric

Take the supremum of the bounded metric over left translations. The left
uniformity makes this supremum compatible with the original topology.
This supplies the metrization step in the proper chain-metric construction.
-/

noncomputable section
namespace PolycyclicRecognition

open Set Filter Metric Topology
open scoped Uniformity

variable {G : Type*} [Group G] [MetricSpace G]

theorem leftInvariantDistance_le_one (x y : G) : leftInvariantDistance x y ≤ 1 :=
  ciSup_le (fun _ => min_le_left _ _)

theorem leftInvariantDistance_mul_left (g x y : G) :
    leftInvariantDistance (g * x) (g * y) = leftInvariantDistance x y := by
  apply le_antisymm
  · apply ciSup_le
    intro h
    simpa only [mul_assoc, leftInvariantDistance] using le_ciSup (translateDistance_bdd x y) (h * g)
  · apply ciSup_le
    intro h
    simpa only [mul_assoc, inv_mul_cancel_left, leftInvariantDistance] using
      le_ciSup (translateDistance_bdd (g * x) (g * y)) (h * g⁻¹)

section LeftUniform
variable [IsLeftUniformGroup G]

theorem leftInvariantMetric_isometric :
    letI := leftInvariantMetric (G := G)
    IsIsometricSMul G G := by
  let m₀ : MetricSpace G := inferInstance
  let := leftInvariantMetric (G := G)
  refine ⟨fun g => Isometry.of_dist_eq ?_⟩
  intro x y
  change @leftInvariantDistance G _ m₀ (g * x) (g * y) =
    @leftInvariantDistance G _ m₀ x y
  exact @leftInvariantDistance_mul_left G _ m₀ g x y

end LeftUniform
/-- Every first-countable Hausdorff topological group has a bounded,
compatible left-invariant metric. -/
theorem exists_bounded_leftInvariant_metric
    {H : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [FirstCountableTopology H] [T2Space H] :
    ∃ m : MetricSpace H,
      m.toUniformSpace.toTopologicalSpace = ‹TopologicalSpace H› ∧
      (letI := m; IsIsometricSMul H H) ∧
      (letI := m; ∀ x y : H, dist x y ≤ 1) := by
  let u : UniformSpace H := IsTopologicalGroup.leftUniformSpace H
  let : UniformSpace H := u
  let : IsCountablyGenerated (𝓤 H) := by
    change IsCountablyGenerated (Filter.comap (fun p : H × H => p.1⁻¹ * p.2) (𝓝 1))
    infer_instance
  let : MetricSpace H := UniformSpace.metricSpace H
  let : IsLeftUniformGroup H :=
    { uniformity_eq := rfl }
  refine ⟨leftInvariantMetric (G := H), rfl, leftInvariantMetric_isometric, ?_⟩
  intro x y
  exact leftInvariantDistance_le_one x y

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
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_ConstructChainMetric
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Constructing the proper chain metric used in model comparison -/

noncomputable section
namespace PolycyclicRecognition

open Set Metric Filter Topology
open scoped Pointwise

/-- Enlarge compact generators by a compact identity neighborhood and inverses. -/
theorem exists_compact_symmetric_generating_neighborhood
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] {L : Set G} (hL : IsCompact L)
    (hgen : Subgroup.closure L = ⊤) :
    ∃ K : Set G, IsCompact K ∧ K ∈ 𝓝 (1 : G) ∧
      Subgroup.closure K = ⊤ ∧ ∀ g : G, g⁻¹ ∈ K ↔ g ∈ K := by
  obtain ⟨U, hU, hUn⟩ := exists_compact_mem_nhds (1 : G)
  let Q := L ∪ U
  let K := Q ∪ Q⁻¹
  have hQ : IsCompact Q := hL.union hU
  refine ⟨K, hQ.union hQ.inv, ?_, ?_, ?_⟩
  · exact mem_of_superset hUn (by intro x hx; exact Or.inl (Or.inr hx))
  · apply top_unique
    rw [← hgen]
    exact Subgroup.closure_mono (by intro x hx; exact Or.inl (Or.inl hx))
  · intro g
    simp only [K, Set.mem_union, Set.mem_inv, inv_inv]
    exact or_comm

/-- Specialization of the proper chain-metric construction to the exact
compact-generation input used by the recognition theorem. -/
theorem geodesicMetricExistenceInput : GeodesicMetricExistenceInput := by
  intro G _ _ _ _ _ _ hgen
  obtain ⟨m, hm, hiso, hbound⟩ := exists_bounded_leftInvariant_metric (H := G)
  let mc : MetricSpace G := m.replaceTopology hm.symm
  have hmc : mc = m := m.replaceTopology_eq hm.symm
  let := mc
  have hi : IsIsometricSMul G G :=
    Eq.mp (congrArg (fun d : MetricSpace G => letI := d; IsIsometricSMul G G) hmc.symm) hiso
  let := hi
  have hb : ∀ x y : G, dist x y ≤ 1 :=
    Eq.mp (congrArg (fun d : MetricSpace G => letI := d; ∀ x y : G, dist x y ≤ 1) hmc.symm) hbound
  obtain ⟨L, hL, hLgen⟩ := hgen
  obtain ⟨K, hK, hKn, hKgen, hKsymm⟩ :=
    exists_compact_symmetric_generating_neighborhood hL hLgen
  obtain ⟨ε, hε, hεK⟩ := Metric.mem_nhds_iff.mp hKn
  let δ := min 1 (ε / 2)
  have hδ : 0 < δ := lt_min zero_lt_one (half_pos hε)
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hball : ∀ g : G, dist 1 g ≤ δ → g ∈ K := by
    intro g hg
    apply hεK
    change dist g 1 < ε
    rw [dist_comm]
    exact hg.trans_lt ((min_le_right 1 (ε / 2)).trans_lt (half_lt_self hε))
  exact ⟨weightedProperChainMetric K hKgen hKsymm hb δ hδ hδ1 hball hK⟩

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_HaarMeasureTransfer
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Transfer of an invariant automorphism to the section-coordinate Haar measure -/

namespace PolycyclicRecognition

open MeasureTheory

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G] [LocallyCompactSpace G] [SecondCountableTopology G]

/-- A map preserving one Haar measure preserves every Haar normalization.
This permits use of the Haar measure constructed from ideal-section coordinates. -/
theorem measurePreserving_of_haarMeasure (μ ν : Measure G)
    [μ.IsHaarMeasure] [ν.IsHaarMeasure] (f : G → G)
    (hf : MeasurePreserving f μ μ) : MeasurePreserving f ν ν := by
  rw [Measure.isMulLeftInvariant_eq_smul ν μ]
  refine ⟨hf.measurable, ?_⟩
  rw [Measure.map_smul, hf.map_eq]

end PolycyclicRecognition

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

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanJacobian
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instDecidableEqConeMixedWords _root_.OAI.PolycyclicRecognition.CartanWordModel.instFintypeConeMixedWords _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_nonempty _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.CartanFactorModel.heightRay_zero _root_.OAI.PolycyclicRecognition.CartanFactorModel.realScaleProfile_apply _root_.OAI.PolycyclicRecognition.CartanFactorModel.sampledProbeProfile_apply _root_.OAI.PolycyclicRecognition.bracketWordDifferential_mul _root_.OAI.PolycyclicRecognition.cartanWeightDerivation_apply_root _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.nilshadowWeightDerivation_symm _root_.OAI.PolycyclicRecognition.nilshadowWeightOperator_symm _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The Jacobian of actual Cartan conjugation

The nilpotent residual exponential has determinant one. The scalar weight
factors multiply to one by the already proved trace balance. Consequently
conjugation on the nilpotent Cartan ideal preserves coordinate volume.
-/

noncomputable section

namespace PolycyclicRecognition

open Module LieAlgebra LieModule
open scoped BigOperators

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {H : LieSubalgebra ℝ L} [H.IsCartanSubalgebra]
  {n : ℕ} (T : TriangularAdjoint L n)

set_option maxHeartbeats 1000000 in
/-- The nonsemisimple part of the actual Cartan action has Jacobian one. -/
theorem det_cartanIdealResidualAutomorphism (h : H) :
    LinearMap.det (cartanIdealResidualAutomorphism T H h).toLinearEquiv.toLinearMap = 1 := by
  let : Module ℚ (cartanRootIdeal H) := Module.compHom _ (algebraMap ℚ ℝ)
  exact det_nilpotent_exp (cartanIdealResidualDerivation T H h).toLinearMap
    ⟨finrank ℝ L, cartanIdealResidualDerivation_pow_eq_zero T H h⟩

namespace CartanWordModel

variable (M : CartanWordModel H)

set_option maxHeartbeats 1000000 in
/-- The diagonal scalar action has Jacobian given by the total word weight. -/
theorem det_idealWeightDilation (β : M.Bases) (h : H) :
    LinearMap.det (cartanIdealWeightDilation T H h).toLinearEquiv.toLinearMap =
      Real.exp (∑ j, bracketWordExponent (fun i => M.weight i h) (β.val j)) := by
  let b := WordBasisSelections.basis M.letter M.wordList β
  let F := (cartanIdealWeightDilation T H h).toLinearEquiv.toLinearMap
  let v := fun j => Real.exp (bracketWordExponent (fun i => M.weight i h) (β.val j))
  have hb (j) : F (b j) = v j • b j := by
    have hh := M.idealWeightDilation_word T h (β.val j)
    have he := WordBasisSelections.eval_words M.letter M.wordList β j
    change evalBracketWord M.letter (β.val j) = b j at he
    rw [he] at hh
    exact hh
  have hm : LinearMap.toMatrix b b F = Matrix.diagonal v := by
    ext i j
    simp only [LinearMap.toMatrix_apply, hb, map_smul, Finsupp.smul_apply,
      Basis.repr_self, Finsupp.single_apply, smul_eq_mul, Matrix.diagonal_apply]
    split_ifs <;> simp_all
  rw [← LinearMap.det_toMatrix b, hm, Matrix.det_diagonal, Real.exp_sum]

set_option maxHeartbeats 1000000 in
include M in
/-- Unimodularity makes all word-basis scalar Jacobians equal to one. -/
theorem det_idealWeightDilation_eq_one
    (hunimod : ∀ x : L, LinearMap.trace ℝ L (ad ℝ L x) = 0) (h : H) :
    LinearMap.det (cartanIdealWeightDilation T H h).toLinearEquiv.toLinearMap = 1 := by
  let β : M.Bases := Classical.choice inferInstance
  rw [M.det_idealWeightDilation T β h]
  have ht := trace_cartan_word_basis H M.letter M.weight M.letter_root
    (WordBasisSelections.basis M.letter M.wordList β)
    (WordBasisSelections.words M.letter M.wordList β)
    (WordBasisSelections.eval_words M.letter M.wordList β) h
  have hz := trace_cartanRootIdeal_eq_zero T H hunimod h
  have hs : (∑ j, bracketWordExponent (fun i => M.weight i h) (β.val j)) = 0 := by
    rw [ht] at hz
    simp only [bracketWordExponent]
    rw [Finset.sum_comm]
    simpa only [Nat.cast_sum, Finset.sum_mul, WordBasisSelections.words] using hz
  rw [hs, Real.exp_zero]

set_option maxHeartbeats 1000000 in
include M in
/-- The full actual Cartan action, rather than only its scalar part, has
Jacobian one on the nilpotent ideal. -/
theorem det_idealAdjointAutomorphism_eq_one
    (hunimod : ∀ x : L, LinearMap.trace ℝ L (ad ℝ L x) = 0) (h : H) :
    LinearMap.det (cartanIdealAdjointAutomorphism T H h).toLinearEquiv.toLinearMap = 1 := by
  change LinearMap.det ((cartanIdealWeightDilation T H h).toLinearEquiv.toLinearMap.comp
    (cartanIdealResidualAutomorphism T H h).toLinearEquiv.toLinearMap) = 1
  rw [LinearMap.det_comp, M.det_idealWeightDilation_eq_one T hunimod,
    det_cartanIdealResidualAutomorphism, mul_one]

end CartanWordModel
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

set_option maxHeartbeats 1000000 in
include hExpD dynkinD in
/-- Bounded increments and containment of the actual prefix heights imply
a polynomial bound for the nilpotent coordinate of the full word. -/
theorem exists_semidirect_word_bound
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (hφ : ∀ d, φ d = M.adjointGroupAutomorphism T eN ExpN hExpN hbijN dynkinN
      (cartanLog H eD ExpD hbijD d))
    {RN RD : ℝ} (hRN : 0 ≤ RN) (hRD : 0 ≤ RD) :
    ∃ (C : ℝ) (q : ℕ), 0 ≤ C ∧ ∀ {E : Set W}, IsCompact E → E.Nonempty →
      ∀ β : M.Bases,
      IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
        (M.boxCost T hunimod eW E) β.val →
      ∀ (γ : M.Bases) (r : ℝ), 0 ≤ r → ∀ (m : ℕ) (u : ℕ → N) (v : ℕ → D),
      (∀ i < m, u i ∈ exponentialCoordinateBox (ExpN ∘ eN)
        (WordBasisSelections.basis M.letter M.wordList γ) RN) →
      (∀ i < m, v i ∈ exponentialCoordinateBox (ExpD ∘ eD) (finBasis ℝ H) RD) →
      (∀ i < m, ∃ w ∈ E,
        eW (heightProjection T.character
          (cartanLog H eD ExpD hbijD (wordPrefix v i) : L)) = r • w) →
      (wordPrefix (fun i => (⟨u i, v i⟩ : N ⋊[φ] D)) m).left ∈
        M.groupBox T hunimod eW (ExpN ∘ eN) E β r (C * (1 + (m : ℝ)) ^ q) := by
  obtain ⟨A, c, hA, hlog⟩ := exists_cartan_word_log_bound H eD ExpD hbijD hExpD dynkinD hRD
  obtain ⟨C, q, hC, hprod⟩ := M.exists_controlled_product_bound T hunimod eW eN ExpN
    hExpN hbijN dynkinN b₀ hA hRN c
  refine ⟨C, q, hC, ?_⟩
  intro E hE hne β hβ γ r hr m u v hu hv hheight
  choose w hw hh using (fun i : Fin m => hheight i.val i.isLt)
  have hp (i : Fin m) :
      ‖(finBasis ℝ H).equivFun (cartanLog H eD ExpD hbijD (wordPrefix v i.val))‖ ≤
        A * (1 + (m : ℝ)) ^ c := by
    apply (hlog v i.val (fun j hj => hv j (hj.trans i.isLt))).trans
    gcongr
    exact_mod_cast i.isLt.le
  have hhprod := hprod hE hne β hβ γ r hr m
    (fun i => cartanLog H eD ExpD hbijD (wordPrefix v i.val)) w hw hh hp
    (fun i => u i.val) (fun i => hu i.val i.isLt)
  rw [semidirect_wordPrefix_left]
  change (List.ofFn (fun i : Fin m => φ (wordPrefix v i.val) (u i.val))).prod ∈ _
  simp_rw [hφ]
  exact hhprod

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanCompactWords
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instDecidableEqConeMixedWords _root_.OAI.PolycyclicRecognition.CartanWordModel.instFintypeConeMixedWords _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Compact increments in the Cartan word model

Compact sets of increments have bounded logarithms in the published global
nilpotent exponential charts. This removes the coordinate-radius assumptions
from the semidirect word estimate and leaves ordinary compact step data.
-/

noncomputable section

namespace PolycyclicRecognition

open Module LieAlgebra LieModule
open scoped Manifold

set_option maxHeartbeats 1000000 in
/-- A compact subset has bounded coordinates in any global exponential chart,
without choosing a norm on the abstract Lie-algebra model. -/
theorem exists_compact_exponential_coordinate_bound
    {L : Type*} [LieRing L] [LieAlgebra ℝ L]
    {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace G] [ChartedSpace E G] [Group G] [LieGroup (𝓘(ℝ, E)) ⊤ G]
    (e : L ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, E)) G)
    (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G)
    (chart : GroupLieAlgebra (𝓘(ℝ, E)) G ≃ₜ G) (hchart : ∀ x, chart x = Exp x)
    {J : Type*} [Fintype J] (b : Basis J ℝ L) {K : Set G} (hK : IsCompact K) :
    ∃ R : ℝ, 0 ≤ R ∧ K ⊆ exponentialCoordinateBox (Exp ∘ e) b R := by
  let f := (b.equivFun.toLinearMap.comp e.symm.toLinearMap).toContinuousLinearMap
  have hc : Continuous (fun g => f (chart.symm g)) := f.continuous.comp chart.symm.continuous
  obtain ⟨R, hR⟩ := hK.exists_bound_of_continuousOn hc.continuousOn
  refine ⟨max R 0, le_max_right _ _, ?_⟩
  intro g hg
  refine ⟨e.symm (chart.symm g), ?_, (hR g hg).trans (le_max_left _ _)⟩
  change Exp (e (e.symm (chart.symm g))) = g
  rw [e.apply_symm_apply, ← hchart, chart.apply_symm_apply]

namespace CartanWordModel

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
  (chartN : GroupLieAlgebra (𝓘(ℝ, EN)) N ≃ₜ N) (hchartN : ∀ x, chartN x = ExpN x)
  (dynkinN : NilpotentDynkinExpansionInput EN N)
  {ED D : Type*} [NormedAddCommGroup ED] [NormedSpace ℝ ED]
  [FiniteDimensional ℝ ED] [TopologicalSpace D] [ChartedSpace ED D] [Group D]
  [LieGroup (𝓘(ℝ, ED)) ⊤ D] [T2Space D]
  (eD : H ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, ED)) D)
  (ExpD : GroupLieAlgebra (𝓘(ℝ, ED)) D → D) (hExpD : IsGroupExponential ExpD)
  (chartD : GroupLieAlgebra (𝓘(ℝ, ED)) D ≃ₜ D) (hchartD : ∀ x, chartD x = ExpD x)
  (dynkinD : NilpotentDynkinExpansionInput ED D)
  (φ : D →* MulAut N)

set_option maxHeartbeats 1000000 in
include hExpD dynkinD hchartN hchartD in
/-- Compact semidirect increments have the same polynomial endpoint bound.
The only path restriction is containment of their actual Cartan prefix heights. -/
theorem exists_compact_semidirect_word_bound
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (γ : M.Bases) {K : Set (N × D)} (hK : IsCompact K)
    (hφ : ∀ d, φ d = M.adjointGroupAutomorphism T eN ExpN hExpN
      (by rw [← show chartN = ExpN from funext hchartN]; exact chartN.bijective) dynkinN
      (cartanLog H eD ExpD
        (by rw [← show chartD = ExpD from funext hchartD]; exact chartD.bijective) d)) :
    ∃ (C : ℝ) (q : ℕ), 0 ≤ C ∧ ∀ {E : Set W}, IsCompact E → E.Nonempty →
      ∀ β : M.Bases,
      IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
        (M.boxCost T hunimod eW E) β.val →
      ∀ r : ℝ, 0 ≤ r → ∀ (m : ℕ) (u : ℕ → N) (v : ℕ → D),
      (∀ i < m, (u i, v i) ∈ K) →
      (∀ i < m, ∃ w ∈ E,
        eW (heightProjection T.character
          (cartanLog H eD ExpD
            (by rw [← show chartD = ExpD from funext hchartD]; exact chartD.bijective)
            (wordPrefix v i) : L)) = r • w) →
      (wordPrefix (fun i => (⟨u i, v i⟩ : N ⋊[φ] D)) m).left ∈
        M.groupBox T hunimod eW (ExpN ∘ eN) E β r (C * (1 + (m : ℝ)) ^ q) := by
  have hbijN : Function.Bijective ExpN := funext hchartN ▸ chartN.bijective
  have hbijD : Function.Bijective ExpD := funext hchartD ▸ chartD.bijective
  obtain ⟨RN, hRN, hN⟩ := exists_compact_exponential_coordinate_bound eN ExpN chartN hchartN
    (WordBasisSelections.basis M.letter M.wordList γ) (hK.image continuous_fst)
  obtain ⟨RD, hRD, hD⟩ := exists_compact_exponential_coordinate_bound eD ExpD chartD hchartD
    (finBasis ℝ H) (hK.image continuous_snd)
  obtain ⟨C, q, hC, hb⟩ := M.exists_semidirect_word_bound T hunimod eW eN ExpN hExpN
    hbijN dynkinN eD ExpD hExpD hbijD dynkinD φ b₀ hφ hRN hRD
  refine ⟨C, q, hC, ?_⟩
  intro E hE hne β hβ r hr m u v huv hh
  exact hb hE hne β hβ γ r hr m u v
    (fun i hi => hN ⟨(u i, v i), huv i hi, rfl⟩)
    (fun i hi => hD ⟨(u i, v i), huv i hi, rfl⟩) hh

end CartanWordModel
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

variable {EG G : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  {ExpG : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H ExpG)
  {W : Type*} [AddCommGroup W] [Module ℝ W]
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

set_option maxHeartbeats 1000000 in
include hπExp in
/-- A lifted prefix has precisely the same height as its Cartan coordinate. -/
theorem lifted_prefix_height
    (hbijN : Function.Bijective F.ExpN) (hbijD : Function.Bijective F.ExpD)
    (u : ℕ → G) (v : ℕ → F.N.carrier) (w : ℕ → F.D.carrier) (j : ℕ)
    (hlift : F.inclusionN
        (wordPrefix (fun i => (⟨v i, w i⟩ : F.N.carrier ⋊[F.action] F.D.carrier)) j).left *
      F.inclusionD (wordPrefix w j) = wordPrefix u j) :
    q (heightProjection T.character
      (cartanLog H F.D.equiv F.ExpD hbijD (wordPrefix w j) :
        GroupLieAlgebra (𝓘(ℝ, EG)) G)) = (π (wordPrefix u j)).toAdd := by
  rw [← F.inclusionD_height T q π hπExp hbijD, ← hlift, map_mul,
    F.inclusionN_height_eq_one T q π hπExp hbijN, one_mul]

end PolycyclicRecognition.CartanFactorModel

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
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanHaarConjugation
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instDecidableEqConeMixedWords _root_.OAI.PolycyclicRecognition.CartanWordModel.instFintypeConeMixedWords _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A common Haar measure for Cartan boxes and conjugation

The determinant computation gives exact invariance under the actual Cartan
adjoint automorphisms. The same measure retains the explicit weighted-box
volume, so the lower packing argument and box rates use compatible measures.
-/

noncomputable section

namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule MeasureTheory
open scoped Manifold

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {H : LieSubalgebra ℝ L} [H.IsCartanSubalgebra] (M : CartanWordModel H)
  {a : ℕ} (T : TriangularAdjoint L a)
  (hunimod : ∀ x : L, LinearMap.trace ℝ L (ad ℝ L x) = 0)
  {EN N : Type*} [NormedAddCommGroup EN] [NormedSpace ℝ EN]
  [FiniteDimensional ℝ EN] [TopologicalSpace N] [ChartedSpace EN N] [Group N]
  [LieGroup (𝓘(ℝ, EN)) ⊤ N] [T2Space N]
  [hNsc : SimplyConnectedSpace N] [MeasurableSpace N] [BorelSpace N]
  (eN : cartanRootIdeal H ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, EN)) N)
  (Exp : GroupLieAlgebra (𝓘(ℝ, EN)) N → N) (hExp : IsGroupExponential Exp)
  (hbij : Function.Bijective Exp) (dynkin : NilpotentDynkinExpansionInput EN N)
  (haar : NilpotentExponentialHaarInput EN N)

include hunimod haar hNsc

set_option maxHeartbeats 1000000 in
/-- One Haar measure has both the exact word-box formula and invariance
under every Cartan adjoint action. -/
theorem exists_haar_adjoint_invariant_weighted_boxes
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H)) :
    ∃ μ : Measure N, μ.IsHaarMeasure ∧
      (∀ h : H, MeasurePreserving (M.adjointGroupAutomorphism T eN Exp hExp hbij dynkin h) μ μ) ∧
      ∀ (cost : M.wordList → ℝ) (β : M.Bases) (r R : ℝ), 0 ≤ R →
        μ (exponentialCoordinateBox (Exp ∘ eN)
          (exponentialRescaleBasis (WordBasisSelections.basis M.letter M.wordList β)
            (fun i => cost (β.val i)) r) R) =
          ENNReal.ofReal |(columnBasisMatrix (wordListCoordinates M.letter M.wordList b₀) β.val).det| *
            ENNReal.ofReal (Real.exp (r * columnBasisWeight cost β.val)) *
              ENNReal.ofReal (2 * R) ^ finrank ℝ (cartanRootIdeal H) := by
  let _ : SimplyConnectedSpace N := hNsc
  have hn : LieRing.IsNilpotent (cartanRootIdeal H) :=
    (LieModule.isNilpotent_iff ℝ _ _).mpr ⟨M.bound, M.bound_zero⟩
  obtain ⟨⟨chart, hc⟩, hhaar⟩ := haar.2 Exp hExp (eN.nilpotent_iff_equiv_nilpotent.mp hn)
  let b := b₀.map eN.toLinearEquiv
  let f := (Exp ∘ eN) ∘ b₀.equivFun.symm
  have hf : f = Exp ∘ b.equivFun.symm := by
    funext t
    change Exp (eN (b₀.equivFun.symm t)) = Exp ((b₀.map eN.toLinearEquiv).equivFun.symm t)
    rw [Basis.map_equivFun]
    rfl
  refine ⟨Measure.map f volume, ?_, ?_, ?_⟩
  · rw [hf]
    exact hhaar _ b
  · intro h
    exact exponentialConjugate_measurePreserving eN Exp hbij chart hc b₀
      (cartanIdealAdjointAutomorphism T H h) (M.det_idealAdjointAutomorphism_eq_one T hunimod h)
  · intro cost β r R hR
    exact exponentialCoordinate_weighted_box_measure eN Exp chart hc b₀ M.letter M.wordList
      cost β r R hR

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanFactorHaarInvariance
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instDecidableEqConeMixedWords _root_.OAI.PolycyclicRecognition.CartanWordModel.instFintypeConeMixedWords _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_countable _root_.OAI.PolycyclicRecognition.finitelyGeneratedSubgroupIndex_countable _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual Cartan factor action preserves the chosen Haar measure -/

noncomputable section
namespace PolycyclicRecognition.CartanFactorModel

open Module LieAlgebra MeasureTheory Set
open scoped Manifold NNReal

variable {EG G : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H Exp)

include T M

set_option maxHeartbeats 1000000 in
/-- Trace zero and the published realization imply that the original
factor action preserves every Haar normalization, including the measure
constructed in ideal/quotient section coordinates. -/
theorem action_preserves_haar
    (hExp : IsGroupExponential Exp)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
    (haarD : NilpotentExponentialHaarInput F.D.modelSpace F.D.carrier)
    (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
    (hunimod : ∀ x : GroupLieAlgebra (𝓘(ℝ, EG)) G, LinearMap.trace ℝ _ (ad ℝ _ x) = 0)
    (μ : Measure F.N.carrier) [μ.IsHaarMeasure] (d : F.D.carrier) :
    MeasurePreserving (F.action d) μ μ := by
  classical
  let _ : IsTopologicalGroup F.N.carrier := topologicalGroup_of_lieGroup (𝓘(ℝ, F.N.modelSpace)) ⊤
  obtain ⟨⟨chartN, hchartN⟩, _⟩ := haarN.2 F.ExpN F.isExpN
    (F.N.tangent_nilpotent (cartanRootIdeal_nilpotent H T))
  obtain ⟨⟨chartD, hchartD⟩, _⟩ := haarD.2 F.ExpD F.isExpD
    (F.D.tangent_nilpotent inferInstance)
  let b := (finBasis ℝ (cartanRootIdeal H)).map F.N.equiv.toLinearEquiv
  let coordinates := b.equivFun.symm.toContinuousLinearEquiv.toHomeomorph.trans chartN
  let _ : LocallyCompactSpace F.N.carrier := coordinates.symm.isOpenEmbedding.locallyCompactSpace
  let _ : SecondCountableTopology F.N.carrier := coordinates.symm.secondCountableTopology
  have hbijN : Function.Bijective F.ExpN := funext hchartN ▸ chartN.bijective
  have hbijD : Function.Bijective F.ExpD := funext hchartD ▸ chartD.bijective
  obtain ⟨ν, hν, hinv, _⟩ := M.exists_haar_adjoint_invariant_weighted_boxes T hunimod
    F.N.equiv F.ExpN F.isExpN hbijN dynkinN haarN (finBasis ℝ (cartanRootIdeal H))
  let _ : ν.IsHaarMeasure := hν
  apply measurePreserving_of_haarMeasure ν μ (F.action d)
  rw [cartan_action_eq_adjoint_of_published_realization T M F hExp realize hbijN hbijD dynkinN d]
  exact hinv _

end PolycyclicRecognition.CartanFactorModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_SemidirectProductTopology
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The product topology on the Cartan semidirect cover -/

noncomputable section
namespace PolycyclicRecognition

variable {N D : Type*} [Group N] [Group D] [TopologicalSpace N] [TopologicalSpace D]
  (φ : D →* MulAut N)

attribute [local instance] semidirectProductTopology

variable [IsTopologicalGroup N] [IsTopologicalGroup D]

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

omit [IsTopologicalGroup N] [IsTopologicalGroup D] in
theorem continuous_semidirect_lift (ι : N →* G) (κ : D →* G)
    (hι : Continuous ι) (hκ : Continuous κ)
    (hc : ∀ d n, ι (φ d n) = κ d * ι n * (κ d)⁻¹) :
    Continuous (semidirectProductLift φ ι κ hc) :=
  (hι.comp (continuous_semidirect_left φ)).mul (hκ.comp (continuous_semidirect_right φ))

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanSemidirectCover
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The genuine product cover of the Cartan factors

The factors in the ambient group may overlap. Their semidirect product instead
has unique product coordinates; the projection is surjective and has compact
lifts, which suffices to descend compact coboundary approximations.
-/

noncomputable section
namespace PolycyclicRecognition

universe v

open scoped Manifold

variable {EG G : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G]
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  {ExpG : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H ExpG)

attribute [local instance] semidirectProductTopology

local instance instIsTopologicalGroupCarrierSubtypeGroupLieAlgebraRealModelWithCornersSelfMemLieIdealCartanRootIdealN : IsTopologicalGroup F.N.carrier :=
  topologicalGroup_of_lieGroup (𝓘(ℝ, F.N.modelSpace)) ⊤
local instance instIsTopologicalGroupCarrierSubtypeGroupLieAlgebraRealModelWithCornersSelfMemLieSubalgebraD : IsTopologicalGroup F.D.carrier :=
  topologicalGroup_of_lieGroup (𝓘(ℝ, F.D.modelSpace)) ⊤

set_option maxHeartbeats 1000000 in
theorem CartanFactorModel.continuous_action :
    Continuous (fun p : F.D.carrier × F.N.carrier => F.action p.1 p.2) := by
  let : IsTopologicalGroup G := topologicalGroup_of_lieGroup (𝓘(ℝ, EG)) ⊤
  apply F.closedN.isEmbedding.isInducing.continuous_iff.mpr
  have hi := F.closedD.continuous.comp (continuous_fst : Continuous (Prod.fst : F.D.carrier × F.N.carrier → _))
  have hn := F.closedN.continuous.comp (continuous_snd : Continuous (Prod.snd : F.D.carrier × F.N.carrier → _))
  have he : (F.inclusionN ∘ (fun p : F.D.carrier × F.N.carrier => F.action p.1 p.2)) =
      (fun p => F.inclusionD p.1 * F.inclusionN p.2 * (F.inclusionD p.1)⁻¹) := by
    funext p
    exact F.conjugation p.1 p.2
  rw [he]
  exact continuous_mul.comp ((continuous_mul.comp (hi.prodMk hn)).prodMk
    (continuous_inv.comp hi))

set_option maxHeartbeats 1000000 in
theorem CartanFactorModel.continuous_semidirectProjection :
    Continuous F.semidirectProjection := by
  let : IsTopologicalGroup G := topologicalGroup_of_lieGroup (𝓘(ℝ, EG)) ⊤
  exact continuous_semidirect_lift F.action F.inclusionN F.inclusionD
    F.closedN.continuous F.closedD.continuous F.conjugation

set_option maxHeartbeats 1000000 in
theorem CartanFactorModel.compact_lifts_semidirectProjection
    (K : Set G) (hK : IsCompact K) :
    ∃ C : Set (F.N.carrier ⋊[F.action] F.D.carrier),
      IsCompact C ∧ K ⊆ F.semidirectProjection '' C := by
  obtain ⟨C, hC, hlift⟩ := F.compactLifts K hK
  refine ⟨(semidirectProductHomeomorph F.action).symm '' C,
    hC.image (semidirectProductHomeomorph F.action).symm.continuous, ?_⟩
  intro g hg
  obtain ⟨p, hp, hpg⟩ := hlift hg
  exact ⟨(semidirectProductHomeomorph F.action).symm p, ⟨p, hp, rfl⟩, hpg⟩

set_option maxHeartbeats 1000000 in
theorem CartanFactorModel.semidirect_topologicalGroup :
    IsTopologicalGroup (F.N.carrier ⋊[F.action] F.D.carrier) :=
  semidirectProductTopologicalGroup F.action F.continuous_action

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_SemidirectProductHaar
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Haar measure in genuine semidirect product coordinates -/

noncomputable section
namespace PolycyclicRecognition

open MeasureTheory MeasureTheory.Measure

variable {N D : Type*} [Group N] [Group D]
  [TopologicalSpace N] [TopologicalSpace D] [IsTopologicalGroup N] [IsTopologicalGroup D]
  [MeasurableSpace N] [MeasurableSpace D] [BorelSpace N] [BorelSpace D]
  [SecondCountableTopology N] [SecondCountableTopology D]
  (φ : D →* MulAut N)

attribute [local instance] semidirectProductTopology

variable [MeasurableSpace (N ⋊[φ] D)] [BorelSpace (N ⋊[φ] D)]
  (μN : Measure N) (μD : Measure D)

variable [SFinite μN] [SFinite μD]

variable [μN.IsMulLeftInvariant] [μD.IsMulLeftInvariant]

omit [SecondCountableTopology N] in
theorem semidirectProductMeasure_left_invariant
    (hφ : Continuous (fun p : D × N => φ p.1 p.2))
    (hpres : ∀ d, MeasurePreserving (φ d) μN μN) (g : N ⋊[φ] D) :
    MeasurePreserving (fun x => g * x) (semidirectProductMeasure φ μN μD)
      (semidirectProductMeasure φ μN μD) := by
  let : IsTopologicalGroup (N ⋊[φ] D) := semidirectProductTopologicalGroup φ hφ
  let e := semidirectProductHomeomorph φ
  have hp : MeasurePreserving (fun p : N × D => (g.left * φ g.right p.1, g.right * p.2))
      (μN.prod μD) (μN.prod μD) :=
    ((measurePreserving_mul_left μN g.left).comp (hpres g.right)).prod
      (measurePreserving_mul_left μD g.right)
  exact (e.symm.measurable.measurePreserving (μN.prod μD)).of_semiconj hp
    (fun _ => rfl) (continuous_const.mul continuous_id).measurable

variable [μN.IsHaarMeasure] [μD.IsHaarMeasure]

omit [μN.IsMulLeftInvariant] [μD.IsMulLeftInvariant] [SecondCountableTopology N] in
theorem semidirectProductMeasure_isHaarMeasure
    (hφ : Continuous (fun p : D × N => φ p.1 p.2))
    (hpres : ∀ d, MeasurePreserving (φ d) μN μN) :
    (semidirectProductMeasure φ μN μD).IsHaarMeasure :=
  { map_mul_left_eq_self := fun g =>
      (semidirectProductMeasure_left_invariant φ μN μD hφ hpres g).map_eq
    toIsFiniteMeasureOnCompacts := Measure.IsFiniteMeasureOnCompacts.map (μN.prod μD)
      (semidirectProductHomeomorph φ).symm
    toIsOpenPosMeasure := (semidirectProductHomeomorph φ).symm.continuous.isOpenPosMeasure_map
      (semidirectProductHomeomorph φ).symm.surjective }

omit [μN.IsMulLeftInvariant] [μD.IsMulLeftInvariant]
  [μN.IsHaarMeasure] [μD.IsHaarMeasure] in
/-- Inversion in the cover is the factorwise inversion followed by the
measure-preserving Cartan action on the nilpotent coordinate. -/
theorem semidirectProductMeasure_isInvInvariant
    [μN.IsInvInvariant] [μD.IsInvInvariant]
    (hφ : Continuous (fun p : D × N => φ p.1 p.2))
    (hpres : ∀ d, MeasurePreserving (φ d) μN μN) :
    (semidirectProductMeasure φ μN μD).IsInvInvariant := by
  let : IsTopologicalGroup (N ⋊[φ] D) := semidirectProductTopologicalGroup φ hφ
  let e := semidirectProductHomeomorph φ
  have ha : MeasurePreserving (fun p : D × N => (p.1, φ p.1 p.2))
      (μD.prod μN) (μD.prod μN) := by
    apply (MeasurePreserving.id μD).skew_product (g := fun d n => φ d n)
    · exact hφ.measurable
    · exact Filter.Eventually.of_forall fun d => (hpres d).map_eq
  have hb : MeasurePreserving (fun p : N × D => (φ p.2 p.1, p.2))
      (μN.prod μD) (μN.prod μD) :=
    Measure.measurePreserving_swap.comp (ha.comp Measure.measurePreserving_swap)
  have hi : MeasurePreserving (fun p : N × D => (φ p.2⁻¹ p.1⁻¹, p.2⁻¹))
      (μN.prod μD) (μN.prod μD) :=
    hb.comp ((measurePreserving_inv μN).prod (measurePreserving_inv μD))
  have hs : MeasurePreserving Inv.inv (semidirectProductMeasure φ μN μD)
      (semidirectProductMeasure φ μN μD) :=
    (e.symm.measurable.measurePreserving (μN.prod μD)).of_semiconj hi
      (fun _ => rfl) continuous_inv.measurable
  exact ⟨hs.map_eq⟩

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanCoverGeometry
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Proper metrics and invariant product measure on the Cartan cover -/

noncomputable section
namespace PolycyclicRecognition

open MeasureTheory MeasureTheory.Measure Module LieAlgebra
open scoped Manifold

variable {EG G : Type} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  {Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H Exp)

attribute [local instance] semidirectProductTopology semidirectProductMeasurableSpace
  semidirectProduct_borelSpace

set_option maxHeartbeats 1000000 in
include T in
omit [SimplyConnectedSpace G] in
theorem CartanFactorModel.nonempty_semidirect_properChainMetric :
    Nonempty (ProperChainMetric (F.N.carrier ⋊[F.action] F.D.carrier)) := by
  have nilp := nilpotentPublishedInputs
  obtain ⟨⟨chartN, _⟩, _⟩ := (nilp.haar _ F.N).2 F.ExpN F.isExpN
    (F.N.tangent_nilpotent (cartanRootIdeal_nilpotent H T))
  obtain ⟨⟨chartD, _⟩, _⟩ := (nilp.haar _ F.D).2 F.ExpD F.isExpD
    (F.D.tangent_nilpotent inferInstance)
  let : SecondCountableTopology F.N.carrier := F.N.secondCountable_of_chart chartN
  let : SecondCountableTopology F.D.carrier := F.D.secondCountable_of_chart chartD
  let : LocallyCompactSpace F.N.carrier :=
    Manifold.locallyCompact_of_finiteDimensional (𝓘(ℝ, F.N.modelSpace))
  let : LocallyCompactSpace F.D.carrier :=
    Manifold.locallyCompact_of_finiteDimensional (𝓘(ℝ, F.D.modelSpace))
  let : IsTopologicalGroup (F.N.carrier ⋊[F.action] F.D.carrier) :=
    F.semidirect_topologicalGroup
  exact geodesicMetricExistenceInput _ (exists_compact_generating_set _)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_WeightSamplingPolytope
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finite_templateSymmetryGroup _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteRootOffsetConeIndex _root_.OAI.PolycyclicRecognition.instFiniteSubtypeLinearEquivRealIdMemSubgroupLinearSupportSymmetryGroup _root_.OAI.PolycyclicRecognition.instNonemptyRootOffsetConeIndex _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The compact polyhedron used for sampling the nilpotent boxes -/

noncomputable section
namespace PolycyclicRecognition

open Set
open scoped BigOperators

variable {W I B : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [FiniteDimensional ℝ W] [Fintype I] [Fintype B]

omit [FiniteDimensional ℝ W] in
/-- Each balanced positive-multiplicity basis controls the absolute value
of every generator weight, including its negative part. -/
theorem SupportDatum.abs_weight_le_basisSupport (D : SupportDatum W I B)
    (b : B) (i : I) (x : W) : |D.weight i x| ≤ D.basisSupport b x := by
  classical
  have hpos (y : W) : D.weight i y ≤ D.basisSupport b y := by
    have hn : (1 : ℝ) ≤ D.multiplicity b i := by exact_mod_cast D.positive b i
    calc
      D.weight i y ≤ max 0 (D.weight i y) := le_max_right _ _
      _ ≤ (D.multiplicity b i : ℝ) * max 0 (D.weight i y) :=
        le_mul_of_one_le_left (le_max_left _ _) hn
      _ ≤ D.basisSupport b y := by
        apply Finset.single_le_sum (s := Finset.univ) (f := fun j =>
          (D.multiplicity b j : ℝ) * max 0 (D.weight j y))
        · intro j _
          exact mul_nonneg (Nat.cast_nonneg _) (le_max_left _ _)
        · exact Finset.mem_univ i
  have hm := hpos (-x)
  rw [map_neg, D.basisSupport_neg] at hm
  exact abs_le.mpr ⟨by linarith, hpos x⟩

omit [FiniteDimensional ℝ W] [Fintype B] [Fintype I] in
theorem isClosed_weightSamplingPolytope (α : I → W →L[ℝ] ℝ) :
    IsClosed (weightSamplingPolytope α) := by
  simp only [weightSamplingPolytope, ofPred_forall]
  exact isClosed_iInter fun i => isClosed_le (α i).continuous continuous_const

omit [FiniteDimensional ℝ W] [Fintype B] [Fintype I] in
theorem closedBall_subset_weightSamplingPolytope (α : I → W →L[ℝ] ℝ) :
    Metric.closedBall (0 : W) 1 ⊆ weightSamplingPolytope α := by
  intro x hx i
  have hn : ‖x‖ ≤ 1 := by simpa using hx
  exact ((le_abs_self _).trans ((α i).le_opNorm x)).trans
    ((mul_le_mul_of_nonneg_left hn (norm_nonneg _)).trans_eq (mul_one _))

/-- Positive balance and separation make the sampling polyhedron compact.
No boundedness assumption on the polyhedron is needed. -/
theorem SupportDatum.isCompact_weightSamplingPolytope (D : SupportDatum W I B) (b : B) :
    IsCompact (weightSamplingPolytope (fun i => (D.weight i).toContinuousLinearMap)) := by
  classical
  let α : W →ₗ[ℝ] (I → ℝ) := LinearMap.pi D.weight
  have hα : Function.Injective α := by
    apply LinearMap.ker_eq_bot.mp
    apply eq_bot_iff.mpr
    intro x hx
    apply D.separates x
    intro i
    exact congrFun hx i
  have hemb := LinearMap.isClosedEmbedding_of_injective (LinearMap.ker_eq_bot.mpr hα)
  let C : ℝ := ∑ i, (D.multiplicity b i : ℝ) * ‖(D.weight i).toContinuousLinearMap‖
  have hbound : weightSamplingPolytope (fun i => (D.weight i).toContinuousLinearMap) ⊆
      α ⁻¹' Icc (fun _ => -C) (fun _ => C) := by
    intro x hx
    have hs : D.basisSupport b x ≤ C := by
      apply Finset.sum_le_sum
      intro i _
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      exact max_le (norm_nonneg _) (hx i)
    constructor <;> intro i
    · exact neg_le_of_abs_le ((D.abs_weight_le_basisSupport b i x).trans hs)
    · exact le_of_abs_le ((D.abs_weight_le_basisSupport b i x).trans hs)
  exact (hemb.isCompact_preimage isCompact_Icc).of_isClosed_subset
    (isClosed_weightSamplingPolytope _) hbound

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_WeightSamplingSupport
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instNonemptyBases _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_nonempty _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact positive widths of the sampling polytope -/

noncomputable section
namespace PolycyclicRecognition

open Set

/-- Every defining halfspace is attained at its Euclidean contact point. -/
theorem weightSampling_support_eq_norm
    {W I : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    [FiniteDimensional ℝ W] [Fintype I]
    (α : I → W →L[ℝ] ℝ) (hC : IsCompact (weightSamplingPolytope α))
    (i : I) (hi : α i ≠ 0) :
    sSup (α i '' weightSamplingPolytope α) = ‖α i‖ := by
  obtain ⟨p, hp, hval, _⟩ := exists_weight_contact_point (α i) hi
  have hpC : p ∈ weightSamplingPolytope α :=
    closedBall_subset_weightSamplingPolytope α (by simpa using hp.le)
  apply le_antisymm
  · have himg : (α i '' weightSamplingPolytope α).Nonempty := ⟨α i p, p, hpC, rfl⟩
    apply csSup_le himg
    rintro _ ⟨x, hx, rfl⟩
    exact hx i
  · rw [← hval]
    exact le_csSup (hC.image (α i).continuous).bddAbove ⟨p, hpC, rfl⟩

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanSamplingParameters
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_nonempty _root_.OAI.PolycyclicRecognition.finite_templateSymmetryGroup _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.instFiniteRootOffsetConeIndex _root_.OAI.PolycyclicRecognition.instFiniteSubtypeLinearEquivRealIdMemSubgroupLinearSupportSymmetryGroup _root_.OAI.PolycyclicRecognition.instNonemptyRootOffsetConeIndex _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Concrete parameters for the neighboring-sheet sampling argument -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra Set

variable {L W : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {H : LieSubalgebra ℝ L} [H.IsCartanSubalgebra] (M : CartanWordModel H)
  {a : ℕ} (T : TriangularAdjoint L a)
  (hunimod : ∀ x : L, LinearMap.trace ℝ L (ad ℝ L x) = 0)
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)

set_option maxHeartbeats 1000000 in
theorem isCompact_samplingPolytope : IsCompact (M.samplingPolytope T hunimod eW) := by
  exact (M.supportIn T hunimod eW).isCompact_weightSamplingPolytope (Classical.arbitrary M.Bases)

set_option maxHeartbeats 1000000 in
theorem sampling_weightSupport_eq (i : Fin M.letterCount) :
    (M.supportIn T hunimod eW).weightSupport (M.samplingPolytope T hunimod eW) i =
      ‖((M.supportIn T hunimod eW).weight i).toContinuousLinearMap‖ :=
  weightSampling_support_eq_norm _ (M.isCompact_samplingPolytope T hunimod eW)
    i (M.sampling_weight_ne_zero T hunimod eW i)

set_option maxHeartbeats 1000000 in
theorem sampling_weightSupport_pos (i : Fin M.letterCount) :
    0 < (M.supportIn T hunimod eW).weightSupport (M.samplingPolytope T hunimod eW) i := by
  rw [M.sampling_weightSupport_eq T hunimod eW i]
  exact norm_pos_iff.mpr (M.sampling_weight_ne_zero T hunimod eW i)

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanCocycleWordGrowth
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_nonempty _root_.OAI.PolycyclicRecognition.finite_templateSymmetryGroup _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteRootOffsetConeIndex _root_.OAI.PolycyclicRecognition.instFiniteSubtypeLinearEquivRealIdMemSubgroupLinearSupportSymmetryGroup _root_.OAI.PolycyclicRecognition.instNonemptyRootOffsetConeIndex _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.CartanFactorModel.heightRay_zero _root_.OAI.PolycyclicRecognition.CartanFactorModel.realScaleProfile_apply _root_.OAI.PolycyclicRecognition.CartanFactorModel.sampledProbeProfile_apply _root_.OAI.PolycyclicRecognition.exponentialRescaleBasis_zero _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.modelNilradicalLinearAction_apply _root_.OAI.PolycyclicRecognition.modelNilradicalRotation_apply _root_.OAI.PolycyclicRecognition.modelNilradicalRotation_mul _root_.OAI.PolycyclicRecognition.modelNilradicalRotation_one _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Sublinear cocycles on compact words in the ambient Cartan group

The actual compact factor lifts control both factors of the same word. The
nilpotent factor lies in a polynomially enlarged root box; the Cartan factor
remains a word in one compact set, where nilpotent reduced cohomology applies.
-/

noncomputable section
namespace PolycyclicRecognition

open Module LieAlgebra LieModule Set
open scoped Manifold

variable {EG G : Type} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  {ExpG : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H ExpG)
  (M : CartanWordModel H) (hExpG : IsGroupExponential ExpG)
  (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
  (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
  (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
  (chartN : GroupLieAlgebra (𝓘(ℝ, F.N.modelSpace)) F.N.carrier ≃ₜ F.N.carrier)
  (hchartN : ∀ x, chartN x = F.ExpN x)
  (chartD : GroupLieAlgebra (𝓘(ℝ, F.D.modelSpace)) F.D.carrier ≃ₜ F.D.carrier)
  (hchartD : ∀ x, chartD x = F.ExpD x)
  (dynkinD : NilpotentDynkinExpansionInput F.D.modelSpace F.D.carrier)
  (hunimod : ∀ x : GroupLieAlgebra (𝓘(ℝ, EG)) G,
    LinearMap.trace ℝ _ (ad ℝ _ x) = 0)
  {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  (eW : HeightSpace T.character ≃ₗ[ℝ] W) (π : G →* Multiplicative W)
  (hπExp : ∀ x, (π (ExpG x)).toAdd = eW (heightProjection T.character x))
  (hπcont : Continuous (fun g => (π g).toAdd))
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  (ρ : G →* (E ≃ₗᵢ[ℝ] E)) (hρ : ∀ v, Continuous (fun g => ρ g v))
  (hfix : ∀ v, (∀ g, ρ g v = v) → v = 0)

include T M hExpG realize haarN dynkinN hchartN hchartD dynkinD hunimod
  hπExp hπcont hρ hfix in
set_option maxHeartbeats 1000000 in
theorem cartan_cocycle_compact_words
    (b : G → E) (hbc : Continuous b) (hb : IsUnitaryCocycle ρ b)
    {K : Set G} (hK : IsCompact K) :
    ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, 0 ≤ B ∧ ∀ (u : ℕ → G) (m : ℕ),
      (∀ i < m, u i ∈ K) → ‖b (wordPrefix u m)‖ ≤ ε * (m : ℝ) + B := by
  classical
  obtain ⟨K', hK', hlift⟩ := exists_compact_cartan_word_lifts F hK
  have hbijN : Function.Bijective F.ExpN := funext hchartN ▸ chartN.bijective
  have hbijD : Function.Bijective F.ExpD := funext hchartD ▸ chartD.bijective
  let b₀ := finBasis ℝ (cartanRootIdeal H)
  let γ : M.Bases := Classical.arbitrary _
  obtain ⟨C, q, hC, hbound⟩ := M.exists_compact_semidirect_word_bound T hunimod eW
    F.N.equiv F.ExpN F.isExpN chartN hchartN dynkinN
    F.D.equiv F.ExpD F.isExpD chartD hchartD dynkinD F.action b₀ γ hK'
    (fun d => cartan_action_eq_adjoint_of_published_realization T M F hExpG realize
      hbijN hbijD dynkinN d)
  let S := M.samplingPolytope T hunimod eW
  have hS : IsCompact S := M.isCompact_samplingPolytope T hunimod eW
  have hball : Metric.closedBall (0 : W) 1 ⊆ S :=
    closedBall_subset_weightSamplingPolytope _
  have hSne : S.Nonempty := ⟨0, hball (by simp)⟩
  obtain ⟨β, hβ⟩ := exists_maximizing_wordBasis M.letter M.wordList b₀
    (M.boxCost T hunimod eW S)
  obtain ⟨R, hR⟩ := hK.exists_bound_of_continuousOn hπcont.continuousOn
  let A := max R 1
  have hA : 1 ≤ A := le_max_right _ _
  have hApos : 0 < A := lt_of_lt_of_le zero_lt_one hA
  intro ε hε
  obtain ⟨B, hB, hN⟩ := cartan_cocycle_polynomial_boxes T F M hExpG realize haarN dynkinN
    ρ hρ hfix b hbc hb b₀ ((M.supportIn T hunimod eW).weightSupport S)
    (M.sampling_weightSupport_pos T hunimod eW) β hβ hC q
    (ε / (2 * A)) (div_pos hε (by positivity))
  obtain ⟨φ, hφ⟩ := cartan_cocycle_approximation T F M hExpG realize haarN dynkinN
    ρ hρ hfix b hbc hb (Prod.snd '' K') (hK'.image continuous_snd)
    (by positivity : 0 < ε / 2)
  refine ⟨B + 2 * ‖φ‖, by positivity, ?_⟩
  intro u m hu
  by_cases hm : m = 0
  · subst m
    simp only [wordPrefix_zero, hb.map_one, norm_zero, Nat.cast_zero, mul_zero, zero_add]
    positivity
  have hmpos : 0 < (m : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hm
  let r := A * (m : ℝ)
  have hr : 0 < r := mul_pos hApos hmpos
  obtain ⟨v, w, hvw, hprefix⟩ := hlift u m hu
  have hheight (i : ℕ) (hi : i < m) : ∃ z ∈ S,
      eW (heightProjection T.character
        (cartanLog H F.D.equiv F.ExpD hbijD (wordPrefix w i) :
          GroupLieAlgebra (𝓘(ℝ, EG)) G)) = r • z := by
    let z := r⁻¹ • (π (wordPrefix u i)).toAdd
    have hn : ‖(π (wordPrefix u i)).toAdd‖ ≤ r := by
      have h := norm_height_wordPrefix_le π u i (R := A)
        (fun j hj => (hR _ (hu j (hj.trans hi))).trans (le_max_left _ _))
      have him : (i : ℝ) ≤ m := by exact_mod_cast hi.le
      exact h.trans (by dsimp [r] <;> nlinarith)
    have hz : ‖z‖ ≤ 1 := by
      dsimp only [z]
      rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hr, ← div_eq_inv_mul]
      exact (div_le_one hr).2 hn
    refine ⟨z, hball (by simpa using hz), ?_⟩
    rw [F.lifted_prefix_height T eW π hπExp hbijN hbijD u v w i (hprefix i hi.le)]
    dsimp [z]
    rw [smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
  have hbox := hbound hS hSne β hβ r hr.le m v w hvw hheight
  obtain ⟨x, hx, hxbound⟩ := hbox
  have hmle : (m : ℝ) ≤ r := by dsimp [r] <;> nlinarith
  have hxbound' : ‖(M.boxBasis T hunimod eW S β r).equivFun x‖ ≤ C * (1 + r) ^ q :=
    hxbound.trans (mul_le_mul_of_nonneg_left (by gcongr) hC)
  have hn := hN r hr.le x hxbound'
  change ‖b (F.inclusionN ((F.ExpN ∘ F.N.equiv) x))‖ ≤ _ at hn
  rw [hx] at hn
  have hd := hb.norm_mapped_wordPrefix_le_of_coboundary F.inclusionD
    (Prod.snd '' K') φ hφ w m (fun i hi => ⟨(v i, w i), hvw i hi, rfl⟩)
  have heq : (ε / (2 * A)) * r = (ε / 2) * (m : ℝ) := by
    dsimp [r]
    field_simp
  calc
    ‖b (wordPrefix u m)‖ = ‖b (F.inclusionN
        ((wordPrefix (fun i => (⟨v i, w i⟩ : F.N.carrier ⋊[F.action] F.D.carrier)) m).left) *
        F.inclusionD (wordPrefix w m))‖ := by rw [hprefix m le_rfl]
    _ ≤ _ := hb.norm_mul_le _ _
    _ ≤ ((ε / (2 * A)) * r + B) + ((m : ℝ) * (ε / 2) + 2 * ‖φ‖) := add_le_add hn hd
    _ = ε * (m : ℝ) + (B + 2 * ‖φ‖) := by rw [heq]; ring

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_CartanReducedCohomology
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Reduced unitary cohomology of the actual unimodular Cartan group

Root contraction proves sublinearity. Concrete controlled Følner pairs in the
semidirect cover supply the averaging vectors, and compact lifts descend the
uniform approximation to the original group.
-/

noncomputable section
namespace PolycyclicRecognition

universe v

open Module LieAlgebra LieModule MeasureTheory MeasureTheory.Measure Set
open scoped Manifold

attribute [local instance] semidirectProductTopology semidirectProductMeasurableSpace
  semidirectProduct_borelSpace

variable {EG G : Type} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  {Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H Exp)
  (M : CartanWordModel H) (hExp : IsGroupExponential Exp)
  (hunimod : ∀ x : GroupLieAlgebra (𝓘(ℝ, EG)) G,
    LinearMap.trace ℝ _ (ad ℝ _ x) = 0)
  {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  (eW : HeightSpace T.character ≃ₗ[ℝ] W) (π : G →* Multiplicative W)
  (hπExp : ∀ x, (π (Exp x)).toAdd = eW (heightProjection T.character x))
  (hπcont : Continuous (fun g => (π g).toAdd))

set_option maxHeartbeats 1000000 in
include T F M hExp hunimod hπExp hπcont in
theorem cartan_unitary_reduced_vanishing_oai : UnitaryReducedVanishing.{0, v} G := by
  intro E _ _ _ ρ hfix hρ b hbc hb Q hQ ε hε
  have nilp := nilpotentPublishedInputs
  have haarN := nilp.haar _ F.N
  have haarD := nilp.haar _ F.D
  obtain ⟨⟨chartN, hchartN⟩, _⟩ := haarN.2 F.ExpN F.isExpN
    (F.N.tangent_nilpotent (cartanRootIdeal_nilpotent H T))
  obtain ⟨⟨chartD, hchartD⟩, _⟩ := haarD.2 F.ExpD F.isExpD
    (F.D.tangent_nilpotent inferInstance)
  let : SecondCountableTopology F.N.carrier := F.N.secondCountable_of_chart chartN
  let : SecondCountableTopology F.D.carrier := F.D.secondCountable_of_chart chartD
  let : LocallyCompactSpace F.N.carrier :=
    Manifold.locallyCompact_of_finiteDimensional (𝓘(ℝ, F.N.modelSpace))
  let : LocallyCompactSpace F.D.carrier :=
    Manifold.locallyCompact_of_finiteDimensional (𝓘(ℝ, F.D.modelSpace))
  let : IsTopologicalGroup F.N.carrier :=
    topologicalGroup_of_lieGroup (𝓘(ℝ, F.N.modelSpace)) ⊤
  let : IsTopologicalGroup F.D.carrier :=
    topologicalGroup_of_lieGroup (𝓘(ℝ, F.D.modelSpace)) ⊤
  obtain ⟨dD⟩ := geodesicMetricExistenceInput F.D.carrier (exists_compact_generating_set _)
  obtain ⟨dS⟩ := F.nonempty_semidirect_properChainMetric T
  let := dS.compatibleMetric
  let : IsTopologicalGroup (F.N.carrier ⋊[F.action] F.D.carrier) := F.semidirect_topologicalGroup
  let : IsIsometricSMul (F.N.carrier ⋊[F.action] F.D.carrier)
      (F.N.carrier ⋊[F.action] F.D.carrier) := dS.isometric_compatibleMetric
  let : ProperSpace (F.N.carrier ⋊[F.action] F.D.carrier) := dS.proper_compatibleMetric
  let μN : Measure F.N.carrier := haar
  let μD : Measure F.D.carrier := haar
  let μ := semidirectProductMeasure F.action μN μD
  have hpres := F.action_preserves_haar T M hExp exponentialLinearRealizationInput_intrinsic
    haarN haarD (nilp.dynkin _ F.N) hunimod μN
  let : μ.IsHaarMeasure := semidirectProductMeasure_isHaarMeasure F.action μN μD
    F.continuous_action hpres
  let : μN.IsInvInvariant := nilpotent_haar_isInvInvariant haarN F.ExpN F.isExpN
    (F.N.tangent_nilpotent (cartanRootIdeal_nilpotent H T)) μN
  let : μD.IsInvInvariant := nilpotent_haar_isInvInvariant haarD F.ExpD F.isExpD
    (F.D.tangent_nilpotent inferInstance) μD
  let : μ.IsInvInvariant := semidirectProductMeasure_isInvInvariant F.action μN μD
    F.continuous_action hpres
  obtain ⟨pairs⟩ := cartan_cover_controlled_pairs T F M hExp hunimod eW π hπExp hπcont
    dS dD μN μD
  let f := F.semidirectProjection
  have hf : Continuous f := F.continuous_semidirectProjection
  have hbp : IsUnitaryCocycle (ρ.comp f) (b ∘ f) := by
    intro g h
    change b (f (g * h)) = _
    rw [map_mul]
    exact hb _ _
  have hsub := sublinear_comp_of_compact_word_estimates f hf b dS.chains_compatibleMetric
    (fun K hK => cartan_cocycle_compact_words T F M hExp exponentialLinearRealizationInput_intrinsic
      haarN (nilp.dynkin _ F.N) chartN hchartN chartD hchartD (nilp.dynkin _ F.D)
      hunimod eW π hπExp hπcont ρ hρ hfix b hbc hb hK)
  obtain ⟨K, hK, hlift⟩ := F.compact_lifts_semidirectProjection Q hQ
  obtain ⟨φ, hφ⟩ := (pairs.toReiter μ).almost_coboundary μ (hbc.comp hf) hbp hsub K hK hε
  refine ⟨φ, fun q hq => ?_⟩
  obtain ⟨x, hx, rfl⟩ := hlift hq
  exact hφ x hx

end PolycyclicRecognition

end

end OAI
end

theorem solution.{v} : type_of% @OAI.PolycyclicRecognition.cartan_unitary_reduced_vanishing_oai.{v} := @OAI.PolycyclicRecognition.cartan_unitary_reduced_vanishing_oai.{v}
