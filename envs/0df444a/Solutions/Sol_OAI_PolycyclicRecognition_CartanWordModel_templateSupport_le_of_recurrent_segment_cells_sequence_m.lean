-- Prove2me | solution 1 for OAI.PolycyclicRecognition.CartanWordModel.templateSupport_le_of_recurrent_segment_cells_sequence_m
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-03T00:26:05.099827+00:00
-- url     : https://prove2.me/submissions/11e2dddc-4e79-4124-87e5-5c72d4bad88b

import Mathlib
import Definitions.Def_PolycyclicRecognition
import Definitions.Def_OAIQ093D027
import Theorems.Thm_OAI_PolycyclicRecognition_CartanWordModel_exists_coarse_path_polynomial_packing
import Theorems.Thm_OAI_PolycyclicRecognition_CartanWordModel_exists_segment_sampled_visit_bound

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_AutocorrelationRecurrence
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The positive autocorrelation behind backward recurrence -/

noncomputable section

namespace PolycyclicRecognition

open MeasureTheory Set
open scoped ENNReal

variable {G : Type} [Group G] [MeasurableSpace G]
  [MeasurableMul₂ G] [MeasurableInv G]

theorem measurable_rightInverseAverage (σ : Measure G) [SFinite σ]
    {f : G → ℝ≥0∞} (hf : Measurable f) :
    Measurable (rightInverseAverage σ f) := by
  apply Measurable.lintegral_prod_right (f := fun x s : G => f (x * s⁻¹))
  exact hf.comp (measurable_fst.mul measurable_snd.inv)

omit [MeasurableMul₂ G] [MeasurableInv G] in
theorem rightInverseAverage_le_one (σ : Measure G) [IsProbabilityMeasure σ]
    {f : G → ℝ≥0∞} (hf : ∀ x, f x ≤ 1) (x : G) :
    rightInverseAverage σ f x ≤ 1 := by
  calc
    _ ≤ ∫⁻ _ : G, (1 : ℝ≥0∞) ∂σ := lintegral_mono (fun s => hf (x * s⁻¹))
    _ = 1 := by simp

omit [MeasurableMul₂ G] [MeasurableInv G] in
/-- The averaged indicator vanishes outside the product of its original
set and a set carrying the increment law. This is the support bound used
in Cauchy--Schwarz. -/
theorem rightInverseAverage_indicator_eq_zero
    (σ : Measure G) (A K R : Set G) (hK : ∀ᵐ s ∂σ, s ∈ K)
    (hAR : ∀ a ∈ A, ∀ s ∈ K, a * s ∈ R) {x : G} (hx : x ∉ R) :
    rightInverseAverage σ (A.indicator (fun _ => (1 : ℝ≥0∞))) x = 0 := by
  apply lintegral_eq_zero_of_ae_eq_zero
  filter_upwards [hK] with s hs
  apply indicator_of_notMem
  intro hxs
  apply hx
  simpa only [inv_mul_cancel_right] using hAR (x * s⁻¹) hxs s hs

/-- The transition law obtained from two independent copies of the same
increment has nonnegative quadratic form. The square identity is exact and
uses right Haar invariance and Tonelli, with no symmetry assumption on σ. -/
theorem right_autocorrelation_eq_square
    (μ σ : Measure G) [SFinite μ] [SFinite σ] [μ.IsMulRightInvariant]
    (f : G → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ x, f x * (∫⁻ s, rightInverseAverage σ f (x * s) ∂σ) ∂μ) =
      ∫⁻ z, rightInverseAverage σ f z ^ 2 ∂μ := by
  have hA := measurable_rightInverseAverage σ hf
  have hprod : Measurable (fun p : G × G => f p.1 * rightInverseAverage σ f (p.1 * p.2)) :=
    (hf.comp measurable_fst).mul (hA.comp (measurable_fst.mul measurable_snd))
  calc
    _ = ∫⁻ x, ∫⁻ s, f x * rightInverseAverage σ f (x * s) ∂σ ∂μ := by
      apply lintegral_congr
      intro x
      exact (lintegral_const_mul _ (hA.comp (measurable_const.mul measurable_id))).symm
    _ = ∫⁻ s, ∫⁻ x, f x * rightInverseAverage σ f (x * s) ∂μ ∂σ :=
      lintegral_lintegral_swap hprod.aemeasurable
    _ = ∫⁻ s, ∫⁻ z, f (z * s⁻¹) * rightInverseAverage σ f z ∂μ ∂σ := by
      apply lintegral_congr
      intro s
      have h := lintegral_mul_right_eq_self (μ := μ)
        (fun z => f (z * s⁻¹) * rightInverseAverage σ f z) s
      simpa only [mul_inv_cancel_right] using h
    _ = ∫⁻ z, ∫⁻ s, f (z * s⁻¹) * rightInverseAverage σ f z ∂σ ∂μ := by
      apply lintegral_lintegral_swap
      exact ((hf.comp (measurable_snd.mul measurable_fst.inv)).mul
        (hA.comp measurable_snd)).aemeasurable
    _ = _ := by
      apply lintegral_congr
      intro z
      have hz : Measurable (fun s => f (z * s⁻¹)) :=
        hf.comp (measurable_const.mul measurable_inv)
      rw [lintegral_mul_const _ hz]
      simp only [pow_two, rightInverseAverage]

/-- The first averaged function has the same total mass as the original
one. This is the second input to the recurrence lower bound. -/
theorem lintegral_rightInverseAverage
    (μ σ : Measure G) [SFinite μ] [IsProbabilityMeasure σ] [μ.IsMulRightInvariant]
    (f : G → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ z, rightInverseAverage σ f z ∂μ) = ∫⁻ z, f z ∂μ := by
  change (∫⁻ z, ∫⁻ s, f (z * s⁻¹) ∂σ ∂μ) = _
  have hm : Measurable (fun p : G × G => f (p.1 * p.2⁻¹)) :=
    hf.comp (measurable_fst.mul measurable_snd.inv)
  rw [lintegral_lintegral_swap (f := fun z s : G => f (z * s⁻¹)) hm.aemeasurable]
  simp only [lintegral_mul_right_eq_self, lintegral_const, measure_univ, mul_one]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_RecurrenceIntegralBounds
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Quantitative integral bounds used by backward recurrence -/

noncomputable section

namespace PolycyclicRecognition

open MeasureTheory Set Filter

/-- Cauchy--Schwarz against the constant function, proved directly by the
nonnegativity of variance. The measure need only have positive finite mass. -/
theorem sq_integral_le_mass_mul_integral_sq
    {X : Type} [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]
    (hM : 0 < μ.real univ) (f : X → ℝ) (hf : Integrable f μ)
    (hf2 : Integrable (fun x => f x ^ 2) μ) :
    (∫ x, f x ∂μ) ^ 2 ≤ μ.real univ * ∫ x, f x ^ 2 ∂μ := by
  let M := μ.real univ
  let I := ∫ x, f x ∂μ
  let a := I / M
  have ha : a * M = I := div_mul_cancel₀ I hM.ne'
  have hi : Integrable (fun x => f x ^ 2 - (2 * a) * f x) μ :=
    hf2.sub (hf.const_mul _)
  have heq : (∫ x, (f x - a) ^ 2 ∂μ) =
      (∫ x, f x ^ 2 ∂μ) - (2 * a) * I + a ^ 2 * M := by
    calc
      _ = ∫ x, (f x ^ 2 - (2 * a) * f x) + a ^ 2 ∂μ := by
        apply integral_congr_ae
        exact Eventually.of_forall (fun x => by ring)
      _ = _ := by
        rw [integral_add hi (integrable_const _), integral_sub hf2 (hf.const_mul _),
          integral_const_mul, integral_const]
        simp only [smul_eq_mul, M, I]
        ring
  have hpos : 0 ≤ (∫ x, f x ^ 2 ∂μ) - (2 * a) * I + a ^ 2 * M := by
    rw [← heq]
    exact integral_nonneg (fun x => sq_nonneg (f x - a))
  have halg : M * ((∫ x, f x ^ 2 ∂μ) - (2 * a) * I + a ^ 2 * M) =
      M * (∫ x, f x ^ 2 ∂μ) - I ^ 2 := by
    calc
      _ = M * (∫ x, f x ^ 2 ∂μ) - 2 * (a * M) * I + (a * M) ^ 2 := by ring
      _ = _ := by rw [ha]; ring
  have hnonneg := mul_nonneg hM.le hpos
  rw [halg] at hnonneg
  exact sub_nonneg.mp hnonneg

/-- A bounded transition function can carry a large integral only if its
superlevel set has large measure. -/
theorem integral_le_superlevel_mass_add
    {X : Type} [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]
    (f : X → ℝ) (hf : Measurable f) (hbound : ∀ x, 0 ≤ f x ∧ f x ≤ 1)
    {t : ℝ} (ht : 0 ≤ t) :
    (∫ x, f x ∂μ) ≤ μ.real {x | t ≤ f x} + t * μ.real univ := by
  let S := {x | t ≤ f x}
  have hS : MeasurableSet S := measurableSet_le measurable_const hf
  have hfi : Integrable f μ := Integrable.of_bound hf.aestronglyMeasurable 1
    (Eventually.of_forall (fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hbound x).1]
      exact (hbound x).2))
  have hI : Integrable (S.indicator (fun _ : X => (1 : ℝ))) μ :=
    (integrable_const (1 : ℝ)).indicator hS
  have hle : (∫ x, f x ∂μ) ≤ ∫ x, S.indicator (fun _ => (1 : ℝ)) x + t ∂μ := by
    apply integral_mono hfi (hI.add (integrable_const t))
    intro x
    change f x ≤ S.indicator (fun _ => (1 : ℝ)) x + t
    by_cases hx : x ∈ S
    · rw [indicator_of_mem hx]
      linarith [(hbound x).2]
    · rw [indicator_of_notMem hx]
      have hn : ¬ t ≤ f x := hx
      simpa only [zero_add] using (lt_of_not_ge hn).le
  rw [integral_add hI (integrable_const t), integral_indicator_const (1 : ℝ) hS,
    integral_const] at hle
  simpa only [smul_eq_mul, mul_one, mul_comm _ t] using hle

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_AutocorrelationLowerBound
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The quantitative lower bound for a two-sample return -/

noncomputable section

namespace PolycyclicRecognition

open MeasureTheory Set Filter
open scoped ENNReal

/-- A function with values in `[0,1]`, supported in a finite-volume region,
has square integral at least its squared mass divided by that volume. -/
theorem sq_mass_le_region_mul_square_mass
    {X : Type} [MeasurableSpace X] (μ : Measure X)
    (f : X → ℝ≥0∞) (hf : Measurable f) (hb : ∀ x, f x ≤ 1)
    (R : Set X) (hRfin : μ R ≠ ∞) (hRpos : 0 < (μ R).toReal)
    (hsupp : ∀ x, x ∉ R → f x = 0) :
    (∫⁻ x, f x ∂μ).toReal ^ 2 ≤ (μ R).toReal * (∫⁻ x, f x ^ 2 ∂μ).toReal := by
  let ν := μ.restrict R
  let : IsFiniteMeasure ν := ⟨by simpa only [ν, Measure.restrict_apply_univ] using hRfin.lt_top⟩
  have hfn (x : X) : f x ≠ ∞ := (hb x).trans_lt (by simp) |>.ne
  have hr (x : X) : 0 ≤ (f x).toReal ∧ (f x).toReal ≤ 1 :=
    ⟨ENNReal.toReal_nonneg, by simpa using ENNReal.toReal_mono (by simp) (hb x)⟩
  have hfi : Integrable (fun x => (f x).toReal) ν :=
    Integrable.of_bound hf.ennreal_toReal.aestronglyMeasurable 1
      (Eventually.of_forall (fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hr x).1]
        exact (hr x).2))
  have hfi2 : Integrable (fun x => (f x).toReal ^ 2) ν :=
    Integrable.of_bound (hf.ennreal_toReal.pow_const 2).aestronglyMeasurable 1
      (Eventually.of_forall (fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        nlinarith [(hr x).1, (hr x).2]))
  have hregion : Function.support f ⊆ R := by
    intro x hx
    by_contra hn
    exact hx (hsupp x hn)
  have hregion2 : Function.support (fun x => f x ^ 2) ⊆ R := by
    intro x hx
    by_contra hn
    exact hx (by simp [hsupp x hn])
  have hI : (∫ x, (f x).toReal ∂ν) = (∫⁻ x, f x ∂μ).toReal := by
    rw [integral_toReal hf.aemeasurable (Eventually.of_forall (fun x => (hfn x).lt_top))]
    congr 1
    exact setLIntegral_eq_of_support_subset hregion
  have hI2 : (∫ x, (f x).toReal ^ 2 ∂ν) = (∫⁻ x, f x ^ 2 ∂μ).toReal := by
    simp_rw [← ENNReal.toReal_pow]
    rw [integral_toReal (hf.pow_const 2).aemeasurable
      (Eventually.of_forall (fun x => by exact ENNReal.pow_ne_top (hfn x) |>.lt_top))]
    congr 1
    exact setLIntegral_eq_of_support_subset hregion2
  have h := sq_integral_le_mass_mul_integral_sq ν
    (by simpa only [measureReal_def, ν, Measure.restrict_apply_univ] using hRpos)
    (fun x => (f x).toReal) hfi hfi2
  simpa only [hI, hI2, measureReal_def, ν, Measure.restrict_apply_univ] using h

/-- The mean probability of returning to `A` after a difference of two
independent increments has the required quadratic lower bound. The region
`R` can be the compact product `Q * support σ` in the application. -/
theorem return_correlation_lower_bound
    {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]
    (μ σ : Measure G) [SFinite μ] [IsProbabilityMeasure σ] [μ.IsMulRightInvariant]
    (A K R : Set G) (hA : MeasurableSet A) (hK : ∀ᵐ s ∂σ, s ∈ K)
    (hRfin : μ R ≠ ∞) (hRpos : 0 < (μ R).toReal)
    (hAR : ∀ a ∈ A, ∀ s ∈ K, a * s ∈ R) :
    (μ A).toReal ^ 2 ≤ (μ R).toReal *
      (∫⁻ x in A, ∫⁻ s₁, ∫⁻ s₂,
        A.indicator (fun _ => (1 : ℝ≥0∞)) (x * s₁ * s₂⁻¹) ∂σ ∂σ ∂μ).toReal := by
  let f := A.indicator (fun _ => (1 : ℝ≥0∞))
  have hf : Measurable f := measurable_const.indicator hA
  have hb : ∀ x, f x ≤ 1 := indicator_le_self' (fun _ _ => bot_le)
  have h := sq_mass_le_region_mul_square_mass μ (rightInverseAverage σ f)
    (measurable_rightInverseAverage σ hf) (rightInverseAverage_le_one σ hb)
    R hRfin hRpos (fun x hx => rightInverseAverage_indicator_eq_zero σ A K R hK hAR hx)
  rw [lintegral_rightInverseAverage μ σ f hf, lintegral_indicator_const hA, one_mul,
    ← right_autocorrelation_eq_square μ σ f hf] at h
  have heq : (fun x => f x * (∫⁻ s, rightInverseAverage σ f (x * s) ∂σ)) =
      A.indicator (fun x => ∫⁻ s₁, ∫⁻ s₂, f (x * s₁ * s₂⁻¹) ∂σ ∂σ) := by
    funext x
    by_cases hx : x ∈ A <;> simp [f, hx, rightInverseAverage]
  rw [heq, lintegral_indicator hA] at h
  exact h

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

theorem subexponential_lower_const {c : ℝ} (hc : 0 < c) :
    HasSubexponentialLowerBound (fun _ => c) := by
  intro ε hε
  have ht := Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.const_mul_atTop hε)
  have he := ht.eventually (gt_mem_nhds hc)
  simpa only [Function.comp_def, id_eq, neg_mul] using he.mono (fun _ h => h.le)

end PolycyclicRecognition

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_BackwardRecurrenceStep
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # One quantitative step of backward recurrence -/

noncomputable section

namespace PolycyclicRecognition

open MeasureTheory Set Filter
open scoped ENNReal

variable {G : Type} [Group G] [MeasurableSpace G]
  [MeasurableMul₂ G] [MeasurableInv G]

theorem measurable_twoSampleReturn (σ : Measure G) [SFinite σ]
    {A : Set G} (hA : MeasurableSet A) : Measurable (twoSampleReturn σ A) := by
  have hchi : Measurable (A.indicator (fun _ => (1 : ℝ≥0∞))) :=
    measurable_const.indicator hA
  have hm := measurable_rightInverseAverage σ hchi
  exact Measurable.lintegral_prod_right (f := fun x s : G =>
    rightInverseAverage σ (A.indicator (fun _ => (1 : ℝ≥0∞))) (x * s))
    (hm.comp (measurable_fst.mul measurable_snd))

omit [MeasurableMul₂ G] [MeasurableInv G] in
theorem twoSampleReturn_le_one (σ : Measure G) [IsProbabilityMeasure σ]
    (A : Set G) (x : G) : twoSampleReturn σ A x ≤ 1 := by
  calc
    _ ≤ ∫⁻ _ : G, ∫⁻ _ : G, (1 : ℝ≥0∞) ∂σ ∂σ := by
      apply lintegral_mono
      intro s
      apply lintegral_mono
      intro t
      exact indicator_le_self' (fun _ _ => bot_le) _
    _ = 1 := by simp

/-- Discarding points with small return probability retains a definite
quadratic fraction of the original set. This is the backward construction
used to keep every intermediate sheet in the prescribed good set. -/
theorem exists_backward_recurrence_step
    (μ σ : Measure G) [SFinite μ] [IsProbabilityMeasure σ] [μ.IsMulRightInvariant]
    (A Q K R : Set G) (hA : MeasurableSet A) (hQfin : μ Q ≠ ∞)
    (hAQ : A ⊆ Q) (hApos : 0 < (μ A).toReal) (hQpos : 0 < (μ Q).toReal)
    (hK : ∀ᵐ s ∂σ, s ∈ K) (hRfin : μ R ≠ ∞) (hRpos : 0 < (μ R).toReal)
    (hAR : ∀ a ∈ A, ∀ s ∈ K, a * s ∈ R)
    {D : ℝ} (hD : 0 < D) (hvol : (μ R).toReal ≤ D * (μ Q).toReal) :
    ∃ B : Set G, MeasurableSet B ∧ B ⊆ A ∧ 0 < (μ B).toReal ∧
      (μ A).toReal ^ 2 / (2 * D * (μ Q).toReal) ≤ (μ B).toReal ∧
      ∀ x ∈ B, (μ A).toReal / (2 * D * (μ Q).toReal) ≤
        (twoSampleReturn σ A x).toReal := by
  let ν := μ.restrict A
  have hAfin : μ A ≠ ∞ := (lt_of_le_of_lt (measure_mono hAQ) hQfin.lt_top).ne
  let : IsFiniteMeasure ν := ⟨by simpa only [ν, Measure.restrict_apply_univ] using hAfin.lt_top⟩
  let p : G → ℝ := fun x => (twoSampleReturn σ A x).toReal
  have hpm : Measurable p := (measurable_twoSampleReturn σ hA).ennreal_toReal
  have hp (x : G) : 0 ≤ p x ∧ p x ≤ 1 :=
    ⟨ENNReal.toReal_nonneg, by simpa using ENNReal.toReal_mono (by simp) (twoSampleReturn_le_one σ A x)⟩
  have hI : (∫ x, p x ∂ν) = (∫⁻ x in A, twoSampleReturn σ A x ∂μ).toReal := by
    exact integral_toReal (measurable_twoSampleReturn σ hA).aemeasurable
      (Eventually.of_forall (fun x => (twoSampleReturn_le_one σ A x).trans_lt (by simp)))
  have hlow : (μ A).toReal ^ 2 ≤ (D * (μ Q).toReal) * ∫ x, p x ∂ν := by
    have h := return_correlation_lower_bound μ σ A K R hA hK hRfin hRpos hAR
    change (μ A).toReal ^ 2 ≤ (μ R).toReal *
      (∫⁻ x in A, twoSampleReturn σ A x ∂μ).toReal at h
    rw [← hI] at h
    exact h.trans (mul_le_mul_of_nonneg_right hvol (integral_nonneg (fun x => (hp x).1)))
  let M := D * (μ Q).toReal
  have hM : 0 < M := mul_pos hD hQpos
  let t := (μ A).toReal / (2 * M)
  let B := A ∩ {x | t ≤ p x}
  have hlevel : MeasurableSet {x | t ≤ p x} := measurableSet_le measurable_const hpm
  have hBm : MeasurableSet B := hA.inter hlevel
  have hmass : ν.real {x | t ≤ p x} = (μ B).toReal := by
    simp only [measureReal_def, ν, Measure.restrict_apply hlevel, B, inter_comm]
  have hu := integral_le_superlevel_mass_add ν p hpm hp (div_nonneg hApos.le (by positivity : 0 ≤ 2 * M))
  change (∫ x, p x ∂ν) ≤ ν.real {x | t ≤ p x} + t * ν.real univ at hu
  rw [hmass, show ν.real univ = (μ A).toReal by simp [measureReal_def, ν]] at hu
  have htM : t * M = (μ A).toReal / 2 := by dsimp [t]; field_simp
  have hmul : M * (∫ x, p x ∂ν) ≤ M * (μ B).toReal + (μ A).toReal ^ 2 / 2 := by
    calc
      _ ≤ M * ((μ B).toReal + t * (μ A).toReal) := mul_le_mul_of_nonneg_left hu hM.le
      _ = M * (μ B).toReal + (t * M) * (μ A).toReal := by ring
      _ = _ := by rw [htM]; ring
  have hbnd : (μ A).toReal ^ 2 / (2 * M) ≤ (μ B).toReal := by
    apply (div_le_iff₀ (mul_pos (by norm_num) hM)).mpr
    change (μ A).toReal ^ 2 ≤ M * (∫ x, p x ∂ν) at hlow
    nlinarith [hlow, hmul]
  have hBpos : 0 < (μ B).toReal :=
    (div_pos (sq_pos_of_pos hApos) (mul_pos (by norm_num) hM)).trans_le hbnd
  refine ⟨B, hBm, inter_subset_left, hBpos, ?_, ?_⟩
  · simpa only [M, mul_assoc] using hbnd
  · intro x hx
    have hx' : t ≤ p x := hx.2
    simpa only [t, p, M, mul_assoc] using hx'

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_BackwardSwitchProbability
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Probability of retaining every intermediate sheet -/

noncomputable section

namespace PolycyclicRecognition

open MeasureTheory Set
open scoped ENNReal NNReal

variable {G : Type} [Group G] [MeasurableSpace G]

theorem switchThresholdProduct_ne_top (τ : ℕ → ℝ≥0) (n k : ℕ) :
    switchThresholdProduct τ n k ≠ ∞ := by
  induction k generalizing n with
  | zero => simp [switchThresholdProduct]
  | succ k ih => exact ENNReal.mul_ne_top ENNReal.coe_ne_top (ih (n + 1))

theorem switchThresholdProduct_pos (τ : ℕ → ℝ≥0) (n k : ℕ)
    (hτ : ∀ j, n ≤ j → j < n + k → 0 < τ j) :
    0 < switchThresholdProduct τ n k := by
  induction k generalizing n with
  | zero => simp [switchThresholdProduct]
  | succ k ih =>
    apply ENNReal.mul_pos
    · exact_mod_cast (hτ n le_rfl (by omega)).ne'
    · exact (ih (n + 1) (fun j hj hj' => hτ j (by omega) (by omega))).ne'

/-- Independent sampling multiplies the conditional return bounds. The
sets may differ at each stage, which is essential for backward recurrence. -/
theorem switchThresholdProduct_le_survival
    (σ : ℕ → Measure G) (S : ℕ → Set G) (τ : ℕ → ℝ≥0)
    (n k : ℕ)
    (hreturn : ∀ j, j < n + k → ∀ x ∈ S j,
      (τ j : ℝ≥0∞) ≤ twoSampleReturn (σ j) (S (j + 1)) x)
    {x : G} (hx : x ∈ S n) :
    switchThresholdProduct τ n k ≤ survivingSwitchProbability σ S n k x := by
  induction k generalizing n x with
  | zero => rfl
  | succ k ih =>
    let P := switchThresholdProduct τ (n + 1) k
    have hP : P ≠ ∞ := switchThresholdProduct_ne_top τ (n + 1) k
    have hnext (y : G) (hy : y ∈ S (n + 1)) :
        P ≤ survivingSwitchProbability σ S (n + 1) k y := by
      apply ih (n + 1) (fun j hj => hreturn j (by omega)) hy
    have hbound : P * twoSampleReturn (σ n) (S (n + 1)) x ≤
        survivingSwitchProbability σ S n (k + 1) x := by
      calc
        _ = ∫⁻ s₁, ∫⁻ s₂,
            P * (S (n + 1)).indicator (fun _ => (1 : ℝ≥0∞)) (x * s₁ * s₂⁻¹)
              ∂σ n ∂σ n := by
          rw [twoSampleReturn, ← lintegral_const_mul' P _ hP]
          apply lintegral_congr
          intro s₁
          exact (lintegral_const_mul' P _ hP).symm
        _ ≤ _ := by
          apply lintegral_mono
          intro s₁
          apply lintegral_mono
          intro s₂
          by_cases hy : x * s₁ * s₂⁻¹ ∈ S (n + 1)
          · simpa only [indicator_of_mem hy, mul_one] using hnext _ hy
          · simp only [indicator_of_notMem hy, mul_zero, le_refl]
    change (τ n : ℝ≥0∞) * P ≤ _
    calc
      _ = P * (τ n : ℝ≥0∞) := mul_comm _ _
      _ ≤ P * twoSampleReturn (σ n) (S (n + 1)) x :=
        mul_le_mul' le_rfl (hreturn n (by omega) x hx)
      _ ≤ _ := hbound

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_BackwardRecurrenceSets
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Nested positive-measure sets for a fixed sequence of switches -/

noncomputable section

namespace PolycyclicRecognition

open MeasureTheory Set
open scoped ENNReal

/-- Iterating the quantitative return estimate backwards produces the
nested sets used in the segment-volume argument. The number and order of
the increment laws are fixed before this construction. -/
theorem exists_backward_recurrence_sets
    {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]
    (μ : Measure G) [SFinite μ] [μ.IsMulRightInvariant]
    (σ : ℕ → Measure G) [∀ j, IsProbabilityMeasure (σ j)]
    (Q : Set G) (hQfin : μ Q ≠ ∞) (hQpos : 0 < (μ Q).toReal)
    (K R : ℕ → Set G) (hK : ∀ j, ∀ᵐ s ∂σ j, s ∈ K j)
    (hRfin : ∀ j, μ (R j) ≠ ∞) (hRpos : ∀ j, 0 < (μ (R j)).toReal)
    (hQR : ∀ j, ∀ a ∈ Q, ∀ s ∈ K j, a * s ∈ R j)
    (D : ℕ → ℝ) (hD : ∀ j, 0 < D j)
    (hvol : ∀ j, (μ (R j)).toReal ≤ D j * (μ Q).toReal)
    (h : ℕ) (A : Set G) (hA : MeasurableSet A) (hAQ : A ⊆ Q)
    (hApos : 0 < (μ A).toReal) :
    ∃ S : ℕ → Set G, S h = A ∧
      (∀ j, j ≤ h → MeasurableSet (S j) ∧ S j ⊆ A ∧ 0 < (μ (S j)).toReal) ∧
      ∀ j, j < h → S j ⊆ S (j + 1) ∧
        (μ (S (j + 1))).toReal ^ 2 / (2 * D j * (μ Q).toReal) ≤ (μ (S j)).toReal ∧
        ∀ x ∈ S j, (μ (S (j + 1))).toReal / (2 * D j * (μ Q).toReal) ≤
          (twoSampleReturn (σ j) (S (j + 1)) x).toReal := by
  induction h generalizing A with
  | zero =>
    refine ⟨fun _ => A, rfl, ?_, ?_⟩
    · intro j hj
      exact ⟨hA, Subset.rfl, hApos⟩
    · intro j hj
      omega
  | succ h ih =>
    obtain ⟨B, hBm, hBA, hBpos, hmass, hreturn⟩ :=
      exists_backward_recurrence_step μ (σ h) A Q (K h) (R h) hA hQfin hAQ hApos hQpos
        (hK h) (hRfin h) (hRpos h) (fun a ha => hQR h a (hAQ ha)) (hD h) (hvol h)
    obtain ⟨S, hSh, hprop, hstep⟩ := ih B hBm (hBA.trans hAQ) hBpos
    let S' := fun j => if j ≤ h then S j else A
    have hlow (j : ℕ) (hj : j ≤ h) : S' j = S j := by simp only [S', hj, ite_true, if_true]
    have hlast : S' (h + 1) = A := by simp only [S', show ¬ h + 1 ≤ h by omega, ite_false, if_false]
    refine ⟨S', hlast, ?_, ?_⟩
    · intro j hj
      by_cases hjh : j ≤ h
      · rw [hlow j hjh]
        exact ⟨(hprop j hjh).1, (hprop j hjh).2.1.trans hBA, (hprop j hjh).2.2⟩
      · have heq : j = h + 1 := by omega
        rw [heq, hlast]
        exact ⟨hA, Subset.rfl, hApos⟩
    · intro j hj
      by_cases hjh : j < h
      · rw [hlow j (by omega), hlow (j + 1) (by omega)]
        exact hstep j hjh
      · have heq : j = h := by omega
        rw [heq, hlow h le_rfl, hlast, hSh]
        exact ⟨hBA, hmass, hreturn⟩

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_BackwardRecurrenceProbability
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Positive probability of all prescribed returns -/

noncomputable section

namespace PolycyclicRecognition

open MeasureTheory Set
open scoped ENNReal NNReal

/-- Backward recurrence and independent sampling together. The thresholds
are the actual normalized masses of the subsequent retained sets. -/
theorem exists_backward_recurrence_probability
    {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]
    (μ : Measure G) [SFinite μ] [μ.IsMulRightInvariant]
    (σ : ℕ → Measure G) [∀ j, IsProbabilityMeasure (σ j)]
    (Q : Set G) (hQfin : μ Q ≠ ∞) (hQpos : 0 < (μ Q).toReal)
    (K R : ℕ → Set G) (hK : ∀ j, ∀ᵐ s ∂σ j, s ∈ K j)
    (hRfin : ∀ j, μ (R j) ≠ ∞) (hRpos : ∀ j, 0 < (μ (R j)).toReal)
    (hQR : ∀ j, ∀ a ∈ Q, ∀ s ∈ K j, a * s ∈ R j)
    (D : ℕ → ℝ) (hD : ∀ j, 0 < D j)
    (hvol : ∀ j, (μ (R j)).toReal ≤ D j * (μ Q).toReal)
    (h : ℕ) (A : Set G) (hA : MeasurableSet A) (hAQ : A ⊆ Q)
    (hApos : 0 < (μ A).toReal) :
    ∃ S : ℕ → Set G, S h = A ∧
      (∀ j, j ≤ h → MeasurableSet (S j) ∧ S j ⊆ A ∧ 0 < (μ (S j)).toReal) ∧
      (∀ j, j < h → S j ⊆ S (j + 1) ∧
        (μ (S (j + 1))).toReal ^ 2 / (2 * D j * (μ Q).toReal) ≤ (μ (S j)).toReal) ∧
      let τ := fun j => Real.toNNReal ((μ (S (j + 1))).toReal / (2 * D j * (μ Q).toReal))
      0 < switchThresholdProduct τ 0 h ∧
        ∀ x ∈ S 0, switchThresholdProduct τ 0 h ≤ survivingSwitchProbability σ S 0 h x := by
  obtain ⟨S, hlast, hsets, hstep⟩ := exists_backward_recurrence_sets μ σ Q hQfin hQpos
    K R hK hRfin hRpos hQR D hD hvol h A hA hAQ hApos
  refine ⟨S, hlast, hsets, fun j hj => ⟨(hstep j hj).1, (hstep j hj).2.1⟩, ?_⟩
  let τ := fun j => Real.toNNReal ((μ (S (j + 1))).toReal / (2 * D j * (μ Q).toReal))
  have hpos (j : ℕ) (hj : j < h) :
      0 < (μ (S (j + 1))).toReal / (2 * D j * (μ Q).toReal) :=
    div_pos (hsets (j + 1) (by omega)).2.2
      (mul_pos (mul_pos (by norm_num) (hD j)) hQpos)
  have hτ (j : ℕ) (hj : j < h) : 0 < τ j := by
    exact Real.toNNReal_pos.mpr (hpos j hj)
  refine ⟨switchThresholdProduct_pos τ 0 h (fun j _ hj => hτ j (by omega)), ?_⟩
  intro x hx
  apply switchThresholdProduct_le_survival σ S τ 0 h _ hx
  intro j hj y hy
  have hjh : j < h := by omega
  have hr := (hstep j hjh).2.2 y hy
  have hfin : twoSampleReturn (σ j) (S (j + 1)) y ≠ ∞ :=
    (twoSampleReturn_le_one (σ j) (S (j + 1)) y).trans_lt (by simp) |>.ne
  have hr' := ENNReal.ofReal_le_ofReal hr
  rw [ENNReal.ofReal_toReal hfin] at hr'
  exact hr'

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_BackwardRecurrenceFamily
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Backward recurrence for a varying family of Haar boxes -/

noncomputable section

namespace PolycyclicRecognition

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology

/-- The elementary change from Haar mass to relative Haar mass in the
quadratic recurrence. -/
theorem normalized_backward_mass_bound {a b q D : ℝ} (hq : 0 < q) (hD : 0 < D)
    (h : b ^ 2 / (2 * D * q) ≤ a) :
    (b / q) ^ 2 / (2 * D) ≤ a / q := by
  have heq : (b / q) ^ 2 / (2 * D) = (b ^ 2 / (2 * D * q)) / q := by
    field_simp
  rw [heq]
  exact div_le_div_of_nonneg_right h hq.le

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_CoordinateMesh
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A polynomial-size coordinate mesh for a bounded parameter cube -/

noncomputable section

namespace PolycyclicRecognition

theorem exists_coordinate_mesh (n : ℕ) {R ρ : ℝ} (hR : 0 ≤ R) (hρ : 0 < ρ) :
    ∃ k : ℕ, (k : ℝ) ≤ 2 * R / ρ + 2 ∧
      ∃ c : (Fin n → Fin k) → (Fin n → ℝ),
        (∀ i, ‖c i‖ ≤ R + ρ) ∧
        ∀ x : Fin n → ℝ, ‖x‖ ≤ R → ∃ i, dist x (c i) ≤ ρ := by
  let k := ⌈2 * R / ρ⌉₊ + 1
  have hratio : 0 ≤ 2 * R / ρ := div_nonneg (by positivity) hρ.le
  have hk : (k : ℝ) ≤ 2 * R / ρ + 2 := by
    dsimp only [k]
    have h := Nat.ceil_lt_add_one hratio
    push_cast
    linarith
  let c := fun i : Fin n → Fin k => fun j => -R + ρ * (i j : ℕ)
  refine ⟨k, hk, c, ?_, ?_⟩
  · intro i
    apply (pi_norm_le_iff_of_nonneg (by positivity : 0 ≤ R + ρ)).mpr
    intro j
    rw [Real.norm_eq_abs, abs_le]
    have hji : (i j : ℕ) ≤ ⌈2 * R / ρ⌉₊ := Nat.le_of_lt_succ (i j).isLt
    have hj : ((i j : ℕ) : ℝ) ≤ (⌈2 * R / ρ⌉₊ : ℝ) := by exact_mod_cast hji
    have hc := Nat.ceil_lt_add_one hratio
    have hp : ρ * ((i j : ℕ) : ℝ) ≤ 2 * R + ρ := by
      have ht := mul_le_mul_of_nonneg_left (hj.trans hc.le) hρ.le
      have he : ρ * (2 * R / ρ + 1) = 2 * R + ρ := by field_simp
      rwa [he] at ht
    dsimp only [c]
    constructor
    · nlinarith [show (0 : ℝ) ≤ ((i j : ℕ) : ℝ) from Nat.cast_nonneg _]
    · linarith
  · intro x hx
    have hxj := (pi_norm_le_iff_of_nonneg hR).mp hx
    let i : Fin n → Fin k := fun j => ⟨⌊(x j + R) / ρ⌋₊, by
      have hj : (x j + R) / ρ ≤ 2 * R / ρ := by
        apply div_le_div_of_nonneg_right _ hρ.le
        have := (abs_le.mp (by simpa only [Real.norm_eq_abs] using hxj j)).2
        linarith
      exact Nat.lt_succ_of_le ((Nat.floor_mono hj).trans (Nat.floor_le_ceil _))⟩
    refine ⟨i, ?_⟩
    rw [dist_eq_norm]
    apply (pi_norm_le_iff_of_nonneg hρ.le).mpr
    intro j
    have hlow : -R ≤ x j := (abs_le.mp (by simpa only [Real.norm_eq_abs] using hxj j)).1
    have hnonneg : 0 ≤ (x j + R) / ρ := div_nonneg (by linarith) hρ.le
    have hlo := (le_div_iff₀ hρ).mp (Nat.floor_le hnonneg)
    have hhi := (div_lt_iff₀ hρ).mp (Nat.lt_floor_add_one ((x j + R) / ρ))
    change ‖x j - (-R + ρ * (⌊(x j + R) / ρ⌋₊ : ℝ))‖ ≤ ρ
    rw [Real.norm_eq_abs, abs_le]
    constructor <;> nlinarith

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_ParameterSplit
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Splitting the independent parameter cube preserves volume -/

namespace PolycyclicRecognition

open MeasureTheory

theorem measurePreserving_finAppend (n k : ℕ) :
    MeasurePreserving (fun p : (Fin n → ℝ) × (Fin k → ℝ) => Fin.append p.1 p.2)
      volume volume := by
  have h₁ := volume_measurePreserving_sumPiEquivProdPi_symm
    (fun _ : Fin n ⊕ Fin k => ℝ)
  have h₂ := volume_measurePreserving_piCongrLeft
    (fun _ : Fin (n + k) => ℝ) finSumFinEquiv
  convert h₂.comp h₁ using 1
  all_goals try with_reducible_and_instances rfl
  ext p i
  obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective i
  simp only [Function.comp_apply]
  rw [MeasurableEquiv.piCongrLeft_apply_apply]
  cases j with
  | inl j =>
      change Fin.append p.1 p.2 (Fin.castAdd k j) = p.1 j
      simp
  | inr j =>
      change Fin.append p.1 p.2 (Fin.natAdd n j) = p.2 j
      simp

end PolycyclicRecognition

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_PolynomialDifferential
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Formal partial derivatives are the actual differential -/

noncomputable section

namespace PolycyclicRecognition

open MvPolynomial
open scoped BigOperators

theorem hasFDerivAt_mvPolynomial_eval {m : ℕ} (p : MvPolynomial (Fin m) ℝ)
    (x : Fin m → ℝ) :
    HasFDerivAt (fun y => MvPolynomial.eval y p) (polynomialDifferential p x) x := by
  classical
  induction p using MvPolynomial.induction_on with
  | C c => simpa [polynomialDifferential, pderiv_C] using hasFDerivAt_const c x
  | add p q hp hq =>
      simp only [map_add]
      refine (hp.add hq).congr_fderiv ?_
      simp [polynomialDifferential, add_smul, Finset.sum_add_distrib]
  | mul_X p j hp =>
      simp only [map_mul, MvPolynomial.eval_X]
      refine (hp.mul (hasFDerivAt_apply j x)).congr_fderiv ?_
      ext v
      simp [polynomialDifferential, Pi.single_apply, add_mul,
        Finset.sum_add_distrib, Finset.mul_sum, apply_ite, ite_mul, mul_assoc]

theorem polynomialDifferential_basis {m : ℕ} (p : MvPolynomial (Fin m) ℝ)
    (x : Fin m → ℝ) (j : Fin m) :
    polynomialDifferential p x (Pi.single j 1) = MvPolynomial.eval x (pderiv j p) := by
  classical
  simp [polynomialDifferential, Pi.single_apply]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_PolynomialMinor
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial derivative minors and their uniform degree bounds -/

noncomputable section

namespace PolycyclicRecognition

open MvPolynomial Matrix
open scoped BigOperators

theorem totalDegree_pderiv_le {m : ℕ} (p : MvPolynomial (Fin m) ℝ) (j : Fin m) :
    (pderiv j p).totalDegree ≤ p.totalDegree - 1 := by
  classical
  unfold totalDegree
  apply Finset.sup_le
  intro s hs
  have hc : (pderiv j p).coeff s ≠ 0 := mem_support_iff.mp hs
  rw [coeff_pderiv] at hc
  have hp : s + Finsupp.single j 1 ∈ p.support :=
    mem_support_iff.mpr (left_ne_zero_of_mul hc)
  have hd := le_totalDegree hp
  rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl),
    Finsupp.sum_single_index (by rfl)] at hd
  change (s.sum fun _ e => e) ≤ p.totalDegree - 1
  omega

theorem totalDegree_polynomialJacobianMinor_le {n k D : ℕ}
    (p : Fin n → MvPolynomial (Fin (n + k)) ℝ)
    (hp : ∀ i, (p i).totalDegree ≤ D) :
    (polynomialJacobianMinor p).totalDegree ≤ n * (D - 1) := by
  classical
  unfold polynomialJacobianMinor
  rw [Matrix.det_apply]
  apply totalDegree_finsetSum_le
  intro σ _
  calc
    _ ≤ (∏ i, pderiv (Fin.castAdd k i) (p (σ i))).totalDegree :=
      totalDegree_smul_le _ _
    _ ≤ ∑ i : Fin n, (pderiv (Fin.castAdd k i) (p (σ i))).totalDegree :=
      totalDegree_finsetProd _ _
    _ ≤ n * (D - 1) := by
      calc
        _ ≤ ∑ _i : Fin n, (D - 1) := Finset.sum_le_sum (fun i _ =>
          (totalDegree_pderiv_le _ _).trans (Nat.sub_le_sub_right (hp (σ i)) 1))
        _ = _ := by simp

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_PolynomialFamilies
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Fixed-degree polynomial formulas in the independent amplitudes -/

noncomputable section

namespace PolycyclicRecognition

open MvPolynomial
open scoped BigOperators

theorem hasPolynomialFormula_const {P : Type} {m : ℕ} (c : P → ℝ) :
    HasPolynomialFormula (fun a (_ : Fin m → ℝ) => c a) :=
  ⟨0, fun a => ⟨C (c a), by simp, fun _ => by simp⟩⟩

theorem hasPolynomialFormula_coordinate {P : Type} {m : ℕ} (j : Fin m) :
    HasPolynomialFormula (fun (_ : P) (x : Fin m → ℝ) => x j) :=
  ⟨1, fun _ => ⟨X j, by simp, fun _ => by simp⟩⟩

theorem HasPolynomialFormula.add {P : Type} {m : ℕ} {f g : P → (Fin m → ℝ) → ℝ}
    (hf : HasPolynomialFormula f) (hg : HasPolynomialFormula g) :
    HasPolynomialFormula (fun a x => f a x + g a x) := by
  obtain ⟨D, hD⟩ := hf
  obtain ⟨E, hE⟩ := hg
  refine ⟨D + E, fun a => ?_⟩
  obtain ⟨p, hp, he⟩ := hD a
  obtain ⟨q, hq, he'⟩ := hE a
  exact ⟨p + q, (totalDegree_add p q).trans (max_le (by omega) (by omega)),
    fun x => by simp [he, he']⟩

theorem HasPolynomialFormula.mul {P : Type} {m : ℕ} {f g : P → (Fin m → ℝ) → ℝ}
    (hf : HasPolynomialFormula f) (hg : HasPolynomialFormula g) :
    HasPolynomialFormula (fun a x => f a x * g a x) := by
  obtain ⟨D, hD⟩ := hf
  obtain ⟨E, hE⟩ := hg
  refine ⟨D + E, fun a => ?_⟩
  obtain ⟨p, hp, he⟩ := hD a
  obtain ⟨q, hq, he'⟩ := hE a
  exact ⟨p * q, (totalDegree_mul p q).trans (Nat.add_le_add hp hq),
    fun x => by simp [he, he']⟩

theorem hasPolynomialFormula_sum {P I : Type} {m : ℕ}
    (s : Finset I) (f : I → P → (Fin m → ℝ) → ℝ)
    (hf : ∀ i ∈ s, HasPolynomialFormula (f i)) :
    HasPolynomialFormula (fun a x => ∑ i ∈ s, f i a x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hasPolynomialFormula_const (P := P) (m := m) (fun _ => 0)
  | @insert i s hi ih =>
      have h₁ := hf i (Finset.mem_insert_self i s)
      have h₂ := ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))
      simpa only [Finset.sum_insert hi] using h₁.add h₂

theorem HasPolynomialCoordinates.exists_uniform_polynomials
    {P : Type} {m n : ℕ} {f : P → (Fin m → ℝ) → (Fin n → ℝ)}
    (hf : HasPolynomialCoordinates f) :
    ∃ D : ℕ, ∃ q : P → Fin n → MvPolynomial (Fin m) ℝ,
      (∀ a i, (q a i).totalDegree ≤ D) ∧
      ∀ a x i, MvPolynomial.eval x (q a i) = f a x i := by
  classical
  choose d hd using hf
  choose q hq hvalue using (fun a i => hd i a)
  refine ⟨∑ i, d i, q, ?_, fun a x i => hvalue a i x⟩
  intro a i
  exact (hq a i).trans (Finset.single_le_sum (fun j _ => Nat.zero_le (d j)) (Finset.mem_univ i))

theorem hasPolynomialCoordinates_const {P : Type} {m n : ℕ} (v : P → Fin n → ℝ) :
    HasPolynomialCoordinates (fun a (_ : Fin m → ℝ) => v a) :=
  fun i => hasPolynomialFormula_const (fun a => v a i)

theorem HasPolynomialCoordinates.smul {P : Type} {m n : ℕ}
    {f : P → (Fin m → ℝ) → (Fin n → ℝ)} {t : P → (Fin m → ℝ) → ℝ}
    (hf : HasPolynomialCoordinates f) (ht : HasPolynomialFormula t) :
    HasPolynomialCoordinates (fun a x => t a x • f a x) :=
  fun i => ht.mul (hf i)

theorem bilinear_pi_expansion {n : ℕ}
    (B : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) (v w : Fin n → ℝ) :
    B v w = ∑ i : Fin n, ∑ j : Fin n,
      (v i * w j) • B (Pi.single i 1) (Pi.single j 1) := by
  calc
    B v w = B (∑ i, v i • Pi.single i 1) (∑ j, w j • Pi.single j 1) := by
      rw [← pi_eq_sum_univ' v, ← pi_eq_sum_univ' w]
    _ = _ := by
      simp only [map_sum, map_smul, sum_apply,
        smul_apply, Finset.smul_sum, smul_smul]
      rw [Finset.sum_comm]
      simp only [mul_comm]

theorem HasPolynomialCoordinates.bilinear {P : Type} {m n : ℕ}
    (B : P → (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] (Fin n → ℝ))
    {f g : P → (Fin m → ℝ) → (Fin n → ℝ)}
    (hf : HasPolynomialCoordinates f) (hg : HasPolynomialCoordinates g) :
    HasPolynomialCoordinates (fun a x => B a (f a x) (g a x)) := by
  intro l
  have he : (fun a x => B a (f a x) (g a x) l) =
      (fun a x => ∑ i : Fin n, ∑ j : Fin n,
        (f a x i * g a x j) * B a (Pi.single i 1) (Pi.single j 1) l) := by
    funext a x
    rw [bilinear_pi_expansion]
    simp
  rw [he]
  apply hasPolynomialFormula_sum
  intro i _
  apply hasPolynomialFormula_sum
  intro j _
  exact ((hf i).mul (hg j)).mul (hasPolynomialFormula_const
    (fun a => B a (Pi.single i 1) (Pi.single j 1) l))

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_PolynomialMinorDifferential
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A polynomial minor is the determinant of the actual slice derivative -/

noncomputable section

namespace PolycyclicRecognition

open MvPolynomial Matrix
open scoped BigOperators

theorem appendParameterLinear_apply (n k : ℕ) (v : Fin n → ℝ) :
    appendParameterLinear n k v = Fin.append v 0 := by
  ext i
  refine Fin.addCases ?_ ?_ i <;> intro j <;> simp [appendParameterLinear]

theorem hasFDerivAt_finAppend {n k : ℕ} (v : Fin n → ℝ) (z : Fin k → ℝ) :
    HasFDerivAt (fun w => Fin.append w z) (appendParameterLinear n k) v := by
  convert (appendParameterLinear n k).hasFDerivAt.add_const (Fin.append 0 z) using 1
  all_goals try with_reducible_and_instances rfl
  ext w i
  refine Fin.addCases ?_ ?_ i <;> intro j <;>
    simp [appendParameterLinear_apply]

theorem hasFDerivAt_polynomialSlice {n k : ℕ}
    (p : Fin n → MvPolynomial (Fin (n + k)) ℝ) (v : Fin n → ℝ) (z : Fin k → ℝ) :
    HasFDerivAt (fun w i => MvPolynomial.eval (Fin.append w z) (p i))
      (polynomialSliceDifferential p v z) v := by
  exact (hasFDerivAt_pi.mpr (fun i => hasFDerivAt_mvPolynomial_eval (p i) (Fin.append v z))).comp v
    (hasFDerivAt_finAppend v z)

theorem eval_polynomialJacobianMinor {n k : ℕ}
    (p : Fin n → MvPolynomial (Fin (n + k)) ℝ) (v : Fin n → ℝ) (z : Fin k → ℝ) :
    MvPolynomial.eval (Fin.append v z) (polynomialJacobianMinor p) =
      (polynomialSliceDifferential p v z).det := by
  classical
  rw [polynomialJacobianMinor, RingHom.map_det]
  change _ = (polynomialSliceDifferential p v z).toLinearMap.det
  rw [← LinearMap.det_toMatrix']
  congr 1
  ext i j
  rw [LinearMap.toMatrix'_apply]
  change MvPolynomial.eval (Fin.append v z) (pderiv (Fin.castAdd k j) (p i)) =
    polynomialDifferential (p i) (Fin.append v z) (appendParameterLinear n k (Pi.single j 1))
  have he : appendParameterLinear n k (Pi.single j 1) = Pi.single (Fin.castAdd k j) 1 := by
    rw [appendParameterLinear_apply]
    ext a
    refine Fin.addCases ?_ ?_ a <;> intro b <;> simp [Pi.single_apply]
    intro h
    have hh := congrArg Fin.val h
    simp only [Fin.val_natAdd, Fin.val_castAdd] at hh
    omega
  rw [he, polynomialDifferential_basis]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_CoordinateMinorPermutation
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Reordering an actual nonzero minor into the sliced coordinates -/

noncomputable section

namespace PolycyclicRecognition

open Set MeasureTheory

theorem exists_fin_equiv_extending_injection {n m : ℕ}
    (j : Fin n → Fin m) (hj : Function.Injective j) :
    ∃ k : ℕ, ∃ e : Fin (n + k) ≃ Fin m, ∀ i, e (Fin.castAdd k i) = j i := by
  classical
  let s : Set (Fin m) := range j
  let k := Fintype.card ↥(sᶜ)
  let ec : ↥(sᶜ) ≃ Fin k := Fintype.equivFin _
  let e : Fin (n + k) ≃ Fin m := finSumFinEquiv.symm.trans
    (((Equiv.ofInjective j hj).sumCongr ec.symm).trans (Equiv.Set.sumCompl (range j)))
  refine ⟨k, e, fun i => ?_⟩
  simp [e]

theorem reindexParameters_norm {l m : ℕ} (e : Fin l ≃ Fin m) (x : Fin l → ℝ) :
    ‖reindexParameters e x‖ = ‖x‖ := by
  have h := (IsometryEquiv.piCongrLeft' (Y := fun _ : Fin l => ℝ) e).isometry.dist_eq x 0
  change dist (reindexParameters e x) (reindexParameters e 0) = dist x 0 at h
  simpa only [map_zero, dist_zero_right] using h

theorem measurePreserving_reindexParameters {l m : ℕ} (e : Fin l ≃ Fin m) :
    MeasurePreserving (reindexParameters e) volume volume := by
  convert volume_measurePreserving_piCongrLeft (fun _ : Fin m => ℝ) e using 1
  all_goals try with_reducible_and_instances rfl
  ext x i
  obtain ⟨j, rfl⟩ := e.surjective i
  rw [MeasurableEquiv.piCongrLeft_apply_apply, reindexParameters_apply_equiv]

theorem HasPolynomialFormula.reindex {P : Type} {l m : ℕ}
    {f : P → (Fin m → ℝ) → ℝ} (hf : HasPolynomialFormula f) (e : Fin l ≃ Fin m) :
    HasPolynomialFormula (fun a x => f a (reindexParameters e x)) := by
  obtain ⟨D, hD⟩ := hf
  refine ⟨D, fun a => ?_⟩
  obtain ⟨p, hp, he⟩ := hD a
  refine ⟨MvPolynomial.rename e.symm p, (MvPolynomial.totalDegree_rename_le _ _).trans hp, ?_⟩
  intro x
  rw [MvPolynomial.eval_rename]
  exact he _

theorem reindexParameters_single {l m : ℕ} (e : Fin l ≃ Fin m) (j : Fin l) :
    reindexParameters e (Pi.single j 1) = Pi.single (e j) 1 := by
  classical
  ext i
  obtain ⟨i, rfl⟩ := e.surjective i
  simp [Pi.single_apply, e.injective.eq_iff]

/-- The selected column determinant is the derivative determinant after reordering. -/
theorem det_reindexed_slice {n k m : ℕ} (e : Fin (n + k) ≃ Fin m)
    (f : (Fin m → ℝ) → (Fin n → ℝ)) (v : Fin n → ℝ) (z : Fin k → ℝ)
    (hf : DifferentiableAt ℝ f (reindexParameters e (Fin.append v z))) :
    (fderiv ℝ (fun w => f (reindexParameters e (Fin.append w z))) v).det =
      (Matrix.of fun i j => fderiv ℝ f (reindexParameters e (Fin.append v z))
        (Pi.single (e (Fin.castAdd k j)) 1) i).det := by
  have hd := hf.hasFDerivAt.comp v
    ((reindexParameters e).hasFDerivAt.comp v (hasFDerivAt_finAppend v z))
  change HasFDerivAt (fun w => f (reindexParameters e (Fin.append w z))) _ v at hd
  rw [hd.fderiv]
  change (ContinuousLinearMap.comp _ _).toLinearMap.det = _
  rw [← LinearMap.det_toMatrix']
  congr 1
  ext i j
  rw [LinearMap.toMatrix'_apply]
  change fderiv ℝ f _ (reindexParameters e (appendParameterLinear n k (Pi.single j 1))) i = _
  have ha : appendParameterLinear n k (Pi.single j 1) = Pi.single (Fin.castAdd k j) 1 := by
    ext a
    refine Fin.addCases ?_ ?_ a <;> intro b <;> simp [appendParameterLinear, Pi.single_apply]
    intro h
    have hh := congrArg Fin.val h
    simp only [Fin.val_natAdd, Fin.val_castAdd] at hh
    omega
  rw [ha, reindexParameters_single]
  rfl

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_DeterminantLowerNorm
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Quantitative invertibility from a determinant lower bound

Compactness bounds the adjugate on the unit ball. Homogeneity then gives
the polynomial loss needed to choose injective patches for polynomial maps.
-/

noncomputable section

namespace PolycyclicRecognition

open Set Metric Matrix
open scoped Matrix.Norms.Operator

theorem exists_adjugate_norm_bound (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (A : Matrix (Fin n) (Fin n) ℝ) (L : ℝ),
      0 < L → ‖A‖ ≤ L → ‖A.adjugate‖ ≤ C * L ^ (n - 1) := by
  have hc : Continuous (fun A : Matrix (Fin n) (Fin n) ℝ => A.adjugate) :=
    continuous_id.matrix_adjugate
  obtain ⟨C, hC, hbound⟩ := (isCompact_closedBall (0 : Matrix (Fin n) (Fin n) ℝ) 1).image hc
    |>.isBounded.exists_pos_norm_le
  refine ⟨C, hC, fun A L hL hA => ?_⟩
  have hunit : L⁻¹ • A ∈ closedBall (0 : Matrix (Fin n) (Fin n) ℝ) 1 := by
    rw [mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hL)]
    exact (inv_mul_le_iff₀ hL).mpr (by simpa using hA)
  have h := hbound _ ⟨L⁻¹ • A, hunit, rfl⟩
  dsimp only at h
  rw [Matrix.adjugate_smul, Fintype.card_fin, norm_smul, Real.norm_eq_abs,
    abs_of_pos (pow_pos (inv_pos.mpr hL) _), inv_pow] at h
  have he := (inv_mul_le_iff₀ (pow_pos hL (n - 1))).mp h
  simpa only [mul_comm] using he

/-- The adjugate identity bounds below the action of the original matrix. -/
theorem determinant_mul_norm_le_adjugate_mul_norm {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ) :
    |A.det| * ‖v‖ ≤ ‖A.adjugate‖ * ‖A *ᵥ v‖ := by
  have he : A.adjugate *ᵥ (A *ᵥ v) = A.det • v := by
    rw [Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec]
  have hb := Matrix.linfty_opNorm_mulVec A.adjugate (A *ᵥ v)
  rw [he, norm_smul, Real.norm_eq_abs] at hb
  exact hb

/-- Uniform lower norm control for all matrices with bounded norm and a
prescribed positive determinant lower bound. -/
theorem exists_determinant_lower_norm_bound (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (A : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) (L η : ℝ),
      0 < L → ‖A‖ ≤ L → η ≤ |A.det| → ∀ v,
      η * ‖v‖ ≤ (C * L ^ (n - 1)) * ‖A v‖ := by
  obtain ⟨C, hC, hbound⟩ := exists_adjugate_norm_bound n
  refine ⟨C, hC, fun A L η hL hA hη v => ?_⟩
  let M := LinearMap.toMatrix' A.toLinearMap
  have hM : ‖M‖ ≤ L := by simpa only [M, Matrix.linfty_opNorm_toMatrix] using hA
  have hb := determinant_mul_norm_le_adjugate_mul_norm M v
  dsimp only [M] at hb
  rw [LinearMap.det_toMatrix', LinearMap.toMatrix'_mulVec] at hb
  exact (mul_le_mul_of_nonneg_right hη (norm_nonneg v)).trans
    (hb.trans (mul_le_mul_of_nonneg_right (hbound M L hL hM) (norm_nonneg (A v))))

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

omit [Nonempty B] in
theorem templateSupportConstant_nonneg : 0 ≤ D.templateSupportConstant :=
  Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg
    (fun _ _ => mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _)))

theorem templateSupport_le_of_nearby {E F : Set W} (hE : IsCompact E) (hneE : E.Nonempty)
    (hF : IsCompact F) {δ : ℝ} (hδ : 0 ≤ δ)
    (hnear : ∀ x ∈ E, ∃ y ∈ F, ‖x - y‖ ≤ δ) :
    D.templateSupport E ≤ D.templateSupport F + D.templateSupportConstant * δ := by
  apply D.templateSupport_le
  intro b
  have hc : (∑ i, (D.multiplicity b i : ℝ) * ‖(D.weight i).toContinuousLinearMap‖) ≤
      D.templateSupportConstant := by
    unfold templateSupportConstant
    exact Finset.single_le_sum
      (f := fun b => ∑ i, (D.multiplicity b i : ℝ) * ‖(D.weight i).toContinuousLinearMap‖)
      (fun b _ => Finset.sum_nonneg
        (fun _ _ => mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _))) (Finset.mem_univ b)
  calc
    D.basisTemplateSupport E b ≤
        ∑ i, (D.multiplicity b i : ℝ) *
          (D.weightSupport F i + ‖(D.weight i).toContinuousLinearMap‖ * δ) :=
      Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left
        (D.weightSupport_le_of_nearby hE hneE hF hnear i) (Nat.cast_nonneg _))
    _ = D.basisTemplateSupport F b +
        (∑ i, (D.multiplicity b i : ℝ) * ‖(D.weight i).toContinuousLinearMap‖) * δ := by
      simp only [basisTemplateSupport, mul_add, Finset.sum_add_distrib, Finset.sum_mul, mul_assoc]
    _ ≤ D.templateSupport F + D.templateSupportConstant * δ :=
      add_le_add (D.basisTemplateSupport_le F b) (mul_le_mul_of_nonneg_right hc hδ)

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
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_PolynomialEndpointSchemes
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.basisDynkinParameter_zero _root_.OAI.PolycyclicRecognition.dynkinRightTranslation_apply _root_.OAI.PolycyclicRecognition.dynkinRightTranslation_symm_apply _root_.OAI.PolycyclicRecognition.exponentialHomOfDynkin_apply_exp _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Smooth generator endpoint maps for varying polynomial laws

Each scheme is a fixed finite expression in the bracket, generators, and
its variable amplitudes. Consequently it remains smooth outside the set of
valid group laws, as required for the parameter-preserving submersion theorem.
-/

noncomputable section

namespace PolycyclicRecognition

open Module

variable {V P I : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup P] [NormedSpace ℝ P]

theorem contDiff_polynomialListProduct_ofFn {c n : ℕ} {k : ℕ∞}
    (a : DynkinCoefficients c 2) (B : P → V →L[ℝ] V →L[ℝ] V)
    (X : P → Fin n → V) (hB : ContDiff ℝ k B)
    (hX : ∀ i, ContDiff ℝ k (fun p => X p i)) :
    ContDiff ℝ k (fun p => polynomialListProduct (dynkinProduct a (B p)) (List.ofFn (X p))) := by
  induction n with
  | zero => simpa [List.ofFn_zero, polynomialListProduct] using
      (contDiff_const : ContDiff ℝ k (fun _ : P => (0 : V)))
  | succ n ih =>
    simp only [List.ofFn_succ, polynomialListProduct]
    exact contDiff_dynkinProduct a B _ _ hB (hX 0)
      (ih (fun p i => X p i.succ) (fun i => hX i.succ))

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_PolynomialEndpointCoordinates
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.basisDynkinParameter_zero _root_.OAI.PolycyclicRecognition.dynkinRightTranslation_apply _root_.OAI.PolycyclicRecognition.dynkinRightTranslation_symm_apply _root_.OAI.PolycyclicRecognition.exponentialHomOfDynkin_apply_exp _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual generator endpoint schemes have uniformly bounded degree -/

noncomputable section

namespace PolycyclicRecognition

open scoped BigOperators

theorem hasPolynomialCoordinates_sum {P I : Type} {m n : ℕ}
    (s : Finset I) (f : I → P → (Fin m → ℝ) → (Fin n → ℝ))
    (hf : ∀ i ∈ s, HasPolynomialCoordinates (f i)) :
    HasPolynomialCoordinates (fun a x => ∑ i ∈ s, f i a x) := by
  intro l
  simpa only [Finset.sum_apply] using hasPolynomialFormula_sum s
    (fun i a x => f i a x l) (fun i hi => hf i hi l)

theorem hasPolynomialCoordinates_evalBilinearWord
    {P I : Type} {m n : ℕ}
    (B : P → (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] (Fin n → ℝ))
    (X : P → (Fin m → ℝ) → I → (Fin n → ℝ))
    (hX : ∀ i, HasPolynomialCoordinates (fun a x => X a x i)) (w : FreeMagma I) :
    HasPolynomialCoordinates (fun a x => evalBilinearWord (B a) (X a x) w) := by
  induction w using FreeMagma.rec with
  | of i => exact hX i
  | mul u v hu hv => exact hu.bilinear B hv

theorem hasPolynomialCoordinates_bilinearDynkin
    {P : Type} {m n c l : ℕ} (a : DynkinCoefficients c l)
    (B : P → (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] (Fin n → ℝ))
    (X : P → (Fin m → ℝ) → Fin l → (Fin n → ℝ))
    (hX : ∀ i, HasPolynomialCoordinates (fun b x => X b x i)) :
    HasPolynomialCoordinates (fun b x => bilinearDynkinPolynomial a (B b) (X b x)) := by
  apply hasPolynomialCoordinates_sum
  intro d _
  apply hasPolynomialCoordinates_sum
  intro w _
  exact (hasPolynomialCoordinates_evalBilinearWord B X hX _).smul
    (hasPolynomialFormula_const (fun _ => a d w))

theorem hasPolynomialCoordinates_dynkinProduct
    {P : Type} {m n c : ℕ} (a : DynkinCoefficients c 2)
    (B : P → (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] (Fin n → ℝ))
    {f g : P → (Fin m → ℝ) → (Fin n → ℝ)}
    (hf : HasPolynomialCoordinates f) (hg : HasPolynomialCoordinates g) :
    HasPolynomialCoordinates (fun b x => dynkinProduct a (B b) (f b x) (g b x)) := by
  apply hasPolynomialCoordinates_bilinearDynkin a B (fun b x => ![f b x, g b x])
  intro i
  fin_cases i
  · exact hf
  · exact hg

theorem hasPolynomialCoordinates_listProduct
    {P : Type} {m n c l : ℕ} (a : DynkinCoefficients c 2)
    (B : P → (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] (Fin n → ℝ))
    (X : P → (Fin m → ℝ) → Fin l → (Fin n → ℝ))
    (hX : ∀ i, HasPolynomialCoordinates (fun b x => X b x i)) :
    HasPolynomialCoordinates (fun b x =>
      polynomialListProduct (dynkinProduct a (B b)) (List.ofFn (X b x))) := by
  induction l with
  | zero => simpa [polynomialListProduct] using
      hasPolynomialCoordinates_const (m := m) (fun _ : P => (0 : Fin n → ℝ))
  | succ l ih =>
    simp only [List.ofFn_succ, polynomialListProduct]
    exact hasPolynomialCoordinates_dynkinProduct a B (hX 0)
      (ih (fun b x i => X b x i.succ) (fun i => hX i.succ))

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_SurjectiveColumns
attribute [-instance] _root_.GeneratesNS.fintype_closedBall _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A surjective differential has a fixed nonzero column minor -/

noncomputable section

namespace PolycyclicRecognition

open Module Set

theorem exists_nonsingular_column_minor {n m : ℕ}
    (A : (Fin m → ℝ) →ₗ[ℝ] (Fin n → ℝ)) (hA : Function.Surjective A) :
    ∃ j : Fin n → Fin m, Function.Injective j ∧
      (Matrix.of fun i k => A (Pi.single (j k) 1) i).det ≠ 0 := by
  classical
  let v : Fin m → (Fin n → ℝ) := fun i => A (Pi.single i 1)
  have hspan : ⊤ ≤ Submodule.span ℝ (range v) := by
    intro y _
    obtain ⟨x, rfl⟩ := hA y
    rw [pi_eq_sum_univ' x, map_sum]
    apply Submodule.sum_mem
    intro i _
    rw [map_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (mem_range_self i))
  let J := (linearIndepOn_empty ℝ (id : (Fin n → ℝ) → (Fin n → ℝ))).extend (empty_subset (range v))
  let b : Basis J ℝ (Fin n → ℝ) := Basis.ofSpan hspan
  let : Fintype J := Fintype.ofFinite _
  let e : J ≃ Fin n := Fintype.equivFinOfCardEq (by simpa using (finrank_eq_card_basis b).symm)
  let b' := b.reindex e
  have hb (k : Fin n) : ∃ i, v i = b' k := by
    simpa only [b', Basis.coe_reindex, Function.comp_apply, Set.mem_range] using
      (Basis.ofSpan_subset hspan (show b (e.symm k) ∈ range b from ⟨_, rfl⟩))
  choose j hj using hb
  refine ⟨j, ?_, ?_⟩
  · intro x y hxy
    apply b'.injective
    rw [← hj x, ← hj y, hxy]
  · have he : (Matrix.of fun i k => A (Pi.single (j k) 1) i) =
        LinearMap.toMatrix' b'.equivFun.symm.toLinearMap := by
      ext i k
      rw [LinearMap.toMatrix'_apply]
      change A (Pi.single (j k) 1) i = b'.equivFun.symm (Pi.single k 1) i
      have hs : b'.equivFun.symm (Pi.single k 1) = b' k := by
        apply b'.equivFun.injective
        simp
      rw [hs]
      exact congrFun (hj k) i
    rw [he, LinearMap.det_toMatrix']
    exact b'.equivFun.symm.isUnit_det'.ne_zero

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_PolynomialLargeValueSet
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_countable _root_.OAI.PolycyclicRecognition.finitelyGeneratedSubgroupIndex_countable _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Keeping compact parameter mass away from a polynomial zero set -/

noncomputable section

namespace PolycyclicRecognition

open Set Metric MeasureTheory
open scoped ENNReal

theorem exists_compact_large_polynomial_values
    (rem : RemezPolynomialInput) (n D : ℕ) (hn : 1 ≤ n) (hD : 1 ≤ D) :
    ∃ A : ℝ, 0 < A ∧
      ∀ (p : MvPolynomial (Fin n) ℝ), p.totalDegree ≤ D →
      ∀ (R c : ℝ), 1 ≤ R → 0 < c →
      ∀ x₀ ∈ closedBall 0 R, c ≤ |MvPolynomial.eval x₀ p| →
      ∀ E : Set (Fin n → ℝ), MeasurableSet E → E ⊆ closedBall 0 R →
      0 < (volume E).toReal →
      let η := (c / 2) / (2 * A * (1 + R) ^ n / (volume E).toReal) ^ (n * D)
      ∃ K : Set (Fin n → ℝ), K ⊆ E ∧ IsCompact K ∧
        (volume E).toReal / 4 < (volume K).toReal ∧
        ∀ x ∈ K, η ≤ |MvPolynomial.eval x p| := by
  obtain ⟨A, hA, hrem⟩ := rem n D hn hD
  refine ⟨A, hA, ?_⟩
  intro p hp R c hR hc x₀ hx₀ hx₀c E hE hER hm
  let m := (volume E).toReal
  let a := 2 * A * (1 + R) ^ n / m
  let η := (c / 2) / a ^ (n * D)
  have ha : 0 < a := by dsimp [a, m] <;> positivity
  have hη : 0 < η := by dsimp [η] <;> positivity
  have hEfinite : volume E ≠ ∞ :=
    measure_ne_top_of_subset hER (isCompact_closedBall (0 : Fin n → ℝ) R).measure_ne_top
  let B := E ∩ {x | |MvPolynomial.eval x p| < η}
  let G := E ∩ {x | η ≤ |MvPolynomial.eval x p|}
  have hB : MeasurableSet B := hE.inter
    (isOpen_lt p.continuous_eval.abs continuous_const).measurableSet
  have hG : MeasurableSet G := hE.inter
    (isClosed_le continuous_const p.continuous_eval.abs).measurableSet
  have hBfinite : volume B ≠ ∞ := measure_ne_top_of_subset inter_subset_left hEfinite
  have hGfinite : volume G ≠ ∞ := measure_ne_top_of_subset inter_subset_left hEfinite
  have hBmass : (volume B).toReal ≤ m / 2 := by
    by_contra h
    have hlarge : m / 2 < (volume B).toReal := lt_of_not_ge h
    have hBpos : 0 < (volume B).toReal := (by dsimp [m]; positivity : 0 < m / 2).trans hlarge
    have hpoint := hrem p hp R hR B hB (inter_subset_left.trans hER) hBpos
      η hη.le (fun x hx => hx.2.le) x₀ hx₀
    have hquot : A * (1 + R) ^ n / (volume B).toReal ≤ a := by
      dsimp [a]
      apply (div_le_div_iff₀ hBpos hm).mpr
      have hnonneg : 0 ≤ A * (1 + R) ^ n := by positivity
      nlinarith
    have hpow : (A * (1 + R) ^ n / (volume B).toReal) ^ (n * D) ≤ a ^ (n * D) :=
      pow_le_pow_left₀ (by positivity) hquot (n * D)
    have he : a ^ (n * D) * η = c / 2 := by
      dsimp [η]
      field_simp
    have hlast : c ≤ c / 2 := calc
      c ≤ |MvPolynomial.eval x₀ p| := hx₀c
      _ ≤ (A * (1 + R) ^ n / (volume B).toReal) ^ (n * D) * η := hpoint
      _ ≤ a ^ (n * D) * η := mul_le_mul_of_nonneg_right hpow hη.le
      _ = c / 2 := he
    linarith
  have hEG : E = B ∪ G := by
    ext x
    simp only [B, G, mem_union, mem_inter_iff, mem_ofPred_eq]
    constructor
    · intro hx
      rcases lt_or_ge |MvPolynomial.eval x p| η with h | h
      · exact Or.inl ⟨hx, h⟩
      · exact Or.inr ⟨hx, h⟩
    · rintro (⟨hx, _⟩ | ⟨hx, _⟩) <;> exact hx
  have hGmass : m / 2 ≤ (volume G).toReal := by
    have hu := measureReal_union_le (μ := volume) B G
    rw [← hEG] at hu
    change m ≤ (volume B).toReal + (volume G).toReal at hu
    linarith
  have hstrict : ENNReal.ofReal (m / 4) < volume G := by
    apply (ENNReal.toReal_lt_toReal (by simp) hGfinite).mp
    rw [ENNReal.toReal_ofReal (by positivity)]
    linarith
  obtain ⟨K, hKG, hK, hKmass⟩ := hG.exists_lt_isCompact hstrict
  refine ⟨K, hKG.trans inter_subset_left, hK, ?_, fun x hx => (hKG hx).2⟩
  have hh := (ENNReal.toReal_lt_toReal (by simp) hK.measure_ne_top).mpr hKmass
  simpa only [ENNReal.toReal_ofReal (by positivity : 0 ≤ m / 4)] using hh

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_SectionVolume
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Retaining parameter volume on one coordinate slice -/

namespace PolycyclicRecognition

open MeasureTheory Set
open scoped ENNReal

/-- Fubini gives a large section without choosing a measurable family of
representatives for the image of the parameter set. -/
theorem exists_section_measure_gt
    {V Z : Type} [MeasurableSpace V] [MeasurableSpace Z]
    (μ : Measure V) (ν : Measure Z) [SFinite μ] [SFinite ν]
    {K : Set (V × Z)} (hK : MeasurableSet K)
    {Q : Set Z} (hQ : MeasurableSet Q)
    (hKQ : ∀ p ∈ K, p.2 ∈ Q) (t : ℝ≥0∞)
    (hmass : t * ν Q < (μ.prod ν) K) :
    ∃ z ∈ Q, t < μ {v | (v, z) ∈ K} := by
  by_contra h
  have hbound (z : Z) : μ {v | (v, z) ∈ K} ≤ Q.indicator (fun _ => t) z := by
    by_cases hz : z ∈ Q
    · rw [indicator_of_mem hz]
      exact le_of_not_gt (fun ht => h ⟨z, hz, ht⟩)
    · have hempty : {v | (v, z) ∈ K} = ∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        intro v hv
        exact hz (hKQ (v, z) hv)
      rw [hempty, measure_empty, indicator_of_notMem hz]
  have he : (μ.prod ν) K ≤ t * ν Q := by
    rw [Measure.prod_apply_symm hK]
    calc
      _ ≤ ∫⁻ z, Q.indicator (fun _ => t) z ∂ν := lintegral_mono hbound
      _ = t * ν Q := by rw [lintegral_indicator hQ]; simp
  exact not_lt_of_ge he hmass

end PolycyclicRecognition

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_CompactSectionVolume
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_countable _root_.OAI.PolycyclicRecognition.finitelyGeneratedSubgroupIndex_countable _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Compact coordinate sections with quantitative retained volume -/

noncomputable section

namespace PolycyclicRecognition

open Set MeasureTheory
open scoped ENNReal

theorem isCompact_coordinate_section
    {V Z : Type} [TopologicalSpace V] [TopologicalSpace Z] [T1Space Z]
    {K : Set (V × Z)} (hK : IsCompact K) (z : Z) :
    IsCompact {v | (v, z) ∈ K} := by
  have he : {v | (v, z) ∈ K} =
      Prod.fst '' (K ∩ Prod.snd ⁻¹' {z}) := by
    ext v
    constructor
    · intro hv
      exact ⟨(v, z), ⟨hv, rfl⟩, rfl⟩
    · rintro ⟨⟨w, y⟩, ⟨hw, hy⟩, rfl⟩
      simp only [mem_preimage, mem_singleton_iff] at hy
      change (w, z) ∈ K
      simpa only [hy] using hw
  rw [he]
  exact (hK.inter_right (isClosed_singleton.preimage continuous_snd)).image continuous_fst

theorem exists_compact_section_volume_gt
    (n k : ℕ) {K : Set ((Fin n → ℝ) × (Fin k → ℝ))}
    (hK : IsCompact K) {Q : Set (Fin k → ℝ)} (hQ : IsCompact Q)
    (hKQ : ∀ p ∈ K, p.2 ∈ Q)
    {t q : ℝ} (ht : 0 ≤ t) (hq : (volume Q).toReal ≤ q)
    (hmass : t * q < (volume K).toReal) :
    ∃ z ∈ Q, IsCompact {v | (v, z) ∈ K} ∧
      t < (volume {v | (v, z) ∈ K}).toReal := by
  have hlt : ENNReal.ofReal t * volume Q < volume K := by
    apply (ENNReal.toReal_lt_toReal
      (ENNReal.mul_ne_top (by simp) hQ.measure_ne_top) hK.measure_ne_top).mp
    simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal ht]
    exact (mul_le_mul_of_nonneg_left hq ht).trans_lt hmass
  obtain ⟨z, hz, hvolume⟩ := exists_section_measure_gt volume volume hK.measurableSet
    hQ.measurableSet hKQ (ENNReal.ofReal t) hlt
  have hsection := isCompact_coordinate_section hK z
  refine ⟨z, hz, hsection, ?_⟩
  have hh := (ENNReal.toReal_lt_toReal (by simp) hsection.measure_ne_top).mpr hvolume
  simpa only [ENNReal.toReal_ofReal ht] using hh

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_InjectivePatchVolume
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Volume lower bounds from a controlled finite injective cover

This is the change-of-variables step for measurable polynomial parameters.
The parameter set itself need not contain an open set. When it is compact,
the image used below is a compact witness for inner volume.
-/

noncomputable section

namespace PolycyclicRecognition

open MeasureTheory Set
open scoped ENNReal NNReal BigOperators

theorem volume_image_lower_of_finite_injective_cover
    {V I : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V]
    (μ : Measure V) [μ.IsAddHaarMeasure]
    (f : V → V) (df : V → V →L[ℝ] V)
    {K : Set V} (hK : MeasurableSet K) (s : Finset I) (U : I → Set V)
    (hU : ∀ i ∈ s, MeasurableSet (U i))
    (hcover : K ⊆ ⋃ i ∈ s, U i)
    (hdf : ∀ x ∈ K, HasFDerivAt f (df x) x)
    (hinj : ∀ i ∈ s, Set.InjOn f (K ∩ U i))
    (η : ℝ≥0) (hdet : ∀ x ∈ K, (η : ℝ) ≤ |(df x).det|) :
    (η : ℝ≥0∞) * μ K ≤ (s.card : ℝ≥0∞) * μ (f '' K) := by
  classical
  have hcover' : K ⊆ ⋃ i ∈ s, K ∩ U i := by
    intro x hx
    obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp (hcover hx)
    exact mem_iUnion₂.mpr ⟨i, hi, hx, hxi⟩
  have hmass : μ K ≤ ∑ i ∈ s, μ (K ∩ U i) :=
    (measure_mono hcover').trans (measure_biUnion_finset_le s (fun i => K ∩ U i))
  calc
    (η : ℝ≥0∞) * μ K ≤ η * ∑ i ∈ s, μ (K ∩ U i) := mul_le_mul' le_rfl hmass
    _ = ∑ i ∈ s, (η : ℝ≥0∞) * μ (K ∩ U i) := by rw [Finset.mul_sum]
    _ ≤ ∑ _i ∈ s, μ (f '' K) := by
      apply Finset.sum_le_sum
      intro i hi
      calc
        (η : ℝ≥0∞) * μ (K ∩ U i) = ∫⁻ _x in K ∩ U i, (η : ℝ≥0∞) ∂μ := by simp
        _ ≤ ∫⁻ x in K ∩ U i, ENNReal.ofReal |(df x).det| ∂μ := by
          apply setLIntegral_mono' (hK.inter (hU i hi))
          intro x hx
          rw [← ENNReal.ofReal_coe_nnreal]
          exact ENNReal.ofReal_le_ofReal (hdet x hx.1)
        _ = μ (f '' (K ∩ U i)) :=
          lintegral_abs_det_fderiv_eq_addHaar_image μ (hK.inter (hU i hi))
            (fun x hx => (hdf x hx.1).hasFDerivWithinAt) (hinj i hi)
        _ ≤ μ (f '' K) := measure_mono (image_mono inter_subset_left)
    _ = (s.card : ℝ≥0∞) * μ (f '' K) := by simp

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_DerivativeOscillation
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Injectivity on convex patches with controlled derivative oscillation -/

namespace PolycyclicRecognition

open Set

theorem injOn_of_derivative_oscillation
    {V W : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (f : V → W) (df : V → V →L[ℝ] W) (A : V →L[ℝ] W)
    {S : Set V} (hS : Convex ℝ S)
    (hf : ∀ x ∈ S, HasFDerivAt f (df x) x)
    {η D ε : ℝ} (hD : 0 ≤ D) (hgap : D * ε < η)
    (hA : ∀ v, η * ‖v‖ ≤ D * ‖A v‖)
    (hosc : ∀ x ∈ S, ‖df x - A‖ ≤ ε) : Set.InjOn f S := by
  intro x hx y hy hxy
  have he := hS.norm_image_sub_le_of_norm_hasFDerivWithin_le
    (f := fun z => f z - A z) (f' := fun z => df z - A)
    (fun z hz => ((hf z hz).sub A.hasFDerivAt).hasFDerivWithinAt)
    hosc hx hy
  have hn : ‖A (y - x)‖ ≤ ε * ‖y - x‖ := by
    rw [map_sub, norm_sub_rev]
    simpa only [hxy, sub_sub_sub_cancel_left] using he
  have hb := (hA (y - x)).trans (mul_le_mul_of_nonneg_left hn hD)
  have hz : ‖y - x‖ = 0 := by nlinarith [norm_nonneg (y - x)]
  exact (sub_eq_zero.mp (norm_eq_zero.mp hz)).symm

end PolycyclicRecognition

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_QuantitativeInjectiveCover
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Quantitative injective patches near nondegenerate derivatives -/

noncomputable section

namespace PolycyclicRecognition

open Set Metric

theorem exists_quantitative_injective_cover (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (f : (Fin n → ℝ) → (Fin n → ℝ))
        (df : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] (Fin n → ℝ))
        (R L η : ℝ), 0 ≤ R → 1 ≤ L → 0 < η →
      (∀ z, ‖z‖ ≤ R + 2 → HasFDerivAt f (df z) z) →
      (∀ z, ‖z‖ ≤ R + 2 → ‖df z‖ ≤ L) →
      (∀ z w, ‖z‖ ≤ R + 2 → ‖w‖ ≤ R + 2 →
        ‖df z - df w‖ ≤ L * dist z w) →
      ∃ (ρ : ℝ) (k : ℕ) (c : (Fin n → Fin k) → (Fin n → ℝ)),
        ρ = min 1 (η / (8 * (C * L ^ (n - 1)) * L)) ∧ 0 < ρ ∧
        (k : ℝ) ≤ 2 * R / ρ + 2 ∧
        (∀ z, ‖z‖ ≤ R → ∃ i, z ∈ closedBall (c i) ρ) ∧
        ∀ i, Set.InjOn f
          ({z | ‖z‖ ≤ R ∧ η ≤ |(df z).det|} ∩ closedBall (c i) ρ) := by
  obtain ⟨C, hC, hbound⟩ := exists_determinant_lower_norm_bound n
  refine ⟨C, hC, ?_⟩
  intro f df R L η hR hL hη hf hdf hosc
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL
  let D := C * L ^ (n - 1)
  have hD : 0 < D := mul_pos hC (pow_pos hLpos _)
  let ρ := min 1 (η / (8 * D * L))
  have hρ : 0 < ρ := lt_min zero_lt_one (div_pos hη (by positivity))
  have hρone : ρ ≤ 1 := min_le_left _ _
  have hgap : D * (2 * L * ρ) < η := by
    have hρle : ρ ≤ η / (8 * D * L) := min_le_right _ _
    have hh := (le_div_iff₀ (show 0 < 8 * D * L by positivity)).mp hρle
    nlinarith
  obtain ⟨k, hk, c, hc, hcover⟩ := exists_coordinate_mesh n hR hρ
  refine ⟨ρ, k, c, rfl, hρ, hk, ?_, ?_⟩
  · intro z hz
    obtain ⟨i, hi⟩ := hcover z hz
    exact ⟨i, hi⟩
  · intro i
    by_cases hempty : ({z | ‖z‖ ≤ R ∧ η ≤ |(df z).det|} ∩ closedBall (c i) ρ).Nonempty
    · obtain ⟨z₀, hz₀, hz₀ball⟩ := hempty
      have hbig (z : Fin n → ℝ) (hz : z ∈ closedBall (c i) ρ) : ‖z‖ ≤ R + 2 := by
        have he : ‖z‖ ≤ ‖z - c i‖ + ‖c i‖ := by
          simpa only [dist_eq_norm, sub_zero] using dist_triangle z (c i) 0
        have hd : ‖z - c i‖ ≤ ρ := hz
        have hh := hc i
        linarith
      have hi : Set.InjOn f (closedBall (c i) ρ) := by
        apply injOn_of_derivative_oscillation f df (df z₀) (convex_closedBall _ _)
          (fun z hz => hf z (hbig z hz)) hD.le hgap
        · exact hbound (df z₀) L η hLpos (hdf z₀ (hbig z₀ hz₀ball)) hz₀.2
        · intro z hz
          have hd : dist z z₀ ≤ 2 * ρ := by
            calc
              dist z z₀ ≤ dist z (c i) + dist (c i) z₀ := dist_triangle _ _ _
              _ ≤ ρ + ρ := add_le_add hz
                (by simpa only [dist_comm] using (mem_closedBall.mp hz₀ball))
              _ = 2 * ρ := by ring
          exact (hosc z z₀ (hbig z hz) (hbig z₀ hz₀ball)).trans
            (by nlinarith [mul_le_mul_of_nonneg_left hd hLpos.le])
      exact hi.mono inter_subset_right
    · simpa only [not_nonempty_iff_eq_empty.mp hempty] using (Set.injOn_empty f)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_CompactImageVolume
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_countable _root_.OAI.PolycyclicRecognition.finitelyGeneratedSubgroupIndex_countable _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Quantitative compact image volume away from the critical set -/

noncomputable section

namespace PolycyclicRecognition

open Set Metric MeasureTheory
open scoped ENNReal NNReal

theorem exists_compact_image_volume_bound (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (f : (Fin n → ℝ) → (Fin n → ℝ))
        (df : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] (Fin n → ℝ))
        (R L η : ℝ), 0 ≤ R → 1 ≤ L → 0 < η →
      (∀ z, ‖z‖ ≤ R + 2 → HasFDerivAt f (df z) z) →
      (∀ z, ‖z‖ ≤ R + 2 → ‖df z‖ ≤ L) →
      (∀ z w, ‖z‖ ≤ R + 2 → ‖w‖ ≤ R + 2 →
        ‖df z - df w‖ ≤ L * dist z w) →
      ∀ K : Set (Fin n → ℝ), IsCompact K →
      (∀ z ∈ K, ‖z‖ ≤ R ∧ η ≤ |(df z).det|) →
      let ρ := min 1 (η / (8 * (C * L ^ (n - 1)) * L))
      IsCompact (f '' K) ∧
        η * (volume K).toReal ≤ (2 * R / ρ + 2) ^ n * (volume (f '' K)).toReal := by
  classical
  obtain ⟨C, hC, hcover⟩ := exists_quantitative_injective_cover n
  refine ⟨C, hC, ?_⟩
  intro f df R L η hR hL hη hf hdf hosc K hK hgood
  obtain ⟨ρ, k, c, hρeq, hρ, hk, hcov, hinj⟩ := hcover f df R L η hR hL hη hf hdf hosc
  have hcont : ContinuousOn f K := fun z hz =>
    (hf z (by have := (hgood z hz).1; linarith)).continuousAt.continuousWithinAt
  have himage : IsCompact (f '' K) := hK.image_of_continuousOn hcont
  have hinjK (i : Fin n → Fin k) : Set.InjOn f (K ∩ closedBall (c i) ρ) := by
    intro z hz w hw he
    exact hinj i ⟨hgood z hz.1, hz.2⟩ ⟨hgood w hw.1, hw.2⟩ he
  have hb := volume_image_lower_of_finite_injective_cover volume f df hK.measurableSet
    (Finset.univ : Finset (Fin n → Fin k)) (fun i => closedBall (c i) ρ)
    (fun _ _ => measurableSet_closedBall) (fun z hz => by
      obtain ⟨i, hi⟩ := hcov z (hgood z hz).1
      exact mem_iUnion₂.mpr ⟨i, Finset.mem_univ _, hi⟩)
    (fun z hz => hf z (by have := (hgood z hz).1; linarith))
    (fun i _ => hinjK i)
    (Real.toNNReal η) (fun z hz => by simpa [Real.coe_toNNReal η hη.le] using (hgood z hz).2)
  have ht := ENNReal.toReal_mono
    (ENNReal.mul_ne_top (by simp) himage.measure_ne_top) hb
  have hr : η * (volume K).toReal ≤ (k : ℝ) ^ n * (volume (f '' K)).toReal := by
    simpa only [ENNReal.toReal_mul, ENNReal.coe_toReal, Real.coe_toNNReal η hη.le,
      Finset.card_univ, Fintype.card_fun, Fintype.card_fin, ENNReal.toReal_natCast,
      ENNReal.toReal_pow, Nat.cast_pow] using ht
  have hpow : (k : ℝ) ^ n ≤ (2 * R / ρ + 2) ^ n :=
    pow_le_pow_left₀ (Nat.cast_nonneg k) hk n
  subst ρ
  exact ⟨himage, hr.trans (mul_le_mul_of_nonneg_right hpow ENNReal.toReal_nonneg)⟩

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CompactDerivativeBounds
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform derivative bounds on a compact family of endpoint maps -/

noncomputable section

namespace PolycyclicRecognition

open Set Metric

theorem compact_family_derivative_bounds
    {P V W : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (f : P × V → W) (hf : ContDiff ℝ 2 f)
    {S : Set P} (hS : IsCompact S) (R : ℝ) :
    ∃ L : ℝ, 1 ≤ L ∧
      (∀ p ∈ S, ∀ v, ‖v‖ ≤ R → ‖fderiv ℝ (fun w => f (p, w)) v‖ ≤ L) ∧
      ∀ p ∈ S, ∀ v w, ‖v‖ ≤ R → ‖w‖ ≤ R →
        ‖fderiv ℝ (fun u => f (p, u)) v - fderiv ℝ (fun u => f (p, u)) w‖ ≤
          L * dist v w := by
  let df : P × V → V →L[ℝ] W := fun z => fderiv ℝ (fun w => f (z.1, w)) z.2
  have hdf : ContDiff ℝ 1 df := by
    apply ContDiff.fderiv (g := Prod.snd)
      (hf.comp (contDiff_fst.fst.prodMk contDiff_snd)) contDiff_snd
    norm_num
  let K := S ×ˢ closedBall (0 : V) R
  have hK : IsCompact K := hS.prod (isCompact_closedBall _ _)
  obtain ⟨C₁, hC₁, hb₁⟩ := (hK.image hdf.continuous).isBounded.exists_pos_norm_le
  obtain ⟨C₂, hC₂, hb₂⟩ := (hK.image (hdf.continuous_fderiv one_ne_zero)).isBounded.exists_pos_norm_le
  let L := max 1 (max C₁ C₂)
  have hL₁ : C₁ ≤ L := (le_max_left C₁ C₂).trans (le_max_right 1 _)
  have hL₂ : C₂ ≤ L := (le_max_right C₁ C₂).trans (le_max_right 1 _)
  refine ⟨L, le_max_left _ _, ?_, ?_⟩
  · intro p hp v hv
    exact (hb₁ _ ⟨(p, v), ⟨hp, by simpa using hv⟩, rfl⟩).trans hL₁
  · intro p hp v w hv hw
    have hder (u : V) : HasFDerivAt (fun x => df (p, x))
        ((fderiv ℝ df (p, u)).comp (ContinuousLinearMap.inr ℝ P V)) u := by
      exact (hdf.differentiable one_ne_zero (p, u)).hasFDerivAt.comp u
        ((hasFDerivAt_const p u).prodMk (hasFDerivAt_id u))
    have hbound (u : V) (hu : u ∈ closedBall 0 R) :
        ‖(fderiv ℝ df (p, u)).comp (ContinuousLinearMap.inr ℝ P V)‖ ≤ L := by
      calc
        _ ≤ ‖fderiv ℝ df (p, u)‖ * ‖ContinuousLinearMap.inr ℝ P V‖ :=
          ContinuousLinearMap.opNorm_comp_le _ _
        _ ≤ ‖fderiv ℝ df (p, u)‖ * 1 := mul_le_mul_of_nonneg_left
          (ContinuousLinearMap.norm_inr_le_one ℝ P V) (norm_nonneg (fderiv ℝ df (p, u)))
        _ ≤ L := by simpa using (hb₂ _ ⟨(p, u), ⟨hp, hu⟩, rfl⟩).trans hL₂
    have hh := (convex_closedBall (0 : V) R).norm_image_sub_le_of_norm_hasFDerivWithin_le
      (fun u _ => (hder u).hasFDerivWithinAt) hbound
      (by simpa using hw) (by simpa using hv)
    simpa only [df, dist_eq_norm] using hh

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_SmoothPolynomialFamilyImage
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Measurable images in a compact smooth polynomial family

Smoothness supplies all local differential bounds. The polynomial formulas
supply the actual minor and its fixed degree. Only scalar Remez is external.
-/

noncomputable section

namespace PolycyclicRecognition

open Set Metric MeasureTheory

theorem contDiff_finAppend (n k : ℕ) {q : ℕ∞} :
    ContDiff ℝ q (fun p : (Fin n → ℝ) × (Fin k → ℝ) => Fin.append p.1 p.2) := by
  apply contDiff_pi.mpr
  intro i
  refine Fin.addCases ?_ ?_ i <;> intro j
  · simpa only [Fin.append_left, Function.comp_def] using
      (contDiff_apply ℝ ℝ j).comp (contDiff_fst (E := Fin n → ℝ) (F := Fin k → ℝ))
  · simpa only [Fin.append_right, Function.comp_def] using
      (contDiff_apply ℝ ℝ j).comp (contDiff_snd (E := Fin n → ℝ) (F := Fin k → ℝ))

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_ConvergingPolynomialImage
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A noncritical limit supplies the minor bound for all late parameters -/

noncomputable section

namespace PolycyclicRecognition

open Set Metric MeasureTheory Filter
open scoped Topology

theorem continuous_det_clm {P : Type} [TopologicalSpace P] {n : ℕ}
    {d : P → (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)} (hd : Continuous d) :
    Continuous (fun p => (d p).det) := by
  have hm : Continuous (fun p => LinearMap.toMatrix' (d p).toLinearMap) := by
    apply continuous_matrix
    intro i j
    simp only [LinearMap.toMatrix'_apply]
    exact (continuous_apply i).comp (hd.clm_apply continuous_const)
  simpa only [LinearMap.det_toMatrix'] using hm.matrix_det

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_DifferenceAmplitudeWord
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Two independent interval samples per generator switch -/

noncomputable section

namespace PolycyclicRecognition

open Module

theorem hasPolynomialCoordinates_differenceAmplitudeWord {I : Type} {n m c : ℕ}
    (a : DynkinCoefficients c 2) (letters : Fin m → I) :
    HasPolynomialCoordinates (differenceAmplitudeWordEndpoint (n := n) a letters) := by
  apply hasPolynomialCoordinates_listProduct a Prod.fst
  intro j
  apply HasPolynomialCoordinates.smul
  · exact hasPolynomialCoordinates_const (fun p :
      ((Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) × (I → Fin n → ℝ) =>
      p.2 (letters j))
  · have h₁ := hasPolynomialFormula_coordinate (P :=
      ((Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) × (I → Fin n → ℝ)) (Fin.castAdd m j)
    have h₂ := (hasPolynomialFormula_const (P :=
      ((Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) × (I → Fin n → ℝ))
      (m := m + m) (fun _ => (-1 : ℝ))).mul (hasPolynomialFormula_coordinate (Fin.natAdd m j))
    simpa only [differenceParameters_apply, neg_one_mul, sub_eq_add_neg] using h₁.add h₂

theorem contDiff_differenceAmplitudeWord {I : Type} [Fintype I] {n m c : ℕ}
    (a : DynkinCoefficients c 2) (letters : Fin m → I) {q : ℕ∞} :
    ContDiff ℝ q (fun z :
      (((Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) × (I → Fin n → ℝ)) ×
        (Fin (m + m) → ℝ) => differenceAmplitudeWordEndpoint a letters z.1 z.2) := by
  change ContDiff ℝ q (fun z :
      (((Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) × (I → Fin n → ℝ)) ×
        (Fin (m + m) → ℝ) => polynomialListProduct (dynkinProduct a z.1.1)
          (List.ofFn fun j =>
            (z.2 (Fin.castAdd m j) - z.2 (Fin.natAdd m j)) • z.1.2 (letters j)))
  apply contDiff_polynomialListProduct_ofFn
  · exact contDiff_fst.fst
  · intro j
    exact (((contDiff_apply ℝ ℝ (Fin.castAdd m j)).comp contDiff_snd).sub
      ((contDiff_apply ℝ ℝ (Fin.natAdd m j)).comp contDiff_snd)).smul
      ((contDiff_apply ℝ (Fin n → ℝ) (letters j)).comp contDiff_fst.snd)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_IndependentSwitchParameters
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The measurable event of successful independent switch parameters -/

noncomputable section

namespace PolycyclicRecognition

open MeasureTheory Set
open scoped ENNReal

universe u

variable {G : Type} [Group G] [MeasurableSpace G]

theorem measurableSet_switchSuccessful [MeasurableMul₂ G] [MeasurableInv G]
    (S : ℕ → Set G) (hS : ∀ j, MeasurableSet (S j)) (n k : ℕ) :
    MeasurableSet {p : G × SwitchParameters G k | SwitchSuccessful S n k p.1 p.2} := by
  induction k generalizing n with
  | zero => exact MeasurableSet.univ
  | succ k ih =>
    have hm : Measurable (fun p : G × SwitchParameters G (k + 1) =>
        p.1 * p.2.1 * p.2.2.1⁻¹) :=
      (measurable_fst.mul measurable_snd.fst).mul measurable_snd.snd.fst.inv
    exact (hS (n + 1) |>.preimage hm).inter
      ((ih (n + 1)).preimage (hm.prodMk measurable_snd.snd.snd))

theorem measurableSet_switchSuccessful_fixed [MeasurableMul₂ G] [MeasurableInv G]
    (S : ℕ → Set G) (hS : ∀ j, MeasurableSet (S j)) (n k : ℕ) (x : G) :
    MeasurableSet {p : SwitchParameters G k | SwitchSuccessful S n k x p} :=
  (measurableSet_switchSuccessful S hS n k).preimage (measurable_const.prodMk measurable_id)

/-- The recursive survival integral equals the probability of the actual
measurable successful-parameter event under the independent product law. -/
theorem switchParameterLaw_success [MeasurableMul₂ G] [MeasurableInv G]
    (σ : ℕ → Measure G) [∀ j, IsProbabilityMeasure (σ j)]
    (S : ℕ → Set G) (hS : ∀ j, MeasurableSet (S j)) (n k : ℕ) (x : G) :
    switchParameterLaw σ n k {p | SwitchSuccessful S n k x p} =
      survivingSwitchProbability σ S n k x := by
  induction k generalizing n x with
  | zero =>
    change (Measure.dirac PUnit.unit) univ = 1
    exact Measure.dirac_apply_of_mem (Set.mem_univ _)
  | succ k ih =>
    rw [← lintegral_indicator_one (measurableSet_switchSuccessful_fixed S hS n (k + 1) x)]
    let f : SwitchParameters G (k + 1) → ℝ≥0∞ :=
      {p | SwitchSuccessful S n (k + 1) x p}.indicator (fun _ => 1)
    have hf : Measurable f := measurable_const.indicator
      (measurableSet_switchSuccessful_fixed S hS n (k + 1) x)
    change (∫⁻ p, f p ∂(σ n).prod ((σ n).prod (switchParameterLaw σ (n + 1) k))) = _
    rw [lintegral_prod f hf.aemeasurable]
    change (∫⁻ s₁, ∫⁻ p, f (s₁, p) ∂(σ n).prod (switchParameterLaw σ (n + 1) k) ∂σ n) = _
    apply lintegral_congr
    intro s₁
    have hf₁ : Measurable (fun p : G × SwitchParameters G k => f (s₁, p)) :=
      hf.comp (measurable_const.prodMk measurable_id)
    rw [lintegral_prod (fun p : G × SwitchParameters G k => f (s₁, p)) hf₁.aemeasurable]
    apply lintegral_congr
    intro s₂
    by_cases hy : x * s₁ * s₂⁻¹ ∈ S (n + 1)
    · have he : (fun p => f (s₁, s₂, p)) =
          {p | SwitchSuccessful S (n + 1) k (x * s₁ * s₂⁻¹) p}.indicator (fun _ => 1) := by
        funext p
        change {q | SwitchSuccessful S n (k + 1) x q}.indicator (fun _ => (1 : ℝ≥0∞))
          (s₁, s₂, p) =
            {q | SwitchSuccessful S (n + 1) k (x * s₁ * s₂⁻¹) q}.indicator (fun _ => 1) p
        by_cases hp : SwitchSuccessful S (n + 1) k (x * s₁ * s₂⁻¹) p
        · rw [indicator_of_mem (s := {q : SwitchParameters G (k + 1) |
              SwitchSuccessful S n (k + 1) x q}) (show SwitchSuccessful S n (k + 1) x (s₁, s₂, p) from
            ⟨hy, hp⟩), indicator_of_mem (s := {q : SwitchParameters G k |
              SwitchSuccessful S (n + 1) k (x * s₁ * s₂⁻¹) q}) hp]
        · have hn : ¬ SwitchSuccessful S n (k + 1) x (s₁, s₂, p) := fun h => hp h.2
          rw [indicator_of_notMem (s := {q : SwitchParameters G (k + 1) |
              SwitchSuccessful S n (k + 1) x q}) hn,
            indicator_of_notMem (s := {q : SwitchParameters G k |
              SwitchSuccessful S (n + 1) k (x * s₁ * s₂⁻¹) q}) hp]
      rw [he]
      change (∫⁻ p, {p | SwitchSuccessful S (n + 1) k (x * s₁ * s₂⁻¹) p}.indicator 1 p
        ∂switchParameterLaw σ (n + 1) k) = _
      rw [lintegral_indicator_one
        (measurableSet_switchSuccessful_fixed S hS (n + 1) k (x * s₁ * s₂⁻¹)), ih]
      exact (indicator_of_mem hy _).symm
    · have he : (fun p => f (s₁, s₂, p)) = fun _ => 0 := by
        funext p
        simp only [f, SwitchSuccessful, hy, false_and, mem_ofPred_eq,
          not_false_eq_true, indicator_of_notMem]
      rw [he, lintegral_zero]
      exact (indicator_of_notMem hy _).symm

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_FiniteSwitchEvents
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Successful switch events only use the prescribed finite list of sheets -/

noncomputable section

namespace PolycyclicRecognition

open MeasureTheory Set

variable {G : Type} [Group G] [MeasurableSpace G]

omit [MeasurableSpace G] in
theorem switchSuccessful_mono (S R : ℕ → Set G) (n k : ℕ)
    (hsub : ∀ j, n < j → j ≤ n + k → S j ⊆ R j)
    (x : G) (p : SwitchParameters G k)
    (hp : SwitchSuccessful S n k x p) : SwitchSuccessful R n k x p := by
  induction k generalizing n x with
  | zero => trivial
  | succ k ih =>
    exact ⟨hsub (n + 1) (by omega) (by omega) hp.1,
      ih (n + 1) (fun j hj hj' => hsub j (by omega) (by omega)) _ p.2.2 hp.2⟩

omit [MeasurableSpace G] in
theorem switchSuccessful_congr (S R : ℕ → Set G) (n k : ℕ)
    (heq : ∀ j, n < j → j ≤ n + k → S j = R j)
    (x : G) (p : SwitchParameters G k) :
    SwitchSuccessful S n k x p ↔ SwitchSuccessful R n k x p := by
  induction k generalizing n x with
  | zero => rfl
  | succ k ih =>
    change (_ ∈ S (n + 1) ∧ _) ↔ (_ ∈ R (n + 1) ∧ _)
    rw [heq (n + 1) (by omega) (by omega)]
    exact and_congr_right (fun _ => ih (n + 1)
      (fun j hj hj' => heq j (by omega) (by omega)) _ p.2.2)

theorem survivingSwitchProbability_congr (σ : ℕ → Measure G)
    (S R : ℕ → Set G) (n k : ℕ)
    (heq : ∀ j, n < j → j ≤ n + k → S j = R j) (x : G) :
    survivingSwitchProbability σ S n k x = survivingSwitchProbability σ R n k x := by
  induction k generalizing n x with
  | zero => rfl
  | succ k ih =>
    simp only [survivingSwitchProbability]
    apply lintegral_congr
    intro s₁
    apply lintegral_congr
    intro s₂
    rw [heq (n + 1) (by omega) (by omega)]
    exact congrFun (indicator_congr (fun y _ =>
      ih (n + 1) (fun j hj hj' => heq j (by omega) (by omega)) y)) _

/-- No measurability conditions on unused sheets are needed. -/
theorem switchParameterLaw_success_finite [MeasurableMul₂ G] [MeasurableInv G]
    (σ : ℕ → Measure G) [∀ j, IsProbabilityMeasure (σ j)]
    (S : ℕ → Set G) (n k : ℕ)
    (hS : ∀ j, n < j → j ≤ n + k → MeasurableSet (S j)) (x : G) :
    MeasurableSet {p : SwitchParameters G k | SwitchSuccessful S n k x p} ∧
      switchParameterLaw σ n k {p | SwitchSuccessful S n k x p} =
        survivingSwitchProbability σ S n k x := by
  let R := fun j => if n < j ∧ j ≤ n + k then S j else ∅
  have hR (j : ℕ) : MeasurableSet (R j) := by
    by_cases hj : n < j ∧ j ≤ n + k
    · simpa [R, hj] using hS j hj.1 hj.2
    · simp [R, hj]
  have heq (j : ℕ) (hj : n < j) (hj' : j ≤ n + k) : S j = R j := by
    simp [R, hj, hj']
  have hsets : {p : SwitchParameters G k | SwitchSuccessful S n k x p} =
      {p | SwitchSuccessful R n k x p} := by
    ext p
    exact switchSuccessful_congr S R n k heq x p
  constructor
  · exact hsets.symm ▸ measurableSet_switchSuccessful_fixed R hR n k x
  · calc
      _ = switchParameterLaw σ n k {p | SwitchSuccessful R n k x p} :=
        congrArg (switchParameterLaw σ n k) hsets
      _ = survivingSwitchProbability σ R n k x := switchParameterLaw_success σ R hR n k x
      _ = _ := (survivingSwitchProbability_congr σ S R n k heq x).symm

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_SequenceSubexponential
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instNonemptyBases _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_nonempty _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Subexponential estimates along the actual sequence of profile scales -/

noncomputable section

namespace PolycyclicRecognition

open Filter
open scoped Topology

theorem HasSubexponentialLowerBound.along_sequence {f : ℝ → ℝ}
    (hf : HasSubexponentialLowerBound f) {scale : ℕ → ℝ}
    (hs : Tendsto scale atTop atTop) : HasSubexponentialLowerBoundSeq scale (f ∘ scale) :=
  fun ε hε => hs.eventually (hf ε hε)

theorem HasSubexponentialLowerBoundSeq.eventually_pos {scale f : ℕ → ℝ}
    (hf : HasSubexponentialLowerBoundSeq scale f) : ∀ᶠ n in atTop, 0 < f n :=
  (hf 1 zero_lt_one).mono (fun _ h => (Real.exp_pos _).trans_le h)

theorem HasSubexponentialLowerBoundSeq.mono {scale f g : ℕ → ℝ}
    (hf : HasSubexponentialLowerBoundSeq scale f) (hfg : f ≤ᶠ[atTop] g) :
    HasSubexponentialLowerBoundSeq scale g := by
  intro ε hε
  filter_upwards [hf ε hε, hfg] with n hn hfg
  exact hn.trans hfg

theorem HasSubexponentialLowerBoundSeq.mul {scale f g : ℕ → ℝ}
    (hf : HasSubexponentialLowerBoundSeq scale f) (hg : HasSubexponentialLowerBoundSeq scale g) :
    HasSubexponentialLowerBoundSeq scale (fun n => f n * g n) := by
  intro ε hε
  filter_upwards [hf (ε / 2) (half_pos hε), hg (ε / 2) (half_pos hε)] with n hn hm
  calc
    Real.exp (-ε * scale n) = Real.exp (-(ε / 2) * scale n) *
        Real.exp (-(ε / 2) * scale n) := by rw [← Real.exp_add]; congr 1; ring
    _ ≤ f n * g n := mul_le_mul hn hm (Real.exp_pos _).le ((Real.exp_pos _).trans_le hn).le

theorem HasSubexponentialLowerBoundSeq.div {scale f g : ℕ → ℝ}
    (hf : HasSubexponentialLowerBoundSeq scale f) (hg : HasSubexponentialUpperBoundSeq scale g)
    (hg0 : ∀ᶠ n in atTop, 0 < g n) :
    HasSubexponentialLowerBoundSeq scale (fun n => f n / g n) := by
  intro ε hε
  filter_upwards [hf (ε / 2) (half_pos hε), hg (ε / 2) (half_pos hε), hg0] with n hn hm h0
  calc
    Real.exp (-ε * scale n) = Real.exp (-(ε / 2) * scale n) /
        Real.exp (ε / 2 * scale n) := by rw [← Real.exp_sub]; congr 1; ring
    _ ≤ f n / g n := div_le_div₀ ((Real.exp_pos _).trans_le hn).le hn h0 hm

theorem exponent_le_of_sequence_subexponential_bounds
    {scale f g : ℕ → ℝ} (hs : Tendsto scale atTop atTop) {p q : ℝ}
    (hf : HasSubexponentialLowerBoundSeq scale f) (hg : HasSubexponentialUpperBoundSeq scale g)
    (hbound : ∀ᶠ n in atTop, f n * Real.exp (scale n * p) ≤ g n * Real.exp (scale n * q)) :
    p ≤ q := by
  by_contra h
  have hpq : q < p := lt_of_not_ge h
  let ε := (p - q) / 4
  have hε : 0 < ε := by dsimp [ε] <;> linarith
  obtain ⟨n, hn, hm, hb, hnpos⟩ := ((hf ε hε).and ((hg ε hε).and
    (hbound.and (hs.eventually (eventually_gt_atTop (0 : ℝ)))))).exists
  have he : Real.exp ((p - ε) * scale n) ≤ Real.exp ((q + ε) * scale n) := calc
    _ = Real.exp (-ε * scale n) * Real.exp (scale n * p) := by
      rw [← Real.exp_add]; congr 1; ring
    _ ≤ f n * Real.exp (scale n * p) := mul_le_mul_of_nonneg_right hn (Real.exp_pos _).le
    _ ≤ g n * Real.exp (scale n * q) := hb
    _ ≤ Real.exp (ε * scale n) * Real.exp (scale n * q) :=
      mul_le_mul_of_nonneg_right hm (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have hh := Real.exp_le_exp.mp he
  have hgap : 0 < p - q - 2 * ε := by dsimp [ε] <;> linarith
  have hprod := mul_pos hgap hnpos
  nlinarith

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

theorem sequence_subexponential_lower_const (hs : Tendsto scale atTop atTop)
    {c : ℝ} (hc : 0 < c) : HasSubexponentialLowerBoundSeq scale (fun _ => c) := by
  simpa only [Function.comp_def] using (subexponential_lower_const hc).along_sequence hs

theorem HasSubexponentialLowerBoundSeq.min {f g : ℕ → ℝ}
    (hf : HasSubexponentialLowerBoundSeq scale f) (hg : HasSubexponentialLowerBoundSeq scale g) :
    HasSubexponentialLowerBoundSeq scale (fun n => min (f n) (g n)) := by
  intro ε hε
  filter_upwards [hf ε hε, hg ε hε] with n hn hm
  exact le_min hn hm

theorem HasSubexponentialLowerBoundSeq.inv {f : ℕ → ℝ}
    (hf : HasSubexponentialLowerBoundSeq scale f) :
    HasSubexponentialUpperBoundSeq scale (fun n => (f n)⁻¹) := by
  intro ε hε
  filter_upwards [hf ε hε] with n hn
  calc
    (f n)⁻¹ ≤ (Real.exp (-ε * scale n))⁻¹ := by
      simpa only [one_div] using one_div_le_one_div_of_le (Real.exp_pos _) hn
    _ = Real.exp (ε * scale n) := by rw [← Real.exp_neg]; congr 1; ring

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
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_SequenceBackwardAsymptotics
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Subexponential mass and success probability in backward recurrence -/

namespace PolycyclicRecognition

open Filter
open scoped Topology NNReal ENNReal

/-- A fixed number of backward recurrence steps retains subexponential
normalized mass. Both the initial mass and the enlargements may vary with
the scale. -/
theorem subexponential_backward_masses_sequence
    (scale : ℕ → ℝ) (hscale : Tendsto scale atTop atTop) (h : ℕ) (a D : ℕ → ℕ → ℝ)
    (hlast : HasSubexponentialLowerBoundSeq scale (a h))
    (hD : ∀ j, j < h → HasSubexponentialUpperBoundSeq scale (D j))
    (hDpos : ∀ j, j < h → ∀ᶠ r in atTop, 0 < D j r)
    (hstep : ∀ j, j < h → ∀ᶠ r in atTop,
      a (j + 1) r ^ 2 / (2 * D j r) ≤ a j r) :
    ∀ j, j ≤ h → HasSubexponentialLowerBoundSeq scale (a j) := by
  induction h with
  | zero =>
    intro j hj
    have : j = 0 := by omega
    simpa only [this] using hlast
  | succ h ih =>
    have hah : HasSubexponentialLowerBoundSeq scale (a h) := by
      have hnum := hlast.mul hlast
      have hden := (sequence_subexponential_upper_const hscale 2).mul (hD h (by omega))
        (Eventually.of_forall (fun _ => by norm_num))
      have hp : ∀ᶠ r in atTop, 0 < 2 * D h r :=
        (hDpos h (by omega)).mono (fun _ hr => mul_pos (by norm_num) hr)
      have hl := hnum.div hden hp
      apply hl.mono
      filter_upwards [hstep h (by omega)] with r hr
      simpa only [pow_two] using hr
    intro j hj
    by_cases he : j = h + 1
    · simpa only [he] using hlast
    · exact ih hah (fun k hk => hD k (by omega))
        (fun k hk => hDpos k (by omega)) (fun k hk => hstep k (by omega)) j (by omega)

/-- A fixed ordered product of transition probabilities retains a
subexponential lower bound. -/
theorem subexponential_switch_product_sequence
    (scale : ℕ → ℝ) (hscale : Tendsto scale atTop atTop) (τ : ℕ → ℕ → ℝ≥0) (n k : ℕ)
    (hτ : ∀ j, n ≤ j → j < n + k →
      HasSubexponentialLowerBoundSeq scale (fun r => (τ j r : ℝ))) :
    HasSubexponentialLowerBoundSeq scale (fun r => (switchThresholdProduct (fun j => τ j r) n k).toReal) := by
  induction k generalizing n with
  | zero => simpa only [switchThresholdProduct, ENNReal.toReal_one] using
      sequence_subexponential_lower_const hscale (by norm_num : (0 : ℝ) < 1)
  | succ k ih =>
    have htail := ih (n + 1) (fun j hj hj' => hτ j (by omega) (by omega))
    have hhead := hτ n le_rfl (by omega)
    simpa only [switchThresholdProduct, ENNReal.toReal_mul, ENNReal.coe_toReal] using
      hhead.mul htail

/-- The normalized masses supplied by recurrence give the required lower
bound on each threshold, with the same enlargement factors. -/
theorem subexponential_backward_thresholds_sequence
    (scale : ℕ → ℝ) (hscale : Tendsto scale atTop atTop) (h : ℕ) (a D : ℕ → ℕ → ℝ)
    (hlast : HasSubexponentialLowerBoundSeq scale (a h))
    (hD : ∀ j, j < h → HasSubexponentialUpperBoundSeq scale (D j))
    (hDpos : ∀ j, j < h → ∀ᶠ r in atTop, 0 < D j r)
    (hstep : ∀ j, j < h → ∀ᶠ r in atTop,
      a (j + 1) r ^ 2 / (2 * D j r) ≤ a j r) :
    ∀ j, j < h → HasSubexponentialLowerBoundSeq scale (fun r => a (j + 1) r / (2 * D j r)) := by
  intro j hj
  apply (subexponential_backward_masses_sequence scale hscale h a D hlast hD hDpos hstep (j + 1) (by omega)).div
  · exact (sequence_subexponential_upper_const hscale 2).mul (hD j hj)
      (Eventually.of_forall (fun _ => by norm_num))
  · exact (hDpos j hj).mono (fun _ hr => mul_pos (by norm_num) hr)

end PolycyclicRecognition

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_SequenceBackwardRecurrence
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Successful parameter volume along the profile-scale sequence -/

noncomputable section

namespace PolycyclicRecognition

open Set Metric MeasureTheory Filter
open scoped Topology ENNReal NNReal

theorem exists_subexponential_backward_recurrence_sequence
    {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]
    (scale : ℕ → ℝ) (hscale : Tendsto scale atTop atTop)
    (μ : Measure G) [SFinite μ] [μ.IsMulRightInvariant]
    (σ : ℕ → ℕ → Measure G) [∀ r j, IsProbabilityMeasure (σ r j)]
    (Q A : ℕ → Set G) (K R : ℕ → ℕ → Set G) (D : ℕ → ℕ → ℝ)
    (hQfin : ∀ r, μ (Q r) ≠ ∞) (hQpos : ∀ r, 0 < (μ (Q r)).toReal)
    (hK : ∀ r j, ∀ᵐ s ∂σ r j, s ∈ K r j)
    (hRfin : ∀ r j, μ (R r j) ≠ ∞) (hRpos : ∀ r j, 0 < (μ (R r j)).toReal)
    (hQR : ∀ r j, ∀ a ∈ Q r, ∀ s ∈ K r j, a * s ∈ R r j)
    (hD : ∀ r j, 0 < D r j)
    (hvol : ∀ r j, (μ (R r j)).toReal ≤ D r j * (μ (Q r)).toReal)
    (h : ℕ) (hA : ∀ r, MeasurableSet (A r)) (hAQ : ∀ r, A r ⊆ Q r)
    (hApos : ∀ r, 0 < (μ (A r)).toReal)
    (hAlower : HasSubexponentialLowerBoundSeq scale (fun r => (μ (A r)).toReal / (μ (Q r)).toReal))
    (hDupper : ∀ j, j < h → HasSubexponentialUpperBoundSeq scale (fun r => D r j)) :
    ∃ S : ℕ → ℕ → Set G,
      (∀ r, S r h = A r) ∧
      (∀ r j, j ≤ h → MeasurableSet (S r j) ∧ S r j ⊆ A r ∧ 0 < (μ (S r j)).toReal) ∧
      HasSubexponentialLowerBoundSeq scale (fun r => (μ (S r 0)).toReal / (μ (Q r)).toReal) ∧
      let τ := fun r j => Real.toNNReal ((μ (S r (j + 1))).toReal /
        (2 * D r j * (μ (Q r)).toReal))
      HasSubexponentialLowerBoundSeq scale (fun r => (switchThresholdProduct (τ r) 0 h).toReal) ∧
        ∀ r x, x ∈ S r 0 →
          switchThresholdProduct (τ r) 0 h ≤ survivingSwitchProbability (σ r) (S r) 0 h x := by
  choose S hS using fun r => exists_backward_recurrence_probability μ (σ r) (Q r)
    (hQfin r) (hQpos r) (K r) (R r) (hK r) (hRfin r) (hRpos r) (hQR r)
    (D r) (hD r) (hvol r) h (A r) (hA r) (hAQ r) (hApos r)
  let a := fun j r => (μ (S r j)).toReal / (μ (Q r)).toReal
  have hlast : HasSubexponentialLowerBoundSeq scale (a h) := by
    simpa only [a, (hS _).1] using hAlower
  have hsteps (j : ℕ) (hj : j < h) : ∀ᶠ r in atTop,
      a (j + 1) r ^ 2 / (2 * D r j) ≤ a j r := by
    exact Eventually.of_forall (fun r => normalized_backward_mass_bound (hQpos r) (hD r j)
      ((hS r).2.2.1 j hj).2)
  have hpos (j : ℕ) (_ : j < h) : ∀ᶠ r in atTop, 0 < D r j :=
    Eventually.of_forall (fun r => hD r j)
  have hmasses := subexponential_backward_masses_sequence scale hscale h a (fun j r => D r j)
    hlast hDupper hpos hsteps
  have hthresholds := subexponential_backward_thresholds_sequence scale hscale h a (fun j r => D r j)
    hlast hDupper hpos hsteps
  let τ := fun r j => Real.toNNReal ((μ (S r (j + 1))).toReal /
    (2 * D r j * (μ (Q r)).toReal))
  have hτ (j : ℕ) (hj : j < h) :
      HasSubexponentialLowerBoundSeq scale (fun r => (τ r j : ℝ)) := by
    apply (hthresholds j hj).mono
    apply Eventually.of_forall
    intro r
    have heq : (τ r j : ℝ) = a (j + 1) r / (2 * D r j) := by
      have hp : 0 ≤ (μ (S r (j + 1))).toReal / (2 * D r j * (μ (Q r)).toReal) :=
        div_nonneg ENNReal.toReal_nonneg
          (mul_pos (mul_pos (by norm_num) (hD r j)) (hQpos r)).le
      change (Real.toNNReal ((μ (S r (j + 1))).toReal /
        (2 * D r j * (μ (Q r)).toReal)) : ℝ) =
        ((μ (S r (j + 1))).toReal / (μ (Q r)).toReal) / (2 * D r j)
      rw [Real.coe_toNNReal _ hp]
      ring
    exact heq.ge
  refine ⟨S, fun r => (hS r).1, fun r => (hS r).2.1, hmasses 0 (Nat.zero_le _), ?_⟩
  refine ⟨subexponential_switch_product_sequence scale hscale (fun j r => τ r j) 0 h (fun j _ hj => hτ j (by omega)), ?_⟩
  exact fun r x hx => (hS r).2.2.2.2 x hx

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_SequenceParameterDensity
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Successful parameter volume along the profile-scale sequence -/

noncomputable section

namespace PolycyclicRecognition

open Set Metric MeasureTheory Filter
open scoped Topology ENNReal NNReal

theorem subexponential_volume_of_probability_sequence
    {A : Type} [MeasurableSpace A]
    (scale : ℕ → ℝ)
    (μ ν : ℕ → Measure A) (E : ℕ → Set A) (D : ℕ → ℝ≥0)
    (hfinite : ∀ r, μ r (E r) ≠ ∞)
    (hdom : ∀ r, ν r ≤ (D r : ℝ≥0∞) • μ r)
    (hprob : HasSubexponentialLowerBoundSeq scale (fun r => (ν r (E r)).toReal))
    (hD : HasSubexponentialUpperBoundSeq scale (fun r => (D r : ℝ)))
    (hpos : ∀ᶠ r in atTop, 0 < D r) :
    HasSubexponentialLowerBoundSeq scale (fun r => (μ r (E r)).toReal) := by
  have hdiv := hprob.div hD hpos
  apply hdiv.mono
  filter_upwards [hpos] with r hr
  apply (div_le_iff₀ (show 0 < (D r : ℝ) from hr)).mpr
  have hbound := ENNReal.toReal_mono
    (ENNReal.mul_ne_top ENNReal.coe_ne_top (hfinite r)) (hdom r (E r))
  simpa only [Measure.smul_apply, smul_eq_mul, ENNReal.toReal_mul,
    ENNReal.coe_toReal, mul_comm] using hbound

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_SequencePolynomialValues
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Subexponential mass with a subexponential polynomial minor bound -/

noncomputable section

namespace PolycyclicRecognition

open Set Metric MeasureTheory Filter
open scoped Topology

theorem exists_subexponential_large_polynomial_values_sequence
    (scale : ℕ → ℝ) (hscale : Tendsto scale atTop atTop)
    (rem : RemezPolynomialInput) (n D : ℕ) (hn : 1 ≤ n) (hD : 1 ≤ D)
    (p : ℕ → MvPolynomial (Fin n) ℝ) (hp : ∀ r, (p r).totalDegree ≤ D)
    (R c : ℕ → ℝ) (hR : ∀ r, 1 ≤ R r) (hc : ∀ r, 0 < c r)
    (hRupper : HasSubexponentialUpperBoundSeq scale R)
    (hclower : HasSubexponentialLowerBoundSeq scale c)
    (x₀ : ℕ → Fin n → ℝ) (hx₀ : ∀ r, x₀ r ∈ closedBall 0 (R r))
    (hvalue : ∀ r, c r ≤ |MvPolynomial.eval (x₀ r) (p r)|)
    (E : ℕ → Set (Fin n → ℝ)) (hE : ∀ r, MeasurableSet (E r))
    (hER : ∀ r, E r ⊆ closedBall 0 (R r))
    (hm : ∀ r, 0 < (volume (E r)).toReal)
    (hmlower : HasSubexponentialLowerBoundSeq scale (fun r => (volume (E r)).toReal)) :
    ∃ (η : ℕ → ℝ) (K : ℕ → Set (Fin n → ℝ)),
      (∀ r, 0 < η r) ∧ HasSubexponentialLowerBoundSeq scale η ∧
      (∀ r, K r ⊆ E r) ∧ (∀ r, IsCompact (K r)) ∧
      (∀ r, 0 < (volume (K r)).toReal) ∧
      HasSubexponentialLowerBoundSeq scale (fun r => (volume (K r)).toReal) ∧
      ∀ r x, x ∈ K r → η r ≤ |MvPolynomial.eval x (p r)| := by
  classical
  obtain ⟨A, hA, hselect⟩ := exists_compact_large_polynomial_values rem n D hn hD
  let m := fun r => (volume (E r)).toReal
  let a := fun r => 2 * A * (1 + R r) ^ n / m r
  let η := fun r => (c r / 2) / a r ^ (n * D)
  have ha (r : ℕ) : 0 < a r := by
    have h := hR r
    have h' := hm r
    dsimp [a, m]
    positivity
  have hη (r : ℕ) : 0 < η r := div_pos (div_pos (hc r) (by norm_num)) (pow_pos (ha r) (n * D))
  have hs (r : ℕ) := hselect (p r) (hp r) (R r) (c r) (hR r) (hc r)
    (x₀ r) (hx₀ r) (hvalue r) (E r) (hE r) (hER r) (hm r)
  choose K hKE hK hmass hgood using hs
  have hR0 : ∀ᶠ r in atTop, 0 ≤ 1 + R r := Eventually.of_forall (fun r => by have := hR r; linarith)
  have haUpper : HasSubexponentialUpperBoundSeq scale a := by
    have hpowers := ((sequence_subexponential_upper_const hscale 1).add hRupper hscale).pow hscale hR0 n
    have hnum := (sequence_subexponential_upper_const hscale (2 * A)).mul hpowers
      (Eventually.of_forall (fun _ => by positivity))
    have hh := hnum.mul hmlower.inv (Eventually.of_forall (fun r => by
      have := hR r
      positivity))
    simpa only [a, m, div_eq_mul_inv] using hh
  have hηlower : HasSubexponentialLowerBoundSeq scale η :=
    (hclower.div (sequence_subexponential_upper_const hscale 2) (Eventually.of_forall (by intro r; norm_num))).div
      (haUpper.pow hscale (Eventually.of_forall (fun r => (ha r).le)) (n * D))
      (Eventually.of_forall (fun r => pow_pos (ha r) (n * D)))
  have hKlower : HasSubexponentialLowerBoundSeq scale (fun r => (volume (K r)).toReal) := by
    apply (hmlower.div (sequence_subexponential_upper_const hscale 4) (Eventually.of_forall (by intro r; norm_num))).mono
    exact Eventually.of_forall (fun r => (hmass r).le)
  exact ⟨η, K, hη, hηlower, hKE, hK,
    fun r => (div_pos (hm r) (by norm_num : (0 : ℝ) < 4)).trans (hmass r),
    hKlower, hgood⟩

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_SequencePositiveParameters
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_countable _root_.OAI.PolycyclicRecognition.finitelyGeneratedSubgroupIndex_countable _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Successful parameter volume along the profile-scale sequence -/

noncomputable section

namespace PolycyclicRecognition

open Set Metric MeasureTheory Filter
open scoped Topology ENNReal NNReal

theorem exists_positive_parameter_sets_sequence {m : ℕ} {R : ℝ}
    (scale : ℕ → ℝ) (hR : 0 < R)
    (E : ℕ → Set (Fin m → ℝ)) (hE : ∀ r, MeasurableSet (E r))
    (hER : ∀ r, E r ⊆ closedBall 0 R)
    (hmlower : HasSubexponentialLowerBoundSeq scale (fun r => (volume (E r)).toReal)) :
    ∃ F : ℕ → Set (Fin m → ℝ),
      (∀ r, MeasurableSet (F r)) ∧ (∀ r, F r ⊆ closedBall 0 R) ∧
      (∀ r, 0 < (volume (F r)).toReal) ∧
      HasSubexponentialLowerBoundSeq scale (fun r => (volume (F r)).toReal) ∧
      ∀ᶠ r in atTop, F r = E r := by
  classical
  let F := fun r => if 0 < (volume (E r)).toReal then E r else closedBall 0 R
  have heq : ∀ᶠ r in atTop, F r = E r :=
    hmlower.eventually_pos.mono (fun _ h => ite_eq_left h)
  have hball : 0 < (volume (closedBall (0 : Fin m → ℝ) R)).toReal := by
    rw [Real.volume_pi_closedBall _ hR.le, ENNReal.toReal_ofReal (by positivity)]
    positivity
  refine ⟨F, ?_, ?_, ?_, ?_, heq⟩
  · intro r
    dsimp [F]
    split_ifs
    · exact hE r
    · exact measurableSet_closedBall
  · intro r
    dsimp [F]
    split_ifs
    · exact hER r
    · exact Subset.rfl
  · intro r
    dsimp [F]
    split_ifs with h
    · exact h
    · exact hball
  · apply hmlower.mono
    exact heq.mono (fun _ h => le_of_eq (congrArg (fun s => (volume s).toReal) h.symm))

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_SwitchParameterPullback
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Pulling the successful event back to the original independent samples -/

noncomputable section

namespace PolycyclicRecognition

open MeasureTheory Set

theorem measurePreserving_mapSwitchParameters {A B : Type}
    [MeasurableSpace A] [MeasurableSpace B]
    (f : ℕ → A → B) (τ : ℕ → Measure A) (σ : ℕ → Measure B)
    [∀ j, IsProbabilityMeasure (τ j)] [∀ j, IsProbabilityMeasure (σ j)]
    (hf : ∀ j, MeasurePreserving (f j) (τ j) (σ j)) (n k : ℕ) :
    MeasurePreserving (mapSwitchParameters f n k)
      (switchParameterLaw τ n k) (switchParameterLaw σ n k) := by
  induction k generalizing n with
  | zero =>
    refine ⟨measurable_const, ?_⟩
    simp [mapSwitchParameters, switchParameterLaw]
  | succ k ih => exact (hf n).prod ((hf n).prod (ih (n + 1)))

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_VectorSwitchParameters
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite vectors of independent pairs and the recursive switch law -/

noncomputable section

namespace PolycyclicRecognition

open MeasureTheory

theorem measurePreserving_vectorSwitchParameters {A : Type} [MeasurableSpace A]
    (τ : Measure A) [IsProbabilityMeasure τ] (n k : ℕ) :
    MeasurePreserving (vectorSwitchParameters (A := A) k)
      (Measure.pi (fun _ : Fin k => τ.prod τ)) (switchParameterLaw (fun _ => τ) n k) := by
  induction k generalizing n with
  | zero =>
    refine ⟨measurable_const, ?_⟩
    simp [vectorSwitchParameters, switchParameterLaw]
  | succ k ih =>
    have hhead := measurePreserving_piFinSuccAbove (fun _ : Fin (k + 1) => τ.prod τ) 0
    have htail := (MeasurePreserving.id (τ.prod τ)).prod (ih (n + 1))
    have hassoc := measurePreserving_prodAssoc τ τ (switchParameterLaw (fun _ => τ) (n + 1) k)
    change MeasurePreserving _ _ (τ.prod (τ.prod (switchParameterLaw (fun _ => τ) (n + 1) k)))
    convert hassoc.comp (htail.comp hhead) using 1
    all_goals try with_reducible_and_instances rfl
    funext p
    simp [vectorSwitchParameters, Function.comp_def, MeasurableEquiv.piFinSuccAbove_apply]
    rfl

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_FlatSwitchSamples
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_countable _root_.OAI.PolycyclicRecognition.finitelyGeneratedSubgroupIndex_countable _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The recursive independent sampling law on the flat parameter cube -/

noncomputable section

namespace PolycyclicRecognition

open MeasureTheory

theorem measurePreserving_finAppend_law (τ : Measure ℝ) [SigmaFinite τ] (n k : ℕ) :
    MeasurePreserving (fun p : (Fin n → ℝ) × (Fin k → ℝ) => Fin.append p.1 p.2)
      ((Measure.pi (fun _ => τ)).prod (Measure.pi (fun _ => τ)))
      (Measure.pi (fun _ => τ)) := by
  have h₁ := measurePreserving_sumPiEquivProdPi_symm (fun _ : Fin n ⊕ Fin k => τ)
  have h₂ := measurePreserving_piCongrLeft (fun _ : Fin (n + k) => τ) finSumFinEquiv
  convert h₂.comp h₁ using 1
  all_goals try with_reducible_and_instances rfl
  ext p i
  obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective i
  simp only [Function.comp_apply]
  rw [MeasurableEquiv.piCongrLeft_apply_apply]
  cases j with
  | inl j =>
    change Fin.append p.1 p.2 (Fin.castAdd k j) = p.1 j
    simp
  | inr j =>
    change Fin.append p.1 p.2 (Fin.natAdd n j) = p.2 j
    simp

theorem measurePreserving_flatSamplePairs (τ : Measure ℝ) [SigmaFinite τ] (m : ℕ) :
    MeasurePreserving (flatSamplePairs m)
      (Measure.pi (fun _ => τ)) (Measure.pi (fun _ : Fin m => τ.prod τ)) := by
  let e := (Fin.appendIsometry (α := ℝ) m m).toHomeomorph.toMeasurableEquiv
  have he : MeasurePreserving e
      ((Measure.pi (fun _ => τ)).prod (Measure.pi (fun _ => τ)))
      (Measure.pi (fun _ => τ)) := measurePreserving_finAppend_law τ m m
  have hp := (measurePreserving_arrowProdEquivProdArrow ℝ ℝ (Fin m)
    (fun _ => τ) (fun _ => τ)).symm (MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ (Fin m))
  convert hp.comp (he.symm e) using 1
  all_goals try with_reducible_and_instances rfl
  ext t j <;> rfl

theorem measurePreserving_flatSwitchSamples (τ : Measure ℝ) [IsProbabilityMeasure τ]
    (n m : ℕ) :
    MeasurePreserving (flatSwitchSamples m)
      (Measure.pi (fun _ => τ)) (switchParameterLaw (fun _ => τ) n m) :=
  (measurePreserving_vectorSwitchParameters τ n m).comp (measurePreserving_flatSamplePairs τ m)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_UniformIntervalSamples
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_countable _root_.OAI.PolycyclicRecognition.finitelyGeneratedSubgroupIndex_countable _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform interval sampling has a fixed density on the full parameter cube -/

noncomputable section

namespace PolycyclicRecognition

open Set Metric MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal

theorem uniformIntervalLaw_isProbability {R : ℝ} (hR : 0 < R) :
    IsProbabilityMeasure (uniformIntervalLaw R) := by
  apply cond_isProbabilityMeasure_of_finite
  · simpa only [Real.volume_closedBall, ne_eq, ENNReal.ofReal_eq_zero] using
      (not_le.mpr (mul_pos (by norm_num : (0 : ℝ) < 2) hR))
  · rw [Real.volume_closedBall]
    exact ENNReal.ofReal_ne_top

theorem uniformIntervalLaw_pi_eq {R : ℝ} (hR : 0 < R) (m : ℕ) :
    Measure.pi (fun _ : Fin m => uniformIntervalLaw R) =
      (ENNReal.ofReal (2 * R))⁻¹ ^ m • volume.restrict (closedBall (0 : Fin m → ℝ) R) := by
  let _ := uniformIntervalLaw_isProbability hR
  apply Measure.pi_eq
  intro s hs
  rw [Measure.smul_apply, Measure.restrict_apply (MeasurableSet.univ_pi hs)]
  have hint : univ.pi s ∩ closedBall (0 : Fin m → ℝ) R =
      univ.pi (fun i => s i ∩ closedBall 0 R) := by
    rw [closedBall_pi _ hR.le]
    ext x
    simp only [mem_inter_iff, Set.mem_pi, mem_univ, forall_const, Pi.zero_apply]
    exact ⟨fun h i => ⟨h.1 i, h.2 i⟩, fun h => ⟨fun i => (h i).1, fun i => (h i).2⟩⟩
  rw [hint, volume_pi_pi]
  simp only [uniformIntervalLaw, ProbabilityTheory.cond, Measure.smul_apply,
    Measure.restrict_apply (hs _), smul_eq_mul, Real.volume_closedBall]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

theorem uniformIntervalLaw_pi_le {R : ℝ} (hR : 0 < R) (m : ℕ) :
    Measure.pi (fun _ : Fin m => uniformIntervalLaw R) ≤
      (ENNReal.ofReal (2 * R))⁻¹ ^ m • (volume : Measure (Fin m → ℝ)) := by
  rw [uniformIntervalLaw_pi_eq hR]
  intro s
  simp only [Measure.smul_apply, smul_eq_mul]
  gcongr
  exact Measure.restrict_le_self

theorem uniformIntervalLaw_pi_ae_mem {R : ℝ} (hR : 0 < R) (m : ℕ) :
    ∀ᵐ x : Fin m → ℝ ∂Measure.pi (fun _ => uniformIntervalLaw R), x ∈ closedBall 0 R := by
  rw [uniformIntervalLaw_pi_eq hR]
  exact Measure.ae_smul_measure (ae_restrict_mem measurableSet_closedBall) _

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_SampledSuccessfulVolume
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual successful interval parameters have subexponential volume -/

noncomputable section

namespace PolycyclicRecognition

open Set Metric MeasureTheory Filter
open scoped Topology

theorem measurePreserving_sampledSwitchParameters {G : Type} [MeasurableSpace G]
    (f : ℕ → ℝ → G) (τ : Measure ℝ) [IsProbabilityMeasure τ]
    (σ : ℕ → Measure G) [∀ j, IsProbabilityMeasure (σ j)]
    (hf : ∀ j, MeasurePreserving (f j) τ (σ j)) (m : ℕ) :
    MeasurePreserving (sampledSwitchParameters f m)
      (Measure.pi (fun _ => τ)) (switchParameterLaw σ 0 m) :=
  (measurePreserving_mapSwitchParameters f (fun _ => τ) σ hf 0 m).comp
    (measurePreserving_flatSwitchSamples τ 0 m)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_SequenceSuccessfulParameterMass
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Successful parameter volume along the profile-scale sequence -/

noncomputable section

namespace PolycyclicRecognition

open Set Metric MeasureTheory Filter
open scoped Topology ENNReal NNReal

theorem exists_subexponential_successful_parameters_sequence
    {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]
    (scale : ℕ → ℝ) (hscale : Tendsto scale atTop atTop)
    (μ : Measure G) [SFinite μ] [μ.IsMulRightInvariant]
    (σ : ℕ → ℕ → Measure G) [∀ r j, IsProbabilityMeasure (σ r j)]
    (Q A : ℕ → Set G) (K R : ℕ → ℕ → Set G) (D : ℕ → ℕ → ℝ)
    (hQfin : ∀ r, μ (Q r) ≠ ∞) (hQpos : ∀ r, 0 < (μ (Q r)).toReal)
    (hK : ∀ r j, ∀ᵐ s ∂σ r j, s ∈ K r j)
    (hRfin : ∀ r j, μ (R r j) ≠ ∞) (hRpos : ∀ r j, 0 < (μ (R r j)).toReal)
    (hQR : ∀ r j, ∀ a ∈ Q r, ∀ s ∈ K r j, a * s ∈ R r j)
    (hD : ∀ r j, 0 < D r j)
    (hvol : ∀ r j, (μ (R r j)).toReal ≤ D r j * (μ (Q r)).toReal)
    (h : ℕ) (hA : ∀ r, MeasurableSet (A r)) (hAQ : ∀ r, A r ⊆ Q r)
    (hApos : ∀ r, 0 < (μ (A r)).toReal)
    (hAlower : HasSubexponentialLowerBoundSeq scale (fun r => (μ (A r)).toReal / (μ (Q r)).toReal))
    (hDupper : ∀ j, j < h → HasSubexponentialUpperBoundSeq scale (fun r => D r j)) :
    ∃ (x : ℕ → G) (E : ℕ → Set (SwitchParameters G h)),
      (∀ r, x r ∈ A r) ∧ (∀ r, MeasurableSet (E r)) ∧
      HasSubexponentialLowerBoundSeq scale (fun r => (switchParameterLaw (σ r) 0 h (E r)).toReal) ∧
      ∀ r p, p ∈ E r → SwitchSuccessful (fun _ => A r) 0 h (x r) p := by
  obtain ⟨S, hlast, hS, _, hprob, hlower⟩ := exists_subexponential_backward_recurrence_sequence
    scale hscale μ σ Q A K R D hQfin hQpos hK hRfin hRpos hQR hD hvol h hA hAQ hApos hAlower hDupper
  have hnonempty (r : ℕ) : (S r 0).Nonempty :=
    nonempty_of_measure_ne_zero (ne_of_gt (ENNReal.toReal_pos_iff.mp ((hS r 0 (Nat.zero_le h)).2.2)).1)
  choose x hx using hnonempty
  let E := fun r => {p : SwitchParameters G h | SwitchSuccessful (S r) 0 h (x r) p}
  have hevent (r : ℕ) := switchParameterLaw_success_finite (σ r) (S r) 0 h
    (fun j _ hj => (hS r j (by simpa using hj)).1) (x r)
  refine ⟨x, E, fun r => (hS r 0 (Nat.zero_le h)).2.1 (hx r), fun r => (hevent r).1, ?_, ?_⟩
  · apply hprob.mono
    apply Eventually.of_forall
    intro r
    apply ENNReal.toReal_mono (measure_ne_top _ _)
    rw [(hevent r).2]
    exact hlower r (x r) (hx r)
  · intro r p hp
    exact switchSuccessful_mono (S r) (fun _ => A r) 0 h
      (fun j _ hj => (hS r j (by simpa using hj)).2.1) (x r) p hp

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_SequenceCompactImage
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Subexponential volume of compact noncritical parameter images -/

noncomputable section

namespace PolycyclicRecognition

open Set MeasureTheory Filter
open scoped Topology

theorem subexponential_compact_image_sequence
    (scale : ℕ → ℝ) (hscale : Tendsto scale atTop atTop)
    (n : ℕ) (f : ℕ → (Fin n → ℝ) → (Fin n → ℝ))
    (df : ℕ → (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] (Fin n → ℝ))
    (R L η : ℕ → ℝ) (hR : ∀ r, 0 ≤ R r) (hL : ∀ r, 1 ≤ L r)
    (hη : ∀ r, 0 < η r)
    (hRupper : HasSubexponentialUpperBoundSeq scale R) (hLupper : HasSubexponentialUpperBoundSeq scale L)
    (hηlower : HasSubexponentialLowerBoundSeq scale η)
    (hf : ∀ r z, ‖z‖ ≤ R r + 2 → HasFDerivAt (f r) (df r z) z)
    (hdf : ∀ r z, ‖z‖ ≤ R r + 2 → ‖df r z‖ ≤ L r)
    (hosc : ∀ r z w, ‖z‖ ≤ R r + 2 → ‖w‖ ≤ R r + 2 →
      ‖df r z - df r w‖ ≤ L r * dist z w)
    (K : ℕ → Set (Fin n → ℝ)) (hK : ∀ r, IsCompact (K r))
    (hgood : ∀ r z, z ∈ K r → ‖z‖ ≤ R r ∧ η r ≤ |(df r z).det|)
    (hKlower : HasSubexponentialLowerBoundSeq scale (fun r => (volume (K r)).toReal)) :
    (∀ r, IsCompact (f r '' K r)) ∧
      HasSubexponentialLowerBoundSeq scale (fun r => (volume (f r '' K r)).toReal) := by
  obtain ⟨C, hC, hb⟩ := exists_compact_image_volume_bound n
  let D := fun r => 8 * (C * L r ^ (n - 1)) * L r
  let ρ := fun r => min 1 (η r / D r)
  have hL0 : ∀ᶠ r in atTop, 0 ≤ L r := Eventually.of_forall (fun r => le_trans zero_le_one (hL r))
  have hD : ∀ r, 0 < D r := by
    intro r
    have hLp : 0 < L r := lt_of_lt_of_le zero_lt_one (hL r)
    dsimp [D]
    positivity
  have hDupper : HasSubexponentialUpperBoundSeq scale D := by
    have hp := hLupper.pow hscale hL0 (n - 1)
    have hcp := (sequence_subexponential_upper_const hscale C).mul hp (Eventually.of_forall (fun _ => hC.le))
    have h8 := (sequence_subexponential_upper_const hscale 8).mul hcp (Eventually.of_forall (by intro r; norm_num))
    exact h8.mul hLupper (Eventually.of_forall (by
      intro r
      have hLp : 0 ≤ L r := le_trans zero_le_one (hL r)
      positivity))
  have hρlower : HasSubexponentialLowerBoundSeq scale ρ :=
    (sequence_subexponential_lower_const hscale zero_lt_one).min
      (hηlower.div hDupper (Eventually.of_forall hD))
  have hρpos (r : ℕ) : 0 < ρ r := lt_min zero_lt_one (div_pos (hη r) (hD r))
  let B := fun r => (2 * R r / ρ r + 2) ^ n
  have hBupper : HasSubexponentialUpperBoundSeq scale B := by
    have h2R := (sequence_subexponential_upper_const hscale 2).mul hRupper
      (Eventually.of_forall (by intro r; norm_num))
    have hquot := h2R.mul hρlower.inv (Eventually.of_forall (fun r => mul_nonneg (by norm_num) (hR r)))
    have hsum := hquot.add (sequence_subexponential_upper_const hscale 2) hscale
    simpa only [B, div_eq_mul_inv] using hsum.pow hscale (Eventually.of_forall (by
      intro r
      have h := hR r
      have h' := hρpos r
      positivity)) n
  have hBpos (r : ℕ) : 0 < B r := by
    have h := hR r
    have h' := hρpos r
    dsimp [B]
    positivity
  have hresult (r : ℕ) := hb (f r) (df r) (R r) (L r) (η r)
    (hR r) (hL r) (hη r) (hf r) (hdf r) (hosc r) (K r) (hK r) (hgood r)
  refine ⟨fun r => (hresult r).1, ?_⟩
  apply ((hηlower.mul hKlower).div hBupper (Eventually.of_forall hBpos)).mono
  apply Eventually.of_forall
  intro r
  apply (div_le_iff₀ (hBpos r)).mpr
  simpa only [B, ρ, D, mul_comm] using (hresult r).2

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_SequenceCompactSections
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # One compact slice retains subexponential volume -/

noncomputable section

namespace PolycyclicRecognition

open Set Metric MeasureTheory Filter
open scoped Topology

theorem exists_subexponential_compact_sections_sequence
    (scale : ℕ → ℝ) (hscale : Tendsto scale atTop atTop)
    (n k : ℕ) (R : ℕ → ℝ) (hR : ∀ r, 1 ≤ R r)
    (hRupper : HasSubexponentialUpperBoundSeq scale R)
    (K : ℕ → Set ((Fin n → ℝ) × (Fin k → ℝ)))
    (hK : ∀ r, IsCompact (K r))
    (hKR : ∀ r p, p ∈ K r → ‖p.2‖ ≤ R r)
    (hKpos : ∀ r, 0 < (volume (K r)).toReal)
    (hKlower : HasSubexponentialLowerBoundSeq scale (fun r => (volume (K r)).toReal)) :
    ∃ z : ℕ → Fin k → ℝ,
      (∀ r, ‖z r‖ ≤ R r) ∧
      (∀ r, IsCompact {v | (v, z r) ∈ K r}) ∧
      HasSubexponentialLowerBoundSeq scale (fun r => (volume {v | (v, z r) ∈ K r}).toReal) := by
  classical
  let q := fun r => (2 * R r) ^ k
  let t := fun r => (volume (K r)).toReal / (2 * q r)
  have hqpos (r : ℕ) : 0 < q r := by have := hR r; dsimp [q] <;> positivity
  have htpos (r : ℕ) : 0 < t r := div_pos (hKpos r) (mul_pos (by norm_num) (hqpos r))
  have hs (r : ℕ) : ∃ z ∈ closedBall 0 (R r),
      IsCompact {v | (v, z) ∈ K r} ∧ t r < (volume {v | (v, z) ∈ K r}).toReal := by
    apply exists_compact_section_volume_gt n k (q := q r) (hK r) (isCompact_closedBall _ _)
      (fun p hp => by simpa only [mem_closedBall, dist_zero_right] using hKR r p hp)
      (htpos r).le
    · rw [Real.volume_pi_closedBall _ (by have := hR r; linarith),
        ENNReal.toReal_ofReal (by have := hR r; positivity)]
      simp only [Fintype.card_fin, q, le_refl]
    · have he : t r * q r = (volume (K r)).toReal / 2 := by
        dsimp [t]
        field_simp [ne_of_gt (hqpos r)]
      rw [he]
      linarith [hKpos r]
  choose z hz hzc hmass using hs
  have hqUpper : HasSubexponentialUpperBoundSeq scale q :=
    ((sequence_subexponential_upper_const hscale 2).mul hRupper (Eventually.of_forall (by intro r; norm_num))).pow hscale
      (Eventually.of_forall (fun r => by have := hR r; positivity)) k
  have htLower : HasSubexponentialLowerBoundSeq scale t := hKlower.div
    ((sequence_subexponential_upper_const hscale 2).mul hqUpper (Eventually.of_forall (by intro r; norm_num)))
    (Eventually.of_forall (fun r => mul_pos (by norm_num) (hqpos r)))
  exact ⟨z, fun r => by simpa only [mem_closedBall, dist_zero_right] using hz r,
    hzc, htLower.mono (Eventually.of_forall (fun r => (hmass r).le))⟩

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_SequencePolynomialImage
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_countable _root_.OAI.PolycyclicRecognition.finitelyGeneratedSubgroupIndex_countable _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Compact image-volume witnesses for arbitrary measurable parameters

The domain can have more coordinates than the range. The scalar polynomial
is an actual derivative minor. Remez, inner regularity, Fubini, and the
quantitative injective patch estimate provide the compact image witnesses.
-/

noncomputable section

namespace PolycyclicRecognition

open Set Metric MeasureTheory Filter
open scoped Topology

theorem exists_subexponential_polynomial_image_sequence
    (scale : ℕ → ℝ) (hscale : Tendsto scale atTop atTop)
    (rem : RemezPolynomialInput) (n k D : ℕ) (hn : 1 ≤ n) (hD : 1 ≤ D)
    (f : ℕ → (Fin (n + k) → ℝ) → (Fin n → ℝ))
    (df : ℕ → (Fin n → ℝ) → (Fin k → ℝ) → (Fin n → ℝ) →L[ℝ] (Fin n → ℝ))
    (p : ℕ → MvPolynomial (Fin (n + k)) ℝ)
    (hp : ∀ r, (p r).totalDegree ≤ D)
    (hminor : ∀ r v z, MvPolynomial.eval (Fin.append v z) (p r) = (df r v z).det)
    (R L c : ℕ → ℝ) (hR : ∀ r, 1 ≤ R r) (hL : ∀ r, 1 ≤ L r)
    (hc : ∀ r, 0 < c r)
    (hRupper : HasSubexponentialUpperBoundSeq scale R) (hLupper : HasSubexponentialUpperBoundSeq scale L)
    (hclower : HasSubexponentialLowerBoundSeq scale c)
    (hf : ∀ r z, ‖z‖ ≤ R r → ∀ v, ‖v‖ ≤ R r + 2 →
      HasFDerivAt (fun w => f r (Fin.append w z)) (df r v z) v)
    (hdf : ∀ r z, ‖z‖ ≤ R r → ∀ v, ‖v‖ ≤ R r + 2 → ‖df r v z‖ ≤ L r)
    (hosc : ∀ r z, ‖z‖ ≤ R r → ∀ v w, ‖v‖ ≤ R r + 2 → ‖w‖ ≤ R r + 2 →
      ‖df r v z - df r w z‖ ≤ L r * dist v w)
    (x₀ : ℕ → Fin (n + k) → ℝ) (hx₀ : ∀ r, x₀ r ∈ closedBall 0 (R r))
    (hvalue : ∀ r, c r ≤ |MvPolynomial.eval (x₀ r) (p r)|)
    (E : ℕ → Set (Fin (n + k) → ℝ)) (hE : ∀ r, MeasurableSet (E r))
    (hER : ∀ r, E r ⊆ closedBall 0 (R r))
    (hm : ∀ r, 0 < (volume (E r)).toReal)
    (hmlower : HasSubexponentialLowerBoundSeq scale (fun r => (volume (E r)).toReal)) :
    ∃ C : ℕ → Set (Fin n → ℝ),
      (∀ r, IsCompact (C r)) ∧ (∀ r, C r ⊆ f r '' E r) ∧
      HasSubexponentialLowerBoundSeq scale (fun r => (volume (C r)).toReal) := by
  obtain ⟨η, K, hη, hηlower, hKE, hK, hKpos, hKlower, hgood⟩ :=
    exists_subexponential_large_polynomial_values_sequence scale hscale rem (n + k) D (by omega) hD
      p hp R c hR hc hRupper hclower x₀ hx₀ hvalue E hE hER hm hmlower
  let e := Fin.appendIsometry (α := ℝ) n k
  let K' := fun r => e ⁻¹' K r
  have hK' (r : ℕ) : IsCompact (K' r) := e.toHomeomorph.isCompact_preimage.mpr (hK r)
  have hK'mass (r : ℕ) : volume (K' r) = volume (K r) :=
    (measurePreserving_finAppend n k).measure_preimage (hK r).measurableSet.nullMeasurableSet
  have hbound (r : ℕ) (v : (Fin n → ℝ) × (Fin k → ℝ)) (hv : v ∈ K' r) :
      ‖v‖ ≤ R r := by
    have hb := hER r (hKE r hv)
    have hd := e.dist_eq v 0
    have he0 : e 0 = 0 := by
      ext i
      refine Fin.addCases ?_ ?_ i <;> intro j <;> simp [e]
    rw [he0, dist_zero_right, dist_zero_right] at hd
    simpa only [mem_closedBall, dist_zero_right, hd] using hb
  obtain ⟨z, hz, hs, hsmass⟩ := exists_subexponential_compact_sections_sequence scale hscale n k R hR hRupper
    K' hK' (fun r v hv => (norm_snd_le v).trans (hbound r v hv))
    (fun r => by rw [hK'mass]; exact hKpos r)
    (by simpa only [hK'mass] using hKlower)
  have himage := subexponential_compact_image_sequence scale hscale n
    (fun r v => f r (Fin.append v (z r))) (fun r v => df r v (z r))
    R L η (fun r => (hR r).trans' zero_le_one) hL hη hRupper hLupper hηlower
    (fun r => hf r (z r) (hz r)) (fun r => hdf r (z r) (hz r))
    (fun r => hosc r (z r) (hz r))
    (fun r => {v | (v, z r) ∈ K' r}) hs (fun r v hv => by
      refine ⟨(norm_fst_le (v, z r)).trans (hbound r (v, z r) hv), ?_⟩
      rw [← hminor]
      exact hgood r _ hv) hsmass
  refine ⟨fun r => (fun v => f r (Fin.append v (z r))) '' {v | (v, z r) ∈ K' r},
    himage.1, ?_, himage.2⟩
  intro r y hy
  obtain ⟨v, hv, rfl⟩ := hy
  exact ⟨Fin.append v (z r), hKE r hv, rfl⟩

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_SequenceSmoothPolynomialImage
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial image volume along the actual profile-scale sequence -/

noncomputable section

namespace PolycyclicRecognition

open Set Metric MeasureTheory Filter
open scoped Topology

theorem compact_smooth_polynomial_family_image_sequence
    {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (scale : ℕ → ℝ) (hscale : Tendsto scale atTop atTop)
    (rem : RemezPolynomialInput) (n k : ℕ) (hn : 1 ≤ n)
    (f : P × (Fin (n + k) → ℝ) → (Fin n → ℝ))
    (hf : ContDiff ℝ 2 f)
    (hpoly : HasPolynomialCoordinates (fun a x => f (a, x)))
    (S : Set P) (hS : IsCompact S) (b : ℕ → P) (hb : ∀ r, b r ∈ S)
    (R c : ℝ) (hR : 1 ≤ R) (hc : 0 < c)
    (v₀ : Fin n → ℝ) (z₀ : Fin k → ℝ)
    (hanchor : Fin.append v₀ z₀ ∈ closedBall 0 R)
    (hdet : ∀ a ∈ S, c ≤ |(fderiv ℝ (fun v => f (a, Fin.append v z₀)) v₀).det|)
    (E : ℕ → Set (Fin (n + k) → ℝ)) (hE : ∀ r, MeasurableSet (E r))
    (hER : ∀ r, E r ⊆ closedBall 0 R)
    (hm : ∀ r, 0 < (volume (E r)).toReal)
    (hmlower : HasSubexponentialLowerBoundSeq scale (fun r => (volume (E r)).toReal)) :
    ∃ C : ℕ → Set (Fin n → ℝ),
      (∀ r, IsCompact (C r)) ∧ (∀ r, C r ⊆ (fun x => f (b r, x)) '' E r) ∧
      HasSubexponentialLowerBoundSeq scale (fun r => (volume (C r)).toReal) := by
  obtain ⟨D, p, hp, hvalue⟩ := hpoly.exists_uniform_polynomials
  let F : (P × (Fin k → ℝ)) × (Fin n → ℝ) → (Fin n → ℝ) :=
    fun x => f (x.1.1, Fin.append x.2 x.1.2)
  have hF : ContDiff ℝ 2 F := hf.comp
    (contDiff_fst.fst.prodMk ((contDiff_finAppend n k).comp (contDiff_snd.prodMk contDiff_fst.snd)))
  obtain ⟨L, hL, hbound, hosc⟩ := compact_family_derivative_bounds F hF
    (hS.prod (isCompact_closedBall (0 : Fin k → ℝ) R)) (R + 2)
  let df := fun r v z => fderiv ℝ (fun w => f (b r, Fin.append w z)) v
  have hdfpoly (a : P) (v : Fin n → ℝ) (z : Fin k → ℝ) :
      fderiv ℝ (fun w => f (a, Fin.append w z)) v = polynomialSliceDifferential (p a) v z := by
    have he : (fun w i => MvPolynomial.eval (Fin.append w z) (p a i)) =
        (fun w => f (a, Fin.append w z)) := by
      funext w i
      exact hvalue a (Fin.append w z) i
    have hh := hasFDerivAt_polynomialSlice (p a) v z
    rw [he] at hh
    exact hh.fderiv
  have hminor (r : ℕ) (v : Fin n → ℝ) (z : Fin k → ℝ) :
      MvPolynomial.eval (Fin.append v z) (polynomialJacobianMinor (p (b r))) = (df r v z).det := by
    rw [eval_polynomialJacobianMinor, ← hdfpoly]
  apply exists_subexponential_polynomial_image_sequence scale hscale rem n k (max 1 (n * (D - 1))) hn (le_max_left _ _)
    (fun r x => f (b r, x)) df (fun r => polynomialJacobianMinor (p (b r)))
    (fun r => (totalDegree_polynomialJacobianMinor_le _ (hp (b r))).trans (le_max_right _ _))
    hminor (fun _ => R) (fun _ => L) (fun _ => c) (fun _ => hR) (fun _ => hL) (fun _ => hc)
    (sequence_subexponential_upper_const hscale R) (sequence_subexponential_upper_const hscale L) (sequence_subexponential_lower_const hscale hc)
    (fun r z _ v _ => ?_) (fun r z hz v hv => ?_) (fun r z hz v w hv hw => ?_)
    (fun _ => Fin.append v₀ z₀) (fun _ => hanchor)
    (fun r => by rw [hminor]; exact hdet (b r) (hb r)) E hE hER hm hmlower
  · exact ((hF.comp ((contDiff_const (c := (b r, z))).prodMk contDiff_id)).differentiable
      (by norm_num) v).hasFDerivAt
  · exact hbound (b r, z) ⟨hb r, by simpa using hz⟩ v hv
  · exact hosc (b r, z) ⟨hb r, by simpa using hz⟩ v w hv hw

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_SequenceConvergingPolynomialImage
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial image volume along the actual profile-scale sequence -/

noncomputable section

namespace PolycyclicRecognition

open Set Metric MeasureTheory Filter
open scoped Topology

theorem converging_smooth_polynomial_family_image_sequence
    {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (scale : ℕ → ℝ) (hscale : Tendsto scale atTop atTop)
    (rem : RemezPolynomialInput) (n k : ℕ) (hn : 1 ≤ n)
    (f : P × (Fin (n + k) → ℝ) → (Fin n → ℝ))
    (hf : ContDiff ℝ 2 f)
    (hpoly : HasPolynomialCoordinates (fun a x => f (a, x)))
    (S : Set P) (hS : IsCompact S) (b : ℕ → P) (hb : ∀ r, b r ∈ S)
    (b₀ : P) (hb₀ : b₀ ∈ S) (hlim : Tendsto b atTop (𝓝 b₀))
    (R : ℝ) (hR : 1 ≤ R) (v₀ : Fin n → ℝ) (z₀ : Fin k → ℝ)
    (hanchor : Fin.append v₀ z₀ ∈ closedBall 0 R)
    (hdet : (fderiv ℝ (fun v => f (b₀, Fin.append v z₀)) v₀).det ≠ 0)
    (E : ℕ → Set (Fin (n + k) → ℝ)) (hE : ∀ r, MeasurableSet (E r))
    (hER : ∀ r, E r ⊆ closedBall 0 R)
    (hm : ∀ r, 0 < (volume (E r)).toReal)
    (hmlower : HasSubexponentialLowerBoundSeq scale (fun r => (volume (E r)).toReal)) :
    ∃ C : ℕ → Set (Fin n → ℝ),
      (∀ r, IsCompact (C r)) ∧
      (∀ᶠ r in atTop, C r ⊆ (fun x => f (b r, x)) '' E r) ∧
      HasSubexponentialLowerBoundSeq scale (fun r => (volume (C r)).toReal) := by
  classical
  let d := fun a => fderiv ℝ (fun v => f (a, Fin.append v z₀)) v₀
  have hd : Continuous d := by
    have hg : ContDiff ℝ 2 (fun p : P × (Fin n → ℝ) => f (p.1, Fin.append p.2 z₀)) :=
      hf.comp (contDiff_fst.prodMk
        ((contDiff_finAppend n k).comp (contDiff_snd.prodMk contDiff_const)))
    have hh : ContDiff ℝ 1 d := ContDiff.fderiv hg (contDiff_const (c := v₀)) (by norm_num)
    exact hh.continuous
  let D := fun a => |(d a).det|
  have hD : Continuous D := (continuous_det_clm hd).abs
  have hDpos : 0 < D b₀ := abs_pos.mpr hdet
  let c := D b₀ / 2
  have hc : 0 < c := half_pos hDpos
  let T := S ∩ {a | c ≤ D a}
  have hT : IsCompact T := hS.inter_right (isClosed_le continuous_const hD)
  have hb₀T : b₀ ∈ T := ⟨hb₀, (half_le_self hDpos.le)⟩
  have hlate : ∀ᶠ r in atTop, b r ∈ T := by
    have hh := (hD.continuousAt.tendsto.comp hlim).eventually
      (Ioi_mem_nhds (show c < D b₀ from half_lt_self hDpos))
    filter_upwards [hh] with r hr
    exact ⟨hb r, hr.le⟩
  let b' := fun r => if b r ∈ T then b r else b₀
  have hb' : ∀ r, b' r ∈ T := by
    intro r
    dsimp [b']
    split_ifs with h
    · exact h
    · exact hb₀T
  obtain ⟨C, hC, hCE, hClower⟩ := compact_smooth_polynomial_family_image_sequence
    scale hscale rem n k hn f hf hpoly T hT b' hb' R c hR hc v₀ z₀ hanchor
    (fun a ha => ha.2) E hE hER hm hmlower
  refine ⟨C, hC, ?_, hClower⟩
  filter_upwards [hlate] with r hr
  simpa only [b', ite_eq_left hr] using hCE r

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_SequenceSubmersivePolynomialImage
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_countable _root_.OAI.PolycyclicRecognition.finitelyGeneratedSubgroupIndex_countable _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial image volume along the actual profile-scale sequence -/

noncomputable section

namespace PolycyclicRecognition

open Set Metric MeasureTheory Filter
open scoped Topology

theorem converging_submersive_polynomial_image_sequence
    {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] {m n : ℕ}
    (scale : ℕ → ℝ) (hscale : Tendsto scale atTop atTop)
    (rem : RemezPolynomialInput) (hn : 1 ≤ n)
    (f : P × (Fin m → ℝ) → (Fin n → ℝ)) (hf : ContDiff ℝ 2 f)
    (hpoly : HasPolynomialCoordinates (fun a x => f (a, x)))
    (S : Set P) (hS : IsCompact S) (b : ℕ → P) (hb : ∀ r, b r ∈ S)
    (b₀ : P) (hb₀ : b₀ ∈ S) (hlim : Tendsto b atTop (𝓝 b₀))
    (R : ℝ) (hR : 1 ≤ R) (t₀ : Fin m → ℝ) (ht₀ : ‖t₀‖ ≤ R)
    (hs : Function.Surjective (fderiv ℝ (fun x => f (b₀, x)) t₀))
    (E : ℕ → Set (Fin m → ℝ)) (hE : ∀ r, MeasurableSet (E r))
    (hER : ∀ r, E r ⊆ closedBall 0 R)
    (hm : ∀ r, 0 < (volume (E r)).toReal)
    (hmlower : HasSubexponentialLowerBoundSeq scale (fun r => (volume (E r)).toReal)) :
    ∃ C : ℕ → Set (Fin n → ℝ),
      (∀ r, IsCompact (C r)) ∧
      (∀ᶠ r in atTop, C r ⊆ (fun x => f (b r, x)) '' E r) ∧
      HasSubexponentialLowerBoundSeq scale (fun r => (volume (C r)).toReal) := by
  classical
  obtain ⟨j, hj, hminor⟩ := exists_nonsingular_column_minor
    (fderiv ℝ (fun x => f (b₀, x)) t₀).toLinearMap hs
  obtain ⟨k, e, he⟩ := exists_fin_equiv_extending_injection j hj
  let u₀ := reindexParameters e.symm t₀
  let v₀ := fun i : Fin n => u₀ (Fin.castAdd k i)
  let z₀ := fun i : Fin k => u₀ (Fin.natAdd n i)
  have hu : Fin.append v₀ z₀ = u₀ := by
    ext i
    refine Fin.addCases ?_ ?_ i <;> intro i <;> simp [v₀, z₀]
  have hback : reindexParameters e (Fin.append v₀ z₀) = t₀ := by
    rw [hu]
    ext i
    simp [u₀]
  let g := fun p : P × (Fin (n + k) → ℝ) => f (p.1, reindexParameters e p.2)
  have hg : ContDiff ℝ 2 g :=
    hf.comp (contDiff_fst.prodMk ((reindexParameters e).contDiff.comp contDiff_snd))
  have hgpoly : HasPolynomialCoordinates (fun a x => g (a, x)) :=
    fun i => (hpoly i).reindex e
  have hd : (fderiv ℝ (fun v => g (b₀, Fin.append v z₀)) v₀).det ≠ 0 := by
    have hfd : DifferentiableAt ℝ (fun x => f (b₀, x))
        (reindexParameters e (Fin.append v₀ z₀)) := by
      rw [hback]
      exact ((hf.comp (contDiff_const.prodMk contDiff_id)).differentiable (by norm_num)).differentiableAt
    rw [show (fun v => g (b₀, Fin.append v z₀)) =
      (fun v => f (b₀, reindexParameters e (Fin.append v z₀))) from rfl,
      det_reindexed_slice e (fun x => f (b₀, x)) v₀ z₀ hfd, hback]
    simpa only [he, ContinuousLinearMap.coe_coe] using hminor
  let E' := fun r => reindexParameters e ⁻¹' E r
  have hE' : ∀ r, MeasurableSet (E' r) :=
    fun r => (hE r).preimage (reindexParameters e).continuous.measurable
  have hvol (r : ℕ) : volume (E' r) = volume (E r) :=
    (measurePreserving_reindexParameters e).measure_preimage (hE r).nullMeasurableSet
  have hER' (r : ℕ) : E' r ⊆ closedBall 0 R := by
    intro x hx
    have hh := hER r hx
    simpa only [mem_closedBall, dist_zero_right, reindexParameters_norm] using hh
  have hanchor : Fin.append v₀ z₀ ∈ closedBall 0 R := by
    rw [hu, mem_closedBall, dist_zero_right, reindexParameters_norm]
    exact ht₀
  obtain ⟨C, hC, hCE, hClower⟩ := converging_smooth_polynomial_family_image_sequence
    scale hscale rem n k hn g hg hgpoly S hS b hb b₀ hb₀ hlim R hR v₀ z₀ hanchor hd
    E' hE' hER' (fun r => by rw [hvol]; exact hm r) (by simpa only [hvol] using hmlower)
  refine ⟨C, hC, ?_, hClower⟩
  filter_upwards [hCE] with r hr
  rintro y hy
  obtain ⟨x, hx, rfl⟩ := hr hy
  exact ⟨reindexParameters e x, hx, rfl⟩

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_SequenceEventualPolynomialImage
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Successful parameter volume along the profile-scale sequence -/

noncomputable section

namespace PolycyclicRecognition

open Set Metric MeasureTheory Filter
open scoped Topology ENNReal NNReal

theorem converging_submersive_polynomial_image_eventual_sequence
    {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] {m n : ℕ}
    (scale : ℕ → ℝ) (hscale : Tendsto scale atTop atTop)
    (rem : RemezPolynomialInput) (hn : 1 ≤ n)
    (f : P × (Fin m → ℝ) → (Fin n → ℝ)) (hf : ContDiff ℝ 2 f)
    (hpoly : HasPolynomialCoordinates (fun a x => f (a, x)))
    (S : Set P) (hS : IsCompact S) (b : ℕ → P) (hb : ∀ r, b r ∈ S)
    (b₀ : P) (hb₀ : b₀ ∈ S) (hlim : Tendsto b atTop (𝓝 b₀))
    (R : ℝ) (hR : 1 ≤ R) (t₀ : Fin m → ℝ) (ht₀ : ‖t₀‖ ≤ R)
    (hs : Function.Surjective (fderiv ℝ (fun x => f (b₀, x)) t₀))
    (E : ℕ → Set (Fin m → ℝ)) (hE : ∀ r, MeasurableSet (E r))
    (hER : ∀ r, E r ⊆ closedBall 0 R)
    (hmlower : HasSubexponentialLowerBoundSeq scale (fun r => (volume (E r)).toReal)) :
    ∃ C : ℕ → Set (Fin n → ℝ),
      (∀ r, IsCompact (C r)) ∧
      (∀ᶠ r in atTop, C r ⊆ (fun x => f (b r, x)) '' E r) ∧
      HasSubexponentialLowerBoundSeq scale (fun r => (volume (C r)).toReal) := by
  obtain ⟨E', hE', hER', hm', hlower', heq⟩ :=
    exists_positive_parameter_sets_sequence scale (lt_of_lt_of_le zero_lt_one hR) E hE hER hmlower
  obtain ⟨C, hC, hCE, hlower⟩ := converging_submersive_polynomial_image_sequence
    scale hscale rem hn f hf hpoly S hS b hb b₀ hb₀ hlim R hR t₀ ht₀ hs E' hE' hER' hm' hlower'
  refine ⟨C, hC, ?_, hlower⟩
  filter_upwards [hCE, heq] with r hr he
  simpa only [he] using hr

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_SequenceUniformInterval
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Successful parameter volume along the profile-scale sequence -/

noncomputable section

namespace PolycyclicRecognition

open Set Metric MeasureTheory Filter
open scoped Topology ENNReal NNReal

theorem subexponential_volume_of_uniform_samples_sequence {R : ℝ}
    (scale : ℕ → ℝ) (hscale : Tendsto scale atTop atTop) (hR : 0 < R) (m : ℕ)
    (E : ℕ → Set (Fin m → ℝ)) (hER : ∀ r, E r ⊆ closedBall 0 R)
    (hprob : HasSubexponentialLowerBoundSeq scale
      (fun r => (Measure.pi (fun _ : Fin m => uniformIntervalLaw R) (E r)).toReal)) :
    HasSubexponentialLowerBoundSeq scale (fun r => (volume (E r)).toReal) := by
  let d : ℝ≥0 := ((ENNReal.ofReal (2 * R))⁻¹ ^ m).toNNReal
  have htop : (ENNReal.ofReal (2 * R))⁻¹ ^ m ≠ ∞ := by
    apply ENNReal.pow_ne_top
    exact ENNReal.inv_ne_top.mpr (by positivity)
  have hd : (d : ℝ≥0∞) = (ENNReal.ofReal (2 * R))⁻¹ ^ m := ENNReal.coe_toNNReal htop
  apply subexponential_volume_of_probability_sequence scale (fun _ => volume)
    (fun _ => Measure.pi (fun _ : Fin m => uniformIntervalLaw R)) E (fun _ => d)
    (fun r => ne_top_of_le_ne_top (measure_closedBall_lt_top.ne) (measure_mono (hER r)))
    (fun _ => by rw [hd]; exact uniformIntervalLaw_pi_le hR m) hprob
    (sequence_subexponential_upper_const hscale _) (Eventually.of_forall fun _ => ?_)
  exact ENNReal.toNNReal_pos (pow_ne_zero _ (ENNReal.inv_ne_zero.mpr ENNReal.ofReal_ne_top)) htop

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_SequenceSampledSuccessfulVolume
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_countable _root_.OAI.PolycyclicRecognition.finitelyGeneratedSubgroupIndex_countable _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Successful parameter volume along the profile-scale sequence -/

noncomputable section

namespace PolycyclicRecognition

open Set Metric MeasureTheory Filter
open scoped Topology ENNReal NNReal

theorem exists_sampled_success_volume_sequence {G : Type} [Group G] [MeasurableSpace G]
    {R : ℝ} (hR : 0 < R) (m : ℕ)
    (scale : ℕ → ℝ) (hscale : Tendsto scale atTop atTop)
    (f : ℕ → ℕ → ℝ → G) (σ : ℕ → ℕ → Measure G)
    [∀ r j, IsProbabilityMeasure (σ r j)]
    (hf : ∀ r j, MeasurePreserving (f r j) (uniformIntervalLaw R) (σ r j))
    (x : ℕ → G) (A : ℕ → Set G) (E : ℕ → Set (SwitchParameters G m))
    (hE : ∀ r, MeasurableSet (E r))
    (hprob : HasSubexponentialLowerBoundSeq scale (fun r => (switchParameterLaw (σ r) 0 m (E r)).toReal))
    (hsuccess : ∀ r p, p ∈ E r → SwitchSuccessful (fun _ => A r) 0 m (x r) p) :
    ∃ F : ℕ → Set (Fin (m + m) → ℝ),
      (∀ r, MeasurableSet (F r)) ∧ (∀ r, F r ⊆ closedBall 0 R) ∧
      HasSubexponentialLowerBoundSeq scale (fun r => (volume (F r)).toReal) ∧
      ∀ r t, t ∈ F r → SwitchSuccessful (fun _ => A r) 0 m (x r)
        (sampledSwitchParameters (f r) m t) := by
  let _ := uniformIntervalLaw_isProbability hR
  let F := fun r => sampledSwitchParameters (f r) m ⁻¹' E r ∩ closedBall 0 R
  have hmap (r : ℕ) := measurePreserving_sampledSwitchParameters (f r)
    (uniformIntervalLaw R) (σ r) (hf r) m
  have hvol (r : ℕ) : Measure.pi (fun _ : Fin (m + m) => uniformIntervalLaw R) (F r) =
      switchParameterLaw (σ r) 0 m (E r) := by
    change Measure.pi _ (_ ∩ _) = _
    rw [measure_inter_conull (show Measure.pi (fun _ : Fin (m + m) => uniformIntervalLaw R)
        (closedBall (0 : Fin (m + m) → ℝ) R)ᶜ = 0 from
      mem_ae_iff.mp (uniformIntervalLaw_pi_ae_mem hR (m + m)))]
    exact (hmap r).measure_preimage (hE r).nullMeasurableSet
  refine ⟨F, fun r => ((hE r).preimage (hmap r).measurable).inter measurableSet_closedBall,
    fun _ => inter_subset_right, ?_, ?_⟩
  · apply subexponential_volume_of_uniform_samples_sequence scale hscale hR (m + m) F (fun _ => inter_subset_right)
    simpa only [hvol] using hprob
  · intro r t ht
    exact hsuccess r _ ht.1

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_SequenceSuccessfulWordImage
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Successful parameter volume along the profile-scale sequence -/

noncomputable section

namespace PolycyclicRecognition

open Set Metric MeasureTheory Filter
open scoped Topology ENNReal NNReal

theorem successful_differenceWord_image_sequence
    {I G : Type} [Fintype I] [Group G] [MeasurableSpace G] {n m c : ℕ}
    (scale : ℕ → ℝ) (hscale : Tendsto scale atTop atTop)
    (rem : RemezPolynomialInput) (hn : 1 ≤ n) (a : DynkinCoefficients c 2)
    (letters : Fin m → I)
    (S : Set (((Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) × (I → Fin n → ℝ)))
    (hS : IsCompact S)
    (b : ℕ → ((Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) × (I → Fin n → ℝ))
    (hb : ∀ r, b r ∈ S)
    (b₀ : ((Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) × (I → Fin n → ℝ))
    (hb₀ : b₀ ∈ S) (hlim : Tendsto b atTop (𝓝 b₀))
    (R : ℝ) (hR : 1 ≤ R) (t₀ : Fin (m + m) → ℝ) (ht₀ : ‖t₀‖ ≤ R)
    (hs : Function.Surjective (fderiv ℝ (differenceAmplitudeWordEndpoint a letters b₀) t₀))
    (sample : ℕ → ℕ → ℝ → G) (σ : ℕ → ℕ → Measure G)
    [∀ r j, IsProbabilityMeasure (σ r j)]
    (hsample : ∀ r j, MeasurePreserving (sample r j) (uniformIntervalLaw R) (σ r j))
    (x : ℕ → G) (A : ℕ → Set G) (E : ℕ → Set (SwitchParameters G m))
    (hE : ∀ r, MeasurableSet (E r))
    (hprob : HasSubexponentialLowerBoundSeq scale (fun r => (switchParameterLaw (σ r) 0 m (E r)).toReal))
    (hsuccess : ∀ r p, p ∈ E r → SwitchSuccessful (fun _ => A r) 0 m (x r) p) :
    ∃ C : ℕ → Set (Fin n → ℝ),
      (∀ r, IsCompact (C r)) ∧
      HasSubexponentialLowerBoundSeq scale (fun r => (volume (C r)).toReal) ∧
      ∀ᶠ r in atTop, ∀ y ∈ C r, ∃ t ∈ closedBall (0 : Fin (m + m) → ℝ) R,
        SwitchSuccessful (fun _ => A r) 0 m (x r) (sampledSwitchParameters (sample r) m t) ∧
        differenceAmplitudeWordEndpoint a letters (b r) t = y := by
  obtain ⟨F, hF, hFR, hFvol, hFs⟩ := exists_sampled_success_volume_sequence
    (lt_of_lt_of_le zero_lt_one hR) m scale hscale sample σ hsample x A E hE hprob hsuccess
  obtain ⟨C, hC, hCF, hCvol⟩ := converging_submersive_polynomial_image_eventual_sequence
    scale hscale rem hn (fun z => differenceAmplitudeWordEndpoint a letters z.1 z.2)
    (contDiff_differenceAmplitudeWord a letters)
    (hasPolynomialCoordinates_differenceAmplitudeWord a letters)
    S hS b hb b₀ hb₀ hlim R hR t₀ ht₀ hs F hF hFR hFvol
  refine ⟨C, hC, hCvol, ?_⟩
  filter_upwards [hCF] with r hr
  intro y hy
  obtain ⟨t, ht, he⟩ := hr hy
  exact ⟨t, hFR r ht, hFs r t ht, he⟩

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_SequenceRecurrentWordImage
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Successful parameter volume along the profile-scale sequence -/

noncomputable section

namespace PolycyclicRecognition

open Set Metric MeasureTheory Filter
open scoped Topology ENNReal NNReal

theorem recurrent_differenceWord_image_sequence
    {I G : Type} [Fintype I] [Group G] [MeasurableSpace G]
    [MeasurableMul₂ G] [MeasurableInv G] {n m c : ℕ}
    (scale : ℕ → ℝ) (hscale : Tendsto scale atTop atTop)
    (rem : RemezPolynomialInput) (hn : 1 ≤ n) (a : DynkinCoefficients c 2)
    (letters : Fin m → I)
    (S : Set (((Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) × (I → Fin n → ℝ)))
    (hS : IsCompact S)
    (b : ℕ → ((Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) × (I → Fin n → ℝ))
    (hb : ∀ r, b r ∈ S)
    (b₀ : ((Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) × (I → Fin n → ℝ))
    (hb₀ : b₀ ∈ S) (hlim : Tendsto b atTop (𝓝 b₀))
    (ρ : ℝ) (hρ : 1 ≤ ρ) (t₀ : Fin (m + m) → ℝ) (ht₀ : ‖t₀‖ ≤ ρ)
    (hs : Function.Surjective (fderiv ℝ (differenceAmplitudeWordEndpoint a letters b₀) t₀))
    (μ : Measure G) [SFinite μ] [μ.IsMulRightInvariant]
    (sample : ℕ → ℕ → ℝ → G) (σ : ℕ → ℕ → Measure G)
    [∀ r j, IsProbabilityMeasure (σ r j)]
    (hsample : ∀ r j, MeasurePreserving (sample r j) (uniformIntervalLaw ρ) (σ r j))
    (Q A : ℕ → Set G) (K R : ℕ → ℕ → Set G) (D : ℕ → ℕ → ℝ)
    (hQfin : ∀ r, μ (Q r) ≠ ∞) (hQpos : ∀ r, 0 < (μ (Q r)).toReal)
    (hK : ∀ r j, ∀ᵐ s ∂σ r j, s ∈ K r j)
    (hRfin : ∀ r j, μ (R r j) ≠ ∞) (hRpos : ∀ r j, 0 < (μ (R r j)).toReal)
    (hQR : ∀ r j, ∀ x ∈ Q r, ∀ s ∈ K r j, x * s ∈ R r j)
    (hD : ∀ r j, 0 < D r j)
    (hvol : ∀ r j, (μ (R r j)).toReal ≤ D r j * (μ (Q r)).toReal)
    (hA : ∀ r, MeasurableSet (A r)) (hAQ : ∀ r, A r ⊆ Q r)
    (hApos : ∀ r, 0 < (μ (A r)).toReal)
    (hAlower : HasSubexponentialLowerBoundSeq scale (fun r => (μ (A r)).toReal / (μ (Q r)).toReal))
    (hDupper : ∀ j, j < m → HasSubexponentialUpperBoundSeq scale (fun r => D r j)) :
    ∃ (x : ℕ → G) (C : ℕ → Set (Fin n → ℝ)),
      (∀ r, x r ∈ A r) ∧ (∀ r, IsCompact (C r)) ∧
      HasSubexponentialLowerBoundSeq scale (fun r => (volume (C r)).toReal) ∧
      ∀ᶠ r in atTop, ∀ y ∈ C r, ∃ t ∈ closedBall (0 : Fin (m + m) → ℝ) ρ,
        SwitchSuccessful (fun _ => A r) 0 m (x r) (sampledSwitchParameters (sample r) m t) ∧
        differenceAmplitudeWordEndpoint a letters (b r) t = y := by
  obtain ⟨x, E, hx, hE, hprob, hsuccess⟩ := exists_subexponential_successful_parameters_sequence
    scale hscale μ σ Q A K R D hQfin hQpos hK hRfin hRpos hQR hD hvol m hA hAQ hApos hAlower hDupper
  obtain ⟨C, hC, hCvol, hgood⟩ := successful_differenceWord_image_sequence
    scale hscale rem hn a letters S hS b hb b₀ hb₀ hlim ρ hρ t₀ ht₀ hs
    sample σ hsample x A E hE hprob hsuccess
  exact ⟨x, C, hx, hC, hCvol, hgood⟩

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_TemplateThickeningLimit
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finite_templateSymmetryGroup _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteRootOffsetConeIndex _root_.OAI.PolycyclicRecognition.instFiniteSubtypeLinearEquivRealIdMemSubgroupLinearSupportSymmetryGroup _root_.OAI.PolycyclicRecognition.instNonemptyRootOffsetConeIndex _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.CartanWordModel.supportDatum_weight _root_.OAI.PolycyclicRecognition.SupportDatum.transport_weight_apply _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Removing the final height-template enlargement -/

namespace PolycyclicRecognition.SupportDatum

open Set Metric
open scoped Pointwise

variable {W I B : Type} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [FiniteDimensional ℝ W] [Fintype I] [Fintype B] [Nonempty B]
  (D : SupportDatum W I B)

/-- An exponent bounded by every positive thickening is bounded by the
original compact template. -/
theorem le_templateSupport_of_thickenings {E : Set W} (hE : IsCompact E)
    (hne : E.Nonempty) {p : ℝ}
    (h : ∀ ε : ℝ, 0 < ε → p ≤ D.templateSupport (E + closedBall 0 ε)) :
    p ≤ D.templateSupport E := by
  apply le_of_forall_pos_le_add
  intro η hη
  let ε := η / (D.templateSupportConstant + 1)
  have hε : 0 < ε := div_pos hη (by linarith [D.templateSupportConstant_nonneg])
  have hn : (E + closedBall (0 : W) ε).Nonempty := by
    obtain ⟨z, hz⟩ := hne
    exact ⟨z + 0, add_mem_add hz (by simpa using hε.le)⟩
  have hu := D.templateSupport_le_of_nearby (hE.add (isCompact_closedBall 0 ε)) hn
    hE hε.le (show ∀ x ∈ E + closedBall 0 ε, ∃ y ∈ E, ‖x - y‖ ≤ ε by
      rintro x ⟨y, hy, u, hu, rfl⟩
      refine ⟨y, hy, ?_⟩
      simpa only [add_sub_cancel_left, mem_closedBall, dist_zero_right] using hu)
  have hsmall : D.templateSupportConstant * ε ≤ η := by
    dsimp [ε]
    rw [← mul_div_assoc]
    apply (div_le_iff₀ (by linarith [D.templateSupportConstant_nonneg])).mpr
    nlinarith
  exact (h ε hε).trans (hu.trans (add_le_add le_rfl hsmall))

end PolycyclicRecognition.SupportDatum

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_SwitchEndpoints
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The polynomial difference word is the endpoint of the successful switches -/

noncomputable section

namespace PolycyclicRecognition

variable {G : Type} [Group G]

theorem switchEndpoint_vector (m : ℕ) (x : G) (p : Fin m → G × G) :
    switchEndpoint m x (vectorSwitchParameters m p) =
      x * (List.ofFn (fun j => (p j).1 * (p j).2⁻¹)).prod := by
  induction m generalizing x with
  | zero => simp [switchEndpoint]
  | succ m ih =>
    rw [List.ofFn_succ, List.prod_cons]
    change switchEndpoint m (x * (p 0).1 * (p 0).2⁻¹)
      (vectorSwitchParameters m (fun j => p j.succ)) = _
    rw [ih]
    simp only [mul_assoc]

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

theorem sampledSwitchEndpoint_eq (f : ℕ → ℝ → G) (m : ℕ)
    (hf : ∀ j s t, f j s * (f j t)⁻¹ = f j (s - t))
    (x : G) (t : Fin (m + m) → ℝ) :
    switchEndpoint m x (sampledSwitchParameters f m t) =
      x * (List.ofFn (fun j : Fin m =>
        f j.val (t (Fin.castAdd m j) - t (Fin.natAdd m j)))).prod := by
  unfold sampledSwitchParameters flatSwitchSamples
  rw [mapSwitchParameters_vector, switchEndpoint_vector]
  simp only [Nat.zero_add, flatSamplePairs, hf]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_RescaledWordEndpoints
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.basisDynkinParameter_zero _root_.OAI.PolycyclicRecognition.dynkinRightTranslation_apply _root_.OAI.PolycyclicRecognition.dynkinRightTranslation_symm_apply _root_.OAI.PolycyclicRecognition.exponentialHomOfDynkin_apply_exp _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual group endpoints in rescaled logarithmic coordinates -/

noncomputable section

namespace PolycyclicRecognition

open Module

variable {L G I : Type} [LieRing L] [LieAlgebra ℝ L] [Group G] {n c m : ℕ}

theorem exp_basis_listProduct (b : Basis (Fin n) ℝ L) (Exp : L → G)
    (hzero : Exp 0 = 1) (a : DynkinCoefficients c 2)
    (hm : ∀ x y, Exp (finiteDynkinPolynomial a ![x, y]) = Exp x * Exp y)
    (xs : List (Fin n → ℝ)) :
    Exp (b.equivFun.symm (polynomialListProduct (dynkinProduct a (basisBracket b)) xs)) =
      (xs.map (fun x => Exp (b.equivFun.symm x))).prod := by
  induction xs with
  | nil => simpa [polynomialListProduct] using hzero
  | cons x xs ih =>
    simp only [polynomialListProduct, List.map_cons, List.prod_cons]
    have he := basis_dynkinProduct b a (b.equivFun.symm x)
      (b.equivFun.symm (polynomialListProduct (dynkinProduct a (basisBracket b)) xs))
    simp only [LinearEquiv.apply_symm_apply] at he
    rw [he, LinearEquiv.symm_apply_apply, hm, ih]

theorem exp_rescaled_differenceWord (b : Basis (Fin n) ℝ L) (Exp : L → G)
    (hzero : Exp 0 = 1) (a : DynkinCoefficients c 2)
    (hm : ∀ x y, Exp (finiteDynkinPolynomial a ![x, y]) = Exp x * Exp y)
    (X : I → L) (s : I → ℝ) (r : ℝ) (letters : Fin m → I)
    (t : Fin (m + m) → ℝ) :
    Exp (b.equivFun.symm (differenceAmplitudeWordEndpoint a letters
      (basisBracket b, fun i => b.equivFun (Real.exp (r * s i) • X i)) t)) =
      (List.ofFn (fun j => Exp
        ((t (Fin.castAdd m j) - t (Fin.natAdd m j)) •
          (Real.exp (r * s (letters j)) • X (letters j))))).prod := by
  unfold differenceAmplitudeWordEndpoint amplitudeWordEndpoint
  rw [exp_basis_listProduct b Exp hzero a hm, List.map_ofFn]
  simp only [Function.comp_def, differenceParameters_apply, map_smul, LinearEquiv.symm_apply_apply]

theorem sampled_rescaled_endpoint_eq (b : Basis (Fin n) ℝ L) (Exp : L → G)
    (hzero : Exp 0 = 1) (a : DynkinCoefficients c 2)
    (hm : ∀ x y, Exp (finiteDynkinPolynomial a ![x, y]) = Exp x * Exp y)
    (X : I → L) (s : I → ℝ) (r : ℝ) (letters : Fin m → I)
    (sample : ℕ → ℝ → G)
    (hsub : ∀ j u v, sample j u * (sample j v)⁻¹ = sample j (u - v))
    (hsample : ∀ j : Fin m, ∀ u, sample j.val u =
      Exp (u • (Real.exp (r * s (letters j)) • X (letters j))))
    (x : G) (t : Fin (m + m) → ℝ) :
    switchEndpoint m x (sampledSwitchParameters sample m t) =
      x * Exp (b.equivFun.symm (differenceAmplitudeWordEndpoint a letters
        (basisBracket b, fun i => b.equivFun (Real.exp (r * s i) • X i)) t)) := by
  rw [sampledSwitchEndpoint_eq sample m hsub, exp_rescaled_differenceWord b Exp hzero a hm]
  simp only [hsample]

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

theorem PathMetricBound.cast {p : Path x y} {L κ : ℝ} (h : PathMetricBound p L κ)
    {x' y' : X} (hx : x' = x) (hy : y' = y) : PathMetricBound (p.cast hx hy) L κ := h

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
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_SupportVisitPaths
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Outward, switch, and return paths

The actual three curves are concatenated, retaining their exact heights and
the logarithmic switch error. This statement is independent of how the
switch estimate is obtained and is used below for the Cartan root curves.
-/

noncomputable section

namespace PolycyclicRecognition

open scoped unitInterval

variable {G W : Type} [Group G] [PseudoMetricSpace G] [IsTopologicalGroup G]
  [IsIsometricSMul G G] [AddCommGroup W] [Module ℝ W]

omit [IsIsometricSMul G G] in
/-- Pointwise changes of representation preserve the specified visit curve. -/
theorem supportVisitPath_apply_congr
    (d d' f f' : ℝ → G) (hd : Continuous d) (hd' : Continuous d')
    (hd₀ : d 0 = 1) (hd₀' : d' 0 = 1)
    (hf : Continuous f) (hf' : Continuous f') (hf₀ : f 0 = 1) (hf₀' : f' 0 = 1)
    (he_d : ∀ t, d t = d' t) (he_f : ∀ t, f t = f' t)
    (n k k' : G) (he_k : k = k') (r b : ℝ) (t : unitInterval) :
    supportVisitPath d hd hd₀ f hf hf₀ n k r b t =
      supportVisitPath d' hd' hd₀' f' hf' hf₀' n k' r b t := by
  obtain rfl := funext he_d
  obtain rfl := funext he_f
  obtain rfl := he_k
  rfl

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_SuccessfulWordPaths
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
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

variable [PseudoMetricSpace G] [IsTopologicalGroup G]
  {I : Type} (d f : I → ℝ → G) (hd : ∀ i, Continuous (d i)) (hf : ∀ i, Continuous (f i))
  (hd₀ : ∀ i, d i 0 = 1) (hf₀ : ∀ i, f i 0 = 1) (d₀ : G) (r : ℝ)

/-- Concatenation only asks for the good states actually visited by this
word. The observable range need not be defined by a homomorphism. -/
theorem supportWordPath_good_bound (A S : Set G) (P : I → ℝ → Prop)
    {L κ : ℝ} (hL : 0 ≤ L) (hκ : 0 ≤ κ)
    (hbase : ∀ n ∈ A, n * d₀ ∈ S)
    (hstep : ∀ n ∈ A, ∀ i b, P i b → n * f i b ∈ A →
      PathMetricBound (supportVisitPath (d i) (hd i) (hd₀ i)
        (f i) (hf i) (hf₀ i) n d₀ r b) L κ ∧
      ∀ t, supportVisitPath (d i) (hd i) (hd₀ i)
        (f i) (hf i) (hf₀ i) n d₀ r b t ∈ S)
    (u : List (I × ℝ)) (hu : ∀ z ∈ u, P z.1 z.2) (n : G)
    (hgood : WordSheetsGood A n (u.map (fun z => f z.1 z.2))) :
    PathMetricBound (supportWordPath d f hd hf hd₀ hf₀ d₀ r u n)
      (L * 2 ^ u.length) (κ * 2 ^ u.length) ∧
      ∀ t, supportWordPath d f hd hf hd₀ hf₀ d₀ r u n t ∈ S := by
  induction u generalizing n with
  | nil =>
    constructor
    · intro s t
      change dist (n * d₀) (n * d₀) ≤ _
      simp only [dist_self, List.length_nil, pow_zero, mul_one]
      positivity
    · exact fun _ => hbase n hgood
  | cons z u ih =>
    rcases z with ⟨i, b⟩
    have hg : n ∈ A ∧ WordSheetsGood A (n * f i b) (u.map (fun z => f z.1 z.2)) := hgood
    have hu' : ∀ z ∈ u, P z.1 z.2 := fun z hz => hu z (List.mem_cons_of_mem _ hz)
    obtain ⟨hp, hpS⟩ := hstep n hg.1 i b (hu (i, b) List.mem_cons_self) hg.2.start
    obtain ⟨hq, hqS⟩ := ih hu' (n * f i b) hg.2
    have hpow : 1 ≤ (2 : ℝ) ^ u.length := one_le_pow₀ (by norm_num)
    have hp' := hp.mono
      (show L ≤ L * 2 ^ u.length by nlinarith)
      (show κ ≤ κ * 2 ^ u.length by nlinarith)
    constructor
    · have hb := hp'.trans (mul_nonneg hκ (by positivity)) hq
      have he : n * indexedWordProduct f ((i, b) :: u) * d₀ =
          (n * f i b) * indexedWordProduct f u * d₀ := by
        simp [indexedWordProduct, mul_assoc]
      have hb' := hb.cast rfl he
      convert hb' using 1 <;>
        first | rfl | (simp only [List.length_cons, pow_succ]; ring)
    · exact path_trans_range_mem hpS hqS

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_SuccessfulSamplePaths
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The exact path endpoint of a successful sample sequence -/

noncomputable section

namespace PolycyclicRecognition

open Set

variable {N G : Type} [Group N] [Group G]

/-- Transport the visited sheets through a subgroup map and a fixed left translate. -/
theorem WordSheetsGood.map_mul_hom (ι : N →* G) (x : G)
    {A : Set N} {n : N} {u : List N} (h : WordSheetsGood A n u) :
    WordSheetsGood ((fun v => x * ι v) '' A) (x * ι n) (u.map ι) := by
  induction u generalizing n with
  | nil => exact ⟨n, h, rfl⟩
  | cons g u ih =>
    refine ⟨⟨n, h.1, rfl⟩, ?_⟩
    simpa only [map_mul, mul_assoc] using ih h.2

variable [PseudoMetricSpace G] [IsTopologicalGroup G]

/-- A successful independent sample sequence gives the specified geometric
word path to its actual group endpoint, with bounds inherited from its
single-letter visits on the good sheets. -/
theorem successful_sample_path
    (ι : N →* G) (x d₀ : G) (A : Set N) (S : Set G) (m : ℕ)
    (sample : ℕ → ℝ → N) (hsub : ∀ j s t, sample j s * (sample j t)⁻¹ = sample j (s - t))
    (d : Fin m → ℝ → G) (hd : ∀ i, Continuous (d i)) (hd₀ : ∀ i, d i 0 = 1)
    (hf : ∀ i : Fin m, Continuous (fun t => ι (sample i.val t)))
    (hf₀ : ∀ i : Fin m, ι (sample i.val 0) = 1)
    (r : ℝ) {L κ ρ : ℝ} (hL : 0 ≤ L) (hκ : 0 ≤ κ)
    (hbase : ∀ n ∈ A, x * ι n * d₀ ∈ S)
    (hstep : ∀ n ∈ A, ∀ i : Fin m, ∀ b : ℝ, |b| ≤ 2 * ρ → n * sample i.val b ∈ A →
      PathMetricBound (supportVisitPath (d i) (hd i) (hd₀ i)
        (fun t => ι (sample i.val t)) (hf i) (hf₀ i) (x * ι n) d₀ r b) L κ ∧
      ∀ t, supportVisitPath (d i) (hd i) (hd₀ i)
        (fun t => ι (sample i.val t)) (hf i) (hf₀ i) (x * ι n) d₀ r b t ∈ S)
    (hinj : Function.Injective ι)
    (n : N) (hn : n ∈ A) (t : Fin (m + m) → ℝ) (ht : ‖t‖ ≤ ρ)
    (hs : SwitchSuccessful (fun _ => A) 0 m n (sampledSwitchParameters sample m t)) :
    ∃ γ : Path (x * ι n * d₀)
      (x * ι (switchEndpoint m n (sampledSwitchParameters sample m t)) * d₀),
      PathMetricBound γ (L * 2 ^ m) (κ * 2 ^ m) ∧ ∀ u, γ u ∈ S := by
  let f : Fin m → ℝ → G := fun j b => ι (sample j.val b)
  let word := List.ofFn (fun j : Fin m => (j, t (Fin.castAdd m j) - t (Fin.natAdd m j)))
  have hgood := (wordSheetsGood_sampled A sample hsub m t n hn hs).map_mul_hom ι x
  have hgood' : WordSheetsGood ((fun v => x * ι v) '' A) (x * ι n)
      (word.map (fun z => f z.1 z.2)) := by
    simpa only [word, List.map_ofFn, f, Function.comp_def] using hgood
  have hparam : ∀ z ∈ word, |z.2| ≤ 2 * ρ := by
    intro z hz
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hz
    have h₁ := (norm_le_pi_norm t (Fin.castAdd m j)).trans ht
    have h₂ := (norm_le_pi_norm t (Fin.natAdd m j)).trans ht
    have hh := abs_sub (t (Fin.castAdd m j)) (t (Fin.natAdd m j))
    rw [Real.norm_eq_abs] at h₁ h₂
    linarith
  obtain ⟨hbound, hrange⟩ := supportWordPath_good_bound d f hd hf hd₀ hf₀ d₀ r
    ((fun v => x * ι v) '' A) S (fun _ b => |b| ≤ 2 * ρ) hL hκ
    (by rintro _ ⟨v, hv, rfl⟩; exact hbase v hv)
    (by
      rintro _ ⟨v, hv, rfl⟩ i b hb ⟨w, hw, he⟩
      have hv' : v * sample i.val b ∈ A := by
        have he' : w = v * sample i.val b := hinj (by simpa [map_mul, mul_assoc] using he)
        exact he' ▸ hw
      exact hstep v hv i b hb hv') word hparam (x * ι n) hgood'
  let γ := supportWordPath d f hd hf hd₀ hf₀ d₀ r word (x * ι n)
  have hend : x * ι (switchEndpoint m n (sampledSwitchParameters sample m t)) * d₀ =
      (x * ι n) * indexedWordProduct f word * d₀ := by
    rw [sampledSwitchEndpoint_eq sample m hsub]
    simp only [map_mul, map_list_prod, List.map_ofFn, indexedWordProduct, word, f, Function.comp_def, mul_assoc]
  refine ⟨γ.cast rfl hend, ?_, hrange⟩
  change PathMetricBound γ (L * 2 ^ m) (κ * 2 ^ m)
  simpa only [word, List.length_ofFn] using hbound

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_AccessibleWordPaths
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.basisDynkinParameter_zero _root_.OAI.PolycyclicRecognition.dynkinRightTranslation_apply _root_.OAI.PolycyclicRecognition.dynkinRightTranslation_symm_apply _root_.OAI.PolycyclicRecognition.exponentialHomOfDynkin_apply_exp _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual paths to compact successful polynomial images -/

noncomputable section

namespace PolycyclicRecognition

open Module Set Metric

/-- The successful parameter witnesses give paths to every point of the
actual rescaled exponential image. No inverse to the polynomial endpoint map
is chosen and no extra good-sheet hypothesis is introduced. -/
theorem accessible_word_paths
    {L N G I : Type} [LieRing L] [LieAlgebra ℝ L] [Group N] [Group G]
    [PseudoMetricSpace G] [IsTopologicalGroup G] {n m c : ℕ}
    (basis : Basis (Fin n) ℝ L) (Exp : L → N) (hzero : Exp 0 = 1)
    (a : DynkinCoefficients c 2)
    (hm : ∀ u v, Exp (finiteDynkinPolynomial a ![u, v]) = Exp u * Exp v)
    (X : I → L) (s : I → ℝ) (r : ℝ) (letters : Fin m → I)
    (ι : N →* G) (hinj : Function.Injective ι) (x d₀ : G)
    (A : Set N) (S : Set G) (n₀ : N) (hn₀ : n₀ ∈ A)
    (sample : ℕ → ℝ → N) (hsub : ∀ j u v, sample j u * (sample j v)⁻¹ = sample j (u - v))
    (hsample : ∀ j : Fin m, ∀ u, sample j.val u =
      Exp (u • (Real.exp (r * s (letters j)) • X (letters j))))
    (d : Fin m → ℝ → G) (hd : ∀ i, Continuous (d i)) (hd₀ : ∀ i, d i 0 = 1)
    (hf : ∀ i : Fin m, Continuous (fun t => ι (sample i.val t)))
    (hf₀ : ∀ i : Fin m, ι (sample i.val 0) = 1)
    {speed error ρ : ℝ} (hspeed : 0 ≤ speed) (herror : 0 ≤ error)
    (hbase : ∀ n ∈ A, x * ι n * d₀ ∈ S)
    (hstep : ∀ n ∈ A, ∀ i : Fin m, ∀ b : ℝ, |b| ≤ 2 * ρ → n * sample i.val b ∈ A →
      PathMetricBound (supportVisitPath (d i) (hd i) (hd₀ i)
        (fun t => ι (sample i.val t)) (hf i) (hf₀ i) (x * ι n) d₀ r b) speed error ∧
      ∀ t, supportVisitPath (d i) (hd i) (hd₀ i)
        (fun t => ι (sample i.val t)) (hf i) (hf₀ i) (x * ι n) d₀ r b t ∈ S)
    (C : Set (Fin n → ℝ))
    (hC : ∀ y ∈ C, ∃ t ∈ closedBall (0 : Fin (m + m) → ℝ) ρ,
      SwitchSuccessful (fun _ => A) 0 m n₀ (sampledSwitchParameters sample m t) ∧
      differenceAmplitudeWordEndpoint a letters
        (basisBracket basis, fun i => basis.equivFun (Real.exp (r * s i) • X i)) t = y) :
    ∀ y ∈ C, ∃ γ : Path (x * ι n₀ * d₀)
      (x * ι (n₀ * Exp (basis.equivFun.symm y)) * d₀),
      PathMetricBound γ (speed * 2 ^ m) (error * 2 ^ m) ∧ ∀ u, γ u ∈ S := by
  intro y hy
  obtain ⟨t, ht, hs, he⟩ := hC y hy
  obtain ⟨γ, hγ, hS⟩ := successful_sample_path ι x d₀ A S m sample hsub d hd hd₀ hf hf₀
    r hspeed herror hbase hstep hinj n₀ hn₀ t (by simpa using ht) hs
  have hend : switchEndpoint m n₀ (sampledSwitchParameters sample m t) =
      n₀ * Exp (basis.equivFun.symm y) := by
    rw [sampled_rescaled_endpoint_eq basis Exp hzero a hm X s r letters sample hsub hsample, he]
  refine ⟨γ.cast rfl (by rw [hend]), ?_, hS⟩
  exact hγ

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

/-- An entire path over a prescribed profile image lies over its translated
image when centered at its actual start, with the same explicit error. -/
theorem centered_path_height_bound
    {X : Type} [TopologicalSpace X] {a b : X} (γ : Path a b) (J : X → W)
    (center w₀ : W) (E : Set W) (r B B₀ : ℝ)
    (hstart : ‖J a - center - r • w₀‖ ≤ B₀)
    (hpath : ∀ t, ∃ w ∈ E, ‖J (γ t) - center - r • w‖ ≤ B) :
    ∀ t, ∃ w ∈ (fun z => z - w₀) '' E, ‖J (γ t) - J a - r • w‖ ≤ B + B₀ := by
  intro t
  obtain ⟨w, hw, hh⟩ := hpath t
  exact ⟨w - w₀, ⟨w, hw, rfl⟩, norm_centered_sub_smul_le hh hstart⟩

end PolycyclicRecognition

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_SupportVisitImage
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Image control on a visit between two good sheets

Only the outward and return sheets require a prescribed profile. The short
root switch is controlled from its first endpoint by Lipschitz continuity.
-/

noncomputable section

namespace PolycyclicRecognition

open Set
open scoped NNReal

variable {G W : Type} [Group G] [PseudoMetricSpace G] [IsTopologicalGroup G]
  [IsIsometricSMul G G] [NormedAddCommGroup W] [NormedSpace ℝ W]

omit [IsIsometricSMul G G] in
/-- An arbitrary Lipschitz observable has controlled image on the whole
visit once both endpoint sheets have controlled images along the support leg. -/
theorem supportVisitPath_image_bound
    (d : ℝ → G) (hd : Continuous d) (hzero : d 0 = 1)
    (f : ℝ → G) (hf : Continuous f) (hf₀ : f 0 = 1)
    (J : G → W) {K : ℝ≥0} (hJ : LipschitzWith K J)
    (n d₀ : G) (r b : ℝ) (center : W) (E : Set W) {B κ : ℝ}
    (hκ : 0 ≤ κ)
    (hout : ∀ t : unitInterval, ∃ w ∈ E,
      ‖J ((n * d₀) * d (r * t)) - center - r • w‖ ≤ B)
    (hback : ∀ t : unitInterval, ∃ w ∈ E,
      ‖J ((n * f b * d₀) * d (r * t)) - center - r • w‖ ≤ B)
    (hswitch : ∀ t : unitInterval,
      dist (n * f ((t : ℝ) * b) * (d₀ * d r)) ((n * d₀) * d r) ≤ κ) :
    ∀ t, ∃ w ∈ E,
      ‖J (supportVisitPath d hd hzero f hf hf₀ n d₀ r b t) - center - r • w‖ ≤
        B + K * κ := by
  let S := {g : G | ∃ w ∈ E, ‖J g - center - r • w‖ ≤ B + K * κ}
  have hsmall : 0 ≤ (K : ℝ) * κ := mul_nonneg K.coe_nonneg hκ
  have hp₀ : ∀ t, flowPath d hd hzero (n * d₀) r t ∈ S := by
    intro t
    obtain ⟨w, hw, hh⟩ := hout t
    exact ⟨w, hw, hh.trans (le_add_of_nonneg_right hsmall)⟩
  have hp₁ : ∀ t, (flowPath d hd hzero (n * f b * d₀) r).symm t ∈ S := by
    intro t
    obtain ⟨w, hw, hh⟩ := hback (unitInterval.symm t)
    exact ⟨w, hw, hh.trans (le_add_of_nonneg_right hsmall)⟩
  let q : Path ((n * d₀) * d r) ((n * f b * d₀) * d r) := {
    toFun := fun t => n * f ((t : ℝ) * b) * (d₀ * d r)
    continuous_toFun := (continuous_const.mul
      (hf.comp (continuous_subtype_val.mul continuous_const))).mul continuous_const
    source' := by simp [hf₀, mul_assoc]
    target' := by simp [mul_assoc] }
  apply path_trans_range_mem (q := (flowPath d hd hzero (n * f b * d₀) r).symm)
    (path_trans_range_mem (q := q) hp₀ ?_) hp₁
  intro t
  obtain ⟨w, hw, hh⟩ := hout 1
  refine ⟨w, hw, ?_⟩
  have hdist := (hJ.dist_le_mul _ _).trans
    (mul_le_mul_of_nonneg_left (hswitch t) K.coe_nonneg)
  have he : J (n * f ((t : ℝ) * b) * (d₀ * d r)) - center - r • w =
      (J (n * f ((t : ℝ) * b) * (d₀ * d r)) - J ((n * d₀) * d r)) +
        (J ((n * d₀) * d r) - center - r • w) := by abel
  change ‖J (n * f ((t : ℝ) * b) * (d₀ * d r)) - center - r • w‖ ≤ _
  rw [he]
  have hh' : ‖J ((n * d₀) * d r) - center - r • w‖ ≤ B := by simpa using hh
  calc
    _ ≤ ‖J (n * f ((t : ℝ) * b) * (d₀ * d r)) - J ((n * d₀) * d r)‖ +
        ‖J ((n * d₀) * d r) - center - r • w‖ := norm_add_le _ _
    _ ≤ K * κ + B := add_le_add (by simpa only [dist_eq_norm] using hdist) hh'
    _ = _ := add_comm _ _

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_AccessibleProfilePaths
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Successful endpoint paths with their actual relative profile bounds -/

noncomputable section

namespace PolycyclicRecognition

open Module Set Metric
open scoped NNReal

/-- Successful parameters supply paths to every retained polynomial endpoint.
The two good-sheet leg estimates and the short switch estimate control the
whole image; subtracting the actual starting image costs its profile error. -/
theorem accessible_word_profile_paths
    {L N G I W : Type} [LieRing L] [LieAlgebra ℝ L] [Group N] [Group G]
    [PseudoMetricSpace G] [IsTopologicalGroup G]
    [NormedAddCommGroup W] [NormedSpace ℝ W] {n m c : ℕ}
    (basis : Basis (Fin n) ℝ L) (Exp : L → N) (hzero : Exp 0 = 1)
    (a : DynkinCoefficients c 2)
    (hm : ∀ u v, Exp (finiteDynkinPolynomial a ![u, v]) = Exp u * Exp v)
    (X : I → L) (s : I → ℝ) (r : ℝ) (letters : Fin m → I)
    (ι : N →* G) (hinj : Function.Injective ι) (x d₀ : G)
    (A : Set N) (n₀ : N) (hn₀ : n₀ ∈ A)
    (sample : ℕ → ℝ → N) (hsub : ∀ j u v, sample j u * (sample j v)⁻¹ = sample j (u - v))
    (hsample : ∀ j : Fin m, ∀ u, sample j.val u =
      Exp (u • (Real.exp (r * s (letters j)) • X (letters j))))
    (d : Fin m → ℝ → G) (hd : ∀ i, Continuous (d i)) (hd₀ : ∀ i, d i 0 = 1)
    (hf : ∀ i : Fin m, Continuous (fun t => ι (sample i.val t)))
    (hf₀ : ∀ i : Fin m, ι (sample i.val 0) = 1)
    (J : G → W) {K : ℝ≥0} (hJ : LipschitzWith K J)
    (center w₀ : W) (E : Set W)
    {speed error ρ B B₀ δ : ℝ} (hspeed : 0 ≤ speed) (herror : 0 ≤ error) (hδ : 0 ≤ δ)
    (hbase : ∀ n ∈ A, ∃ w ∈ E, ‖J (x * ι n * d₀) - center - r • w‖ ≤ B)
    (hstart : ‖J (x * ι n₀ * d₀) - center - r • w₀‖ ≤ B₀)
    (hleg : ∀ n ∈ A, ∀ i : Fin m, ∀ t : unitInterval,
      ∃ w ∈ E, ‖J ((x * ι n * d₀) * d i (r * t)) - center - r • w‖ ≤ B)
    (hmetric : ∀ n ∈ A, ∀ i : Fin m, ∀ b : ℝ, |b| ≤ 2 * ρ → n * sample i.val b ∈ A →
      PathMetricBound (supportVisitPath (d i) (hd i) (hd₀ i)
        (fun t => ι (sample i.val t)) (hf i) (hf₀ i) (x * ι n) d₀ r b) speed error)
    (hswitch : ∀ n ∈ A, ∀ i : Fin m, ∀ b : ℝ, |b| ≤ 2 * ρ → ∀ t : unitInterval,
      dist ((x * ι n) * ι (sample i.val ((t : ℝ) * b)) * (d₀ * d i r))
        ((x * ι n * d₀) * d i r) ≤ δ)
    (C : Set (Fin n → ℝ))
    (hC : ∀ y ∈ C, ∃ t ∈ closedBall (0 : Fin (m + m) → ℝ) ρ,
      SwitchSuccessful (fun _ => A) 0 m n₀ (sampledSwitchParameters sample m t) ∧
      differenceAmplitudeWordEndpoint a letters
        (basisBracket basis, fun i => basis.equivFun (Real.exp (r * s i) • X i)) t = y) :
    ∀ y ∈ C, ∃ γ : Path (x * ι n₀ * d₀)
      (x * ι (n₀ * Exp (basis.equivFun.symm y)) * d₀),
      PathMetricBound γ (speed * 2 ^ m) (error * 2 ^ m) ∧
      ∀ u, ∃ w ∈ (fun z => z - w₀) '' E,
        ‖J (γ u) - J (x * ι n₀ * d₀) - r • w‖ ≤ B + K * δ + B₀ := by
  let S := {g : G | ∃ w ∈ E, ‖J g - center - r • w‖ ≤ B + K * δ}
  have hnonneg : 0 ≤ (K : ℝ) * δ := mul_nonneg K.coe_nonneg hδ
  have hbase' : ∀ n ∈ A, x * ι n * d₀ ∈ S := by
    intro n hn
    obtain ⟨w, hw, hh⟩ := hbase n hn
    exact ⟨w, hw, hh.trans (le_add_of_nonneg_right hnonneg)⟩
  have hstep : ∀ n ∈ A, ∀ i : Fin m, ∀ b : ℝ, |b| ≤ 2 * ρ → n * sample i.val b ∈ A →
      PathMetricBound (supportVisitPath (d i) (hd i) (hd₀ i)
        (fun t => ι (sample i.val t)) (hf i) (hf₀ i) (x * ι n) d₀ r b) speed error ∧
      ∀ t, supportVisitPath (d i) (hd i) (hd₀ i)
        (fun t => ι (sample i.val t)) (hf i) (hf₀ i) (x * ι n) d₀ r b t ∈ S := by
    intro n hn i b hb hn'
    refine ⟨hmetric n hn i b hb hn', ?_⟩
    apply supportVisitPath_image_bound (d i) (hd i) (hd₀ i)
      (fun t => ι (sample i.val t)) (hf i) (hf₀ i) J hJ
      (x * ι n) d₀ r b center E hδ (hleg n hn i) ?_ (hswitch n hn i b hb)
    simpa only [map_mul, mul_assoc] using hleg (n * sample i.val b) hn' i
  intro y hy
  obtain ⟨γ, hγ, hγS⟩ := accessible_word_paths basis Exp hzero a hm X s r letters
    ι hinj x d₀ A S n₀ hn₀ sample hsub hsample d hd hd₀ hf hf₀
    hspeed herror hbase' hstep C hC y hy
  exact ⟨γ, hγ, centered_path_height_bound γ J center w₀ E r (B + K * δ) B₀ hstart hγS⟩

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_NormalizedPairPacking
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.inversePairCoupling_finiteOnCompacts _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.normalizedPairAction _root_.OAI.PolycyclicRecognition.normalizedPairContinuousAction _root_.OAI.PolycyclicRecognition.normalizedPair_polishSpace _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.normalizedPair_smul_fst _root_.OAI.PolycyclicRecognition.normalizedPair_smul_snd _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Separation and paths under an actual normalized pair -/

noncomputable section

namespace PolycyclicRecognition

open Metric
open scoped NNReal

variable {G : Type} [Group G] [MetricSpace G] {Λ : ℝ≥0}

/-- The lower metric inequality turns this fixed source separation into
unit separation in the image. -/
theorem normalizedPair_image_dist_gt_one (p : NormalizedPair G Λ)
    (hΛ : 0 < (Λ : ℝ)) {x y : G}
    (hxy : (Λ : ℝ) * ((Λ : ℝ) + 1) < dist x y) :
    1 < dist (p.val.1 x) (p.val.1 y) := by
  have hi : 0 < (Λ : ℝ)⁻¹ := inv_pos.mpr hΛ
  calc
    1 = (Λ : ℝ)⁻¹ * ((Λ : ℝ) * ((Λ : ℝ) + 1)) - Λ := by field_simp <;> ring
    _ < (Λ : ℝ)⁻¹ * dist x y - Λ := sub_lt_sub_right (mul_lt_mul_of_pos_left hxy hi) _
    _ ≤ _ := p.property.1.2.2.1 x y

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_BasedImagePaths
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.inversePairCoupling_finiteOnCompacts _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.normalizedPairAction _root_.OAI.PolycyclicRecognition.normalizedPairContinuousAction _root_.OAI.PolycyclicRecognition.normalizedPair_polishSpace _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
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

omit [IsTopologicalGroup G] in
/-- A based image of a separated source set has the same cardinality and
unit-separated points, by the actual lower quasi-isometry inequality. -/
theorem basedImage_separated_card [DecidableEq G] {Λ : ℝ≥0} (p : NormalizedPair G Λ)
    (hΛ : 0 < (Λ : ℝ)) (a : G) (s : Finset G)
    (hsep : ∀ x ∈ s, ∀ y ∈ s, x ≠ y → (Λ : ℝ) * ((Λ : ℝ) + 1) < dist x y) :
    (s.image (basedImage p.val.1 a)).card = s.card ∧
      ∀ x ∈ s.image (basedImage p.val.1 a),
        ∀ y ∈ s.image (basedImage p.val.1 a), x ≠ y → 1 ≤ dist x y := by
  classical
  have hd (x y : G) (hx : x ∈ s) (hy : y ∈ s) (hne : x ≠ y) :
      1 < dist (basedImage p.val.1 a x) (basedImage p.val.1 a y) := by
    rw [basedImage_dist]
    exact normalizedPair_image_dist_gt_one p hΛ (hsep x hx y hy hne)
  constructor
  · apply Finset.card_image_iff.mpr
    intro x hx y hy he
    by_contra hne
    have hh := hd x y hx hy hne
    rw [he, dist_self] at hh
    linarith
  · intro x hx y hy hne
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hy
    exact (hd u v hu hv (fun he => hne (congrArg _ he))).le

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_CoarsePackingAsymptotics
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial losses and logarithmic errors in path packing -/

namespace PolycyclicRecognition

open Filter
open scoped Topology ENNReal

/-- Every fixed affine function of the logarithmic path error is sublinear. -/
theorem eventually_logarithmic_error_le (a b : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ r : ℝ in atTop, a * (1 + Real.log (2 + r)) + b ≤ ε * r := by
  have hadd : Tendsto (fun r : ℝ => 2 + r) atTop atTop := by
    apply tendsto_atTop.mpr
    intro x
    filter_upwards [eventually_ge_atTop (x - 2)] with r hr
    linarith
  have hlog : Tendsto (fun r : ℝ => Real.log (2 + r) / r) atTop (𝓝 0) := by
    have h := (Real.tendsto_pow_log_div_mul_add_atTop 1 (-2) 1 one_ne_zero).comp hadd
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    funext r
    simp only [Function.comp_apply, pow_one, one_mul]
    congr 1
    ring
  have hconst : Tendsto (fun r : ℝ => (a + b) / r) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  have hlim : Tendsto (fun r : ℝ => (a * (1 + Real.log (2 + r)) + b) / r)
      atTop (𝓝 0) := by
    have h := (hlog.const_mul a).add hconst
    convert h using 1
    · funext r; ring
    · simp
  filter_upwards [(tendsto_order.mp hlim).2 ε hε, eventually_gt_atTop (0 : ℝ)] with r hr hr0
  exact ((div_lt_iff₀ hr0).mp hr).le

/-- The path-word subdivision prefactor is bounded by one fixed quadratic. -/
theorem coarse_path_word_prefactor_le {A r : ℝ} (hA : 0 ≤ A) (hr : 1 ≤ r) :
    3 + (A * r + 1) * (A * (1 + Real.log (2 + r)) + 2) ≤
      (3 + (A + 1) * (3 * A + 2)) * (1 + r) ^ 2 := by
  have hr0 : 0 ≤ r := by linarith
  have hlog : 1 + Real.log (2 + r) ≤ 3 * r := by
    have h := Real.log_le_sub_one_of_pos (by linarith : 0 < 2 + r)
    linarith
  have h1 : A * r + 1 ≤ (A + 1) * (1 + r) := by nlinarith
  have h2 : A * (1 + Real.log (2 + r)) + 2 ≤ (3 * A + 2) * (1 + r) := by
    have h := mul_le_mul_of_nonneg_left hlog hA
    nlinarith
  have hlog0 : 0 ≤ 1 + Real.log (2 + r) := by
    have hh := Real.log_nonneg (by linarith : 1 ≤ 2 + r)
    linarith
  have hm := mul_le_mul h1 h2 (by positivity : 0 ≤ A * (1 + Real.log (2 + r)) + 2)
    (by positivity : 0 ≤ (A + 1) * (1 + r))
  calc
    _ ≤ 3 + (A + 1) * (1 + r) * ((3 * A + 2) * (1 + r)) := add_le_add le_rfl hm
    _ ≤ _ := by nlinarith [sq_nonneg r]

end PolycyclicRecognition

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_CoordinateChartSampling
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The coordinate maps of the actual two-factor chart samples -/

noncomputable section

namespace PolycyclicRecognition

open Module
open scoped NNReal

/-- A Lie-algebra identification transports the same binary Dynkin formula. -/
theorem model_binary_dynkin
    {L L' N : Type} [LieRing L] [LieAlgebra ℝ L]
    [LieRing L'] [LieAlgebra ℝ L'] [Group N]
    (e : L ≃ₗ⁅ℝ⁆ L') (Exp : L' → N) {c : ℕ} (a : DynkinCoefficients c 2)
    (hm : ∀ x y, Exp (finiteDynkinPolynomial a ![x, y]) = Exp x * Exp y)
    (x y : L) :
    Exp (e (finiteDynkinPolynomial a ![x, y])) = Exp (e x) * Exp (e y) := by
  have he := congrArg Exp (finiteDynkinPolynomial_map e.toLieHom a ![x, y])
  have hv : (fun i => e.toLieHom (![x, y] i)) = ![e x, e y] := by
    funext i
    fin_cases i <;> rfl
  rw [hv] at he
  exact he.trans (hm (e x) (e y))

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_MeasurePacking
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Counting separated endpoints using Haar volume

Disjoint fixed-radius balls around separated endpoints have the same positive
Haar mass. A polynomial-volume region containing their thickening therefore
gives a polynomial cardinal bound. This is the counting step of the path
packing lemma, separated from its Lie-coordinate estimate.
-/

namespace PolycyclicRecognition

open MeasureTheory MeasureTheory.Measure Metric Set
open scoped ENNReal

variable {G : Type} [Group G] [MetricSpace G] [MeasurableSpace G]
  [BorelSpace G] [MeasurableMul G] [IsIsometricSMul G G]

/-- The same maximal-packing argument applies to arbitrary endpoint sets. A
bound on their finite separated subsets already supplies a finite net; no
measurability or compactness of the endpoint set is needed. -/
theorem finite_separated_cover_set_of_bound {X : Type} [PseudoMetricSpace X]
    (S : Set X) {r : ℝ} (hr : 0 ≤ r) (N : ℕ)
    (hbound : ∀ t : Finset X, (↑t : Set X) ⊆ S →
      (∀ x ∈ t, ∀ y ∈ t, x ≠ y → r < dist x y) → t.card ≤ N) :
    ∃ t : Finset X, (↑t : Set X) ⊆ S ∧
      (∀ x ∈ t, ∀ y ∈ t, x ≠ y → r < dist x y) ∧ t.card ≤ N ∧
      ∀ x ∈ S, ∃ y ∈ t, dist x y ≤ r := by
  classical
  let P (k : ℕ) := ∃ t : Finset X, (↑t : Set X) ⊆ S ∧
    (∀ x ∈ t, ∀ y ∈ t, x ≠ y → r < dist x y) ∧ t.card = k
  have hP0 : P 0 := ⟨∅, by simp, by simp, by simp⟩
  obtain ⟨t, hts, hsep, hcard⟩ := Nat.findGreatest_spec (Nat.zero_le N) hP0
  have hmax (u : Finset X) (hu : (↑u : Set X) ⊆ S)
      (husep : ∀ x ∈ u, ∀ y ∈ u, x ≠ y → r < dist x y) : u.card ≤ t.card := by
    rw [hcard]
    exact Nat.le_findGreatest (hbound u hu husep) ⟨u, hu, husep, rfl⟩
  refine ⟨t, hts, hsep, hbound t hts hsep, ?_⟩
  intro x hx
  by_contra hno
  have hfar : ∀ y ∈ t, r < dist x y := by
    intro y hy
    exact lt_of_not_ge (fun h => hno ⟨y, hy, h⟩)
  have hxt : x ∉ t := by
    intro hxt
    exact (not_lt_of_ge hr) (by simpa only [dist_self] using hfar x hxt)
  have hins : (↑(insert x t) : Set X) ⊆ S := by
    intro y hy
    rcases Finset.mem_insert.mp hy with hxy | hyt
    · exact hxy ▸ hx
    · exact hts hyt
  have hsepins : ∀ a ∈ insert x t, ∀ b ∈ insert x t, a ≠ b → r < dist a b := by
    intro a ha b hb hab
    rcases Finset.mem_insert.mp ha with hax | hat
    · subst a
      rcases Finset.mem_insert.mp hb with hbx | hbt
      · exact (hab hbx.symm).elim
      · exact hfar b hbt
    · rcases Finset.mem_insert.mp hb with hbx | hbt
      · subst b
        simpa only [dist_comm] using hfar a hat
      · exact hsep a hat b hbt hab
  have h := hmax (insert x t) hins hsepins
  rw [Finset.card_insert_of_notMem hxt] at h
  omega

end PolycyclicRecognition

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_LowerPacking
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Lower packing bounds from Haar volume

A totally bounded endpoint set has a finite separated net. Its volume is
at most the cardinality of that net times the mass of a fixed-radius ball.
This is the lower packing estimate used after stationary mesh selection.
-/

noncomputable section

open Metric Set MeasureTheory
open scoped ENNReal

namespace PolycyclicRecognition

/-- A totally bounded set admits a finite separated net with its centers
inside the set. The set itself need not be closed or measurable. -/
theorem exists_separated_net_of_totallyBounded
    {X : Type} [PseudoMetricSpace X] {S : Set X} (hS : TotallyBounded S)
    {r : ℝ} (hr : 0 < r) :
    ∃ t : Finset X, (↑t : Set X) ⊆ S ∧
      (∀ x ∈ t, ∀ y ∈ t, x ≠ y → r < dist x y) ∧
      ∀ x ∈ S, ∃ y ∈ t, dist x y ≤ r := by
  classical
  obtain ⟨U, _hUS, hUfin, hUcover⟩ := finite_approx_of_totallyBounded hS (r / 3) (by positivity)
  let u := hUfin.toFinset
  have hbound (t : Finset X) (ht : (↑t : Set X) ⊆ S)
      (hsep : ∀ x ∈ t, ∀ y ∈ t, x ≠ y → r < dist x y) : t.card ≤ u.card := by
    have hchoice (x : {x // x ∈ t}) : ∃ y : {y // y ∈ u}, dist x.val y.val < r / 3 := by
      obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.mp (hUcover (ht x.property))
      exact ⟨⟨y, hUfin.mem_toFinset.mpr hy⟩, Metric.mem_ball.mp hxy⟩
    choose c hc using hchoice
    have hinj : Function.Injective c := by
      intro x y hxy
      apply Subtype.ext
      by_contra hne
      have hdist : dist x.val y.val < r := by
        calc
          dist x.val y.val ≤ dist x.val (c x).val + dist (c x).val y.val := dist_triangle _ _ _
          _ = dist x.val (c x).val + dist y.val (c y).val := by rw [hxy, dist_comm (c y).val]
          _ < r := by linarith [hc x, hc y]
      exact (not_lt_of_ge hdist.le) (hsep x.val x.property y.val y.property hne)
    simpa only [Fintype.card_coe] using Fintype.card_le_of_injective c hinj
  obtain ⟨t, ht, hsep, _hcard, hcover⟩ :=
    finite_separated_cover_set_of_bound S hr.le u.card hbound
  exact ⟨t, ht, hsep, hcover⟩

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_FixedSlicePacking
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Lower packing on a fixed Cartan slice

A finite net in the ambient group pulls back to a cover of the nilpotent
parameter set. Conjugation preserving Haar makes the mass of every pulled-back
ball independent of the slice position. This is the fixed-position part of
the manuscript's lower packing argument, with no assumption on an image's
absolute continuity or multiplicity.
-/

noncomputable section

namespace PolycyclicRecognition

open MeasureTheory Metric Set
open scoped ENNReal

/-- A net of an image gives a lower cardinality bound whenever the preimage
of each covering ball has uniformly bounded mass. The source set need not be
measurable. -/
theorem exists_separated_image_net_volume_bound
    {N G : Type} [MeasurableSpace N] [PseudoMetricSpace G]
    (μ : Measure N) (f : N → G) {S : Set N}
    (hS : TotallyBounded (f '' S)) {r : ℝ} (hr : 0 < r) (C : ℝ≥0∞)
    (hball : ∀ y ∈ f '' S, μ (f ⁻¹' closedBall y r) ≤ C) :
    ∃ t : Finset G, (↑t : Set G) ⊆ f '' S ∧
      (∀ x ∈ t, ∀ y ∈ t, x ≠ y → r < dist x y) ∧
      μ S ≤ (t.card : ℝ≥0∞) * C := by
  classical
  obtain ⟨t, ht, hsep, hcover⟩ := exists_separated_net_of_totallyBounded hS hr
  refine ⟨t, ht, hsep, ?_⟩
  calc
    μ S ≤ μ (⋃ y ∈ t, f ⁻¹' closedBall y r) := measure_mono (by
      intro x hx
      obtain ⟨y, hy, hxy⟩ := hcover (f x) ⟨x, hx, rfl⟩
      exact mem_iUnion₂.mpr ⟨y, hy, hxy⟩)
    _ ≤ ∑ y ∈ t, μ (f ⁻¹' closedBall y r) := measure_biUnion_finset_le _ _
    _ ≤ ∑ _y ∈ t, C := Finset.sum_le_sum (fun y hy => hball y (ht hy))
    _ = (t.card : ℝ≥0∞) * C := by simp [nsmul_eq_mul]

variable {N D G : Type} [Group N] [Group D] [Group G]
  [MeasurableSpace N] [MetricSpace G] [IsIsometricSMul G G]
  (ι : N →* G) (κ : D →* G) (φ : D →* MulAut N)

omit [MeasurableSpace N] in
/-- Compute the entire fiber of an ambient ball on a fixed slice. The
identity-neighborhood in the nilpotent group is conjugated, then translated. -/
theorem fixedSlice_ball_preimage
    (hconj : ∀ d n, ι (φ d n) = κ d * ι n * (κ d)⁻¹)
    (x : G) (d : D) (v : N) (r : ℝ) :
    (fun u : N => x * ι u * κ d) ⁻¹' closedBall (x * ι v * κ d) r =
      (fun n => v * φ d n) '' (ι ⁻¹' closedBall (1 : G) r) := by
  ext u
  constructor
  · intro hu
    let n := φ d⁻¹ (v⁻¹ * u)
    have hn : φ d n = v⁻¹ * u := by simp [n]
    refine ⟨n, ?_, ?_⟩
    · change dist (ι n) 1 ≤ r
      have he : (x * ι v * κ d) * ι n = x * ι u * κ d := by
        have hc := hconj d n
        rw [hn] at hc
        have hh : κ d * ι n = ι (v⁻¹ * u) * κ d := by
          rw [hc]
          simp only [mul_assoc, inv_mul_cancel, mul_one]
        calc
          (x * ι v * κ d) * ι n = x * ι v * (κ d * ι n) := by simp only [mul_assoc]
          _ = x * ι v * (ι (v⁻¹ * u) * κ d) := by rw [hh]
          _ = x * ι u * κ d := by simp [mul_assoc]
      have hd := dist_mul_left (x * ι v * κ d) (ι n) 1
      rw [he, mul_one] at hd
      exact hd ▸ hu
    · simp [hn]
  · rintro ⟨n, hn, rfl⟩
    change dist (x * ι (v * φ d n) * κ d) (x * ι v * κ d) ≤ r
    rw [map_mul, hconj]
    have he : x * (ι v * (κ d * ι n * (κ d)⁻¹)) * κ d =
        (x * ι v * κ d) * ι n := by group
    rw [he]
    calc
      dist ((x * ι v * κ d) * ι n) (x * ι v * κ d) = dist (ι n) 1 := by
        simpa only [mul_one] using dist_mul_left (x * ι v * κ d) (ι n) 1
      _ ≤ r := hn

variable [MeasurableMul N]

/-- Haar mass of a slice ball depends only on its radius. In particular it
does not grow with the Cartan position or the center of the ball. -/
theorem fixedSlice_ball_measure
    (μ : Measure N) [μ.IsMulLeftInvariant]
    (hφ : ∀ d, MeasurePreserving (φ d) μ μ)
    (hconj : ∀ d n, ι (φ d n) = κ d * ι n * (κ d)⁻¹)
    (x : G) (d : D) (v : N) (r : ℝ) :
    μ ((fun u : N => x * ι u * κ d) ⁻¹' closedBall (x * ι v * κ d) r) =
      μ (ι ⁻¹' closedBall (1 : G) r) := by
  rw [fixedSlice_ball_preimage ι κ φ hconj]
  let e : N ≃ᵐ N :=
    { toEquiv :=
        { toFun := fun n => v * φ d n
          invFun := fun n => φ d⁻¹ (v⁻¹ * n)
          left_inv := by intro n; simp
          right_inv := by intro n; simp }
      measurable_toFun := (measurable_const_mul v).comp (hφ d).measurable
      measurable_invFun := (hφ d⁻¹).measurable.comp (measurable_const_mul v⁻¹) }
  have hmp : MeasurePreserving e μ μ := (measurePreserving_mul_left μ v).comp (hφ d)
  change μ (e '' _) = _
  have hm := hmp.measure_preimage_equiv (e '' (ι ⁻¹' closedBall (1 : G) r))
  rw [Set.preimage_image_eq _ e.injective] at hm
  exact hm.symm

/-- The fixed-position lower packing estimate. The only volume constant is
the Haar mass of the identity ball pulled back to the nilpotent subgroup. -/
theorem exists_fixedSlice_separated_net
    (μ : Measure N) [μ.IsMulLeftInvariant]
    (hφ : ∀ d, MeasurePreserving (φ d) μ μ)
    (hconj : ∀ d n, ι (φ d n) = κ d * ι n * (κ d)⁻¹)
    (x : G) (d : D) (S : Set N)
    (hS : TotallyBounded ((fun u : N => x * ι u * κ d) '' S))
    {r : ℝ} (hr : 0 < r) :
    ∃ t : Finset G, (↑t : Set G) ⊆ (fun u : N => x * ι u * κ d) '' S ∧
      (∀ a ∈ t, ∀ b ∈ t, a ≠ b → r < dist a b) ∧
      μ S ≤ (t.card : ℝ≥0∞) * μ (ι ⁻¹' closedBall (1 : G) r) := by
  apply exists_separated_image_net_volume_bound μ _ hS hr
  rintro y ⟨v, _, rfl⟩
  exact (fixedSlice_ball_measure ι κ φ μ hφ hconj x d v r).le

variable [TopologicalSpace N] [ContinuousMul G]

omit [IsIsometricSMul G G] [MeasurableMul N] [ContinuousMul G] in
/-- A closed subgroup realization gives a finite packing constant at every
fixed radius, since the ambient metric is proper. -/
theorem fixedSlice_packing_constant_lt_top
    [ProperSpace G] (μ : Measure N) [IsFiniteMeasureOnCompacts μ]
    (hι : Topology.IsClosedEmbedding ι) (r : ℝ) :
    μ (ι ⁻¹' closedBall (1 : G) r) < ⊤ :=
  (hι.isProperMap.isCompact_preimage (isCompact_closedBall 1 r)).measure_lt_top

/-- Any subset of a compact parameter set satisfies the fixed-slice lower
packing bound. Its image need not be measurable. -/
theorem exists_fixedSlice_separated_net_of_compact
    (μ : Measure N) [μ.IsMulLeftInvariant]
    (hφ : ∀ d, MeasurePreserving (φ d) μ μ)
    (hconj : ∀ d n, ι (φ d n) = κ d * ι n * (κ d)⁻¹)
    (hι : Continuous ι) (x : G) (d : D) {K S : Set N}
    (hK : IsCompact K) (hS : S ⊆ K) {r : ℝ} (hr : 0 < r) :
    ∃ t : Finset G, (↑t : Set G) ⊆ (fun u : N => x * ι u * κ d) '' S ∧
      (∀ a ∈ t, ∀ b ∈ t, a ≠ b → r < dist a b) ∧
      μ S ≤ (t.card : ℝ≥0∞) * μ (ι ⁻¹' closedBall (1 : G) r) := by
  apply exists_fixedSlice_separated_net ι κ φ μ hφ hconj x d S
  · exact ((hK.image ((continuous_const.mul hι).mul continuous_const)).totallyBounded).subset
      (image_mono hS)
  · exact hr

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_SegmentProfileLegs
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # From a single good horizontal segment to every support leg -/

noncomputable section

namespace PolycyclicRecognition

open Filter Set
open scoped Topology

/-- Every shortened support leg lies in the same original horizontal
segment. In particular, one good profile controls all the chosen support
endpoints and the common pivot, without separate good sets for the letters. -/
theorem segment_profile_support_legs
    {L D N G W I : Type} [AddCommGroup L] [Module ℝ L]
    [Group D] [Group N] [Group G] [NormedAddCommGroup W] [NormedSpace ℝ W]
    (ExpD : L → D) (hzero : ExpD 0 = 1) (ι : N →* G) (κ : D →* G)
    (J : G → W) (x d₀ : G) (center : W) (A : Set N) (r T ε : ℝ)
    (hT : 0 ≤ T) (v : L) (θ : I → ℝ) (hθ : ∀ i, θ i ∈ Icc 0 T)
    (g : ℝ → W)
    (hgood : ∀ u ∈ A, ∀ t ∈ Icc (0 : ℝ) T,
      ‖J ((x * ι u * d₀) * κ (ExpD ((r * t) • v))) - center - r • g t‖ ≤ ε) :
    (∀ u ∈ A, ‖J (x * ι u * d₀) - center - r • g 0‖ ≤ ε) ∧
    ∀ u ∈ A, ∀ i, ∀ t : unitInterval,
      ∃ w ∈ g '' Icc (0 : ℝ) T,
        ‖J ((x * ι u * d₀) * κ (ExpD ((r * t) • (θ i • v)))) - center - r • w‖ ≤ ε := by
  constructor
  · intro u hu
    simpa only [mul_zero, zero_smul, hzero, map_one, mul_one] using
      hgood u hu 0 ⟨le_rfl, hT⟩
  · intro u hu i t
    have ht : θ i * (t : ℝ) ∈ Icc (0 : ℝ) T := by
      refine ⟨mul_nonneg (hθ i).1 t.property.1, ?_⟩
      exact (mul_le_of_le_one_right (hθ i).1 t.property.2).trans (hθ i).2
    refine ⟨g (θ i * t), ⟨θ i * t, ht, rfl⟩, ?_⟩
    have he : (r * (t : ℝ)) • (θ i • v) = (r * (θ i * (t : ℝ))) • v := by
      rw [smul_smul]
      congr 1
      ring
    rw [he]
    exact hgood u hu _ ht

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_SegmentSupportTimes
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finite_templateSymmetryGroup _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteRootOffsetConeIndex _root_.OAI.PolycyclicRecognition.instFiniteSubtypeLinearEquivRealIdMemSubgroupLinearSupportSymmetryGroup _root_.OAI.PolycyclicRecognition.instNonemptyRootOffsetConeIndex _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.CartanWordModel.supportDatum_weight _root_.OAI.PolycyclicRecognition.SupportDatum.transport_weight_apply _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Prescribed endpoint times realizing the segment support exponents -/

noncomputable section

namespace PolycyclicRecognition.SupportDatum

open Set

variable {W I B : Type} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [Fintype I] [Fintype B] (D : SupportDatum W I B)

theorem segmentSupportTime_mem (v : W) {T : ℝ} (hT : 0 ≤ T) (i : I) :
    D.segmentSupportTime v T i ∈ Icc 0 T := by
  by_cases hi : 0 ≤ D.weight i v <;> simp [segmentSupportTime, hi, hT]

end PolycyclicRecognition.SupportDatum

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_SequenceAccessiblePaths
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Sublinear errors on accessible paths along profile sequences -/

noncomputable section

namespace PolycyclicRecognition

open Module Set Metric Filter
open scoped Topology NNReal

/-- The vanishing good-profile errors on all support legs give exactly the
relative height estimate required by the accessible-volume comparison.
Only successful endpoints are used; the submersive endpoint map is unchanged. -/
theorem sublinear_accessible_word_paths_sequence
    {L N G I W : Type} [LieRing L] [LieAlgebra ℝ L] [Group N] [Group G]
    [PseudoMetricSpace G] [IsTopologicalGroup G]
    [NormedAddCommGroup W] [NormedSpace ℝ W] {n m c : ℕ}
    (scale : ℕ → ℝ) (hscale : Tendsto scale atTop atTop)
    (basis : ℕ → Basis (Fin n) ℝ L) (Exp : L → N) (hzero : Exp 0 = 1)
    (a : DynkinCoefficients c 2)
    (hm : ∀ u v, Exp (finiteDynkinPolynomial a ![u, v]) = Exp u * Exp v)
    (X : I → L) (s : I → ℝ) (letters : Fin m → I)
    (ι : N →* G) (hinj : Function.Injective ι) (x d₀ : ℕ → G)
    (A : ℕ → Set N) (n₀ : ℕ → N) (hn₀ : ∀ r, n₀ r ∈ A r)
    (sample : ℕ → ℕ → ℝ → N)
    (hsub : ∀ r j u v, sample r j u * (sample r j v)⁻¹ = sample r j (u - v))
    (hsample : ∀ r, ∀ j : Fin m, ∀ u, sample r j.val u =
      Exp (u • (Real.exp (scale r * s (letters j)) • X (letters j))))
    (d : Fin m → ℝ → G) (hd : ∀ i, Continuous (d i)) (hd₀ : ∀ i, d i 0 = 1)
    (hf : ∀ r, ∀ i : Fin m, Continuous (fun t => ι (sample r i.val t)))
    (hf₀ : ∀ r, ∀ i : Fin m, ι (sample r i.val 0) = 1)
    (J : ℕ → G → W) {K : ℝ≥0} (hJ : ∀ r, LipschitzWith K (J r))
    (center : ℕ → W) (w₀ : W) (E : Set W)
    (ζ : ℕ → ℝ) (hζ : Tendsto ζ atTop (𝓝 0))
    {speed switchError ρ : ℝ} (hspeed : 0 ≤ speed) (hswitchError : 0 ≤ switchError)
    (hbase : ∀ η : ℝ, 0 < η → ∀ᶠ r in atTop, ∀ u ∈ A r,
      ∃ w ∈ E, ‖J r (x r * ι u * d₀ r) - center r - scale r • w‖ ≤ scale r * (ζ r + η))
    (hstart : ∀ η : ℝ, 0 < η → ∀ᶠ r in atTop,
      ‖J r (x r * ι (n₀ r) * d₀ r) - center r - scale r • w₀‖ ≤ scale r * (ζ r + η))
    (hleg : ∀ η : ℝ, 0 < η → ∀ᶠ r in atTop, ∀ u ∈ A r, ∀ i : Fin m,
      ∀ t : unitInterval, ∃ w ∈ E,
        ‖J r ((x r * ι u * d₀ r) * d i (scale r * t)) - center r - scale r • w‖ ≤ scale r * (ζ r + η))
    (hmetric : ∀ᶠ r in atTop, ∀ u ∈ A r, ∀ i : Fin m, ∀ b : ℝ,
      |b| ≤ 2 * ρ → u * sample r i.val b ∈ A r →
      PathMetricBound (supportVisitPath (d i) (hd i) (hd₀ i)
        (fun t => ι (sample r i.val t)) (hf r i) (hf₀ r i) (x r * ι u) (d₀ r) (scale r) b)
        (speed * scale r) (speed * (1 + Real.log (2 + scale r))))
    (hswitch : ∀ᶠ r in atTop, ∀ u ∈ A r, ∀ i : Fin m, ∀ b : ℝ,
      |b| ≤ 2 * ρ → ∀ t : unitInterval,
      dist ((x r * ι u) * ι (sample r i.val ((t : ℝ) * b)) * (d₀ r * d i (scale r)))
        ((x r * ι u * d₀ r) * d i (scale r)) ≤ switchError * (1 + Real.log (2 + scale r)))
    (C : ℕ → Set (Fin n → ℝ))
    (hC : ∀ᶠ r in atTop, ∀ y ∈ C r, ∃ t ∈ closedBall (0 : Fin (m + m) → ℝ) ρ,
      SwitchSuccessful (fun _ => A r) 0 m (n₀ r) (sampledSwitchParameters (sample r) m t) ∧
      differenceAmplitudeWordEndpoint a letters
        (basisBracket (basis r), fun i => (basis r).equivFun (Real.exp (scale r * s i) • X i)) t = y) :
    ∀ η : ℝ, 0 < η → ∀ᶠ r in atTop, ∀ y ∈ C r,
      ∃ γ : Path (x r * ι (n₀ r) * d₀ r)
        (x r * ι (n₀ r * Exp ((basis r).equivFun.symm y)) * d₀ r),
        PathMetricBound γ ((speed * 2 ^ m) * scale r)
          ((speed * 2 ^ m) * (1 + Real.log (2 + scale r))) ∧
        ∀ u, ∃ w ∈ (fun z => z - w₀) '' E,
          ‖J r (γ u) - J r (x r * ι (n₀ r) * d₀ r) - scale r • w‖ ≤
            η * scale r + K * switchError * (1 + Real.log (2 + scale r)) := by
  intro η hη
  have hη4 : 0 < η / 4 := by positivity
  filter_upwards [hbase (η / 4) hη4, hstart (η / 4) hη4, hleg (η / 4) hη4,
    hmetric, hswitch, hC, hζ.eventually (gt_mem_nhds hη4),
    hscale.eventually (eventually_ge_atTop (0 : ℝ))] with r hb hst hl hmtr hsw hCr hz hr y hy
  have hlog : 0 ≤ 1 + Real.log (2 + scale r) := by
    have hh := Real.log_nonneg (show 1 ≤ 2 + scale r by linarith)
    linarith
  obtain ⟨γ, hγ, hheight⟩ := accessible_word_profile_paths (basis r) Exp hzero a hm
    X s (scale r) letters ι hinj (x r) (d₀ r) (A r) (n₀ r) (hn₀ r)
    (sample r) (hsub r) (hsample r) d hd hd₀ (hf r) (hf₀ r) (J r) (hJ r)
    (center r) w₀ E (mul_nonneg hspeed hr) (mul_nonneg hspeed hlog)
    (mul_nonneg hswitchError hlog) hb hst hl hmtr hsw (C r) hCr y hy
  refine ⟨γ, ?_, ?_⟩
  · convert hγ using 1 <;> first | (with_reducible_and_instances rfl) | ring
  · intro u
    obtain ⟨w, hw, hh⟩ := hheight u
    refine ⟨w, hw, hh.trans ?_⟩
    nlinarith

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_SequenceVolumeComparison
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exponential volume comparison along the profile-scale sequence -/

namespace PolycyclicRecognition

open Filter
open scoped Topology ENNReal

theorem subexponential_upper_polynomial {D : ℝ} (hD : 0 < D) (k : ℕ) :
    HasSubexponentialUpperBound (fun r => D * (1 + r) ^ k) := by
  intro ε hε
  filter_upwards [eventually_logarithmic_error_le (k : ℝ) (Real.log D) hε,
    eventually_ge_atTop (0 : ℝ)] with r hr hr0
  have h1 : 0 < 1 + r := by positivity
  apply (Real.log_le_iff_le_exp (mul_pos hD (pow_pos h1 k))).mp
  rw [Real.log_mul hD.ne' (pow_ne_zero _ h1.ne'), Real.log_pow]
  have hlog : Real.log (1 + r) ≤ Real.log (2 + r) :=
    Real.log_le_log h1 (by linarith)
  have hk : 0 ≤ (k : ℝ) := Nat.cast_nonneg _
  nlinarith [mul_le_mul_of_nonneg_left hlog hk]

theorem exponent_le_of_sequence_polynomial_bound
    {scale f : ℕ → ℝ} (hs : Tendsto scale atTop atTop) {p q D : ℝ}
    (hf : HasSubexponentialLowerBoundSeq scale f) (hD : 0 < D) (k : ℕ)
    (hbound : ∀ᶠ n in atTop,
      f n * Real.exp (scale n * p) ≤ D * (1 + scale n) ^ k * Real.exp (scale n * q)) :
    p ≤ q :=
  exponent_le_of_sequence_subexponential_bounds hs hf
    ((subexponential_upper_polynomial hD k).along_sequence hs) hbound

theorem exponent_le_of_sequence_separated_counts
    {scale f : ℕ → ℝ} (hs : Tendsto scale atTop atTop) {p q D : ℝ}
    (hf : HasSubexponentialLowerBoundSeq scale f) (hD : 0 < D)
    {Q : ℝ≥0∞} (hQ : Q < ⊤) (k : ℕ)
    (hcount : ∀ᶠ n in atTop, ∃ N : ℕ,
      ENNReal.ofReal (f n) * ENNReal.ofReal (Real.exp (scale n * p)) ≤ (N : ℝ≥0∞) * Q ∧
      (N : ℝ) ≤ D * (1 + scale n) ^ k * Real.exp (scale n * q)) : p ≤ q := by
  apply exponent_le_of_sequence_polynomial_bound hs hf
    (show 0 < D * Q.toReal + 1 by positivity) k
  filter_upwards [hcount, hf.eventually_pos, hs.eventually (eventually_ge_atTop (0 : ℝ))]
    with n hn hfpos hrpos
  obtain ⟨N, hlow, hupp⟩ := hn
  have hfinite : (N : ℝ≥0∞) * Q ≠ ⊤ := ENNReal.mul_ne_top (by simp) hQ.ne
  have hl := ENNReal.toReal_mono hfinite hlow
  simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hfpos.le,
    ENNReal.toReal_ofReal (Real.exp_pos _).le, ENNReal.toReal_natCast] at hl
  calc
    f n * Real.exp (scale n * p) ≤ (N : ℝ) * Q.toReal := hl
    _ ≤ (D * (1 + scale n) ^ k * Real.exp (scale n * q)) * Q.toReal :=
      mul_le_mul_of_nonneg_right hupp ENNReal.toReal_nonneg
    _ = (D * Q.toReal) * (1 + scale n) ^ k * Real.exp (scale n * q) := by ring
    _ ≤ _ := by gcongr; linarith

end PolycyclicRecognition

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_SequencePathPacking
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.inversePairCoupling_finiteOnCompacts _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.normalizedPairAction _root_.OAI.PolycyclicRecognition.normalizedPairContinuousAction _root_.OAI.PolycyclicRecognition.normalizedPair_polishSpace _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.normalizedPair_smul_fst _root_.OAI.PolycyclicRecognition.normalizedPair_smul_snd _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Path-packing comparison along a sequence of profile scales -/

noncomputable section

namespace PolycyclicRecognition

open Filter Metric Set
open scoped NNReal ENNReal Topology Pointwise

variable {G W : Type} [Group G] [MetricSpace G]
  [IsTopologicalGroup G] [IsIsometricSMul G G]
  [NormedAddCommGroup W] [NormedSpace ℝ W] {Λ : ℝ≥0}

/-- Successful endpoint sets may lose subexponential mass. Center every
image path at its actual start before applying the ambient packing theorem. -/
theorem exponent_le_of_sequence_image_paths
    (scale : ℕ → ℝ) (hscale : Tendsto scale atTop atTop)
    (π : G →* Multiplicative W) (E : Set W) (P : Set W → ℝ)
    {p K C D : ℝ} {Q : ℝ≥0∞} {mass : ℕ → ℝ}
    (hmass : HasSubexponentialLowerBoundSeq scale mass) (hΛ : 0 < (Λ : ℝ))
    (hK : 0 ≤ K) (hC : 0 ≤ C) (hQ : Q < ⊤) (hD : 0 < D) (k : ℕ)
    (hlower : ∀ η : ℝ, 0 < η → ∀ᶠ n in atTop,
      ∃ (f : NormalizedPair G Λ) (a : G) (s : Finset G),
        (∀ x ∈ s, ∀ y ∈ s, x ≠ y → (Λ : ℝ) * ((Λ : ℝ) + 1) < dist x y) ∧
        ENNReal.ofReal (mass n) * ENNReal.ofReal (Real.exp (scale n * p)) ≤
          (s.card : ℝ≥0∞) * Q ∧
        ∀ g ∈ s, ∃ γ : Path a g,
          PathMetricBound γ (C * scale n) (C * (1 + Real.log (2 + scale n))) ∧
          ∀ t, ∃ z ∈ E,
            ‖(π (f.val.1 (γ t))).toAdd - (π (f.val.1 a)).toAdd - scale n • z‖ ≤
              η * scale n + K * Λ * C * (1 + Real.log (2 + scale n)))
    (hupper : ∀ {r L κ B ε : ℝ}, 0 < r → 0 ≤ L → 0 ≤ κ → 0 ≤ ε →
      K * (κ + 2) + B ≤ r * ε → ∀ s : Finset G,
      (∀ x ∈ s, ∀ y ∈ s, x ≠ y → 1 ≤ dist x y) →
      (∀ x ∈ s, ∃ γ : Path (1 : G) x, PathMetricBound γ L κ ∧
        ∀ t, ∃ z ∈ E, ‖(π (γ t)).toAdd - r • z‖ ≤ B) →
      (s.card : ℝ) ≤ D * (3 + (L + 1) * (κ + 2)) ^ k *
        Real.exp (r * P (E + closedBall 0 ε))) :
    ∀ ε : ℝ, 0 < ε → p ≤ P (E + closedBall 0 ε) := by
  classical
  intro ε hε
  let A := (Λ : ℝ) * C
  let b := K * Λ * C
  have hA : 0 ≤ A := mul_nonneg Λ.coe_nonneg hC
  have hb : 0 ≤ b := by dsimp [b] <;> positivity
  let η := ε / 2
  have hη : 0 < η := by dsimp [η] <;> positivity
  let H := 3 + (A + 1) * (3 * A + 2)
  have hH : 0 < H := by dsimp [H] <;> positivity
  apply exponent_le_of_sequence_separated_counts hscale hmass
    (show 0 < D * H ^ k by positivity) hQ (2 * k)
  filter_upwards [hlower η hη, hscale.eventually (eventually_ge_atTop (1 : ℝ)),
    hscale.eventually (eventually_logarithmic_error_le (2 * b) (2 * K) (half_pos hε))]
      with n hr hr1 hlog
  let r := scale n
  have hrpos : 0 < r := by linarith
  have hlog0 : 0 ≤ 1 + Real.log (2 + r) := by
    have := Real.log_nonneg (by linarith : 1 ≤ 2 + r)
    linarith
  obtain ⟨f, a, s, hsep, hlow, hpaths⟩ := hr
  let t := s.image (basedImage f.val.1 a)
  obtain ⟨hcard, hsep'⟩ := basedImage_separated_card f hΛ a s hsep
  let L := A * r
  let κ := A * (1 + Real.log (2 + r))
  let B := η * r + b * (1 + Real.log (2 + r))
  have hL : 0 ≤ L := mul_nonneg hA hrpos.le
  have hκ : 0 ≤ κ := mul_nonneg hA hlog0
  have herr : K * (κ + 2) + B ≤ r * ε := by
    dsimp only [κ, B, A, b, η] at *
    nlinarith
  have himage : ∀ x ∈ t, ∃ γ : Path (1 : G) x, PathMetricBound γ L κ ∧
      ∀ u, ∃ z ∈ E, ‖(π (γ u)).toAdd - r • z‖ ≤ B := by
    intro x hx
    obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨γ, hγ, hh⟩ := hpaths g hg
    obtain ⟨ζ, hζ, hmetric⟩ := basedImage_map_path f.val.1 f.property.1.1 γ hγ
    refine ⟨ζ, ?_, ?_⟩
    · convert hmetric using 1 <;> first | (with_reducible_and_instances rfl) | (dsimp [L, κ, A] <;> ring)
    · intro u
      rw [hζ, basedImage_height]
      exact hh u
  have hcount := hupper hrpos hL hκ hε.le herr t hsep' himage
  refine ⟨s.card, hlow, ?_⟩
  rw [← hcard]
  apply hcount.trans
  have hpoly := coarse_path_word_prefactor_le hA hr1
  dsimp only [L, κ] at *
  calc
    _ ≤ D * (H * (1 + r) ^ 2) ^ k * Real.exp (r * P (E + closedBall 0 ε)) := by
      apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
      apply mul_le_mul_of_nonneg_left _ hD.le
      exact pow_le_pow_left₀ (by positivity) hpoly k
    _ = _ := by rw [mul_pow, ← pow_mul]; ring

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_SequenceFixedSliceVolume
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.inversePairCoupling_finiteOnCompacts _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.normalizedPairAction _root_.OAI.PolycyclicRecognition.normalizedPairContinuousAction _root_.OAI.PolycyclicRecognition.normalizedPair_polishSpace _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Accessible fixed-slice volume along the profile-scale sequence -/

noncomputable section

namespace PolycyclicRecognition

open MeasureTheory Filter Metric Set
open scoped NNReal ENNReal Topology Pointwise

/-- The geometric packing comparison for compact accessible endpoint sets.
Haar volume supplies the lower count; only the image paths and the existing
ambient path-packing theorem are used for the upper count. -/
theorem fixedSlice_sequence_volume_exponent_le
    {N D G W : Type} [Group N] [Group D] [Group G]
    [TopologicalSpace N] [MeasurableSpace N] [MeasurableMul N]
    [MetricSpace G] [IsTopologicalGroup G] [IsIsometricSMul G G] [ProperSpace G]
    [NormedAddCommGroup W] [NormedSpace ℝ W] {Λ : ℝ≥0}
    (scale : ℕ → ℝ) (hscale : Tendsto scale atTop atTop)
    (ι : N →* G) (κ : D →* G) (φ : D →* MulAut N)
    (μ : Measure N) [μ.IsMulLeftInvariant] [IsFiniteMeasureOnCompacts μ]
    (hφ : ∀ d, MeasurePreserving (φ d) μ μ)
    (hconj : ∀ d n, ι (φ d n) = κ d * ι n * (κ d)⁻¹)
    (hι : Topology.IsClosedEmbedding ι)
    (S : ℕ → Set N) (hS : ∀ n, IsCompact (S n))
    (x : ℕ → G) (d : ℕ → D) (a : ℕ → G) (f : ℕ → NormalizedPair G Λ)
    (π : G →* Multiplicative W) (E : Set W) (P : Set W → ℝ)
    {p K C A : ℝ} (hΛ : 0 < (Λ : ℝ)) (hK : 0 ≤ K) (hC : 0 ≤ C)
    (hmass : HasSubexponentialLowerBoundSeq scale (fun n => (μ (S n)).toReal / Real.exp (scale n * p)))
    (hpaths : ∀ η : ℝ, 0 < η → ∀ᶠ n in atTop, ∀ u ∈ S n,
      ∃ γ : Path (a n) (x n * ι u * κ (d n)),
        PathMetricBound γ (C * scale n) (C * (1 + Real.log (2 + scale n))) ∧
        ∀ t, ∃ z ∈ E,
          ‖(π ((f n).val.1 (γ t))).toAdd - (π ((f n).val.1 (a n))).toAdd - scale n • z‖ ≤
            η * scale n + K * Λ * C * (1 + Real.log (2 + scale n)))
    (hA : 0 < A) (k : ℕ)
    (hupper : ∀ {r L κ' B ε : ℝ}, 0 < r → 0 ≤ L → 0 ≤ κ' → 0 ≤ ε →
      K * (κ' + 2) + B ≤ r * ε → ∀ s : Finset G,
      (∀ y ∈ s, ∀ z ∈ s, y ≠ z → 1 ≤ dist y z) →
      (∀ y ∈ s, ∃ γ : Path (1 : G) y, PathMetricBound γ L κ' ∧
        ∀ t, ∃ z ∈ E, ‖(π (γ t)).toAdd - r • z‖ ≤ B) →
      (s.card : ℝ) ≤ A * (3 + (L + 1) * (κ' + 2)) ^ k *
        Real.exp (r * P (E + closedBall 0 ε))) :
    ∀ ε : ℝ, 0 < ε → p ≤ P (E + closedBall 0 ε) := by
  let ρ := (Λ : ℝ) * ((Λ : ℝ) + 1)
  have hρ : 0 < ρ := mul_pos hΛ (by linarith)
  let Q := μ (ι ⁻¹' closedBall (1 : G) ρ)
  have hQ : Q < ⊤ := fixedSlice_packing_constant_lt_top ι μ hι ρ
  apply exponent_le_of_sequence_image_paths scale hscale π E P hmass hΛ hK hC hQ hA k
  · intro η hη
    filter_upwards [hpaths η hη] with n hr
    obtain ⟨s, hs, hsep, hmass'⟩ := exists_fixedSlice_separated_net_of_compact
      ι κ φ μ hφ hconj hι.continuous (x n) (d n) (hS n) (Subset.refl (S n)) hρ
    refine ⟨f n, a n, s, hsep, ?_, ?_⟩
    · have hv : μ (S n) ≠ ⊤ := (hS n).measure_lt_top.ne
      have he : ENNReal.ofReal ((μ (S n)).toReal / Real.exp (scale n * p)) *
          ENNReal.ofReal (Real.exp (scale n * p)) = μ (S n) := by
        rw [← ENNReal.ofReal_mul (div_nonneg ENNReal.toReal_nonneg (Real.exp_pos _).le)]
        rw [div_mul_cancel₀ _ (Real.exp_ne_zero _), ENNReal.ofReal_toReal hv]
      rw [he]
      exact hmass'
    · intro g hg
      obtain ⟨u, hu, rfl⟩ := hs hg
      exact hr u hu
  · exact hupper

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_SequenceRescaledImageVolume
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.CartanFactorModel.realScaleProfile_apply _root_.OAI.PolycyclicRecognition.bracketWordDifferential_mul _root_.OAI.PolycyclicRecognition.exponentialRescaleBasis_zero _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Rescaled exponential image volume along profile sequences -/

noncomputable section

namespace PolycyclicRecognition

open Module MeasureTheory Set Filter
open scoped Manifold Topology ENNReal

variable {L : Type} [LieRing L] [LieAlgebra ℝ L]
  {E G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace G] [ChartedSpace E G] [Group G]
  [LieGroup (𝓘(ℝ, E)) ⊤ G] [MeasurableSpace G] [BorelSpace G]

/-- The subexponential logarithmic image loss survives the rescaled
exponential chart with exactly the selected word-basis exponent. -/
theorem rescaled_image_volume_lower_sequence
    (scale : ℕ → ℝ) (hscale : Tendsto scale atTop atTop)
    (e : L ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, E)) G)
    (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G)
    (chart : GroupLieAlgebra (𝓘(ℝ, E)) G ≃ₜ G) (hchart : ∀ x, chart x = Exp x)
    {I : Type} (X : I → L) (words : Finset (FreeMagma I))
    (b₀ : Basis (Fin (finrank ℝ L)) ℝ L) (β : WordBasisSelections X words)
    (cost : words → ℝ) (C : ℕ → Set (Fin (finrank ℝ L) → ℝ))
    (hlower : HasSubexponentialLowerBoundSeq scale (fun n => (volume (C n)).toReal)) :
    HasSubexponentialLowerBoundSeq scale (fun n =>
      ((Measure.map ((Exp ∘ e) ∘ b₀.equivFun.symm) volume)
        ((((Exp ∘ e) ∘ (exponentialRescaleBasis (WordBasisSelections.basis X words β)
          (fun j => cost (β.val j)) (scale n)).equivFun.symm)) '' C n)).toReal /
        Real.exp (scale n * columnBasisWeight cost β.val)) := by
  have hdet : 0 < |(columnBasisMatrix (wordListCoordinates X words b₀) β.val).det| :=
    abs_pos.mpr (wordBasis_det_ne_zero X words b₀ β)
  have he (n : ℕ) :
      ((Measure.map ((Exp ∘ e) ∘ b₀.equivFun.symm) volume)
        ((((Exp ∘ e) ∘ (exponentialRescaleBasis (WordBasisSelections.basis X words β)
          (fun j => cost (β.val j)) (scale n)).equivFun.symm)) '' C n)).toReal /
        Real.exp (scale n * columnBasisWeight cost β.val) =
      |(columnBasisMatrix (wordListCoordinates X words b₀) β.val).det| * (volume (C n)).toReal := by
    rw [exponential_rescaled_subset_measure e Exp chart hchart X words b₀ β cost (scale n) (C n)]
    rw [ENNReal.toReal_mul, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (abs_nonneg _), ENNReal.toReal_ofReal (Real.exp_pos _).le]
    field_simp
  have hc : HasSubexponentialLowerBoundSeq scale (fun _ =>
      |(columnBasisMatrix (wordListCoordinates X words b₀) β.val).det|) := by
    simpa only [Function.comp_def] using (subexponential_lower_const hdet).along_sequence hscale
  have hh := hc.mul hlower
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  funext n
  exact he n

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
local instance instNontrivialSubtypeMemLieSubmoduleRealLieSubalgebraRootSpaceCoeWeight_solutions_1_r72e8a9_1 : Nontrivial (rootSpace H χ) :=
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
local instance instNontrivialSubtypeMemLieSubmoduleRealLieSubalgebraRootSpaceCoeWeight_solutions_2_r72e8a9_1 : Nontrivial (rootSpace H χ) :=
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
local instance instNontrivialSubtypeMemLieSubmoduleRealLieSubalgebraRootSpaceCoeWeight_solutions_2_r72e8a9_2 : Nontrivial (rootSpace H χ) :=
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
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanIntervalVisits
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instDecidableEqConeMixedWords _root_.OAI.PolycyclicRecognition.CartanWordModel.instFintypeConeMixedWords _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.CartanFactorModel.heightRay_zero _root_.OAI.PolycyclicRecognition.CartanFactorModel.realScaleProfile_apply _root_.OAI.PolycyclicRecognition.CartanFactorModel.sampledProbeProfile_apply _root_.OAI.PolycyclicRecognition.cartanWeightDerivation_apply_root _root_.OAI.PolycyclicRecognition.chartExponentialFlow_zero _root_.OAI.PolycyclicRecognition.derivationSemidirectHom_apply _root_.OAI.PolycyclicRecognition.exponentialHomOfDynkin_apply_exp _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.nilshadowWeightDerivation_symm _root_.OAI.PolycyclicRecognition.nilshadowWeightOperator_symm _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Physical visit bounds for the original root interval samples -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra
open scoped Manifold

variable {EG G W I : Type} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G] [IsIsometricSMul G G]
  [IsTopologicalGroup G]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [Fintype I] [DecidableEq I]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H Exp)
  (hExp : IsGroupExponential Exp)
  (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))

set_option maxHeartbeats 1000000 in
omit [IsIsometricSMul G G] in
/-- Coordinate descriptions of the same root curve produce the same visit. -/
theorem supportVisitPath_apply_eq_sampled
    (v : H) (i : Fin M.letterCount) (n k : G) (h₀ : H) (r s b : ℝ)
    (f : ℝ → G) (hf : Continuous f) (hf₀ : f 0 = 1)
    (he : ∀ t, f t = Exp ((t * Real.exp (r * s)) •
      (M.letter i : GroupLieAlgebra (𝓘(ℝ, EG)) G)))
    (hd : Continuous (fun t : ℝ => Exp (t • (v : GroupLieAlgebra (𝓘(ℝ, EG)) G))))
    (hd₀ : Exp ((0 : ℝ) • (v : GroupLieAlgebra (𝓘(ℝ, EG)) G)) = 1)
    (hk : k = Exp h₀) (t : unitInterval) :
    supportVisitPath (fun t => Exp (t • (v : GroupLieAlgebra (𝓘(ℝ, EG)) G)))
      hd hd₀ f hf hf₀ n k r b t =
      M.sampledDirectionalVisitPath T hExp realize v i n h₀ r s b t := by
  unfold sampledDirectionalVisitPath
  exact supportVisitPath_apply_congr _ _ _ _ hd
    (continuous_exp_line_of_published_realization T Exp hExp realize v)
    hd₀ (by simp [hExp.map_zero]) hf
    ((continuous_exp_line_of_published_realization T Exp hExp realize (M.letter i)).comp
      (continuous_id.mul_const _)) hf₀ (by simp [hExp.map_zero])
    (fun _ => rfl) he n k (Exp h₀) hk r b t

end PolycyclicRecognition.CartanWordModel

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

variable {L : Type} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
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
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_SequenceCartanAccessible
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instDecidableEqConeMixedWords _root_.OAI.PolycyclicRecognition.CartanWordModel.instFintypeConeMixedWords _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_nonempty _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.inversePairCoupling_finiteOnCompacts _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.normalizedPairAction _root_.OAI.PolycyclicRecognition.normalizedPairContinuousAction _root_.OAI.PolycyclicRecognition.normalizedPair_polishSpace _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.CartanFactorModel.heightRay_zero _root_.OAI.PolycyclicRecognition.CartanFactorModel.realScaleProfile_apply _root_.OAI.PolycyclicRecognition.CartanFactorModel.sampledProbeProfile_apply _root_.OAI.PolycyclicRecognition.bracketWordDifferential_mul _root_.OAI.PolycyclicRecognition.cartanWeightDerivation_apply_root _root_.OAI.PolycyclicRecognition.exponentialRescaleBasis_zero _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.modelNilradicalLinearAction_apply _root_.OAI.PolycyclicRecognition.modelNilradicalRotation_apply _root_.OAI.PolycyclicRecognition.modelNilradicalRotation_mul _root_.OAI.PolycyclicRecognition.modelNilradicalRotation_one _root_.OAI.PolycyclicRecognition.nilshadowWeightDerivation_symm _root_.OAI.PolycyclicRecognition.nilshadowWeightOperator_symm _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.normalizedPair_smul_fst _root_.OAI.PolycyclicRecognition.normalizedPair_smul_snd _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Cartan accessible-volume comparison along profile sequences -/

noncomputable section

namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule MeasureTheory Filter Set
open scoped Manifold NNReal ENNReal

variable {EG G W : Type} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [IsIsometricSMul G G] [ProperSpace G] [IsTopologicalGroup G]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  {Λ : ℝ≥0} {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H Exp)
  (hunimod : ∀ x : GroupLieAlgebra (𝓘(ℝ, EG)) G, LinearMap.trace ℝ _ (ad ℝ _ x) = 0)
  (eW : HeightSpace T.character ≃ₗ[ℝ] W) (π : G →* Multiplicative W)
  (hπExp : ∀ x, (π (Exp x)).toAdd = eW (heightProjection T.character x))
  (chartN : GroupLieAlgebra (𝓘(ℝ, F.N.modelSpace)) F.N.carrier ≃ₜ F.N.carrier)
  (hchartN : ∀ x, chartN x = F.ExpN x)
  (chartD : GroupLieAlgebra (𝓘(ℝ, F.D.modelSpace)) F.D.carrier ≃ₜ F.D.carrier)
  (hchartD : ∀ x, chartD x = F.ExpD x)
  (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
  (dynkinD : NilpotentDynkinExpansionInput F.D.modelSpace F.D.carrier)
  (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
  (haarD : NilpotentExponentialHaarInput F.D.modelSpace F.D.carrier)

set_option maxHeartbeats 1000000 in
include hπExp dynkinD haarN haarD in
/-- A compact successful logarithmic image of subexponential volume cannot
have a larger source support exponent than its image-path height template. -/
theorem accessible_templateSupport_le_sequence
    (scale : ℕ → ℝ) (hscale : Tendsto scale atTop atTop)
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (source target : Set W) (htarget : IsCompact target) (hne : target.Nonempty)
    (β : M.Bases)
    (hβ : IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
      (M.boxCost T hunimod eW source) β.val)
    (C : ℕ → Set (Fin (finrank ℝ (cartanRootIdeal H)) → ℝ))
    (hC : ∀ n, IsCompact (C n))
    (hvol : HasSubexponentialLowerBoundSeq scale (fun n => (volume (C n)).toReal))
    (x : ℕ → G) (d : ℕ → F.D.carrier) (start : ℕ → G)
    (f : ℕ → NormalizedPair G Λ) (hΛ : 0 < (Λ : ℝ))
    (hφ : ∀ d, F.action d = M.adjointGroupAutomorphism T F.N.equiv F.ExpN F.isExpN
      (by rw [← show chartN = F.ExpN from funext hchartN]; exact chartN.bijective) dynkinN
      (cartanLog H F.D.equiv F.ExpD
        (by rw [← show chartD = F.ExpD from funext hchartD]; exact chartD.bijective) d))
    (hpath : ∀ g : G, ∃ γ : ℝ → G, γ 0 = 1 ∧ γ 1 = g ∧
      ∀ t ∈ Icc (0 : ℝ) 1, ∀ u ∈ Icc (0 : ℝ) 1,
        dist (γ t) (γ u) ≤ dist 1 g * |t - u|)
    {K L : ℝ} (hK : 0 ≤ K) (hL : 0 ≤ L)
    (hLip : ∀ g h, ‖(π g).toAdd - (π h).toAdd‖ ≤ K * dist g h)
    (hpaths : ∀ η : ℝ, 0 < η → ∀ᶠ n in atTop, ∀ y ∈ C n,
      ∃ γ : Path (start n)
        (x n * F.inclusionN (F.ExpN (F.N.equiv
          ((M.boxBasis T hunimod eW source β (scale n)).equivFun.symm y))) * F.inclusionD (d n)),
        PathMetricBound γ (L * scale n) (L * (1 + Real.log (2 + scale n))) ∧
        ∀ t, ∃ z ∈ target,
          ‖(π ((f n).val.1 (γ t))).toAdd - (π ((f n).val.1 (start n))).toAdd - scale n • z‖ ≤
            η * scale n + K * Λ * L * (1 + Real.log (2 + scale n))) :
    (M.supportIn T hunimod eW).templateSupport source ≤
      (M.supportIn T hunimod eW).templateSupport target := by
  let : IsTopologicalGroup F.N.carrier := topologicalGroup_of_lieGroup (𝓘(ℝ, F.N.modelSpace)) ⊤
  let μ := Measure.map ((F.ExpN ∘ F.N.equiv) ∘ b₀.equivFun.symm) volume
  have hnil : LieRing.IsNilpotent (cartanRootIdeal H) :=
    (LieModule.isNilpotent_iff ℝ _ _).mpr ⟨M.bound, M.bound_zero⟩
  let : μ.IsHaarMeasure := exponential_basis_measure_isHaar haarN F.N.equiv hnil F.ExpN F.isExpN b₀
  have hpres (d : F.D.carrier) : MeasurePreserving (F.action d) μ μ := by
    rw [hφ]
    exact exponentialConjugate_measurePreserving F.N.equiv F.ExpN
      (by rw [← show chartN = F.ExpN from funext hchartN]; exact chartN.bijective)
      chartN hchartN b₀ _ (M.det_idealAdjointAutomorphism_eq_one T hunimod _)
  let S := fun n => ((F.ExpN ∘ F.N.equiv) ∘
    (M.boxBasis T hunimod eW source β (scale n)).equivFun.symm) '' C n
  have hS (n : ℕ) : IsCompact (S n) :=
    (hC n).image (continuous_exponential_basis F.N.equiv F.ExpN chartN hchartN _)
  have hexp := M.columnBasisWeight_eq_templateSupport_of_maximizing T hunimod eW b₀ source β hβ
  have hmass : HasSubexponentialLowerBoundSeq scale (fun n =>
      (μ (S n)).toReal / Real.exp (scale n * (M.supportIn T hunimod eW).templateSupport source)) := by
    have hh := rescaled_image_volume_lower_sequence scale hscale F.N.equiv F.ExpN chartN hchartN M.letter M.wordList
      b₀ β (M.boxCost T hunimod eW source) C hvol
    simpa only [μ, S, boxBasis, hexp] using hh
  obtain ⟨A, k, hA, hupper⟩ := M.exists_coarse_path_polynomial_packing T F hunimod eW π hπExp
    chartN hchartN chartD hchartD dynkinN dynkinD haarN haarD b₀ β
    (show (0 : ℝ) < 1 by norm_num) hφ hpath hK hLip
  apply (M.supportIn T hunimod eW).le_templateSupport_of_thickenings htarget hne
  apply fixedSlice_sequence_volume_exponent_le scale hscale F.inclusionN F.inclusionD F.action μ hpres
    F.conjugation F.closedN S hS x d start f π target
    (M.supportIn T hunimod eW).templateSupport hΛ hK hL hmass
  · intro η hη
    filter_upwards [hpaths η hη] with n hr u hu
    obtain ⟨y, hy, rfl⟩ := hu
    exact hr y hy
  · exact hA
  · exact hupper htarget hne

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_SequenceCartanProfilePacking
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instDecidableEqConeMixedWords _root_.OAI.PolycyclicRecognition.CartanWordModel.instFintypeConeMixedWords _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_nonempty _root_.OAI.PolycyclicRecognition.finite_templateSymmetryGroup _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.instFiniteRootOffsetConeIndex _root_.OAI.PolycyclicRecognition.instFiniteSubtypeLinearEquivRealIdMemSubgroupLinearSupportSymmetryGroup _root_.OAI.PolycyclicRecognition.instNonemptyRootOffsetConeIndex _root_.OAI.PolycyclicRecognition.inversePairCoupling_finiteOnCompacts _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.CartanFactorModel.heightRay_zero _root_.OAI.PolycyclicRecognition.CartanFactorModel.realScaleProfile_apply _root_.OAI.PolycyclicRecognition.CartanFactorModel.sampledProbeProfile_apply _root_.OAI.PolycyclicRecognition.basisDynkinParameter_zero _root_.OAI.PolycyclicRecognition.bracketWordDifferential_mul _root_.OAI.PolycyclicRecognition.cartanWeightDerivation_apply_root _root_.OAI.PolycyclicRecognition.chartExponentialFlow_zero _root_.OAI.PolycyclicRecognition.derivationSemidirectHom_apply _root_.OAI.PolycyclicRecognition.dynkinRightTranslation_apply _root_.OAI.PolycyclicRecognition.dynkinRightTranslation_symm_apply _root_.OAI.PolycyclicRecognition.exponentialHomOfDynkin_apply_exp _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.modelNilradicalLinearAction_apply _root_.OAI.PolycyclicRecognition.modelNilradicalRotation_apply _root_.OAI.PolycyclicRecognition.modelNilradicalRotation_mul _root_.OAI.PolycyclicRecognition.modelNilradicalRotation_one _root_.OAI.PolycyclicRecognition.nilshadowWeightDerivation_symm _root_.OAI.PolycyclicRecognition.nilshadowWeightOperator_symm _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Packing comparison for successful good sheets along profile sequences -/

noncomputable section

namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule MeasureTheory Filter Set
open scoped Manifold NNReal ENNReal Topology

variable {EG G W : Type} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [IsIsometricSMul G G] [ProperSpace G] [IsTopologicalGroup G]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  {Λ : ℝ≥0} {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H Exp)
  (hunimod : ∀ x : GroupLieAlgebra (𝓘(ℝ, EG)) G, LinearMap.trace ℝ _ (ad ℝ _ x) = 0)
  (eW : HeightSpace T.character ≃ₗ[ℝ] W) (π : G →* Multiplicative W)
  (hπExp : ∀ x, (π (Exp x)).toAdd = eW (heightProjection T.character x))
  (chartN : GroupLieAlgebra (𝓘(ℝ, F.N.modelSpace)) F.N.carrier ≃ₜ F.N.carrier)
  (hchartN : ∀ x, chartN x = F.ExpN x)
  (chartD : GroupLieAlgebra (𝓘(ℝ, F.D.modelSpace)) F.D.carrier ≃ₜ F.D.carrier)
  (hchartD : ∀ x, chartD x = F.ExpD x)
  (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
  (dynkinD : NilpotentDynkinExpansionInput F.D.modelSpace F.D.carrier)
  (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
  (haarD : NilpotentExponentialHaarInput F.D.modelSpace F.D.carrier)

set_option maxHeartbeats 1000000 in
include hπExp dynkinD haarN haarD in
/-- The good-sheet leg estimates and short root switches supply the full
controlled-path premise of the Cartan volume comparison. -/
theorem templateSupport_le_of_good_profile_paths_sequence
    (scale : ℕ → ℝ) (hscale : Tendsto scale atTop atTop)
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (source E : Set W) (hE : IsCompact E) (hne : E.Nonempty) (w₀ : W)
    (β : M.Bases)
    (hβ : IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
      (M.boxCost T hunimod eW source) β.val)
    (C : ℕ → Set (Fin (finrank ℝ (cartanRootIdeal H)) → ℝ))
    (hC : ∀ r, IsCompact (C r))
    (hvol : HasSubexponentialLowerBoundSeq scale (fun r => (volume (C r)).toReal))
    (x : ℕ → G) (d₀ : ℕ → F.D.carrier) (n₀ : ℕ → F.N.carrier)
    (A : ℕ → Set F.N.carrier) (hn₀ : ∀ r, n₀ r ∈ A r)
    (f : ℕ → NormalizedPair G Λ) (hΛ : 0 < (Λ : ℝ))
    (hφ : ∀ d, F.action d = M.adjointGroupAutomorphism T F.N.equiv F.ExpN F.isExpN
      (by rw [← show chartN = F.ExpN from funext hchartN]; exact chartN.bijective) dynkinN
      (cartanLog H F.D.equiv F.ExpD
        (by rw [← show chartD = F.ExpD from funext hchartD]; exact chartD.bijective) d))
    (hpath : ∀ g : G, ∃ γ : ℝ → G, γ 0 = 1 ∧ γ 1 = g ∧
      ∀ t ∈ Icc (0 : ℝ) 1, ∀ u ∈ Icc (0 : ℝ) 1,
        dist (γ t) (γ u) ≤ dist 1 g * |t - u|)
    {K : ℝ≥0} (hLip : LipschitzWith K (fun g => (π g).toAdd))
    {m c : ℕ} (aN : DynkinCoefficients c 2)
    (hm : ∀ u v, F.ExpN (finiteDynkinPolynomial aN ![u, v]) = F.ExpN u * F.ExpN v)
    (s : Fin M.letterCount → ℝ) (letters : Fin m → Fin M.letterCount)
    (sample : ℕ → ℕ → ℝ → F.N.carrier)
    (hsub : ∀ r j u v, sample r j u * (sample r j v)⁻¹ = sample r j (u - v))
    (hsample : ∀ r, ∀ j : Fin m, ∀ u, sample r j.val u =
      F.ExpN (F.N.equiv (u • (Real.exp (scale r * s (letters j)) • M.letter (letters j)))))
    (d : Fin m → ℝ → G) (hd : ∀ i, Continuous (d i)) (hd₀ : ∀ i, d i 0 = 1)
    (hf : ∀ r, ∀ i : Fin m, Continuous (fun t => F.inclusionN (sample r i.val t)))
    (hf₀ : ∀ r, ∀ i : Fin m, F.inclusionN (sample r i.val 0) = 1)
    (center : ℕ → W) (ζ : ℕ → ℝ) (hζ : Tendsto ζ atTop (𝓝 0))
    {speed switchError ρ : ℝ} (hspeed : 0 ≤ speed) (hswitchError : 0 ≤ switchError)
    (hbase : ∀ η : ℝ, 0 < η → ∀ᶠ r in atTop, ∀ u ∈ A r,
      ∃ w ∈ E, ‖(π ((f r).val.1 (x r * F.inclusionN u * F.inclusionD (d₀ r)))).toAdd -
        center r - scale r • w‖ ≤ scale r * (ζ r + η))
    (hstart : ∀ η : ℝ, 0 < η → ∀ᶠ r in atTop,
      ‖(π ((f r).val.1 (x r * F.inclusionN (n₀ r) * F.inclusionD (d₀ r)))).toAdd -
        center r - scale r • w₀‖ ≤ scale r * (ζ r + η))
    (hleg : ∀ η : ℝ, 0 < η → ∀ᶠ r in atTop, ∀ u ∈ A r, ∀ i : Fin m,
      ∀ t : unitInterval, ∃ w ∈ E,
        ‖(π ((f r).val.1 ((x r * F.inclusionN u * F.inclusionD (d₀ r)) * d i (scale r * t)))).toAdd -
          center r - scale r • w‖ ≤ scale r * (ζ r + η))
    (hmetric : ∀ᶠ r in atTop, ∀ u ∈ A r, ∀ i : Fin m, ∀ b : ℝ,
      |b| ≤ 2 * ρ → u * sample r i.val b ∈ A r →
      PathMetricBound (supportVisitPath (d i) (hd i) (hd₀ i)
        (fun t => F.inclusionN (sample r i.val t)) (hf r i) (hf₀ r i)
        (x r * F.inclusionN u) (F.inclusionD (d₀ r)) (scale r) b)
        (speed * scale r) (speed * (1 + Real.log (2 + scale r))))
    (hswitch : ∀ᶠ r in atTop, ∀ u ∈ A r, ∀ i : Fin m, ∀ b : ℝ,
      |b| ≤ 2 * ρ → ∀ t : unitInterval,
      dist ((x r * F.inclusionN u) * F.inclusionN (sample r i.val ((t : ℝ) * b)) *
          (F.inclusionD (d₀ r) * d i (scale r)))
        ((x r * F.inclusionN u * F.inclusionD (d₀ r)) * d i (scale r)) ≤
          switchError * (1 + Real.log (2 + scale r)))
    (haccessible : ∀ᶠ r in atTop, ∀ y ∈ C r,
      ∃ t ∈ Metric.closedBall (0 : Fin (m + m) → ℝ) ρ,
      SwitchSuccessful (fun _ => A r) 0 m (n₀ r) (sampledSwitchParameters (sample r) m t) ∧
      differenceAmplitudeWordEndpoint aN letters
        (basisBracket (M.boxBasis T hunimod eW source β (scale r)),
          fun i => (M.boxBasis T hunimod eW source β (scale r)).equivFun
            (Real.exp (scale r * s i) • M.letter i)) t = y) :
    (M.supportIn T hunimod eW).templateSupport source ≤
      (M.supportIn T hunimod eW).templateSupport E := by
  let J := fun (r : ℕ) g => (π ((f r).val.1 g)).toAdd
  have hJ (r : ℕ) : LipschitzWith (K * Λ) (J r) := hLip.comp (f r).property.1.1
  have hpaths := sublinear_accessible_word_paths_sequence scale hscale
    (fun r => M.boxBasis T hunimod eW source β (scale r)) (F.ExpN ∘ F.N.equiv)
    (by simp [F.isExpN.map_zero]) aN (model_binary_dynkin F.N.equiv F.ExpN aN hm)
    M.letter s letters F.inclusionN F.closedN.injective x (fun r => F.inclusionD (d₀ r))
    A n₀ hn₀ sample hsub hsample d hd hd₀ hf hf₀ J hJ center w₀ E ζ hζ
    hspeed hswitchError hbase hstart hleg hmetric hswitch C haccessible
  let L := speed * 2 ^ m + switchError
  have hL : 0 ≤ L := by dsimp [L] <;> positivity
  have htranslate := (M.supportIn T hunimod eW).templateSupport_translate hE hne (-w₀)
  rw [← htranslate]
  simp only [← sub_eq_add_neg]
  apply M.accessible_templateSupport_le_sequence T F hunimod eW π hπExp chartN hchartN chartD hchartD
    dynkinN dynkinD haarN haarD scale hscale b₀ source ((fun z => z - w₀) '' E)
    (hE.image (continuous_id.sub continuous_const)) (hne.image _) β hβ C hC hvol
    (fun r => x r * F.inclusionN (n₀ r)) d₀
    (fun r => x r * F.inclusionN (n₀ r) * F.inclusionD (d₀ r)) f hΛ hφ hpath
    K.coe_nonneg hL
    (fun g h => by simpa only [dist_eq_norm] using hLip.dist_le_mul g h)
  intro η hη
  filter_upwards [hpaths η hη, hscale.eventually (eventually_ge_atTop (0 : ℝ))] with r hr hr0 y hy
  obtain ⟨γ, hγ, hh⟩ := hr y hy
  have hend :
      (x r * F.inclusionN (n₀ r)) * F.inclusionN (F.ExpN (F.N.equiv
        ((M.boxBasis T hunimod eW source β (scale r)).equivFun.symm y))) * F.inclusionD (d₀ r) =
      x r * F.inclusionN (n₀ r * F.ExpN (F.N.equiv
        ((M.boxBasis T hunimod eW source β (scale r)).equivFun.symm y))) * F.inclusionD (d₀ r) := by
    simp only [map_mul, mul_assoc]
  refine ⟨γ.cast rfl hend, ?_, ?_⟩
  · apply hγ.mono
    · apply mul_le_mul_of_nonneg_right _ hr0
      exact le_add_of_nonneg_right hswitchError
    · apply mul_le_mul_of_nonneg_right _ (by
        have := Real.log_nonneg (show 1 ≤ 2 + scale r by linarith)
        linarith)
      exact le_add_of_nonneg_right hswitchError
  · intro t
    obtain ⟨w, hw, hb⟩ := hh t
    refine ⟨w, hw, hb.trans ?_⟩
    simp only [NNReal.coe_mul]
    apply add_le_add le_rfl
    apply mul_le_mul_of_nonneg_right _ (by
      have := Real.log_nonneg (show 1 ≤ 2 + scale r by linarith)
      linarith)
    exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (by positivity : 0 ≤ speed * 2 ^ m))
      (mul_nonneg K.coe_nonneg Λ.coe_nonneg)

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanRecurrentProfilePacking
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instDecidableEqConeMixedWords _root_.OAI.PolycyclicRecognition.CartanWordModel.instFintypeConeMixedWords _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_countable _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_nonempty _root_.OAI.PolycyclicRecognition.finitelyGeneratedSubgroupIndex_countable _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.inversePairCoupling_finiteOnCompacts _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # From recurrent good sheets to the actual Cartan support inequality -/

noncomputable section

namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule MeasureTheory Filter Set
open scoped Manifold NNReal ENNReal Topology

variable {EG G W : Type} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [IsIsometricSMul G G] [ProperSpace G] [IsTopologicalGroup G]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  {Λ : ℝ≥0} {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H Exp)
  (hunimod : ∀ x : GroupLieAlgebra (𝓘(ℝ, EG)) G, LinearMap.trace ℝ _ (ad ℝ _ x) = 0)
  (eW : HeightSpace T.character ≃ₗ[ℝ] W) (π : G →* Multiplicative W)
  (hπExp : ∀ x, (π (Exp x)).toAdd = eW (heightProjection T.character x))
  (chartN : GroupLieAlgebra (𝓘(ℝ, F.N.modelSpace)) F.N.carrier ≃ₜ F.N.carrier)
  (hchartN : ∀ x, chartN x = F.ExpN x)
  (chartD : GroupLieAlgebra (𝓘(ℝ, F.D.modelSpace)) F.D.carrier ≃ₜ F.D.carrier)
  (hchartD : ∀ x, chartD x = F.ExpD x)
  (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
  (dynkinD : NilpotentDynkinExpansionInput F.D.modelSpace F.D.carrier)
  (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
  (haarD : NilpotentExponentialHaarInput F.D.modelSpace F.D.carrier)

set_option maxHeartbeats 1000000 in
include hπExp dynkinD haarN haarD in
theorem templateSupport_le_of_recurrent_good_profiles_sequence
    (scale : ℕ → ℝ) (hscale : Tendsto scale atTop atTop)
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (source E : Set W) (hE : IsCompact E) (hne : E.Nonempty) (w₀ : W)
    (β : M.Bases)
    (hβ : IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
      (M.boxCost T hunimod eW source) β.val)
    (x : ℕ → G) (d₀ : ℕ → F.D.carrier)
    (A Q : ℕ → Set F.N.carrier) (K₀ R₀ : ℕ → ℕ → Set F.N.carrier)
    (D : ℕ → ℕ → ℝ)
    (μ : Measure F.N.carrier) [SFinite μ] [μ.IsMulRightInvariant]
    (f : ℕ → NormalizedPair G Λ) (hΛ : 0 < (Λ : ℝ))
    (hφ : ∀ d, F.action d = M.adjointGroupAutomorphism T F.N.equiv F.ExpN F.isExpN
      (by rw [← show chartN = F.ExpN from funext hchartN]; exact chartN.bijective) dynkinN
      (cartanLog H F.D.equiv F.ExpD
        (by rw [← show chartD = F.ExpD from funext hchartD]; exact chartD.bijective) d))
    (hpath : ∀ g : G, ∃ γ : ℝ → G, γ 0 = 1 ∧ γ 1 = g ∧
      ∀ t ∈ Icc (0 : ℝ) 1, ∀ u ∈ Icc (0 : ℝ) 1,
        dist (γ t) (γ u) ≤ dist 1 g * |t - u|)
    {K : ℝ≥0} (hLip : LipschitzWith K (fun g => (π g).toAdd))
    {m c : ℕ} (aN : DynkinCoefficients c 2)
    (hm : ∀ u v, F.ExpN (finiteDynkinPolynomial aN ![u, v]) = F.ExpN u * F.ExpN v)
    (s : Fin M.letterCount → ℝ) (letters : Fin m → Fin M.letterCount)
    (sample : ℕ → ℕ → ℝ → F.N.carrier)
    (hsub : ∀ r j u v, sample r j u * (sample r j v)⁻¹ = sample r j (u - v))
    (hsample : ∀ r, ∀ j : Fin m, ∀ u, sample r j.val u =
      F.ExpN (F.N.equiv (u • (Real.exp (scale r * s (letters j)) • M.letter (letters j)))))
    (S : Set (((Fin (finrank ℝ (cartanRootIdeal H)) → ℝ) →L[ℝ]
      (Fin (finrank ℝ (cartanRootIdeal H)) → ℝ) →L[ℝ]
      (Fin (finrank ℝ (cartanRootIdeal H)) → ℝ)) ×
      (Fin M.letterCount → Fin (finrank ℝ (cartanRootIdeal H)) → ℝ)))
    (hS : IsCompact S)
    (hb : ∀ r, (basisBracket (M.boxBasis T hunimod eW source β (scale r)),
      fun i => (M.boxBasis T hunimod eW source β (scale r)).equivFun
        (Real.exp (scale r * s i) • M.letter i)) ∈ S)
    (b₁ : ((Fin (finrank ℝ (cartanRootIdeal H)) → ℝ) →L[ℝ]
      (Fin (finrank ℝ (cartanRootIdeal H)) → ℝ) →L[ℝ]
      (Fin (finrank ℝ (cartanRootIdeal H)) → ℝ)) ×
      (Fin M.letterCount → Fin (finrank ℝ (cartanRootIdeal H)) → ℝ))
    (hb₁ : b₁ ∈ S)
    (hlim : Tendsto (fun r => (basisBracket (M.boxBasis T hunimod eW source β (scale r)),
      fun i => (M.boxBasis T hunimod eW source β (scale r)).equivFun
        (Real.exp (scale r * s i) • M.letter i))) atTop (𝓝 b₁))
    (rem : RemezPolynomialInput) (hdim : 1 ≤ finrank ℝ (cartanRootIdeal H))
    (ρ : ℝ) (hρ : 1 ≤ ρ) (t₀ : Fin (m + m) → ℝ) (ht₀ : ‖t₀‖ ≤ ρ)
    (honto : Function.Surjective (fderiv ℝ (differenceAmplitudeWordEndpoint aN letters b₁) t₀))
    (σ : ℕ → ℕ → Measure F.N.carrier) [∀ r j, IsProbabilityMeasure (σ r j)]
    (hlaw : ∀ r j, MeasurePreserving (sample r j) (uniformIntervalLaw ρ) (σ r j))
    (hQfin : ∀ r, μ (Q r) ≠ ∞) (hQpos : ∀ r, 0 < (μ (Q r)).toReal)
    (hK₀ : ∀ r j, ∀ᵐ u ∂σ r j, u ∈ K₀ r j)
    (hRfin : ∀ r j, μ (R₀ r j) ≠ ∞) (hRpos : ∀ r j, 0 < (μ (R₀ r j)).toReal)
    (hQR : ∀ r j, ∀ u ∈ Q r, ∀ v ∈ K₀ r j, u * v ∈ R₀ r j)
    (hD : ∀ r j, 0 < D r j)
    (hdenom : ∀ r j, (μ (R₀ r j)).toReal ≤ D r j * (μ (Q r)).toReal)
    (hA : ∀ r, MeasurableSet (A r)) (hAQ : ∀ r, A r ⊆ Q r)
    (hApos : ∀ r, 0 < (μ (A r)).toReal)
    (hAlower : HasSubexponentialLowerBoundSeq scale
      (fun r => (μ (A r)).toReal / (μ (Q r)).toReal))
    (hDupper : ∀ j, j < m → HasSubexponentialUpperBoundSeq scale (fun r => D r j))
    (d : Fin m → ℝ → G) (hd : ∀ i, Continuous (d i)) (hd₀ : ∀ i, d i 0 = 1)
    (hf : ∀ r, ∀ i : Fin m, Continuous (fun t => F.inclusionN (sample r i.val t)))
    (hf₀ : ∀ r, ∀ i : Fin m, F.inclusionN (sample r i.val 0) = 1)
    (center : ℕ → W) (ζ : ℕ → ℝ) (hζ : Tendsto ζ atTop (𝓝 0))
    {speed switchError : ℝ} (hspeed : 0 ≤ speed) (hswitchError : 0 ≤ switchError)
    (hbase : ∀ η : ℝ, 0 < η → ∀ᶠ r in atTop, ∀ u ∈ A r,
      ∃ w ∈ E, ‖(π ((f r).val.1 (x r * F.inclusionN u * F.inclusionD (d₀ r)))).toAdd -
        center r - scale r • w‖ ≤ scale r * (ζ r + η))
    (hstart : ∀ η : ℝ, 0 < η → ∀ᶠ r in atTop, ∀ u ∈ A r,
      ‖(π ((f r).val.1 (x r * F.inclusionN u * F.inclusionD (d₀ r)))).toAdd -
        center r - scale r • w₀‖ ≤ scale r * (ζ r + η))
    (hleg : ∀ η : ℝ, 0 < η → ∀ᶠ r in atTop, ∀ u ∈ A r, ∀ i : Fin m,
      ∀ t : unitInterval, ∃ w ∈ E,
        ‖(π ((f r).val.1 ((x r * F.inclusionN u * F.inclusionD (d₀ r)) * d i (scale r * t)))).toAdd -
          center r - scale r • w‖ ≤ scale r * (ζ r + η))
    (hmetric : ∀ᶠ r in atTop, ∀ u ∈ A r, ∀ i : Fin m, ∀ b : ℝ,
      |b| ≤ 2 * ρ → u * sample r i.val b ∈ A r →
      PathMetricBound (supportVisitPath (d i) (hd i) (hd₀ i)
        (fun t => F.inclusionN (sample r i.val t)) (hf r i) (hf₀ r i)
        (x r * F.inclusionN u) (F.inclusionD (d₀ r)) (scale r) b)
        (speed * scale r) (speed * (1 + Real.log (2 + scale r))))
    (hswitch : ∀ᶠ r in atTop, ∀ u ∈ A r, ∀ i : Fin m, ∀ b : ℝ,
      |b| ≤ 2 * ρ → ∀ t : unitInterval,
      dist ((x r * F.inclusionN u) * F.inclusionN (sample r i.val ((t : ℝ) * b)) *
          (F.inclusionD (d₀ r) * d i (scale r)))
        ((x r * F.inclusionN u * F.inclusionD (d₀ r)) * d i (scale r)) ≤
          switchError * (1 + Real.log (2 + scale r)))
 :
    (M.supportIn T hunimod eW).templateSupport source ≤
      (M.supportIn T hunimod eW).templateSupport E := by
  let cN := chartN.symm.trans
    (finBasis ℝ (GroupLieAlgebra (𝓘(ℝ, F.N.modelSpace)) F.N.carrier)).equivFun.toContinuousLinearEquiv.toHomeomorph
  let : SecondCountableTopology F.N.carrier := cN.secondCountableTopology
  let : IsTopologicalGroup F.N.carrier := topologicalGroup_of_lieGroup (𝓘(ℝ, F.N.modelSpace)) ⊤
  obtain ⟨n₀, C, hn₀, hC, hvol, haccessible⟩ := recurrent_differenceWord_image_sequence
    scale hscale rem hdim aN letters S hS _ hb b₁ hb₁ hlim ρ hρ t₀ ht₀ honto
    μ sample σ hlaw Q A K₀ R₀ D hQfin hQpos hK₀ hRfin hRpos hQR hD hdenom
    hA hAQ hApos hAlower hDupper
  apply M.templateSupport_le_of_good_profile_paths_sequence T F hunimod eW π hπExp
    chartN hchartN chartD hchartD dynkinN dynkinD haarN haarD scale hscale
    b₀ source E hE hne w₀ β hβ C hC hvol x d₀ n₀ A hn₀ f hΛ hφ hpath hLip
    aN hm s letters sample hsub hsample d hd hd₀ hf hf₀ center ζ hζ
    hspeed hswitchError hbase _ hleg hmetric hswitch haccessible
  intro η hη
  filter_upwards [hstart η hη] with r hr
  exact hr (n₀ r) (hn₀ r)

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanSegmentCellPacking
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instDecidableEqConeMixedWords _root_.OAI.PolycyclicRecognition.CartanWordModel.instFintypeConeMixedWords _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_nonempty _root_.OAI.PolycyclicRecognition.finite_templateSymmetryGroup _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.instFiniteRootOffsetConeIndex _root_.OAI.PolycyclicRecognition.instFiniteSubtypeLinearEquivRealIdMemSubgroupLinearSupportSymmetryGroup _root_.OAI.PolycyclicRecognition.instNonemptyRootOffsetConeIndex _root_.OAI.PolycyclicRecognition.inversePairCoupling_finiteOnCompacts _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.CartanFactorModel.heightRay_zero _root_.OAI.PolycyclicRecognition.CartanFactorModel.realScaleProfile_apply _root_.OAI.PolycyclicRecognition.CartanFactorModel.sampledProbeProfile_apply _root_.OAI.PolycyclicRecognition.basisDynkinParameter_zero _root_.OAI.PolycyclicRecognition.bracketWordDifferential_mul _root_.OAI.PolycyclicRecognition.cartanWeightDerivation_apply_root _root_.OAI.PolycyclicRecognition.chartExponentialFlow_zero _root_.OAI.PolycyclicRecognition.derivationSemidirectHom_apply _root_.OAI.PolycyclicRecognition.dynkinRightTranslation_apply _root_.OAI.PolycyclicRecognition.dynkinRightTranslation_symm_apply _root_.OAI.PolycyclicRecognition.exponentialHomOfDynkin_apply_exp _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.modelNilradicalLinearAction_apply _root_.OAI.PolycyclicRecognition.modelNilradicalRotation_apply _root_.OAI.PolycyclicRecognition.modelNilradicalRotation_mul _root_.OAI.PolycyclicRecognition.modelNilradicalRotation_one _root_.OAI.PolycyclicRecognition.nilshadowWeightDerivation_symm _root_.OAI.PolycyclicRecognition.nilshadowWeightOperator_symm _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # From recurrent good sheets to the actual Cartan support inequality -/

noncomputable section

namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule MeasureTheory Filter Set
open scoped Manifold NNReal ENNReal Topology

variable {EG G W I : Type} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [IsIsometricSMul G G] [ProperSpace G] [IsTopologicalGroup G] [SimplyConnectedSpace G]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] [Fintype I] [DecidableEq I]
  {Λ : ℝ≥0} {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H Exp)
  (hunimod : ∀ x : GroupLieAlgebra (𝓘(ℝ, EG)) G, LinearMap.trace ℝ _ (ad ℝ _ x) = 0)
  (eW : HeightSpace T.character ≃ₗ[ℝ] W) (π : G →* Multiplicative W)
  (hπExp : ∀ x, (π (Exp x)).toAdd = eW (heightProjection T.character x))
  (chartN : GroupLieAlgebra (𝓘(ℝ, F.N.modelSpace)) F.N.carrier ≃ₜ F.N.carrier)
  (hchartN : ∀ x, chartN x = F.ExpN x)
  (chartD : GroupLieAlgebra (𝓘(ℝ, F.D.modelSpace)) F.D.carrier ≃ₜ F.D.carrier)
  (hchartD : ∀ x, chartD x = F.ExpD x)
  (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
  (dynkinD : NilpotentDynkinExpansionInput F.D.modelSpace F.D.carrier)
  (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
  (haarD : NilpotentExponentialHaarInput F.D.modelSpace F.D.carrier)

set_option maxHeartbeats 1000000 in
include hπExp dynkinN dynkinD haarN haarD in
/-- Whole good segment legs, the actual pivot visits and recurrent sheet volume
imply the support inequality. No separate path or switch estimate is assumed. -/
theorem templateSupport_le_of_recurrent_segment_cells_sequence_m_oai
    (hExp : IsGroupExponential Exp)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (scale : ℕ → ℝ) (hscale : Tendsto scale atTop atTop) (hscale1 : ∀ n, 1 ≤ scale n)
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (X : I → H) (SD : Finset (FreeMagma I)) (βD : WordBasisSelections X SD)
    (z : Fin (finrank ℝ H) → ℝ) (v : H) {T₀ : ℝ} (hT₀ : 0 < T₀)
    (source : Set W)
    (hsource : source = segment ℝ
      (eW (heightProjection T.character ((WordBasisSelections.basis X SD βD).equivFun.symm z :
        GroupLieAlgebra (𝓘(ℝ, EG)) G)))
      ((eW (heightProjection T.character ((WordBasisSelections.basis X SD βD).equivFun.symm z :
        GroupLieAlgebra (𝓘(ℝ, EG)) G))) +
        T₀ • eW (heightProjection T.character (v : GroupLieAlgebra (𝓘(ℝ, EG)) G))))
    (β : M.Bases)
    (hβ : IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
      (M.boxCost T hunimod eW source) β.val)
    (x : ℕ → G)
    (A Q : ℕ → Set F.N.carrier) (K₀ R₀ : ℕ → ℕ → Set F.N.carrier)
    (D : ℕ → ℕ → ℝ)
    (μ : Measure F.N.carrier) [SFinite μ] [μ.IsMulRightInvariant]
    (f : ℕ → NormalizedPair G Λ) (hΛ : 0 < (Λ : ℝ))
    (hpath : ∀ g : G, ∃ γ : ℝ → G, γ 0 = 1 ∧ γ 1 = g ∧
      ∀ t ∈ Icc (0 : ℝ) 1, ∀ u ∈ Icc (0 : ℝ) 1,
        dist (γ t) (γ u) ≤ dist 1 g * |t - u|)
    {K : ℝ≥0} (hLip : LipschitzWith K (fun g => (π g).toAdd))
    {m c : ℕ} (aN : DynkinCoefficients c 2)
    (hm : ∀ u v, F.ExpN (finiteDynkinPolynomial aN ![u, v]) = F.ExpN u * F.ExpN v)
    (letters : Fin m → Fin M.letterCount)
    (sample : ℕ → ℕ → ℝ → F.N.carrier)
    (hsub : ∀ r j u v, sample r j u * (sample r j v)⁻¹ = sample r j (u - v))
    (hsample : ∀ r, ∀ j : Fin m, ∀ u, sample r j.val u =
      F.ExpN (F.N.equiv (u • (Real.exp (scale r * (M.supportIn T hunimod eW).weightSupport source (letters j)) • M.letter (letters j)))))
    (S : Set (((Fin (finrank ℝ (cartanRootIdeal H)) → ℝ) →L[ℝ]
      (Fin (finrank ℝ (cartanRootIdeal H)) → ℝ) →L[ℝ]
      (Fin (finrank ℝ (cartanRootIdeal H)) → ℝ)) ×
      (Fin M.letterCount → Fin (finrank ℝ (cartanRootIdeal H)) → ℝ)))
    (hS : IsCompact S)
    (hb : ∀ r, (basisBracket (M.boxBasis T hunimod eW source β (scale r)),
      fun i => (M.boxBasis T hunimod eW source β (scale r)).equivFun
        (Real.exp (scale r * (M.supportIn T hunimod eW).weightSupport source i) • M.letter i)) ∈ S)
    (b₁ : ((Fin (finrank ℝ (cartanRootIdeal H)) → ℝ) →L[ℝ]
      (Fin (finrank ℝ (cartanRootIdeal H)) → ℝ) →L[ℝ]
      (Fin (finrank ℝ (cartanRootIdeal H)) → ℝ)) ×
      (Fin M.letterCount → Fin (finrank ℝ (cartanRootIdeal H)) → ℝ))
    (hb₁ : b₁ ∈ S)
    (hlim : Tendsto (fun r => (basisBracket (M.boxBasis T hunimod eW source β (scale r)),
      fun i => (M.boxBasis T hunimod eW source β (scale r)).equivFun
        (Real.exp (scale r * (M.supportIn T hunimod eW).weightSupport source i) • M.letter i))) atTop (𝓝 b₁))
    (rem : RemezPolynomialInput) (hdim : 1 ≤ finrank ℝ (cartanRootIdeal H))
    (ρ : ℝ) (hρ : 1 ≤ ρ) (t₀ : Fin (m + m) → ℝ) (ht₀ : ‖t₀‖ ≤ ρ)
    (honto : Function.Surjective (fderiv ℝ (differenceAmplitudeWordEndpoint aN letters b₁) t₀))
    (σ : ℕ → ℕ → Measure F.N.carrier) [∀ r j, IsProbabilityMeasure (σ r j)]
    (hlaw : ∀ r j, MeasurePreserving (sample r j) (uniformIntervalLaw ρ) (σ r j))
    (hQfin : ∀ r, μ (Q r) ≠ ∞) (hQpos : ∀ r, 0 < (μ (Q r)).toReal)
    (hK₀ : ∀ r j, ∀ᵐ u ∂σ r j, u ∈ K₀ r j)
    (hRfin : ∀ r j, μ (R₀ r j) ≠ ∞) (hRpos : ∀ r j, 0 < (μ (R₀ r j)).toReal)
    (hQR : ∀ r j, ∀ u ∈ Q r, ∀ v ∈ K₀ r j, u * v ∈ R₀ r j)
    (hD : ∀ r j, 0 < D r j)
    (hdenom : ∀ r j, (μ (R₀ r j)).toReal ≤ D r j * (μ (Q r)).toReal)
    (hA : ∀ r, MeasurableSet (A r)) (hAQ : ∀ r, A r ⊆ Q r)
    (hApos : ∀ r, 0 < (μ (A r)).toReal)
    (hAlower : HasSubexponentialLowerBoundSeq scale
      (fun r => (μ (A r)).toReal / (μ (Q r)).toReal))
    (hDupper : ∀ j, j < m → HasSubexponentialUpperBoundSeq scale (fun r => D r j))
    (g : ℝ → W) (hg : Continuous g)
    (center : ℕ → W) (ζ : ℕ → ℝ) (hζ : Tendsto ζ atTop (𝓝 0))
    (hgood : ∀ η : ℝ, 0 < η → ∀ᶠ r in atTop, ∀ u ∈ A r, ∀ t ∈ Icc 0 T₀,
      ‖(π ((f r).val.1 ((x r * F.inclusionN u *
        F.inclusionD (F.ExpD (F.D.equiv (wordChartPivot X SD βD (scale r) z)))) *
          F.inclusionD (F.ExpD (F.D.equiv ((scale r * t) • v)))))).toAdd -
        center r - scale r • g t‖ ≤ scale r * (ζ r + η)) :
    (M.supportIn T hunimod eW).templateSupport source ≤
      (M.supportIn T hunimod eW).templateSupport (g '' Icc 0 T₀) := by
  obtain ⟨⟨chartN, hchartN⟩, _⟩ := haarN.2 F.ExpN F.isExpN
    (F.N.tangent_nilpotent (cartanRootIdeal_nilpotent H T))
  obtain ⟨⟨chartD, hchartD⟩, _⟩ := haarD.2 F.ExpD F.isExpD
    (F.D.tangent_nilpotent inferInstance)
  let P := M.supportIn T hunimod eW
  let θ := P.segmentSupportTime (eW (heightProjection T.character v)) T₀
  let d : Fin m → ℝ → G := fun i t => Exp (t • (θ (letters i) • v : H))
  let d₀ : ℕ → F.D.carrier := fun n =>
    F.ExpD (F.D.equiv (wordChartPivot X SD βD (scale n) z))
  have hd (i : Fin m) : Continuous (d i) :=
    continuous_exp_line_of_published_realization T Exp hExp realize (θ (letters i) • v)
  have hd₀ (i : Fin m) : d i 0 = 1 := by simp [d, hExp.map_zero]
  have hsampleG (r : ℕ) (j : Fin m) (t : ℝ) :
      F.inclusionN (sample r j.val t) =
        Exp ((t * Real.exp (scale r * P.weightSupport source (letters j))) •
          (M.letter (letters j) : GroupLieAlgebra (𝓘(ℝ, EG)) G)) := by
    rw [hsample, F.compatibleN]
    simp only [SetLike.val_smul, smul_smul, P]
  have hf (r : ℕ) (j : Fin m) : Continuous (fun t => F.inclusionN (sample r j.val t)) := by
    have he := funext (hsampleG r j)
    rw [he]
    exact (continuous_exp_line_of_published_realization T Exp hExp realize (M.letter (letters j))).comp
      (continuous_id.mul_const _)
  have hf₀ (r : ℕ) (j : Fin m) : F.inclusionN (sample r j.val 0) = 1 := by
    simp [hsampleG, hExp.map_zero]
  have hvisit := M.exists_segment_sampled_visit_bound T F hExp realize haarD dynkinD
    hunimod eW π hπExp X SD βD z v hT₀.le (zero_le_one.trans hρ)
  dsimp only at hvisit
  rw [← hsource] at hvisit
  rcases hvisit with ⟨C, hC, hbound⟩
  have hmetrics : ∀ r u (i : Fin m) b, |b| ≤ 2 * ρ →
      PathMetricBound (supportVisitPath (d i) (hd i) (hd₀ i)
        (fun t => F.inclusionN (sample r i.val t)) (hf r i) (hf₀ r i)
        (x r * F.inclusionN u) (F.inclusionD (d₀ r)) (scale r) b)
        (C * scale r) (C * (1 + Real.log (2 + scale r))) := by
    intro r u i b hb
    have hh := (hbound (scale r) (hscale1 r) (x r * F.inclusionN u) (letters i) b hb).1
    intro t t'
    have he (s : unitInterval) := M.supportVisitPath_apply_eq_sampled T hExp realize
      (θ (letters i) • v) (letters i) (x r * F.inclusionN u) (F.inclusionD (d₀ r))
      (wordChartPivot X SD βD (scale r) z) (scale r) (P.weightSupport source (letters i)) b
      _ (hf r i) (hf₀ r i) (hsampleG r i) (hd i) (hd₀ i) (F.compatibleD _) s
    rw [he, he]
    exact hh t t'
  have hswitches : ∀ r u (i : Fin m) b, |b| ≤ 2 * ρ → ∀ t : unitInterval,
      dist ((x r * F.inclusionN u) * F.inclusionN (sample r i.val ((t : ℝ) * b)) *
          (F.inclusionD (d₀ r) * d i (scale r)))
        ((x r * F.inclusionN u * F.inclusionD (d₀ r)) * d i (scale r)) ≤
          C * (1 + Real.log (2 + scale r)) := by
    intro r u i b hb t
    have hh := (hbound (scale r) (hscale1 r) (x r * F.inclusionN u) (letters i) b hb).2
      t t.property 0 ⟨le_rfl, zero_le_one⟩
    simp only [zero_mul, zero_smul, hExp.map_zero, mul_one] at hh
    simp only [hsampleG, d₀, F.compatibleD, d, P, θ, SetLike.val_smul]
    have hle : C * Real.log (2 + scale r) ≤ C * (1 + Real.log (2 + scale r)) := by nlinarith
    simpa only [mul_assoc, SetLike.val_smul] using hh.trans hle
  have hgood' (η : ℝ) (hη : 0 < η) : ∀ᶠ r in atTop,
      (∀ u ∈ A r, ‖(π ((f r).val.1 (x r * F.inclusionN u * F.inclusionD (d₀ r)))).toAdd -
        center r - scale r • g 0‖ ≤ scale r * (ζ r + η)) ∧
      ∀ u ∈ A r, ∀ i : Fin m, ∀ t : unitInterval, ∃ w ∈ g '' Icc 0 T₀,
        ‖(π ((f r).val.1 ((x r * F.inclusionN u * F.inclusionD (d₀ r)) * d i (scale r * t)))).toAdd -
          center r - scale r • w‖ ≤ scale r * (ζ r + η) := by
    filter_upwards [hgood η hη] with r hr
    have hh := segment_profile_support_legs (F.ExpD ∘ F.D.equiv)
      (by simp [F.isExpD.map_zero]) F.inclusionN F.inclusionD
      (fun y => (π ((f r).val.1 y)).toAdd) (x r) (F.inclusionD (d₀ r)) (center r)
      (A r) (scale r) T₀ (scale r * (ζ r + η)) hT₀.le v (fun i : Fin m => θ (letters i))
      (fun i => P.segmentSupportTime_mem _ hT₀.le (letters i)) g hr
    simpa only [Function.comp_apply, F.compatibleD, d, d₀, SetLike.val_smul] using hh
  have hbase : ∀ η : ℝ, 0 < η → ∀ᶠ r in atTop, ∀ u ∈ A r,
      ∃ w ∈ g '' Icc 0 T₀,
        ‖(π ((f r).val.1 (x r * F.inclusionN u * F.inclusionD (d₀ r)))).toAdd -
          center r - scale r • w‖ ≤ scale r * (ζ r + η) := by
    intro η hη
    filter_upwards [hgood' η hη] with r hr u hu
    exact ⟨g 0, ⟨0, ⟨le_rfl, hT₀.le⟩, rfl⟩, hr.1 u hu⟩
  exact M.templateSupport_le_of_recurrent_good_profiles_sequence T F hunimod eW π hπExp
    chartN hchartN chartD hchartD dynkinN dynkinD haarN haarD scale hscale
    b₀ source (g '' Icc 0 T₀) (isCompact_Icc.image hg) ⟨g 0, 0, ⟨le_rfl, hT₀.le⟩, rfl⟩
    (g 0) β hβ x d₀ A Q K₀ R₀ D μ f hΛ
    (fun d => cartan_action_eq_adjoint_of_published_realization T M F hExp realize _ _ dynkinN d)
    hpath hLip aN hm (P.weightSupport source) letters sample hsub hsample S hS hb b₁ hb₁ hlim
    rem hdim ρ hρ t₀ ht₀ honto σ hlaw hQfin hQpos hK₀ hRfin hRpos hQR hD hdenom hA hAQ hApos
    hAlower hDupper d hd hd₀ hf hf₀ center ζ hζ hC hC hbase
    (fun η hη => (hgood' η hη).mono fun _ h => h.1)
    (fun η hη => (hgood' η hη).mono fun _ h => h.2)
    (Eventually.of_forall fun r u _ i b hb _ => hmetrics r u i b hb)
    (Eventually.of_forall fun r u _ i b hb => hswitches r u i b hb)

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

theorem solution : type_of% @OAI.PolycyclicRecognition.CartanWordModel.templateSupport_le_of_recurrent_segment_cells_sequence_m_oai := @OAI.PolycyclicRecognition.CartanWordModel.templateSupport_le_of_recurrent_segment_cells_sequence_m_oai
