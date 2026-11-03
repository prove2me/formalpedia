-- Prove2me | solution 1 for OAI.PolycyclicRecognition.supported_profile_increment_of_flow
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-02T23:45:05.17509+00:00
-- url     : https://prove2.me/submissions/a3ad96a2-5810-47fc-aecd-11e6c655d1a3

import Mathlib
import Definitions.Def_OAIQ093D010
import Definitions.Def_OAIQ093D011

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

variable {G : Type*} [Group G] [PseudoMetricSpace G] [IsIsometricSMul G G]

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
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_OccupationSampling
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual probability laws of independent chart samples -/

noncomputable section

namespace PolycyclicRecognition

open MeasureTheory Filter Set
open scoped Topology

/-- A density sample lies almost surely in every set outside which the
density vanishes. In particular its compact support carries the law. -/
theorem ae_mem_densityProbabilityMeasure
    {Z : Type*} [MeasurableSpace Z]
    (μ : Measure Z) (ρ : Z → ℝ) (hi : Integrable ρ μ)
    (hp : ∀ z, 0 ≤ ρ z) (hmass : ∫ z, ρ z ∂μ = 1)
    (K : Set Z) (hK : ∀ z, z ∉ K → ρ z = 0) :
    ∀ᵐ z ∂(densityProbabilityMeasure μ ρ hi hp hmass : Measure Z), z ∈ K := by
  change ∀ᵐ z ∂μ.withDensity (fun z => ENNReal.ofReal (ρ z)), z ∈ K
  rw [ae_withDensity_iff' hi.aestronglyMeasurable.aemeasurable.ennreal_ofReal]
  exact Eventually.of_forall (fun z hz => by
    by_contra hn
    exact hz (by rw [hK z hn, ENNReal.ofReal_zero]))

theorem productOccupationLaw_coe {A D X : Type*}
    [MeasurableSpace A] [MeasurableSpace D] [MeasurableSpace X]
    (μ : ProbabilityMeasure A) (ν : ProbabilityMeasure D) {p : A × D → X}
    (hp : AEMeasurable p ((μ : Measure A).prod (ν : Measure D))) :
    (productOccupationLaw μ ν p : Measure X) = Measure.map p ((μ : Measure A).prod (ν : Measure D)) := by
  unfold productOccupationLaw
  simp only [hp, ↓reduceDIte]
  rfl

/-- Fubini's formula for a bounded continuous observable of a chart sample. -/
theorem integral_productOccupationLaw
    {A D X : Type*} [MeasurableSpace A] [MeasurableSpace D]
    [TopologicalSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
    (μ : ProbabilityMeasure A) (ν : ProbabilityMeasure D)
    (p : A × D → X) (hp : Measurable p) (f : C(X, ℝ)) :
    (∫ x, f x ∂(productOccupationLaw μ ν p : Measure X)) =
      ∫ a, ∫ d, f (p (a, d)) ∂(ν : Measure D) ∂(μ : Measure A) := by
  rw [productOccupationLaw_coe μ ν hp.aemeasurable]
  rw [integral_map hp.aemeasurable f.continuous.aestronglyMeasurable]
  apply integral_prod
  exact Integrable.of_bound (f.continuous.measurable.comp hp).aestronglyMeasurable
    ‖f‖ (Eventually.of_forall (fun z => f.norm_coe_le_norm (p z)))

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_OccupationDomination
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Domination of translated chart samples by one occupation law -/

noncomputable section

namespace PolycyclicRecognition

open MeasureTheory Set
open scoped NNReal ENNReal

/-- The density comparison is made before projecting the coordinates. A
measure-preserving coordinate move therefore retains the same bound after
pushforward, without any injectivity requirement on the chart. -/
theorem map_densityProbabilityMeasure_le
    {D : Type*} [MeasurableSpace D] (m : Measure D)
    (η ρ : D → ℝ) (hiη : Integrable η m) (hiρ : Integrable ρ m)
    (hpη : ∀ z, 0 ≤ η z) (hpρ : ∀ z, 0 ≤ ρ z)
    (hmη : ∫ z, η z ∂m = 1) (hmρ : ∫ z, ρ z ∂m = 1)
    (hρ : Measurable ρ) (T : D → D) (hT : MeasurePreserving T m m)
    (c : ℝ≥0) (hbound : ∀ z, η z ≤ (c : ℝ) * ρ (T z)) :
    Measure.map T (densityProbabilityMeasure m η hiη hpη hmη : Measure D) ≤
      c • (densityProbabilityMeasure m ρ hiρ hpρ hmρ : Measure D) := by
  apply Measure.le_iff.mpr
  intro s hs
  change Measure.map T (m.withDensity (fun z => ENNReal.ofReal (η z))) s ≤
    (c • m.withDensity (fun z => ENNReal.ofReal (ρ z))) s
  rw [Measure.map_apply hT.measurable hs, Measure.smul_apply,
    withDensity_apply _ (hT.measurable hs), withDensity_apply _ hs]
  calc
    _ ≤ ∫⁻ z in T ⁻¹' s, (c : ℝ≥0∞) * ENNReal.ofReal (ρ (T z)) ∂m := by
      apply lintegral_mono
      intro z
      simpa only [ENNReal.ofReal_mul c.coe_nonneg, ENNReal.ofReal_coe_nnreal]
        using ENNReal.ofReal_le_ofReal (hbound z)
    _ = (c : ℝ≥0∞) * ∫⁻ z in T ⁻¹' s, ENNReal.ofReal (ρ (T z)) ∂m :=
      lintegral_const_mul _ ((hρ.comp hT.measurable).ennreal_ofReal)
    _ = _ := by rw [hT.setLIntegral_comp_preimage hs hρ.ennreal_ofReal]; rfl

/-- A uniform upper bound on the initial density and a positive lower bound
on the swept support give the coordinate density comparison. -/
theorem density_bound_on_swept_support
    {D : Type*} (η ρ : D → ℝ) (T : D → D) (K : Set D)
    {A b : ℝ} (hA : 0 ≤ A) (hb : 0 < b)
    (hη : ∀ z, η z ≤ A) (hρ : ∀ z, 0 ≤ ρ z)
    (hsupp : ∀ z, η z ≠ 0 → T z ∈ K) (hlower : ∀ z ∈ K, b ≤ ρ z) :
    ∀ z, η z ≤ (A / b) * ρ (T z) := by
  intro z
  by_cases hz : η z = 0
  · rw [hz]
    exact mul_nonneg (div_nonneg hA hb.le) (hρ _)
  · calc
      η z ≤ A := hη z
      _ = (A / b) * b := (div_mul_cancel₀ A hb.ne').symm
      _ ≤ _ := mul_le_mul_of_nonneg_left (hlower _ (hsupp z hz)) (div_nonneg hA hb.le)

/-- Domination in the second sampling coordinate passes through the actual
chart and its exact action identity. -/
theorem map_productOccupationLaw_le
    {A D X : Type*} [MeasurableSpace A] [MeasurableSpace D] [MeasurableSpace X]
    (μ : ProbabilityMeasure A) (σ ν : ProbabilityMeasure D)
    (p : A × D → X) (hp : Measurable p)
    (T : D → D) (hT : Measurable T) (act : X → X) (hact : Measurable act)
    (hmove : ∀ a z, act (p (a, z)) = p (a, T z))
    (c : ℝ≥0) (hdom : Measure.map T (σ : Measure D) ≤ c • (ν : Measure D)) :
    Measure.map act (productOccupationLaw μ σ p : Measure X) ≤
      c • (productOccupationLaw μ ν p : Measure X) := by
  rw [productOccupationLaw_coe μ σ hp.aemeasurable, productOccupationLaw_coe μ ν hp.aemeasurable]
  change Measure.map act (Measure.map p ((μ : Measure A).prod (σ : Measure D))) ≤
    c • Measure.map p ((μ : Measure A).prod (ν : Measure D))
  have heq : act ∘ p = p ∘ Prod.map id T := by
    funext z
    exact hmove z.1 z.2
  rw [Measure.map_map hact hp, heq,
    ← Measure.map_map hp (measurable_id.prodMap hT),
    ← Measure.map_prod_map (μ : Measure A) (σ : Measure D) measurable_id hT,
    Measure.map_id]
  have h := Measure.map_mono (Measure.prod_mono (le_refl (μ : Measure A)) hdom) hp
  rw [Measure.prod_smul_right, Measure.map_smul] at h
  exact h

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_OccupationLimitSelection
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Selecting one occupation limit while preserving the profile limit -/

namespace PolycyclicRecognition

open Filter MeasureTheory Set
open scoped Topology

/-- Compactness selects a single occupation limit on a finer filter, and
every already established profile limit is retained. The filter and the
occupation measure are selected before any microstep length. -/
theorem exists_occupation_limit_preserving
    {X Y ι : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [MeasurableSpace X] [BorelSpace X] [TopologicalSpace Y]
    {l : Filter ι} [l.NeBot] (μs : ι → ProbabilityMeasure X)
    {profiles : ι → Y} {ν : Y} (hν : Tendsto profiles l (𝓝 ν)) :
    ∃ (u : Ultrafilter ι) (μ : ProbabilityMeasure X),
      (u : Filter ι) ≤ l ∧ Tendsto μs u (𝓝 μ) ∧ Tendsto profiles u (𝓝 ν) := by
  obtain ⟨μ, _, hμ⟩ := (isCompact_univ : IsCompact (univ : Set (ProbabilityMeasure X))).exists_mapClusterPt
    (show Filter.map μs l ≤ 𝓟 univ by simp)
  obtain ⟨u, hul, huμ⟩ := mapClusterPt_iff_ultrafilter.mp hμ
  exact ⟨u, μ, hul, huμ, hν.mono_left hul⟩

end PolycyclicRecognition

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

variable {G : Type*} [Group G] [PseudoMetricSpace G] [IsIsometricSMul G G]

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
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CoarseFlowBounds
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_nonempty _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform coarse bounds along actual one-parameter subgroups

Continuity and the homomorphism law suffice for the path-mesh estimates.
The additive constant accommodates short parameter intervals without an
extra Riemannian regularity assumption on the ambient metric.
-/

noncomputable section

namespace PolycyclicRecognition

open Set

variable {G : Type*} [Group G] [PseudoMetricSpace G] [IsIsometricSMul G G]

theorem continuous_flow_coarse_bound (d : ℝ → G) (hd : Continuous d) (hzero : d 0 = 1)
    (hmul : ∀ s t, d (s + t) = d s * d t) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, dist 1 (d t) ≤ C * (1 + |t|) := by
  obtain ⟨C, hC⟩ := (isCompact_Icc : IsCompact (Icc (-1 : ℝ) 1)).bddAbove_image
    (continuous_const.dist hd).continuousOn
  have hC0 : 0 ≤ C := by
    have hh := hC (mem_image_of_mem (fun t => dist (1 : G) (d t))
      (show (0 : ℝ) ∈ Icc (-1 : ℝ) 1 by constructor <;> norm_num))
    simpa [hzero] using hh
  have hpower (s : ℝ) (n : ℕ) : d ((n : ℝ) * s) = d s ^ n := by
    induction n with
    | zero => simp [hzero]
    | succ n ih => rw [Nat.cast_succ, add_mul, one_mul, hmul, ih, pow_succ]
  refine ⟨C, hC0, ?_⟩
  intro t
  let n := ⌊|t|⌋₊ + 1
  have hn : 0 < (n : ℝ) := by exact_mod_cast (Nat.succ_pos ⌊|t|⌋₊)
  have htn : |t| ≤ (n : ℝ) := by simpa [n] using (Nat.lt_floor_add_one |t|).le
  have hnt : (n : ℝ) ≤ |t| + 1 := by
    simpa [n] using add_le_add_right (Nat.floor_le (abs_nonneg t)) 1
  have hsabs : |t / n| ≤ 1 := by
    rw [abs_div, abs_of_pos hn]
    exact (div_le_one hn).mpr htn
  have hs : t / n ∈ Icc (-1 : ℝ) 1 := abs_le.mp hsabs
  have hlocal : dist 1 (d (t / n)) ≤ C := hC (mem_image_of_mem _ hs)
  have he : d t = d (t / n) ^ n := by
    convert hpower (t / n) n using 1
    all_goals try with_reducible_and_instances rfl
    field_simp
  rw [he]
  exact (dist_one_pow_le _ _).trans ((mul_le_mul_of_nonneg_left hlocal hn.le).trans
    (by nlinarith))

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_PairMeanControl
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.inversePairCoupling_finiteOnCompacts _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Metric control of the actual stationary mean

The common Lipschitz constant of normalized pairs bounds their height
profiles, and hence bounds the homomorphism obtained by integration.
Consequently the actual averaged homomorphism kills every root flow.
-/

noncomputable section

namespace PolycyclicRecognition

open MeasureTheory LieAlgebra LieModule
open scoped NNReal Manifold

section Mean

variable {G W : Type*} [Group G] [MetricSpace G] [ProperSpace G]
  [IsTopologicalGroup G] [IsIsometricSMul G G]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
  {Λ K : ℝ≥0}

omit [ProperSpace G] [IsTopologicalGroup G] [IsIsometricSMul G G]
  [NormedSpace ℝ W] [CompleteSpace W] in
/-- Pointwise height control uses the forward normalization at the identity. -/
theorem norm_pairHeight_le (π : G →* Multiplicative W)
    (hπ : LipschitzWith K (fun g => (π g).toAdd))
    (g : G) (p : NormalizedPair G Λ) :
    ‖pairHeight π g p‖ ≤ (K : ℝ) * Λ * dist 1 g := by
  have h₁ := hπ.dist_le_mul (p.val.1 g) (p.val.1 1)
  have h₂ := p.property.1.1.dist_le_mul g 1
  rw [p.property.2] at h₂
  rw [p.property.2, map_one] at h₁
  change dist (pairHeight π g p) 0 ≤ _ at h₁
  rw [dist_zero_right] at h₁
  exact h₁.trans (by simpa only [dist_comm, mul_assoc] using
    mul_le_mul_of_nonneg_left h₂ K.coe_nonneg)

attribute [local instance] stationaryL2Action

end Mean

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_PairLabelFunctions
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.inversePairCoupling_finiteOnCompacts _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Continuous uniformly bounded label-distance observables -/

noncomputable section

namespace PolycyclicRecognition

open Metric
open scoped NNReal ENNReal

variable {G W : Type*} [Group G] [MetricSpace G] [ProperSpace G]
  [IsTopologicalGroup G] [IsIsometricSMul G G]
  [NormedAddCommGroup W] [NormedSpace ℝ W] {Λ K : ℝ≥0}

omit [IsTopologicalGroup G] [IsIsometricSMul G G] in
/-- For each fixed scale the observable is continuous on the compact pair section. -/
theorem continuous_pair_label_distance
    (π : G →* Multiplicative W) (hπ : Continuous fun g => (π g).toAdd)
    (g : G) (r : ℝ) (S : Set W) :
    Continuous (fun p : NormalizedPair G Λ => infDist (r⁻¹ • pairHeight π g p) S) :=
  (continuous_infDist_pt S).comp ((pairHeightProfile π hπ g).continuous.const_smul _)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_ConvexMicrosteps
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Convex control of the actual microstep sum

The unfinished final microstep is filled with one fixed label. Its cost is
explicit, so the number of full steps need not divide the total time.
-/

noncomputable section

namespace PolycyclicRecognition

open scoped BigOperators
open Metric Set

/-- The convex error of a weighted sum is bounded by the sum of its label
errors and the exact remainder error. The labels are chosen only in a finite
sum; no measurable choice is used. -/
theorem infDist_weighted_sum_le
    {ι W : Type*} [Fintype ι] [NormedAddCommGroup W] [NormedSpace ℝ W]
    {S : Set W} (hS : IsCompact S) {w₀ : W} (hw₀ : w₀ ∈ S)
    (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) (hsum : ∑ i, a i ≤ 1)
    (x : ι → W) (e : W) :
    infDist ((∑ i, a i • x i) + e) (convexHull ℝ S) ≤
      (∑ i, a i * infDist (x i) S) + ‖e - (1 - ∑ i, a i) • w₀‖ := by
  choose y hy hdist using fun i => hS.exists_infDist_eq_dist ⟨w₀, hw₀⟩ (x i)
  let b : Option ι → ℝ := fun i => i.elim (1 - ∑ i, a i) a
  let z : Option ι → W := fun i => i.elim w₀ y
  have hb : ∀ i, 0 ≤ b i := by
    intro i
    cases i with
    | none => exact sub_nonneg.mpr hsum
    | some i => exact ha i
  have hb1 : ∑ i, b i = 1 := by simp [b, Fintype.sum_option]
  have hz : ∀ i, z i ∈ convexHull ℝ S := by
    intro i
    apply subset_convexHull
    cases i with
    | none => exact hw₀
    | some i => exact hy i
  have hmem := (convex_convexHull ℝ S).sum_mem
    (t := Finset.univ) (w := b) (z := z) (fun i _ => hb i) hb1 (fun i _ => hz i)
  have hmem' : (∑ i, a i • y i) + (1 - ∑ i, a i) • w₀ ∈ convexHull ℝ S := by
    simpa only [b, z, Fintype.sum_option, Option.elim_none, Option.elim_some, add_comm] using hmem
  calc
    _ ≤ dist ((∑ i, a i • x i) + e)
        ((∑ i, a i • y i) + (1 - ∑ i, a i) • w₀) := infDist_le_dist_of_mem hmem'
    _ = ‖(∑ i, a i • (x i - y i)) + (e - (1 - ∑ i, a i) • w₀)‖ := by
      rw [dist_eq_norm]
      congr 1
      simp only [smul_sub, Finset.sum_sub_distrib]
      abel
    _ ≤ ‖∑ i, a i • (x i - y i)‖ + ‖e - (1 - ∑ i, a i) • w₀‖ := norm_add_le _ _
    _ ≤ (∑ i, ‖a i • (x i - y i)‖) + ‖e - (1 - ∑ i, a i) • w₀‖ :=
      add_le_add (norm_sum_le _ _) le_rfl
    _ = _ := by
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (ha i), hdist i, dist_eq_norm]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_PairMicrosteps
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.inversePairCoupling_finiteOnCompacts _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact normalized pair-height microsteps

The inverse power in the normalized left action records the original right
translation of the sampling point. The final group remainder is retained.
-/

noncomputable section

namespace PolycyclicRecognition

open Metric Set
open scoped BigOperators NNReal

variable {G W : Type*} [Group G] [MetricSpace G]
  [IsTopologicalGroup G] [IsIsometricSMul G G]
  [NormedAddCommGroup W] [NormedSpace ℝ W] {Λ K : ℝ≥0}

omit [NormedSpace ℝ W] in
/-- The actual height cocycle telescopes along successive right microsteps. -/
theorem pairHeight_pow_sum (π : G →* Multiplicative W) (g : G)
    (p : NormalizedPair G Λ) (n : ℕ) :
    pairHeight π (g ^ n) p =
      ∑ j ∈ Finset.range n, pairHeight π g ((g ^ j)⁻¹ • p) := by
  induction n with
  | zero => simp [pairHeight, p.property.2]
  | succ n ih =>
    rw [pow_succ, pairHeight_cocycle, ih, Finset.sum_range_succ]

omit [NormedSpace ℝ W] in
/-- Keep the final incomplete step in the telescoping identity. -/
theorem pairHeight_pow_mul (π : G →* Multiplicative W) (g h : G)
    (p : NormalizedPair G Λ) (n : ℕ) :
    pairHeight π (g ^ n * h) p =
      (∑ j : Fin n, pairHeight π g ((g ^ (j : ℕ))⁻¹ • p)) +
        pairHeight π h ((g ^ n)⁻¹ • p) := by
  rw [pairHeight_cocycle, pairHeight_pow_sum]
  congr 1
  exact (Fin.sum_univ_eq_sum_range (fun j => pairHeight π g ((g ^ j)⁻¹ • p)) n).symm

/-- The convex distance estimate for the exact microstep decomposition, before
bounding the final incomplete step by the Lipschitz constant. -/
theorem normalized_pair_microsteps_convex_bound
    (π : G →* Multiplicative W) (g h : G) (p : NormalizedPair G Λ)
    (n : ℕ) {L t : ℝ} (hL : 0 < L) (ht : 0 < t) (hn : (n : ℝ) * L ≤ t)
    {S : Set W} (hS : IsCompact S) {w₀ : W} (hw₀ : w₀ ∈ S) :
    infDist (t⁻¹ • pairHeight π (g ^ n * h) p) (convexHull ℝ S) ≤
      (L / t) * (∑ j : Fin n,
        infDist (L⁻¹ • pairHeight π g ((g ^ (j : ℕ))⁻¹ • p)) S) +
      ‖t⁻¹ • pairHeight π h ((g ^ n)⁻¹ • p) - (1 - (n : ℝ) * (L / t)) • w₀‖ := by
  have ha : (∑ _j : Fin n, L / t) ≤ 1 := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [← mul_div_assoc]
    exact (div_le_one ht).mpr hn
  have h := infDist_weighted_sum_le hS hw₀ (fun _ : Fin n => L / t)
    (fun _ => (div_pos hL ht).le) ha
    (fun j => L⁻¹ • pairHeight π g ((g ^ (j : ℕ))⁻¹ • p))
    (t⁻¹ • pairHeight π h ((g ^ n)⁻¹ • p))
  have hscale : (L / t) * L⁻¹ = t⁻¹ := by field_simp
  simpa only [smul_smul, hscale, ← Finset.smul_sum, ← smul_add,
    ← pairHeight_pow_mul, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, ← Finset.mul_sum] using h

/-- Lipschitz height control makes the incomplete microstep cost at most its
relative length times one fixed constant. -/
theorem normalized_pair_microsteps_convex_bound_of_remainder
    (π : G →* Multiplicative W) (hπ : LipschitzWith K (fun g => (π g).toAdd))
    (g h : G) (p : NormalizedPair G Λ) (n : ℕ)
    {L t D : ℝ} (hL : 0 < L) (ht : 0 < t) (_hD : 0 ≤ D)
    (hn : (n : ℝ) * L ≤ t) (hn' : t ≤ ((n : ℝ) + 1) * L)
    (hrem : dist 1 h ≤ D * L)
    {S : Set W} (hS : IsCompact S) {w₀ : W} (hw₀ : w₀ ∈ S) :
    infDist (t⁻¹ • pairHeight π (g ^ n * h) p) (convexHull ℝ S) ≤
      (L / t) * (∑ j : Fin n,
        infDist (L⁻¹ • pairHeight π g ((g ^ (j : ℕ))⁻¹ • p)) S) +
      (L / t) * ((K : ℝ) * Λ * D + ‖w₀‖) := by
  have heq : 1 - (n : ℝ) * (L / t) = (t - (n : ℝ) * L) / t := by
    field_simp
  have hpos : 0 ≤ 1 - (n : ℝ) * (L / t) := by
    rw [heq]
    exact div_nonneg (sub_nonneg.mpr hn) ht.le
  have hsmall : 1 - (n : ℝ) * (L / t) ≤ L / t := by
    rw [heq]
    apply div_le_div_of_nonneg_right _ ht.le
    nlinarith
  have hnorm : ‖t⁻¹ • pairHeight π h ((g ^ n)⁻¹ • p)‖ ≤
      (L / t) * ((K : ℝ) * Λ * D) := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr ht)]
    calc
      _ ≤ t⁻¹ * ((K : ℝ) * Λ * dist 1 h) :=
        mul_le_mul_of_nonneg_left (norm_pairHeight_le π hπ h _) (inv_nonneg.mpr ht.le)
      _ ≤ t⁻¹ * ((K : ℝ) * Λ * (D * L)) := by gcongr
      _ = _ := by ring
  apply (normalized_pair_microsteps_convex_bound π g h p n hL ht hn hS hw₀).trans
  apply add_le_add le_rfl
  calc
    _ ≤ ‖t⁻¹ • pairHeight π h ((g ^ n)⁻¹ • p)‖ +
        ‖(1 - (n : ℝ) * (L / t)) • w₀‖ := norm_sub_le _ _
    _ ≤ (L / t) * ((K : ℝ) * Λ * D) + (L / t) * ‖w₀‖ := by
      have hw : ‖(1 - (n : ℝ) * (L / t)) • w₀‖ ≤ (L / t) * ‖w₀‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hpos]
        exact mul_le_mul_of_nonneg_right hsmall (norm_nonneg _)
      exact add_le_add hnorm hw
    _ = _ := by ring

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_OccupationMicrosteps
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.inversePairCoupling_finiteOnCompacts _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Microstep estimates under dominated occupation laws

The sampling calculation supplies domination of the translated laws. This
file applies that domination to the exact normalized height increments.
-/

namespace PolycyclicRecognition

open MeasureTheory Metric Set
open scoped NNReal BigOperators

/-- Domination of a pushed sampling law controls every nonnegative continuous
observable on the compact section. -/
theorem integral_comp_le_of_map_le
    {X : Type*} [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X]
    (σ μ : Measure X) [IsFiniteMeasure σ] [IsFiniteMeasure μ]
    (T : X → X) (hT : Continuous T) {c : ℝ≥0}
    (hdom : Measure.map T σ ≤ c • μ)
    (f : X → ℝ) (hf : Continuous f) (hpos : ∀ x, 0 ≤ f x) :
    ∫ x, f (T x) ∂σ ≤ (c : ℝ) * ∫ x, f x ∂μ := by
  calc
    _ = ∫ x, f x ∂Measure.map T σ :=
      (integral_map hT.measurable.aemeasurable hf.aestronglyMeasurable).symm
    _ ≤ ∫ x, f x ∂c • μ := integral_mono_measure hdom
      (Filter.Eventually.of_forall hpos)
      (hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    _ = _ := by rw [integral_smul_nnreal_measure]; rfl

variable {G W : Type*} [Group G] [MetricSpace G] [ProperSpace G]
  [IsTopologicalGroup G] [IsIsometricSMul G G]
  [NormedAddCommGroup W] [NormedSpace ℝ W] {Λ K : ℝ≥0}
  [MeasurableSpace (NormalizedPair G Λ)] [BorelSpace (NormalizedPair G Λ)]

/-- The mean convex error of a long increment is bounded by one fixed-length
occupation observable and the explicit final-step error. -/
theorem integral_normalized_microsteps_le
    (σ μ : Measure (NormalizedPair G Λ)) [IsProbabilityMeasure σ] [IsProbabilityMeasure μ]
    (π : G →* Multiplicative W) (hπ : LipschitzWith K (fun g => (π g).toAdd))
    (g h : G) (n : ℕ) {c : ℝ≥0}
    (hdom : ∀ j : Fin n, Measure.map (fun p : NormalizedPair G Λ => (g ^ (j : ℕ))⁻¹ • p) σ ≤ c • μ)
    {L t D : ℝ} (hL : 0 < L) (ht : 0 < t) (hD : 0 ≤ D)
    (hn : (n : ℝ) * L ≤ t) (hn' : t ≤ ((n : ℝ) + 1) * L)
    (hrem : dist 1 h ≤ D * L)
    {S : Set W} (hS : IsCompact S) {w₀ : W} (hw₀ : w₀ ∈ S) :
    ∫ p, infDist (t⁻¹ • pairHeight π (g ^ n * h) p) (convexHull ℝ S) ∂σ ≤
      (c : ℝ) * (∫ p, infDist (L⁻¹ • pairHeight π g p) S ∂μ) +
        (L / t) * ((K : ℝ) * Λ * D + ‖w₀‖) := by
  let d : NormalizedPair G Λ → ℝ := fun p => infDist (L⁻¹ • pairHeight π g p) S
  have hd : Continuous d := continuous_pair_label_distance π hπ.continuous g L S
  have hj (j : Fin n) :
      ∫ p, d ((g ^ (j : ℕ))⁻¹ • p) ∂σ ≤ (c : ℝ) * ∫ p, d p ∂μ :=
    integral_comp_le_of_map_le σ μ _ (continuous_const_smul _) (hdom j) d hd
      (fun _ => infDist_nonneg)
  have hji (j : Fin n) : Integrable (fun p => d ((g ^ (j : ℕ))⁻¹ • p)) σ :=
    (hd.comp (continuous_const_smul _)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hleft := (continuous_pair_label_distance π hπ.continuous (g ^ n * h) t
    (convexHull ℝ S)).integrable_of_hasCompactSupport (μ := σ)
      (HasCompactSupport.of_compactSpace _)
  have hsumI : Integrable (fun p => ∑ j : Fin n, d ((g ^ (j : ℕ))⁻¹ • p)) σ :=
    integrable_finsetSum Finset.univ (fun j _ => hji j)
  let E := (L / t) * ((K : ℝ) * Λ * D + ‖w₀‖)
  have hb := integral_mono hleft ((hsumI.const_mul (L / t)).add (integrable_const E))
    (fun p => normalized_pair_microsteps_convex_bound_of_remainder
      π hπ g h p n hL ht hD hn hn' hrem hS hw₀)
  simp only [Pi.add_apply] at hb
  rw [integral_add (hsumI.const_mul _) (integrable_const E), integral_const_mul,
    integral_finsetSum Finset.univ (fun j _ => hji j), integral_const] at hb
  simp only [measureReal_def, measure_univ, ENNReal.toReal_one, one_smul] at hb
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun j _ => hj j)
  have hcoef : (L / t) * (n : ℝ) ≤ 1 := by
    rw [mul_comm, ← mul_div_assoc]
    exact (div_le_one ht).mpr hn
  have hI : 0 ≤ (c : ℝ) * ∫ p, d p ∂μ :=
    mul_nonneg c.coe_nonneg (integral_nonneg (fun _ => infDist_nonneg))
  apply hb.trans
  apply add_le_add _ le_rfl
  calc
    (L / t) * ∑ j : Fin n, ∫ p, d ((g ^ (j : ℕ))⁻¹ • p) ∂σ
        ≤ (L / t) * ∑ _j : Fin n, (c : ℝ) * ∫ p, d p ∂μ :=
          mul_le_mul_of_nonneg_left hsum (div_pos hL ht).le
    _ = ((L / t) * (n : ℝ)) * ((c : ℝ) * ∫ p, d p ∂μ) := by simp <;> ring
    _ ≤ _ := by simpa using mul_le_mul_of_nonneg_right hcoef hI

end PolycyclicRecognition

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_OccupationMicrostepLimit
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_nonempty _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.inversePairCoupling_finiteOnCompacts _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The two successive limits in the convex increment argument -/

noncomputable section

namespace PolycyclicRecognition

open MeasureTheory Filter Metric Set
open scoped NNReal Topology

variable {G W : Type*} [Group G] [MetricSpace G] [ProperSpace G]
  [IsTopologicalGroup G] [IsIsometricSMul G G]
  [NormedAddCommGroup W] [NormedSpace ℝ W] {Λ K : ℝ≥0}
  [MeasurableSpace (NormalizedPair G Λ)] [BorelSpace (NormalizedPair G Λ)]

/-- First take the chart scale to infinity for a fixed integer microstep,
then take the microstep length to infinity for the single limiting law.
No rate of stationary convergence uniform over probabilities is used. -/
theorem normalized_microstep_error_tendsto_zero
    {ι : Type*} {l : Filter ι}
    (π : G →* Multiplicative W) (hπ : LipschitzWith K (fun g => (π g).toAdd))
    (σ μs : ι → ProbabilityMeasure (NormalizedPair G Λ))
    (μ : ProbabilityMeasure (NormalizedPair G Λ))
    (hμ : Tendsto μs l (𝓝 μ))
    (t : ι → ℝ) (ht : Tendsto t l atTop)
    (endpoint : ι → G) (g : ℕ → G) (n : ℕ → ι → ℕ) (h : ℕ → ι → G)
    (c : ℝ≥0) {D : ℝ} (hD : 0 ≤ D)
    (hsteps : ∀ L : ℕ, 0 < L → ∀ᶠ r in l,
      0 < t r ∧ (n L r : ℝ) * L ≤ t r ∧ t r ≤ ((n L r : ℝ) + 1) * L ∧
      dist 1 (h L r) ≤ D * L ∧ g L ^ n L r * h L r = endpoint r ∧
      ∀ j : Fin (n L r), Measure.map
        (fun p : NormalizedPair G Λ => (g L ^ (j : ℕ))⁻¹ • p) (σ r : Measure _) ≤
          c • (μs r : Measure _))
    {S : Set W} (hS : IsCompact S) {w₀ : W} (hw₀ : w₀ ∈ S)
    (hstationary : Tendsto (fun L : ℕ => ∫ p : NormalizedPair G Λ,
      infDist ((L : ℝ)⁻¹ • pairHeight π (g L) p) S ∂(μ : Measure _)) atTop (𝓝 0)) :
    Tendsto (fun r => ∫ p : NormalizedPair G Λ,
      infDist ((t r)⁻¹ • pairHeight π (endpoint r) p) (convexHull ℝ S)
        ∂(σ r : Measure _)) l (𝓝 0) := by
  apply tendsto_order.2
  constructor
  · intro a ha
    exact Eventually.of_forall (fun r => ha.trans_le (integral_nonneg (fun _ => infDist_nonneg)))
  · intro b hb
    have hstat := hstationary.const_mul (c : ℝ)
    simp only [mul_zero] at hstat
    have hsmall := hstat.eventually (eventually_lt_nhds (half_pos hb))
    obtain ⟨L, hL, hLb⟩ := ((eventually_gt_atTop (0 : ℕ)).and hsmall).exists
    let dL : C(NormalizedPair G Λ, ℝ) :=
      ⟨fun p => infDist ((L : ℝ)⁻¹ • pairHeight π (g L) p) S,
        continuous_pair_label_distance π hπ.continuous (g L) L S⟩
    have hint := (ProbabilityMeasure.continuous_integral_continuousMap dL).tendsto μ |>.comp hμ
    have hrem : Tendsto (fun r => ((L : ℝ) / t r) *
        ((K : ℝ) * Λ * D + ‖w₀‖)) l (𝓝 0) := by
      simpa only [zero_mul] using
        (tendsto_const_nhds.div_atTop ht).mul_const ((K : ℝ) * Λ * D + ‖w₀‖)
    have hrhs := (hint.const_mul (c : ℝ)).add hrem
    simp only [add_zero] at hrhs
    have hrhsb := hrhs.eventually (eventually_lt_nhds (hLb.trans (half_lt_self hb)))
    filter_upwards [hsteps L hL, hrhsb] with r hs hlt
    obtain ⟨htr, hn, hn', hremr, hend, hdom⟩ := hs
    have he := integral_normalized_microsteps_le (Λ := Λ) (K := K) (c := c)
      (σ r : Measure (NormalizedPair G Λ)) (μs r : Measure (NormalizedPair G Λ))
      π hπ (g L) (h L r) (n L r) hdom (Nat.cast_pos.mpr hL) htr hD
      hn hn' hremr hS hw₀
    rw [hend] at he
    exact he.trans_lt hlt

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_CompactProbabilityDensity
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Compact probability cutoffs for occupation and segment sampling -/

noncomputable section

namespace PolycyclicRecognition

open Set MeasureTheory Filter
open scoped Topology

/-- A compact subset of an open chart admits a continuous compactly
supported probability density which is one fixed positive constant on that
subset. It is bounded above by that same constant everywhere. -/
theorem exists_compact_probability_density
    {X : Type*} [TopologicalSpace X] [R1Space X] [LocallyCompactSpace X]
    [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) [μ.IsOpenPosMeasure] [IsFiniteMeasureOnCompacts μ]
    {K U : Set X} (hK : IsCompact K) (hne : K.Nonempty)
    (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ (ρ : C(X, ℝ)) (b : ℝ), 0 < b ∧ HasCompactSupport ρ ∧ tsupport ρ ⊆ U ∧
      (∀ x, 0 ≤ ρ x ∧ ρ x ≤ b) ∧ (∀ x ∈ K, ρ x = b) ∧
      Integrable ρ μ ∧ ∫ x, ρ x ∂μ = 1 := by
  obtain ⟨f, hfK, hfcomp, hfU, hf⟩ :=
    exists_continuousMap_one_of_isCompact_subset_isOpen hK hU hKU
  have hfi : Integrable f μ := f.continuous.integrable_of_hasCompactSupport hfcomp
  obtain ⟨x, hx⟩ := hne
  have hx1 : f x = 1 := hfK hx
  have hmass : 0 < ∫ x, f x ∂μ :=
    f.continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero hfcomp
      (fun y => (hf y).1) (by rw [hx1]; norm_num)
  let b := (∫ x, f x ∂μ)⁻¹
  let ρ : C(X, ℝ) := ⟨fun x => b * f x, continuous_const.mul f.continuous⟩
  have hb : 0 < b := inv_pos.mpr hmass
  have hsub : tsupport ρ ⊆ tsupport f := tsupport_mul_subset_right
  have hcomp : HasCompactSupport ρ := hfcomp.of_isClosed_subset (isClosed_tsupport ρ) hsub
  refine ⟨ρ, b, hb, hcomp, hsub.trans hfU, ?_, ?_, ?_, ?_⟩
  · intro y
    exact ⟨mul_nonneg hb.le (hf y).1, by
      change b * f y ≤ b
      nlinarith [(hf y).2]⟩
  · intro y hy
    change b * f y = b
    rw [hfK hy, Pi.one_apply, mul_one]
  · exact ρ.continuous.integrable_of_hasCompactSupport hcomp
  · change (∫ x, b * f x ∂μ) = 1
    rw [integral_const_mul]
    exact inv_mul_cancel₀ hmass.ne'

/-- Every point where the continuous density is positive belongs to the
support of its probability measure. -/
theorem mem_support_densityProbabilityMeasure
    {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) [μ.IsOpenPosMeasure] (ρ : X → ℝ) (hρ : Continuous ρ)
    (hi : Integrable ρ μ) (hp : ∀ x, 0 ≤ ρ x) (hm : ∫ x, ρ x ∂μ = 1)
    {x : X} (hx : 0 < ρ x) :
    x ∈ (densityProbabilityMeasure μ ρ hi hp hm : Measure X).support := by
  apply (Measure.mem_support_iff_forall x).mpr
  intro U hU
  apply pos_iff_ne_zero.mpr
  intro hzero
  change μ.withDensity (fun y => ENNReal.ofReal (ρ y)) U = 0 at hzero
  have hz := (withDensity_apply_eq_zero hρ.measurable.ennreal_ofReal).mp hzero
  have hpos : 0 < μ ({y | 0 < ρ y} ∩ U) := μ.measure_pos_of_mem_nhds
    (inter_mem (hρ.continuousAt.preimage_mem_nhds (Ioi_mem_nhds hx)) hU)
  apply hpos.ne'
  apply measure_mono_null _ hz
  intro y hy
  exact ⟨(ENNReal.ofReal_pos.mpr hy.1).ne', hy.2⟩

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_CompactProbabilityProduct
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Independent compact sampling and supported limits -/

noncomputable section

namespace PolycyclicRecognition

open MeasureTheory Filter Set
open scoped Topology NNReal

/-- Pushing forward the first independent coordinate is the same as
pushing the joint law through the corresponding product map. -/
theorem productOccupationLaw_map_left
    {A B D : Type*} [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace D]
    (μ : ProbabilityMeasure A) (ν : ProbabilityMeasure D)
    (f : A → B) (hf : Measurable f) :
    productOccupationLaw (ProbabilityMeasure.map μ (f := f) (by first | exact hf.aemeasurable | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)) ν id =
      productOccupationLaw μ ν (Prod.map f id) := by
  apply ProbabilityMeasure.toMeasure_injective
  rw [productOccupationLaw_coe _ _ aemeasurable_id,
    productOccupationLaw_coe _ _ (hf.prodMap measurable_id).aemeasurable]
  change Measure.map id ((Measure.map f (μ : Measure A)).prod (ν : Measure D)) =
    Measure.map (Prod.map f id) ((μ : Measure A).prod (ν : Measure D))
  rw [Measure.map_id]
  simpa only [Measure.map_id] using
    (Measure.map_prod_map (μ : Measure A) (ν : Measure D) hf measurable_id)

/-- Integration against a probability is continuous in the uniform norm. -/
theorem continuous_integral_compact_function
    {X : Type*} [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] (μ : ProbabilityMeasure X) :
    Continuous (fun f : C(X, ℝ) => ∫ x, f x ∂(μ : Measure X)) := by
  apply LipschitzWith.continuous (K := 1)
  apply LipschitzWith.of_dist_le_mul
  intro f g
  have hi (h : C(X, ℝ)) : Integrable h (μ : Measure X) :=
    h.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace h)
  rw [dist_eq_norm, ← integral_sub (hi f) (hi g)]
  have hb := norm_integral_le_of_norm_le_const (μ := (μ : Measure X))
    (f := fun x => f x - g x) (C := ‖f - g‖)
    (Eventually.of_forall (fun x => (f - g).norm_coe_le_norm x))
  simpa only [measureReal_def, measure_univ, ENNReal.toReal_one, mul_one,
    NNReal.coe_one, one_mul, dist_eq_norm] using hb

/-- A fixed independent coordinate preserves weak convergence of the
profile law. No rate in the other coordinate is required. -/
theorem productOccupationLaw_tendsto_fixed
    {A D ι : Type*} [TopologicalSpace A] [CompactSpace A]
    [TopologicalSpace D] [CompactSpace D] [SecondCountableTopology D]
    [MeasurableSpace A] [BorelSpace A] [MeasurableSpace D] [BorelSpace D]
    {l : Filter ι} (μs : ι → ProbabilityMeasure A) (μ : ProbabilityMeasure A)
    (hμ : Tendsto μs l (𝓝 μ)) (ν : ProbabilityMeasure D) :
    Tendsto (fun i => productOccupationLaw (μs i) ν id) l
      (𝓝 (productOccupationLaw μ ν id)) := by
  apply ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr
  intro f
  let fc : C(A × D, ℝ) := f.toContinuousMap
  let avg : C(A, ℝ) := ⟨fun a => ∫ z, fc (a, z) ∂(ν : Measure D),
    (continuous_integral_compact_function ν).comp fc.curry.continuous⟩
  have h := (ProbabilityMeasure.continuous_integral_continuousMap avg).tendsto μ |>.comp hμ
  change Tendsto (fun i => ∫ x, fc x ∂(productOccupationLaw (μs i) ν id : Measure _)) l
    (𝓝 (∫ x, fc x ∂(productOccupationLaw μ ν id : Measure _)))
  simp_rw [integral_productOccupationLaw _ _ id measurable_id fc]
  exact h

/-- Every pair of supported points is supported by independent sampling. -/
theorem mem_support_productOccupationLaw
    {A D : Type*} [TopologicalSpace A] [TopologicalSpace D]
    [MeasurableSpace A] [MeasurableSpace D]
    (μ : ProbabilityMeasure A) (ν : ProbabilityMeasure D)
    {a : A} {d : D} (ha : a ∈ (μ : Measure A).support)
    (hd : d ∈ (ν : Measure D).support) :
    (a, d) ∈ (productOccupationLaw μ ν id : Measure (A × D)).support := by
  apply (Measure.mem_support_iff_forall (a, d)).mpr
  intro U hU
  rw [nhds_prod_eq] at hU
  obtain ⟨P, hP, Q, hQ, hPQ⟩ := mem_prod_iff.mp hU
  have hp := (Measure.mem_support_iff_forall a).mp ha P hP
  have hq := (Measure.mem_support_iff_forall d).mp hd Q hQ
  rw [productOccupationLaw_coe μ ν aemeasurable_id]
  change 0 < Measure.map id ((μ : Measure A).prod (ν : Measure D)) U
  rw [Measure.map_id]
  have hpq : 0 < (μ : Measure A).prod (ν : Measure D) (P ×ˢ Q) := by
    rw [Measure.prod_prod]
    exact ENNReal.mul_pos hp.ne' hq.ne'
  exact hpq.trans_le (measure_mono hPQ)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_SupportedProfileConstraints
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Passing vanishing profile errors to every supported limit -/

noncomputable section

namespace PolycyclicRecognition

open MeasureTheory Filter Metric Set
open scoped Topology

/-- Uniformly convergent observables can be integrated against a weakly
convergent family of probabilities. Both vary in this statement. -/
theorem integral_tendsto_of_uniformly_and_weakly
    {X ι : Type*} [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] {l : Filter ι}
    (μs : ι → ProbabilityMeasure X) (μ : ProbabilityMeasure X)
    (hμ : Tendsto μs l (𝓝 μ)) (fs : ι → C(X, ℝ)) (f : C(X, ℝ))
    (hf : TendstoUniformly (fun i x => fs i x) f l) :
    Tendsto (fun i => ∫ x, fs i x ∂(μs i : Measure X)) l
      (𝓝 (∫ x, f x ∂(μ : Measure X))) := by
  have herr : Tendsto (fun i => ∫ x, (fs i x - f x) ∂(μs i : Measure X)) l (𝓝 0) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    filter_upwards [(Metric.tendstoUniformly_iff.mp hf) (ε / 2) (half_pos hε)] with i hi
    have hb := norm_integral_le_of_norm_le_const (μ := (μs i : Measure X))
      (f := fun x => fs i x - f x) (C := ε / 2)
      (Eventually.of_forall (fun x => by simpa only [dist_eq_norm, norm_sub_rev] using (hi x).le))
    simp only [measureReal_def, measure_univ, ENNReal.toReal_one, mul_one] at hb
    simpa only [dist_zero_right] using hb.trans_lt (half_lt_self hε)
  have hfixed := (ProbabilityMeasure.continuous_integral_continuousMap f).tendsto μ |>.comp hμ
  have hsum := herr.add hfixed
  simp only [zero_add] at hsum
  apply hsum.congr
  intro i
  rw [integral_sub ((fs i).continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _))
    (f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))]
  exact sub_add_cancel _ _

/-- A continuous nonnegative error with vanishing expectations vanishes at
every point in the support of the weak limit. -/
theorem zero_on_support_of_uniformly_vanishing_integrals
    {X ι : Type*} [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] {l : Filter ι} [l.NeBot]
    (μs : ι → ProbabilityMeasure X) (μ : ProbabilityMeasure X)
    (hμ : Tendsto μs l (𝓝 μ)) (fs : ι → C(X, ℝ)) (f : C(X, ℝ))
    (hf : TendstoUniformly (fun i x => fs i x) f l)
    (hpos : ∀ x, 0 ≤ f x)
    (hzero : Tendsto (fun i => ∫ x, fs i x ∂(μs i : Measure X)) l (𝓝 0))
    {x : X} (hx : x ∈ (μ : Measure X).support) : f x = 0 := by
  have hint : ∫ x, f x ∂(μ : Measure X) = 0 :=
    tendsto_nhds_unique (integral_tendsto_of_uniformly_and_weakly μs μ hμ fs f hf) hzero
  have hae : f =ᵐ[(μ : Measure X)] 0 :=
    (integral_eq_zero_iff_of_nonneg hpos (f.continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _))).mp hint
  exact (μ : Measure X).support_subset_of_isClosed
    (isClosed_eq f.continuous continuous_const) hae hx

/-- Apply the preceding result to distance from a nonempty closed convex
constraint set. The conclusion holds on the support, not just almost surely. -/
theorem mem_on_support_of_uniformly_vanishing_distance
    {X W ι : Type*} [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] [PseudoMetricSpace W]
    {l : Filter ι} [l.NeBot]
    (μs : ι → ProbabilityMeasure X) (μ : ProbabilityMeasure X)
    (hμ : Tendsto μs l (𝓝 μ)) (vs : ι → C(X, W)) (v : C(X, W))
    (hv : TendstoUniformly (fun i x => vs i x) v l)
    {S : Set W} (hS : IsClosed S) (hne : S.Nonempty)
    (hzero : Tendsto (fun i => ∫ x, infDist (vs i x) S ∂(μs i : Measure X)) l (𝓝 0))
    {x : X} (hx : x ∈ (μ : Measure X).support) : v x ∈ S := by
  apply (hS.mem_iff_infDist_zero hne).mpr
  let fs : ι → C(X, ℝ) := fun i => ⟨fun x => infDist (vs i x) S,
    (continuous_infDist_pt S).comp (vs i).continuous⟩
  let f : C(X, ℝ) := ⟨fun x => infDist (v x) S,
    (continuous_infDist_pt S).comp v.continuous⟩
  have hf : TendstoUniformly (fun i x => fs i x) f l := by
    rw [Metric.tendstoUniformly_iff] at hv ⊢
    intro ε hε
    filter_upwards [hv ε hε] with i hi
    intro y
    exact (lipschitz_infDist_pt S).dist_le_mul (v y) (vs i y) |>.trans_lt (by simpa using hi y)
  exact zero_on_support_of_uniformly_vanishing_integrals μs μ hμ fs f hf
    (fun _ => infDist_nonneg) hzero hx

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_ProfileFlowConvergence
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform evaluation of compact profile families along converging flows -/

noncomputable section

namespace PolycyclicRecognition

open Set Filter
open scoped Topology

variable {U V W : Type*} [TopologicalSpace U] [LocallyCompactSpace U]
  [TopologicalSpace V] [LocallyCompactSpace V] [PseudoMetricSpace W]

/-- Compact-open continuity of joint profile evaluation. -/
theorem continuous_profileAlongMap (S : Set C(V, W)) (K : Set U) :
    Continuous (profileAlongMap (W := W) S K) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  change Continuous (fun p : C(U, V) × (S × K) => p.2.1.val (p.1 p.2.2.val))
  exact continuous_eval.comp
    ((continuous_subtype_val.comp continuous_snd.fst).prodMk
      (continuous_eval.comp (continuous_fst.prodMk
        (continuous_subtype_val.comp continuous_snd.snd))))

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_ProfileIncrementLimits
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Supported increment constraints from actual converging chart flows -/

noncomputable section

namespace PolycyclicRecognition

open Set Filter MeasureTheory
open scoped Topology

variable {U V W : Type*} [TopologicalSpace U] [LocallyCompactSpace U]
  [TopologicalSpace V] [LocallyCompactSpace V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- The increment observable is continuous in the endpoint map. -/
theorem continuous_profileIncrementMap (S : Set C(V, W)) (K : Set U) (q : ℝ)
    (A : C(U, V)) : Continuous (profileIncrementMap S K q A) := by
  exact (continuous_const : Continuous (fun _ : C(U, V) => q)).smul
    ((continuous_profileAlongMap S K).sub continuous_const)

/-- Varying endpoint maps give uniformly convergent increment observables
on a compact profile family and compact starting-point set. -/
theorem profileIncrementMap_tendstoUniformly
    (S : Set C(V, W)) (hS : IsCompact S) (K : Set U) (hK : IsCompact K)
    (q : ℝ) (A : C(U, V)) {ι : Type*} {l : Filter ι}
    {T : ι → C(U, V)} {T₀ : C(U, V)} (hT : Tendsto T l (𝓝 T₀)) :
    TendstoUniformly (fun i p => profileIncrementMap S K q A (T i) p)
      (profileIncrementMap S K q A T₀) l := by
  let : CompactSpace S := isCompact_iff_compactSpace.mp hS
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have ht : Tendsto (fun i => profileIncrementMap S K q A (T i)) l
      (𝓝 (profileIncrementMap S K q A T₀)) := by
    simpa only [Function.comp_def] using
      ((continuous_profileIncrementMap S K q A).tendsto T₀).comp hT
  exact tendstoUniformlyOn_univ.mp
    ((ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn.mp ht) univ isCompact_univ)

/-- A vanishing expected distance for the actual scaled endpoints forces
the limiting segment increment to satisfy the constraint at every supported
profile and starting point. -/
theorem profile_increment_mem_on_support
    (S : Set C(V, W)) (hS : IsCompact S) (K : Set U) (hK : IsCompact K)
    [MeasurableSpace (S × K)] [BorelSpace (S × K)]
    (q : ℝ) (A : C(U, V)) {ι : Type*} {l : Filter ι} [l.NeBot]
    {T : ι → C(U, V)} {T₀ : C(U, V)} (hT : Tendsto T l (𝓝 T₀))
    (μs : ι → ProbabilityMeasure (S × K)) (μ : ProbabilityMeasure (S × K))
    (hμ : Tendsto μs l (𝓝 μ)) {C : Set W} (hC : IsClosed C) (hne : C.Nonempty)
    (herr : Tendsto (fun i => ∫ p, Metric.infDist
      (profileIncrementMap S K q A (T i) p) C ∂(μs i : Measure (S × K))) l (𝓝 0))
    {p : S × K} (hp : p ∈ (μ : Measure (S × K)).support) :
    q • (p.1.val (T₀ p.2.val) - p.1.val (A p.2.val)) ∈ C := by
  let : CompactSpace S := isCompact_iff_compactSpace.mp hS
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  exact mem_on_support_of_uniformly_vanishing_distance μs μ hμ
    (fun i => profileIncrementMap S K q A (T i)) (profileIncrementMap S K q A T₀)
    (profileIncrementMap_tendstoUniformly S hS K hK q A hT) hC hne herr hp

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_IndependentProfileLimits
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Supported profile increments with an independent starting point -/

noncomputable section

namespace PolycyclicRecognition

open MeasureTheory Set Filter
open scoped Topology

/-- The independent starting-point law need only have the specified point
in its support. The conclusion then holds at every supported profile. -/
theorem profile_increment_mem_of_independent_errors
    {U V W ι : Type*} [TopologicalSpace U] [LocallyCompactSpace U]
    [SecondCountableTopology U] [TopologicalSpace V] [LocallyCompactSpace V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (S : Set C(V, W)) (hS : IsCompact S) (K : Set U) (hK : IsCompact K)
    [MeasurableSpace S] [BorelSpace S] [MeasurableSpace K] [BorelSpace K]
    (q : ℝ) (A : C(U, V)) {l : Filter ι} [l.NeBot]
    {T : ι → C(U, V)} {T₀ : C(U, V)} (hT : Tendsto T l (𝓝 T₀))
    (νs : ι → ProbabilityMeasure S) (ν : ProbabilityMeasure S)
    (hν : Tendsto νs l (𝓝 ν)) (η : ProbabilityMeasure K)
    {C : Set W} (hC : IsClosed C) (hne : C.Nonempty)
    (herr : Tendsto (fun i => ∫ f, ∫ z : K, Metric.infDist
      (q • (f.val (T i z.val) - f.val (A z.val))) C
      ∂(η : Measure K) ∂(νs i : Measure S)) l (𝓝 0))
    {f : S} (hf : f ∈ (ν : Measure S).support)
    {z : K} (hz : z ∈ (η : Measure K).support) :
    q • (f.val (T₀ z.val) - f.val (A z.val)) ∈ C := by
  let : CompactSpace S := isCompact_iff_compactSpace.mp hS
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let μs := fun i => productOccupationLaw (νs i) η id
  let μ := productOccupationLaw ν η id
  have hμ : Tendsto μs l (𝓝 μ) := productOccupationLaw_tendsto_fixed νs ν hν η
  have he : Tendsto (fun i => ∫ p, Metric.infDist
      (profileIncrementMap S K q A (T i) p) C ∂(μs i : Measure (S × K))) l (𝓝 0) := by
    let error := fun i => (⟨fun p => Metric.infDist (profileIncrementMap S K q A (T i) p) C,
      (Metric.continuous_infDist_pt C).comp
        (profileIncrementMap S K q A (T i)).continuous⟩ : C(S × K, ℝ))
    have heq (i : ι) := integral_productOccupationLaw (νs i) η id measurable_id (error i)
    simp only [Function.id_def] at heq
    exact herr.congr (fun i => (heq i).symm)
  exact profile_increment_mem_on_support S hS K hK q A hT μs μ hμ hC hne he
    (mem_support_productOccupationLaw ν η hf hz)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_SupportedProbabilityRestriction
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Viewing a supported probability as a probability on its compact support -/

noncomputable section

namespace PolycyclicRecognition

open MeasureTheory Set Filter
open scoped Topology

theorem supportedProbabilityRestriction_map
    {X : Type*} [MeasurableSpace X] (μ : ProbabilityMeasure X)
    (K : Set X) (hK : MeasurableSet K) (hfull : ∀ᵐ x ∂(μ : Measure X), x ∈ K) :
    Measure.map Subtype.val (supportedProbabilityRestriction μ K hK hfull : Measure K) = μ := by
  exact (map_comap_subtype_coe hK _).trans
    (Measure.restrict_eq_self_of_ae_mem hfull)

/-- Supported points stay supported after restriction to a carrying set. -/
theorem mem_support_supportedProbabilityRestriction
    {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    (μ : ProbabilityMeasure X) (K : Set X) (hK : MeasurableSet K)
    (hfull : ∀ᵐ x ∂(μ : Measure X), x ∈ K)
    {x : K} (hx : x.val ∈ (μ : Measure X).support) :
    x ∈ (supportedProbabilityRestriction μ K hK hfull : Measure K).support := by
  apply (Measure.mem_support_iff_forall x).mpr
  intro U hU
  rw [nhds_subtype_eq_comap] at hU
  obtain ⟨V, hV, hVU⟩ := Filter.mem_comap.mp hU
  have hp := (Measure.mem_support_iff_forall x.val).mp hx V hV
  have hsame : (μ : Measure X) (Subtype.val '' (Subtype.val ⁻¹' V : Set K)) =
      (μ : Measure X) V := by
    rw [image_preimage_eq_inter_range, Subtype.range_coe]
    apply measure_congr
    filter_upwards [hfull] with y hy
    change (y ∈ V ∩ K) = (y ∈ V)
    simp only [mem_inter_iff, hy, and_true]
  have hsub : (supportedProbabilityRestriction μ K hK hfull : Measure K)
      (Subtype.val ⁻¹' V) = (μ : Measure X) V := by
    change (μ : Measure X).comap Subtype.val (Subtype.val ⁻¹' V) = _
    rw [comap_subtype_coe_apply hK, hsame]
  rw [← hsub] at hp
  exact hp.trans_le (measure_mono hVU)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_OccupationCompactRestriction
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Compactly supported starting densities in the profile argument -/

noncomputable section

namespace PolycyclicRecognition

open MeasureTheory Filter Set
open scoped Topology

theorem productOccupationLaw_map_right
    {A D E X : Type*} [MeasurableSpace A] [MeasurableSpace D]
    [MeasurableSpace E] [MeasurableSpace X]
    (μ : ProbabilityMeasure A) (ν : ProbabilityMeasure D)
    (f : D → E) (hf : Measurable f) (p : A × E → X) (hp : Measurable p) :
    productOccupationLaw μ (ProbabilityMeasure.map ν (f := f) (by first | exact hf.aemeasurable | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)) p =
      productOccupationLaw μ ν (fun z => p (z.1, f z.2)) := by
  apply ProbabilityMeasure.toMeasure_injective
  rw [productOccupationLaw_coe _ _ hp.aemeasurable,
    productOccupationLaw_coe μ ν (p := fun z => p (z.1, f z.2))
      (hp.comp (measurable_fst.prodMk (hf.comp measurable_snd))).aemeasurable]
  have hprod : (μ : Measure A).prod (Measure.map f (ν : Measure D)) =
      Measure.map (Prod.map id f) ((μ : Measure A).prod (ν : Measure D)) := by
    simpa only [Measure.map_id] using
      (Measure.map_prod_map (μ : Measure A) (ν : Measure D) measurable_id hf)
  change Measure.map p ((μ : Measure A).prod (Measure.map f (ν : Measure D))) = _
  rw [hprod, Measure.map_map hp (measurable_id.prodMap hf)]
  rfl

/-- Restricting the starting probability to a compact carrying set does
not change the occupation law. -/
theorem productOccupationLaw_supportedRestriction
    {A V X : Type*} [MeasurableSpace A] [MeasurableSpace V] [MeasurableSpace X]
    (μ : ProbabilityMeasure A) (η : ProbabilityMeasure V) (K : Set V)
    (hK : MeasurableSet K) (hfull : ∀ᵐ z ∂(η : Measure V), z ∈ K)
    (p : A × V → X) (hp : Measurable p) :
    productOccupationLaw μ (supportedProbabilityRestriction η K hK hfull)
      (fun z => p (z.1, z.2.val)) = productOccupationLaw μ η p := by
  have hmap : ProbabilityMeasure.map (supportedProbabilityRestriction η K hK hfull)
      (f := Subtype.val) (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability) = η := by
    apply Subtype.ext
    exact supportedProbabilityRestriction_map η K hK hfull
  rw [← productOccupationLaw_map_right μ _ Subtype.val measurable_subtype_coe p hp, hmap]

theorem flowTimeSlice_tendsto
    {V ι : Type*} [TopologicalSpace V] {l : Filter ι}
    {Fs : ι → C(V × ℝ, V)} {F : C(V × ℝ, V)} (hF : Tendsto Fs l (𝓝 F)) (T : ℝ) :
    Tendsto (fun i => flowTimeSlice (Fs i) T) l (𝓝 (flowTimeSlice F T)) := by
  exact (ContinuousMap.continuous_precomp
    (⟨fun z => (z, T), continuous_id.prodMk continuous_const⟩ : C(V, V × ℝ))).continuousAt.tendsto.comp hF

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_OccupationFlowMicrosteps
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact microstep decomposition of a continuous one-parameter subgroup -/

noncomputable section

namespace PolycyclicRecognition

open Filter MeasureTheory
open scoped Topology NNReal

variable {G : Type*} [Group G] [PseudoMetricSpace G] [IsIsometricSMul G G]

/-- A fixed integer microstep leaves a remainder of uniformly bounded
length. The endpoint factorization is exact. -/
theorem exists_flow_microstep_bound (d : ℝ → G) (hd : Continuous d)
    (hd0 : d 0 = 1) (hmul : ∀ s t, d (s + t) = d s * d t) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ L : ℕ, 0 < L → ∀ t : ℝ, 0 < t →
      let n := ⌊t / (L : ℝ)⌋₊
      (n : ℝ) * L ≤ t ∧ t ≤ ((n : ℝ) + 1) * L ∧
      dist 1 (d (t - (n : ℝ) * L)) ≤ D * L ∧
      d L ^ n * d (t - (n : ℝ) * L) = d t := by
  obtain ⟨C, hC, hbound⟩ := continuous_flow_coarse_bound d hd hd0 hmul
  have hpow (s : ℝ) (n : ℕ) : d ((n : ℝ) * s) = d s ^ n := by
    induction n with
    | zero => simp [hd0]
    | succ n ih => rw [Nat.cast_succ, add_mul, one_mul, hmul, ih, pow_succ]
  refine ⟨2 * C, by positivity, ?_⟩
  intro L hL t ht
  dsimp only
  let n := ⌊t / (L : ℝ)⌋₊
  have hLr : 0 < (L : ℝ) := Nat.cast_pos.mpr hL
  have hlo : (n : ℝ) * L ≤ t :=
    (le_div_iff₀ hLr).mp (Nat.floor_le (div_nonneg ht.le hLr.le))
  have hhi : t ≤ ((n : ℝ) + 1) * L :=
    ((div_lt_iff₀ hLr).mp (Nat.lt_floor_add_one (t / (L : ℝ)))).le
  refine ⟨hlo, hhi, ?_, ?_⟩
  · apply (hbound _).trans
    rw [abs_of_nonneg (sub_nonneg.mpr hlo)]
    have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast hL
    nlinarith
  · rw [← hpow, ← hmul]
    congr 1
    ring

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_OccupationFlowLimit
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.inversePairCoupling_finiteOnCompacts _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Convex flow increments from dominated occupation laws -/

noncomputable section

namespace PolycyclicRecognition

open Filter MeasureTheory Metric Set
open scoped Topology NNReal

variable {G W : Type*} [Group G] [MetricSpace G] [ProperSpace G]
  [IsTopologicalGroup G] [IsIsometricSMul G G]
  [NormedAddCommGroup W] [NormedSpace ℝ W] {Λ K : ℝ≥0}
  [MeasurableSpace (NormalizedPair G Λ)] [BorelSpace (NormalizedPair G Λ)]

/-- For a genuine continuous one-parameter subgroup all mesh, remainder,
and endpoint hypotheses follow from the flow laws. Only the occupation
comparison and the stationary estimate remain to be supplied. -/
theorem normalized_flow_error_tendsto_zero
    {ι : Type*} {l : Filter ι}
    (π : G →* Multiplicative W) (hπ : LipschitzWith K (fun g => (π g).toAdd))
    (σ μs : ι → ProbabilityMeasure (NormalizedPair G Λ))
    (μ : ProbabilityMeasure (NormalizedPair G Λ)) (hμ : Tendsto μs l (𝓝 μ))
    (d : ℝ → G) (hd : Continuous d) (hd0 : d 0 = 1)
    (hmul : ∀ s t, d (s + t) = d s * d t)
    (t : ι → ℝ) (ht : Tendsto t l atTop) (c : ℝ≥0)
    (hdom : ∀ L : ℕ, 0 < L → ∀ᶠ i in l, ∀ j : Fin ⌊t i / (L : ℝ)⌋₊,
      Measure.map (fun p : NormalizedPair G Λ => (d L ^ (j : ℕ))⁻¹ • p)
        (σ i : Measure _) ≤ c • (μs i : Measure _))
    {S : Set W} (hS : IsCompact S) {w₀ : W} (hw₀ : w₀ ∈ S)
    (hstationary : Tendsto (fun L : ℕ => ∫ p : NormalizedPair G Λ,
      infDist ((L : ℝ)⁻¹ • pairHeight π (d L) p) S ∂(μ : Measure _)) atTop (𝓝 0)) :
    Tendsto (fun i => ∫ p : NormalizedPair G Λ,
      infDist ((t i)⁻¹ • pairHeight π (d (t i)) p) (convexHull ℝ S)
        ∂(σ i : Measure _)) l (𝓝 0) := by
  obtain ⟨D, hD, hb⟩ := exists_flow_microstep_bound d hd hd0 hmul
  apply normalized_microstep_error_tendsto_zero π hπ σ μs μ hμ t ht
    (fun i => d (t i)) (fun L => d L)
    (fun L i => ⌊t i / (L : ℝ)⌋₊)
    (fun L i => d (t i - (⌊t i / (L : ℝ)⌋₊ : ℝ) * L)) c hD _ hS hw₀ hstationary
  intro L hL
  filter_upwards [ht.eventually (eventually_gt_atTop (0 : ℝ)), hdom L hL] with i hi hid
  obtain ⟨hlo, hhi, hrem, hend⟩ := hb L hL (t i) hi
  exact ⟨hi, hlo, hhi, hrem, hend, hid⟩

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_SampledProfileIncrements
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.inversePairCoupling_finiteOnCompacts _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Convex increments of supported sampled profiles -/

noncomputable section

namespace PolycyclicRecognition

open Filter MeasureTheory Set Metric
open scoped Topology NNReal

/-- The two-limit occupation estimate implies the increment constraint for
every supported profile. Sampling, the exact cocycle identity, and domination
are stated separately so that all are checked on the actual chart. -/
theorem sampled_profile_increment_mem
    {U V W A G ι : Type*}
    [TopologicalSpace U] [LocallyCompactSpace U] [SecondCountableTopology U]
    [TopologicalSpace V] [LocallyCompactSpace V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    [Group G] [MetricSpace G] [ProperSpace G] [IsTopologicalGroup G]
    [IsIsometricSMul G G] [MeasurableSpace A]
    {Λ Kπ : ℝ≥0} [MeasurableSpace (NormalizedPair G Λ)]
    [BorelSpace (NormalizedPair G Λ)]
    (S : Set C(V, W)) (hS : IsCompact S) (K : Set U) (hK : IsCompact K)
    [MeasurableSpace S] [BorelSpace S] [MeasurableSpace K] [BorelSpace K]
    (π : G →* Multiplicative W) (hπ : LipschitzWith Kπ (fun g => (π g).toAdd))
    {l : Filter ι} [l.NeBot] (samples : ι → ProbabilityMeasure A)
    (profile : ι → A → S) (hprofile : ∀ i, Measurable (profile i))
    (ν : ProbabilityMeasure S)
    (hν : Tendsto (fun i => ProbabilityMeasure.map (samples i) (f := (profile i)) (by first | exact (hprofile i).aemeasurable | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)) l (𝓝 ν))
    (η : ProbabilityMeasure K)
    (chart : ι → A × K → NormalizedPair G Λ) (hchart : ∀ i, Measurable (chart i))
    (μs : ι → ProbabilityMeasure (NormalizedPair G Λ))
    (μ : ProbabilityMeasure (NormalizedPair G Λ)) (hμ : Tendsto μs l (𝓝 μ))
    (d : ℝ → G) (hd : Continuous d) (hd0 : d 0 = 1)
    (hmul : ∀ s t, d (s + t) = d s * d t)
    (t : ι → ℝ) (ht : Tendsto t l atTop) (c : ℝ≥0)
    (hdom : ∀ L : ℕ, 0 < L → ∀ᶠ i in l, ∀ j : Fin ⌊t i / (L : ℝ)⌋₊,
      Measure.map (fun p : NormalizedPair G Λ => (d L ^ (j : ℕ))⁻¹ • p)
        (productOccupationLaw (samples i) η (chart i) : Measure _) ≤ c • (μs i : Measure _))
    (q : ℝ) (start : C(U, V)) (ends : ι → C(U, V)) (end₀ : C(U, V))
    (hends : Tendsto ends l (𝓝 end₀))
    (hidentity : ∀ i, ∀ᵐ a ∂(samples i : Measure A), ∀ z,
      (t i)⁻¹ • pairHeight π (d (t i)) (chart i (a, z)) =
      q • ((profile i a).val (ends i z.val) - (profile i a).val (start z.val)))
    {B : Set W} (hB : IsCompact B) {b : W} (hb : b ∈ B)
    (hconvex : IsClosed (convexHull ℝ B))
    (hstationary : Tendsto (fun L : ℕ => ∫ p : NormalizedPair G Λ,
      infDist ((L : ℝ)⁻¹ • pairHeight π (d L) p) B ∂(μ : Measure _)) atTop (𝓝 0))
    {f : S} (hf : f ∈ (ν : Measure S).support)
    {z : K} (hz : z ∈ (η : Measure K).support) :
    q • (f.val (end₀ z.val) - f.val (start z.val)) ∈ convexHull ℝ B := by
  let : CompactSpace S := isCompact_iff_compactSpace.mp hS
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let σ := fun i => productOccupationLaw (samples i) η (chart i)
  have herror := normalized_flow_error_tendsto_zero π hπ σ μs μ hμ d hd hd0 hmul
    t ht c hdom hB hb hstationary
  apply profile_increment_mem_of_independent_errors S hS K hK q start hends
    (fun i => ProbabilityMeasure.map (samples i) (f := (profile i)) (by first | exact (hprofile i).aemeasurable | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)) ν hν η
    hconvex ⟨b, subset_convexHull ℝ B hb⟩ _ hf hz
  have heq (i : ι) :
      (∫ f, ∫ z : K, infDist (q • (f.val (ends i z.val) - f.val (start z.val)))
          (convexHull ℝ B) ∂(η : Measure K)
        ∂(ProbabilityMeasure.map (samples i) (f := (profile i)) (by first | exact (hprofile i).aemeasurable | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability) : Measure S)) =
      ∫ p, infDist ((t i)⁻¹ • pairHeight π (d (t i)) p) (convexHull ℝ B)
        ∂(σ i : Measure (NormalizedPair G Λ)) := by
    let error : C(S × K, ℝ) := ⟨fun p => infDist
      (profileIncrementMap S K q start (ends i) p) (convexHull ℝ B),
      (continuous_infDist_pt _).comp (profileIncrementMap S K q start (ends i)).continuous⟩
    change (∫ f, ∫ z : K, error (id (f, z)) ∂(η : Measure K)
      ∂(ProbabilityMeasure.map (samples i) (f := (profile i)) (by first | exact (hprofile i).aemeasurable | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability) : Measure S)) = _
    rw [← integral_productOccupationLaw _ η id measurable_id error,
      productOccupationLaw_map_left _ η _ (hprofile i),
      integral_productOccupationLaw _ η _ ((hprofile i).prodMap measurable_id) error]
    let pairError : C(NormalizedPair G Λ, ℝ) :=
      ⟨_, continuous_pair_label_distance π hπ.continuous (d (t i)) (t i) (convexHull ℝ B)⟩
    change (∫ a, ∫ z, error (Prod.map (profile i) id (a, z)) ∂(η : Measure K)
      ∂(samples i : Measure A)) =
      ∫ p, pairError p ∂(productOccupationLaw (samples i) η (chart i) : Measure _)
    rw [integral_productOccupationLaw _ η _ (hchart i) pairError]
    apply integral_congr_ae
    filter_upwards [hidentity i] with a ha
    apply integral_congr_ae
    exact Eventually.of_forall (fun z => by
        change infDist (q • ((profile i a).val (ends i z.val) -
          (profile i a).val (start z.val))) (convexHull ℝ B) =
          infDist ((t i)⁻¹ • pairHeight π (d (t i)) (chart i (a, z))) (convexHull ℝ B)
        rw [ha])
  exact herror.congr (fun i => (heq i).symm)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CompactFlowNeighborhood
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # One compact neighborhood for all sufficiently large coordinate flows -/

namespace PolycyclicRecognition

open Set Filter Metric
open scoped Topology

/-- Compact convergence of coordinate paths allows one compact cutoff to
contain the entire late family inside the prescribed open chart. -/
theorem exists_compact_eventual_flow_image
    {X Y ι : Type*} [TopologicalSpace X] [MetricSpace Y] [LocallyCompactSpace Y]
    {l : Filter ι} {F : ι → X → Y} {f : X → Y} {K : Set X} {U : Set Y}
    (hK : IsCompact K) (hf : ContinuousOn f K) (hU : IsOpen U)
    (himage : f '' K ⊆ U) (hF : TendstoUniformlyOn F f l K) :
    ∃ Q : Set Y, IsCompact Q ∧ Q ⊆ U ∧ f '' K ⊆ Q ∧
      ∀ᶠ i in l, F i '' K ⊆ Q := by
  have hc : IsCompact (f '' K) := hK.image_of_continuousOn hf
  obtain ⟨O, hO, hfO, hOU, hOc⟩ := exists_open_between_and_isCompact_closure hc hU himage
  obtain ⟨δ, hδ, hthick⟩ := hc.exists_thickening_subset_open hO hfO
  refine ⟨closure O, hOc, hOU, hfO.trans subset_closure, ?_⟩
  filter_upwards [(Metric.tendstoUniformlyOn_iff.mp hF) δ hδ] with i hi
  rintro y ⟨x, hx, rfl⟩
  apply subset_closure
  apply hthick
  exact mem_thickening_iff.mpr ⟨f x, mem_image_of_mem f hx, by simpa only [dist_comm] using hi x hx⟩

end PolycyclicRecognition

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_FlowProbabilityCutoffs
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Fixed probability cutoffs for converging horizontal segments -/

noncomputable section

namespace PolycyclicRecognition

open Set Filter MeasureTheory
open scoped Topology NNReal

/-- A segment in the open chart admits one starting density and one
occupation density. The domination constant works for every time on the
segment and all sufficiently late scaled flows, before choosing a mesh. -/
theorem exists_flow_probability_cutoffs
    {X ι : Type*} [MetricSpace X] [LocallyCompactSpace X]
    [MeasurableSpace X] [BorelSpace X]
    (m : Measure X) [m.IsOpenPosMeasure] [IsFiniteMeasureOnCompacts m]
    {l : Filter ι} (Fs : ι → C(X × ℝ, X)) (F : C(X × ℝ, X))
    (hF : Tendsto Fs l (𝓝 F)) (z : X) {T : ℝ} (hT : 0 ≤ T)
    {U : Set X} (hU : IsOpen U) (hseg : ∀ t ∈ Icc 0 T, F (z, t) ∈ U) :
    ∃ (η ρ : C(X, ℝ)) (c : ℝ≥0),
      HasCompactSupport η ∧ HasCompactSupport ρ ∧ tsupport ρ ⊆ U ∧
      (∀ x, 0 ≤ η x) ∧ (∀ x, 0 ≤ ρ x) ∧ 0 < η z ∧
      Integrable η m ∧ Integrable ρ m ∧
      (∫ x, η x ∂m) = 1 ∧ (∫ x, ρ x ∂m) = 1 ∧
      ∀ᶠ i in l, ∀ t ∈ Icc 0 T, ∀ x, η x ≤ (c : ℝ) * ρ (Fs i (x, t)) := by
  obtain ⟨O, V, hO, _, hzO, hIV, hprod⟩ := generalized_tube_lemma
    (isCompact_singleton : IsCompact ({z} : Set X)) isCompact_Icc
    (hU.preimage F.continuous) (by
      rintro ⟨x, t⟩ ⟨hx, ht⟩
      have hxz : x = z := mem_singleton_iff.mp hx
      subst x
      exact hseg t ht)
  obtain ⟨η, A, hA, hηcomp, hηO, hηbound, hηz, hηi, hηmass⟩ :=
    exists_compact_probability_density m isCompact_singleton (singleton_nonempty z)
      hO hzO
  have hηz' : η z = A := hηz z (mem_singleton z)
  have hzsup : z ∈ tsupport η := subset_tsupport η (by
    change η z ≠ 0
    rw [hηz']
    exact hA.ne')
  have hcompact : IsCompact (tsupport η ×ˢ Icc 0 T) := hηcomp.prod isCompact_Icc
  have himage : F '' (tsupport η ×ˢ Icc 0 T) ⊆ U := by
    rintro y ⟨⟨x, t⟩, ⟨hx, ht⟩, rfl⟩
    exact hprod ⟨hηO hx, hIV ht⟩
  have hunif := (ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn.mp hF)
    (tsupport η ×ˢ Icc 0 T) hcompact
  obtain ⟨Q, hQ, hQU, hFQ, hFsQ⟩ := exists_compact_eventual_flow_image
    hcompact F.continuous.continuousOn hU himage hunif
  have hQne : Q.Nonempty := ⟨F (z, 0), hFQ (mem_image_of_mem F ⟨hzsup, le_rfl, hT⟩)⟩
  obtain ⟨ρ, b, hb, hρcomp, hρU, hρbound, hρQ, hρi, hρmass⟩ :=
    exists_compact_probability_density m hQ hQne hU hQU
  let c : ℝ≥0 := ⟨A / b, div_nonneg hA.le hb.le⟩
  refine ⟨η, ρ, c, hηcomp, hρcomp, hρU, fun x => (hηbound x).1,
    fun x => (hρbound x).1, by simpa only [hηz'] using hA,
    hηi, hρi, hηmass, hρmass, ?_⟩
  filter_upwards [hFsQ] with i hi
  intro t ht
  exact density_bound_on_swept_support η ρ (fun x => Fs i (x, t)) Q hA.le hb
    (fun x => (hηbound x).2) (fun x => (hρbound x).1)
    (fun x hx => hi (mem_image_of_mem (Fs i) ⟨subset_tsupport η hx, ht⟩))
    (fun x hx => (hρQ x hx).ge)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_FlowSampleDomination
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.inversePairCoupling_finiteOnCompacts _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Domination of all discrete microsteps by the fixed cutoff law -/

noncomputable section

namespace PolycyclicRecognition

open Filter MeasureTheory Set
open scoped Topology NNReal

theorem oneParameter_nat_mul {G : Type*} [Monoid G]
    (d : ℝ → G) (hd0 : d 0 = 1) (hmul : ∀ s t, d (s + t) = d s * d t)
    (t : ℝ) (n : ℕ) : d ((n : ℝ) * t) = d t ^ n := by
  induction n with
  | zero => simp [hd0]
  | succ n ih => rw [Nat.cast_succ, add_mul, one_mul, hmul, ih, pow_succ]

/-- All integer mesh starting times lie in the prescribed compact time
interval, including when the final interval is shorter than a mesh step. -/
theorem microstep_time_mem_Icc {r T : ℝ} (hr : 0 < r) (hT : 0 ≤ T)
    (L : ℕ) (hL : 0 < L) (j : Fin ⌊r * T / (L : ℝ)⌋₊) :
    (j : ℝ) * L / r ∈ Icc 0 T := by
  have hLr : 0 < (L : ℝ) := Nat.cast_pos.mpr hL
  have hj : (j : ℝ) ≤ (⌊r * T / (L : ℝ)⌋₊ : ℝ) := by
    exact_mod_cast j.isLt.le
  have hfloor : (⌊r * T / (L : ℝ)⌋₊ : ℝ) * L ≤ r * T :=
    (le_div_iff₀ hLr).mp (Nat.floor_le (div_nonneg (mul_nonneg hr.le hT) hLr.le))
  refine ⟨div_nonneg (mul_nonneg (Nat.cast_nonneg _) hLr.le) hr.le, ?_⟩
  apply (div_le_iff₀ hr).mpr
  calc
    (j : ℝ) * L ≤ (⌊r * T / (L : ℝ)⌋₊ : ℝ) * L := mul_le_mul_of_nonneg_right hj hLr.le
    _ ≤ r * T := hfloor
    _ = T * r := mul_comm _ _

/-- Haar-preserving coordinate moves and the one fixed pair of cutoff
densities imply every domination premise of the two-limit argument. -/
theorem microstep_sample_laws_dominated
    {A V G ι : Type*} [MeasurableSpace A] [MeasurableSpace V]
    [Group G] [MetricSpace G] [ProperSpace G] [IsTopologicalGroup G]
    [IsIsometricSMul G G] {Λ : ℝ≥0}
    [MeasurableSpace (NormalizedPair G Λ)] [BorelSpace (NormalizedPair G Λ)]
    {l : Filter ι} (m : Measure V) (samples : ι → ProbabilityMeasure A)
    (η ρ : V → ℝ) (hiη : Integrable η m) (hiρ : Integrable ρ m)
    (hpη : ∀ z, 0 ≤ η z) (hpρ : ∀ z, 0 ≤ ρ z)
    (hmη : ∫ z, η z ∂m = 1) (hmρ : ∫ z, ρ z ∂m = 1) (hρ : Measurable ρ)
    (r : ι → ℝ) (hr : ∀ᶠ i in l, 0 < r i) {T : ℝ} (hT : 0 ≤ T)
    (F : ι → V × ℝ → V)
    (hpres : ∀ i t, MeasurePreserving (fun z => F i (z, t)) m m)
    (chart : ι → A × V → NormalizedPair G Λ) (hchart : ∀ i, Measurable (chart i))
    (d : ℝ → G) (hd0 : d 0 = 1) (hmul : ∀ s t, d (s + t) = d s * d t)
    (hmove : ∀ i a z t, (d (r i * t))⁻¹ • chart i (a, z) = chart i (a, F i (z, t)))
    (c : ℝ≥0)
    (hbound : ∀ᶠ i in l, ∀ t ∈ Icc 0 T, ∀ z, η z ≤ (c : ℝ) * ρ (F i (z, t))) :
    ∀ L : ℕ, 0 < L → ∀ᶠ i in l, ∀ j : Fin ⌊r i * T / (L : ℝ)⌋₊,
      Measure.map (fun p : NormalizedPair G Λ => (d L ^ (j : ℕ))⁻¹ • p)
        (productOccupationLaw (samples i) (densityProbabilityMeasure m η hiη hpη hmη)
          (chart i) : Measure _) ≤
      c • (productOccupationLaw (samples i) (densityProbabilityMeasure m ρ hiρ hpρ hmρ)
        (chart i) : Measure _) := by
  intro L hL
  filter_upwards [hr, hbound] with i hri hbi
  intro j
  let u := (j : ℝ) * L / r i
  have hu : u ∈ Icc 0 T := microstep_time_mem_Icc hri hT L hL j
  apply map_productOccupationLaw_le (samples i) _ _ (chart i) (hchart i)
    (fun z => F i (z, u)) (hpres i u).measurable
    (fun p => (d L ^ (j : ℕ))⁻¹ • p) (continuous_const_smul _).measurable
  · intro a z
    have htime : r i * u = (j : ℝ) * L := by dsimp [u]; field_simp
    simpa only [htime, oneParameter_nat_mul d hd0 hmul] using hmove i a z u
  · exact map_densityProbabilityMeasure_le m η ρ hiη hiρ hpη hpρ hmη hmρ
      hρ _ (hpres i u) c (hbi u hu)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_FlowSupportedProfileIncrement
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.inversePairCoupling_finiteOnCompacts _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Supported profile increments from one fixed occupation limit

The cutoff is chosen before the occupation limit, which is chosen before
the microstep length. Invariance and the stationary estimate remain explicit
interfaces to the already proved Cartan occupation and stationary theorems.
-/

noncomputable section

namespace PolycyclicRecognition

open Filter MeasureTheory Set Metric
open scoped Topology NNReal

theorem supported_profile_increment_of_flow_oai
    {V W A G ι : Type*} [MetricSpace V] [LocallyCompactSpace V] [SecondCountableTopology V]
    [MeasurableSpace V] [BorelSpace V] [NormedAddCommGroup W] [NormedSpace ℝ W]
    [MeasurableSpace A] [Group G] [MetricSpace G] [ProperSpace G]
    [IsTopologicalGroup G] [IsIsometricSMul G G]
    {Λ Kπ : ℝ≥0} [MeasurableSpace (NormalizedPair G Λ)] [BorelSpace (NormalizedPair G Λ)]
    (S : Set C(V, W)) (hS : IsCompact S) [MeasurableSpace S] [BorelSpace S]
    (π : G →* Multiplicative W) (hπ : LipschitzWith Kπ (fun g => (π g).toAdd))
    {l : Filter ι} [l.NeBot]
    (samples : ι → ProbabilityMeasure A) (profile : ι → A → S)
    (hprofile : ∀ i, Measurable (profile i)) (ν : ProbabilityMeasure S)
    (hν : Tendsto (fun i => ProbabilityMeasure.map (samples i) (f := (profile i)) (by first | exact (hprofile i).aemeasurable | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)) l (𝓝 ν))
    (m : Measure V) [m.IsOpenPosMeasure] [IsFiniteMeasureOnCompacts m]
    (Fs : ι → C(V × ℝ, V)) (F : C(V × ℝ, V)) (hF : Tendsto Fs l (𝓝 F))
    (hpres : ∀ i t, MeasurePreserving (fun z => Fs i (z, t)) m m)
    (chart : ι → A × V → NormalizedPair G Λ) (hchart : ∀ i, Measurable (chart i))
    (d : ℝ → G) (hd : Continuous d) (hd0 : d 0 = 1)
    (hmul : ∀ s t, d (s + t) = d s * d t)
    (r : ι → ℝ) (hr : Tendsto r l atTop) {T : ℝ} (hT : 0 < T)
    (hmove : ∀ i a z t, (d (r i * t))⁻¹ • chart i (a, z) = chart i (a, Fs i (z, t)))
    (hidentity : ∀ i, ∀ᵐ a ∂(samples i : Measure A), ∀ z,
      (r i * T)⁻¹ • pairHeight π (d (r i * T)) (chart i (a, z)) =
      T⁻¹ • ((profile i a).val (Fs i (z, T)) - (profile i a).val z))
    {U : Set V} (hU : IsOpen U) (z : V) (hseg : ∀ t ∈ Icc 0 T, F (z, t) ∈ U)
    (hinvariant : ∀ (ρ : C(V, ℝ)) (hi : Integrable ρ m) (hp : ∀ x, 0 ≤ ρ x)
      (hm : ∫ x, ρ x ∂m = 1), HasCompactSupport ρ → tsupport ρ ⊆ U →
      ∀ (u : Ultrafilter ι), (u : Filter ι) ≤ l →
      ∀ μ : ProbabilityMeasure (NormalizedPair G Λ),
      Tendsto (fun i => productOccupationLaw (samples i)
        (densityProbabilityMeasure m ρ hi hp hm) (chart i)) u (𝓝 μ) →
      SMulInvariantMeasure G (NormalizedPair G Λ) (μ : Measure _))
    {B : Set W} (hB : IsCompact B) {b : W} (hb : b ∈ B)
    (hconvex : IsClosed (convexHull ℝ B))
    (hstationary : ∀ μ : ProbabilityMeasure (NormalizedPair G Λ),
      SMulInvariantMeasure G (NormalizedPair G Λ) (μ : Measure _) →
      Tendsto (fun L : ℕ => ∫ p : NormalizedPair G Λ,
        infDist ((L : ℝ)⁻¹ • pairHeight π (d L) p) B ∂(μ : Measure _)) atTop (𝓝 0))
    {f : S} (hf : f ∈ (ν : Measure S).support) :
    T⁻¹ • (f.val (F (z, T)) - f.val z) ∈ convexHull ℝ B := by
  obtain ⟨η, ρ, c, hηcomp, hρcomp, hρU, hηpos, hρpos, hηz, hηi, hρi,
    hηmass, hρmass, hbound⟩ := exists_flow_probability_cutoffs m Fs F hF z hT.le hU hseg
  let ηlaw := densityProbabilityMeasure m η hηi hηpos hηmass
  let μs := fun i => productOccupationLaw (samples i)
    (densityProbabilityMeasure m ρ hρi hρpos hρmass) (chart i)
  obtain ⟨u, μ, hul, hμ, hνu⟩ := exists_occupation_limit_preserving μs hν
  have hinv := hinvariant ρ hρi hρpos hρmass hρcomp hρU u hul μ hμ
  let K := tsupport η
  have hKm : MeasurableSet K := (isClosed_tsupport η).measurableSet
  have hηfull : ∀ᵐ x ∂(ηlaw : Measure V), x ∈ K :=
    ae_mem_densityProbabilityMeasure m η hηi hηpos hηmass K
      (fun x hx => image_eq_zero_of_notMem_tsupport hx)
  let ηK := supportedProbabilityRestriction ηlaw K hKm hηfull
  let chartK := fun i (p : A × K) => chart i (p.1, p.2.val)
  have hchartK (i : ι) : Measurable (chartK i) :=
    (hchart i).comp (measurable_fst.prodMk (measurable_subtype_coe.comp measurable_snd))
  have hlaws (i : ι) : productOccupationLaw (samples i) ηK (chartK i) =
      productOccupationLaw (samples i) ηlaw (chart i) :=
    productOccupationLaw_supportedRestriction (samples i) ηlaw K hKm hηfull (chart i) (hchart i)
  have hdom := microstep_sample_laws_dominated m samples η ρ hηi hρi hηpos hρpos
    hηmass hρmass ρ.continuous.measurable r
    (hr.eventually (eventually_gt_atTop 0)) hT.le (fun i p => Fs i p) hpres chart hchart
    d hd0 hmul hmove c hbound
  have hdomu : ∀ L : ℕ, 0 < L → ∀ᶠ i in (u : Filter ι), ∀ j : Fin ⌊r i * T / (L : ℝ)⌋₊,
      Measure.map (fun p : NormalizedPair G Λ => (d L ^ (j : ℕ))⁻¹ • p)
        (productOccupationLaw (samples i) ηK (chartK i) : Measure _) ≤ c • (μs i : Measure _) := by
    intro L hL
    filter_upwards [(hdom L hL).filter_mono hul] with i hi
    simpa only [hlaws] using hi
  have hzK : z ∈ K := subset_tsupport η hηz.ne'
  have hzsup : (⟨z, hzK⟩ : K) ∈ (ηK : Measure K).support :=
    mem_support_supportedProbabilityRestriction ηlaw K hKm hηfull
      (mem_support_densityProbabilityMeasure m η η.continuous hηi hηpos hηmass hηz)
  have ht : Tendsto (fun i => r i * T) u atTop :=
    (hr.atTop_mul_const hT).mono_left hul
  exact sampled_profile_increment_mem S hS K hηcomp π hπ samples profile hprofile ν hνu
    ηK chartK hchartK μs μ hμ d hd hd0 hmul _ ht c hdomu T⁻¹ (ContinuousMap.id V)
    (fun i => flowTimeSlice (Fs i) T) (flowTimeSlice F T)
    ((flowTimeSlice_tendsto hF T).mono_left hul)
    (fun i => (hidentity i).mono (fun a ha x => ha x.val))
    hB hb hconvex (hstationary μ hinv) hf hzsup

end PolycyclicRecognition

end

end OAI
end

theorem solution.{u_1, u_2, u_3, u_4, u_5} : type_of% @OAI.PolycyclicRecognition.supported_profile_increment_of_flow_oai.{u_1, u_2, u_3, u_4, u_5} := @OAI.PolycyclicRecognition.supported_profile_increment_of_flow_oai.{u_1, u_2, u_3, u_4, u_5}
