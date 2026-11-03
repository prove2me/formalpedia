-- Prove2me | solution 1 for OAI.PolycyclicRecognition.CartanWordModel.exists_one_cone_offset_threshold
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-03T00:50:30.809693+00:00
-- url     : https://prove2.me/submissions/9ee6eb89-fad3-4b77-8a78-dd2215b7b675

import Mathlib
import Definitions.Def_PolycyclicRecognition
import Definitions.Def_OAIQ093D022
import Theorems.Thm_OAI_PolycyclicRecognition_CartanWordModel_AffineNeighborRow_polar_offset_nonpos
import Theorems.Thm_OAI_PolycyclicRecognition_CartanWordModel_MeasuredCone_exists_canonical_polar_samplers
import Theorems.Thm_OAI_PolycyclicRecognition_CartanWordModel_MeasuredCone_exists_uniform_polar_target_regions
import Theorems.Thm_OAI_PolycyclicRecognition_CartanWordModel_MeasuredCone_sectionMeasure_isHaar
import Theorems.Thm_OAI_PolycyclicRecognition_CartanWordModel_exists_uniform_contact_step_bridge_m

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_ConePolarTemplate
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
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

variable {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
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
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_QuotientSectionIndependence
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The product Haar normalization is independent of the section -/

noncomputable section
namespace PolycyclicRecognition

open MeasureTheory

variable {N Q : Type} [Group N] [Group Q]
  [TopologicalSpace N] [TopologicalSpace Q] [IsTopologicalGroup N] [IsTopologicalGroup Q]
  [SecondCountableTopology Q]
  [MeasurableSpace N] [MeasurableSpace Q] [BorelSpace N] [BorelSpace Q]

omit [IsTopologicalGroup Q] in
/-- Changing the continuous quotient section translates each kernel fiber
on the right. Thus one product normalization serves every adapted basis. -/
theorem quotientSection_product_independent
    (π : N →* Q) (hπ : Continuous π)
    (s t : C(Q, N)) (hs : ∀ q, π (s q) = q) (ht : ∀ q, π (t q) = q)
    (μQ : Measure Q) (μI : Measure π.ker) [SFinite μQ] [SFinite μI]
    [μI.IsMulRightInvariant] :
    Measure.map (quotientSectionHomeomorph π hπ s hs).symm (μQ.prod μI) =
      Measure.map (quotientSectionHomeomorph π hπ t ht).symm (μQ.prod μI) := by
  let c : Q → π.ker := fun q => quotientSectionResidual π t ht (s q)
  have hc : Continuous c := by
    exact ((s.continuous.mul (t.continuous.comp (hπ.comp s.continuous)).inv)).subtype_mk _
  let changeSection := fun p : Q × π.ker => (p.1, p.2 * c p.1)
  have hchange : MeasurePreserving changeSection (μQ.prod μI) (μQ.prod μI) := by
    apply (MeasurePreserving.id μQ).skew_product (g := fun q i => i * c q)
    · exact (continuous_snd.mul (hc.comp continuous_fst)).measurable
    · exact Filter.Eventually.of_forall (fun q => map_mul_right_eq_self μI (c q))
  have he : (quotientSectionHomeomorph π hπ s hs).symm =
      (quotientSectionHomeomorph π hπ t ht).symm ∘ changeSection := by
    funext p
    change (p.2 : N) * s p.1 = ((p.2 : N) * (s p.1 * (t (π (s p.1)))⁻¹)) * t p.1
    rw [hs, mul_assoc, inv_mul_cancel_right]
  rw [he, ← Measure.map_map (quotientSectionHomeomorph π hπ t ht).symm.measurable
    hchange.measurable, hchange.map_eq]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_SequenceScaleExtraction
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_nonempty _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Cofinal, strictly increasing scales with one fixed finite mode -/

noncomputable section
namespace PolycyclicRecognition

open Filter

/-- A divergent real scale can be made strictly increasing and at least one
by restricting the original sequence. -/
theorem exists_strictMono_scale_subsequence (scale : ℕ → ℝ)
    (hs : Tendsto scale atTop atTop) :
    ∃ u : ℕ → ℕ, StrictMono u ∧ StrictMono (scale ∘ u) ∧
      ∀ n, 1 ≤ scale (u n) := by
  classical
  obtain ⟨n₀, hn₀⟩ := (hs.eventually (eventually_ge_atTop (1 : ℝ))).exists
  have he (n : ℕ) : ∃ k : ℕ, n < k ∧ scale n < scale k :=
    ((eventually_gt_atTop n).and (hs.eventually (eventually_gt_atTop (scale n)))).exists
  choose next hnext hscale using he
  let u : ℕ → ℕ := Nat.rec n₀ (fun _ k => next k)
  have hu : StrictMono u := strictMono_nat_of_lt_succ fun n => hnext (u n)
  have hv : StrictMono (scale ∘ u) :=
    strictMono_nat_of_lt_succ fun n => hscale (u n)
  refine ⟨u, hu, hv, fun n => hn₀.trans ?_⟩
  exact hv.monotone (Nat.zero_le n)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_SmallFactorCell
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A fixed small factor cell for varying Haar normalizations -/

noncomputable section
namespace PolycyclicRecognition

open Set MeasureTheory
open scoped Topology

/-- This cell is chosen before the Haar normalization used by a probe region.
Its interior contains the identity, so every product Haar measure gives it
positive finite mass. -/
theorem exists_small_factor_cell
    {N D G : Type} [Group N] [Group D] [Group G]
    [TopologicalSpace N] [TopologicalSpace D]
    [LocallyCompactSpace N] [LocallyCompactSpace D]
    [MetricSpace G] [IsTopologicalGroup G]
    (ι : N →* G) (κ : D →* G) (hι : Continuous ι) (hκ : Continuous κ) :
    ∃ U : Set (N × D), IsCompact U ∧ (1 : N × D) ∈ interior U ∧
      ∀ z ∈ U, dist (1 : G) (ι z.1 * κ z.2) < 1 / 2 := by
  have hopen : IsOpen {z : N × D | dist (1 : G) (ι z.1 * κ z.2) < 1 / 2} :=
    isOpen_lt (continuous_const.dist
      ((hι.comp continuous_fst).mul (hκ.comp continuous_snd))) continuous_const
  have hone : (1 : N × D) ∈ {z : N × D | dist (1 : G) (ι z.1 * κ z.2) < 1 / 2} := by
    simp
  exact exists_compact_subset hopen hone

/-- The same fixed cell works for each of the section-dependent Haar
products appearing in the target comparison. -/
theorem small_factor_cell_measure
    {N D : Type} [TopologicalSpace N] [TopologicalSpace D]
    [T2Space N] [T2Space D]
    [SecondCountableTopology N] [SecondCountableTopology D]
    [MeasurableSpace N] [MeasurableSpace D] [BorelSpace N] [BorelSpace D]
    (μ : Measure N) (ν : Measure D) [SFinite μ] [SFinite ν]
    [μ.IsOpenPosMeasure] [ν.IsOpenPosMeasure]
    [IsFiniteMeasureOnCompacts μ] [IsFiniteMeasureOnCompacts ν]
    {U : Set (N × D)} (hU : IsCompact U) (hne : (interior U).Nonempty) :
    MeasurableSet U ∧ (μ.prod ν) U ≠ 0 ∧ (μ.prod ν) U ≠ ⊤ := by
  exact ⟨hU.isClosed.measurableSet,
    (Measure.measure_pos_of_nonempty_interior _ hne).ne', hU.measure_ne_top⟩

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

variable {W I B : Type} [NormedAddCommGroup W] [NormedSpace ℝ W]
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

omit [FiniteDimensional ℝ W] [Fintype B] in
theorem isOpen_weightSamplingInterior (α : I → W →L[ℝ] ℝ) :
    IsOpen (weightSamplingInterior α) := by
  simp only [weightSamplingInterior, ofPred_forall]
  exact isOpen_iInter_of_finite fun i => isOpen_lt (α i).continuous continuous_const

omit [FiniteDimensional ℝ W] [Fintype B] in
theorem weightSamplingInterior_subset_interior (α : I → W →L[ℝ] ℝ) :
    weightSamplingInterior α ⊆ interior (weightSamplingPolytope α) := by
  apply interior_maximal
  · intro x hx i
    exact (hx i).le
  · exact isOpen_weightSamplingInterior α

omit [FiniteDimensional ℝ W] [Fintype B] in
/-- Strict scaled facet inequalities place a point in the scaled interior. -/
theorem mem_smul_weightSamplingInterior (α : I → W →L[ℝ] ℝ)
    {a : ℝ} (ha : 0 < a) (x : W) (hx : ∀ i, α i x < a * ‖α i‖) :
    x ∈ (fun y : W => a • y) '' interior (weightSamplingPolytope α) := by
  refine ⟨a⁻¹ • x, weightSamplingInterior_subset_interior α ?_, ?_⟩
  · intro i
    simp only [map_smul, smul_eq_mul]
    exact (inv_mul_lt_iff₀ ha).mpr (hx i)
  · simp [smul_smul, ha.ne']

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
    {W I : Type} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
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

variable {L W : Type} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
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

namespace PolycyclicRecognition

open Set

set_option maxHeartbeats 1000000 in
/-- The facet inequalities give precisely the compact, convex templates
inside one open convex profile domain required by both path construction
and raw concentration. The domain is also inside the original sampling
polytope, which supplies the common coordinate bound. -/
theorem polar_sampling_template_geometry
    {W I : Type} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    [FiniteDimensional ℝ W] [Fintype I]
    (α : I → W →L[ℝ] ℝ) (K : ProperCone ℝ (W →L[ℝ] ℝ))
    (p : W) (ε δ c : ℝ) (hc : 0 ≤ c) (hδ : 0 < δ)
    (hfactor : 0 < 1 - (c + 1) * δ)
    (hfacet : ∀ k : Fin 3, ∀ z ∈ conePolarTemplate K, ∀ i,
      α i ((1 - (c + 1) * δ) • p + threePolarRadii ε k • z) <
        (1 - c * δ) * ‖α i‖) :
    let w := (1 - (c + 1) * δ) • p
    let E := polarSamplingTemplates K ε w
    let V := samplingHeightDomain α (1 - c * δ)
    (∀ k, IsCompact (E k) ∧ Convex ℝ (E k) ∧ w ∈ E k ∧ E k ⊆ V) ∧
      IsOpen V ∧ Convex ℝ V ∧
      V ⊆ (fun y : W => (1 - c * δ) • y) '' interior (weightSamplingPolytope α) ∧
      V ⊆ weightSamplingPolytope α := by
  dsimp only
  let w := (1 - (c + 1) * δ) • p
  have hf : 0 < 1 - c * δ := by nlinarith
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro k
    refine ⟨((isCompact_conePolarTemplate K).image
      (continuous_const.smul continuous_id)).image (continuous_id.add_const w), ?_, ?_, ?_⟩
    · have hcv := ((convex_conePolarTemplate K).smul (threePolarRadii ε k)).translate w
      change Convex ℝ ((fun x => w + x) ''
        ((fun z => threePolarRadii ε k • z) '' conePolarTemplate K)) at hcv
      simpa only [polarSamplingTemplates, w, add_comm] using hcv
    · exact ⟨0, ⟨0, zero_mem_conePolarTemplate K, smul_zero _⟩, zero_add w⟩
    · rintro x ⟨u, ⟨z, hz, rfl⟩, rfl⟩ i
      simpa only [add_comm] using hfacet k z hz i
  · simp only [samplingHeightDomain, Set.ofPred_forall]
    exact isOpen_iInter_of_finite (fun i => isOpen_lt (α i).continuous continuous_const)
  · simp only [samplingHeightDomain, Set.ofPred_forall]
    exact convex_iInter (fun i => convex_halfSpace_lt (α i).toLinearMap.isLinear _)
  · intro x hx
    exact mem_smul_weightSamplingInterior α hf x hx
  · intro x hx i
    have hle : (1 - c * δ) * ‖α i‖ ≤ ‖α i‖ := by
      nlinarith [norm_nonneg (α i), mul_nonneg hc hδ.le]
    exact (hx i).le.trans hle

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanPublishedPolarRegions
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual target regions and Haar trace for a transformed polar cone -/

noncomputable section
namespace PolycyclicRecognition

set_option maxHeartbeats 1000000 in
theorem recentered_polarSamplingTemplates
    {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W]
    (K : ProperCone ℝ (StrongDual ℝ W)) (ε : ℝ) (w : W)
    (A : W →ₗ[ℝ] W) (k : Fin 3) :
    (fun z => A (z - w)) '' polarSamplingTemplates K ε w k =
      A '' normalizedPolarTemplates K ε k := by
  simp only [polarSamplingTemplates, normalizedPolarTemplates, Set.image_image,
    add_sub_cancel_right]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanPolarRegionMeasure
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_countable _root_.OAI.PolycyclicRecognition.finitelyGeneratedSubgroupIndex_countable _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.CartanFactorModel.heightRay_zero _root_.OAI.PolycyclicRecognition.CartanFactorModel.realScaleProfile_apply _root_.OAI.PolycyclicRecognition.CartanFactorModel.sampledProbeProfile_apply _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.modelNilradicalLinearAction_apply _root_.OAI.PolycyclicRecognition.modelNilradicalRotation_apply _root_.OAI.PolycyclicRecognition.modelNilradicalRotation_mul _root_.OAI.PolycyclicRecognition.modelNilradicalRotation_one _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A single target Haar normalization for all concentrated probes -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra MeasureTheory Set Filter
open scoped Manifold Topology

variable {EG G : Type} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G]
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H Exp)
  (C : Set (H →ₗ[ℝ] ℝ)) (D : M.MeasuredCone F C)

set_option maxHeartbeats 1000000 in
/-- Every adapted target section gives exactly the same measure, not just
another scalar multiple of Haar measure. -/
theorem MeasuredCone.sectionMeasure_eq
    (σ τ : ContinuousMap D.Q.carrier F.N.carrier)
    (hσ : ∀ q, D.maps.quotient (σ q) = q)
    (hτ : ∀ q, D.maps.quotient (τ q) = q) :
    D.sectionMeasure M F C σ hσ = D.sectionMeasure M F C τ hτ := by
  let : IsTopologicalGroup F.N.carrier :=
    topologicalGroup_of_lieGroup (𝓘(ℝ, F.N.modelSpace)) ⊤
  let : IsTopologicalGroup D.Q.carrier :=
    topologicalGroup_of_lieGroup (𝓘(ℝ, D.Q.modelSpace)) ⊤
  let bQ := (finBasis ℝ ((cartanRootIdeal H) ⧸ M.coneWordIdeal C)).map
    D.Q.equiv.toLinearEquiv
  let coordQ := bQ.equivFun.symm.toContinuousLinearEquiv.toHomeomorph.trans D.maps.chartQ
  let : SecondCountableTopology D.Q.carrier := coordQ.symm.secondCountableTopology
  let : LocallyCompactSpace D.Q.carrier := coordQ.symm.isOpenEmbedding.locallyCompactSpace
  let bI := (finBasis ℝ (M.coneWordIdeal C)).map D.I.equiv.toLinearEquiv
  let coordI := bI.equivFun.symm.toContinuousLinearEquiv.toHomeomorph.trans D.maps.chartI
  let ke := kernelRealization D.maps.quotient D.maps.inclusion
    D.maps.inclusion_closed D.maps.inclusion_range
  let : SecondCountableTopology D.maps.quotient.ker :=
    (coordI.trans ke.toHomeomorph).symm.secondCountableTopology
  let : LocallyCompactSpace D.maps.quotient.ker :=
    (coordI.trans ke.toHomeomorph).symm.isOpenEmbedding.locallyCompactSpace
  let : D.measures.measureQ.IsHaarMeasure := D.measures.haarQ
  let : (D.kernelMeasure M F C).IsHaarMeasure := D.measures.haarKernel
  let : (D.kernelMeasure M F C).IsMulRightInvariant := D.measures.kernel_rightInvariant
  exact quotientSection_product_independent D.maps.quotient D.maps.quotient_continuous
    σ τ hσ hτ D.measures.measureQ (D.kernelMeasure M F C)

variable {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [IsTopologicalGroup F.N.carrier]

set_option maxHeartbeats 1000000 in
/-- Instantiate the published polar-region construction with twice the
concentration error and retain the fixed original target Haar measure.
The region threshold was chosen before the concentration error or its
path constant. -/
theorem MeasuredCone.fixed_polar_region_factory
    (K : ProperCone ℝ (StrongDual ℝ W)) (A : W →ₗ[ℝ] W) (ε : ℝ) (w : W)
    (height : G →* Multiplicative W)
    (act : G →* Equiv.Perm D.Q.carrier)
    (ν : Measure F.D.carrier) (cell : Set (F.N.carrier × F.D.carrier))
    (scale : ℕ → ℝ) (P₂ δ δ₀ : ℝ) (hδ : 0 < δ) (hδ₀ : δ ≤ δ₀)
    (regions : ∀ (η : ℕ → ℝ), (∀ n, 0 ≤ η n) → Tendsto η atTop (𝓝 0) →
      ∀ Cp Clog : ℝ, 0 ≤ Cp → 0 ≤ Clog →
      ∃ R : MeasuredProbeRegions D.maps.quotient D.measures.measureQ
        (D.kernelMeasure M F C) ν scale P₂,
        ∀ δ' : ℝ, 0 < δ' → δ' ≤ δ₀ →
        ∀ᶠ n in atTop, R.ControlsTwoPaths
          (fun u d => F.inclusionN u * F.inclusionD d) F.action (fun g q => act g q)
          height cell (A '' normalizedPolarTemplates K ε 0)
          (A '' normalizedPolarTemplates K ε 2) η Cp Clog δ' n) :
    ∀ (η : ℕ → ℝ), (∀ n, 0 ≤ η n) → Tendsto η atTop (𝓝 0) →
      ∀ Cp : ℝ, 0 ≤ Cp →
      ∃ R : MeasuredProbeRegions D.maps.quotient D.measures.measureQ
        (D.kernelMeasure M F C) ν scale P₂,
        D.sectionMeasure M F C D.maps.sectionMap D.maps.section_rightInverse =
          Measure.map (quotientSectionHomeomorph D.maps.quotient
            D.maps.quotient_continuous R.sectionMap R.section_rightInverse).symm
            (D.measures.measureQ.prod (D.kernelMeasure M F C)) ∧
        ∀ᶠ n in atTop, R.ControlsTwoPaths
          (fun u d => F.inclusionN u * F.inclusionD d) F.action (fun g q => act g q)
          height cell
          ((fun z => A (z - w)) '' polarSamplingTemplates K ε w 0)
          ((fun z => A (z - w)) '' polarSamplingTemplates K ε w 2)
          (fun n => 2 * η n) Cp Cp δ n := by
  intro η hη0 hη Cp hCp
  have htwo : Tendsto (fun n => 2 * η n) atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.mul hη
  obtain ⟨R, hR⟩ := regions (fun n => 2 * η n)
    (fun n => mul_nonneg (by norm_num) (hη0 n)) htwo Cp Cp hCp hCp
  refine ⟨R, ?_, ?_⟩
  · exact D.sectionMeasure_eq M F C D.maps.sectionMap R.sectionMap
      D.maps.section_rightInverse R.section_rightInverse
  · simpa only [recentered_polarSamplingTemplates] using hR δ hδ hδ₀

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanFixedPolarTargets
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.instFiniteRootOffsetConeIndex _root_.OAI.PolycyclicRecognition.instNonemptyRootOffsetConeIndex _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The fixed target measure and trace on a transformed polar cone -/

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
  [IsTopologicalGroup F.N.carrier]

set_option maxHeartbeats 1000000 in
/-- Normalize only the target quotient Haar measure. The published action,
its exact trace, and every later path region use this same fixed product
measure on the nilpotent factor. -/
theorem MeasuredCone.exists_fixed_polar_target_regions
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
    let E₂ := A '' normalizedPolarTemplates K ε 2
    ∃ (α : F.D.carrier →* MulAut D.Q.carrier) (act : G →* Equiv.Perm D.Q.carrier)
      (μQ : Measure D.Q.carrier) (c : Fin M.letterCount → ℕ)
      (β₂ : M.ConeIdealBases C),
      ∃ hμQ : μQ.IsHaarMeasure,
      let D' := D.withQuotientHaar M F C μQ hμQ
      let μN := D'.sectionMeasure M F C D'.maps.sectionMap D'.maps.section_rightInverse
      (∀ n d q, act (F.inclusionN n * F.inclusionD d) q = D.maps.quotient n * α d q) ∧
      (∀ i, ((M.supportIn T hunimod eW).weight i).toContinuousLinearMap ∉
        transformedPolarCone K A → c i = 0) ∧
      (∀ i, ((M.supportIn T hunimod eW).weight i).toContinuousLinearMap ∈
        transformedPolarCone K A → 0 < c i) ∧
      (∀ g E, μQ (act g '' E) = ENNReal.ofReal (Real.exp
        ((∑ i, (c i : ℝ) • ((M.supportIn T hunimod eW).weight i).toContinuousLinearMap)
          (height g).toAdd)) * μQ E) ∧
      M.IsMaximizingConeIdealBasis C bI ((M.supportIn T hunimod eW).weightSupport E₂) β₂ ∧
      ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ (scale : ℕ → ℝ),
        StrictMono scale → Tendsto scale atTop atTop → (∀ n, 1 ≤ scale n) →
        ∀ (w : W) (δ : ℝ), 0 < δ → δ ≤ δ₀ →
        ∀ (η : ℕ → ℝ), (∀ n, 0 ≤ η n) → Tendsto η atTop (𝓝 0) →
        ∀ Cp : ℝ, 0 ≤ Cp →
        ∃ R : MeasuredProbeRegions D.maps.quotient μQ
          (D.kernelMeasure M F C) ν scale
          (∑ j, M.coneIdealWordCost C
            ((M.supportIn T hunimod eW).weightSupport E₂) (β₂.val j)),
          μN = Measure.map (quotientSectionHomeomorph D.maps.quotient
            D.maps.quotient_continuous R.sectionMap R.section_rightInverse).symm
            (μQ.prod (D.kernelMeasure M F C)) ∧
          ∀ᶠ n in atTop, R.ControlsTwoPaths
            (fun u d => F.inclusionN u * F.inclusionD d) F.action (fun g q => act g q)
            height cell
            ((fun z => A (z - w)) '' polarSamplingTemplates K ε w 0)
            ((fun z => A (z - w)) '' polarSamplingTemplates K ε w 2)
            (fun n => 2 * η n) Cp Cp δ n := by
  dsimp only
  obtain ⟨α, act, μQ, c, β₂, hμQ, hact, hout, hin, hHaar, hβ₂, δ₀, hδ₀, hregions⟩ :=
    D.exists_uniform_polar_target_regions M F T hunimod eW
      hExp realize hNbij hDbij dynkinN dynkinD chartN hchartN chartD hchartD
      height hheight hpath hLheight hLip K A hK haarQ haarI haarD ν bN bI γ₀ hcell hε
  refine ⟨α, act, μQ, c, β₂, hμQ, hact, hout, hin, hHaar, hβ₂, δ₀, hδ₀, ?_⟩
  intro scale hs hscale hs1 w δ hδ hd η hη0 hη Cp hCp
  let C := heightConePreimage (H := H) T eW (transformedPolarCone K A)
  let D' := D.withQuotientHaar M F C μQ hμQ
  exact D'.fixed_polar_region_factory M F C K A.toLinearMap ε w height act ν cell
    scale _ δ δ₀ hδ hd
    (fun η hη0 hη Cp Clog hCp hClog =>
      hregions scale η hs hscale hs1 hη0 hη Cp Clog hCp hClog)
    η hη0 hη Cp hCp

end CartanWordModel
end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_FixedWeightContact
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instNonemptyBases _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_nonempty _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A common Euclidean contact point for every cone containing one root -/

noncomputable section
namespace PolycyclicRecognition

open Set

variable {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
  [FiniteDimensional ℝ W]

/-- All unit contact points for a nonzero functional coincide. -/
theorem weight_contact_unique (α : W →L[ℝ] ℝ) (hα : α ≠ 0)
    {p q : W} (hp : ‖p‖ = 1) (hq : ‖q‖ = 1)
    (hap : α p = ‖α‖) (haq : α q = ‖α‖) : p = q := by
  let v := (InnerProductSpace.toDual ℝ W).symm α
  have hv : ‖v‖ = ‖α‖ := (InnerProductSpace.toDual ℝ W).symm.norm_map α
  have hc (x : W) (hx : ‖x‖ = 1) (hax : α x = ‖α‖) : v = ‖α‖ • x := by
    have he : inner ℝ v x = ‖v‖ * ‖x‖ := by
      rw [show inner ℝ v x = α x from InnerProductSpace.toDual_symm_apply,
        hax, hv, hx, mul_one]
    simpa only [hx, one_smul, hv] using inner_eq_norm_mul_iff_real.mp he
  have he := congrArg (fun x : W => ‖α‖⁻¹ • x) ((hc p hp hap).symm.trans (hc q hq haq))
  simpa only [smul_smul, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hα), one_smul] using he

/-- The contact point is fixed before choosing any cone that contains the root. -/
theorem exists_polar_template_facet_slack_at
    {I : Type} [Fintype I] (α : I → W →L[ℝ] ℝ) (hne : ∀ i, α i ≠ 0)
    (i₀ : I) (p : W) (hp : ‖p‖ = 1) (hpα : α i₀ p = ‖α i₀‖)
    (C : ProperCone ℝ (W →L[ℝ] ℝ)) (hC : α i₀ ∈ C)
    {c c' : ℝ} (hc : 0 ≤ c) (hcc : c < c') :
    ∃ (ε₀ δ₀ : ℝ), 0 < ε₀ ∧ 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
      ∀ ε : ℝ, 0 ≤ ε → ε ≤ ε₀ → ∀ z ∈ conePolarTemplate C,
        ∀ i, α i ((1 - c' * δ) • p + ε • z) < (1 - c * δ) * ‖α i‖ := by
  classical
  obtain ⟨q, hq, hqα, hstrictq⟩ := exists_weight_contact_point (α i₀) (hne i₀)
  have hpq : p = q := weight_contact_unique (α i₀) (hne i₀) hp hq hpα hqα
  subst q
  have hstrict := hstrictq
  let ray (i : I) : Prop := ∃ t : ℝ, 0 < t ∧ α i = t • α i₀
  let m : Option I → ℝ := fun j => match j with
    | none => 1
    | some i => if ray i then 1 else
        (‖α i‖ - α i p) / ((c + c' + 1) * ‖α i‖)
  have hc' : 0 < c' := lt_of_le_of_lt hc hcc
  have hm : ∀ j, 0 < m j := by
    intro j
    cases j with
    | none => exact zero_lt_one
    | some i =>
      dsimp [m]
      split_ifs with h
      · exact zero_lt_one
      · exact div_pos (sub_pos.mpr (hstrict (α i) (hne i) h))
          (mul_pos (by linarith) (norm_pos_iff.mpr (hne i)))
  let τ := Finset.univ.inf' Finset.univ_nonempty m
  have hτ : 0 < τ := (Finset.lt_inf'_iff _).mpr (fun j _ => hm j)
  have hτm (i : I) : τ ≤ m (some i) :=
    Finset.inf'_le _ (Finset.mem_univ (some i))
  let ε₀ := τ / 2
  let δ₀ := min ε₀ (1 / (2 * (c' + 1)))
  have hε₀ : 0 < ε₀ := half_pos hτ
  have hδ₀ : 0 < δ₀ := lt_min hε₀ (by positivity)
  refine ⟨ε₀, δ₀, hε₀, hδ₀, ?_⟩
  intro δ hδ hδmax ε hε hεmax z hz i
  have hδτ : δ ≤ τ / 2 := hδmax.trans (min_le_left _ _)
  have hδbound : δ ≤ 1 / (2 * (c' + 1)) := hδmax.trans (min_le_right _ _)
  have hfactor : 0 ≤ 1 - c' * δ := by
    have hh := (le_div_iff₀ (show 0 < 2 * (c' + 1) by positivity)).mp hδbound
    nlinarith
  have hi : 0 < ‖α i‖ := norm_pos_iff.mpr (hne i)
  have happ : |α i p| ≤ ‖α i‖ := by simpa [hp] using (α i).le_opNorm p
  have haz : α i z ≤ ‖α i‖ := by
    exact ((le_abs_self _).trans ((α i).le_opNorm z)).trans
      ((mul_le_mul_of_nonneg_left hz.1 (norm_nonneg _)).trans_eq (mul_one _))
  simp only [map_add, map_smul, smul_eq_mul]
  by_cases hray : ray i
  · obtain ⟨t, ht, he⟩ := hray
    have hiC : α i ∈ C := by
      rw [he]
      exact C.smul_mem hC ht.le
    have hzneg : α i z ≤ 0 := hz.2 (α i) hiC
    have hfirst := mul_le_mul_of_nonneg_left (le_trans (le_abs_self _) happ) hfactor
    have hlast : ε * α i z ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hε hzneg
    have hgap : 0 < (c' - c) * δ * ‖α i‖ :=
      mul_pos (mul_pos (sub_pos.mpr hcc) hδ) hi
    nlinarith
  · have htau : τ * ((c + c' + 1) * ‖α i‖) ≤ ‖α i‖ - α i p := by
      apply (le_div_iff₀ (mul_pos (by linarith) hi)).mp
      simpa [m, hray] using hτm i
    have hneg : -α i p ≤ ‖α i‖ := (neg_le_abs _).trans happ
    have herror : -c' * δ * α i p ≤ c' * δ * ‖α i‖ := by
      nlinarith [mul_le_mul_of_nonneg_left hneg (mul_nonneg hc'.le hδ.le)]
    have hzerror : ε * α i z ≤ ε * ‖α i‖ := mul_le_mul_of_nonneg_left haz hε
    have htotal : (c + c') * δ * ‖α i‖ + ε * ‖α i‖ < ‖α i‖ - α i p := by
      have hδerr := mul_le_mul_of_nonneg_right hδτ
        (mul_nonneg (show 0 ≤ c + c' by linarith) hi.le)
      have hεerr := mul_le_mul_of_nonneg_right hεmax hi.le
      have hgap : 0 < ‖α i‖ - α i p := sub_pos.mpr (hstrict (α i) (hne i) hray)
      dsimp only [ε₀] at hεerr
      nlinarith
    nlinarith


end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanFixedSamplingGeometry
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finite_templateSymmetryGroup _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.instFiniteRootOffsetConeIndex _root_.OAI.PolycyclicRecognition.instFiniteSubtypeLinearEquivRealIdMemSubgroupLinearSupportSymmetryGroup _root_.OAI.PolycyclicRecognition.instNonemptyRootOffsetConeIndex _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.CartanFactorModel.heightRay_zero _root_.OAI.PolycyclicRecognition.CartanFactorModel.realScaleProfile_apply _root_.OAI.PolycyclicRecognition.CartanFactorModel.sampledProbeProfile_apply _root_.OAI.PolycyclicRecognition.cartanWeightDerivation_apply_root _root_.OAI.PolycyclicRecognition.cartanWeightDilation_apply _root_.OAI.PolycyclicRecognition.cartanWeightScale_add_apply _root_.OAI.PolycyclicRecognition.cartanWeightScale_zero_apply _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.nilshadowWeightDerivation_symm _root_.OAI.PolycyclicRecognition.nilshadowWeightOperator_symm _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Contact points and source templates in the actual Cartan height space -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra Set

variable {L W : Type} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {H : LieSubalgebra ℝ L} [H.IsCartanSubalgebra] (M : CartanWordModel H)
  {a : ℕ} (T : TriangularAdjoint L a)
  (hunimod : ∀ x : L, LinearMap.trace ℝ L (ad ℝ L x) = 0)
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)

set_option maxHeartbeats 1000000 in
/-- All cone tests for one root use the same unit contact point. Only the
positive template radius and enlargement threshold depend on the cone. -/
theorem exists_fixed_polar_sampling_geometry
    (i : Fin M.letterCount) (p : W) (hp : ‖p‖ = 1)
    (hpi : ((M.supportIn T hunimod eW).weight i).toContinuousLinearMap p =
      ‖((M.supportIn T hunimod eW).weight i).toContinuousLinearMap‖)
    (K : ProperCone ℝ (StrongDual ℝ W))
    (hi : ((M.supportIn T hunimod eW).weight i).toContinuousLinearMap ∈ K)
    {c : ℝ} (hc : 0 ≤ c) :
    ∃ (ε₀ δ₀ : ℝ), 0 < ε₀ ∧ 0 < δ₀ ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ → ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
        let w := (1 - (c + 1) * δ) • p
        let E := polarSamplingTemplates K ε w
        let V := samplingHeightDomain
          (fun j => ((M.supportIn T hunimod eW).weight j).toContinuousLinearMap)
          (1 - c * δ)
        0 < 1 - (c + 1) * δ ∧
        (∀ k, IsCompact (E k) ∧ Convex ℝ (E k) ∧ w ∈ E k ∧ E k ⊆ V) ∧
        IsOpen V ∧ Convex ℝ V ∧
        V ⊆ (fun y : W => (1 - c * δ) • y) '' interior (M.samplingPolytope T hunimod eW) ∧
        V ⊆ M.samplingPolytope T hunimod eW := by
  let α := fun j => ((M.supportIn T hunimod eW).weight j).toContinuousLinearMap
  obtain ⟨ε₀, δ₁, hε₀, hd₁, hinside⟩ :=
    exists_polar_template_facet_slack_at α (M.sampling_weight_ne_zero T hunimod eW)
      i p hp hpi K hi hc (by linarith : c < c + 1)
  let δ₀ := min δ₁ (1 / (2 * (c + 2)))
  have hd₀ : 0 < δ₀ := lt_min hd₁ (by positivity)
  refine ⟨ε₀, δ₀, hε₀, hd₀, ?_⟩
  intro ε hε hεmax δ hδ hδ₀
  have hbound : δ ≤ 1 / (2 * (c + 2)) := hδ₀.trans (min_le_right _ _)
  have hmul := (le_div_iff₀ (by positivity : 0 < 2 * (c + 2))).mp hbound
  have hfactor : 0 < 1 - (c + 1) * δ := by nlinarith
  have hfacets : ∀ k : Fin 3, ∀ z ∈ conePolarTemplate K, ∀ j,
      α j ((1 - (c + 1) * δ) • p + threePolarRadii ε k • z) <
        (1 - c * δ) * ‖α j‖ := by
    intro k z hz j
    have hrad : 0 ≤ threePolarRadii ε k ∧ threePolarRadii ε k ≤ ε := by
      fin_cases k <;> dsimp [threePolarRadii] <;> constructor <;> linarith
    exact hinside δ hδ (hδ₀.trans (min_le_left _ _)) _ hrad.1
      (hrad.2.trans hεmax) z hz j
  dsimp only
  exact ⟨hfactor, polar_sampling_template_geometry α K p ε δ c hc hδ hfactor hfacets⟩

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanOffsetThreshold
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Choosing the source enlargement before the sampled frames -/

namespace PolycyclicRecognition

set_option maxHeartbeats 1000000 in
/-- The source enlargement and the vanishing-rate tolerance are chosen
from the fixed metric constants and target restriction threshold. Neither
depends on the source section, the sample, or the path-length constant. -/
theorem exists_source_offset_threshold
    {A B Λ c target source : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hΛ : 0 ≤ Λ) (hc : 0 ≤ c)
    (htarget : 0 < target) (hsource : 0 < source) :
    ∃ δ₀ ε : ℝ, 0 < δ₀ ∧ 0 < ε ∧ δ₀ ≤ source ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
        c * δ ≤ 1 ∧ Λ * (A * δ + B * ε) ≤ target := by
  let a := (Λ + 1) * (A + 1)
  let b := (Λ + 1) * (B + 1)
  have ha : 0 < a := mul_pos (by linarith) (by linarith)
  have hb : 0 < b := mul_pos (by linarith) (by linarith)
  let δ₀ := min source (min (1 / (c + 1)) (target / (2 * a)))
  let ε := target / (2 * b)
  have hδ₀ : 0 < δ₀ := lt_min hsource
    (lt_min (div_pos zero_lt_one (by linarith)) (div_pos htarget (by positivity)))
  have hε : 0 < ε := div_pos htarget (by positivity)
  refine ⟨δ₀, ε, hδ₀, hε, min_le_left _ _, ?_⟩
  intro δ hδ hd
  have hdc : δ ≤ 1 / (c + 1) :=
    hd.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hda : δ ≤ target / (2 * a) :=
    hd.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hca : δ * (c + 1) ≤ 1 := (le_div_iff₀ (by linarith)).mp hdc
  have hda' : δ * (2 * a) ≤ target := (le_div_iff₀ (by positivity)).mp hda
  have heb : ε * (2 * b) = target := div_mul_cancel₀ _ (by positivity)
  have hΛA : Λ * A ≤ a := by dsimp [a] <;> nlinarith
  have hΛB : Λ * B ≤ b := by dsimp [b] <;> nlinarith
  have hfirst := mul_le_mul_of_nonneg_right hΛA hδ.le
  have hsecond := mul_le_mul_of_nonneg_right hΛB hε.le
  constructor <;> nlinarith

end PolycyclicRecognition

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanSourceDilation
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The same Cartan dilation in tiling, concentration, and source measure -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule
open scoped Manifold

variable {EG G W : Type} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H Exp)
  (hbij : Function.Bijective F.ExpN)
  (chartN : GroupLieAlgebra (𝓘(ℝ, F.N.modelSpace)) F.N.carrier ≃ₜ F.N.carrier)
  (hchartN : ∀ v, chartN v = F.ExpN v)
  (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)

set_option maxHeartbeats 1000000 in
theorem sourceDilation_apply_exp (h : H) (v : cartanRootIdeal H) :
    M.sourceDilation T F hbij chartN hchartN dynkinN h (F.ExpN (F.N.equiv v)) =
      F.ExpN (F.N.equiv (cartanIdealWeightDilation T H h v)) :=
  integrateNilpotentLieEquiv_apply_exp F.N.equiv F.ExpN hbij dynkinN F.isExpN
    M.bound_zero (cartanIdealWeightDilation T H h) v

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanOneConeThreshold
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_countable _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_nonempty _root_.OAI.PolycyclicRecognition.finitelyGeneratedSubgroupIndex_countable _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.instFiniteRootOffsetConeIndex _root_.OAI.PolycyclicRecognition.instNonemptyRootOffsetConeIndex _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.unitaryCentralFixed_complete _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A polar trace inequality uniformly before choosing a neighboring row -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule MeasureTheory Filter Set
open scoped Manifold Topology ENNReal NNReal BigOperators

attribute [local instance] stationaryL2Action zeroMeanL2Action

variable {EG G W I : Type} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G]
  [IsTopologicalGroup G] [IsIsometricSMul G G] [ProperSpace G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  [MeasurableSpace W] [BorelSpace W] [SecondCountableTopology W]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H) [Nonempty (Fin M.letterCount)]
  [Nonempty (Fin (finrank ℝ (cartanRootIdeal H)))]
  {Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H Exp)
  (hunimod : ∀ x : GroupLieAlgebra (𝓘(ℝ, EG)) G, LinearMap.trace ℝ _ (ad ℝ _ x) = 0)
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)
  [IsTopologicalGroup F.N.carrier] [SecondCountableTopology F.N.carrier]
  [IsTopologicalGroup F.D.carrier] [SecondCountableTopology F.D.carrier]
  [Fintype I] [DecidableEq I] {Λ : ℝ≥0}
  [MeasurableSpace (NormalizedPair G Λ)] [BorelSpace (NormalizedPair G Λ)]
  [MeasurableSpace C((Fin (finrank ℝ H) → ℝ), W)]
  [BorelSpace C((Fin (finrank ℝ H) → ℝ), W)]

local notation "Eall" => M.samplingPolytope T hunimod eW

set_option maxHeartbeats 1000000 in
/-- The finite cone and label are fixed before the scale, maps or weak law.
All sampling, contact and target-volume data are constructed from the
published exponential inputs and the actual Cartan models. -/
theorem exists_one_cone_offset_threshold_oai
    (hExp : IsGroupExponential Exp)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
    (haarD : NilpotentExponentialHaarInput F.D.modelSpace F.D.carrier)
    (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
    (dynkinD : NilpotentDynkinExpansionInput F.D.modelSpace F.D.carrier)
    (chartN : GroupLieAlgebra (𝓘(ℝ, F.N.modelSpace)) F.N.carrier ≃ₜ F.N.carrier)
    (hchartN : ∀ x, chartN x = F.ExpN x)
    (chartD : GroupLieAlgebra (𝓘(ℝ, F.D.modelSpace)) F.D.carrier ≃ₜ F.D.carrier)
    (hchartD : ∀ x, chartD x = F.ExpD x)
    (m : Measure G) [m.IsHaarMeasure] [m.IsMulRightInvariant]
    (νD : Measure F.D.carrier) [νD.IsHaarMeasure] [SFinite νD]
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
    (bN : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (γ : M.Bases)
    (hγ : IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList bN)
      (M.boxCost T hunimod eW Eall) γ.val)
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
    (rem : RemezPolynomialInput) (hdim : 1 ≤ finrank ℝ (cartanRootIdeal H))
    (pivot : Fin M.letterCount → H) (i : Fin M.letterCount)
    (hcanonical : cartanHeightSection T H (heightProjection T.character (pivot i)) = pivot i)
    (hunit : ‖eW (heightProjection T.character (pivot i))‖ = 1)
    (hcontact : ((M.supportIn T hunimod eW).weight i).toContinuousLinearMap
      (eW (heightProjection T.character (pivot i))) =
        ‖((M.supportIn T hunimod eW).weight i).toContinuousLinearMap‖)
    (hpositive : 0 < M.weight i (pivot i))
    {lo hi c B : ℝ} (hc : 0 ≤ c) (hhi : 0 ≤ hi) (hB : 0 ≤ B)
    (hcost : ∀ w : M.wordList, lo ≤ M.boxCost T hunimod eW Eall w ∧
      M.boxCost T hunimod eW Eall w ≤ hi)
    (hgap : (M.bound : ℝ) * hi < c * lo)
    (σchamber : Fin M.letterCount → Bool)
    (hσchamber : (weightChamber (fun j =>
      ((M.supportIn T hunimod eW).weight j).toContinuousLinearMap) σchamber).Nonempty)
    (Profiles : Set C((Fin (finrank ℝ H) → ℝ), W))
    [MeasurableSpace Profiles] [BorelSpace Profiles] [BorelSpace (Profiles × Profiles)]
    (K : ProperCone ℝ (StrongDual ℝ W))
    (hK : (K : ConvexCone ℝ (StrongDual ℝ W)).Salient)
    (hiK : ((M.supportIn T hunimod eW).weight i).toContinuousLinearMap ∈ K)
    (A : templateSymmetryGroup (M.supportIn T hunimod eW))
    (Ds : M.MeasuredCone F (heightConePreimage T eW K))
    (dynkinI : NilpotentDynkinExpansionInput Ds.I.modelSpace Ds.I.carrier)
    (haarI : NilpotentExponentialHaarInput Ds.I.modelSpace Ds.I.carrier)
    (Dt₀ : M.MeasuredCone F (heightConePreimage T eW (transformedPolarCone K A.val)))
    (haarQt : NilpotentExponentialHaarInput Dt₀.Q.modelSpace Dt₀.Q.carrier)
    (haarIt : NilpotentExponentialHaarInput Dt₀.I.modelSpace Dt₀.I.carrier) :
    ∃ coeff : Fin M.letterCount → ℕ,
      (∀ j, ((M.supportIn T hunimod eW).weight j).toContinuousLinearMap ∉
        transformedPolarCone K A.val → coeff j = 0) ∧
      (∀ j, ((M.supportIn T hunimod eW).weight j).toContinuousLinearMap ∈
        transformedPolarCone K A.val → 0 < coeff j) ∧
      ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
      ∀ row : AffineNeighborRow T M F hunimod eW π bN Eall γ X βD
        haarN chartN hchartN pivot c B δ Profiles (Λ := Λ),
      row.mode = i → row.label₁ = A → row.label₂ = A →
        (∑ j, (coeff j : ℝ) • ((M.supportIn T hunimod eW).weight j).toContinuousLinearMap)
          (row.offset₂ - row.offset₁) ≤ 0 := by
  classical
  have hbijN : Function.Bijective F.ExpN := funext hchartN ▸ chartN.bijective
  have hbijD : Function.Bijective F.ExpD := funext hchartD ▸ chartD.bijective
  let : LocallyCompactSpace F.N.carrier := F.closedN.locallyCompactSpace
  let : LocallyCompactSpace F.D.carrier := F.closedD.locallyCompactSpace
  let : IsTopologicalGroup Ds.I.carrier := topologicalGroup_of_lieGroup (𝓘(ℝ, Ds.I.modelSpace)) ⊤
  let : IsTopologicalGroup Dt₀.Q.carrier := topologicalGroup_of_lieGroup (𝓘(ℝ, Dt₀.Q.modelSpace)) ⊤
  let bIs := finBasis ℝ (M.coneWordIdeal (heightConePreimage T eW K))
  let bIt := finBasis ℝ (M.coneWordIdeal (heightConePreimage T eW (transformedPolarCone K A.val)))
  let icoord := ((bIs.map Ds.I.equiv.toLinearEquiv).equivFun.symm.toContinuousLinearEquiv.toHomeomorph).trans Ds.maps.chartI
  let : SecondCountableTopology Ds.I.carrier := icoord.symm.secondCountableTopology
  obtain ⟨U, hU, hUone, hsmall⟩ := exists_small_factor_cell F.inclusionN F.inclusionD
    F.closedN.continuous F.closedD.continuous
  obtain ⟨ε₀, δg, hε₀, hδg, hgeometry⟩ := M.exists_fixed_polar_sampling_geometry
    T hunimod eW i _ hunit hcontact K hiK hc
  let ε := ε₀
  have hε : 0 < ε := hε₀
  obtain ⟨actionQ, act, μQ, coeff, βtarget, hμQ, hact, hout, hin, hHaar,
      hβtarget, δtarget, hδtarget, hregions⟩ :=
    Dt₀.exists_fixed_polar_target_regions M F T hunimod eW hExp realize
      hbijN hbijD dynkinN dynkinD chartN hchartN chartD hchartD π hπExp hpath
      Kπ.coe_nonneg (fun x y => by simpa only [dist_eq_norm] using hπ.dist_le_mul x y)
      K A.val hK haarQt haarIt haarD νD bN bIt γ hU hε
  let Ct := heightConePreimage (H := H) T eW (transformedPolarCone K A.val)
  let Dt := Dt₀.withQuotientHaar M F Ct μQ hμQ
  let : IsTopologicalGroup Dt.Q.carrier :=
    topologicalGroup_of_lieGroup (𝓘(ℝ, Dt.Q.modelSpace)) ⊤
  let μN := Dt.sectionMeasure M F Ct Dt.maps.sectionMap Dt.maps.section_rightInverse
  let : μN.IsHaarMeasure := Dt.sectionMeasure_isHaar M F Ct
    Dt.maps.sectionMap Dt.maps.section_rightInverse
  obtain ⟨hUmeas, hUzero, hUtop⟩ := small_factor_cell_measure μN νD hU ⟨1, hUone⟩
  obtain ⟨β, bQ, lift, Rbox, δs, hlift, hβ, hRbox, hδs, hsamplers⟩ :=
    Ds.exists_canonical_polar_samplers T M F hunimod eW K hExp realize haarN dynkinN
      hbijN chartN hchartN dynkinI haarI bN bIs i hiK (pivot i) hpositive
      (c + 1) B ε (by linarith) hB hε
  obtain ⟨Ca, Cb, hCa, hCb, hbridge⟩ := M.exists_uniform_contact_step_bridge_m (I := Ds.I.carrier)
    T F hunimod eW (heightConePreimage T eW K) hExp realize haarN haarD dynkinN
      hbijN chartN hchartN bN i (pivot i) hpositive (by linarith : 0 ≤ c + 1) hB
  obtain ⟨δ₀, η, hδ₀, hη, hδsource, hthreshold⟩ :=
    exists_source_offset_threshold hCa hCb hΛ.le (by linarith : 0 ≤ c + 1)
      hδtarget (lt_min hδg hδs)
  refine ⟨coeff, hout, hin, δ₀, hδ₀, ?_⟩
  intro δ hδ hd row hmode hlabel₁ hlabel₂
  have hδg' : δ ≤ δg := (hd.trans hδsource).trans (min_le_left _ _)
  have hδs' : δ ≤ δs := (hd.trans hδsource).trans (min_le_right _ _)
  obtain ⟨hδc, herror⟩ := hthreshold δ hδ hd
  obtain ⟨u, hu, hmono, hs1⟩ := exists_strictMono_scale_subsequence row.scale row.grows
  let row₁ := row.reindex T M F hunimod eW π bN Eall γ X βD
    haarN chartN hchartN pivot c B δ Profiles u hu
  have htime₁ (n) : |row₁.time n| ≤ row₁.radius n * Real.exp
      ((M.weight i (pivot i) + δ * B) * row₁.scale n) := by
    change |row.time (u n)| ≤ row.radius (u n) * Real.exp
      ((M.weight i (pivot i) + δ * B) * row.scale (u n))
    simpa only [hmode] using row.time_bound (u n)
  have hroot₁ (n) : F.inclusionN (row₁.step n) =
      Exp (row₁.time n • (M.letter i : GroupLieAlgebra (𝓘(ℝ, EG)) G)) := by
    change F.inclusionN (row.step (u n)) =
      Exp (row.time (u n) • (M.letter i : GroupLieAlgebra (𝓘(ℝ, EG)) G))
    simpa only [hmode] using row.root_step (u n)
  obtain ⟨n₀, P, hbQ, hL, hconj⟩ := hsamplers δ hδ hδs'
    row₁.scale hmono row₁.grows (fun n => zero_lt_one.trans_le (hs1 n))
    row₁.radius row₁.time row₁.radius_subexponential htime₁ row₁.step hroot₁
  have htail : StrictMono (fun n : ℕ => n + n₀) := by
    intro m n hmn
    exact Nat.add_lt_add_right hmn n₀
  let row₂ := row₁.reindex T M F hunimod eW π bN Eall γ X βD
    haarN chartN hchartN pivot c B δ Profiles (fun n => n + n₀) htail
  have hmono₂ : StrictMono row₂.scale := hmono.comp htail
  have hs₂ (n) : 1 ≤ row₂.scale n := hs1 (n + n₀)
  let p := eW (heightProjection T.character (pivot i))
  let w := (1 - (c + 1) * δ) • p
  let contact := (1 - (c + 1) * δ) • pivot i
  let h := fun n => (row₂.scale n * (1 - (c + 1) * δ)) • pivot i
  let S := fun n => M.sourceDilation T F hbijN chartN hchartN dynkinN (h n)
  obtain ⟨hfactor, hgeom, hV, hVconv, hVinside, hVall⟩ := hgeometry ε hε le_rfl δ hδ hδg'
  let V := samplingHeightDomain
    (fun j => ((M.supportIn T hunimod eW).weight j).toContinuousLinearMap) (1 - c * δ)
  have hcontactHeight : eW (heightProjection T.character contact) = w := by
    simp only [contact, w, p, SetLike.val_smul, map_smul]
  have hsection : cartanHeightSection T H (eW.symm w) = contact := by
    simp only [w, p, contact, map_smul, eW.symm_apply_apply, hcanonical]
  have hS (n) (v : cartanRootIdeal H) : S n (F.ExpN (F.N.equiv v)) =
      F.ExpN (F.N.equiv (cartanIdealWeightDilation T H
        (row₂.scale n • cartanHeightSection T H (eW.symm w)) v)) := by
    rw [hsection]
    simpa only [S, h, contact, smul_smul] using
      M.sourceDilation_apply_exp T F hbijN chartN hchartN dynkinN (h n) v
  have hb := hbridge (Ds.maps.expI ∘ Ds.I.equiv) (normalizedPolarTemplates K ε)
    (fun _ => β) P.ambient (fun j => ε * M.polarProbeWidths T hunimod eW K j)
    row₂.scale _ Ds.maps.inclusion P.tiles P.anchor P.chain Ds.Q Ds.maps.chartQ
    Ds.maps.quotient Ds.maps.inclusion_closed Ds.maps.inclusion_range
    row₂.radius row₂.grows (fun n => zero_le_one.trans (hs₂ n)) row₂.radius_nonneg
    row₂.radius_subexponential η hη δ hδ.le hδc row₂.base row₂.step row₂.time
    (fun n => by
      change |row₁.time (n + n₀)| ≤ row₁.radius (n + n₀) * Real.exp
        ((M.weight i (pivot i) + B * δ) * row₁.scale (n + n₀))
      simpa only [mul_comm B δ] using htime₁ (n + n₀))
    (fun n => hroot₁ (n + n₀))
  have hE : IsCompact Eall := M.isCompact_samplingPolytope T hunimod eW
  have hne : (Eall).Nonempty := ⟨0, by
    intro j
    simpa only [map_zero] using norm_nonneg (((M.supportIn T hunimod eW).weight j).toContinuousLinearMap)⟩
  have hN : Continuous F.ExpN := funext hchartN ▸ chartN.continuous
  have hD : Continuous F.ExpD := funext hchartD ▸ chartD.continuous
  have hlabels : row₂.label₂ = row₂.label₁ := hlabel₂.trans hlabel₁.symm
  exact AffineNeighborRow.polar_offset_nonpos
    (T := T) (M := M) (F := F) (hunimod := hunimod) (eW := eW)
    (π := π) (bN := bN) («Eall» := Eall) (γ := γ) (X := X) (βD := βD)
    (haarN := haarN) (chartN := chartN) (hchartN := hchartN)
    (pivotRoots := pivot) (c := c) (B := B) (δ := δ) (Profiles := Profiles)
    (row := row₂) (scale := row₂.scale) (A := A) (hscale := rfl) (hlabel := hlabel₁) (K := K) (D := Ds) (β := β) (Rbox := Rbox) (P := P)
    (w := w) (S := S) (βtarget := βtarget) (Dt := Dt)
    (hExp := hExp) (realize := realize) (haarD := haarD)
    (dynkinN := dynkinN) (dynkinD := dynkinD) (m := m)
    (hπExp := hπExp) (hdec := hdec) (hvan := hvan) (hΛ := hΛ)
    (hπ := hπ) (hpath := hpath) (hE := hE) (hne := hne) (γaux := γ)
    (hβ := hγ) (hweights := M.sampling_weightSupport_pos T hunimod eW)
    (hδ := hδ) (hc := hc) (hhi := hhi) (ht := by linarith)
    (hcost := hcost) (hgap := hgap) (hDnil := hDnil) (hDletters := hDletters)
    (bD₀ := bD₀) (hβD := hβD) (aN := aN) (hmN := hmN) (aD := aD) (hmD := hmD)
    (hmono := hmono₂) (hscale1 := hs₂)
    (hBE := (hgeom 1).2.2.2.trans hVall)
    (hφsource := hconj) (rem := rem) (hdim := hdim) (hN := hN) (hD := hD)
    (pivot := contact) (V := V) (hV := hV) (hVconv := hVconv)
    (hEc := fun k => (hgeom k).1) (hEconv := fun k => (hgeom k).2.1)
    (hpivot := fun k => by simpa only [hcontactHeight, polarSamplingTemplates, normalizedPolarTemplates, w, p] using (hgeom k).2.2.1)
    (hEV := fun k => (hgeom k).2.2.2) (hVheight := hVinside)
    (σchamber := σchamber) (hσchamber := hσchamber) (hlabels := hlabels)
    (haarI := haarI) (bI := bIs) (hε := hε) (hRbox := hRbox.le) (hβsource := hβ)
    (bItarget := bIt) (hβtarget := hβtarget) (hS := hS)
    (Dbridge := Ca * δ + Cb * η) (δtarget := δtarget) (hδtarget := hδtarget) (hDb := herror)
    (hbridge := by
      filter_upwards [hb] with n hn
      intro y
      simpa only [S, h, contact, smul_smul, SetLike.val_smul] using hn ⟨y.val, y.property⟩)
    (νD := νD) (actionQ := actionQ) (act := act) (hact := hact)
    (cell := U) (hcell := hUmeas) (hcell0 := hUzero) (hcelltop := hUtop) (hsmall := hsmall)
    (regionFactory := fun η hη0 hη Cp hCp => by
      convert hregions row₂.scale hmono₂ row₂.grows hs₂ w δtarget hδtarget le_rfl η hη0 hη Cp hCp using 1 <;>
        simp only [hcontactHeight, polarSamplingTemplates, normalizedPolarTemplates,
          Dt, Ct, MeasuredCone.withQuotientHaar, MeasuredCone.kernelMeasure] <;> rfl)
    (ell := ∑ j, (coeff j : ℝ) • ((M.supportIn T hunimod eW).weight j).toContinuousLinearMap)
    (hHaar := hHaar)

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

theorem solution : type_of% @OAI.PolycyclicRecognition.CartanWordModel.exists_one_cone_offset_threshold_oai := @OAI.PolycyclicRecognition.CartanWordModel.exists_one_cone_offset_threshold_oai
