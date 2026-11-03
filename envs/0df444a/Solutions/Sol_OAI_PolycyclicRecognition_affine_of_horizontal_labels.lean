-- Prove2me | solution 1 for OAI.PolycyclicRecognition.affine_of_horizontal_labels
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-02T23:40:17.563764+00:00
-- url     : https://prove2.me/submissions/3e2f8bb4-6c4c-43e8-9983-89e0a2363d5e

import Mathlib
import Definitions.Def_OAIQ093D015

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_ActiveRayConstraints
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The active hyperplanes of a polyhedral extreme ray

If a direction annihilates every inequality active at an extreme ray, small
positive and negative perturbations stay in the cone. Extremality therefore
forces that direction onto the ray's line. The cone inequalities choose the
nonnegative half-line.
-/

noncomputable section

namespace PolycyclicRecognition

open Set Filter
open scoped Topology

variable {W I : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [Finite I]

theorem exists_two_sided_cone_perturbation (α : I → W →L[ℝ] ℝ)
    {w x : W} (hw : w ∈ linearInequalityCone α)
    (hx : ∀ i, α i w = 0 → α i x = 0) :
    ∃ t : ℝ, 0 < t ∧ w + t • x ∈ linearInequalityCone α ∧
      w - t • x ∈ linearInequalityCone α := by
  have hevent (i : I) : ∀ᶠ t : ℝ in 𝓝 0,
      0 ≤ α i (w + t • x) ∧ 0 ≤ α i (w - t • x) := by
    by_cases hi : α i w = 0
    · exact Eventually.of_forall (fun t => by simp only [map_add, map_sub, map_smul,
        hi, hx i hi, smul_eq_mul, mul_zero, add_zero, sub_zero, le_refl, and_self])
    · have hp : 0 < α i w := lt_of_le_of_ne (hw i) (Ne.symm hi)
      have hp' : 0 < α i (w + (0 : ℝ) • x) := by simpa using hp
      have hm' : 0 < α i (w - (0 : ℝ) • x) := by simpa using hp
      have hplus : Continuous (fun t : ℝ => α i (w + t • x)) := by fun_prop
      have hminus : Continuous (fun t : ℝ => α i (w - t • x)) := by fun_prop
      filter_upwards [(isOpen_lt continuous_const hplus).mem_nhds hp',
        (isOpen_lt continuous_const hminus).mem_nhds hm'] with t ht hu
      exact ⟨ht.le, hu.le⟩
  have hall := eventually_all.mpr hevent
  obtain ⟨ε, hε, he⟩ := Metric.eventually_nhds_iff.mp hall
  have hsmall : dist (ε / 2) 0 < ε := by
    rw [Real.dist_eq, sub_zero, abs_of_pos (half_pos hε)]
    exact half_lt_self hε
  exact ⟨ε / 2, by positivity, fun i => (he hsmall i).1, fun i => (he hsmall i).2⟩

/-- This uses the standard `IsExtreme` predicate on the actual nonnegative
ray, rather than assuming a description of the active hyperplanes. -/
theorem eq_smul_of_active_constraints (α : I → W →L[ℝ] ℝ) {w x : W}
    (hExt : IsExtreme ℝ (linearInequalityCone α) (nonnegativeRay w))
    (hx : ∀ i, α i w = 0 → α i x = 0) : ∃ r : ℝ, x = r • w := by
  have hw : w ∈ linearInequalityCone α := hExt.subset ⟨1, zero_le_one, by simp⟩
  obtain ⟨t, ht, hp, hm⟩ := exists_two_sided_cone_perturbation α hw hx
  have hmid : w ∈ openSegment ℝ (w + t • x) (w - t • x) := by
    refine ⟨(1 / 2 : ℝ), (1 / 2 : ℝ), by norm_num, by norm_num, by norm_num, ?_⟩
    rw [smul_add, smul_sub]
    calc
      (1 / 2 : ℝ) • w + (1 / 2 : ℝ) • (t • x) +
          ((1 / 2 : ℝ) • w - (1 / 2 : ℝ) • (t • x)) =
          (1 / 2 : ℝ) • w + (1 / 2 : ℝ) • w := by abel
      _ = w := by rw [← add_smul]; norm_num
  obtain ⟨r, _hr, he⟩ := hExt.left_mem_of_mem_openSegment hp hm
    (show w ∈ nonnegativeRay w from ⟨1, zero_le_one, by simp⟩) hmid
  have htx : t • x = (r - 1) • w := by
    calc
      t • x = (w + t • x) - w := by abel
      _ = r • w - (1 : ℝ) • w := by rw [he, one_smul]
      _ = (r - 1) • w := (sub_smul r 1 w).symm
  refine ⟨t⁻¹ * (r - 1), ?_⟩
  calc
    x = t⁻¹ • (t • x) := by rw [smul_smul, inv_mul_cancel₀ ht.ne', one_smul]
    _ = (t⁻¹ * (r - 1)) • w := by rw [htx, smul_smul]

theorem mem_ray_of_active_constraints (α : I → W →L[ℝ] ℝ)
    (hsep : ∀ x : W, (∀ i, α i x = 0) → x = 0) {w x : W}
    (hExt : IsExtreme ℝ (linearInequalityCone α) (nonnegativeRay w))
    (hxcone : x ∈ linearInequalityCone α)
    (hx : ∀ i, α i w = 0 → α i x = 0) : x ∈ nonnegativeRay w := by
  obtain ⟨r, rfl⟩ := eq_smul_of_active_constraints α hExt hx
  by_cases hw : w = 0
  · exact ⟨0, le_rfl, by simp [hw]⟩
  have hwcone : w ∈ linearInequalityCone α := hExt.subset ⟨1, zero_le_one, by simp⟩
  have hi : ∃ i, 0 < α i w := by
    by_contra! hn
    apply hw
    apply hsep
    intro i
    exact le_antisymm (hn i) (hwcone i)
  obtain ⟨i, hi⟩ := hi
  have hri := hxcone i
  simp only [map_smul, smul_eq_mul] at hri
  exact ⟨r, by nlinarith, rfl⟩

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_GeneratorSchemes
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite generator schemes with locally open endpoint maps

A conjugated-generator basis gives a single finite scheme, with fixed
conjugating words, whose endpoint map covers a neighborhood of the identity.
The logarithm of that map has the identity-rank differential proved from BCH.
-/

noncomputable section

namespace PolycyclicRecognition

open Module

variable {I L : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {G : Type*} [Group G]

variable (X : I → L) (Exp : L → G)

attribute [local instance] OAI.PolycyclicRecognition.generatorSchemeNormedAddCommGroup
attribute [local instance] OAI.PolycyclicRecognition.generatorSchemeNormedSpace
theorem generatorGroupWord_append (u v : List (I × ℝ)) :
    generatorGroupWord X Exp (u ++ v) =
      generatorGroupWord X Exp u * generatorGroupWord X Exp v := by
  simp only [generatorGroupWord, List.map_append, List.prod_append]

theorem generatorGroupWord_inverse (hneg : ∀ x, Exp (-x) = (Exp x)⁻¹)
    (w : List (I × ℝ)) :
    generatorGroupWord X Exp (inverseGeneratorWord w) = (generatorGroupWord X Exp w)⁻¹ := by
  induction w with
  | nil => simp [inverseGeneratorWord]
  | cons p w ih =>
    rcases p with ⟨i, t⟩
    simp only [inverseGeneratorWord, List.reverse_cons, List.map_append, List.map_cons,
      List.map_nil, generatorGroupWord_append, generatorGroupWord_cons,
      generatorGroupWord_nil, mul_one, mul_inv_rev] at *
    rw [ih]
    congr 1
    simpa only [neg_smul] using hneg (t • X i)

attribute [local instance 100] LieRing.ofAssociativeRing

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_LipschitzProfileFTC
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Fundamental integral identities for Lipschitz profile lines -/

noncomputable section

namespace PolycyclicRecognition

open MeasureTheory Set Filter
open scoped NNReal

theorem scalar_lipschitz_fundamental_identity
    {f q : ℝ → ℝ} {C : ℝ≥0} {T : ℝ} (hT : 0 ≤ T)
    (hf : LipschitzOnWith C f (Icc 0 T))
    (hq : ∀ᵐ t ∂volume.restrict (Icc 0 T), HasDerivAt f (q t) t) :
    IntervalIntegrable q volume 0 T ∧
      ∀ t ∈ Icc 0 T, f t - f 0 = ∫ s in 0..t, q s := by
  have hac : AbsolutelyContinuousOnInterval f 0 T := by
    apply LipschitzOnWith.absolutelyContinuousOnInterval
    simpa only [uIcc_of_le hT] using hf
  have heq : deriv f =ᵐ[volume.restrict (Icc 0 T)] q := hq.mono (fun _ ht => ht.deriv)
  have heqt (t : ℝ) (ht : t ∈ Icc 0 T) : deriv f =ᵐ[volume.restrict (uIoc 0 t)] q := by
    rw [uIoc_of_le ht.1]
    apply heq.filter_mono
    apply ae_mono
    exact Measure.restrict_mono
      (show Ioc (0 : ℝ) t ⊆ Icc 0 T from fun _ hs => ⟨hs.1.le, hs.2.trans ht.2⟩) le_rfl
  refine ⟨hac.intervalIntegrable_deriv.congr_ae (heqt T ⟨hT, le_rfl⟩), ?_⟩
  intro t ht
  have hac' : AbsolutelyContinuousOnInterval f 0 t :=
    hac.mono (by
      simp only [uIcc_of_le ht.1, uIcc_of_le hT]
      exact Icc_subset_Icc le_rfl ht.2)
  exact hac'.integral_deriv_eq_sub.symm.trans (intervalIntegral.integral_congr_ae_restrict (heqt t ht))

theorem profile_weight_fundamental_identities
    {W I : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    (α : I → W →L[ℝ] ℝ) {h q : ℝ → W} {C : ℝ≥0} {T : ℝ} (hT : 0 ≤ T)
    (hh : LipschitzOnWith C h (Icc 0 T))
    (hq : ∀ᵐ t ∂volume.restrict (Icc 0 T), HasDerivAt h (q t) t) :
    (∀ i, IntervalIntegrable (fun t => α i (q t)) volume 0 T) ∧
      ∀ i t, t ∈ Icc 0 T → α i (h t - h 0) = ∫ s in 0..t, α i (q s) := by
  have hf (i : I) := scalar_lipschitz_fundamental_identity hT
    ((α i).lipschitz.comp_lipschitzOnWith hh)
    (hq.mono (fun t ht => (α i).hasFDerivAt.comp_hasDerivAt t ht))
  exact ⟨fun i => (hf i).1, fun i t ht => by
    simpa only [map_sub, Function.comp_apply] using (hf i).2 t ht⟩

/-- The spanning weights detect an affine vector-valued line when its
almost-everywhere derivative is constant. -/
theorem affine_of_lipschitz_ae_constant_derivative
    {W I : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    (α : I → W →L[ℝ] ℝ) (hsep : ∀ w : W, (∀ i, α i w = 0) → w = 0)
    {h : ℝ → W} {C : ℝ≥0} {T : ℝ} (hT : 0 ≤ T)
    (hh : LipschitzOnWith C h (Icc 0 T)) (u : W)
    (hderiv : ∀ᵐ t ∂volume.restrict (Icc 0 T), HasDerivAt h u t) :
    ∀ t ∈ Icc 0 T, h t = h 0 + t • u := by
  have hFTC := profile_weight_fundamental_identities α hT hh hderiv
  intro t ht
  have hz : h t - h 0 - t • u = 0 := by
    apply hsep
    intro i
    rw [map_sub, (hFTC.2 i t ht), map_smul]
    simp [intervalIntegral.integral_const, smul_eq_mul]
  exact (sub_eq_iff_eq_add.mp (sub_eq_zero.mp hz)).trans (add_comm _ _)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_AffineProfileLines
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Pairwise almost-everywhere derivative agreement makes profile lines affine -/

noncomputable section

namespace PolycyclicRecognition

open MeasureTheory Set Filter
open scoped NNReal

theorem exists_affine_mem_of_lipschitz_pairwise_derivative
    {W I : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    (α : I → W →L[ℝ] ℝ) (hsep : ∀ w : W, (∀ i, α i w = 0) → w = 0)
    {h q : ℝ → W} {C : ℝ≥0} {T : ℝ} (hT : 0 < T)
    (hlip : LipschitzOnWith C h (Icc 0 T))
    (hderiv : ∀ᵐ t ∂volume.restrict (Icc 0 T), HasDerivAt h (q t) t)
    (hpair : ∀ᵐ s ∂volume.restrict (Icc 0 T),
      ∀ᵐ t ∂volume.restrict (Icc 0 T), q s = q t)
    {E : Set W} (hq : ∀ᵐ t ∂volume.restrict (Icc 0 T), q t ∈ E) :
    ∃ u ∈ E, ∀ t ∈ Icc 0 T, h t = h 0 + t • u := by
  let μ : Measure ℝ := volume.restrict (Icc 0 T)
  have hμ : μ ≠ 0 := by
    intro hz
    have hm := congrArg (fun ν : Measure ℝ => ν univ) hz
    have he : ENNReal.ofReal T = 0 := by simpa [μ] using hm
    exact (not_le_of_gt hT) (ENNReal.ofReal_eq_zero.mp he)
  let : NeZero μ := ⟨hμ⟩
  obtain ⟨s, hs, hsE⟩ := (hpair.and hq).exists
  refine ⟨q s, hsE, affine_of_lipschitz_ae_constant_derivative α hsep hT.le hlip (q s) ?_⟩
  filter_upwards [hderiv, hs] with t ht hst
  rwa [← hst] at ht

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_FiniteLabelTransport
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_countable _root_.OAI.PolycyclicRecognition.finitelyGeneratedSubgroupIndex_countable _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Measurable finite labels along converging measure-preserving maps

This is the local transport step in the profile affinity argument. A common
finite-measure carrier lets continuity of measurable-set preimages control
every label fiber. Relations between two transported labels then pass to the
limit directly, without selecting pointwise values on exceptional sets.
-/

noncomputable section

namespace PolycyclicRecognition

open MeasureTheory Filter Set
open scoped Topology ENNReal symmDiff

theorem finiteLabel_disagreement_tendsto
    {X Y I ι : Type*}
    [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] [R1Space X]
    [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y] [R1Space Y]
    [Fintype I] [MeasurableSpace I] [MeasurableSingletonClass I]
    {μ : Measure X} {ν : Measure Y} [μ.InnerRegularCompactLTTop] [IsLocallyFiniteMeasure ν]
    (label : Y → I) (hlabel : Measurable label)
    {l : Filter ι} (φ : ι → C(X, Y)) (φ₀ : C(X, Y))
    (hφ : Tendsto φ l (𝓝 φ₀))
    (hpres : ∀ᶠ n in l, MeasurePreserving (φ n) μ ν)
    (hpres₀ : MeasurePreserving φ₀ μ ν)
    (K : Set X) (Q : Set Y) (hQ : MeasurableSet Q) (hQfin : ν Q ≠ ∞)
    (himage : ∀ᶠ n in l, ∀ x ∈ K, φ n x ∈ Q) :
    Tendsto (fun n => μ {x | x ∈ K ∧ label (φ n x) ≠ label (φ₀ x)}) l (𝓝 0) := by
  classical
  let T : I → Set Y := fun i => Q ∩ label ⁻¹' {i}
  have hT (i : I) : MeasurableSet (T i) := hQ.inter (hlabel (measurableSet_singleton i))
  have hTfin (i : I) : ν (T i) ≠ ∞ :=
    ne_top_of_le_ne_top hQfin (measure_mono inter_subset_left)
  have hlim (i : I) : Tendsto (fun n => μ ((φ n ⁻¹' T i) ∆ (φ₀ ⁻¹' T i))) l (𝓝 0) :=
    tendsto_measure_symmDiff_preimage_nhds_zero hφ hpres hpres₀ (hT i).nullMeasurableSet (hTfin i)
  have hsum : Tendsto (fun n => ∑ i : I, μ ((φ n ⁻¹' T i) ∆ (φ₀ ⁻¹' T i))) l (𝓝 0) := by
    simpa only [Finset.sum_const_zero] using tendsto_finsetSum Finset.univ (fun i _ => hlim i)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum
    (Eventually.of_forall (fun _ => bot_le))
  filter_upwards [himage] with n hn
  apply (measure_mono (show {x | x ∈ K ∧ label (φ n x) ≠ label (φ₀ x)} ⊆
      ⋃ i ∈ (Finset.univ : Finset I), (φ n ⁻¹' T i) ∆ (φ₀ ⁻¹' T i) from ?_)).trans
    (measure_biUnion_finset_le _ _)
  rintro x ⟨hx, hneq⟩
  apply Set.mem_iUnion₂.mpr
  refine ⟨label (φ n x), Finset.mem_univ _, ?_⟩
  apply Set.mem_symmDiff.mpr
  left
  refine ⟨⟨hn x hx, rfl⟩, ?_⟩
  intro hh
  exact hneq hh.2.symm

/-- Relations between finite transported labels survive the limit because
the exceptional disagreement sets have vanishing measure. -/
theorem relation_of_disagreement_tendsto
    {X I J ι : Type*} [MeasurableSpace X]
    {μ : Measure X} {l : Filter ι} [l.NeBot]
    (f : ι → X → I) (g : ι → X → J) (f₀ : X → I) (g₀ : X → J)
    (R : I → J → Prop)
    (hR : ∀ᶠ n in l, ∀ᵐ x ∂μ, R (f n x) (g n x))
    (hf : Tendsto (fun n => μ {x | f n x ≠ f₀ x}) l (𝓝 0))
    (hg : Tendsto (fun n => μ {x | g n x ≠ g₀ x}) l (𝓝 0)) :
    ∀ᵐ x ∂μ, R (f₀ x) (g₀ x) := by
  have hbound : ∀ᶠ n in l, μ {x | ¬ R (f₀ x) (g₀ x)} ≤
      μ {x | f n x ≠ f₀ x} + μ {x | g n x ≠ g₀ x} := by
    filter_upwards [hR] with n hn
    have hnull : μ {x | ¬ R (f n x) (g n x)} = 0 := ae_iff.mp hn
    have hs : {x | ¬ R (f₀ x) (g₀ x)} ⊆
        ({x | f n x ≠ f₀ x} ∪ {x | g n x ≠ g₀ x}) ∪ {x | ¬ R (f n x) (g n x)} := by
      intro x hx
      by_cases hfx : f n x = f₀ x
      · by_cases hgx : g n x = g₀ x
        · exact Or.inr (by change ¬ R (f n x) (g n x); rwa [hfx, hgx])
        · exact Or.inl (Or.inr hgx)
      · exact Or.inl (Or.inl hfx)
    have hh := (measure_mono (μ := μ) hs).trans (measure_union_le _ _)
    rw [hnull, add_zero] at hh
    exact hh.trans (measure_union_le _ _)
  have hzero : μ {x | ¬ R (f₀ x) (g₀ x)} ≤ 0 :=
    ge_of_tendsto (by simpa only [add_zero] using hf.add hg) hbound
  exact ae_iff.mpr (le_antisymm hzero bot_le)

/-- Local chamber relations pass to the limiting flow maps. The common
carrier is needed only to localize the measurable finite label field. -/
theorem finiteLabel_relation_transport
    {X Y I ι : Type*}
    [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] [R1Space X]
    [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y] [R1Space Y]
    [Fintype I] [MeasurableSpace I] [MeasurableSingletonClass I]
    {μ : Measure X} {ν : Measure Y} [μ.InnerRegularCompactLTTop] [IsLocallyFiniteMeasure ν]
    (label : Y → I) (hlabel : Measurable label)
    {l : Filter ι} [l.NeBot] (φ ψ : ι → C(X, Y)) (φ₀ ψ₀ : C(X, Y))
    (hφ : Tendsto φ l (𝓝 φ₀)) (hψ : Tendsto ψ l (𝓝 ψ₀))
    (hφpres : ∀ᶠ n in l, MeasurePreserving (φ n) μ ν)
    (hψpres : ∀ᶠ n in l, MeasurePreserving (ψ n) μ ν)
    (hφpres₀ : MeasurePreserving φ₀ μ ν) (hψpres₀ : MeasurePreserving ψ₀ μ ν)
    (K : Set X) (Q : Set Y) (hQ : MeasurableSet Q) (hQfin : ν Q ≠ ∞)
    (hφimage : ∀ᶠ n in l, ∀ x ∈ K, φ n x ∈ Q)
    (hψimage : ∀ᶠ n in l, ∀ x ∈ K, ψ n x ∈ Q)
    (R : I → I → Prop)
    (hR : ∀ᶠ n in l, ∀ᵐ x ∂μ.restrict K, R (label (φ n x)) (label (ψ n x))) :
    ∀ᵐ x ∂μ.restrict K, R (label (φ₀ x)) (label (ψ₀ x)) := by
  have hdis (f g : C(X, Y)) :
      μ.restrict K {x | label (f x) ≠ label (g x)} =
        μ {x | x ∈ K ∧ label (f x) ≠ label (g x)} := by
    have hmeas : MeasurableSet {x | label (f x) ≠ label (g x)} :=
      (measurableSet_eq_fun (hlabel.comp f.measurable) (hlabel.comp g.measurable)).compl
    rw [Measure.restrict_apply hmeas]
    congr 1
    ext x
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, and_comm]
  apply relation_of_disagreement_tendsto (μ := μ.restrict K)
    (fun n x => label (φ n x)) (fun n x => label (ψ n x))
    (fun x => label (φ₀ x)) (fun x => label (ψ₀ x)) R hR
  · simpa only [hdis] using finiteLabel_disagreement_tendsto label hlabel φ φ₀
      hφ hφpres hφpres₀ K Q hQ hQfin hφimage
  · simpa only [hdis] using finiteLabel_disagreement_tendsto label hlabel ψ ψ₀
      hψ hψpres hψpres₀ K Q hQ hQfin hψimage

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_JointDirectionLabels
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instNonemptyBases _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_nonempty _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Joint transport of direction labels in both flow times

Keeping both times as coordinates turns the horizontal flows into
measure-preserving skew products. This supplies local convergence in measure
on triples directly, including compact sets that are not product sets.
-/

noncomputable section

namespace PolycyclicRecognition

open MeasureTheory Filter Set
open scoped Topology

variable {G V : Type*} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem continuous_timedRightTranslation (Exp : V → G) (hExp : Continuous Exp)
    (pick : (ℝ × ℝ) → ℝ) (hpick : Continuous pick) :
    Continuous (timedRightTranslation Exp hExp pick hpick) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  change Continuous (fun p : V × ((ℝ × ℝ) × G) =>
    (p.2.1, p.2.2 * Exp (pick p.2.1 • p.1)))
  fun_prop

variable [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
  [TopologicalSpace.PseudoMetrizableSpace G] [MeasurableSpace G] [BorelSpace G]

omit [T2Space G] [TopologicalSpace.PseudoMetrizableSpace G] in
theorem measurePreserving_timedRightTranslation
    (μ : Measure G) [μ.IsHaarMeasure] [μ.IsMulRightInvariant]
    (Exp : V → G) (hExp : Continuous Exp)
    (pick : (ℝ × ℝ) → ℝ) (hpick : Continuous pick) (v : V) :
    MeasurePreserving (timedRightTranslation Exp hExp pick hpick v)
      (pairTimeMeasure.prod μ) (pairTimeMeasure.prod μ) := by
  exact (MeasurePreserving.id pairTimeMeasure).skew_product
    (by change Measurable (fun z : (ℝ × ℝ) × G => z.2 * Exp (pick z.1 • v)); fun_prop)
    (Eventually.of_forall (fun t => (measurePreserving_mul_right μ (Exp (pick t • v))).map_eq))

/-- A finite relation true locally on triples for nearby directions remains
true at the limiting direction. Compact carriers are built from the actual
convergent sequence and the two continuous skew products. -/
theorem finiteLabel_jointDirections_relation
    {L : Type*} [Fintype L] [MeasurableSpace L] [MeasurableSingletonClass L]
    (μ : Measure G) [μ.IsHaarMeasure] [μ.IsMulRightInvariant]
    (Exp : V → G) (hExp : Continuous Exp) (label : G → L) (hlabel : Measurable label)
    (v : ℕ → V) {v₀ : V} (hv : Tendsto v atTop (𝓝 v₀))
    (K : Set ((ℝ × ℝ) × G)) (hK : IsCompact K) (R : L → L → Prop)
    (hR : ∀ᶠ n in atTop, ∀ᵐ z ∂(pairTimeMeasure.prod μ).restrict K,
      R (label (z.2 * Exp (z.1.1 • v n))) (label (z.2 * Exp (z.1.2 • v n)))) :
    ∀ᵐ z ∂(pairTimeMeasure.prod μ).restrict K,
      R (label (z.2 * Exp (z.1.1 • v₀))) (label (z.2 * Exp (z.1.2 • v₀))) := by
  let F : ((ℝ × ℝ) × G) × V → (ℝ × ℝ) × G :=
    fun p => (p.1.1, p.1.2 * Exp (p.1.1.1 • p.2))
  let H : ((ℝ × ℝ) × G) × V → (ℝ × ℝ) × G :=
    fun p => (p.1.1, p.1.2 * Exp (p.1.1.2 • p.2))
  have hF : Continuous F := by fun_prop
  have hH : Continuous H := by fun_prop
  let Q := F '' (K ×ˢ insert v₀ (range v)) ∪ H '' (K ×ˢ insert v₀ (range v))
  have hQ : IsCompact Q :=
    ((hK.prod hv.isCompact_insert_range).image hF).union
      ((hK.prod hv.isCompact_insert_range).image hH)
  apply finiteLabel_relation_transport (μ := pairTimeMeasure.prod μ)
    (fun z : (ℝ × ℝ) × G => label z.2) (hlabel.comp measurable_snd)
    (fun n => timedRightTranslation Exp hExp Prod.fst continuous_fst (v n))
    (fun n => timedRightTranslation Exp hExp Prod.snd continuous_snd (v n))
    (timedRightTranslation Exp hExp Prod.fst continuous_fst v₀)
    (timedRightTranslation Exp hExp Prod.snd continuous_snd v₀)
    ((continuous_timedRightTranslation Exp hExp Prod.fst continuous_fst).continuousAt.tendsto.comp hv)
    ((continuous_timedRightTranslation Exp hExp Prod.snd continuous_snd).continuousAt.tendsto.comp hv)
    (Eventually.of_forall (fun n =>
      measurePreserving_timedRightTranslation μ Exp hExp Prod.fst continuous_fst (v n)))
    (Eventually.of_forall (fun n =>
      measurePreserving_timedRightTranslation μ Exp hExp Prod.snd continuous_snd (v n)))
    (measurePreserving_timedRightTranslation μ Exp hExp Prod.fst continuous_fst v₀)
    (measurePreserving_timedRightTranslation μ Exp hExp Prod.snd continuous_snd v₀)
    K Q hQ.measurableSet hQ.measure_ne_top _ _ R hR
  · exact Eventually.of_forall (fun n z hz => Or.inl ⟨(z, v n), ⟨hz, Or.inr ⟨n, rfl⟩⟩, rfl⟩)
  · exact Eventually.of_forall (fun n z hz => Or.inr ⟨(z, v n), ⟨hz, Or.inr ⟨n, rfl⟩⟩, rfl⟩)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CompactFlowSegments
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Compact families of flow segments remain in an open domain -/

noncomputable section

namespace PolycyclicRecognition

open Set Filter
open scoped Topology

variable {G V : Type*} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem isOpen_flowSegmentDomain (U : Set G) (hU : IsOpen U)
    (Exp : V → G) (hExp : Continuous Exp) (v : V) :
    IsOpen (flowSegmentDomain U Exp v) := by
  let F : ((ℝ × ℝ) × G) → C(ℝ, G) := fun z =>
    ⟨flowSegmentPoint Exp v z, by
      change Continuous (fun r : ℝ => z.2 * Exp (((1 - r) * z.1.1 + r * z.1.2) • v))
      fun_prop⟩
  have hc : Continuous F := by
    apply ContinuousMap.continuous_of_continuous_uncurry
    change Continuous (fun p : ((ℝ × ℝ) × G) × ℝ => flowSegmentPoint Exp v p.1 p.2)
    dsimp [flowSegmentPoint]
    fun_prop
  exact (ContinuousMap.continuous_compactOpen.mp hc (Icc (0 : ℝ) 1) isCompact_Icc U hU)

theorem eventually_compact_flowSegments
    (U : Set G) (hU : IsOpen U) (Exp : V → G) (hExp : Continuous Exp)
    (v : ℕ → V) {v₀ : V} (hv : Tendsto v atTop (𝓝 v₀))
    (K : Set ((ℝ × ℝ) × G)) (hK : IsCompact K)
    (hKU : K ⊆ flowSegmentDomain U Exp v₀) :
    ∀ᶠ n in atTop, K ⊆ flowSegmentDomain U Exp (v n) := by
  let F : V → C(((ℝ × ℝ) × G) × ℝ, G) := fun w =>
    ⟨fun p => flowSegmentPoint Exp w p.1 p.2, by dsimp [flowSegmentPoint]; fun_prop⟩
  have hc : Continuous F := by
    apply ContinuousMap.continuous_of_continuous_uncurry
    change Continuous (fun p : V × (((ℝ × ℝ) × G) × ℝ) =>
      flowSegmentPoint Exp p.1 p.2.1 p.2.2)
    dsimp [flowSegmentPoint]
    fun_prop
  have hmaps : MapsTo (F v₀) (K ×ˢ Icc (0 : ℝ) 1) U := by
    rintro ⟨z, r⟩ ⟨hz, hr⟩
    exact hKU hz r hr
  have he := ContinuousMap.tendsto_nhds_compactOpen.mp
    (hc.continuousAt.tendsto.comp hv) (K ×ˢ Icc (0 : ℝ) 1)
    (hK.prod isCompact_Icc) U hU hmaps
  filter_upwards [he] with n hn z hz r hr
  exact hn (x := (z, r)) ⟨hz, hr⟩

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_FlowLineLabels
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Fubini turns joint flow-label agreement into agreement on lines -/

noncomputable section

namespace PolycyclicRecognition

open MeasureTheory MeasureTheory.Measure Set Filter

theorem ae_flowLine_pair_relation
    {G V L : Type*} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    [MeasurableSpace G]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (μ : Measure G) [SFinite μ] (Exp : V → G) (v : V) (U : Set G)
    (label : G → L) (R : L → L → Prop)
    (hR : ∀ᵐ z ∂(pairTimeMeasure.prod μ).restrict (flowSegmentDomain U Exp v),
      R (label (z.2 * Exp (z.1.1 • v))) (label (z.2 * Exp (z.1.2 • v))))
    (T : ℝ) :
    ∀ᵐ g ∂μ, (∀ a ∈ Icc 0 T, g * Exp (a • v) ∈ U) →
      ∀ᵐ s ∂volume.restrict (Icc 0 T), ∀ᵐ t ∂volume.restrict (Icc 0 T),
        R (label (g * Exp (s • v))) (label (g * Exp (t • v))) := by
  have hglobal := ae_imp_of_ae_restrict hR
  have hswap := (Measure.measurePreserving_swap (μ := μ) (ν := pairTimeMeasure)).quasiMeasurePreserving.ae
    hglobal
  filter_upwards [ae_ae_of_ae_prod hswap] with g hg
  intro hstay
  change ∀ᵐ p ∂(volume.prod volume),
    (p, g) ∈ flowSegmentDomain U Exp v →
      R (label (g * Exp (p.1 • v))) (label (g * Exp (p.2 • v))) at hg
  filter_upwards [ae_restrict_of_ae (ae_ae_of_ae_prod hg), ae_restrict_mem measurableSet_Icc]
    with s hs hsmem
  filter_upwards [ae_restrict_of_ae hs, ae_restrict_mem measurableSet_Icc] with t ht htmem
  apply ht
  intro r hr
  apply hstay
  have hm := (convex_Icc (0 : ℝ) T) hsmem htmem
    (sub_nonneg.mpr hr.2) hr.1 (show (1 - r) + r = 1 by ring)
  simpa only [smul_eq_mul] using hm

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_ContinuousFlowAffinity
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Continuity upgrades almost-everywhere affine flow restrictions -/

noncomputable section

namespace PolycyclicRecognition

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped Topology

variable {G V W : Type*} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

theorem isOpen_flowLineBase (U : Set G) (hU : IsOpen U)
    (Exp : V → G) (hExp : Continuous Exp) (v : V) (T : ℝ) :
    IsOpen (flowLineBase U Exp v T) := by
  let F : G → C(ℝ, G) := fun g =>
    ⟨fun t => g * Exp (t • v), by fun_prop⟩
  have hc : Continuous F := by
    apply ContinuousMap.continuous_of_continuous_uncurry
    change Continuous (fun p : G × ℝ => p.1 * Exp (p.2 • v))
    fun_prop
  exact ContinuousMap.continuous_compactOpen.mp hc (Icc 0 T) isCompact_Icc U hU

omit [NormedSpace ℝ W] in
theorem continuousOn_flowLine_evaluation
    {U : Set G} {Exp : V → G} (_hExp : Continuous Exp) {v : V} {T t : ℝ}
    {f : G → W} (hf : ContinuousOn f U) (ht : t ∈ Icc 0 T) :
    ContinuousOn (fun g => f (g * Exp (t • v))) (flowLineBase U Exp v T) :=
  hf.comp (by fun_prop) (fun _ hg => hg t ht)

omit [Group G] [IsTopologicalGroup G] [NormedSpace ℝ W] in
theorem mapsTo_closed_of_ae
    [MeasurableSpace G] (μ : Measure G) [μ.IsOpenPosMeasure]
    {U : Set G} (hU : IsOpen U) {f : G → W} (hf : ContinuousOn f U)
    {E : Set W} (hE : IsClosed E)
    (hae : ∀ᵐ g ∂μ, g ∈ U → f g ∈ E) : MapsTo f U E := by
  have ho : IsOpen (U ∩ f ⁻¹' Eᶜ) := hf.isOpen_inter_preimage hU hE.isOpen_compl
  have hz : μ (U ∩ f ⁻¹' Eᶜ) = 0 := by
    apply measure_mono_null (fun g hg => ?_) hae
    exact fun h => hg.2 (h hg.1)
  have he := ho.eq_empty_of_measure_zero hz
  intro g hg
  by_contra hn
  have : g ∈ U ∩ f ⁻¹' Eᶜ := ⟨hg, hn⟩
  rw [he] at this
  exact this

theorem continuousOn_flowLineSlope
    {U : Set G} {Exp : V → G} (hExp : Continuous Exp) (hExp0 : Exp 0 = 1)
    {v : V} {T : ℝ} (hT : 0 ≤ T) {f : G → W} (hf : ContinuousOn f U) :
    ContinuousOn (flowLineSlope f Exp v T) (flowLineBase U Exp v T) := by
  have hbase : flowLineBase U Exp v T ⊆ U := by
    intro g hg
    simpa [hExp0] using hg 0 ⟨le_rfl, hT⟩
  exact ((continuousOn_flowLine_evaluation hExp hf ⟨hT, le_rfl⟩).sub
    (hf.mono hbase)).const_smul T⁻¹

theorem flowLine_affinity_of_ae
    [MeasurableSpace G] [OpensMeasurableSpace G] (μ : Measure G) [μ.IsOpenPosMeasure]
    {U : Set G} (hU : IsOpen U) {Exp : V → G} (hExp : Continuous Exp)
    (hExp0 : Exp 0 = 1) {v : V} {T : ℝ} (hT : 0 < T)
    {f : G → W} (hf : ContinuousOn f U)
    (hae : ∀ᵐ g ∂μ, g ∈ flowLineBase U Exp v T →
      ∃ u : W, ∀ t ∈ Icc 0 T, f (g * Exp (t • v)) = f g + t • u) :
    ∀ g ∈ flowLineBase U Exp v T, ∀ t ∈ Icc 0 T,
      f (g * Exp (t • v)) = f g + t • flowLineSlope f Exp v T g := by
  have hbase : flowLineBase U Exp v T ⊆ U := by
    intro g hg
    simpa [hExp0] using hg 0 ⟨le_rfl, hT.le⟩
  intro g hg t ht
  apply eqOn_open_of_ae_eq (μ := μ) (U := flowLineBase U Exp v T) ?_
    (isOpen_flowLineBase U hU Exp hExp v T)
    (continuousOn_flowLine_evaluation hExp hf ht)
    ((hf.mono hbase).add ((continuousOn_flowLineSlope hExp hExp0 hT.le hf).const_smul t)) hg
  filter_upwards [ae_restrict_of_ae hae, ae_restrict_mem
    (isOpen_flowLineBase U hU Exp hExp v T).measurableSet] with x hx hxB
  obtain ⟨u, hu⟩ := hx hxB
  have hs : flowLineSlope f Exp v T x = u := by
    simp [flowLineSlope, hu T ⟨hT.le, le_rfl⟩, smul_smul, hT.ne']
  change f (x * Exp (t • v)) = f x + t • flowLineSlope f Exp v T x
  rw [hs]
  exact hu t ht

theorem flowLineSlope_mem_of_ae
    [MeasurableSpace G] (μ : Measure G) [μ.IsOpenPosMeasure]
    {U : Set G} (hU : IsOpen U) {Exp : V → G} (hExp : Continuous Exp)
    (hExp0 : Exp 0 = 1) {v : V} {T : ℝ} (hT : 0 < T)
    {f : G → W} (hf : ContinuousOn f U) {E : Set W} (hE : IsClosed E)
    (hae : ∀ᵐ g ∂μ, g ∈ flowLineBase U Exp v T →
      ∃ u ∈ E, ∀ t ∈ Icc 0 T, f (g * Exp (t • v)) = f g + t • u) :
    MapsTo (flowLineSlope f Exp v T) (flowLineBase U Exp v T) E := by
  apply mapsTo_closed_of_ae μ (isOpen_flowLineBase U hU Exp hExp v T)
    (continuousOn_flowLineSlope hExp hExp0 hT.le hf) hE
  filter_upwards [hae] with g hg hbase
  obtain ⟨u, huE, hu⟩ := hg hbase
  simpa [flowLineSlope, hu T ⟨hT.le, le_rfl⟩, smul_smul, hT.ne'] using huE

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_AdmissibleGeneratorWords
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Generator words whose entire path stays in an open set -/

noncomputable section

namespace PolycyclicRecognition

open Set Filter
open scoped Topology

variable {G V I : Type*} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem isOpen_generatorWordBase (U : Set G) (hU : IsOpen U)
    (Exp : V → G) (hExp : Continuous Exp) (X : I → V) (w : List (I × ℝ)) :
    IsOpen (generatorWordBase U Exp X w) := by
  induction w with
  | nil => exact hU
  | cons p w ih =>
    exact (isOpen_flowLineBase U hU Exp hExp (p.2 • X p.1) 1).inter
      (ih.preimage (by fun_prop))

omit [TopologicalSpace G] [IsTopologicalGroup G] in
theorem generatorWordBase_subset (U : Set G) (Exp : V → G) (hExp0 : Exp 0 = 1)
    (X : I → V) (w : List (I × ℝ)) : generatorWordBase U Exp X w ⊆ U := by
  cases w with
  | nil => exact Subset.rfl
  | cons p w =>
    intro g hg
    simpa [hExp0] using hg.1 0 (show (0 : ℝ) ∈ Icc 0 1 by simp)

theorem eventually_short_flowLineBase
    {U : Set G} (hU : IsOpen U) {Exp : V → G} (hExp : Continuous Exp)
    (hExp0 : Exp 0 = 1) (v : V) {g : G} (hg : g ∈ U) :
    ∀ᶠ t in 𝓝 (0 : ℝ), g ∈ flowLineBase U Exp (t • v) 1 := by
  let F : ℝ → C(ℝ, G) := fun t =>
    ⟨fun r => g * Exp (r • (t • v)), by fun_prop⟩
  have hc : Continuous F := by
    apply ContinuousMap.continuous_of_continuous_uncurry
    change Continuous (fun p : ℝ × ℝ => g * Exp (p.2 • (p.1 • v)))
    fun_prop
  have ho := ContinuousMap.continuous_compactOpen.mp hc
    (Icc (0 : ℝ) 1) isCompact_Icc U hU
  apply ho.mem_nhds
  intro r _hr
  simpa [F, hExp0] using hg

theorem eventually_prefix_generatorWordBase
    (U : Set G) (hU : IsOpen U) (Exp : V → G) (hExp : Continuous Exp)
    (hExp0 : Exp 0 = 1) (X : I → V) (w : List (I × ℝ))
    {g : G} (hg : g ∈ generatorWordBase U Exp X w) (i : I) :
    ∀ᶠ t in 𝓝 (0 : ℝ), g ∈ generatorWordBase U Exp X ((i, t) :: w) := by
  have ht : ∀ᶠ t in 𝓝 (0 : ℝ), g * Exp (t • X i) ∈ generatorWordBase U Exp X w := by
    have hc : Continuous (fun t : ℝ => g * Exp (t • X i)) := by fun_prop
    have hc0 : Tendsto (fun t : ℝ => g * Exp (t • X i)) (𝓝 0) (𝓝 g) := by
      simpa [hExp0] using hc.tendsto 0
    exact hc0.eventually ((isOpen_generatorWordBase U hU Exp hExp X w).mem_nhds hg)
  exact (eventually_short_flowLineBase hU hExp hExp0 (X i)
    (generatorWordBase_subset U Exp hExp0 X w hg)).and ht

omit [TopologicalSpace G] [IsTopologicalGroup G] in
theorem eq_on_admissible_generatorWord
    {W : Type*} (f : G → W) (U : Set G) (Exp : V → G) (X : I → V)
    (hflow : ∀ (i : I) (g : G) (t : ℝ), g ∈ flowLineBase U Exp (t • X i) 1 →
      f (g * Exp (t • X i)) = f g)
    (w : List (I × ℝ)) {g : G} (hg : g ∈ generatorWordBase U Exp X w) :
    f (g * generatorGroupWord X Exp w) = f g := by
  induction w generalizing g with
  | nil => simp [generatorGroupWord]
  | cons p w ih =>
    rw [generatorGroupWord_cons, ← mul_assoc, ih hg.2, hflow p.1 g p.2 hg.1]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_AdmissibleWordOperations
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Concatenating and reversing admissible generator paths -/

noncomputable section

namespace PolycyclicRecognition

open Set

variable {G V I : Type*} [Group G] [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem mem_generatorWordBase_append
    (U : Set G) (Exp : V → G) (hExp0 : Exp 0 = 1) (X : I → V)
    (w z : List (I × ℝ)) (g : G) :
    g ∈ generatorWordBase U Exp X (w ++ z) ↔
      g ∈ generatorWordBase U Exp X w ∧
        g * generatorGroupWord X Exp w ∈ generatorWordBase U Exp X z := by
  induction w generalizing g with
  | nil =>
    simp only [List.nil_append, generatorWordBase, generatorGroupWord_nil, mul_one]
    exact ⟨fun h => ⟨generatorWordBase_subset U Exp hExp0 X z h, h⟩, And.right⟩
  | cons p w ih =>
    rcases p with ⟨i, t⟩
    simp only [List.cons_append, generatorWordBase, mem_inter_iff, mem_preimage,
      ih, generatorGroupWord_cons, mul_assoc]
    tauto

theorem generatorGroupWord_inverse_of_exp_neg
    (Exp : V → G) (hneg : ∀ v, Exp (-v) = (Exp v)⁻¹)
    (X : I → V) (w : List (I × ℝ)) :
    generatorGroupWord X Exp (inverseGeneratorWord w) = (generatorGroupWord X Exp w)⁻¹ := by
  induction w with
  | nil => simp [inverseGeneratorWord]
  | cons p w ih =>
    rcases p with ⟨i, t⟩
    have he : inverseGeneratorWord ((i, t) :: w) = inverseGeneratorWord w ++ [(i, -t)] := by
      simp only [inverseGeneratorWord, List.reverse_cons, List.map_append, List.map_cons,
        List.map_nil]
    rw [he]
    have ha : generatorGroupWord X Exp (inverseGeneratorWord w ++ [(i, -t)]) =
        generatorGroupWord X Exp (inverseGeneratorWord w) * Exp ((-t) • X i) := by
      simp [generatorGroupWord, List.map_append, List.prod_append]
    rw [ha, ih, generatorGroupWord_cons, mul_inv_rev]
    simp only [neg_smul, hneg]

theorem reverse_flowLineBase
    (U : Set G) (Exp : V → G)
    (hadd : ∀ v (s t : ℝ), Exp ((s + t) • v) = Exp (s • v) * Exp (t • v))
    (v : V) {g : G} (hg : g ∈ flowLineBase U Exp v 1) :
    g * Exp v ∈ flowLineBase U Exp (-v) 1 := by
  intro r hr
  have hmem := hg (1 - r) (show 1 - r ∈ Icc (0 : ℝ) 1 by constructor <;> linarith [hr.1, hr.2])
  have he : (g * Exp v) * Exp (r • -v) = g * Exp ((1 - r) • v) := by
    rw [mul_assoc]
    congr 1
    have hh := hadd v 1 (-r)
    simpa only [one_smul, sub_eq_add_neg, smul_neg, neg_smul] using hh.symm
  rwa [he]

theorem mem_generatorWordBase_inverse
    (U : Set G) (Exp : V → G) (hExp0 : Exp 0 = 1)
    (hneg : ∀ v, Exp (-v) = (Exp v)⁻¹)
    (hadd : ∀ v (s t : ℝ), Exp ((s + t) • v) = Exp (s • v) * Exp (t • v))
    (X : I → V) (w : List (I × ℝ)) {g : G}
    (hg : g ∈ generatorWordBase U Exp X w) :
    g * generatorGroupWord X Exp w ∈
      generatorWordBase U Exp X (inverseGeneratorWord w) := by
  induction w generalizing g with
  | nil => simpa [inverseGeneratorWord, generatorWordBase] using hg
  | cons p w ih =>
    rcases p with ⟨i, t⟩
    have hcons : inverseGeneratorWord ((i, t) :: w) = inverseGeneratorWord w ++ [(i, -t)] := by
      simp only [inverseGeneratorWord, List.reverse_cons, List.map_append, List.map_cons,
        List.map_nil]
    rw [hcons]
    rw [mem_generatorWordBase_append U Exp hExp0]
    constructor
    · simpa [generatorGroupWord_cons, mul_assoc] using ih hg.2
    · have he : (g * generatorGroupWord X Exp ((i, t) :: w)) *
          generatorGroupWord X Exp (inverseGeneratorWord w) = g * Exp (t • X i) := by
        rw [generatorGroupWord_cons, generatorGroupWord_inverse_of_exp_neg Exp hneg X w]
        group
      rw [he]
      constructor
      · simpa only [neg_smul] using reverse_flowLineBase U Exp hadd (t • X i) hg.1
      · change (g * Exp (t • X i)) * Exp ((-t) • X i) ∈ U
        have hgU := generatorWordBase_subset U Exp hExp0 X ((i, t) :: w) hg
        simpa [neg_smul, hneg] using hgU

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_NormalizedGeneration
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Generation persists in the compact normalized family

The word-normalization equations express a fixed vector-space basis as words
in the generators. They therefore imply Lie generation for every limiting law.
-/

noncomputable section

namespace PolycyclicRecognition

open Module

variable {V I J : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The recursively evaluated operation agrees with the Lie structure that
it defines. -/
theorem evalBilinearWord_eq_lieWord (B : V →L[ℝ] V →L[ℝ] V)
    (h : IsLieBracket B) (X : I → V) (w : FreeMagma I) :
    letI := lieRingOfBilinear B h
    letI := lieAlgebraOfBilinear B h
    evalBilinearWord B X w = evalBracketWord X w := by
  let := lieRingOfBilinear B h
  let := lieAlgebraOfBilinear B h
  induction w using FreeMagma.rec with
  | of i => rfl
  | mul a b ha hb => change B _ _ = B _ _; rw [ha, hb]

/-- Fixed basis-word identities prevent loss of generation in a limit. -/
theorem lieSpan_eq_top_of_word_basis (B : V →L[ℝ] V →L[ℝ] V)
    (h : IsLieBracket B) (X : I → V) (b : Basis J ℝ V) (w : J → FreeMagma I)
    (hw : ∀ j, evalBilinearWord B X (w j) = b j) :
    letI := lieRingOfBilinear B h
    letI := lieAlgebraOfBilinear B h
    LieSubalgebra.lieSpan ℝ V (Set.range X) = ⊤ := by
  let := lieRingOfBilinear B h
  let := lieAlgebraOfBilinear B h
  have hb (j : J) : b j ∈ LieSubalgebra.lieSpan ℝ V (Set.range X) := by
    rw [← hw j, evalBilinearWord_eq_lieWord B h]
    exact evalBracketWord_mem_lieSpan X (w j)
  have hspan : (⊤ : Submodule ℝ V) ≤
      (LieSubalgebra.lieSpan ℝ V (Set.range X)).toSubmodule := by
    rw [← b.span_eq]
    exact Submodule.span_le.mpr (by rintro _ ⟨j, rfl⟩; exact hb j)
  apply top_unique
  intro v _
  exact hspan (Submodule.mem_top)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_SupportNorm
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finite_templateSymmetryGroup _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteRootOffsetConeIndex _root_.OAI.PolycyclicRecognition.instFiniteSubtypeLinearEquivRealIdMemSubgroupLinearSupportSymmetryGroup _root_.OAI.PolycyclicRecognition.instNonemptyRootOffsetConeIndex _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The norm obtained from weighted nilpotent boxes

For a bracket-word basis, each generator occurs with a positive integral
multiplicity. Unimodularity says that the corresponding weighted sum of
characters is zero. The support exponent of a segment is the maximum, over
these bases, of the weighted positive parts of the characters. This finite
data yields the support norm identities.
-/

namespace PolycyclicRecognition

open scoped BigOperators

variable {W I B : Type*} [AddCommGroup W] [Module ℝ W]
  [Fintype I] [Fintype B] [Nonempty B]

namespace SupportDatum

variable (D : SupportDatum W I B)

theorem segmentSupport_pos {w : W} (hw : w ≠ 0) : 0 < D.segmentSupport w := by
  exact lt_of_le_of_ne (D.segmentSupport_nonneg w)
    (Ne.symm fun h => hw ((D.segmentSupport_eq_zero_iff w).mp h))

end SupportDatum
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

variable {W I B : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
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

end PolycyclicRecognition.SupportDatum

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_PolynomialCoordinateGroup
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.PolynomialCoordinateGroup.instBorelSpace _root_.OAI.PolycyclicRecognition.PolynomialCoordinateGroup.instMeasurableSpace _root_.OAI.PolycyclicRecognition.PolynomialCoordinateGroup.instTopologicalSpace _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The group carried by a polynomial coordinate law

This type keeps the group multiplication distinct from vector addition. The
exponential-coordinate bijection is the identity on underlying points.
-/

noncomputable section

namespace PolycyclicRecognition

variable {V I : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

namespace PolynomialCoordinateGroup

variable (m : V → V → V) (h : PolynomialGroupLaws m)

theorem exp_add_smul (x : V) (s t : ℝ) :
    exp m h ((s + t) • x) = exp m h (s • x) * exp m h (t • x) :=
  (h.2.2.2.2 x s t).symm

end PolynomialCoordinateGroup

/-- The direct polynomial evaluation is exactly the generator group word. -/
theorem exp_polynomialWord (m : V → V → V) (h : PolynomialGroupLaws m)
    (X : I → V) (w : List (I × ℝ)) :
    PolynomialCoordinateGroup.exp m h (polynomialWord m X w) =
      generatorGroupWord X (PolynomialCoordinateGroup.exp m h) w := by
  induction w with
  | nil => rfl
  | cons p w ih =>
    rcases p with ⟨i, t⟩
    change PolynomialCoordinateGroup.exp m h
      (m (t • X i) (polynomialWord m X w)) = _
    rw [PolynomialCoordinateGroup.exp_mul, ih, generatorGroupWord_cons]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_PolynomialEndpointSchemes
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.PolynomialCoordinateGroup.instBorelSpace _root_.OAI.PolycyclicRecognition.PolynomialCoordinateGroup.instMeasurableSpace _root_.OAI.PolycyclicRecognition.PolynomialCoordinateGroup.instTopologicalSpace _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
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

variable {V P I : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup P] [NormedSpace ℝ P]

theorem exp_polynomialListProduct (m : V → V → V) (h : PolynomialGroupLaws m)
    (xs : List V) :
    PolynomialCoordinateGroup.exp m h (polynomialListProduct m xs) =
      (xs.map (PolynomialCoordinateGroup.exp m h)).prod := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    change PolynomialCoordinateGroup.exp m h (m x (polynomialListProduct m xs)) = _
    rw [PolynomialCoordinateGroup.exp_mul, ih]
    rfl

theorem contDiff_polynomialWord {c : ℕ} {k : ℕ∞}
    (a : DynkinCoefficients c 2) (B : P → V →L[ℝ] V →L[ℝ] V)
    (X : P → I → V) (hB : ContDiff ℝ k B)
    (hX : ∀ i, ContDiff ℝ k (fun p => X p i)) (w : List (I × ℝ)) :
    ContDiff ℝ k (fun p => polynomialWord (dynkinProduct a (B p)) (X p) w) := by
  induction w with
  | nil => exact contDiff_const
  | cons z w ih =>
    rcases z with ⟨i, t⟩
    exact contDiff_dynkinProduct a B _ _ hB ((hX i).const_smul t) ih

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

variable [Fintype I]

/-- Joint smoothness includes the law and generator data, rather than just
the inserted amplitudes at one fixed law. -/
theorem contDiff_polynomialEndpointScheme {c n : ℕ} {k : ℕ∞}
    (a : DynkinCoefficients c 2) (w : Fin n → List (I × ℝ)) (i : Fin n → I) :
    ContDiff ℝ k (fun z : ((V →L[ℝ] V →L[ℝ] V) × (I → V)) × (Fin n → ℝ) =>
      polynomialEndpointScheme a w i z.1 z.2) := by
  apply contDiff_polynomialListProduct_ofFn
  · exact contDiff_fst.fst
  · intro j
    apply contDiff_dynkinProduct
    · exact contDiff_fst.fst
    · apply contDiff_dynkinProduct
      · exact contDiff_fst.fst
      · exact contDiff_polynomialWord a _ _ contDiff_fst.fst
          (fun l => (contDiff_apply ℝ V l).comp contDiff_fst.snd) (w j)
      · exact ((contDiff_apply ℝ ℝ j).comp contDiff_snd).smul
          ((contDiff_apply ℝ V (i j)).comp contDiff_fst.snd)
    · exact contDiff_polynomialWord a _ _ contDiff_fst.fst
        (fun l => (contDiff_apply ℝ V l).comp contDiff_fst.snd) (inverseGeneratorWord (w j))

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_CoordinateSchemeBasis
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.PolynomialCoordinateGroup.instBorelSpace _root_.OAI.PolycyclicRecognition.PolynomialCoordinateGroup.instMeasurableSpace _root_.OAI.PolycyclicRecognition.PolynomialCoordinateGroup.instTopologicalSpace _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.dynkinRightTranslation_apply _root_.OAI.PolycyclicRecognition.dynkinRightTranslation_symm_apply _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Nondegenerate schemes in limiting coordinate groups

The preserved adjoint-conjugation identity turns the spanning adjoint orbits
into actual group-word conjugates. Their polynomial endpoint map is exactly
the ordered exponential product in the resulting basis.
-/

noncomputable section

namespace PolycyclicRecognition

open Module

variable {V I : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V]

omit [FiniteDimensional ℝ V] in
/-- The coordinate adjoint word is realized by the corresponding generator
word in the polynomial coordinate group. -/
theorem exp_bilinearAdjointWord (m : V → V → V) (hg : PolynomialGroupLaws m)
    (B : V →L[ℝ] V →L[ℝ] V) (hc : ExponentialConjugationLaw m B)
    (X : I → V) (w : List (I × ℝ)) (v : V) :
    PolynomialCoordinateGroup.exp m hg (bilinearAdjointWord B X w v) =
      generatorGroupWord X (PolynomialCoordinateGroup.exp m hg) w *
        PolynomialCoordinateGroup.exp m hg v *
        (generatorGroupWord X (PolynomialCoordinateGroup.exp m hg) w)⁻¹ := by
  have he (x y : V) (t : ℝ) :
      PolynomialCoordinateGroup.exp m hg (NormedSpace.exp (t • B x) y) =
        PolynomialCoordinateGroup.exp m hg (t • x) *
          PolynomialCoordinateGroup.exp m hg y *
          (PolynomialCoordinateGroup.exp m hg (t • x))⁻¹ := by
    rw [← hc x y t]
    rfl
  induction w with
  | nil => simp [bilinearAdjointWord]
  | cons z w ih =>
    rcases z with ⟨i, t⟩
    change PolynomialCoordinateGroup.exp m hg
      (NormedSpace.exp (t • B (X i)) (bilinearAdjointWord B X w v)) = _
    rw [he, ih, generatorGroupWord_cons]
    group

/-- Expanding a polynomial scheme gives its actual generator word. -/
theorem exp_polynomialEndpointScheme {c n : ℕ}
    (a : DynkinCoefficients c 2) (B : V →L[ℝ] V →L[ℝ] V) (hB : IsLieBracket B)
    (hg : PolynomialGroupLaws (dynkinProduct a B)) (X : I → V)
    (w : Fin n → List (I × ℝ)) (i : Fin n → I) (t : Fin n → ℝ) :
    PolynomialCoordinateGroup.exp (dynkinProduct a B) hg
      (polynomialEndpointScheme a w i (B, X) t) =
    generatorGroupWord X (PolynomialCoordinateGroup.exp (dynkinProduct a B) hg)
      (generatorSchemeWord w i t) := by
  let := lieRingOfBilinear B hB
  let := lieAlgebraOfBilinear B hB
  unfold polynomialEndpointScheme
  rw [exp_polynomialListProduct, List.map_ofFn]
  unfold generatorSchemeWord generatorGroupWord
  rw [List.map_flatten, List.prod_flatten, List.map_map, List.map_ofFn]
  congr 1
  apply congrArg List.ofFn
  funext k
  change PolynomialCoordinateGroup.exp (dynkinProduct a B) hg
    (dynkinProduct a B
      (dynkinProduct a B (polynomialWord (dynkinProduct a B) X (w k)) (t k • X (i k)))
      (polynomialWord (dynkinProduct a B) X (inverseGeneratorWord (w k)))) =
    generatorGroupWord X (PolynomialCoordinateGroup.exp (dynkinProduct a B) hg)
      (w k ++ [(i k, t k)] ++ inverseGeneratorWord (w k))
  rw [PolynomialCoordinateGroup.exp_mul, PolynomialCoordinateGroup.exp_mul,
    exp_polynomialWord, exp_polynomialWord,
    generatorGroupWord_append, generatorGroupWord_append]
  simp only [generatorGroupWord, List.map_cons, List.map_nil, List.prod_cons,
    List.prod_nil, mul_one]

/-- The polynomial formula of a chosen conjugate scheme is the genuine
ordered basis product whenever the parameters satisfy the group laws. -/
theorem polynomialEndpointScheme_basisProduct {c n : ℕ}
    (a : DynkinCoefficients c 2) (B : V →L[ℝ] V →L[ℝ] V) (hB : IsLieBracket B)
    (hg : PolynomialGroupLaws (dynkinProduct a B))
    (X : I → V) (b : Basis (Fin n) ℝ V)
    (w : Fin n → List (I × ℝ)) (i : Fin n → I)
    (hb : ∀ k (s : ℝ), PolynomialCoordinateGroup.exp (dynkinProduct a B) hg (s • b k) =
      generatorGroupWord X (PolynomialCoordinateGroup.exp (dynkinProduct a B) hg) (w k) *
        PolynomialCoordinateGroup.exp (dynkinProduct a B) hg (s • X (i k)) *
        (generatorGroupWord X (PolynomialCoordinateGroup.exp (dynkinProduct a B) hg) (w k))⁻¹)
    (t : Fin n → ℝ) :
    PolynomialCoordinateGroup.exp (dynkinProduct a B) hg
      (polynomialEndpointScheme a w i (B, X) t) =
        basisExponentialProduct (PolynomialCoordinateGroup.exp (dynkinProduct a B) hg) b t := by
  let := lieRingOfBilinear B hB
  let := lieAlgebraOfBilinear B hB
  unfold polynomialEndpointScheme
  rw [exp_polynomialListProduct, List.map_ofFn]
  unfold basisExponentialProduct
  congr 1
  apply congrArg List.ofFn
  funext k
  change PolynomialCoordinateGroup.exp (dynkinProduct a B) hg
    (dynkinProduct a B
      (dynkinProduct a B (polynomialWord (dynkinProduct a B) X (w k)) (t k • X (i k)))
      (polynomialWord (dynkinProduct a B) X (inverseGeneratorWord (w k)))) = _
  rw [PolynomialCoordinateGroup.exp_mul, PolynomialCoordinateGroup.exp_mul,
    exp_polynomialWord, exp_polynomialWord,
    generatorGroupWord_inverse X _ (PolynomialCoordinateGroup.exp_neg _ _) (w k)]
  exact (hb k (t k)).symm

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_ExpandedSchemeAmplitudes
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The conjugate scheme inside a word with independent amplitudes -/

noncomputable section

namespace PolycyclicRecognition

variable {I : Type*} {n d c : ℕ}

theorem map_schemeAmplitudeSlots (w : Fin n → List (I × ℝ)) (i : Fin n → I)
    (t : Fin n → ℝ) :
    (schemeAmplitudeSlots w i).map (fun p => (p.1, evaluateAmplitudeSlot t p.2)) =
      generatorSchemeWord w i t := by
  simp [schemeAmplitudeSlots, generatorSchemeWord, List.map_flatten,
    List.map_map, List.map_ofFn, evaluateAmplitudeSlot, Function.comp_def]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_ParameterizedAdmissibleWords
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Admissibility is stable under perturbing all word amplitudes -/

noncomputable section

namespace PolycyclicRecognition

open Set Filter
open scoped Topology

variable {G V I P : Type*} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [TopologicalSpace P]

theorem eventually_parameterized_generatorWord
    (U : Set G) (hU : IsOpen U) (Exp : V → G) (hExp : Continuous Exp) (X : I → V)
    (w : List (I × (P → ℝ))) (hc : ∀ p ∈ w, Continuous p.2)
    (g : P → G) (hg : Continuous g) {p₀ : P}
    (hbase : g p₀ ∈ generatorWordBase U Exp X (w.map (fun q => (q.1, q.2 p₀)))) :
    ∀ᶠ p in 𝓝 p₀, g p ∈ generatorWordBase U Exp X (w.map (fun q => (q.1, q.2 p))) := by
  induction w generalizing g with
  | nil => exact hg.continuousAt.eventually (hU.mem_nhds hbase)
  | cons q w ih =>
    have hq : Continuous q.2 := hc q (List.mem_cons_self ..)
    have htail := ih (fun p hp => hc p (List.mem_cons_of_mem _ hp))
      (fun p => g p * Exp (q.2 p • X q.1)) (by fun_prop) hbase.2
    let F : P → C(ℝ, G) := fun p =>
      ⟨fun r => g p * Exp (r • (q.2 p • X q.1)), by fun_prop⟩
    have hF : Continuous F := by
      apply ContinuousMap.continuous_of_continuous_uncurry
      change Continuous (fun z : P × ℝ => g z.1 * Exp (z.2 • (q.2 z.1 • X q.1)))
      fun_prop
    have ho := ContinuousMap.continuous_compactOpen.mp hF
      (Icc (0 : ℝ) 1) isCompact_Icc U hU
    have hfirst : ∀ᶠ p in 𝓝 p₀, g p ∈ flowLineBase U Exp (q.2 p • X q.1) 1 :=
      ho.mem_nhds hbase.1
    filter_upwards [hfirst, htail] with p hp hptail
    exact ⟨hp, hptail⟩

theorem eventually_generatorScheme
    (U : Set G) (hU : IsOpen U) (Exp : V → G) (hExp : Continuous Exp) (X : I → V)
    {n : ℕ} (w : Fin n → List (I × ℝ)) (i : Fin n → I)
    {g : G} (hbase : g ∈ generatorWordBase U Exp X (generatorSchemeWord w i 0)) :
    ∀ᶠ t : Fin n → ℝ in 𝓝 0,
      g ∈ generatorWordBase U Exp X (generatorSchemeWord w i t) := by
  let l := (schemeAmplitudeSlots w i).map
    (fun q => (q.1, fun t : Fin n → ℝ => evaluateAmplitudeSlot t q.2))
  have hcont : ∀ p ∈ l, Continuous p.2 := by
    intro p hp
    obtain ⟨q, _hq, rfl⟩ := List.mem_map.mp hp
    cases q.2 with
    | inl r => exact continuous_const
    | inr j => exact continuous_apply j
  have he (t : Fin n → ℝ) : l.map (fun q => (q.1, q.2 t)) = generatorSchemeWord w i t := by
    simp only [l, List.map_map, Function.comp_def]
    exact map_schemeAmplitudeSlots w i t
  have h := eventually_parameterized_generatorWord U hU Exp hExp X l hcont
    (fun _ => g) continuous_const (p₀ := 0) (by rwa [he])
  simpa only [he] using h

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_AdmissibleConjugateScheme
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Conjugate schemes remain admissible near zero amplitudes -/

noncomputable section

namespace PolycyclicRecognition

open Set Filter
open scoped Topology

variable {G V I : Type*} [Group G] [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem mem_generatorWordBase_zero_cons
    (U : Set G) (Exp : V → G) (hExp0 : Exp 0 = 1) (X : I → V)
    (i : I) (w : List (I × ℝ)) (g : G) :
    g ∈ generatorWordBase U Exp X ((i, 0) :: w) ↔ g ∈ generatorWordBase U Exp X w := by
  constructor
  · intro h
    simpa [hExp0] using h.2
  · intro h
    constructor
    · intro r _hr
      simpa [hExp0] using generatorWordBase_subset U Exp hExp0 X w h
    · simpa [hExp0] using h

theorem mem_generatorWordBase_conjugate_zero
    (U : Set G) (Exp : V → G) (hExp0 : Exp 0 = 1)
    (hneg : ∀ v, Exp (-v) = (Exp v)⁻¹)
    (hadd : ∀ v (s t : ℝ), Exp ((s + t) • v) = Exp (s • v) * Exp (t • v))
    (X : I → V) (w : List (I × ℝ)) (i : I) {g : G}
    (hg : g ∈ generatorWordBase U Exp X w) :
    g ∈ generatorWordBase U Exp X (w ++ [(i, 0)] ++ inverseGeneratorWord w) := by
  rw [List.append_assoc, mem_generatorWordBase_append U Exp hExp0]
  refine ⟨hg, ?_⟩
  rw [List.singleton_append, mem_generatorWordBase_zero_cons U Exp hExp0]
  exact mem_generatorWordBase_inverse U Exp hExp0 hneg hadd X w hg

theorem generatorGroupWord_conjugate_zero
    (Exp : V → G) (hExp0 : Exp 0 = 1) (hneg : ∀ v, Exp (-v) = (Exp v)⁻¹)
    (X : I → V) (w : List (I × ℝ)) (i : I) :
    generatorGroupWord X Exp (w ++ [(i, 0)] ++ inverseGeneratorWord w) = 1 := by
  have he : generatorGroupWord X Exp (w ++ [(i, 0)] ++ inverseGeneratorWord w) =
      generatorGroupWord X Exp w * generatorGroupWord X Exp (inverseGeneratorWord w) := by
    simp [generatorGroupWord, List.map_append, List.prod_append, hExp0]
  rw [he, generatorGroupWord_inverse_of_exp_neg Exp hneg X w, mul_inv_cancel]

theorem mem_generatorWordBase_flatten_loops
    (U : Set G) (Exp : V → G) (hExp0 : Exp 0 = 1) (X : I → V)
    (ws : List (List (I × ℝ))) {g : G}
    (hg : g ∈ U)
    (hws : ∀ w ∈ ws, g ∈ generatorWordBase U Exp X w ∧ generatorGroupWord X Exp w = 1) :
    g ∈ generatorWordBase U Exp X ws.flatten := by
  induction ws with
  | nil => exact hg
  | cons w ws ih =>
    rw [List.flatten_cons, mem_generatorWordBase_append U Exp hExp0]
    obtain ⟨hw, he⟩ := hws w (List.mem_cons_self ..)
    refine ⟨hw, ?_⟩
    rw [he, mul_one]
    exact ih (fun z hz => hws z (List.mem_cons_of_mem _ hz))

theorem mem_generatorScheme_zero
    (U : Set G) (Exp : V → G) (hExp0 : Exp 0 = 1)
    (hneg : ∀ v, Exp (-v) = (Exp v)⁻¹)
    (hadd : ∀ v (s t : ℝ), Exp ((s + t) • v) = Exp (s • v) * Exp (t • v))
    (X : I → V) {n : ℕ} (w : Fin n → List (I × ℝ)) (i : Fin n → I)
    {g : G} (hg : g ∈ U) (hw : ∀ k, g ∈ generatorWordBase U Exp X (w k)) :
    g ∈ generatorWordBase U Exp X (generatorSchemeWord w i 0) := by
  apply mem_generatorWordBase_flatten_loops U Exp hExp0 X _ hg
  intro z hz
  obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hz
  exact ⟨mem_generatorWordBase_conjugate_zero U Exp hExp0 hneg hadd X (w k) (i k) (hw k),
    generatorGroupWord_conjugate_zero Exp hExp0 hneg X (w k) (i k)⟩

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_GenericWeightDirections
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_countable _root_.OAI.PolycyclicRecognition.finitelyGeneratedSubgroupIndex_countable _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Generic directions for a finite weight arrangement -/

noncomputable section

namespace PolycyclicRecognition

open Set

variable {W I : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [FiniteDimensional ℝ W] [Finite I]

/-- Every nonzero weight cuts out a closed hyperplane with empty interior;
the finitely many hyperplanes can be avoided in every open set. -/
theorem dense_genericWeightDirections (α : I → W →L[ℝ] ℝ)
    (hα : ∀ i, α i ≠ 0) : Dense (genericWeightDirections α) := by
  have hd (i : I) : Dense {w : W | α i w ≠ 0} := by
    have hproper : (α i).ker ≠ ⊤ := by
      intro h
      apply hα i
      ext w
      have hw : w ∈ (α i).ker := h ▸ Submodule.mem_top
      exact hw
    have hi : interior ((α i).ker : Set W) = ∅ := by
      apply Set.not_nonempty_iff_eq_empty.mp
      intro h
      exact hproper ((α i).ker.eq_top_of_nonempty_interior' h)
    exact interior_eq_empty_iff_dense_compl.mp hi
  have ho (i : I) : IsOpen {w : W | α i w ≠ 0} :=
    (isClosed_eq (α i).continuous continuous_const).isOpen_compl
  have h := dense_iInter_of_isOpen ho hd
  simpa only [genericWeightDirections, Set.iInter_ofPred] using h

/-- A prescribed side of any one weight contains generic directions. -/
theorem exists_generic_weight_positive (α : I → W →L[ℝ] ℝ)
    (hα : ∀ i, α i ≠ 0) (i : I) :
    ∃ w ∈ genericWeightDirections α, 0 < α i w := by
  have hex : ∃ w, α i w ≠ 0 := by
    by_contra! h
    exact hα i (by ext w; exact h w)
  obtain ⟨v, hv⟩ := hex
  have hne : ({w : W | 0 < α i w} : Set W).Nonempty := by
    rcases lt_or_gt_of_ne hv with hn | hp
    · refine ⟨-v, ?_⟩
      change 0 < α i (-v)
      simpa only [map_neg] using neg_pos.mpr hn
    · exact ⟨v, hp⟩
  exact (dense_genericWeightDirections α hα).exists_mem_open
    (isOpen_lt continuous_const (α i).continuous) hne

theorem exists_generic_weight_negative (α : I → W →L[ℝ] ℝ)
    (hα : ∀ i, α i ≠ 0) (i : I) :
    ∃ w ∈ genericWeightDirections α, α i w < 0 := by
  obtain ⟨v, hv, hi⟩ := exists_generic_weight_positive α hα i
  exact ⟨-v, fun j => by simpa only [map_neg, neg_ne_zero] using hv j,
    by simpa only [map_neg] using neg_neg_of_pos hi⟩

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_WeightChambers
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Incident weight chambers determine an extreme ray

Both signs of every active hyperplane occur among genuine open chambers.
Intersecting their closures therefore imposes the active equations; actual
extremality, rather than a rank assumption, identifies the resulting ray.
-/

noncomputable section

namespace PolycyclicRecognition

open Set Filter
open scoped Topology

variable {W I : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [FiniteDimensional ℝ W] [Finite I]

omit [FiniteDimensional ℝ W] in
theorem exists_positive_chamber_perturbation (α : I → W →L[ℝ] ℝ)
    (σ : I → Bool) {w v : W} (hw : w ∈ closedWeightChamber α σ)
    (hv : ∀ i, orientedWeight α σ i w = 0 → 0 < orientedWeight α σ i v) :
    ∃ t : ℝ, 0 < t ∧ w + t • v ∈ weightChamber α σ := by
  have hevent (i : I) : ∀ᶠ t : ℝ in 𝓝 0,
      0 < t → 0 < orientedWeight α σ i (w + t • v) := by
    by_cases hi : orientedWeight α σ i w = 0
    · exact Eventually.of_forall (fun t ht => by
        simpa only [map_add, map_smul, hi, zero_add, smul_eq_mul]
          using mul_pos ht (hv i hi))
    · have hp : 0 < orientedWeight α σ i w :=
        lt_of_le_of_ne (hw i) (Ne.symm hi)
      have hc : Continuous (fun t : ℝ => orientedWeight α σ i (w + t • v)) := by
        fun_prop
      have h0 : 0 < orientedWeight α σ i (w + (0 : ℝ) • v) := by simpa using hp
      filter_upwards [(isOpen_lt continuous_const hc).mem_nhds h0] with t ht
      exact fun _ => ht
  obtain ⟨ε, hε, he⟩ := Metric.eventually_nhds_iff.mp (eventually_all.mpr hevent)
  have hsmall : dist (ε / 2) 0 < ε := by
    rw [Real.dist_eq, sub_zero, abs_of_pos (half_pos hε)]
    exact half_lt_self hε
  exact ⟨ε / 2, half_pos hε, fun i => he hsmall i (half_pos hε)⟩

omit [FiniteDimensional ℝ W] in
/-- Break ties at the active hyperplanes using a generic direction. -/
theorem exists_incident_chamber_of_generic (α : I → W →L[ℝ] ℝ) (w : W)
    {v : W} (hv : v ∈ genericWeightDirections α) :
    ∃ σ : I → Bool, incidentWeightChamber α w σ ∧
      ∀ i, α i w = 0 → σ i = weightSigns α v i := by
  classical
  let σ : I → Bool := fun i => if α i w = 0 then weightSigns α v i else weightSigns α w i
  have hw : w ∈ closedWeightChamber α σ := by
    intro i
    by_cases hi : α i w = 0
    · cases hs : σ i <;> simp [orientedWeight, hs, hi]
    · by_cases hp : 0 < α i w
      · simpa [orientedWeight, σ, hi, weightSigns, hp] using hp.le
      · simpa [orientedWeight, σ, hi, weightSigns, hp] using neg_nonneg.mpr (le_of_not_gt hp)
  have hv' : ∀ i, orientedWeight α σ i w = 0 → 0 < orientedWeight α σ i v := by
    intro i hi
    have hw0 : α i w = 0 := by
      by_cases hs : σ i = true
      · simpa [orientedWeight, hs] using hi
      · simpa [orientedWeight, hs] using hi
    by_cases hp : 0 < α i v
    · simp [orientedWeight, σ, hw0, weightSigns, hp]
    · have hn : α i v < 0 := lt_of_le_of_ne (le_of_not_gt hp) (hv i)
      simpa [orientedWeight, σ, hw0, weightSigns, hp] using neg_pos.mpr hn
  obtain ⟨t, _, ht⟩ := exists_positive_chamber_perturbation α σ hw hv'
  exact ⟨σ, ⟨⟨w + t • v, ht⟩, hw⟩, fun i hi => by simp [σ, hi]⟩

theorem exists_incident_chamber_positive (α : I → W →L[ℝ] ℝ)
    (hα : ∀ i, α i ≠ 0) (w : W) (i : I) (hi : α i w = 0) :
    ∃ σ : I → Bool, incidentWeightChamber α w σ ∧ σ i = true := by
  obtain ⟨v, hv, hp⟩ := exists_generic_weight_positive α hα i
  obtain ⟨σ, hs, he⟩ := exists_incident_chamber_of_generic α w hv
  exact ⟨σ, hs, by simpa [weightSigns, hp] using he i hi⟩

theorem exists_incident_chamber_negative (α : I → W →L[ℝ] ℝ)
    (hα : ∀ i, α i ≠ 0) (w : W) (i : I) (hi : α i w = 0) :
    ∃ σ : I → Bool, incidentWeightChamber α w σ ∧ σ i = false := by
  obtain ⟨v, hv, hp⟩ := exists_generic_weight_negative α hα i
  obtain ⟨σ, hs, he⟩ := exists_incident_chamber_of_generic α w hv
  refine ⟨σ, hs, ?_⟩
  rw [he i hi]
  simp [weightSigns, not_lt.mpr hp.le]

theorem incident_chamber_intersection_eq_ray (α : I → W →L[ℝ] ℝ)
    (hα : ∀ i, α i ≠ 0)
    (hsep : ∀ x : W, (∀ i, α i x = 0) → x = 0)
    {w : W} (σ₀ : I → Bool) (hσ₀ : (weightChamber α σ₀).Nonempty)
    (hExt : IsExtreme ℝ (closedWeightChamber α σ₀) (nonnegativeRay w)) :
    {x | ∀ σ, incidentWeightChamber α w σ → x ∈ closedWeightChamber α σ} =
      nonnegativeRay w := by
  ext x
  constructor
  · intro hx
    have hw : w ∈ closedWeightChamber α σ₀ := hExt.subset ⟨1, zero_le_one, by simp⟩
    have hsep' : ∀ y : W, (∀ i, orientedWeight α σ₀ i y = 0) → y = 0 := by
      intro y hy
      apply hsep y
      intro i
      have hi := hy i
      cases hs : σ₀ i <;> simpa [orientedWeight, hs] using hi
    apply mem_ray_of_active_constraints (orientedWeight α σ₀) hsep' hExt
      (hx σ₀ ⟨hσ₀, hw⟩)
    intro i hi
    have hw0 : α i w = 0 := by
      cases hs : σ₀ i <;> simpa [orientedWeight, hs] using hi
    obtain ⟨σp, hσp, hp⟩ := exists_incident_chamber_positive α hα w i hw0
    obtain ⟨σm, hσm, hm⟩ := exists_incident_chamber_negative α hα w i hw0
    have hpos : 0 ≤ α i x := by
      simpa [orientedWeight, hp] using hx σp hσp i
    have hneg : α i x ≤ 0 := by
      simpa [orientedWeight, hm] using hx σm hσm i
    have hzero := le_antisymm hneg hpos
    cases hs : σ₀ i <;> simp [orientedWeight, hs, hzero]
  · rintro ⟨r, hr, rfl⟩ σ hσ i
    simpa only [map_smul, smul_eq_mul] using mul_nonneg hr (hσ.2 i)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_WeightChamberLimits
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instNonemptyBases _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_nonempty _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Approaching an incident chamber and identifying its ray labels -/

noncomputable section

namespace PolycyclicRecognition

open Set Filter
open scoped Topology

variable {W I : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]

theorem isClosed_closedWeightChamber (α : I → W →L[ℝ] ℝ) (σ : I → Bool) :
    IsClosed (closedWeightChamber α σ) := by
  change IsClosed {w | ∀ i, 0 ≤ orientedWeight α σ i w}
  simp only [ofPred_forall]
  exact isClosed_iInter (fun i => isClosed_le continuous_const (orientedWeight α σ i).continuous)

theorem mem_chamber_add_smul (α : I → W →L[ℝ] ℝ) (σ : I → Bool)
    {w v : W} (hw : w ∈ closedWeightChamber α σ) (hv : v ∈ weightChamber α σ)
    {t : ℝ} (ht : 0 < t) : w + t • v ∈ weightChamber α σ := by
  intro i
  simpa only [map_add, map_smul, smul_eq_mul] using
    add_pos_of_nonneg_of_pos (hw i) (mul_pos ht (hv i))

theorem closure_weightChamber (α : I → W →L[ℝ] ℝ) (σ : I → Bool)
    (hσ : (weightChamber α σ).Nonempty) :
    closure (weightChamber α σ) = closedWeightChamber α σ := by
  apply Subset.antisymm
  · apply (isClosed_closedWeightChamber α σ).closure_subset_iff.mpr
    exact fun _ hx i => (hx i).le
  · intro w hw
    obtain ⟨v, hv⟩ := hσ
    have ht : Tendsto (fun n : ℕ => w + (1 / ((n : ℝ) + 1)) • v) atTop (𝓝 w) := by
      simpa using tendsto_const_nhds.add
        ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).smul_const v)
    exact mem_closure_of_tendsto ht (Eventually.of_forall (fun n =>
      mem_chamber_add_smul α σ hw hv (by positivity)))

/-- The approximating horizontal vectors are explicit: add a vanishing
multiple of any lift of an interior chamber vector. -/
theorem exists_lifted_chamber_sequence
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (π : V →L[ℝ] W) (hπ : Function.Surjective π)
    (α : I → W →L[ℝ] ℝ) (v : V) (σ : I → Bool)
    (hσ : incidentWeightChamber α (π v) σ) :
    ∃ u : ℕ → V, Tendsto u atTop (𝓝 v) ∧ ∀ n, π (u n) ∈ weightChamber α σ := by
  obtain ⟨w, hw⟩ := hσ.1
  obtain ⟨x, hx⟩ := hπ w
  refine ⟨fun n => v + (1 / ((n : ℝ) + 1)) • x, ?_, ?_⟩
  · simpa using tendsto_const_nhds.add
      ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).smul_const x)
  · intro n
    rw [map_add, map_smul, hx]
    exact mem_chamber_add_smul α σ hσ.2 hw (by positivity)

variable [FiniteDimensional ℝ W] [Finite I]

/-- Agreement on the incident chamber images gives agreement on the ray. -/
theorem map_mem_ray_of_incident_chambers
    (α : I → W →L[ℝ] ℝ) (hα : ∀ i, α i ≠ 0)
    (hsep : ∀ x : W, (∀ i, α i x = 0) → x = 0)
    {w : W} (σ₀ : I → Bool) (hσ₀ : (weightChamber α σ₀).Nonempty)
    (hExt : IsExtreme ℝ (closedWeightChamber α σ₀) (nonnegativeRay w))
    (A B : W ≃ₗ[ℝ] W)
    (himages : ∀ σ, incidentWeightChamber α w σ →
      A '' closedWeightChamber α σ = B '' closedWeightChamber α σ) :
    B w ∈ nonnegativeRay (A w) := by
  have hpre : A.symm (B w) ∈ nonnegativeRay w := by
    rw [← incident_chamber_intersection_eq_ray α hα hsep σ₀ hσ₀ hExt]
    intro σ hσ
    have hb : B w ∈ A '' closedWeightChamber α σ := by
      rw [himages σ hσ]
      exact mem_image_of_mem B hσ.2
    obtain ⟨x, hx, he⟩ := hb
    have hxe : A.symm (B w) = x := by rw [← he, A.symm_apply_apply]
    exact hxe ▸ hx
  obtain ⟨r, hr, he⟩ := hpre
  have he' : B w = r • A w := by
    have hh := congrArg A he
    simpa only [A.apply_symm_apply, map_smul] using hh
  exact ⟨r, hr, he'⟩

/-- Any positive homogeneous gauge suffices; in particular the existing
segment support norm can be used without changing normed-space instances. -/
theorem eq_on_extreme_ray_of_incident_chambers_of_gauge
    (α : I → W →L[ℝ] ℝ) (hα : ∀ i, α i ≠ 0)
    (hsep : ∀ x : W, (∀ i, α i x = 0) → x = 0)
    {w : W} (σ₀ : I → Bool) (hσ₀ : (weightChamber α σ₀).Nonempty)
    (hExt : IsExtreme ℝ (closedWeightChamber α σ₀) (nonnegativeRay w))
    (p : W → ℝ) (hp : ∀ x, x ≠ 0 → 0 < p x)
    (hsmul : ∀ x r, 0 ≤ r → p (r • x) = r * p x)
    (A B : W ≃ₗ[ℝ] W) (hA : p (A w) = p w) (hB : p (B w) = p w)
    (himages : ∀ σ, incidentWeightChamber α w σ →
      A '' closedWeightChamber α σ = B '' closedWeightChamber α σ) : A w = B w := by
  by_cases hw : w = 0
  · simp [hw]
  obtain ⟨r, hr, he⟩ := map_mem_ray_of_incident_chambers α hα hsep σ₀ hσ₀ hExt A B himages
  have hval : r * p w = p w := by
    rw [he, hsmul _ _ hr, hA] at hB
    exact hB
  have hr1 : r = 1 := by nlinarith [hp w hw]
  simpa only [hr1, one_smul] using he.symm

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_ChamberBase
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A compact normalized base of a pointed weight chamber -/

noncomputable section

namespace PolycyclicRecognition

open Set

variable {W I : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [Fintype I]

omit [Fintype I] in
theorem oriented_weights_separate (α : I → W →L[ℝ] ℝ) (σ : I → Bool)
    (hsep : ∀ x : W, (∀ i, α i x = 0) → x = 0) :
    ∀ x : W, (∀ i, orientedWeight α σ i x = 0) → x = 0 := by
  intro x hx
  apply hsep x
  intro i
  have hi := hx i
  cases hs : σ i <;> simpa [orientedWeight, hs] using hi

theorem chamberFunctional_pos (α : I → W →L[ℝ] ℝ) (σ : I → Bool)
    (hsep : ∀ x : W, (∀ i, α i x = 0) → x = 0)
    {x : W} (hx : x ∈ closedWeightChamber α σ) (hx0 : x ≠ 0) :
    0 < chamberFunctional α σ x := by
  change 0 < (∑ i, orientedWeight α σ i) x
  rw [sum_apply]
  apply lt_of_le_of_ne (Finset.sum_nonneg (fun i _ => hx i))
  intro he
  apply hx0
  apply oriented_weights_separate α σ hsep x
  have hz := Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hx i) |>.mp he.symm
  exact fun i => hz i (Finset.mem_univ i)

theorem isClosed_chamberBase (α : I → W →L[ℝ] ℝ) (σ : I → Bool) :
    IsClosed (chamberBase α σ) :=
  (isClosed_closedWeightChamber α σ).inter
    (isClosed_eq (chamberFunctional α σ).continuous continuous_const)

theorem convex_chamberBase (α : I → W →L[ℝ] ℝ) (σ : I → Bool) :
    Convex ℝ (chamberBase α σ) := by
  intro x hx y hy a b ha hb hab
  constructor
  · intro i
    simp only [map_add, map_smul, smul_eq_mul]
    exact add_nonneg (mul_nonneg ha (hx.1 i)) (mul_nonneg hb (hy.1 i))
  · simp only [map_add, map_smul, hx.2, hy.2, smul_eq_mul, mul_one]
    exact hab

theorem isCompact_chamberBase [FiniteDimensional ℝ W] (α : I → W →L[ℝ] ℝ) (σ : I → Bool)
    (hsep : ∀ x : W, (∀ i, α i x = 0) → x = 0) :
    IsCompact (chamberBase α σ) := by
  let e : W →L[ℝ] (I → ℝ) := ContinuousLinearMap.pi (orientedWeight α σ)
  have hinj : Function.Injective e := by
    intro x y hxy
    apply sub_eq_zero.mp
    apply oriented_weights_separate α σ hsep
    intro i
    have hi := congrFun hxy i
    change orientedWeight α σ i x = orientedWeight α σ i y at hi
    simp only [map_sub, hi, sub_self]
  obtain ⟨K, _hK, he⟩ := e.toLinearMap.injective_iff_antilipschitz.mp hinj
  have hcube : IsCompact (Set.pi univ (fun _ : I => Icc (0 : ℝ) 1)) :=
    isCompact_univ_pi (fun _ => isCompact_Icc)
  apply Metric.isCompact_of_isClosed_isBounded (isClosed_chamberBase α σ)
  apply (he.isBounded_preimage hcube.isBounded).subset
  intro x hx i _hi
  change 0 ≤ orientedWeight α σ i x ∧ orientedWeight α σ i x ≤ 1
  refine ⟨hx.1 i, ?_⟩
  have hle := Finset.single_le_sum (fun j _ => hx.1 j) (Finset.mem_univ i)
  have hsum : ∑ j, orientedWeight α σ j x = 1 := by
    simpa only [chamberFunctional, sum_apply] using hx.2
  exact hle.trans_eq hsum

theorem normalize_mem_chamberBase (α : I → W →L[ℝ] ℝ) (σ : I → Bool)
    (hsep : ∀ x : W, (∀ i, α i x = 0) → x = 0)
    {x : W} (hx : x ∈ closedWeightChamber α σ) (hx0 : x ≠ 0) :
    (chamberFunctional α σ x)⁻¹ • x ∈ chamberBase α σ := by
  have hp := chamberFunctional_pos α σ hsep hx hx0
  constructor
  · intro i
    simpa only [map_smul, smul_eq_mul] using mul_nonneg (inv_nonneg.mpr hp.le) (hx i)
  · simp only [map_smul, smul_eq_mul, inv_mul_cancel₀ hp.ne']

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_ChamberExtremeDirections
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Extreme directions span a full-dimensional weight chamber -/

noncomputable section

namespace PolycyclicRecognition

open Set

variable {W I : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [Fintype I]

theorem extremePoint_base_extreme_ray (α : I → W →L[ℝ] ℝ) (σ : I → Bool)
    (hsep : ∀ x : W, (∀ i, α i x = 0) → x = 0)
    {x : W} (hx : x ∈ (chamberBase α σ).extremePoints ℝ) :
    x ∈ chamberExtremeDirections α σ := by
  have hxbase := extremePoints_subset hx
  have hx0 : x ≠ 0 := by
    intro h
    simpa only [h, map_zero, zero_ne_one] using hxbase.2
  refine ⟨hx0, ⟨?_, ?_⟩⟩
  · rintro _ ⟨r, hr, rfl⟩ i
    simpa only [map_smul, smul_eq_mul] using mul_nonneg hr (hxbase.1 i)
  · intro u hu v hv z hz hseg
    obtain ⟨r, hr, rfl⟩ := hz
    obtain ⟨a, b, ha, hb, hab, he⟩ := hseg
    by_cases hu0 : u = 0
    · exact ⟨0, le_rfl, by simp [hu0]⟩
    by_cases hv0 : v = 0
    · have hau : a • u = r • x := by simpa only [hv0, smul_zero, add_zero] using he
      refine ⟨a⁻¹ * r, mul_nonneg (inv_nonneg.mpr ha.le) hr, ?_⟩
      calc
        u = a⁻¹ • (a • u) := by rw [smul_smul, inv_mul_cancel₀ ha.ne', one_smul]
        _ = (a⁻¹ * r) • x := by rw [hau, smul_smul]
    have hpu := chamberFunctional_pos α σ hsep hu hu0
    have hpv := chamberFunctional_pos α σ hsep hv hv0
    have hsum : a * chamberFunctional α σ u + b * chamberFunctional α σ v = r := by
      have hh := congrArg (chamberFunctional α σ) he
      simpa only [map_add, map_smul, smul_eq_mul, hxbase.2, mul_one] using hh
    have hrpos : 0 < r := by
      rw [← hsum]
      exact add_pos (mul_pos ha hpu) (mul_pos hb hpv)
    have hnormseg : x ∈ openSegment ℝ
        ((chamberFunctional α σ u)⁻¹ • u) ((chamberFunctional α σ v)⁻¹ • v) := by
      refine ⟨a * chamberFunctional α σ u / r, b * chamberFunctional α σ v / r,
        div_pos (mul_pos ha hpu) hrpos, div_pos (mul_pos hb hpv) hrpos, ?_, ?_⟩
      · rw [← add_div, hsum, div_self hrpos.ne']
      · have hau : (a * chamberFunctional α σ u / r) * (chamberFunctional α σ u)⁻¹ =
            r⁻¹ * a := by field_simp
        have hbv : (b * chamberFunctional α σ v / r) * (chamberFunctional α σ v)⁻¹ =
            r⁻¹ * b := by field_simp
        rw [smul_smul, smul_smul, hau, hbv, ← smul_smul, ← smul_smul,
          ← smul_add, he, smul_smul, inv_mul_cancel₀ hrpos.ne', one_smul]
    have hueq : (chamberFunctional α σ u)⁻¹ • u = x :=
      hx.2 (normalize_mem_chamberBase α σ hsep hu hu0)
        (normalize_mem_chamberBase α σ hsep hv hv0) hnormseg
    refine ⟨chamberFunctional α σ u, hpu.le, ?_⟩
    calc
      u = chamberFunctional α σ u • ((chamberFunctional α σ u)⁻¹ • u) := by
        rw [smul_smul, mul_inv_cancel₀ hpu.ne', one_smul]
      _ = chamberFunctional α σ u • x := by rw [hueq]

variable [FiniteDimensional ℝ W]

theorem chamberBase_subset_span_extremeDirections (α : I → W →L[ℝ] ℝ) (σ : I → Bool)
    (hsep : ∀ x : W, (∀ i, α i x = 0) → x = 0) :
    chamberBase α σ ⊆ Submodule.span ℝ (chamberExtremeDirections α σ) := by
  rw [← closure_convexHull_extremePoints (isCompact_chamberBase α σ hsep)
    (convex_chamberBase α σ)]
  apply closure_minimal
  · apply convexHull_min
    · exact fun _ hx => Submodule.subset_span (extremePoint_base_extreme_ray α σ hsep hx)
    · exact Submodule.convex _
  · exact Submodule.closed_of_finiteDimensional _

theorem closedChamber_subset_span_extremeDirections (α : I → W →L[ℝ] ℝ) (σ : I → Bool)
    (hsep : ∀ x : W, (∀ i, α i x = 0) → x = 0) :
    closedWeightChamber α σ ⊆ Submodule.span ℝ (chamberExtremeDirections α σ) := by
  intro x hx
  by_cases hx0 : x = 0
  · rw [hx0]; exact Submodule.zero_mem _
  have hn := chamberBase_subset_span_extremeDirections α σ hsep
    (normalize_mem_chamberBase α σ hsep hx hx0)
  have hp := chamberFunctional_pos α σ hsep hx hx0
  have hh := Submodule.smul_mem (Submodule.span ℝ (chamberExtremeDirections α σ))
    (chamberFunctional α σ x) hn
  rw [smul_smul, mul_inv_cancel₀ hp.ne', one_smul] at hh
  exact hh

theorem span_chamberExtremeDirections_eq_top (α : I → W →L[ℝ] ℝ) (σ : I → Bool)
    (hsep : ∀ x : W, (∀ i, α i x = 0) → x = 0)
    (hne : (weightChamber α σ).Nonempty) :
    Submodule.span ℝ (chamberExtremeDirections α σ) = ⊤ := by
  have hopen : IsOpen (weightChamber α σ) := by
    change IsOpen {w | ∀ i, 0 < orientedWeight α σ i w}
    simp only [ofPred_forall]
    exact isOpen_iInter_of_finite (fun i =>
      isOpen_lt continuous_const (orientedWeight α σ i).continuous)
  have hsub : weightChamber α σ ⊆ Submodule.span ℝ (chamberExtremeDirections α σ) :=
    fun _ hx => closedChamber_subset_span_extremeDirections α σ hsep (fun i => (hx i).le)
  apply Submodule.eq_top_of_nonempty_interior'
  exact hne.mono (hopen.subset_interior_iff.mpr hsub)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_CompactAeExhaustion
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_countable _root_.OAI.PolycyclicRecognition.finitelyGeneratedSubgroupIndex_countable _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Extending local almost-everywhere assertions over an open domain -/

namespace PolycyclicRecognition

open Set MeasureTheory

theorem ae_restrict_of_compact_subsets
    {X : Type*} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    [SecondCountableTopology X] [MeasurableSpace X]
    (μ : Measure X) (U : Set X) (hU : IsOpen U) (p : X → Prop)
    (h : ∀ K : Set X, IsCompact K → K ⊆ U → ∀ᵐ x ∂μ.restrict K, p x) :
    ∀ᵐ x ∂μ.restrict U, p x := by
  let : LocallyCompactSpace U := hU.locallyCompactSpace
  have hσ : IsSigmaCompact U := by
    simpa only [Subtype.range_coe] using
      (isSigmaCompact_range (continuous_subtype_val : Continuous ((↑) : U → X)))
  obtain ⟨K, hK, hcover⟩ := hσ
  rw [← hcover, ae_restrict_iUnion_iff]
  intro n
  exact h (K n) (hK n) (fun x hx => hcover ▸ mem_iUnion.mpr ⟨n, hx⟩)

end PolycyclicRecognition

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_ExtremeDirectionLabels
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_countable _root_.OAI.PolycyclicRecognition.finitelyGeneratedSubgroupIndex_countable _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Constant labels on extreme horizontal directions

The generic chamber relation passes through actual approximating horizontal
vectors, jointly in the base point and both times. The incident chambers
then determine the extreme ray and its norm-preserving label value.
-/

noncomputable section

namespace PolycyclicRecognition

open MeasureTheory Filter Set
open scoped Topology

variable {G V W I L : Type*}
  [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
  [TopologicalSpace.PseudoMetrizableSpace G] [MeasurableSpace G] [BorelSpace G]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] [Finite I]
  [Fintype L] [MeasurableSpace L] [MeasurableSingletonClass L]

omit [FiniteDimensional ℝ W] in
theorem direction_chambers_agree_on_compact
    (μ : Measure G) [μ.IsHaarMeasure] [μ.IsMulRightInvariant]
    (π : V →L[ℝ] W) (hπ : Function.Surjective π)
    (Exp : V → G) (hExp : Continuous Exp)
    (label : G → L) (hlabel : Measurable label)
    (A : L → W ≃ₗ[ℝ] W) (α : I → W →L[ℝ] ℝ)
    (U : Set G) (hU : IsOpen U) (v : V)
    (hgeneric : ∀ σ : I → Bool, incidentWeightChamber α (π v) σ →
      ∀ u : V, π u ∈ weightChamber α σ →
      ∀ᵐ z ∂(pairTimeMeasure.prod μ), z ∈ flowSegmentDomain U Exp u →
        A (label (z.2 * Exp (z.1.1 • u))) '' closedWeightChamber α σ =
          A (label (z.2 * Exp (z.1.2 • u))) '' closedWeightChamber α σ)
    (K : Set ((ℝ × ℝ) × G)) (hK : IsCompact K)
    (hKU : K ⊆ flowSegmentDomain U Exp v) :
    ∀ᵐ z ∂(pairTimeMeasure.prod μ).restrict K,
      ∀ σ, incidentWeightChamber α (π v) σ →
        A (label (z.2 * Exp (z.1.1 • v))) '' closedWeightChamber α σ =
          A (label (z.2 * Exp (z.1.2 • v))) '' closedWeightChamber α σ := by
  have hchamber (σ : I → Bool) : ∀ᵐ z ∂(pairTimeMeasure.prod μ).restrict K,
      incidentWeightChamber α (π v) σ →
        A (label (z.2 * Exp (z.1.1 • v))) '' closedWeightChamber α σ =
          A (label (z.2 * Exp (z.1.2 • v))) '' closedWeightChamber α σ := by
    by_cases hs : incidentWeightChamber α (π v) σ
    · obtain ⟨u, hu, huc⟩ := exists_lifted_chamber_sequence π hπ α v σ hs
      have hstay := eventually_compact_flowSegments U hU Exp hExp u hu K hK hKU
      have hevent : ∀ᶠ n in atTop, ∀ᵐ z ∂(pairTimeMeasure.prod μ).restrict K,
          A (label (z.2 * Exp (z.1.1 • u n))) '' closedWeightChamber α σ =
            A (label (z.2 * Exp (z.1.2 • u n))) '' closedWeightChamber α σ := by
        filter_upwards [hstay] with n hn
        filter_upwards [ae_restrict_of_ae (hgeneric σ hs (u n) (huc n)),
          ae_restrict_mem hK.measurableSet] with z hz hzk
        exact hz (hn hzk)
      have he := finiteLabel_jointDirections_relation μ Exp hExp label hlabel u hu K hK
        (fun l m => A l '' closedWeightChamber α σ = A m '' closedWeightChamber α σ) hevent
      exact he.mono (fun _ hz _ => hz)
    · exact Eventually.of_forall (fun _ h => (hs h).elim)
  exact ae_all_iff.mpr hchamber

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_ExtremeTemplateLabels
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteRootOffsetConeIndex _root_.OAI.PolycyclicRecognition.instNonemptyRootOffsetConeIndex _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual template labels agree along extreme directions

The positive homogeneous segment-support norm already removes scaling on a
ray. No auxiliary invariant Euclidean norm is a premise of this theorem.
-/

noncomputable section

namespace PolycyclicRecognition.SupportDatum

open MeasureTheory Set Filter

theorem extreme_template_derivative_values_equal
    {G V W I B L : Type*}
    [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
    [TopologicalSpace.PseudoMetrizableSpace G] [MeasurableSpace G] [BorelSpace G]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
    [Fintype I] [Fintype B] [Nonempty B]
    [Fintype L] [MeasurableSpace L] [MeasurableSingletonClass L]
    (D : SupportDatum W I B) (hweights : ∀ i, D.weight i ≠ 0)
    (μ : Measure G) [μ.IsHaarMeasure] [μ.IsMulRightInvariant]
    (π : V →L[ℝ] W) (hπ : Function.Surjective π)
    (Exp : V → G) (hExp : Continuous Exp)
    (label : G → L) (hlabel : Measurable label) (A : L → templateSymmetryGroup D)
    (U : Set G) (hU : IsOpen U) (v : V) (σ₀ : I → Bool)
    (hσ₀ : (weightChamber (fun i => (D.weight i).toContinuousLinearMap) σ₀).Nonempty)
    (hExt : IsExtreme ℝ (closedWeightChamber (fun i => (D.weight i).toContinuousLinearMap) σ₀)
      (nonnegativeRay (π v)))
    (hgeneric : ∀ σ : I → Bool,
      incidentWeightChamber (fun i => (D.weight i).toContinuousLinearMap) (π v) σ →
      ∀ u : V, π u ∈ weightChamber (fun i => (D.weight i).toContinuousLinearMap) σ →
      ∀ᵐ z ∂(pairTimeMeasure.prod μ), z ∈ flowSegmentDomain U Exp u →
        (A (label (z.2 * Exp (z.1.1 • u)))).val ''
            closedWeightChamber (fun i => (D.weight i).toContinuousLinearMap) σ =
          (A (label (z.2 * Exp (z.1.2 • u)))).val ''
            closedWeightChamber (fun i => (D.weight i).toContinuousLinearMap) σ) :
    ∀ᵐ z ∂(pairTimeMeasure.prod μ).restrict (flowSegmentDomain U Exp v),
      (A (label (z.2 * Exp (z.1.1 • v)))).val (π v) =
        (A (label (z.2 * Exp (z.1.2 • v)))).val (π v) := by
  let α : I → W →L[ℝ] ℝ := fun i => (D.weight i).toContinuousLinearMap
  have hα (i : I) : α i ≠ 0 := by
    intro hi
    apply hweights i
    ext w
    exact congrArg (fun f : W →L[ℝ] ℝ => f w) hi
  apply ae_restrict_of_compact_subsets (pairTimeMeasure.prod μ)
    (flowSegmentDomain U Exp v) (isOpen_flowSegmentDomain U hU Exp hExp v)
  intro K hK hKU
  filter_upwards [direction_chambers_agree_on_compact μ π hπ Exp hExp label hlabel
    (fun l => (A l).val) α U hU v hgeneric K hK hKU] with z hz
  exact eq_on_extreme_ray_of_incident_chambers_of_gauge α hα D.separates σ₀ hσ₀ hExt
    D.segmentSupport (fun _ hw => D.segmentSupport_pos hw)
    (fun w _ hr => D.segmentSupport_smul_of_nonneg w hr) _ _
    (templateSymmetry_mem_linearSupportSymmetry D (A _) (π v))
    (templateSymmetry_mem_linearSupportSymmetry D (A _) (π v)) hz

end PolycyclicRecognition.SupportDatum

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_PositiveVariationEquality
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Equality in the positive-variation bound

Attaining the total positive variation at an intermediate time forces the
derivative to have the two ordered signs on either side of that time.
-/

noncomputable section

namespace PolycyclicRecognition

open MeasureTheory Set

/-- The equality case used at a maximizing time of each scalar weight of a
profile. The positive and negative variations are derived from the integrable
derivative; their vanishing is a conclusion. -/
theorem positive_variation_equality_signs
    (q : ℝ → ℝ) {a t b : ℝ} (hat : a ≤ t) (htb : t ≤ b)
    (hq : IntervalIntegrable q volume a b)
    (heq : (∫ s in a..t, q s) = ∫ s in a..b, max (q s) 0) :
    (∀ᵐ s ∂volume.restrict (Ioc a t), 0 ≤ q s) ∧
      (∀ᵐ s ∂volume.restrict (Ioc t b), q s ≤ 0) := by
  have hp : IntervalIntegrable (fun s => max (q s) 0) volume a b :=
    ⟨hq.1.pos_part, hq.2.pos_part⟩
  have hn : IntervalIntegrable (fun s => max (-q s) 0) volume a b :=
    ⟨hq.1.neg_part, hq.2.neg_part⟩
  have hsub₁ : uIcc a t ⊆ uIcc a b := by
    rw [uIcc_of_le hat, uIcc_of_le (hat.trans htb)]
    exact Icc_subset_Icc le_rfl htb
  have hsub₂ : uIcc t b ⊆ uIcc a b := by
    rw [uIcc_of_le htb, uIcc_of_le (hat.trans htb)]
    exact Icc_subset_Icc hat le_rfl
  have hp₁ := hp.mono_set hsub₁
  have hp₂ := hp.mono_set hsub₂
  have hn₁ := hn.mono_set hsub₁
  have hparts : (∫ s in a..t, q s) =
      (∫ s in a..t, max (q s) 0) - ∫ s in a..t, max (-q s) 0 := by
    rw [← intervalIntegral.integral_sub hp₁ hn₁]
    apply intervalIntegral.integral_congr
    intro s _
    change q s = max (q s) 0 - max (-q s) 0
    by_cases hs : 0 ≤ q s
    · rw [max_eq_left hs, max_eq_right (neg_nonpos.mpr hs), sub_zero]
    · have hs' := le_of_not_ge hs
      rw [max_eq_right hs', max_eq_left (neg_nonneg.mpr hs')]
      ring
  have hadd := intervalIntegral.integral_add_adjacent_intervals hp₁ hp₂
  have hnonneg₁ : 0 ≤ ∫ s in a..t, max (-q s) 0 :=
    intervalIntegral.integral_nonneg_of_forall hat (fun _ => le_max_right _ _)
  have hnonneg₂ : 0 ≤ ∫ s in t..b, max (q s) 0 :=
    intervalIntegral.integral_nonneg_of_forall htb (fun _ => le_max_right _ _)
  have hzero₁ : (∫ s in a..t, max (-q s) 0) = 0 := by linarith
  have hzero₂ : (∫ s in t..b, max (q s) 0) = 0 := by linarith
  have hae₁ := (intervalIntegral.integral_eq_zero_iff_of_le_of_nonneg_ae hat
    (Filter.Eventually.of_forall (fun s => le_max_right (-q s) 0)) hn₁).mp hzero₁
  have hae₂ := (intervalIntegral.integral_eq_zero_iff_of_le_of_nonneg_ae htb
    (Filter.Eventually.of_forall (fun s => le_max_right (q s) 0)) hp₂).mp hzero₂
  constructor
  · filter_upwards [hae₁] with s hs
    have := le_max_left (-q s) 0
    change max (-q s) 0 = 0 at hs
    linarith
  · filter_upwards [hae₂] with s hs
    have := le_max_left (q s) 0
    change max (q s) 0 = 0 at hs
    linarith

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_FiniteSignOrder
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_countable _root_.OAI.PolycyclicRecognition.finitelyGeneratedSubgroupIndex_countable _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Ordered signs with constant positive count are constant -/

noncomputable section

namespace PolycyclicRecognition

open MeasureTheory Set Filter

/-- A finite set of signs cannot change when every positive sign can only
disappear and their total count stays constant. -/
theorem positive_signs_eq_of_ordered
    {I : Type*} [Fintype I] (q : I → ℝ → ℝ) (τ : I → ℝ)
    {s t : ℝ} (hst : s ≤ t)
    (hs : ∀ i, q i s ≠ 0 ∧ (s ≤ τ i → 0 ≤ q i s) ∧ (τ i < s → q i s ≤ 0))
    (ht : ∀ i, q i t ≠ 0 ∧ (t ≤ τ i → 0 ≤ q i t) ∧ (τ i < t → q i t ≤ 0))
    (hcard : (Finset.univ.filter (fun i => 0 < q i s)).card =
      (Finset.univ.filter (fun i => 0 < q i t)).card) :
    ∀ i, (0 < q i s ↔ 0 < q i t) := by
  classical
  have hsub : Finset.univ.filter (fun i => 0 < q i t) ⊆
      Finset.univ.filter (fun i => 0 < q i s) := by
    intro i hi
    have hpos := (Finset.mem_filter.mp hi).2
    have htτ : t ≤ τ i := by
      by_contra hn
      exact (not_lt_of_ge ((ht i).2.2 (lt_of_not_ge hn))) hpos
    have hnonneg := (hs i).2.1 (hst.trans htτ)
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ i,
      lt_of_le_of_ne hnonneg (Ne.symm (hs i).1)⟩
  have heq := Finset.eq_of_subset_of_card_le hsub hcard.le
  intro i
  simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using
    (show i ∈ Finset.univ.filter (fun i => 0 < q i s) ↔
      i ∈ Finset.univ.filter (fun i => 0 < q i t) by rw [heq])

/-- The almost-everywhere version needed for the scalar derivatives of a
profile. No monotonicity of the label itself is assumed. -/
theorem exists_constant_positive_signs
    {I : Type*} [Fintype I] (q : I → ℝ → ℝ) (τ : I → ℝ)
    {a b : ℝ} (n : ℕ)
    (hnonzero : ∀ i, ∀ᵐ t ∂volume.restrict (Ioc a b), q i t ≠ 0)
    (hleft : ∀ i, ∀ᵐ t ∂volume.restrict (Ioc a (τ i)), 0 ≤ q i t)
    (hright : ∀ i, ∀ᵐ t ∂volume.restrict (Ioc (τ i) b), q i t ≤ 0)
    (hcard : ∀ᵐ t ∂volume.restrict (Ioc a b),
      (Finset.univ.filter (fun i => 0 < q i t)).card = n) :
    ∃ S : Finset I, ∀ᵐ t ∂volume.restrict (Ioc a b),
      ∀ i, (0 < q i t ↔ i ∈ S) := by
  classical
  let μ := volume.restrict (Ioc a b)
  have hsign (i : I) : ∀ᵐ t ∂μ,
      q i t ≠ 0 ∧ (t ≤ τ i → 0 ≤ q i t) ∧ (τ i < t → q i t ≤ 0) := by
    filter_upwards [hnonzero i, ae_restrict_mem measurableSet_Ioc,
      ae_restrict_of_ae (ae_imp_of_ae_restrict (hleft i)),
      ae_restrict_of_ae (ae_imp_of_ae_restrict (hright i))] with t ht hmem hl hr
    exact ⟨ht, fun h => hl ⟨hmem.1, h⟩, fun h => hr ⟨h, hmem.2⟩⟩
  have hgood : ∀ᵐ t ∂μ,
      (∀ i, q i t ≠ 0 ∧ (t ≤ τ i → 0 ≤ q i t) ∧ (τ i < t → q i t ≤ 0)) ∧
      (Finset.univ.filter (fun i => 0 < q i t)).card = n :=
    ((ae_all_iff).mpr hsign).and hcard
  by_cases hμ : μ = 0
  · refine ⟨∅, ?_⟩
    change ∀ᵐ t ∂μ, _
    rw [hμ]
    simp
  · have : NeZero μ := ⟨hμ⟩
    obtain ⟨s, hs⟩ := hgood.exists
    refine ⟨Finset.univ.filter (fun i => 0 < q i s), ?_⟩
    filter_upwards [hgood] with t ht
    have heq : ∀ i, 0 < q i s ↔ 0 < q i t := by
      rcases le_total s t with hst | hts
      · exact positive_signs_eq_of_ordered q τ hst hs.1 ht.1 (hs.2.trans ht.2.symm)
      · exact fun i => (positive_signs_eq_of_ordered q τ hts ht.1 hs.1
          (ht.2.trans hs.2.symm) i).symm
    intro i
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using (heq i).symm

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_TemplateVariationEquality
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finite_templateSymmetryGroup _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteRootOffsetConeIndex _root_.OAI.PolycyclicRecognition.instFiniteSubtypeLinearEquivRealIdMemSubgroupLinearSupportSymmetryGroup _root_.OAI.PolycyclicRecognition.instNonemptyRootOffsetConeIndex _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The segment-volume lower bound saturates every scalar variation bound -/

noncomputable section

namespace PolycyclicRecognition.SupportDatum

open MeasureTheory Set
open scoped BigOperators

variable {W I B : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [FiniteDimensional ℝ W] [Fintype I] [Fintype B] [Nonempty B]
  (D : PolycyclicRecognition.SupportDatum W I B)

/-- For a centered absolutely continuous profile, equality of its support
lower bound and derivative-speed upper bound forces every weight to exhaust
its positive variation at a maximizing time. The scalar integral identities
are the fundamental theorem of calculus data for the line restriction. -/
theorem exists_ordered_weight_signs
    (h : ℝ → W) (q : ℝ → W) (hc : Continuous h)
    {T c : ℝ} (hT : 0 ≤ T)
    (hq : ∀ i, IntervalIntegrable (fun t => D.weight i (q t)) volume 0 T)
    (hFTC : ∀ i t, t ∈ Icc 0 T →
      D.weight i (h t) = ∫ s in 0..t, D.weight i (q s))
    (hbound : ∀ b, ∀ᵐ t ∂volume.restrict (Icc 0 T), D.basisSupport b (q t) ≤ c)
    (hlower : T * c ≤ D.templateSupport (h '' Icc 0 T)) :
    ∃ τ : I → ℝ, (∀ i, τ i ∈ Icc 0 T) ∧
      (∀ i, D.weight i (h (τ i)) = D.weightSupport (h '' Icc 0 T) i) ∧
      (∀ i, ∀ᵐ t ∂volume.restrict (Ioc 0 (τ i)), 0 ≤ D.weight i (q t)) ∧
      (∀ i, ∀ᵐ t ∂volume.restrict (Ioc (τ i) T), D.weight i (q t) ≤ 0) := by
  classical
  let E := h '' Icc 0 T
  have hE : IsCompact E := isCompact_Icc.image hc
  have hne : E.Nonempty := (nonempty_Icc.mpr hT).image h
  have hp (i : I) : IntervalIntegrable (fun t => max (D.weight i (q t)) 0) volume 0 T :=
    ⟨(hq i).1.pos_part, (hq i).2.pos_part⟩
  have hweight (i : I) : D.weightSupport E i ≤
      ∫ t in 0..T, max (D.weight i (q t)) 0 := by
    obtain ⟨_, ⟨t, ht, rfl⟩, heq⟩ := D.exists_weightSupport_point hE hne i
    rw [heq, hFTC i t ht]
    have hqi := (hq i).mono_set (by
      rw [uIcc_of_le ht.1, uIcc_of_le hT]
      exact Icc_subset_Icc le_rfl ht.2)
    have hpi := (hp i).mono_set (by
      rw [uIcc_of_le ht.1, uIcc_of_le hT]
      exact Icc_subset_Icc le_rfl ht.2)
    exact (intervalIntegral.integral_mono ht.1 hqi hpi (fun _ => le_max_left _ _)).trans
      (intervalIntegral.integral_mono_interval le_rfl ht.1 ht.2
        (Filter.Eventually.of_forall (fun _ => le_max_right _ _)) (hp i))
  have hbupper (b : B) :
      (∑ i, (D.multiplicity b i : ℝ) *
        ∫ t in 0..T, max (D.weight i (q t)) 0) ≤ T * c := by
    have hbi : IntervalIntegrable (fun t => D.basisSupport b (q t)) volume 0 T := by
      convert IntervalIntegrable.sum Finset.univ
        (fun i _ => (hp i).const_mul (D.multiplicity b i : ℝ)) using 1
      all_goals try with_reducible_and_instances rfl
      ext t
      simp only [basisSupport, Finset.sum_apply, max_comm]
    have hsum : (∫ t in 0..T, D.basisSupport b (q t)) =
        ∑ i, (D.multiplicity b i : ℝ) * ∫ t in 0..T, max (D.weight i (q t)) 0 := by
      simp only [basisSupport, max_comm (0 : ℝ)]
      rw [intervalIntegral.integral_finsetSum (fun i _ =>
        (hp i).const_mul (D.multiplicity b i : ℝ))]
      simp only [intervalIntegral.integral_const_mul]
    rw [← hsum]
    have hh := intervalIntegral.integral_mono_ae_restrict hT hbi
      (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => c) volume 0 T) (hbound b)
    simpa only [intervalIntegral.integral_const, sub_zero, smul_eq_mul] using hh
  obtain ⟨b, _, hb⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty
    (D.basisTemplateSupport E)
  have hb' : D.templateSupport E = D.basisTemplateSupport E b := hb
  have hsumzero : (∑ i, (D.multiplicity b i : ℝ) *
      ((∫ t in 0..T, max (D.weight i (q t)) 0) - D.weightSupport E i)) = 0 := by
    have hnonneg : 0 ≤ ∑ i, (D.multiplicity b i : ℝ) *
        ((∫ t in 0..T, max (D.weight i (q t)) 0) - D.weightSupport E i) :=
      Finset.sum_nonneg (fun i _ => mul_nonneg (Nat.cast_nonneg _) (sub_nonneg.mpr (hweight i)))
    have hsumle := hbupper b
    change T * c ≤ D.templateSupport E at hlower
    rw [hb'] at hlower
    simp only [mul_sub, Finset.sum_sub_distrib] at hnonneg ⊢
    unfold basisTemplateSupport at hlower
    exact le_antisymm (by linarith) hnonneg
  have hsaturated (i : I) : D.weightSupport E i =
      ∫ t in 0..T, max (D.weight i (q t)) 0 := by
    have hterm := Finset.single_le_sum (s := Finset.univ) (a := i)
      (f := fun j => (D.multiplicity b j : ℝ) *
        ((∫ t in 0..T, max (D.weight j (q t)) 0) - D.weightSupport E j))
      (fun j _ => mul_nonneg (Nat.cast_nonneg _) (sub_nonneg.mpr (hweight j)))
      (Finset.mem_univ i)
    rw [hsumzero] at hterm
    have hpos : (0 : ℝ) < D.multiplicity b i := Nat.cast_pos.mpr (D.positive b i)
    nlinarith [hweight i]
  have hmax (i : I) : ∃ t ∈ Icc 0 T,
      D.weight i (h t) = D.weightSupport E i := by
    obtain ⟨_, ⟨t, ht, rfl⟩, heq⟩ := D.exists_weightSupport_point hE hne i
    exact ⟨t, ht, heq.symm⟩
  choose τ hτ hτmax using hmax
  refine ⟨τ, hτ, hτmax, ?_, ?_⟩
  · intro i
    exact (positive_variation_equality_signs (fun t => D.weight i (q t))
      (hτ i).1 (hτ i).2 (hq i) (by
        rw [← hFTC i (τ i) (hτ i), hτmax i, hsaturated i])).1
  · intro i
    exact (positive_variation_equality_signs (fun t => D.weight i (q t))
      (hτ i).1 (hτ i).2 (hq i) (by
        rw [← hFTC i (τ i) (hτ i), hτmax i, hsaturated i])).2

end PolycyclicRecognition.SupportDatum

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_WeightRayPermutation
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Permutations and sign counts of distinct positive weight rays -/

noncomputable section

namespace PolycyclicRecognition

variable {W I : Type*} [AddCommGroup W] [Module ℝ W] [Fintype I]

/-- Pullback preserving a finite family of distinct positive rays acts by a
permutation. Distinctness is on rays, not on a possibly repeated generator list. -/
theorem exists_weight_ray_permutation
    (α : I → W →ₗ[ℝ] ℝ) (A : W ≃ₗ[ℝ] W)
    (hdistinct : ∀ i j (r : ℝ), 0 < r → α i = r • α j → i = j)
    (hmaps : ∀ i, ∃ (j : I) (r : ℝ), 0 < r ∧ (α i).comp A.toLinearMap = r • α j) :
    ∃ σ : I ≃ I, ∃ r : I → ℝ, (∀ i, 0 < r i) ∧
      ∀ i, (α i).comp A.toLinearMap = r i • α (σ i) := by
  classical
  choose j r hr heq using hmaps
  have hj : Function.Injective j := by
    intro i k hik
    apply hdistinct i k (r i / r k) (div_pos (hr i) (hr k))
    ext x
    have hi := LinearMap.congr_fun (heq i) (A.symm x)
    have hk := LinearMap.congr_fun (heq k) (A.symm x)
    change α i (A (A.symm x)) = r i * α (j i) (A.symm x) at hi
    change α k (A (A.symm x)) = r k * α (j k) (A.symm x) at hk
    simp only [A.apply_symm_apply] at hi hk
    change α i x = (r i / r k) * α k x
    rw [hik] at hi
    rw [hi, hk]
    field_simp [(hr k).ne']
  let σ : I ≃ I := Equiv.ofBijective j ⟨hj, Finite.surjective_of_injective hj⟩
  exact ⟨σ, r, hr, heq⟩

/-- A ray permutation preserves the number of positive weights at every
vector. This supplies the fixed-count input of the line-sign argument. -/
theorem positive_weight_count_of_ray_permutation
    (α : I → W →ₗ[ℝ] ℝ) (A : W ≃ₗ[ℝ] W) (σ : I ≃ I) (r : I → ℝ)
    (hr : ∀ i, 0 < r i)
    (heq : ∀ i, (α i).comp A.toLinearMap = r i • α (σ i)) (w : W) :
    (Finset.univ.filter (fun i => 0 < α i (A w))).card =
      (Finset.univ.filter (fun i => 0 < α i w)).card := by
  classical
  apply Finset.card_equiv σ
  intro i
  have hi := LinearMap.congr_fun (heq i) w
  change α i (A w) = r i * α (σ i) w at hi
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [hi]
  exact mul_pos_iff_of_pos_left (hr i)

omit [Fintype I] in
/-- Genericity is also preserved by the same positive ray permutation. -/
theorem nonzero_weights_of_ray_permutation
    (α : I → W →ₗ[ℝ] ℝ) (A : W ≃ₗ[ℝ] W) (σ : I ≃ I) (r : I → ℝ)
    (hr : ∀ i, 0 < r i)
    (heq : ∀ i, (α i).comp A.toLinearMap = r i • α (σ i))
    (w : W) (hw : ∀ i, α i w ≠ 0) : ∀ i, α i (A w) ≠ 0 := by
  intro i
  have hi := LinearMap.congr_fun (heq i) w
  change α i (A w) = r i * α (σ i) w at hi
  rw [hi]
  exact mul_ne_zero (hr i).ne' (hw (σ i))

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_NormalizedWeightRays
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Deduplicating positive weight rays

Unit normalization gives a concrete finite set of positive rays, even when
the original generator list repeats some rays with different multiplicities.
-/

noncomputable section

namespace PolycyclicRecognition

open Set

variable {W I : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [Fintype I]

theorem norm_normalizedWeight (φ : W →L[ℝ] ℝ) (hφ : φ ≠ 0) :
    ‖normalizedWeight φ‖ = 1 := by
  simp [normalizedWeight, norm_smul, norm_ne_zero_iff.mpr hφ]

theorem normalizedWeight_pos_iff (φ : W →L[ℝ] ℝ) (hφ : φ ≠ 0) (w : W) :
    0 < normalizedWeight φ w ↔ 0 < φ w := by
  change 0 < ‖φ‖⁻¹ * φ w ↔ _
  exact mul_pos_iff_of_pos_left (inv_pos.mpr (norm_pos_iff.mpr hφ))

omit [Fintype I] in
theorem normalizedWeightRays_distinct (α : I → W →L[ℝ] ℝ) (hα : ∀ i, α i ≠ 0)
    (x y : NormalizedWeightRays α) (r : ℝ) (hr : 0 < r)
    (heq : x.val.toLinearMap = r • y.val.toLinearMap) : x = y := by
  have hx : ‖x.val‖ = 1 := by
    obtain ⟨i, hi⟩ := x.property
    rw [← hi]
    exact norm_normalizedWeight _ (hα i)
  have hy : ‖y.val‖ = 1 := by
    obtain ⟨i, hi⟩ := y.property
    rw [← hi]
    exact norm_normalizedWeight _ (hα i)
  have heq' : x.val = r • y.val := by
    ext w
    exact LinearMap.congr_fun heq w
  have hnorm := congrArg norm heq'
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr, hx, hy, mul_one] at hnorm
  apply Subtype.ext
  simpa only [← hnorm, one_smul] using heq'

/-- A pullback on the original weights induces a permutation of the actual
distinct rays, independently of duplicate generator weights. -/
theorem exists_normalizedWeightRays_permutation
    (α : I → W →L[ℝ] ℝ) (hα : ∀ i, α i ≠ 0) (A : W ≃ₗ[ℝ] W)
    (hmaps : ∀ i, ∃ (j : I) (r : ℝ), 0 < r ∧
      (α i).toLinearMap.comp A.toLinearMap = r • (α j).toLinearMap) :
    ∃ σ : NormalizedWeightRays α ≃ NormalizedWeightRays α,
      ∃ r : NormalizedWeightRays α → ℝ, (∀ x, 0 < r x) ∧
        ∀ x, x.val.toLinearMap.comp A.toLinearMap = r x • (σ x).val.toLinearMap := by
  let : Fintype (NormalizedWeightRays α) := Fintype.ofFinite _
  apply exists_weight_ray_permutation (fun x : NormalizedWeightRays α => x.val.toLinearMap)
    A (normalizedWeightRays_distinct α hα)
  intro x
  obtain ⟨i, hi⟩ := x.property
  obtain ⟨j, r, hr, hij⟩ := hmaps i
  let y : NormalizedWeightRays α := ⟨normalizedWeight (α j), ⟨j, rfl⟩⟩
  refine ⟨y, ‖α i‖⁻¹ * r * ‖α j‖, ?_, ?_⟩
  · exact mul_pos (mul_pos (inv_pos.mpr (norm_pos_iff.mpr (hα i))) hr)
      (norm_pos_iff.mpr (hα j))
  · ext w
    have hh := LinearMap.congr_fun hij w
    change α i (A w) = r * α j w at hh
    change x.val (A w) = (‖α i‖⁻¹ * r * ‖α j‖) * y.val w
    rw [← hi]
    change ‖α i‖⁻¹ * α i (A w) =
      (‖α i‖⁻¹ * r * ‖α j‖) * (‖α j‖⁻¹ * α j w)
    rw [hh]
    field_simp [norm_ne_zero_iff.mpr (hα j)]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_SupportDirectionCap
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instNonemptyBases _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_nonempty _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Separating one unsupported direction by a small cap

The cap preserves all the supports in a finite list of directions and
strictly lowers support in a direction outside their positive rays.
-/

noncomputable section

namespace PolycyclicRecognition

open Set

variable {W I : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
  [FiniteDimensional ℝ W] [Fintype I]

/-- A compact convex truncation of the unit ball leaves the prescribed
support values unchanged but strictly lowers support in any additional
direction not on their positive rays. -/
theorem exists_support_direction_cap (v : I → W) (b : W) (hb : b ≠ 0)
    (hnot : ∀ i (r : ℝ), 0 < r → b ≠ r • v i) :
    ∃ E : Set W, IsCompact E ∧ E.Nonempty ∧ Convex ℝ E ∧
      E ⊆ Metric.closedBall 0 1 ∧
      (∀ i, ∃ x ∈ E, inner ℝ (v i) x = ‖v i‖) ∧
      ∃ c : ℝ, c < ‖b‖ ∧ ∀ x ∈ E, inner ℝ b x ≤ c := by
  classical
  let u : I → W := fun i => ‖v i‖⁻¹ • v i
  have hunorm (i : I) : ‖u i‖ ≤ 1 := by
    by_cases hv : v i = 0
    · simp [u, hv]
    · have hvn : ‖v i‖ ≠ 0 := norm_ne_zero_iff.mpr hv
      simp [u, norm_smul, hvn]
  have huinner (i : I) : inner ℝ (v i) (u i) = ‖v i‖ := by
    by_cases hv : v i = 0
    · simp [u, hv]
    · have hvn : ‖v i‖ ≠ 0 := norm_ne_zero_iff.mpr hv
      simp only [u, real_inner_smul_right, real_inner_self_eq_norm_sq]
      field_simp
  have hult (i : I) : inner ℝ b (u i) < ‖b‖ := by
    by_cases hv : v i = 0
    · simpa [u, hv] using norm_pos_iff.mpr hb
    · have hvn : ‖v i‖ ≠ 0 := norm_ne_zero_iff.mpr hv
      have hunit : ‖u i‖ = 1 := by
        simp [u, norm_smul, hvn]
      have hne : ‖u i‖ • b ≠ ‖b‖ • u i := by
        intro heq
        have heq' : b = (‖b‖ / ‖v i‖) • v i := by
          simpa only [hunit, one_smul, u, smul_smul, div_eq_mul_inv] using heq
        exact hnot i (‖b‖ / ‖v i‖)
          (div_pos (norm_pos_iff.mpr hb) (norm_pos_iff.mpr hv)) heq'
      simpa only [hunit, mul_one] using (inner_lt_norm_mul_iff_real.mpr hne)
  let x : Option I → W := fun i => i.elim 0 u
  let c : ℝ := Finset.univ.sup' Finset.univ_nonempty (fun i : Option I => inner ℝ b (x i))
  have hc0 : 0 ≤ c := by
    have hh := Finset.le_sup' (f := fun i : Option I => inner ℝ b (x i))
      (Finset.mem_univ none)
    simpa only [x, Option.elim_none, inner_zero_right] using hh
  have hcb : c < ‖b‖ := by
    rw [Finset.sup'_lt_iff]
    intro i _
    cases i with
    | none => simpa only [x, Option.elim_none, inner_zero_right] using norm_pos_iff.mpr hb
    | some i => exact hult i
  let E := Metric.closedBall (0 : W) 1 ∩ {y : W | inner ℝ b y ≤ c}
  have hclosed : IsClosed {y : W | inner ℝ b y ≤ c} :=
    isClosed_le (continuous_const.inner continuous_id) continuous_const
  have hcompact : IsCompact E := (isCompact_closedBall (0 : W) 1).inter_right hclosed
  have hconvex : Convex ℝ E := (convex_closedBall (0 : W) 1).inter
    (convex_halfSpace_le (innerSL ℝ b).toLinearMap.isLinear c)
  refine ⟨E, hcompact, ⟨0, ?_⟩, hconvex, inter_subset_left, ?_, c, hcb, ?_⟩
  · exact ⟨by simp, by simpa using hc0⟩
  · intro i
    refine ⟨u i, ⟨?_, ?_⟩, huinner i⟩
    · simpa only [Metric.mem_closedBall, dist_zero_right] using hunorm i
    · exact Finset.le_sup' (f := fun j : Option I => inner ℝ b (x j))
        (Finset.mem_univ (some i))
  · exact fun _ hy => hy.2

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_TemplateSupportOrder
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finite_templateSymmetryGroup _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteRootOffsetConeIndex _root_.OAI.PolycyclicRecognition.instFiniteSubtypeLinearEquivRealIdMemSubgroupLinearSupportSymmetryGroup _root_.OAI.PolycyclicRecognition.instNonemptyRootOffsetConeIndex _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Monotonicity and strictness of the weighted template support -/

noncomputable section

namespace PolycyclicRecognition.SupportDatum

open Set
open scoped BigOperators

variable {W I B : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [FiniteDimensional ℝ W] [Fintype I] [Fintype B] [Nonempty B]
  (D : PolycyclicRecognition.SupportDatum W I B)

omit [Nonempty B] in
theorem weightSupport_eq_of_bound_and_attained {E : Set W} (hc : IsCompact E)
    (i : I) (r : ℝ) (hbound : ∀ x ∈ E, D.weight i x ≤ r)
    (hattained : ∃ x ∈ E, D.weight i x = r) : D.weightSupport E i = r := by
  obtain ⟨x, hx, heq⟩ := hattained
  apply le_antisymm
  · obtain ⟨y, hy, hsup⟩ := D.exists_weightSupport_point hc ⟨x, hx⟩ i
    rw [hsup]
    exact hbound y hy
  · rw [← heq]
    exact D.weight_le_weightSupport hc hx i

omit [Nonempty B] in
theorem weightSupport_mono {E F : Set W} (hE : IsCompact E) (hn : E.Nonempty)
    (hF : IsCompact F) (hEF : E ⊆ F) (i : I) :
    D.weightSupport E i ≤ D.weightSupport F i := by
  obtain ⟨x, hx, heq⟩ := D.exists_weightSupport_point hE hn i
  rw [heq]
  exact D.weight_le_weightSupport hF (hEF hx) i

omit [FiniteDimensional ℝ W] in
/-- Every word basis contains every generator with positive multiplicity,
so decreasing one support strictly decreases the entire finite maximum. -/
theorem templateSupport_lt_of_weightSupport {E F : Set W}
    (hle : ∀ i, D.weightSupport E i ≤ D.weightSupport F i)
    (hlt : ∃ i, D.weightSupport E i < D.weightSupport F i) :
    D.templateSupport E < D.templateSupport F := by
  obtain ⟨b, _, hb⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty
    (D.basisTemplateSupport E)
  change Finset.univ.sup' _ _ < _
  rw [hb]
  apply lt_of_lt_of_le _ (D.basisTemplateSupport_le F b)
  unfold basisTemplateSupport
  apply Finset.sum_lt_sum
  · intro i _
    exact mul_le_mul_of_nonneg_left (hle i) (Nat.cast_nonneg _)
  · obtain ⟨i, hi⟩ := hlt
    exact ⟨i, Finset.mem_univ i,
      mul_lt_mul_of_pos_left hi (Nat.cast_pos.mpr (D.positive b i))⟩

end PolycyclicRecognition.SupportDatum

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_TemplateWeightRays
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteRootOffsetConeIndex _root_.OAI.PolycyclicRecognition.instNonemptyRootOffsetConeIndex _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.CartanWordModel.supportDatum_weight _root_.OAI.PolycyclicRecognition.SupportDatum.transport_weight_apply _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Template symmetries preserve the positive generator-weight rays -/

noncomputable section

namespace PolycyclicRecognition

open Set

variable {W I B : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
  [FiniteDimensional ℝ W] [Fintype I] [Fintype B] [Nonempty B]

/-- The cap argument from the support-symmetries lemma: pullback of every
nonzero generator weight is a positive multiple of another generator weight.
It uses preservation of all compact convex templates, not only segments. -/
theorem templateSymmetry_weight_ray
    (D : SupportDatum W I B) (A : templateSymmetryGroup D)
    (j : I) (hj : D.weight j ≠ 0) :
    ∃ (i : I) (r : ℝ), 0 < r ∧ (D.weight j).comp A.val.toLinearMap = r • D.weight i := by
  classical
  let v : I → W := fun i => (InnerProductSpace.toDual ℝ W).symm
    (D.weight i).toContinuousLinearMap
  let β : W →ₗ[ℝ] ℝ := (D.weight j).comp A.val.toLinearMap
  let b : W := (InnerProductSpace.toDual ℝ W).symm β.toContinuousLinearMap
  have hv (i : I) (x : W) : inner ℝ (v i) x = D.weight i x :=
    InnerProductSpace.toDual_symm_apply
  have hbval (x : W) : inner ℝ b x = D.weight j (A.val x) :=
    InnerProductSpace.toDual_symm_apply
  have hb : b ≠ 0 := by
    intro hb
    apply hj
    ext x
    have hh := hbval (A.val.symm x)
    simpa only [hb, inner_zero_left, LinearEquiv.apply_symm_apply, LinearMap.zero_apply]
      using hh.symm
  by_contra hn
  have hnot : ∀ i (r : ℝ), 0 < r → b ≠ r • v i := by
    intro i r hr heq
    apply hn
    refine ⟨i, r, hr, ?_⟩
    ext x
    change D.weight j (A.val x) = r * D.weight i x
    rw [← hbval, heq, real_inner_smul_left, hv]
  obtain ⟨E, hE, hne, hconv, hEK, hreach, c, hcb, hcap⟩ :=
    exists_support_direction_cap v b hb hnot
  let K := Metric.closedBall (0 : W) 1
  have hK : IsCompact K := isCompact_closedBall 0 1
  have hKne : K.Nonempty := ⟨0, by simp [K]⟩
  have hbound (i : I) (x : W) (hx : x ∈ K) : D.weight i x ≤ ‖v i‖ := by
    have hx' : ‖x‖ ≤ 1 := by simpa only [K, Metric.mem_closedBall, dist_zero_right] using hx
    rw [← hv]
    exact (real_inner_le_norm _ _).trans (by nlinarith [norm_nonneg (v i)])
  have hsupp (i : I) : D.weightSupport E i = D.weightSupport K i := by
    obtain ⟨x, hx, heq⟩ := hreach i
    have heq' : D.weight i x = ‖v i‖ := by rwa [hv] at heq
    have hsE := D.weightSupport_eq_of_bound_and_attained hE i ‖v i‖
      (fun y hy => hbound i y (hEK hy)) ⟨x, hx, heq'⟩
    have hsK := D.weightSupport_eq_of_bound_and_attained hK i ‖v i‖
      (hbound i) ⟨x, hEK hx, heq'⟩
    exact hsE.trans hsK.symm
  have hPE : D.templateSupport E = D.templateSupport K := by
    unfold SupportDatum.templateSupport
    congr 1
    funext k
    simp only [SupportDatum.basisTemplateSupport, hsupp]
  have hAE : IsCompact (A.val '' E) := hE.image A.val.continuous_of_finiteDimensional
  have hAK : IsCompact (A.val '' K) := hK.image A.val.continuous_of_finiteDimensional
  have hAEne : (A.val '' E).Nonempty := hne.image A.val
  have hle (i : I) : D.weightSupport (A.val '' E) i ≤ D.weightSupport (A.val '' K) i :=
    D.weightSupport_mono hAE hAEne hAK (image_mono hEK) i
  have hjE : D.weightSupport (A.val '' E) j ≤ c := by
    obtain ⟨_, ⟨x, hx, rfl⟩, heq⟩ := D.exists_weightSupport_point hAE hAEne j
    rw [heq, ← hbval]
    exact hcap x hx
  let u : W := ‖b‖⁻¹ • b
  have hbn : ‖b‖ ≠ 0 := norm_ne_zero_iff.mpr hb
  have huK : u ∈ K := by
    simp [u, K, Metric.mem_closedBall, dist_zero_right, norm_smul, hbn]
  have hbu : inner ℝ b u = ‖b‖ := by
    simp only [u, real_inner_smul_right, real_inner_self_eq_norm_sq]
    field_simp
  have hjK : ‖b‖ ≤ D.weightSupport (A.val '' K) j := by
    have hh := D.weight_le_weightSupport hAK (mem_image_of_mem A.val huK) j
    rw [← hbval, hbu] at hh
    exact hh
  have hstrict := D.templateSupport_lt_of_weightSupport hle
    ⟨j, hjE.trans_lt (hcb.trans_le hjK)⟩
  rw [A.property E hE hne hconv,
    A.property K hK hKne (convex_closedBall (0 : W) 1), hPE] at hstrict
  exact lt_irrefl _ hstrict

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_GenericProfileSigns
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteRootOffsetConeIndex _root_.OAI.PolycyclicRecognition.instNonemptyRootOffsetConeIndex _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Constant generic line signs from the actual template label action -/

noncomputable section

namespace PolycyclicRecognition.SupportDatum

open MeasureTheory Set Filter

/-- Duplicate generator rays are normalized and removed before counting
positive signs. Thus the constant-count step follows from the actual template
symmetry action, rather than being a new hypothesis on the profile. -/
theorem generic_profile_signs_constant
    {W I B : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    [FiniteDimensional ℝ W] [Fintype I] [Fintype B] [Nonempty B]
    (D : PolycyclicRecognition.SupportDatum W I B)
    (hweights : ∀ i, D.weight i ≠ 0)
    (h q : ℝ → W) (hc : Continuous h) (w : W) (hw : ∀ i, D.weight i w ≠ 0)
    {T : ℝ} (hT : 0 ≤ T)
    (hq : ∀ i, IntervalIntegrable (fun t => D.weight i (q t)) volume 0 T)
    (hFTC : ∀ i t, t ∈ Icc 0 T →
      D.weight i (h t) = ∫ s in 0..t, D.weight i (q s))
    (label : ℝ → templateSymmetryGroup D)
    (hlabel : ∀ᵐ t ∂volume.restrict (Icc 0 T), q t = (label t).val w)
    (hlower : T * D.segmentSupport w ≤ D.templateSupport (h '' Icc 0 T)) :
    ∃ S : Finset I, ∀ᵐ t ∂volume.restrict (Ioc 0 T),
      ∀ i, (0 < D.weight i (q t) ↔ i ∈ S) := by
  classical
  let α : I → W →L[ℝ] ℝ := fun i => (D.weight i).toContinuousLinearMap
  have hα (i : I) : α i ≠ 0 := by
    intro hi
    apply hweights i
    ext x
    exact congrArg (fun f : W →L[ℝ] ℝ => f x) hi
  let R := NormalizedWeightRays α
  let : Fintype R := Fintype.ofFinite _
  let β : R → W →ₗ[ℝ] ℝ := fun x => x.val.toLinearMap
  have hperm (A : templateSymmetryGroup D) : ∃ σ : R ≃ R, ∃ r : R → ℝ,
      (∀ x, 0 < r x) ∧ ∀ x, (β x).comp A.val.toLinearMap = r x • β (σ x) := by
    exact exists_normalizedWeightRays_permutation α hα A.val
      (fun i => templateSymmetry_weight_ray D A i (hweights i))
  have hgeneric (x : R) : β x w ≠ 0 := by
    obtain ⟨i, hi⟩ := x.property
    change x.val w ≠ 0
    rw [← hi]
    change ‖α i‖⁻¹ * α i w ≠ 0
    exact mul_ne_zero (inv_ne_zero (norm_ne_zero_iff.mpr (hα i))) (hw i)
  have hnonzero (A : templateSymmetryGroup D) : ∀ x, β x (A.val w) ≠ 0 := by
    obtain ⟨σ, r, hr, heq⟩ := hperm A
    exact nonzero_weights_of_ray_permutation β A.val σ r hr heq w hgeneric
  have hcount (A : templateSymmetryGroup D) :
      (Finset.univ.filter (fun x => 0 < β x (A.val w))).card =
        (Finset.univ.filter (fun x => 0 < β x w)).card := by
    obtain ⟨σ, r, hr, heq⟩ := hperm A
    exact positive_weight_count_of_ray_permutation β A.val σ r hr heq w
  have hbound (b : B) : ∀ᵐ t ∂volume.restrict (Icc 0 T),
      D.basisSupport b (q t) ≤ D.segmentSupport w := by
    filter_upwards [hlabel] with t ht
    rw [ht]
    exact (D.basisSupport_le b _).trans_eq
      (templateSymmetry_mem_linearSupportSymmetry D (label t) w)
  obtain ⟨τ, _, _, hleft, hright⟩ :=
    D.exists_ordered_weight_signs h q hc hT hq hFTC hbound hlower
  have hrep (x : R) : ∃ i, x.val = normalizedWeight (α i) := by
    obtain ⟨i, hi⟩ := x.property
    exact ⟨i, hi.symm⟩
  choose rep hrep using hrep
  let θ : R → ℝ := fun x => τ (rep x)
  have hleftR (x : R) : ∀ᵐ t ∂volume.restrict (Ioc 0 (θ x)), 0 ≤ β x (q t) := by
    filter_upwards [hleft (rep x)] with t ht
    change 0 ≤ x.val (q t)
    rw [hrep x]
    exact mul_nonneg (inv_nonneg.mpr (norm_nonneg _)) ht
  have hrightR (x : R) : ∀ᵐ t ∂volume.restrict (Ioc (θ x) T), β x (q t) ≤ 0 := by
    filter_upwards [hright (rep x)] with t ht
    change x.val (q t) ≤ 0
    rw [hrep x]
    exact mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr (norm_nonneg _)) ht
  have hlabel' : ∀ᵐ t ∂volume.restrict (Ioc 0 T), q t = (label t).val w :=
    hlabel.filter_mono (ae_mono (Measure.restrict_mono Ioc_subset_Icc_self le_rfl))
  have hnonzeroR (x : R) : ∀ᵐ t ∂volume.restrict (Ioc 0 T), β x (q t) ≠ 0 := by
    filter_upwards [hlabel'] with t ht
    rw [ht]
    exact hnonzero (label t) x
  have hcountR : ∀ᵐ t ∂volume.restrict (Ioc 0 T),
      (Finset.univ.filter (fun x => 0 < β x (q t))).card =
        (Finset.univ.filter (fun x => 0 < β x w)).card := by
    filter_upwards [hlabel'] with t ht
    rw [ht]
    exact hcount (label t)
  obtain ⟨S, hS⟩ := exists_constant_positive_signs (fun x t => β x (q t)) θ
    (Finset.univ.filter (fun x => 0 < β x w)).card hnonzeroR hleftR hrightR hcountR
  let ray (i : I) : R := ⟨normalizedWeight (α i), ⟨i, rfl⟩⟩
  refine ⟨Finset.univ.filter (fun i => ray i ∈ S), ?_⟩
  filter_upwards [hS] with t ht
  intro i
  have hi := ht (ray i)
  change 0 < normalizedWeight (α i) (q t) ↔ ray i ∈ S at hi
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  change 0 < α i (q t) ↔ ray i ∈ S
  exact (normalizedWeight_pos_iff (α i) (hα i) (q t)).symm.trans hi

end PolycyclicRecognition.SupportDatum

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_WeightChamberAction
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # From weight-sign agreement to chamber-image agreement -/

noncomputable section

namespace PolycyclicRecognition

open Set

variable {W I : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]

theorem generic_of_mem_weightChamber (α : I → W →L[ℝ] ℝ)
    {σ : I → Bool} {w : W} (hw : w ∈ weightChamber α σ) : ∀ i, α i w ≠ 0 := by
  intro i hi
  have hh := hw i
  cases hs : σ i <;> simp [orientedWeight, hs, hi] at hh

theorem weightSigns_eq_of_mem_chamber (α : I → W →L[ℝ] ℝ)
    {σ : I → Bool} {w : W} (hw : w ∈ weightChamber α σ) : weightSigns α w = σ := by
  funext i
  have hh := hw i
  cases hs : σ i with
  | false =>
    have hn : α i w < 0 := by simpa [orientedWeight, hs] using hh
    simp [weightSigns, not_lt.mpr hn.le]
  | true =>
    have hp : 0 < α i w := by simpa [orientedWeight, hs] using hh
    simp [weightSigns, hp]

theorem mem_weightChamber_signs_iff (α : I → W →L[ℝ] ℝ) {w x : W}
    (hw : ∀ i, α i w ≠ 0) :
    x ∈ weightChamber α (weightSigns α w) ↔ ∀ i, 0 < α i x * α i w := by
  constructor
  · intro hx i
    have hi := hx i
    by_cases hp : 0 < α i w
    · have hxi : 0 < α i x := by simpa [orientedWeight, weightSigns, hp] using hi
      exact mul_pos hxi hp
    · have hn : α i w < 0 := lt_of_le_of_ne (le_of_not_gt hp) (hw i)
      have hxi : α i x < 0 := by simpa [orientedWeight, weightSigns, hp] using hi
      exact mul_pos_of_neg_of_neg hxi hn
  · intro hx i
    by_cases hp : 0 < α i w
    · have hxi : 0 < α i x := by nlinarith [hx i]
      simpa [orientedWeight, weightSigns, hp] using hxi
    · have hn : α i w < 0 := lt_of_le_of_ne (le_of_not_gt hp) (hw i)
      have hxi : α i x < 0 := by nlinarith [hx i]
      simpa [orientedWeight, weightSigns, hp] using hxi

theorem positive_weight_products_map (α : I → W →L[ℝ] ℝ) (A : W ≃ₗ[ℝ] W)
    (hA : PreservesPositiveWeightRays α A) {x w : W}
    (h : ∀ i, 0 < α i x * α i w) : ∀ i, 0 < α i (A x) * α i (A w) := by
  intro i
  obtain ⟨j, r, hr, he⟩ := hA i
  have hx := LinearMap.congr_fun he x
  have hw := LinearMap.congr_fun he w
  change α i (A x) = r * α j x at hx
  change α i (A w) = r * α j w at hw
  rw [hx, hw]
  have hp := mul_pos (mul_pos hr hr) (h j)
  nlinarith only [hp]

theorem generic_weights_map (α : I → W →L[ℝ] ℝ) (A : W ≃ₗ[ℝ] W)
    (hA : PreservesPositiveWeightRays α A) {w : W} (hw : ∀ i, α i w ≠ 0) :
    ∀ i, α i (A w) ≠ 0 := by
  intro i
  obtain ⟨j, r, hr, he⟩ := hA i
  have hh := LinearMap.congr_fun he w
  change α i (A w) = r * α j w at hh
  rw [hh]
  exact mul_ne_zero hr.ne' (hw j)

theorem image_weightChamber (α : I → W →L[ℝ] ℝ) (A : W ≃ₗ[ℝ] W)
    (hA : PreservesPositiveWeightRays α A) (hAi : PreservesPositiveWeightRays α A.symm)
    {w : W} (hw : ∀ i, α i w ≠ 0) :
    A '' weightChamber α (weightSigns α w) =
      weightChamber α (weightSigns α (A w)) := by
  have haw := generic_weights_map α A hA hw
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (mem_weightChamber_signs_iff α haw).mpr
      (positive_weight_products_map α A hA ((mem_weightChamber_signs_iff α hw).mp hx))
  · intro hy
    refine ⟨A.symm y, ?_, A.apply_symm_apply y⟩
    apply (mem_weightChamber_signs_iff α hw).mpr
    have hh := positive_weight_products_map α A.symm hAi
      ((mem_weightChamber_signs_iff α haw).mp hy)
    simpa only [A.symm_apply_apply] using hh

variable [FiniteDimensional ℝ W]

theorem image_closedWeightChamber (α : I → W →L[ℝ] ℝ) (A : W ≃ₗ[ℝ] W)
    (hA : PreservesPositiveWeightRays α A) (hAi : PreservesPositiveWeightRays α A.symm)
    {w : W} (hw : ∀ i, α i w ≠ 0) :
    A '' closedWeightChamber α (weightSigns α w) =
      closedWeightChamber α (weightSigns α (A w)) := by
  have hmem : w ∈ weightChamber α (weightSigns α w) :=
    (mem_weightChamber_signs_iff α hw).mpr (fun i => mul_self_pos.mpr (hw i))
  have haw := generic_weights_map α A hA hw
  have hmemA : A w ∈ weightChamber α (weightSigns α (A w)) :=
    (mem_weightChamber_signs_iff α haw).mpr (fun i => mul_self_pos.mpr (haw i))
  rw [← closure_weightChamber α _ ⟨w, hmem⟩,
    ← closure_weightChamber α _ ⟨A w, hmemA⟩]
  have he := A.toContinuousLinearEquiv.toHomeomorph.image_closure
    (weightChamber α (weightSigns α w))
  change A '' closure (weightChamber α (weightSigns α w)) =
    closure (A '' weightChamber α (weightSigns α w)) at he
  rw [he, image_weightChamber α A hA hAi hw]

/-- Equal signs on one generic direction identify the full chamber images. -/
theorem image_closedWeightChamber_eq_of_signs
    (α : I → W →L[ℝ] ℝ) (A B : W ≃ₗ[ℝ] W)
    (hA : PreservesPositiveWeightRays α A) (hAi : PreservesPositiveWeightRays α A.symm)
    (hB : PreservesPositiveWeightRays α B) (hBi : PreservesPositiveWeightRays α B.symm)
    {w : W} (hw : ∀ i, α i w ≠ 0)
    (hsign : ∀ i, 0 < α i (A w) ↔ 0 < α i (B w)) :
    A '' closedWeightChamber α (weightSigns α w) =
      B '' closedWeightChamber α (weightSigns α w) := by
  rw [image_closedWeightChamber α A hA hAi hw, image_closedWeightChamber α B hB hBi hw]
  congr 1
  funext i
  simp only [weightSigns, hsign i]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_GenericProfileChambers
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteRootOffsetConeIndex _root_.OAI.PolycyclicRecognition.instNonemptyRootOffsetConeIndex _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Generic profile lines have one image chamber

The scalar variation equalities give constant signs. Positive weight-ray
preservation, for a template symmetry and its inverse, upgrades those signs
to agreement of the entire image of the closed chamber.
-/

noncomputable section

namespace PolycyclicRecognition.SupportDatum

open MeasureTheory Set Filter

variable {W I B : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
  [FiniteDimensional ℝ W] [Fintype I] [Fintype B] [Nonempty B]

theorem templateSymmetry_preservesPositiveWeightRays
    (D : SupportDatum W I B) (hweights : ∀ i, D.weight i ≠ 0)
    (A : templateSymmetryGroup D) :
    PreservesPositiveWeightRays (fun i => (D.weight i).toContinuousLinearMap) A.val := by
  intro i
  exact templateSymmetry_weight_ray D A i (hweights i)

theorem generic_profile_chamber_agreement
    (D : SupportDatum W I B) (hweights : ∀ i, D.weight i ≠ 0)
    (h q : ℝ → W) (hc : Continuous h) (w : W) (hw : ∀ i, D.weight i w ≠ 0)
    {T : ℝ} (hT : 0 ≤ T)
    (hq : ∀ i, IntervalIntegrable (fun t => D.weight i (q t)) volume 0 T)
    (hFTC : ∀ i t, t ∈ Icc 0 T →
      D.weight i (h t) = ∫ s in 0..t, D.weight i (q s))
    (label : ℝ → templateSymmetryGroup D)
    (hlabel : ∀ᵐ t ∂volume.restrict (Icc 0 T), q t = (label t).val w)
    (hlower : T * D.segmentSupport w ≤ D.templateSupport (h '' Icc 0 T)) :
    ∀ᵐ s ∂volume.restrict (Ioc 0 T), ∀ᵐ t ∂volume.restrict (Ioc 0 T),
      (label s).val '' closedWeightChamber (fun i => (D.weight i).toContinuousLinearMap)
          (weightSigns (fun i => (D.weight i).toContinuousLinearMap) w) =
        (label t).val '' closedWeightChamber (fun i => (D.weight i).toContinuousLinearMap)
          (weightSigns (fun i => (D.weight i).toContinuousLinearMap) w) := by
  obtain ⟨S, hS⟩ := generic_profile_signs_constant D hweights h q hc w hw hT hq hFTC
    label hlabel hlower
  have hlabel' : ∀ᵐ t ∂volume.restrict (Ioc 0 T), q t = (label t).val w :=
    hlabel.filter_mono (ae_mono (Measure.restrict_mono Ioc_subset_Icc_self le_rfl))
  filter_upwards [hS, hlabel'] with s hs hqs
  filter_upwards [hS, hlabel'] with t ht hqt
  apply image_closedWeightChamber_eq_of_signs _ _ _
    (templateSymmetry_preservesPositiveWeightRays D hweights (label s))
    (templateSymmetry_preservesPositiveWeightRays D hweights (label s)⁻¹)
    (templateSymmetry_preservesPositiveWeightRays D hweights (label t))
    (templateSymmetry_preservesPositiveWeightRays D hweights (label t)⁻¹) hw
  intro i
  change 0 < D.weight i ((label s).val w) ↔ 0 < D.weight i ((label t).val w)
  rw [← hqs, ← hqt]
  exact (hs i).trans (ht i).symm

end PolycyclicRecognition.SupportDatum

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_GenericLipschitzProfile
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteRootOffsetConeIndex _root_.OAI.PolycyclicRecognition.instNonemptyRootOffsetConeIndex _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Generic chamber agreement from actual Lipschitz line derivatives -/

noncomputable section

namespace PolycyclicRecognition.SupportDatum

open MeasureTheory Set Filter
open scoped NNReal

theorem generic_lipschitz_profile_chamber_agreement
    {W I B : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    [FiniteDimensional ℝ W] [Fintype I] [Fintype B] [Nonempty B]
    (D : SupportDatum W I B) (hweights : ∀ i, D.weight i ≠ 0)
    (h : ℝ → W) (hc : Continuous h) (hzero : h 0 = 0)
    (w : W) (hw : ∀ i, D.weight i w ≠ 0) {T : ℝ} (hT : 0 ≤ T)
    {C : ℝ≥0} (hlip : LipschitzOnWith C h (Icc 0 T))
    (label : ℝ → templateSymmetryGroup D)
    (hderiv : ∀ᵐ t ∂volume.restrict (Icc 0 T), HasDerivAt h ((label t).val w) t)
    (hlower : T * D.segmentSupport w ≤ D.templateSupport (h '' Icc 0 T)) :
    ∀ᵐ s ∂volume.restrict (Ioc 0 T), ∀ᵐ t ∂volume.restrict (Ioc 0 T),
      (label s).val '' closedWeightChamber (fun i => (D.weight i).toContinuousLinearMap)
          (weightSigns (fun i => (D.weight i).toContinuousLinearMap) w) =
        (label t).val '' closedWeightChamber (fun i => (D.weight i).toContinuousLinearMap)
          (weightSigns (fun i => (D.weight i).toContinuousLinearMap) w) := by
  obtain ⟨hq, hFTC⟩ := profile_weight_fundamental_identities
    (fun i => (D.weight i).toContinuousLinearMap) hT hlip hderiv
  apply generic_profile_chamber_agreement D hweights h (fun t => (label t).val w)
    hc w hw hT hq _ label (Eventually.of_forall (fun _ => rfl)) hlower
  intro i t ht
  have hh := hFTC i t ht
  change D.weight i (h t - h 0) = ∫ s in 0..t, D.weight i ((label s).val w) at hh
  simpa only [hzero, sub_zero] using hh

end PolycyclicRecognition.SupportDatum

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_PolynomialCoordinateTopology
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The topology carried by an actual polynomial coordinate group -/

noncomputable section

namespace PolycyclicRecognition.PolynomialCoordinateGroup

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem isTopologicalGroup (m : V → V → V) (h : PolynomialGroupLaws m)
    (hc : Continuous (fun p : V × V => m p.1 p.2)) :
    IsTopologicalGroup (PolynomialCoordinateGroup m h) where
  continuous_mul := hc
  continuous_inv := by
    change Continuous (fun x : V => -x)
    exact continuous_neg

end PolycyclicRecognition.PolynomialCoordinateGroup

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_FlowNeighborhoods
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Connected neighborhoods admit one time interval for finitely many flows -/

noncomputable section

namespace PolycyclicRecognition

open Set Filter
open scoped Topology

variable {G V I : Type*} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

omit [TopologicalSpace G] [IsTopologicalGroup G] in
theorem flowLineBase_rescale
    (U : Set G) (Exp : V → G) (v : V) {T : ℝ} (hT : 0 < T) (g : G) :
    g ∈ flowLineBase U Exp (T • v) 1 ↔ g ∈ flowLineBase U Exp v T := by
  constructor
  · intro h s hs
    have hr : s / T ∈ Icc (0 : ℝ) 1 :=
      ⟨div_nonneg hs.1 hT.le, (div_le_one hT).mpr hs.2⟩
    have hh := h (s / T) hr
    simpa only [smul_smul, div_mul_cancel₀ _ hT.ne'] using hh
  · intro h r hr
    have hs : r * T ∈ Icc (0 : ℝ) T :=
      ⟨mul_nonneg hr.1 hT.le, by nlinarith [hr.2]⟩
    simpa only [smul_smul] using h (r * T) hs

theorem exists_connected_flow_neighborhood
    [LocallyConnectedSpace G] [Finite I]
    (Ω : Set G) (hΩ : IsOpen Ω) (Exp : V → G) (hExp : Continuous Exp)
    (hExp0 : Exp 0 = 1) (X : I → V) {g : G} (hg : g ∈ Ω) :
    ∃ T : ℝ, 0 < T ∧ ∃ N : Set G, IsOpen N ∧ g ∈ N ∧ IsConnected N ∧ N ⊆ Ω ∧
      ∀ i, N ⊆ flowLineBase Ω Exp (X i) T := by
  have hsmall : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ i, g ∈ flowLineBase Ω Exp (t • X i) 1 :=
    eventually_all.mpr (fun i => eventually_short_flowLineBase hΩ hExp hExp0 (X i) hg)
  obtain ⟨ε, hε, he⟩ := Metric.eventually_nhds_iff.mp hsmall
  have hhalf : 0 < ε / 2 := half_pos hε
  have hd : dist (ε / 2) (0 : ℝ) < ε := by
    rw [Real.dist_eq, sub_zero, abs_of_pos hhalf]
    linarith
  have hpoint (i : I) : g ∈ flowLineBase Ω Exp (X i) (ε / 2) :=
    (flowLineBase_rescale Ω Exp (X i) hhalf g).mp (he hd i)
  let Q := Ω ∩ ⋂ i, flowLineBase Ω Exp (X i) (ε / 2)
  have hQo : IsOpen Q := hΩ.inter
    (isOpen_iInter_of_finite fun i => isOpen_flowLineBase Ω hΩ Exp hExp (X i) (ε / 2))
  have hgQ : g ∈ Q := ⟨hg, mem_iInter.mpr hpoint⟩
  obtain ⟨N, hNQ, hNo, hgN, hNc⟩ :=
    locallyConnectedSpace_iff_subsets_isOpen_isConnected.mp inferInstance g Q (hQo.mem_nhds hgQ)
  refine ⟨ε / 2, hhalf, N, hNo, hgN, hNc, fun x hx => (hNQ hx).1, ?_⟩
  intro i x hx
  exact mem_iInter.mp (hNQ hx).2 i

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_FlowDerivativeTransport
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Base-point derivatives transported to almost every point of a flow line -/

noncomputable section

namespace PolycyclicRecognition

open Set Filter MeasureTheory MeasureTheory.Measure

theorem ae_flow_hasDerivAt_of_ae_base
    {G V W : Type*} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    [MeasurableSpace G] [BorelSpace G]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (μ : Measure G) [SFinite μ] [μ.IsMulRightInvariant]
    (Exp : V → G) (hExp : Continuous Exp)
    (hadd : ∀ v (s t : ℝ), Exp ((s + t) • v) = Exp (s • v) * Exp (t • v))
    (v : V) (f q : G → W) (U : Set G)
    (hbase : ∀ᵐ g ∂μ, g ∈ U → HasDerivAt (fun t : ℝ => f (g * Exp (t • v))) (q g) 0) :
    ∀ᵐ g ∂μ, ∀ᵐ t : ℝ, g * Exp (t • v) ∈ U →
      HasDerivAt (fun s : ℝ => f (g * Exp (s • v))) (q (g * Exp (t • v))) t := by
  have hpres : MeasurePreserving (fun z : ℝ × G => (z.1, z.2 * Exp (z.1 • v)))
      (volume.prod μ) (volume.prod μ) := by
    exact (MeasurePreserving.id volume).skew_product
      (by
        change Measurable (fun z : ℝ × G => z.2 * Exp (z.1 • v))
        exact (continuous_snd.mul (hExp.comp (continuous_fst.smul continuous_const))).measurable)
      (Eventually.of_forall (fun t => (measurePreserving_mul_right μ (Exp (t • v))).map_eq))
  have hh := hpres.quasiMeasurePreserving.ae (quasiMeasurePreserving_snd.ae hbase)
  have hswap := (Measure.measurePreserving_swap (μ := μ) (ν := (volume : Measure ℝ))).quasiMeasurePreserving.ae hh
  filter_upwards [ae_ae_of_ae_prod hswap] with g hg
  filter_upwards [hg] with t ht hmem
  change g * Exp (t • v) ∈ U →
    HasDerivAt (fun s : ℝ => f ((g * Exp (t • v)) * Exp (s • v)))
      (q (g * Exp (t • v))) 0 at ht
  have hd := (ht hmem).scomp_of_eq t ((hasDerivAt_id t).sub_const t) (by simp)
  have heq : (fun s : ℝ => f ((g * Exp (t • v)) * Exp ((s - t) • v))) =
      (fun s : ℝ => f (g * Exp (s • v))) := by
    funext s
    rw [mul_assoc, ← hadd]
    rw [show t + (s - t) = s by ring]
  simpa only [Function.comp_def, Function.id_def, one_smul, heq] using hd

theorem ae_flowLine_hasDerivAt_of_ae_base
    {G V W : Type*} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    [MeasurableSpace G] [BorelSpace G]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (μ : Measure G) [SFinite μ] [μ.IsMulRightInvariant]
    (Exp : V → G) (hExp : Continuous Exp)
    (hadd : ∀ v (s t : ℝ), Exp ((s + t) • v) = Exp (s • v) * Exp (t • v))
    (v : V) (f q : G → W) (U : Set G)
    (hbase : ∀ᵐ g ∂μ, g ∈ U → HasDerivAt (fun t : ℝ => f (g * Exp (t • v))) (q g) 0)
    (T : ℝ) :
    ∀ᵐ g ∂μ, g ∈ flowLineBase U Exp v T → ∀ᵐ t ∂volume.restrict (Icc 0 T),
      HasDerivAt (fun s : ℝ => f (g * Exp (s • v))) (q (g * Exp (t • v))) t := by
  filter_upwards [ae_flow_hasDerivAt_of_ae_base μ Exp hExp hadd v f q U hbase] with g hg hstay
  filter_upwards [ae_restrict_of_ae hg, ae_restrict_mem measurableSet_Icc] with t ht hmem
  exact ht (hstay t hmem)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_GenericFlowChambers
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteRootOffsetConeIndex _root_.OAI.PolycyclicRecognition.instNonemptyRootOffsetConeIndex _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.CartanWordModel.supportDatum_weight _root_.OAI.PolycyclicRecognition.SupportDatum.transport_weight_apply _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Generic flow restrictions have one image chamber almost everywhere -/

noncomputable section

namespace PolycyclicRecognition.SupportDatum

open Set Filter MeasureTheory
open scoped NNReal

theorem ae_generic_flowLine_chamber_agreement
    {G V W I B L : Type*} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    [MeasurableSpace G] [BorelSpace G]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
    [Fintype I] [Fintype B] [Nonempty B]
    (D : SupportDatum W I B) (hweights : ∀ i, D.weight i ≠ 0)
    (μ : Measure G) [SFinite μ] [μ.IsMulRightInvariant]
    (Exp : V → G) (hExp : Continuous Exp) (hzero : Exp 0 = 1)
    (hadd : ∀ v (s t : ℝ), Exp ((s + t) • v) = Exp (s • v) * Exp (t • v))
    (π : V →L[ℝ] W) (v : V) (hw : ∀ i, D.weight i (π v) ≠ 0)
    (f : G → W) (hf : Continuous f) (U : Set G)
    (label : G → L) (A : L → templateSymmetryGroup D)
    (hbase : ∀ᵐ g ∂μ, g ∈ U → HasDerivAt (fun t : ℝ => f (g * Exp (t • v)))
      ((A (label g)).val (π v)) 0)
    {T : ℝ} (hT : 0 ≤ T) (C : ℝ≥0)
    (hlip : ∀ g ∈ flowLineBase U Exp v T,
      LipschitzOnWith C (fun t : ℝ => f (g * Exp (t • v))) (Icc 0 T))
    (hvol : ∀ g ∈ flowLineBase U Exp v T,
      T * D.segmentSupport (π v) ≤ D.templateSupport ((fun t : ℝ => f (g * Exp (t • v))) '' Icc 0 T)) :
    ∀ᵐ g ∂μ, g ∈ flowLineBase U Exp v T →
      ∀ᵐ s ∂volume.restrict (Ioc 0 T), ∀ᵐ t ∂volume.restrict (Ioc 0 T),
        (A (label (g * Exp (s • v)))).val ''
            closedWeightChamber (fun i => (D.weight i).toContinuousLinearMap)
              (weightSigns (fun i => (D.weight i).toContinuousLinearMap) (π v)) =
          (A (label (g * Exp (t • v)))).val ''
            closedWeightChamber (fun i => (D.weight i).toContinuousLinearMap)
              (weightSigns (fun i => (D.weight i).toContinuousLinearMap) (π v)) := by
  filter_upwards [ae_flowLine_hasDerivAt_of_ae_base μ Exp hExp hadd v f
    (fun g => (A (label g)).val (π v)) U hbase T] with g hg hstay
  let c : ℝ → W := fun t => f (g * Exp (t • v))
  have hc : Continuous c := by dsimp [c]; fun_prop
  have hdc : ∀ᵐ t ∂volume.restrict (Icc 0 T),
      HasDerivAt (fun s : ℝ => c s - f g) ((A (label (g * Exp (t • v)))).val (π v)) t := by
    filter_upwards [hg hstay] with t ht
    exact ht.sub_const (f g)
  have hvol' : T * D.segmentSupport (π v) ≤
      D.templateSupport ((fun t : ℝ => c t - f g) '' Icc 0 T) := by
    have hcpt : IsCompact (c '' Icc 0 T) := isCompact_Icc.image hc
    have hne : (c '' Icc 0 T).Nonempty := (nonempty_Icc.mpr hT).image c
    have heq : (fun t : ℝ => c t - f g) '' Icc 0 T =
        (fun x : W => x + (-f g)) '' (c '' Icc 0 T) := by
      rw [image_image]
      simp only [sub_eq_add_neg]
    rw [heq, D.templateSupport_translate hcpt hne (-f g)]
    exact hvol g hstay
  have hlip' : LipschitzOnWith C (fun t : ℝ => c t - f g) (Icc 0 T) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro s hs t ht
    simpa only [dist_sub_right, c] using (hlip g hstay).dist_le_mul s hs t ht
  exact D.generic_lipschitz_profile_chamber_agreement hweights (fun t => c t - f g)
    (hc.sub continuous_const) (by simp [c, hzero]) (π v) hw hT
    hlip' (fun t => A (label (g * Exp (t • v)))) hdc hvol'

end PolycyclicRecognition.SupportDatum

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_RationalFlowBoxes
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A countable interval cover of admissible flow segments -/

noncomputable section

namespace PolycyclicRecognition

open Set Filter Metric

theorem exists_rational_interval_in_open
    {U : Set ℝ} (hU : IsOpen U) {s t : ℝ} (hseg : Icc (min s t) (max s t) ⊆ U) :
    ∃ a b : ℚ, s ∈ Ioo (a : ℝ) b ∧ t ∈ Ioo (a : ℝ) b ∧ Icc (a : ℝ) b ⊆ U := by
  obtain ⟨δ, hδ, hthick⟩ := isCompact_Icc.exists_cthickening_subset_open hU hseg
  obtain ⟨a, ha₀, ha₁⟩ := exists_rat_btwn (show min s t - δ < min s t by linarith)
  obtain ⟨b, hb₀, hb₁⟩ := exists_rat_btwn (show max s t < max s t + δ by linarith)
  refine ⟨a, b, ⟨ha₁.trans_le (min_le_left _ _), (le_max_left _ _).trans_lt hb₀⟩,
    ⟨ha₁.trans_le (min_le_right _ _), (le_max_right _ _).trans_lt hb₀⟩, ?_⟩
  intro u hu
  apply hthick
  by_cases hlow : u < min s t
  · apply mem_cthickening_of_dist_le u (min s t) δ (Icc (min s t) (max s t))
      ⟨le_rfl, min_le_max⟩
    rw [Real.dist_eq, abs_of_neg (sub_neg.mpr hlow)]
    linarith [hu.1]
  · by_cases hhigh : max s t < u
    · apply mem_cthickening_of_dist_le u (max s t) δ (Icc (min s t) (max s t))
        ⟨min_le_max, le_rfl⟩
      rw [Real.dist_eq, abs_of_pos (sub_pos.mpr hhigh)]
      linarith [hu.2]
    · exact self_subset_cthickening (Icc (min s t) (max s t)) ⟨le_of_not_gt hlow, le_of_not_gt hhigh⟩

theorem flowSegmentDomain_eq_iUnion_rationalFlowBox
    {G V : Type*} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (U : Set G) (hU : IsOpen U) (Exp : V → G) (hExp : Continuous Exp) (v : V) :
    flowSegmentDomain U Exp v = ⋃ q : ℚ × ℚ, rationalFlowBox U Exp v q := by
  ext z
  constructor
  · intro hz
    have ho : IsOpen {t : ℝ | z.2 * Exp (t • v) ∈ U} := hU.preimage (by fun_prop)
    have hs : Icc (min z.1.1 z.1.2) (max z.1.1 z.1.2) ⊆
        {t : ℝ | z.2 * Exp (t • v) ∈ U} := by
      intro t ht
      have ht' : t ∈ segment ℝ z.1.1 z.1.2 := by rwa [segment_eq_Icc']
      rw [segment_eq_image] at ht'
      obtain ⟨r, hr, rfl⟩ := ht'
      change z.2 * Exp (((1 - r) • z.1.1 + r • z.1.2) • v) ∈ U
      simpa only [flowSegmentPoint, smul_eq_mul] using hz r hr
    obtain ⟨a, b, hs, ht, hab⟩ := exists_rational_interval_in_open ho hs
    exact mem_iUnion.mpr ⟨(a, b), hs, ht, hab⟩
  · intro hz
    obtain ⟨q, hs, ht, hab⟩ := mem_iUnion.mp hz
    intro r hr
    apply hab
    have hh := (convex_Icc (q.1 : ℝ) q.2) ⟨hs.1.le, hs.2.le⟩ ⟨ht.1.le, ht.2.le⟩
      (sub_nonneg.mpr hr.2) hr.1 (show (1 - r) + r = 1 by ring)
    simpa only [smul_eq_mul] using hh

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_JointFlowRelation
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_countable _root_.OAI.PolycyclicRecognition.finitelyGeneratedSubgroupIndex_countable _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # From intervalwise label agreement to agreement on all admissible segments -/

noncomputable section

namespace PolycyclicRecognition

open Set Filter MeasureTheory MeasureTheory.Measure

theorem measurableSet_flow_label_relation
    {G V L : Type*} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    [MeasurableSpace G] [BorelSpace G]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [Countable L] [MeasurableSpace L] [MeasurableSingletonClass L]
    (Exp : V → G) (hExp : Continuous Exp) (v : V)
    (label : G → L) (hl : Measurable label) (R : L → L → Prop) :
    MeasurableSet {z : (ℝ × ℝ) × G |
      R (label (z.2 * Exp (z.1.1 • v))) (label (z.2 * Exp (z.1.2 • v)))} := by
  have hm : Measurable (fun z : (ℝ × ℝ) × G =>
      (label (z.2 * Exp (z.1.1 • v)), label (z.2 * Exp (z.1.2 • v)))) :=
    (hl.comp ((continuous_snd.mul (hExp.comp
      ((continuous_fst.comp continuous_fst).smul continuous_const))).measurable)).prodMk
      (hl.comp ((continuous_snd.mul (hExp.comp
        ((continuous_snd.comp continuous_fst).smul continuous_const))).measurable))
  exact hm ((Set.to_countable {p : L × L | R p.1 p.2}).measurableSet)

theorem ae_joint_flow_relation_of_intervals
    {G V L : Type*} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    [MeasurableSpace G] [BorelSpace G]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [Countable L] [MeasurableSpace L] [MeasurableSingletonClass L]
    (μ : Measure G) [SFinite μ] [μ.IsMulRightInvariant]
    (Exp : V → G) (hExp : Continuous Exp)
    (hadd : ∀ v (s t : ℝ), Exp ((s + t) • v) = Exp (s • v) * Exp (t • v))
    (v : V) (U : Set G) (hU : IsOpen U)
    (label : G → L) (hl : Measurable label) (R : L → L → Prop)
    (hline : ∀ T : ℝ, 0 < T → ∀ᵐ g ∂μ, g ∈ flowLineBase U Exp v T →
      ∀ᵐ s ∂volume.restrict (Ioc 0 T), ∀ᵐ t ∂volume.restrict (Ioc 0 T),
        R (label (g * Exp (s • v))) (label (g * Exp (t • v)))) :
    ∀ᵐ z ∂(pairTimeMeasure.prod μ).restrict (flowSegmentDomain U Exp v),
      R (label (z.2 * Exp (z.1.1 • v))) (label (z.2 * Exp (z.1.2 • v))) := by
  have hRel := measurableSet_flow_label_relation Exp hExp v label hl R
  rw [flowSegmentDomain_eq_iUnion_rationalFlowBox U hU Exp hExp v,
    ae_restrict_iUnion_iff]
  rintro ⟨a, b⟩
  apply (ae_restrict_iff hRel).mpr
  by_cases hab : (a : ℝ) < b
  · let T : ℝ := b - a
    have hT : 0 < T := sub_pos.mpr hab
    let P : ((ℝ × ℝ) × G) → Prop := fun z =>
      z.1.1 ∈ Ioc 0 T → z.1.2 ∈ Ioc 0 T → z.2 ∈ flowLineBase U Exp v T →
        R (label (z.2 * Exp (z.1.1 • v))) (label (z.2 * Exp (z.1.2 • v)))
    have hP : MeasurableSet {z | P z} := by
      change MeasurableSet {z : (ℝ × ℝ) × G | z.1.1 ∈ Ioc 0 T →
        z.1.2 ∈ Ioc 0 T → z.2 ∈ flowLineBase U Exp v T →
        R (label (z.2 * Exp (z.1.1 • v))) (label (z.2 * Exp (z.1.2 • v)))}
      exact (measurableSet_Ioc.preimage (measurable_fst.comp measurable_fst)).imp
        ((measurableSet_Ioc.preimage (measurable_snd.comp measurable_fst)).imp
          (((isOpen_flowLineBase U hU Exp hExp v T).measurableSet.preimage
            measurable_snd).imp hRel))
    have hswap : ∀ᵐ z ∂μ.prod pairTimeMeasure, P (z.2, z.1) := by
      apply (ae_prod_iff_ae_ae (hP.preimage measurable_swap)).mpr
      filter_upwards [hline T hT] with g hg
      apply (ae_prod_iff_ae_ae ((hP.preimage (by fun_prop)))).mpr
      by_cases hstay : g ∈ flowLineBase U Exp v T
      · filter_upwards [(ae_restrict_iff' measurableSet_Ioc).mp (hg hstay)] with s hs
        by_cases hs' : s ∈ Ioc 0 T
        · filter_upwards [(ae_restrict_iff' measurableSet_Ioc).mp (hs hs')] with t ht
          exact fun _ ht' _ => ht ht'
        · exact Eventually.of_forall (fun _ hs'' => (hs' hs'').elim)
      · exact Eventually.of_forall (fun _ => Eventually.of_forall (fun _ _ _ hg' =>
          (hstay hg').elim))
    have hpair : ∀ᵐ z ∂pairTimeMeasure.prod μ, P z :=
      (measurePreserving_swap (μ := pairTimeMeasure) (ν := μ)).quasiMeasurePreserving.ae hswap
    have hshift : MeasurePreserving
        (fun z : (ℝ × ℝ) × G => ((z.1.1 - a, z.1.2 - a), z.2 * Exp ((a : ℝ) • v)))
        (pairTimeMeasure.prod μ) (pairTimeMeasure.prod μ) := by
      convert
        ((measurePreserving_add_right (volume : Measure ℝ) (-(a : ℝ))).prod
          (measurePreserving_add_right (volume : Measure ℝ) (-(a : ℝ)))).prod
          (measurePreserving_mul_right μ (Exp ((a : ℝ) • v))) using 1
      all_goals try with_reducible_and_instances rfl
      funext z
      simp only [Prod.map, sub_eq_add_neg]
      all_goals rfl
    filter_upwards [hshift.quasiMeasurePreserving.ae hpair] with z hz hzbox
    have hs : z.1.1 - a ∈ Ioc 0 T := by
      change 0 < z.1.1 - a ∧ z.1.1 - a ≤ (b : ℝ) - a
      constructor <;> linarith [hzbox.1.1, hzbox.1.2]
    have ht : z.1.2 - a ∈ Ioc 0 T := by
      change 0 < z.1.2 - a ∧ z.1.2 - a ≤ (b : ℝ) - a
      constructor <;> linarith [hzbox.2.1.1, hzbox.2.1.2]
    have hstay : z.2 * Exp ((a : ℝ) • v) ∈ flowLineBase U Exp v T := by
      intro t ht
      rw [mul_assoc, ← hadd]
      apply hzbox.2.2
      constructor <;> dsimp [T] at ht <;> linarith [ht.1, ht.2]
    have heq (t : ℝ) : z.2 * Exp ((a : ℝ) • v) * Exp ((t - a) • v) =
        z.2 * Exp (t • v) := by
      rw [mul_assoc, ← hadd]
      rw [show (a : ℝ) + (t - a) = t by ring]
    simpa only [P, heq] using hz hs ht hstay
  · exact Eventually.of_forall (fun z hz => (hab (hz.1.1.trans hz.1.2)).elim)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_GenericJointChambers
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteRootOffsetConeIndex _root_.OAI.PolycyclicRecognition.instNonemptyRootOffsetConeIndex _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The generic chamber relation on the full domain of admissible triples -/

noncomputable section

namespace PolycyclicRecognition.SupportDatum

open Set Filter MeasureTheory
open scoped NNReal

theorem ae_generic_joint_chamber_agreement
    {G V W I B L : Type*} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    [MeasurableSpace G] [BorelSpace G]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
    [Fintype I] [Fintype B] [Nonempty B]
    [Countable L] [MeasurableSpace L] [MeasurableSingletonClass L]
    (D : SupportDatum W I B) (hweights : ∀ i, D.weight i ≠ 0)
    (μ : Measure G) [SFinite μ] [μ.IsMulRightInvariant]
    (Exp : V → G) (hExp : Continuous Exp) (hzero : Exp 0 = 1)
    (hadd : ∀ v (s t : ℝ), Exp ((s + t) • v) = Exp (s • v) * Exp (t • v))
    (π : V →L[ℝ] W) (v : V) (hw : ∀ i, D.weight i (π v) ≠ 0)
    (f : G → W) (hf : Continuous f) (U : Set G) (hU : IsOpen U)
    (label : G → L) (hlabel : Measurable label) (A : L → templateSymmetryGroup D)
    (hbase : ∀ᵐ g ∂μ, g ∈ U → HasDerivAt (fun t : ℝ => f (g * Exp (t • v)))
      ((A (label g)).val (π v)) 0)
    (C : ℝ≥0)
    (hlip : ∀ g, LipschitzOnWith C (fun t : ℝ => f (g * Exp (t • v)))
      {t | g * Exp (t • v) ∈ U})
    (hvol : ∀ T : ℝ, 0 < T → ∀ g ∈ flowLineBase U Exp v T,
      T * D.segmentSupport (π v) ≤ D.templateSupport ((fun t : ℝ => f (g * Exp (t • v))) '' Icc 0 T)) :
    ∀ᵐ z ∂(pairTimeMeasure.prod μ).restrict (flowSegmentDomain U Exp v),
      (A (label (z.2 * Exp (z.1.1 • v)))).val ''
          closedWeightChamber (fun i => (D.weight i).toContinuousLinearMap)
            (weightSigns (fun i => (D.weight i).toContinuousLinearMap) (π v)) =
        (A (label (z.2 * Exp (z.1.2 • v)))).val ''
          closedWeightChamber (fun i => (D.weight i).toContinuousLinearMap)
            (weightSigns (fun i => (D.weight i).toContinuousLinearMap) (π v)) := by
  apply ae_joint_flow_relation_of_intervals μ Exp hExp hadd v U hU label hlabel
    (fun l₁ l₂ => (A l₁).val ''
      closedWeightChamber (fun i => (D.weight i).toContinuousLinearMap)
        (weightSigns (fun i => (D.weight i).toContinuousLinearMap) (π v)) =
      (A l₂).val '' closedWeightChamber (fun i => (D.weight i).toContinuousLinearMap)
        (weightSigns (fun i => (D.weight i).toContinuousLinearMap) (π v)))
  intro T hT
  exact D.ae_generic_flowLine_chamber_agreement hweights μ Exp hExp hzero hadd π v hw
    f hf U label A hbase hT.le C (fun g hg => (hlip g).mono hg) (hvol T hT)

end PolycyclicRecognition.SupportDatum

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_HorizontalExtremeSpanning
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finitely many extreme and kernel directions span the horizontal layer -/

noncomputable section

namespace PolycyclicRecognition

open Set

theorem exists_finite_spanning_horizontal_directions
    {V W I : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] [Fintype I]
    (π : V →L[ℝ] W) (hπ : Function.Surjective π)
    (α : I → W →L[ℝ] ℝ) (σ : I → Bool)
    (hsep : ∀ w : W, (∀ i, α i w = 0) → w = 0)
    (hne : (weightChamber α σ).Nonempty) :
    ∃ S : Finset V, Submodule.span ℝ (S : Set V) = ⊤ ∧
      ∀ v ∈ S, π v = 0 ∨ π v ∈ chamberExtremeDirections α σ := by
  let D := chamberExtremeDirections α σ
  let E : Set V := {v | π v = 0 ∨ π v ∈ D}
  let P := Submodule.span ℝ E
  have hker : π.ker ≤ P := by
    intro v hv
    exact Submodule.subset_span (Or.inl hv)
  have himage : Submodule.span ℝ D ≤ P.map π.toLinearMap := by
    rw [Submodule.span_le]
    intro w hw
    obtain ⟨v, hv⟩ := hπ w
    refine ⟨v, Submodule.subset_span (Or.inr ?_), hv⟩
    rwa [hv]
  have hDtop : Submodule.span ℝ D = ⊤ := span_chamberExtremeDirections_eq_top α σ hsep hne
  have hPtop : P = ⊤ := by
    apply top_unique
    intro v _hv
    have hvimage : π v ∈ P.map π.toLinearMap := himage (hDtop ▸ Submodule.mem_top)
    obtain ⟨u, hu, he⟩ := hvimage
    change π u = π v at he
    have hdiff : v - u ∈ π.ker := by
      change π (v - u) = 0
      rw [map_sub, he, sub_self]
    have hsum := P.add_mem (hker hdiff) hu
    simpa only [sub_add_cancel] using hsum
  obtain ⟨S, hSE, _hcard, hspan, _hindep⟩ := Submodule.exists_finset_span_eq_linearIndepOn ℝ E
  refine ⟨S, hspan.trans hPtop, ?_⟩
  intro v hv
  exact hSE hv

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_HorizontalGeneratorChange
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Changing a horizontal spanning family preserves bracket generation -/

noncomputable section

namespace PolycyclicRecognition

open Module

theorem exists_word_basis_of_spanning_horizontal
    {H V I J K : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (B : V →L[ℝ] V →L[ℝ] V) (hB : IsLieBracket B)
    (D : H →L[ℝ] V) (X : I → H) (b₀ : Basis K ℝ V) (w₀ : K → FreeMagma I)
    (hw₀ : ∀ k, evalBilinearWord B (fun i => D (X i)) (w₀ k) = b₀ k)
    (Y : J → H) (hY : Submodule.span ℝ (Set.range Y) = ⊤) :
    ∃ b : Basis (Fin (Module.finrank ℝ V)) ℝ V,
      ∃ w : Fin (Module.finrank ℝ V) → FreeMagma J,
        ∀ k, evalBilinearWord B (fun j => D (Y j)) (w k) = b k := by
  let := lieRingOfBilinear B hB
  let := lieAlgebraOfBilinear B hB
  let P := LieSubalgebra.lieSpan ℝ V (Set.range (fun j => D (Y j)))
  have hD (h : H) : D h ∈ P := by
    have hh : h ∈ Submodule.span ℝ (Set.range Y) := by rw [hY]; trivial
    induction hh using Submodule.span_induction with
    | mem h hh =>
      obtain ⟨j, rfl⟩ := hh
      exact LieSubalgebra.subset_lieSpan ⟨j, rfl⟩
    | zero => simpa only [map_zero] using P.zero_mem
    | add h k _ _ hh hk => simpa only [map_add] using P.add_mem hh hk
    | smul c h _ hh => simpa only [map_smul] using P.smul_mem c hh
  have hP : P = ⊤ := by
    apply top_unique
    rw [← lieSpan_eq_top_of_word_basis B hB (fun i => D (X i)) b₀ w₀ hw₀]
    apply LieSubalgebra.lieSpan_le.mpr
    rintro _ ⟨i, rfl⟩
    exact hD (X i)
  obtain ⟨b, hb⟩ := exists_bracketWord_basis (fun j => D (Y j)) hP
  choose w hw using hb
  refine ⟨b, w, fun k => ?_⟩
  rw [evalBilinearWord_eq_lieWord B hB]
  exact hw k

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_LocalGeneratorOrbit
attribute [-instance] _root_.GeneratesNS.fintype_closedBall _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Adjoint generators restricted to an open family of words

Only arbitrarily small prefixes are needed in the spanning proof. This lets
the conjugating words stay inside a specified open coordinate neighborhood.
-/

noncomputable section

namespace PolycyclicRecognition

open Set Filter Module
open scoped Topology

variable {V I : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V]

theorem derivative_mem_submodule_of_eventually
    {f : ℝ → V} {v : V} (hd : HasDerivAt f v 0) (P : Submodule ℝ V)
    (hf : ∀ᶠ t in 𝓝 0, f t ∈ P) : v ∈ P := by
  have hzero : f 0 ∈ P :=
    (show (0 : ℝ) ∈ {t : ℝ | f t ∈ P} from mem_of_mem_nhds hf)
  apply P.closed_of_finiteDimensional.mem_of_tendsto hd.tendsto_slope
  filter_upwards [hf.filter_mono nhdsWithin_le_nhds] with t ht
  exact P.smul_mem _ (P.sub_mem ht hzero)

omit [FiniteDimensional ℝ V] in
theorem local_bilinear_generator_mem (B : V →L[ℝ] V →L[ℝ] V) (X : I → V)
    (good : List (I × ℝ) → Prop) (hnil : good []) (i : I) :
    X i ∈ localBilinearOrbitSpan B X good := by
  apply Submodule.subset_span
  exact ⟨[], hnil, i, by simp [bilinearAdjointWord]⟩

theorem local_bilinear_ad_mem (B : V →L[ℝ] V →L[ℝ] V) (X : I → V)
    (good : List (I × ℝ) → Prop)
    (hprefix : ∀ w, good w → ∀ i, ∀ᶠ t in 𝓝 (0 : ℝ), good ((i, t) :: w))
    (i : I) {v : V} (hv : v ∈ localBilinearOrbitSpan B X good) :
    B (X i) v ∈ localBilinearOrbitSpan B X good := by
  induction hv using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨w, hw, j, rfl⟩ := hv
    let z := bilinearAdjointWord B X w (X j)
    have hd : HasDerivAt (fun t : ℝ => NormedSpace.exp (t • B (X i)) z)
        (B (X i) z) 0 := by
      simpa using (hasDerivAt_exp_smul_const (B (X i)) (0 : ℝ)).clm_apply
        (hasDerivAt_const (0 : ℝ) z)
    apply derivative_mem_submodule_of_eventually hd
    filter_upwards [hprefix w hw i] with t ht
    apply Submodule.subset_span
    exact ⟨(i, t) :: w, ht, j, rfl⟩
  | zero => simp
  | add x y _ _ hx hy => simpa using (localBilinearOrbitSpan B X good).add_mem hx hy
  | smul c x _ hx => simpa using (localBilinearOrbitSpan B X good).smul_mem c hx

theorem localBilinearOrbitSpan_eq_top {J : Type*}
    (B : V →L[ℝ] V →L[ℝ] V) (hB : IsLieBracket B)
    (X : I → V) (b : Basis J ℝ V) (w : J → FreeMagma I)
    (hw : ∀ j, evalBilinearWord B X (w j) = b j)
    (good : List (I × ℝ) → Prop) (hnil : good [])
    (hprefix : ∀ w, good w → ∀ i, ∀ᶠ t in 𝓝 (0 : ℝ), good ((i, t) :: w)) :
    localBilinearOrbitSpan B X good = ⊤ := by
  let := lieRingOfBilinear B hB
  let := lieAlgebraOfBilinear B hB
  have hX := lieSpan_eq_top_of_word_basis B hB X b w hw
  let P := localBilinearOrbitSpan B X good
  have hstab : submoduleAdjointStabilizer P = ⊤ := by
    apply top_unique
    rw [← hX]
    apply LieSubalgebra.lieSpan_le.mpr
    rintro _ ⟨i, rfl⟩ v hv
    exact local_bilinear_ad_mem B X good hprefix i hv
  let Q : LieSubalgebra ℝ V := { P with
    lie_mem' := by
      intro x y hx hy
      have hx' : x ∈ submoduleAdjointStabilizer P := by rw [hstab]; trivial
      exact hx' y hy }
  have hQ : Q = ⊤ := by
    apply top_unique
    rw [← hX]
    apply LieSubalgebra.lieSpan_le.mpr
    rintro _ ⟨i, rfl⟩
    exact local_bilinear_generator_mem B X good hnil i
  exact congrArg LieSubalgebra.toSubmodule hQ

theorem exists_local_bilinearOrbit_basis {J : Type*}
    (B : V →L[ℝ] V →L[ℝ] V) (hB : IsLieBracket B)
    (X : I → V) (b₀ : Basis J ℝ V) (w₀ : J → FreeMagma I)
    (hw₀ : ∀ j, evalBilinearWord B X (w₀ j) = b₀ j)
    (good : List (I × ℝ) → Prop) (hnil : good [])
    (hprefix : ∀ w, good w → ∀ i, ∀ᶠ t in 𝓝 (0 : ℝ), good ((i, t) :: w)) :
    ∃ (b : Basis (Fin (finrank ℝ V)) ℝ V)
      (w : Fin (finrank ℝ V) → List (I × ℝ)) (i : Fin (finrank ℝ V) → I),
      ∀ k, good (w k) ∧ bilinearAdjointWord B X (w k) (X (i k)) = b k := by
  classical
  let S : Set V := {v | ∃ w, good w ∧ ∃ i, bilinearAdjointWord B X w (X i) = v}
  have hspan : ⊤ ≤ Submodule.span ℝ S :=
    (localBilinearOrbitSpan_eq_top B hB X b₀ w₀ hw₀ good hnil hprefix).ge
  let J' := (linearIndepOn_empty ℝ (id : V → V)).extend (Set.empty_subset S)
  let b : Basis J' ℝ V := Basis.ofSpan hspan
  let : Fintype J' := Fintype.ofFinite _
  let e : J' ≃ Fin (finrank ℝ V) :=
    Fintype.equivFinOfCardEq (finrank_eq_card_basis b).symm
  have hb (k : Fin (finrank ℝ V)) :
      ∃ w, good w ∧ ∃ i, bilinearAdjointWord B X w (X i) = (b.reindex e) k := by
    have hmem : b (e.symm k) ∈ S :=
      Basis.ofSpan_subset hspan (show b (e.symm k) ∈ range b from ⟨_, rfl⟩)
    simpa only [S, mem_ofPred_eq, Basis.coe_reindex, Function.comp_apply] using hmem
  choose w hw i hi using hb
  exact ⟨b.reindex e, w, i, fun k => ⟨hw k, hi k⟩⟩

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_LocalCoordinateScheme
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.basisDynkinParameter_zero _root_.OAI.PolycyclicRecognition.dynkinRightTranslation_apply _root_.OAI.PolycyclicRecognition.dynkinRightTranslation_symm_apply _root_.OAI.PolycyclicRecognition.exponentialHomOfDynkin_apply_exp _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A full-rank coordinate scheme with admissible conjugating paths -/

noncomputable section

namespace PolycyclicRecognition

open Set Filter Module
open scoped Topology

variable {V I : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] [Fintype I]

set_option maxHeartbeats 1000000 in
theorem coordinateScheme_map_nhds
    {c : ℕ} (a : DynkinCoefficients c 2) (B : V →L[ℝ] V →L[ℝ] V)
    (hB : IsLieBracket B) (hg : PolynomialGroupLaws (dynkinProduct a B))
    (hc : ExponentialConjugationLaw (dynkinProduct a B) B)
    (X : I → V) (b : Basis (Fin (finrank ℝ V)) ℝ V)
    (w : Fin (finrank ℝ V) → List (I × ℝ)) (i : Fin (finrank ℝ V) → I)
    (hb : ∀ k, bilinearAdjointWord B X (w k) (X (i k)) = b k) :
    map (polynomialEndpointScheme a w i (B, X)) (𝓝 0) = 𝓝 0 := by
  let Exp := PolynomialCoordinateGroup.exp (dynkinProduct a B) hg
  have he (t) : Exp (polynomialEndpointScheme a w i (B, X) t) =
      basisExponentialProduct Exp b t := by
    apply polynomialEndpointScheme_basisProduct a B hB hg X b w i
    intro k s
    rw [← hb k, ← map_smul]
    exact exp_bilinearAdjointWord _ hg B hc X (w k) (s • X (i k))
  have hz : polynomialEndpointScheme a w i (B, X) 0 = 0 := by
    apply Exp.injective
    rw [he]
    simp [Exp, basisExponentialProduct]
  have haxis (j : Fin (finrank ℝ V)) (s : ℝ) :
      polynomialEndpointScheme a w i (B, X) (Pi.single j s) = s • b j := by
    apply Exp.injective
    rw [he]
    unfold basisExponentialProduct
    rw [list_prod_ofFn_eq_single _ j (by
      intro k hk
      simp [Pi.single_eq_of_ne hk, Exp])]
    simp [Exp]
  let f := polynomialEndpointScheme a w i (B, X)
  have hdiff : ContDiff ℝ 1 f :=
    (contDiff_polynomialEndpointScheme a w i).comp (contDiff_const.prodMk contDiff_id)
  have hcol (j : Fin (finrank ℝ V)) : fderiv ℝ f 0 (Pi.single j 1) = b j := by
    have hd := hdiff.differentiable_one 0 |>.hasFDerivAt
    have h := hd.comp_hasDerivAt_of_eq (0 : ℝ) (hasDerivAt_single j (0 : ℝ)) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
    have heq : (fun s : ℝ => f (Pi.single j s)) = fun s => s • b j := funext (haxis j)
    change HasDerivAt (fun s : ℝ => f (Pi.single j s)) _ 0 at h
    rw [heq] at h
    exact h.unique (by simpa using (hasDerivAt_id (0 : ℝ)).smul_const (b j))
  have hd (t : Fin (finrank ℝ V) → ℝ) : fderiv ℝ f 0 t = b.equivFun.symm t := by
    calc
      _ = fderiv ℝ f 0 (∑ j, t j • Pi.single j (1 : ℝ)) :=
        congrArg _ (pi_eq_sum_univ' t)
      _ = ∑ j, t j • b j := by simp only [map_sum, map_smul, hcol]
      _ = _ := by
        simpa only [LinearEquiv.apply_symm_apply] using b.sum_equivFun (b.equivFun.symm t)
  have hs : (fderiv ℝ f 0).range = ⊤ := by
    apply LinearMap.range_eq_top.mpr
    intro y
    refine ⟨b.equivFun y, ?_⟩
    change fderiv ℝ f 0 (b.equivFun y) = y
    rw [hd, LinearEquiv.symm_apply_apply]
  simpa only [f, hz] using (hdiff.contDiffAt.hasStrictFDerivAt one_ne_zero).map_nhds_eq_of_surj hs

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_LocalGeneratorAccessibility
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Local accessibility from actual generator words

This uses the proved adjoint spanning and inverse function arguments. No
accessibility, regularity or affinity theorem is assumed as an input.
-/

noncomputable section

namespace PolycyclicRecognition

open Set Filter Module
open scoped Topology

variable {V I J : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] [Fintype I]
  {c : ℕ} (a : DynkinCoefficients c 2) (B : V →L[ℝ] V →L[ℝ] V)
  (hB : IsLieBracket B) (hg : PolynomialGroupLaws (dynkinProduct a B))
  (hc : ExponentialConjugationLaw (dynkinProduct a B) B)
  (X : I → V) (b₀ : Basis J ℝ V) (w₀ : J → FreeMagma I)
  (hw₀ : ∀ j, evalBilinearWord B X (w₀ j) = b₀ j)

include hB hc hw₀

theorem reachable_generatorWords_mem_nhds
    (U : Set (PolynomialCoordinateGroup (dynkinProduct a B) hg)) (hU : IsOpen U)
    {g : PolynomialCoordinateGroup (dynkinProduct a B) hg} (hgU : g ∈ U) :
    {y | ∃ w : List (I × ℝ),
      g ∈ generatorWordBase U (PolynomialCoordinateGroup.exp _ hg) X w ∧
        g * generatorGroupWord X (PolynomialCoordinateGroup.exp _ hg) w = y} ∈ 𝓝 g := by
  let G := PolynomialCoordinateGroup (dynkinProduct a B) hg
  let Exp := PolynomialCoordinateGroup.exp (dynkinProduct a B) hg
  let : IsTopologicalGroup G := PolynomialCoordinateGroup.isTopologicalGroup _ hg
    (continuous_dynkinProduct a (fun _ => B) Prod.fst Prod.snd
      continuous_const continuous_fst continuous_snd)
  have hExp : Continuous Exp := continuous_id
  have hExp0 : Exp 0 = 1 := rfl
  have hneg : ∀ v, Exp (-v) = (Exp v)⁻¹ := fun _ => rfl
  have hadd := PolynomialCoordinateGroup.exp_add_smul (dynkinProduct a B) hg
  obtain ⟨b, w, i, hw⟩ := exists_local_bilinearOrbit_basis B hB X b₀ w₀ hw₀
    (fun w => g ∈ generatorWordBase U Exp X w) hgU
    (fun w hw i => eventually_prefix_generatorWordBase U hU Exp hExp hExp0 X w hw i)
  have hzero := mem_generatorScheme_zero U Exp hExp0 hneg hadd X w i hgU (fun k => (hw k).1)
  have hgood := eventually_generatorScheme U hU Exp hExp X w i hzero
  let F := polynomialEndpointScheme a w i (B, X)
  have hmapF : map F (𝓝 0) = 𝓝 0 := coordinateScheme_map_nhds a B hB hg hc X b w i
    (fun k => (hw k).2)
  let e : V ≃ₜ G := (PolynomialCoordinateGroup.expHomeomorph _ hg).trans
    (Homeomorph.mulLeft g)
  have hmap : map (fun t => g * Exp (F t)) (𝓝 0) = 𝓝 g := by
    change map (e ∘ F) (𝓝 0) = 𝓝 g
    rw [← map_map, hmapF, e.map_nhds_eq]
    change 𝓝 (g * Exp 0) = 𝓝 g
    rw [hExp0, mul_one]
  have himage := image_mem_map (m := fun t => g * Exp (F t)) hgood
  rw [hmap] at himage
  apply mem_of_superset himage
  rintro y ⟨t, ht, rfl⟩
  refine ⟨generatorSchemeWord w i t, ht, ?_⟩
  exact congrArg (fun z => g * z) (exp_polynomialEndpointScheme a B hB hg X w i t).symm

theorem eq_of_generator_flow_invariance
    {W : Type*}
    (U : Set (PolynomialCoordinateGroup (dynkinProduct a B) hg))
    (hU : IsOpen U) (hconn : IsPreconnected U)
    (f : PolynomialCoordinateGroup (dynkinProduct a B) hg → W)
    (hflow : ∀ (i : I) (g : PolynomialCoordinateGroup (dynkinProduct a B) hg) (t : ℝ),
      g ∈ flowLineBase U (PolynomialCoordinateGroup.exp _ hg) (t • X i) 1 →
        f (g * PolynomialCoordinateGroup.exp _ hg (t • X i)) = f g)
    {x y : PolynomialCoordinateGroup (dynkinProduct a B) hg}
    (hx : x ∈ U) (hy : y ∈ U) : f x = f y := by
  have hlocal (g : PolynomialCoordinateGroup (dynkinProduct a B) hg) (hgU : g ∈ U) :
      ∀ᶠ z in 𝓝 g, f z = f g := by
    filter_upwards [reachable_generatorWords_mem_nhds a B hB hg hc X b₀ w₀ hw₀ U hU hgU]
      with z hz
    obtain ⟨w, hw, rfl⟩ := hz
    exact eq_on_admissible_generatorWord f U (PolynomialCoordinateGroup.exp _ hg) X hflow w hw
  let : PreconnectedSpace U := Subtype.preconnectedSpace hconn
  have hlc : IsLocallyConstant (fun z : U => f z.val) := by
    apply (IsLocallyConstant.iff_eventually_eq _).mpr
    intro z
    exact continuous_subtype_val.continuousAt.tendsto.eventually (hlocal z.val z.property)
  exact hlc.apply_eq_of_preconnectedSpace ⟨x, hx⟩ ⟨y, hy⟩

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_FlowStepIteration
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Small constant flow increments imply constancy on an entire segment -/

noncomputable section

namespace PolycyclicRecognition

open Set

variable {G V W : Type*} [Group G] [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem eq_on_positive_flow_of_small_steps
    (f : G → W) (U : Set G) (Exp : V → G) (hExp0 : Exp 0 = 1)
    (hadd : ∀ v (s t : ℝ), Exp ((s + t) • v) = Exp (s • v) * Exp (t • v))
    (v : V) {T : ℝ} (hT : 0 < T)
    (hstep : ∀ g ∈ U, ∀ s ∈ Icc 0 T, f (g * Exp (s • v)) = f g)
    {g : G} {t : ℝ} (ht : 0 ≤ t)
    (hstay : g ∈ flowLineBase U Exp (t • v) 1) : f (g * Exp (t • v)) = f g := by
  obtain ⟨n, hn⟩ := exists_nat_gt (max (t / T) 0)
  have hnpos : (0 : ℝ) < n := lt_of_le_of_lt (le_max_right _ _) hn
  have hn0 : (n : ℝ) ≠ 0 := hnpos.ne'
  have hδ : t / n ∈ Icc (0 : ℝ) T := by
    refine ⟨div_nonneg ht hnpos.le, (div_le_iff₀ hnpos).mpr ?_⟩
    have hlt : t / T < n := lt_of_le_of_lt (le_max_left _ _) hn
    exact (le_of_lt ((div_lt_iff₀ hT).mp hlt)).trans_eq (mul_comm _ _)
  have he (k : ℕ) (hk : k ≤ n) : f (g * Exp (((k : ℝ) * (t / n)) • v)) = f g := by
    induction k with
    | zero => simp [hExp0]
    | succ k ih =>
      have hk' : k ≤ n := (Nat.le_succ k).trans hk
      have hbase : g * Exp (((k : ℝ) * (t / n)) • v) ∈ U := by
        have hr : (k : ℝ) / n ∈ Icc (0 : ℝ) 1 := by
          refine ⟨div_nonneg (Nat.cast_nonneg k) hnpos.le, ?_⟩
          exact (div_le_one hnpos).mpr (by exact_mod_cast hk')
        have h := hstay ((k : ℝ) / n) hr
        simpa only [smul_smul, div_mul_eq_mul_div, mul_div_assoc] using h
      have hs := hstep _ hbase _ hδ
      rw [mul_assoc, ← hadd] at hs
      have hnum : (k : ℝ) * (t / n) + t / n = ((k + 1 : ℕ) : ℝ) * (t / n) := by
        push_cast
        ring
      rw [hnum] at hs
      exact hs.trans (ih hk')
  have h := he n le_rfl
  have hcancel : (n : ℝ) * (t / n) = t := by field_simp
  simpa only [hcancel] using h

theorem eq_on_flow_of_small_steps
    (f : G → W) (U : Set G) (Exp : V → G) (hExp0 : Exp 0 = 1)
    (hadd : ∀ v (s t : ℝ), Exp ((s + t) • v) = Exp (s • v) * Exp (t • v))
    (v : V) {T : ℝ} (hT : 0 < T)
    (hstep : ∀ g ∈ U, ∀ s ∈ Icc 0 T, f (g * Exp (s • v)) = f g)
    {g : G} {t : ℝ} (hstay : g ∈ flowLineBase U Exp (t • v) 1) :
    f (g * Exp (t • v)) = f g := by
  by_cases ht : 0 ≤ t
  · exact eq_on_positive_flow_of_small_steps f U Exp hExp0 hadd v hT hstep ht hstay
  · have ht' : 0 ≤ -t := neg_nonneg.mpr (le_of_not_ge ht)
    have hback : g * Exp (t • v) ∈ flowLineBase U Exp ((-t) • v) 1 := by
      intro r hr
      have h := hstay (1 - r) (show 1 - r ∈ Icc (0 : ℝ) 1 by
        constructor <;> linarith [hr.1, hr.2])
      have he : (g * Exp (t • v)) * Exp (r • ((-t) • v)) =
          g * Exp ((1 - r) • (t • v)) := by
        have hscalar : t + r * (-t) = (1 - r) * t := by ring
        rw [smul_smul, smul_smul, mul_assoc, ← hadd, hscalar]
      rwa [he]
    have h := eq_on_positive_flow_of_small_steps f U Exp hExp0 hadd v hT hstep ht' hback
    have he : (g * Exp (t • v)) * Exp ((-t) • v) = g := by
      rw [mul_assoc, ← hadd]
      simp [hExp0]
    rw [he] at h
    exact h.symm

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_FiniteFlowSlopes
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite derivative labels give finite, locally constant flow slopes -/

noncomputable section

namespace PolycyclicRecognition

open MeasureTheory Set Filter
open scoped NNReal

theorem ae_affine_flowLine_mem_of_joint_derivative_agreement
    {G V W I : Type*} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    [MeasurableSpace G] [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (μ : Measure G) [SFinite μ] (Exp : V → G) (hExp0 : Exp 0 = 1)
    (v : V) (U : Set G) (f q : G → W)
    (α : I → W →L[ℝ] ℝ) (hsep : ∀ w : W, (∀ i, α i w = 0) → w = 0)
    {T : ℝ} (hT : 0 < T) {C : ℝ≥0}
    (hlip : ∀ g ∈ flowLineBase U Exp v T,
      LipschitzOnWith C (fun t => f (g * Exp (t • v))) (Icc 0 T))
    (hderiv : ∀ᵐ g ∂μ, g ∈ flowLineBase U Exp v T →
      ∀ᵐ t ∂volume.restrict (Icc 0 T),
        HasDerivAt (fun s => f (g * Exp (s • v))) (q (g * Exp (t • v))) t)
    (hpair : ∀ᵐ z ∂(pairTimeMeasure.prod μ).restrict (flowSegmentDomain U Exp v),
      q (z.2 * Exp (z.1.1 • v)) = q (z.2 * Exp (z.1.2 • v)))
    {E : Set W} (hq : ∀ g ∈ U, q g ∈ E) :
    ∀ᵐ g ∂μ, g ∈ flowLineBase U Exp v T →
      ∃ u ∈ E, ∀ t ∈ Icc 0 T, f (g * Exp (t • v)) = f g + t • u := by
  filter_upwards [hderiv, ae_flowLine_pair_relation μ Exp v U q Eq hpair T] with g hd hp
  intro hstay
  have hqline : ∀ᵐ t ∂volume.restrict (Icc 0 T), q (g * Exp (t • v)) ∈ E := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    exact hq _ (hstay t ht)
  obtain ⟨u, huE, hu⟩ := exists_affine_mem_of_lipschitz_pairwise_derivative α hsep hT
    (hlip g hstay) (hd hstay) (hp hstay) hqline
  exact ⟨u, huE, fun t ht => by simpa only [zero_smul, hExp0, mul_one] using hu t ht⟩

theorem finite_flowLine_slopes
    {G V W I : Type*} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    [MeasurableSpace G] [OpensMeasurableSpace G]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (μ : Measure G) [SFinite μ] [μ.IsOpenPosMeasure]
    (Exp : V → G) (hExp : Continuous Exp) (hExp0 : Exp 0 = 1)
    (v : V) (U : Set G) (hU : IsOpen U) (f q : G → W) (hf : ContinuousOn f U)
    (α : I → W →L[ℝ] ℝ) (hsep : ∀ w : W, (∀ i, α i w = 0) → w = 0)
    {T : ℝ} (hT : 0 < T) {C : ℝ≥0}
    (hlip : ∀ g ∈ flowLineBase U Exp v T,
      LipschitzOnWith C (fun t => f (g * Exp (t • v))) (Icc 0 T))
    (hderiv : ∀ᵐ g ∂μ, g ∈ flowLineBase U Exp v T →
      ∀ᵐ t ∂volume.restrict (Icc 0 T),
        HasDerivAt (fun s => f (g * Exp (s • v))) (q (g * Exp (t • v))) t)
    (hpair : ∀ᵐ z ∂(pairTimeMeasure.prod μ).restrict (flowSegmentDomain U Exp v),
      q (z.2 * Exp (z.1.1 • v)) = q (z.2 * Exp (z.1.2 • v)))
    {E : Set W} (hE : E.Finite) (hq : ∀ g ∈ U, q g ∈ E) :
    (∀ g ∈ flowLineBase U Exp v T, ∀ t ∈ Icc 0 T,
      f (g * Exp (t • v)) = f g + t • flowLineSlope f Exp v T g) ∧
    MapsTo (flowLineSlope f Exp v T) (flowLineBase U Exp v T) E := by
  have hae := ae_affine_flowLine_mem_of_joint_derivative_agreement μ Exp hExp0 v U f q
    α hsep hT hlip hderiv hpair hq
  refine ⟨flowLine_affinity_of_ae μ hU hExp hExp0 hT hf ?_,
    flowLineSlope_mem_of_ae μ hU hExp hExp0 hT hf hE.isClosed hae⟩
  filter_upwards [hae] with g hg hbase
  obtain ⟨u, _, hu⟩ := hg hbase
  exact ⟨u, hu⟩

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_LocalFlowLabel
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # One finite label on a connected family of admissible flow lines -/

noncomputable section

namespace PolycyclicRecognition

open MeasureTheory Set Filter

theorem exists_label_of_continuous_slopes
    {X W J L : Type*} [TopologicalSpace X] [MeasurableSpace X]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [Fintype J] [Finite L]
    (μ : Measure X) [μ.IsOpenPosMeasure]
    {U : Set X} (hU : IsOpen U) (hconn : IsPreconnected U) (hne : U.Nonempty)
    (c : X → J → W) (hc : ∀ j, ContinuousOn (fun x => c x j) U)
    (A : L → J → W)
    (hae : ∀ᵐ x ∂μ, x ∈ U → ∃ l, ∀ j, c x j = A l j) :
    ∃ l, ∀ x ∈ U, ∀ j, c x j = A l j := by
  have hc' : ContinuousOn c U := continuousOn_pi.mpr hc
  have hmaps : MapsTo c U (range A) := by
    apply mapsTo_closed_of_ae μ hU hc' (finite_range A).isClosed
    filter_upwards [hae] with x hx hxU
    obtain ⟨l, hl⟩ := hx hxU
    exact ⟨l, (funext hl).symm⟩
  obtain ⟨x, hx⟩ := hne
  obtain ⟨l, hl⟩ := hmaps hx
  refine ⟨l, ?_⟩
  intro y hy j
  have he := hconn.constant_of_mapsTo (finite_range A).isDiscrete hc' hmaps hy hx
  exact congrFun (he.trans hl.symm) j

theorem flowLineSlope_eq_of_hasDerivAt
    {G V W : Type*} [Group G] [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (f : G → W) (Exp : V → G) (hExp0 : Exp 0 = 1) (v : V) (g : G)
    {T : ℝ} (hT : 0 < T) {q : W}
    (hline : ∀ t ∈ Icc 0 T,
      f (g * Exp (t • v)) = f g + t • flowLineSlope f Exp v T g)
    (hd : HasDerivAt (fun t : ℝ => f (g * Exp (t • v))) q 0) :
    flowLineSlope f Exp v T g = q := by
  have ha : HasDerivAt (fun t : ℝ => f g + t • flowLineSlope f Exp v T g)
      (flowLineSlope f Exp v T g) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const
      (flowLineSlope f Exp v T g)).const_add (f g)
  have hb := ha.hasDerivWithinAt.congr hline (by simp [hExp0])
  exact (uniqueDiffOn_Icc hT 0 ⟨le_rfl, hT.le⟩).eq_deriv _ hb hd.hasDerivWithinAt

theorem exists_single_label_on_flow_neighborhood
    {G V W J L : Type*} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    [MeasurableSpace G] [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [Fintype J] [Finite L]
    (μ : Measure G) [μ.IsOpenPosMeasure]
    (Exp : V → G) (hExp : Continuous Exp) (hExp0 : Exp 0 = 1)
    (v : J → V) (A : L → V →L[ℝ] W)
    (Ω U : Set G) (hU : IsOpen U) (hconn : IsPreconnected U) (hne : U.Nonempty)
    (f : G → W) (hf : ContinuousOn f Ω) {T : ℝ} (hT : 0 < T)
    (hstay : ∀ j, U ⊆ flowLineBase Ω Exp (v j) T)
    (hline : ∀ j g, g ∈ U → ∀ t ∈ Icc 0 T,
      f (g * Exp (t • v j)) = f g + t • flowLineSlope f Exp (v j) T g)
    (hderiv : ∀ᵐ g ∂μ, g ∈ U → ∃ l, ∀ j,
      HasDerivAt (fun t : ℝ => f (g * Exp (t • v j))) (A l (v j)) 0) :
    ∃ l, ∀ g ∈ U, ∀ j t, t ∈ Icc 0 T →
      f (g * Exp (t • v j)) = f g + t • A l (v j) := by
  have hc (j : J) : ContinuousOn (fun g => flowLineSlope f Exp (v j) T g) U :=
    (continuousOn_flowLineSlope hExp hExp0 hT.le hf).mono (hstay j)
  have hlabels : ∀ᵐ g ∂μ, g ∈ U → ∃ l, ∀ j,
      flowLineSlope f Exp (v j) T g = A l (v j) := by
    filter_upwards [hderiv] with g hg hgU
    obtain ⟨l, hl⟩ := hg hgU
    exact ⟨l, fun j => flowLineSlope_eq_of_hasDerivAt f Exp hExp0 (v j) g
      hT (hline j g hgU) (hl j)⟩
  obtain ⟨l, hl⟩ := exists_label_of_continuous_slopes μ hU hconn hne
    (fun g j => flowLineSlope f Exp (v j) T g) hc (fun l j => A l (v j)) hlabels
  refine ⟨l, ?_⟩
  intro g hg j t ht
  rw [hline j g hg t ht, hl g hg j]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_LocalProfileAffinity
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.basisDynkinParameter_zero _root_.OAI.PolycyclicRecognition.dynkinRightTranslation_apply _root_.OAI.PolycyclicRecognition.dynkinRightTranslation_symm_apply _root_.OAI.PolycyclicRecognition.exponentialHomOfDynkin_apply_exp _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Local profile affinity from the actual finite flow labels

The proof uses admissible generator words and the inverse function theorem;
it does not assume a smooth profile or a hypoellipticity conclusion.
-/

noncomputable section

namespace PolycyclicRecognition

open Set MeasureTheory Module

variable {V W I J : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] [Fintype I]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  {c : ℕ} (a : DynkinCoefficients c 2) (B : V →L[ℝ] V →L[ℝ] V)
  (hB : IsLieBracket B) (hg : PolynomialGroupLaws (dynkinProduct a B))
  (hc : ExponentialConjugationLaw (dynkinProduct a B) B)
  (X : I → V) (b₀ : Basis J ℝ V) (w₀ : J → FreeMagma I)
  (hw₀ : ∀ j, evalBilinearWord B X (w₀ j) = b₀ j)

include hB hc hw₀

theorem affine_of_small_generator_increments
    (U : Set (PolynomialCoordinateGroup (dynkinProduct a B) hg))
    (hU : IsOpen U) (hconn : IsPreconnected U) (hne : U.Nonempty)
    (f : PolynomialCoordinateGroup (dynkinProduct a B) hg → W)
    (π : PolynomialCoordinateGroup (dynkinProduct a B) hg →* Multiplicative W)
    (p : V →L[ℝ] W)
    (hπExp : ∀ v, (π (PolynomialCoordinateGroup.exp _ hg v)).toAdd = p v)
    (A : W →L[ℝ] W) {T : ℝ} (hT : 0 < T)
    (hstep : ∀ g ∈ U, ∀ i s, s ∈ Icc 0 T →
      f (g * PolynomialCoordinateGroup.exp _ hg (s • X i)) = f g + s • A (p (X i))) :
    ∃ b : W, ∀ g ∈ U, f g = A (π g).toAdd + b := by
  let Exp := PolynomialCoordinateGroup.exp (dynkinProduct a B) hg
  let F := fun g => f g - A (π g).toAdd
  have hFstep (i : I) (g) (hgU : g ∈ U) (s : ℝ) (hs : s ∈ Icc 0 T) :
      F (g * Exp (s • X i)) = F g := by
    have hp : (π (g * Exp (s • X i))).toAdd = (π g).toAdd + s • p (X i) := by
      rw [map_mul]
      change (π g).toAdd + (π (Exp (s • X i))).toAdd = _
      rw [hπExp, map_smul]
    dsimp [F]
    rw [hstep g hgU i s hs, hp, map_add, map_smul]
    abel
  have hflow (i : I) (g) (t : ℝ)
      (hst : g ∈ flowLineBase U Exp (t • X i) 1) : F (g * Exp (t • X i)) = F g :=
    eq_on_flow_of_small_steps F U Exp (by rfl)
      (PolynomialCoordinateGroup.exp_add_smul _ hg) (X i) hT (hFstep i) hst
  obtain ⟨x, hx⟩ := hne
  refine ⟨F x, ?_⟩
  intro g hgU
  have he : F g = F x := eq_of_generator_flow_invariance a B hB hg hc X b₀ w₀ hw₀
    U hU hconn F hflow hgU hx
  exact (sub_eq_iff_eq_add.mp he).trans (add_comm _ _)

theorem affine_on_flow_neighborhood
    {L : Type*} [Finite L]
    [MeasurableSpace (PolynomialCoordinateGroup (dynkinProduct a B) hg)]
    (μ : Measure (PolynomialCoordinateGroup (dynkinProduct a B) hg)) [μ.IsOpenPosMeasure]
    (Ω U : Set (PolynomialCoordinateGroup (dynkinProduct a B) hg))
    (hU : IsOpen U) (hconn : IsPreconnected U) (hne : U.Nonempty)
    (f : PolynomialCoordinateGroup (dynkinProduct a B) hg → W) (hf : ContinuousOn f Ω)
    (π : PolynomialCoordinateGroup (dynkinProduct a B) hg →* Multiplicative W)
    (p : V →L[ℝ] W)
    (hπExp : ∀ v, (π (PolynomialCoordinateGroup.exp _ hg v)).toAdd = p v)
    (A : L → W →L[ℝ] W) {T : ℝ} (hT : 0 < T)
    (hstay : ∀ i, U ⊆ flowLineBase Ω (PolynomialCoordinateGroup.exp _ hg) (X i) T)
    (hline : ∀ i g, g ∈ U → ∀ t ∈ Icc 0 T,
      f (g * PolynomialCoordinateGroup.exp _ hg (t • X i)) =
        f g + t • flowLineSlope f (PolynomialCoordinateGroup.exp _ hg) (X i) T g)
    (hderiv : ∀ᵐ g ∂μ, g ∈ U → ∃ l, ∀ i,
      HasDerivAt (fun t : ℝ => f (g * PolynomialCoordinateGroup.exp _ hg (t • X i)))
        (A l (p (X i))) 0) :
    ∃ l b, ∀ g ∈ U, f g = A l (π g).toAdd + b := by
  let : IsTopologicalGroup (PolynomialCoordinateGroup (dynkinProduct a B) hg) :=
    PolynomialCoordinateGroup.isTopologicalGroup _ hg
      (continuous_dynkinProduct a (fun _ => B) Prod.fst Prod.snd
        continuous_const continuous_fst continuous_snd)
  obtain ⟨l, hl⟩ := exists_single_label_on_flow_neighborhood
    (G := PolynomialCoordinateGroup (dynkinProduct a B) hg) μ
    (PolynomialCoordinateGroup.exp (dynkinProduct a B) hg)
    (PolynomialCoordinateGroup.expHomeomorph _ hg).continuous (by rfl)
    X (fun l => (A l).comp p) Ω U hU hconn hne f hf hT hstay hline hderiv
  obtain ⟨b, hb⟩ := affine_of_small_generator_increments a B hB hg hc X b₀ w₀ hw₀
    U hU hconn hne f π p hπExp (A l) hT (fun g hg i s hs => hl g hg i s hs)
  exact ⟨l, b, hb⟩

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_AffineProfileGluing
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Local affine height formulas agree on a connected open domain -/

noncomputable section

namespace PolycyclicRecognition

open Set Filter
open scoped Topology

theorem affine_parameters_eq_on_open
    {W Z : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    {U : Set W} (hU : IsOpen U) (hne : U.Nonempty)
    (A B : W →L[ℝ] Z) (b c : Z)
    (heq : ∀ x ∈ U, A x + b = B x + c) : A = B ∧ b = c := by
  obtain ⟨x, hx⟩ := hne
  have hfg : (fun y => A y + b) =ᶠ[𝓝 x] (fun y => B y + c) := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact heq y hy
  have hA := (A.hasFDerivAt (x := x)).add_const b
  have hB := (B.hasFDerivAt (x := x)).add_const c
  have hAB : A = B := (hA.congr_of_eventuallyEq hfg.symm).unique hB
  refine ⟨hAB, ?_⟩
  have h := heq x hx
  rw [hAB] at h
  exact add_left_cancel h

theorem exists_global_affine_of_local
    {G W Z L : Type*} [TopologicalSpace G]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (π : G → W) (hπ : IsOpenMap π) (A : L → W →L[ℝ] Z) (f : G → Z)
    {U : Set G} (hconn : IsPreconnected U) (hne : U.Nonempty)
    (hlocal : ∀ x ∈ U, ∃ N : Set G, IsOpen N ∧ x ∈ N ∧ N ⊆ U ∧
      ∃ l b, ∀ y ∈ N, f y = A l (π y) + b) :
    ∃ l b, ∀ x ∈ U, f x = A l (π x) + b := by
  classical
  have hchoices (x : U) := hlocal x.val x.property
  choose N hNo hNx hNU l b he using hchoices
  let C : U → (W →L[ℝ] Z) × Z := fun x => (A (l x), b x)
  have hC : IsLocallyConstant C := by
    apply (IsLocallyConstant.iff_eventually_eq _).mpr
    intro x
    have hnear : ∀ᶠ y : U in 𝓝 x, y.val ∈ N x :=
      continuous_subtype_val.continuousAt.tendsto.eventually ((hNo x).mem_nhds (hNx x))
    filter_upwards [hnear] with y hy
    have ho : IsOpen (π '' (N y ∩ N x)) := hπ _ ((hNo y).inter (hNo x))
    have hn : (π '' (N y ∩ N x)).Nonempty := ⟨π y, y, ⟨hNx y, hy⟩, rfl⟩
    have hsame := affine_parameters_eq_on_open ho hn (A (l y)) (A (l x)) (b y) (b x) (by
      rintro z ⟨g, hg, rfl⟩
      exact (he y g hg.1).symm.trans (he x g hg.2))
    exact Prod.ext hsame.1 hsame.2
  let : PreconnectedSpace U := Subtype.preconnectedSpace hconn
  obtain ⟨x, hx⟩ := hne
  let x₀ : U := ⟨x, hx⟩
  refine ⟨l x₀, b x₀, ?_⟩
  intro y hy
  let y₀ : U := ⟨y, hy⟩
  have hsame := hC.apply_eq_of_preconnectedSpace y₀ x₀
  have hlin : A (l y₀) = A (l x₀) := congrArg Prod.fst hsame
  have hoff : b y₀ = b x₀ := congrArg Prod.snd hsame
  have hyformula := he y₀ y (hNx y₀)
  rw [hlin, hoff] at hyformula
  exact hyformula

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_GlobalProfileAffinity
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Affine flow lines and finite derivative labels give global profile affinity -/

noncomputable section

namespace PolycyclicRecognition

open Set MeasureTheory Module

theorem global_affine_of_finite_derivative_and_flow_lines
    {V W I J L : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [Fintype I] [Finite L]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
    {c : ℕ} (a : DynkinCoefficients c 2) (B : V →L[ℝ] V →L[ℝ] V)
    (hB : IsLieBracket B) (hg : PolynomialGroupLaws (dynkinProduct a B))
    (hc : ExponentialConjugationLaw (dynkinProduct a B) B)
    (X : I → V) (b₀ : Basis J ℝ V) (w₀ : J → FreeMagma I)
    (hw₀ : ∀ j, evalBilinearWord B X (w₀ j) = b₀ j)
    [MeasurableSpace (PolynomialCoordinateGroup (dynkinProduct a B) hg)]
    (μ : Measure (PolynomialCoordinateGroup (dynkinProduct a B) hg)) [μ.IsOpenPosMeasure]
    (Ω : Set (PolynomialCoordinateGroup (dynkinProduct a B) hg))
    (hΩ : IsOpen Ω) (hconn : IsPreconnected Ω) (hne : Ω.Nonempty)
    (f : PolynomialCoordinateGroup (dynkinProduct a B) hg → W) (hf : ContinuousOn f Ω)
    (π : PolynomialCoordinateGroup (dynkinProduct a B) hg →* Multiplicative W)
    (p : V →L[ℝ] W) (hp : Function.Surjective p)
    (hπExp : ∀ v, (π (PolynomialCoordinateGroup.exp _ hg v)).toAdd = p v)
    (A : L → W →L[ℝ] W)
    (hline : ∀ i T, 0 < T → ∀ g ∈ flowLineBase Ω (PolynomialCoordinateGroup.exp _ hg) (X i) T,
      ∀ t ∈ Icc 0 T, f (g * PolynomialCoordinateGroup.exp _ hg (t • X i)) =
        f g + t • flowLineSlope f (PolynomialCoordinateGroup.exp _ hg) (X i) T g)
    (hderiv : ∀ᵐ g ∂μ, g ∈ Ω → ∃ l, ∀ i,
      HasDerivAt (fun t : ℝ => f (g * PolynomialCoordinateGroup.exp _ hg (t • X i)))
        (A l (p (X i))) 0) :
    ∃ l b, ∀ g ∈ Ω, f g = A l (π g).toAdd + b := by
  let G := PolynomialCoordinateGroup (dynkinProduct a B) hg
  let e : V ≃ₜ G := PolynomialCoordinateGroup.expHomeomorph _ hg
  let : IsTopologicalGroup G := PolynomialCoordinateGroup.isTopologicalGroup _ hg
    (continuous_dynkinProduct a (fun _ => B) Prod.fst Prod.snd
      continuous_const continuous_fst continuous_snd)
  let : LocallyConnectedSpace G := e.symm.isOpenEmbedding.locallyConnectedSpace
  have hπopen : IsOpenMap (fun g : G => (π g).toAdd) := by
    have heq : (fun g : G => (π g).toAdd) = p ∘ e.symm := by
      funext g
      have h := hπExp (e.symm g)
      change (π (e (e.symm g))).toAdd = p (e.symm g) at h
      simpa only [e.apply_symm_apply, Function.comp_apply] using h
    rw [heq]
    exact (p.toLinearMap.isOpenMap_of_finiteDimensional hp).comp e.symm.isOpenMap
  apply exists_global_affine_of_local (fun g => (π g).toAdd) hπopen A f hconn hne
  intro g hgΩ
  obtain ⟨T, hT, N, hNo, hgN, hNc, hNΩ, hstay⟩ :=
    exists_connected_flow_neighborhood Ω hΩ (PolynomialCoordinateGroup.exp _ hg)
      e.continuous (by rfl) X hgΩ
  have hd : ∀ᵐ x ∂μ, x ∈ N → ∃ l, ∀ i,
      HasDerivAt (fun t : ℝ => f (x * PolynomialCoordinateGroup.exp _ hg (t • X i)))
        (A l (p (X i))) 0 := by
    filter_upwards [hderiv] with x hx hxN
    exact hx (hNΩ hxN)
  obtain ⟨l, b, hab⟩ := affine_on_flow_neighborhood a B hB hg hc X b₀ w₀ hw₀
    μ Ω N hNo hNc.isPreconnected hNc.nonempty f hf π p hπExp A hT hstay
    (fun i x hx t ht => hline i T hT x (hstay i hx) t ht) hd
  exact ⟨N, hNo, hgN, hNΩ, l, b, hab⟩

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_ExtremeFlowAffinity
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_countable _root_.OAI.PolycyclicRecognition.finitelyGeneratedSubgroupIndex_countable _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteRootOffsetConeIndex _root_.OAI.PolycyclicRecognition.instNonemptyRootOffsetConeIndex _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.CartanWordModel.supportDatum_weight _root_.OAI.PolycyclicRecognition.SupportDatum.transport_weight_apply _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Affine restrictions in kernel and extreme horizontal directions -/

noncomputable section

namespace PolycyclicRecognition.SupportDatum

open Set Filter MeasureTheory
open scoped NNReal

theorem flowLine_affine_in_extreme_or_kernel_direction
    {G V W I B L : Type*} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
    [TopologicalSpace.PseudoMetrizableSpace G] [MeasurableSpace G] [BorelSpace G]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
    [Fintype I] [Fintype B] [Nonempty B]
    [Fintype L] [MeasurableSpace L] [MeasurableSingletonClass L]
    (D : SupportDatum W I B) (hweights : ∀ i, D.weight i ≠ 0)
    (μ : Measure G) [μ.IsHaarMeasure] [μ.IsMulRightInvariant]
    (Exp : V → G) (hExp : Continuous Exp) (hzero : Exp 0 = 1)
    (hadd : ∀ v (s t : ℝ), Exp ((s + t) • v) = Exp (s • v) * Exp (t • v))
    (π : V →L[ℝ] W) (hπ : Function.Surjective π)
    (f : G → W) (hf : Continuous f) (U : Set G) (hU : IsOpen U)
    (label : G → L) (hlabel : Measurable label) (A : L → templateSymmetryGroup D)
    (hbase : ∀ v, ∀ᵐ g ∂μ, g ∈ U → HasDerivAt (fun t : ℝ => f (g * Exp (t • v)))
      ((A (label g)).val (π v)) 0)
    (C : V → ℝ≥0)
    (hlip : ∀ v g, LipschitzOnWith (C v) (fun t : ℝ => f (g * Exp (t • v)))
      {t | g * Exp (t • v) ∈ U})
    (hvol : ∀ v (T : ℝ), 0 < T → ∀ g ∈ flowLineBase U Exp v T,
      T * D.segmentSupport (π v) ≤ D.templateSupport ((fun t : ℝ => f (g * Exp (t • v))) '' Icc 0 T))
    (σ : I → Bool) (hσ : (weightChamber (fun i => (D.weight i).toContinuousLinearMap) σ).Nonempty)
    (v : V) (hv : π v = 0 ∨ π v ∈ chamberExtremeDirections
      (fun i => (D.weight i).toContinuousLinearMap) σ)
    {T : ℝ} (hT : 0 < T) :
    ∀ g ∈ flowLineBase U Exp v T, ∀ t ∈ Icc 0 T,
      f (g * Exp (t • v)) = f g + t • flowLineSlope f Exp v T g := by
  let q : G → W := fun g => (A (label g)).val (π v)
  have hpair : ∀ᵐ z ∂(pairTimeMeasure.prod μ).restrict (flowSegmentDomain U Exp v),
      q (z.2 * Exp (z.1.1 • v)) = q (z.2 * Exp (z.1.2 • v)) := by
    rcases hv with hv | hv
    · exact Eventually.of_forall (fun _ => by simp [q, hv])
    · apply D.extreme_template_derivative_values_equal hweights μ π hπ Exp hExp
        label hlabel A U hU v σ hσ hv.2
      intro τ _ u hu
      have hw := generic_of_mem_weightChamber
        (fun i => (D.weight i).toContinuousLinearMap) hu
      have he := weightSigns_eq_of_mem_chamber
        (fun i => (D.weight i).toContinuousLinearMap) hu
      have hh := ae_imp_of_ae_restrict (D.ae_generic_joint_chamber_agreement hweights μ
        Exp hExp hzero hadd π u hw f hf U hU label hlabel A (hbase u)
        (C u) (hlip u) (hvol u))
      simpa only [he] using hh
  exact (finite_flowLine_slopes μ Exp hExp hzero v U hU f q hf.continuousOn
    (fun i => (D.weight i).toContinuousLinearMap) D.separates hT
    (fun g hg => (hlip v g).mono hg)
    (ae_flowLine_hasDerivAt_of_ae_base μ Exp hExp hadd v f q U (hbase v) T)
    hpair (Set.finite_range (fun l => (A l).val (π v)))
    (fun g _ => ⟨label g, rfl⟩)).1

end PolycyclicRecognition.SupportDatum

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_AffineFromHorizontalLabels
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_countable _root_.OAI.PolycyclicRecognition.finitelyGeneratedSubgroupIndex_countable _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteRootOffsetConeIndex _root_.OAI.PolycyclicRecognition.instNonemptyRootOffsetConeIndex _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.basisDynkinParameter_zero _root_.OAI.PolycyclicRecognition.dynkinRightTranslation_apply _root_.OAI.PolycyclicRecognition.dynkinRightTranslation_symm_apply _root_.OAI.PolycyclicRecognition.exponentialHomOfDynkin_apply_exp _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Measurable horizontal labels and segment volume force a single affine profile -/

noncomputable section

namespace PolycyclicRecognition

open Set Filter MeasureTheory Module
open scoped NNReal

theorem affine_of_horizontal_labels_oai
    {H V W I B K J L : Type*}
    [NormedAddCommGroup H] [NormedSpace ℝ H] [FiniteDimensional ℝ H]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V]
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
    [Fintype I] [Fintype B] [Nonempty B]
    [Fintype L] [MeasurableSpace L] [MeasurableSingletonClass L]
    {c : ℕ} (a : DynkinCoefficients c 2) (br : V →L[ℝ] V →L[ℝ] V)
    (hbr : IsLieBracket br) (hg : PolynomialGroupLaws (dynkinProduct a br))
    (hc : ExponentialConjugationLaw (dynkinProduct a br) br)
    (D : H →L[ℝ] V) (X : K → H) (b₀ : Basis J ℝ V) (w₀ : J → FreeMagma K)
    (hw₀ : ∀ j, evalBilinearWord br (fun k => D (X k)) (w₀ j) = b₀ j)
    (μ : Measure (PolynomialCoordinateGroup (dynkinProduct a br) hg))
    [μ.IsHaarMeasure] [μ.IsMulRightInvariant]
    (Ω : Set (PolynomialCoordinateGroup (dynkinProduct a br) hg))
    (hΩ : IsOpen Ω) (hconn : IsPreconnected Ω) (hne : Ω.Nonempty)
    (f : PolynomialCoordinateGroup (dynkinProduct a br) hg → W) (hf : Continuous f)
    (π : PolynomialCoordinateGroup (dynkinProduct a br) hg →* Multiplicative W)
    (p : V →L[ℝ] W) (hp : Function.Surjective (p.comp D))
    (hπExp : ∀ v, (π (PolynomialCoordinateGroup.exp _ hg v)).toAdd = p v)
    (P : SupportDatum W I B) (hweights : ∀ i, P.weight i ≠ 0)
    (σ : I → Bool) (hσ : (weightChamber (fun i => (P.weight i).toContinuousLinearMap) σ).Nonempty)
    (label : PolynomialCoordinateGroup (dynkinProduct a br) hg → L)
    (hlabel : Measurable label) (A : L → templateSymmetryGroup P)
    (hbase : ∀ v : H, ∀ᵐ g ∂μ, g ∈ Ω →
      HasDerivAt (fun t : ℝ => f (g * PolynomialCoordinateGroup.exp _ hg (t • D v)))
        ((A (label g)).val (p (D v))) 0)
    (C : H → ℝ≥0)
    (hlip : ∀ v g, LipschitzOnWith (C v)
      (fun t : ℝ => f (g * PolynomialCoordinateGroup.exp _ hg (t • D v)))
      {t | g * PolynomialCoordinateGroup.exp _ hg (t • D v) ∈ Ω})
    (hvol : ∀ v (T : ℝ), 0 < T →
      ∀ g ∈ flowLineBase Ω (PolynomialCoordinateGroup.exp _ hg) (D v) T,
        T * P.segmentSupport (p (D v)) ≤ P.templateSupport
          ((fun t : ℝ => f (g * PolynomialCoordinateGroup.exp _ hg (t • D v))) '' Icc 0 T)) :
    ∃ l b, ∀ g ∈ Ω, f g = (A l).val ((π g).toAdd) + b := by
  let G := PolynomialCoordinateGroup (dynkinProduct a br) hg
  let e : V ≃ₜ G := PolynomialCoordinateGroup.expHomeomorph _ hg
  let : IsTopologicalGroup G := PolynomialCoordinateGroup.isTopologicalGroup _ hg
    (continuous_dynkinProduct a (fun _ => br) Prod.fst Prod.snd
      continuous_const continuous_fst continuous_snd)
  let : T2Space G := inferInstanceAs (T2Space V)
  let : LocallyCompactSpace G := inferInstanceAs (LocallyCompactSpace V)
  let : SecondCountableTopology G := inferInstanceAs (SecondCountableTopology V)
  let : TopologicalSpace.PseudoMetrizableSpace G :=
    inferInstanceAs (TopologicalSpace.PseudoMetrizableSpace V)
  have he_apply (v : V) : e v = PolynomialCoordinateGroup.exp _ hg v := rfl
  let eH : H → G := fun v => e (D v)
  have heH : Continuous eH := e.continuous.comp D.continuous
  have he0 : eH 0 = 1 := by simp only [eH, map_zero, he_apply, PolynomialCoordinateGroup.exp_zero]
  have headd (v : H) (s t : ℝ) : eH ((s + t) • v) = eH (s • v) * eH (t • v) := by
    simpa only [eH, he_apply, map_smul] using PolynomialCoordinateGroup.exp_add_smul _ hg (D v) s t
  obtain ⟨S, hS, hdir⟩ := exists_finite_spanning_horizontal_directions (p.comp D) hp
    (fun i => (P.weight i).toContinuousLinearMap) σ P.separates hσ
  let Y : S → H := fun v => v.val
  have hY : Submodule.span ℝ (range Y) = ⊤ := by
    have heq : range Y = (S : Set H) := by ext v; simp [Y]
    rwa [heq]
  obtain ⟨b₁, w₁, hw₁⟩ := exists_word_basis_of_spanning_horizontal br hbr D X b₀ w₀ hw₀ Y hY
  have hps : Function.Surjective p := by
    intro w
    obtain ⟨v, hv⟩ := hp w
    exact ⟨D v, hv⟩
  apply global_affine_of_finite_derivative_and_flow_lines a br hbr hg hc
    (fun v : S => D (Y v)) b₁ w₁ hw₁ μ Ω hΩ hconn hne f hf.continuousOn π p hps
    hπExp (fun l => (A l).val.toLinearMap.toContinuousLinearMap)
  · intro v T hT
    have hb (u : H) : ∀ᵐ g ∂μ, g ∈ Ω →
        HasDerivAt (fun t : ℝ => f (g * eH (t • u)))
          ((A (label g)).val ((p.comp D) u)) 0 := by
      simpa only [eH, he_apply, map_smul,
        ContinuousLinearMap.comp_apply] using hbase u
    have hl (u : H) (g : G) : LipschitzOnWith (C u)
        (fun t : ℝ => f (g * eH (t • u))) {t | g * eH (t • u) ∈ Ω} := by
      simpa only [eH, he_apply, map_smul] using hlip u g
    have hv (u : H) (T : ℝ) (hT : 0 < T) : ∀ g ∈ flowLineBase Ω eH u T,
        T * P.segmentSupport ((p.comp D) u) ≤
          P.templateSupport ((fun t : ℝ => f (g * eH (t • u))) '' Icc 0 T) := by
      simpa only [eH, he_apply, flowLineBase, map_smul,
        ContinuousLinearMap.comp_apply] using hvol u T hT
    have hline := P.flowLine_affine_in_extreme_or_kernel_direction hweights μ eH heH he0
      headd (p.comp D) hp f hf Ω hΩ label hlabel A hb C hl hv σ hσ (Y v)
      (hdir v.val v.property) hT
    simpa only [eH, he_apply, flowLineBase, flowLineSlope,
      map_smul] using hline
  · have hall : ∀ᵐ g ∂μ, ∀ v : S, g ∈ Ω →
        HasDerivAt (fun t : ℝ => f (g * PolynomialCoordinateGroup.exp _ hg (t • D (Y v))))
          ((A (label g)).val (p (D (Y v)))) 0 := ae_all_iff.mpr (fun v => hbase (Y v))
    filter_upwards [hall] with g hg hgΩ
    exact ⟨label g, fun v => hg v hgΩ⟩

end PolycyclicRecognition

end

end OAI
end

theorem solution.{u_1, u_2, u_3, u_4, u_5, u_6, u_7, u_8} : type_of% @OAI.PolycyclicRecognition.affine_of_horizontal_labels_oai.{u_1, u_2, u_3, u_4, u_5, u_6, u_7, u_8} := @OAI.PolycyclicRecognition.affine_of_horizontal_labels_oai.{u_1, u_2, u_3, u_4, u_5, u_6, u_7, u_8}
