-- Prove2me | solution 1 for OAI.PolycyclicRecognition.main_uniform_bounded_height
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-03T01:04:11.167338+00:00
-- url     : https://prove2.me/submissions/a4ad009a-7f3d-4d59-a414-7b9f947824e9

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_PolycyclicRecognition
import Definitions.Def_OAIQ093D023
import Theorems.Thm_OAI_PolycyclicRecognition_CartanWordModel_exists_uniform_height_intrinsic
import Theorems.Thm_OAI_PolycyclicRecognition_exists_intrinsic_smooth_coordinates
import Theorems.Thm_OAI_PolycyclicRecognition_trace_ad_eq_zero_of_intrinsic_kernel_haar

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_LinearMetricChains
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instNonemptyBases _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_nonempty _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Linear metric chains and coarse Lipschitz bounds

An explicit large-scale geodesic condition allows one to sum local bounds
along a chain. For continuous homomorphisms out of proper metric groups,
the local bound comes from compactness. This is the elementary metric step
in the proper cocompact homomorphism form of the Milnor--Švarc argument.
-/

noncomputable section

namespace PolycyclicRecognition

open Metric Set

variable {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]

variable {G H : Type*} [Group G] [Group H] [MetricSpace G] [MetricSpace H]
  [IsIsometricSMul G G] [IsIsometricSMul H H]

/-- A continuous homomorphism out of a proper metric group has uniformly
bounded image displacement on any bounded source step. -/
theorem continuousHom_bounded_metric_steps [ProperSpace G]
    (f : G →* H) (hf : Continuous f) (R : ℝ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ x y, dist x y ≤ R → dist (f x) (f y) ≤ D := by
  obtain ⟨D, hD⟩ := (isCompact_closedBall (1 : G) R).bddAbove_image
    (continuous_const.dist hf).continuousOn
  refine ⟨max D 0, le_max_right _ _, fun x y hxy => ?_⟩
  have hmem : x⁻¹ * y ∈ closedBall (1 : G) R := by
    simpa only [mem_closedBall, dist_comm (x⁻¹ * y), dist_one_groupDifference] using hxy
  have hb : dist (1 : H) (f (x⁻¹ * y)) ≤ D := hD (mem_image_of_mem _ hmem)
  rw [map_mul, map_inv, dist_one_groupDifference] at hb
  exact hb.trans (le_max_left _ _)

/-- The homomorphism's affine bound requires only compactness and the
explicit linear chains; no global differentiability estimate is needed. -/
theorem continuousHom_coarseLipschitz [ProperSpace G] (C : LinearMetricChains G)
    (f : G →* H) (hf : Continuous f) :
    ∃ K B : ℝ, 0 ≤ K ∧ 0 ≤ B ∧
      ∀ x y, dist (f x) (f y) ≤ K * dist x y + B := by
  obtain ⟨D, hD, hstep⟩ := continuousHom_bounded_metric_steps f hf C.step
  exact ⟨D * C.slope, D * C.error,
    mul_nonneg hD C.slope_nonneg, mul_nonneg hD C.error_nonneg,
    C.coarseLipschitz f hD hstep⟩

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
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_MinimizingLieMetric
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The published minimizing metric on the connected Lie model

The sole input is the connected Lie-group specialization of J. M. Lee,
*Introduction to Riemannian Manifolds*, second edition, GTM 176 (2018):
Lemma 3.10(b), p. 68 constructs a left-invariant Riemannian metric;
Problem 6-12(c), p. 188 gives completeness of homogeneous metrics;
Corollary 6.21, p. 170 gives minimizing segments; Problem 6-14(a), p. 188
(or the compact exponential-ball argument in Lemma 6.18) gives properness.
Only the resulting metric and normalized minimizing paths are retained.
The large-scale chain property is proved here rather than included in the
published hypothesis.
-/

noncomputable section
namespace PolycyclicRecognition

open Set

namespace ProperMinimizingMetric

variable {G : Type*} [Group G] [TopologicalSpace G] (d : ProperMinimizingMetric G)

theorem minimizing_compatibleMetric :
    letI := d.toProperChainMetric.compatibleMetric
    ∀ g : G, ∃ γ : ℝ → G, γ 0 = 1 ∧ γ 1 = g ∧
      ∀ t ∈ Icc (0 : ℝ) 1, ∀ u ∈ Icc (0 : ℝ) 1,
        dist (γ t) (γ u) ≤ dist 1 g * |t - u| := by
  rw [d.toProperChainMetric.compatibleMetric_eq]
  exact d.minimizing

end ProperMinimizingMetric
end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CanonicalHeight
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The linear canonical height quotient

The height space is the quotient by the common kernel of the diagonal adjoint
characters. The induced characters on this quotient separate points.
-/

namespace PolycyclicRecognition

open scoped BigOperators

section Linear

variable {L I : Type*} [AddCommGroup L] [Module ℝ L]

/-- The common kernel has been removed: all induced character values vanish
only at the zero height. -/
theorem heightCharacters_separate (χ : I → L →ₗ[ℝ] ℝ) (w : HeightSpace χ)
    (hw : ∀ i, heightCharacter χ i w = 0) : w = 0 := by
  obtain ⟨x, rfl⟩ := heightProjection_surjective χ w
  apply (Submodule.Quotient.mk_eq_zero (heightKernel χ)).mpr
  exact (mem_heightKernel χ x).mpr hw

end Linear

end PolycyclicRecognition

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_ExponentialHeightKernel
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The group height kernel from exponential coordinates

A representation strictly upper triangular on the canonical Lie kernel is
unipotent on the group height kernel. Thus the already proved chain-packing
theorem applies without a separate group-kernel hypothesis.
-/

noncomputable section

namespace PolycyclicRecognition

open PositiveTriangular
open scoped Matrix.Norms.Operator

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L]
  {a : ℕ} (T : TriangularAdjoint L a)
  {G W : Type*} [Group G] [NormedAddCommGroup W] [NormedSpace ℝ W]
  (q : HeightSpace T.character ≃ₗ[ℝ] W)
  (Exp : L → G) (π : G →* Multiplicative W)
  (hπExp : ∀ x, (π (Exp x)).toAdd = q (heightProjection T.character x))

include T q Exp hπExp

theorem integrated_height_surjective : Function.Surjective π := by
  intro w
  obtain ⟨x, hx⟩ := heightProjection_surjective T.character (q.symm w.toAdd)
  refine ⟨Exp x, ?_⟩
  apply Multiplicative.ext
  rw [hπExp, hx, q.apply_symm_apply]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_RiemannianChartLength
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Chart displacement controlled by the length of a path -/

noncomputable section
namespace PolycyclicRecognition

open Set MeasureTheory Manifold
open scoped Manifold ContDiff ENNReal NNReal Bundle

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) 1 M]
  [Bundle.RiemannianBundle (TangentSpace (𝓘(ℝ, E)) : M → Type _)]

attribute [local instance] OAI.PolycyclicRecognition.tangentModelOperatorENorm
theorem chart_edist_le_pathELength (x : M) (γ : ℝ → M)
    (hγ : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓘(ℝ, E)) 1 γ (Icc 0 1))
    (hsource : ∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ (chartAt E x).source)
    (C : ℝ≥0) (hC : ∀ t ∈ Icc (0 : ℝ) 1,
      ‖mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) (extChartAt (𝓘(ℝ, E)) x) (γ t)‖ₑ ≤ C) :
    edist (extChartAt (𝓘(ℝ, E)) x (γ 0)) (extChartAt (𝓘(ℝ, E)) x (γ 1)) ≤
      C * pathELength (𝓘(ℝ, E)) γ 0 1 := by
  let η := extChartAt (𝓘(ℝ, E)) x ∘ γ
  have hη : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓘(ℝ, E)) 1 η (Icc 0 1) :=
    contMDiffOn_extChartAt.comp hγ hsource
  calc
    _ = ‖η 1 - η 0‖ₑ := by rw [edist_comm, edist_eq_enorm_sub]; rfl
    _ ≤ ∫⁻ t in Icc 0 1, ‖derivWithin η (Icc 0 1) t‖ₑ :=
      enorm_sub_le_lintegral_derivWithin_Icc_of_contDiffOn_Icc hη.contDiffOn zero_le_one
    _ = ∫⁻ t in Icc 0 1, ‖mfderivWithin (𝓘(ℝ, ℝ)) (𝓘(ℝ, E)) η (Icc 0 1) t 1‖ₑ := by
      simp_rw [← fderivWithin_derivWithin, mfderivWithin_eq_fderivWithin]
      rfl
    _ ≤ ∫⁻ t in Icc 0 1, C * ‖mfderivWithin (𝓘(ℝ, ℝ)) (𝓘(ℝ, E)) γ (Icc 0 1) t 1‖ₑ := by
      apply setLIntegral_mono' measurableSet_Icc
      intro t ht
      have hd : mfderivWithin (𝓘(ℝ, ℝ)) (𝓘(ℝ, E)) η (Icc 0 1) t =
          (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) (extChartAt (𝓘(ℝ, E)) x) (γ t)).comp
            (mfderivWithin (𝓘(ℝ, ℝ)) (𝓘(ℝ, E)) γ (Icc 0 1) t) := by
        apply mfderiv_comp_mfderivWithin
        · exact mdifferentiableAt_extChartAt (hsource t ht)
        · exact (hγ.mdifferentiableOn one_ne_zero) t ht
        · rw [uniqueMDiffWithinAt_iff_uniqueDiffWithinAt]
          exact uniqueDiffOn_Icc zero_lt_one t ht
      have hv := congrArg (fun D => D (1 : TangentSpace (𝓘(ℝ, ℝ)) t)) hd
      rw [hv]
      change ‖mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) (extChartAt (𝓘(ℝ, E)) x) (γ t)
        (mfderivWithin (𝓘(ℝ, ℝ)) (𝓘(ℝ, E)) γ (Icc 0 1) t 1)‖ₑ ≤ _
      apply (ContinuousLinearMap.le_opENorm _ _).trans
      gcongr
      exact hC t ht
    _ = _ := by
      rw [lintegral_const_mul' _ _ ENNReal.coe_ne_top,
        pathELength_eq_lintegral_mfderivWithin_Icc]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_LocalRiemannianChart
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Local Lipschitz control of a chart by the Riemannian distance -/

noncomputable section
namespace PolycyclicRecognition

open Set Filter Manifold Bundle Metric
open scoped Topology Manifold ContDiff Bundle NNReal

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [TopologicalSpace G] [ChartedSpace E G] [Group G] [LieGroup (𝓘(ℝ, E)) ∞ G]
  [T3Space G] [ConnectedSpace G] (e : E ≃L[ℝ] F)

theorem leftRiemannianChart_lipschitz (x : G) :
    letI := leftRiemannianMetric (G := G) e
    ∃ C : ℝ≥0, ∃ U ∈ 𝓝 x,
      LipschitzOnWith C (extChartAt (𝓘(ℝ, E)) x) U := by
  let metric := leftRiemannianMetric (G := G) e
  let bundle := leftRiemannianBundle (G := G) e
  let continuousBundle : IsContinuousRiemannianBundle E
      (TangentSpace (𝓘(ℝ, E)) : G → Type _) :=
    ⟨⟨(leftInvariantRiemannianMetric (G := G) e).inner,
      (leftInvariantRiemannianMetric (G := G) e).contMDiff.continuous, fun _ _ _ => rfl⟩⟩
  obtain ⟨C, hCpos, hC⟩ := eventually_enorm_mfderiv_extChartAt_lt (𝓘(ℝ, E)) x
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp
    (inter_mem hC (chart_source_mem_nhds E x))
  have hpos : (0 : ℝ) < C := hCpos
  refine ⟨C, ball x (r / 4), ball_mem_nhds x (by positivity),
    LipschitzOnWith.of_dist_le_mul ?_⟩
  intro y hy z hz
  have hxy : dist x y < r / 4 := by simpa only [mem_ball, dist_comm] using hy
  have hxz : dist x z < r / 4 := by simpa only [mem_ball, dist_comm] using hz
  have hyz : dist y z < r / 2 := by
    have := dist_triangle y x z
    rw [dist_comm y x] at this
    linarith
  apply le_of_forall_pos_le_add
  intro ε hε
  let δ := min (ε / (C : ℝ)) (r / 4)
  have hδ : 0 < δ := lt_min (div_pos hε hpos) (by positivity)
  have hδr : δ ≤ r / 4 := min_le_right _ _
  have hδε : (C : ℝ) * δ ≤ ε := by
    have := min_le_left (ε / (C : ℝ)) (r / 4)
    change δ ≤ ε / (C : ℝ) at this
    have h := (le_div_iff₀ hpos).mp this
    simpa only [mul_comm] using h
  have hnear : riemannianEDist (𝓘(ℝ, E)) y z < ENNReal.ofReal (dist y z + δ) := by
    change edist y z < _
    rw [edist_dist, ENNReal.ofReal_lt_ofReal_iff_of_nonneg dist_nonneg]
    linarith
  obtain ⟨γ, h₀, h₁, hγ, hlen⟩ := exists_lt_of_riemannianEDist_lt hnear
  have hfinite : pathELength (𝓘(ℝ, E)) γ 0 1 ≠ ⊤ := ne_top_of_lt hlen
  have hlenreal : (pathELength (𝓘(ℝ, E)) γ 0 1).toReal < dist y z + δ := by
    have h := (ENNReal.toReal_lt_toReal hfinite ENNReal.ofReal_ne_top).mpr hlen
    simpa only [ENNReal.toReal_ofReal (by positivity : 0 ≤ dist y z + δ)] using h
  have hinside (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : γ t ∈ ball x r := by
    have hprefix : edist y (γ t) ≤ pathELength (𝓘(ℝ, E)) γ 0 1 :=
      (riemannianEDist_le_pathELength (hγ.mono (Icc_subset_Icc le_rfl ht.2))
        h₀ rfl ht.1).trans (pathELength_mono le_rfl ht.2)
    have hd := ENNReal.toReal_mono hfinite hprefix
    rw [edist_dist, ENNReal.toReal_ofReal dist_nonneg] at hd
    rw [mem_ball, dist_comm]
    have htri := dist_triangle x y (γ t)
    linarith
  have hchart := chart_edist_le_pathELength x γ hγ
    (fun t ht => (hball (hinside t ht)).2) C
    (fun t ht => (hball (hinside t ht)).1.le)
  rw [h₀, h₁] at hchart
  have hchartreal := ENNReal.toReal_mono (ENNReal.mul_ne_top (by simp) hfinite) hchart
  rw [edist_dist, ENNReal.toReal_ofReal dist_nonneg, ENNReal.toReal_mul,
    ENNReal.coe_toReal] at hchartreal
  nlinarith

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_SmoothFromRiemannian
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Smooth maps from the invariant Riemannian metric are locally Lipschitz -/

noncomputable section
namespace PolycyclicRecognition

open Set Filter Manifold
open scoped Topology Manifold ContDiff

variable {E F V G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [TopologicalSpace G] [ChartedSpace E G] [Group G] [LieGroup (𝓘(ℝ, E)) ∞ G]
  [T3Space G] [ConnectedSpace G] (e : E ≃L[ℝ] F)

theorem smooth_from_leftRiemannian_locallyLipschitz {f : G → V}
    (hf : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, V)) ∞ f) :
    letI := leftRiemannianMetric (G := G) e
    LocallyLipschitz f := by
  let metric := leftRiemannianMetric (G := G) e
  intro x
  obtain ⟨C, U, hU, hχ⟩ := leftRiemannianChart_lipschitz e x
  let χ := extChartAt (𝓘(ℝ, E)) x
  have hs : ContDiffAt ℝ 1 (f ∘ χ.symm) (χ x) := by
    have hm := contMDiffAt_iff_source.mp
      ((hf.contMDiffAt (x := x)).of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top : (1 : ℕ∞ω) ≤ ∞))
    have hm' : ContMDiffAt (𝓘(ℝ, E)) (𝓘(ℝ, V)) 1 (f ∘ χ.symm) (χ x) := by
      have hr : Set.range (𝓘(ℝ, E)) = Set.univ := Set.range_id
      rw [hr, contMDiffWithinAt_univ] at hm
      exact hm
    exact hm'.contDiffAt
  obtain ⟨K, A, hA, hKA⟩ := hs.exists_lipschitzOnWith
  have hpre : χ ⁻¹' A ∈ 𝓝 x := (continuousAt_extChartAt x).preimage_mem_nhds hA
  let W := U ∩ (χ ⁻¹' A ∩ χ.source)
  have hW : W ∈ 𝓝 x := inter_mem hU (inter_mem hpre (extChartAt_source_mem_nhds x))
  refine ⟨K * C, W, hW, LipschitzOnWith.of_dist_le_mul ?_⟩
  intro y hy z hz
  have hb := hKA.dist_le_mul (x := χ y) (y := χ z) hy.2.1 hz.2.1
  have hcy := χ.left_inv hy.2.2
  have hcz := χ.left_inv hz.2.2
  simp only [Function.comp_apply, hcy, hcz] at hb
  calc
    dist (f y) (f z) ≤ K * dist (χ y) (χ z) := hb
    _ ≤ K * ((C : ℝ) * dist y z) :=
      mul_le_mul_of_nonneg_left (hχ.dist_le_mul (x := y) (y := z) hy.1 hz.1) K.coe_nonneg
    _ = ↑(K * C) * dist y z := by simp only [NNReal.coe_mul, mul_assoc]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_GroupIncrementLipschitz
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Local Lipschitz control from coordinates of group increments -/

namespace PolycyclicRecognition

open Set Filter
open scoped Topology NNReal

theorem locallyLipschitz_of_group_increments
    {V W G : Type*} [PseudoMetricSpace V] [PseudoMetricSpace W]
    [Group G] [MetricSpace G] [IsTopologicalGroup G] [IsIsometricSMul G G]
    (f : V → G) (χ : G → W) (hf : Continuous f)
    (C : ℝ≥0) (U : Set G) (hU : U ∈ 𝓝 (1 : G))
    (hχ : ∀ z ∈ U, dist (1 : G) z ≤ C * dist (χ 1) (χ z))
    (hF : ∀ x : V, ∃ K : ℝ≥0, ∃ A ∈ 𝓝 (x, x),
      LipschitzOnWith K (fun p : V × V => χ ((f p.1)⁻¹ * f p.2)) A) :
    LocallyLipschitz f := by
  intro x
  obtain ⟨K, A, hA, hFA⟩ := hF x
  have hinc : Continuous (fun p : V × V => (f p.1)⁻¹ * f p.2) :=
    (hf.comp continuous_fst).inv.mul (hf.comp continuous_snd)
  have hpre : (fun p : V × V => (f p.1)⁻¹ * f p.2) ⁻¹' U ∈ 𝓝 (x, x) :=
    hinc.continuousAt.preimage_mem_nhds (by simpa only [inv_mul_cancel] using hU)
  obtain ⟨A₁, hA₁, A₂, hA₂, hprod⟩ := mem_nhds_prod_iff.mp (inter_mem hA hpre)
  refine ⟨C * K, A₁ ∩ A₂, inter_mem hA₁ hA₂, LipschitzOnWith.of_dist_le_mul ?_⟩
  intro a ha b hb
  have hab := hprod (show (a, b) ∈ A₁ ×ˢ A₂ from ⟨ha.1, hb.2⟩)
  have haa := hprod (show (a, a) ∈ A₁ ×ˢ A₂ from ⟨ha.1, ha.2⟩)
  have hcoord := hFA.dist_le_mul (x := (a, a)) (y := (a, b)) haa.1 hab.1
  simp only [inv_mul_cancel, Prod.dist_eq, dist_self, max_eq_right dist_nonneg] at hcoord
  calc
    dist (f a) (f b) = dist (1 : G) ((f a)⁻¹ * f b) := by
      simpa only [mul_one, mul_inv_cancel_left] using
        dist_mul_left (f a) 1 ((f a)⁻¹ * f b)
    _ ≤ C * dist (χ 1) (χ ((f a)⁻¹ * f b)) := hχ _ hab.2
    _ ≤ C * ((K : ℝ) * dist a b) := mul_le_mul_of_nonneg_left hcoord C.coe_nonneg
    _ = ↑(C * K) * dist a b := by simp only [NNReal.coe_mul, mul_assoc]

end PolycyclicRecognition

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_SmoothIntoRiemannian
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Smooth maps into the invariant Riemannian metric are locally Lipschitz -/

noncomputable section
namespace PolycyclicRecognition

open Set Filter Manifold Bundle
open scoped Topology Manifold ContDiff Bundle

variable {E F V G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [TopologicalSpace G] [ChartedSpace E G] [Group G] [LieGroup (𝓘(ℝ, E)) ∞ G]
  [T3Space G] [ConnectedSpace G] (e : E ≃L[ℝ] F)

theorem smooth_into_leftRiemannian_locallyLipschitz {f : V → G}
    (hf : ContMDiff (𝓘(ℝ, V)) (𝓘(ℝ, E)) ∞ f) :
    letI := leftRiemannianMetric (G := G) e
    LocallyLipschitz f := by
  let metric := leftRiemannianMetric (G := G) e
  let bundle := leftRiemannianBundle (G := G) e
  let continuousBundle : IsContinuousRiemannianBundle E
      (TangentSpace (𝓘(ℝ, E)) : G → Type _) :=
    ⟨⟨(leftInvariantRiemannianMetric (G := G) e).inner,
      (leftInvariantRiemannianMetric (G := G) e).contMDiff.continuous, fun _ _ _ => rfl⟩⟩
  let groupTopology : IsTopologicalGroup G := topologicalGroup_of_lieGroup (𝓘(ℝ, E)) ∞
  let isometric := leftRiemannianMetric_isometric (G := G) e
  obtain ⟨C, _, hC⟩ := eventually_riemannianEDist_le_edist_extChartAt (𝓘(ℝ, E)) (1 : G)
  let χ : G → E := extChartAt (𝓘(ℝ, E)) (1 : G)
  let U := {z : G | riemannianEDist (𝓘(ℝ, E)) 1 z ≤ C * edist (χ 1) (χ z)}
  apply locallyLipschitz_of_group_increments f χ hf.continuous C U hC
  · intro z hz
    have hb := ENNReal.toReal_mono
      (ENNReal.mul_ne_top ENNReal.coe_ne_top (edist_ne_top (χ 1) (χ z))) hz
    change (edist (1 : G) z).toReal ≤ _ at hb
    simpa only [ENNReal.toReal_mul, ENNReal.coe_toReal, edist_dist,
      ENNReal.toReal_ofReal dist_nonneg] using hb
  · intro x
    have hincr : ContMDiff ((𝓘(ℝ, V)).prod (𝓘(ℝ, V))) (𝓘(ℝ, E)) ∞
        (fun p : V × V => (f p.1)⁻¹ * f p.2) :=
      (hf.comp contMDiff_fst).inv.mul (hf.comp contMDiff_snd)
    have hchart : ContMDiffAt (𝓘(ℝ, E)) (𝓘(ℝ, E)) ∞ χ ((f x)⁻¹ * f x) := by
      simpa only [inv_mul_cancel] using (contMDiffAt_extChartAt (I := 𝓘(ℝ, E)) (x := (1 : G)))
    have hc := hchart.comp (x, x) hincr.contMDiffAt
    rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod] at hc
    exact (hc.contDiffAt.of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top : (1 : ℕ∞ω) ≤ ∞)).exists_lipschitzOnWith

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_ConstructRiemannianInput
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Discharging the Riemannian metric and coordinate-regularity input -/

noncomputable section
namespace PolycyclicRecognition

open scoped Manifold ContDiff

theorem lieRiemannianMetricInput : LieRiemannianMetricInput := by
  intro S
  let groupTopology : IsTopologicalGroup S.carrier :=
    topologicalGroup_of_lieGroup (𝓘(ℝ, S.modelSpace)) ∞
  let localCompact : LocallyCompactSpace S.carrier :=
    Manifold.locallyCompact_of_finiteDimensional (𝓘(ℝ, S.modelSpace))
  let e : S.modelSpace ≃L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ S.modelSpace)) :=
    (Module.finBasis ℝ S.modelSpace).equivFun.toContinuousLinearEquiv.trans
      (EuclideanSpace.equiv (Fin (Module.finrank ℝ S.modelSpace)) ℝ).symm
  refine ⟨leftRiemannianMinimizingMetric e, ?_⟩
  rw [ProperChainMetric.compatibleMetric_eq]
  change letI := leftRiemannianMetric (G := S.carrier) e
    ∀ (n : ℕ) (φ : (Fin n → ℝ) ≃ₜ S.carrier),
      ContMDiff (𝓘(ℝ, Fin n → ℝ)) (𝓘(ℝ, S.modelSpace)) ∞ φ →
      ContMDiff (𝓘(ℝ, S.modelSpace)) (𝓘(ℝ, Fin n → ℝ)) ∞ φ.symm →
      LocallyLipschitz φ ∧ LocallyLipschitz φ.symm
  let metric := leftRiemannianMetric (G := S.carrier) e
  intro n φ hφ hφinv
  exact ⟨smooth_into_leftRiemannian_locallyLipschitz e hφ,
    smooth_from_leftRiemannian_locallyLipschitz e hφinv⟩

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_CoordinatePolynomial
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial restrictions to coordinate lines -/

noncomputable section
namespace PolycyclicRecognition

open Polynomial

theorem CoordinatePolynomial.head {n D : ℕ} {f : (Fin (n + 1) → ℝ) → ℝ}
    (hf : CoordinatePolynomial (n + 1) D f) (x : Fin n → ℝ) :
    ∃ p : ℝ[X], p.natDegree ≤ D ∧ ∀ t, p.eval t = f (Fin.cons t x) := by
  obtain ⟨p, hp, he⟩ := hf 0 (Fin.cons 0 x)
  exact ⟨p, hp, fun t => by simpa only [Fin.update_cons_zero] using he t⟩

theorem CoordinatePolynomial.tail {n D : ℕ} {f : (Fin (n + 1) → ℝ) → ℝ}
    (hf : CoordinatePolynomial (n + 1) D f) (t : ℝ) :
    CoordinatePolynomial n D (fun x => f (Fin.cons t x)) := by
  intro i x
  obtain ⟨p, hp, he⟩ := hf i.succ (Fin.cons t x)
  exact ⟨p, hp, fun u => by simpa only [← Fin.cons_update] using he u⟩

theorem coordinatePolynomial_eval {n D : ℕ} (p : MvPolynomial (Fin n) ℝ)
    (hp : p.totalDegree ≤ D) :
    CoordinatePolynomial n D (fun x => MvPolynomial.eval x p) := by
  classical
  intro i x
  let e := Equiv.optionSubtypeNe i
  let q := MvPolynomial.rename e.symm p
  let P := MvPolynomial.optionEquivLeft ℝ {j : Fin n // j ≠ i} q
  let r := Polynomial.map (MvPolynomial.eval (fun j : {j : Fin n // j ≠ i} => x j)) P
  refine ⟨r, ?_, ?_⟩
  · calc
      r.natDegree ≤ P.natDegree := Polynomial.natDegree_map_le
      _ = p.degreeOf i := (MvPolynomial.degreeOf_eq_natDegree i p).symm
      _ ≤ p.totalDegree := MvPolynomial.degreeOf_le_totalDegree p i
      _ ≤ D := hp
  · intro t
    change Polynomial.eval t (Polynomial.map (MvPolynomial.eval
      (fun j : {j : Fin n // j ≠ i} => x j)) (MvPolynomial.optionEquivLeft ℝ _ q)) = _
    rw [← MvPolynomial.optionEquivLeft_elim_eval, MvPolynomial.eval_rename]
    apply congrArg (fun v : Fin n → ℝ => MvPolynomial.eval v p)
    funext j
    by_cases hj : j = i
    · subst j
      simp [e]
    · simp [e, Equiv.optionSubtypeNe_symm_apply, hj]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_NormalizePositiveMass
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Normalizing a positive partition mass bounded below by one -/

namespace PolycyclicRecognition

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The cutoff partition has mass at least one. Normalizing such vectors
costs at most a factor two in their normed distance. -/
theorem norm_normalized_sub_le_two (x y : E) (hx : 1 ≤ ‖x‖) (hy : 1 ≤ ‖y‖) :
    ‖‖x‖⁻¹ • x - ‖y‖⁻¹ • y‖ ≤ 2 * ‖x - y‖ := by
  have hx0 : 0 < ‖x‖ := lt_of_lt_of_le zero_lt_one hx
  have hy0 : 0 < ‖y‖ := lt_of_lt_of_le zero_lt_one hy
  have hcoef : (‖x‖⁻¹ - ‖y‖⁻¹) * ‖y‖ = (‖y‖ - ‖x‖) / ‖x‖ := by
    field_simp
  have he : ‖(‖x‖⁻¹ - ‖y‖⁻¹) • y‖ = |‖y‖ - ‖x‖| / ‖x‖ := by
    rw [norm_smul, Real.norm_eq_abs]
    calc
      |‖x‖⁻¹ - ‖y‖⁻¹| * ‖y‖ = |(‖x‖⁻¹ - ‖y‖⁻¹) * ‖y‖| := by
        rw [abs_mul, abs_of_nonneg (norm_nonneg y)]
      _ = |‖y‖ - ‖x‖| / ‖x‖ := by rw [hcoef, abs_div, abs_of_pos hx0]
  have hnorm : |‖y‖ - ‖x‖| ≤ ‖x - y‖ := by
    simpa only [dist_zero_right, dist_eq_norm, sub_zero, norm_sub_rev] using abs_dist_sub_le y x (0 : E)
  calc
    _ = ‖‖x‖⁻¹ • (x - y) + (‖x‖⁻¹ - ‖y‖⁻¹) • y‖ := by
      congr 1
      rw [smul_sub, sub_smul]
      abel
    _ ≤ ‖‖x‖⁻¹ • (x - y)‖ + ‖(‖x‖⁻¹ - ‖y‖⁻¹) • y‖ := norm_add_le _ _
    _ = ‖x - y‖ / ‖x‖ + |‖y‖ - ‖x‖| / ‖x‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hx0), he]
      simp only [div_eq_inv_mul]
    _ ≤ ‖x - y‖ / ‖x‖ + ‖x - y‖ / ‖x‖ :=
      add_le_add le_rfl (div_le_div_of_nonneg_right hnorm hx0.le)
    _ ≤ 2 * ‖x - y‖ := by
      have hdiv : ‖x - y‖ / ‖x‖ ≤ ‖x - y‖ :=
        (div_le_iff₀ hx0).mpr (by nlinarith only [hx, norm_nonneg (x - y)])
      linarith only [hdiv]

end PolycyclicRecognition

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_FiniteCutoffPartition
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The quantitative cutoff partition used by Lipschitz replacement -/

noncomputable section
namespace PolycyclicRecognition

open scoped BigOperators

variable {X I : Type*} [MetricSpace X] [Fintype I]

private theorem cutoff_difference_le (v x y : X) :
    |max 0 (2 - dist x v) - max 0 (2 - dist y v)| ≤ dist x y := by
  have hd := abs_le.mp (abs_dist_sub_le x y v)
  simp only [max_def]
  split_ifs <;> apply abs_le.mpr <;> constructor <;> linarith [dist_nonneg (x := x) (y := y)]

/-- Before normalization, at most one distance error is charged per
participating center. The application restricts to the finite local support. -/
theorem norm_cutoffMass_sub_le (v : I → X) (x y : X) :
    ‖cutoffMass v x - cutoffMass v y‖ ≤ (Fintype.card I : ℝ) * dist x y := by
  rw [PiLp.norm_eq_of_L1]
  change (∑ i, |max 0 (2 - dist x (v i)) - max 0 (2 - dist y (v i))|) ≤ _
  calc
    _ ≤ ∑ _i : I, dist x y := Finset.sum_le_sum (fun i _ => cutoff_difference_le (v i) x y)
    _ = _ := by simp

/-- The unit-ball cover gives the uniform lower bound on the denominator. -/
theorem one_le_norm_cutoffMass (v : I → X) (x : X)
    (hcover : ∃ i, dist x (v i) ≤ 1) : 1 ≤ ‖cutoffMass v x‖ := by
  obtain ⟨i, hi⟩ := hcover
  rw [PiLp.norm_eq_of_L1]
  change 1 ≤ ∑ j, ‖max 0 (2 - dist x (v j))‖
  calc
    1 ≤ max 0 (2 - dist x (v i)) := (by linarith : 1 ≤ 2 - dist x (v i)).trans (le_max_right _ _)
    _ = ‖max 0 (2 - dist x (v i))‖ := (Real.norm_of_nonneg (le_max_left _ _)).symm
    _ ≤ _ := Finset.single_le_sum (fun j _ => norm_nonneg (max 0 (2 - dist x (v j)))) (Finset.mem_univ i)

/-- Normalization costs a factor two, uniformly over points whose unit
balls contain one of the participating centers. -/
theorem norm_cutoffPartition_sub_le (v : I → X) (x y : X)
    (hx : ∃ i, dist x (v i) ≤ 1) (hy : ∃ i, dist y (v i) ≤ 1) :
    ‖cutoffPartition v x - cutoffPartition v y‖ ≤
      2 * (Fintype.card I : ℝ) * dist x y := by
  exact (norm_normalized_sub_le_two (cutoffMass v x) (cutoffMass v y)
    (one_le_norm_cutoffMass v x hx) (one_le_norm_cutoffMass v y hy)).trans
    (by nlinarith only [norm_cutoffMass_sub_le v x y])

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_FiniteFiberMass
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Positive mass on quantitatively large sections

This is the finite-measure Fubini estimate used to iterate one-dimensional
polynomial bounds. It concerns an arbitrary measurable set in a product.
-/

noncomputable section
namespace PolycyclicRecognition

open MeasureTheory Set
open scoped ENNReal

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

theorem exists_large_sections (μ : Measure X) (ν : Measure Y)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (ha : 0 < (μ univ).toReal) (hb : 0 < (ν univ).toReal)
    (S : Set (X × Y)) (hS : MeasurableSet S)
    (hm : 0 < (μ.prod ν S).toReal) :
    ∃ A : Set X, MeasurableSet A ∧
      (μ.prod ν S).toReal / (2 * (ν univ).toReal) ≤ (μ A).toReal ∧
      ∀ x ∈ A,
        (μ.prod ν S).toReal / (2 * (μ univ).toReal) ≤
          (ν (Prod.mk x ⁻¹' S)).toReal := by
  let m := (μ.prod ν S).toReal
  let a := (μ univ).toReal
  let b := (ν univ).toReal
  let c := m / (2 * a)
  let f : X → ℝ := fun x => (ν (Prod.mk x ⁻¹' S)).toReal
  have hc : 0 < c := div_pos hm (mul_pos (by norm_num) ha)
  have hfm : Measurable f := (measurable_measure_prodMk_left hS).ennreal_toReal
  have hf0 (x : X) : 0 ≤ f x := ENNReal.toReal_nonneg
  have hfb (x : X) : f x ≤ b :=
    ENNReal.toReal_mono (measure_ne_top ν univ) (measure_mono (subset_univ _))
  have hfi : Integrable f μ := (integrable_const b).mono' hfm.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun x => by simpa only [Real.norm_eq_abs, abs_of_nonneg (hf0 x)] using hfb x))
  have hint : ∫ x, f x ∂μ = m := by
    change (∫ x, (ν (Prod.mk x ⁻¹' S)).toReal ∂μ) = (μ.prod ν S).toReal
    rw [Measure.prod_apply hS]
    exact integral_toReal (measurable_measure_prodMk_left hS).aemeasurable
      (Filter.Eventually.of_forall (fun x => measure_lt_top ν _))
  let A := {x | c ≤ f x}
  have hA : MeasurableSet A := measurableSet_le measurable_const hfm
  have hgi : Integrable (fun x => c + A.indicator (fun _ => b) x) μ :=
    (integrable_const c).add ((integrable_const b).indicator hA)
  have hbound (x : X) : f x ≤ c + A.indicator (fun _ => b) x := by
    by_cases hx : x ∈ A
    · rw [indicator_of_mem hx]
      linarith [hfb x]
    · rw [indicator_of_notMem hx, add_zero]
      exact (lt_of_not_ge hx).le
  have hi := integral_mono hfi hgi hbound
  rw [hint, integral_add (integrable_const c) ((integrable_const b).indicator hA),
    integral_const, integral_indicator hA, setIntegral_const] at hi
  simp only [smul_eq_mul, measureReal_def] at hi
  have hca : c * a = m / 2 := by
    dsimp [c]
    field_simp [show a ≠ 0 from ne_of_gt ha]
  change m ≤ a * c + (μ A).toReal * b at hi
  rw [mul_comm a c, hca] at hi
  refine ⟨A, hA, ?_, fun x hx => hx⟩
  apply (div_le_iff₀ (mul_pos (by norm_num) hb)).2
  nlinarith

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_NilpotentGenerators
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Lifting generators from the nilpotent abelianization

For the Cartan model, homogeneous lifts of a basis modulo the derived algebra
generate the whole nilpotent ideal. The proof pushes the error down its actual
lower central series; no generation hypothesis is substituted for this step.
-/

namespace PolycyclicRecognition

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L]

/-- Lie generation implies linear spanning modulo brackets. -/
theorem span_sup_lowerCentralSeries_one_of_lieSpan
    (S : Set L) (hS : LieSubalgebra.lieSpan ℝ L S = ⊤) :
    Submodule.span ℝ S ⊔ (LieModule.lowerCentralSeries ℝ L L 1).toSubmodule = ⊤ := by
  let V := Submodule.span ℝ S ⊔ (LieModule.lowerCentralSeries ℝ L L 1).toSubmodule
  have hmem : ∀ x ∈ LieSubalgebra.lieSpan ℝ L S, x ∈ V := by
    intro x hx
    induction hx using LieSubalgebra.lieSpan_induction with
    | mem x hx => exact Submodule.mem_sup_left (Submodule.subset_span hx)
    | zero => exact V.zero_mem
    | add x y _ _ hx hy => exact V.add_mem hx hy
    | smul r x _ hx => exact V.smul_mem r hx
    | lie x y _ _ _ _ =>
      apply Submodule.mem_sup_right
      change ⁅x, y⁆ ∈ LieModule.lowerCentralSeries ℝ L L (0 + 1)
      rw [LieModule.lowerCentralSeries_succ, LieModule.lowerCentralSeries_zero]
      exact LieSubmodule.lie_mem_lie (LieSubmodule.mem_top x) (LieSubmodule.mem_top y)
  apply top_unique
  intro x _
  exact hmem x (hS ▸ LieSubalgebra.mem_top x)

theorem lieSubalgebra_sup_lowerCentralSeries
    (U : LieSubalgebra ℝ L)
    (hU : U.toSubmodule ⊔ (LieModule.lowerCentralSeries ℝ L L 1).toSubmodule = ⊤) :
    ∀ k, U.toSubmodule ⊔ (LieModule.lowerCentralSeries ℝ L L k).toSubmodule = ⊤ := by
  intro k
  induction k with
  | zero => simp
  | succ k hk =>
    let C := LieModule.lowerCentralSeries ℝ L L k
    let C' := LieModule.lowerCentralSeries ℝ L L (k + 1)
    let S := U.toSubmodule ⊔ C'.toSubmodule
    have hright (x y : L) (hy : y ∈ C) : ⁅x, y⁆ ∈ C' := by
      change ⁅x, y⁆ ∈ LieModule.lowerCentralSeries ℝ L L (k + 1)
      rw [LieModule.lowerCentralSeries_succ]
      exact LieSubmodule.lie_mem_lie (LieSubmodule.mem_top x) hy
    have hbracket (x y : L) : ⁅x, y⁆ ∈ S := by
      have hx : x ∈ U.toSubmodule ⊔ C.toSubmodule := by rw [hk]; trivial
      have hy : y ∈ U.toSubmodule ⊔ C.toSubmodule := by rw [hk]; trivial
      obtain ⟨u, hu, a, ha, rfl⟩ := Submodule.mem_sup.mp hx
      obtain ⟨v, hv, b, hb, rfl⟩ := Submodule.mem_sup.mp hy
      rw [add_lie, lie_add, lie_add]
      apply S.add_mem
      · exact S.add_mem (Submodule.mem_sup_left (U.lie_mem hu hv))
          (Submodule.mem_sup_right (hright u b hb))
      · apply S.add_mem
        · rw [← lie_skew]
          exact Submodule.mem_sup_right (C'.neg_mem (hright v a ha))
        · exact Submodule.mem_sup_right (hright a b hb)
    have hC : (LieModule.lowerCentralSeries ℝ L L 1).toSubmodule ≤ S := by
      rw [LieModule.lowerCentralSeries_succ, LieModule.lowerCentralSeries_zero,
        LieSubmodule.lieIdeal_oper_eq_linear_span']
      apply Submodule.span_le.mpr
      rintro _ ⟨x, _, y, _, rfl⟩
      exact hbracket x y
    apply top_unique
    rw [← hU]
    exact sup_le le_sup_left hC

/-- Lifts spanning the abelianization generate a nilpotent Lie algebra. -/
theorem lieSubalgebra_eq_top_of_sup_lowerCentralSeries_one
    [LieRing.IsNilpotent L] (U : LieSubalgebra ℝ L)
    (hU : U.toSubmodule ⊔ (LieModule.lowerCentralSeries ℝ L L 1).toSubmodule = ⊤) :
    U = ⊤ := by
  obtain ⟨k, hk⟩ := LieModule.IsNilpotent.nilpotent ℝ L L
  have h := lieSubalgebra_sup_lowerCentralSeries U hU k
  rw [hk, LieSubmodule.bot_toSubmodule, sup_bot_eq] at h
  exact SetLike.coe_injective (congrArg (fun V : Submodule ℝ L => (V : Set L)) h)

end PolycyclicRecognition

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_HomogeneousGenerators
attribute [-instance] _root_.GeneratesNS.fintype_closedBall _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Choosing generators and their positive word multiplicities

A basis of the abelianization can be selected from any homogeneous spanning
pool. Its lifts generate the nilpotent algebra. Every bracket-word basis
then uses every selected generator, which is the positivity needed in the
support-volume formula.
-/

noncomputable section

namespace PolycyclicRecognition

open Module
open scoped BigOperators

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L]

theorem exists_quotient_basis_lifts [FiniteDimensional ℝ L]
    (N : Submodule ℝ L) (S : Set L) (hS : Submodule.span ℝ S ⊔ N = ⊤) :
    ∃ (b : Basis (Fin (Module.finrank ℝ (L ⧸ N))) ℝ (L ⧸ N))
      (X : Fin (Module.finrank ℝ (L ⧸ N)) → L),
      (∀ i, X i ∈ S) ∧ (∀ i, N.mkQ (X i) = b i) ∧
      Submodule.span ℝ (Set.range X) ⊔ N = ⊤ := by
  have himage : Submodule.span ℝ (N.mkQ '' S) = ⊤ := by
    rw [← Submodule.map_span, N.map_mkQ_eq_top]
    simpa only [sup_comm] using hS
  let J := (linearIndepOn_empty ℝ (id : (L ⧸ N) → (L ⧸ N))).extend
    (Set.empty_subset (N.mkQ '' S))
  let b₀ : Basis J ℝ (L ⧸ N) := Basis.ofSpan himage.ge
  let : Fintype J := Fintype.ofFinite _
  let e : J ≃ Fin (Module.finrank ℝ (L ⧸ N)) :=
    Fintype.equivFinOfCardEq (Module.finrank_eq_card_basis b₀).symm
  let b := b₀.reindex e
  have hlift : ∀ i, ∃ x ∈ S, N.mkQ x = b i := by
    intro i
    simpa only [b, Basis.coe_reindex, Function.comp_apply, Set.mem_image] using
      (Basis.ofSpan_subset himage.ge
        (show b₀ (e.symm i) ∈ Set.range b₀ from ⟨_, rfl⟩))
  choose X hXS hX using hlift
  refine ⟨b, X, hXS, hX, ?_⟩
  rw [sup_comm, ← N.map_mkQ_eq_top, Submodule.map_span, ← Set.range_comp]
  have heq : N.mkQ ∘ X = b := funext hX
  rw [heq]
  exact b.span_eq

end PolycyclicRecognition

end

end OAI
end

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
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_MassFractionBounds
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Scalar normalization estimates for recursive interpolation -/

namespace PolycyclicRecognition

private theorem mass_fraction_left_le {A B u v : ℝ}
    (hA : 0 < A) (hB : 0 < B) (hAB : A ≤ B)
    (hv : 0 ≤ v) (hvB : v ≤ B) :
    A * |u / A - v / B| ≤ |u - v| + |A - B| := by
  have hid : A * |u / A - v / B| = |(u * B - A * v) / B| := by
    calc
      _ = |A * (u / A - v / B)| := by rw [abs_mul, abs_of_pos hA]
      _ = _ := by congr 1; field_simp
  rw [hid, abs_of_nonpos (sub_nonpos.mpr hAB)]
  apply abs_le.mpr
  constructor
  · apply (le_div_iff₀ hB).mpr
    have ha := neg_abs_le (u - v)
    nlinarith [mul_nonneg (sub_nonneg.mpr hAB) (sub_nonneg.mpr hvB),
      mul_le_mul_of_nonneg_right ha hB.le]
  · apply (div_le_iff₀ hB).mpr
    have ha := le_abs_self (u - v)
    nlinarith [mul_nonneg (sub_nonneg.mpr hAB) hv,
      mul_le_mul_of_nonneg_right ha hB.le]

/-- Normalization of a partial mass costs at most its own change plus
the change of the total mass, after multiplication by the smaller total. -/
theorem min_mass_mul_abs_fraction_sub_le {A B u v : ℝ}
    (hA : 0 < A) (hB : 0 < B) (hu : 0 ≤ u) (huA : u ≤ A)
    (hv : 0 ≤ v) (hvB : v ≤ B) :
    min A B * |u / A - v / B| ≤ |u - v| + |A - B| := by
  rcases le_total A B with h | h
  · rw [min_eq_left h]
    exact mass_fraction_left_le hA hB h hv hvB
  · rw [min_eq_right h]
    simpa only [abs_sub_comm] using mass_fraction_left_le hB hA h hu huA

/-- The smaller normalized partial mass, rescaled by the smaller total,
never exceeds either original partial mass. -/
theorem min_mass_mul_min_fraction_le {A B u v : ℝ}
    (hA : 0 < A) (hB : 0 < B) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    min A B * min (u / A) (v / B) ≤ min u v := by
  have hm : 0 ≤ min A B := le_min hA.le hB.le
  apply le_min
  · calc
      _ ≤ min A B * (u / A) := mul_le_mul_of_nonneg_left (min_le_left _ _) hm
      _ ≤ A * (u / A) := mul_le_mul_of_nonneg_right (min_le_left _ _) (div_nonneg hu hA.le)
      _ = u := by field_simp
  · calc
      _ ≤ min A B * (v / B) := mul_le_mul_of_nonneg_left (min_le_right _ _) hm
      _ ≤ B * (v / B) := mul_le_mul_of_nonneg_right (min_le_right _ _) (div_nonneg hv hB.le)
      _ = v := by field_simp

end PolycyclicRecognition

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_ControlledContraction
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform contractions about arbitrary centers -/

noncomputable section
namespace PolycyclicRecognition

open Set Metric

variable (G : Type*) [MetricSpace G]

namespace ControlledContraction

variable {G}

theorem dist_center_le (c : ControlledContraction G) {R C : ℝ}
    (hC : ∀ p z w : G, dist z p ≤ R → dist w p ≤ R →
      ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      dist (c.contract p s z) (c.contract p t w) ≤
        C * (|s - t| + min s t * dist z w))
    {p z : G} (hz : dist z p ≤ R) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    dist (c.contract p s z) p ≤ C * s := by
  have h := hC p z z hz hz s hs 0 ⟨le_rfl, zero_le_one⟩
  simpa only [c.zero, sub_zero, abs_of_nonneg hs.1, min_eq_right hs.1,
    dist_self, mul_zero, add_zero] using h

end ControlledContraction
end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_OrderedInterpolation
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Ordered interpolation of finitely many nonnegative masses

Zero masses can be omitted. Thus one fixed order on the net gives compatible
interpolations on different finite supports without a simplicial-complex API.
-/

noncomputable section
namespace PolycyclicRecognition

variable {I G : Type*} [MetricSpace G]

theorem listMass_nonneg (a : I → ℝ) (l : List I) (ha : ∀ i ∈ l, 0 ≤ a i) :
    0 ≤ listMass a l := by
  induction l with
  | nil => exact le_rfl
  | cons i l ih => exact add_nonneg (ha i (by simp)) (ih (fun j hj => ha j (by simp [hj])))

theorem listVariation_nonneg (a b : I → ℝ) (l : List I) : 0 ≤ listVariation a b l :=
  listMass_nonneg _ _ (fun _i _ => abs_nonneg _)

theorem abs_listMass_sub_le (a b : I → ℝ) (l : List I) :
    |listMass a l - listMass b l| ≤ listVariation a b l := by
  induction l with
  | nil => simp [listMass, listVariation]
  | cons i l ih =>
    change |(a i + listMass a l) - (b i + listMass b l)| ≤ |a i - b i| + listVariation a b l
    calc
      _ = |(a i - b i) + (listMass a l - listMass b l)| := by congr 1; ring
      _ ≤ |a i - b i| + |listMass a l - listMass b l| := abs_add_le _ _
      _ ≤ _ := add_le_add le_rfl ih

theorem listMass_filter_zero (a : I → ℝ) (l : List I) :
    listMass a (l.filter (fun i => a i ≠ 0)) = listMass a l := by
  classical
  induction l with
  | nil => rfl
  | cons i l ih =>
    by_cases hi : a i = 0
    · have hd : decide (a i ≠ 0) = false := by simp only [hi, ne_eq, not_true_eq_false, decide_false]
      rw [List.filter_cons_of_neg (by rw [hd]; decide)]
      simpa only [listMass, hi, zero_add] using ih
    · have hd : decide (a i ≠ 0) = true := by exact decide_eq_true hi
      rw [List.filter_cons_of_pos (p := fun j : I => decide (a j ≠ 0)) (a := i) hd]
      simp only [listMass, ih]

theorem orderedCenter_singleton (c : ControlledContraction G) (p₀ : G)
    (v : I → G) (a : I → ℝ) (i : I) : orderedCenter c p₀ v a [i] = v i := by
  simp [orderedCenter, listMass, c.zero]

/-- Inserting a zero mass at the front does not change a positive-mass
interpolation. This is the compatibility needed at a support boundary. -/
theorem orderedCenter_zero_cons (c : ControlledContraction G) (p₀ : G)
    (v : I → G) (a : I → ℝ) (i : I) (l : List I)
    (hi : a i = 0) (hl : listMass a l ≠ 0) :
    orderedCenter c p₀ v a (i :: l) = orderedCenter c p₀ v a l := by
  simp [orderedCenter, listMass, hi, div_self hl, c.one]

/-- Erasing all zero coordinates does not change the interpolated point
when the total mass is positive. -/
theorem orderedCenter_filter_zero (c : ControlledContraction G) (p₀ : G)
    (v : I → G) (a : I → ℝ) (l : List I)
    (ha : ∀ i ∈ l, 0 ≤ a i) (hm : 0 < listMass a l) :
    orderedCenter c p₀ v a (l.filter (fun i => a i ≠ 0)) = orderedCenter c p₀ v a l := by
  classical
  induction l with
  | nil => simp [listMass] at hm
  | cons i l ih =>
    have hal : ∀ j ∈ l, 0 ≤ a j := fun j hj => ha j (by simp [hj])
    have hml := listMass_nonneg a l hal
    by_cases hi : a i = 0
    · have hpos : 0 < listMass a l := by simpa [listMass, hi] using hm
      have hd : decide (a i ≠ 0) = false := by simp only [hi, ne_eq, not_true_eq_false, decide_false]
      rw [List.filter_cons_of_neg (by rw [hd]; decide), orderedCenter_zero_cons c p₀ v a i l hi hpos.ne']
      exact ih hal hpos
    · have hd : decide (a i ≠ 0) = true := decide_eq_true hi
      rw [List.filter_cons_of_pos (p := fun j : I => decide (a j ≠ 0)) (a := i) hd]
      change c.contract (v i) (listMass a (l.filter (fun j => decide (a j ≠ 0))) /
          listMass a (i :: l.filter (fun j => decide (a j ≠ 0))))
          (orderedCenter c p₀ v a (l.filter (fun j => decide (a j ≠ 0)))) = _
      rw [listMass, listMass_filter_zero]
      by_cases hl : listMass a l = 0
      · simp [hl, orderedCenter, listMass, c.zero]
      · rw [ih hal (lt_of_le_of_ne hml (Ne.symm hl))]
        rfl

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_OrderedInterpolationRadius
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform radius of interpolation on a bounded number of vertices -/

namespace PolycyclicRecognition

variable {I G : Type*} [MetricSpace G]

theorem listMass_tail_fraction_mem (a : I → ℝ) (i : I) (l : List I)
    (ha : ∀ j ∈ i :: l, 0 ≤ a j) :
    listMass a l / listMass a (i :: l) ∈ Set.Icc (0 : ℝ) 1 := by
  have ht := listMass_nonneg a l (fun j hj => ha j (by simp [hj]))
  have htot := listMass_nonneg a (i :: l) ha
  refine ⟨div_nonneg ht htot, ?_⟩
  by_cases hz : listMass a (i :: l) = 0
  · simp [hz]
  · apply (div_le_one (lt_of_le_of_ne htot (Ne.symm hz))).mpr
    change listMass a l ≤ a i + listMass a l
    exact le_add_of_nonneg_left (ha i (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))

/-- With at most `n` input vertices of bounded diameter, interpolation
stays within a radius depending only on `n`, the diameter, and the contraction. -/
theorem exists_interpolation_radius (c : ControlledContraction G) {D : ℝ} (hD : 0 ≤ D) (n : ℕ) :
    ∃ R : ℝ, 0 ≤ R ∧ InterpolationRadius (I := I) c D n R := by
  induction n with
  | zero =>
    refine ⟨0, le_rfl, ?_⟩
    intro l p₀ v a hne hlen ha hdiam p hp
    have : l = [] := List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero hlen)
    exact (hne this).elim
  | succ n ih =>
    obtain ⟨R, hR, hrad⟩ := ih
    obtain ⟨C, hC, hcontrol⟩ := c.bounds R hR
    have hC0 : 0 ≤ C := le_trans zero_le_one hC
    refine ⟨C + D, add_nonneg hC0 hD, ?_⟩
    intro l p₀ v a hne hlen ha hdiam p hp
    cases l with
    | nil => exact (hne rfl).elim
    | cons i l =>
      cases l with
      | nil =>
        rw [orderedCenter_singleton]
        exact (hp i (by simp)).trans (le_add_of_nonneg_left hC0)
      | cons j tail =>
        have htlen : (j :: tail).length ≤ n := by simpa only [List.length_cons, Nat.add_le_add_iff_right] using hlen
        have hat : ∀ k ∈ j :: tail, 0 ≤ a k := fun k hk => ha k (List.mem_cons_of_mem i hk)
        have hdiamt : ∀ k ∈ j :: tail, ∀ m ∈ j :: tail, dist (v k) (v m) ≤ D :=
          fun k hk m hm => hdiam k (List.mem_cons_of_mem i hk) m (List.mem_cons_of_mem i hm)
        have hi : ∀ k ∈ j :: tail, dist (v k) (v i) ≤ D :=
          fun k hk => hdiam k (List.mem_cons_of_mem i hk) i (by simp)
        have hr := hrad (j :: tail) p₀ v a (by simp) htlen hat hdiamt (v i) hi
        have hs := listMass_tail_fraction_mem a i (j :: tail) ha
        have hb := c.dist_center_le hcontrol hr hs
        change dist (c.contract (v i) (listMass a (j :: tail) / listMass a (i :: j :: tail))
          (orderedCenter c p₀ v a (j :: tail))) p ≤ C + D
        exact (dist_triangle _ (v i) p).trans (add_le_add
          (hb.trans (mul_le_of_le_one_right hC0 hs.2)) (hp i (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)))

end PolycyclicRecognition

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_LipschitzInversePairBounds
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Lower quasi-isometry bounds from Lipschitz coarse inverses -/

namespace PolycyclicRecognition

open scoped NNReal

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]

/-- A Lipschitz inverse with bounded composition error supplies the lower
inequality, with the same enlarged constant used by the compact pair space. -/
theorem coarse_lower_of_lipschitz_inverse
    {Λ : ℝ≥0} (hΛ : 2 ≤ (Λ : ℝ)) (f : X → Y) (g : Y → X)
    (hg : LipschitzWith Λ g) (hinv : ∀ x, dist (g (f x)) x ≤ Λ) (x y : X) :
    (Λ : ℝ)⁻¹ * dist x y - Λ ≤ dist (f x) (f y) := by
  have hpos : 0 < (Λ : ℝ) := lt_of_lt_of_le (by norm_num) hΛ
  have hd : dist x y ≤ (Λ : ℝ) + Λ * dist (f x) (f y) + Λ := by
    calc
      dist x y ≤ dist x (g (f x)) + dist (g (f x)) (g (f y)) + dist (g (f y)) y :=
        dist_triangle4 _ _ _ _
      _ ≤ (Λ : ℝ) + Λ * dist (f x) (f y) + Λ :=
        add_le_add (add_le_add (by simpa only [dist_comm] using hinv x)
          (hg.dist_le_mul _ _)) (hinv y)
  have hdiv : (Λ : ℝ)⁻¹ * dist x y ≤ dist (f x) (f y) + 2 := by
    rw [← div_eq_inv_mul, div_le_iff₀ hpos]
    nlinarith only [hd]
  linarith only [hdiv, hΛ]

variable {G : Type*} [Group G] [MetricSpace G]

omit [Group G] in
/-- No separate lower-bound hypothesis is needed once the two Lipschitz
representatives have controlled inverse errors. -/
theorem lipschitzPairBounds_of_inverse_bounds
    {Λ : ℝ≥0} (hΛ : 2 ≤ (Λ : ℝ)) (p : C(G, G) × C(G, G))
    (hf : LipschitzWith Λ p.1) (hg : LipschitzWith Λ p.2)
    (hgf : ∀ x, dist (p.2 (p.1 x)) x ≤ Λ)
    (hfg : ∀ x, dist (p.1 (p.2 x)) x ≤ Λ) :
    LipschitzPairBounds G Λ p :=
  ⟨hf, hg, coarse_lower_of_lipschitz_inverse hΛ p.1 p.2 hg hgf,
    coarse_lower_of_lipschitz_inverse hΛ p.2 p.1 hf hfg, hgf, hfg⟩

end PolycyclicRecognition

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_PerturbedInversePairs
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Quantitative inverse bounds for bounded Lipschitz replacements -/

namespace PolycyclicRecognition

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]

/-- Perturbing a coarse inverse pair preserves its inverse error with a
constant determined only by the original controls and perturbation radii. -/
theorem inverse_error_of_bounded_perturbations
    (f f' : X → Y) (g g' : Y → X)
    {Kg Cg Df Dg E : ℝ} (hKg : 0 ≤ Kg)
    (hg : ∀ y z, dist (g y) (g z) ≤ Kg * dist y z + Cg)
    (hfclose : ∀ x, dist (f' x) (f x) ≤ Df)
    (hgclose : ∀ y, dist (g' y) (g y) ≤ Dg)
    (hinv : ∀ x, dist (g (f x)) x ≤ E) (x : X) :
    dist (g' (f' x)) x ≤ Dg + (Kg * Df + Cg) + E := by
  calc
    dist (g' (f' x)) x ≤ dist (g' (f' x)) (g (f' x)) +
        dist (g (f' x)) (g (f x)) + dist (g (f x)) x := dist_triangle4 _ _ _ _
    _ ≤ Dg + (Kg * Df + Cg) + E := by
      exact add_le_add (add_le_add (hgclose _) ((hg _ _).trans
        (add_le_add (mul_le_mul_of_nonneg_left (hfclose x) hKg) le_rfl))) (hinv x)

end PolycyclicRecognition

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_RectangleFiberMass
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Large sections inside a finite rectangle -/

noncomputable section
namespace PolycyclicRecognition

open MeasureTheory Set
open scoped ENNReal

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

theorem exists_large_sections_in_rectangle (μ : Measure X) (ν : Measure Y)
    [SFinite μ] [SFinite ν] (U : Set X) (V : Set Y)
    (hU : MeasurableSet U)
    (hUfin : μ U ≠ ∞) (hVfin : ν V ≠ ∞)
    (hUpos : 0 < (μ U).toReal) (hVpos : 0 < (ν V).toReal)
    (S : Set (X × Y)) (hS : MeasurableSet S) (hsub : S ⊆ U ×ˢ V)
    (hm : 0 < (μ.prod ν S).toReal) :
    ∃ A : Set X, MeasurableSet A ∧ A ⊆ U ∧
      (μ.prod ν S).toReal / (2 * (ν V).toReal) ≤ (μ A).toReal ∧
      ∀ x ∈ A,
        (μ.prod ν S).toReal / (2 * (μ U).toReal) ≤
          (ν (Prod.mk x ⁻¹' S)).toReal := by
  let : IsFiniteMeasure (μ.restrict U) := ⟨by simpa using hUfin.lt_top⟩
  let : IsFiniteMeasure (ν.restrict V) := ⟨by simpa using hVfin.lt_top⟩
  have hprod : (μ.restrict U).prod (ν.restrict V) S = μ.prod ν S := by
    rw [Measure.prod_restrict, Measure.restrict_apply hS, inter_eq_left.2 hsub]
  obtain ⟨A, hA, hmass, hfiber⟩ := exists_large_sections
    (μ.restrict U) (ν.restrict V) (by simpa using hUpos) (by simpa using hVpos)
    S hS (by simpa only [hprod] using hm)
  refine ⟨A ∩ U, hA.inter hU, inter_subset_right, ?_, ?_⟩
  · simpa only [hprod, Measure.restrict_apply hA, Measure.restrict_apply_univ] using hmass
  · intro x hx
    have hsV : Prod.mk x ⁻¹' S ⊆ V := fun y hy => (hsub hy).2
    have hmeas : MeasurableSet (Prod.mk x ⁻¹' S) := hS.preimage measurable_prodMk_left
    simpa only [hprod, Measure.restrict_apply_univ, Measure.restrict_apply hmeas,
      inter_eq_left.2 hsV] using hfiber x hx.1

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_PiFiberMass
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_countable _root_.OAI.PolycyclicRecognition.finitelyGeneratedSubgroupIndex_countable _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Large coordinate sections of a Euclidean cube -/

noncomputable section
namespace PolycyclicRecognition

open Set Metric MeasureTheory
open scoped ENNReal

theorem measurePreserving_cons (n : ℕ) :
    MeasurePreserving (fun z : (Fin n → ℝ) × ℝ => (Fin.cons z.2 z.1 : Fin (n + 1) → ℝ))
      ((volume : Measure (Fin n → ℝ)).prod (volume : Measure ℝ)) volume := by
  have he := (volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0).symm.comp
    (Measure.measurePreserving_swap (μ := (volume : Measure (Fin n → ℝ))) (ν := (volume : Measure ℝ)))
  convert he using 1
  all_goals try with_reducible_and_instances rfl
  ext z i
  exact Fin.cases (by simp) (fun j => by simp) i

theorem mem_closedBall_cons {n : ℕ} (R : ℝ) (hR : 0 ≤ R)
    (t : ℝ) (x : Fin n → ℝ) :
    (Fin.cons t x : Fin (n + 1) → ℝ) ∈ closedBall 0 R ↔
      t ∈ closedBall 0 R ∧ x ∈ closedBall 0 R := by
  simp only [closedBall_pi (0 : Fin (n + 1) → ℝ) hR,
    closedBall_pi (0 : Fin n → ℝ) hR, mem_pi, mem_univ, forall_const,
    Fin.forall_fin_succ, Fin.cons_zero, Pi.zero_apply, Fin.cons_succ]

theorem realVolume_cube (n : ℕ) (R : ℝ) (hR : 0 ≤ R) :
    (volume (closedBall (0 : Fin n → ℝ) R)).toReal = (2 * R) ^ n := by
  rw [Real.volume_pi_closedBall _ hR, ENNReal.toReal_ofReal (by positivity)]
  simp only [Fintype.card_fin]

theorem exists_large_coordinate_sections (n : ℕ) (R : ℝ) (hR : 0 < R)
    (S : Set (Fin (n + 1) → ℝ)) (hS : MeasurableSet S)
    (hSR : S ⊆ closedBall 0 R) (hm : 0 < (volume S).toReal) :
    ∃ A : Set (Fin n → ℝ), MeasurableSet A ∧ A ⊆ closedBall 0 R ∧
      (volume S).toReal / (4 * R) ≤ (volume A).toReal ∧
      ∀ x ∈ A, (volume S).toReal / (2 * (2 * R) ^ n) ≤
        (volume {t : ℝ | Fin.cons t x ∈ S}).toReal := by
  let T : Set ((Fin n → ℝ) × ℝ) := (fun z => Fin.cons z.2 z.1) ⁻¹' S
  have hT : MeasurableSet T := hS.preimage (measurePreserving_cons n).measurable
  have hTS : (volume.prod volume) T = volume S :=
    (measurePreserving_cons n).measure_preimage hS.nullMeasurableSet
  have hsub : T ⊆ closedBall 0 R ×ˢ closedBall 0 R := by
    intro z hz
    exact ((mem_closedBall_cons R hR.le z.2 z.1).1 (hSR hz)).symm
  have hv : (volume (closedBall (0 : ℝ) R)).toReal = 2 * R := by
    rw [Real.volume_closedBall, ENNReal.toReal_ofReal (by positivity)]
  obtain ⟨A, hA, hAR, hmass, hfiber⟩ := exists_large_sections_in_rectangle
    (volume : Measure (Fin n → ℝ)) (volume : Measure ℝ)
    (closedBall 0 R) (closedBall 0 R) measurableSet_closedBall
    (isCompact_closedBall (0 : Fin n → ℝ) R).measure_ne_top
    (isCompact_closedBall (0 : ℝ) R).measure_ne_top
    (by rw [realVolume_cube n R hR.le]; positivity) (by rw [hv]; positivity)
    T hT hsub (by rwa [hTS])
  refine ⟨A, hA, hAR, ?_, ?_⟩
  · simpa only [hTS, hv, ← mul_assoc, show (2 : ℝ) * 2 = 4 by norm_num] using hmass
  · intro x hx
    have hh := hfiber x hx
    change ((volume.prod volume) T).toReal /
      (2 * (volume (closedBall (0 : Fin n → ℝ) R)).toReal) ≤
      (volume {t : ℝ | Fin.cons t x ∈ S}).toReal at hh
    simpa only [hTS, realVolume_cube n R hR.le] using hh

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_PolynomialInterpolationBound
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Elementary interpolation estimates on measurable sets

Positive length supplies separated interpolation nodes. Lagrange interpolation
then bounds a polynomial on an interval in terms of its values on these nodes.
These bounds give the scalar Remez estimate on measurable sets.
-/

noncomputable section
namespace PolycyclicRecognition

open Set Metric MeasureTheory Polynomial
open scoped ENNReal

/-- A set of length greater than `2*n*δ` contains `n` points separated by `δ`.
No regularity of the set is needed. -/
theorem exists_separated_finset_of_length (S : Set ℝ) (δ : ℝ) (hδ : 0 < δ)
    (n : ℕ) (hm : 2 * (n : ℝ) * δ < (volume S).toReal) :
    ∃ s : Finset ℝ, s.card = n ∧ (↑s : Set ℝ) ⊆ S ∧
      ∀ x ∈ s, ∀ y ∈ s, x ≠ y → δ ≤ |x - y| := by
  classical
  induction n with
  | zero => exact ⟨∅, rfl, by simp, by simp⟩
  | succ n ih =>
    have hm' : 2 * (n : ℝ) * δ < (volume S).toReal := by
      push_cast at hm
      nlinarith
    obtain ⟨s, hs, hS, hsep⟩ := ih hm'
    have hex : ∃ x ∈ S, ∀ y ∈ s, δ ≤ |x - y| := by
      by_contra h
      have hcover : S ⊆ ⋃ y ∈ s, ball y δ := by
        intro x hx
        push Not at h
        obtain ⟨y, hy, hxy⟩ := h x hx
        exact mem_iUnion.2 ⟨y, mem_iUnion.2 ⟨hy, by simpa [Real.dist_eq] using hxy⟩⟩
      have hfinite : volume (⋃ y ∈ s, ball y δ) ≠ ∞ :=
        (measure_biUnion_lt_top s.finite_toSet (fun y _ => by
          rw [Real.volume_ball]
          exact ENNReal.ofReal_lt_top)).ne
      have hb := (measureReal_mono hcover hfinite).trans
        (measureReal_biUnion_finset_le (μ := volume) s (fun y => ball y δ))
      simp only [measureReal_def, Real.volume_ball,
        ENNReal.toReal_ofReal (by positivity : 0 ≤ 2 * δ), Finset.sum_const,
        nsmul_eq_mul, hs] at hb
      push_cast at hm
      nlinarith
    obtain ⟨x, hx, hxsep⟩ := hex
    have hxs : x ∉ s := by
      intro hx'
      have hh := hxsep x hx'
      simp only [sub_self, abs_zero] at hh
      linarith
    refine ⟨insert x s, by simp [hxs, hs], ?_, ?_⟩
    · simpa only [Finset.coe_insert] using insert_subset hx hS
    · intro a ha b hb hab
      by_cases hax : a = x
      · subst a
        exact hxsep b ((Finset.mem_insert.1 hb).resolve_left (Ne.symm hab))
      · have has : a ∈ s := (Finset.mem_insert.1 ha).resolve_left hax
        by_cases hbx : b = x
        · subst b
          simpa only [abs_sub_comm a x] using hxsep a has
        · exact hsep a has b ((Finset.mem_insert.1 hb).resolve_left hbx) hab

/-- Explicit interpolation bound, with the separation and interval radius
visible. The degree may be strictly smaller than the number of nodes. -/
theorem polynomial_bound_of_separated_nodes (p : ℝ[X]) (s : Finset ℝ)
    (hdeg : p.degree < s.card) (δ R η : ℝ) (hδ : 0 < δ)
    (hR : 0 ≤ R) (hη : 0 ≤ η)
    (hsep : ∀ a ∈ s, ∀ b ∈ s, a ≠ b → δ ≤ |a - b|)
    (hs : ∀ a ∈ s, |a| ≤ R) (hp : ∀ a ∈ s, |p.eval a| ≤ η)
    (x : ℝ) (hx : |x| ≤ R) :
    |p.eval x| ≤ (s.card : ℝ) * η * (2 * R / δ) ^ (s.card - 1) := by
  classical
  have hterm (a : ℝ) (ha : a ∈ s) :
      |(Lagrange.basis s id a).eval x| ≤ (2 * R / δ) ^ (s.card - 1) := by
    rw [Lagrange.basis, eval_prod, Finset.abs_prod]
    have hfactor (b : ℝ) (hb : b ∈ s.erase a) :
        |(Lagrange.basisDivisor (id a) (id b)).eval x| ≤ 2 * R / δ := by
      obtain ⟨hba, hb⟩ := Finset.mem_erase.1 hb
      have hsep' := hsep a ha b hb (Ne.symm hba)
      have hnum : |x - b| ≤ 2 * R := by
        have := abs_sub x b
        linarith [hs b hb]
      simp only [Lagrange.basisDivisor, eval_mul, eval_C, eval_sub,
        eval_X, id_eq, abs_mul, abs_inv]
      simpa only [div_eq_mul_inv, mul_comm] using
        (div_le_div₀ (by positivity : 0 ≤ 2 * R) hnum hδ hsep')
    calc
      (∏ b ∈ s.erase a, |(Lagrange.basisDivisor (id a) (id b)).eval x|) ≤
          ∏ _b ∈ s.erase a, (2 * R / δ) :=
        Finset.prod_le_prod (fun _ _ => abs_nonneg _) hfactor
      _ = (2 * R / δ) ^ (s.card - 1) := by
        rw [Finset.prod_const, Finset.card_erase_of_mem ha]
  have heq := Lagrange.eq_interpolate (v := id) (s := s) Function.injective_id.injOn hdeg
  conv_lhs => rw [heq, Lagrange.interpolate_apply, eval_finsetSum]
  calc
    |∑ a ∈ s, (C (p.eval (id a)) * Lagrange.basis s id a).eval x| ≤
        ∑ a ∈ s, |(C (p.eval (id a)) * Lagrange.basis s id a).eval x| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _a ∈ s, η * (2 * R / δ) ^ (s.card - 1) := by
      apply Finset.sum_le_sum
      intro a ha
      simp only [eval_mul, eval_C, id_eq, abs_mul]
      exact mul_le_mul (hp a ha) (hterm a ha) (abs_nonneg _) hη
    _ = (s.card : ℝ) * η * (2 * R / δ) ^ (s.card - 1) := by
      rw [Finset.sum_const, nsmul_eq_mul, mul_assoc]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_UnitSeparatedNet
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The locally finite unit net used for Lipschitz replacement -/

noncomputable section
namespace PolycyclicRecognition

open Set Metric

variable {X : Type*} [MetricSpace X]

/-- A maximal unit-separated set covers the whole metric space by closed
unit balls. No measure or geometric input is required for this step. -/
theorem exists_unit_separated_net :
    ∃ V : Set X, V.Pairwise (fun x y => 1 < dist x y) ∧
      ∀ x : X, ∃ v ∈ V, dist x v ≤ 1 := by
  classical
  obtain ⟨V, hV⟩ := zorn_subset {V : Set X | V.Pairwise (fun x y => 1 < dist x y)}
    (by
      intro C hC hc
      exact ⟨⋃₀ C, hc.pairwise_sUnion.mpr (fun s hs => hC hs), fun s hs => subset_sUnion_of_mem hs⟩)
  refine ⟨V, hV.1, ?_⟩
  intro x
  by_contra hn
  have hfar : ∀ v ∈ V, 1 < dist x v := by
    intro v hv
    exact lt_of_not_ge (fun h => hn ⟨v, hv, h⟩)
  have hi : (insert x V).Pairwise (fun y z => 1 < dist y z) := by
    rw [Set.pairwise_insert]
    exact ⟨hV.1, fun y hy _ => ⟨hfar y hy, by simpa only [dist_comm] using hfar y hy⟩⟩
  have hx : x ∈ V := hV.2 hi (subset_insert x V) (mem_insert x V)
  exact hn ⟨x, hx, by simp⟩

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_UniformUnitNetBound
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform multiplicity of the unit-net cover

A finite cover of a compact ball at the identity bounds the number of
separated centers at every translate. This proves the multiplicity estimate
without needing a Haar-volume comparison.
-/

noncomputable section
namespace PolycyclicRecognition

open Set Metric

variable {G : Type*} [Group G] [MetricSpace G] [ProperSpace G]
  [IsIsometricSMul G G]

theorem exists_uniform_unit_net_card (R : ℝ) :
    ∃ M : ℕ, ∀ V : Set G, V.Pairwise (fun x y => 1 < dist x y) →
      ∀ x : G, (V ∩ closedBall x R).ncard ≤ M := by
  classical
  obtain ⟨C, hC, hcover⟩ := Metric.totallyBounded_iff.mp
    (isCompact_closedBall (1 : G) R).totallyBounded (1 / 3 : ℝ) (by norm_num)
  refine ⟨C.ncard, ?_⟩
  intro V hV x
  let U := V ∩ closedBall x R
  have hc (v : U) : ∃ c : C, dist (x⁻¹ * (v : G)) c < 1 / 3 := by
    have hv : x⁻¹ * (v : G) ∈ closedBall (1 : G) R := by
      change dist (x⁻¹ * (v : G)) 1 ≤ R
      calc
        _ = dist (v : G) x := by
          simpa only [inv_mul_cancel] using dist_mul_left x⁻¹ (v : G) x
        _ ≤ R := v.property.2
    rcases mem_iUnion.mp (hcover hv) with ⟨c, hc⟩
    rcases mem_iUnion.mp hc with ⟨hc, hv⟩
    exact ⟨⟨c, hc⟩, mem_ball.mp hv⟩
  choose c hc using hc
  have hinj : Function.Injective c := by
    intro v w he
    apply Subtype.ext
    by_contra hne
    have hsep := hV v.property.1 w.property.1 hne
    have ht := dist_triangle (x⁻¹ * (v : G)) (c v : G) (x⁻¹ * (w : G))
    have hv := hc v
    have hw := hc w
    rw [← he] at hw
    rw [dist_comm (c v : G) (x⁻¹ * (w : G)), dist_mul_left] at ht
    linarith
  let : Finite C := hC.to_subtype
  have hcard := Nat.card_le_card_of_injective c hinj
  simpa only [Nat.card_coe_set_eq] using hcard

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_UnitNetPartition
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finitely supported cutoff weights on the infinite unit net -/

noncomputable section
namespace PolycyclicRecognition

open Set Metric
open scoped BigOperators

variable {X : Type*} [MetricSpace X] [ProperSpace X]
  {V : Set X} (hV : V.Pairwise (fun x y => 1 < dist x y))

theorem mem_support_unitNetMass_iff (x : X) (v : V) :
    v ∈ (unitNetMass hV x).support ↔ dist x v < 2 := by
  rw [Finsupp.mem_support_iff, unitNetMass_apply]
  constructor
  · intro h
    by_contra hn
    exact h (max_eq_left (by linarith))
  · intro h he
    have := le_max_right (0 : ℝ) (2 - dist x v)
    rw [he] at this
    linarith

theorem unitNetMass_nonneg (x : X) (v : V) : 0 ≤ unitNetMass hV x v :=
  le_max_left _ _

theorem one_le_unitNetTotal (hcover : ∀ x : X, ∃ v ∈ V, dist x v ≤ 1) (x : X) :
    1 ≤ unitNetTotal hV x := by
  obtain ⟨v, hv, hd⟩ := hcover x
  have hp : 1 ≤ unitNetMass hV x ⟨v, hv⟩ := by
    exact (by linarith : 1 ≤ 2 - dist x v).trans (le_max_right _ _)
  have hm : (⟨v, hv⟩ : V) ∈ (unitNetMass hV x).support := by
    apply Finsupp.mem_support_iff.mpr
    linarith
  exact hp.trans (Finset.single_le_sum (fun i _ => unitNetMass_nonneg hV x i) hm)

theorem unitNetPartition_nonneg (x : X) (v : V) : 0 ≤ unitNetPartition hV x v :=
  mul_nonneg (inv_nonneg.mpr (Finset.sum_nonneg (fun i _ => unitNetMass_nonneg hV x i)))
    (unitNetMass_nonneg hV x v)

theorem unitNetPartition_total (hcover : ∀ x : X, ∃ v ∈ V, dist x v ≤ 1) (x : X) :
    (unitNetPartition hV x).sum (fun _ a => a) = 1 := by
  have ht : unitNetTotal hV x ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one (one_le_unitNetTotal hV hcover x))
  rw [unitNetPartition, Finsupp.sum_smul_index' (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)]
  change (∑ i ∈ (unitNetMass hV x).support, (unitNetTotal hV x)⁻¹ * unitNetMass hV x i) = 1
  rw [← Finset.mul_sum]
  change (unitNetTotal hV x)⁻¹ * unitNetTotal hV x = 1
  exact inv_mul_cancel₀ ht

theorem unitNetTotal_eq_sum (x : X) (s : Finset V)
    (hs : (unitNetMass hV x).support ⊆ s) :
    unitNetTotal hV x = ∑ v ∈ s, max 0 (2 - dist x v) := by
  exact Finsupp.sum_of_support_subset _ hs _ (by simp)

/-- On any finite set containing the support, the global partition agrees
with the finite-dimensional cutoff partition. -/
theorem cutoffPartition_eq_unitNetPartition (x : X) (s : Finset V)
    (hs : (unitNetMass hV x).support ⊆ s) (v : s) :
    cutoffPartition (fun u : s => (u.val : X)) x v = unitNetPartition hV x v.val := by
  have he : ‖cutoffMass (fun u : s => (u.val : X)) x‖ = unitNetTotal hV x := by
    rw [PiLp.norm_eq_of_L1, unitNetTotal_eq_sum hV x s hs]
    change (∑ u : s, ‖max 0 (2 - dist x (u.val : X))‖) = _
    simp only [Real.norm_of_nonneg (le_max_left (0 : ℝ) _)]
    exact Finset.sum_coe_sort s (fun u : V => max 0 (2 - dist x u))
  change ‖cutoffMass (fun u : s => (u.val : X)) x‖⁻¹ * max 0 (2 - dist x (v.val : X)) = _
  rw [he]
  rfl

theorem unitNetPartition_variation_on_finset
    (hcover : ∀ x : X, ∃ v ∈ V, dist x v ≤ 1) (x y : X) (s : Finset V)
    (hx : (unitNetMass hV x).support ⊆ s)
    (hy : (unitNetMass hV y).support ⊆ s) :
    (∑ v ∈ s, |unitNetPartition hV x v - unitNetPartition hV y v|) ≤
      2 * (s.card : ℝ) * dist x y := by
  have cover (z : X) (hz : (unitNetMass hV z).support ⊆ s) :
      ∃ u : s, dist z (u.val : X) ≤ 1 := by
    obtain ⟨v, hv, hd⟩ := hcover z
    have hm := (mem_support_unitNetMass_iff hV z ⟨v, hv⟩).mpr (by linarith)
    exact ⟨⟨⟨v, hv⟩, hz hm⟩, hd⟩
  have h := norm_cutoffPartition_sub_le (fun u : s => (u.val : X)) x y (cover x hx) (cover y hy)
  rw [PiLp.norm_eq_of_L1] at h
  simp only [PiLp.sub_apply, Real.norm_eq_abs, cutoffPartition_eq_unitNetPartition hV x s hx,
    cutoffPartition_eq_unitNetPartition hV y s hy, Fintype.card_coe] at h
  calc
    _ = ∑ v : s, |unitNetPartition hV x v.val - unitNetPartition hV y v.val| :=
      (Finset.sum_coe_sort s (fun v : V => |unitNetPartition hV x v - unitNetPartition hV y v|)).symm
    _ ≤ _ := h

theorem unitNetMass_support_card_le {M : ℕ}
    (hM : ∀ x : X, (V ∩ closedBall x 2).ncard ≤ M) (x : X) :
    (unitNetMass hV x).support.card ≤ M := by
  classical
  let B := V ∩ closedBall x 2
  let : Finite B := (finite_unit_net_ball hV x 2).to_subtype
  let j : (unitNetMass hV x).support → B := fun v =>
    ⟨v.val.val, v.val.property, by
      rw [mem_closedBall, dist_comm]
      exact ((mem_support_unitNetMass_iff hV x v.val).mp v.property).le⟩
  have hj : Function.Injective j := by
    intro v w he
    have he' : v.val.val = w.val.val := congrArg (fun z : B => z.val) he
    exact Subtype.ext (Subtype.ext he')
  have h := Nat.card_le_card_of_injective j hj
  simp only [Nat.card_eq_finsetCard, Nat.card_coe_set_eq] at h
  exact h.trans (hM x)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_CompatibleMetricComparison
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instNonemptyBases _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_nonempty _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Comparing the two compatible metrics used in height rigidity -/

noncomputable section
namespace PolycyclicRecognition

/-- Any two proper, compatible, left-invariant chain metrics on the same
group have affine comparison bounds. This is applied to the fixed metric
and the chosen Riemannian metric, with the identity map on the group. -/
theorem ProperChainMetric.compare
    {G : Type} [Group G] [TopologicalSpace G]
    (d₁ d₂ : ProperChainMetric G) :
    ∃ K C : ℝ, 0 ≤ K ∧ 0 ≤ C ∧ ∀ x y : G,
      @dist G d₂.compatibleMetric.toPseudoMetricSpace.toDist x y ≤
        K * @dist G d₁.compatibleMetric.toPseudoMetricSpace.toDist x y + C := by
  let := d₁.compatibleMetric
  let := d₁.proper_compatibleMetric
  let := d₁.isometric_compatibleMetric
  let len : G → ℝ := fun x => @dist G d₂.compatibleMetric.toPseudoMetricSpace.toDist 1 x
  have hcont : Continuous len := by
    let := d₂.compatibleMetric
    exact continuous_const.dist continuous_id
  let chains := d₁.chains_compatibleMetric
  obtain ⟨D, hD⟩ := (isCompact_closedBall (1 : G) chains.step).bddAbove_image hcont.continuousOn
  let b := max D 0
  have hb : 0 ≤ b := le_max_right _ _
  have hstep (x y : G) (hxy : dist x y ≤ chains.step) :
      @dist G d₂.compatibleMetric.toPseudoMetricSpace.toDist x y ≤ b := by
    have hx : x⁻¹ * y ∈ Metric.closedBall (1 : G) chains.step := by
      simpa only [Metric.mem_closedBall, dist_comm (x⁻¹ * y), dist_one_groupDifference] using hxy
    have hz : len (x⁻¹ * y) ≤ D := hD (Set.mem_image_of_mem _ hx)
    have hid : len (x⁻¹ * y) =
        @dist G d₂.compatibleMetric.toPseudoMetricSpace.toDist x y := by
      let := d₂.compatibleMetric
      let := d₂.isometric_compatibleMetric
      exact dist_one_groupDifference x y
    rw [hid] at hz
    exact hz.trans (le_max_left _ _)
  refine ⟨b * chains.slope, b * chains.error, mul_nonneg hb chains.slope_nonneg,
    mul_nonneg hb chains.error_nonneg, ?_⟩
  exact @LinearMetricChains.coarseLipschitz G G
    d₁.compatibleMetric.toPseudoMetricSpace d₂.compatibleMetric.toPseudoMetricSpace
    chains id b hb hstep

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_CoarsePairMetricChange
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform coarse-pair estimates under a change of compatible metric -/

noncomputable section
namespace PolycyclicRecognition

theorem coarse_pair_metric_change
    {G P : Type} [Group G] [TopologicalSpace G]
    (d₁ d₂ : ProperChainMetric G) {κ ξ ε : ℝ}
    (hκ : 0 ≤ κ) (hξ : 0 ≤ ξ) (hε : 0 ≤ ε)
    (f g : P → G → G)
    (hf : letI := d₁.compatibleMetric
      ∀ p x y, dist (f p x) (f p y) ≤ κ * dist x y + ξ)
    (hg : letI := d₁.compatibleMetric
      ∀ p x y, dist (g p x) (g p y) ≤ κ * dist x y + ξ)
    (hgf : letI := d₁.compatibleMetric; ∀ p x, dist (g p (f p x)) x ≤ ε)
    (hfg : letI := d₁.compatibleMetric; ∀ p x, dist (f p (g p x)) x ≤ ε) :
    letI := d₂.compatibleMetric
    ∃ κ' ξ' ε' : ℝ, 0 ≤ κ' ∧ 0 ≤ ξ' ∧ 0 ≤ ε' ∧
      (∀ p x y, dist (f p x) (f p y) ≤ κ' * dist x y + ξ') ∧
      (∀ p x y, dist (g p x) (g p y) ≤ κ' * dist x y + ξ') ∧
      (∀ p x, dist (g p (f p x)) x ≤ ε') ∧
      (∀ p x, dist (f p (g p x)) x ≤ ε') := by
  obtain ⟨a, b, ha, hb, h₁₂⟩ := d₁.compare d₂
  obtain ⟨a', b', ha', hb', h₂₁⟩ := d₂.compare d₁
  let := d₂.compatibleMetric
  let oldDist := @dist G d₁.compatibleMetric.toPseudoMetricSpace.toDist
  have hcontrol (F : P → G → G)
      (hF : ∀ p x y, oldDist (F p x) (F p y) ≤ κ * oldDist x y + ξ) :
      ∀ p x y, dist (F p x) (F p y) ≤
        (a * κ * a') * dist x y + (a * κ * b' + a * ξ + b) := by
    intro p x y
    calc
      _ ≤ a * oldDist (F p x) (F p y) + b := h₁₂ _ _
      _ ≤ a * (κ * oldDist x y + ξ) + b := by gcongr; exact hF p x y
      _ ≤ a * (κ * (a' * dist x y + b') + ξ) + b := by gcongr; exact h₂₁ x y
      _ = _ := by ring
  refine ⟨a * κ * a', a * κ * b' + a * ξ + b, a * ε + b,
    by positivity, by positivity, by positivity, hcontrol f hf, hcontrol g hg, ?_, ?_⟩
  · intro p x
    exact (h₁₂ _ _).trans (add_le_add (mul_le_mul_of_nonneg_left (hgf p x) ha) le_rfl)
  · intro p x
    exact (h₁₂ _ _).trans (add_le_add (mul_le_mul_of_nonneg_left (hfg p x) ha) le_rfl)

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
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_UnivariateRemez
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # An elementary one-variable Remez bound

The constant is deliberately coarse. Only a fixed power of inverse length is
needed in the subexponential geometric argument.
-/

noncomputable section
namespace PolycyclicRecognition

open Set Metric MeasureTheory Polynomial

theorem univariate_remez_bound (D : ℕ) (hD : 1 ≤ D) (p : ℝ[X])
    (hp : p.natDegree ≤ D) (R : ℝ) (hR : 1 ≤ R)
    (S : Set ℝ) (hS : S ⊆ closedBall 0 R) (hm : 0 < (volume S).toReal)
    (η : ℝ) (hη : 0 ≤ η) (hvalues : ∀ x ∈ S, |p.eval x| ≤ η)
    (x : ℝ) (hx : x ∈ closedBall 0 R) :
    |p.eval x| ≤
      (8 * ((D + 1 : ℕ) : ℝ) ^ 2 * (1 + R) / (volume S).toReal) ^ D * η := by
  classical
  let N : ℝ := (D + 1 : ℕ)
  let m := (volume S).toReal
  let δ := m / (4 * N)
  have hN : 1 ≤ N := by dsimp [N]; norm_cast; omega
  have hNpos : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have hδ : 0 < δ := div_pos hm (by positivity)
  have hlength : 2 * N * δ < m := by
    dsimp [δ]
    field_simp
    nlinarith
  obtain ⟨s, hs, hsS, hsep⟩ :=
    exists_separated_finset_of_length S δ hδ (D + 1) hlength
  have hdegree : p.degree < s.card := by
    rw [hs]
    exact (natDegree_le_iff_degree_le.mp hp).trans_lt (by exact_mod_cast Nat.lt_succ_self D)
  have hR0 : 0 ≤ R := zero_le_one.trans hR
  have hb := polynomial_bound_of_separated_nodes p s hdegree δ R η hδ hR0 hη hsep
    (fun a ha => by simpa [mem_closedBall, Real.dist_eq] using hS (hsS ha))
    (fun a ha => hvalues a (hsS ha)) x
    (by simpa [mem_closedBall, Real.dist_eq] using hx)
  rw [hs, Nat.add_sub_cancel] at hb
  change |p.eval x| ≤ N * η * (2 * R / δ) ^ D at hb
  have hNpow : N ≤ N ^ D := by
    calc
      N = N ^ 1 := (pow_one N).symm
      _ ≤ N ^ D := pow_le_pow_right₀ hN hD
  have hbase : N * (2 * R / δ) ≤ 8 * N ^ 2 * (1 + R) / m := by
    have heq : N * (2 * R / δ) = 8 * N ^ 2 * R / m := by
      dsimp [δ]
      field_simp
      ring
    rw [heq]
    exact div_le_div_of_nonneg_right (by nlinarith [sq_nonneg N]) hm.le
  calc
    |p.eval x| ≤ N * η * (2 * R / δ) ^ D := hb
    _ ≤ N ^ D * η * (2 * R / δ) ^ D := by gcongr
    _ = (N * (2 * R / δ)) ^ D * η := by rw [mul_pow]; ring
    _ ≤ (8 * N ^ 2 * (1 + R) / m) ^ D * η := by
      apply mul_le_mul_of_nonneg_right _ hη
      exact pow_le_pow_left₀ (by positivity) hbase D

/-- The scalar interval sublevel estimate. -/
theorem exists_univariate_remez_constant (D : ℕ) (hD : 1 ≤ D) :
    ∃ A : ℝ, 0 < A ∧
      ∀ (p : ℝ[X]), p.natDegree ≤ D → ∀ R : ℝ, 1 ≤ R →
      ∀ S : Set ℝ, S ⊆ closedBall 0 R → 0 < (volume S).toReal →
      ∀ η : ℝ, 0 ≤ η → (∀ x ∈ S, |p.eval x| ≤ η) →
      ∀ x ∈ closedBall 0 R,
        |p.eval x| ≤ (A * (1 + R) / (volume S).toReal) ^ D * η := by
  refine ⟨8 * ((D + 1 : ℕ) : ℝ) ^ 2, by positivity, ?_⟩
  exact fun p hp R hR S hS hm η hη hv x hx =>
    univariate_remez_bound D hD p hp R hR S hS hm η hη hv x hx

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_CoordinateRemez
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A coarse multivariable Remez inequality by slicing

Iterating the elementary interval estimate loses a factor of dimension in the
exponent. The geometric application only requires a fixed polynomial loss.
-/

noncomputable section
namespace PolycyclicRecognition

open Set Metric MeasureTheory

theorem coordinate_polynomial_remez (n D : ℕ) (hD : 1 ≤ D) :
    ∃ A : ℝ, 0 < A ∧
      ∀ f : (Fin n → ℝ) → ℝ, CoordinatePolynomial n D f →
      ∀ R : ℝ, 1 ≤ R → ∀ S : Set (Fin n → ℝ),
      MeasurableSet S → S ⊆ closedBall 0 R → 0 < (volume S).toReal →
      ∀ η : ℝ, 0 ≤ η → (∀ x ∈ S, |f x| ≤ η) →
      ∀ x ∈ closedBall 0 R,
        |f x| ≤ (A * (1 + R) ^ n / (volume S).toReal) ^ (n * D) * η := by
  classical
  obtain ⟨C, hC, hline⟩ := exists_univariate_remez_constant D hD
  induction n with
  | zero =>
    refine ⟨1, by norm_num, ?_⟩
    intro f _ R _ S _ _ hm η _ hv x _
    have hne : S.Nonempty := by
      by_contra h
      have he := Set.not_nonempty_iff_eq_empty.mp h
      simp [he] at hm
    obtain ⟨y, hy⟩ := hne
    have he : y = x := Subsingleton.elim _ _
    simpa only [zero_mul, pow_zero, one_mul, he] using hv y hy
  | succ n ih =>
    obtain ⟨A, hA, hind⟩ := ih
    let B := max (2 ^ (n + 1) * C) (4 * A)
    have hB : 0 < B := (by positivity : 0 < 4 * A).trans_le (le_max_right _ _)
    refine ⟨B, hB, ?_⟩
    intro f hf R hR S hS hSR hm η hη hv x hx
    have hRpos : 0 < R := zero_lt_one.trans_le hR
    have hR0 : 0 ≤ R := hRpos.le
    let m := (volume S).toReal
    let q := m / (2 * (2 * R) ^ n)
    have hq : 0 < q := by dsimp [q, m] <;> positivity
    obtain ⟨T, hT, hTR, hmass, hfib⟩ :=
      exists_large_coordinate_sections n R hRpos S hS hSR hm
    have hTpos : 0 < (volume T).toReal :=
      (div_pos hm (by positivity : 0 < 4 * R)).trans_le hmass
    let b := B * (1 + R) ^ (n + 1) / m
    have hb : 0 < b := by dsimp [b, m] <;> positivity
    let η' := b ^ D * η
    have hη' : 0 ≤ η' := by dsimp [η'] <;> positivity
    have hx' : x 0 ∈ closedBall 0 R ∧ Fin.tail x ∈ closedBall 0 R :=
      (mem_closedBall_cons R hR0 (x 0) (Fin.tail x)).mp (by simpa only [Fin.cons_self_tail] using hx)
    have hvT (y : Fin n → ℝ) (hy : y ∈ T) : |f (Fin.cons (x 0) y)| ≤ η' := by
      let E := {t : ℝ | Fin.cons t y ∈ S}
      have hE : E ⊆ closedBall 0 R := fun t ht =>
        ((mem_closedBall_cons R hR0 t y).mp (hSR ht)).1
      have hEm : q ≤ (volume E).toReal := hfib y hy
      have hEpos : 0 < (volume E).toReal := hq.trans_le hEm
      obtain ⟨p, hp, he⟩ := hf.head y
      have hh := hline p hp R hR E hE hEpos η hη
        (fun t ht => by rw [he]; exact hv _ ht) (x 0) hx'.1
      rw [he] at hh
      have hratio : C * (1 + R) / (volume E).toReal ≤ b := by
        calc
          C * (1 + R) / (volume E).toReal ≤ C * (1 + R) / q :=
            div_le_div_of_nonneg_left (by positivity) hq hEm
          _ = (2 ^ (n + 1) * C) * (1 + R) * R ^ n / m := by
            dsimp [q]
            rw [mul_pow, pow_succ]
            field_simp
          _ ≤ B * (1 + R) ^ (n + 1) / m := by
            apply div_le_div_of_nonneg_right _ hm.le
            calc
              (2 ^ (n + 1) * C) * (1 + R) * R ^ n ≤
                  B * (1 + R) * (1 + R) ^ n := by
                apply mul_le_mul
                · exact mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
                · exact pow_le_pow_left₀ hR0 (by linarith) n
                · positivity
                · positivity
              _ = B * (1 + R) ^ (n + 1) := by rw [pow_succ]; ring
      exact hh.trans (mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (by positivity) hratio D) hη)
    have hpoint := hind (fun y => f (Fin.cons (x 0) y)) (hf.tail (x 0))
      R hR T hT hTR hTpos η' hη' hvT (Fin.tail x) hx'.2
    rw [Fin.cons_self_tail] at hpoint
    have hratio : A * (1 + R) ^ n / (volume T).toReal ≤ b := by
      calc
        A * (1 + R) ^ n / (volume T).toReal ≤
            A * (1 + R) ^ n / (m / (4 * R)) :=
          div_le_div_of_nonneg_left (by positivity) (div_pos hm (by positivity)) hmass
        _ = (4 * A) * R * (1 + R) ^ n / m := by field_simp
        _ ≤ B * (1 + R) ^ (n + 1) / m := by
          apply div_le_div_of_nonneg_right _ hm.le
          calc
            (4 * A) * R * (1 + R) ^ n ≤ B * (1 + R) * (1 + R) ^ n := by
              apply mul_le_mul_of_nonneg_right _ (by positivity)
              exact mul_le_mul (le_max_right _ _) (by linarith) hR0 hB.le
            _ = B * (1 + R) ^ (n + 1) := by rw [pow_succ]; ring
    calc
      |f x| ≤ (A * (1 + R) ^ n / (volume T).toReal) ^ (n * D) * η' := hpoint
      _ ≤ b ^ (n * D) * η' := mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (by positivity) hratio _) hη'
      _ = b ^ ((n + 1) * D) * η := by
        dsimp [η']
        rw [← mul_assoc, ← pow_add]
        congr 2
        ring

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_OrderedInterpolationWeights
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Stability of ordered interpolation under changes of mass -/

namespace PolycyclicRecognition

variable {I G : Type*} [MetricSpace G]

/-- On lists of bounded length and bounded image diameter, ordered
interpolation is uniformly Lipschitz on probability weights. The stronger
weighted estimate also covers vanishing tail masses in the recursion. -/
theorem exists_interpolation_weight_control (c : ControlledContraction G)
    {D : ℝ} (hD : 0 ≤ D) (n : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ InterpolationWeightControl (I := I) c D n K := by
  induction n with
  | zero =>
    refine ⟨0, le_rfl, ?_⟩
    intro l p₀ v a b hlen ha hb hdiam
    have hl : l = [] := List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero hlen)
    simp [hl, listMass, listVariation]
  | succ n ih =>
    obtain ⟨K, hK, hweight⟩ := ih
    obtain ⟨R, hR, hrad⟩ := exists_interpolation_radius (I := I) c hD n
    obtain ⟨C, hC, hcontrol⟩ := c.bounds R hR
    have hC0 : 0 ≤ C := le_trans zero_le_one hC
    refine ⟨C * (2 + K), mul_nonneg hC0 (by linarith), ?_⟩
    intro l p₀ v a b hlen ha hb hdiam
    cases l with
    | nil => simp [listMass, listVariation]
    | cons i l =>
      cases l with
      | nil =>
        simp only [orderedCenter_singleton, dist_self, mul_zero]
        exact mul_nonneg (mul_nonneg hC0 (by linarith)) (listVariation_nonneg a b [i])
      | cons j tail =>
        let l := j :: tail
        have hlt : l.length ≤ n := by
          change (j :: tail).length ≤ n
          simpa only [List.length_cons, Nat.add_le_add_iff_right] using hlen
        have hat : ∀ k ∈ l, 0 ≤ a k := fun k hk => ha k (List.mem_cons_of_mem i hk)
        have hbt : ∀ k ∈ l, 0 ≤ b k := fun k hk => hb k (List.mem_cons_of_mem i hk)
        have hdiamt : ∀ k ∈ l, ∀ m ∈ l, dist (v k) (v m) ≤ D :=
          fun k hk m hm => hdiam k (List.mem_cons_of_mem i hk) m (List.mem_cons_of_mem i hm)
        have hi : ∀ k ∈ l, dist (v k) (v i) ≤ D :=
          fun k hk => hdiam k (List.mem_cons_of_mem i hk) i (by simp)
        have hra := hrad l p₀ v a (by simp [l]) hlt hat hdiamt (v i) hi
        have hrb := hrad l p₀ v b (by simp [l]) hlt hbt hdiamt (v i) hi
        have hA := listMass_nonneg a (i :: l) ha
        have hB := listMass_nonneg b (i :: l) hb
        have hU := listMass_nonneg a l hat
        have hV := listMass_nonneg b l hbt
        have hδ := listVariation_nonneg a b (i :: l)
        change min (listMass a (i :: l)) (listMass b (i :: l)) *
          dist (orderedCenter c p₀ v a (i :: l)) (orderedCenter c p₀ v b (i :: l)) ≤ _
        by_cases hAz : listMass a (i :: l) = 0
        · rw [hAz, min_eq_left hB, zero_mul]
          exact mul_nonneg (mul_nonneg hC0 (by linarith)) hδ
        by_cases hBz : listMass b (i :: l) = 0
        · rw [hBz, min_eq_right hA, zero_mul]
          exact mul_nonneg (mul_nonneg hC0 (by linarith)) hδ
        have hAp : 0 < listMass a (i :: l) := lt_of_le_of_ne hA (Ne.symm hAz)
        have hBp : 0 < listMass b (i :: l) := lt_of_le_of_ne hB (Ne.symm hBz)
        have huA : listMass a l ≤ listMass a (i :: l) := by
          change _ ≤ a i + listMass a l
          exact le_add_of_nonneg_left (ha i (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))
        have hvB : listMass b l ≤ listMass b (i :: l) := by
          change _ ≤ b i + listMass b l
          exact le_add_of_nonneg_left (hb i (by simp))
        have hsa := listMass_tail_fraction_mem a i l ha
        have hsb := listMass_tail_fraction_mem b i l hb
        have hc := hcontrol (v i) (orderedCenter c p₀ v a l) (orderedCenter c p₀ v b l)
          hra hrb _ hsa _ hsb
        have hm : 0 ≤ min (listMass a (i :: l)) (listMass b (i :: l)) := le_min hA hB
        have htime := min_mass_mul_abs_fraction_sub_le hAp hBp hU huA hV hvB
        have htime' : min (listMass a (i :: l)) (listMass b (i :: l)) *
            |listMass a l / listMass a (i :: l) - listMass b l / listMass b (i :: l)| ≤
            2 * listVariation a b (i :: l) := by
          have h₁ := abs_listMass_sub_le a b l
          have h₂ := abs_listMass_sub_le a b (i :: l)
          have htail : listVariation a b l ≤ listVariation a b (i :: l) := by
            change _ ≤ |a i - b i| + listVariation a b l
            exact le_add_of_nonneg_left (abs_nonneg _)
          linarith
        have hspace := min_mass_mul_min_fraction_le hAp hBp hU hV
        have hspace' : min (listMass a (i :: l)) (listMass b (i :: l)) *
            min (listMass a l / listMass a (i :: l)) (listMass b l / listMass b (i :: l)) *
              dist (orderedCenter c p₀ v a l) (orderedCenter c p₀ v b l) ≤
            K * listVariation a b l := by
          exact (mul_le_mul_of_nonneg_right hspace dist_nonneg).trans
            (hweight l p₀ v a b hlt hat hbt hdiamt)
        have htail : listVariation a b l ≤ listVariation a b (i :: l) := by
          change _ ≤ |a i - b i| + listVariation a b l
          exact le_add_of_nonneg_left (abs_nonneg _)
        have hc' := mul_le_mul_of_nonneg_left hc hm
        change min (listMass a (i :: l)) (listMass b (i :: l)) *
          dist (c.contract (v i) _ _) (c.contract (v i) _ _) ≤ _
        calc
          _ ≤ C * (2 * listVariation a b (i :: l) + K * listVariation a b l) := by
            nlinarith only [hc', mul_le_mul_of_nonneg_left htime' hC0,
              mul_le_mul_of_nonneg_left hspace' hC0]
          _ ≤ C * (2 + K) * listVariation a b (i :: l) := by
            nlinarith only [mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left htail hK) hC0]

end PolycyclicRecognition

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_FiniteSupportInterpolation
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Compatible interpolation on finite supports -/

noncomputable section
namespace PolycyclicRecognition

open scoped BigOperators

variable {I G : Type*} [LinearOrder I] [MetricSpace G]

omit [LinearOrder I] in
theorem listMass_eq_list_sum (a : I → ℝ) (l : List I) :
    listMass a l = (l.map a).sum := by
  induction l with
  | nil => rfl
  | cons i l ih => simpa only [listMass, List.map_cons, List.sum_cons] using congrArg (a i + ·) ih

theorem listMass_sort (a : I → ℝ) (s : Finset I) :
    listMass a (s.sort (· ≤ ·)) = ∑ i ∈ s, a i := by
  rw [listMass_eq_list_sum]
  change Multiset.sum (Multiset.map a (s.sort (· ≤ ·) : Multiset I)) = _
  rw [Finset.sort_eq]
  rfl

theorem filter_sort_support (a : I →₀ ℝ) (s : Finset I) (hs : a.support ⊆ s) :
    (s.sort (· ≤ ·)).filter (fun i => a i ≠ 0) = a.support.sort (· ≤ ·) := by
  classical
  let l := (s.sort (· ≤ ·)).filter (fun i => a i ≠ 0)
  have hl : l.toFinset = a.support := by
    ext i
    simp only [l, List.mem_toFinset, List.mem_filter, Finset.mem_sort, decide_eq_true_eq,
      Finsupp.mem_support_iff]
    exact ⟨fun h => h.2, fun h => ⟨hs (Finsupp.mem_support_iff.mpr h), h⟩⟩
  have hp : l.Pairwise (· ≤ ·) := (s.pairwise_sort (· ≤ ·)).filter _
  have hn : l.Nodup := (s.sort_nodup (· ≤ ·)).filter _
  have h := (List.toFinset_sort (r := (· ≤ ·)) hn).mpr hp
  rw [hl] at h
  exact h.symm

theorem finiteSupportCenter_eq_on_superset (c : ControlledContraction G) (p₀ : G)
    (v : I → G) (a : I →₀ ℝ) (s : Finset I) (hs : a.support ⊆ s)
    (ha : ∀ i, 0 ≤ a i) (hm : 0 < a.sum (fun _ r => r)) :
    finiteSupportCenter c p₀ v a = orderedCenter c p₀ v a (s.sort (· ≤ ·)) := by
  have hsum : listMass a (s.sort (· ≤ ·)) = a.sum (fun _ r => r) := by
    rw [listMass_sort, Finsupp.sum_of_support_subset _ hs _ (by simp)]
  have h := orderedCenter_filter_zero c p₀ v a (s.sort (· ≤ ·)) (fun i _ => ha i) (hsum.symm ▸ hm)
  rw [filter_sort_support a s hs] at h
  exact h

/-- A common finite support allows the list stability estimate to compare
two probability vectors, even when some coordinates vanish in just one. -/
theorem finiteSupportCenter_dist_le (c : ControlledContraction G) {D K : ℝ} {n : ℕ}
    (hK : InterpolationWeightControl (I := I) c D n K) (p₀ : G) (v : I → G)
    (a b : I →₀ ℝ) (s : Finset I)
    (has : a.support ⊆ s) (hbs : b.support ⊆ s) (hs : s.card ≤ n)
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i)
    (ham : a.sum (fun _ r => r) = 1) (hbm : b.sum (fun _ r => r) = 1)
    (hdiam : ∀ i ∈ s, ∀ j ∈ s, dist (v i) (v j) ≤ D) :
    dist (finiteSupportCenter c p₀ v a) (finiteSupportCenter c p₀ v b) ≤
      K * (∑ i ∈ s, |a i - b i|) := by
  have hm (u : I →₀ ℝ) (hu : u.support ⊆ s) (hut : u.sum (fun _ r => r) = 1) :
      listMass u (s.sort (· ≤ ·)) = 1 := by
    rw [listMass_sort, ← Finsupp.sum_of_support_subset u hu (fun _ (r : ℝ) => r) (by simp), hut]
  rw [finiteSupportCenter_eq_on_superset c p₀ v a s has ha (by rw [ham]; norm_num),
    finiteSupportCenter_eq_on_superset c p₀ v b s hbs hb (by rw [hbm]; norm_num)]
  have h := hK (s.sort (· ≤ ·)) p₀ v a b (by simpa using hs)
    (fun i _ => ha i) (fun i _ => hb i)
    (fun i hi j hj => hdiam i ((Finset.mem_sort (· ≤ ·)).mp hi) j ((Finset.mem_sort (· ≤ ·)).mp hj))
  rw [hm a has ham, hm b hbs hbm, min_self, one_mul] at h
  simpa only [listVariation, listMass_sort] using h

theorem finiteSupportCenter_dist_anchor_le (c : ControlledContraction G) {D R : ℝ} {n : ℕ}
    (hR : InterpolationRadius (I := I) c D n R) (p₀ : G) (v : I → G) (a : I →₀ ℝ)
    (ha : ∀ i, 0 ≤ a i) (ham : a.sum (fun _ r => r) = 1) (hcard : a.support.card ≤ n)
    (hdiam : ∀ i ∈ a.support, ∀ j ∈ a.support, dist (v i) (v j) ≤ D)
    (p : G) (hp : ∀ i ∈ a.support, dist (v i) p ≤ D) :
    dist (finiteSupportCenter c p₀ v a) p ≤ R := by
  have hsum : listMass a (a.support.sort (· ≤ ·)) = 1 := by
    rw [listMass_sort]
    exact ham
  have hne : a.support.sort (· ≤ ·) ≠ [] := by
    intro hn
    rw [hn] at hsum
    norm_num [listMass] at hsum
  exact hR _ p₀ v a hne (by simpa using hcard) (fun i _ => ha i)
    (fun i hi j hj => hdiam i ((Finset.mem_sort (· ≤ ·)).mp hi) j ((Finset.mem_sort (· ≤ ·)).mp hj))
    p (fun i hi => hp i ((Finset.mem_sort (· ≤ ·)).mp hi))

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_LocalLipschitzMinimizing
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # From a fixed-radius Lipschitz bound to the global bound -/

namespace PolycyclicRecognition

open Set
open scoped NNReal

theorem lipschitzWith_of_unit_local_bound
    {G Y : Type*} [Group G] [MetricSpace G] [IsIsometricSMul G G] [MetricSpace Y]
    (hpath : ∀ g : G, ∃ γ : ℝ → G, γ 0 = 1 ∧ γ 1 = g ∧
      ∀ t ∈ Icc (0 : ℝ) 1, ∀ u ∈ Icc (0 : ℝ) 1,
        dist (γ t) (γ u) ≤ dist 1 g * |t - u|)
    {K : ℝ≥0} (f : G → Y)
    (hf : ∀ x y, dist x y ≤ 1 → dist (f x) (f y) ≤ K * dist x y) :
    LipschitzWith K f := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  obtain ⟨γ, h0, h1, hγ⟩ := hpath (x⁻¹ * y)
  let D := dist 1 (x⁻¹ * y)
  let n := ⌊D⌋₊ + 1
  have hn : 0 < n := Nat.succ_pos _
  have hnr : 0 < (n : ℝ) := by exact_mod_cast hn
  have hDn : D ≤ (n : ℝ) := by simpa [n] using (Nat.lt_floor_add_one D).le
  let p : ℕ → G := fun k => x * γ ((k : ℝ) / n)
  have hp0 : p 0 = x := by simp [p, h0]
  have hpn : p n = y := by simp [p, h1, hnr.ne']
  have hp (k : ℕ) (hk : k < n) : dist (p k) (p (k + 1)) ≤ D / (n : ℝ) := by
    have ht : (k : ℝ) / n ∈ Icc (0 : ℝ) 1 :=
      ⟨by positivity, (div_le_one hnr).mpr (by exact_mod_cast hk.le)⟩
    have hu : ((k + 1 : ℕ) : ℝ) / n ∈ Icc (0 : ℝ) 1 :=
      ⟨by positivity, (div_le_one hnr).mpr (by exact_mod_cast hk)⟩
    have hd : |(k : ℝ) / n - ((k + 1 : ℕ) : ℝ) / n| = 1 / n := by
      rw [abs_of_nonpos (sub_nonpos.mpr (div_le_div_of_nonneg_right (by simp) hnr.le))]
      push_cast
      ring
    change dist (x * γ _) (x * γ _) ≤ _
    rw [dist_mul_left]
    simpa only [hd, mul_one_div] using hγ _ ht _ hu
  have hstep (k : ℕ) (hk : k < n) : dist (f (p k)) (f (p (k + 1))) ≤ K * (D / (n : ℝ)) :=
    (hf _ _ ((hp k hk).trans ((div_le_one hnr).mpr hDn))).trans
      (mul_le_mul_of_nonneg_left (hp k hk) K.2)
  calc
    dist (f x) (f y) = dist (f (p 0)) (f (p n)) := by rw [hp0, hpn]
    _ ≤ ∑ k ∈ Finset.range n, K * (D / (n : ℝ)) :=
      dist_le_range_sum_of_dist_le (f := fun k => f (p k)) n (fun {k} hk => hstep k hk)
    _ = K * D := by simp; field_simp
    _ = K * dist x y := by rw [show D = dist x y from dist_one_groupDifference x y]

end PolycyclicRecognition

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_NetSmoothing
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniformly close Lipschitz interpolation of coarse maps -/

noncomputable section
namespace PolycyclicRecognition

open Set Metric
open scoped NNReal BigOperators

variable {X Y : Type*} [Group X] [MetricSpace X] [ProperSpace X]
  [IsIsometricSMul X X] [MetricSpace Y]
  {V : Set X} (hV : V.Pairwise (fun x y => 1 < dist x y)) [LinearOrder V]

omit [Group X] [IsIsometricSMul X X] in
theorem net_union_support_diameter {x y : X} (hxy : dist x y ≤ 1)
    {v w : V}
    (hv : v ∈ (unitNetMass hV x).support ∪ (unitNetMass hV y).support)
    (hw : w ∈ (unitNetMass hV x).support ∪ (unitNetMass hV y).support) :
    dist (v : X) (w : X) ≤ 6 := by
  have hb (u : V) (hu : u ∈ (unitNetMass hV x).support ∪ (unitNetMass hV y).support) :
      dist x (u : X) ≤ 3 := by
    rcases Finset.mem_union.mp hu with hu | hu
    · have h := (mem_support_unitNetMass_iff hV x u).mp hu
      linarith
    · have h := (mem_support_unitNetMass_iff hV y u).mp hu
      have ht := dist_triangle x y (u : X)
      linarith
  have hv' := hb v hv
  have hw' := hb w hw
  have ht := dist_triangle (v : X) x (w : X)
  rw [dist_comm (v : X) x] at ht
  linarith

/-- The same constants work for every map with the prescribed coarse
upper bound. All interpolation data are constructed from the fixed net. -/
theorem exists_uniform_net_smoothing (c : ControlledContraction Y) (p₀ : Y)
    (hcover : ∀ x : X, ∃ v ∈ V, dist x v ≤ 1)
    (hpath : ∀ g : X, ∃ γ : ℝ → X, γ 0 = 1 ∧ γ 1 = g ∧
      ∀ t ∈ Icc (0 : ℝ) 1, ∀ u ∈ Icc (0 : ℝ) 1,
        dist (γ t) (γ u) ≤ dist 1 g * |t - u|)
    {K C : ℝ} (hK : 0 ≤ K) (hC : 0 ≤ C) :
    ∃ L : ℝ≥0, ∃ E : ℝ, 0 ≤ E ∧ ∀ f : X → Y,
      (∀ x y, dist (f x) (f y) ≤ K * dist x y + C) →
      LipschitzWith L (netSmoothedMap hV c p₀ f) ∧
        ∀ x, dist (netSmoothedMap hV c p₀ f x) (f x) ≤ E := by
  obtain ⟨M, hM⟩ := exists_uniform_unit_net_card (G := X) 2
  have hMv := hM V hV
  let D := 6 * K + C
  have hD : 0 ≤ D := by dsimp [D] <;> positivity
  obtain ⟨R, hR, hrad⟩ := exists_interpolation_radius (I := V) c hD (2 * M)
  obtain ⟨Q, hQ, hweight⟩ := exists_interpolation_weight_control (I := V) c hD (2 * M)
  let L : ℝ≥0 := ⟨Q * (4 * (M : ℝ)), mul_nonneg hQ (by positivity)⟩
  refine ⟨L, R, hR, ?_⟩
  intro f hf
  constructor
  · apply lipschitzWith_of_unit_local_bound hpath
    intro x y hxy
    let s := (unitNetMass hV x).support ∪ (unitNetMass hV y).support
    have hs : s.card ≤ 2 * M := by
      have h := (Finset.card_union_le (unitNetMass hV x).support (unitNetMass hV y).support).trans
        (Nat.add_le_add (unitNetMass_support_card_le hV hMv x) (unitNetMass_support_card_le hV hMv y))
      simpa only [two_mul] using h
    have hx : (unitNetMass hV x).support ⊆ s := Finset.subset_union_left
    have hy : (unitNetMass hV y).support ⊆ s := Finset.subset_union_right
    have hpx : (unitNetPartition hV x).support ⊆ s := Finset.Subset.trans Finsupp.support_smul hx
    have hpy : (unitNetPartition hV y).support ⊆ s := Finset.Subset.trans Finsupp.support_smul hy
    have hd : ∀ v ∈ s, ∀ w ∈ s, dist (f (v : X)) (f (w : X)) ≤ D := by
      intro v hv w hw
      exact (hf v w).trans (by dsimp [D]; nlinarith only [net_union_support_diameter hV hxy hv hw, hK])
    have h := finiteSupportCenter_dist_le c hweight p₀ (fun v : V => f v)
      (unitNetPartition hV x) (unitNetPartition hV y) s hpx hpy hs
      (unitNetPartition_nonneg hV x) (unitNetPartition_nonneg hV y)
      (unitNetPartition_total hV hcover x) (unitNetPartition_total hV hcover y) hd
    have hv := unitNetPartition_variation_on_finset hV hcover x y s hx hy
    have hsr : (s.card : ℝ) ≤ 2 * M := by exact_mod_cast hs
    change dist (finiteSupportCenter c p₀ _ _) (finiteSupportCenter c p₀ _ _) ≤ _
    apply h.trans
    have hv' : (∑ v ∈ s, |unitNetPartition hV x v - unitNetPartition hV y v|) ≤
        4 * (M : ℝ) * dist x y := by
      nlinarith only [hv, mul_le_mul_of_nonneg_right hsr (dist_nonneg (x := x) (y := y))]
    exact (mul_le_mul_of_nonneg_left hv' hQ).trans_eq (by change _ = (Q * (4 * (M : ℝ))) * dist x y; ring)
  · intro x
    have hs : (unitNetPartition hV x).support ⊆ (unitNetMass hV x).support := Finsupp.support_smul
    have hcard : (unitNetPartition hV x).support.card ≤ 2 * M :=
      (Finset.card_le_card hs).trans ((unitNetMass_support_card_le hV hMv x).trans (by omega))
    have hd : ∀ v ∈ (unitNetPartition hV x).support,
        ∀ w ∈ (unitNetPartition hV x).support, dist (f (v : X)) (f (w : X)) ≤ D := by
      intro v hv w hw
      have h := net_union_support_diameter hV (x := x) (y := x) (by simp)
        (Finset.mem_union_left _ (hs hv)) (Finset.mem_union_left _ (hs hw))
      exact (hf v w).trans (by dsimp [D]; nlinarith only [h, hK])
    apply finiteSupportCenter_dist_anchor_le c hrad p₀ (fun v : V => f v)
      (unitNetPartition hV x) (unitNetPartition_nonneg hV x)
      (unitNetPartition_total hV hcover x) hcard hd (f x)
    intro v hv
    have h := ((mem_support_unitNetMass_iff hV x v).mp (hs hv)).le
    rw [dist_comm x (v : X)] at h
    exact (hf v x).trans (by dsimp [D]; nlinarith only [h, hK])

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_LipschitzReplacement
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Lipschitz replacement with all net choices internal -/

noncomputable section
namespace PolycyclicRecognition

open Set
open scoped NNReal

/-- Construct a uniformly close Lipschitz representative of every map
with the given coarse upper bound. The net and its order are chosen here. -/
theorem exists_lipschitz_replacement_constants
    {X Y : Type*} [Group X] [MetricSpace X] [ProperSpace X]
    [IsIsometricSMul X X] [MetricSpace Y]
    (c : ControlledContraction Y) (p₀ : Y)
    (hpath : ∀ g : X, ∃ γ : ℝ → X, γ 0 = 1 ∧ γ 1 = g ∧
      ∀ t ∈ Icc (0 : ℝ) 1, ∀ u ∈ Icc (0 : ℝ) 1,
        dist (γ t) (γ u) ≤ dist 1 g * |t - u|)
    {K C : ℝ} (hK : 0 ≤ K) (hC : 0 ≤ C) :
    ∃ L : ℝ≥0, ∃ E : ℝ, 0 ≤ E ∧ ∀ f : X → Y,
      (∀ x y, dist (f x) (f y) ≤ K * dist x y + C) →
      ∃ f' : C(X, Y), LipschitzWith L f' ∧ ∀ x, dist (f' x) (f x) ≤ E := by
  classical
  obtain ⟨V, hV, hcover⟩ := exists_unit_separated_net (X := X)
  let : LinearOrder V := linearOrderOfSTO WellOrderingRel
  obtain ⟨L, E, hE, hsmooth⟩ := exists_uniform_net_smoothing hV c p₀ hcover hpath hK hC
  refine ⟨L, E, hE, ?_⟩
  intro f hf
  obtain ⟨hLip, hclose⟩ := hsmooth f hf
  exact ⟨⟨netSmoothedMap hV c p₀ f, hLip.continuous⟩, hLip, hclose⟩

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_LipschitzPairReplacement
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform Lipschitz replacement of coarse inverse pairs -/

noncomputable section
namespace PolycyclicRecognition

open Set
open scoped NNReal

theorem exists_lipschitz_pair_replacement_constants
    {G : Type*} [Group G] [MetricSpace G] [ProperSpace G] [IsIsometricSMul G G]
    (c : ControlledContraction G)
    (hpath : ∀ g : G, ∃ γ : ℝ → G, γ 0 = 1 ∧ γ 1 = g ∧
      ∀ t ∈ Icc (0 : ℝ) 1, ∀ u ∈ Icc (0 : ℝ) 1,
        dist (γ t) (γ u) ≤ dist 1 g * |t - u|)
    {K C A : ℝ} (hK : 0 ≤ K) (hC : 0 ≤ C) :
    ∃ Λ : ℝ≥0, 2 ≤ (Λ : ℝ) ∧ ∃ E : ℝ, 0 ≤ E ∧
      ∀ f g : G → G,
        (∀ x y, dist (f x) (f y) ≤ K * dist x y + C) →
        (∀ x y, dist (g x) (g y) ≤ K * dist x y + C) →
        (∀ x, dist (g (f x)) x ≤ A) → (∀ x, dist (f (g x)) x ≤ A) →
        ∃ p : C(G, G) × C(G, G), LipschitzPairBounds G Λ p ∧
          (∀ x, dist (p.1 x) (f x) ≤ E) ∧ (∀ x, dist (p.2 x) (g x) ≤ E) := by
  obtain ⟨L, E, hE, hrep⟩ := exists_lipschitz_replacement_constants c (1 : G) hpath hK hC
  let B := E + (K * E + C) + A
  let Λ : ℝ≥0 := ⟨max 2 (max (L : ℝ) B), le_trans (by norm_num) (le_max_left _ _)⟩
  have hΛ : 2 ≤ (Λ : ℝ) := le_max_left _ _
  have hLΛ : L ≤ Λ := (le_max_left (L : ℝ) B).trans (le_max_right _ _)
  have hBΛ : B ≤ (Λ : ℝ) := (le_max_right (L : ℝ) B).trans (le_max_right _ _)
  refine ⟨Λ, hΛ, E, hE, ?_⟩
  intro f g hf hg hgf hfg
  obtain ⟨f', hf', hff'⟩ := hrep f hf
  obtain ⟨g', hg', hgg'⟩ := hrep g hg
  have hgf' : ∀ x, dist (g' (f' x)) x ≤ Λ := fun x =>
    (inverse_error_of_bounded_perturbations f f' g g' hK hg hff' hgg' hgf x).trans hBΛ
  have hfg' : ∀ x, dist (f' (g' x)) x ≤ Λ := fun x =>
    (inverse_error_of_bounded_perturbations g g' f f' hK hf hgg' hff' hfg x).trans hBΛ
  exact ⟨(f', g'), lipschitzPairBounds_of_inverse_bounds hΛ (f', g')
    (hf'.weaken hLΛ) (hg'.weaken hLΛ) hgf' hfg', hff', hgg'⟩

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_RemezFromInterpolation
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial mass estimates from interpolation

Separated interpolation points and finite-measure Fubini give the
scalar sublevel estimate with exponent the dimension times the degree.
-/

noncomputable section
namespace PolycyclicRecognition

theorem remezPolynomialInput : RemezPolynomialInput := by
  intro n D _ hD
  obtain ⟨A, hA, hbound⟩ := coordinate_polynomial_remez n D hD
  refine ⟨A, hA, ?_⟩
  intro p hp R hR S hS hSR hm η hη hv x hx
  exact hbound (fun y => MvPolynomial.eval y p) (coordinatePolynomial_eval p hp)
    R hR S hS hSR hm η hη hv x hx

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_SelfQuasiIsometry
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform coarse inverse bounds for self quasi-isometries -/

noncomputable section
namespace PolycyclicRecognition

variable (G : Type*) [PseudoMetricSpace G] (K C : ℝ)

variable {G K C}

theorem SelfQuasiIsometry.inverse_close (f : SelfQuasiIsometry G K C) (y : G) :
    dist y (f.toFun (f.inverse y)) ≤ C :=
  Classical.choose_spec (f.surjective y)

theorem SelfQuasiIsometry.left_inverse_close (f : SelfQuasiIsometry G K C)
    (hK : 0 ≤ K) (x : G) : dist (f.inverse (f.toFun x)) x ≤ 2 * K * C := by
  have h := f.lower x (f.inverse (f.toFun x))
  have hc := mul_le_mul_of_nonneg_left (f.inverse_close (f.toFun x)) hK
  rw [dist_comm] at h
  linarith

theorem SelfQuasiIsometry.inverse_upper (f : SelfQuasiIsometry G K C)
    (hK : 0 ≤ K) (x y : G) :
    dist (f.inverse x) (f.inverse y) ≤ K * dist x y + 3 * K * C := by
  have hd : dist (f.toFun (f.inverse x)) (f.toFun (f.inverse y)) ≤ dist x y + 2 * C := by
    have := dist_triangle4 (f.toFun (f.inverse x)) x y (f.toFun (f.inverse y))
    have hx := f.inverse_close x
    have hy := f.inverse_close y
    rw [dist_comm x] at hx
    linarith
  have := f.lower (f.inverse x) (f.inverse y)
  have := mul_le_mul_of_nonneg_left hd hK
  linarith

end PolycyclicRecognition

end

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

set_option maxHeartbeats 1000000 in
/-- Retain the actual abelianization basis along with its homogeneous lifts.
This gives positivity for every later choice of a word basis. -/
theorem exists_cartan_abelianization_generators [FiniteDimensional ℝ L]
    {n : ℕ} (T : TriangularAdjoint L n) :
    ∃ (m : ℕ) (X : Fin m → cartanRootIdeal H) (χ : Fin m → Weight ℝ H L)
      (b : Basis (Fin m) ℝ (cartanRootAbelianization H)),
      (∀ i, (χ i).IsNonZero ∧ (X i : L) ∈ rootSpace H (χ i)) ∧
      (∀ i, (LieModule.lowerCentralSeries ℝ (cartanRootIdeal H)
        (cartanRootIdeal H) 1).toSubmodule.mkQ (X i) = b i) ∧
      LieSubalgebra.lieSpan ℝ (cartanRootIdeal H) (Set.range X) = ⊤ := by
  let := cartanRootIdeal_nilpotent H T
  let C := (LieModule.lowerCentralSeries ℝ (cartanRootIdeal H)
    (cartanRootIdeal H) 1).toSubmodule
  obtain ⟨b, X, hXS, hXq, hspan⟩ := exists_quotient_basis_lifts C (cartanGeneratorPool H)
    (span_sup_lowerCentralSeries_one_of_lieSpan _ (cartanGeneratorPool_lieSpan H T))
  choose χ hχ using hXS
  refine ⟨Module.finrank ℝ (cartanRootAbelianization H), X, χ, b, hχ, hXq, ?_⟩
  apply lieSubalgebra_eq_top_of_sup_lowerCentralSeries_one
  apply top_unique
  rw [← hspan]
  apply sup_le_sup_right
  exact Submodule.span_le.mpr LieSubalgebra.subset_lieSpan

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanWordModel
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instDecidableEqConeMixedWords _root_.OAI.PolycyclicRecognition.CartanWordModel.instFintypeConeMixedWords _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
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

set_option maxHeartbeats 1000000 in
/-- Construction uses the triangular adjoint action and the actual Cartan
root ideal; no word-generation or nilpotence premise is left to the caller. -/
theorem nonempty_cartanWordModel {n : ℕ} (T : TriangularAdjoint L n) :
    Nonempty (CartanWordModel H) := by
  obtain ⟨m, X, χ, bq, hroot, hq, hgen⟩ := exists_cartan_abelianization_generators H T
  let := cartanRootIdeal_nilpotent H T
  obtain ⟨k, hk⟩ := LieModule.IsNilpotent.nilpotent ℝ (cartanRootIdeal H) (cartanRootIdeal H)
  exact ⟨⟨m, X, χ, fun i => (hroot i).1, fun i => (hroot i).2, bq, hq, hgen, k, hk⟩⟩

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_ExponentialBasisSection
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A global section for a linear exponential quotient

A product of lifted basis one-parameter subgroups is a continuous global
section. Only the individual exponential curves are used; the exponential
map need not be globally invertible or even be supplied as a continuous map.
-/

noncomputable section
namespace PolycyclicRecognition

open scoped Manifold ContDiff BigOperators

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace G] [ChartedSpace E G] [Group G]
  [LieGroup (𝓘(ℝ, E)) ⊤ G]
  {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]

omit [LieGroup (𝓘(ℝ, E)) ⊤ G] in
theorem exponentialProduct_linear_quotient
    {Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G}
    (d : E →ₗ[ℝ] W) (π : G →* Multiplicative W)
    (hπ : ∀ x, (π (Exp x)).toAdd = d x)
    {n : ℕ} (v : Fin n → E) (t : Fin n → ℝ) :
    (π (exponentialProduct Exp v t)).toAdd = ∑ i, t i • d (v i) := by
  induction n with
  | zero => simp [exponentialProduct]
  | succ n ih =>
    change (π (Exp (t 0 • v 0) *
      exponentialProduct Exp (v ∘ Fin.succ) (t ∘ Fin.succ))).toAdd = _
    rw [map_mul, toAdd_mul]
    have hhead : (π (Exp (t 0 • v 0))).toAdd = t 0 • d (v 0) :=
      (hπ _).trans (d.map_smul _ _)
    exact (congrArg₂ (· + ·) hhead (ih (v ∘ Fin.succ) (t ∘ Fin.succ))).trans
      (Fin.sum_univ_succ (fun i => t i • d (v i))).symm

theorem exists_smooth_section_of_exponential_linear_quotient
    [FiniteDimensional ℝ W]
    {Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G} (hExp : IsGroupExponential Exp)
    (d : E →ₗ[ℝ] W) (hd : Function.Surjective d)
    (π : G →* Multiplicative W) (hπ : ∀ x, (π (Exp x)).toAdd = d x) :
    ∃ (s : W → G) (l : W →L[ℝ] E),
      ContMDiff (𝓘(ℝ, W)) (𝓘(ℝ, E)) ∞ s ∧ s 0 = 1 ∧
      (∀ w, (π (s w)).toAdd = w) ∧
      HasMFDerivAt (𝓘(ℝ, W)) (𝓘(ℝ, E)) s 0 l ∧
      d.comp l.toLinearMap = LinearMap.id := by
  let b := Module.finBasis ℝ W
  choose v hv using fun i => hd (b i)
  let c : W →L[ℝ] (Fin (Module.finrank ℝ W) → ℝ) :=
    b.equivFun.toLinearMap.toContinuousLinearMap
  let s : W → G := fun w => exponentialProduct Exp v (c w)
  let l : W →L[ℝ] E := (tangentCombination v).comp c
  refine ⟨s, l, ?_, ?_, ?_, ?_, ?_⟩
  · exact (hExp.contMDiff_exponentialProduct v).comp c.contDiff.contMDiff
  · change exponentialProduct Exp v (c 0) = 1
    rw [map_zero]
    exact hExp.exponentialProduct_zero v
  · intro w
    rw [show s w = exponentialProduct Exp v (c w) from rfl,
      exponentialProduct_linear_quotient d π hπ]
    simp only [hv]
    exact b.sum_repr w
  · have hc : HasMFDerivAt (𝓘(ℝ, W)) (𝓘(ℝ, Fin (Module.finrank ℝ W) → ℝ))
        c 0 c := c.hasFDerivAt.hasMFDerivAt
    have hp := hExp.hasMFDerivAt_exponentialProduct_zero v
    have hzero : c 0 = 0 := map_zero c
    rw [← hzero] at hp
    exact hp.comp 0 hc
  · ext w
    change d ((tangentCombination v) (c w)) = w
    rw [tangentCombination_apply, map_sum]
    simp only [map_smul, hv]
    exact b.sum_repr w

theorem exists_continuous_section_of_exponential_linear_quotient
    [FiniteDimensional ℝ W]
    {Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G} (hExp : IsGroupExponential Exp)
    (d : E →ₗ[ℝ] W) (hd : Function.Surjective d)
    (π : G →* Multiplicative W) (hπ : ∀ x, (π (Exp x)).toAdd = d x) :
    ∃ s : W → G, Continuous s ∧ s 0 = 1 ∧ ∀ w, (π (s w)).toAdd = w := by
  obtain ⟨s, _, hs, hs0, hsπ, _⟩ :=
    exists_smooth_section_of_exponential_linear_quotient hExp d hd π hπ
  exact ⟨s, hs.continuous, hs0, hsπ⟩

theorem isQuotientMap_of_exponential_linear_quotient
    [FiniteDimensional ℝ W]
    {Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G} (hExp : IsGroupExponential Exp)
    (d : E →ₗ[ℝ] W) (hd : Function.Surjective d)
    (π : G →* Multiplicative W) (hπ : ∀ x, (π (Exp x)).toAdd = d x)
    (hc : Continuous (fun g => (π g).toAdd)) :
    Topology.IsQuotientMap (fun g => (π g).toAdd) := by
  obtain ⟨s, hs, _, hright⟩ :=
    exists_continuous_section_of_exponential_linear_quotient hExp d hd π hπ
  exact Topology.IsQuotientMap.of_inverse hs hc hright

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_HeightLipschitz
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Removing the additive error from a vector-valued homomorphism

A homomorphism to a real normed vector group scales exactly on powers.
Distances in a left-invariant source metric grow at most linearly on powers.
Consequently an affine upper bound for the homomorphism is already a genuine
Lipschitz bound. Compactness and the existing linear-chain argument supply
the affine bound for continuous homomorphisms.
-/

namespace PolycyclicRecognition

variable {G W : Type*} [Group G] [MetricSpace G] [IsIsometricSMul G G]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- The additive constant disappears by applying the bound to arbitrarily
large powers. No commutativity of the source is required. -/
theorem height_lipschitz_of_affine_bound (π : G →* Multiplicative W)
    {K C : ℝ} (hK : 0 ≤ K)
    (hbound : ∀ g, ‖(π g).toAdd‖ ≤ K * dist (1 : G) g + C) :
    ∀ x y, ‖(π x).toAdd - (π y).toAdd‖ ≤ K * dist x y := by
  have hone (g : G) : ‖(π g).toAdd‖ ≤ K * dist (1 : G) g := by
    by_contra h
    have hpos : 0 < ‖(π g).toAdd‖ - K * dist (1 : G) g :=
      sub_pos.mpr (lt_of_not_ge h)
    obtain ⟨n, hn⟩ := exists_nat_gt (C / (‖(π g).toAdd‖ - K * dist (1 : G) g))
    have hlarge : C < (n : ℝ) * (‖(π g).toAdd‖ - K * dist (1 : G) g) :=
      (div_lt_iff₀ hpos).mp hn
    have hp : ‖(π (g ^ n)).toAdd‖ = (n : ℝ) * ‖(π g).toAdd‖ := by
      rw [map_pow, toAdd_pow, ← Nat.cast_smul_eq_nsmul ℝ, norm_smul]
      simp
    have hb := hbound (g ^ n)
    have hd := mul_le_mul_of_nonneg_left (dist_one_pow_le g n) hK
    rw [hp] at hb
    nlinarith
  intro x y
  have h := hone (x⁻¹ * y)
  rw [map_mul, map_inv, toAdd_mul, toAdd_inv, dist_one_groupDifference] at h
  simpa only [← sub_eq_add_neg, add_comm (-(π x).toAdd), norm_sub_rev] using h

/-- A continuous vector-valued homomorphism from a proper group with linear
metric chains is globally Lipschitz. -/
theorem continuous_height_lipschitz [ProperSpace G] (C : LinearMetricChains G)
    (π : G →* Multiplicative W) (hπ : Continuous (fun g => (π g).toAdd)) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ x y, ‖(π x).toAdd - (π y).toAdd‖ ≤ K * dist x y := by
  obtain ⟨K, B, hK, _, hbound⟩ := continuousHom_coarseLipschitz C π hπ
  refine ⟨K, hK, height_lipschitz_of_affine_bound π (C := B) hK (fun g => ?_)⟩
  have h := hbound 1 g
  rw [map_one] at h
  change dist (0 : W) (π g).toAdd ≤ K * dist (1 : G) g + B at h
  simpa only [dist_zero_left] using h

end PolycyclicRecognition

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_IntrinsicAdjointHeight
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Intrinsic adjoint height on a connected triangular Lie group

The actual adjoint action is positive upper triangular because this holds
on exponential basis curves, which generate the connected group. Its
logarithmic diagonal is therefore a continuous character without a global
exponential chart or a faithful group representation.
-/

noncomputable section
namespace PolycyclicRecognition

open scoped Manifold Matrix.Norms.Operator

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace G] [ChartedSpace E G]
  [Group G] [LieGroup (𝓘(ℝ, E)) ⊤ G]

theorem continuous_adjointMatrixHom {n : ℕ}
    (b : Module.Basis (Fin n) ℝ (GroupLieAlgebra (𝓘(ℝ, E)) G)) :
    Continuous (adjointMatrixHom b : G → Matrix (Fin n) (Fin n) ℝ) := by
  let fL : (E →L[ℝ] E) →ₗ[ℝ] Matrix (Fin n) (Fin n) ℝ :=
    (LinearMap.toMatrix b b).toLinearMap.comp (ContinuousLinearMap.coeLM ℝ)
  change Continuous (fun g => fL (conjugationDifferentialHom (E := E) g))
  exact fL.continuous_of_finiteDimensional.comp contMDiff_conjugationDifferentialHom.continuous

variable [IsTopologicalGroup G] [PreconnectedSpace G]

theorem intrinsicAdjointCharacterHom_exp {n : ℕ}
    (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, E)) G) n)
    {Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G} (hExp : IsGroupExponential Exp)
    (x : GroupLieAlgebra (𝓘(ℝ, E)) G) (i : Fin n) :
    (intrinsicAdjointCharacterHom T hExp (Exp x)).toAdd i = T.character i x := by
  change Real.log (adjointMatrixHom T.basis (Exp x) i i) = _
  rw [adjointMatrixHom_exp_intrinsic T.basis hExp,
    matrix_exp_diagonal _ (T.upper x), Real.log_exp, T.character_eq_diag]

theorem continuous_intrinsicAdjointCharacterHom {n : ℕ}
    (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, E)) G) n)
    {Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G} (hExp : IsGroupExponential Exp) :
    Continuous (fun g => (intrinsicAdjointCharacterHom T hExp g).toAdd) := by
  apply continuous_pi
  intro i
  change Continuous (fun g => Real.log (adjointMatrixHom T.basis g i i))
  exact ((continuous_apply i).comp
    ((continuous_apply i).comp (continuous_adjointMatrixHom T.basis))).log
    (fun g => ((adjointMatrixHom_positive_triangular T hExp g).2 i).ne')

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_IntrinsicCanonicalHeight
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.CartanFactorModel.heightRay_zero _root_.OAI.PolycyclicRecognition.CartanWordModel.supportDatum_weight _root_.OAI.PolycyclicRecognition.cartanHeightSection_height _root_.OAI.PolycyclicRecognition.cartanHeightWeight_projection _root_.OAI.PolycyclicRecognition.cartanWeightDerivation_apply_root _root_.OAI.PolycyclicRecognition.cartanWeightDilation_apply _root_.OAI.PolycyclicRecognition.cartanWeightScale_add_apply _root_.OAI.PolycyclicRecognition.cartanWeightScale_zero_apply _root_.OAI.PolycyclicRecognition.derivationSemidirectHom_apply _root_.OAI.PolycyclicRecognition.exponentialHomOfDynkin_apply_exp _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.integrateNilpotentLieEquiv_apply_exp _root_.OAI.PolycyclicRecognition.nilshadowWeightDerivation_symm _root_.OAI.PolycyclicRecognition.nilshadowWeightOperator_symm _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Canonical height without a global exponential chart

The logarithmic adjoint diagonal is projected back to the canonical linear
quotient using a linear left inverse. Exponential basis products give a
continuous section and prove the quotient-map property.
-/

noncomputable section
namespace PolycyclicRecognition

open scoped Manifold

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace G] [ChartedSpace E G]
  [Group G] [LieGroup (𝓘(ℝ, E)) ⊤ G]
  [IsTopologicalGroup G] [PreconnectedSpace G]
  {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]

theorem exists_intrinsic_canonical_height_with_kernel {a : ℕ}
    (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, E)) G) a)
    (q : HeightSpace T.character ≃ₗ[ℝ] W)
    {Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G} (hExp : IsGroupExponential Exp) :
    ∃ π : G →* Multiplicative W,
      Continuous (fun g => (π g).toAdd) ∧
      (∀ x, (π (Exp x)).toAdd = q (heightProjection T.character x)) ∧
      Function.Surjective π ∧ Topology.IsQuotientMap (fun g => (π g).toAdd) ∧
      (∃ s : W → G, Continuous s ∧ s 0 = 1 ∧ ∀ w, (π (s w)).toAdd = w) ∧
      (∀ g, adjointMatrixHom T.basis g = 1 → π g = 1) ∧
      ∃ P : (Fin a → ℝ) →L[ℝ] W, ∀ g,
        (π g).toAdd = P (fun i => Real.log (adjointMatrixHom T.basis g i i)) := by
  let d : E →ₗ[ℝ] W := q.toLinearMap.comp (heightProjection T.character)
  have hd : Function.Surjective d :=
    q.surjective.comp (heightProjection_surjective T.character)
  let : FiniteDimensional ℝ W := Module.Finite.of_surjective d hd
  let k : W →ₗ[ℝ] (Fin a → ℝ) :=
    LinearMap.pi fun i => (heightCharacter T.character i).comp q.symm.toLinearMap
  have hk : Function.Injective k := by
    intro u v huv
    apply q.symm.injective
    apply sub_eq_zero.mp
    apply heightCharacters_separate T.character
    intro i
    change heightCharacter T.character i (q.symm u - q.symm v) = 0
    rw [map_sub]
    exact sub_eq_zero.mpr (congrFun huv i)
  obtain ⟨p, hp⟩ := k.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr hk)
  have hpk (w : W) : p (k w) = w := LinearMap.congr_fun hp w
  let c := intrinsicAdjointCharacterHom T hExp
  let π : G →* Multiplicative W :=
    { toFun g := Multiplicative.ofAdd (p (c g).toAdd)
      map_one' := by
        apply Multiplicative.ext
        change p (c 1).toAdd = 0
        rw [map_one]
        exact map_zero p
      map_mul' g h := by
        apply Multiplicative.ext
        change p (c (g * h)).toAdd = p (c g).toAdd + p (c h).toAdd
        rw [map_mul, toAdd_mul, map_add] }
  have hc : Continuous (fun g => (π g).toAdd) :=
    p.continuous_of_finiteDimensional.comp (continuous_intrinsicAdjointCharacterHom T hExp)
  have hπ (x : E) : (π (Exp x)).toAdd = d x := by
    change p (c (Exp x)).toAdd = d x
    have hcx : (c (Exp x)).toAdd = k (d x) := by
      funext i
      apply (intrinsicAdjointCharacterHom_exp T hExp x i).trans
      change T.character i x = heightCharacter T.character i
        (q.symm (q (heightProjection T.character x)))
      rw [q.symm_apply_apply]
      exact (heightCharacter_projection T.character i x).symm
    rw [hcx, hpk]
  refine ⟨π, hc, hπ, integrated_height_surjective T q Exp π hπ,
    isQuotientMap_of_exponential_linear_quotient hExp d hd π hπ hc, ?_, ?_, ?_⟩
  · exact exists_continuous_section_of_exponential_linear_quotient hExp d hd π hπ
  · intro g hg
    apply Multiplicative.ext
    change p (c g).toAdd = 0
    have hcg : (c g).toAdd = 0 := by
      funext i
      change Real.log (adjointMatrixHom T.basis g i i) = 0
      rw [hg]
      simp
    rw [hcg, map_zero]
  · exact ⟨p.toContinuousLinearMap, fun _ => rfl⟩

/-- The canonical height and its section, without exposing the optional
adjoint-kernel property used in the representation construction. -/
theorem exists_intrinsic_canonical_height {a : ℕ}
    (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, E)) G) a)
    (q : HeightSpace T.character ≃ₗ[ℝ] W)
    {Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G} (hExp : IsGroupExponential Exp) :
    ∃ π : G →* Multiplicative W,
      Continuous (fun g => (π g).toAdd) ∧
      (∀ x, (π (Exp x)).toAdd = q (heightProjection T.character x)) ∧
      Function.Surjective π ∧ Topology.IsQuotientMap (fun g => (π g).toAdd) ∧
      ∃ s : W → G, Continuous s ∧ s 0 = 1 ∧ ∀ w, (π (s w)).toAdd = w := by
  obtain ⟨π, hc, he, hs, hq, hsection, _, _⟩ :=
    exists_intrinsic_canonical_height_with_kernel T q hExp
  exact ⟨π, hc, he, hs, hq, hsection⟩

section Metric

variable {EM GM WM : Type*} [NormedAddCommGroup EM] [NormedSpace ℝ EM]
  [FiniteDimensional ℝ EM] [MetricSpace GM] [ChartedSpace EM GM]
  [Group GM] [LieGroup (𝓘(ℝ, EM)) ⊤ GM] [IsTopologicalGroup GM]
  [PreconnectedSpace GM] [IsIsometricSMul GM GM] [ProperSpace GM]
  [NormedAddCommGroup WM] [NormedSpace ℝ WM]

/-- Metric compatibility of intrinsic height requires neither Dixmier nor
an independent triangular representation premise. -/
theorem exists_lipschitz_intrinsic_canonical_height {a : ℕ}
    (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EM)) GM) a)
    (q : HeightSpace T.character ≃ₗ[ℝ] WM) (chains : LinearMetricChains GM)
    {Exp : GroupLieAlgebra (𝓘(ℝ, EM)) GM → GM} (hExp : IsGroupExponential Exp) :
    ∃ π : GM →* Multiplicative WM,
      (∀ x, (π (Exp x)).toAdd = q (heightProjection T.character x)) ∧
      Function.Surjective π ∧ Topology.IsQuotientMap (fun g => (π g).toAdd) ∧
      ∃ K : ℝ, 0 ≤ K ∧ ∀ x y, ‖(π x).toAdd - (π y).toAdd‖ ≤ K * dist x y := by
  obtain ⟨π, hc, he, hs, hq, _⟩ := exists_intrinsic_canonical_height T q hExp
  exact ⟨π, he, hs, hq, continuous_height_lipschitz chains π hc⟩

end Metric
end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_ExponentialHomExt
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.chartExponentialFlow_zero _root_.OAI.PolycyclicRecognition.derivationSemidirectHom_apply _root_.OAI.PolycyclicRecognition.exponentialHomOfDynkin_apply_exp _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.integrateNilpotentLieEquiv_apply_exp _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Homomorphisms are determined by exponential curves -/

noncomputable section
namespace PolycyclicRecognition

open scoped Manifold

variable {E G H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace G] [ChartedSpace E G]
  [Group G] [LieGroup (𝓘(ℝ, E)) ⊤ G] [IsTopologicalGroup G]
  [PreconnectedSpace G] [Group H]

theorem monoidHom_ext_exponential
    {Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G} (hExp : IsGroupExponential Exp)
    (f g : G →* H) (h : ∀ x, f (Exp x) = g (Exp x)) : f = g := by
  let S : Subgroup G :=
    { carrier := {x | f x = g x}
      one_mem' := by simp
      mul_mem' := by
        intro x y hx hy
        change f x = g x at hx
        change f y = g y at hy
        change f (x * y) = g (x * y)
        rw [map_mul, map_mul, hx, hy]
      inv_mem' := by
        intro x hx
        change f x = g x at hx
        change f x⁻¹ = g x⁻¹
        rw [map_inv, map_inv, hx] }
  have hS : S = ⊤ := by
    apply subgroup_eq_top_of_exponential_basis hExp (Module.finBasis ℝ E)
    intro i t
    exact h _
  ext x
  have hx : x ∈ S := by rw [hS]; trivial
  exact hx

theorem height_eq_of_exponential_linear
    {W W' : Type*} [AddCommGroup W] [Module ℝ W] [AddCommGroup W'] [Module ℝ W']
    {Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G} (hExp : IsGroupExponential Exp)
    (π : G →* Multiplicative W) (ψ : G →* Multiplicative W') (e : W' →ₗ[ℝ] W)
    (he : ∀ x, (π (Exp x)).toAdd = e (ψ (Exp x)).toAdd) :
    ∀ g, (π g).toAdd = e (ψ g).toAdd := by
  let τ : G →* Multiplicative W :=
    { toFun := fun g => Multiplicative.ofAdd (e (ψ g).toAdd)
      map_one' := by simp
      map_mul' := by intro g h; simp only [map_mul, toAdd_mul, map_add]; rfl }
  have h : π = τ := monoidHom_ext_exponential hExp π τ
    (fun x => Multiplicative.ext (he x))
  intro g
  exact congrArg (fun f : G →* Multiplicative W => (f g).toAdd) h

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_NormalizedPairHeightTransfer
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteRootOffsetConeIndex _root_.OAI.PolycyclicRecognition.instNonemptyRootOffsetConeIndex _root_.OAI.PolycyclicRecognition.inversePairCoupling_finiteOnCompacts _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.normalizedPair_polishSpace _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Passing bounded height from normalized representatives to coarse maps -/

noncomputable section
namespace PolycyclicRecognition

open scoped NNReal

variable {G W P I B₀ : Type*} [Group G] [MetricSpace G] [ProperSpace G]
  [IsTopologicalGroup G] [IsIsometricSMul G G]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  [Fintype I] [Fintype B₀] [Nonempty B₀]

omit [ProperSpace G] in
/-- Bounded perturbations of both evaluation points cost at most twice
the height-Lipschitz constant times the perturbation radius. No continuity
of the original coarse maps is used. -/
theorem uniform_affine_height_of_bounded_pair_representatives
    (D : SupportDatum W I B₀) (π : G →* Multiplicative W)
    {L : ℝ} (hL : 0 ≤ L)
    (hπ : ∀ x y, ‖(π x).toAdd - (π y).toAdd‖ ≤ L * dist x y)
    {Λ : ℝ≥0} (label : NormalizedPair G Λ → templateSymmetryGroup D)
    {K : ℝ} (hK : 0 ≤ K)
    (hbound : ∀ p x, ‖(π (p.val.1 x)).toAdd - (label p).val (π x).toAdd‖ ≤ K)
    (f : P → G → G) (rep : P → C(G, G) × C(G, G))
    (hrep : ∀ p, LipschitzPairBounds G Λ (rep p))
    {E : ℝ} (hE : 0 ≤ E) (hclose : ∀ p x, dist ((rep p).1 x) (f p x) ≤ E) :
    ∃ (A : P → templateSymmetryGroup D) (B : ℝ), 0 ≤ B ∧ ∀ p x,
      ‖(π (f p x)).toAdd - ((π (f p 1)).toAdd + (A p).val (π x).toAdd)‖ ≤ B := by
  let q := fun p => normalizePair (rep p) (hrep p)
  let A := fun p => label (q p)
  have hb (p : P) (x : G) :
      ‖(π ((rep p).1 x)).toAdd - (π ((rep p).1 1)).toAdd -
        (A p).val (π x).toAdd‖ ≤ K := by
    have h := hbound (q p) x
    change ‖(π (((rep p).1 1)⁻¹ * (rep p).1 (1 * x))).toAdd -
      (A p).val (π x).toAdd‖ ≤ K at h
    simpa only [one_mul, map_mul, map_inv, toAdd_mul, toAdd_inv, neg_add_eq_sub] using h
  refine ⟨A, K + 2 * L * E, by positivity, ?_⟩
  intro p x
  have hx : ‖(π (f p x)).toAdd - (π ((rep p).1 x)).toAdd‖ ≤ L * E := by
    exact (hπ _ _).trans (mul_le_mul_of_nonneg_left
      (by simpa only [dist_comm] using hclose p x) hL)
  have h1 : ‖(π ((rep p).1 1)).toAdd - (π (f p 1)).toAdd‖ ≤ L * E :=
    (hπ _ _).trans (mul_le_mul_of_nonneg_left (hclose p 1) hL)
  calc
    _ = ‖((π (f p x)).toAdd - (π ((rep p).1 x)).toAdd) +
        ((π ((rep p).1 x)).toAdd - (π ((rep p).1 1)).toAdd - (A p).val (π x).toAdd) +
        ((π ((rep p).1 1)).toAdd - (π (f p 1)).toAdd)‖ := by congr 1; abel
    _ ≤ (‖(π (f p x)).toAdd - (π ((rep p).1 x)).toAdd‖ +
        ‖(π ((rep p).1 x)).toAdd - (π ((rep p).1 1)).toAdd - (A p).val (π x).toAdd‖) +
        ‖(π ((rep p).1 1)).toAdd - (π (f p 1)).toAdd‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ (L * E + K) + L * E := add_le_add (add_le_add hx (hb p x)) h1
    _ = K + 2 * L * E := by ring

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CoarsePairHeight
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteRootOffsetConeIndex _root_.OAI.PolycyclicRecognition.instNonemptyRootOffsetConeIndex _root_.OAI.PolycyclicRecognition.inversePairCoupling_finiteOnCompacts _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.normalizedPair_polishSpace _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Bounded height for uniform families of coarse inverse pairs

Representative existence is proved here from the controlled contraction.
The normalized height premise is discharged by the Cartan theorem in the
application; it is not declared as a published result.
-/

noncomputable section
namespace PolycyclicRecognition

open Set
open scoped NNReal

variable {G W P I B₀ : Type*} [Group G] [MetricSpace G] [ProperSpace G]
  [IsTopologicalGroup G] [IsIsometricSMul G G]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  [Fintype I] [Fintype B₀] [Nonempty B₀]

theorem uniform_affine_height_of_coarse_inverse_pairs
    (c : ControlledContraction G)
    (hpath : ∀ g : G, ∃ γ : ℝ → G, γ 0 = 1 ∧ γ 1 = g ∧
      ∀ t ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1,
        dist (γ t) (γ s) ≤ dist 1 g * |t - s|)
    (D : SupportDatum W I B₀) (π : G →* Multiplicative W)
    {L : ℝ} (hL : 0 ≤ L)
    (hπ : ∀ x y, ‖(π x).toAdd - (π y).toAdd‖ ≤ L * dist x y)
    (hheight : ∀ Λ : ℝ≥0, 2 ≤ (Λ : ℝ) →
      ∃ label : NormalizedPair G Λ → templateSymmetryGroup D,
        ∃ B : ℝ, 0 ≤ B ∧
          ∀ p x, ‖(π (p.val.1 x)).toAdd - (label p).val (π x).toAdd‖ ≤ B)
    {K C A : ℝ} (hK : 0 ≤ K) (hC : 0 ≤ C) (f g : P → G → G)
    (hf : ∀ p x y, dist (f p x) (f p y) ≤ K * dist x y + C)
    (hg : ∀ p x y, dist (g p x) (g p y) ≤ K * dist x y + C)
    (hgf : ∀ p x, dist (g p (f p x)) x ≤ A)
    (hfg : ∀ p x, dist (f p (g p x)) x ≤ A) :
    ∃ (label : P → templateSymmetryGroup D) (B : ℝ), 0 ≤ B ∧ ∀ p x,
      ‖(π (f p x)).toAdd - ((π (f p 1)).toAdd + (label p).val (π x).toAdd)‖ ≤ B := by
  obtain ⟨Λ, hΛ, E, hE, hreplace⟩ := exists_lipschitz_pair_replacement_constants c hpath hK hC
  have hex (p : P) : ∃ q : C(G, G) × C(G, G), LipschitzPairBounds G Λ q ∧
      (∀ x, dist (q.1 x) (f p x) ≤ E) ∧ (∀ x, dist (q.2 x) (g p x) ≤ E) :=
    hreplace (f p) (g p) (hf p) (hg p) (hgf p) (hfg p)
  choose rep hrep hclose _ using hex
  obtain ⟨label, B, hB, hbound⟩ := hheight Λ hΛ
  exact uniform_affine_height_of_bounded_pair_representatives D π hL hπ
    label hB hbound f rep hrep hE hclose

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_HeightChangeOfCoordinates
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite height groups and bounds under a change of normed coordinates -/

noncomputable section
namespace PolycyclicRecognition

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ V]
  [FiniteDimensional ℝ W]

omit [FiniteDimensional ℝ V] [FiniteDimensional ℝ W] in
theorem finite_heightConjugation (e : V ≃ₗ[ℝ] W) (D : Subgroup (V ≃ₗ[ℝ] V))
    [Finite D] : Set.Finite (D.map (heightConjugation e) : Set (W ≃ₗ[ℝ] W)) := by
  apply (Set.finite_range (fun A : D => heightConjugation e A.val)).subset
  rintro A ⟨B, hB, rfl⟩
  exact ⟨⟨B, hB⟩, rfl⟩

omit [FiniteDimensional ℝ W] in
theorem norm_height_difference_le (e : V ≃ₗ[ℝ] W)
    (x y z : V) (A : V ≃ₗ[ℝ] V) {B : ℝ}
    (h : ‖x - (y + A z)‖ ≤ B) :
    ‖e x - (e y + heightConjugation e A (e z))‖ ≤
      ‖e.toContinuousLinearEquiv.toContinuousLinearMap‖ * B := by
  have heq : e x - (e y + heightConjugation e A (e z)) = e (x - (y + A z)) := by
    simp [heightConjugation]
  rw [heq]
  exact (e.toContinuousLinearEquiv.toContinuousLinearMap.le_opNorm _).trans
    (mul_le_mul_of_nonneg_left h (norm_nonneg _))

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_ConditionalBoundedHeight
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_countable _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_nonempty _root_.OAI.PolycyclicRecognition.finitelyGeneratedSubgroupIndex_countable _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform bounded height in a fixed metric and an arbitrary norm

The auxiliary Riemannian metric is used only to construct smoothing. The
identity comparison transfers every uniformly controlled family from the
specified proper chain metric. A bounded linear change of coordinates then
returns the estimate to the specified norm on the canonical height space.
-/

noncomputable section
namespace PolycyclicRecognition

open Module LieAlgebra MeasureTheory
open scoped Manifold NNReal

attribute [local instance] stationaryL2Action zeroMeanL2Action

/-- The standalone uniform bounded-height theorem. In particular the
fixed metric can be any left-invariant proper Riemannian metric. The finite
group is chosen before the quasi-isometry constants, and the bound is
uniform over all self quasi-isometries with those constants. -/
theorem uniform_bounded_height
    (R : SimplyConnectedSolvableLieModel) (d : ProperChainMetric R.carrier)
    {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, R.modelSpace)) R.carrier) a)
    (huni : ModelIsUnimodular R)
    {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
    (q : HeightSpace T.character ≃ₗ[ℝ] W)
    (Exp : GroupLieAlgebra (𝓘(ℝ, R.modelSpace)) R.carrier → R.carrier)
    (hExp : IsGroupExponential Exp) (π : R.carrier →* Multiplicative W)
    (hπExp : ∀ x, (π (Exp x)).toAdd = q (heightProjection T.character x)) :
    letI := d.compatibleMetric
    ∃ A : Subgroup (W ≃ₗ[ℝ] W), Set.Finite (A : Set (W ≃ₗ[ℝ] W)) ∧
      ∀ K C : ℝ, 1 ≤ K → 0 ≤ C → ∃ B : ℝ, 0 ≤ B ∧
        ∀ F : SelfQuasiIsometry R.carrier K C, ∃ AF : A, ∀ g,
          ‖(π (F.toFun g)).toAdd - ((π (F.toFun 1)).toAdd + AF.val (π g).toAdd)‖ ≤ B := by
  classical
  let : IsTopologicalGroup R.carrier :=
    topologicalGroup_of_lieGroup (𝓘(ℝ, R.modelSpace)) ⊤
  let : LocallyCompactSpace R.carrier :=
    Manifold.locallyCompact_of_finiteDimensional (𝓘(ℝ, R.modelSpace))
  let : MeasurableSpace R.carrier := borel _
  let : BorelSpace R.carrier := ⟨rfl⟩
  let m : Measure R.carrier := Measure.haar
  let : m.IsMulRightInvariant := huni
  obtain ⟨d₀, hcompat⟩ := lieRiemannianMetricInput R
  let := d₀.toProperChainMetric.compatibleMetric
  let := d₀.toProperChainMetric.proper_compatibleMetric
  let := d₀.toProperChainMetric.isometric_compatibleMetric
  let V := EuclideanSpace ℝ (Fin (finrank ℝ (HeightSpace T.character)))
  let q₀ : HeightSpace T.character ≃ₗ[ℝ] V :=
    LinearEquiv.ofFinrankEq _ _ (by simp [V])
  obtain ⟨π₀, hπ₀Exp, _, _, L, hL, hπ₀Lip⟩ :=
    exists_lipschitz_intrinsic_canonical_height T q₀ d₀.toProperChainMetric.chains_compatibleMetric hExp
  let e : V ≃ₗ[ℝ] W := q₀.symm.trans q
  have hπe (g : R.carrier) : (π g).toAdd = e (π₀ g).toAdd := by
    apply height_eq_of_exponential_linear hExp π π₀ e.toLinearMap
    intro x
    rw [hπExp, hπ₀Exp]
    simp [e]
  have hπ₀ : LipschitzWith (⟨L, hL⟩ : ℝ≥0) (fun g => (π₀ g).toAdd) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [dist_eq_norm]
    exact hπ₀Lip x y
  obtain ⟨n, φ, hφ0, hf, hb⟩ :=
    exists_intrinsic_smooth_coordinates T q₀ Exp hExp π₀ hπ₀.continuous hπ₀Exp
  obtain ⟨hfLip, hbLip⟩ := hcompat n φ hf hb
  let c := ControlledContraction.ofChart φ hφ0 hfLip hbLip
  have hunimod (x : GroupLieAlgebra (𝓘(ℝ, R.modelSpace)) R.carrier) :
      LinearMap.trace ℝ _ (ad ℝ _ x) = 0 :=
    trace_ad_eq_zero_of_intrinsic_kernel_haar T q₀ Exp hExp π₀ hπ₀.continuous hπ₀Exp m x
  obtain ⟨x, hx⟩ := LieAlgebra.exists_isCartanSubalgebra_engel ℝ
    (GroupLieAlgebra (𝓘(ℝ, R.modelSpace)) R.carrier)
  let H := LieSubalgebra.engel ℝ x
  let : H.IsCartanSubalgebra := hx
  obtain ⟨M⟩ := nonempty_cartanWordModel H T
  let D := M.supportIn T hunimod q₀
  have hheight := M.exists_uniform_height_intrinsic T hunimod q₀ Exp hExp
    m π₀ hπ₀Exp hπ₀
    d₀.minimizing_compatibleMetric remezPolynomialInput geodesicMetricExistenceInput
  let A := (templateSymmetryGroup D).map (heightConjugation e)
  refine ⟨A, finite_heightConjugation e (templateSymmetryGroup D), ?_⟩
  intro K C hK hC
  let Q := @SelfQuasiIsometry R.carrier d.compatibleMetric.toPseudoMetricSpace K C
  let f : Q → R.carrier → R.carrier := by
    let := d.compatibleMetric
    exact fun F => F.toFun
  let g : Q → R.carrier → R.carrier := by
    let := d.compatibleMetric
    exact fun F => F.inverse
  have hK₀ : 0 ≤ K := le_trans zero_le_one hK
  have hf : letI := d.compatibleMetric
      ∀ F x y, dist (f F x) (f F y) ≤ K * dist x y + (C + 3 * K * C) := by
    let := d.compatibleMetric
    intro F x y
    exact (F.upper x y).trans (by nlinarith)
  have hg : letI := d.compatibleMetric
      ∀ F x y, dist (g F x) (g F y) ≤ K * dist x y + (C + 3 * K * C) := by
    let := d.compatibleMetric
    intro F x y
    exact (F.inverse_upper hK₀ x y).trans (by linarith)
  have hgf : letI := d.compatibleMetric
      ∀ F x, dist (g F (f F x)) x ≤ C + 2 * K * C := by
    let := d.compatibleMetric
    intro F x
    exact (F.left_inverse_close hK₀ x).trans (by linarith)
  have hfg : letI := d.compatibleMetric
      ∀ F x, dist (f F (g F x)) x ≤ C + 2 * K * C := by
    let := d.compatibleMetric
    intro F x
    exact ((dist_comm _ _).trans_le (F.inverse_close x)).trans (by nlinarith)
  obtain ⟨κ, ξ, ε, hκ, hξ, _, hf', hg', hgf', hfg'⟩ :=
    coarse_pair_metric_change d d₀.toProperChainMetric hK₀
      (by positivity : 0 ≤ C + 3 * K * C) (by positivity : 0 ≤ C + 2 * K * C)
      f g hf hg hgf hfg
  obtain ⟨label, B, hB, hbound⟩ := uniform_affine_height_of_coarse_inverse_pairs
    c d₀.minimizing_compatibleMetric D π₀ hL hπ₀Lip hheight
    hκ hξ f g hf' hg' hgf' hfg'
  refine ⟨‖e.toContinuousLinearEquiv.toContinuousLinearMap‖ * B,
    mul_nonneg (norm_nonneg _) hB, ?_⟩
  intro F
  refine ⟨⟨heightConjugation e (label F).val, ?_⟩, fun y => ?_⟩
  · exact ⟨(label F).val, (label F).property, rfl⟩
  · simp only [hπe]
    exact norm_height_difference_le e _ _ _ (label F).val (hbound F y)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CorrectedHeightRecognition
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

namespace OAI

/-! # Corrected-height recognition without the KMN input -/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory ThompsonNonamenability
open scoped IsMulCommutative

instance height_quotient_commutative
    {G W : Type} [Group G] [AddCommGroup W] (τ : G →* Multiplicative W) :
    IsMulCommutative (G ⧸ τ.ker) := by
  let f : (G ⧸ τ.ker) →* Multiplicative W :=
    τ.range.subtype.comp (QuotientGroup.quotientKerEquivRange τ).toMonoidHom
  have hf : Function.Injective f :=
    Subtype.val_injective.comp (QuotientGroup.quotientKerEquivRange τ).injective
  exact ⟨⟨fun a b => hf (by simp only [map_mul, mul_comm])⟩⟩

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Recognition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Unconditional quasi-isometric recognition of virtually polycyclic groups

The geometric height theorem, finiteness and duality endgame, and solvable
lattice realization combine with Gromov's polynomial-growth theorem to yield
virtual polycyclicity and a finite-index uniform-lattice model.
-/

noncomputable section
namespace PolycyclicRecognition

open Module LieAlgebra MeasureTheory
open scoped Manifold NNReal

/-- The standalone geometric main theorem of the paper. -/
theorem main_uniform_bounded_height_oai
    (R : SimplyConnectedSolvableLieModel) (d : ProperChainMetric R.carrier)
    {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, R.modelSpace)) R.carrier) a)
    (huni : ModelIsUnimodular R)
    {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
    (q : HeightSpace T.character ≃ₗ[ℝ] W)
    (Exp : GroupLieAlgebra (𝓘(ℝ, R.modelSpace)) R.carrier → R.carrier)
    (hExp : IsGroupExponential Exp) (π : R.carrier →* Multiplicative W)
    (hπExp : ∀ x, (π (Exp x)).toAdd = q (heightProjection T.character x)) :
    letI := d.compatibleMetric
    ∃ A : Subgroup (W ≃ₗ[ℝ] W), Set.Finite (A : Set (W ≃ₗ[ℝ] W)) ∧
      ∀ K C : ℝ, 1 ≤ K → 0 ≤ C → ∃ B : ℝ, 0 ≤ B ∧
        ∀ F : SelfQuasiIsometry R.carrier K C, ∃ AF : A, ∀ g,
          ‖(π (F.toFun g)).toAdd - ((π (F.toFun 1)).toAdd + AF.val (π g).toAdd)‖ ≤ B :=
  uniform_bounded_height R d T huni q Exp hExp π hπExp

end PolycyclicRecognition

end

end OAI
end

theorem solution : type_of% @OAI.PolycyclicRecognition.main_uniform_bounded_height_oai := @OAI.PolycyclicRecognition.main_uniform_bounded_height_oai
