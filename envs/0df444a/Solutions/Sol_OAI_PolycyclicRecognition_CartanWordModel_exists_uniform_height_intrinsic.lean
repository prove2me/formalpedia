-- Prove2me | solution 1 for OAI.PolycyclicRecognition.CartanWordModel.exists_uniform_height_intrinsic
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-02T22:59:32.91503+00:00
-- url     : https://prove2.me/submissions/6e09d83a-65e0-4c3a-8577-1ad3be3155c0

import Mathlib
import Definitions.Def_PolycyclicRecognition
import Definitions.Def_OAIQ093D022
import Theorems.Thm_OAI_PolycyclicRecognition_CartanWordModel_exists_published_sublinear_height
import Theorems.Thm_OAI_PolycyclicRecognition_CartanWordModel_uniform_normalized_affine_bound_of_published_inputs_and_sublinear
import Theorems.Thm_OAI_PolycyclicRecognition_cartan_unitary_reduced_vanishing
import Theorems.Thm_OAI_PolycyclicRecognition_exponentialLinearRealizationInput_intrinsic
import Theorems.Thm_OAI_PolycyclicRecognition_intrinsic_exponential_injective

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_ClosedEmbeddingSplitKernel
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A closed kernel embedding gives a closed embedding over a split quotient -/

noncomputable section
namespace PolycyclicRecognition

variable {N G Q : Type} [Group N] [Group G] [Group Q]
  [TopologicalSpace N] [TopologicalSpace G] [TopologicalSpace Q]
  [IsTopologicalGroup N] [IsTopologicalGroup G] [IsTopologicalGroup Q]
  (f : N →* G) (hf : Continuous f) (π : G →* Q) (hπ : Continuous π)
  (s : C(Q, N)) (hs : ∀ q, π (f (s q)) = q)

omit [IsTopologicalGroup Q] in
include hf hπ s hs in
/-- Global section coordinates reduce closedness and the induced topology
of a subgroup to those of its map on the kernel. -/
theorem closedEmbedding_of_splitKernel
    (hk : Topology.IsClosedEmbedding (splitKernelHom f π)) :
    Topology.IsClosedEmbedding f := by
  let sG : C(Q, G) := ⟨fun q => f (s q), hf.comp s.continuous⟩
  let eN := quotientSectionHomeomorph (π.comp f) (hπ.comp hf) s hs
  let eG := quotientSectionHomeomorph π hπ sG hs
  have heq : f = eG.symm ∘ Prod.map id (splitKernelHom f π) ∘ eN := by
    funext n
    change f n = f (n * (s (π (f n)))⁻¹) * f (s (π (f n)))
    rw [map_mul, map_inv, inv_mul_cancel_right]
  rw [heq]
  exact eG.symm.isClosedEmbedding.comp
    ((Topology.IsClosedEmbedding.id.prodMap hk).comp eN.isClosedEmbedding)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_InvariantDisintegration
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Conditional measures over an invariant measurable factor

Disintegrating the graph of an invariant measurable map gives a measurable
probability kernel with the original measure as barycenter. Uniqueness of
conditional kernels proves invariance of its components almost everywhere,
for each acting element. No ergodicity is assumed here.
-/

noncomputable section

namespace PolycyclicRecognition

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal ProbabilityTheory

variable {G X Y : Type} [Group G] [MeasurableSpace X] [MeasurableSpace Y]
  [MulAction G X] [MeasurableConstSMul G X] [StandardBorelSpace X] [Nonempty X]
  (μ : Measure X) [IsProbabilityMeasure μ] (f : X → Y) (hf : Measurable f)

include hf

omit [StandardBorelSpace X] [Nonempty X] [IsProbabilityMeasure μ] in
theorem factorGraphMeasure_fst : (factorGraphMeasure μ f hf).fst = μ.map f := by
  have hm : Measurable (fun x => (f x, x)) := hf.prodMk measurable_id
  rw [factorGraphMeasure, Measure.fst, Measure.map_map measurable_fst hm]
  rfl

theorem factorConditionalKernel_disintegrate :
    μ.map f ⊗ₘ factorConditionalKernel μ f hf = factorGraphMeasure μ f hf := by
  rw [← factorGraphMeasure_fst μ f hf]
  unfold factorConditionalKernel
  exact (factorGraphMeasure μ f hf).disintegrate _

/-- Conditioning preserves the original measure as its setwise barycenter. -/
theorem factorConditionalKernel_barycenter (s : Set X) (hs : MeasurableSet s) :
    μ s = ∫⁻ x, factorConditionalKernel μ f hf (f x) s ∂μ := by
  have hm : Measurable (fun x => (f x, x)) := hf.prodMk measurable_id
  have h := congrArg (fun ν : Measure (Y × X) => ν (univ ×ˢ s))
    (factorConditionalKernel_disintegrate μ f hf)
  rw [Measure.compProd_apply_prod MeasurableSet.univ hs, setLIntegral_univ,
    factorGraphMeasure, Measure.map_apply hm
      (MeasurableSet.univ.prod hs)] at h
  have he : (fun x => (f x, x)) ⁻¹' (univ ×ˢ s) = s := by ext x; simp
  rw [he] at h
  rw [← h, lintegral_map (factorConditionalKernel μ f hf |>.measurable_coe hs) hf]

omit [StandardBorelSpace X] [Nonempty X] in
/-- An invariant factor makes the graph measure invariant in its second coordinate. -/
theorem factorGraphMeasure_map_smul [SMulInvariantMeasure G X μ]
    (hfi : ∀ (g : G) (s : Set Y), MeasurableSet s →
      ∀ x, f (g • x) ∈ s ↔ f x ∈ s) (g : G) :
    (factorGraphMeasure μ f hf).map (Prod.map id (g • ·)) = factorGraphMeasure μ f hf := by
  have hg : Measurable (fun x : X => g • x) := measurable_const_smul g
  have hm : Measurable (fun x => (f x, x)) := hf.prodMk measurable_id
  rw [factorGraphMeasure, Measure.map_map (measurable_id.prodMap hg) hm]
  apply Measure.ext_prod
  intro s t hs ht
  have hcomp : Measurable (Prod.map id (g • ·) ∘ (fun x => (f x, x))) :=
    (measurable_id.prodMap hg).comp hm
  rw [Measure.map_apply hcomp (hs.prod ht), Measure.map_apply hm (hs.prod ht)]
  have he : (Prod.map id (g • ·) ∘ (fun x => (f x, x))) ⁻¹' (s ×ˢ t) =
      (g • ·) ⁻¹' ((fun x => (f x, x)) ⁻¹' (s ×ˢ t)) := by
    ext x
    change (f x ∈ s ∧ g • x ∈ t) ↔ (f (g • x) ∈ s ∧ g • x ∈ t)
    rw [hfi g s hs x]
  rw [he, measure_preimage_smul μ g]

/-- Each fixed acting element preserves almost every conditional probability. -/
theorem factorConditionalKernel_map_smul_ae [SMulInvariantMeasure G X μ]
    (hfi : ∀ (g : G) (s : Set Y), MeasurableSet s →
      ∀ x, f (g • x) ∈ s ↔ f x ∈ s) (g : G) :
    ∀ᵐ y ∂μ.map f,
      (factorConditionalKernel μ f hf y).map (g • ·) = factorConditionalKernel μ f hf y := by
  have hg : Measurable (fun x : X => g • x) := measurable_const_smul g
  have hdis : factorGraphMeasure μ f hf = (factorGraphMeasure μ f hf).fst ⊗ₘ
      Kernel.map (factorConditionalKernel μ f hf) (g • ·) := by
    rw [factorGraphMeasure_fst μ f hf, Measure.compProd_map hg,
      factorConditionalKernel_disintegrate μ f hf, factorGraphMeasure_map_smul μ f hf hfi g]
  have h := eq_condKernel_of_measure_eq_compProd
    (Kernel.map (factorConditionalKernel μ f hf) (g • ·)) hdis
  rw [factorGraphMeasure_fst μ f hf] at h
  filter_upwards [h] with y hy
  simpa only [Kernel.map_apply _ hg, factorConditionalKernel] using hy

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_InvariantFactor
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Conditioning on all invariant measurable sets

The factor retains the original points but equips them with the sigma algebra
of invariant sets. Its conditional kernel is pointwise constant on every orbit
and has the original probability as its barycenter.
-/

noncomputable section

namespace PolycyclicRecognition

open MeasureTheory ProbabilityTheory Set

variable (G X : Type) [Group G] [mX : MeasurableSpace X] [MulAction G X]

theorem measurableSet_invariantSigma {s : Set X} :
    @MeasurableSet X (invariantSigma G X) s ↔
      @MeasurableSet X mX s ∧ ∀ g : G, (g • ·) ⁻¹' s = s := by
  rw [invariantSigma, MeasurableSpace.measurableSet_iInf]
  simp only [MeasurableSpace.measurableSet_invariants]
  exact ⟨fun h => ⟨(h 1).1, fun g => (h g).2⟩,
    fun h g => ⟨h.1, h.2 g⟩⟩

variable {G X}

/-- Every measurable scalar observable on the factor is exactly orbit invariant. -/
theorem invariantFactor_observable {Z : Type} [MeasurableSpace Z]
    [MeasurableSingletonClass Z] (f : InvariantFactor G X → Z) (hf : Measurable f)
    (g : G) (x : X) : f (invariantFactorMap G X (g • x)) =
      f (invariantFactorMap G X x) := by
  have hm : @Measurable X (InvariantFactor G X) (invariantSigma G X) _
      (invariantFactorMap G X) := by
    rw [measurable_iff_comap_le]
    change ((invariantSigma G X).comap InvariantFactor.val).comap (invariantFactorMap G X) ≤ _
    rw [MeasurableSpace.comap_comp]
    change (invariantSigma G X).comap id ≤ _
    rw [MeasurableSpace.comap_id]
  have h : @Measurable X Z (MeasurableSpace.invariants (g • ·)) _
      (fun x : X => f (invariantFactorMap G X x)) :=
    (hf.comp hm).mono (iInf_le _ g) le_rfl
  exact congrFun (MeasurableSpace.comp_eq_of_measurable_invariants h) x

variable [StandardBorelSpace X] [Nonempty X]
  (μ : Measure X) [IsProbabilityMeasure μ]

theorem invariantConditionalMeasures_barycenter (s : Set X) (hs : MeasurableSet s) :
    μ s = ∫⁻ x, invariantConditionalMeasures (G := G) μ x s ∂μ :=
  factorConditionalKernel_barycenter μ (invariantFactorMap G X)
    (measurable_invariantFactorMap G X) s hs

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_ConditionalKernelFiber
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Conditional probabilities preserve factor observables

Every measurable observable of the conditioning factor is almost surely
constant under almost every component, at its value on that component.
-/

noncomputable section

namespace PolycyclicRecognition

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

variable {X Y Z : Type} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
  [StandardBorelSpace X] [Nonempty X] [MeasurableEq Z]
  (μ : Measure X) [IsProbabilityMeasure μ] (f : X → Y) (hf : Measurable f)
  (h : Y → Z) (hh : Measurable h)

include hh

/-- A factor observable retains its value under the conditional probability. -/
theorem factorConditionalKernel_fiber :
    ∀ᵐ y ∂μ.map f, ∀ᵐ x ∂factorConditionalKernel μ f hf y, h (f x) = h y := by
  have hm : Measurable (fun x => (f x, x)) := hf.prodMk measurable_id
  have he : ∀ᵐ p : Y × X ∂factorGraphMeasure μ f hf, h (f p.2) = h p.1 := by
    apply (ae_map_iff hm.aemeasurable
      (measurableSet_eq_fun ((hh.comp hf).comp measurable_snd) (hh.comp measurable_fst))).2
    exact Filter.Eventually.of_forall (fun _ => rfl)
  rw [← factorConditionalKernel_disintegrate μ f hf] at he
  exact Measure.ae_ae_of_ae_compProd he

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_ConditionalKernelAlmostEverywhere
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Transferring almost-everywhere statements to conditional measures -/

noncomputable section

namespace PolycyclicRecognition

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

variable {X Y : Type} [MeasurableSpace X] [MeasurableSpace Y]
  [StandardBorelSpace X] [Nonempty X]
  (μ : Measure X) [IsProbabilityMeasure μ] (f : X → Y) (hf : Measurable f)

theorem factorConditionalKernel_ae {P : X → Prop}
    (hPm : MeasurableSet {x | P x}) (hP : ∀ᵐ x ∂μ, P x) :
    ∀ᵐ y ∂μ.map f, ∀ᵐ x ∂factorConditionalKernel μ f hf y, P x := by
  have hm : Measurable (fun x => (f x, x)) := hf.prodMk measurable_id
  have he : ∀ᵐ p : Y × X ∂factorGraphMeasure μ f hf, P p.2 := by
    exact (ae_map_iff hm.aemeasurable (hPm.preimage measurable_snd)).2 hP
  rw [← factorConditionalKernel_disintegrate μ f hf] at he
  exact Measure.ae_ae_of_ae_compProd he

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
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_ConjugationLift
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Recovering a group action from faithful conjugation

Pointwise automorphisms compatible with ambient conjugation automatically
form an action. This removes a separate action-law assumption when the Cartan
automorphisms have already been identified in a faithful representation.
-/

noncomputable section

namespace PolycyclicRecognition

variable {N D G : Type} [Group N] [Group D] [Group G]

theorem conjugationLiftOfNormal_spec (ι : N →* G) (κ : D →* G)
    (hι : Function.Injective ι) (hnormal : ι.range.Normal) (d : D) (n : N) :
    ι (conjugationLiftOfNormal ι κ hι hnormal d n) = κ d * ι n * (κ d)⁻¹ := by
  let _ := hnormal
  simp only [conjugationLiftOfNormal, conjugationLift, MonoidHom.coe_mk, OneHom.coe_mk,
    MulEquiv.trans_apply, MonoidHom.apply_ofInjective_symm,
    MulAut.conjNormal_apply, MonoidHom.ofInjective_apply]

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
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_ExponentialIntegralCurve
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.chartExponentialFlow_zero _root_.OAI.PolycyclicRecognition.derivationSemidirectHom_apply _root_.OAI.PolycyclicRecognition.exponentialHomOfDynkin_apply_exp _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.integrateNilpotentLieEquiv_apply_exp _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Intrinsic exponential curves and the invariant vector field

The group law and derivative at zero determine the global differential
equation of an intrinsic exponential curve.
-/

noncomputable section
namespace PolycyclicRecognition

open scoped Manifold

variable {E G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace G] [ChartedSpace E G] [Group G]
  [LieGroup (𝓘(ℝ, E)) ⊤ G]

omit [FiniteDimensional ℝ E] in
/-- The intrinsic characterization determines the exponential uniquely.
This uses manifold ODE uniqueness for the already constructed invariant
vector field, with no external Lie-theoretic input. -/
theorem IsGroupExponential.unique [T2Space G]
    {Exp Exp' : GroupLieAlgebra (𝓘(ℝ, E)) G → G}
    (hExp : IsGroupExponential Exp) (hExp' : IsGroupExponential Exp') : Exp = Exp' := by
  funext v
  have hv : ContMDiff (𝓘(ℝ, E)) ((𝓘(ℝ, E)).prod (𝓘(ℝ, E))) 1
      (fun g : G => (⟨g, mulInvariantVectorField v g⟩ : TangentBundle (𝓘(ℝ, E)) G)) :=
    (contMDiff_mulInvariantVectorField v).of_le (by norm_num)
  have heq := isMIntegralCurve_Ioo_eq_of_contMDiff_boundaryless (t₀ := 0) hv
    (hExp.isMIntegralCurve v) (hExp'.isMIntegralCurve v)
    (by simp only [zero_smul, hExp.map_zero, hExp'.map_zero])
  simpa only [one_smul] using congrFun heq 1

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_ConnectedIdealNormality
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Normality of integrated ideals in a connected Lie group

The normalizer contains each exponential one-parameter subgroup, so the
basis-generation theorem makes it the whole group. Surjectivity of the
ambient exponential is not needed.
-/

noncomputable section
namespace PolycyclicRecognition

open scoped Manifold

variable {E G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace G] [ChartedSpace E G]
  [Group G] [LieGroup (𝓘(ℝ, E)) ⊤ G] [T2Space G]
  [IsTopologicalGroup G] [PreconnectedSpace G]

theorem normal_of_exponential_ideal_connected
    {Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G} (hExp : IsGroupExponential Exp)
    (I : LieIdeal ℝ (GroupLieAlgebra (𝓘(ℝ, E)) G)) (S : Subgroup G)
    (hS : (S : Set G) = Exp '' (I : Set (GroupLieAlgebra (𝓘(ℝ, E)) G))) : S.Normal := by
  have hconj (x : GroupLieAlgebra (𝓘(ℝ, E)) G) (y : G) (hy : y ∈ S) :
      Exp x * y * (Exp x)⁻¹ ∈ S := by
    change y ∈ (S : Set G) at hy
    change Exp x * y * (Exp x)⁻¹ ∈ (S : Set G)
    rw [hS] at hy ⊢
    obtain ⟨v, hv, rfl⟩ := hy
    rw [conjugation_exponential hExp]
    change Exp (adjointLinearMap (E := E) (Exp x) v) ∈ _
    have he := adjointLinearMap_exponential hExp x 1
    simp only [one_smul] at he
    rw [he]
    refine ⟨NormedSpace.exp (groupAdjointOperator (E := E) x) v, ?_, rfl⟩
    let U : Submodule ℝ E := I.toSubmodule
    exact exp_apply_mem_of_stable U U.closed_of_finiteDimensional
      (groupAdjointOperator (E := E) x) (fun w hw => I.lie_mem hw) hv
  apply Subgroup.normalizer_eq_top_iff.mp
  apply subgroup_eq_top_of_exponential_basis hExp (Module.finBasis ℝ E)
  intro i t
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · exact hconj (t • Module.finBasis ℝ E i) y
  · intro hy
    have h := hconj (-(t • Module.finBasis ℝ E i)) _ hy
    have heq : Exp (-(t • Module.finBasis ℝ E i)) *
        (Exp (t • Module.finBasis ℝ E i) * y * (Exp (t • Module.finBasis ℝ E i))⁻¹) *
        (Exp (-(t • Module.finBasis ℝ E i)))⁻¹ = y := by
      erw [hExp.map_neg]
      group
    rwa [heq] at h

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_FiniteOrbitAverage
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_countable _root_.OAI.PolycyclicRecognition.finitelyGeneratedSubgroupIndex_countable _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite convex averages of translates

The same finite data act on actual functions and on their L2 classes. This
allows the averages to be transported to a conditional component measure.
-/

noncomputable section

namespace PolycyclicRecognition

open MeasureTheory Set

variable {G X : Type} [Group G] [MulAction G X]

theorem FiniteOrbitAverage.apply_le_one (A : FiniteOrbitAverage G) (f : X → ℝ)
    (hf : ∀ x, f x ≤ 1) (x : X) : A.apply f x ≤ 1 := by
  calc
    A.apply f x ≤ ∑ i, A.weight i * 1 :=
      Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hf _) (A.nonneg i))
    _ = 1 := by simpa only [mul_one] using A.mass

variable [MeasurableSpace X] [MeasurableConstSMul G X]

theorem FiniteOrbitAverage.measurable_apply (A : FiniteOrbitAverage G) (f : X → ℝ)
    (hf : Measurable f) : Measurable (A.apply f) :=
  Finset.measurable_sum _ (fun i _ => measurable_const.mul
    (hf.comp (measurable_const_smul (A.element i)⁻¹)))

variable
  (μ : Measure X) [SMulInvariantMeasure G X μ]

/-- Every vector in the convex hull of an orbit has finite averaging data. -/
theorem exists_finiteOrbitAverage (v w : Lp ℝ 2 μ)
    (hw : w ∈ convexHull ℝ (range (fun g : G => stationaryPullback μ g v))) :
    ∃ A : FiniteOrbitAverage G, A.onL2 μ v = w := by
  obtain ⟨ι, hι, a, z, ha, hs, hz, he⟩ := mem_convexHull_iff_exists_fintype.mp hw
  let := hι
  choose g hg using hz
  let A : FiniteOrbitAverage G :=
    { index := ι
      finiteIndex := hι
      weight := a
      nonneg := ha
      mass := hs
      element := g }
  refine ⟨A, ?_⟩
  change (∑ i, a i • stationaryPullback μ (g i) v) = w
  simpa only [hg] using he

/-- Pointwise representatives of the finite Hilbert average. -/
theorem FiniteOrbitAverage.onL2_coe (A : FiniteOrbitAverage G) (v : Lp ℝ 2 μ) :
    (A.onL2 μ v : X → ℝ) =ᵐ[μ] A.apply v := by
  have hsum := Lp.coeFn_finsetSum Finset.univ
    (fun i : A.index => A.weight i • stationaryPullback μ (A.element i) v)
  have hi (i : A.index) :
      ((A.weight i • stationaryPullback μ (A.element i) v : Lp ℝ 2 μ) : X → ℝ)
        =ᵐ[μ] fun x => A.weight i * v ((A.element i)⁻¹ • x) := by
    have hsm := Lp.coeFn_smul (A.weight i) (stationaryPullback μ (A.element i) v)
    have hp := Lp.coeFn_compMeasurePreserving v (measurePreserving_smul (A.element i)⁻¹ μ)
    filter_upwards [hsm, hp] with x hx hpx
    exact hx.trans (congrArg (fun t : ℝ => A.weight i * t) hpx)
  filter_upwards [hsum, ae_all_iff.2 hi] with x hx hi
  change (A.onL2 μ v) x = ∑ i, A.weight i * v ((A.element i)⁻¹ • x)
  rw [Finset.sum_apply] at hx
  exact hx.trans (Finset.sum_congr rfl (fun i _ => hi i))

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_GroupAveragedRepresentative
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exactly invariant representatives from group averaging

A probability equivalent to Haar measure is quasi-preserved by every right
translation. On the invariant measurable set where an orbit function is
essentially constant, its group integral is that constant. Assigning zero on
the complement gives a measurable, everywhere invariant representative.
-/

noncomputable section

namespace PolycyclicRecognition

open MeasureTheory MeasureTheory.Measure Set Filter

variable {G X : Type} [Group G] [MeasurableSpace G] [MeasurableSpace X]
  [MulAction G X] (η : Measure G) [IsProbabilityMeasure η]

theorem measurable_groupAverage (f : X → ℝ)
    (hf : Measurable (fun p : X × G => f (p.2 • p.1))) :
    Measurable (groupAverage η f) :=
  hf.stronglyMeasurable.integral_prod_right'.measurable

theorem measurableSet_groupAverageGood (f : X → ℝ)
    (hf : Measurable (fun p : X × G => f (p.2 • p.1))) :
    MeasurableSet (groupAverageGood η f) := by
  have hm := measurable_groupAverage η f hf
  have hs : MeasurableSet {p : X × G | f (p.2 • p.1) ≠ groupAverage η f p.1} :=
    (measurableSet_eq_fun hf (hm.comp measurable_fst)).compl
  have hmass := measurable_measure_prodMk_left (ν := η) hs
  have he : groupAverageGood η f =
      {x | η (Prod.mk x ⁻¹' {p : X × G | f (p.2 • p.1) ≠ groupAverage η f p.1}) = 0} := by
    ext x
    simp only [groupAverageGood, mem_ofPred_eq, measure_eq_zero_iff_ae_notMem,
      mem_preimage, not_not]
  rw [he]
  exact measurableSet_eq_fun hmass measurable_const

omit [MeasurableSpace X] in
theorem groupAverageGood_smul (f : X → ℝ)
    (hq : ∀ h : G, QuasiMeasurePreserving (fun g => g * h) η η)
    {x : X} (hx : x ∈ groupAverageGood η f) (h : G) :
    h • x ∈ groupAverageGood η f ∧ groupAverage η f (h • x) = groupAverage η f x := by
  have he : ∀ᵐ g ∂η, f (g • (h • x)) = groupAverage η f x := by
    simpa only [mul_smul] using (hq h).ae hx
  have hav : groupAverage η f (h • x) = groupAverage η f x := by
    rw [groupAverage, integral_congr_ae he]
    simp
  exact ⟨by simpa only [groupAverageGood, mem_ofPred_eq, hav] using he, hav⟩

theorem measurable_invariantRepresentative_of_groupAverage
    (hq : ∀ h : G, QuasiMeasurePreserving (fun g => g * h) η η)
    (μ : Measure X) [SFinite μ] (f : X → ℝ) (hf : Measurable f)
    (ha : Measurable (fun p : G × X => p.1 • p.2))
    (hi : ∀ g : G, (fun x => f (g • x)) =ᵐ[μ] f) :
    ∃ F : X → ℝ, Measurable F ∧ F =ᵐ[μ] f ∧ ∀ (g : G) x, F (g • x) = F x := by
  have hfx : Measurable (fun p : X × G => f (p.2 • p.1)) :=
    (hf.comp ha).comp measurable_swap
  let S := groupAverageGood η f
  let F := S.indicator (groupAverage η f)
  have hSm : MeasurableSet S := measurableSet_groupAverageGood η f hfx
  have haex : ∀ᵐ x ∂μ, ∀ᵐ g ∂η, f (g • x) = f x := by
    apply (Measure.ae_ae_comm (μ := η) (ν := μ)
      (measurableSet_eq_fun (hf.comp ha) (hf.comp measurable_snd))).1
    exact Filter.Eventually.of_forall hi
  refine ⟨F, (measurable_groupAverage η f hfx).indicator hSm, ?_, ?_⟩
  · filter_upwards [haex] with x hx
    have hav : groupAverage η f x = f x := by
      rw [groupAverage, integral_congr_ae hx]
      simp
    have hS : x ∈ S := by
      change ∀ᵐ g ∂η, f (g • x) = groupAverage η f x
      simpa only [hav] using hx
    simp only [F, indicator_of_mem hS, hav]
  · intro g x
    by_cases hx : x ∈ S
    · obtain ⟨hg, he⟩ := groupAverageGood_smul η f hq hx g
      change g • x ∈ S at hg
      simp only [F, indicator_of_mem hx, indicator_of_mem hg, he]
    · have hg : g • x ∉ S := by
        intro h
        have hh := (groupAverageGood_smul η f hq h g⁻¹).1
        exact hx (by simpa only [inv_smul_smul] using hh)
      simp only [F, indicator_of_notMem hx, indicator_of_notMem hg]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_HilbertOrbitAverage
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instNonemptyBases _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_nonempty _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Hilbert averaging over a group orbit

The closed convex hull of a unitary orbit has a fixed vector of minimal norm.
This requires no invariant mean on the acting group. It supplies the averaging
step in the construction of ergodic conditional component measures.
-/

noncomputable section

namespace PolycyclicRecognition

open Set

variable {G E : Type} [Group G] [NormedAddCommGroup E]
  [InnerProductSpace ℝ E]
  (ρ : G →* (E ≃ₗᵢ[ℝ] E)) (x : E)

theorem hilbertOrbitHull_nonempty : (hilbertOrbitHull ρ x).Nonempty :=
  (Set.range_nonempty (fun g => ρ g x)).convexHull.closure

theorem hilbertOrbitHull_convex : Convex ℝ (hilbertOrbitHull ρ x) :=
  (convex_convexHull ℝ _).closure

/-- Every acting isometry preserves the closed convex hull. -/
theorem hilbertOrbitHull_map (g : G) {y : E} (hy : y ∈ hilbertOrbitHull ρ x) :
    ρ g y ∈ hilbertOrbitHull ρ x := by
  apply closure_minimal (t := (ρ g) ⁻¹' hilbertOrbitHull ρ x) ?_
    (isClosed_closure.preimage (ρ g).continuous) hy
  apply convexHull_min
  · rintro _ ⟨h, rfl⟩
    apply subset_closure
    apply subset_convexHull ℝ
    refine ⟨g * h, ?_⟩
    change ρ (g * h) x = ρ g (ρ h x)
    rw [map_mul]
    rfl
  · exact (hilbertOrbitHull_convex ρ x).linear_preimage (ρ g).toLinearEquiv.toLinearMap

variable [CompleteSpace E]

/-- A fixed vector is a norm limit of finite convex combinations of the orbit. -/
theorem exists_fixed_in_hilbertOrbitHull :
    ∃ y ∈ hilbertOrbitHull ρ x, ∀ g : G, ρ g y = y := by
  obtain ⟨y, hy, hmin⟩ := exists_norm_eq_iInf_of_complete_convex
    (hilbertOrbitHull_nonempty ρ x) isClosed_closure.isComplete
    (hilbertOrbitHull_convex ρ x) (0 : E)
  refine ⟨y, hy, fun g => ?_⟩
  have hi := (norm_eq_iInf_iff_real_inner_le_zero
    (hilbertOrbitHull_convex ρ x) hy).mp hmin (ρ g y) (hilbertOrbitHull_map ρ x g hy)
  have hn : ‖ρ g y‖ = ‖y‖ := (ρ g).norm_map y
  have hu := real_inner_le_norm y (ρ g y)
  have hl : ‖y‖ ^ 2 ≤ inner ℝ y (ρ g y) := by
    have hi' : -(inner ℝ y (ρ g y)) ≤ -‖y‖ ^ 2 := by
      simpa only [zero_sub, inner_neg_left, inner_sub_right, real_inner_self_eq_norm_sq,
        neg_sub, sub_nonpos] using hi
    linarith
  have he : inner ℝ (ρ g y) y = ‖y‖ ^ 2 := by
    rw [real_inner_comm]
    rw [hn] at hu
    nlinarith
  exact eq_of_norm_le_re_inner_eq_norm_sq (𝕜 := ℝ) hn.le he

section IsometricAction

variable [DistribMulAction G E] [SMulCommClass G ℝ E] [IsIsometricSMul G E]

/-- The convex orbit averaging theorem in the unbundled action notation. -/
theorem exists_fixed_in_convex_orbit (x : E) :
    ∃ y ∈ closure (convexHull ℝ (range (fun g : G => g • x))),
      ∀ g : G, g • y = y :=
  exists_fixed_in_hilbertOrbitHull (isometricLinearAction (G := G) (E := E)) x

end IsometricAction

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_DenseInvariantMeasure
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Invariance on a dense set of acting elements

For a continuous action on a compact metric space, a finite measure invariant
under a dense family of group elements is invariant under the whole group.
This turns countably many almost-everywhere identities of conditional kernels
into invariance of their components for a locally compact second countable group.
-/

noncomputable section

namespace PolycyclicRecognition

open MeasureTheory Set
open scoped CompactlySupported

variable {G X ι : Type} [Group G] [TopologicalSpace G]
  [FirstCountableTopology G] [LocallyCompactSpace G]
  [MetricSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X] [MulAction G X] [ContinuousSMul G X]
  (ν : Measure X) [IsFiniteMeasure ν]

/-- Dense invariance is sufficient; the dense family need not be a subgroup. -/
theorem smulInvariantMeasure_of_denseRange (a : ι → G) (ha : DenseRange a)
    (hν : ∀ i, ν.map (a i • ·) = ν) : SMulInvariantMeasure G X ν := by
  have hmap (g : G) : ν.map (g • ·) = ν := by
    apply Measure.ext_of_integral_eq_on_compactlySupported
    intro f
    have hc : Continuous (fun g : G => ∫ x, f (g • x) ∂ν) := by
      have h := continuous_parametric_integral_of_continuous (μ := ν)
        (f := fun (g : G) (x : X) => f (g • x))
        (show Continuous (fun p : G × X => f (p.1 • p.2)) from
          f.continuous.comp continuous_smul) isCompact_univ
      simpa only [setIntegral_univ] using h
    have hmf (g : G) : (∫ x, f x ∂ν.map (g • ·)) = ∫ x, f (g • x) ∂ν :=
      integral_map (continuous_const_smul g).measurable.aemeasurable
        (show AEStronglyMeasurable (fun x : X => f x) (ν.map (g • ·)) from
          f.continuous.aestronglyMeasurable)
    have he : (fun g : G => ∫ x, f (g • x) ∂ν) = fun _ => ∫ x, f x ∂ν := by
      apply ha.equalizer hc continuous_const
      funext i
      change (∫ x, f (a i • x) ∂ν) = _
      rw [← hmf (a i), hν i]
      rfl
    rw [hmf g, congrFun he g]
  refine ⟨fun g s hs => ?_⟩
  rw [← Measure.map_apply (continuous_const_smul g).measurable hs, hmap g]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_InvariantFactorComponents
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instNonemptyBases _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_countable _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_nonempty _root_.OAI.PolycyclicRecognition.finitelyGeneratedSubgroupIndex_countable _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Invariance of the conditional component measures

Only countably many identities are intersected. Continuity of the action
extends invariance from the dense sequence to the full acting group.
-/

noncomputable section

namespace PolycyclicRecognition

open MeasureTheory ProbabilityTheory TopologicalSpace

variable {G X Y : Type} [Group G] [TopologicalSpace G]
  [LocallyCompactSpace G] [SecondCountableTopology G]
  [MetricSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X] [StandardBorelSpace X] [Nonempty X]
  [MeasurableSpace Y] [MulAction G X] [ContinuousSMul G X]
  (μ : Measure X) [IsProbabilityMeasure μ] [SMulInvariantMeasure G X μ]
  (f : X → Y) (hf : Measurable f)

/-- The invariant factor may have a sigma algebra that is not countably generated. -/
theorem factorConditionalKernel_invariant_ae_dense
    (hfi : ∀ (g : G) (s : Set Y), MeasurableSet s →
      ∀ x, f (g • x) ∈ s ↔ f x ∈ s) :
    ∀ᵐ y ∂μ.map f, SMulInvariantMeasure G X (factorConditionalKernel μ f hf y) := by
  have h := ae_all_iff.2 (fun n : ℕ =>
    factorConditionalKernel_map_smul_ae μ f hf hfi (denseSeq G n))
  filter_upwards [h] with y hy
  exact smulInvariantMeasure_of_denseRange _ (denseSeq G) (denseRange_denseSeq G) hy

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_InvariantFactorObservables
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Observable and almost-everywhere identities on invariant components -/

noncomputable section

namespace PolycyclicRecognition

open MeasureTheory ProbabilityTheory Set

variable {G X Z : Type} [Group G] [MeasurableSpace X] [MulAction G X]
  [MeasurableSpace Z]

theorem measurable_invariantFactor_lift (F : X → Z) (hF : Measurable F)
    (hi : ∀ (g : G) x, F (g • x) = F x) :
    Measurable (fun y : InvariantFactor G X => F y.val) := by
  intro s hs
  change ∃ t, @MeasurableSet X (invariantSigma G X) t ∧
    InvariantFactor.val ⁻¹' t = (fun y : InvariantFactor G X => F y.val) ⁻¹' s
  refine ⟨F ⁻¹' s, (measurableSet_invariantSigma G X).2 ⟨hF hs, ?_⟩, rfl⟩
  intro g
  ext x
  simp only [mem_preimage, hi]

theorem invariantFactor_membership_smul (g : G) (s : Set (InvariantFactor G X))
    (hs : MeasurableSet s) (x : X) :
    invariantFactorMap G X (g • x) ∈ s ↔ invariantFactorMap G X x ∈ s := by
  have hm : @Measurable X (InvariantFactor G X) (invariantSigma G X) _
      (invariantFactorMap G X) := by
    rw [measurable_iff_comap_le]
    change ((invariantSigma G X).comap InvariantFactor.val).comap (invariantFactorMap G X) ≤ _
    rw [MeasurableSpace.comap_comp]
    change (invariantSigma G X).comap id ≤ _
    rw [MeasurableSpace.comap_id]
  have he := ((measurableSet_invariantSigma G X).mp (hm hs)).2 g
  exact Iff.of_eq (congrArg (fun t : Set X => x ∈ t) he)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_KernelConullRepair
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Repairing a probability kernel on a null set of parameters -/

noncomputable section

namespace PolycyclicRecognition

open MeasureTheory ProbabilityTheory Set Filter

variable {X Y : Type} [MeasurableSpace X] [MeasurableSpace Y]
  (ν : Measure Y) [IsProbabilityMeasure ν] (κ : Kernel Y X) [IsMarkovKernel κ]

theorem exists_kernel_conull_repair (P : Measure X → Prop)
    (hP : ∀ᵐ y ∂ν, P (κ y)) :
    ∃ k : Y → Measure X, Measurable k ∧
      (∀ y, IsProbabilityMeasure (k y) ∧ P (k y)) ∧ k =ᵐ[ν] κ := by
  classical
  let T := toMeasurable ν {y | ¬P (κ y)}
  have hTm : MeasurableSet T := measurableSet_toMeasurable _ _
  have hT : ν T = 0 := (measure_toMeasurable _).trans (ae_iff.mp hP)
  have hae : ∀ᵐ y ∂ν, y ∉ T := measure_eq_zero_iff_ae_notMem.mp hT
  obtain ⟨y₀, hy₀⟩ := hae.exists
  have h₀ : P (κ y₀) := by
    by_contra h
    exact hy₀ (subset_toMeasurable ν _ h)
  let k : Y → Measure X := T.piecewise (fun _ => κ y₀) κ
  refine ⟨k, measurable_const.piecewise hTm κ.measurable, ?_, ?_⟩
  · intro y
    by_cases hy : y ∈ T
    · simpa only [k, piecewise_eq_of_mem T _ _ hy] using
        (show IsProbabilityMeasure (κ y₀) ∧ P (κ y₀) from ⟨(by first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)), h₀⟩)
    · have h : P (κ y) := by
        by_contra h
        exact hy (subset_toMeasurable ν _ h)
      simpa only [k, piecewise_eq_of_notMem T _ _ hy] using
        (show IsProbabilityMeasure (κ y) ∧ P (κ y) from ⟨(by first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)), h⟩)
  · filter_upwards [hae] with y hy
    exact piecewise_eq_of_notMem T _ _ hy

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_KernelLinearSplitting
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The linear splitting used by the height-kernel product

The tangent inclusion onto the height kernel, together with any continuous
linear right inverse of height, gives an invertible product differential.
-/

noncomputable section
namespace PolycyclicRecognition

variable {U V W : Type}
  [NormedAddCommGroup U] [NormedSpace ℝ U]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

theorem kernel_coprod_bijective
    (j : U →L[ℝ] V) (d : V →L[ℝ] W) (l : W →L[ℝ] V)
    (hj : Function.Injective j)
    (hrange : LinearMap.range j.toLinearMap = LinearMap.ker d.toLinearMap)
    (hdl : d.comp l = ContinuousLinearMap.id ℝ W) :
    Function.Bijective (j.coprod l) := by
  have hdj (u : U) : d (j u) = 0 := by
    have hu : j u ∈ LinearMap.range j.toLinearMap := ⟨u, rfl⟩
    rwa [hrange] at hu
  have hdl' (w : W) : d (l w) = w := congrArg (fun F : W →L[ℝ] W => F w) hdl
  constructor
  · intro a b hab
    have hw : a.2 = b.2 := by
      have h := congrArg d hab
      change d (j a.1 + l a.2) = d (j b.1 + l b.2) at h
      simpa only [map_add, hdj, hdl', zero_add] using h
    apply Prod.ext _ hw
    apply hj
    change j a.1 + l a.2 = j b.1 + l b.2 at hab
    rw [hw] at hab
    exact add_right_cancel hab
  · intro v
    have hv : v - l (d v) ∈ LinearMap.range j.toLinearMap := by
      rw [hrange]
      change d (v - l (d v)) = 0
      rw [map_sub, hdl', sub_self]
    obtain ⟨u, hu⟩ := hv
    refine ⟨(u, d v), ?_⟩
    change j u = v - l (d v) at hu
    change j u + l (d v) = v
    rw [hu, sub_add_cancel]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_ManifoldLocalCoordinates
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Local coordinates from an invertible manifold differential

This is the chart reduction needed when the source of an integrated Lie
homomorphism is a manifold rather than a vector space.
-/

noncomputable section
namespace PolycyclicRecognition

open Set Filter
open scoped Manifold Topology ContDiff

variable {E F H M N : Type}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [TopologicalSpace N] [ChartedSpace F N] [IsManifold (𝓘(ℝ, F)) ∞ N]

theorem locally_injective_open_of_manifold_mfderiv_equiv
    {f : M → N} {x : M} (d : E ≃L[ℝ] F) (hIrange : Set.range I = univ)
    (hf : ContMDiffAt I (𝓘(ℝ, F)) ∞ f x)
    (hd : HasMFDerivAt I (𝓘(ℝ, F)) f x d.toContinuousLinearMap) :
    (∃ U ∈ 𝓝 x, InjOn f U) ∧ map f (𝓝 x) = 𝓝 (f x) := by
  let φ := extChartAt I x
  have hx : x ∈ φ.source := mem_extChartAt_source x
  have hleft : φ.symm (φ x) = x := φ.left_inv hx
  have hφ : ContMDiffAt (𝓘(ℝ, E)) I ∞ φ.symm (φ x) := by
    simpa only [hIrange, contMDiffWithinAt_univ] using
      (contMDiffWithinAt_extChartAt_symm_range_self (I := I) (n := ∞) x)
  have hφd : HasMFDerivAt (𝓘(ℝ, E)) I φ.symm (φ x)
      (ContinuousLinearMap.id ℝ E) := by
    apply (hφ.mdifferentiableAt (by simp)).hasMFDerivAt.congr_mfderiv
    have hh := mfderivWithin_range_extChartAt_symm (I := I) (x := x)
    rw [hIrange, mfderivWithin_univ] at hh
    exact hh
  have hq : ContMDiffAt (𝓘(ℝ, E)) (𝓘(ℝ, F)) ∞ (f ∘ φ.symm) (φ x) :=
    hf.comp_of_eq hφ hleft
  have hqd : HasMFDerivAt (𝓘(ℝ, E)) (𝓘(ℝ, F)) (f ∘ φ.symm) (φ x)
      d.toContinuousLinearMap := by
    have hd' : HasMFDerivAt I (𝓘(ℝ, F)) f (φ.symm (φ x))
        d.toContinuousLinearMap := by rwa [hleft]
    have hh : HasMFDerivAt (𝓘(ℝ, E)) (𝓘(ℝ, F)) (f ∘ φ.symm) (φ x)
        (d.toContinuousLinearMap.comp (ContinuousLinearMap.id ℝ E)) :=
      hd'.comp (φ x) hφd
    apply hh.congr_mfderiv
    ext v
    rfl
  obtain ⟨⟨U, hU, hi⟩, hm⟩ := locally_injective_open_of_mfderiv_equiv d hq hqd
  constructor
  · refine ⟨φ.source ∩ φ ⁻¹' U, ?_, ?_⟩
    · exact inter_mem (extChartAt_source_mem_nhds (I := I) x)
        ((continuousAt_extChartAt x).preimage_mem_nhds hU)
    · intro a ha b hb hab
      apply φ.injOn ha.1 hb.1
      apply hi ha.2 hb.2
      simpa only [Function.comp_apply, φ.left_inv ha.1, φ.left_inv hb.1] using hab
  · have hψ : map φ.symm (𝓝 (φ x)) = 𝓝 x := by
      simpa only [φ, hIrange, nhdsWithin_univ] using
        map_extChartAt_symm_nhdsWithin_range (I := I) x
    calc
      map f (𝓝 x) = map f (map φ.symm (𝓝 (φ x))) := by rw [hψ]
      _ = map (f ∘ φ.symm) (𝓝 (φ x)) := map_map
      _ = 𝓝 (f (φ.symm (φ x))) := hm
      _ = 𝓝 (f x) := by rw [hleft]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_KernelProductCoordinates
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Local multiplication coordinates for an integrated height kernel

The kernel inclusion and a normalized height section have complementary
actual differentials. Their product map is therefore a local coordinate
map at the identity, by the ordinary inverse function theorem.
-/

noncomputable section
namespace PolycyclicRecognition

open Set Filter
open scoped Manifold Topology ContDiff

variable {EN E W N G : Type}
  [NormedAddCommGroup EN] [NormedSpace ℝ EN] [FiniteDimensional ℝ EN]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  [TopologicalSpace N] [ChartedSpace EN N] [IsManifold (𝓘(ℝ, EN)) ∞ N]
  [TopologicalSpace G] [ChartedSpace E G] [Group G] [LieGroup (𝓘(ℝ, E)) ⊤ G]

theorem kernel_product_local_coordinates
    (f : N → G) (s : W → G) (n : N)
    (hf : ContMDiff (𝓘(ℝ, EN)) (𝓘(ℝ, E)) ∞ f)
    (hs : ContMDiff (𝓘(ℝ, W)) (𝓘(ℝ, E)) ∞ s)
    (hf1 : f n = 1) (hs0 : s 0 = 1)
    (j : EN →L[ℝ] E) (d : E →L[ℝ] W) (l : W →L[ℝ] E)
    (hfj : HasMFDerivAt (𝓘(ℝ, EN)) (𝓘(ℝ, E)) f n j)
    (hsl : HasMFDerivAt (𝓘(ℝ, W)) (𝓘(ℝ, E)) s 0 l)
    (hj : Function.Injective j)
    (hrange : LinearMap.range j.toLinearMap = LinearMap.ker d.toLinearMap)
    (hdl : d.comp l = ContinuousLinearMap.id ℝ W) :
    (∃ U ∈ 𝓝 (n, (0 : W)), InjOn (fun p : N × W => f p.1 * s p.2) U) ∧
      map (fun p : N × W => f p.1 * s p.2) (𝓝 (n, (0 : W))) = 𝓝 (1 : G) := by
  let D : (EN × W) ≃L[ℝ] E :=
    (LinearEquiv.ofBijective (j.coprod l).toLinearMap
      (kernel_coprod_bijective j d l hj hrange hdl)).toContinuousLinearEquiv
  have hD : D.toContinuousLinearMap = j.coprod l := rfl
  have hfst : HasMFDerivAt ((𝓘(ℝ, EN)).prod (𝓘(ℝ, W))) (𝓘(ℝ, EN))
      Prod.fst (n, (0 : W)) (ContinuousLinearMap.fst ℝ EN W) := hasMFDerivAt_fst (n, (0 : W))
  have hsnd : HasMFDerivAt ((𝓘(ℝ, EN)).prod (𝓘(ℝ, W))) (𝓘(ℝ, W))
      Prod.snd (n, (0 : W)) (ContinuousLinearMap.snd ℝ EN W) := hasMFDerivAt_snd (n, (0 : W))
  have hp := PolycyclicRecognition.HasMFDerivAt.mul_at_one
    (hfj.comp (n, (0 : W)) hfst) (hsl.comp (n, (0 : W)) hsnd) hf1 hs0
  have hprod : HasMFDerivAt ((𝓘(ℝ, EN)).prod (𝓘(ℝ, W))) (𝓘(ℝ, E))
      (fun p : N × W => f p.1 * s p.2) (n, (0 : W)) D.toContinuousLinearMap := by
    rw [hD]
    apply hp.congr_mfderiv
    exact ContinuousLinearMap.comp_fst_add_comp_snd j l
  have hsmooth : ContMDiffAt ((𝓘(ℝ, EN)).prod (𝓘(ℝ, W))) (𝓘(ℝ, E)) ∞
      (fun p : N × W => f p.1 * s p.2) (n, (0 : W)) := by
    exact ((hf.comp contMDiff_fst).mul (hs.comp contMDiff_snd)).contMDiffAt
  simpa only [hf1, hs0, mul_one] using
    locally_injective_open_of_manifold_mfderiv_equiv D
      (by ext p; simp) hsmooth hprod

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_LocalSubmersion
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The local open mapping consequence needed for Cartan multiplication

This is a direct chartwise application of Mathlib's strict inverse function
theorem. It uses a surjective differential, without requiring complementary
Cartan factors or assuming a local product theorem.
-/

noncomputable section

namespace PolycyclicRecognition

open Filter Set
open scoped Manifold Topology

variable {E E' H H' M M' : Type}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [CompleteSpace E']
  [TopologicalSpace H] [TopologicalSpace H']
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ E' H'}
  [I.Boundaryless] [J.Boundaryless]
  [TopologicalSpace M] [TopologicalSpace M']
  [ChartedSpace H M] [ChartedSpace H' M']
  {f : M → M'} {x : M}

/-- A continuously differentiable map with surjective differential sends
the neighborhood filter exactly onto the neighborhood filter of its value. -/
theorem map_nhds_eq_of_surjective_mfderiv
    (hf : ContMDiffAt I J 1 f x)
    (hsurj : Function.Surjective (mfderiv I J f x)) :
    map f (𝓝 x) = 𝓝 (f x) := by
  let F := writtenInExtChartAt I J x f
  have hC : ContDiffAt ℝ 1 F (extChartAt I x x) := by
    simpa only [F, writtenInExtChartAt, I.range_eq_univ, contDiffWithinAt_univ] using
      (contMDiffAt_iff.mp hf).2
  have hD := hf.mdifferentiableAt one_ne_zero
  have hF : Function.Surjective (fderiv ℝ F (extChartAt I x x)) := by
    intro y
    obtain ⟨v, hv⟩ := hsurj ((tangentSpaceCastModel J (f x)).symm y)
    refine ⟨tangentSpaceCastModel I x v, ?_⟩
    rw [hD.mfderiv] at hv
    simp only [F, I.range_eq_univ, fderivWithin_univ, ContinuousLinearMap.comp_apply,
      ContinuousLinearEquiv.coe_coe] at hv
    -- the casts are the identity by definition here (d13f23b simplifies them away)
    exact hv
  have hmap := (hC.hasStrictFDerivAt one_ne_zero).map_nhds_eq_of_surj
    (LinearMap.range_eq_top.mpr hF)
  have hvalue : F (extChartAt I x x) = extChartAt J (f x) (f x) := by
    simp only [F, writtenInExtChartAt, Function.comp_apply, extChartAt_to_inv]
  rw [hvalue] at hmap
  have hsource : map (extChartAt I x).symm (𝓝 (extChartAt I x x)) = 𝓝 x := by
    simpa only [I.range_eq_univ, nhdsWithin_univ] using
      (map_extChartAt_symm_nhdsWithin_range (I := I) x)
  have htarget : map (extChartAt J (f x)).symm
      (𝓝 (extChartAt J (f x) (f x))) = 𝓝 (f x) := by
    simpa only [J.range_eq_univ, nhdsWithin_univ] using
      (map_extChartAt_symm_nhdsWithin_range (I := J) (f x))
  have hcancel : (extChartAt J (f x)).symm ∘ extChartAt J (f x) ∘ f =ᶠ[𝓝 x] f := by
    filter_upwards [hf.continuousAt.preimage_mem_nhds
      (extChartAt_source_mem_nhds (I := J) (f x))] with z hz
    exact (extChartAt J (f x)).left_inv hz
  calc
    map f (𝓝 x) = map ((extChartAt J (f x)).symm ∘ extChartAt J (f x) ∘ f) (𝓝 x) :=
      (Filter.map_congr hcancel).symm
    _ = map (extChartAt J (f x)).symm (map F (𝓝 (extChartAt I x x))) := by
      dsimp only [F, writtenInExtChartAt]
      simp only [← map_map]
      rw [hsource]
    _ = 𝓝 (f x) := by rw [hmap, htarget]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_NilpotentBasisWordChoices
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite word choices for the actual Cartan basis -/

noncomputable section
namespace PolycyclicRecognition

open Module LieModule

variable {L : Type} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  [LieRing.IsNilpotent L]

/-- A fixed linear basis supplies a finite generating alphabet. Nilpotence
and finite maximization supply all remaining word-chart choices. -/
theorem exists_nilpotent_basis_word_choices (b : Basis (Fin (finrank ℝ L)) ℝ L) :
    ∃ (d : ℕ) (β : WordBasisSelections (fun i => b i) (boundedBracketWords d)),
      lowerCentralSeries ℝ L L d = ⊥ ∧
      (∀ i : Fin (finrank ℝ L), FreeMagma.of i ∈ boundedBracketWords d) ∧
      IsMaximizingColumnBasis (wordListCoordinates (fun i => b i) (boundedBracketWords d) b)
        (fun w => bracketWordExponent (fun _ : Fin (finrank ℝ L) => 1) w) β.val := by
  classical
  obtain ⟨k, hk⟩ := LieModule.IsNilpotent.nilpotent ℝ L L
  have hd : lowerCentralSeries ℝ L L (k + 2) = ⊥ := by
    apply eq_bot_iff.mpr
    exact (antitone_lowerCentralSeries ℝ L L (by omega : k ≤ k + 2)).trans (by rw [hk])
  have hgen : LieSubalgebra.lieSpan ℝ L (Set.range fun i => b i) = ⊤ := by
    apply eq_top_iff.mpr
    intro x _
    exact LieSubalgebra.submodule_span_le_lieSpan
      (by rw [show Submodule.span ℝ (Set.range fun i => b i) = ⊤ from b.span_eq]; trivial)
  let : Nonempty (WordBasisSelections (fun i => b i) (boundedBracketWords (k + 2))) :=
    nonempty_wordBasisSelections (fun i => b i) hd hgen
  obtain ⟨β, hβ⟩ := exists_maximizing_wordBasis (fun i => b i) (boundedBracketWords (k + 2)) b
    (fun w => bracketWordExponent (fun _ : Fin (finrank ℝ L) => 1) w)
  refine ⟨k + 2, β, hd, ?_, hβ⟩
  intro i
  simp only [mem_boundedBracketWords, bracketWordDepth]
  omega

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

variable {L : Type} [LieRing L] [LieAlgebra ℝ L] (N : NilpotentLieModel L)

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
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_UnconditionalNilpotentModel
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.abelianRealCoordinates _root_.OAI.PolycyclicRecognition.abelianRealFiniteDimensional _root_.OAI.PolycyclicRecognition.abelianRealLieAbelian _root_.OAI.PolycyclicRecognition.abelianRealNormedLie _root_.OAI.PolycyclicRecognition.derivationLieSpaceFiniteDimensional _root_.OAI.PolycyclicRecognition.derivationLieSpaceRealNormed _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.polynomialLieIdealSubgroup_normal _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Simply connected nilpotent model existence without published inputs -/

noncomputable section
namespace PolycyclicRecognition

open scoped Manifold

theorem nilpotentLieModel_exists (L : Type) [RealNormedLieAlgebra L]
    [FiniteDimensional ℝ L] (hnil : LieRing.IsNilpotent L) : Nonempty (NilpotentLieModel L) := by
  obtain ⟨P⟩ := polynomialExponentialCoordinates_nilpotent L hnil
  let := P
  exact ⟨polynomialCoordinateLieModel L⟩

theorem nilpotentLieExistenceInput (L : Type) [LieRing L] [LieAlgebra ℝ L]
    [FiniteDimensional ℝ L] : NilpotentLieExistenceInput L := by
  let b := Module.finBasis ℝ L
  let : NormedAddCommGroup L := NormedAddCommGroup.induced L _ b.equivFun b.equivFun.injective
  let : NormedSpace ℝ L := NormedSpace.induced ℝ L _ b.equivFun
  let : RealNormedLieAlgebra L :=
    { (inferInstance : NormedAddCommGroup L), (inferInstance : LieRing L),
      (inferInstance : NormedSpace ℝ L), (inferInstance : LieAlgebra ℝ L) with }
  exact nilpotentLieModel_exists L

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
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_CompactLifts
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Compact lifts under an open quotient

A compact target set has lifts in one compact source set for an open
surjection from a locally compact space. This is the precise bounded-step
lifting consequence needed by the Cartan multiplication map.
-/

noncomputable section

namespace PolycyclicRecognition

open Set Topology

/-- Compact lifts need no global section, properness, or injectivity of the
quotient map. Finite local compact neighborhoods suffice. -/
theorem exists_compact_lifts_of_open_surjection
    {X Y : Type} [TopologicalSpace X] [LocallyCompactSpace X] [TopologicalSpace Y]
    (f : X → Y) (hopen : IsOpenMap f) (hsurj : Function.Surjective f)
    {K : Set Y} (hK : IsCompact K) :
    ∃ C : Set X, IsCompact C ∧ K ⊆ f '' C := by
  choose C hC hn using (fun x : X => exists_compact_mem_nhds x)
  have hxi (x : X) : x ∈ interior (C x) := mem_interior_iff_mem_nhds.mpr (hn x)
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun x => f '' interior (C x))
    (fun _ => hopen _ isOpen_interior) (by
      intro y _
      obtain ⟨x, rfl⟩ := hsurj y
      exact mem_iUnion.mpr ⟨x, ⟨x, hxi x, rfl⟩⟩)
  refine ⟨⋃ x ∈ t, C x, t.isCompact_biUnion (fun x _ => hC x), ?_⟩
  intro y hy
  obtain ⟨x, hx, z, hz, hzy⟩ := mem_iUnion₂.mp (ht hy)
  exact ⟨z, mem_iUnion₂.mpr ⟨x, hx, interior_subset hz⟩, hzy⟩

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanMultiplication
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Multiplication of overlapping Cartan factors

Compatible conjugation gives the actual multiplication homomorphism from the
semidirect product. Its kernel records the overlap. Local surjectivity makes
it globally surjective in a connected ambient group, and an open product map
then has compact lifts of compact sets. No complementary subgroup is assumed.
-/

noncomputable section

namespace PolycyclicRecognition

open Set Topology
open scoped Topology

section OpenProduct

variable {N D G : Type} [Group N] [Group D] [Group G]
  [TopologicalSpace N] [TopologicalSpace D] [TopologicalSpace G]
  [IsTopologicalGroup N] [IsTopologicalGroup D] [IsTopologicalGroup G]

set_option maxHeartbeats 1000000 in
/-- For a product of two homomorphisms, openness at the identity propagates
to every point by independent left and right translations. -/
theorem isOpenMap_factorProduct_of_map_nhds_one
    (ι : N →* G) (κ : D →* G)
    (hlocal : Filter.map (fun p : N × D => ι p.1 * κ p.2) (𝓝 1) = 𝓝 1) :
    IsOpenMap (fun p : N × D => ι p.1 * κ p.2) := by
  let f : N × D → G := fun p => ι p.1 * κ p.2
  apply IsOpenMap.of_nhds_le
  intro p
  let t : N × D ≃ₜ N × D :=
    (Homeomorph.mulLeft p.1).prodCongr (Homeomorph.mulRight p.2)
  let s : G ≃ₜ G := (Homeomorph.mulLeft (ι p.1)).trans (Homeomorph.mulRight (κ p.2))
  have ht : t 1 = p := by
    change (p.1 * 1, 1 * p.2) = p
    simp only [mul_one, one_mul, Prod.eta]
  have hs : s 1 = f p := by simp [s, f]
  have hcomm : f ∘ t = s ∘ f := by
    funext q
    simp [t, s, f, map_mul, mul_assoc]
  have hm : Filter.map f (𝓝 p) = 𝓝 (f p) := by
    rw [← ht, ← t.map_nhds_eq, Filter.map_map, hcomm, ← Filter.map_map,
      hlocal, s.map_nhds_eq, hs]
    rw [ht]
  exact hm.ge

end OpenProduct

variable {N D G : Type} [Group N] [Group D] [Group G]
  (ι : N →* G) (κ : D →* G) (φ : D →* MulAut N)
  (hconj : ∀ d n, ι (φ d n) = κ d * ι n * (κ d)⁻¹)

set_option maxHeartbeats 1000000 in
/-- The range agrees with the ordinary product parameterization, even when
its fibers are nontrivial. -/
theorem range_cartanMultiplication :
    Set.range (cartanMultiplication ι κ φ hconj) =
      Set.range (fun p : N × D => ι p.1 * κ p.2) := by
  ext g
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨(z.left, z.right), rfl⟩
  · rintro ⟨⟨n, d⟩, rfl⟩
    exact ⟨⟨n, d⟩, rfl⟩

variable [TopologicalSpace G] [IsTopologicalGroup G] [PreconnectedSpace G]

set_option maxHeartbeats 1000000 in
/-- A local product neighborhood is enough for global factorization in the
connected ambient group. -/
theorem cartanMultiplication_surjective_of_range_mem_nhds
    (hlocal : Set.range (fun p : N × D => ι p.1 * κ p.2) ∈ 𝓝 (1 : G)) :
    Function.Surjective (cartanMultiplication ι κ φ hconj) := by
  let q := cartanMultiplication ι κ φ hconj
  have hn : (q.range : Set G) ∈ 𝓝 (1 : G) := by
    change Set.range q ∈ 𝓝 (1 : G)
    rwa [range_cartanMultiplication]
  have ho := q.range.isOpen_of_mem_nhds hn
  have hc : IsClopen (q.range : Set G) := ⟨q.range.isClosed_of_isOpen ho, ho⟩
  have he := hc.eq_univ ⟨1, q.range.one_mem⟩
  intro g
  have hg : g ∈ (q.range : Set G) := he.symm ▸ mem_univ g
  exact hg

variable [TopologicalSpace N] [TopologicalSpace D] [LocallyCompactSpace (N × D)]

set_option maxHeartbeats 1000000 in
include hconj in
/-- Once the local product map is open, every compact set admits compact
factor lifts. The kernel can be arbitrary. -/
theorem exists_compact_cartan_factor_lifts
    (hlocal : Set.range (fun p : N × D => ι p.1 * κ p.2) ∈ 𝓝 (1 : G))
    (hopen : IsOpenMap (fun p : N × D => ι p.1 * κ p.2))
    {K : Set G} (hK : IsCompact K) :
    ∃ C : Set (N × D), IsCompact C ∧ K ⊆ (fun p : N × D => ι p.1 * κ p.2) '' C := by
  apply exists_compact_lifts_of_open_surjection _ hopen _ hK
  intro g
  obtain ⟨z, hz⟩ := cartanMultiplication_surjective_of_range_mem_nhds ι κ φ hconj hlocal g
  exact ⟨(z.left, z.right), hz⟩

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanLocalProduct
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Local multiplication of the actual Cartan factors

Surjectivity of the differential follows from spanning by the two Lie
algebras. The factors may overlap. The resulting local open mapping property
propagates to every point by left and right translations.
-/

noncomputable section

namespace PolycyclicRecognition

open Filter Set
open scoped Manifold Topology ContDiff

variable {EN ED EG N D G : Type}
  [NormedAddCommGroup EN] [NormedSpace ℝ EN] [FiniteDimensional ℝ EN]
  [NormedAddCommGroup ED] [NormedSpace ℝ ED] [FiniteDimensional ℝ ED]
  [NormedAddCommGroup EG] [NormedSpace ℝ EG] [FiniteDimensional ℝ EG]
  [TopologicalSpace N] [ChartedSpace EN N] [Group N] [LieGroup (𝓘(ℝ, EN)) ⊤ N]
  [TopologicalSpace D] [ChartedSpace ED D] [Group D] [LieGroup (𝓘(ℝ, ED)) ⊤ D]
  [TopologicalSpace G] [ChartedSpace EG G] [Group G] [LieGroup (𝓘(ℝ, EG)) ⊤ G]
  (ι : N →* G) (κ : D →* G)

omit [FiniteDimensional ℝ EN] [FiniteDimensional ℝ ED] [FiniteDimensional ℝ EG]
  [LieGroup (𝓘(ℝ, EN)) ⊤ N] [LieGroup (𝓘(ℝ, ED)) ⊤ D] in
set_option maxHeartbeats 1000000 in
/-- The derivative of multiplication of homomorphisms at the identity is
the sum of their derivatives. -/
theorem mfderiv_factorProduct_one
    (hι : ContMDiff (𝓘(ℝ, EN)) (𝓘(ℝ, EG)) ∞ ι)
    (hκ : ContMDiff (𝓘(ℝ, ED)) (𝓘(ℝ, EG)) ∞ κ)
    (v : TangentSpace ((𝓘(ℝ, EN)).prod (𝓘(ℝ, ED))) (1 : N × D)) :
    (tangentSpaceCast (𝓘(ℝ, EG)) (ι 1 * κ 1) 1)
      (mfderiv ((𝓘(ℝ, EN)).prod (𝓘(ℝ, ED))) (𝓘(ℝ, EG))
        (fun p : N × D => ι p.1 * κ p.2) 1 v) =
      (tangentSpaceCast (𝓘(ℝ, EG)) (ι 1) 1) (mfderiv (𝓘(ℝ, EN)) (𝓘(ℝ, EG)) ι 1 v.1) +
      (tangentSpaceCast (𝓘(ℝ, EG)) (κ 1) 1) (mfderiv (𝓘(ℝ, ED)) (𝓘(ℝ, EG)) κ 1 v.2) := by
  have hs : MDifferentiableAt ((𝓘(ℝ, EN)).prod (𝓘(ℝ, ED))) (𝓘(ℝ, EG))
      (fun p : N × D => ι p.1 * κ p.2) 1 :=
    ((hι.comp contMDiff_fst).mul (hκ.comp contMDiff_snd)).mdifferentiableAt
      (show (∞ : ℕ∞ω) ≠ 0 by simp)
  have he := mfderiv_prod_eq_add_apply (v := v) hs
  have hl : (fun z : N => ι z * κ 1) = ι := by ext z; simp
  have hr : (fun z : D => ι 1 * κ z) = κ := by ext z; simp
  change _ = mfderiv (𝓘(ℝ, EN)) (𝓘(ℝ, EG)) (fun z : N => ι z * κ 1) 1 v.1 +
    mfderiv (𝓘(ℝ, ED)) (𝓘(ℝ, EG)) (fun z : D => ι 1 * κ z) 1 v.2 at he
  rw [hl, hr] at he
  exact he

set_option maxHeartbeats 1000000 in
omit [LieGroup (𝓘(ℝ, EN)) ⊤ N] [LieGroup (𝓘(ℝ, ED)) ⊤ D] in
/-- Spanning tangent images give the exact local open mapping property. -/
theorem factorProduct_map_nhds_one
    (hι : ContMDiff (𝓘(ℝ, EN)) (𝓘(ℝ, EG)) ∞ ι)
    (hκ : ContMDiff (𝓘(ℝ, ED)) (𝓘(ℝ, EG)) ∞ κ)
    (hspan : ∀ z : GroupLieAlgebra (𝓘(ℝ, EG)) G,
      ∃ u v, (tangentSpaceCast (𝓘(ℝ, EG)) (ι 1) 1) (mfderiv (𝓘(ℝ, EN)) (𝓘(ℝ, EG)) ι 1 u) +
        (tangentSpaceCast (𝓘(ℝ, EG)) (κ 1) 1) (mfderiv (𝓘(ℝ, ED)) (𝓘(ℝ, EG)) κ 1 v) = z) :
    map (fun p : N × D => ι p.1 * κ p.2) (𝓝 (1 : N × D)) = 𝓝 (1 : G) := by
  have hs : ContMDiffAt ((𝓘(ℝ, EN)).prod (𝓘(ℝ, ED))) (𝓘(ℝ, EG)) 1
      (fun p : N × D => ι p.1 * κ p.2) 1 :=
    (((hι.comp contMDiff_fst).mul (hκ.comp contMDiff_snd)).contMDiffAt
      (x := 1)).of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hsurj : Function.Surjective
      (mfderiv ((𝓘(ℝ, EN)).prod (𝓘(ℝ, ED))) (𝓘(ℝ, EG))
        (fun p : N × D => ι p.1 * κ p.2) 1) := by
    intro z
    obtain ⟨u, v, huv⟩ := hspan ((tangentSpaceCast (𝓘(ℝ, EG)) (ι 1 * κ 1) 1) z)
    refine ⟨(u, v), (tangentSpaceCast (𝓘(ℝ, EG)) (ι 1 * κ 1) 1).injective ?_⟩
    exact (mfderiv_factorProduct_one ι κ hι hκ (u, v)).trans huv
  simpa only [Prod.fst_one, Prod.snd_one, map_one, mul_one] using
    map_nhds_eq_of_surjective_mfderiv hs hsurj

set_option maxHeartbeats 1000000 in
/-- The previously proved Cartan spanning theorem supplies the differential
surjectivity, including when the two subalgebras intersect. -/
theorem cartanFactorProduct_map_nhds_one
    {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
    (H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)) [H.IsCartanSubalgebra]
    (eN : cartanRootIdeal H ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, EN)) N)
    (eD : H ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, ED)) D)
    (hι : ContMDiff (𝓘(ℝ, EN)) (𝓘(ℝ, EG)) ∞ ι)
    (hκ : ContMDiff (𝓘(ℝ, ED)) (𝓘(ℝ, EG)) ∞ κ)
    (dι : ∀ x : cartanRootIdeal H,
      (tangentSpaceCast (𝓘(ℝ, EG)) (ι 1) 1)
        (mfderiv (𝓘(ℝ, EN)) (𝓘(ℝ, EG)) ι 1 (eN x)) = x)
    (dκ : ∀ x : H,
      (tangentSpaceCast (𝓘(ℝ, EG)) (κ 1) 1)
        (mfderiv (𝓘(ℝ, ED)) (𝓘(ℝ, EG)) κ 1 (eD x)) = x) :
    map (fun p : N × D => ι p.1 * κ p.2) (𝓝 (1 : N × D)) = 𝓝 (1 : G) := by
  apply factorProduct_map_nhds_one ι κ hι hκ
  intro z
  have hz : z ∈ (cartanRootIdeal H).toSubmodule ⊔ H.toSubmodule := by
    rw [triangular_cartan_spanning T H]
    trivial
  obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.mp hz
  refine ⟨eN ⟨u, hu⟩, eD ⟨v, hv⟩, ?_⟩
  rw [dι, dκ]
  exact huv

set_option maxHeartbeats 1000000 in
/-- A local factor product gives both global factorization and compact
lifts in a connected Lie group. No complement or global section is needed. -/
theorem factorProduct_surjective_and_compact_lifts
    [PreconnectedSpace G] [IsTopologicalGroup N] [IsTopologicalGroup D]
    [IsTopologicalGroup G] [LocallyCompactSpace N] [LocallyCompactSpace D]
    (φ : D →* MulAut N)
    (hconj : ∀ d n, ι (φ d n) = κ d * ι n * (κ d)⁻¹)
    (hlocal : map (fun p : N × D => ι p.1 * κ p.2) (𝓝 (1 : N × D)) = 𝓝 (1 : G)) :
    Function.Surjective (fun p : N × D => ι p.1 * κ p.2) ∧
      ∀ K : Set G, IsCompact K → ∃ C : Set (N × D), IsCompact C ∧
        K ⊆ (fun p : N × D => ι p.1 * κ p.2) '' C := by
  have hopen := isOpenMap_factorProduct_of_map_nhds_one ι κ hlocal
  have hnhds : Set.range (fun p : N × D => ι p.1 * κ p.2) ∈ 𝓝 (1 : G) := by
    rw [← hlocal]
    exact Filter.mem_map.mpr (by simp)
  have hsurj := cartanMultiplication_surjective_of_range_mem_nhds ι κ φ hconj hnhds
  refine ⟨?_, fun K hK => exists_compact_cartan_factor_lifts ι κ φ hconj hnhds hopen hK⟩
  intro g
  obtain ⟨z, hz⟩ := hsurj g
  exact ⟨(z.left, z.right), hz⟩

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_NilpotentPublishedInputs
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The nilpotent published-input family used by the Cartan construction

The finite BCH expansion follows Baudoin (2004), Appendix B.5--B.6.
The intrinsic adjoint calculation and integration into arbitrary Lie groups
give model existence, global coordinates, integration, and exponential
Haar compatibility.
-/

noncomputable section
namespace PolycyclicRecognition

open scoped Manifold

/-- Codimension-one induction constructs the analytic simply connected model. -/
theorem NilpotentPublishedInputs.existsModel (_h : NilpotentPublishedInputs)
    (L : Type) [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L] :
    NilpotentLieExistenceInput L :=
  nilpotentLieExistenceInput L

variable {EG G : Type} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G]
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]

/-- The six inputs for each actual cone are specializations of the cited
nilpotent theorems. Cone geometry itself is not assumed. -/
theorem NilpotentPublishedInputs.polar (h : NilpotentPublishedInputs)
    (M : CartanWordModel H) {Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G}
    (F : CartanFactorModel H Exp) (C : Set (H →ₗ[ℝ] ℝ)) :
    M.PolarConeModelInputs F C := by
  let : LieRing.IsNilpotent (cartanRootIdeal H) := LieModule.IsNilpotent.mk _ M.bound_zero
  let : LieRing.IsNilpotent ((cartanRootIdeal H) ⧸ M.coneWordIdeal C) :=
    (M.coneProjection_surjective C).lieAlgebra_isNilpotent
  exact {
    existsQ := h.existsModel _
    haarQ := h.haar _
    integratesQ := h.integrate _ _ F.N
    existsI := h.existsModel _
    haarI := h.haar _
    integratesI := fun I => h.integrate _ _ I F.N }

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_OrbitAverageIntegral
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Integrals of finite orbit averages

Convex averaging preserves integrals against an invariant measure, including
its restriction to an almost invariant measurable set.
-/

noncomputable section

namespace PolycyclicRecognition

open MeasureTheory Set
open scoped ENNReal

variable {G X : Type} [Group G] [MeasurableSpace X]
  [MulAction G X] [MeasurableConstSMul G X]
  (ν : Measure X) [SMulInvariantMeasure G X ν]

/-- Restricting an invariant measure to an almost invariant set is invariant. -/
theorem smulInvariantMeasure_restrict_ae (s : Set X) (hs : MeasurableSet s)
    (hi : ∀ g : G, (g • ·) ⁻¹' s =ᵐ[ν] s) : SMulInvariantMeasure G X (ν.restrict s) := by
  refine ⟨fun g t ht => ?_⟩
  have hp := (measurePreserving_smul g ν).restrict_preimage hs
  rw [Measure.restrict_congr_set (hi g)] at hp
  rw [← Measure.map_apply (measurable_const_smul g) ht, hp.map_eq]

/-- Finite convex averaging preserves every nonnegative integral. -/
theorem FiniteOrbitAverage.lintegral (A : FiniteOrbitAverage G) (f : X → ℝ)
    (hf : Measurable f) (hn : ∀ x, 0 ≤ f x) :
    (∫⁻ x, ENNReal.ofReal (A.apply f x) ∂ν) = ∫⁻ x, ENNReal.ofReal (f x) ∂ν := by
  have he (x : X) : ENNReal.ofReal (A.apply f x) =
      ∑ i, ENNReal.ofReal (A.weight i) * ENNReal.ofReal (f ((A.element i)⁻¹ • x)) := by
    rw [FiniteOrbitAverage.apply, ENNReal.ofReal_sum_of_nonneg
      (fun i _ => mul_nonneg (A.nonneg i) (hn _))]
    apply Finset.sum_congr rfl
    intro i _
    exact ENNReal.ofReal_mul (A.nonneg i)
  simp_rw [he]
  have hm (i : A.index) : Measurable (fun x : X =>
      ENNReal.ofReal (A.weight i) * ENNReal.ofReal (f ((A.element i)⁻¹ • x))) :=
    measurable_const.mul (ENNReal.measurable_ofReal.comp
      (hf.comp (measurable_const_smul _)))
  rw [lintegral_finsetSum Finset.univ (fun i _ => hm i)]
  have hi (i : A.index) :
      (∫⁻ x, ENNReal.ofReal (A.weight i) * ENNReal.ofReal (f ((A.element i)⁻¹ • x)) ∂ν) =
        ENNReal.ofReal (A.weight i) * ∫⁻ x, ENNReal.ofReal (f x) ∂ν := by
    have hmf : Measurable (fun x : X => ENNReal.ofReal (f ((A.element i)⁻¹ • x))) :=
      ENNReal.measurable_ofReal.comp (hf.comp (measurable_const_smul _))
    rw [lintegral_const_mul _ hmf]
    exact congrArg (fun z => ENNReal.ofReal (A.weight i) * z)
      ((measurePreserving_smul (A.element i)⁻¹ ν).lintegral_comp
        (show Measurable (fun x : X => ENNReal.ofReal (f x)) from
          ENNReal.measurable_ofReal.comp hf))
  simp_rw [hi]
  rw [← Finset.sum_mul, ← ENNReal.ofReal_sum_of_nonneg (fun i _ => A.nonneg i), A.mass]
  simp

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_OrbitAverageLimitMass
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instNonemptyBases _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_nonempty _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The mass identified by a convergent convex orbit average -/

noncomputable section

namespace PolycyclicRecognition

open MeasureTheory Set Filter
open scoped ENNReal Topology

variable {G X : Type} [Group G] [MeasurableSpace X]
  [MulAction G X] [MeasurableConstSMul G X]
  (ν : Measure X) [IsFiniteMeasure ν] [SMulInvariantMeasure G X ν]

theorem orbitAverage_limit_mass (f : X → ℝ) (hf : Measurable f)
    (hn : ∀ x, 0 ≤ f x) (hb : ∀ x, f x ≤ 1)
    (A : ℕ → FiniteOrbitAverage G) (c : ℝ)
    (hlim : ∀ᵐ x ∂ν, Tendsto (fun n => (A n).apply f x) atTop (𝓝 c)) :
    (∫⁻ x, ENNReal.ofReal (f x) ∂ν) = ENNReal.ofReal c * ν univ := by
  have ht := tendsto_lintegral_of_dominated_convergence
    (μ := ν) (fun _ : X => (1 : ℝ≥0∞))
    (fun n => ENNReal.measurable_ofReal.comp ((A n).measurable_apply f hf))
    (fun n => Filter.Eventually.of_forall (fun x => by
      simpa using ENNReal.ofReal_le_ofReal ((A n).apply_le_one f hb x)))
    (by simp)
    (hlim.mono (fun x hx => ENNReal.continuous_ofReal.continuousAt.tendsto.comp hx))
  change Tendsto (fun n => ∫⁻ x, ENNReal.ofReal ((A n).apply f x) ∂ν)
    atTop (𝓝 (∫⁻ _ : X, ENNReal.ofReal c ∂ν)) at ht
  simp_rw [FiniteOrbitAverage.lintegral ν _ f hf hn] at ht
  simp only [lintegral_const] at ht
  exact tendsto_nhds_unique tendsto_const_nhds ht

theorem orbitAverage_indicator_limit_mass (t : Set X) (ht : MeasurableSet t)
    (A : ℕ → FiniteOrbitAverage G) (c : ℝ)
    (hlim : ∀ᵐ x ∂ν,
      Tendsto (fun n => (A n).apply (t.indicator (fun _ => (1 : ℝ))) x) atTop (𝓝 c)) :
    ν t = ENNReal.ofReal c * ν univ := by
  have hm := orbitAverage_limit_mass ν (t.indicator (fun _ => (1 : ℝ)))
    (measurable_const.indicator ht)
    (fun x => by by_cases hx : x ∈ t <;> simp [hx])
    (fun x => by by_cases hx : x ∈ t <;> simp [hx]) A c hlim
  have he : (fun x => ENNReal.ofReal (t.indicator (fun _ => (1 : ℝ)) x)) =
      t.indicator (fun _ => (1 : ℝ≥0∞)) := by
    funext x
    by_cases hx : x ∈ t <;> simp [hx]
  rw [he, lintegral_indicator ht] at hm
  simpa using hm

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_PointwiseOrbitAverages
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_countable _root_.OAI.PolycyclicRecognition.finitelyGeneratedSubgroupIndex_countable _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Almost-everywhere convergence of finite orbit averages

For a countable measure-preserving action, finite convex averages of any L2
function have a subsequence converging almost everywhere to an exactly
invariant measurable function. These are actual functions, so the convergence
can be disintegrated to the conditional measures.
-/

noncomputable section

namespace PolycyclicRecognition

open MeasureTheory Set Filter
open scoped Topology

variable {G X : Type} [Group G] [MeasurableSpace X]
  [MulAction G X] [MeasurableConstSMul G X]
  (μ : Measure X) [SMulInvariantMeasure G X μ]

theorem FiniteOrbitAverage.apply_congr_ae (A : FiniteOrbitAverage G) {f h : X → ℝ}
    (hfh : f =ᵐ[μ] h) : A.apply f =ᵐ[μ] A.apply h := by
  have hi (i : A.index) : (fun x => f ((A.element i)⁻¹ • x)) =ᵐ[μ]
      fun x => h ((A.element i)⁻¹ • x) :=
    (measurePreserving_smul (A.element i)⁻¹ μ).quasiMeasurePreserving.ae_eq_comp hfh
  filter_upwards [ae_all_iff.2 hi] with x hx
  exact Finset.sum_congr rfl (fun i _ => congrArg (fun t : ℝ => A.weight i * t) (hx i))

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_ProductLocalCoordinates
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Extracting local coordinates from a product map

A local coordinate map of the form `(x,z) ↦ (f x,z)` supplies local
coordinates for `f`. This bridge works even when the target factor has no
manifold structure yet.
-/

noncomputable section
namespace PolycyclicRecognition

open Set Filter Topology

variable {X Y Z : Type} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

theorem local_coordinates_of_prodMap {f : X → Y} (x : X) (z : Z)
    (hinj : ∃ U ∈ 𝓝 (x, z), InjOn (fun p : X × Z => (f p.1, p.2)) U)
    (hmap : map (fun p : X × Z => (f p.1, p.2)) (𝓝 (x, z)) = 𝓝 (f x, z)) :
    (∃ U ∈ 𝓝 x, InjOn f U) ∧ map f (𝓝 x) = 𝓝 (f x) := by
  constructor
  · obtain ⟨U, hU, hi⟩ := hinj
    refine ⟨(fun y : X => (y, z)) ⁻¹' U, ?_, ?_⟩
    · exact (continuous_id.prodMk continuous_const).continuousAt.preimage_mem_nhds hU
    · intro a ha b hb hab
      exact congrArg Prod.fst (hi ha hb (Prod.ext hab rfl))
  · calc
      map f (𝓝 x) = map f (map Prod.fst (𝓝 (x, z))) := by rw [map_fst_nhds]
      _ = map (f ∘ Prod.fst) (𝓝 (x, z)) := map_map
      _ = map Prod.fst (map (fun p : X × Z => (f p.1, p.2)) (𝓝 (x, z))) :=
        map_map.symm
      _ = 𝓝 (f x) := by rw [hmap, map_fst_nhds]

theorem localHomeomorph_hom_of_prodMap
    {N K Q : Type} [Group N] [TopologicalSpace N] [IsTopologicalGroup N]
    [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [TopologicalSpace Q]
    (f : N →* K) (q : Q)
    (hinj : ∃ U ∈ 𝓝 (1, q), InjOn (fun p : N × Q => (f p.1, p.2)) U)
    (hmap : map (fun p : N × Q => (f p.1, p.2)) (𝓝 (1, q)) = 𝓝 (1, q)) :
    IsLocalHomeomorph f := by
  let : Zero N := ⟨1⟩
  obtain ⟨hi, hm⟩ := local_coordinates_of_prodMap (f := f) 1 q hinj (by simpa using hmap)
  apply localHomeomorph_of_translations f (fun n => Homeomorph.mulLeft n)
    (fun n => mul_one n) (fun n m => f.map_mul n m) (by
      change map f (𝓝 (1 : N)) = 𝓝 (1 : K)
      simpa only [map_one] using hm) hi

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_SimplyConnectedRetraction
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Simple connectivity of a split kernel

A continuous retraction preserves simple connectivity. A group quotient with
a normalized continuous section retracts onto its actual kernel.
-/

noncomputable section
namespace PolycyclicRecognition

open scoped ContinuousMap

theorem simplyConnectedSpace_of_continuous_retraction
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [SimplyConnectedSpace Y] (i : X → Y) (r : Y → X)
    (hi : Continuous i) (hr : Continuous r) (hri : Function.LeftInverse r i) :
    SimplyConnectedSpace X := by
  have : PathConnectedSpace X := hri.surjective.pathConnectedSpace hr
  apply simply_connected_iff_paths_homotopic'.mpr
  refine ⟨inferInstance, ?_⟩
  intro x y p q
  have h := (SimplyConnectedSpace.paths_homotopic (p.map hi) (q.map hi)).map
    (⟨r, hr⟩ : C(Y, X))
  have h' := h.pathCast (hri x).symm (hri y).symm
  have hp : ((p.map hi).map hr).cast (hri x).symm (hri y).symm = p := by
    ext t
    exact hri (p t)
  have hq : ((q.map hi).map hr).cast (hri x).symm (hri y).symm = q := by
    ext t
    exact hri (q t)
  rwa [hp, hq] at h'

theorem simplyConnectedSpace_kernel_of_section
    {G Q : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q]
    [SimplyConnectedSpace G]
    (π : G →* Q) (hπ : Continuous π) (s : C(Q, G))
    (hs : ∀ q, π (s q) = q) (hsone : s 1 = 1) : SimplyConnectedSpace π.ker := by
  let r := quotientSectionResidual π s hs
  have hr : Continuous r := by
    exact (continuous_id.mul (s.continuous.comp hπ).inv).subtype_mk _
  apply simplyConnectedSpace_of_continuous_retraction
    (fun k : π.ker => (k : G)) r continuous_subtype_val hr
  intro k
  apply Subtype.ext
  change (k : G) * (s (π k))⁻¹ = k
  rw [show π k = 1 from k.property, hsone, inv_one, mul_one]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_ConnectedHomCovering
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Inverting a local group isomorphism over a simply connected group

Local injectivity and the neighborhood-image identity at one suffice.
Translations propagate them, connectedness gives surjectivity, and the
proved covering-space argument gives the global inverse.
-/

noncomputable section
namespace PolycyclicRecognition

open Set Filter Topology

variable {N K : Type} [Group N] [TopologicalSpace N] [IsTopologicalGroup N]
  [Group K] [TopologicalSpace K] [IsTopologicalGroup K]

theorem surjective_of_hom_map_nhds_one [PreconnectedSpace K]
    (f : N →* K) (hmap : map f (𝓝 1) = 𝓝 1) : Function.Surjective f := by
  let : Zero N := ⟨1⟩
  have hm := map_nhds_of_translations f (fun n => Homeomorph.mulLeft n)
    (fun n => mul_one n) (fun n m => f.map_mul n m) hmap
  have hopen : IsOpenMap f := IsOpenMap.of_nhds_le fun n => (hm n).ge
  have hrange : IsOpen (f.range : Set K) := by
    simpa only [image_univ, MonoidHom.coe_range] using hopen univ isOpen_univ
  have hclosed := f.range.isClosed_of_isOpen hrange
  have hall : (f.range : Set K) = univ :=
    (show IsClopen (f.range : Set K) from ⟨hclosed, hrange⟩).eq_univ ⟨1, f.range.one_mem⟩
  intro k
  have hk : k ∈ f.range := by
    change k ∈ (f.range : Set K)
    rw [hall]
    trivial
  exact hk

theorem covering_of_hom_local_coordinates [PreconnectedSpace K]
    (f : N →* K) (hmap : map f (𝓝 1) = 𝓝 1)
    (hinj : ∃ U ∈ 𝓝 (1 : N), InjOn f U) : IsCoveringMap f := by
  let : Zero N := ⟨1⟩
  have hlocal := localHomeomorph_of_translations f (fun n => Homeomorph.mulLeft n)
    (fun n => mul_one n) (fun n m => f.map_mul n m) hmap hinj
  exact covering_of_translations (f := f) (R := fun n => Homeomorph.mulRight n)
    (hR := fun n m => f.map_mul m n) (hzero := f.map_one) (hf := hlocal)
    (hRinv := by
      change Continuous (fun p : N × N => p.2 * p.1⁻¹)
      exact continuous_snd.mul continuous_fst.inv)
    (hRcont := by
      change Continuous (fun p : N × N => p.2 * p.1)
      exact continuous_snd.mul continuous_fst)
    (L := fun n => Homeomorph.mulLeft n) (hL := fun n m => f.map_mul n m)
    (hsurj := surjective_of_hom_map_nhds_one f hmap)


theorem bijective_of_hom_local_coordinates [PreconnectedSpace N]
    [SimplyConnectedSpace K] [LocallyPathConnectedSpace K]
    (f : N →* K) (hmap : map f (𝓝 1) = 𝓝 1)
    (hinj : ∃ U ∈ 𝓝 (1 : N), InjOn f U) : Function.Bijective f := by
  let : Zero N := ⟨1⟩
  let cov := covering_of_hom_local_coordinates f hmap hinj
  exact (homeomorphOfSimplyConnectedCovering f cov).bijective

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_SplitKernelCoordinates
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Identifying an integrated kernel from local product coordinates

A normalized section turns a local product map into a product with the
identity. The actual kernel is simply connected by retraction. A connected
source with these local coordinates therefore maps homeomorphically onto
that kernel, and its inclusion in the ambient group is closed.
-/

noncomputable section
namespace PolycyclicRecognition

open Set Filter Topology
open scoped ContinuousMap

variable {N G Q : Type}
  [Group N] [TopologicalSpace N] [IsTopologicalGroup N]
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q]
  (π : G →* Q) (hπ : Continuous π) (s : C(Q, G))
  (hs : ∀ q, π (s q) = q) (hsone : s 1 = 1)
  (f : N →* G) (hf : ∀ n, π (f n) = 1)

omit [IsTopologicalGroup Q] in
include hπ hs hsone hf in
theorem localHomeomorph_kernel_of_split_coordinates
    (hinj : ∃ U ∈ 𝓝 ((1 : N), (1 : Q)),
      InjOn (fun p : N × Q => f p.1 * s p.2) U)
    (hmap : map (fun p : N × Q => f p.1 * s p.2) (𝓝 (1, 1)) = 𝓝 (1 : G)) :
    IsLocalHomeomorph (f.codRestrict π.ker hf) := by
  let e := (quotientSectionHomeomorph π hπ s hs).trans (Homeomorph.prodComm Q π.ker)
  let k := f.codRestrict π.ker hf
  have he (p : N × Q) : e (f p.1 * s p.2) = (k p.1, p.2) := by
    apply Prod.ext
    · apply Subtype.ext
      change (f p.1 * s p.2) * (s (π (f p.1 * s p.2)))⁻¹ = f p.1
      rw [map_mul, hf, hs, one_mul]
      exact mul_inv_cancel_right _ _
    · change π (f p.1 * s p.2) = p.2
      rw [map_mul, hf, hs, one_mul]
  have heone : e 1 = (1, 1) := by
    have hh := he (1, 1)
    simpa only [map_one, hsone, mul_one] using hh
  apply localHomeomorph_hom_of_prodMap k (1 : Q)
  · obtain ⟨U, hU, hi⟩ := hinj
    refine ⟨U, hU, ?_⟩
    intro a ha b hb hab
    apply hi ha hb
    apply e.injective
    rw [he, he]
    exact hab
  · have heq : (fun p : N × Q => (k p.1, p.2)) =
        e ∘ (fun p : N × Q => f p.1 * s p.2) := (funext he).symm
    rw [heq, ← map_map, hmap, e.map_nhds_eq, heone]

include hπ hs hsone hf in
theorem closedEmbedding_kernel_of_split_coordinates
    [PreconnectedSpace N] [LocallyPathConnectedSpace N]
    [SimplyConnectedSpace G] [T2Space Q]
    (hinj : ∃ U ∈ 𝓝 ((1 : N), (1 : Q)),
      InjOn (fun p : N × Q => f p.1 * s p.2) U)
    (hmap : map (fun p : N × Q => f p.1 * s p.2) (𝓝 (1, 1)) = 𝓝 (1 : G)) :
    Topology.IsClosedEmbedding f ∧ Set.range f = (π.ker : Set G) := by
  let k := f.codRestrict π.ker hf
  have hlocal : IsLocalHomeomorph k :=
    localHomeomorph_kernel_of_split_coordinates π hπ s hs hsone f hf hinj hmap
  let : SimplyConnectedSpace π.ker :=
    simplyConnectedSpace_kernel_of_section π hπ s hs hsone
  have hkmap : map k (𝓝 1) = 𝓝 1 := by simpa only [map_one] using hlocal.map_nhds_eq 1
  have hsurj := surjective_of_hom_map_nhds_one k hkmap
  let : LocallyPathConnectedSpace π.ker :=
    (hlocal.isOpenMap.isQuotientMap hlocal.continuous hsurj).locallyPathConnectedSpace
  obtain ⟨U, hU, h1, hi⟩ := hlocal.isLocallyInjective 1
  have hbij := bijective_of_hom_local_coordinates k hkmap ⟨U, hU.mem_nhds h1, hi⟩
  let e := hlocal.toHomeomorphOfBijective hbij
  have hclosed : IsClosed (π.ker : Set G) := isClosed_eq hπ continuous_const
  constructor
  · exact hclosed.isClosedEmbedding_subtypeVal.comp e.isClosedEmbedding
  · ext g
    constructor
    · rintro ⟨n, rfl⟩
      exact hf n
    · intro hg
      obtain ⟨n, hn⟩ := hsurj ⟨g, hg⟩
      exact ⟨n, congrArg Subtype.val hn⟩

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_HaarInvariantRepresentative
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instNonemptyBases _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_nonempty _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exactly invariant representatives for locally compact groups

The probability equivalent to Haar measure supplies the group averaging
measure. This removes countability of the acting group from the invariant
representative construction.
-/

noncomputable section

namespace PolycyclicRecognition

open MeasureTheory MeasureTheory.Measure Set Filter

variable {G X : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]
  [MeasurableSpace X] [MulAction G X] [MeasurableSMul₂ G X]
  (μ : Measure X) [SFinite μ]

theorem measurable_haarInvariantRepresentative (f : X → ℝ) (hf : Measurable f)
    (hi : ∀ g : G, (fun x => f (g • x)) =ᵐ[μ] f) :
    ∃ F : X → ℝ, Measurable F ∧ F =ᵐ[μ] f ∧ ∀ (g : G) x, F (g • x) = F x := by
  let mG : Measure G := haar
  have hq (g : G) : QuasiMeasurePreserving (fun h => h * g) mG.toFinite mG.toFinite :=
    QuasiMeasurePreserving.mono (toFinite_absolutelyContinuous mG)
      (absolutelyContinuous_toFinite mG) (quasiMeasurePreserving_mul_right mG g)
  exact measurable_invariantRepresentative_of_groupAverage mG.toFinite hq μ f hf
    measurable_smul hi

theorem aemeasurable_haarInvariantRepresentative [SMulInvariantMeasure G X μ]
    (f : X → ℝ) (hf : AEMeasurable f μ)
    (hi : ∀ g : G, (fun x => f (g • x)) =ᵐ[μ] f) :
    ∃ F : X → ℝ, Measurable F ∧ F =ᵐ[μ] f ∧ ∀ (g : G) x, F (g • x) = F x := by
  let f' := hf.mk f
  have he : f =ᵐ[μ] f' := hf.ae_eq_mk
  have hfi (g : G) : (fun x => f' (g • x)) =ᵐ[μ] f' := by
    have hc := (measurePreserving_smul g μ).quasiMeasurePreserving.ae_eq_comp he
    filter_upwards [he, hc, hi g] with x hx hxg hix
    exact hxg.symm.trans (hix.trans hx)
  obtain ⟨F, hF, hFe, hFi⟩ := measurable_haarInvariantRepresentative μ f' hf.measurable_mk hfi
  exact ⟨F, hF, hFe.trans he.symm, hFi⟩

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_HaarOrbitAverages
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Convex orbit averages for locally compact group actions -/

noncomputable section

namespace PolycyclicRecognition

open MeasureTheory Set Filter
open scoped Topology

variable {G X : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]
  [MeasurableSpace X] [MulAction G X] [MeasurableSMul₂ G X]
  (μ : Measure X) [SFinite μ] [SMulInvariantMeasure G X μ]

theorem fixedL2_haarInvariantRepresentative (v : Lp ℝ 2 μ)
    (hfix : ∀ g : G, stationaryPullback μ g v = v) :
    ∃ F : X → ℝ, Measurable F ∧ F =ᵐ[μ] v ∧ ∀ (g : G) x, F (g • x) = F x := by
  apply aemeasurable_haarInvariantRepresentative μ v (Lp.aestronglyMeasurable v).aemeasurable
  intro g
  have hp : Lp.compMeasurePreserving (fun x : X => g • x)
      (measurePreserving_smul g μ) v = v := by
    simpa only [stationaryPullback, inv_inv] using hfix g⁻¹
  have he := Lp.coeFn_compMeasurePreserving v (measurePreserving_smul g μ)
  rw [hp] at he
  exact he.symm

attribute [local instance] stationaryL2Action

theorem exists_L2_haarOrbitAverage (v : Lp ℝ 2 μ) :
    ∃ (w : Lp ℝ 2 μ) (F : X → ℝ),
      w ∈ closure (convexHull ℝ (range (fun g : G => stationaryPullback μ g v))) ∧
      Measurable F ∧ F =ᵐ[μ] w ∧ ∀ (g : G) x, F (g • x) = F x := by
  obtain ⟨w, hw, hfix⟩ := exists_fixed_in_convex_orbit (G := G) v
  obtain ⟨F, hF, he, hFi⟩ := fixedL2_haarInvariantRepresentative μ w hfix
  exact ⟨w, F, hw, hF, he, hFi⟩

theorem exists_pointwise_haarOrbitAverages (f : X → ℝ) (hf : MemLp f 2 μ) :
    ∃ (A : ℕ → FiniteOrbitAverage G) (F : X → ℝ),
      Measurable F ∧ (∀ (g : G) x, F (g • x) = F x) ∧
      ∀ᵐ x ∂μ, Tendsto (fun n => (A n).apply f x) atTop (𝓝 (F x)) := by
  let v := hf.toLp f
  obtain ⟨w, F, hw, hF, he, hFi⟩ := exists_L2_haarOrbitAverage (G := G) μ v
  obtain ⟨u, hu, hlim⟩ := mem_closure_iff_seq_limit.mp hw
  choose A hA using fun n => exists_finiteOrbitAverage (G := G) μ v (u n) (hu n)
  have hlim' : Tendsto (fun n => (A n).onL2 μ v) atTop (𝓝 w) := by
    simpa only [hA] using hlim
  have hmeas : TendstoInMeasure μ (fun n => (A n).apply f) atTop F := by
    have hcoe (n : ℕ) := ((A n).onL2_coe μ v).trans
      ((A n).apply_congr_ae μ hf.coeFn_toLp)
    exact TendstoInMeasure.congr hcoe he.symm (tendstoInMeasure_of_tendsto_Lp hlim')
  obtain ⟨ns, _, hns⟩ := hmeas.exists_seq_tendsto_ae
  exact ⟨A ∘ ns, F, hF, hFi, hns⟩

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_CountableMeasureTests
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_countable _root_.OAI.PolycyclicRecognition.finitelyGeneratedSubgroupIndex_countable _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A countable determining family for finite measures

Finite intersections of a countable measurable generator form a countable
pi system. Equality on this family and equality of total mass determine a
finite measure. This permits simultaneous statements about conditional kernels.
-/

noncomputable section

namespace PolycyclicRecognition

open MeasureTheory MeasurableSpace Set

variable (X : Type) [mX : MeasurableSpace X] [CountablyGenerated X]

theorem measurableSet_finiteMeasureTest (I : Finset ℕ) :
    MeasurableSet (finiteMeasureTest X I) := by
  exact MeasurableSet.iInter (fun i => MeasurableSet.iInter (fun _ =>
    measurableSet_natGeneratingSequence i))

theorem finiteMeasureTest_union (I J : Finset ℕ) :
    finiteMeasureTest X (I ∪ J) = finiteMeasureTest X I ∩ finiteMeasureTest X J := by
  ext x
  simp only [finiteMeasureTest, mem_iInter, Finset.mem_union, mem_inter_iff]
  constructor
  · intro h
    exact ⟨fun i hi => h i (Or.inl hi), fun i hi => h i (Or.inr hi)⟩
  · rintro ⟨hI, hJ⟩ i (hi | hi)
    · exact hI i hi
    · exact hJ i hi

theorem isPiSystem_finiteMeasureTest : IsPiSystem (range (finiteMeasureTest X)) := by
  rintro s ⟨I, rfl⟩ t ⟨J, rfl⟩ _
  exact ⟨I ∪ J, finiteMeasureTest_union X I J⟩

theorem generateFrom_finiteMeasureTest :
    generateFrom (range (finiteMeasureTest X)) = mX := by
  apply le_antisymm
  · exact generateFrom_le (fun s ⟨I, hI⟩ => hI ▸ measurableSet_finiteMeasureTest X I)
  · apply (generateFrom_natGeneratingSequence X).symm.le.trans
    apply generateFrom_mono
    rintro s ⟨i, rfl⟩
    exact ⟨{i}, by ext x; simp [finiteMeasureTest]⟩

/-- A countable determining test suitable for probability kernels. -/
theorem measure_eq_of_finiteMeasureTests (μ ν : Measure X) [IsFiniteMeasure μ]
    (h : ∀ I, μ (finiteMeasureTest X I) = ν (finiteMeasureTest X I)) : μ = ν := by
  apply ext_of_generate_finite (range (finiteMeasureTest X))
    (generateFrom_finiteMeasureTest X).symm (isPiSystem_finiteMeasureTest X)
  · rintro s ⟨I, rfl⟩
    exact h I
  · simpa [finiteMeasureTest] using h ∅

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_OrbitAverageErgodicity
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A countable convex-averaging criterion for ergodicity

If indicators in a determining family admit finite orbit averages converging
almost everywhere to constants, restriction to any invariant set is a scalar
multiple of the original probability. Evaluating on its complement gives the
zero-one law.
-/

noncomputable section

namespace PolycyclicRecognition

open MeasureTheory Set Filter
open scoped Topology

variable {G X : Type} [Group G] [MeasurableSpace X] [MeasurableSpace.CountablyGenerated X]
  [MulAction G X] [MeasurableConstSMul G X]
  (ν : Measure X) [IsProbabilityMeasure ν] [SMulInvariantMeasure G X ν]

theorem ergodicSMul_of_orbitAverages
    (hav : ∀ I : Finset ℕ, ∃ (A : ℕ → FiniteOrbitAverage G) (c : ℝ),
      ∀ᵐ x ∂ν, Tendsto
        (fun n => (A n).apply ((finiteMeasureTest X I).indicator (fun _ => (1 : ℝ))) x)
        atTop (𝓝 c)) : ErgodicSMul G X ν := by
  refine ⟨fun {s} hs hi => ?_⟩
  let : SMulInvariantMeasure G X (ν.restrict s) :=
    smulInvariantMeasure_restrict_ae ν s hs hi
  have he : ν.restrict s = (ν s) • ν := by
    apply measure_eq_of_finiteMeasureTests X
    intro I
    obtain ⟨A, c, hc⟩ := hav I
    have hcν := orbitAverage_indicator_limit_mass ν (finiteMeasureTest X I)
      (measurableSet_finiteMeasureTest X I) A c hc
    have hcs := orbitAverage_indicator_limit_mass (ν.restrict s) (finiteMeasureTest X I)
      (measurableSet_finiteMeasureTest X I) A c (ae_restrict_of_ae hc)
    simp only [measure_univ, mul_one] at hcν
    rw [hcs, Measure.smul_apply, smul_eq_mul, hcν, Measure.restrict_apply_univ]
    exact mul_comm _ _
  have hz : ν s * ν sᶜ = 0 := by
    have hh := congrArg (fun m : Measure X => m sᶜ) he
    simpa only [Measure.restrict_apply hs.compl, compl_inter_self, measure_empty,
      Measure.smul_apply, smul_eq_mul] using hh.symm
  rcases mul_eq_zero.mp hz with h | h
  · exact eventuallyConst_set.2 (Or.inr (measure_eq_zero_iff_ae_notMem.mp h))
  · apply eventuallyConst_set.2
    left
    simpa only [mem_compl_iff, not_not] using measure_eq_zero_iff_ae_notMem.mp h

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_LocallyCompactErgodicComponents
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_countable _root_.OAI.PolycyclicRecognition.finitelyGeneratedSubgroupIndex_countable _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Ergodic components for a locally compact group on a compact metric space -/

noncomputable section

namespace PolycyclicRecognition

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology

variable {G X : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]
  [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
  [StandardBorelSpace X] [Nonempty X] [MulAction G X] [ContinuousSMul G X]
  (μ : Measure X) [IsProbabilityMeasure μ] [SMulInvariantMeasure G X μ]

theorem invariantConditionalKernel_testAverages (I : Finset ℕ) :
    ∀ᵐ z ∂μ.map (invariantFactorMap G X),
      ∃ (A : ℕ → FiniteOrbitAverage G) (c : ℝ),
      ∀ᵐ y ∂invariantConditionalKernel (G := G) μ z, Tendsto
        (fun n => (A n).apply ((finiteMeasureTest X I).indicator (fun _ => (1 : ℝ))) y)
        atTop (𝓝 c) := by
  let f := (finiteMeasureTest X I).indicator (fun _ => (1 : ℝ))
  have hf : Measurable f := measurable_const.indicator (measurableSet_finiteMeasureTest X I)
  have hL : MemLp f 2 μ := (memLp_const (1 : ℝ)).indicator
    (measurableSet_finiteMeasureTest X I)
  obtain ⟨A, F, hF, hFi, hlim⟩ := exists_pointwise_haarOrbitAverages (G := G) μ f hL
  have ht := factorConditionalKernel_ae μ (invariantFactorMap G X)
    (measurable_invariantFactorMap G X)
    (measurableSet_tendsto_fun (fun n => (A n).measurable_apply f hf) hF) hlim
  have hc := factorConditionalKernel_fiber μ (invariantFactorMap G X)
    (measurable_invariantFactorMap G X) (fun z => F z.val)
    (measurable_invariantFactor_lift F hF hFi)
  filter_upwards [ht, hc] with z hz hcz
  refine ⟨A, F z.val, ?_⟩
  filter_upwards [hz, hcz] with y hy hcy
  change F y = F z.val at hcy
  simpa only [hcy] using hy

theorem invariantConditionalKernel_ergodic_ae :
    ∀ᵐ z ∂μ.map (invariantFactorMap G X),
      ErgodicSMul G X (invariantConditionalKernel (G := G) μ z) := by
  have ht := ae_all_iff.2 (invariantConditionalKernel_testAverages (G := G) μ)
  have hi := factorConditionalKernel_invariant_ae_dense μ (invariantFactorMap G X)
    (measurable_invariantFactorMap G X) invariantFactor_membership_smul
  filter_upwards [ht, hi] with z hz hzi
  have : IsProbabilityMeasure (invariantConditionalKernel (G := G) μ z) := by first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
  have : SMulInvariantMeasure G X (invariantConditionalKernel (G := G) μ z) := hzi
  exact ergodicSMul_of_orbitAverages (invariantConditionalKernel (G := G) μ z) hz

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_CompactErgodicDecomposition
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Ergodic decomposition on compact metrizable action spaces

Conditioning on the invariant sigma algebra gives ergodic components almost
everywhere. Repairing the null exceptional set on the factor preserves exact
orbit invariance of the component map.
-/

noncomputable section

namespace PolycyclicRecognition

open MeasureTheory ProbabilityTheory Set

variable {G X : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [SecondCountableTopology G]
  [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
  [StandardBorelSpace X] [MulAction G X] [ContinuousSMul G X]

theorem ergodicDecompositionInput_of_compactMetric : ErgodicDecompositionInput G X := by
  let : MeasurableSpace G := borel G
  let : BorelSpace G := ⟨rfl⟩
  intro μ hμ hi
  have : IsProbabilityMeasure μ := hμ
  have : SMulInvariantMeasure G X μ := hi
  have : Nonempty X := nonempty_of_isProbabilityMeasure μ
  have : IsProbabilityMeasure (μ.map (invariantFactorMap G X)) :=
    Measure.isProbabilityMeasure_map (measurable_invariantFactorMap G X).aemeasurable
  obtain ⟨k, hk, hgood, he⟩ := exists_kernel_conull_repair
    (μ.map (invariantFactorMap G X)) (invariantConditionalKernel (G := G) μ)
    (fun ν => ErgodicSMul G X ν) (invariantConditionalKernel_ergodic_ae (G := G) μ)
  let κ : X → Measure X := fun x => k (invariantFactorMap G X x)
  have hκ : Measurable κ := hk.comp (measurable_invariantFactorMap G X)
  have heκ : κ =ᵐ[μ] invariantConditionalMeasures (G := G) μ :=
    ae_of_ae_map (measurable_invariantFactorMap G X).aemeasurable he
  refine ⟨κ, fun x => hgood _, ?_, ?_⟩
  · intro g x
    ext s hs
    exact invariantFactor_observable (fun z => k z s)
      ((Measure.measurable_coe hs).comp hk) g x
  · intro s hs
    refine ⟨(Measure.measurable_coe hs).comp hκ, ?_⟩
    rw [invariantConditionalMeasures_barycenter (G := G) μ s hs]
    exact lintegral_congr_ae (heκ.mono (fun x hx => congrArg (fun ν : Measure X => ν s) hx.symm))

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_NormalizedPairErgodicDecomposition
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.inversePairCoupling_finiteOnCompacts _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Unconditional ergodic decomposition on normalized pair spaces -/

noncomputable section

namespace PolycyclicRecognition

open scoped NNReal

variable {G : Type} [Group G] [MetricSpace G] [ProperSpace G]
  [SecondCountableTopology G] [IsTopologicalGroup G] [IsIsometricSMul G G]
  {Λ : ℝ≥0} [MeasurableSpace (NormalizedPair G Λ)] [BorelSpace (NormalizedPair G Λ)]

theorem normalizedPair_ergodicDecomposition : ErgodicDecompositionInput G (NormalizedPair G Λ) := by
  let : MetricSpace (NormalizedPair G Λ) :=
    TopologicalSpace.metrizableSpaceMetric (NormalizedPair G Λ)
  exact ergodicDecompositionInput_of_compactMetric

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_UnitaryReducedVanishing
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The unitary formulation of reduced cocycle vanishing -/

noncomputable section

namespace PolycyclicRecognition

universe u v

open Set

variable {G : Type} [Group G] [TopologicalSpace G]

theorem UnitaryReducedVanishing.to_reduced
    (h : UnitaryReducedVanishing.{0, 0} G)
    (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [DistribMulAction G E] [IsIsometricSMul G E] [SMulCommClass G ℝ E] :
    ReducedCohomologyInput G E := by
  intro hfix hact b hbc hb Q hQ ε hε
  exact h E (isometricLinearAction (G := G) (E := E)) hfix hact b hbc hb Q hQ ε hε

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
attribute [-simp] _root_.OAI.PolycyclicRecognition.CartanFactorModel.realScaleProfile_apply _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
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

/-- Every nonempty bracket word has strictly positive sampling width. -/
theorem bracketWordExponent_pos_dup1
    {I : Type} [Fintype I] [DecidableEq I]
    (s : I → ℝ) (hs : ∀ i, 0 < s i) (w : FreeMagma I) :
    0 < bracketWordExponent s w := by
  induction w using FreeMagma.rec with
  | of i => simpa using hs i
  | mul u v hu hv =>
    change 0 < bracketWordExponent s (u * v)
    simpa only [bracketWordExponent_mul] using add_pos hu hv

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

set_option maxHeartbeats 1000000 in
/-- The finite word list supplies positive lower and upper widths and a
strict concentration gap. These constants are chosen from the actual
sampling polytope rather than assumed as geometric inputs. -/
theorem exists_sampling_gap [Nonempty (Fin M.letterCount)] :
    ∃ lo hi c : ℝ, 0 < lo ∧ 0 < hi ∧ 0 < c ∧
      (∀ w : M.wordList, lo ≤ M.boxCost T hunimod eW
        (M.samplingPolytope T hunimod eW) w ∧
        M.boxCost T hunimod eW (M.samplingPolytope T hunimod eW) w ≤ hi) ∧
      (M.bound : ℝ) * hi < c * lo := by
  classical
  let cost := M.boxCost T hunimod eW (M.samplingPolytope T hunimod eW)
  have hcost (w : M.wordList) : 0 < cost w :=
    bracketWordExponent_pos_dup1 _ (M.sampling_weightSupport_pos T hunimod eW) w
  have hne : (Finset.univ : Finset M.wordList).Nonempty := by
    let i : Fin M.letterCount := Classical.arbitrary _
    have hi : FreeMagma.of i ∈ M.wordList := by
      apply M.mem_wordList_of_eval_ne_zero
      simp only [evalBracketWord_of]
      intro hz
      have hq := M.letter_quotient i
      rw [hz, map_zero] at hq
      exact M.abelianBasis.ne_zero i hq.symm
    exact ⟨⟨FreeMagma.of i, hi⟩, Finset.mem_univ _⟩
  obtain ⟨u, _, hu⟩ := Finset.exists_min_image Finset.univ cost hne
  obtain ⟨v, _, hv⟩ := Finset.exists_max_image Finset.univ cost hne
  let c := ((M.bound : ℝ) * cost v + 1) / cost u
  have hc : 0 < c := div_pos
    (add_pos_of_nonneg_of_pos (mul_nonneg (Nat.cast_nonneg _) (hcost v).le) zero_lt_one)
    (hcost u)
  refine ⟨cost u, cost v, c, hcost u, hcost v, hc,
    fun w => ⟨hu w (Finset.mem_univ w), hv w (Finset.mem_univ w)⟩, ?_⟩
  dsimp only [c]
  rw [div_mul_cancel₀ _ (hcost u).ne']
  linarith

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanFixedSamplingGeometry
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finite_templateSymmetryGroup _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.instFiniteRootOffsetConeIndex _root_.OAI.PolycyclicRecognition.instFiniteSubtypeLinearEquivRealIdMemSubgroupLinearSupportSymmetryGroup _root_.OAI.PolycyclicRecognition.instNonemptyRootOffsetConeIndex _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
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
/-- Canonical-section lifts of the Euclidean contact points satisfy the
root-neighbor affinity hypotheses simultaneously for all generators. -/
theorem exists_sampling_contact_pivots :
    ∃ pivot : Fin M.letterCount → H, ∀ i,
      cartanHeightSection T H (heightProjection T.character (pivot i : L)) = pivot i ∧
      ‖eW (heightProjection T.character (pivot i : L))‖ = 1 ∧
      ((M.supportIn T hunimod eW).weight i).toContinuousLinearMap
        (eW (heightProjection T.character (pivot i : L))) =
          ‖((M.supportIn T hunimod eW).weight i).toContinuousLinearMap‖ ∧
      0 < M.weight i (pivot i) ∧
      eW (heightProjection T.character (pivot i : L)) ∈ M.samplingPolytope T hunimod eW ∧
      ∀ j, ((M.supportIn T hunimod eW).weight j).toContinuousLinearMap
          (eW (heightProjection T.character (pivot i : L))) =
            ‖((M.supportIn T hunimod eW).weight j).toContinuousLinearMap‖ →
        ∃ t : ℝ, 0 < t ∧ ((M.supportIn T hunimod eW).weight j).toContinuousLinearMap =
          t • ((M.supportIn T hunimod eW).weight i).toContinuousLinearMap := by
  classical
  let α := fun j => ((M.supportIn T hunimod eW).weight j).toContinuousLinearMap
  choose p hpn hpa hstrict using fun i =>
    exists_weight_contact_point (α i) (M.sampling_weight_ne_zero T hunimod eW i)
  let pivot := fun i => cartanHeightSection T H (eW.symm (p i))
  have hheight (i) : eW (heightProjection T.character (pivot i : L)) = p i := by
    simp only [pivot, cartanHeightSection_height, eW.apply_symm_apply]
  refine ⟨pivot, fun i => ⟨?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · simp only [pivot, cartanHeightSection_height]
  · rw [hheight]; exact hpn i
  · rw [hheight]; exact hpa i
  · have he : M.weight i (pivot i) = α i (p i) := rfl
    rw [he, hpa]
    exact norm_pos_iff.mpr (M.sampling_weight_ne_zero T hunimod eW i)
  · change ∀ j, α j (eW (heightProjection T.character (pivot i : L))) ≤ ‖α j‖
    rw [hheight]
    intro j
    calc
      α j (p i) ≤ |α j (p i)| := le_abs_self _
      _ ≤ ‖α j‖ * ‖p i‖ := (α j).le_opNorm _
      _ = ‖α j‖ := by rw [hpn, mul_one]
  · intro j hj
    rw [hheight] at hj
    by_contra hn
    exact (ne_of_lt (hstrict i (α j) (M.sampling_weight_ne_zero T hunimod eW j) hn)) hj

end PolycyclicRecognition.CartanWordModel

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

variable {W I : Type} [NormedAddCommGroup W] [NormedSpace ℝ W]
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

variable {W I : Type} [NormedAddCommGroup W] [NormedSpace ℝ W]
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

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanPublishedBoundedHeight
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_nonempty _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.unitaryCentralFixed_complete _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Bounded affine height from precisely published inputs -/

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
theorem exists_uniform_published_bounded_height
    (hExp : IsGroupExponential Exp) (hinj : Function.Injective Exp)
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
    (νD : Measure F.D.carrier) [νD.IsHaarMeasure] [SigmaFinite νD]
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
    (pivot : Fin M.letterCount → H)
    (hcanonical : ∀ i, cartanHeightSection T H (heightProjection T.character (pivot i)) = pivot i)
    (hunit : ∀ i, ‖eW (heightProjection T.character (pivot i))‖ = 1)
    (hcontact : ∀ i, ((M.supportIn T hunimod eW).weight i).toContinuousLinearMap
      (eW (heightProjection T.character (pivot i))) =
        ‖((M.supportIn T hunimod eW).weight i).toContinuousLinearMap‖)
    (hpositive : ∀ i, 0 < M.weight i (pivot i))
    {lo hi c B : ℝ} (hc : 0 ≤ c) (hhi : 0 ≤ hi) (hB : 0 ≤ B)
    (hcost : ∀ w : M.wordList, lo ≤ M.boxCost T hunimod eW Eall w ∧
      M.boxCost T hunimod eW Eall w ≤ hi)
    (hgap : (M.bound : ℝ) * hi < c * lo)
    (σchamber : Fin M.letterCount → Bool)
    (hσchamber : (weightChamber (fun j =>
      ((M.supportIn T hunimod eW).weight j).toContinuousLinearMap) σchamber).Nonempty)
    (hnz : ∀ i, (M.supportIn T hunimod eW).weight i ≠ 0)
    (sourceInputs : ∀ (i : Fin M.letterCount)
      (s : rootOffsetConeIndex (M.supportIn T hunimod eW) i),
      M.PolarConeModelInputs F (heightConePreimage T eW
        (rootOffsetCone (M.supportIn T hunimod eW) hnz i s)))
    (sourceDynkin : ∀ (i : Fin M.letterCount)
      (s : rootOffsetConeIndex (M.supportIn T hunimod eW) i)
      (J : NilpotentLieModel (M.coneWordIdeal (heightConePreimage T eW
        (rootOffsetCone (M.supportIn T hunimod eW) hnz i s)))),
      NilpotentDynkinExpansionInput J.modelSpace J.carrier)
    (targetInputs : ∀ (i : Fin M.letterCount)
      (A : templateSymmetryGroup (M.supportIn T hunimod eW))
      (s : rootOffsetConeIndex (M.supportIn T hunimod eW) i),
      M.PolarConeModelInputs F (heightConePreimage T eW
        (transformedPolarCone (rootOffsetCone (M.supportIn T hunimod eW) hnz i s) A.val)))
    (hweightB : ∀ i, (M.supportIn T hunimod eW).weightSupport Eall i ≤ B)
    (metricInput : GeodesicMetricExistenceInput)
    (raySource : ∀ (A : templateSymmetryGroup (M.supportIn T hunimod eW)) (i : Fin M.letterCount),
      M.PolarConeModelInputs F (positiveWeightRay
        ((((M.supportIn T hunimod eW).weight i).comp A.val.toLinearMap).comp
          (eW.toLinearMap.comp ((heightProjection T.character).comp H.subtype)))))
    (rayTarget : ∀ i : Fin M.letterCount,
      M.PolarConeModelInputs F (positiveWeightRay
        (((M.supportIn T hunimod eW).weight i).comp
          (eW.toLinearMap.comp ((heightProjection T.character).comp H.subtype)))))
    (raySourceDynkin : ∀ (A : templateSymmetryGroup (M.supportIn T hunimod eW)) (i : Fin M.letterCount)
      (Q : NilpotentLieModel ((cartanRootIdeal H) ⧸ M.coneWordIdeal (positiveWeightRay
        ((((M.supportIn T hunimod eW).weight i).comp A.val.toLinearMap).comp
          (eW.toLinearMap.comp ((heightProjection T.character).comp H.subtype)))))),
      NilpotentDynkinExpansionInput Q.modelSpace Q.carrier)
    (rayTargetDynkin : ∀ (i : Fin M.letterCount)
      (Q : NilpotentLieModel ((cartanRootIdeal H) ⧸ M.coneWordIdeal (positiveWeightRay
        (((M.supportIn T hunimod eW).weight i).comp
          (eW.toLinearMap.comp ((heightProjection T.character).comp H.subtype)))))),
      NilpotentDynkinExpansionInput Q.modelSpace Q.carrier)
    :
    ∃ (A : NormalizedPair G Λ → templateSymmetryGroup (M.supportIn T hunimod eW))
      (K : ℝ), 0 ≤ K ∧ ∀ p x,
      ‖(π (p.val.1 x)).toAdd - (A p).val (π x).toAdd‖ ≤ K := by
  obtain ⟨A, hsub⟩ := M.exists_published_sublinear_height T F hunimod eW
    hExp hinj realize haarN haarD dynkinN dynkinD chartN hchartN chartD hchartD m νD
    π hπExp hdec hvan hΛ hπ hpath bN γ hγ X hDnil hDletters bD₀ βD hβD
    aN hmN aD hmD rem hdim pivot hcanonical hunit hcontact hpositive
    hc hhi hB hcost hgap σchamber hσchamber hnz sourceInputs sourceDynkin targetInputs hweightB
  obtain ⟨K, hK, hb⟩ := M.uniform_normalized_affine_bound_of_published_inputs_and_sublinear
    T F hunimod eW π hπExp chartN hchartN chartD hchartD dynkinN dynkinD
    hExp realize haarN haarD metricInput bN γ hpath Kπ.coe_nonneg
    (fun x y => by simpa only [dist_eq_norm] using hπ.dist_le_mul x y)
    raySource rayTarget raySourceDynkin rayTargetDynkin A hsub
  exact ⟨A, K, hK, hb⟩

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanChosenSamplingHeight
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_nonempty _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.unitaryCentralFixed_complete _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.basisDynkinParameter_zero _root_.OAI.PolycyclicRecognition.bracketWordDifferential_mul _root_.OAI.PolycyclicRecognition.cartanWeightDerivation_apply_root _root_.OAI.PolycyclicRecognition.chartExponentialFlow_zero _root_.OAI.PolycyclicRecognition.derivationSemidirectHom_apply _root_.OAI.PolycyclicRecognition.exponentialHomOfDynkin_apply_exp _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.modelNilradicalLinearAction_apply _root_.OAI.PolycyclicRecognition.modelNilradicalRotation_apply _root_.OAI.PolycyclicRecognition.modelNilradicalRotation_mul _root_.OAI.PolycyclicRecognition.modelNilradicalRotation_one _root_.OAI.PolycyclicRecognition.nilshadowWeightDerivation_symm _root_.OAI.PolycyclicRecognition.nilshadowWeightOperator_symm _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Choosing the remaining concrete sampling data -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule MeasureTheory Filter Set
open scoped Manifold Topology ENNReal NNReal BigOperators

attribute [local instance] stationaryL2Action zeroMeanL2Action

variable {EG G W : Type} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
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
  {Λ : ℝ≥0}
  [MeasurableSpace (NormalizedPair G Λ)] [BorelSpace (NormalizedPair G Λ)]
  [MeasurableSpace C((Fin (finrank ℝ H) → ℝ), W)]
  [BorelSpace C((Fin (finrank ℝ H) → ℝ), W)]

set_option maxHeartbeats 1000000 in
/-- All finite-dimensional sampling choices are made in the proof. The
remaining hypotheses are the explicit published inputs and the actual
Cartan model and canonical height. -/
theorem exists_bounded_height_of_published_inputs
    (hExp : IsGroupExponential Exp) (hinj : Function.Injective Exp)
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
    (νD : Measure F.D.carrier) [νD.IsHaarMeasure] [SigmaFinite νD]
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
    (rem : RemezPolynomialInput)
    (sourceInputs : ∀ (i : Fin M.letterCount)
      (s : rootOffsetConeIndex (M.supportIn T hunimod eW) i),
      M.PolarConeModelInputs F (heightConePreimage T eW
        (rootOffsetCone (M.supportIn T hunimod eW) (M.sampling_linear_weight_ne_zero T hunimod eW) i s)))
    (sourceDynkin : ∀ (i : Fin M.letterCount)
      (s : rootOffsetConeIndex (M.supportIn T hunimod eW) i)
      (J : NilpotentLieModel (M.coneWordIdeal (heightConePreimage T eW
        (rootOffsetCone (M.supportIn T hunimod eW) (M.sampling_linear_weight_ne_zero T hunimod eW) i s)))),
      NilpotentDynkinExpansionInput J.modelSpace J.carrier)
    (targetInputs : ∀ (i : Fin M.letterCount)
      (A : templateSymmetryGroup (M.supportIn T hunimod eW))
      (s : rootOffsetConeIndex (M.supportIn T hunimod eW) i),
      M.PolarConeModelInputs F (heightConePreimage T eW
        (transformedPolarCone (rootOffsetCone (M.supportIn T hunimod eW) (M.sampling_linear_weight_ne_zero T hunimod eW) i s) A.val)))
    (metricInput : GeodesicMetricExistenceInput)
    (raySource : ∀ (A : templateSymmetryGroup (M.supportIn T hunimod eW)) (i : Fin M.letterCount),
      M.PolarConeModelInputs F (positiveWeightRay
        ((((M.supportIn T hunimod eW).weight i).comp A.val.toLinearMap).comp
          (eW.toLinearMap.comp ((heightProjection T.character).comp H.subtype)))))
    (rayTarget : ∀ i : Fin M.letterCount,
      M.PolarConeModelInputs F (positiveWeightRay
        (((M.supportIn T hunimod eW).weight i).comp
          (eW.toLinearMap.comp ((heightProjection T.character).comp H.subtype)))))
    (raySourceDynkin : ∀ (A : templateSymmetryGroup (M.supportIn T hunimod eW)) (i : Fin M.letterCount)
      (Q : NilpotentLieModel ((cartanRootIdeal H) ⧸ M.coneWordIdeal (positiveWeightRay
        ((((M.supportIn T hunimod eW).weight i).comp A.val.toLinearMap).comp
          (eW.toLinearMap.comp ((heightProjection T.character).comp H.subtype)))))),
      NilpotentDynkinExpansionInput Q.modelSpace Q.carrier)
    (rayTargetDynkin : ∀ (i : Fin M.letterCount)
      (Q : NilpotentLieModel ((cartanRootIdeal H) ⧸ M.coneWordIdeal (positiveWeightRay
        (((M.supportIn T hunimod eW).weight i).comp
          (eW.toLinearMap.comp ((heightProjection T.character).comp H.subtype)))))),
      NilpotentDynkinExpansionInput Q.modelSpace Q.carrier)
    :
    ∃ (A : NormalizedPair G Λ → templateSymmetryGroup (M.supportIn T hunimod eW))
      (K : ℝ), 0 ≤ K ∧ ∀ p x,
      ‖(π (p.val.1 x)).toAdd - (A p).val (π x).toAdd‖ ≤ K := by
  classical
  let bN := finBasis ℝ (cartanRootIdeal H)
  obtain ⟨γ, hγ, _⟩ := M.exists_maximizing_box_basis T hunimod eW bN
    (M.samplingPolytope T hunimod eW)
  let bD := finBasis ℝ H
  obtain ⟨d, βD, hDnil, hDletters, hβD⟩ := exists_nilpotent_basis_word_choices bD
  let : LieRing.IsNilpotent (GroupLieAlgebra (𝓘(ℝ, F.N.modelSpace)) F.N.carrier) :=
    F.N.tangent_nilpotent (cartanRootIdeal_nilpotent H T)
  let : LieRing.IsNilpotent (GroupLieAlgebra (𝓘(ℝ, F.D.modelSpace)) F.D.carrier) :=
    F.D.tangent_nilpotent inferInstance
  obtain ⟨cN, hcN⟩ := LieModule.IsNilpotent.nilpotent ℝ
    (GroupLieAlgebra (𝓘(ℝ, F.N.modelSpace)) F.N.carrier)
    (GroupLieAlgebra (𝓘(ℝ, F.N.modelSpace)) F.N.carrier)
  obtain ⟨cD, hcD⟩ := LieModule.IsNilpotent.nilpotent ℝ
    (GroupLieAlgebra (𝓘(ℝ, F.D.modelSpace)) F.D.carrier)
    (GroupLieAlgebra (𝓘(ℝ, F.D.modelSpace)) F.D.carrier)
  obtain ⟨aN, _, haN⟩ := dynkinN F.ExpN F.isExpN cN hcN 2
  obtain ⟨aD, _, haD⟩ := dynkinD F.ExpD F.isExpD cD hcD 2
  have hmN : ∀ x y, F.ExpN (finiteDynkinPolynomial aN ![x, y]) = F.ExpN x * F.ExpN y := by
    intro x y
    simpa using (haN ![x, y]).symm
  have hmD : ∀ x y, F.ExpD (finiteDynkinPolynomial aD ![x, y]) = F.ExpD x * F.ExpD y := by
    intro x y
    simpa using (haD ![x, y]).symm
  obtain ⟨lo, hi, c, hlo, hhi, hc, hcost, hgap⟩ := M.exists_sampling_gap T hunimod eW
  obtain ⟨pivot, hpivot⟩ := M.exists_sampling_contact_pivots T hunimod eW
  let α := fun i => ((M.supportIn T hunimod eW).weight i).toContinuousLinearMap
  obtain ⟨v, hv⟩ := (dense_genericWeightDirections α (M.sampling_weight_ne_zero T hunimod eW)).nonempty
  obtain ⟨σ, hσ, _⟩ := exists_incident_chamber_of_generic α 0 hv
  let B := ∑ i, ‖α i‖
  have hB : 0 ≤ B := Finset.sum_nonneg (fun i _ => norm_nonneg _)
  have hweightB : ∀ i, (M.supportIn T hunimod eW).weightSupport
      (M.samplingPolytope T hunimod eW) i ≤ B := by
    intro i
    rw [M.sampling_weightSupport_eq T hunimod eW]
    exact Finset.single_le_sum (fun j _ => norm_nonneg (α j)) (Finset.mem_univ i)
  have hdim : 1 ≤ finrank ℝ (cartanRootIdeal H) := by
    have hn : 0 < finrank ℝ (cartanRootIdeal H) := Fin.pos_iff_nonempty.mpr inferInstance
    omega
  exact M.exists_uniform_published_bounded_height T F hunimod eW
    hExp hinj realize haarN haarD dynkinN dynkinD chartN hchartN chartD hchartD m νD
    π hπExp hdec hvan hΛ hπ hpath bN γ hγ (fun i => bD i) hDnil hDletters bD βD hβD
    aN hmN aD hmD rem hdim pivot (fun i => (hpivot i).1) (fun i => (hpivot i).2.1)
    (fun i => (hpivot i).2.2.1) (fun i => (hpivot i).2.2.2.1)
    hc.le hhi.le hB hcost hgap σ hσ.1 (M.sampling_linear_weight_ne_zero T hunimod eW)
    sourceInputs sourceDynkin targetInputs hweightB metricInput
    raySource rayTarget raySourceDynkin rayTargetDynkin

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanNontrivialHeight
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finite_templateSymmetryGroup _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.instFiniteRootOffsetConeIndex _root_.OAI.PolycyclicRecognition.instFiniteSubtypeLinearEquivRealIdMemSubgroupLinearSupportSymmetryGroup _root_.OAI.PolycyclicRecognition.instNonemptyRootOffsetConeIndex _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Nontrivial height forces the nonzero sampling branch -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule

variable {L W : Type} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {H : LieSubalgebra ℝ L} [H.IsCartanSubalgebra] (M : CartanWordModel H)
  {a : ℕ} (T : TriangularAdjoint L a)
  (hunimod : ∀ x : L, LinearMap.trace ℝ L (ad ℝ L x) = 0)
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)

set_option maxHeartbeats 1000000 in
include T hunimod eW in
omit [FiniteDimensional ℝ W] in
/-- With no generator weights, separation makes the height space trivial. -/
theorem nonempty_letters_of_nontrivial_height [Nontrivial W] :
    Nonempty (Fin M.letterCount) := by
  classical
  by_contra hn
  let : IsEmpty (Fin M.letterCount) := not_nonempty_iff.mp hn
  obtain ⟨w, hw⟩ := exists_ne (0 : W)
  exact hw ((M.supportIn T hunimod eW).separates w (fun i => isEmptyElim i))

set_option maxHeartbeats 1000000 in
/-- A retained generator gives positive dimension of the root ideal. -/
theorem nonempty_root_coordinates_of_nonempty_letters
    [Nonempty (Fin M.letterCount)] :
    Nonempty (Fin (finrank ℝ (cartanRootIdeal H))) := by
  obtain ⟨i⟩ := ‹Nonempty (Fin M.letterCount)›
  have hi : M.letter i ≠ 0 := by
    intro hz
    have h := M.letter_quotient i
    rw [hz, map_zero] at h
    exact M.abelianBasis.ne_zero i h.symm
  let : Nontrivial (cartanRootIdeal H) := nontrivial_of_ne (M.letter i) 0 hi
  exact Fin.pos_iff_nonempty.mp (Module.finrank_pos (R := ℝ) (M := cartanRootIdeal H))

end PolycyclicRecognition.CartanWordModel

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

variable {E G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace G] [ChartedSpace E G] [Group G]
  [LieGroup (𝓘(ℝ, E)) ⊤ G]
  {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W]

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

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_IntrinsicHeightKernel
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.CartanFactorModel.heightRay_zero _root_.OAI.PolycyclicRecognition.CartanFactorModel.realScaleProfile_apply _root_.OAI.PolycyclicRecognition.CartanFactorModel.sampledProbeProfile_apply _root_.OAI.PolycyclicRecognition.cartanWeightDerivation_apply_root _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.modelNilradicalLinearAction_apply _root_.OAI.PolycyclicRecognition.modelNilradicalRotation_apply _root_.OAI.PolycyclicRecognition.modelNilradicalRotation_mul _root_.OAI.PolycyclicRecognition.modelNilradicalRotation_one _root_.OAI.PolycyclicRecognition.nilshadowWeightDerivation_symm _root_.OAI.PolycyclicRecognition.nilshadowWeightOperator_symm _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The closed nilpotent height kernel without a global ambient chart

A product of exponential curves supplies a smooth height section. The inverse
function theorem identifies the integrated nilpotent model locally with the
kernel. The section retracts the ambient group onto the actual kernel, so
simple connectedness upgrades that local identification to a closed embedding.
-/

noncomputable section
namespace PolycyclicRecognition

open Set Filter
open scoped Manifold ContDiff Topology

variable {E G W : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MetricSpace G] [ChartedSpace E G] [Group G]
  [LieGroup (𝓘(ℝ, E)) ⊤ G] [SimplyConnectedSpace G]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, E)) G) a)
  (q : HeightSpace T.character ≃ₗ[ℝ] W)
  (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G) (hExp : IsGroupExponential Exp)
  (π : G →* Multiplicative W) (hπ : Continuous π)
  (hπExp : ∀ v, (π (Exp v)).toAdd = q (heightProjection T.character v))

include q hExp hπ hπExp in
theorem exists_closed_intrinsic_height_kernel :
    ∃ (N : NilpotentLieModel T.kernelIdeal)
      (ExpN : GroupLieAlgebra (𝓘(ℝ, N.modelSpace)) N.carrier → N.carrier),
      IsGroupExponential ExpN ∧
      ∃ ι : N.carrier →* G, Topology.IsClosedEmbedding ι ∧
        ContMDiff (𝓘(ℝ, N.modelSpace)) (𝓘(ℝ, E)) ∞ ι ∧
        (∀ x : T.kernelIdeal, ι (ExpN (N.equiv x)) = Exp x) ∧
        Set.range ι = (π.ker : Set G) := by
  obtain ⟨N⟩ := nilpotentPublishedInputs.existsModel T.kernelIdeal T.kernelIdeal_nilpotent
  let : IsTopologicalGroup G := topologicalGroup_of_lieGroup (𝓘(ℝ, E)) ⊤
  let : IsTopologicalGroup N.carrier :=
    topologicalGroup_of_lieGroup (𝓘(ℝ, N.modelSpace)) ⊤
  obtain ⟨ExpN, hExpN, cN, hcN⟩ :=
    N.exists_exponential_chart T.kernelIdeal_nilpotent
      (nilpotentPublishedInputs.haar T.kernelIdeal N)
  let j := T.kernelIdeal.incl.comp N.equiv.symm.toLieHom
  have hj : Function.Injective j := Subtype.val_injective.comp N.equiv.symm.injective
  obtain ⟨ι, hιsmooth, hιdiff, hιExp⟩ :=
    nilpotentLieIntegrationInput_of_smooth (nilpotentSmoothIntegrationInput T.kernelIdeal N)
      inferInstance (N.tangent_nilpotent T.kernelIdeal_nilpotent) j ExpN Exp hExpN hExp
  let d : E →ₗ[ℝ] W := q.toLinearMap.comp (heightProjection T.character)
  have hd : Function.Surjective d :=
    q.surjective.comp (heightProjection_surjective T.character)
  obtain ⟨s, l, hs, hs0, hsπ, hsl, hdl⟩ :=
    exists_smooth_section_of_exponential_linear_quotient hExp d hd π hπExp
  let jc : N.modelSpace →L[ℝ] E := j.toLinearMap.toContinuousLinearMap
  let dc : E →L[ℝ] W := d.toContinuousLinearMap
  have hjrange : LinearMap.range jc.toLinearMap = LinearMap.ker dc.toLinearMap := by
    ext x
    constructor
    · rintro ⟨v, rfl⟩
      change q (heightProjection T.character (j v)) = 0
      have hz : heightProjection T.character (j v) = 0 :=
        (Submodule.Quotient.mk_eq_zero _).mpr (N.equiv.symm v).property
      rw [hz, map_zero]
    · intro hx
      have hz : heightProjection T.character x = 0 := by
        apply q.injective
        exact (show d x = 0 from hx).trans (map_zero q).symm
      have hxK : x ∈ T.kernelIdeal := (Submodule.Quotient.mk_eq_zero _).mp hz
      refine ⟨N.equiv ⟨x, hxK⟩, ?_⟩
      change j (N.equiv ⟨x, hxK⟩) = x
      exact congrArg Subtype.val (N.equiv.symm_apply_apply ⟨x, hxK⟩)
  have hdcl : dc.comp l = ContinuousLinearMap.id ℝ W := by
    ext w
    exact LinearMap.congr_fun hdl w
  have hιj : HasMFDerivAt (𝓘(ℝ, N.modelSpace)) (𝓘(ℝ, E)) ι 1 jc := by
    apply (hιsmooth.mdifferentiable (by simp) 1).hasMFDerivAt.congr_mfderiv
    ext v
    exact hιdiff v
  have hcoordinates := kernel_product_local_coordinates ι s 1 hιsmooth hs
    (map_one ι) hs0 jc dc l hιj hsl hj hjrange hdcl
  have hιker (n : N.carrier) : π (ι n) = 1 := by
    obtain ⟨v, hv⟩ := cN.surjective n
    rw [hcN] at hv
    rw [← hv, hιExp]
    apply Multiplicative.ext
    change (π (Exp (j v))).toAdd = 0
    have hz : heightProjection T.character (j v) = 0 :=
      (Submodule.Quotient.mk_eq_zero _).mpr (N.equiv.symm v).property
    rw [hπExp, hz, map_zero]
  let sectionMap : C(Multiplicative W, G) := ⟨fun w => s w.toAdd, hs.continuous⟩
  have hsection (w : Multiplicative W) : π (sectionMap w) = w :=
    Multiplicative.ext (hsπ w.toAdd)
  have hsection1 : sectionMap 1 = 1 := hs0
  let : LocallyPathConnectedSpace N.carrier :=
    ChartedSpace.locallyPathConnectedSpace N.modelSpace N.carrier
  have hinj : ∃ U ∈ 𝓝 ((1 : N.carrier), (1 : Multiplicative W)),
      InjOn (fun p : N.carrier × Multiplicative W => ι p.1 * sectionMap p.2) U :=
    hcoordinates.1
  have hmap : map (fun p : N.carrier × Multiplicative W => ι p.1 * sectionMap p.2)
      (𝓝 (1, 1)) = 𝓝 (1 : G) := hcoordinates.2
  obtain ⟨hclosed, hrange⟩ := closedEmbedding_kernel_of_split_coordinates
    π hπ sectionMap hsection hsection1 ι hιker hinj hmap
  refine ⟨N, ExpN, hExpN, ι, hclosed, hιsmooth, ?_, hrange⟩
  intro x
  simpa [j] using hιExp (N.equiv x)

include q hExp hπ hπExp in
/-- The exponential is injective on the entire canonical height kernel. -/
theorem exponential_injOn_intrinsic_height_kernel :
    InjOn Exp (T.kernelIdeal : Set (GroupLieAlgebra (𝓘(ℝ, E)) G)) := by
  obtain ⟨N, ExpN, hExpN, ι, hι, _, hcompat, _⟩ :=
    exists_closed_intrinsic_height_kernel T q Exp hExp π hπ hπExp
  obtain ⟨cN, hcN⟩ := ((nilpotentPublishedInputs.haar T.kernelIdeal N).2
    ExpN hExpN (N.tangent_nilpotent T.kernelIdeal_nilpotent)).1
  intro x hx y hy hxy
  have he : ExpN (N.equiv ⟨x, hx⟩) = ExpN (N.equiv ⟨y, hy⟩) := by
    apply hι.injective
    rw [hcompat, hcompat]
    exact hxy
  have hn : N.equiv ⟨x, hx⟩ = N.equiv ⟨y, hy⟩ := by
    apply cN.injective
    simpa only [hcN] using he
  exact congrArg Subtype.val (N.equiv.injective hn)

include q hExp hπ hπExp in
/-- A kernel point has no other exponential preimage in the ambient algebra. -/
theorem exponential_eq_of_mem_intrinsic_height_kernel
    {x y : GroupLieAlgebra (𝓘(ℝ, E)) G} (hx : x ∈ T.kernelIdeal)
    (he : Exp x = Exp y) : x = y := by
  have hx0 : heightProjection T.character x = 0 :=
    (Submodule.Quotient.mk_eq_zero _).mpr hx
  have hy0 : heightProjection T.character y = 0 := by
    apply q.injective
    rw [← hπExp, ← he, hπExp, hx0, map_zero]
  exact exponential_injOn_intrinsic_height_kernel T q Exp hExp π hπ hπExp hx
    ((Submodule.Quotient.mk_eq_zero _).mp hy0) he

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_ClosedIntegrationInHeightKernel
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Closed integration of ideals inside the canonical height kernel -/

noncomputable section
namespace PolycyclicRecognition

open scoped Manifold ContDiff

variable {E G W : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MetricSpace G] [ChartedSpace E G] [Group G]
  [LieGroup (𝓘(ℝ, E)) ⊤ G] [SimplyConnectedSpace G]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, E)) G) a)
  (q : HeightSpace T.character ≃ₗ[ℝ] W)
  (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G) (hExp : IsGroupExponential Exp)
  (π : G →* Multiplicative W) (hπ : Continuous π)
  (hπExp : ∀ v, (π (Exp v)).toAdd = q (heightProjection T.character v))

include q hExp hπ hπExp in
theorem exists_closed_integration_in_height_kernel
    (I : LieIdeal ℝ (GroupLieAlgebra (𝓘(ℝ, E)) G)) (hI : I ≤ T.kernelIdeal)
    (hnil : LieRing.IsNilpotent I) (N : NilpotentLieModel I)
    (ExpN : GroupLieAlgebra (𝓘(ℝ, N.modelSpace)) N.carrier → N.carrier)
    (hExpN : IsGroupExponential ExpN) :
    ∃ ι : N.carrier →* G, Topology.IsClosedEmbedding ι ∧
      ContMDiff (𝓘(ℝ, N.modelSpace)) (𝓘(ℝ, E)) ∞ ι ∧
      ∀ x : I, ι (ExpN (N.equiv x)) = Exp x := by
  obtain ⟨K, ExpK, hExpK, κ, hκ, hκsmooth, heκ, _⟩ :=
    exists_closed_intrinsic_height_kernel T q Exp hExp π hπ hπExp
  obtain ⟨cK, hcK⟩ := ((nilpotentPublishedInputs.haar T.kernelIdeal K).2
    ExpK hExpK (K.tangent_nilpotent T.kernelIdeal_nilpotent)).1
  obtain ⟨cN, hcN⟩ := ((nilpotentPublishedInputs.haar I N).2
    ExpN hExpN (N.tangent_nilpotent hnil)).1
  let j := K.equiv.toLieHom.comp ((LieIdeal.inclusion hI).comp N.equiv.symm.toLieHom)
  have hj : Function.Injective j := K.equiv.injective.comp
    ((LieIdeal.inclusion_injective hI).comp N.equiv.symm.injective)
  obtain ⟨f, hf, hfsmooth, _, hef, _⟩ := exists_closed_integration
    (nilpotentLieIntegrationInput_of_smooth
      (nilpotentSmoothIntegrationInput (E := K.modelSpace) (G := K.carrier) I N))
    (N.tangent_nilpotent hnil) j hj ExpN ExpK hExpN hExpK cN hcN cK hcK
  refine ⟨κ.comp f, hκ.comp hf, hκsmooth.comp hfsmooth, ?_⟩
  intro x
  change κ (f (ExpN (N.equiv x))) = Exp x
  rw [hef]
  change κ (ExpK (K.equiv ((LieIdeal.inclusion hI) (N.equiv.symm (N.equiv x))))) = Exp x
  rw [N.equiv.symm_apply_apply, heκ]
  rfl

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_ClosedIntegrationOverHeight
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Closed nilpotent integration over the canonical height quotient

A nilpotent subalgebra projecting onto height has a closed integrated image.
The proof compares its kernel with the constructed nilpotent height kernel
and uses section coordinates for the remaining directions.
-/

noncomputable section
namespace PolycyclicRecognition

open Set
open scoped Manifold ContDiff

variable {E G W : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MetricSpace G] [ChartedSpace E G] [Group G]
  [LieGroup (𝓘(ℝ, E)) ⊤ G] [SimplyConnectedSpace G]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, E)) G) a)
  (q : HeightSpace T.character ≃ₗ[ℝ] W)
  (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G) (hExp : IsGroupExponential Exp)
  (π : G →* Multiplicative W) (hπ : Continuous π)
  (hπExp : ∀ v, (π (Exp v)).toAdd = q (heightProjection T.character v))

include q hExp hπ hπExp in
theorem exists_closed_nilpotent_integration_over_height
    (L : Type) [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
    (N : NilpotentLieModel L) (hnil : LieRing.IsNilpotent L)
    (j : GroupLieAlgebra (𝓘(ℝ, N.modelSpace)) N.carrier →ₗ⁅ℝ⁆
      GroupLieAlgebra (𝓘(ℝ, E)) G) (hj : Function.Injective j)
    (hsurj : Function.Surjective
      ((q.toLinearMap.comp (heightProjection T.character)).comp j.toLinearMap)) :
    ∃ ι : N.carrier →* G, Topology.IsClosedEmbedding ι ∧
      ContMDiff (𝓘(ℝ, N.modelSpace)) (𝓘(ℝ, E)) ∞ ι ∧
      ∀ (ExpN : GroupLieAlgebra (𝓘(ℝ, N.modelSpace)) N.carrier → N.carrier),
        IsGroupExponential ExpN → ∀ x, ι (ExpN x) = Exp (j x) := by
  let : IsTopologicalGroup G := topologicalGroup_of_lieGroup (𝓘(ℝ, E)) ⊤
  let : IsTopologicalGroup N.carrier :=
    topologicalGroup_of_lieGroup (𝓘(ℝ, N.modelSpace)) ⊤
  obtain ⟨ExpN, hExpN, cN, hcN⟩ := N.exists_exponential_chart hnil
    (nilpotentPublishedInputs.haar L N)
  obtain ⟨ι, hι, hdι, heι⟩ :=
    nilpotentLieIntegrationInput_of_smooth (nilpotentSmoothIntegrationInput L N)
      inferInstance (N.tangent_nilpotent hnil) j ExpN Exp hExpN hExp
  obtain ⟨K, ExpK, hExpK, κ, hκ, _, heκ, hrκ⟩ :=
    exists_closed_intrinsic_height_kernel T q Exp hExp π hπ hπExp
  let : IsTopologicalGroup K.carrier :=
    topologicalGroup_of_lieGroup (𝓘(ℝ, K.modelSpace)) ⊤
  obtain ⟨cK, hcK⟩ := ((nilpotentPublishedInputs.haar T.kernelIdeal K).2
    ExpK hExpK (K.tangent_nilpotent T.kernelIdeal_nilpotent)).1
  let d := (q.toLinearMap.comp (heightProjection T.character)).comp j.toLinearMap
  have hquot (x : N.modelSpace) : (π (ι (ExpN x))).toAdd = d x := by
    exact (congrArg (fun g : G => (π g).toAdd) (heι x)).trans (hπExp (j x))
  obtain ⟨s, hs, _, hsright⟩ :=
    exists_continuous_section_of_exponential_linear_quotient hExpN d hsurj
      (π.comp ι) hquot
  let sectionN : C(Multiplicative W, N.carrier) := ⟨fun w => s w.toAdd, hs⟩
  have hsN (w : Multiplicative W) : π (ι (sectionN w)) = w :=
    Multiplicative.ext (hsright w.toAdd)
  let eN : d.ker ≃ₜ (π.comp ι).ker := cN.subtype (fun x => by
    change d x = 0 ↔ π (ι (cN x)) = 1
    rw [hcN]
    constructor
    · intro hx
      apply Multiplicative.ext
      exact (hquot x).trans hx
    · intro hx
      exact (hquot x).symm.trans (congrArg Multiplicative.toAdd hx))
  let eK : K.modelSpace ≃ₜ π.ker := cK.trans (kernelRealization π κ hκ hrκ).toHomeomorph
  let jK : d.ker →ₗ[ℝ] K.modelSpace :=
    K.equiv.toLinearMap.comp
      ((j.toLinearMap.comp d.ker.subtype).codRestrict T.kernelIdeal.toSubmodule (by
        intro x
        apply (Submodule.Quotient.mk_eq_zero _).mp
        apply q.injective
        exact (show d x = 0 from x.property).trans (map_zero q).symm))
  have hjK : Function.Injective jK := by
    intro x y h
    apply Subtype.ext
    apply hj
    have hh := K.equiv.injective h
    exact congrArg Subtype.val hh
  have hclosedKernel : Topology.IsClosedEmbedding (splitKernelHom ι π) := by
    apply isClosedEmbedding_of_compatible_charts eN eK jK hjK
    intro x
    apply Subtype.ext
    change ι (cN x) = κ (cK (jK x))
    have hh := heκ (K.equiv.symm (jK x))
    have hh' : κ (ExpK (jK x)) = Exp (K.equiv.symm (jK x)).val :=
      (congrArg (fun y : GroupLieAlgebra (𝓘(ℝ, K.modelSpace)) K.carrier => κ (ExpK y))
        (K.equiv.apply_symm_apply (jK x))).symm.trans hh
    have hcancel : (K.equiv.symm (jK x)).val = j x :=
      congrArg Subtype.val (K.equiv.symm_apply_apply _)
    exact ((congrArg ι (hcN x)).trans (heι x)).trans
      (((congrArg κ (hcK (jK x))).trans hh').trans (congrArg Exp hcancel)).symm
  refine ⟨ι, closedEmbedding_of_splitKernel ι hι.continuous π hπ sectionN hsN hclosedKernel,
    hι, ?_⟩
  intro ExpN' hExpN' x
  rw [← hExpN.unique hExpN']
  exact heι x

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_IntrinsicCartanFactorModel
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.CartanFactorModel.heightRay_zero _root_.OAI.PolycyclicRecognition.CartanFactorModel.realScaleProfile_apply _root_.OAI.PolycyclicRecognition.CartanFactorModel.sampledProbeProfile_apply _root_.OAI.PolycyclicRecognition.cartanWeightDerivation_apply_root _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.modelNilradicalLinearAction_apply _root_.OAI.PolycyclicRecognition.modelNilradicalRotation_apply _root_.OAI.PolycyclicRecognition.modelNilradicalRotation_mul _root_.OAI.PolycyclicRecognition.modelNilradicalRotation_one _root_.OAI.PolycyclicRecognition.nilshadowWeightDerivation_symm _root_.OAI.PolycyclicRecognition.nilshadowWeightOperator_symm _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Cartan factors from the intrinsic height kernel

Both nilpotent factor inclusions are closed without the ambient exponential
chart. Their product and exact overlap follow from local multiplication
coordinates and uniqueness of exponential preimages in the height kernel.
-/

noncomputable section
namespace PolycyclicRecognition

open Set
open scoped Manifold ContDiff

variable {E G W : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MetricSpace G] [ChartedSpace E G] [Group G]
  [LieGroup (𝓘(ℝ, E)) ⊤ G] [SimplyConnectedSpace G]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, E)) G) a)
  (q : HeightSpace T.character ≃ₗ[ℝ] W)
  (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G) (hExp : IsGroupExponential Exp)
  (π : G →* Multiplicative W) (hπ : Continuous π)
  (hπExp : ∀ v, (π (Exp v)).toAdd = q (heightProjection T.character v))
  (H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, E)) G)) [H.IsCartanSubalgebra]

set_option maxHeartbeats 1000000 in
include q hExp hπ hπExp in
theorem nonempty_intrinsic_cartanFactorModel : Nonempty (CartanFactorModel H Exp) := by
  let : IsTopologicalGroup G := topologicalGroup_of_lieGroup (𝓘(ℝ, E)) ⊤
  have hn := cartanRootIdeal_nilpotent H T
  obtain ⟨N⟩ := nilpotentPublishedInputs.existsModel (cartanRootIdeal H) hn
  obtain ⟨D⟩ := nilpotentPublishedInputs.existsModel H inferInstance
  let : IsTopologicalGroup N.carrier :=
    topologicalGroup_of_lieGroup (𝓘(ℝ, N.modelSpace)) ⊤
  let : IsTopologicalGroup D.carrier :=
    topologicalGroup_of_lieGroup (𝓘(ℝ, D.modelSpace)) ⊤
  let : LocallyCompactSpace N.carrier := ChartedSpace.locallyCompactSpace N.modelSpace N.carrier
  let : LocallyCompactSpace D.carrier := ChartedSpace.locallyCompactSpace D.modelSpace D.carrier
  obtain ⟨ExpN, hExpN, cN, hcN⟩ := N.exists_exponential_chart hn
    (nilpotentPublishedInputs.haar (cartanRootIdeal H) N)
  obtain ⟨ExpD, hExpD, cD, hcD⟩ := D.exists_exponential_chart inferInstance
    (nilpotentPublishedInputs.haar H D)
  obtain ⟨ι, hι, hιsmooth, heι⟩ := exists_closed_integration_in_height_kernel T q Exp hExp
    π hπ hπExp (cartanRootIdeal H) (cartanRootIdeal_le_kernel H T) hn N ExpN hExpN
  let jD := H.incl.comp D.equiv.symm.toLieHom
  have hjD : Function.Injective jD := Subtype.val_injective.comp D.equiv.symm.injective
  have hsurj : Function.Surjective
      ((q.toLinearMap.comp (heightProjection T.character)).comp jD.toLinearMap) := by
    exact q.surjective.comp ((cartan_height_surjective T H).comp D.equiv.symm.surjective)
  obtain ⟨κ, hκ, hκsmooth, heκall⟩ := exists_closed_nilpotent_integration_over_height T q Exp
    hExp π hπ hπExp H D inferInstance jD hjD hsurj
  have heκ (x : H) : κ (ExpD (D.equiv x)) = Exp x := by
    simpa [jD] using heκall ExpD hExpD (D.equiv x)
  have hiExp (x : N.modelSpace) : ι (ExpN x) = Exp ((cartanRootIdeal H).incl (N.equiv.symm x)) := by
    change ι (ExpN x) = Exp (N.equiv.symm x)
    exact (congrArg (fun y : GroupLieAlgebra (𝓘(ℝ, N.modelSpace)) N.carrier =>
      ι (ExpN y)) (N.equiv.apply_symm_apply x)).symm.trans (heι (N.equiv.symm x))
  have hkExp (x : D.modelSpace) : κ (ExpD x) = Exp (H.incl (D.equiv.symm x)) := by
    change κ (ExpD x) = Exp (D.equiv.symm x)
    exact (congrArg (fun y : GroupLieAlgebra (𝓘(ℝ, D.modelSpace)) D.carrier =>
      κ (ExpD y)) (D.equiv.apply_symm_apply x)).symm.trans (heκ (D.equiv.symm x))
  have hiRange : Set.range ι = Exp '' (cartanRootIdeal H : Set (GroupLieAlgebra (𝓘(ℝ, E)) G)) := by
    ext g
    constructor
    · rintro ⟨n, rfl⟩
      obtain ⟨x, hx⟩ := cN.surjective n
      rw [hcN] at hx
      exact ⟨N.equiv.symm x, (N.equiv.symm x).property, (hiExp x).symm.trans (congrArg ι hx)⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨ExpN (N.equiv ⟨x, hx⟩), heι ⟨x, hx⟩⟩
  have hkRange : Set.range κ = Exp '' (H : Set (GroupLieAlgebra (𝓘(ℝ, E)) G)) := by
    ext g
    constructor
    · rintro ⟨d, rfl⟩
      obtain ⟨x, hx⟩ := cD.surjective d
      rw [hcD] at hx
      exact ⟨D.equiv.symm x, (D.equiv.symm x).property, (hkExp x).symm.trans (congrArg κ hx)⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨ExpD (D.equiv ⟨x, hx⟩), heκ ⟨x, hx⟩⟩
  have hnormal : ι.range.Normal := normal_of_exponential_ideal_connected hExp
    (cartanRootIdeal H) ι.range hiRange
  let φ := conjugationLiftOfNormal ι κ hι.injective hnormal
  have hconj (d : D.carrier) (n : N.carrier) :
      ι (φ d n) = κ d * ι n * (κ d)⁻¹ :=
    conjugationLiftOfNormal_spec ι κ hι.injective hnormal d n
  have hiDiff := mfderiv_eq_of_exponential_compatibility hExpN hExp ι
    (hιsmooth.mdifferentiable (by simp))
    ((cartanRootIdeal H).incl.comp N.equiv.symm.toLieHom).toLinearMap hiExp
  have hkDiff := mfderiv_eq_of_exponential_compatibility hExpD hExp κ
    (hκsmooth.mdifferentiable (by simp)) jD.toLinearMap hkExp
  have hlocal := cartanFactorProduct_map_nhds_one ι κ T H N.equiv D.equiv hιsmooth hκsmooth
    (fun x => by
      change mfderiv (𝓘(ℝ, N.modelSpace)) (𝓘(ℝ, E)) ι 1 (N.equiv x) = (x : GroupLieAlgebra (𝓘(ℝ, E)) G)
      exact (hiDiff (N.equiv x)).trans
        (congrArg (fun z : cartanRootIdeal H => (z : GroupLieAlgebra (𝓘(ℝ, E)) G))
          (N.equiv.symm_apply_apply x)))
    (fun x => by
      change mfderiv (𝓘(ℝ, D.modelSpace)) (𝓘(ℝ, E)) κ 1 (D.equiv x) = (x : GroupLieAlgebra (𝓘(ℝ, E)) G)
      exact (hkDiff (D.equiv x)).trans
        (congrArg (fun z : H => (z : GroupLieAlgebra (𝓘(ℝ, E)) G))
          (D.equiv.symm_apply_apply x)))
  obtain ⟨hprod, hlifts⟩ := factorProduct_surjective_and_compact_lifts ι κ φ hconj hlocal
  have hoverlap : Set.range ι ∩ Set.range κ = Exp ''
      ((cartanRootIdeal H : Set (GroupLieAlgebra (𝓘(ℝ, E)) G)) ∩ H) := by
    rw [hiRange, hkRange]
    ext g
    constructor
    · rintro ⟨⟨x, hx, hxe⟩, ⟨y, hy, hye⟩⟩
      have hxy := exponential_eq_of_mem_intrinsic_height_kernel T q Exp hExp π hπ hπExp
        (cartanRootIdeal_le_kernel H T hx) (hxe.trans hye.symm)
      exact ⟨x, ⟨hx, hxy ▸ hy⟩, hxe⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx.1, rfl⟩, ⟨x, hx.2, rfl⟩⟩
  exact ⟨{
    N := N, D := D, ExpN := ExpN, ExpD := ExpD, isExpN := hExpN, isExpD := hExpD,
    inclusionN := ι, inclusionD := κ, action := φ, closedN := hι, closedD := hκ,
    compatibleN := heι, compatibleD := heκ, normalN := hnormal, conjugation := hconj,
    surjective := hprod, compactLifts := hlifts, overlap := hoverlap }⟩

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_UniformCartanHeight
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_nonempty _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.unitaryCentralFixed_complete _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform Cartan height, including the zero-height branch -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule MeasureTheory Filter Set
open scoped Manifold Topology ENNReal NNReal BigOperators

attribute [local instance] stationaryL2Action zeroMeanL2Action

variable {EG G W : Type} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G]
  [IsTopologicalGroup G] [IsIsometricSMul G G] [ProperSpace G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  [MeasurableSpace W] [BorelSpace W] [SecondCountableTopology W]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H Exp)
  (hunimod : ∀ x : GroupLieAlgebra (𝓘(ℝ, EG)) G, LinearMap.trace ℝ _ (ad ℝ _ x) = 0)
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)
  [IsTopologicalGroup F.N.carrier] [SecondCountableTopology F.N.carrier]
  [IsTopologicalGroup F.D.carrier] [SecondCountableTopology F.D.carrier]
  {Λ : ℝ≥0}
  [MeasurableSpace (NormalizedPair G Λ)] [BorelSpace (NormalizedPair G Λ)]
  [MeasurableSpace C((Fin (finrank ℝ H) → ℝ), W)]
  [BorelSpace C((Fin (finrank ℝ H) → ℝ), W)]

set_option maxHeartbeats 1000000 in
theorem exists_uniform_cartan_height
    (hExp : IsGroupExponential Exp) (hinj : Function.Injective Exp)
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
    (νD : Measure F.D.carrier) [νD.IsHaarMeasure] [SigmaFinite νD]
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
    (rem : RemezPolynomialInput)
    (sourceInputs : ∀ (i : Fin M.letterCount)
      (s : rootOffsetConeIndex (M.supportIn T hunimod eW) i),
      M.PolarConeModelInputs F (heightConePreimage T eW
        (rootOffsetCone (M.supportIn T hunimod eW) (M.sampling_linear_weight_ne_zero T hunimod eW) i s)))
    (sourceDynkin : ∀ (i : Fin M.letterCount)
      (s : rootOffsetConeIndex (M.supportIn T hunimod eW) i)
      (J : NilpotentLieModel (M.coneWordIdeal (heightConePreimage T eW
        (rootOffsetCone (M.supportIn T hunimod eW) (M.sampling_linear_weight_ne_zero T hunimod eW) i s)))),
      NilpotentDynkinExpansionInput J.modelSpace J.carrier)
    (targetInputs : ∀ (i : Fin M.letterCount)
      (A : templateSymmetryGroup (M.supportIn T hunimod eW))
      (s : rootOffsetConeIndex (M.supportIn T hunimod eW) i),
      M.PolarConeModelInputs F (heightConePreimage T eW
        (transformedPolarCone (rootOffsetCone (M.supportIn T hunimod eW) (M.sampling_linear_weight_ne_zero T hunimod eW) i s) A.val)))
    (metricInput : GeodesicMetricExistenceInput)
    (raySource : ∀ (A : templateSymmetryGroup (M.supportIn T hunimod eW)) (i : Fin M.letterCount),
      M.PolarConeModelInputs F (positiveWeightRay
        ((((M.supportIn T hunimod eW).weight i).comp A.val.toLinearMap).comp
          (eW.toLinearMap.comp ((heightProjection T.character).comp H.subtype)))))
    (rayTarget : ∀ i : Fin M.letterCount,
      M.PolarConeModelInputs F (positiveWeightRay
        (((M.supportIn T hunimod eW).weight i).comp
          (eW.toLinearMap.comp ((heightProjection T.character).comp H.subtype)))))
    (raySourceDynkin : ∀ (A : templateSymmetryGroup (M.supportIn T hunimod eW)) (i : Fin M.letterCount)
      (Q : NilpotentLieModel ((cartanRootIdeal H) ⧸ M.coneWordIdeal (positiveWeightRay
        ((((M.supportIn T hunimod eW).weight i).comp A.val.toLinearMap).comp
          (eW.toLinearMap.comp ((heightProjection T.character).comp H.subtype)))))),
      NilpotentDynkinExpansionInput Q.modelSpace Q.carrier)
    (rayTargetDynkin : ∀ (i : Fin M.letterCount)
      (Q : NilpotentLieModel ((cartanRootIdeal H) ⧸ M.coneWordIdeal (positiveWeightRay
        (((M.supportIn T hunimod eW).weight i).comp
          (eW.toLinearMap.comp ((heightProjection T.character).comp H.subtype)))))),
      NilpotentDynkinExpansionInput Q.modelSpace Q.carrier)
    :
    ∃ (A : NormalizedPair G Λ → templateSymmetryGroup (M.supportIn T hunimod eW))
      (K : ℝ), 0 ≤ K ∧ ∀ p x,
      ‖(π (p.val.1 x)).toAdd - (A p).val (π x).toAdd‖ ≤ K := by
  classical
  rcases subsingleton_or_nontrivial W with hW | hW
  · let : Subsingleton W := hW
    refine ⟨fun _ => 1, 0, le_rfl, ?_⟩
    intro p x
    rw [show (π (p.val.1 x)).toAdd - ((1 : templateSymmetryGroup (M.supportIn T hunimod eW)).val)
      (π x).toAdd = 0 from Subsingleton.elim _ _, norm_zero]
  · let : Nontrivial W := hW
    let : Nonempty (Fin M.letterCount) := M.nonempty_letters_of_nontrivial_height T hunimod eW
    let : Nonempty (Fin (finrank ℝ (cartanRootIdeal H))) :=
      M.nonempty_root_coordinates_of_nonempty_letters
    exact M.exists_bounded_height_of_published_inputs T F hunimod eW
      hExp hinj realize haarN haarD dynkinN dynkinD chartN hchartN chartD hchartD m νD
      π hπExp hdec hvan hΛ hπ hpath rem sourceInputs sourceDynkin targetInputs
      metricInput raySource rayTarget raySourceDynkin rayTargetDynkin

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_IntrinsicCartanHeightAssembly
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_nonempty _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The uniform height theorem with intrinsic Cartan factors

The factors, coordinates, realization, ergodic decomposition, reduced
cohomology, and polynomial and metric estimates are supplied by proved
constructions for the actual unimodular group.
-/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule MeasureTheory Set
open scoped Manifold NNReal

attribute [local instance] stationaryL2Action zeroMeanL2Action

variable {EG G W : Type} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G]
  [IsTopologicalGroup G] [IsIsometricSMul G G] [ProperSpace G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  [MeasurableSpace W] [BorelSpace W] [SecondCountableTopology W]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  (hunimod : ∀ x : GroupLieAlgebra (𝓘(ℝ, EG)) G, LinearMap.trace ℝ _ (ad ℝ _ x) = 0)
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)

set_option maxHeartbeats 1000000 in
theorem exists_uniform_height_intrinsic_oai
    (Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G) (hExp : IsGroupExponential Exp)
    (m : Measure G) [m.IsHaarMeasure] [m.IsMulRightInvariant]
    (π : G →* Multiplicative W)
    (hπExp : ∀ x, (π (Exp x)).toAdd = eW (heightProjection T.character x))
    {Kπ : ℝ≥0} (hπ : LipschitzWith Kπ (fun g => (π g).toAdd))
    (hpath : ∀ g : G, ∃ γ : ℝ → G, γ 0 = 1 ∧ γ 1 = g ∧
      ∀ t ∈ Icc (0 : ℝ) 1, ∀ u ∈ Icc (0 : ℝ) 1,
        dist (γ t) (γ u) ≤ dist 1 g * |t - u|)
    (rem : RemezPolynomialInput) (metric : GeodesicMetricExistenceInput) :
    ∀ Λ : ℝ≥0, 2 ≤ (Λ : ℝ) →
      ∃ A : NormalizedPair G Λ → templateSymmetryGroup (M.supportIn T hunimod eW),
        ∃ K : ℝ, 0 ≤ K ∧ ∀ p x,
          ‖(π (p.val.1 x)).toAdd - (A p).val (π x).toAdd‖ ≤ K := by
  let nilp := nilpotentPublishedInputs
  obtain ⟨F⟩ := nonempty_intrinsic_cartanFactorModel T eW Exp hExp π hπ.continuous hπExp H
  let : IsTopologicalGroup F.N.carrier := topologicalGroup_of_lieGroup (𝓘(ℝ, F.N.modelSpace)) ⊤
  let : IsTopologicalGroup F.D.carrier := topologicalGroup_of_lieGroup (𝓘(ℝ, F.D.modelSpace)) ⊤
  let : LocallyCompactSpace F.D.carrier :=
    Manifold.locallyCompact_of_finiteDimensional (𝓘(ℝ, F.D.modelSpace))
  obtain ⟨⟨chartN, hchartN⟩, _⟩ := (nilp.haar _ F.N).2 F.ExpN F.isExpN
    (F.N.tangent_nilpotent (cartanRootIdeal_nilpotent H T))
  obtain ⟨⟨chartD, hchartD⟩, _⟩ := (nilp.haar _ F.D).2 F.ExpD F.isExpD
    (F.D.tangent_nilpotent inferInstance)
  let : SecondCountableTopology F.N.carrier := F.N.secondCountable_of_chart chartN
  let : SecondCountableTopology F.D.carrier := F.D.secondCountable_of_chart chartD
  let νD : Measure F.D.carrier := Measure.haar
  intro Λ hΛ
  let : MeasurableSpace (NormalizedPair G Λ) := borel _
  let : BorelSpace (NormalizedPair G Λ) := ⟨rfl⟩
  let : MeasurableSpace C((Fin (finrank ℝ H) → ℝ), W) := borel _
  let : BorelSpace C((Fin (finrank ℝ H) → ℝ), W) := ⟨rfl⟩
  exact M.exists_uniform_cartan_height T F hunimod eW hExp
    (intrinsic_exponential_injective T Exp hExp) exponentialLinearRealizationInput_intrinsic
    (nilp.haar _ F.N) (nilp.haar _ F.D) (nilp.dynkin _ F.N) (nilp.dynkin _ F.D)
    chartN hchartN chartD hchartD m νD π hπExp normalizedPair_ergodicDecomposition
    (fun μ _ _ => (cartan_unitary_reduced_vanishing T F M hExp hunimod eW π hπExp
      hπ.continuous).to_reduced (ZeroMeanL2 (W := W) μ))
    (by linarith) hπ hpath rem
    (fun _ _ => nilp.polar M F _) (fun _ _ J => nilp.dynkin _ J)
    (fun _ _ _ => nilp.polar M F _) metric
    (fun _ _ => nilp.polar M F _) (fun _ => nilp.polar M F _)
    (fun _ _ Q => nilp.dynkin _ Q) (fun _ Q => nilp.dynkin _ Q)

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

theorem solution : type_of% @OAI.PolycyclicRecognition.CartanWordModel.exists_uniform_height_intrinsic_oai := @OAI.PolycyclicRecognition.CartanWordModel.exists_uniform_height_intrinsic_oai
