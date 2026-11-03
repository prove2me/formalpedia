-- Prove2me | solution 1 for OAI.PolycyclicRecognition.CartanWordModel.MeasuredCone.sectionMeasure_isHaar
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-02T22:40:17.051007+00:00
-- url     : https://prove2.me/submissions/bf5b3a3e-cb88-44b6-be4b-9908bf2917bc

import Mathlib
import Definitions.Def_OAIQ093D027

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_QuotientSectionCoordinates
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Coordinates separating a quotient and its kernel

A continuous section of the actual quotient map gives global coordinates.
The formulas retain the conjugation and section cocycle needed for product
Haar measure and the ideal-coordinate estimates.
-/

noncomputable section
namespace PolycyclicRecognition

variable {N Q : Type*} [Group N] [Group Q]
  [TopologicalSpace N] [TopologicalSpace Q] [IsTopologicalGroup N] [IsTopologicalGroup Q]
  (π : N →* Q) (hπ : Continuous π) (s : C(Q, N)) (hs : ∀ q, π (s q) = q)

omit [IsTopologicalGroup Q] in
theorem quotientSection_left_translation (n : N) (p : Q × π.ker) :
    quotientSectionHomeomorph π hπ s hs
      (n * (quotientSectionHomeomorph π hπ s hs).symm p) =
    (π n * p.1, quotientKernelConjugate π n p.2 * quotientSectionCocycle π s hs n p.1) := by
  have hp : π p.2 = 1 := p.2.property
  apply Prod.ext
  · simp [quotientSectionHomeomorph, hp, hs]
  · apply Subtype.ext
    change n * ((p.2 : N) * s p.1) * (s (π (n * ((p.2 : N) * s p.1))))⁻¹ =
      (n * p.2 * n⁻¹) * (n * s p.1 * (s (π n * p.1))⁻¹)
    simp only [map_mul, hp, hs, one_mul]
    group

theorem continuous_quotientSectionCocycle (n : N) :
    Continuous (quotientSectionCocycle π s hs n) := by
  exact ((continuous_const.mul s.continuous).mul
    (s.continuous.comp (continuous_const.mul continuous_id)).inv).subtype_mk _

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_QuotientSectionMeasure
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Product measure in quotient-section coordinates -/

noncomputable section
namespace PolycyclicRecognition

open MeasureTheory

variable {N Q : Type*} [Group N] [Group Q]
  [TopologicalSpace N] [TopologicalSpace Q] [IsTopologicalGroup N] [IsTopologicalGroup Q]
  [SecondCountableTopology Q]
  [MeasurableSpace N] [MeasurableSpace Q] [BorelSpace N] [BorelSpace Q]
  (π : N →* Q) (hπ : Continuous π) (s : C(Q, N)) (hs : ∀ q, π (s q) = q)
  (μQ : Measure Q) (μI : Measure π.ker) [SFinite μQ] [SFinite μI]
  [μQ.IsMulLeftInvariant] [μI.IsMulRightInvariant]

/-- Conjugation invariance of the kernel measure and right invariance of
its translations make the coordinate skew action preserve product measure. -/
theorem quotientSection_skew_measurePreserving
    (hconj : ∀ n : N, MeasurePreserving (quotientKernelConjugate π n) μI μI) (n : N) :
    MeasurePreserving (fun p : Q × π.ker =>
      (π n * p.1, quotientKernelConjugate π n p.2 * quotientSectionCocycle π s hs n p.1))
      (μQ.prod μI) (μQ.prod μI) := by
  have hleft : MeasurePreserving (fun q : Q => π n * q) μQ μQ :=
    ⟨measurable_const.mul measurable_id, map_mul_left_eq_self μQ (π n)⟩
  apply hleft.skew_product (g := fun q i =>
    quotientKernelConjugate π n i * quotientSectionCocycle π s hs n q)
  · have hc : Continuous (quotientKernelConjugate π n) :=
      ((continuous_const.mul continuous_subtype_val).mul continuous_const).subtype_mk _
    exact ((hc.comp continuous_snd).mul
      ((continuous_quotientSectionCocycle π s hs n).comp continuous_fst)).measurable
  · apply Filter.Eventually.of_forall
    intro q
    have hright : MeasurePreserving (fun i : π.ker => i * quotientSectionCocycle π s hs n q) μI μI :=
      ⟨(continuous_id.mul continuous_const).measurable, map_mul_right_eq_self μI _⟩
    exact (hright.comp (hconj n)).map_eq

/-- Pushing product measure through the actual global section coordinates
gives a left-invariant measure on the original group. -/
theorem quotientSection_product_left_invariant
    (hconj : ∀ n : N, MeasurePreserving (quotientKernelConjugate π n) μI μI) (n : N) :
    MeasurePreserving (fun x : N => n * x)
      (Measure.map (quotientSectionHomeomorph π hπ s hs).symm (μQ.prod μI))
      (Measure.map (quotientSectionHomeomorph π hπ s hs).symm (μQ.prod μI)) := by
  let e := quotientSectionHomeomorph π hπ s hs
  let T := fun p : Q × π.ker =>
    (π n * p.1, quotientKernelConjugate π n p.2 * quotientSectionCocycle π s hs n p.1)
  have hT := quotientSection_skew_measurePreserving π s hs μQ μI hconj n
  have hsem : Function.Semiconj e.symm T (fun x => n * x) := by
    intro p
    apply e.injective
    rw [e.apply_symm_apply]
    exact (quotientSection_left_translation π hπ s hs n p).symm
  exact (e.symm.measurable.measurePreserving (μQ.prod μI)).of_semiconj hT hsem
    (continuous_const.mul continuous_id).measurable

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_QuotientSectionHaar
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Haar measure in quotient-section coordinates -/

noncomputable section
namespace PolycyclicRecognition

open MeasureTheory

variable {N Q : Type*} [Group N] [Group Q]
  [TopologicalSpace N] [TopologicalSpace Q] [IsTopologicalGroup N] [IsTopologicalGroup Q]
  [SecondCountableTopology Q]
  [MeasurableSpace N] [MeasurableSpace Q] [BorelSpace N] [BorelSpace Q]
  (π : N →* Q) (hπ : Continuous π) (s : C(Q, N)) (hs : ∀ q, π (s q) = q)
  (μQ : Measure Q) (μI : Measure π.ker) [SFinite μQ] [SFinite μI]
  [μQ.IsHaarMeasure] [μI.IsHaarMeasure] [μI.IsMulRightInvariant]

/-- The coordinate product is itself Haar: left invariance follows from
the explicit skew action, and the homeomorphism preserves finiteness on
compact sets and positivity on open sets. -/
theorem quotientSection_product_isHaarMeasure
    (hconj : ∀ n : N, MeasurePreserving (quotientKernelConjugate π n) μI μI) :
    (Measure.map (quotientSectionHomeomorph π hπ s hs).symm (μQ.prod μI)).IsHaarMeasure := by
  let e := (quotientSectionHomeomorph π hπ s hs).symm
  exact
    { map_mul_left_eq_self := fun n =>
        (quotientSection_product_left_invariant π hπ s hs μQ μI hconj n).map_eq
      toIsFiniteMeasureOnCompacts := Measure.IsFiniteMeasureOnCompacts.map (μQ.prod μI) e
      toIsOpenPosMeasure := e.continuous.isOpenPosMeasure_map e.surjective }

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanMeasuredConeHaar
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_countable _root_.OAI.PolycyclicRecognition.finitelyGeneratedSubgroupIndex_countable _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Haar measure for the actual section used by the probe chains -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule MeasureTheory
open scoped Manifold

variable {EG G : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G]
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {ExpG : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H ExpG)
  (C : Set (H →ₗ[ℝ] ℝ)) (D : M.MeasuredCone F C)

set_option maxHeartbeats 1000000 in
/-- The pure-word section chosen by the tile construction can replace the
initial quotient section without changing the Haar property. -/
theorem MeasuredCone.sectionMeasure_isHaar_oai
    (σ : ContinuousMap D.Q.carrier F.N.carrier) (hσ : ∀ q, D.maps.quotient (σ q) = q) :
    (D.sectionMeasure M F C σ hσ).IsHaarMeasure := by
  let : IsTopologicalGroup F.N.carrier :=
    topologicalGroup_of_lieGroup (𝓘(ℝ, F.N.modelSpace)) ⊤
  let : IsTopologicalGroup D.Q.carrier :=
    topologicalGroup_of_lieGroup (𝓘(ℝ, D.Q.modelSpace)) ⊤
  let bQ := (finBasis ℝ ((cartanRootIdeal H) ⧸ M.coneWordIdeal C)).map D.Q.equiv.toLinearEquiv
  let qcoord := bQ.equivFun.symm.toContinuousLinearEquiv.toHomeomorph.trans D.maps.chartQ
  let : SecondCountableTopology D.Q.carrier := qcoord.symm.secondCountableTopology
  let : LocallyCompactSpace D.Q.carrier := qcoord.symm.isOpenEmbedding.locallyCompactSpace
  let bI := (finBasis ℝ (M.coneWordIdeal C)).map D.I.equiv.toLinearEquiv
  let icoord := bI.equivFun.symm.toContinuousLinearEquiv.toHomeomorph.trans D.maps.chartI
  let : SecondCountableTopology D.I.carrier := icoord.symm.secondCountableTopology
  let ke := kernelRealization D.maps.quotient D.maps.inclusion D.maps.inclusion_closed D.maps.inclusion_range
  let : SecondCountableTopology D.maps.quotient.ker := ke.symm.toHomeomorph.secondCountableTopology
  let : LocallyCompactSpace D.I.carrier := icoord.symm.isOpenEmbedding.locallyCompactSpace
  let : LocallyCompactSpace D.maps.quotient.ker := ke.symm.toHomeomorph.isOpenEmbedding.locallyCompactSpace
  let : D.measures.measureQ.IsHaarMeasure := D.measures.haarQ
  let : (D.kernelMeasure M F C).IsHaarMeasure := D.measures.haarKernel
  let : (D.kernelMeasure M F C).IsMulRightInvariant := D.measures.kernel_rightInvariant
  exact quotientSection_product_isHaarMeasure D.maps.quotient D.maps.quotient_continuous σ hσ
    D.measures.measureQ (D.kernelMeasure M F C) D.measures.conjugation_invariant

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.PolycyclicRecognition.CartanWordModel.MeasuredCone.sectionMeasure_isHaar_oai.{u_1, u_2} := @OAI.PolycyclicRecognition.CartanWordModel.MeasuredCone.sectionMeasure_isHaar_oai.{u_1, u_2}
