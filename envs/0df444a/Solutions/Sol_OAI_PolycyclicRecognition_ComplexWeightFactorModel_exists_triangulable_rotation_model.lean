-- Prove2me | solution 1 for OAI.PolycyclicRecognition.ComplexWeightFactorModel.exists_triangulable_rotation_model
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-03T01:09:20.324273+00:00
-- url     : https://prove2.me/submissions/6e3f51eb-0ba2-4048-b26d-a078529a4cf8

import Mathlib
import Definitions.Def_PolycyclicRecognition
import Definitions.Def_OAIQ093D021
import Definitions.Def_OAIQ093D025
import Theorems.Thm_OAI_PolycyclicRecognition_ComplexWeightFactorModel_contMDiff_factorParameter
import Theorems.Thm_OAI_PolycyclicRecognition_ComplexWeightFactorModel_exists_faithful_rotation_triangular_representation
import Theorems.Thm_OAI_PolycyclicRecognition_ComplexWeightFactorModel_hasMFDerivAt_factorParameter
import Theorems.Thm_OAI_PolycyclicRecognition_exists_triangulable_model_of_representations

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_ComplexFactorParameters
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.ComplexWeightFactorModel.smoothRotationalModificationSimplyConnected _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanRealShadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Linear parameters for the two actual complex-weight factors -/

noncomputable section
namespace PolycyclicRecognition

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {n : ℕ} (T : ComplexTriangularAdjoint L n)
  (H : LieSubalgebra ℝ L) [H.IsCartanSubalgebra]

namespace ComplexTriangularAdjoint

theorem factorComponents_add (x : L) :
    (T.kernelComponent H x : L) + (T.cartanComponent H x : L) = x :=
  sub_add_cancel _ _

end ComplexTriangularAdjoint
end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_ComplexFactorLocalChart
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.ComplexWeightFactorModel.smoothRotationalModificationSimplyConnected _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanRealShadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Smooth local coordinates from the complex-weight factors -/

noncomputable section
namespace PolycyclicRecognition
open scoped Manifold ContDiff Topology

variable {E G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MetricSpace G] [ChartedSpace E G]
  [Group G] [LieGroup (𝓘(ℝ,E)) ⊤ G]
  {a : ℕ} {T : ComplexTriangularAdjoint (GroupLieAlgebra (𝓘(ℝ,E)) G) a}
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ,E)) G)} [H.IsCartanSubalgebra]
  {Exp : GroupLieAlgebra (𝓘(ℝ,E)) G → G}

namespace ComplexWeightFactorModel
variable (F : ComplexWeightFactorModel T H Exp)

theorem factorParameter_zero : F.factorParameter 0 = 1 := by
  unfold factorParameter
  rw [map_zero,map_zero]
  have hn : F.ExpN (0 : F.N.modelSpace) = 1 := F.isExpN.map_zero
  have hd : F.ExpD (0 : F.D.modelSpace) = 1 := F.isExpD.map_zero
  rw [hn,hd,map_one,map_one,mul_one]

end ComplexWeightFactorModel
end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_HomeomorphicParameter
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Transporting local parameters across a homeomorphism -/

noncomputable section
namespace PolycyclicRecognition

variable {V X Y : Type*} [TopologicalSpace V] [TopologicalSpace X] [TopologicalSpace Y]
  [Zero V] [One X] [One Y]

omit [TopologicalSpace V] in
theorem parameter_zero_of_coordinates (e : X ≃ₜ Y) (he : e 1 = 1)
    (P : V → X) (Q : V → Y) (h : ∀ v, e (P v) = Q v) (hQ : Q 0 = 1) : P 0 = 1 :=
  e.injective ((h 0).trans (hQ.trans he.symm))

theorem exists_parameter_of_coordinate_homeomorph (e : X ≃ₜ Y) (he : e 1 = 1)
    (P : V → X) (Q : V → Y) (h : ∀ v, e (P v) = Q v) (hQ : Q 0 = 1)
    (hl : ∃ q : OpenPartialHomeomorph V Y,
      (0 : V) ∈ q.source ∧ q 0 = Q 0 ∧ ∀ v ∈ q.source, q v = Q v) :
    ∃ p : OpenPartialHomeomorph V X,
      (0 : V) ∈ p.source ∧ p 0 = 1 ∧ ∀ v ∈ p.source, p v = P v := by
  obtain ⟨q,hq,hq0,hqP⟩ := hl
  let p := q.trans e.symm.toOpenPartialHomeomorph
  have hp : (0 : V) ∈ p.source := ⟨hq,Set.mem_univ _⟩
  have hP (v : V) (hv : v ∈ p.source) : p v = P v := by
    apply e.injective
    change e (e.symm (q v)) = _
    rw [e.apply_symm_apply,hqP v hv.1,h]
  exact ⟨p,hp,(hP 0 hp).trans (parameter_zero_of_coordinates e he P Q h hQ),hP⟩

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_AnalyticInverseChart
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Restricting an analytic inverse chart to its analytic domain -/

noncomputable section
namespace PolycyclicRecognition
open Set Filter
open scoped ContDiff Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem exists_analytic_inverse_chart {f : E → E}
    (hf : ContDiffAt ℝ ω f 0) (h0 : f 0 = 0)
    (hd : HasFDerivAt f (ContinuousLinearMap.id ℝ E) 0) :
    ∃ q : OpenPartialHomeomorph E E,
      (0 : E) ∈ q.source ∧ q 0 = 0 ∧ (q : E → E) = f ∧
        ContDiffOn ℝ ω q.symm q.target := by
  let d := ContinuousLinearEquiv.refl ℝ E
  let q : OpenPartialHomeomorph E E := hf.toOpenPartialHomeomorph f (f' := d) hd (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hq0 : (0 : E) ∈ q.source := hf.mem_toOpenPartialHomeomorph_source (f' := d) hd (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hi : ContDiffAt ℝ ω q.symm 0 := by
    change ContDiffAt ℝ ω (hf.localInverse (f' := d) hd (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)) 0
    simpa only [h0] using hf.to_localInverse (f' := d) hd (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  obtain ⟨s,hs,hsi⟩ := hi.contDiffOn le_rfl (by intro _; rfl)
  obtain ⟨u,hus,hu,hu0⟩ := mem_nhds_iff.mp hs
  let r := OpenPartialHomeomorph.trans q (OpenPartialHomeomorph.ofSet u hu)
  refine ⟨r, ?_, ?_, rfl, ?_⟩
  · refine ⟨hq0, ?_⟩
    change f 0 ∈ u
    rwa [h0]
  · exact h0
  · change ContDiffOn ℝ ω (fun x => q.symm x) _
    apply hsi.mono
    intro x hx
    exact hus hx.1

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_RepresentationParameterChart
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Matrix coordinates from an analytic represented local parameter -/

noncomputable section
namespace PolycyclicRecognition
open Set
open scoped ContDiff

variable {G E A : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedRing A] [NormedAlgebra ℝ A]

omit [IsTopologicalGroup G] in
theorem representedLocalChart_of_parameter
    (ρ : G →* Aˣ) (p : OpenPartialHomeomorph E G)
    (hp : (0 : E) ∈ p.source) (hp0 : p 0 = 1)
    (P : A →L[ℝ] E) (U V : E → A)
    (hU : ContDiff ℝ ω U) (hV : ContDiff ℝ ω V)
    (heU : ∀ x ∈ p.source, U x = (ρ (p x) : A))
    (heV : ∀ x ∈ p.source, V x = ((ρ (p x))⁻¹ : Aˣ))
    (hd : HasFDerivAt (fun x => P (U x - 1)) (ContinuousLinearMap.id ℝ E) 0) :
    Nonempty (RepresentedLocalChart (E := E) ρ) := by
  have hU0 : U 0 = 1 := by rw [heU 0 hp,hp0,map_one,Units.val_one]
  have hQ : ContDiff ℝ ω (fun x => P (U x - 1)) :=
    P.contDiff.comp (hU.sub contDiff_const)
  have hQ0 : P (U 0 - 1) = 0 := by rw [hU0,sub_self,map_zero]
  obtain ⟨q,hq0,hqzero,hq,hqi⟩ := exists_analytic_inverse_chart hQ.contDiffAt hQ0 hd
  have hpinv : p.symm (1 : G) = 0 := by rw [← hp0]; exact p.left_inv hp
  let e := p.symm.trans q
  have heone : (1 : G) ∈ e.source := by
    refine ⟨hp0 ▸ p.map_source hp, ?_⟩
    change p.symm 1 ∈ q.source
    rwa [hpinv]
  have hetarget : e.target ⊆ q.target := fun _ hx => hx.1
  refine ⟨{
    chart := e
    one_mem := heone
    at_one := ?_
    coordinate := P
    coordinate_eq := ?_
    realization := U ∘ q.symm
    realization_contDiff := hU.comp_contDiffOn (hqi.mono hetarget)
    realization_eq := ?_
    inverseRealization := V ∘ q.symm
    inverseRealization_contDiff := hV.comp_contDiffOn (hqi.mono hetarget)
    inverseRealization_eq := ?_ }⟩
  · change q (p.symm 1) = 0
    rw [hpinv,hqzero]
  · intro g hg
    change q (p.symm g) = P ((ρ g : A) - 1)
    rw [hq]
    change P (U (p.symm g) - 1) = _
    rw [heU _ (p.map_target hg.1),p.right_inv hg.1]
  · intro x hx
    exact heU (q.symm x) hx.2
  · intro x hx
    exact heV (q.symm x) hx.2

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_ExponentialTriangularImage
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Global triangularity from exponential factor coordinates -/

noncomputable section
namespace PolycyclicRecognition
open scoped Matrix.Norms.Operator

theorem upperTriangular_of_exponential_factors {Γ X Y : Type*} [Group Γ] {m : ℕ}
    (f : X × Y → Γ) (hf : Function.Surjective f)
    (P : X → Matrix (Fin m) (Fin m) ℝ) (Q : Y → Matrix (Fin m) (Fin m) ℝ)
    (hP : ∀ x, (P x).IsUpperTriangular) (hQ : ∀ y, (Q y).IsUpperTriangular)
    (ρ : Γ →* (Matrix (Fin m) (Fin m) ℝ)ˣ)
    (he : ∀ x y, ρ (f (x,y)) = algebraExpUnit (P x) * algebraExpUnit (Q y)) :
    ∀ g, (ρ g : Matrix (Fin m) (Fin m) ℝ).IsUpperTriangular := by
  intro g
  obtain ⟨⟨x,y⟩,rfl⟩ := hf g
  rw [he]
  exact (positiveTriangularExp (P x) (hP x) * positiveTriangularExp (Q y) (hQ y)).property.1

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_RepresentedMatrixChoice
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Assembling a represented group from faithful factor integrations -/

noncomputable section
namespace PolycyclicRecognition
open scoped Matrix.Norms.Operator
attribute [local instance 100] LieRing.ofAssociativeRing

variable {L Γ X Y E : Type} [LieRing L] [LieAlgebra ℝ L]
  [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [IsTopologicalGroup Γ] in
theorem exists_represented_matrix_group
    (Q : ∀ m, (L →ₗ⁅ℝ⁆ Matrix (Fin m) (Fin m) ℝ) → Prop)
    (u : X → L) (v : Y → L) (f : X × Y → Γ) (hf : Function.Surjective f)
    (hdata : ∃ m, 0 < m ∧ ∃ j, Q m j ∧
      ∃ ρ : Γ →* (Matrix (Fin m) (Fin m) ℝ)ˣ, Continuous ρ ∧ Function.Injective ρ ∧
        ∀ x y, ρ (f (x,y)) = algebraExpUnit (j (u x)) * algebraExpUnit (j (v y)))
    (hu : ∀ m j, Q m j → ∀ z, (j z).IsUpperTriangular)
    (hc : ∀ m j, Q m j → ∀ ρ : Γ →* (Matrix (Fin m) (Fin m) ℝ)ˣ,
      (∀ x y, ρ (f (x,y)) = algebraExpUnit (j (u x)) * algebraExpUnit (j (v y))) →
        Nonempty (RepresentedLocalChart (E := E) ρ)) :
    ∃ m, ∃ ρ : Γ →* (Matrix (Fin m) (Fin m) ℝ)ˣ, Continuous ρ ∧ Function.Injective ρ ∧
      (∀ g, (ρ g : Matrix (Fin m) (Fin m) ℝ).IsUpperTriangular) ∧
      Nonempty (RepresentedLocalChart (E := E) ρ) := by
  obtain ⟨m,_,j,hj,ρ,hρ,hi,he⟩ := hdata
  exact ⟨m,ρ,hρ,hi,upperTriangular_of_exponential_factors f hf
    (j ∘ u) (j ∘ v) (fun x => hu m j hj _) (fun y => hu m j hj _) ρ he,
    hc m j hj ρ he⟩

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_ActualSmoothRotation
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.ComplexWeightFactorModel.smoothRotationalModificationSimplyConnected _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanRealShadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The smooth rotational modification from the actual Cartan factors

The chosen compact action retains its factor formula. This constructs a
smooth graph group; its Lie algebra identification and triangular matrix
realization are separate steps.
-/

noncomputable section
namespace PolycyclicRecognition
open scoped Manifold ContDiff

variable {E G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MetricSpace G] [ChartedSpace E G]
  [Group G] [LieGroup (𝓘(ℝ,E)) ⊤ G]
  {a : ℕ} {T : ComplexTriangularAdjoint (GroupLieAlgebra (𝓘(ℝ,E)) G) a}
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ,E)) G)} [H.IsCartanSubalgebra]
  {Exp : GroupLieAlgebra (𝓘(ℝ,E)) G → G}

namespace ComplexWeightFactorModel
variable (F : ComplexWeightFactorModel T H Exp) (hExp : IsGroupExponential Exp)

theorem continuous_factorCompactRotationAction :
    Continuous (fun p : realRotationTorus (GroupLieAlgebra (𝓘(ℝ,E)) G) H × G =>
      F.factorCompactRotationAction hExp p.1 p.2) :=
  (F.exists_compact_rotation_action hExp).choose_spec.1

attribute [local instance] semidirectProductTopology

attribute [local instance] smoothRotationalModificationChartedSpace

end ComplexWeightFactorModel
end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_ExponentialProductCoordinates
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Projected coordinates for products of exponentials -/

noncomputable section
namespace PolycyclicRecognition
open scoped ContDiff

variable {E A : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

theorem contDiff_algebra_exp : ContDiff ℝ ω (NormedSpace.exp : A → A) :=
  contDiff_iff_contDiffAt.mpr fun x => (NormedSpace.exp_analytic (𝕂 := ℝ) x).contDiffAt

theorem exponential_product_derivative (K D : E →L[ℝ] A) :
    HasFDerivAt (fun x => NormedSpace.exp (K x) * NormedSpace.exp (D x)) (K + D) 0 := by
  have hK : HasFDerivAt (fun x => NormedSpace.exp (K x)) K 0 := by
    have h : HasFDerivAt (NormedSpace.exp : A → A) (1 : A →L[ℝ] A) (K 0) := by
      simpa only [map_zero] using (hasFDerivAt_exp_zero (𝕂 := ℝ) (𝔸 := A))
    simpa only [Function.comp_def, ContinuousLinearMap.one_def, ContinuousLinearMap.id_comp]
      using h.comp 0 K.hasFDerivAt
  have hD : HasFDerivAt (fun x => NormedSpace.exp (D x)) D 0 := by
    have h : HasFDerivAt (NormedSpace.exp : A → A) (1 : A →L[ℝ] A) (D 0) := by
      simpa only [map_zero] using (hasFDerivAt_exp_zero (𝕂 := ℝ) (𝔸 := A))
    simpa only [Function.comp_def, ContinuousLinearMap.one_def, ContinuousLinearMap.id_comp]
      using h.comp 0 D.hasFDerivAt
  convert hK.mul' hD using 1 <;> first | (with_reducible_and_instances rfl) | (simp [add_comm])

theorem exists_projected_exponential_coordinates [FiniteDimensional ℝ A]
    (K D : E →L[ℝ] A) (hinj : Function.Injective (K + D)) :
    ∃ P : A →L[ℝ] E,
      HasFDerivAt (fun x => P (NormedSpace.exp (K x) * NormedSpace.exp (D x) - 1))
        (ContinuousLinearMap.id ℝ E) 0 := by
  obtain ⟨p,hp⟩ := (K + D).toLinearMap.exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr hinj)
  let P : A →L[ℝ] E := p.toContinuousLinearMap
  refine ⟨P, ?_⟩
  have h := P.hasFDerivAt.comp 0 ((exponential_product_derivative K D).sub_const 1)
  have he : P.comp (K + D) = ContinuousLinearMap.id ℝ E := by
    apply ContinuousLinearMap.ext
    intro x
    exact LinearMap.congr_fun hp x
  exact he ▸ h

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_ExponentialParameterChart
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # An analytic represented chart from two exponential parameters -/

noncomputable section
namespace PolycyclicRecognition
open scoped ContDiff

variable {G E A : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedRing A] [NormedAlgebra ℝ A] [FiniteDimensional ℝ A]

omit [IsTopologicalGroup G] in
theorem representedLocalChart_of_exponential_parameter
    (ρ : G →* Aˣ) (p : OpenPartialHomeomorph E G)
    (hp : (0 : E) ∈ p.source) (hp0 : p 0 = 1)
    (K D : E →L[ℝ] A) (hinj : Function.Injective (K + D))
    (he : ∀ x ∈ p.source, ρ (p x) = algebraExpUnit (K x) * algebraExpUnit (D x)) :
    Nonempty (RepresentedLocalChart (E := E) ρ) := by
  obtain ⟨P,hP⟩ := exists_projected_exponential_coordinates K D hinj
  let U : E → A := fun x => NormedSpace.exp (K x) * NormedSpace.exp (D x)
  let V : E → A := fun x => NormedSpace.exp (-D x) * NormedSpace.exp (-K x)
  have hU : ContDiff ℝ ω U :=
    (contDiff_algebra_exp.comp K.contDiff).mul (contDiff_algebra_exp.comp D.contDiff)
  have hV : ContDiff ℝ ω V :=
    (contDiff_algebra_exp.comp D.contDiff.neg).mul (contDiff_algebra_exp.comp K.contDiff.neg)
  apply representedLocalChart_of_parameter ρ p hp hp0 P U V hU hV _ _ hP
  · intro x hx
    rw [he x hx]
    rfl
  · intro x hx
    rw [he x hx, mul_inv_rev]
    rfl

omit [IsTopologicalGroup G] in
theorem representedLocalChart_of_exponential_localization
    (ρ : G →* Aˣ) (f : E → G) (K D : E →L[ℝ] A)
    (hinj : Function.Injective (K + D))
    (he : ∀ x, ρ (f x) = algebraExpUnit (K x) * algebraExpUnit (D x))
    (hl : ∃ p : OpenPartialHomeomorph E G, (0 : E) ∈ p.source ∧ p 0 = 1 ∧
      ∀ x ∈ p.source, p x = f x) :
    Nonempty (RepresentedLocalChart (E := E) ρ) := by
  obtain ⟨p,hp,hp0,hpf⟩ := hl
  exact representedLocalChart_of_exponential_parameter ρ p hp hp0 K D hinj
    (fun x hx => (congrArg ρ (hpf x hx)).trans (he x))

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_ManifoldLocalParameter
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A local homeomorphism from an invertible manifold derivative -/

noncomputable section
namespace PolycyclicRecognition
open Set
open scoped Manifold ContDiff

variable {V E M : Type*}
  [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ,E)) ∞ M]

theorem exists_manifold_local_parameter {P : V → M} {x₀ : V} {d : V ≃L[ℝ] E}
    (hP : ContMDiff (𝓘(ℝ,V)) (𝓘(ℝ,E)) ∞ P)
    (hd : HasMFDerivAt (𝓘(ℝ,V)) (𝓘(ℝ,E)) P x₀ d.toContinuousLinearMap) :
    ∃ p : OpenPartialHomeomorph V M, x₀ ∈ p.source ∧ p x₀ = P x₀ ∧
      ∀ x ∈ p.source, p x = P x := by
  let c := chartAt E (P x₀)
  let Q : V → E := c ∘ P
  have hc : ContMDiffAt (𝓘(ℝ,E)) (𝓘(ℝ,E)) ∞ c (P x₀) := by
    change ContMDiffAt (𝓘(ℝ,E)) (𝓘(ℝ,E)) ∞ (extChartAt (𝓘(ℝ,E)) (P x₀)) (P x₀)
    exact contMDiffAt_extChartAt
  have hQ : ContDiffAt ℝ ∞ Q x₀ := (hc.comp x₀ hP.contMDiffAt).contDiffAt
  have hcder : HasMFDerivAt (𝓘(ℝ,E)) (𝓘(ℝ,E)) c (P x₀)
      (ContinuousLinearMap.id ℝ E) := by
    apply hc.mdifferentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) |>.hasMFDerivAt |>.congr_mfderiv
    change mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,E)) (extChartAt (𝓘(ℝ,E)) (P x₀)) (P x₀) = _
    rw [mfderiv_extChartAt_self]
    rfl
  have hQd : HasFDerivAt Q d.toContinuousLinearMap x₀ := by
    have hh : HasFDerivAt Q ((ContinuousLinearMap.id ℝ E).comp d.toContinuousLinearMap) x₀ :=
      (hcder.comp x₀ hd).hasFDerivAt
    simpa only [ContinuousLinearMap.id_comp] using hh
  let q := hQ.toOpenPartialHomeomorph Q hQd (by simp)
  let u := {x | P x ∈ c.source}
  have hu : IsOpen u := c.open_source.preimage hP.continuous
  let r := q.restr u
  let p := r.trans c.symm
  have hpP (x : V) (hx : x ∈ p.source) : p x = P x := by
    have hxr : x ∈ (q.restr u).source := hx.1
    rw [q.restr_source' u hu] at hxr
    exact c.left_inv hxr.2
  have hx : x₀ ∈ p.source := by
    refine ⟨?_, ?_⟩
    · change x₀ ∈ (q.restr u).source
      rw [q.restr_source' u hu]
      exact ⟨hQ.mem_toOpenPartialHomeomorph_source hQd (by simp), mem_chart_source E (P x₀)⟩
    · exact c.map_source (mem_chart_source E (P x₀))
  exact ⟨p,hx,hpP x₀ hx,hpP⟩

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_SmoothRotationExtension
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanRealShadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual smooth graph and its compact extension -/

noncomputable section
namespace PolycyclicRecognition
open scoped Manifold

variable {E G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MetricSpace G] [ChartedSpace E G]
  [Group G] [LieGroup (𝓘(ℝ,E)) ⊤ G]
  {a : ℕ} {T : ComplexTriangularAdjoint (GroupLieAlgebra (𝓘(ℝ,E)) G) a}
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ,E)) G)} [H.IsCartanSubalgebra]
  {Exp : GroupLieAlgebra (𝓘(ℝ,E)) G → G}

namespace ComplexWeightFactorModel
variable (F : ComplexWeightFactorModel T H Exp) (hExp : IsGroupExponential Exp)
attribute [local instance] semidirectProductTopology

instance smoothRotationExtensionTopologicalGroup :
    IsTopologicalGroup (G ⋊[F.factorCompactRotationAction hExp]
      realRotationTorus (GroupLieAlgebra (𝓘(ℝ,E)) G) H) := by
  let : IsTopologicalGroup G := topologicalGroup_of_lieGroup (𝓘(ℝ,E)) ⊤
  exact semidirectProductTopologicalGroup _ (F.continuous_factorCompactRotationAction hExp)

instance smoothRotationalModificationTopologicalGroup :
    IsTopologicalGroup (F.SmoothRotationalModification hExp) := inferInstance

end ComplexWeightFactorModel
end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_RotationFactorProduct
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Global factor coordinates for the actual rotational graph -/

noncomputable section
namespace PolycyclicRecognition
open scoped Manifold ContDiff

private theorem surjective_of_coordinates {A X Y : Type*} (e : X → Y)
    (he : Function.Injective e) (f : A → X) (g : A → Y)
    (hf : ∀ a, e (f a) = g a) (hg : Function.Surjective g) : Function.Surjective f := by
  intro x
  obtain ⟨a,ha⟩ := hg (e x)
  exact ⟨a, he ((hf a).trans ha)⟩

private theorem rotationalTwistLift_mul_left {A G K : Type*}
    [Group A] [Group G] [CommGroup K] [TopologicalSpace G] [TopologicalSpace K]
    (α : K →* MulAut G) (τ : G →* K) (hinv : ∀ k g, τ (α k g) = τ g)
    (f : A →* G) (hfix : ∀ a b, α ((τ (f a))⁻¹) (f b) = f b)
    (a : A) (p : rotationalTwist α τ hinv) (ha : τ (f a) = 1) :
    (rotationalTwistLift α τ hinv f hfix a * p).val.left = f a * p.val.left := by
  change f a * α ((τ (f a))⁻¹) p.val.left = _
  rw [ha, inv_one, map_one]
  rfl

variable {E G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MetricSpace G] [ChartedSpace E G]
  [Group G] [LieGroup (𝓘(ℝ,E)) ⊤ G]
  {a : ℕ} {T : ComplexTriangularAdjoint (GroupLieAlgebra (𝓘(ℝ,E)) G) a}
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ,E)) G)} [H.IsCartanSubalgebra]
  {Exp : GroupLieAlgebra (𝓘(ℝ,E)) G → G}

namespace ComplexWeightFactorModel
variable (F : ComplexWeightFactorModel T H Exp) (hExp : IsGroupExponential Exp)
attribute [local instance] semidirectProductTopology

theorem rotationFactorProduct_coordinates (n : F.N.carrier) (d : F.D.carrier) :
    F.smoothRotationalModificationHomeomorph hExp
      (F.nilpotentFactorToRotation hExp n * F.cartanFactorToRotation hExp d) =
        F.inclusionN n * F.inclusionD d :=
  rotationalTwistLift_mul_left _ _ _ _ _ n _ (F.rotationCharacter_inclusionN n)

theorem rotationFactorProduct_surjective :
    Function.Surjective (fun p : F.N.carrier × F.D.carrier =>
      F.nilpotentFactorToRotation hExp p.1 * F.cartanFactorToRotation hExp p.2) := by
  exact surjective_of_coordinates (F.smoothRotationalModificationHomeomorph hExp)
    (F.smoothRotationalModificationHomeomorph hExp).injective _ _
    (fun p => F.rotationFactorProduct_coordinates hExp p.1 p.2) F.surjective

end ComplexWeightFactorModel
end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_RotationExponentialProduct
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Global exponential factor coordinates and cancellation -/

noncomputable section
namespace PolycyclicRecognition
open scoped Manifold

variable {E G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MetricSpace G] [ChartedSpace E G]
  [Group G] [LieGroup (𝓘(ℝ,E)) ⊤ G]
  {a : ℕ} {T : ComplexTriangularAdjoint (GroupLieAlgebra (𝓘(ℝ,E)) G) a}
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ,E)) G)} [H.IsCartanSubalgebra]
  {Exp : GroupLieAlgebra (𝓘(ℝ,E)) G → G}

namespace ComplexWeightFactorModel
variable (F : ComplexWeightFactorModel T H Exp) (hExp : IsGroupExponential Exp)
attribute [local instance] semidirectProductTopology

theorem rotationExponentialProduct_surjective :
    Function.Surjective (F.rotationExponentialProduct hExp) :=
  (F.rotationFactorProduct_surjective hExp).comp
    (F.expN_surjective.prodMap F.expD_surjective)

end ComplexWeightFactorModel
end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_RotationFactorParameter
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Local coordinates for the rotational graph from the original factors -/

noncomputable section
namespace PolycyclicRecognition
open scoped Manifold ContDiff

variable {E G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MetricSpace G] [ChartedSpace E G]
  [Group G] [LieGroup (𝓘(ℝ,E)) ⊤ G]
  {a : ℕ} {T : ComplexTriangularAdjoint (GroupLieAlgebra (𝓘(ℝ,E)) G) a}
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ,E)) G)} [H.IsCartanSubalgebra]
  {Exp : GroupLieAlgebra (𝓘(ℝ,E)) G → G}

namespace ComplexWeightFactorModel
variable (F : ComplexWeightFactorModel T H Exp) (hExp : IsGroupExponential Exp)
attribute [local instance] semidirectProductTopology

theorem rotationFactorParameter_coordinates (v : E) :
    F.smoothRotationalModificationHomeomorph hExp (F.rotationFactorParameter hExp v) =
      F.factorParameter v := F.rotationFactorProduct_coordinates hExp _ _

theorem exists_rotationFactorParameter_chart :
    ∃ p : OpenPartialHomeomorph E (F.SmoothRotationalModification hExp),
      (0 : E) ∈ p.source ∧ p 0 = 1 ∧
        ∀ v ∈ p.source, p v = F.rotationFactorParameter hExp v := by
  apply exists_parameter_of_coordinate_homeomorph
    (F.smoothRotationalModificationHomeomorph hExp) rfl
    (F.rotationFactorParameter hExp) F.factorParameter
    (F.rotationFactorParameter_coordinates hExp) F.factorParameter_zero
  exact exists_manifold_local_parameter (d := ContinuousLinearEquiv.refl ℝ E)
    (F.contMDiff_factorParameter hExp) (F.hasMFDerivAt_factorParameter hExp)

end ComplexWeightFactorModel
end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_ShadowExponentialCoordinates
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.ComplexWeightFactorModel.smoothRotationExtensionTopologicalGroup _root_.OAI.PolycyclicRecognition.ComplexWeightFactorModel.smoothRotationalModificationSimplyConnected _root_.OAI.PolycyclicRecognition.ComplexWeightFactorModel.smoothRotationalModificationTopologicalGroup _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Linear coordinates for the two real-shadow exponential factors -/

noncomputable section
namespace PolycyclicRecognition
attribute [local instance 100] LieRing.ofAssociativeRing

variable {L A : Type} [LieRing L] [LieAlgebra ℝ L]
  [FiniteDimensional ℝ L]
  [NormedRing A] [NormedAlgebra ℝ A]
  {a : ℕ} (T : ComplexTriangularAdjoint L a)
  (H : LieSubalgebra ℝ L) [H.IsCartanSubalgebra]
  (j : CartanRealShadow T H →ₗ⁅ℝ⁆ A)

theorem shadowParameters_add : shadowKernelParameter T H j + shadowCartanParameter T H j =
    shadowRepresentationParameter T H j := by
  apply LinearMap.ext
  intro v
  change j (cartanRealShadowEquiv T H (T.kernelComponent H v)) +
    j (cartanRealShadowEquiv T H (T.cartanComponent H v)) = j (cartanRealShadowEquiv T H v)
  rw [← map_add, ← map_add, T.factorComponents_add H]

theorem shadowParameters_injective (hj : Function.Injective j) :
    Function.Injective (shadowKernelParameter T H j + shadowCartanParameter T H j) := by
  rw [shadowParameters_add]
  exact hj.comp (cartanRealShadowEquiv T H).injective

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_RotationRepresentedChart
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Concrete analytic representation coordinates for the rotational graph -/

noncomputable section
namespace PolycyclicRecognition
open scoped Manifold ContDiff
attribute [local instance 100] LieRing.ofAssociativeRing

variable {E G A : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MetricSpace G] [ChartedSpace E G]
  [Group G] [LieGroup (𝓘(ℝ,E)) ⊤ G]
  [NormedRing A] [NormedAlgebra ℝ A] [FiniteDimensional ℝ A]
  {a : ℕ} {T : ComplexTriangularAdjoint (GroupLieAlgebra (𝓘(ℝ,E)) G) a}
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ,E)) G)} [H.IsCartanSubalgebra]
  {Exp : GroupLieAlgebra (𝓘(ℝ,E)) G → G}

namespace ComplexWeightFactorModel
variable (F : ComplexWeightFactorModel T H Exp) (hExp : IsGroupExponential Exp)
attribute [local instance] semidirectProductTopology

theorem exists_rotation_representedLocalChart
    (j : CartanRealShadow T H →ₗ⁅ℝ⁆ A) (hj : Function.Injective j)
    (ρ : F.SmoothRotationalModification hExp →* Aˣ)
    (he : ∀ (x : T.kernelIdeal) (h : H),
      ρ (F.nilpotentFactorToRotation hExp (F.ExpN (F.N.equiv x)) *
        F.cartanFactorToRotation hExp (F.ExpD (F.D.equiv h))) =
        algebraExpUnit (j (cartanRealShadowEquiv T H x)) *
          algebraExpUnit (j (cartanRealShadowEquiv T H h))) :
    Nonempty (RepresentedLocalChart (E := E) ρ) := by
  apply representedLocalChart_of_exponential_localization ρ (F.rotationFactorParameter hExp)
    (shadowKernelParameter T H j).toContinuousLinearMap
    (shadowCartanParameter T H j).toContinuousLinearMap
    (shadowParameters_injective T H j hj) _ (F.exists_rotationFactorParameter_chart hExp)
  intro v
  exact he (T.kernelComponent H v) (T.cartanComponent H v)

end ComplexWeightFactorModel
end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_RotationTriangulableModel
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The analytic real-triangulable model of the actual rotational graph -/

noncomputable section
namespace PolycyclicRecognition
open scoped Manifold Matrix.Norms.Operator
attribute [local instance 100] LieRing.ofAssociativeRing

variable {E G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MetricSpace G] [ChartedSpace E G]
  [Group G] [LieGroup (𝓘(ℝ,E)) ⊤ G]
  [SimplyConnectedSpace G] [SecondCountableTopology G] [Group.IsSolvable G]
  {a : ℕ} {T : ComplexTriangularAdjoint (GroupLieAlgebra (𝓘(ℝ,E)) G) a}
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ,E)) G)} [H.IsCartanSubalgebra]
  {Exp : GroupLieAlgebra (𝓘(ℝ,E)) G → G}

namespace ComplexWeightFactorModel
variable (F : ComplexWeightFactorModel T H Exp) (hExp : IsGroupExponential Exp)
attribute [local instance] semidirectProductTopology

omit [SimplyConnectedSpace G] [SecondCountableTopology G] in
theorem smoothRotationalModification_solvable : Group.IsSolvable (F.SmoothRotationalModification hExp) := by
  let solv : Group.IsSolvable (G ⋊[F.factorCompactRotationAction hExp]
      realRotationTorus (GroupLieAlgebra (𝓘(ℝ,E)) G) H) :=
    semidirect_solvable (F.factorCompactRotationAction hExp)
  infer_instance

theorem exists_triangulable_rotation_model_oai :
    ∃ S : SimplyConnectedSolvableLieModel, IsRealTriangulable S ∧
      Nonempty (ProperCocompactHom S.carrier
        (G ⋊[F.factorCompactRotationAction hExp]
          realRotationTorus (GroupLieAlgebra (𝓘(ℝ,E)) G) H)) := by
  let metric : MetricSpace (F.SmoothRotationalModification hExp) :=
    F.smoothRotationalModificationMetric hExp
  let countable : SecondCountableTopology (F.SmoothRotationalModification hExp) :=
    (F.smoothRotationalModificationHomeomorph hExp).secondCountableTopology
  let solv : Group.IsSolvable (F.SmoothRotationalModification hExp) :=
    F.smoothRotationalModification_solvable hExp
  apply exists_triangulable_model_of_representations (E := E)
    (F.smoothModificationToRotationExtension hExp)
  exact exists_represented_matrix_group
    (fun _ j => Function.Injective j ∧ (∀ x, (j x).IsUpperTriangular) ∧
      (∀ x ∈ realShadowKernel T H, IsNilpotent (j x)))
    (fun x : T.kernelIdeal => cartanRealShadowEquiv T H x)
    (fun h : H => cartanRealShadowEquiv T H h)
    (F.rotationExponentialProduct hExp) (F.rotationExponentialProduct_surjective hExp)
    (F.exists_faithful_rotation_triangular_representation hExp)
    (fun _ _ hj => hj.2.1)
    (fun _ j hj ρ he => F.exists_rotation_representedLocalChart hExp j hj.1 ρ he)

end ComplexWeightFactorModel
end PolycyclicRecognition

end

end OAI
end

theorem solution : type_of% @OAI.PolycyclicRecognition.ComplexWeightFactorModel.exists_triangulable_rotation_model_oai := @OAI.PolycyclicRecognition.ComplexWeightFactorModel.exists_triangulable_rotation_model_oai
