-- Prove2me | solution 1 for OAI.PolycyclicRecognition.ComplexWeightFactorModel.rotationRepresentation_conjugation
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-03T01:09:42.826045+00:00
-- url     : https://prove2.me/submissions/a9c521be-00dc-4b4e-9f4f-706a295bc961

import Mathlib
import Definitions.Def_PolycyclicRecognition
import Definitions.Def_OAIQ093D023

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

variable {N D G : Type*} [Group N] [Group D] [Group G]

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
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_FiniteFrameDifferentiation
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Differentiability of a finite-dimensional frame -/

noncomputable section
namespace PolycyclicRecognition
open scoped Manifold

variable {X E F : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A finite basis makes pointwise differentiability sufficient for an
operator-valued frame. -/
theorem differentiableAt_clm_of_apply {A : X → E →L[ℝ] F} {x : X}
    (hA : ∀ v : E, DifferentiableAt ℝ (fun z => A z v) x) :
    DifferentiableAt ℝ A x := by
  let b := Module.finBasis ℝ E
  have heq : A = fun z => ∑ i, ContinuousLinearMap.smulRightL ℝ E F
      (b.coord i).toContinuousLinearMap (A z (b i)) := by
    funext z
    apply ContinuousLinearMap.ext
    intro v
    change A z v = (∑ i, ContinuousLinearMap.smulRightL ℝ E F
      (b.coord i).toContinuousLinearMap (A z (b i))) v
    simp only [sum_apply]
    change A z v = ∑ i, b.coord i v • A z (b i)
    simpa only [map_sum,map_smul,Module.Basis.coord_apply] using
      (congrArg (A z) (b.sum_repr v)).symm
  rw [heq]
  apply DifferentiableAt.fun_sum
  intro i _
  exact (ContinuousLinearMap.smulRightL ℝ E F (b.coord i).toContinuousLinearMap).differentiableAt.comp x
    (hA (b i))

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_ComplexPhaseDerivative
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The derivative of a Cartan phase along a real line -/

noncomputable section
namespace PolycyclicRecognition.ComplexCartan
open LieAlgebra LieModule Module

variable {L : Type*} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L]
  (H : LieSubalgebra ℂ L) [H.IsCartanSubalgebra]

attribute [local instance] OAI.PolycyclicRecognition.ComplexCartan.instNormedAddCommGroup_solutions
attribute [local instance] OAI.PolycyclicRecognition.ComplexCartan.instNormedSpaceComplex_solutions
attribute [local instance] OAI.PolycyclicRecognition.ComplexCartan.instNormedSpaceReal_solutions
theorem hasDerivAt_phase_line (h : H) (χ : Weight ℂ H L) :
    HasDerivAt (fun t : ℝ => phase H (t • h) χ) (imaginaryPart (χ h)) 0 := by
  have hd := ((hasDerivAt_id (0 : ℝ)).smul_const (imaginaryPart (χ h))).cexp
  have he (t : ℝ) : χ (t • h) = t • χ h :=
    (χ : H →ₗ[ℂ] ℂ).map_smul_of_tower t h
  simpa only [phase,he,map_smul,id_eq,zero_smul,
    Complex.exp_zero,one_smul,mul_one,one_mul] using hd

theorem hasDerivAt_rotation_line (h : H) (x : L) :
    HasDerivAt (fun t : ℝ => rotationLinear H (t • h) x) (imaginaryOperator H h x) 0 := by
  apply root_induction H (x := x)
  · intro χ v hv
    have hd := (hasDerivAt_phase_line H h χ).smul_const v
    simpa only [rotationLinear_apply H _ χ hv,imaginaryOperator_apply H h χ hv] using hd
  · simpa only [map_zero] using (hasDerivAt_const (0 : ℝ) (0 : L))
  · intro v w hv hw
    rw [map_add]
    exact (hv.add hw).congr_of_eventuallyEq
      (Filter.Eventually.of_forall (fun t => map_add (rotationLinear H (t • h)) v w))

end PolycyclicRecognition.ComplexCartan

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_WeightRotationDerivation
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanRealShadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.modelNilradicalLinearAction_apply _root_.OAI.PolycyclicRecognition.modelNilradicalRotation_apply _root_.OAI.PolycyclicRecognition.modelNilradicalRotation_mul _root_.OAI.PolycyclicRecognition.modelNilradicalRotation_one _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.realShadowCartanHom_apply _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The infinitesimal rotation factors through the complex weight quotient -/

noncomputable section
namespace PolycyclicRecognition
open LieAlgebra LieModule Module
open scoped TensorProduct

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {n : ℕ} (T : ComplexTriangularAdjoint L n)
  (H : LieSubalgebra ℝ L) [H.IsCartanSubalgebra]

namespace ComplexTriangularAdjoint

/-- No infinitesimal rotation remains on a nilpotent Cartan parameter. -/
theorem realImaginaryOperator_eq_zero (h : H) (hh : T.weightMap (h : L) = 0) (x : L) :
    realImaginaryOperator L H h x = 0 := by
  have hn := complex_ad_nilpotent (h : L) (T.ad_nilpotent h hh)
  apply complexificationLieHom_injective L
  change (1 : ℂ) ⊗ₜ[ℝ] realImaginaryOperator L H h x = 1 ⊗ₜ[ℝ] (0 : L)
  rw [realImaginaryOperator_complexify,TensorProduct.tmul_zero]
  apply ComplexCartan.root_induction (complexifiedSubalgebra L H)
    (p := fun v => ComplexCartan.imaginaryOperator (complexifiedSubalgebra L H)
      (realCartanInComplex L H h) v = 0) (x := (1 : ℂ) ⊗ₜ[ℝ] x)
  · intro χ v hv
    rw [ComplexCartan.imaginaryOperator_apply _ _ χ hv]
    have hz := χ.apply_eq_zero_of_isNilpotent (realCartanInComplex L H h) hn
    rw [hz,map_zero,zero_smul]
  · simp
  · intro v w hv hw
    simp only [map_add,hv,hw,add_zero]

theorem realImaginaryOperator_eq_of_weightMap_eq (h k : H)
    (hh : T.weightMap (h : L) = T.weightMap (k : L)) (x : L) :
    realImaginaryOperator L H h x = realImaginaryOperator L H k x := by
  have hz : T.weightMap ((h-k : H) : L) = 0 := by
    change T.weightMap ((h : L) - k) = 0
    rw [map_sub,hh,sub_self]
  have he := realImaginaryOperator_add L H (h-k) k x
  rw [sub_add_cancel,T.realImaginaryOperator_eq_zero H (h-k) hz x,zero_add] at he
  exact he

@[simp] theorem weightImaginaryAction_cartan (h : H) (x : L) :
    T.weightImaginaryAction H (h : L) x = realImaginaryOperator L H h x := by
  apply T.realImaginaryOperator_eq_of_weightMap_eq H
  exact T.cartanWeightSection_weight H _

end ComplexTriangularAdjoint
end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_RealPhaseDerivative
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The real infinitesimal phase on the group model space -/

noncomputable section
namespace PolycyclicRecognition
open scoped Manifold TensorProduct

variable {E G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace G] [ChartedSpace E G]
  [Group G] [LieGroup (𝓘(ℝ,E)) ⊤ G]
  (H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ,E)) G)) [H.IsCartanSubalgebra]

attribute [local instance] OAI.PolycyclicRecognition.instNormedAddCommGroupTensorProductRealComplexGroupLieAlgebraModelWithCornersSelf_solutions
attribute [local instance] OAI.PolycyclicRecognition.instNormedSpaceComplexTensorProductRealGroupLieAlgebraModelWithCornersSelf_solutions
attribute [local instance] OAI.PolycyclicRecognition.instNormedSpaceRealTensorProductComplexGroupLieAlgebraModelWithCornersSelf_solutions
theorem hasDerivAt_realPhase_line (h : H) (x : GroupLieAlgebra (𝓘(ℝ,E)) G) :
    HasDerivAt (fun t : ℝ =>
      (tangentTorusUnitAction H (realPhaseVector (GroupLieAlgebra (𝓘(ℝ,E)) G) H (t • h)) : E →L[ℝ] E) x)
      (show E from realImaginaryOperator (GroupLieAlgebra (𝓘(ℝ,E)) G) H h x) 0 := by
  let P : (ℂ ⊗[ℝ] GroupLieAlgebra (𝓘(ℝ,E)) G) →ₗ[ℝ] E :=
    complexificationRealPart (GroupLieAlgebra (𝓘(ℝ,E)) G)
  have hc := ComplexCartan.hasDerivAt_rotation_line
    (complexifiedSubalgebra (GroupLieAlgebra (𝓘(ℝ,E)) G) H)
    (realCartanInComplex (GroupLieAlgebra (𝓘(ℝ,E)) G) H h) ((1 : ℂ) ⊗ₜ[ℝ] x)
  have hd := P.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt 0 hc
  apply hd.congr_of_eventuallyEq
  exact Filter.Eventually.of_forall (fun t => by
    change _ = P (ComplexCartan.rotationLinear
      (complexifiedSubalgebra (GroupLieAlgebra (𝓘(ℝ,E)) G) H)
      (t • realCartanInComplex (GroupLieAlgebra (𝓘(ℝ,E)) G) H h) ((1 : ℂ) ⊗ₜ[ℝ] x))
    rw [← realCartanInComplex_real_smul]
    rfl)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_RealPhaseExponential
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Compact Cartan rotations as exponentials of their imaginary derivations -/

noncomputable section
namespace PolycyclicRecognition
open scoped Manifold

variable {E G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace G] [ChartedSpace E G]
  [Group G] [LieGroup (𝓘(ℝ,E)) ⊤ G]
  (H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ,E)) G)) [H.IsCartanSubalgebra]

theorem tangentPhase_eq_exp (h : H) (t : ℝ) :
    (tangentTorusUnitAction H
      (realPhaseVector (GroupLieAlgebra (𝓘(ℝ,E)) G) H (t • h)) : E →L[ℝ] E) =
      NormedSpace.exp (t • tangentImaginaryOperator H h) := by
  let L := GroupLieAlgebra (𝓘(ℝ,E)) G
  let R : ℝ → E →L[ℝ] E := fun s =>
    tangentTorusUnitAction H (realPhaseVector L H (s • h))
  let line : ℝ →ₗ[ℝ] H := LinearMap.toSpanSingleton ℝ H h
  let q := (realPhaseHom L H).comp line.toAddMonoidHom.toMultiplicative
  let U : Multiplicative ℝ →* (E →L[ℝ] E) :=
    (Units.coeHom (E →L[ℝ] E)).comp ((tangentTorusUnitAction H).comp q)
  have hR (s : ℝ) : R s = U (Multiplicative.ofAdd s) := rfl
  have hzero : R 0 = 1 := by
    rw [hR]
    exact U.map_one
  have hadd (s u : ℝ) : R (s+u) = R s * R u := by
    rw [hR, hR, hR]
    exact U.map_mul (Multiplicative.ofAdd s) (Multiplicative.ofAdd u)
  have hd := (differentiableAt_clm_of_apply (A := R)
    (fun v => (hasDerivAt_realPhase_line H h v).differentiableAt)).hasDerivAt
  have he : deriv R 0 = tangentImaginaryOperator H h := by
    ext v
    have hv := hd.clm_apply (hasDerivAt_const (0 : ℝ) v)
    have hp := hasDerivAt_realPhase_line H h v
    have hh := hv.unique hp
    change (deriv R 0) v =
      (show E from realImaginaryOperator (GroupLieAlgebra (𝓘(ℝ,E)) G) H h v)
    simpa only [map_zero, add_zero] using hh
  rw [he] at hd
  exact oneParameter_eq_exp hzero hadd hd t

theorem tangentPhase_inv_eq_exp (h : H) :
    (tangentTorusUnitAction H
      (realPhaseVector (GroupLieAlgebra (𝓘(ℝ,E)) G) H h)⁻¹ : E →L[ℝ] E) =
      NormedSpace.exp (-tangentImaginaryOperator H h) := by
  have he : realPhaseVector (GroupLieAlgebra (𝓘(ℝ,E)) G) H (-h) =
      (realPhaseVector (GroupLieAlgebra (𝓘(ℝ,E)) G) H h)⁻¹ :=
    (realPhaseHom (GroupLieAlgebra (𝓘(ℝ,E)) G) H).map_inv (Multiplicative.ofAdd h)
  simpa only [neg_one_smul, he] using tangentPhase_eq_exp H h (-1)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_RealShadowCartan
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The unchanged Cartan factor and its corrected adjoint action -/

noncomputable section
namespace PolycyclicRecognition
open LieAlgebra Module

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {a : ℕ} (T : ComplexTriangularAdjoint L a)
  (H : LieSubalgebra ℝ L) [H.IsCartanSubalgebra]

set_option maxHeartbeats 1000000 in
/-- The two operators whose exponentials occur in the rotational correction commute. -/
theorem realImaginaryOperator_commutes_ad (h : H) :
    Commute (realImaginaryOperator L H h) (ad ℝ L (h : L)) := by
  ext x
  change realImaginaryOperator L H h ⁅(h : L),x⁆ =
    ⁅(h : L),realImaginaryOperator L H h x⁆
  rw [realImaginaryOperator_lie, realImaginaryOperator_cartan, zero_lie, zero_add]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanTangentConjugation
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The corrected adjoint in the original tangent coordinates -/

noncomputable section
namespace PolycyclicRecognition
open scoped Manifold
attribute [local instance 100] LieRing.ofAssociativeRing

variable {E G A : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace G] [ChartedSpace E G]
  [Group G] [LieGroup (𝓘(ℝ,E)) ⊤ G]
  [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
  {a : ℕ} (T : ComplexTriangularAdjoint (GroupLieAlgebra (𝓘(ℝ,E)) G) a)
  (H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ,E)) G)) [H.IsCartanSubalgebra]

set_option maxHeartbeats 1000000 in
theorem realShadow_representation_rotated_adjoint
    {Exp : GroupLieAlgebra (𝓘(ℝ,E)) G → G} (hExp : IsGroupExponential Exp)
    (j : CartanRealShadow T H →ₗ⁅ℝ⁆ A) (h : H)
    (y : GroupLieAlgebra (𝓘(ℝ,E)) G) :
    j (cartanRealShadowEquiv T H
      (realTorusOperator (GroupLieAlgebra (𝓘(ℝ,E)) G) H
        (realPhaseVector (GroupLieAlgebra (𝓘(ℝ,E)) G) H h)⁻¹
        (adjointLinearMap (E := E) (Exp h) y))) =
      NormedSpace.exp (j (cartanRealShadowEquiv T H h)) *
        j (cartanRealShadowEquiv T H y) *
          NormedSpace.exp (-j (cartanRealShadowEquiv T H h)) := by
  let L := GroupLieAlgebra (𝓘(ℝ,E)) G
  let J : E →L[ℝ] A := (show E →ₗ[ℝ] A from
    j.toLinearMap.comp (cartanRealShadowEquiv T H).toLinearMap).toContinuousLinearMap
  let B := groupAdjointOperator (E := E) (G := G) h
  let C := tangentImaginaryOperator H h
  let S := B - C
  have hinter (x : E) : J (S x) =
      adjointOperator (j (cartanRealShadowEquiv T H h)) (J x) := by
    have hb : cartanRealShadowEquiv T H (S x) =
        ⁅cartanRealShadowEquiv T H h,cartanRealShadowEquiv T H x⁆ := by
      let z : L := x
      change cartanRealShadowEquiv T H
          (⁅(h : L), z⁆ - realImaginaryOperator L H h z) =
        ⁅cartanRealShadowEquiv T H h, cartanRealShadowEquiv T H z⁆
      apply (cartanRealShadowEquiv T H).symm.injective
      rw [(cartanRealShadowEquiv T H).symm_apply_apply, cartanRealShadow_bracket,
        T.weightImaginaryAction_cartan, weightImaginaryAction_apply_cartan, add_zero]
    change j (cartanRealShadowEquiv T H (S x)) = _
    rw [hb]
    exact j.map_lie _ _
  have hc : Commute C B := by
    ext x
    have hh := LinearMap.congr_fun (realImaginaryOperator_commutes_ad (L := L) H h).eq x
    exact hh
  have hprod : NormedSpace.exp (-C) * NormedSpace.exp B = NormedSpace.exp S := by
    let : NormedAlgebra ℚ (E →L[ℝ] E) := NormedAlgebra.restrictScalars ℚ ℝ _
    rw [← NormedSpace.exp_add_of_commute hc.neg_left]
    congr 1
    dsimp only [S]
    abel
  have ha := adjointLinearMap_exponential hExp (h : L) 1
  simp only [one_smul] at ha
  have hp := tangentPhase_inv_eq_exp H h
  change j (cartanRealShadowEquiv T H
    ((tangentTorusUnitAction H (realPhaseVector L H h)⁻¹ : E →L[ℝ] E)
      (adjointLinearMap (E := E) (Exp h) y))) = _
  rw [hp, ha]
  have he := congrArg (fun D : E →L[ℝ] E => J (D y)) hprod
  exact he.trans ((exp_intertwine_apply J S _ hinter y).trans
    (exp_adjointOperator_apply _ _))

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_WeightRotationCharacter
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanRealShadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.ComplexTriangularAdjoint.weightImaginaryAction_annihilate _root_.OAI.PolycyclicRecognition.ComplexTriangularAdjoint.weightImaginaryAction_cartan _root_.OAI.PolycyclicRecognition.ComplexTriangularAdjoint.weightImaginaryAction_kernel _root_.OAI.PolycyclicRecognition.ComplexTriangularAdjoint.weightImaginaryAction_lie _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.modelNilradicalLinearAction_apply _root_.OAI.PolycyclicRecognition.modelNilradicalRotation_apply _root_.OAI.PolycyclicRecognition.modelNilradicalRotation_mul _root_.OAI.PolycyclicRecognition.modelNilradicalRotation_one _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.realImaginaryOperator_complexify _root_.OAI.PolycyclicRecognition.realShadowCartanHom_apply _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A compact rotation character on the actual adjoint-weight quotient -/

noncomputable section
namespace PolycyclicRecognition

open Module LieAlgebra LieModule
open scoped TensorProduct

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {n : ℕ} (T : ComplexTriangularAdjoint L n)
  (H : LieSubalgebra ℝ L) [H.IsCartanSubalgebra]

namespace ComplexTriangularAdjoint

/-- The rotations do not depend on the chosen Cartan representative. -/
theorem realPhaseVector_eq_of_weightMap_eq (h k : H)
    (hh : T.weightMap (h : L) = T.weightMap (k : L)) :
    realPhaseVector L H h = realPhaseVector L H k := by
  have hd : ((h - k : H) : L) ∈ T.kernelIdeal := by
    change T.weightMap ((h : L) - k) = 0
    rw [map_sub, hh, sub_self]
  have hn := complex_ad_nilpotent ((h - k : H) : L) (T.ad_nilpotent _ hd)
  have he : realCartanInComplex L H (h - k) =
      realCartanInComplex L H h - realCartanInComplex L H k := by
    apply Subtype.ext
    change (1 : ℂ) ⊗ₜ[ℝ] ((h : L) - k) = _
    exact TensorProduct.tmul_sub _ _ _
  apply Subtype.ext
  apply Subtype.ext
  funext χ
  have hz := χ.apply_eq_zero_of_isNilpotent (realCartanInComplex L H (h - k)) hn
  rw [he, map_sub, sub_eq_zero] at hz
  apply Subtype.ext
  change ComplexCartan.phase (complexifiedSubalgebra L H) (realCartanInComplex L H h) χ =
    ComplexCartan.phase (complexifiedSubalgebra L H) (realCartanInComplex L H k) χ
  unfold ComplexCartan.phase
  rw [hz]

@[simp] theorem weightRotationCharacter_cartan (h : H) :
    T.weightRotationCharacter H (Multiplicative.ofAdd (T.weightMap.rangeRestrict (h : L))) =
      realPhaseVector L H h := by
  apply T.realPhaseVector_eq_of_weightMap_eq H
  exact T.cartanWeightSection_weight H _

end ComplexTriangularAdjoint
end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_FactorRotationCharacter
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanRealShadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The invariant compact character for the actual Cartan factors -/

noncomputable section
namespace PolycyclicRecognition
open scoped Manifold

variable {E G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MetricSpace G] [ChartedSpace E G] [Group G]
  [LieGroup (𝓘(ℝ,E)) ⊤ G]
  {a : ℕ} {T : ComplexTriangularAdjoint (GroupLieAlgebra (𝓘(ℝ,E)) G) a}
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ,E)) G)} [H.IsCartanSubalgebra]
  {Exp : GroupLieAlgebra (𝓘(ℝ,E)) G → G}

namespace ComplexWeightFactorModel
variable (F : ComplexWeightFactorModel T H Exp)

/- The actual quotient character followed by its compact rotational part. -/

theorem rotationCharacter_exp (x : GroupLieAlgebra (𝓘(ℝ,E)) G) :
    F.rotationCharacter (Exp x) =
      T.weightRotationCharacter H (Multiplicative.ofAdd (T.weightMap.rangeRestrict x)) := by
  exact congrArg (T.weightRotationCharacter H) (Multiplicative.ext (F.weightCharacter_exp x))

theorem rotationCharacter_cartan (h : H) :
    F.rotationCharacter (Exp h) = realPhaseVector (GroupLieAlgebra (𝓘(ℝ,E)) G) H h :=
  (F.rotationCharacter_exp h).trans (T.weightRotationCharacter_cartan H h)

end ComplexWeightFactorModel
end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_SmoothIndividualRotations
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanRealShadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Differentiating the individual compact rotations -/

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
  (β : realRotationTorus (GroupLieAlgebra (𝓘(ℝ,E)) G) H →* MulAut G)
  (hβ : ∀ z (x : T.kernelIdeal) d,
    β z (F.inclusionN (F.ExpN (F.N.equiv x)) * F.inclusionD d) =
      F.inclusionN (F.ExpN (F.N.equiv (T.nilradicalRotation H z x))) * F.inclusionD d)

include hβ in
theorem rotation_exp_nilradical
    (z : realRotationTorus (GroupLieAlgebra (𝓘(ℝ,E)) G) H) (x : T.kernelIdeal) :
    β z (Exp x) = Exp (T.nilradicalRotation H z x) := by
  have hh := hβ z x (1 : F.D.carrier)
  simpa only [map_one,mul_one,F.compatibleN] using hh

end ComplexWeightFactorModel
end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_RotationalTwistConjugation
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Conjugation in the inverse-character graph -/

noncomputable section
namespace PolycyclicRecognition

variable {N D G K : Type*} [Group N] [Group D] [Group G] [CommGroup K]
  [TopologicalSpace G] [TopologicalSpace K]
  (α : K →* MulAut G) (τ : G →* K) (hinv : ∀ k g, τ (α k g) = τ g)
  (iN : N →* G) (iD : D →* G)
  (hN : ∀ n m, α ((τ (iN n))⁻¹) (iN m) = iN m)
  (hD : ∀ d e, α ((τ (iD d))⁻¹) (iD e) = iD e)

omit [TopologicalSpace G] [TopologicalSpace K] in
/-- The graph conjugation is the original conjugation followed by the
inverse compact rotation. -/
theorem rotationalTwistLift_conjugation_left (d : D) (n : N)
    (hn : τ (iN n) = 1) :
    ((rotationalTwistLift α τ hinv iD hD d *
      rotationalTwistLift α τ hinv iN hN n *
      (rotationalTwistLift α τ hinv iD hD d)⁻¹).val.left) =
      α ((τ (iD d))⁻¹) (iD d * iN n * (iD d)⁻¹) := by
  change (iD d * α ((τ (iD d))⁻¹) (iN n)) *
    α ((τ (iD d))⁻¹ * (τ (iN n))⁻¹)
      (α (((τ (iD d))⁻¹)⁻¹) ((iD d)⁻¹)) = _
  rw [hn, inv_one, mul_one, ← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one]
  change (iD d * α ((τ (iD d))⁻¹) (iN n)) * (iD d)⁻¹ = _
  rw [(α ((τ (iD d))⁻¹)).map_mul, (α ((τ (iD d))⁻¹)).map_mul,
    (α ((τ (iD d))⁻¹)).map_inv, hD d d]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_RotationFactorAction
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The Cartan action on the nilpotent factor of the rotational graph -/

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

theorem rotationFactorAction_conjugation (d : F.D.carrier) (n : F.N.carrier) :
    F.nilpotentFactorToRotation hExp (F.rotationFactorAction hExp d n) =
      F.cartanFactorToRotation hExp d * F.nilpotentFactorToRotation hExp n *
        (F.cartanFactorToRotation hExp d)⁻¹ :=
  conjugationLiftOfNormal_spec _ _ _ _ d n

theorem rotationFactorAction_exponential (h : H) (x : T.kernelIdeal) :
    F.rotationFactorAction hExp (F.ExpD (F.D.equiv h)) (F.ExpN (F.N.equiv x)) =
      F.ExpN (F.N.equiv (T.nilradicalRotation H
        (realPhaseVector (GroupLieAlgebra (𝓘(ℝ,E)) G) H h)⁻¹
        ⟨adjointLinearMap (E := E) (Exp h) (x : GroupLieAlgebra (𝓘(ℝ,E)) G),
          cartan_conjugation_mem hExp h x⟩)) := by
  apply F.closedN.injective
  have hc := congrArg (F.smoothRotationalModificationHomeomorph hExp)
    (F.rotationFactorAction_conjugation hExp
      (F.ExpD (F.D.equiv h)) (F.ExpN (F.N.equiv x)))
  have ht := rotationalTwistLift_conjugation_left
    (F.factorCompactRotationAction hExp) F.rotationCharacter
    (F.factorCompactRotationAction_invariant hExp) F.inclusionN F.inclusionD
    (F.inverse_rotation_fixes_nilpotent_factor hExp)
    (F.inverse_rotation_fixes_cartan_factor hExp)
    (F.ExpD (F.D.equiv h)) (F.ExpN (F.N.equiv x))
    (F.rotationCharacter_nilradical x)
  have he := hc.trans ht
  change F.inclusionN (F.rotationFactorAction hExp _ _) = _ at he
  let y : T.kernelIdeal := ⟨adjointLinearMap (E := E) (Exp h)
    (x : GroupLieAlgebra (𝓘(ℝ,E)) G), cartan_conjugation_mem hExp h x⟩
  have hchar := (congrArg F.rotationCharacter (F.compatibleD h)).trans
    (F.rotationCharacter_cartan h)
  have harg : F.inclusionD (F.ExpD (F.D.equiv h)) *
      F.inclusionN (F.ExpN (F.N.equiv x)) * (F.inclusionD (F.ExpD (F.D.equiv h)))⁻¹ =
      Exp (y : GroupLieAlgebra (𝓘(ℝ,E)) G) := by
    rw [F.compatibleD h, F.compatibleN x]
    exact conjugation_exponential hExp (Exp h) x
  have hrotate := congrArg₂ (fun z g => F.factorCompactRotationAction hExp z⁻¹ g)
    hchar harg
  exact he.trans (hrotate.trans ((F.rotation_exp_nilradical (F.factorCompactRotationAction hExp)
    (F.factorCompactRotationAction_formula hExp) _ y).trans (F.compatibleN _).symm))

end ComplexWeightFactorModel
end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_RotationRepresentationRelations
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Relations between the integrated representations of the two factors -/

noncomputable section
namespace PolycyclicRecognition
open scoped Manifold
attribute [local instance 100] LieRing.ofAssociativeRing

private theorem forall_of_two_surjections {X Y N D : Type*}
    (f : X → N) (g : Y → D) (hf : Function.Surjective f) (hg : Function.Surjective g)
    (P : N → D → Prop) (hP : ∀ x y, P (f x) (g y)) : ∀ n d, P n d := by
  intro n d
  obtain ⟨x,rfl⟩ := hf n
  obtain ⟨y,rfl⟩ := hg d
  exact hP x y

variable {E G A : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MetricSpace G] [ChartedSpace E G]
  [Group G] [LieGroup (𝓘(ℝ,E)) ⊤ G]
  [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
  {a : ℕ} {T : ComplexTriangularAdjoint (GroupLieAlgebra (𝓘(ℝ,E)) G) a}
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ,E)) G)} [H.IsCartanSubalgebra]
  {Exp : GroupLieAlgebra (𝓘(ℝ,E)) G → G}

namespace ComplexWeightFactorModel
variable (F : ComplexWeightFactorModel T H Exp) (hExp : IsGroupExponential Exp)
  (j : CartanRealShadow T H →ₗ⁅ℝ⁆ A)
  (ρN : F.N.carrier →* Aˣ) (ρD : F.D.carrier →* Aˣ)
  (hN : ∀ x : T.kernelIdeal, ρN (F.ExpN (F.N.equiv x)) =
    algebraExpUnit (j (cartanRealShadowEquiv T H x)))
  (hD : ∀ h : H, ρD (F.ExpD (F.D.equiv h)) =
    algebraExpUnit (j (cartanRealShadowEquiv T H h)))
attribute [local instance] semidirectProductTopology

include hN hD in
theorem rotationRepresentation_conjugation_oai :
    ∀ d n, ρN (F.rotationFactorAction hExp d n) = ρD d * ρN n * (ρD d)⁻¹ := by
  apply forall_of_two_surjections (fun h : H => F.ExpD (F.D.equiv h))
    (fun x : T.kernelIdeal => F.ExpN (F.N.equiv x)) F.expD_surjective F.expN_surjective
  intro h x
  rw [F.rotationFactorAction_exponential hExp, hN, hD, hN]
  have he := realShadow_representation_rotated_adjoint T H hExp j h x
  change j (cartanRealShadowEquiv T H
    ((T.nilradicalRotation H (realPhaseVector (GroupLieAlgebra (𝓘(ℝ,E)) G) H h)⁻¹
      ⟨adjointLinearMap (E := E) (Exp h) (x : GroupLieAlgebra (𝓘(ℝ,E)) G),
        cartan_conjugation_mem hExp h x⟩) : GroupLieAlgebra (𝓘(ℝ,E)) G)) = _ at he
  rw [he]
  exact algebraExpUnit_conj (algebraExpUnit (j (cartanRealShadowEquiv T H h)))
    (j (cartanRealShadowEquiv T H x))

end ComplexWeightFactorModel
end PolycyclicRecognition

end

end OAI
end

theorem solution : type_of% @OAI.PolycyclicRecognition.ComplexWeightFactorModel.rotationRepresentation_conjugation_oai := @OAI.PolycyclicRecognition.ComplexWeightFactorModel.rotationRepresentation_conjugation_oai
