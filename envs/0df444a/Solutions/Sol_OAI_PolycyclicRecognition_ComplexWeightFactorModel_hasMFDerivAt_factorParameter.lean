-- Prove2me | solution 1 for OAI.PolycyclicRecognition.ComplexWeightFactorModel.hasMFDerivAt_factorParameter
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-03T01:01:31.813147+00:00
-- url     : https://prove2.me/submissions/55530480-4544-4f72-8ad5-8b7275218839

import Mathlib
import Definitions.Def_PolycyclicRecognition
import Definitions.Def_OAIQ093D021
import Theorems.Thm_OAI_PolycyclicRecognition_ComplexWeightFactorModel_contMDiff_factorParameter

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_ComplexFactorParameters
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanRealShadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
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
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_SmoothExponentialDifferential
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The derivative of a smooth intrinsic exponential at zero -/

noncomputable section
namespace PolycyclicRecognition
open scoped Manifold ContDiff

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace G] [ChartedSpace E G]
  [Group G] [LieGroup (𝓘(ℝ,E)) ⊤ G]

/- Directional derivatives along linear curves determine the full derivative
of an already smooth map. -/
omit [FiniteDimensional ℝ E] [Group G] [LieGroup (𝓘(ℝ,E)) ⊤ G] in
theorem hasMFDerivAt_zero_of_smooth_linear_curves
    {f : E → G} (d : E →L[ℝ] E)
    (hs : ContMDiffAt (𝓘(ℝ,E)) (𝓘(ℝ,E)) ∞ f 0)
    (hc : ∀ v : E, HasMFDerivAt (𝓘(ℝ,ℝ)) (𝓘(ℝ,E))
      (fun t : ℝ => f (t • v)) 0
      (ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℝ ℝ) (d v))) :
    HasMFDerivAt (𝓘(ℝ,E)) (𝓘(ℝ,E)) f 0 d := by
  have hd := (hs.mdifferentiableAt (by simp)).hasMFDerivAt
  apply hd.congr_mfderiv
  apply ContinuousLinearMap.ext
  intro v
  change E at v
  let line : ℝ →L[ℝ] E := ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℝ ℝ) v
  have hl : HasMFDerivAt (𝓘(ℝ,ℝ)) (𝓘(ℝ,E)) (fun t : ℝ => t • v) 0 line :=
    line.hasMFDerivAt
  have hs' : ContMDiffAt (𝓘(ℝ,E)) (𝓘(ℝ,E)) ∞ f ((0 : ℝ) • v) := by
    rw [zero_smul]
    exact hs
  have hh := (hs'.mdifferentiableAt (by simp)).hasMFDerivAt.comp (0 : ℝ) hl
  have he := congrArg (fun k : ℝ →L[ℝ] E => k 1) (hasMFDerivAt_unique hh (hc v))
  change (mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,E)) f ((0 : ℝ) • v)) ((1 : ℝ) • v) = (1 : ℝ) • d v at he
  have he' : (mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,E)) f ((0 : ℝ) • v)) v = d v := by
    simpa only [one_smul] using he
  have hz := congrArg (fun z : E => (mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,E)) f z) v) (zero_smul ℝ v)
  exact hz.symm.trans he'

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_ComplexFactorLocalChart
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanRealShadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
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

theorem factorParameter_line (v : E) (t : ℝ) :
    F.factorParameter (t • v) =
      Exp (t • (T.kernelComponent H v : GroupLieAlgebra (𝓘(ℝ,E)) G)) *
        Exp (t • (T.cartanComponent H v : GroupLieAlgebra (𝓘(ℝ,E)) G)) := by
  change F.inclusionN (F.ExpN (F.N.equiv (T.kernelComponent H (t • v)))) *
    F.inclusionD (F.ExpD (F.D.equiv (T.cartanComponent H (t • v)))) = _
  rw [F.compatibleN,F.compatibleD]
  exact congrArg₂ (fun x y : GroupLieAlgebra (𝓘(ℝ, E)) G => Exp x * Exp y)
    (congrArg Subtype.val ((T.kernelComponent H).map_smul t v))
    (congrArg Subtype.val ((T.cartanComponent H).map_smul t v))

theorem hasMFDerivAt_factorParameter_line (hExp : IsGroupExponential Exp) (v : E) :
    HasMFDerivAt (𝓘(ℝ,ℝ)) (𝓘(ℝ,E)) (fun t : ℝ => F.factorParameter (t • v)) 0
      (ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℝ ℝ) v) := by
  rw [show (fun t : ℝ => F.factorParameter (t • v)) =
      (fun t => Exp (t • (T.kernelComponent H v : GroupLieAlgebra (𝓘(ℝ,E)) G)) *
        Exp (t • (T.cartanComponent H v : GroupLieAlgebra (𝓘(ℝ,E)) G))) from
    funext (F.factorParameter_line v)]
  have hc := PolycyclicRecognition.HasMFDerivAt.mul_at_one
    (hExp.hasMFDerivAt_zero (T.kernelComponent H v))
    (hExp.hasMFDerivAt_zero (T.cartanComponent H v))
    (by rw [zero_smul,hExp.map_zero]) (by rw [zero_smul,hExp.map_zero])
  have hd : (ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℝ ℝ)
      (T.kernelComponent H v : GroupLieAlgebra (𝓘(ℝ,E)) G) +
      ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℝ ℝ)
      (T.cartanComponent H v : GroupLieAlgebra (𝓘(ℝ,E)) G)) =
      ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℝ ℝ) v := by
    apply ContinuousLinearMap.ext
    intro t
    change t • (T.kernelComponent H v : GroupLieAlgebra (𝓘(ℝ,E)) G) +
      t • (T.cartanComponent H v : GroupLieAlgebra (𝓘(ℝ,E)) G) = t • v
    rw [← smul_add]
    exact congrArg (fun x : GroupLieAlgebra (𝓘(ℝ, E)) G => t • x)
      (T.factorComponents_add H v)
  exact hc.congr_mfderiv hd

theorem hasMFDerivAt_factorParameter_oai (hExp : IsGroupExponential Exp) :
    HasMFDerivAt (𝓘(ℝ,E)) (𝓘(ℝ,E)) F.factorParameter 0
      (ContinuousLinearMap.id ℝ E) := by
  apply hasMFDerivAt_zero_of_smooth_linear_curves _ (F.contMDiff_factorParameter hExp).contMDiffAt
  intro v
  exact F.hasMFDerivAt_factorParameter_line hExp v

end ComplexWeightFactorModel
end PolycyclicRecognition

end

end OAI
end

theorem solution : type_of% @OAI.PolycyclicRecognition.ComplexWeightFactorModel.hasMFDerivAt_factorParameter_oai := @OAI.PolycyclicRecognition.ComplexWeightFactorModel.hasMFDerivAt_factorParameter_oai
