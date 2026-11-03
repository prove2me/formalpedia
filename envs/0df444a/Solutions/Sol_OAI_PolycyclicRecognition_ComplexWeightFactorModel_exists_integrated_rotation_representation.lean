-- Prove2me | solution 1 for OAI.PolycyclicRecognition.ComplexWeightFactorModel.exists_integrated_rotation_representation
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-03T01:08:57.814713+00:00
-- url     : https://prove2.me/submissions/c8510a5b-1697-4193-8073-3a100795abc5

import Mathlib
import Definitions.Def_PolycyclicRecognition
import Definitions.Def_OAIQ093D023
import Theorems.Thm_OAI_PolycyclicRecognition_ComplexWeightFactorModel_rotationRepresentation_conjugation

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
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_UnitsLieAlgebra
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual tangent Lie algebra of algebra units

Differentiating the inclusion identifies the tangent Lie algebra with the
commutator algebra. This permits the proved nilpotent integration theorem
to target matrix units directly.
-/

noncomputable section
namespace PolycyclicRecognition

open scoped Manifold ContDiff
attribute [local instance 100] LieRing.ofAssociativeRing

variable (A : Type*) [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

variable [FiniteDimensional ℝ A]

theorem groupExponential_units (x : GroupLieAlgebra (𝓘(ℝ, A)) Aˣ) :
    groupExponential x = algebraExpUnit (unitsLieEquiv A x) :=
  hom_exp_eq_algebraExpUnit groupExponential_isGroupExponential (MonoidHom.id Aˣ)
    (unitsLieHom A).toLinearMap.toContinuousLinearMap
    (hasMFDerivAt_unitsHomLieDifferential (MonoidHom.id Aˣ) Units.contMDiff_val) x

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_NilpotentAlgebraRepresentation
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.CartanFactorModel.heightRay_zero _root_.OAI.PolycyclicRecognition.CartanFactorModel.realScaleProfile_apply _root_.OAI.PolycyclicRecognition.CartanFactorModel.sampledProbeProfile_apply _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.modelNilradicalLinearAction_apply _root_.OAI.PolycyclicRecognition.modelNilradicalRotation_apply _root_.OAI.PolycyclicRecognition.modelNilradicalRotation_mul _root_.OAI.PolycyclicRecognition.modelNilradicalRotation_one _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Integrating nilpotent factor representations into matrix units

The source model is arbitrary and the represented matrices need not be
nilpotent. Only the source Lie algebra is nilpotent.
-/

noncomputable section
namespace PolycyclicRecognition

open scoped Manifold ContDiff
attribute [local instance 100] LieRing.ofAssociativeRing

theorem NilpotentLieModel.exists_algebra_representation
    {L A : Type} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
    [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A] [FiniteDimensional ℝ A]
    (N : NilpotentLieModel L) (hn : LieRing.IsNilpotent L) (j : L →ₗ⁅ℝ⁆ A) :
    ∃ ρ : N.carrier →* Aˣ,
      ContMDiff (𝓘(ℝ, N.modelSpace)) (𝓘(ℝ, A)) ∞ ρ ∧
      ∀ (ExpN : GroupLieAlgebra (𝓘(ℝ, N.modelSpace)) N.carrier → N.carrier),
        IsGroupExponential ExpN → ∀ x : L,
          ρ (ExpN (N.equiv x)) = algebraExpUnit (j x) := by
  let f := (unitsLieEquiv A).symm.toLieHom.comp (j.comp N.equiv.symm.toLieHom)
  have hnN : LieRing.IsNilpotent (GroupLieAlgebra (𝓘(ℝ, N.modelSpace)) N.carrier) :=
    N.equiv.nilpotent_iff_equiv_nilpotent.mp hn
  obtain ⟨ρ, hρ, hderiv⟩ := nilpotentSmoothIntegrationInput (E := A) (G := Aˣ) L N
    inferInstance hnN f
  refine ⟨ρ, hρ, ?_⟩
  intro ExpN hExpN x
  have h := hExpN.map_of_mdifferentiable groupExponential_isGroupExponential ρ
    (hρ.mdifferentiable (by simp)) (N.equiv x)
  rw [hderiv, groupExponential_units] at h
  simpa only [f, LieHom.comp_apply, LieEquiv.coe_toLieHom,
    N.equiv.symm_apply_apply, LieEquiv.apply_symm_apply] using h

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_NilpotentContinuousRepresentation
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The continuous exponential formula needed for representation descent -/

noncomputable section
namespace PolycyclicRecognition
open scoped Manifold
attribute [local instance 100] LieRing.ofAssociativeRing

theorem NilpotentLieModel.exists_continuous_algebra_representation
    {L A : Type} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
    [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A] [FiniteDimensional ℝ A]
    (N : NilpotentLieModel L) (hn : LieRing.IsNilpotent L) (j : L →ₗ⁅ℝ⁆ A)
    (ExpN : GroupLieAlgebra (𝓘(ℝ,N.modelSpace)) N.carrier → N.carrier)
    (hExpN : IsGroupExponential ExpN) :
    ∃ ρ : N.carrier →* Aˣ, Continuous ρ ∧
      ∀ x : L, ρ (ExpN (N.equiv x)) = algebraExpUnit (j x) := by
  obtain ⟨ρ,hρ,he⟩ := N.exists_algebra_representation hn j
  exact ⟨ρ,hρ.continuous,he ExpN hExpN⟩

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_NormalProductRepresentation
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Gluing representations across a normal subgroup product

This is the algebraic descent used to integrate a solvable representation
from its nilpotent ideal and Cartan subgroup: agreement on the intersection
and compatibility with conjugation are exactly the required relations.
-/

noncomputable section
namespace PolycyclicRecognition

variable {N H G A : Type*} [Group N] [Group H] [Group G] [Group A]

theorem exists_representation_of_factor_maps
    (φ : H →* MulAut N) (iN : N →* G) (iH : H →* G)
    (hbase : ∀ h, iN.comp (φ h).toMonoidHom =
      (MulAut.conj (iH h)).toMonoidHom.comp iN)
    (hcover : ∀ g : G, ∃ n : N, ∃ h : H, iN n * iH h = g)
    (fN : N →* A) (fH : H →* A)
    (hconj : ∀ (h : H) (n : N), fN (φ h n) = fH h * fN n * (fH h)⁻¹)
    (hagree : ∀ (n : N) (h : H), iN n = iH h → fN n = fH h) :
    ∃ f : G →* A, ∀ (n : N) (h : H), f (iN n * iH h) = fN n * fH h := by
  have htarget (h : H) : fN.comp (φ h).toMonoidHom =
      (MulAut.conj (fH h)).toMonoidHom.comp fN := by
    ext n
    exact hconj h n
  let π : N ⋊[φ] H →* G := SemidirectProduct.lift iN iH hbase
  let F : N ⋊[φ] H →* A := SemidirectProduct.lift fN fH htarget
  have hπ : Function.Surjective π := by
    intro g
    obtain ⟨n, h, rfl⟩ := hcover g
    exact ⟨⟨n, h⟩, rfl⟩
  have hker : π.ker ≤ F.ker := by
    intro z hz
    change iN z.left * iH z.right = 1 at hz
    change fN z.left * fH z.right = 1
    have heq : iN z.left = iH z.right⁻¹ := by
      rw [map_inv]
      exact eq_inv_of_mul_eq_one_left hz
    rw [hagree z.left z.right⁻¹ heq, map_inv, inv_mul_cancel]
  let e := QuotientGroup.quotientKerEquivOfSurjective π hπ
  let F' := QuotientGroup.lift π.ker F hker
  refine ⟨F'.comp e.symm.toMonoidHom, ?_⟩
  intro n h
  have he : e (QuotientGroup.mk (⟨n, h⟩ : N ⋊[φ] H)) = iN n * iH h := rfl
  change F' (e.symm (iN n * iH h)) = _
  rw [← he, e.symm_apply_apply]
  rfl

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_OpenProductRepresentation
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Continuous representation descent across an open normal product -/

noncomputable section
namespace PolycyclicRecognition

variable {N D G A : Type*} [Group N] [Group D] [Group G] [Group A]
  [TopologicalSpace N] [TopologicalSpace D] [TopologicalSpace G] [TopologicalSpace A]
  [ContinuousMul G] [ContinuousMul A]

/-- An open surjective factor product is a quotient map, so algebraic
representation descent preserves continuity. -/
theorem exists_continuous_representation_of_open_factor_maps
    (φ : D →* MulAut N) (iN : N →* G) (iD : D →* G)
    (hiN : Continuous iN) (hiD : Continuous iD)
    (hbase : ∀ d, iN.comp (φ d).toMonoidHom =
      (MulAut.conj (iD d)).toMonoidHom.comp iN)
    (hs : Function.Surjective (fun p : N × D => iN p.1 * iD p.2))
    (ho : IsOpenMap (fun p : N × D => iN p.1 * iD p.2))
    (fN : N →* A) (fD : D →* A) (hfN : Continuous fN) (hfD : Continuous fD)
    (hconj : ∀ d n, fN (φ d n) = fD d * fN n * (fD d)⁻¹)
    (hagree : ∀ n d, iN n = iD d → fN n = fD d) :
    ∃ f : G →* A, Continuous f ∧ ∀ n d, f (iN n * iD d) = fN n * fD d := by
  obtain ⟨f,he⟩ := exists_representation_of_factor_maps φ iN iD hbase
    (fun g => by obtain ⟨⟨n,d⟩,h⟩ := hs g; exact ⟨n,d,h⟩) fN fD hconj hagree
  have hq := ho.isQuotientMap
    ((hiN.comp continuous_fst).mul (hiD.comp continuous_snd)) hs
  refine ⟨f,hq.continuous_iff.mpr ?_,he⟩
  have heq : f ∘ (fun p : N × D => iN p.1 * iD p.2) =
      (fun p : N × D => fN p.1 * fD p.2) := funext fun p => he p.1 p.2
  rw [heq]
  exact (hfN.comp continuous_fst).mul (hfD.comp continuous_snd)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_ActualSmoothRotation
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanRealShadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
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
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_ExponentialRepresentationDescent
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Descent while retaining explicit factor-coordinate formulas -/

noncomputable section
namespace PolycyclicRecognition

variable {N D G A X Y : Type*} [Group N] [Group D] [Group G] [Group A]
  [TopologicalSpace N] [TopologicalSpace D] [TopologicalSpace G] [TopologicalSpace A]
  [ContinuousMul G] [ContinuousMul A]

theorem exists_representation_with_factor_coordinates
    (φ : D →* MulAut N) (iN : N →* G) (iD : D →* G)
    (hiN : Continuous iN) (hiD : Continuous iD)
    (hbase : ∀ d, iN.comp (φ d).toMonoidHom =
      (MulAut.conj (iD d)).toMonoidHom.comp iN)
    (hs : Function.Surjective (fun p : N × D => iN p.1 * iD p.2))
    (ho : IsOpenMap (fun p : N × D => iN p.1 * iD p.2))
    (nExp : X → N) (dExp : Y → D) (nVal : X → A) (dVal : Y → A)
    (hn : ∃ fN : N →* A, Continuous fN ∧ ∀ x, fN (nExp x) = nVal x)
    (hd : ∃ fD : D →* A, Continuous fD ∧ ∀ y, fD (dExp y) = dVal y)
    (hrelations : ∀ (fN : N →* A) (fD : D →* A),
      (∀ x, fN (nExp x) = nVal x) → (∀ y, fD (dExp y) = dVal y) →
        (∀ d n, fN (φ d n) = fD d * fN n * (fD d)⁻¹) ∧
        (∀ n d, iN n = iD d → fN n = fD d)) :
    ∃ f : G →* A, Continuous f ∧
      ∀ x y, f (iN (nExp x) * iD (dExp y)) = nVal x * dVal y := by
  obtain ⟨fN,hfN,heN⟩ := hn
  obtain ⟨fD,hfD,heD⟩ := hd
  obtain ⟨hc,ha⟩ := hrelations fN fD heN heD
  obtain ⟨f,hf,he⟩ := exists_continuous_representation_of_open_factor_maps
    φ iN iD hiN hiD hbase hs ho fN fD hfN hfD hc ha
  exact ⟨f,hf,fun x y => (he _ _).trans (by rw [heN,heD])⟩

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_FactorExponentialOverlap
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanRealShadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Common exponential coordinates on the intersection of the factors -/

noncomputable section
namespace PolycyclicRecognition
open scoped Manifold

variable {E G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MetricSpace G] [ChartedSpace E G]
  [Group G] [LieGroup (𝓘(ℝ,E)) ⊤ G]
  {a : ℕ} {T : ComplexTriangularAdjoint (GroupLieAlgebra (𝓘(ℝ,E)) G) a}
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ,E)) G)}
  {Exp : GroupLieAlgebra (𝓘(ℝ,E)) G → G}

namespace ComplexWeightFactorModel
variable (F : ComplexWeightFactorModel T H Exp)

/-- The recorded intersection theorem supplies a single tangent vector for
both factor coordinates, using only injectivity of their actual inclusions. -/
theorem factor_overlap_coordinates (n : F.N.carrier) (d : F.D.carrier)
    (he : F.inclusionN n = F.inclusionD d) :
    ∃ x : GroupLieAlgebra (𝓘(ℝ,E)) G, ∃ hx : x ∈ T.kernelIdeal, ∃ hy : x ∈ H,
      n = F.ExpN (F.N.equiv ⟨x,hx⟩) ∧ d = F.ExpD (F.D.equiv ⟨x,hy⟩) := by
  have hm : F.inclusionN n ∈ Set.range F.inclusionN ∩ Set.range F.inclusionD :=
    ⟨⟨n,rfl⟩,⟨d,he.symm⟩⟩
  rw [F.overlap] at hm
  obtain ⟨x,hx,hg⟩ := hm
  exact ⟨x,hx.1,hx.2,
    F.closedN.injective (hg.symm.trans (F.compatibleN ⟨x,hx.1⟩).symm),
    F.closedD.injective ((he.symm.trans hg.symm).trans (F.compatibleD ⟨x,hx.2⟩).symm)⟩

end ComplexWeightFactorModel
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

theorem closedEmbedding_cartanFactorToRotation :
    Topology.IsClosedEmbedding (F.cartanFactorToRotation hExp) :=
  Topology.IsClosedEmbedding.of_comp
    (F.smoothRotationalModificationHomeomorph hExp).isEmbedding F.closedD

theorem rotationFactorProduct_open :
    IsOpenMap (fun p : F.N.carrier × F.D.carrier =>
      F.nilpotentFactorToRotation hExp p.1 * F.cartanFactorToRotation hExp p.2) := by
  let e := F.smoothRotationalModificationHomeomorph hExp
  have he : (fun p : F.N.carrier × F.D.carrier =>
      F.nilpotentFactorToRotation hExp p.1 * F.cartanFactorToRotation hExp p.2) =
      e.symm ∘ (fun p : F.N.carrier × F.D.carrier => F.inclusionN p.1 * F.inclusionD p.2) := by
    funext p
    apply e.injective
    exact (F.rotationFactorProduct_coordinates hExp p.1 p.2).trans (e.apply_symm_apply _).symm
  rw [he]
  exact e.symm.isOpenMap.comp F.openProduct

end ComplexWeightFactorModel
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
theorem rotationRepresentation_overlap (n : F.N.carrier) (d : F.D.carrier)
    (he : F.nilpotentFactorToRotation hExp n = F.cartanFactorToRotation hExp d) :
    ρN n = ρD d := by
  have hg := congrArg (F.smoothRotationalModificationHomeomorph hExp) he
  change F.inclusionN n = F.inclusionD d at hg
  obtain ⟨x,hx,hy,hn,hd⟩ := F.factor_overlap_coordinates n d hg
  rw [hn, hd, hN, hD]

end ComplexWeightFactorModel
end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_RotationRepresentationIntegration
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Integration of the real-shadow algebra on the actual rotational graph -/

noncomputable section
namespace PolycyclicRecognition
open scoped Manifold ContDiff
attribute [local instance 100] LieRing.ofAssociativeRing

variable {E G A : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MetricSpace G] [ChartedSpace E G]
  [Group G] [LieGroup (𝓘(ℝ,E)) ⊤ G]
  [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A] [FiniteDimensional ℝ A]
  {a : ℕ} {T : ComplexTriangularAdjoint (GroupLieAlgebra (𝓘(ℝ,E)) G) a}
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ,E)) G)} [H.IsCartanSubalgebra]
  {Exp : GroupLieAlgebra (𝓘(ℝ,E)) G → G}

namespace ComplexWeightFactorModel
variable (F : ComplexWeightFactorModel T H Exp) (hExp : IsGroupExponential Exp)
attribute [local instance] semidirectProductTopology

theorem exists_integrated_rotation_representation_oai (j : CartanRealShadow T H →ₗ⁅ℝ⁆ A) :
    ∃ ρ : F.SmoothRotationalModification hExp →* Aˣ, Continuous ρ ∧
      ∀ (x : T.kernelIdeal) (h : H),
        ρ (F.nilpotentFactorToRotation hExp (F.ExpN (F.N.equiv x)) *
          F.cartanFactorToRotation hExp (F.ExpD (F.D.equiv h))) =
          algebraExpUnit (j (cartanRealShadowEquiv T H x)) *
            algebraExpUnit (j (cartanRealShadowEquiv T H h)) := by
  let : IsTopologicalGroup Aˣ := topologicalGroup_of_lieGroup (𝓘(ℝ,A)) ⊤
  let : IsTopologicalGroup G := topologicalGroup_of_lieGroup (𝓘(ℝ,E)) ⊤
  let jN : T.kernelIdeal →ₗ⁅ℝ⁆ A := j.comp ((realShadowKernel T H).incl.comp
    (realShadowKernelEquiv T H).toLieHom)
  let jD : H →ₗ⁅ℝ⁆ A := j.comp (realShadowCartanHom T H)
  refine exists_representation_with_factor_coordinates
    (F.rotationFactorAction hExp) (F.nilpotentFactorToRotation hExp)
    (F.cartanFactorToRotation hExp)
    (F.closedEmbedding_nilpotentFactorToRotation hExp).continuous
    (F.closedEmbedding_cartanFactorToRotation hExp).continuous
    (fun d => MonoidHom.ext (fun n => F.rotationFactorAction_conjugation hExp d n))
    (F.rotationFactorProduct_surjective hExp) (F.rotationFactorProduct_open hExp)
    (fun x : T.kernelIdeal => F.ExpN (F.N.equiv x))
    (fun h : H => F.ExpD (F.D.equiv h))
    (fun x => algebraExpUnit (j (cartanRealShadowEquiv T H x)))
    (fun h => algebraExpUnit (j (cartanRealShadowEquiv T H h))) ?_ ?_ ?_
  · exact F.N.exists_continuous_algebra_representation
      T.kernelIdeal_nilpotent jN F.ExpN F.isExpN
  · exact F.D.exists_continuous_algebra_representation
      inferInstance jD F.ExpD F.isExpD
  · intro ρN ρD hN hD
    exact ⟨F.rotationRepresentation_conjugation hExp j ρN ρD hN hD,
      F.rotationRepresentation_overlap hExp j ρN ρD hN hD⟩

end ComplexWeightFactorModel
end PolycyclicRecognition

end

end OAI
end

theorem solution : type_of% @OAI.PolycyclicRecognition.ComplexWeightFactorModel.exists_integrated_rotation_representation_oai := @OAI.PolycyclicRecognition.ComplexWeightFactorModel.exists_integrated_rotation_representation_oai
