-- Prove2me | solution 1 for OAI.PolycyclicRecognition.CartanWordModel.nonempty_rayBoundaryComparison_of_shadows_m
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-03T00:56:13.516437+00:00
-- url     : https://prove2.me/submissions/78386489-fa42-40d6-93c9-29abf0867c9f

import Mathlib
import Definitions.Def_PolycyclicRecognition
import Definitions.Def_OAIQ093D022

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

variable {L : Type} [LieRing L] [LieAlgebra ℝ L]
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

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanResidualAction
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial bounds for the residual Cartan action

On an actual generalized root space, subtracting its scalar character leaves
an operator nilpotent in a uniform dimension bound. Its exponential therefore
has polynomial growth in the Cartan parameter. This supplies the residual
operator estimate used in box conjugation.
-/

noncomputable section

namespace PolycyclicRecognition

open LieAlgebra LieModule Module

set_option maxHeartbeats 1000000 in
/-- Split an arbitrary scalar character from an operator exponential. -/
theorem exp_eq_scalar_smul_residual
    {A : Type} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
    (a : ℝ) (X : A) :
    NormedSpace.exp X = Real.exp a • NormedSpace.exp (X - a • 1) := by
  let : NormedAlgebra ℚ A := NormedAlgebra.restrictScalars ℚ ℝ A
  have hc : Commute (a • (1 : A)) (X - a • 1) := by
    simpa only [Algebra.algebraMap_eq_smul_one] using
      Algebra.commute_algebraMap_left a (X - a • 1)
  have he : NormedSpace.exp (a • (1 : A)) = Real.exp a • (1 : A) := by
    simpa only [Real.exp_eq_exp_ℝ, Algebra.algebraMap_eq_smul_one] using
      (NormedSpace.algebraMap_exp_comm (𝕂 := ℝ) (𝔸 := A) a).symm
  conv_lhs => rw [show X = a • 1 + (X - a • 1) by module]
  rw [NormedSpace.exp_add_of_commute hc, he, smul_mul_assoc, one_mul]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanResidualBounds
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.CartanFactorModel.heightRay_zero _root_.OAI.PolycyclicRecognition.CartanFactorModel.realScaleProfile_apply _root_.OAI.PolycyclicRecognition.CartanFactorModel.sampledProbeProfile_apply _root_.OAI.PolycyclicRecognition.cartanWeightDerivation_apply_root _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.nilshadowWeightDerivation_symm _root_.OAI.PolycyclicRecognition.nilshadowWeightOperator_symm _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Bounds for the actual residual automorphism

We identify the residual automorphism on a nonzero root with the analytic
exponential already estimated there. This removes a separate bound premise
for the automorphisms constructed from the Cartan action.
-/

noncomputable section

namespace PolycyclicRecognition

open Module LieAlgebra LieModule
open scoped BigOperators

variable {L : Type} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {n : ℕ} (T : TriangularAdjoint L n)
  (H : LieSubalgebra ℝ L) [H.IsCartanSubalgebra] (χ : Weight ℝ H L) (hχ : χ.IsNonZero)

attribute [local instance] OAI.PolycyclicRecognition.instNormedAddCommGroupSubtypeMemLieSubmoduleRealLieSubalgebraRootSpaceCoeWeight_solutions_1
attribute [local instance] OAI.PolycyclicRecognition.instNormedSpaceRealSubtypeMemLieSubmoduleLieSubalgebraRootSpaceCoeWeight_solutions_1
local instance instNontrivialSubtypeMemLieSubmoduleRealLieSubalgebraRootSpaceCoeWeight_solutions_1_r245ce9_1 : Nontrivial (rootSpace H χ) :=
  (LieSubmodule.nontrivial_iff_ne_bot ℝ H L).mpr χ.genWeightSpace_ne_bot
set_option maxHeartbeats 1000000 in
/-- Inclusion intertwines the root residual operator and the actual ideal
derivation. -/
theorem rootInIdeal_residual_apply (h : H) (v : rootSpace H χ) :
    CartanWordModel.rootInIdeal χ hχ ((rootAction H χ h - χ h • 1) v) =
      cartanIdealResidualDerivation T H h (CartanWordModel.rootInIdeal χ hχ v) := by
  apply Subtype.ext
  change (((rootAction H χ h - χ h • 1) v : rootSpace H χ) : L) =
    cartanResidualDerivation T H h (v : L)
  rw [cartanResidualDerivation_apply_root T H h χ v.property]
  rfl

set_option maxHeartbeats 1000000 in
theorem rootInIdeal_residual_pow (h : H) (k : ℕ) (v : rootSpace H χ) :
    CartanWordModel.rootInIdeal χ hχ (((rootAction H χ h - χ h • 1) ^ k) v) =
      ((cartanIdealResidualDerivation T H h).toLinearMap ^ k)
        (CartanWordModel.rootInIdeal χ hχ v) := by
  induction k generalizing v with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ, mul_apply_eq_comp, ih, rootInIdeal_residual_apply,
      pow_succ, Module.End.mul_apply]
    rfl

set_option maxHeartbeats 1000000 in
include T hχ in
/-- The ambient dimension also truncates the analytic root operator. -/
theorem rootResidual_pow_ambient_dim (h : H) :
    (rootAction H χ h - χ h • 1) ^ finrank ℝ L = 0 := by
  apply ContinuousLinearMap.ext
  intro v
  have hinj : Function.Injective (CartanWordModel.rootInIdeal χ hχ) := by
    intro x y hxy
    exact Subtype.ext (congrArg (fun z : cartanRootIdeal H => (z : L)) hxy)
  apply hinj
  rw [rootInIdeal_residual_pow T H χ hχ h (finrank ℝ L) v,
    cartanIdealResidualDerivation_pow_eq_zero T H h]
  simp

set_option maxHeartbeats 1000000 in
/-- The polynomial Lie automorphism agrees with the analytic root residual
exponential, so the earlier operator norm bounds apply to this automorphism. -/
theorem rootInIdeal_residual_exp (h : H) (v : rootSpace H χ) :
    CartanWordModel.rootInIdeal χ hχ ((NormedSpace.exp (rootAction H χ h - χ h • 1)) v) =
      cartanIdealResidualAutomorphism T H h (CartanWordModel.rootInIdeal χ hχ v) := by
  rw [exp_eq_finite_sum_of_pow_eq_zero _ (rootResidual_pow_ambient_dim T H χ hχ h),
    cartanIdealResidualAutomorphism_apply]
  simp only [sum_apply, smul_apply, map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro k _
  rw [rootInIdeal_residual_pow]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_RootRepresentation
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Root distortion in a faithful integrated representation

The conjugation identity is proved from a Lie homomorphism into a normed
algebra and the ordinary exponential matching identities. It is not an
additional geometric hypothesis.
-/

noncomputable section

namespace PolycyclicRecognition

open LieAlgebra LieModule

attribute [local instance 100] LieRing.ofAssociativeRing
attribute [local instance] rootNormedAddCommGroup rootNormedSpace rootNontrivial

variable {L : Type} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {A : Type} [NormedRing A] [NormedAlgebra ℝ A]
  (H : LieSubalgebra ℝ L) [H.IsCartanSubalgebra] (χ : Weight ℝ H L)
  (j : L →ₗ⁅ℝ⁆ A)

theorem representedRootVector_intertwines (h : H) (v : rootSpace H χ) :
    representedRootVector H χ j (rootAction H χ h v) =
      adjointOperator (j h) (representedRootVector H χ j v) := by
  change j ⁅(h : L), (v : L)⁆ = j h * j v - j v * j h
  rw [j.map_lie, Ring.lie_def]

variable [CompleteSpace A]

/-- The restricted root action exponentiates to actual matrix conjugation. -/
theorem represented_root_flow (h : H) (t : ℝ) (v : rootSpace H χ) :
    representedRootVector H χ j ((NormedSpace.exp (t • rootAction H χ h)) v) =
      NormedSpace.exp (t • j h) * j v * NormedSpace.exp (-(t • j h)) := by
  have hi := exp_intertwine_apply (representedRootVector H χ j)
    (t • rootAction H χ h) (t • adjointOperator (j h)) (by
      intro v
      simp only [smul_apply, map_smul, representedRootVector_intertwines]) v
  rw [exp_smul_adjointOperator_apply] at hi
  exact hi

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanAdjointAction
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The full exponential Cartan action

The scalar dilation and the polynomial residual automorphism together give
the exponential of the actual adjoint action on every nonzero root. In a
compatible faithful representation this is conjugation, not an independently
assumed action on the nilpotent ideal.
-/

noncomputable section

namespace PolycyclicRecognition

open Module LieAlgebra LieModule

variable {L : Type} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {n : ℕ} (T : TriangularAdjoint L n)
  (H : LieSubalgebra ℝ L) [H.IsCartanSubalgebra]

variable (χ : Weight ℝ H L) (hχ : χ.IsNonZero)

attribute [local instance] OAI.PolycyclicRecognition.instNormedAddCommGroupSubtypeMemLieSubmoduleRealLieSubalgebraRootSpaceCoeWeight_solutions_2
attribute [local instance] OAI.PolycyclicRecognition.instNormedSpaceRealSubtypeMemLieSubmoduleLieSubalgebraRootSpaceCoeWeight_solutions_2
local instance instNontrivialSubtypeMemLieSubmoduleRealLieSubalgebraRootSpaceCoeWeight_solutions_2_r245ce9_1 : Nontrivial (rootSpace H χ) :=
  (LieSubmodule.nontrivial_iff_ne_bot ℝ H L).mpr χ.genWeightSpace_ne_bot
set_option maxHeartbeats 1000000 in
/-- The full action is the analytic adjoint exponential on each nonzero root. -/
theorem rootInIdeal_adjoint_exp (h : H) (v : rootSpace H χ) :
    CartanWordModel.rootInIdeal χ hχ ((NormedSpace.exp (rootAction H χ h)) v) =
      cartanIdealAdjointAutomorphism T H h (CartanWordModel.rootInIdeal χ hχ v) := by
  rw [exp_eq_scalar_smul_residual (χ h) (rootAction H χ h),
    smul_apply, map_smul, rootInIdeal_residual_exp T H χ hχ h v]
  apply Subtype.ext
  change Real.exp (χ h) •
      (cartanIdealResidualAutomorphism T H h (CartanWordModel.rootInIdeal χ hχ v) : L) =
    cartanWeightScale T H h _
  exact (cartanWeightScale_apply_root T H h χ
    (cartanIdealResidualAutomorphism_root_mem T H h χ _ v.property)).symm

section Representation

variable {A : Type} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

attribute [local instance 100] LieRing.ofAssociativeRing

attribute [local instance] OAI.PolycyclicRecognition.instNormedAddCommGroupSubtypeMemLieSubmoduleRealLieSubalgebraRootSpaceCoeWeight_solutions_2
attribute [local instance] OAI.PolycyclicRecognition.instNormedSpaceRealSubtypeMemLieSubmoduleLieSubalgebraRootSpaceCoeWeight_solutions_2
local instance instNontrivialSubtypeMemLieSubmoduleRealLieSubalgebraRootSpaceCoeWeight_solutions_2_r245ce9_2 : Nontrivial (rootSpace H χ) :=
  (LieSubmodule.nontrivial_iff_ne_bot ℝ H L).mpr χ.genWeightSpace_ne_bot
set_option maxHeartbeats 1000000 in
/-- The constructed action agrees with conjugation in a compatible algebra
representation on every generating root. -/
theorem represented_adjoint_root (j : L →ₗ⁅ℝ⁆ A) (h : H) (v : rootSpace H χ) :
    j (cartanIdealAdjointAutomorphism T H h (CartanWordModel.rootInIdeal χ hχ v) : L) =
      NormedSpace.exp (j h) * j v * NormedSpace.exp (-j h) := by
  rw [← rootInIdeal_adjoint_exp T H χ hχ h v]
  have hh := represented_root_flow H χ j h 1 v
  simp only [one_smul] at hh
  exact hh

set_option maxHeartbeats 1000000 in
omit hχ χ in
/-- Lie generation extends the root calculation to every vector in the
nilpotent ideal. -/
theorem represented_adjoint_ideal (j : L →ₗ⁅ℝ⁆ A) (h : H) (x : cartanRootIdeal H) :
    j (cartanIdealAdjointAutomorphism T H h x : L) =
      NormedSpace.exp (j h) * j x * NormedSpace.exp (-j h) := by
  let u := algebraExpUnit (j h)
  change j (cartanIdealAdjointAutomorphism T H h x : L) =
    (u : A) * j x * (↑(u⁻¹) : A)
  have hx : x ∈ LieSubalgebra.lieSpan ℝ (cartanRootIdeal H) (cartanGeneratorPool H) := by
    rw [cartanGeneratorPool_lieSpan H T]
    trivial
  have hmul (a b : A) :
      ((u : A) * a * (↑(u⁻¹) : A)) * ((u : A) * b * (↑(u⁻¹) : A)) =
        (u : A) * (a * b) * (↑(u⁻¹) : A) := by
    calc
      _ = (u : A) * a * ((↑(u⁻¹) : A) * u) * b * (↑(u⁻¹) : A) := by
        simp only [mul_assoc]
      _ = _ := by simp only [Units.inv_mul, mul_one, mul_assoc]
  induction hx using LieSubalgebra.lieSpan_induction with
  | mem x hx =>
    obtain ⟨ψ, hψ, hx⟩ := hx
    have he : CartanWordModel.rootInIdeal ψ hψ ⟨x, hx⟩ = x := Subtype.ext rfl
    have hh := represented_adjoint_root T H ψ hψ j h ⟨x, hx⟩
    rw [he] at hh
    exact hh
  | zero => simp only [map_zero, ZeroMemClass.coe_zero, mul_zero, zero_mul]
  | add x y _ _ hx hy =>
    simpa only [map_add, AddMemClass.coe_add, mul_add, add_mul] using congrArg₂ (· + ·) hx hy
  | smul a x _ hx =>
    simpa only [map_smul, SetLike.val_smul, smul_mul_assoc, mul_smul_comm,
      RingHom.id_apply] using congrArg (a • ·) hx
  | lie x y _ _ hx hy =>
    rw [LieEquiv.map_lie]
    change j ⁅(cartanIdealAdjointAutomorphism T H h x : L),
      (cartanIdealAdjointAutomorphism T H h y : L)⁆ =
        (u : A) * j ⁅(x : L), (y : L)⁆ * (↑(u⁻¹) : A)
    rw [j.map_lie, j.map_lie, hx, hy]
    simp only [Ring.lie_def, mul_sub, sub_mul, hmul]

end Representation

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanActualConjugation
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instDecidableEqConeMixedWords _root_.OAI.PolycyclicRecognition.CartanWordModel.instFintypeConeMixedWords _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual Cartan conjugation and shifted boxes

The full Lie action integrates to the nilpotent group. A faithful compatible
representation identifies this automorphism with ambient conjugation. The
resulting box estimate retains the polynomial residual factor and the exact
canonical-height translation.
-/

noncomputable section

namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule
open scoped Manifold

variable {L : Type} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {H : LieSubalgebra ℝ L} [H.IsCartanSubalgebra] (M : CartanWordModel H)
  {n : ℕ} (T : TriangularAdjoint L n)
  {EN N : Type} [NormedAddCommGroup EN] [NormedSpace ℝ EN]
  [FiniteDimensional ℝ EN] [TopologicalSpace N] [ChartedSpace EN N] [Group N]
  [LieGroup (𝓘(ℝ, EN)) ⊤ N] [T2Space N]
  (eN : cartanRootIdeal H ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, EN)) N)
  (Exp : GroupLieAlgebra (𝓘(ℝ, EN)) N → N) (hExp : IsGroupExponential Exp)
  (hbij : Function.Bijective Exp) (dynkin : NilpotentDynkinExpansionInput EN N)

section Representation

variable {A G : Type} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A] [Group G]

attribute [local instance 100] LieRing.ofAssociativeRing

set_option maxHeartbeats 1000000 in
/-- Compatibility of exponentials in a faithful representation identifies
the constructed automorphism with actual ambient conjugation. -/
theorem adjointGroupAutomorphism_eq_conjugation
    (j : L →ₗ⁅ℝ⁆ A) (ρ : G →* Aˣ) (hρ : Function.Injective ρ)
    (ι : N →* G) (d : H → G)
    (hN : ∀ x : cartanRootIdeal H, ρ (ι (Exp (eN x))) = algebraExpUnit (j x))
    (hd : ∀ h, ρ (d h) = algebraExpUnit (j h)) (h : H) (g : N) :
    ι (M.adjointGroupAutomorphism T eN Exp hExp hbij dynkin h g) =
      d h * ι g * (d h)⁻¹ := by
  obtain ⟨x, rfl⟩ := (hbij.comp eN.bijective).surjective g
  apply hρ
  change ρ (ι (integrateNilpotentLieEquiv eN Exp hbij dynkin hExp M.bound_zero
    (cartanIdealAdjointAutomorphism T H h) (Exp (eN x)))) = _
  rw [integrateNilpotentLieEquiv_apply_exp, hN, map_mul, map_mul, map_inv, hd]
  change algebraExpUnit (j (cartanIdealAdjointAutomorphism T H h x : L)) =
    algebraExpUnit (j h) * ρ (ι (Exp (eN x))) * (algebraExpUnit (j h))⁻¹
  rw [hN]
  rw [represented_adjoint_ideal T H j h x]
  exact algebraExpUnit_conj (algebraExpUnit (j h)) (j x)

end Representation

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_MixedWordIdeal
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The mixed-word ideal used by the cone quotients -/

noncomputable section
namespace PolycyclicRecognition

open Set

variable {I L : Type} [LieRing L] [LieAlgebra ℝ L]

/-- The quotient by the mixed-word ideal is spanned by pure words. -/
theorem quotient_mixedWordIdeal_span_pure (X : I → L) (outside : I → Prop)
    (hgen : LieSubalgebra.lieSpan ℝ L (range X) = ⊤) :
    let J := (mixedWordIdeal X outside hgen).toSubmodule
    Submodule.span ℝ (J.mkQ '' (evalBracketWord X '' {w | ¬IsMixedWord outside w})) = ⊤ := by
  dsimp only
  let J := (mixedWordIdeal X outside hgen).toSubmodule
  let P := Submodule.span ℝ (J.mkQ '' (evalBracketWord X '' {w | ¬IsMixedWord outside w}))
  apply top_unique
  intro q hq
  clear hq
  obtain ⟨x, rfl⟩ := J.mkQ_surjective q
  have hx : x ∈ Submodule.span ℝ (range (evalBracketWord X)) := by
    rw [span_evalBracketWord, hgen]
    trivial
  change J.mkQ x ∈ P
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨w, rfl⟩ := hx
    by_cases hw : IsMixedWord outside w
    · have hz : J.mkQ (evalBracketWord X w) = 0 :=
        (Submodule.Quotient.mk_eq_zero J).mpr (eval_mixed_mem_span X outside hw)
      rw [hz]
      exact P.zero_mem
    · exact Submodule.subset_span ⟨_, ⟨w, hw, rfl⟩, rfl⟩
  | zero => simpa only [map_zero] using P.zero_mem
  | add x y _ _ hx hy => simpa only [map_add] using P.add_mem hx hy
  | smul r x _ hx => simpa only [map_smul] using P.smul_mem r hx

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_QuotientWordBasis
attribute [-instance] _root_.GeneratesNS.fintype_closedBall _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.CartanFactorModel.realScaleProfile_apply _root_.OAI.PolycyclicRecognition.bracketWordDifferential_mul _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.OAI.PolycyclicRecognition.wordBasisOfDet_val _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Pure word bases of the mixed-word quotient

An inside generator is retained in every pure word basis. The proof uses
its actual coordinate in the original abelianization, descended through
the mixed-word ideal.
-/

noncomputable section
namespace PolycyclicRecognition

open Module Set
open scoped BigOperators

variable {I L : Type} [LieRing L] [LieAlgebra ℝ L]

theorem exists_pure_quotient_word_basis [FiniteDimensional ℝ L]
    (X : I → L) (outside : I → Prop)
    (hgen : LieSubalgebra.lieSpan ℝ L (range X) = ⊤) :
    let J := (mixedWordIdeal X outside hgen).toSubmodule
    ∃ (b : Basis (Fin (finrank ℝ (L ⧸ J))) ℝ (L ⧸ J))
      (words : Fin (finrank ℝ (L ⧸ J)) → FreeMagma I),
      (∀ j, ¬IsMixedWord outside (words j)) ∧
      (∀ j, J.mkQ (evalBracketWord X (words j)) = b j) := by
  dsimp only
  let J := (mixedWordIdeal X outside hgen).toSubmodule
  let S := J.mkQ '' (evalBracketWord X '' {w | ¬IsMixedWord outside w})
  have hS : ⊤ ≤ Submodule.span ℝ S :=
    (quotient_mixedWordIdeal_span_pure X outside hgen).ge
  let K := (linearIndepOn_empty ℝ (id : (L ⧸ J) → (L ⧸ J))).extend
    (empty_subset S)
  let b₀ : Basis K ℝ (L ⧸ J) := Basis.ofSpan hS
  let : Fintype K := Fintype.ofFinite _
  let e : K ≃ Fin (finrank ℝ (L ⧸ J)) :=
    Fintype.equivFinOfCardEq (Module.finrank_eq_card_basis b₀).symm
  let b := b₀.reindex e
  have hw (j) : ∃ w, ¬IsMixedWord outside w ∧ J.mkQ (evalBracketWord X w) = b j := by
    have hj := Basis.ofSpan_subset hS (show b₀ (e.symm j) ∈ range b₀ from ⟨_, rfl⟩)
    obtain ⟨_, ⟨w, hp, rfl⟩, he⟩ := hj
    exact ⟨w, hp, by simpa only [b, Basis.coe_reindex, Function.comp_apply] using he⟩
  choose words hp he using hw
  exact ⟨b, words, hp, he⟩

variable [DecidableEq I]

omit [DecidableEq I] in
/-- An inside abelian coordinate vanishes on the entire mixed-word ideal. -/
theorem inside_abelian_coordinate_kills_mixed
    {Q : Type} [AddCommGroup Q] [Module ℝ Q]
    (X : I → L) (outside : I → Prop)
    (q : L →ₗ[ℝ] Q) (hq : ∀ x y : L, q ⁅x, y⁆ = 0)
    (bq : Basis I ℝ Q) (hX : ∀ i, q (X i) = bq i)
    (i : I) (hi : ¬outside i) :
    mixedWordSpan X outside ≤ LinearMap.ker ((bq.coord i).comp q) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨w, hw, rfl⟩
  change bq.repr (q (evalBracketWord X w)) i = 0
  cases w with
  | of j =>
    have hij : i ≠ j := fun he => hi (he ▸ hw)
    simp [evalBracketWord, hX, hij]
  | mul u v => simp [evalBracketWord, hq]

omit [DecidableEq I] in
/-- Every retained generator occurs as a one-letter word in any pure
word basis of the quotient. -/
theorem mandatory_inside_letter_in_quotient
    {Q K : Type} [AddCommGroup Q] [Module ℝ Q]
    (X : I → L) (outside : I → Prop)
    (hgen : LieSubalgebra.lieSpan ℝ L (range X) = ⊤)
    (q : L →ₗ[ℝ] Q) (hq : ∀ x y : L, q ⁅x, y⁆ = 0)
    (bq : Basis I ℝ Q) (hX : ∀ i, q (X i) = bq i)
    (b : Basis K ℝ (L ⧸ (mixedWordIdeal X outside hgen).toSubmodule))
    (words : K → FreeMagma I)
    (hwords : ∀ j, (mixedWordIdeal X outside hgen).toSubmodule.mkQ
      (evalBracketWord X (words j)) = b j)
    (i : I) (hi : ¬outside i) : ∃ j, words j = .of i := by
  let J := (mixedWordIdeal X outside hgen).toSubmodule
  let f := (bq.coord i).comp q
  let fQ := J.liftQ f (inside_abelian_coordinate_kills_mixed X outside q hq bq hX i hi)
  by_contra hn
  have hn' : ∀ j, words j ≠ .of i := fun j h => hn ⟨j, h⟩
  have hf : fQ = 0 := b.ext fun j => by
    rw [← hwords j]
    change f (evalBracketWord X (words j)) = 0
    cases hw : words j with
    | of k =>
      have hki : k ≠ i := fun h => hn' j (hw.trans (congrArg FreeMagma.of h))
      simp [f, evalBracketWord, hX, Basis.coord_apply, hki]
    | mul u v => simp [f, evalBracketWord, hq]
  have h := congrArg (fun F : (L ⧸ J) →ₗ[ℝ] ℝ => F (J.mkQ (X i))) hf
  change f (X i) = 0 at h
  simp [f, hX, Basis.coord_apply] at h

theorem positive_inside_quotient_word_counts
    [Fintype I] {Q K : Type} [Fintype K] [AddCommGroup Q] [Module ℝ Q]
    (X : I → L) (outside : I → Prop)
    (hgen : LieSubalgebra.lieSpan ℝ L (range X) = ⊤)
    (q : L →ₗ[ℝ] Q) (hq : ∀ x y : L, q ⁅x, y⁆ = 0)
    (bq : Basis I ℝ Q) (hX : ∀ i, q (X i) = bq i)
    (b : Basis K ℝ (L ⧸ (mixedWordIdeal X outside hgen).toSubmodule))
    (words : K → FreeMagma I)
    (hwords : ∀ j, (mixedWordIdeal X outside hgen).toSubmodule.mkQ
      (evalBracketWord X (words j)) = b j)
    (i : I) (hi : ¬outside i) : 0 < ∑ j, bracketWordCount (words j) i := by
  obtain ⟨j, hj⟩ := mandatory_inside_letter_in_quotient X outside hgen q hq bq hX
    b words hwords i hi
  have hle := Finset.single_le_sum (fun j (_ : j ∈ (Finset.univ : Finset K)) =>
    Nat.zero_le (bracketWordCount (words j) i)) (Finset.mem_univ j)
  rw [hj] at hle
  simp only [bracketWordCount, ite_true, if_true] at hle
  exact lt_of_lt_of_le Nat.zero_lt_one hle

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanConeTrace
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instDecidableEqConeMixedWords _root_.OAI.PolycyclicRecognition.CartanWordModel.instFintypeConeMixedWords _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The positive trace character of a Cartan cone quotient

The coefficients come from an actual pure-word basis of the quotient.
The abelianization coordinates prove strict positivity for every inside
generator, including the extremal generators of a ray or a two-ray cone.
-/

noncomputable section
namespace PolycyclicRecognition

open Module LieAlgebra LieModule Set
open scoped BigOperators

set_option maxHeartbeats 1000000 in
theorem bracketWordCount_eq_zero_of_pure
    {I : Type} [DecidableEq I] (outside : I → Prop)
    {w : FreeMagma I} (hw : ¬IsMixedWord outside w) {i : I} (hi : outside i) :
    bracketWordCount w i = 0 := by
  induction w using FreeMagma.rec with
  | of j =>
    have hij : i ≠ j := fun h => hw (h ▸ hi)
    simp [bracketWordCount, hij]
  | mul u v hu hv =>
    exact Nat.add_eq_zero_iff.mpr ⟨hu (fun h => hw (Or.inl h)), hv (fun h => hw (Or.inr h))⟩

namespace CartanWordModel

variable {L : Type} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {H : LieSubalgebra ℝ L} [H.IsCartanSubalgebra] (M : CartanWordModel H)

set_option maxHeartbeats 1000000 in
/-- Trace on a pure-word quotient basis is the sum of the actual word
weights; generalized eigenspaces retain the nilpotent parts of the action. -/
theorem trace_cone_word_basis
    (C : Set (H →ₗ[ℝ] ℝ)) (hadd : ∀ x ∈ C, ∀ y ∈ C, x + y ∈ C)
    {J : Type} [Fintype J]
    (b : Basis J ℝ ((cartanRootIdeal H) ⧸ M.coneCartanSubmodule C hadd))
    (words : J → FreeMagma (Fin M.letterCount))
    (hwords : ∀ j, (M.coneWordIdeal C).toSubmodule.mkQ
      (evalBracketWord M.letter (words j)) = b j) (h : H) :
    LinearMap.trace ℝ ((cartanRootIdeal H) ⧸ M.coneCartanSubmodule C hadd)
      (toEnd ℝ H _ h) =
        ∑ i, ((∑ j, bracketWordCount (words j) i : ℕ) : ℝ) * M.weight i h := by
  let Q := (cartanRootIdeal H) ⧸ M.coneCartanSubmodule C hadd
  let q := LieSubmodule.Quotient.mk' (M.coneCartanSubmodule C hadd)
  let α := fun i => (M.weight i : H →ₗ[ℝ] ℝ)
  have hm (j : J) : b j ∈ genWeightSpace Q (bracketWordWeight α (words j)) := by
    rw [← hwords j]
    exact map_genWeightSpace_le q ⟨_,
      cartan_word_mem_genWeight H M.letter M.weight M.letter_root (words j), rfl⟩
  let ψ : J → Weight ℝ H Q := fun j =>
    { toFun := bracketWordWeight α (words j)
      genWeightSpace_ne_bot' := by
        intro hz
        have hh := hm j
        rw [hz] at hh
        exact b.ne_zero j hh }
  have ht := trace_eq_sum_of_generalizedWeight_basis b ψ hm h
  change LinearMap.trace ℝ Q (toEnd ℝ H Q h) =
    ∑ j, bracketWordWeight α (words j) h at ht
  rw [ht]
  simp_rw [bracketWordWeight_eq_count, Nat.cast_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  rfl

set_option maxHeartbeats 1000000 in
/-- The quotient trace is an integral combination of inside generator
weights, with strictly positive coefficients for every inside generator. -/
theorem exists_positive_cone_trace_coefficients
    (C : Set (H →ₗ[ℝ] ℝ)) (hadd : ∀ x ∈ C, ∀ y ∈ C, x + y ∈ C) :
    ∃ c : Fin M.letterCount → ℕ,
      (∀ i, (M.weight i : H →ₗ[ℝ] ℝ) ∉ C → c i = 0) ∧
      (∀ i, (M.weight i : H →ₗ[ℝ] ℝ) ∈ C → 0 < c i) ∧
      ∀ h : H, LinearMap.trace ℝ
        ((cartanRootIdeal H) ⧸ M.coneCartanSubmodule C hadd) (toEnd ℝ H _ h) =
          ∑ i, (c i : ℝ) * M.weight i h := by
  classical
  let outside := fun i => (M.weight i : H →ₗ[ℝ] ℝ) ∉ C
  obtain ⟨b, words, hpure, hwords⟩ :=
    exists_pure_quotient_word_basis M.letter outside M.generates
  refine ⟨fun i => ∑ j, bracketWordCount (words j) i, ?_, ?_, ?_⟩
  · intro i hi
    exact Finset.sum_eq_zero (fun j _ => bracketWordCount_eq_zero_of_pure outside (hpure j) hi)
  · intro i hi
    let N := (lowerCentralSeries ℝ (cartanRootIdeal H) (cartanRootIdeal H) 1).toSubmodule
    apply positive_inside_quotient_word_counts M.letter outside M.generates N.mkQ ?_
      M.abelianBasis M.letter_quotient b words hwords i (not_not.mpr hi)
    intro x y
    apply (Submodule.Quotient.mk_eq_zero N).mpr
    change ⁅x, y⁆ ∈ lowerCentralSeries ℝ (cartanRootIdeal H) (cartanRootIdeal H) (0 + 1)
    rw [lowerCentralSeries_succ, lowerCentralSeries_zero]
    exact LieSubmodule.lie_mem_lie (LieSubmodule.mem_top x) (LieSubmodule.mem_top y)
  · exact M.trace_cone_word_basis C hadd b words hwords

end CartanWordModel
end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_ConeQuotientJacobian
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instDecidableEqConeMixedWords _root_.OAI.PolycyclicRecognition.CartanWordModel.instFintypeConeMixedWords _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.stationaryL2SMulComm _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.CartanFactorModel.heightRay_zero _root_.OAI.PolycyclicRecognition.CartanFactorModel.realScaleProfile_apply _root_.OAI.PolycyclicRecognition.CartanFactorModel.sampledProbeProfile_apply _root_.OAI.PolycyclicRecognition.bracketWordDifferential_mul _root_.OAI.PolycyclicRecognition.cartanWeightDerivation_apply_root _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.nilshadowWeightDerivation_symm _root_.OAI.PolycyclicRecognition.nilshadowWeightOperator_symm _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The Jacobian of the induced Cartan action on a cone quotient -/

noncomputable section
namespace PolycyclicRecognition

open Module LieAlgebra LieModule Set
open scoped BigOperators

/-- A quotient of a unipotent operator is unipotent. This supplies the
determinant-one part of the quotient action without diagonalizability. -/
theorem quotient_unipotent
    {V : Type} [AddCommGroup V] [Module ℝ V]
    (J : Submodule ℝ V) (F : V →ₗ[ℝ] V) (hF : ∀ x ∈ J, F x ∈ J)
    (hu : _root_.IsNilpotent (F - 1)) :
    _root_.IsNilpotent (J.mapQ J F hF - 1) := by
  have hsub : ∀ x ∈ J, (F - 1) x ∈ J := fun x hx => J.sub_mem (hF x hx) hx
  have he : J.mapQ J F hF - 1 = J.mapQ J (F - 1) hsub := by
    apply LinearMap.ext
    intro x
    obtain ⟨v, rfl⟩ := J.mkQ_surjective x
    simp
  obtain ⟨k, hk⟩ := hu
  refine ⟨k, ?_⟩
  rw [he, ← J.mapQ_pow hsub]
  apply LinearMap.ext
  intro x
  obtain ⟨v, rfl⟩ := J.mkQ_surjective x
  simp [hk]

namespace CartanWordModel

variable {L : Type} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {H : LieSubalgebra ℝ L} [H.IsCartanSubalgebra] (M : CartanWordModel H)
  {n : ℕ} (T : TriangularAdjoint L n)

/-- The quotient scalar Jacobian is the exponential of the total retained
word weight. -/
theorem det_cone_dilation_word_basis
    (C : Set (H →ₗ[ℝ] ℝ)) (h : H) {J : Type} [Fintype J]
    (b : Basis J ℝ ((cartanRootIdeal H) ⧸ M.coneWordIdeal C))
    (words : J → FreeMagma (Fin M.letterCount))
    (hb : ∀ j, (M.coneWordIdeal C).toSubmodule.mkQ (evalBracketWord M.letter (words j)) = b j) :
    LinearMap.det ((M.coneWordIdeal C).toSubmodule.mapQ (M.coneWordIdeal C).toSubmodule
      (cartanIdealWeightDilation T H h).toLinearEquiv.toLinearMap
      (M.coneWordIdeal_dilation_mem T C h)) =
        Real.exp (∑ j, bracketWordExponent (fun i => M.weight i h) (words j)) := by
  classical
  let I := (M.coneWordIdeal C).toSubmodule
  let F := I.mapQ I (cartanIdealWeightDilation T H h).toLinearEquiv.toLinearMap
    (M.coneWordIdeal_dilation_mem T C h)
  let w := fun j => Real.exp (bracketWordExponent (fun i => M.weight i h) (words j))
  have hF (j) : F (b j) = w j • b j := by
    rw [← hb j]
    change I.mkQ (cartanIdealWeightDilation T H h (evalBracketWord M.letter (words j))) = _
    rw [M.idealWeightDilation_word T h, map_smul]
  have hm : LinearMap.toMatrix b b F = Matrix.diagonal w := by
    ext i j
    simp only [LinearMap.toMatrix_apply, hF, map_smul, Finsupp.smul_apply,
      Basis.repr_self, Finsupp.single_apply, smul_eq_mul, Matrix.diagonal_apply]
    split_ifs <;> simp_all
  rw [← LinearMap.det_toMatrix b, hm, Matrix.det_diagonal, Real.exp_sum]

theorem det_cone_residual_eq_one
    (C : Set (H →ₗ[ℝ] ℝ)) (hadd : ∀ x ∈ C, ∀ y ∈ C, x + y ∈ C) (h : H) :
    LinearMap.det ((M.coneWordIdeal C).toSubmodule.mapQ (M.coneWordIdeal C).toSubmodule
      (cartanIdealResidualAutomorphism T H h).toLinearEquiv.toLinearMap
      (M.coneWordIdeal_residual_mem T C hadd h)) = 1 := by
  apply det_eq_one_of_sub_one_nilpotent
  apply quotient_unipotent
  let : Module ℚ (cartanRootIdeal H) := Module.compHom _ (algebraMap ℚ ℝ)
  have hn : _root_.IsNilpotent (cartanIdealResidualDerivation T H h).toLinearMap :=
    ⟨finrank ℝ L, cartanIdealResidualDerivation_pow_eq_zero T H h⟩
  exact hn.isNilpotent_exp_sub_one

/-- The full induced action has Jacobian equal to the exponential of its
actual quotient trace, including all nonsemisimple corrections. -/
theorem det_cone_adjoint_eq_exp_trace
    (C : Set (H →ₗ[ℝ] ℝ)) (hadd : ∀ x ∈ C, ∀ y ∈ C, x + y ∈ C) (h : H) :
    LinearMap.det ((M.coneWordIdeal C).toSubmodule.mapQ (M.coneWordIdeal C).toSubmodule
      (cartanIdealAdjointAutomorphism T H h).toLinearEquiv.toLinearMap
      (M.coneWordIdeal_adjoint_mem T C hadd h)) =
    Real.exp (LinearMap.trace ℝ ((cartanRootIdeal H) ⧸ M.coneCartanSubmodule C hadd)
      (toEnd ℝ H _ h)) := by
  classical
  let I := (M.coneWordIdeal C).toSubmodule
  have heq : I.mapQ I (cartanIdealAdjointAutomorphism T H h).toLinearEquiv.toLinearMap
      (M.coneWordIdeal_adjoint_mem T C hadd h) =
      (I.mapQ I (cartanIdealWeightDilation T H h).toLinearEquiv.toLinearMap
        (M.coneWordIdeal_dilation_mem T C h)).comp
      (I.mapQ I (cartanIdealResidualAutomorphism T H h).toLinearEquiv.toLinearMap
        (M.coneWordIdeal_residual_mem T C hadd h)) := by
    apply LinearMap.ext
    intro x
    obtain ⟨v, rfl⟩ := I.mkQ_surjective x
    rfl
  obtain ⟨b, words, _hpure, hb⟩ := exists_pure_quotient_word_basis M.letter
    (fun i => (M.weight i : H →ₗ[ℝ] ℝ) ∉ C) M.generates
  rw [heq, LinearMap.det_comp, M.det_cone_residual_eq_one T C hadd h, mul_one,
    M.det_cone_dilation_word_basis T C h b words hb]
  apply congrArg Real.exp
  rw [M.trace_cone_word_basis C hadd b words hb h]
  simp only [bracketWordExponent, Nat.cast_sum, Finset.sum_mul]
  rw [Finset.sum_comm]

end CartanWordModel
end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_ExponentialHaarMultiplier
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_countable _root_.OAI.PolycyclicRecognition.finitelyGeneratedSubgroupIndex_countable _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The exact Haar multiplier of an exponential-coordinate automorphism -/

noncomputable section
namespace PolycyclicRecognition

open Module MeasureTheory
open scoped Manifold

variable {L : Type} [LieRing L] [LieAlgebra ℝ L]
  {E G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace G] [ChartedSpace E G] [Group G]
  [LieGroup (𝓘(ℝ, E)) ⊤ G] [MeasurableSpace G] [BorelSpace G]
  (e : L ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, E)) G)
  (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G) (hbij : Function.Bijective Exp)
  (chart : GroupLieAlgebra (𝓘(ℝ, E)) G ≃ₜ G) (hchart : ∀ x, chart x = Exp x)
  {n : ℕ} (b : Basis (Fin n) ℝ L)

include hchart in
/-- The pushforward multiplier is the reciprocal absolute determinant.
Consequently the multiplier of image volumes is the absolute determinant. -/
theorem exponentialConjugate_map_measure (F : L ≃ₗ⁅ℝ⁆ L) :
    Measure.map (exponentialConjugate e Exp hbij F)
      (Measure.map ((Exp ∘ e) ∘ b.equivFun.symm) volume) =
    ENNReal.ofReal |(LinearMap.det F.toLinearEquiv.toLinearMap)⁻¹| •
      Measure.map ((Exp ∘ e) ∘ b.equivFun.symm) volume := by
  let A : (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ) :=
    (b.equivFun.symm.trans F.toLinearEquiv).trans b.equivFun
  let f : (Fin n → ℝ) ≃ₜ G :=
    (b.equivFun.symm.trans e.toLinearEquiv).toContinuousLinearEquiv.toHomeomorph.trans chart
  have hf : (f : (Fin n → ℝ) → G) = (Exp ∘ e) ∘ b.equivFun.symm := by
    funext t
    exact hchart _
  have hAdet : LinearMap.det A.toLinearMap = LinearMap.det F.toLinearEquiv.toLinearMap := by
    have hd := congrArg Units.val (LinearEquiv.det_conj F.toLinearEquiv b.equivFun)
    simpa only [LinearEquiv.coe_det] using hd
  have hA : Measure.map A volume = ENNReal.ofReal |(LinearMap.det A.toLinearMap)⁻¹| • volume :=
    Real.map_linearMap_volume_pi_eq_smul_volume_pi A.isUnit_det'.ne_zero
  have hsem : Function.Semiconj f A (exponentialConjugate e Exp hbij F) := by
    intro t
    rw [hf]
    change Exp (e (b.equivFun.symm (A t))) = _
    simp only [A, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
    exact (exponentialConjugate_apply_exp e Exp hbij F (b.equivFun.symm t)).symm
  have heq : (exponentialConjugate e Exp hbij F : G → G) = f ∘ A ∘ f.symm := by
    funext g
    obtain ⟨t, rfl⟩ := f.surjective g
    simpa only [Function.comp_apply, f.symm_apply_apply] using (hsem t).symm
  have hmeas : Measurable (exponentialConjugate e Exp hbij F) := by
    rw [heq]
    exact f.continuous.measurable.comp
      (A.toContinuousLinearEquiv.continuous.measurable.comp f.symm.continuous.measurable)
  have hcomp : (exponentialConjugate e Exp hbij F) ∘ f = f ∘ A :=
    funext (fun t => (hsem t).symm)
  have hAmeas : Measurable (A : (Fin n → ℝ) → (Fin n → ℝ)) :=
    A.toContinuousLinearEquiv.continuous.measurable
  rw [← hf, Measure.map_map hmeas f.continuous.measurable, hcomp,
    ← Measure.map_map f.continuous.measurable hAmeas,
    hA, Measure.map_smul, hAdet]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_ConeQuotientAutomorphism
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instDecidableEqConeMixedWords _root_.OAI.PolycyclicRecognition.CartanWordModel.instFintypeConeMixedWords _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The quotient Lie automorphism and its exponential Haar multiplier -/

noncomputable section
namespace PolycyclicRecognition

open Module LieAlgebra LieModule Set MeasureTheory
open scoped Manifold

namespace CartanWordModel

variable {L : Type} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {H : LieSubalgebra ℝ L} [H.IsCartanSubalgebra] (M : CartanWordModel H)
  {n : ℕ} (T : TriangularAdjoint L n)

theorem det_coneAdjointAutomorphism
    (C : Set (H →ₗ[ℝ] ℝ)) (hadd : ∀ x ∈ C, ∀ y ∈ C, x + y ∈ C) (h : H) :
    LinearMap.det (M.coneAdjointAutomorphism T C hadd h).toLinearEquiv.toLinearMap =
      Real.exp (LinearMap.trace ℝ ((cartanRootIdeal H) ⧸ M.coneCartanSubmodule C hadd)
        (toEnd ℝ H _ h)) :=
  M.det_cone_adjoint_eq_exp_trace T C hadd h

end CartanWordModel
end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_CompactLiftQuotient
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Compact lifts and the topology of the actual quotient orbit -/

noncomputable section
namespace PolycyclicRecognition

open Set TopologicalSpace Topology
open scoped Manifold

/-- A continuous surjection with compact lifts of compact sets is a
quotient map into a Hausdorff compactly generated space. -/
theorem isQuotientMap_of_compact_lifts
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [T2Space Y] [CompactlyGeneratedSpace Y]
    (f : X → Y) (hf : Continuous f) (hsurj : Function.Surjective f)
    (hlift : ∀ K : Set Y, IsCompact K → ∃ C : Set X, IsCompact C ∧ K ⊆ f '' C) :
    IsQuotientMap f := by
  refine isQuotientMap_iff_isClosed.mpr ⟨hsurj, fun S => ⟨fun h => h.preimage hf, ?_⟩⟩
  intro hS
  apply (CompactlyGeneratedSpace.isClosed_iff_of_t2 S).mpr
  intro K hK
  obtain ⟨C, hC, hcover⟩ := hlift K hK
  have hc : IsCompact ((C ∩ f ⁻¹' S) ∩ f ⁻¹' K) :=
    (hC.inter_right hS).inter_right (hK.isClosed.preimage hf)
  have he : f '' ((C ∩ f ⁻¹' S) ∩ f ⁻¹' K) = S ∩ K := by
    ext y
    constructor
    · rintro ⟨x, ⟨⟨_, hxS⟩, hxK⟩, rfl⟩
      exact ⟨hxS, hxK⟩
    · rintro ⟨hyS, hyK⟩
      obtain ⟨x, hxC, hxy⟩ := hcover hyK
      exact ⟨x, ⟨⟨hxC, by simpa only [mem_preimage, hxy] using hyS⟩,
        by simpa only [mem_preimage, hxy] using hyK⟩, hxy⟩
  rw [← he]
  exact (hc.image hf).isClosed

namespace CartanFactorModel

variable {EG G Q : Type} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [TopologicalSpace Q] [Group Q]
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  {ExpG : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H ExpG)

/-- The actual orbit map is a quotient map. Its topology follows from
compact Cartan lifts and a continuous section of the nilpotent projection. -/
theorem orbitMap_isQuotientMap
    (π : F.N.carrier →* Q) (hπ : Continuous π)
    (s : Q → F.N.carrier) (hs : Continuous s) (hsection : Function.RightInverse s π)
    (α : F.D.carrier →* MulAut Q) (act : G →* Equiv.Perm Q)
    (hact : ∀ u d q, act (F.inclusionN u * F.inclusionD d) q = π u * α d q) :
    IsQuotientMap (fun g => act g 1) := by
  let _ : IsTopologicalGroup G := topologicalGroup_of_lieGroup (𝓘(ℝ, EG)) ⊤
  let p : F.N.carrier × F.D.carrier → G := fun z => F.inclusionN z.1 * F.inclusionD z.2
  have hp : IsQuotientMap p := isQuotientMap_of_compact_lifts p
    ((F.closedN.continuous.comp continuous_fst).mul (F.closedD.continuous.comp continuous_snd))
    F.surjective F.compactLifts
  have hcont : Continuous (fun g => act g 1) := hp.continuous_iff.mpr (by
    have hh : (fun z : F.N.carrier × F.D.carrier => act (p z) 1) =
        fun z => π z.1 := by
      funext z
      simp only [p, hact, map_one, mul_one]
    change Continuous (fun z => act (p z) 1)
    rw [hh]
    exact hπ.comp continuous_fst)
  have hright : Function.LeftInverse (fun g => act g 1) (fun q => F.inclusionN (s q)) := by
    intro q
    have hh := hact (s q) 1 1
    simpa only [map_one, mul_one, hsection q] using hh
  exact IsQuotientMap.of_inverse (F.closedN.continuous.comp hs) hcont hright

end CartanFactorModel
end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_ExponentialHaarImage
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Image volumes under exponential-coordinate automorphisms -/

noncomputable section
namespace PolycyclicRecognition

open Module MeasureTheory
open scoped Manifold

variable {L : Type} [LieRing L] [LieAlgebra ℝ L]
  {E G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace G] [ChartedSpace E G] [Group G]
  [LieGroup (𝓘(ℝ, E)) ⊤ G] [MeasurableSpace G] [BorelSpace G]
  (e : L ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, E)) G)
  (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G) (hbij : Function.Bijective Exp)
  (chart : GroupLieAlgebra (𝓘(ℝ, E)) G ≃ₜ G) (hchart : ∀ x, chart x = Exp x)
  {n : ℕ} (b : Basis (Fin n) ℝ L)

include hchart in
/-- A positive exponential determinant is the image-volume multiplier.
This identity holds for arbitrary sets, using the measurable embedding. -/
theorem exponentialConjugate_image_measure
    (F : L ≃ₗ⁅ℝ⁆ L) (d : ℝ)
    (hd : LinearMap.det F.toLinearEquiv.toLinearMap = Real.exp d) (S : Set G) :
    (Measure.map ((Exp ∘ e) ∘ b.equivFun.symm) volume)
      (exponentialConjugate e Exp hbij F '' S) =
    ENNReal.ofReal (Real.exp d) *
      (Measure.map ((Exp ∘ e) ∘ b.equivFun.symm) volume) S := by
  let A : (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ) :=
    (b.equivFun.symm.trans F.toLinearEquiv).trans b.equivFun
  let f : (Fin n → ℝ) ≃ₜ G :=
    (b.equivFun.symm.trans e.toLinearEquiv).toContinuousLinearEquiv.toHomeomorph.trans chart
  let g : G ≃ₜ G := (f.symm.trans A.toContinuousLinearEquiv.toHomeomorph).trans f
  let μ := Measure.map ((Exp ∘ e) ∘ b.equivFun.symm) volume
  have hf : (f : (Fin n → ℝ) → G) = (Exp ∘ e) ∘ b.equivFun.symm := by
    funext t
    exact hchart _
  have hg : (g : G → G) = exponentialConjugate e Exp hbij F := by
    funext x
    obtain ⟨v, rfl⟩ := f.surjective x
    change f (A (f.symm (f v))) = _
    rw [f.symm_apply_apply, hf]
    simp only [A, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply, Function.comp_apply]
    change Exp (e (F (b.equivFun.symm v))) = _
    exact (exponentialConjugate_apply_exp e Exp hbij F (b.equivFun.symm v)).symm
  have hm := exponentialConjugate_map_measure e Exp hbij chart hchart b F
  rw [← hg, hd, ← Real.exp_neg, abs_of_pos (Real.exp_pos _)] at hm
  have hv := congrArg (fun ν : Measure G => ν (g '' S)) hm
  rw [g.measurableEmbedding.map_apply, Set.preimage_image_eq _ g.injective,
    Measure.smul_apply, smul_eq_mul] at hv
  have hmul : ENNReal.ofReal (Real.exp d) * ENNReal.ofReal (Real.exp (-d)) = 1 := by
    rw [← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add, add_neg_cancel,
      Real.exp_zero, ENNReal.ofReal_one]
  rw [← hg]
  change μ (g '' S) = ENNReal.ofReal (Real.exp d) * μ S
  calc
    μ (g '' S) = 1 * μ (g '' S) := (one_mul _).symm
    _ = (ENNReal.ofReal (Real.exp d) * ENNReal.ofReal (Real.exp (-d))) * μ (g '' S) := by rw [hmul]
    _ = ENNReal.ofReal (Real.exp d) * μ S := by rw [mul_assoc, ← hv]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_ConeQuotientHaar
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instDecidableEqConeMixedWords _root_.OAI.PolycyclicRecognition.CartanWordModel.instFintypeConeMixedWords _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The exact positive character of quotient Haar measure -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule MeasureTheory
open scoped Manifold

variable {L : Type} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {H : LieSubalgebra ℝ L} [H.IsCartanSubalgebra] (M : CartanWordModel H)
  {n : ℕ} (T : TriangularAdjoint L n)

/-- A single Haar measure has the quotient Jacobian character for every
Cartan parameter. The character coefficients are positive exactly on the
retained generators. -/
theorem exists_cone_haar_multiplier
    (C : Set (H →ₗ[ℝ] ℝ)) (hadd : ∀ x ∈ C, ∀ y ∈ C, x + y ∈ C)
    (Q : NilpotentLieModel ((cartanRootIdeal H) ⧸ M.coneWordIdeal C))
    (ExpQ : GroupLieAlgebra (𝓘(ℝ, Q.modelSpace)) Q.carrier → Q.carrier)
    (hExpQ : IsGroupExponential ExpQ) (hbij : Function.Bijective ExpQ)
    (haar : NilpotentExponentialHaarInput Q.modelSpace Q.carrier) :
    ∃ (μ : Measure Q.carrier) (c : Fin M.letterCount → ℕ), μ.IsHaarMeasure ∧
      (∀ i, (M.weight i : H →ₗ[ℝ] ℝ) ∉ C → c i = 0) ∧
      (∀ i, (M.weight i : H →ₗ[ℝ] ℝ) ∈ C → 0 < c i) ∧
      (∀ h : H, Measure.map
        (exponentialConjugate Q.equiv ExpQ hbij (M.coneAdjointAutomorphism T C hadd h)) μ =
        ENNReal.ofReal (Real.exp (-(∑ i, (c i : ℝ) * M.weight i h))) • μ) ∧
      ∀ (h : H) (S : Set Q.carrier),
        μ (exponentialConjugate Q.equiv ExpQ hbij (M.coneAdjointAutomorphism T C hadd h) '' S) =
        ENNReal.ofReal (Real.exp (∑ i, (c i : ℝ) * M.weight i h)) * μ S := by
  obtain ⟨⟨chart, hchart⟩, hhaar⟩ :=
    haar.2 ExpQ hExpQ (Q.tangent_nilpotent (M.coneQuotient_nilpotent C))
  let b := Module.finBasis ℝ ((cartanRootIdeal H) ⧸ M.coneWordIdeal C)
  let μ := Measure.map ((ExpQ ∘ Q.equiv) ∘ b.equivFun.symm) volume
  obtain ⟨c, hout, hin, htrace⟩ := M.exists_positive_cone_trace_coefficients C hadd
  refine ⟨μ, c, ?_, hout, hin, ?_, ?_⟩
  · have hf : (ExpQ ∘ Q.equiv) ∘ b.equivFun.symm =
        ExpQ ∘ (b.map Q.equiv.toLinearEquiv).equivFun.symm := by
      funext x
      rw [Basis.map_equivFun]
      rfl
    dsimp only [μ]
    rw [hf]
    exact hhaar _ (b.map Q.equiv.toLinearEquiv)
  · intro h
    have hd := M.det_coneAdjointAutomorphism T C hadd h
    rw [htrace] at hd
    have hm := exponentialConjugate_map_measure Q.equiv ExpQ hbij chart hchart b
      (M.coneAdjointAutomorphism T C hadd h)
    rw [hd, ← Real.exp_neg, abs_of_pos (Real.exp_pos _)] at hm
    exact hm
  · intro h S
    have hd := M.det_coneAdjointAutomorphism T C hadd h
    rw [htrace] at hd
    exact exponentialConjugate_image_measure Q.equiv ExpQ hbij chart hchart b
      (M.coneAdjointAutomorphism T C hadd h) _ hd S

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_BoundaryCompactSandwich
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform compact sandwiches for boundary images

A coarse pair and its compact boundary shadows give both inclusions used
in the boundary volume comparison. The sets are uniform in the pair and
in the ambient basepoint.
-/

noncomputable section
namespace PolycyclicRecognition

open Set Metric
open scoped Pointwise

/-- A compact set in the source boundary has one common compact image
shadow under a family with common coarse Lipschitz and shadow bounds. -/
theorem compact_boundary_image_upper
    {P G S T : Type} [Group G] [MetricSpace G] [IsTopologicalGroup G]
    [IsIsometricSMul G G] [ProperSpace G]
    [One S] [TopologicalSpace S] [One T]
    (actS : G →* Equiv.Perm S) (actT : G →* Equiv.Perm T)
    (B : P → S → T) (f : P → G → G)
    {L error : ℝ} (hL : 0 ≤ L)
    (hf : ∀ p x y, dist (f p x) (f p y) ≤ L * dist x y + error)
    (σ : S → G) (hσ : Continuous σ) (hsection : ∀ q, actS (σ q) 1 = q)
    (KT : Set G) (hKT : IsCompact KT)
    (hB : ∀ p x, ∃ v ∈ KT, B p (actS x 1) = actT (f p x) (actT v 1))
    (U : Set S) (hU : IsCompact U) :
    ∃ V : Set G, IsCompact V ∧ ∀ p x,
      B p '' (actS x '' U) ⊆ actT (f p x) '' ((fun g => actT g 1) '' V) := by
  obtain ⟨R, hR⟩ := (hU.image hσ).exists_bound_of_continuousOn
    ((continuous_const : Continuous (fun _ : G => (1 : G))).dist continuous_id).continuousOn
  let radius := L * R + error
  refine ⟨closedBall (1 : G) radius * KT, (isCompact_closedBall _ _).mul hKT, ?_⟩
  intro p x y hy
  rcases hy with ⟨s, ⟨q, hq, rfl⟩, rfl⟩
  let u := σ q
  have hu : dist 1 u ≤ R := by
    have hh := hR u ⟨q, hq, rfl⟩
    simpa only [Real.norm_eq_abs, abs_of_nonneg dist_nonneg, id_eq] using hh
  obtain ⟨v, hv, he⟩ := hB p (x * u)
  let δ := (f p x)⁻¹ * f p (x * u)
  have hδ : δ ∈ closedBall (1 : G) radius := by
    have hd : dist 1 δ = dist (f p x) (f p (x * u)) := by
      simpa only [δ, mul_one, mul_inv_cancel_left] using
        (dist_mul_left (f p x) (1 : G) δ).symm
    have hc := hf p x (x * u)
    have hs : dist x (x * u) = dist 1 u := by
      simpa only [mul_one] using dist_mul_left x (1 : G) u
    rw [mem_closedBall, dist_comm, hd]
    exact hc.trans (by rw [hs]; exact add_le_add (mul_le_mul_of_nonneg_left hu hL) le_rfl)
  refine ⟨actT (δ * v) 1, ⟨δ * v, Set.mul_mem_mul hδ hv, rfl⟩, ?_⟩
  have hsource : actS (x * u) 1 = actS x q := by
    simp only [map_mul, Equiv.Perm.mul_apply, u, hsection]
  have htarget : actT (f p x) (actT (δ * v) 1) = actT (f p (x * u)) (actT v 1) := by
    rw [← Equiv.Perm.mul_apply, ← map_mul, ← mul_assoc]
    simp only [δ, mul_inv_cancel_left, map_mul, Equiv.Perm.mul_apply]
  exact htarget.trans (by simpa only [hsource] using he.symm)

/-- Both compact inclusions needed for volume comparison follow from
coarse inverses and the already constructed boundary shadows. -/
theorem boundary_image_compact_sandwich
    {P G S T : Type} [Group G] [MetricSpace G] [IsTopologicalGroup G]
    [IsIsometricSMul G G] [ProperSpace G]
    [One S] [TopologicalSpace S] [One T] [TopologicalSpace T]
    (actS : G →* Equiv.Perm S) (actT : G →* Equiv.Perm T)
    (hcontS : Continuous (fun g => actS g 1))
    (hcontT : Continuous (fun g => actT g 1))
    (B : P → S → T) (C : P → T → S) (f g : P → G → G)
    {Lf Lg ef eg E : ℝ} (hLf : 0 ≤ Lf) (hLg : 0 ≤ Lg)
    (hf : ∀ p x y, dist (f p x) (f p y) ≤ Lf * dist x y + ef)
    (hg : ∀ p x y, dist (g p x) (g p y) ≤ Lg * dist x y + eg)
    (hinv : ∀ p x, dist (g p (f p x)) x ≤ E)
    (hBC : ∀ p, Function.RightInverse (C p) (B p))
    (σS : S → G) (hσS : Continuous σS) (hsectionS : ∀ q, actS (σS q) 1 = q)
    (σT : T → G) (hσT : Continuous σT) (hsectionT : ∀ q, actT (σT q) 1 = q)
    (KS KT : Set G) (hKS : IsCompact KS) (hKT : IsCompact KT)
    (hB : ∀ p x, ∃ v ∈ KT, B p (actS x 1) = actT (f p x) (actT v 1))
    (hC : ∀ p x, ∃ v ∈ KS, C p (actT x 1) = actS (g p x) (actS v 1))
    (U₀ : Set S) (hU₀ : IsCompact U₀) (Vminus : Set T) (hVminus : IsCompact Vminus) :
    ∃ (U : Set S) (Vplus : Set T), IsCompact U ∧ IsCompact Vplus ∧ U₀ ⊆ U ∧
      ∀ p x, actT (f p x) '' Vminus ⊆ B p '' (actS x '' U) ∧
        B p '' (actS x '' U) ⊆ actT (f p x) '' Vplus := by
  obtain ⟨V, hV, hVupper⟩ := compact_boundary_image_upper actT actS C g hLg hg
    σT hσT hsectionT KS hKS hC Vminus hVminus
  let U := ((fun z => actS z 1) '' (closedBall (1 : G) E * V)) ∪ U₀
  have hU : IsCompact U := ((isCompact_closedBall _ _).mul hV).image hcontS |>.union hU₀
  obtain ⟨W, hW, hWupper⟩ := compact_boundary_image_upper actS actT B f hLf hf
    σS hσS hsectionS KT hKT hB U hU
  refine ⟨U, (fun z => actT z 1) '' W, hU, hW.image hcontT, subset_union_right, ?_⟩
  intro p x
  refine ⟨?_, hWupper p x⟩
  intro y hy
  have hc := hVupper p (f p x) (Set.mem_image_of_mem (C p) hy)
  rcases hc with ⟨q, ⟨v, hv, rfl⟩, hq⟩
  let δ := x⁻¹ * g p (f p x)
  have hδ : δ ∈ closedBall (1 : G) E := by
    have hd : dist 1 δ = dist x (g p (f p x)) := by
      simpa only [δ, mul_one, mul_inv_cancel_left] using
        (dist_mul_left x (1 : G) δ).symm
    rw [mem_closedBall, dist_comm, hd, dist_comm]
    exact hinv p x
  have hmem : actS (δ * v) 1 ∈ U := Or.inl ⟨δ * v, Set.mul_mem_mul hδ hv, rfl⟩
  have he : actS x (actS (δ * v) 1) = C p y := by
    rw [← Equiv.Perm.mul_apply, ← map_mul, ← mul_assoc]
    simpa only [δ, mul_inv_cancel_left, map_mul, Equiv.Perm.mul_apply] using hq
  exact ⟨C p y, ⟨actS (δ * v) 1, hmem, he⟩, hBC p y⟩

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_BoundaryHeight
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Scalar and vector boundary height estimates

Haar-volume distortion on ray quotients yields additive trace bounds after
taking logarithms. Finitely many spanning traces then bound the full height
error. A linear coefficient compatible with a sublinear error is unique.
-/

namespace PolycyclicRecognition

/-- Uniform multiplicative comparison of positive quantities bounds the
difference of their logarithms. -/
theorem abs_log_sub_le_of_comparison {a b K : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hK : 0 < K) (hab : a ≤ K * b) (hba : b ≤ K * a) :
    |Real.log a - Real.log b| ≤ Real.log K := by
  apply abs_sub_le_iff.mpr
  constructor
  · have h := Real.log_le_log ha hab
    rw [Real.log_mul hK.ne' hb.ne'] at h
    linarith
  · have h := Real.log_le_log hb hba
    rw [Real.log_mul hK.ne' ha.ne'] at h
    linarith

/-- Applying the logarithmic comparison to exponential Jacobians. -/
theorem abs_sub_le_log_of_exp_comparison {a b K : ℝ} (hK : 0 < K)
    (hab : Real.exp a ≤ K * Real.exp b) (hba : Real.exp b ≤ K * Real.exp a) :
    |a - b| ≤ Real.log K := by
  simpa only [Real.log_exp] using abs_log_sub_le_of_comparison
    (Real.exp_pos a) (Real.exp_pos b) hK hab hba

end PolycyclicRecognition

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_BoundaryVolumeTrace
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Boundary volume sandwiches bound trace-height differences -/

noncomputable section
namespace PolycyclicRecognition

open MeasureTheory Set

/-- Equal source boundary sets have equal images. A fixed positive lower
volume and finite upper volume then bound the difference of the two
logarithmic Haar characters. The constant is independent of the map. -/
theorem boundary_trace_bound_of_sandwich
    {P G S T : Type} [Group G] [MeasurableSpace T]
    (actS : G →* Equiv.Perm S) (actT : G →* Equiv.Perm T)
    (B : P → S → T) (f : P → G → G) (μ : Measure T) (height : G → ℝ)
    (hvolume : ∀ g E, μ (actT g '' E) = ENNReal.ofReal (Real.exp (height g)) * μ E)
    (U : Set S) (Vminus Vplus : Set T)
    (hVminus0 : μ Vminus ≠ 0) (hVminusfinite : μ Vminus ≠ ⊤) (hVplusfinite : μ Vplus ≠ ⊤)
    (hsandwich : ∀ p x, actT (f p x) '' Vminus ⊆ B p '' (actS x '' U) ∧
      B p '' (actS x '' U) ⊆ actT (f p x) '' Vplus) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ p x y, actS x '' U = actS y '' U →
      |height (f p x) - height (f p y)| ≤ K := by
  let c := (μ Vminus).toReal
  let C := (μ Vplus).toReal
  have hc : 0 < c := ENNReal.toReal_pos hVminus0 hVminusfinite
  have hC : 0 ≤ C := ENNReal.toReal_nonneg
  let K := C / c + 1
  have hK : 0 < K := by dsimp [K] <;> positivity
  have hKc : K * c = C + c := by
    dsimp only [K]
    rw [add_mul, div_mul_cancel₀ _ hc.ne', one_mul]
  have hcmp (p : P) (x y : G) (he : actS x '' U = actS y '' U) :
      Real.exp (height (f p x)) ≤ K * Real.exp (height (f p y)) := by
    have hs : actT (f p x) '' Vminus ⊆ actT (f p y) '' Vplus := by
      exact (hsandwich p x).1.trans (he ▸ (hsandwich p y).2)
    have hm := measure_mono (μ := μ) hs
    rw [hvolume, hvolume] at hm
    have hr := ENNReal.toReal_mono (by finiteness) hm
    simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.exp_pos _).le] at hr
    change Real.exp (height (f p x)) * c ≤ Real.exp (height (f p y)) * C at hr
    have hh : Real.exp (height (f p x)) * c ≤ (K * Real.exp (height (f p y))) * c := by
      calc
        Real.exp (height (f p x)) * c ≤ Real.exp (height (f p y)) * C := hr
        _ ≤ Real.exp (height (f p y)) * (C + c) := by gcongr; linarith
        _ = (K * Real.exp (height (f p y))) * c := by rw [mul_assoc, mul_comm (Real.exp _) c, ← mul_assoc, hKc, mul_comm]
    exact (mul_le_mul_iff_left₀ hc).mp hh
  refine ⟨max 0 (Real.log K), le_max_left _ _, ?_⟩
  intro p x y he
  exact (abs_sub_le_log_of_exp_comparison hK (hcmp p x y he) (hcmp p y x he.symm)).trans
    (le_max_right _ _)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_BoundaryImageMass
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Absolute boundary masses from compact image sandwiches -/

noncomputable section
namespace PolycyclicRecognition

open MeasureTheory Set
open scoped ENNReal

/-- A compact lower/upper sandwich gives one positive comparison constant
for the absolute boundary image masses throughout the map family. -/
theorem boundary_image_mass_bounds
    {P G S T : Type} [Group G] [MeasurableSpace T]
    (actS : G →* Equiv.Perm S) (actT : G →* Equiv.Perm T)
    (B : P → S → T) (f : P → G → G) (μ : Measure T) (height : G → ℝ)
    (hvolume : ∀ g E, μ (actT g '' E) = ENNReal.ofReal (Real.exp (height g)) * μ E)
    (U : Set S) (Vminus Vplus : Set T)
    (hVminus0 : μ Vminus ≠ 0) (hVminusfinite : μ Vminus ≠ ⊤) (hVplusfinite : μ Vplus ≠ ⊤)
    (hsandwich : ∀ p x, actT (f p x) '' Vminus ⊆ B p '' (actS x '' U) ∧
      B p '' (actS x '' U) ⊆ actT (f p x) '' Vplus) :
    ∃ K : ℝ, 0 < K ∧ ∀ p x,
      ENNReal.ofReal (Real.exp (height (f p x))) ≤
        ENNReal.ofReal K * μ (B p '' (actS x '' U)) ∧
      μ (B p '' (actS x '' U)) ≤
        ENNReal.ofReal K * ENNReal.ofReal (Real.exp (height (f p x))) := by
  let c := (μ Vminus).toReal
  let C := (μ Vplus).toReal
  have hc : 0 < c := ENNReal.toReal_pos hVminus0 hVminusfinite
  have hC : 0 ≤ C := ENNReal.toReal_nonneg
  let K := C + 1 / c + 1
  have hK : 0 < K := by dsimp [K] <;> positivity
  have hKC : C ≤ K := by dsimp [K] <;> linarith [one_div_nonneg.mpr hc.le]
  have hKc : 1 ≤ K * c := by
    have h : (1 / c) * c = (1 : ℝ) := div_mul_cancel₀ 1 hc.ne'
    dsimp only [K]
    nlinarith [mul_nonneg hC hc.le]
  have hKcm : 1 ≤ ENNReal.ofReal K * μ Vminus := by
    rw [← ENNReal.ofReal_toReal hVminusfinite, ← ENNReal.ofReal_mul hK.le]
    exact_mod_cast ENNReal.ofReal_le_ofReal hKc
  have hCm : μ Vplus ≤ ENNReal.ofReal K := by
    rw [← ENNReal.ofReal_toReal hVplusfinite]
    exact ENNReal.ofReal_le_ofReal hKC
  refine ⟨K, hK, ?_⟩
  intro p x
  have hlo := measure_mono (μ := μ) (hsandwich p x).1
  have hup := measure_mono (μ := μ) (hsandwich p x).2
  rw [hvolume] at hlo hup
  constructor
  · calc
      ENNReal.ofReal (Real.exp (height (f p x))) =
          ENNReal.ofReal (Real.exp (height (f p x))) * 1 := (mul_one _).symm
      _ ≤ ENNReal.ofReal (Real.exp (height (f p x))) *
          (ENNReal.ofReal K * μ Vminus) := mul_le_mul' le_rfl hKcm
      _ = ENNReal.ofReal K *
          (ENNReal.ofReal (Real.exp (height (f p x))) * μ Vminus) := by ac_rfl
      _ ≤ ENNReal.ofReal K * μ (B p '' (actS x '' U)) := mul_le_mul' le_rfl hlo
  · exact hup.trans (by simpa only [mul_comm] using mul_le_mul' le_rfl hCm)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_BoundaryFamilyMass
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instNonemptyBases _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_nonempty _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform masses and equal-set traces for a compact-shadow family -/

noncomputable section
namespace PolycyclicRecognition

open Set MeasureTheory TopologicalSpace
open scoped ENNReal

/-- The compact shadows provide a single source window with uniform mass
and trace bounds. A compact set with interior in the source can be retained
inside this window for the subsequent averaging argument. -/
theorem boundary_family_mass_and_trace_of_compact_shadows
    {P G S T : Type} [Group G] [MetricSpace G] [IsTopologicalGroup G]
    [IsIsometricSMul G G] [ProperSpace G]
    [One S] [TopologicalSpace S]
    [Group T] [TopologicalSpace T] [IsTopologicalGroup T] [LocallyCompactSpace T]
    [MeasurableSpace T] [BorelSpace T]
    (actS : G →* Equiv.Perm S) (actT : G →* Equiv.Perm T)
    (hcontS : Continuous (fun g => actS g 1))
    (hcontT : Continuous (fun g => actT g 1))
    (B : P → S → T) (C : P → T → S) (f g : P → G → G)
    {Lf Lg ef eg E : ℝ} (hLf : 0 ≤ Lf) (hLg : 0 ≤ Lg)
    (hf : ∀ p x y, dist (f p x) (f p y) ≤ Lf * dist x y + ef)
    (hg : ∀ p x y, dist (g p x) (g p y) ≤ Lg * dist x y + eg)
    (hinv : ∀ p x, dist (g p (f p x)) x ≤ E)
    (hBC : ∀ p, Function.RightInverse (C p) (B p))
    (σS : S → G) (hσS : Continuous σS) (hsectionS : ∀ q, actS (σS q) 1 = q)
    (σT : T → G) (hσT : Continuous σT) (hsectionT : ∀ q, actT (σT q) 1 = q)
    (KS : Set S) (KT : Set T) (hKS : IsCompact KS) (hKT : IsCompact KT)
    (hB : ∀ p x, ∃ q ∈ KT, B p (actS x 1) = actT (f p x) q)
    (hC : ∀ p x, ∃ q ∈ KS, C p (actT x 1) = actS (g p x) q)
    (μ : Measure T) [μ.IsHaarMeasure] (height : G → ℝ)
    (hvolume : ∀ x V, μ (actT x '' V) = ENNReal.ofReal (Real.exp (height x)) * μ V)
    (U₀ : Set S) (hU₀ : IsCompact U₀) :
    ∃ (U : Set S) (K D : ℝ), IsCompact U ∧ U₀ ⊆ U ∧ 0 < K ∧ 0 ≤ D ∧
      (∀ p x, ENNReal.ofReal (Real.exp (height (f p x))) ≤
          ENNReal.ofReal K * μ (B p '' (actS x '' U)) ∧
        μ (B p '' (actS x '' U)) ≤
          ENNReal.ofReal K * ENNReal.ofReal (Real.exp (height (f p x)))) ∧
      ∀ p x y, actS x '' U = actS y '' U → |height (f p x) - height (f p y)| ≤ D := by
  classical
  let Vminus : PositiveCompacts T := Classical.choice inferInstance
  have hVminus0 : μ (Vminus : Set T) ≠ 0 :=
    (Measure.measure_pos_of_nonempty_interior μ Vminus.interior_nonempty).ne'
  have hVminusfin : μ (Vminus : Set T) ≠ ⊤ := Vminus.isCompact.measure_ne_top
  let KSG := σS '' KS
  let KTG := σT '' KT
  have hB' : ∀ p x, ∃ v ∈ KTG, B p (actS x 1) = actT (f p x) (actT v 1) := by
    intro p x
    obtain ⟨q, hq, he⟩ := hB p x
    exact ⟨σT q, ⟨q, hq, rfl⟩, by simpa only [hsectionT] using he⟩
  have hC' : ∀ p x, ∃ v ∈ KSG, C p (actT x 1) = actS (g p x) (actS v 1) := by
    intro p x
    obtain ⟨q, hq, he⟩ := hC p x
    exact ⟨σS q, ⟨q, hq, rfl⟩, by simpa only [hsectionS] using he⟩
  obtain ⟨U, Vplus, hU, hVplus, hU₀U, hsandwich⟩ := boundary_image_compact_sandwich
    actS actT hcontS hcontT B C f g hLf hLg hf hg hinv hBC
    σS hσS hsectionS σT hσT hsectionT KSG KTG (hKS.image hσS) (hKT.image hσT)
    hB' hC' U₀ hU₀ Vminus Vminus.isCompact
  obtain ⟨K, hK, hmass⟩ := boundary_image_mass_bounds actS actT B f μ height hvolume
    U Vminus Vplus hVminus0 hVminusfin hVplus.measure_ne_top hsandwich
  obtain ⟨D, hD, htrace⟩ := boundary_trace_bound_of_sandwich actS actT B f μ height hvolume
    U Vminus Vplus hVminus0 hVminusfin hVplus.measure_ne_top hsandwich
  exact ⟨U, K, D, hU, hU₀U, hK, hD, hmass, htrace⟩

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanWordLogarithms
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Cartan logarithms of bounded words

The Cartan group is nilpotent. The finite Dynkin identity therefore gives a
polynomial bound on the logarithm of every prefix of a bounded word. We also
record the exact semidirect-product word formula used to apply the controlled
Cartan estimates to such prefixes.
-/

noncomputable section

namespace PolycyclicRecognition

open Module LieModule
open scoped Manifold

variable {L : Type} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  (H : LieSubalgebra ℝ L) [H.IsCartanSubalgebra]
  {ED D : Type} [NormedAddCommGroup ED] [NormedSpace ℝ ED]
  [FiniteDimensional ℝ ED] [TopologicalSpace D] [ChartedSpace ED D] [Group D]
  [LieGroup (𝓘(ℝ, ED)) ⊤ D] [T2Space D]
  (eD : H ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, ED)) D)
  (ExpD : GroupLieAlgebra (𝓘(ℝ, ED)) D → D) (hbijD : Function.Bijective ExpD)

set_option maxHeartbeats 1000000 in
omit [FiniteDimensional ℝ L] [H.IsCartanSubalgebra] [T2Space D] in
theorem exp_cartanLog (d : D) : ExpD (eD (cartanLog H eD ExpD hbijD d)) = d := by
  unfold cartanLog
  rw [eD.apply_symm_apply]
  exact (Equiv.ofBijective ExpD hbijD).apply_symm_apply d

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanSemidirectWords
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instDecidableEqConeMixedWords _root_.OAI.PolycyclicRecognition.CartanWordModel.instFintypeConeMixedWords _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Controlled words in the actual semidirect product

Nilpotent Cartan increments give polynomial bounds on every Cartan prefix.
The exact semidirect-product formula then reduces its nilpotent coordinate
to the controlled product estimate. No polynomial bound on prefixes is left
as an assumption of this theorem.
-/

noncomputable section

namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule
open scoped Manifold

variable {L : Type} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {H : LieSubalgebra ℝ L} [H.IsCartanSubalgebra] (M : CartanWordModel H)
  {n : ℕ} (T : TriangularAdjoint L n)
  (hunimod : ∀ x : L, LinearMap.trace ℝ L (ad ℝ L x) = 0)
  {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)
  {EN N : Type} [NormedAddCommGroup EN] [NormedSpace ℝ EN]
  [FiniteDimensional ℝ EN] [TopologicalSpace N] [ChartedSpace EN N] [Group N]
  [LieGroup (𝓘(ℝ, EN)) ⊤ N] [T2Space N]
  (eN : cartanRootIdeal H ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, EN)) N)
  (ExpN : GroupLieAlgebra (𝓘(ℝ, EN)) N → N) (hExpN : IsGroupExponential ExpN)
  (hbijN : Function.Bijective ExpN) (dynkinN : NilpotentDynkinExpansionInput EN N)
  {ED D : Type} [NormedAddCommGroup ED] [NormedSpace ℝ ED]
  [FiniteDimensional ℝ ED] [TopologicalSpace D] [ChartedSpace ED D] [Group D]
  [LieGroup (𝓘(ℝ, ED)) ⊤ D] [T2Space D]
  (eD : H ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, ED)) D)
  (ExpD : GroupLieAlgebra (𝓘(ℝ, ED)) D → D) (hExpD : IsGroupExponential ExpD)
  (hbijD : Function.Bijective ExpD) (dynkinD : NilpotentDynkinExpansionInput ED D)
  (φ : D →* MulAut N)

section Representation

variable {A G : Type} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A] [Group G]

attribute [local instance 100] LieRing.ofAssociativeRing

set_option maxHeartbeats 1000000 in
omit [T2Space D] in
/-- The required semidirect action identity follows from compatible
exponentials in an ambient faithful representation. -/
theorem action_eq_adjoint_of_representation
    (j : L →ₗ⁅ℝ⁆ A) (ρ : G →* Aˣ) (hρ : Function.Injective ρ)
    (ιN : N →* G) (hιN : Function.Injective ιN) (ιD : D →* G)
    (hconj : ∀ d g, ιN (φ d g) = ιD d * ιN g * (ιD d)⁻¹)
    (hN : ∀ x : cartanRootIdeal H, ρ (ιN (ExpN (eN x))) = algebraExpUnit (j x))
    (hD : ∀ h : H, ρ (ιD (ExpD (eD h))) = algebraExpUnit (j h)) (d : D) :
    φ d = M.adjointGroupAutomorphism T eN ExpN hExpN hbijN dynkinN
      (cartanLog H eD ExpD hbijD d) := by
  apply MulEquiv.ext
  intro g
  apply hιN
  rw [hconj]
  have hh := M.adjointGroupAutomorphism_eq_conjugation T eN ExpN hExpN hbijN dynkinN
    j ρ hρ ιN (fun h => ιD (ExpD (eD h))) hN hD (cartanLog H eD ExpD hbijD d) g
  simpa only [exp_cartanLog] using hh.symm

end Representation

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanFactorHeight
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Canonical height of the constructed Cartan factors

The nilpotent root factor has zero height. The Cartan logarithm records the
height of every lifted prefix exactly, not just up to bounded error.
-/

noncomputable section

namespace PolycyclicRecognition.CartanFactorModel

open scoped Manifold

variable {EG G : Type} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  {ExpG : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H ExpG)
  {W : Type} [AddCommGroup W] [Module ℝ W]
  (q : HeightSpace T.character ≃ₗ[ℝ] W) (π : G →* Multiplicative W)
  (hπExp : ∀ x, (π (ExpG x)).toAdd = q (heightProjection T.character x))

set_option maxHeartbeats 1000000 in
include hπExp in
/-- The root ideal lies in the canonical height kernel, hence so does its
entire integrated group. -/
theorem inclusionN_height_eq_one
    (hbij : Function.Bijective F.ExpN) (n : F.N.carrier) :
    π (F.inclusionN n) = 1 := by
  obtain ⟨x, rfl⟩ := (hbij.comp F.N.equiv.bijective).surjective n
  change π (F.inclusionN (F.ExpN (F.N.equiv x))) = 1
  rw [F.compatibleN]
  change (π (ExpG x)).toAdd = 0
  rw [hπExp]
  have hz : heightProjection T.character (x : GroupLieAlgebra (𝓘(ℝ, EG)) G) = 0 :=
    (Submodule.Quotient.mk_eq_zero _).mpr (cartanRootIdeal_le_kernel H T x.property)
  rw [hz, map_zero]

set_option maxHeartbeats 1000000 in
include hπExp in
/-- Cartan logarithmic coordinates recover the actual ambient height. -/
theorem inclusionD_height
    (hbij : Function.Bijective F.ExpD) (d : F.D.carrier) :
    (π (F.inclusionD d)).toAdd = q (heightProjection T.character
      (cartanLog H F.D.equiv F.ExpD hbij d : GroupLieAlgebra (𝓘(ℝ, EG)) G)) := by
  have h := F.compatibleD (cartanLog H F.D.equiv F.ExpD hbij d)
  rw [exp_cartanLog H F.D.equiv F.ExpD hbij d] at h
  rw [h, hπExp]

end PolycyclicRecognition.CartanFactorModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_PositiveWeightCones
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The positive parts of the ray and two-generator cones -/

noncomputable section
namespace PolycyclicRecognition

open Set
open scoped BigOperators

variable {V : Type} [AddCommGroup V] [Module ℝ V]

/-- Positive integral multiplicities on a ray give a positive ray character. -/
theorem positive_sum_on_weightRay {I : Type} [Fintype I]
    (α : V) (β : I → V) (c : I → ℕ)
    (hout : ∀ i, β i ∉ positiveWeightRay α → c i = 0)
    (i₀ : I) (h₀ : β i₀ ∈ positiveWeightRay α) (hc₀ : 0 < c i₀) :
    ∃ a : ℝ, 0 < a ∧ ∑ i, (c i : ℝ) • β i = a • α := by
  classical
  have hd (i) : ∃ d : ℝ, 0 ≤ d ∧
      (c i : ℝ) • β i = ((c i : ℝ) * d) • α ∧
      (β i ∈ positiveWeightRay α → 0 < d) := by
    by_cases hi : β i ∈ positiveWeightRay α
    · obtain ⟨d, hd, he⟩ := hi
      exact ⟨d, hd.le, by rw [he, smul_smul], fun _ => hd⟩
    · exact ⟨0, le_rfl, by simp [hout i hi], fun h => False.elim (hi h)⟩
  choose d hd he hp using hd
  refine ⟨∑ i, (c i : ℝ) * d i, ?_, ?_⟩
  · exact lt_of_lt_of_le (mul_pos (Nat.cast_pos.mpr hc₀) (hp i₀ h₀))
      (Finset.single_le_sum (fun i _ => mul_nonneg (Nat.cast_nonneg _) (hd i))
        (Finset.mem_univ i₀))
  · simp_rw [he]
    rw [Finset.sum_smul]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_RayTangentContraction
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instDecidableEqConeMixedWords _root_.OAI.PolycyclicRecognition.CartanWordModel.instFintypeConeMixedWords _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Ray contraction in the actual tangent coordinate basis -/
noncomputable section
namespace PolycyclicRecognition

open Module LieAlgebra LieModule Set
open scoped Manifold

namespace CartanWordModel
variable {L : Type} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {H : LieSubalgebra ℝ L} [H.IsCartanSubalgebra] (M : CartanWordModel H)
  {a : ℕ} (T : TriangularAdjoint L a)

theorem coneAdjoint_projection
    (C : Set (H →ₗ[ℝ] ℝ)) (hadd : ∀ x ∈ C, ∀ y ∈ C, x + y ∈ C)
    (h : H) (x : cartanRootIdeal H) :
    M.coneAdjointAutomorphism T C hadd h (M.coneProjection C x) =
      M.coneProjection C (cartanIdealAdjointAutomorphism T H h x) := rfl

end CartanWordModel
end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanRayFactorContraction
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instDecidableEqConeMixedWords _root_.OAI.PolycyclicRecognition.CartanWordModel.instFintypeConeMixedWords _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Compact increments and contraction for the actual Cartan factors -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule Set
open scoped Manifold

variable {EG G : Type} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {ExpG : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H ExpG)

variable (α₀ : H →ₗ[ℝ] ℝ)
  (Q : NilpotentLieModel ((cartanRootIdeal H) ⧸ M.coneWordIdeal (positiveWeightRay α₀)))
  (ExpQ : GroupLieAlgebra (𝓘(ℝ, Q.modelSpace)) Q.carrier → Q.carrier)
  (hbijQ : Function.Bijective ExpQ)
  (chartQ : GroupLieAlgebra (𝓘(ℝ, Q.modelSpace)) Q.carrier ≃ₜ Q.carrier)
  (hchartQ : ∀ v, chartQ v = ExpQ v)
  (hbijN : Function.Bijective F.ExpN) (hbijD : Function.Bijective F.ExpD)
  (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
  (π : F.N.carrier →* Q.carrier)
  (hπ : ∀ x : cartanRootIdeal H,
    π (F.ExpN (F.N.equiv x)) = ExpQ (Q.equiv (M.coneProjection (positiveWeightRay α₀) x)))
  (α : F.D.carrier →* MulAut Q.carrier)
  (hα : ∀ d n, α d (π n) = π (F.action d n))
  (hφ : ∀ d, F.action d = M.adjointGroupAutomorphism T F.N.equiv F.ExpN F.isExpN
    hbijN dynkinN (cartanLog H F.D.equiv F.ExpD hbijD d))

set_option maxHeartbeats 1000000 in
include hπ hα hφ in
/-- The quotient action of each actual Cartan factor is the exponential
of its induced Lie action, with the actual Cartan logarithm. -/
theorem factor_quotient_action_eq_exponential (d : F.D.carrier) (q : Q.carrier) :
    α d q = exponentialConjugate Q.equiv ExpQ hbijQ
      (M.coneAdjointAutomorphism T (positiveWeightRay α₀) (positiveWeightRay_add α₀)
        (cartanLog H F.D.equiv F.ExpD hbijD d)) q := by
  obtain ⟨v, hv⟩ := hbijQ.surjective q
  obtain ⟨w, hw⟩ := Q.equiv.surjective v
  obtain ⟨x, hx⟩ := M.coneProjection_surjective (positiveWeightRay α₀) w
  have hq : ExpQ (Q.equiv (M.coneProjection (positiveWeightRay α₀) x)) = q :=
    (congrArg ExpQ ((congrArg Q.equiv hx).trans hw)).trans hv
  rw [← hq]
  let h := cartanLog H F.D.equiv F.ExpD hbijD d
  have he : F.action d (F.ExpN (F.N.equiv x)) =
      F.ExpN (F.N.equiv (cartanIdealAdjointAutomorphism T H h x)) := by
    exact (congrArg (fun a : MulAut F.N.carrier => a (F.ExpN (F.N.equiv x)))
      (hφ d)).trans (integrateNilpotentLieEquiv_apply_exp F.N.equiv F.ExpN hbijN dynkinN
        F.isExpN M.bound_zero (cartanIdealAdjointAutomorphism T H h) x)
  calc
    α d (ExpQ (Q.equiv (M.coneProjection (positiveWeightRay α₀) x))) =
        α d (π (F.ExpN (F.N.equiv x))) := congrArg (α d) (hπ x).symm
    _ = π (F.action d (F.ExpN (F.N.equiv x))) := hα d _
    _ = π (F.ExpN (F.N.equiv (cartanIdealAdjointAutomorphism T H h x))) := congrArg π he
    _ = ExpQ (Q.equiv (M.coneProjection (positiveWeightRay α₀)
        (cartanIdealAdjointAutomorphism T H h x))) := hπ _
    _ = _ := by
      have hp := M.coneAdjoint_projection T (positiveWeightRay α₀)
        (positiveWeightRay_add α₀) h x
      exact (congrArg (fun v => ExpQ (Q.equiv v)) hp).symm.trans
        (exponentialConjugate_apply_exp Q.equiv ExpQ hbijQ
          (M.coneAdjointAutomorphism T (positiveWeightRay α₀)
            (positiveWeightRay_add α₀) h) (M.coneProjection (positiveWeightRay α₀) x)).symm

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_ConeHeightMultiplier
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instDecidableEqConeMixedWords _root_.OAI.PolycyclicRecognition.CartanWordModel.instFintypeConeMixedWords _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The quotient Haar character in canonical height coordinates -/

noncomputable section
namespace PolycyclicRecognition

open Module LieAlgebra LieModule MeasureTheory Set
open scoped Manifold BigOperators

namespace CartanWordModel

variable {L W : Type} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {H : LieSubalgebra ℝ L} [H.IsCartanSubalgebra] (M : CartanWordModel H)
  {a : ℕ} (T : TriangularAdjoint L a)
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)

/-- The positive trace coefficients give the exact Haar multiplier as a
linear functional on the already chosen canonical height space. -/
theorem exists_cone_haar_height_multiplier
    (C : Set (H →ₗ[ℝ] ℝ)) (hadd : ∀ x ∈ C, ∀ y ∈ C, x + y ∈ C)
    (Q : NilpotentLieModel ((cartanRootIdeal H) ⧸ M.coneWordIdeal C))
    (ExpQ : GroupLieAlgebra (𝓘(ℝ, Q.modelSpace)) Q.carrier → Q.carrier)
    (hExpQ : IsGroupExponential ExpQ) (hbij : Function.Bijective ExpQ)
    (haar : NilpotentExponentialHaarInput Q.modelSpace Q.carrier) :
    ∃ (μ : Measure Q.carrier) (ell : W →ₗ[ℝ] ℝ) (c : Fin M.letterCount → ℕ),
      μ.IsHaarMeasure ∧
      (∀ i, (M.weight i : H →ₗ[ℝ] ℝ) ∉ C → c i = 0) ∧
      (∀ i, (M.weight i : H →ₗ[ℝ] ℝ) ∈ C → 0 < c i) ∧
      ell = (∑ i, (c i : ℝ) • cartanHeightWeight T H (M.weight i)).comp
        eW.symm.toLinearMap ∧
      ∀ (h : H) (S : Set Q.carrier),
        μ (exponentialConjugate Q.equiv ExpQ hbij
          (M.coneAdjointAutomorphism T C hadd h) '' S) =
        ENNReal.ofReal (Real.exp (ell (eW (heightProjection T.character (h : L))))) * μ S := by
  obtain ⟨μ, c, hμ, hout, hin, _, hvol⟩ :=
    M.exists_cone_haar_multiplier T C hadd Q ExpQ hExpQ hbij haar
  let ell := (∑ i, (c i : ℝ) • cartanHeightWeight T H (M.weight i)).comp eW.symm.toLinearMap
  refine ⟨μ, ell, c, hμ, hout, hin, rfl, ?_⟩
  intro h S
  have heval : ell (eW (heightProjection T.character (h : L))) =
      ∑ i, (c i : ℝ) * M.weight i h := by
    simp only [ell, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.symm_apply_apply, LinearMap.sum_apply, LinearMap.smul_apply,
      smul_eq_mul, cartanHeightWeight_projection]
  rw [heval]
  exact hvol h S

end CartanWordModel

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanBoundaryHaarAction
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instDecidableEqConeMixedWords _root_.OAI.PolycyclicRecognition.CartanWordModel.instFintypeConeMixedWords _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual boundary Haar action in ambient height coordinates -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule Set Filter MeasureTheory
open scoped Pointwise BigOperators
open scoped Manifold Topology

variable {EG G : Type} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {ExpG : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H ExpG)

variable (α₀ : H →ₗ[ℝ] ℝ)
  (Q : NilpotentLieModel ((cartanRootIdeal H) ⧸ M.coneWordIdeal (positiveWeightRay α₀)))
  (ExpQ : GroupLieAlgebra (𝓘(ℝ, Q.modelSpace)) Q.carrier → Q.carrier)
  (hbijQ : Function.Bijective ExpQ)
  (chartQ : GroupLieAlgebra (𝓘(ℝ, Q.modelSpace)) Q.carrier ≃ₜ Q.carrier)
  (hchartQ : ∀ v, chartQ v = ExpQ v)
  (hbijN : Function.Bijective F.ExpN) (hbijD : Function.Bijective F.ExpD)
  (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
  (π : F.N.carrier →* Q.carrier)
  (hπ : ∀ x : cartanRootIdeal H,
    π (F.ExpN (F.N.equiv x)) = ExpQ (Q.equiv (M.coneProjection (positiveWeightRay α₀) x)))
  (α : F.D.carrier →* MulAut Q.carrier)
  (hα : ∀ d n, α d (π n) = π (F.action d n))
  (hφ : ∀ d, F.action d = M.adjointGroupAutomorphism T F.N.equiv F.ExpN F.isExpN
    hbijN dynkinN (cartanLog H F.D.equiv F.ExpD hbijD d))


set_option maxHeartbeats 1000000 in
include hbijQ hπ hα hφ in
/-- The quotient Haar character is the actual ambient height character.
The nilpotent factor contributes only a Haar-preserving translation. -/
theorem exists_boundary_haar_height_multiplier
    {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W]
    (eW : HeightSpace T.character ≃ₗ[ℝ] W) (height : G →* Multiplicative W)
    (hheight : ∀ x, (height (ExpG x)).toAdd = eW (heightProjection T.character x))
    (hExpQ : IsGroupExponential ExpQ)
    (haar : NilpotentExponentialHaarInput Q.modelSpace Q.carrier)
    (act : G →* Equiv.Perm Q.carrier)
    (hact : ∀ u d q, act (F.inclusionN u * F.inclusionD d) q = π u * α d q) :
    ∃ (μ : Measure Q.carrier) (ell : W →ₗ[ℝ] ℝ) (c : Fin M.letterCount → ℕ),
      μ.IsHaarMeasure ∧
      (∀ i, (M.weight i : H →ₗ[ℝ] ℝ) ∉ positiveWeightRay α₀ → c i = 0) ∧
      (∀ i, (M.weight i : H →ₗ[ℝ] ℝ) ∈ positiveWeightRay α₀ → 0 < c i) ∧
      ell = (∑ i, (c i : ℝ) • cartanHeightWeight T H (M.weight i)).comp
        eW.symm.toLinearMap ∧
      ∀ (g : G) (E : Set Q.carrier), μ (act g '' E) =
        ENNReal.ofReal (Real.exp (ell (height g).toAdd)) * μ E := by
  let _ : IsTopologicalGroup Q.carrier := topologicalGroup_of_lieGroup (𝓘(ℝ, Q.modelSpace)) ⊤
  obtain ⟨μ, ell, c, hμ, hout, hin, hell, hvol⟩ := M.exists_cone_haar_height_multiplier T eW
    (positiveWeightRay α₀) (positiveWeightRay_add α₀) Q ExpQ hExpQ hbijQ haar
  let : μ.IsHaarMeasure := hμ
  refine ⟨μ, ell, c, hμ, hout, hin, hell, ?_⟩
  intro g E
  obtain ⟨⟨u, d⟩, rfl⟩ := F.surjective g
  let h := cartanLog H F.D.equiv F.ExpD hbijD d
  have hαeq : (fun q => α d q) = exponentialConjugate Q.equiv ExpQ hbijQ
      (M.coneAdjointAutomorphism T (positiveWeightRay α₀) (positiveWeightRay_add α₀) h) := by
    funext q
    exact M.factor_quotient_action_eq_exponential T F α₀ Q ExpQ hbijQ
      hbijN hbijD dynkinN π hπ α hα hφ d q
  have hset : act (F.inclusionN u * F.inclusionD d) '' E = π u • (α d '' E) := by
    rw [← Set.image_smul, Set.image_image]
    congr 1
    funext q
    exact hact u d q
  have hh : (height (F.inclusionN u * F.inclusionD d)).toAdd =
      eW (heightProjection T.character (h : GroupLieAlgebra (𝓘(ℝ, EG)) G)) := by
    rw [map_mul, F.inclusionN_height_eq_one T eW height hheight hbijN, one_mul]
    exact F.inclusionD_height T eW height hheight hbijD d
  rw [hset, measure_smul, hh]
  have himage : α d '' E = exponentialConjugate Q.equiv ExpQ hbijQ
      (M.coneAdjointAutomorphism T (positiveWeightRay α₀) (positiveWeightRay_add α₀) h) '' E :=
    congrArg (fun k : Q.carrier → Q.carrier => k '' E) hαeq
  rw [himage]
  exact hvol h E

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_ExponentialRepresentationInput
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instDecidableEqConeMixedWords _root_.OAI.PolycyclicRecognition.CartanWordModel.instFintypeConeMixedWords _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exponential compatibility in the published faithful realization

Onshuus–Post (2022), Proposition 2.4 and proof, give a faithful inducing
linear Lie realization of a simply connected real triangular group.
Lee, *Introduction to Smooth Manifolds*, second edition (2013), Theorem 8.44
(p.195) and Proposition 20.8(g) (p.520), give its Lie algebra map and
exponential compatibility. Only these properties are retained below.

https://doi.org/10.1112/blms.12574
https://doi.org/10.1007/978-1-4419-9982-5

The action and all bounds remain proved consequences, not part of the input.
-/

noncomputable section

namespace PolycyclicRecognition

open scoped Manifold Matrix.Norms.Operator

attribute [local instance 100] LieRing.ofAssociativeRing

variable {EG G : Type} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G]

variable [SimplyConnectedSpace G]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {ExpG : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H ExpG)

/-- The published representation identifies the actual factor action with
the explicit full Cartan adjoint automorphism. -/
theorem cartan_action_eq_adjoint_of_published_realization
    (hExpG : IsGroupExponential ExpG)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (hbijN : Function.Bijective F.ExpN) (hbijD : Function.Bijective F.ExpD)
    (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
    (d : F.D.carrier) :
    F.action d = M.adjointGroupAutomorphism T F.N.equiv F.ExpN F.isExpN hbijN dynkinN
      (cartanLog H F.D.equiv F.ExpD hbijD d) := by
  obtain ⟨m, hm, ρ, j, hind, hExp⟩ := realize ⟨a, ⟨T⟩⟩ ExpG hExpG
  let _ : NeZero m := ⟨Nat.ne_of_gt hm⟩
  have hρ : Function.Injective ρ := by
    intro g h he
    exact hind.injective (congrArg (fun u : (Matrix (Fin m) (Fin m) ℝ)ˣ =>
      (u : Matrix (Fin m) (Fin m) ℝ)) he)
  exact M.action_eq_adjoint_of_representation T F.N.equiv F.ExpN F.isExpN hbijN dynkinN
    F.D.equiv F.ExpD hbijD F.action j ρ hρ F.inclusionN F.closedN.injective F.inclusionD
    F.conjugation (fun x => by rw [F.compatibleN, hExp])
    (fun x => by rw [F.compatibleD, hExp]) d

open Module LieAlgebra LieModule

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanRayBoundaryModel
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Concrete ray quotients and their ambient actions

The model is chosen from the previously stated nilpotent existence,
integration, and Haar inputs. Its action, section, topology and contraction
are proved properties of that choice.
-/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule Set Filter TopologicalSpace Topology
open scoped Manifold Topology

variable {EG G : Type} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G]
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {ExpG : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H ExpG)
  (α₀ : H →ₗ[ℝ] ℝ)

namespace RayBoundaryModel

variable {M F α₀} (R : M.RayBoundaryModel F α₀)

set_option maxHeartbeats 1000000 in
theorem continuous_sectionMap : Continuous R.sectionMap :=
  F.closedN.continuous.comp R.cone.maps.sectionMap.continuous

set_option maxHeartbeats 1000000 in
theorem section_rightInverse (q : R.cone.Q.carrier) : R.action (R.sectionMap q) 1 = q := by
  have h := R.action_eq (R.cone.maps.sectionMap q) 1 1
  simpa only [sectionMap, map_one, mul_one, R.cone.maps.section_rightInverse] using h

set_option maxHeartbeats 1000000 in
theorem orbit_isQuotientMap : IsQuotientMap (fun g => R.action g 1) :=
  F.orbitMap_isQuotientMap R.cone.maps.quotient R.cone.maps.quotient_continuous
    R.cone.maps.sectionMap R.cone.maps.sectionMap.continuous
    R.cone.maps.section_rightInverse R.factorAction R.action R.action_eq

end RayBoundaryModel

open scoped Matrix.Norms.Operator
attribute [local instance 100] LieRing.ofAssociativeRing

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanRayBoundaryHaar
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Positive Haar characters on the concrete boundary rays -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule Set MeasureTheory
open scoped Manifold BigOperators

variable {EG G W : Type} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {ExpG : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H ExpG)
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)
  (αW : W →L[ℝ] ℝ)
  (R : M.RayBoundaryModel F (αW.toLinearMap.comp
    (eW.toLinearMap.comp ((heightProjection T.character).comp H.subtype))))

set_option maxHeartbeats 1000000 in
/-- A retained generator makes the Haar character strictly positive on
the selected ray. No volume or trace comparison is assumed. -/
theorem RayBoundaryModel.exists_positive_haar_height_multiplier
    (hExpG : IsGroupExponential ExpG)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (hbijN : Function.Bijective F.ExpN) (hbijD : Function.Bijective F.ExpD)
    (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
    (haarQ : NilpotentExponentialHaarInput R.cone.Q.modelSpace R.cone.Q.carrier)
    (height : G →* Multiplicative W)
    (hheight : ∀ x, (height (ExpG x)).toAdd = eW (heightProjection T.character x))
    (j : Fin M.letterCount)
    (hj : (M.weight j : H →ₗ[ℝ] ℝ) ∈ positiveWeightRay (αW.toLinearMap.comp
      (eW.toLinearMap.comp ((heightProjection T.character).comp H.subtype)))) :
    ∃ (μ : Measure R.cone.Q.carrier) (rate : ℝ), μ.IsHaarMeasure ∧ 0 < rate ∧
      ∀ g E, μ (R.action g '' E) =
        ENNReal.ofReal (Real.exp (rate * αW (height g).toAdd)) * μ E := by
  let α₀ := αW.toLinearMap.comp
    (eW.toLinearMap.comp ((heightProjection T.character).comp H.subtype))
  have hbijQ : Function.Bijective R.cone.maps.expQ := by
    rw [← show R.cone.maps.chartQ = R.cone.maps.expQ from funext R.cone.maps.chartQ_eq]
    exact R.cone.maps.chartQ.bijective
  obtain ⟨μ, ell, c, hμ, hout, hin, hell, hvol⟩ :=
    M.exists_boundary_haar_height_multiplier T F α₀ R.cone.Q R.cone.maps.expQ
      hbijQ hbijN hbijD dynkinN
      R.cone.maps.quotient R.cone.maps.quotient_exp R.factorAction R.equivariant
      (fun d => cartan_action_eq_adjoint_of_published_realization
        T M F hExpG realize hbijN hbijD dynkinN d)
      eW height hheight R.cone.maps.isExpQ haarQ R.action R.action_eq
  obtain ⟨rate, hrate, he⟩ := positive_sum_on_weightRay α₀
    (fun i => (M.weight i : H →ₗ[ℝ] ℝ)) c hout j hj (hin j hj)
  have hell' : ell = rate • αW.toLinearMap := by
    rw [hell]
    ext w
    have h := LinearMap.congr_fun he (cartanHeightSection T H (eW.symm w))
    have hp : eW (heightProjection T.character
        (H.subtype (cartanHeightSection T H (eW.symm w)))) = w := by
      change eW (heightProjection T.character
        ((cartanHeightSection T H (eW.symm w) : H) : GroupLieAlgebra (𝓘(ℝ, EG)) G)) = w
      rw [cartanHeightSection_height, eW.apply_symm_apply]
    simpa only [α₀, LinearMap.comp_apply, LinearMap.sum_apply, LinearMap.smul_apply,
      smul_eq_mul, cartanHeightWeight, LinearEquiv.coe_coe, hp] using h
  refine ⟨μ, rate, hμ, hrate, ?_⟩
  intro g E
  rw [hvol, hell']
  rfl

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanRayBoundaryMass
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_nonempty _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Common boundary windows for the actual Cartan quotient actions -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule Set MeasureTheory TopologicalSpace
open scoped Manifold ENNReal

variable {EG G P : Type} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [IsIsometricSMul G G] [ProperSpace G]
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  {M : CartanWordModel H}
  {ExpG : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} {F : CartanFactorModel H ExpG}
  {αS αT : H →ₗ[ℝ] ℝ} (RS : M.RayBoundaryModel F αS) (RT : M.RayBoundaryModel F αT)

set_option maxHeartbeats 1000000 in
/-- The common shadow bounds produce a compact source window with nonempty
interior and both of the uniform inequalities used in the leaf/trace proof. -/
theorem RayBoundaryModel.exists_mass_and_equal_set_trace
    (B : P → RS.cone.Q.carrier ≃ₜ RT.cone.Q.carrier) (f g : P → G → G)
    {Lf Lg ef eg E : ℝ} (hLf : 0 ≤ Lf) (hLg : 0 ≤ Lg)
    (hf : ∀ p x y, dist (f p x) (f p y) ≤ Lf * dist x y + ef)
    (hg : ∀ p x y, dist (g p x) (g p y) ≤ Lg * dist x y + eg)
    (hinv : ∀ p x, dist (g p (f p x)) x ≤ E)
    (KS : Set RS.cone.Q.carrier) (KT : Set RT.cone.Q.carrier)
    (hKS : IsCompact KS) (hKT : IsCompact KT)
    (hB : ∀ p x, ∃ z ∈ KT, B p (RS.action x 1) = RT.action (f p x) z)
    (hC : ∀ p x, ∃ z ∈ KS, (B p).symm (RT.action x 1) = RS.action (g p x) z)
    (μ : Measure RT.cone.Q.carrier) [μ.IsHaarMeasure] (height : G → ℝ)
    (hvolume : ∀ x V, μ (RT.action x '' V) =
      ENNReal.ofReal (Real.exp (height x)) * μ V) :
    ∃ (U : PositiveCompacts RS.cone.Q.carrier) (K D : ℝ), 0 < K ∧ 0 ≤ D ∧
      (∀ p x, ENNReal.ofReal (Real.exp (height (f p x))) ≤
          ENNReal.ofReal K * μ (B p '' (RS.action x '' (U : Set RS.cone.Q.carrier))) ∧
        μ (B p '' (RS.action x '' (U : Set RS.cone.Q.carrier))) ≤
          ENNReal.ofReal K * ENNReal.ofReal (Real.exp (height (f p x)))) ∧
      ∀ p x y, RS.action x '' (U : Set RS.cone.Q.carrier) = RS.action y '' (U : Set RS.cone.Q.carrier) →
        |height (f p x) - height (f p y)| ≤ D := by
  let : IsTopologicalGroup G := topologicalGroup_of_lieGroup (𝓘(ℝ, EG)) ⊤
  let : IsTopologicalGroup RT.cone.Q.carrier :=
    topologicalGroup_of_lieGroup (𝓘(ℝ, RT.cone.Q.modelSpace)) ⊤
  let : LocallyCompactSpace RT.cone.Q.carrier :=
    Manifold.locallyCompact_of_finiteDimensional (𝓘(ℝ, RT.cone.Q.modelSpace))
  let : LocallyCompactSpace RS.cone.Q.carrier :=
    Manifold.locallyCompact_of_finiteDimensional (𝓘(ℝ, RS.cone.Q.modelSpace))
  let U₀ : PositiveCompacts RS.cone.Q.carrier := Classical.choice inferInstance
  obtain ⟨U, K, D, hU, hU₀U, hK, hD, hmass, htrace⟩ :=
    boundary_family_mass_and_trace_of_compact_shadows RS.action RT.action
      RS.orbit_isQuotientMap.continuous RT.orbit_isQuotientMap.continuous
      (fun p => B p) (fun p => (B p).symm) f g hLf hLg hf hg hinv
      (fun p => (B p).apply_symm_apply)
      RS.sectionMap RS.continuous_sectionMap RS.section_rightInverse
      RT.sectionMap RT.continuous_sectionMap RT.section_rightInverse
      KS KT hKS hKT hB hC μ height hvolume U₀ U₀.isCompact
  let V : PositiveCompacts RS.cone.Q.carrier :=
    ⟨⟨U, hU⟩, U₀.interior_nonempty.mono (interior_mono hU₀U)⟩
  exact ⟨V, K, D, hK, hD, hmass, htrace⟩

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanRayBoundaryComparison
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Boundary volume data constructed on the actual ray quotients -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule Set MeasureTheory TopologicalSpace
open scoped Manifold ENNReal

variable {EG G W P : Type} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  {a : ℕ} {T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a}
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  {M : CartanWordModel H}
  {ExpG : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} {F : CartanFactorModel H ExpG}
  {eW : HeightSpace T.character ≃ₗ[ℝ] W} {αS αT : W →L[ℝ] ℝ}
  (RS : M.RayBoundaryModel F (αS.toLinearMap.comp
    (eW.toLinearMap.comp ((heightProjection T.character).comp H.subtype))))
  (RT : M.RayBoundaryModel F (αT.toLinearMap.comp
    (eW.toLinearMap.comp ((heightProjection T.character).comp H.subtype))))
  (height : G →* Multiplicative W) (f : P → G → G)

variable [IsIsometricSMul G G] [ProperSpace G] [SimplyConnectedSpace G]

set_option maxHeartbeats 1000000 in
/-- The two actual Haar characters and the compact-shadow sandwich produce
all volume data required in the leaf and averaging steps. -/
theorem nonempty_rayBoundaryComparison_of_shadows_m_oai
    (hExpG : IsGroupExponential ExpG)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (hbijN : Function.Bijective F.ExpN) (hbijD : Function.Bijective F.ExpD)
    (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
    (haarS : NilpotentExponentialHaarInput RS.cone.Q.modelSpace RS.cone.Q.carrier)
    (haarT : NilpotentExponentialHaarInput RT.cone.Q.modelSpace RT.cone.Q.carrier)
    (hheight : ∀ x, (height (ExpG x)).toAdd = eW (heightProjection T.character x))
    (jS jT : Fin M.letterCount)
    (hjS : (M.weight jS : H →ₗ[ℝ] ℝ) ∈ positiveWeightRay (αS.toLinearMap.comp
      (eW.toLinearMap.comp ((heightProjection T.character).comp H.subtype))))
    (hjT : (M.weight jT : H →ₗ[ℝ] ℝ) ∈ positiveWeightRay (αT.toLinearMap.comp
      (eW.toLinearMap.comp ((heightProjection T.character).comp H.subtype))))
    (B : P → RS.cone.Q.carrier ≃ₜ RT.cone.Q.carrier) (g : P → G → G)
    {Lf Lg ef eg E : ℝ} (hLf : 0 ≤ Lf) (hLg : 0 ≤ Lg)
    (hf : ∀ p x y, dist (f p x) (f p y) ≤ Lf * dist x y + ef)
    (hg : ∀ p x y, dist (g p x) (g p y) ≤ Lg * dist x y + eg)
    (hinv : ∀ p x, dist (g p (f p x)) x ≤ E)
    (KS : Set RS.cone.Q.carrier) (KT : Set RT.cone.Q.carrier)
    (hKS : IsCompact KS) (hKT : IsCompact KT)
    (hB : ∀ p x, ∃ z ∈ KT, B p (RS.action x 1) = RT.action (f p x) z)
    (hC : ∀ p x, ∃ z ∈ KS, (B p).symm (RT.action x 1) = RS.action (g p x) z) :
    Nonempty (RayBoundaryComparison RS RT height f) := by
  obtain ⟨μS, rS, hμS, hrS, hvolS⟩ := RS.exists_positive_haar_height_multiplier
    T M F eW αS hExpG realize hbijN hbijD dynkinN haarS height hheight jS hjS
  obtain ⟨μT, rT, hμT, hrT, hvolT⟩ := RT.exists_positive_haar_height_multiplier
    T M F eW αT hExpG realize hbijN hbijD dynkinN haarT height hheight jT hjT
  let : μT.IsHaarMeasure := hμT
  obtain ⟨U, K, D, hK, hD, hmass, htrace⟩ := RS.exists_mass_and_equal_set_trace RT
    B f g hLf hLg hf hg hinv KS KT hKS hKT hB hC μT
    (fun x => rT * αT (height x).toAdd) hvolT
  exact ⟨⟨B, U, μS, μT, hμS, hμT, rS, rT, hrS, hrT,
    hvolS, hvolT, K, hK, hmass, D, hD, htrace⟩⟩

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

theorem solution : type_of% @OAI.PolycyclicRecognition.CartanWordModel.nonempty_rayBoundaryComparison_of_shadows_m_oai := @OAI.PolycyclicRecognition.CartanWordModel.nonempty_rayBoundaryComparison_of_shadows_m_oai
