-- Prove2me | solution 1 for OAI.PolycyclicRecognition.ComplexWeightFactorModel.rotationRepresentation_faithful
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-03T01:12:56.879566+00:00
-- url     : https://prove2.me/submissions/bbe00e43-0b26-46c2-be6d-298d351aa436

import Mathlib
import Definitions.Def_PolycyclicRecognition
import Definitions.Def_OAIQ093D023

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_BasisQuotientLifts
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A basis adapted to specified quotient lifts -/

noncomputable section
namespace PolycyclicRecognition

open Module Set

variable {𝕜 : Type*} [Field 𝕜]

variable {V I J : Type*} [AddCommGroup V] [Module 𝕜 V] (U : Submodule 𝕜 V)
  (bU : Basis I 𝕜 U) (bQ : Basis J 𝕜 (V ⧸ U))
  (lift : J → V) (hlift : ∀ j, U.mkQ (lift j) = bQ j)

theorem basisWithQuotientLifts_repr_inl (v : U) (i : I) :
    (basisWithQuotientLifts U bU bQ lift hlift).repr (v : V) (Sum.inl i) = bU.repr v i := by
  classical
  let b := basisWithQuotientLifts U bU bQ lift hlift
  have hf : (b.coord (Sum.inl i)).comp U.subtype = bU.coord i := by
    apply bU.ext
    intro j
    change b.repr (bU j : V) (Sum.inl i) = bU.repr (bU j) i
    rw [← basisWithQuotientLifts_inl U bU bQ lift hlift j]
    simp only [b, Basis.repr_self, Finsupp.single_apply, Sum.inl.injEq]
  exact congrArg (fun f : U →ₗ[𝕜] 𝕜 => f v) hf

theorem basisWithQuotientLifts_repr_inr (v : V) (j : J) :
    (basisWithQuotientLifts U bU bQ lift hlift).repr v (Sum.inr j) =
      bQ.repr (U.mkQ v) j := by
  classical
  let b := basisWithQuotientLifts U bU bQ lift hlift
  have hf : b.coord (Sum.inr j) = (bQ.coord j).comp U.mkQ := by
    apply b.ext
    intro k
    cases k with
    | inl i =>
      change b.repr (b (Sum.inl i)) (Sum.inr j) = bQ.repr (U.mkQ (b (Sum.inl i))) j
      rw [Basis.repr_self]
      have hz : U.mkQ (b (Sum.inl i)) = 0 := by
        rw [basisWithQuotientLifts_inl]
        exact (Submodule.Quotient.mk_eq_zero U).mpr (bU i).property
      rw [hz, map_zero]
      simp
    | inr i =>
      change b.repr (b (Sum.inr i)) (Sum.inr j) = bQ.repr (U.mkQ (b (Sum.inr i))) j
      rw [Basis.repr_self, basisWithQuotientLifts_inr, hlift, Basis.repr_self]
      simp only [Finsupp.single_apply, Sum.inr.injEq]
  exact congrArg (fun f : V →ₗ[𝕜] 𝕜 => f v) hf

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_RepresentationKernelCoordinates
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Faithfulness checked in a surjective coordinate system -/

namespace PolycyclicRecognition

theorem injective_of_kernel_in_coordinates {G A X : Type*} [Group G] [Group A]
    (ρ : G →* A) (f : X → G) (hf : Function.Surjective f)
    (hker : ∀ x, ρ (f x) = 1 → f x = 1) : Function.Injective ρ := by
  apply (MonoidHom.ker_eq_bot_iff ρ).mp
  apply le_antisymm _ bot_le
  intro g hg
  obtain ⟨x,rfl⟩ := hf g
  exact hker x hg

end PolycyclicRecognition

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_AnalyticNilpotentLogarithm
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite logarithms of analytic unipotent exponentials -/

noncomputable section
namespace PolycyclicRecognition

variable {A : Type*} [NormedRing A] [NormedAlgebra ℚ A]

theorem finiteNilpotentLog_analytic_exp (a : A) (n : ℕ) (ha : a ^ (n + 1) = 0) :
    finiteNilpotentLog (n + 1) (NormedSpace.exp a - 1) = a := by
  rw [analytic_exp_eq_nilpotent_exp ⟨n + 1, ha⟩]
  exact finiteNilpotentLog_exp a n ha

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_ExponentialDuhamel
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The difference formula for matrix exponentials

The scalar-time exponential derivative and the fundamental theorem of
calculus give the noncommutative difference formula. This is the concrete
step toward identifying the differential in the retained Dixmier input.
-/

noncomputable section
namespace PolycyclicRecognition

open MeasureTheory Set

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

attribute [local instance] OAI.PolycyclicRecognition.instNormedAlgebraRat_solutions
theorem hasDerivAt_exponential_bridge (a b : A) (t : ℝ) :
    HasDerivAt (fun s : ℝ => NormedSpace.exp ((1 - s) • a) * NormedSpace.exp (s • b))
      (NormedSpace.exp ((1 - t) • a) * (b - a) * NormedSpace.exp (t • b)) t := by
  let : NormedAlgebra ℚ A := NormedAlgebra.restrictScalars ℚ ℝ A
  have ha := (hasDerivAt_exp_smul_const a (1 - t)).scomp t
    ((hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_id t))
  have hb := hasDerivAt_exp_smul_const b t
  have h := ha.mul hb
  have hc : Commute b (NormedSpace.exp (t • b)) :=
    ((Commute.refl b).smul_right t).exp_right
  have he : (-1 : ℝ) • (NormedSpace.exp ((1 - t) • a) * a) * NormedSpace.exp (t • b) +
      NormedSpace.exp ((1 - t) • a) * (NormedSpace.exp (t • b) * b) =
      NormedSpace.exp ((1 - t) • a) * (b - a) * NormedSpace.exp (t • b) := by
    rw [neg_one_smul, ← hc.eq]
    noncomm_ring
  change HasDerivAt (fun s : ℝ => NormedSpace.exp ((1 - s) • a) *
    NormedSpace.exp (s • b)) _ t at h
  simpa only [Function.comp_def, zero_sub, he] using h

theorem exponential_sub_eq_integral (a b : A) :
    NormedSpace.exp b - NormedSpace.exp a =
      ∫ t in (0 : ℝ)..1,
        NormedSpace.exp ((1 - t) • a) * (b - a) * NormedSpace.exp (t • b) := by
  have hc : Continuous (fun t : ℝ =>
      NormedSpace.exp ((1 - t) • a) * (b - a) * NormedSpace.exp (t • b)) :=
    ((NormedSpace.exp_continuous.comp ((continuous_const.sub continuous_id).smul
      continuous_const)).mul continuous_const).mul
        (NormedSpace.exp_continuous.comp (continuous_id.smul continuous_const))
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := (0 : ℝ)) (b := 1) (fun t _ => hasDerivAt_exponential_bridge a b t)
    (hc.intervalIntegrable (μ := volume) 0 1)
  simpa only [sub_self, zero_smul, NormedSpace.exp_zero, one_mul, sub_zero,
    one_smul, mul_one] using h.symm

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_ExponentialDuhamelDerivative
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The differential of the noncommutative exponential

The difference formula and continuity of integrals on a compact interval
identify the derivative along each line. Analyticity then identifies the
actual Frechet differential; no inverse-exponential theorem is assumed.
-/

noncomputable section
namespace PolycyclicRecognition

open MeasureTheory Set Filter
open scoped Topology

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

attribute [local instance] OAI.PolycyclicRecognition.instNormedAlgebraRat_solutions_1
theorem hasDerivAt_exp_add_smul_zero (a b : A) :
    HasDerivAt (fun s : ℝ => NormedSpace.exp (a + s • b))
      (∫ t in (0 : ℝ)..1, NormedSpace.exp ((1 - t) • a) * b *
        NormedSpace.exp (t • a)) 0 := by
  let F : ℝ → ℝ → A := fun s t =>
    NormedSpace.exp ((1 - t) • a) * b * NormedSpace.exp (t • (a + s • b))
  have hF : Continuous F.uncurry := by
    exact ((NormedSpace.exp_continuous.comp
      ((continuous_const.sub continuous_snd).smul continuous_const)).mul
      continuous_const).mul (NormedSpace.exp_continuous.comp
        (continuous_snd.smul (continuous_const.add (continuous_fst.smul continuous_const))))
  have hc : Continuous (fun s => ∫ t in (0 : ℝ)..1, F s t) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hF 0 1
  have he (s : ℝ) : NormedSpace.exp (a + s • b) - NormedSpace.exp a =
      s • ∫ t in (0 : ℝ)..1, F s t := by
    have h := exponential_sub_eq_integral a (a + s • b)
    simpa only [add_sub_cancel_left, mul_smul_comm, smul_mul_assoc,
      intervalIntegral.integral_smul, F] using h
  apply hasDerivAt_iff_tendsto_slope.mpr
  have hlim : Tendsto (fun s => ∫ t in (0 : ℝ)..1, F s t) (𝓝[≠] 0)
      (𝓝 (∫ t in (0 : ℝ)..1, F 0 t)) :=
    hc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have heq : slope (fun s : ℝ => NormedSpace.exp (a + s • b)) 0 =ᶠ[𝓝[≠] 0]
      (fun s => ∫ t in (0 : ℝ)..1, F s t) := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hs' : s ≠ 0 := hs
    simp only [slope, sub_zero, zero_smul, add_zero, vsub_eq_sub, he,
      smul_smul, inv_mul_cancel₀ hs', one_smul]
  have hlim' := hlim.congr' heq.symm
  simpa only [F, zero_smul, add_zero] using hlim'

theorem fderiv_exp_eq_integral (a b : A) :
    fderiv ℝ NormedSpace.exp a b =
      ∫ t in (0 : ℝ)..1, NormedSpace.exp ((1 - t) • a) * b *
        NormedSpace.exp (t • a) := by
  have hd := (NormedSpace.exp_analytic (𝕂 := ℝ) a).differentiableAt.hasFDerivAt
  have hb : HasDerivAt (fun s : ℝ => a + s • b) b 0 := by
    simpa only [id_eq, one_smul] using (hasDerivAt_id (0 : ℝ)).smul_const b |>.const_add a
  have hd' : HasFDerivAt NormedSpace.exp (fderiv ℝ NormedSpace.exp a) (a + (0 : ℝ) • b) := by
    simpa only [zero_smul, add_zero] using hd
  have h := hd'.comp_hasDerivAt 0 hb
  simpa only [zero_smul, add_zero, Function.comp_def] using
    h.unique (hasDerivAt_exp_add_smul_zero a b)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_ExponentialLocalSeparation
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Separation of arbitrary exponential preimages near a regular logarithm

If the exponential has trivial kernel, a local injectivity neighborhood
cannot have an additional logarithm outside that neighborhood. Conjugating
the small logarithm by the one-parameter subgroup of the other logarithm
first forces the two logarithms to commute.
-/

noncomputable section
namespace PolycyclicRecognition

open Set Filter Topology

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

theorem exp_eq_of_local_injectivity
    (hker : ∀ a : A, NormedSpace.exp a = 1 → a = 0)
    (U : Set A) (hU : IsOpen U) (hi : Set.InjOn NormedSpace.exp U)
    {a b : A} (hb : b ∈ U) (he : NormedSpace.exp a = NormedSpace.exp b) : a = b := by
  let : NormedAlgebra ℚ A := NormedAlgebra.restrictScalars ℚ ℝ A
  let C : ℝ → A := fun t => NormedSpace.exp (t • a) * b * NormedSpace.exp (-(t • a))
  have hC0 : C 0 = b := by simp [C]
  have hcont : Continuous C := by
    apply Continuous.mul
    · exact ((NormedSpace.exp_continuous.comp (continuous_id.smul continuous_const)).mul
        continuous_const)
    · exact NormedSpace.exp_continuous.comp (continuous_id.smul continuous_const).neg
  have hCexp (t : ℝ) : NormedSpace.exp (C t) = NormedSpace.exp b := by
    have hc : Commute (NormedSpace.exp (t • a)) (NormedSpace.exp a) :=
      ((Commute.refl a).smul_left t).exp
    have hz : NormedSpace.exp (t • a) * NormedSpace.exp (-(t • a)) = 1 := by
      rw [← NormedSpace.exp_add_of_commute (Commute.refl (t • a)).neg_right,
        add_neg_cancel, NormedSpace.exp_zero]
    change NormedSpace.exp
      ((algebraExpUnit (t • a) : A) * b * ((algebraExpUnit (t • a))⁻¹ : Aˣ)) = _
    rw [NormedSpace.exp_units_conj, ← he]
    change NormedSpace.exp (t • a) * NormedSpace.exp a * NormedSpace.exp (-(t • a)) = _
    rw [hc.eq, mul_assoc, hz, mul_one]
  have hCU : ∀ᶠ t in 𝓝 (0 : ℝ), C t ∈ U := by
    apply hcont.continuousAt.preimage_mem_nhds
    rw [hC0]
    exact hU.mem_nhds hb
  have hCe : C =ᶠ[𝓝 (0 : ℝ)] fun _ => b :=
    hCU.mono fun t ht => hi ht hb (hCexp t)
  have hd : HasDerivAt C (a * b - b * a) 0 := by
    have hp : HasDerivAt (fun t : ℝ => NormedSpace.exp (t • a)) a 0 := by
      simpa only [zero_smul, NormedSpace.exp_zero, one_mul] using
        (hasDerivAt_exp_smul_const a (0 : ℝ))
    have hn : HasDerivAt (fun t : ℝ => NormedSpace.exp (-(t • a))) (-a) 0 := by
      simpa only [smul_neg, zero_smul, neg_zero, NormedSpace.exp_zero, one_mul] using
        (hasDerivAt_exp_smul_const (-a) (0 : ℝ))
    have hd0 := (hp.mul_const b).mul hn
    have hfun : ((fun t : ℝ => NormedSpace.exp (t • a) * b) *
        fun t : ℝ => NormedSpace.exp (-(t • a))) = C := rfl
    rw [hfun] at hd0
    simpa only [zero_smul, neg_zero, NormedSpace.exp_zero, one_mul, mul_one,
      mul_neg, sub_eq_add_neg] using hd0
  have hz : a * b - b * a = 0 :=
    (hd.congr_of_eventuallyEq hCe.symm).unique (hasDerivAt_const (0 : ℝ) b)
  have hc : Commute a b := sub_eq_zero.mp hz
  have hezero : NormedSpace.exp (a - b) = 1 := by
    rw [sub_eq_add_neg, NormedSpace.exp_add_of_commute hc.neg_right, he,
      ← NormedSpace.exp_add_of_commute (Commute.refl b).neg_right,
      add_neg_cancel, NormedSpace.exp_zero]
  exact sub_eq_zero.mp (hker (a - b) hezero)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_InvariantTriangularBasis
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Restricting an actual triangular action

An invariant subspace of a simultaneous real triangular action again
has a simultaneous triangular basis. The proof chooses the last
nonzero coordinate functional and inducts on its invariant kernel.
No spectral splitting or solvability hypothesis is needed.
-/

noncomputable section

namespace PolycyclicRecognition

open Module Matrix

/-- The last active coordinate of a triangular representation is a
common eigenfunctional on every nonzero invariant subspace. -/
theorem exists_triangular_eigenfunctional
    {ι W : Type*} [AddCommGroup W] [Module ℝ W] [Nontrivial W]
    {n : ℕ} (e : W →ₗ[ℝ] (Fin n → ℝ)) (he : Function.Injective e)
    (T : ι → W →ₗ[ℝ] W) (A : ι → Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ x, (A x).IsUpperTriangular)
    (hinter : ∀ x v, e (T x v) = A x *ᵥ e v) :
    ∃ (p : W →ₗ[ℝ] ℝ), p ≠ 0 ∧
      ∀ x, ∃ c : ℝ, ∀ v, p (T x v) = c * p v := by
  classical
  let s : Finset (Fin n) := Finset.univ.filter fun i => ∃ v : W, e v i ≠ 0
  have hs : s.Nonempty := by
    obtain ⟨v, hv⟩ := exists_ne (0 : W)
    have hev : e v ≠ 0 := fun h => hv (he (h.trans (map_zero e).symm))
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hev
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, v, hi⟩⟩
  let i := s.max' hs
  have hi : i ∈ s := Finset.max'_mem s hs
  have hzero : ∀ j : Fin n, i < j → ∀ v : W, e v j = 0 := by
    intro j hij v
    by_contra hj
    have hjs : j ∈ s := Finset.mem_filter.mpr ⟨Finset.mem_univ j, v, hj⟩
    exact (not_le_of_gt hij) (Finset.le_max' s j hjs)
  let p : W →ₗ[ℝ] ℝ := (LinearMap.proj i).comp e
  refine ⟨p, ?_, ?_⟩
  · obtain ⟨v, hv⟩ := (Finset.mem_filter.mp hi).2
    intro hp
    exact hv (congrArg (fun f : W →ₗ[ℝ] ℝ => f v) hp)
  · intro x
    refine ⟨A x i i, fun v => ?_⟩
    change e (T x v) i = A x i i * e v i
    rw [hinter, Matrix.mulVec, dotProduct]
    apply Finset.sum_eq_single i
    · intro j _ hji
      rcases lt_or_gt_of_ne hji with h | h
      · exact mul_eq_zero_of_left (hA x (i := i) (j := j) h) _
      · rw [hzero j h v, mul_zero]
    · simp

/-- Every action embedded into actual upper triangular matrices admits
an upper triangular basis on its own finite-dimensional space. -/
theorem exists_upperTriangular_basis_of_embedding
    {ι W : Type*} [AddCommGroup W] [Module ℝ W] [FiniteDimensional ℝ W]
    {n : ℕ} (e : W →ₗ[ℝ] (Fin n → ℝ)) (he : Function.Injective e)
    (T : ι → W →ₗ[ℝ] W) (A : ι → Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ x, (A x).IsUpperTriangular)
    (hinter : ∀ x v, e (T x v) = A x *ᵥ e v) :
    ∃ (m : ℕ) (b : Basis (Fin m) ℝ W),
      ∀ x, (LinearMap.toMatrix b b (T x)).IsUpperTriangular := by
  classical
  by_cases hzero : finrank ℝ W = 0
  · refine ⟨finrank ℝ W, Module.finBasis ℝ W, ?_⟩
    intro x i j hij
    have := i.isLt
    omega
  let : Nontrivial W := finrank_pos_iff.mp (Nat.pos_of_ne_zero hzero)
  obtain ⟨p, hp, hscalar⟩ := exists_triangular_eigenfunctional e he T A hA hinter
  let N := p.ker
  have hN : ∀ x, ∀ v ∈ N, T x v ∈ N := by
    intro x v hv
    obtain ⟨c, hc⟩ := hscalar x
    change p (T x v) = 0
    rw [hc]
    exact mul_eq_zero_of_right c hv
  let TN (x : ι) : N →ₗ[ℝ] N := (T x).restrict (hN x)
  let eN : N →ₗ[ℝ] (Fin n → ℝ) := e.comp N.subtype
  have heN : Function.Injective eN := he.comp Subtype.val_injective
  have hinterN : ∀ x v, eN (TN x v) = A x *ᵥ eN v := by
    intro x v
    exact hinter x v
  have hNlt : finrank ℝ N < finrank ℝ W := by
    apply Submodule.finrank_lt
    exact fun h => hp (LinearMap.ker_eq_top.mp h)
  obtain ⟨m, bN, hbN⟩ :=
    exists_upperTriangular_basis_of_embedding eN heN TN A hA hinterN
  have hrange : p.range = ⊤ := by
    apply LinearMap.range_eq_top.mpr
    obtain ⟨v, hv⟩ : ∃ v, p v ≠ 0 := by
      by_contra! h
      exact hp (LinearMap.ext h)
    intro y
    refine ⟨(y / p v) • v, ?_⟩
    simp only [map_smul, smul_eq_mul]
    exact div_mul_cancel₀ y hv
  have hdimQ : finrank ℝ (W ⧸ N) = 1 := by
    have heq := LinearEquiv.finrank_eq (LinearMap.quotKerEquivRange p)
    change finrank ℝ (W ⧸ p.ker) = 1
    rw [heq, hrange, finrank_top, finrank_self]
  let bQ : Basis (Fin 1) ℝ (W ⧸ N) :=
    (Module.finBasis ℝ (W ⧸ N)).reindex (finCongr hdimQ)
  choose lift hlift using fun i : Fin 1 => N.mkQ_surjective (bQ i)
  let b := basisWithQuotientLifts N bN bQ lift hlift
  let er : Fin m ⊕ Fin 1 ≃ Fin (m + 1) := finSumFinEquiv
  refine ⟨m + 1, b.reindex er, ?_⟩
  intro x i j hij
  obtain ⟨i, rfl⟩ := er.surjective i
  obtain ⟨j, rfl⟩ := er.surjective j
  simp only [LinearMap.toMatrix_apply, Basis.repr_reindex_apply, Basis.reindex_apply,
    Equiv.symm_apply_apply]
  dsimp only [b]
  cases i with
  | inl i =>
    cases j with
    | inl j =>
      rw [basisWithQuotientLifts_inl]
      change (basisWithQuotientLifts N bN bQ lift hlift).repr
        ((TN x (bN j) : N) : W) (Sum.inl i) = 0
      rw [basisWithQuotientLifts_repr_inl]
      simpa only [LinearMap.toMatrix_apply] using
        hbN x (i := i) (j := j) (by
          change (j : ℕ) < (i : ℕ) at hij ⊢
          exact hij)
    | inr j =>
      have hj : (j : ℕ) = 0 := by omega
      change m + (j : ℕ) < (i : ℕ) at hij
      have := i.isLt
      omega
  | inr i =>
    cases j with
    | inl j =>
      rw [basisWithQuotientLifts_inl, basisWithQuotientLifts_repr_inr]
      have hz : N.mkQ (T x (bN j)) = 0 :=
        (Submodule.Quotient.mk_eq_zero N).mpr (hN x (bN j) (bN j).property)
      rw [hz, map_zero, Finsupp.zero_apply]
    | inr j =>
      have heq : i = j := Subsingleton.elim i j
      exact (hij.ne (congrArg (fun a => er (Sum.inr a)) heq).symm).elim
termination_by finrank ℝ W

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_TriangularExponentialAverage
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Invertibility of the averaged real triangular exponential

This is the linear operator appearing in the differential of exponential
coordinates. Its diagonal entries are integrals of positive real
exponentials, so they cannot vanish. No global exponential theorem is used.
-/

noncomputable section
namespace PolycyclicRecognition

open scoped Matrix.Norms.Operator
open MeasureTheory Set

variable {n : ℕ}

theorem triangularExpAverage_entry (A : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    triangularExpAverage A i j = ∫ t in (0 : ℝ)..1, NormedSpace.exp (t • A) i j := by
  let ev : Matrix (Fin n) (Fin n) ℝ →ₗ[ℝ] ℝ :=
    { toFun := fun B => B i j
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  have hc : Continuous (fun t : ℝ => NormedSpace.exp (t • A)) :=
    NormedSpace.exp_continuous.comp (continuous_id.smul continuous_const)
  exact (ev.toContinuousLinearMap.intervalIntegral_comp_comm (hc.intervalIntegrable (μ := volume) 0 1)).symm

theorem triangularExpAverage_upper (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.IsUpperTriangular) : (triangularExpAverage A).IsUpperTriangular := by
  intro i j hji
  rw [triangularExpAverage_entry]
  have hzero (t : ℝ) : NormedSpace.exp (t • A) i j = 0 := by
    apply matrix_exp_upperTriangular (t • A) _ hji
    intro k l hlk
    simp only [Matrix.smul_apply, smul_eq_mul, hA hlk, mul_zero]
  simp only [hzero, intervalIntegral.integral_zero]

theorem triangularExpAverage_diagonal (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.IsUpperTriangular) (i : Fin n) :
    triangularExpAverage A i i = ∫ t in (0 : ℝ)..1, Real.exp (t * A i i) := by
  rw [triangularExpAverage_entry]
  apply intervalIntegral.integral_congr
  intro t _
  have ht : (t • A).IsUpperTriangular := by
    intro k l hlk
    simp only [Matrix.smul_apply, smul_eq_mul, hA hlk, mul_zero]
  change NormedSpace.exp (t • A) i i = Real.exp (t * A i i)
  rw [matrix_exp_diagonal (t • A) ht]
  rfl

theorem triangularExpAverage_diagonal_pos (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.IsUpperTriangular) (i : Fin n) : 0 < triangularExpAverage A i i := by
  rw [triangularExpAverage_diagonal A hA]
  apply intervalIntegral.integral_pos zero_lt_one
    (Real.continuous_exp.comp (continuous_id.mul_const (A i i))).continuousOn
  · intro t _
    exact (Real.exp_pos _).le
  · exact ⟨0, ⟨le_rfl, zero_le_one⟩, Real.exp_pos _⟩

theorem triangularExpAverage_isUnit (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.IsUpperTriangular) : IsUnit (triangularExpAverage A) := by
  rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero,
    Matrix.det_of_isUpperTriangular (triangularExpAverage_upper A hA)]
  exact Finset.prod_ne_zero_iff.mpr fun i _ =>
    ne_of_gt (triangularExpAverage_diagonal_pos A hA i)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_TriangularOperatorAverage
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Invertibility of an averaged operator with real triangular matrix

This is the linear-algebra part of regularity of real triangular exponential
coordinates. It applies to the adjoint operator in its given triangular basis.
-/

noncomputable section
namespace PolycyclicRecognition

open MeasureTheory
open scoped Matrix.Norms.Operator

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {n : ℕ}

theorem toMatrix_operatorExpAverage (b : Module.Basis (Fin n) ℝ E)
    (D : E →L[ℝ] E) :
    LinearMap.toMatrix b b (operatorExpAverage D).toLinearMap =
      triangularExpAverage (LinearMap.toMatrix b b D.toLinearMap) := by
  let f : (E →L[ℝ] E) →+* Matrix (Fin n) (Fin n) ℝ :=
    (LinearMap.toMatrixAlgEquiv b).toRingHom.comp ContinuousLinearMap.toLinearMapRingHom
  let fL : (E →L[ℝ] E) →ₗ[ℝ] Matrix (Fin n) (Fin n) ℝ :=
    (LinearMap.toMatrix b b).toLinearMap.comp (ContinuousLinearMap.coeLM ℝ)
  let : NormedAlgebra ℚ (E →L[ℝ] E) := NormedAlgebra.restrictScalars ℚ ℝ _
  let : NormedAlgebra ℚ (Matrix (Fin n) (Fin n) ℝ) := NormedAlgebra.restrictScalars ℚ ℝ _
  have he (t : ℝ) : fL (NormedSpace.exp (t • D)) =
      NormedSpace.exp (t • fL D) := by
    have h := NormedSpace.map_exp f fL.continuous_of_finiteDimensional (t • D)
    exact h.trans (congrArg NormedSpace.exp (fL.map_smul t D))
  have hc : Continuous (fun t : ℝ => NormedSpace.exp (t • D)) :=
    NormedSpace.exp_continuous.comp (continuous_id.smul continuous_const)
  change fL.toContinuousLinearMap (∫ t in (0 : ℝ)..1, NormedSpace.exp (t • D)) = _
  exact (fL.toContinuousLinearMap.intervalIntegral_comp_comm
    (hc.intervalIntegrable (μ := volume) 0 1)).symm.trans
      (intervalIntegral.integral_congr (fun t _ => he t))

theorem operatorExpAverage_injective (b : Module.Basis (Fin n) ℝ E)
    (D : E →L[ℝ] E) (hD : (LinearMap.toMatrix b b D.toLinearMap).IsUpperTriangular) :
    Function.Injective (operatorExpAverage D) := by
  have hunit := triangularExpAverage_isUnit (LinearMap.toMatrix b b D.toLinearMap) hD
  rw [← toMatrix_operatorExpAverage b D] at hunit
  change IsUnit ((LinearMap.toMatrixAlgEquiv b) (operatorExpAverage D).toLinearMap) at hunit
  have hu : IsUnit (operatorExpAverage D).toLinearMap := by
    simpa only [AlgEquiv.symm_apply_apply] using
      hunit.map (LinearMap.toMatrixAlgEquiv b).symm
  exact LinearMap.ker_eq_bot.mp ((LinearMap.isUnit_iff_ker_eq_bot _).mp hu)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_RepresentedExponentialDifferential
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The exponential differential in a faithful Lie representation

Left translation identifies this differential with the average of the
negative adjoint flow. A real triangular adjoint basis makes that average
invertible, independently of a global exponential chart.
-/

noncomputable section
namespace PolycyclicRecognition

open MeasureTheory
attribute [local instance 100] LieRing.ofAssociativeRing

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

attribute [local instance] OAI.PolycyclicRecognition.instNormedAddCommGroup_solutions
attribute [local instance] OAI.PolycyclicRecognition.instNormedSpaceReal_solutions
attribute [local instance] OAI.PolycyclicRecognition.instNormedAlgebraRat_solutions_2
theorem represented_exponential_differential
    (j : L →ₗ⁅ℝ⁆ A) (x v : L) :
    fderiv ℝ NormedSpace.exp (j x) (j v) =
      NormedSpace.exp (j x) * j
        (operatorExpAverage (-(continuousAd x)) v) := by
  let D : L →L[ℝ] L := continuousAd x
  let J : L →L[ℝ] A := j.toLinearMap.toContinuousLinearMap
  let F : (L →L[ℝ] L) →L[ℝ] A :=
    ((ContinuousLinearMap.mul ℝ A (NormedSpace.exp (j x))).comp J).comp
      (ContinuousLinearMap.apply ℝ L v)
  let : NormedAlgebra ℚ A := NormedAlgebra.restrictScalars ℚ ℝ A
  have he (t : ℝ) : j (NormedSpace.exp (t • (-D)) v) =
      NormedSpace.exp (-(t • j x)) * j v * NormedSpace.exp (t • j x) := by
    have h := exp_intertwine_apply J (t • (-D)) ((-t) • adjointOperator (j x))
      (fun w => by
        change j (t • -⁅x, w⁆) = (-t) • (j x * j w - j w * j x)
        rw [map_smul, map_neg, j.map_lie]
        simp only [neg_smul, smul_neg]
        rfl) v
    rw [exp_smul_adjointOperator_apply] at h
    change j (NormedSpace.exp (t • (-D)) v) =
      NormedSpace.exp ((-t) • j x) * j v * NormedSpace.exp (-((-t) • j x)) at h
    simpa only [neg_smul, neg_neg] using h
  have hprod (t : ℝ) :
      NormedSpace.exp (j x) * NormedSpace.exp (-(t • j x)) =
        NormedSpace.exp ((1 - t) • j x) := by
    rw [← NormedSpace.exp_add_of_commute ((Commute.refl (j x)).smul_right t).neg_right]
    congr 1
    rw [sub_smul, one_smul, sub_eq_add_neg]
  have hc : Continuous (fun t : ℝ => NormedSpace.exp (t • (-D))) :=
    NormedSpace.exp_continuous.comp (continuous_id.smul continuous_const)
  rw [fderiv_exp_eq_integral]
  change _ = F (∫ t in (0 : ℝ)..1, NormedSpace.exp (t • (-D)))
  rw [← F.intervalIntegral_comp_comm (hc.intervalIntegrable (μ := volume) 0 1)]
  apply intervalIntegral.integral_congr
  intro t _
  change _ = NormedSpace.exp (j x) * j (NormedSpace.exp (t • (-D)) v)
  rw [he, ← mul_assoc, ← mul_assoc, hprod]

theorem represented_exponential_differential_injective
    {n : ℕ} (T : TriangularAdjoint L n) (j : L →ₗ⁅ℝ⁆ A)
    (hj : Function.Injective j) (x : L) :
    Function.Injective ((fderiv ℝ NormedSpace.exp (j x)).comp
      j.toLinearMap.toContinuousLinearMap) := by
  let D : L →L[ℝ] L := continuousAd x
  have hu : (LinearMap.toMatrix T.basis T.basis (-D).toLinearMap).IsUpperTriangular := by
    change (LinearMap.toMatrix T.basis T.basis (-LieAlgebra.ad ℝ L x)).IsUpperTriangular
    rw [map_neg]
    intro i k hki
    simp only [Matrix.neg_apply, T.upper x hki, neg_zero]
  have hQ := operatorExpAverage_injective T.basis (-D) hu
  intro v w h
  change fderiv ℝ NormedSpace.exp (j x) (j v) =
    fderiv ℝ NormedSpace.exp (j x) (j w) at h
  rw [represented_exponential_differential, represented_exponential_differential] at h
  exact hQ (hj ((NormedSpace.isUnit_exp (j x)).mul_left_cancel h))

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_TriangularAdjointEmbedding
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# A triangular adjoint basis from a faithful triangular representation

Order matrix units by increasing row and decreasing column. Commuting
with an upper triangular matrix then gives an upper triangular operator.
Restricting this action to a faithfully embedded Lie algebra supplies
its actual adjoint basis.
-/

noncomputable section

namespace PolycyclicRecognition

open Module Matrix

attribute [local instance 100] LieRing.ofAssociativeRing

private theorem matrix_commutator_single_zero {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsUpperTriangular)
    (p q r s : Fin n)
    (hij : triangularMatrixOrder n (r, s) < triangularMatrixOrder n (p, q)) :
    ((A * Matrix.single r s (1 : ℝ) - Matrix.single r s (1 : ℝ) * A) :
      Matrix (Fin n) (Fin n) ℝ) p q = 0 := by
  rw [Matrix.sub_apply]
  have hleft : (A * Matrix.single r s (1 : ℝ)) p q = 0 := by
    by_cases hqs : q = s
    · subst q
      rw [Matrix.mul_single_apply_same, mul_one]
      apply hA
      have hm : n * (r : ℕ) < n * (p : ℕ) := by
        change (s.rev : ℕ) + n * (r : ℕ) < (s.rev : ℕ) + n * (p : ℕ) at hij
        omega
      change (r : ℕ) < (p : ℕ)
      exact Nat.lt_of_mul_lt_mul_left hm
    · exact Matrix.mul_single_apply_of_ne 1 r s p q hqs A
  have hright : (Matrix.single r s (1 : ℝ) * A) p q = 0 := by
    by_cases hpr : p = r
    · subst p
      rw [Matrix.single_mul_apply_same, one_mul]
      apply hA
      have hrev : s.rev < q.rev := by
        change (s.rev : ℕ) + n * (r : ℕ) < (q.rev : ℕ) + n * (r : ℕ) at hij
        change (s.rev : ℕ) < (q.rev : ℕ)
        omega
      exact Fin.rev_lt_rev.mp hrev
    · exact Matrix.single_mul_apply_of_ne 1 r s p q hpr A
  rw [hleft, hright, sub_self]

/-- Commutation by an upper triangular matrix is upper triangular on
the full matrix algebra in the ordered matrix-unit basis. -/
theorem upperTriangular_matrix_ad {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.IsUpperTriangular) :
    (LinearMap.toMatrix (triangularMatrixBasis n) (triangularMatrixBasis n)
      (LieAlgebra.ad ℝ (Matrix (Fin n) (Fin n) ℝ) A)).IsUpperTriangular := by
  intro i j hij
  obtain ⟨⟨p, q⟩, rfl⟩ := (triangularMatrixOrder n).surjective i
  obtain ⟨⟨r, s⟩, rfl⟩ := (triangularMatrixOrder n).surjective j
  rw [LinearMap.toMatrix_apply, triangularMatrixBasis_apply,
    LieAlgebra.ad_apply, LieRing.of_associative_ring_bracket,
    triangularMatrixBasis_repr]
  exact matrix_commutator_single_zero A hA p q r s hij

/-- A faithful triangular matrix representation produces the precise
simultaneous adjoint basis used by the height development. -/
theorem nonempty_triangularAdjoint_of_triangular_representation
    {L : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
    {n : ℕ} (ρ : L →ₗ⁅ℝ⁆ Matrix (Fin n) (Fin n) ℝ)
    (hρ : Function.Injective ρ) (htri : ∀ x, (ρ x).IsUpperTriangular) :
    ∃ m : ℕ, Nonempty (TriangularAdjoint L m) := by
  let b := triangularMatrixBasis n
  let e : L →ₗ[ℝ] (Fin (n * n) → ℝ) :=
    (triangularMatrixCoordinates n).toLinearMap.comp ρ.toLinearMap
  let T := LieAlgebra.ad ℝ L
  let A (x : L) := LinearMap.toMatrix b b
    (LieAlgebra.ad ℝ (Matrix (Fin n) (Fin n) ℝ) (ρ x))
  have he : Function.Injective e :=
    (triangularMatrixCoordinates n).injective.comp hρ
  have hA : ∀ x, (A x).IsUpperTriangular := fun x =>
    upperTriangular_matrix_ad (ρ x) (htri x)
  have hinter : ∀ x v, e (T x v) = A x *ᵥ e v := by
    intro x v
    have hc := LinearMap.toMatrix_mulVec_repr b b
      (LieAlgebra.ad ℝ (Matrix (Fin n) (Fin n) ℝ) (ρ x)) (ρ v)
    have hm : ρ (T x v) = ⁅ρ x, ρ v⁆ := ρ.map_lie x v
    have hcoord (M : Matrix (Fin n) (Fin n) ℝ) :
        ⇑(b.repr M) = triangularMatrixCoordinates n M :=
      funext fun i => triangularMatrixBasis_repr_apply M i
    rw [hcoord, hcoord] at hc
    change triangularMatrixCoordinates n (ρ (T x v)) =
      A x *ᵥ triangularMatrixCoordinates n (ρ v)
    rw [hm]
    exact hc.symm
  obtain ⟨m, bL, hbL⟩ := exists_upperTriangular_basis_of_embedding e he T A hA hinter
  exact ⟨m, ⟨⟨bL, hbL⟩⟩⟩

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_TriangularExponentialKernel
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Positive triangular exponentials and their kernel

A faithful triangular Lie representation exponentiates into the positive
triangular group. Nilradical exponentials are unipotent, and a real upper
triangular matrix with exponential equal to the identity is zero.
-/

noncomputable section
namespace PolycyclicRecognition

open scoped Matrix.Norms.Operator

variable {n : ℕ}

theorem triangular_exp_eq_one_iff (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.IsUpperTriangular) : NormedSpace.exp A = 1 ↔ A = 0 := by
  constructor
  · intro he
    have hdiag (i : Fin n) : A i i = 0 := by
      have hi := congrArg (fun B : Matrix (Fin n) (Fin n) ℝ => B i i) he
      rw [matrix_exp_diagonal A hA] at hi
      apply Real.exp_injective
      simpa only [Real.exp_zero, Matrix.one_apply_eq] using hi
    have hn := upperTriangular_nilpotent_of_diag_zero A hA hdiag
    obtain ⟨k, hk⟩ := hn
    let : NormedAlgebra ℚ (Matrix (Fin n) (Fin n) ℝ) :=
      NormedAlgebra.restrictScalars ℚ ℝ _
    have hk' : A ^ (k + 1) = 0 := by rw [pow_succ, hk, zero_mul]
    have h := finiteNilpotentLog_analytic_exp A k hk'
    have hz : finiteNilpotentLog (k + 1) (0 : Matrix (Fin n) (Fin n) ℝ) = 0 := by
      rw [finiteNilpotentLog, ← Polynomial.coeff_zero_eq_aeval_zero']
      simp [PowerSeries.coeff_trunc, PowerSeries.coeff_log]
    have he' : NormedSpace.exp A - 1 = (0 : Matrix (Fin n) (Fin n) ℝ) :=
      (congrArg (fun B : Matrix (Fin n) (Fin n) ℝ => B - 1) he).trans (sub_self 1)
    exact h.symm.trans ((congrArg (finiteNilpotentLog (k + 1)) he').trans hz)
  · rintro rfl
    exact NormedSpace.exp_zero

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_TriangularLocalLogarithm
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The local logarithm in the full real upper triangular algebra -/

noncomputable section
namespace PolycyclicRecognition

open Filter Topology
open scoped Matrix.Norms.Operator

variable {n : ℕ}

theorem realTriangularAlgebra_coe_exp (a : RealTriangularAlgebra n) :
    ((NormedSpace.exp a : RealTriangularAlgebra n) : Matrix (Fin n) (Fin n) ℝ) =
      NormedSpace.exp (a : Matrix (Fin n) (Fin n) ℝ) := by
  let : NormedAlgebra ℚ (RealTriangularAlgebra n) :=
    NormedAlgebra.restrictScalars ℚ ℝ _
  let : NormedAlgebra ℚ (Matrix (Fin n) (Fin n) ℝ) :=
    NormedAlgebra.restrictScalars ℚ ℝ _
  exact NormedSpace.map_exp
    (Matrix.blockTriangularSubalgebra ℝ ℝ (id : Fin n → Fin n)).val.toRingHom
    continuous_subtype_val a

theorem realTriangularAlgebra_exp_kernel (a : RealTriangularAlgebra n)
    (ha : NormedSpace.exp a = 1) : a = 0 := by
  apply Subtype.ext
  have he := congrArg (fun b : RealTriangularAlgebra n =>
    (b : Matrix (Fin n) (Fin n) ℝ)) ha
  rw [realTriangularAlgebra_coe_exp] at he
  exact (triangular_exp_eq_one_iff _ a.property).mp he

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_TriangularExponentialInjective
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.CartanFactorModel.heightRay_zero _root_.OAI.PolycyclicRecognition.CartanWordModel.supportDatum_weight _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Global injectivity of the real upper triangular matrix exponential

Its differential is nonsingular at every point, by the real triangular
adjoint calculation. Local injectivity at a logarithm, together with the
already proved trivial exponential kernel, excludes every other logarithm.
-/

noncomputable section
namespace PolycyclicRecognition

open Set
open scoped Matrix.Norms.Operator ContDiff
attribute [local instance 100] LieRing.ofAssociativeRing

theorem realTriangularAlgebra_exp_injective (n : ℕ) :
    Function.Injective (NormedSpace.exp : RealTriangularAlgebra n → RealTriangularAlgebra n) := by
  let A := RealTriangularAlgebra n
  let ρ : A →ₗ⁅ℝ⁆ Matrix (Fin n) (Fin n) ℝ :=
    (Matrix.blockTriangularSubalgebra ℝ ℝ (id : Fin n → Fin n)).val.toLieHom
  obtain ⟨m, ⟨T⟩⟩ := nonempty_triangularAdjoint_of_triangular_representation
    ρ Subtype.val_injective (fun x => x.property)
  intro a b hab
  let D : A →L[ℝ] A := fderiv ℝ NormedSpace.exp b
  have hD : Function.Injective D := by
    intro x y hxy
    apply represented_exponential_differential_injective T (LieHom.id : A →ₗ⁅ℝ⁆ A)
      Function.injective_id b
    exact hxy
  have hsurj : Function.Surjective D :=
    (LinearMap.injective_iff_surjective).mp hD
  let e : A ≃L[ℝ] A :=
    (LinearEquiv.ofBijective D.toLinearMap ⟨hD, hsurj⟩).toContinuousLinearEquiv
  have hd : HasFDerivAt (NormedSpace.exp : A → A) e.toContinuousLinearMap b :=
    (NormedSpace.exp_analytic (𝕂 := ℝ) b).differentiableAt.hasFDerivAt
  have hreg : ContDiffAt ℝ ∞ (NormedSpace.exp : A → A) b :=
    (NormedSpace.exp_analytic (𝕂 := ℝ) b).contDiffAt
  have hs := hreg.hasStrictFDerivAt' hd (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  let p := hs.toOpenPartialHomeomorph NormedSpace.exp
  exact exp_eq_of_local_injectivity realTriangularAlgebra_exp_kernel
    p.source p.open_source p.injOn hs.mem_toOpenPartialHomeomorph_source hab

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

theorem rotationExponentialProduct_eq_one (x : T.kernelIdeal) (h : H)
    (hx : (x : GroupLieAlgebra (𝓘(ℝ,E)) G) = -(h : GroupLieAlgebra (𝓘(ℝ,E)) G)) :
    F.rotationExponentialProduct hExp (x,h) = 1 := by
  apply (F.smoothRotationalModificationHomeomorph hExp).injective
  change F.smoothRotationalModificationHomeomorph hExp
    (F.nilpotentFactorToRotation hExp (F.ExpN (F.N.equiv x)) *
      F.cartanFactorToRotation hExp (F.ExpD (F.D.equiv h))) = 1
  rw [F.rotationFactorProduct_coordinates, F.compatibleN, F.compatibleD, hx,
    hExp.map_neg, inv_mul_cancel]

end ComplexWeightFactorModel
end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_TriangularMatrixExponentialInjective
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Injectivity on upper triangular real matrices -/

noncomputable section
namespace PolycyclicRecognition
open scoped Matrix.Norms.Operator

theorem triangularMatrix_exp_injective {m : ℕ}
    {x y : Matrix (Fin m) (Fin m) ℝ}
    (hx : x.IsUpperTriangular) (hy : y.IsUpperTriangular)
    (h : NormedSpace.exp x = NormedSpace.exp y) : x = y := by
  let X : RealTriangularAlgebra m := ⟨x,hx⟩
  let Y : RealTriangularAlgebra m := ⟨y,hy⟩
  have he : NormedSpace.exp X = NormedSpace.exp Y := by
    apply Subtype.ext
    simpa only [realTriangularAlgebra_coe_exp] using h
  exact congrArg Subtype.val (realTriangularAlgebra_exp_injective m he)

theorem triangular_units_product_eq_one_imp_neg {L : Type*}
    [AddCommGroup L] [Module ℝ L] {m : ℕ}
    (j : L →ₗ[ℝ] Matrix (Fin m) (Fin m) ℝ) (hj : Function.Injective j)
    (hu : ∀ x, (j x).IsUpperTriangular) (x y : L)
    (h : algebraExpUnit (j x) * algebraExpUnit (j y) = 1) : x = -y := by
  have hm : algebraExpUnit (j x) = algebraExpUnit (-j y) := by
    rw [algebraExpUnit_neg]
    exact eq_inv_of_mul_eq_one_left h
  have he := triangularMatrix_exp_injective (hu x) (hu y).neg (congrArg Units.val hm)
  apply hj
  simpa only [map_neg] using he

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_RotationRepresentationFaithful
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Faithfulness from the two exponential factors -/

noncomputable section
namespace PolycyclicRecognition
open scoped Manifold Matrix.Norms.Operator
attribute [local instance 100] LieRing.ofAssociativeRing

variable {E G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MetricSpace G] [ChartedSpace E G]
  [Group G] [LieGroup (𝓘(ℝ,E)) ⊤ G]
  {a : ℕ} {T : ComplexTriangularAdjoint (GroupLieAlgebra (𝓘(ℝ,E)) G) a}
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ,E)) G)} [H.IsCartanSubalgebra]
  {Exp : GroupLieAlgebra (𝓘(ℝ,E)) G → G}

namespace ComplexWeightFactorModel
variable (F : ComplexWeightFactorModel T H Exp) (hExp : IsGroupExponential Exp)
attribute [local instance] semidirectProductTopology

theorem rotationRepresentation_faithful_oai {m : ℕ}
    (j : CartanRealShadow T H →ₗ⁅ℝ⁆ Matrix (Fin m) (Fin m) ℝ)
    (hj : Function.Injective j) (hu : ∀ x, (j x).IsUpperTriangular)
    (ρ : F.SmoothRotationalModification hExp →* (Matrix (Fin m) (Fin m) ℝ)ˣ)
    (he : ∀ (x : T.kernelIdeal) (h : H),
      ρ (F.nilpotentFactorToRotation hExp (F.ExpN (F.N.equiv x)) *
        F.cartanFactorToRotation hExp (F.ExpD (F.D.equiv h))) =
        algebraExpUnit (j (cartanRealShadowEquiv T H x)) *
          algebraExpUnit (j (cartanRealShadowEquiv T H h))) :
    Function.Injective ρ := by
  let f := F.rotationExponentialProduct hExp
  have hf : Function.Surjective f := F.rotationExponentialProduct_surjective hExp
  apply injective_of_kernel_in_coordinates ρ f hf
  rintro ⟨x,h⟩ hg
  change ρ (F.nilpotentFactorToRotation hExp (F.ExpN (F.N.equiv x)) *
      F.cartanFactorToRotation hExp (F.ExpD (F.D.equiv h))) = 1 at hg
  rw [he] at hg
  have ht := triangular_units_product_eq_one_imp_neg j.toLinearMap hj hu
    (cartanRealShadowEquiv T H x) (cartanRealShadowEquiv T H h) hg
  have hx : (x : GroupLieAlgebra (𝓘(ℝ,E)) G) = -(h : GroupLieAlgebra (𝓘(ℝ,E)) G) := by
    apply (cartanRealShadowEquiv T H).injective
    simpa only [map_neg] using ht
  exact F.rotationExponentialProduct_eq_one hExp x h hx

end ComplexWeightFactorModel
end PolycyclicRecognition

end

end OAI
end

theorem solution : type_of% @OAI.PolycyclicRecognition.ComplexWeightFactorModel.rotationRepresentation_faithful_oai := @OAI.PolycyclicRecognition.ComplexWeightFactorModel.rotationRepresentation_faithful_oai
