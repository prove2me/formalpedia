-- Prove2me | solution 1 for OAI.PolycyclicRecognition.cornulierTesseraModelInput
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-03T01:02:39.099594+00:00
-- url     : https://prove2.me/submissions/db31e9f2-9644-417b-a7c7-8929fe2e837d

import Mathlib
import Definitions.Def_PolycyclicRecognition
import Definitions.Def_OAIQ093D023
import Theorems.Thm_OAI_PolycyclicRecognition_ComplexWeightFactorModel_exists_triangulable_rotation_model

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_AlgebraGroupTangent
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Infinitesimal commutators of matrix groups

The finite-dimensional span of derivatives of curves in a subgroup records
its infinitesimal action. Differentiating group commutators twice puts the
algebra commutator into the tangent span of the derived subgroup.
-/

noncomputable section
namespace PolycyclicRecognition

open scoped Topology commutatorElement
open Filter

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]
  [FiniteDimensional ℝ A] [CompleteSpace A]

omit [FiniteDimensional ℝ A] [CompleteSpace A] in
/-- The identity group has zero tangent span. -/
theorem algebraGroupTangentSpan_bot : algebraGroupTangentSpan (⊥ : Subgroup Aˣ) = ⊥ := by
  apply le_antisymm _ bot_le
  apply Submodule.span_le.mpr
  rintro X ⟨c, hc, _, hd⟩
  have hfun : (fun t => (c t : A)) = fun _ => (1 : A) := by
    funext t
    rw [show c t = 1 from hc t]
    rfl
  rw [hfun] at hd
  exact hd.unique (hasDerivAt_const 0 (1 : A))

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_AlgebraTangentSolvable
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Solvability of the infinitesimal action of a solvable matrix group

The group derived series controls successive commutators of the tangent
spans. This avoids assuming a closed-subgroup or Lie–Kolchin theorem.
-/

noncomputable section
namespace PolycyclicRecognition

attribute [local instance 100] LieRing.ofAssociativeRing

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]
  [FiniteDimensional ℝ A] [CompleteSpace A]

/-- The tangent Lie algebra of a solvable subgroup of units is solvable. -/
theorem algebraGroupTangentLie_isSolvable (D : Subgroup Aˣ) [Group.IsSolvable D] :
    LieAlgebra.IsSolvable (algebraGroupTangentLie D) := by
  let L := algebraGroupTangentLie D
  let E (n : ℕ) := (derivedSeries D n).map D.subtype
  have hE0 : E 0 = D := by simp [E, ← MonoidHom.range_eq_map]
  have hEs (n : ℕ) : E (n + 1) = ⁅E n, E n⁆ := by
    dsimp [E]
    rw [Subgroup.map_commutator]
  have hbound (n : ℕ) : ∀ x ∈ LieAlgebra.derivedSeries ℝ L n,
      (x : A) ∈ algebraGroupTangentSpan (E n) := by
    induction n with
    | zero =>
      intro x _
      rw [hE0]
      exact x.property
    | succ n ih =>
      intro x hx
      have hh : (LieAlgebra.derivedSeries ℝ L (n + 1)).toSubmodule ≤
          (algebraGroupTangentSpan (E (n + 1))).comap L.incl.toLinearMap := by
        rw [LieAlgebra.derivedSeries_def, LieAlgebra.derivedSeriesOfIdeal_succ,
          LieSubmodule.lieIdeal_oper_eq_linear_span']
        apply Submodule.span_le.mpr
        rintro _ ⟨y, hy, z, hz, rfl⟩
        change (y : A) * (z : A) - (z : A) * (y : A) ∈ algebraGroupTangentSpan (E (n + 1))
        rw [hEs]
        exact algebraGroupTangentSpan_commutator (ih y hy) (ih z hz)
      exact hh hx
  obtain ⟨n, hn⟩ := Group.IsSolvable.solvable (G := D)
  apply (LieAlgebra.isSolvable_iff ℝ L).mpr
  refine ⟨n, le_antisymm ?_ bot_le⟩
  intro x hx
  change x = 0
  apply Subtype.ext
  have hb := hbound n x hx
  simpa only [E, hn, Subgroup.map_bot, algebraGroupTangentSpan_bot,
    Submodule.mem_bot, ZeroMemClass.coe_zero] using hb

end PolycyclicRecognition

end

end OAI
end

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

variable {N G Q : Type*} [Group N] [Group G] [Group Q]
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

variable {U V W : Type*}
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

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
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

variable {E F H M N : Type*}
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

variable {EN E W N G : Type*}
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

variable {E E' H H' M M' : Type*}
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
    {X Y : Type*} [TopologicalSpace X] [LocallyCompactSpace X] [TopologicalSpace Y]
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

variable {N D G : Type*} [Group N] [Group D] [Group G]
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

variable {N D G : Type*} [Group N] [Group D] [Group G]
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
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
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

variable {EN ED EG N D G : Type*}
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

variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

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
    {N K Q : Type*} [Group N] [TopologicalSpace N] [IsTopologicalGroup N]
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
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
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
    {G Q : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
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

variable {N K : Type*} [Group N] [TopologicalSpace N] [IsTopologicalGroup N]
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

variable {N G Q : Type*}
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

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_ClosedNilpotentLinearKernel
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.CartanFactorModel.heightRay_zero _root_.OAI.PolycyclicRecognition.CartanFactorModel.realScaleProfile_apply _root_.OAI.PolycyclicRecognition.CartanFactorModel.sampledProbeProfile_apply _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.modelNilradicalLinearAction_apply _root_.OAI.PolycyclicRecognition.modelNilradicalRotation_apply _root_.OAI.PolycyclicRecognition.modelNilradicalRotation_mul _root_.OAI.PolycyclicRecognition.modelNilradicalRotation_one _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Closed integration of a nilpotent linear kernel

The split-coordinate argument for the real height kernel also applies to the
complex adjoint weights, viewed as a real linear quotient. Only nilpotence,
surjectivity and the exact exponential identity are used.
-/

noncomputable section
namespace PolycyclicRecognition

open Set Filter
open scoped Manifold ContDiff Topology

variable {E G W : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MetricSpace G] [ChartedSpace E G] [Group G]
  [LieGroup (𝓘(ℝ, E)) ⊤ G] [SimplyConnectedSpace G]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]

/-- Integrate the nilpotent kernel of an actual surjective linear group
character as a closed subgroup of the given simply connected Lie group. -/
theorem exists_closed_nilpotent_linear_kernel
    (I : LieIdeal ℝ (GroupLieAlgebra (𝓘(ℝ, E)) G)) (hnil : LieRing.IsNilpotent I)
    (d : E →ₗ[ℝ] W) (hd : Function.Surjective d)
    (hker : ∀ x, d x = 0 ↔ x ∈ I)
    (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G) (hExp : IsGroupExponential Exp)
    (π : G →* Multiplicative W) (hπ : Continuous π)
    (hπExp : ∀ x, (π (Exp x)).toAdd = d x) :
    ∃ (N : NilpotentLieModel I)
      (ExpN : GroupLieAlgebra (𝓘(ℝ, N.modelSpace)) N.carrier → N.carrier),
      IsGroupExponential ExpN ∧
      ∃ ι : N.carrier →* G, Topology.IsClosedEmbedding ι ∧
        ContMDiff (𝓘(ℝ, N.modelSpace)) (𝓘(ℝ, E)) ∞ ι ∧
        (∀ x : I, ι (ExpN (N.equiv x)) = Exp x) ∧
        Set.range ι = (π.ker : Set G) := by
  obtain ⟨N⟩ := nilpotentPublishedInputs.existsModel I hnil
  let : IsTopologicalGroup G := topologicalGroup_of_lieGroup (𝓘(ℝ, E)) ⊤
  let : IsTopologicalGroup N.carrier :=
    topologicalGroup_of_lieGroup (𝓘(ℝ, N.modelSpace)) ⊤
  obtain ⟨ExpN, hExpN, cN, hcN⟩ :=
    N.exists_exponential_chart hnil (nilpotentPublishedInputs.haar I N)
  let j := I.incl.comp N.equiv.symm.toLieHom
  have hj : Function.Injective j := Subtype.val_injective.comp N.equiv.symm.injective
  obtain ⟨ι, hιsmooth, hιdiff, hιExp⟩ :=
    nilpotentLieIntegrationInput_of_smooth (nilpotentSmoothIntegrationInput I N)
      inferInstance (N.tangent_nilpotent hnil) j ExpN Exp hExpN hExp
  obtain ⟨s, l, hs, hs0, hsπ, hsl, hdl⟩ :=
    exists_smooth_section_of_exponential_linear_quotient hExp d hd π hπExp
  let jc : N.modelSpace →L[ℝ] E := j.toLinearMap.toContinuousLinearMap
  let dc : E →L[ℝ] W := d.toContinuousLinearMap
  have hjrange : LinearMap.range jc.toLinearMap = LinearMap.ker dc.toLinearMap := by
    ext x
    constructor
    · rintro ⟨v, rfl⟩
      exact (hker (j v)).mpr (N.equiv.symm v).property
    · intro hx
      have hxI : x ∈ I := (hker x).mp hx
      refine ⟨N.equiv ⟨x, hxI⟩, ?_⟩
      exact congrArg Subtype.val (N.equiv.symm_apply_apply ⟨x, hxI⟩)
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
    rw [hπExp]
    exact (hker (j v)).mpr (N.equiv.symm v).property
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

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_ClosedIntegrationOverLinearQuotient
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Closed nilpotent integration over a real linear quotient

This is the section-and-kernel argument with the concrete kernel supplied
explicitly. It applies to the complex adjoint-weight quotient, regarded as a
real vector space, without real triangularity of the original group.
-/

noncomputable section
namespace PolycyclicRecognition

open Set
open scoped Manifold ContDiff

variable {E G W : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MetricSpace G] [ChartedSpace E G] [Group G]
  [LieGroup (𝓘(ℝ, E)) ⊤ G] [SimplyConnectedSpace G]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]

theorem exists_closed_nilpotent_integration_over_linear_quotient
    (I : LieIdeal ℝ (GroupLieAlgebra (𝓘(ℝ, E)) G)) (hI : LieRing.IsNilpotent I)
    (d : E →ₗ[ℝ] W) (hd : Function.Surjective d)
    (hker : ∀ x, d x = 0 ↔ x ∈ I)
    (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G) (hExp : IsGroupExponential Exp)
    (π : G →* Multiplicative W) (hπ : Continuous π)
    (hπExp : ∀ x, (π (Exp x)).toAdd = d x)
    (L : Type) [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
    (N : NilpotentLieModel L) (hnil : LieRing.IsNilpotent L)
    (j : GroupLieAlgebra (𝓘(ℝ, N.modelSpace)) N.carrier →ₗ⁅ℝ⁆
      GroupLieAlgebra (𝓘(ℝ, E)) G) (hj : Function.Injective j)
    (hsurj : Function.Surjective (d.comp j.toLinearMap)) :
    ∃ ι : N.carrier →* G, Topology.IsClosedEmbedding ι ∧
      ContMDiff (𝓘(ℝ, N.modelSpace)) (𝓘(ℝ, E)) ∞ ι ∧
      ∀ (ExpN : GroupLieAlgebra (𝓘(ℝ, N.modelSpace)) N.carrier → N.carrier),
        IsGroupExponential ExpN → ∀ x, ι (ExpN x) = Exp (j x) := by
  let : IsTopologicalGroup G := topologicalGroup_of_lieGroup (𝓘(ℝ, E)) ⊤
  let : IsTopologicalGroup N.carrier := topologicalGroup_of_lieGroup (𝓘(ℝ, N.modelSpace)) ⊤
  obtain ⟨ExpN, hExpN, cN, hcN⟩ := N.exists_exponential_chart hnil
    (nilpotentPublishedInputs.haar L N)
  obtain ⟨ι, hι, _, heι⟩ :=
    nilpotentLieIntegrationInput_of_smooth (nilpotentSmoothIntegrationInput L N)
      inferInstance (N.tangent_nilpotent hnil) j ExpN Exp hExpN hExp
  obtain ⟨K, ExpK, hExpK, κ, hκ, _, heκ, hrκ⟩ :=
    exists_closed_nilpotent_linear_kernel I hI d hd hker Exp hExp π hπ hπExp
  let : IsTopologicalGroup K.carrier := topologicalGroup_of_lieGroup (𝓘(ℝ, K.modelSpace)) ⊤
  obtain ⟨cK, hcK⟩ := ((nilpotentPublishedInputs.haar I K).2
    ExpK hExpK (K.tangent_nilpotent hI)).1
  let dN := d.comp j.toLinearMap
  have hquot (x : N.modelSpace) : (π (ι (ExpN x))).toAdd = dN x := by
    exact (congrArg (fun g => (π g).toAdd) (heι x)).trans (hπExp (j x))
  obtain ⟨s, hs, _, hsright⟩ :=
    exists_continuous_section_of_exponential_linear_quotient hExpN dN hsurj (π.comp ι) hquot
  let sectionN : C(Multiplicative W, N.carrier) := ⟨fun w => s w.toAdd, hs⟩
  have hsN (w : Multiplicative W) : π (ι (sectionN w)) = w := Multiplicative.ext (hsright w.toAdd)
  let eN : dN.ker ≃ₜ (π.comp ι).ker := cN.subtype (fun x => by
    change dN x = 0 ↔ π (ι (cN x)) = 1
    rw [hcN]
    constructor
    · intro hx
      apply Multiplicative.ext
      exact (hquot x).trans hx
    · intro hx
      exact (hquot x).symm.trans (congrArg Multiplicative.toAdd hx))
  let eK : K.modelSpace ≃ₜ π.ker :=
    cK.trans (kernelRealization π κ hκ hrκ).toHomeomorph
  let jK : dN.ker →ₗ[ℝ] K.modelSpace := K.equiv.toLinearMap.comp
    ((j.toLinearMap.comp dN.ker.subtype).codRestrict I.toSubmodule (by
      intro x
      exact (hker (j x)).mp x.property))
  have hjK : Function.Injective jK := by
    intro x y h
    apply Subtype.ext
    apply hj
    exact congrArg Subtype.val (K.equiv.injective h)
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
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_ComplexCharacterLift
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Additive lifts of complex characters

Rotational diagonal characters in a simply connected solvable group have
continuous logarithms. Uniqueness of covering lifts makes the normalized
logarithm additive; its value on an exponential curve is the prescribed
linear weight, with no choice of a global principal logarithm.
-/

noncomputable section
namespace PolycyclicRecognition

open Function

/-- Two continuous lifts through the complex exponential agree everywhere
when they agree at one point of a connected domain. -/
theorem eq_of_continuous_complex_exp_eq
    {X : Type*} [TopologicalSpace X] [PreconnectedSpace X]
    {f g : X → ℂ} (hf : Continuous f) (hg : Continuous g)
    (he : ∀ x, Complex.exp (f x) = Complex.exp (g x))
    (x₀ : X) (h₀ : f x₀ = g x₀) : f = g := by
  apply Complex.isCoveringMap_exp.eq_of_comp_eq hf hg _ x₀ h₀
  funext x
  exact Subtype.ext (he x)

/-- A continuous character into the nonzero complex numbers has a
normalized additive lift on a simply connected group. -/
theorem exists_additive_lift_complex_character
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [SimplyConnectedSpace G] [LocallyPathConnectedSpace G]
    (χ : G →* ℂˣ) (hχ : Continuous (fun g => (χ g : ℂ))) :
    ∃ π : G →* Multiplicative ℂ, Continuous (fun g => (π g).toAdd) ∧
      ∀ g, Complex.exp (π g).toAdd = (χ g : ℂ) := by
  let c : C(G, ℂ) := ⟨fun g => (χ g : ℂ), hχ⟩
  obtain ⟨F, ⟨hF0, hFexp⟩, _⟩ :=
    Complex.isCoveringMapOn_exp.existsUnique_continuousMap_lifts c
      (a₀ := 1) (e₀ := 0) (by simp [c]) (fun g => (χ g).ne_zero)
  have he (g : G) : Complex.exp (F g) = (χ g : ℂ) := congrFun hFexp g
  have hmul (g h : G) : F (g * h) = F g + F h := by
    have heq : (fun h : G => F (g * h) - F g) = F := by
      refine eq_of_continuous_complex_exp_eq
        ((F.continuous.comp (continuous_const.mul continuous_id)).sub continuous_const)
        F.continuous (fun h => ?_) 1 (by simp [hF0])
      rw [Complex.exp_sub, he, he, he, map_mul, Units.val_mul]
      exact mul_div_cancel_left₀ _ (χ g).ne_zero
    have hv := congrFun heq h
    exact (sub_eq_iff_eq_add.mp hv).trans (add_comm _ _)
  refine ⟨{
    toFun := fun g => Multiplicative.ofAdd (F g)
    map_one' := hF0
    map_mul' := hmul }, F.continuous, he⟩

/-- The additive lift recovers the exact weight along a continuous
one-parameter curve starting at the identity. -/
theorem additive_lift_complex_character_on_curve
    {G : Type*} [Group G] [TopologicalSpace G]
    (χ : G →* ℂˣ) (π : G →* Multiplicative ℂ)
    (hπ : Continuous (fun g => (π g).toAdd))
    (he : ∀ g, Complex.exp (π g).toAdd = (χ g : ℂ))
    (γ : ℝ → G) (hγ : Continuous γ) (hγ0 : γ 0 = 1)
    (z : ℂ) (hz : ∀ t, (χ (γ t) : ℂ) = Complex.exp ((t : ℂ) * z)) :
    ∀ t, (π (γ t)).toAdd = (t : ℂ) * z := by
  have hf : (fun t => (π (γ t)).toAdd) = (fun t : ℝ => (t : ℂ) * z) := by
    exact eq_of_continuous_complex_exp_eq (hπ.comp hγ)
      (Complex.continuous_ofReal.mul continuous_const)
      (fun t => (he (γ t)).trans (hz t)) 0 (by simp [hγ0])
  exact congrFun hf

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_SplitLieQuotient
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Compatibility with OpenAI's Mathlib (d13f23b): a lemma it has and ours lacks. -/

theorem Module.End.map_genEigenspace_le {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    {N : Type*} [AddCommGroup N] [Module R N]
    {f : Module.End R M} {g : Module.End R N} (φ : M →ₗ[R] N) (hφ : g.comp φ = φ.comp f)
    (μ : R) (k : ℕ∞) :
    (f.genEigenspace μ k).map φ ≤ g.genEigenspace μ k := by
  rintro y ⟨x, hx, rfl⟩
  obtain ⟨l, hl, hx⟩ := Module.End.mem_genEigenspace.mp hx
  refine Module.End.mem_genEigenspace.mpr ⟨l, hl, ?_⟩
  simp only [LinearMap.mem_ker, Module.End.pow_apply] at hx ⊢
  suffices (⇑φ).Semiconj ⇑(f - μ • 1) ⇑(g - μ • 1) by rw [← this.iterate_right, hx, map_zero]
  intro; simpa using congr($hφ _).symm

namespace OAI

/-!
# Split Lie actions pass to invariant quotients

The simultaneous-basis form of Lie's theorem requires induction on a
quotient by a common eigenline. We prove the splitting hypothesis for
that quotient using images of the original generalized eigenspaces.
-/

namespace PolycyclicRecognition

open Module

variable {𝕜 : Type*} [Field 𝕜]

variable {L V : Type*} [LieRing L] [LieAlgebra 𝕜 L]
  [AddCommGroup V] [Module 𝕜 V] [LieRingModule L V] [LieModule 𝕜 L V]

/-- A quotient of a split Lie action remains split. The image of each
generalized eigenspace lies in the corresponding quotient eigenspace. -/
theorem quotient_isTriangularizable [LieModule.IsTriangularizable 𝕜 L V]
    (N : LieSubmodule 𝕜 L V) : LieModule.IsTriangularizable 𝕜 L (V ⧸ N) := by
  refine ⟨fun x => ?_⟩
  let q : V →ₗ[𝕜] V ⧸ N := N.toSubmodule.mkQ
  have hq : q.range = ⊤ := LinearMap.range_eq_top.mpr N.toSubmodule.mkQ_surjective
  have hcomm : (LieModule.toEnd 𝕜 L (V ⧸ N) x).comp q =
      q.comp (LieModule.toEnd 𝕜 L V x) := by
    ext v
    rfl
  apply le_antisymm le_top
  calc
    (⊤ : Submodule 𝕜 (V ⧸ N)) = (⊤ : Submodule 𝕜 V).map q := by
      rw [Submodule.map_top, hq]
    _ = (⨆ μ : 𝕜, (LieModule.toEnd 𝕜 L V x).maxGenEigenspace μ).map q := by
      rw [LieModule.IsTriangularizable.maxGenEigenspace_eq_top x]
    _ ≤ ⨆ μ : 𝕜, (LieModule.toEnd 𝕜 L (V ⧸ N) x).maxGenEigenspace μ := by
      rw [Submodule.map_iSup]
      exact iSup_mono fun μ => Module.End.map_genEigenspace_le q hcomm μ ⊤

end PolycyclicRecognition

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_SimultaneousAdjointBasis
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The simultaneous-basis form of Lie's theorem

Mathlib's Lie theorem supplies a common eigenvector for a solvable split
action. We iterate it on invariant quotients and lift each quotient basis,
obtaining the single upper triangular basis required by `TriangularAdjoint`.
-/

noncomputable section

namespace PolycyclicRecognition

open Module Set

/-- A finite-dimensional split action of a solvable split Lie algebra has
a simultaneous upper triangular basis. -/
theorem exists_upperTriangular_lieModule_basis {𝕜 : Type*} [Field 𝕜] [CharZero 𝕜]
    (L V : Type*)
    [LieRing L] [LieAlgebra 𝕜 L] [LieAlgebra.IsSolvable L]
    [AddCommGroup V] [Module 𝕜 V] [LieRingModule L V] [LieModule 𝕜 L V]
    [FiniteDimensional 𝕜 V] [LieModule.IsTriangularizable 𝕜 L V] :
    ∃ (n : ℕ) (b : Basis (Fin n) 𝕜 V),
      ∀ x : L, (LinearMap.toMatrix b b (LieModule.toEnd 𝕜 L V x)).IsUpperTriangular := by
  classical
  by_cases hzero : finrank 𝕜 V = 0
  · refine ⟨finrank 𝕜 V, Module.finBasis 𝕜 V, ?_⟩
    intro x i j hij
    have := i.isLt
    omega
  have hpos : 0 < finrank 𝕜 V := Nat.pos_of_ne_zero hzero
  let : Nontrivial V := finrank_pos_iff.mp hpos
  obtain ⟨χ, hχ⟩ := LieModule.exists_nontrivial_weightSpace_of_isSolvable 𝕜 L V
  let := hχ
  obtain ⟨v, hv⟩ := exists_ne (0 : LieModule.weightSpace V χ)
  have hv0 : (v : V) ≠ 0 := by
    intro h
    exact hv (Subtype.ext h)
  have hvχ : ∀ x : L, ⁅x, (v : V)⁆ = χ x • (v : V) :=
    (LieModule.mem_weightSpace χ (v : V)).mp v.property
  let N : LieSubmodule 𝕜 L V :=
    { (𝕜 ∙ (v : V)) with
      lie_mem := by
        intro x w hw
        obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hw
        rw [lie_smul, hvχ]
        exact Submodule.smul_mem _ a
          (Submodule.smul_mem _ (χ x) (Submodule.mem_span_singleton_self (v : V))) }
  have hdimN : finrank 𝕜 N.toSubmodule = 1 := finrank_span_singleton hv0
  have hlt : finrank 𝕜 (V ⧸ N) < finrank 𝕜 V := by
    change finrank 𝕜 (V ⧸ N.toSubmodule) < finrank 𝕜 V
    have hd := N.toSubmodule.finrank_quotient_add_finrank
    rw [hdimN] at hd
    omega
  let : LieModule.IsTriangularizable 𝕜 L (V ⧸ N) := quotient_isTriangularizable (𝕜 := 𝕜) N
  obtain ⟨n, bQ, hQ⟩ := exists_upperTriangular_lieModule_basis (𝕜 := 𝕜) L (V ⧸ N)
  let bN : Basis (Fin 1) 𝕜 N.toSubmodule := FiniteDimensional.basisSingleton (Fin 1) hdimN
    ⟨v, Submodule.mem_span_singleton_self (v : V)⟩ (by
      intro h
      apply hv0
      exact congrArg Subtype.val h)
  choose lift hlift using fun i : Fin n => N.toSubmodule.mkQ_surjective (bQ i)
  let b := basisWithQuotientLifts N.toSubmodule bN bQ lift hlift
  let e : Fin 1 ⊕ Fin n ≃ Fin (1 + n) := finSumFinEquiv
  refine ⟨1 + n, b.reindex e, ?_⟩
  intro x i j hij
  obtain ⟨i, rfl⟩ := e.surjective i
  obtain ⟨j, rfl⟩ := e.surjective j
  simp only [LinearMap.toMatrix_apply, LieModule.toEnd_apply_apply]
  simp only [Basis.repr_reindex_apply, Basis.reindex_apply, Equiv.symm_apply_apply]
  dsimp only [b]
  cases i with
  | inl i =>
    cases j with
    | inl j =>
      have hi : (i : ℕ) = 0 := by omega
      have hj : (j : ℕ) = 0 := by omega
      have heq : i = j := Fin.ext (hi.trans hj.symm)
      exact (hij.ne (congrArg (fun a => e (Sum.inl a)) heq).symm).elim
    | inr j =>
      have hi : (i : ℕ) = 0 := by omega
      change 1 + (j : ℕ) < (i : ℕ) at hij
      omega
  | inr i =>
    cases j with
    | inl j =>
      rw [basisWithQuotientLifts_inl, basisWithQuotientLifts_repr_inr]
      have hz : N.toSubmodule.mkQ ⁅x, (bN j : V)⁆ = 0 :=
        (Submodule.Quotient.mk_eq_zero N.toSubmodule).mpr (N.lie_mem (bN j).property)
      rw [hz, map_zero, Finsupp.zero_apply]
    | inr j =>
      rw [basisWithQuotientLifts_inr, basisWithQuotientLifts_repr_inr]
      have hq : N.toSubmodule.mkQ ⁅x, lift j⁆ =
          (LieModule.toEnd 𝕜 L (V ⧸ N) x) (bQ j) := by
        change (LieModule.toEnd 𝕜 L (V ⧸ N) x) (N.toSubmodule.mkQ (lift j)) = _
        rw [hlift]
      rw [hq]
      change 1 + (j : ℕ) < 1 + (i : ℕ) at hij
      simpa only [LinearMap.toMatrix_apply, LieModule.toEnd_apply_apply] using
        hQ x (i := i) (j := j) (by change (j : ℕ) < (i : ℕ); omega)
termination_by finrank 𝕜 V

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_ComplexAdjointWeights
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Complex adjoint weights for solvable real Lie algebras

The existing simultaneous-basis construction applies over the complex
numbers as well. Its restriction to real vectors supplies the weights whose
lifted group characters are used in the general solvable lattice argument.
-/

noncomputable section
namespace PolycyclicRecognition

open scoped TensorProduct
open Module
attribute [local instance 100] LieRing.ofAssociativeRing

variable (L : Type*) [LieRing L] [LieAlgebra ℝ L]

/-- A complex triangular basis of the actual complexified adjoint action. -/
theorem exists_complex_triangular_adjoint_basis [FiniteDimensional ℝ L]
    [LieAlgebra.IsSolvable L] :
    ∃ (n : ℕ) (b : Basis (Fin n) ℂ (ℂ ⊗[ℝ] L)),
      ∀ x : ℂ ⊗[ℝ] L,
        (LinearMap.toMatrix b b (LieAlgebra.ad ℂ (ℂ ⊗[ℝ] L) x)).IsUpperTriangular := by
  exact exists_upperTriangular_lieModule_basis (𝕜 := ℂ) (ℂ ⊗[ℝ] L) (ℂ ⊗[ℝ] L)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_IntrinsicAdjointHeight
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
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

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_ComplexMatrixExtension
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Complex matrix coordinates for the intrinsic adjoint representation -/

noncomputable section
namespace PolycyclicRecognition

open Module
open scoped TensorProduct Manifold Matrix.Norms.Operator
attribute [local instance 100] LieRing.ofAssociativeRing

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] {m n : ℕ}

theorem complexMatrixExtension_ad (b : Basis (Fin m) ℝ L)
    (c : Basis (Fin n) ℂ (ℂ ⊗[ℝ] L)) (x : L) :
    complexMatrixExtension b c (LinearMap.toMatrix b b (LieAlgebra.ad ℝ L x)) =
      complexifiedAdjointMatrix L c x := by
  have hmat : (Algebra.ofId ℝ ℂ).mapMatrix
      (LinearMap.toMatrix b b (LieAlgebra.ad ℝ L x)) =
      LinearMap.toMatrix (b.baseChange ℂ) (b.baseChange ℂ)
        (LieAlgebra.ad ℂ (ℂ ⊗[ℝ] L) ((complexificationLieHom L) x)) := by
    ext i j
    simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, LinearMap.toMatrix_apply,
      Basis.baseChange_apply]
    change _ = (b.baseChange ℂ).repr ⁅(1 : ℂ) ⊗ₜ[ℝ] x, (1 : ℂ) ⊗ₜ[ℝ] b j⁆ i
    simp
  change (LinearMap.toMatrixAlgEquiv c)
    ((LinearMap.toMatrixAlgEquiv (b.baseChange ℂ)).symm
      ((Algebra.ofId ℝ ℂ).mapMatrix _)) = _
  rw [hmat]
  exact congrArg (LinearMap.toMatrixAlgEquiv c)
    ((LinearMap.toMatrixAlgEquiv (b.baseChange ℂ)).symm_apply_apply _)

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace G] [ChartedSpace E G]
  [Group G] [LieGroup (𝓘(ℝ, E)) ⊤ G] [T2Space G]

omit [T2Space G] in
theorem continuous_complexAdjointMatrixHom
    (b : Basis (Fin m) ℝ (GroupLieAlgebra (𝓘(ℝ, E)) G))
    (c : Basis (Fin n) ℂ (ℂ ⊗[ℝ] GroupLieAlgebra (𝓘(ℝ, E)) G)) :
    Continuous (complexAdjointMatrixHom b c) :=
  (complexMatrixExtension b c).toLinearMap.continuous_of_finiteDimensional.comp
    (continuous_adjointMatrixHom b)

omit [T2Space G] in
theorem complexAdjointMatrixHom_exp
    (b : Basis (Fin m) ℝ (GroupLieAlgebra (𝓘(ℝ, E)) G))
    (c : Basis (Fin n) ℂ (ℂ ⊗[ℝ] GroupLieAlgebra (𝓘(ℝ, E)) G))
    {Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G} (hExp : IsGroupExponential Exp)
    (x : GroupLieAlgebra (𝓘(ℝ, E)) G) :
    complexAdjointMatrixHom b c (Exp x) = NormedSpace.exp (complexifiedAdjointMatrix _ c x) := by
  let F := complexMatrixExtension b c
  let : NormedAlgebra ℚ (Matrix (Fin m) (Fin m) ℝ) := NormedAlgebra.restrictScalars ℚ ℝ _
  let : NormedAlgebra ℚ (Matrix (Fin n) (Fin n) ℂ) := NormedAlgebra.restrictScalars ℚ ℝ _
  change F (adjointMatrixHom b (Exp x)) = _
  rw [adjointMatrixHom_exp_intrinsic b hExp]
  have hm := NormedSpace.map_exp F.toRingHom F.toLinearMap.continuous_of_finiteDimensional
    (LinearMap.toMatrix b b (LieAlgebra.ad ℝ _ x))
  exact hm.trans (congrArg NormedSpace.exp (complexMatrixExtension_ad b c x))

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

/-- Connectedness discharges the compact-generation hypothesis of the
published metric-existence theorem for the solvable Lie model. -/
theorem SimplyConnectedSolvableLieModel.nonempty_properChainMetric
    (S : SimplyConnectedSolvableLieModel) (metricInput : GeodesicMetricExistenceInput) :
    Nonempty (ProperChainMetric S.carrier) := by
  let : IsTopologicalGroup S.carrier :=
    topologicalGroup_of_lieGroup (𝓘(ℝ, S.modelSpace)) ⊤
  let : LocallyCompactSpace S.carrier :=
    Manifold.locallyCompact_of_finiteDimensional (𝓘(ℝ, S.modelSpace))
  exact metricInput S.carrier (exists_compact_generating_set S.carrier)

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
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_ComplexTriangularExponential
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Complex upper triangular matrix exponentials -/

noncomputable section
namespace PolycyclicRecognition
open scoped Matrix.Norms.Operator
variable {n : ℕ}

private theorem entry_hasSum (A : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    HasSum (fun k : ℕ => (k.factorial : ℂ)⁻¹ * (A ^ k) i j) (NormedSpace.exp A i j) := by
  let ev : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] ℂ :=
    { toFun := fun B => B i j
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  exact (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) A).map
    ev.toContinuousLinearMap ev.toContinuousLinearMap.continuous

theorem complex_matrix_exp_upperTriangular (A : Matrix (Fin n) (Fin n) ℂ)
    (hA : A.IsUpperTriangular) : (NormedSpace.exp A).IsUpperTriangular := by
  intro i j hji
  have hs := entry_hasSum A i j
  have hz : (fun k : ℕ => (k.factorial : ℂ)⁻¹ * (A ^ k) i j) = fun _ => 0 := by
    funext k
    rw [(hA.pow k) hji, mul_zero]
  rw [hz] at hs
  exact hs.unique hasSum_zero

theorem complex_matrix_exp_diagonal (A : Matrix (Fin n) (Fin n) ℂ)
    (hA : A.IsUpperTriangular) (i : Fin n) :
    NormedSpace.exp A i i = Complex.exp (A i i) := by
  have hp (k : ℕ) : (A ^ k) i i = (A i i) ^ k := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, complex_triangular_mul_diag _ _ (hA.pow k) hA, ih, pow_succ]
  have hs := entry_hasSum A i i
  simp only [hp] at hs
  have ht : HasSum (fun k : ℕ => (k.factorial : ℂ)⁻¹ * (A i i) ^ k)
      (Complex.exp (A i i)) := by
    simpa only [smul_eq_mul, ← Complex.exp_eq_exp_ℂ] using
      NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) (A i i)
  exact hs.unique ht

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_ComplexWeightLift
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Simultaneous additive lifts of triangular matrix characters -/

noncomputable section
namespace PolycyclicRecognition

variable {G V : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [SimplyConnectedSpace G] [LocallyPathConnectedSpace G]
  [AddCommGroup V] [Module ℝ V] {n : ℕ}

/-- Simply connectedness lifts all diagonal characters, preserving the
specified linear weights on exponential curves. -/
theorem exists_lifted_complex_matrix_weights
    (ρ : G →* Matrix (Fin n) (Fin n) ℂ) (hρ : Continuous ρ)
    (hu : ∀ g, (ρ g).IsUpperTriangular)
    (d : V →ₗ[ℝ] (Fin n → ℂ)) (Exp : V → G)
    (hExp0 : Exp 0 = 1) (hcurve : ∀ x, Continuous (fun t : ℝ => Exp (t • x)))
    (he : ∀ x i, ρ (Exp x) i i = Complex.exp (d x i)) :
    ∃ π : G →* Multiplicative (Fin n → ℂ),
      Continuous (fun g => (π g).toAdd) ∧ ∀ x, (π (Exp x)).toAdd = d x := by
  let χ (i : Fin n) := (complexMatrixDiagonalHom ρ hu i).toHomUnits
  have hc (i : Fin n) : Continuous (fun g => (χ i g : ℂ)) :=
    (continuous_apply i).comp ((continuous_apply i).comp hρ)
  choose p hp heq using fun i => exists_additive_lift_complex_character (χ i) (hc i)
  have hex (i : Fin n) (x : V) : (p i (Exp x)).toAdd = d x i := by
    have h := additive_lift_complex_character_on_curve (χ i) (p i) (hp i) (heq i)
      (fun t : ℝ => Exp (t • x)) (hcurve x) (by simpa using hExp0) (d x i)
      (fun t => by
        change ρ (Exp (t • x)) i i = _
        rw [he, map_smul]
        rfl) 1
    simpa only [one_smul, Complex.ofReal_one, one_mul] using h
  let π : G →* Multiplicative (Fin n → ℂ) :=
    { toFun := fun g => Multiplicative.ofAdd (fun i => (p i g).toAdd)
      map_one' := by apply Multiplicative.ext; ext i; exact congrArg Multiplicative.toAdd (map_one (p i))
      map_mul' := by
        intro g h
        apply Multiplicative.ext
        ext i
        exact congrArg Multiplicative.toAdd (map_mul (p i) g h) }
  refine ⟨π, continuous_pi hp, fun x => ?_⟩
  funext i
  exact hex i x

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_ComplexAdjointGroup
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanRealShadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.ComplexTriangularAdjoint.cartanWeightSection_weight _root_.OAI.PolycyclicRecognition.ComplexTriangularAdjoint.complexWeightMap_one_tmul _root_.OAI.PolycyclicRecognition.ComplexTriangularAdjoint.weightImaginaryAction_annihilate _root_.OAI.PolycyclicRecognition.ComplexTriangularAdjoint.weightImaginaryAction_kernel _root_.OAI.PolycyclicRecognition.ComplexTriangularAdjoint.weightImaginaryAction_lie _root_.OAI.PolycyclicRecognition.derivationSemidirectHom_apply _root_.OAI.PolycyclicRecognition.exponentialHomOfDynkin_apply_exp _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.integrateNilpotentLieEquiv_apply_exp _root_.OAI.PolycyclicRecognition.modelNilradicalLinearAction_apply _root_.OAI.PolycyclicRecognition.modelNilradicalRotation_apply _root_.OAI.PolycyclicRecognition.modelNilradicalRotation_mul _root_.OAI.PolycyclicRecognition.modelNilradicalRotation_one _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.realShadowCartanHom_apply _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Additive complex adjoint weights on a simply connected solvable group -/

noncomputable section
namespace PolycyclicRecognition
open Module
open scoped Manifold TensorProduct Matrix.Norms.Operator

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace G] [ChartedSpace E G]
  [Group G] [LieGroup (𝓘(ℝ, E)) ⊤ G]
  [IsTopologicalGroup G] [PreconnectedSpace G] {m n : ℕ}

/-- The triangular infinitesimal adjoint action exponentiates to a
triangular group action, using only local exponential generation. -/
theorem complexAdjointMatrixHom_upper
    (b : Basis (Fin m) ℝ (GroupLieAlgebra (𝓘(ℝ, E)) G))
    (T : ComplexTriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, E)) G) n)
    {Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G} (hExp : IsGroupExponential Exp)
    (g : G) : (complexAdjointMatrixHom b T.basis g).IsUpperTriangular := by
  let ρ := complexAdjointMatrixHom b T.basis
  let S : Subgroup G :=
    { carrier := {g | (ρ g).IsUpperTriangular ∧ (ρ (g⁻¹)).IsUpperTriangular}
      one_mem' := by
        have hone : (1 : Matrix (Fin n) (Fin n) ℂ).IsUpperTriangular := by
          intro i j hji
          change j < i at hji
          simp only [Matrix.one_apply, ite_eq_right_iff]
          intro hij
          exact False.elim ((ne_of_gt hji) hij)
        change (ρ 1).IsUpperTriangular ∧ (ρ ((1 : G)⁻¹)).IsUpperTriangular
        simpa only [inv_one, map_one] using And.intro hone hone
      mul_mem' := by
        intro a b ha hb
        exact ⟨by simpa only [map_mul] using ha.1.mul hb.1,
          by simpa only [mul_inv_rev, map_mul] using hb.2.mul ha.2⟩
      inv_mem' := by intro g hg; exact ⟨hg.2, by simpa using hg.1⟩ }
  have he (x : GroupLieAlgebra (𝓘(ℝ, E)) G) :
      (ρ (Exp x)).IsUpperTriangular := by
    rw [complexAdjointMatrixHom_exp b T.basis hExp]
    exact complex_matrix_exp_upperTriangular _ (T.upper _)
  have hinv (x : GroupLieAlgebra (𝓘(ℝ, E)) G) :
      (ρ ((Exp x)⁻¹)).IsUpperTriangular :=
    (congrArg (fun g : G => (ρ g).IsUpperTriangular) (hExp.map_neg x)).mp (he (-x))
  have hS : S = ⊤ := by
    apply subgroup_eq_top_of_exponential_basis hExp (Module.finBasis ℝ E)
    intro i t
    constructor
    · exact he _
    · exact hinv _
  have hg : g ∈ S := by rw [hS]; trivial
  exact hg.1

theorem exists_additive_complex_adjoint_weights
    [SimplyConnectedSpace G] [LocallyPathConnectedSpace G]
    (b : Basis (Fin m) ℝ (GroupLieAlgebra (𝓘(ℝ, E)) G))
    (T : ComplexTriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, E)) G) n)
    {Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G} (hExp : IsGroupExponential Exp) :
    ∃ π : G →* Multiplicative (Fin n → ℂ), Continuous (fun g => (π g).toAdd) ∧
      ∀ x, (π (Exp x)).toAdd = T.weightMap x := by
  apply exists_lifted_complex_matrix_weights (complexAdjointMatrixHom b T.basis)
    (continuous_complexAdjointMatrixHom b T.basis)
    (complexAdjointMatrixHom_upper b T hExp) T.weightMap Exp hExp.map_zero
    (fun x => (hExp.contMDiff_curve x).continuous)
  intro x i
  rw [complexAdjointMatrixHom_exp b T.basis hExp]
  simp only [complexifiedAdjointMatrix_apply]
  rw [complex_matrix_exp_diagonal _ (T.upper _)]
  rfl

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_ComplexWeightRange
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Restricting lifted weights to their infinitesimal image -/

noncomputable section
namespace PolycyclicRecognition
open scoped Manifold

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace G] [ChartedSpace E G]
  [Group G] [LieGroup (𝓘(ℝ, E)) ⊤ G]
  [IsTopologicalGroup G] [PreconnectedSpace G] {n : ℕ}

/-- Exponential generation ensures the lifted character takes values in
the real linear image of its derivative. -/
theorem exists_range_restricted_complex_weights
    {Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G} (hExp : IsGroupExponential Exp)
    (d : E →ₗ[ℝ] (Fin n → ℂ)) (π : G →* Multiplicative (Fin n → ℂ))
    (hπ : Continuous (fun g => (π g).toAdd))
    (he : ∀ x, (π (Exp x)).toAdd = d x) :
    ∃ q : G →* Multiplicative d.range, Continuous (fun g => (q g).toAdd) ∧
      ∀ x, (q (Exp x)).toAdd = d.rangeRestrict x := by
  let S : Subgroup G :=
    { carrier := {g | (π g).toAdd ∈ d.range}
      one_mem' := by
        change (π 1).toAdd ∈ d.range
        rw [map_one]
        exact d.range.zero_mem
      mul_mem' := by
        intro g h hg hh
        change (π (g * h)).toAdd ∈ d.range
        rw [map_mul]
        exact d.range.add_mem hg hh
      inv_mem' := by
        intro g hg
        change (π g⁻¹).toAdd ∈ d.range
        rw [map_inv]
        exact d.range.neg_mem hg }
  have hex (x : GroupLieAlgebra (𝓘(ℝ, E)) G) : (π (Exp x)).toAdd ∈ d.range := by
    rw [he]
    exact LinearMap.mem_range_self d _
  have hS : S = ⊤ := by
    apply subgroup_eq_top_of_exponential_basis hExp (Module.finBasis ℝ E)
    intro i t
    exact hex _
  have hmem (g : G) : (π g).toAdd ∈ d.range := by
    change g ∈ S
    rw [hS]
    trivial
  let q : G →* Multiplicative d.range :=
    { toFun := fun g => Multiplicative.ofAdd ⟨(π g).toAdd, hmem g⟩
      map_one' := by apply Multiplicative.ext; apply Subtype.ext; exact congrArg Multiplicative.toAdd π.map_one
      map_mul' := by
        intro g h
        apply Multiplicative.ext
        apply Subtype.ext
        exact congrArg Multiplicative.toAdd (π.map_mul g h) }
  refine ⟨q, hπ.subtype_mk hmem, fun x => ?_⟩
  apply Subtype.ext
  exact he x

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_ComplexWeightKernel
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanRealShadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual closed kernel of the complex adjoint weights -/

noncomputable section
namespace PolycyclicRecognition

open Module
open scoped Manifold ContDiff

variable {E G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MetricSpace G] [ChartedSpace E G] [Group G]
  [LieGroup (𝓘(ℝ, E)) ⊤ G] [SimplyConnectedSpace G]
  {n : ℕ} (T : ComplexTriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, E)) G) n)
  (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G) (hExp : IsGroupExponential Exp)

include hExp in
/-- The nilpotent infinitesimal weight kernel integrates onto the full
kernel of a continuous character on the original group. -/
theorem exists_closed_complex_weight_kernel :
    ∃ π : G →* Multiplicative T.weightMap.range, Continuous π ∧
      (∀ x, (π (Exp x)).toAdd = T.weightMap.rangeRestrict x) ∧
      ∃ (N : NilpotentLieModel T.kernelIdeal)
        (ExpN : GroupLieAlgebra (𝓘(ℝ, N.modelSpace)) N.carrier → N.carrier),
        IsGroupExponential ExpN ∧
        ∃ ι : N.carrier →* G, Topology.IsClosedEmbedding ι ∧
          ContMDiff (𝓘(ℝ, N.modelSpace)) (𝓘(ℝ, E)) ∞ ι ∧
          (∀ x : T.kernelIdeal, ι (ExpN (N.equiv x)) = Exp x) ∧
          Set.range ι = (π.ker : Set G) := by
  let : IsTopologicalGroup G := topologicalGroup_of_lieGroup (𝓘(ℝ, E)) ⊤
  let : LocallyPathConnectedSpace G := ChartedSpace.locallyPathConnectedSpace E G
  obtain ⟨π₀, hπ₀, hπ₀Exp⟩ := exists_additive_complex_adjoint_weights (Module.finBasis ℝ E) T hExp
  obtain ⟨π, hπ, he⟩ := exists_range_restricted_complex_weights hExp T.weightMap π₀ hπ₀ hπ₀Exp
  have hπc : Continuous π := continuous_ofAdd.comp hπ
  refine ⟨π, hπc, he, ?_⟩
  apply exists_closed_nilpotent_linear_kernel T.kernelIdeal T.kernelIdeal_nilpotent
    T.weightMap.rangeRestrict T.weightMap.surjective_rangeRestrict _ Exp hExp π hπc he
  intro x
  constructor
  · intro hx
    exact congrArg Subtype.val hx
  · intro hx
    exact Subtype.ext hx

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_ComplexWeightFactorModel
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanRealShadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.CartanFactorModel.heightRay_zero _root_.OAI.PolycyclicRecognition.CartanFactorModel.realScaleProfile_apply _root_.OAI.PolycyclicRecognition.CartanFactorModel.sampledProbeProfile_apply _root_.OAI.PolycyclicRecognition.ComplexTriangularAdjoint.weightImaginaryAction_annihilate _root_.OAI.PolycyclicRecognition.ComplexTriangularAdjoint.weightImaginaryAction_kernel _root_.OAI.PolycyclicRecognition.ComplexTriangularAdjoint.weightImaginaryAction_lie _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.modelNilradicalLinearAction_apply _root_.OAI.PolycyclicRecognition.modelNilradicalRotation_apply _root_.OAI.PolycyclicRecognition.modelNilradicalRotation_mul _root_.OAI.PolycyclicRecognition.modelNilradicalRotation_one _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.realShadowCartanHom_apply _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Nilpotent and Cartan factors for a solvable group with complex weights -/

noncomputable section
namespace PolycyclicRecognition
open Set Filter
open scoped Manifold ContDiff Topology

variable {EG G : Type} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G]
  {a : ℕ} (T : ComplexTriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  (H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)) [H.IsCartanSubalgebra]
  (ExpG : GroupLieAlgebra (𝓘(ℝ, EG)) G → G)


include T in
theorem nonempty_complexWeightFactorModel (hExp : IsGroupExponential ExpG) :
    Nonempty (ComplexWeightFactorModel T H ExpG) := by
  let : IsTopologicalGroup G := topologicalGroup_of_lieGroup (𝓘(ℝ, EG)) ⊤
  obtain ⟨π, hπ, hπExp, N, ExpN, hExpN, ι, hι, hιsmooth, heι, hrι⟩ :=
    exists_closed_complex_weight_kernel T ExpG hExp
  obtain ⟨D⟩ := nilpotentPublishedInputs.existsModel H inferInstance
  let : IsTopologicalGroup N.carrier := topologicalGroup_of_lieGroup (𝓘(ℝ, N.modelSpace)) ⊤
  let : IsTopologicalGroup D.carrier := topologicalGroup_of_lieGroup (𝓘(ℝ, D.modelSpace)) ⊤
  let : LocallyCompactSpace N.carrier := ChartedSpace.locallyCompactSpace N.modelSpace N.carrier
  let : LocallyCompactSpace D.carrier := ChartedSpace.locallyCompactSpace D.modelSpace D.carrier
  obtain ⟨cN, hcN⟩ := ((nilpotentPublishedInputs.haar T.kernelIdeal N).2
    ExpN hExpN (N.tangent_nilpotent T.kernelIdeal_nilpotent)).1
  obtain ⟨ExpD, hExpD, cD, hcD⟩ := D.exists_exponential_chart inferInstance
    (nilpotentPublishedInputs.haar H D)
  let d := T.weightMap.rangeRestrict
  have hker (x : GroupLieAlgebra (𝓘(ℝ, EG)) G) : d x = 0 ↔ x ∈ T.kernelIdeal := by
    constructor
    · exact fun h => congrArg Subtype.val h
    · exact fun h => Subtype.ext h
  let jD := H.incl.comp D.equiv.symm.toLieHom
  have hjD : Function.Injective jD := Subtype.val_injective.comp D.equiv.symm.injective
  have hsurj : Function.Surjective (d.comp jD.toLinearMap) :=
    (T.cartan_weightRange_surjective H).comp D.equiv.symm.surjective
  obtain ⟨κ, hκ, hκsmooth, heκall⟩ := exists_closed_nilpotent_integration_over_linear_quotient
    T.kernelIdeal T.kernelIdeal_nilpotent d T.weightMap.surjective_rangeRestrict hker
    ExpG hExp π hπ hπExp H D inferInstance jD hjD hsurj
  have heκ (x : H) : κ (ExpD (D.equiv x)) = ExpG x := by
    simpa only [jD, LieHom.comp_apply, LieEquiv.coe_toLieHom, LieEquiv.symm_apply_apply,
      LieSubalgebra.coe_incl] using
      heκall ExpD hExpD (D.equiv x)
  have hiExp (x : N.modelSpace) : ι (ExpN x) = ExpG (T.kernelIdeal.incl (N.equiv.symm x)) := by
    exact (congrArg (fun y : GroupLieAlgebra (𝓘(ℝ, N.modelSpace)) N.carrier =>
      ι (ExpN y)) (N.equiv.apply_symm_apply x)).symm.trans (heι (N.equiv.symm x))
  have hkExp (x : D.modelSpace) : κ (ExpD x) = ExpG (H.incl (D.equiv.symm x)) := by
    exact (congrArg (fun y : GroupLieAlgebra (𝓘(ℝ, D.modelSpace)) D.carrier =>
      κ (ExpD y)) (D.equiv.apply_symm_apply x)).symm.trans (heκ (D.equiv.symm x))
  have hiRange : Set.range ι = ExpG '' (T.kernelIdeal : Set (GroupLieAlgebra (𝓘(ℝ, EG)) G)) := by
    ext g
    constructor
    · rintro ⟨n, rfl⟩
      obtain ⟨x, hx⟩ := cN.surjective n
      rw [hcN] at hx
      exact ⟨N.equiv.symm x, (N.equiv.symm x).property, (hiExp x).symm.trans (congrArg ι hx)⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨ExpN (N.equiv ⟨x, hx⟩), heι ⟨x, hx⟩⟩
  have hkRange : Set.range κ = ExpG '' (H : Set (GroupLieAlgebra (𝓘(ℝ, EG)) G)) := by
    ext g
    constructor
    · rintro ⟨d, rfl⟩
      obtain ⟨x, hx⟩ := cD.surjective d
      rw [hcD] at hx
      exact ⟨D.equiv.symm x, (D.equiv.symm x).property, (hkExp x).symm.trans (congrArg κ hx)⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨ExpD (D.equiv ⟨x, hx⟩), heκ ⟨x, hx⟩⟩
  have hnormal : ι.range.Normal := by
    have he : ι.range = π.ker := SetLike.coe_injective hrι
    rw [he]
    infer_instance
  let φ := conjugationLiftOfNormal ι κ hι.injective hnormal
  have hconj (d : D.carrier) (n : N.carrier) :
      ι (φ d n) = κ d * ι n * (κ d)⁻¹ :=
    conjugationLiftOfNormal_spec ι κ hι.injective hnormal d n
  have hiDiff := mfderiv_eq_of_exponential_compatibility hExpN hExp ι
    (hιsmooth.mdifferentiable (by simp))
    (T.kernelIdeal.incl.comp N.equiv.symm.toLieHom).toLinearMap hiExp
  have hkDiff := mfderiv_eq_of_exponential_compatibility hExpD hExp κ
    (hκsmooth.mdifferentiable (by simp)) jD.toLinearMap hkExp
  have hiVal (x : T.kernelIdeal) :
      (tangentSpaceCast (𝓘(ℝ, EG)) (ι 1) 1)
        (mfderiv (𝓘(ℝ, N.modelSpace)) (𝓘(ℝ, EG)) ι 1 (N.equiv x)) =
          (x : GroupLieAlgebra (𝓘(ℝ, EG)) G) := by
    change mfderiv (𝓘(ℝ, N.modelSpace)) (𝓘(ℝ, EG)) ι 1 (N.equiv x) =
      (x : GroupLieAlgebra (𝓘(ℝ, EG)) G)
    exact (hiDiff (N.equiv x)).trans
      (congrArg (fun z : T.kernelIdeal => (z : GroupLieAlgebra (𝓘(ℝ, EG)) G))
        (N.equiv.symm_apply_apply x))
  have hkVal (x : H) :
      (tangentSpaceCast (𝓘(ℝ, EG)) (κ 1) 1)
        (mfderiv (𝓘(ℝ, D.modelSpace)) (𝓘(ℝ, EG)) κ 1 (D.equiv x)) =
          (x : GroupLieAlgebra (𝓘(ℝ, EG)) G) := by
    change mfderiv (𝓘(ℝ, D.modelSpace)) (𝓘(ℝ, EG)) κ 1 (D.equiv x) =
      (x : GroupLieAlgebra (𝓘(ℝ, EG)) G)
    exact (hkDiff (D.equiv x)).trans
      (congrArg (fun z : H => (z : GroupLieAlgebra (𝓘(ℝ, EG)) G))
        (D.equiv.symm_apply_apply x))
  have hlocal : Filter.map (fun p : N.carrier × D.carrier => ι p.1 * κ p.2)
      (𝓝 (1 : N.carrier × D.carrier)) = 𝓝 (1 : G) := by
    apply factorProduct_map_nhds_one ι κ hιsmooth hκsmooth
    intro x
    obtain ⟨h, hh⟩ := T.exists_real_cartan_representative H x
    have hu : x - (h : GroupLieAlgebra (𝓘(ℝ, EG)) G) ∈ T.kernelIdeal := by
      change T.weightMap (x - (h : GroupLieAlgebra (𝓘(ℝ, EG)) G)) = 0
      rw [map_sub, hh, sub_self]
    refine ⟨N.equiv ⟨x - h, hu⟩, D.equiv h, ?_⟩
    rw [hiVal, hkVal]
    exact sub_add_cancel x h
  obtain ⟨hprod, hlifts⟩ := factorProduct_surjective_and_compact_lifts ι κ φ hconj hlocal
  have hexpinj {x y : GroupLieAlgebra (𝓘(ℝ, EG)) G} (hx : x ∈ T.kernelIdeal)
      (he : ExpG x = ExpG y) : x = y := by
    have hy : y ∈ T.kernelIdeal := by
      apply (hker y).mp
      rw [← hπExp, ← he, hπExp]
      exact (hker x).mpr hx
    have hn : ExpN (N.equiv ⟨x, hx⟩) = ExpN (N.equiv ⟨y, hy⟩) :=
      hι.injective ((heι ⟨x, hx⟩).trans (he.trans (heι ⟨y, hy⟩).symm))
    have hn' : N.equiv ⟨x, hx⟩ = N.equiv ⟨y, hy⟩ :=
      cN.injective (by simpa only [hcN] using hn)
    exact congrArg Subtype.val (N.equiv.injective hn')
  have hoverlap : Set.range ι ∩ Set.range κ = ExpG ''
      ((T.kernelIdeal : Set (GroupLieAlgebra (𝓘(ℝ, EG)) G)) ∩ H) := by
    rw [hiRange, hkRange]
    ext g
    constructor
    · rintro ⟨⟨x, hx, he⟩, ⟨y, hy, he'⟩⟩
      have hxy := hexpinj hx (he.trans he'.symm)
      exact ⟨x, ⟨hx, hxy ▸ hy⟩, he⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx.1, rfl⟩, ⟨x, hx.2, rfl⟩⟩
  exact ⟨{
    N := N, D := D, weightCharacter := π, continuousWeightCharacter := hπ,
    weightCharacter_exp := hπExp, ExpN := ExpN, ExpD := ExpD, isExpN := hExpN, isExpD := hExpD,
    inclusionN := ι, inclusionD := κ, action := φ, closedN := hι, closedD := hκ,
    compatibleN := heι, compatibleD := heκ, normalN := hnormal, conjugation := hconj,
    surjective := hprod, openProduct := isOpenMap_factorProduct_of_map_nhds_one ι κ hlocal,
    compactLifts := hlifts, overlap := hoverlap }⟩

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
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_SolvableGroupLieAlgebra
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.ComplexWeightFactorModel.smoothRotationExtensionTopologicalGroup _root_.OAI.PolycyclicRecognition.ComplexWeightFactorModel.smoothRotationalModificationTopologicalGroup _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The Lie algebra of an actual solvable Lie group

The intrinsic adjoint exponential puts the adjoint representation into the
infinitesimal action of a solvable matrix group. Its derived series vanishes;
one additional bracket kills the central kernel of the adjoint action.
-/

noncomputable section
namespace PolycyclicRecognition

open scoped Manifold
attribute [local instance 100] LieRing.ofAssociativeRing

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace G] [ChartedSpace E G]
  [Group G] [LieGroup (𝓘(ℝ, E)) ⊤ G] [T2Space G] [Group.IsSolvable G]

/-- Group solvability implies solvability of the intrinsic tangent Lie algebra. -/
theorem groupLieAlgebra_isSolvable :
    LieAlgebra.IsSolvable (GroupLieAlgebra (𝓘(ℝ, E)) G) := by
  let L := GroupLieAlgebra (𝓘(ℝ, E)) G
  let A := E →L[ℝ] E
  let ρ : G →* Aˣ := (conjugationDifferentialHom (E := E) (G := G)).toHomUnits
  let R := algebraGroupTangentLie ρ.range
  let : Group.IsSolvable ρ.range :=
    Group.isSolvable_of_surjective (f := ρ.rangeRestrict) ρ.rangeRestrict_surjective
  let : LieAlgebra.IsSolvable R := algebraGroupTangentLie_isSolvable ρ.range
  let j₀ : L →ₗ⁅ℝ⁆ A :=
    { toLinearMap :=
        { toFun := groupAdjointOperator
          map_add' := by
            intro x y
            ext z
            exact congrArg (fun w : L => (w : E)) (add_lie x y (show L from z))
          map_smul' := by
            intro r x
            ext z
            exact congrArg (fun w : L => (w : E)) (smul_lie r x (show L from z)) }
      map_lie' := by
        intro x y
        ext z
        exact congrArg (fun w : L => (w : E)) (lie_lie x y (show L from z)) }
  have hmem (v : L) : j₀ v ∈ R := by
    apply Submodule.subset_span
    let Exp := groupExponential (E := E) (G := G)
    have hExp : IsGroupExponential Exp := groupExponential_isGroupExponential
    refine ⟨fun t => ρ (Exp (t • v)), fun t => ⟨Exp (t • v), rfl⟩, ?_, ?_⟩
    · change ρ (Exp (0 • v)) = 1
      rw [zero_smul, hExp.map_zero, map_one]
    · have h := hasDerivAt_exp_smul_const (j₀ v) (0 : ℝ)
      simp only [zero_smul, NormedSpace.exp_zero, one_mul] at h
      convert h using 1
      all_goals try with_reducible_and_instances rfl
      funext t
      exact adjointLinearMap_exponential hExp v t
  let j : L →ₗ⁅ℝ⁆ R :=
    { toFun := fun x => ⟨j₀ x, hmem x⟩
      map_add' := fun x y => Subtype.ext (j₀.map_add x y)
      map_smul' := fun r x => Subtype.ext (j₀.map_smul r x)
      map_lie' := fun {x y} => Subtype.ext (j₀.map_lie x y) }
  obtain ⟨n, hn⟩ := LieAlgebra.IsSolvable.solvable ℝ R
  have hjzero (x : L) (hx : x ∈ LieAlgebra.derivedSeries ℝ L n) : j x = 0 := by
    have hm := LieIdeal.derivedSeries_map_le (f := j) n (LieIdeal.mem_map hx)
    rwa [hn] at hm
  apply (LieAlgebra.isSolvable_iff ℝ L).mpr
  refine ⟨n + 1, le_antisymm ?_ bot_le⟩
  have hz : (LieAlgebra.derivedSeries ℝ L (n + 1)).toSubmodule ≤ ⊥ := by
    rw [LieAlgebra.derivedSeries_def, LieAlgebra.derivedSeriesOfIdeal_succ,
      LieSubmodule.lieIdeal_oper_eq_linear_span']
    apply Submodule.span_le.mpr
    rintro _ ⟨x, hx, y, _, rfl⟩
    change ⁅x, y⁆ = 0
    have hzero : j₀ x = 0 := congrArg Subtype.val (hjzero x hx)
    exact congrArg (fun f : A => f y) hzero
  exact hz

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_CornulierTesseraConstruction
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_countable _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_nonempty _root_.OAI.PolycyclicRecognition.finitelyGeneratedSubgroupIndex_countable _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Constructing the Cornulier–Tessera comparison

The original group and its real rotational modification both embed properly
and cocompactly in the same compact semidirect extension. The modification's
analytic chart and closed triangular realization have been constructed above.
-/

noncomputable section
namespace PolycyclicRecognition
open scoped Manifold
attribute [local instance] semidirectProductTopology

theorem cornulierTesseraModelInput_oai : CornulierTesseraModelInput := by
  intro S
  obtain ⟨d⟩ := S.nonempty_properChainMetric geodesicMetricExistenceInput
  let metric : MetricSpace S.carrier := d.compatibleMetric
  let L := GroupLieAlgebra (𝓘(ℝ,S.modelSpace)) S.carrier
  let solv : LieAlgebra.IsSolvable L :=
    groupLieAlgebra_isSolvable (E := S.modelSpace) (G := S.carrier)
  obtain ⟨n,b,hb⟩ := exists_complex_triangular_adjoint_basis L
  let T : ComplexTriangularAdjoint L n := ⟨b,hb⟩
  obtain ⟨x,hx⟩ := LieAlgebra.exists_isCartanSubalgebra_engel ℝ L
  let H := LieSubalgebra.engel ℝ x
  let cartan : H.IsCartanSubalgebra := hx
  let Exp := groupExponential (E := S.modelSpace) (G := S.carrier)
  have hExp : IsGroupExponential Exp := groupExponential_isGroupExponential
  obtain ⟨F⟩ := nonempty_complexWeightFactorModel T H Exp hExp
  obtain ⟨R,hR,hf⟩ := F.exists_triangulable_rotation_model hExp
  let S₁ := S.toLCModel
  let S₂ := compactSemidirectLCModel S₁ (realRotationTorus L H)
    (F.factorCompactRotationAction hExp) (F.continuous_factorCompactRotationAction hExp)
  exact ⟨R,hR,S₁,S₂,⟨ProperCocompactHom.id S.carrier⟩,
    ⟨F.originalToSmoothRotationExtension hExp⟩,hf⟩

end PolycyclicRecognition

end

end OAI
end

theorem solution : type_of% @OAI.PolycyclicRecognition.cornulierTesseraModelInput_oai := @OAI.PolycyclicRecognition.cornulierTesseraModelInput_oai
