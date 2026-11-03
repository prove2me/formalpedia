-- Prove2me | solution 1 for OAI.PolycyclicRecognition.intrinsic_exponential_contMDiff
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-03T00:34:17.439775+00:00
-- url     : https://prove2.me/submissions/93942d2e-9bd4-48d8-8c91-017577fd3280

import Mathlib
import Definitions.Def_PolycyclicRecognition
import Definitions.Def_OAIQ093D022

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
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_BoundedWordAlgebra
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite algebras from a bound on generator products

This is the finite-dimensionality step for the truncated enveloping algebra
used to extend a nilpotent representation by derivations.
-/

noncomputable section
namespace PolycyclicRecognition

open Set

variable {R A : Type*} [Field R] [Ring A] [Algebra R A]
  {ι : Type*} [Fintype ι] (j : ι → A) (c : ℕ)

theorem boundedWordProducts_finite : (boundedWordProducts j c).Finite :=
  Set.finite_range _

omit [Fintype ι] in
theorem list_prod_mem_boundedWordSpan
    (hnil : ∀ l : List ι, c < l.length → (l.map j).prod = 0) (l : List ι) :
    (l.map j).prod ∈ Submodule.span R (boundedWordProducts j c) := by
  by_cases hl : l.length ≤ c
  · apply Submodule.subset_span
    refine ⟨⟨⟨l.length, Nat.lt_succ_of_le hl⟩, l.get⟩, ?_⟩
    change (List.ofFn (j ∘ l.get)).prod = _
    rw [← List.map_ofFn, List.ofFn_get]
  · rw [hnil l (Nat.lt_of_not_ge hl)]
    exact Submodule.zero_mem _

omit [Fintype ι] in
theorem adjoin_le_boundedWordSpan
    (hnil : ∀ l : List ι, c < l.length → (l.map j).prod = 0) :
    (Algebra.adjoin R (Set.range j)).toSubmodule ≤
      Submodule.span R (boundedWordProducts j c) := by
  rw [Algebra.adjoin_eq_span]
  apply Submodule.span_le.mpr
  intro x hx
  have hword : ∃ l : List ι, (l.map j).prod = x := by
    induction hx using Submonoid.closure_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      exact ⟨[i], by simp⟩
    | one => exact ⟨[], by simp⟩
    | mul x y _ _ hx hy =>
      obtain ⟨l, rfl⟩ := hx
      obtain ⟨k, rfl⟩ := hy
      exact ⟨l ++ k, by simp⟩
  obtain ⟨l, rfl⟩ := hword
  exact list_prod_mem_boundedWordSpan j c hnil l

theorem finiteDimensional_of_bounded_generator_products
    (hgen : Algebra.adjoin R (Set.range j) = ⊤)
    (hnil : ∀ l : List ι, c < l.length → (l.map j).prod = 0) :
    FiniteDimensional R A := by
  have hspan : Submodule.span R (boundedWordProducts j c) = ⊤ := by
    apply top_unique
    have h := adjoin_le_boundedWordSpan (R := R) j c hnil
    rw [hgen] at h
    exact h
  apply Module.Finite.of_fg_top
  rw [← hspan]
  exact Submodule.fg_span (boundedWordProducts_finite j c)

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
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_SmoothAutonomousCurve
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Smoothness bootstrapping for autonomous integral curves

Only the differential equation and smoothness of its vector field are used.
This is the local analytic step needed for smooth Lie exponential curves.
-/

noncomputable section
namespace PolycyclicRecognition

open Set Filter
open scoped Topology ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem contDiff_of_autonomous_curve {F : E → E} {γ : ℝ → E}
    (hF : ContDiff ℝ ∞ F) (hγ : ∀ t, HasDerivAt γ (F (γ t)) t) :
    ContDiff ℝ ∞ γ := by
  apply contDiff_iff_contDiffAt.2
  intro t
  exact contDiffAt_of_autonomous_curve hF.contDiffAt (Eventually.of_forall hγ)

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

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
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
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_ContinuousOneParameter
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Continuous one-parameter subgroups are differentiable

An integral of the curve over a sufficiently short interval is invertible.
The subgroup identity then expresses the curve using a differentiable
primitive and multiplication by that fixed inverse.
-/

noncomputable section
namespace PolycyclicRecognition

open MeasureTheory Set Filter
open scoped Topology ContDiff

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

theorem exists_isUnit_intervalIntegral {f : ℝ → A}
    (hf : Continuous f) (hf0 : f 0 = 1) :
    ∃ a : ℝ, a ≠ 0 ∧ IsUnit (∫ s in 0..a, f s) := by
  let J : ℝ → A := fun a => ∫ s in 0..a, f s
  have hd : HasDerivAt J 1 0 := by
    simpa only [hf0] using intervalIntegral.integral_hasDerivAt_right
      (hf.intervalIntegrable 0 0) hf.aestronglyMeasurable.stronglyMeasurableAtFilter
      hf.continuousAt
  have ht : Tendsto (fun a => a⁻¹ • J a) (𝓝[≠] 0) (𝓝 (1 : A)) := by
    simpa only [zero_add, J, intervalIntegral.integral_same, sub_zero] using hd.tendsto_slope_zero
  have hu : ∀ᶠ a in 𝓝[≠] 0, IsUnit (a⁻¹ • J a) :=
    ht.eventually (Units.isOpen.mem_nhds isUnit_one)
  obtain ⟨a, hua, ha⟩ := (hu.and self_mem_nhdsWithin).exists
  have ha0 : a ≠ 0 := ha
  have hscalar : IsUnit (algebraMap ℝ A a) :=
    (isUnit_iff_ne_zero.mpr ha0).map (algebraMap ℝ A)
  refine ⟨a, ha0, ?_⟩
  simpa only [← Algebra.smul_def, smul_smul, mul_inv_cancel₀ ha0, one_smul] using
    hscalar.mul hua

theorem continuous_oneParameter_hasDerivAt_zero {f : ℝ → A}
    (hf : Continuous f) (hf0 : f 0 = 1)
    (hadd : ∀ s t, f (s + t) = f s * f t) :
    ∃ v : A, HasDerivAt f v 0 := by
  obtain ⟨a, _, u, hu⟩ := exists_isUnit_intervalIntegral hf hf0
  let J : ℝ → A := fun t => ∫ s in 0..t, f s
  have hJ (t : ℝ) : HasDerivAt J (f t) t :=
    intervalIntegral.integral_hasDerivAt_right (hf.intervalIntegrable 0 t)
      hf.aestronglyMeasurable.stronglyMeasurableAtFilter hf.continuousAt
  have hid (t : ℝ) : J (t + a) - J t = f t * (u : A) := by
    rw [hu]
    dsimp [J]
    rw [intervalIntegral.integral_interval_sub_left
      (hf.intervalIntegrable 0 (t + a)) (hf.intervalIntegrable 0 t)]
    have htrans := intervalIntegral.integral_comp_add_left (f := f) (a := 0) (b := a) t
    rw [add_zero] at htrans
    rw [← htrans]
    simpa only [hadd, ContinuousLinearMap.mul_apply'] using
      (ContinuousLinearMap.mul ℝ A (f t)).intervalIntegral_comp_comm (hf.intervalIntegrable 0 a)
  have heq : (fun t => (J (t + a) - J t) * (↑u⁻¹ : A)) = f := by
    funext t
    rw [hid, mul_assoc, u.mul_inv, mul_one]
  have hshift : HasDerivAt (fun t : ℝ => J (t + a)) (f a) 0 := by
    have hJa : HasDerivAt J (f a) (0 + a) := by simpa only [zero_add] using hJ a
    simpa only [one_smul, Function.comp_def] using hJa.scomp (h := fun t : ℝ => t + a) 0
      ((hasDerivAt_id 0).add_const a)
  have hd := (hshift.sub (hJ 0)).mul_const (↑u⁻¹ : A)
  change HasDerivAt (fun t => (J (t + a) - J t) * (↑u⁻¹ : A)) _ 0 at hd
  rw [heq] at hd
  exact ⟨_, hd⟩

theorem contDiff_continuous_oneParameter {f : ℝ → A}
    (hf : Continuous f) (hf0 : f 0 = 1)
    (hadd : ∀ s t, f (s + t) = f s * f t) :
    ContDiff ℝ ∞ f := by
  obtain ⟨v, hv⟩ := continuous_oneParameter_hasDerivAt_zero hf hf0 hadd
  exact contDiff_of_autonomous_curve (ContinuousLinearMap.mul ℝ A v).contDiff
    (oneParameter_hasDerivAt hadd hv)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_AutomaticSmoothAlgebraHom
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Automatic smoothness of continuous homomorphisms into algebra units

Products of one-parameter subgroups supply coordinates of the second kind.
The integral argument for continuous algebra-valued one-parameter groups
then proves smoothness in those coordinates.
-/

noncomputable section
namespace PolycyclicRecognition

open Function
open scoped Manifold ContDiff

variable {E G A : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace G] [ChartedSpace E G] [Group G] [LieGroup (𝓘(ℝ, E)) ⊤ G]
  [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

theorem contDiff_comp_exponentialProduct
    {Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G} (hExp : IsGroupExponential Exp)
    (ρ : G →* Aˣ) (hρ : Continuous (fun g => (ρ g : A)))
    {n : ℕ} (v : Fin n → E) :
    ContDiff ℝ ∞ (fun x => (ρ (exponentialProduct Exp v x) : A)) := by
  induction n with
  | zero =>
    simpa only [exponentialProduct, map_one, Units.val_one] using
      (contDiff_const : ContDiff ℝ ∞ (fun _ : Fin 0 → ℝ => (1 : A)))
  | succ n ih =>
    have hc : ContDiff ℝ ∞ (fun t : ℝ => (ρ (Exp (t • v 0)) : A)) := by
      apply contDiff_continuous_oneParameter
      · exact hρ.comp (hExp.contMDiff_curve (v 0)).continuous
      · rw [zero_smul]
        have hz : Exp (0 : E) = 1 := hExp.map_zero
        rw [hz, map_one, Units.val_one]
      · intro s t
        have heq : Exp ((s + t) • v 0) = Exp (s • v 0) * Exp (t • v 0) :=
          hExp.map_add_smul (v 0) s t
        rw [heq, map_mul, Units.val_mul]
    have hh := hc.comp (ContinuousLinearMap.proj (0 : Fin (n + 1)) :
      (Fin (n + 1) → ℝ) →L[ℝ] ℝ).contDiff
    have ht := (ih (v ∘ Fin.succ)).comp (coordinateTail n).contDiff
    have hp := hh.mul ht
    change ContDiff ℝ ∞ (fun x : Fin (n + 1) → ℝ =>
      (ρ (Exp (x 0 • v 0)) : A) *
        (ρ (exponentialProduct Exp (v ∘ Fin.succ) (x ∘ Fin.succ)) : A)) at hp
    simpa only [exponentialProduct, map_mul, Units.val_mul] using hp

theorem contMDiffAt_one_of_continuous_unitsHom [FiniteDimensional ℝ E]
    {Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G} (hExp : IsGroupExponential Exp)
    (ρ : G →* Aˣ) (hρ : Continuous (fun g => (ρ g : A))) :
    ContMDiffAt (𝓘(ℝ, E)) (𝓘(ℝ, A)) ∞ (fun g => (ρ g : A)) 1 := by
  let b := Module.finBasis ℝ E
  let d := b.equivFun.toContinuousLinearEquiv.symm
  have hcomb : tangentCombination b = d.toContinuousLinearMap := by
    ext x
    simp only [tangentCombination_apply]
    exact (b.equivFun_symm_apply x).symm
  have hd : HasMFDerivAt (𝓘(ℝ, Fin (Module.finrank ℝ E) → ℝ)) (𝓘(ℝ, E))
      (exponentialProduct Exp b) 0 d.toContinuousLinearMap := by
    apply (hExp.hasMFDerivAt_exponentialProduct_zero b).congr_mfderiv
    exact hcomb
  have hh := contMDiffAt_of_local_parameterization (f := fun g => (ρ g : A))
    (hExp.contMDiff_exponentialProduct b).contMDiffAt hd
    (contDiff_comp_exponentialProduct hExp ρ hρ b).contDiffAt
  simpa only [hExp.exponentialProduct_zero] using hh

theorem contMDiff_of_continuous_unitsHom [FiniteDimensional ℝ E]
    {Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G} (hExp : IsGroupExponential Exp)
    (ρ : G →* Aˣ) (hρ : Continuous (fun g => (ρ g : A))) :
    ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, A)) ∞ (fun g => (ρ g : A)) := by
  have hbase := contMDiffAt_one_of_continuous_unitsHom hExp ρ hρ
  intro g
  have hl : ContMDiffAt (𝓘(ℝ, E)) (𝓘(ℝ, E)) ∞ (fun x : G => g⁻¹ * x) g :=
    (contMDiff_mul_left (I := 𝓘(ℝ, E)) (a := g⁻¹) :
      ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) ∞ (fun x : G => g⁻¹ * x)).contMDiffAt
  have hm := hbase.comp_of_eq hl (inv_mul_cancel g)
  have hh := (ContinuousLinearMap.mul ℝ A (ρ g : A)).contDiff.contMDiff.contMDiffAt.comp g hm
  have heq : (fun x => (ρ g : A) * (ρ (g⁻¹ * x) : A)) = fun x => (ρ x : A) := by
    funext x
    rw [← Units.val_mul, ← map_mul, mul_inv_cancel_left]
  change ContMDiffAt (𝓘(ℝ, E)) (𝓘(ℝ, A)) ∞
    (fun x => (ρ g : A) * (ρ (g⁻¹ * x) : A)) g at hh
  rwa [heq] at hh

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_NilpotentPolynomialRepresentation
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.abelianRealCoordinates _root_.OAI.PolycyclicRecognition.abelianRealFiniteDimensional _root_.OAI.PolycyclicRecognition.abelianRealLieAbelian _root_.OAI.PolycyclicRecognition.abelianRealNormedLie _root_.OAI.PolycyclicRecognition.derivationLieSpaceFiniteDimensional _root_.OAI.PolycyclicRecognition.derivationLieSpaceRealNormed _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.polynomialLieIdealSubgroup_normal _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Nilpotence of the faithful polynomial representation

The representation is polynomial on every straight one-parameter subgroup.
The actual Lie differential therefore consists of nilpotent matrices.
-/

noncomputable section
namespace PolycyclicRecognition

open scoped Matrix.Norms.Operator
attribute [local instance 100] LieRing.ofAssociativeRing

variable {L : Type*} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  [P : PolynomialExponentialCoordinates L] {n m : ℕ}
  (b : Module.Basis (Fin n) ℝ L)
  (B : (Fin m → ℝ) ≃ₗ[ℝ] coordinateOrbitSpan (polynomialModelCoordinate b))

include b in
theorem exists_faithful_nilpotent_matrixLieRepresentation :
    ∃ (m : ℕ) (j : L →ₗ⁅ℝ⁆ Matrix (Fin m) (Fin m) ℝ),
      Function.Injective j ∧ ∀ x, IsNilpotent (j x) := by
  let := finiteDimensional_polynomialModelOrbit b
  let m := Module.finrank ℝ (coordinateOrbitSpan (polynomialModelCoordinate b))
  let B : (Fin m → ℝ) ≃ₗ[ℝ] coordinateOrbitSpan (polynomialModelCoordinate b) :=
    (Module.finBasis ℝ (coordinateOrbitSpan (polynomialModelCoordinate b))).equivFun.symm
  exact ⟨m, polynomialMatrixLieRepresentation b B,
    polynomialMatrixLieRepresentation_injective b B,
    polynomialMatrixLieRepresentation_nilpotent b B⟩

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_NilpotentFaithfulRepresentation
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.abelianRealCoordinates _root_.OAI.PolycyclicRecognition.abelianRealFiniteDimensional _root_.OAI.PolycyclicRecognition.abelianRealLieAbelian _root_.OAI.PolycyclicRecognition.abelianRealNormedLie _root_.OAI.PolycyclicRecognition.derivationLieSpaceFiniteDimensional _root_.OAI.PolycyclicRecognition.derivationLieSpaceRealNormed _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.polynomialLieIdealSubgroup_normal _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A faithful nilpotent matrix representation of a real nilpotent algebra

The coordinate model and its regular representation have both been constructed
without a published-input hypothesis. Engel gives a uniform product bound.
-/

noncomputable section
namespace PolycyclicRecognition

attribute [local instance 100] LieRing.ofAssociativeRing

theorem exists_faithful_nilpotent_representation (L : Type) [RealNormedLieAlgebra L]
    [FiniteDimensional ℝ L] (hnil : LieRing.IsNilpotent L) :
    ∃ (m c : ℕ) (j : L →ₗ⁅ℝ⁆ Matrix (Fin m) (Fin m) ℝ),
      Function.Injective j ∧ (∀ x, IsNilpotent (j x)) ∧
      ∀ l : List L, c ≤ l.length → (l.map j).prod = 0 := by
  obtain ⟨P⟩ := polynomialExponentialCoordinates_nilpotent L hnil
  let := P
  obtain ⟨m, j, hj, hn⟩ := exists_faithful_nilpotent_matrixLieRepresentation (Module.finBasis ℝ L)
  obtain ⟨c, hc⟩ := exists_vanishing_matrix_products_of_pointwise_nilpotent j hn
  exact ⟨m, c, j, hj, hn, hc⟩

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_TruncatedEnvelopingAlgebra
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The finite truncated enveloping algebra and its faithful generators

A given nilpotent representation bounds the truncation degree and certifies
injectivity. No PBW theorem or additional representation input is assumed.
-/

noncomputable section
namespace PolycyclicRecognition

open Module

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]

attribute [local instance 100] LieRing.ofAssociativeRing

local notation "U" => UniversalEnvelopingAlgebra R L
local notation "η" => UniversalEnvelopingAlgebra.ι R (L := L)

theorem truncatedEnvelopingProjection_eq_zero (c : ℕ) (u : U) :
    truncatedEnvelopingProjection c u = 0 ↔ u ∈ envelopingTruncationIdeal (R := R) c :=
  RingCon.eq _

theorem truncatedEnvelopingGenerator_prod_eq_zero (c : ℕ) (l : List L)
    (hl : c ≤ l.length) : (l.map (truncatedEnvelopingGenerator (R := R) c)).prod = 0 := by
  have h := (truncatedEnvelopingProjection_eq_zero c _).mpr
    (longWord_mem_envelopingTruncationIdeal (R := R) c l hl)
  simpa only [map_list_prod, List.map_map, Function.comp_def,
    truncatedEnvelopingGenerator, LieHom.coe_comp, AlgHom.coe_toLieHom] using h

theorem truncatedEnveloping_adjoin_basis {ι : Type*} [Fintype ι]
    (b : Basis ι R L) (c : ℕ) :
    Algebra.adjoin R (Set.range fun i => truncatedEnvelopingGenerator (R := R) c (b i)) = ⊤ := by
  classical
  let S := Algebra.adjoin R
    (Set.range fun i => truncatedEnvelopingGenerator (R := R) c (b i))
  have hgen (x : L) : truncatedEnvelopingGenerator (R := R) c x ∈ S := by
    rw [← b.sum_repr x]
    simp only [map_sum, map_smul]
    apply S.sum_mem
    intro i _
    apply S.smul_mem
    exact Algebra.subset_adjoin (s := Set.range fun i =>
      truncatedEnvelopingGenerator (R := R) c (b i)) ⟨i, rfl⟩
  apply top_unique
  intro z hz
  clear hz
  obtain ⟨u, rfl⟩ := truncatedEnvelopingProjection_surjective (R := R) (L := L) c z
  induction u using enveloping_induction with
  | hscalar r => exact S.algebraMap_mem r
  | hgen x => exact hgen x
  | hadd a b ha hb => exact S.add_mem ha hb
  | hmul a b ha hb => exact S.mul_mem ha hb

theorem truncatedEnvelopingGenerator_injective {A : Type*} [Ring A] [Algebra R A]
    (c : ℕ) (j : L →ₗ⁅R⁆ A) (hj : Function.Injective j)
    (hnil : ∀ l : List L, c ≤ l.length → (l.map j).prod = 0) :
    Function.Injective (truncatedEnvelopingGenerator (R := R) (L := L) c) := by
  let f : U →ₐ[R] A := UniversalEnvelopingAlgebra.lift R j
  have hk {u : U} (hu : u ∈ envelopingTruncationIdeal (R := R) c) : f u = 0 := by
    induction hu using TwoSidedIdeal.span_induction with
    | mem u hu =>
      obtain ⟨l, hl, rfl⟩ := hu
      dsimp only [f]
      simpa only [map_list_prod, List.map_map, Function.comp_def,
        UniversalEnvelopingAlgebra.lift_ι_apply] using hnil l hl
    | zero => exact map_zero f
    | add a b _ _ ha hb => rw [map_add, ha, hb, add_zero]
    | neg a _ ha => rw [map_neg, ha, neg_zero]
    | left_absorb a b _ hb => rw [map_mul, hb, mul_zero]
    | right_absorb b a _ ha => rw [map_mul, ha, zero_mul]
  intro x y hxy
  apply hj
  have hrel : (envelopingTruncationIdeal (R := R) c).ringCon (η x) (η y) :=
    (RingCon.eq _).mp hxy
  have hz := hk (((envelopingTruncationIdeal (R := R) c).rel_iff _ _).mp hrel)
  simpa only [map_sub, f, UniversalEnvelopingAlgebra.lift_ι_apply, sub_eq_zero] using hz

section FiniteDimensional
variable {K : Type*} [Field K] [LieAlgebra K L]

theorem finiteDimensional_truncatedEnvelopingAlgebra {ι : Type*} [Fintype ι]
    (b : Basis ι K L) (c : ℕ) : FiniteDimensional K (TruncatedEnvelopingAlgebra K L c) := by
  apply finiteDimensional_of_bounded_generator_products
    (fun i => truncatedEnvelopingGenerator (R := K) c (b i)) c
    (truncatedEnveloping_adjoin_basis b c)
  intro l hl
  have h := truncatedEnvelopingGenerator_prod_eq_zero (R := K) c (l.map b)
    (by simpa only [List.length_map] using hl.le)
  simpa only [List.map_map, Function.comp_def] using h

end FiniteDimensional
end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_TruncatedSemidirectRepresentation
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Representing a semidirect extension on the truncated enveloping algebra -/

noncomputable section
namespace PolycyclicRecognition

open LieAlgebra

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]

attribute [local instance 100] LieRing.ofAssociativeRing

local notation "Q" => TruncatedEnvelopingAlgebra R L

variable {H : Type*} [LieRing H] [LieAlgebra R H]

theorem truncatedSemidirectRepresentation_injective (c : ℕ)
    (ψ : H →ₗ⁅R⁆ LieDerivation R L L) (hψ : Function.Injective ψ)
    (hgen : Function.Injective (truncatedEnvelopingGenerator (R := R) (L := L) c)) :
    Function.Injective (truncatedSemidirectRepresentation c ψ) := by
  intro p q hpq
  have hl : p.left = q.left := by
    apply hgen
    have h := DFunLike.congr_fun hpq 1
    change truncatedEnvelopingGenerator c p.left * 1 +
      truncatedEnvelopingDerivation c (ψ p.right) 1 =
      truncatedEnvelopingGenerator c q.left * 1 +
      truncatedEnvelopingDerivation c (ψ q.right) 1 at h
    simpa only [mul_one, truncatedEnvelopingDerivation_one, add_zero] using h
  have hd : truncatedEnvelopingDerivation c (ψ p.right) =
      truncatedEnvelopingDerivation c (ψ q.right) := by
    change truncatedLeftRepresentation (R := R) c p.left +
      truncatedEnvelopingDerivation c (ψ p.right) =
      truncatedLeftRepresentation (R := R) c q.left +
      truncatedEnvelopingDerivation c (ψ q.right) at hpq
    rw [hl] at hpq
    exact add_left_cancel hpq
  have hr : p.right = q.right := by
    apply hψ
    apply LieDerivation.ext
    intro x
    apply hgen
    have h := DFunLike.congr_fun hd (truncatedEnvelopingGenerator c x)
    simpa only [truncatedEnvelopingDerivation_generator] using h
  exact SemiDirectSum.ext hl hr

theorem truncatedLeftRepresentation_nilpotent (c : ℕ) (x : L) :
    IsNilpotent (truncatedLeftRepresentation (R := R) c x) := by
  have hq : (truncatedEnvelopingGenerator (R := R) c x) ^ c = 0 := by
    simpa only [List.map_replicate, List.prod_replicate] using
      truncatedEnvelopingGenerator_prod_eq_zero (R := R) c (List.replicate c x)
        (by simp only [List.length_replicate, le_refl])
  refine ⟨c, ?_⟩
  change (Algebra.lmul R (Q c) (truncatedEnvelopingGenerator c x)) ^ c = 0
  rw [← map_pow, hq, map_zero]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_FaithfulTruncatedEnveloping
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.abelianRealFiniteDimensional _root_.OAI.PolycyclicRecognition.abelianRealLieAbelian _root_.OAI.PolycyclicRecognition.abelianRealNormedLie _root_.OAI.PolycyclicRecognition.derivationLieSpaceFiniteDimensional _root_.OAI.PolycyclicRecognition.derivationLieSpaceRealNormed _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.polynomialLieIdealSubgroup_normal _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A faithful nilpotent representation compatible with derivations

A faithful nilpotent representation determines a truncation degree.
The resulting finite representation carries the full derivation action,
as required for a solvable extension.
-/

noncomputable section
namespace PolycyclicRecognition

open Module

theorem exists_faithful_truncated_enveloping (L : Type) [RealNormedLieAlgebra L]
    [FiniteDimensional ℝ L] (hnil : LieRing.IsNilpotent L) :
    ∃ c : ℕ, FiniteDimensional ℝ (TruncatedEnvelopingAlgebra ℝ L c) ∧
      Function.Injective (truncatedEnvelopingGenerator (R := ℝ) (L := L) c) := by
  obtain ⟨m, c, j, hj, _, hc⟩ := exists_faithful_nilpotent_representation L hnil
  exact ⟨c, finiteDimensional_truncatedEnvelopingAlgebra (finBasis ℝ L) c,
    truncatedEnvelopingGenerator_injective c j hj hc⟩

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_FilteredPolynomialPerturbation
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial annihilators under a filtration-raising perturbation

If `D` preserves a finite descending filtration and `N` raises its level,
then a polynomial annihilating `D`, evaluated at `D + N`, raises its level.
Consequently a power of that polynomial annihilates `D + N`.
-/

noncomputable section
namespace PolycyclicRecognition

open Polynomial

variable {V : Type*} [AddCommGroup V] [Module ℝ V]
  (B : ℕ → Submodule ℝ V) (D N : Module.End ℝ V)
  (hB : Antitone B)
  (hD : ∀ k v, v ∈ B k → D v ∈ B k)
  (hN : ∀ k v, v ∈ B k → N v ∈ B (k + 1))

include hB hD hN

theorem filtered_sum_maps (k : ℕ) (v : V) (hv : v ∈ B k) : (D + N) v ∈ B k := by
  exact (B k).add_mem (hD k v hv) (hB (Nat.le_succ k) (hN k v hv))

theorem filtered_sum_pow_maps (a k : ℕ) (v : V) (hv : v ∈ B k) :
    ((D + N) ^ a) v ∈ B k := by
  induction a with
  | zero => simpa only [pow_zero, Module.End.one_apply] using hv
  | succ a ha =>
    rw [pow_succ', Module.End.mul_apply]
    exact filtered_sum_maps B D N hB hD hN k _ ha

theorem filtered_pow_difference (a k : ℕ) (v : V) (hv : v ∈ B k) :
    ((D + N) ^ a) v - (D ^ a) v ∈ B (k + 1) := by
  induction a with
  | zero => simpa only [pow_zero, sub_self] using (B (k + 1)).zero_mem
  | succ a ha =>
    rw [pow_succ', pow_succ', Module.End.mul_apply, Module.End.mul_apply,
      LinearMap.add_apply]
    have heq : D (((D + N) ^ a) v) + N (((D + N) ^ a) v) - D ((D ^ a) v) =
        D (((D + N) ^ a) v - (D ^ a) v) + N (((D + N) ^ a) v) := by
      rw [map_sub]
      abel
    rw [heq]
    exact (B (k + 1)).add_mem (hD _ _ ha)
      (hN _ _ (filtered_sum_pow_maps B D N hB hD hN a k v hv))

theorem filtered_polynomial_difference (p : ℝ[X]) (k : ℕ) (v : V) (hv : v ∈ B k) :
    aeval (D + N) p v - aeval D p v ∈ B (k + 1) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    simp only [map_add, LinearMap.add_apply]
    have heq : aeval (D + N) p v + aeval (D + N) q v -
        (aeval D p v + aeval D q v) =
        (aeval (D + N) p v - aeval D p v) + (aeval (D + N) q v - aeval D q v) := by abel
    rw [heq]
    exact (B (k + 1)).add_mem hp hq
  | monomial a r =>
    simp only [aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply]
    rw [← smul_sub]
    exact (B (k + 1)).smul_mem r (filtered_pow_difference B D N hB hD hN a k v hv)

theorem filtered_polynomial_annihilator (c : ℕ) (hzero : B 0 = ⊤) (hc : B c = ⊥)
    (p : ℝ[X]) (hp : aeval D p = 0) : aeval (D + N) (p ^ c) = 0 := by
  have hraise (k : ℕ) (v : V) (hv : v ∈ B k) : aeval (D + N) p v ∈ B (k + 1) := by
    simpa only [hp, LinearMap.zero_apply, sub_zero] using
      filtered_polynomial_difference B D N hB hD hN p k v hv
  have hpow (k : ℕ) (v : V) : ((aeval (D + N) p) ^ k) v ∈ B k := by
    induction k with
    | zero => rw [hzero]; trivial
    | succ k hk =>
      rw [pow_succ', Module.End.mul_apply]
      exact hraise k _ hk
  rw [map_pow]
  ext v
  have h := hpow c v
  rw [hc, Submodule.mem_bot] at h
  exact h

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
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanModel
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The nilpotent ideal in the Cartan model

Nonzero generalized root vectors lie in the derived algebra. Their generated
ideal is nilpotent for an actual triangular adjoint representation, and its
sum with the Cartan subalgebra is the full Lie algebra.
-/

noncomputable section

namespace PolycyclicRecognition

open LieAlgebra LieModule

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L]
  (H : LieSubalgebra ℝ L) [H.IsCartanSubalgebra]

set_option maxHeartbeats 1000000 in
theorem cartanRootIdeal_le_derived : cartanRootIdeal H ≤ derivedSeries ℝ L 1 := by
  apply LieSubmodule.lieSpan_le.mpr
  rintro v ⟨χ, hχ, hv⟩
  apply nonzero_root_le_ideal H (derivedSeries ℝ L 1) _ χ hχ hv
  intro x y
  change ⁅x, y⁆ ∈ ⁅(⊤ : LieIdeal ℝ L), ⊤⁆
  exact LieSubmodule.lie_mem_lie (LieSubmodule.mem_top _) (LieSubmodule.mem_top _)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanDecomposition
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instNonemptyBases _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_nonempty _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Cartan models for the real triangular adjoint action

The nilpotent ideal and Cartan subalgebra span the algebra, and the Cartan
subalgebra maps onto the actual canonical height quotient.
-/

noncomputable section

namespace PolycyclicRecognition

open LieAlgebra LieModule

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {n : ℕ} (T : TriangularAdjoint L n)

set_option maxHeartbeats 1000000 in
/-- Existence and the Lie-algebra assertions of the manuscript's Cartan
model lemma. All terms are constructed from the actual adjoint basis. -/
theorem exists_cartan_model :
    ∃ H : LieSubalgebra ℝ L, ∃ _ : H.IsCartanSubalgebra,
      LieRing.IsNilpotent (cartanRootIdeal H) ∧
      cartanRootIdeal H ≤ derivedSeries ℝ L 1 ∧
      (cartanRootIdeal H).toSubmodule ⊔ H.toSubmodule = ⊤ ∧
      Function.Surjective ((heightProjection T.character).comp H.subtype) := by
  obtain ⟨x, hx⟩ := exists_isCartanSubalgebra_engel ℝ L
  let := hx
  exact ⟨LieSubalgebra.engel ℝ x, hx, cartanRootIdeal_nilpotent _ T,
    cartanRootIdeal_le_derived _, triangular_cartan_spanning T _,
    cartan_height_surjective T _⟩

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
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_RealEigenAnnihilator
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A real split annihilator from spanning real eigenvectors -/

noncomputable section
namespace PolycyclicRecognition

open Polynomial Module

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
  (D : Module.End ℝ V)

theorem realEigenPolynomial_monic : (realEigenPolynomial D).Monic := by
  classical
  exact monic_prod_of_monic _ _ fun r _ => monic_X_sub_C (r : ℝ)

theorem realEigenPolynomial_splits : (realEigenPolynomial D).Splits := by
  classical
  exact Splits.prod fun r _ => Splits.X_sub_C (r : ℝ)

theorem realEigenPolynomial_annihilates (hspan : (⨆ r : ℝ, D.eigenspace r) = ⊤) :
    aeval D (realEigenPolynomial D) = 0 := by
  classical
  let : Fintype {r // D.HasUnifEigenvalue r 1} := inferInstanceAs (Fintype D.Eigenvalues)
  ext v
  have hv : v ∈ ⨆ r : ℝ, D.eigenspace r := by
    rw [hspan]
    trivial
  apply Submodule.iSup_induction (fun r : ℝ => D.eigenspace r)
    (motive := fun v => aeval D (realEigenPolynomial D) v = 0) hv
  · intro r v hvr
    by_cases hv0 : v = 0
    · simp [hv0]
    · have hr : D.HasEigenvalue r := D.hasEigenvalue_of_hasEigenvector ⟨hvr, hv0⟩
      have hz : (realEigenPolynomial D).eval r = 0 := by
        change (Polynomial.evalRingHom r) (∏ t : D.Eigenvalues, (X - C (t : ℝ))) = 0
        rw [map_prod]
        apply Finset.prod_eq_zero (Finset.mem_univ (⟨r, hr⟩ : D.Eigenvalues))
        simp
      rw [D.aeval_apply_of_mem_apply_eq_smul (Module.End.mem_eigenspace_iff.mp hvr), hz, zero_smul]
  · simp
  · intro u v hu hv
    simp only [map_add, hu, hv, add_zero]

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
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanJordanDecomposition
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.CartanFactorModel.heightRay_zero _root_.OAI.PolycyclicRecognition.CartanWordModel.supportDatum_weight _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.nilshadowWeightDerivation_symm _root_.OAI.PolycyclicRecognition.nilshadowWeightOperator_symm _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Identifying the Cartan weight operator as the semisimple part

The polynomial Jordan decomposition shows that the weight operator preserves
every subspace preserved by the original adjoint operator. This will keep the
original triangular flag when the weight operator is subtracted.
-/

noncomputable section
namespace PolycyclicRecognition

open LieAlgebra LieModule Module

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {n : ℕ} (T : TriangularAdjoint L n)
  (H : LieSubalgebra ℝ L) [H.IsCartanSubalgebra]

set_option maxHeartbeats 1000000 in
theorem cartanWeightOperator_jordan (h : H) :
    cartanWeightOperator T H h ∈ Algebra.adjoin ℝ {ad ℝ L (h : L)} ∧
      IsNilpotent (ad ℝ L (h : L) - cartanWeightOperator T H h) := by
  obtain ⟨N, hN, S, hS, hnil, hss, hsum⟩ :=
    (ad ℝ L (h : L)).exists_isNilpotent_isSemisimple
  have hc : Commute (ad ℝ L (h : L)) S :=
    Algebra.commute_of_mem_adjoin_singleton_of_commute hS (Commute.refl _)
  have hd : IsNilpotent (ad ℝ L (h : L) - S) := by
    simpa only [hsum, add_sub_cancel_right] using hnil
  have heq : S = cartanWeightOperator T H h := by
    ext x
    apply cartan_root_induction T H (x := x)
    · intro χ v hv
      rw [cartanWeightOperator_apply_root T H h χ hv]
      have hv' : v ∈ (ad ℝ L (h : L)).maxGenEigenspace (χ h) :=
        genWeightSpace_le_genWeightSpaceOf L h χ hv
      exact End.apply_eq_of_mem_of_comm_of_isFinitelySemisimple_of_isNil
        hv' hc hss.isFinitelySemisimple hd
    · simp
    · intro u v hu hv
      simp only [map_add, hu, hv]
  exact ⟨heq ▸ hS, heq ▸ hd⟩

set_option maxHeartbeats 1000000 in
theorem cartanWeightOperator_upper (h : H) :
    (LinearMap.toMatrix T.basis T.basis (cartanWeightOperator T H h)).IsUpperTriangular := by
  let F := LinearMap.toMatrixAlgEquiv T.basis
  let A := Matrix.blockTriangularSubalgebra ℝ ℝ (id : Fin n → Fin n)
  have hle : Algebra.adjoin ℝ {ad ℝ L (h : L)} ≤ A.comap F.toAlgHom := by
    apply Algebra.adjoin_le
    intro f hf
    obtain rfl := Set.mem_singleton_iff.mp hf
    exact T.upper h
  exact hle (cartanWeightOperator_jordan T H h).1

set_option maxHeartbeats 1000000 in
/-- Removing the semisimple height action leaves a strictly triangular
operator in the original adjoint flag. -/
theorem heightReducedAdjoint_nilpotent (x : L) :
    IsNilpotent (ad ℝ L x - (heightSemisimpleAction T H x).toLinearMap) := by
  let h := cartanHeightSection T H (heightProjection T.character x)
  let u : L := x - (h : L)
  let N := ad ℝ L (h : L) - cartanWeightOperator T H h
  have hN : IsNilpotent N := (cartanWeightOperator_jordan T H h).2
  have hNu : (LinearMap.toMatrix T.basis T.basis N).IsUpperTriangular := by
    rw [show N = ad ℝ L (h : L) - cartanWeightOperator T H h from rfl, map_sub]
    exact (T.upper h).sub (cartanWeightOperator_upper T H h)
  have hNd (i : Fin n) : LinearMap.toMatrix T.basis T.basis N i i = 0 :=
    upperTriangular_nilpotent_diag _ hNu
      (hN.map (LinearMap.toMatrixAlgEquiv T.basis).toRingHom) i
  have huk : u ∈ T.kernelIdeal := by
    apply (Submodule.Quotient.mk_eq_zero _).mp
    change heightProjection T.character (x - (h : L)) = 0
    rw [map_sub, cartanHeightSection_height, sub_self]
  have hud (i : Fin n) : LinearMap.toMatrix T.basis T.basis (ad ℝ L u) i i = 0 := by
    rw [← T.character_eq_diag]
    exact (T.mem_kernelIdeal u).mp huk i
  have heq : ad ℝ L x - (heightSemisimpleAction T H x).toLinearMap = ad ℝ L u + N := by
    change ad ℝ L x - cartanWeightOperator T H h = ad ℝ L (x - (h : L)) + N
    rw [map_sub]
    dsimp only [N]
    abel
  rw [heq]
  obtain ⟨k, hk⟩ := upperTriangular_nilpotent_of_diag_zero
    (LinearMap.toMatrix T.basis T.basis (ad ℝ L u + N))
    (by rw [map_add]; exact (T.upper u).add hNu)
    (by intro i; simp only [map_add, Matrix.add_apply, hud, hNd, add_zero])
  refine ⟨k, (LinearMap.toMatrixAlgEquiv T.basis).injective ?_⟩
  rw [map_pow, map_zero]
  change (LinearMap.toMatrix T.basis T.basis (ad ℝ L u + N)) ^ k = 0
  exact hk

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Lattices_CartanNilshadow
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanRealShadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The nilpotent Lie algebra attached to the Cartan height action

The graph of minus the semisimple height action is a Lie subalgebra of the
affine derivation algebra. Its first coordinate is linearly the original Lie
algebra, while its bracket has the semisimple action removed.
-/

noncomputable section
namespace PolycyclicRecognition

open LieAlgebra Module

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {n : ℕ} (T : TriangularAdjoint L n)
  (H : LieSubalgebra ℝ L) [H.IsCartanSubalgebra]

set_option maxHeartbeats 1000000 in
private theorem nilpotent_of_square_eq_mul {V : Type*} [AddCommGroup V] [Module ℝ V]
    {A F : Module.End ℝ V} (hA : IsNilpotent A) (hFF : F * F = A * F) : IsNilpotent F := by
  have hp (k : ℕ) : F ^ (k + 1) = A ^ k * F := by
    induction k with
    | zero => simp
    | succ k hk =>
      calc
        F ^ (k + 1 + 1) = F ^ (k + 1) * F := pow_succ _ _
        _ = A ^ k * (F * F) := by rw [hk, mul_assoc]
        _ = A ^ (k + 1) * F := by rw [hFF, ← mul_assoc, pow_succ]
  obtain ⟨k, hk⟩ := hA
  exact ⟨k + 1, by rw [hp, hk, zero_mul]⟩

set_option maxHeartbeats 1000000 in
/-- The Cartan graph is nilpotent; no nilshadow theorem is assumed. -/
theorem cartanNilshadow_nilpotent : LieRing.IsNilpotent (CartanNilshadow T H) := by
  let e := cartanNilshadowEquiv T H
  apply (LieAlgebra.isNilpotent_iff_forall (R := ℝ)).mpr
  intro p
  obtain ⟨x, rfl⟩ := e.surjective p
  let F : Module.End ℝ L := e.symm.conjRingEquiv (ad ℝ (CartanNilshadow T H) (e x))
  let A : Module.End ℝ L := ad ℝ L x - (heightSemisimpleAction T H x).toLinearMap
  have hF (y : L) : F y = ⁅x, y⁆ - heightSemisimpleAction T H x y +
      heightSemisimpleAction T H y x := cartanNilshadow_bracket T H x y
  have hFh (y : L) : heightProjection T.character (F y) = 0 := by
    rw [hF, map_add, map_sub, T.height_lie, heightSemisimpleAction_height_zero,
      heightSemisimpleAction_height_zero, sub_self, add_zero]
  have hFr (y : L) (hy : heightProjection T.character y = 0) : F y = A y := by
    have hs : heightSemisimpleAction T H y = 0 := by
      change cartanWeightDerivationLinear T H
        (cartanHeightSection T H (heightProjection T.character y)) = 0
      rw [hy, map_zero, map_zero]
    rw [hF, hs, LieDerivation.zero_apply, add_zero]
    rfl
  have hFF : F * F = A * F := by
    ext y
    exact hFr (F y) (hFh y)
  obtain ⟨k, hk⟩ := nilpotent_of_square_eq_mul (heightReducedAdjoint_nilpotent T H x) hFF
  refine ⟨k, e.symm.conjRingEquiv.injective ?_⟩
  rw [map_pow, map_zero]
  exact hk

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Lattices_NilshadowWeightAction
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original solvable algebra as an extension of its nilshadow -/

noncomputable section
namespace PolycyclicRecognition

open LieAlgebra Module

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {n : ℕ} (T : TriangularAdjoint L n)
  (H : LieSubalgebra ℝ L) [H.IsCartanSubalgebra]

local notation "σ" => heightSemisimpleAction T H
local notation "e" => cartanNilshadowEquiv T H

theorem nilshadowWeightDerivation_equiv (x y : L) :
    nilshadowWeightDerivation T H x (e y) = e (σ x y) := by
  apply (e).symm.injective
  simp only [nilshadowWeightDerivation_symm, LinearEquiv.symm_apply_apply]

theorem nilshadowSemidirectEmbedding_injective :
    Function.Injective (nilshadowSemidirectEmbedding T H) := by
  intro x y h
  exact (e).injective (congrArg SemiDirectSum.left h)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_SolvableFaithfulRepresentation
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.CartanFactorModel.heightRay_zero _root_.OAI.PolycyclicRecognition.CartanWordModel.supportDatum_weight _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A faithful representation nilpotent on the canonical nilradical

The representation is obtained from the proved nilshadow and its finite
truncated enveloping algebra. Real triangularization is a separate step.
-/

noncomputable section
namespace PolycyclicRecognition

open Module LieAlgebra

attribute [local instance 100] LieRing.ofAssociativeRing

variable {L : Type} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {n : ℕ} (T : TriangularAdjoint L n)
  (H : LieSubalgebra ℝ L) [H.IsCartanSubalgebra]

local notation "K" => CartanNilshadow T H

theorem nilshadowWeightDerivation_eq_zero_of_mem_kernel (x : L) (hx : x ∈ T.kernelIdeal) :
    nilshadowWeightDerivation T H x = 0 := by
  have hσ : heightSemisimpleAction T H x = 0 := by
    change cartanWeightDerivationLinear T H
      (cartanHeightSection T H (heightProjection T.character x)) = 0
    have hz : heightProjection T.character x = 0 := (Submodule.Quotient.mk_eq_zero _).mpr hx
    rw [hz, map_zero, map_zero]
  apply LieDerivation.ext
  intro p
  apply (cartanNilshadowEquiv T H).symm.injective
  rw [nilshadowWeightDerivation_symm, hσ]
  simp

theorem solvableTruncatedRepresentation_nilpotent (c : ℕ) (x : L)
    (hx : x ∈ T.kernelIdeal) : IsNilpotent (solvableTruncatedRepresentation T H c x) := by
  change IsNilpotent (truncatedLeftRepresentation (R := ℝ) c (cartanNilshadowEquiv T H x) +
    truncatedEnvelopingDerivationRepresentation c (nilshadowWeightDerivation T H x))
  rw [nilshadowWeightDerivation_eq_zero_of_mem_kernel T H x hx, map_zero, add_zero]
  exact truncatedLeftRepresentation_nilpotent _ _

theorem solvableTruncatedRepresentation_injective (c : ℕ)
    (hgen : Function.Injective (truncatedEnvelopingGenerator (R := ℝ) (L := K) c)) :
    Function.Injective (solvableTruncatedRepresentation T H c) :=
  (truncatedSemidirectRepresentation_injective c _
    (show Function.Injective (nilshadowWeightAction T H).range.incl from
      Subtype.val_injective) hgen).comp
    (nilshadowSemidirectEmbedding_injective T H)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_SplitAnnihilator
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Split annihilators and real generalized eigenspaces

The usual finite-dimensional decomposition only needs a split annihilator,
rather than an algebraically closed scalar field. Restrictions retain the
same annihilator, so the argument also applies to invariant subspaces.
-/

noncomputable section
namespace PolycyclicRecognition

open Polynomial Module

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

theorem aeval_restrict_apply (f : Module.End ℝ V) (S : Submodule ℝ V)
    (hS : ∀ v ∈ S, f v ∈ S) (p : ℝ[X]) (v : S) :
    ((aeval (f.restrict hS) p v : S) : V) = aeval f p (v : V) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, LinearMap.add_apply, Submodule.coe_add, hp, hq]
  | monomial n a =>
    simp only [aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply,
      Submodule.coe_smul_of_tower]
    congr 1
    induction n with
    | zero => rfl
    | succ n hn =>
      rw [pow_succ', pow_succ', Module.End.mul_apply, Module.End.mul_apply]
      exact congrArg f hn

theorem aeval_restrict_eq_zero (f : Module.End ℝ V) (S : Submodule ℝ V)
    (hS : ∀ v ∈ S, f v ∈ S) (p : ℝ[X]) (hp : aeval f p = 0) :
    aeval (f.restrict hS) p = 0 := by
  ext v
  rw [aeval_restrict_apply, hp]
  rfl

theorem exists_eigenvalue_of_split_annihilator [FiniteDimensional ℝ V] [Nontrivial V]
    (f : Module.End ℝ V) (p : ℝ[X]) (hp0 : p ≠ 0) (hps : p.Splits)
    (hp : aeval f p = 0) : ∃ r : ℝ, f.HasEigenvalue r := by
  have hi := Algebra.IsIntegral.isIntegral (R := ℝ) f
  have hs : (minpoly ℝ f).Splits := hps.of_dvd hp0 (minpoly.dvd ℝ f hp)
  obtain ⟨r, hr⟩ := hs.exists_eval_eq_zero (ne_of_gt (minpoly.degree_pos hi))
  exact ⟨r, Module.End.hasEigenvalue_of_isRoot hr⟩

theorem iSup_maxGenEigenspace_eq_top_of_split_annihilator [FiniteDimensional ℝ V]
    (f : Module.End ℝ V) (p : ℝ[X]) (hp0 : p ≠ 0) (hps : p.Splits)
    (hp : aeval f p = 0) : ⨆ r : ℝ, f.maxGenEigenspace r = ⊤ := by
  suffices ∀ n, finrank ℝ V = n → ⨆ r : ℝ, f.maxGenEigenspace r = ⊤ by
    exact this _ rfl
  intro n hn
  induction n using Nat.strong_induction_on generalizing V with
  | h n ih =>
    rcases n with - | n
    · rw [← top_le_iff]
      simp only [Submodule.finrank_eq_zero.1 (Eq.trans (finrank_top _ _) hn), bot_le]
    · have : Nontrivial V := finrank_pos_iff.1 (by rw [hn]; exact Nat.zero_lt_succ n)
      obtain ⟨r, hr⟩ := exists_eigenvalue_of_split_annihilator f p hp0 hps hp
      let ES := f.genEigenspace r (finrank ℝ V)
      let ER := f.genEigenrange r (finrank ℝ V)
      have hER : ∀ v ∈ ER, f v ∈ ER := fun v hv =>
        Module.End.map_genEigenrange_le (Submodule.mem_map_of_mem hv)
      let f' : Module.End ℝ ER := f.restrict hER
      have hpos : 0 < finrank ℝ ES := by
        dsimp +instances only [ES]
        rw [hn]
        exact Module.End.pos_finrank_genEigenspace_of_hasEigenvalue hr (Nat.zero_lt_succ n)
      have hadd : finrank ℝ ER + finrank ℝ ES = finrank ℝ V := by
        dsimp +instances only [ER, ES]
        rw [Module.End.genEigenspace_nat, Module.End.genEigenrange_nat]
        exact LinearMap.finrank_range_add_finrank_ker _
      have hlt : finrank ℝ ER < n.succ := by omega
      have hspan : ⨆ r : ℝ, f'.maxGenEigenspace r = ⊤ :=
        ih (finrank ℝ ER) hlt f' (aeval_restrict_eq_zero f ER hER p hp) rfl
      have hspan' : ⨆ r : ℝ, (f'.maxGenEigenspace r).map ER.subtype = ER := by
        simp only [(Submodule.map_iSup _ _).symm, hspan, Submodule.map_subtype_top ER]
      have hmap : ∀ r, (f'.maxGenEigenspace r).map ER.subtype ≤ f.maxGenEigenspace r := by
        intro r
        rw [Module.End.maxGenEigenspace, Module.End.genEigenspace_restrict]
        apply Submodule.map_comap_le
      have hleR : ER ≤ ⨆ r : ℝ, f.maxGenEigenspace r := by
        rw [← hspan']
        exact iSup_mono hmap
      have hleS : ES ≤ ⨆ r : ℝ, f.maxGenEigenspace r :=
        ((f.genEigenspace r).mono le_top).trans (le_iSup f.maxGenEigenspace r)
      have hdis : Disjoint ER ES := Module.End.generalized_eigenvec_disjoint_range_ker f r
      rw [← top_le_iff, ← Submodule.eq_top_of_disjoint ER ES hadd.ge hdis]
      exact sup_le hleR hleS

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_WordLengthFiltration
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Word-length filtration for a nilpotent generated algebra

Left multiplication raises word length; a derivation carrying generators to
generators preserves it. This separates the nilpotent and semisimple parts
of the finite solvable representation.
-/

noncomputable section
namespace PolycyclicRecognition

variable {A ι : Type*} [Ring A] [Algebra ℝ A] (j : ι → A)

theorem wordLengthSpan_antitone : Antitone (wordLengthSpan j) := by
  intro k l hkl
  apply Submodule.span_mono
  rintro a ⟨w, hw, rfl⟩
  exact ⟨w, hkl.trans hw, rfl⟩

theorem wordLengthSpan_generator_mul (k : ℕ) (x : ι) {a : A}
    (ha : a ∈ wordLengthSpan j k) : j x * a ∈ wordLengthSpan j (k + 1) := by
  induction ha using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨l, hl, rfl⟩ := ha
    apply Submodule.subset_span
    exact ⟨x :: l, Nat.succ_le_succ hl, by simp⟩
  | zero => simpa only [mul_zero] using (wordLengthSpan j (k + 1)).zero_mem
  | add a b _ _ ha hb =>
    rw [mul_add]
    exact (wordLengthSpan j (k + 1)).add_mem ha hb
  | smul r a _ ha =>
    rw [Algebra.mul_smul_comm]
    exact (wordLengthSpan j (k + 1)).smul_mem r ha

theorem wordLengthSpan_zero_eq_top (hgen : Algebra.adjoin ℝ (Set.range j) = ⊤) :
    wordLengthSpan j 0 = ⊤ := by
  have hle : (Algebra.adjoin ℝ (Set.range j)).toSubmodule ≤ wordLengthSpan j 0 := by
    rw [Algebra.adjoin_eq_span]
    apply Submodule.span_le.mpr
    intro a ha
    have hw : ∃ l : List ι, (l.map j).prod = a := by
      induction ha using Submonoid.closure_induction with
      | mem a ha =>
        obtain ⟨x, rfl⟩ := ha
        exact ⟨[x], by simp⟩
      | one => exact ⟨[], by simp⟩
      | mul a b _ _ ha hb =>
        obtain ⟨v, rfl⟩ := ha
        obtain ⟨w, rfl⟩ := hb
        exact ⟨v ++ w, by simp⟩
    obtain ⟨l, rfl⟩ := hw
    exact Submodule.subset_span ⟨l, Nat.zero_le _, rfl⟩
  apply top_unique
  rw [hgen] at hle
  exact hle

theorem wordLengthSpan_eq_bot (c : ℕ)
    (hnil : ∀ l : List ι, c ≤ l.length → (l.map j).prod = 0) :
    wordLengthSpan j c = ⊥ := by
  apply eq_bot_iff.mpr
  apply Submodule.span_le.mpr
  rintro a ⟨l, hl, rfl⟩
  exact (Submodule.mem_bot ℝ).mpr (hnil l hl)

variable (D : Module.End ℝ A) (f : ι → ι)
  (hmul : ∀ a b, D (a * b) = a * D b + D a * b)
  (hone : D 1 = 0) (hgen : ∀ x, D (j x) = j (f x))

include f hmul hone hgen

theorem wordLengthSpan_prefix_derivative (k : ℕ) (p l : List ι)
    (h : k ≤ p.length + l.length) :
    (p.map j).prod * D (l.map j).prod ∈ wordLengthSpan j k := by
  induction l generalizing p with
  | nil =>
    simpa only [List.map_nil, List.prod_nil, hone, mul_zero] using (wordLengthSpan j k).zero_mem
  | cons x l ih =>
    simp only [List.map_cons, List.prod_cons, hmul, hgen, mul_add]
    apply (wordLengthSpan j k).add_mem
    · have hp : k ≤ (p ++ [x]).length + l.length := by
        simpa only [List.length_append, List.length_singleton, List.length_cons,
          List.length_nil, zero_add, Nat.add_assoc, Nat.add_comm 1] using h
      simpa only [List.map_append, List.prod_append, List.map_singleton,
        List.prod_singleton, mul_assoc] using ih (p ++ [x]) hp
    · apply Submodule.subset_span
      refine ⟨p ++ f x :: l, ?_, ?_⟩
      · simpa only [List.length_append, List.length_cons] using h
      · simp only [List.map_append, List.prod_append, List.map_cons, List.prod_cons]

theorem wordLengthSpan_derivative (k : ℕ) {a : A} (ha : a ∈ wordLengthSpan j k) :
    D a ∈ wordLengthSpan j k := by
  induction ha using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨l, hl, rfl⟩ := ha
    simpa only [List.map_nil, List.prod_nil, one_mul] using
      wordLengthSpan_prefix_derivative j D f hmul hone hgen k [] l (by simpa using hl)
  | zero => simpa only [map_zero] using (wordLengthSpan j k).zero_mem
  | add a b _ _ ha hb =>
    rw [map_add]
    exact (wordLengthSpan j k).add_mem ha hb
  | smul r a _ ha =>
    rw [map_smul]
    exact (wordLengthSpan j k).smul_mem r ha

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_SolvableWeightEigenvectors
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanRealShadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Real eigenvectors span the finite weight representation -/

noncomputable section
namespace PolycyclicRecognition

open Module LieAlgebra LieModule

variable {L : Type} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {n : ℕ} (T : TriangularAdjoint L n)
  (H : LieSubalgebra ℝ L) [H.IsCartanSubalgebra]

local notation "K" => CartanNilshadow T H
local notation "e" => cartanNilshadowEquiv T H
local notation "Q" c => TruncatedEnvelopingAlgebra ℝ K c

theorem solvableWeightDerivation_eigenspaces_span (c : ℕ) (x : L) :
    derivationEigenvectorSpan (truncatedEnvelopingDerivation c
      (nilshadowWeightDerivation T H x)) = ⊤ := by
  let D := truncatedEnvelopingDerivation c (nilshadowWeightDerivation T H x)
  let S := derivationEigenvectorSubalgebra D
    (truncatedEnvelopingDerivation_one c _)
    (truncatedEnvelopingDerivation_mul c _)
  have hgen (v : K) : truncatedEnvelopingGenerator (R := ℝ) c v ∈ S := by
    obtain ⟨v, rfl⟩ := (e).surjective v
    apply cartan_root_induction T H (x := v)
    · intro χ v hv
      apply Submodule.mem_iSup_of_mem (cartanHeightWeight T H χ (heightProjection T.character x))
      rw [Module.End.mem_eigenspace_iff]
      change truncatedEnvelopingDerivation c (nilshadowWeightDerivation T H x)
        (truncatedEnvelopingGenerator c (e v)) = _
      rw [truncatedEnvelopingDerivation_generator, nilshadowWeightDerivation_equiv,
        heightSemisimpleAction_apply_root T H x χ hv, map_smul, map_smul]
    · simpa only [map_zero] using S.zero_mem
    · intro v w hv hw
      simpa only [map_add] using S.add_mem hv hw
  have hle : (⊤ : Subalgebra ℝ (Q c)) ≤ S := by
    rw [← truncatedEnveloping_adjoin_basis (finBasis ℝ K) c]
    apply Algebra.adjoin_le
    rintro _ ⟨i, rfl⟩
    exact hgen _
  apply top_unique
  intro u _
  exact hle (by trivial)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_SolvableRepresentationAnnihilator
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanRealShadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Real split annihilators for the faithful solvable representation

The semisimple derivation preserves word length, while left multiplication
raises it. The finite word-length filtration therefore turns the split
annihilator of the derivation into one for their sum.
-/

noncomputable section
namespace PolycyclicRecognition

open Polynomial Module

variable {L : Type} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {n : ℕ} (T : TriangularAdjoint L n)
  (H : LieSubalgebra ℝ L) [H.IsCartanSubalgebra]

local notation "K" => CartanNilshadow T H
local notation "Q" c => TruncatedEnvelopingAlgebra ℝ K c

theorem solvableTruncatedRepresentation_split_annihilator (c : ℕ) (x : L) :
    ∃ p : ℝ[X], p.Monic ∧ p.Splits ∧
      aeval (solvableTruncatedRepresentation T H c x) p = 0 := by
  let := finiteDimensional_truncatedEnvelopingAlgebra (finBasis ℝ K) c
  let j := truncatedEnvelopingGenerator (R := ℝ) (L := K) c
  let δ := nilshadowWeightDerivation T H x
  let D := truncatedEnvelopingDerivation c δ
  let N := truncatedLeftRepresentation (R := ℝ) c (cartanNilshadowEquiv T H x)
  let B := wordLengthSpan j
  have hgen : Algebra.adjoin ℝ (Set.range j) = ⊤ := by
    apply top_unique
    rw [← truncatedEnveloping_adjoin_basis (finBasis ℝ K) c]
    apply Algebra.adjoin_mono
    rintro _ ⟨i, rfl⟩
    exact ⟨finBasis ℝ K i, rfl⟩
  have hD (k : ℕ) (v : Q c) (hv : v ∈ B k) : D v ∈ B k :=
    wordLengthSpan_derivative j D δ (truncatedEnvelopingDerivation_mul c δ)
      (truncatedEnvelopingDerivation_one c δ)
      (truncatedEnvelopingDerivation_generator c δ) k hv
  have hN (k : ℕ) (v : Q c) (hv : v ∈ B k) : N v ∈ B (k + 1) :=
    wordLengthSpan_generator_mul j k (cartanNilshadowEquiv T H x) hv
  let p := realEigenPolynomial D
  have hp : aeval D p = 0 := realEigenPolynomial_annihilates D
    (solvableWeightDerivation_eigenspaces_span T H c x)
  refine ⟨p ^ c, (realEigenPolynomial_monic D).pow c,
    (realEigenPolynomial_splits D).pow c, ?_⟩
  have heq : solvableTruncatedRepresentation T H c x = D + N := by
    change N + D = D + N
    exact add_comm _ _
  rw [heq]
  exact filtered_polynomial_annihilator B D N (wordLengthSpan_antitone j) hD hN c
    (wordLengthSpan_zero_eq_top j hgen)
    (wordLengthSpan_eq_bot j c (truncatedEnvelopingGenerator_prod_eq_zero c)) p hp

theorem solvableTruncatedRepresentation_genEigenspaces_span (c : ℕ) (x : L) :
    ⨆ r : ℝ, (solvableTruncatedRepresentation T H c x).maxGenEigenspace r = ⊤ := by
  let := finiteDimensional_truncatedEnvelopingAlgebra (finBasis ℝ K) c
  obtain ⟨p, hm, hs, hz⟩ := solvableTruncatedRepresentation_split_annihilator T H c x
  exact iSup_maxGenEigenspace_eq_top_of_split_annihilator _ p hm.ne_zero hs hz

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
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_CompactLiftContinuity
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Continuity of a descended map from compact lifts

The Cartan multiplication map already has compact lifts of compact sets.
This gives the quotient-continuity statement needed for a representation
defined by its two factors.
-/

namespace PolycyclicRecognition

open Set Filter Topology

theorem continuous_of_compact_lifts
    {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    [T2Space Y] [LocallyCompactSpace Y]
    (p : X → Y) (F : X → Z) (f : Y → Z) (hp : Continuous p) (hF : Continuous F)
    (hcomp : ∀ x, f (p x) = F x)
    (hlift : ∀ K : Set Y, IsCompact K → ∃ C : Set X, IsCompact C ∧ K ⊆ p '' C) :
    Continuous f := by
  rw [continuous_def]
  intro U hU
  apply isOpen_iff_mem_nhds.mpr
  intro y hy
  obtain ⟨K, hK, hKy⟩ := exists_compact_mem_nhds y
  obtain ⟨C, hC, hKC⟩ := hlift K hK
  let B := C ∩ F ⁻¹' Uᶜ
  have hB : IsCompact B := hC.inter_right (hU.isClosed_compl.preimage hF)
  have hclosed : IsClosed (p '' B) := (hB.image hp).isClosed
  have hyB : y ∉ p '' B := by
    rintro ⟨x, hx, rfl⟩
    exact hx.2 (hcomp x ▸ hy)
  have hneigh : (p '' B)ᶜ ∈ 𝓝 y := hclosed.isOpen_compl.mem_nhds hyB
  apply Filter.mem_of_superset (inter_mem hKy hneigh)
  rintro z ⟨hzK, hzB⟩
  obtain ⟨x, hxC, rfl⟩ := hKC hzK
  by_contra hz
  apply hzB
  refine ⟨x, ⟨hxC, ?_⟩, rfl⟩
  change F x ∉ U
  change f (p x) ∉ U at hz
  rwa [hcomp x] at hz

end PolycyclicRecognition

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_AlgebraRepresentationDerivative
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Recovering represented tangent vectors from exponential lines -/

noncomputable section
namespace PolycyclicRecognition

open scoped Manifold ContDiff
attribute [local instance 100] LieRing.ofAssociativeRing

variable {E G A : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace G] [ChartedSpace E G]
  [Group G] [LieGroup (𝓘(ℝ, E)) ⊤ G]
  [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

theorem unitsHomLieDifferential_eq_of_exponential_line
    {Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G} (hExp : IsGroupExponential Exp)
    (ρ : G →* Aˣ)
    (hf : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, A)) ∞ (fun g => (ρ g : A)))
    (x : GroupLieAlgebra (𝓘(ℝ, E)) G) (a : A)
    (he : ∀ t : ℝ, ρ (Exp (t • x)) = algebraExpUnit (t • a)) :
    unitsHomLieDifferential ρ hf x = a := by
  let j := (unitsHomLieDifferential ρ hf).toLinearMap.toContinuousLinearMap
  have hd := hasMFDerivAt_unitsHomLieDifferential ρ hf
  have hbase : HasMFDerivAt (𝓘(ℝ, E)) (𝓘(ℝ, A))
      (fun g => (ρ g : A)) (Exp ((0 : ℝ) • x)) j := by
    rw [zero_smul, hExp.map_zero]
    exact hd
  have hcomp := hbase.comp 0 (hExp.hasMFDerivAt_zero x)
  have hF : HasFDerivAt (fun t : ℝ => (ρ (Exp (t • x)) : A))
      (j.comp (ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℝ ℝ) x)) 0 :=
    hcomp.hasFDerivAt
  have h := hF.hasDerivAt
  change HasDerivAt (fun t : ℝ => (ρ (Exp (t • x)) : A)) (j ((1 : ℝ) • x)) 0 at h
  have hj : j x = unitsHomLieDifferential ρ hf x := rfl
  rw [one_smul, hj] at h
  have h' : HasDerivAt (fun t : ℝ => NormedSpace.exp (t • a))
      (unitsHomLieDifferential ρ hf x) 0 := by
    simpa only [he, coe_algebraExpUnit] using h
  have ha : HasDerivAt (fun t : ℝ => NormedSpace.exp (t • a)) a 0 := by
    simpa only [zero_smul, NormedSpace.exp_zero, one_mul] using
      (hasDerivAt_exp_smul_const a (0 : ℝ))
  exact h'.unique ha

end PolycyclicRecognition

end

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
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanRepresentationDescent
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Descending continuous representations from the Cartan factors

The existing factor model includes surjectivity and compact lifts. Thus
the algebraic descent also preserves continuity, without choosing a
global continuous factorization.
-/

noncomputable section
namespace PolycyclicRecognition

open scoped Manifold

variable {E G A : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MetricSpace G] [ChartedSpace E G]
  [Group G] [LieGroup (𝓘(ℝ, E)) ⊤ G] [SimplyConnectedSpace G] [LocallyCompactSpace G]
  [Group A] [TopologicalSpace A] [IsTopologicalGroup A]
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, E)) G)} [H.IsCartanSubalgebra]
  {Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G}

set_option maxHeartbeats 1000000 in
omit [SimplyConnectedSpace G] in
theorem CartanFactorModel.descend_representation (F : CartanFactorModel H Exp)
    (ρN : F.N.carrier →* A) (ρD : F.D.carrier →* A)
    (hcN : Continuous ρN) (hcD : Continuous ρD)
    (hconj : ∀ d n, ρN (F.action d n) = ρD d * ρN n * (ρD d)⁻¹)
    (hagree : ∀ n d, F.inclusionN n = F.inclusionD d → ρN n = ρD d) :
    ∃ ρ : G →* A, Continuous ρ ∧
      ∀ n d, ρ (F.inclusionN n * F.inclusionD d) = ρN n * ρD d := by
  let : ContinuousMul G := ⟨(contMDiff_mul (𝓘(ℝ, E)) ⊤).continuous⟩
  obtain ⟨ρ, hρ⟩ := exists_representation_of_factor_maps F.action F.inclusionN F.inclusionD
    (fun d => by ext n; exact F.conjugation d n)
    (fun g => by obtain ⟨⟨n, d⟩, h⟩ := F.surjective g; exact ⟨n, d, h⟩)
    ρN ρD hconj hagree
  refine ⟨ρ, ?_, hρ⟩
  exact continuous_of_compact_lifts
    (fun p : F.N.carrier × F.D.carrier => F.inclusionN p.1 * F.inclusionD p.2)
    (fun p : F.N.carrier × F.D.carrier => ρN p.1 * ρD p.2) ρ
    ((F.closedN.continuous.comp continuous_fst).mul (F.closedD.continuous.comp continuous_snd))
    ((hcN.comp continuous_fst).mul (hcD.comp continuous_snd))
    (fun p => hρ p.1 p.2) F.compactLifts

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_RepresentedAdjoint
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Intertwining the intrinsic adjoint action with matrix conjugation -/

noncomputable section
namespace PolycyclicRecognition

open scoped Manifold
attribute [local instance 100] LieRing.ofAssociativeRing

variable {E G A : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace G] [ChartedSpace E G]
  [Group G] [LieGroup (𝓘(ℝ, E)) ⊤ G]
  [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

theorem lieHom_adjoint_exponential
    {Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G} (hExp : IsGroupExponential Exp)
    (j : GroupLieAlgebra (𝓘(ℝ, E)) G →ₗ⁅ℝ⁆ A)
    (x y : GroupLieAlgebra (𝓘(ℝ, E)) G) :
    j (adjointLinearMap (E := E) (Exp x) y) =
      NormedSpace.exp (j x) * j y * NormedSpace.exp (-j x) := by
  let f : E →ₗ[ℝ] A := j.toLinearMap
  have he := exp_intertwine_apply f.toContinuousLinearMap
    (groupAdjointOperator (E := E) x) (adjointOperator (j x))
    (fun v => by
      change j ⁅x, v⁆ = j x * j v - j v * j x
      exact j.map_lie x v) y
  have hAd := adjointLinearMap_exponential hExp x 1
  simp only [one_smul] at hAd
  rw [hAd]
  exact he.trans (exp_adjointOperator_apply (j x) (j y))

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanFactorRepresentation
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Integrating a Lie representation through the Cartan factors

Uniqueness of exponential preimages meeting the root ideal suffices to descend
a nilpotently integrated representation through the factor product. Global
injectivity of the exponential gives a specialization.
-/

noncomputable section
namespace PolycyclicRecognition

open scoped Manifold ContDiff
attribute [local instance 100] LieRing.ofAssociativeRing

variable {E G A : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MetricSpace G] [ChartedSpace E G]
  [Group G] [LieGroup (𝓘(ℝ, E)) ⊤ G] [SimplyConnectedSpace G] [LocallyCompactSpace G]
  [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A] [FiniteDimensional ℝ A]
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, E)) G)} [H.IsCartanSubalgebra]
  {Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G}

set_option maxHeartbeats 1000000 in
omit [SimplyConnectedSpace G] in
theorem CartanFactorModel.exists_integrated_representation_of_root_preimages
    (F : CartanFactorModel H Exp)
    (hExp : IsGroupExponential Exp)
    (hinj : ∀ (x : GroupLieAlgebra (𝓘(ℝ, E)) G), x ∈ cartanRootIdeal H →
      ∀ y, Exp x = Exp y → x = y)
    (hn : LieRing.IsNilpotent (cartanRootIdeal H))
    (hspan : (cartanRootIdeal H).toSubmodule ⊔ H.toSubmodule = ⊤)
    (hsN : Function.Surjective F.ExpN) (hsD : Function.Surjective F.ExpD)
    (j : GroupLieAlgebra (𝓘(ℝ, E)) G →ₗ⁅ℝ⁆ A) :
    ∃ ρ : G →* Aˣ, Continuous ρ ∧ ∀ x, ρ (Exp x) = algebraExpUnit (j x) := by
  let : IsTopologicalGroup Aˣ := topologicalGroup_of_lieGroup (𝓘(ℝ, A)) ⊤
  obtain ⟨ρN, hρN, heN⟩ := F.N.exists_algebra_representation hn
    (j.comp (cartanRootIdeal H).incl)
  obtain ⟨ρD, hρD, heD⟩ := F.D.exists_algebra_representation inferInstance
    (j.comp H.incl)
  have hN (x : cartanRootIdeal H) :
      ρN (F.ExpN (F.N.equiv x)) = algebraExpUnit (j x) :=
    heN F.ExpN F.isExpN x
  have hD (x : H) : ρD (F.ExpD (F.D.equiv x)) = algebraExpUnit (j x) :=
    heD F.ExpD F.isExpD x
  have coverN (n : F.N.carrier) : ∃ x : cartanRootIdeal H, F.ExpN (F.N.equiv x) = n := by
    obtain ⟨v, rfl⟩ := hsN n
    exact ⟨F.N.equiv.symm v, by rw [F.N.equiv.apply_symm_apply]⟩
  have coverD (d : F.D.carrier) : ∃ x : H, F.ExpD (F.D.equiv x) = d := by
    obtain ⟨v, rfl⟩ := hsD d
    exact ⟨F.D.equiv.symm v, by rw [F.D.equiv.apply_symm_apply]⟩
  have hconj (d : F.D.carrier) (n : F.N.carrier) :
      ρN (F.action d n) = ρD d * ρN n * (ρD d)⁻¹ := by
    obtain ⟨x, rfl⟩ := coverD d
    obtain ⟨y, rfl⟩ := coverN n
    obtain ⟨z, hz⟩ := coverN (F.action (F.ExpD (F.D.equiv x)) (F.ExpN (F.N.equiv y)))
    have heq : (z : GroupLieAlgebra (𝓘(ℝ, E)) G) =
        adjointLinearMap (E := E) (Exp x)
          (y : GroupLieAlgebra (𝓘(ℝ, E)) G) := by
      apply hinj z z.property
      rw [← F.compatibleN z, hz, F.conjugation, F.compatibleD, F.compatibleN]
      exact conjugation_exponential hExp (Exp x) y
    rw [← hz, hN, hD, hN]
    rw [heq, lieHom_adjoint_exponential hExp j x y]
    exact algebraExpUnit_conj (algebraExpUnit (j x)) (j y)
  have hagree (n : F.N.carrier) (d : F.D.carrier)
      (he : F.inclusionN n = F.inclusionD d) : ρN n = ρD d := by
    obtain ⟨x, rfl⟩ := coverN n
    obtain ⟨y, rfl⟩ := coverD d
    rw [F.compatibleN, F.compatibleD] at he
    have hxy := hinj x x.property y he
    rw [hN, hD, hxy]
  obtain ⟨ρ, hρ, hprod⟩ := F.descend_representation ρN ρD
    hρN.continuous hρD.continuous hconj hagree
  have heN' (x : cartanRootIdeal H) : ρ (Exp x) = algebraExpUnit (j x) := by
    have h := hprod (F.ExpN (F.N.equiv x)) 1
    simpa only [map_one, mul_one, F.compatibleN, hN] using h
  have heD' (x : H) : ρ (Exp x) = algebraExpUnit (j x) := by
    have h := hprod 1 (F.ExpD (F.D.equiv x))
    simpa only [map_one, one_mul, F.compatibleD, hD] using h
  have hf := contMDiff_of_continuous_unitsHom hExp ρ (Units.continuous_val.comp hρ)
  have hdiffN (x : cartanRootIdeal H) : unitsHomLieDifferential ρ hf x = j x := by
    apply unitsHomLieDifferential_eq_of_exponential_line hExp ρ hf
    intro t
    have ht := heN' (t • x)
    change ρ (Exp (t • (x : GroupLieAlgebra (𝓘(ℝ, E)) G))) =
      algebraExpUnit (j (t • (x : GroupLieAlgebra (𝓘(ℝ, E)) G))) at ht
    rwa [map_smul] at ht
  have hdiffD (x : H) : unitsHomLieDifferential ρ hf x = j x := by
    apply unitsHomLieDifferential_eq_of_exponential_line hExp ρ hf
    intro t
    have ht := heD' (t • x)
    change ρ (Exp (t • (x : GroupLieAlgebra (𝓘(ℝ, E)) G))) =
      algebraExpUnit (j (t • (x : GroupLieAlgebra (𝓘(ℝ, E)) G))) at ht
    rwa [map_smul] at ht
  have hdiff : unitsHomLieDifferential ρ hf = j := by
    ext x
    have hx : x ∈ (cartanRootIdeal H).toSubmodule ⊔ H.toSubmodule := by
      rw [hspan]
      trivial
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hx
    rw [map_add, map_add, hdiffN ⟨y, hy⟩, hdiffD ⟨z, hz⟩]
  refine ⟨ρ, hρ, fun x => ?_⟩
  have he := hom_exp_eq_algebraExpUnit hExp ρ
    (unitsHomLieDifferential ρ hf).toLinearMap.toContinuousLinearMap
    (hasMFDerivAt_unitsHomLieDifferential ρ hf) x
  change ρ (Exp x) = algebraExpUnit (unitsHomLieDifferential ρ hf x) at he
  rwa [hdiff] at he

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

/-- Near the identity the inverse-function logarithm is the only logarithm,
even among points outside its initial domain. -/
theorem exists_unique_local_logarithm
    (hker : ∀ a : A, NormedSpace.exp a = 1 → a = 0) :
    ∃ log : A → A, ContinuousAt log 1 ∧ log 1 = 0 ∧
      ∀ᶠ z in 𝓝 (1 : A), NormedSpace.exp (log z) = z ∧
        ∀ a, NormedSpace.exp a = z → a = log z := by
  let d : A ≃L[ℝ] A := ContinuousLinearEquiv.refl ℝ A
  have hd : HasStrictFDerivAt (NormedSpace.exp : A → A) d.toContinuousLinearMap 0 :=
    hasStrictFDerivAt_exp_zero
  let p := hd.toOpenPartialHomeomorph NormedSpace.exp
  have hzero : (0 : A) ∈ p.source := hd.mem_toOpenPartialHomeomorph_source
  have hone : (1 : A) ∈ p.target := by
    simpa only [NormedSpace.exp_zero] using hd.image_mem_toOpenPartialHomeomorph_target
  refine ⟨p.symm, p.continuousAt_symm hone, ?_, ?_⟩
  · have h := p.left_inv hzero
    simpa only [p, HasStrictFDerivAt.toOpenPartialHomeomorph_coe,
      NormedSpace.exp_zero] using h
  · filter_upwards [p.open_target.mem_nhds hone] with z hz
    have hinv : NormedSpace.exp (p.symm z) = z := p.right_inv hz
    refine ⟨hinv, fun a ha => ?_⟩
    exact exp_eq_of_local_injectivity hker p.source p.open_source p.injOn
      (p.map_target hz) (ha.trans hinv.symm)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_ExponentialRepresentationTopology
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Recovering the source topology from a faithful exponential representation -/

noncomputable section
namespace PolycyclicRecognition

open Filter Topology

variable {L G A : Type*} [NormedAddCommGroup L] [NormedSpace ℝ L]
  [FiniteDimensional ℝ L] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A] [FiniteDimensional ℝ A]

omit [FiniteDimensional ℝ L] [CompleteSpace A] in
theorem inducing_of_exponential_chart_and_local_logarithm
    (S : Subalgebra ℝ A) [IsTopologicalRing S] (chart : L ≃ₜ G) (hzero : chart 0 = 1)
    (j : L →ₗ[ℝ] S) (hj : Function.Injective j)
    (ρ : G →* Aˣ) (hρ : Continuous ρ)
    (hexp : ∀ x, (ρ (chart x) : A) = (NormedSpace.exp (j x) : S))
    (hker : ∀ a : S, NormedSpace.exp a = 1 → a = 0) :
    Topology.IsInducing ρ := by
  obtain ⟨q, hq⟩ := j.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr hj)
  obtain ⟨P, hP⟩ := S.val.toLinearMap.exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr Subtype.val_injective)
  have hqj (x : L) : q (j x) = x := DFunLike.congr_fun hq x
  have hPi (x : S) : P (x : A) = x := DFunLike.congr_fun hP x
  obtain ⟨log, hlog, hlog1, huniq⟩ := exists_unique_local_logarithm hker
  let r : Aˣ → S := fun u => P (u : A)
  have hr : Continuous r := P.continuous_of_finiteDimensional.comp Units.continuous_val
  have hr1 : r 1 = 1 := hPi 1
  let inv : Aˣ → G := fun u => chart (q (log (r u)))
  have hinv1 : inv 1 = 1 := by simp only [inv, hr1, hlog1, map_zero, hzero]
  have hcinv : ContinuousAt inv 1 := by
    exact chart.continuous.continuousAt.comp
      (q.continuous_of_finiteDimensional.continuousAt.comp
        (hlog.comp_of_eq hr.continuousAt hr1))
  have hevent : ∀ᶠ u in 𝓝 (1 : Aˣ),
      ∀ x : L, ρ (chart x) = u → inv u = chart x := by
    have ht := (hr.continuousAt.tendsto.mono_right (le_of_eq (congrArg nhds hr1))) huniq
    filter_upwards [ht] with u hu x hx
    have hxexp : NormedSpace.exp (j x) = r u := by
      have he := congrArg P (hexp x)
      rw [hPi] at he
      simpa only [r, hx] using he.symm
    have hjx := hu.2 (j x) hxexp
    change chart (q (log (r u))) = chart x
    rw [← hjx, hqj]
  have hleft : ∀ᶠ g in Filter.comap ρ (𝓝 (1 : Aˣ)), inv (ρ g) = g := by
    filter_upwards [Filter.tendsto_comap hevent] with g hg
    have h := hg (chart.symm g) (by rw [chart.apply_symm_apply])
    simpa only [chart.apply_symm_apply] using h
  have ht : Tendsto (fun g => inv (ρ g)) (Filter.comap ρ (𝓝 (1 : Aˣ))) (𝓝 (1 : G)) := by
    rw [← hinv1]
    exact hcinv.tendsto.comp Filter.tendsto_comap
  have hle : Filter.comap ρ (𝓝 (1 : Aˣ)) ≤ 𝓝 (1 : G) := by
    have ht' : Tendsto (id : G → G) (Filter.comap ρ (𝓝 (1 : Aˣ))) (𝓝 (1 : G)) :=
      ht.congr' hleft
    simpa only [Filter.tendsto_id'] using ht'
  apply (IsTopologicalGroup.isInducing_iff_nhds_one (f := ρ)).mpr
  apply le_antisymm
  · exact (hρ.continuousAt.tendsto.mono_right
      (le_of_eq (congrArg nhds (ρ.map_one)))).le_comap
  · exact hle

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
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_FaithfulTriangularRepresentation
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.abelianRealFiniteDimensional _root_.OAI.PolycyclicRecognition.abelianRealLieAbelian _root_.OAI.PolycyclicRecognition.abelianRealNormedLie _root_.OAI.PolycyclicRecognition.derivationLieSpaceFiniteDimensional _root_.OAI.PolycyclicRecognition.derivationLieSpaceRealNormed _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanRealShadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.polynomialLieIdealSubgroup_normal _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A faithful real triangular representation with nilpotent nilradical

The finite enveloping representation has real split annihilators. Applying
the already proved simultaneous-basis theorem therefore triangularizes it
over the real field, retaining injectivity and nilpotence on the nilradical.
This is the Lie-algebraic part of the Onshuus--Post realization.
-/

noncomputable section
namespace PolycyclicRecognition

open Module LieAlgebra

attribute [local instance 100] LieRing.ofAssociativeRing

variable {L : Type} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  [LieAlgebra.IsSolvable L] {n : ℕ} (T : TriangularAdjoint L n)
  (H : LieSubalgebra ℝ L) [H.IsCartanSubalgebra]

include H in
theorem exists_faithful_triangular_nilradical_representation :
    ∃ m : ℕ, ∃ j : L →ₗ⁅ℝ⁆ Matrix (Fin m) (Fin m) ℝ,
      Function.Injective j ∧ (∀ x, (j x).IsUpperTriangular) ∧
      ∀ x ∈ T.kernelIdeal, IsNilpotent (j x) := by
  let K := CartanNilshadow T H
  let bK := finBasis ℝ K
  let : NormedAddCommGroup K := NormedAddCommGroup.induced K _ bK.equivFun bK.equivFun.injective
  let : NormedSpace ℝ K := NormedSpace.induced ℝ K _ bK.equivFun
  let : RealNormedLieAlgebra K :=
    { (inferInstance : NormedAddCommGroup K), (inferInstance : LieRing K),
      (inferInstance : NormedSpace ℝ K), (inferInstance : LieAlgebra ℝ K) with }
  obtain ⟨c, hfin, hgen⟩ := exists_faithful_truncated_enveloping K (cartanNilshadow_nilpotent T H)
  let := hfin
  let Q := TruncatedEnvelopingAlgebra ℝ K c
  let ρ := solvableTruncatedRepresentation T H c
  let := LieRingModule.compLieHom Q ρ
  let := LieModule.compLieHom Q ρ
  let : LieModule.IsTriangularizable ℝ L Q :=
    ⟨solvableTruncatedRepresentation_genEigenspaces_span T H c⟩
  obtain ⟨m, b, hb⟩ := exists_upperTriangular_lieModule_basis (𝕜 := ℝ) L Q
  let j := (LinearMap.toMatrixAlgEquiv b).toLieEquiv.toLieHom.comp ρ
  refine ⟨m, j, ?_, ?_, ?_⟩
  · exact (LinearMap.toMatrixAlgEquiv b).injective.comp
      (solvableTruncatedRepresentation_injective T H c hgen)
  · exact hb
  · intro x hx
    exact (solvableTruncatedRepresentation_nilpotent T H c x hx).map
      (LinearMap.toMatrixAlgEquiv b).toRingHom

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_InducingFromHeightKernel
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Recovering topology from a quotient and its kernel -/

noncomputable section
namespace PolycyclicRecognition

open Filter Topology

variable {G Q A : Type*} [Group G] [Group Q] [Group A]
  [TopologicalSpace G] [TopologicalSpace Q] [TopologicalSpace A]
  [IsTopologicalGroup G] [IsTopologicalGroup Q] [IsTopologicalGroup A]

omit [IsTopologicalGroup Q] in
/-- Near the identity, a continuous quotient coordinate and an inducing
representation on its kernel determine the topology on the whole group. -/
theorem inducing_of_height_kernel
    (ρ : G →* A) (hρ : Continuous ρ) (π : G →* Q) (hπ : Continuous π)
    (s : C(Q, G)) (hs : ∀ q, π (s q) = q) (hsone : s 1 = 1)
    (hk : Topology.IsInducing (fun k : π.ker => ρ k))
    (f : A → Q) (hf : ContinuousAt f 1) (hf1 : f 1 = 1)
    (hfactor : ∀ g, f (ρ g) = π g) : Topology.IsInducing ρ := by
  let F := comap ρ (𝓝 (1 : A))
  have hρF : Tendsto ρ F (𝓝 (1 : A)) := tendsto_comap
  have hπF : Tendsto π F (𝓝 (1 : Q)) := by
    simpa only [Function.comp_def, hfactor, hf1] using hf.tendsto.comp hρF
  let r := quotientSectionResidual π s hs
  have hr : Tendsto r F (𝓝 (1 : π.ker)) := by
    apply hk.tendsto_nhds_iff.mpr
    have hsF : Tendsto (fun g => s (π g)) F (𝓝 (1 : G)) := by
      simpa only [Function.comp_def, hsone] using (s.continuous.tendsto (1 : Q)).comp hπF
    have hρs : Tendsto (fun g => ρ (s (π g))) F (𝓝 (1 : A)) := by
      simpa only [Function.comp_def, map_one] using (hρ.tendsto (1 : G)).comp hsF
    change Tendsto (fun g => ρ (r g)) F (𝓝 (ρ (1 : G)))
    rw [map_one]
    have hres := hρF.mul hρs.inv
    have hbase : ρ (s 1) = 1 := by rw [hsone, map_one]
    simpa only [Function.comp_def, r, quotientSectionResidual,
      map_mul, map_inv, hbase, inv_one, mul_one, map_one] using hres
  let e := quotientSectionHomeomorph π hπ s hs
  have he : Tendsto e F (𝓝 (e 1)) := by
    have heone : e 1 = (1, 1) := by
      apply Prod.ext
      · exact map_one π
      · apply Subtype.ext
        change 1 * (s (π 1))⁻¹ = 1
        rw [map_one, hsone, inv_one, mul_one]
    rw [heone]
    exact hπF.prodMk_nhds hr
  have hid : Tendsto (id : G → G) F (𝓝 (1 : G)) := by
    change Tendsto (fun g : G => g) F (𝓝 (1 : G))
    simpa only [Function.comp_def, e.symm_apply_apply] using
      e.symm.continuous.continuousAt.tendsto.comp he
  apply (IsTopologicalGroup.isInducing_iff_nhds_one (f := ρ)).mpr
  apply le_antisymm
  · exact (hρ.continuousAt.tendsto.mono_right
      (le_of_eq (congrArg nhds ρ.map_one))).le_comap
  · exact tendsto_id'.mp hid

end PolycyclicRecognition

end

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
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_RepresentationKernelAdjoint
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A faithful Lie representation detects the adjoint action of its group kernel -/

noncomputable section
namespace PolycyclicRecognition

open scoped Manifold
attribute [local instance 100] LieRing.ofAssociativeRing

variable {E G A : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace G] [ChartedSpace E G]
  [Group G] [LieGroup (𝓘(ℝ, E)) ⊤ G] [T2Space G]
  [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

theorem adjointLinearMap_eq_id_of_representation_kernel
    {Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G} (hExp : IsGroupExponential Exp)
    (j : GroupLieAlgebra (𝓘(ℝ, E)) G →ₗ⁅ℝ⁆ A) (hj : Function.Injective j)
    (ρ : G →* Aˣ) (he : ∀ x, ρ (Exp x) = algebraExpUnit (j x))
    (g : G) (hg : ρ g = 1) :
    adjointLinearMap (E := E) g = ContinuousLinearMap.id ℝ E := by
  ext x
  apply hj
  have hcurve (t : ℝ) :
      NormedSpace.exp (t • j (adjointLinearMap (E := E) g x)) =
        NormedSpace.exp (t • j x) := by
    have hc : Exp (t • adjointLinearMap (E := E) g x) =
        g * Exp (t • x) * g⁻¹ := by
      exact (congrArg Exp (map_smul (adjointLinearMap (E := E) g) t x).symm).trans
        (conjugation_exponential hExp g (t • x)).symm
    have h := congrArg ρ hc
    rw [map_mul, map_mul, map_inv, hg, inv_one, one_mul, mul_one] at h
    have hv := congrArg (fun u : Aˣ => (u : A)) ((he _).symm.trans (h.trans (he _)))
    simp only [coe_algebraExpUnit] at hv
    exact (congrArg NormedSpace.exp (j.map_smul t (adjointLinearMap (E := E) g x))).symm.trans
      (hv.trans (congrArg NormedSpace.exp (j.map_smul t x)))
  have hd₁ : HasDerivAt (fun t : ℝ => NormedSpace.exp
      (t • j (adjointLinearMap (E := E) g x))) (j (adjointLinearMap (E := E) g x)) 0 := by
    simpa only [zero_smul, NormedSpace.exp_zero, one_mul] using
      hasDerivAt_exp_smul_const (j (adjointLinearMap (E := E) g x)) (0 : ℝ)
  have hd₂ : HasDerivAt (fun t : ℝ => NormedSpace.exp (t • j x)) (j x) 0 := by
    simpa only [zero_smul, NormedSpace.exp_zero, one_mul] using
      hasDerivAt_exp_smul_const (j x) (0 : ℝ)
  rw [show (fun t : ℝ => NormedSpace.exp (t • j (adjointLinearMap (E := E) g x))) =
    (fun t : ℝ => NormedSpace.exp (t • j x)) from funext hcurve] at hd₁
  exact hd₁.unique hd₂

/-- Exponential compatibility also intertwines the full adjoint action. -/
theorem lieHom_adjoint_of_exponential_intertwining
    {Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G} (hExp : IsGroupExponential Exp)
    (j : GroupLieAlgebra (𝓘(ℝ, E)) G →ₗ⁅ℝ⁆ A)
    (ρ : G →* Aˣ) (he : ∀ x, ρ (Exp x) = algebraExpUnit (j x))
    (g : G) (x : GroupLieAlgebra (𝓘(ℝ, E)) G) :
    j (adjointLinearMap (E := E) g x) = (ρ g : A) * j x * (ρ g)⁻¹ := by
  let y : A := (ρ g : A) * j x * (ρ g)⁻¹
  have hcurve (t : ℝ) : NormedSpace.exp (t • j (adjointLinearMap (E := E) g x)) =
      NormedSpace.exp (t • y) := by
    have hc : Exp (t • adjointLinearMap (E := E) g x) = g * Exp (t • x) * g⁻¹ := by
      exact (congrArg Exp (map_smul (adjointLinearMap (E := E) g) t x).symm).trans
        (conjugation_exponential hExp g (t • x)).symm
    have h := congrArg ρ hc
    rw [map_mul, map_mul, map_inv] at h
    have hu := (he _).symm.trans (h.trans
      ((congrArg (fun u : Aˣ => ρ g * u * (ρ g)⁻¹) (he (t • x))).trans
        (algebraExpUnit_conj (ρ g) (j (t • x))).symm))
    have hv := congrArg (fun u : Aˣ => (u : A)) hu
    simp only [coe_algebraExpUnit] at hv
    have hs : (ρ g : A) * j (t • x) * (ρ g)⁻¹ = t • y := by
      calc
        (ρ g : A) * j (t • x) * (ρ g)⁻¹ = (ρ g : A) * (t • j x) * (ρ g)⁻¹ :=
          congrArg (fun a : A => (ρ g : A) * a * (ρ g)⁻¹) (j.map_smul t x)
        _ = t • y := by simp only [mul_smul_comm, smul_mul_assoc]; rfl
    exact (congrArg NormedSpace.exp (j.map_smul t (adjointLinearMap (E := E) g x))).symm.trans
      (hv.trans (congrArg NormedSpace.exp hs))
  have hd₁ : HasDerivAt (fun t : ℝ => NormedSpace.exp
      (t • j (adjointLinearMap (E := E) g x))) (j (adjointLinearMap (E := E) g x)) 0 := by
    simpa only [zero_smul, NormedSpace.exp_zero, one_mul] using
      hasDerivAt_exp_smul_const (j (adjointLinearMap (E := E) g x)) (0 : ℝ)
  have hd₂ : HasDerivAt (fun t : ℝ => NormedSpace.exp (t • y)) y 0 := by
    simpa only [zero_smul, NormedSpace.exp_zero, one_mul] using
      hasDerivAt_exp_smul_const y (0 : ℝ)
  rw [show (fun t : ℝ => NormedSpace.exp (t • j (adjointLinearMap (E := E) g x))) =
    (fun t : ℝ => NormedSpace.exp (t • y)) from funext hcurve] at hd₁
  exact hd₁.unique hd₂

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_TriangularAdjointSolvable
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Solvability from a real triangular adjoint basis -/

noncomputable section
namespace PolycyclicRecognition

open LieAlgebra

theorem TriangularAdjoint.lieAlgebra_isSolvable
    {L : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
    {n : ℕ} (T : TriangularAdjoint L n) : LieAlgebra.IsSolvable L := by
  let : LieRing.IsNilpotent T.kernelIdeal := T.kernelIdeal_nilpotent
  have hder : derivedSeries ℝ L 1 ≤ T.kernelIdeal := by
    intro z hz
    change z ∈ (derivedSeries ℝ L 1 : Submodule ℝ L) at hz
    rw [coe_derivedSeries_one_eq] at hz
    exact (Submodule.span_le.mpr (by
      rintro _ ⟨x, y, rfl⟩
      exact (T.mem_kernelIdeal _).mpr fun i => T.character_lie i x y) hz :
        z ∈ T.kernelIdeal.toSubmodule)
  obtain ⟨k, hk⟩ := IsSolvable.solvable ℝ T.kernelIdeal
  have hK : derivedSeriesOfIdeal ℝ L k T.kernelIdeal = ⊥ :=
    (LieIdeal.derivedSeries_eq_bot_iff T.kernelIdeal k).mp hk
  apply IsSolvable.mk (R := ℝ) (k := k + 1)
  apply le_antisymm _ bot_le
  change derivedSeriesOfIdeal ℝ L (k + 1) ⊤ ≤ ⊥
  rw [derivedSeriesOfIdeal_add]
  exact (derivedSeriesOfIdeal_mono hder k).trans (le_of_eq hK)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_PositiveSizeTriangularRepresentation
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Positive-size padding for the triangular representation

A trivial one-dimensional summand handles zero-dimensional Lie algebras
without a separate group-realization case.
-/

noncomputable section
namespace PolycyclicRecognition

attribute [local instance 100] LieRing.ofAssociativeRing

theorem padTriangularMatrix_apply (m : ℕ) (A : Matrix (Fin m) (Fin m) ℝ)
    (i j : Fin m ⊕ Fin 1) :
    padTriangularMatrix m A (finSumFinEquiv i) (finSumFinEquiv j) =
      Matrix.fromBlocks A 0 0 0 i j := by
  simp [padTriangularMatrix, matrixTrivialSummand, Matrix.coe_reindexAlgEquiv]

theorem padTriangularMatrix_injective (m : ℕ) : Function.Injective (padTriangularMatrix m) := by
  intro A B h
  ext i j
  have h' := congrArg (fun M => M (finSumFinEquiv (Sum.inl i))
    (finSumFinEquiv (Sum.inl j))) h
  simpa only [padTriangularMatrix_apply, Matrix.fromBlocks_apply₁₁] using h'

theorem padTriangularMatrix_upper (m : ℕ) (A : Matrix (Fin m) (Fin m) ℝ)
    (hA : A.IsUpperTriangular) : (padTriangularMatrix m A).IsUpperTriangular := by
  intro i j hji
  obtain ⟨i, rfl⟩ := (finSumFinEquiv : Fin m ⊕ Fin 1 ≃ Fin (m + 1)).surjective i
  obtain ⟨j, rfl⟩ := (finSumFinEquiv : Fin m ⊕ Fin 1 ≃ Fin (m + 1)).surjective j
  rw [padTriangularMatrix_apply]
  cases i with
  | inl i =>
    cases j with
    | inl j => exact hA hji
    | inr j => simp
  | inr i => cases j <;> simp

theorem padTriangularMatrix_nilpotent (m : ℕ) (A : Matrix (Fin m) (Fin m) ℝ)
    (hA : A.IsUpperTriangular) (hn : IsNilpotent A) : IsNilpotent (padTriangularMatrix m A) := by
  apply upperTriangular_nilpotent_of_diag_zero _ (padTriangularMatrix_upper m A hA)
  intro i
  obtain ⟨i, rfl⟩ := (finSumFinEquiv : Fin m ⊕ Fin 1 ≃ Fin (m + 1)).surjective i
  rw [padTriangularMatrix_apply]
  cases i with
  | inl i => exact upperTriangular_nilpotent_diag A hA hn i
  | inr i => simp

theorem exists_positive_faithful_triangular_representation
    {L : Type} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
    [LieAlgebra.IsSolvable L] {n : ℕ} (T : TriangularAdjoint L n) :
    ∃ m : ℕ, 0 < m ∧ ∃ j : L →ₗ⁅ℝ⁆ Matrix (Fin m) (Fin m) ℝ,
      Function.Injective j ∧ (∀ x, (j x).IsUpperTriangular) ∧
      ∀ x ∈ T.kernelIdeal, IsNilpotent (j x) := by
  obtain ⟨H, hH, _⟩ := exists_cartan_model T
  let := hH
  obtain ⟨m, j, hj, hu, hn⟩ := exists_faithful_triangular_nilradical_representation T H
  exact ⟨m + 1, Nat.succ_pos m, (padTriangularMatrix m).comp j,
    (padTriangularMatrix_injective m).comp hj,
    fun x => padTriangularMatrix_upper m (j x) (hu x),
    fun x hx => padTriangularMatrix_nilpotent m (j x) (hu x) (hn x hx)⟩

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
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_IntrinsicTriangularRepresentation
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A faithful triangular group representation without Dixmier

The intrinsic height kernel makes the Cartan construction and its overlap
faithful. A kernel element of the resulting representation acts trivially
on the Lie algebra, hence has zero intrinsic height and lies in the known
nilpotent kernel, where faithfulness follows from the finite logarithm.
-/

noncomputable section
namespace PolycyclicRecognition

open scoped Manifold Matrix.Norms.Operator
attribute [local instance 100] LieRing.ofAssociativeRing

variable {E G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MetricSpace G] [ChartedSpace E G]
  [Group G] [LieGroup (𝓘(ℝ, E)) ⊤ G] [SimplyConnectedSpace G]

theorem exists_intrinsic_faithful_triangular_representation
    {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, E)) G) a)
    (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G) (hExp : IsGroupExponential Exp) :
    ∃ m : ℕ, 0 < m ∧
      ∃ j : GroupLieAlgebra (𝓘(ℝ, E)) G →ₗ⁅ℝ⁆ Matrix (Fin m) (Fin m) ℝ,
      ∃ ρ : G →* (Matrix (Fin m) (Fin m) ℝ)ˣ,
        Function.Injective j ∧ (∀ x, (j x).IsUpperTriangular) ∧
        (∀ x ∈ T.kernelIdeal, IsNilpotent (j x)) ∧
        Continuous ρ ∧ Function.Injective ρ ∧
        ∀ x, ρ (Exp x) = algebraExpUnit (j x) := by
  let : IsTopologicalGroup G := topologicalGroup_of_lieGroup (𝓘(ℝ, E)) ⊤
  let : LocallyCompactSpace G := ChartedSpace.locallyCompactSpace E G
  let := T.lieAlgebra_isSolvable
  let W := Fin (Module.finrank ℝ (HeightSpace T.character)) → ℝ
  let q : HeightSpace T.character ≃ₗ[ℝ] W := (Module.finBasis ℝ (HeightSpace T.character)).equivFun
  obtain ⟨π, hπ, hπExp, _, _, _, hkill, _⟩ := exists_intrinsic_canonical_height_with_kernel T q hExp
  have hπc : Continuous π := hπ
  obtain ⟨H, hH, hn, _, hspan, _⟩ := exists_cartan_model T
  let := hH
  obtain ⟨F⟩ := nonempty_intrinsic_cartanFactorModel T q Exp hExp π hπc hπExp H
  obtain ⟨m, hm, j, hj, hu, hnrep⟩ := exists_positive_faithful_triangular_representation T
  have hsN : Function.Surjective F.ExpN := by
    obtain ⟨c, hc⟩ := ((nilpotentPublishedInputs.haar _ F.N).2 F.ExpN F.isExpN
      (F.N.tangent_nilpotent hn)).1
    intro n
    obtain ⟨x, hx⟩ := c.surjective n
    exact ⟨x, (hc x).symm.trans hx⟩
  have hsD : Function.Surjective F.ExpD := by
    obtain ⟨c, hc⟩ := ((nilpotentPublishedInputs.haar _ F.D).2 F.ExpD F.isExpD
      (F.D.tangent_nilpotent inferInstance)).1
    intro d
    obtain ⟨x, hx⟩ := c.surjective d
    exact ⟨x, (hc x).symm.trans hx⟩
  obtain ⟨ρ, hρ, he⟩ := F.exists_integrated_representation_of_root_preimages hExp
    (fun x hx y hxy => exponential_eq_of_mem_intrinsic_height_kernel T q Exp hExp π hπc hπExp
      (cartanRootIdeal_le_kernel H T hx) hxy) hn hspan hsN hsD j
  obtain ⟨K, ExpK, hExpK, κ, _, _, hκExp, hrange⟩ :=
    exists_closed_intrinsic_height_kernel T q Exp hExp π hπc hπExp
  obtain ⟨cK, hcK⟩ := ((nilpotentPublishedInputs.haar T.kernelIdeal K).2 ExpK hExpK
    (K.tangent_nilpotent T.kernelIdeal_nilpotent)).1
  have hfaithful : Function.Injective ρ := by
    apply (MonoidHom.ker_eq_bot_iff ρ).mp
    apply le_antisymm _ bot_le
    intro g hg
    change ρ g = 1 at hg
    change g = 1
    have had := adjointLinearMap_eq_id_of_representation_kernel hExp j hj ρ he g hg
    have hmatrix : adjointMatrixHom T.basis g = 1 := by
      change LinearMap.toMatrix T.basis T.basis
        (adjointLinearMap (E := E) g).toLinearMap = 1
      rw [had]
      exact map_one (LinearMap.toMatrixAlgEquiv T.basis)
    have hheight : π g = 1 := hkill g hmatrix
    have hgrange : g ∈ Set.range κ := by
      rw [hrange]
      exact hheight
    obtain ⟨k, hk⟩ := hgrange
    obtain ⟨v, hv⟩ := cK.surjective k
    have hexpg : Exp (K.equiv.symm v) = g := by
      rw [← hκExp, K.equiv.apply_symm_apply, ← hcK, hv, hk]
    have hexp : NormedSpace.exp (j (K.equiv.symm v)) = 1 := by
      have h := congrArg Units.val (show ρ (Exp (K.equiv.symm v)) = 1 by rw [hexpg, hg])
      simp only [he, coe_algebraExpUnit, Units.val_one] at h
      exact h
    have hz : (K.equiv.symm v : GroupLieAlgebra (𝓘(ℝ, E)) G) = 0 := by
      apply hj
      exact ((triangular_exp_eq_one_iff _ (hu _)).mp hexp).trans (map_zero j).symm
    rw [← hexpg, hz, hExp.map_zero]
  exact ⟨m, hm, j, ρ, hj, hu, hnrep, hρ, hfaithful, he⟩

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_RepresentationHeightFactor
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.CartanFactorModel.heightRay_zero _root_.OAI.PolycyclicRecognition.CartanWordModel.supportDatum_weight _root_.OAI.PolycyclicRecognition.cartanHeightSection_height _root_.OAI.PolycyclicRecognition.cartanHeightWeight_projection _root_.OAI.PolycyclicRecognition.cartanWeightDerivation_apply_root _root_.OAI.PolycyclicRecognition.cartanWeightDilation_apply _root_.OAI.PolycyclicRecognition.cartanWeightScale_add_apply _root_.OAI.PolycyclicRecognition.cartanWeightScale_zero_apply _root_.OAI.PolycyclicRecognition.derivationSemidirectHom_apply _root_.OAI.PolycyclicRecognition.exponentialHomOfDynkin_apply_exp _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.integrateNilpotentLieEquiv_apply_exp _root_.OAI.PolycyclicRecognition.nilshadowWeightDerivation_symm _root_.OAI.PolycyclicRecognition.nilshadowWeightOperator_symm _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Recovering canonical height continuously from a faithful representation -/

noncomputable section
namespace PolycyclicRecognition

open scoped Manifold
attribute [local instance 100] LieRing.ofAssociativeRing

variable {E G A W : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace G] [ChartedSpace E G]
  [Group G] [LieGroup (𝓘(ℝ, E)) ⊤ G] [T2Space G]
  [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A] [FiniteDimensional ℝ A]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

theorem exists_local_height_factor_of_representation
    {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, E)) G) a)
    {Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G} (hExp : IsGroupExponential Exp)
    (j : GroupLieAlgebra (𝓘(ℝ, E)) G →ₗ⁅ℝ⁆ A) (hj : Function.Injective j)
    (ρ : G →* Aˣ) (he : ∀ x, ρ (Exp x) = algebraExpUnit (j x))
    (π : G →* Multiplicative W) (P : (Fin a → ℝ) →L[ℝ] W)
    (hP : ∀ g, (π g).toAdd = P (fun i => Real.log (adjointMatrixHom T.basis g i i))) :
    ∃ f : Aˣ → Multiplicative W, ContinuousAt f 1 ∧ f 1 = 1 ∧ ∀ g, f (ρ g) = π g := by
  obtain ⟨p, hp⟩ := j.toLinearMap.exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr hj)
  have hpj (x : GroupLieAlgebra (𝓘(ℝ, E)) G) : p (j x) = x := LinearMap.congr_fun hp x
  let diag : Aˣ → Fin a → ℝ := fun u i =>
    T.basis.coord i (p ((u : A) * j (T.basis i) * (u⁻¹ : Aˣ)))
  have hd1 (i : Fin a) : diag 1 i = 1 := by
    change T.basis.coord i (p ((1 : A) * j (T.basis i) * 1)) = 1
    rw [one_mul, mul_one, hpj]
    simp
  have hdc (i : Fin a) : Continuous (fun u => diag u i) := by
    let c := (T.basis.coord i).comp p
    exact c.continuous_of_finiteDimensional.comp
      ((Units.continuous_val.mul continuous_const).mul
        (Units.continuous_val.comp continuous_inv))
  have hdg (g : G) (i : Fin a) : diag (ρ g) i = adjointMatrixHom T.basis g i i := by
    change T.basis.coord i (p ((ρ g : A) * j (T.basis i) * (ρ g)⁻¹)) = _
    rw [← lieHom_adjoint_of_exponential_intertwining hExp j ρ he]
    apply (congrArg (T.basis.coord i) (hpj (adjointLinearMap (E := E) g (T.basis i)))).trans
    change T.basis.repr (adjointLinearMap (E := E) g (T.basis i)) i =
      LinearMap.toMatrix T.basis T.basis (adjointLinearMap (E := E) g).toLinearMap i i
    exact (LinearMap.toMatrix_apply T.basis T.basis
      (adjointLinearMap (E := E) g).toLinearMap i i).symm
  let f : Aˣ → Multiplicative W := fun u =>
    Multiplicative.ofAdd (P (fun i => Real.log (diag u i)))
  refine ⟨f, ?_, ?_, ?_⟩
  · apply P.continuous.continuousAt.comp
    apply continuousAt_pi.mpr
    intro i
    exact (hdc i).continuousAt.log (by rw [hd1]; exact one_ne_zero)
  · apply Multiplicative.ext
    change P (fun i => Real.log (diag 1 i)) = 0
    simp only [hd1, Real.log_one]
    exact map_zero P
  · intro g
    apply Multiplicative.ext
    change P (fun i => Real.log (diag (ρ g) i)) = (π g).toAdd
    simp only [hdg]
    exact (hP g).symm

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_IntrinsicTriangularTopology
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The topology of the intrinsic triangular representation

The adjoint action recovers height continuously from the representation.
On the height kernel the nilpotent exponential chart and unique triangular
logarithm already recover the topology. Section coordinates combine them.
-/

noncomputable section
namespace PolycyclicRecognition

open scoped Manifold Matrix.Norms.Operator
attribute [local instance 100] LieRing.ofAssociativeRing

variable {E G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MetricSpace G] [ChartedSpace E G]
  [Group G] [LieGroup (𝓘(ℝ, E)) ⊤ G] [SimplyConnectedSpace G]

theorem intrinsic_triangular_representation_inducing
    {a m : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, E)) G) a)
    (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G) (hExp : IsGroupExponential Exp)
    (j : GroupLieAlgebra (𝓘(ℝ, E)) G →ₗ⁅ℝ⁆ Matrix (Fin m) (Fin m) ℝ)
    (hj : Function.Injective j) (hu : ∀ x, (j x).IsUpperTriangular)
    (ρ : G →* (Matrix (Fin m) (Fin m) ℝ)ˣ) (hρ : Continuous ρ)
    (he : ∀ x, ρ (Exp x) = algebraExpUnit (j x)) :
    Topology.IsInducing (fun g => (ρ g : Matrix (Fin m) (Fin m) ℝ)) := by
  let : IsTopologicalGroup G := topologicalGroup_of_lieGroup (𝓘(ℝ, E)) ⊤
  let W := Fin (Module.finrank ℝ (HeightSpace T.character)) → ℝ
  let q : HeightSpace T.character ≃ₗ[ℝ] W := (Module.finBasis ℝ (HeightSpace T.character)).equivFun
  obtain ⟨π, hπ, hπExp, _, _, ⟨s, hs, hs0, hsright⟩, _, P, hP⟩ :=
    exists_intrinsic_canonical_height_with_kernel T q hExp
  have hπc : Continuous π := hπ
  let sectionMap : C(Multiplicative W, G) := ⟨fun w => s w.toAdd, hs⟩
  have hsection (w : Multiplicative W) : π (sectionMap w) = w := Multiplicative.ext (hsright w.toAdd)
  have hsection1 : sectionMap 1 = 1 := hs0
  obtain ⟨N, ExpN, hExpN, κ, hκ, _, hκExp, hrange⟩ :=
    exists_closed_intrinsic_height_kernel T q Exp hExp π hπc hπExp
  let : IsTopologicalGroup N.carrier :=
    topologicalGroup_of_lieGroup (𝓘(ℝ, N.modelSpace)) ⊤
  obtain ⟨cN, hcN⟩ := ((nilpotentPublishedInputs.haar T.kernelIdeal N).2 ExpN hExpN
    (N.tangent_nilpotent T.kernelIdeal_nilpotent)).1
  let chart : N.modelSpace ≃ₜ N.carrier := cN
  let S := Matrix.blockTriangularSubalgebra ℝ ℝ (id : Fin m → Fin m)
  let J : N.modelSpace →ₗ[ℝ] S :=
    (j.toLinearMap.comp (T.kernelIdeal.incl.toLinearMap.comp N.equiv.symm.toLinearMap)).codRestrict
      S.toSubmodule (fun x => hu _)
  have hJ : Function.Injective J := by
    intro x y hxy
    apply N.equiv.symm.injective
    apply Subtype.val_injective
    apply hj
    exact congrArg Subtype.val hxy
  have hzero : cN 0 = 1 := (hcN 0).trans hExpN.map_zero
  have hmatch (x : N.modelSpace) :
      ((ρ.comp κ) (cN x) : Matrix (Fin m) (Fin m) ℝ) = (NormedSpace.exp (J x) : S) := by
    rw [realTriangularAlgebra_coe_exp]
    change (ρ (κ (cN x)) : Matrix (Fin m) (Fin m) ℝ) = NormedSpace.exp (j (N.equiv.symm x))
    have hh : κ (cN x) = Exp (N.equiv.symm x) :=
      (congrArg κ (hcN x)).trans
        ((congrArg (fun y : GroupLieAlgebra (𝓘(ℝ, N.modelSpace)) N.carrier =>
          κ (ExpN y)) (N.equiv.apply_symm_apply x)).symm.trans (hκExp (N.equiv.symm x)))
    have he' := congrArg Units.val (he (N.equiv.symm x))
    simp only [coe_algebraExpUnit] at he'
    exact (congrArg (fun g : G => (ρ g : Matrix (Fin m) (Fin m) ℝ)) hh).trans he'
  have hNind : Topology.IsInducing (ρ.comp κ) :=
    inducing_of_exponential_chart_and_local_logarithm S chart hzero J hJ
      (ρ.comp κ) (hρ.comp hκ.continuous) hmatch realTriangularAlgebra_exp_kernel
  let e := (kernelRealization π κ hκ hrange).toHomeomorph
  have hEq : (fun k : π.ker => ρ k) = (ρ.comp κ) ∘ e.symm := by
    funext k
    have hh : κ (e.symm k) = (k : G) := congrArg Subtype.val (e.apply_symm_apply k)
    exact (congrArg ρ hh).symm
  have hkind : Topology.IsInducing (fun k : π.ker => ρ k) := by
    rw [hEq]
    exact hNind.comp e.symm.isInducing
  obtain ⟨f, hf, hf1, hfactor⟩ :=
    exists_local_height_factor_of_representation T hExp j hj ρ he π P hP
  have hwhole := inducing_of_height_kernel ρ hρ π hπc sectionMap hsection hsection1
    hkind f hf hf1 hfactor
  exact Units.isOpenEmbedding_val.isInducing.comp hwhole

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_SmoothImmersionCancellation
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Recovering smoothness through an injective differential

Only the finite-dimensional vector-space target needed for exponential
coordinates is used. A linear left inverse followed by the ordinary inverse
function theorem supplies the local smooth inverse along the image.
-/

noncomputable section
namespace PolycyclicRecognition

open Filter
open scoped Manifold Topology ContDiff

variable {E V A M : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup A] [NormedSpace ℝ A] [FiniteDimensional ℝ A]
  [TopologicalSpace M] [ChartedSpace E M]

theorem contMDiffAt_of_comp_of_injective_differential
    {f : M → V} {F : V → A} {x : M} {D : V →L[ℝ] A}
    (hf : ContinuousAt f x) (hF : ContDiffAt ℝ ∞ F (f x))
    (hD : HasFDerivAt F D (f x)) (hDi : Function.Injective D)
    (hcomp : ContMDiffAt (𝓘(ℝ, E)) (𝓘(ℝ, A)) ∞ (F ∘ f) x) :
    ContMDiffAt (𝓘(ℝ, E)) (𝓘(ℝ, V)) ∞ f x := by
  obtain ⟨p, hp⟩ := D.toLinearMap.exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr hDi)
  let q : A →L[ℝ] V := p.toContinuousLinearMap
  have hqD : q.comp D = ContinuousLinearMap.id ℝ V := by
    ext v
    exact DFunLike.congr_fun hp v
  let P : V → V := q ∘ F
  have hP : ContDiffAt ℝ ∞ P (f x) := q.contDiff.contDiffAt.comp (f x) hF
  let d : V ≃L[ℝ] V := ContinuousLinearEquiv.refl ℝ V
  have hPd : HasFDerivAt P d.toContinuousLinearMap (f x) := by
    change HasFDerivAt P (ContinuousLinearMap.id ℝ V) (f x)
    rw [← hqD]
    exact q.hasFDerivAt.comp (f x) hD
  let r : V → V := hP.localInverse hPd (by simp)
  have hr : ContDiffAt ℝ ∞ r (P (f x)) := hP.to_localInverse hPd (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hleft : ∀ᶠ y in 𝓝 (f x), r (P y) = y :=
    (hP.hasStrictFDerivAt' hPd (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).eventually_left_inverse
  have hqcomp : ContMDiffAt (𝓘(ℝ, E)) (𝓘(ℝ, V)) ∞ (P ∘ f) x :=
    q.contDiff.contMDiff.contMDiffAt.comp x hcomp
  have hres : ContMDiffAt (𝓘(ℝ, E)) (𝓘(ℝ, V)) ∞ (r ∘ P ∘ f) x :=
    hr.contMDiffAt.comp x hqcomp
  apply hres.congr_of_eventuallyEq
  filter_upwards [hf.tendsto.eventually hleft] with y hy
  exact hy.symm

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_SmoothManifoldImmersionCancellation
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The local chart form of smoothness cancellation -/

noncomputable section
namespace PolycyclicRecognition

open Filter Set
open scoped Manifold Topology ContDiff

variable {E V A N M : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup A] [NormedSpace ℝ A] [FiniteDimensional ℝ A]
  [TopologicalSpace N] [ChartedSpace E N]
  [TopologicalSpace M] [ChartedSpace V M] [IsManifold (𝓘(ℝ, V)) ∞ M]

theorem contMDiffAt_of_comp_of_injective_mfderiv
    {f : N → M} {F : M → A} {x : N} {D : V →L[ℝ] A}
    (hf : ContinuousAt f x)
    (hF : ContMDiffAt (𝓘(ℝ, V)) (𝓘(ℝ, A)) ∞ F (f x))
    (hD : HasMFDerivAt (𝓘(ℝ, V)) (𝓘(ℝ, A)) F (f x) D)
    (hDi : Function.Injective D)
    (hcomp : ContMDiffAt (𝓘(ℝ, E)) (𝓘(ℝ, A)) ∞ (F ∘ f) x) :
    ContMDiffAt (𝓘(ℝ, E)) (𝓘(ℝ, V)) ∞ f x := by
  let φ := extChartAt (𝓘(ℝ, V)) (f x)
  have hinv : φ.symm (φ (f x)) = f x := φ.left_inv (mem_extChartAt_source (f x))
  have hφ : ContMDiffAt (𝓘(ℝ, V)) (𝓘(ℝ, V)) ∞ φ.symm (φ (f x)) := by
    simpa only [modelWithCornersSelf_coe, Set.range_id, contMDiffWithinAt_univ] using
      (contMDiffWithinAt_extChartAt_symm_range_self (I := 𝓘(ℝ, V)) (n := ∞) (f x))
  have hφd : HasMFDerivAt (𝓘(ℝ, V)) (𝓘(ℝ, V)) φ.symm (φ (f x))
      (ContinuousLinearMap.id ℝ V) := by
    apply (hφ.mdifferentiableAt (by simp)).hasMFDerivAt.congr_mfderiv
    have hrange : Set.range (𝓘(ℝ, V)) = (Set.univ : Set V) := by ext v; simp
    have hh := mfderivWithin_range_extChartAt_symm (I := 𝓘(ℝ, V)) (x := f x)
    rw [hrange, mfderivWithin_univ] at hh
    exact hh
  have hF' : ContDiffAt ℝ ∞ (F ∘ φ.symm) (φ (f x)) :=
    (hF.comp_of_eq hφ hinv).contDiffAt
  have hD' : HasFDerivAt (F ∘ φ.symm) D (φ (f x)) := by
    have hd : HasMFDerivAt (𝓘(ℝ, V)) (𝓘(ℝ, A)) F (φ.symm (φ (f x))) D := by
      rwa [hinv]
    have hh : HasFDerivAt (F ∘ φ.symm) (D.comp (ContinuousLinearMap.id ℝ V))
        (φ (f x)) := (hd.comp _ hφd).hasFDerivAt
    simpa only [ContinuousLinearMap.comp_id] using hh
  have hc : ContinuousAt (φ ∘ f) x := (continuousAt_extChartAt (f x)).comp hf
  have heq : (F ∘ φ.symm) ∘ (φ ∘ f) =ᶠ[𝓝 x] F ∘ f := by
    filter_upwards [hf.preimage_mem_nhds (extChartAt_source_mem_nhds (I := 𝓘(ℝ, V)) (f x))]
      with y hy
    change F (φ.symm (φ (f y))) = F (f y)
    rw [φ.left_inv hy]
  apply contMDiffAt_iff_target.mpr
  refine ⟨hf, ?_⟩
  exact contMDiffAt_of_comp_of_injective_differential hc hF' hD' hDi
    (hcomp.congr_of_eventuallyEq heq)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_SmoothFaithfulRepresentation
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Testing smoothness in faithful group coordinates

An injective differential at the identity suffices to test smoothness:
translate to the identity and apply local chart cancellation.
-/

noncomputable section
namespace PolycyclicRecognition

open scoped Manifold ContDiff

variable {EN EG N G A : Type*}
  [NormedAddCommGroup EN] [NormedSpace ℝ EN]
  [NormedAddCommGroup EG] [NormedSpace ℝ EG] [FiniteDimensional ℝ EG]
  [TopologicalSpace N] [ChartedSpace EN N]
  [TopologicalSpace G] [ChartedSpace EG G] [Group G]
  [IsTopologicalGroup G] [LieGroup (𝓘(ℝ, EG)) ⊤ G]
  [NormedRing A] [NormedAlgebra ℝ A] [FiniteDimensional ℝ A]

theorem contMDiffAt_of_unitsHom_injective_differential
    (ρ : G →* Aˣ)
    (hρ : ContMDiff (𝓘(ℝ, EG)) (𝓘(ℝ, A)) ∞ (fun g => (ρ g : A)))
    (D : EG →L[ℝ] A)
    (hD : HasMFDerivAt (𝓘(ℝ, EG)) (𝓘(ℝ, A)) (fun g => (ρ g : A)) 1 D)
    (hDi : Function.Injective D)
    {f : N → G} {x : N} (hf : ContinuousAt f x)
    (hcomp : ContMDiffAt (𝓘(ℝ, EN)) (𝓘(ℝ, A)) ∞ (fun y => (ρ (f y) : A)) x) :
    ContMDiffAt (𝓘(ℝ, EN)) (𝓘(ℝ, EG)) ∞ f x := by
  let g := f x
  let f' : N → G := fun y => g⁻¹ * f y
  let F : G → A := fun z => (ρ z : A)
  have hf' : ContinuousAt f' x := continuousAt_const.mul hf
  have hz : f' x = 1 := inv_mul_cancel g
  have hF' : ContMDiffAt (𝓘(ℝ, EG)) (𝓘(ℝ, A)) ∞ F (f' x) := by
    rw [hz]
    exact hρ 1
  have hD' : HasMFDerivAt (𝓘(ℝ, EG)) (𝓘(ℝ, A)) F (f' x) D := by
    rw [hz]
    exact hD
  have hc : ContMDiffAt (𝓘(ℝ, EN)) (𝓘(ℝ, A)) ∞ (F ∘ f') x := by
    have h := (ContinuousLinearMap.mul ℝ A (ρ g⁻¹ : A)).contDiff.contMDiff.contMDiffAt.comp
      x hcomp
    have heq : (fun y => (ρ g⁻¹ : A) * (ρ (f y) : A)) = F ∘ f' := by
      funext y
      simp only [Function.comp_apply, F, f', map_mul, Units.val_mul]
    change ContMDiffAt (𝓘(ℝ, EN)) (𝓘(ℝ, A)) ∞
      (fun y => (ρ g⁻¹ : A) * (ρ (f y) : A)) x at h
    rwa [heq] at h
  have hs := contMDiffAt_of_comp_of_injective_mfderiv hf' hF' hD' hDi hc
  have hout := (contMDiff_mul_left (I := 𝓘(ℝ, EG)) (a := g)).contMDiffAt.comp x hs
  have heq : (fun z => g * z) ∘ f' = f := by
    funext y
    exact mul_inv_cancel_left g (f y)
  rwa [heq] at hout

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_IntrinsicExponentialSmooth
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Smoothness of the intrinsic real triangular exponential

The inducing representation first proves continuity. Smooth cancellation
then recovers the actual manifold regularity from the matrix exponential.
No global exponential chart is used.
-/

noncomputable section
namespace PolycyclicRecognition

open scoped Manifold ContDiff Matrix.Norms.Operator
attribute [local instance 100] LieRing.ofAssociativeRing

variable {E G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MetricSpace G] [ChartedSpace E G]
  [Group G] [LieGroup (𝓘(ℝ, E)) ⊤ G] [SimplyConnectedSpace G]

theorem intrinsic_exponential_contMDiff_oai
    {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, E)) G) a)
    (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G) (hExp : IsGroupExponential Exp) :
    ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) ∞ (fun x : E => Exp x) := by
  let : IsTopologicalGroup G := topologicalGroup_of_lieGroup (𝓘(ℝ, E)) ⊤
  obtain ⟨m, _, j, ρ, hj, hu, _, hρ, _, he⟩ :=
    exists_intrinsic_faithful_triangular_representation T Exp hExp
  have hind := intrinsic_triangular_representation_inducing T Exp hExp j hj hu ρ hρ he
  let J : E →L[ℝ] Matrix (Fin m) (Fin m) ℝ := j.toLinearMap.toContinuousLinearMap
  have hcoords (x : E) : (ρ (Exp x) : Matrix (Fin m) (Fin m) ℝ) =
      NormedSpace.exp (J x) := by
    exact congrArg Units.val (he x)
  have hc : Continuous (fun x : E => Exp x) := by
    apply hind.continuous_iff.mpr
    change Continuous (fun x : E => (ρ (Exp x) : Matrix (Fin m) (Fin m) ℝ))
    rw [show (fun x : E => (ρ (Exp x) : Matrix (Fin m) (Fin m) ℝ)) =
      (fun x => NormedSpace.exp (J x)) from funext hcoords]
    exact NormedSpace.exp_continuous.comp J.continuous
  have hsρ := contMDiff_of_continuous_unitsHom hExp ρ (Units.continuous_val.comp hρ)
  have hjρ : unitsHomLieDifferential ρ hsρ = j := by
    apply LieHom.ext
    intro x
    apply unitsHomLieDifferential_eq_of_exponential_line hExp ρ hsρ x (j x)
    intro t
    simpa only [map_smul] using he (t • x)
  have hdρ := hasMFDerivAt_unitsHomLieDifferential ρ hsρ
  rw [hjρ] at hdρ
  have hreg : ContDiff ℝ ∞ (fun y : E => NormedSpace.exp (J y)) := by
    apply contDiff_iff_contDiffAt.mpr
    intro x
    exact (NormedSpace.exp_analytic (𝕂 := ℝ) (J x)).contDiffAt.comp x J.contDiff.contDiffAt
  have hscomp := hreg.contMDiff
  rw [← show (fun x : E => (ρ (Exp x) : Matrix (Fin m) (Fin m) ℝ)) =
    (fun x => NormedSpace.exp (J x)) from funext hcoords] at hscomp
  intro x
  exact contMDiffAt_of_unitsHom_injective_differential ρ hsρ J hdρ hj
    hc.continuousAt (hscomp x)

end PolycyclicRecognition

end

end OAI
end

theorem solution : type_of% @OAI.PolycyclicRecognition.intrinsic_exponential_contMDiff_oai := @OAI.PolycyclicRecognition.intrinsic_exponential_contMDiff_oai
