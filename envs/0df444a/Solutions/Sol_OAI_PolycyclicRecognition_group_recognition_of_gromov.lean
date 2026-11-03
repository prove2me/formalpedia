-- Prove2me | solution 1 for OAI.PolycyclicRecognition.group_recognition_of_gromov
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-03T01:03:47.480798+00:00
-- url     : https://prove2.me/submissions/cf929468-2470-44c4-bf9a-07da31d2d09b

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_PolycyclicRecognition
import Definitions.Def_OAIQ093D023
import Theorems.Thm_OAI_PolycyclicRecognition_CartanWordModel_exists_uniform_height_intrinsic
import Theorems.Thm_OAI_PolycyclicRecognition_cornulierTesseraModelInput
import Theorems.Thm_OAI_PolycyclicRecognition_dekimpeLatticeRealizationInput
import Theorems.Thm_OAI_PolycyclicRecognition_exists_intrinsic_smooth_coordinates
import Theorems.Thm_OAI_PolycyclicRecognition_isPolycyclic_finitelyGenerated_discrete_of_linear_nilpotent_kernel
import Theorems.Thm_OAI_PolycyclicRecognition_recognition_and_lattice_of_uniform_normalized_height_proved
import Theorems.Thm_OAI_PolycyclicRecognition_trace_ad_eq_zero_of_intrinsic_kernel_haar

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
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_LogDistortion
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Logarithmic distortion from polynomially corrected contraction

The nilpotent part of a real weight action introduces a polynomial factor.
It is absorbed by an additional logarithmic conjugating time. These lemmas
retain that factor instead of assuming a semisimple action.
-/

noncomputable section

open Filter
open scoped Topology

namespace PolycyclicRecognition

variable {G : Type*} [Group G] [PseudoMetricSpace G] [IsIsometricSMul G G]

/-- Product lengths in a left invariant metric. -/
theorem dist_one_mul_le (a b : G) : dist 1 (a * b) ≤ dist 1 a + dist 1 b := by
  calc
    dist 1 (a * b) ≤ dist 1 a + dist a (a * b) := dist_triangle _ _ _
    _ = _ := by simpa only [mul_one] using congrArg (dist 1 a + ·) (dist_mul_left a 1 b)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_ContinuousFlowDistortion
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Continuous contracting flows

The local metric bounds in logarithmic distortion follow from continuity
and compactness. A continuous one-parameter homomorphism has at most linear
metric growth, so no differentiability estimate needs to be assumed here.
-/

noncomputable section

namespace PolycyclicRecognition

open Set Metric

variable {G : Type*} [Group G] [PseudoMetricSpace G] [IsIsometricSMul G G]

theorem dist_one_pow_le (g : G) (n : ℕ) : dist 1 (g ^ n) ≤ (n : ℝ) * dist 1 g := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ]
    calc
      dist 1 (g ^ n * g) ≤ dist 1 (g ^ n) + dist 1 g := dist_one_mul_le _ _
      _ ≤ (n : ℝ) * dist 1 g + dist 1 g := add_le_add ih le_rfl
      _ = _ := by push_cast <;> ring

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
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_LinearMetricChains
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instNonemptyBases _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_nonempty _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Linear metric chains and coarse Lipschitz bounds

An explicit large-scale geodesic condition allows one to sum local bounds
along a chain. For continuous homomorphisms out of proper metric groups,
the local bound comes from compactness. This is the elementary metric step
in the proper cocompact homomorphism form of the Milnor--Švarc argument.
-/

noncomputable section

namespace PolycyclicRecognition

open Metric Set

variable {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]

variable {G H : Type*} [Group G] [Group H] [MetricSpace G] [MetricSpace H]
  [IsIsometricSMul G G] [IsIsometricSMul H H]

/-- A continuous homomorphism out of a proper metric group has uniformly
bounded image displacement on any bounded source step. -/
theorem continuousHom_bounded_metric_steps [ProperSpace G]
    (f : G →* H) (hf : Continuous f) (R : ℝ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ x y, dist x y ≤ R → dist (f x) (f y) ≤ D := by
  obtain ⟨D, hD⟩ := (isCompact_closedBall (1 : G) R).bddAbove_image
    (continuous_const.dist hf).continuousOn
  refine ⟨max D 0, le_max_right _ _, fun x y hxy => ?_⟩
  have hmem : x⁻¹ * y ∈ closedBall (1 : G) R := by
    simpa only [mem_closedBall, dist_comm (x⁻¹ * y), dist_one_groupDifference] using hxy
  have hb : dist (1 : H) (f (x⁻¹ * y)) ≤ D := hD (mem_image_of_mem _ hmem)
  rw [map_mul, map_inv, dist_one_groupDifference] at hb
  exact hb.trans (le_max_left _ _)

/-- The homomorphism's affine bound requires only compactness and the
explicit linear chains; no global differentiability estimate is needed. -/
theorem continuousHom_coarseLipschitz [ProperSpace G] (C : LinearMetricChains G)
    (f : G →* H) (hf : Continuous f) :
    ∃ K B : ℝ, 0 ≤ K ∧ 0 ≤ B ∧
      ∀ x y, dist (f x) (f y) ≤ K * dist x y + B := by
  obtain ⟨D, hD, hstep⟩ := continuousHom_bounded_metric_steps f hf C.step
  exact ⟨D * C.slope, D * C.error,
    mul_nonneg hD C.slope_nonneg, mul_nonneg hD C.error_nonneg,
    C.coarseLipschitz f hD hstep⟩

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_Polycyclic
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Compatibility with OpenAI's Mathlib (d13f23b): its instance that `comap` keeps a finite index
(`GroupTheory/Index.lean`). -/

namespace OAI

/-!
# Polycyclic and virtually polycyclic groups

We use the existing concrete cyclic subnormal series, including normality and
cyclicity of each quotient. Neither polycyclicity nor virtual polycyclicity is
an unspecified property parameter.
-/

namespace PolycyclicRecognition

open ChromaticCyclic

variable (G : Type*) [Group G]

variable {G} {H : Type*} [Group H]

/-- Subgroups of polycyclic groups are polycyclic, by pulling back the cyclic series. -/
theorem IsPolycyclic.of_injective (hG : IsPolycyclic G)
    (f : H →* G) (hf : Function.Injective f) : IsPolycyclic H := by
  obtain ⟨n, ⟨c⟩⟩ := hG
  refine ⟨n, ?_⟩
  have hc := c.comap f
  rw [MonoidHom.comap_bot, (MonoidHom.ker_eq_bot_iff f).mpr hf,
    Subgroup.comap_top] at hc
  exact ⟨hc⟩

/-- A polycyclic group is virtually polycyclic, using the whole group. -/
theorem IsPolycyclic.isVirtuallyPolycyclic (hG : IsPolycyclic G) :
    IsVirtuallyPolycyclic G := by
  refine ⟨⊤, inferInstance, ?_⟩
  exact hG.of_injective (⊤ : Subgroup G).subtype Subtype.val_injective

end PolycyclicRecognition

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Lattices_UniformLatticeMetric
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Uniform lattice metric comparison

A discrete subgroup with a compact set of right-coset representatives is a
uniform lattice. Its inclusion has a uniformly close section. This gives
the discrete-group coarse comparison required in the duality endgame from
a metric quasi-isometry to the ambient Lie group. Neither finite generation
nor a recognition conclusion is built into the lattice definition.
-/

noncomputable section

namespace PolycyclicRecognition

open Metric

variable {G : Type*} [Group G]

variable [MetricSpace G] [IsTopologicalGroup G] [IsIsometricSMul G G]

omit [IsTopologicalGroup G] in
/-- Compactness of a fundamental cover gives a uniform distance to the
lattice. -/
theorem IsUniformLattice.exists_covering_radius {Λ : Subgroup G}
    (hΛ : IsUniformLattice Λ) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ g : G, ∃ γ : Λ, dist g (γ : G) ≤ R := by
  obtain ⟨K, hK, hcover⟩ := hΛ.2
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall (1 : G)
  refine ⟨max R 0, le_max_right _ _, fun g => ?_⟩
  obtain ⟨γ, k, hk, rfl⟩ := hcover g
  refine ⟨γ, ?_⟩
  have hkR : dist k 1 ≤ R := hR hk
  calc
    dist ((γ : G) * k) (γ : G) = dist k 1 := by
      simpa only [mul_one] using dist_mul_left (γ : G) k 1
    _ ≤ max R 0 := hkR.trans (le_max_left _ _)

omit [IsIsometricSMul G G] in
/-- A discrete subgroup has finite metric balls in a proper ambient group. -/
theorem IsUniformLattice.finite_closedBall [ProperSpace G] {Λ : Subgroup G}
    (hΛ : IsUniformLattice Λ) (R : ℝ) :
    (closedBall (1 : Λ) R).Finite := by
  let := hΛ.1
  have hclosed : IsClosed (Λ : Set G) := Subgroup.isClosed_of_discrete
  have hcompact := hclosed.isClosedEmbedding_subtypeVal.isCompact_preimage
    (isCompact_closedBall (1 : G) R)
  exact hcompact.finite_of_discrete

omit [IsTopologicalGroup G] in
/-- A uniformly close lattice section has explicit coarse Lipschitz bounds. -/
theorem IsUniformLattice.exists_metric_section {Λ : Subgroup G}
    (hΛ : IsUniformLattice Λ) :
    ∃ (r : G → Λ) (R : ℝ), 0 ≤ R ∧
      (∀ g, dist g (r g : G) ≤ R) ∧
      (∀ x y, dist (r x) (r y) ≤ dist x y + (R + R)) := by
  obtain ⟨R, hR, hcover⟩ := hΛ.exists_covering_radius
  choose r hr using hcover
  refine ⟨r, R, hR, hr, fun x y => ?_⟩
  change dist (r x : G) (r y : G) ≤ _
  calc
    dist (r x : G) (r y : G) ≤
        dist (r x : G) x + dist x y + dist y (r y : G) := dist_triangle4 _ _ _ _
    _ ≤ R + dist x y + R := by
      gcongr
      exact (dist_comm (r x : G) x).trans_le (hr x)
      exact hr y
    _ = dist x y + (R + R) := by ring

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Lattices_UniformLatticeQuotient
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Compact quotient and compact fundamental cover

The concrete uniform lattice definition agrees with the usual compact-coset-
quotient definition. Left and right cosets are interchanged by inversion.
-/

noncomputable section

namespace PolycyclicRecognition

open Set
open scoped Topology

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- In a locally compact group, a compact coset quotient admits a compact
fundamental cover. The finite subcover consists of images of relatively
compact neighborhoods. -/
theorem isUniformLattice_of_compact_quotient [LocallyCompactSpace G]
    (Λ : Subgroup G) [DiscreteTopology Λ] [CompactSpace (G ⧸ Λ)] :
    IsUniformLattice Λ := by
  let q : G → G ⧸ Λ := QuotientGroup.mk
  choose K hK hneigh using fun x : G => exists_compact_mem_nhds x
  have hxK (x : G) : x ∈ interior (K x) := mem_interior_iff_mem_nhds.mpr (hneigh x)
  have hcover : (univ : Set (G ⧸ Λ)) ⊆ ⋃ x : G, q '' interior (K x) := by
    intro y _
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
    exact mem_iUnion.mpr ⟨x, ⟨x, hxK x, rfl⟩⟩
  obtain ⟨F, hF⟩ := isCompact_univ.elim_finite_subcover
    (fun x : G => q '' interior (K x))
    (fun x => QuotientGroup.isOpenMap_coe _ isOpen_interior) hcover
  let L : Set G := ⋃ x ∈ F, K x
  have hL : IsCompact L := F.isCompact_biUnion (fun x _ => hK x)
  refine ⟨inferInstance, Inv.inv '' L, hL.image continuous_inv, ?_⟩
  intro g
  obtain ⟨x, hx, k, hk, hkg⟩ := mem_iUnion₂.mp (hF (mem_univ (q g⁻¹)))
  have hrel : k⁻¹ * g⁻¹ ∈ Λ := QuotientGroup.eq.mp hkg
  refine ⟨⟨g * k, ?_⟩, k⁻¹, ⟨k, ?_, rfl⟩, ?_⟩
  · simpa only [mul_inv_rev, inv_inv] using Λ.inv_mem hrel
  · exact mem_iUnion₂.mpr ⟨x, hx, interior_subset hk⟩
  · simp [mul_assoc]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Lattices_SolvableLatticeModel
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Solvable-lattice realization

K. Dekimpe, *Solvable Lie Algebras, Lie Groups and Polynomial Structures*,
Compositio Mathematica 121 (2000), 183–204, Theorem 4.1, p.199,
DOI 10.1023/A:1001738932743, gives a finite-index subgroup of a
polycyclic-by-finite group as a uniform lattice in a connected simply
connected solvable Lie group. We use only this consequence, omitting the
additional equality with the Fitting subgroup and omitting normality.

The realization predicate specifies a finite-dimensional smooth Lie structure
and a discrete lattice with compact coset quotient.
-/

noncomputable section

namespace PolycyclicRecognition

open scoped Manifold

attribute [instance] SimplyConnectedSolvableLieModel.normedAddCommGroup
  SimplyConnectedSolvableLieModel.normedSpace SimplyConnectedSolvableLieModel.finiteDimensional
  SimplyConnectedSolvableLieModel.topologicalSpace SimplyConnectedSolvableLieModel.chartedSpace
  SimplyConnectedSolvableLieModel.group SimplyConnectedSolvableLieModel.lieGroup
  SimplyConnectedSolvableLieModel.t2Space SimplyConnectedSolvableLieModel.simplyConnectedSpace
  SimplyConnectedSolvableLieModel.secondCountableTopology
  SimplyConnectedSolvableLieModel.solvable

/-- Restate the published realization using the equivalent compact-cover
definition used by the metric lattice lemmas. -/
theorem exists_uniform_solvable_lattice_of_virtuallyPolycyclic
    (dekimpe : DekimpeLatticeRealizationInput)
    (P : Type) [Group P] (hP : IsVirtuallyPolycyclic P) :
    ∃ Γ : Subgroup P, Γ.FiniteIndex ∧
      ∃ (S : SimplyConnectedSolvableLieModel) (Λ : Subgroup S.carrier),
        IsUniformLattice Λ ∧ Nonempty (Γ ≃* Λ) := by
  obtain ⟨Γ, hΓ, S, Λ, hdisc, hcompact, e⟩ := dekimpe P hP
  let := hdisc
  let := hcompact
  let : IsTopologicalGroup S.carrier :=
    topologicalGroup_of_lieGroup (𝓘(ℝ, S.modelSpace)) ⊤
  let : LocallyCompactSpace S.carrier :=
    Manifold.locallyCompact_of_finiteDimensional (𝓘(ℝ, S.modelSpace))
  exact ⟨Γ, hΓ, S, Λ, isUniformLattice_of_compact_quotient Λ, e⟩

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

namespace ProperChainMetric

variable {G : Type*} [Group G] [TopologicalSpace G] (d : ProperChainMetric G)

theorem proper_compatibleMetric : letI := d.compatibleMetric; ProperSpace G := by
  rw [d.compatibleMetric_eq]
  exact d.proper

theorem isometric_compatibleMetric : letI := d.compatibleMetric; IsIsometricSMul G G := by
  rw [d.compatibleMetric_eq]
  exact d.leftInvariant

end ProperChainMetric

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
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_MinimizingLieMetric
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The published minimizing metric on the connected Lie model

The sole input is the connected Lie-group specialization of J. M. Lee,
*Introduction to Riemannian Manifolds*, second edition, GTM 176 (2018):
Lemma 3.10(b), p. 68 constructs a left-invariant Riemannian metric;
Problem 6-12(c), p. 188 gives completeness of homogeneous metrics;
Corollary 6.21, p. 170 gives minimizing segments; Problem 6-14(a), p. 188
(or the compact exponential-ball argument in Lemma 6.18) gives properness.
Only the resulting metric and normalized minimizing paths are retained.
The large-scale chain property is proved here rather than included in the
published hypothesis.
-/

noncomputable section
namespace PolycyclicRecognition

open Set

namespace ProperMinimizingMetric

variable {G : Type*} [Group G] [TopologicalSpace G] (d : ProperMinimizingMetric G)

theorem minimizing_compatibleMetric :
    letI := d.toProperChainMetric.compatibleMetric
    ∀ g : G, ∃ γ : ℝ → G, γ 0 = 1 ∧ γ 1 = g ∧
      ∀ t ∈ Icc (0 : ℝ) 1, ∀ u ∈ Icc (0 : ℝ) 1,
        dist (γ t) (γ u) ≤ dist 1 g * |t - u| := by
  rw [d.toProperChainMetric.compatibleMetric_eq]
  exact d.minimizing

end ProperMinimizingMetric
end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_Packing
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Packing estimates and intrinsic word balls

This is the finite counting step in Lemma `height-kernel-growth` of
*Quasi-isometric recognition of virtually polycyclic groups*. A metric cover of
orbit points and a bound on the number of source points in a small target ball
give a cardinal bound on the original finite set. Applying this to intrinsic
word balls does not require the subgroup to be undistorted in an ambient group.
-/

namespace PolycyclicRecognition

universe u v

section Packing

variable {H : Type u} {X : Type v} [PseudoMetricSpace X]

/-- Count a finite set using a finite metric-ball cover and bounds on each fiber
of the cover. The balls may overlap. -/
theorem card_le_cover_mul [DecidableEq H] [DecidableEq X]
    (S : Finset H) (f : H → X) (centers : Finset X) (radius : ℝ) (M : ℕ)
    (hcover : ∀ h ∈ S, ∃ c ∈ centers, dist (f h) c ≤ radius)
    (hfiber : ∀ c ∈ centers, (S.filter fun h => dist (f h) c ≤ radius).card ≤ M) :
    S.card ≤ centers.card * M := by
  classical
  have hsubset : S ⊆ centers.biUnion (fun c => S.filter fun h => dist (f h) c ≤ radius) := by
    intro h hh
    obtain ⟨c, hc, hdist⟩ := hcover h hh
    exact Finset.mem_biUnion.mpr ⟨c, hc, Finset.mem_filter.mpr ⟨hh, hdist⟩⟩
  exact (Finset.card_le_card hsubset).trans
    (Finset.card_biUnion_le_card_mul centers _ M hfiber)

/-- A uniform bound on all finite subsets lying over a target ball can be used
for every finite source set. -/
theorem card_le_cover_mul_of_bounded_multiplicity [DecidableEq H] [DecidableEq X]
    (S : Finset H) (f : H → X) (centers : Finset X) (radius : ℝ) (M : ℕ)
    (hcover : ∀ h ∈ S, ∃ c ∈ centers, dist (f h) c ≤ radius)
    (hmultiplicity : ∀ (c : X) (A : Finset H),
      (∀ h ∈ A, dist (f h) c ≤ radius) → A.card ≤ M) :
    S.card ≤ centers.card * M := by
  apply card_le_cover_mul S f centers radius M hcover
  intro c _
  apply hmultiplicity c
  intro h hh
  exact (Finset.mem_filter.mp hh).2

end Packing

end PolycyclicRecognition

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_CoarseMultiplicity
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Uniform multiplicity of a coarse embedding

The recognition proof counts points in an intrinsic subgroup word ball using
the ambient group's fixed word metric. Its lower quasi-isometry bound gives a
uniform bound for the number of points mapping into a fixed-radius target ball.
No undistortion of the subgroup is used.
-/

namespace PolycyclicRecognition

theorem exists_uniform_ball_multiplicity
    {H X : Type*} [Group H] [MetricSpace H] [PseudoMetricSpace X]
    [IsIsometricSMul H H] (f : H → X)
    (hfinite : ∀ R : ℝ, (Metric.closedBall (1 : H) R).Finite)
    {K C r : ℝ} (hK : 0 ≤ K)
    (hlower : ∀ x y, dist x y ≤ K * dist (f x) (f y) + C) :
    ∃ M : ℕ, ∀ (c : X) (A : Finset H),
      (∀ h ∈ A, dist (f h) c ≤ r) → A.card ≤ M := by
  classical
  let R := K * (r + r) + C
  let ball := (hfinite R).toFinset
  refine ⟨ball.card, fun c A hA => ?_⟩
  by_cases hne : A.Nonempty
  · obtain ⟨a, ha⟩ := hne
    have hinj : Function.Injective (fun h : H => a⁻¹ * h) := fun _ _ h => mul_left_cancel h
    have himage : A.image (fun h => a⁻¹ * h) ⊆ ball := by
      intro h hh
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hh
      apply (hfinite R).mem_toFinset.mpr
      change dist (a⁻¹ * b) 1 ≤ R
      have hd : dist (f a) (f b) ≤ r + r := by
        exact (dist_triangle (f a) c (f b)).trans
          (add_le_add (hA a ha) (by simpa only [dist_comm] using hA b hb))
      have hs := (hlower a b).trans
        (add_le_add (mul_le_mul_of_nonneg_left hd hK) le_rfl)
      have heq : dist (a⁻¹ * b) 1 = dist a b := by
        rw [dist_comm]
        simpa only [mul_one, mul_inv_cancel_left] using
          (dist_mul_left a (1 : H) (a⁻¹ * b)).symm
      rwa [heq]
    simpa only [Finset.card_image_of_injective A hinj] using Finset.card_le_card himage
  · simp only [Finset.not_nonempty_iff_eq_empty.mp hne, Finset.card_empty, Nat.zero_le]

end PolycyclicRecognition

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_MeasurePacking
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Counting separated endpoints using Haar volume

Disjoint fixed-radius balls around separated endpoints have the same positive
Haar mass. A polynomial-volume region containing their thickening therefore
gives a polynomial cardinal bound. This is the counting step of the path
packing lemma, separated from its Lie-coordinate estimate.
-/

namespace PolycyclicRecognition

open MeasureTheory MeasureTheory.Measure Metric Set
open scoped ENNReal

variable {G : Type*} [Group G] [MetricSpace G] [MeasurableSpace G]
  [BorelSpace G] [MeasurableMul G] [IsIsometricSMul G G]

omit [BorelSpace G] in
theorem measure_ball_eq_identity (μ : Measure G) [IsMulLeftInvariant μ]
    (x : G) (r : ℝ) : μ (ball x r) = μ (ball (1 : G) r) := by
  have h := measure_preimage_mul μ x (ball x r)
  rw [preimage_mul_left_ball, inv_mul_cancel] at h
  exact h.symm

/-- The Haar volume of a thickening bounds the number of separated centers. -/
theorem separated_card_mul_ball_le (μ : Measure G) [IsMulLeftInvariant μ]
    (s : Finset G) (r : ℝ) (region : Set G)
    (hsep : ∀ x ∈ s, ∀ y ∈ s, x ≠ y → r + r ≤ dist x y)
    (hthick : ∀ x ∈ s, ball x r ⊆ region) :
    (s.card : ℝ≥0∞) * μ (ball (1 : G) r) ≤ μ region := by
  classical
  have hd : Set.Pairwise (s : Set G) (fun x y => Disjoint (ball x r) (ball y r)) := by
    intro x hx y hy hxy
    exact ball_disjoint_ball (hsep x hx y hy hxy)
  calc
    (s.card : ℝ≥0∞) * μ (ball (1 : G) r) = μ (⋃ x ∈ s, ball x r) := by
      rw [measure_biUnion_finset hd (fun x _ => measurableSet_ball)]
      simp only [measure_ball_eq_identity, Finset.sum_const, nsmul_eq_mul]
    _ ≤ μ region := measure_mono (iUnion₂_subset hthick)

/-- The same maximal-packing argument applies to arbitrary endpoint sets. A
bound on their finite separated subsets already supplies a finite net; no
measurability or compactness of the endpoint set is needed. -/
theorem finite_separated_cover_set_of_bound {X : Type*} [PseudoMetricSpace X]
    (S : Set X) {r : ℝ} (hr : 0 ≤ r) (N : ℕ)
    (hbound : ∀ t : Finset X, (↑t : Set X) ⊆ S →
      (∀ x ∈ t, ∀ y ∈ t, x ≠ y → r < dist x y) → t.card ≤ N) :
    ∃ t : Finset X, (↑t : Set X) ⊆ S ∧
      (∀ x ∈ t, ∀ y ∈ t, x ≠ y → r < dist x y) ∧ t.card ≤ N ∧
      ∀ x ∈ S, ∃ y ∈ t, dist x y ≤ r := by
  classical
  let P (k : ℕ) := ∃ t : Finset X, (↑t : Set X) ⊆ S ∧
    (∀ x ∈ t, ∀ y ∈ t, x ≠ y → r < dist x y) ∧ t.card = k
  have hP0 : P 0 := ⟨∅, by simp, by simp, by simp⟩
  obtain ⟨t, hts, hsep, hcard⟩ := Nat.findGreatest_spec (Nat.zero_le N) hP0
  have hmax (u : Finset X) (hu : (↑u : Set X) ⊆ S)
      (husep : ∀ x ∈ u, ∀ y ∈ u, x ≠ y → r < dist x y) : u.card ≤ t.card := by
    rw [hcard]
    exact Nat.le_findGreatest (hbound u hu husep) ⟨u, hu, husep, rfl⟩
  refine ⟨t, hts, hsep, hbound t hts hsep, ?_⟩
  intro x hx
  by_contra hno
  have hfar : ∀ y ∈ t, r < dist x y := by
    intro y hy
    exact lt_of_not_ge (fun h => hno ⟨y, hy, h⟩)
  have hxt : x ∉ t := by
    intro hxt
    exact (not_lt_of_ge hr) (by simpa only [dist_self] using hfar x hxt)
  have hins : (↑(insert x t) : Set X) ⊆ S := by
    intro y hy
    rcases Finset.mem_insert.mp hy with hxy | hyt
    · exact hxy ▸ hx
    · exact hts hyt
  have hsepins : ∀ a ∈ insert x t, ∀ b ∈ insert x t, a ≠ b → r < dist a b := by
    intro a ha b hb hab
    rcases Finset.mem_insert.mp ha with hax | hat
    · subst a
      rcases Finset.mem_insert.mp hb with hbx | hbt
      · exact (hab hbx.symm).elim
      · exact hfar b hbt
    · rcases Finset.mem_insert.mp hb with hbx | hbt
      · subst b
        simpa only [dist_comm] using hfar a hat
      · exact hsep a hat b hbt hab
  have h := hmax (insert x t) hins hsepins
  rw [Finset.card_insert_of_notMem hxt] at h
  omega

end PolycyclicRecognition

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
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_RiemannianChartLength
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Chart displacement controlled by the length of a path -/

noncomputable section
namespace PolycyclicRecognition

open Set MeasureTheory Manifold
open scoped Manifold ContDiff ENNReal NNReal Bundle

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) 1 M]
  [Bundle.RiemannianBundle (TangentSpace (𝓘(ℝ, E)) : M → Type _)]

attribute [local instance] OAI.PolycyclicRecognition.tangentModelOperatorENorm
theorem chart_edist_le_pathELength (x : M) (γ : ℝ → M)
    (hγ : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓘(ℝ, E)) 1 γ (Icc 0 1))
    (hsource : ∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ (chartAt E x).source)
    (C : ℝ≥0) (hC : ∀ t ∈ Icc (0 : ℝ) 1,
      ‖mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) (extChartAt (𝓘(ℝ, E)) x) (γ t)‖ₑ ≤ C) :
    edist (extChartAt (𝓘(ℝ, E)) x (γ 0)) (extChartAt (𝓘(ℝ, E)) x (γ 1)) ≤
      C * pathELength (𝓘(ℝ, E)) γ 0 1 := by
  let η := extChartAt (𝓘(ℝ, E)) x ∘ γ
  have hη : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓘(ℝ, E)) 1 η (Icc 0 1) :=
    contMDiffOn_extChartAt.comp hγ hsource
  calc
    _ = ‖η 1 - η 0‖ₑ := by rw [edist_comm, edist_eq_enorm_sub]; rfl
    _ ≤ ∫⁻ t in Icc 0 1, ‖derivWithin η (Icc 0 1) t‖ₑ :=
      enorm_sub_le_lintegral_derivWithin_Icc_of_contDiffOn_Icc hη.contDiffOn zero_le_one
    _ = ∫⁻ t in Icc 0 1, ‖mfderivWithin (𝓘(ℝ, ℝ)) (𝓘(ℝ, E)) η (Icc 0 1) t 1‖ₑ := by
      simp_rw [← fderivWithin_derivWithin, mfderivWithin_eq_fderivWithin]
      rfl
    _ ≤ ∫⁻ t in Icc 0 1, C * ‖mfderivWithin (𝓘(ℝ, ℝ)) (𝓘(ℝ, E)) γ (Icc 0 1) t 1‖ₑ := by
      apply setLIntegral_mono' measurableSet_Icc
      intro t ht
      have hd : mfderivWithin (𝓘(ℝ, ℝ)) (𝓘(ℝ, E)) η (Icc 0 1) t =
          (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) (extChartAt (𝓘(ℝ, E)) x) (γ t)).comp
            (mfderivWithin (𝓘(ℝ, ℝ)) (𝓘(ℝ, E)) γ (Icc 0 1) t) := by
        apply mfderiv_comp_mfderivWithin
        · exact mdifferentiableAt_extChartAt (hsource t ht)
        · exact (hγ.mdifferentiableOn one_ne_zero) t ht
        · rw [uniqueMDiffWithinAt_iff_uniqueDiffWithinAt]
          exact uniqueDiffOn_Icc zero_lt_one t ht
      have hv := congrArg (fun D => D (1 : TangentSpace (𝓘(ℝ, ℝ)) t)) hd
      rw [hv]
      change ‖mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) (extChartAt (𝓘(ℝ, E)) x) (γ t)
        (mfderivWithin (𝓘(ℝ, ℝ)) (𝓘(ℝ, E)) γ (Icc 0 1) t 1)‖ₑ ≤ _
      apply (ContinuousLinearMap.le_opENorm _ _).trans
      gcongr
      exact hC t ht
    _ = _ := by
      rw [lintegral_const_mul' _ _ ENNReal.coe_ne_top,
        pathELength_eq_lintegral_mfderivWithin_Icc]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_LocalRiemannianChart
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Local Lipschitz control of a chart by the Riemannian distance -/

noncomputable section
namespace PolycyclicRecognition

open Set Filter Manifold Bundle Metric
open scoped Topology Manifold ContDiff Bundle NNReal

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [TopologicalSpace G] [ChartedSpace E G] [Group G] [LieGroup (𝓘(ℝ, E)) ∞ G]
  [T3Space G] [ConnectedSpace G] (e : E ≃L[ℝ] F)

theorem leftRiemannianChart_lipschitz (x : G) :
    letI := leftRiemannianMetric (G := G) e
    ∃ C : ℝ≥0, ∃ U ∈ 𝓝 x,
      LipschitzOnWith C (extChartAt (𝓘(ℝ, E)) x) U := by
  let metric := leftRiemannianMetric (G := G) e
  let bundle := leftRiemannianBundle (G := G) e
  let continuousBundle : IsContinuousRiemannianBundle E
      (TangentSpace (𝓘(ℝ, E)) : G → Type _) :=
    ⟨⟨(leftInvariantRiemannianMetric (G := G) e).inner,
      (leftInvariantRiemannianMetric (G := G) e).contMDiff.continuous, fun _ _ _ => rfl⟩⟩
  obtain ⟨C, hCpos, hC⟩ := eventually_enorm_mfderiv_extChartAt_lt (𝓘(ℝ, E)) x
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp
    (inter_mem hC (chart_source_mem_nhds E x))
  have hpos : (0 : ℝ) < C := hCpos
  refine ⟨C, ball x (r / 4), ball_mem_nhds x (by positivity),
    LipschitzOnWith.of_dist_le_mul ?_⟩
  intro y hy z hz
  have hxy : dist x y < r / 4 := by simpa only [mem_ball, dist_comm] using hy
  have hxz : dist x z < r / 4 := by simpa only [mem_ball, dist_comm] using hz
  have hyz : dist y z < r / 2 := by
    have := dist_triangle y x z
    rw [dist_comm y x] at this
    linarith
  apply le_of_forall_pos_le_add
  intro ε hε
  let δ := min (ε / (C : ℝ)) (r / 4)
  have hδ : 0 < δ := lt_min (div_pos hε hpos) (by positivity)
  have hδr : δ ≤ r / 4 := min_le_right _ _
  have hδε : (C : ℝ) * δ ≤ ε := by
    have := min_le_left (ε / (C : ℝ)) (r / 4)
    change δ ≤ ε / (C : ℝ) at this
    have h := (le_div_iff₀ hpos).mp this
    simpa only [mul_comm] using h
  have hnear : riemannianEDist (𝓘(ℝ, E)) y z < ENNReal.ofReal (dist y z + δ) := by
    change edist y z < _
    rw [edist_dist, ENNReal.ofReal_lt_ofReal_iff_of_nonneg dist_nonneg]
    linarith
  obtain ⟨γ, h₀, h₁, hγ, hlen⟩ := exists_lt_of_riemannianEDist_lt hnear
  have hfinite : pathELength (𝓘(ℝ, E)) γ 0 1 ≠ ⊤ := ne_top_of_lt hlen
  have hlenreal : (pathELength (𝓘(ℝ, E)) γ 0 1).toReal < dist y z + δ := by
    have h := (ENNReal.toReal_lt_toReal hfinite ENNReal.ofReal_ne_top).mpr hlen
    simpa only [ENNReal.toReal_ofReal (by positivity : 0 ≤ dist y z + δ)] using h
  have hinside (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : γ t ∈ ball x r := by
    have hprefix : edist y (γ t) ≤ pathELength (𝓘(ℝ, E)) γ 0 1 :=
      (riemannianEDist_le_pathELength (hγ.mono (Icc_subset_Icc le_rfl ht.2))
        h₀ rfl ht.1).trans (pathELength_mono le_rfl ht.2)
    have hd := ENNReal.toReal_mono hfinite hprefix
    rw [edist_dist, ENNReal.toReal_ofReal dist_nonneg] at hd
    rw [mem_ball, dist_comm]
    have htri := dist_triangle x y (γ t)
    linarith
  have hchart := chart_edist_le_pathELength x γ hγ
    (fun t ht => (hball (hinside t ht)).2) C
    (fun t ht => (hball (hinside t ht)).1.le)
  rw [h₀, h₁] at hchart
  have hchartreal := ENNReal.toReal_mono (ENNReal.mul_ne_top (by simp) hfinite) hchart
  rw [edist_dist, ENNReal.toReal_ofReal dist_nonneg, ENNReal.toReal_mul,
    ENNReal.coe_toReal] at hchartreal
  nlinarith

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_SmoothFromRiemannian
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Smooth maps from the invariant Riemannian metric are locally Lipschitz -/

noncomputable section
namespace PolycyclicRecognition

open Set Filter Manifold
open scoped Topology Manifold ContDiff

variable {E F V G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [TopologicalSpace G] [ChartedSpace E G] [Group G] [LieGroup (𝓘(ℝ, E)) ∞ G]
  [T3Space G] [ConnectedSpace G] (e : E ≃L[ℝ] F)

theorem smooth_from_leftRiemannian_locallyLipschitz {f : G → V}
    (hf : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, V)) ∞ f) :
    letI := leftRiemannianMetric (G := G) e
    LocallyLipschitz f := by
  let metric := leftRiemannianMetric (G := G) e
  intro x
  obtain ⟨C, U, hU, hχ⟩ := leftRiemannianChart_lipschitz e x
  let χ := extChartAt (𝓘(ℝ, E)) x
  have hs : ContDiffAt ℝ 1 (f ∘ χ.symm) (χ x) := by
    have hm := contMDiffAt_iff_source.mp
      ((hf.contMDiffAt (x := x)).of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top : (1 : ℕ∞ω) ≤ ∞))
    have hm' : ContMDiffAt (𝓘(ℝ, E)) (𝓘(ℝ, V)) 1 (f ∘ χ.symm) (χ x) := by
      have hr : Set.range (𝓘(ℝ, E)) = Set.univ := Set.range_id
      rw [hr, contMDiffWithinAt_univ] at hm
      exact hm
    exact hm'.contDiffAt
  obtain ⟨K, A, hA, hKA⟩ := hs.exists_lipschitzOnWith
  have hpre : χ ⁻¹' A ∈ 𝓝 x := (continuousAt_extChartAt x).preimage_mem_nhds hA
  let W := U ∩ (χ ⁻¹' A ∩ χ.source)
  have hW : W ∈ 𝓝 x := inter_mem hU (inter_mem hpre (extChartAt_source_mem_nhds x))
  refine ⟨K * C, W, hW, LipschitzOnWith.of_dist_le_mul ?_⟩
  intro y hy z hz
  have hb := hKA.dist_le_mul (x := χ y) (y := χ z) hy.2.1 hz.2.1
  have hcy := χ.left_inv hy.2.2
  have hcz := χ.left_inv hz.2.2
  simp only [Function.comp_apply, hcy, hcz] at hb
  calc
    dist (f y) (f z) ≤ K * dist (χ y) (χ z) := hb
    _ ≤ K * ((C : ℝ) * dist y z) :=
      mul_le_mul_of_nonneg_left (hχ.dist_le_mul (x := y) (y := z) hy.1 hz.1) K.coe_nonneg
    _ = ↑(K * C) * dist y z := by simp only [NNReal.coe_mul, mul_assoc]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_GroupIncrementLipschitz
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Local Lipschitz control from coordinates of group increments -/

namespace PolycyclicRecognition

open Set Filter
open scoped Topology NNReal

theorem locallyLipschitz_of_group_increments
    {V W G : Type*} [PseudoMetricSpace V] [PseudoMetricSpace W]
    [Group G] [MetricSpace G] [IsTopologicalGroup G] [IsIsometricSMul G G]
    (f : V → G) (χ : G → W) (hf : Continuous f)
    (C : ℝ≥0) (U : Set G) (hU : U ∈ 𝓝 (1 : G))
    (hχ : ∀ z ∈ U, dist (1 : G) z ≤ C * dist (χ 1) (χ z))
    (hF : ∀ x : V, ∃ K : ℝ≥0, ∃ A ∈ 𝓝 (x, x),
      LipschitzOnWith K (fun p : V × V => χ ((f p.1)⁻¹ * f p.2)) A) :
    LocallyLipschitz f := by
  intro x
  obtain ⟨K, A, hA, hFA⟩ := hF x
  have hinc : Continuous (fun p : V × V => (f p.1)⁻¹ * f p.2) :=
    (hf.comp continuous_fst).inv.mul (hf.comp continuous_snd)
  have hpre : (fun p : V × V => (f p.1)⁻¹ * f p.2) ⁻¹' U ∈ 𝓝 (x, x) :=
    hinc.continuousAt.preimage_mem_nhds (by simpa only [inv_mul_cancel] using hU)
  obtain ⟨A₁, hA₁, A₂, hA₂, hprod⟩ := mem_nhds_prod_iff.mp (inter_mem hA hpre)
  refine ⟨C * K, A₁ ∩ A₂, inter_mem hA₁ hA₂, LipschitzOnWith.of_dist_le_mul ?_⟩
  intro a ha b hb
  have hab := hprod (show (a, b) ∈ A₁ ×ˢ A₂ from ⟨ha.1, hb.2⟩)
  have haa := hprod (show (a, a) ∈ A₁ ×ˢ A₂ from ⟨ha.1, ha.2⟩)
  have hcoord := hFA.dist_le_mul (x := (a, a)) (y := (a, b)) haa.1 hab.1
  simp only [inv_mul_cancel, Prod.dist_eq, dist_self, max_eq_right dist_nonneg] at hcoord
  calc
    dist (f a) (f b) = dist (1 : G) ((f a)⁻¹ * f b) := by
      simpa only [mul_one, mul_inv_cancel_left] using
        dist_mul_left (f a) 1 ((f a)⁻¹ * f b)
    _ ≤ C * dist (χ 1) (χ ((f a)⁻¹ * f b)) := hχ _ hab.2
    _ ≤ C * ((K : ℝ) * dist a b) := mul_le_mul_of_nonneg_left hcoord C.coe_nonneg
    _ = ↑(C * K) * dist a b := by simp only [NNReal.coe_mul, mul_assoc]

end PolycyclicRecognition

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_SmoothIntoRiemannian
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Smooth maps into the invariant Riemannian metric are locally Lipschitz -/

noncomputable section
namespace PolycyclicRecognition

open Set Filter Manifold Bundle
open scoped Topology Manifold ContDiff Bundle

variable {E F V G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [TopologicalSpace G] [ChartedSpace E G] [Group G] [LieGroup (𝓘(ℝ, E)) ∞ G]
  [T3Space G] [ConnectedSpace G] (e : E ≃L[ℝ] F)

theorem smooth_into_leftRiemannian_locallyLipschitz {f : V → G}
    (hf : ContMDiff (𝓘(ℝ, V)) (𝓘(ℝ, E)) ∞ f) :
    letI := leftRiemannianMetric (G := G) e
    LocallyLipschitz f := by
  let metric := leftRiemannianMetric (G := G) e
  let bundle := leftRiemannianBundle (G := G) e
  let continuousBundle : IsContinuousRiemannianBundle E
      (TangentSpace (𝓘(ℝ, E)) : G → Type _) :=
    ⟨⟨(leftInvariantRiemannianMetric (G := G) e).inner,
      (leftInvariantRiemannianMetric (G := G) e).contMDiff.continuous, fun _ _ _ => rfl⟩⟩
  let groupTopology : IsTopologicalGroup G := topologicalGroup_of_lieGroup (𝓘(ℝ, E)) ∞
  let isometric := leftRiemannianMetric_isometric (G := G) e
  obtain ⟨C, _, hC⟩ := eventually_riemannianEDist_le_edist_extChartAt (𝓘(ℝ, E)) (1 : G)
  let χ : G → E := extChartAt (𝓘(ℝ, E)) (1 : G)
  let U := {z : G | riemannianEDist (𝓘(ℝ, E)) 1 z ≤ C * edist (χ 1) (χ z)}
  apply locallyLipschitz_of_group_increments f χ hf.continuous C U hC
  · intro z hz
    have hb := ENNReal.toReal_mono
      (ENNReal.mul_ne_top ENNReal.coe_ne_top (edist_ne_top (χ 1) (χ z))) hz
    change (edist (1 : G) z).toReal ≤ _ at hb
    simpa only [ENNReal.toReal_mul, ENNReal.coe_toReal, edist_dist,
      ENNReal.toReal_ofReal dist_nonneg] using hb
  · intro x
    have hincr : ContMDiff ((𝓘(ℝ, V)).prod (𝓘(ℝ, V))) (𝓘(ℝ, E)) ∞
        (fun p : V × V => (f p.1)⁻¹ * f p.2) :=
      (hf.comp contMDiff_fst).inv.mul (hf.comp contMDiff_snd)
    have hchart : ContMDiffAt (𝓘(ℝ, E)) (𝓘(ℝ, E)) ∞ χ ((f x)⁻¹ * f x) := by
      simpa only [inv_mul_cancel] using (contMDiffAt_extChartAt (I := 𝓘(ℝ, E)) (x := (1 : G)))
    have hc := hchart.comp (x, x) hincr.contMDiffAt
    rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod] at hc
    exact (hc.contDiffAt.of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top : (1 : ℕ∞ω) ≤ ∞)).exists_lipschitzOnWith

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_ConstructRiemannianInput
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Discharging the Riemannian metric and coordinate-regularity input -/

noncomputable section
namespace PolycyclicRecognition

open scoped Manifold ContDiff

theorem lieRiemannianMetricInput : LieRiemannianMetricInput := by
  intro S
  let groupTopology : IsTopologicalGroup S.carrier :=
    topologicalGroup_of_lieGroup (𝓘(ℝ, S.modelSpace)) ∞
  let localCompact : LocallyCompactSpace S.carrier :=
    Manifold.locallyCompact_of_finiteDimensional (𝓘(ℝ, S.modelSpace))
  let e : S.modelSpace ≃L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ S.modelSpace)) :=
    (Module.finBasis ℝ S.modelSpace).equivFun.toContinuousLinearEquiv.trans
      (EuclideanSpace.equiv (Fin (Module.finrank ℝ S.modelSpace)) ℝ).symm
  refine ⟨leftRiemannianMinimizingMetric e, ?_⟩
  rw [ProperChainMetric.compatibleMetric_eq]
  change letI := leftRiemannianMetric (G := S.carrier) e
    ∀ (n : ℕ) (φ : (Fin n → ℝ) ≃ₜ S.carrier),
      ContMDiff (𝓘(ℝ, Fin n → ℝ)) (𝓘(ℝ, S.modelSpace)) ∞ φ →
      ContMDiff (𝓘(ℝ, S.modelSpace)) (𝓘(ℝ, Fin n → ℝ)) ∞ φ.symm →
      LocallyLipschitz φ ∧ LocallyLipschitz φ.symm
  let metric := leftRiemannianMetric (G := S.carrier) e
  intro n φ hφ hφinv
  exact ⟨smooth_into_leftRiemannian_locallyLipschitz e hφ,
    smooth_from_leftRiemannian_locallyLipschitz e hφinv⟩

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
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_CoordinatePolynomial
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial restrictions to coordinate lines -/

noncomputable section
namespace PolycyclicRecognition

open Polynomial

theorem CoordinatePolynomial.head {n D : ℕ} {f : (Fin (n + 1) → ℝ) → ℝ}
    (hf : CoordinatePolynomial (n + 1) D f) (x : Fin n → ℝ) :
    ∃ p : ℝ[X], p.natDegree ≤ D ∧ ∀ t, p.eval t = f (Fin.cons t x) := by
  obtain ⟨p, hp, he⟩ := hf 0 (Fin.cons 0 x)
  exact ⟨p, hp, fun t => by simpa only [Fin.update_cons_zero] using he t⟩

theorem CoordinatePolynomial.tail {n D : ℕ} {f : (Fin (n + 1) → ℝ) → ℝ}
    (hf : CoordinatePolynomial (n + 1) D f) (t : ℝ) :
    CoordinatePolynomial n D (fun x => f (Fin.cons t x)) := by
  intro i x
  obtain ⟨p, hp, he⟩ := hf i.succ (Fin.cons t x)
  exact ⟨p, hp, fun u => by simpa only [← Fin.cons_update] using he u⟩

theorem coordinatePolynomial_eval {n D : ℕ} (p : MvPolynomial (Fin n) ℝ)
    (hp : p.totalDegree ≤ D) :
    CoordinatePolynomial n D (fun x => MvPolynomial.eval x p) := by
  classical
  intro i x
  let e := Equiv.optionSubtypeNe i
  let q := MvPolynomial.rename e.symm p
  let P := MvPolynomial.optionEquivLeft ℝ {j : Fin n // j ≠ i} q
  let r := Polynomial.map (MvPolynomial.eval (fun j : {j : Fin n // j ≠ i} => x j)) P
  refine ⟨r, ?_, ?_⟩
  · calc
      r.natDegree ≤ P.natDegree := Polynomial.natDegree_map_le
      _ = p.degreeOf i := (MvPolynomial.degreeOf_eq_natDegree i p).symm
      _ ≤ p.totalDegree := MvPolynomial.degreeOf_le_totalDegree p i
      _ ≤ D := hp
  · intro t
    change Polynomial.eval t (Polynomial.map (MvPolynomial.eval
      (fun j : {j : Fin n // j ≠ i} => x j)) (MvPolynomial.optionEquivLeft ℝ _ q)) = _
    rw [← MvPolynomial.optionEquivLeft_elim_eval, MvPolynomial.eval_rename]
    apply congrArg (fun v : Fin n → ℝ => MvPolynomial.eval v p)
    funext j
    by_cases hj : j = i
    · subst j
      simp [e]
    · simp [e, Equiv.optionSubtypeNe_symm_apply, hj]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_FiniteFiberMass
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Positive mass on quantitatively large sections

This is the finite-measure Fubini estimate used to iterate one-dimensional
polynomial bounds. It concerns an arbitrary measurable set in a product.
-/

noncomputable section
namespace PolycyclicRecognition

open MeasureTheory Set
open scoped ENNReal

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

theorem exists_large_sections (μ : Measure X) (ν : Measure Y)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (ha : 0 < (μ univ).toReal) (hb : 0 < (ν univ).toReal)
    (S : Set (X × Y)) (hS : MeasurableSet S)
    (hm : 0 < (μ.prod ν S).toReal) :
    ∃ A : Set X, MeasurableSet A ∧
      (μ.prod ν S).toReal / (2 * (ν univ).toReal) ≤ (μ A).toReal ∧
      ∀ x ∈ A,
        (μ.prod ν S).toReal / (2 * (μ univ).toReal) ≤
          (ν (Prod.mk x ⁻¹' S)).toReal := by
  let m := (μ.prod ν S).toReal
  let a := (μ univ).toReal
  let b := (ν univ).toReal
  let c := m / (2 * a)
  let f : X → ℝ := fun x => (ν (Prod.mk x ⁻¹' S)).toReal
  have hc : 0 < c := div_pos hm (mul_pos (by norm_num) ha)
  have hfm : Measurable f := (measurable_measure_prodMk_left hS).ennreal_toReal
  have hf0 (x : X) : 0 ≤ f x := ENNReal.toReal_nonneg
  have hfb (x : X) : f x ≤ b :=
    ENNReal.toReal_mono (measure_ne_top ν univ) (measure_mono (subset_univ _))
  have hfi : Integrable f μ := (integrable_const b).mono' hfm.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun x => by simpa only [Real.norm_eq_abs, abs_of_nonneg (hf0 x)] using hfb x))
  have hint : ∫ x, f x ∂μ = m := by
    change (∫ x, (ν (Prod.mk x ⁻¹' S)).toReal ∂μ) = (μ.prod ν S).toReal
    rw [Measure.prod_apply hS]
    exact integral_toReal (measurable_measure_prodMk_left hS).aemeasurable
      (Filter.Eventually.of_forall (fun x => measure_lt_top ν _))
  let A := {x | c ≤ f x}
  have hA : MeasurableSet A := measurableSet_le measurable_const hfm
  have hgi : Integrable (fun x => c + A.indicator (fun _ => b) x) μ :=
    (integrable_const c).add ((integrable_const b).indicator hA)
  have hbound (x : X) : f x ≤ c + A.indicator (fun _ => b) x := by
    by_cases hx : x ∈ A
    · rw [indicator_of_mem hx]
      linarith [hfb x]
    · rw [indicator_of_notMem hx, add_zero]
      exact (lt_of_not_ge hx).le
  have hi := integral_mono hfi hgi hbound
  rw [hint, integral_add (integrable_const c) ((integrable_const b).indicator hA),
    integral_const, integral_indicator hA, setIntegral_const] at hi
  simp only [smul_eq_mul, measureReal_def] at hi
  have hca : c * a = m / 2 := by
    dsimp [c]
    field_simp [show a ≠ 0 from ne_of_gt ha]
  change m ≤ a * c + (μ A).toReal * b at hi
  rw [mul_comm a c, hca] at hi
  refine ⟨A, hA, ?_, fun x hx => hx⟩
  apply (div_le_iff₀ (mul_pos (by norm_num) hb)).2
  nlinarith

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_NilpotentGenerators
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Lifting generators from the nilpotent abelianization

For the Cartan model, homogeneous lifts of a basis modulo the derived algebra
generate the whole nilpotent ideal. The proof pushes the error down its actual
lower central series; no generation hypothesis is substituted for this step.
-/

namespace PolycyclicRecognition

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L]

/-- Lie generation implies linear spanning modulo brackets. -/
theorem span_sup_lowerCentralSeries_one_of_lieSpan
    (S : Set L) (hS : LieSubalgebra.lieSpan ℝ L S = ⊤) :
    Submodule.span ℝ S ⊔ (LieModule.lowerCentralSeries ℝ L L 1).toSubmodule = ⊤ := by
  let V := Submodule.span ℝ S ⊔ (LieModule.lowerCentralSeries ℝ L L 1).toSubmodule
  have hmem : ∀ x ∈ LieSubalgebra.lieSpan ℝ L S, x ∈ V := by
    intro x hx
    induction hx using LieSubalgebra.lieSpan_induction with
    | mem x hx => exact Submodule.mem_sup_left (Submodule.subset_span hx)
    | zero => exact V.zero_mem
    | add x y _ _ hx hy => exact V.add_mem hx hy
    | smul r x _ hx => exact V.smul_mem r hx
    | lie x y _ _ _ _ =>
      apply Submodule.mem_sup_right
      change ⁅x, y⁆ ∈ LieModule.lowerCentralSeries ℝ L L (0 + 1)
      rw [LieModule.lowerCentralSeries_succ, LieModule.lowerCentralSeries_zero]
      exact LieSubmodule.lie_mem_lie (LieSubmodule.mem_top x) (LieSubmodule.mem_top y)
  apply top_unique
  intro x _
  exact hmem x (hS ▸ LieSubalgebra.mem_top x)

theorem lieSubalgebra_sup_lowerCentralSeries
    (U : LieSubalgebra ℝ L)
    (hU : U.toSubmodule ⊔ (LieModule.lowerCentralSeries ℝ L L 1).toSubmodule = ⊤) :
    ∀ k, U.toSubmodule ⊔ (LieModule.lowerCentralSeries ℝ L L k).toSubmodule = ⊤ := by
  intro k
  induction k with
  | zero => simp
  | succ k hk =>
    let C := LieModule.lowerCentralSeries ℝ L L k
    let C' := LieModule.lowerCentralSeries ℝ L L (k + 1)
    let S := U.toSubmodule ⊔ C'.toSubmodule
    have hright (x y : L) (hy : y ∈ C) : ⁅x, y⁆ ∈ C' := by
      change ⁅x, y⁆ ∈ LieModule.lowerCentralSeries ℝ L L (k + 1)
      rw [LieModule.lowerCentralSeries_succ]
      exact LieSubmodule.lie_mem_lie (LieSubmodule.mem_top x) hy
    have hbracket (x y : L) : ⁅x, y⁆ ∈ S := by
      have hx : x ∈ U.toSubmodule ⊔ C.toSubmodule := by rw [hk]; trivial
      have hy : y ∈ U.toSubmodule ⊔ C.toSubmodule := by rw [hk]; trivial
      obtain ⟨u, hu, a, ha, rfl⟩ := Submodule.mem_sup.mp hx
      obtain ⟨v, hv, b, hb, rfl⟩ := Submodule.mem_sup.mp hy
      rw [add_lie, lie_add, lie_add]
      apply S.add_mem
      · exact S.add_mem (Submodule.mem_sup_left (U.lie_mem hu hv))
          (Submodule.mem_sup_right (hright u b hb))
      · apply S.add_mem
        · rw [← lie_skew]
          exact Submodule.mem_sup_right (C'.neg_mem (hright v a ha))
        · exact Submodule.mem_sup_right (hright a b hb)
    have hC : (LieModule.lowerCentralSeries ℝ L L 1).toSubmodule ≤ S := by
      rw [LieModule.lowerCentralSeries_succ, LieModule.lowerCentralSeries_zero,
        LieSubmodule.lieIdeal_oper_eq_linear_span']
      apply Submodule.span_le.mpr
      rintro _ ⟨x, _, y, _, rfl⟩
      exact hbracket x y
    apply top_unique
    rw [← hU]
    exact sup_le le_sup_left hC

/-- Lifts spanning the abelianization generate a nilpotent Lie algebra. -/
theorem lieSubalgebra_eq_top_of_sup_lowerCentralSeries_one
    [LieRing.IsNilpotent L] (U : LieSubalgebra ℝ L)
    (hU : U.toSubmodule ⊔ (LieModule.lowerCentralSeries ℝ L L 1).toSubmodule = ⊤) :
    U = ⊤ := by
  obtain ⟨k, hk⟩ := LieModule.IsNilpotent.nilpotent ℝ L L
  have h := lieSubalgebra_sup_lowerCentralSeries U hU k
  rw [hk, LieSubmodule.bot_toSubmodule, sup_bot_eq] at h
  exact SetLike.coe_injective (congrArg (fun V : Submodule ℝ L => (V : Set L)) h)

end PolycyclicRecognition

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_HomogeneousGenerators
attribute [-instance] _root_.GeneratesNS.fintype_closedBall _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Choosing generators and their positive word multiplicities

A basis of the abelianization can be selected from any homogeneous spanning
pool. Its lifts generate the nilpotent algebra. Every bracket-word basis
then uses every selected generator, which is the positivity needed in the
support-volume formula.
-/

noncomputable section

namespace PolycyclicRecognition

open Module
open scoped BigOperators

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L]

theorem exists_quotient_basis_lifts [FiniteDimensional ℝ L]
    (N : Submodule ℝ L) (S : Set L) (hS : Submodule.span ℝ S ⊔ N = ⊤) :
    ∃ (b : Basis (Fin (Module.finrank ℝ (L ⧸ N))) ℝ (L ⧸ N))
      (X : Fin (Module.finrank ℝ (L ⧸ N)) → L),
      (∀ i, X i ∈ S) ∧ (∀ i, N.mkQ (X i) = b i) ∧
      Submodule.span ℝ (Set.range X) ⊔ N = ⊤ := by
  have himage : Submodule.span ℝ (N.mkQ '' S) = ⊤ := by
    rw [← Submodule.map_span, N.map_mkQ_eq_top]
    simpa only [sup_comm] using hS
  let J := (linearIndepOn_empty ℝ (id : (L ⧸ N) → (L ⧸ N))).extend
    (Set.empty_subset (N.mkQ '' S))
  let b₀ : Basis J ℝ (L ⧸ N) := Basis.ofSpan himage.ge
  let : Fintype J := Fintype.ofFinite _
  let e : J ≃ Fin (Module.finrank ℝ (L ⧸ N)) :=
    Fintype.equivFinOfCardEq (Module.finrank_eq_card_basis b₀).symm
  let b := b₀.reindex e
  have hlift : ∀ i, ∃ x ∈ S, N.mkQ x = b i := by
    intro i
    simpa only [b, Basis.coe_reindex, Function.comp_apply, Set.mem_image] using
      (Basis.ofSpan_subset himage.ge
        (show b₀ (e.symm i) ∈ Set.range b₀ from ⟨_, rfl⟩))
  choose X hXS hX using hlift
  refine ⟨b, X, hXS, hX, ?_⟩
  rw [sup_comm, ← N.map_mkQ_eq_top, Submodule.map_span, ← Set.range_comp]
  have heq : N.mkQ ∘ X = b := funext hX
  rw [heq]
  exact b.span_eq

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_RectangleFiberMass
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Large sections inside a finite rectangle -/

noncomputable section
namespace PolycyclicRecognition

open MeasureTheory Set
open scoped ENNReal

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

theorem exists_large_sections_in_rectangle (μ : Measure X) (ν : Measure Y)
    [SFinite μ] [SFinite ν] (U : Set X) (V : Set Y)
    (hU : MeasurableSet U)
    (hUfin : μ U ≠ ∞) (hVfin : ν V ≠ ∞)
    (hUpos : 0 < (μ U).toReal) (hVpos : 0 < (ν V).toReal)
    (S : Set (X × Y)) (hS : MeasurableSet S) (hsub : S ⊆ U ×ˢ V)
    (hm : 0 < (μ.prod ν S).toReal) :
    ∃ A : Set X, MeasurableSet A ∧ A ⊆ U ∧
      (μ.prod ν S).toReal / (2 * (ν V).toReal) ≤ (μ A).toReal ∧
      ∀ x ∈ A,
        (μ.prod ν S).toReal / (2 * (μ U).toReal) ≤
          (ν (Prod.mk x ⁻¹' S)).toReal := by
  let : IsFiniteMeasure (μ.restrict U) := ⟨by simpa using hUfin.lt_top⟩
  let : IsFiniteMeasure (ν.restrict V) := ⟨by simpa using hVfin.lt_top⟩
  have hprod : (μ.restrict U).prod (ν.restrict V) S = μ.prod ν S := by
    rw [Measure.prod_restrict, Measure.restrict_apply hS, inter_eq_left.2 hsub]
  obtain ⟨A, hA, hmass, hfiber⟩ := exists_large_sections
    (μ.restrict U) (ν.restrict V) (by simpa using hUpos) (by simpa using hVpos)
    S hS (by simpa only [hprod] using hm)
  refine ⟨A ∩ U, hA.inter hU, inter_subset_right, ?_, ?_⟩
  · simpa only [hprod, Measure.restrict_apply hA, Measure.restrict_apply_univ] using hmass
  · intro x hx
    have hsV : Prod.mk x ⁻¹' S ⊆ V := fun y hy => (hsub hy).2
    have hmeas : MeasurableSet (Prod.mk x ⁻¹' S) := hS.preimage measurable_prodMk_left
    simpa only [hprod, Measure.restrict_apply_univ, Measure.restrict_apply hmeas,
      inter_eq_left.2 hsV] using hfiber x hx.1

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_PiFiberMass
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_countable _root_.OAI.PolycyclicRecognition.finitelyGeneratedSubgroupIndex_countable _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Large coordinate sections of a Euclidean cube -/

noncomputable section
namespace PolycyclicRecognition

open Set Metric MeasureTheory
open scoped ENNReal

theorem measurePreserving_cons (n : ℕ) :
    MeasurePreserving (fun z : (Fin n → ℝ) × ℝ => (Fin.cons z.2 z.1 : Fin (n + 1) → ℝ))
      ((volume : Measure (Fin n → ℝ)).prod (volume : Measure ℝ)) volume := by
  have he := (volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0).symm.comp
    (Measure.measurePreserving_swap (μ := (volume : Measure (Fin n → ℝ))) (ν := (volume : Measure ℝ)))
  convert he using 1
  all_goals try with_reducible_and_instances rfl
  ext z i
  exact Fin.cases (by simp) (fun j => by simp) i

theorem mem_closedBall_cons {n : ℕ} (R : ℝ) (hR : 0 ≤ R)
    (t : ℝ) (x : Fin n → ℝ) :
    (Fin.cons t x : Fin (n + 1) → ℝ) ∈ closedBall 0 R ↔
      t ∈ closedBall 0 R ∧ x ∈ closedBall 0 R := by
  simp only [closedBall_pi (0 : Fin (n + 1) → ℝ) hR,
    closedBall_pi (0 : Fin n → ℝ) hR, mem_pi, mem_univ, forall_const,
    Fin.forall_fin_succ, Fin.cons_zero, Pi.zero_apply, Fin.cons_succ]

theorem realVolume_cube (n : ℕ) (R : ℝ) (hR : 0 ≤ R) :
    (volume (closedBall (0 : Fin n → ℝ) R)).toReal = (2 * R) ^ n := by
  rw [Real.volume_pi_closedBall _ hR, ENNReal.toReal_ofReal (by positivity)]
  simp only [Fintype.card_fin]

theorem exists_large_coordinate_sections (n : ℕ) (R : ℝ) (hR : 0 < R)
    (S : Set (Fin (n + 1) → ℝ)) (hS : MeasurableSet S)
    (hSR : S ⊆ closedBall 0 R) (hm : 0 < (volume S).toReal) :
    ∃ A : Set (Fin n → ℝ), MeasurableSet A ∧ A ⊆ closedBall 0 R ∧
      (volume S).toReal / (4 * R) ≤ (volume A).toReal ∧
      ∀ x ∈ A, (volume S).toReal / (2 * (2 * R) ^ n) ≤
        (volume {t : ℝ | Fin.cons t x ∈ S}).toReal := by
  let T : Set ((Fin n → ℝ) × ℝ) := (fun z => Fin.cons z.2 z.1) ⁻¹' S
  have hT : MeasurableSet T := hS.preimage (measurePreserving_cons n).measurable
  have hTS : (volume.prod volume) T = volume S :=
    (measurePreserving_cons n).measure_preimage hS.nullMeasurableSet
  have hsub : T ⊆ closedBall 0 R ×ˢ closedBall 0 R := by
    intro z hz
    exact ((mem_closedBall_cons R hR.le z.2 z.1).1 (hSR hz)).symm
  have hv : (volume (closedBall (0 : ℝ) R)).toReal = 2 * R := by
    rw [Real.volume_closedBall, ENNReal.toReal_ofReal (by positivity)]
  obtain ⟨A, hA, hAR, hmass, hfiber⟩ := exists_large_sections_in_rectangle
    (volume : Measure (Fin n → ℝ)) (volume : Measure ℝ)
    (closedBall 0 R) (closedBall 0 R) measurableSet_closedBall
    (isCompact_closedBall (0 : Fin n → ℝ) R).measure_ne_top
    (isCompact_closedBall (0 : ℝ) R).measure_ne_top
    (by rw [realVolume_cube n R hR.le]; positivity) (by rw [hv]; positivity)
    T hT hsub (by rwa [hTS])
  refine ⟨A, hA, hAR, ?_, ?_⟩
  · simpa only [hTS, hv, ← mul_assoc, show (2 : ℝ) * 2 = 4 by norm_num] using hmass
  · intro x hx
    have hh := hfiber x hx
    change ((volume.prod volume) T).toReal /
      (2 * (volume (closedBall (0 : Fin n → ℝ) R)).toReal) ≤
      (volume {t : ℝ | Fin.cons t x ∈ S}).toReal at hh
    simpa only [hTS, realVolume_cube n R hR.le] using hh

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_PolynomialInterpolationBound
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Elementary interpolation estimates on measurable sets

Positive length supplies separated interpolation nodes. Lagrange interpolation
then bounds a polynomial on an interval in terms of its values on these nodes.
These bounds give the scalar Remez estimate on measurable sets.
-/

noncomputable section
namespace PolycyclicRecognition

open Set Metric MeasureTheory Polynomial
open scoped ENNReal

/-- A set of length greater than `2*n*δ` contains `n` points separated by `δ`.
No regularity of the set is needed. -/
theorem exists_separated_finset_of_length (S : Set ℝ) (δ : ℝ) (hδ : 0 < δ)
    (n : ℕ) (hm : 2 * (n : ℝ) * δ < (volume S).toReal) :
    ∃ s : Finset ℝ, s.card = n ∧ (↑s : Set ℝ) ⊆ S ∧
      ∀ x ∈ s, ∀ y ∈ s, x ≠ y → δ ≤ |x - y| := by
  classical
  induction n with
  | zero => exact ⟨∅, rfl, by simp, by simp⟩
  | succ n ih =>
    have hm' : 2 * (n : ℝ) * δ < (volume S).toReal := by
      push_cast at hm
      nlinarith
    obtain ⟨s, hs, hS, hsep⟩ := ih hm'
    have hex : ∃ x ∈ S, ∀ y ∈ s, δ ≤ |x - y| := by
      by_contra h
      have hcover : S ⊆ ⋃ y ∈ s, ball y δ := by
        intro x hx
        push Not at h
        obtain ⟨y, hy, hxy⟩ := h x hx
        exact mem_iUnion.2 ⟨y, mem_iUnion.2 ⟨hy, by simpa [Real.dist_eq] using hxy⟩⟩
      have hfinite : volume (⋃ y ∈ s, ball y δ) ≠ ∞ :=
        (measure_biUnion_lt_top s.finite_toSet (fun y _ => by
          rw [Real.volume_ball]
          exact ENNReal.ofReal_lt_top)).ne
      have hb := (measureReal_mono hcover hfinite).trans
        (measureReal_biUnion_finset_le (μ := volume) s (fun y => ball y δ))
      simp only [measureReal_def, Real.volume_ball,
        ENNReal.toReal_ofReal (by positivity : 0 ≤ 2 * δ), Finset.sum_const,
        nsmul_eq_mul, hs] at hb
      push_cast at hm
      nlinarith
    obtain ⟨x, hx, hxsep⟩ := hex
    have hxs : x ∉ s := by
      intro hx'
      have hh := hxsep x hx'
      simp only [sub_self, abs_zero] at hh
      linarith
    refine ⟨insert x s, by simp [hxs, hs], ?_, ?_⟩
    · simpa only [Finset.coe_insert] using insert_subset hx hS
    · intro a ha b hb hab
      by_cases hax : a = x
      · subst a
        exact hxsep b ((Finset.mem_insert.1 hb).resolve_left (Ne.symm hab))
      · have has : a ∈ s := (Finset.mem_insert.1 ha).resolve_left hax
        by_cases hbx : b = x
        · subst b
          simpa only [abs_sub_comm a x] using hxsep a has
        · exact hsep a has b ((Finset.mem_insert.1 hb).resolve_left hbx) hab

/-- Explicit interpolation bound, with the separation and interval radius
visible. The degree may be strictly smaller than the number of nodes. -/
theorem polynomial_bound_of_separated_nodes (p : ℝ[X]) (s : Finset ℝ)
    (hdeg : p.degree < s.card) (δ R η : ℝ) (hδ : 0 < δ)
    (hR : 0 ≤ R) (hη : 0 ≤ η)
    (hsep : ∀ a ∈ s, ∀ b ∈ s, a ≠ b → δ ≤ |a - b|)
    (hs : ∀ a ∈ s, |a| ≤ R) (hp : ∀ a ∈ s, |p.eval a| ≤ η)
    (x : ℝ) (hx : |x| ≤ R) :
    |p.eval x| ≤ (s.card : ℝ) * η * (2 * R / δ) ^ (s.card - 1) := by
  classical
  have hterm (a : ℝ) (ha : a ∈ s) :
      |(Lagrange.basis s id a).eval x| ≤ (2 * R / δ) ^ (s.card - 1) := by
    rw [Lagrange.basis, eval_prod, Finset.abs_prod]
    have hfactor (b : ℝ) (hb : b ∈ s.erase a) :
        |(Lagrange.basisDivisor (id a) (id b)).eval x| ≤ 2 * R / δ := by
      obtain ⟨hba, hb⟩ := Finset.mem_erase.1 hb
      have hsep' := hsep a ha b hb (Ne.symm hba)
      have hnum : |x - b| ≤ 2 * R := by
        have := abs_sub x b
        linarith [hs b hb]
      simp only [Lagrange.basisDivisor, eval_mul, eval_C, eval_sub,
        eval_X, id_eq, abs_mul, abs_inv]
      simpa only [div_eq_mul_inv, mul_comm] using
        (div_le_div₀ (by positivity : 0 ≤ 2 * R) hnum hδ hsep')
    calc
      (∏ b ∈ s.erase a, |(Lagrange.basisDivisor (id a) (id b)).eval x|) ≤
          ∏ _b ∈ s.erase a, (2 * R / δ) :=
        Finset.prod_le_prod (fun _ _ => abs_nonneg _) hfactor
      _ = (2 * R / δ) ^ (s.card - 1) := by
        rw [Finset.prod_const, Finset.card_erase_of_mem ha]
  have heq := Lagrange.eq_interpolate (v := id) (s := s) Function.injective_id.injOn hdeg
  conv_lhs => rw [heq, Lagrange.interpolate_apply, eval_finsetSum]
  calc
    |∑ a ∈ s, (C (p.eval (id a)) * Lagrange.basis s id a).eval x| ≤
        ∑ a ∈ s, |(C (p.eval (id a)) * Lagrange.basis s id a).eval x| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _a ∈ s, η * (2 * R / δ) ^ (s.card - 1) := by
      apply Finset.sum_le_sum
      intro a ha
      simp only [eval_mul, eval_C, id_eq, abs_mul]
      exact mul_le_mul (hp a ha) (hterm a ha) (abs_nonneg _) hη
    _ = (s.card : ℝ) * η * (2 * R / δ) ^ (s.card - 1) := by
      rw [Finset.sum_const, nsmul_eq_mul, mul_assoc]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_ApproximateInvariantMean
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.boundedFunctionPull_apply _root_.OAI.PolycyclicRecognition.boundedFunctionPull_one _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.kernelAverage_one _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.smallCoefficientBoundedReal_one _root_.OAI.PolycyclicRecognition.subgroupFunctionExtension_apply _root_.OAI.PolycyclicRecognition.subgroupFunctionExtension_one _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Constructing an invariant mean from approximate finite averages

Compactness is applied to the actual bounded-function space. The conclusion
is the invariant mean used by the height-correction argument, not a separate
amenability predicate.
-/

noncomputable section

namespace PolycyclicRecognition

open ThompsonNonamenability Filter Set
open scoped Topology ENNReal

variable {G : Type*} [Group G]

omit [Group G] in
/-- Positivity and normalization control every bounded real function. -/
theorem positive_normalized_bound
    (L : BoundedReal G →ₗ[ℝ] ℝ)
    (hpos : ∀ f, (∀ g, 0 ≤ f g) → 0 ≤ L f) (hone : L 1 = 1)
    (f : BoundedReal G) : |L f| ≤ ‖f‖ := by
  have hmono {a b : BoundedReal G} (h : ∀ g, a g ≤ b g) : L a ≤ L b := by
    have hh := hpos (b - a) (fun g => sub_nonneg.mpr (h g))
    rw [map_sub] at hh
    exact sub_nonneg.mp hh
  have hlo := hmono (a := (-‖f‖) • (1 : BoundedReal G)) (b := f) (fun g => by
    have hh := lp.norm_apply_le_norm ENNReal.top_ne_zero f g
    simp only [BoundedReal.smul_one_apply]
    exact (abs_le.mp (by simpa only [Real.norm_eq_abs] using hh)).1)
  have hhi := hmono (a := f) (b := ‖f‖ • (1 : BoundedReal G)) (fun g => by
    have hh := lp.norm_apply_le_norm ENNReal.top_ne_zero f g
    simp only [BoundedReal.smul_one_apply]
    exact (abs_le.mp (by simpa only [Real.norm_eq_abs] using hh)).2)
  simp only [map_smul, smul_eq_mul, hone, mul_one] at hlo hhi
  exact abs_le.mpr ⟨hlo, hhi⟩

/-- Compactness simultaneously preserves positivity, normalization and
vanishing translation defects for any prescribed set of group elements. -/
theorem exists_partially_invariantMean_of_approximate
    {ι : Type*} {l : Filter ι} [l.NeBot]
    (L : ι → BoundedReal G →ₗ[ℝ] ℝ)
    (hpos : ∀ i f, (∀ g, 0 ≤ f g) → 0 ≤ L i f)
    (hone : ∀ i, L i 1 = 1)
    (S : Set G)
    (hdefect : ∀ g ∈ S, ∀ f, Tendsto (fun i => L i (leftPull g f) - L i f) l (𝓝 0)) :
    ∃ M : BoundedReal G →ₗ[ℝ] ℝ,
      (∀ f, (∀ g, 0 ≤ f g) → 0 ≤ M f) ∧ M 1 = 1 ∧
        ∀ g ∈ S, ∀ f, M (leftPull g f) = M f := by
  let K (f : BoundedReal G) := Icc (-‖f‖) ‖f‖
  have (f : BoundedReal G) : CompactSpace (K f) :=
    isCompact_iff_compactSpace.mp (isCompact_Icc : IsCompact (K f))
  let Z := (f : BoundedReal G) → K f
  let p : ι → Z := fun i f => ⟨L i f,
    abs_le.mp (positive_normalized_bound (L i) (hpos i) (hone i) f)⟩
  obtain ⟨z, _, hz⟩ := (isCompact_univ : IsCompact (univ : Set Z)).exists_mapClusterPt
    (show Filter.map p l ≤ 𝓟 univ by simp)
  obtain ⟨u, hul, huz⟩ := mapClusterPt_iff_ultrafilter.mp hz
  have hlim (f : BoundedReal G) : Tendsto (fun i => L i f) u (𝓝 (z f).val) := by
    exact (continuous_subtype_val.comp (continuous_apply f)).tendsto z |>.comp huz
  let M : BoundedReal G →ₗ[ℝ] ℝ :=
    { toFun := fun f => (z f).val
      map_add' := by
        intro f g
        apply tendsto_nhds_unique (hlim (f + g))
        simpa only [map_add] using (hlim f).add (hlim g)
      map_smul' := by
        intro r f
        apply tendsto_nhds_unique (hlim (r • f))
        simpa only [map_smul, smul_eq_mul, RingHom.id_apply] using (hlim f).const_mul r }
  refine ⟨M, ?_, ?_, ?_⟩
  · intro f hf
    exact ge_of_tendsto (hlim f) (Eventually.of_forall (fun i => hpos i f hf))
  · change (z 1).val = 1
    apply tendsto_nhds_unique (hlim 1)
    simpa only [hone] using (tendsto_const_nhds : Tendsto (fun _ : ι => (1 : ℝ)) u (𝓝 1))
  · intro g hg f
    change (z (leftPull g f)).val = (z f).val
    apply sub_eq_zero.mp
    exact tendsto_nhds_unique ((hlim (leftPull g f)).sub (hlim f))
      ((hdefect g hg f).mono_left hul)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_FolnerRatio
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Passing from a boundary estimate to a volume ratio -/

namespace PolycyclicRecognition

open Filter
open scoped Topology

theorem tendsto_ratio_one_of_boundary
    {ι : Type*} {l : Filter ι} (A N s b : ι → ℝ) {α β : ℝ}
    (hα : 0 < α) (hβ : 0 ≤ β)
    (hs : ∀ i, 0 < s i) (hb : ∀ i, 0 ≤ b i)
    (hlower : ∀ i, α * s i ≤ A i)
    (hmono : ∀ i, A i ≤ N i) (hupper : ∀ i, N i ≤ A i + β * b i)
    (hlim : Tendsto (fun i => b i / s i) l (𝓝 0)) :
    Tendsto (fun i => N i / A i) l (𝓝 1) := by
  have hA (i : ι) : 0 < A i := (mul_pos hα (hs i)).trans_le (hlower i)
  have hbound (i : ι) : N i / A i - 1 ≤ (β / α) * (b i / s i) := by
    calc
      N i / A i - 1 = (N i - A i) / A i := by field_simp [(hA i).ne']
      _ ≤ (β * b i) / A i :=
        div_le_div_of_nonneg_right (by linarith [hupper i]) (hA i).le
      _ ≤ (β * b i) / (α * s i) :=
        div_le_div_of_nonneg_left (mul_nonneg hβ (hb i)) (mul_pos hα (hs i)) (hlower i)
      _ = (β / α) * (b i / s i) := by ring
  have hz : Tendsto (fun i => N i / A i - 1) l (𝓝 0) := by
    apply squeeze_zero (fun i => sub_nonneg.mpr ((one_le_div (hA i)).mpr (hmono i))) hbound
    simpa only [mul_zero] using hlim.const_mul (β / α)
  simpa only [sub_add_cancel, zero_add] using hz.add_const 1

end PolycyclicRecognition

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_LowerPacking
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Lower packing bounds from Haar volume

A totally bounded endpoint set has a finite separated net. Its volume is
at most the cardinality of that net times the mass of a fixed-radius ball.
This is the lower packing estimate used after stationary mesh selection.
-/

noncomputable section

open Metric Set MeasureTheory
open scoped ENNReal

namespace PolycyclicRecognition

/-- A totally bounded set admits a finite separated net with its centers
inside the set. The set itself need not be closed or measurable. -/
theorem exists_separated_net_of_totallyBounded
    {X : Type*} [PseudoMetricSpace X] {S : Set X} (hS : TotallyBounded S)
    {r : ℝ} (hr : 0 < r) :
    ∃ t : Finset X, (↑t : Set X) ⊆ S ∧
      (∀ x ∈ t, ∀ y ∈ t, x ≠ y → r < dist x y) ∧
      ∀ x ∈ S, ∃ y ∈ t, dist x y ≤ r := by
  classical
  obtain ⟨U, _hUS, hUfin, hUcover⟩ := finite_approx_of_totallyBounded hS (r / 3) (by positivity)
  let u := hUfin.toFinset
  have hbound (t : Finset X) (ht : (↑t : Set X) ⊆ S)
      (hsep : ∀ x ∈ t, ∀ y ∈ t, x ≠ y → r < dist x y) : t.card ≤ u.card := by
    have hchoice (x : {x // x ∈ t}) : ∃ y : {y // y ∈ u}, dist x.val y.val < r / 3 := by
      obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.mp (hUcover (ht x.property))
      exact ⟨⟨y, hUfin.mem_toFinset.mpr hy⟩, Metric.mem_ball.mp hxy⟩
    choose c hc using hchoice
    have hinj : Function.Injective c := by
      intro x y hxy
      apply Subtype.ext
      by_contra hne
      have hdist : dist x.val y.val < r := by
        calc
          dist x.val y.val ≤ dist x.val (c x).val + dist (c x).val y.val := dist_triangle _ _ _
          _ = dist x.val (c x).val + dist y.val (c y).val := by rw [hxy, dist_comm (c y).val]
          _ < r := by linarith [hc x, hc y]
      exact (not_lt_of_ge hdist.le) (hsep x.val x.property y.val y.property hne)
    simpa only [Fintype.card_coe] using Fintype.card_le_of_injective c hinj
  obtain ⟨t, ht, hsep, _hcard, hcover⟩ :=
    finite_separated_cover_set_of_bound S hr.le u.card hbound
  exact ⟨t, ht, hsep, hcover⟩

variable {G : Type*} [Group G] [MetricSpace G] [MeasurableSpace G]
  [BorelSpace G] [MeasurableMul G] [IsIsometricSMul G G]

omit [BorelSpace G] in
/-- Haar mass of a closed ball is independent of its center. -/
theorem measure_closedBall_eq_identity (μ : Measure G) [μ.IsMulLeftInvariant]
    (x : G) (r : ℝ) : μ (closedBall x r) = μ (closedBall (1 : G) r) := by
  have h := measure_preimage_mul μ x (closedBall x r)
  rw [preimage_mul_left_closedBall, inv_mul_cancel] at h
  exact h.symm

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_InvariantMeanGenerators
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # It suffices to make a mean invariant under a generating set -/

noncomputable section

namespace PolycyclicRecognition

open ThompsonNonamenability Filter Set
open scoped Topology

variable {G : Type*} [Group G]

/-- Approximate invariance need only be checked on generators; the limiting
functional is invariant under their whole algebraic closure. -/
theorem exists_invariantMean_of_approximate_generators
    {ι : Type*} {l : Filter ι} [l.NeBot]
    (L : ι → BoundedReal G →ₗ[ℝ] ℝ)
    (hpos : ∀ i f, (∀ g, 0 ≤ f g) → 0 ≤ L i f)
    (hone : ∀ i, L i 1 = 1) (S : Set G) (hS : Subgroup.closure S = ⊤)
    (hdefect : ∀ g ∈ S, ∀ f, Tendsto (fun i => L i (leftPull g f) - L i f) l (𝓝 0)) :
    Nonempty (InvariantMean G) := by
  obtain ⟨M, hM, hMone, hMinv⟩ := exists_partially_invariantMean_of_approximate
    (l := l) L hpos hone S hdefect
  have hc : Subgroup.closure S ≤ meanStabilizer M := by
    rw [Subgroup.closure_le]
    exact hMinv
  rw [hS] at hc
  exact ⟨⟨M, hM, hMone, fun g f => hc (Subgroup.mem_top g) f⟩⟩

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.Thompson_FiniteAverage
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Real finite averages and left-translation cancellation

These are literal finite sums. The translation estimate cancels the common
intersection of the two finite sets, and the function bound is global. No
invariant mean, support assumption, or limiting average is used.
-/

noncomputable section

universe uα uι uG

namespace ThompsonNonamenability

open scoped BigOperators symmDiff

variable {α : Type uα} {ι : Type uι}

theorem realAvg_sub (A : Finset α) (f g : α → ℝ) :
    realAvg A (fun x => f x - g x) = realAvg A f - realAvg A g := by
  simp only [realAvg, Finset.sum_sub_distrib, mul_sub]

end ThompsonNonamenability

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_CyclicInvariantMean
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instNonemptyBases _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_nonempty _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Invariant means on cyclic groups from literal power averages -/

noncomputable section

namespace PolycyclicRecognition

open ThompsonNonamenability Filter Set
open scoped Topology BigOperators ENNReal

variable {G : Type*} [Group G]

theorem cyclicMeanState_positive (a : G) (n : ℕ) (f : BoundedReal G)
    (hf : ∀ g, 0 ≤ f g) : 0 ≤ cyclicMeanState a n f :=
  realAvg_nonneg _ (fun k _ => hf (a ^ k))

theorem cyclicMeanState_one (a : G) (n : ℕ) : cyclicMeanState a n 1 = 1 :=
  realAvg_const _ (Finset.nonempty_range_iff.mpr (Nat.succ_ne_zero n)) 1

/-- The generator defect telescopes without any injectivity assumption on
the powers. The same averages work for finite and infinite cyclic groups. -/
theorem cyclicMeanState_generator_defect (a : G) (n : ℕ) (f : BoundedReal G) :
    cyclicMeanState a n (leftPull a f) - cyclicMeanState a n f =
      (f (a ^ (n + 1)) - f 1) / ((n : ℝ) + 1) := by
  have havg (v : ℕ → ℝ) :
      realAvg (Finset.range (n + 1)) (fun k => v (k + 1) - v k) =
        (v (n + 1) - v 0) / ((n : ℝ) + 1) := by
    rw [realAvg, Finset.sum_range_sub]
    simp only [Finset.card_range, Nat.cast_add, Nat.cast_one, div_eq_mul_inv, mul_comm]
  have hpull : (fun k : ℕ => leftPull a f (a ^ k)) =
      (fun k : ℕ => f (a ^ (k + 1))) := by
    funext k
    rw [leftPull_apply, pow_succ']
  change realAvg (Finset.range (n + 1)) (fun k => leftPull a f (a ^ k)) -
    realAvg (Finset.range (n + 1)) (fun k => f (a ^ k)) = _
  rw [hpull, ← realAvg_sub]
  simpa only [pow_zero] using havg (fun k => f (a ^ k))

theorem invariantMean_of_zpowers_eq_top (a : G) (ha : Subgroup.zpowers a = ⊤) :
    Nonempty (InvariantMean G) := by
  apply exists_invariantMean_of_approximate_generators (l := atTop)
    (cyclicMeanState a) (cyclicMeanState_positive a) (cyclicMeanState_one a) {a}
    (by rwa [← Subgroup.zpowers_eq_closure])
  intro g hg f
  have hga : g = a := mem_singleton_iff.mp hg
  subst g
  have hbound (n : ℕ) :
      ‖cyclicMeanState a n (leftPull a f) - cyclicMeanState a n f‖ ≤
        (2 * ‖f‖) / ((n : ℝ) + 1) := by
    rw [Real.norm_eq_abs, cyclicMeanState_generator_defect, abs_div,
      abs_of_pos (show 0 < (n : ℝ) + 1 by positivity)]
    apply div_le_div_of_nonneg_right _ (by positivity)
    have h₁ := lp.norm_apply_le_norm ENNReal.top_ne_zero f (a ^ (n + 1))
    have h₂ := lp.norm_apply_le_norm ENNReal.top_ne_zero f 1
    have hsub := abs_sub (f (a ^ (n + 1))) (f 1)
    simp only [Real.norm_eq_abs] at h₁ h₂
    linarith
  apply squeeze_zero_norm hbound
  simpa only [div_eq_mul_inv, one_mul, mul_zero, mul_assoc] using
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (2 * ‖f‖)

theorem invariantMean_of_isCyclic [IsCyclic G] : Nonempty (InvariantMean G) := by
  obtain ⟨a, ha⟩ := isCyclic_iff_exists_zpowers_eq_top.mp (inferInstance : IsCyclic G)
  exact invariantMean_of_zpowers_eq_top a ha

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_ExtensionInvariantMean
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Invariant means on extensions

Average first on each kernel coset and then on the quotient. All averages
act on the actual bounded real functions used in the height correction.
-/

noncomputable section

namespace PolycyclicRecognition

open ThompsonNonamenability
open scoped ENNReal

variable {G Q : Type*} [Group G] [Group Q]

theorem invariantMean_of_extension (φ : G →* Q) (hφ : Function.Surjective φ)
    (hN : Nonempty (InvariantMean φ.ker)) (hQ : Nonempty (InvariantMean Q)) :
    Nonempty (InvariantMean G) := by
  choose s hs using hφ
  exact ⟨extensionInvariantMean φ s hs hN.some hQ.some⟩

theorem invariantMean_of_normal_subgroup (N : Subgroup G) [N.Normal]
    (hN : Nonempty (InvariantMean N)) (hQ : Nonempty (InvariantMean (G ⧸ N))) :
    Nonempty (InvariantMean G) := by
  apply invariantMean_of_extension (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N)
    _ hQ
  rw [QuotientGroup.ker_mk']
  exact hN

/-- No normality assumption is needed for a finite extension: restrict to
the normal core, then average over its finite quotient. -/
theorem invariantMean_of_finiteIndex (K : Subgroup G) [K.FiniteIndex]
    (hK : Nonempty (InvariantMean K)) : Nonempty (InvariantMean G) := by
  let N := K.normalCore
  let i : N →* K := Subgroup.inclusion K.normalCore_le
  let MN := subgroupInvariantMean hK.some i.range
  let e : N ≃* i.range := MonoidHom.ofInjective (Subgroup.inclusion_injective _)
  have hN : Nonempty (InvariantMean N) :=
    ⟨imageInvariantMean e.symm.toMonoidHom e.symm.surjective MN⟩
  exact invariantMean_of_normal_subgroup N hN ⟨finiteInvariantMean⟩

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.Thompson_FiniteLevels
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite scalar levels

The distinct values of a nonnegative function on a finite set, together with
zero, give a finite subdivision. Its positive gaps reconstruct every value
and every absolute difference by strict superlevel indicators. These are
finite sums, including when the only level is zero.
-/

open scoped BigOperators

universe uG

namespace ThompsonNonamenability

variable {G : Type uG}

namespace FiniteLevelChain

theorem exists_chain (K : Finset G) (p : G → ℝ)
    (hp : ∀ x ∈ K, 0 ≤ p x) : Nonempty (FiniteLevelChain K p) :=
  ⟨ofNonneg K p hp⟩

variable {K : Finset G} {p : G → ℝ} (c : FiniteLevelChain K p)

theorem gap_pos (i : Fin c.n) : 0 < c.gap i := by
  apply sub_pos.mpr
  exact c.strictMono_value (show i.castSucc < i.succ from Nat.lt_succ_self i.val)

/-- Telescoping below any selected value of a strictly increasing finite list. -/
private theorem telescope : ∀ (n : ℕ) (f : Fin (n + 1) → ℝ),
    StrictMono f → ∀ k : Fin (n + 1),
      f k - f 0 = ∑ i : Fin n,
        (f i.succ - f i.castSucc) * (if f i.castSucc < f k then 1 else 0) := by
  intro n
  induction n with
  | zero =>
      intro f hf k
      have hk : k = 0 := by
        apply Fin.ext
        have hklt := k.isLt
        omega
      subst k
      simp
  | succ n ih =>
      intro f hf k
      refine Fin.cases ?_ (fun k => ?_) k
      · have hnot : ∀ i : Fin (n + 1), ¬ f i.castSucc < f 0 := by
          intro i
          exact not_lt_of_ge (hf.monotone (Fin.zero_le i.castSucc))
        simp [hnot]
      · have hs := ih (fun j : Fin (n + 1) => f j.succ)
          (by intro a b hab; exact hf (Nat.succ_lt_succ hab)) k
        have hfirst : f 0 < f k.succ := hf (Fin.succ_pos k)
        rw [Fin.sum_univ_succ]
        change f k.succ - f 0 =
          (f (0 : Fin (n + 1)).succ - f 0) * (if f 0 < f k.succ then 1 else 0) +
            ∑ i : Fin n, (f i.succ.succ - f i.castSucc.succ) *
              (if f i.castSucc.succ < f k.succ then 1 else 0)
        rw [ite_eq_left hfirst, mul_one, ← hs]
        ring

/-- The finite layer decomposition of each value in the actual level set. -/
theorem reconstruct (a : ℝ) (ha : a ∈ insert 0 (K.image p)) :
    a = ∑ i : Fin c.n, c.gap i *
      (if c.value i.castSucc < a then (1 : ℝ) else 0) := by
  classical
  have ha' : a ∈ Finset.univ.image c.value := by
    rw [c.image_value_eq]
    exact ha
  rcases Finset.mem_image.mp ha' with ⟨k, _, rfl⟩
  simpa only [gap, c.value_zero, sub_zero] using
    telescope c.n c.value c.strictMono_value k

private theorem abs_sub_eq_sum_of_le (a b : ℝ)
    (ha : a ∈ insert 0 (K.image p)) (hb : b ∈ insert 0 (K.image p))
    (hab : a ≤ b) :
    |a - b| = ∑ i : Fin c.n, c.gap i *
      |(if c.value i.castSucc < a then (1 : ℝ) else 0) -
        (if c.value i.castSucc < b then (1 : ℝ) else 0)| := by
  classical
  have hi : ∀ i : Fin c.n,
      (if c.value i.castSucc < a then (1 : ℝ) else 0) ≤
        (if c.value i.castSucc < b then (1 : ℝ) else 0) := by
    intro i
    by_cases hai : c.value i.castSucc < a
    · have hbi : c.value i.castSucc < b := lt_of_lt_of_le hai hab
      simp [hai, hbi]
    · simp only [ite_eq_right hai]
      by_cases hbi : c.value i.castSucc < b <;> simp [hbi]
  calc
    |a - b| = b - a := by rw [abs_of_nonpos (sub_nonpos.mpr hab)]; ring
    _ = (∑ i : Fin c.n, c.gap i * (if c.value i.castSucc < b then (1 : ℝ) else 0)) -
        (∑ i : Fin c.n, c.gap i * (if c.value i.castSucc < a then (1 : ℝ) else 0)) :=
      congrArg₂ (fun x y : ℝ => x - y) (c.reconstruct b hb) (c.reconstruct a ha)
    _ = ∑ i : Fin c.n, c.gap i *
        |(if c.value i.castSucc < a then (1 : ℝ) else 0) -
          (if c.value i.castSucc < b then (1 : ℝ) else 0)| := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i _
      rw [abs_of_nonpos (sub_nonpos.mpr (hi i))]
      ring

/-- The finite coarea identity for a scalar absolute difference. -/
theorem abs_sub_eq_sum (a b : ℝ)
    (ha : a ∈ insert 0 (K.image p)) (hb : b ∈ insert 0 (K.image p)) :
    |a - b| = ∑ i : Fin c.n, c.gap i *
      |(if c.value i.castSucc < a then (1 : ℝ) else 0) -
        (if c.value i.castSucc < b then (1 : ℝ) else 0)| := by
  rcases le_total a b with hab | hba
  · exact c.abs_sub_eq_sum_of_le a b ha hb hab
  · simpa only [abs_sub_comm] using c.abs_sub_eq_sum_of_le b a hb ha hba

end FiniteLevelChain

end ThompsonNonamenability

end OAI
end

section
-- module Solutions.OAIQ093_PR.Thompson_FiniteCoarea
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

universe uG

namespace ThompsonNonamenability

open scoped BigOperators symmDiff

variable {G : Type uG} [DecidableEq G]

private theorem sum_indicator_eq_card (A C : Finset G) (hAC : A ⊆ C) :
    (∑ x ∈ C, if x ∈ A then (1 : ℝ) else 0) = (A.card : ℝ) := by
  classical
  have hfilter : C.filter (fun x => x ∈ A) = A := by
    ext x
    simp only [Finset.mem_filter]
    exact ⟨And.right, fun hx => ⟨hAC hx, hx⟩⟩
  rw [← Finset.sum_filter, hfilter]
  simp

private theorem sum_abs_indicators_eq_card_symmDiff
    (A B C : Finset G) (hAC : A ⊆ C) (hBC : B ⊆ C) :
    (∑ x ∈ C,
      |(if x ∈ A then (1 : ℝ) else 0) -
        (if x ∈ B then (1 : ℝ) else 0)|) = ((A ∆ B).card : ℝ) := by
  classical
  have hsub : A ∆ B ⊆ C := by
    intro x hx
    rcases Finset.mem_symmDiff.mp hx with hx | hx
    · exact hAC hx.1
    · exact hBC hx.1
  calc
    _ = ∑ x ∈ C, if x ∈ A ∆ B then (1 : ℝ) else 0 := by
      apply Finset.sum_congr rfl
      intro x hx
      by_cases hA : x ∈ A <;> by_cases hB : x ∈ B <;>
        simp [hA, hB, Finset.mem_symmDiff]
    _ = _ := sum_indicator_eq_card (A ∆ B) C hsub

private theorem finite_value_mem {K : Finset G} {p : G → ℝ}
    (hpK : ∀ x, x ∉ K → p x = 0) (x : G) :
    p x ∈ insert 0 (K.image p) := by
  classical
  by_cases hx : x ∈ K
  · exact Finset.mem_insert_of_mem (Finset.mem_image_of_mem p hx)
  · rw [hpK x hx]
    exact Finset.mem_insert_self _ _

namespace FiniteLevelChain

variable {K : Finset G} {p : G → ℝ}

omit [DecidableEq G] in
theorem levelSet_subset [DecidableEq G] (c : FiniteLevelChain K p) (i : Fin c.n) :
    c.levelSet i ⊆ K := Finset.filter_subset _ _

/-- The finite carrier restriction does not change positive-threshold membership. -/
theorem mem_levelSet (c : FiniteLevelChain K p)
    (hpK : ∀ x, x ∉ K → p x = 0) (i : Fin c.n) (x : G) :
    x ∈ c.levelSet i ↔ c.value i.castSucc < p x := by
  classical
  have hv : 0 ≤ c.value i.castSucc := by
    simpa only [c.value_zero] using
      c.strictMono_value.monotone (Fin.zero_le i.castSucc)
  constructor
  · intro hx
    exact (Finset.mem_filter.mp hx).2
  · intro hx
    apply Finset.mem_filter.mpr
    refine ⟨?_, hx⟩
    by_contra hxK
    rw [hpK x hxK] at hx
    exact (not_lt_of_ge hv) hx

omit [DecidableEq G] in
theorem levelSet_nonempty [DecidableEq G] (c : FiniteLevelChain K p) (i : Fin c.n) :
    (c.levelSet i).Nonempty := by
  classical
  have hlt : c.value i.castSucc < c.value i.succ :=
    c.strictMono_value (by
      change i.val < i.val + 1
      exact Nat.lt_succ_self i.val)
  have hv : 0 ≤ c.value i.castSucc := by
    simpa only [c.value_zero] using
      c.strictMono_value.monotone (Fin.zero_le i.castSucc)
  have hpos : 0 < c.value i.succ := lt_of_le_of_lt hv hlt
  have hmem : c.value i.succ ∈ insert 0 (K.image p) := by
    rw [← c.image_value_eq]
    exact Finset.mem_image_of_mem _ (Finset.mem_univ _)
  have himage : c.value i.succ ∈ K.image p :=
    (Finset.mem_insert.mp hmem).resolve_left (ne_of_gt hpos)
  obtain ⟨x, hxK, hpx⟩ := Finset.mem_image.mp himage
  refine ⟨x, Finset.mem_filter.mpr ⟨hxK, ?_⟩⟩
  rw [hpx]
  exact hlt

/-- Exact finite layer-cake identity for the mass. -/
theorem coarea_mass (c : FiniteLevelChain K p)
    (hpK : ∀ x, x ∉ K → p x = 0) :
    (∑ x ∈ K, p x) =
      ∑ i : Fin c.n, c.gap i * ((c.levelSet i).card : ℝ) := by
  classical
  calc
    _ = ∑ x ∈ K, ∑ i : Fin c.n, c.gap i *
        (if c.value i.castSucc < p x then (1 : ℝ) else 0) := by
      apply Finset.sum_congr rfl
      intro x hx
      exact c.reconstruct (p x) (finite_value_mem hpK x)
    _ = ∑ i : Fin c.n, ∑ x ∈ K, c.gap i *
        (if c.value i.castSucc < p x then (1 : ℝ) else 0) :=
      Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [← Finset.mul_sum]
      congr 1
      calc
        _ = ∑ x ∈ K, if x ∈ c.levelSet i then (1 : ℝ) else 0 := by
          apply Finset.sum_congr rfl
          intro x hx
          simp only [c.mem_levelSet hpK i x]
        _ = _ := sum_indicator_eq_card _ K (c.levelSet_subset i)

end FiniteLevelChain

section Translation

variable [Group G]

theorem mem_leftTranslate_iff (h : G) (A : Finset G) (x : G) :
    x ∈ leftTranslate h A ↔ h⁻¹ * x ∈ A := by
  constructor
  · intro hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    simpa using hy
  · intro hx
    exact Finset.mem_image.mpr ⟨h⁻¹ * x, hx, by simp⟩

namespace FiniteLevelChain

variable {K : Finset G} {p : G → ℝ}

/-- Exact coarea identity for one left translation, over its finite support carrier. -/
theorem coarea_translation (c : FiniteLevelChain K p)
    (hpK : ∀ x, x ∉ K → p x = 0) (h : G) :
    (∑ x ∈ K ∪ leftTranslate h K, |p (h⁻¹ * x) - p x|) =
      ∑ i : Fin c.n, c.gap i *
        ((leftTranslate h (c.levelSet i) ∆ c.levelSet i).card : ℝ) := by
  classical
  calc
    _ = ∑ x ∈ K ∪ leftTranslate h K, ∑ i : Fin c.n, c.gap i *
        |(if c.value i.castSucc < p (h⁻¹ * x) then (1 : ℝ) else 0) -
          (if c.value i.castSucc < p x then (1 : ℝ) else 0)| := by
      apply Finset.sum_congr rfl
      intro x hx
      exact c.abs_sub_eq_sum (p (h⁻¹ * x)) (p x)
        (finite_value_mem hpK _) (finite_value_mem hpK _)
    _ = ∑ i : Fin c.n, ∑ x ∈ K ∪ leftTranslate h K, c.gap i *
        |(if c.value i.castSucc < p (h⁻¹ * x) then (1 : ℝ) else 0) -
          (if c.value i.castSucc < p x then (1 : ℝ) else 0)| :=
      Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [← Finset.mul_sum]
      congr 1
      have hleft : leftTranslate h (c.levelSet i) ⊆ K ∪ leftTranslate h K := by
        intro x hx
        obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
        exact Finset.mem_union_right _
          (Finset.mem_image_of_mem (fun y => h * y) (c.levelSet_subset i hy))
      have hright : c.levelSet i ⊆ K ∪ leftTranslate h K := by
        intro x hx
        exact Finset.mem_union_left _ (c.levelSet_subset i hx)
      calc
        _ = ∑ x ∈ K ∪ leftTranslate h K,
            |(if x ∈ leftTranslate h (c.levelSet i) then (1 : ℝ) else 0) -
              (if x ∈ c.levelSet i then (1 : ℝ) else 0)| := by
          apply Finset.sum_congr rfl
          intro x hx
          simp only [mem_leftTranslate_iff, c.mem_levelSet hpK]
        _ = _ := sum_abs_indicators_eq_card_symmDiff _ _ _ hleft hright

/-- Summing the exact translation identities introduces no cardinality factor. -/
theorem coarea_sum (c : FiniteLevelChain K p)
    (hpK : ∀ x, x ∉ K → p x = 0) (S : Finset G) :
    (∑ h ∈ S, ∑ x ∈ K ∪ leftTranslate h K, |p (h⁻¹ * x) - p x|) =
      ∑ i : Fin c.n, c.gap i *
        (∑ h ∈ S, ((leftTranslate h (c.levelSet i) ∆ c.levelSet i).card : ℝ)) := by
  calc
    _ = ∑ h ∈ S, ∑ i : Fin c.n, c.gap i *
        ((leftTranslate h (c.levelSet i) ∆ c.levelSet i).card : ℝ) :=
      Finset.sum_congr rfl (fun h _ => c.coarea_translation hpK h)
    _ = _ := by
      rw [Finset.sum_comm]
      simp only [Finset.mul_sum]

end FiniteLevelChain

/-- A nonempty level inside the supplied finite support has small total boundary. -/
theorem finite_folner_of_small_defect_subset
    {K S : Finset G} {p : G → ℝ} {ε : ℝ}
    (hp0 : ∀ g, 0 ≤ p g)
    (hpK : ∀ g, g ∉ K → p g = 0)
    (mass : ∑ g ∈ K, p g = 1)
    (hdef : (∑ h ∈ S, ∑ x ∈ K ∪ leftTranslate h K,
      |p (h⁻¹ * x) - p x|) < ε) :
    ∃ A : Finset G, A ⊆ K ∧ A.Nonempty ∧
      (∑ h ∈ S, ((leftTranslate h A ∆ A).card : ℝ)) < ε * (A.card : ℝ) := by
  classical
  obtain ⟨c⟩ := FiniteLevelChain.exists_chain K p (fun g _ => hp0 g)
  have hmass : (∑ i : Fin c.n, c.gap i * ((c.levelSet i).card : ℝ)) = 1 :=
    (c.coarea_mass hpK).symm.trans mass
  have hex : ∃ i : Fin c.n,
      (∑ h ∈ S, ((leftTranslate h (c.levelSet i) ∆ c.levelSet i).card : ℝ)) <
        ε * ((c.levelSet i).card : ℝ) := by
    by_contra hnone
    have hfail : ∀ i : Fin c.n, ε * ((c.levelSet i).card : ℝ) ≤
        ∑ h ∈ S, ((leftTranslate h (c.levelSet i) ∆ c.levelSet i).card : ℝ) :=
      fun i => le_of_not_gt (fun hi => hnone ⟨i, hi⟩)
    have hle : ε ≤ ∑ h ∈ S, ∑ x ∈ K ∪ leftTranslate h K,
        |p (h⁻¹ * x) - p x| := by
      calc
        ε = ε * ∑ i : Fin c.n, c.gap i * ((c.levelSet i).card : ℝ) := by
          rw [hmass, mul_one]
        _ = ∑ i : Fin c.n, c.gap i * (ε * ((c.levelSet i).card : ℝ)) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i hi
          ring
        _ ≤ ∑ i : Fin c.n, c.gap i *
            (∑ h ∈ S, ((leftTranslate h (c.levelSet i) ∆ c.levelSet i).card : ℝ)) :=
          Finset.sum_le_sum (fun i _ =>
            mul_le_mul_of_nonneg_left (hfail i) (c.gap_pos i).le)
        _ = _ := (c.coarea_sum hpK S).symm
    exact (not_lt_of_ge hle) hdef
  obtain ⟨i, hi⟩ := hex
  exact ⟨c.levelSet i, c.levelSet_subset i, c.levelSet_nonempty i, hi⟩

/-- Finite probability with small total translation defect yields a finite Følner set. -/
theorem finite_folner_of_small_defect
    {K S : Finset G} {p : G → ℝ} {ε : ℝ}
    (hp0 : ∀ g, 0 ≤ p g)
    (hpK : ∀ g, g ∉ K → p g = 0)
    (mass : ∑ g ∈ K, p g = 1)
    (hdef : (∑ h ∈ S, ∑ x ∈ K ∪ leftTranslate h K,
      |p (h⁻¹ * x) - p x|) < ε) :
    ∃ A : Finset G, A.Nonempty ∧
      (∑ h ∈ S, ((leftTranslate h A ∆ A).card : ℝ)) < ε * (A.card : ℝ) := by
  obtain ⟨A, _, hA, hsmall⟩ := finite_folner_of_small_defect_subset hp0 hpK mass hdef
  exact ⟨A, hA, hsmall⟩

end Translation

end ThompsonNonamenability

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.Thompson_ProbabilityDefects
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.OAI.ThompsonNonamenability.separatorCoordinate_apply _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite probabilities and their simultaneous translation defects

One ℓ¹ space on `S × G` carries the sum of all translation defects.  In
particular its norm is the exact finite sum, without a factor depending on
`S.card`.  This is the finite-probability input to the separation argument.
-/

noncomputable section

open scoped BigOperators Classical

universe uG uι

namespace ThompsonNonamenability

variable {G : Type uG}

theorem isProbabilityWeights_single (g : G) :
    IsProbabilityWeights (Finsupp.single g (1 : ℝ)) := by
  refine ⟨?_, mass_single g 1⟩
  intro x
  simp only [Finsupp.single_apply]
  split_ifs
  · exact zero_le_one
  · exact le_rfl

theorem convex_probabilityWeights :
    Convex ℝ {p : G →₀ ℝ | IsProbabilityWeights p} := by
  intro p hp q hq a b ha hb hab
  refine ⟨?_, ?_⟩
  · intro g
    change 0 ≤ a * p g + b * q g
    exact add_nonneg (mul_nonneg ha (hp.1 g)) (mul_nonneg hb (hq.1 g))
  · rw [map_add, map_smul, map_smul, hp.2, hq.2]
    simpa using hab

variable [Group G]

private theorem single_apply_real {ι : Type uι} [DecidableEq ι] (i j : ι) (a : ℝ) :
    (lp.single 1 i a : lp (fun _ : ι => ℝ) 1) j = if i = j then a else 0 := by
  by_cases hij : i = j
  · subst j
    simp
  · rw [lp.single_apply_ne (E := fun _ : ι => ℝ) 1 i a (Ne.symm hij), ite_eq_right hij]

/-- Coordinate computation for a single point probability. -/
theorem diracDefect_apply (S : Finset G) (g : G) (h : S) (x : G) :
    diracDefect S g (h, x) =
      (Finsupp.single g (1 : ℝ)) (h.val⁻¹ * x) - (Finsupp.single g (1 : ℝ)) x := by
  have hmul : h.val * g = x ↔ g = h.val⁻¹ * x := by
    constructor
    · intro heq
      simpa [mul_assoc] using congrArg (fun y => h.val⁻¹ * y) heq
    · intro heq
      simpa [mul_assoc] using congrArg (fun y => h.val * y) heq
  unfold diracDefect
  rw [lp.coeFn_sum, Finset.sum_apply, Finset.sum_eq_single h]
  · simp only [lp.coeFn_sub, Pi.sub_apply]
    rw [single_apply_real, single_apply_real]
    simp only [Prod.mk.injEq, true_and, hmul,
      Finsupp.single_apply]
  · intro k _ hkh
    simp [Prod.mk.injEq, hkh]
  · simp

/-- The product coordinate is exactly the left translation difference. -/
theorem defectMap_apply (S : Finset G) (p : G →₀ ℝ) (h : S) (x : G) :
    defectMap S p (h, x) = p (h.val⁻¹ * x) - p x := by
  induction p using Finsupp.induction_linear with
  | zero => simp
  | add p q hp hq =>
      simp only [map_add, lp.coeFn_add, Pi.add_apply, Finsupp.add_apply, hp, hq]
      ring
  | single g a =>
      rw [defectMap_single, lp.coeFn_smul, Pi.smul_apply, diracDefect_apply]
      simp only [smul_eq_mul, Finsupp.single_apply, mul_sub, mul_ite, mul_one, mul_zero]

/-- Each translation difference vanishes outside its exact finite support bound. -/
theorem translation_difference_eq_zero_of_not_mem (p : G →₀ ℝ) (h x : G)
    (hx : x ∉ p.support ∪ p.support.image (fun g => h * g)) :
    p (h⁻¹ * x) - p x = 0 := by
  have hx₀ : x ∉ p.support := fun hmem => hx (Finset.mem_union_left _ hmem)
  have hx₁ : h⁻¹ * x ∉ p.support := by
    intro hmem
    apply hx
    apply Finset.mem_union_right
    exact Finset.mem_image.mpr ⟨h⁻¹ * x, hmem, by simp⟩
  simp [Finsupp.notMem_support_iff.mp hx₀, Finsupp.notMem_support_iff.mp hx₁]

/-- Exact ℓ¹ norm of the simultaneous defect, with no `S.card` loss. -/
theorem norm_defectMap (S : Finset G) (p : G →₀ ℝ) :
    ‖defectMap S p‖ =
      ∑ h ∈ S, ∑ x ∈ p.support ∪ p.support.image (fun g => h * g),
        |p (h⁻¹ * x) - p x| := by
  have hsum : HasSum (fun z : S × G => ‖defectMap S p z‖) ‖defectMap S p‖ := by
    simpa only [ENNReal.toReal_one, Real.rpow_one] using
      (lp.hasSum_norm (p := 1) (by simp) (defectMap S p))
  calc
    ‖defectMap S p‖ = ∑' z : S × G, ‖defectMap S p z‖ := hsum.tsum_eq.symm
    _ = ∑ h : S, ∑' x : G, ‖defectMap S p (h, x)‖ := by
      rw [hsum.summable.tsum_prod, tsum_fintype]
    _ = ∑ h : S, ∑ x ∈ p.support ∪ p.support.image (fun g => h.val * g),
        |p (h.val⁻¹ * x) - p x| := by
      apply Finset.sum_congr rfl
      intro h _
      simp only [defectMap_apply, Real.norm_eq_abs]
      apply tsum_eq_sum
      intro x hx
      rw [translation_difference_eq_zero_of_not_mem p h.val x hx, abs_zero]
    _ = ∑ h ∈ S, ∑ x ∈ p.support ∪ p.support.image (fun g => h * g),
        |p (h⁻¹ * x) - p x| :=
      Finset.sum_coe_sort S (fun h : G =>
        ∑ x ∈ p.support ∪ p.support.image (fun g => h * g),
          |p (h⁻¹ * x) - p x|)

theorem convex_defectSet (S : Finset G) : Convex ℝ (defectSet S) :=
  convex_probabilityWeights.linear_image (defectMap S)

theorem diracDefect_mem_defectSet (S : Finset G) (g : G) :
    diracDefect S g ∈ defectSet S := by
  refine ⟨Finsupp.single g 1, isProbabilityWeights_single g, ?_⟩
  simp

end ThompsonNonamenability

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.Thompson_MeanApproximation
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite probabilities approximately invariant under a finite set

The usual positive normalized invariant mean forces zero to lie in the
closure of the actual finite-probability defect set. The separation argument
uses bounded coordinate functions of a continuous linear functional on ℓ¹;
no identification of the full dual of ℓ¹ is assumed.
-/

noncomputable section

open scoped ENNReal BigOperators

universe uG

namespace ThompsonNonamenability

variable {G : Type uG} [Group G] [DecidableEq G]

attribute [local instance] OAI.ThompsonNonamenability.instFactLeENNRealOfNat_solutions
theorem separatorDefect_apply {S : Finset G} (ell : DefectSpace S →L[ℝ] ℝ)
    (g : G) : separatorDefect ell g = ell (diracDefect S g) := by
  classical
  cases Subsingleton.elim (inferInstance : DecidableEq G) (Classical.decEq G)
  simp only [separatorDefect, lp.coeFn_sum, Finset.sum_apply,
    lp.coeFn_sub, Pi.sub_apply, leftPull_apply, separatorCoordinate_apply,
    diracDefect, map_sum, map_sub]

theorem InvariantMean.separatorDefect_eq_zero (M : InvariantMean G)
    {S : Finset G} (ell : DefectSpace S →L[ℝ] ℝ) : M (separatorDefect ell) = 0 := by
  classical
  change M.toLinearMap (∑ h : {h : G // h ∈ S},
    (leftPull h.val (separatorCoordinate ell h) - separatorCoordinate ell h)) = 0
  simp only [map_sum, map_sub, M.left_invariant, sub_self, Finset.sum_const_zero]

/-- Separation contradicts the existence of a positive normalized invariant mean. -/
theorem InvariantMean.zero_mem_closure_defectSet (M : InvariantMean G)
    (S : Finset G) : (0 : DefectSpace S) ∈ closure (defectSet S) := by
  classical
  by_contra hout
  obtain ⟨ell, c, hc, hsep⟩ := geometric_hahn_banach_point_closed
    (convex_defectSet S).closure isClosed_closure hout
  have hcpos : 0 < c := by simpa only [ell.map_zero] using hc
  have hpoint (g : G) : c ≤ separatorDefect ell g := by
    rw [separatorDefect_apply]
    apply le_of_lt
    apply hsep
    apply subset_closure
    exact diracDefect_mem_defectSet S g
  have hmean : c ≤ M (separatorDefect ell) := by
    simpa only [InvariantMean.map_const] using
      M.mono (f := c • (1 : BoundedReal G)) (g := separatorDefect ell)
        (fun g => by simpa only [BoundedReal.smul_one_apply] using hpoint g)
  rw [M.separatorDefect_eq_zero] at hmean
  exact (not_le_of_gt hcpos) hmean

/-- Actual nonnegative finite probabilities with arbitrarily small total defect. -/
theorem InvariantMean.exists_probability_small_defect (M : InvariantMean G)
    (S : Finset G) {ε : ℝ} (hε : 0 < ε) :
    ∃ p : G →₀ ℝ, IsProbabilityWeights p ∧ ‖defectMap S p‖ < ε := by
  classical
  obtain ⟨v, hv, hvsmall⟩ := Metric.mem_closure_iff.mp
    (M.zero_mem_closure_defectSet S) ε hε
  obtain ⟨p, hp, rfl⟩ := hv
  refine ⟨p, hp, ?_⟩
  simpa only [dist_zero_left] using hvsmall

end ThompsonNonamenability

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.Thompson_MeanToFolner
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators symmDiff

universe uG

namespace ThompsonNonamenability

variable {G : Type uG} [Group G] [DecidableEq G]

/-- A standard invariant mean yields a finite set with small total boundary. -/
theorem InvariantMean.exists_folner_total (M : InvariantMean G)
    (S : Finset G) {ε : ℝ} (hε : 0 < ε) :
    ∃ A : Finset G, A.Nonempty ∧
      (∑ h ∈ S, ((leftTranslate h A ∆ A).card : ℝ)) < ε * A.card := by
  classical
  cases Subsingleton.elim (inferInstance : DecidableEq G) (Classical.decEq G)
  obtain ⟨p, hp, hsmall⟩ := M.exists_probability_small_defect S hε
  have hmass : ∑ g ∈ p.support, p g = 1 := by
    simpa only [mass_apply] using hp.2
  have hdef : (∑ h ∈ S, ∑ x ∈ p.support ∪ leftTranslate h p.support,
      |p (h⁻¹ * x) - p x|) < ε := by
    simpa only [norm_defectMap, leftTranslate] using hsmall
  exact finite_folner_of_small_defect (p := fun g => p g) (K := p.support)
    (S := S) hp.1 (fun g hg => Finsupp.notMem_support_iff.mp hg) hmass hdef

end ThompsonNonamenability

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_PolycyclicInvariantMean
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finite_templateSymmetryGroup _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteSubtypeLinearEquivRealIdMemSubgroupLinearSupportSymmetryGroup _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Concrete invariant means for virtually polycyclic groups

The finite cyclic subnormal series gives the mean by successive kernel and
quotient averages. Thus amenability in the model reduction is proved from
polycyclicity, rather than retained as an extra premise.
-/

noncomputable section

namespace PolycyclicRecognition

open ThompsonNonamenability ChromaticCyclic

variable {G : Type*} [Group G]

theorem invariantMean_of_cyclicStep {H K : Subgroup G} (s : CyclicStep H K)
    (hH : Nonempty (InvariantMean H)) : Nonempty (InvariantMean K) := by
  let := s.normal
  let := s.cyclic
  let e := (Subgroup.subgroupOfEquivOfLe s.le).symm
  exact invariantMean_of_normal_subgroup (H.subgroupOf K)
    ⟨imageInvariantMean e.toMonoidHom e.surjective hH.some⟩ invariantMean_of_isCyclic

theorem invariantMean_of_cyclicSeries {H K : Subgroup G} {n : ℕ}
    (c : CyclicSeries H K n) (hH : Nonempty (InvariantMean H)) :
    Nonempty (InvariantMean K) := by
  have hm : ∀ i, i ≤ n → Nonempty (InvariantMean (c.group i)) := by
    intro i
    induction i with
    | zero => intro _; rw [c.first]; exact hH
    | succ i ih =>
      intro hi
      exact invariantMean_of_cyclicStep (c.step i (by omega)) (ih (by omega))
  rw [← c.last]
  exact hm n le_rfl

theorem invariantMean_of_isPolycyclic (hG : IsPolycyclic G) :
    Nonempty (InvariantMean G) := by
  obtain ⟨n, ⟨c⟩⟩ := hG
  have htop := invariantMean_of_cyclicSeries c ⟨finiteInvariantMean⟩
  exact ⟨imageInvariantMean (⊤ : Subgroup G).subtype
    (by intro g; exact ⟨⟨g, trivial⟩, rfl⟩) htop.some⟩

theorem invariantMean_of_isVirtuallyPolycyclic (hG : IsVirtuallyPolycyclic G) :
    Nonempty (InvariantMean G) := by
  obtain ⟨K, hindex, hK⟩ := hG
  let := hindex
  exact invariantMean_of_finiteIndex K (invariantMean_of_isPolycyclic hK)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_RightFolnerExpansion
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.meanCorrection_one _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.smallCoefficientRealCoinvariantMean_one _root_.OAI.PolycyclicRecognition.smallCoefficientRealMean_one _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.OAI.PolycyclicRecognition.vectorMeanCorrection_one _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Right finite expansions and metric Følner sets in the source group

Left-invariant metrics use right expansions of finite sets. Inversion
converts the left Følner sets supplied by an invariant mean into these sets.
-/

noncomputable section

namespace PolycyclicRecognition

open ThompsonNonamenability
open scoped symmDiff

variable {G : Type*} [Group G] [DecidableEq G]

theorem exists_small_rightExpansion (M : InvariantMean G) (S : Finset G)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ E : Finset G, E.Nonempty ∧
      ((rightFiniteExpansion E S \ E).card : ℝ) < ε * E.card := by
  obtain ⟨A, hA, hsmall⟩ := M.exists_folner_total (S.image Inv.inv) hε
  let E := A.image Inv.inv
  have hE : E.card = A.card := Finset.card_image_of_injective A inv_injective
  have hbound (g : G) : ((E.image (· * g) \ E).card : ℝ) ≤
      ((_root_.OAI.ThompsonNonamenability.leftTranslate g⁻¹ A ∆ A).card : ℝ) := by
    have hs : (E.image (· * g) \ E).image Inv.inv ⊆ _root_.OAI.ThompsonNonamenability.leftTranslate g⁻¹ A ∆ A := by
      intro x hx
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨hy, hyE⟩ := Finset.mem_sdiff.mp hy
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hy
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hz
      apply Finset.mem_symmDiff.mpr
      left
      refine ⟨?_, ?_⟩
      · apply Finset.mem_image.mpr
        exact ⟨a, ha, by simp⟩
      · intro hin
        apply hyE
        apply Finset.mem_image.mpr
        exact ⟨(a⁻¹ * g)⁻¹, hin, inv_inv _⟩
    have hc := Finset.card_le_card hs
    rw [Finset.card_image_of_injective _
      (inv_injective : Function.Injective (fun g : G => g⁻¹))] at hc
    exact_mod_cast hc
  have hs : rightFiniteExpansion E S \ E ⊆
      S.biUnion (fun g => E.image (· * g) \ E) := by
    intro x hx
    obtain ⟨hx, hxE⟩ := Finset.mem_sdiff.mp hx
    obtain ⟨g, hg, hxg⟩ := Finset.mem_biUnion.mp hx
    exact Finset.mem_biUnion.mpr ⟨g, hg, Finset.mem_sdiff.mpr ⟨hxg, hxE⟩⟩
  have hcard : ((rightFiniteExpansion E S \ E).card : ℝ) ≤
      ∑ g ∈ S, ((E.image (· * g) \ E).card : ℝ) := by
    exact_mod_cast (Finset.card_le_card hs).trans Finset.card_biUnion_le
  have hsum : (∑ g ∈ S, ((_root_.OAI.ThompsonNonamenability.leftTranslate g⁻¹ A ∆ A).card : ℝ)) < ε * E.card := by
    rw [hE]
    convert hsmall using 1
    all_goals try with_reducible_and_instances rfl
    rw [Finset.sum_image]
    intro a _ b _ hab
    exact inv_injective hab
  exact ⟨E, hA.image Inv.inv, (hcard.trans (Finset.sum_le_sum (fun g _ => hbound g))).trans_lt hsum⟩

variable [MetricSpace G] [IsIsometricSMul G G]

theorem mem_finiteMetricNeighborhood
    (hfinite : ∀ R : ℝ, (Metric.closedBall (1 : G) R).Finite)
    (E : Finset G) (R : ℝ) (x : G) :
    x ∈ finiteMetricNeighborhood hfinite E R ↔ ∃ p ∈ E, dist x p ≤ R := by
  constructor
  · intro hx
    obtain ⟨g, hg, hxg⟩ := Finset.mem_biUnion.mp hx
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hxg
    refine ⟨p, hp, ?_⟩
    have hg' : dist g 1 ≤ R := (hfinite R).mem_toFinset.mp hg
    simpa only [mul_one] using (dist_mul_left p g (1 : G)).trans_le hg'
  · rintro ⟨p, hp, hd⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨p⁻¹ * x, (hfinite R).mem_toFinset.mpr ?_, ?_⟩
    · change dist (p⁻¹ * x) 1 ≤ R
      have he : dist (p⁻¹ * x) 1 = dist x p := by
        simpa only [mul_one, mul_inv_cancel_left] using
          (dist_mul_left p (p⁻¹ * x) (1 : G)).symm
      rw [he]
      exact hd
    · exact Finset.mem_image.mpr ⟨p, hp, mul_inv_cancel_left p x⟩

omit [IsIsometricSMul G G] in
theorem exists_small_metricNeighborhood (M : InvariantMean G)
    (hfinite : ∀ R : ℝ, (Metric.closedBall (1 : G) R).Finite)
    (R : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ E : Finset G, E.Nonempty ∧
      ((finiteMetricNeighborhood hfinite E R \ E).card : ℝ) < ε * E.card :=
  exists_small_rightExpansion M _ hε

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_MetricFolnerVolume
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The volume estimates in metric Følner transfer

A finite union of fixed-radius target balls has mass bounded below by its
source cardinality, using a separated net and bounded coarse multiplicity.
Its metric boundary is covered by balls indexed by the source boundary.
-/

noncomputable section

namespace PolycyclicRecognition

open Metric Set MeasureTheory
open scoped ENNReal

theorem metricFolnerSet_measurable {X Y : Type*} [PseudoMetricSpace Y]
    [MeasurableSpace Y] [BorelSpace Y] (u : X → Y) (E : Finset X) (a : ℝ) :
    MeasurableSet (metricFolnerSet u E a) :=
  E.finite_toSet.measurableSet_biUnion (fun _ _ => measurableSet_ball)

theorem metricFolnerSet_volume_lower
    {X Y : Type*} [Group Y] [MetricSpace Y] [MeasurableSpace Y]
    [BorelSpace Y] [MeasurableMul Y] [IsIsometricSMul Y Y]
    (μ : Measure Y) [μ.IsMulLeftInvariant] (u : X → Y) (E : Finset X)
    {a : ℝ} (ha : 0 < a) (M : ℕ)
    (hmult : ∀ (y : Y) (A : Finset X),
      (∀ x ∈ A, dist (u x) y ≤ a + a) → A.card ≤ M) :
    (E.card : ℝ≥0∞) * μ (ball (1 : Y) a) ≤
      (M : ℝ≥0∞) * μ (metricFolnerSet u E a) := by
  classical
  obtain ⟨t, ht, hsep, hcover⟩ := exists_separated_net_of_totallyBounded
    (E.image u).finite_toSet.isCompact.totallyBounded (add_pos ha ha)
  have hc : E.card ≤ t.card * M :=
    card_le_cover_mul_of_bounded_multiplicity E u t (a + a) M
      (fun x hx => hcover (u x) (Finset.mem_image.mpr ⟨x, hx, rfl⟩)) hmult
  have hv : (t.card : ℝ≥0∞) * μ (ball (1 : Y) a) ≤ μ (metricFolnerSet u E a) := by
    apply separated_card_mul_ball_le μ t a _
      (fun x hx y hy hxy => (hsep x hx y hy hxy).le)
    intro y hy z hz
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp (ht hy)
    exact Set.mem_iUnion₂.mpr ⟨x, hx, hz⟩
  have hc' : (E.card : ℝ≥0∞) ≤ (t.card : ℝ≥0∞) * M := by exact_mod_cast hc
  calc
    (E.card : ℝ≥0∞) * μ (ball (1 : Y) a) ≤
        ((t.card : ℝ≥0∞) * M) * μ (ball (1 : Y) a) := by gcongr
    _ = (M : ℝ≥0∞) * ((t.card : ℝ≥0∞) * μ (ball (1 : Y) a)) := by ac_rfl
    _ ≤ _ := by gcongr

theorem metricFolnerSet_boundary_subset
    {X Y : Type*} [Group X] [MetricSpace X] [IsIsometricSMul X X]
    [PseudoMetricSpace Y] [DecidableEq X]
    (hfinite : ∀ R : ℝ, (closedBall (1 : X) R).Finite)
    (u : X → Y) (E : Finset X) {a c K C R : ℝ}
    (hca : c < a) (hK : 0 ≤ K) (hR : 0 ≤ R)
    (hsurj : ∀ y, ∃ q, dist y (u q) ≤ c)
    (hlower : ∀ x y, dist x y ≤ K * dist (u x) (u y) + C) :
    cthickening R (metricFolnerSet u E a) \ metricFolnerSet u E a ⊆
      ⋃ q ∈ finiteMetricNeighborhood hfinite E (K * (c + (R + 1) + a) + C) \ E,
        closedBall (u q) c := by
  rintro y ⟨hy, hyout⟩
  have hy' : y ∈ thickening (R + 1) (metricFolnerSet u E a) :=
    cthickening_subset_thickening' (by linarith) (by linarith) _ hy
  obtain ⟨z, hz, hyz⟩ := mem_thickening_iff.mp hy'
  obtain ⟨p, hp, hzp⟩ := Set.mem_iUnion₂.mp hz
  obtain ⟨q, hyq⟩ := hsurj y
  have hqnot : q ∉ E := by
    intro hq
    apply hyout
    exact Set.mem_iUnion₂.mpr ⟨q, hq, lt_of_le_of_lt hyq hca⟩
  have hqp : dist q p ≤ K * (c + (R + 1) + a) + C := by
    apply (hlower q p).trans
    apply add_le_add (mul_le_mul_of_nonneg_left _ hK) le_rfl
    calc
      dist (u q) (u p) ≤ dist (u q) y + dist y (u p) := dist_triangle _ _ _
      _ ≤ dist (u q) y + (dist y z + dist z (u p)) := by
        gcongr
        exact dist_triangle _ _ _
      _ ≤ c + (R + 1) + a := by
        rw [dist_comm (u q) y]
        have hzp' : dist z (u p) < a := hzp
        linarith
  exact Set.mem_iUnion₂.mpr ⟨q,
    Finset.mem_sdiff.mpr ⟨(mem_finiteMetricNeighborhood hfinite E _ q).mpr ⟨p, hp, hqp⟩,
      hqnot⟩, hyq⟩

theorem metricFolnerSet_boundary_volume
    {X Y : Type*} [Group X] [MetricSpace X] [IsIsometricSMul X X]
    [Group Y] [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    [MeasurableMul Y] [IsIsometricSMul Y Y] [DecidableEq X]
    (μ : Measure Y) [μ.IsMulLeftInvariant]
    (hfinite : ∀ R : ℝ, (closedBall (1 : X) R).Finite)
    (u : X → Y) (E : Finset X) {a c K C R : ℝ}
    (hca : c < a) (hK : 0 ≤ K) (hR : 0 ≤ R)
    (hsurj : ∀ y, ∃ q, dist y (u q) ≤ c)
    (hlower : ∀ x y, dist x y ≤ K * dist (u x) (u y) + C) :
    μ (cthickening R (metricFolnerSet u E a) \ metricFolnerSet u E a) ≤
      ((finiteMetricNeighborhood hfinite E (K * (c + (R + 1) + a) + C) \ E).card : ℝ≥0∞) *
        μ (closedBall (1 : Y) c) := by
  apply (measure_mono (metricFolnerSet_boundary_subset hfinite u E hca hK hR hsurj hlower)).trans
  apply (measure_biUnion_finset_le _ _).trans
  simp only [measure_closedBall_eq_identity, Finset.sum_const, nsmul_eq_mul, le_refl]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_SourceMetricFolner
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # One source Følner sequence works for every metric radius -/

noncomputable section

namespace PolycyclicRecognition

open ThompsonNonamenability Filter Metric
open scoped Topology

variable {G : Type*} [Group G] [MetricSpace G] [IsIsometricSMul G G] [DecidableEq G]

theorem finiteMetricNeighborhood_mono
    (hfinite : ∀ R : ℝ, (closedBall (1 : G) R).Finite)
    (E : Finset G) {R S : ℝ} (hRS : R ≤ S) :
    finiteMetricNeighborhood hfinite E R ⊆ finiteMetricNeighborhood hfinite E S := by
  intro x hx
  obtain ⟨p, hp, hd⟩ := (mem_finiteMetricNeighborhood hfinite E R x).mp hx
  exact (mem_finiteMetricNeighborhood hfinite E S x).mpr ⟨p, hp, hd.trans hRS⟩

theorem exists_sourceMetricFolner_sequence (M : InvariantMean G)
    (hfinite : ∀ R : ℝ, (closedBall (1 : G) R).Finite) :
    ∃ E : ℕ → Finset G, (∀ n, (E n).Nonempty) ∧
      ∀ R : ℝ, Tendsto
        (fun n => ((finiteMetricNeighborhood hfinite (E n) R \ E n).card : ℝ) / (E n).card)
        atTop (𝓝 0) := by
  have hex (n : ℕ) : ∃ E : Finset G, E.Nonempty ∧
      ((finiteMetricNeighborhood hfinite E n \ E).card : ℝ) <
        (1 / ((n : ℝ) + 1)) * E.card :=
    exists_small_metricNeighborhood M hfinite n (by positivity)
  choose E hE hsmall using hex
  refine ⟨E, hE, fun R => ?_⟩
  obtain ⟨N, hN⟩ := exists_nat_ge R
  have hupper : ∀ᶠ n : ℕ in atTop,
      ((finiteMetricNeighborhood hfinite (E n) R \ E n).card : ℝ) / (E n).card ≤
        1 / ((n : ℝ) + 1) := by
    filter_upwards [eventually_ge_atTop N] with n hn
    have hRn : R ≤ (n : ℝ) := hN.trans (by exact_mod_cast hn)
    have hc : (finiteMetricNeighborhood hfinite (E n) R \ E n).card ≤
        (finiteMetricNeighborhood hfinite (E n) n \ E n).card :=
      Finset.card_le_card (by
        intro x hx
        obtain ⟨hx, hxE⟩ := Finset.mem_sdiff.mp hx
        exact Finset.mem_sdiff.mpr
          ⟨finiteMetricNeighborhood_mono hfinite (E n) hRn hx, hxE⟩)
    apply (div_le_iff₀ (by exact_mod_cast (hE n).card_pos)).mpr
    have hcr : ((finiteMetricNeighborhood hfinite (E n) R \ E n).card : ℝ) ≤
        (finiteMetricNeighborhood hfinite (E n) n \ E n).card := by exact_mod_cast hc
    exact hcr.trans (hsmall n).le
  exact squeeze_zero' (Eventually.of_forall (fun _ => by positivity)) hupper
    tendsto_one_div_add_atTop_nhds_zero_nat

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_MetricFolnerTransfer
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.meanCorrection_one _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.smallCoefficientRealCoinvariantMean_one _root_.OAI.PolycyclicRecognition.smallCoefficientRealMean_one _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.OAI.PolycyclicRecognition.vectorMeanCorrection_one _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual metric Følner transfer to a coarsely equivalent measured group -/

noncomputable section

namespace PolycyclicRecognition

open ThompsonNonamenability Metric MeasureTheory Filter Set
open scoped Topology ENNReal

variable {X Y : Type*} [Group X] [MetricSpace X] [IsIsometricSMul X X]
  [DecidableEq X] [Group Y] [MetricSpace Y] [ProperSpace Y]
  [MeasurableSpace Y] [BorelSpace Y] [MeasurableMul Y] [IsIsometricSMul Y Y]

theorem exists_metricFolner_sequence
    (M : InvariantMean X) (hfinite : ∀ R : ℝ, (closedBall (1 : X) R).Finite)
    (μ : Measure Y) [μ.IsMulLeftInvariant] [μ.IsOpenPosMeasure] [IsFiniteMeasureOnCompacts μ]
    (u : X → Y) {c K C : ℝ} (hc : 0 ≤ c) (hK : 0 ≤ K)
    (hsurj : ∀ y, ∃ q, dist y (u q) ≤ c)
    (hlower : ∀ x y, dist x y ≤ K * dist (u x) (u y) + C) :
    ∃ A : ℕ → Set Y,
      (∀ n, MeasurableSet (A n)) ∧ (∀ n, μ (A n) ≠ 0) ∧ (∀ n, μ (A n) ≠ ∞) ∧
      ∀ R : ℝ, 0 ≤ R → Tendsto (fun n => μ (cthickening R (A n)) / μ (A n))
        atTop (𝓝 1) := by
  classical
  let a := c + 1
  have ha : 0 < a := by dsimp [a] <;> linarith
  have hca : c < a := by dsimp [a] <;> linarith
  obtain ⟨E, hE, hlim⟩ := exists_sourceMetricFolner_sequence M hfinite
  obtain ⟨m, hm⟩ := exists_uniform_ball_multiplicity (r := a + a) u hfinite hK hlower
  let m' := m + 1
  have hmpos : 0 < (m' : ℝ) := by dsimp [m'] <;> positivity
  have hm' : ∀ (y : Y) (F : Finset X),
      (∀ x ∈ F, dist (u x) y ≤ a + a) → F.card ≤ m' :=
    fun y F hF => (hm y F hF).trans (Nat.le_succ m)
  let A := fun n => metricFolnerSet u (E n) a
  have hAfin (n : ℕ) : μ (A n) ≠ ∞ := by
    exact measure_biUnion_ne_top (E n).finite_toSet (fun _ _ => measure_ball_ne_top)
  have hApos (n : ℕ) : 0 < μ (A n) := by
    obtain ⟨p, hp⟩ := hE n
    exact (measure_ball_pos μ (u p) ha).trans_le (measure_mono (by
      intro y hy
      exact Set.mem_iUnion₂.mpr ⟨p, hp, hy⟩))
  have hameas (n : ℕ) : MeasurableSet (A n) := metricFolnerSet_measurable u (E n) a
  let b := μ.real (ball (1 : Y) a)
  have hbpos : 0 < b :=
    ENNReal.toReal_pos (measure_ball_pos μ 1 ha).ne' measure_ball_ne_top
  have hlowerA (n : ℕ) : (b / m') * (E n).card ≤ μ.real (A n) := by
    have hv := metricFolnerSet_volume_lower μ u (E n) ha m' hm'
    have hr := ENNReal.toReal_mono (ENNReal.mul_ne_top (by simp) (hAfin n)) hv
    simp only [ENNReal.toReal_mul, ENNReal.toReal_natCast] at hr
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hmpos).mpr
    simpa only [b, Measure.real, mul_comm] using hr
  refine ⟨A, hameas, fun n => (hApos n).ne', hAfin, fun R hR => ?_⟩
  let S := K * (c + (R + 1) + a) + C
  let B := fun n => finiteMetricNeighborhood hfinite (E n) S \ E n
  let β := μ.real (closedBall (1 : Y) c)
  have hbound (n : ℕ) : μ (cthickening R (A n) \ A n) ≤
      ((B n).card : ℝ≥0∞) * μ (closedBall (1 : Y) c) :=
    metricFolnerSet_boundary_volume μ hfinite u (E n) hca hK hR hsurj hlower
  have hbdFin (n : ℕ) : μ (cthickening R (A n) \ A n) ≠ ∞ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) measure_closedBall_lt_top.ne) (hbound n)
  have hsplit (n : ℕ) : μ (cthickening R (A n)) =
      μ (cthickening R (A n) \ A n) + μ (A n) := by
    have h := measure_sdiff_add_inter (μ := μ) (cthickening R (A n)) (hameas n)
    rw [Set.inter_eq_right.mpr (self_subset_cthickening (A n))] at h
    exact h.symm
  have hNfin (n : ℕ) : μ (cthickening R (A n)) ≠ ∞ := by
    rw [hsplit n]
    exact ENNReal.add_ne_top.mpr ⟨hbdFin n, hAfin n⟩
  have hupper (n : ℕ) : μ.real (cthickening R (A n)) ≤
      μ.real (A n) + β * (B n).card := by
    have hr := ENNReal.toReal_mono
      (ENNReal.mul_ne_top (by simp) measure_closedBall_lt_top.ne) (hbound n)
    simp only [ENNReal.toReal_mul, ENNReal.toReal_natCast] at hr
    change (μ (cthickening R (A n))).toReal ≤ _
    rw [hsplit n, ENNReal.toReal_add (hbdFin n) (hAfin n)]
    dsimp only [Measure.real, β]
    linarith
  have hreal : Tendsto (fun n => μ.real (cthickening R (A n)) / μ.real (A n))
      atTop (𝓝 1) := by
    apply tendsto_ratio_one_of_boundary _ _ (fun n => ((E n).card : ℝ))
      (fun n => ((B n).card : ℝ)) (div_pos hbpos hmpos) ENNReal.toReal_nonneg
      (fun n => by exact_mod_cast (hE n).card_pos) (fun _ => Nat.cast_nonneg _)
      hlowerA _ hupper (hlim S)
    intro n
    exact measureReal_mono (self_subset_cthickening (A n)) (hNfin n)
  have heq (n : ℕ) : ENNReal.ofReal (μ.real (cthickening R (A n)) / μ.real (A n)) =
      μ (cthickening R (A n)) / μ (A n) := by
    change ENNReal.ofReal ((μ (cthickening R (A n))).toReal / (μ (A n)).toReal) = _
    rw [ENNReal.ofReal_div_of_pos (ENNReal.toReal_pos (hApos n).ne' (hAfin n))]
    rw [ENNReal.ofReal_toReal (hNfin n), ENNReal.ofReal_toReal (hAfin n)]
  simpa only [Function.comp_def, heq, ENNReal.ofReal_one] using
    ENNReal.continuous_ofReal.continuousAt.tendsto.comp hreal

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_MetricFolnerUnimodular
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Metric Følner sets force right invariance of Haar measure

Right translation moves every point a fixed distance in a left invariant
metric. A nontrivial modular character contradicts the neighborhood-volume
ratio tending to one.
-/

noncomputable section

namespace PolycyclicRecognition

open MeasureTheory Filter
open scoped Topology ENNReal

theorem isMulRightInvariant_of_metricFolner
    {G ι : Type*} [Group G] [MetricSpace G] [IsTopologicalGroup G]
    [IsIsometricSMul G G] [LocallyCompactSpace G]
    [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsHaarMeasure] [Measure.InnerRegular μ]
    {l : Filter ι} [l.NeBot] (A : ι → Set G)
    (hA : ∀ i, MeasurableSet (A i))
    (hzero : ∀ i, μ (A i) ≠ 0) (hfinite : ∀ i, μ (A i) ≠ ∞)
    (hratio : ∀ R : ℝ, 0 ≤ R →
      Tendsto (fun i => μ (Metric.cthickening R (A i)) / μ (A i)) l (𝓝 1)) :
    μ.IsMulRightInvariant := by
  have hle (g : G) : Measure.modularCharacter g ≤ 1 := by
    have hbound (i : ι) : (Measure.modularCharacter g : ℝ≥0∞) ≤
        μ (Metric.cthickening (dist (1 : G) g) (A i)) / μ (A i) := by
      apply (ENNReal.le_div_iff_mul_le (Or.inl (hzero i)) (Or.inl (hfinite i))).mpr
      have hsubset : (fun x : G => x * g) ⁻¹' A i ⊆
          Metric.cthickening (dist (1 : G) g) (A i) := by
        intro x hx
        apply Metric.mem_cthickening_of_dist_le x (x * g) _ _ hx
        have hh := dist_mul_left x (1 : G) g
        simpa only [mul_one] using hh.le
      have hm := μ.mono hsubset
      change μ ((fun x : G => x * g) ⁻¹' A i) ≤
        μ (Metric.cthickening (dist (1 : G) g) (A i)) at hm
      rw [← Measure.map_apply (measurable_mul_const g) (hA i),
        Measure.map_right_mul_eq_modularCharacterFun_smul μ g] at hm
      rw [Measure.smul_apply] at hm
      change (Measure.modularCharacter g : ℝ≥0∞) * μ (A i) ≤ _ at hm
      exact hm
    have hh := ge_of_tendsto (hratio (dist (1 : G) g) dist_nonneg)
      (Eventually.of_forall hbound)
    exact_mod_cast hh
  have heq (g : G) : Measure.modularCharacter g = 1 := by
    apply le_antisymm (hle g)
    calc
      1 = Measure.modularCharacter g * Measure.modularCharacter g⁻¹ := by
        rw [← map_mul, mul_inv_cancel, map_one]
      _ ≤ Measure.modularCharacter g * 1 :=
        mul_le_mul_of_nonneg_left (hle g⁻¹) (zero_le : 0 ≤ Measure.modularCharacter g)
      _ = Measure.modularCharacter g := mul_one _
  refine ⟨fun g => ?_⟩
  rw [Measure.map_right_mul_eq_modularCharacterFun_smul μ g,
    show Measure.modularCharacterFun g = 1 from heq g, one_smul]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_CoarseModelUnimodular
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instNonemptyBases _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_nonempty _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Unimodularity of the Lie model follows from the original comparison group

The quasi-isometry contributes its lower bound and coarse surjectivity.
Polycyclicity contributes a proved invariant mean; no model-unimodularity
hypothesis is retained.
-/

noncomputable section

namespace PolycyclicRecognition

open Metric MeasureTheory

theorem isMulRightInvariant_of_coarse_virtualPolycyclic
    {P G : Type*} [Group P] [MetricSpace P] [IsIsometricSMul P P] [DecidableEq P]
    [Group G] [MetricSpace G] [IsTopologicalGroup G] [IsIsometricSMul G G]
    [ProperSpace G] [MeasurableSpace G] [BorelSpace G] [MeasurableMul G]
    (μ : Measure G) [μ.IsHaarMeasure] [Measure.InnerRegular μ]
    (hP : IsVirtuallyPolycyclic P)
    (hfinite : ∀ R : ℝ, (closedBall (1 : P) R).Finite)
    (u : P → G) {c K C : ℝ} (hc : 0 ≤ c) (hK : 0 ≤ K)
    (hsurj : ∀ y, ∃ p, dist y (u p) ≤ c)
    (hlower : ∀ x y, dist x y ≤ K * dist (u x) (u y) + C) :
    μ.IsMulRightInvariant := by
  obtain ⟨A, hA, hzero, hfin, hratio⟩ := exists_metricFolner_sequence
    (invariantMean_of_isVirtuallyPolycyclic hP).some hfinite μ u hc hK hsurj hlower
  exact isMulRightInvariant_of_metricFolner μ A hA hzero hfin hratio

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
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_UnivariateRemez
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # An elementary one-variable Remez bound

The constant is deliberately coarse. Only a fixed power of inverse length is
needed in the subexponential geometric argument.
-/

noncomputable section
namespace PolycyclicRecognition

open Set Metric MeasureTheory Polynomial

theorem univariate_remez_bound (D : ℕ) (hD : 1 ≤ D) (p : ℝ[X])
    (hp : p.natDegree ≤ D) (R : ℝ) (hR : 1 ≤ R)
    (S : Set ℝ) (hS : S ⊆ closedBall 0 R) (hm : 0 < (volume S).toReal)
    (η : ℝ) (hη : 0 ≤ η) (hvalues : ∀ x ∈ S, |p.eval x| ≤ η)
    (x : ℝ) (hx : x ∈ closedBall 0 R) :
    |p.eval x| ≤
      (8 * ((D + 1 : ℕ) : ℝ) ^ 2 * (1 + R) / (volume S).toReal) ^ D * η := by
  classical
  let N : ℝ := (D + 1 : ℕ)
  let m := (volume S).toReal
  let δ := m / (4 * N)
  have hN : 1 ≤ N := by dsimp [N]; norm_cast; omega
  have hNpos : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have hδ : 0 < δ := div_pos hm (by positivity)
  have hlength : 2 * N * δ < m := by
    dsimp [δ]
    field_simp
    nlinarith
  obtain ⟨s, hs, hsS, hsep⟩ :=
    exists_separated_finset_of_length S δ hδ (D + 1) hlength
  have hdegree : p.degree < s.card := by
    rw [hs]
    exact (natDegree_le_iff_degree_le.mp hp).trans_lt (by exact_mod_cast Nat.lt_succ_self D)
  have hR0 : 0 ≤ R := zero_le_one.trans hR
  have hb := polynomial_bound_of_separated_nodes p s hdegree δ R η hδ hR0 hη hsep
    (fun a ha => by simpa [mem_closedBall, Real.dist_eq] using hS (hsS ha))
    (fun a ha => hvalues a (hsS ha)) x
    (by simpa [mem_closedBall, Real.dist_eq] using hx)
  rw [hs, Nat.add_sub_cancel] at hb
  change |p.eval x| ≤ N * η * (2 * R / δ) ^ D at hb
  have hNpow : N ≤ N ^ D := by
    calc
      N = N ^ 1 := (pow_one N).symm
      _ ≤ N ^ D := pow_le_pow_right₀ hN hD
  have hbase : N * (2 * R / δ) ≤ 8 * N ^ 2 * (1 + R) / m := by
    have heq : N * (2 * R / δ) = 8 * N ^ 2 * R / m := by
      dsimp [δ]
      field_simp
      ring
    rw [heq]
    exact div_le_div_of_nonneg_right (by nlinarith [sq_nonneg N]) hm.le
  calc
    |p.eval x| ≤ N * η * (2 * R / δ) ^ D := hb
    _ ≤ N ^ D * η * (2 * R / δ) ^ D := by gcongr
    _ = (N * (2 * R / δ)) ^ D * η := by rw [mul_pow]; ring
    _ ≤ (8 * N ^ 2 * (1 + R) / m) ^ D * η := by
      apply mul_le_mul_of_nonneg_right _ hη
      exact pow_le_pow_left₀ (by positivity) hbase D

/-- The scalar interval sublevel estimate. -/
theorem exists_univariate_remez_constant (D : ℕ) (hD : 1 ≤ D) :
    ∃ A : ℝ, 0 < A ∧
      ∀ (p : ℝ[X]), p.natDegree ≤ D → ∀ R : ℝ, 1 ≤ R →
      ∀ S : Set ℝ, S ⊆ closedBall 0 R → 0 < (volume S).toReal →
      ∀ η : ℝ, 0 ≤ η → (∀ x ∈ S, |p.eval x| ≤ η) →
      ∀ x ∈ closedBall 0 R,
        |p.eval x| ≤ (A * (1 + R) / (volume S).toReal) ^ D * η := by
  refine ⟨8 * ((D + 1 : ℕ) : ℝ) ^ 2, by positivity, ?_⟩
  exact fun p hp R hR S hS hm η hη hv x hx =>
    univariate_remez_bound D hD p hp R hR S hS hm η hη hv x hx

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_CoordinateRemez
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A coarse multivariable Remez inequality by slicing

Iterating the elementary interval estimate loses a factor of dimension in the
exponent. The geometric application only requires a fixed polynomial loss.
-/

noncomputable section
namespace PolycyclicRecognition

open Set Metric MeasureTheory

theorem coordinate_polynomial_remez (n D : ℕ) (hD : 1 ≤ D) :
    ∃ A : ℝ, 0 < A ∧
      ∀ f : (Fin n → ℝ) → ℝ, CoordinatePolynomial n D f →
      ∀ R : ℝ, 1 ≤ R → ∀ S : Set (Fin n → ℝ),
      MeasurableSet S → S ⊆ closedBall 0 R → 0 < (volume S).toReal →
      ∀ η : ℝ, 0 ≤ η → (∀ x ∈ S, |f x| ≤ η) →
      ∀ x ∈ closedBall 0 R,
        |f x| ≤ (A * (1 + R) ^ n / (volume S).toReal) ^ (n * D) * η := by
  classical
  obtain ⟨C, hC, hline⟩ := exists_univariate_remez_constant D hD
  induction n with
  | zero =>
    refine ⟨1, by norm_num, ?_⟩
    intro f _ R _ S _ _ hm η _ hv x _
    have hne : S.Nonempty := by
      by_contra h
      have he := Set.not_nonempty_iff_eq_empty.mp h
      simp [he] at hm
    obtain ⟨y, hy⟩ := hne
    have he : y = x := Subsingleton.elim _ _
    simpa only [zero_mul, pow_zero, one_mul, he] using hv y hy
  | succ n ih =>
    obtain ⟨A, hA, hind⟩ := ih
    let B := max (2 ^ (n + 1) * C) (4 * A)
    have hB : 0 < B := (by positivity : 0 < 4 * A).trans_le (le_max_right _ _)
    refine ⟨B, hB, ?_⟩
    intro f hf R hR S hS hSR hm η hη hv x hx
    have hRpos : 0 < R := zero_lt_one.trans_le hR
    have hR0 : 0 ≤ R := hRpos.le
    let m := (volume S).toReal
    let q := m / (2 * (2 * R) ^ n)
    have hq : 0 < q := by dsimp [q, m] <;> positivity
    obtain ⟨T, hT, hTR, hmass, hfib⟩ :=
      exists_large_coordinate_sections n R hRpos S hS hSR hm
    have hTpos : 0 < (volume T).toReal :=
      (div_pos hm (by positivity : 0 < 4 * R)).trans_le hmass
    let b := B * (1 + R) ^ (n + 1) / m
    have hb : 0 < b := by dsimp [b, m] <;> positivity
    let η' := b ^ D * η
    have hη' : 0 ≤ η' := by dsimp [η'] <;> positivity
    have hx' : x 0 ∈ closedBall 0 R ∧ Fin.tail x ∈ closedBall 0 R :=
      (mem_closedBall_cons R hR0 (x 0) (Fin.tail x)).mp (by simpa only [Fin.cons_self_tail] using hx)
    have hvT (y : Fin n → ℝ) (hy : y ∈ T) : |f (Fin.cons (x 0) y)| ≤ η' := by
      let E := {t : ℝ | Fin.cons t y ∈ S}
      have hE : E ⊆ closedBall 0 R := fun t ht =>
        ((mem_closedBall_cons R hR0 t y).mp (hSR ht)).1
      have hEm : q ≤ (volume E).toReal := hfib y hy
      have hEpos : 0 < (volume E).toReal := hq.trans_le hEm
      obtain ⟨p, hp, he⟩ := hf.head y
      have hh := hline p hp R hR E hE hEpos η hη
        (fun t ht => by rw [he]; exact hv _ ht) (x 0) hx'.1
      rw [he] at hh
      have hratio : C * (1 + R) / (volume E).toReal ≤ b := by
        calc
          C * (1 + R) / (volume E).toReal ≤ C * (1 + R) / q :=
            div_le_div_of_nonneg_left (by positivity) hq hEm
          _ = (2 ^ (n + 1) * C) * (1 + R) * R ^ n / m := by
            dsimp [q]
            rw [mul_pow, pow_succ]
            field_simp
          _ ≤ B * (1 + R) ^ (n + 1) / m := by
            apply div_le_div_of_nonneg_right _ hm.le
            calc
              (2 ^ (n + 1) * C) * (1 + R) * R ^ n ≤
                  B * (1 + R) * (1 + R) ^ n := by
                apply mul_le_mul
                · exact mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
                · exact pow_le_pow_left₀ hR0 (by linarith) n
                · positivity
                · positivity
              _ = B * (1 + R) ^ (n + 1) := by rw [pow_succ]; ring
      exact hh.trans (mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (by positivity) hratio D) hη)
    have hpoint := hind (fun y => f (Fin.cons (x 0) y)) (hf.tail (x 0))
      R hR T hT hTR hTpos η' hη' hvT (Fin.tail x) hx'.2
    rw [Fin.cons_self_tail] at hpoint
    have hratio : A * (1 + R) ^ n / (volume T).toReal ≤ b := by
      calc
        A * (1 + R) ^ n / (volume T).toReal ≤
            A * (1 + R) ^ n / (m / (4 * R)) :=
          div_le_div_of_nonneg_left (by positivity) (div_pos hm (by positivity)) hmass
        _ = (4 * A) * R * (1 + R) ^ n / m := by field_simp
        _ ≤ B * (1 + R) ^ (n + 1) / m := by
          apply div_le_div_of_nonneg_right _ hm.le
          calc
            (4 * A) * R * (1 + R) ^ n ≤ B * (1 + R) * (1 + R) ^ n := by
              apply mul_le_mul_of_nonneg_right _ (by positivity)
              exact mul_le_mul (le_max_right _ _) (by linarith) hR0 hB.le
            _ = B * (1 + R) ^ (n + 1) := by rw [pow_succ]; ring
    calc
      |f x| ≤ (A * (1 + R) ^ n / (volume T).toReal) ^ (n * D) * η' := hpoint
      _ ≤ b ^ (n * D) * η' := mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (by positivity) hratio _) hη'
      _ = b ^ ((n + 1) * D) * η := by
        dsimp [η']
        rw [← mul_assoc, ← pow_add]
        congr 2
        ring

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_FiniteWordMetric
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finite_templateSymmetryGroup _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteSubtypeLinearEquivRealIdMemSubgroupLinearSupportSymmetryGroup _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The concrete word metrics used in the metric-free main statement -/

noncomputable section
namespace PolycyclicRecognition

open Set Metric

theorem finite_lists_length_le (A : Type*) [Finite A] (n : ℕ) :
    {l : List A | l.length ≤ n}.Finite := by
  induction n with
  | zero => simp
  | succ n ih =>
    apply ((Set.finite_singleton ([] : List A)).union
      ((Set.toFinite (Set.univ : Set A)).image2 List.cons ih)).subset
    intro l hl
    cases l with
    | nil => exact Or.inl rfl
    | cons a l =>
      exact Or.inr ⟨a, Set.mem_univ _, l, by simpa using hl, rfl⟩

namespace WordMetric

variable {G I : Type*} [Group G] (P : Group.Generators G I)

theorem discrete : letI := P.normedGroup; DiscreteTopology G := by
  let := P.normedGroup
  apply DiscreteTopology.of_forall_le_dist (show (0 : ℝ) < 1 by norm_num)
  intro x y hxy
  rw [dist_eq]
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr (by
    intro hzero
    exact hxy (inv_mul_eq_one.mp (P.wordLength_eq_zero_iff.mp hzero)))

theorem finite_closedBall [Finite I] (x : G) (R : ℝ) :
    letI := P.normedGroup
    (closedBall x R).Finite := by
  let := P.normedGroup
  apply ((finite_lists_length_le (I × Bool) ⌈R⌉₊).image
    (fun l => x * P.wordProd l)).subset
  intro y hy
  obtain ⟨l, hl, he⟩ := P.exists_isGeodesic (x⁻¹ * y)
  refine ⟨l, ?_, by simp [he]⟩
  have hlen : (l.length : ℝ) ≤ R := by
    rw [mem_closedBall, dist_comm, dist_eq, ← he, hl.eq] at hy
    exact hy
  exact_mod_cast hlen.trans (Nat.le_ceil R)

theorem proper [Finite I] : letI := P.normedGroup; ProperSpace G :=
  by
    let := P.normedGroup
    exact ⟨fun x R => (finite_closedBall P x R).isCompact⟩

end WordMetric

/-- A finitely generated group admits the concrete proper, discrete word
metric and its linear chains, without an external metric-existence input. -/
theorem exists_finite_word_metric (G : Type*) [Group G] [Group.FG G] :
    ∃ d : MetricSpace G, letI := d
      DiscreteTopology G ∧ IsIsometricSMul G G ∧ ProperSpace G ∧
        Nonempty (LinearMetricChains G) := by
  obtain ⟨n, ⟨P⟩⟩ := Group.fg_iff_nonempty_finite_generators.mp (inferInstance : Group.FG G)
  exact ⟨P.normedGroup.toMetricSpace, WordMetric.discrete P, WordMetric.leftInvariant P,
    WordMetric.proper P, ⟨WordMetric.chains P⟩⟩

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_ProperCocompactMetric
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instNonemptyBases _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_nonempty _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Metric comparison through a proper cocompact homomorphism

Properness bounds preimages of target balls. A coarse section and explicit
linear metric chains then give the lower quasi-isometry inequality. Together
with the continuous-homomorphism upper bound this is the metric part of the
Milnor--Švarc comparison, proved here without a recognition hypothesis.
-/

noncomputable section

namespace PolycyclicRecognition

open Metric Set

variable {G H : Type*} [Group G] [Group H] [MetricSpace G] [MetricSpace H]
  [IsIsometricSMul G G] [IsIsometricSMul H H]

/-- A proper homomorphism has uniformly bounded preimages of bounded
group differences. Compactness of the kernel is included in this argument. -/
theorem properHom_bounded_preimage_steps [ProperSpace H]
    (f : G →* H) (hproper : IsProperMap f) (R : ℝ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ x y, dist (f x) (f y) ≤ R → dist x y ≤ D := by
  have hcompact := hproper.isCompact_preimage (isCompact_closedBall (1 : H) R)
  obtain ⟨D, hD⟩ := hcompact.bddAbove_image (continuous_const.dist continuous_id).continuousOn
  refine ⟨max D 0, le_max_right _ _, fun x y hxy => ?_⟩
  have hmem : x⁻¹ * y ∈ f ⁻¹' closedBall (1 : H) R := by
    change dist (f (x⁻¹ * y)) 1 ≤ R
    rw [map_mul, map_inv, dist_comm, dist_one_groupDifference]
    exact hxy
  have hb : dist (1 : G) (x⁻¹ * y) ≤ D := hD (mem_image_of_mem _ hmem)
  rw [dist_one_groupDifference] at hb
  exact hb.trans (le_max_left _ _)

omit [MetricSpace G] [IsIsometricSMul G G] in
/-- Cocompactness, expressed as a compact cover of right image cosets,
gives the metric coarse-surjectivity radius. -/
theorem compact_image_cover_coarsely_surjective (f : G →* H)
    (K : Set H) (hK : IsCompact K)
    (hcover : ∀ h : H, ∃ (g : G) (k : H), k ∈ K ∧ f g * k = h) :
    ∃ E : ℝ, 0 ≤ E ∧ ∀ h : H, ∃ g : G, dist h (f g) ≤ E := by
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall (1 : H)
  refine ⟨max R 0, le_max_right _ _, fun h => ?_⟩
  obtain ⟨g, k, hk, rfl⟩ := hcover h
  refine ⟨g, ?_⟩
  have hkR : dist k 1 ≤ R := hR hk
  calc
    dist (f g * k) (f g) = dist k 1 := by simpa only [mul_one] using dist_mul_left (f g) k 1
    _ ≤ max R 0 := hkR.trans (le_max_left _ _)

/-- The lower quasi-isometry inequality is a consequence of properness,
coarse surjectivity, and target chains. No injectivity is required. -/
theorem properHom_coarse_lower [ProperSpace H] (C : LinearMetricChains H)
    (f : G →* H) (hproper : IsProperMap f) {E : ℝ}
    (hsurj : ∀ h, ∃ g, dist h (f g) ≤ E) :
    ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧
      ∀ x y, dist x y ≤ A * dist (f x) (f y) + B := by
  choose r hr using hsurj
  obtain ⟨D, hD, hpre⟩ := properHom_bounded_preimage_steps f hproper (E + C.step + E)
  obtain ⟨L, hL, herror⟩ := properHom_bounded_preimage_steps f hproper E
  have hstep : ∀ x y : H, dist x y ≤ C.step → dist (r x) (r y) ≤ D := by
    intro x y hxy
    apply hpre
    calc
      dist (f (r x)) (f (r y)) ≤
          dist (f (r x)) x + dist x y + dist y (f (r y)) := dist_triangle4 _ _ _ _
      _ ≤ E + C.step + E := by
        exact add_le_add (add_le_add ((dist_comm (f (r x)) x).trans_le (hr x)) hxy) (hr y)
  have hrbound := C.coarseLipschitz r hD hstep
  have herr (x : G) : dist x (r (f x)) ≤ L := herror x (r (f x)) (hr (f x))
  refine ⟨D * C.slope, D * C.error + (L + L),
    mul_nonneg hD C.slope_nonneg,
    add_nonneg (mul_nonneg hD C.error_nonneg) (add_nonneg hL hL), fun x y => ?_⟩
  calc
    dist x y ≤ dist x (r (f x)) + dist (r (f x)) (r (f y)) + dist (r (f y)) y :=
      dist_triangle4 _ _ _ _
    _ ≤ L + ((D * C.slope) * dist (f x) (f y) + D * C.error) + L := by
      exact add_le_add (add_le_add (herr x) (hrbound (f x) (f y)))
        ((dist_comm (r (f y)) y).trans_le (herr y))
    _ = (D * C.slope) * dist (f x) (f y) + (D * C.error + (L + L)) := by ring

/-- A continuous proper homomorphism with compact image-coset cover is a
metric quasi-isometry when both metrics have the stated linear chains. -/
theorem proper_cocompact_hom_quasiIsometry [ProperSpace G] [ProperSpace H]
    (CG : LinearMetricChains G) (CH : LinearMetricChains H)
    (f : G →* H) (hf : Continuous f) (hproper : IsProperMap f)
    (K : Set H) (hK : IsCompact K)
    (hcover : ∀ h : H, ∃ (g : G) (k : H), k ∈ K ∧ f g * k = h) :
    ∃ A B A' B' E : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ 0 ≤ A' ∧ 0 ≤ B' ∧ 0 ≤ E ∧
      (∀ x y, dist (f x) (f y) ≤ A * dist x y + B) ∧
      (∀ x y, dist x y ≤ A' * dist (f x) (f y) + B') ∧
      (∀ h, ∃ g, dist h (f g) ≤ E) := by
  obtain ⟨E, hE, hsurj⟩ := compact_image_cover_coarsely_surjective f K hK hcover
  obtain ⟨A, B, hA, hB, hupper⟩ := continuousHom_coarseLipschitz CG f hf
  obtain ⟨A', B', hA', hB', hlower⟩ := properHom_coarse_lower CH f hproper hsurj
  exact ⟨A, B, A', B', E, hA, hB, hA', hB', hE, hupper, hlower, hsurj⟩

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_MetricQuasiEquivalence
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Composing the metric comparisons in a Lie-model reduction

The proper cocompact homomorphism reduction has arrows in both directions.
We keep actual coarse inverse maps and their affine bounds, so that the
three-arrow zigzag can be composed without assuming a recognition result.
-/

noncomputable section

namespace PolycyclicRecognition

namespace MetricQuasiEquivalence

variable {X Y Z : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y] [PseudoMetricSpace Z]

/-- Recover the usual inequalities from actual coarse inverse maps. -/
theorem quasiIsometry_toFun (e : MetricQuasiEquivalence X Y) :
    ∃ K C K' C' E : ℝ, 0 ≤ K ∧ 0 ≤ C ∧ 0 ≤ K' ∧ 0 ≤ C' ∧ 0 ≤ E ∧
      (∀ x y, dist (e.toFun x) (e.toFun y) ≤ K * dist x y + C) ∧
      (∀ x y, dist x y ≤ K' * dist (e.toFun x) (e.toFun y) + C') ∧
      (∀ y, ∃ x, dist y (e.toFun x) ≤ E) := by
  obtain ⟨K, C, hK, hC, hf⟩ := e.toFun_control
  obtain ⟨K', C', hK', hC', hr⟩ := e.invFun_control
  obtain ⟨L, hL, hl⟩ := e.left_close
  obtain ⟨E, hE, he⟩ := e.right_close
  refine ⟨K, C, K', C' + (L + L), E, hK, hC, hK',
    add_nonneg hC' (add_nonneg hL hL), hE, hf, ?_, fun y => ⟨e.invFun y, he y⟩⟩
  intro x y
  calc
    dist x y ≤ dist x (e.invFun (e.toFun x)) +
        dist (e.invFun (e.toFun x)) (e.invFun (e.toFun y)) +
          dist (e.invFun (e.toFun y)) y := dist_triangle4 _ _ _ _
    _ ≤ L + (K' * dist (e.toFun x) (e.toFun y) + C') + L := by
      exact add_le_add (add_le_add (hl x) (hr _ _)) ((dist_comm _ _).trans_le (hl y))
    _ = K' * dist (e.toFun x) (e.toFun y) + (C' + (L + L)) := by ring

end MetricQuasiEquivalence

/-- Coarse inverse maps for a proper cocompact homomorphism, suitable for
composition along the model zigzag. -/
theorem nonempty_metricQuasiEquivalence_of_proper_cocompact_hom
    {G H : Type*} [Group G] [Group H] [MetricSpace G] [MetricSpace H]
    [IsIsometricSMul G G] [IsIsometricSMul H H] [ProperSpace G] [ProperSpace H]
    (CG : LinearMetricChains G) (CH : LinearMetricChains H)
    (f : G →* H) (hf : Continuous f) (hproper : IsProperMap f)
    (K : Set H) (hK : IsCompact K)
    (hcover : ∀ h : H, ∃ (g : G) (k : H), k ∈ K ∧ f g * k = h) :
    Nonempty (MetricQuasiEquivalence G H) := by
  obtain ⟨A, B, A', B', E, hA, hB, hA', hB', hE, hup, hlo, hsurj⟩ :=
    proper_cocompact_hom_quasiIsometry CG CH f hf hproper K hK hcover
  exact ⟨MetricQuasiEquivalence.ofQuasiIsometry f hA hB hA' hB' hE hup hlo hsurj⟩

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_RemezFromInterpolation
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial mass estimates from interpolation

Separated interpolation points and finite-measure Fubini give the
scalar sublevel estimate with exponent the dimension times the degree.
-/

noncomputable section
namespace PolycyclicRecognition

theorem remezPolynomialInput : RemezPolynomialInput := by
  intro n D _ hD
  obtain ⟨A, hA, hbound⟩ := coordinate_polynomial_remez n D hD
  refine ⟨A, hA, ?_⟩
  intro p hp R hR S hS hSR hm η hη hv x hx
  exact hbound (fun y => MvPolynomial.eval y p) (coordinatePolynomial_eval p hp)
    R hR S hS hSR hm η hη hv x hx

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_TriangulableLieModel
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The published reduction to a real-triangulable Lie model

Y. Cornulier and R. Tessera, *Geometric presentations of Lie groups and
their Dehn functions*, Publications Mathématiques de l'IHÉS 125 (2017),
79–219, Lemma 3.A.1, p.108, gives proper continuous homomorphisms with
cocompact images `G ← G₁ → G₂ ← G₃`, with `G₃` real triangulable.
Definition 1.1, p.83, identifies this last property with being isomorphic
to a closed connected group of invertible upper triangular real matrices.

The input below keeps precisely that topological reduction. Its metric
consequence is proved using the separately identified compatible-metric
existence input and the explicit inverse-map composition lemmas. No
adjoint basis, height control, or recognition conclusion is placed in the
published input.
-/

noncomputable section

namespace PolycyclicRecognition

/-- Compatible metrics turn one of the topological arrows into actual
coarse inverse maps. -/
theorem ProperCocompactHom.nonempty_metricQuasiEquivalence
    {A B : Type*} [Group A] [Group B] [TopologicalSpace A] [TopologicalSpace B]
    (f : ProperCocompactHom A B) (dA : ProperChainMetric A) (dB : ProperChainMetric B) :
    letI := dA.compatibleMetric
    letI := dB.compatibleMetric
    Nonempty (MetricQuasiEquivalence A B) := by
  let := dA.compatibleMetric
  let := dB.compatibleMetric
  let := dA.proper_compatibleMetric
  let := dB.proper_compatibleMetric
  let := dA.isometric_compatibleMetric
  let := dB.isometric_compatibleMetric
  obtain ⟨K, hK, hcover⟩ := f.cover
  exact nonempty_metricQuasiEquivalence_of_proper_cocompact_hom
    dA.chains_compatibleMetric dB.chains_compatibleMetric
    f.hom f.proper.continuous f.proper K hK hcover

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_TriangulableMetricChoice
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Choosing the endpoint metrics after the topological model reduction -/

noncomputable section
namespace PolycyclicRecognition

/-- The topological model can be fixed before either endpoint metric.
This permits selecting a minimizing-path metric on the Lie model while
retaining the comparison through the two locally compact intermediate groups. -/
theorem exists_realTriangulable_model_with_metric_choice
    (ct : CornulierTesseraModelInput) (metricInput : GeodesicMetricExistenceInput)
    (S : SimplyConnectedSolvableLieModel) :
    ∃ T : SimplyConnectedSolvableLieModel, IsRealTriangulable T ∧
      ∀ (dS : ProperChainMetric S.carrier) (dT : ProperChainMetric T.carrier),
        letI := dS.compatibleMetric
        letI := dT.compatibleMetric
        Nonempty (MetricQuasiEquivalence S.carrier T.carrier) := by
  obtain ⟨T, hT, G₁, G₂, ⟨f₁⟩, ⟨f₂⟩, ⟨f₃⟩⟩ := ct S
  obtain ⟨d₁⟩ := metricInput G₁.carrier G₁.compactlyGenerated
  obtain ⟨d₂⟩ := metricInput G₂.carrier G₂.compactlyGenerated
  refine ⟨T, hT, ?_⟩
  intro dS dT
  let := dS.compatibleMetric
  let := dT.compatibleMetric
  let := d₁.compatibleMetric
  let := d₂.compatibleMetric
  obtain ⟨e₁⟩ := f₁.nonempty_metricQuasiEquivalence d₁ dS
  obtain ⟨e₂⟩ := f₂.nonempty_metricQuasiEquivalence d₁ d₂
  obtain ⟨e₃⟩ := f₃.nonempty_metricQuasiEquivalence dT d₂
  exact ⟨(e₁.symm.trans e₂).trans e₃.symm⟩

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

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L]
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

set_option maxHeartbeats 1000000 in
/-- Retain the actual abelianization basis along with its homogeneous lifts.
This gives positivity for every later choice of a word basis. -/
theorem exists_cartan_abelianization_generators [FiniteDimensional ℝ L]
    {n : ℕ} (T : TriangularAdjoint L n) :
    ∃ (m : ℕ) (X : Fin m → cartanRootIdeal H) (χ : Fin m → Weight ℝ H L)
      (b : Basis (Fin m) ℝ (cartanRootAbelianization H)),
      (∀ i, (χ i).IsNonZero ∧ (X i : L) ∈ rootSpace H (χ i)) ∧
      (∀ i, (LieModule.lowerCentralSeries ℝ (cartanRootIdeal H)
        (cartanRootIdeal H) 1).toSubmodule.mkQ (X i) = b i) ∧
      LieSubalgebra.lieSpan ℝ (cartanRootIdeal H) (Set.range X) = ⊤ := by
  let := cartanRootIdeal_nilpotent H T
  let C := (LieModule.lowerCentralSeries ℝ (cartanRootIdeal H)
    (cartanRootIdeal H) 1).toSubmodule
  obtain ⟨b, X, hXS, hXq, hspan⟩ := exists_quotient_basis_lifts C (cartanGeneratorPool H)
    (span_sup_lowerCentralSeries_one_of_lieSpan _ (cartanGeneratorPool_lieSpan H T))
  choose χ hχ using hXS
  refine ⟨Module.finrank ℝ (cartanRootAbelianization H), X, χ, b, hχ, hXq, ?_⟩
  apply lieSubalgebra_eq_top_of_sup_lowerCentralSeries_one
  apply top_unique
  rw [← hspan]
  apply sup_le_sup_right
  exact Submodule.span_le.mpr LieSubalgebra.subset_lieSpan

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanWordModel
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instDecidableEqConeMixedWords _root_.OAI.PolycyclicRecognition.CartanWordModel.instFintypeConeMixedWords _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
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

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  (H : LieSubalgebra ℝ L) [H.IsCartanSubalgebra]

set_option maxHeartbeats 1000000 in
/-- Construction uses the triangular adjoint action and the actual Cartan
root ideal; no word-generation or nilpotence premise is left to the caller. -/
theorem nonempty_cartanWordModel {n : ℕ} (T : TriangularAdjoint L n) :
    Nonempty (CartanWordModel H) := by
  obtain ⟨m, X, χ, bq, hroot, hq, hgen⟩ := exists_cartan_abelianization_generators H T
  let := cartanRootIdeal_nilpotent H T
  obtain ⟨k, hk⟩ := LieModule.IsNilpotent.nilpotent ℝ (cartanRootIdeal H) (cartanRootIdeal H)
  exact ⟨⟨m, X, χ, fun i => (hroot i).1, fun i => (hroot i).2, bq, hq, hgen, k, hk⟩⟩

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
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CorrectedHeightRecognition
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

namespace OAI

/-! # Corrected-height recognition without the KMN input -/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory ThompsonNonamenability
open scoped IsMulCommutative

instance height_quotient_commutative
    {G W : Type} [Group G] [AddCommGroup W] (τ : G →* Multiplicative W) :
    IsMulCommutative (G ⧸ τ.ker) := by
  let f : (G ⧸ τ.ker) →* Multiplicative W :=
    τ.range.subtype.comp (QuotientGroup.quotientKerEquivRange τ).toMonoidHom
  have hf : Function.Injective f :=
    Subtype.val_injective.comp (QuotientGroup.quotientKerEquivRange τ).injective
  exact ⟨⟨fun a b => hf (by simp only [map_mul, mul_comm])⟩⟩

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_ExponentialBasisSection
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.height_quotient_commutative _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
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
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_HeightLipschitz
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.height_quotient_commutative _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Removing the additive error from a vector-valued homomorphism

A homomorphism to a real normed vector group scales exactly on powers.
Distances in a left-invariant source metric grow at most linearly on powers.
Consequently an affine upper bound for the homomorphism is already a genuine
Lipschitz bound. Compactness and the existing linear-chain argument supply
the affine bound for continuous homomorphisms.
-/

namespace PolycyclicRecognition

variable {G W : Type*} [Group G] [MetricSpace G] [IsIsometricSMul G G]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- The additive constant disappears by applying the bound to arbitrarily
large powers. No commutativity of the source is required. -/
theorem height_lipschitz_of_affine_bound (π : G →* Multiplicative W)
    {K C : ℝ} (hK : 0 ≤ K)
    (hbound : ∀ g, ‖(π g).toAdd‖ ≤ K * dist (1 : G) g + C) :
    ∀ x y, ‖(π x).toAdd - (π y).toAdd‖ ≤ K * dist x y := by
  have hone (g : G) : ‖(π g).toAdd‖ ≤ K * dist (1 : G) g := by
    by_contra h
    have hpos : 0 < ‖(π g).toAdd‖ - K * dist (1 : G) g :=
      sub_pos.mpr (lt_of_not_ge h)
    obtain ⟨n, hn⟩ := exists_nat_gt (C / (‖(π g).toAdd‖ - K * dist (1 : G) g))
    have hlarge : C < (n : ℝ) * (‖(π g).toAdd‖ - K * dist (1 : G) g) :=
      (div_lt_iff₀ hpos).mp hn
    have hp : ‖(π (g ^ n)).toAdd‖ = (n : ℝ) * ‖(π g).toAdd‖ := by
      rw [map_pow, toAdd_pow, ← Nat.cast_smul_eq_nsmul ℝ, norm_smul]
      simp
    have hb := hbound (g ^ n)
    have hd := mul_le_mul_of_nonneg_left (dist_one_pow_le g n) hK
    rw [hp] at hb
    nlinarith
  intro x y
  have h := hone (x⁻¹ * y)
  rw [map_mul, map_inv, toAdd_mul, toAdd_inv, dist_one_groupDifference] at h
  simpa only [← sub_eq_add_neg, add_comm (-(π x).toAdd), norm_sub_rev] using h

/-- A continuous vector-valued homomorphism from a proper group with linear
metric chains is globally Lipschitz. -/
theorem continuous_height_lipschitz [ProperSpace G] (C : LinearMetricChains G)
    (π : G →* Multiplicative W) (hπ : Continuous (fun g => (π g).toAdd)) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ x y, ‖(π x).toAdd - (π y).toAdd‖ ≤ K * dist x y := by
  obtain ⟨K, B, hK, _, hbound⟩ := continuousHom_coarseLipschitz C π hπ
  refine ⟨K, hK, height_lipschitz_of_affine_bound π (C := B) hK (fun g => ?_)⟩
  have h := hbound 1 g
  rw [map_one] at h
  change dist (0 : W) (π g).toAdd ≤ K * dist (1 : G) g + B at h
  simpa only [dist_zero_left] using h

end PolycyclicRecognition

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_IntrinsicCanonicalHeight
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.height_quotient_commutative _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
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

/-- The canonical height and its section, without exposing the optional
adjoint-kernel property used in the representation construction. -/
theorem exists_intrinsic_canonical_height {a : ℕ}
    (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, E)) G) a)
    (q : HeightSpace T.character ≃ₗ[ℝ] W)
    {Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G} (hExp : IsGroupExponential Exp) :
    ∃ π : G →* Multiplicative W,
      Continuous (fun g => (π g).toAdd) ∧
      (∀ x, (π (Exp x)).toAdd = q (heightProjection T.character x)) ∧
      Function.Surjective π ∧ Topology.IsQuotientMap (fun g => (π g).toAdd) ∧
      ∃ s : W → G, Continuous s ∧ s 0 = 1 ∧ ∀ w, (π (s w)).toAdd = w := by
  obtain ⟨π, hc, he, hs, hq, hsection, _, _⟩ :=
    exists_intrinsic_canonical_height_with_kernel T q hExp
  exact ⟨π, hc, he, hs, hq, hsection⟩

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_InvariantTriangularBasis
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.height_quotient_commutative _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
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
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_TriangularAdjointEmbedding
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.height_quotient_commutative _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
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
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_TriangularLieDifferential
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.height_quotient_commutative _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The differential of a triangular Lie-group realization

The differential of a continuous injective matrix-group homomorphism
is a Lie algebra homomorphism. Precisely, John M. Lee, *Introduction
to Smooth Manifolds*, second edition, GTM 218 (2013), Problem 20-11(b),
pp.537–538, gives automatic smoothness; Theorem 8.44, p.195, gives the
induced Lie algebra homomorphism; Proposition 8.41, pp.193–195, identifies
the matrix-group Lie algebra with the matrix commutator algebra. Its
injectivity follows from Proposition 7.17, pp.157–158 (see its proof using
Theorem 7.5 and the Global Rank Theorem 4.14(b)).

The input retains only the Lie homomorphism and its equality to the
matrix-valued derivative. Its injectivity is proved using faithful
one-parameter subgroups. The derivative is upper triangular and solvable, and admits a
simultaneous adjoint basis.
-/

noncomputable section

namespace PolycyclicRecognition

open scoped Manifold Matrix.Norms.Elementwise

attribute [local instance 100] LieRing.ofAssociativeRing

attribute [local instance] OAI.PolycyclicRecognition.matrixModelChartedSpace
open scoped Matrix.Norms.Operator in
/-- Faithfulness of the actual derivative follows from faithfulness of
the group map, without an immersion theorem. -/
theorem matrixLieDifferential_injective
    (S : SimplyConnectedSolvableLieModel) (n : ℕ)
    (ρ : S.carrier →* Matrix.GeneralLinearGroup (Fin n) ℝ)
    (hi : Function.Injective ρ)
    (d : GroupLieAlgebra (𝓘(ℝ, S.modelSpace)) S.carrier →ₗ⁅ℝ⁆
      Matrix (Fin n) (Fin n) ℝ)
    (hd : HasMFDerivAt (𝓘(ℝ, S.modelSpace))
      (𝓘(ℝ, Matrix (Fin n) (Fin n) ℝ))
      (fun g => (ρ g : Matrix (Fin n) (Fin n) ℝ)) 1
      d.toLinearMap.toContinuousLinearMap) : Function.Injective d :=
  injective_algebra_differential groupExponential_isGroupExponential ρ hi
    d.toLinearMap.toContinuousLinearMap hd

/-- Differentiating the identically zero entries below the diagonal
preserves upper triangularity. -/
theorem hasMFDerivAt_upperTriangular
    {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace G] [ChartedSpace E G] {n : ℕ}
    {f : G → Matrix (Fin n) (Fin n) ℝ} {a : G}
    {d : TangentSpace (𝓘(ℝ, E)) a →L[ℝ] Matrix (Fin n) (Fin n) ℝ}
    (hd : HasMFDerivAt (𝓘(ℝ, E)) (𝓘(ℝ, Matrix (Fin n) (Fin n) ℝ)) f a d)
    (hf : ∀ g, (f g).IsUpperTriangular) (v : TangentSpace (𝓘(ℝ, E)) a) :
    (d v).IsUpperTriangular := by
  intro i j hij
  let q₀ : Matrix (Fin n) (Fin n) ℝ →ₗ[ℝ] ℝ :=
    { toFun := fun A => A i j
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let q : Matrix (Fin n) (Fin n) ℝ →L[ℝ] ℝ :=
    q₀.toContinuousLinearMap
  have hq : HasMFDerivAt (𝓘(ℝ, E)) (𝓘(ℝ, ℝ))
      (q ∘ f) a (q.comp d) := q.hasFDerivAt.hasMFDerivAt.comp a hd
  have heq : q ∘ f = fun _ => (0 : ℝ) := by
    funext g
    exact hf g hij
  rw [heq] at hq
  have hz : q.comp d = 0 := by
    rw [← hq.mfderiv, mfderiv_const]
    rfl
  exact congrArg (fun l : TangentSpace (𝓘(ℝ, E)) a →L[ℝ] ℝ => l v) hz

/-- CT's actual closed triangular matrix realization supplies a
simultaneous adjoint basis once the narrow matrix-differential input is
given. The algebraic conclusions come from the proved matrix lemmas. -/
theorem IsRealTriangulable.exists_triangularAdjoint
    (differential : MatrixLieDifferentialInput)
    (S : SimplyConnectedSolvableLieModel) (hS : IsRealTriangulable S) :
    ∃ m : ℕ, Nonempty (TriangularAdjoint
      (GroupLieAlgebra (𝓘(ℝ, S.modelSpace)) S.carrier) m) := by
  obtain ⟨n, ρ, hρ, htri⟩ := hS
  obtain ⟨d, hderiv⟩ := differential S n ρ hρ.continuous hρ.injective
  have hd := matrixLieDifferential_injective S n ρ hρ.injective d hderiv
  apply nonempty_triangularAdjoint_of_triangular_representation d hd
  intro v
  exact hasMFDerivAt_upperTriangular (E := S.modelSpace) hderiv htri v

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_IntrinsicContractionModel
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.height_quotient_commutative _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.CartanFactorModel.heightRay_zero _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The height model and its contraction without a published global chart -/

noncomputable section
namespace PolycyclicRecognition

open Module
open scoped Manifold

theorem exists_intrinsic_height_model_with_controlled_contraction
    (ct : CornulierTesseraModelInput) (metric : GeodesicMetricExistenceInput)
    (riemannian : LieRiemannianMetricInput) (differential : MatrixLieDifferentialInput)
    (S : SimplyConnectedSolvableLieModel) :
    ∃ (R : SimplyConnectedSolvableLieModel) (a : ℕ)
      (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, R.modelSpace)) R.carrier) a),
      ∃ (dS : ProperChainMetric S.carrier) (dR : ProperMinimizingMetric R.carrier),
        letI := dS.compatibleMetric
        letI := dR.toProperChainMetric.compatibleMetric
        let W := EuclideanSpace ℝ (Fin (finrank ℝ (HeightSpace T.character)))
        Nonempty (MetricQuasiEquivalence S.carrier R.carrier) ∧
        Nonempty (ControlledContraction R.carrier) ∧
        ∃ (q : HeightSpace T.character ≃ₗ[ℝ] W)
          (Exp : GroupLieAlgebra (𝓘(ℝ, R.modelSpace)) R.carrier → R.carrier)
          (π : R.carrier →* Multiplicative W),
          IsGroupExponential Exp ∧
          (∀ v, (π (Exp v)).toAdd = q (heightProjection T.character v)) ∧
          Function.Surjective π ∧ Topology.IsQuotientMap (fun g => (π g).toAdd) ∧
          ∃ K : ℝ, 0 ≤ K ∧ ∀ x y,
            ‖(π x).toAdd - (π y).toAdd‖ ≤ K * dist x y := by
  obtain ⟨R, hR, hmetrics⟩ := exists_realTriangulable_model_with_metric_choice ct metric S
  obtain ⟨a, ⟨T⟩⟩ := IsRealTriangulable.exists_triangularAdjoint differential R hR
  obtain ⟨dS⟩ := S.nonempty_properChainMetric metric
  obtain ⟨dR, hcompat⟩ := riemannian R
  refine ⟨R, a, T, dS, dR, ?_⟩
  let := dS.compatibleMetric
  let := dR.toProperChainMetric.compatibleMetric
  let := dR.toProperChainMetric.proper_compatibleMetric
  let := dR.toProperChainMetric.isometric_compatibleMetric
  let : IsTopologicalGroup R.carrier :=
    topologicalGroup_of_lieGroup (𝓘(ℝ, R.modelSpace)) ⊤
  let W := EuclideanSpace ℝ (Fin (finrank ℝ (HeightSpace T.character)))
  let q : HeightSpace T.character ≃ₗ[ℝ] W := LinearEquiv.ofFinrankEq _ _ (by simp [W])
  let Exp := groupExponential (E := R.modelSpace) (G := R.carrier)
  have hExp : IsGroupExponential Exp := groupExponential_isGroupExponential
  obtain ⟨π, hπ, he, hsurj, hquot, _⟩ := exists_intrinsic_canonical_height T q hExp
  obtain ⟨K, hK, hLip⟩ := continuous_height_lipschitz
    dR.toProperChainMetric.chains_compatibleMetric π hπ
  obtain ⟨n, φ, hφ0, hf, hb⟩ := exists_intrinsic_smooth_coordinates T q Exp hExp π hπ he
  obtain ⟨hfLip, hbLip⟩ := hcompat n φ hf hb
  exact ⟨hmetrics dS dR.toProperChainMetric,
    ⟨ControlledContraction.ofChart φ hφ0 hfLip hbLip⟩,
    q, Exp, π, hExp, he, hsurj, hquot, K, hK, hLip⟩

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_LieModelUnimodular
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.height_quotient_commutative _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Unimodularity of the metric Lie model

Restrict the ambient quasi-isometry to an actual uniform lattice. Its
compact coset cover supplies coarse surjectivity, and its inherited
metric has finite balls. The previously proved metric Følner transfer
then makes the target Haar measure right invariant. No unimodularity
assumption is made about either ambient group.
-/

noncomputable section

namespace PolycyclicRecognition

open Metric MeasureTheory

section MetricComparison

variable {S G : Type*} [Group S] [Group G]
  [MetricSpace S] [IsTopologicalGroup S] [IsIsometricSMul S S] [ProperSpace S]
  [MetricSpace G] [IsTopologicalGroup G] [IsIsometricSMul G G] [ProperSpace G]
  [MeasurableSpace G] [BorelSpace G] [MeasurableMul G]

/-- The compact cover of a polycyclic uniform lattice and an ambient
quasi-isometry give right invariance of the target's actual Haar measure. -/
theorem IsUniformLattice.isMulRightInvariant_of_metricQuasiEquivalence
    {Λ : Subgroup S} (hΛ : IsUniformLattice Λ) (hpoly : IsPolycyclic Λ)
    (e : MetricQuasiEquivalence S G)
    (μ : Measure G) [μ.IsHaarMeasure] [Measure.InnerRegular μ] :
    μ.IsMulRightInvariant := by
  classical
  let : IsIsometricSMul Λ Λ := ⟨fun γ => Isometry.of_dist_eq (fun x y => by
    change dist ((γ : S) * (x : S)) ((γ : S) * (y : S)) = dist (x : S) (y : S)
    exact dist_mul_left (γ : S) (x : S) (y : S))⟩
  obtain ⟨K, C, K', C', E, hK, hC, hK', _hC', hE, hup, hlo, hsurj⟩ :=
    e.quasiIsometry_toFun
  obtain ⟨R, hR, hcover⟩ := hΛ.exists_covering_radius
  have hsurj' : ∀ y : G, ∃ x : Λ, dist y (e.toFun (x : S)) ≤ E + (K * R + C) := by
    intro y
    obtain ⟨s, hs⟩ := hsurj y
    obtain ⟨x, hx⟩ := hcover s
    refine ⟨x, (dist_triangle y (e.toFun s) (e.toFun (x : S))).trans ?_⟩
    exact add_le_add hs ((hup s (x : S)).trans
      (add_le_add (mul_le_mul_of_nonneg_left hx hK) le_rfl))
  have hE' : 0 ≤ E + (K * R + C) := by
    positivity
  exact isMulRightInvariant_of_coarse_virtualPolycyclic μ hpoly.isVirtuallyPolycyclic
    hΛ.finite_closedBall (fun x : Λ => e.toFun (x : S)) hE' hK' hsurj'
    (fun x y => hlo (x : S) (y : S))

end MetricComparison

open scoped Manifold

/-- The actual Lie model obtained by the CT metric comparison is
unimodular when its source contains the given uniform solvable lattice.
Farb–Weinberger is used only for polycyclicity of that lattice. -/
theorem SimplyConnectedSolvableLieModel.isMulRightInvariant_of_lattice_comparison
    (fw : FarbWeinbergerLatticeInput) (S T : SimplyConnectedSolvableLieModel)
    (Λ : Subgroup S.carrier) (hΛ : IsUniformLattice Λ)
    (dS : ProperChainMetric S.carrier) (dT : ProperChainMetric T.carrier)
    (e : letI := dS.compatibleMetric
      letI := dT.compatibleMetric
      MetricQuasiEquivalence S.carrier T.carrier)
    [MeasurableSpace T.carrier] [BorelSpace T.carrier]
    (μ : Measure T.carrier) [μ.IsHaarMeasure] [Measure.InnerRegular μ] :
    μ.IsMulRightInvariant := by
  let := dS.compatibleMetric
  let := dT.compatibleMetric
  let := dS.proper_compatibleMetric
  let := dT.proper_compatibleMetric
  let := dS.isometric_compatibleMetric
  let := dT.isometric_compatibleMetric
  let : IsTopologicalGroup S.carrier :=
    topologicalGroup_of_lieGroup (𝓘(ℝ, S.modelSpace)) ⊤
  let : IsTopologicalGroup T.carrier :=
    topologicalGroup_of_lieGroup (𝓘(ℝ, T.modelSpace)) ⊤
  exact hΛ.isMulRightInvariant_of_metricQuasiEquivalence (fw S Λ hΛ) e μ

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_MatrixDifferentialFromSmoothness
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.height_quotient_commutative _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Discharging the matrix Lie differential input

The representation is only assumed continuous. Automatic smoothness is
proved using exponential product coordinates, and the Lie-homomorphism law
is proved using related vector fields in a chart.
-/

noncomputable section
namespace PolycyclicRecognition

open scoped Manifold ContDiff Matrix.Norms.Operator

attribute [local instance 100] LieRing.ofAssociativeRing

attribute [local instance] OAI.PolycyclicRecognition.matrixDifferentialChartedSpace
theorem matrixLieDifferentialInput : MatrixLieDifferentialInput := by
  intro S n ρ hc _hi
  have hv : Continuous (fun g => (ρ g : Matrix (Fin n) (Fin n) ℝ)) :=
    Units.continuous_val.comp hc
  have hs : ContMDiff (𝓘(ℝ, S.modelSpace)) (𝓘(ℝ, Matrix (Fin n) (Fin n) ℝ)) ∞
      (fun g => (ρ g : Matrix (Fin n) (Fin n) ℝ)) :=
    contMDiff_of_continuous_unitsHom groupExponential_isGroupExponential ρ hv
  exact ⟨unitsHomLieDifferential ρ hs, hasMFDerivAt_unitsHomLieDifferential ρ hs⟩

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_SolvableGroupLieAlgebra
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.height_quotient_commutative _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
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
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Lattices_LatticeMetricChains
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.height_quotient_commutative _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Linear metric chains on a uniform lattice -/

noncomputable section
namespace PolycyclicRecognition

variable {G : Type*} [Group G] [MetricSpace G] [IsTopologicalGroup G]
  [IsIsometricSMul G G] {Λ : Subgroup G}

omit [IsTopologicalGroup G] in
/-- Rounding an ambient chain to a uniformly close lattice section keeps
the linear length bound and enlarges only the step size. -/
theorem IsUniformLattice.nonempty_linearMetricChains
    (hΛ : IsUniformLattice Λ) (C : LinearMetricChains G) :
    Nonempty (LinearMetricChains Λ) := by
  classical
  obtain ⟨r, R, hR, hr, _⟩ := hΛ.exists_metric_section
  let s : G → Λ := fun x => if h : x ∈ Λ then ⟨x, h⟩ else r x
  have hs (x : G) : dist x (s x : G) ≤ R := by
    dsimp [s]
    split
    · simpa using hR
    · exact hr x
  have hfix (x : Λ) : s x = x := by simp [s]
  refine ⟨{
    step := C.step + (R + R)
    step_pos := by linarith [C.step_pos]
    slope := C.slope
    slope_nonneg := C.slope_nonneg
    error := C.error
    error_nonneg := C.error_nonneg
    chain := ?_ }⟩
  intro x y
  obtain ⟨n, p, h0, hn, hlen, hstep⟩ := C.chain (x : G) (y : G)
  refine ⟨n, s ∘ p, by simpa only [Function.comp_apply, h0] using hfix x,
    by simpa only [Function.comp_apply, hn] using hfix y, hlen, ?_⟩
  intro i hi
  change dist (s (p i) : G) (s (p (i + 1)) : G) ≤ _
  calc
    _ ≤ dist (s (p i) : G) (p i) + dist (p i) (p (i + 1)) +
        dist (p (i + 1)) (s (p (i + 1)) : G) := dist_triangle4 _ _ _ _
    _ ≤ R + C.step + R := add_le_add (add_le_add
      ((dist_comm _ _).trans_le (hs _)) (hstep i hi)) (hs _)
    _ = C.step + (R + R) := by ring

omit [IsTopologicalGroup G] in
/-- Inclusion and a bounded section are metric quasi-inverses. -/
theorem IsUniformLattice.nonempty_metricQuasiEquivalence
    (hΛ : IsUniformLattice Λ) : Nonempty (MetricQuasiEquivalence Λ G) := by
  obtain ⟨r, R, hR, hr, hrlip⟩ := hΛ.exists_metric_section
  refine ⟨{
    toFun := Subtype.val
    invFun := r
    toFun_control := ⟨1, 0, by norm_num, by norm_num, fun x y => by
      change dist (x : G) (y : G) ≤ 1 * dist (x : G) (y : G) + 0
      simp⟩
    invFun_control := ⟨1, R + R, by norm_num, add_nonneg hR hR,
      fun x y => by simpa using hrlip x y⟩
    left_close := ⟨R, hR, fun x => hr x⟩
    right_close := ⟨R, hR, hr⟩ }⟩

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Lattices_OriginalLatticeComparison
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.height_quotient_commutative _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Metric comparison with the original finite-index lattice model -/

noncomputable section
namespace PolycyclicRecognition

open scoped Manifold

/-- The discrete finite-index and lattice comparisons become a metric
quasi-equivalence in the chosen ambient metric. The linear-chain condition
on the original group makes explicit the word-metric scope. -/
theorem nonempty_original_lattice_comparison
    {P : Type} [Group P] [MetricSpace P] [IsIsometricSMul P P]
    (CP : LinearMetricChains P)
    (hfinite : ∀ R : ℝ, (Metric.closedBall (1 : P) R).Finite)
    (Γ : Subgroup P) (hΓ : Γ.FiniteIndex)
    (S : SimplyConnectedSolvableLieModel) (Λ : Subgroup S.carrier)
    (hΛ : IsUniformLattice Λ) (iso : Γ ≃* Λ) (dS : ProperChainMetric S.carrier) :
    letI := dS.compatibleMetric
    Nonempty (MetricQuasiEquivalence P S.carrier) := by
  let := hΓ
  let := dS.compatibleMetric
  let := dS.proper_compatibleMetric
  let := dS.isometric_compatibleMetric
  let : IsTopologicalGroup S.carrier :=
    topologicalGroup_of_lieGroup (𝓘(ℝ, S.modelSpace)) ⊤
  let : IsIsometricSMul Λ Λ := ⟨fun γ => Isometry.of_dist_eq (fun x y => by
    change dist ((γ : S.carrier) * (x : S.carrier)) ((γ : S.carrier) * (y : S.carrier)) = _
    exact dist_mul_left (γ : S.carrier) (x : S.carrier) (y : S.carrier))⟩
  obtain ⟨CΛ⟩ := hΛ.nonempty_linearMetricChains dS.chains_compatibleMetric
  let ePΛ := ((finiteIndexCoarseEquivalence Γ).symm.trans
    (PolycyclicRecognition.MulEquiv.groupCoarseEquivalence iso)).metric
    CP CΛ hfinite hΛ.finite_closedBall
  obtain ⟨eΛS⟩ := hΛ.nonempty_metricQuasiEquivalence
  exact ⟨ePΛ.trans eΛS⟩

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Lattices_UniformLatticeFiniteGeneration
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.height_quotient_commutative _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite generation of a uniform lattice from metric chains

The bounded-distance lattice section sends ambient chains to bounded
lattice steps. The steps belong to one finite ball, which therefore
generates the lattice. This is the finite-generation part of the
Švarc argument, proved from compactness and explicit chains.
-/

noncomputable section

namespace PolycyclicRecognition

open Metric Set

variable {G : Type*} [Group G] [MetricSpace G] [IsTopologicalGroup G]
  [IsIsometricSMul G G] [ProperSpace G]

omit [IsTopologicalGroup G] [ProperSpace G] in
/-- A uniform lattice in a metric group with linear metric chains
has a finite generating set contained in a single induced metric ball. -/
theorem IsUniformLattice.exists_generating_ball {Λ : Subgroup G}
    (hΛ : IsUniformLattice Λ) (C : LinearMetricChains G) :
    ∃ B : ℝ, 0 ≤ B ∧
      Subgroup.closure (closedBall (1 : Λ) B) = ⊤ := by
  obtain ⟨r, R, hR, hr, hrlip⟩ := hΛ.exists_metric_section
  let B := R + R + C.step
  have hRB : R ≤ B := by dsimp [B] <;> linarith [C.step_pos]
  let K : Subgroup Λ := Subgroup.closure (closedBall (1 : Λ) B)
  have hsmall (x : Λ) (hx : dist (1 : G) (x : G) ≤ B) : x ∈ K := by
    apply Subgroup.subset_closure
    change dist (x : G) 1 ≤ B
    simpa only [dist_comm] using hx
  have hdiff (x y : Λ) (hxy : dist (x : G) (y : G) ≤ B) : x⁻¹ * y ∈ K := by
    apply hsmall
    change dist (1 : G) ((x : G)⁻¹ * (y : G)) ≤ B
    rwa [dist_one_groupDifference]
  refine ⟨B, hR.trans hRB, ?_⟩
  apply top_unique
  intro x _
  obtain ⟨n, p, hp0, hpn, _, hpstep⟩ := C.chain 1 (x : G)
  have hstart : r (p 0) ∈ K := by
    apply hsmall
    rw [hp0]
    exact (hr 1).trans hRB
  have hvertices : ∀ i ≤ n, r (p i) ∈ K := by
    intro i hi
    induction i with
    | zero => exact hstart
    | succ i ih =>
      have hi' : i < n := Nat.lt_of_succ_le hi
      have hprev := ih (Nat.le_of_lt hi')
      have hnext : (r (p i))⁻¹ * r (p (i + 1)) ∈ K := by
        apply hdiff
        have hs := (hrlip (p i) (p (i + 1))).trans
          (add_le_add (hpstep i hi') le_rfl)
        change dist (r (p i) : G) (r (p (i + 1)) : G) ≤ _ at hs
        simpa only [B, add_assoc, add_comm, add_left_comm] using hs
      simpa only [mul_inv_cancel_left] using K.mul_mem hprev hnext
  have hend : (r (p n))⁻¹ * x ∈ K := by
    apply hdiff
    rw [hpn, dist_comm]
    exact (hr x).trans hRB
  simpa only [mul_inv_cancel_left] using K.mul_mem (hvertices n le_rfl) hend

/-- Compactness and linear ambient chains give finite generation without
any algebraic structure theorem for lattices. -/
theorem IsUniformLattice.finitelyGenerated {Λ : Subgroup G}
    (hΛ : IsUniformLattice Λ) (C : LinearMetricChains G) : Group.FG Λ := by
  obtain ⟨B, _, hB⟩ := hΛ.exists_generating_ball C
  exact Group.fg_iff.mpr ⟨closedBall (1 : Λ) B, hB, hΛ.finite_closedBall B⟩

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Lattices_SolvableLatticePolycyclic
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.height_quotient_commutative _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanRealShadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polycyclicity of lattices in simply connected solvable Lie groups

Complex adjoint weights include rotations. Their normalized additive lifts
have nilpotent Lie kernel and a real vector-space quotient. Discrete subgroups
of the kernel are polycyclic, and finite generation controls the abelian image.
-/

noncomputable section
namespace PolycyclicRecognition
open scoped Manifold

/-- Every finitely generated discrete subgroup of a connected simply
connected finite-dimensional real solvable Lie group is polycyclic. -/
theorem isPolycyclic_finitelyGenerated_discrete_solvableLieGroup
    {E G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MetricSpace G] [ChartedSpace E G] [Group G] [LieGroup (𝓘(ℝ, E)) ⊤ G]
    [SimplyConnectedSpace G] [Group.IsSolvable G]
    (Γ : Subgroup G) [DiscreteTopology Γ] [Group.FG Γ] : IsPolycyclic Γ := by
  let L := GroupLieAlgebra (𝓘(ℝ, E)) G
  let : IsTopologicalGroup G := topologicalGroup_of_lieGroup (𝓘(ℝ, E)) ⊤
  let : LocallyPathConnectedSpace G := ChartedSpace.locallyPathConnectedSpace E G
  let : LieAlgebra.IsSolvable L := groupLieAlgebra_isSolvable (E := E) (G := G)
  obtain ⟨n, b, hb⟩ := exists_complex_triangular_adjoint_basis L
  let T : ComplexTriangularAdjoint L n := ⟨b, hb⟩
  let Exp := groupExponential (E := E) (G := G)
  have hExp : IsGroupExponential Exp := groupExponential_isGroupExponential
  obtain ⟨π, hπ, he⟩ := exists_additive_complex_adjoint_weights (Module.finBasis ℝ L) T hExp
  obtain ⟨q, hq, hqe⟩ := exists_range_restricted_complex_weights hExp T.weightMap π hπ he
  exact isPolycyclic_finitelyGenerated_discrete_of_linear_nilpotent_kernel
    T.kernelIdeal T.kernelIdeal_nilpotent T.weightMap.rangeRestrict
    T.weightMap.surjective_rangeRestrict (LinearMap.ker_rangeRestrict T.weightMap)
    Exp hExp q hq hqe Γ

/-- The full solvable lattice theorem used by the recognition argument. -/
theorem isPolycyclic_uniformLattice_solvableLieGroup
    (S : SimplyConnectedSolvableLieModel) (Λ : Subgroup S.carrier)
    (hΛ : IsUniformLattice Λ) : IsPolycyclic Λ := by
  obtain ⟨d⟩ := S.nonempty_properChainMetric geodesicMetricExistenceInput
  let := d.compatibleMetric
  let := d.proper_compatibleMetric
  let := d.isometric_compatibleMetric
  let : IsTopologicalGroup S.carrier := topologicalGroup_of_lieGroup (𝓘(ℝ, S.modelSpace)) ⊤
  let : DiscreteTopology Λ := hΛ.1
  let : Group.FG Λ := hΛ.finitelyGenerated d.chains_compatibleMetric
  exact isPolycyclic_finitelyGenerated_discrete_solvableLieGroup (E := S.modelSpace) Λ

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_RecognitionFromGromov
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Recognition from the polynomial-growth theorem

The geometric height estimate, lattice realization, finiteness, and duality
combine with the exact polynomial-growth statement of Gromov's theorem.
-/
noncomputable section
namespace PolycyclicRecognition
open Module LieAlgebra MeasureTheory
open scoped Manifold NNReal
attribute [local instance] stationaryL2Action zeroMeanL2Action

theorem recognition_and_lattice_of_gromov
    (gromov : ∀ (K : Type) [Group K] [DecidableEq K], GromovPolynomialGrowthInput K)
    {P J : Type} [Group P] [Group J] [MetricSpace P] [MetricSpace J]
    [IsIsometricSMul P P] [IsIsometricSMul J J] [Group.FG P] [Group.FG J]
    [DiscreteTopology J] [ProperSpace J]
    [MeasurableSpace J] [BorelSpace J] [MeasurableMul J]
    (e : MetricQuasiEquivalence P J) (hP : IsVirtuallyPolycyclic P)
    (CP : LinearMetricChains P)
    (hPfinite : ∀ r : ℝ, (Metric.closedBall (1 : P) r).Finite) :
    IsVirtuallyPolycyclic J ∧
      ∃ Γ : Subgroup J, Γ.FiniteIndex ∧
        ∃ (S : SimplyConnectedSolvableLieModel) (Λ : Subgroup S.carrier),
          IsUniformLattice Λ ∧ Nonempty (Γ ≃* Λ) := by
  classical
  obtain ⟨Γ, hΓ, S, Λ, hΛ, ⟨iso⟩⟩ :=
    exists_uniform_solvable_lattice_of_virtuallyPolycyclic dekimpeLatticeRealizationInput P hP
  obtain ⟨R, a, T, dS, dR, hmodel⟩ :=
    exists_intrinsic_height_model_with_controlled_contraction cornulierTesseraModelInput
      geodesicMetricExistenceInput lieRiemannianMetricInput matrixLieDifferentialInput S
  let := dS.compatibleMetric
  let := dR.toProperChainMetric.compatibleMetric
  let := dS.proper_compatibleMetric
  let := dS.isometric_compatibleMetric
  let := dR.toProperChainMetric.proper_compatibleMetric
  let := dR.toProperChainMetric.isometric_compatibleMetric
  let : IsTopologicalGroup S.carrier :=
    topologicalGroup_of_lieGroup (𝓘(ℝ, S.modelSpace)) ⊤
  let : IsTopologicalGroup R.carrier :=
    topologicalGroup_of_lieGroup (𝓘(ℝ, R.modelSpace)) ⊤
  let : MeasurableSpace R.carrier := borel _
  let : BorelSpace R.carrier := ⟨rfl⟩
  obtain ⟨⟨eSR⟩, ⟨c⟩, q, Exp, π, hExp, hπExp, _, _, K, hK, hπLip⟩ := hmodel
  obtain ⟨ePS⟩ := nonempty_original_lattice_comparison CP hPfinite Γ hΓ S Λ hΛ iso dS
  let u := e.symm.trans (ePS.trans eSR)
  let m : Measure R.carrier := Measure.haar
  let : m.IsMulRightInvariant :=
    SimplyConnectedSolvableLieModel.isMulRightInvariant_of_lattice_comparison
      isPolycyclic_uniformLattice_solvableLieGroup S R Λ hΛ
      dS dR.toProperChainMetric eSR m
  have hπ : LipschitzWith (⟨K, hK⟩ : ℝ≥0) (fun g => (π g).toAdd) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [dist_eq_norm]
    exact hπLip x y
  have hunimod (x : GroupLieAlgebra (𝓘(ℝ, R.modelSpace)) R.carrier) :
      LinearMap.trace ℝ _ (ad ℝ _ x) = 0 :=
    trace_ad_eq_zero_of_intrinsic_kernel_haar T q Exp hExp π hπ.continuous hπExp m x
  obtain ⟨x, hx⟩ := LieAlgebra.exists_isCartanSubalgebra_engel ℝ
    (GroupLieAlgebra (𝓘(ℝ, R.modelSpace)) R.carrier)
  let H := LieSubalgebra.engel ℝ x
  let : H.IsCartanSubalgebra := hx
  obtain ⟨M⟩ := nonempty_cartanWordModel H T
  have hheight := M.exists_uniform_height_intrinsic T hunimod q Exp hExp
    m π hπExp hπ
    dR.minimizing_compatibleMetric remezPolynomialInput geodesicMetricExistenceInput
  exact recognition_and_lattice_of_uniform_normalized_height_proved dekimpeLatticeRealizationInput
    e hP hPfinite T _ q π Exp hExp hπExp u gromov (M.supportIn T hunimod q)
    hπ c dR.minimizing_compatibleMetric hheight


theorem group_recognition_of_gromov_oai
    (gromov : ∀ (K : Type) [Group K] [DecidableEq K], GromovPolynomialGrowthInput K)
    {P J : Type} [Group P] [Group J] [Group.FG P] [Group.FG J]
    (e : GroupCoarseEquivalence P J) (hP : IsVirtuallyPolycyclic P) :
    IsVirtuallyPolycyclic J ∧
      ∃ Γ : Subgroup J, Γ.FiniteIndex ∧
        ∃ (S : SimplyConnectedSolvableLieModel) (Λ : Subgroup S.carrier),
          IsUniformLattice Λ ∧ Nonempty (Γ ≃* Λ) := by
  obtain ⟨dP, hPd, hPi, hPp, ⟨CP⟩⟩ := exists_finite_word_metric P
  let := dP
  let := hPd
  let := hPi
  let := hPp
  obtain ⟨dJ, hJd, hJi, hJp, ⟨CJ⟩⟩ := exists_finite_word_metric J
  let := dJ
  let := hJd
  let := hJi
  let := hJp
  let : MeasurableSpace J := borel _
  let : BorelSpace J := ⟨rfl⟩
  have hPfinite (r : ℝ) : (Metric.closedBall (1 : P) r).Finite :=
    (isCompact_closedBall (1 : P) r).finite_of_discrete
  have hJfinite (r : ℝ) : (Metric.closedBall (1 : J) r).Finite :=
    (isCompact_closedBall (1 : J) r).finite_of_discrete
  exact recognition_and_lattice_of_gromov gromov
    (e.metric CP CJ hPfinite hJfinite) hP CP hPfinite


end PolycyclicRecognition

end

end OAI
end

theorem solution : type_of% @OAI.PolycyclicRecognition.group_recognition_of_gromov_oai := @OAI.PolycyclicRecognition.group_recognition_of_gromov_oai
