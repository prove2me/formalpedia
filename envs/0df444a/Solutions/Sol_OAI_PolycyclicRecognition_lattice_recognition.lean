-- Prove2me | solution 1 for OAI.PolycyclicRecognition.lattice_recognition
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-02T23:59:32.277822+00:00
-- url     : https://prove2.me/submissions/4e4824c9-a51f-438c-b534-2a234775a277

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_PolycyclicRecognition
import Definitions.Def_OAIQ093D017
import Theorems.Thm_OAI_PolycyclicRecognition_group_recognition
import Theorems.Thm_OAI_PolycyclicRecognition_isPolycyclic_finitelyGenerated_discrete_of_linear_nilpotent_kernel

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
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_CoarseFiniteGeneration
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.controlledCochainMap_apply _root_.OAI.PolycyclicRecognition.controlledCochainPullback_apply _root_.OAI.PolycyclicRecognition.controlledPrismHom_succ _root_.OAI.PolycyclicRecognition.controlledPrismTerm_apply _root_.OAI.PolycyclicRecognition.controlledPrism_apply _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite generation is preserved by discrete-group coarse equivalence. -/

namespace PolycyclicRecognition

variable {G H : Type*} [Group G] [Group H]

/-- Coarse connectedness, expressed by finite generation, transfers through the
finite-difference control and finite error sets of a coarse equivalence. -/
theorem GroupCoarseEquivalence.finitelyGenerated (e : GroupCoarseEquivalence G H)
    [Group.FG G] : Group.FG H := by
  classical
  obtain ⟨S, hS, hSfinite⟩ := Group.fg_iff.mp (inferInstance : Group.FG G)
  obtain ⟨T, hT, hcontrol⟩ := e.bornologous_toFun S hSfinite
  let E := Set.range fun y => y⁻¹ * e.toFun (e.invFun y)
  let U := T ∪ E ∪ {e.toFun 1}
  have hU : U.Finite := (hT.union e.right_error).union (Set.finite_singleton _)
  let K := Subgroup.closure U
  have hTmem {t : H} (ht : t ∈ T) : t ∈ K :=
    Subgroup.subset_closure (Or.inl (Or.inl ht))
  have hsteps : ∀ a : G, ∀ x : G, (e.toFun x)⁻¹ * e.toFun (x * a) ∈ K := by
    intro a
    have ha : a ∈ Subgroup.closure S := hS ▸ Subgroup.mem_top a
    induction ha using Subgroup.closure_induction with
    | mem a ha =>
      intro x
      exact hTmem (hcontrol x (x * a) (by simpa using ha))
    | one =>
      intro x
      simp
    | mul a b _ _ ia ib =>
      intro x
      have hm := K.mul_mem (ia x) (ib (x * a))
      simpa only [mul_assoc, mul_inv_cancel_left] using hm
    | inv a _ ia =>
      intro x
      have hi := K.inv_mem (ia (x * a⁻¹))
      simpa only [mul_assoc, inv_mul_cancel_left, mul_inv_cancel_right,
        mul_inv_rev, inv_inv, inv_mul_cancel, mul_one] using hi
  apply Group.fg_iff.mpr
  refine ⟨U, top_unique ?_, hU⟩
  intro y _
  have hbase : e.toFun 1 ∈ K := Subgroup.subset_closure (Or.inr (Set.mem_singleton _))
  have himage : e.toFun (e.invFun y) ∈ K := by
    simpa using K.mul_mem hbase (hsteps (e.invFun y) 1)
  have herr : y⁻¹ * e.toFun (e.invFun y) ∈ K :=
    Subgroup.subset_closure (Or.inl (Or.inr ⟨y, rfl⟩))
  simpa only [mul_inv_rev, inv_inv, mul_inv_cancel_left] using
    K.mul_mem himage (K.inv_mem herr)

end PolycyclicRecognition

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

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Recognition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Unconditional quasi-isometric recognition of virtually polycyclic groups

The geometric height theorem, finiteness and duality endgame, and solvable
lattice realization combine with Gromov's polynomial-growth theorem to yield
virtual polycyclicity and a finite-index uniform-lattice model.
-/

noncomputable section
namespace PolycyclicRecognition

open Module LieAlgebra MeasureTheory
open scoped Manifold NNReal

/-- The full finite-covolume lattice corollary. Finite generation of the source
lattice follows from the given coarse equivalence. The existing discrete
subgroup theorem then supplies its polycyclicity, without a uniformity input. -/
theorem lattice_recognition_oai
    (S : SimplyConnectedSolvableLieModel) (Λ : Subgroup S.carrier)
    (hΛ : IsFiniteCovolumeLattice Λ)
    {J : Type} [Group J] [Group.FG J] (e : GroupCoarseEquivalence Λ J) :
    ∃ Γ : Subgroup J, Γ.FiniteIndex ∧
      ∃ (R : SimplyConnectedSolvableLieModel) (Δ : Subgroup R.carrier),
        IsUniformLattice Δ ∧ Nonempty (Γ ≃* Δ) := by
  obtain ⟨d⟩ := S.nonempty_properChainMetric geodesicMetricExistenceInput
  let := d.compatibleMetric
  let : Group.FG Λ := e.symm.finitelyGenerated
  let : DiscreteTopology Λ := hΛ.1
  have hpoly : IsPolycyclic Λ :=
    isPolycyclic_finitelyGenerated_discrete_solvableLieGroup
      (E := S.modelSpace) Λ
  exact (group_recognition e hpoly.isVirtuallyPolycyclic).2

end PolycyclicRecognition

end

end OAI
end

theorem solution : type_of% @OAI.PolycyclicRecognition.lattice_recognition_oai := @OAI.PolycyclicRecognition.lattice_recognition_oai
