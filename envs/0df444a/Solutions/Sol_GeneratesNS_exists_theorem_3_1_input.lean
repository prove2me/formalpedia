-- Prove2me | solution 1 for GeneratesNS.exists_theorem_3_1_input
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-02T22:08:25.379702+00:00
-- url     : https://prove2.me/submissions/3bcc5212-211c-459b-8147-d88aa4322dc5

import Mathlib
import Definitions.Def_OAIQ093D011
import Definitions.Def_OAIQ093D016
import Theorems.Thm_GeneratesNS_rho_g_case_finite
import Theorems.Thm_compact_lie_virtually_abelian

section
-- module Solutions.OAIQ093_PR.Complexification
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Complexification of a real inner product space

This file builds the complexification `Cx V` of a real inner product space `V`, realised
concretely as pairs `(x, y)` thought of as `x + i y`.  It provides the complex module and
complex inner product space structure, the dimension formula
`finrank ℂ (Cx V) = finrank ℝ V`, and the complexification of a continuous real-linear map,
packaged as an injective monoid homomorphism on units.

`Cx V` is primarily a **complex** vector space; its real structure is the restriction of scalars
of the complex one (via `NormedSpace.complexToReal`), so the real normed/analysis instances agree
with the complex ones rather than forming a diamond.

This is the device that lets the Gromov development keep its Lipschitz harmonic functions
real-valued while still feeding the (irreducibly complex) compact-Lie / unitary-trick step:
the real representation is complexified here, just before the unitary machinery is invoked.
-/


open scoped ComplexConjugate

namespace Cx

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-!
### Completeness

`Cx V` carries the `L²` norm of its two components, so it is isometric to `V × V` with the `L²`
norm and inherits completeness from `V`.  This is what makes `Cx V →L[ℂ] Cx V` a C⋆-algebra, and
hence what makes Mathlib's continuous functional calculus (`cfc`) available on complexified
operators: the `ContinuousFunctionalCalculus ℝ _ IsSelfAdjoint` instance is derived from the
complex one, so it is not available on `V →L[ℝ] V` itself.
-/

/-!
### Real structure

The real module / normed structure is the restriction of scalars of the complex one, supplied by
`NormedSpace.complexToReal`.  The real scalar action is `r • p = (r : ℂ) • p`, componentwise.
-/

/-! ### Complexification of a real-linear map -/

lemma norm_mapCLM_le (f : V →L[ℝ] V) : ‖mapCLM f‖ ≤ ‖f‖ :=
  LinearMap.mkContinuous_norm_le _ (norm_nonneg f) _

lemma mapCLM_continuous : Continuous (mapCLM : (V →L[ℝ] V) → (Cx V →L[ℂ] Cx V)) := by
  have h : LipschitzWith 1 (mapCLM : (V →L[ℝ] V) → (Cx V →L[ℂ] Cx V)) := by
    refine LipschitzWith.of_dist_le_mul fun f g => ?_
    rw [dist_eq_norm, dist_eq_norm, mapCLM_sub]
    simpa using norm_mapCLM_le (f - g)
  exact h.continuous

lemma mapCLM_injective : Function.Injective (mapCLM : (V →L[ℝ] V) → Cx V →L[ℂ] Cx V) := by
  intro f g h
  ext x
  have hx := congrArg (fun T : Cx V →L[ℂ] Cx V => (T ((x, 0) : Cx V)).fst) h
  exact hx

lemma unitsMapHom_injective :
    Function.Injective (unitsMapHom : (V →L[ℝ] V)ˣ → (Cx V →L[ℂ] Cx V)ˣ) :=
  Units.map_injective mapCLM_injective

lemma unitsMapHom_continuous :
    Continuous (unitsMapHom : (V →L[ℝ] V)ˣ → (Cx V →L[ℂ] Cx V)ˣ) := by
  apply Units.continuous_iff.mpr
  exact ⟨mapCLM_continuous.comp Units.continuous_val,
         mapCLM_continuous.comp Units.continuous_coe_inv⟩

/-!
### Self-adjointness

The complexification of a self-adjoint operator is self-adjoint.  Together with the
`CompleteSpace (Cx V)` instance above, this is what lets `cfc f (mapCLM Δ) (p := IsSelfAdjoint)`
elaborate *and* lets the `cfc` API lemmas discharge their `IsSelfAdjoint` side conditions.
-/

/-!
### Spectrum

Complexification preserves the spectrum *at real points*: `mapCLM f` is invertible exactly when
`f` is, because `mapCLM f` acts componentwise and so is bijective exactly when `f` is.

Note this is **not** the same as saying `spectrum ℂ (mapCLM f) = ((↑) '' spectrum ℝ f)`, which is
false in general: rotation by a quarter turn on `ℝ²` has empty real spectrum but complex spectrum
`{I, -I}`.  Only the real points of `spectrum ℂ (mapCLM f)` correspond to `spectrum ℝ f`; see
`ofReal_mem_spectrum_mapCLM_iff`.  For a self-adjoint `f` the complex spectrum is real anyway, so
in that case nothing is lost.
-/


end Cx
end

section
-- module Solutions.OAIQ093_PR.Defs
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# The discrete Laplacian and the `G`-action

The Laplacian `Laplace_b` / `Laplace`, the constant functions `ConstF`, the quotient `W`, the
`G`-action `gAct`, and the closed-ball counting lemmas.

Root of the `Gromov.Defs` hierarchy: importing it pulls in the word metric, the measure
structure, `LipschitzH` and the convolution API.
-/


set_option linter.style.longLine false
set_option linter.style.cdot false
set_option linter.style.commandStart false
set_option linter.style.whitespace false

open Subgroup
open scoped Finset
open scoped Pointwise
open scoped commutatorElement

lemma group_fg_map {G G': Type*} [Group G] [Group G'] (H: Subgroup G) (h_fg: H.FG) (f: G →* G'): (Subgroup.map f H).FG := by
  obtain ⟨s, hs⟩ := h_fg
  classical
  rw [Subgroup.fg_iff]
  use s.image f
  refine ⟨?_, ?_⟩
  .
    rw [Finset.coe_image]
    rw [← MonoidHom.map_closure]
    rw [hs]
  . simp
    exact Set.toFinite (⇑f '' ↑s)
end

section
-- module Solutions.OAIQ093_PR.Unitary_WeylTrick
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instNonemptyBases _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

/-!
# The unitarian trick

`new_weyl_unitarian_trick`: a bounded subgroup of `GL` is conjugate into the unitary group.
-/


open scoped Matrix.Norms.L2Operator ComplexInnerProductSpace

set_option linter.style.longLine false
set_option linter.style.commandStart false

open Subgroup Pointwise Finset
open scoped Pointwise Finset
open scoped commutatorElement IsMulCommutative


attribute [local implicit_reducible] FreshInnerProduct

set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 500000 in
lemma new_weyl_unitarian_trick {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]  (H : Subgroup (V →L[ℂ] V)ˣ)   [LocallyCompactSpace H] [CompactSpace H]: ∃ S : Subgroup ↥(Matrix.unitaryGroup (Fin (Module.finrank ℂ V)) ℂ), Nonempty (S ≃* H) := by
  let integrand := fun (v w : FreshInnerProduct V) (h : H) => ⟪(h.val.val v), (h.val.val w)⟫
  have continuous_integrand : ∀ v w : FreshInnerProduct V, Continuous fun h : H => integrand v w h := by
    intro v w
    simp only [integrand]
    fun_prop

  borelize (V →L[ℂ] V)ˣ

  --

  have finite_dimensional_fresh : FiniteDimensional ℂ (FreshInnerProduct V) := inferInstanceAs (FiniteDimensional ℂ V)

  have integrable_on : ∀ v w : V, MeasureTheory.Integrable (integrand v w) (MeasureTheory.Measure.haar.inv (G := H)) := by
    intro v w
    rw [← MeasureTheory.integrableOn_univ]
    apply ContinuousOn.integrableOn_compact
    · exact CompactSpace.isCompact_univ
    · apply (continuous_integrand v w).continuousOn


  let inner_product_core : InnerProductSpace.Core ℂ (FreshInnerProduct V) := {
    inner := fun v w => MeasureTheory.integral (MeasureTheory.Measure.haar.inv) (integrand v w)
    conj_inner_symm := by
      intro x y
      simp only [integrand]
      simp_rw [show ∀ h : ↥H, (⟪(h.val.val x : V), (h.val.val y : V)⟫ : ℂ)
          = (starRingEnd ℂ) ⟪(h.val.val y : V), (h.val.val x : V)⟫
        from fun h => (inner_conj_symm _ _).symm]
      exact integral_conj.symm
    re_inner_nonneg := by
      intro x
      simp [integrand]
      conv =>
        rhs
        arg 1
        arg 2
        intro h
        equals ⟪h.val.val x, h.val.val x⟫ =>
          simp
      conv =>
        rhs
        arg 1
        arg 2
        intro h
        rw [← inner_self_ofReal_re]
      simp
      rw [integral_complex_ofReal]
      apply MeasureTheory.integral_nonneg
      rw [Pi.le_def]
      intro y
      simp
      rw [← RCLike.re_to_complex]
      simp
      rw [Complex.re_nonneg_iff_nonneg]
      .
        norm_cast
        positivity
      . rw [isSelfAdjoint_iff]
        simp
    add_left := by
      intro a b c
      have hpt : (integrand (a + b) c) = (fun h => integrand a c h + integrand b c h) := by
        funext h
        simp only [integrand]
        rw [show (h.val.val (a + b) : V) = h.val.val a + h.val.val b from map_add _ _ _,
          inner_add_left]
      rw [hpt]
      exact MeasureTheory.integral_add (integrable_on a c) (integrable_on b c)
    smul_left := by
      intro x y z
      have hpt : (integrand (z • x) y) = (fun h => (starRingEnd ℂ) z * integrand x y h) := by
        funext h
        simp only [integrand]
        rw [show (h.val.val (z • x) : V) = z • h.val.val x from map_smul _ _ _, inner_smul_left]
      rw [hpt]
      exact MeasureTheory.integral_const_mul _ _
    definite := by
      intro x hx
      simp only [integrand] at hx
      conv at hx =>
        lhs
        arg 2
        intro h
        rw [← inner_self_ofReal_re]

      simp at hx
      rw [integral_complex_ofReal] at hx
      norm_cast at hx
      rw [MeasureTheory.integral_eq_zero_iff_of_nonneg ?_] at hx
      · dsimp only [Filter.EventuallyEq] at hx
        conv at hx =>
          pattern MeasureTheory.Measure.haar.inv
          rw [← MeasureTheory.Measure.restrict_univ (μ := MeasureTheory.Measure.haar.inv)]


        obtain ⟨q, _, inner_q_zero⟩ := MeasureTheory.Measure.exists_mem_of_measure_ne_zero_of_ae ?_ hx
        conv at inner_q_zero =>
          equals ⟪(q.val.val x), (q.val.val x)⟫ = 0 =>
            rw [← inner_self_ofReal_re]
            simp
            norm_cast
            simp


        simp at inner_q_zero
        have map_iff_zero := LinearMap.map_eq_zero_iff (f := q.val.val.toLinearMap) (x := x) ?_
        · exact map_iff_zero.mp inner_q_zero
        · -- TODO - find a better way of doing this
          let my_map := (ContinuousLinearMap.toLinearMapRingHom (R₁ := ℂ) (M₁ := V)).toMonoidHom
          let f_map := (Units.map my_map) q.val
          let f_as_equiv := fun f => (LinearMap.GeneralLinearGroup.toLinearEquiv (R := ℂ) (M := V) f)
          simp [LinearMap.GeneralLinearGroup] at f_as_equiv
          have injective_f := (f_as_equiv f_map).injective
          simp [f_as_equiv, f_map] at injective_f
          exact injective_f
      · have foo := integrable_on x x
        simp [integrand] at foo
        norm_cast
        norm_cast at foo
        apply MeasureTheory.Integrable.re at foo
        norm_cast at foo
      · rw [Pi.le_def]
        intro y
        simpa using inner_self_nonneg (𝕜 := ℂ) (x := (y.val.val x))
  }
  · exact Ne.symm (NeZero.ne' (MeasureTheory.Measure.haar.inv Set.univ))

  let new_inner := InnerProductSpace.ofCore inner_product_core.toCore
  let normed_add := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ) (F := (FreshInnerProduct V))


  have proper_fresh : ProperSpace (FreshInnerProduct V) := by
    apply FiniteDimensional.proper_rclike ℂ _


  let apply_rep (h : H) (v : FreshInnerProduct V): FreshInnerProduct V := h.val.val v

  have v_preserves_inner : ∀ h : H, ∀ v w : FreshInnerProduct V, ⟪(apply_rep h v), (apply_rep h w)⟫ = ⟪v, w⟫ := by
    intro h v w
    show MeasureTheory.integral (MeasureTheory.Measure.haar.inv (G := H)) (integrand (apply_rep h v) (apply_rep h w))
       = MeasureTheory.integral (MeasureTheory.Measure.haar.inv (G := H)) (integrand v w)
    have hpt : integrand (apply_rep h v) (apply_rep h w) = (fun g : H => integrand v w (g * h)) := by
      funext g
      simp only [integrand, apply_rep, Subgroup.coe_mul, Units.val_mul]
      rfl
    rw [hpt]
    exact MeasureTheory.integral_mul_right_eq_self (integrand v w) h
  · -- finDimVectorspaceEquiv
    have rank_eq := Module.finrank_eq_rank' ℂ (FreshInnerProduct V)
    have V_equiv := (finDimVectorspaceEquiv (Module.finrank ℂ (FreshInnerProduct V)) rank_eq.symm).toContinuousLinearEquiv
    let V_equiv_fresh : V ≃L[ℂ] (FreshInnerProduct V) := ContinuousLinearEquiv.ofFinrankEq ?_
    let V_fresh_arrow := ContinuousLinearEquiv.arrowCongr V_equiv_fresh V_equiv_fresh

    let new_H_matrix := ContinuousLinearMap.toLinearMap '' (Units.val '' H.carrier)
    -- Deliberate defeq abuse, so that things line up with our integral (which is over plain V)
    let new_H_coe : Set ((FreshInnerProduct V) →ₗ[ℂ] (FreshInnerProduct V)) := new_H_matrix



    have V_basis := stdOrthonormalBasis ℂ (FreshInnerProduct V)

    let H_matrix := (LinearMap.toMatrix V_basis.toBasis V_basis.toBasis) '' new_H_coe


    have H_mem_unitary : ∀ h ∈ H_matrix, h ∈ Matrix.unitaryGroup (Fin (Module.finrank ℂ (FreshInnerProduct V))) ℂ := by
      intro h h_mem
      simp [H_matrix, new_H_coe, new_H_matrix] at h_mem
      obtain ⟨u, u_mem, hu⟩ := h_mem
      let a : FreshInnerProduct V →ₗ[ℂ] FreshInnerProduct V := (↑↑u : V →ₗ[ℂ] V)
      have ha : (LinearMap.toMatrix V_basis.toBasis V_basis.toBasis) a = h := hu
      rw [← ha, Matrix.mem_unitaryGroup_iff']
      -- `a` is the linear map underlying an element of `H`, so it preserves the new inner product.
      have preserves_inner : ∀ (x y : FreshInnerProduct V), ⟪a x, a y⟫ = ⟪x, y⟫ := by
        intro x y
        exact v_preserves_inner ⟨u, u_mem⟩ x y
      -- Preservation of the inner product means `adjoint a ∘ a = id`.
      have adj : a.adjoint ∘ₗ a = LinearMap.id := by
        apply LinearMap.ext
        intro x
        rw [LinearMap.comp_apply, LinearMap.id_apply]
        apply ext_inner_right ℂ
        intro y
        rw [LinearMap.adjoint_inner_left]
        exact preserves_inner x y
      have hmat : star (LinearMap.toMatrix V_basis.toBasis V_basis.toBasis a) *
          (LinearMap.toMatrix V_basis.toBasis V_basis.toBasis a) = 1 := by
        rw [Matrix.star_eq_conjTranspose, ← LinearMap.toMatrix_adjoint, ← LinearMap.toMatrix_comp,
          adj, LinearMap.toMatrix_id]
      exact hmat


    let H_matrix_subgroup : Subgroup (Matrix.unitaryGroup (Fin (Module.finrank ℂ V)) ℂ) := {
      carrier := Set.range (fun (h : H_matrix) => ⟨h.val, H_mem_unitary h (by simp)⟩),
      mul_mem' := by
        intro X Y hx hy
        simp
        use (X * Y).val
        simp
        simp at hx
        simp at hy
        simp [H_matrix]
        simp [H_matrix] at hx
        simp [H_matrix] at hy
        obtain ⟨a, ⟨p, p_mem, p_eq_a⟩, a_eq_x⟩ := hx
        obtain ⟨b, ⟨q, q_mem, q_eq_b⟩, b_eq_y⟩ := hy
        simp [new_H_coe, new_H_matrix] at q_mem
        simp [new_H_coe, new_H_matrix] at p_mem
        obtain ⟨y, y_mem, y_eq_q⟩ := q_mem
        obtain ⟨x, x_mem, x_eq_p⟩ := p_mem
        simp [new_H_coe, new_H_matrix]
        refine ⟨?_, rfl⟩
        have hX : X.val = a := by rw [← a_eq_x]
        have hY : Y.val = b := by rw [← b_eq_y]
        refine ⟨x * y, H.mul_mem x_mem y_mem, ?_⟩
        rw [hX, hY, ← p_eq_a, ← q_eq_b, ← LinearMap.toMatrix_mul, ← x_eq_p, ← y_eq_q]
        rfl
      one_mem' := by
        simp [H_matrix, new_H_coe, new_H_matrix]
        refine ⟨1, H.one_mem, ?_⟩
        exact LinearMap.toMatrix_one _
      inv_mem' := by
        simp
        intro a ha b hb a_eq_b
        refine ⟨a⁻¹, ?_, ?_⟩
        · simp [H_matrix, new_H_coe, new_H_matrix] at ⊢ hb
          obtain ⟨u, u_mem, hz₀⟩ := hb
          refine ⟨u⁻¹, H.inv_mem u_mem, ?_⟩
          rw [← a_eq_b, ← hz₀]
          refine (Matrix.inv_eq_left_inv ?_).symm
          rw [← LinearMap.toMatrix_mul]
          convert LinearMap.toMatrix_one (R := ℂ) V_basis.toBasis using 2
          all_goals try with_reducible_and_instances rfl
          ext v
          change (↑(u⁻¹) : V →L[ℂ] V) ((↑u : V →L[ℂ] V) v) = v
          rw [← mul_apply_eq_comp, ← Units.val_mul, inv_mul_cancel, Units.val_one,
            one_apply_eq_self]
        · rw [Matrix.mem_unitaryGroup_iff] at ha
          apply Matrix.inv_eq_right_inv at ha
          rw [Subtype.ext_iff]
          show a⁻¹ = star a
          exact ha
    }

    let remove_fresh (h : FreshInnerProduct V →ₗ[ℂ] FreshInnerProduct V): (V →ₗ[ℂ] V) := h

    · use H_matrix_subgroup
      apply Nonempty.intro
      exact {
        toFun := fun h => ⟨{
          val := ((remove_fresh (h.val.val.toLin V_basis.toBasis V_basis.toBasis)).toContinuousLinearMap),
          inv := ((remove_fresh (h.val.val⁻¹.toLin V_basis.toBasis V_basis.toBasis)).toContinuousLinearMap),
          val_inv := by
            simp [remove_fresh]
            ext a
            simp
            conv =>
              lhs
              equals Matrix.toLin V_basis.toBasis V_basis.toBasis (h.val.val * h.val.val⁻¹) a =>
                rw [eq_comm]
                exact Matrix.toLin_mul_apply (v₁ := V_basis.toBasis) (v₂ := V_basis.toBasis) (v₃ := V_basis.toBasis) _ _ _
            rw [Matrix.mul_nonsing_inv]
            · exact LinearMap.congr_fun (Matrix.toLin_one (v₁ := V_basis.toBasis)) a
            · apply Matrix.UnitaryGroup.det_isUnit
          inv_val := by
            simp [remove_fresh]
            ext a
            simp
            conv =>
              lhs
              equals Matrix.toLin V_basis.toBasis V_basis.toBasis (h.val.val⁻¹ * h.val.val) a =>
                rw [eq_comm]
                exact Matrix.toLin_mul_apply (v₁ := V_basis.toBasis) (v₂ := V_basis.toBasis) (v₃ := V_basis.toBasis) _ _ _
            rw [Matrix.nonsing_inv_mul]
            · exact LinearMap.congr_fun (Matrix.toLin_one (v₁ := V_basis.toBasis)) a
            · apply Matrix.UnitaryGroup.det_isUnit
        }, by (
          simp [remove_fresh]
          have h_prop := h.property
          simp only [H_matrix_subgroup] at h_prop
          rw [← Subgroup.mem_carrier] at h_prop
          simp only [] at h_prop
          rw [Set.mem_range] at h_prop
          obtain ⟨a, ha⟩ := h_prop
          have a_prop := a.property
          simp only [H_matrix, new_H_coe, new_H_matrix] at a_prop
          rw [Set.mem_image] at a_prop
          obtain ⟨b, b_mem, b_eq_a⟩ := a_prop
          obtain ⟨c, ⟨d, d_mem, d_eq_c⟩, c_eq_b⟩ := b_mem
          simp_rw [← ha, ← b_eq_a]
          simp
          simp_rw [← c_eq_b, ← d_eq_c]
          conv =>
            arg 2
            arg 1
            equals d.val =>
              rfl

          simp
          rw [Subgroup.mem_carrier] at d_mem
          exact d_mem
        )⟩
        invFun := fun h => ⟨⟨(LinearMap.toMatrix V_basis.toBasis V_basis.toBasis) h.val.val.toLinearMap, by (
          apply H_mem_unitary
          exact ⟨h.val.val.toLinearMap, ⟨h.val.val, ⟨h.val, h.property, rfl⟩, rfl⟩, rfl⟩
        )⟩, by (
          refine ⟨⟨_, ⟨h.val.val.toLinearMap, ⟨h.val.val, ⟨h.val, h.property, rfl⟩, rfl⟩, rfl⟩⟩, rfl⟩
        )⟩,
        left_inv := by
          intro h
          simp
          rw [Subtype.ext_iff]
          simp [remove_fresh]
        right_inv := by
          intro h
          simp
          simp [remove_fresh]
          ext a
          simp
        map_mul' := by
          intro x y
          simp [remove_fresh]
          ext a
          simp
          exact Matrix.toLin_mul_apply (v₁ := V_basis.toBasis) (v₂ := V_basis.toBasis)
            (v₃ := V_basis.toBasis) _ _ _
      }
    · rfl
end

section
-- module Solutions.OAIQ093_PR.Representation
attribute [-instance] _root_.GeneratesNS.rho_g_FG _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# The representation of `G` on `W`

The space `W = LipschitzH ⧸ ConstF`, the representation `GRep` / `GRepW` of `G` on it, and the
fact that it preserves the quotient norm.
-/


set_option linter.style.longLine false
set_option linter.style.cdot false
-- TODO - vscode stops reporting underlines if there are too many total underlines / gutter messages
-- I've disabled some failing lints for now so that error underlines still sho up
set_option linter.style.commandStart false

open Subgroup
open scoped Finset
open scoped Pointwise
open scoped commutatorElement

namespace GeneratesNS
open Generates

variable [hGS: Generates]
include hGS

open scoped RealInnerProductSpace

-- `LipschitzH_seminorm` and `LipschitzH_normed` are public instances in
-- `Gromov.LipschitzNorm`, so they are already available here.

-- The lift of LipschitzSemiNorm to W, using a proof that LipschitzSemiNorm doesn't depend on the choice representative
-- (adding a constant to a Lipschitz function doesn't change its Lipschitz constant)


set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 9000000


-- GRep just translates functions by g⁻¹, so it preserves the Lipschitz operator norm
lemma GRep_preserves_norm (g: G) (f: LipschitzH): ‖(GRep g) f‖ = ‖f‖ := by
  simp [GRep]
  simp [norm]
  nth_rw 1 [LipschitzSemiNorm]
  rw [gAct]
  simp [DFunLike.coe]
  conv =>
    lhs
    arg 1
    arg 1
    intro k
    equals (LipschitzWith k (f.toFun ∘ (fun y => (y * g)))) =>
      rfl

  have comp := LipschitzWith.comp (f := f.toFun) (g := fun y => (y * g)) (Kf := (LipschitzSemiNorm ⇑f)) (Kg := 1) ?_ ?_
  rotate_left 1
  . apply lipschitz_attains_norm
    exact f.lipschitz
  .
    simp [LipschitzWith]

  have norm_mem: (LipschitzSemiNorm f) ∈ { k: NNReal | LipschitzWith k (f.toFun ∘ (fun y => (y * g))) } := by
    simp
    simp at comp
    exact comp


  apply le_antisymm
  .
    apply csInf_le (by
      simp [BddBelow]
      apply Set.nonempty_of_mem (x := 0)
      rw [mem_lowerBounds]
      simp
    ) norm_mem
  .
    apply le_csInf
    .
      apply Set.nonempty_of_mem (x := (LipschitzSemiNorm ⇑f)) norm_mem
    . intro b hb
      simp at hb
      simp [LipschitzSemiNorm]
      apply csInf_le
      .
        simp [BddBelow]
        apply Set.nonempty_of_mem (x := 0)
        rw [mem_lowerBounds]
        simp
      . simp
        simp [LipschitzWith] at hb
        simp [LipschitzWith]
        intro x y
        specialize hb (x * g⁻¹) (y * g⁻¹)
        simp at hb
        grw [hb]


lemma quotient_norm_eq_norm (f: LipschitzH): ‖(Submodule.Quotient.mk f : W)‖ = ‖f‖ := by
  conv =>
    lhs
    equals ‖(QuotientAddGroup.mk f : (LipschitzH ⧸ ConstF.toAddSubgroup))‖ =>
      rfl
  rw [QuotientAddGroup.norm_mk]
  simp [Metric.infDist]
  have hzero : (0 : LipschitzH) ∈ (↑ConstF : Set LipschitzH) :=
    SetLike.mem_coe.mpr (Submodule.zero_mem ConstF)
  have hconst : ∀ y ∈ (↑ConstF : Set LipschitzH), edist f y = (‖f‖₊ : ENNReal) := by
    intro y hy
    simp [ConstF] at hy
    obtain ⟨a, ha⟩ := hy
    simp [edist, PseudoMetricSpace.edist]
    simp [LipschitzSemiNorm]
    simp [LipschitzWith]
    simp_rw [← ha]
    simp [ConstLipschitzH]
    rfl
  have hinf : Metric.infEDist f (↑ConstF : Set LipschitzH) = (‖f‖₊ : ENNReal) := by
    apply le_antisymm
    · calc Metric.infEDist f (↑ConstF : Set LipschitzH) ≤ edist f 0 :=
            Metric.infEDist_le_edist_of_mem hzero
        _ = (‖f‖₊ : ENNReal) := hconst 0 hzero
    · rw [Metric.le_infEDist]
      exact fun y hy => (hconst y hy).ge
  rw [hinf]
  simp


lemma GLW_preseves_norm (g: G) (w: W): ‖(GRepW (GRepW_base g)).val w‖ = ‖w‖ := by
  have exists_v: ∃ v, Submodule.Quotient.mk v = w := by
    apply Quotient.exists_rep
  obtain ⟨v, hv⟩ := exists_v
  simp [GRepW, GRepW_base, GRepW_non_invertible]
  nth_rw 1 [← hv]
  rw [Representation.asGroupHom_apply]
  simp only [Representation.quotient_apply, Submodule.mapQ_apply]
  rw [quotient_norm_eq_norm]
  rw [GRep_preserves_norm]
  rw [← hv]
  rw [quotient_norm_eq_norm]


lemma GRepW_norm_le (g: G): ‖(GRepW (GRepW_base g)).val‖ ≤ 1 := by
  rw [ContinuousLinearMap.opNorm_le_iff]
  . simp [GLW_preseves_norm]
  . simp


set_option synthInstance.maxHeartbeats 500000


end GeneratesNS
end

section
-- module Solutions.OAIQ093_PR.Theorem38
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

/-!
# Theorem 3.8

`theorem_3_8` and its real form: a group of polynomial growth admits a nontrivial
finite-dimensional representation.
-/


set_option linter.style.longLine false
set_option linter.style.cdot false
set_option linter.style.commandStart false

open Subgroup
open scoped Finset
open scoped Pointwise
open scoped commutatorElement

namespace GeneratesNS
open Generates

variable [hGS: Generates]
include hGS

open scoped RealInnerProductSpace

set_option synthInstance.maxHeartbeats 500000

set_option maxHeartbeats 9000000

omit hGS in
set_option maxHeartbeats 500000 in
lemma theorem_3_8 {V: Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] (H: Subgroup (V →L[ℂ] V)ˣ) [DecidableEq H] (h_compact: CompactSpace H) (G: Subgroup H) (G_fg: G.FG) (S_data: SPolyData G): ∃ A: Subgroup G, IsMulCommutative A ∧ A.FiniteIndex := by
  obtain ⟨H', ⟨H_equiv_H'⟩⟩ := new_weyl_unitarian_trick (V := V) (H := H)
  let G' := Subgroup.map H'.subtype (Subgroup.map H_equiv_H'.symm.toMonoidHom G)
  let my_hom := MonoidHom.ofInjective (f := H'.subtype) (by exact subtype_injective H')
  let other := Subgroup.map my_hom.toMonoidHom (Subgroup.map H_equiv_H'.symm.toMonoidHom G)

  let reverse := Subgroup.comap H'.subtype


  let G'_to_G: G' →* G := {
    toFun := fun g => (by
      use ⟨H_equiv_H' (my_hom.symm ⟨g, by (
        have g_prop := g.property
        simp only [G'] at g_prop
        rw [Subgroup.mem_map] at g_prop
        obtain ⟨x, x_mem, g_eq⟩ := g_prop
        rw [← g_eq]
        simp
      )⟩), by (
        simp [my_hom]
      )⟩
      simp [my_hom]
      have g_prop := g.property
      simp only [G'] at g_prop
      rw [Subgroup.mem_map] at g_prop
      obtain ⟨x, x_mem, g_eq⟩ := g_prop
      simp_rw [← g_eq]
      rw [Subgroup.mem_map] at x_mem
      obtain ⟨y, y_mem, x_eq⟩ := x_mem
      simp_rw [← x_eq]
      have key : (MonoidHom.ofInjective (subtype_injective H')).symm
          ⟨H'.subtype (H_equiv_H'.symm.toMonoidHom y), ⟨_, rfl⟩⟩
            = H_equiv_H'.symm.toMonoidHom y :=
        subtype_injective H' (MonoidHom.apply_ofInjective_symm _ _)
      rw [key]
      simpa using y_mem
    )
    map_one' := by simp
    map_mul' := by
      intro a b
      conv =>
        enter [1, 1, 1, 1, 2, 2]
        equals ⟨a.val, (by
          have a_prop := a.property
          simp only [G'] at a_prop
          rw [Subgroup.mem_map] at a_prop
          obtain ⟨x, x_mem, a_eq⟩ := a_prop
          rw [← a_eq]
          simp
        )⟩ * ⟨b.val, (by
          have b_prop := b.property
          simp only [G'] at b_prop
          rw [Subgroup.mem_map] at b_prop
          obtain ⟨y, y_mem, b_eq⟩ := b_prop
          rw [← b_eq]
          simp
        )⟩ =>
          rfl

      simp_rw [MulEquiv.map_mul]
      rfl
  }

  have G'_fg: G'.FG := by
    simp [G']
    apply group_fg_map
    apply group_fg_map
    exact G_fg

  by_cases dim_le_one: Module.finrank ℂ (V) ≤ 1
  .
    use ⊤
    refine ⟨?_, ?_⟩
    .

      have map_dim := Module.finrank_linearMap ℂ ℂ V V
      -- TODO - is there an easier way to prove this?
      have map_dim_le_one: Module.finrank ℂ (V →ₗ[ℂ] V) ≤ 1 := by
        rw [map_dim]
        by_cases dim_eq_zero: Module.finrank ℂ (V) = 0
        . simp [dim_eq_zero]
        . have dim_eq_one: Module.finrank ℂ (V) = 1 := by omega
          simp [dim_eq_one]

      rw [finrank_le_one_iff] at map_dim_le_one
      obtain ⟨v, v_span⟩ := map_dim_le_one
      refine { is_comm := ?_ }
      refine { comm := ?_ }
      intro x y
      ext a
      simp
      obtain ⟨p, hx⟩ := v_span x.val.val.val
      obtain ⟨q, hy⟩ := v_span y.val.val.val

      -- TODO - upstream to mathlib
      have clm_apply (f: V →L[ℂ] V) (v: V): f v = f.toLinearMap v := rfl
      rw [clm_apply]
      rw [clm_apply]
      rw [clm_apply]
      rw [clm_apply]

      rw [← hx, ← hy]
      simp
      rw [smul_comm]
    . infer_instance
  .

    let new_S_data := map_S_data G (f := H'.subtype.comp (H_equiv_H'.symm.toMonoidHom)) S_data
    obtain ⟨N, N_comm, N_finite_index⟩ := compact_lie_virtually_abelian (Module.finrank ℂ V) (by omega) G' G'_fg (by
      unfold G'
      rw [Subgroup.map_map]
      exact new_S_data
    )

    let new_N := N
    simp [G'] at new_N


    let new_N' := Subgroup.map G'.subtype N

    let new_N' := Subgroup.map G'_to_G N
    use new_N'
    refine ⟨?_, ?_⟩
    .
      simp [new_N']
      apply Subgroup.map_isMulCommutative
    .
      simp [new_N']
      rw [Subgroup.finiteIndex_iff]
      rw [Subgroup.index_map_of_injective]
      . simp
        refine ⟨?_, ?_⟩
        . exact N_finite_index.index_ne_zero
        . conv =>
            arg 1
            arg 1
            arg 1
            equals ⊤ =>
              rw [MonoidHom.range_eq_top]
              simp [G'_to_G]
              intro a
              simp
              use H'.subtype (H_equiv_H'.symm a)
              simp [my_hom]
              use ?_
              . have key : (MonoidHom.ofInjective (subtype_injective H')).symm
                    ⟨↑(H_equiv_H'.symm (↑a : ↥H)), ⟨H_equiv_H'.symm (↑a : ↥H), rfl⟩⟩
                      = H_equiv_H'.symm (↑a : ↥H) :=
                  subtype_injective H' (MonoidHom.apply_ofInjective_symm _ _)
                exact Subtype.ext ((congrArg H_equiv_H' key).trans
                  (H_equiv_H'.apply_symm_apply _))
              . simp [G']
                use a.val
                use ?_
                . simp
                . simp

          simp
      .
        simp [G'_to_G]
        intro a b hab
        simpa using hab


/-- The real-inner-product-space version of `theorem_3_8`: a finitely generated, polynomial-growth
subgroup of the units of a compact linear group over `ℝ` is virtually abelian.  We reduce to the
complex `theorem_3_8` by complexifying (`Cx.unitsMapHom`) just before the unitary machinery. -/
lemma theorem_3_8_real {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] (H : Subgroup (V →L[ℝ] V)ˣ) [DecidableEq H]
    (h_compact : CompactSpace H) (G : Subgroup H) (G_fg : G.FG) (S_data : SPolyData G) :
    ∃ A : Subgroup G, IsMulCommutative A ∧ A.FiniteIndex := by
  classical
  have φ_inj : Function.Injective (Cx.unitsMapHom (V := V)) := Cx.unitsMapHom_injective
  have φ_cont : Continuous (Cx.unitsMapHom (V := V)) := Cx.unitsMapHom_continuous
  let Hc : Subgroup ((Cx V →L[ℂ] Cx V)ˣ) := Subgroup.map Cx.unitsMapHom H
  let e : H ≃* Hc := Subgroup.equivMapOfInjective H Cx.unitsMapHom φ_inj
  let Gc : Subgroup Hc := Subgroup.map e.toMonoidHom G
  let eG : G ≃* Gc := MulEquiv.subgroupMap e G
  have Gc_fg : Gc.FG := group_fg_map G G_fg e.toMonoidHom
  have Sc : SPolyData Gc := map_equiv_S_data eG S_data
  have hc : CompactSpace Hc := by
    have hH : IsCompact ((H : Set (V →L[ℝ] V)ˣ)) := by
      have h1 := (isCompact_univ (X := ↥H)).image continuous_subtype_val
      rwa [Set.image_univ, Subtype.range_coe] at h1
    have h2 : IsCompact ((Hc : Set (Cx V →L[ℂ] Cx V)ˣ)) := by
      have := hH.image φ_cont
      rwa [← Subgroup.coe_map] at this
    exact isCompact_iff_compactSpace.mp h2
  obtain ⟨A, A_comm, A_fi⟩ := theorem_3_8 (V := Cx V) Hc hc Gc Gc_fg Sc
  refine ⟨Subgroup.map eG.symm.toMonoidHom A, ?_, ?_⟩
  · exact Subgroup.map_isMulCommutative A eG.symm.toMonoidHom
  · rw [Subgroup.finiteIndex_iff, Subgroup.index_map_of_injective A eG.symm.injective,
      eG.symm.toMonoidHom.range_eq_top.mpr eG.symm.surjective, Subgroup.index_top, mul_one]
    exact A_fi.index_ne_zero

end GeneratesNS
end

section
-- module Solutions.OAIQ093_PR.RhoAbelian
attribute [-instance] _root_.OAI.PolycyclicRecognition.CartanWordModel.instNonemptyBases _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

/-!
# `rho_g` contains a finite-index abelian subgroup

`rho_g_contains_abelian`, the bundled input `Theorem3_1_Input`, and the infinite-image case.
-/


set_option linter.style.longLine false
set_option linter.style.cdot false
set_option linter.style.commandStart false

open Subgroup
open scoped Finset
open scoped Pointwise
open scoped commutatorElement

namespace GeneratesNS
open Generates

variable [hGS: Generates]
include hGS

open scoped RealInnerProductSpace

set_option synthInstance.maxHeartbeats 500000

set_option maxHeartbeats 9000000

open scoped RealInnerProductSpace in
attribute [-simp] Subgroup.map_toSubmonoid in
set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 600000 in
--set_option trace.Meta.synthInstance true in
lemma rho_g_contains_abelian {d: ℕ} (hd: HasPolynomialGrowthD S d) : ∃ M: Subgroup ((rho_g)), IsMulCommutative M ∧ M.FiniteIndex := by
  classical
  let my_map := Subgroup.subtype (rho_g)
  have W_equiv: (W) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin <| Module.finrank ℝ W) := LinearEquiv.ofFinrankEq _ _ finrank_euclideanSpace_fin.symm


  unfold GL_W at my_map
  -- TODO - is there a simpler way to get an arbitrary inner product space?
  let inner_prod_core: InnerProductSpace.Core ℝ (FreshTopology (W)) := {
    inner := fun v w => ⟪W_equiv v, W_equiv w⟫,
    conj_inner_symm := by intro x y; simp [real_inner_comm],
    re_inner_nonneg := by
      exact fun x ↦ inner_self_nonneg
    add_left := by
      intro x y z
      have key : ∀ a b : FreshTopology (W), W_equiv (a + b) = W_equiv a + W_equiv b :=
        fun a b => map_add W_equiv a b
      rw [key, inner_add_left]
    smul_left := by
      intro x y r
      have key : ∀ (c : ℝ) (a : FreshTopology (W)), W_equiv (c • a) = c • W_equiv a :=
        fun c a => map_smul W_equiv c a
      rw [key, inner_smul_left]
    definite := by
      intro x hx
      exact W_equiv.map_eq_zero_iff.mp (by simpa using hx)
  }

  let temp_inner := InnerProductSpace.ofCore inner_prod_core.toCore
  let add_comm := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℝ) (F := (FreshTopology (W)))

  let normed_space := InnerProductSpace.Core.toNormedSpace (𝕜 := ℝ) (F := (FreshTopology (W)))

  have proper_space: ProperSpace (FreshTopology (W)) := FiniteDimensional.proper_rclike ℝ _

  have fresh_t2: T2Space (FreshTopology (W)) := TopologicalSpace.t2Space_of_metrizableSpace


  let plain_linear_to_clm: (((W)) →ₗ[ℝ] ((W)))ˣ →* (((W)) →L[ℝ] ((W)))ˣ := {
    toFun := fun f => {
      val := LinearMap.toContinuousLinearMap f.val
      inv := LinearMap.toContinuousLinearMap f.inv
      val_inv := by
        have old_inv := f.val_inv
        ext a
        apply_fun (fun f => f a) at old_inv
        simp only [Units.inv_eq_val_inv, Module.End.one_apply] at old_inv
        apply old_inv
      inv_val := by
        have old_inv := f.inv_val
        ext a
        apply_fun (fun f => f a) at old_inv
        simp only [Units.inv_eq_val_inv, Module.End.one_apply] at old_inv
        apply old_inv
    }
    -- TODO - why is a normal `simp` so slow here?
    map_one' := by
      ext a
      simp only []
      rfl
    map_mul' := by
      intro f g
      ext a
      simp only []
      rfl
  }

  let linear_to_clm: ((FreshTopology (W)) →ₗ[ℝ] (FreshTopology (W)))ˣ →* ((FreshTopology (W)) →L[ℝ] (FreshTopology (W)))ˣ := {
    toFun := fun f => {
      val := LinearMap.toContinuousLinearMap f.val
      inv := LinearMap.toContinuousLinearMap f.inv
      val_inv := by
        have old_inv := f.val_inv
        ext a
        apply_fun (fun f => f a) at old_inv
        simp only [Units.inv_eq_val_inv, Module.End.one_apply] at old_inv
        apply old_inv
      inv_val := by
        have old_inv := f.inv_val
        ext a
        apply_fun (fun f => f a) at old_inv
        simp only [Units.inv_eq_val_inv, Module.End.one_apply] at old_inv
        apply old_inv
    }
    -- TODO - why is a normal `simp` so slow here?
    map_one' := by
      ext a
      simp only []
      rfl
    map_mul' := by
      intro f g
      ext a
      simp only []
      rfl
  }


  have plain_linear_to_clm_preserves_norm (g: G) (w: (W)): ‖(plain_linear_to_clm (GRepW_base g)).val w‖ = ‖w‖ := by
    simp [plain_linear_to_clm]
    have exists_v: ∃ v, Submodule.Quotient.mk v = w := by
      apply Quotient.exists_rep
    obtain ⟨v, hv⟩ := exists_v
    simp [GRepW, GRepW_base, GRepW_non_invertible]
    nth_rw 1 [← hv]
    rw [Representation.asGroupHom_apply]
    simp only [Representation.quotient_apply, Submodule.mapQ_apply]

    rw [quotient_norm_eq_norm]
    rw [GRep_preserves_norm]
    rw [← hv]
    rw [quotient_norm_eq_norm]


  let my_range := (linear_to_clm.comp GRepW_base).range

  have fresh_complete: CompleteSpace (FreshTopology (W)) := by apply complete_of_proper (α := FreshTopology (W))



  -- TODO - generalize to LinearMap/ContinuousLinearMap
  have units_val_embedding: Topology.IsEmbedding (Units.val (α := ((FreshTopology (W)) →L[ℝ] (FreshTopology (W))))) := by
    apply Units.isEmbedding_val_mk' (f := fun g => g.inverse)
    . intro a ha
      apply (ContinuousLinearMap.IsInvertible.contDiffAt_map_inverse (n := 1) ?_).continuousAt.continuousWithinAt
      simp at ha
      obtain ⟨b, hb⟩ := ha
      use ContinuousLinearEquiv.ofUnit b
      rw [← hb]
      rfl
    . intro u
      apply ContinuousLinearMap.inverse_eq
      .
        have u_val_inv := u.val_inv
        rw [ContinuousLinearMap.mul_def] at u_val_inv
        -- TODO - avoid the unfold somehow
        unfold Inv.inv
        unfold Units.instInv
        simp only []
        rw [u_val_inv]
        rfl
      .
        unfold Inv.inv
        unfold Units.instInv
        simp only []
        have u_inv_val := u.inv_val
        rw [ContinuousLinearMap.mul_def] at u_inv_val
        rw [u_inv_val]
        rfl


  let my_new_range := ((GRepW).comp GRepW_base).range
  unfold rho_g


  -- Naming the type keeps this out of the instance diamond on `W →L[ℝ] W`
  -- (`PseudoMetricSpace…toTopologicalSpace` vs `ContinuousLinearMap.topologicalSpace`),
  -- which `infer_instance` can only bridge at a raised `maxSynthPendingDepth`.
  have continuous_mul: ContinuousMul ((W) →L[ℝ] (W)) :=
    (NonUnitalSeminormedRing.toIsTopologicalRing (α := (W) →L[ℝ] (W))).toContinuousMul

  have is_topological: IsTopologicalGroup ((W) →L[ℝ] (W))ˣ := by
    infer_instance

  let plain_units_metric: MetricSpace (((W)) →L[ℝ] ((W)))ˣ := by
    apply Topology.IsEmbedding.comapMetricSpace (f := Units.val)
    exact isembedding_units_val

  let units_metric: MetricSpace ((FreshTopology (W)) →L[ℝ] (FreshTopology (W)))ˣ := by
    apply Topology.IsEmbedding.comapMetricSpace (f := Units.val)
    apply units_val_embedding


  have fresh_equiv: W ≃L[ℝ] FreshTopology (W) := ContinuousLinearEquiv.ofFinrankEq (rfl)

  let to_fresh (f: (W) ≃ₗ[ℝ] (W)): (FreshTopology (W)) ≃ₗ[ℝ] (FreshTopology (W)) := f
  let new_map_entry (f: (W →L[ℝ] W)ˣ): ((FreshTopology W) →L[ℝ] (FreshTopology W))ˣ := {
    val := ContinuousLinearEquiv.arrowCongr fresh_equiv fresh_equiv f.val,
    inv := ContinuousLinearEquiv.arrowCongr fresh_equiv fresh_equiv f.inv
    val_inv := by
      ext a
      simp
      conv =>
        arg 1
        equals (fresh_equiv ((f.val * f.inv) (fresh_equiv.symm a))) =>
          rfl
      simp
    inv_val := by
      ext a
      simp
      conv =>
        arg 1
        equals (fresh_equiv ((f.inv * f.val) (fresh_equiv.symm a))) =>
          rfl
      simp
  }

  let new_map_entry_inv (f: ((FreshTopology W) →L[ℝ] (FreshTopology W))ˣ ): (W →L[ℝ] W)ˣ  := {
    val := (ContinuousLinearEquiv.arrowCongr fresh_equiv fresh_equiv).symm f.val,
    inv := (ContinuousLinearEquiv.arrowCongr fresh_equiv fresh_equiv).symm f.inv
    val_inv := by
      ext a
      simp
      conv =>
        arg 1
        equals (fresh_equiv.symm ((f.val * f.inv) (fresh_equiv a))) =>
          rfl
      simp
    inv_val := by
      ext a
      simp
      conv =>
        arg 1
        equals (fresh_equiv.symm ((f.inv * f.val) (fresh_equiv a))) =>
          rfl
      simp
  }

  let to_continuous_hom: (FreshTopology (W) →ₗ[ℝ] FreshTopology (W)) →* (FreshTopology (W) →L[ℝ] FreshTopology (W)) := {
    toFun := fun f => f.toContinuousLinearMap,
    map_one' := by
      ext a
      simp
    map_mul' := by
      intro a b
      rfl
    }

  let new_map_hom: (W →L[ℝ] W)ˣ ≃* ((FreshTopology W) →L[ℝ] (FreshTopology W))ˣ := {
    toFun := new_map_entry,
    invFun := new_map_entry_inv,
    left_inv := by
      simp [Function.LeftInverse]
      intro x
      ext a
      simp [new_map_entry, new_map_entry_inv]
    right_inv := by
      simp [Function.RightInverse]
      intro x
      ext a
      simp [new_map_entry, new_map_entry_inv]
    map_mul' := by
      intro f g
      simp [new_map_entry]
      ext a
      simp
  }


  let mapped_group := Subgroup.map new_map_hom.toMonoidHom my_new_range.topologicalClosure

  have my_new_range_compact: CompactSpace my_new_range.topologicalClosure := by
    refine { isCompact_univ := ?_ }
    rw [Subtype.isCompact_iff]
    rw [Topology.IsEmbedding.isCompact_iff (f := Units.val) ?_]
    . rw [Metric.isCompact_iff_isClosed_bounded (α := (W) →L[ℝ] (W))]
      refine ⟨?_, ?_⟩
      . apply IsSeqClosed.isClosed
        by_contra!
        simp [IsSeqClosed] at this
        obtain ⟨seq, seq_in, ⟨lim_seq, seq_tendsto_lim_seq, lim_seq_not_mem⟩⟩ := this

        by_cases lim_seq_invertible: IsUnit lim_seq.toLinearMap
        .
          -- If the limit (in the space of linear maps) is invertible, then the limit will also exist in the space
          -- of units, which will then imply that the limit exists in the space of linear maps.
          -- TODO - this probably can be a direct proof, rather than by contradiction
          obtain ⟨u, hu⟩ := lim_seq_invertible
          have closure_closed := Subgroup.isClosed_topologicalClosure my_new_range
          apply IsClosed.isSeqClosed at closure_closed
          dsimp [IsSeqClosed] at closure_closed

          have seq_units: ∀ n: ℕ, IsUnit (seq n) := by
            intro n
            obtain ⟨x, x_mem, seq_eq_x⟩ := (seq_in n)
            rw [← seq_eq_x]
            apply Units.isUnit

          have lim_units := closure_closed (x := fun n => (seq_units n).unit) (p := plain_linear_to_clm u) ?_ ?_
          .
            specialize lim_seq_not_mem (plain_linear_to_clm u) lim_units
            conv at lim_seq_not_mem =>
              arg 1
              lhs
              equals u.val.toContinuousLinearMap =>
                rfl
            rw [hu] at lim_seq_not_mem
            conv at lim_seq_not_mem =>
              arg 1
              lhs
              equals lim_seq =>
                rfl
            simp at lim_seq_not_mem
          . intro n
            have seq_n := seq_in n
            obtain ⟨x, x_mem, seq_eq_x⟩ := seq_n
            simp_rw [← seq_eq_x]
            simpa using x_mem
          .
            rw [Topology.IsEmbedding.tendsto_nhds_iff (g := Units.val)]
            .
              conv =>
                arg 1
                equals seq =>
                  rfl

              have to_clm_u: plain_linear_to_clm u = u.val.toContinuousLinearMap := by
                rfl

              have u_val_eq_lim: u.val.toContinuousLinearMap = lim_seq := by
                rw [hu]
                rfl

              rw [to_clm_u, u_val_eq_lim]
              exact seq_tendsto_lim_seq
            .
              exact isembedding_units_val


        -- If the limit (in the space of linear maps) is not invertible, then it has a non-trivial kernel.
        rw [LinearMap.isUnit_iff_ker_eq_bot] at lim_seq_invertible
        apply Submodule.exists_mem_ne_zero_of_ne_bot at lim_seq_invertible
        obtain ⟨v, v_in_ker, v_ne_zero⟩ := lim_seq_invertible
        simp at v_in_ker


        have eval_at := Filter.Tendsto.eval_const seq_tendsto_lim_seq v
        have norm_tendsto := Continuous.tendsto (f := fun (x: W) => ‖x‖) (by fun_prop) (lim_seq v)
        have norm_seq_lim := Filter.Tendsto.comp norm_tendsto eval_at
        rw [v_in_ker] at norm_seq_lim
        rw [norm_zero] at norm_seq_lim
        conv at norm_seq_lim =>
          arg 1
          -- Use the fact that the action preserves the euclidian norm (maybe just up to a constant),
          -- so the sequence is actually constant
          equals fun x => ‖v‖ =>
            funext n
            simp
            have seq_mem := seq_in n
            obtain ⟨x, x_mem, seq_eq_x⟩ := seq_mem
            rw [← seq_eq_x]
            apply ContinuousWithinAt.eq_const_of_mem_closure (f := fun (x: ((W) →L[ℝ] (W))ˣ) => ‖x.val v‖) (c := ‖v‖) (x := x) (s := my_new_range)
            . apply Continuous.continuousWithinAt
              fun_prop
            . exact x_mem
            . intro y hy
              simp [my_range] at hy
              obtain ⟨g, rep_g_eq_y⟩ := hy
              rw [← rep_g_eq_y]
              apply plain_linear_to_clm_preserves_norm

        -- TODO - why do we need this?
        have r_t2: T2Space ℝ := TopologicalSpace.t2Space_of_metrizableSpace

        have tendsto_norm_v := tendsto_const_nhds (α := ℕ) (f := Filter.atTop) (x := ‖v‖)
        have norm_v_zero := tendsto_nhds_unique tendsto_norm_v norm_seq_lim
        simp at norm_v_zero
        contradiction
      .
        simp
        apply LipschitzWith.isBounded_image (f := Units.val) (K := 1)
        . rw [lipschitzWith_iff_dist_le_mul]
          intro a b
          simp
          rfl
        .
          apply Bornology.IsBounded.closure
          rw [Metric.isBounded_iff_subset_ball 1]
          use 3
          intro a ha
          simp [my_new_range] at ha
          obtain ⟨g, rep_g_eq_a⟩ := ha
          simp
          conv =>
            lhs
            equals dist (a.val) (ContinuousLinearMap.id _ _) =>
              rfl
          grw [dist_le_norm_add_norm (a.val) (ContinuousLinearMap.id ℝ W)]
          grw [ContinuousLinearMap.norm_id_le]
          rw [← rep_g_eq_a]
          grw [GRepW_norm_le]
          norm_num
        -- Bornology.isBounded_image_subtype_val
    . exact isembedding_units_val


  have continuous_new_map_entry: Continuous new_map_entry := by
    simp [new_map_entry]
    rw [Units.continuous_iff]
    refine ⟨?_, ?_⟩
    . fun_prop
    . fun_prop


  have compact_mapped_group: CompactSpace mapped_group := by
    have h1 : IsCompact (my_new_range.topologicalClosure : Set (W →L[ℝ] W)ˣ) :=
      isCompact_iff_compactSpace.mpr my_new_range_compact
    have hcont : Continuous (⇑new_map_hom.toMonoidHom) := by
      simp [new_map_hom]
      apply continuous_new_map_entry
    have h2 := h1.image hcont
    rw [← Subgroup.coe_map] at h2
    exact isCompact_iff_compactSpace.mp h2

  let map_sub_equiv := (Subgroup.subgroupOfEquivOfLe (H := map new_map_hom.toMonoidHom my_new_range) (K := mapped_group) (by
    unfold mapped_group
    simp
    rw [Subgroup.map_le_map_iff]
    apply le_sup_of_le_left
    exact le_topologicalClosure my_new_range
  )).symm

  have S_data_range := map_range_S_data (f := (GRepW.comp GRepW_base)) (G_SPolyData hd)
  have mapped_S_data := map_S_data (f := new_map_hom.toMonoidHom) _ S_data_range
  have final_data := map_equiv_S_data map_sub_equiv mapped_S_data


  let data := theorem_3_8_real (H := mapped_group) compact_mapped_group ((Subgroup.map new_map_hom.toMonoidHom my_new_range).subgroupOf mapped_group) ?_ (final_data)
  obtain ⟨B, B_abelian, B_finite_index⟩ := data

  let reverse_hom: ((map new_map_hom.toMonoidHom my_new_range).subgroupOf mapped_group) →* (GRepW_base).range := {
    toFun := fun g => (
      ((⟨Units.map (ContinuousLinearMap.toLinearMapRingHom.toMonoidHom) (new_map_hom.symm g.val), by (
        simp
        have g_prop := g.property
        rw [Subgroup.mem_subgroupOf] at g_prop
        rw [Subgroup.mem_map] at g_prop
        obtain ⟨x, x_mem, g_eq⟩ := g_prop
        simp [my_new_range] at x_mem
        obtain ⟨a, ha⟩ := x_mem
        use a
        ext f
        simp
        apply_fun (fun h => Units.map (ContinuousLinearMap.toLinearMapRingHom.toMonoidHom) h) at ha
        simp [GRepW] at ha
        rw [ha]
        simp [new_map_hom, new_map_entry_inv]
        rw [← g_eq]
        simp [new_map_hom, new_map_entry]
      )⟩) : GRepW_base.range)
    ),
    map_one' := by
      simp [map_one]
    map_mul' := by
      intro a b
      apply Subtype.ext
      show (Units.map _) (new_map_hom.symm ↑↑(a * b)) =
        (Units.map _) (new_map_hom.symm ↑↑a) * (Units.map _) (new_map_hom.symm ↑↑b)
      rw [← map_mul (Units.map _), ← map_mul new_map_hom.symm]
      norm_cast
  }

  have reverse_hom_ker_bot: reverse_hom.ker = ⊥ := by
    rw [MonoidHom.ker_eq_bot_iff]
    intro a b hab
    simp only [reverse_hom, MonoidHom.coe_mk, OneHom.coe_mk, Subtype.mk.injEq] at hab
    apply Units.map_injective at hab
    .
      replace hab := new_map_hom.symm.injective hab
      exact Subtype.ext (Subtype.ext hab)
    .
      intro a b hab
      simpa using hab

  have reverse_hom_range_top: reverse_hom.range = ⊤ := by
    rw [Subgroup.eq_top_iff']
    intro x
    have x_prop := x.property
    rw [MonoidHom.mem_range] at x_prop
    obtain ⟨g, hg⟩ := x_prop
    have mem_range: plain_linear_to_clm ↑x ∈ my_new_range := by
      refine MonoidHom.mem_range.mpr ⟨g, ?_⟩
      rw [← hg]
      rfl
    have mem_closure: plain_linear_to_clm ↑x ∈ my_new_range.topologicalClosure :=
      Subgroup.le_topologicalClosure my_new_range mem_range
    refine MonoidHom.mem_range.mpr
      ⟨⟨⟨new_map_entry (plain_linear_to_clm ↑x),
          Subgroup.mem_map_of_mem new_map_hom.toMonoidHom mem_closure⟩, ?_⟩, ?_⟩
    .
      rw [Subgroup.mem_subgroupOf]
      exact Subgroup.mem_map_of_mem new_map_hom.toMonoidHom mem_range
    .
      have hrt : ∀ y, new_map_hom.symm (new_map_entry y) = y := new_map_hom.left_inv
      refine Subtype.ext ?_
      change (Units.map (ContinuousLinearMap.toLinearMapRingHom (R₁ := ℝ) (M₁ := W)).toMonoidHom)
          (new_map_hom.symm (new_map_entry (plain_linear_to_clm ↑x))) = x.val
      rw [hrt]
      ext f
      rfl


  let B' := Subgroup.map reverse_hom B
  use B'
  refine ⟨?_, ?_⟩
  . simp only [B']
    apply Subgroup.map_isMulCommutative
  . simp only [B']
    rw [Subgroup.finiteIndex_iff]
    rw [Subgroup.index_map]
    rw [reverse_hom_ker_bot, reverse_hom_range_top, sup_bot_eq, Subgroup.index_top, mul_one]
    exact B_finite_index.index_ne_zero
  .
    have base_fg: (map new_map_hom.toMonoidHom my_new_range).FG := by
      apply group_fg_map
      simp [my_new_range]
      have group_fg: Group.FG (GRepW.comp (GRepW_base)).range := by
        apply Group.fg_range
      exact (Group.fg_iff_subgroup_fg (GRepW.comp GRepW_base).range).mp group_fg

    have base_le: (map new_map_hom.toMonoidHom my_new_range) ≤ mapped_group := by
      intro a ha
      simp at ha
      simp [mapped_group]
      obtain ⟨g, g_mem, g_eq_a⟩ := ha
      use g
      refine ⟨?_, g_eq_a⟩
      apply Subgroup.le_topologicalClosure my_new_range g_mem


    rw [Subgroup.fg_iff]
    rw [Subgroup.fg_iff] at base_fg
    obtain ⟨S, S_eq, S_finite⟩ := base_fg

    have S_in_map: ∀ s ∈ S, s ∈ (map new_map_hom.toMonoidHom my_new_range) := by
      rw [Subgroup.ext_iff] at S_eq
      intro s hs
      apply (S_eq s).mp ?_
      exact Subgroup.mem_closure.mpr fun K a ↦ a hs

    let S' := Set.range (fun (s: S) => (⟨s.val, base_le (S_in_map s s.property)⟩ : mapped_group))
    use S'
    -- TODO - this is a huge mess. This can be a general proof about the closure of Subgroup.subgroupOf
    refine ⟨?_, ?_⟩
    .
      simp only [S']
      rw [← S_eq]
      ext a
      refine ⟨?_, ?_⟩
      . intro ha
        rw [Subgroup.mem_subgroupOf]
        induction ha using Subgroup.closure_induction_left with
        | one => simp
        | mul_left y hy z hz h_other_z =>
          simp
          apply Subgroup.mul_mem
          . simp at hy
            obtain ⟨p, p_mem, p_eq_y⟩ := hy
            rw [← p_eq_y]
            simp
            apply Subgroup.mem_closure_of_mem p_mem
          . exact h_other_z
        | inv_mul_cancel y hy z hz h_other_z =>
          simp
          apply Subgroup.mul_mem
          . simp
            simp at hy
            obtain ⟨p, p_mem, p_eq_y⟩ := hy
            rw [← p_eq_y]
            simp
            apply Subgroup.mem_closure_of_mem p_mem
          . exact h_other_z
      . intro ha
        rw [Subgroup.mem_subgroupOf] at ha
        rw [Subgroup.mem_closure]
        intro K hK
        rw [Subgroup.mem_closure] at ha
        have a_mem := ha (Subgroup.map mapped_group.subtype K) ?_
        . simpa using a_mem
        . simp
          intro s hs
          rw [Set.range_subset_iff] at hK
          have s_mem := hK ⟨s, hs⟩
          simp
          simp at s_mem
          use ?_
          apply base_le (S_in_map s hs)
    .
      simp [S']
      rw [← Set.finite_coe_iff] at S_finite
      apply Set.finite_range

-- We need this to work with Finset


lemma g_hom_abelian {T: Type*} [Group T] (A: Subgroup G) (A_finite_index: A.FiniteIndex) (hom: A →* T) (hom_surjective: Function.Surjective hom) (H: Subgroup T) (H_infinite: Infinite H) (H_abeliean: IsMulCommutative H) (H_finite_index: H.FiniteIndex) (H_FG: Group.FG H): Nonempty (Theorem3_1_Input G) := by
  -- TODO - generalize this to a lemma: finite-index subgroup of an infinite group is infinite
  -- and upstream to mathlib


  -- TODO - figure out how to make instance inference work here
  obtain ⟨i, j, i_fin, j_fin, p, p_prime, e, exists_iso⟩ := @CommGroup.equiv_free_prod_prod_multiplicative_zmod H (haveI := H_abeliean; { (inferInstance : Group H) with mul_comm := mul_comm' }) (H_FG)
  have iso := Classical.choice exists_iso

  have j_nonempty: Nonempty j := by
    by_contra!
    have H_finite : Finite H := by
      rw [Equiv.finite_iff iso.toEquiv]
      have finite_i: Finite i := by
        infer_instance
      have finite_mul: ∀ f: i, Finite (Multiplicative (ZMod (p f ^ e f))) := by
        intro f
        simp [Multiplicative]
        have pow_ne_zero: NeZero (p f ^ e f) := by
          exact {
            out := by
              simp
              have first_ne_zero := Nat.Prime.ne_zero (p_prime f)
              simp [first_ne_zero]
          }
        apply Finite.of_fintype
      apply Finite.instProd
    have no_finite := H_infinite.not_finite
    contradiction

  -- TODO - can we get the comp '∘' syntax to give us a monoid hom, instead of a plain function?
  let h_to_z := (Pi.evalMonoidHom _ (Classical.choice (by
    exact j_nonempty
  ))).comp ((MonoidHom.fst _ _).comp iso.toMonoidHom)

  have h_to_z_surjective: Function.Surjective h_to_z := by
    unfold h_to_z
    simp
    apply Function.Surjective.comp
    .
      intro x
      simp
      use fun _ => x
    . apply Function.Surjective.comp
      . exact Prod.fst_surjective
      . exact iso.surjective


  let G' := Subgroup.comap hom H

  -- TODO - generalize this and PR to mathlib


  have G'_finite_index: G'.FiniteIndex := by
    unfold G'
    exact {
      index_ne_zero := by
        simp
        rw [Subgroup.index_comap]
        -- apply somehow found this - how does it work???
        exact Subgroup.FiniteIndex.index_ne_zero
    }


  -- TODO - there must be an easier way to do this
  let g'_to_h: (map A.subtype G') →* H := {
    toFun := fun g => ⟨hom ⟨g.val, by (
      -- TODO - clean this up
      have foo := g.property
      rw [Subgroup.mem_map] at foo
      obtain ⟨x, hx, a_subtype⟩ := foo
      rw [← a_subtype]
      simp
    )⟩, by (
      have g_prop := g.property
      simp only [G', Subgroup.mem_comap] at g_prop
      rw [Subgroup.mem_map] at g_prop
      obtain ⟨x, hx, a_subtype⟩ := g_prop
      simp_rw [← a_subtype]
      simp
      simp at hx
      exact hx
    )⟩
    map_one' := by
      simp
      conv =>
        lhs
        arg 2
        equals 1 => simp
      simp

    map_mul' := by
      simp
      intro a ha a_mem b hb b_mem

      conv =>
        lhs
        arg 2
        equals ⟨a, ha⟩ * ⟨b, hb⟩ => simp
      rw [MonoidHom.map_mul]
  }

  let additive_g'_to_h := g'_to_h.toAdditive
  let additive_h_to_z := h_to_z.toAdditive

  let g_to_additive_z := additive_h_to_z.comp additive_g'_to_h
  let g_to_z := (AddEquiv.additiveMultiplicative ℤ).toAddMonoidHom.comp g_to_additive_z


  apply Nonempty.intro
  exact {
    G' := Subgroup.map A.subtype G',
    finite_index := by
      rw [Subgroup.finiteIndex_iff]
      simp [Subgroup.index_map_subtype]
      refine ⟨?_, ?_⟩
      . rw [← ne_eq]
        rw [← Subgroup.finiteIndex_iff]
        exact G'_finite_index
      . exact A_finite_index.index_ne_zero
      -- G'_finite_index
    φ := g_to_z,
    hφ := by
      simp [g_to_z, g_to_additive_z]
      apply Function.Surjective.comp
      . simp [additive_h_to_z]
        exact h_to_z_surjective
      .
        simp [additive_g'_to_h, g'_to_h]
        intro h
        obtain ⟨a, hom_a⟩ := hom_surjective h
        simp
        use a
        simp
        simp [G', hom_a]
  }

-- Case 1 in Section 3.3 of Vikman, where the representation ρ(G) is infinite
lemma rho_g_case_infinite {d: ℕ} (hd: HasPolynomialGrowthD S d) (hr: Infinite (↥(rho_g))): Nonempty (Theorem3_1_Input G) := by
  obtain ⟨H, H_abelian, H_finite_index⟩ := rho_g_contains_abelian hd


  have h_fg: Group.FG H := by
    apply Subgroup.fg_of_index_ne_zero

  let top_equiv := Subgroup.topEquiv (G := G)
  let top_comp := (GRepW_base).comp top_equiv.toMonoidHom
  let g_rho := (GRepW_base).rangeRestrict.comp top_equiv.toMonoidHom


  have target := g_hom_abelian ⊤ (by infer_instance) (g_rho) ?_ (H) ?_ ?_ ?_ ?_
  . exact target
  .
    simp [g_rho]
    exact MonoidHom.rangeRestrict_surjective GRepW_base
  .
    unfold rho_g at hr
    have card_mul := Subgroup.card_mul_index H
    unfold rho_g at card_mul
    nth_rw 2 [Nat.card_eq_zero_of_infinite] at card_mul
    rw [Nat.mul_eq_zero] at card_mul
    replace card_mul := card_mul.resolve_right H_finite_index.index_ne_zero
    rw [Nat.card_eq_zero] at card_mul
    exact card_mul.resolve_left (fun h => h.false ⟨1, H.one_mem⟩)
  . exact H_abelian
  . exact H_finite_index
  . exact h_fg

end GeneratesNS
end

section
-- module Solutions.OAIQ093_PR.Theorem31Input
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Constructing a `Theorem3_1_Input`

The finite-image case `rho_g_case_finite` and `exists_theorem_3_1_input`.
-/


set_option linter.style.longLine false
set_option linter.style.cdot false
set_option linter.style.commandStart false

open Subgroup
open scoped Finset
open scoped Pointwise
open scoped commutatorElement

namespace GeneratesNS
open Generates

variable [hGS: Generates]
include hGS

open scoped RealInnerProductSpace

set_option synthInstance.maxHeartbeats 500000

set_option maxHeartbeats 9000000

open MeasureTheory

open MeasureTheory

-- TODO - figure out why we need these


-- TODO - upstream to mathlib
omit hGS in
lemma exists_theorem_3_1_input_oai [hGS: Generates ] {d: ℕ} (hd: HasPolynomialGrowthD S d): Nonempty (Theorem3_1_Input G) := by
  by_cases rho_g_infinite: Infinite (↥(rho_g))
  . exact rho_g_case_infinite hd rho_g_infinite
  . exact rho_g_case_finite (by simpa using rho_g_infinite)

end GeneratesNS
end

theorem solution.{u_1} : type_of% @GeneratesNS.exists_theorem_3_1_input_oai.{u_1} := @GeneratesNS.exists_theorem_3_1_input_oai.{u_1}
