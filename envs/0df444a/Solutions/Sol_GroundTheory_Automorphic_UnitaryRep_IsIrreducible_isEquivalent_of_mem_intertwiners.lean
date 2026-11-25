-- Prove2me | solution 1 for GroundTheory.Automorphic.UnitaryRep.IsIrreducible.isEquivalent_of_mem_intertwiners
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:32:28.897584+00:00
-- url     : https://prove2.me/submissions/cd6ace0e-5db0-4360-b9a1-3214dd0e9964

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_UnitaryRepresentations_IsInvariantIffCommuteStarProjection
import Definitions.Def_GroundTheory_AutomorphicForms_UnitaryRepresentations_ExistsEqAlgebraMapOfIsSelfAdjoint
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_IsIrreducible_exists_eq_smul_one
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_IsEquivalent_symm
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_adjoint_mem_intertwiners
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_coe_restrict_apply
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_comp_mem_intertwiners
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.UnitaryRep.coe_restrict_apply



set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.UnitaryRep
open scoped InnerProductSpace ComplexConjugate
open scoped ComplexStarModule
open ContinuousLinearMap Complex
variable {G : Type*} [Group G] [TopologicalSpace G]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable {π : UnitaryRep G H} {σ : UnitaryRep G K}
namespace GroundTheory.Automorphic.UnitaryRep
namespace IsIrreducible
theorem _root_.solution (hπ : π.IsIrreducible)
    (hσ : σ.IsIrreducible) {T : H →L[ℂ] K} (hT : T ∈ π.intertwiners σ) (hT0 : T ≠ 0) :
    π.IsEquivalent σ := by
  obtain ⟨c, hc⟩ := hπ.exists_eq_smul_one
    (comp_mem_intertwiners (adjoint_mem_intertwiners hT) hT)
  obtain ⟨d, hd⟩ := hσ.exists_eq_smul_one
    (comp_mem_intertwiners hT (adjoint_mem_intertwiners hT))
  have key : ∀ v, (‖T v‖ : ℂ) ^ 2 = c * (‖v‖ : ℂ) ^ 2 := by
    intro v
    have h1 : ⟪v, (adjoint T ∘L T) v⟫_ℂ = ⟪T v, T v⟫_ℂ := by
      rw [comp_apply, adjoint_inner_right]
    rw [hc] at h1
    simp only [smul_apply, one_apply_eq_self, inner_smul_right] at h1
    have e1 : ⟪v, v⟫_ℂ = (‖v‖ : ℂ) ^ 2 := by rw [inner_self_eq_norm_sq_to_K]; rfl
    have e2 : ⟪T v, T v⟫_ℂ = (‖T v‖ : ℂ) ^ 2 := by rw [inner_self_eq_norm_sq_to_K]; rfl
    rw [e1, e2] at h1
    exact h1.symm
  obtain ⟨v₀, hv₀⟩ : ∃ v, T v ≠ 0 := by
    by_contra h
    push Not at h
    exact hT0 (ContinuousLinearMap.ext h)
  have hv₀' : v₀ ≠ 0 := fun h => hv₀ (by rw [h, map_zero])
  set r : ℝ := ‖T v₀‖ / ‖v₀‖ with hr
  have hrpos : 0 < r := div_pos (norm_pos_iff.mpr hv₀) (norm_pos_iff.mpr hv₀')
  have hcr : c = ((r ^ 2 : ℝ) : ℂ) := by
    have h := key v₀
    have hn : (‖v₀‖ : ℂ) ^ 2 ≠ 0 := pow_ne_zero _ (by exact_mod_cast (norm_pos_iff.mpr hv₀').ne')
    rw [hr, div_pow]
    push_cast
    exact eq_div_of_mul_eq hn h.symm
  have hnorm : ∀ v, ‖T v‖ = r * ‖v‖ := by
    intro v
    have h := key v
    rw [hcr] at h
    have h' : ‖T v‖ ^ 2 = (r * ‖v‖) ^ 2 := by
      rw [mul_pow]; exact_mod_cast h
    exact (pow_left_inj₀ (norm_nonneg _) (mul_nonneg hrpos.le (norm_nonneg _)) two_ne_zero).mp h'
  have hc0 : c ≠ 0 := by rw [hcr]; exact_mod_cast (pow_pos hrpos 2).ne'
  have hcd : c = d := by
    have e1 : T ∘L (adjoint T ∘L T) = c • T := by rw [hc]; ext v; simp
    have e2 : (T ∘L adjoint T) ∘L T = d • T := by rw [hd]; ext v; simp
    have e3 : (c - d) • T = 0 := by rw [sub_smul, ← e1, ← e2]; simp [comp_assoc]
    rcases smul_eq_zero.mp e3 with h | h
    · exact sub_eq_zero.mp h
    · exact absurd h hT0
  have hsurjT : Function.Surjective T := by
    intro w
    refine ⟨c⁻¹ • adjoint T w, ?_⟩
    have : (T ∘L adjoint T) w = d • w := by rw [hd]; simp
    rw [map_smul, show T (adjoint T w) = d • w from this, smul_smul, ← hcd, inv_mul_cancel₀ hc0,
      one_smul]
  let U : H →L[ℂ] K := ((r⁻¹ : ℝ) : ℂ) • T
  have hU : ∀ v, ‖U v‖ = ‖v‖ := by
    intro v
    simp only [U, smul_apply, norm_smul, Complex.norm_real, Real.norm_eq_abs, hnorm v,
      abs_of_pos (inv_pos.mpr hrpos)]
    rw [← mul_assoc, inv_mul_cancel₀ hrpos.ne', one_mul]
  let Ui : H →ₗᵢ[ℂ] K := { toLinearMap := (U : H →ₗ[ℂ] K), norm_map' := hU }
  have hsurj : Function.Surjective Ui := by
    intro w
    obtain ⟨v, rfl⟩ := hsurjT w
    refine ⟨(r : ℂ) • v, ?_⟩
    show U ((r : ℂ) • v) = T v
    simp only [U, smul_apply, map_smul, smul_smul]
    rw [← Complex.ofReal_mul, mul_inv_cancel₀ hrpos.ne', Complex.ofReal_one, one_smul]
  refine ⟨⟨LinearIsometryEquiv.ofSurjective Ui hsurj, fun g v => ?_⟩⟩
  show U (π g v) = σ g (U v)
  exact (Submodule.smul_mem _ _ hT) g v
end IsIrreducible
end GroundTheory.Automorphic.UnitaryRep
