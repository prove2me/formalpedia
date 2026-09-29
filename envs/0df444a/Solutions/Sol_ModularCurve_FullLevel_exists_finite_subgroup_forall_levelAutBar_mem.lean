-- Prove2me | solution 1 for ModularCurve.FullLevel.exists_finite_subgroup_forall_levelAutBar_mem
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.339302+00:00
-- url     : https://prove2.me/submissions/5647b5f0-184e-518e-b627-d3ec27272a9d

import Mathlib
import Definitions.Def_ModularCurve_FullLevelJacobian
import Theorems.Thm_ModularCurve_FullLevel_levelAutBar_mul
import Theorems.Thm_ModularCurve_FullLevel_levelAutBar_pow_inv_eq_levelAutBar_of_diag_conj
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_exists_finite_subgroup_forall_levelAutBar_mem

set_option autoImplicit false

p2m_open "ModularCurve P2MW.S_ModularCurve_FullLevel_exists_finite_subgroup_forall_levelAutBar_mem.ModularCurve ModularCurve.FullLevel P2MW.S_ModularCurve_FullLevel_exists_finite_subgroup_forall_levelAutBar_mem.ModularCurve.FullLevel CongruenceSubgroup"
open scoped MatrixGroups

namespace ModularCurve
namespace FullLevel
p2m_export "ModularCurve.FullLevel" "fieldBar Idx levelAutBar levelAutBar_mul levelAutBar_pow_inv_eq_levelAutBar_of_diag_conj"
p2m_open "ModularCurve.FullLevel ModularCurve"

theorem GAL_levelAutBar_eq_of_map_eq (q : ℕ) [Fact q.Prime] (M' : ℕ) (hqM' : ¬ q ∣ M') (ζ : Idx q)
    (α α' : SL(2, ℤ)) (hα : α ∈ Gamma0 M') (hα' : α' ∈ Gamma0 M')
    (h : (α : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ZMod q) =
      (α' : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ZMod q)) :
    levelAutBar q M' ζ α = levelAutBar q M' ζ α' := by
  have key : ∀ β : SL(2, ℤ), β ∈ Gamma0 M' →
      (α : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ZMod q) =
        (β : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ZMod q) →
      levelAutBar q M' (ζ.pow 1⁻¹) α = levelAutBar q M' ζ β := by
    intro β hβ hβ'
    refine levelAutBar_pow_inv_eq_levelAutBar_of_diag_conj q M' hqM' ζ 1 α β hα hβ ?_
    rw [Units.val_one, ← Matrix.one_fin_two, one_mul, mul_one]
    exact hβ'
  exact (key α hα rfl).symm.trans (key α' hα' h)

theorem GAL_finite_setOf_levelAutBar (q : ℕ) [Fact q.Prime] (M' : ℕ) (hqM' : ¬ q ∣ M') (ζ : Idx q) :
    Set.Finite {τ : fieldBar q M' ≃ₐ[AlgebraicClosure ℚ] fieldBar q M' |
      ∃ γ : SL(2, ℤ), γ ∈ Gamma0 M' ∧ τ = levelAutBar q M' ζ γ} := by
  haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  have hsub : ∀ m : Matrix (Fin 2) (Fin 2) (ZMod q),
      Set.Subsingleton {τ : fieldBar q M' ≃ₐ[AlgebraicClosure ℚ] fieldBar q M' |
        ∃ γ : SL(2, ℤ), γ ∈ Gamma0 M' ∧
          (γ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ZMod q) = m ∧ τ = levelAutBar q M' ζ γ} := by
    intro m
    rintro τ₁ ⟨γ₁, h₁, hm₁, rfl⟩ τ₂ ⟨γ₂, h₂, hm₂, rfl⟩
    exact GAL_levelAutBar_eq_of_map_eq q M' hqM' ζ γ₁ γ₂ h₁ h₂ (hm₁.trans hm₂.symm)
  refine Set.Finite.subset (Set.finite_iUnion fun m => (hsub m).finite) ?_
  rintro τ ⟨γ, hγ, rfl⟩
  exact Set.mem_iUnion.mpr ⟨_, γ, hγ, rfl, rfl⟩

theorem GAL_levelAutBar_one (q : ℕ) [Fact q.Prime] (M' : ℕ) (hqM' : ¬ q ∣ M') (ζ : Idx q) :
    levelAutBar q M' ζ 1 = 1 := by
  have h := levelAutBar_mul q M' hqM' ζ 1 1 (one_mem _) (one_mem _)
  rw [one_mul, ← AlgEquiv.aut_mul] at h
  have h2 : levelAutBar q M' ζ 1 * levelAutBar q M' ζ 1 = levelAutBar q M' ζ 1 * 1 := by
    rw [mul_one]; exact h.symm
  exact mul_left_cancel h2

theorem GAL_levelAutBar_mul' (q : ℕ) [Fact q.Prime] (M' : ℕ) (hqM' : ¬ q ∣ M') (ζ : Idx q)
    (α β : SL(2, ℤ)) (hα : α ∈ Gamma0 M') (hβ : β ∈ Gamma0 M') :
    levelAutBar q M' ζ α * levelAutBar q M' ζ β = levelAutBar q M' ζ (β * α) := by
  rw [AlgEquiv.aut_mul, levelAutBar_mul q M' hqM' ζ β α hβ hα]

theorem GAL_levelAutBar_inv (q : ℕ) [Fact q.Prime] (M' : ℕ) (hqM' : ¬ q ∣ M') (ζ : Idx q)
    (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M') :
    (levelAutBar q M' ζ γ)⁻¹ = levelAutBar q M' ζ γ⁻¹ := by
  apply inv_eq_of_mul_eq_one_right
  rw [GAL_levelAutBar_mul' q M' hqM' ζ γ γ⁻¹ hγ (inv_mem hγ), inv_mul_cancel, GAL_levelAutBar_one q M' hqM' ζ]

end ModularCurve.FullLevel

theorem solution
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M') (ζ : Idx q) :
    ∃ G : Subgroup (fieldBar q M' ≃ₐ[AlgebraicClosure ℚ] fieldBar q M'),
      Finite ↥G ∧
      (∀ γ : SL(2, ℤ), γ ∈ Gamma0 M' → levelAutBar q M' ζ γ ∈ G) ∧
      (∀ τ ∈ G, ∃ γ : SL(2, ℤ), γ ∈ Gamma0 M' ∧ τ = levelAutBar q M' ζ γ) := by
  refine ⟨{ carrier := {τ | ∃ γ : SL(2, ℤ), γ ∈ Gamma0 M' ∧ τ = levelAutBar q M' ζ γ},
            mul_mem' := ?_, one_mem' := ?_, inv_mem' := ?_ }, ?_, ?_, ?_⟩
  · rintro a b ⟨α, hα, rfl⟩ ⟨β, hβ, rfl⟩
    exact ⟨β * α, mul_mem hβ hα, GAL_levelAutBar_mul' q M' hqM' ζ α β hα hβ⟩
  · exact ⟨1, one_mem _, (GAL_levelAutBar_one q M' hqM' ζ).symm⟩
  · rintro τ ⟨γ, hγ, rfl⟩
    exact ⟨γ⁻¹, inv_mem hγ, GAL_levelAutBar_inv q M' hqM' ζ γ hγ⟩
  · exact (GAL_finite_setOf_levelAutBar q M' hqM' ζ).to_subtype
  · intro γ hγ
    exact ⟨γ, hγ, rfl⟩
  · intro τ hτ
    exact hτ

end S_ModularCurve_FullLevel_exists_finite_subgroup_forall_levelAutBar_mem
end P2MW
export P2MW.S_ModularCurve_FullLevel_exists_finite_subgroup_forall_levelAutBar_mem (solution)
