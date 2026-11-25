-- Prove2me | solution 1 for GlobalTheory.AdTh.scalar_of_intertwines_up_to_scalar
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:28:25.339859+00:00
-- url     : https://prove2.me/submissions/35467c12-fd0a-44e5-95fe-20d547505657

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ScalarOfIntertwinesUpToScalar

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.AdTh
namespace GlobalTheory.AdTh
theorem _root_.solution (Γ M : Type) [Group Γ] [AddCommGroup M] [Module ℂ M]
    [FiniteDimensional ℂ M] [Nontrivial M] (ρ : Γ →* Module.End ℂ M) (S : Set Γ)
    (hS : Subgroup.closure S = ⊤) (htr : ∀ γ ∈ S, LinearMap.trace ℂ M (ρ γ) ≠ 0)
    (hirr : ∀ U : Submodule ℂ M, (∀ γ, U.map (ρ γ) ≤ U) → U = ⊥ ∨ U = ⊤)
    (T : M →ₗ[ℂ] M) (χ : Γ → ℂ) (hT : Function.Injective T)
    (h : ∀ γ x, T (ρ γ x) = χ γ • ρ γ (T x)) : ∃ a : ℂ, ∀ x, T x = a • x := by
  have hu : IsUnit (T : Module.End ℂ M) :=
    (Module.End.isUnit_iff _).2 ⟨hT, LinearMap.injective_iff_surjective.1 hT⟩
  obtain ⟨u, hu⟩ := hu
  have h1 : ∀ γ, (u : Module.End ℂ M) * ρ γ = χ γ • (ρ γ * u) := by
    intro γ
    ext x
    simp [hu, h]
  have hχ : ∀ γ ∈ S, χ γ = 1 := by
    intro γ hγ
    have h2 : (u : Module.End ℂ M) * ρ γ * (↑u⁻¹ : Module.End ℂ M) = χ γ • ρ γ := by
      rw [h1, smul_mul_assoc, mul_assoc, Units.mul_inv, mul_one]
    have h3 := congrArg (LinearMap.trace ℂ M) h2
    rw [LinearMap.trace_mul_comm, ← mul_assoc, Units.inv_mul, one_mul, map_smul, smul_eq_mul] at h3
    have h4 := htr γ hγ
    have : (χ γ - 1) * LinearMap.trace ℂ M (ρ γ) = 0 := by linear_combination -h3
    rcases mul_eq_zero.1 this with h5 | h5
    · exact sub_eq_zero.1 h5
    · exact absurd h5 h4
  have hc : ∀ γ, Commute (u : Module.End ℂ M) (ρ γ) := by
    intro γ
    have hγ : γ ∈ Subgroup.closure S := hS ▸ Subgroup.mem_top γ
    induction hγ using Subgroup.closure_induction with
    | mem x hx =>
      have := h1 x
      rw [hχ x hx, one_smul] at this
      exact this
    | one => rw [map_one]; exact Commute.one_right _
    | mul x y _ _ hx hy => rw [map_mul]; exact hx.mul_right hy
    | inv x _ hx =>
      have e1 : ρ x * ρ x⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
      have e2 : ρ x⁻¹ * ρ x = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
      exact Commute.units_inv_right (u := ⟨ρ x, ρ x⁻¹, e1, e2⟩) hx
  obtain ⟨a, ha⟩ := Module.End.exists_eigenvalue (T : Module.End ℂ M)
  refine ⟨a, fun x => ?_⟩
  rcases hirr (Module.End.eigenspace T a) (by
      rintro γ _ ⟨y, hy, rfl⟩
      have hy' : T y = a • y := Module.End.mem_eigenspace_iff.1 hy
      rw [Module.End.mem_eigenspace_iff]
      have := congrArg (fun f : Module.End ℂ M => f y) (hc γ).eq
      simp only [hu, Module.End.mul_apply] at this
      rw [this, hy', map_smul]) with h0 | h0
  · exact absurd h0 (Module.End.hasEigenvalue_iff.1 ha)
  · exact Module.End.mem_eigenspace_iff.1 (h0 ▸ Submodule.mem_top)
end GlobalTheory.AdTh
