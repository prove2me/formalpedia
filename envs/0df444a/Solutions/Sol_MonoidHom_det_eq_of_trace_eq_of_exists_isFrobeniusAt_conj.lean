-- Prove2me | solution 1 for MonoidHom.det_eq_of_trace_eq_of_exists_isFrobeniusAt_conj
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/da72bac8-32b7-52f6-b4c5-b75ac1f0eef4

import Mathlib
import Definitions.Def_GaloisRep_FrobeniusPowerDense
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MonoidHom_det_eq_of_trace_eq_of_exists_isFrobeniusAt_conj

set_option autoImplicit false

private theorem two_mul_det_eq_trace_sq_sub_trace_mul_self {R : Type} [CommRing R] (M : Matrix (Fin 2) (Fin 2) R) :
    2 * M.det = M.trace ^ 2 - (M * M).trace := by
  simp only [Matrix.det_fin_two, Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
  ring

private theorem apply_eq_apply_of_mul_inv_mem_ker {G M : Type} [Group G] [Monoid M] (ρ : G →* M) {σ τ g : G}
    (h : g * τ * g⁻¹ * σ⁻¹ ∈ ρ.ker) : ρ σ = ρ (g * τ * g⁻¹) := by
  rw [MonoidHom.mem_ker] at h
  calc ρ σ = ρ (g * τ * g⁻¹ * σ⁻¹) * ρ σ := by rw [h, one_mul]
    _ = ρ (g * τ * g⁻¹ * σ⁻¹ * σ) := (map_mul ρ _ _).symm
    _ = ρ (g * τ * g⁻¹) := by rw [inv_mul_cancel_right]

private theorem trace_apply_mul_mul_inv_eq {G R : Type} [Group G] [CommRing R] (ρ : G →* Matrix (Fin 2) (Fin 2) R)
    (g τ : G) : (ρ (g * τ * g⁻¹)).trace = (ρ τ).trace := by
  rw [map_mul, map_mul, Matrix.trace_mul_comm, ← mul_assoc, ← map_mul, inv_mul_cancel, map_one, one_mul]

theorem solution
    (p : ℕ) (hp2 : p ≠ 2) (F : Type) [Field F] [CharP F p]
    (ρ₁ ρ₂ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* Matrix (Fin 2) (Fin 2) F)
    (S : Finset ℕ)
    (hdense : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
      ∃ (ℓ : ℕ) (A : ValuationSubring (AlgebraicClosure ℚ))
        (τ g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ),
        ℓ.Prime ∧ ℓ ∉ S ∧ A.LiesOverPrime ℓ ∧ A.IsFrobeniusAt τ ℓ ∧
          g * τ * g⁻¹ * σ⁻¹ ∈ ρ₁.ker ⊓ ρ₂.ker)
    (htr : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∉ S →
      ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
        ∀ τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt τ ℓ →
          (ρ₁ τ).trace = (ρ₂ τ).trace)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    (ρ₁ σ).det = (ρ₂ σ).det := by
  have h2 : (2 : F) ≠ 0 := by
    intro h
    have h' : ((2 : ℕ) : F) = 0 := by exact_mod_cast h
    rcases (Nat.dvd_prime Nat.prime_two).mp ((CharP.cast_eq_zero_iff F p 2).mp h') with h1 | h1
    · exact CharP.char_ne_one F p h1
    · exact hp2 h1
  have htrace : ∀ x : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, (ρ₁ x).trace = (ρ₂ x).trace := by
    intro x
    obtain ⟨ℓ, A, τ, g, hℓ, hS, hA, hτ, hker⟩ := hdense x
    rw [apply_eq_apply_of_mul_inv_mem_ker ρ₁ (Subgroup.mem_inf.mp hker).1,
      apply_eq_apply_of_mul_inv_mem_ker ρ₂ (Subgroup.mem_inf.mp hker).2, trace_apply_mul_mul_inv_eq,
      trace_apply_mul_mul_inv_eq]
    exact htr ℓ hℓ hS A hA τ hτ
  have key : 2 * (ρ₁ σ).det = 2 * (ρ₂ σ).det := by
    rw [two_mul_det_eq_trace_sq_sub_trace_mul_self, two_mul_det_eq_trace_sq_sub_trace_mul_self, ← map_mul,
      ← map_mul, htrace, htrace]
  exact mul_left_cancel₀ h2 key

end S_MonoidHom_det_eq_of_trace_eq_of_exists_isFrobeniusAt_conj
end P2MW
export P2MW.S_MonoidHom_det_eq_of_trace_eq_of_exists_isFrobeniusAt_conj (solution)
