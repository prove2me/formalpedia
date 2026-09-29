-- Prove2me | solution 1 for Leopoldt.semilocalGaloisAut_comm_of_exponent_two
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-09-27T22:44:40.658994+00:00
-- url     : https://prove2.me/submissions/0bb65efe-83d9-4b25-9c46-d65f882e5f0c

import Theorems.Thm_Leopoldt_galois_aut_mul_comm_of_square_eq_one
import Theorems.Thm_Leopoldt_exists_monoidHom_mulAut_semilocalGaloisAut

open NumberField

theorem solution (p : ℕ) [Fact p.Prime]
    (K : Type*) [Field K] [NumberField K] [IsGalois ℚ K]
    (h : ∀ ρ : K ≃ₐ[ℚ] K, ρ * ρ = 1) (σ τ : K ≃ₐ[ℚ] K) :
    Leopoldt.semilocalGaloisAut p K σ * Leopoldt.semilocalGaloisAut p K τ =
      Leopoldt.semilocalGaloisAut p K τ * Leopoldt.semilocalGaloisAut p K σ := by
  obtain ⟨φ, hφ⟩ := Leopoldt.exists_monoidHom_mulAut_semilocalGaloisAut p K
  calc
    Leopoldt.semilocalGaloisAut p K σ * Leopoldt.semilocalGaloisAut p K τ = φ (σ * τ) := by
      rw [map_mul, hφ σ, hφ τ]
    _ = φ (τ * σ) := by rw [Leopoldt.galois_aut_mul_comm_of_square_eq_one K h σ τ]
    _ = Leopoldt.semilocalGaloisAut p K τ * Leopoldt.semilocalGaloisAut p K σ := by
      rw [map_mul, hφ τ, hφ σ]
