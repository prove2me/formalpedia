-- Prove2me | solution 1 for Leopoldt.semilocalGaloisAut_sq_of_involution
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-09-27T22:33:45.253614+00:00
-- url     : https://prove2.me/submissions/457c92e5-439f-4170-9182-76698471cd96

import Theorems.Thm_Leopoldt_exists_monoidHom_mulAut_semilocalGaloisAut

open NumberField

theorem solution (p : ℕ) [Fact p.Prime]
    (K : Type*) [Field K] [NumberField K] (σ : K ≃ₐ[ℚ] K) (hσ : σ * σ = 1) :
    Leopoldt.semilocalGaloisAut p K σ * Leopoldt.semilocalGaloisAut p K σ = 1 := by
  obtain ⟨φ, hφ⟩ := Leopoldt.exists_monoidHom_mulAut_semilocalGaloisAut p K
  calc
    Leopoldt.semilocalGaloisAut p K σ * Leopoldt.semilocalGaloisAut p K σ = φ (σ * σ) := by
      rw [map_mul, hφ σ]
    _ = 1 := by rw [hσ, map_one]
