-- Prove2me | solution 1 for NeutrinoDecoherence.dissipator_pauli_expansion
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-26T01:51:51.874058+00:00
-- url     : https://prove2.me/submissions/126fe29a-a274-4352-9a00-07e31da67de5

import Mathlib
import Definitions.Def_NeutrinoDecoherence_Defs

set_option autoImplicit false

open NeutrinoDecoherence Matrix Complex in
theorem solution (a : Matrix (Fin 3) (Fin 3) ℂ) (ha : a.IsHermitian)
    (r₀ r₁ r₂ r₃ : ℝ) :
    dissipator a ((r₀ : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) + (r₁ : ℂ) • pauli 0 +
        (r₂ : ℂ) • pauli 1 + (r₃ : ℂ) • pauli 2) =
      ((2 * ((a 1 0).re * r₂ + (a 2 0).re * r₃ - (a 1 1).re * r₁ - (a 2 2).re * r₁
          + 2 * r₀ * (a 2 1).im) : ℝ) : ℂ) • pauli 0 +
      ((2 * ((a 0 1).re * r₁ + (a 2 1).re * r₃ - (a 0 0).re * r₂ - (a 2 2).re * r₂
          + 2 * r₀ * (a 0 2).im) : ℝ) : ℂ) • pauli 1 +
      ((2 * ((a 0 2).re * r₁ + (a 1 2).re * r₂ - (a 0 0).re * r₃ - (a 1 1).re * r₃
          + 2 * r₀ * (a 1 0).im) : ℝ) : ℂ) • pauli 2 := by
  have hH : ∀ i j, a j i = star (a i j) := fun i j => (ha.apply j i).symm
  have hd : ∀ i, (a i i).im = 0 := by
    intro i
    have h := congrArg Complex.im (hH i i)
    simp at h
    linarith
  have h10 := hH 0 1
  have h20 := hH 0 2
  have h21 := hH 1 2
  have h0 := hd 0
  have h1 := hd 1
  have h2 := hd 2
  have hρ : ((r₀ : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) + (r₁ : ℂ) • pauli 0 +
      (r₂ : ℂ) • pauli 1 + (r₃ : ℂ) • pauli 2) =
      !![(r₀ : ℂ) + r₃, r₁ - I * r₂; r₁ + I * r₂, r₀ - r₃] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [pauli] <;> ring
  rw [hρ]
  simp only [dissipator, Fin.sum_univ_three, pauli]
  ext i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    simp [h10, h20, h21, h0, h1, h2] <;> ring
