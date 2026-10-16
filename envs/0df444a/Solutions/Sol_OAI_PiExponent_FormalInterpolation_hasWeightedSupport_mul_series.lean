-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.hasWeightedSupport_mul_series
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-16T06:28:40.208568+00:00
-- url     : https://prove2.me/submissions/85c55305-e003-4b17-b679-55db1f8d896e

import Definitions.Def_OAI_PiExponent_WeightedSupport
import Mathlib.Tactic.Ring

open OAI.PiExponent.FormalInterpolation
open scoped BigOperators

theorem solution {m : ℕ} (v : Fin (m + 1) → ℝ) (A B : ℝ)
    (F G : MvPowerSeries (Fin (m + 1)) ℂ)
    (hF : hasWeightedSupport v A F) (hG : hasWeightedSupport v B G) :
    hasWeightedSupport v (A + B) (F * G) := by
  classical
  intro b hb
  rw [MvPowerSeries.coeff_mul] at hb
  have hex : ∃ p ∈ Finset.antidiagonal (OAI.PiExponent.InterpolationMatrix.exponentVector b),
      MvPowerSeries.coeff p.1 F * MvPowerSeries.coeff p.2 G ≠ 0 := by
    by_contra h
    push_neg at h
    exact hb (Finset.sum_eq_zero fun p hp => h p hp)
  obtain ⟨p, hp, hprod⟩ := hex
  have hleft : MvPowerSeries.coeff p.1 F ≠ 0 := left_ne_zero_of_mul hprod
  have hright : MvPowerSeries.coeff p.2 G ≠ 0 := right_ne_zero_of_mul hprod
  let b₁ : Fin (m + 1) → ℕ := fun i => p.1 i
  let b₂ : Fin (m + 1) → ℕ := fun i => p.2 i
  have hidx₁ : OAI.PiExponent.InterpolationMatrix.exponentVector b₁ = p.1 := by
    ext i
    simp [b₁, OAI.PiExponent.InterpolationMatrix.exponentVector]
  have hidx₂ : OAI.PiExponent.InterpolationMatrix.exponentVector b₂ = p.2 := by
    ext i
    simp [b₂, OAI.PiExponent.InterpolationMatrix.exponentVector]
  have hFne : MvPowerSeries.coeff (OAI.PiExponent.InterpolationMatrix.exponentVector b₁) F ≠ 0 := by
    rw [hidx₁]
    exact hleft
  have hGne : MvPowerSeries.coeff (OAI.PiExponent.InterpolationMatrix.exponentVector b₂) G ≠ 0 := by
    rw [hidx₂]
    exact hright
  have hFbound := hF b₁ hFne
  have hGbound := hG b₂ hGne
  have hsum : p.1 + p.2 = OAI.PiExponent.InterpolationMatrix.exponentVector b :=
    Finset.mem_antidiagonal.mp hp
  have hcoord : ∀ i, b i = b₁ i + b₂ i := by
    intro i
    have hi := congrArg (fun d : (Fin (m + 1) →₀ ℕ) => d i) hsum
    simpa [b₁, b₂, OAI.PiExponent.InterpolationMatrix.exponentVector] using hi.symm
  calc
    A + B ≤ (∑ i, (b₁ i : ℝ) * v i) + ∑ i, (b₂ i : ℝ) * v i := add_le_add hFbound hGbound
    _ = ∑ i, (b i : ℝ) * v i := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      rw [hcoord i]
      rw [Nat.cast_add]
      ring