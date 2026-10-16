-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.hasWeightedSupport_mul_closure
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-16T06:40:27.114982+00:00
-- url     : https://prove2.me/submissions/9b928d21-cd57-41e7-85bf-bed8dfdf07c5

import Definitions.Def_OAI_PiExponent_WeightedSupport

open OAI.PiExponent.FormalInterpolation

theorem solution {m : ℕ} (v : Fin (m + 1) → ℝ) (B : ℝ)
    (F G : MvPowerSeries (Fin (m + 1)) ℂ)
    (hF : hasWeightedSupport v 0 F) (hG : hasWeightedSupport v B G) :
    hasWeightedSupport v B (F * G) := by
  classical
  intro b hb
  let n := OAI.PiExponent.InterpolationMatrix.exponentVector b
  have hcoeff : MvPowerSeries.coeff n (F * G) ≠ 0 := hb
  rw [MvPowerSeries.coeff_mul] at hcoeff
  obtain ⟨p, hp, hprod⟩ := Finset.exists_ne_zero_of_sum_ne_zero hcoeff
  have hp_factors :
      MvPowerSeries.coeff p.1 F ≠ 0 ∧ MvPowerSeries.coeff p.2 G ≠ 0 :=
    mul_ne_zero_iff.mp hprod
  have hp_add : p.1 + p.2 = n := Finset.mem_antidiagonal.mp hp
  have hF_exp :
      OAI.PiExponent.InterpolationMatrix.exponentVector (fun i => p.1 i) = p.1 := by
    ext i
    simp [OAI.PiExponent.InterpolationMatrix.exponentVector]
  have hG_exp :
      OAI.PiExponent.InterpolationMatrix.exponentVector (fun i => p.2 i) = p.2 := by
    ext i
    simp [OAI.PiExponent.InterpolationMatrix.exponentVector]
  have hF_bound : 0 ≤ ∑ i, (p.1 i : ℝ) * v i :=
    hF (fun i => p.1 i) (by simpa only [hF_exp] using hp_factors.1)
  have hG_bound : B ≤ ∑ i, (p.2 i : ℝ) * v i :=
    hG (fun i => p.2 i) (by simpa only [hG_exp] using hp_factors.2)
  have hweight :
      (∑ i, (p.1 i : ℝ) * v i) + (∑ i, (p.2 i : ℝ) * v i) =
        ∑ i, (b i : ℝ) * v i := by
    have h := congrArg
      (fun q : Fin (m + 1) →₀ ℕ => ∑ i, (q i : ℝ) * v i) hp_add
    simpa [n, OAI.PiExponent.InterpolationMatrix.exponentVector,
      Finsupp.add_apply, Nat.cast_add, add_mul, Finset.sum_add_distrib] using h
  linarith