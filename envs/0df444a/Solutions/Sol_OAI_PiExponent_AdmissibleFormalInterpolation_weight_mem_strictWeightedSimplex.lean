-- Prove2me | solution 1 for OAI.PiExponent.AdmissibleFormalInterpolation.weight_mem_strictWeightedSimplex
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T15:50:25.86791+00:00
-- url     : https://prove2.me/submissions/3a7df9f1-bf70-409f-9757-b50ac29b0b3c

import Mathlib
import Definitions.Def_OAI_NumberTheory_PiExponent_Polynomials_SimplexCounting_WeightedDomains

open scoped BigOperators
theorem solution
    {m : ℕ} (v0 : ℝ) (u : Fin m → ℝ) (H : ℝ)
    (hv0 : 0 < v0) (hu : ∀ i, 0 < u i) (hH : 0 < H)
    (a : Fin (m + 1) → ℕ)
    (ha : (∑ i, Fin.cases v0 u i * (a i : ℝ)) < H) :
    a ∈ OAI.PiExponent.strictWeightedSimplex (Fin.cases v0 u) H := by
  have hw : ∀ i, 0 < (Fin.cases v0 u i : ℝ) := by
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa using hv0
    · simpa using hu j
  unfold OAI.PiExponent.strictWeightedSimplex OAI.PiExponent.realWeightedSimplex
  simp only [Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_range]
  refine ⟨⟨fun i => ?_, ha.le⟩, ha⟩
  have h1 : (Fin.cases v0 u i : ℝ) * (a i : ℝ) ≤ ∑ j, (Fin.cases v0 u j : ℝ) * (a j : ℝ) :=
    Finset.single_le_sum (fun j _ => mul_nonneg (hw j).le (Nat.cast_nonneg _)) (Finset.mem_univ i)
  have h2 : (a i : ℝ) ≤ H / (Fin.cases v0 u i : ℝ) := by
    rw [le_div_iff₀ (hw i)]; linarith
  have := Nat.le_floor h2
  omega
