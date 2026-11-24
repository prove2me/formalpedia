-- Prove2me | solution 1 for GlobalTheory.DeterminantSimpLemma.main
-- status  : ACCEPTED   (prove)
-- author  : @sockpaprika
-- created : 2026-11-24T14:17:54.221527+00:00
-- url     : https://prove2.me/submissions/2e3f84a1-0258-44b2-9086-96f9d84a92c4

import Mathlib

open Submodule

theorem solution {K : Type} [inst : Field K] [NumberField K] {n : ℕ}
    {M : Submodule (NumberField.RingOfIntegers K) (Fin n → K)} {x : Fin n → K} :
    x ∈ Submodule.span K (↑M : Set (Fin n → K)) →
      ∃ (d : NumberField.RingOfIntegers K), d ≠ (0 : NumberField.RingOfIntegers K) ∧ d • x ∈ M := by
  intro hx
  refine Submodule.span_induction
    (p := fun y _ => ∃ d : NumberField.RingOfIntegers K, d ≠ 0 ∧ d • y ∈ M) ?_ ?_ ?_ ?_ hx
  · intro y hy
    exact ⟨1, one_ne_zero, by simpa using hy⟩
  · exact ⟨1, one_ne_zero, by simp⟩
  · intro y z hy hz ihy ihz
    obtain ⟨a, ha0, hav⟩ := ihy
    obtain ⟨b, hb0, hbv⟩ := ihz
    refine ⟨a * b, mul_ne_zero ha0 hb0, ?_⟩
    have : (a * b) • (y + z) = b • (a • y) + a • (b • z) := by
      rw [smul_add, mul_smul, mul_smul, smul_comm a b y]
    rw [this]
    exact M.add_mem (M.smul_mem b hav) (M.smul_mem a hbv)
  · intro c y hy ih
    obtain ⟨a, ha0, hav⟩ := ih
    by_cases hc0 : c = 0
    · subst hc0
      exact ⟨1, one_ne_zero, by simp⟩
    · obtain ⟨p, q, hq, hc⟩ := IsFractionRing.div_surjective (NumberField.RingOfIntegers K) c
      have hq0 : q ≠ 0 := by rwa [mem_nonZeroDivisors_iff_ne_zero] at hq
      have hqK : algebraMap (NumberField.RingOfIntegers K) K q ≠ 0 := by
        intro hz
        apply hq0
        exact IsFractionRing.injective (NumberField.RingOfIntegers K) K (by rw [map_zero]; exact hz)
      refine ⟨a * q, mul_ne_zero ha0 hq0, ?_⟩
      have hcalc : algebraMap (NumberField.RingOfIntegers K) K (a * q) * c =
          algebraMap (NumberField.RingOfIntegers K) K (a * p) := by
        rw [← hc, map_mul]
        field_simp [hqK]
        rw [← map_mul]
      have : (a * q) • (c • y) = p • (a • y) := by
        calc (a * q) • (c • y)
            = algebraMap (NumberField.RingOfIntegers K) K (a * q) • (c • y) := by rw [algebraMap_smul]
          _ = (algebraMap (NumberField.RingOfIntegers K) K (a * q) * c) • y := by rw [smul_smul]
          _ = algebraMap (NumberField.RingOfIntegers K) K (a * p) • y := by rw [hcalc]
          _ = (a * p) • y := by rw [algebraMap_smul]
          _ = p • (a • y) := by rw [mul_comm a p, mul_smul]
      rw [this]
      exact M.smul_mem p hav