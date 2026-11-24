-- Prove2me | solution 1 for GlobalTheory.RootEx.ChainLattice.exists_smul_mem
-- status  : ACCEPTED   (prove)
-- author  : @sockpaprika
-- created : 2026-11-24T14:00:48.028738+00:00
-- url     : https://prove2.me/submissions/044bb745-99b4-4c92-b615-5cbbbb3228d5

import Mathlib

open Submodule

theorem solution {R K V : Type} [CommRing R] [IsDomain R] [Field K] [Algebra R K]
    [IsFractionRing R K] [AddCommGroup V] [Module R V] [Module K V] [IsScalarTower R K V]
    (M : Submodule R V) {v : V} (hv : v ∈ Submodule.span K (M : Set V)) :
    ∃ a : R, a ≠ 0 ∧ a • v ∈ M := by
  refine Submodule.span_induction (p := fun x _ => ∃ a : R, a ≠ 0 ∧ a • x ∈ M) ?_ ?_ ?_ ?_ hv
  · intro x hx
    exact ⟨1, one_ne_zero, by simpa using hx⟩
  · exact ⟨1, one_ne_zero, by simp⟩
  · intro x y hx hy ihx ihy
    obtain ⟨a, ha0, hav⟩ := ihx
    obtain ⟨b, hb0, hbv⟩ := ihy
    refine ⟨a * b, mul_ne_zero ha0 hb0, ?_⟩
    have : (a * b) • (x + y) = b • (a • x) + a • (b • y) := by
      rw [smul_add, mul_smul, mul_smul, smul_comm a b x]
    rw [this]
    exact M.add_mem (M.smul_mem b hav) (M.smul_mem a hbv)
  · intro c x hx ih
    obtain ⟨a, ha0, hav⟩ := ih
    by_cases hc0 : c = 0
    · subst hc0
      exact ⟨1, one_ne_zero, by simp⟩
    · obtain ⟨p, q, hq, hc⟩ := IsFractionRing.div_surjective R c
      have hq0 : q ≠ 0 := by rwa [mem_nonZeroDivisors_iff_ne_zero] at hq
      have hqK : algebraMap R K q ≠ 0 := by
        intro hz
        apply hq0
        exact IsFractionRing.injective R K (by rw [map_zero]; exact hz)
      refine ⟨a * q, mul_ne_zero ha0 hq0, ?_⟩
      have hcalc : algebraMap R K (a * q) * c = algebraMap R K (a * p) := by
        rw [← hc, map_mul]
        field_simp [hqK]
        rw [← map_mul]
      have : (a * q) • (c • x) = p • (a • x) := by
        calc (a * q) • (c • x)
            = algebraMap R K (a * q) • (c • x) := by rw [algebraMap_smul]
          _ = (algebraMap R K (a * q) * c) • x := by rw [smul_smul]
          _ = algebraMap R K (a * p) • x := by rw [hcalc]
          _ = (a * p) • x := by rw [algebraMap_smul]
          _ = p • (a • x) := by rw [mul_comm a p, mul_smul]
      rw [this]
      exact M.smul_mem p hav