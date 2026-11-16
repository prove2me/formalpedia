-- Prove2me | solution 1 for Kyprianou.Ch01.branchingZeroAbsorbing
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T08:01:29.766874+00:00
-- url     : https://prove2.me/submissions/c5319b19-64ce-49f4-ad40-927bb38c1dea

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Theorems.Thm_Kyprianou_Ch01_pmfLaplaceConvolution

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Kyprianou.Ch01 MeasureTheory Filter Set
open scoped NNReal ENNReal BigOperators
set_option autoImplicit false

/-- An idempotent probability distribution on the natural additive monoid is delta-zero. -/
private theorem pmf_add_idempotent_pure_zero (p : PMF ℕ)
    (hidem : p = p.bind (fun n => p.map (fun m => n + m))) :
    p = PMF.pure 0 := by
  let W : ℕ → ℝ := fun n => Real.exp (-(n : ℝ))
  let G : ℝ := ∑' n : ℕ, (p n).toReal * W n
  have hsum : Summable (fun n : ℕ => (p n).toReal) :=
    ENNReal.summable_toReal p.tsum_coe_ne_top
  have hnonneg (n : ℕ) : 0 ≤ (p n).toReal * W n :=
    mul_nonneg ENNReal.toReal_nonneg (Real.exp_pos _).le
  have hweight (n : ℕ) : W n ≤ 1 := by
    dsimp [W]
    exact Real.exp_le_one_iff.mpr (by
      have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith)
  have hle (n : ℕ) : (p n).toReal * W n ≤ (p n).toReal :=
    mul_le_of_le_one_right ENNReal.toReal_nonneg (hweight n)
  have hsumW : Summable (fun n : ℕ => (p n).toReal * W n) :=
    Summable.of_nonneg_of_le hnonneg hle hsum
  obtain ⟨n, hn⟩ := p.support_nonempty
  have hnpos : 0 < (p n).toReal :=
    ENNReal.toReal_pos ((p.mem_support_iff n).mp hn) (p.apply_ne_top n)
  have hGpos : 0 < G := by
    exact hsumW.tsum_pos hnonneg n
      (mul_pos hnpos (Real.exp_pos _))
  have hId : G = G * G := by
    have h := Kyprianou.Ch01.pmfLaplaceConvolution p p 1 (by norm_num)
    rw [← hidem] at h
    simpa [G, W] using h
  have hGone : G = 1 := by nlinarith
  have hsum1 : (∑' n : ℕ, (p n).toReal) = 1 := by
    rw [← ENNReal.tsum_toReal_eq (fun n => p.apply_ne_top n)]
    simp
  have hzero (n : ℕ) (hn : 0 < n) : p n = 0 := by
    by_contra hne
    have hp : 0 < (p n).toReal :=
      ENNReal.toReal_pos hne (p.apply_ne_top n)
    have hexp : W n < 1 := by
      dsimp [W]
      apply Real.exp_lt_one_iff.mpr
      have hh : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
      linarith
    have hlt : (p n).toReal * W n < (p n).toReal := by
      nlinarith [mul_lt_mul_of_pos_left hexp hp]
    have hltSum := Summable.tsum_lt_tsum_of_nonneg
      hnonneg hle hlt hsum
    dsimp [G] at hGone hGpos
    linarith
  have hp0 : p 0 = 1 := by
    have h : (∑' n, p n) = p 0 :=
      tsum_eq_single 0 (by
        intro n hn
        exact hzero n (Nat.pos_of_ne_zero hn))
    rw [p.tsum_coe] at h
    exact h.symm
  apply PMF.ext
  intro n
  by_cases hn : n = 0
  · subst n
    simp [PMF.pure_apply, hp0]
  · have hpn := hzero n (Nat.pos_of_ne_zero hn)
    simp [PMF.pure_apply, hn, hpn]

theorem solution
    (law : PopulationLaws) (hbranch : HasBranchingProperty law) :
    ∀ t : ℝ≥0, law 0 t = PMF.pure 0 := by
  intro t
  apply pmf_add_idempotent_pure_zero
  simpa only [zero_add] using hbranch 0 0 t
