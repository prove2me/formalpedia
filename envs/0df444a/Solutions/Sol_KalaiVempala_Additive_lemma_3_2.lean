-- Prove2me | solution 1 for KalaiVempala.Additive.lemma_3_2
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T05:46:57.484474+00:00
-- url     : https://prove2.me/submissions/eff970ef-338a-4cf8-b930-68ac97b5b2aa

import Mathlib
import Definitions.Def_OracleRO_ApproxFPL_FPL
import Definitions.Def_KalaiVempala_Additive_Setting

set_option autoImplicit false
open MeasureTheory OracleRO.ApproxFPL

theorem kva_weierstrass {ι : Type*} (s : Finset ι) (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) :
    1 - ∑ i ∈ s, a i ≤ ∏ i ∈ s, max (1 - a i) 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [Finset.sum_insert hj, Finset.prod_insert hj]
    have hp : 0 ≤ ∏ i ∈ s, max (1 - a i) 0 := Finset.prod_nonneg fun i _ => le_max_right _ _
    have hsum : 0 ≤ ∑ i ∈ s, a i := Finset.sum_nonneg fun i _ => ha i
    by_cases h1 : 1 ≤ a j
    · rw [max_eq_right (by linarith)]
      simp only [zero_mul]
      linarith
    · push Not at h1
      rw [max_eq_left (by linarith)]
      nlinarith [mul_nonneg (ha j) hsum]

theorem solution {n : ℕ} (ε : ℝ) (hε : 0 < ε) (v : Fin n → ℝ) :
    ENNReal.ofReal (1 - ε * ∑ i, |v i|) ≤
      perturbLaw n ε {x | x - v ∈ Set.Icc (0 : Fin n → ℝ) (fun _ => ε⁻¹)} := by
  set C : Set (Fin n → ℝ) := Set.Icc (0 : Fin n → ℝ) (fun _ => ε⁻¹) with hC
  have hCm : MeasurableSet C := measurableSet_Icc
  have hr : 0 < ε⁻¹ := inv_pos.mpr hε
  have hvolC : volume C = ENNReal.ofReal ε⁻¹ ^ n := by
    rw [hC, Real.volume_Icc_pi]
    simp
  have hinter : C ∩ {x | x - v ∈ C} = Set.Icc (fun i => max 0 (v i)) (fun i => min ε⁻¹ (v i + ε⁻¹)) := by
    ext x
    simp only [hC, Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_Icc, Pi.le_def]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3, h4⟩
      refine ⟨fun i => max_le (h1 i) ?_, fun i => le_min (h2 i) ?_⟩
      · have := h3 i; simp at this; linarith
      · have := h4 i; simp at this; linarith
    · rintro ⟨h1, h2⟩
      refine ⟨⟨fun i => le_trans (le_max_left _ _) (h1 i), fun i => le_trans (h2 i) (min_le_left _ _)⟩, fun i => ?_, fun i => ?_⟩
      · have := le_trans (le_max_right _ _) (h1 i); simp; linarith
      · have := le_trans (h2 i) (min_le_right _ _); simp; linarith
  have hvolI : volume (C ∩ {x | x - v ∈ C}) =
      ENNReal.ofReal ε⁻¹ ^ n * ∏ i, ENNReal.ofReal (1 - ε * |v i|) := by
    have e : ENNReal.ofReal ε⁻¹ ^ n = ∏ i : Fin n, ENNReal.ofReal ε⁻¹ := by simp
    rw [hinter, Real.volume_Icc_pi, e, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← ENNReal.ofReal_mul hr.le]
    congr 1
    have : min ε⁻¹ (v i + ε⁻¹) - max 0 (v i) = ε⁻¹ - |v i| := by
      rcases le_total 0 (v i) with h | h
      · rw [abs_of_nonneg h, max_eq_right h, min_eq_left (by linarith)]
      · rw [abs_of_nonpos h, max_eq_left h, min_eq_right (by linarith)]; ring
    rw [this]
    field_simp
  have hne0 : ENNReal.ofReal ε⁻¹ ^ n ≠ 0 := pow_ne_zero _ (by simpa using hr)
  have hnetop : ENNReal.ofReal ε⁻¹ ^ n ≠ ⊤ := ENNReal.pow_ne_top ENNReal.ofReal_ne_top
  have hcond : perturbLaw n ε {x | x - v ∈ C} = ∏ i, ENNReal.ofReal (1 - ε * |v i|) := by
    unfold perturbLaw
    rw [← hC, ProbabilityTheory.cond_apply hCm, hvolC, hvolI, ENNReal.inv_mul_cancel_left hne0 hnetop]
  rw [hcond]
  have h1 : 1 - ε * ∑ i, |v i| ≤ ∏ i, max (1 - ε * |v i|) 0 := by
    have := kva_weierstrass Finset.univ (fun i => ε * |v i|) (fun i => by positivity)
    simpa [Finset.mul_sum] using this
  calc ENNReal.ofReal (1 - ε * ∑ i, |v i|) ≤ ENNReal.ofReal (∏ i, max (1 - ε * |v i|) 0) :=
        ENNReal.ofReal_le_ofReal h1
    _ = ∏ i, ENNReal.ofReal (max (1 - ε * |v i|) 0) :=
        ENNReal.ofReal_prod_of_nonneg fun i _ => le_max_right _ _
    _ = ∏ i, ENNReal.ofReal (1 - ε * |v i|) := by
        refine Finset.prod_congr rfl fun i _ => ?_
        by_cases h : 1 - ε * |v i| ≤ 0
        · rw [max_eq_right h, ENNReal.ofReal_of_nonpos h]; simp
        · rw [max_eq_left (by linarith)]
