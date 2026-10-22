-- Prove2me | solution 1 for KalaiVempala.Lazy.lemma_3_2
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T08:10:48.635266+00:00
-- url     : https://prove2.me/submissions/ec17e021-9c6c-44e6-9cbd-b59cadad6854

import Mathlib
import Definitions.Def_OracleRO_ApproxFPL_FPL
import Definitions.Def_KalaiVempala_Lazy_Setting

set_option autoImplicit false
open MeasureTheory OracleRO.ApproxFPL

lemma kvl_prod_ge {ι : Type*} (s : Finset ι) (a : ι → ℝ) (c : ι → ℝ)
    (h0 : ∀ i ∈ s, 0 ≤ a i) (h1 : ∀ i ∈ s, a i ≤ 1) (hc : ∀ i ∈ s, 1 - a i ≤ c i) :
    1 - ∑ i ∈ s, c i ≤ ∏ i ∈ s, a i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [Finset.sum_insert hj, Finset.prod_insert hj]
    have ih' := ih (fun i hi => h0 i (Finset.mem_insert_of_mem hi))
      (fun i hi => h1 i (Finset.mem_insert_of_mem hi))
      (fun i hi => hc i (Finset.mem_insert_of_mem hi))
    have hj0 := h0 j (Finset.mem_insert_self j s)
    have hj1 := h1 j (Finset.mem_insert_self j s)
    have hjc := hc j (Finset.mem_insert_self j s)
    have hS : 0 ≤ ∑ i ∈ s, c i := by
      apply Finset.sum_nonneg
      intro i hi
      have := h1 i (Finset.mem_insert_of_mem hi)
      have := hc i (Finset.mem_insert_of_mem hi)
      linarith
    nlinarith [mul_le_mul_of_nonneg_left ih' hj0]

theorem solution {n : ℕ} (ε : ℝ) (hε : 0 < ε) (v : Fin n → ℝ) :
    ENNReal.ofReal (1 - ε * ∑ i, |v i|) ≤
      perturbLaw n ε {x | x - v ∈ Set.Icc (0 : Fin n → ℝ) (fun _ => ε⁻¹)} := by
  unfold perturbLaw
  rw [ProbabilityTheory.cond_apply measurableSet_Icc]
  have hset : {x : Fin n → ℝ | x - v ∈ Set.Icc (0 : Fin n → ℝ) (fun _ => ε⁻¹)}
      = Set.Icc v (v + fun _ => ε⁻¹) := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_Icc, Pi.le_def, Pi.sub_apply, Pi.zero_apply,
      Pi.add_apply, sub_nonneg]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, fun i => by linarith [h2 i]⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, fun i => by linarith [h2 i]⟩
  rw [hset, Set.Icc_inter_Icc, Real.volume_Icc_pi, Real.volume_Icc_pi]
  have hmin : ∀ i, ENNReal.ofReal (((fun _ => ε⁻¹) ⊓ (v + fun _ => ε⁻¹) : Fin n → ℝ) i - ((0 : Fin n → ℝ) ⊔ v) i)
      = ENNReal.ofReal ε⁻¹ * ENNReal.ofReal (1 - ε * |v i|) := by
    intro i
    simp only [Pi.inf_apply, Pi.sup_apply, Pi.add_apply, Pi.zero_apply]
    rw [← ENNReal.ofReal_mul (inv_nonneg.2 hε.le)]
    congr 1
    rcases le_total 0 (v i) with h | h
    · rw [min_eq_left (by linarith), max_eq_right h, abs_of_nonneg h]; field_simp; try ring
    · rw [min_eq_right (by linarith), max_eq_left h, abs_of_nonpos h]; field_simp; try ring
  have h0 : ∀ i : Fin n, ENNReal.ofReal (ε⁻¹ - (0 : Fin n → ℝ) i) = ENNReal.ofReal ε⁻¹ := by
    intro i; simp
  simp only [h0, hmin, Finset.prod_mul_distrib]
  have hne0 : (∏ i : Fin n, ENNReal.ofReal ε⁻¹) ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    intro i _
    simpa using hε
  have hnet : (∏ i : Fin n, ENNReal.ofReal ε⁻¹) ≠ ⊤ :=
    ENNReal.prod_ne_top (fun i _ => ENNReal.ofReal_ne_top)
  rw [ENNReal.inv_mul_cancel_left hne0 hnet]
  set a : Fin n → ℝ := fun i => max (1 - ε * |v i|) 0 with ha
  have hrw : ∀ i, ENNReal.ofReal (1 - ε * |v i|) = ENNReal.ofReal (a i) := by
    intro i
    simp only [ha]
    rw [ENNReal.ofReal_max]; simp
  simp only [hrw]
  rw [← ENNReal.ofReal_prod_of_nonneg (fun i _ => le_max_right _ _)]
  apply ENNReal.ofReal_le_ofReal
  have := kvl_prod_ge (Finset.univ : Finset (Fin n)) a (fun i => ε * |v i|)
    (fun i _ => le_max_right _ _)
    (fun i _ => max_le (by nlinarith [abs_nonneg (v i)]) zero_le_one)
    (fun i _ => by
      simp only [ha]
      rcases le_total 0 (1 - ε * |v i|) with h | h
      · rw [max_eq_left h]; linarith
      · rw [max_eq_right h]; linarith)
  rw [← Finset.mul_sum] at this
  exact this
