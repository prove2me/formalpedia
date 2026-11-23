-- Prove2me | solution 1 for GlobalTheory.PerronPsi.far_term
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:44:05.21197+00:00
-- url     : https://prove2.me/submissions/9fd9cbd7-3b9f-4251-8fbd-71c81722b8a1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_TruncatedPerronKernel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_TruncatedPerronPsi
import Theorems.Thm_GlobalTheory_PerronPsi_half_le_log

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory
open GlobalTheory GlobalTheory.PerronPsi
namespace GlobalTheory.PerronPsi
theorem _root_.solution {u T C E : ℝ} {n : ℕ} (hu : 2 ≤ u) (hT : 0 < T) (hn : 0 < n) (hC : 0 ≤ C)
    (hE : 0 ≤ E) (h : E * (T * |Real.log (u / n)|) ≤ C * (u / n) ^ (1 + 1 / Real.log u))
    (hf : (n : ℝ) ≤ u / 2 ∨ 2 * u ≤ n) :
    Real.log n * E ≤ C * (12 * u * Real.log u / T
      * (1 / (n : ℝ) ^ (1 + 1 / (2 * Real.log u)))) := by
  have hu0 : 0 < u := by linarith
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hL := half_le_log hu
  set L := Real.log u with hLdef
  have hL0 : 0 < L := by linarith
  set a := 1 / (2 * L) with ha
  have hlogn : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn)
  have habs : 1 / 2 ≤ |Real.log (u / n)| := by
    rcases hf with hf | hf
    · have h2 : 2 ≤ u / n := by rw [le_div_iff₀ hn0]; linarith
      exact (half_le_log h2).trans (le_abs_self _)
    · have h2 : 2 ≤ n / u := by rw [le_div_iff₀ hu0]; linarith
      have h1 := half_le_log h2
      rw [Real.log_div hu0.ne' hn0.ne', abs_sub_comm, ← Real.log_div hn0.ne' hu0.ne']
      exact h1.trans (le_abs_self _)
  have key1 : E * T ≤ 2 * (C * (u / n) ^ (1 + 1 / L)) := by
    have h1 : E * (T * (1 / 2)) ≤ E * (T * |Real.log (u / n)|) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left habs hT.le) hE
    linarith
  have hQ : 0 < (n : ℝ) ^ a := Real.rpow_pos_of_pos hn0 a
  have hP : 0 < (n : ℝ) ^ (1 + a) := Real.rpow_pos_of_pos hn0 _
  have hexp : 1 + a + a = 1 + 1 / L := by rw [ha]; ring
  have key2 : (u / n) ^ (1 + 1 / L) * ((n : ℝ) ^ (1 + a) * (n : ℝ) ^ a) = u * Real.exp 1 := by
    rw [← Real.rpow_add hn0, hexp, Real.div_rpow hu0.le hn0.le,
      div_mul_cancel₀ _ (Real.rpow_pos_of_pos hn0 _).ne', Real.rpow_add hu0, Real.rpow_one,
      Real.rpow_def_of_pos hu0, ← hLdef, mul_one_div_cancel hL0.ne']
  have key3 : Real.log n ≤ 2 * L * (n : ℝ) ^ a := by
    have h1 := Real.log_le_sub_one_of_pos hQ
    rw [Real.log_rpow hn0] at h1
    have h2 : 2 * L * a = 1 := by rw [ha]; field_simp
    calc Real.log n = 2 * L * (a * Real.log n) := by rw [← mul_assoc, h2, one_mul]
      _ ≤ 2 * L * ((n : ℝ) ^ a - 1) := mul_le_mul_of_nonneg_left h1 (by linarith)
      _ ≤ 2 * L * (n : ℝ) ^ a := by nlinarith
  have he : Real.exp 1 < 3 := by have := Real.exp_one_lt_d9; linarith
  have hgoal : C * (12 * u * L / T * (1 / (n : ℝ) ^ (1 + a)))
      = (12 * C * u * L) / (T * (n : ℝ) ^ (1 + a)) := by
    field_simp
  rw [hgoal, le_div_iff₀ (mul_pos hT hP)]
  have h0 : 0 ≤ C * L * u := mul_nonneg (mul_nonneg hC hL0.le) hu0.le
  calc Real.log n * E * (T * (n : ℝ) ^ (1 + a)) = Real.log n * (E * T) * (n : ℝ) ^ (1 + a) := by ring
    _ ≤ (2 * L * (n : ℝ) ^ a) * (2 * (C * (u / n) ^ (1 + 1 / L))) * (n : ℝ) ^ (1 + a) := by
        apply mul_le_mul_of_nonneg_right _ hP.le
        exact mul_le_mul key3 key1 (mul_nonneg hE hT.le) (mul_nonneg (by linarith) hQ.le)
    _ = 4 * C * L * ((u / n) ^ (1 + 1 / L) * ((n : ℝ) ^ (1 + a) * (n : ℝ) ^ a)) := by ring
    _ = 4 * C * L * (u * Real.exp 1) := by rw [key2]
    _ ≤ 12 * C * u * L := by nlinarith
end GlobalTheory.PerronPsi
