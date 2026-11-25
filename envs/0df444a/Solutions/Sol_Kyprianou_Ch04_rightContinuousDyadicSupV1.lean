-- Prove2me | solution 1 for Kyprianou.Ch04.rightContinuousDyadicSupV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T21:27:49.637655+00:00
-- url     : https://prove2.me/submissions/c8f1bd03-232d-4ce0-86db-49eb09c6266f

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_right_continuous_strict_dyadic_grid_event
open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false

/-- A right-continuous nonnegative path has the same extended supremum as its dyadic samples. -/
theorem solution (f : ℝ≥0 → ℝ) (T : ℝ≥0) (hT : 0 < T)
    (hf : ∀ t, 0 ≤ f t)
    (hr : ∀ t, ContinuousWithinAt f (Ici t) t) :
    (⨆ t : Iic T, ENNReal.ofReal (f t)) =
      ⨆ n : ℕ, ENNReal.ofReal ((Finset.range (2^n+1)).sup'
        Finset.nonempty_range_add_one (fun i => f ((i : ℝ≥0) * T / (2^n : ℝ≥0)))) := by
  classical
  let S : ℝ≥0∞ := ⨆ n : ℕ, ENNReal.ofReal ((Finset.range (2^n+1)).sup'
        Finset.nonempty_range_add_one (fun i => f ((i : ℝ≥0) * T / (2^n : ℝ≥0))))
  refine le_antisymm (iSup_le fun t => ?_) (iSup_le fun n => ?_)
  · change ENNReal.ofReal (f t) ≤ S
    by_cases hS : S = ⊤
    · rw [hS]; exact le_top
    · by_contra h
      have ht : S.toReal < f t := by
        have hh := ENNReal.toReal_lt_toReal hS (ENNReal.ofReal_ne_top (r := f t))
        rw [ENNReal.toReal_ofReal (hf t)] at hh
        exact hh.mpr (lt_of_not_ge h)
      have hneg : ∀ r, ContinuousWithinAt (fun u => -f u) (Ici r) r :=
        fun r => (hr r).neg
      obtain ⟨n,k,hk⟩ := (AvramDividend.Classical.avram_ws01e_b_right_continuous_strict_dyadic_grid_event
        (fun u => -f u) T hT hneg (-S.toReal)).mp ⟨t,t.2,by linarith⟩
      have heq : (k.val : ℝ≥0) / (2 : ℝ≥0)^n * T =
          (k.val : ℝ≥0) * T / (2^n : ℝ≥0) := by rw [div_mul_eq_mul_div]
      rw [heq] at hk
      have hle : ENNReal.ofReal (f ((k.val : ℝ≥0) * T / (2^n : ℝ≥0))) ≤ S :=
        (ENNReal.ofReal_le_ofReal (Finset.le_sup' (f := fun i : ℕ =>
          f ((i : ℝ≥0) * T / (2^n : ℝ≥0))) (Finset.mem_range.mpr k.isLt))).trans
          (le_iSup (fun n : ℕ => ENNReal.ofReal ((Finset.range (2^n+1)).sup'
            Finset.nonempty_range_add_one (fun i => f ((i : ℝ≥0) * T / (2^n : ℝ≥0))))) n)
      have hreal := ENNReal.toReal_mono hS hle
      rw [ENNReal.toReal_ofReal (hf _)] at hreal
      linarith
  · obtain ⟨i,hi,heq⟩ := Finset.exists_mem_eq_sup' (Finset.nonempty_range_add_one (n := 2^n))
      (fun i : ℕ => f ((i : ℝ≥0) * T / (2^n : ℝ≥0)))
    rw [heq]
    have hi' : (i : ℝ≥0) ≤ (2 : ℝ≥0)^n := by
      exact_mod_cast Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have ht : (i : ℝ≥0) * T / (2^n : ℝ≥0) ≤ T := by
      rw [div_le_iff₀ (by positivity)]
      calc (i : ℝ≥0) * T ≤ (2 : ℝ≥0)^n * T :=
            mul_le_mul_of_nonneg_right hi' zero_le
        _ = T * 2^n := mul_comm _ _
    exact le_iSup_of_le ⟨_,ht⟩ le_rfl
