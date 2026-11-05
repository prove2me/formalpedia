-- Prove2me | solution 1 for LL_Decomp1543a.inner_l_sum
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-04T10:05:27.100514+00:00
-- url     : https://prove2.me/submissions/0712cf0d-afdc-4c9a-9917-2b6e25896a70

import Mathlib
import Definitions.Def_LL_Decomp1543a_nint
import Definitions.Def_LL_Decomp1543a_minK
import Definitions.Def_LL_Decomp1543a_Dioph
import Definitions.Def_LL_Decomp1543a_lRange
import Definitions.Def_LL_Decomp1543a_WCLemma2

open Real Finset ArithmeticFunction

namespace VaAAux
open LL_Decomp1543a

theorem minK_nonneg (X : ℝ) (hX : 0 ≤ X) (θ : ℝ) : 0 ≤ minK X θ := by
  unfold minK
  split_ifs
  · exact hX
  · exact le_min hX (div_nonneg zero_le_one (mul_nonneg zero_le_two (abs_nonneg _)))

end VaAAux

open LL_Decomp1543a in
theorem solution (hwc : WCLemma2) (α : ℝ) (a : ℤ) (q : ℕ) (hD : Dioph α a q) (N : ℕ)
    (U Y X : ℝ) (hU : 0 ≤ U) (hX : 0 < X) (m : ℕ) :
    ∑ l ∈ lRange N U Y, minK X (α * ((m : ℝ) - l)) ≤
      ((((⌊Y⌋₊ - ⌊U⌋₊) / q : ℕ) : ℝ) + 1) * (5 * X + q * Real.log q) := by
  have hq : 1 ≤ q := hD.1
  have hlogq : 0 ≤ Real.log q := Real.log_nonneg (by exact_mod_cast hq)
  by_cases hY : ⌊U⌋₊ < ⌊Y⌋₊
  · set Y' := ⌊Y⌋₊ - ⌊U⌋₊ with hY'
    have hY1 : 1 ≤ Y' := by omega
    have hw := hwc α a q hD X hX Y' ((m : ℤ) - ⌊Y⌋₊ - 1) hY1
    calc ∑ l ∈ lRange N U Y, minK X (α * ((m : ℝ) - l))
        = ∑ n ∈ (lRange N U Y).image (fun l : ℕ => (m : ℤ) - l), minK X (α * (n : ℝ)) := by
          rw [sum_image]
          · apply sum_congr rfl
            intro l _
            push_cast
            rfl
          · intro x _ y _ h
            simp only at h
            omega
      _ ≤ ∑ n ∈ Ioc ((m : ℤ) - ⌊Y⌋₊ - 1) (((m : ℤ) - ⌊Y⌋₊ - 1) + (Y' : ℕ)), minK X (α * (n : ℝ)) := by
          apply sum_le_sum_of_subset_of_nonneg
          · intro n hn
            obtain ⟨l, hl, rfl⟩ := mem_image.1 hn
            unfold lRange at hl
            simp only [mem_filter, mem_Icc] at hl
            have h1 : ⌊U⌋₊ < l := (Nat.floor_lt hU).2 hl.2.1
            have h2 : l ≤ ⌊Y⌋₊ := Nat.le_floor hl.2.2
            rw [mem_Ioc]
            omega
          · intro n _ _
            exact VaAAux.minK_nonneg X hX.le _
      _ ≤ _ := hw
  · have : lRange N U Y = ∅ := by
      ext l
      simp only [lRange, mem_filter, mem_Icc, Finset.notMem_empty, iff_false]
      rintro ⟨_, h1, h2⟩
      have h3 : ⌊U⌋₊ < l := (Nat.floor_lt hU).2 h1
      have h4 : l ≤ ⌊Y⌋₊ := Nat.le_floor h2
      omega
    rw [this, sum_empty]
    exact mul_nonneg (by positivity)
      (add_nonneg (by positivity) (mul_nonneg (Nat.cast_nonneg q) hlogq))
