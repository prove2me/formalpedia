-- Prove2me | solution 1 for Kyprianou.Ch04.kw47_esscher_H_grid_variation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T19:56:52.558504+00:00
-- url     : https://prove2.me/submissions/a8a56c37-6b34-403e-a3cd-fe7dfdf7c67f

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_kw47_monotone_exp_unit_variation
import Theorems.Thm_Kyprianou_Ch04_kw47_positive_monotone_grid_variation
import Theorems.Thm_Kyprianou_Ch04_kw47_product_grid_variation_bound
import Theorems.Thm_AvramDividend_Classical_runningSup_isDividendStrategy
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_path_nonneg
open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Uniform finite-horizon deterministic variation of the
continuous Kella-Whitt Esscher running-maximum factor. -/
theorem solution
    {Ω : Type} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {F : Filtration NNReal mΩ}
    (L : SpectrallyNegativeLevy P F)
    (alpha : Real) (hAlpha : 0 ≤ alpha)
    (T : NNReal) (u : Nat → NNReal) (hu : Monotone u)
    (hT : ∀ i, u i ≤ T) (n : Nat) (w : Ω) :
    (∑ i ∈ Finset.range n,
       |Real.exp (-alpha * runningSup L (u (i+1)) w +
           L.ψ alpha * (u (i+1) : Real)) -
        Real.exp (-alpha * runningSup L (u i) w +
           L.ψ alpha * (u i : Real))|)
      ≤ 2 * Real.exp (|L.ψ alpha| * (T : Real)) := by
  let A : Nat → Real :=
    fun i => Real.exp (-alpha * runningSup L (u i) w)
  let B : Nat → Real :=
    fun i => Real.exp (L.ψ alpha * (u i : Real))
  let C : Real := Real.exp (|L.ψ alpha| * (T : Real))
  have hUmono : Monotone (fun r : NNReal => runningSup L r w) :=
    (runningSup_isDividendStrategy L).2.1 w
  have hUnonneg (r : NNReal) : 0 ≤ runningSup L r w :=
    dividendStrategy_path_nonneg (runningSup L)
      (runningSup_isDividendStrategy L) w r
  have hA (i : Nat) : |A i| ≤ 1 := by
    have hExpArg : -alpha * runningSup L (u i) w ≤ 0 := by
      nlinarith [mul_nonneg hAlpha (hUnonneg (u i))]
    have he : Real.exp (-alpha * runningSup L (u i) w) ≤
        Real.exp 0 := Real.exp_le_exp.mpr hExpArg
    simpa only [A, abs_of_pos (Real.exp_pos _), Real.exp_zero] using he
  have hB (i : Nat) : |B i| ≤ C := by
    have hUi : 0 ≤ (u i : Real) := NNReal.coe_nonneg _
    have hUiT : (u i : Real) ≤ (T : Real) := by exact_mod_cast hT i
    have h1 : L.ψ alpha * (u i : Real) ≤
        |L.ψ alpha| * (u i : Real) :=
      mul_le_mul_of_nonneg_right (le_abs_self _) hUi
    have h2 : |L.ψ alpha| * (u i : Real) ≤
        |L.ψ alpha| * (T : Real) :=
      mul_le_mul_of_nonneg_left hUiT (abs_nonneg _)
    have ht : B i ≤ C :=
      Real.exp_le_exp.mpr (h1.trans h2)
    simpa only [B, C, abs_of_pos (Real.exp_pos _)] using ht
  have hBmono : Monotone B ∨ Antitone B := by
    by_cases hp : 0 ≤ L.ψ alpha
    · left
      intro i j hij
      apply Real.exp_le_exp.mpr
      have ht : (u i : Real) ≤ (u j : Real) := by exact_mod_cast hu hij
      exact mul_le_mul_of_nonneg_left ht hp
    · right
      intro i j hij
      apply Real.exp_le_exp.mpr
      have ht : (u i : Real) ≤ (u j : Real) := by exact_mod_cast hu hij
      exact mul_le_mul_of_nonpos_left ht (le_of_not_ge hp)
  have hVA : (∑ i ∈ Finset.range n,
      |A (i+1) - A i|) ≤ 1 := by
    exact Kyprianou.Ch04.kw47_monotone_exp_unit_variation
      (fun r => runningSup L r w) hUmono hUnonneg
      alpha hAlpha u hu n
  have hVB : (∑ i ∈ Finset.range n,
      |B (i+1) - B i|) ≤ C :=
    Kyprianou.Ch04.kw47_positive_monotone_grid_variation
      B n C hBmono (Real.exp_nonneg _) (Real.exp_nonneg _)
      ((le_abs_self (B 0)).trans (hB 0))
      ((le_abs_self (B n)).trans (hB n))
  have hprod := Kyprianou.Ch04.kw47_product_grid_variation_bound
    A B C n (Real.exp_nonneg _) hA hB hVA hVB
  calc
    (∑ i ∈ Finset.range n,
       |Real.exp (-alpha * runningSup L (u (i+1)) w +
           L.ψ alpha * (u (i+1) : Real)) -
        Real.exp (-alpha * runningSup L (u i) w +
           L.ψ alpha * (u i : Real))|)
      = ∑ i ∈ Finset.range n,
          |A (i+1) * B (i+1) - A i * B i| := by
          apply Finset.sum_congr rfl
          intro i hi
          simp only [A, B, Real.exp_add]
    _ ≤ 2 * C := hprod
    _ = 2 * Real.exp (|L.ψ alpha| * (T : Real)) := rfl
