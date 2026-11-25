-- Prove2me | solution 1 for Kyprianou.Ch04.exercise42GridCellIntegralV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T17:49:00.950802+00:00
-- url     : https://prove2.me/submissions/76b98849-2796-49fb-98ae-0ca01f7e7e2b

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_exercise42GridCellFloorRealV1
open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    (t : NNReal) (ht : 0 < t) (U g : NNReal → ℝ)
    (K : NNReal) (hU : LipschitzWith K U)
    (C : ℝ) (hC : 0 ≤ C) (hg : ∀ s : NNReal, s ≤ t → ‖g s‖ ≤ C) :
    let T : ℝ := t
    let V : ℝ → ℝ := fun s => U s.toNNReal
    let D : ℝ → ℝ := deriv V
    let q : ℕ → ℕ → ℝ := fun n i => T * (i : ℝ) / ((n : ℝ) + 2)
    let j : ℕ → ℝ → ℕ := fun n s => ⌊(s / T) * ((n : ℝ) + 2)⌋₊
    let F : ℕ → ℝ → ℝ := fun n s => g (q n (j n s)).toNNReal * D s
    ∀ n : ℕ,
      (∫ s in Icc 0 T, F n s) =
        ∑ i ∈ Finset.range (n + 2),
          g (t * (i : NNReal) / ((n + 2 : ℕ) : NNReal)) *
            (U (t * ((i + 1 : ℕ) : NNReal) / ((n + 2 : ℕ) : NNReal)) -
             U (t * (i : NNReal) / ((n + 2 : ℕ) : NNReal))) := by
  classical
  intro T V D q j F
  have hT : 0 < T := ht
  have hLip : LipschitzWith K V := by
    simpa [V, Function.comp_def] using hU.comp Real.lipschitzWith_toNNReal
  have hAc (a b : ℝ) : AbsolutelyContinuousOnInterval V a b :=
    hLip.lipschitzOnWith.absolutelyContinuousOnInterval
  have hFTC (a b : ℝ) : (∫ x in a..b, D x) = V b - V a :=
    (hAc a b).integral_deriv_eq_sub
  have hq0 (n i : ℕ) : 0 ≤ q n i := by dsimp [q]; positivity
  have hqmono (n : ℕ) : Monotone (q n) := by
    intro i k hik
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left (by exact_mod_cast hik) hT.le) (by positivity)
  have hqfirst (n : ℕ) : q n 0 = 0 := by simp [q]
  have hqlast (n : ℕ) : q n (n + 2) = T := by
    simp [q, Nat.cast_add]
    field_simp
  have hcell (n i : ℕ) (s : ℝ)
      (hs : s ∈ Ico (q n i) (q n (i + 1))) : j n s = i := by
    exact Kyprianou.Ch04.exercise42GridCellFloorRealV1 T hT n i s hs
  have hgrid (n : ℕ) :
      (∫ s in Icc 0 T, F n s) =
        ∑ i ∈ Finset.range (n + 2),
          g (q n i).toNNReal * (V (q n (i + 1)) - V (q n i)) := by
    have hint (i : ℕ) (hi : i < n + 2) :
        IntervalIntegrable (F n) volume (q n i) (q n (i + 1)) := by
      have hle := hqmono n (Nat.le_succ i)
      apply (intervalIntegrable_iff_integrableOn_Ico_of_le hle).2
      rw [integrableOn_congr_fun (g := fun s => g (q n i).toNNReal * D s)
        (fun s hs => by simp only [F, hcell n i s hs]) measurableSet_Ico]
      exact (intervalIntegrable_iff_integrableOn_Ico_of_le hle).1
        ((hAc (q n i) (q n (i + 1))).intervalIntegrable_deriv.const_mul _)
    calc
      (∫ s in Icc 0 T, F n s) = ∫ s in q n 0..q n (n + 2), F n s := by
        rw [hqfirst, hqlast, intervalIntegral.integral_of_le hT.le,
          integral_Icc_eq_integral_Ioc]
      _ = ∑ i ∈ Finset.range (n + 2), ∫ s in q n i..q n (i + 1), F n s :=
        (intervalIntegral.sum_integral_adjacent_intervals hint).symm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i hi
        have hle := hqmono n (Nat.le_succ i)
        rw [intervalIntegral.integral_of_le hle, ← integral_Ico_eq_integral_Ioc]
        calc
          _ = ∫ s in Ico (q n i) (q n (i + 1)), g (q n i).toNNReal * D s := by
            apply setIntegral_congr_fun measurableSet_Ico
            intro s hs
            simp only [F, hcell n i s hs]
          _ = _ := by
            rw [integral_const_mul, integral_Ico_eq_integral_Ioc,
              ← intervalIntegral.integral_of_le hle, hFTC]
  have hcast (n i : ℕ) :
      (q n i).toNNReal = t * (i : NNReal) / ((n + 2 : ℕ) : NNReal) := by
    apply NNReal.coe_injective
    rw [Real.coe_toNNReal _ (hq0 n i)]
    simp [q, T, Nat.cast_add]
  intro n
  change (∫ s in Icc 0 T, F n s) = _
  rw [hgrid]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [V, hcast]
