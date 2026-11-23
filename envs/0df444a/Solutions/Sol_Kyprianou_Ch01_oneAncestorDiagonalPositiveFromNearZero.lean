-- Prove2me | solution 1 for Kyprianou.Ch01.oneAncestorDiagonalPositiveFromNearZero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T09:06:08.610553+00:00
-- url     : https://prove2.me/submissions/3854b116-41b2-4606-b790-a039b884c7e0

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
import Theorems.Thm_Kyprianou_Ch01_oneAncestorDiagonalSupermultiplicative
open Kyprianou.Ch01 MeasureTheory
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    (K : PopulationLaws)
    (hSemi : IsPopulationMarkovSemigroup K)
    (hInit : K 1 0 = PMF.pure 1)
    (δ : ℝ) (hδ : 0 < δ)
    (hNear : ∀ t : ℝ≥0, (t : ℝ) < δ →
      0 < ((K 1 t) 1).toReal) :
    ∀ t : ℝ≥0, 0 < ((K 1 t) 1).toReal := by
  intro t
  obtain ⟨n, hn⟩ := exists_nat_gt ((t : ℝ) / δ)
  let m : ℕ := n + 1
  have hmpos : (0 : ℝ) < (m : ℝ) := by
    exact_mod_cast Nat.succ_pos n
  let step : ℝ≥0 := t / (m : ℝ≥0)
  have hstepSmall : (step : ℝ) < δ := by
    have hbound : (t : ℝ) < (n : ℝ) * δ :=
      (div_lt_iff₀ hδ).mp hn
    dsimp [step, m]
    apply (div_lt_iff₀ hmpos).mpr
    calc
      (t : ℝ) < (n : ℝ) * δ := hbound
      _ ≤ (m : ℝ) * δ :=
        mul_le_mul_of_nonneg_right (by simp [m]) hδ.le
      _ = δ * (m : ℝ) := mul_comm _ _
  have hstepPos : 0 < ((K 1 step) 1).toReal :=
    hNear step hstepSmall
  have hstepENN : (0 : ℝ≥0∞) < (K 1 step) 1 := by
    by_contra hnot
    have hzero : (K 1 step) 1 = 0 :=
      le_antisymm (not_lt.mp hnot) (zero_le)
    simp [hzero] at hstepPos
  have hpow : ∀ k : ℕ,
      ((K 1 step) 1) ^ k ≤ (K 1 ((k : ℝ≥0) * step)) 1 := by
    intro k
    induction k with
    | zero =>
        simpa [hInit] using (le_refl (1 : ℝ≥0∞))
    | succ k ih =>
        calc
          ((K 1 step) 1) ^ (k + 1) =
              ((K 1 step) 1) ^ k * (K 1 step) 1 := pow_succ _ _
          _ ≤ ((K 1 ((k : ℝ≥0) * step)) 1) * (K 1 step) 1 :=
              mul_le_mul_of_nonneg_right ih
                (show (0 : ℝ≥0∞) ≤ (K 1 step) 1 from zero_le)
          _ ≤ (K 1 ((k : ℝ≥0) * step + step)) 1 :=
              Kyprianou.Ch01.oneAncestorDiagonalSupermultiplicative
                K hSemi ((k : ℝ≥0) * step) step
          _ = (K 1 (((k + 1 : ℕ) : ℝ≥0) * step)) 1 := by
              congr 1
              push_cast
              ring
  have hmpos' : (m : ℝ≥0) ≠ 0 := by
    exact_mod_cast Nat.succ_ne_zero n
  have hEq : (m : ℝ≥0) * step = t := by
    dsimp [step]
    rw [mul_comm]
    exact div_mul_cancel₀ t hmpos'
  have htENN : (0 : ℝ≥0∞) < (K 1 t) 1 := by
    rw [← hEq]
    have hpowNZ : ((K 1 step) 1) ^ m ≠ 0 :=
      pow_ne_zero m (ne_of_gt hstepENN)
    have hpowPos : (0 : ℝ≥0∞) < ((K 1 step) 1) ^ m :=
      lt_of_le_of_ne (zero_le) (Ne.symm hpowNZ)
    exact lt_of_lt_of_le hpowPos (hpow m)
  exact ENNReal.toReal_pos (ne_of_gt htENN) ((K 1 t).apply_ne_top 1)
