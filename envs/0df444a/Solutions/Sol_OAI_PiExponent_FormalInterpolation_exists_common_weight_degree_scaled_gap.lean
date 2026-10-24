-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.exists_common_weight_degree.scaled_gap
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T09:07:46.242846+00:00
-- url     : https://prove2.me/submissions/b882ebe6-7fb5-4032-9732-38a04cd8a05d

import Mathlib.Data.Real.Basic
import Mathlib.Tactic

theorem solution
    (q : Real) (hq : 0 < q)
    (lo : Real) (hlo : 0 < lo) (R : Real) (hgap : lo < R)
    (C : Real) (hC : 0 ≤ C) (N : Nat) :
    ∃ s : Nat, 0 < s ∧ N ≤ s ∧
      ∃ D : Real, 0 < D ∧
        (s : Real) * lo + C < D ∧
        D < (s : Real) * R ∧
        ∃ k : Nat, 0 < k ∧ D = (k : Real) * q := by
  have hwidth : 0 < R - lo := by linarith
  obtain ⟨n, hn⟩ := exists_nat_gt ((C + q) / (R - lo))
  let s : Nat := max N (n + 1)
  have hs : 0 < s := by
    dsimp [s]
    omega
  have hNs : N ≤ s := by
    dsimp [s]
    omega
  have hns : n ≤ s := by
    dsimp [s]
    omega
  have hscaleN : C + q < (n : Real) * (R - lo) := by
    have hmul := mul_lt_mul_of_pos_right hn hwidth
    rw [div_mul_cancel₀ _ (ne_of_gt hwidth)] at hmul
    exact hmul
  have hscale : C + q < (s : Real) * (R - lo) := by
    have hns' : (n : Real) ≤ (s : Real) := by exact_mod_cast hns
    have hmul := mul_le_mul_of_nonneg_right hns' (le_of_lt hwidth)
    linarith
  let x : Real := ((s : Real) * lo + C) / q
  have hx0 : 0 ≤ x := by
    dsimp [x]
    positivity
  let k : Nat := Nat.floor x + 1
  have hfloor : ((Nat.floor x : Nat) : Real) ≤ x := Nat.floor_le hx0
  have hceil : x < ((Nat.floor x : Nat) : Real) + 1 := Nat.lt_floor_add_one x
  have hkpos : 0 < k := by
    dsimp [k]
    omega
  have hxk : x < (k : Real) := by
    dsimp [k]
    push_cast
    exact hceil
  have hlowD : (s : Real) * lo + C < (k : Real) * q := by
    have hmul := mul_lt_mul_of_pos_right hxk hq
    dsimp [x] at hmul
    rw [div_mul_cancel₀ _ (ne_of_gt hq)] at hmul
    exact hmul
  have hfloorq : ((Nat.floor x : Nat) : Real) * q ≤ (s : Real) * lo + C := by
    have hmul := mul_le_mul_of_nonneg_right hfloor (le_of_lt hq)
    dsimp [x] at hmul
    rw [div_mul_cancel₀ _ (ne_of_gt hq)] at hmul
    exact hmul
  have hbound : (k : Real) * q ≤ (s : Real) * lo + C + q := by
    dsimp [k]
    push_cast
    nlinarith
  have hupD : (k : Real) * q < (s : Real) * R := by
    have hbound' := hbound
    nlinarith [hscale]
  refine ⟨s, hs, hNs, (k : Real) * q, ?_, hlowD, hupD, k, hkpos, rfl⟩
  positivity