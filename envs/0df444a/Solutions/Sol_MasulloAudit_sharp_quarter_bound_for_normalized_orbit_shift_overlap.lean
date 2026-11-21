-- Prove2me | solution 1 for MasulloAudit.sharp_quarter_bound_for_normalized_orbit_shift_overlap
-- status  : ACCEPTED   (prove)
-- author  : @Yi
-- created : 2026-11-21T01:21:23.480791+00:00
-- url     : https://prove2.me/submissions/7c0d8af3-369c-4ea4-93e6-a6e1429e5b22

import Mathlib.Data.Finsupp.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

open Finset

private theorem split_shift (d : ℤ) (w : ℤ →₀ ℝ) (X Y : Finset ℤ)
    (h : ∀ x ∈ X, w (x+d) ≠ 0 → x+d ∈ Y) :
    ∑ x ∈ X, w x * w (x+d) =
      ∑ x ∈ X, ∑ y ∈ Y, if x+d=y then w x * w y else 0 := by
  refine sum_congr rfl fun x hx => ?_
  rw [sum_ite_eq]
  by_cases hy : x+d ∈ Y
  · simp [hy]
  · have hw : w (x+d) = 0 := by by_contra hn; exact hy (h x hx hn)
    simp [hy,hw]

theorem solution (d : ℤ) (hd : d ≠ 0) :
    (∀ w : ℤ →₀ ℝ, (∀ i : ℤ, 0 ≤ w i) → (∑ i ∈ w.support, w i) = 1 →
      (∑ i ∈ w.support, w i * w (i+d)) ≤ 1/4) ∧
    (∃ w : ℤ →₀ ℝ, (∀ i : ℤ, 0 ≤ w i) ∧ (∑ i ∈ w.support, w i) = 1 ∧
      (∑ i ∈ w.support, w i * w (i+d)) = 1/4) := by
  classical
  constructor
  · intro w hw htotal
    let color (i : ℤ) := (i/d)%2 = 0
    have flip (i : ℤ) : color (i+d) ↔ ¬color i := by
      dsimp only [color]
      rw [Int.add_ediv_of_dvd_right (dvd_refl d),Int.ediv_self hd]
      omega
    let A := w.support.filter color
    let B := w.support.filter (fun i => ¬ color i)
    have hAB : ∀ i ∈ A, w (i+d) ≠ 0 → i+d ∈ B := by
      intro i hi h
      exact mem_filter.mpr ⟨Finsupp.mem_support_iff.mpr h, fun hc =>
        ((flip i).mp hc) (mem_filter.mp hi).2⟩
    have hBA : ∀ i ∈ B, w (i+d) ≠ 0 → i+d ∈ A := by
      intro i hi h
      exact mem_filter.mpr ⟨Finsupp.mem_support_iff.mpr h, (flip i).mpr (mem_filter.mp hi).2⟩
    have part := w.support.sum_filter_add_sum_filter_not color (fun i => w i * w (i+d))
    change ∑ i ∈ A, _ + ∑ i ∈ B, _ = _ at part
    have hm := w.support.sum_filter_add_sum_filter_not color w
    change (∑ i ∈ A, w i) + ∑ i ∈ B, w i = _ at hm
    rw [htotal] at hm
    rw [←part,split_shift d w A B hAB,split_shift d w B A hBA,
      sum_comm (s:=B) (t:=A),←sum_add_distrib]
    calc _ ≤ ∑ i ∈ A, ∑ j ∈ B, w i * w j := by
              apply sum_le_sum
              intro i hi
              rw [←sum_add_distrib]
              apply sum_le_sum
              intro j hj
              by_cases h1 : i+d=j
              · have h2 : j+d≠i := by omega
                simp [h1,h2]
              · by_cases h2 : j+d=i
                · simp [h1,h2,mul_comm]
                · simp [h1,h2,mul_nonneg (hw i) (hw j)]
         _ = (∑ i ∈ A, w i)*(∑ j ∈ B, w j) := by rw [sum_mul]; simp_rw [mul_sum]
         _ ≤ 1/4 := by nlinarith [sq_nonneg ((∑ i ∈ A, w i)-(∑ j ∈ B, w j)),
                 congrArg (fun x : ℝ => x^2) hm]
  · let w : ℤ →₀ ℝ := Finsupp.single 0 (1/2) + Finsupp.single d (1/2)
    have wform (i : ℤ) : w i = (if 0=i then 1/2 else 0) + (if d=i then 1/2 else 0) := by
      simp [w,Finsupp.single_apply]
    have hs : w.support = {0,d} := by
      ext i
      rw [Finsupp.mem_support_iff,wform]
      by_cases hi : i=0
      · subst i; simp [hd]
      · by_cases hj : i=d
        · subst i; simp [hd, Ne.symm hd]
        · simp [hi,hj,Ne.symm hi,Ne.symm hj]
    refine ⟨w, fun i => ?_, ?_, ?_⟩
    · rw [wform]; split_ifs <;> norm_num
    · rw [hs]; norm_num [hd,Ne.symm hd,wform]
    · rw [hs]
      have hdd : d+d ≠ 0 := by omega
      have hds : d+d ≠ d := by omega
      norm_num [wform,hd,Ne.symm hd,Ne.symm hdd,Ne.symm hds]
