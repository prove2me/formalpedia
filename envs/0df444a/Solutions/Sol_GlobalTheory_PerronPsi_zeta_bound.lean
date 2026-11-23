-- Prove2me | solution 1 for GlobalTheory.PerronPsi.zeta_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:44:11.165419+00:00
-- url     : https://prove2.me/submissions/60dcb302-8ffe-469b-ac80-5458cf6e0ff4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_TruncatedPerronKernel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_TruncatedPerronPsi

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
theorem _root_.solution {s : ℝ} (hs : 1 < s) : ∑' n : ℕ, 1 / (n : ℝ) ^ s ≤ 1 + 1 / (s - 1) := by
  have hs0 : 0 < s := by linarith
  have hnn : ∀ n : ℕ, 0 ≤ 1 / (n : ℝ) ^ s := fun n => by positivity
  have hI : ∀ a : ℕ, ∑ i ∈ Finset.range a, 1 / ((i : ℝ) + 1 + 1) ^ s ≤ 1 / (s - 1) := by
    intro a
    have hanti : AntitoneOn (fun x : ℝ => 1 / x ^ s) (Set.Icc 1 (1 + a)) := by
      intro x hx y hy hxy
      have hx0 : 0 < x := by linarith [hx.1]
      exact one_div_le_one_div_of_le (Real.rpow_pos_of_pos hx0 s)
        (Real.rpow_le_rpow hx0.le hxy hs0.le)
    have h1 := hanti.sum_le_integral
    have h1a : (1 : ℝ) ≤ 1 + a := by
      have := (Nat.cast_nonneg a : (0 : ℝ) ≤ a)
      linarith
    have hsum : ∑ i ∈ Finset.range a, 1 / ((i : ℝ) + 1 + 1) ^ s
        = ∑ i ∈ Finset.range a, 1 / ((1 : ℝ) + ((i + 1 : ℕ) : ℝ)) ^ s := by
      apply Finset.sum_congr rfl
      intro i _
      push_cast
      ring_nf
    have hint : ∫ x in (1 : ℝ)..1 + a, 1 / x ^ s = ∫ x in (1 : ℝ)..1 + a, x ^ (-s) := by
      apply intervalIntegral.integral_congr
      intro x hx
      have hx0 : 0 < x := by
        rw [Set.uIcc_of_le h1a] at hx
        linarith [hx.1]
      simp only
      rw [Real.rpow_neg hx0.le, one_div]
    have h0 : (0 : ℝ) ∉ Set.uIcc (1 : ℝ) (1 + a) := by
      rw [Set.uIcc_of_le h1a]
      intro h
      linarith [h.1]
    have hval : ∫ x in (1 : ℝ)..1 + a, x ^ (-s) = (1 - (1 + (a : ℝ)) ^ (1 - s)) / (s - 1) := by
      rw [integral_rpow (r := -s) (Or.inr ⟨fun h => by linarith, h0⟩), Real.one_rpow]
      have : -s + 1 = 1 - s := by ring
      rw [this]
      have hs1 : s - 1 ≠ 0 := by linarith
      have hs2 : 1 - s ≠ 0 := by linarith
      field_simp
      ring
    have hpos : 0 ≤ (1 + (a : ℝ)) ^ (1 - s) := by positivity
    rw [hsum]
    calc _ ≤ _ := h1
      _ = (1 - (1 + (a : ℝ)) ^ (1 - s)) / (s - 1) := by rw [hint, hval]
      _ ≤ 1 / (s - 1) := by
        apply div_le_div_of_nonneg_right _ (by linarith)
        linarith
  apply Real.tsum_le_of_sum_range_le hnn
  intro n
  calc ∑ i ∈ Finset.range n, 1 / (i : ℝ) ^ s
      ≤ ∑ i ∈ Finset.range (n + 2), 1 / (i : ℝ) ^ s :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 (by omega))
          (fun i _ _ => hnn i)
    _ = ∑ i ∈ Finset.range n, 1 / ((i : ℝ) + 1 + 1) ^ s + 1 := by
        rw [Finset.sum_range_succ', Finset.sum_range_succ']
        push_cast
        rw [Real.zero_rpow hs0.ne', Real.one_rpow]
        simp
    _ ≤ 1 + 1 / (s - 1) := by linarith [hI n]
end GlobalTheory.PerronPsi
