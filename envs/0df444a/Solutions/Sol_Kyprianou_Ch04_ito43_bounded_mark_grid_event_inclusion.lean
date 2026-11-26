-- Prove2me | solution 1 for Kyprianou.Ch04.ito43_bounded_mark_grid_event_inclusion
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T21:49:19.317013+00:00
-- url     : https://prove2.me/submissions/af3505cb-eaf1-4a77-b566-186f1b3a6f64

import Mathlib.Data.NNReal.Defs
import Mathlib.MeasureTheory.SetSemiring
import Mathlib.Order.Filter.Defs
import Mathlib.Tactic.Positivity
import Theorems.Thm_Kyprianou_Ch04_ito43_cosine_clipped_prefix
import Theorems.Thm_Kyprianou_Ch04_ito43_cosine_grid_bias_from_mean
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false
theorem solution (X : NNReal → ℝ) (q : ℝ → ℝ) (h0 : q 0 = 0)
    (T : NNReal) (c μ C e : ℝ) (he : 0 < e)
    (hC : 0 ≤ C) (hq : ∀ z, 0 ≤ q z ∧ q z ≤ C)
    (n : ℕ) (hn : 0 < n)
    (hmean : |(n:ℝ)*μ-c*(T:ℝ)| < e/4)
    (hmesh : |c| * ((T:ℝ)/(n:ℝ)) < e/4)
    (hcut : C < e/4) :
    let u : ℕ → NNReal := fun k => T*(k:NNReal)/(n:NNReal)
    ∀ t ≤ T, e ≤ |c*(t:ℝ)-∑ k ∈ Finset.range n,
        q (X (min t (u (k+1)))-X (min t (u k)))| →
      ∃ j ≤ n, e/4 ≤ |∑ k ∈ Finset.range j,
        (q (X (u (k+1))-X (u k))-μ)| := by
  intro u t ht herr
  obtain ⟨j,hj,hclock,hclip⟩ := Kyprianou.Ch04.ito43_cosine_clipped_prefix
    X q h0 C hC hq T t ht n hn
  have hclock' : |(t:ℝ)-(T:ℝ)*(j:ℝ)/(n:ℝ)| ≤ (T:ℝ)/(n:ℝ) := by
    exact_mod_cast hclock
  have hb := Kyprianou.Ch04.ito43_cosine_grid_bias_from_mean T c μ n j hn hj t
    (e/4) (by positivity) hmean hclock'
  let S : ℝ := ∑ k ∈ Finset.range j, q (X (u (k+1))-X (u k))
  let R : ℝ := ∑ k ∈ Finset.range n, q (X (min t (u (k+1)))-X (min t (u k)))
  have hD : (∑ k ∈ Finset.range j, (q (X (u (k+1))-X (u k))-μ)) =
      S-(j:ℝ)*μ := by
    simp [S,Finset.sum_sub_distrib,Finset.sum_const,nsmul_eq_mul]
  refine ⟨j,hj,?_⟩
  rw [hD]
  by_contra h
  have hsmall := lt_of_not_ge h
  have hh : |R-S| ≤ C := hclip
  change e ≤ |c*(t:ℝ)-R| at herr
  have heq : c*(t:ℝ)-R =
      (c*(t:ℝ)-(j:ℝ)*μ)-(S-(j:ℝ)*μ)-(R-S) := by ring
  rw [heq] at herr
  have h1 := abs_sub_le (c*(t:ℝ)-(j:ℝ)*μ) 0 (S-(j:ℝ)*μ)
  have h2 := abs_sub_le (c*(t:ℝ)-(j:ℝ)*μ-(S-(j:ℝ)*μ)) 0 (R-S)
  simp only [sub_zero,zero_sub,abs_neg] at h1 h2
  linarith
