-- Prove2me | solution 1 for Helfgott.finite_shell_weighted_integral_bound
-- status  : ACCEPTED   (prove)
-- author  : @flyingviper
-- created : 2026-11-11T00:17:58.480958+00:00
-- url     : https://prove2.me/submissions/fc92bede-0012-4b30-b63d-78a4b639020b

import Mathlib.Algebra.BigOperators.Module
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open MeasureTheory Finset
open scoped BigOperators

private lemma finite_abel_majorant (N : ℕ) (a w F : ℕ → ℝ)
    (hw : ∀ i < N, w (i + 1) ≤ w i) (hwN : 0 ≤ w N)
    (hF : ∀ k ≤ N, ∑ i ∈ range (k + 1), a i ≤ F k) :
    (∑ i ∈ range (N + 1), w i * a i) ≤
      w N * F N + ∑ i ∈ range N, (w i - w (i + 1)) * F i := by
  have hid := Finset.sum_range_by_parts w a (N + 1)
  simp only [Nat.add_sub_cancel, smul_eq_mul] at hid
  rw [hid]
  have hs : (∑ i ∈ range N, (w i - w (i + 1)) *
      (∑ j ∈ range (i + 1), a j)) ≤
      ∑ i ∈ range N, (w i - w (i + 1)) * F i := by
    apply Finset.sum_le_sum
    intro i hi
    exact mul_le_mul_of_nonneg_left (hF i (Nat.le_of_lt (mem_range.mp hi)))
      (sub_nonneg.mpr (hw i (mem_range.mp hi)))
  have hn := mul_le_mul_of_nonneg_left (hF N le_rfl) hwN
  have heq : (∑ i ∈ range N, (w (i + 1) - w i) *
      (∑ j ∈ range (i + 1), a j)) =
      -(∑ i ∈ range N, (w i - w (i + 1)) *
        (∑ j ∈ range (i + 1), a j)) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [heq]
  linarith

-- Discrete version of Helfgott's Lemma 6.1 / Proposition 6.2.
-- The sets are disjoint arc shells; F bounds their cumulative energy.
theorem solution {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (N : ℕ) (s : ℕ → Set α) (f g : α → ℝ) (w F : ℕ → ℝ)
    (hs : ∀ i ≤ N, MeasurableSet (s i))
    (hdisj : Set.PairwiseDisjoint (↑(range (N + 1)) : Set ℕ) s)
    (hf : Integrable f μ) (hfg : Integrable (fun x => f x * g x) μ)
    (hf0 : ∀ x, 0 ≤ f x)
    (hg : ∀ i ≤ N, ∀ x ∈ s i, g x ≤ w i)
    (hw : ∀ i < N, w (i + 1) ≤ w i) (hwN : 0 ≤ w N)
    (hF : ∀ k ≤ N,
      (∫ x in ⋃ i ∈ range (k + 1), s i, f x ∂μ) ≤ F k) :
    (∫ x in ⋃ i ∈ range (N + 1), s i, f x * g x ∂μ) ≤
      w N * F N + ∑ i ∈ range N, (w i - w (i + 1)) * F i := by
  have hprefix (k : ℕ) (hk : k ≤ N) :
      (∫ x in ⋃ i ∈ range (k + 1), s i, f x ∂μ) =
        ∑ i ∈ range (k + 1), ∫ x in s i, f x ∂μ := by
    apply integral_biUnion_finset
    · intro i hi
      exact hs i (by have := mem_range.mp hi; omega)
    · intro i hi j hj hij
      have hi' : i < k + 1 := mem_range.mp hi
      have hj' : j < k + 1 := mem_range.mp hj
      exact hdisj (mem_range.mpr (by omega)) (mem_range.mpr (by omega)) hij
    · intro i hi
      exact hf.integrableOn
  rw [integral_biUnion_finset (range (N + 1))
    (fun i hi => hs i (by have := mem_range.mp hi; omega)) hdisj
    (fun i hi => hfg.integrableOn)]
  calc
    _ ≤ ∑ i ∈ range (N + 1), w i * (∫ x in s i, f x ∂μ) := by
      apply Finset.sum_le_sum
      intro i hi
      rw [← integral_const_mul]
      apply setIntegral_mono_on hfg.integrableOn (hf.const_mul (w i)).integrableOn
        (hs i (by have := mem_range.mp hi; omega))
      intro x hx
      simpa [mul_comm] using mul_le_mul_of_nonneg_left
        (hg i (by have := mem_range.mp hi; omega) x hx) (hf0 x)
    _ ≤ _ := finite_abel_majorant N (fun i => ∫ x in s i, f x ∂μ) w F hw hwN
      (fun k hk => by rw [← hprefix k hk]; exact hF k hk)
