-- Prove2me | solution 1 for Kyprianou.Ch04.clippedAffineGridWeightErrorV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T23:42:55.018941+00:00
-- url     : https://prove2.me/submissions/7a7f1889-0983-4511-8a55-583c1facd8ea

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_clippedAffineGridVariationBoundV1
open MeasureTheory Set
open scoped NNReal Classical
set_option autoImplicit false

/-- The variation of a finite affine step path bounds all clipped mesh
weight perturbations independently of the mesh size. -/
theorem solution (T : NNReal) (S : Finset NNReal) (a Y H L : NNReal → ℝ)
    (b d : ℝ) (hd : 0 ≤ d) (u : ℕ → NNReal) (hu : Monotone u) (n : ℕ)
    (hY : ∀ s ≤ T, Y s = b * (s : ℝ) + ∑ r ∈ S, if r ≤ s then a r else 0)
    (hH : ∀ k ∈ Finset.range n, |H (u k)-L (u k)| ≤ d) :
    ∀ t ≤ T, |(∑ k ∈ Finset.range n,H (u k) *
      (Y (min t (u (k+1)))-Y (min t (u k)))) -
      (∑ k ∈ Finset.range n,L (u k) *
      (Y (min t (u (k+1)))-Y (min t (u k))))| ≤
      (|b| * (T : ℝ)+∑ r ∈ S,|a r|) * d := by
  intro t ht
  let v : ℕ → NNReal := fun k => min t (u k)
  have hvar := Kyprianou.Ch04.clippedAffineGridVariationBoundV1 T S a Y b u hu n hY t ht
  change |(∑ k ∈ Finset.range n,H (u k)*(Y (v (k+1))-Y (v k))) -
    (∑ k ∈ Finset.range n,L (u k)*(Y (v (k+1))-Y (v k)))| ≤ _
  rw [← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc
    _ ≤ ∑ k ∈ Finset.range n,d*|Y (v (k+1))-Y (v k)| := by
      apply Finset.sum_le_sum
      intro k hk
      rw [← sub_mul,abs_mul]
      exact mul_le_mul_of_nonneg_right (hH k hk) (abs_nonneg _)
    _ = d*(∑ k ∈ Finset.range n,|Y (v (k+1))-Y (v k)|) := by rw [Finset.mul_sum]
    _ ≤ _ := by rw [mul_comm]; exact mul_le_mul_of_nonneg_right hvar hd
