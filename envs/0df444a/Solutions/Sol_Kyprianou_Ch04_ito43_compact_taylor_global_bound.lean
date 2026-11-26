-- Prove2me | solution 1 for Kyprianou.Ch04.ito43_compact_taylor_global_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T17:27:42.801999+00:00
-- url     : https://prove2.me/submissions/d690e22c-b089-4db8-a7e1-6ed98892e3b5

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_ito43_spatial_taylor_modulus
open Set
set_option autoImplicit false

/-- A compact time-space rectangle bounds both the second derivative and the uncentred Taylor remainder. -/
theorem solution (f : ℝ × ℝ → ℝ) (T M : ℝ)
    (hf : ∀ s ∈ Icc 0 T, ContDiff ℝ 2 (fun x : ℝ => f (s,x)))
    (hg : ContinuousOn (fun z : ℝ × ℝ => iteratedDeriv 2 (fun x : ℝ => f (z.1,x)) z.2)
      (Icc 0 T ×ˢ Icc (-M) M)) :
    ∃ C : ℝ, 0 ≤ C ∧
      (∀ s ∈ Icc 0 T, ∀ x ∈ Icc (-M) M,
        |iteratedDeriv 2 (fun z : ℝ => f (s,z)) x| ≤ C) ∧
      (∀ s ∈ Icc 0 T, ∀ x ∈ Icc (-M) M, ∀ y ∈ Icc (-M) M,
        |f (s,y)-f (s,x)-deriv (fun z : ℝ => f (s,z)) x*(y-x)| ≤ C*(y-x)^2/2) := by
  let K : Set (ℝ × ℝ) := Icc 0 T ×ˢ Icc (-M) M
  let g : ℝ × ℝ → ℝ := fun z => iteratedDeriv 2 (fun x : ℝ => f (z.1,x)) z.2
  have hK : IsCompact K := isCompact_Icc.prod isCompact_Icc
  obtain ⟨C,hC⟩ := hK.bddAbove_image (continuous_abs.comp_continuousOn hg)
  have hb (s : ℝ) (hs : s ∈ Icc 0 T) (x : ℝ) (hx : x ∈ Icc (-M) M) :
      |g (s,x)| ≤ max C 0 :=
    (hC (mem_image_of_mem _ (show (s,x) ∈ K from ⟨hs,hx⟩))).trans (le_max_left _ _)
  refine ⟨max C 0,le_max_right _ _,hb,?_⟩
  intro s hs x hx y hy
  have H := Kyprianou.Ch04.ito43_spatial_taylor_modulus (fun z => f (s,z))
    (hf s hs) x y 0 (max C 0) (le_max_right _ _)
    (fun z hz => by simpa only [sub_zero] using hb s hs z (uIcc_subset_Icc hx hy hz))
  simpa only [zero_mul,zero_div,sub_zero] using H
