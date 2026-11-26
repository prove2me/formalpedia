-- Prove2me | solution 1 for Kyprianou.Ch04.ito43_spatial_compact_taylor
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T15:56:09.119561+00:00
-- url     : https://prove2.me/submissions/695dd14d-67f8-4704-a229-a0430080566d

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_ito43_spatial_taylor_modulus
open Set
set_option autoImplicit false

/-- Small spatial Taylor excess is bounded by an arbitrarily small multiple of squared increments,
uniformly on a compact time-space rectangle. -/
theorem solution (f : ℝ × ℝ → ℝ) (T M : ℝ)
    (hf : ∀ s ∈ Icc 0 T, ContDiff ℝ 2 (fun x : ℝ => f (s,x)))
    (hg : ContinuousOn (fun z : ℝ × ℝ => iteratedDeriv 2 (fun x : ℝ => f (z.1,x)) z.2)
      (Icc 0 T ×ˢ Icc (-M) M)) :
    ∀ e : ℝ, 0 < e → ∃ δ : ℝ, 0 < δ ∧
      ∀ s ∈ Icc 0 T, ∀ x ∈ Icc (-M) M, ∀ y ∈ Icc (-M) M, |y-x| ≤ δ →
        |f (s,y) - f (s,x) - deriv (fun z : ℝ => f (s,z)) x * (y-x) -
          iteratedDeriv 2 (fun z : ℝ => f (s,z)) x * (y-x)^2/2| ≤ e * (y-x)^2 := by
  intro e he
  let g : ℝ × ℝ → ℝ := fun z => iteratedDeriv 2 (fun x : ℝ => f (z.1,x)) z.2
  have hK : IsCompact (Icc 0 T ×ˢ Icc (-M) M) := isCompact_Icc.prod isCompact_Icc
  obtain ⟨δ,hδ,hδb⟩ := Metric.uniformContinuousOn_iff_le.mp
    (hK.uniformContinuousOn_of_continuous hg) e he
  refine ⟨δ,hδ,?_⟩
  intro s hs x hx y hy hxy
  have hb (z : ℝ) (hz : z ∈ uIcc x y) :
      |iteratedDeriv 2 (fun q : ℝ => f (s,q)) z -
        iteratedDeriv 2 (fun q : ℝ => f (s,q)) x| ≤ e := by
    have hz' : z ∈ Icc (-M) M := uIcc_subset_Icc hx hy hz
    have hd : dist (s,z) (s,x) ≤ δ := by
      rw [dist_prod_same_left,dist_comm z x]
      exact (Real.dist_left_le_of_mem_uIcc hz).trans (by simpa [Real.dist_eq,abs_sub_comm] using hxy)
    exact hδb (s,z) ⟨hs,hz'⟩ (s,x) ⟨hs,hx⟩ hd
  have H := Kyprianou.Ch04.ito43_spatial_taylor_modulus
    (fun z : ℝ => f (s,z)) (hf s hs) x y _ e he.le hb
  exact H.trans (by nlinarith [mul_nonneg he.le (sq_nonneg (y-x))])
