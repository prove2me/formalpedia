-- Prove2me | solution 1 for Kyprianou.Ch04.ito43_spatial_slice_derivative
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T15:44:41.170614+00:00
-- url     : https://prove2.me/submissions/f7c68746-d13c-40b1-ae46-61727b8b2fba

import Mathlib
open Set Filter
open scoped Topology
set_option autoImplicit false

/-- At positive times the ambient spatial derivative is the derivative of the fixed-time slice. -/
theorem solution (f : ℝ × ℝ → ℝ)
    (hf : ContDiffOn ℝ 1 f (Ici (0 : ℝ) ×ˢ (univ : Set ℝ)))
    (s x : ℝ) (hs : 0 < s) :
    fderiv ℝ f (s,x) (0,1) = deriv (fun y : ℝ => f (s,y)) x := by
  let S := Ici (0 : ℝ) ×ˢ (univ : Set ℝ)
  have hm : S ∈ nhds (s,x) := by
    apply Filter.mem_of_superset ((isOpen_Ioi.prod isOpen_univ).mem_nhds
      (show (s,x) ∈ Ioi (0 : ℝ) ×ˢ (univ : Set ℝ) from ⟨hs,mem_univ _⟩))
    exact prod_mono Ioi_subset_Ici_self Subset.rfl
  have hd := ((hf.differentiableOn (by norm_num) (s,x)
    (show (s,x) ∈ S from ⟨hs.le,mem_univ _⟩)).differentiableAt hm).hasFDerivAt
  have hk : HasDerivAt (fun y : ℝ => (s,y)) (0,1) x :=
    (hasDerivAt_const x s).prodMk (hasDerivAt_id x)
  exact (hd.comp_hasDerivAt x hk).deriv.symm
