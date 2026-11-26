-- Prove2me | solution 1 for Kyprianou.Ch04.ito43_time_slice_derivative
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T12:16:48.111824+00:00
-- url     : https://prove2.me/submissions/613c2bd5-60a2-46cb-b892-10b4d6e3dc3e

import Mathlib
open MeasureTheory Set Filter
open scoped Topology
set_option autoImplicit false

/-- The time derivative within the closed half-plane extends continuously to the time boundary. -/
theorem solution (f : ℝ × ℝ → ℝ)
    (hf : ContDiffOn ℝ 1 f (Ici (0 : ℝ) ×ˢ (univ : Set ℝ))) :
    let S := Ici (0 : ℝ) ×ˢ (univ : Set ℝ)
    let g := fun z : ℝ × ℝ => fderivWithin ℝ f S z (1,0)
    ContinuousOn g S ∧ ∀ s : ℝ, 0 < s → ∀ x : ℝ,
      g (s,x) = fderiv ℝ f (s,x) (1,0) := by
  intro S g
  have hu : UniqueDiffOn ℝ S := (uniqueDiffOn_Ici _).prod uniqueDiffOn_univ
  refine ⟨(hf.continuousOn_fderivWithin hu (by norm_num)).clm_apply continuousOn_const, ?_⟩
  intro s hs x
  have hN : S ∈ nhds (s,x) := by
    apply Filter.mem_of_superset ((isOpen_Ioi.prod isOpen_univ).mem_nhds
      (show (s,x) ∈ Ioi (0 : ℝ) ×ˢ (univ : Set ℝ) from ⟨hs,mem_univ _⟩))
    exact prod_mono Ioi_subset_Ici_self Subset.rfl
  change fderivWithin ℝ f S (s,x) (1,0) = _
  rw [fderivWithin_of_mem_nhds hN]
