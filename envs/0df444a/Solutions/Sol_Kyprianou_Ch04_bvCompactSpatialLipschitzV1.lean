-- Prove2me | solution 1 for Kyprianou.Ch04.bvCompactSpatialLipschitzV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T00:32:47.821422+00:00
-- url     : https://prove2.me/submissions/06765b16-0e94-48f0-9be1-4ae6e3ede20d

import Mathlib
open MeasureTheory Filter Set
set_option autoImplicit false

theorem solution
    (f : ℝ × ℝ → ℝ)
    (hf : ContDiffOn ℝ 1 f (Set.prod (Set.Ici (0 : ℝ)) Set.univ))
    (T M : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (u x y : ℝ),
      u ∈ Set.Icc 0 T → x ∈ Set.Icc (-M) M → y ∈ Set.Icc (-M) M →
      |f (u,x) - f (u,y)| ≤ C * |x-y| := by
  let H : Set (ℝ × ℝ) := Set.prod (Set.Ici (0 : ℝ)) Set.univ
  let K : Set (ℝ × ℝ) := Set.prod (Icc 0 T) (Icc (-M) M)
  have hsub : K ⊆ H := fun z hz => ⟨hz.1.1, mem_univ _⟩
  have hUnique : UniqueDiffOn ℝ H := (uniqueDiffOn_Ici 0).prod uniqueDiffOn_univ
  have hD := hf.continuousOn_fderivWithin hUnique le_rfl
  have hK : IsCompact K := isCompact_Icc.prod isCompact_Icc
  obtain ⟨C,hC⟩ := hK.bddAbove_image (hD.norm.mono hsub)
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro u x y hu hx hy
  have hc : Convex ℝ K := (convex_Icc 0 T).prod (convex_Icc (-M) M)
  have hder (z : ℝ × ℝ) (hz : z ∈ K) :
      HasFDerivWithinAt f (fderivWithin ℝ f H z) K z :=
    ((hf.differentiableOn_one z (hsub hz)).hasFDerivWithinAt).mono hsub
  have hb (z : ℝ × ℝ) (hz : z ∈ K) : ‖fderivWithin ℝ f H z‖ ≤ max C 0 :=
    (hC (mem_image_of_mem _ hz)).trans (le_max_left _ _)
  have h := hc.norm_image_sub_le_of_norm_hasFDerivWithin_le hder hb
    (show (u,y) ∈ K from ⟨hu,hy⟩) (show (u,x) ∈ K from ⟨hu,hx⟩)
  simpa [Real.norm_eq_abs, Prod.norm_def, max_eq_right (abs_nonneg (x-y))] using h
