-- Prove2me | solution 1 for HryniewiczCriterion.unknotted_selfLinking_of_bounds_global_section
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-07T16:41:16.690069+00:00
-- url     : https://prove2.me/submissions/0a269282-d32d-41a2-b900-4741d7f15a2e

import Definitions.Def_HryniewiczCriterion_ConleyZehnder
import Theorems.Thm_HryniewiczCriterion_exists_circle_param_of_image_eq
import Theorems.Thm_HryniewiczCriterion_disk_conormal_xi_winding_eq_one
import Theorems.Thm_HryniewiczCriterion_disk_conormal_pushOff_linking_zero
import Theorems.Thm_HryniewiczCriterion_selfLinking_eq_sub_of_pushOff_winding

open HryniewiczCriterion

theorem solution (H : R4 → ℝ)
    (hS : IsStrictlyStarShapedLevel H) (hdc : IsDynamicallyConvex H)
    (P : PeriodicOrbit H) (hP : P.IsPrime)
    (hD : BoundsDiskLikeGlobalSection H P) :
    IsUnknotted H P ∧ HasSelfLinkingNumber H P (-1) := by
  obtain ⟨e, he, hDS, hbd, htr, -⟩ := hD
  refine ⟨⟨e, he, hDS, hbd⟩, ?_⟩
  obtain ⟨u, hu, huper, hucirc, heu⟩ := exists_circle_param_of_image_eq H hS P e he hbd
  obtain ⟨r, θ, hr, hθ, hr0, hrper, hθper, hV⟩ :=
    disk_conormal_xi_winding_eq_one H hS P hP e he hDS hbd htr u hu huper hucirc heu
  obtain ⟨ε₀, hε₀, hl⟩ :=
    disk_conormal_pushOff_linking_zero H hS P hP e he hDS hbd u hu huper hucirc heu
  have key := selfLinking_eq_sub_of_pushOff_winding H hS P hP r θ hr hθ hr0 hrper 1
    (fun s => by rw [hθper s]; push_cast; ring) 0
    ⟨ε₀, hε₀, fun ε h1 h2 => by simpa only [hV] using hl ε h1 h2⟩
  simpa using key
