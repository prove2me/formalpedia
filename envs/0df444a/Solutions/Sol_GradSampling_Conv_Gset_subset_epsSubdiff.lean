-- Prove2me | solution 1 for GradSampling.Conv.Gset_subset_epsSubdiff
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T14:03:09.367556+00:00
-- url     : https://prove2.me/submissions/77e05d29-aad1-45f5-bab1-6fb8a6912260

import Mathlib
import Definitions.Def_ClarkeGradients_Shared_generalizedGradient
import Definitions.Def_GradSampling_Conv_Setting

open MeasureTheory ProbabilityTheory Filter Topology

open GradSampling.Conv in
theorem solution {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (D : Set (EuclideanSpace ℝ (Fin n)))
    (hDo : IsOpen D) (hC1 : ContDiffOn ℝ 1 f D) (ε : ℝ) (hε : 0 < ε) :
    ∀ x, Gset f D ε x ⊆ epsSubdiff f ε x := by
  intro x
  unfold Gset epsSubdiff
  apply closure_mono
  apply convexHull_mono
  rintro _ ⟨y, ⟨hyB, hyD⟩, rfl⟩
  refine Set.mem_biUnion hyB ?_
  apply subset_convexHull
  have hdiff : DifferentiableAt ℝ f y :=
    (hC1.differentiableOn one_ne_zero).differentiableAt (hDo.mem_nhds hyD)
  refine ⟨fun _ => 0, tendsto_const_nhds, fun _ => by simpa using hdiff, ?_⟩
  simp only [add_zero]
  exact tendsto_const_nhds
