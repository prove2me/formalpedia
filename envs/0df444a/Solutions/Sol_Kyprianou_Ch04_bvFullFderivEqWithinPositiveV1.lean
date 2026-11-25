-- Prove2me | solution 1 for Kyprianou.Ch04.bvFullFderivEqWithinPositiveV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T00:32:38.616018+00:00
-- url     : https://prove2.me/submissions/ec2591ab-6349-471d-a8a4-2f7092de4a5f

import Mathlib
open MeasureTheory Filter Set
open scoped Topology
set_option autoImplicit false

theorem solution
    (f : ℝ × ℝ → ℝ)
    (hf : ContDiffOn ℝ 1 f (Set.prod (Set.Ici (0 : ℝ)) Set.univ))
    (u x : ℝ) (hu : 0 < u) :
    fderivWithin ℝ f (Set.prod (Set.Ici (0 : ℝ)) Set.univ) (u,x) =
      fderiv ℝ f (u,x) := by
  let H : Set (ℝ × ℝ) := Set.prod (Set.Ici (0 : ℝ)) Set.univ
  have hUnique : UniqueDiffOn ℝ H := (uniqueDiffOn_Ici 0).prod uniqueDiffOn_univ
  have hmem : H ∈ 𝓝 (u,x) := by
    refine Filter.mem_of_superset
      ((isOpen_Ioi.prod isOpen_univ).mem_nhds
        (show (u,x) ∈ Set.prod (Ioi (0 : ℝ)) Set.univ from ⟨hu, mem_univ _⟩)) ?_
    intro z hz
    exact ⟨show z.1 ∈ Ici (0 : ℝ) from le_of_lt (show 0 < z.1 from hz.1), hz.2⟩
  have hz : (u,x) ∈ H := ⟨hu.le, mem_univ _⟩
  exact fderivWithin_eq_fderiv (hUnique _ hz)
    ((hf.differentiableOn_one _ hz).differentiableAt hmem)
