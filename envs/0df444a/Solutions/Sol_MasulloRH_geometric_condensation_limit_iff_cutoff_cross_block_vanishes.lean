-- Prove2me | solution 1 for MasulloRH.geometric_condensation_limit_iff_cutoff_cross_block_vanishes
-- status  : ACCEPTED   (prove)
-- author  : @Yi
-- created : 2026-11-21T05:23:51.809171+00:00
-- url     : https://prove2.me/submissions/7fce74b5-39fc-441e-bf92-1ed70c49e156

import Mathlib
open Filter Topology
theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (P A M : E →L[ℂ] E) (B : ℕ → E →L[ℂ] E)
    (hgeom : ∀ x, P (A (P x)) = A (P x))
    (hB : ∀ x, Tendsto (fun n => B n x) atTop (𝓝 (P x))) :
    (∀ x, Tendsto (fun n => M (P (A (B n x)))) atTop (𝓝 (M (A (P x))))) ∧
    ((∀ x, Tendsto (fun n => M (P (A (B n x)))) atTop (𝓝 (M (P (A x))))) ↔
      ∀ x, M (P (A (x - P x))) = 0) := by
  have hlim (x : E) : Tendsto (fun n => M (P (A (B n x)))) atTop (𝓝 (M (A (P x)))) := by
    rw [← hgeom x]
    exact (M.continuous.tendsto _).comp ((P.continuous.tendsto _).comp
      ((A.continuous.tendsto _).comp (hB x)))
  refine ⟨hlim, ?_⟩
  constructor
  · intro h x
    simpa only [map_sub, hgeom x, sub_eq_zero] using
      (show M (P (A x)) = M (A (P x)) from tendsto_nhds_unique (h x) (hlim x))
  · intro h x
    have he : M (P (A x)) = M (A (P x)) := by
      simpa only [map_sub, hgeom x, sub_eq_zero] using h x
    rw [he]
    exact hlim x
