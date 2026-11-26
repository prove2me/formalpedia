-- Prove2me | solution 1 for Kyprianou.Ch04.rationalRightLimitBridgeV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T23:45:13.263817+00:00
-- url     : https://prove2.me/submissions/ffda2be1-e1a5-4f60-8c36-d502df6fa75a

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_rationalNearRightPointV1
open MeasureTheory Set Filter Topology
open scoped NNReal
set_option autoImplicit false

/-- A right-continuous real function on positive times has its right limit iff its rational restriction does. -/
theorem solution (g : ℝ≥0 → ℝ) (d : ℝ)
    (hR : ∀ t : ℝ≥0, 0 < t → ContinuousWithinAt g (Ici t) t) :
    Tendsto (fun r : ℚ => g (Real.toNNReal (r : ℝ)))
      (nhdsWithin (0 : ℚ) (Ioi 0)) (nhds d) ↔
    Tendsto g (nhdsWithin (0 : ℝ≥0) (Ioi 0)) (nhds d) := by
  rw [Metric.tendsto_nhdsWithin_nhds, Metric.tendsto_nhdsWithin_nhds]
  constructor
  · intro h ε hε
    obtain ⟨δ, hδ, hd⟩ := h (ε / 2) (by positivity)
    refine ⟨δ, hδ, ?_⟩
    intro t ht htd
    obtain ⟨ρ, hρ, hc⟩ := Metric.tendsto_nhdsWithin_nhds.mp (hR t ht) (ε / 2) (by positivity)
    obtain ⟨r, hr, hrδ, hut, huρ⟩ :=
      Kyprianou.Ch04.rationalNearRightPointV1 t δ ρ ht htd hρ
    have h1 := hc hut huρ
    have h2 := hd hr hrδ
    calc
      dist (g t) d ≤ dist (g t) (g (Real.toNNReal (r : ℝ))) +
          dist (g (Real.toNNReal (r : ℝ))) d := dist_triangle _ _ _
      _ < ε := by rw [dist_comm (g t) (g (Real.toNNReal (r : ℝ)))]; linarith
  · intro h ε hε
    obtain ⟨δ, hδ, hd⟩ := h ε hε
    refine ⟨δ, hδ, ?_⟩
    intro r hr hrδ
    have hr0 : 0 < (r : ℝ) := by exact_mod_cast hr
    have hu : ((Real.toNNReal (r : ℝ) : ℝ≥0) : ℝ) = (r : ℝ) :=
      Real.coe_toNNReal (r : ℝ) hr0.le
    apply hd
    · change 0 < Real.toNNReal (r : ℝ)
      exact_mod_cast (show 0 < ((Real.toNNReal (r : ℝ) : ℝ≥0) : ℝ) by rw [hu]; exact hr0)
    · rw [NNReal.dist_eq, hu, NNReal.coe_zero]
      rwa [Rat.dist_eq, Rat.cast_zero] at hrδ
