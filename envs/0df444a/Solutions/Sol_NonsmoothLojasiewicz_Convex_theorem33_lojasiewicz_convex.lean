-- Prove2me | solution 1 for NonsmoothLojasiewicz.Convex.theorem33_lojasiewicz_convex
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-08T04:45:59.303482+00:00
-- url     : https://prove2.me/submissions/91f7d54b-ad8f-4add-8cb6-aad5acb75473
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_NonconvexSplitting_Shared_LimitingSubdiff
import Definitions.Def_MoreauProx_Characterization_GammaZero
import Definitions.Def_NonsmoothLojasiewicz_Continuous_IsSubanalytic
import Definitions.Def_NonsmoothLojasiewicz_Convex_crit
import Theorems.Thm_NonsmoothLojasiewicz_Convex_ineq15_distance_bound
import Theorems.Thm_NonsmoothLojasiewicz_Convex_ineq16_value_gap_le

open Filter Topology
open NonconvexSplitting.Shared MoreauProx.Characterization

set_option autoImplicit false

theorem solution {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → EReal)
    (hf : GammaZero f) (hsub : NonsmoothLojasiewicz.Continuous.IsSubanalyticFn f)
    (hcrit : (NonsmoothLojasiewicz.Convex.crit f).Nonempty)
    (K : Set (EuclideanSpace ℝ (Fin n))) (hK : Bornology.IsBounded K) :
    ∃ θ : ℝ, 0 ≤ θ ∧ θ < 1 ∧ ∃ C : ℝ, ∀ x ∈ K, ∀ v ∈ LimitingSubdiff f x,
      |(f x).toReal - (⨅ y, f y).toReal| ^ θ ≤ C * ‖v‖ := by
  obtain ⟨r, hr1, c, hc, h15⟩ :=
    NonsmoothLojasiewicz.Convex.ineq15_distance_bound f hf hsub hcrit K hK
  have hr0 : 0 < r := lt_trans zero_lt_one hr1
  have hinv_lt : 1 / r < 1 := by rw [div_lt_one hr0]; exact hr1
  have hinv_pos : 0 < 1 / r := by positivity
  have ha : 0 < c ^ (-1 / r) := Real.rpow_pos_of_pos hc _
  refine ⟨1 - 1 / r, by linarith, by linarith, c ^ (-1 / r), ?_⟩
  intro x hx v hv
  have hfin : f x ≠ ⊤ := hv.1
  have h16 := NonsmoothLojasiewicz.Convex.ineq16_value_gap_le f hf hcrit x v hv
  have hd := h15 x hx hfin
  set g := |(f x).toReal - (⨅ y, f y).toReal| with hg
  set d := Metric.infDist x (NonsmoothLojasiewicz.Convex.crit f) with hdd
  set a := c ^ (-1 / r) with haa
  have hv0 : 0 ≤ ‖v‖ := norm_nonneg v
  rcases (show (0:ℝ) ≤ g from abs_nonneg _).eq_or_lt with h0 | hpos
  · rw [← h0, Real.zero_rpow (by linarith)]
    exact mul_nonneg ha.le hv0
  · have hgp : 0 < g ^ (1 / r) := Real.rpow_pos_of_pos hpos _
    have key : g ≤ a * ‖v‖ * g ^ (1 / r) := by
      calc g ≤ ‖v‖ * d := h16
        _ ≤ ‖v‖ * (a * g ^ (1 / r)) := mul_le_mul_of_nonneg_left hd hv0
        _ = a * ‖v‖ * g ^ (1 / r) := by ring
    rw [Real.rpow_sub hpos, Real.rpow_one, div_le_iff₀ hgp]
    exact key
