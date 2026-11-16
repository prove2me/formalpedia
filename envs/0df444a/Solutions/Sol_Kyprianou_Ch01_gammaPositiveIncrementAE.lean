-- Prove2me | solution 1 for Kyprianou.Ch01.gammaPositiveIncrementAE
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T19:58:25.275234+00:00
-- url     : https://prove2.me/submissions/36df193a-0e13-47e1-9196-18ffcaaedf3e

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Theorems.Thm_Kyprianou_Ch01_gammaLaplacePositiveTimeAE
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology
set_option autoImplicit false

/-- Stationarity transports gamma marginal positivity to a strictly positive
    increment on any prescribed ordered time pair. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ)
    (alpha beta : ℝ) (ha : 0 < alpha) (hb : 0 < beta)
    (hX : ProbabilityTheory.IsLevyProcess X P)
    (hLaplace : ∀ (t : ℝ≥0) (q : ℝ), 0 ≤ q →
      Integrable (fun ω => Real.exp (-q * X t ω)) P ∧
      (∫ ω, Real.exp (-q * X t ω) ∂P) =
        (alpha / (alpha + q)) ^ (beta * (t : ℝ)))
    (s t : ℝ≥0) (hst : s < t) :
    ∀ᵐ ω ∂P, X s ω < X t ω := by
  have hdist := hX.stationary_increments s (t - s)
  have ht : s + (t - s) = t := add_tsub_cancel_of_le hst.le
  have hz : increment X 0 (t - s) = X (t - s) := by
    funext ω
    simp [increment, hX.start_zero]
  rw [ht, hz] at hdist
  change IdentDistrib (fun ω => X t ω - X s ω) (X (t - s)) P P at hdist
  have hpos : ∀ᵐ ω ∂P, 0 < X (t - s) ω :=
    Kyprianou.Ch01.gammaLaplacePositiveTimeAE P X alpha beta ha hb
      hLaplace (t - s) (tsub_pos_of_lt hst)
  have hPosSet : (X (t - s)) ⁻¹' Ioi (0 : ℝ) ∈ ae P := by
    change ∀ᵐ ω ∂P, 0 < X (t - s) ω
    exact hpos
  have hlaw : Ioi (0 : ℝ) ∈ ae (P.map (X (t - s))) :=
    (mem_ae_map_iff hdist.aemeasurable_snd measurableSet_Ioi).mpr hPosSet
  rw [← hdist.map_eq] at hlaw
  have hinc : Ioi (0 : ℝ) ∈ ae (P.map (fun ω => X t ω - X s ω)) :=
    hlaw
  have hpath := (mem_ae_map_iff hdist.aemeasurable_fst measurableSet_Ioi).mp hinc
  change ∀ᵐ ω ∂P, 0 < X t ω - X s ω at hpath
  filter_upwards [hpath] with ω hw
  exact sub_pos.mp hw
