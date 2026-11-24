-- Prove2me | solution 1 for Kyprianou.Ch03.levyFixedTimeIncrementLimitLawV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T08:22:34.085298+00:00
-- url     : https://prove2.me/submissions/421c1ccc-444c-42a4-8e0c-0afb8975cde3

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Theorems.Thm_Kyprianou_Ch03_levyShrinkingIncrementPairLawV1
import Theorems.Thm_Kyprianou_Ch02_identDistribPairOfAELimitsV1
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false
theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : NNReal -> Omega -> Real)
    (hX : ProbabilityTheory.IsLevyProcess X P)
    (u : NNReal) (hu : 0 < u) :
    IdentDistrib
      (fun ω : Omega => (X u ω - Function.leftLim (fun r : NNReal => X r ω) u, (0 : Real)))
      (fun _ : Omega => ((0 : Real), (0 : Real))) P P := by
  letI : (𝓝[<] u).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, hu⟩
  obtain ⟨s, hs⟩ := Filter.exists_seq_tendsto (𝓝[<] u)
  apply Kyprianou.Ch02.identDistribPairOfAELimitsV1 P
    (fun n ω => (X u ω - X (min (s n) u) ω, (0 : ℝ)))
    (fun n ω => (X (u - min (s n) u) ω, (0 : ℝ)))
  · exact fun n => Kyprianou.Ch03.levyShrinkingIncrementPairLawV1 P X hX u (s n)
  · filter_upwards [hX.cadlag_ae] with ω hω
    have hh := (tendsto_leftLim_of_tendsto ((hω u).2)).comp hs
    have hlt : ∀ᶠ n in atTop, s n < u := hs.eventually self_mem_nhdsWithin
    apply ((tendsto_const_nhds.sub hh).prodMk_nhds tendsto_const_nhds).congr'
    filter_upwards [hlt] with n hn
    simp [min_eq_left (le_of_lt hn)]
  · filter_upwards [hX.cadlag_ae] with ω hω
    have hz : Tendsto (fun r : NNReal => X r ω) (𝓝 0) (𝓝 0) := by
      simpa [ContinuousWithinAt, hX.start_zero] using (hω 0).1
    have ht := ((continuous_const.sub (continuous_id.min continuous_const) :
      Continuous (fun r : NNReal => u - min r u)).tendsto u).mono_left
        (show 𝓝[<] u ≤ 𝓝 u from nhdsWithin_le_nhds)
    have htime : Tendsto (fun n => u - min (s n) u) atTop (𝓝 0) := by
      have hh : Tendsto (fun n => u - min (s n) u) atTop (𝓝 (u - min u u)) :=
        ht.comp hs
      simpa only [min_self, tsub_self] using hh
    exact (hz.comp htime).prodMk_nhds tendsto_const_nhds
