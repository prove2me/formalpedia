-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.source_result8_2_v2_bridge_upper_drawdown
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T18:43:06.435264+00:00
-- url     : https://prove2.me/submissions/2f7e2519-ab39-4251-9a42-3ba1c4f48f49

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal
theorem solution {Ω : Type} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (D : SpectrallyNegativeModel Ω P) :
    ∀ l d : ℝ, 0 < l → 0 < d →
      ∀ t : ℝ≥0, ∀ ω : Ω,
        (t : WithTop ℝ≥0) < tauPlus D.X d ω →
        tauPlus D.X d ω < tauMinus D.X (-l) ω →
        reflectAtSup D.X 0 t ω ≤ l + d := by
  intro l d hl hd t ω ht hUpDown
  have hX0 : D.X 0 ω = 0 := congrFun D.levy.start_zero ω
  have hpos : ∀ s : ℝ≥0, s ≠ 0 → 0 < s := by
    intro s hs0
    rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ s) with h | h
    · exact absurd h.symm hs0
    · exact h
  have hLeD : ∀ s : ℝ≥0, (s : WithTop ℝ≥0) < tauPlus D.X d ω → D.X s ω ≤ d := by
    intro s hs
    by_cases hs0 : s = 0
    · subst hs0 ; rw [hX0] ; exact le_of_lt hd
    · apply le_of_not_gt
      intro hlt
      have hmem : (s : WithTop ℝ≥0) ∈ {w : WithTop ℝ≥0 | ∃ u : ℝ≥0, 0 < u ∧ (u : WithTop ℝ≥0) = w ∧ d < D.X u ω} :=
        ⟨s, hpos s hs0, rfl, hlt⟩
      have hle : tauPlus D.X d ω ≤ (s : WithTop ℝ≥0) := by unfold tauPlus ; exact sInf_le hmem
      exact (not_lt_of_ge hle) hs
  have hGeL : -l ≤ D.X t ω := by
    have htU : (t : WithTop ℝ≥0) < tauMinus D.X (-l) ω := lt_trans ht hUpDown
    by_cases ht0 : t = 0
    · subst ht0 ; rw [hX0] ; linarith
    · apply le_of_not_gt
      intro hlt
      have hmem : (t : WithTop ℝ≥0) ∈ {w : WithTop ℝ≥0 | ∃ u : ℝ≥0, 0 < u ∧ (u : WithTop ℝ≥0) = w ∧ D.X u ω < -l} :=
        ⟨t, hpos t ht0, rfl, hlt⟩
      have hle : tauMinus D.X (-l) ω ≤ (t : WithTop ℝ≥0) := by unfold tauMinus ; exact sInf_le hmem
      exact (not_lt_of_ge hle) htU
  have hSup_le : runningSup D.X t ω ≤ d := by
    apply csSup_le
    · exact ⟨D.X 0 ω, 0, (zero_le : (0 : ℝ≥0) ≤ t), rfl⟩
    · intro y hy
      obtain ⟨u, hut, rfl⟩ := hy
      have hu_lt : (u : WithTop ℝ≥0) < tauPlus D.X d ω := lt_of_le_of_lt (by exact_mod_cast hut) ht
      exact hLeD u hu_lt
  have hMax_le : max 0 (runningSup D.X t ω) ≤ d := max_le_iff.mpr ⟨le_of_lt hd, hSup_le⟩
  unfold reflectAtSup ; linarith
