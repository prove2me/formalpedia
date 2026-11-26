-- Prove2me | solution 1 for Kyprianou.Ch04.exercise49PrefixBlockAppendV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T13:01:51.144845+00:00
-- url     : https://prove2.me/submissions/082504b1-8d3c-48f6-8b53-ae1ef5613d82

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_exercise49FuturePrefixEventV1
import Theorems.Thm_Kyprianou_Ch04_exercise49PrefixFutureMassV1
import Theorems.Thm_Kyprianou_Ch04_shiftedIsLevyProcessV1
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch03_CompletedNaturalFiltration
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false
/-- Independent blocks and pathwise survival. -/
theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : NNReal → Ω → ℝ) (hX : IsLevyProcess X P)
    (hm : ∀ t, Measurable (X t)) (hc : ∀ ω, IsCadlag (fun t => X t ω))
    (s t : NNReal) (b a : ℝ) (hb : 0 ≤ b)
    (hA : 0 < P {ω | (∀ u : NNReal, u ≤ s → 0 ≤ X u ω) ∧ b ≤ X s ω})
    (hB : 0 < P {ω | (∀ u : NNReal, u ≤ t → 0 ≤ X u ω) ∧ a ≤ X t ω}) :
    0 < P {ω | (∀ u : NNReal, u ≤ s + t → 0 ≤ X u ω) ∧ b + a ≤ X (s + t) ω} := by
  obtain ⟨B, hBm, hBc⟩ := Kyprianou.Ch04.exercise49FuturePrefixEventV1 t a
  let A : Set Ω := {ω | (∀ u : NNReal, u ≤ s → 0 ≤ X u ω) ∧ b ≤ X s ω}
  let U : Ω → (NNReal → ℝ) := fun ω u => X (s + u) ω - X s ω
  have he : {ω | (fun u => X u ω) ∈ B} =
      {ω | (∀ u : NNReal, u ≤ t → 0 ≤ X u ω) ∧ a ≤ X t ω} := by
    ext ω
    exact hBc _ (hc ω)
  have hmass := Kyprianou.Ch04.exercise49PrefixFutureMassV1 P X hX hm hc s b B hBm
  change P (A ∩ U ⁻¹' B) = P A * P {ω | (fun u => X u ω) ∈ B} at hmass
  rw [he] at hmass
  have hp : 0 < P (A ∩ U ⁻¹' B) := by
    rw [hmass]
    exact ENNReal.mul_pos hA.ne' hB.ne'
  have hshift := (Kyprianou.Ch04.shiftedIsLevyProcessV1 P X hX s).cadlag_ae
  apply lt_of_lt_of_le hp
  apply measure_mono_ae
  filter_upwards [hshift] with ω hω hw
  change ((∀ u : NNReal, u ≤ s → 0 ≤ X u ω) ∧ b ≤ X s ω) ∧ U ω ∈ B at hw
  obtain ⟨⟨hpre, hgain⟩, hBω⟩ := hw
  have ⟨hnext, hnextGain⟩ := (hBc _ hω).mp hBω
  change (∀ u : NNReal, u ≤ s + t → 0 ≤ X u ω) ∧ b + a ≤ X (s + t) ω
  constructor
  · intro u hu
    by_cases hus : u ≤ s
    · exact hpre u hus
    · have hsu : s ≤ u := (lt_of_not_ge hus).le
      have hut : u - s ≤ t := tsub_le_iff_right.mpr (by simpa [add_comm] using hu)
      have hh := hnext (u - s) hut
      rw [add_tsub_cancel_of_le hsu] at hh
      linarith
  · linarith
