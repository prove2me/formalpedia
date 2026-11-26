-- Prove2me | solution 1 for Kyprianou.Ch04.exercise49PrefixSafeMassV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T13:03:03.136235+00:00
-- url     : https://prove2.me/submissions/c8a88a93-b4df-4efd-a70a-43de5149d78c

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_exercise49FutureSafeEventV1
import Theorems.Thm_Kyprianou_Ch04_exercise49PrefixFutureMassV1
import Theorems.Thm_Kyprianou_Ch04_shiftedIsLevyProcessV1
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch03_CompletedNaturalFiltration
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false
/-- Independent safe future after a favourable prefix gives positive survival mass. -/
theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : NNReal → Ω → ℝ) (hX : IsLevyProcess X P)
    (hm : ∀ t, Measurable (X t)) (hc : ∀ ω, IsCadlag (fun t => X t ω))
    (s : NNReal) (b : ℝ)
    (hA : 0 < P {ω | (∀ u : NNReal, u ≤ s → 0 ≤ X u ω) ∧ b ≤ X s ω})
    (hB : 0 < P {ω | ∀ u : NNReal, -b ≤ X u ω}) :
    0 < P {ω | ∀ u : NNReal, 0 ≤ X u ω} := by
  obtain ⟨B, hBm, hBc⟩ := Kyprianou.Ch04.exercise49FutureSafeEventV1 (-b)
  let A : Set Ω := {ω | (∀ u : NNReal, u ≤ s → 0 ≤ X u ω) ∧ b ≤ X s ω}
  let U : Ω → (NNReal → ℝ) := fun ω u => X (s + u) ω - X s ω
  let S : Set Ω := {ω | ∀ u : NNReal, 0 ≤ X u ω}
  have he : {ω | (fun u => X u ω) ∈ B} =
      {ω | ∀ u : NNReal, -b ≤ X u ω} := by
    ext ω
    exact hBc _ (hc ω)
  have hmass := Kyprianou.Ch04.exercise49PrefixFutureMassV1 P X hX hm hc s b B hBm
  change P (A ∩ U ⁻¹' B) = P A * P {ω | (fun u => X u ω) ∈ B} at hmass
  rw [he] at hmass
  have hp : 0 < P (A ∩ U ⁻¹' B) := by
    rw [hmass]
    exact ENNReal.mul_pos hA.ne' hB.ne'
  have hshift := (Kyprianou.Ch04.shiftedIsLevyProcessV1 P X hX s).cadlag_ae
  have hS : 0 < P S := by
    apply lt_of_lt_of_le hp
    apply measure_mono_ae
    filter_upwards [hshift] with ω hω hw
    change ((∀ u : NNReal, u ≤ s → 0 ≤ X u ω) ∧ b ≤ X s ω) ∧ U ω ∈ B at hw
    obtain ⟨⟨hpre, hgain⟩, hBω⟩ := hw
    have hfuture := (hBc _ hω).mp hBω
    change ∀ u : NNReal, 0 ≤ X u ω
    intro u
    by_cases hus : u ≤ s
    · exact hpre u hus
    · have hh := hfuture (u - s)
      rw [add_tsub_cancel_of_le (lt_of_not_ge hus).le] at hh
      linarith
  exact hS
