-- Prove2me | solution 1 for Kyprianou.Ch03.completedNaturalFiltrationExistsV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T23:02:21.89623+00:00
-- url     : https://prove2.me/submissions/8bfa83ec-ea16-4d63-b559-b25bb79eae26

import Mathlib
import Definitions.Def_Kyprianou_Ch03_CompletedNaturalFiltration
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch03_EsscherDensity
import Definitions.Def_PerfCorrMSQ_NaturalFiltration
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch03

theorem solution
    {Ω : Type} [m : MeasurableSpace Ω] (P : Measure Ω) [P.IsComplete]
    (X : NNReal → Ω → ℝ) (hx : ∀ t, Measurable (X t)) :
    ∃ F : Filtration NNReal m,
      IsCompletedNaturalFiltration P X F := by
  let N : MeasurableSpace Ω :=
    MeasurableSpace.generateFrom {A | ∃ B : Set Ω,
      MeasurableSet B ∧ P B = 0 ∧ A ⊆ B}
  have hn : N ≤ m := by
    apply MeasurableSpace.generateFrom_le
    rintro A ⟨B, _, hz, hs⟩
    exact measurableSet_of_null (μ := P) (measure_mono_null hs hz)
  have hl : ∀ t, PerfCorrMSQ.natFiltr X t ≤ m := by
    intro t
    unfold PerfCorrMSQ.natFiltr
    exact iSup_le fun u => iSup_le fun _ => (hx u).comap_le
  refine ⟨⟨fun t => PerfCorrMSQ.natFiltr X t ⊔ N, ?_, ?_⟩, fun _ => rfl⟩
  · intro s t hst
    apply sup_le_sup_right
    unfold PerfCorrMSQ.natFiltr
    exact iSup_le fun u => iSup_le fun hu =>
      le_iSup_of_le u (le_iSup_of_le (hu.trans hst) le_rfl)
  · exact fun t => sup_le (hl t) hn
