-- Prove2me | solution 1 for Kyprianou.Ch03.delayedClosedHitFixedApproxUpperV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T12:45:12.866141+00:00
-- url     : https://prove2.me/submissions/2b498080-5dcb-490a-99c4-ee56a451fe5f

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch03_EntryAndHittingTimes
import Definitions.Def_Kyprianou_Ch03_CompletedNaturalFiltration
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (X : NNReal → Omega → Real) (hX : IsLevyProcess X P)
    (hNatural : Kyprianou.Ch03.IsCompletedNaturalFiltration P X F)
    (B : Set ℝ) (hB : IsClosed B) (a : NNReal)
    (T : ℕ → Omega → WithTop NNReal)
    (hT : ∀ n w, T n w = sInf ((fun t : NNReal => (t : WithTop NNReal)) ''
      {t : NNReal | a ≤ t ∧ X t w ∈ Metric.thickening (1 / ((n : ℝ) + 1)) B}))
    (hStop : ∀ n, IsStoppingTime F (T n)) :
    ∀ w, (⨆ n, T n w) ≤ sInf ((fun t : NNReal => (t : WithTop NNReal)) '' {t : NNReal | a ≤ t ∧ X t w ∈ B}) := by
  intro w
  apply iSup_le
  intro n
  rw [hT n w]
  apply sInf_le_sInf
  rintro u ⟨r, ⟨hr, hmem⟩, rfl⟩
  exact ⟨r, ⟨hr, Metric.self_subset_thickening (by positivity) B hmem⟩, rfl⟩
