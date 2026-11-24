-- Prove2me | solution 1 for Kyprianou.Ch03.openHitAfterCutoffStoppingV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T12:21:20.577871+00:00
-- url     : https://prove2.me/submissions/581ee1aa-4c09-426f-816c-52f7ba63c2ce

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch03_EntryAndHittingTimes
import Definitions.Def_Kyprianou_Ch03_CompletedNaturalFiltration
import Theorems.Thm_Kyprianou_Ch03_delayedOpenHitStoppingV1
open MeasureTheory ProbabilityTheory Filter Set
open Kyprianou.Ch03
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (X : NNReal → Omega → Real)
    (hX : IsLevyProcess X P)
    (hNatural : IsCompletedNaturalFiltration P X F)
    (B : Set Real) (hB : IsOpen B) (a : NNReal)
    (hRC : F.IsRightContinuous) :
    IsStoppingTime F (fun w : Omega => sInf {u : WithTop NNReal | ∃ r : NNReal,
        a < r ∧ X r w ∈ B ∧ u = (r : WithTop NNReal)}) := by
  letI := hRC
  let T (n : ℕ) (w : Omega) : WithTop NNReal :=
    sInf ((fun t : NNReal => (t : WithTop NNReal)) ''
      {t : NNReal | a + 1 / ((n : NNReal) + 1) ≤ t ∧ X t w ∈ B})
  have hT (n : ℕ) : IsStoppingTime F (T n) :=
    delayedOpenHitStoppingV1 P F X hX hNatural hRC _ B hB
  have he (w : Omega) :
      sInf {u : WithTop NNReal | ∃ r : NNReal,
        a < r ∧ X r w ∈ B ∧ u = (r : WithTop NNReal)} = ⨅ n, T n w := by
    apply le_antisymm
    · apply le_iInf
      intro n
      apply le_sInf
      rintro _ ⟨r, ⟨hr, hB'⟩, rfl⟩
      exact sInf_le ⟨r, (lt_add_of_pos_right _ (by positivity)).trans_le hr, hB', rfl⟩
    · apply le_sInf
      rintro _ ⟨r, hr, hB', rfl⟩
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (tsub_pos_of_lt hr)
      have hnr : a + 1 / ((n : NNReal) + 1) ≤ r :=
        ((lt_tsub_iff_left).mp hn).le
      exact (iInf_le _ n).trans (sInf_le ⟨r, ⟨hnr, hB'⟩, rfl⟩)
  rw [show (fun w : Omega => sInf {u : WithTop NNReal | ∃ r : NNReal,
      a < r ∧ X r w ∈ B ∧ u = (r : WithTop NNReal)}) =
      (fun w => ⨅ n, T n w) from funext he]
  exact IsStoppingTime.iInf hT
