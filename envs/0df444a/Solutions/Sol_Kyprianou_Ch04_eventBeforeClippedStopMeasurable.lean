-- Prove2me | solution 1 for Kyprianou.Ch04.eventBeforeClippedStopMeasurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T09:01:44.532925+00:00
-- url     : https://prove2.me/submissions/4048cf18-49a0-476a-933d-c99603017215

import Mathlib
open MeasureTheory Filter Set
open scoped NNReal
set_option autoImplicit false

/-- The surviving portion of an event at a deterministic time is measurable at the clipped stop. -/
theorem solution {Omega : Type} [MeasurableSpace Omega]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (tau : Omega → WithTop NNReal) (ht : IsStoppingTime F tau)
    (s : NNReal) (A : Set Omega) (hA : MeasurableSet[F s] A) :
    MeasurableSet[(ht.min_const s).measurableSpace]
      (A ∩ {w | tau w ≤ (s : WithTop NNReal)}ᶜ) := by
  let B := A ∩ {w | tau w ≤ (s : WithTop NNReal)}ᶜ
  have hB : MeasurableSet[F s] B := hA.inter (ht s).compl
  refine ⟨le_iSup (fun u => F u) s B hB, fun u => ?_⟩
  by_cases hsu : s ≤ u
  · exact (F.mono hsu B hB).inter (ht.min_const s u)
  · have he : B ∩ {w | min (tau w) (s : WithTop NNReal) ≤ (u : WithTop NNReal)} = ∅ := by
      ext w
      simp only [Set.mem_inter_iff,Set.mem_empty_iff_false,iff_false]
      rintro ⟨hw,hwu⟩
      have hnot : ¬ tau w ≤ (s : WithTop NNReal) := hw.2
      change min (tau w) (s : WithTop NNReal) ≤ (u : WithTop NNReal) at hwu
      rw [min_eq_right (le_of_not_ge hnot)] at hwu
      exact hsu (WithTop.coe_le_coe.mp hwu)
    change MeasurableSet[F u] (B ∩ {w | min (tau w) (s : WithTop NNReal) ≤ (u : WithTop NNReal)})
    rw [he]
    exact @MeasurableSet.empty Omega (F u)
