-- Prove2me | solution 1 for Kyprianou.Ch03.delayedClosedHitFixedApproxV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T12:39:17.263011+00:00
-- url     : https://prove2.me/submissions/cbcb5a26-b586-4dee-a807-482d18473678

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch03_EntryAndHittingTimes
import Definitions.Def_Kyprianou_Ch03_CompletedNaturalFiltration
import Theorems.Thm_Kyprianou_Ch03_delayedNeighbourhoodClockBoundsV1
import Theorems.Thm_Kyprianou_Ch03_delayedOpenInfValueInClosedNeighbourhoodV1
import Theorems.Thm_Kyprianou_Ch03_monotoneStoppingSupValuesLimitV1
import Theorems.Thm_Kyprianou_Ch03_shrinkingClosedNeighbourhoodLimitV1
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
    ∀ᵐ w ∂P, (⨆ n, T n w) = sInf ((fun t : NNReal => (t : WithTop NNReal)) ''
      {t : NNReal | a ≤ t ∧ X t w ∈ B}) := by
  have hb w := Kyprianou.Ch03.delayedNeighbourhoodClockBoundsV1 X B a T hT w
  have hlim := Kyprianou.Ch03.monotoneStoppingSupValuesLimitV1 P F X hX hNatural T hStop
    (fun w => (hb w).1)
  filter_upwards [hlim, hX.cadlag_ae] with w hw hcad
  let S : WithTop NNReal := ⨆ n, T n w
  apply le_antisymm (hb w).2.1
  change _ ≤ S
  by_cases hS : S = ⊤
  · simp [hS]
  have hcoe (v : WithTop NNReal) (hv : v ≠ ⊤) :
      ((v.untopD 0 : NNReal) : WithTop NNReal) = v := by
    induction v using WithTop.recTopCoe with
    | top => exact (hv rfl).elim
    | coe v => rfl
  have hfin (n : ℕ) : T n w ≠ ⊤ :=
    ne_top_of_le_ne_top hS (le_iSup (fun n => T n w) n)
  have hmem (n : ℕ) : X ((T n w).untopD 0) w ∈
      Metric.cthickening (1 / ((n : ℝ) + 1)) B :=
    Kyprianou.Ch03.delayedOpenInfValueInClosedNeighbourhoodV1
      (fun t => X t w) (fun t => (hcad t).1) B _ a _
      ((hcoe _ (hfin n)).trans (hT n w))
  have hv : X (S.untopD 0) w ∈ B :=
    Kyprianou.Ch03.shrinkingClosedNeighbourhoodLimitV1 B hB _ _ (hw hS) hmem
  have ha : a ≤ S.untopD 0 := WithTop.coe_le_coe.mp (by rw [hcoe S hS]; exact (hb w).2.2)
  have hs : ((S.untopD 0 : NNReal) : WithTop NNReal) ∈
      ((fun t : NNReal => (t : WithTop NNReal)) '' {t : NNReal | a ≤ t ∧ X t w ∈ B}) :=
    ⟨S.untopD 0, ⟨ha, hv⟩, rfl⟩
  exact (sInf_le hs).trans_eq (hcoe S hS)
