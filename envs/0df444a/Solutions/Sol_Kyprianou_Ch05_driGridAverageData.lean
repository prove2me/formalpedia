-- Prove2me | solution 1 for Kyprianou.Ch05.driGridAverageData
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T18:48:10.022807+00:00
-- url     : https://prove2.me/submissions/5f3a15b1-434c-481f-9422-ac9017d83aba

import Mathlib
import Definitions.Def_Kyprianou_Ch05_RenewalMeasure
import Theorems.Thm_Kyprianou_Ch05_driNonnegativeGridOscillationBudget
import Theorems.Thm_Kyprianou_Ch05_driGridCellAverageOscillation
import Theorems.Thm_Kyprianou_Ch05_gridAverageSeries
open MeasureTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch05

/-- Combine cell averages, closed-cell oscillations and the small grid budget. -/
theorem solution
    (h : Real → Real) (hm : Measurable h)
    (hDRI : DirectlyRiemannIntegrable h) (eps : Real) (heps : 0 < eps) :
    ∃ d : Real, 0 < d ∧ ∃ c e : Nat → Real,
      Summable (fun k => |c k|) ∧ Summable (fun k => |e k|) ∧
      (∀ (k : Nat) (y : Real), y ∈ Set.Ico ((k : Real)*d) (((k : Real)+1)*d) →
        |h y-c k| ≤ e k) ∧
      (∑' k : Nat, c k)*d = (∫ y in Set.Ici 0, h y ∂volume) ∧
      (∑' k : Nat, e k)*d < eps := by
  obtain ⟨d,hd,he,hbudget⟩ := driNonnegativeGridOscillationBudget h hDRI eps heps
  obtain ⟨hc,hsum⟩ := gridAverageSeries h hDRI.1 d hd
  exact ⟨d, hd, _, _, hc, he,
    fun k y hy => driGridCellAverageOscillation h hDRI.1 hDRI.2.1 d hd k y hy,
    hsum, hbudget⟩
