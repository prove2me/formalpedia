-- Prove2me | solution 1 for HHRControl.PV.example_4_11
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-26T23:25:50.103508+00:00
-- url     : https://prove2.me/submissions/df2890ee-fa26-4b16-afb3-3d5fdeb8dfe8

import Mathlib
import Definitions.Def_HHRControl_PV_Elections

open HHRControl.PV Finset

def Pa411 : Fin 10 → Approval 3 := ![{2}, {2}, {2}, {2}, {0}, {0}, {0}, {1}, {1}, {1}]

theorem solution :
    (let P : Fin 10 → Approval 3 :=
        ![{2}, {2}, {2}, {2}, {0}, {0}, {0}, {1}, {1}, {1}];
      approval.winners 3 10 P univ univ = {2} ∧
      approval.winners 3 10 P univ {0, 1, 4, 5, 6} = {0} ∧
      approval.winners 3 10 P univ ({0, 1, 4, 5, 6} : Finset (Fin 10))ᶜ = {1} ∧
      ∀ rule : TieRule, twoStage rule approval P {0, 1, 4, 5, 6} = {0, 1}) ∧
    SusceptibleDC .TE approval ∧ SusceptibleDC .TP approval := by
  have h1 : approval.winners 3 10 Pa411 univ univ = {2} ∧
      approval.winners 3 10 Pa411 univ {0, 1, 4, 5, 6} = {0} ∧
      approval.winners 3 10 Pa411 univ ({0, 1, 4, 5, 6} : Finset (Fin 10))ᶜ = {1} := by decide
  have hTE : twoStage .TE approval Pa411 {0, 1, 4, 5, 6} = {0, 1} := by decide
  have hTP : twoStage .TP approval Pa411 {0, 1, 4, 5, 6} = {0, 1} := by decide
  have h2 : ∀ rule : TieRule, twoStage rule approval Pa411 {0, 1, 4, 5, 6} = {0, 1} := by
    intro rule; cases rule
    · exact hTE
    · exact hTP
  refine ⟨⟨h1.1, h1.2.1, h1.2.2, h2⟩, ?_, ?_⟩
  · refine ⟨3, 10, Pa411, 2, h1.1, ⟨{0, 1, 4, 5, 6}, ?_⟩⟩
    rw [hTE]; decide
  · refine ⟨3, 10, Pa411, 2, h1.1, ⟨{0, 1, 4, 5, 6}, ?_⟩⟩
    rw [hTP]; decide
