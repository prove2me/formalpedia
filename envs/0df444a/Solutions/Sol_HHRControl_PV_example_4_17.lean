-- Prove2me | solution 1 for HHRControl.PV.example_4_17
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-26T23:29:05.744461+00:00
-- url     : https://prove2.me/submissions/afce0183-9561-4cde-91fd-b567bf4f56df

import Mathlib
import Definitions.Def_HHRControl_PV_Elections

open HHRControl.PV Finset

def Pa417 : Fin 8 → Approval 3 := ![{0}, {0}, {0}, {1}, {1}, {2}, {2}, {2}]

theorem solution :
    (let P : Fin 8 → Approval 3 := ![{0}, {0}, {0}, {1}, {1}, {2}, {2}, {2}];
      approval.winners 3 8 P univ univ = {0, 2} ∧
      approval.winners 3 8 P univ {0, 1, 5, 6, 7} = {2} ∧
      approval.winners 3 8 P univ ({0, 1, 5, 6, 7} : Finset (Fin 8))ᶜ = {1} ∧
      ∀ rule : TieRule, twoStage rule approval P {0, 1, 5, 6, 7} = {2}) ∧
    SusceptibleCC .TE approval ∧ SusceptibleCC .TP approval := by
  have h1 : approval.winners 3 8 Pa417 univ univ = {0, 2} ∧
      approval.winners 3 8 Pa417 univ {0, 1, 5, 6, 7} = {2} ∧
      approval.winners 3 8 Pa417 univ ({0, 1, 5, 6, 7} : Finset (Fin 8))ᶜ = {1} := by decide
  have hTE : twoStage .TE approval Pa417 {0, 1, 5, 6, 7} = {2} := by decide
  have hTP : twoStage .TP approval Pa417 {0, 1, 5, 6, 7} = {2} := by decide
  have h2 : ∀ rule : TieRule, twoStage rule approval Pa417 {0, 1, 5, 6, 7} = {2} := by
    intro rule; cases rule
    · exact hTE
    · exact hTP
  have hne : approval.winners 3 8 Pa417 univ univ ≠ {2} := by rw [h1.1]; decide
  exact ⟨⟨h1.1, h1.2.1, h1.2.2, h2⟩, ⟨3, 8, Pa417, 2, hne, ⟨{0, 1, 5, 6, 7}, hTE⟩⟩,
    ⟨3, 8, Pa417, 2, hne, ⟨{0, 1, 5, 6, 7}, hTP⟩⟩⟩
