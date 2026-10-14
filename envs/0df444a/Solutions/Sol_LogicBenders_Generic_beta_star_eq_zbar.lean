-- Prove2me | solution 1 for LogicBenders.Generic.beta_star_eq_zbar
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-13T01:56:34.670889+00:00
-- url     : https://prove2.me/submissions/a0b47e49-b468-4731-8170-8e236563228f

import Definitions.Def_LogicBenders_Generic_Setting
import Mathlib
import Theorems.Thm_LogicBenders_Generic_strong_inference_duality

open LogicBenders.Generic

theorem solution {X Y : Type*} (S : Set (X × Y)) (f : X → Y → ℝ)
    (cut : ℕ → Y → EReal) (k : ℕ) (hB1 : ∀ j ≤ k, ValidCut S f (cut j))
    (z : EReal) (yb : Y) (h : IsMasterOptimal cut k z yb)
    (hstop : ¬ ∃ β : EReal, IsDualFeasible S f yb β ∧ z < β) :
    subDualVal S f yb = z ∧ subVal S f yb = z := by
  have hz : IsDualFeasible S f yb z := by
    intro x hx
    rw [h.1]
    unfold masterLHS
    refine iSup_le fun j => iSup_le fun hj => ?_
    exact hB1 j (by simpa using Finset.mem_range.mp hj) x yb hx
  have hd : subDualVal S f yb = z := by
    apply le_antisymm
    · apply sSup_le
      intro b hb
      exact le_of_not_gt (fun hgt => hstop ⟨b, hb, hgt⟩)
    · exact le_sSup hz
  have hdual : subVal S f yb = subDualVal S f yb := by
    exact strong_inference_duality {x : X | (x, yb) ∈ S} (fun x => f x yb)
  exact ⟨hd, hdual.trans hd⟩
