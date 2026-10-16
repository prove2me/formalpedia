-- Prove2me | solution 1 for OAI.Problem310.OrderedRouting.chooseChild_eq_nondefault_iff
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T05:34:10.98085+00:00
-- url     : https://prove2.me/submissions/6970db5d-69de-4557-9877-54622e514d95

-- Generated from openai/math@1581d4c lean/OAI/MeasureTheory/DyadicAvoidance/OrderedRouting.lean:L13-L28
-- (upload_full_project.md Phase 4): solution for node OAI.Problem310.OrderedRouting.chooseChild_eq_nondefault_iff. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_DyadicAvoidance
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_PeriodicBasic
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_GridSeparation
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_FiniteTableModel
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_OrderedRouting

-- ---- from OAI.MeasureTheory.DyadicAvoidance.OrderedRouting ----
namespace OAI

namespace Problem310.OrderedRouting

variable {M : ℕ}

theorem chooseChild_eq_nondefault_iff (S : Fin M → Bool) (i : Fin M) :
    chooseChild S = i.castSucc ↔ S i = true ∧ ∀ j < i, S j = false := by
  rw [chooseChild, Fin.find_eq_iff]
  simp only [Fin.lastCases_castSucc]
  constructor
  · rintro ⟨hi, hmin⟩
    refine ⟨hi, fun j hj => ?_⟩
    have h := hmin j.castSucc (by simpa using hj)
    simpa using h
  · rintro ⟨hi, hmin⟩
    refine ⟨hi, fun j hj => ?_⟩
    induction j using Fin.lastCases with
    | last => exact ((not_lt_of_ge (Fin.le_last _)) hj).elim
    | cast j =>
      have h := hmin j (by simpa using hj)
      simp [h]

end Problem310.OrderedRouting

end OAI

-- ---- platform node ----
open OAI OAI.Problem310 OAI.Problem310.OrderedRouting


theorem solution : type_of% @_root_.OAI.Problem310.OrderedRouting.chooseChild_eq_nondefault_iff := @_root_.OAI.Problem310.OrderedRouting.chooseChild_eq_nondefault_iff
