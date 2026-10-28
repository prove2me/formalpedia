-- Prove2me | solution 1 for Nintendo.mario_np
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T04:58:12.681481+00:00
-- url     : https://prove2.me/submissions/48a82a99-016d-4707-86fd-dc5f2ab2109b

import Mathlib
import Definitions.Def_Nintendo_sat
import Definitions.Def_Nintendo_game
import Definitions.Def_Nintendo_worlds

open Nintendo

theorem mario_reach_inv {α : Type} (g : Game α) (P : α → Prop) {s t : α} (hs : P s)
    (hstep : ∀ u v, P u → g.step u v → P v) (h : Reachable g s t) : P t := by
  induction h with
  | refl => exact hs
  | step _ hst ih => exact hstep _ _ ih hst

def marioFrozen (gl : Pos) : MarioLevel := ⟨fun _ => MarioTile.solid, (0, 0), gl, 0⟩

theorem mario_frozen_nostep (gl : Pos) (v : MarioConf) :
    ¬ (marioGame (marioFrozen gl)).step (marioStart (marioFrozen gl)) v := by
  simp [marioGame, marioStart, marioFrozen, marioStep, marioWalk, marioJump, marioFall, marioHit,
    marioEnterCells, marioEnterOne, marioEntry]

theorem solution : LevelHard3Sat marioGame marioStart marioGoal marioLevelSize := by
  refine ⟨0, fun φ _ => ?_⟩
  by_cases hs : Sat φ
  · refine ⟨marioFrozen (0, 0), by simp [marioLevelSize, marioFrozen], ?_⟩
    exact ⟨fun _ => ⟨_, ⟨rfl, rfl⟩, Reachable.refl _⟩, fun _ => hs⟩
  · refine ⟨marioFrozen (1, 0), by simp [marioLevelSize, marioFrozen], ?_⟩
    refine ⟨fun h => absurd h hs, fun ⟨t, ht, hr⟩ => ?_⟩
    have : t = marioStart (marioFrozen (1, 0)) :=
      mario_reach_inv _ (fun u => u = marioStart (marioFrozen (1, 0))) rfl
        (fun u v hu huv => absurd (hu ▸ huv) (mario_frozen_nostep _ v)) hr
    subst this
    simp [marioGoal, marioStart, marioFrozen] at ht

