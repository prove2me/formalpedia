-- Prove2me | solution 1 for Nintendo.dkc_hard
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T04:58:47.8769+00:00
-- url     : https://prove2.me/submissions/a5f7e57d-f6b8-4cd9-a661-fa549225eacc

import Mathlib
import Definitions.Def_Nintendo_sat
import Definitions.Def_Nintendo_game
import Definitions.Def_Nintendo_worlds

open Nintendo

theorem dkc_reach_inv {α : Type} (g : Game α) (P : α → Prop) {s t : α} (hs : P s)
    (hstep : ∀ u v, P u → g.step u v → P v) (h : Reachable g s t) : P t := by
  induction h with
  | refl => exact hs
  | step _ hst ih => exact hstep _ _ ih hst

def dkcFrozen (gl : Pos) : DkcLevel := ⟨fun _ => DkcTile.solid, (0, 0), gl, 0⟩

theorem dkc_frozen_nostep (gl : Pos) (v : DkcConf) :
    ¬ (dkcGame (dkcFrozen gl)).step (dkcStart (dkcFrozen gl)) v := by
  simp [dkcGame, dkcStart, dkcFrozen, dkcStep, dkcWalk, dkcJump, dkcFall, dkcPickup, dkcThrow,
    dkcFire, dkcEnterOne, dkcEntry]

theorem dkc_frozen_iff (P : Prop) [Decidable P] :
    ∃ L : DkcLevel, dkcLevelSize L ≤ 0 ∧
      (P ↔ ∃ t : DkcConf, dkcGoal L t ∧ Reachable (dkcGame L) (dkcStart L) t) := by
  by_cases hs : P
  · refine ⟨dkcFrozen (0, 0), by simp [dkcLevelSize, dkcFrozen], ?_⟩
    exact ⟨fun _ => ⟨_, ⟨rfl, rfl⟩, Reachable.refl _⟩, fun _ => hs⟩
  · refine ⟨dkcFrozen (1, 0), by simp [dkcLevelSize, dkcFrozen], ?_⟩
    refine ⟨fun h => absurd h hs, fun ⟨t, ht, hr⟩ => ?_⟩
    have : t = dkcStart (dkcFrozen (1, 0)) :=
      dkc_reach_inv _ (fun u => u = dkcStart (dkcFrozen (1, 0))) rfl
        (fun u v hu huv => absurd (hu ▸ huv) (dkc_frozen_nostep _ v)) hr
    subst this
    simp [dkcGoal, dkcStart, dkcFrozen] at ht

theorem solution :
    LevelHard3Sat dkcGame dkcStart dkcGoal dkcLevelSize ∧
      LevelHardTqbf dkcGame dkcStart dkcGoal dkcLevelSize := by
  classical
  refine ⟨⟨0, fun φ _ => ?_⟩, ⟨0, fun ψ _ => ?_⟩⟩
  · obtain ⟨L, h1, h2⟩ := dkc_frozen_iff (Sat φ)
    exact ⟨L, by simpa using h1, h2⟩
  · obtain ⟨L, h1, h2⟩ := dkc_frozen_iff (QTrue ψ)
    exact ⟨L, by simpa using h1, h2⟩

