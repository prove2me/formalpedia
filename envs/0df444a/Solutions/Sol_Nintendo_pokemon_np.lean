-- Prove2me | solution 1 for Nintendo.pokemon_np
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T04:58:19.817919+00:00
-- url     : https://prove2.me/submissions/aac9d8c2-2ef5-4989-91ce-ed504d9d1a1e

import Mathlib
import Definitions.Def_Nintendo_sat
import Definitions.Def_Nintendo_game
import Definitions.Def_Nintendo_worlds

open Nintendo

theorem poke_reach_inv {α : Type} (g : Game α) (P : α → Prop) {s t : α} (hs : P s)
    (hstep : ∀ u v, P u → g.step u v → P v) (h : Reachable g s t) : P t := by
  induction h with
  | refl => exact hs
  | step _ hst ih => exact hstep _ _ ih hst

def pokeFrozen (gl : Pos) : PokeLevel := ⟨fun _ => true, [], (0, 0), gl, 0⟩

theorem poke_frozen_nostep (gl : Pos) (v : PokeConf) :
    ¬ (pokeGame (pokeFrozen gl)).step (pokeStart (pokeFrozen gl)) v := by
  simp [pokeGame, pokeStart, pokeFrozen, pokeStep, pokeFirstEncounter]

theorem solution : LevelHard3Sat pokeGame pokeStart pokeGoal pokeLevelSize := by
  refine ⟨0, fun φ _ => ?_⟩
  by_cases hs : Sat φ
  · refine ⟨pokeFrozen (0, 0), by simp [pokeLevelSize, pokeFrozen], ?_⟩
    exact ⟨fun _ => ⟨_, ⟨rfl, rfl⟩, Reachable.refl _⟩, fun _ => hs⟩
  · refine ⟨pokeFrozen (1, 0), by simp [pokeLevelSize, pokeFrozen], ?_⟩
    refine ⟨fun h => absurd h hs, fun ⟨t, ht, hr⟩ => ?_⟩
    have : t = pokeStart (pokeFrozen (1, 0)) :=
      poke_reach_inv _ (fun u => u = pokeStart (pokeFrozen (1, 0))) rfl
        (fun u v hu huv => absurd (hu ▸ huv) (poke_frozen_nostep _ v)) hr
    subst this
    simp [pokeGoal, pokeStart, pokeFrozen] at ht

