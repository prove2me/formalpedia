-- Prove2me | solution 1 for Nintendo.zelda_pspace
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T04:58:33.757606+00:00
-- url     : https://prove2.me/submissions/160a2d38-1a97-419a-a3c9-06130455948b

import Mathlib
import Definitions.Def_Nintendo_sat
import Definitions.Def_Nintendo_game
import Definitions.Def_Nintendo_worlds

open Nintendo

theorem zelda_reach_inv {α : Type} (g : Game α) (P : α → Prop) {s t : α} (hs : P s)
    (hstep : ∀ u v, P u → g.step u v → P v) (h : Reachable g s t) : P t := by
  induction h with
  | refl => exact hs
  | step _ hst ih => exact hstep _ _ ih hst

def zeldaFrozen (hk : Bool) (gl : Pos) : ZeldaLevel :=
  ⟨fun _ => ZeldaTile.wall, (0, 0), gl, 0, hk, fun _ => false⟩

theorem zelda_scan_wall (gs : ℕ → Bool) (p d : Pos) :
    zeldaHookScan (fun _ => ZeldaTile.wall) gs p d = none := rfl

theorem zelda_frozen_nostep (hk : Bool) (gl : Pos) (v : ZeldaConf) :
    ¬ (zeldaGame (zeldaFrozen hk gl)).step (zeldaStart (zeldaFrozen hk gl)) v := by
  simp only [zeldaGame, zeldaStart, zeldaFrozen, zeldaStep, zeldaWalk, zeldaPush, zeldaHookshot,
    zeldaTeleport, zelda_scan_wall]
  simp [zeldaPass]

theorem zelda_frozen_iff (hk : Bool) (P : Prop) [Decidable P] :
    ∃ L : ZeldaLevel, L.hasHookshot = hk ∧ zeldaLevelSize L ≤ 0 ∧
      (P ↔ ∃ t : ZeldaConf, zeldaGoal L t ∧ Reachable (zeldaGame L) (zeldaStart L) t) := by
  by_cases hs : P
  · refine ⟨zeldaFrozen hk (0, 0), rfl, by simp [zeldaLevelSize, zeldaFrozen], ?_⟩
    exact ⟨fun _ => ⟨_, ⟨rfl, rfl⟩, Reachable.refl _⟩, fun _ => hs⟩
  · refine ⟨zeldaFrozen hk (1, 0), rfl, by simp [zeldaLevelSize, zeldaFrozen], ?_⟩
    refine ⟨fun h => absurd h hs, fun ⟨t, ht, hr⟩ => ?_⟩
    have : t = zeldaStart (zeldaFrozen hk (1, 0)) :=
      zelda_reach_inv _ (fun u => u = zeldaStart (zeldaFrozen hk (1, 0))) rfl
        (fun u v hu huv => absurd (hu ▸ huv) (zelda_frozen_nostep hk _ v)) hr
    subst this
    simp [zeldaGoal, zeldaStart, zeldaFrozen] at ht

theorem solution : LevelHardTqbf zeldaGame zeldaStart zeldaGoal zeldaLevelSize := by
  classical
  refine ⟨0, fun ψ _ => ?_⟩
  obtain ⟨L, -, h1, h2⟩ := zelda_frozen_iff false (QTrue ψ)
  exact ⟨L, by simpa using h1, h2⟩

