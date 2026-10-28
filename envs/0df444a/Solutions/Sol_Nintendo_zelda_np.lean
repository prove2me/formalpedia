-- Prove2me | solution 1 for Nintendo.zelda_np
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T04:58:40.723613+00:00
-- url     : https://prove2.me/submissions/2ef385ea-bf3d-4005-960d-bd0e3650b502

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

theorem zelda_np_aux (b : Bool) :
    LevelHard3Sat (fun L : ZeldaLevel => zeldaGame {L with hasHookshot := b})
       (fun L : ZeldaLevel => zeldaStart {L with hasHookshot := b})
       (fun L : ZeldaLevel => zeldaGoal {L with hasHookshot := b})
       (fun L : ZeldaLevel => zeldaLevelSize {L with hasHookshot := b}) := by
  classical
  refine ⟨0, fun φ _ => ?_⟩
  obtain ⟨L, hL, h1, h2⟩ := zelda_frozen_iff b (Sat φ)
  have hE : ({L with hasHookshot := b} : ZeldaLevel) = L := by
    cases L; simp only at hL; subst hL; rfl
  refine ⟨L, ?_, ?_⟩
  · simp only [hE]; simpa using h1
  · simp only [hE]; exact h2

theorem solution :
    (LevelHard3Sat (fun L : ZeldaLevel => zeldaGame {L with hasHookshot := false})
       (fun L : ZeldaLevel => zeldaStart {L with hasHookshot := false})
       (fun L : ZeldaLevel => zeldaGoal {L with hasHookshot := false})
       (fun L : ZeldaLevel => zeldaLevelSize {L with hasHookshot := false})) ∧
    (LevelHard3Sat (fun L : ZeldaLevel => zeldaGame {L with hasHookshot := true})
       (fun L : ZeldaLevel => zeldaStart {L with hasHookshot := true})
       (fun L : ZeldaLevel => zeldaGoal {L with hasHookshot := true})
       (fun L : ZeldaLevel => zeldaLevelSize {L with hasHookshot := true})) :=
  ⟨zelda_np_aux false, zelda_np_aux true⟩

