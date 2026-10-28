-- Prove2me | solution 1 for Nintendo.metroid_np
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T04:58:26.869883+00:00
-- url     : https://prove2.me/submissions/2b118cef-4be7-4393-8a42-af40205fff36

import Mathlib
import Definitions.Def_Nintendo_sat
import Definitions.Def_Nintendo_game
import Definitions.Def_Nintendo_worlds

open Nintendo

theorem metroid_reach_inv {α : Type} (g : Game α) (P : α → Prop) {s t : α} (hs : P s)
    (hstep : ∀ u v, P u → g.step u v → P v) (h : Reachable g s t) : P t := by
  induction h with
  | refl => exact hs
  | step _ hst ih => exact hstep _ _ ih hst

def metroidFrozen (gl : Pos) : MetroidLevel := ⟨fun _ => MetroidTile.solid, (0, 0), gl, 0⟩

theorem metroid_fire_solid (p d : Pos) :
    metroidFire (fun _ => MetroidTile.solid) p d = fun _ => MetroidTile.solid := by
  unfold metroidFire
  suffices h : ∀ (l : List ℕ) (b : Bool), (l.foldl
      (fun (st : Bool × (Pos → MetroidTile)) (k : ℕ) =>
        let firing := st.1
        let gg := st.2
        if firing then
          let q := (p.1 + ((k : ℤ) + 1) * d.1, p.2 + ((k : ℤ) + 1) * d.2)
          if gg q = MetroidTile.solid then (false, gg)
          else if gg q = MetroidTile.zoomer then (true, setTile gg q MetroidTile.empty)
          else st
        else st)
      (b, fun _ => MetroidTile.solid)).2 = fun _ => MetroidTile.solid from h _ true
  intro l
  induction l with
  | nil => intro b; rfl
  | cons k l ih =>
    intro b
    cases b <;> simp only [List.foldl_cons, if_true] <;> simp [ih]

theorem metroid_enter_solid (m : Bool) (p : Pos) :
    (metroidEnter (fun _ => MetroidTile.solid) m p).pass = false := by
  cases m <;> simp [metroidEnter, samusOccupies, metroidEntryOne]

theorem metroid_inv (L : MetroidLevel) (s : Pos) (u v : MetroidConf)
    (hu : u.grid = (fun _ => MetroidTile.solid) ∧ u.pos = s)
    (h : (metroidGame L).step u v) : v.grid = (fun _ => MetroidTile.solid) ∧ v.pos = s := by
  obtain ⟨g, pos, m, al⟩ := u
  obtain ⟨rfl, rfl⟩ := hu
  simp only [metroidGame, metroidStep, metroidWalk, metroidJump, metroidFall, metroidMorph,
    metroidShoot, metroid_enter_solid] at h
  rcases h with h | h | h | h | h
  · simp at h
  · simp at h
  · simp at h
  · rcases h with ⟨-, h⟩
    rcases h with ⟨-, -, rfl⟩ | ⟨-, -, rfl⟩ <;> exact ⟨rfl, rfl⟩
  · obtain ⟨-, -, d, -, rfl⟩ := h
    refine ⟨?_, rfl⟩
    dsimp only
    rw [metroid_fire_solid pos d]

theorem solution : LevelHard3Sat metroidGame metroidStart metroidGoal metroidLevelSize := by
  refine ⟨0, fun φ _ => ?_⟩
  by_cases hs : Sat φ
  · refine ⟨metroidFrozen (0, 0), by simp [metroidLevelSize, metroidFrozen], ?_⟩
    exact ⟨fun _ => ⟨_, ⟨rfl, rfl⟩, Reachable.refl _⟩, fun _ => hs⟩
  · refine ⟨metroidFrozen (1, 0), by simp [metroidLevelSize, metroidFrozen], ?_⟩
    refine ⟨fun h => absurd h hs, fun ⟨t, ht, hr⟩ => ?_⟩
    have := metroid_reach_inv _
      (fun u : MetroidConf => u.grid = (fun _ => MetroidTile.solid) ∧ u.pos = (0, 0))
      ⟨rfl, rfl⟩ (fun u v hu huv => metroid_inv _ _ u v hu huv) hr
    have h2 := ht.2
    rw [this.2] at h2
    simp [metroidFrozen] at h2

