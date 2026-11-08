-- Prove2me | solution 1 for LosslessCond.eq_2_1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T14:59:25.869748+00:00
-- url     : https://prove2.me/submissions/d6957d5d-b437-44e9-9073-20aa90cda85e

import Mathlib
import Definitions.Def_DetCCHard_commCost

open Classical

namespace Aux_LosslessCond_eq_2_1

open DetCCHard

noncomputable def bobT {X Y : Type} (M : X → Y → Bool) (x : X) : List Y → Protocol X Y
  | [] => .leaf false
  | y0 :: l => .bob (fun y => decide (y = y0)) (bobT M x l) (.leaf (M x y0))

theorem bobT_eval {X Y : Type} (M : X → Y → Bool) (x x' : X) (y : Y) :
    ∀ l : List Y, y ∈ l → (bobT M x l).eval x' y = M x y
  | [], h => absurd h (List.not_mem_nil)
  | y0 :: l, h => by
    simp only [bobT, Protocol.eval]
    by_cases hy : y = y0
    · subst hy
      simp [Protocol.eval]
    · have hl : y ∈ l := by
        rcases List.mem_cons.mp h with h1 | h1
        · exact absurd h1 hy
        · exact h1
      simp only [hy, decide_false, Bool.false_eq_true, if_false]
      exact bobT_eval M x x' y l hl

noncomputable def aliceT {X Y : Type} (M : X → Y → Bool) (ly : List Y) : List X → Protocol X Y
  | [] => .leaf false
  | x0 :: l => .alice (fun x => decide (x = x0)) (aliceT M ly l) (bobT M x0 ly)

theorem aliceT_eval {X Y : Type} (M : X → Y → Bool) (ly : List Y) (x : X) (y : Y)
    (hy : y ∈ ly) : ∀ lx : List X, x ∈ lx → (aliceT M ly lx).eval x y = M x y
  | [], h => absurd h (List.not_mem_nil)
  | x0 :: l, h => by
    simp only [aliceT, Protocol.eval]
    by_cases hx : x = x0
    · subst hx
      simp only [decide_true, if_true]
      exact bobT_eval M x x y ly hy
    · have hl : x ∈ l := by
        rcases List.mem_cons.mp h with h1 | h1
        · exact absurd h1 hx
        · exact h1
      simp only [hx, decide_false, Bool.false_eq_true, if_false]
      exact aliceT_eval M ly x y hy l hl

end Aux_LosslessCond_eq_2_1

theorem solution {X Y : Type} [Fintype X] [Fintype Y] (M : X → Y → Bool)
    (U U' : Set X) (V V' : Set Y) (hU : U ⊆ U') (hV : V ⊆ V') :
    DetCCHard.commCost M U V ≤ DetCCHard.commCost M U' V' := by
  unfold DetCCHard.commCost
  set P := Aux_LosslessCond_eq_2_1.aliceT M (Finset.univ : Finset Y).toList
    (Finset.univ : Finset X).toList
  have hne : {n : ℕ | ∃ P : DetCCHard.Protocol X Y, P.depth ≤ n ∧
      ∀ x ∈ U', ∀ y ∈ V', P.eval x y = M x y}.Nonempty := by
    refine ⟨P.depth, P, le_rfl, fun x _ y _ => ?_⟩
    exact Aux_LosslessCond_eq_2_1.aliceT_eval M _ x y (by simp) _ (by simp)
  have hmem := Nat.sInf_mem hne
  apply Nat.sInf_le
  obtain ⟨Q, hQd, hQ⟩ := hmem
  exact ⟨Q, hQd, fun x hx y hy => hQ x (hU hx) y (hV hy)⟩
