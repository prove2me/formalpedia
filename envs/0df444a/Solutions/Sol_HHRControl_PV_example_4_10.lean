-- Prove2me | solution 1 for HHRControl.PV.example_4_10
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-26T23:24:05.080139+00:00
-- url     : https://prove2.me/submissions/c714666a-72e3-4f25-9005-b3aac86c4584

import Mathlib
import Definitions.Def_HHRControl_PV_Elections

open HHRControl.PV Finset

theorem rankingCode_injective' {m : ℕ} {r s : Ranking m} (h : rankingCode r = rankingCode s) :
    r = s := by
  unfold rankingCode at h
  have h2 := List.ofFn_injective h
  apply Equiv.symm_bijective.injective
  ext i
  exact congrFun h2 i

/-- Build a permutation of `Fin m` from a function and its inverse. -/
def mkPerm' {m : ℕ} (f g : Fin m → Fin m) (h1 : ∀ x, g (f x) = x) (h2 : ∀ x, f (g x) = x) :
    Ranking m := ⟨f, g, h1, h2⟩

-- the ranking whose code is `[a, b, c]` has `symm = ![a, b, c]`
def q201 : Ranking 3 := mkPerm' ![1,2,0] ![2,0,1] (by decide) (by decide)
def q210 : Ranking 3 := mkPerm' ![2,1,0] ![2,1,0] (by decide) (by decide)
def q102 : Ranking 3 := mkPerm' ![1,0,2] ![1,0,2] (by decide) (by decide)
def q120 : Ranking 3 := mkPerm' ![2,0,1] ![1,2,0] (by decide) (by decide)
def q012 : Ranking 3 := mkPerm' ![0,1,2] ![0,1,2] (by decide) (by decide)
def q021 : Ranking 3 := mkPerm' ![0,2,1] ![0,2,1] (by decide) (by decide)

def Pc410 : Fin 7 → Ranking 3 := ![q201, q201, q210, q102, q120, q012, q021]

theorem solution :
    (∀ P : Fin 7 → Ranking 3,
      (∀ v, rankingCode (P v) =
        ![[2, 0, 1], [2, 0, 1], [2, 1, 0], [1, 0, 2], [1, 2, 0], [0, 1, 2], [0, 2, 1]] v) →
        condorcet.winners 3 7 P univ univ = {2} ∧
        condorcet.winners 3 7 P univ {0, 6} = ∅ ∧
        condorcet.winners 3 7 P univ ({0, 6} : Finset (Fin 7))ᶜ = {1} ∧
        ∀ rule : TieRule, twoStage rule condorcet P {0, 6} ≠ {2}) ∧
    ∀ rule : TieRule, SusceptibleDC rule condorcet := by
  have hA : ∀ P : Fin 7 → Ranking 3,
      (∀ v, rankingCode (P v) =
        ![[2, 0, 1], [2, 0, 1], [2, 1, 0], [1, 0, 2], [1, 2, 0], [0, 1, 2], [0, 2, 1]] v) →
      P = Pc410 := by
    intro P hP
    have hc : ∀ v, rankingCode (Pc410 v) =
        ![[2, 0, 1], [2, 0, 1], [2, 1, 0], [1, 0, 2], [1, 2, 0], [0, 1, 2], [0, 2, 1]] v := by
      decide
    funext v
    exact rankingCode_injective' ((hP v).trans (hc v).symm)
  have h1 : condorcet.winners 3 7 Pc410 univ univ = {2} ∧
        condorcet.winners 3 7 Pc410 univ {0, 6} = ∅ ∧
        condorcet.winners 3 7 Pc410 univ ({0, 6} : Finset (Fin 7))ᶜ = {1} := by decide
  have hTE : twoStage .TE condorcet Pc410 {0, 6} ≠ {2} := by decide
  have hTP : twoStage .TP condorcet Pc410 {0, 6} ≠ {2} := by decide
  have h2 : ∀ rule : TieRule, twoStage rule condorcet Pc410 {0, 6} ≠ {2} := by
    intro rule; cases rule
    · exact hTE
    · exact hTP
  refine ⟨fun P hP => ?_, fun rule => ?_⟩
  · rw [hA P hP]; exact ⟨h1.1, h1.2.1, h1.2.2, h2⟩
  · exact ⟨3, 7, Pc410, 2, h1.1, ⟨{0, 6}, h2 rule⟩⟩
