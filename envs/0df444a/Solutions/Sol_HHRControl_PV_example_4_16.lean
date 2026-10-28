-- Prove2me | solution 1 for HHRControl.PV.example_4_16
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-26T23:27:35.847657+00:00
-- url     : https://prove2.me/submissions/48f1f4d6-9083-4428-8241-7aa5d6630110

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

def q021 : Ranking 3 := mkPerm' ![0,2,1] ![0,2,1] (by decide) (by decide)
def q102 : Ranking 3 := mkPerm' ![1,0,2] ![1,0,2] (by decide) (by decide)
def q201 : Ranking 3 := mkPerm' ![1,2,0] ![2,0,1] (by decide) (by decide)

def Pc416 : Fin 8 → Ranking 3 := ![q021, q021, q021, q102, q102, q201, q201, q201]
def Pc416' : Fin 10 → Ranking 3 :=
  ![q021, q021, q021, q102, q102, q201, q201, q201, q102, q201]

theorem solution :
    (∀ P : Fin 8 → Ranking 3,
      (∀ v, rankingCode (P v) = ![[0, 2, 1], [0, 2, 1], [0, 2, 1], [1, 0, 2], [1, 0, 2],
          [2, 0, 1], [2, 0, 1], [2, 0, 1]] v) →
        plurality.winners 3 8 P univ univ = {0, 2} ∧
        plurality.winners 3 8 P univ {0, 1, 5, 6, 7} = {2} ∧
        plurality.winners 3 8 P univ ({0, 1, 5, 6, 7} : Finset (Fin 8))ᶜ = {1} ∧
        twoStage .TP plurality P {0, 1, 5, 6, 7} = {2}) ∧
    (∀ P' : Fin 10 → Ranking 3,
      (∀ v, rankingCode (P' v) = ![[0, 2, 1], [0, 2, 1], [0, 2, 1], [1, 0, 2], [1, 0, 2],
          [2, 0, 1], [2, 0, 1], [2, 0, 1], [1, 0, 2], [2, 0, 1]] v) →
        plurality.winners 3 10 P' univ univ = {2} ∧
        plurality.winners 3 10 P' univ {0, 1, 2, 5, 6} = {0} ∧
        plurality.winners 3 10 P' univ ({0, 1, 2, 5, 6} : Finset (Fin 10))ᶜ = {1} ∧
        twoStage .TP plurality P' {0, 1, 2, 5, 6} = {0}) ∧
    SusceptibleCC .TP plurality ∧ SusceptibleDC .TP plurality := by
  have hA : ∀ P : Fin 8 → Ranking 3,
      (∀ v, rankingCode (P v) = ![[0, 2, 1], [0, 2, 1], [0, 2, 1], [1, 0, 2], [1, 0, 2],
          [2, 0, 1], [2, 0, 1], [2, 0, 1]] v) → P = Pc416 := by
    intro P hP
    have hc : ∀ v, rankingCode (Pc416 v) = ![[0, 2, 1], [0, 2, 1], [0, 2, 1], [1, 0, 2],
        [1, 0, 2], [2, 0, 1], [2, 0, 1], [2, 0, 1]] v := by decide
    funext v
    exact rankingCode_injective' ((hP v).trans (hc v).symm)
  have hB : ∀ P' : Fin 10 → Ranking 3,
      (∀ v, rankingCode (P' v) = ![[0, 2, 1], [0, 2, 1], [0, 2, 1], [1, 0, 2], [1, 0, 2],
          [2, 0, 1], [2, 0, 1], [2, 0, 1], [1, 0, 2], [2, 0, 1]] v) → P' = Pc416' := by
    intro P hP
    have hc : ∀ v, rankingCode (Pc416' v) = ![[0, 2, 1], [0, 2, 1], [0, 2, 1], [1, 0, 2],
        [1, 0, 2], [2, 0, 1], [2, 0, 1], [2, 0, 1], [1, 0, 2], [2, 0, 1]] v := by decide
    funext v
    exact rankingCode_injective' ((hP v).trans (hc v).symm)
  have h1 : plurality.winners 3 8 Pc416 univ univ = {0, 2} ∧
        plurality.winners 3 8 Pc416 univ {0, 1, 5, 6, 7} = {2} ∧
        plurality.winners 3 8 Pc416 univ ({0, 1, 5, 6, 7} : Finset (Fin 8))ᶜ = {1} ∧
        twoStage .TP plurality Pc416 {0, 1, 5, 6, 7} = {2} := by decide
  have h2 : plurality.winners 3 10 Pc416' univ univ = {2} ∧
        plurality.winners 3 10 Pc416' univ {0, 1, 2, 5, 6} = {0} ∧
        plurality.winners 3 10 Pc416' univ ({0, 1, 2, 5, 6} : Finset (Fin 10))ᶜ = {1} ∧
        twoStage .TP plurality Pc416' {0, 1, 2, 5, 6} = {0} := by decide
  refine ⟨fun P hP => ?_, fun P' hP' => ?_, ?_, ?_⟩
  · rw [hA P hP]; exact h1
  · rw [hB P' hP']; exact h2
  · refine ⟨3, 8, Pc416, 2, ?_, ⟨{0, 1, 5, 6, 7}, h1.2.2.2⟩⟩
    rw [h1.1]; decide
  · refine ⟨3, 10, Pc416', 2, h2.1, ⟨{0, 1, 2, 5, 6}, ?_⟩⟩
    rw [h2.2.2.2]; decide
