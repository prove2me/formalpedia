-- Prove2me | solution 1 for HHRControl.PV.example_4_9
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-26T23:18:53.492204+00:00
-- url     : https://prove2.me/submissions/0cb42b6f-d74c-4960-8f32-78b601a0e515

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

def p012' : Ranking 3 := mkPerm' ![0,1,2] ![0,1,2] (by decide) (by decide)
def p102' : Ranking 3 := mkPerm' ![1,0,2] ![1,0,2] (by decide) (by decide)
def p201' : Ranking 3 := mkPerm' ![1,2,0] ![2,0,1] (by decide) (by decide)

def Pc49 : Fin 5 → Ranking 3 := ![p012', p012', p102', p102', p201']
def Pc49' : Fin 4 → Ranking 3 := ![p012', p012', p102', p201']

theorem solution :
    (∀ P : Fin 5 → Ranking 3,
      (∀ v, rankingCode (P v) = ![[0, 1, 2], [0, 1, 2], [1, 0, 2], [1, 0, 2], [2, 0, 1]] v) →
        (2 : Fin 3) ∉ plurality.winners 3 5 P univ univ ∧
        plurality.winners 3 5 P univ {4} = {2} ∧
        plurality.winners 3 5 P univ ({4} : Finset (Fin 5))ᶜ = {0, 1} ∧
        twoStage .TE plurality P {4} = {2}) ∧
    (∀ P' : Fin 4 → Ranking 3,
      (∀ v, rankingCode (P' v) = ![[0, 1, 2], [0, 1, 2], [1, 0, 2], [2, 0, 1]] v) →
        plurality.winners 3 4 P' univ univ = {0} ∧
        nominees .TE plurality P' {0, 2} = ∅ ∧
        nominees .TE plurality P' ({0, 2} : Finset (Fin 4))ᶜ = ∅ ∧
        twoStage .TE plurality P' {0, 2} ≠ {0}) ∧
    SusceptibleCC .TE plurality ∧ SusceptibleDC .TE plurality := by
  have hA : ∀ P : Fin 5 → Ranking 3,
      (∀ v, rankingCode (P v) = ![[0, 1, 2], [0, 1, 2], [1, 0, 2], [1, 0, 2], [2, 0, 1]] v) →
      P = Pc49 := by
    intro P hP
    have hc : ∀ v, rankingCode (Pc49 v) =
        ![[0, 1, 2], [0, 1, 2], [1, 0, 2], [1, 0, 2], [2, 0, 1]] v := by decide
    funext v
    exact rankingCode_injective' ((hP v).trans (hc v).symm)
  have hB : ∀ P' : Fin 4 → Ranking 3,
      (∀ v, rankingCode (P' v) = ![[0, 1, 2], [0, 1, 2], [1, 0, 2], [2, 0, 1]] v) →
      P' = Pc49' := by
    intro P hP
    have hc : ∀ v, rankingCode (Pc49' v) =
        ![[0, 1, 2], [0, 1, 2], [1, 0, 2], [2, 0, 1]] v := by decide
    funext v
    exact rankingCode_injective' ((hP v).trans (hc v).symm)
  have h1 : (2 : Fin 3) ∉ plurality.winners 3 5 Pc49 univ univ ∧
        plurality.winners 3 5 Pc49 univ {4} = {2} ∧
        plurality.winners 3 5 Pc49 univ ({4} : Finset (Fin 5))ᶜ = {0, 1} ∧
        twoStage .TE plurality Pc49 {4} = {2} := by decide
  have h2 : plurality.winners 3 4 Pc49' univ univ = {0} ∧
        nominees .TE plurality Pc49' {0, 2} = ∅ ∧
        nominees .TE plurality Pc49' ({0, 2} : Finset (Fin 4))ᶜ = ∅ ∧
        twoStage .TE plurality Pc49' {0, 2} ≠ {0} := by decide
  refine ⟨fun P hP => ?_, fun P' hP' => ?_, ?_, ?_⟩
  · rw [hA P hP]; exact h1
  · rw [hB P' hP']; exact h2
  · refine ⟨3, 5, Pc49, 2, ?_, ⟨{4}, h1.2.2.2⟩⟩
    intro h
    exact h1.1 (h ▸ Finset.mem_singleton_self _)
  · exact ⟨3, 4, Pc49', 0, h2.1, ⟨{0, 2}, h2.2.2.2⟩⟩
