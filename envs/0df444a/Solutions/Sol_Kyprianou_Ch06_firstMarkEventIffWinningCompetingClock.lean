-- Prove2me | solution 1 for Kyprianou.Ch06.firstMarkEventIffWinningCompetingClock
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T11:23:58.452862+00:00
-- url     : https://prove2.me/submissions/f2233400-047c-4d76-a280-4f98e0c7f262

import Mathlib
import Theorems.Thm_Kyprianou_Ch06_firstMarkWitnessFollowsEarlierCompetingClock
import Theorems.Thm_Kyprianou_Ch06_positiveMarkedPointBeforeClockMinForcesEarlierRegion
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Omega E : Type}
    (N : Omega → NNReal → Set E → Nat)
    (omega : Omega) (B D : Set E) (firstMark : Option E)
    (t : NNReal) (ht : 0 < t)
    (hMin : (t : WithTop NNReal) =
      min
        (sInf ((fun u : NNReal => (u : WithTop NNReal)) ''
          {u : NNReal | 0 < u ∧ 0 < N omega u B}))
        (sInf ((fun u : NNReal => (u : WithTop NNReal)) ''
          {u : NNReal | 0 < u ∧ 0 < N omega u D})))
    (hNoTie :
      sInf ((fun u : NNReal => (u : WithTop NNReal)) ''
        {u : NNReal | 0 < u ∧ 0 < N omega u B}) ≠
      sInf ((fun u : NNReal => (u : WithTop NNReal)) ''
        {u : NNReal | 0 < u ∧ 0 < N omega u D}))
    (hInitD : N omega 0 D = 0)
    (hAdd : ∀ S T : Set E, Disjoint S T →
      N omega t (S ∪ T) = N omega t S + N omega t T)
    (hWitness : ∃ x : E, firstMark = some x ∧ x ∈ B ∪ D ∧
      0 < N omega t ({x} : Set E)) :
    (firstMark ∈ (some '' B) ↔
      sInf ((fun u : NNReal => (u : WithTop NNReal)) ''
        {u : NNReal | 0 < u ∧ 0 < N omega u B}) <
      sInf ((fun u : NNReal => (u : WithTop NNReal)) ''
        {u : NNReal | 0 < u ∧ 0 < N omega u D})) := by
  let tauB : WithTop NNReal :=
    sInf ((fun u : NNReal => (u : WithTop NNReal)) ''
      {u : NNReal | 0 < u ∧ 0 < N omega u B})
  let tauD : WithTop NNReal :=
    sInf ((fun u : NNReal => (u : WithTop NNReal)) ''
      {u : NNReal | 0 < u ∧ 0 < N omega u D})
  change firstMark ∈ (some '' B) ↔ tauB < tauD
  change (t : WithTop NNReal) = min tauB tauD at hMin
  change tauB ≠ tauD at hNoTie
  constructor
  · intro hImage
    rcases hWitness with ⟨x, hxMark, hxSet, hxPos⟩
    obtain ⟨y, hyB, hyMark⟩ := hImage
    have hxy : y = x := Option.some.inj (by simpa [hxMark] using hyMark)
    subst y
    exact
      Kyprianou.Ch06.positiveMarkedPointBeforeClockMinForcesEarlierRegion
        N omega B D t x ht hyB hAdd hxPos hMin hNoTie
  · intro hEarlier
    have hFinite : tauB ≠ ⊤ := by
      intro hTop
      simp [hTop] at hEarlier
    have hMinLeft : min tauB tauD = tauB :=
      min_eq_left (le_of_lt hEarlier)
    have hVal : tauB.untopD 0 = t := by
      have htau : tauB = (t : WithTop NNReal) := by
        rw [hMinLeft] at hMin
        exact hMin.symm
      rw [htau]
      exact WithTop.untopD_coe 0 t
    have hAt : ∀ S T : Set E, Disjoint S T →
      N omega (tauB.untopD 0) (S ∪ T) =
        N omega (tauB.untopD 0) S +
          N omega (tauB.untopD 0) T := by
      simpa only [hVal] using hAdd
    have hWitnessB : ∃ x : E,
        firstMark = some x ∧ x ∈ B ∪ D ∧
          0 < N omega (tauB.untopD 0) ({x} : Set E) := by
      simpa only [hVal] using hWitness
    exact
      Kyprianou.Ch06.firstMarkWitnessFollowsEarlierCompetingClock
        N omega B D firstMark tauB
        hFinite hEarlier hInitD hAt hWitnessB
