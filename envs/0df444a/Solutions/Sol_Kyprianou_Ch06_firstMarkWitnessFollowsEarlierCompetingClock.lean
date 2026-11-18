-- Prove2me | solution 1 for Kyprianou.Ch06.firstMarkWitnessFollowsEarlierCompetingClock
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T11:11:21.463034+00:00
-- url     : https://prove2.me/submissions/02b10758-86b4-4db0-8596-68d0d1d84f32

import Mathlib.Data.NNReal.Defs
import Mathlib.MeasureTheory.SetSemiring
import Theorems.Thm_Kyprianou_Ch06_firstMarkedWinnerRegionFromCompetingSurvival
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Omega E : Type}
    (N : Omega → NNReal → Set E → Nat)
    (omega : Omega) (B D : Set E)
    (firstMark : Option E)
    (tauB : WithTop NNReal)
    (hFinite : tauB ≠ ⊤)
    (hEarlier : tauB <
      sInf ((fun u : NNReal => (u : WithTop NNReal)) ''
        {u : NNReal | 0 < u ∧ 0 < N omega u D}))
    (hInitD : N omega 0 D = 0)
    (hAdd : ∀ S T : Set E, Disjoint S T →
      N omega (tauB.untopD 0) (S ∪ T) =
        N omega (tauB.untopD 0) S +
          N omega (tauB.untopD 0) T)
    (hWitness : ∃ x : E, firstMark = some x ∧ x ∈ B ∪ D ∧
      0 < N omega (tauB.untopD 0) ({x} : Set E)) :
    firstMark ∈ (some '' B) := by
  obtain ⟨v, hv⟩ := WithTop.ne_top_iff_exists.mp hFinite
  have hVal : tauB.untopD 0 = v := by
    rw [← hv]
    exact WithTop.untopD_coe 0 v
  have hBefore : ((tauB.untopD 0 : NNReal) : WithTop NNReal) <
      sInf ((fun u : NNReal => (u : WithTop NNReal)) ''
        {u : NNReal | 0 < u ∧ 0 < N omega u D}) := by
    rw [hVal, hv]
    exact hEarlier
  rcases hWitness with ⟨x, hMark, hIn, hPositive⟩
  have hxB :=
    Kyprianou.Ch06.firstMarkedWinnerRegionFromCompetingSurvival
      N omega (tauB.untopD 0) x B D hIn hInitD hAdd
      hPositive hBefore
  rw [hMark]
  exact Set.mem_image_of_mem _ hxB
