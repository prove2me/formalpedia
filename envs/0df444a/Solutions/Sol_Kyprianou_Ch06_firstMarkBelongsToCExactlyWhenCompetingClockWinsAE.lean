-- Prove2me | solution 1 for Kyprianou.Ch06.firstMarkBelongsToCExactlyWhenCompetingClockWinsAE
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T12:14:16.964405+00:00
-- url     : https://prove2.me/submissions/1122e748-eb3b-4e69-ad0e-f230293f01e7

import Mathlib
import Definitions.Def_Kyprianou_Ch06_MarkedPoissonPointProcess
import Theorems.Thm_Kyprianou_Ch06_firstArrivalPartitionedByMarkMembership
import Theorems.Thm_Kyprianou_Ch06_firstMarkEventIffWinningCompetingClock
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Omega E : Type} [MeasurableSpace Omega] [MeasurableSpace E]
    (P : Measure Omega) (n : Measure E)
    (N : Omega → NNReal → Set E → Nat)
    (A C : Set E) (firstMark : Omega → Option E)
    (hPPP : Kyprianou.Ch06.IsMarkedPoissonPointProcess P n N)
    (hMark : ∀ᵐ omega ∂P,
      let sigma : WithTop NNReal :=
        sInf ((fun t : NNReal => (t : WithTop NNReal)) ''
          {t : NNReal | 0 < t ∧ 0 < N omega t A})
      (sigma = ⊤ → firstMark omega = none) ∧
      (sigma ≠ ⊤ → ∃ x : E,
        firstMark omega = some x ∧ x ∈ A ∧
        0 < N omega (sigma.untopD 0) {x})) :
    ∀ᵐ omega ∂P,
      let sigma : WithTop NNReal :=
        sInf ((fun t : NNReal => (t : WithTop NNReal)) ''
          {t : NNReal | 0 < t ∧ 0 < N omega t A})
      let tauB : WithTop NNReal :=
        sInf ((fun t : NNReal => (t : WithTop NNReal)) ''
          {t : NNReal | 0 < t ∧ 0 < N omega t (A ∩ C)})
      let tauD : WithTop NNReal :=
        sInf ((fun t : NNReal => (t : WithTop NNReal)) ''
          {t : NNReal | 0 < t ∧ 0 < N omega t (A \ C)})
      sigma ≠ ⊤ → 0 < sigma.untopD 0 → tauB ≠ tauD →
      (firstMark omega ∈ (some '' (A ∩ C)) ↔ tauB < tauD) := by
  have hPartition :=
    Kyprianou.Ch06.firstArrivalPartitionedByMarkMembership
      P n N hPPP A C
  filter_upwards [hPPP.2.1, hMark, hPartition] with omega hPath hWitness hPart
  dsimp only
  intro hFinite hPositive hNoTie
  let tauA : WithTop NNReal :=
    sInf ((fun t : NNReal => (t : WithTop NNReal)) ''
      {t : NNReal | 0 < t ∧ 0 < N omega t A})
  let tauB : WithTop NNReal :=
    sInf ((fun t : NNReal => (t : WithTop NNReal)) ''
      {t : NNReal | 0 < t ∧ 0 < N omega t (A ∩ C)})
  let tauD : WithTop NNReal :=
    sInf ((fun t : NNReal => (t : WithTop NNReal)) ''
      {t : NNReal | 0 < t ∧ 0 < N omega t (A \ C)})
  change tauA ≠ ⊤ at hFinite
  change 0 < tauA.untopD 0 at hPositive
  change tauB ≠ tauD at hNoTie
  have hPart' : tauA = min tauB tauD := hPart
  obtain ⟨v, hv⟩ := WithTop.ne_top_iff_exists.mp hFinite
  have hVal : tauA.untopD 0 = v := by
    rw [← hv]
    exact WithTop.untopD_coe 0 v
  have hTauMin :
      ((tauA.untopD 0 : NNReal) : WithTop NNReal) =
        min tauB tauD := by
    rw [hVal, hv]
    exact hPart'
  have hSplit : (A ∩ C) ∪ (A \ C) = A := by
    ext x
    simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_diff]
    tauto
  have hCount : ∀ S T : Set E, Disjoint S T →
      N omega (tauA.untopD 0) (S ∪ T) =
      N omega (tauA.untopD 0) S +
      N omega (tauA.untopD 0) T := hPath.2.1 _
  obtain ⟨x, hx, hxA, hxPos⟩ := hWitness.2 hFinite
  have hxSplit : x ∈ (A ∩ C) ∪ (A \ C) := by
    simpa only [hSplit] using hxA
  change firstMark omega ∈ (some '' (A ∩ C)) ↔ tauB < tauD
  exact
    Kyprianou.Ch06.firstMarkEventIffWinningCompetingClock
      N omega (A ∩ C) (A \ C) (firstMark omega)
      (tauA.untopD 0) hPositive hTauMin hNoTie
      (hPath.1 _) hCount ⟨x, hx, hxSplit, hxPos⟩
