-- Prove2me | solution 1 for Kyprianou.Ch06.finiteObservationTimeCompatibleIntervalSchedule
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T07:35:13.921979+00:00
-- url     : https://prove2.me/submissions/48949bde-2de8-47cf-9b6c-4c608df3b0f3

import Mathlib
import Theorems.Thm_Kyprianou_Ch06_finiteObservationTimesStrictGrid
import Theorems.Thm_Kyprianou_Ch06_finiteOrderedTimeGridCountTelescoping
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open scoped NNReal
set_option autoImplicit false

theorem solution
    (m : Nat) (times : Fin m → NNReal) :
    ∃ (k : Nat) (starts stops : Fin k → NNReal),
      (∀ j, starts j ≤ stops j) ∧
      (∀ j l : Fin k, j ≠ l →
        stops j ≤ starts l ∨ stops l ≤ starts j) ∧
      ∀ i : Fin m, ∃ J : Finset (Fin k),
        ∀ (F : NNReal → Nat), Monotone F → F 0 = 0 →
          F (times i) =
            ∑ j ∈ J, (F (stops j) - F (starts j)) := by
  classical
  obtain ⟨q, g, hStrict, hTimes, hZero⟩ :=
    Kyprianou.Ch06.finiteObservationTimesStrictGrid m times
  cases q with
  | zero =>
      obtain ⟨j, _⟩ := hZero
      exact Fin.elim0 j
  | succ k =>
      have hMono : Monotone g := hStrict.monotone
      have hFirst : g 0 = 0 := by
        obtain ⟨j, hj⟩ := hZero
        have hle : g (0 : Fin (k + 1)) ≤ g j :=
          hMono (Fin.zero_le j)
        have hle0 : g (0 : Fin (k + 1)) ≤ 0 := by
          simpa [hj] using hle
        exact le_antisymm hle0 (show (0 : NNReal) ≤ g 0 from zero_le)
      let starts : Fin k → NNReal := fun j => g j.castSucc
      let stops : Fin k → NNReal := fun j => g j.succ
      refine ⟨k, starts, stops, ?_, ?_, ?_⟩
      · intro j
        exact hMono (Fin.mk_le_mk.mpr (by omega))
      · intro j l hne
        by_cases hjl : j.val < l.val
        · left
          exact hMono (Fin.mk_le_mk.mpr (by omega))
        · right
          have hlj : l.val < j.val := by
            have heq : j.val ≠ l.val := by
              intro heq
              apply hne
              exact Fin.ext heq
            omega
          exact hMono (Fin.mk_le_mk.mpr (by omega))
      · intro i
        obtain ⟨r, hr⟩ := hTimes i
        let J : Finset (Fin k) :=
          Finset.univ.filter (fun j => j.val < r.val)
        refine ⟨J, ?_⟩
        intro F hF hFZero
        have hrle : r.val ≤ k := Nat.le_of_lt_succ r.isLt
        have hCount :=
          Kyprianou.Ch06.finiteOrderedTimeGridCountTelescoping
            k g hMono hFirst F hF hFZero r.val hrle
        have hIndex :
            (⟨r.val, Nat.lt_succ_of_le hrle⟩ : Fin (k + 1)) = r :=
          Fin.ext rfl
        simpa [J, starts, stops, hIndex, hr] using hCount
