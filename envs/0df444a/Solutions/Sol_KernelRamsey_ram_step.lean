-- Prove2me | solution 1 for KernelRamsey.ram_step
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-24T17:00:42.679339+00:00
-- url     : https://prove2.me/submissions/762ec0c2-318f-4de0-a2b3-d5b4c6e9d545

import Mathlib
import Definitions.Def_KernelRamsey_Ram
import Theorems.Thm_KernelRamsey_nbhd_lt
import Theorems.Thm_KernelRamsey_card_split
import Theorems.Thm_KernelRamsey_nonnbr_false
open KernelRamsey Finset

theorem solution {t m : Nat} (h : Ram (t - 1) m) (ht : 1 ≤ t) : Ram t (m + t) := by
  classical
  intro V G A hA
  by_contra hno
  push Not at hno
  obtain ⟨hnoT, hnoI⟩ := hno
  have hpos : 0 < A.card := by omega
  obtain ⟨v, hv⟩ := Finset.card_pos.mp hpos
  have hN := nbhd_lt G hnoT hnoI hv
  have hs := card_split G A hv
  exact nonnbr_false G h ht hnoT hnoI hv (by omega)
