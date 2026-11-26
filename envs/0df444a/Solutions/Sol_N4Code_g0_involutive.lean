-- Prove2me | solution 1 for N4Code.g0_involutive
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:19:10.800198+00:00
-- url     : https://prove2.me/submissions/1a58dec4-f1c7-43dd-a31c-a2fd993ac618

import Definitions.Def_N4Code_Compare
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Positivity
import Definitions.Def_N4Code_ZeroColumn
import Theorems.Thm_N4Code_dRowMin_flip_eq
import Theorems.Thm_N4Code_dRowMin_ge_one

set_option autoImplicit true
open scoped BigOperators
noncomputable section
open N4Code
set_option maxRecDepth 1000000
namespace N4Code
theorem _root_.solution {n : ℕ} (C : Code n) (s' : Column) (hO : (colZeros s').Nonempty)
    (hP : (colOnes s').Nonempty) (t : Fin n) (y : Word n) (hcol : C t = col0) :
    g0 C s' hO hP t (g0 C s' hO hP t y) = y := by
  by_cases hle : dOc C s' hO y ≤ dPc C s' hP y
  · simp [g0, hle]
  · have hgt : dPc C s' hP y < dOc C s' hO y := lt_of_not_ge hle
    have hg0 : g0 C s' hO hP t y = flipBit t y := by
      simp [g0, hle]
    rw [hg0]
    by_cases hyt : y t = true
    · have hdO := (dRowMin_flip_eq C (colZeros s') hO t y hcol).1 hyt
      have hdP := (dRowMin_flip_eq C (colOnes s') hP t y hcol).1 hyt
      have hgt' : dRowMin C (colOnes s') hP y < dRowMin C (colZeros s') hO y := by
        simpa [dOc, dPc] using hgt
      have hle' : ¬ dOc C s' hO (flipBit t y) ≤ dPc C s' hP (flipBit t y) := by
        unfold dOc dPc
        rw [hdO, hdP]
        have hPge : 1 ≤ dRowMin C (colOnes s') hP y :=
          dRowMin_ge_one C (colOnes s') hP t y hcol hyt
        omega
      simp [g0, hle', flipBit_involutive]
    · have hytf : y t = false := by
        simpa using hyt
      have hdO' := (dRowMin_flip_eq C (colZeros s') hO t y hcol).2 hytf
      have hdP' := (dRowMin_flip_eq C (colOnes s') hP t y hcol).2 hytf
      have hgt' : dRowMin C (colOnes s') hP y < dRowMin C (colZeros s') hO y := by
        simpa [dOc, dPc] using hgt
      have hle' : ¬ dOc C s' hO (flipBit t y) ≤ dPc C s' hP (flipBit t y) := by
        unfold dOc dPc
        rw [hdO', hdP']
        omega
      simp [g0, hle', flipBit_involutive]
end N4Code
