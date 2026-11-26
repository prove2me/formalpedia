-- Prove2me | solution 1 for N4Code.zero_closer
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:23:14.152813+00:00
-- url     : https://prove2.me/submissions/8c825160-4cf0-4c37-8f2b-7e878f40b85d

import Definitions.Def_N4Code_Compare
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Positivity
import Definitions.Def_N4Code_ZeroColumn
import Theorems.Thm_N4Code_dRowMin_flip_eq
import Theorems.Thm_N4Code_dCode_replace_0
import Theorems.Thm_N4Code_dRowMin_ge_one
import Theorems.Thm_N4Code_dCode_eq_min_dOc_dPc

set_option autoImplicit true
open scoped BigOperators
noncomputable section
open N4Code
set_option maxRecDepth 1000000
namespace N4Code
theorem _root_.solution {n : ℕ} (C : Code n) (t : Fin n) (s' : Column) (hcol : C t = col0)
    (hO : (colZeros s').Nonempty) (hP : (colOnes s').Nonempty) (y : Word n)
    (hS : Y3c C s' hO hP t y) :
    dCode C y = dCode (replaceColumn C t s') (g0 C s' hO hP t y) + 1 := by
  rcases hS with ⟨hyt, hEq⟩
  have hdC : dCode C y = dOc C s' hO y := by
    rw [dCode_eq_min_dOc_dPc C s' hO hP, hEq]
    simp
  have hg0 : g0 C s' hO hP t y = y := by
    simp [g0, hEq]
  have hdP := (dRowMin_flip_eq C (colOnes s') hP t y hcol).1 hyt
  have hdC' : dCode (replaceColumn C t s') y = dOc C s' hO y - 1 := by
    rw [dCode_replace_0 C t s' hcol hO hP y]
    change min (dOc C s' hO y) (dRowMin C (colOnes s') hP (flipBit t y)) = dOc C s' hO y - 1
    rw [hdP]
    change min (dOc C s' hO y) (dPc C s' hP y - 1) = dOc C s' hO y - 1
    rw [hEq.symm]
    have hPge : 1 ≤ dOc C s' hO y := by
      rw [hEq]
      exact dRowMin_ge_one C (colOnes s') hP t y hcol hyt
    omega
  rw [hdC, hg0, hdC']
  have hPge : 1 ≤ dOc C s' hO y := by
    rw [hEq]
    exact dRowMin_ge_one C (colOnes s') hP t y hcol hyt
  omega
end N4Code
