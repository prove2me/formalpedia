-- Prove2me | solution 1 for OAI.CirculantHadamard.rowCirculant_gram_apply
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T09:49:32.056982+00:00
-- url     : https://prove2.me/submissions/3900c83c-9951-45d4-8a67-e08a0dc909e2

import Mathlib
import Definitions.Def_CirculantHadamard
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_Basic
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_Witnesses
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_MatrixBridge

open OAI OAI.CirculantHadamard
universe uR
open scoped BigOperators
variable {n : ℕ}
theorem solution [NeZero n] {R : Type uR} [CommRing R]
    (h : Fin n → R) (i a : Fin n) :
    (rowCirculant h * (rowCirculant h).transpose) i a =
      ∑ j, h j * h (j - (a - i)) := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, rowCirculant_apply]
  exact Fintype.sum_equiv (Equiv.subRight i) _ _ (fun k => by
    simp only [Equiv.subRight_apply]; congr 2; abel)
