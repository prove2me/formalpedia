-- Prove2me | solution 1 for GroverWiki.standardOracle_tensor_minus
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-15T19:07:00.246421+00:00
-- url     : https://prove2.me/submissions/1aafe778-92a9-4de0-a08e-365ec74a54fe

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic.FinCases
import Definitions.Def_GroverWiki_Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Matrix

open GroverWiki

theorem solution {N : ℕ} (f : Fin N → Fin 2) (x : Fin N) :
    standardOracle f *ᵥ tensorKet (ket x) minusState =
      tensorKet (phaseOracle f *ᵥ ket x) minusState := by
  classical
  ext p
  rcases p with ⟨i, j⟩
  simp only [phaseOracle, mulVec_diagonal]
  by_cases hi : i = x
  · subst i
    simp only [mulVec, dotProduct, standardOracle, tensorKet, ket,
      Fintype.sum_prod_type, Pi.single_apply, mul_ite, ite_mul]
    generalize hf : f x = z
    fin_cases z <;> fin_cases j <;>
      simp [Fin.sum_univ_two, minusState, hf]
  · simp [mulVec, dotProduct, standardOracle, tensorKet, ket,
      Fintype.sum_prod_type, Pi.single_apply, mul_ite, ite_mul, hi, Ne.symm hi]
