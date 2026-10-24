-- Prove2me | solution 1 for HiringLP.Parallel.theorem_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-23T17:17:47.69666+00:00
-- url     : https://prove2.me/submissions/dbfa112c-d8fe-473c-a293-bf378817fdff

import Mathlib
import Definitions.Def_HiringLP_Parallel_Model
import Theorems.Thm_HiringLP_Parallel_hired_value_eq
import Theorems.Thm_HiringLP_Parallel_lemma_7
import Theorems.Thm_HiringLP_Parallel_lemma_8

open HiringLP.Parallel Finset

theorem solution {n k : ℕ} (I : Instance n k) (hI : I.Valid)
    (acc : Fin n → Finset (Fin k) → ℝ) (hacc : AccLaw I acc)
    (y : Fin n → Fin k → ℝ) (hopt : IsLPOpt I y)
    (μ : Finset (Fin n × Fin k) → ℝ) (hμ : IsGKPS y μ)
    (ord : Fin k → Equiv.Perm (Fin n)) (hord : IsValueOrder I ord) :
    (1 - Real.exp (-1)) * LPobj I y ≤ algReward I acc μ ord := by
  have hy : LPFeasible I y := hopt.1
  have hsplit : algReward I acc μ ord = ∑ j, Lpos I acc μ ord j := by
    unfold algReward Lpos
    rw [Finset.sum_comm (f := fun j Y => _)]
    refine Finset.sum_congr rfl (fun Y _ => ?_)
    rw [← Finset.mul_sum]
    congr 1
    rw [Finset.sum_comm (f := fun j A => _)]
    refine Finset.sum_congr rfl (fun A _ => ?_)
    rw [← Finset.mul_sum]
  have hobj : LPobj I y = ∑ j, Lstar I y j := rfl
  rw [hsplit, hobj, Finset.mul_sum]
  refine Finset.sum_le_sum (fun j _ => ?_)
  have h8 := lemma_8 I hI y hy j
  have h7 := lemma_7 I hI acc hacc y hy μ hμ j
  have hL := hired_value_eq I hI acc y hy μ hμ ord hord j
  rw [hL]; linarith
