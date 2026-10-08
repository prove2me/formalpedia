-- Prove2me | solution 1 for KelsoCrawford.NoCore.firm_j_unique_demands
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-06T23:52:52.360796+00:00
-- url     : https://prove2.me/submissions/c71bfd3f-cb02-4d84-a718-905fd6d32df5

import Mathlib
import Definitions.Def_KelsoCrawford_NoCore_Example
open KelsoCrawford.NoCore KelsoCrawford.Process
set_option maxRecDepth 4096
set_option maxHeartbeats 0
theorem solution :
    (∀ C : Finset (Fin 3), IsDemanded techJ ![3, 3, 3] C ↔ C = {0, 1}) ∧
    profit techJ {0, 1} ![3, 3, 3] = 3 / 2 ∧
    (∀ C : Finset (Fin 3), IsDemanded techJ ![3, 4, 3] C ↔ C = {2}) ∧
    profit techJ {2} ![3, 4, 3] = 5 / 4 := by
  have d1 : ∀ C : Finset (Fin 3), IsDemanded techJ ![3, 3, 3] C ↔ C = {0, 1} := by
    intro C
    constructor
    · intro h
      have h' := h {0, 1}
      fin_cases C <;> simp +decide [profit, techJ] at h' ⊢ <;> norm_num at h'
    · intro h; subst C; intro D; fin_cases D <;>
        simp +decide [profit, techJ] <;> norm_num
  have d2 : ∀ C : Finset (Fin 3), IsDemanded techJ ![3, 4, 3] C ↔ C = {2} := by
    intro C
    constructor
    · intro h
      have h' := h {2}
      fin_cases C <;> simp +decide [profit, techJ] at h' ⊢ <;> norm_num at h'
    · intro h; subst C; intro D; fin_cases D <;>
        simp +decide [profit, techJ] <;> norm_num
  refine ⟨d1, ?_, d2, ?_⟩ <;> simp +decide [profit, techJ] <;> norm_num
#print axioms solution
