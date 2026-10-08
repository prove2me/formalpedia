-- Prove2me | solution 1 for KelsoCrawford.NoCore.firm_j_subadditive_not_gs
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T00:11:19.54192+00:00
-- url     : https://prove2.me/submissions/28779e8d-9497-4e4c-9bfe-d218bd83fb28

import Mathlib
import Definitions.Def_KelsoCrawford_NoCore_Notions
import Definitions.Def_KelsoCrawford_NoCore_Example
open KelsoCrawford.NoCore KelsoCrawford.Process
set_option maxRecDepth 4096
set_option maxHeartbeats 0
private theorem demand_result :
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

theorem solution :
    KelsoCrawford.Returns.Subadditive techJ ∧
    (∀ (i : Fin 3) (C : Finset (Fin 3)), i ∉ C →
      0 ≤ techJ (insert i C) - techJ C - noCoreMarket.σ i 0) ∧
    techJ ∅ = 0 ∧
    ¬ GrossSubstitutesOn techJ Set.univ := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro C D hd
    fin_cases C <;> fin_cases D <;>
      simp +decide [techJ] at hd ⊢ <;> norm_num
  · intro i C hi
    fin_cases i <;> fin_cases C <;>
      simp +decide [techJ, noCoreMarket] at hi ⊢ <;> norm_num
  · simp [techJ]
  · intro h
    obtain ⟨C, hd, hs⟩ := h ![3, 3, 3] (by simp) ![3, 4, 3] (by simp)
      (by intro i; fin_cases i <;> norm_num) {0, 1} (demand_result.1 _ |>.mpr rfl)
    have hc := demand_result.2.2.1 C |>.mp hd
    have hz := hs (show (0 : Fin 3) ∈ ({0, 1} : Finset (Fin 3)).filter
        (fun i => (![3, 4, 3] : Fin 3 → ℝ) i = ![3, 3, 3] i) by simp)
    simp +decide [hc] at hz
#print axioms solution
