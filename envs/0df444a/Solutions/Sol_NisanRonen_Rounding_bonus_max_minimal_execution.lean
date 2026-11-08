-- Prove2me | solution 1 for NisanRonen.Rounding.bonus_max_minimal_execution
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-08T00:15:12.914873+00:00
-- url     : https://prove2.me/submissions/d5b41cbe-cbac-491b-9757-90e50fcfd0f7

import Mathlib
import Definitions.Def_NisanRonen_Rounding_roundedMakespan
import Definitions.Def_NisanRonen_Rounding_corr
import Definitions.Def_NisanRonen_Rounding_corrStar

open NisanRonen.Rounding in
theorem solution {n k : ℕ} [NeZero n] {δ : ℝ} (hδ : 0 < δ)
    (x : Fin k → Fin n) (d : Fin n → Fin k → ℝ) (i : Fin n) (ti tt : Fin k → ℝ)
    (htt : ∀ j, x j = i → ti j ≤ tt j) :
    roundedMakespan δ x (corr i x d ti) ≤ roundedMakespan δ x (corr i x d tt) ∧
      corr i x d ti = corrStar x (Function.update d i ti) := by
  have hc : ∀ j, corr i x d ti j ≤ corr i x d tt j := by
    intro j
    unfold corr
    by_cases h : x j = i
    · rw [if_pos h, if_pos h]; exact htt j h
    · rw [if_neg h, if_neg h]
  have hr : ∀ j, roundUp δ (corr i x d ti j) ≤ roundUp δ (corr i x d tt j) := by
    intro j
    unfold roundUp
    apply mul_le_mul_of_nonneg_left _ hδ.le
    exact_mod_cast Int.ceil_mono (div_le_div_of_nonneg_right (hc j) hδ.le)
  refine ⟨?_, ?_⟩
  · unfold roundedMakespan makespan
    apply Finset.sup'_le
    intro m hm
    apply Finset.le_sup'_of_le _ hm
    unfold load
    exact Finset.sum_le_sum (fun j _ => hr j)
  · funext j
    unfold corr corrStar
    by_cases h : x j = i
    · rw [if_pos h, h, Function.update_self]
    · rw [if_neg h, Function.update_of_ne h]
