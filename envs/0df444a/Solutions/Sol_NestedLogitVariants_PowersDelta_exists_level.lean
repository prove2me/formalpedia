-- Prove2me | solution 1 for NestedLogitVariants.PowersDelta.exists_level
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-07T13:20:57.444096+00:00
-- url     : https://prove2.me/submissions/b75d0eee-4b87-44b0-8773-2b77cdfaf2e6

import Mathlib
import Definitions.Def_NestedLogitVariants_PowersDelta_Levels

set_option autoImplicit false

open NestedLogitVariants.PowersDelta

theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ} [NeZero n] (I : Instance ι n)
    (hI : I.Standing) (γbar : ℝ) (hγbar : IsGreatest (Set.range I.γ) γbar) (hγbar1 : 1 < γbar)
    (δ : ℝ) (hδ : 1 < δ)
    (i : ι) (S : Finset (Fin n)) (hS : S.Nonempty) :
    ∃ l : ℤ, lL I i δ ≤ l ∧ l ≤ lU I i δ ∧ InLevel I i δ l S := by
  have hvL : 0 < vL I i := by
    apply add_pos_of_nonneg_of_pos (hI.vnp_nonneg i)
    exact (Finset.lt_inf'_iff _).2 fun j _ => hI.v_pos i j
  have hlow : vL I i ≤ V I i S := by
    obtain ⟨j, hj⟩ := hS
    apply add_le_add le_rfl
    exact (Finset.inf'_le _ (Finset.mem_univ j)).trans
      (Finset.single_le_sum (fun k _ => (hI.v_pos i k).le) hj)
  have hupp : V I i S ≤ vU I i := by
    apply add_le_add le_rfl
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
      (fun j _ _ => (hI.v_pos i j).le)
  have hv : 0 < V I i S := hvL.trans_le hlow
  refine ⟨⌈Real.logb δ (V I i S)⌉, ?_, ?_, ?_, ?_⟩
  · exact Int.ceil_mono (Real.logb_le_logb_of_le hδ hvL hlow)
  · exact Int.ceil_mono (Real.logb_le_logb_of_le hδ hv hupp)
  · rw [← Real.rpow_intCast]
    apply (Real.le_logb_iff_rpow_le hδ hv).mp
    have hc := Int.ceil_lt_add_one (Real.logb δ (V I i S))
    push_cast
    linarith
  · rw [← Real.rpow_intCast]
    exact (Real.logb_le_iff_le_rpow hδ hv).mp (Int.le_ceil _)
