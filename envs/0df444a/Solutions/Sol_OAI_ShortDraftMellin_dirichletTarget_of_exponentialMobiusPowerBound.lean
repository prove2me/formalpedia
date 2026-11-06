-- Prove2me | solution 1 for OAI.ShortDraftMellin.dirichletTarget_of_exponentialMobiusPowerBound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:04:24.531719+00:00
-- url     : https://prove2.me/submissions/b5a670db-a0c2-487e-b263-917433d90565

import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_ExponentialSmoothing
import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_LogProfiles
import Theorems.Thm_OAI_ShortDraftMellin_dirichlet_exp_zero_free_of_power_bound_only
import Theorems.Thm_OAI_ShortDraftMellin_principal_dirichlet_exp_zero_free_of_power_bound_only
import Theorems.Thm_OAI_ShortDraft_dirichlet_target_of_one_le_re


set_option autoImplicit false
open OAI
open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open OAI.ShortDraftMellin
namespace OAI.ShortDraftMellin
theorem _root_.solution
    (hbound : ExponentialMobiusPowerBound) : ShortDraft.DirichletTarget := by
  intro q _ χ s h23 hprincipal
  by_cases hs : s.re < 1
  · let σ : ℝ := ((23 / 24 : ℝ) + s.re) / 2
    have hσ23 : (23 / 24 : ℝ) < σ := by dsimp [σ]; linarith
    have hσs : σ < s.re := by dsimp [σ]; linarith
    have hσone : σ < 1 := lt_trans hσs hs
    have hσpos : 0 < σ := lt_trans (by norm_num : (0 : ℝ) < 23 / 24) hσ23
    by_cases hχ : χ = 1
    · subst χ
      have hsone : s ≠ 1 := by
        intro h; exact hprincipal ⟨rfl, h⟩
      exact principal_dirichlet_exp_zero_free_of_power_bound_only q σ
        hσpos hσone (hbound q 1 σ hσ23 hσone) s hσs hsone
    · exact dirichlet_exp_zero_free_of_power_bound_only χ hχ σ
        hσpos hσone (hbound q χ σ hσ23 hσone) s hσs
  · exact ShortDraft.dirichlet_target_of_one_le_re q χ s
      (le_of_not_gt hs) hprincipal
end OAI.ShortDraftMellin
