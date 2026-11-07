-- Prove2me | solution 1 for OAI.TargetLocalReduction.dirichletTarget_of_localBound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T06:46:05.496008+00:00
-- url     : https://prove2.me/submissions/7c39e5a7-d0e7-47ca-8002-204f0a3acbec

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_ThetaLocalRows
import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_LocalNonvanishing
import Theorems.Thm_OAI_ShortDraftMellin_dirichlet_exp_zero_free_of_power_bound_only
import Theorems.Thm_OAI_ShortDraftMellin_principal_dirichlet_exp_zero_free_of_power_bound_only
import Theorems.Thm_OAI_ShortDraft_dirichlet_target_of_one_le_re


set_option autoImplicit false
open OAI
noncomputable section
open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open OAI.TargetLocalReduction
namespace OAI.TargetLocalReduction
theorem _root_.solution
    (hbound : LocalExponentialMobiusBound) : ShortDraft.DirichletTarget := by
  intro q _ χ ρ h23 hprincipal
  by_cases hρ : ρ.re < 1
  · obtain ⟨σ, hσpos, hσρ, hσone, htop⟩ := hbound q χ ρ h23 hρ
    by_cases hχ : χ = 1
    · subst χ
      have hρone : ρ ≠ 1 := by
        intro h
        exact hprincipal ⟨rfl, h⟩
      exact ShortDraftMellin.principal_dirichlet_exp_zero_free_of_power_bound_only
        q σ hσpos hσone htop ρ hσρ hρone
    · exact ShortDraftMellin.dirichlet_exp_zero_free_of_power_bound_only
        χ hχ σ hσpos hσone htop ρ hσρ
  · exact ShortDraft.dirichlet_target_of_one_le_re q χ ρ
      (le_of_not_gt hρ) hprincipal
end OAI.TargetLocalReduction
