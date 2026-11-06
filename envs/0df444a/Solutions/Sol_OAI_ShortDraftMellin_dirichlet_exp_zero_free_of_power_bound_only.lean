-- Prove2me | solution 1 for OAI.ShortDraftMellin.dirichlet_exp_zero_free_of_power_bound_only
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:33:33.63492+00:00
-- url     : https://prove2.me/submissions/812c62fa-631b-4dbb-aea2-2135cb00a4a3

import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_ExponentialSmoothing
import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_LogProfiles
import Theorems.Thm_OAI_ShortDraftMellin_mobiusExpSum_inv_locallyIntegrableOn_pos
import Theorems.Thm_OAI_ShortDraftMellin_dirichlet_exp_zero_free_of_power_bound
import Theorems.Thm_OAI_ShortDraftMellin_mobiusExpSum_flat_at_zero


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
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (σ : ℝ) (hσpos : 0 < σ) (hσ : σ < 1)
    (htop : (fun D : ℝ => mobiusExpSum χ D⁻¹) =O[atTop]
      (fun D : ℝ => D ^ σ))
    (ρ : ℂ) (hρ : σ < ρ.re) : χ.LFunction ρ ≠ 0 := by
  exact dirichlet_exp_zero_free_of_power_bound χ hχ σ hσpos hσ
    (mobiusExpSum_inv_locallyIntegrableOn_pos χ) htop
    (mobiusExpSum_flat_at_zero χ) ρ hρ
end OAI.ShortDraftMellin
