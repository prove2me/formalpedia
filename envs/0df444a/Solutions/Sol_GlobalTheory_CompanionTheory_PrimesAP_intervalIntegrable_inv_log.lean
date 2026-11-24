-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.PrimesAP.intervalIntegrable_inv_log
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:17:19.569054+00:00
-- url     : https://prove2.me/submissions/7f98f78f-db5e-416f-90ea-d5634a617fcd

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AutomorphicForms__IsExcRat_5b5b692fee064c30
import Definitions.Def_Development_AutomorphicSpectrum_PublishedTheorems_PublishedGlobalResults_PrimesInProgressionsRelative
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_LFunctionConjEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ZeroFreePrincipal
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_PrimesInProgressionsRelativeOfTzRat

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset DirichletCharacter
open scoped Classical
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.PrimesAP
namespace GlobalTheory.CompanionTheory.PrimesAP
theorem _root_.solution {Y X : ℝ} (hY : 2 ≤ Y) (hX : 2 ≤ X) :
    IntervalIntegrable (fun t => 1 / Real.log t) MeasureTheory.volume Y X := by
  apply ContinuousOn.intervalIntegrable
  have : ∀ t ∈ Set.uIcc Y X, 2 ≤ t := fun t ht => le_trans (le_min hY hX) ht.1
  refine continuousOn_const.div (Real.continuousOn_log.mono ?_) ?_
  · intro t ht
    have := this t ht
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    linarith [this]
  · intro t ht
    exact (Real.log_pos (by linarith [this t ht])).ne'
end GlobalTheory.CompanionTheory.PrimesAP
