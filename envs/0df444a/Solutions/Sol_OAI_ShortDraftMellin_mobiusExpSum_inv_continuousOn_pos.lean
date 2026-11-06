-- Prove2me | solution 1 for OAI.ShortDraftMellin.mobiusExpSum_inv_continuousOn_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:30:28.153206+00:00
-- url     : https://prove2.me/submissions/415f0d45-e744-4776-bcdd-8d854374b5f7

import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_ExponentialSmoothing
import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_LogProfiles
import Theorems.Thm_OAI_ShortDraftMellin_mobiusExpSum_continuousOn_pos

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
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :
    ContinuousOn (fun D : ℝ => mobiusExpSum χ D⁻¹) (Set.Ioi 0) := by
  apply (mobiusExpSum_continuousOn_pos χ).comp
    (continuousOn_inv₀.mono (by
      intro D hD
      exact ne_of_gt hD))
  intro D hD
  exact inv_pos.mpr (show 0 < D from hD)
end OAI.ShortDraftMellin
