-- Prove2me | solution 1 for OAI.ShortDraftMellin.mobiusExpSum_inv_locallyIntegrableOn_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:31:18.453201+00:00
-- url     : https://prove2.me/submissions/fbf332cc-2146-4174-a29f-226473d28f95

import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_ExponentialSmoothing
import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_LogProfiles
import Theorems.Thm_OAI_ShortDraftMellin_mobiusExpSum_inv_continuousOn_pos

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
    LocallyIntegrableOn
      (fun D : ℝ => mobiusExpSum χ D⁻¹) (Set.Ioi 0) :=
  (mobiusExpSum_inv_continuousOn_pos χ).locallyIntegrableOn measurableSet_Ioi
end OAI.ShortDraftMellin
