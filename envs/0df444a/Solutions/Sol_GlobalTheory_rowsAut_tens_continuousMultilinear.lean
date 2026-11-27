-- Prove2me | solution 1 for GlobalTheory.rowsAut_tens_continuousMultilinear
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:44:51.328678+00:00
-- url     : https://prove2.me/submissions/16ce1455-b82f-4f4c-b3ff-958492f97c52

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_GlobAut
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsContinuousMultilinearMapOfInnerProd
import Theorems.Thm_GlobalTheory_exists_continuousMultilinearMap_of_inner_prod

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.MainNotions.S NumberField
open scoped InnerProductSpace
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ B : RowsAut, ∃ m : ContinuousMultilinearMap ℂ B.H B.Hs,
      (∀ x, m x = B.tens x) ∧ ∀ x, ‖B.tens x‖ = ∏ v, ‖x v‖ := fun B =>
  exists_continuousMultilinearMap_of_inner_prod B.tens B.tens_spec.1 B.tens_spec.2.2
end GlobalTheory
