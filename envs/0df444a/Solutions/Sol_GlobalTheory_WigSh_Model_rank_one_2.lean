-- Prove2me | solution 2 for GlobalTheory.WigSh.Model.rank_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:35:37.072979+00:00
-- url     : https://prove2.me/submissions/9c0acd78-c67b-4e33-a411-164195e0d39e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_Imports
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_FactorNonneg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open GlobalTheory GlobalTheory.WigSh GlobalTheory.WigSh.Model
namespace GlobalTheory.WigSh.Model
theorem _root_.solution (L : Fin 1 → ℤ) (M : Fin 0 → ℤ) : wP L M 0 = 1 ∧ wM L M 0 = 1 := by
  constructor <;> simp [GlobalTheory.WigSh.wP, GlobalTheory.WigSh.wM]
end GlobalTheory.WigSh.Model
