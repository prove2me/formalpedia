-- Prove2me | solution 1 for GlobalTheory.WigSh.Model.example_wP
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:35:32.960928+00:00
-- url     : https://prove2.me/submissions/360ecc8b-1293-4646-9722-d931e3b540aa

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_Imports
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_FactorNonneg
import Theorems.Thm_GlobalTheory_WigSh_Model_prod_erase_eq

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
theorem _root_.solution : Box ![3, -1] ![1] ∧ wP ![3, -1] ![1] 0 = 3 / 4 ∧ wP ![3, -1] ![1] 1 = 1 / 4 := by
  refine ⟨?_, ?_, ?_⟩
  · intro j
    fin_cases j
    decide
  · simp [GlobalTheory.WigSh.wP, prod_erase_eq]
    norm_num
  · simp [GlobalTheory.WigSh.wP, prod_erase_eq, Fin.succAbove]
    norm_num
end GlobalTheory.WigSh.Model
