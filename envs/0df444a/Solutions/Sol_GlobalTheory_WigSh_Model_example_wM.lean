-- Prove2me | solution 1 for GlobalTheory.WigSh.Model.example_wM
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:36:52.969118+00:00
-- url     : https://prove2.me/submissions/4f6aa6c6-0644-4423-852a-713f29f1bf8c

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
theorem _root_.solution : wM ![3, -1] ![1] 0 = 1 / 2 ∧ wM ![3, -1] ![1] 1 = 1 / 2 := by
  refine ⟨?_, ?_⟩
  · simp [GlobalTheory.WigSh.wM, prod_erase_eq]
    norm_num
  · simp [GlobalTheory.WigSh.wM, prod_erase_eq, Fin.succAbove]
    norm_num
end GlobalTheory.WigSh.Model
