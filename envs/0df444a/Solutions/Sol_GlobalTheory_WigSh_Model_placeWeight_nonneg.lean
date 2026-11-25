-- Prove2me | solution 1 for GlobalTheory.WigSh.Model.placeWeight_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T05:28:56.746322+00:00
-- url     : https://prove2.me/submissions/9f01d97b-a0ef-4398-b869-ae6b6457a999

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_Imports
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_FactorNonneg
import Theorems.Thm_GlobalTheory_WigSh_Model_prod_erase_eq
import Theorems.Thm_GlobalTheory_WigSh_Model_factor_nonneg

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
theorem _root_.solution {n : ℕ} {L : Fin (n + 1) → ℤ} {M : Fin n → ℤ} (h : Box L M)
    (l : Fin (n + 1)) : 0 ≤ wP L M l := by
  unfold GlobalTheory.WigSh.wP
  rw [prod_erase_eq, ← Finset.prod_div_distrib]
  refine Finset.prod_nonneg fun j _ => ?_
  simpa using factor_nonneg h l j 1 zero_le_one le_rfl
end GlobalTheory.WigSh.Model
