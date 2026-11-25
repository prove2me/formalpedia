-- Prove2me | solution 1 for GlobalTheory.WigSh.Model.wM_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T05:29:13.360043+00:00
-- url     : https://prove2.me/submissions/36963090-c72b-463d-b07a-f429d23c52bd

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
    (l : Fin (n + 1)) : 0 ≤ wM L M l := by
  unfold GlobalTheory.WigSh.wM
  rw [prod_erase_eq, ← Finset.prod_div_distrib]
  refine Finset.prod_nonneg fun j _ => ?_
  simpa using factor_nonneg h l j 0 le_rfl zero_le_one
end GlobalTheory.WigSh.Model
