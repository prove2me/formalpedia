-- Prove2me | solution 1 for GlobalTheory.WigSh.Model.denom_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:36:47.963073+00:00
-- url     : https://prove2.me/submissions/cb37782c-9310-468b-8ede-805060815e86

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_Imports
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_FactorNonneg
import Theorems.Thm_GlobalTheory_WigSh_Model_Box_strictAnti
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
theorem _root_.solution {n : ℕ} {L : Fin (n + 1) → ℤ} {M : Fin n → ℤ} (h : Box L M)
    (l : Fin (n + 1)) : ∏ j ∈ univ.erase l, ((L j : ℝ) - (L l : ℝ)) ≠ 0 := by
  rw [prod_erase_eq]
  refine Finset.prod_ne_zero_iff.mpr fun j _ => sub_ne_zero.mpr ?_
  exact_mod_cast h.strictAnti.injective.ne (Fin.succAbove_ne l j)
end GlobalTheory.WigSh.Model
