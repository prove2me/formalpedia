-- Prove2me | solution 1 for HSDoublingWork.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:48:59.927526+00:00
-- url     : https://prove2.me/submissions/903db5d7-6f43-4780-963e-f793b62816f7

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GlobalRankLatticeProofs_UnitTraceSumBounds_CBCardNC
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DoubleSumSwap_SumSwap
import Theorems.Thm_HSDoublingWork_entry
import Theorems.Thm_HSDoublingWork_sumU
import Theorems.Thm_HSDoublingWork_sumSwap

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open HSDoublingWork
open Formalism.MainNotions.Ext.CutB
variable {N : ℕ} (ε : Fin N → Bool) (z : cBNC ε → ℂ)
namespace HSDoublingWork
theorem _root_.solution : cBhsPP := by
  intro N ε z
  unfold cBhs
  rw [← Fintype.sum_prod_type' (fun a b => ‖cBpp ε z a b‖ ^ 2)]
  rw [Finset.sum_congr rfl (fun x _ => entry ε z x), Finset.sum_add_distrib, sumSwap, sumU]
  ring
end HSDoublingWork
