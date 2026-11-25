-- Prove2me | solution 1 for HSDoublingWork.sumSwap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:25:44.409868+00:00
-- url     : https://prove2.me/submissions/8bedf60c-794b-47bd-b964-8355b6ef98c7

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GlobalRankLatticeProofs_UnitTraceSumBounds_CBCardNC
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DoubleSumSwap_SumSwap

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
theorem _root_.solution : ∑ x : Fin N × Fin N, U ε z x.swap = ∑ x, U ε z x :=
  Fintype.sum_equiv (Equiv.prodComm _ _) _ _ (fun _ => rfl)
end HSDoublingWork
