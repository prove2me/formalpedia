-- Prove2me | solution 1 for HSDoublingWork.sumU
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:25:45.355162+00:00
-- url     : https://prove2.me/submissions/7a68da56-9a77-4ede-9083-804df57e6b40

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
theorem _root_.solution : ∑ x, U ε z x = ∑ pr : cBNC ε, ‖z pr‖ ^ 2 := by
  rw [← Fintype.sum_subtype_add_sum_subtype (fun x : Fin N × Fin N => x.1 < x.2 ∧ ε x.1 ≠ ε x.2) (U ε z)]
  have h0 : ∑ i : {x : Fin N × Fin N // ¬ (x.1 < x.2 ∧ ε x.1 ≠ ε x.2)}, U ε z i = 0 :=
    Finset.sum_eq_zero (fun i _ => dif_neg i.2)
  rw [h0, add_zero]
  exact Finset.sum_congr rfl (fun i _ => dif_pos i.2)
end HSDoublingWork
