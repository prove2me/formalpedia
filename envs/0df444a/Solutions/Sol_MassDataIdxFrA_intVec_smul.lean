-- Prove2me | solution 1 for MassDataIdxFrA.intVec_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:50:48.942006+00:00
-- url     : https://prove2.me/submissions/fde64e64-d952-49b4-b8db-d523aa973785

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeIndices_CongSpanSingleIff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MassDataIdxFrA
variable {F k : Type} [Field F] [Field k] (O : ValuationSubring F) (π : O →+* k) (γ : O)
  {ι : Type} [Fintype ι] [DecidableEq ι]
omit [DecidableEq ι]
namespace MassDataIdxFrA
theorem _root_.solution (c : O) {v : ι → F} (hv : IntVec O v) : IntVec O ((c : F) • v) := by
  exact fun i => mul_mem c.2 (hv i)
end MassDataIdxFrA
