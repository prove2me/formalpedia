-- Prove2me | solution 1 for MassDataIdxFrA.intVec_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:50:41.834189+00:00
-- url     : https://prove2.me/submissions/754ee3cc-f220-449d-98f4-82c442051452

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
theorem _root_.solution {v w : ι → F} (hv : IntVec O v) (hw : IntVec O w) : IntVec O (v + w) := by
  exact fun i => add_mem (hv i) (hw i)
end MassDataIdxFrA
