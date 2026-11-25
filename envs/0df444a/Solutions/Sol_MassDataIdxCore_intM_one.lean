-- Prove2me | solution 1 for MassDataIdxCore.intM_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:29:13.064575+00:00
-- url     : https://prove2.me/submissions/571bcc64-cb14-45eb-a681-18c801358a62

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeIndices_StRedCore
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeIndices_SecondSplitTensorVector

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MassDataIdxCore
open Matrix
variable {K T : Type} [Field K] [CommRing T] [Algebra K T] (O : ValuationSubring K) {n : Type} [Fintype n]
  [DecidableEq n]
namespace MassDataIdxCore
theorem _root_.solution : IntM O (1 : Matrix n n K) := by
  intro i j
  rw [Matrix.one_apply]
  split_ifs
  · exact O.one_mem
  · exact O.zero_mem
end MassDataIdxCore
