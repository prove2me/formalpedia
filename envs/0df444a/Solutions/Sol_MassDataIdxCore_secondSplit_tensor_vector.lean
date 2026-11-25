-- Prove2me | solution 1 for MassDataIdxCore.secondSplit_tensor_vector
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:29:26.640846+00:00
-- url     : https://prove2.me/submissions/86551117-7f40-4e1f-b5ee-561544cf4bef

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
variable (θ : T ≃ₐ[K] K × K) (J : Matrix n n T) (P : GL n K)
namespace MassDataIdxCore
theorem _root_.solution (j : n) : (fun i => t2 θ (tv θ P j i)) = 0 := by
  funext i
  simp [tv, t2]
end MassDataIdxCore
