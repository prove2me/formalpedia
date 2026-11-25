-- Prove2me | solution 1 for MassDataIdxCore.intV_mulVec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:29:18.456266+00:00
-- url     : https://prove2.me/submissions/f094adff-f11d-440e-92f1-1beae627a00a

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
theorem _root_.solution {M : Matrix n n K} {v : n → K} (hM : IntM O M) (hv : IntV O v) : IntV O (M *ᵥ v) := fun i => by
  simp only [Matrix.mulVec, dotProduct]
  exact sum_mem fun j _ => mul_mem (hM i j) (hv j)
end MassDataIdxCore
