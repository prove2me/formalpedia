-- Prove2me | solution 1 for MassDataIdxCore.pairMatrix_firstSplit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:08:34.240126+00:00
-- url     : https://prove2.me/submissions/6b28c788-a540-4dc1-92b1-31a101cefab3

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeIndices_KerBack
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeIndices_PairMatrixSecondSplit

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
variable (θ : T ≃ₐ[K] K × K)
namespace MassDataIdxCore
theorem _root_.solution (a b : Matrix n n K) : (pm θ a b).map (t1 θ) = a := by
  ext i j
  simp [pm, t1]
end MassDataIdxCore
