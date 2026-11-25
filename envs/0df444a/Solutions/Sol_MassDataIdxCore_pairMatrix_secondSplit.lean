-- Prove2me | solution 1 for MassDataIdxCore.pairMatrix_secondSplit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:09:04.218392+00:00
-- url     : https://prove2.me/submissions/ef288790-2b0f-4f98-8908-9cf9d4c8b82a

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
theorem _root_.solution (a b : Matrix n n K) : (pm θ a b).map (t2 θ) = b := by
  ext i j
  simp [pm, t2]
end MassDataIdxCore
