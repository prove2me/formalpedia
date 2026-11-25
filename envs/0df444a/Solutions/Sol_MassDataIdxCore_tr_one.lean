-- Prove2me | solution 1 for MassDataIdxCore.tr_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:09:05.850385+00:00
-- url     : https://prove2.me/submissions/211f41be-3cca-4017-bad8-f9d5e4b7e9ee

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
namespace MassDataIdxCore
theorem _root_.solution {R : Type} [CommRing R] {X Y : Matrix n n R} (h : X * Y = 1) : Yᵀ * Xᵀ = 1 := by
  rw [← Matrix.transpose_mul, h, Matrix.transpose_one]
end MassDataIdxCore
