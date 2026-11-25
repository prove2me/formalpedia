-- Prove2me | solution 1 for MassDataIdxCore.cancel_l
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:08:24.549386+00:00
-- url     : https://prove2.me/submissions/b5c3b709-31b8-4de2-a570-fb78fa7e6fba

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
theorem _root_.solution {R : Type} [CommRing R] {X Y : Matrix n n R} (h : X * Y = 1) (M : Matrix n n R) :
    X * (Y * M) = M := by
  rw [← Matrix.mul_assoc, h, Matrix.one_mul]
end MassDataIdxCore
