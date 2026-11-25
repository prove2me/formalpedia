-- Prove2me | solution 1 for MassDataIdxStIm.card_matrix
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:30:49.865523+00:00
-- url     : https://prove2.me/submissions/26dc73e2-2aba-4de8-b58c-2447a303b1ad

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeIndices_LeviEmbeddingBlock32
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeIndices_Block31OfBlocks

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.unusedVariables false
open MassDataIdxStIm
open Matrix Finset
open Formalism.DoubleCosetMeasures (IsUpUni upUniG isUpUni_mul isUpUni_inv isUpUni_one isUpUni_det)
open Formalism.FourierDecayAlt.S3
namespace MassDataIdxStIm
theorem _root_.solution (m n K : Type) [Finite m] [Finite n] :
    Nat.card (Matrix m n K) = Nat.card K ^ (Nat.card m * Nat.card n) := by
  show Nat.card (m → n → K) = _
  rw [Nat.card_fun, Nat.card_fun, ← pow_mul, Nat.mul_comm (Nat.card n) (Nat.card m)]
end MassDataIdxStIm
