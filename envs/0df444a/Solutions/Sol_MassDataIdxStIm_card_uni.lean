-- Prove2me | solution 1 for MassDataIdxStIm.card_uni
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:38:05.848444+00:00
-- url     : https://prove2.me/submissions/a7033e6d-39c7-46b1-9a59-9919ad2ec032

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeIndices_LeviEmbeddingBlock32
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeIndices_Block31OfBlocks
import Theorems.Thm_MassDataIdxStIm_card_lt_pairs

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
variable {A : Type} [CommRing A]
namespace MassDataIdxStIm
theorem _root_.solution (K : Type) [Field K] [Fintype K] (n : ℕ) :
    Nat.card {u : Matrix (Fin n) (Fin n) K // IsUpUni u} = Fintype.card K ^ (n * (n - 1) / 2) := by
  rw [Nat.card_congr (uniEquiv (A := K) n), Nat.card_fun, card_lt_pairs, Nat.card_eq_fintype_card]
end MassDataIdxStIm
