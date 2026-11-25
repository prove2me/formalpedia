-- Prove2me | solution 1 for MassDataIdxStIm.block23_of_blocks
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:30:47.425792+00:00
-- url     : https://prove2.me/submissions/02e476d2-93e2-42b2-8757-616b68ca81db

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
variable {A : Type} [CommRing A]
variable {r k : ℕ}
variable (a : Matrix (Fin r) (Fin r) A) (b : Matrix (Fin r) (Mid k) A) (c : Matrix (Fin r) (Fin r) A)
    (m : Matrix (Mid k) (Mid k) A) (e : Matrix (Mid k) (Fin r) A) (f : Matrix (Fin r) (Fin r) A)
namespace MassDataIdxStIm
theorem _root_.solution : b23 (mk a b c m e f) = e := by
  first
    | rfl
    | (ext i j; simp [mk, b23])
end MassDataIdxStIm
