-- Prove2me | solution 1 for MassDataIdxStIm.hEmb_inj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:38:57.612789+00:00
-- url     : https://prove2.me/submissions/c5018285-8d14-4128-968c-8e8121c2efc2

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeIndices_LeviEmbeddingBlock32
import Theorems.Thm_MassDataIdxStIm_midEmb_inj

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
open MassDataIdxStIm
open Matrix Finset
open Formalism.DoubleCosetMeasures (IsUpUni upUniG isUpUni_mul isUpUni_inv isUpUni_one isUpUni_det)
open Formalism.FourierDecayAlt.S3
variable {A : Type} {r k : ℕ}
variable [CommRing A]
namespace MassDataIdxStIm
theorem _root_.solution {h h' : Matrix (Fin k) (Fin k) A} (e : hEmb r h = hEmb r h') : h = h' := by
  have e1 := (Matrix.fromBlocks_inj.1 e).2.2.2
  exact midEmb_inj (Matrix.fromBlocks_inj.1 e1).1
end MassDataIdxStIm
