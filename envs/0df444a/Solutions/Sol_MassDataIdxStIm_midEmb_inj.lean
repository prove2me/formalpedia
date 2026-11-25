-- Prove2me | solution 1 for MassDataIdxStIm.midEmb_inj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:30:51.115139+00:00
-- url     : https://prove2.me/submissions/8624c2ac-5a6d-404a-815c-75c82fbeb08e

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeIndices_LeviEmbeddingBlock32

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
theorem _root_.solution {h h' : Matrix (Fin k) (Fin k) A} (e : midEmb h = midEmb h') : h = h' := (Matrix.fromBlocks_inj.1 e).1
end MassDataIdxStIm
