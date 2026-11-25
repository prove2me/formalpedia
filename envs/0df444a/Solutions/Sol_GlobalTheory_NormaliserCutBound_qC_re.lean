-- Prove2me | solution 1 for GlobalTheory.NormaliserCutBound.qC_re
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T07:01:57.513293+00:00
-- url     : https://prove2.me/submissions/4a18dfdf-19d9-46d0-86ea-53968ffd3ba2

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_StatementI
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Interlace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_Imports
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_TwoBracketsLePowMulProdEntries
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ProdFinEqProdIcc

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt Finset
open GlobalTheory GlobalTheory.NormaliserCutBound
namespace GlobalTheory.NormaliserCutBound
theorem _root_.solution (P : M.Par) (y : ℝ) :
    (M.qC P (y : ℂ)).re = I.qpoly P.k P.T P.T' P.u P.u' y := by
  have : M.qC P (y : ℂ) = ((I.qpoly P.k P.T P.T' P.u P.u' y : ℝ) : ℂ) := by
    unfold M.qC I.qpoly
    push_cast
    rfl
  rw [this, Complex.ofReal_re]
end GlobalTheory.NormaliserCutBound
