-- Prove2me | solution 1 for GlobalTheory.FibLine.aeval_fibPow_explicit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:45:29.741227+00:00
-- url     : https://prove2.me/submissions/a9fcf059-d9e3-4a1a-8057-a0388b064dc8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HPolyAddTwo
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntegralCompFsDens
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DivFractionsBilinearFormula
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_EqZeroOfEvalHermitian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntegralAffinePowEqHPoly
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntegrableProdQCoefMulFsDens
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AevalFibPowExplicit
import Theorems.Thm_GlobalTheory_FibLine_aeval_fibPow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MeasureTheory MvPolynomial GlobalTheory.FibLine
open GlobalTheory GlobalTheory.FibLine
namespace GlobalTheory.FibLine
theorem _root_.solution : ∀ (R : Type) [CommRing R] [Algebra ℂ R] (H : Matrix (Fin 2) (Fin 2) R) (k : ℕ),
    MvPolynomial.aeval (entries H) (fibPow k) =
      (1 / ((k : ℂ) + 1)) • MvPolynomial.aeval ![H.trace, H.det] (hPoly k) :=
  fun _ _ _ H k => aeval_fibPow H k
end GlobalTheory.FibLine
