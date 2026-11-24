-- Prove2me | solution 1 for GlobalTheory.FibLine.aeval_fibPow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T17:11:19.975023+00:00
-- url     : https://prove2.me/submissions/28cb79da-6dcb-4ea4-b836-1d442b8fdfa2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HPolyAddTwo
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntegralCompFsDens
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DivFractionsBilinearFormula
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_EqZeroOfEvalHermitian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntegralAffinePowEqHPoly
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntegrableProdQCoefMulFsDens
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AevalFibPowExplicit
import Theorems.Thm_GlobalTheory_FibLine_eval_trDet
import Theorems.Thm_GlobalTheory_FibLine_fibPow_eq

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
theorem _root_.solution {R : Type} [CommRing R] [Algebra ℂ R] (H : Matrix (Fin 2) (Fin 2) R) (k : ℕ) :
    MvPolynomial.aeval (entries H) (fibPow k) =
      (1 / ((k : ℂ) + 1)) • MvPolynomial.aeval ![H.trace, H.det] (hPoly k) := by
  rw [fibPow_eq, map_smul, eval_trDet]
end GlobalTheory.FibLine
