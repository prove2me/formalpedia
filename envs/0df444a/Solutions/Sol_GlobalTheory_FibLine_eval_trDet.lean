-- Prove2me | solution 1 for GlobalTheory.FibLine.eval_trDet
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:07:12.192267+00:00
-- url     : https://prove2.me/submissions/8d83ab20-1db5-4a63-90ae-a8972ffbb02a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HPolyAddTwo
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntegralCompFsDens
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DivFractionsBilinearFormula
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_EqZeroOfEvalHermitian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntegralAffinePowEqHPoly
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntegrableProdQCoefMulFsDens
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AevalFibPowExplicit

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
theorem _root_.solution {R : Type} [CommRing R] [Algebra ℂ R] (H : Matrix (Fin 2) (Fin 2) R) (p : MvPolynomial (Fin 2) ℂ) :
    MvPolynomial.aeval (entries H) (MvPolynomial.aeval trDet p) = MvPolynomial.aeval ![H.trace, H.det] p := by
  rw [← AlgHom.comp_apply, MvPolynomial.comp_aeval]
  have e : (fun i => MvPolynomial.aeval (entries H) (trDet i)) = ![H.trace, H.det] := by
    funext i
    fin_cases i <;> simp [trDet, entries, Matrix.trace_fin_two, Matrix.det_fin_two]
  rw [e]
end GlobalTheory.FibLine
