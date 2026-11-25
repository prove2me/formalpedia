-- Prove2me | solution 1 for GlobalTheory.DiagBlock.kill_X
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:50:07.205535+00:00
-- url     : https://prove2.me/submissions/a59907e5-b9ab-4d60-9d3e-38965a3cfec6

import Mathlib
import Definitions.Def_Formalism_DropLevelBounds_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_LeWeightOfCoeffPow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_DetPowDiagonalRowsBlockJetRestrict

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.UnitaryBoundIntegral Formalism.IncomingBounds
open scoped BigOperators
noncomputable section
open GlobalTheory GlobalTheory.DiagBlock
variable {R : Type} [CommRing R] {σ : Type}
namespace GlobalTheory.DiagBlock
theorem _root_.solution (S : σ → Prop) [DecidablePred S] (x : σ) :
    kill (R := R) S (MvPolynomial.X x) = if S x then 0 else MvPolynomial.X x := by
  rw [kill, MvPolynomial.aeval_X]
end GlobalTheory.DiagBlock
