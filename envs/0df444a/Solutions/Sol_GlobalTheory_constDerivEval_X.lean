-- Prove2me | solution 1 for GlobalTheory.constDerivEval_X
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:43:35.523857+00:00
-- url     : https://prove2.me/submissions/31fabb05-741c-4043-86e1-995c5221a7c9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_PredMulSumPadicValNatFactorialAddCardLe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open Finsupp
open MvPolynomial
variable {R σ Λ : Type*} [CommRing R]
namespace GlobalTheory
theorem _root_.solution (v : Λ → σ → R) (l : Λ) :
    constDerivEval v (X l) = (constDeriv (v l)).toLinearMap := commEval_X _ _ l
end GlobalTheory
