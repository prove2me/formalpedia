-- Prove2me | solution 1 for GlobalTheory.LineThrough.eval_zero_lineMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T18:45:10.796514+00:00
-- url     : https://prove2.me/submissions/04bb87b4-d83a-4503-9da6-7174185029eb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_ExistsPrimeDimensionLEOneAvoiding

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory GlobalTheory.LineThrough
namespace GlobalTheory.LineThrough
theorem _root_.solution {d : ℕ} (a c : Fin d → ℂ) (f : MvPolynomial (Fin d) ℂ) :
    (lineMap a c f).eval 0 = MvPolynomial.eval a f := by
  induction f using MvPolynomial.induction_on with
  | C r => simp [lineMap]
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp => rw [map_mul, eval_mul, hp]; simp [lineMap]
end GlobalTheory.LineThrough
