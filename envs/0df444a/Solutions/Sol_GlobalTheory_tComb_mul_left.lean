-- Prove2me | solution 1 for GlobalTheory.tComb_mul_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:36:57.267028+00:00
-- url     : https://prove2.me/submissions/1c265489-1598-4fc0-ae61-085ceb71a337

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_DegProd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_AlternatingSumChooseMulSubPow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_KaFormHomogeneous

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open Finset GlobalTheory.KeyKa
namespace GlobalTheory
theorem _root_.solution {R : Type} [CommRing R] (g n l Pr : ℕ) (t c : Rˣ) (lam : ℕ → Rˣ) :
    tComb g n l Pr (t * c) lam = tComb g n l Pr t lam * c ^ (4 * Pr ^ (3 * g + 2)) := by
  unfold tComb
  rw [mul_pow]
  exact mul_right_comm _ _ _
end GlobalTheory
