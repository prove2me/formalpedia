-- Prove2me | solution 1 for GlobalTheory.CapelliDiff.Tm_add_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:08:12.998288+00:00
-- url     : https://prove2.me/submissions/2c7a0db8-385e-48d0-8979-720a5ae3724c

import Mathlib
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_QdetAddOneSubEqSumQminor

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.REAL Finset
open GlobalTheory GlobalTheory.CapelliDiff
namespace GlobalTheory.CapelliDiff
theorem _root_.solution {A : Type*} [Ring A] [Algebra ℂ A] {n : ℕ} (E : Fin n → Fin n → A) (v : ℂ) (a b : Fin n) :
    Tm E (v + 1) a b = Tm E v a b + algebraMap ℂ A (if a = b then 1 else 0) := by
  unfold Tm
  split_ifs <;> simp [map_add]; abel
end GlobalTheory.CapelliDiff
