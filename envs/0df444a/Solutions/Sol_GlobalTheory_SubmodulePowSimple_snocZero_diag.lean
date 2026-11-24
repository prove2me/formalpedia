-- Prove2me | solution 1 for GlobalTheory.SubmodulePowSimple.snocZero_diag
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T20:58:45.389854+00:00
-- url     : https://prove2.me/submissions/7c29a8ac-00dd-4c68-8bc4-f7ea66c76d7c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SubmodulePowSimpleEqSumEquivValues

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Submodule
open GlobalTheory GlobalTheory.SubmodulePowSimple
variable {P : Type} [AddCommGroup P] [Module ℂ P] {ι : Type}
namespace GlobalTheory.SubmodulePowSimple
theorem _root_.solution {m : ℕ} (b : Module.End ℂ P) (z : Fin m → P) :
    snocZero m (fun j => b (z j)) = fun j => b (snocZero m z j) := by
  funext j; refine Fin.lastCases ?_ (fun j => ?_) j <;> simp [snocZero]
end GlobalTheory.SubmodulePowSimple
