-- Prove2me | solution 1 for GlobalTheory.LegendreFacts.mfact_eq_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:38:55.961816+00:00
-- url     : https://prove2.me/submissions/67522f67-5f80-4b13-89bf-475c39a88fbc

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BiadditiveInSingleVariables
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_LegendreBoundsFactorialMultiIndexCapelli
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_LegendreAndCapelli

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds
open GlobalTheory GlobalTheory.LegendreFacts
open GlobalTheory.LegendreBounds
namespace GlobalTheory.LegendreFacts
theorem _root_.solution {σ : Type} [Fintype σ] (A : σ →₀ ℕ) :
    mfact A = ∏ j, (A j).factorial := by
  unfold mfact
  exact Finsupp.prod_fintype A _ (fun _ => Nat.factorial_zero)
end GlobalTheory.LegendreFacts
