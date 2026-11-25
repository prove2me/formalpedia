-- Prove2me | solution 1 for GlobalTheory.LegendreFacts.capNat_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:40:56.702286+00:00
-- url     : https://prove2.me/submissions/ad2fea86-df43-4d18-87fd-88050a51c478

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
theorem _root_.solution (n0 x : ℕ) :
    capNat n0 x * ∏ c ∈ Finset.range n0, c.factorial
      = ∏ c ∈ Finset.range n0, (x + c).factorial := by
  unfold capNat
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl ?_
  intro c _
  exact Nat.div_mul_cancel (Nat.factorial_dvd_factorial (Nat.le_add_left c x))
end GlobalTheory.LegendreFacts
