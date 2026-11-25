-- Prove2me | solution 1 for GlobalTheory.MinorGerm.low_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:46:32.443805+00:00
-- url     : https://prove2.me/submissions/606f8083-b9a3-4edc-84bc-29270862ffb9

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BiadditiveInSingleVariables
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_LegendreAndCapelli
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ProdFactorialDiag

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds
noncomputable section
open GlobalTheory GlobalTheory.MinorGerm
variable {C : Type} [Field C] {σ : Type}
namespace GlobalTheory.MinorGerm
theorem _root_.solution : Low (0 : σ →₀ ℕ) (1 : MvPowerSeries σ C) := by
  classical
  refine ⟨by simp, fun m _ hm => ?_⟩
  rw [MvPowerSeries.coeff_one, if_neg hm]
end GlobalTheory.MinorGerm
