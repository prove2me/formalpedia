-- Prove2me | solution 1 for GlobalTheory.MinorGerm.Low.pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:07:16.893102+00:00
-- url     : https://prove2.me/submissions/341bc2d7-a6c7-430d-bf15-9c8439be6beb

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BiadditiveInSingleVariables
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_LegendreAndCapelli
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ProdFactorialDiag
import Theorems.Thm_GlobalTheory_MinorGerm_low_one
import Theorems.Thm_GlobalTheory_MinorGerm_Low_mul

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
namespace Low
theorem _root_.solution {α : σ →₀ ℕ} {g : MvPowerSeries σ C} (hg : Low α g) (n : ℕ) :
    Low (n • α) (g ^ n) := by
  classical
  induction n with
  | zero => simpa using (low_one : Low (0 : σ →₀ ℕ) (1 : MvPowerSeries σ C))
  | succ n ih =>
    rw [succ_nsmul, pow_succ]
    exact ih.mul hg
end Low
end GlobalTheory.MinorGerm
