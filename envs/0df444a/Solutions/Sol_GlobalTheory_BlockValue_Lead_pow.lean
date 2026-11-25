-- Prove2me | solution 1 for GlobalTheory.BlockValue.Lead.pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T01:21:42.630901+00:00
-- url     : https://prove2.me/submissions/4340b89b-ea92-4b45-99da-5393505e8e10

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BiadditiveInSingleVariables
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_DetPowDiagonalRowsBlockJetRestrict
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_BlockValueOnRowsEq
import Theorems.Thm_GlobalTheory_BlockValue_OnlyIn_mul
import Theorems.Thm_GlobalTheory_BlockValue_Lead_of_coeff_zero
import Theorems.Thm_GlobalTheory_BlockValue_Lead_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.UnitaryBoundIntegral
open scoped BigOperators
open GlobalTheory GlobalTheory.BlockValue
variable {C : Type} [Field C] {σ κ : Type}
namespace GlobalTheory.BlockValue
namespace Lead
theorem _root_.solution {π : σ → κ} {d : σ →₀ ℕ} {f : MvPowerSeries σ C} (hf : Lead π d f) (k : ℕ) :
    Lead π (k • d) (f ^ k) := by
  induction k with
  | zero => simpa using Lead.of_coeff_zero π (by simp)
  | succ k ih => rw [pow_succ, succ_nsmul]; exact ih.mul hf
end Lead
end GlobalTheory.BlockValue
