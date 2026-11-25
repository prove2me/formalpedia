-- Prove2me | solution 1 for GlobalTheory.DiagBlock.rowDeg_filter_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:49:11.853062+00:00
-- url     : https://prove2.me/submissions/76e33c5d-01d8-4e3c-80c8-32a11d201647

import Mathlib
import Definitions.Def_Formalism_DropLevelBounds_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_LeWeightOfCoeffPow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_DetPowDiagonalRowsBlockJetRestrict

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.UnitaryBoundIntegral Formalism.IncomingBounds
open scoped BigOperators
noncomputable section
open GlobalTheory GlobalTheory.DiagBlock
namespace GlobalTheory.DiagBlock
theorem _root_.solution {n : ℕ} (p : PVar n → Prop) [DecidablePred p] (m : PVar n →₀ ℕ) (ρ : Fin n) :
    rowDegZ (m.filter p) ρ ≤ rowDegZ m ρ ∧ rowDegZ' (m.filter p) ρ ≤ rowDegZ' m ρ := by
  constructor <;>
  · refine Finset.sum_le_sum fun c _ => ?_
    rw [Finsupp.filter_apply]
    split_ifs <;> simp
end GlobalTheory.DiagBlock
