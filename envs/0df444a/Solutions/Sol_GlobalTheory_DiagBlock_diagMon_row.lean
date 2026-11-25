-- Prove2me | solution 1 for GlobalTheory.DiagBlock.diagMon_row
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:58:27.675811+00:00
-- url     : https://prove2.me/submissions/f45a49d3-1dff-402b-91d0-876dce84c7c6

import Mathlib
import Definitions.Def_Formalism_DropLevelBounds_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_LeWeightOfCoeffPow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_DetPowDiagonalRowsBlockJetRestrict
import Theorems.Thm_GlobalTheory_DiagBlock_diagMon_inl
import Theorems.Thm_GlobalTheory_DiagBlock_diagMon_inr

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
theorem _root_.solution {n0 n L y : ℕ} (x : PVar n) (hx : x ∈ (diagMon n0 n L y).support) :
    n0 ≤ (rowOf x).val := by
  rw [Finsupp.mem_support_iff] at hx
  rcases x with ⟨ρ, c⟩ | ⟨ρ, c⟩
  · rw [diagMon_inl] at hx
    split_ifs at hx with h
    · exact h.1
    · exact absurd rfl hx
  · rw [diagMon_inr] at hx
    split_ifs at hx with h
    · exact h.1
    · exact absurd rfl hx
end GlobalTheory.DiagBlock
