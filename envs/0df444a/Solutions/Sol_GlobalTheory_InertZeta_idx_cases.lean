-- Prove2me | solution 1 for GlobalTheory.InertZeta.idx_cases
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T16:32:55.466803+00:00
-- url     : https://prove2.me/submissions/796e8de5-0b92-4571-8749-6da61fd8bc40

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MemSiegelOfIffRightAct
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AntiJMulApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Theorems.Thm_Formalism_UG_Final_KpqSubgroupCompact


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism.UG Matrix MeasureTheory GlobalTheory.SatakeWeyl
open GlobalTheory GlobalTheory.InertZeta
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {N : ℕ}
namespace GlobalTheory.InertZeta
theorem _root_.solution (i : Fin (N + 2)) : i = 0 ∨ (∃ j, i = mid j) ∨ i = Fin.last (N + 1) := by
  induction i using Fin.cases with
  | zero => exact Or.inl rfl
  | succ i =>
    induction i using Fin.lastCases with
    | last => exact Or.inr (Or.inr rfl)
    | cast i => exact Or.inr (Or.inl ⟨i, rfl⟩)
end GlobalTheory.InertZeta
