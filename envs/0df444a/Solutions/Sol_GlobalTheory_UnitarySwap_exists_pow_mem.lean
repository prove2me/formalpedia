-- Prove2me | solution 1 for GlobalTheory.UnitarySwap.exists_pow_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T19:35:09.442392+00:00
-- url     : https://prove2.me/submissions/7cf044e5-b163-4f1e-9903-5f9f6d203336

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Formalism_SatakeDualWeyl_StatementF
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_ImportsTail
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_InvMemDoubleCosetAndComm
import Theorems.Thm_Formalism_UG_Final_KpqSubgroupCompact
import Theorems.Thm_GlobalTheory_MatrixEntryBound_main


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.UG Matrix
noncomputable section
open GlobalTheory GlobalTheory.UnitarySwap
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]
variable {n : ℕ} {σ : L →+* L}
namespace GlobalTheory.UnitarySwap
theorem _root_.solution {ϖ : L} (hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ)) (M : Matrix (Fin n) (Fin n) L) :
    ∃ N : ℕ, ∀ i j, ϖ ^ N * M i j ∈ intL L := by
  first
  | exact @_root_.GlobalTheory.MatrixEntryBound.main
  | exact _root_.GlobalTheory.MatrixEntryBound.main
  | (apply _root_.GlobalTheory.MatrixEntryBound.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.MatrixEntryBound.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.MatrixEntryBound.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.MatrixEntryBound.main ..)
end GlobalTheory.UnitarySwap
