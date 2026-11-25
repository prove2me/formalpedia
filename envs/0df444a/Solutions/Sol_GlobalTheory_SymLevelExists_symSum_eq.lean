-- Prove2me | solution 1 for GlobalTheory.SymLevelExists.symSum_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T02:45:54.138393+00:00
-- url     : https://prove2.me/submissions/5271d9aa-7273-4c20-98f5-16eaf485c185

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_FramePositiveSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_UnipotentRadicalBasic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsIsSymmetricPositionLevel
import Theorems.Thm_GlobalTheory_SymLevelExists_simpleSum_mul_embX
import Theorems.Thm_P2M_GlobalTheory_SymLevelExists_toBlocks___mul_embX_f9431060e73d

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix Topology GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum
noncomputable section
open GlobalTheory GlobalTheory.SymLevelExists
variable {F : Type} [Field F] {κ l : ℕ}
namespace GlobalTheory.SymLevelExists
theorem _root_.solution {p : ℕ} {u : GL (Fin κ ⊕ Fin l) F} (hu : u ∈ N F (Fin κ) l p) (γ : GL (Fin κ) F) :
    symSum (u * embX l γ) = simpleSum u + superSum Fin.val γ.val := by
  rw [symSum, simpleSum_mul_embX, toBlocks₁₁_mul_embX hu]
end GlobalTheory.SymLevelExists
