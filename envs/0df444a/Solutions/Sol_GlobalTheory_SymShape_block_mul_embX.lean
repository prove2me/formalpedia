-- Prove2me | solution 1 for GlobalTheory.SymShape.block_mul_embX
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:23:10.651617+00:00
-- url     : https://prove2.me/submissions/b850fb24-b029-49e0-945a-9461d5cbacc4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_FramePositiveSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_UnipotentRadicalBasic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_GenericLevelOfFrameBlockAndCharacter
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SymmetricPositionLevelShapeOnParabolic
import Theorems.Thm_GlobalTheory_RootEx_Radical_embX_val
import Theorems.Thm_P2M_GlobalTheory_RootEx_Radical_toBlocks___of_mem_fe0d9551bf6c


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix Topology GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum
open GlobalTheory GlobalTheory.SymShape
namespace GlobalTheory.SymShape
theorem _root_.solution {F : Type} [Field F] {κ l p : ℕ} {u : GL (Fin κ ⊕ Fin l) F} (hu : u ∈ N F (Fin κ) l p)
    (γ : GL (Fin κ) F) : (u * embX l γ).val.toBlocks₁₁ = γ.val := by
  rw [Units.val_mul, GlobalTheory.RootEx.Radical.embX_val, ← Matrix.fromBlocks_toBlocks u.val,
    Matrix.fromBlocks_multiply, Matrix.toBlocks_fromBlocks₁₁, GlobalTheory.RootEx.Radical.toBlocks₁₁_of_mem hu]
  simp
end GlobalTheory.SymShape
