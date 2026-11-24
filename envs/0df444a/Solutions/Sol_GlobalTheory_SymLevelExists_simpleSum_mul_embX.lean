-- Prove2me | solution 1 for GlobalTheory.SymLevelExists.simpleSum_mul_embX
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:12:39.278572+00:00
-- url     : https://prove2.me/submissions/34c7d469-e409-4983-8517-fd38bee53b56

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_FramePositiveSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_UnipotentRadicalBasic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsIsSymmetricPositionLevel
import Theorems.Thm_GlobalTheory_RootEx_Radical_embX_val


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
theorem _root_.solution (u : GL (Fin κ ⊕ Fin l) F) (γ : GL (Fin κ) F) :
    simpleSum (u * embX l γ) = simpleSum u := by
  have hv : ∀ i j, (u * embX l γ).val (Sum.inr i) (Sum.inr j) = u.val (Sum.inr i) (Sum.inr j) := by
    intro i j
    rw [Units.val_mul, Radical.embX_val, ← fromBlocks_toBlocks u.val]
    simp [fromBlocks_multiply]
  simp only [simpleSum, hv]
end GlobalTheory.SymLevelExists
