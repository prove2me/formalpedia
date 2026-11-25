-- Prove2me | solution 1 for GlobalTheory.T.exists_isSymmetricPositionLevel
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T07:02:22.153794+00:00
-- url     : https://prove2.me/submissions/25eb754a-beb9-4f89-809a-62611b7828d7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsIsSymmetricPositionLevel
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_FramePositiveSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsIsSymmetricPositionLevelStatement
import Theorems.Thm_GlobalTheory_SymLevelExists_exists_isSymLevel


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix Topology GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), HasConductor ψ 1 → ∀ ϖ : kˣ, IsUnif ϖ → ∀ ρ κ l : ℕ, ∃ P : TypeDatum k (Fin κ ⊕ Fin l), IsSymLevel ψ ϖ ρ P := by
  first | exact @GlobalTheory.SymLevelExists.exists_isSymLevel | exact GlobalTheory.SymLevelExists.exists_isSymLevel | (intros; apply GlobalTheory.SymLevelExists.exists_isSymLevel <;> assumption)
end _root_.GlobalTheory.T
