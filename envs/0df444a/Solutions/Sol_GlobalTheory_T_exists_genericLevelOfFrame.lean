-- Prove2me | solution 1 for GlobalTheory.T.exists_genericLevelOfFrame
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:34:49.01088+00:00
-- url     : https://prove2.me/submissions/7cc7a017-6b6a-49ce-8caa-60b48fc6ca20

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsGenericLevelOfFrame
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_FramePositiveSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsGenericLevelOfFrameStatement
import Theorems.Thm_GlobalTheory_GenericLevel_exists_isGenericLevel


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
theorem _root_.solution : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), HasConductor ψ 1 → ∀ ϖ : kˣ, IsUnif ϖ → ∀ κ l : ℕ, ∃ P : TypeDatum k (Fin κ ⊕ Fin l), IsGenericLevel ψ ϖ P := by
  first | exact @GlobalTheory.GenericLevel.exists_isGenericLevel | exact GlobalTheory.GenericLevel.exists_isGenericLevel | (intros; apply GlobalTheory.GenericLevel.exists_isGenericLevel <;> assumption)
end _root_.GlobalTheory.T
