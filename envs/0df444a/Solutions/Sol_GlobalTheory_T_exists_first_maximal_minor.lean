-- Prove2me | solution 1 for GlobalTheory.T.exists_first_maximal_minor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T20:09:39.365555+00:00
-- url     : https://prove2.me/submissions/137ea2ba-8a36-479d-ad7b-81106e9783aa

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsFirstMaximalMinor
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_OmAOneApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsFirstMaximalMinorStatement
import Theorems.Thm_GlobalTheory_RankFibreKer_exists_isFirstMax


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory ValuativeRel GlobalTheory.SplitFlip GlobalTheory.SmGL GlobalTheory.WeilM GlobalTheory.RankFibre GlobalTheory.SplitWeil GlobalTheory.RankFibreKer
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (a d : ℕ) (Y : Matrix (Fin a) (Fin d) k), (∃ J, minor Y J ≠ 0) → ∃ J, IsFirstMax Y J := by
  first | exact @GlobalTheory.RankFibreKer.exists_isFirstMax | exact GlobalTheory.RankFibreKer.exists_isFirstMax | (intros; apply GlobalTheory.RankFibreKer.exists_isFirstMax <;> assumption)
end _root_.GlobalTheory.T
