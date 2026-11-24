-- Prove2me | solution 1 for GlobalTheory.T.first_maximal_minor_locally_constant
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:09:42.706089+00:00
-- url     : https://prove2.me/submissions/1f8b5448-0672-4005-a095-9cb855733442

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FirstMaximalMinorLocallyConstant
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_OmAOneApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FirstMaximalMinorLocallyConstantStatement
import Theorems.Thm_GlobalTheory_RankFibreKer_isFirstMax_eventually


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
theorem _root_.solution : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (a d : ℕ) (Y : Matrix (Fin a) (Fin d) k) (J : Fin a ↪ Fin d), IsFirstMax Y J →
    ∀ᶠ Y' in nhds Y, IsFirstMax Y' J := by
  first | exact @GlobalTheory.RankFibreKer.isFirstMax_eventually | exact GlobalTheory.RankFibreKer.isFirstMax_eventually | (intros; apply GlobalTheory.RankFibreKer.isFirstMax_eventually <;> assumption)
end _root_.GlobalTheory.T
