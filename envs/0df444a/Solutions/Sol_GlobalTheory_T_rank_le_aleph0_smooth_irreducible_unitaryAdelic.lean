-- Prove2me | solution 1 for GlobalTheory.T.rank_le_aleph0_smooth_irreducible_unitaryAdelic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T18:26:44.316567+00:00
-- url     : https://prove2.me/submissions/4873ee92-5924-4117-93a4-70191f25f707

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RankLeAleph0SmoothIrreducibleUnitaryAdelic
import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_GaloisLevelStructure_DefsFinTyp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RankLeAleph0SmoothIrreducibleUnitaryAdelicStatement
import Theorems.Thm_GlobalTheory_FinTyp_rank_le_aleph0


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} (π : Formalism.L2.NG.FinTyp L n), Module.rank ℂ π.S ≤ Cardinal.aleph0 := by
  first | exact @GlobalTheory.FinTyp.rank_le_aleph0 | exact GlobalTheory.FinTyp.rank_le_aleph0 | (intros; apply GlobalTheory.FinTyp.rank_le_aleph0 <;> assumption)
end _root_.GlobalTheory.T
