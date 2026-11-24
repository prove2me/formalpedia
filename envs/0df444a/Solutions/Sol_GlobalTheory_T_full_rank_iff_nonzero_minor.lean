-- Prove2me | solution 1 for GlobalTheory.T.full_rank_iff_nonzero_minor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:10:13.826459+00:00
-- url     : https://prove2.me/submissions/d57ac2b5-7a92-474f-9d38-4bfe12b535b2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FullRankIffNonzeroMinor
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_OmAOneApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FullRankIffNonzeroMinorStatement
import Theorems.Thm_GlobalTheory_RankFibreKer_rank_eq_iff_exists_minor_ne_zero


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
theorem _root_.solution : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (a d : ℕ) (Y : Matrix (Fin a) (Fin d) k), Y.rank = a ↔ ∃ J, minor Y J ≠ 0 := by
  first | exact @GlobalTheory.RankFibreKer.rank_eq_iff_exists_minor_ne_zero | exact GlobalTheory.RankFibreKer.rank_eq_iff_exists_minor_ne_zero | (intros; apply GlobalTheory.RankFibreKer.rank_eq_iff_exists_minor_ne_zero <;> assumption)
end _root_.GlobalTheory.T
