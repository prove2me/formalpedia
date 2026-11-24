-- Prove2me | solution 1 for GlobalTheory.T.slice_stabilizer_trivial
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:22:26.610608+00:00
-- url     : https://prove2.me/submissions/63416197-e5d2-42b7-9bde-e347fb20a951

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SliceStabilizerTrivial
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_OmAOneApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SliceStabilizerTrivialStatement
import Theorems.Thm_GlobalTheory_RankFibreKer_eq_one_of_mem_slice_of_mul_mem_slice


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
theorem _root_.solution : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (a d : ℕ) (Z : Matrix (Fin a) (Fin d) k) (g : GL (Fin a) k), Z ∈ slice k a d → g.val * Z ∈ slice k a d → g = 1 := by
  first | exact @GlobalTheory.RankFibreKer.eq_one_of_mem_slice_of_mul_mem_slice | exact GlobalTheory.RankFibreKer.eq_one_of_mem_slice_of_mul_mem_slice | (intros; apply GlobalTheory.RankFibreKer.eq_one_of_mem_slice_of_mul_mem_slice <;> assumption)
end _root_.GlobalTheory.T
