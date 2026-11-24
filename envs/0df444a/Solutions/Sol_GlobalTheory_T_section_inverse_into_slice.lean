-- Prove2me | solution 1 for GlobalTheory.T.section_inverse_into_slice
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:22:24.276269+00:00
-- url     : https://prove2.me/submissions/92daa9a8-1c1d-4696-aedc-77bb1b1c94ec

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SectionInverseIntoSlice
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_OmAOneApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SectionInverseIntoSliceStatement
import Theorems.Thm_GlobalTheory_RankFibreKer_sec_inv_mul_mem_slice


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
    ((sec Y)⁻¹).val * Y ∈ slice k a d := by
  first | exact @GlobalTheory.RankFibreKer.sec_inv_mul_mem_slice | exact GlobalTheory.RankFibreKer.sec_inv_mul_mem_slice | (intros; apply GlobalTheory.RankFibreKer.sec_inv_mul_mem_slice <;> assumption)
end _root_.GlobalTheory.T
