-- Prove2me | solution 1 for GlobalTheory.SgGlob.one_mem_UO
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:24:48.794508+00:00
-- url     : https://prove2.me/submissions/84c2ccec-9a9c-4374-b15d-818dd3b50c5f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FrameLats
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsDifferentPair
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_DiagMemCongruencePairs

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Matrix GlobalTheory.SgAlg
open scoped nonZeroDivisors
open GlobalTheory GlobalTheory.SgGlob
variable {E : Type} [Field E] [NumberField E]
variable {n r : ℕ}
namespace GlobalTheory.SgGlob
theorem _root_.solution : (1 : Matrix (Fin (r + 1)) (Fin (r + 1)) E) ∈ UO E r :=
  ⟨fun _ _ => ⟨fun h => Matrix.one_apply_ne h.ne', fun h => h ▸ Matrix.one_apply_eq _⟩,
    fun _ _ h => by rw [Matrix.one_apply_ne h.ne]; exact FractionalIdeal.zero_mem _⟩
end GlobalTheory.SgGlob
