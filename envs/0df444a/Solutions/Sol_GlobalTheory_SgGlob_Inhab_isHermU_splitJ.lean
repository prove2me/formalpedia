-- Prove2me | solution 1 for GlobalTheory.SgGlob.Inhab.isHermU_splitJ
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:23:48.472161+00:00
-- url     : https://prove2.me/submissions/390a3599-df0a-4ae7-8e0f-c89d1eede3bf

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FrameLats
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsDifferentPair

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
open GlobalTheory GlobalTheory.SgGlob GlobalTheory.SgGlob.Inhab
variable {E : Type} [Field E] [NumberField E]
omit [NumberField E]
namespace GlobalTheory.SgGlob.Inhab
theorem _root_.solution (σ : E →+* E) : IsHermU σ (splitJ E) := by
  refine ⟨?_, Matrix.isUnit_det_of_left_inverse (B := splitJ E) ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [cT, splitJ]
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [splitJ, Matrix.mul_apply, Fin.sum_univ_eight]
end GlobalTheory.SgGlob.Inhab
