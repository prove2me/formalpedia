-- Prove2me | solution 1 for GlobalTheory.SgGlob.Inhab.form_two
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:23:46.065149+00:00
-- url     : https://prove2.me/submissions/fed93a7b-349e-4a1d-a89a-87150aa73680

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
theorem _root_.solution (σ : E →+* E) (v w : Fin 2 → E) :
    form σ !![1, 0; 0, -1] v w = σ (w 0) * v 0 - σ (w 1) * v 1 := by
  simp [form, dotProduct, Matrix.mulVec, Fin.sum_univ_two, sub_eq_add_neg]
end GlobalTheory.SgGlob.Inhab
