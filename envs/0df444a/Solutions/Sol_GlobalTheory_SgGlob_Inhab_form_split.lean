-- Prove2me | solution 1 for GlobalTheory.SgGlob.Inhab.form_split
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T20:47:00.293559+00:00
-- url     : https://prove2.me/submissions/39834d9b-2ca0-465a-97c0-bb27d8427c14

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
theorem _root_.solution (σ : E →+* E) (v w : Fin 8 → E) :
    form σ (splitJ E) v w = σ (w 0) * v 1 + σ (w 1) * v 0 + σ (w 2) * v 2 + σ (w 3) * v 3 +
      σ (w 4) * v 4 + σ (w 5) * v 5 + σ (w 6) * v 6 - σ (w 7) * v 7 := by
  simp [form, splitJ, dotProduct, Matrix.mulVec, Fin.sum_univ_eight, sub_eq_add_neg]
end GlobalTheory.SgGlob.Inhab
