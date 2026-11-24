-- Prove2me | solution 1 for GlobalTheory.SgGlob.Inhab.dOne_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:19:56.884734+00:00
-- url     : https://prove2.me/submissions/94570c23-e841-4dca-8bff-c41b8d1750b2

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
namespace GlobalTheory.SgGlob.Inhab
theorem _root_.solution : dOne E ≠ 0 := by
  rw [dOne, coeIdeal_differentIdeal ℤ ℚ E (𝓞 E)]
  exact inv_ne_zero (FractionalIdeal.dual_ne_zero ℤ ℚ one_ne_zero)
end GlobalTheory.SgGlob.Inhab
