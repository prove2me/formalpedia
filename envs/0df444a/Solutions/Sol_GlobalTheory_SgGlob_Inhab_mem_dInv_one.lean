-- Prove2me | solution 1 for GlobalTheory.SgGlob.Inhab.mem_dInv_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:30:15.160381+00:00
-- url     : https://prove2.me/submissions/fbec3679-8228-453c-b7d5-7dec5e13e5be

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FrameLats
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsDifferentPair
import Theorems.Thm_GlobalTheory_SgGlob_Inhab_dOne_ne_zero
import Theorems.Thm_P2M_GlobalTheory_SgGlob_Inhab_mem_one_iff__00678d2868dc

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
theorem _root_.solution (x : E) : x ∈ dInv E 1 ↔ ∀ t ∈ dOne E, x * t ∈ Int' E := by
  rw [dInv, pow_one, FractionalIdeal.mem_inv_iff dOne_ne_zero]
  simp only [mem_one_iff']
end GlobalTheory.SgGlob.Inhab
