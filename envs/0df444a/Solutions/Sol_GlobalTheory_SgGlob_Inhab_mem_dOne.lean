-- Prove2me | solution 1 for GlobalTheory.SgGlob.Inhab.mem_dOne
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:30:29.355294+00:00
-- url     : https://prove2.me/submissions/4d987fc6-a516-4769-bc71-5fe09dea23f5

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
theorem _root_.solution (t : E) : t ∈ dOne E ↔ ∀ x ∈ dInv E 1, t * x ∈ Int' E := by
  have h : dOne E = (dInv E 1)⁻¹ := by rw [dInv, pow_one, inv_inv]
  have h0 : dInv E 1 ≠ 0 := by rw [dInv, pow_one]; exact inv_ne_zero dOne_ne_zero
  rw [h, FractionalIdeal.mem_inv_iff h0]
  simp only [mem_one_iff']
end GlobalTheory.SgGlob.Inhab
