-- Prove2me | solution 1 for GlobalTheory.SgGlob.Inhab.map_mem_dOne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:27:41.975647+00:00
-- url     : https://prove2.me/submissions/ce7c91c5-bd3b-4ee3-9250-26e0ad1da727

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FrameLats
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsDifferentPair
import Theorems.Thm_GlobalTheory_SgGlob_Inhab_map_mem_int
import Theorems.Thm_GlobalTheory_SgGlob_Inhab_mem_dOne
import Theorems.Thm_GlobalTheory_SgGlob_Inhab_map_mem_dInv

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
theorem _root_.solution (σ : E →+* E) (hσ : ∀ x, σ (σ x) = x) {t : E} (ht : t ∈ dOne E) :
    σ t ∈ dOne E := by
  rw [mem_dOne] at ht ⊢
  intro x hx
  have := map_mem_int σ (ht _ (map_mem_dInv σ hσ hx))
  rwa [map_mul, hσ] at this
end GlobalTheory.SgGlob.Inhab
