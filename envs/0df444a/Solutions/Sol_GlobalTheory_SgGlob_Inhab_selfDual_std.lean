-- Prove2me | solution 1 for GlobalTheory.SgGlob.Inhab.selfDual_std
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:15:02.650874+00:00
-- url     : https://prove2.me/submissions/1e452fb5-a0b5-4696-96f2-da8e8b39c711

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FrameLats
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsDifferentPair
import Theorems.Thm_GlobalTheory_SgGlob_Inhab_map_mem_int
import Theorems.Thm_GlobalTheory_SgGlob_Inhab_mem_std
import Theorems.Thm_GlobalTheory_SgGlob_Inhab_form_two

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
theorem _root_.solution (σ : E →+* E) : SelfDual σ !![1, 0; 0, -1] (std E) := by
  refine ⟨Submodule.fg_span (Set.toFinite _), fun v => ⟨fun hv w hw => ?_, fun h => ?_⟩⟩
  · rw [mem_std] at hv hw
    rw [form_two]
    exact sub_mem (mul_mem (map_mem_int σ hw.1) hv.1) (mul_mem (map_mem_int σ hw.2) hv.2)
  · have h0 := h ![1, 0] ((mem_std _).2 ⟨one_mem _, zero_mem _⟩)
    have h1 := h ![0, -1] ((mem_std _).2 ⟨zero_mem _, neg_mem (one_mem _)⟩)
    rw [form_two] at h0 h1
    exact (mem_std v).2 ⟨by simpa using h0, by simpa using h1⟩
end GlobalTheory.SgGlob.Inhab
