-- Prove2me | solution 1 for GlobalTheory.SgGlob.Inhab.mem_lzSet
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:27:42.51419+00:00
-- url     : https://prove2.me/submissions/14d95c5d-ccd1-4c0e-a2ec-33e0cf563a68

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FrameLats
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsDifferentPair
import Theorems.Thm_GlobalTheory_SgGlob_Inhab_smul_eq
import Theorems.Thm_GlobalTheory_SgGlob_Inhab_mem_std
import Theorems.Thm_GlobalTheory_SgGlob_Inhab_form_two
import Theorems.Thm_GlobalTheory_SgGlob_Inhab_selfDual_std

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
theorem _root_.solution (σ : E →+* E) : (std E, ![0, 1]) ∈ LzSet σ !![1, 0; 0, -1] 1 := by
  refine ⟨selfDual_std σ, by simp [form_two], ?_, ?_⟩
  · dsimp only
    rw [Submodule.span_le]
    rintro v rfl
    exact (mem_std _).2 ⟨zero_mem _, one_mem _⟩
  · intro v hv hs
    dsimp only at hv hs ⊢
    rw [Submodule.span_span_of_tower, Submodule.mem_span_singleton] at hs
    obtain ⟨a, rfl⟩ := hs
    obtain ⟨c, hc⟩ := ((mem_std _).1 hv).2
    refine Submodule.mem_span_singleton.2 ⟨c, ?_⟩
    ext i
    fin_cases i <;> simp [smul_eq]
    simpa using hc
end GlobalTheory.SgGlob.Inhab
