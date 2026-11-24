-- Prove2me | solution 1 for GlobalTheory.SgGlob.Inhab.int_mul_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:28:13.251799+00:00
-- url     : https://prove2.me/submissions/40fe6db7-e908-415a-8bb8-4d2eb505d2f7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FrameLats
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsDifferentPair
import Theorems.Thm_GlobalTheory_SgGlob_Inhab_smul_eq

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
theorem _root_.solution {I : FractionalIdeal (𝓞 E)⁰ E} {c x : E} (hc : c ∈ Int' E) (hx : x ∈ I) :
    c * x ∈ I := by
  obtain ⟨c, rfl⟩ := hc
  rw [← smul_eq]
  exact Submodule.smul_mem (I : Submodule (𝓞 E) E) c hx
end GlobalTheory.SgGlob.Inhab
