-- Prove2me | solution 1 for GlobalTheory.SgGlob.Inhab.mem_std
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:28:13.35361+00:00
-- url     : https://prove2.me/submissions/613697f7-e65d-4bce-a728-4827e26133da

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
theorem _root_.solution (v : Fin 2 → E) : v ∈ std E ↔ v 0 ∈ Int' E ∧ v 1 ∈ Int' E := by
  rw [std, Submodule.mem_span_pair]
  constructor
  · rintro ⟨a, b, rfl⟩
    constructor
    · exact ⟨b, by simp [smul_eq]⟩
    · exact ⟨a + b, by simp [smul_eq]⟩
  · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
    refine ⟨b - a, a, ?_⟩
    ext i
    fin_cases i <;> simp [smul_eq, ← ha, ← hb]
end GlobalTheory.SgGlob.Inhab
