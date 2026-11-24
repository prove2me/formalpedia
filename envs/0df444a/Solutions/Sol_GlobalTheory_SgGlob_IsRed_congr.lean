-- Prove2me | solution 1 for GlobalTheory.SgGlob.IsRed.congr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:13:32.897373+00:00
-- url     : https://prove2.me/submissions/daed85f7-2764-4a48-a285-adb5fa2d61be

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FrameLats
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsDifferentPair
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_DiagMemCongruencePairs
import Theorems.Thm_GlobalTheory_SgGlob_IsRed_mem_iff
import Theorems.Thm_GlobalTheory_SgGlob_zOf_mem_perpX

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
open GlobalTheory GlobalTheory.SgGlob
variable {E : Type} [Field E] [NumberField E]
variable {σ : E →+* E} {n m r : ℕ} {J : Matrix (Fin n) (Fin n) E} {Jb : Matrix (Fin m) (Fin m) E}
omit [NumberField E]
namespace GlobalTheory.SgGlob
namespace IsRed
theorem _root_.solution {T : E} {Λ : Submodule (𝓞 E) (Fin n → E)} {P : Matrix (Fin n) (Fin (r + 1)) E}
    {x : Lz E m} {al bl : Matrix (Fin m) (Fin n) E} (h : IsRed σ J Jb Λ P x al) (hP : IsFrame σ J T P)
    (hb : ∀ v ∈ perpX σ J P, bl *ᵥ v = al *ᵥ v) : IsRed σ J Jb Λ P x bl := by
  refine ⟨fun v hv => by rw [hb v hv, h.1 v hv], fun y => ?_,
    fun v hv w hw => by rw [hb v hv, hb w hw, h.2.2.1 v hv w hw], ?_,
    (hb _ (zOf_mem_perpX hP)).trans h.2.2.2.2⟩
  · obtain ⟨v, hv, rfl⟩ := h.2.1 y
    exact ⟨v, hv, hb v hv⟩
  · ext y
    rw [h.mem_iff]
    exact ⟨fun ⟨v, hv, e⟩ => ⟨v, hv, (hb v hv.2).symm.trans e⟩,
      fun ⟨v, hv, e⟩ => ⟨v, hv, (hb v hv.2).trans e⟩⟩
end IsRed
end GlobalTheory.SgGlob
