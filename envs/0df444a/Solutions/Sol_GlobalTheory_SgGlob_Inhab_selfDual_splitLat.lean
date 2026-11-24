-- Prove2me | solution 1 for GlobalTheory.SgGlob.Inhab.selfDual_splitLat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:40:19.455933+00:00
-- url     : https://prove2.me/submissions/43ee35af-6499-4bed-98d9-8e243cefc735

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FrameLats
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsDifferentPair
import Theorems.Thm_GlobalTheory_SgGlob_Inhab_map_mem_int
import Theorems.Thm_GlobalTheory_SgGlob_Inhab_mem_dInv_one
import Theorems.Thm_GlobalTheory_SgGlob_Inhab_mem_dOne
import Theorems.Thm_GlobalTheory_SgGlob_Inhab_map_mem_dInv
import Theorems.Thm_GlobalTheory_SgGlob_Inhab_map_mem_dOne
import Theorems.Thm_GlobalTheory_SgGlob_Inhab_form_split
import Theorems.Thm_GlobalTheory_SgGlob_Inhab_mem_splitLat

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
theorem _root_.solution (σ : E →+* E) (hσ : ∀ x, σ (σ x) = x) :
    SelfDual σ (splitJ E) (splitLat E) := by
  refine ⟨Submodule.fg_pi fun i => FractionalIdeal.fg_of_isNoetherianRing le_rfl _,
    fun v => ⟨fun hv w hw => ?_, fun h => ?_⟩⟩
  · rw [mem_splitLat] at hv hw
    obtain ⟨v0, v1, v2, v3, v4, v5, v6, v7⟩ := hv
    obtain ⟨w0, w1, w2, w3, w4, w5, w6, w7⟩ := hw
    rw [form_split]
    have m {x y : E} (hx : x ∈ Int' E) (hy : y ∈ Int' E) := mul_mem (map_mem_int σ hx) hy
    exact sub_mem (add_mem (add_mem (add_mem (add_mem (add_mem (add_mem
      ((mem_dInv_one _).1 (map_mem_dInv σ hσ w0) _ v1) ((mem_dOne _).1 (map_mem_dOne σ hσ w1) _ v0))
      (m w2 v2)) (m w3 v3)) (m w4 v4)) (m w5 v5)) (m w6 v6)) (m w7 v7)
  · have z (I : FractionalIdeal (𝓞 E)⁰ E) : (0 : E) ∈ I := FractionalIdeal.zero_mem I
    have o : (0 : E) ∈ Int' E := zero_mem _
    have u : (1 : E) ∈ Int' E := one_mem _
    refine (mem_splitLat v).2 ⟨(mem_dInv_one _).2 fun t ht => ?_, (mem_dOne _).2 fun t ht => ?_,
      ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa [form_split, hσ, mul_comm] using h ![0, σ t, 0, 0, 0, 0, 0, 0]
        ((mem_splitLat _).2 ⟨z _, map_mem_dOne σ hσ ht, o, o, o, o, o, o⟩)
    · simpa [form_split, hσ, mul_comm] using h ![σ t, 0, 0, 0, 0, 0, 0, 0]
        ((mem_splitLat _).2 ⟨map_mem_dInv σ hσ ht, z _, o, o, o, o, o, o⟩)
    · simpa [form_split] using h ![0, 0, 1, 0, 0, 0, 0, 0]
        ((mem_splitLat _).2 ⟨z _, z _, u, o, o, o, o, o⟩)
    · simpa [form_split] using h ![0, 0, 0, 1, 0, 0, 0, 0]
        ((mem_splitLat _).2 ⟨z _, z _, o, u, o, o, o, o⟩)
    · simpa [form_split] using h ![0, 0, 0, 0, 1, 0, 0, 0]
        ((mem_splitLat _).2 ⟨z _, z _, o, o, u, o, o, o⟩)
    · simpa [form_split] using h ![0, 0, 0, 0, 0, 1, 0, 0]
        ((mem_splitLat _).2 ⟨z _, z _, o, o, o, u, o, o⟩)
    · simpa [form_split] using h ![0, 0, 0, 0, 0, 0, 1, 0]
        ((mem_splitLat _).2 ⟨z _, z _, o, o, o, o, u, o⟩)
    · simpa [form_split] using h ![0, 0, 0, 0, 0, 0, 0, -1]
        ((mem_splitLat _).2 ⟨z _, z _, o, o, o, o, o, neg_mem u⟩)
end GlobalTheory.SgGlob.Inhab
