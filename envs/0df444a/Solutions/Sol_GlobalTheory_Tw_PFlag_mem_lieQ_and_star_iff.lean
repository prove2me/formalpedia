-- Prove2me | solution 1 for GlobalTheory.Tw.PFlag.mem_lieQ_and_star_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:09:26.685775+00:00
-- url     : https://prove2.me/submissions/984b4e01-6c70-4c7d-9e69-f4de8b784c93

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_MemCentIffTwConj
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsHermitianOfMemRealScalars
import Theorems.Thm_GlobalTheory_Tw_mulVec_dot_star
import Theorems.Thm_GlobalTheory_Tw_dot_star_comm_zero
import Theorems.Thm_GlobalTheory_Tw_eq_zero_of_mem_perp
import Theorems.Thm_GlobalTheory_Tw_perp_perp
import Theorems.Thm_GlobalTheory_Tw_PFlag_le_of_summand_le
import Theorems.Thm_GlobalTheory_Tw_PFlag_summand_le_perp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open GlobalTheory GlobalTheory.Tw
variable {n : ℕ}
open GlobalTheory.Tw.PFlag
variable {F : PFlag n ℂ}
namespace GlobalTheory.Tw.PFlag
theorem _root_.solution {X : Matrix (Fin n) (Fin n) ℂ} :
    X ∈ F.lieQ ∧ Xᴴ ∈ F.lieQ ↔ ∀ V ∈ F.carrier, ∀ v ∈ F.summand V, X *ᵥ v ∈ F.summand V := by
  constructor
  · rintro ⟨h1, h2⟩ V hV v hv
    exact ⟨h1 V hV v hv.1, fun w hw => by rw [mulVec_dot_star]; exact hv.2 _ (mulVec_mem_pred h2 V hw)⟩
  · intro h
    refine ⟨fun V hV => le_of_summand_le (U := V.comap X.mulVecLin) hV fun V' hV' hle v hv => hle (h V' hV' v hv).1,
      fun V hV v hv => ?_⟩
    rw [← perp_perp V]
    intro w hw
    have h1 : ⊤ ≤ V ⊔ (perp V ⊓ (perp V).comap X.mulVecLin) := le_of_summand_le F.top_mem fun V' hV' _ => by
      rcases F.chain.total hV' hV with h' | h'
      · exact le_sup_of_le_left (inf_le_left.trans h')
      · rcases h'.eq_or_lt with rfl | h''
        · exact le_sup_of_le_left inf_le_left
        · exact le_sup_of_le_right fun u hu => ⟨summand_le_perp hV h'' hu, summand_le_perp hV h'' (h V' hV' u hu)⟩
    obtain ⟨y, hy, u, hu, rfl⟩ := Submodule.mem_sup.1 (h1 (Submodule.mem_top (x := w)))
    have h2 : y = 0 := eq_zero_of_mem_perp hy (by simpa using sub_mem hw hu.1)
    rw [h2, zero_add, mulVec_dot_star, conjTranspose_conjTranspose]
    exact dot_star_comm_zero (hu.2 v hv)
end GlobalTheory.Tw.PFlag
