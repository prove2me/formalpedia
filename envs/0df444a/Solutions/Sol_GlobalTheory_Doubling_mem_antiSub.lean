-- Prove2me | solution 1 for GlobalTheory.Doubling.mem_antiSub
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:34:22.198525+00:00
-- url     : https://prove2.me/submissions/ad26aab5-8869-4097-98e5-2d6badb68490

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsIwasawaOfIsCompact
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MemSiegelOfIffRightAct
import Theorems.Thm_GlobalTheory_Doubling_pairVec_mem_antiSub

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.Doubling
open Matrix Formalism.UG
variable {A B : Type} [CommRing A] [CommRing B] {m n ι : Type}
variable (e : n ⊕ n ≃ ι)
namespace GlobalTheory.Doubling
theorem _root_.solution {w : ι → A} : w ∈ antiSub A e ↔ ∃ x, w = pairVec e x (-x) := by
  refine ⟨fun h => ⟨fun i => w (e (.inl i)), ?_⟩, by rintro ⟨x, rfl⟩; exact (pairVec_mem_antiSub e).2 (neg_neg _).symm⟩
  rw [← pairVec_eta e w, pairVec_mem_antiSub] at h
  nth_rewrite 2 [h]
  rw [neg_neg]
  exact (pairVec_eta e w).symm
end GlobalTheory.Doubling
