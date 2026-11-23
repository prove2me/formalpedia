-- Prove2me | solution 1 for GlobalTheory.Doubling.mem_diagSub
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:34:22.371198+00:00
-- url     : https://prove2.me/submissions/102d001e-97eb-4b4e-9780-2a4908729a15

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsIwasawaOfIsCompact
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MemSiegelOfIffRightAct

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
theorem _root_.solution {w : ι → A} : w ∈ diagSub A e ↔ ∃ x, w = pairVec e x x := by
  refine ⟨fun h => ⟨fun i => w (e (.inl i)), ?_⟩, by rintro ⟨x, rfl⟩; exact (pairVec_mem_diagSub e).2 rfl⟩
  rw [← pairVec_eta e w, pairVec_mem_diagSub] at h
  nth_rewrite 2 [h]
  exact (pairVec_eta e w).symm
end GlobalTheory.Doubling
