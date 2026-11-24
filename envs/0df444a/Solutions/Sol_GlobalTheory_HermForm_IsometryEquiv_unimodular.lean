-- Prove2me | solution 1 for GlobalTheory.HermForm.IsometryEquiv.unimodular
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:40:06.027816+00:00
-- url     : https://prove2.me/submissions/d4dcaae7-8e8c-478c-8832-4c4214393a63

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MemUnitaryGroupIffIsIsometry
import Theorems.Thm_GlobalTheory_HermForm_Unimodular_exists_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open NumberField
open GlobalTheory
open GlobalTheory.HermForm
variable {R M N P : Type*} [CommRing R] [StarRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] [AddCommGroup P] [Module R P]
variable (h : HermForm R M)
variable {h}
open GlobalTheory.HermForm.IsometryEquiv
variable {h₁ : HermForm R M} {h₂ : HermForm R N} {h₃ : HermForm R P}
namespace GlobalTheory.HermForm.IsometryEquiv
theorem _root_.solution (f : h₁.IsometryEquiv h₂) (H : h₁.Unimodular) : h₂.Unimodular := by
  refine h₂.unimodular_iff.2 ⟨f.nondegenerate H.nondegenerate, fun φ => ?_⟩
  obtain ⟨y, hy⟩ := H.exists_eq (φ ∘ₗ f.toLinearEquiv.toLinearMap)
  exact ⟨f y, fun x => by rw [f.map_app_right, hy]; simp⟩
end GlobalTheory.HermForm.IsometryEquiv
