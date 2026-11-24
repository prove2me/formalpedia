-- Prove2me | solution 1 for GlobalTheory.ScalarSnakeLength.exact_kerMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T20:33:02.324569+00:00
-- url     : https://prove2.me/submissions/6206b787-b709-47cf-b395-72b1fbc525ff

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LengthEqKerAddRange

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open GlobalTheory.ScalarSnakeLength
variable {A : Type} [CommRing A]
variable {M₁ M₂ M₃ : Type} [AddCommGroup M₁] [AddCommGroup M₂] [AddCommGroup M₃]
  [Module A M₁] [Module A M₂] [Module A M₃]
namespace GlobalTheory.ScalarSnakeLength
theorem _root_.solution (f : M₁ →ₗ[A] M₂) (g : M₂ →ₗ[A] M₃) (hf : Function.Injective f)
    (hfg : Function.Exact f g) (b : A) : Function.Exact (kerMap f b) (kerMap g b) := by
  intro x
  constructor
  · intro hx
    have hx' : g x.1 = 0 := congrArg Subtype.val hx
    obtain ⟨y, hy⟩ := (hfg _).1 hx'
    refine ⟨⟨y, ?_⟩, Subtype.ext hy⟩
    show b • y = 0
    apply hf
    rw [map_smul, hy, map_zero]
    exact x.2
  · rintro ⟨y, rfl⟩
    exact Subtype.ext ((hfg _).2 ⟨y.1, rfl⟩)
end GlobalTheory.ScalarSnakeLength
