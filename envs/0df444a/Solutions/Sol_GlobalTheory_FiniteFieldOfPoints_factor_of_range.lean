-- Prove2me | solution 1 for GlobalTheory.FiniteFieldOfPoints.factor_of_range
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T15:07:48.14308+00:00
-- url     : https://prove2.me/submissions/0ee4e772-bfd0-4581-852b-bdae334a58bf

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsFiniteFieldOfPoints

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory GlobalTheory.FiniteFieldOfPoints
namespace GlobalTheory.FiniteFieldOfPoints
theorem _root_.solution {C K₂ Ω : Type} [CommRing C] [Field K₂] [Field Ω]
    (j : K₂ →+* Ω) (ψ : C →+* Ω) (h : ∀ c, ∃ x, j x = ψ c) :
    ∃ ψ₀ : C →+* K₂, j.comp ψ₀ = ψ := by
  choose f hf using h
  refine ⟨{ toFun := f, map_one' := ?_, map_mul' := ?_, map_zero' := ?_, map_add' := ?_ }, ?_⟩
  · apply j.injective; simp [hf]
  · intro a b; apply j.injective; simp [hf]
  · apply j.injective; simp [hf]
  · intro a b; apply j.injective; simp [hf]
  · ext c; simp [hf]
end GlobalTheory.FiniteFieldOfPoints
