-- Prove2me | solution 1 for GlobalTheory.linearMap_rat_valued_eq_trace
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:19:02.514795+00:00
-- url     : https://prove2.me/submissions/02e4368f-15f0-4f9a-807a-05f549831665

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RationalFunctionalTraceRepresentation

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] (g : E →ₗ[ℚ] ℝ), (∀ z, ∃ q : ℚ, g z = q) →
    ∃ mu : E, ∀ z, g z = ((Algebra.trace ℚ E (mu * z) : ℚ) : ℝ) := by
  intro E _ _ g hg
  choose f hf using hg
  let g' : E →ₗ[ℚ] ℚ :=
    { toFun := f
      map_add' := by
        intro x y
        apply (Rat.cast_injective (α := ℝ))
        rw [Rat.cast_add, ← hf, ← hf, ← hf, map_add]
      map_smul' := by
        intro c x
        apply (Rat.cast_injective (α := ℝ))
        rw [smul_eq_mul, RingHom.id_apply, Rat.cast_mul, ← hf, ← hf, map_smul, Rat.smul_def] }
  have hB := traceForm_nondegenerate ℚ E
  refine ⟨(LinearMap.BilinForm.toDual _ hB).symm g', fun z => ?_⟩
  have h1 : (LinearMap.BilinForm.toDual _ hB ((LinearMap.BilinForm.toDual _ hB).symm g')) z = g' z := by
    rw [LinearEquiv.apply_symm_apply]
  rw [LinearMap.BilinForm.toDual_def, Algebra.traceForm_apply] at h1
  rw [h1]
  exact hf z
end GlobalTheory
