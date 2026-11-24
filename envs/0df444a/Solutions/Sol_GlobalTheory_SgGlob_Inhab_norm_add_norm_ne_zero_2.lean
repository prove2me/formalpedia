-- Prove2me | solution 2 for GlobalTheory.SgGlob.Inhab.norm_add_norm_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:24:14.098107+00:00
-- url     : https://prove2.me/submissions/5648aad9-8601-489f-8830-675ce2048330

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FrameLats
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsDifferentPair

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
theorem _root_.solution (σ : E →+* E) (τ : E →+* ℂ) (hτ : ∀ x, τ (σ x) = starRingEnd ℂ (τ x))
    {a : E} (ha : a ≠ 0) (b : E) : a * σ a + b * σ b ≠ 0 := by
  intro h
  have h1 := congrArg τ h
  rw [map_add, map_mul, map_mul, hτ, hτ, Complex.mul_conj, Complex.mul_conj, map_zero,
    ← Complex.ofReal_add, Complex.ofReal_eq_zero] at h1
  have h2 := Complex.normSq_pos.2 ((map_ne_zero τ).2 ha)
  have h3 := Complex.normSq_nonneg (τ b)
  linarith
end GlobalTheory.SgGlob.Inhab
