-- Prove2me | solution 1 for GlobalTheory.finrank_int_eq_finrank_ringOfIntegers_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:56:44.269452+00:00
-- url     : https://prove2.me/submissions/ae77f250-b311-4de2-9065-3e0eb9b08077

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FinrankIntEqFinrankRingOfIntegersMul

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
open TensorProduct nonZeroDivisors
namespace GlobalTheory
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] (N : Type) [AddCommGroup N] [Module (𝓞 E) N] [Module.Free ℤ N] [Module.Finite ℤ N], Module.finrank ℤ N = Module.finrank (𝓞 E) N * Module.finrank ℚ E := by
  intro E _ _ N _ _ _ _
  let g : N →ₗ[𝓞 E] E ⊗[𝓞 E] N := TensorProduct.mk (𝓞 E) E N 1
  have hb : IsBaseChange E g := TensorProduct.isBaseChange (𝓞 E) N E
  have h1 : Module.finrank E (E ⊗[𝓞 E] N) = Module.finrank (𝓞 E) N := hb.finrank_eq
  haveI : IsLocalization (Algebra.algebraMapSubmonoid (𝓞 E) ℤ⁰) E := inferInstance
  haveI h2 : IsLocalizedModule (Algebra.algebraMapSubmonoid (𝓞 E) ℤ⁰) g :=
    (isLocalizedModule_iff_isBaseChange _ E g).2 hb
  haveI h3 : IsLocalizedModule ℤ⁰ (g.restrictScalars ℤ) :=
    IsLocalizedModule.restrictScalars ℤ⁰ g
  have h4 : Module.finrank ℤ (E ⊗[𝓞 E] N) = Module.finrank ℤ N :=
    IsLocalizedModule.finrank_eq ℤ⁰ (g.restrictScalars ℤ) le_rfl
  have h5 : Module.finrank ℚ (E ⊗[𝓞 E] N) = Module.finrank ℤ (E ⊗[𝓞 E] N) :=
    IsFractionRing.finrank_right_eq ℤ ℚ _
  rw [← h4, ← h5, ← h1, mul_comm, Module.finrank_mul_finrank]
end GlobalTheory
