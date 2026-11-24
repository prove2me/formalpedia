-- Prove2me | solution 1 for GlobalTheory.CNorm.mem_kNorm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:06:43.418971+00:00
-- url     : https://prove2.me/submissions/9f3ec28f-7366-42f6-b411-e27d110a07a9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_SqSubLeNormSub
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_MemPowSub

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Polynomial
open scoped TensorProduct
noncomputable section
open GlobalTheory GlobalTheory.CNorm
open NumberField IsDedekindDomain Polynomial
open scoped TensorProduct
namespace GlobalTheory.CNorm
namespace _root_.GlobalTheory.CNorm
theorem _root_.solution (p : ℕ) {F L : Type} [Field F] [Field L] (φ : F →+* L)
    (δ : F) (x : Fˣ) :
    x ∈ _root_.GlobalTheory.CNorm.kNorm p φ δ ↔ ∃ y : (AdjoinRoot (X ^ p - C (φ δ) : L[X]))ˣ,
      Algebra.norm L (y : AdjoinRoot (X ^ p - C (φ δ) : L[X])) = φ (x : F) := by
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨y, by simpa using congrArg Units.val hy⟩
  · rintro ⟨y, hy⟩
    exact ⟨y, Units.ext (by simpa using hy)⟩
end _root_.GlobalTheory.CNorm
end GlobalTheory.CNorm
