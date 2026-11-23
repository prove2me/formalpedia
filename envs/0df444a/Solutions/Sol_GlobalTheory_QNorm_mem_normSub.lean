-- Prove2me | solution 1 for GlobalTheory.QNorm.mem_normSub
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:27:49.700798+00:00
-- url     : https://prove2.me/submissions/348a1ef9-e8e7-4bfd-89b3-d239c8fd7232

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_SqSubLeNormSub

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
open scoped WithZero
noncomputable section
open GlobalTheory GlobalTheory.QNorm
namespace GlobalTheory.QNorm
theorem _root_.solution {F L : Type} [Field F] [Field L] (φ : F →+* L) (δ : F) (x : Fˣ) :
    x ∈ normSub φ δ ↔ ∃ a b : L, φ (x : F) = a ^ 2 - φ δ * b ^ 2 := Iff.rfl
end GlobalTheory.QNorm
