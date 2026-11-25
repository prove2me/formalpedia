-- Prove2me | solution 1 for GlobalTheory.CNorm.mem_powSub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:37:15.680133+00:00
-- url     : https://prove2.me/submissions/9229cf17-4b3b-435d-82f8-77bf9fa1f0e0

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
    (x : Fˣ) : x ∈ _root_.GlobalTheory.CNorm.powSub p φ ↔ ∃ r : L, r ^ p = φ (x : F) := Iff.rfl
end _root_.GlobalTheory.CNorm
end GlobalTheory.CNorm
