-- Prove2me | solution 1 for GlobalTheory.T.alternating_form_lattice_integrality
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T18:12:01.881805+00:00
-- url     : https://prove2.me/submissions/ba0ef78f-44da-4bc5-8a5c-853e9d1fb9e5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AlternatingFormLatticeIntegrality
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AlternatingFormLatticeIntegralityStatement
import Theorems.Thm_GlobalTheory_exists_alternating_bilinForm_eq_pairing


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open scoped nonZeroDivisors
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {F V : Type} [Field F] [NumberField F] [AddCommGroup V] [Module F V], Module.finrank F V = 2 → ∀ (L : Set V),
    (∀ x ∈ L, ∀ x' ∈ L, x + x' ∈ L) → (∀ (a : 𝓞 F), ∀ x ∈ L, (a : F) • x ∈ L) → ∀ (P : V → V → F),
    (∀ x ∈ L, ∀ x' ∈ L, P x x' = -P x' x) →
    (∀ x₁ ∈ L, ∀ x₂ ∈ L, ∀ x' ∈ L, P (x₁ + x₂) x' = P x₁ x' + P x₂ x') →
    (∀ (a : 𝓞 F), ∀ x ∈ L, ∀ x' ∈ L, P ((a : F) • x) x' = (a : F) * P x x') →
    ∀ {x x' : V}, x ∈ L → x' ∈ L → P x x' ≠ 0 →
    ∃ B : LinearMap.BilinForm F V, (∀ z, B z z = 0) ∧ ∀ z ∈ L, ∀ w ∈ L, P z w = B z w := by
  first | exact @GlobalTheory.exists_alternating_bilinForm_eq_pairing | exact GlobalTheory.exists_alternating_bilinForm_eq_pairing | (intros; apply GlobalTheory.exists_alternating_bilinForm_eq_pairing <;> assumption)
end _root_.GlobalTheory.T
