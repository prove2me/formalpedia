-- Prove2me | solution 1 for GlobalTheory.IntegralMultiples.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:52:50.94142+00:00
-- url     : https://prove2.me/submissions/1e3b47d4-ad80-4c01-9bf4-bf05c1dfc72d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_ExistsIntMulMem
import Theorems.Thm_GlobalTheory_IntegralMultiples_exists_int_smul_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.IntegralMultiples
namespace GlobalTheory.IntegralMultiples
theorem _root_.solution : ∀ {E : Type} [inst : Field E] [NumberField E] {r : ℕ}
    (Λ : Submodule (NumberField.RingOfIntegers E) (Fin r → E)),
    Submodule.span E (↑Λ : Set (Fin r → E)) = ⊤ →
      ∀ (v : Fin r → E), ∃ (k : ℤ), k ≠ (0 : ℤ) ∧ k • v ∈ Λ := by
  intro E _ _ r Λ hΛ v
  exact exists_int_smul_mem Λ hΛ v
end GlobalTheory.IntegralMultiples
