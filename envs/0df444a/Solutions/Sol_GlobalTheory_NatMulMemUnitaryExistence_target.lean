-- Prove2me | solution 1 for GlobalTheory.NatMulMemUnitaryExistence.target
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:12:13.205258+00:00
-- url     : https://prove2.me/submissions/7bf07489-6a78-48db-bda0-87c7c7b2a0f4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsNatMulMem
import Theorems.Thm_GlobalTheory_NatMulMemUnitaryExistence_main

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.NatMulMemUnitaryExistence
open NumberField
namespace GlobalTheory.NatMulMemUnitaryExistence
theorem _root_.solution : ∀ {E : Type} [inst : Field E] [NumberField E] {n : ℕ}
    (L : Submodule (NumberField.RingOfIntegers E) (Fin n → E)),
    Submodule.span E (↑L : Set (Fin n → E)) = ⊤ → ∀ (x : Fin n → E), ∃ (d : ℕ), (0 : ℕ) < d ∧ d • x ∈ L :=
  fun L hL x => main L hL x
end GlobalTheory.NatMulMemUnitaryExistence
