-- Prove2me | solution 1 for GlobalTheory.IsIntegralDetLattice.isIntegral_det_of_preserves_lattice
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T18:28:27.335975+00:00
-- url     : https://prove2.me/submissions/1621d28a-16f9-4431-9d5f-639876bd61e0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_IsIntegralDetOfPreservesLattice
import Theorems.Thm_GlobalTheory_IsIntegralDetLattice_isIntegral_det
import Theorems.Thm_GlobalTheory_IsIntegralDetLattice_isIntegral_of_preserves

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory GlobalTheory.IsIntegralDetLattice
namespace GlobalTheory.IsIntegralDetLattice
theorem _root_.solution {E : Type} [Field E] [NumberField E] {N : ℕ}
    (L : Submodule (NumberField.RingOfIntegers E) (Fin N → E)) (hL : L.FG)
    (hs : Submodule.span E (↑L : Set (Fin N → E)) = ⊤) (γ : Matrix (Fin N) (Fin N) E)
    (hγ : ∀ v ∈ L, γ.mulVec v ∈ L) : IsIntegral ℤ γ.det := by
  exact isIntegral_trans _ (isIntegral_det γ (isIntegral_of_preserves L hL hs γ hγ))
end GlobalTheory.IsIntegralDetLattice
