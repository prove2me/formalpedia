-- Prove2me | solution 1 for GlobalTheory.T.lattice_vector_pairing_one_ideal_multiple
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:33:54.58747+00:00
-- url     : https://prove2.me/submissions/a7601430-9c5b-4b4c-8885-5660033251a3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LatticeVectorPairingOneIdealMultiple
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LatticeVectorPairingOneIdealMultipleStatement
import Theorems.Thm_GlobalTheory_exists_section_of_fractionalIdeal_values


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
theorem _root_.solution : ∀ {F V : Type} [Field F] [NumberField F] [AddCommGroup V] [Module F V] (B : LinearMap.BilinForm F V) (L : Set V), (0 : V) ∈ L → (∀ x ∈ L, ∀ x' ∈ L, x + x' ∈ L) →
    (∀ (a : 𝓞 F), ∀ x ∈ L, (a : F) • x ∈ L) → ∀ {v : V} (K : FractionalIdeal (𝓞 F)⁰ F), K ≠ 0 →
    (∀ t, t ∈ K ↔ ∃ z ∈ L, t = B z v) → ∃ w : V, B w v = 1 ∧ ∀ t ∈ K, t • w ∈ L := by
  first | exact @GlobalTheory.exists_section_of_fractionalIdeal_values | exact GlobalTheory.exists_section_of_fractionalIdeal_values | (intros; apply GlobalTheory.exists_section_of_fractionalIdeal_values <;> assumption)
end _root_.GlobalTheory.T
