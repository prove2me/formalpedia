-- Prove2me | solution 1 for GlobalTheory.T.lattice_form_ideal_pair_of_vectors
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T18:23:31.018565+00:00
-- url     : https://prove2.me/submissions/a03c38cc-70f1-479e-a1ce-dc6eeddf000b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LatticeFormIdealPairOfVectors
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LatticeFormIdealPairOfVectorsStatement
import Theorems.Thm_GlobalTheory_lattice_eq_ideal_sum_and_mul_eq


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
theorem _root_.solution : ∀ {F V : Type} [Field F] [NumberField F] [AddCommGroup V] [Module F V], Module.finrank F V = 2 → ∀ (B : LinearMap.BilinForm F V), (∀ z, B z z = 0) → ∀ (L : Set V), (0 : V) ∈ L → (∀ x ∈ L, ∀ x' ∈ L, x + x' ∈ L) → (∀ (a : 𝓞 F), ∀ x ∈ L, (a : F) • x ∈ L) →
    ∀ (J : FractionalIdeal (𝓞 F)⁰ F), (∀ z ∈ L, ∀ w ∈ L, B z w ∈ J) →
    (∀ t ∈ J, t ∈ Submodule.span (𝓞 F) {t | ∃ z ∈ L, ∃ w ∈ L, t = B z w}) →
    ∀ {v w : V}, v ≠ 0 → ∀ (I K : FractionalIdeal (𝓞 F)⁰ F), (∀ a : F, a ∈ I ↔ a • v ∈ L) →
    (∀ t, t ∈ K ↔ ∃ z ∈ L, t = B z v) → B w v = 1 → (∀ t ∈ K, t • w ∈ L) →
    (∀ x, x ∈ L ↔ ∃ a ∈ I, ∃ t ∈ K, x = a • v + t • w) ∧ I * K = J := by
  first | exact @GlobalTheory.lattice_eq_ideal_sum_and_mul_eq | exact GlobalTheory.lattice_eq_ideal_sum_and_mul_eq | (intros; apply GlobalTheory.lattice_eq_ideal_sum_and_mul_eq <;> assumption)
end _root_.GlobalTheory.T
