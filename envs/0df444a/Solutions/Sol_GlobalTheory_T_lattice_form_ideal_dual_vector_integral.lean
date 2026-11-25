-- Prove2me | solution 1 for GlobalTheory.T.lattice_form_ideal_dual_vector_integral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T18:21:27.565111+00:00
-- url     : https://prove2.me/submissions/6016ae16-0860-4dbf-a0fa-9ed6603a54eb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LatticeFormIdealDualVectorIntegral
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LatticeFormIdealDualVectorIntegralStatement
import Theorems.Thm_GlobalTheory_exists_fractionalIdeal_smul_mem_lattice_of_alternating


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
    ∀ (J : FractionalIdeal (𝓞 F)⁰ F), J ≠ 0 → (∀ z ∈ L, ∀ w ∈ L, B z w ∈ J) →
    (∀ t ∈ J, t ∈ Submodule.span (𝓞 F) {t | ∃ z ∈ L, ∃ w ∈ L, t = B z w}) →
    ∀ {v : V}, v ≠ 0 → ∃ I : FractionalIdeal (𝓞 F)⁰ F, I ≠ 0 ∧ ∀ a : F, a ∈ I ↔ a • v ∈ L := by
  first | exact @GlobalTheory.exists_fractionalIdeal_smul_mem_lattice_of_alternating | exact GlobalTheory.exists_fractionalIdeal_smul_mem_lattice_of_alternating | (intros; apply GlobalTheory.exists_fractionalIdeal_smul_mem_lattice_of_alternating <;> assumption)
end _root_.GlobalTheory.T
