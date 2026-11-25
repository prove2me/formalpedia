-- Prove2me | solution 1 for GlobalTheory.T.finite_image_lattice_of_hom_trivial_on_multiples
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T18:17:10.403434+00:00
-- url     : https://prove2.me/submissions/7d8dd00e-2539-49a0-b890-a47a523ba3d5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LatticeHomFiniteImageOfTrivialOnMultiples
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LatticeHomFiniteImageOfTrivialOnMultiplesStatement
import Theorems.Thm_GlobalTheory_lattice_hom_finite_image_of_trivial_on_multiples


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)) (G : Type) [Group G] (e : (Fin g → ℂ) → G) (N : ℕ),
    DiscreteTopology Λ → Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ → (∀ z w, e (z + w) = e z * e w) → 0 < N →
    (∀ l ∈ Λ, e ((N : ℂ) • l) = 1) → (e '' (Λ : Set (Fin g → ℂ))).Finite := by
  first | exact @GlobalTheory.lattice_hom_finite_image_of_trivial_on_multiples | exact GlobalTheory.lattice_hom_finite_image_of_trivial_on_multiples | (intros; apply GlobalTheory.lattice_hom_finite_image_of_trivial_on_multiples <;> assumption)
end _root_.GlobalTheory.T
