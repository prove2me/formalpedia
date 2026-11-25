-- Prove2me | solution 1 for GroundTheory.LocalField.card_conjugates_mul_card_inertia
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:40:08.229264+00:00
-- url     : https://prove2.me/submissions/63c894b3-daeb-4240-933a-97b95a262bad

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionCharacters
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionInduced
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionClifford
import Theorems.Thm_GroundTheory_LocalField_comp_conjNormal_eq_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.LocalField
open Module Representation
variable {G : Type*} [Group G] (A : Subgroup G) [hA : A.Normal]
open Classical
namespace GroundTheory.LocalField
theorem _root_.solution [Fintype G] (θ : A → ℂ) :
    (Finset.univ.image fun g : G ↦ θ ∘ conjNormal A g).card * Nat.card (inertia A θ) = Nat.card G := by
  have hcard : ∀ g : G, (Finset.univ.filter fun h : G ↦ θ ∘ conjNormal A h = θ ∘ conjNormal A g).card =
      Nat.card (inertia A θ) := by
    intro g
    rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
    exact Nat.card_congr ((Equiv.mulLeft g⁻¹).subtypeEquiv fun h ↦ by
      rw [comp_conjNormal_eq_iff]
      rfl)
  have h := Finset.card_eq_sum_card_image (fun g : G ↦ θ ∘ conjNormal A g) Finset.univ
  have h2 : ∑ φ ∈ Finset.univ.image (fun g : G ↦ θ ∘ conjNormal A g),
      (Finset.univ.filter fun x : G ↦ θ ∘ conjNormal A x = φ).card =
      ∑ φ ∈ Finset.univ.image (fun g : G ↦ θ ∘ conjNormal A g), Nat.card (inertia A θ) :=
    Finset.sum_congr rfl fun φ hφ ↦ by
      obtain ⟨g, -, rfl⟩ := Finset.mem_image.mp hφ
      exact hcard g
  have h3 := h.trans h2
  rw [Finset.sum_const, smul_eq_mul, Finset.card_univ] at h3
  rw [← h3, Nat.card_eq_fintype_card]
end GroundTheory.LocalField
