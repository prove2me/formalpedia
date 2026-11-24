-- Prove2me | solution 1 for GlobalTheory.exists_isSymplecticBasis_of_finrank
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:40:44.489572+00:00
-- url     : https://prove2.me/submissions/d3c0f17c-ad35-499f-8985-74939c8acc07

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DualRestrictSurjectiveOfIsTorsionFreeQuotient
import Theorems.Thm_GlobalTheory_IsSymplecticBasisOfType_finrank_eq
import Theorems.Thm_GlobalTheory_IsSymplecticFamily_exists_isSymplecticBasis
import Theorems.Thm_GlobalTheory_exists_isSymplecticBasis

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Function
open GlobalTheory
variable {R M : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] [AddCommGroup M]
  [Module R M] [Module.Free R M] [Module.Finite R M] {B : LinearMap.BilinForm R M}
namespace GlobalTheory
theorem _root_.solution (hB : B.IsAlt) (hp : Bijective B) {g : ℕ}
    (hg : finrank R M = 2 * g) : ∃ b : Basis (Fin g ⊕ Fin g) R M, IsSymplecticBasis B b := by
  obtain ⟨g', b, hb⟩ := exists_isSymplecticBasis hB hp
  have := IsSymplecticBasisOfType.finrank_eq b
  obtain rfl : g' = g := by rw [hg, Fintype.card_fin] at this; omega
  exact ⟨b, hb⟩
end GlobalTheory
