-- Prove2me | solution 1 for GlobalTheory.exists_isSymplecticBasis
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:32:11.464024+00:00
-- url     : https://prove2.me/submissions/db229012-8ce3-451b-844d-58f5c147ae96

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DualRestrictSurjectiveOfIsTorsionFreeQuotient
import Theorems.Thm_GlobalTheory_exists_isSymplecticFamily_span_eq
import Theorems.Thm_GlobalTheory_IsSymplecticFamily_exists_isSymplecticBasis

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
theorem _root_.solution (hB : B.IsAlt) (hp : Bijective B) :
    ∃ (g : ℕ) (b : Basis (Fin g ⊕ Fin g) R M), IsSymplecticBasis B b := by
  obtain ⟨g, e, f, d, h, hd, -, hspan⟩ := exists_isSymplecticFamily_span_eq hB ⊤
    fun x _ hx => (injective_iff_map_eq_zero B).1 hp.1 x (LinearMap.ext fun y => hx y trivial)
  obtain ⟨b, hb, -⟩ := h.exists_isSymplecticBasis hd hspan hp.2
  exact ⟨g, b, hb⟩
end GlobalTheory
