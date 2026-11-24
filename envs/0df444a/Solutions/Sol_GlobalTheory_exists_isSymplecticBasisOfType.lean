-- Prove2me | solution 1 for GlobalTheory.exists_isSymplecticBasisOfType
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:42:38.581631+00:00
-- url     : https://prove2.me/submissions/97b07d7f-1e97-467b-a44e-ead9adaff381

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DualRestrictSurjectiveOfIsTorsionFreeQuotient
import Theorems.Thm_GlobalTheory_IsSymplecticFamily_linearIndependent
import Theorems.Thm_GlobalTheory_exists_isSymplecticFamily_span_eq

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
theorem _root_.solution (hB : B.IsAlt) (hnd : Injective B) :
    ∃ (g : ℕ) (b : Basis (Fin g ⊕ Fin g) R M) (d : Fin g → R), IsSymplecticBasisOfType B b d ∧
      (∀ i, d i ≠ 0) ∧ ∀ i j, i ≤ j → d i ∣ d j := by
  obtain ⟨g, e, f, d, h, hd, hdvd, hspan⟩ := exists_isSymplecticFamily_span_eq hB ⊤
    fun x _ hx => (injective_iff_map_eq_zero B).1 hnd x (LinearMap.ext fun y => hx y trivial)
  exact ⟨g, Basis.mk (h.linearIndependent hd) hspan.ge, d,
    by simpa [IsSymplecticBasisOfType] using h, hd, hdvd⟩
end GlobalTheory
