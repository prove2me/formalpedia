-- Prove2me | solution 1 for GlobalTheory.dualRestrict_surjective_of_isTorsionFree_quotient
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:55:33.136184+00:00
-- url     : https://prove2.me/submissions/487d1098-d2c9-4314-a589-ec009ed05c59

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DualRestrictSurjectiveOfIsTorsionFreeQuotient
import Theorems.Thm_GlobalTheory_orthogonalQuotientForm_mk
import Theorems.Thm_GlobalTheory_exists_projection_of_isTorsionFree_quotient
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.orthogonalQuotientForm_mk

set_option autoImplicit false
open Module Function
open GlobalTheory
variable {R M : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] [AddCommGroup M]
  [Module R M] [Module.Finite R M] {B : LinearMap.BilinForm R M} {I : Submodule R M}
namespace GlobalTheory
theorem _root_.solution (hI : IsTorsionFree R (M ⧸ I)) :
    Surjective I.dualRestrict := by
  obtain ⟨p, hp⟩ := exists_projection_of_isTorsionFree_quotient hI
  exact fun φ => ⟨φ ∘ₗ p, LinearMap.ext fun x => by simp [hp]⟩
end GlobalTheory
