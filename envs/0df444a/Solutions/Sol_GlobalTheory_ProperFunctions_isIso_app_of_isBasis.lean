-- Prove2me | solution 1 for GlobalTheory.ProperFunctions.isIso_app_of_isBasis
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T19:38:48.853857+00:00
-- url     : https://prove2.me/submissions/414b58ae-c3be-42b2-9c98-71e3eb5989b0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIsoAppTopOfIsPullbackOfSurjective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry TensorProduct Opposite
universe u
open GlobalTheory
open GlobalTheory.ProperFunctions
variable {X Y S T : Scheme.{u}}
namespace GlobalTheory.ProperFunctions
theorem _root_.solution (p : X ⟶ S) {ι : Type*} (B : ι → S.Opens)
    (hB : TopologicalSpace.Opens.IsBasis (Set.range B))
    (h : ∀ i, IsIso (p ∣_ B i).appTop) (U : S.Opens) : IsIso (p.app U) := by
  have h1 : ∀ i, IsIso (p.app (B i)) := by
    intro i
    have := h i
    rw [morphismRestrict_appTop] at this
    have := (@isIso_comp_right_iff _ _ _ _ _ (p.app ((B i).ι ''ᵁ ⊤)) _
      (by rw [eqToHom_op]; exact Functor.map_isIso _ _)).mp this
    rwa [(B i).ι_image_top] at this
  let φ : S.sheaf ⟶ (TopCat.Sheaf.pushforward _ p.base).obj X.sheaf := ⟨p.c⟩
  have : IsIso φ := TopCat.Sheaf.isIso_iff_isIso_basis hB h1
  have : IsIso p.c := (TopCat.Sheaf.forget _ _).map_isIso φ
  exact inferInstanceAs (IsIso (p.c.app (op U)))
end GlobalTheory.ProperFunctions
