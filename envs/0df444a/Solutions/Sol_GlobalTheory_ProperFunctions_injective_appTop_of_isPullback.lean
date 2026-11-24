-- Prove2me | solution 1 for GlobalTheory.ProperFunctions.injective_appTop_of_isPullback
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T20:14:09.608798+00:00
-- url     : https://prove2.me/submissions/41e89440-109f-45ec-94b0-5814aa444e1c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIsoAppTopOfIsPullbackOfSurjective
import Theorems.Thm_GlobalTheory_ProperFunctions_mem_map_ker_of_app_eq_zero
import Theorems.Thm_GlobalTheory_ProperFunctions_eq_zero_of_forall_affineOpens

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
variable {X Y S T : Scheme.{u}} {f : T ⟶ S} {g : Y ⟶ X} {p : X ⟶ S} {q : Y ⟶ T}
namespace GlobalTheory.ProperFunctions
theorem _root_.solution (H : IsPullback g q p f) [IsAffine S] [IsAffine T] [Flat p]
    (hf : Function.Injective f.appTop) : Function.Injective g.appTop := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  refine eq_zero_of_forall_affineOpens x fun U ↦ ?_
  have := mem_map_ker_of_app_eq_zero H U.2 (X.presheaf.map (homOfLE (le_top : U.1 ≤ ⊤)).op x) (by
    rw [← CommRingCat.comp_apply, g.naturality, CommRingCat.comp_apply]
    erw [hx]
    exact map_zero _)
  rwa [(RingHom.injective_iff_ker_eq_bot _).mp hf, Ideal.map_bot, Ideal.mem_bot] at this
end GlobalTheory.ProperFunctions
