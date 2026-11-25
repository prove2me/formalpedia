-- Prove2me | solution 1 for GlobalTheory.FormalAlg.IsSystem.baseIdeal_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:43:57.573449+00:00
-- url     : https://prove2.me/submissions/ef836595-10eb-4986-8ae1-4e2a4f6d6147

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ThickTransComp
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_BaseIdealIdeal

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
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open GlobalTheory.AbLaw
open GlobalTheory GlobalTheory.FormalAlg
variable {R : Type} [CommRing R] {W : Scheme.{0}}
namespace GlobalTheory.FormalAlg
namespace IsSystem
theorem _root_.solution {f : W ⟶ Spec (CommRingCat.of R)} {I : Ideal R}
    {t : ℕ → W.IdealSheafData} (h : IsSystem f I t) (e : ℕ) : baseIdeal f (I ^ (e + 1)) ≤ t e := by
  rw [h e]
  exact le_sup_right
end IsSystem
end GlobalTheory.FormalAlg
