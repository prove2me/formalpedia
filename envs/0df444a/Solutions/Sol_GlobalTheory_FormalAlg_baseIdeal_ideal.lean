-- Prove2me | solution 1 for GlobalTheory.FormalAlg.baseIdeal_ideal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:44:02.921201+00:00
-- url     : https://prove2.me/submissions/994ce53c-2d40-4bbe-aec2-93da9854ce92

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
theorem _root_.solution (f : W ⟶ Spec (CommRingCat.of R)) (J : Ideal R) (U : W.affineOpens) :
    (baseIdeal f J).ideal U = J.map (cst f U.1) := by
  rw [baseIdeal, Scheme.IdealSheafData.ofIdealTop_ideal, Ideal.map_map]
  congr 1
  ext r
  exact rs_cst f le_top r
end GlobalTheory.FormalAlg
