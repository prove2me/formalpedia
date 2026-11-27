-- Prove2me | solution 1 for GlobalTheory.T.cechDeRhamHypercohomologyCup_anticomm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:34:37.431668+00:00
-- url     : https://prove2.me/submissions/21d4cdba-bc53-48ee-bb43-3f90192f3217

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CechDeRhamHypercohomologyCupAnticomm
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_AxesVanishingStructureSheafDegOne
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__AbelianHodgeDeRham_0e03413a4fcf6a02
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CechDeRhamHypercohomologyCupAnticommStatement
import Theorems.Thm_GlobalTheory_AbCoh_cupHyp_add_cupHyp_swap


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (R : Type) [CommRing R] (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R), ∀ a b : Hyp1 F, cupHyp F a b + cupHyp F b a = 0 := by
  first | exact @GlobalTheory.AbCoh.cupHyp_add_cupHyp_swap | exact GlobalTheory.AbCoh.cupHyp_add_cupHyp_swap | (intros; apply GlobalTheory.AbCoh.cupHyp_add_cupHyp_swap <;> assumption)
end _root_.GlobalTheory.T
