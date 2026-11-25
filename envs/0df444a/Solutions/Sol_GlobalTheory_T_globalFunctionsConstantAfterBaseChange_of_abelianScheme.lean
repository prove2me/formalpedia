-- Prove2me | solution 1 for GlobalTheory.T.globalFunctionsConstantAfterBaseChange_of_abelianScheme
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T18:18:33.290134+00:00
-- url     : https://prove2.me/submissions/3e8d0ab8-2bdb-4409-9acf-5e02ed434a49

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GlobalFunctionsConstantAfterBaseChangeOfAbelianS
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_AxesVanishingStructureSheafDegOne
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__AbelianHodgeDeRham_0e03413a4fcf6a02
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GlobalFunctionsConstantAfterBaseChangeOfAbelianSStatement
import Theorems.Thm_GlobalTheory_AbCoh_uConst_of_isAbelianScheme


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
theorem _root_.solution : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A → UConst A.hom := by
  first | exact @GlobalTheory.AbCoh.uConst_of_isAbelianScheme | exact GlobalTheory.AbCoh.uConst_of_isAbelianScheme | (intros; apply GlobalTheory.AbCoh.uConst_of_isAbelianScheme <;> assumption)
end _root_.GlobalTheory.T
