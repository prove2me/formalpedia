-- Prove2me | solution 1 for GlobalTheory.AbCoh.pairToPre_pull2_pairRes
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:33:08.226441+00:00
-- url     : https://prove2.me/submissions/facea602-15c0-4056-bfbb-77f7d78b9b3d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_AxesVanishingStructureSheafDegOne
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_PreUMono
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__AbelianHodgeDeRham_0e03413a4fcf6a02
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CocyclePullbackIffPreimageAffineHom
import Theorems.Thm_GlobalTheory_CatCoh_CoefMap_pullCohomologyTwo_comp
import Theorems.Thm_GlobalTheory_CatCoh_CoefMap_pullCohomologyTwo_eq_of_natTrans


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
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AbCoh
variable {R R' : Type} [CommRing R] [CommRing R'] {X X' : Scheme.{0}} {φ : X' ⟶ X} [IsAffineHom φ]
  {s : X ⟶ Sp R} {s' : X' ⟶ Sp R'} {σ : R →+* R'}
namespace GlobalTheory.AbCoh
theorem _root_.solution (x : HO2 s') :
    (pairToPre φ s').pull2 ((pairRes φ s').pull2 x) = (preRes φ s').pull2 x := by
  rw [← CoefMap.pullCohomologyTwo_comp]
  exact CoefMap.pullCohomologyTwo_eq_of_natTrans _ _ { app U := 𝟙 _ } (fun U b ↦ mp_id (OAff s') _ b) x
end GlobalTheory.AbCoh
