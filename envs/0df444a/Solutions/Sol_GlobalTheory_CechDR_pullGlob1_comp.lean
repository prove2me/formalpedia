-- Prove2me | solution 1 for GlobalTheory.CechDR.pullGlob1_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:07:43.021806+00:00
-- url     : https://prove2.me/submissions/170a0324-913b-4e2a-aac9-112a51ecc588

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_AxesVanishingStructureSheafDegOne
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__AbelianHodgeDeRham_0e03413a4fcf6a02
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_StructureSheafCohomologyPullbackCompCupId
import Theorems.Thm_GlobalTheory_CechDR_SemiHom_comp
import Theorems.Thm_GlobalTheory_CechDR_SemiHom_oneFormMap_comp_oneFormMap


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
open GlobalTheory GlobalTheory.CechDR
variable {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R'']
  {C C' C'' : Type} [Category.{0} C] [Category.{0} C'] [Category.{0} C'']
  {σ : R →+* R'} {τ : R' →+* R''} {F : C ⥤ CommAlgCat.{0} R} {F' : C' ⥤ CommAlgCat.{0} R'}
  {F'' : C'' ⥤ CommAlgCat.{0} R''}
namespace GlobalTheory.CechDR
theorem _root_.solution (m : CoefMap σ F F') (n : CoefMap τ F' F'') (ω : Glob1 F) :
    pullGlob1 (m.comp n) ω = pullGlob1 n (pullGlob1 m ω) :=
  Subtype.ext (funext fun _ ↦ (SemiHom.oneFormMap_comp_oneFormMap _ _ _ (fun _ ↦ rfl) _).symm)
end GlobalTheory.CechDR
