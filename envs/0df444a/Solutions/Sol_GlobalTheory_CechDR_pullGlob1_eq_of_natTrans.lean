-- Prove2me | solution 1 for GlobalTheory.CechDR.pullGlob1_eq_of_natTrans
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:21:58.435449+00:00
-- url     : https://prove2.me/submissions/b8f46e53-8452-4bdc-af7e-8aeb82cbad2a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_AxesVanishingStructureSheafDegOne
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__AbelianHodgeDeRham_0e03413a4fcf6a02
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_StructureSheafCohomologyPullbackCompCupId
import Theorems.Thm_GlobalTheory_CechDR_cechDeRhamCoefMapOneForms_eq_of_natTrans


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
theorem _root_.solution (m : CoefMap σ F F') {σ' : R →+* R'} (m' : CoefMap σ' F F')
    (θ : m.G ⟶ m'.G) (h : ∀ T b, m'.α T (mp F (θ.app T) b) = m.α T b) (ω : Glob1 F) :
    pullGlob1 m ω = pullGlob1 m' ω :=
  Subtype.ext (funext fun T ↦ by
    change q1 m T (ω.1 _) = q1 m' T (ω.1 _)
    rw [ω.2 (θ.app T), cechDeRhamCoefMapOneForms_eq_of_natTrans m m' θ h])
end GlobalTheory.CechDR
