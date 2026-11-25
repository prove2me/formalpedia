-- Prove2me | solution 1 for GlobalTheory.CechDR.toHO1_pullHH1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:13:25.112019+00:00
-- url     : https://prove2.me/submissions/7364ca05-bc96-44ec-ad48-299abfcdcabb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_AxesVanishingStructureSheafDegOne
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__AbelianHodgeDeRham_0e03413a4fcf6a02
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_StructureSheafCohomologyPullbackCompCupId
import Theorems.Thm_GlobalTheory_CechDR_IsPull1_toO
import Theorems.Thm_GlobalTheory_CechDR_IsPullO_eq_pullHO1
import Theorems.Thm_GlobalTheory_CechDR_isPull1_pullHH1


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
variable {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] {X X' X'' : Scheme.{0}}
  {s : X ⟶ Sp R} {s' : X' ⟶ Sp R'} {s'' : X'' ⟶ Sp R''} {σ : R →+* R'} {τ : R' →+* R''}
  {ψ : X'' ⟶ X'} {φ : X' ⟶ X}
namespace GlobalTheory.CechDR
theorem _root_.solution (h : φ ≫ s = s' ≫ spMap σ) (a : HH1 s) :
    toHO1 s' (pullHH1 h a) = pullHO1 h (toHO1 s a) :=
  IsPullO.eq_pullHO1 h (isPull1_pullHH1 h a).toO
end GlobalTheory.CechDR
