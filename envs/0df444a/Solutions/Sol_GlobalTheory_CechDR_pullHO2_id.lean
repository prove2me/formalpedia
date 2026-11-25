-- Prove2me | solution 1 for GlobalTheory.CechDR.pullHO2_id
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:08:33.448418+00:00
-- url     : https://prove2.me/submissions/64315e5e-9f73-4e44-b9e6-dbb6a8d0a515

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_AxesVanishingStructureSheafDegOne
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__AbelianHodgeDeRham_0e03413a4fcf6a02
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_StructureSheafCohomologyPullbackCompCupId
import Theorems.Thm_GlobalTheory_CechDR_eq_pullHO2
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
open GlobalTheory GlobalTheory.CechDR
variable {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] {X X' X'' : Scheme.{0}}
  {s : X ⟶ Sp R} {s' : X' ⟶ Sp R'} {s'' : X'' ⟶ Sp R''} {σ : R →+* R'} {τ : R' →+* R''}
  {ψ : X'' ⟶ X'} {φ : X' ⟶ X}
namespace GlobalTheory.CechDR
theorem _root_.solution (h : 𝟙 X ≫ s = s ≫ spMap (RingHom.id R)) (c : HO2 s) : pullHO2 h c = c :=
  (eq_pullHO2 h (CoefMap.pullCohomologyTwo_eq_of_natTrans (pairPull h) (pairRes _ s) (pairIdTrans X)
    (fun _ _ ↦ rfl) c)).symm
end GlobalTheory.CechDR
