-- Prove2me | solution 1 for GlobalTheory.CechDR.pullHH1_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:10:47.245745+00:00
-- url     : https://prove2.me/submissions/7f00b1f7-12a9-42a0-8354-4c29340ff697

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_AxesVanishingStructureSheafDegOne
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__AbelianHodgeDeRham_0e03413a4fcf6a02
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_StructureSheafCohomologyPullbackCompCupId
import Theorems.Thm_GlobalTheory_CechDR_IsPull1_eq_pullHH1
import Theorems.Thm_GlobalTheory_CechDR_SemiHom_comp
import Theorems.Thm_GlobalTheory_CechDR_isPull1_pullHH1
import Theorems.Thm_GlobalTheory_CechDR_isPull_comp


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
theorem _root_.solution (h : φ ≫ s = s' ≫ spMap σ) (h' : ψ ≫ s' = s'' ≫ spMap τ)
    (h'' : (ψ ≫ φ) ≫ s = s'' ≫ spMap (τ.comp σ)) (a : HH1 s) :
    pullHH1 h' (pullHH1 h a) = pullHH1 h'' a :=
  IsPull1.eq_pullHH1 h'' ((isPull_comp h h' h'').1 _ _ _ (isPull1_pullHH1 h a) (isPull1_pullHH1 h' _))
end GlobalTheory.CechDR
