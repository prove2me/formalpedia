-- Prove2me | solution 1 for GlobalTheory.AbCoh.pullHO2_surjective_of_wedge
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:05:59.664108+00:00
-- url     : https://prove2.me/submissions/981c9331-d1a8-4e73-affc-ec44c42a92b3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_AxesVanishingStructureSheafDegOne
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__AbelianHodgeDeRham_0e03413a4fcf6a02
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_StructureSheafCohomologyPullbackCompCupIdStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PullCupOfBijective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SurjectivePullHO2OfPullHO1
import Theorems.Thm_GlobalTheory_PullbackCupProduct_main


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
set_option autoImplicit false
open GlobalTheory GlobalTheory.AbCoh
namespace GlobalTheory.AbCoh
theorem _root_.solution : ∀ (R R' : Type) [CommRing R] [CommRing R'] (X X' : Scheme.{0})
    (s : X ⟶ Sp R) (s' : X' ⟶ Sp R') (σ : R →+* R') (φ : X' ⟶ X) (h : φ ≫ s = s' ≫ spMap σ),
    Function.Surjective (pullHO1 h) → WedgeO (OAff s') → Function.Surjective (pullHO2 h) := by
  first
  | exact @_root_.GlobalTheory.PullbackCupProduct.main
  | exact _root_.GlobalTheory.PullbackCupProduct.main
  | (apply _root_.GlobalTheory.PullbackCupProduct.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.PullbackCupProduct.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.PullbackCupProduct.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.PullbackCupProduct.main ..)
end GlobalTheory.AbCoh
