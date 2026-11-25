-- Prove2me | solution 1 for GlobalTheory.CechDR.pullHO2_cup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:00:37.635806+00:00
-- url     : https://prove2.me/submissions/d0eac575-26b4-416f-b0a2-bf080b40952e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_AxesVanishingStructureSheafDegOne
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__AbelianHodgeDeRham_0e03413a4fcf6a02
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_StructureSheafCohomologyPullbackCompCupId
import Theorems.Thm_GlobalTheory_CechDR_eq_pullHO2
import Theorems.Thm_GlobalTheory_CatCoh_CoefMap_pullCohomologyTwo_cup
import Theorems.Thm_GlobalTheory_CechDR_IsPull1_cup
import Theorems.Thm_GlobalTheory_CechDR_isPullO_pullHO1
import Theorems.Thm_GlobalTheory_Cris_IsMor_pullCohomologyTwo_cup


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
theorem _root_.solution (h : φ ≫ s = s' ≫ spMap σ) (a b : HO1 s) :
    pullHO2 h (cup _ a b) = cup _ (pullHO1 h a) (pullHO1 h b) := by
  refine (eq_pullHO2 h ?_).symm
  rw [CoefMap.pullCohomologyTwo_cup, CoefMap.pullCohomologyTwo_cup, isPullO_pullHO1 h a, isPullO_pullHO1 h b]
end GlobalTheory.CechDR
