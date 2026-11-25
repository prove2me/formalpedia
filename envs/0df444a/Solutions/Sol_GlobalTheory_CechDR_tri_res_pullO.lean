-- Prove2me | solution 1 for GlobalTheory.CechDR.tri_res_pullO
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:11:27.472483+00:00
-- url     : https://prove2.me/submissions/ebffb75d-135a-4f54-a90b-c06dbf19c6b8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_AxesVanishingStructureSheafDegOne
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__AbelianHodgeDeRham_0e03413a4fcf6a02
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_StructureSheafCohomologyPullbackCompCupId
import Theorems.Thm_GlobalTheory_CechDR_pullGlob1_comp
import Theorems.Thm_GlobalTheory_CechDR_pullGlob1_eq_of_natTrans
import Theorems.Thm_GlobalTheory_CatCoh_CoefMap_pullCohomologyOne_comp
import Theorems.Thm_GlobalTheory_CatCoh_CoefMap_pullCohomologyOne_eq_of_natTrans
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
open GlobalTheory GlobalTheory.CechDR
variable {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] {X X' X'' : Scheme.{0}}
  {s : X ⟶ Sp R} {s' : X' ⟶ Sp R'} {s'' : X'' ⟶ Sp R''} {σ : R →+* R'} {τ : R' →+* R''}
  {ψ : X'' ⟶ X'} {φ : X' ⟶ X}
namespace GlobalTheory.CechDR
theorem _root_.solution (h' : ψ ≫ s' = s'' ≫ spMap τ) :
    (∀ a : HO1 s', (cechTriplePullbackSecond (φ := φ) h').pull1 ((pairRes φ s').pull1 a) =
      (cechTripleRestrictFirst ψ φ s'').pull1 ((pairPull h').pull1 a)) ∧
    (∀ a : HO2 s', (cechTriplePullbackSecond (φ := φ) h').pull2 ((pairRes φ s').pull2 a) =
      (cechTripleRestrictFirst ψ φ s'').pull2 ((pairPull h').pull2 a)) ∧
    (∀ a : GlobForm s', pullGlob1 (cechTriplePullbackSecond (φ := φ) h') (pullGlob1 (pairRes φ s') a) =
      pullGlob1 (cechTripleRestrictFirst ψ φ s'') (pullGlob1 (pairPull h') a)) := by
  refine ⟨fun a ↦ ?_, fun a ↦ ?_, fun a ↦ ?_⟩
  · rw [← CoefMap.pullCohomologyOne_comp, ← CoefMap.pullCohomologyOne_comp]
    exact CoefMap.pullCohomologyOne_eq_of_natTrans _ _ { app U := 𝟙 _ } (fun U b ↦ by erw [mp_id]) a
  · rw [← CoefMap.pullCohomologyTwo_comp, ← CoefMap.pullCohomologyTwo_comp]
    exact CoefMap.pullCohomologyTwo_eq_of_natTrans _ _ { app U := 𝟙 _ } (fun U b ↦ by erw [mp_id]) a
  · rw [← pullGlob1_comp, ← pullGlob1_comp]
    exact pullGlob1_eq_of_natTrans _ _ { app U := 𝟙 _ } (fun U b ↦ by erw [mp_id]) a
end GlobalTheory.CechDR
