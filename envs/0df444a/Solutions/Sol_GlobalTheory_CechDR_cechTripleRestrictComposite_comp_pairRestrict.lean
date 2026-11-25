-- Prove2me | solution 1 for GlobalTheory.CechDR.cechTripleRestrictComposite_comp_pairRestrict
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:42:01.876917+00:00
-- url     : https://prove2.me/submissions/2a8896a3-8ef9-4b74-a6fb-346df4b639b2

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
variable (ψ φ)
namespace GlobalTheory.CechDR
theorem _root_.solution (s'' : X'' ⟶ Sp R'') :
    (∀ c : HO1 s'', (cechTripleRestrictComposite ψ φ s'').pull1 ((pairRes (ψ ≫ φ) s'').pull1 c) =
      (CoefMap.restrict (OAff s'') (cechTripleProjFirstThird ψ φ ⋙ pairFst (ψ ≫ φ))).pull1 c) ∧
    (∀ c : HO2 s'', (cechTripleRestrictComposite ψ φ s'').pull2 ((pairRes (ψ ≫ φ) s'').pull2 c) =
      (CoefMap.restrict (OAff s'') (cechTripleProjFirstThird ψ φ ⋙ pairFst (ψ ≫ φ))).pull2 c) ∧
    (∀ c : GlobForm s'', pullGlob1 (cechTripleRestrictComposite ψ φ s'') (pullGlob1 (pairRes (ψ ≫ φ) s'') c) =
      pullGlob1 (CoefMap.restrict (OAff s'') (cechTripleProjFirstThird ψ φ ⋙ pairFst (ψ ≫ φ))) c) := by
  refine ⟨fun c ↦ ?_, fun c ↦ ?_, fun c ↦ ?_⟩
  · rw [← CoefMap.pullCohomologyOne_comp]
    exact CoefMap.pullCohomologyOne_eq_of_natTrans _ _ { app U := 𝟙 _ } (fun U b ↦ mp_id (OAff s'') _ b) c
  · rw [← CoefMap.pullCohomologyTwo_comp]
    exact CoefMap.pullCohomologyTwo_eq_of_natTrans _ _ { app U := 𝟙 _ } (fun U b ↦ mp_id (OAff s'') _ b) c
  · rw [← pullGlob1_comp]
    exact pullGlob1_eq_of_natTrans _ _ { app U := 𝟙 _ } (fun U b ↦ mp_id (OAff s'') _ b) c
end GlobalTheory.CechDR
