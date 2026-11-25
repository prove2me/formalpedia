-- Prove2me | solution 1 for GlobalTheory.CechDR.tri_res_resO
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:49:41.60745+00:00
-- url     : https://prove2.me/submissions/2773f826-505a-4173-ad03-6db374eb336b

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
    (∀ a : HO1 s'', (cechTripleRestrictFirst ψ φ s'').pull1 ((pairRes ψ s'').pull1 a) =
      (cechTripleRestrictComposite ψ φ s'').pull1 ((pairRes (ψ ≫ φ) s'').pull1 a)) ∧
    (∀ a : HO2 s'', (cechTripleRestrictFirst ψ φ s'').pull2 ((pairRes ψ s'').pull2 a) =
      (cechTripleRestrictComposite ψ φ s'').pull2 ((pairRes (ψ ≫ φ) s'').pull2 a)) ∧
    (∀ a : GlobForm s'', pullGlob1 (cechTripleRestrictFirst ψ φ s'') (pullGlob1 (pairRes ψ s'') a) =
      pullGlob1 (cechTripleRestrictComposite ψ φ s'') (pullGlob1 (pairRes (ψ ≫ φ) s'') a)) := by
  refine ⟨fun a ↦ ?_, fun a ↦ ?_, fun a ↦ ?_⟩
  · rw [← CoefMap.pullCohomologyOne_comp, ← CoefMap.pullCohomologyOne_comp]
    exact CoefMap.pullCohomologyOne_eq_of_natTrans _ _ { app U := 𝟙 _ } (fun U b ↦ mp_id (OAff s'') _ b) a
  · rw [← CoefMap.pullCohomologyTwo_comp, ← CoefMap.pullCohomologyTwo_comp]
    exact CoefMap.pullCohomologyTwo_eq_of_natTrans _ _ { app U := 𝟙 _ } (fun U b ↦ mp_id (OAff s'') _ b) a
  · rw [← pullGlob1_comp, ← pullGlob1_comp]
    exact pullGlob1_eq_of_natTrans _ _ { app U := 𝟙 _ } (fun U b ↦ mp_id (OAff s'') _ b) a
end GlobalTheory.CechDR
