-- Prove2me | solution 1 for GlobalTheory.AbCoh.red_iff_pre
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:08:02.215073+00:00
-- url     : https://prove2.me/submissions/64c42c02-46e2-4597-be11-86fa21b1e3b7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_AxesVanishingStructureSheafDegOne
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_PreUMono
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__AbelianHodgeDeRham_0e03413a4fcf6a02
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CocyclePullbackIffPreimageAffineHom
import Theorems.Thm_GlobalTheory_AbCoh_pairToPre_pull1_pairRes
import Theorems.Thm_GlobalTheory_AbCoh_pairToPre_pull2_pairRes
import Theorems.Thm_GlobalTheory_AbCoh_preToPairRes_pull1_preRes
import Theorems.Thm_GlobalTheory_AbCoh_preToPairRes_pull2_preRes
import Theorems.Thm_GlobalTheory_AbCoh_pairToPre_pull1_pairPull
import Theorems.Thm_GlobalTheory_AbCoh_pairToPre_pull2_pairPull
import Theorems.Thm_P2M_GlobalTheory_AbCoh_preToPairRes_pre__191ebb21c4d1
import Theorems.Thm_GlobalTheory_CatCoh_CoefMap_pullCohomologyOne_class
import Theorems.Thm_GlobalTheory_CatCoh_CoefMap_pullCohomologyTwo_class
import Theorems.Thm_GlobalTheory_CechDR_isPullO_pullHO1


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
open GlobalTheory GlobalTheory.AbCoh
namespace GlobalTheory.AbCoh
theorem _root_.solution : ∀ (R R' : Type) [CommRing R] [CommRing R'] (X X' : Scheme.{0}) (s : X ⟶ Sp R) (s' : X' ⟶ Sp R') (σ : R →+* R') (φ : X' ⟶ X) (h : φ ≫ s = s' ≫ spMap σ) [IsAffineHom φ], (∀ (f : C1 (OAff s)) (x : HO1 s'), Red1 h f x ↔ ∃ c : Z1 (OPre φ s'), (∀ U V (a : U ⟶ V), c.1 U V a = preα φ s s' V (f U V a)) ∧ GlobalTheory.CatCoh.H1.mk _ c = (preRes φ s').pull1 x) ∧ (∀ (v : C2 (OAff s)) (z : HO2 s'), Red2 h v z ↔ ∃ c : Z2 (OPre φ s'), (∀ U V W (a : U ⟶ V) (b : V ⟶ W), c.1 U V W a b = preα φ s s' W (v U V W a b)) ∧ GlobalTheory.CatCoh.H2.mk _ c = (preRes φ s').pull2 z) ∧ (∀ y, (preRes φ s').pull1 (pullHO1 h y) = (preCoef h).pull1 y) ∧ ∀ y, (preRes φ s').pull2 (pullHO2 h y) = (preCoef h).pull2 y := by
  intro R R' _ _ X X' s s' σ φ h _
  refine ⟨fun f x ↦ ⟨?_, ?_⟩, fun v z ↦ ⟨?_, ?_⟩, fun y ↦ ?_, fun y ↦ ?_⟩
  · rintro ⟨c, hc, hx⟩
    refine ⟨(pairToPre φ s').pullbackOneCocycle c, fun U V a ↦ hc _ _ _, ?_⟩
    rw [← CoefMap.pullCohomologyOne_class, hx, pairToPre_pull1_pairRes]
  · rintro ⟨c, hc, hx⟩
    refine ⟨(preToPairRes φ s').pullbackOneCocycle c, fun p q a ↦ ?_, ?_⟩
    · rw [CoefMap.pullCocycleOne_apply, hc]
      exact preToPairRes_preα h q _
    · rw [← CoefMap.pullCohomologyOne_class, hx, preToPairRes_pull1_preRes]
  · rintro ⟨c, hc, hx⟩
    refine ⟨(pairToPre φ s').pullbackTwoCocycle c, fun U V W a b ↦ hc _ _ _ _ _, ?_⟩
    rw [← CoefMap.pullCohomologyTwo_class, hx, pairToPre_pull2_pairRes]
  · rintro ⟨c, hc, hx⟩
    refine ⟨(preToPairRes φ s').pullbackTwoCocycle c, fun p q r a b ↦ ?_, ?_⟩
    · rw [CoefMap.pullCocycleTwo_apply, hc]
      exact preToPairRes_preα h r _
    · rw [← CoefMap.pullCohomologyTwo_class, hx, preToPairRes_pull2_preRes]
  · have e := congrArg (pairToPre φ s').pull1 (isPullO_pullHO1 h y)
    rw [pairToPre_pull1_pairPull, pairToPre_pull1_pairRes] at e
    exact e.symm
  · have e : (pairRes φ s').pull2 (pullHO2 h y) = (pairPull h).pull2 y :=
      (LinearEquiv.ofBijective (pairRes φ s').pull2 (pairRes_pull2_bijective φ s')).apply_symm_apply _
    have e' := congrArg (pairToPre φ s').pull2 e
    rw [pairToPre_pull2_pairPull, pairToPre_pull2_pairRes] at e'
    exact e'
end GlobalTheory.AbCoh
