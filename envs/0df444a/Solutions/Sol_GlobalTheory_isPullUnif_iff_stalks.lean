-- Prove2me | solution 1 for GlobalTheory.isPullUnif_iff_stalks
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:47:10.218994+00:00
-- url     : https://prove2.me/submissions/505176de-6d5c-46a9-9b82-3b96e0b197f1

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_GmMulEqOfResMulEq
import Theorems.Thm_GlobalTheory_square_res_iff_gw
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_maps_iff


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
noncomputable section
open GlobalTheory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
namespace GlobalTheory
theorem _root_.solution : ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (I : Ideal R) (I' : Ideal R') (φ : R →+* R') (D : DegData R I) (D' : DegData R' I') (hD : IsPullDeg φ D.toPre D'.toPre) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (A' : PolAV (Spec (CommRingCat.of (FractionRing R')))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (G' : Over (Spec (CommRingCat.of R'))) [GrpObj G'] [IsCommMonObj G'] (bc : G' ≅ (Over.pullback (specOf φ)).obj G) (U : Unif I D A G) (U' : Unif I' D' A' G'), IsPullUnif φ hD bc U U' ↔ ∃ wL : LB.Iso U'.LG.L (U.LG.L.pull (bc.hom.left ≫ pullback.fst G.hom (specOf φ))), wL.IsGen ∧ ∃ he : eSec G' ≫ bc.hom.left ≫ pullback.fst G.hom (specOf φ) = specOf φ ≫ eSec G, LB.Gen.Maps (LB.linCombIso wL (K := PUnit) (fun _ => eSec G') (fun _ => 1)) U'.LG.rig (rigPullOf (bc.hom.left ≫ pullback.fst G.hom (specOf φ)) (specOf φ) he U.LG.L U.LG.rig) ∧ ∀ e : ℕ, ∃ (h : (thickObj R' I' e G').left ⟶ (thickObj R I e G).left), h ≫ (fstG I e G).left = (fstG I' e G').left ≫ (bc.hom.left ≫ pullback.fst G.hom (specOf φ)) ∧ ((U'.gt e).pG.left ≫ (hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf φ)) = h ≫ (U.gt e).pG.left ∧ ∀ x : D'.toPre.X, (∀ κ : Fin 4, D'.toPre.Oφ (U'.gt e).pG x κ ≫ (hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf φ)) = h ≫ D.toPre.Oφ (U.gt e).pG (hD.xe x) κ) ∧ Geo.Tor.PMaps hD.w (D'.toPre.Oφ (U'.gt e).pG x) (D.toPre.Oφ (U.gt e).pG (hD.xe x)) Oinvε ((U'.gt e).t x) ((U.gt e).t (hD.xe x)) h) ∧ (∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R' I' e G').left) (z : Z) (jM : D.toPre.P.L.ι) (jM' : D'.toPre.P.L.ι) (jL : U.LG.L.ι) (jL' : U'.LG.L.ι), ((hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf φ))) ((U'.gt e).pG.left (r z)) ∈ D.toPre.P.L.U jM → (U'.gt e).pG.left (r z) ∈ D'.toPre.P.L.U jM' → ((bc.hom.left ≫ pullback.fst G.hom (specOf φ))) ((fstG I' e G').left (r z)) ∈ U.LG.L.U jL → (fstG I' e G').left (r z) ∈ U'.LG.L.U jL' → Geo.Tor.gw hD.w (r ≫ (U'.gt e).pG.left) z jM jM' * Geo.Tor.gw (U'.w e) r z jM' (fun _ => jL') = Geo.Tor.gw (U.w e) (r ≫ h) z jM (fun _ => jL) * Geo.Tor.gw wL (r ≫ (fstG I' e G').left) z jL jL') := by
  intro R R' _ _ _ _ I I' φ D D' hD A A' G _ _ G' _ _ bc U U'
  constructor
  · rintro ⟨wL, hg, he, hr, H⟩
    refine ⟨wL, hg, he, hr, fun e => ?_⟩
    obtain ⟨h, hf, hp, ht, hw⟩ := H e
    refine ⟨h, hf, ⟨hp, fun x => ?_⟩, (square_res_iff_gw hf hp hD.w wL (U.w e) (U'.w e)).1 hw⟩
    obtain ⟨hψ, hm⟩ := ht x
    exact ⟨hψ, (maps_iff hD.w _ _ _ _ _ h _ (GeneratorPullback.pullAlong_le _ _ _ _ _ hψ) (fun _ => rfl)).1 hm⟩
  · rintro ⟨wL, hg, he, hr, H⟩
    refine ⟨wL, hg, he, hr, fun e => ?_⟩
    obtain ⟨h, hf, ⟨hp, ht⟩, hw⟩ := H e
    refine ⟨h, hf, hp, fun x => ?_, (square_res_iff_gw hf hp hD.w wL (U.w e) (U'.w e)).2 hw⟩
    obtain ⟨hψ, hm⟩ := ht x
    exact ⟨hψ, (maps_iff hD.w _ _ _ _ _ h _ (GeneratorPullback.pullAlong_le _ _ _ _ _ hψ) (fun _ => rfl)).2 hm⟩
end GlobalTheory
