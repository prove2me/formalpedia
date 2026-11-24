-- Prove2me | solution 1 for GlobalTheory.unifPull_rig_compat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:38:56.235097+00:00
-- url     : https://prove2.me/submissions/ba1679d9-faed-45d2-9517-00ba0d250b64

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_CompatAlongOfSquare
import Theorems.Thm_GlobalTheory_UnifPullRig_compatAlong_of_square
import Theorems.Thm_GlobalTheory_UnifPullRig_rigAlong_of_square
import Theorems.Thm_GlobalTheory_UnifPullRig_eSec_hom
import Theorems.Thm_GlobalTheory_UnifPullRig_thickMap_fstG
import Theorems.Thm_GlobalTheory_UnifPullRig_eSec_fstG
import Theorems.Thm_GlobalTheory_UnifPullRig_mono_fstG
import Theorems.Thm_GlobalTheory_UnifPullRig_eSec_pG
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
noncomputable section
open GlobalTheory
open UnifPullRig ReciprocityTheory.ChartRestriction.G.Geo.Tor
namespace GlobalTheory
theorem _root_.solution : ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (I : Ideal R) (I' : Ideal R') (φ : R →+* R') (D : DegData R I) (D' : DegData R' I') (hD : IsPullDeg φ D.toPre D'.toPre) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (A' : PolAV (Spec (CommRingCat.of (FractionRing R')))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (G' : Over (Spec (CommRingCat.of R'))) [GrpObj G'] [IsCommMonObj G'] (bc : G' ≅ (Over.pullback (specOf φ)).obj G), I.map φ ≤ I' → IsMonHom bc.hom → ∀ (U : UnifPre I D A G) (L' : RigLB G') (wL : LB.Iso L'.L (U.LG.L.pull (bc.hom.left ≫ pullback.fst G.hom (specOf φ)))) (he : eSec G' ≫ bc.hom.left ≫ pullback.fst G.hom (specOf φ) = specOf φ ≫ eSec G), wL.IsGen → LB.Gen.Maps (LB.linCombIso wL (K := PUnit) (fun _ => eSec G') (fun _ => 1)) L'.rig (rigPullOf (bc.hom.left ≫ pullback.fst G.hom (specOf φ)) (specOf φ) he U.LG.L U.LG.rig) → ∀ (gt' : ∀ e : ℕ, GtCoord I' D'.toPre e G') (w' : ∀ e : ℕ, LB.Iso (L'.L.pull (fstG I' e G').left) (D'.toPre.P.L.pull (gt' e).pG.left)), (∀ e, (w' e).IsGen) → (∀ e, thickMap R' I' e G' ≫ (gt' (e + 1)).pG.left = (gt' e).pG.left) → (∀ e : ℕ, ∃ (h : (thickObj R' I' e G').left ⟶ (thickObj R I e G).left), h ≫ (fstG I e G).left = (fstG I' e G').left ≫ (bc.hom.left ≫ pullback.fst G.hom (specOf φ)) ∧ ((gt' e).pG.left ≫ (hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf φ)) = h ≫ (U.gt e).pG.left ∧ ∀ x : D'.toPre.X, (∀ κ : Fin 4, D'.toPre.Oφ (gt' e).pG x κ ≫ (hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf φ)) = h ≫ D.toPre.Oφ (U.gt e).pG (hD.xe x) κ) ∧ Geo.Tor.PMaps hD.w (D'.toPre.Oφ (gt' e).pG x) (D.toPre.Oφ (U.gt e).pG (hD.xe x)) Oinvε ((gt' e).t x) ((U.gt e).t (hD.xe x)) h) ∧ (∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R' I' e G').left) (z : Z) (jM : D.toPre.P.L.ι) (jM' : D'.toPre.P.L.ι) (jL : U.LG.L.ι) (jL' : L'.L.ι), ((hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf φ))) ((gt' e).pG.left (r z)) ∈ D.toPre.P.L.U jM → (gt' e).pG.left (r z) ∈ D'.toPre.P.L.U jM' → ((bc.hom.left ≫ pullback.fst G.hom (specOf φ))) ((fstG I' e G').left (r z)) ∈ U.LG.L.U jL → (fstG I' e G').left (r z) ∈ L'.L.U jL' → Geo.Tor.gw hD.w (r ≫ (gt' e).pG.left) z jM jM' * Geo.Tor.gw (w' e) r z jM' (fun _ => jL') = Geo.Tor.gw (U.w e) (r ≫ h) z jM (fun _ => jL) * Geo.Tor.gw wL (r ≫ (fstG I' e G').left) z jL jL')) → (∀ (e : ℕ) (p : (PUnit → D'.toPre.P.L.ι) × (PUnit → L'.L.ι)) (V : (Spec (CommRingCat.of (R' ⧸ I' ^ (e + 1)))).Opens) (h₁ : V ≤ eSec (thickObj R' I' e G') ⁻¹ᵁ ((D'.toPre.P.L.pull (gt' e).pG.left).U p.1 ⊓ (L'.L.pull (fstG I' e G').left).U p.2)) (h₂ : V ≤ thick R' I' e ⁻¹ᵁ (L'.L.pull (eSec G')).U p.2) (h₃ : V ≤ thick R' I' e ⁻¹ᵁ (D'.toPre.P.L.pull (eSec D'.toPre.P.A)).U p.1), res h₁ (pullU (eSec (thickObj R' I' e G')) _ ((w' e).s p)) * res h₂ (pullU (thick R' I' e) _ (L'.rig.s p.2)) = res h₃ (pullU (thick R' I' e) _ (D'.toPre.rig.s p.1))) ∧ (∀ (e : ℕ) (p : (PUnit → D'.toPre.P.L.ι) × (PUnit → L'.L.ι)) (V : (thickObj R' I' e G').left.Opens) (h₁ : V ≤ thickMap R' I' e G' ⁻¹ᵁ ((D'.toPre.P.L.pull (gt' (e + 1)).pG.left).U p.1 ⊓ (L'.L.pull (fstG I' (e + 1) G').left).U p.2)) (h₂ : V ≤ (D'.toPre.P.L.pull (gt' e).pG.left).U p.1 ⊓ (L'.L.pull (fstG I' e G').left).U p.2), res h₁ (pullU (thickMap R' I' e G') _ ((w' (e + 1)).s p)) = res h₂ ((w' e).s p)) := by
  intro R R' _ _ _ _ I I' φ D D' hD A A' G _ _ G' _ _ bc _ _ U L' wL he _ hrig gt' w' _ hq H
  have PL := (maps_iff wL _ (fun _ => eSec G) _ L'.rig U.LG.rig (specOf φ) _
    (rigPull_le (G' := G') (G := G) _ (specOf φ) he U.LG.L) (fun _ => rfl)).1 hrig
  have PM := (maps_iff hD.w _ (fun _ => eSec D.toPre.P.A) _ D'.toPre.rig D.toPre.rig (specOf φ) _
    (rigPull_le (G' := D'.toPre.P.A) (G := D.toPre.P.A) _ (specOf φ) hD.he D.toPre.P.L) (fun _ => rfl)).1 hD.w_rig
  choose h hF hE Q using H
  refine ⟨fun e => ?_, fun e => ?_⟩
  · have := mono_fstG I e G
    have hσ : (eSec (thickObj R' I' e G') ≫ h e ≫ (thickObj R I e G).hom) ≫ thick R I e =
        thick R' I' e ≫ specOf φ := by
      have c : (thickObj R I e G).hom ≫ thick R I e = (fstG I e G).left ≫ G.hom :=
        pullback.condition.symm
      have a := eSec_fstG I' e G'
      have b := eSec_hom G
      calc _ = eSec (thickObj R' I' e G') ≫ (h e ≫ (fstG I e G).left) ≫ G.hom := by
            simp only [Category.assoc, c]
        _ = (eSec (thickObj R' I' e G') ≫ (fstG I' e G').left) ≫
              (bc.hom.left ≫ pullback.fst G.hom (specOf φ)) ≫ G.hom := by
            rw [hF e]; simp only [Category.assoc]
        _ = thick R' I' e ≫ (eSec G' ≫ bc.hom.left ≫ pullback.fst G.hom (specOf φ)) ≫ G.hom := by
            rw [a]; simp only [Category.assoc]
        _ = thick R' I' e ≫ specOf φ := by
            rw [he, Category.assoc, b]; exact congrArg _ (Category.comp_id _)
    have hε : eSec (thickObj R' I' e G') ≫ h e =
        (eSec (thickObj R' I' e G') ≫ h e ≫ (thickObj R I e G).hom) ≫ eSec (thickObj R I e G) := by
      rw [← cancel_mono (fstG I e G).left, Category.assoc, hF e, ← Category.assoc, eSec_fstG,
        Category.assoc, he, Category.assoc _ (eSec (thickObj R I e G)), eSec_fstG]
      exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ eSec G) hσ.symm).trans
        (Category.assoc _ _ _))
    exact rigAlong_of_square U.LG.isLB D.toPre.P.isLB (Q e) (U.w_rig e) PL PM (eSec_fstG I e G)
      (eSec_pG I (U.gt e)) (eSec_fstG I' e G') (eSec_pG I' (gt' e)) (hF e) (hE e).1 hε hσ
  · have := mono_fstG I (e + 1) G
    have hm : thickMap R' I' e G' ≫ h (e + 1) = h e ≫ thickMap R I e G := by
      rw [← cancel_mono (fstG I (e + 1) G).left, Category.assoc, hF (e + 1), ← Category.assoc,
        thickMap_fstG, Category.assoc, thickMap_fstG, hF e]
    exact compatAlong_of_square U.LG.isLB D.toPre.P.isLB (Q e) (Q (e + 1)) (U.w_compat e)
      (thickMap_fstG I e G) (U.gt_q e) (thickMap_fstG I' e G') (hq e) (hF e) (hE e).1 hm
end GlobalTheory
