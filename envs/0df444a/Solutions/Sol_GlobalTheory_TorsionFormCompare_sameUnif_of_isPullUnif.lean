-- Prove2me | solution 1 for GlobalTheory.TorsionFormCompare.sameUnif_of_isPullUnif
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:34:37.91518+00:00
-- url     : https://prove2.me/submissions/9bd6d32f-47d7-4e87-a492-30737211770c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_SameUnifRefl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_GmMulEqOfResMulEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_SameUniformizationIdentityPullback
import Theorems.Thm_GlobalTheory_TorsionFormCompare_mono_fst_thick
import Theorems.Thm_GlobalTheory_TorsionFormCompare_corr_pullGen_of_pmaps
import Theorems.Thm_GlobalTheory_isPullUnif_iff_stalks
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_self
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_maps_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_specOf_id


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
open GlobalTheory GlobalTheory.TorsionFormCompare
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
namespace GlobalTheory.TorsionFormCompare
theorem _root_.solution : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegData R I) (A : PolAV (Sp (FractionRing R))) (G G' : Over (Sp R)) [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G'] (ε : G' ≅ G) (hD : IsPullDeg (RingHom.id R) D.toPre D.toPre), IsIdPull hD → ∀ (bc : G' ≅ (Over.pullback (specOf (RingHom.id R))).obj G) (U : Unif I D A G) (U' : Unif I D A G'), bc.hom.left ≫ pullback.fst G.hom (specOf (RingHom.id R)) = ε.hom.left → U'.gen.hom = (Over.pullback (jK R)).map ε.hom ≫ U.gen.hom → IsPullUnif (RingHom.id R) hD bc U U' → SameUnif ε U.toUnifPre U'.toUnifPre := by
  intro R _ _ I D A G G' _ _ _ _ ε hD hid bc U U' hF hgen H
  obtain ⟨hx, hΦ, hw₀⟩ := hid
  obtain ⟨wL, hg, he, hr, H⟩ := (isPullUnif_iff_stalks R R I I _ D D hD A A G G' bc U U').1 H
  have hr' := (maps_iff wL _ (fun _ => eSec G) _ U'.LG.rig U.LG.rig (specOf (RingHom.id R)) _
    (rigPull_le _ _ he U.LG.L) (fun _ => rfl)).1 hr
  clear hr he
  generalize bc.hom.left ≫ pullback.fst G.hom (specOf (RingHom.id R)) = F at wL hg hr' H hF
  subst hF
  refine ⟨hgen, wL, ⟨hg, ?_⟩, fun e => ?_⟩
  · have hs := specOf_id R
    rw [hs] at hr'
    exact hr'
  obtain ⟨h, hf, ⟨hp, ht⟩, hw⟩ := H e
  have hh : h = ((Over.pullback (thick R I e)).map ε.hom).left := by
    have := mono_fst_thick I e G
    rw [← cancel_mono (pullback.fst G.hom (thick R I e))]
    refine hf.trans ?_
    exact (pullback.lift_fst _ _ _).symm
  subst hh
  rw [hΦ, Category.comp_id] at hp
  have hpt : ∀ y, (hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf (RingHom.id R))) y = y := fun y => by
    rw [hΦ]; rfl
  refine ⟨?_, fun χ => ?_, ?_⟩
  · ext1
    have := mono_fst_thick I e D.toPre.P.A
    rw [← cancel_mono (pullback.fst D.toPre.P.A.hom (thick R I e))]
    exact hp
  · obtain ⟨hψ, hm⟩ := ht χ
    rw [hx χ] at hψ hm
    exact corr_pullGen_of_pmaps D.toPre.P.isLB hΦ hD.w hw₀ hψ hm
  · intro Z r z jM jL jL' h₁ h₂ h₃
    have key := hw Z r z jM jM jL jL' (by rw [hpt]; exact h₁) h₁ h₂ h₃
    rw [hw₀ _ (r ≫ (U'.gt e).pG.left) z jM jM h₁ h₁, gm_self D.toPre.P.isLB (r ≫ (U'.gt e).pG.left) z h₁,
      _root_.one_mul] at key
    exact key
end GlobalTheory.TorsionFormCompare
