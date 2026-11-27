-- Prove2me | solution 1 for GlobalTheory.TorsionFormCompare.exists_isIdPull
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:34:29.467236+00:00
-- url     : https://prove2.me/submissions/5f241109-8828-4df6-b99e-4f04c6a29a3b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_SameUnifRefl
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_CMModuli_FlatIsoUnitGenerator
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_CMModuli_FlatTorsionIsomorphism
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsIdentityPullbackDegeneration
import Theorems.Thm_GlobalTheory_TorsionFormCompare_exists_mapsAt_id
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_congr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_corr_of_val
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_grpPullback_iso
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gw_isoPullId
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_idIso_isGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_idIso_maps
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_isGen_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_isGrpPullback_of_iso
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_isGrpPullback_pullback
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_isoPullId_maps
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_isoPullId_pgen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_specOf_id
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_corr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_pull


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.TorsionFormCompare
open scoped CategoryTheory.Obj
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.TorsionFormCompare
namespace GlobalTheory.TorsionFormCompare
theorem _root_.solution : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (W : (Sp R).Opens), genericPoint (Sp R) ∈ W → Nonempty (PsiOn D W) → ∃ hD : IsPullDeg (RingHom.id R) D D, IsIdPull hD := by
  rintro R _ _ D W hW ⟨ψ⟩
  have hs := specOf_id R
  have mR : IsMonHom (Iso.refl D.P.A).hom := by show IsMonHom (𝟙 _); infer_instance
  have gp : IsGrpPullback D.P.A D.P.A (specOf (RingHom.id R)) (Iso.refl D.P.A).hom.left :=
    (isGrpPullback_of_iso (Iso.refl D.P.A)).congr hs.symm rfl
  obtain ⟨e, me, he⟩ := grpPullback_iso gp (isGrpPullback_pullback D.P.A (specOf (RingHom.id R)))
  have hF : e.hom.left ≫ pullback.fst D.P.A.hom (specOf (RingHom.id R)) = 𝟙 _ := he
  have hz : eSec D.P.A ≫ e.hom.left ≫ pullback.fst D.P.A.hom (specOf (RingHom.id R)) =
      specOf (RingHom.id R) ≫ eSec D.P.A := by
    rw [hF, hs, Category.comp_id]; exact (Category.id_comp _).symm
  have hgen : ∀ z : Sp (FractionRing R), jK R z ∈ W := by
    intro z
    have : jK R z = genericPoint (Sp R) := by
      rw [genericPoint_eq_bot_of_affine]
      apply PrimeSpectrum.ext
      show Ideal.comap (algebraMap R (FractionRing R)) z.asIdeal = ⊥
      have hz0 : z.asIdeal = ⊥ := @Ideal.eq_bot_of_prime _ _ _ z.isPrime
      rw [hz0]
      exact Ideal.comap_bot_of_injective _ (IsFractionRing.injective R _)
    rw [this]; exact hW
  have hr : Set.range (𝟙 (Sp (FractionRing R)) : _ ⟶ _) ⊆ Set.range (jK R ⁻¹ᵁ W).ι := by
    rintro _ ⟨z, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact hgen z
  let l := IsOpenImmersion.lift (jK R ⁻¹ᵁ W).ι (𝟙 _) hr
  have hl : l ≫ (jK R ⁻¹ᵁ W).ι = 𝟙 _ := IsOpenImmersion.lift_fac _ _ _
  refine ⟨{ e := e, e_hom := me, w := isoPullId (idIso D.P.L) hF
            w_gen := (isGen_iff _).2 (isoPullId_pgen (idIso_isGen D.P.isLB) hF)
            he := hz
            w_rig := isoPullId_maps (idIso_maps (⟨D.P.L, D.rig, D.P.isLB, D.rig_gen⟩ : RigLB D.P.A)) hF hs hz
            xe := AddEquiv.refl _
            c_pr := fun x => by rw [hF, hs, Category.comp_id]; exact (Category.id_comp _).symm
            W := W, psiW := ψ, g := l ≫ jK R ∣_ W
            g_comm := by
              rw [hs, Category.comp_id]
              exact (Category.assoc _ _ _).trans ((congrArg (l ≫ ·) (morphismRestrict_ι (jK R) W)).trans
                ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ jK R) hl).trans (Category.id_comp _))))
            psi_pr := fun x => ?_ }, fun _ => rfl, hF, fun Y f y j k hj hk => ?_⟩
  · obtain ⟨b, hb, hv⟩ := exists_mapsAt_id hF (D.xK x) (-1) (D.psi x) (D.psi_gen x)
    refine ⟨b, hb, corr_of_val D.P.isLB fun y J hJ => ?_⟩
    have c := val_corr hJ (ψ.psi_eq x) l
    have c₁ := val_pull hJ (ψ.psi x) (jK R ∣_ W) l
    have c₂ := val_pull hJ (D.psi x) (jK R ⁻¹ᵁ W).ι l
    have c₃ := val_pull hJ (ψ.psi x) (l ≫ jK R ∣_ W) (𝟙 _)
    refine (hv _ _ y J).trans (Eq.trans ?_ c₃.symm)
    refine (congrArg (fun r => val (D.psi x) r y J) hl).symm.trans (c₂.symm.trans (c.symm.trans (c₁.trans ?_)))
    exact congrArg (fun r => val (ψ.psi x) r y J) (Category.id_comp _).symm
  · exact gw_isoPullId (idIso D.P.L) hF f y j k hj hk
end GlobalTheory.TorsionFormCompare
