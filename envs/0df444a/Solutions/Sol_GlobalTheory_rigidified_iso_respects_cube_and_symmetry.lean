-- Prove2me | solution 1 for GlobalTheory.rigidified_iso_respects_cube_and_symmetry
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:06:18.525478+00:00
-- url     : https://prove2.me/submissions/3b589692-6653-4c4e-b108-4700c64a78b3

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_RigidifiedIsoRespectsCubeAndSymmetry
import Theorems.Thm_GlobalTheory_RigidIsoCube_surjective_appTop_of_baseChange
import Theorems.Thm_GlobalTheory_RigidIsoCube_surjective_snd_of_generic
import Theorems.Thm_GlobalTheory_RigidIsoCube_pmaps_of_section
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_isCub_cubV
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_isGen_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_prod_cub
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_surj_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_corr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_pull


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
open RigidIsoCube
namespace GlobalTheory
theorem _root_.solution : GlobalFnsSt → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (I : Ideal R), AdmBase R I → ∀ (D D' : DegData R I) (A A' : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : UnifPre I D A G) (U' : UnifPre I D' A' G) (wL : LB.Iso U'.LG.L (U.LG.L.pull (𝟙 G.left))) (he : eSec G ≫ 𝟙 G.left = 𝟙 _ ≫ eSec G), wL.IsGen → LB.Gen.Maps (LB.linCombIso wL (K := PUnit) (fun _ => eSec G) (fun _ => 1)) U'.LG.rig (rigPullOf (𝟙 G.left) (𝟙 _) he U.LG.L U.LG.rig) → (Geo.Tor.PMaps wL (thφ G (x3 G)) (thφ G (x3 G)) thε U'.cubG.t U.cubG.t (𝟙 _) ∧ Geo.Tor.PMaps wL (K := Fin 2) ![(ι[G]).left, 𝟙 G.left] ![(ι[G]).left, 𝟙 G.left] ![1, -1] U'.symG U.symG (𝟙 G.left)) := by
  intro hG R _ _ _ I _ D D' A A' G _ _ _ U U' wL _ hw _
  have := U.smooth
  have : IsDominant (jK R) := ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).2
    (((RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective R (FractionRing R))).le.trans bot_le)⟩
  have := IsSchemeTheoreticallyDominant.of_isDominant (jK R)
  have hg : IsPullback (U.gen.inv.left ≫ pullback.fst G.hom (jK R)) A.A.hom G.hom (jK R) := by
    have : IsIso U.gen.inv.left := inferInstanceAs (IsIso ((Over.forget _).map U.gen.inv))
    have s : IsPullback U.gen.inv.left A.A.hom (pullback.snd G.hom (jK R)) (𝟙 _) :=
      IsPullback.of_horiz_isIso ⟨(Over.w U.gen.inv).trans (Category.comp_id _).symm⟩
    simpa using s.paste_horiz (IsPullback.of_hasPullback G.hom (jK R))
  have s₁ : Function.Surjective G.hom.appTop.hom :=
    surjective_appTop_of_baseChange hg (eSec G) (Over.w η[G]) (hG _ _ A.isAb).2
  have : Flat (G ⊗ G).hom := by rw [Over.tensorObj_hom]; infer_instance
  have sj : Function.Surjective ((snd G (G ⊗ G)).left ≫ (snd G G).left ≫ G.hom).appTop.hom :=
    surj_comp (surjective_snd_of_generic hG (jK R) G A.isAb hg _)
      (surj_comp (surjective_snd_of_generic hG (jK R) G A.isAb hg _) s₁)
  have pg := (isGen_iff wL).1 hw
  constructor
  · let e : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ G3 G := lift 1 (lift 1 1)
    have he : e.left ≫ (snd G (G ⊗ G)).left ≫ (snd G G).left ≫ G.hom = 𝟙 _ := by
      rw [Over.w, Over.w]; exact Over.w e
    refine pmaps_of_section pg U.LG.isLB U'.LG.isLB (φ' := thφ G (x3 G)) (φ := thφ G (x3 G)) (ε := thε)
      U'.cubG.t U'.cubG.isGen U.cubG.t U.cubG.isGen (fun _ => Category.comp_id _) _ e.left he sj fun y J J' hJ hJ' => ?_
    have p := prod_cub (1 : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ G) 1 1
      (fun q => gw wL q y (J (q ≫ 𝟙 _)) (J' q))
    rw [_root_.mul_one, _root_.mul_one] at p
    refine ((isCub_cubV U.cubG hJ).face 1 1).trans
      (Eq.trans ?_ (congrArg₂ (· * ·) p ((isCub_cubV U'.cubG hJ').face 1 1)).symm)
    simp
  · have oi : eSec G ≫ (ι[G]).left = eSec G := by
      have : η[G] ≫ ι[G] = η[G] := by simp
      exact congrArg (fun q => q.left) this
    refine pmaps_of_section pg U.LG.isLB U'.LG.isLB U'.symG U'.symG_gen U.symG U.symG_gen
      (fun _ => Category.comp_id _) G.hom (eSec G) (Over.w η[G]) s₁ fun y J J' hJ hJ' => ?_
    have a := val_corr hJ U.symG_rig (𝟙 _)
    rw [val_pull hJ, val_one, Category.id_comp] at a
    have b := val_corr hJ' U'.symG_rig (𝟙 _)
    rw [val_pull hJ', val_one, Category.id_comp] at b
    rw [a, b, Fin.prod_univ_two]
    show 1 = gw wL (eSec G ≫ (ι[G]).left) y (J ((eSec G ≫ (ι[G]).left) ≫ 𝟙 _)) (J' (eSec G ≫ (ι[G]).left)) ^ (1 : ℤ) *
      gw wL (eSec G ≫ 𝟙 _) y (J ((eSec G ≫ 𝟙 _) ≫ 𝟙 _)) (J' (eSec G ≫ 𝟙 _)) ^ (-1 : ℤ) * 1
    simp only [oi, Category.comp_id]
    simp
end GlobalTheory
