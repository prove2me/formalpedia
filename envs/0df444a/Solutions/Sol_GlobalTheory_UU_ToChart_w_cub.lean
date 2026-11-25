-- Prove2me | solution 1 for GlobalTheory.UU.ToChart.w_cub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:24:54.805805+00:00
-- url     : https://prove2.me/submissions/60328766-735f-41d2-a8d3-ecbd8a938e5e

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_WCompat
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_SameB
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_GmResPull
import Theorems.Thm_GlobalTheory_UU_ToChart_gm_res_pull
import Theorems.Thm_P2M_GlobalTheory_UU_ToChart_cub_alg__dec35e250081
import Theorems.Thm_GlobalTheory_UU_ToChart_cube_left
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_good
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_prod_cub
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_unit_ext
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_of


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
noncomputable section
open GlobalTheory GlobalTheory.UU GlobalTheory.UU.ToChart
variable {R : Type} [CommRing R] [IsDomain R] (I : Ideal R) (e : ℕ)
variable {I e} {D : DegPre R} {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]
variable {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} (U : PreU I D A G)
namespace GlobalTheory.UU.ToChart
theorem _root_.solution (e : ℕ) (T : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))))
    (x : Fin 3 → (T ⟶ thickObj R I e G)) (jL : thK → U.P.L.L.ι) (jM : thK → D.P.L.ι)
    (cL : LB.Coh U.P.L.L (fun k => (lift ((Over.map (thick R I e)).map (x 0) ≫ fstG I e G)
      (lift ((Over.map (thick R I e)).map (x 1) ≫ fstG I e G)
        ((Over.map (thick R I e)).map (x 2) ≫ fstG I e G))).left ≫ thφ G (x3 G) k) jL)
    (cM : LB.Coh D.P.L (fun k => (lift ((Over.map (thick R I e)).map (x 0) ≫ (U.gt e).pG)
      (lift ((Over.map (thick R I e)).map (x 1) ≫ (U.gt e).pG)
        ((Over.map (thick R I e)).map (x 2) ≫ (U.gt e).pG))).left ≫
          thφ D.P.A (x3 D.P.A) k) jM)
    (V : T.left.Opens)
      (hB : V ≤ (lift ((Over.map (thick R I e)).map (x 0) ≫ (U.gt e).pG)
        (lift ((Over.map (thick R I e)).map (x 1) ≫ (U.gt e).pG)
          ((Over.map (thick R I e)).map (x 2) ≫ (U.gt e).pG))).left ⁻¹ᵁ
            (Theta D.P.A D.P.L).U jM)
      (hG : V ≤ (lift ((Over.map (thick R I e)).map (x 0) ≫ fstG I e G)
        (lift ((Over.map (thick R I e)).map (x 1) ≫ fstG I e G)
          ((Over.map (thick R I e)).map (x 2) ≫ fstG I e G))).left ⁻¹ᵁ (Theta G U.P.L.L).U jL)
      (hw : ∀ k : thK, V ≤ (psum (thickObj R I e G) x k.down).left ⁻¹ᵁ
        ((D.P.L.pull (U.gt e).pG.left).U (fun _ => jM k) ⊓
          (U.P.L.L.pull (fstG I e G).left).U (fun _ => jL k))) :
      res hB (pullU _ _ (D.cub.t.s jM)) =
        (∏ k : thK, res (hw k) (pullU (psum (thickObj R I e G) x k.down).left _
          ((U.w e).s (fun _ => jM k, fun _ => jL k))) ^ thε k) *
        res hG (pullU _ _ (U.P.c.t.s jL)) := by
  refine unit_ext fun y hy => ?_
  obtain ⟨JG, hJG, eG⟩ := exists_good U.P.L.L U.P.L.isLB y _ jL cL (fun k => Set.mem_iInter.1 (hG hy) k)
  obtain ⟨J, hJ, eB⟩ := exists_good D.P.L D.P.isLB y _ jM cM (fun k => Set.mem_iInter.1 (hB hy) k)
  obtain ⟨h, hh⟩ : ∃ h : (T.left ⟶ (thickObj R I e G).left) → (T.left.presheaf.stalk y)ˣ, ∀ q,
      h q = gw (U.w e) q y (J (q ≫ (U.gt e).pG.left)) (fun _ => JG (q ≫ (fstG I e G).left)) := ⟨_, fun _ => rfl⟩
  have H := (U.w_vals e T y JG J hJG hJ (fun a => h a.left) (fun _ => hh _)).2.2 (x 0) (x 1) (x 2)
  have P := prod_cub (x 0) (x 1) (x 2) h
  have Q : ∀ k : thK, gm (𝟙 T.left) y V (res (hw k) (pullU (psum (thickObj R I e G) x k.down).left _
      ((U.w e).s (fun _ => jM k, fun _ => jL k)))) =
      h ((lift (x 0) (lift (x 1) (x 2))).left ≫ thφ (thickObj R I e G) (x3 _) k) := fun k => by
    have g : JG ((psum (thickObj R I e G) x k.down).left ≫ (fstG I e G).left) = jL k :=
      (congrArg JG (cube_left (fstHom I e G T) x k).symm).trans (eG k)
    have b : J ((psum (thickObj R I e G) x k.down).left ≫ (U.gt e).pG.left) = jM k :=
      (congrArg J (cube_left (projHom (U.gt e) T) x k).symm).trans (eB k)
    refine (gm_res_pull _ (hw k) hy _).trans (Eq.trans ?_ (congrArg h (cube_left (MonoidHom.id _) x k)).symm)
    exact ((hh _).trans (congrArg₂ (fun j l => gw (U.w e) (psum (thickObj R I e G) x k.down).left y j (fun _ => l))
      b g)).symm
  have a := val_of (L := D.P.L) (φ := thφ D.P.A (x3 D.P.A)) (ε := thε) D.cub.t _ y J jM eB
  have b := val_of (L := U.P.L.L) (φ := thφ G (x3 G)) (ε := thε) U.P.c.t _ y JG jL eG
  refine (gm_res_pull _ hB hy _).trans (Eq.trans ?_ ((map_mul _ _ _).trans (congrArg₂ (· * ·)
    (((map_prod _ _ _).trans (Finset.prod_congr rfl fun k _ => (map_zpow _ _ _).trans
      (congrArg (· ^ thε k) (Q k)))).trans P) (gm_res_pull _ hG hy _))).symm)
  exact a.symm.trans ((cub_alg' H).trans (congrArg₂ (· * ·) rfl b))
end GlobalTheory.UU.ToChart
