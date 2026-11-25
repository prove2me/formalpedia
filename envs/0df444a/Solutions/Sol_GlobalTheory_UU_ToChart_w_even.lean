-- Prove2me | solution 1 for GlobalTheory.UU.ToChart.w_even
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:32:04.521838+00:00
-- url     : https://prove2.me/submissions/5228d7ec-3ee1-4cce-9454-b4749ef85715

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
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_good
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_res
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
theorem _root_.solution (e : ℕ) (jS : Fin 2 → U.P.L.L.ι) (jT : Fin 2 → D.P.L.ι)
    (cS : LB.Coh U.P.L.L (fun k => (fstG I e G).left ≫ (![(ι[G]).left, 𝟙 G.left] : Fin 2 → _) k) jS)
    (cT : LB.Coh D.P.L
      (fun k => (U.gt e).pG.left ≫ (![(ι[D.P.A]).left, 𝟙 D.P.A.left] : Fin 2 → _) k) jT)
    (V : (thickObj R I e G).left.Opens)
      (h₁ : V ≤ (U.gt e).pG.left ⁻¹ᵁ (LB.LinComb D.P.L (K := Fin 2)
        ![(ι[D.P.A]).left, 𝟙 D.P.A.left] ![1, -1]).U jT)
      (h₂ : V ≤ (D.P.L.pull (U.gt e).pG.left).U (fun _ => jT 1) ⊓
        (U.P.L.L.pull (fstG I e G).left).U (fun _ => jS 1))
      (h₃ : V ≤ (ι[thickObj R I e G]).left ⁻¹ᵁ ((D.P.L.pull (U.gt e).pG.left).U (fun _ => jT 0) ⊓
        (U.P.L.L.pull (fstG I e G).left).U (fun _ => jS 0)))
      (h₄ : V ≤ (fstG I e G).left ⁻¹ᵁ (LB.LinComb U.P.L.L (K := Fin 2)
        ![(ι[G]).left, 𝟙 G.left] ![1, -1]).U jS) :
      res h₁ (pullU (U.gt e).pG.left _ (D.sym.s jT)) *
        res h₂ ((U.w e).s (fun _ => jT 1, fun _ => jS 1)) =
      res h₃ (pullU (ι[thickObj R I e G]).left _ ((U.w e).s (fun _ => jT 0, fun _ => jS 0))) *
        res h₄ (pullU (fstG I e G).left _ (U.P.sym.s jS)) := by
  refine unit_ext fun y hy => ?_
  obtain ⟨JG, hJG, eG⟩ := exists_good U.P.L.L U.P.L.isLB y _ jS cS (fun k => Set.mem_iInter.1 (h₄ hy) k)
  obtain ⟨J, hJ, eB⟩ := exists_good D.P.L D.P.isLB y _ jT cT (fun k => Set.mem_iInter.1 (h₁ hy) k)
  have H := (U.w_vals e _ y JG J hJG hJ _ (fun _ => rfl)).2.1 (𝟙 _)
  have o : ((𝟙 (thickObj R I e G))⁻¹).left = (ι[thickObj R I e G]).left := by rw [Hom.inv_def, Category.id_comp]
  have iG : ((𝟙 (thickObj R I e G))⁻¹).left ≫ (fstG I e G).left = (fstG I e G).left ≫ (ι[G]).left :=
    (congrArg (fun q => q.left) (map_inv (fstHom I e G _) (𝟙 _))).trans
      (congrArg (· ≫ (ι[G]).left) (Category.id_comp (fstG I e G).left))
  have iB : ((𝟙 (thickObj R I e G))⁻¹).left ≫ (U.gt e).pG.left = (U.gt e).pG.left ≫ (ι[D.P.A]).left :=
    (congrArg (fun q => q.left) (map_inv (projHom (U.gt e) _) (𝟙 _))).trans
      (congrArg (· ≫ (ι[D.P.A]).left) (Category.id_comp (U.gt e).pG.left))
  have g₀ : JG ((fstG I e G).left ≫ (ι[G]).left) = jS 0 := eG 0
  have g₁ : JG (fstG I e G).left = jS 1 := (congrArg JG (Category.comp_id _).symm).trans (eG 1)
  have b₀ : J ((U.gt e).pG.left ≫ (ι[D.P.A]).left) = jT 0 := eB 0
  have b₁ : J (U.gt e).pG.left = jT 1 := (congrArg J (Category.comp_id _).symm).trans (eB 1)
  rw [iG, iB, o, g₀, b₀, Over.id_left, Category.id_comp, Category.id_comp, g₁, b₁, val_of _ _ _ _ jT eB,
    val_of _ _ _ _ jS eG] at H
  refine (map_mul _ _ _).trans (Eq.trans ?_ (map_mul _ _ _).symm)
  exact (congrArg₂ (· * ·) (gm_res_pull _ h₁ hy _) (gm_res _ y h₂ hy _)).trans
    (H.trans (congrArg₂ (· * ·) (gm_res_pull _ h₃ hy _) (gm_res_pull _ h₄ hy _)).symm)
end GlobalTheory.UU.ToChart
