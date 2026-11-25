-- Prove2me | solution 1 for GlobalTheory.UU.ToChart.w_rig
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:24:58.593791+00:00
-- url     : https://prove2.me/submissions/747bd967-6564-49df-9382-a93b9478037e

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
theorem _root_.solution (e : ℕ) (p : (PUnit → D.P.L.ι) × (PUnit → U.P.L.L.ι))
    (V : (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))).Opens)
    (h₁ : V ≤ eSec (thickObj R I e G) ⁻¹ᵁ
      ((D.P.L.pull (U.gt e).pG.left).U p.1 ⊓ (U.P.L.L.pull (fstG I e G).left).U p.2))
    (h₂ : V ≤ thick R I e ⁻¹ᵁ (U.P.L.L.pull (eSec G)).U p.2)
    (h₃ : V ≤ thick R I e ⁻¹ᵁ (D.P.L.pull (eSec D.P.A)).U p.1) :
    res h₁ (pullU (eSec (thickObj R I e G)) _ ((U.w e).s p)) *
      res h₂ (pullU (thick R I e) _ (U.P.L.rig.s p.2)) =
      res h₃ (pullU (thick R I e) _ (D.rig.s p.1)) := by
  refine unit_ext fun y hy => ?_
  obtain ⟨JG, hJG, eG⟩ := exists_good U.P.L.L U.P.L.isLB y (K := Fin 2)
    ![thick R I e ≫ eSec G, eSec (thickObj R I e G) ≫ (fstG I e G).left] (fun _ => p.2 PUnit.unit) (fun _ _ _ => rfl)
    (Fin.forall_fin_two.2 ⟨Set.mem_iInter.1 (h₂ hy) PUnit.unit, Set.mem_iInter.1 (h₁ hy).2 PUnit.unit⟩)
  obtain ⟨J, hJ, eB⟩ := exists_good D.P.L D.P.isLB y (K := Fin 2)
    ![thick R I e ≫ eSec D.P.A, eSec (thickObj R I e G) ≫ (U.gt e).pG.left] (fun _ => p.1 PUnit.unit) (fun _ _ _ => rfl)
    (Fin.forall_fin_two.2 ⟨Set.mem_iInter.1 (h₃ hy) PUnit.unit, Set.mem_iInter.1 (h₁ hy).1 PUnit.unit⟩)
  have H := (U.w_vals e (𝟙_ _) y JG J hJG hJ _ (fun _ => rfl)).1
  have o : (1 : 𝟙_ _ ⟶ thickObj R I e G).left = eSec (thickObj R I e G) :=
    (one_left _ _).trans (Category.id_comp _)
  have t : (𝟙_ (Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))))).hom ≫ thick R I e = thick R I e := Category.id_comp _
  rw [o, t] at H
  have a := val_of (L := D.P.L) (φ := fun _ : PUnit => eSec D.P.A) (ε := fun _ => 1) D.rig (thick R I e) y J p.1
    (fun _ => eB 0)
  have b := val_of (L := U.P.L.L) (φ := fun _ : PUnit => eSec G) (ε := fun _ => 1) U.P.L.rig (thick R I e) y JG p.2
    (fun _ => eG 0)
  have c := congrArg₂ (fun j k => gw (U.w e) (eSec (thickObj R I e G)) y j (fun _ => k)) (eB 1) (eG 1)
  refine (map_mul _ _ _).trans (Eq.trans ?_ (gm_res_pull _ h₃ hy _).symm)
  refine (congrArg₂ (· * ·) (gm_res_pull _ h₁ hy _) (gm_res_pull _ h₂ hy _)).trans ?_
  exact (a.symm.trans (H.trans (congrArg₂ (· * ·) c b))).symm
end GlobalTheory.UU.ToChart
