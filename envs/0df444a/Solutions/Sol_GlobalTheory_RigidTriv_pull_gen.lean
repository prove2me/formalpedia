-- Prove2me | solution 1 for GlobalTheory.RigidTriv.pull_gen
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:26:45.049217+00:00
-- url     : https://prove2.me/submissions/7ac89576-f732-443a-a97f-691b56881d46

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigidSys
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Splits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GtBaseChangeSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsGenOfRigid
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
noncomputable section
namespace GlobalTheory.RigidTriv
variable {X Y Z : Scheme.{0}}
private lemma gm_id_val_eq_germ (W : Z.Opens) (z : Z) (hz : z ∈ W) (u : Γ(Z, W)ˣ) :
    Units.val (gm (𝟙 Z) z W u) = (Z.presheaf.germ W z hz).hom u.1 := by
  simp [gm, hz, pullU]
  rfl
private lemma gm_val_eq_germ_app (f : Z ⟶ Y) (z : Z) (U : Y.Opens) (h : f z ∈ U) (a : Γ(Y, U)ˣ) :
    Units.val (gm f z U a) = (Z.presheaf.germ (f ⁻¹ᵁ U) z h).hom (f.app U a.1) := by
  simp [gm, h, pullU]
end GlobalTheory.RigidTriv
end
end

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
noncomputable section
open GlobalTheory GlobalTheory.RigidTriv
variable {X Y Z : Scheme.{0}}
namespace GlobalTheory.RigidTriv
theorem _root_.solution {N : LB Y} {F : Z ⟶ Y} {t : (N.pull F).Gen} (ht : t.IsGen) (z : Z) (i j : N.ι)
    (hi : F z ∈ N.U i) (hj : F z ∈ N.U j) :
    gm (𝟙 Z) z ((N.pull F).U (fun _ => i)) (t.s fun _ => i) =
      gm F z (N.U i ⊓ N.U j) (N.g i j) * gm (𝟙 Z) z ((N.pull F).U (fun _ => j)) (t.s fun _ => j) := by
  have hz : z ∈ (N.pull F).U (fun _ => i) ⊓ (N.pull F).U (fun _ => j) :=
    ⟨Set.mem_iInter.2 fun _ => hi, Set.mem_iInter.2 fun _ => hj⟩
  have hij : F z ∈ N.U i ⊓ N.U j := ⟨hi, hj⟩
  have H := congrArg (fun u => (Z.presheaf.germ _ z hz).hom (Units.val u)) (ht (fun _ => i) (fun _ => j))
  ext1
  rw [Units.val_mul, gm_id_val_eq_germ _ z hz.1, gm_id_val_eq_germ _ z hz.2, gm_val_eq_germ_app F z _ hij]
  simp only [res, Units.coe_map, Units.val_mul, map_mul, MonoidHom.coe_coe, TopCat.Presheaf.germ_res_apply] at H
  have hg : (Z.presheaf.germ _ z hz).hom ((N.pull F).g (fun _ => i) (fun _ => j)).1 =
      (Z.presheaf.germ (F ⁻¹ᵁ (N.U i ⊓ N.U j)) z hij).hom (F.app _ (N.g i j).1) := by
    simp only [LB.pull, LB.LinComb, Fintype.prod_unique, zpow_one]
    exact TopCat.Presheaf.germ_res_apply ..
  rw [hg] at H
  exact H
end GlobalTheory.RigidTriv
