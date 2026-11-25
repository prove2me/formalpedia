-- Prove2me | solution 1 for GlobalTheory.BoxSymmetry.trF_box
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T15:48:12.360501+00:00
-- url     : https://prove2.me/submissions/d94caabe-b11f-4640-b714-55ba88fb0dd6

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_CubePullbacks_SubAddEqZeroOfEqAdd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_BoxSymIsSymmetry
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.BoxSymmetry
section Generators
variable {X X' Y Z : Scheme.{0}} (L : LB X) {J K : Type} [Fintype J] [Fintype K]
private theorem gm_res_eq_gm {X Z : Scheme.{0}} (r : Z ⟶ X) (z : Z) {U V : X.Opens} (hUV : U ≤ V)
    (hz : r z ∈ U) (x : Γ(X, V)ˣ) : gm r z U (res hUV x) = gm r z V x := by
  have key : X.presheaf.map (homOfLE hUV).op ≫ r.app U ≫ Z.presheaf.germ (r ⁻¹ᵁ U) z hz =
      r.app V ≫ Z.presheaf.germ (r ⁻¹ᵁ V) z (hUV hz) := by
    rw [Scheme.Hom.naturality_assoc]
    congr 1
    exact TopCat.Presheaf.germ_res _ _ _ _
  unfold gm res
  rw [dif_pos hz, dif_pos (hUV hz)]
  unfold pullU
  ext
  simp only [MonoidHom.comp_apply, Units.coe_map, MonoidHom.coe_coe]
  have e := congrArg (fun f => CommRingCat.Hom.hom f (x : Γ(X, V))) key
  simpa using e
private theorem gm_lin_lemma_2 {X X' Z : Scheme.{0}} (L : LB X) {J : Type} [Fintype J]
    (F : J → (X' ⟶ X)) (y : Z ⟶ X') (z : Z) (j j' : J → L.ι) (e : ℤ)
    (hy : y z ∈ (L.LinComb F fun _ => 1).U j ⊓ (L.LinComb F fun _ => 1).U j') :
    gm y z ((L.LinComb F fun _ => 1).U j ⊓ (L.LinComb F fun _ => 1).U j')
        ((L.LinComb F fun _ => 1).g j j') ^ e =
      ∏ i, gm y z ((L.pull (F i)).U (fun _ => j i) ⊓ (L.pull (F i)).U (fun _ => j' i))
        ((L.pull (F i)).g (fun _ => j i) (fun _ => j' i)) ^ e := by
  rw [Finset.prod_zpow]
  congr 1
  unfold LB.pull LB.LinComb at *
  dsimp only at *
  refine (map_prod _ _ _).trans (Finset.prod_congr rfl fun i _ => ?_)
  rw [zpow_one, Fintype.prod_unique, zpow_one]
  refine (gm_res_eq_gm y z _ hy _).trans (gm_res_eq_gm y z _ ?_ _).symm
  unfold LB.wchart at hy ⊢
  exact ⟨Set.mem_iInter.2 fun _ => Set.mem_iInter.1 hy.1 i, Set.mem_iInter.2 fun _ => Set.mem_iInter.1 hy.2 i⟩
end Generators
variable {S : Scheme.{0}}
end GlobalTheory.BoxSymmetry
end
end

set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.BoxSymmetry
variable {X X' Y Z : Scheme.{0}} (L : LB X) {J K : Type} [Fintype J] [Fintype K]
namespace GlobalTheory.BoxSymmetry
theorem _root_.solution (F : J → (X' ⟶ X)) (φ : K → (Y ⟶ X')) (ε : K → ℤ) (r : Z ⟶ Y) (z : Z)
    (jj jj' : K → (LB.LinComb L F (fun _ => 1)).ι)
    (h : r z ∈ LB.wchart (LB.LinComb L F (fun _ => 1)) φ jj)
    (h' : r z ∈ LB.wchart (LB.LinComb L F (fun _ => 1)) φ jj') :
    trF (L := LB.LinComb L F (fun _ => 1)) φ ε r z jj jj' =
      ∏ i, trF (L := L.pull (F i)) φ ε r z (fun k _ => jj k i) (fun k _ => jj' k i) := by
  unfold trF
  rw [Finset.prod_comm]
  refine Finset.prod_congr rfl fun k _ => ?_
  have hk : (r ≫ φ k) z ∈ (L.LinComb F fun _ => 1).U (jj k) ⊓ (L.LinComb F fun _ => 1).U (jj' k) := by
    unfold LB.wchart at h h'
    exact ⟨Set.mem_iInter.1 h k, Set.mem_iInter.1 h' k⟩
  exact gm_lin_lemma_2 L F (r ≫ φ k) z (jj k) (jj' k) (ε k) hk
end GlobalTheory.BoxSymmetry
