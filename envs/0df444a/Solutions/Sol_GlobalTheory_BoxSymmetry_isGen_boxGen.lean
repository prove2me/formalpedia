-- Prove2me | solution 1 for GlobalTheory.BoxSymmetry.isGen_boxGen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:08:04.809986+00:00
-- url     : https://prove2.me/submissions/96e4561d-a2b2-4e94-8b4a-557989f824ec

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_CubePullbacks_SubAddEqZeroOfEqAdd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_BoxSymIsSymmetry
import Theorems.Thm_GlobalTheory_BoxSymmetry_gm_boxGen
import Theorems.Thm_GlobalTheory_BoxSymmetry_trF_box
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
private theorem gm_pullU_eq_gm_comp' {X Y Z : Scheme.{0}} (f : Y ⟶ X) (r : Z ⟶ Y) (z : Z) (V : X.Opens)
    (hz : r z ∈ f ⁻¹ᵁ V) (a : Γ(X, V)ˣ) : gm r z (f ⁻¹ᵁ V) (pullU f V a) = gm (r ≫ f) z V a := by
  have hz' : (r ≫ f) z ∈ V := by simpa using hz
  unfold gm
  rw [dif_pos hz, dif_pos hz']
  unfold pullU
  ext
  simp
  rfl
private theorem units_ext_of_gm_id_eq_on_open {Y : Scheme.{0}} {W : Y.Opens} (s s' : Γ(Y, W)ˣ)
    (h : ∀ y : Y, y ∈ W → gm (𝟙 Y) y W s = gm (𝟙 Y) y W s') : s = s' := by
  apply Units.ext
  apply TopCat.Presheaf.section_ext Y.sheaf W
  intro y hy
  have e := congrArg Units.val (h y hy)
  unfold gm pullU at e
  rw [dif_pos (by simpa using hy)] at e
  exact e
private theorem gm_linComb_transition_eq {X' Y Z : Scheme.{0}} (M : LB X') {K : Type} [Fintype K] (φ : K → (Y ⟶ X'))
    (ε : K → ℤ) (r : Z ⟶ Y) (z : Z) (a b : K → M.ι)
    (hz : r z ∈ (M.LinComb φ ε).U a ⊓ (M.LinComb φ ε).U b) :
    gm r z ((M.LinComb φ ε).U a ⊓ (M.LinComb φ ε).U b) ((M.LinComb φ ε).g a b) = trF (L := M) φ ε r z a b := by
  unfold trF
  unfold LB.LinComb at *
  dsimp only at *
  refine (map_prod _ _ _).trans (Finset.prod_congr rfl fun k _ => ?_)
  rw [map_zpow]
  congr 1
  refine (gm_res_eq_gm r z _ hz _).trans (gm_pullU_eq_gm_comp' (φ k) r z (M.U (a k) ⊓ M.U (b k)) ?_ (M.g (a k) (b k)))
  unfold LB.wchart at hz
  exact ⟨Set.mem_iInter.1 hz.1 k, Set.mem_iInter.1 hz.2 k⟩
private theorem mem_pull_wchart_of_mem_linComb_wchart {X X' Y : Scheme.{0}} (L : LB X) {J K : Type} [Fintype J] [Fintype K]
    (F : J → (X' ⟶ X)) (φ : K → (Y ⟶ X')) (y : Y) (jj : K → J → L.ι) (i : J)
    (h : y ∈ (L.LinComb F fun _ => 1).wchart φ jj) : y ∈ (L.pull (F i)).wchart φ (fun k _ => jj k i) := by
  unfold LB.pull
  unfold LB.wchart LB.LinComb at *
  dsimp only at *
  unfold LB.wchart at *
  exact Set.mem_iInter.2 fun k => Set.mem_iInter.2 fun _ => Set.mem_iInter.1 (Set.mem_iInter.1 h k) i
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
theorem _root_.solution (F : J → (X' ⟶ X)) (φ : K → (Y ⟶ X')) (ε : K → ℤ)
    (t : ∀ i, LB.Gen (LB.LinComb (L.pull (F i)) φ ε)) (ht : ∀ i, (t i).IsGen) :
    (GeneratorPullback.boxGen L F φ ε t).IsGen := by
  intro (a : K → (L.LinComb F fun _ => 1).ι) (b : K → (L.LinComb F fun _ => 1).ι)
  apply units_ext_of_gm_id_eq_on_open
  intro y hy
  have hy' : (𝟙 Y : Y ⟶ Y) y ∈ ((L.LinComb F fun _ => 1).LinComb φ ε).U a ⊓
      ((L.LinComb F fun _ => 1).LinComb φ ε).U b := hy
  have ha : (𝟙 Y : Y ⟶ Y) y ∈ (L.LinComb F fun _ => 1).wchart φ a := hy.1
  have hb : (𝟙 Y : Y ⟶ Y) y ∈ (L.LinComb F fun _ => 1).wchart φ b := hy.2
  rw [map_mul, gm_res_eq_gm (𝟙 Y) y _ hy' _, gm_res_eq_gm (𝟙 Y) y _ hy' _, gm_linComb_transition_eq _ φ ε (𝟙 Y) y a b hy']
  erw [gm_boxGen L F φ ε t (𝟙 Y) y a ha, gm_boxGen L F φ ε t (𝟙 Y) y b hb, trF_box L F φ ε (𝟙 Y) y a b ha hb,
    ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  have hi : (𝟙 Y : Y ⟶ Y) y ∈ ((L.pull (F i)).LinComb φ ε).U (fun k _ => a k i) ⊓
      ((L.pull (F i)).LinComb φ ε).U (fun k _ => b k i) :=
    ⟨mem_pull_wchart_of_mem_linComb_wchart L F φ y a i hy.1, mem_pull_wchart_of_mem_linComb_wchart L F φ y b i hy.2⟩
  have e := congrArg (gm (𝟙 Y) y _) (ht i (fun k _ => a k i) (fun k _ => b k i))
  rw [map_mul, gm_res_eq_gm (𝟙 Y) y _ hi _, gm_res_eq_gm (𝟙 Y) y _ hi _, gm_linComb_transition_eq _ φ ε (𝟙 Y) y _ _ hi] at e
  exact e
end GlobalTheory.BoxSymmetry
