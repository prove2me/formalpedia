-- Prove2me | solution 1 for GlobalTheory.boxSym_isSymmetry
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:37:04.563894+00:00
-- url     : https://prove2.me/submissions/f152c552-2e1b-44da-bb76-0c0a11c82dd8

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_CubePullbacks_SubAddEqZeroOfEqAdd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_BoxSymIsSymmetry
import Theorems.Thm_GlobalTheory_BoxSymmetry_gm_boxGen
import Theorems.Thm_GlobalTheory_BoxSymmetry_isGen_boxGen
import Theorems.Thm_GlobalTheory_BoxSymmetry_eSec_comp_sym
import Theorems.Thm_GlobalTheory_BoxSymmetry_eSec_comp_hom
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_corr_of_val
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_good
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_corr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_of
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_pull
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_LBxP_isGen_pullAlong
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_LB_isLB_linComb

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
private theorem mem_pull_wchart_of_mem_linComb_wchart {X X' Y : Scheme.{0}} (L : LB X) {J K : Type} [Fintype J] [Fintype K]
    (F : J → (X' ⟶ X)) (φ : K → (Y ⟶ X')) (y : Y) (jj : K → J → L.ι) (i : J)
    (h : y ∈ (L.LinComb F fun _ => 1).wchart φ jj) : y ∈ (L.pull (F i)).wchart φ (fun k _ => jj k i) := by
  unfold LB.pull
  unfold LB.wchart LB.LinComb at *
  dsimp only at *
  unfold LB.wchart at *
  exact Set.mem_iInter.2 fun k => Set.mem_iInter.2 fun _ => Set.mem_iInter.1 (Set.mem_iInter.1 h k) i
private theorem gm_pullAlong_section_eq_gm_comp {X X' Y Y' Z : Scheme.{0}} (L : LB X) {K : Type} [Fintype K]
    (F : X' ⟶ X) (h : Y' ⟶ Y) (φ : K → (Y ⟶ X)) (ε : K → ℤ) (ψ : K → (Y' ⟶ X'))
    (hψ : ∀ k, ψ k ≫ F = h ≫ φ k) (t : (L.LinComb φ ε).Gen) (r : Z ⟶ Y') (z : Z)
    (a : K → (L.pull F).ι) (hz : r z ∈ (L.pull F).wchart ψ a) :
    gm r z ((L.pull F).wchart ψ a) ((GeneratorPullback.pullAlong L F h φ ε ψ hψ t).s a) =
      gm (r ≫ h) z (L.wchart φ fun k => a k PUnit.unit) (t.s fun k => a k PUnit.unit) := by
  unfold GeneratorPullback.pullAlong
  dsimp only
  refine (gm_res_eq_gm r z _ hz _).trans (gm_pullU_eq_gm_comp' h r z _ ?_ _)
  unfold LB.wchart at hz ⊢
  refine Set.mem_iInter.2 fun k => ?_
  have h1 := Set.mem_iInter.1 hz k
  unfold LB.pull LB.LinComb at h1
  dsimp only at h1
  unfold LB.wchart at h1
  have h2 := Set.mem_iInter.1 h1 PUnit.unit
  have e := congrArg (fun m : Y' ⟶ X => m.base (r z)) (hψ k)
  simp at e h2
  simp [← e, h2]
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
open GlobalTheory.BoxSymmetry
namespace GlobalTheory
theorem _root_.solution : ∀ S : Scheme.{0}, BoxSymSt (S := S) := by
  intro S
  unfold BoxSymSt
  intro G' G _ _ _ _ j p L sy hL hsy hc
  have c' : ∀ k, eSec G' ≫ ![(ι[G']).left, 𝟙 G'.left] k = eSec G' := fun k => eSec_comp_sym G' k
  have c : ∀ k, eSec G ≫ ![(ι[G]).left, 𝟙 G.left] k = eSec G := fun k => eSec_comp_sym G k
  have key : ∀ (y : (𝟙_ (Over S)).left) (a : Fin 2 → L.ι), (∀ k, a k = a 0) → eSec G y ∈ L.U (a 0) →
      gm (eSec G) y (L.wchart ![(ι[G]).left, 𝟙 G.left] a) (sy.s a) = 1 := by
    intro y a ha hy
    obtain ⟨J, hJ, hJa⟩ := exists_good L hL y (fun k => (𝟙 _ ≫ eSec G) ≫ ![(ι[G]).left, 𝟙 G.left] k) a
      (fun k k' _ => (ha k).trans (ha k').symm) (fun k => by
        show ((𝟙 _ ≫ eSec G) ≫ ![(ι[G]).left, 𝟙 G.left] k) y ∈ L.U (a k)
        rw [Category.id_comp, c k, ha k]
        exact hy)
    have e := val_corr hJ hc (𝟙 _)
    rw [val_pull hJ, val_one, val_of sy _ y J a hJa, Category.id_comp] at e
    exact e
  have hm : ∀ i, IsMonHom (p.pr i) := by
    intro i
    exact p.hom i
  refine ⟨?_, ?_⟩
  · unfold boxSym boxLB
    exact isGen_boxGen L _ _ _ _ fun i => LBxP.isGen_pullAlong L _ _ _ _ _ _ _ hsy
  · refine corr_of_val (LB.isLB_linComb hL _ _) fun y JB hJB => ?_
    rw [val_pull hJB, val_one,
      val_of _ _ y JB (fun k => JB ((𝟙 _ ≫ eSec G') ≫ ![(ι[G']).left, 𝟙 G'.left] k)) (fun _ => rfl)]
    have hmem := hJB.mem ![(ι[G']).left, 𝟙 G'.left] (𝟙 _ ≫ eSec G')
    erw [gm_boxGen L _ _ _ _ (𝟙 _ ≫ eSec G') y _ hmem]
    refine Finset.prod_eq_one fun i _ => ?_
    erw [gm_pullAlong_section_eq_gm_comp L _ _ _ _ _ _ sy (𝟙 _ ≫ eSec G') y _ (mem_pull_wchart_of_mem_linComb_wchart L _ _ _ _ i hmem)]
    rw [show (𝟙 _ ≫ eSec G') ≫ (p.pr i).left = eSec G by rw [Category.id_comp, eSec_comp_hom]]
    apply key
    · intro k
      show JB ((𝟙 _ ≫ eSec G') ≫ ![(ι[G']).left, 𝟙 G'.left] k) i =
        JB ((𝟙 _ ≫ eSec G') ≫ ![(ι[G']).left, 𝟙 G'.left] 0) i
      rw [Category.id_comp, c' k, c' 0]
    · show eSec G y ∈ L.U (JB ((𝟙 _ ≫ eSec G') ≫ ![(ι[G']).left, 𝟙 G'.left] 0) i)
      have g1 := hJB ((𝟙 _ ≫ eSec G') ≫ ![(ι[G']).left, 𝟙 G'.left] 0)
      have g2 : ((𝟙 _ ≫ eSec G') ≫ ![(ι[G']).left, 𝟙 G'.left] 0) y ∈
          (p.pr i).left ⁻¹ᵁ L.U (JB ((𝟙 _ ≫ eSec G') ≫ ![(ι[G']).left, 𝟙 G'.left] 0) i) := by
        unfold LB.LinComb LB.wchart at g1
        exact Set.mem_iInter.1 g1 i
      have e : (((𝟙 _ ≫ eSec G') ≫ ![(ι[G']).left, 𝟙 G'.left] 0) ≫ (p.pr i).left) y = eSec G y := by
        rw [Category.id_comp, c' 0, eSec_comp_hom]
      rw [← e]
      exact g2
end GlobalTheory
