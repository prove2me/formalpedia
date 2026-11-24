-- Prove2me | solution 1 for GlobalTheory.SecPowUnflat.unflat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T20:37:26.120904+00:00
-- url     : https://prove2.me/submissions/94417d2c-a96f-4692-bdea-1bfb4714723f

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CocycleIdentityIso
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_LinCombPowSectionUnflatten
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm


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
open GlobalTheory GlobalTheory.SecPowUnflat
namespace GlobalTheory.SecPowUnflat
theorem _root_.solution : ∀ {X Y : Scheme.{0}} (L : LB X) (a n m : ℤ), m = a * n → ∀ (g : Y ⟶ X) (s' : LB.Sec (LB.LinComb L (K := Fin 1) (fun _ => g) (fun _ => m))), ∃ s : LB.Sec (LB.LinComb (LB.LinComb L (K := Fin 1) (fun _ => 𝟙 X) (fun _ => a)) (K := Fin 1) (fun _ => g) (fun _ => n)), ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (j : L.ι), g (r z) ∈ L.U j → gs r z _ (s'.f fun _ => j) = gs r z _ (s.f fun _ => fun _ => j) := by
  intro X Y L a n m hm g s'
  have le : ∀ J : Fin 1 → (Fin 1 → L.ι),
      LB.wchart (LB.LinComb L (K := Fin 1) (fun _ => 𝟙 X) (fun _ => a)) (fun _ : Fin 1 => g) J ≤
        LB.wchart L (fun _ : Fin 1 => g) (fun k => J k 0) := fun J y hy =>
    Set.mem_iInter.2 fun k => Set.mem_iInter.1 (Set.mem_iInter.1 hy k) 0
  refine ⟨⟨fun J => (Y.presheaf.map (homOfLE (le J)).op).hom (s'.f (fun k => J k 0)), fun J J' => ?_⟩, ?_⟩
  · refine fn_ext fun y hy => ?_
    have hy1 : y ∈ (LB.LinComb L (K := Fin 1) (fun _ => g) (fun _ => m)).U (fun k => J k 0) := le J hy.1
    have hy2 : y ∈ (LB.LinComb L (K := Fin 1) (fun _ => g) (fun _ => m)).U (fun k => J' k 0) := le J' hy.2
    have hS : y ∈ (LB.LinComb L (K := Fin 1) (fun _ => g) (fun _ => m)).U (fun k => J k 0) ⊓
        (LB.LinComb L (K := Fin 1) (fun _ => g) (fun _ => m)).U (fun k => J' k 0) := ⟨hy1, hy2⟩
    have c := congrArg (gs (𝟙 Y) y _) (s'.compat (fun k => J k 0) (fun k => J' k 0))
    rw [gs_res (𝟙 Y) y _ hS, gs_mul (𝟙 Y) y _ hS, gs_unit (𝟙 Y) y _ hS, gs_res (𝟙 Y) y _ hS] at c
    erw [gm_linComb L _ _ (𝟙 Y) y _ _ hy1 hy2] at c
    erw [gs_res (𝟙 Y) y _ hy, gs_res (𝟙 Y) y _ hy.1, gs_mul (𝟙 Y) y _ hy, gs_unit (𝟙 Y) y _ hy, gs_res (𝟙 Y) y _ hy,
      gs_res (𝟙 Y) y _ hy.2, c]
    erw [gm_linComb _ _ _ (𝟙 Y) y J J' hy.1 hy.2]
    have i1 : (𝟙 Y ≫ g) y ∈ (LB.LinComb L (K := Fin 1) (fun _ => 𝟙 X) (fun _ => a)).U (J 0) := by
      simpa using Set.mem_iInter.1 hy.1 0
    have i2 : (𝟙 Y ≫ g) y ∈ (LB.LinComb L (K := Fin 1) (fun _ => 𝟙 X) (fun _ => a)).U (J' 0) := by
      simpa using Set.mem_iInter.1 hy.2 0
    simp only [Fin.prod_univ_one]
    erw [gm_linComb L _ _ (𝟙 Y ≫ g) y (J 0) (J' 0) i1 i2]
    simp only [Fin.prod_univ_one, Category.comp_id, Category.id_comp, hm, zpow_mul]
    rfl
  · intro Z r z j h
    exact (gs_res r z (le _) (Set.mem_iInter.2 fun _ => Set.mem_iInter.2 fun _ => h) _).symm
end GlobalTheory.SecPowUnflat
