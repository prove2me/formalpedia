-- Prove2me | solution 1 for GlobalTheory.LevelCompat.corr_of_pmaps
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T18:43:55.412329+00:00
-- url     : https://prove2.me/submissions/4653f95b-e003-4bfe-93c3-1c249bd2c56f

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_WeightedChartPullback_CancelSecAct
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_GtCoordCompatOfPull
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_corr_of_val
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_chart
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_corr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_of
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
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
open GlobalTheory.LevelCompat
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
namespace GlobalTheory.LevelCompat
theorem _root_.solution {X X' Y₀ Y₁ Y₀' Y₁' : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} (hL : L.IsLB)
    (hL' : L'.IsLB) (w : LB.Iso L' (L.pull F)) {K : Type} [Fintype K] {ε : K → ℤ}
    {φ₀ : K → (Y₀ ⟶ X)} {φ₁ : K → (Y₁ ⟶ X)} {φ₀' : K → (Y₀' ⟶ X')} {φ₁' : K → (Y₁' ⟶ X')}
    {t₀ : LB.Gen (LB.LinComb L φ₀ ε)} {t₁ : LB.Gen (LB.LinComb L φ₁ ε)}
    {t₀' : LB.Gen (LB.LinComb L' φ₀' ε)} {t₁' : LB.Gen (LB.LinComb L' φ₁' ε)}
    {h₀ : Y₀' ⟶ Y₀} {h₁ : Y₁' ⟶ Y₁} {m : Y₀ ⟶ Y₁} {m' : Y₀' ⟶ Y₁'} (hm : m' ≫ h₁ = h₀ ≫ m)
    (c₀ : ∀ k, φ₀' k ≫ F = h₀ ≫ φ₀ k) (c₁ : ∀ k, φ₁' k ≫ F = h₁ ≫ φ₁ k) (c' : ∀ k, m' ≫ φ₁' k = φ₀' k)
    (H₀ : PMaps w φ₀' φ₀ ε t₀' t₀ h₀) (H₁ : PMaps w φ₁' φ₁ ε t₁' t₁ h₁)
    (H : LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ t₁ m) t₀) :
    LB.Gen.Corr L' _ _ _ _ (LB.pullGen L' _ _ t₁' m') t₀' := by
  refine corr_of_val hL' fun y J' hJ' => ?_
  choose J hJ using fun χ : Y₀' ⟶ X => exists_chart hL (χ y)
  have hJ : Good L y J := hJ
  rw [val_pull hJ', Category.id_comp]
  have a₀ := H₀ _ (𝟙 _) y (fun k => J (φ₀' k ≫ F)) (fun k => J' (φ₀' k)) (fun k => hJ (φ₀' k ≫ F))
    (fun k => hJ' (φ₀' k))
  have a₁ := H₁ _ m' y (fun k => J (φ₀' k ≫ F)) (fun k => J' (φ₀' k))
    (fun k => (congrArg (fun g => F (g y) ∈ L.U (J (φ₀' k ≫ F))) (c' k)).mpr (hJ (φ₀' k ≫ F)))
    (fun k => (congrArg (fun g => g y ∈ L'.U (J' (φ₀' k))) (c' k)).mpr (hJ' (φ₀' k)))
  rw [← val_of t₀ _ y J _ (fun k => by rw [Category.id_comp, c₀]),
    ← val_of t₀' _ y J' _ (fun k => by rw [Category.id_comp]), Category.id_comp] at a₀
  rw [← val_of t₁ _ y J _ (fun k => by rw [Category.assoc, ← c₁, ← Category.assoc, c']),
    ← val_of t₁' _ y J' _ (fun k => by rw [c']), hm, ← val_pull hJ, val_corr hJ H, a₀] at a₁
  simp only [Category.id_comp, c'] at a₁
  exact (mul_left_cancel a₁).symm
end GlobalTheory.LevelCompat
