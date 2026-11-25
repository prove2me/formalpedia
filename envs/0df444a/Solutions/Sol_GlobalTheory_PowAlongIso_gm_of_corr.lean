-- Prove2me | solution 1 for GlobalTheory.PowAlongIso.gm_of_corr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:32:45.853405+00:00
-- url     : https://prove2.me/submissions/6b6fd746-2dd9-4297-b660-88c966daddb7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_SameUnifRefl
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ProdExpPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifPowOf3
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_WeightedChartPullback_CancelSecAct
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_UniformizationPowerGroup
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_gm_linCombIso
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_mem_finf
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
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
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.PowAlongIso
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.TorsionFormCompare
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.DVR (bw gm_linCombIso mem_finf)
variable {X X' X'' Y Y' Y₀ Z : Scheme.{0}}
variable {M : LB X} {M' : LB X'} {M'' : LB X''} {j : ℕ} {pr : Fin j → (X' ⟶ X)}
namespace GlobalTheory.PowAlongIso
theorem _root_.solution (hM : M.IsLB) {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {φ' : K → (Y' ⟶ X)} {ε : K → ℤ}
    {h : Y' ⟶ Y} (hφ : ∀ k, φ' k = h ≫ φ k) {t : LB.Gen (LB.LinComb M φ ε)} {t' : LB.Gen (LB.LinComb M φ' ε)}
    (ht : t.IsGen) (ht' : t'.IsGen) (H : LB.Gen.Corr M _ _ _ _ t' (LB.pullGen M φ ε t h)) (r : Z ⟶ Y') (z : Z)
    {a : K → M.ι} (ha : r z ∈ LB.wchart M φ' a) :
    gm r z (LB.wchart M φ' a) (t'.s a) = gm (r ≫ h) z (LB.wchart M φ a) (t.s a) := by
  obtain rfl : φ' = fun k => h ≫ φ k := funext hφ
  choose J hJ using fun χ : Z ⟶ X => exists_chart hM (χ z)
  have hJ : Good M z J := hJ
  have e := (val_corr hJ H r).trans (val_pull hJ t h r)
  rw [val_of t (r ≫ h) z J (fun k => J (r ≫ h ≫ φ k)) (fun k => by rw [Category.assoc])] at e
  have m := hJ.mem (fun k => h ≫ φ k) r
  rw [gen_trans ht' r z ha m, gen_trans ht (r ≫ h) z (j := a) (j' := fun k => J (r ≫ h ≫ φ k))
    (Set.mem_iInter.2 fun k => Set.mem_iInter.1 ha k) (Set.mem_iInter.2 fun k => Set.mem_iInter.1 m k), ← e]
  simp only [trF, Category.assoc, val]
end GlobalTheory.PowAlongIso
