-- Prove2me | solution 1 for GlobalTheory.PowAlongIso.mapsAt_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:32:50.471802+00:00
-- url     : https://prove2.me/submissions/dd286836-58ac-402e-88c0-5310d4d26987

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_SameUnifRefl
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ProdExpPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifPowOf3
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_WeightedChartPullback_CancelSecAct
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_UniformizationPowerGroup
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_gm_linCombIso
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_mem_finf
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_pull
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_res
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_unit_ext


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
theorem _root_.solution (w : LB.Iso M' (LB.LinComb M pr (fun _ => 1))) (p : Y ⟶ X') (n : ℤ)
    (a : LB.Gen (LB.LinComb M' (K := PUnit) (fun _ => p) (fun _ => n)))
    (b : LB.Gen (LB.LinComb M (K := Fin j) (fun i => p ≫ pr i) (fun _ => n))) :
    GeneratorPullback.MapsAt M M' pr w p n a b ↔ ∀ (y : Y) (jN : Fin j → M.ι) (jL : M'.ι),
      p y ∈ LB.wchart M pr jN → p y ∈ M'.U jL →
      gm (𝟙 Y) y (LB.wchart M (fun i => p ≫ pr i) jN) (b.s jN) =
        bw w p y jN jL ^ n * gm (𝟙 Y) y ((M'.pull p).U (fun _ => jL)) (a.s (fun _ => jL)) := by
  have key : ∀ (y : Y) (jN : Fin j → M.ι) (jL : M'.ι) (hm : p y ∈ LB.wchart M pr jN ⊓ M'.U jL),
      gm (𝟙 Y) y _ ((pullU p _ (w.s (jN, jL))) ^ n * res (GeneratorPullback.mapsAt_le_a M M' pr p jN jL) (a.s (fun _ => jL))) =
        bw w p y jN jL ^ n * gm (𝟙 Y) y ((M'.pull p).U (fun _ => jL)) (a.s (fun _ => jL)) := fun y jN jL hm =>
    (map_mul _ _ _).trans (congrArg₂ (· * ·) ((map_zpow _ _ _).trans (congrArg (· ^ n)
      ((gm_pull (𝟙 Y) p y (LB.wchart M pr jN ⊓ M'.U jL) hm _).trans (by rw [Category.id_comp]; rfl))))
      (gm_res (𝟙 Y) y (GeneratorPullback.mapsAt_le_a M M' pr p jN jL) hm _))
  constructor
  · intro H y jN jL h₁ h₂
    exact (gm_res (𝟙 Y) y (GeneratorPullback.mapsAt_le_b M M' pr p jN jL) ⟨h₁, h₂⟩ _).symm.trans
      ((congrArg (gm (𝟙 Y) y _) (H jN jL)).trans (key y jN jL ⟨h₁, h₂⟩))
  · intro H jN jL
    exact unit_ext fun y hy => (gm_res (𝟙 Y) y (GeneratorPullback.mapsAt_le_b M M' pr p jN jL) hy _).trans
      ((H y jN jL hy.1 hy.2).trans (key y jN jL hy).symm)
end GlobalTheory.PowAlongIso
