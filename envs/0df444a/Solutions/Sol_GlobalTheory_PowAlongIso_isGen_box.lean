-- Prove2me | solution 1 for GlobalTheory.PowAlongIso.isGen_box
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:00:26.505364+00:00
-- url     : https://prove2.me/submissions/867a700b-cb79-4066-a773-ddc8bdeb3581

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_SameUnifRefl
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ProdExpPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifPowOf3
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_WeightedChartPullback_CancelSecAct
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_UniformizationPowerGroup
import Theorems.Thm_GlobalTheory_PowAlongIso_isGen_germ
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_gm_linCombIso
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_mem_finf


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
theorem _root_.solution (w : LB.Iso M' (LB.LinComb M pr (fun _ => 1))) : w.IsGen ↔ ∀ (Z : Scheme.{0}) (ψ : Z ⟶ X') (z : Z)
    (a a' : Fin j → M.ι) (b b' : M'.ι), ψ z ∈ LB.wchart M pr a → ψ z ∈ LB.wchart M pr a' → ψ z ∈ M'.U b →
    ψ z ∈ M'.U b' →
    bw w ψ z a b = (∏ i, gm (ψ ≫ pr i) z _ (M.g (a i) (a' i))) * (gm ψ z _ (M'.g b b'))⁻¹ * bw w ψ z a' b' := by
  rw [isGen_germ]
  refine forall_congr' fun Z => forall_congr' fun ψ => forall_congr' fun z => forall_congr' fun a =>
    forall_congr' fun a' => forall_congr' fun b => forall_congr' fun b' => forall_congr' fun ha =>
    forall_congr' fun ha' => forall_congr' fun hb => forall_congr' fun hb' => ?_
  have e := gm_linComb M pr (fun _ => 1) ψ z a a' ha ha'
  simp only [zpow_one] at e
  rw [← e]
  exact Iff.rfl
end GlobalTheory.PowAlongIso
