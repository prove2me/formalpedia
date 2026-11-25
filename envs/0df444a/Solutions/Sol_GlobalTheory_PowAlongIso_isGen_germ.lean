-- Prove2me | solution 1 for GlobalTheory.PowAlongIso.isGen_germ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:25:39.785407+00:00
-- url     : https://prove2.me/submissions/5d4cadf9-76f6-45c3-91eb-b910f27f005a

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
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_div
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
namespace GlobalTheory.PowAlongIso
theorem _root_.solution {L' L : LB X} (w : LB.Iso L' L) : w.IsGen ↔ ∀ (Y : Scheme.{0}) (f : Y ⟶ X) (y : Y) (j j' : L.ι)
    (k k' : L'.ι), f y ∈ L.U j → f y ∈ L.U j' → f y ∈ L'.U k → f y ∈ L'.U k' →
    gm f y (L.U j ⊓ L'.U k) (w.s (j, k)) =
      gm f y _ (L.g j j') * (gm f y _ (L'.g k k'))⁻¹ * gm f y (L.U j' ⊓ L'.U k') (w.s (j', k')) := by
  constructor
  · intro hw Y f y j j' k k' hj hj' hk hk'
    have hm : f y ∈ L.U j ⊓ L'.U k ⊓ (L.U j' ⊓ L'.U k') := ⟨⟨hj, hk⟩, ⟨hj', hk'⟩⟩
    have e := congrArg (gm f y (L.U j ⊓ L'.U k ⊓ (L.U j' ⊓ L'.U k'))) (hw (j, k) (j', k'))
    exact (gm_res f y _ hm _).symm.trans (e.trans ((map_mul _ _ _).trans (congrArg₂ (· * ·)
      (gm_div L' L f y (j, k) (j', k') hm) (gm_res f y _ hm _))))
  · rintro h ⟨j, k⟩ ⟨j', k'⟩
    refine unit_ext fun x hx => ?_
    have := h _ (𝟙 X) x j j' k k' hx.1.1 hx.2.1 hx.1.2 hx.2.2
    exact (gm_res _ x _ hx _).trans (this.trans ((map_mul _ _ _).trans (congrArg₂ (· * ·)
      (gm_div L' L (𝟙 X) x (j, k) (j', k') hx) (gm_res _ x _ hx _))).symm)
end GlobalTheory.PowAlongIso
