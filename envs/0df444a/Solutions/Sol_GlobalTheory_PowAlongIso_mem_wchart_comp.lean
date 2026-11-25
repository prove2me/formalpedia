-- Prove2me | solution 1 for GlobalTheory.PowAlongIso.mem_wchart_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:01:26.699277+00:00
-- url     : https://prove2.me/submissions/340be67b-e091-462c-b7f4-d31011edd9f6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_SameUnifRefl
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ProdExpPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifPowOf3
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_WeightedChartPullback_CancelSecAct
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_UniformizationPowerGroup
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
theorem _root_.solution {E : X'' ⟶ X'} {x : X''} {a : Fin j → M.ι} :
    x ∈ LB.wchart M (fun i => E ≫ pr i) a ↔ E x ∈ LB.wchart M pr a :=
  ⟨fun h => Set.mem_iInter.2 fun i => Set.mem_iInter.1 h i, fun h => Set.mem_iInter.2 fun i => Set.mem_iInter.1 h i⟩
end GlobalTheory.PowAlongIso
