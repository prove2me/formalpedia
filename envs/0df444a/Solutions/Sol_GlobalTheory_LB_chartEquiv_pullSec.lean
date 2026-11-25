-- Prove2me | solution 1 for GlobalTheory.LB.chartEquiv_pullSec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:50:18.421829+00:00
-- url     : https://prove2.me/submissions/0164452d-b00c-4bb7-87dc-41e71d79702c

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_LinCombTrivG
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ThetaVV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_AppCompatGeneric
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniformBaseChange_Transport
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_SpanSingletonEqTopIffIsUnitOfIsBaseChange
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_BijectiveSmulChartSec
import Theorems.Thm_GlobalTheory_LB_chartEquiv_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_LB_isLB_pull


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
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
open GlobalTheory.LB
variable {X Y : Scheme.{0}}
variable (L : LB X)
variable {L}
variable (f : Y ⟶ X)
namespace GlobalTheory.LB
theorem _root_.solution (hL : L.IsLB) (j : (L.pull f).ι) {V : X.Opens}
    (h : V ≤ L.U (j PUnit.unit)) (h' : f ⁻¹ᵁ V ≤ (L.pull f).U j) (s : Γ(toMod L, V)) :
    chartEquiv (Semi.LB.isLB_pull hL f) j h' (pullSec L f V s) =
      (f.app V).hom (chartEquiv hL (j PUnit.unit) h s) := by
  rw [chartEquiv_apply, chartEquiv_apply, coord_pullSec, resG_appLE,
    ← appLE_resG f (le_inf le_rfl h) le_rfl, Scheme.Hom.appLE_eq_app]
end GlobalTheory.LB
