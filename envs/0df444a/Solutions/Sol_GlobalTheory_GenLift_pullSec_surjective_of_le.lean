-- Prove2me | solution 1 for GlobalTheory.GenLift.pullSec_surjective_of_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:19:39.341554+00:00
-- url     : https://prove2.me/submissions/8f307e37-1278-47da-931b-9d9fb7731991

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_BijectiveSmulChartSec
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsQuasicoherentOfForallExistsAffine
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsGenLiftOfIsNilpotent
import Theorems.Thm_GlobalTheory_LB_chartEquiv_pullSec
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
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.GenLift
open GlobalTheory.LB
variable {X Y : Scheme.{0}}
namespace GlobalTheory.GenLift
theorem _root_.solution (f : Y ⟶ X) [IsClosedImmersion f] {L : LB X} (hL : L.IsLB)
    {V : X.Opens} (hV : IsAffineOpen V) (i : L.ι) (h : V ≤ L.U i) :
    Function.Surjective (pullSec L f V) := by
  intro s
  have h' : f ⁻¹ᵁ V ≤ (L.pull f).U (fun _ => i) :=
    (f.preimage_mono h).trans (pull_U f (fun _ => i)).ge
  obtain ⟨a, ha⟩ := f.app_surjective V hV (chartEquiv (Semi.LB.isLB_pull hL f) (fun _ => i) h' s)
  refine ⟨(chartEquiv hL i h).symm a, ?_⟩
  apply (chartEquiv (Semi.LB.isLB_pull hL f) (fun _ => i) h').injective
  rw [chartEquiv_pullSec f hL (fun _ => i) h h', LinearEquiv.apply_symm_apply]
  exact ha
end GlobalTheory.GenLift
