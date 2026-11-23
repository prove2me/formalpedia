-- Prove2me | solution 1 for GlobalTheory.ZH.CrdCalc.crd_exists
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:10:31.637405+00:00
-- url     : https://prove2.me/submissions/cbe3ca94-3623-4a99-bf11-231cef74e9dd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PullChartIsLB
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsUnitCharts
import Theorems.Thm_GlobalTheory_ZH_CrdCalc_top_le_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra
noncomputable section
open GlobalTheory GlobalTheory.ZH GlobalTheory.ZH.CrdCalc
variable {R : Type} [CommRing R] {X : Scheme.{0}}
variable {H : LB X} {J : Type} {s : J → H.Sec}
namespace GlobalTheory.ZH.CrdCalc
theorem _root_.solution [IsLocalRing R] (hH : H.IsLB) (s : J → H.Sec) (x : Sp R ⟶ X) : ∃ v, Crd H s x v := by
  have : x (IsLocalRing.closedPoint R) ∈ ⨆ i, H.U i := by rw [hH.cover]; trivial
  obtain ⟨l, hl⟩ := TopologicalSpace.Opens.mem_iSup.1 this
  exact ⟨_, l, 1, (top_le_iff x _).2 hl, fun _ => rfl⟩
end GlobalTheory.ZH.CrdCalc
