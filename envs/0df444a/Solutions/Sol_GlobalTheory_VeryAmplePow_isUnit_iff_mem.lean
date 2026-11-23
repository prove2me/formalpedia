-- Prove2me | solution 1 for GlobalTheory.VeryAmplePow.isUnit_iff_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:13:45.096271+00:00
-- url     : https://prove2.me/submissions/4cd49fb3-b459-4d00-b07b-fcc3a0a3b3a5

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_SectionArithmetic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsUnitIffMem
import Theorems.Thm_GlobalTheory_VeryAmplePow_isUnit_gs
import Theorems.Thm_P2M_GlobalTheory_VeryAmplePow_sec_trans__22f5df49d8af

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.VeryAmplePow
open ReciprocityTheory.ChartRestriction.G.Geo.Tor TopologicalSpace
namespace GlobalTheory.VeryAmplePow
theorem _root_.solution {Z Y : Scheme.{0}} {M : LB Y} (s : LB.Sec M) (r : Z ⟶ Y) (z : Z) {j : M.ι}
    (hj : r z ∈ M.U j) : IsUnit (gs r z (M.U j) (s.f j)) ↔ r z ∈ nonzeroLocus s := by
  refine ⟨fun h => Opens.mem_iSup.2 ⟨j, (isUnit_gs r z _ hj _).1 h⟩, fun h => ?_⟩
  obtain ⟨k, hk⟩ := Opens.mem_iSup.1 h
  have hk' : r z ∈ M.U k := Y.basicOpen_le _ hk
  rw [sec_trans' s r z hj hk']
  exact (Units.isUnit _).mul ((isUnit_gs r z _ hk' _).2 hk)
end GlobalTheory.VeryAmplePow
