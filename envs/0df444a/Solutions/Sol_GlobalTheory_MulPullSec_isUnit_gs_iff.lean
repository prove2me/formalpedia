-- Prove2me | solution 1 for GlobalTheory.MulPullSec.isUnit_gs_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:52:51.304717+00:00
-- url     : https://prove2.me/submissions/b659a20f-b735-4274-89af-2d36e914f891

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaFamilyOrigin_ExistsMulPullSec

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.MulPullSec
variable {X Y Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K]
namespace GlobalTheory.MulPullSec
theorem _root_.solution (r : Z ⟶ Y) (z : Z) (U : Y.Opens) (h : r z ∈ U) (a : Γ(Y, U)) :
    IsUnit (gs r z U a) ↔ r z ∈ Y.basicOpen a := by
  rw [gs_eq r z U h]
  refine (Z.mem_basicOpen (U := r ⁻¹ᵁ U) ((r.app U).hom a) z h).symm.trans ?_
  rw [← Scheme.preimage_basicOpen]
  rfl
end GlobalTheory.MulPullSec
