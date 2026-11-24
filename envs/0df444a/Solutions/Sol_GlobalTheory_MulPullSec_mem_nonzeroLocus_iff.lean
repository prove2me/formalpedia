-- Prove2me | solution 1 for GlobalTheory.MulPullSec.mem_nonzeroLocus_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:56:00.436509+00:00
-- url     : https://prove2.me/submissions/dfc2869d-3293-4dfb-9d75-70110e1e4fbb

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaFamilyOrigin_ExistsMulPullSec
import Theorems.Thm_GlobalTheory_MulPullSec_isUnit_gs_iff

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
theorem _root_.solution {φ : K → (Y ⟶ X)} {ε : K → ℤ} (s : LB.Sec (LB.LinComb L φ ε)) (r : Z ⟶ Y) (z : Z)
    {J : (Z ⟶ X) → L.ι} (hJ : Good L z J) : r z ∈ Out.nonzeroLocus s ↔ IsUnit (sval s r z J) := by
  have hm := hJ.mem φ r
  refine Opens.mem_iSup.trans ⟨fun ⟨j, hj⟩ => ?_, fun h => ⟨_, (isUnit_gs_iff r z _ hm _).1 h⟩⟩
  have hj' : r z ∈ LB.wchart L φ j := Y.basicOpen_le _ hj
  have u := (isUnit_gs_iff r z _ hj' _).2 hj
  rw [sec_trans s r z hj' hm] at u
  exact isUnit_of_mul_isUnit_right u
end GlobalTheory.MulPullSec
