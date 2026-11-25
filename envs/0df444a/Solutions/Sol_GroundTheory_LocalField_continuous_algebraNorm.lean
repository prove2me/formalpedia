-- Prove2me | solution 1 for GroundTheory.LocalField.continuous_algebraNorm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:45:09.242559+00:00
-- url     : https://prove2.me/submissions/090fd617-699b-4750-a9ca-0f0d38693ccb

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_Interface
import Definitions.Def_GroundTheory_LocalFields_Uniqueness
import Definitions.Def_GroundTheory_LocalFields_Integers
import Definitions.Def_GroundTheory_LocalFields_UnitsBasic
import Definitions.Def_GroundTheory_LocalFields_UnitsPowers
import Definitions.Def_GroundTheory_LocalFields_ExistsUnitFiltrationUnitsLeAndRangePowLe
import Definitions.Def_GroundTheory_LocalFields_ExistsUnitFiltrationUnitsLeRangeNormUnits

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.LocalField
open ValuativeRel IsLocalRing Topology Filter Polynomial
open scoped WithZero nonZeroDivisors
variable (K L : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]
variable {K L}
variable (K L)
namespace GroundTheory.LocalField
theorem _root_.solution : Continuous (Algebra.norm K : L → K) := by
  classical
  have := isModuleTopology K L
  let b := Module.finBasis K L
  have hlin : Continuous (Algebra.leftMulMatrix b : L → Matrix _ _ K) :=
    IsModuleTopology.continuous_of_linearMap (Algebra.leftMulMatrix b).toLinearMap
  have h : (Algebra.norm K : L → K) = fun x ↦ (Algebra.leftMulMatrix b x).det := by
    funext x
    exact Algebra.norm_eq_matrix_det b x
  rw [h]
  exact hlin.matrix_det
end GroundTheory.LocalField
