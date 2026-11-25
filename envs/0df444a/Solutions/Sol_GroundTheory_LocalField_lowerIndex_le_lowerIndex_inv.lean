-- Prove2me | solution 1 for GroundTheory.LocalField.lowerIndex_le_lowerIndex_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T07:57:51.670016+00:00
-- url     : https://prove2.me/submissions/b9fa6428-a98a-4474-806a-5ea86264766a

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_Ramification
import Definitions.Def_GroundTheory_LocalFields_Monogenic
import Definitions.Def_GroundTheory_LocalFields_Unramified
import Definitions.Def_GroundTheory_LocalFields_LowerIndex
import Theorems.Thm_GroundTheory_LocalField_le_lowerIndex_iff
import Theorems.Thm_GroundTheory_LocalField_lowerIndex_le

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
open ValuativeRel IsLocalRing IsDiscreteValuationRing Polynomial
variable (K L : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]
variable {K L}
namespace GroundTheory.LocalField
theorem _root_.solution (σ : L ≃ₐ[K] L) : lowerIndex K L σ ≤ lowerIndex K L σ⁻¹ := by
  rw [le_lowerIndex_iff]
  intro x
  have h : integerAlgEquiv K L σ⁻¹ x - x =
      -(integerAlgEquiv K L σ (integerAlgEquiv K L σ⁻¹ x) - integerAlgEquiv K L σ⁻¹ x) := by
    rw [← AlgEquiv.mul_apply, ← map_mul, mul_inv_cancel, map_one, AlgEquiv.one_apply]
    ring
  rw [h, AddValuation.map_neg]
  exact lowerIndex_le σ _
end GroundTheory.LocalField
