-- Prove2me | solution 1 for GroundTheory.LocalField.min_le_lowerIndex_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T06:32:54.763507+00:00
-- url     : https://prove2.me/submissions/7d96584e-c6c0-4863-9353-f3d3a8bd6eef

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
theorem _root_.solution (σ τ : L ≃ₐ[K] L) :
    min (lowerIndex K L σ) (lowerIndex K L τ) ≤ lowerIndex K L (σ * τ) := by
  rw [le_lowerIndex_iff]
  intro x
  have h : integerAlgEquiv K L (σ * τ) x - x =
      (integerAlgEquiv K L σ (integerAlgEquiv K L τ x) - integerAlgEquiv K L τ x) +
        (integerAlgEquiv K L τ x - x) := by
    rw [map_mul, AlgEquiv.mul_apply]; ring
  rw [h]
  exact le_trans (min_le_min (lowerIndex_le σ _) (lowerIndex_le τ x)) ((addVal 𝒪[L]).map_add _ _)
end GroundTheory.LocalField
