-- Prove2me | solution 1 for GroundTheory.LocalField.mem_range_unitsIncl_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:18:59.69682+00:00
-- url     : https://prove2.me/submissions/6e1c9dcb-2fe7-4908-9602-234b07bfbdeb

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_UnitsBasic

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.LocalField
open ValuativeRel IsLocalRing
open scoped WithZero
variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable {K}
namespace GroundTheory.LocalField
theorem _root_.solution {x : Kˣ} :
    x ∈ (unitsIncl K).range ↔ normalizedValuation K x = 1 := by
  constructor
  · rintro ⟨u, rfl⟩
    simpa using normalizedValuation_unit u
  · intro h
    have h1 : valuation K (x : K) = 1 := by
      rwa [← map_one (normalizedValuation K), normalizedValuation_eq_iff, map_one] at h
    have h2 : valuation K ((x⁻¹ : Kˣ) : K) = 1 := by
      rw [Units.val_inv_eq_inv_val, map_inv₀, h1, inv_one]
    refine ⟨⟨⟨x, h1.le⟩, ⟨(x⁻¹ : Kˣ), h2.le⟩, ?_, ?_⟩, ?_⟩
    · ext; simp
    · ext; simp
    · ext; rfl
end GroundTheory.LocalField
