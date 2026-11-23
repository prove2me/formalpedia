-- Prove2me | solution 1 for GroundTheory.Global.div_mem_unitFiltration_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:19:59.726699+00:00
-- url     : https://prove2.me/submissions/78e809a9-63b4-4e60-99d8-457f5e0e8c9d

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_UnitsBasic
import Definitions.Def_GroundTheory_LocalFields_FilteredSurj
import Definitions.Def_GroundTheory_GlobalFields_KummerTheory_LocalIndex

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Global
open ValuativeRel IsLocalRing GroundTheory.LocalField
open scoped WithZero
variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
namespace GroundTheory.Global
theorem _root_.solution {k : ℕ} {x y : 𝒪[K]ˣ} :
    x / y ∈ unitFiltration K k ↔ (x : 𝒪[K]) - y ∈ 𝓂[K] ^ k := by
  rw [mem_unitFiltration]
  have h1 : ((x / y : 𝒪[K]ˣ) : 𝒪[K]) - 1 = ((x : 𝒪[K]) - y) * ((y⁻¹ : 𝒪[K]ˣ) : 𝒪[K]) := by
    rw [div_eq_mul_inv, Units.val_mul]
    linear_combination (Units.mul_inv y)
  have h2 : (x : 𝒪[K]) - y = (y : 𝒪[K]) * (((x / y : 𝒪[K]ˣ) : 𝒪[K]) - 1) := by
    rw [div_eq_mul_inv, Units.val_mul]
    linear_combination (-(x : 𝒪[K])) * (Units.mul_inv y)
  constructor
  · intro h; rw [h2]; exact Ideal.mul_mem_left _ _ h
  · intro h; rw [h1]; exact Ideal.mul_mem_right _ _ h
end GroundTheory.Global
