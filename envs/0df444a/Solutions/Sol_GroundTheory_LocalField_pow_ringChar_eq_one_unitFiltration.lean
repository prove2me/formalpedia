-- Prove2me | solution 1 for GroundTheory.LocalField.pow_ringChar_eq_one_unitFiltration
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:14:22.151815+00:00
-- url     : https://prove2.me/submissions/9ebff324-5aca-4d33-9c3d-9ef71808907f

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_RamificationUnits
import Definitions.Def_GroundTheory_LocalFields_RamificationStructure

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
open ValuativeRel IsLocalRing
variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]
namespace GroundTheory.LocalField
theorem _root_.solution {n : ℕ} (hn : 1 ≤ n)
    (y : unitFiltration L n ⧸ unitFiltrationSucc L n) : y ^ ringChar 𝓀[L] = 1 := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[L]
  apply (unitFiltrationGradedEquiv hϖ hn).injective
  rw [map_pow, map_one]
  apply Multiplicative.toAdd.injective
  rw [toAdd_pow, toAdd_one, nsmul_eq_mul, ringChar.Nat.cast_ringChar, zero_mul]
end GroundTheory.LocalField
