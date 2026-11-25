-- Prove2me | solution 1 for GroundTheory.LocalField.addVal_term_of_totallyRamified
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T01:45:21.809718+00:00
-- url     : https://prove2.me/submissions/b8f89743-8833-4279-a82a-4fee3eddb5bb

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_Interface
import Definitions.Def_GroundTheory_LocalFields_Integers
import Definitions.Def_GroundTheory_LocalFields_IntermediateField
import Definitions.Def_GroundTheory_LocalFields_Eisenstein
import Theorems.Thm_GroundTheory_LocalField_addVal_algebraMap_integer
import Theorems.Thm_GroundTheory_LocalField_mem_maximalIdeal_pow_iff_le_addVal

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
open ValuativeRel Polynomial IsDiscreteValuationRing
open scoped _root_.IntermediateField
variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]
  (h : ramificationIndex K L = Module.finrank K L) {ϖ : 𝒪[L]} (hϖ : Irreducible ϖ)
include h hϖ
namespace GroundTheory.LocalField
theorem _root_.solution (g : 𝒪[K][X]) (i : ℕ) :
    (∀ k, g.coeff i ∈ IsLocalRing.maximalIdeal 𝒪[K] ^ k →
      ((Module.finrank K L * k + i : ℕ) : ℕ∞) ≤
        addVal 𝒪[L] (algebraMap 𝒪[K] 𝒪[L] (g.coeff i) * ϖ ^ i)) ∧
    (IsUnit (g.coeff i) → addVal 𝒪[L] (algebraMap 𝒪[K] 𝒪[L] (g.coeff i) * ϖ ^ i) = i) := by
  have hval : addVal 𝒪[L] (algebraMap 𝒪[K] 𝒪[L] (g.coeff i) * ϖ ^ i) =
      Module.finrank K L * addVal 𝒪[K] (g.coeff i) + i := by
    rw [addVal_mul, addVal_algebraMap_integer, h, hϖ.addVal_pow]
  refine ⟨fun k hk => ?_, fun hu => ?_⟩
  · rw [mem_maximalIdeal_pow_iff_le_addVal] at hk
    rw [hval]
    push_cast
    gcongr
  · rw [hval, addVal_eq_zero_iff.mpr hu, mul_zero, zero_add]
end GroundTheory.LocalField
