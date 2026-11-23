-- Prove2me | solution 1 for GroundTheory.LocalField.partialNorm_add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:00:30.658633+00:00
-- url     : https://prove2.me/submissions/c2b54747-3f15-418c-b3ca-4d46f4e6264b

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_CompleteTrivial
import Definitions.Def_GroundTheory_LocalFields_HilbertCyclic

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
open Finset
variable {K L : Type*} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
variable (σ : L ≃ₐ[K] L) (x : Lˣ)
omit [FiniteDimensional K L]
namespace GroundTheory.LocalField
theorem _root_.solution (a b : ℕ) :
    partialNorm σ x (a + b) = partialNorm σ x a * (σ ^ a) • partialNorm σ x b := by
  rw [partialNorm, prod_range_add, partialNorm, partialNorm, smul_prod']
  simp_rw [pow_add, mul_smul]
end GroundTheory.LocalField
