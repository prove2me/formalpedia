-- Prove2me | solution 1 for GroundTheory.PAdicHodge.mem_cycl_of_pow_prime_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:42:47.701802+00:00
-- url     : https://prove2.me/submissions/03fbb74e-ac23-4a7d-90b4-52a97b54146c

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_NormalizedTrace
import Definitions.Def_GroundTheory_PAdicHodge_CyclotomicField
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_NormNatCastPrime
import Definitions.Def_GroundTheory_PAdicHodge_CyclotomicTower
import Theorems.Thm_GroundTheory_PAdicHodge_pow_eq_one_mem_cycl


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.PAdicHodge
open IntermediateField Polynomial Module
noncomputable section
variable {p : ℕ} [Fact p.Prime]
namespace GroundTheory.PAdicHodge
theorem _root_.solution {k : ℕ} (hk : 1 ≤ k) {ε : PadicAlgCl p} (hε : ε ^ p = 1) :
    ε ∈ cycl p k := by
  apply pow_eq_one_mem_cycl
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [pow_succ', pow_mul, hε, one_pow]
end GroundTheory.PAdicHodge
