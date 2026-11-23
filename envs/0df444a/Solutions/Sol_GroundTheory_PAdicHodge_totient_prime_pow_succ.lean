-- Prove2me | solution 1 for GroundTheory.PAdicHodge.totient_prime_pow_succ
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:42:47.722497+00:00
-- url     : https://prove2.me/submissions/b4d094f0-15ab-44e2-bbc2-41862e6d8314

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_NormalizedTrace
import Definitions.Def_GroundTheory_PAdicHodge_CyclotomicField
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_NormNatCastPrime
import Definitions.Def_GroundTheory_PAdicHodge_CyclotomicTower

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
theorem _root_.solution {k : ℕ} (hk : 1 ≤ k) :
    Nat.totient (p ^ (k + 1)) = p * Nat.totient (p ^ k) := by
  rw [pow_succ', Nat.totient_mul_of_prime_of_dvd (Fact.out : p.Prime)
    (dvd_pow_self p (by omega))]
end GroundTheory.PAdicHodge
