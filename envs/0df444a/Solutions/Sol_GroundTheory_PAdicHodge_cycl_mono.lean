-- Prove2me | solution 1 for GroundTheory.PAdicHodge.cycl_mono
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:33:50.743536+00:00
-- url     : https://prove2.me/submissions/c9cf5aba-77a2-4c1a-8c6d-6857704db0be

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_NormalizedTrace
import Definitions.Def_GroundTheory_PAdicHodge_CyclotomicField

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
open IntermediateField Polynomial
noncomputable section
variable (p : ℕ) [Fact p.Prime]
variable {p}
namespace GroundTheory.PAdicHodge
theorem _root_.solution : Monotone (cycl p) := fun n m h =>
  adjoin.mono _ _ _ fun x (hx : x ^ (p ^ n) = 1) => by
    show x ^ (p ^ m) = 1
    obtain ⟨k, hk⟩ := Nat.pow_dvd_pow p h
    rw [hk, pow_mul, hx, one_pow]
end GroundTheory.PAdicHodge
