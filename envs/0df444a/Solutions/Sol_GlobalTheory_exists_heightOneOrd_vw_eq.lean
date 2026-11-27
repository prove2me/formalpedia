-- Prove2me | solution 1 for GlobalTheory.exists_heightOneOrd_vw_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:41:15.347574+00:00
-- url     : https://prove2.me/submissions/01c28c7b-bbbe-4f63-8e09-31126b9f18e7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_MemRangeOfForallHeightEqOneOfIsReflexive
import Theorems.Thm_GlobalTheory_heightOneOrd_vw_zpow
import Theorems.Thm_GlobalTheory_heightOneOrd_vw_of_irreducible

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped nonZeroDivisors TensorProduct WithZero
open GlobalTheory
variable {A : Type*} [CommRing A] [IsDomain A]
variable (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
variable {K}
variable [IsNoetherianRing A]
variable [IsIntegrallyClosed A]
variable (p : Ideal A) [p.IsPrime] (hp : p.height = 1)
namespace GlobalTheory
theorem _root_.solution (n : ℤ) : ∃ x : K, x ≠ 0 ∧ heightOneOrd_vw p hp x = n := by
  have := isDiscreteValuationRing_of_height_eq_one p hp (primeLocalSubalgebra K p)
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (primeLocalSubalgebra K p)
  refine ⟨(ϖ : K) ^ n, zpow_ne_zero n fun e => hϖ.ne_zero (Subtype.ext e), ?_⟩
  rw [heightOneOrd_vw_zpow, heightOneOrd_vw_of_irreducible p hp hϖ, mul_one]
end GlobalTheory
