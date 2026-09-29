-- Prove2me | solution 1 for IsLocalRing.isPGroup_lowerRamificationGroup_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/ba9b3571-a9e9-5eb4-a83a-3cdf79f72e67

import Mathlib
import Definitions.Def_Mathlib_RingTheory_Valuation_LowerRamificationGroup
import Definitions.Def_Mathlib_RingTheory_Valuation_LowerRamificationGroupDepth
import Theorems.Thm_IsLocalRing_pow_mem_lowerRamificationGroup_succ
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsLocalRing_isPGroup_lowerRamificationGroup_one

set_option autoImplicit false

theorem solution
    {R : Type*} [CommRing R] [IsLocalRing R]
    {G : Type*} [Group G] [Finite G] [MulSemiringAction G R] [FaithfulSMul G R]
    {p : ℕ} (hp : (p : R) ∈ IsLocalRing.maximalIdeal R)
    (hsep : ⨅ n, IsLocalRing.maximalIdeal R ^ n = ⊥) :
    IsPGroup p (IsLocalRing.lowerRamificationGroup R G 1) := by
  obtain ⟨N, hN⟩ := IsLocalRing.exists_lowerRamificationGroup_eq_bot (R := R) (G := G) hsep
  intro σ
  refine ⟨N, ?_⟩
  have key : ∀ k : ℕ, (σ : G) ^ p ^ k ∈ IsLocalRing.lowerRamificationGroup R G (k + 1) := by
    intro k
    induction k with
    | zero => simpa using σ.2
    | succ k ih =>
      rw [pow_succ, pow_mul]
      exact IsLocalRing.pow_mem_lowerRamificationGroup_succ hp (Nat.succ_le_succ (Nat.zero_le k)) ih
  have h := key N
  rw [hN (N + 1) (Nat.le_succ N), Subgroup.mem_bot] at h
  exact Subtype.ext (by simpa using h)

end S_IsLocalRing_isPGroup_lowerRamificationGroup_one
end P2MW
export P2MW.S_IsLocalRing_isPGroup_lowerRamificationGroup_one (solution)
