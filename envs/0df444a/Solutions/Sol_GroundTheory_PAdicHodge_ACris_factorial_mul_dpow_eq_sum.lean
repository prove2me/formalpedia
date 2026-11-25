-- Prove2me | solution 1 for GroundTheory.PAdicHodge.ACris.factorial_mul_dpow_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:33:03.461136+00:00
-- url     : https://prove2.me/submissions/5b310eff-cb25-435f-94ea-a3f938b6ee13

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_ACrisLog
import Definitions.Def_GroundTheory_PAdicHodge_LogPowSeries
import Definitions.Def_GroundTheory_PAdicHodge_ACrisPhi
import Theorems.Thm_GroundTheory_PAdicHodge_ACris_powCoeff_of_lt
import Theorems.Thm_GroundTheory_PAdicHodge_ACris_one_add_pow_sub_one_pow_eq_sum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.PAdicHodge
open _root_.WittVector Polynomial
open GroundTheory.PAdicHodge.ACris
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable {p : ℕ} [hp : Fact p.Prime] [IsPerfectoidField K p]
local notation "θ" => fontaineTheta (normInteger K) p
local notation "𝔸" => Localization.Away (p : AInf K p)
namespace GroundTheory.PAdicHodge.ACris
theorem _root_.solution (x : AInf K p) (n L : ℕ) (hL : p * (n + 1) ≤ L) :
    (n.factorial : 𝔸) * dpow (n + 1) ((1 + x) ^ p - 1) =
      ∑ j ∈ Finset.range L, ((powCoeff p (n + 1) (j + 1) *
        (((j + 1).factorial / (n + 1) : ℕ) : ℤ) : ℤ) : 𝔸) * dpow (j + 1) x := by
  have h1 := isUnit_natCast (K := K) (p := p) (Nat.succ_ne_zero n)
  apply h1.mul_left_cancel
  rw [← mul_assoc, ← Nat.cast_mul, ← Nat.factorial_succ, factorial_mul_dpow, ← map_pow,
    one_add_pow_sub_one_pow_eq_sum x (n + 1) L hL, map_sum, Finset.sum_range_succ', Finset.mul_sum]
  simp only [map_mul, map_intCast, map_pow, pow_zero, mul_one, powCoeff_of_lt p n.succ_pos,
    Int.cast_zero, zero_mul, map_zero, add_zero]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases h : n ≤ j
  · have hdvd : n + 1 ∣ (j + 1).factorial := Nat.dvd_factorial n.succ_pos (Nat.succ_le_succ h)
    rw [← factorial_mul_dpow (j + 1) x]
    obtain ⟨d, hd⟩ : ∃ d, (j + 1).factorial / (n + 1) = d := ⟨_, rfl⟩
    have hd' : (n + 1) * d = (j + 1).factorial := by rw [← hd, Nat.mul_div_cancel' hdvd]
    rw [hd, ← hd']
    push_cast
    ring
  · rw [powCoeff_of_lt p (show j + 1 < n + 1 by omega)]
    simp
end GroundTheory.PAdicHodge.ACris
