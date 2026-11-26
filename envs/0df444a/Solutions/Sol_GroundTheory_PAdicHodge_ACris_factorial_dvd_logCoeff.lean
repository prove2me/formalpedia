-- Prove2me | solution 1 for GroundTheory.PAdicHodge.ACris.factorial_dvd_logCoeff
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-26T16:47:37.585857+00:00
-- url     : https://prove2.me/submissions/940ec358-e3ed-4650-956c-23a058e30835

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_ACrisLog
import Definitions.Def_GroundTheory_PAdicHodge_LogPowSeries
import Definitions.Def_GroundTheory_PAdicHodge_ACrisPhi
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
omit hp

open GroundTheory.PAdicHodge.ACris Polynomial in
theorem solution (n j : ℕ) : (n.factorial : ℤ) ∣ logCoeff p n j := by
  have hX : X ∣ ((1 : ℤ[X]) + X) ^ p - 1 := by
    rw [X_dvd_iff, coeff_sub, coeff_one, coeff_one_add_X_pow]
    simp
  by_cases hj : j < n
  · have hpow : powCoeff p (n + 1) (j + 1) = 0 := by
      have hdvd : X ^ (n + 1) ∣ (((1 : ℤ[X]) + X) ^ p - 1) ^ (n + 1) :=
        pow_dvd_pow_of_dvd hX (n + 1)
      simpa [powCoeff] using (X_pow_dvd_iff.mp hdvd) (j + 1) (Nat.succ_lt_succ hj)
    simp [logCoeff, hpow]
  · have hle : n ≤ j := Nat.le_of_not_gt hj
    have hfac : (n + 1).factorial ∣ (j + 1).factorial :=
      Nat.factorial_dvd_factorial (Nat.succ_le_succ hle)
    simp only [logCoeff]
    refine dvd_mul_of_dvd_right ?_ _
    -- (n.factorial : ℤ) ∣ ↑((j+1)! / (n+1))
    have hdiv : (n + 1) * n.factorial ∣ (j + 1).factorial := by
      simpa [Nat.factorial_succ] using hfac
    -- Nat: a * b ∣ c → b ∣ c / a if a ∣ c
    have ha : (n + 1) ∣ (j + 1).factorial :=
      (Nat.dvd_factorial (Nat.succ_pos _) (Nat.succ_le_succ hle))
    have : n.factorial ∣ (j + 1).factorial / (n + 1) := by
      obtain ⟨c, hc⟩ := hdiv
      have : (j + 1).factorial / (n + 1) = n.factorial * c := by
        have hne : n + 1 ≠ 0 := Nat.succ_ne_zero n
        apply Nat.div_eq_of_eq_mul_right (Nat.succ_pos _)
        calc
          (j + 1).factorial = (n + 1) * n.factorial * c := hc
          _ = (n + 1) * (n.factorial * c) := by ring
      rw [this]
      exact Nat.dvd_mul_right _ _
    exact_mod_cast this
