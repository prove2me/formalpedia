-- Prove2me | solution 1 for GroundTheory.PAdicHodge.PowerSeries.log_subst_one_add_X_pow_sub_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:29:59.713349+00:00
-- url     : https://prove2.me/submissions/4fda6b35-63ab-487d-91f3-68bcef82697e

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_LogPowSeries
import Theorems.Thm_GroundTheory_PAdicHodge_one_add_X_mul_mk_neg_one_pow
import Theorems.Thm_GroundTheory_PAdicHodge_hasSubst_one_add_X_pow_sub_one

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
open PowerSeries
namespace GroundTheory.PAdicHodge
namespace PowerSeries
theorem _root_.solution (q : ℕ) :
    (log ℚ).subst ((1 + X : ℚ⟦X⟧) ^ q - 1) = (q : ℚ⟦X⟧) * log ℚ := by
  set U : ℚ⟦X⟧ := (1 + X) ^ q - 1 with hU
  have hs : HasSubst U := hasSubst_one_add_X_pow_sub_one q
  set G : ℚ⟦X⟧ := mk fun n => algebraMap ℚ ℚ ((-1 : ℚ) ^ n)
  have hG : (1 + U) * G.subst U = 1 := by
    have h := congrArg (substAlgHom (R := ℚ) hs) one_add_X_mul_mk_neg_one_pow
    rw [map_mul, map_add, map_one] at h
    simp only [coe_substAlgHom] at h
    rwa [subst_X hs] at h
  have h1U : 1 + U = (1 + X) ^ q := by rw [hU]; ring
  apply derivative.ext
  · have hd : d⁄dX ℚ ((log ℚ).subst U) = d⁄dX ℚ ((q : ℚ⟦X⟧) * log ℚ) := by
      have hunit : IsUnit (1 + X : ℚ⟦X⟧) := by
        rw [isUnit_iff_constantCoeff]; simp
      apply hunit.mul_left_cancel
      rw [derivative_subst hs, deriv_log, Derivation.leibniz, deriv_log]
      rcases q with _ | q
      · simp [hU]
      · have hdU : d⁄dX ℚ U = ((q + 1 : ℕ) : ℚ⟦X⟧) * (1 + X) ^ q := by
          rw [hU, map_sub, derivative_pow, Derivation.map_one_eq_zero, sub_zero, map_add,
            Derivation.map_one_eq_zero, derivative_X, zero_add, mul_one, Nat.add_sub_cancel]
        rw [hdU]
        have hc : d⁄dX ℚ ((q + 1 : ℕ) : ℚ⟦X⟧) = 0 := by
          rw [← map_natCast (C (R := ℚ)), derivative_C]
        rw [hc, smul_zero, add_zero, smul_eq_mul]
        calc (1 + X) * (G.subst U * (((q + 1 : ℕ) : ℚ⟦X⟧) * (1 + X) ^ q))
            = ((q + 1 : ℕ) : ℚ⟦X⟧) * ((1 + X) ^ (q + 1) * G.subst U) := by ring
          _ = ((q + 1 : ℕ) : ℚ⟦X⟧) := by rw [← h1U, hG, mul_one]
          _ = (1 + X) * (((q + 1 : ℕ) : ℚ⟦X⟧) * G) := by
            rw [mul_left_comm, one_add_X_mul_mk_neg_one_pow, mul_one]
    exact hd
  · have h0 : constantCoeff U = 0 := by simp [hU]
    have h1 : constantCoeff ((log ℚ).subst U) = 0 :=
      constantCoeff_subst_eq_zero h0 _ constantCoeff_log
    rw [h1]
    simp
end PowerSeries
end GroundTheory.PAdicHodge
