-- Prove2me | solution 1 for GroundTheory.PAdicHodge.log_subst_one_add_X_pow_sub_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:29:29.119082+00:00
-- url     : https://prove2.me/submissions/1a284df4-ea8a-4134-a37b-be4473004786

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_BdRSeries
import Theorems.Thm_GroundTheory_PAdicHodge_seriesEval_X
import Theorems.Thm_GroundTheory_PAdicHodge_one_add_X_mul_geom
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.PAdicHodge.seriesEval_X

set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.PAdicHodge
open PowerSeries
namespace GroundTheory.PAdicHodge
theorem _root_.solution (k : ℕ) :
    (log ℚ).subst ((1 + X) ^ k - 1 : ℚ⟦X⟧) = (k : ℚ⟦X⟧) * log ℚ := by
  have hg : constantCoeff ((1 + X) ^ k - 1 : ℚ⟦X⟧) = 0 := by simp
  have hS := HasSubst.of_constantCoeff_zero' hg
  apply derivative.ext
  · set G : ℚ⟦X⟧ := mk (fun n => algebraMap ℚ ℚ ((-1) ^ n)) with hG
    have hsub : ((1 + X : ℚ⟦X⟧) ^ k) * G.subst ((1 + X) ^ k - 1 : ℚ⟦X⟧) = 1 := by
      have h := congrArg (substAlgHom hS) one_add_X_mul_geom
      rw [map_mul, map_one, map_add, map_one, coe_substAlgHom, subst_X hS, add_sub_cancel] at h
      exact h
    rw [derivative_subst hS, deriv_log, ← hG]
    have hd : d⁄dX ℚ ((k : ℚ⟦X⟧) * log ℚ) = (k : ℚ⟦X⟧) * G := by
      rw [Derivation.leibniz, deriv_log, ← hG, Derivation.map_natCast, smul_zero, add_zero,
        smul_eq_mul]
    rw [hd, map_sub, derivative_pow, derivative_one, sub_zero, map_add, derivative_one,
      derivative_X, zero_add, mul_one]
    have hne : ((1 + X : ℚ⟦X⟧) ^ k) ≠ 0 := by
      refine pow_ne_zero _ fun h => ?_
      have := congrArg constantCoeff h
      simp at this
    apply mul_left_cancel₀ hne
    rcases k with _ | k
    · simp
    · have h1 : (1 + X : ℚ⟦X⟧) * G = 1 := one_add_X_mul_geom
      calc (1 + X : ℚ⟦X⟧) ^ (k + 1) * (G.subst ((1 + X) ^ (k + 1) - 1 : ℚ⟦X⟧) *
              (((k + 1 : ℕ) : ℚ⟦X⟧) * (1 + X) ^ (k + 1 - 1)))
          = ((1 + X : ℚ⟦X⟧) ^ (k + 1) * G.subst ((1 + X) ^ (k + 1) - 1 : ℚ⟦X⟧)) *
              (((k + 1 : ℕ) : ℚ⟦X⟧) * (1 + X) ^ k) := by rw [Nat.add_sub_cancel]; ring
        _ = ((k + 1 : ℕ) : ℚ⟦X⟧) * (1 + X) ^ k * ((1 + X) * G) := by rw [hsub, h1]; ring
        _ = (1 + X : ℚ⟦X⟧) ^ (k + 1) * (((k + 1 : ℕ) : ℚ⟦X⟧) * G) := by ring
  · have h0 : MvPowerSeries.constantCoeff ((1 + X) ^ k - 1 : ℚ⟦X⟧) = 0 := hg
    have := constantCoeff_subst_eq_zero h0 (log ℚ) constantCoeff_log
    rw [map_mul, constantCoeff_log, mul_zero]
    exact this
end GroundTheory.PAdicHodge
