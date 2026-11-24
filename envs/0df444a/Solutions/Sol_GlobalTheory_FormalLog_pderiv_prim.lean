-- Prove2me | solution 1 for GlobalTheory.FormalLog.pderiv_prim
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T15:50:56.282988+00:00
-- url     : https://prove2.me/submissions/4d731445-53cd-44a9-bd48-31ab982aca94

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_EqCOfPderivZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ConstantCoeffPrim
import Theorems.Thm_GlobalTheory_FormalLog_coeff_prim
import Theorems.Thm_GlobalTheory_FormalLog_degree_eq_sum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MvPowerSeries
open GlobalTheory GlobalTheory.FormalLog
variable {k : Type} [CommRing k] [Algebra ℚ k] {τ : Type} [Fintype τ] [DecidableEq τ]
namespace GlobalTheory.FormalLog
theorem _root_.solution (ω : τ → MvPowerSeries τ k)
    (hω : ∀ a c, pderiv k c (ω a) = pderiv k a (ω c)) (v : τ) : pderiv k v (prim ω) = ω v := by
  ext n
  rw [coeff_pderiv, coeff_prim]
  have hterm : ∀ w, ((n v : k) + 1) *
      (if (n + Finsupp.single v 1 : τ →₀ ℕ) w = 0 then 0 else coeff (n + Finsupp.single v 1 - Finsupp.single w 1) (ω w)) =
      ((n w : k) + if w = v then 1 else 0) * coeff n (ω v) := by
    intro w
    by_cases hwv : w = v
    · subst hwv
      rw [if_neg (by simp), add_tsub_cancel_right, if_pos rfl]
    · have hsw : (Finsupp.single v 1 : τ →₀ ℕ) w = 0 := by rw [Finsupp.single_apply, if_neg (Ne.symm hwv)]
      rw [Finsupp.add_apply, hsw, add_zero, if_neg hwv]
      by_cases hnw : n w = 0
      · simp [hnw]
      · rw [if_neg hnw]
        have hle : Finsupp.single w 1 ≤ n := Finsupp.single_le_iff.2 (Nat.one_le_iff_ne_zero.2 hnw)
        set p := n - Finsupp.single w 1 with hp
        have hpn : p + Finsupp.single w 1 = n := tsub_add_cancel_of_le hle
        have hpv : p v = n v := by
          simp [hp, Finsupp.tsub_apply, Finsupp.single_apply, hwv]
        have hpw : p w + 1 = n w := by
          simp only [hp, Finsupp.tsub_apply, Finsupp.single_eq_same]; omega
        have h1 : n + Finsupp.single v 1 - Finsupp.single w 1 = p + Finsupp.single v 1 := by
          rw [← hpn, add_right_comm, add_tsub_cancel_right]
        have hc := congrArg (coeff p) (hω v w)
        rw [coeff_pderiv, coeff_pderiv, hpn, hpv] at hc
        rw [h1, mul_comm, ← hc, ← hpw]
        push_cast
        ring
  have hsum : ((n v : k) + 1) * ∑ w, (if (n + Finsupp.single v 1 : τ →₀ ℕ) w = 0 then 0 else
      coeff (n + Finsupp.single v 1 - Finsupp.single w 1) (ω w)) = ((n.degree : k) + 1) * coeff n (ω v) := by
    rw [Finset.mul_sum, Finset.sum_congr rfl fun w _ => hterm w, ← Finset.sum_mul, Finset.sum_add_distrib,
      Finset.sum_ite_eq', if_pos (Finset.mem_univ _), degree_eq_sum]
    push_cast; ring
  have hdeg : ((n + Finsupp.single v 1).degree : ℚ) = (n.degree : ℚ) + 1 := by
    rw [map_add, Finsupp.degree_single]; push_cast; ring
  rw [mul_comm, ← mul_assoc, mul_comm _ (algebraMap ℚ k _), mul_assoc, hsum, hdeg, ← mul_assoc]
  have : algebraMap ℚ k (((n.degree : ℚ) + 1)⁻¹) * ((n.degree : k) + 1) = 1 := by
    rw [show ((n.degree : k) + 1) = algebraMap ℚ k ((n.degree : ℚ) + 1) by simp, ← map_mul,
      inv_mul_cancel₀ (by positivity), map_one]
  rw [this, one_mul]
end GlobalTheory.FormalLog
