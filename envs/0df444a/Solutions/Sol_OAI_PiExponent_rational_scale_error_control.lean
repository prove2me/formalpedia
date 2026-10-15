-- Prove2me | solution 1 for OAI.PiExponent.rational_scale_error_control
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-15T05:09:50.982718+00:00
-- url     : https://prove2.me/submissions/594519b9-8b75-4d35-af8a-38f788fe8252

import Mathlib.Data.Real.Basic
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

theorem solution
    (theta : ℚ) (m K : ℕ) (a b s d g c : ℝ)
    (hK : 0 < K) (htheta : 0 < theta)
    (hbalance : (K : ℝ) ^ 2 * (theta : ℝ) ^ m < 1)
    (ha : 0 ≤ a) (ha_gap : a < g / 4)
    (hb : 0 ≤ b) (hs : 0 < s) (hd : 0 ≤ d) (hg : 0 < g)
    (hcapacity : 4 * (b + 2 * s) * (1 + g) / g < c) :
    ∃ (v w : ℚ) (n : ℕ),
      0 < v ∧ 0 < w ∧ 0 < n ∧
      (K : ℚ) * (w / v) * theta ^ m < 1 ∧
      0 ≤ a + b / (v : ℝ) + s * (K : ℝ) / (w : ℝ) + d / (n : ℝ) ∧
      a + b / (v : ℝ) + s * (K : ℝ) / (w : ℝ) + d / (n : ℝ) < g ∧
      1 + (a + b / (v : ℝ) + s * (K : ℝ) / (w : ℝ) + d / (n : ℝ)) <
        c / (v : ℝ) := by
  -- A rational point in this interval leaves both error and capacity margins.
  have hB : 0 < b + 2 * s := by linarith only [hb, hs]
  have hleft : 0 < 2 * (b + 2 * s) / g :=
    div_pos (mul_pos (by norm_num) hB) hg
  have hinterval :
      2 * (b + 2 * s) / g < 4 * (b + 2 * s) / g := by
    apply (div_lt_div_iff_of_pos_right hg).2
    linarith only [hB]
  obtain ⟨v, hvlower, hvupper⟩ := exists_rat_btwn hinterval
  have hvR : 0 < (v : ℝ) := hleft.trans hvlower
  have hv : 0 < v := by exact_mod_cast hvR
  have hvsmall : (b + 2 * s) / (v : ℝ) < g / 2 := by
    apply (div_lt_iff₀ hvR).2
    have hlower : 2 * (b + 2 * s) < (v : ℝ) * g :=
      (div_lt_iff₀ hg).1 hvlower
    nlinarith only [hlower]
  have hvcollision : 1 + g < c / (v : ℝ) := by
    apply (lt_div_iff₀ hvR).2
    calc
      (1 + g) * (v : ℝ) < (1 + g) * (4 * (b + 2 * s) / g) :=
        mul_lt_mul_of_pos_left hvupper (by linarith only [hg])
      _ = 4 * (b + 2 * s) * (1 + g) / g := by ring
      _ < c := hcapacity
  -- The exact rational choice w = K v already meets the balance condition.
  let w : ℚ := (K : ℚ) * v
  have hKQ : 0 < (K : ℚ) := by exact_mod_cast hK
  have hKR : 0 < (K : ℝ) := by exact_mod_cast hK
  have hw : 0 < w := mul_pos hKQ hv
  have hwR : 0 < (w : ℝ) := by exact_mod_cast hw
  have hwcast : (w : ℝ) = (K : ℝ) * (v : ℝ) := by
    simp only [w, Rat.cast_mul, Rat.cast_natCast]
  have hwratio : (K : ℚ) * (w / v) * theta ^ m < 1 := by
    have hbalanceQ : (K : ℚ) ^ 2 * theta ^ m < 1 := by
      exact_mod_cast hbalance
    change (K : ℚ) * (((K : ℚ) * v) / v) * theta ^ m < 1
    rw [mul_div_cancel_right₀ _ hv.ne']
    simpa only [pow_two] using hbalanceQ
  have hwerror : s * (K : ℝ) / (w : ℝ) = s / (v : ℝ) := by
    rw [hwcast, mul_comm s, mul_div_mul_left _ _ hKR.ne']
  have hcore :
      b / (v : ℝ) + s * (K : ℝ) / (w : ℝ) <
        (b + 2 * s) / (v : ℝ) := by
    rw [hwerror, ← add_div]
    apply (div_lt_div_iff_of_pos_right hvR).2
    linarith only [hs]
  -- Archimedeanness controls the remaining reciprocal error, also when d = 0.
  obtain ⟨n, hnlarge⟩ := exists_nat_gt (max 0 (4 * d / g))
  have hnR : 0 < (n : ℝ) := (le_max_left _ _).trans_lt hnlarge
  have hn : 0 < n := by exact_mod_cast hnR
  have hnerror : d / (n : ℝ) < g / 4 := by
    apply (div_lt_iff₀ hnR).2
    have hlarge : 4 * d / g < (n : ℝ) :=
      (le_max_right _ _).trans_lt hnlarge
    have hlarge' : 4 * d < (n : ℝ) * g := (div_lt_iff₀ hg).1 hlarge
    nlinarith only [hlarge']
  have herror_nonneg :
      0 ≤ a + b / (v : ℝ) + s * (K : ℝ) / (w : ℝ) + d / (n : ℝ) := by
    exact add_nonneg
      (add_nonneg (add_nonneg ha (div_nonneg hb hvR.le))
        (div_nonneg (mul_nonneg hs.le hKR.le) hwR.le))
      (div_nonneg hd hnR.le)
  have herror_lt :
      a + b / (v : ℝ) + s * (K : ℝ) / (w : ℝ) + d / (n : ℝ) < g := by
    linarith only [ha_gap, hvsmall, hnerror, hcore]
  refine ⟨v, w, n, hv, hw, hn, hwratio, herror_nonneg, herror_lt, ?_⟩
  linarith only [herror_lt, hvcollision]
