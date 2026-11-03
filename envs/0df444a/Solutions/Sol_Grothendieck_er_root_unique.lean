-- Prove2me | solution 1 for Grothendieck.er_root_unique
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-02T14:52:59.113118+00:00
-- url     : https://prove2.me/submissions/ffa443fd-c390-4ba5-a4ab-6cd26553af25

/-
# Proposition 3.3 of Briët--de Oliveira Filho--Vallentin (Theory of Computing 10(4), 2014)

`E_r` has exactly one zero in the open unit disc, at the origin, and `E_r'(0) = C_r ≠ 0`.

The paper's argument is Rouché's theorem on `|z| = 1` (`|tail| ≤ 1 - C_r < C_r = |C_r z|`).
Mathlib has no Rouché theorem; the proof below needs none, because the coefficients of `E_r`
are positive and *decreasing*. Writing `a_k = ErCoeff r k`, `G(w) = ∑ a_k w^k` and
`d_k = a_k - a_{k+1} ≥ 0`, the finite-difference identity

  `(1 - w) * G(w) = a_0 - w * ∑ d_k w^k`     (`ErCoeff_tsum_eq`)

gives `|G(w)| ≥ (a_0 - ‖w‖ ∑ d_k) / (1 + ‖w‖) ≥ a_0 (1 - ‖w‖) / (1 + ‖w‖) > 0` for `‖w‖ < 1`,
since `∑ d_k = a_0 - lim a_k ≤ a_0`.  As `ErComplex r z = z * G(z²)`, the only zero in the disc is
`z = 0`, and the same identity shows `G(w) - a_0 = O(‖w‖)` near `0`, hence `E_r'(0) = a_0 = C_r`.

Contents:
* positivity / monotonicity / recursion of `ErCoeff`, `summable_ErCoeff_diff` (the `d`-series);
* the identity `ErCoeff_tsum_eq` and the bound `norm_tsum_ErCoeff_diff_le`;
* zero-freeness `ErCoeff_tsum_ne_zero`, the factorisation `ErComplex_eq_mul_tsum`;
* the derivative `hasDerivAt_ErComplex`, and `er_root_unique_proof`.
-/
import Mathlib
import Definitions.Def_Grothendieck_Series

set_option autoImplicit false

noncomputable section

open scoped BigOperators Real Topology
open Filter

namespace Grothendieck

/-! ## Positivity and monotonicity of the coefficients `ErCoeff` -/

theorem risingFact_pos {a : ℝ} (ha : 0 < a) (k : ℕ) : 0 < risingFact a k := by
  rw [risingFact]
  exact Finset.prod_pos fun i _ => by positivity

theorem risingFact_succ (a : ℝ) (k : ℕ) :
    risingFact a (k + 1) = risingFact a k * (a + k) := by
  simp only [risingFact, Finset.prod_range_succ]

theorem Cr_pos {r : ℕ} (hr : 1 ≤ r) : 0 < Cr r := by
  unfold Cr
  have h1 : (0 : ℝ) < Real.Gamma (((r : ℝ) + 1) / 2) := Real.Gamma_pos_of_pos (by positivity)
  have h2 : (0 : ℝ) < Real.Gamma ((r : ℝ) / 2) := Real.Gamma_pos_of_pos (by positivity)
  have h3 : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr
  positivity

theorem ErCoeff_pos {r : ℕ} (hr : 1 ≤ r) (k : ℕ) : 0 < ErCoeff r k := by
  unfold ErCoeff
  have h1 := Cr_pos hr
  have h2 := risingFact_pos (a := 1 / 2) (by norm_num) k
  have h3 := risingFact_pos (a := (r : ℝ) / 2 + 1) (by positivity) k
  have h4 : (0 : ℝ) < (k.factorial : ℝ) := by exact_mod_cast k.factorial_pos
  positivity

/-- The recursion for the coefficients of `E_r`: the ratio `a_{k+1}/a_k`. -/
theorem ErCoeff_succ_mul (r k : ℕ) :
    ErCoeff r (k + 1) =
      ErCoeff r k * ((1 / 2 + (k : ℝ)) ^ 2 / (((r : ℝ) / 2 + 1 + (k : ℝ)) * ((k : ℝ) + 1))) := by
  unfold ErCoeff
  rw [risingFact_succ, risingFact_succ]
  have hf : ((k + 1).factorial : ℝ) = (k.factorial : ℝ) * ((k : ℝ) + 1) := by
    rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    ring
  rw [hf]
  have hp : (0 : ℝ) < risingFact (1 / 2) k := risingFact_pos (by norm_num) k
  have hq : (0 : ℝ) < risingFact ((r : ℝ) / 2 + 1) k := risingFact_pos (by positivity) k
  have hf0 : (0 : ℝ) < (k.factorial : ℝ) := by exact_mod_cast k.factorial_pos
  have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hk2 : (0 : ℝ) < ((r : ℝ) / 2 + 1 + (k : ℝ)) := by positivity
  field_simp

/-- The coefficients decrease: `a_{k+1} ≤ a_k` for `r ≥ 1`. -/
theorem ErCoeff_succ_le (r k : ℕ) (hr : 1 ≤ r) : ErCoeff r (k + 1) ≤ ErCoeff r k := by
  rw [ErCoeff_succ_mul]
  have hp := ErCoeff_pos hr k
  have hden : (0 : ℝ) < ((r : ℝ) / 2 + 1 + (k : ℝ)) * ((k : ℝ) + 1) := by positivity
  have hle : (1 / 2 + (k : ℝ)) ^ 2 / (((r : ℝ) / 2 + 1 + (k : ℝ)) * ((k : ℝ) + 1)) ≤ 1 := by
    rw [div_le_one hden]
    have hr1 : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
    have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    nlinarith [hr1, hk]
  calc ErCoeff r k * ((1 / 2 + (k : ℝ)) ^ 2 / (((r : ℝ) / 2 + 1 + (k : ℝ)) * ((k : ℝ) + 1)))
      ≤ ErCoeff r k * 1 := by
        apply mul_le_mul_of_nonneg_left hle (le_of_lt hp)
    _ = ErCoeff r k := mul_one _

theorem ErCoeff_antitone (r : ℕ) (hr : 1 ≤ r) : Antitone (ErCoeff r) :=
  antitone_nat_of_succ_le fun k => ErCoeff_succ_le r k hr

theorem ErCoeff_le_ErCoeff_zero (r k : ℕ) (hr : 1 ≤ r) : ErCoeff r k ≤ ErCoeff r 0 :=
  ErCoeff_antitone r hr (Nat.zero_le k)

/-- `ErCoeff r 0 = Cr r`. -/
theorem ErCoeff_zero (r : ℕ) : ErCoeff r 0 = Cr r := by
  simp [ErCoeff, risingFact]

/-! ## Summability of the difference series `a_k - a_{k+1}` -/

theorem summable_ErCoeff_diff (r : ℕ) (hr : 1 ≤ r) :
    Summable (fun k => ErCoeff r k - ErCoeff r (k + 1)) := by
  have hnonneg : ∀ k, 0 ≤ ErCoeff r k - ErCoeff r (k + 1) := fun k => by
    have := ErCoeff_succ_le r k hr
    linarith
  apply summable_of_sum_range_le hnonneg
  intro n
  have htel : ∑ k ∈ Finset.range n, (ErCoeff r k - ErCoeff r (k + 1)) =
      ErCoeff r 0 - ErCoeff r n := by
    rw [Finset.sum_range_sub']
  rw [htel]
  have := ErCoeff_pos hr n
  linarith

theorem tsum_ErCoeff_diff_le (r : ℕ) (hr : 1 ≤ r) :
    ∑' k, (ErCoeff r k - ErCoeff r (k + 1)) ≤ ErCoeff r 0 := by
  refine Real.tsum_le_of_sum_range_le (fun k => ?_) (fun n => ?_)
  · have := ErCoeff_succ_le r k hr; linarith
  · have htel : ∑ k ∈ Finset.range n, (ErCoeff r k - ErCoeff r (k + 1)) =
        ErCoeff r 0 - ErCoeff r n := by
      rw [Finset.sum_range_sub']
    rw [htel]
    have := ErCoeff_pos hr n
    linarith

theorem summable_ErCoeff_diff_mul_pow (r : ℕ) (hr : 1 ≤ r) {w : ℂ} (hw : ‖w‖ ≤ 1) :
    Summable (fun k => ((ErCoeff r k - ErCoeff r (k + 1) : ℝ) : ℂ) * w ^ k) := by
  refine Summable.of_norm_bounded (g := fun k => ErCoeff r k - ErCoeff r (k + 1))
    (summable_ErCoeff_diff r hr) fun k => ?_
  have hnn : (0 : ℝ) ≤ ErCoeff r k - ErCoeff r (k + 1) := by
    have := ErCoeff_succ_le r k hr; linarith
  have h1 : ‖((ErCoeff r k - ErCoeff r (k + 1) : ℝ) : ℂ)‖ = ErCoeff r k - ErCoeff r (k + 1) := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnn]
  rw [norm_mul, h1, norm_pow]
  have h2 : ‖w‖ ^ k ≤ 1 := pow_le_one₀ (norm_nonneg w) hw
  have := mul_le_mul_of_nonneg_left h2 hnn
  simpa using this

end Grothendieck

namespace Grothendieck

/-! ## The power series `∑ a_k w^k` is nonzero on the open unit disc -/

/-- Summability of the series `∑ a_k w^k` inside the unit disc (geometric comparison with `a_0`). -/
theorem summable_ErCoeff_mul_pow (r : ℕ) (hr : 1 ≤ r) {w : ℂ} (hw : ‖w‖ < 1) :
    Summable (fun k : ℕ => (ErCoeff r k : ℂ) * w ^ k) := by
  refine Summable.of_norm_bounded (g := fun k : ℕ => ErCoeff r 0 * ‖w‖ ^ k) ?_ fun k => ?_
  · exact (summable_geometric_of_lt_one (norm_nonneg w) hw).mul_left _
  · rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (le_of_lt (ErCoeff_pos hr k))]
    exact mul_le_mul_of_nonneg_right (ErCoeff_le_ErCoeff_zero r k hr) (by positivity)

/-- **The structural identity** `(1 - w) ∑ a_k w^k = a_0 - w ∑ (a_k - a_{k+1}) w^k`
inside the unit disc, using that the coefficients decrease. -/
theorem ErCoeff_tsum_eq (r : ℕ) (hr : 1 ≤ r) {w : ℂ} (hw : ‖w‖ < 1) :
    (1 - w) * (∑' k : ℕ, (ErCoeff r k : ℂ) * w ^ k) =
      (ErCoeff r 0 : ℂ) -
        w * ∑' k : ℕ, ((ErCoeff r k - ErCoeff r (k + 1) : ℝ) : ℂ) * w ^ k := by
  have hw1 : ‖w‖ ≤ 1 := le_of_lt hw
  have hc : Summable (fun k : ℕ => (ErCoeff r k : ℂ) * w ^ k) := summable_ErCoeff_mul_pow r hr hw
  have hc1 : Summable (fun k : ℕ => (ErCoeff r (k + 1) : ℂ) * w ^ (k + 1)) :=
    hc.comp_injective (fun a b h => Nat.succ.inj h)
  have hcw : Summable (fun k : ℕ => (ErCoeff r k : ℂ) * w ^ (k + 1)) :=
    (hc.mul_left w).congr fun k => by ring
  have hd : Summable (fun k : ℕ => ((ErCoeff r k - ErCoeff r (k + 1) : ℝ) : ℂ) * w ^ k) :=
    summable_ErCoeff_diff_mul_pow r hr hw1
  -- `w * ∑ a_k w^k = ∑ a_k w^{k+1}`
  have hstep1 : w * (∑' k : ℕ, (ErCoeff r k : ℂ) * w ^ k)
      = ∑' k : ℕ, (ErCoeff r k : ℂ) * w ^ (k + 1) := by
    rw [← Summable.tsum_mul_left w hc]
    exact tsum_congr fun k => by ring
  -- `∑ a_k w^k = a_0 + ∑ a_{k+1} w^{k+1}`
  have hsplit : ∑' k : ℕ, (ErCoeff r k : ℂ) * w ^ k
      = (ErCoeff r 0 : ℂ) + ∑' k : ℕ, (ErCoeff r (k + 1) : ℂ) * w ^ (k + 1) := by
    simpa using hc.tsum_eq_zero_add
  -- the difference series
  have hsub : ∑' k : ℕ, ((ErCoeff r k - ErCoeff r (k + 1) : ℝ) : ℂ) * w ^ (k + 1)
      = (∑' k : ℕ, (ErCoeff r k : ℂ) * w ^ (k + 1)) -
        ∑' k : ℕ, (ErCoeff r (k + 1) : ℂ) * w ^ (k + 1) := by
    rw [← Summable.tsum_sub hcw hc1]
    exact tsum_congr fun k => by push_cast; ring
  have hsubw : w * (∑' k : ℕ, ((ErCoeff r k - ErCoeff r (k + 1) : ℝ) : ℂ) * w ^ k)
      = ∑' k : ℕ, ((ErCoeff r k - ErCoeff r (k + 1) : ℝ) : ℂ) * w ^ (k + 1) := by
    rw [← Summable.tsum_mul_left w hd]
    exact tsum_congr fun k => by ring
  calc (1 - w) * (∑' k : ℕ, (ErCoeff r k : ℂ) * w ^ k)
      = (∑' k : ℕ, (ErCoeff r k : ℂ) * w ^ k) -
          w * (∑' k : ℕ, (ErCoeff r k : ℂ) * w ^ k) := by ring
    _ = (∑' k : ℕ, (ErCoeff r k : ℂ) * w ^ k) -
          ∑' k : ℕ, (ErCoeff r k : ℂ) * w ^ (k + 1) := by rw [hstep1]
    _ = ((ErCoeff r 0 : ℂ) + ∑' k : ℕ, (ErCoeff r (k + 1) : ℂ) * w ^ (k + 1)) -
          ∑' k : ℕ, (ErCoeff r k : ℂ) * w ^ (k + 1) := by rw [hsplit]
    _ = (ErCoeff r 0 : ℂ) - ((∑' k : ℕ, (ErCoeff r k : ℂ) * w ^ (k + 1)) -
          ∑' k : ℕ, (ErCoeff r (k + 1) : ℂ) * w ^ (k + 1)) := by ring
    _ = (ErCoeff r 0 : ℂ) -
          ∑' k : ℕ, ((ErCoeff r k - ErCoeff r (k + 1) : ℝ) : ℂ) * w ^ (k + 1) := by rw [hsub]
    _ = (ErCoeff r 0 : ℂ) -
          w * ∑' k : ℕ, ((ErCoeff r k - ErCoeff r (k + 1) : ℝ) : ℂ) * w ^ k := by rw [hsubw]

/-- The norm of the difference series is at most `a_0`. -/
theorem norm_tsum_ErCoeff_diff_le (r : ℕ) (hr : 1 ≤ r) {w : ℂ} (hw : ‖w‖ < 1) :
    ‖∑' k : ℕ, ((ErCoeff r k - ErCoeff r (k + 1) : ℝ) : ℂ) * w ^ k‖ ≤ ErCoeff r 0 := by
  have hw1 : ‖w‖ ≤ 1 := le_of_lt hw
  have hnn : ∀ k : ℕ, (0 : ℝ) ≤ ErCoeff r k - ErCoeff r (k + 1) := fun k => by
    have := ErCoeff_succ_le r k hr
    linarith
  have hd : Summable (fun k : ℕ => ((ErCoeff r k - ErCoeff r (k + 1) : ℝ) : ℂ) * w ^ k) :=
    summable_ErCoeff_diff_mul_pow r hr hw1
  have h1 : ∀ k : ℕ, ‖((ErCoeff r k - ErCoeff r (k + 1) : ℝ) : ℂ) * w ^ k‖
      ≤ ErCoeff r k - ErCoeff r (k + 1) := by
    intro k
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hnn k)]
    exact mul_le_of_le_one_right (hnn k) (pow_le_one₀ (norm_nonneg w) hw1)
  have h2 : Summable (fun k : ℕ => ‖((ErCoeff r k - ErCoeff r (k + 1) : ℝ) : ℂ) * w ^ k‖) := by
    refine Summable.of_norm_bounded (g := fun k : ℕ => ErCoeff r k - ErCoeff r (k + 1))
      (summable_ErCoeff_diff r hr) fun k => ?_
    rw [norm_norm]
    exact h1 k
  calc ‖∑' k : ℕ, ((ErCoeff r k - ErCoeff r (k + 1) : ℝ) : ℂ) * w ^ k‖
      ≤ ∑' k : ℕ, ‖((ErCoeff r k - ErCoeff r (k + 1) : ℝ) : ℂ) * w ^ k‖ :=
        norm_tsum_le_tsum_norm h2
    _ ≤ ∑' k : ℕ, (ErCoeff r k - ErCoeff r (k + 1)) :=
        Summable.tsum_le_tsum h1 h2 (summable_ErCoeff_diff r hr)
    _ ≤ ErCoeff r 0 := tsum_ErCoeff_diff_le r hr

/-- **Key zero-freeness**: for `‖w‖ < 1` the series `∑ a_k w^k` does not vanish. -/
theorem ErCoeff_tsum_ne_zero (r : ℕ) (hr : 1 ≤ r) {w : ℂ} (hw : ‖w‖ < 1) :
    (∑' k : ℕ, (ErCoeff r k : ℂ) * w ^ k) ≠ 0 := by
  have hE := norm_tsum_ErCoeff_diff_le r hr hw
  have hc0 : (0 : ℝ) < ErCoeff r 0 := ErCoeff_pos hr 0
  have h1 : ‖w * ∑' k : ℕ, ((ErCoeff r k - ErCoeff r (k + 1) : ℝ) : ℂ) * w ^ k‖
      ≤ ‖w‖ * ErCoeff r 0 := by
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left hE (norm_nonneg w)
  have h2 : ‖(ErCoeff r 0 : ℂ)‖ = ErCoeff r 0 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (le_of_lt hc0)]
  have hnorm : (0 : ℝ) < ‖(ErCoeff r 0 : ℂ) -
      w * ∑' k : ℕ, ((ErCoeff r k - ErCoeff r (k + 1) : ℝ) : ℂ) * w ^ k‖ := by
    have h3 : (0 : ℝ) < ErCoeff r 0 - ‖w‖ * ErCoeff r 0 := by
      have h4 : ‖w‖ * ErCoeff r 0 < 1 * ErCoeff r 0 := mul_lt_mul_of_pos_right hw hc0
      linarith
    calc (0 : ℝ) < ErCoeff r 0 - ‖w‖ * ErCoeff r 0 := h3
      _ = ‖(ErCoeff r 0 : ℂ)‖ - ‖w‖ * ErCoeff r 0 := by rw [h2]
      _ ≤ ‖(ErCoeff r 0 : ℂ)‖ -
            ‖w * ∑' k : ℕ, ((ErCoeff r k - ErCoeff r (k + 1) : ℝ) : ℂ) * w ^ k‖ := by linarith
      _ ≤ ‖(ErCoeff r 0 : ℂ) -
            w * ∑' k : ℕ, ((ErCoeff r k - ErCoeff r (k + 1) : ℝ) : ℂ) * w ^ k‖ :=
          norm_sub_norm_le _ _
  intro hzero
  have hid := ErCoeff_tsum_eq r hr hw
  rw [hzero, mul_zero] at hid
  rw [← hid] at hnorm
  simp at hnorm

/-- The analytic continuation factors as `E_r(z) = z · ∑ a_k (z²)^k` inside the unit disc. -/
theorem ErComplex_eq_mul_tsum (r : ℕ) (hr : 1 ≤ r) {z : ℂ} (hz : ‖z‖ < 1) :
    ErComplex r z = z * ∑' k : ℕ, (ErCoeff r k : ℂ) * (z ^ 2) ^ k := by
  have hw : ‖z ^ 2‖ < 1 := by
    rw [norm_pow]
    nlinarith [norm_nonneg z]
  have hsum : Summable (fun k : ℕ => (ErCoeff r k : ℂ) * (z ^ 2) ^ k) :=
    summable_ErCoeff_mul_pow r hr hw
  rw [ErComplex, ← Summable.tsum_mul_left z hsum]
  exact tsum_congr fun k => by ring

theorem ErComplex_zero (r : ℕ) : ErComplex r 0 = 0 := by
  rw [ErComplex]
  simp

/-- Quantitative bound: near the origin, `∑ a_k w^k = a_0 + O(‖w‖)`. -/
theorem norm_tsum_ErCoeff_sub_le (r : ℕ) (hr : 1 ≤ r) {w : ℂ} (hw : ‖w‖ ≤ 1 / 2) :
    ‖(∑' k : ℕ, (ErCoeff r k : ℂ) * w ^ k) - (ErCoeff r 0 : ℂ)‖
      ≤ 4 * ErCoeff r 0 * ‖w‖ := by
  have hw1 : ‖w‖ < 1 := by linarith
  have hid := ErCoeff_tsum_eq r hr hw1
  have h1w : (1 : ℂ) - w ≠ 0 := by
    intro h
    have h' : w = 1 := by linear_combination -h
    rw [h'] at hw
    norm_num at hw
  have hc0 : (0 : ℝ) < ErCoeff r 0 := ErCoeff_pos hr 0
  have hE := norm_tsum_ErCoeff_diff_le r hr hw1
  have hG : ∑' k : ℕ, (ErCoeff r k : ℂ) * w ^ k
      = ((1 : ℂ) - w)⁻¹ * ((ErCoeff r 0 : ℂ) -
          w * ∑' k : ℕ, ((ErCoeff r k - ErCoeff r (k + 1) : ℝ) : ℂ) * w ^ k) := by
    rw [eq_inv_mul_iff_mul_eq₀ h1w]
    exact hid
  have hkey : ((1 : ℂ) - w)⁻¹ * ((ErCoeff r 0 : ℂ) -
        w * ∑' k : ℕ, ((ErCoeff r k - ErCoeff r (k + 1) : ℝ) : ℂ) * w ^ k) - (ErCoeff r 0 : ℂ)
      = ((1 : ℂ) - w)⁻¹ * (w * ((ErCoeff r 0 : ℂ) -
          ∑' k : ℕ, ((ErCoeff r k - ErCoeff r (k + 1) : ℝ) : ℂ) * w ^ k)) := by
    field_simp
    ring
  rw [hG, hkey, norm_mul, norm_mul]
  have h1 : ‖((1 : ℂ) - w)⁻¹‖ ≤ 2 := by
    rw [norm_inv]
    have h2 : (1 : ℝ) - ‖w‖ ≤ ‖(1 : ℂ) - w‖ := by
      have := norm_sub_norm_le (1 : ℂ) w
      simpa using this
    have h4 : (1 : ℝ) / 2 ≤ 1 - ‖w‖ := by linarith
    have hpos : (0 : ℝ) < ‖(1 : ℂ) - w‖ := by linarith
    rw [inv_le_comm₀ hpos (by norm_num : (0 : ℝ) < 2)]
    linarith
  have hinner : ‖(ErCoeff r 0 : ℂ) -
      ∑' k : ℕ, ((ErCoeff r k - ErCoeff r (k + 1) : ℝ) : ℂ) * w ^ k‖ ≤ 2 * ErCoeff r 0 := by
    have hc0' : ‖(ErCoeff r 0 : ℂ)‖ = ErCoeff r 0 := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (le_of_lt hc0)]
    calc ‖(ErCoeff r 0 : ℂ) - ∑' k : ℕ, ((ErCoeff r k - ErCoeff r (k + 1) : ℝ) : ℂ) * w ^ k‖
        ≤ ‖(ErCoeff r 0 : ℂ)‖ + ‖∑' k : ℕ, ((ErCoeff r k - ErCoeff r (k + 1) : ℝ) : ℂ) * w ^ k‖ :=
          norm_sub_le _ _
      _ ≤ ErCoeff r 0 + ErCoeff r 0 := by rw [hc0']; linarith
      _ = 2 * ErCoeff r 0 := by ring
  calc ‖((1 : ℂ) - w)⁻¹‖ * (‖w‖ * ‖(ErCoeff r 0 : ℂ) -
        ∑' k : ℕ, ((ErCoeff r k - ErCoeff r (k + 1) : ℝ) : ℂ) * w ^ k‖)
      ≤ 2 * (‖w‖ * (2 * ErCoeff r 0)) := by
        refine mul_le_mul h1 ?_ (by positivity) (by norm_num)
        exact mul_le_mul_of_nonneg_left hinner (norm_nonneg w)
    _ = 4 * ErCoeff r 0 * ‖w‖ := by ring

theorem tendsto_slope_ErComplex (r : ℕ) (hr : 1 ≤ r) :
    Tendsto (fun t : ℂ => t⁻¹ * ErComplex r t) (𝓝[≠] (0 : ℂ)) (𝓝 (ErCoeff r 0 : ℂ)) := by
  have hbound : ∀ᶠ t : ℂ in 𝓝[≠] (0 : ℂ),
      ‖t⁻¹ * ErComplex r t - (ErCoeff r 0 : ℂ)‖ ≤ 4 * ErCoeff r 0 * ‖t‖ ^ 2 := by
    have hball : ∀ᶠ t : ℂ in 𝓝[≠] (0 : ℂ), ‖t‖ ≤ 1 / 2 := by
      filter_upwards [nhdsWithin_le_nhds
        (Metric.closedBall_mem_nhds (0 : ℂ) (by norm_num : (0 : ℝ) < 1 / 2))] with t ht
      simpa using ht
    filter_upwards [hball, self_mem_nhdsWithin] with t ht htne
    have hz : ‖t‖ < 1 := by linarith
    have hw2 : ‖t ^ 2‖ ≤ 1 / 2 := by
      rw [norm_pow]
      nlinarith [norm_nonneg t]
    have hfac := ErComplex_eq_mul_tsum r hr hz
    have hG := norm_tsum_ErCoeff_sub_le r hr hw2
    rw [norm_pow] at hG
    have h1 : t⁻¹ * ErComplex r t - (ErCoeff r 0 : ℂ)
        = (∑' k : ℕ, (ErCoeff r k : ℂ) * (t ^ 2) ^ k) - (ErCoeff r 0 : ℂ) := by
      rw [hfac, ← mul_assoc, inv_mul_cancel₀ htne, one_mul]
    rw [h1]
    exact hG
  have hmaj : Tendsto (fun t : ℂ => 4 * ErCoeff r 0 * ‖t‖ ^ 2) (𝓝[≠] (0 : ℂ)) (𝓝 0) := by
    have h1 : Tendsto (fun t : ℂ => ‖t‖ ^ 2) (𝓝[≠] (0 : ℂ)) (𝓝 0) := by
      have h2 : Tendsto (fun t : ℂ => ‖t‖ ^ 2) (𝓝 (0 : ℂ)) (𝓝 (‖(0 : ℂ)‖ ^ 2)) :=
        (continuous_norm.tendsto (0 : ℂ)).pow 2
      simpa using h2.mono_left nhdsWithin_le_nhds
    simpa using h1.const_mul (4 * ErCoeff r 0)
  have hzero : Tendsto (fun t : ℂ => t⁻¹ * ErComplex r t - (ErCoeff r 0 : ℂ))
      (𝓝[≠] (0 : ℂ)) (𝓝 0) := squeeze_zero_norm' hbound hmaj
  simpa using hzero.add_const (ErCoeff r 0 : ℂ)

theorem hasDerivAt_ErComplex (r : ℕ) (hr : 1 ≤ r) :
    HasDerivAt (ErComplex r) (ErCoeff r 0 : ℂ) 0 := by
  rw [hasDerivAt_iff_tendsto_slope_zero]
  simpa [smul_eq_mul, ErComplex_zero] using tendsto_slope_ErComplex r hr

/-- **Proposition 3.3** (p. 88): `E_r` has exactly one root in the open unit disc, a simple one
at the origin, with `E_r'(0) = C_r ≠ 0`. -/
theorem er_root_unique_proof (r : ℕ) (hr : 1 ≤ r) :
    (∀ z : ℂ, ‖z‖ < 1 → (ErComplex r z = 0 ↔ z = 0)) ∧
      deriv (ErComplex r) 0 = (Cr r : ℂ) ∧ Cr r ≠ 0 := by
  refine ⟨?_, ?_, ?_⟩
  · intro z hz
    constructor
    · intro h
      have hfac := ErComplex_eq_mul_tsum r hr hz
      rw [hfac] at h
      rcases mul_eq_zero.mp h with h1 | h2
      · exact h1
      · exfalso
        have hw : ‖z ^ 2‖ < 1 := by
          rw [norm_pow]
          nlinarith [norm_nonneg z]
        exact ErCoeff_tsum_ne_zero r hr hw h2
    · intro h
      rw [h, ErComplex_zero]
  · have h := (hasDerivAt_ErComplex r hr).deriv
    rw [h, ErCoeff_zero]
  · exact ne_of_gt (Cr_pos hr)

end Grothendieck

open Grothendieck in
theorem solution (r : ℕ) (hr : 1 ≤ r) :
    (∀ z : ℂ, ‖z‖ < 1 → (ErComplex r z = 0 ↔ z = 0)) ∧
      deriv (ErComplex r) 0 = (Cr r : ℂ) ∧ Cr r ≠ 0 :=
  er_root_unique_proof r hr
