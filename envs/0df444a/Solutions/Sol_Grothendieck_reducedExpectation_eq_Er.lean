-- Prove2me | solution 1 for Grothendieck.reducedExpectation_eq_Er
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T05:57:00.385478+00:00
-- url     : https://prove2.me/submissions/5e140669-0d94-4543-b78c-4597d51da3cf

import Mathlib
import Definitions.Def_Grothendieck_Reduced
import Definitions.Def_Grothendieck_Fubini
import Definitions.Def_Grothendieck_Series

set_option autoImplicit false

open MeasureTheory
open scoped BigOperators Real Topology ENNReal

/-! ### inlined: chain/Beta.lean -/
noncomputable section

open MeasureTheory intervalIntegral Filter
open scoped BigOperators Real Topology

namespace Grothendieck

/-- The rising factorial `(a)_k = a(a+1)···(a+k-1)` is a ratio of Gamma values. -/
theorem risingFact_eq_Gamma_div {a : ℝ} (ha : 0 < a) (k : ℕ) :
    risingFact a k = Real.Gamma (a + k) / Real.Gamma a := by
  induction k with
  | zero =>
    rw [risingFact, Finset.prod_range_zero, Nat.cast_zero, add_zero,
      div_self (Real.Gamma_pos_of_pos ha).ne']
  | succ k ih =>
    have hk : a + (k : ℝ) ≠ 0 := by positivity
    have h1 : risingFact a (k + 1) = risingFact a k * (a + (k : ℝ)) := by
      simp only [risingFact, Finset.prod_range_succ]
    have hcast : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
    have heq : a + ((k : ℝ) + 1) = (a + (k : ℝ)) + 1 := by ring
    rw [h1, ih, hcast, heq, Real.Gamma_add_one hk]
    ring

/-- `Real.Gamma (1/2) = √π` in the shape used below. -/
theorem Gamma_half_eq_sqrt_pi : Real.Gamma (1 / 2) = Real.sqrt Real.pi :=
  Real.Gamma_one_half_eq

/-- The Beta integral: `∫_0^1 u^{a-1} (1-u)^{b-1} du = Γ a Γ b / Γ (a+b)` for `a, b > 0`. -/
theorem betaIntegral_real {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (∫ u in (0 : ℝ)..1, u ^ (a - 1) * (1 - u) ^ (b - 1))
      = Real.Gamma a * Real.Gamma b / Real.Gamma (a + b) := by
  have hkey := Complex.Gamma_mul_Gamma_eq_betaIntegral (s := (a : ℂ)) (t := (b : ℂ))
    (by simpa using ha) (by simpa using hb)
  have hbeta : Complex.betaIntegral (a : ℂ) (b : ℂ)
      = ((∫ u in (0 : ℝ)..1, u ^ (a - 1) * (1 - u) ^ (b - 1) : ℝ) : ℂ) := by
    rw [Complex.betaIntegral.eq_1]
    rw [← intervalIntegral.integral_ofReal
      (f := fun u : ℝ => u ^ (a - 1) * (1 - u) ^ (b - 1))]
    apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hx
    obtain ⟨hx0, hx1⟩ := hx
    change (↑x : ℂ) ^ ((a : ℂ) - 1) * ((1 : ℂ) - ↑x) ^ ((b : ℂ) - 1)
      = ↑(x ^ (a - 1) * (1 - x) ^ (b - 1))
    have h1 : (↑x : ℂ) ^ ((a : ℂ) - 1) = ↑(x ^ (a - 1)) := by
      rw [show ((a : ℂ) - 1) = ((a - 1 : ℝ) : ℂ) by push_cast; ring]
      exact (Complex.ofReal_cpow hx0 (a - 1)).symm
    have h2 : ((1 : ℂ) - ↑x) ^ ((b : ℂ) - 1) = ↑((1 - x) ^ (b - 1)) := by
      have hx' : (1 : ℂ) - ↑x = ↑(1 - x) := by push_cast; ring
      rw [hx', show ((b : ℂ) - 1) = ((b - 1 : ℝ) : ℂ) by push_cast; ring]
      exact (Complex.ofReal_cpow (by linarith : (0 : ℝ) ≤ 1 - x) (b - 1)).symm
    rw [h1, h2]
    push_cast
    ring
  have h2 : (Real.Gamma a * Real.Gamma b : ℝ)
      = Real.Gamma (a + b) * ∫ u in (0 : ℝ)..1, u ^ (a - 1) * (1 - u) ^ (b - 1) := by
    have hc : ((Real.Gamma a * Real.Gamma b : ℝ) : ℂ)
        = ((Real.Gamma (a + b)
            * ∫ u in (0 : ℝ)..1, u ^ (a - 1) * (1 - u) ^ (b - 1) : ℝ) : ℂ) := by
      push_cast
      rw [← Complex.Gamma_ofReal a, ← Complex.Gamma_ofReal b, ← Complex.Gamma_ofReal (a + b)]
      rw [show ((a : ℝ) : ℂ) + ((b : ℝ) : ℂ) = ((a + b : ℝ) : ℂ) by push_cast; ring,
        hbeta] at hkey
      exact hkey
    exact_mod_cast hc
  have hpos : Real.Gamma (a + b) ≠ 0 := (Real.Gamma_pos_of_pos (by linarith)).ne'
  rw [eq_div_iff hpos, mul_comm]
  exact h2.symm

/-- Integrability of `v ↦ v^{a-1} e^{-rv}` on `(0,∞)`, for `a, r > 0`. -/
theorem integrableOn_rpow_mul_exp_neg_mul {a r : ℝ} (ha : 0 < a) (hr : 0 < r) :
    IntegrableOn (fun v : ℝ => v ^ (a - 1) * Real.exp (-(r * v))) (Set.Ioi 0) := by
  have hbase : IntegrableOn (fun w : ℝ => w ^ (a - 1) * Real.exp (-w)) (Set.Ioi 0) := by
    simpa only [mul_comm] using Real.GammaIntegral_convergent ha
  have hcomp : IntegrableOn (fun v : ℝ => (r * v) ^ (a - 1) * Real.exp (-(r * v)))
      (Set.Ioi 0) :=
    (MeasureTheory.integrableOn_Ioi_comp_mul_left_iff
      (f := fun w : ℝ => w ^ (a - 1) * Real.exp (-w)) (c := 0) hr).2 (by simpa using hbase)
  have h1 : Integrable (fun v : ℝ => r ^ (1 - a) * ((r * v) ^ (a - 1) * Real.exp (-(r * v))))
      (volume.restrict (Set.Ioi 0)) := hcomp.const_mul _
  refine h1.congr ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
  have hv0 : (0 : ℝ) < v := hv
  have hr0 : (0 : ℝ) ≤ r := le_of_lt hr
  have hv0' : (0 : ℝ) ≤ v := le_of_lt hv0
  rw [Real.mul_rpow hr0 hv0']
  have hrr : r ^ (1 - a) * r ^ (a - 1) = 1 := by
    rw [← Real.rpow_add hr, show 1 - a + (a - 1) = 0 by ring, Real.rpow_zero]
  linear_combination (v ^ (a - 1) * Real.exp (-(r * v))) * hrr

/-- The Gamma/binomial expansion `(1-x)^{-s} = ∑_n Γ(s+n)/(Γ s · n!) x^n` for `|x| < 1`. -/
theorem hasSum_rpow_neg_of_abs_lt_one {s : ℝ} (hs : 0 < s) {x : ℝ} (hx : |x| < 1) :
    HasSum (fun n : ℕ => Real.Gamma (s + n) / (Real.Gamma s * (n.factorial : ℝ)) * x ^ n)
      ((1 - x) ^ (-s)) := by
  obtain ⟨hxm, hx1⟩ := abs_lt.1 hx
  have hpos : (0 : ℝ) < 1 - x := by linarith
  have hpos' : (0 : ℝ) ≤ 1 - x := le_of_lt hpos
  -- the integral identity for `(1-x)^{-s}`
  have hInt : (∫ v in Set.Ioi (0 : ℝ), v ^ (s - 1) * Real.exp (-((1 - x) * v)))
      = (1 - x) ^ (-s) * Real.Gamma s := by
    rw [Real.integral_rpow_mul_exp_neg_mul_Ioi hs hpos, one_div,
      Real.inv_rpow hpos' s, Real.rpow_neg hpos' s]
  -- pointwise exponential expansion
  have hpoint : ∀ v ∈ Set.Ioi (0 : ℝ),
      HasSum (fun n : ℕ => v ^ (s - 1) * Real.exp (-v) * ((x * v) ^ n / (n.factorial : ℝ)))
        (v ^ (s - 1) * Real.exp (-((1 - x) * v))) := by
    intro v _
    have hexp : HasSum (fun n : ℕ => (x * v) ^ n / (n.factorial : ℝ)) (Real.exp (x * v)) := by
      have h := NormedSpace.expSeries_div_hasSum_exp (𝔸 := ℝ) (x * v)
      simpa only [← Real.exp_eq_exp_ℝ] using h
    have := hexp.mul_left (v ^ (s - 1) * Real.exp (-v))
    have key : v ^ (s - 1) * Real.exp (-v) * Real.exp (x * v)
        = v ^ (s - 1) * Real.exp (-((1 - x) * v)) := by
      rw [mul_assoc, ← Real.exp_add]
      congr 2
      ring
    rw [key] at this
    exact this
  -- termwise integration
  have hsummable_abs : ∀ v ∈ Set.Ioi (0 : ℝ),
      Summable (fun n : ℕ => v ^ (s - 1) * Real.exp (-v) * ((|x| * v) ^ n / (n.factorial : ℝ))) := by
    intro v _
    have hexp : Summable (fun n : ℕ => (|x| * v) ^ n / (n.factorial : ℝ)) := by
      have h := NormedSpace.expSeries_div_hasSum_exp (𝔸 := ℝ) (|x| * v)
      exact h.summable
    exact hexp.mul_left _
  have htsum_bound : ∀ v ∈ Set.Ioi (0 : ℝ),
      (∑' n : ℕ, v ^ (s - 1) * Real.exp (-v) * ((|x| * v) ^ n / (n.factorial : ℝ)))
        = v ^ (s - 1) * Real.exp (-((1 - |x|) * v)) := by
    intro v hv
    have h := (hpoint v hv)
    have h' : HasSum (fun n : ℕ => v ^ (s - 1) * Real.exp (-v) * ((|x| * v) ^ n / (n.factorial : ℝ)))
        (v ^ (s - 1) * Real.exp (-((1 - |x|) * v))) := by
      have hexp : HasSum (fun n : ℕ => (|x| * v) ^ n / (n.factorial : ℝ)) (Real.exp (|x| * v)) := by
        have h2 := NormedSpace.expSeries_div_hasSum_exp (𝔸 := ℝ) (|x| * v)
        simpa only [← Real.exp_eq_exp_ℝ] using h2
      have := hexp.mul_left (v ^ (s - 1) * Real.exp (-v))
      have key : v ^ (s - 1) * Real.exp (-v) * Real.exp (|x| * v)
          = v ^ (s - 1) * Real.exp (-((1 - |x|) * v)) := by
        rw [mul_assoc, ← Real.exp_add]
        congr 2
        ring
      rw [key] at this
      exact this
    exact h'.tsum_eq
  have hbound_int : Integrable
      (fun v : ℝ => ∑' n : ℕ, v ^ (s - 1) * Real.exp (-v) * ((|x| * v) ^ n / (n.factorial : ℝ)))
      (volume.restrict (Set.Ioi 0)) := by
    have hg : IntegrableOn (fun v : ℝ => v ^ (s - 1) * Real.exp (-((1 - |x|) * v))) (Set.Ioi 0) :=
      integrableOn_rpow_mul_exp_neg_mul hs (by linarith : (0 : ℝ) < 1 - |x|)
    refine hg.congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
    exact (htsum_bound v hv).symm
  have hmain : HasSum
      (fun n : ℕ => ∫ v in Set.Ioi (0 : ℝ),
        v ^ (s - 1) * Real.exp (-v) * ((x * v) ^ n / (n.factorial : ℝ)))
      (∫ v in Set.Ioi (0 : ℝ), v ^ (s - 1) * Real.exp (-((1 - x) * v))) := by
    refine MeasureTheory.hasSum_integral_of_dominated_convergence
      (bound := fun n v => v ^ (s - 1) * Real.exp (-v) * ((|x| * v) ^ n / (n.factorial : ℝ))) ?_ ?_ ?_ ?_ ?_
    · intro n
      exact (by measurability : Measurable fun v : ℝ =>
        v ^ (s - 1) * Real.exp (-v) * ((x * v) ^ n / (n.factorial : ℝ))).aestronglyMeasurable
    · intro n
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
      have hv0 : (0 : ℝ) < v := hv
      have hpow : (0 : ℝ) ≤ v ^ (s - 1) := Real.rpow_nonneg (le_of_lt hv0) _
      have hfac : (0 : ℝ) < (n.factorial : ℝ) := by exact_mod_cast n.factorial_pos
      have hxv : |x * v| = |x| * v := by rw [abs_mul, abs_of_pos hv0]
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_div, abs_pow, hxv,
        abs_of_pos hfac, abs_of_nonneg hpow, abs_of_pos (Real.exp_pos _)]
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
      exact hsummable_abs v hv
    · exact hbound_int
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
      exact hpoint v hv
  -- evaluate the `n`-th integral
  have hFn : ∀ n : ℕ, (∫ v in Set.Ioi (0 : ℝ),
        v ^ (s - 1) * Real.exp (-v) * ((x * v) ^ n / (n.factorial : ℝ)))
      = x ^ n * (Real.Gamma (s + n) / (n.factorial : ℝ)) := by
    intro n
    have hveq : (fun v : ℝ => v ^ (s - 1) * Real.exp (-v) * ((x * v) ^ n / (n.factorial : ℝ)))
        =ᵐ[volume.restrict (Set.Ioi 0)]
        (fun v : ℝ => (x ^ n / (n.factorial : ℝ)) * (v ^ (s + n - 1) * Real.exp (-v))) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
      have hv0 : (0 : ℝ) < v := hv
      have h3 : (x * v) ^ n = x ^ n * v ^ n := by ring
      have hvpow : v ^ n = v ^ (n : ℝ) := (Real.rpow_natCast v n).symm
      have h2 : v ^ (s - 1) * v ^ (n : ℝ) = v ^ (s + n - 1) := by
        rw [← Real.rpow_add hv0]; ring_nf
      rw [h3, hvpow]
      calc v ^ (s - 1) * Real.exp (-v) * (x ^ n * v ^ (n : ℝ) / (n.factorial : ℝ))
          = v ^ (s - 1) * v ^ (n : ℝ) * Real.exp (-v) * (x ^ n / (n.factorial : ℝ)) := by
            ring
        _ = v ^ (s + n - 1) * Real.exp (-v) * (x ^ n / (n.factorial : ℝ)) := by rw [h2]
        _ = x ^ n / (n.factorial : ℝ) * (v ^ (s + n - 1) * Real.exp (-v)) := by ring
    have hII : (∫ v in Set.Ioi (0 : ℝ), v ^ (s + n - 1) * Real.exp (-v))
        = Real.Gamma (s + n) := by
      rw [Real.Gamma_eq_integral (by positivity : (0 : ℝ) < s + n)]
      congr 1 with v
      ring
    rw [MeasureTheory.integral_congr_ae hveq, MeasureTheory.integral_const_mul, hII]
    ring
  have hfin : HasSum (fun n : ℕ => x ^ n * (Real.Gamma (s + n) / (n.factorial : ℝ)))
      ((1 - x) ^ (-s) * Real.Gamma s) := by
    rw [← hInt]
    exact hmain.congr_fun (fun n => (hFn n).symm)
  have hgs : Real.Gamma s ≠ 0 := (Real.Gamma_pos_of_pos hs).ne'
  have hdiv := hfin.div_const (Real.Gamma s)
  have h1 := hdiv
  have hterm : (fun i : ℕ => x ^ i * (Real.Gamma (s + ↑i) / ↑i.factorial) / Real.Gamma s)
      = (fun n : ℕ => Real.Gamma (s + ↑n) / (Real.Gamma s * ↑n.factorial) * x ^ n) := by
    funext n
    field_simp
  rw [hterm] at h1
  rwa [show (1 - x) ^ (-s) * Real.Gamma s / Real.Gamma s = (1 - x) ^ (-s) by field_simp] at h1

/-- The weight `u ↦ u^{-1/2} (1-u)^{(r-1)/2}` is interval integrable on `[0,1]`. -/
theorem intervalIntegrable_weight (r : ℕ) (hr : 1 ≤ r) :
    IntervalIntegrable (fun u : ℝ => u ^ (-(1/2) : ℝ) * (1 - u) ^ (((r : ℝ) - 1) / 2))
      volume 0 1 := by
  have hnn : (0 : ℝ) ≤ ((r : ℝ) - 1) / 2 := by
    have hr1 : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
    linarith
  have h1 : IntervalIntegrable (fun u : ℝ => u ^ (-(1/2) : ℝ)) volume 0 1 :=
    intervalIntegral.intervalIntegrable_rpow' (by norm_num)
  have hc : Continuous fun u : ℝ => (1 - u) ^ (((r : ℝ) - 1) / 2) := by
    have := (continuous_const.sub continuous_id).rpow_const
      (fun u => Or.inr hnn : ∀ u : ℝ, (1 - u) ≠ 0 ∨ (0 : ℝ) ≤ ((r : ℝ) - 1) / 2)
    simpa using this
  have := h1.continuousOn_mul hc.continuousOn
  simpa only [mul_comm] using this
/-- The Beta moment `∫_0^1 u^{-1/2}(1-u)^{(r-1)/2} · c u^n du`. -/
theorem integral_rpow_weight (r n : ℕ) (hr : 1 ≤ r) (c : ℝ) :
    (∫ u in (0 : ℝ)..1, u ^ (-(1/2) : ℝ) * (1 - u) ^ (((r : ℝ) - 1) / 2) * (c * u ^ n))
      = c * (Real.Gamma ((n : ℝ) + 1/2) * Real.Gamma (((r : ℝ) + 1) / 2)
          / Real.Gamma ((n : ℝ) + (r : ℝ) / 2 + 1)) := by
  have hb := betaIntegral_real (a := (n : ℝ) + 1/2) (b := ((r : ℝ) + 1) / 2)
    (by positivity) (by positivity)
  have hsum : (n : ℝ) + 1/2 + ((r : ℝ) + 1) / 2 = (n : ℝ) + (r : ℝ) / 2 + 1 := by ring
  rw [hsum] at hb
  rw [intervalIntegral.integral_congr_ae
    (g := fun u : ℝ => c * (u ^ (((n : ℝ) + 1/2) - 1) * (1 - u) ^ ((((r : ℝ) + 1) / 2) - 1)))]
  · rw [intervalIntegral.integral_const_mul, hb]
  · filter_upwards with u hu
    rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hu
    have hu0 : (0 : ℝ) < u := hu.1
    have h1 : u ^ (-(1/2) : ℝ) * u ^ n = u ^ ((n : ℝ) + 1/2 - 1) := by
      rw [← Real.rpow_natCast, ← Real.rpow_add hu0]
      ring_nf
    have h2 : ((r : ℝ) + 1) / 2 - 1 = ((r : ℝ) - 1) / 2 := by ring
    rw [h2, ← h1]
    ring

/-- `ErCoeff` in terms of Gamma values. -/
theorem ErCoeff_eq_Gamma (r n : ℕ) (hr : 1 ≤ r) :
    ErCoeff r n = Real.Gamma (((r : ℝ) + 1) / 2) ^ 2 * Real.Gamma ((n : ℝ) + 1/2) ^ 2 /
      (Real.Gamma ((r : ℝ) / 2) * (Real.sqrt Real.pi) ^ 2 *
        Real.Gamma ((n : ℝ) + (r : ℝ) / 2 + 1) * (n.factorial : ℝ)) := by
  unfold ErCoeff Cr
  rw [risingFact_eq_Gamma_div (by norm_num : (0 : ℝ) < 1 / 2),
    risingFact_eq_Gamma_div (by positivity : (0 : ℝ) < (r : ℝ) / 2 + 1),
    Gamma_half_eq_sqrt_pi]
  have h1 : Real.Gamma ((r : ℝ) / 2 + 1) = ((r : ℝ) / 2) * Real.Gamma ((r : ℝ) / 2) := by
    have h := Real.Gamma_add_one (s := (r : ℝ) / 2) (by positivity : (r : ℝ) / 2 ≠ 0)
    rw [← h]
  have h2 : Real.Gamma (1 / 2 + (n : ℝ)) = Real.Gamma ((n : ℝ) + 1/2) := by
    rw [show (1 : ℝ) / 2 + (n : ℝ) = (n : ℝ) + 1/2 by ring]
  have h3 : Real.Gamma ((r : ℝ) / 2 + 1 + (n : ℝ)) = Real.Gamma ((n : ℝ) + (r : ℝ) / 2 + 1) := by
    rw [show (r : ℝ) / 2 + 1 + (n : ℝ) = (n : ℝ) + (r : ℝ) / 2 + 1 by ring]
  rw [h2, h3, h1]
  have hΓr : Real.Gamma ((r : ℝ) / 2) ≠ 0 := (Real.Gamma_pos_of_pos (by positivity)).ne'
  have hΓrn : Real.Gamma ((n : ℝ) + (r : ℝ) / 2 + 1) ≠ 0 :=
    (Real.Gamma_pos_of_pos (by positivity)).ne'
  have hfac : ((n.factorial : ℝ)) ≠ 0 := by positivity
  have hrne : ((r : ℝ)) ≠ 0 := by positivity
  have hsqrt : Real.sqrt Real.pi ≠ 0 := (Real.sqrt_pos.2 Real.pi_pos).ne'
  field_simp

/-- **Lemma 2.1, endgame**: the paper's series `E_r t` equals a Beta-type integral. -/
theorem Er_eq_betaIntegral (r : ℕ) (hr : 1 ≤ r) {t : ℝ} (ht : |t| < 1) :
    Er r t = Real.Gamma (((r : ℝ) + 1) / 2)
        / (Real.sqrt Real.pi * Real.Gamma ((r : ℝ) / 2)) *
      (t * ∫ u in (0 : ℝ)..1, u ^ (-(1/2) : ℝ) * (1 - u) ^ (((r : ℝ) - 1) / 2) *
        (1 - t ^ 2 * u) ^ (-(1/2) : ℝ)) := by
  obtain ⟨htm, htp⟩ := abs_lt.1 ht
  have ht2 : t ^ 2 < 1 := by
    nlinarith [mul_pos (by linarith : (0 : ℝ) < 1 - t) (by linarith : (0 : ℝ) < 1 + t)]
  have ht2' : |t ^ 2| < 1 := by rwa [abs_of_nonneg (sq_nonneg t)]
  have hpoint : ∀ u : ℝ, |t ^ 2 * u| < 1 →
      HasSum (fun n : ℕ => u ^ (-(1/2) : ℝ) * (1 - u) ^ (((r : ℝ) - 1) / 2) *
        (Real.Gamma ((n : ℝ) + 1/2) / (Real.sqrt Real.pi * (n.factorial : ℝ)) * (t ^ 2 * u) ^ n))
      (u ^ (-(1/2) : ℝ) * (1 - u) ^ (((r : ℝ) - 1) / 2) *
        (1 - t ^ 2 * u) ^ (-(1/2) : ℝ)) := by
    intro u hu
    have h1 := hasSum_rpow_neg_of_abs_lt_one (s := (1 / 2 : ℝ)) (by norm_num) hu
    have hterm : (fun n : ℕ =>
          Real.Gamma (1 / 2 + (n : ℝ)) / (Real.Gamma (1 / 2) * (n.factorial : ℝ)) * (t ^ 2 * u) ^ n)
        = (fun n : ℕ => Real.Gamma ((n : ℝ) + 1/2) /
            (Real.sqrt Real.pi * (n.factorial : ℝ)) * (t ^ 2 * u) ^ n) := by
      funext n
      rw [Gamma_half_eq_sqrt_pi, show (1 : ℝ) / 2 + (n : ℝ) = (n : ℝ) + 1/2 by ring]
    rw [hterm] at h1
    exact h1.mul_left _
  have hcoef : HasSum (fun n : ℕ =>
      Real.Gamma ((n : ℝ) + 1/2) / (Real.sqrt Real.pi * (n.factorial : ℝ)) * (t ^ 2) ^ n)
      ((1 - t ^ 2) ^ (-(1/2) : ℝ)) := by
    have h1 := hasSum_rpow_neg_of_abs_lt_one (s := (1 / 2 : ℝ)) (by norm_num) ht2'
    have hterm : (fun n : ℕ =>
          Real.Gamma (1 / 2 + (n : ℝ)) / (Real.Gamma (1 / 2) * (n.factorial : ℝ)) * (t ^ 2) ^ n)
        = (fun n : ℕ => Real.Gamma ((n : ℝ) + 1/2) /
            (Real.sqrt Real.pi * (n.factorial : ℝ)) * (t ^ 2) ^ n) := by
      funext n
      rw [Gamma_half_eq_sqrt_pi, show (1 : ℝ) / 2 + (n : ℝ) = (n : ℝ) + 1/2 by ring]
    rw [hterm] at h1
    exact h1
  have hsumm : Summable (fun n : ℕ =>
      Real.Gamma ((n : ℝ) + 1/2) / (Real.sqrt Real.pi * (n.factorial : ℝ)) * t ^ (2 * n)) := by
    refine hcoef.summable.congr (fun n => ?_)
    rw [show t ^ (2 * n) = (t ^ 2) ^ n by ring]
  have hweight := intervalIntegrable_weight r hr
  have hInt : HasSum
      (fun n : ℕ => ∫ u in (0 : ℝ)..1, u ^ (-(1/2) : ℝ) * (1 - u) ^ (((r : ℝ) - 1) / 2) *
        (Real.Gamma ((n : ℝ) + 1/2) / (Real.sqrt Real.pi * (n.factorial : ℝ)) * (t ^ 2 * u) ^ n))
      (∫ u in (0 : ℝ)..1, u ^ (-(1/2) : ℝ) * (1 - u) ^ (((r : ℝ) - 1) / 2) *
        (1 - t ^ 2 * u) ^ (-(1/2) : ℝ)) := by
    refine intervalIntegral.hasSum_integral_of_dominated_convergence (μ := volume)
      (a := 0) (b := 1)
      (F := fun (n : ℕ) (u : ℝ) => u ^ (-(1/2) : ℝ) * (1 - u) ^ (((r : ℝ) - 1) / 2) *
        (Real.Gamma ((n : ℝ) + 1/2) / (Real.sqrt Real.pi * (n.factorial : ℝ)) * (t ^ 2 * u) ^ n))
      (f := fun (u : ℝ) => u ^ (-(1/2) : ℝ) * (1 - u) ^ (((r : ℝ) - 1) / 2) *
        (1 - t ^ 2 * u) ^ (-(1/2) : ℝ))
      (bound := fun (n : ℕ) (u : ℝ) => u ^ (-(1/2) : ℝ) * (1 - u) ^ (((r : ℝ) - 1) / 2) *
        (Real.Gamma ((n : ℝ) + 1/2) / (Real.sqrt Real.pi * (n.factorial : ℝ)) * t ^ (2 * n)))
      ?_ ?_ ?_ ?_ ?_
    · intro n
      exact (by measurability : Measurable fun u : ℝ => u ^ (-(1/2) : ℝ) *
        (1 - u) ^ (((r : ℝ) - 1) / 2) *
        (Real.Gamma ((n : ℝ) + 1/2) / (Real.sqrt Real.pi * (n.factorial : ℝ)) *
          (t ^ 2 * u) ^ n)).aestronglyMeasurable
    · intro n
      filter_upwards with u hu
      rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hu
      obtain ⟨hu0, hu1⟩ := hu
      have hw : (0 : ℝ) ≤ u ^ (-(1/2) : ℝ) * (1 - u) ^ (((r : ℝ) - 1) / 2) := by
        apply mul_nonneg <;> apply Real.rpow_nonneg <;> linarith
      have hcn : (0 : ℝ) ≤ Real.Gamma ((n : ℝ) + 1/2) /
          (Real.sqrt Real.pi * (n.factorial : ℝ)) := by
        apply div_nonneg
        · exact (Real.Gamma_pos_of_pos (by positivity)).le
        · exact mul_nonneg (Real.sqrt_nonneg _) (by positivity)
      have hwu : |u ^ (-(1/2) : ℝ)| = u ^ (-(1/2) : ℝ) :=
        abs_of_nonneg (Real.rpow_nonneg (le_of_lt hu0) _)
      have hw1u : |(1 - u) ^ (((r : ℝ) - 1) / 2)| = (1 - u) ^ (((r : ℝ) - 1) / 2) :=
        abs_of_nonneg (Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ 1 - u) _)
      have hcn' : |Real.Gamma ((n : ℝ) + 1/2) / (Real.sqrt Real.pi * (n.factorial : ℝ))|
          = Real.Gamma ((n : ℝ) + 1/2) / (Real.sqrt Real.pi * (n.factorial : ℝ)) :=
        abs_of_nonneg hcn
      have ht2u : |t ^ 2 * u| = t ^ 2 * u := abs_of_nonneg (by positivity)
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, hwu, hw1u, hcn', abs_pow, ht2u]
      have hle : (t ^ 2 * u) ^ n ≤ t ^ (2 * n) := by
        rw [show t ^ (2 * n) = (t ^ 2) ^ n by ring]
        exact pow_le_pow_left₀ (by positivity) (by nlinarith [sq_nonneg t]) n
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hle hcn) hw
    · filter_upwards with u hu
      exact hsumm.mul_left _
    · have hfun : (fun u : ℝ => ∑' n : ℕ, u ^ (-(1/2) : ℝ) * (1 - u) ^ (((r : ℝ) - 1) / 2) *
          (Real.Gamma ((n : ℝ) + 1/2) / (Real.sqrt Real.pi * (n.factorial : ℝ)) * t ^ (2 * n)))
          = fun u : ℝ => u ^ (-(1/2) : ℝ) * (1 - u) ^ (((r : ℝ) - 1) / 2) *
            (1 - t ^ 2) ^ (-(1/2) : ℝ) := by
        funext u
        have hcoef' : (∑' n : ℕ, Real.Gamma ((n : ℝ) + 1/2) /
            (Real.sqrt Real.pi * (n.factorial : ℝ)) * t ^ (2 * n)) = (1 - t ^ 2) ^ (-(1/2) : ℝ) := by
          rw [← hcoef.tsum_eq]
          apply tsum_congr
          intro n
          rw [show t ^ (2 * n) = (t ^ 2) ^ n by ring]
        rw [← hcoef', ← tsum_mul_left]
      rw [hfun]
      exact hweight.mul_const _
    · filter_upwards with u hu
      rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hu
      obtain ⟨hu0, hu1⟩ := hu
      refine hpoint u ?_
      rw [abs_of_nonneg (by positivity)]
      have h1 : t ^ 2 * u ≤ t ^ 2 * 1 :=
        mul_le_mul_of_nonneg_left hu1 (by positivity : (0 : ℝ) ≤ t ^ 2)
      nlinarith [h1, ht2]
  have hcoef_int : ∀ n : ℕ,
      (∫ u in (0 : ℝ)..1, u ^ (-(1/2) : ℝ) * (1 - u) ^ (((r : ℝ) - 1) / 2) *
        (Real.Gamma ((n : ℝ) + 1/2) / (Real.sqrt Real.pi * (n.factorial : ℝ)) * (t ^ 2 * u) ^ n))
      = Real.Gamma ((n : ℝ) + 1/2) / (Real.sqrt Real.pi * (n.factorial : ℝ)) * t ^ (2 * n) *
          (Real.Gamma ((n : ℝ) + 1/2) * Real.Gamma (((r : ℝ) + 1) / 2)
            / Real.Gamma ((n : ℝ) + (r : ℝ) / 2 + 1)) := by
    intro n
    rw [intervalIntegral.integral_congr_ae
      (g := fun u : ℝ => u ^ (-(1/2) : ℝ) * (1 - u) ^ (((r : ℝ) - 1) / 2) *
        ((Real.Gamma ((n : ℝ) + 1/2) / (Real.sqrt Real.pi * (n.factorial : ℝ))) * t ^ (2 * n) * u ^ n))]
    · rw [integral_rpow_weight r n hr]
    · filter_upwards with u _
      ring
  have hInt' : HasSum
      (fun n : ℕ => Real.Gamma ((n : ℝ) + 1/2) / (Real.sqrt Real.pi * (n.factorial : ℝ)) *
        t ^ (2 * n) * (Real.Gamma ((n : ℝ) + 1/2) * Real.Gamma (((r : ℝ) + 1) / 2)
          / Real.Gamma ((n : ℝ) + (r : ℝ) / 2 + 1)))
      (∫ u in (0 : ℝ)..1, u ^ (-(1/2) : ℝ) * (1 - u) ^ (((r : ℝ) - 1) / 2) *
        (1 - t ^ 2 * u) ^ (-(1/2) : ℝ)) :=
    hInt.congr_fun (fun n => (hcoef_int n).symm)
  have hK := hInt'.mul_left (Real.Gamma (((r : ℝ) + 1) / 2)
    / (Real.sqrt Real.pi * Real.Gamma ((r : ℝ) / 2)) * t)
  have htermid : ∀ n : ℕ,
      (Real.Gamma (((r : ℝ) + 1) / 2) / (Real.sqrt Real.pi * Real.Gamma ((r : ℝ) / 2)) * t) *
        (Real.Gamma ((n : ℝ) + 1/2) / (Real.sqrt Real.pi * (n.factorial : ℝ)) * t ^ (2 * n) *
          (Real.Gamma ((n : ℝ) + 1/2) * Real.Gamma (((r : ℝ) + 1) / 2)
            / Real.Gamma ((n : ℝ) + (r : ℝ) / 2 + 1)))
      = ErCoeff r n * t ^ (2 * n + 1) := by
    intro n
    rw [ErCoeff_eq_Gamma r n hr]
    have hΓn : Real.Gamma ((n : ℝ) + 1/2) ≠ 0 :=
      (Real.Gamma_pos_of_pos (by positivity)).ne'
    have hΓr : Real.Gamma ((r : ℝ) / 2) ≠ 0 := (Real.Gamma_pos_of_pos (by positivity)).ne'
    have hΓrn : Real.Gamma ((n : ℝ) + (r : ℝ) / 2 + 1) ≠ 0 :=
      (Real.Gamma_pos_of_pos (by positivity)).ne'
    have hΓrh : Real.Gamma (((r : ℝ) + 1) / 2) ≠ 0 :=
      (Real.Gamma_pos_of_pos (by positivity)).ne'
    have hsqrt : Real.sqrt Real.pi ≠ 0 := (Real.sqrt_pos.2 Real.pi_pos).ne'
    have hfac : ((n.factorial : ℝ)) ≠ 0 := by positivity
    field_simp
    ring
  have hfinal : HasSum (fun n : ℕ => ErCoeff r n * t ^ (2 * n + 1))
      (Real.Gamma (((r : ℝ) + 1) / 2) / (Real.sqrt Real.pi * Real.Gamma ((r : ℝ) / 2)) *
        (t * ∫ u in (0 : ℝ)..1, u ^ (-(1/2) : ℝ) * (1 - u) ^ (((r : ℝ) - 1) / 2) *
          (1 - t ^ 2 * u) ^ (-(1/2) : ℝ))) := by
    have h := hK
    rw [show (Real.Gamma (((r : ℝ) + 1) / 2) / (Real.sqrt Real.pi * Real.Gamma ((r : ℝ) / 2)) * t)
        * (∫ u in (0 : ℝ)..1, u ^ (-(1/2) : ℝ) * (1 - u) ^ (((r : ℝ) - 1) / 2) *
          (1 - t ^ 2 * u) ^ (-(1/2) : ℝ))
        = Real.Gamma (((r : ℝ) + 1) / 2) / (Real.sqrt Real.pi * Real.Gamma ((r : ℝ) / 2)) *
          (t * ∫ u in (0 : ℝ)..1, u ^ (-(1/2) : ℝ) * (1 - u) ^ (((r : ℝ) - 1) / 2) *
            (1 - t ^ 2 * u) ^ (-(1/2) : ℝ)) by ring] at h
    exact h.congr_fun (fun n => (htermid n).symm)
  rw [Er]
  exact hfinal.tsum_eq

end Grothendieck

namespace Grothendieck

/-- **Lemma 2.1 reduced** to the evaluation of the Gaussian expectation as the Beta-type
integral of the paper. This makes explicit the only input still missing for
`matrix_grothendieck_identity`: for unit `u v` with `|u·v| < 1`,
`E[(Zu/‖Zu‖)·(Zv/‖Zv‖)] = Γ((r+1)/2)/(√π Γ(r/2)) · (u·v) · ∫_0^1 u^{-1/2}(1-u)^{(r-1)/2}(1-(u·v)²u)^{-1/2}du`.
Everything else is proved in this file. -/
theorem matrix_grothendieck_identity_of_beta
    (hbeta : ∀ (r n : ℕ), 1 ≤ r → ∀ (u v : EuclideanSpace ℝ (Fin n)), ‖u‖ = 1 → ‖v‖ = 1 →
      |inner ℝ u v| < 1 →
      grothendieckExpectation r n u v =
        Real.Gamma (((r : ℝ) + 1) / 2) / (Real.sqrt Real.pi * Real.Gamma ((r : ℝ) / 2)) *
          (inner ℝ u v * ∫ x in (0 : ℝ)..1, x ^ (-(1/2) : ℝ) *
            (1 - x) ^ (((r : ℝ) - 1) / 2) * (1 - (inner ℝ u v) ^ 2 * x) ^ (-(1/2) : ℝ)))
    (r n : ℕ) (hr : 1 ≤ r) (u v : EuclideanSpace ℝ (Fin n)) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (hne : |inner ℝ u v| < 1) :
    grothendieckExpectation r n u v = Er r (inner ℝ u v) := by
  rw [hbeta r n hr u v hu hv hne, Er_eq_betaIntegral r hr hne]

end Grothendieck

namespace Grothendieck

/-- `ErCoeff r k` is nonnegative for `r ≥ 1` (needed by any use of `Er` as a monotone series). -/
theorem ErCoeff_nonneg (r k : ℕ) (hr : 1 ≤ r) : 0 ≤ ErCoeff r k := by
  rw [ErCoeff_eq_Gamma r k hr]
  have h1 : (0 : ℝ) < Real.Gamma (((r : ℝ) + 1) / 2) := Real.Gamma_pos_of_pos (by positivity)
  have h2 : (0 : ℝ) < Real.Gamma ((k : ℝ) + 1/2) := Real.Gamma_pos_of_pos (by positivity)
  have h3 : (0 : ℝ) < Real.Gamma ((r : ℝ) / 2) := Real.Gamma_pos_of_pos (by positivity)
  have h4 : (0 : ℝ) < Real.Gamma ((k : ℝ) + (r : ℝ) / 2 + 1) := Real.Gamma_pos_of_pos (by positivity)
  have h5 : (0 : ℝ) < (Real.sqrt Real.pi) ^ 2 := by
    have := Real.sqrt_pos.2 Real.pi_pos
    positivity
  have h6 : (0 : ℝ) < (k.factorial : ℝ) := by exact_mod_cast k.factorial_pos
  positivity

/-- `Er r 0 = 0`. -/
theorem Er_zero (r : ℕ) : Er r 0 = 0 := by
  rw [Er]
  have h : ∀ k : ℕ, ErCoeff r k * (0 : ℝ) ^ (2 * k + 1) = 0 := by
    intro k
    rw [zero_pow (by omega : 2 * k + 1 ≠ 0), mul_zero]
  simp only [h]
  exact tsum_zero

/-- `Er r` is odd. -/
theorem Er_neg (r : ℕ) (t : ℝ) : Er r (-t) = -Er r t := by
  rw [Er, Er]
  rw [show (fun k : ℕ => ErCoeff r k * (-t) ^ (2 * k + 1))
      = (fun k : ℕ => -(ErCoeff r k * t ^ (2 * k + 1))) from by
    funext k
    rw [Odd.neg_pow (odd_two_mul_add_one k) t]
    ring]
  exact tsum_neg

/-- `(1/2)_k ≤ k!`. -/
theorem risingFact_half_le_factorial (k : ℕ) : risingFact (1/2) k ≤ (k.factorial : ℝ) := by
  induction k with
  | zero => simp [risingFact]
  | succ n ih =>
    have h1 : risingFact (1/2) (n + 1) = risingFact (1/2) n * (1/2 + (n : ℝ)) := by
      simp only [risingFact, Finset.prod_range_succ]
    have h2 : (0 : ℝ) ≤ risingFact (1/2) n := by
      rw [risingFact]
      exact Finset.prod_nonneg (fun i _ => by positivity)
    have h3 : (1/2 + (n : ℝ)) ≤ (n : ℝ) + 1 := by linarith
    have h4 : (0 : ℝ) ≤ (1/2 + (n : ℝ)) := by positivity
    have h5 : (0 : ℝ) ≤ ((n.factorial : ℕ) : ℝ) := by positivity
    rw [h1]
    calc risingFact (1/2) n * (1/2 + (n : ℝ))
        ≤ ((n.factorial : ℕ) : ℝ) * ((n : ℝ) + 1) := mul_le_mul ih h3 h4 h5
      _ = ((n + 1).factorial : ℝ) := by
          rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
          push_cast
          ring

/-- `(1/2)_k ≤ (r/2+1)_k` for `r ≥ 1`. -/
theorem risingFact_half_le_risingFact (r k : ℕ) (hr : 1 ≤ r) :
    risingFact (1/2) k ≤ risingFact ((r : ℝ) / 2 + 1) k := by
  rw [risingFact, risingFact]
  apply Finset.prod_le_prod
  · intro i _
    positivity
  · intro i _
    have hi : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg i
    have hr1 : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
    linarith

/-- `ErCoeff r k ≤ Cr r` for `r ≥ 1`. -/
theorem ErCoeff_le_Cr (r k : ℕ) (hr : 1 ≤ r) : ErCoeff r k ≤ Cr r := by
  have h1 := risingFact_half_le_factorial k
  have h2 := risingFact_half_le_risingFact r k hr
  have hnn : (0 : ℝ) ≤ risingFact (1/2) k := by
    rw [risingFact]
    exact Finset.prod_nonneg (fun i _ => by positivity)
  have hfac : (0 : ℝ) < (k.factorial : ℝ) := by exact_mod_cast k.factorial_pos
  have hden : (0 : ℝ) < risingFact ((r : ℝ) / 2 + 1) k * (k.factorial : ℝ) := by
    have : (0 : ℝ) < risingFact ((r : ℝ) / 2 + 1) k := by
      rw [risingFact]
      exact Finset.prod_pos (fun i _ => by positivity)
    positivity
  unfold ErCoeff
  rw [div_le_iff₀ hden]
  have hsq : risingFact (1/2) k ^ 2 ≤ risingFact ((r : ℝ) / 2 + 1) k * (k.factorial : ℝ) := by
    nlinarith [h1, h2, hnn, hfac, mul_nonneg (le_of_lt hfac) (by linarith : (0:ℝ) ≤ risingFact ((r:ℝ)/2+1) k)]
  calc Cr r * risingFact (1/2) k ^ 2
      ≤ Cr r * (risingFact ((r : ℝ) / 2 + 1) k * (k.factorial : ℝ)) := by
        have : (0:ℝ) ≤ Cr r := by
          unfold Cr
          have := Real.Gamma_pos_of_pos (by positivity : (0:ℝ) < ((r:ℝ)+1)/2)
          have := Real.Gamma_pos_of_pos (by positivity : (0:ℝ) < (r:ℝ)/2)
          positivity
        nlinarith [hsq, this]
    _ = Cr r * (risingFact ((r : ℝ) / 2 + 1) k * (k.factorial : ℝ)) := rfl

/-- Summability of the `Er` series inside the open unit interval. -/
theorem summable_ErCoeff_mul_pow (r : ℕ) (hr : 1 ≤ r) {t : ℝ} (ht : |t| < 1) :
    Summable (fun k : ℕ => ErCoeff r k * t ^ (2 * k + 1)) := by
  have htabs : |t| ^ 2 < 1 := by nlinarith [abs_nonneg t, ht]
  have hCr : (0 : ℝ) ≤ Cr r := by
    unfold Cr
    have h1 := Real.Gamma_pos_of_pos (by positivity : (0:ℝ) < ((r:ℝ)+1)/2)
    have h2 := Real.Gamma_pos_of_pos (by positivity : (0:ℝ) < (r:ℝ)/2)
    positivity
  have hgeom : Summable (fun k : ℕ => Cr r * |t| ^ (2 * k + 1)) := by
    have hg : Summable (fun k : ℕ => (|t| ^ 2) ^ k) := by
      apply summable_geometric_of_norm_lt_one
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact htabs
    have h1 : Summable (fun k : ℕ => |t| * (|t| ^ 2) ^ k) := hg.mul_left |t|
    refine (h1.mul_left (Cr r)).congr (fun k => ?_)
    rw [show |t| ^ (2 * k + 1) = |t| * (|t| ^ 2) ^ k by ring]
  refine Summable.of_norm_bounded hgeom (fun k => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (ErCoeff_nonneg r k hr), abs_pow]
  exact mul_le_mul_of_nonneg_right (ErCoeff_le_Cr r k hr) (by positivity)

end Grothendieck

namespace Grothendieck

/-- The real Beta integrand is interval integrable on `[0,1]` (norms of the complex version). -/
theorem intervalIntegrable_beta_weight (r : ℕ) (hr : 1 ≤ r) :
    IntervalIntegrable (fun u : ℝ => u ^ (-(1/2) : ℝ) * (1 - u) ^ (((r : ℝ) - 2) / 2))
      volume 0 1 := by
  set c : ℂ := ((1/2 : ℝ) : ℂ) with hc
  set d : ℂ := (((r : ℝ) / 2) : ℂ) with hd
  have hre1 : 0 < c.re := by rw [hc]; norm_num
  have hre2 : 0 < d.re := by rw [hd]; simp; exact_mod_cast hr
  have h := Complex.betaIntegral_convergent (u := c) (v := d) hre1 hre2
  have hnorm : IntervalIntegrable
      (fun x : ℝ => ‖(↑x : ℂ) ^ (c - 1) * (1 - ↑x) ^ (d - 1)‖) volume 0 1 := h.norm
  refine hnorm.congr_ae ?_
  filter_upwards [ae_restrict_mem measurableSet_uIoc, MeasureTheory.ae_restrict_of_ae (MeasureTheory.Measure.ae_ne volume (1:ℝ))]
    with x hx hx1'
  rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hx
  obtain ⟨hx0, hx1⟩ := hx
  have h0 : (0 : ℝ) < x := hx0
  have h1 : (0 : ℝ) < 1 - x := by
    rcases lt_or_eq_of_le hx1 with h | h
    · linarith
    · exact absurd h hx1'
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos h0]
  rw [show (1 : ℂ) - ↑x = ↑(1 - x) by push_cast; ring]
  rw [Complex.norm_cpow_eq_rpow_re_of_pos h1]
  have e1 : (c - 1).re = -(1/2 : ℝ) := by rw [hc]; norm_num
  have e2 : (d - 1).re = ((r : ℝ) - 2) / 2 := by rw [hd]; simp; ring
  rw [e1, e2]

/-- `(1-x)^((r-1)/2) * (1-x)^(-1/2) = (1-x)^((r-2)/2)` for `0 < 1-x`. -/
theorem rpow_half_mul_neg_half (r : ℕ) {x : ℝ} (hx : 0 < x) :
    x ^ (((r : ℝ) - 1) / 2) * x ^ (-(1/2) : ℝ) = x ^ (((r : ℝ) - 2) / 2) := by
  rw [← Real.rpow_add hx]
  congr 2
  ring

/-- The Beta weight at `t = 1`: `∫_0^1 u^{-1/2}(1-u)^{(r-2)/2} = √π Γ(r/2)/Γ((r+1)/2)`. -/
theorem integral_weight_one (r : ℕ) (hr : 1 ≤ r) :
    (∫ u in (0 : ℝ)..1, u ^ (-(1/2) : ℝ) * (1 - u) ^ (((r : ℝ) - 2) / 2))
      = Real.sqrt Real.pi * Real.Gamma ((r : ℝ) / 2) / Real.Gamma (((r : ℝ) + 1) / 2) := by
  have hb := betaIntegral_real (a := (1/2 : ℝ)) (b := (r : ℝ) / 2) (by norm_num) (by positivity)
  have e1 : ((1/2 : ℝ) - 1) = -(1/2) := by norm_num
  have e2 : ((r : ℝ) / 2 - 1) = ((r : ℝ) - 2) / 2 := by ring
  have e3 : (1/2 + (r : ℝ) / 2) = ((r : ℝ) + 1) / 2 := by ring
  rw [e1, e2, e3, Gamma_half_eq_sqrt_pi] at hb
  exact hb

/-- The Beta weight depends continuously on `t` up to `t = 1`. -/
theorem tendsto_integral_weight (r : ℕ) (hr : 1 ≤ r) :
    Tendsto (fun t : ℝ => (∫ u in (0 : ℝ)..1,
        u ^ (-(1/2) : ℝ) * (1 - u) ^ (((r : ℝ) - 1) / 2) * (1 - t ^ 2 * u) ^ (-(1/2) : ℝ)))
      (𝓝[Set.Iio (1:ℝ)] 1)
      (𝓝 (∫ u in (0 : ℝ)..1, u ^ (-(1/2) : ℝ) * (1 - u) ^ (((r : ℝ) - 2) / 2))) := by
  refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (fun u : ℝ => u ^ (-(1/2) : ℝ) * (1 - u) ^ (((r : ℝ) - 2) / 2)) ?_ ?_
    (intervalIntegrable_beta_weight r hr) ?_
  · filter_upwards with t
    exact (by measurability : Measurable fun u : ℝ =>
      u ^ (-(1/2) : ℝ) * (1 - u) ^ (((r : ℝ) - 1) / 2) * (1 - t ^ 2 * u) ^ (-(1/2) : ℝ)).aestronglyMeasurable
  · have h1 : ∀ᶠ t : ℝ in 𝓝[Set.Iio (1:ℝ)] 1, t < 1 := self_mem_nhdsWithin
    have h2 : ∀ᶠ t : ℝ in 𝓝[Set.Iio (1:ℝ)] 1, (0 : ℝ) < t :=
      eventually_nhdsWithin_of_eventually_nhds (Ioi_mem_nhds (by norm_num : (0 : ℝ) < 1))
    filter_upwards [h1, h2] with t ht ht0
    filter_upwards [MeasureTheory.Measure.ae_ne volume (1 : ℝ)] with u hune
    intro hu
    rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hu
    obtain ⟨hu0, hu1⟩ := hu
    have hlt : u < 1 := lt_of_le_of_ne hu1 hune
    have htn : t ^ 2 < 1 := by
      nlinarith [mul_pos (by linarith : (0:ℝ) < 1 - t) (by linarith : (0:ℝ) < 1 + t)]
    have ht1 : t ^ 2 ≤ 1 := le_of_lt htn
    have hu2 : t ^ 2 * u ≤ t ^ 2 * 1 := mul_le_mul_of_nonneg_left hu1 (by positivity)
    have hu3 : t ^ 2 * u ≤ u := mul_le_of_le_one_left (le_of_lt hu0) ht1
    have hpos : (0 : ℝ) < 1 - t ^ 2 * u := by nlinarith [htn, hu2]
    have hle : 1 - t ^ 2 * u ≥ 1 - u := by linarith
    have hbase : (0 : ℝ) < 1 - u := by linarith
    have hsqrt : (1 - t ^ 2 * u) ^ (-(1/2) : ℝ) ≤ (1 - u) ^ (-(1/2) : ℝ) := by
      rw [Real.rpow_neg (le_of_lt hpos), Real.rpow_neg (le_of_lt hbase), ← Real.sqrt_eq_rpow,
        ← Real.sqrt_eq_rpow, ← one_div, ← one_div]
      apply one_div_le_one_div_of_le
      · exact Real.sqrt_pos.2 hbase
      · exact Real.sqrt_le_sqrt hle
    have hnu : (0 : ℝ) ≤ u ^ (-(1/2) : ℝ) := Real.rpow_nonneg (le_of_lt hu0) _
    have hnb : (0 : ℝ) ≤ (1 - u) ^ (((r : ℝ) - 1) / 2) := Real.rpow_nonneg (le_of_lt hbase) _
    have hnc : (0 : ℝ) ≤ (1 - t ^ 2 * u) ^ (-(1/2) : ℝ) :=
      Real.rpow_nonneg (le_of_lt hpos) _
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hnu, abs_of_nonneg hnb,
      abs_of_nonneg hnc]
    calc u ^ (-(1/2) : ℝ) * (1 - u) ^ (((r : ℝ) - 1) / 2) * (1 - t ^ 2 * u) ^ (-(1/2) : ℝ)
        ≤ u ^ (-(1/2) : ℝ) * (1 - u) ^ (((r : ℝ) - 1) / 2) * (1 - u) ^ (-(1/2) : ℝ) := by
          apply mul_le_mul_of_nonneg_left hsqrt
          exact mul_nonneg hnu hnb
      _ = u ^ (-(1/2) : ℝ) * (1 - u) ^ (((r : ℝ) - 2) / 2) := by
          rw [mul_assoc, rpow_half_mul_neg_half r hbase]
  · filter_upwards [MeasureTheory.Measure.ae_ne volume (1 : ℝ)] with u hune
    intro hu_mem
    rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hu_mem
    obtain ⟨hu0, hu1le⟩ := hu_mem
    have hbase : (0 : ℝ) < 1 - u := by
      rcases lt_or_eq_of_le hu1le with h | h
      · exact sub_pos.2 h
      · exact absurd h hune
    have hcont : Filter.Tendsto (fun t : ℝ => (1 - t ^ 2 * u) ^ (-(1/2) : ℝ)) (𝓝 (1:ℝ))
        (𝓝 ((1 - u) ^ (-(1/2) : ℝ))) := by
      have hinner : Filter.Tendsto (fun t : ℝ => 1 - t ^ 2 * u) (𝓝 (1:ℝ)) (𝓝 (1 - u)) := by
        have hc : Continuous fun t : ℝ => 1 - t ^ 2 * u := by fun_prop
        simpa using hc.tendsto (1:ℝ)
      exact hinner.rpow_const (Or.inl (ne_of_gt hbase))
    have hcont' : Filter.Tendsto (fun t : ℝ => (1 - t ^ 2 * u) ^ (-(1/2) : ℝ))
        (𝓝[Set.Iio (1:ℝ)] 1) (𝓝 ((1 - u) ^ (-(1/2) : ℝ))) := hcont.mono_left inf_le_left
    have hlim := hcont'.const_mul (u ^ (-(1/2) : ℝ) * (1 - u) ^ (((r : ℝ) - 1) / 2))
    convert hlim using 1
    rw [mul_assoc, rpow_half_mul_neg_half r hbase]

/-- **The endpoint `t = 1`**: `Er r 1 = 1` for `r ≥ 1` (the case `u = v` of Lemma 2.1). -/
theorem Er_one (r : ℕ) (hr : 1 ≤ r) : Er r 1 = 1 := by
  -- abbreviations
  set K : ℝ := Real.Gamma (((r : ℝ) + 1) / 2) / (Real.sqrt Real.pi * Real.Gamma ((r : ℝ) / 2))
    with hK
  set I : ℝ → ℝ := fun t : ℝ => ∫ u in (0 : ℝ)..1,
    u ^ (-(1/2) : ℝ) * (1 - u) ^ (((r : ℝ) - 1) / 2) * (1 - t ^ 2 * u) ^ (-(1/2) : ℝ)
    with hI
  set I1 : ℝ := ∫ u in (0 : ℝ)..1, u ^ (-(1/2) : ℝ) * (1 - u) ^ (((r : ℝ) - 2) / 2) with hI1def
  have hΓ1 : Real.Gamma (((r : ℝ) + 1) / 2) ≠ 0 := (Real.Gamma_pos_of_pos (by positivity)).ne'
  have hΓ2 : Real.Gamma ((r : ℝ) / 2) ≠ 0 := (Real.Gamma_pos_of_pos (by positivity)).ne'
  have hsq : Real.sqrt Real.pi ≠ 0 := (Real.sqrt_pos.2 Real.pi_pos).ne'
  -- value of the Beta integral at `t = 1`
  have hI1val : I1 = Real.sqrt Real.pi * Real.Gamma ((r : ℝ) / 2) / Real.Gamma (((r : ℝ) + 1) / 2) :=
    integral_weight_one r hr
  -- limit of the right-hand side
  have hlimI : Tendsto I (𝓝[Set.Iio (1:ℝ)] 1) (𝓝 I1) := tendsto_integral_weight r hr
  have hlim : Tendsto (fun t : ℝ => K * (t * I t)) (𝓝[Set.Iio (1:ℝ)] 1) (𝓝 (K * (1 * I1))) := by
    have ht : Tendsto (fun t : ℝ => t) (𝓝[Set.Iio (1:ℝ)] 1) (𝓝 1) :=
      tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
    exact ((ht.mul hlimI).const_mul K)
  have hlimval : K * (1 * I1) = 1 := by
    rw [one_mul, hI1val, hK]
    field_simp
  -- (a) each partial sum is at most `1`
  have hpartial : ∀ N : ℕ, ∑ k ∈ Finset.range N, ErCoeff r k ≤ 1 := by
    intro N
    have hfinlim : Tendsto (fun t : ℝ => ∑ k ∈ Finset.range N, ErCoeff r k * t ^ (2 * k + 1))
        (𝓝[Set.Iio (1:ℝ)] 1) (𝓝 (∑ k ∈ Finset.range N, ErCoeff r k)) := by
      have hterm : ∀ k ∈ Finset.range N, Tendsto (fun t : ℝ => ErCoeff r k * t ^ (2 * k + 1))
          (𝓝[Set.Iio (1:ℝ)] 1) (𝓝 (ErCoeff r k)) := by
        intro k _
        have ht : Tendsto (fun t : ℝ => t ^ (2 * k + 1)) (𝓝[Set.Iio (1:ℝ)] 1) (𝓝 (1 ^ (2 * k + 1))) :=
          ((continuous_id.pow _).tendsto (1:ℝ)).mono_left inf_le_left
        simpa using ht.const_mul (ErCoeff r k)
      have := tendsto_finset_sum (Finset.range N) hterm
      simpa using this
    have hev : ∀ᶠ t : ℝ in 𝓝[Set.Iio (1:ℝ)] 1,
        (∑ k ∈ Finset.range N, ErCoeff r k * t ^ (2 * k + 1)) ≤ K * (t * I t) := by
      have h1 : ∀ᶠ t : ℝ in 𝓝[Set.Iio (1:ℝ)] 1, t < 1 := self_mem_nhdsWithin
      have h2 : ∀ᶠ t : ℝ in 𝓝[Set.Iio (1:ℝ)] 1, (0 : ℝ) < t :=
        eventually_nhdsWithin_of_eventually_nhds (Ioi_mem_nhds (by norm_num : (0:ℝ) < 1))
      filter_upwards [h1, h2] with t ht ht0
      have habs : |t| < 1 := by rw [abs_of_pos ht0]; exact ht
      have hEq : K * (t * I t) = Er r t := by
        simp only [hK, hI]
        exact (Er_eq_betaIntegral r hr habs).symm
      rw [hEq]
      exact (summable_ErCoeff_mul_pow r hr habs).sum_le_tsum _
        (fun i _ => mul_nonneg (ErCoeff_nonneg r i hr) (pow_nonneg (le_of_lt ht0) _))
    have := le_of_tendsto_of_tendsto hfinlim hlim hev
    rwa [hlimval] at this
  -- (b) summability of the coefficient series and `Er r 1 ≤ 1`
  have hsummable : Summable fun k : ℕ => ErCoeff r k :=
    summable_of_sum_range_le (c := 1) (fun k => ErCoeff_nonneg r k hr) hpartial
  have hEr1 : Er r 1 = ∑' k : ℕ, ErCoeff r k := by
    rw [Er]
    simp
  have hle1 : Er r 1 ≤ 1 := by
    rw [hEr1]
    exact le_of_tendsto hsummable.hasSum.tendsto_sum_nat (Eventually.of_forall hpartial)
  -- (c) the reverse inequality
  have hge1 : 1 ≤ Er r 1 := by
    have hev : ∀ᶠ t : ℝ in 𝓝[Set.Iio (1:ℝ)] 1, K * (t * I t) ≤ Er r 1 := by
      have h1 : ∀ᶠ t : ℝ in 𝓝[Set.Iio (1:ℝ)] 1, t < 1 := self_mem_nhdsWithin
      have h2 : ∀ᶠ t : ℝ in 𝓝[Set.Iio (1:ℝ)] 1, (0 : ℝ) < t :=
        eventually_nhdsWithin_of_eventually_nhds (Ioi_mem_nhds (by norm_num : (0:ℝ) < 1))
      filter_upwards [h1, h2] with t ht ht0
      have habs : |t| < 1 := by rw [abs_of_pos ht0]; exact ht
      have hEq : K * (t * I t) = Er r t := by
        simp only [hK, hI]
        exact (Er_eq_betaIntegral r hr habs).symm
      rw [hEq]
      have hs : Summable fun k : ℕ => ErCoeff r k * t ^ (2 * k + 1) :=
        summable_ErCoeff_mul_pow r hr habs
      have hs1 : Summable fun k : ℕ => ErCoeff r k * (1:ℝ) ^ (2 * k + 1) := by
        simpa using hsummable
      refine hs.tsum_le_tsum (fun k => ?_) hs1
      apply mul_le_mul_of_nonneg_left _ (ErCoeff_nonneg r k hr)
      have ht1 : t ^ 2 ≤ 1 := by nlinarith
      calc t ^ (2 * k + 1) = t * (t ^ 2) ^ k := by ring
        _ ≤ 1 * 1 := by
            exact mul_le_mul ht.le (pow_le_one₀ (sq_nonneg t) ht1) (pow_nonneg (sq_nonneg t) k)
              zero_le_one
        _ = (1:ℝ) ^ (2 * k + 1) := by ring
    have := le_of_tendsto hlim hev
    rwa [hlimval] at this
  exact le_antisymm hle1 hge1

end Grothendieck

namespace Grothendieck

/-- **The Laplace/Gamma identity of step (i)**: `∫_0^∞ s^{-1/2} e^{-A s} ds = √π/√A`, `A > 0`.
Equivalently `1/√A = π^{-1/2} ∫_0^∞ s^{-1/2} e^{-A s} ds`, the first ingredient of the
Laplace representation `1/(‖X‖‖Y‖) = π^{-1} ∫∫ (st)^{-1/2} e^{-s‖X‖²-t‖Y‖²}`. -/
theorem integral_rpow_neg_half_exp {A : ℝ} (hA : 0 < A) :
    (∫ s in Set.Ioi (0:ℝ), s ^ (-(1/2) : ℝ) * Real.exp (-(A * s)))
      = Real.sqrt Real.pi / Real.sqrt A := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := (1/2 : ℝ)) (r := A)
    (by norm_num) hA
  have e1 : (1/2 : ℝ) - 1 = -(1/2) := by norm_num
  rw [e1, Gamma_half_eq_sqrt_pi] at h
  rw [h]
  have hsA : Real.sqrt A ≠ 0 := (Real.sqrt_pos.2 hA).ne'
  have hsp : Real.sqrt Real.pi ≠ 0 := (Real.sqrt_pos.2 Real.pi_pos).ne'
  have h1 : ((1 / A : ℝ)) ^ ((1/2 : ℝ)) = (Real.sqrt A)⁻¹ := by
    rw [one_div, Real.inv_rpow hA.le, ← Real.sqrt_eq_rpow]
  rw [h1, div_eq_mul_inv]
  field_simp

end Grothendieck

/-! ### inlined: chain/PIntegral.lean -/
open MeasureTheory
open scoped BigOperators Real Topology

namespace Grothendieck

/-- **Scaling step of the `p`-integral.** For `A, B > 0`,
`∫₀^∞ (A + B p²)^{-M} dp = √(A/B) · A^{-M} · ∫₀^∞ (1 + t²)^{-M} dt`. -/
theorem integral_add_mul_sq_rpow_neg_eq {A B M : ℝ} (hA : 0 < A) (hB : 0 < B) :
    (∫ p in Set.Ioi (0:ℝ), (A + B * p ^ 2) ^ (-M))
      = Real.sqrt (A / B) * A ^ (-M) *
          ∫ t in Set.Ioi (0:ℝ), (1 + t ^ 2) ^ (-M) := by
  have hb : (0:ℝ) < Real.sqrt (A / B) := Real.sqrt_pos.mpr (div_pos hA hB)
  have hb2 : Real.sqrt (A / B) ^ 2 = A / B := Real.sq_sqrt (le_of_lt (div_pos hA hB))
  have hkey := integral_comp_mul_left_Ioi (fun p : ℝ => (A + B * p ^ 2) ^ (-M)) (0:ℝ) hb
  -- `hkey : ∫ x in Ioi 0, (A + B*(√(A/B)*x)^2)^(-M) = (√(A/B))⁻¹ • ∫ x in Ioi (√(A/B)*0), ...`
  rw [mul_zero, smul_eq_mul] at hkey
  have hpt : ∀ x : ℝ, (A + B * (Real.sqrt (A / B) * x) ^ 2) ^ (-M)
      = A ^ (-M) * (1 + x ^ 2) ^ (-M) := by
    intro x
    have hBsq : B * (Real.sqrt (A / B) * x) ^ 2 = A * x ^ 2 := by
      rw [mul_pow, hb2]; field_simp
    rw [hBsq]
    have hfac : A + A * x ^ 2 = A * (1 + x ^ 2) := by ring
    rw [hfac, Real.mul_rpow (le_of_lt hA) (by positivity)]
  simp only [hpt] at hkey
  rw [MeasureTheory.integral_const_mul] at hkey
  -- `hkey : A^(-M) * ∫ x in Ioi 0, (1+x^2)^(-M) = (√(A/B))⁻¹ * ∫ x in Ioi 0, (A + B*x^2)^(-M)`
  have hfac : Real.sqrt (A / B) * (Real.sqrt (A / B))⁻¹ = 1 := mul_inv_cancel₀ hb.ne'
  calc (∫ p in Set.Ioi (0:ℝ), (A + B * p ^ 2) ^ (-M))
      = Real.sqrt (A / B) * ((Real.sqrt (A / B))⁻¹ *
          ∫ p in Set.Ioi (0:ℝ), (A + B * p ^ 2) ^ (-M)) := by
        rw [← mul_assoc, hfac, one_mul]
    _ = Real.sqrt (A / B) * (A ^ (-M) * ∫ t in Set.Ioi (0:ℝ), (1 + t ^ 2) ^ (-M)) := by
        rw [hkey]
    _ = Real.sqrt (A / B) * A ^ (-M) * ∫ t in Set.Ioi (0:ℝ), (1 + t ^ 2) ^ (-M) := by ring

end Grothendieck

/-! ### inlined: chain/OneAddSq.lean -/
open MeasureTheory intervalIntegral
open scoped BigOperators Real Topology

namespace Grothendieck

/-- Derivative of `t ↦ t²/(1+t²)`. -/
theorem hasDerivAt_sq_div_one_add_sq (t : ℝ) :
    HasDerivAt (fun t : ℝ => t ^ 2 / (1 + t ^ 2)) (2 * t / (1 + t ^ 2) ^ 2) t := by
  have h1 : (1 + t ^ 2) ≠ 0 := by positivity
  have hnum : HasDerivAt (fun t : ℝ => t ^ 2) (2 * t) t := by
    simpa using hasDerivAt_pow 2 t
  have hden : HasDerivAt (fun t : ℝ => 1 + t ^ 2) (2 * t) t := by
    simpa using (hasDerivAt_pow 2 t).const_add 1
  refine HasDerivAt.congr_deriv (hnum.div hden h1) ?_
  field_simp
  ring

/-- **The standard `p`-integral.** For `M > 1/2`,
`∫₀^∞ (1 + t²)^{-M} dt = ½ Γ(½) Γ(M - ½)/Γ(M)`. -/
theorem integral_one_add_sq_rpow_neg {M : ℝ} (hM : 1 / 2 < M) :
    (∫ t in Set.Ioi (0:ℝ), (1 + t ^ 2) ^ (-M))
      = 1 / 2 * Real.Gamma (1 / 2) * Real.Gamma (M - 1 / 2) / Real.Gamma M := by
  -- the Beta integral, pulled back to `Ioo 0 1`
  have hb := betaIntegral_real (a := (1 / 2 : ℝ)) (b := M - 1 / 2) (by norm_num) (by linarith)
  have hb' : (∫ u in (0:ℝ)..1, u ^ (-(1 / 2) : ℝ) * (1 - u) ^ (M - 3 / 2))
      = Real.Gamma (1 / 2) * Real.Gamma (M - 1 / 2) / Real.Gamma (1 / 2 + (M - 1 / 2)) := by
    simpa only [show ((1 / 2 : ℝ) - 1) = -(1 / 2) from by norm_num,
      show ((M - 1 / 2) - 1) = M - 3 / 2 from by ring] using hb
  have hIoo : (∫ u in Set.Ioo (0:ℝ) 1, u ^ (-(1 / 2) : ℝ) * (1 - u) ^ (M - 3 / 2))
      = ∫ u in (0:ℝ)..1, u ^ (-(1 / 2) : ℝ) * (1 - u) ^ (M - 3 / 2) := by
    rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1), integral_Ioc_eq_integral_Ioo]
  have hGam : Real.Gamma (1 / 2 + (M - 1 / 2)) = Real.Gamma M := by
    congr 1
    ring
  have hbeta : (∫ u in Set.Ioo (0:ℝ) 1,
      (1 / 2 : ℝ) * u ^ (-(1 / 2) : ℝ) * (1 - u) ^ (M - 3 / 2))
      = 1 / 2 * Real.Gamma (1 / 2) * Real.Gamma (M - 1 / 2) / Real.Gamma M := by
    have hpt : ∀ u : ℝ, (1 / 2 : ℝ) * u ^ (-(1 / 2) : ℝ) * (1 - u) ^ (M - 3 / 2)
        = (1 / 2) * (u ^ (-(1 / 2) : ℝ) * (1 - u) ^ (M - 3 / 2)) := fun u => by ring
    rw [setIntegral_congr_fun measurableSet_Ioo (fun u _ => hpt u),
      MeasureTheory.integral_const_mul, hIoo, hb', hGam]
    ring
  rw [← hbeta]
  -- the substitution `t ↦ t²/(1+t²)`, which maps `(0,∞)` onto `(0,1)`
  have himg : (fun t : ℝ => t ^ 2 / (1 + t ^ 2)) '' Set.Ioi (0:ℝ) = Set.Ioo (0:ℝ) 1 := by
    ext u
    constructor
    · rintro ⟨t, ht, rfl⟩
      have ht0 : (0:ℝ) < t := ht
      have hpos : 0 < 1 + t ^ 2 := by positivity
      refine ⟨div_pos (by positivity) hpos, ?_⟩
      rw [div_lt_one hpos]
      linarith
    · rintro ⟨hu0, hu1⟩
      refine ⟨Real.sqrt (u / (1 - u)), ?_, ?_⟩
      · exact Real.sqrt_pos.mpr (div_pos hu0 (by linarith))
      · have h1 : (0:ℝ) < 1 - u := by linarith
        have hs : Real.sqrt (u / (1 - u)) ^ 2 = u / (1 - u) :=
          Real.sq_sqrt (le_of_lt (div_pos hu0 h1))
        show (Real.sqrt (u / (1 - u))) ^ 2 / (1 + (Real.sqrt (u / (1 - u))) ^ 2) = u
        rw [hs]
        field_simp
        ring
  have hinj : Set.InjOn (fun t : ℝ => t ^ 2 / (1 + t ^ 2)) (Set.Ioi (0:ℝ)) := by
    intro a ha b hb hab
    have ha0 : (0:ℝ) < a := ha
    have hb0 : (0:ℝ) < b := hb
    have hpa : 0 < 1 + a ^ 2 := by positivity
    have hpb : 0 < 1 + b ^ 2 := by positivity
    rw [div_eq_div_iff hpa.ne' hpb.ne'] at hab
    have hsq : a ^ 2 = b ^ 2 := by nlinarith
    nlinarith [ha0, hb0, hsq]

  have himgform : (∫ u in (fun t : ℝ => t ^ 2 / (1 + t ^ 2)) '' Set.Ioi (0:ℝ),
        (1 / 2 : ℝ) * u ^ (-(1 / 2) : ℝ) * (1 - u) ^ (M - 3 / 2))
      = ∫ t in Set.Ioi (0:ℝ), (1 + t ^ 2) ^ (-M) := by
    rw [integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi
      (fun t _ => (hasDerivAt_sq_div_one_add_sq t).hasDerivWithinAt) hinj]
    refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
    have ht0 : (0:ℝ) < t := ht
    have hpos : (0:ℝ) < 1 + t ^ 2 := by positivity
    have hcompl : (1 : ℝ) - t ^ 2 / (1 + t ^ 2) = 1 / (1 + t ^ 2) := by
      field_simp
      ring
    have hnum : (t ^ 2) ^ (-(1 / 2) : ℝ) = t ^ (-1 : ℝ) := by
      have h2 : t ^ 2 = t * t := by ring
      rw [h2, Real.mul_rpow (le_of_lt ht0) (le_of_lt ht0), ← Real.rpow_add ht0]
      norm_num
    have hdiv : (t ^ 2 / (1 + t ^ 2)) ^ (-(1 / 2) : ℝ) = t ^ (-1 : ℝ) * (1 + t ^ 2) ^ (1 / 2 : ℝ) := by
      rw [Real.div_rpow (le_of_lt (pow_pos ht0 2)) (le_of_lt hpos), hnum,
        Real.rpow_neg (le_of_lt hpos), div_eq_mul_inv, inv_inv]
    have hinv : (1 / (1 + t ^ 2)) ^ (M - 3 / 2) = (1 + t ^ 2) ^ (3 / 2 - M) := by
      rw [one_div, Real.inv_rpow (le_of_lt hpos), ← Real.rpow_neg (le_of_lt hpos)]
      congr 1
      ring
    have habs : |2 * t / (1 + t ^ 2) ^ 2| = 2 * t / (1 + t ^ 2) ^ 2 := by
      rw [abs_of_pos]
      positivity
    have hbase2 : ((1 + t ^ 2) ^ 2 : ℝ) = (1 + t ^ 2) ^ (2 : ℝ) := (Real.rpow_two _).symm
    have habs' : |2 * t / (1 + t ^ 2) ^ 2| = 2 * t * (1 + t ^ 2) ^ (-(2 : ℝ)) := by
      rw [abs_of_pos (by positivity : (0:ℝ) < 2 * t / (1 + t ^ 2) ^ 2), hbase2,
        Real.rpow_neg (le_of_lt hpos), Real.rpow_two, div_eq_mul_inv]
    have htne : t ≠ 0 := ne_of_gt ht0
    simp only [smul_eq_mul, habs', hcompl, hdiv, hinv]
    -- gather the powers of `1 + t ^ 2`
    have hgather : (1 + t ^ 2) ^ (-(2 : ℝ)) * ((1 + t ^ 2) ^ (1 / 2 : ℝ) * (1 + t ^ 2) ^ (3 / 2 - M))
        = (1 + t ^ 2) ^ (-M) := by
      rw [← Real.rpow_add hpos, ← Real.rpow_add hpos]
      congr 1
      ring
    have hred : 2 * t * (1 / 2 : ℝ) * t ^ (-1 : ℝ) = 1 := by
      rw [Real.rpow_neg_one]
      field_simp
    calc 2 * t * (1 + t ^ 2) ^ (-(2 : ℝ)) *
          ((1 / 2 : ℝ) * (t ^ (-1 : ℝ) * (1 + t ^ 2) ^ (1 / 2 : ℝ)) * (1 + t ^ 2) ^ (3 / 2 - M))
        = (2 * t * (1 / 2 : ℝ) * t ^ (-1 : ℝ)) *
            ((1 + t ^ 2) ^ (-(2 : ℝ)) * ((1 + t ^ 2) ^ (1 / 2 : ℝ) * (1 + t ^ 2) ^ (3 / 2 - M))) := by
          ring
      _ = 1 * (1 + t ^ 2) ^ (-M) := by rw [hred, hgather]
      _ = (1 + t ^ 2) ^ (-M) := one_mul _
  rw [himgform.symm, ← himg]

end Grothendieck

/-! ### inlined: chain/PIntegralFull.lean -/
open MeasureTheory
open scoped BigOperators Real Topology

namespace Grothendieck

/-- **The paper's `p`-integral.** For `A, B > 0` and `M > 1/2`,
`∫₀^∞ (A + B p²)^{-M} dp = A^{1/2-M} B^{-1/2} · ½ Γ(½) Γ(M-½) / Γ(M)`. -/
theorem integral_add_mul_sq_rpow_neg {A B M : ℝ} (hA : 0 < A) (hB : 0 < B) (hM : 1 / 2 < M) :
    (∫ p in Set.Ioi (0:ℝ), (A + B * p ^ 2) ^ (-M))
      = A ^ (1 / 2 - M) * B ^ (-(1 / 2) : ℝ) *
          (1 / 2 * Real.Gamma (1 / 2) * Real.Gamma (M - 1 / 2) / Real.Gamma M) := by
  rw [integral_add_mul_sq_rpow_neg_eq hA hB, integral_one_add_sq_rpow_neg hM]
  -- `√(A/B) · A^{-M} = A^{1/2-M} · B^{-1/2}`
  have hsq : Real.sqrt (A / B) = A ^ (1 / 2 : ℝ) * B ^ (-(1 / 2) : ℝ) := by
    rw [Real.sqrt_div' A (le_of_lt hB), Real.sqrt_eq_rpow, Real.sqrt_eq_rpow,
      div_eq_mul_inv, ← Real.rpow_neg (le_of_lt hB)]
  rw [hsq]
  have hcomb : A ^ (1 / 2 : ℝ) * A ^ (-M) = A ^ (1 / 2 - M) := by
    rw [← Real.rpow_add hA]
    ring_nf
  have hstep : A ^ (1 / 2 : ℝ) * B ^ (-(1 / 2) : ℝ) * A ^ (-M) *
        (1 / 2 * Real.Gamma (1 / 2) * Real.Gamma (M - 1 / 2) / Real.Gamma M)
      = (A ^ (1 / 2 : ℝ) * A ^ (-M)) * B ^ (-(1 / 2) : ℝ) *
        (1 / 2 * Real.Gamma (1 / 2) * Real.Gamma (M - 1 / 2) / Real.Gamma M) := by ring
  rw [hstep, hcomb]

end Grothendieck

/-! ### inlined: chain/QSubst.lean -/
open MeasureTheory intervalIntegral
open scoped BigOperators Real Topology

namespace Grothendieck

/-- **The `q² = x/(1-x)` substitution.** For `M > 1/2` and `|τ| < 1`,
`∫₀^∞ (1+q²)^{1/2-M} (1+(1-τ²)q²)^{-1/2} dq = ½ ∫₀^1 x^{-1/2}(1-x)^{M-3/2}(1-τ²x)^{-1/2} dx`. -/
theorem integral_sq_subst {M τ : ℝ} (hM : 1 / 2 < M) (hτ : |τ| < 1) :
    (∫ q in Set.Ioi (0:ℝ), (1 + q ^ 2) ^ (1 / 2 - M) *
        (1 + (1 - τ ^ 2) * q ^ 2) ^ (-(1 / 2) : ℝ))
      = 1 / 2 * ∫ x in Set.Ioo (0:ℝ) 1,
          x ^ (-(1 / 2) : ℝ) * (1 - x) ^ (M - 3 / 2) * (1 - τ ^ 2 * x) ^ (-(1 / 2) : ℝ) := by
  set f : ℝ → ℝ := fun q => q ^ 2 / (1 + q ^ 2) with hf
  set g : ℝ → ℝ := fun x => (1 / 2 : ℝ) * x ^ (-(1 / 2) : ℝ) * (1 - x) ^ (M - 3 / 2) *
    (1 - τ ^ 2 * x) ^ (-(1 / 2) : ℝ) with hg
  have hτ2 : τ ^ 2 < 1 := by
    have := abs_lt.mp hτ
    nlinarith
  -- range and injectivity of `f` on `(0,∞)`
  have himg : f '' Set.Ioi (0:ℝ) = Set.Ioo (0:ℝ) 1 := by
    ext x
    constructor
    · rintro ⟨q, hq, rfl⟩
      have hq0 : (0:ℝ) < q := hq
      have hpos : 0 < 1 + q ^ 2 := by positivity
      exact ⟨div_pos (by positivity) hpos, by rw [div_lt_one hpos]; linarith⟩
    · rintro ⟨hx0, hx1⟩
      refine ⟨Real.sqrt (x / (1 - x)), ?_, ?_⟩
      · exact Real.sqrt_pos.mpr (div_pos hx0 (by linarith))
      · have h1 : (0:ℝ) < 1 - x := by linarith
        have hs : Real.sqrt (x / (1 - x)) ^ 2 = x / (1 - x) :=
          Real.sq_sqrt (le_of_lt (div_pos hx0 h1))
        show (Real.sqrt (x / (1 - x))) ^ 2 / (1 + (Real.sqrt (x / (1 - x))) ^ 2) = x
        rw [hs]
        field_simp
        ring
  have hinj : Set.InjOn f (Set.Ioi (0:ℝ)) := by
    intro a ha b hb hab
    have ha0 : (0:ℝ) < a := ha
    have hb0 : (0:ℝ) < b := hb
    have hpa : (0:ℝ) < 1 + a ^ 2 := by positivity
    have hpb : (0:ℝ) < 1 + b ^ 2 := by positivity
    simp only [hf] at hab
    rw [div_eq_div_iff hpa.ne' hpb.ne'] at hab
    have hsq : a ^ 2 = b ^ 2 := by nlinarith
    nlinarith [ha0, hb0, hsq]
  -- move the constant `1/2` inside `g`
  have hR : 1 / 2 * ∫ x in Set.Ioo (0:ℝ) 1,
        x ^ (-(1 / 2) : ℝ) * (1 - x) ^ (M - 3 / 2) * (1 - τ ^ 2 * x) ^ (-(1 / 2) : ℝ)
      = ∫ x in Set.Ioo (0:ℝ) 1, g x := by
    rw [← MeasureTheory.integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioo (fun x _ => ?_)
    simp only [hg]
    ring
  rw [hR, ← himg,
    integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi
      (fun q _ => (hasDerivAt_sq_div_one_add_sq q).hasDerivWithinAt) hinj g]
  refine setIntegral_congr_fun measurableSet_Ioi (fun q hq => ?_)
  have hq0 : (0:ℝ) < q := hq
  have hpos : (0:ℝ) < 1 + q ^ 2 := by positivity
  have hB : (0:ℝ) < 1 + (1 - τ ^ 2) * q ^ 2 := by
    have h1 : 0 < 1 - τ ^ 2 := by linarith
    positivity
  have hcompl1 : (1:ℝ) - q ^ 2 / (1 + q ^ 2) = 1 / (1 + q ^ 2) := by
    field_simp
    ring
  have hcompl2 : (1:ℝ) - τ ^ 2 * (q ^ 2 / (1 + q ^ 2))
      = (1 + (1 - τ ^ 2) * q ^ 2) / (1 + q ^ 2) := by
    field_simp
    ring
  have hpow1 : (q ^ 2 / (1 + q ^ 2)) ^ (-(1/2) : ℝ) = q ^ (-1 : ℝ) * (1 + q ^ 2) ^ (1/2 : ℝ) := by
    rw [Real.div_rpow (le_of_lt (pow_pos hq0 2)) (le_of_lt hpos)]
    have hnum : (q ^ 2) ^ (-(1/2) : ℝ) = q ^ (-1 : ℝ) := by
      have h2 : q ^ 2 = q * q := by ring
      rw [h2, Real.mul_rpow (le_of_lt hq0) (le_of_lt hq0), ← Real.rpow_add hq0]
      norm_num
    rw [hnum, div_eq_mul_inv, Real.rpow_neg (le_of_lt hpos), inv_inv]
  have hpow2 : (1 / (1 + q ^ 2)) ^ (M - 3/2) = (1 + q ^ 2) ^ (3/2 - M) := by
    rw [one_div, Real.inv_rpow (le_of_lt hpos), ← Real.rpow_neg (le_of_lt hpos)]
    congr 1
    ring
  have hpow3 : ((1 + (1 - τ ^ 2) * q ^ 2) / (1 + q ^ 2)) ^ (-(1/2) : ℝ)
      = (1 + q ^ 2) ^ (1/2 : ℝ) * (1 + (1 - τ ^ 2) * q ^ 2) ^ (-(1/2) : ℝ) := by
    rw [Real.div_rpow (le_of_lt hB) (le_of_lt hpos), div_eq_mul_inv,
      Real.rpow_neg (le_of_lt hpos), inv_inv, mul_comm]
  have habs : |2 * q / (1 + q ^ 2) ^ 2| = 2 * q * (1 + q ^ 2) ^ (-(2) : ℝ) := by
    rw [abs_of_pos (by positivity : (0:ℝ) < 2 * q / (1 + q ^ 2) ^ 2), div_eq_mul_inv,
      Real.rpow_neg (le_of_lt hpos), Real.rpow_two]
  simp only [hg, smul_eq_mul, habs, hcompl1, hcompl2, hpow1, hpow2, hpow3]
  have hqq : q ^ (-1 : ℝ) * q = 1 := by
    rw [Real.rpow_neg_one]
    field_simp
  have hpow : (1 + q ^ 2) ^ (-(2) : ℝ) *
      ((1 + q ^ 2) ^ (1/2 : ℝ) * ((1 + q ^ 2) ^ (3/2 - M) * (1 + q ^ 2) ^ (1/2 : ℝ)))
      = (1 + q ^ 2) ^ (1/2 - M) := by
    rw [← Real.rpow_add hpos, ← Real.rpow_add hpos, ← Real.rpow_add hpos]
    congr 1
    ring
  have hmain : 2 * q * (1 + q ^ 2) ^ (-(2) : ℝ) *
        (1 / 2 * (q ^ (-1 : ℝ) * (1 + q ^ 2) ^ (1/2 : ℝ)) * (1 + q ^ 2) ^ (3/2 - M) *
          ((1 + q ^ 2) ^ (1/2 : ℝ) * (1 + (1 - τ ^ 2) * q ^ 2) ^ (-(1/2) : ℝ)))
      = (q ^ (-1 : ℝ) * q) * ((1 + q ^ 2) ^ (-(2) : ℝ) *
          ((1 + q ^ 2) ^ (1/2 : ℝ) * ((1 + q ^ 2) ^ (3/2 - M) * (1 + q ^ 2) ^ (1/2 : ℝ)))) *
          (1 + (1 - τ ^ 2) * q ^ 2) ^ (-(1/2) : ℝ) := by ring
  rw [hmain, hqq, hpow, one_mul]

end Grothendieck

/-! ### inlined: chain/GammaBook.lean -/
open MeasureTheory
open scoped BigOperators Real Topology

namespace Grothendieck

/-- `Γ((r+2)/2) = (r/2)·Γ(r/2)` for `r ≥ 1`. -/
theorem Gamma_half_succ (r : ℕ) (hr : 1 ≤ r) :
    Real.Gamma (((r : ℝ) + 2) / 2) = ((r : ℝ) / 2) * Real.Gamma ((r : ℝ) / 2) := by
  have hpos : (0:ℝ) < (r : ℝ) / 2 := by
    have : (1:ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
    linarith
  have harg : ((r : ℝ) + 2) / 2 = (r : ℝ) / 2 + 1 := by ring
  rw [harg, Real.Gamma_add_one (ne_of_gt hpos)]

/-- **The constant bookkeeping of Lemma 2.1.** With `M = (r+2)/2`, the prefactor
`2rτ/π · ½Γ(½)Γ(M-½)/Γ(M) · ½` equals `τ·Γ((r+1)/2)/(√π·Γ(r/2))`, the constant in the paper's
`E_r`. -/
theorem constant_bookkeeping (r : ℕ) (hr : 1 ≤ r) (τ : ℝ) :
    2 * (r : ℝ) * τ * Real.pi⁻¹ *
        (1 / 2 * Real.Gamma (1 / 2) * Real.Gamma (((r : ℝ) + 2) / 2 - 1 / 2) /
          Real.Gamma (((r : ℝ) + 2) / 2)) * (1 / 2)
      = τ * Real.Gamma (((r : ℝ) + 1) / 2) / (Real.sqrt Real.pi * Real.Gamma ((r : ℝ) / 2)) := by
  have hr1 : (1:ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hrpos : (0:ℝ) < (r : ℝ) := by linarith
  have hG : Real.Gamma (((r : ℝ) + 2) / 2) = ((r : ℝ) / 2) * Real.Gamma ((r : ℝ) / 2) :=
    Gamma_half_succ r hr
  have hhalf : Real.Gamma (1 / 2) = Real.sqrt Real.pi := Real.Gamma_one_half_eq
  have harg : ((r : ℝ) + 2) / 2 - 1 / 2 = ((r : ℝ) + 1) / 2 := by ring
  rw [harg, hG, hhalf]
  have hpi : (0:ℝ) < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
  have hg : (0:ℝ) < Real.Gamma ((r : ℝ) / 2) := Real.Gamma_pos_of_pos (by linarith)
  have hg1 : (0:ℝ) < Real.Gamma (((r : ℝ) + 1) / 2) := Real.Gamma_pos_of_pos (by linarith)
  field_simp
  rw [Real.sq_sqrt (le_of_lt Real.pi_pos)]

end Grothendieck

/-! ### inlined: chain/KernelSubstIntegrable.lean -/
set_option autoImplicit false

open MeasureTheory
open scoped BigOperators Real Topology

set_option autoImplicit false

open MeasureTheory
open scoped BigOperators Real Topology

open MeasureTheory
open scoped Real Topology ENNReal

namespace Grothendieck

noncomputable section

/-- **One-dimensional majorant.** `x ↦ (1 + x²)^{-M}` is integrable on `(0,∞)` for `M > 1/2`.

Compared with `x^{-2M}` on `(1,∞)` and bounded by `1` on `(0,1]`. -/
theorem integrableOn_one_add_sq_rpow_neg {M : ℝ} (hM : 1 / 2 < M) :
    IntegrableOn (fun x : ℝ => (1 + x ^ 2) ^ (-M)) (Set.Ioi (0 : ℝ)) := by
  have hMpos : (0:ℝ) < M := lt_trans (by norm_num) hM
  have hcont : ContinuousOn (fun x : ℝ => (1 + x ^ 2) ^ (-M)) (Set.Ioi (0 : ℝ)) :=
    (by fun_prop : ContinuousOn (fun x : ℝ => 1 + x ^ 2) (Set.Ioi (0:ℝ))).rpow_const
      (fun x _ => Or.inl (by nlinarith))
  have hcontIoc : ContinuousOn (fun x : ℝ => (1 + x ^ 2) ^ (-M)) (Set.Ioc (0:ℝ) 1) :=
    hcont.mono (fun x hx => hx.1)
  have hcontIoi : ContinuousOn (fun x : ℝ => (1 + x ^ 2) ^ (-M)) (Set.Ioi (1:ℝ)) :=
    hcont.mono (fun x hx => lt_trans (by norm_num : (0:ℝ) < 1) hx)
  have hleft : IntegrableOn (fun x : ℝ => (1 + x ^ 2) ^ (-M)) (Set.Ioc (0:ℝ) 1) := by
    have hmeas : Measurable fun x : ℝ => (1 + x ^ 2) ^ (-M) := by fun_prop
    refine Measure.integrableOn_of_bounded (M := 1) measure_Ioc_lt_top.ne
      hmeas.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    have hx0 : (0:ℝ) ≤ x := le_of_lt hx.1
    have hone : (1:ℝ) ≤ 1 + x ^ 2 := by nlinarith
    have hnonneg : (0:ℝ) < 1 + x ^ 2 := by linarith
    rw [Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hnonneg _)]
    have := Real.rpow_le_one_of_one_le_of_nonpos hone (neg_nonpos.mpr (le_of_lt hMpos))
    simpa using this
  have hright : IntegrableOn (fun x : ℝ => (1 + x ^ 2) ^ (-M)) (Set.Ioi (1:ℝ)) := by
    have hbase : IntegrableOn (fun x : ℝ => x ^ (-(2 * M))) (Set.Ioi (1:ℝ)) :=
      integrableOn_Ioi_rpow_of_lt (by linarith) one_pos
    refine Integrable.mono_nonneg hbase ?_ ?_ ?_
    · exact hcontIoi.aestronglyMeasurable measurableSet_Ioi
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      have hx1 : (1:ℝ) < x := hx
      have hpos : (0:ℝ) < 1 + x ^ 2 := by positivity
      exact le_of_lt (Real.rpow_pos_of_pos hpos _)
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      have hx1 : (1:ℝ) < x := hx
      have hx0 : (0:ℝ) < x := by linarith
      have hx2 : (0:ℝ) < x ^ 2 := by positivity
      have hle : x ^ 2 ≤ 1 + x ^ 2 := by linarith
      have hstep : (1 + x ^ 2) ^ (-M) ≤ (x ^ 2) ^ (-M) :=
        Real.rpow_le_rpow_of_nonpos hx2 hle (neg_nonpos.mpr hMpos.le)
      rw [← Real.rpow_natCast_mul (le_of_lt hx0) 2 (-M),
        show ((2:ℕ) : ℝ) * -M = -(2 * M) by push_cast; ring] at hstep
      exact hstep
  have hunion : IntegrableOn (fun x : ℝ => (1 + x ^ 2) ^ (-M)) (Set.Ioc (0:ℝ) 1 ∪ Set.Ioi (1:ℝ)) :=
    hleft.union hright
  have hset : Set.Ioc (0:ℝ) 1 ∪ Set.Ioi (1:ℝ) = Set.Ioi (0:ℝ) := by
    ext x
    constructor
    · rintro (⟨h0, _⟩ | h1)
      · exact h0
      · exact lt_trans (by norm_num : (0:ℝ) < 1) h1
    · intro hx
      rcases le_or_gt x 1 with h | h
      · exact Or.inl ⟨hx, h⟩
      · exact Or.inr h
  rwa [hset] at hunion

/-- **Separable domination for the substituted kernel.** For `M > 1/2` and `0 ≤ σ < 1` the
substituted Laplace kernel `((1+u²)(1+v²) - σ u²v²)^{-M}` is integrable on the open quadrant.

The pointwise estimate behind it is
`(1+u²)(1+v²) - σ u² v² = (1-σ)(1+u²)(1+v²) + σ(1+u²+v²) ≥ (1-σ)(1+u²)(1+v²)`,
so the kernel is dominated by `(1-σ)^{-M} g(u) g(v)` with `g(x) = (1+x²)^{-M}`. -/
theorem integrable_plane_kernel_subst_gen {M σ : ℝ} (hM : 1 / 2 < M) (hσ0 : 0 ≤ σ) (hσ1 : σ < 1) :
    Integrable (fun p : ℝ × ℝ =>
      ((1 + p.1 ^ 2) * (1 + p.2 ^ 2) - σ * p.1 ^ 2 * p.2 ^ 2) ^ (-M)) planeMeasure := by
  have hMpos : (0 : ℝ) < M := lt_trans (by norm_num) hM
  have ht2 : (0 : ℝ) < 1 - σ := by linarith
  -- the one-dimensional majorant is integrable, hence so is the product majorant
  have hg : Integrable (fun x : ℝ => (1 + x ^ 2) ^ (-M)) (volume.restrict (Set.Ioi (0:ℝ))) :=
    integrableOn_one_add_sq_rpow_neg hM
  have hB : Integrable (fun p : ℝ × ℝ => (1 - σ) ^ (-M) *
      ((1 + p.1 ^ 2) ^ (-M) * (1 + p.2 ^ 2) ^ (-M))) planeMeasure := by
    have h := (hg.mul_prod hg).const_mul ((1 - σ) ^ (-M))
    simpa [planeMeasure] using h
  -- almost every point of `planeMeasure` lies in the open quadrant
  have hae : ∀ᵐ p ∂planeMeasure, 0 < p.1 ∧ 0 < p.2 := by
    rw [planeMeasure, Measure.prod_restrict]
    filter_upwards [ae_restrict_mem (measurableSet_Ioi.prod measurableSet_Ioi)] with p hp
    exact hp
  have hmeas : AEStronglyMeasurable (fun p : ℝ × ℝ =>
      ((1 + p.1 ^ 2) * (1 + p.2 ^ 2) - σ * p.1 ^ 2 * p.2 ^ 2) ^ (-M)) planeMeasure := by
    refine Measurable.aestronglyMeasurable ?_
    fun_prop
  refine Integrable.mono' hB hmeas ?_
  filter_upwards [hae] with p hp
  have hp1 : (0:ℝ) < p.1 := hp.1
  have hp2 : (0:ℝ) < p.2 := hp.2
  have ha : (0:ℝ) ≤ p.1 ^ 2 := sq_nonneg p.1
  have hb : (0:ℝ) ≤ p.2 ^ 2 := sq_nonneg p.2
  have h1a : (0:ℝ) < 1 + p.1 ^ 2 := by linarith
  have h1b : (0:ℝ) < 1 + p.2 ^ 2 := by linarith
  have hkey : (1 + p.1 ^ 2) * (1 + p.2 ^ 2) - σ * p.1 ^ 2 * p.2 ^ 2
      = (1 - σ) * (1 + p.1 ^ 2) * (1 + p.2 ^ 2) + σ * (1 + p.1 ^ 2 + p.2 ^ 2) := by
    ring
  have hKge : (1 - σ) * (1 + p.1 ^ 2) * (1 + p.2 ^ 2) ≤
      (1 + p.1 ^ 2) * (1 + p.2 ^ 2) - σ * p.1 ^ 2 * p.2 ^ 2 := by
    rw [hkey]
    nlinarith
  have hApos : (0:ℝ) < (1 - σ) * (1 + p.1 ^ 2) * (1 + p.2 ^ 2) :=
    mul_pos (mul_pos ht2 h1a) h1b
  have hKpos : (0:ℝ) < (1 + p.1 ^ 2) * (1 + p.2 ^ 2) - σ * p.1 ^ 2 * p.2 ^ 2 :=
    lt_of_lt_of_le hApos hKge
  have hpow_le : ((1 + p.1 ^ 2) * (1 + p.2 ^ 2) - σ * p.1 ^ 2 * p.2 ^ 2) ^ (-M) ≤
      ((1 - σ) * (1 + p.1 ^ 2) * (1 + p.2 ^ 2)) ^ (-M) :=
    Real.rpow_le_rpow_of_nonpos hApos hKge (neg_nonpos.mpr hMpos.le)
  have hpow_split : ((1 - σ) * (1 + p.1 ^ 2) * (1 + p.2 ^ 2)) ^ (-M)
      = (1 - σ) ^ (-M) * ((1 + p.1 ^ 2) ^ (-M) * (1 + p.2 ^ 2) ^ (-M)) := by
    rw [Real.mul_rpow (le_of_lt (mul_pos ht2 h1a)) (le_of_lt h1b),
      Real.mul_rpow (le_of_lt ht2) (le_of_lt h1a)]
    ring
  have hnorm : ‖((1 + p.1 ^ 2) * (1 + p.2 ^ 2) - σ * p.1 ^ 2 * p.2 ^ 2) ^ (-M)‖
      = ((1 + p.1 ^ 2) * (1 + p.2 ^ 2) - σ * p.1 ^ 2 * p.2 ^ 2) ^ (-M) := by
    rw [Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hKpos _)]
  rw [hnorm]
  calc ((1 + p.1 ^ 2) * (1 + p.2 ^ 2) - σ * p.1 ^ 2 * p.2 ^ 2) ^ (-M)
      ≤ ((1 - σ) * (1 + p.1 ^ 2) * (1 + p.2 ^ 2)) ^ (-M) := hpow_le
    _ = (1 - σ) ^ (-M) * ((1 + p.1 ^ 2) ^ (-M) * (1 + p.2 ^ 2) ^ (-M)) := hpow_split

/-- **The target.** The substituted Laplace kernel of Lemma 2.1 is integrable on the open
quadrant: for `r ≥ 2` and `τ² < 1`,

`p ↦ ((1 + p.1²)(1 + p.2²) - τ² p.1² p.2²) ^ (-((r+2)/2))`

is integrable for `Grothendieck.planeMeasure`. -/
theorem integrable_kernel_subst (r : ℕ) (hr : 2 ≤ r) {τ : ℝ} (hτ : τ ^ 2 < 1) :
    Integrable (fun p : ℝ × ℝ =>
      ((1 + p.1 ^ 2) * (1 + p.2 ^ 2) - τ ^ 2 * p.1 ^ 2 * p.2 ^ 2) ^
        (-(((r : ℝ) + 2) / 2) : ℝ)) planeMeasure := by
  have hr2 : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hM : (1 : ℝ) / 2 < ((r : ℝ) + 2) / 2 := by linarith
  exact integrable_plane_kernel_subst_gen (M := ((r : ℝ) + 2) / 2) (σ := τ ^ 2) hM
    (sq_nonneg τ) hτ

end

end Grothendieck

/-! ### inlined: chain/Step5.lean -/
open MeasureTheory
open scoped BigOperators Real Topology

namespace Grothendieck

/-- The algebraic identity behind the `v`-integral: for `u, v : ℝ`,
`(1+u²)(1+v²) - τ²u²v² = (1+u²) + v²((1+u²) - τ²u²)`. -/
theorem kernel_factor (u v τ : ℝ) :
    (1 + u ^ 2) * (1 + v ^ 2) - τ ^ 2 * u ^ 2 * v ^ 2
      = (1 + u ^ 2) + ((1 + u ^ 2) - τ ^ 2 * u ^ 2) * v ^ 2 := by
  ring

/-- **Step 5 of Lemma 2.1: the `v`-integral.** For `r ≥ 2` and `|τ| < 1`, the inner integral over `v`
of the kernel equals the Beta factor times `A^{1/2-M}B^{-1/2}`. -/
theorem integral_kernel_inner (r : ℕ) (hr : 2 ≤ r) {τ : ℝ} (hτ : τ ^ 2 < 1) (u : ℝ) :
    (∫ v in Set.Ioi (0:ℝ),
        ((1 + u ^ 2) * (1 + v ^ 2) - τ ^ 2 * u ^ 2 * v ^ 2) ^ (-(((r : ℝ) + 2) / 2) : ℝ))
      = (1 + u ^ 2) ^ (1 / 2 - ((r : ℝ) + 2) / 2) *
          (1 + (1 - τ ^ 2) * u ^ 2) ^ (-(1 / 2) : ℝ) *
          (1 / 2 * Real.Gamma (1 / 2) * Real.Gamma (((r : ℝ) + 2) / 2 - 1 / 2) /
            Real.Gamma (((r : ℝ) + 2) / 2)) := by
  have hu : (0:ℝ) < 1 + u ^ 2 := by positivity
  have hτ2 : (0:ℝ) < 1 - τ ^ 2 := by linarith
  have hB : (0:ℝ) < 1 + (1 - τ ^ 2) * u ^ 2 := by positivity
  have hM : (1/2 : ℝ) < ((r : ℝ) + 2) / 2 := by
    have : (2:ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
    linarith
  have key := integral_add_mul_sq_rpow_neg (A := 1 + u ^ 2) (B := 1 + (1 - τ ^ 2) * u ^ 2)
    (M := ((r : ℝ) + 2) / 2) hu hB hM
  -- rewrite the integrand into the `(A + B v²)^{-M}` shape
  have hcongr : ∀ v ∈ Set.Ioi (0:ℝ),
      ((1 + u ^ 2) * (1 + v ^ 2) - τ ^ 2 * u ^ 2 * v ^ 2) ^ (-(((r : ℝ) + 2) / 2) : ℝ)
        = ((1 + u ^ 2) + (1 + (1 - τ ^ 2) * u ^ 2) * v ^ 2) ^ (-(((r : ℝ) + 2) / 2) : ℝ) := by
    intro v _
    have hbase : (1 + u ^ 2) * (1 + v ^ 2) - τ ^ 2 * u ^ 2 * v ^ 2
        = (1 + u ^ 2) + (1 + (1 - τ ^ 2) * u ^ 2) * v ^ 2 := by ring
    rw [hbase]
  rw [setIntegral_congr_fun measurableSet_Ioi hcongr, key]

end Grothendieck

/-! ### inlined: chain/SqSubstProved.lean -/
set_option autoImplicit false

open MeasureTheory
open scoped BigOperators Real Topology ENNReal

set_option autoImplicit false

open MeasureTheory
open scoped BigOperators Real Topology ENNReal

set_option autoImplicit false

open MeasureTheory
open scoped BigOperators Real Topology

set_option autoImplicit false

open MeasureTheory
open scoped BigOperators Real Topology

set_option autoImplicit false

open MeasureTheory
open scoped BigOperators Real Topology

namespace Grothendieck

instance : SFinite planeMeasure := by unfold planeMeasure; infer_instance

instance (r : ℕ) (τ : ℝ) : SFinite (reducedLaw r τ) := by
  unfold reducedLaw
  infer_instance

end Grothendieck

set_option autoImplicit false

open MeasureTheory
open scoped BigOperators Real Topology

open MeasureTheory
open scoped BigOperators Real Topology

namespace Grothendieck

/-- The one-dimensional Laplace identity `∫_0^∞ u^{-1/2} e^{-Cu} du = √π/√C`. -/
theorem integral_rpow_neg_half_exp_mul {C : ℝ} (hC : 0 < C) :
    (∫ u in Set.Ioi (0:ℝ), u ^ (-(1/2) : ℝ) * Real.exp (-(C * u)))
      = Real.sqrt Real.pi / Real.sqrt C := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := (1/2:ℝ)) (r := C) (by norm_num) hC
  have h1 : ((1/2:ℝ) - 1) = -(1/2) := by norm_num
  rw [h1, Real.Gamma_one_half_eq] at h
  rw [h, Real.sqrt_eq_rpow, Real.sqrt_eq_rpow,
    Real.div_rpow zero_le_one (le_of_lt hC), Real.one_rpow, one_div, div_eq_mul_inv]
  ring_nf

/-- **The Laplace step.** For `A, B > 0`,
`1/(√A √B) = π⁻¹ ∫∫_{(0,∞)²} (st)^{-1/2} e^{-(sA+tB)} ds dt`. -/
theorem laplace_inv_sqrt_mul_inv_sqrt {A B : ℝ} (hA : 0 < A) (hB : 0 < B) :
    (Real.sqrt A * Real.sqrt B)⁻¹
      = Real.pi⁻¹ * ∫ s in Set.Ioi (0:ℝ), ∫ t in Set.Ioi (0:ℝ),
          (s * t) ^ (-(1/2) : ℝ) * Real.exp (-(s * A + t * B)) := by
  have hI : ∀ C : ℝ, 0 < C →
      (∫ u in Set.Ioi (0:ℝ), u ^ (-(1/2) : ℝ) * Real.exp (-(C * u)))
        = Real.sqrt Real.pi / Real.sqrt C := fun C hC => integral_rpow_neg_half_exp_mul hC
  have hinner : ∀ s ∈ Set.Ioi (0:ℝ),
      (∫ t in Set.Ioi (0:ℝ), (s * t) ^ (-(1/2) : ℝ) * Real.exp (-(s * A + t * B)))
        = (s ^ (-(1/2) : ℝ) * Real.exp (-(A * s))) * (Real.sqrt Real.pi / Real.sqrt B) := by
    intro s hs
    have hs0 : (0:ℝ) < s := hs
    have hpt : ∀ t ∈ Set.Ioi (0:ℝ),
        (s * t) ^ (-(1/2) : ℝ) * Real.exp (-(s * A + t * B))
          = (s ^ (-(1/2) : ℝ) * Real.exp (-(A * s))) * (t ^ (-(1/2) : ℝ) * Real.exp (-(B * t))) := by
      intro t ht
      have ht0 : (0:ℝ) < t := ht
      have e1 : -(s * A + t * B) = -(A * s) + -(B * t) := by ring
      rw [Real.mul_rpow (le_of_lt hs0) (le_of_lt ht0), e1, Real.exp_add]
      ring
    rw [setIntegral_congr_fun measurableSet_Ioi hpt, MeasureTheory.integral_const_mul, hI B hB]
  rw [setIntegral_congr_fun measurableSet_Ioi hinner, MeasureTheory.integral_mul_const, hI A hA]
  have hsq : Real.sqrt Real.pi * Real.sqrt Real.pi = Real.pi := by
    rw [← sq, Real.sq_sqrt (le_of_lt Real.pi_pos)]
  have hp : Real.sqrt Real.pi ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr Real.pi_pos)
  have hA0 : Real.sqrt A ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hA)
  have hB0 : Real.sqrt B ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hB)
  field_simp
  rw [Real.sq_sqrt (le_of_lt Real.pi_pos)]

end Grothendieck

open MeasureTheory
open scoped BigOperators Real

namespace Grothendieck

/-- The reduced integrand as a ratio: `reducedIntegrand r W = ⟨X,Y⟩/(‖X‖‖Y‖)` with `X`, `Y` the two
columns of `W`. -/
theorem reducedIntegrand_eq_inner_div (r : ℕ) (W : Fin r → EuclideanSpace ℝ (Fin 2)) :
    reducedIntegrand r W
      = inner ℝ (colFun r 0 W) (colFun r 1 W)
        * (‖colFun r 0 W‖ * ‖colFun r 1 W‖)⁻¹ := by
  unfold reducedIntegrand normalize
  rw [inner_smul_left, inner_smul_right]
  simp only [conj_trivial, RCLike.real_smul_eq_coe_smul, smul_eq_mul]
  ring

end Grothendieck

open MeasureTheory
open scoped BigOperators Real Topology

namespace Grothendieck

/-- **The Laplace form of the rounding integrand.** Away from the null set where a column vanishes,
the integrand of Lemma 2.1 equals `π⁻¹` times the inner product times the double Laplace integral of
`exp(-(s‖X‖² + t‖Y‖²))`. -/
theorem reducedIntegrand_eq_pi_inv_mul_integral (r : ℕ) (W : Fin r → EuclideanSpace ℝ (Fin 2))
    (hX : colFun r 0 W ≠ 0) (hY : colFun r 1 W ≠ 0) :
    reducedIntegrand r W
      = Real.pi⁻¹ * (inner ℝ (colFun r 0 W) (colFun r 1 W) *
          ∫ s in Set.Ioi (0:ℝ), ∫ t in Set.Ioi (0:ℝ),
            (s * t) ^ (-(1/2) : ℝ) *
              Real.exp (-(s * ‖colFun r 0 W‖ ^ 2 + t * ‖colFun r 1 W‖ ^ 2))) := by
  rw [reducedIntegrand_eq_inner_div]
  have hA : (0:ℝ) < ‖colFun r 0 W‖ ^ 2 := by positivity
  have hB : (0:ℝ) < ‖colFun r 1 W‖ ^ 2 := by positivity
  have hden : (‖colFun r 0 W‖ * ‖colFun r 1 W‖)⁻¹
      = (Real.sqrt (‖colFun r 0 W‖ ^ 2) * Real.sqrt (‖colFun r 1 W‖ ^ 2))⁻¹ := by
    rw [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)]
  rw [hden, laplace_inv_sqrt_mul_inv_sqrt hA hB]
  ring

end Grothendieck

open MeasureTheory
open scoped BigOperators Real Topology

namespace Grothendieck

/-- **The Laplace form of the rounding integrand, unconditionally.** Lean's convention `(0)⁻¹ = 0`
makes both sides vanish when a column vanishes, so no hypothesis is needed. -/
theorem reducedIntegrand_eq_pi_inv_mul_integral_all (r : ℕ)
    (W : Fin r → EuclideanSpace ℝ (Fin 2)) :
    reducedIntegrand r W
      = Real.pi⁻¹ * (inner ℝ (colFun r 0 W) (colFun r 1 W) *
          ∫ s in Set.Ioi (0:ℝ), ∫ t in Set.Ioi (0:ℝ),
            (s * t) ^ (-(1/2) : ℝ) *
              Real.exp (-(s * ‖colFun r 0 W‖ ^ 2 + t * ‖colFun r 1 W‖ ^ 2))) := by
  by_cases hX : colFun r 0 W = 0
  · have hinner : inner ℝ (colFun r 0 W) (colFun r 1 W) = 0 := by simp [hX]
    rw [hinner]
    simp [reducedIntegrand, normalize, hX]
  · by_cases hY : colFun r 1 W = 0
    · have hinner : inner ℝ (colFun r 0 W) (colFun r 1 W) = 0 := by simp [hY]
      rw [hinner]
      simp [reducedIntegrand, normalize, hY]
    · exact reducedIntegrand_eq_pi_inv_mul_integral r W hX hY

end Grothendieck

open MeasureTheory
open scoped BigOperators Real Topology

namespace Grothendieck

/-- **The Fubini majorant.** For a nonzero pair of columns, `‖X‖‖Y‖` times the double Laplace
integral of `e^{-(s‖X‖²+t‖Y‖²)}` is exactly `π`. -/
theorem laplace_integral_mul_norm_eq_pi {r : ℕ} (W : Fin r → EuclideanSpace ℝ (Fin 2))
    (hX : colFun r 0 W ≠ 0) (hY : colFun r 1 W ≠ 0) :
    (‖colFun r 0 W‖ * ‖colFun r 1 W‖) *
        (∫ s in Set.Ioi (0:ℝ), ∫ t in Set.Ioi (0:ℝ),
          (s * t) ^ (-(1/2) : ℝ) *
            Real.exp (-(s * ‖colFun r 0 W‖ ^ 2 + t * ‖colFun r 1 W‖ ^ 2)))
      = Real.pi := by
  have hA : (0:ℝ) < ‖colFun r 0 W‖ ^ 2 := by positivity
  have hB : (0:ℝ) < ‖colFun r 1 W‖ ^ 2 := by positivity
  have hden : (Real.sqrt (‖colFun r 0 W‖ ^ 2) * Real.sqrt (‖colFun r 1 W‖ ^ 2))⁻¹
      = (‖colFun r 0 W‖ * ‖colFun r 1 W‖)⁻¹ := by
    rw [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)]
  have hpi := laplace_inv_sqrt_mul_inv_sqrt hA hB
  rw [hden] at hpi
  have hpos : (0:ℝ) < ‖colFun r 0 W‖ * ‖colFun r 1 W‖ :=
    mul_pos (norm_pos_iff.mpr hX) (norm_pos_iff.mpr hY)
  field_simp at hpi ⊢
  linarith [hpi]

end Grothendieck

open MeasureTheory
open scoped BigOperators Real Topology ENNReal

namespace Grothendieck

noncomputable def fubiniFactor (r : ℕ) (W : Fin r → EuclideanSpace ℝ (Fin 2))
    (p : ℝ × ℝ) : ℝ :=
  (p.1 * p.2) ^ (-(1/2) : ℝ) *
    Real.exp (-(p.1 * ‖colFun r 0 W‖ ^ 2 + p.2 * ‖colFun r 1 W‖ ^ 2))

lemma fubiniFactor_apply (r : ℕ) (W : Fin r → EuclideanSpace ℝ (Fin 2)) (s t : ℝ) :
    fubiniFactor r W (s, t) = (s * t) ^ (-(1/2) : ℝ) *
      Real.exp (-(s * ‖colFun r 0 W‖ ^ 2 + t * ‖colFun r 1 W‖ ^ 2)) := rfl

lemma fubiniIntegrand_eq_mul (r : ℕ) (W : Fin r → EuclideanSpace ℝ (Fin 2)) (p : ℝ × ℝ) :
    fubiniIntegrand r W p = inner ℝ (colFun r 0 W) (colFun r 1 W) * fubiniFactor r W p := rfl

lemma integrable_fubiniFactor_of_ne_zero (r : ℕ) {W : Fin r → EuclideanSpace ℝ (Fin 2)}
    (hc : inner ℝ (colFun r 0 W) (colFun r 1 W) ≠ 0)
    (hW : Integrable (fun p => fubiniIntegrand r W p) planeMeasure) :
    Integrable (fubiniFactor r W) planeMeasure := by
  have h1 : Integrable (fun p => (inner ℝ (colFun r 0 W) (colFun r 1 W))⁻¹ *
      fubiniIntegrand r W p) planeMeasure := hW.const_mul _
  refine h1.congr ?_
  filter_upwards with p
  rw [fubiniIntegrand_eq_mul]
  field_simp

theorem integral_fubiniIntegrand_eq_mul (r : ℕ) (W : Fin r → EuclideanSpace ℝ (Fin 2))
    (hW : Integrable (fun p => fubiniIntegrand r W p) planeMeasure) :
    ∫ p, fubiniIntegrand r W p ∂planeMeasure
      = inner ℝ (colFun r 0 W) (colFun r 1 W) *
          ∫ s in Set.Ioi (0:ℝ), ∫ t in Set.Ioi (0:ℝ),
            (s * t) ^ (-(1/2) : ℝ) *
              Real.exp (-(s * ‖colFun r 0 W‖ ^ 2 + t * ‖colFun r 1 W‖ ^ 2)) := by
  by_cases hc : inner ℝ (colFun r 0 W) (colFun r 1 W) = 0
  · have hzero : ∀ p, fubiniIntegrand r W p = 0 := by
      intro p
      rw [fubiniIntegrand_eq_mul, hc, zero_mul]
    rw [hc, zero_mul]
    simp [hzero]
  · have hg : Integrable (fubiniFactor r W) planeMeasure :=
      integrable_fubiniFactor_of_ne_zero r hc hW
    have hprod : ∫ p, fubiniFactor r W p ∂planeMeasure
        = ∫ s in Set.Ioi (0:ℝ), ∫ t in Set.Ioi (0:ℝ),
            (s * t) ^ (-(1/2) : ℝ) *
              Real.exp (-(s * ‖colFun r 0 W‖ ^ 2 + t * ‖colFun r 1 W‖ ^ 2)) := by
      rw [planeMeasure] at hg ⊢
      rw [integral_prod (f := fubiniFactor r W) hg]
      simp [fubiniFactor_apply]
    calc ∫ p, fubiniIntegrand r W p ∂planeMeasure
        = ∫ p, inner ℝ (colFun r 0 W) (colFun r 1 W) * fubiniFactor r W p ∂planeMeasure := by
          simp [fubiniIntegrand_eq_mul]
      _ = inner ℝ (colFun r 0 W) (colFun r 1 W) * ∫ p, fubiniFactor r W p ∂planeMeasure :=
          MeasureTheory.integral_const_mul _ _
      _ = _ := by rw [hprod]

theorem reducedIntegrand_eq_pi_inv_mul_integral_section (r : ℕ)
    (W : Fin r → EuclideanSpace ℝ (Fin 2))
    (hW : Integrable (fun p => fubiniIntegrand r W p) planeMeasure) :
    reducedIntegrand r W = Real.pi⁻¹ * ∫ p, fubiniIntegrand r W p ∂planeMeasure := by
  rw [reducedIntegrand_eq_pi_inv_mul_integral_all, integral_fubiniIntegrand_eq_mul r W hW]

theorem fubini_swap_of_integrable (r : ℕ) {τ : ℝ}
    (hInt : Integrable (Function.uncurry (fubiniIntegrand r))
      ((reducedLaw r τ).prod planeMeasure)) :
    (∫ W, reducedIntegrand r W ∂(reducedLaw r τ))
      = Real.pi⁻¹ * ∫ p, (∫ W, fubiniIntegrand r W p ∂(reducedLaw r τ)) ∂planeMeasure := by
  have hsec : ∀ᵐ W ∂(reducedLaw r τ),
      Integrable (fun p => fubiniIntegrand r W p) planeMeasure :=
    hInt.prod_right_ae
  have hpoint : ∀ᵐ W ∂(reducedLaw r τ), reducedIntegrand r W
      = Real.pi⁻¹ * ∫ p, fubiniIntegrand r W p ∂planeMeasure := by
    filter_upwards [hsec] with W hW
    exact reducedIntegrand_eq_pi_inv_mul_integral_section r W hW
  calc ∫ W, reducedIntegrand r W ∂(reducedLaw r τ)
      = ∫ W, Real.pi⁻¹ * (∫ p, fubiniIntegrand r W p ∂planeMeasure)
          ∂(reducedLaw r τ) := integral_congr_ae hpoint
    _ = Real.pi⁻¹ * ∫ W, (∫ p, fubiniIntegrand r W p ∂planeMeasure)
          ∂(reducedLaw r τ) := MeasureTheory.integral_const_mul _ _
    _ = Real.pi⁻¹ * ∫ p, (∫ W, fubiniIntegrand r W p ∂(reducedLaw r τ))
          ∂planeMeasure := by
        rw [integral_integral_swap hInt]

theorem measurable_colFun_apply (r : ℕ) (j : Fin 2) :
    Measurable (fun W : Fin r → EuclideanSpace ℝ (Fin 2) => colFun r j W) := by
  have hf : Measurable (fun x : EuclideanSpace ℝ (Fin 2) => x.ofLp j) := by
    have h : Measurable (WithLp.ofLp : EuclideanSpace ℝ (Fin 2) → (Fin 2 → ℝ)) :=
      WithLp.measurable_ofLp (p := 2) (X := Fin 2 → ℝ)
    exact (measurable_pi_apply j).comp h
  unfold colFun
  refine (WithLp.measurable_toLp 2 (Fin r → ℝ)).comp ?_
  exact measurable_pi_iff.mpr fun i => hf.comp (measurable_pi_apply i)

theorem measurable_uncurry_fubiniIntegrand (r : ℕ) :
    Measurable (Function.uncurry (fubiniIntegrand r)) := by
  have h0 : Measurable (fun a : (Fin r → EuclideanSpace ℝ (Fin 2)) × (ℝ × ℝ) =>
      colFun r 0 a.1) := (measurable_colFun_apply r 0).comp measurable_fst
  have h1 : Measurable (fun a : (Fin r → EuclideanSpace ℝ (Fin 2)) × (ℝ × ℝ) =>
      colFun r 1 a.1) := (measurable_colFun_apply r 1).comp measurable_fst
  unfold fubiniIntegrand Function.uncurry
  measurability

theorem integrable_fubiniIntegrand_of_bound (r : ℕ) {τ : ℝ}
    (hmeas : AEStronglyMeasurable (Function.uncurry (fubiniIntegrand r))
      ((reducedLaw r τ).prod planeMeasure))
    (hbound : (∫⁻ z, ENNReal.ofReal ‖Function.uncurry (fubiniIntegrand r) z‖
        ∂((reducedLaw r τ).prod planeMeasure)) ≤ ENNReal.ofReal Real.pi) :
    Integrable (Function.uncurry (fubiniIntegrand r)) ((reducedLaw r τ).prod planeMeasure) := by
  refine ⟨hmeas, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  have hpi : ENNReal.ofReal Real.pi < (⊤ : ENNReal) := ENNReal.ofReal_lt_top
  refine lt_of_le_of_lt ?_ hpi
  simpa only [ofReal_norm] using hbound

theorem fubini_swap_of_bound (r : ℕ) {τ : ℝ}
    (hmeas : AEStronglyMeasurable (Function.uncurry (fubiniIntegrand r))
      ((reducedLaw r τ).prod planeMeasure))
    (hbound : (∫⁻ z, ENNReal.ofReal ‖Function.uncurry (fubiniIntegrand r) z‖
        ∂((reducedLaw r τ).prod planeMeasure)) ≤ ENNReal.ofReal Real.pi) :
    (∫ W, reducedIntegrand r W ∂(reducedLaw r τ))
      = Real.pi⁻¹ * ∫ p, (∫ W, fubiniIntegrand r W p ∂(reducedLaw r τ)) ∂planeMeasure :=
  fubini_swap_of_integrable r (integrable_fubiniIntegrand_of_bound r hmeas hbound)

theorem fubini_swap_of_lintegral_bound (r : ℕ) {τ : ℝ}
    (hbound : (∫⁻ z, ENNReal.ofReal ‖Function.uncurry (fubiniIntegrand r) z‖
        ∂((reducedLaw r τ).prod planeMeasure)) ≤ ENNReal.ofReal Real.pi) :
    (∫ W, reducedIntegrand r W ∂(reducedLaw r τ))
      = Real.pi⁻¹ * ∫ p, (∫ W, fubiniIntegrand r W p ∂(reducedLaw r τ)) ∂planeMeasure :=
  fubini_swap_of_bound r (measurable_uncurry_fubiniIntegrand r).aestronglyMeasurable hbound

noncomputable def fubiniMajorant (r : ℕ) (W : Fin r → EuclideanSpace ℝ (Fin 2))
    (p : ℝ × ℝ) : ℝ :=
  ‖colFun r 0 W‖ * ‖colFun r 1 W‖ *
    ((p.1 * p.2) ^ (-(1/2) : ℝ) *
      Real.exp (-(p.1 * ‖colFun r 0 W‖ ^ 2 + p.2 * ‖colFun r 1 W‖ ^ 2)))

lemma planeMeasure_eq_prod :
    planeMeasure = (volume.restrict (Set.Ioi (0:ℝ))).prod (volume.restrict (Set.Ioi (0:ℝ))) :=
  rfl

lemma ae_planeMeasure_pos : ∀ᵐ p ∂planeMeasure, 0 < p.1 ∧ 0 < p.2 := by
  rw [ae_iff]
  have h : planeMeasure
      = (volume.prod volume).restrict (Set.Ioi (0:ℝ) ×ˢ Set.Ioi (0:ℝ)) := by
    rw [planeMeasure_eq_prod, Measure.prod_restrict]
  rw [h, Measure.restrict_apply' (μ := volume.prod volume)
      (s := Set.Ioi (0:ℝ) ×ˢ Set.Ioi (0:ℝ))
      (t := {p : ℝ × ℝ | ¬ (0 < p.1 ∧ 0 < p.2)})
      (MeasurableSet.prod measurableSet_Ioi measurableSet_Ioi)]
  have hempty : {p : ℝ × ℝ | ¬ (0 < p.1 ∧ 0 < p.2)} ∩ (Set.Ioi (0:ℝ) ×ˢ Set.Ioi (0:ℝ)) = ∅ := by
    ext p
    simp
  rw [hempty, measure_empty]

lemma lintegral_rpow_neg_half_exp_mul {C : ℝ} (hC : 0 < C) :
    (∫⁻ u in Set.Ioi (0:ℝ), ENNReal.ofReal (u ^ (-(1/2) : ℝ) * Real.exp (-(C * u))))
      = ENNReal.ofReal (Real.sqrt Real.pi / Real.sqrt C) := by
  have hmeas : AEStronglyMeasurable (fun u : ℝ => u ^ (-(1/2) : ℝ) * Real.exp (-(C * u)))
      (volume.restrict (Set.Ioi (0:ℝ))) := by
    apply Measurable.aestronglyMeasurable
    fun_prop
  have hnn : 0 ≤ᵐ[volume.restrict (Set.Ioi (0:ℝ))]
      (fun u : ℝ => u ^ (-(1/2) : ℝ) * Real.exp (-(C * u))) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    exact mul_nonneg (Real.rpow_pos_of_pos hu _).le (Real.exp_pos _).le
  have h := integral_eq_lintegral_of_nonneg_ae hnn hmeas
  rw [integral_rpow_neg_half_exp_mul hC] at h
  have hpos : (0:ℝ) < Real.sqrt Real.pi / Real.sqrt C :=
    div_pos (Real.sqrt_pos.mpr Real.pi_pos) (Real.sqrt_pos.mpr hC)
  have hne : (∫⁻ u in Set.Ioi (0:ℝ),
      ENNReal.ofReal (u ^ (-(1/2) : ℝ) * Real.exp (-(C * u)))) ≠ ⊤ := by
    intro htop
    rw [htop, ENNReal.toReal_top] at h
    linarith
  calc (∫⁻ u in Set.Ioi (0:ℝ), ENNReal.ofReal (u ^ (-(1/2) : ℝ) * Real.exp (-(C * u))))
      = ENNReal.ofReal ((∫⁻ u in Set.Ioi (0:ℝ),
          ENNReal.ofReal (u ^ (-(1/2) : ℝ) * Real.exp (-(C * u)))).toReal) :=
        (ENNReal.ofReal_toReal hne).symm
    _ = ENNReal.ofReal (Real.sqrt Real.pi / Real.sqrt C) := by rw [← h]

lemma lintegral_laplace_kernel {A B : ℝ} (hA : 0 < A) (hB : 0 < B) :
    (∫⁻ p, ENNReal.ofReal ((p.1 * p.2) ^ (-(1/2) : ℝ) *
        Real.exp (-(p.1 * A + p.2 * B))) ∂planeMeasure)
      = ENNReal.ofReal (Real.pi / (Real.sqrt A * Real.sqrt B)) := by
  have hgem : ∀ p : ℝ × ℝ, 0 < p.1 → 0 < p.2 →
      ENNReal.ofReal ((p.1 * p.2) ^ (-(1/2) : ℝ) * Real.exp (-(p.1 * A + p.2 * B)))
        = ENNReal.ofReal (p.1 ^ (-(1/2) : ℝ) * Real.exp (-(A * p.1))) *
          ENNReal.ofReal (p.2 ^ (-(1/2) : ℝ) * Real.exp (-(B * p.2))) := by
    intro p h1 h2
    have hg1 : 0 ≤ p.1 ^ (-(1/2) : ℝ) * Real.exp (-(A * p.1)) :=
      mul_nonneg (Real.rpow_pos_of_pos h1 _).le (Real.exp_pos _).le
    have hg2 : 0 ≤ p.2 ^ (-(1/2) : ℝ) * Real.exp (-(B * p.2)) :=
      mul_nonneg (Real.rpow_pos_of_pos h2 _).le (Real.exp_pos _).le
    have hval : (p.1 * p.2) ^ (-(1/2) : ℝ) * Real.exp (-(p.1 * A + p.2 * B))
        = (p.1 ^ (-(1/2) : ℝ) * Real.exp (-(A * p.1))) *
          (p.2 ^ (-(1/2) : ℝ) * Real.exp (-(B * p.2))) := by
      rw [Real.mul_rpow h1.le h2.le,
        show -(p.1 * A + p.2 * B) = -(A * p.1) + -(B * p.2) by ring, Real.exp_add]
      ring
    rw [hval, ENNReal.ofReal_mul hg1]
  have h1 : (∫⁻ p, ENNReal.ofReal ((p.1 * p.2) ^ (-(1/2) : ℝ) *
        Real.exp (-(p.1 * A + p.2 * B))) ∂planeMeasure)
      = ∫⁻ p, ENNReal.ofReal (p.1 ^ (-(1/2) : ℝ) * Real.exp (-(A * p.1))) *
          ENNReal.ofReal (p.2 ^ (-(1/2) : ℝ) * Real.exp (-(B * p.2))) ∂planeMeasure := by
    apply lintegral_congr_ae
    filter_upwards [ae_planeMeasure_pos] with p hp
    exact hgem p hp.1 hp.2
  rw [h1, planeMeasure_eq_prod,
    lintegral_prod_mul (f := fun s => ENNReal.ofReal (s ^ (-(1/2) : ℝ) * Real.exp (-(A * s))))
      (g := fun t => ENNReal.ofReal (t ^ (-(1/2) : ℝ) * Real.exp (-(B * t))))
      (by fun_prop) (by fun_prop),
    lintegral_rpow_neg_half_exp_mul hA, lintegral_rpow_neg_half_exp_mul hB,
    ← ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ Real.sqrt Real.pi / Real.sqrt A)]
  congr 1
  rw [div_mul_div_comm, Real.mul_self_sqrt Real.pi_pos.le]

lemma norm_fubiniIntegrand_le (r : ℕ) (W : Fin r → EuclideanSpace ℝ (Fin 2)) {p : ℝ × ℝ}
    (h1 : 0 < p.1) (h2 : 0 < p.2) :
    ‖fubiniIntegrand r W p‖ ≤ fubiniMajorant r W p := by
  have hfac_pos : 0 < (p.1 * p.2) ^ (-(1/2) : ℝ) :=
    Real.rpow_pos_of_pos (mul_pos h1 h2) _
  have hexp_pos : 0 < Real.exp (-(p.1 * ‖colFun r 0 W‖ ^ 2 + p.2 * ‖colFun r 1 W‖ ^ 2)) :=
    Real.exp_pos _
  have hfac : ‖(p.1 * p.2) ^ (-(1/2) : ℝ) *
        Real.exp (-(p.1 * ‖colFun r 0 W‖ ^ 2 + p.2 * ‖colFun r 1 W‖ ^ 2))‖
      = (p.1 * p.2) ^ (-(1/2) : ℝ) *
        Real.exp (-(p.1 * ‖colFun r 0 W‖ ^ 2 + p.2 * ‖colFun r 1 W‖ ^ 2)) := by
    rw [Real.norm_eq_abs, abs_of_pos (mul_pos hfac_pos hexp_pos)]
  rw [fubiniIntegrand, fubiniMajorant, norm_mul, hfac]
  exact mul_le_mul_of_nonneg_right (norm_inner_le_norm (colFun r 0 W) (colFun r 1 W))
    (mul_nonneg hfac_pos.le hexp_pos.le)

lemma lintegral_majorant_W_le (r : ℕ) (W : Fin r → EuclideanSpace ℝ (Fin 2)) :
    (∫⁻ p, ENNReal.ofReal (fubiniMajorant r W p) ∂planeMeasure)
      ≤ ENNReal.ofReal Real.pi := by
  by_cases hX : colFun r 0 W = 0
  · have hzero : ∀ p, fubiniMajorant r W p = 0 := by
      intro p
      simp [fubiniMajorant, hX]
    simp only [hzero]
    simp
  by_cases hY : colFun r 1 W = 0
  · have hzero : ∀ p, fubiniMajorant r W p = 0 := by
      intro p
      simp [fubiniMajorant, hY]
    simp only [hzero]
    simp
  have hXp : 0 < ‖colFun r 0 W‖ := norm_pos_iff.mpr hX
  have hYp : 0 < ‖colFun r 1 W‖ := norm_pos_iff.mpr hY
  have hc : 0 < ‖colFun r 0 W‖ * ‖colFun r 1 W‖ := mul_pos hXp hYp
  have hfac : ∀ p : ℝ × ℝ,
      ENNReal.ofReal (fubiniMajorant r W p)
        = ENNReal.ofReal (‖colFun r 0 W‖ * ‖colFun r 1 W‖) *
          ENNReal.ofReal ((p.1 * p.2) ^ (-(1/2) : ℝ) *
            Real.exp (-(p.1 * ‖colFun r 0 W‖ ^ 2 + p.2 * ‖colFun r 1 W‖ ^ 2))) := by
    intro p
    rw [fubiniMajorant, ENNReal.ofReal_mul (mul_nonneg (norm_nonneg _) (norm_nonneg _))]
  have hkey : ‖colFun r 0 W‖ * ‖colFun r 1 W‖ *
      (Real.pi / (Real.sqrt (‖colFun r 0 W‖ ^ 2) * Real.sqrt (‖colFun r 1 W‖ ^ 2)))
      = Real.pi := by
    rw [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)]
    exact mul_div_cancel₀ _ (ne_of_gt hc)
  have hval : (∫⁻ p, ENNReal.ofReal (fubiniMajorant r W p) ∂planeMeasure)
      = ENNReal.ofReal Real.pi := by
    rw [lintegral_congr hfac, lintegral_const_mul _ (by fun_prop),
      lintegral_laplace_kernel (by positivity) (by positivity),
      ← ENNReal.ofReal_mul (mul_nonneg (norm_nonneg _) (norm_nonneg _)), hkey]
  exact hval.le

theorem lintegral_norm_fubiniIntegrand_le_pi (r : ℕ) {τ : ℝ} :
    (∫⁻ z, ENNReal.ofReal ‖Function.uncurry (fubiniIntegrand r) z‖
        ∂((reducedLaw r τ).prod planeMeasure)) ≤ ENNReal.ofReal Real.pi := by
  have : SFinite planeMeasure := by
    rw [planeMeasure_eq_prod]
    infer_instance
  have hmeas : AEMeasurable
      (fun z : (Fin r → EuclideanSpace ℝ (Fin 2)) × (ℝ × ℝ) =>
        ENNReal.ofReal (fubiniMajorant r z.1 z.2))
      ((reducedLaw r τ).prod planeMeasure) := by
    apply Measurable.aemeasurable
    simp only [fubiniMajorant, colFun]
    fun_prop
  have hae : ∀ᵐ z ∂((reducedLaw r τ).prod planeMeasure), 0 < z.2.1 ∧ 0 < z.2.2 := by
    have hset : MeasurableSet
        {z : (Fin r → EuclideanSpace ℝ (Fin 2)) × (ℝ × ℝ) | 0 < z.2.1 ∧ 0 < z.2.2} := by
      measurability
    have h := (Measure.ae_prod_mem_iff_ae_ae_mem (μ := reducedLaw r τ) (ν := planeMeasure)
      hset).mpr (Filter.Eventually.of_forall fun _ => ae_planeMeasure_pos)
    simpa using h
  calc (∫⁻ z, ENNReal.ofReal ‖Function.uncurry (fubiniIntegrand r) z‖
        ∂((reducedLaw r τ).prod planeMeasure))
      ≤ ∫⁻ z, ENNReal.ofReal (fubiniMajorant r z.1 z.2)
          ∂((reducedLaw r τ).prod planeMeasure) := by
        apply lintegral_mono_ae
        filter_upwards [hae] with z hz
        exact ENNReal.ofReal_le_ofReal (norm_fubiniIntegrand_le r z.1 hz.1 hz.2)
    _ = ∫⁻ W, (∫⁻ p, ENNReal.ofReal (fubiniMajorant r W p) ∂planeMeasure)
          ∂(reducedLaw r τ) := by
        rw [lintegral_lintegral]
        exact hmeas
    _ ≤ ∫⁻ _W, ENNReal.ofReal Real.pi ∂(reducedLaw r τ) :=
        lintegral_mono fun W => lintegral_majorant_W_le r W
    _ = ENNReal.ofReal Real.pi := by
        rw [lintegral_const]
        have : IsProbabilityMeasure (reducedLaw r τ) := by
          unfold reducedLaw
          infer_instance
        simp

lemma integrable_fubiniIntegrand (r : ℕ) {τ : ℝ}
    (hmeas : AEStronglyMeasurable (Function.uncurry (fubiniIntegrand r))
      ((reducedLaw r τ).prod planeMeasure)) :
    Integrable (Function.uncurry (fubiniIntegrand r)) ((reducedLaw r τ).prod planeMeasure) := by
  refine ⟨hmeas, ?_⟩
  rw [hasFiniteIntegral_iff_norm]
  exact lt_of_le_of_lt (lintegral_norm_fubiniIntegrand_le_pi r) ENNReal.ofReal_lt_top

theorem fubini_swap_proved (r : ℕ) (τ : ℝ) :
    (∫ W, reducedIntegrand r W ∂(reducedLaw r τ))
      = Real.pi⁻¹ * ∫ p, (∫ W, fubiniIntegrand r W p ∂(reducedLaw r τ)) ∂planeMeasure :=
  fubini_swap_of_lintegral_bound r (lintegral_norm_fubiniIntegrand_le_pi r)

end Grothendieck

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators Real RealInnerProductSpace

namespace Grothendieck

lemma isHermitian_corrMat (t : ℝ) : (corrMat t).IsHermitian := by
  refine Matrix.IsHermitian.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp

lemma corrMat_posSemidef {t : ℝ} (ht : |t| ≤ 1) : (corrMat t).PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (isHermitian_corrMat t) fun x => ?_
  simp only [star_trivial, Matrix.mulVec, dotProduct, Fin.sum_univ_two, corrMat_apply_zero_zero,
    corrMat_apply_zero_one, corrMat_apply_one_zero, corrMat_apply_one_one]
  have h1 : (0:ℝ) ≤ 1 - t^2 := by
    have := abs_le.mp ht
    nlinarith
  nlinarith [sq_nonneg (x 0 + t * x 1), sq_nonneg (x 1), h1, mul_nonneg h1 (sq_nonneg (x 1))]

/-- The one-dimensional Gaussian integral of a complex exponential. -/
lemma integral_gaussian_exp (c : ℝ) :
    ∫ t : ℝ, Complex.exp (↑(t * c) * Complex.I) ∂(gaussianReal 0 1)
      = Complex.exp (-↑(c ^ 2) / 2) := by
  simp only [← Real.inner_apply]
  rw [← charFun_apply, charFun_gaussianReal]
  simp only [Complex.ofReal_zero, mul_zero, zero_mul, NNReal.coe_one, Complex.ofReal_one, one_mul]
  congr 1
  rw [Complex.ofReal_pow]
  ring

lemma measurable_normalize (r : ℕ) : Measurable (normalize r) := by
  unfold normalize
  fun_prop

lemma measurable_colFun (r : ℕ) (j : Fin 2) : Measurable (colFun r j) := by
  unfold colFun
  fun_prop

lemma measurable_reducedIntegrand (r : ℕ) : Measurable (reducedIntegrand r) := by
  unfold reducedIntegrand
  exact Measurable.inner (measurable_normalize r |>.comp (measurable_colFun r 0))
    (measurable_normalize r |>.comp (measurable_colFun r 1))

/-- The reduced integrand in coordinates: the cosine of the angle between the two columns. -/
lemma reducedIntegrand_eq (r : ℕ) (W : Fin r → EuclideanSpace ℝ (Fin 2)) :
    reducedIntegrand r W
      = (∑ i, (W i).ofLp 0 * (W i).ofLp 1) /
        (Real.sqrt (∑ i, ((W i).ofLp 0) ^ 2) * Real.sqrt (∑ i, ((W i).ofLp 1) ^ 2)) := by
  have hinner : inner ℝ (colFun r 0 W) (colFun r 1 W)
      = ∑ i, (W i).ofLp 0 * (W i).ofLp 1 := by
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    simp only [dotProduct, star_trivial, colFun, WithLp.ofLp_toLp]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have hn0 : ‖colFun r 0 W‖ = Real.sqrt (∑ i, ((W i).ofLp 0) ^ 2) := by
    rw [← Real.sqrt_sq (norm_nonneg _), EuclideanSpace.real_norm_sq_eq]
    simp [colFun]
  have hn1 : ‖colFun r 1 W‖ = Real.sqrt (∑ i, ((W i).ofLp 1) ^ 2) := by
    rw [← Real.sqrt_sq (norm_nonneg _), EuclideanSpace.real_norm_sq_eq]
    simp [colFun]
  unfold reducedIntegrand normalize
  rw [real_inner_smul_left, real_inner_smul_right, hinner, hn0, hn1]
  rw [inv_mul_eq_div, inv_mul_eq_div, div_div, mul_comm]

lemma measurable_cholMap (t : ℝ) : Measurable (cholMap t) := by
  unfold cholMap
  refine (WithLp.measurable_toLp 2 (Fin 2 → ℝ)).comp ?_
  apply measurable_pi_iff.mpr
  intro j
  fin_cases j <;> simp <;> fun_prop

lemma inner_cholMap (t : ℝ) (y z : EuclideanSpace ℝ (Fin 2)) :
    inner ℝ (cholMap t y) z = inner ℝ y (cholAdj t z) := by
  rw [EuclideanSpace.inner_eq_star_dotProduct, EuclideanSpace.inner_eq_star_dotProduct]
  simp only [dotProduct, star_trivial, cholMap, cholAdj, WithLp.ofLp_toLp, Fin.sum_univ_two,
    Matrix.cons_val_zero, Matrix.cons_val_one, Fin.isValue, Fin.zero_eta, Fin.mk_one]
  ring

lemma norm_sq_cholAdj {t : ℝ} (ht : |t| ≤ 1) (z : EuclideanSpace ℝ (Fin 2)) :
    ‖cholAdj t z‖ ^ 2 = z.ofLp ⬝ᵥ (corrMat t).mulVec z.ofLp := by
  have h1 : (0:ℝ) ≤ 1 - t ^ 2 := by
    have := abs_le.mp ht
    nlinarith
  rw [EuclideanSpace.real_norm_sq_eq]
  simp only [cholAdj, WithLp.ofLp_toLp, Fin.sum_univ_two, Matrix.cons_val_zero,
    Matrix.cons_val_one, Fin.isValue, Fin.zero_eta, Fin.mk_one]
  simp only [dotProduct, Matrix.mulVec, Fin.sum_univ_two, corrMat_apply_zero_zero,
    corrMat_apply_zero_one, corrMat_apply_one_zero, corrMat_apply_one_one]
  rw [mul_pow, Real.sq_sqrt h1]
  ring

/-- **The correlation law in Cholesky form**: the two-dimensional Gaussian with covariance
`!![1,t;t,1]` is the law of `(y₀, t y₀ + √(1-t²) y₁)` for a standard Gaussian `y ∈ ℝ²`. -/
lemma map_cholMap_stdGaussian {t : ℝ} (ht : |t| ≤ 1) :
    Measure.map (cholMap t) (stdGaussian (EuclideanSpace ℝ (Fin 2)))
      = multivariateGaussian 0 (corrMat t) := by
  have hS : (corrMat t).PosSemidef := corrMat_posSemidef ht
  apply Measure.ext_of_charFun
  ext z
  rw [charFun_multivariateGaussian hS]
  simp only [inner_zero_right, Complex.ofReal_zero, mul_zero, zero_mul, sub_zero]
  rw [charFun_apply]
  have hcont : Continuous fun y : EuclideanSpace ℝ (Fin 2) =>
      Complex.exp (↑⟪y, z⟫ * Complex.I) := by fun_prop
  rw [integral_map (measurable_cholMap t).aemeasurable hcont.aestronglyMeasurable]
  simp only [inner_cholMap]
  rw [← charFun_apply, charFun_stdGaussian]
  congr 1
  rw [← Complex.ofReal_pow, norm_sq_cholAdj ht]
  push_cast
  ring

theorem integral_exp_neg_mul_sq {c : ℝ} (hc : 0 < c) :
    (∫ x : ℝ, Real.exp (-c * x ^ 2)) = Real.sqrt (Real.pi / c) := by
  have h := GaussianFourier.integral_rexp_neg_mul_sq_norm (V := ℝ) hc
  rw [Module.finrank_self] at h
  simp only [Nat.cast_one, one_div] at h
  have h' : (∫ x : ℝ, Real.exp (-c * x ^ 2)) = ∫ x : ℝ, Real.exp (-c * ‖x‖ ^ 2) := by
    apply MeasureTheory.integral_congr_ae
    filter_upwards with x
    rw [Real.norm_eq_abs, sq_abs]
  rw [h', h, show (2:ℝ)⁻¹ = 1 / 2 by norm_num, ← Real.sqrt_eq_rpow]

theorem integral_sq_mul_exp_neg_mul_sq_half {c : ℝ} (hc : 0 < c) :
    (∫ x in Set.Ioi (0:ℝ), x ^ 2 * Real.exp (-(c * x ^ 2)))
      = Real.sqrt Real.pi / (4 * c ^ ((3:ℝ)/2)) := by
  have h := integral_rpow_mul_exp_neg_mul_rpow (p := 2) (q := 2) (b := c)
    (by norm_num) (by norm_num) hc
  have e1 : (-(2 + 1) / 2 : ℝ) = -(3/2) := by norm_num
  have e2 : ((2 + 1) / 2 : ℝ) = 3/2 := by norm_num
  rw [e1, e2] at h
  have hΓ : Real.Gamma (3/2 : ℝ) = Real.sqrt Real.pi / 2 := by
    have h1 := Real.Gamma_add_one (s := (1/2 : ℝ)) (by norm_num)
    rw [show (1/2 : ℝ) + 1 = 3/2 by norm_num, Real.Gamma_one_half_eq] at h1
    linarith
  rw [hΓ] at h
  have h' : (∫ x in Set.Ioi (0:ℝ), x ^ 2 * Real.exp (-(c * x ^ 2)))
      = c ^ (-(3/2) : ℝ) * (1/2) * (Real.sqrt Real.pi / 2) := by
    simpa only [Real.rpow_two, neg_mul] using h
  rw [h', Real.rpow_neg (le_of_lt hc)]
  have hc32 : (0:ℝ) < c ^ ((3:ℝ)/2) := Real.rpow_pos_of_pos hc _
  field_simp
  ring

/-- `∫_ℝ x² e^{-c x²} dx = √π/(2 c^{3/2})`. -/
theorem integral_sq_mul_exp_neg_mul_sq {c : ℝ} (hc : 0 < c) :
    (∫ x : ℝ, x ^ 2 * Real.exp (-(c * x ^ 2)))
      = Real.sqrt Real.pi / (2 * c ^ ((3:ℝ)/2)) := by
  have h := integral_comp_abs (f := fun x : ℝ => x ^ 2 * Real.exp (-(c * x ^ 2)))
  rw [integral_sq_mul_exp_neg_mul_sq_half hc] at h
  have h' : (∫ x : ℝ, (fun x : ℝ => x ^ 2 * Real.exp (-(c * x ^ 2))) |x|)
      = ∫ x : ℝ, x ^ 2 * Real.exp (-(c * x ^ 2)) := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [sq_abs]
  rw [h'] at h
  rw [h]
  ring

/-- `∫_ℝ x e^{-c x²} dx = 0` (`c > 0`): the integrand is odd. -/
theorem integral_x_mul_exp_neg_mul_sq {c : ℝ} (hc : 0 < c) :
    (∫ x : ℝ, x * Real.exp (-(c * x ^ 2))) = 0 := by
  have hInt : Integrable (fun x : ℝ => x * Real.exp (-(c * x ^ 2))) := by
    have h := integrable_rpow_mul_exp_neg_mul_sq hc (s := (1:ℝ)) (by norm_num)
    simpa only [Real.rpow_one, neg_mul] using h
  have hsplit := integral_add_compl (μ := volume) (s := Set.Ioi (0:ℝ)) measurableSet_Ioi hInt
  have hneg : (∫ x in (Set.Ioi (0:ℝ))ᶜ, x * Real.exp (-(c * x ^ 2)))
      = -(∫ x in Set.Ioi (0:ℝ), x * Real.exp (-(c * x ^ 2))) := by
    have hc' : (Set.Ioi (0:ℝ))ᶜ = Set.Iic 0 := by rw [Set.compl_Ioi]
    rw [hc']
    have h := integral_comp_neg_Iic (c := 0) (f := fun x : ℝ => x * Real.exp (-(c * x ^ 2)))
    simp only [neg_zero] at h
    rw [← h]
    rw [← MeasureTheory.integral_neg]
    refine setIntegral_congr_fun measurableSet_Iic (fun x _ => ?_)
    simp only [neg_sq]
    ring
  rw [hneg] at hsplit
  linarith

end Grothendieck

set_option maxHeartbeats 2000000

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators Real RealInnerProductSpace NNReal

namespace Grothendieck

theorem integral_exp_neg_mul_sq_norm {c : ℝ} (hc : 0 < c) :
    (∫ x : ℝ, Real.exp (-(c * x ^ 2))) = Real.sqrt (Real.pi / c) := by
  simpa only [neg_mul] using integral_exp_neg_mul_sq hc

theorem integrable_exp_neg_mul_sq_norm {c : ℝ} (hc : 0 < c) :
    Integrable (fun x : ℝ => Real.exp (-(c * x ^ 2))) volume := by
  simpa only [neg_mul] using integrable_exp_neg_mul_sq hc

theorem integrable_mul_exp_neg_mul_sq_norm {c : ℝ} (hc : 0 < c) :
    Integrable (fun x : ℝ => x * Real.exp (-(c * x ^ 2))) volume := by
  simpa only [neg_mul, Real.rpow_one] using
    integrable_rpow_mul_exp_neg_mul_sq hc (s := (1:ℝ)) (by norm_num)

/-- The row map `p ↦ cholMap τ (p.1, p.2)`: the Cholesky parametrisation of one row. -/
def rowMap (t : ℝ) (p : ℝ × ℝ) : EuclideanSpace ℝ (Fin 2) :=
  cholMap t (WithLp.toLp 2 ![p.1, p.2])

@[simp] lemma rowMap_ofLp_zero (t : ℝ) (p : ℝ × ℝ) : (rowMap t p).ofLp 0 = p.1 := rfl
@[simp] lemma rowMap_ofLp_one (t : ℝ) (p : ℝ × ℝ) :
    (rowMap t p).ofLp 1 = t * p.1 + Real.sqrt (1 - t ^ 2) * p.2 := rfl

lemma measurable_toLp_pair : Measurable (fun p : ℝ × ℝ => WithLp.toLp 2 ![p.1, p.2]) := by
  fun_prop

/-- The standard Gaussian on `ℝ²` as the law of a pair of independent standard Gaussians. -/
lemma stdGaussian_fin_two_eq_map_prod :
    stdGaussian (EuclideanSpace ℝ (Fin 2))
      = Measure.map (fun p : ℝ × ℝ => WithLp.toLp 2 ![p.1, p.2])
          ((gaussianReal 0 1).prod (gaussianReal 0 1)) := by
  have hm1 := Measure.map_map (μ := (gaussianReal 0 1).prod (gaussianReal 0 1))
    (g := WithLp.toLp 2)
    (f := fun p : ℝ × ℝ => (MeasurableEquiv.finTwoArrow (α := ℝ)).symm p)
    (WithLp.measurable_toLp 2 (Fin 2 → ℝ)) (MeasurableEquiv.measurable _)
  have hfun : (fun p : ℝ × ℝ => WithLp.toLp 2 ![p.1, p.2])
      = (WithLp.toLp 2) ∘ fun p : ℝ × ℝ => (MeasurableEquiv.finTwoArrow (α := ℝ)).symm p := by
    funext p
    simp only [Function.comp_apply]
    congr 1
  rw [hfun]
  rw [← hm1]
  rw [(measurePreserving_finTwoArrow (gaussianReal 0 1)).symm.map_eq]
  rw [map_pi_eq_stdGaussian (ι := Fin 2)]

lemma measurable_rowMap (t : ℝ) : Measurable (rowMap t) :=
  (measurable_cholMap t).comp measurable_toLp_pair

/-- **The single row law**: the two-dimensional Gaussian with covariance `!![1,t;t,1]` is the
law of `(p.1, t p.1 + √(1-t²) p.2)` for a pair of independent standard Gaussians. -/
theorem rowLaw_eq {t : ℝ} (ht : |t| ≤ 1) :
    Measure.map (rowMap t) ((gaussianReal 0 1).prod (gaussianReal 0 1))
      = multivariateGaussian 0 (corrMat t) := by
  have h := Measure.map_map (μ := (gaussianReal 0 1).prod (gaussianReal 0 1))
    (g := cholMap t) (f := fun p : ℝ × ℝ => WithLp.toLp 2 ![p.1, p.2])
    (measurable_cholMap t) measurable_toLp_pair
  change Measure.map ((cholMap t) ∘
    (fun p : ℝ × ℝ => WithLp.toLp 2 ![p.1, p.2])) _ = _
  rw [← h, ← stdGaussian_fin_two_eq_map_prod, map_cholMap_stdGaussian ht]

lemma gaussianPDFReal_zero_one_apply (x : ℝ) :
    gaussianPDFReal 0 1 x = (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(x ^ 2) / 2) := by
  rw [ProbabilityTheory.gaussianPDFReal_def]
  norm_num

/-- Integration against the standard Gaussian, written through its Lebesgue density. -/
lemma integral_gaussianReal_zero_one_eq (f : ℝ → ℝ) :
    ∫ x, f x ∂(gaussianReal 0 1) = ∫ x, gaussianPDFReal 0 1 x * f x := by
  rw [ProbabilityTheory.gaussianReal_of_var_ne_zero 0 (by norm_num : (1 : ℝ≥0) ≠ 0)]
  rw [integral_withDensity_eq_integral_toReal_smul (measurable_gaussianPDF 0 1)
    (by filter_upwards with x; exact ENNReal.ofReal_lt_top) f]
  simp only [ProbabilityTheory.gaussianPDF.eq_1,
    ENNReal.toReal_ofReal (gaussianPDFReal_nonneg 0 1 _), smul_eq_mul]

/-- The standard Gaussian weight is a bounded factor: `gaussianPDFReal 0 1 x * e^{-c x²}` is a
constant times `e^{-(c+1/2)x²}`. -/
lemma gaussianPDFReal_zero_one_mul_exp (c x : ℝ) :
    gaussianPDFReal 0 1 x * Real.exp (-(c * x ^ 2))
      = (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-((c + 1 / 2) * x ^ 2)) := by
  rw [gaussianPDFReal_zero_one_apply, mul_assoc, ← Real.exp_add]
  congr 2
  ring

/-- `x ↦ e^{-c x²}` is integrable against the standard Gaussian as soon as `c > -1/2`. -/
theorem integrable_exp_neg_mul_sq_gaussianReal {c : ℝ} (hc : -(1 / 2 : ℝ) < c) :
    Integrable (fun x : ℝ => Real.exp (-(c * x ^ 2))) (gaussianReal 0 1) := by
  rw [gaussianReal_of_var_ne_zero 0 (by norm_num : (1 : ℝ≥0) ≠ 0)]
  rw [integrable_withDensity_iff_integrable_smul' (measurable_gaussianPDF 0 1)
    (by filter_upwards with x; exact ENNReal.ofReal_lt_top)]
  have hbase : Integrable (fun x : ℝ => (Real.sqrt (2 * Real.pi))⁻¹ *
      Real.exp (-((c + 1 / 2) * x ^ 2))) volume := by
    have h := (integrable_exp_neg_mul_sq (by linarith : (0:ℝ) < c + 1 / 2)).const_mul
      ((Real.sqrt (2 * Real.pi))⁻¹)
    simpa only [neg_mul] using h
  refine hbase.congr (Filter.Eventually.of_forall fun x => ?_)
  have hexp : Real.exp (-((c + 1 / 2) * x ^ 2))
      = Real.exp (-x ^ 2 / 2) * Real.exp (-(c * x ^ 2)) := by
    rw [← Real.exp_add]; congr 1; ring
  simp only [ProbabilityTheory.gaussianPDF.eq_1, smul_eq_mul, gaussianPDFReal_zero_one_apply]
  rw [ENNReal.toReal_ofReal (by positivity), hexp]
  ring

/-- `x ↦ x * e^{-c x²}` is integrable against the standard Gaussian when `c > -1/2`. -/
theorem integrable_mul_exp_neg_mul_sq_gaussianReal {c : ℝ} (hc : -(1 / 2 : ℝ) < c) :
    Integrable (fun x : ℝ => x * Real.exp (-(c * x ^ 2))) (gaussianReal 0 1) := by
  rw [gaussianReal_of_var_ne_zero 0 (by norm_num : (1 : ℝ≥0) ≠ 0)]
  rw [integrable_withDensity_iff_integrable_smul' (measurable_gaussianPDF 0 1)
    (by filter_upwards with x; exact ENNReal.ofReal_lt_top)]
  have hbase : Integrable (fun x : ℝ => (Real.sqrt (2 * Real.pi))⁻¹ *
      (x * Real.exp (-((c + 1 / 2) * x ^ 2)))) volume := by
    have h := (integrable_rpow_mul_exp_neg_mul_sq (by linarith : (0:ℝ) < c + 1 / 2)
      (s := (1:ℝ)) (by norm_num)).const_mul ((Real.sqrt (2 * Real.pi))⁻¹)
    simpa only [neg_mul, Real.rpow_one] using h
  refine hbase.congr (Filter.Eventually.of_forall fun x => ?_)
  have hexp : Real.exp (-((c + 1 / 2) * x ^ 2))
      = Real.exp (-x ^ 2 / 2) * Real.exp (-(c * x ^ 2)) := by
    rw [← Real.exp_add]; congr 1; ring
  simp only [ProbabilityTheory.gaussianPDF.eq_1, smul_eq_mul, gaussianPDFReal_zero_one_apply]
  rw [ENNReal.toReal_ofReal (by positivity), hexp]
  ring

/-- `x ↦ x² * e^{-c x²}` is integrable against the standard Gaussian when `c > -1/2`. -/
theorem integrable_sq_mul_exp_neg_mul_sq_gaussianReal {c : ℝ} (hc : -(1 / 2 : ℝ) < c) :
    Integrable (fun x : ℝ => x ^ 2 * Real.exp (-(c * x ^ 2))) (gaussianReal 0 1) := by
  rw [gaussianReal_of_var_ne_zero 0 (by norm_num : (1 : ℝ≥0) ≠ 0)]
  rw [integrable_withDensity_iff_integrable_smul' (measurable_gaussianPDF 0 1)
    (by filter_upwards with x; exact ENNReal.ofReal_lt_top)]
  have hbase : Integrable (fun x : ℝ => (Real.sqrt (2 * Real.pi))⁻¹ *
      (x ^ 2 * Real.exp (-((c + 1 / 2) * x ^ 2)))) volume := by
    have h := (integrable_rpow_mul_exp_neg_mul_sq (by linarith : (0:ℝ) < c + 1 / 2)
      (s := (2:ℝ)) (by norm_num)).const_mul ((Real.sqrt (2 * Real.pi))⁻¹)
    simpa only [neg_mul, Real.rpow_two] using h
  refine hbase.congr (Filter.Eventually.of_forall fun x => ?_)
  have hexp : Real.exp (-((c + 1 / 2) * x ^ 2))
      = Real.exp (-x ^ 2 / 2) * Real.exp (-(c * x ^ 2)) := by
    rw [← Real.exp_add]; congr 1; ring
  simp only [ProbabilityTheory.gaussianPDF.eq_1, smul_eq_mul, gaussianPDFReal_zero_one_apply]
  rw [ENNReal.toReal_ofReal (by positivity), hexp]
  ring

/-- **Two-dimensional integration against `γ × γ` as an iterated Lebesgue integral.** -/
theorem integral_prod_gaussianReal_eq (G : ℝ × ℝ → ℝ)
    (hG : Integrable G ((gaussianReal 0 1).prod (gaussianReal 0 1))) :
    ∫ z, G z ∂((gaussianReal 0 1).prod (gaussianReal 0 1))
      = ∫ p, ∫ q, (gaussianPDFReal 0 1 p * gaussianPDFReal 0 1 q) * G (p, q) := by
  rw [integral_prod _ hG]
  simp_rw [integral_gaussianReal_zero_one_eq]
  refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
  dsimp only
  rw [← MeasureTheory.integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun q => ?_)
  dsimp only
  ring

/-- `∫ q, e^{-(D q² + 2 B p q)} = √(π/D) e^{B²p²/D}` for `D > 0`. -/
theorem integral_exp_neg_quadratic_linear {D B p : ℝ} (hD : 0 < D) :
    (∫ q : ℝ, Real.exp (-(D * q ^ 2 + 2 * B * p * q)))
      = Real.sqrt (Real.pi / D) * Real.exp (B ^ 2 * p ^ 2 / D) := by
  have hDne : D ≠ 0 := hD.ne'
  have key : ∀ q : ℝ, -(D * q ^ 2 + 2 * B * p * q)
      = -(D * (q + B * p / D) ^ 2) + B ^ 2 * p ^ 2 / D := by
    intro q; field_simp; ring
  have key2 : ∀ q : ℝ, Real.exp (-(D * q ^ 2 + 2 * B * p * q))
      = Real.exp (B ^ 2 * p ^ 2 / D) * Real.exp (-(D * (q + B * p / D) ^ 2)) := by
    intro q
    rw [key q, Real.exp_add, mul_comm]
  simp_rw [key2]
  rw [MeasureTheory.integral_const_mul,
    MeasureTheory.integral_add_right_eq_self (μ := volume)
      (f := fun u : ℝ => Real.exp (-(D * u ^ 2))) (B * p / D),
    integral_exp_neg_mul_sq_norm hD]
  ring

/-- `∫ q, q e^{-(D q² + 2 B p q)} = -(Bp/D) √(π/D) e^{B²p²/D}` for `D > 0`. -/
theorem integral_mul_exp_neg_quadratic_linear {D B p : ℝ} (hD : 0 < D) :
    (∫ q : ℝ, q * Real.exp (-(D * q ^ 2 + 2 * B * p * q)))
      = -(B * p / D) * Real.sqrt (Real.pi / D) * Real.exp (B ^ 2 * p ^ 2 / D) := by
  have hDne : D ≠ 0 := hD.ne'
  have key : ∀ q : ℝ, -(D * q ^ 2 + 2 * B * p * q)
      = -(D * (q + B * p / D) ^ 2) + B ^ 2 * p ^ 2 / D := by
    intro q; field_simp; ring
  have key2 : ∀ q : ℝ, q * Real.exp (-(D * q ^ 2 + 2 * B * p * q))
      = Real.exp (B ^ 2 * p ^ 2 / D) *
        ((fun u : ℝ => u * Real.exp (-(D * u ^ 2))) (q + B * p / D)
          - (B * p / D) * (fun u : ℝ => Real.exp (-(D * u ^ 2))) (q + B * p / D)) := by
    intro q
    rw [key q]
    simp only
    rw [Real.exp_add]
    field_simp
    ring
  simp_rw [key2]
  rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_sub]
  · rw [MeasureTheory.integral_const_mul,
      MeasureTheory.integral_add_right_eq_self (μ := volume)
        (f := fun u : ℝ => u * Real.exp (-(D * u ^ 2))) (B * p / D),
      MeasureTheory.integral_add_right_eq_self (μ := volume)
        (f := fun u : ℝ => Real.exp (-(D * u ^ 2))) (B * p / D),
      integral_x_mul_exp_neg_mul_sq hD, integral_exp_neg_mul_sq_norm hD]
    ring
  · have h := (integrable_mul_exp_neg_mul_sq_norm hD).comp_sub_right (-(B * p / D))
    simpa only [sub_neg_eq_add] using h
  · have h := ((integrable_exp_neg_mul_sq_norm hD).comp_sub_right (-(B * p / D))).const_mul
      (B * p / D)
    simpa only [sub_neg_eq_add, smul_eq_mul] using h

/-- `x² e^{-a x²} ≤ 2/a` for `a > 0`. -/
lemma sq_mul_exp_neg_le {a x : ℝ} (ha : 0 < a) :
    x ^ 2 * Real.exp (-(a * x ^ 2)) ≤ 2 / a := by
  have hpos : 0 < Real.exp (-(a * x ^ 2)) := Real.exp_pos _
  have hpos2 : 0 < Real.exp (a * x ^ 2 / 2) := Real.exp_pos _
  have h2a : (0:ℝ) < 2 / a := by positivity
  have key : x ^ 2 ≤ (2 / a) * Real.exp (a * x ^ 2 / 2) := by
    have h1 := Real.add_one_le_exp (a * x ^ 2 / 2)
    have h3 : (2 / a) * (a * x ^ 2 / 2 + 1) ≤ (2 / a) * Real.exp (a * x ^ 2 / 2) :=
      mul_le_mul_of_nonneg_left h1 h2a.le
    have h4 : (2 / a) * (a * x ^ 2 / 2 + 1) = x ^ 2 + 2 / a := by field_simp; try ring
    rw [h4] at h3
    linarith
  have hexp : Real.exp (a * x ^ 2 / 2) * Real.exp (-(a * x ^ 2))
      = Real.exp (-(a * x ^ 2 / 2)) := by
    rw [← Real.exp_add]; congr 1; ring
  have hle1 : Real.exp (-(a * x ^ 2 / 2)) ≤ 1 := by
    rw [Real.exp_le_one_iff]; nlinarith [sq_nonneg x, ha.le]
  calc x ^ 2 * Real.exp (-(a * x ^ 2))
      ≤ ((2 / a) * Real.exp (a * x ^ 2 / 2)) * Real.exp (-(a * x ^ 2)) :=
        mul_le_mul_of_nonneg_right key hpos.le
    _ = (2 / a) * (Real.exp (a * x ^ 2 / 2) * Real.exp (-(a * x ^ 2))) := by ring
    _ = (2 / a) * Real.exp (-(a * x ^ 2 / 2)) := by rw [hexp]
    _ ≤ (2 / a) * 1 := mul_le_mul_of_nonneg_left hle1 h2a.le
    _ = 2 / a := by ring

/-- The moment integrand of one row is bounded by `(1/a + 1/b)/2`. -/
lemma abs_mul_le_exp_bound {a b τ σ p q : ℝ} (ha : 0 < a) (hb : 0 < b) :
    |p * (τ * p + σ * q)| * Real.exp (-(a * p ^ 2 + b * (τ * p + σ * q) ^ 2))
      ≤ 1 / a + 1 / b := by
  set s := τ * p + σ * q with hs
  have hfac : Real.exp (-(a * p ^ 2 + b * s ^ 2))
      = Real.exp (-(a * p ^ 2)) * Real.exp (-(b * s ^ 2)) := by
    rw [show -(a * p ^ 2 + b * s ^ 2) = -(a * p ^ 2) + -(b * s ^ 2) by ring, Real.exp_add]
  have hp2 : p ^ 2 * Real.exp (-(a * p ^ 2)) ≤ 2 / a := sq_mul_exp_neg_le ha
  have hsq2 : s ^ 2 * Real.exp (-(b * s ^ 2)) ≤ 2 / b := sq_mul_exp_neg_le hb
  have h1 : |p * s| ≤ (p ^ 2 + s ^ 2) / 2 := by
    rw [abs_mul]
    nlinarith [sq_nonneg (|p| - |s|), abs_nonneg p, abs_nonneg s, sq_abs p, sq_abs s]
  have hlea : Real.exp (-(a * p ^ 2)) ≤ 1 := by
    rw [Real.exp_le_one_iff]; nlinarith [sq_nonneg p, ha.le]
  have hleb : Real.exp (-(b * s ^ 2)) ≤ 1 := by
    rw [Real.exp_le_one_iff]; nlinarith [sq_nonneg s, hb.le]
  have hEa : (0:ℝ) ≤ Real.exp (-(a * p ^ 2)) := (Real.exp_pos _).le
  have hEb : (0:ℝ) ≤ Real.exp (-(b * s ^ 2)) := (Real.exp_pos _).le
  have e1 : (p ^ 2 * Real.exp (-(a * p ^ 2))) * Real.exp (-(b * s ^ 2)) ≤ (2 / a) * 1 :=
    mul_le_mul hp2 hleb hEb (by positivity)
  have e2 : (s ^ 2 * Real.exp (-(b * s ^ 2))) * Real.exp (-(a * p ^ 2)) ≤ (2 / b) * 1 :=
    mul_le_mul hsq2 hlea hEa (by positivity)
  have hsplit : ((p ^ 2 + s ^ 2) / 2) * (Real.exp (-(a * p ^ 2)) * Real.exp (-(b * s ^ 2)))
      = (p ^ 2 * Real.exp (-(a * p ^ 2))) * Real.exp (-(b * s ^ 2)) / 2
        + (s ^ 2 * Real.exp (-(b * s ^ 2))) * Real.exp (-(a * p ^ 2)) / 2 := by ring
  calc |p * s| * Real.exp (-(a * p ^ 2 + b * s ^ 2))
      ≤ ((p ^ 2 + s ^ 2) / 2) * (Real.exp (-(a * p ^ 2)) * Real.exp (-(b * s ^ 2))) :=
        mul_le_mul h1 (le_of_eq hfac) (Real.exp_pos (-(a * p ^ 2 + b * s ^ 2))).le (by positivity)
    _ = (p ^ 2 * Real.exp (-(a * p ^ 2))) * Real.exp (-(b * s ^ 2)) / 2
        + (s ^ 2 * Real.exp (-(b * s ^ 2))) * Real.exp (-(a * p ^ 2)) / 2 := hsplit
    _ ≤ (2 / a) * 1 / 2 + (2 / b) * 1 / 2 := by linarith [e1, e2]
    _ = 1 / a + 1 / b := by field_simp

/-- **The mass of the tilted two-dimensional Gaussian.** For `a, b > 0` and `|τ| < 1`,
`E[e^{-a ξ² - b η²}] = ((1+2a)(1+2b) - 4τ²ab)^{-1/2}` for `(ξ,η) ~ N(0, !![1,τ;τ,1])`. -/
theorem integral_rowLaw_mass {τ a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hτ : τ ^ 2 < 1) :
    (∫ w : EuclideanSpace ℝ (Fin 2),
        Real.exp (-(a * (w.ofLp 0) ^ 2 + b * (w.ofLp 1) ^ 2))
        ∂(multivariateGaussian 0 (corrMat τ)))
      = ((1 + 2 * a) * (1 + 2 * b) - 4 * τ ^ 2 * a * b) ^ (-(1 / 2) : ℝ) := by
  set σ := Real.sqrt (1 - τ ^ 2) with hσdef
  have hσ2 : σ ^ 2 = 1 - τ ^ 2 := by
    rw [hσdef]; exact Real.sq_sqrt (by linarith)
  set D := 1 / 2 + b * σ ^ 2 with hDdef
  set B := b * τ * σ with hBdef
  set A₁ := a + b * τ ^ 2 - B ^ 2 / D with hA₁def
  set A₂ := A₁ + 1 / 2 with hA₂def
  set K := (1 + 2 * a) * (1 + 2 * b) - 4 * τ ^ 2 * a * b with hKdef
  have hDpos : 0 < D := by rw [hDdef]; positivity
  have hDA : D * A₂ = K / 4 := by
    have hDne : D ≠ 0 := hDpos.ne'
    have hB2 : B ^ 2 = b ^ 2 * τ ^ 2 * (1 - τ ^ 2) := by
      rw [hBdef, mul_pow, mul_pow, hσ2]
    have hexp : D * A₂ = D * (a + b * τ ^ 2 + 1 / 2) - B ^ 2 := by
      rw [hA₂def, hA₁def]; field_simp; ring
    rw [hexp, hB2, hKdef, hDdef, hσ2]; ring
  have hKpos : 0 < K := by
    have hab : 0 < a * b := mul_pos ha hb
    have h1 : τ ^ 2 * (a * b) < 1 * (a * b) := mul_lt_mul_of_pos_right hτ hab
    rw [hKdef]; nlinarith [h1, ha, hb]
  have hA₂pos : 0 < A₂ := by
    have h4 : (0:ℝ) < K / 4 := by linarith
    by_contra hcon
    push_neg at hcon
    nlinarith [hDA, hDpos, mul_nonpos_of_nonneg_of_nonpos hDpos.le hcon]
  have hτ1 : |τ| ≤ 1 := by
    have h : |τ| < 1 := by rw [abs_lt]; constructor <;> nlinarith [hτ]
    linarith
  -- 1. the row law is the Cholesky image of `γ × γ`
  rw [← rowLaw_eq hτ1]
  rw [integral_map (measurable_rowMap τ).aemeasurable]
  simp only [rowMap_ofLp_zero, rowMap_ofLp_one, ← hσdef]
  · -- 2. iterated Lebesgue form
    rw [integral_prod_gaussianReal_eq _ ?hInt]
    · -- 3. the inner integral
      have hinner : ∀ p : ℝ,
          (∫ q, (gaussianPDFReal 0 1 p * gaussianPDFReal 0 1 q) *
              Real.exp (-(a * p ^ 2 + b * (τ * p + σ * q) ^ 2)))
          = gaussianPDFReal 0 1 p * (Real.sqrt (2 * Real.pi))⁻¹ *
              Real.sqrt (Real.pi / D) * Real.exp (-(A₁ * p ^ 2)) := by
        intro p
        have hpoint : ∀ q : ℝ, (gaussianPDFReal 0 1 p * gaussianPDFReal 0 1 q) *
            Real.exp (-(a * p ^ 2 + b * (τ * p + σ * q) ^ 2))
            = (gaussianPDFReal 0 1 p * ((Real.sqrt (2 * Real.pi))⁻¹ *
                Real.exp (-((a + b * τ ^ 2) * p ^ 2)))) * Real.exp (-(D * q ^ 2 + 2 * B * p * q)) := by
          intro q
          have h1 : gaussianPDFReal 0 1 q
              = (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(q ^ 2) / 2) := by
            rw [gaussianPDFReal_zero_one_apply]
          rw [h1]
          have hexp : Real.exp (-(q ^ 2) / 2) * Real.exp (-(a * p ^ 2 + b * (τ * p + σ * q) ^ 2))
              = Real.exp (-((a + b * τ ^ 2) * p ^ 2)) * Real.exp (-(D * q ^ 2 + 2 * B * p * q)) := by
            rw [← Real.exp_add, ← Real.exp_add]
            congr 1
            simp only [hDdef, hBdef]
            ring
          rw [show gaussianPDFReal 0 1 p * ((Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(q ^ 2) / 2)) *
              Real.exp (-(a * p ^ 2 + b * (τ * p + σ * q) ^ 2))
              = gaussianPDFReal 0 1 p * ((Real.sqrt (2 * Real.pi))⁻¹ *
                (Real.exp (-(q ^ 2) / 2) *
                  Real.exp (-(a * p ^ 2 + b * (τ * p + σ * q) ^ 2)))) by ring]
          rw [hexp]
          ring
        calc (∫ q, (gaussianPDFReal 0 1 p * gaussianPDFReal 0 1 q) *
              Real.exp (-(a * p ^ 2 + b * (τ * p + σ * q) ^ 2)))
            = ∫ q, (gaussianPDFReal 0 1 p * ((Real.sqrt (2 * Real.pi))⁻¹ *
                Real.exp (-((a + b * τ ^ 2) * p ^ 2)))) *
                Real.exp (-(D * q ^ 2 + 2 * B * p * q)) := by
              exact integral_congr_ae (Filter.Eventually.of_forall hpoint)
          _ = (gaussianPDFReal 0 1 p * ((Real.sqrt (2 * Real.pi))⁻¹ *
                Real.exp (-((a + b * τ ^ 2) * p ^ 2)))) *
                ∫ q, Real.exp (-(D * q ^ 2 + 2 * B * p * q)) := by
              rw [MeasureTheory.integral_const_mul]
          _ = (gaussianPDFReal 0 1 p * ((Real.sqrt (2 * Real.pi))⁻¹ *
                Real.exp (-((a + b * τ ^ 2) * p ^ 2)))) *
                (Real.sqrt (Real.pi / D) * Real.exp (B ^ 2 * p ^ 2 / D)) := by
              rw [integral_exp_neg_quadratic_linear hDpos]
          _ = gaussianPDFReal 0 1 p * (Real.sqrt (2 * Real.pi))⁻¹ *
                Real.sqrt (Real.pi / D) * Real.exp (-(A₁ * p ^ 2)) := by
              rw [hA₁def]
              have hE : Real.exp (-((a + b * τ ^ 2) * p ^ 2)) * Real.exp (B ^ 2 * p ^ 2 / D)
                  = Real.exp (-((a + b * τ ^ 2 - B ^ 2 / D) * p ^ 2)) := by
                rw [← Real.exp_add]; congr 1; ring
              rw [← hE]; ring
      -- 4. the outer integral
      have houter : (∫ p, gaussianPDFReal 0 1 p * Real.exp (-(A₁ * p ^ 2)))
          = (Real.sqrt (2 * Real.pi))⁻¹ * Real.sqrt (Real.pi / A₂) := by
        have h1 : ∀ p : ℝ, gaussianPDFReal 0 1 p * Real.exp (-(A₁ * p ^ 2))
            = (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(A₂ * p ^ 2)) := by
          intro p
          rw [gaussianPDFReal_zero_one_apply, mul_assoc, ← Real.exp_add]
          congr 2
          rw [hA₂def]; ring
        simp only [h1]
        rw [MeasureTheory.integral_const_mul, integral_exp_neg_mul_sq_norm hA₂pos]
      have h2 : ∀ p : ℝ, gaussianPDFReal 0 1 p * (Real.sqrt (2 * Real.pi))⁻¹ *
            Real.sqrt (Real.pi / D) * Real.exp (-(A₁ * p ^ 2))
          = ((Real.sqrt (2 * Real.pi))⁻¹ * Real.sqrt (Real.pi / D)) *
            (gaussianPDFReal 0 1 p * Real.exp (-(A₁ * p ^ 2))) := by
        intro p; ring
      simp only [hinner, h2]
      rw [MeasureTheory.integral_const_mul, houter]
      -- 5. the constant
      have hsq : Real.sqrt (Real.pi / D) * Real.sqrt (Real.pi / A₂)
          = Real.pi / Real.sqrt (D * A₂) := by
        rw [← Real.sqrt_mul (by positivity)]
        rw [show Real.pi / D * (Real.pi / A₂) = Real.pi ^ 2 / (D * A₂) by field_simp]
        rw [Real.sqrt_div (by positivity), Real.sqrt_sq Real.pi_pos.le]
      have hconst : (Real.sqrt (2 * Real.pi))⁻¹ * Real.sqrt (Real.pi / D) *
            ((Real.sqrt (2 * Real.pi))⁻¹ * Real.sqrt (Real.pi / A₂))
          = 1 / (2 * Real.sqrt (D * A₂)) := by
        have hsq2 : Real.sqrt (2 * Real.pi) * Real.sqrt (2 * Real.pi) = 2 * Real.pi :=
          Real.mul_self_sqrt (by positivity)
        have hD2 : Real.sqrt (D * A₂) * Real.sqrt (D * A₂) = D * A₂ :=
          Real.mul_self_sqrt (by positivity)
        have hne : Real.sqrt (2 * Real.pi) ≠ 0 := (Real.sqrt_pos.mpr (by positivity)).ne'
        have hne2 : Real.sqrt (D * A₂) ≠ 0 :=
          (Real.sqrt_pos.mpr (mul_pos hDpos hA₂pos)).ne'
        have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
        rw [show (Real.sqrt (2 * Real.pi))⁻¹ * Real.sqrt (Real.pi / D) *
            ((Real.sqrt (2 * Real.pi))⁻¹ * Real.sqrt (Real.pi / A₂))
            = (Real.sqrt (2 * Real.pi) * Real.sqrt (2 * Real.pi))⁻¹ *
              (Real.sqrt (Real.pi / D) * Real.sqrt (Real.pi / A₂)) by
              rw [mul_inv]; ring]
        rw [hsq2, hsq]
        field_simp
      rw [hconst]
      have hK4' : Real.sqrt K = 2 * Real.sqrt (D * A₂) := by
        rw [show K = 4 * (D * A₂) by rw [hDA]; ring,
          Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 4)]
        norm_num
      rw [← hK4']
      rw [Real.rpow_neg hKpos.le, ← Real.sqrt_eq_rpow]
      norm_num
    · -- integrability of the composite mass integrand
      refine Integrable.mono (integrable_const (1:ℝ))
        (by fun_prop : Measurable (fun z : ℝ × ℝ =>
          Real.exp (-(a * z.1 ^ 2 + b * (τ * z.1 + σ * z.2) ^ 2)))).aestronglyMeasurable ?_
      filter_upwards with z
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.norm_eq_abs, abs_one]
      exact Real.exp_le_one_iff.mpr
        (by nlinarith [sq_nonneg z.1, sq_nonneg (τ * z.1 + σ * z.2), ha.le, hb.le])
  · exact (by fun_prop : Measurable (fun w : EuclideanSpace ℝ (Fin 2) =>
      Real.exp (-(a * (w.ofLp 0) ^ 2 + b * (w.ofLp 1) ^ 2)))).aestronglyMeasurable

/-- Integrability of `q ↦ e^{-(Dq²+2Bpq)}` on the line. -/
theorem integrable_exp_neg_quadratic_linear {D B p : ℝ} (hD : 0 < D) :
    Integrable (fun q : ℝ => Real.exp (-(D * q ^ 2 + 2 * B * p * q))) volume := by
  have hDne : D ≠ 0 := hD.ne'
  have key : ∀ q : ℝ, -(D * q ^ 2 + 2 * B * p * q)
      = -(D * (q + B * p / D) ^ 2) + B ^ 2 * p ^ 2 / D := by
    intro q; field_simp; ring
  have hbase : Integrable (fun q : ℝ => Real.exp (-(D * (q + B * p / D) ^ 2))) volume := by
    have h := (integrable_exp_neg_mul_sq_norm hD).comp_sub_right (-(B * p / D))
    simpa only [sub_neg_eq_add] using h
  refine (hbase.const_mul (Real.exp (B ^ 2 * p ^ 2 / D))).congr ?_
  filter_upwards with q
  rw [key q, Real.exp_add]
  ring

/-- Integrability of `q ↦ q e^{-(Dq²+2Bpq)}` on the line. -/
theorem integrable_mul_exp_neg_quadratic_linear {D B p : ℝ} (hD : 0 < D) :
    Integrable (fun q : ℝ => q * Real.exp (-(D * q ^ 2 + 2 * B * p * q))) volume := by
  have hDne : D ≠ 0 := hD.ne'
  have key : ∀ q : ℝ, q * Real.exp (-(D * q ^ 2 + 2 * B * p * q))
      = Real.exp (B ^ 2 * p ^ 2 / D) *
        ((fun u : ℝ => u * Real.exp (-(D * u ^ 2))) (q + B * p / D)
          - (B * p / D) * (fun u : ℝ => Real.exp (-(D * u ^ 2))) (q + B * p / D)) := by
    intro q
    rw [show -(D * q ^ 2 + 2 * B * p * q)
      = -(D * (q + B * p / D) ^ 2) + B ^ 2 * p ^ 2 / D by field_simp; ring]
    simp only
    rw [Real.exp_add]
    field_simp
    ring
  have h1 : Integrable (fun q : ℝ =>
      (fun u : ℝ => u * Real.exp (-(D * u ^ 2))) (q + B * p / D)) volume := by
    have h := (integrable_mul_exp_neg_mul_sq_norm hD).comp_sub_right (-(B * p / D))
    simpa only [sub_neg_eq_add] using h
  have h2 : Integrable (fun q : ℝ =>
      (B * p / D) * (fun u : ℝ => Real.exp (-(D * u ^ 2))) (q + B * p / D)) volume := by
    have h := ((integrable_exp_neg_mul_sq_norm hD).comp_sub_right (-(B * p / D))).const_mul
      (B * p / D)
    simpa only [sub_neg_eq_add, smul_eq_mul] using h
  refine ((h1.sub h2).const_mul (Real.exp (B ^ 2 * p ^ 2 / D))).congr ?_
  filter_upwards with q
  exact (key q).symm

/-- **The first moment of the tilted two-dimensional Gaussian.** For `a, b > 0`, `|τ| < 1`,
`E[ξη e^{-a ξ² - b η²}] = τ ((1+2a)(1+2b) - 4τ²ab)^{-3/2}`. -/
theorem integral_rowLaw_moment {τ a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hτ : τ ^ 2 < 1) :
    (∫ w : EuclideanSpace ℝ (Fin 2),
        (w.ofLp 0 * w.ofLp 1) * Real.exp (-(a * (w.ofLp 0) ^ 2 + b * (w.ofLp 1) ^ 2))
        ∂(multivariateGaussian 0 (corrMat τ)))
      = τ * ((1 + 2 * a) * (1 + 2 * b) - 4 * τ ^ 2 * a * b) ^ (-(3 / 2) : ℝ) := by
  set σ := Real.sqrt (1 - τ ^ 2) with hσdef
  have hσ2 : σ ^ 2 = 1 - τ ^ 2 := by
    rw [hσdef]; exact Real.sq_sqrt (by linarith)
  set D := 1 / 2 + b * σ ^ 2 with hDdef
  set B := b * τ * σ with hBdef
  set A₁ := a + b * τ ^ 2 - B ^ 2 / D with hA₁def
  set A₂ := A₁ + 1 / 2 with hA₂def
  set K := (1 + 2 * a) * (1 + 2 * b) - 4 * τ ^ 2 * a * b with hKdef
  have hDpos : 0 < D := by rw [hDdef]; positivity
  have hDA : D * A₂ = K / 4 := by
    have hDne : D ≠ 0 := hDpos.ne'
    have hB2 : B ^ 2 = b ^ 2 * τ ^ 2 * (1 - τ ^ 2) := by
      rw [hBdef, mul_pow, mul_pow, hσ2]
    have hexp : D * A₂ = D * (a + b * τ ^ 2 + 1 / 2) - B ^ 2 := by
      rw [hA₂def, hA₁def]; field_simp; ring
    rw [hexp, hB2, hKdef, hDdef, hσ2]; ring
  have hKpos : 0 < K := by
    have hab : 0 < a * b := mul_pos ha hb
    have h1 : τ ^ 2 * (a * b) < 1 * (a * b) := mul_lt_mul_of_pos_right hτ hab
    rw [hKdef]; nlinarith [h1, ha, hb]
  have hA₂pos : 0 < A₂ := by
    have h4 : (0:ℝ) < K / 4 := by linarith
    by_contra hcon
    push_neg at hcon
    nlinarith [hDA, hDpos, mul_nonpos_of_nonneg_of_nonpos hDpos.le hcon]
  have hτ1 : |τ| ≤ 1 := by
    have h : |τ| < 1 := by rw [abs_lt]; constructor <;> nlinarith [hτ]
    linarith
  rw [← rowLaw_eq hτ1]
  rw [integral_map (measurable_rowMap τ).aemeasurable]
  simp only [rowMap_ofLp_zero, rowMap_ofLp_one, ← hσdef]
  · rw [integral_prod_gaussianReal_eq _ ?hInt]
    · have hinner : ∀ p : ℝ,
          (∫ q, (gaussianPDFReal 0 1 p * gaussianPDFReal 0 1 q) *
              ((p * (τ * p + σ * q)) * Real.exp (-(a * p ^ 2 + b * (τ * p + σ * q) ^ 2))))
          = gaussianPDFReal 0 1 p * (Real.sqrt (2 * Real.pi))⁻¹ *
              Real.sqrt (Real.pi / D) * (p ^ 2 * (τ - σ * B / D) * Real.exp (-(A₁ * p ^ 2))) := by
        intro p
        have hpt : ∀ q : ℝ,
            Real.exp (-(q ^ 2) / 2) * Real.exp (-(a * p ^ 2 + b * (τ * p + σ * q) ^ 2))
              = Real.exp (-((a + b * τ ^ 2) * p ^ 2)) * Real.exp (-(D * q ^ 2 + 2 * B * p * q)) := by
          intro q
          rw [← Real.exp_add, ← Real.exp_add]
          congr 1
          simp only [hDdef, hBdef]
          ring
        have hpoint : ∀ q : ℝ, (gaussianPDFReal 0 1 p * gaussianPDFReal 0 1 q) *
            ((p * (τ * p + σ * q)) * Real.exp (-(a * p ^ 2 + b * (τ * p + σ * q) ^ 2)))
            = (gaussianPDFReal 0 1 p * (Real.sqrt (2 * Real.pi))⁻¹) *
              ((p ^ 2 * τ * Real.exp (-((a + b * τ ^ 2) * p ^ 2))) *
                  Real.exp (-(D * q ^ 2 + 2 * B * p * q))
               + (p * σ * Real.exp (-((a + b * τ ^ 2) * p ^ 2))) *
                  (q * Real.exp (-(D * q ^ 2 + 2 * B * p * q)))) := by
          intro q
          have h1 : gaussianPDFReal 0 1 q
              = (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(q ^ 2) / 2) := by
            rw [gaussianPDFReal_zero_one_apply]
          rw [h1,
            show gaussianPDFReal 0 1 p * ((Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(q ^ 2) / 2)) *
                ((p * (τ * p + σ * q)) * Real.exp (-(a * p ^ 2 + b * (τ * p + σ * q) ^ 2)))
              = (gaussianPDFReal 0 1 p * (Real.sqrt (2 * Real.pi))⁻¹) *
                ((p * (τ * p + σ * q)) * (Real.exp (-(q ^ 2) / 2) *
                  Real.exp (-(a * p ^ 2 + b * (τ * p + σ * q) ^ 2)))) by ring,
            hpt q]
          ring
        have hInt1 : Integrable (fun q : ℝ =>
            (p ^ 2 * τ * Real.exp (-((a + b * τ ^ 2) * p ^ 2))) *
              Real.exp (-(D * q ^ 2 + 2 * B * p * q))) volume :=
          (integrable_exp_neg_quadratic_linear hDpos).const_mul _
        have hInt2 : Integrable (fun q : ℝ =>
            (p * σ * Real.exp (-((a + b * τ ^ 2) * p ^ 2))) *
              (q * Real.exp (-(D * q ^ 2 + 2 * B * p * q)))) volume :=
          (integrable_mul_exp_neg_quadratic_linear hDpos).const_mul _
        calc (∫ q, (gaussianPDFReal 0 1 p * gaussianPDFReal 0 1 q) *
              ((p * (τ * p + σ * q)) * Real.exp (-(a * p ^ 2 + b * (τ * p + σ * q) ^ 2))))
            = ∫ q, (gaussianPDFReal 0 1 p * (Real.sqrt (2 * Real.pi))⁻¹) *
              ((p ^ 2 * τ * Real.exp (-((a + b * τ ^ 2) * p ^ 2))) *
                  Real.exp (-(D * q ^ 2 + 2 * B * p * q))
               + (p * σ * Real.exp (-((a + b * τ ^ 2) * p ^ 2))) *
                  (q * Real.exp (-(D * q ^ 2 + 2 * B * p * q)))) :=
              integral_congr_ae (Filter.Eventually.of_forall hpoint)
          _ = (gaussianPDFReal 0 1 p * (Real.sqrt (2 * Real.pi))⁻¹) *
              (((p ^ 2 * τ * Real.exp (-((a + b * τ ^ 2) * p ^ 2))) *
                  (∫ q, Real.exp (-(D * q ^ 2 + 2 * B * p * q))))
               + ((p * σ * Real.exp (-((a + b * τ ^ 2) * p ^ 2))) *
                  (∫ q, q * Real.exp (-(D * q ^ 2 + 2 * B * p * q))))) := by
              rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_add hInt1 hInt2,
                MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
          _ = gaussianPDFReal 0 1 p * (Real.sqrt (2 * Real.pi))⁻¹ *
              Real.sqrt (Real.pi / D) * (p ^ 2 * (τ - σ * B / D) * Real.exp (-(A₁ * p ^ 2))) := by
              have hE : Real.exp (-((a + b * τ ^ 2) * p ^ 2)) * Real.exp (B ^ 2 * p ^ 2 / D)
                  = Real.exp (-(A₁ * p ^ 2)) := by
                rw [hA₁def, ← Real.exp_add]; congr 1; ring
              rw [integral_exp_neg_quadratic_linear hDpos,
                integral_mul_exp_neg_quadratic_linear hDpos, ← hE]
              ring
      have h2 : ∀ p : ℝ, gaussianPDFReal 0 1 p * (Real.sqrt (2 * Real.pi))⁻¹ *
            Real.sqrt (Real.pi / D) * (p ^ 2 * (τ - σ * B / D) * Real.exp (-(A₁ * p ^ 2)))
          = ((Real.sqrt (2 * Real.pi))⁻¹ * Real.sqrt (Real.pi / D)) *
            (gaussianPDFReal 0 1 p * (p ^ 2 * (τ - σ * B / D) * Real.exp (-(A₁ * p ^ 2)))) := by
        intro p; ring
      simp only [hinner, h2]
      have houter : (∫ p, gaussianPDFReal 0 1 p *
            (p ^ 2 * (τ - σ * B / D) * Real.exp (-(A₁ * p ^ 2))))
          = (τ - σ * B / D) * ((Real.sqrt (2 * Real.pi))⁻¹ *
              (Real.sqrt Real.pi / (2 * A₂ ^ ((3:ℝ)/2)))) := by
        have h1 : ∀ p : ℝ, gaussianPDFReal 0 1 p *
            (p ^ 2 * (τ - σ * B / D) * Real.exp (-(A₁ * p ^ 2)))
            = (τ - σ * B / D) * ((Real.sqrt (2 * Real.pi))⁻¹ *
                (p ^ 2 * Real.exp (-(A₂ * p ^ 2)))) := by
          intro p
          have hE : Real.exp (-(p ^ 2) / 2) * Real.exp (-(A₁ * p ^ 2))
              = Real.exp (-(A₂ * p ^ 2)) := by
            rw [← Real.exp_add]; congr 1; rw [hA₂def]; ring
          rw [gaussianPDFReal_zero_one_apply, ← hE]
          ring
        simp only [h1]
        rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
          integral_sq_mul_exp_neg_mul_sq hA₂pos]
      rw [MeasureTheory.integral_const_mul, houter]
      -- the constant
      have hτB : τ - σ * B / D = τ / (2 * D) := by
        rw [hBdef, hDdef]
        have hDne : (1/2 + b * σ ^ 2) ≠ 0 := by positivity
        field_simp
        nlinarith [hσ2]
      rw [hτB]
      have hsqrt_div : Real.sqrt (Real.pi / D) = Real.sqrt Real.pi / Real.sqrt D :=
        Real.sqrt_div Real.pi_pos.le D
      have hA23 : A₂ ^ ((3:ℝ)/2) = A₂ * Real.sqrt A₂ := by
        rw [show ((3:ℝ)/2) = 1 + 1/2 by norm_num, Real.rpow_add hA₂pos, Real.rpow_one,
          Real.sqrt_eq_rpow]
      have h1pi : Real.sqrt (2 * Real.pi) * Real.sqrt (2 * Real.pi) = 2 * Real.pi :=
        Real.mul_self_sqrt (by positivity)
      have h2pi : Real.sqrt Real.pi * Real.sqrt Real.pi = Real.pi :=
        Real.mul_self_sqrt Real.pi_pos.le
      have h3D : Real.sqrt D * Real.sqrt D = D := Real.mul_self_sqrt hDpos.le
      have h4A : Real.sqrt A₂ * Real.sqrt A₂ = A₂ := Real.mul_self_sqrt hA₂pos.le
      have h4pos : (0:ℝ) < 4 * (D * A₂) := by positivity
      have hK4 : K = 4 * (D * A₂) := by rw [hDA]; ring
      rw [hK4]
      -- substitute the square roots by atoms
      set sd := Real.sqrt D with hsd
      set sa := Real.sqrt A₂ with hsa
      set sv := Real.sqrt Real.pi with hsv
      set su := Real.sqrt (2 * Real.pi) with hsu
      have hDeq : D = sd * sd := by
        rw [hsd]; exact (Real.mul_self_sqrt hDpos.le).symm
      have hAeq : A₂ = sa * sa := by
        rw [hsa]; exact (Real.mul_self_sqrt hA₂pos.le).symm
      have hA23 : A₂ ^ ((3:ℝ)/2) = A₂ * sa := by
        rw [show ((3:ℝ)/2) = 1 + 1/2 by norm_num, Real.rpow_add hA₂pos, Real.rpow_one, hsa,
          Real.sqrt_eq_rpow]
      have hseq : (D * A₂) ^ ((3:ℝ)/2) = D * sd * (A₂ * sa) := by
        rw [show ((3:ℝ)/2) = 1 + 1/2 by norm_num,
          Real.rpow_add (by positivity : (0:ℝ) < D * A₂), Real.rpow_one,
          Real.mul_rpow hDpos.le hA₂pos.le, hsd, hsa, Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
        ring
      have h4pow : (4:ℝ) ^ ((3:ℝ)/2) = 8 := by
        rw [show ((3:ℝ)/2) = 1 + 1/2 by norm_num, Real.rpow_add (by norm_num), Real.rpow_one,
          show (4:ℝ) ^ ((1:ℝ)/2) = 2 by rw [← Real.sqrt_eq_rpow]; norm_num]
        norm_num
      have h4pos : (0:ℝ) < 4 * (D * A₂) := by positivity
      rw [Real.rpow_neg h4pos.le,
        Real.mul_rpow (by norm_num : (0:ℝ) ≤ 4) (le_of_lt (mul_pos hDpos hA₂pos)), h4pow, hseq,
        hsqrt_div, hA23]
      rw [hDeq, hAeq]
      have hsvv : sv * sv = Real.pi := by rw [hsv]; exact Real.mul_self_sqrt Real.pi_pos.le
      have hsuu : su * su = 2 * Real.pi := by rw [hsu]; exact Real.mul_self_sqrt (by positivity)
      have hsdne : sd ≠ 0 := by
        rw [hsd]; exact (Real.sqrt_pos.mpr hDpos).ne'
      have hsane : sa ≠ 0 := by
        rw [hsa]; exact (Real.sqrt_pos.mpr hA₂pos).ne'
      have hsvne : sv ≠ 0 := by
        rw [hsv]; exact (Real.sqrt_pos.mpr Real.pi_pos).ne'
      have hsune : su ≠ 0 := by
        rw [hsu]; exact (Real.sqrt_pos.mpr (by positivity)).ne'
      have hπne : Real.pi ≠ 0 := Real.pi_ne_zero
      have hsvv' : sv ^ 2 = Real.pi := by rw [sq, hsvv]
      have hsuu' : su ^ 2 = 2 * Real.pi := by rw [sq, hsuu]
      field_simp
      rw [hsvv', hsuu']
      ring
    · refine Integrable.mono (integrable_const (1 / a + 1 / b))
        (by fun_prop : Measurable (fun z : ℝ × ℝ =>
          (z.1 * (τ * z.1 + σ * z.2)) *
            Real.exp (-(a * z.1 ^ 2 + b * (τ * z.1 + σ * z.2) ^ 2)))).aestronglyMeasurable ?_
      filter_upwards with z
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _), Real.norm_eq_abs,
        abs_of_pos (by positivity : (0:ℝ) < 1 / a + 1 / b)]
      exact abs_mul_le_exp_bound ha hb
  · exact (by fun_prop : Measurable (fun w : EuclideanSpace ℝ (Fin 2) =>
      (w.ofLp 0 * w.ofLp 1) *
        Real.exp (-(a * (w.ofLp 0) ^ 2 + b * (w.ofLp 1) ^ 2)))).aestronglyMeasurable

end Grothendieck

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators Real RealInnerProductSpace NNReal

namespace Grothendieck

theorem isProb_multivariateGaussian (μ : EuclideanSpace ℝ (Fin 2))
    (S : Matrix (Fin 2) (Fin 2) ℝ) :
    IsProbabilityMeasure (multivariateGaussian μ S) :=
  (inferInstance : IsGaussian (multivariateGaussian μ S)).toIsProbabilityMeasure

/-- Integrability of the row mass factor against the row law. -/
theorem integrable_row_exp {τ a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Integrable (fun w : EuclideanSpace ℝ (Fin 2) =>
      Real.exp (-(a * (w.ofLp 0) ^ 2 + b * (w.ofLp 1) ^ 2)))
      (multivariateGaussian 0 (corrMat τ)) := by
  haveI := isProb_multivariateGaussian 0 (corrMat τ)
  refine Integrable.mono (integrable_const (1:ℝ))
    (by fun_prop : Measurable (fun w : EuclideanSpace ℝ (Fin 2) =>
      Real.exp (-(a * (w.ofLp 0) ^ 2 + b * (w.ofLp 1) ^ 2)))).aestronglyMeasurable ?_
  filter_upwards with w
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.norm_eq_abs, abs_one]
  exact Real.exp_le_one_iff.mpr
    (by nlinarith [sq_nonneg (w.ofLp 0), sq_nonneg (w.ofLp 1), ha.le, hb.le])

/-- Integrability of the row moment factor against the row law. -/
theorem integrable_row_moment {τ a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Integrable (fun w : EuclideanSpace ℝ (Fin 2) =>
      (w.ofLp 0 * w.ofLp 1) * Real.exp (-(a * (w.ofLp 0) ^ 2 + b * (w.ofLp 1) ^ 2)))
      (multivariateGaussian 0 (corrMat τ)) := by
  haveI := isProb_multivariateGaussian 0 (corrMat τ)
  refine Integrable.mono (integrable_const (1 / a + 1 / b))
    (by fun_prop : Measurable (fun w : EuclideanSpace ℝ (Fin 2) =>
      (w.ofLp 0 * w.ofLp 1) *
        Real.exp (-(a * (w.ofLp 0) ^ 2 + b * (w.ofLp 1) ^ 2)))).aestronglyMeasurable ?_
  filter_upwards with w
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _), Real.norm_eq_abs,
    abs_of_pos (by positivity : (0:ℝ) < 1 / a + 1 / b)]
  have h := abs_mul_le_exp_bound (a := a) (b := b) (τ := 0) (σ := 1)
    (p := w.ofLp 0) (q := w.ofLp 1) ha hb
  simpa using h

/-- **The row Fubini (step (i) of Leaf 1).** For `r ≥ 1`, `|τ| < 1`, `a, b > 0`,
`∫ W, ⟨col W 0, col W 1⟩ e^{-(a‖col W 0‖² + b‖col W 1‖²)} ∂(reducedLaw r τ)`
`= r · A · C^{r-1} = r τ C^{r+2}` with `C = ((1+2a)(1+2b) - 4τ²ab)^{-1/2}`. -/
theorem integral_reducedLaw_row {r : ℕ} {τ a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hτ : τ ^ 2 < 1) :
    (∫ W : Fin r → EuclideanSpace ℝ (Fin 2),
        (∑ i, (W i).ofLp 0 * (W i).ofLp 1) *
          Real.exp (-(a * ∑ i, ((W i).ofLp 0) ^ 2 + b * ∑ i, ((W i).ofLp 1) ^ 2))
        ∂(reducedLaw r τ))
      = r * τ * ((1 + 2 * a) * (1 + 2 * b) - 4 * τ ^ 2 * a * b) ^ (-(((r : ℝ) + 2) / 2) : ℝ) := by
  classical
  set K := (1 + 2 * a) * (1 + 2 * b) - 4 * τ ^ 2 * a * b with hKdef
  have hτ1 : |τ| ≤ 1 := by
    have h : |τ| < 1 := by rw [abs_lt]; constructor <;> nlinarith [hτ]
    linarith
  have hμ : reducedLaw r τ = Measure.pi (fun _ : Fin r => multivariateGaussian 0 (corrMat τ)) :=
    rfl
  rcases Nat.eq_zero_or_pos r with hr | hr
  · subst hr
    simp [reducedLaw]
  · -- pointwise decomposition
    have hpoint : ∀ W : Fin r → EuclideanSpace ℝ (Fin 2),
        (∑ i, (W i).ofLp 0 * (W i).ofLp 1) *
          Real.exp (-(a * ∑ i, ((W i).ofLp 0) ^ 2 + b * ∑ i, ((W i).ofLp 1) ^ 2))
        = ∑ i, ∏ j, (if j = i then (W j).ofLp 0 * (W j).ofLp 1 else 1) *
            Real.exp (-(a * (W j).ofLp 0 ^ 2 + b * (W j).ofLp 1 ^ 2)) := by
      intro W
      have hsum : a * ∑ i, ((W i).ofLp 0) ^ 2 + b * ∑ i, ((W i).ofLp 1) ^ 2
          = ∑ i, (a * (W i).ofLp 0 ^ 2 + b * (W i).ofLp 1 ^ 2) := by
        rw [Finset.mul_sum, Finset.mul_sum, Finset.sum_add_distrib]
      have hexp : Real.exp (-(a * ∑ i, ((W i).ofLp 0) ^ 2 + b * ∑ i, ((W i).ofLp 1) ^ 2))
          = ∏ i, Real.exp (-(a * (W i).ofLp 0 ^ 2 + b * (W i).ofLp 1 ^ 2)) := by
        rw [hsum, ← Finset.sum_neg_distrib, ← Real.exp_sum]
      rw [hexp, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      have h1 : (∏ j, (if j = i then (W j).ofLp 0 * (W j).ofLp 1 else 1))
          = (W i).ofLp 0 * (W i).ofLp 1 := by
        rw [Finset.prod_eq_single i]
        · simp
        · intro j _ hji; simp [hji]
        · intro h; exact absurd (Finset.mem_univ i) h
      rw [Finset.prod_mul_distrib, h1]
    -- integrability of each summand
    have hφ : Integrable (fun w : EuclideanSpace ℝ (Fin 2) =>
        (w.ofLp 0 * w.ofLp 1) * Real.exp (-(a * (w.ofLp 0) ^ 2 + b * (w.ofLp 1) ^ 2)))
        (multivariateGaussian 0 (corrMat τ)) := integrable_row_moment ha hb
    have hψ : Integrable (fun w : EuclideanSpace ℝ (Fin 2) =>
        Real.exp (-(a * (w.ofLp 0) ^ 2 + b * (w.ofLp 1) ^ 2)))
        (multivariateGaussian 0 (corrMat τ)) := integrable_row_exp ha hb
    have hInt : ∀ i : Fin r, Integrable (fun W : Fin r → EuclideanSpace ℝ (Fin 2) =>
        ∏ j, (if j = i then (W j).ofLp 0 * (W j).ofLp 1 else 1) *
          Real.exp (-(a * (W j).ofLp 0 ^ 2 + b * (W j).ofLp 1 ^ 2)))
        (Measure.pi (fun _ : Fin r => multivariateGaussian 0 (corrMat τ))) := by
      intro i
      have h := Integrable.fintype_prod
        (μ := fun _ : Fin r => multivariateGaussian 0 (corrMat τ))
        (f := fun (j : Fin r) (w : EuclideanSpace ℝ (Fin 2)) =>
          (if j = i then (w.ofLp 0 * w.ofLp 1) else 1) *
            Real.exp (-(a * (w.ofLp 0) ^ 2 + b * (w.ofLp 1) ^ 2)))
        (fun j => by
          by_cases hji : j = i
          · subst hji; simpa using hφ
          · simpa [hji] using hψ)
      simpa using h
    rw [hμ]
    simp only [hpoint]
    rw [MeasureTheory.integral_finset_sum]
    swap
    · intro i _
      exact hInt i
    -- each summand is a product integral
    have hval : ∀ i : Fin r,
        (∫ W : Fin r → EuclideanSpace ℝ (Fin 2),
          ∏ j, (if j = i then (W j).ofLp 0 * (W j).ofLp 1 else 1) *
            Real.exp (-(a * (W j).ofLp 0 ^ 2 + b * (W j).ofLp 1 ^ 2))
          ∂(Measure.pi (fun _ : Fin r => multivariateGaussian 0 (corrMat τ))))
        = τ * K ^ (-(3/2) : ℝ) * (K ^ (-(1/2) : ℝ)) ^ (r - 1) := by
      intro i
      rw [integral_fintype_prod_eq_prod
        (μ := fun _ : Fin r => multivariateGaussian 0 (corrMat τ))
        (f := fun (j : Fin r) (w : EuclideanSpace ℝ (Fin 2)) =>
          (if j = i then (w.ofLp 0 * w.ofLp 1) else 1) *
            Real.exp (-(a * (w.ofLp 0) ^ 2 + b * (w.ofLp 1) ^ 2)))]
      have hstep : ∀ j : Fin r, (∫ w : EuclideanSpace ℝ (Fin 2),
          (if j = i then (w.ofLp 0 * w.ofLp 1) else 1) *
            Real.exp (-(a * (w.ofLp 0) ^ 2 + b * (w.ofLp 1) ^ 2))
          ∂(multivariateGaussian 0 (corrMat τ)))
          = (if j = i then τ * K ^ (-(3/2) : ℝ) else K ^ (-(1/2) : ℝ)) := by
        intro j
        by_cases hji : j = i
        · subst hji
          simp only [if_true]
          rw [show (fun w : EuclideanSpace ℝ (Fin 2) =>
              (w.ofLp 0 * w.ofLp 1) * Real.exp (-(a * (w.ofLp 0) ^ 2 + b * (w.ofLp 1) ^ 2)))
              = (fun w => (w.ofLp 0 * w.ofLp 1) *
                Real.exp (-(a * (w.ofLp 0) ^ 2 + b * (w.ofLp 1) ^ 2))) from rfl,
            integral_rowLaw_moment ha hb hτ, hKdef]
        · subst_vars
          simp only [if_false, one_mul, hji]
          rw [integral_rowLaw_mass ha hb hτ, hKdef]
      simp only [hstep]
      rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ i)]
      have h1 : ∏ j ∈ Finset.univ.erase i, (if j = i then τ * K ^ (-(3/2) : ℝ) else K ^ (-(1/2) : ℝ))
          = ∏ _j ∈ Finset.univ.erase i, K ^ (-(1/2) : ℝ) := by
        refine Finset.prod_congr rfl fun j hj => ?_
        rw [if_neg (Finset.ne_of_mem_erase hj)]
      rw [h1, Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ,
        Fintype.card_fin, if_pos rfl]
      ring
    simp only [hval]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    -- the constant
    have hKpos : 0 < K := by
      have hab : 0 < a * b := mul_pos ha hb
      have h1 : τ ^ 2 * (a * b) < 1 * (a * b) := mul_lt_mul_of_pos_right hτ hab
      rw [hKdef]; nlinarith [h1, ha, hb]
    have hcast : ((r - 1 : ℕ) : ℝ) = (r : ℝ) - 1 := by
      have : 1 ≤ r := hr
      push_cast [Nat.cast_sub this]
      ring
    rw [show (K ^ (-(1/2) : ℝ)) ^ (r - 1) = K ^ (-(1/2) * ((r - 1 : ℕ) : ℝ)) from by
      rw [← Real.rpow_natCast (K ^ (-(1/2) : ℝ)) (r - 1), ← Real.rpow_mul hKpos.le]]
    have hKadd := Real.rpow_add hKpos (-(3/2:ℝ)) (-(1/2) * ((r - 1 : ℕ) : ℝ))
    rw [mul_assoc τ, ← hKadd]
    have hexp : -(3/2 : ℝ) + -(1/2) * ((r : ℝ) - 1) = -(((r : ℝ) + 2) / 2) := by ring
    rw [hcast, hexp]
    ring

end Grothendieck

open MeasureTheory
open scoped BigOperators Real Topology

namespace Grothendieck

/-- The inner product of the two columns is the sum of coordinatewise products. -/
theorem inner_colFun (r : ℕ) (W : Fin r → EuclideanSpace ℝ (Fin 2)) :
    inner ℝ (colFun r 0 W) (colFun r 1 W) = ∑ i, (W i).ofLp 0 * (W i).ofLp 1 := by
  simp [colFun, EuclideanSpace.inner_eq_star_dotProduct, dotProduct, mul_comm]

/-- The squared norm of a column is the sum of the squares of its coordinates. -/
theorem norm_sq_colFun (r : ℕ) (j : Fin 2) (W : Fin r → EuclideanSpace ℝ (Fin 2)) :
    ‖colFun r j W‖ ^ 2 = ∑ i, ((W i).ofLp j) ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp [colFun]

/-- The positive quadrant is almost all of `planeMeasure`. -/
theorem ae_pos_planeMeasure : ∀ᵐ p ∂planeMeasure, 0 < p.1 ∧ 0 < p.2 := by
  unfold planeMeasure
  have h1 : ∀ᵐ s ∂(volume.restrict (Set.Ioi (0:ℝ))), 0 < s := ae_restrict_mem measurableSet_Ioi
  have h2 : ∀ᵐ t ∂(volume.restrict (Set.Ioi (0:ℝ))), 0 < t := ae_restrict_mem measurableSet_Ioi
  have hset : MeasurableSet {p : ℝ × ℝ | 0 < p.1 ∧ 0 < p.2} :=
    (measurableSet_lt measurable_const measurable_fst).inter
      (measurableSet_lt measurable_const measurable_snd)
  rw [Measure.ae_prod_iff_ae_ae hset]
  filter_upwards [h1] with a ha
  filter_upwards [h2] with b hb
  exact ⟨ha, hb⟩

/-- **The kernel form of the rounding expectation.** The expectation is `π⁻¹ r τ` times the double
Laplace integral of the kernel `(st)^{-1/2} C^{r+2}`. -/
theorem reducedExpectation_eq_kernel_proof (r : ℕ) (hr : 2 ≤ r) {τ : ℝ} (hτ : τ ^ 2 < 1) :
    (∫ W, reducedIntegrand r W ∂(reducedLaw r τ))
      = Real.pi⁻¹ * ∫ p, ((p.1 * p.2) ^ (-(1/2) : ℝ) *
          ((r : ℝ) * τ *
            ((1 + 2 * p.1) * (1 + 2 * p.2) - 4 * τ ^ 2 * p.1 * p.2) ^ (-(((r : ℝ) + 2) / 2) : ℝ)))
          ∂planeMeasure := by
  rw [fubini_swap_proved r τ]
  congr 1
  refine integral_congr_ae ?_
  filter_upwards [ae_pos_planeMeasure] with p hp
  obtain ⟨hp1, hp2⟩ := hp
  have hinner : (∫ W, fubiniIntegrand r W p ∂(reducedLaw r τ))
      = (p.1 * p.2) ^ (-(1/2) : ℝ) *
          ∫ W, (∑ i, (W i).ofLp 0 * (W i).ofLp 1) *
            Real.exp (-(p.1 * ∑ i, ((W i).ofLp 0) ^ 2 + p.2 * ∑ i, ((W i).ofLp 1) ^ 2))
            ∂(reducedLaw r τ) := by
    rw [← MeasureTheory.integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun W => ?_)
    simp only [fubiniIntegrand, inner_colFun, norm_sq_colFun]
    ring
  rw [hinner, integral_reducedLaw_row (a := p.1) (b := p.2) hp1 hp2 hτ]

end Grothendieck

/-
Target B: the two-dimensional substitution `Grothendieck.reducedExpectation_eq_sq_subst`.

Route: no integrability whatsoever.  Everything is done at the level of `ℝ≥0∞`-valued
(Lebesgue) integrals, where Tonelli needs no hypotheses beyond measurability, and the
one-dimensional change of variables `MeasureTheory.lintegral_image_eq_lintegral_abs_deriv_mul`
has no integrability hypothesis either.  The final passage back to Bochner integrals uses
`MeasureTheory.integral_eq_lintegral_of_nonneg_ae`, which is valid *without* integrability
(both sides are then `0`), together with the unconditional `ENNReal.toReal_mul`.
-/

open MeasureTheory
open scoped BigOperators Real Topology ENNReal

namespace Grothendieck

theorem measurable_rpow_const_real (y : ℝ) : Measurable fun x : ℝ => x ^ y := by
  refine measurable_of_measurable_on_compl_singleton 0 ?_
  exact Continuous.measurable (continuousOn_iff_continuous_domRestrict.1 (fun x hx =>
    (Real.continuousAt_rpow_const x y (Or.inl hx)).continuousWithinAt))

attribute [fun_prop] measurable_rpow_const_real

/-- `(√(2s))⁻¹ ds = du` under `s = u²/2`, in the form that a factor `c` is carried along.
No measurability or integrability hypothesis on `F`. -/
theorem lintegral_const_sqrt_inv_mul_eq (c : ℝ≥0∞) (F : ℝ → ℝ≥0∞) :
    ∫⁻ t in Set.Ioi (0:ℝ), c * (ENNReal.ofReal ((Real.sqrt (2 * t))⁻¹) * F t)
      = ∫⁻ u in Set.Ioi (0:ℝ), c * F (u ^ 2 / 2) := by
  have himg : (fun u : ℝ => u ^ 2 / 2) '' Set.Ioi (0:ℝ) = Set.Ioi (0:ℝ) := by
    ext s
    constructor
    · rintro ⟨u, hu, rfl⟩
      have hu0 : (0:ℝ) < u := hu
      show (0:ℝ) < u ^ 2 / 2
      positivity
    · intro hs
      have hs0 : (0:ℝ) < s := hs
      refine ⟨Real.sqrt (2 * s), ?_, ?_⟩
      · show (0:ℝ) < Real.sqrt (2 * s)
        positivity
      · show Real.sqrt (2 * s) ^ 2 / 2 = s
        rw [Real.sq_sqrt (by positivity)]
        ring
  have hinj : Set.InjOn (fun u : ℝ => u ^ 2 / 2) (Set.Ioi (0:ℝ)) := by
    intro a ha b hb hab
    have ha0 : (0:ℝ) < a := ha
    have hb0 : (0:ℝ) < b := hb
    simp only at hab
    have : a ^ 2 = b ^ 2 := by linarith
    nlinarith [ha0, hb0, this]
  conv_lhs => rw [← himg]
  rw [MeasureTheory.lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Ioi
    (f := fun u : ℝ => u ^ 2 / 2) (f' := fun u : ℝ => u)
    (fun u _ => ?_) hinj]
  swap
  · have hd : HasDerivAt (fun u : ℝ => u ^ 2 / 2) u u := by
      have h := (hasDerivAt_pow 2 u).div_const 2
      refine HasDerivAt.congr_deriv h ?_
      ring
    exact hd.hasDerivWithinAt
  refine lintegral_congr_ae ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  have hu0 : (0:ℝ) < u := hu
  have habs : |u| = u := abs_of_pos hu0
  have hsq : Real.sqrt (2 * (u ^ 2 / 2)) = u := by
    rw [show 2 * (u ^ 2 / 2) = u ^ 2 by ring, Real.sqrt_sq hu0.le]
  have hone : ENNReal.ofReal u * ENNReal.ofReal u⁻¹ = 1 := by
    rw [← ENNReal.ofReal_mul (le_of_lt hu0), mul_inv_cancel₀ hu0.ne', ENNReal.ofReal_one]
  simp only [habs, hsq]
  rw [show ENNReal.ofReal u * (c * (ENNReal.ofReal u⁻¹ * F (u ^ 2 / 2)))
      = c * ((ENNReal.ofReal u * ENNReal.ofReal u⁻¹) * F (u ^ 2 / 2)) by ring, hone, one_mul]

/-- `(√(2s))⁻¹ ds = du` under `s = u²/2`, as an identity of Lebesgue integrals of
`ℝ≥0∞`-valued functions (no measurability or integrability hypothesis). -/
theorem lintegral_sqrt_inv_mul_eq (F : ℝ → ℝ≥0∞) :
    ∫⁻ t in Set.Ioi (0:ℝ), ENNReal.ofReal ((Real.sqrt (2 * t))⁻¹) * F t
      = ∫⁻ u in Set.Ioi (0:ℝ), F (u ^ 2 / 2) := by
  simpa using lintegral_const_sqrt_inv_mul_eq 1 F

/-- The substitution `s = u²/2`, `t = v²/2` for a general kernel `κ`, with
`κ' u v = κ (u²/2) (v²/2)`.  The weight `(s t)^{-1/2} ds dt` becomes `2 du dv`. -/
theorem lintegral_kernel_subst_general (κ κ' : ℝ → ℝ → ℝ) (c : ℝ)
    (hκpos : ∀ s t : ℝ, 0 < s → 0 < t → 0 < κ s t)
    (hsub : ∀ u v : ℝ, κ' u v = κ (u ^ 2 / 2) (v ^ 2 / 2))
    (hκm : ∀ s : ℝ, Measurable fun t : ℝ => ENNReal.ofReal ((κ s t) ^ (-c : ℝ)))
    (hF : Measurable fun p : ℝ × ℝ =>
      ENNReal.ofReal ((p.1 * p.2) ^ (-(1/2) : ℝ) * (κ p.1 p.2) ^ (-c : ℝ)))
    (hG : Measurable fun p : ℝ × ℝ => ENNReal.ofReal ((κ' p.1 p.2) ^ (-c : ℝ))) :
    ∫⁻ p, ENNReal.ofReal ((p.1 * p.2) ^ (-(1/2) : ℝ) * (κ p.1 p.2) ^ (-c : ℝ)) ∂planeMeasure
      = 2 * ∫⁻ p, ENNReal.ofReal ((κ' p.1 p.2) ^ (-c : ℝ)) ∂planeMeasure := by
  have hst : ∀ s t : ℝ, 0 < s → 0 < t →
      (s * t) ^ (-(1/2) : ℝ) = 2 * (Real.sqrt (2 * s))⁻¹ * (Real.sqrt (2 * t))⁻¹ := by
    intro s t hs ht
    have h4 : (4:ℝ) ^ (-(1/2) : ℝ) = 1/2 := by
      have h4' : Real.sqrt (4:ℝ) = 2 := by
        rw [show (4:ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
      rw [Real.rpow_neg (by norm_num : (0:ℝ) ≤ 4), ← Real.sqrt_eq_rpow, h4']
      norm_num
    have h1 : (Real.sqrt (2 * s))⁻¹ = (2 * s) ^ (-(1/2) : ℝ) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_neg (by positivity : (0:ℝ) ≤ 2 * s)]
    have h2 : (Real.sqrt (2 * t))⁻¹ = (2 * t) ^ (-(1/2) : ℝ) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_neg (by positivity : (0:ℝ) ≤ 2 * t)]
    rw [h1, h2, mul_assoc, ← Real.mul_rpow (by positivity : (0:ℝ) ≤ 2 * s)
      (by positivity : (0:ℝ) ≤ 2 * t)]
    rw [show (2:ℝ) * s * (2 * t) = 4 * (s * t) by ring]
    rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 4) (by positivity : (0:ℝ) ≤ s * t), h4]
    ring
  -- the pointwise identity `(s t)^{-1/2} κ^{-c} = 2 (√(2s))⁻¹ (√(2t))⁻¹ κ^{-c}`
  have hpt : ∀ s t : ℝ, 0 < s → 0 < t →
      ENNReal.ofReal ((s * t) ^ (-(1/2) : ℝ) * (κ s t) ^ (-c : ℝ))
        = 2 * (ENNReal.ofReal ((Real.sqrt (2 * s))⁻¹) *
            (ENNReal.ofReal ((Real.sqrt (2 * t))⁻¹) * ENNReal.ofReal ((κ s t) ^ (-c : ℝ)))) := by
    intro s t hs0 ht0
    have ha : (0:ℝ) ≤ (Real.sqrt (2 * s))⁻¹ := by positivity
    have hb : (0:ℝ) ≤ (Real.sqrt (2 * t))⁻¹ := by positivity
    have hk : (0:ℝ) ≤ (κ s t) ^ (-c : ℝ) :=
      (Real.rpow_pos_of_pos (hκpos s t hs0 ht0) _).le
    rw [hst s t hs0 ht0]
    conv_rhs => rw [show (2:ℝ≥0∞) = ENNReal.ofReal 2 from (ENNReal.ofReal_ofNat 2).symm]
    rw [← ENNReal.ofReal_mul hb, ← ENNReal.ofReal_mul ha,
      ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2)]
    congr 1
    ring
  -- the inner substitution, for fixed `s > 0`
  have step2 : ∀ s ∈ Set.Ioi (0:ℝ),
      ∫⁻ t in Set.Ioi (0:ℝ),
          ENNReal.ofReal ((s * t) ^ (-(1/2) : ℝ) * (κ s t) ^ (-c : ℝ))
        = (2 * ENNReal.ofReal ((Real.sqrt (2 * s))⁻¹)) *
            ∫⁻ v in Set.Ioi (0:ℝ), ENNReal.ofReal ((κ s (v ^ 2 / 2)) ^ (-c : ℝ)) := by
    intro s hs
    have hs0 : (0:ℝ) < s := hs
    have hmeas : Measurable fun t : ℝ =>
        ENNReal.ofReal ((Real.sqrt (2 * t))⁻¹) * ENNReal.ofReal ((κ s t) ^ (-c : ℝ)) := by
      have h1 : Measurable fun t : ℝ => ENNReal.ofReal ((Real.sqrt (2 * t))⁻¹) := by fun_prop
      exact h1.mul (hκm s)
    have hae : (fun t => ENNReal.ofReal ((s * t) ^ (-(1/2) : ℝ) * (κ s t) ^ (-c : ℝ)))
        =ᵐ[volume.restrict (Set.Ioi (0:ℝ))]
        (fun t => 2 * (ENNReal.ofReal ((Real.sqrt (2 * s))⁻¹) *
            (ENNReal.ofReal ((Real.sqrt (2 * t))⁻¹) *
              ENNReal.ofReal ((κ s t) ^ (-c : ℝ))))) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact hpt s t hs0 ht
    rw [lintegral_congr_ae hae]
    rw [show (fun t : ℝ => 2 * (ENNReal.ofReal ((Real.sqrt (2 * s))⁻¹) *
            (ENNReal.ofReal ((Real.sqrt (2 * t))⁻¹) *
              ENNReal.ofReal ((κ s t) ^ (-c : ℝ)))))
          = (fun t : ℝ => (2 * ENNReal.ofReal ((Real.sqrt (2 * s))⁻¹)) *
            (ENNReal.ofReal ((Real.sqrt (2 * t))⁻¹) *
              ENNReal.ofReal ((κ s t) ^ (-c : ℝ)))) from by
      funext t; ring]
    rw [lintegral_const_mul _ hmeas]
    rw [lintegral_sqrt_inv_mul_eq (fun t => ENNReal.ofReal ((κ s t) ^ (-c : ℝ)))]
  -- the outer substitution
  have step3 : ∫⁻ s in Set.Ioi (0:ℝ), ∫⁻ t in Set.Ioi (0:ℝ),
        ENNReal.ofReal ((s * t) ^ (-(1/2) : ℝ) * (κ s t) ^ (-c : ℝ))
      = ∫⁻ u in Set.Ioi (0:ℝ), 2 * ∫⁻ v in Set.Ioi (0:ℝ),
          ENNReal.ofReal ((κ (u ^ 2 / 2) (v ^ 2 / 2)) ^ (-c : ℝ)) := by
    have hae : (fun s => ∫⁻ t in Set.Ioi (0:ℝ),
          ENNReal.ofReal ((s * t) ^ (-(1/2) : ℝ) * (κ s t) ^ (-c : ℝ)))
        =ᵐ[volume.restrict (Set.Ioi (0:ℝ))]
        (fun s => (2 * ENNReal.ofReal ((Real.sqrt (2 * s))⁻¹)) *
            ∫⁻ v in Set.Ioi (0:ℝ), ENNReal.ofReal ((κ s (v ^ 2 / 2)) ^ (-c : ℝ))) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
      exact step2 s hs
    rw [lintegral_congr_ae hae]
    rw [show (fun s : ℝ => (2 * ENNReal.ofReal ((Real.sqrt (2 * s))⁻¹)) *
            ∫⁻ v in Set.Ioi (0:ℝ), ENNReal.ofReal ((κ s (v ^ 2 / 2)) ^ (-c : ℝ)))
          = (fun s : ℝ => 2 * (ENNReal.ofReal ((Real.sqrt (2 * s))⁻¹) *
            ∫⁻ v in Set.Ioi (0:ℝ), ENNReal.ofReal ((κ s (v ^ 2 / 2)) ^ (-c : ℝ)))) from by
      funext s; ring]
    rw [lintegral_const_sqrt_inv_mul_eq 2
      (fun s => ∫⁻ v in Set.Ioi (0:ℝ), ENNReal.ofReal ((κ s (v ^ 2 / 2)) ^ (-c : ℝ)))]
  -- Tonelli again, and the constant `2`
  have step4 : (∫⁻ u in Set.Ioi (0:ℝ), 2 * ∫⁻ v in Set.Ioi (0:ℝ),
          ENNReal.ofReal ((κ (u ^ 2 / 2) (v ^ 2 / 2)) ^ (-c : ℝ)))
      = 2 * ∫⁻ p, ENNReal.ofReal ((κ' p.1 p.2) ^ (-c : ℝ)) ∂
          ((volume.restrict (Set.Ioi (0:ℝ))).prod (volume.restrict (Set.Ioi (0:ℝ)))) := by
    have hf : Measurable fun p : ℝ × ℝ =>
        ENNReal.ofReal ((κ (p.1 ^ 2 / 2) (p.2 ^ 2 / 2)) ^ (-c : ℝ)) := by
      have h := hG
      simpa only [hsub] using h
    have hGm : Measurable fun u : ℝ =>
        ∫⁻ v in Set.Ioi (0:ℝ), ENNReal.ofReal ((κ (u ^ 2 / 2) (v ^ 2 / 2)) ^ (-c : ℝ)) :=
      hf.lintegral_prod_right'
    rw [lintegral_const_mul 2 hGm]
    congr 1
    have hTon := MeasureTheory.lintegral_prod (μ := volume.restrict (Set.Ioi (0:ℝ)))
      (ν := volume.restrict (Set.Ioi (0:ℝ)))
      (fun p : ℝ × ℝ => ENNReal.ofReal ((κ (p.1 ^ 2 / 2) (p.2 ^ 2 / 2)) ^ (-c : ℝ)))
      hf.aemeasurable
    rw [← hTon]
    exact lintegral_congr fun p => by rw [hsub]
  have step1 := MeasureTheory.lintegral_prod (μ := volume.restrict (Set.Ioi (0:ℝ)))
    (ν := volume.restrict (Set.Ioi (0:ℝ)))
    (fun p : ℝ × ℝ => ENNReal.ofReal ((p.1 * p.2) ^ (-(1/2) : ℝ) * (κ p.1 p.2) ^ (-c : ℝ)))
    hF.aemeasurable
  unfold planeMeasure
  rw [step1, step3, step4]

/-- The two-dimensional substitution for the concrete Laplace kernel of Lemma 2.1. -/
theorem lintegral_kernel_eq (r : ℕ) {τ : ℝ} (hτ : τ ^ 2 < 1) :
    ∫⁻ p, ENNReal.ofReal ((p.1 * p.2) ^ (-(1/2) : ℝ) *
        ((1 + 2 * p.1) * (1 + 2 * p.2) - 4 * τ ^ 2 * p.1 * p.2) ^
          (-(((r : ℝ) + 2) / 2) : ℝ)) ∂planeMeasure
      = 2 * ∫⁻ p, ENNReal.ofReal
          (((1 + p.1 ^ 2) * (1 + p.2 ^ 2) - τ ^ 2 * p.1 ^ 2 * p.2 ^ 2) ^
            (-(((r : ℝ) + 2) / 2) : ℝ)) ∂planeMeasure := by
  refine lintegral_kernel_subst_general
    (fun s t => (1 + 2 * s) * (1 + 2 * t) - 4 * τ ^ 2 * s * t)
    (fun u v => (1 + u ^ 2) * (1 + v ^ 2) - τ ^ 2 * u ^ 2 * v ^ 2)
    (((r : ℝ) + 2) / 2) ?_ ?_ ?_ ?_ ?_
  · intro s t hs ht
    have h1 : (0:ℝ) < s * t := mul_pos hs ht
    have h2 : (0:ℝ) < 1 - τ ^ 2 := by linarith
    have h3 : (0:ℝ) < s * t * (1 - τ ^ 2) := mul_pos h1 h2
    nlinarith [h3, hs, ht]
  · intro u v
    ring
  · intro s
    fun_prop
  · fun_prop
  · fun_prop

/-- The positivity of the kernel `(1+2s)(1+2t) - 4τ²st` on the positive quadrant. -/
theorem kernel_pos {τ : ℝ} (hτ : τ ^ 2 < 1) {s t : ℝ} (hs : 0 < s) (ht : 0 < t) :
    0 < (1 + 2 * s) * (1 + 2 * t) - 4 * τ ^ 2 * s * t := by
  have h1 : (0:ℝ) < s * t := mul_pos hs ht
  have h2 : (0:ℝ) < 1 - τ ^ 2 := by linarith
  have h3 : (0:ℝ) < s * t * (1 - τ ^ 2) := mul_pos h1 h2
  nlinarith [h3, hs, ht]

/-- The base of the substituted kernel is nonnegative everywhere. -/
theorem sq_kernel_nonneg {τ : ℝ} (hτ : τ ^ 2 < 1) (u v : ℝ) :
    0 ≤ (1 + u ^ 2) * (1 + v ^ 2) - τ ^ 2 * u ^ 2 * v ^ 2 := by
  have h2 : (0:ℝ) ≤ 1 - τ ^ 2 := by linarith
  nlinarith [sq_nonneg u, sq_nonneg v, mul_nonneg (sq_nonneg u) (sq_nonneg v),
    mul_nonneg (mul_nonneg (sq_nonneg u) (sq_nonneg v)) h2]

/-- The real identity behind the substitution: no integrability is needed at any point. -/
theorem integral_kernel_eq (r : ℕ) {τ : ℝ} (hτ : τ ^ 2 < 1) :
    (∫ p, (p.1 * p.2) ^ (-(1/2) : ℝ) *
        ((1 + 2 * p.1) * (1 + 2 * p.2) - 4 * τ ^ 2 * p.1 * p.2) ^
          (-(((r : ℝ) + 2) / 2) : ℝ) ∂planeMeasure)
      = 2 * ∫ p, (((1 + p.1 ^ 2) * (1 + p.2 ^ 2) - τ ^ 2 * p.1 ^ 2 * p.2 ^ 2) ^
            (-(((r : ℝ) + 2) / 2) : ℝ)) ∂planeMeasure := by
  have hg_nn : 0 ≤ᵐ[planeMeasure] (fun p : ℝ × ℝ => (p.1 * p.2) ^ (-(1/2) : ℝ) *
      ((1 + 2 * p.1) * (1 + 2 * p.2) - 4 * τ ^ 2 * p.1 * p.2) ^
        (-(((r : ℝ) + 2) / 2) : ℝ)) := by
    filter_upwards [ae_pos_planeMeasure] with p hp
    obtain ⟨hp1, hp2⟩ := hp
    exact mul_nonneg (Real.rpow_nonneg (le_of_lt (mul_pos hp1 hp2)) _)
      (le_of_lt (Real.rpow_pos_of_pos (kernel_pos hτ hp1 hp2) _))
  have hH_nn : 0 ≤ᵐ[planeMeasure] (fun p : ℝ × ℝ =>
      ((1 + p.1 ^ 2) * (1 + p.2 ^ 2) - τ ^ 2 * p.1 ^ 2 * p.2 ^ 2) ^
        (-(((r : ℝ) + 2) / 2) : ℝ)) := by
    filter_upwards with p
    exact Real.rpow_nonneg (sq_kernel_nonneg hτ p.1 p.2) _
  have hg_meas : AEStronglyMeasurable (fun p : ℝ × ℝ => (p.1 * p.2) ^ (-(1/2) : ℝ) *
      ((1 + 2 * p.1) * (1 + 2 * p.2) - 4 * τ ^ 2 * p.1 * p.2) ^
        (-(((r : ℝ) + 2) / 2) : ℝ)) planeMeasure := by
    have h : Measurable fun p : ℝ × ℝ => (p.1 * p.2) ^ (-(1/2) : ℝ) *
        ((1 + 2 * p.1) * (1 + 2 * p.2) - 4 * τ ^ 2 * p.1 * p.2) ^
          (-(((r : ℝ) + 2) / 2) : ℝ) := by fun_prop
    exact h.aestronglyMeasurable
  have hH_meas : AEStronglyMeasurable (fun p : ℝ × ℝ =>
      ((1 + p.1 ^ 2) * (1 + p.2 ^ 2) - τ ^ 2 * p.1 ^ 2 * p.2 ^ 2) ^
        (-(((r : ℝ) + 2) / 2) : ℝ)) planeMeasure := by
    have h : Measurable fun p : ℝ × ℝ =>
        ((1 + p.1 ^ 2) * (1 + p.2 ^ 2) - τ ^ 2 * p.1 ^ 2 * p.2 ^ 2) ^
          (-(((r : ℝ) + 2) / 2) : ℝ) := by fun_prop
    exact h.aestronglyMeasurable
  rw [integral_eq_lintegral_of_nonneg_ae hg_nn hg_meas,
    integral_eq_lintegral_of_nonneg_ae hH_nn hH_meas, lintegral_kernel_eq r hτ,
    ENNReal.toReal_mul]
  norm_num

/-- **Step 4b: the substitutions `s = p²/2`, `t = q²/2`.** -/
theorem reducedExpectation_eq_sq_subst (r : ℕ) (hr : 2 ≤ r) {τ : ℝ} (hτ : τ ^ 2 < 1) :
    (∫ W, reducedIntegrand r W ∂(reducedLaw r τ))
      = 2 * (r : ℝ) * τ * Real.pi⁻¹ * ∫ p,
          (((1 + p.1 ^ 2) * (1 + p.2 ^ 2) - τ ^ 2 * p.1 ^ 2 * p.2 ^ 2) ^
            (-(((r : ℝ) + 2) / 2) : ℝ)) ∂planeMeasure := by
  rw [reducedExpectation_eq_kernel_proof r hr hτ]
  have hA : (∫ p, (p.1 * p.2) ^ (-(1/2) : ℝ) *
        ((r : ℝ) * τ * ((1 + 2 * p.1) * (1 + 2 * p.2) - 4 * τ ^ 2 * p.1 * p.2) ^
          (-(((r : ℝ) + 2) / 2) : ℝ)) ∂planeMeasure)
      = ((r : ℝ) * τ) * ∫ p, (p.1 * p.2) ^ (-(1/2) : ℝ) *
        ((1 + 2 * p.1) * (1 + 2 * p.2) - 4 * τ ^ 2 * p.1 * p.2) ^
          (-(((r : ℝ) + 2) / 2) : ℝ) ∂planeMeasure := by
    rw [← MeasureTheory.integral_const_mul]
    exact integral_congr_ae (Filter.Eventually.of_forall fun p => by ring)
  rw [hA, integral_kernel_eq r hτ]
  ring

end Grothendieck

/-! ### inlined: chain/FinalAssembly.lean -/
open MeasureTheory
open scoped BigOperators Real Topology ENNReal

namespace Grothendieck

/-- **The substituted-kernel integral, iterated and evaluated.** -/
theorem kernel_integral_eval (r : ℕ) (hr : 2 ≤ r) {τ : ℝ} (hτ : τ ^ 2 < 1) :
    (∫ p : ℝ × ℝ, ((1 + p.1 ^ 2) * (1 + p.2 ^ 2) - τ ^ 2 * p.1 ^ 2 * p.2 ^ 2) ^
        (-(((r : ℝ) + 2) / 2) : ℝ) ∂planeMeasure)
      = (1 / 2 * Real.Gamma (1 / 2) * Real.Gamma (((r : ℝ) + 2) / 2 - 1 / 2) /
            Real.Gamma (((r : ℝ) + 2) / 2)) *
          (1 / 2 * ∫ x in Set.Ioo (0:ℝ) 1,
            x ^ (-(1 / 2) : ℝ) * (1 - x) ^ ((((r : ℝ) + 2) / 2) - 3 / 2) *
              (1 - τ ^ 2 * x) ^ (-(1 / 2) : ℝ)) := by
  have hM : (1/2 : ℝ) < ((r : ℝ) + 2) / 2 := by
    have : (2:ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
    linarith
  -- iterate the plane integral
  have hiter : (∫ p : ℝ × ℝ, ((1 + p.1 ^ 2) * (1 + p.2 ^ 2) - τ ^ 2 * p.1 ^ 2 * p.2 ^ 2) ^
        (-(((r : ℝ) + 2) / 2) : ℝ) ∂planeMeasure)
      = ∫ u in Set.Ioi (0:ℝ), ∫ v in Set.Ioi (0:ℝ),
          ((1 + u ^ 2) * (1 + v ^ 2) - τ ^ 2 * u ^ 2 * v ^ 2) ^ (-(((r : ℝ) + 2) / 2) : ℝ) := by
    unfold planeMeasure
    rw [integral_prod _ (integrable_kernel_subst r hr hτ)]
  rw [hiter]
  -- evaluate the inner integral
  have hinner : ∀ u : ℝ, (∫ v in Set.Ioi (0:ℝ),
        ((1 + u ^ 2) * (1 + v ^ 2) - τ ^ 2 * u ^ 2 * v ^ 2) ^ (-(((r : ℝ) + 2) / 2) : ℝ))
      = (1 + u ^ 2) ^ (1 / 2 - ((r : ℝ) + 2) / 2) *
          (1 + (1 - τ ^ 2) * u ^ 2) ^ (-(1 / 2) : ℝ) *
          (1 / 2 * Real.Gamma (1 / 2) * Real.Gamma (((r : ℝ) + 2) / 2 - 1 / 2) /
            Real.Gamma (((r : ℝ) + 2) / 2)) := fun u => integral_kernel_inner r hr hτ u
  simp only [hinner]
  -- pull the constant out of the outer integral, then apply the `q² = x/(1-x)` substitution
  have hτ1 : |τ| < 1 := by
    rw [abs_lt]
    constructor <;> nlinarith [hτ]
  have hstep : (∫ u in Set.Ioi (0:ℝ),
        (1 + u ^ 2) ^ (1 / 2 - ((r : ℝ) + 2) / 2) *
          (1 + (1 - τ ^ 2) * u ^ 2) ^ (-(1 / 2) : ℝ) *
          (1 / 2 * Real.Gamma (1 / 2) * Real.Gamma (((r : ℝ) + 2) / 2 - 1 / 2) /
            Real.Gamma (((r : ℝ) + 2) / 2)))
      = (1 / 2 * Real.Gamma (1 / 2) * Real.Gamma (((r : ℝ) + 2) / 2 - 1 / 2) /
            Real.Gamma (((r : ℝ) + 2) / 2)) *
        ∫ u in Set.Ioi (0:ℝ),
          (1 + u ^ 2) ^ (1 / 2 - ((r : ℝ) + 2) / 2) * (1 + (1 - τ ^ 2) * u ^ 2) ^ (-(1 / 2) : ℝ) := by
    rw [← MeasureTheory.integral_const_mul]
    congr 1 with u
    ring
  rw [hstep]
  have hsq := integral_sq_subst (M := ((r : ℝ) + 2) / 2) hM hτ1
  rw [hsq]

/-- **Lemma 2.1, the canonical identity, for `r ≥ 2`.** -/
theorem reducedExpectation_eq_Er_proof (r : ℕ) (hr : 2 ≤ r) {τ : ℝ} (hτ : τ ^ 2 < 1) :
    (∫ W, reducedIntegrand r W ∂(reducedLaw r τ)) = Er r τ := by
  rw [reducedExpectation_eq_sq_subst r hr hτ, kernel_integral_eval r hr hτ]
  have hr1 : (1:ℕ) ≤ r := le_trans (by norm_num) hr
  have hτ1 : |τ| < 1 := by
    rw [abs_lt]
    constructor <;> nlinarith [hτ]
  rw [Er_eq_betaIntegral r hr1 hτ1]
  -- convert the interval integral in `Er` to the `Ioo` integral here
  have hIoo : (∫ u in (0 : ℝ)..1, u ^ (-(1/2) : ℝ) * (1 - u) ^ (((r : ℝ) - 1) / 2) *
        (1 - τ ^ 2 * u) ^ (-(1/2) : ℝ))
      = ∫ x in Set.Ioo (0:ℝ) 1, x ^ (-(1/2) : ℝ) * (1 - x) ^ (((r : ℝ) - 1) / 2) *
        (1 - τ ^ 2 * x) ^ (-(1/2) : ℝ) := by
    rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1),
      integral_Ioc_eq_integral_Ioo]
  rw [hIoo]
  -- match the exponents `(r+2)/2 - 3/2` and `(r-1)/2`
  have hexp : (((r : ℝ) + 2) / 2) - 3 / 2 = ((r : ℝ) - 1) / 2 := by ring
  rw [hexp]
  -- the constants
  have hc := constant_bookkeeping r hr1 τ
  calc 2 * (r : ℝ) * τ * Real.pi⁻¹ *
        (1 / 2 * Real.Gamma (1 / 2) * Real.Gamma (((r : ℝ) + 2) / 2 - 1 / 2) /
            Real.Gamma (((r : ℝ) + 2) / 2) *
          (1 / 2 * ∫ x in Set.Ioo (0:ℝ) 1,
            x ^ (-(1/2) : ℝ) * (1 - x) ^ (((r : ℝ) - 1) / 2) *
              (1 - τ ^ 2 * x) ^ (-(1/2) : ℝ)))
      = (2 * (r : ℝ) * τ * Real.pi⁻¹ *
          (1 / 2 * Real.Gamma (1 / 2) * Real.Gamma (((r : ℝ) + 2) / 2 - 1 / 2) /
            Real.Gamma (((r : ℝ) + 2) / 2)) * (1 / 2)) *
          ∫ x in Set.Ioo (0:ℝ) 1,
            x ^ (-(1/2) : ℝ) * (1 - x) ^ (((r : ℝ) - 1) / 2) *
              (1 - τ ^ 2 * x) ^ (-(1/2) : ℝ) := by ring
    _ = (τ * Real.Gamma (((r : ℝ) + 1) / 2) / (Real.sqrt Real.pi * Real.Gamma ((r : ℝ) / 2))) *
          ∫ x in Set.Ioo (0:ℝ) 1,
            x ^ (-(1/2) : ℝ) * (1 - x) ^ (((r : ℝ) - 1) / 2) *
              (1 - τ ^ 2 * x) ^ (-(1/2) : ℝ) := by rw [hc]
    _ = Real.Gamma (((r : ℝ) + 1) / 2) / (Real.sqrt Real.pi * Real.Gamma ((r : ℝ) / 2)) *
          (τ * ∫ x in Set.Ioo (0:ℝ) 1,
            x ^ (-(1/2) : ℝ) * (1 - x) ^ (((r : ℝ) - 1) / 2) *
              (1 - τ ^ 2 * x) ^ (-(1/2) : ℝ)) := by ring

end Grothendieck

open MeasureTheory in
open Grothendieck in
theorem solution (r : ℕ) (hr : 2 ≤ r) {τ : ℝ} (hτ : τ ^ 2 < 1) :
    (∫ W, reducedIntegrand r W ∂(reducedLaw r τ)) = Er r τ :=
  reducedExpectation_eq_Er_proof r hr hτ
