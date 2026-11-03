-- Prove2me | solution 1 for Grothendieck.ErInv_isInverse
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-02T15:09:16.525877+00:00
-- url     : https://prove2.me/submissions/2e7b4554-674d-43c5-88aa-1d9c63138152

import Mathlib
import Definitions.Def_Grothendieck_Series
import Definitions.Def_Grothendieck_Gaussian

set_option autoImplicit false

set_option maxHeartbeats 1000000

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
theorem Er_one_proof (r : ℕ) (hr : 1 ≤ r) : Er r 1 = 1 := by
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

/-! ## Part 2: monotonicity / continuity layer -/

/-! ## 0. elementary facts about `risingFact` -/

lemma risingFact_succ' (a : ℝ) (k : ℕ) :
    risingFact a (k + 1) = risingFact a k * (a + (k : ℝ)) := by
  simp [risingFact, Finset.prod_range_succ]

lemma risingFact_three_half (k : ℕ) :
    risingFact (1 / 2 + 1) k = (2 * (k : ℝ) + 1) * risingFact (1 / 2) k := by
  induction k with
  | zero => simp [risingFact]
  | succ n ih =>
      rw [risingFact_succ', ih, risingFact_succ']
      push_cast
      ring

lemma risingFact_half_pos (k : ℕ) : 0 < risingFact (1 / 2) k := by
  induction k with
  | zero => simp [risingFact]
  | succ n ih =>
      rw [risingFact_succ']
      have : (0:ℝ) < 1 / 2 + (n:ℝ) := by positivity
      positivity

/-! ## 1. The sequence `b k = (1/2)_k / k!` -/

/-- `b k = (1/2)_k / k!`. -/
def bc (k : ℕ) : ℝ := risingFact (1 / 2) k / (k.factorial : ℝ)

lemma bc_zero : bc 0 = 1 := by simp [bc, risingFact]

lemma bc_pos (k : ℕ) : 0 < bc k := by
  unfold bc
  have h1 : (0:ℝ) < risingFact (1/2) k := risingFact_half_pos k
  have h2 : (0:ℝ) < (k.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos k
  exact div_pos h1 h2

/-- the recurrence `(k+1) b_{k+1} = (k+1/2) b_k`. -/
lemma bc_succ (k : ℕ) : ((k:ℝ) + 1) * bc (k+1) = ((k:ℝ) + 1/2) * bc k := by
  unfold bc
  rw [risingFact_succ', Nat.factorial_succ]
  push_cast
  have hpos : (0:ℝ) < risingFact (1/2) k := risingFact_half_pos k
  have hk : (0:ℝ) < (k:ℝ) + 1 := by positivity
  have hk0 : ((k:ℝ) + 1) ≠ 0 := ne_of_gt hk
  have hfk : ((k.factorial : ℕ) : ℝ) ≠ 0 := by
    have : (0:ℝ) < (k.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos k
    exact ne_of_gt this
  field_simp
  ring

/-- `b k` is the product `∏_{i<k} (i+1/2)/(i+1)`, hence `≤ 1`. -/
lemma bc_succ_div (k : ℕ) : bc (k+1) = bc k * (((k:ℝ) + 1/2) / ((k:ℝ) + 1)) := by
  have h := bc_succ k
  have hk : ((k:ℝ) + 1) ≠ 0 := by positivity
  field_simp at h ⊢
  linarith

lemma bc_le_one : ∀ k : ℕ, bc k ≤ 1 := by
  intro k
  induction k with
  | zero => simp [bc_zero]
  | succ n ih =>
      rw [bc_succ_div]
      have hle : (((n:ℝ) + 1/2) / ((n:ℝ) + 1)) ≤ 1 := by
        rw [div_le_one (by positivity)]; linarith
      have hnn : 0 ≤ (((n:ℝ) + 1/2) / ((n:ℝ) + 1)) := by positivity
      nlinarith [bc_pos n]

lemma bc_nonneg (k : ℕ) : 0 ≤ bc k := le_of_lt (bc_pos k)

/-- The key bound `(2k+1) b_k²  ≤ 1` (Wallis). -/
lemma bc_sq_bound : ∀ k : ℕ, (2*(k:ℝ)+1) * (bc k)^2 ≤ 1 := by
  intro k
  induction k with
  | zero => simp [bc_zero]
  | succ n ih =>
      have hn : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
      have hkey : bc (n+1) = bc n * (((n:ℝ) + 1/2) / ((n:ℝ) + 1)) := bc_succ_div n
      have hratio : (2*(n:ℝ)+3) * ((n:ℝ) + 1/2)^2 ≤ (2*(n:ℝ)+1) * ((n:ℝ) + 1)^2 := by
        nlinarith
      have hbn : (0:ℝ) ≤ (bc n)^2 := sq_nonneg _
      have h2 : (0:ℝ) < ((n:ℝ) + 1)^2 := by positivity
      have hmul : (2*(n:ℝ)+3) * ((n:ℝ) + 1/2)^2 * (bc n)^2
          ≤ (2*(n:ℝ)+1) * (bc n)^2 * ((n:ℝ) + 1)^2 := by
        have h := mul_le_mul_of_nonneg_right hratio hbn
        calc (2*(n:ℝ)+3) * ((n:ℝ) + 1/2)^2 * (bc n)^2
            ≤ ((2*(n:ℝ)+1) * ((n:ℝ) + 1)^2) * (bc n)^2 := h
          _ = (2*(n:ℝ)+1) * (bc n)^2 * ((n:ℝ) + 1)^2 := by ring
      have hid : (2*(n:ℝ)+3) * (bc (n+1))^2 * ((n:ℝ)+1)^2
          = (2*(n:ℝ)+3) * ((n:ℝ)+1/2)^2 * (bc n)^2 := by
        rw [hkey]
        field_simp
      have hstep : (2*(n:ℝ)+3) * (bc (n+1))^2 ≤ (2*(n:ℝ)+1) * (bc n)^2 := by
        have h := hmul
        rw [← hid] at h
        exact le_of_mul_le_mul_right h h2
      have hgoal : (2*((n:ℝ)+1)+1) * bc (n+1)^2 ≤ 1 := by
        rw [show (2*((n:ℝ)+1)+1) = 2*(n:ℝ)+3 by ring]
        linarith
      push_cast
      exact hgoal

/-! ## 2. Summability of the binomial series and of its derivative -/

lemma summable_abs_pow_sub_one {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    Summable (fun n : ℕ => (n:ℝ) * r^(n-1)) := by
  have hr1' : ‖r‖ < 1 := by rwa [Real.norm_eq_abs, abs_of_pos hr0]
  have hid : (fun n : ℕ => (n:ℝ) * r^(n-1)) = fun n : ℕ => ((n:ℝ) * r^n) / r := by
    funext n
    rcases n with _ | k
    · simp
    · rw [Nat.add_sub_cancel, pow_succ]
      field_simp
  rw [hid]
  simpa using (summable_pow_mul_geometric_of_norm_lt_one 1 hr1').div_const r

lemma summable_abs_pow_sub_one' {x : ℝ} (hx : |x| < 1) :
    Summable (fun n : ℕ => (n:ℝ) * |x|^(n-1)) := by
  rcases eq_or_lt_of_le (abs_nonneg x) with h | h
  · rw [← h]
    refine summable_of_ne_finset_zero (s := ({0, 1} : Finset ℕ)) ?_
    intro n hn
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hn
    obtain ⟨h1, h0⟩ := hn
    have hne : n - 1 ≠ 0 := by omega
    rw [zero_pow hne]
    ring
  · exact summable_abs_pow_sub_one h hx

lemma summable_bc_mul_pow {x : ℝ} (hx : |x| < 1) : Summable (fun k : ℕ => bc k * x^k) := by
  have hg : Summable (fun k : ℕ => ‖x‖^k) :=
    summable_geometric_of_norm_lt_one (by simpa only [Real.norm_eq_abs, abs_abs] using hx)
  refine Summable.of_norm_bounded hg (fun k => ?_)
  rw [norm_mul, norm_pow, Real.norm_eq_abs, abs_of_pos (bc_pos k)]
  have h1 : bc k ≤ 1 := bc_le_one k
  have h0 : (0:ℝ) ≤ ‖x‖^k := by positivity
  nlinarith

lemma summable_bc_mul_pow_shift {x : ℝ} (hx : |x| < 1) :
    Summable (fun n : ℕ => (n:ℝ) * bc n * x^(n-1)) := by
  refine Summable.of_norm_bounded (summable_abs_pow_sub_one' hx) (fun n => ?_)
  have hstep : ‖(n:ℝ) * bc n * x^(n-1)‖ = (n:ℝ) * bc n * |x|^(n-1) := by
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_pow, abs_of_pos (bc_pos n),
        abs_of_nonneg (Nat.cast_nonneg n)]
  rw [hstep]
  have h1 : bc n ≤ 1 := bc_le_one n
  have hy : (0:ℝ) ≤ |x|^(n-1) := by positivity
  have hn : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
  have h2 : (n:ℝ) * bc n * |x|^(n-1) ≤ (n:ℝ) * 1 * |x|^(n-1) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 hn) hy
  linarith

/-! ## 3. The binomial series `B(x) = ∑ b_k x^k = (1-x)^{-1/2}` -/

/-- the binomial series. -/
def Bfun (x : ℝ) : ℝ := ∑' k : ℕ, bc k * x^k

/-- its formal derivative. -/
def Afun (x : ℝ) : ℝ := ∑' k : ℕ, ((k:ℝ)+1) * bc (k+1) * x^k

lemma Bfun_zero : Bfun 0 = 1 := by
  rw [Bfun, tsum_eq_single 0]
  · simp [bc_zero]
  · intro b hb
    simp [hb]

lemma summable_Afun {x : ℝ} (hx : |x| < 1) :
    Summable (fun k : ℕ => ((k:ℝ)+1) * bc (k+1) * x^k) := by
  have hs : Summable (fun n : ℕ => (n:ℝ) * bc n * x^(n-1)) := summable_bc_mul_pow_shift hx
  have hshift := (summable_nat_add_iff (f := fun n : ℕ => (n:ℝ) * bc n * x^(n-1)) 1).mpr hs
  simpa only [Nat.cast_add, Nat.cast_one, Nat.add_sub_cancel] using hshift

lemma tsum_deriv_shift {x : ℝ} (hx : |x| < 1) :
    (∑' n : ℕ, (n:ℝ) * bc n * x^(n-1)) = Afun x := by
  have hs := summable_bc_mul_pow_shift hx
  have h := Summable.tsum_eq_zero_add hs
  simp only [Nat.cast_zero, zero_mul, Nat.zero_sub, pow_zero, mul_one, zero_add,
    Nat.cast_add, Nat.cast_one, Nat.add_sub_cancel] at h
  rw [Afun, ← h]

/-- the derivative of the binomial series. -/
lemma hasDerivAt_Bfun {x : ℝ} (hx : |x| < 1) : HasDerivAt Bfun (Afun x) x := by
  obtain ⟨r, hrx, hr1⟩ : ∃ r : ℝ, |x| < r ∧ r < 1 := ⟨(|x| + 1)/2, by linarith, by linarith⟩
  have hr0 : 0 < r := lt_of_le_of_lt (abs_nonneg x) hrx
  have hmem : x ∈ Set.Ioo (-r) r := by
    rw [Set.mem_Ioo]
    exact ⟨by linarith [neg_abs_le x], by linarith [le_abs_self x]⟩
  have hu : Summable (fun n : ℕ => (n:ℝ) * r^(n-1)) := summable_abs_pow_sub_one hr0 hr1
  have hderiv : ∀ (n : ℕ) (y : ℝ), y ∈ Set.Ioo (-r) r →
      HasDerivAt (fun y : ℝ => bc n * y^n) ((n:ℝ) * bc n * y^(n-1)) y := by
    intro n y _
    have h1 : HasDerivAt (fun y : ℝ => y^n) ((n:ℝ) * y^(n-1)) y := hasDerivAt_pow n y
    have h2 := h1.const_mul (bc n)
    have he : bc n * ((n:ℝ) * y^(n-1)) = (n:ℝ) * bc n * y^(n-1) := by ring
    rw [he] at h2
    exact h2
  have hbound : ∀ (n : ℕ) (y : ℝ), y ∈ Set.Ioo (-r) r →
      ‖(n:ℝ) * bc n * y^(n-1)‖ ≤ (n:ℝ) * r^(n-1) := by
    intro n y hy
    have hy' : |y| ≤ r := by
      rw [abs_le]; exact ⟨le_of_lt hy.1, le_of_lt hy.2⟩
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · subst h0
      simp
    · have hstep : ‖(n:ℝ) * bc n * y^(n-1)‖ = (n:ℝ) * bc n * |y|^(n-1) := by
        rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_pow, abs_of_pos (bc_pos n),
          abs_of_nonneg (Nat.cast_nonneg n)]
      rw [hstep]
      have hpow : |y|^(n-1) ≤ r^(n-1) := pow_le_pow_left₀ (abs_nonneg y) hy' _
      have h1 : bc n ≤ 1 := bc_le_one n
      have hn : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
      have h3 : (0:ℝ) ≤ |y|^(n-1) := by positivity
      have hb1 : (n:ℝ) * bc n * |y|^(n-1) ≤ (n:ℝ) * 1 * |y|^(n-1) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 hn) h3
      have hb2 : (n:ℝ) * 1 * |y|^(n-1) ≤ (n:ℝ) * 1 * r^(n-1) :=
        mul_le_mul_of_nonneg_left hpow (by positivity : (0:ℝ) ≤ (n:ℝ) * 1)
      calc (n:ℝ) * bc n * |y|^(n-1) ≤ (n:ℝ) * 1 * |y|^(n-1) := hb1
        _ ≤ (n:ℝ) * 1 * r^(n-1) := hb2
        _ = (n:ℝ) * r^(n-1) := by ring
  have hpt : (0:ℝ) ∈ Set.Ioo (-r) r := ⟨by linarith, by linarith⟩
  have hsum0 : Summable (fun n : ℕ => bc n * (0:ℝ)^n) := by
    refine summable_of_ne_finset_zero (s := ({0} : Finset ℕ)) ?_
    intro n hn
    have hn0 : n ≠ 0 := by simpa using hn
    simp [hn0]
  have hmain := hasDerivAt_tsum_of_isPreconnected (𝕜 := ℝ) (F := ℝ) (y₀ := (0:ℝ))
    (u := fun n : ℕ => (n:ℝ) * r^(n-1))
    (g := fun (n:ℕ) (y:ℝ) => bc n * y^n)
    (g' := fun (n:ℕ) (y:ℝ) => (n:ℝ) * bc n * y^(n-1))
    (t := Set.Ioo (-r) r) hu isOpen_Ioo isPreconnected_Ioo hderiv hbound hpt hsum0 hmem
  rw [← tsum_deriv_shift hx]
  exact hmain

lemma bc_recur (k : ℕ) : ((k:ℝ)+1) * bc (k+1) - (k:ℝ) * bc k = (1/2) * bc k := by
  have h := bc_succ k
  linarith

lemma summable_k_bc_pow {x : ℝ} (hx : |x| < 1) :
    Summable (fun k : ℕ => (k:ℝ) * bc k * x^k) := by
  have hg : Summable (fun k : ℕ => (k:ℝ) * |x|^k) := by
    have h := summable_pow_mul_geometric_of_norm_lt_one 1
      (r := |x|) (by simpa only [Real.norm_eq_abs, abs_abs] using hx)
    simpa using h
  refine Summable.of_norm_bounded hg (fun n => ?_)
  have hstep : ‖(n:ℝ) * bc n * x^n‖ = (n:ℝ) * bc n * |x|^n := by
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_pow, abs_of_pos (bc_pos n),
      abs_of_nonneg (Nat.cast_nonneg n)]
  rw [hstep]
  have h1 : bc n ≤ 1 := bc_le_one n
  have hn : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
  have h3 : (0:ℝ) ≤ |x|^n := by positivity
  have hb1 : (n:ℝ) * bc n * |x|^n ≤ (n:ℝ) * 1 * |x|^n :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 hn) h3
  calc (n:ℝ) * bc n * |x|^n ≤ (n:ℝ) * 1 * |x|^n := hb1
    _ = (n:ℝ) * |x|^n := by ring

/-- the ODE satisfied by the binomial series: `(1-x) B'(x) = B(x)/2`. -/
lemma Bfun_ode {x : ℝ} (hx : |x| < 1) : (1 - x) * Afun x = (1/2) * Bfun x := by
  have hA : Summable (fun k : ℕ => ((k:ℝ)+1) * bc (k+1) * x^k) := summable_Afun hx
  have hB : Summable (fun k : ℕ => bc k * x^k) := summable_bc_mul_pow hx
  have hk : Summable (fun k : ℕ => (k:ℝ) * bc k * x^k) := summable_k_bc_pow hx
  have hxA : x * Afun x = ∑' k : ℕ, ((k:ℝ)+1) * bc (k+1) * x^(k+1) := by
    rw [Afun, ← Summable.tsum_mul_left x hA]
    exact tsum_congr (fun k => by ring)
  have hshift : (∑' k : ℕ, ((k:ℝ)+1) * bc (k+1) * x^(k+1))
      = ∑' k : ℕ, (k:ℝ) * bc k * x^k := by
    have h := Summable.tsum_eq_zero_add hk
    simp only [Nat.cast_zero, zero_mul, zero_add] at h
    refine Eq.trans ?_ h.symm
    refine tsum_congr (fun k => ?_)
    push_cast
    ring
  have hsub : Afun x - x * Afun x
      = ∑' k : ℕ, (((k:ℝ)+1) * bc (k+1) - (k:ℝ) * bc k) * x^k := by
    rw [hxA, Afun, hshift, ← Summable.tsum_sub hA hk]
    exact tsum_congr (fun k => by ring)
  have hhalf : (∑' k : ℕ, (((k:ℝ)+1) * bc (k+1) - (k:ℝ) * bc k) * x^k)
      = (1/2) * Bfun x := by
    rw [Bfun, ← Summable.tsum_mul_left (1/2) hB]
    exact tsum_congr (fun k => by rw [bc_recur k]; ring)
  rw [← hhalf, ← hsub]
  ring

/-- `Q(x) = (1-x)^{-1/2}`. -/
def Qfun (x : ℝ) : ℝ := (1 - x) ^ (-(1/2) : ℝ)

lemma hasDerivAt_Qfun {x : ℝ} (hx : x < 1) :
    HasDerivAt Qfun ((1/2) * (1-x)^(-(3/2) : ℝ)) x := by
  have hf : HasDerivAt (fun y : ℝ => 1 - y) (-1) x := by
    simpa using (hasDerivAt_id x).const_sub (1:ℝ)
  have hg : HasDerivAt (fun _ : ℝ => (-(1/2) : ℝ)) 0 x := hasDerivAt_const x _
  have hpos : (0:ℝ) < 1 - x := by linarith
  have h := hf.rpow hg hpos
  have hsimp : (-1 : ℝ) * (-(1/2)) * (1-x)^((-(1/2) : ℝ) - 1) + 0 * (1-x)^(-(1/2):ℝ) * Real.log (1-x)
      = (1/2) * (1-x)^(-(3/2) : ℝ) := by
    rw [show (-(1/2) : ℝ) - 1 = -(3/2) by ring]
    ring
  rw [hsimp] at h
  exact h

lemma Qfun_ode {x : ℝ} (hx : x < 1) :
    (1 - x) * ((1/2) * (1-x)^(-(3/2) : ℝ)) = (1/2) * Qfun x := by
  unfold Qfun
  have hpos : (0:ℝ) < 1 - x := by linarith
  have h := Real.rpow_add hpos (1:ℝ) (-(3/2) : ℝ)
  rw [show (1:ℝ) + (-(3/2)) = -(1/2) by ring, Real.rpow_one] at h
  rw [h]
  ring

/-- If a function differentiable on `(-1,1)` has derivative zero there and vanishes at `0`,
then it vanishes identically. -/
lemma eq_zero_of_hasDerivAt_zero {f : ℝ → ℝ}
    (h : ∀ y ∈ Set.Ioo (-1:ℝ) 1, HasDerivAt f 0 y) (h0 : f 0 = 0) :
    ∀ x ∈ Set.Ioo (-1:ℝ) 1, f x = 0 := by
  intro x hx
  rcases lt_trichotomy x 0 with hlt | heq | hgt
  · obtain ⟨c, hc, hcd⟩ := exists_deriv_eq_slope f hlt
      (fun y hy => ((h y ⟨by linarith [hy.1, hx.1], by linarith [hy.2]⟩).continuousAt).continuousWithinAt)
      (fun y hy => (h y ⟨by linarith [hy.1, hx.1], by linarith [hy.2]⟩).differentiableAt.differentiableWithinAt)
    have hc' : c ∈ Set.Ioo (-1:ℝ) 1 := ⟨by linarith [hc.1, hx.1], by linarith [hc.2]⟩
    rw [(h c hc').deriv] at hcd
    have hne : (0:ℝ) - x ≠ 0 := by linarith
    field_simp at hcd
    linarith [hcd]
  · rw [heq]; exact h0
  · obtain ⟨c, hc, hcd⟩ := exists_deriv_eq_slope f hgt
      (fun y hy => ((h y ⟨by linarith [hy.1], by linarith [hy.2, hx.2]⟩).continuousAt).continuousWithinAt)
      (fun y hy => (h y ⟨by linarith [hy.1], by linarith [hy.2, hx.2]⟩).differentiableAt.differentiableWithinAt)
    have hc' : c ∈ Set.Ioo (-1:ℝ) 1 := ⟨by linarith [hc.1], by linarith [hc.2, hx.2]⟩
    rw [(h c hc').deriv] at hcd
    have hne : x - 0 ≠ 0 := by linarith
    field_simp at hcd
    linarith [hcd]

/-- `∑ b_k x^k = (1-x)^{-1/2}` on `(-1,1)`. -/
theorem Bfun_eq {x : ℝ} (hx : |x| < 1) : Bfun x = (1 - x) ^ (-(1/2) : ℝ) := by
  obtain ⟨hx1, hx2⟩ := abs_lt.mp hx
  set D : ℝ → ℝ := fun y => Bfun y - Qfun y with hD
  have hDderiv : ∀ y ∈ Set.Ioo (-1:ℝ) 1, HasDerivAt D (D y / (2*(1-y))) y := by
    intro y hy
    have hy1 : y < 1 := hy.2
    have habs : |y| < 1 := by rw [abs_lt]; exact hy
    have h1 : HasDerivAt Bfun (Afun y) y := hasDerivAt_Bfun habs
    have h2 : HasDerivAt Qfun ((1/2)*(1-y)^(-(3/2) : ℝ)) y := hasDerivAt_Qfun hy1
    have hB := Bfun_ode habs
    have hQ := Qfun_ode hy1
    have hne : (1:ℝ) - y ≠ 0 := by linarith
    have hval : Afun y - (1/2)*(1-y)^(-(3/2) : ℝ) = (Bfun y - Qfun y)/(2*(1-y)) := by
      field_simp
      linarith [hB, hQ]
    have h3 : HasDerivAt (fun z => Bfun z - Qfun z) ((Bfun y - Qfun y)/(2*(1-y))) y := by
      have h1' : HasDerivAt (fun z => Bfun z - Qfun z)
          (Afun y - (1/2)*(1-y)^(-(3/2) : ℝ)) y := h1.sub h2
      rw [hval] at h1'
      exact h1'
    rw [hD]
    exact h3
  have hE : ∀ y ∈ Set.Ioo (-1:ℝ) 1, HasDerivAt (fun z => (D z)^2 * (1-z)) 0 y := by
    intro y hy
    have h1 : HasDerivAt D (D y / (2*(1-y))) y := hDderiv y hy
    have h2 : HasDerivAt (fun z => D z * D z)
        ((D y/(2*(1-y))) * D y + D y * (D y/(2*(1-y)))) y := h1.mul h1
    have h3 : HasDerivAt (fun z : ℝ => 1 - z) (-1) y := by
      simpa using (hasDerivAt_id y).const_sub (1:ℝ)
    have h4 : HasDerivAt (fun z => (D z * D z) * (1-z))
        (((D y/(2*(1-y))) * D y + D y * (D y/(2*(1-y)))) * (1-y) + (D y * D y) * (-1)) y :=
      h2.mul h3
    have hne : (1:ℝ) - y ≠ 0 := by linarith [hy.2]
    have hzero : ((D y/(2*(1-y))) * D y + D y * (D y/(2*(1-y)))) * (1-y) + (D y * D y) * (-1) = 0 := by
      field_simp
      ring
    rw [hzero] at h4
    convert h4 using 1
    ring_nf
  have hone := eq_zero_of_hasDerivAt_zero hE (by simp [D, Bfun_zero, Qfun])
  have hdx : D x = 0 := by
    have hz := hone x ⟨hx1, hx2⟩
    have h1x : (0:ℝ) < 1 - x := by linarith
    have hsq : (D x)^2 = 0 := by
      rcases mul_eq_zero.mp hz with h | h
      · exact h
      · exact absurd h (ne_of_gt h1x)
    by_contra hne0
    have hpos : (0:ℝ) < (D x)^2 := by positivity
    linarith
  rw [hD] at hdx
  simpa [Qfun, sub_eq_zero] using hdx

/-! ## 4. The arcsine series `∑_k (b_k/(2k+1)) t^{2k+1} = arcsin t` -/

/-- the arcsine series. -/
def Ffun (t : ℝ) : ℝ := ∑' k : ℕ, bc k / (2*(k:ℝ)+1) * t^(2*k+1)

lemma Ffun_zero : Ffun 0 = 0 := by
  rw [Ffun]
  have h : (fun k : ℕ => bc k / (2*(k:ℝ)+1) * (0:ℝ)^(2*k+1)) = fun _ => 0 := by
    funext k
    have hz : (2*k+1) ≠ 0 := by omega
    rw [zero_pow hz]
    ring
  rw [h, tsum_zero]

lemma summable_Ffun {t : ℝ} (ht : |t| < 1) :
    Summable (fun k : ℕ => bc k / (2*(k:ℝ)+1) * t^(2*k+1)) := by
  have hg : Summable (fun k : ℕ => |t|^k) :=
    summable_geometric_of_norm_lt_one (by simpa only [Real.norm_eq_abs, abs_abs] using ht)
  refine Summable.of_norm_bounded hg (fun n => ?_)
  have hd : (0:ℝ) < 2*(n:ℝ)+1 := by positivity
  have hstep : ‖bc n / (2*(n:ℝ)+1) * t^(2*n+1)‖ = bc n / (2*(n:ℝ)+1) * |t|^(2*n+1) := by
    rw [Real.norm_eq_abs, abs_mul, abs_div, abs_of_pos (bc_pos n), abs_of_pos hd, abs_pow]
  rw [hstep]
  have ht0 : |t| < 1 := ht
  have ht1 : |t| ^ (2*n+1) ≤ |t|^n := by
    have hnn : (0:ℝ) ≤ |t| := abs_nonneg t
    exact pow_le_pow_of_le_one hnn ht0.le (by omega)
  have hle : bc n / (2*(n:ℝ)+1) * |t|^(2*n+1) ≤ 1 * |t|^n := by
    have hbc : bc n / (2*(n:ℝ)+1) ≤ 1 := by
      rw [div_le_one hd]
      have h1 : bc n ≤ 1 := bc_le_one n
      linarith
    have hnn : (0:ℝ) ≤ |t|^(2*n+1) := by positivity
    calc bc n / (2*(n:ℝ)+1) * |t|^(2*n+1) ≤ 1 * |t|^(2*n+1) :=
          mul_le_mul_of_nonneg_right hbc hnn
      _ ≤ 1 * |t|^n := mul_le_mul_of_nonneg_left ht1 zero_le_one
  simpa using hle

/-- `Ffun` has derivative `Bfun (t^2) = (1-t^2)^{-1/2}`. -/
lemma hasDerivAt_Ffun {t : ℝ} (ht : |t| < 1) : HasDerivAt Ffun (Bfun (t^2)) t := by
  obtain ⟨r, hrt, hr1⟩ : ∃ r : ℝ, |t| < r ∧ r < 1 := ⟨(|t| + 1)/2, by linarith, by linarith⟩
  have hr0 : 0 < r := lt_of_le_of_lt (abs_nonneg t) hrt
  have hmem : t ∈ Set.Ioo (-r) r := by
    rw [Set.mem_Ioo]
    exact ⟨by linarith [neg_abs_le t], by linarith [le_abs_self t]⟩
  -- summable bound: r^{2n}
  have hr2 : r^2 < 1 := by nlinarith [hr0, hr1]
  have hu : Summable (fun n : ℕ => ((r^2)^n)) := by
    apply summable_geometric_of_norm_lt_one
    rw [Real.norm_eq_abs, abs_of_pos (by positivity : (0:ℝ) < r^2)]
    exact hr2
  have hderiv : ∀ (n : ℕ) (y : ℝ), y ∈ Set.Ioo (-r) r →
      HasDerivAt (fun y : ℝ => bc n / (2*(n:ℝ)+1) * y^(2*n+1)) (bc n * y^(2*n)) y := by
    intro n y _
    have h1 : HasDerivAt (fun y : ℝ => y^(2*n+1)) ((2*(n:ℝ)+1) * y^(2*n)) y := by
      have h := hasDerivAt_pow (2*n+1) y
      have he : ((2*n+1 : ℕ) : ℝ) = 2*(n:ℝ)+1 := by push_cast; ring
      rw [he] at h
      have hsub : 2*n+1-1 = 2*n := by omega
      rw [hsub] at h
      exact h
    have h2 := h1.const_mul (bc n / (2*(n:ℝ)+1))
    have hden : (2*(n:ℝ)+1) ≠ 0 := by positivity
    have heq : bc n / (2*(n:ℝ)+1) * ((2*(n:ℝ)+1) * y^(2*n)) = bc n * y^(2*n) := by
      field_simp
    rw [heq] at h2
    exact h2
  have hbound : ∀ (n : ℕ) (y : ℝ), y ∈ Set.Ioo (-r) r → ‖bc n * y^(2*n)‖ ≤ (r^2)^n := by
    intro n y hy
    have hy' : |y| ≤ r := by rw [abs_le]; exact ⟨le_of_lt hy.1, le_of_lt hy.2⟩
    have hstep : ‖bc n * y^(2*n)‖ = bc n * |y|^(2*n) := by
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (bc_pos n), abs_pow]
    rw [hstep]
    have h1 : bc n ≤ 1 := bc_le_one n
    have hpow : |y|^(2*n) ≤ r^(2*n) := pow_le_pow_left₀ (abs_nonneg y) hy' _
    have hrw : r^(2*n) = (r^2)^n := by rw [← pow_mul]
    rw [hrw] at hpow
    calc bc n * |y|^(2*n) ≤ 1 * (r^2)^n := by
          apply mul_le_mul h1 hpow (by positivity) (by positivity)
      _ = (r^2)^n := by ring
  have hpt : (0:ℝ) ∈ Set.Ioo (-r) r := ⟨by linarith, by linarith⟩
  have hsum0 : Summable (fun n : ℕ => bc n / (2*(n:ℝ)+1) * (0:ℝ)^(2*n+1)) := by
    refine summable_of_ne_finset_zero (s := (∅ : Finset ℕ)) ?_
    intro n _
    have h : (2*n+1) ≠ 0 := by omega
    rw [zero_pow h]
    ring
  have hmain := hasDerivAt_tsum_of_isPreconnected (𝕜 := ℝ) (F := ℝ) (y₀ := (0:ℝ))
    (u := fun n : ℕ => (r^2)^n)
    (g := fun (n:ℕ) (y:ℝ) => bc n / (2*(n:ℝ)+1) * y^(2*n+1))
    (g' := fun (n:ℕ) (y:ℝ) => bc n * y^(2*n))
    (t := Set.Ioo (-r) r) hu isOpen_Ioo isPreconnected_Ioo hderiv hbound hpt hsum0 hmem
  have hfin : (∑' n : ℕ, bc n * t^(2*n)) = Bfun (t^2) := by
    rw [Bfun]
    exact tsum_congr (fun n => by rw [pow_mul])
  rw [← hfin]
  exact hmain

/-- `arcsin` has derivative `(1-t²)^{-1/2}` on `(-1,1)`. -/
lemma hasDerivAt_arcsin' {t : ℝ} (ht : |t| < 1) :
    HasDerivAt Real.arcsin ((1 - t^2) ^ (-(1/2) : ℝ)) t := by
  have ht1 : t ≠ 1 := by
    intro h; rw [h] at ht; norm_num at ht
  have ht2 : t ≠ -1 := by
    intro h; rw [h] at ht; norm_num at ht
  have h := Real.hasDerivAt_arcsin ht2 ht1
  have hpos : (0:ℝ) < 1 - t^2 := by
    have := abs_lt.mp ht
    nlinarith [this.1, this.2]
  have heq : (1:ℝ) / √(1 - t^2) = (1 - t^2) ^ (-(1/2) : ℝ) := by
    rw [Real.sqrt_eq_rpow, one_div, ← Real.rpow_neg hpos.le]
  rw [heq] at h
  exact h

/-- the arcsine series is `arcsin` on `(-1,1)`. -/
theorem Ffun_eq_arcsin {t : ℝ} (ht : |t| < 1) : Ffun t = Real.arcsin t := by
  have key : ∀ y ∈ Set.Ioo (-1:ℝ) 1, HasDerivAt (fun z => Ffun z - Real.arcsin z) 0 y := by
    intro y hy
    have hyabs : |y| < 1 := by rw [abs_lt]; exact hy
    have h1 : HasDerivAt Ffun (Bfun (y^2)) y := hasDerivAt_Ffun hyabs
    have h2 : HasDerivAt Real.arcsin ((1-y^2)^(-(1/2):ℝ)) y := hasDerivAt_arcsin' hyabs
    have hy2 : |y^2| < 1 := by
      rw [abs_lt]; constructor <;> nlinarith [hy.1, hy.2]
    have h3 : Bfun (y^2) = (1-y^2)^(-(1/2):ℝ) := Bfun_eq hy2
    have h4 : HasDerivAt (fun z => Ffun z - Real.arcsin z)
        (Bfun (y^2) - (1-y^2)^(-(1/2):ℝ)) y := h1.sub h2
    rw [h3, sub_self] at h4
    exact h4
  have h0 : (fun z => Ffun z - Real.arcsin z) 0 = 0 := by
    simp [Ffun_zero]
  have hfin := eq_zero_of_hasDerivAt_zero key h0 t (abs_lt.mp ht)
  simp only [sub_eq_zero] at hfin
  exact hfin

/-! ## 5. `Er 1 t = (2/π) arcsin t` -/

lemma Cr_one : Cr 1 = 2 / Real.pi := by
  unfold Cr
  norm_num
  rw [Real.Gamma_one_half_eq, Real.sq_sqrt Real.pi_pos.le, div_eq_mul_inv]

lemma ErCoeff_one (k : ℕ) : ErCoeff 1 k = Cr 1 * (bc k / (2*(k:ℝ)+1)) := by
  unfold ErCoeff bc
  simp only [Nat.cast_one]
  rw [risingFact_three_half]
  push_cast
  have hpos : (0:ℝ) < risingFact (1/2) k := risingFact_half_pos k
  have hk : ((k.factorial : ℕ) : ℝ) ≠ 0 := by
    have : (0:ℝ) < (k.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos k
    exact ne_of_gt this
  have h2k : (2*(k:ℝ)+1) ≠ 0 := by positivity
  field_simp

/-- **The `r = 1` case of the right-hand side of Lemma 2.1**: `E_1(t) = (2/π) arcsin t`. -/
theorem Er_one_arcsin {t : ℝ} (ht : |t| < 1) : Er 1 t = 2 / Real.pi * Real.arcsin t := by
  have hsummable : Summable (fun k : ℕ => bc k / (2*(k:ℝ)+1) * t^(2*k+1)) := summable_Ffun ht
  have hstep : (∑' k : ℕ, ErCoeff 1 k * t^(2*k+1)) = (2/Real.pi) * Ffun t := by
    rw [Ffun, ← Summable.tsum_mul_left (2/Real.pi) hsummable]
    exact tsum_congr (fun k => by rw [ErCoeff_one, Cr_one]; ring)
  rw [Er, hstep, Ffun_eq_arcsin ht]

/-! ## 6. The boundary points `t = ±1` -/

lemma bc_telescope (k : ℕ) : bc k - bc (k+1) = bc k / (2*((k:ℝ)+1)) := by
  have h := bc_succ k
  have hk : ((k:ℝ)+1) ≠ 0 := by positivity
  field_simp at h ⊢
  linarith

lemma bc_div_le (k : ℕ) : bc k / (2*(k:ℝ)+1) ≤ 2 * (bc k - bc (k+1)) := by
  rw [bc_telescope]
  have h1 : (0:ℝ) < (k:ℝ)+1 := by positivity
  have h3 : (0:ℝ) ≤ bc k := bc_nonneg k
  have h4 : (k:ℝ)+1 ≤ 2*(k:ℝ)+1 := by
    have : (0:ℝ) ≤ (k:ℝ) := Nat.cast_nonneg k
    linarith
  have h5 : bc k / (2*(k:ℝ)+1) ≤ bc k / ((k:ℝ)+1) :=
    div_le_div_of_nonneg_left h3 h1 h4
  have h6 : (2:ℝ) * (bc k / (2*((k:ℝ)+1))) = bc k / ((k:ℝ)+1) := by
    field_simp
  rw [h6]
  exact h5

lemma summable_bc_div : Summable (fun k : ℕ => bc k / (2*(k:ℝ)+1)) := by
  refine summable_of_sum_range_le (f := fun k : ℕ => bc k / (2*(k:ℝ)+1)) (c := 2)
    (fun n => ?_) (fun n => ?_)
  · have h1 : (0:ℝ) < bc n := bc_pos n
    have h2 : (0:ℝ) < 2*(n:ℝ)+1 := by positivity
    positivity
  · calc ∑ k ∈ Finset.range n, bc k / (2*(k:ℝ)+1)
        ≤ ∑ k ∈ Finset.range n, 2 * (bc k - bc (k+1)) :=
          Finset.sum_le_sum (fun k _ => bc_div_le k)
      _ = 2 * (bc 0 - bc n) := by
          rw [← Finset.mul_sum]
          have h := Finset.sum_range_sub (f := bc) n
          have h2 : ∑ i ∈ Finset.range n, (bc i - bc (i + 1))
              = -(∑ i ∈ Finset.range n, (bc (i + 1) - bc i)) := by
            rw [← Finset.sum_neg_distrib]
            exact Finset.sum_congr rfl (fun i _ => by ring)
          rw [h2, h]
          ring
      _ ≤ 2 := by
          have h1 : bc 0 = 1 := bc_zero
          have h2 : 0 < bc n := bc_pos n
          rw [h1]
          linarith

lemma ErCoeff_one_nonneg (n : ℕ) : 0 ≤ ErCoeff 1 n := by
  rw [ErCoeff_one]
  have h1 : (0:ℝ) < Cr 1 := by rw [Cr_one]; positivity
  have h2 : (0:ℝ) ≤ bc n / (2*(n:ℝ)+1) := by
    have h3 : (0:ℝ) < bc n := bc_pos n
    have h4 : (0:ℝ) < 2*(n:ℝ)+1 := by positivity
    positivity
  positivity

lemma summable_ErCoeff_one : Summable (fun k : ℕ => ErCoeff 1 k) := by
  have h := summable_bc_div.mul_left (Cr 1)
  have h2 : (fun k : ℕ => Cr 1 * (bc k / (2*(k:ℝ)+1))) = fun k => ErCoeff 1 k := by
    funext k
    exact (ErCoeff_one k).symm
  rw [h2] at h
  exact h

lemma continuousOn_Er_one : ContinuousOn (fun t => Er 1 t) (Set.Icc (-1:ℝ) 1) := by
  have hu := summable_ErCoeff_one
  have hb : ∀ (n : ℕ) (x : ℝ), x ∈ Set.Icc (-1:ℝ) 1 →
      ‖ErCoeff 1 n * x^(2*n+1)‖ ≤ ErCoeff 1 n := by
    intro n x hx
    have hx1 : |x| ≤ 1 := by rw [abs_le]; exact ⟨hx.1, hx.2⟩
    have hlt : |x|^(2*n+1) ≤ 1 := pow_le_one₀ (abs_nonneg x) hx1
    rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg (ErCoeff_one_nonneg n)]
    calc ErCoeff 1 n * |x|^(2*n+1) ≤ ErCoeff 1 n * 1 := by
          apply mul_le_mul_of_nonneg_left hlt (ErCoeff_one_nonneg n)
      _ = ErCoeff 1 n := by ring
  have hunif := tendstoUniformlyOn_tsum hu hb
  have hcont : ∀ (s : Finset ℕ), ContinuousOn
      (fun t : ℝ => ∑ k ∈ s, ErCoeff 1 k * t^(2*k+1)) (Set.Icc (-1:ℝ) 1) := by
    intro s
    have hc : Continuous (fun t : ℝ => ∑ k ∈ s, ErCoeff 1 k * t^(2*k+1)) := by
      apply continuous_finset_sum
      intro k _
      fun_prop
    exact hc.continuousOn
  exact hunif.continuousOn (Eventually.of_forall hcont).frequently

theorem Er_one_Icc {t : ℝ} (ht : t ∈ Set.Icc (-1:ℝ) 1) :
    Er 1 t = 2 / Real.pi * Real.arcsin t := by
  obtain ⟨ht1, ht2⟩ := ht
  have keym1 : Er 1 (-1) = 2 / Real.pi * Real.arcsin (-1) := by
    haveI : (𝓝[Set.Ioo (-1:ℝ) 1] (-1)).NeBot := by
      rw [← mem_closure_iff_nhdsWithin_neBot, closure_Ioo (by norm_num : (-1:ℝ) ≠ 1)]
      exact ⟨le_rfl, by norm_num⟩
    have hcontIcc : ContinuousWithinAt (fun t => Er 1 t) (Set.Icc (-1:ℝ) 1) (-1) :=
      continuousOn_Er_one.continuousWithinAt (by simp)
    have h2 : Tendsto (fun t => Er 1 t) (𝓝[Set.Ioo (-1:ℝ) 1] (-1)) (𝓝 (Er 1 (-1))) :=
      hcontIcc.mono_left (nhdsWithin_mono _ Set.Ioo_subset_Icc_self)
    have hg : ContinuousWithinAt (fun t => 2 / Real.pi * Real.arcsin t) (Set.Ioo (-1:ℝ) 1) (-1) :=
      (continuous_const.mul Real.continuous_arcsin).continuousWithinAt
    have h3 : Tendsto (fun t => Er 1 t) (𝓝[Set.Ioo (-1:ℝ) 1] (-1))
        (𝓝 (2 / Real.pi * Real.arcsin (-1))) :=
      hg.congr' (eventually_of_mem self_mem_nhdsWithin
        (fun y hy => (Er_one_arcsin (by rw [abs_lt]; exact hy)).symm))
    exact tendsto_nhds_unique h2 h3
  have key1 : Er 1 1 = 2 / Real.pi * Real.arcsin 1 := by
    haveI : (𝓝[Set.Ioo (-1:ℝ) 1] 1).NeBot := by
      rw [← mem_closure_iff_nhdsWithin_neBot, closure_Ioo (by norm_num : (-1:ℝ) ≠ 1)]
      exact ⟨by norm_num, le_rfl⟩
    have hcontIcc : ContinuousWithinAt (fun t => Er 1 t) (Set.Icc (-1:ℝ) 1) 1 :=
      continuousOn_Er_one.continuousWithinAt (by simp)
    have h2 : Tendsto (fun t => Er 1 t) (𝓝[Set.Ioo (-1:ℝ) 1] 1) (𝓝 (Er 1 1)) :=
      hcontIcc.mono_left (nhdsWithin_mono _ Set.Ioo_subset_Icc_self)
    have hg : ContinuousWithinAt (fun t => 2 / Real.pi * Real.arcsin t) (Set.Ioo (-1:ℝ) 1) 1 :=
      (continuous_const.mul Real.continuous_arcsin).continuousWithinAt
    have h3 : Tendsto (fun t => Er 1 t) (𝓝[Set.Ioo (-1:ℝ) 1] 1)
        (𝓝 (2 / Real.pi * Real.arcsin 1)) :=
      hg.congr' (eventually_of_mem self_mem_nhdsWithin
        (fun y hy => (Er_one_arcsin (by rw [abs_lt]; exact hy)).symm))
    exact tendsto_nhds_unique h2 h3
  rcases lt_trichotomy t 1 with hlt | heq | hgt
  · rcases lt_trichotomy t (-1) with h | h | h
    · linarith
    · rw [h]; exact keym1
    · exact Er_one_arcsin (by rw [abs_lt]; exact ⟨h, hlt⟩)
  · rw [heq]; exact key1
  · linarith

/-! ## 7. General facts about `Cr`, `ErCoeff`, `Er` (for `r ≥ 1`) -/

lemma Cr_pos {r : ℕ} (hr : 1 ≤ r) : 0 < Cr r := by
  unfold Cr
  have hr0 : (0:ℝ) < (r:ℝ) := by exact_mod_cast hr
  have h1 : (0:ℝ) < Real.Gamma (((r:ℝ)+1)/2) :=
    Real.Gamma_pos_of_pos (by linarith)
  have h2 : (0:ℝ) < Real.Gamma ((r:ℝ)/2) :=
    Real.Gamma_pos_of_pos (by linarith)
  have : (0:ℝ) < Real.Gamma (((r:ℝ)+1)/2) / Real.Gamma ((r:ℝ)/2) := div_pos h1 h2
  positivity

lemma risingFact_half_sq_pos (k : ℕ) : 0 < (risingFact (1/2) k)^2 := by
  have := risingFact_half_pos k
  positivity

lemma risingFact_arg_pos {r : ℕ} (hr : 1 ≤ r) (k : ℕ) : 0 < risingFact ((r:ℝ)/2+1) k := by
  unfold risingFact
  apply Finset.prod_pos
  intro i _
  have h1 : (0:ℝ) ≤ (i:ℝ) := Nat.cast_nonneg i
  have h2 : (0:ℝ) < (r:ℝ) := by exact_mod_cast hr
  push_cast
  linarith

theorem ErCoeff_nonneg_m {r : ℕ} (hr : 1 ≤ r) (k : ℕ) : 0 ≤ ErCoeff r k := by
  unfold ErCoeff
  have h1 : 0 < Cr r := Cr_pos hr
  have h2 : 0 < (risingFact (1/2) k)^2 := risingFact_half_sq_pos k
  have h3 : 0 < risingFact ((r:ℝ)/2+1) k := risingFact_arg_pos hr k
  have h4 : (0:ℝ) < (k.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos k
  positivity

theorem Er_zero_m (r : ℕ) : Er r 0 = 0 := by
  rw [Er]
  have h : (fun k : ℕ => ErCoeff r k * (0:ℝ)^(2*k+1)) = fun _ => 0 := by
    funext k
    have hz : (2*k+1) ≠ 0 := by omega
    rw [zero_pow hz]
    ring
  rw [h, tsum_zero]

/-- For `r = 1`, `E_1` maps `[-1,1]` into `[-1,1]`. -/
theorem abs_Er_one_le_one {t : ℝ} (ht : t ∈ Set.Icc (-1:ℝ) 1) : |Er 1 t| ≤ 1 := by
  rw [Er_one_Icc ht, abs_mul]
  have hpi : (0:ℝ) < Real.pi := Real.pi_pos
  have h1 : |2 / Real.pi| = 2 / Real.pi := by
    rw [abs_of_pos]; positivity
  rw [h1]
  have h2 : |Real.arcsin t| ≤ Real.pi / 2 :=
    abs_le.mpr ⟨Real.neg_pi_div_two_le_arcsin t, Real.arcsin_le_pi_div_two t⟩
  calc 2 / Real.pi * |Real.arcsin t| ≤ 2 / Real.pi * (Real.pi / 2) := by
        apply mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = 1 := by field_simp

end Grothendieck

namespace Grothendieck

/-! ## 8. Summability, continuity and monotonicity of `Er r` for `r ≥ 1` -/

lemma risingFact_mono_arg {r : ℕ} (hr : 1 ≤ r) (k : ℕ) :
    risingFact (1/2+1) k ≤ risingFact ((r:ℝ)/2+1) k := by
  unfold risingFact
  apply Finset.prod_le_prod
  · intro i _
    have h : (0:ℝ) ≤ (i:ℝ) := Nat.cast_nonneg i
    linarith
  · intro i _
    have h : (1:ℝ) ≤ (r:ℝ) := by exact_mod_cast hr
    linarith

lemma ErCoeff_le {r : ℕ} (hr : 1 ≤ r) (k : ℕ) :
    ErCoeff r k ≤ Cr r * (bc k / (2*(k:ℝ)+1)) := by
  unfold ErCoeff
  have hC : 0 < Cr r := Cr_pos hr
  have hsq : 0 < (risingFact (1/2) k)^2 := risingFact_half_sq_pos k
  have hfk : (0:ℝ) < (k.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos k
  have hden1 : 0 < risingFact (1/2+1) k := by
    unfold risingFact
    apply Finset.prod_pos
    intro i _
    have h : (0:ℝ) ≤ (i:ℝ) := Nat.cast_nonneg i
    push_cast
    linarith
  have hden2 : 0 < risingFact ((r:ℝ)/2+1) k := risingFact_arg_pos hr k
  have hmono : risingFact (1/2+1) k ≤ risingFact ((r:ℝ)/2+1) k := risingFact_mono_arg hr k
  have h1 : (risingFact (1/2) k)^2 / (risingFact ((r:ℝ)/2+1) k * (k.factorial:ℝ))
      ≤ (risingFact (1/2) k)^2 / (risingFact (1/2+1) k * (k.factorial:ℝ)) := by
    apply div_le_div_of_nonneg_left (le_of_lt hsq) (by positivity)
    exact mul_le_mul_of_nonneg_right hmono (le_of_lt hfk)
  calc Cr r * (risingFact (1/2) k)^2 / (risingFact ((r:ℝ)/2+1) k * (k.factorial:ℝ))
      = Cr r * ((risingFact (1/2) k)^2 / (risingFact ((r:ℝ)/2+1) k * (k.factorial:ℝ))) := by
        field_simp
    _ ≤ Cr r * ((risingFact (1/2) k)^2 / (risingFact (1/2+1) k * (k.factorial:ℝ))) := by
        apply mul_le_mul_of_nonneg_left h1 (le_of_lt hC)
    _ = Cr r * (bc k / (2*(k:ℝ)+1)) := by
        rw [risingFact_three_half]
        unfold bc
        have h2k : (0:ℝ) < 2*(k:ℝ)+1 := by positivity
        have hrf : (0:ℝ) < risingFact (1/2) k := risingFact_half_pos k
        field_simp

lemma summable_ErCoeff {r : ℕ} (hr : 1 ≤ r) : Summable (fun k : ℕ => ErCoeff r k) := by
  have h := summable_bc_div.mul_left (Cr r)
  exact Summable.of_nonneg_of_le (fun k => ErCoeff_nonneg_m hr k) (fun k => ErCoeff_le hr k) h

/-- `Er r` is continuous on `[-1,1]` for every `r ≥ 1`. -/
lemma continuousOn_Er {r : ℕ} (hr : 1 ≤ r) : ContinuousOn (fun t => Er r t) (Set.Icc (-1:ℝ) 1) := by
  have hu := summable_ErCoeff hr
  have hb : ∀ (n : ℕ) (x : ℝ), x ∈ Set.Icc (-1:ℝ) 1 →
      ‖ErCoeff r n * x^(2*n+1)‖ ≤ ErCoeff r n := by
    intro n x hx
    have hx1 : |x| ≤ 1 := by rw [abs_le]; exact ⟨hx.1, hx.2⟩
    have hlt : |x|^(2*n+1) ≤ 1 := pow_le_one₀ (abs_nonneg x) hx1
    rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg (ErCoeff_nonneg_m hr n)]
    calc ErCoeff r n * |x|^(2*n+1) ≤ ErCoeff r n * 1 :=
          mul_le_mul_of_nonneg_left hlt (ErCoeff_nonneg_m hr n)
      _ = ErCoeff r n := by ring
  have hunif := tendstoUniformlyOn_tsum hu hb
  have hcont : ∀ (s : Finset ℕ), ContinuousOn
      (fun t : ℝ => ∑ k ∈ s, ErCoeff r k * t^(2*k+1)) (Set.Icc (-1:ℝ) 1) := by
    intro s
    have hc : Continuous (fun t : ℝ => ∑ k ∈ s, ErCoeff r k * t^(2*k+1)) := by
      apply continuous_finset_sum
      intro k _
      fun_prop
    exact hc.continuousOn
  exact hunif.continuousOn (Eventually.of_forall hcont).frequently

/-- `Er r` is monotone on `[0,1]` for `r ≥ 1`. -/
lemma Er_mono {r : ℕ} (hr : 1 ≤ r) {s t : ℝ} (hs : s ∈ Set.Icc (0:ℝ) 1)
    (ht : t ∈ Set.Icc (0:ℝ) 1) (hst : s ≤ t) : Er r s ≤ Er r t := by
  have hsum : Summable (fun k : ℕ => ErCoeff r k * t^(2*k+1)) := by
    refine Summable.of_nonneg_of_le (fun k => ?_) (fun k => ?_) (summable_ErCoeff hr)
    · exact mul_nonneg (ErCoeff_nonneg_m hr k) (pow_nonneg ht.1 _)
    · calc ErCoeff r k * t^(2*k+1) ≤ ErCoeff r k * 1 :=
            mul_le_mul_of_nonneg_left (pow_le_one₀ ht.1 (by linarith [ht.2]))
              (ErCoeff_nonneg_m hr k)
        _ = ErCoeff r k := by ring
  have hsum_s : Summable (fun k : ℕ => ErCoeff r k * s^(2*k+1)) := by
    refine Summable.of_nonneg_of_le (fun k => ?_) (fun k => ?_) (summable_ErCoeff hr)
    · exact mul_nonneg (ErCoeff_nonneg_m hr k) (pow_nonneg hs.1 _)
    · calc ErCoeff r k * s^(2*k+1) ≤ ErCoeff r k * 1 :=
            mul_le_mul_of_nonneg_left (pow_le_one₀ hs.1 (by linarith [hs.2]))
              (ErCoeff_nonneg_m hr k)
        _ = ErCoeff r k := by ring
  have hle : ∀ k, ErCoeff r k * s^(2*k+1) ≤ ErCoeff r k * t^(2*k+1) := by
    intro k
    apply mul_le_mul_of_nonneg_left _ (ErCoeff_nonneg_m hr k)
    apply pow_le_pow_left₀ hs.1 hst
  rw [Er, Er]
  exact Summable.tsum_le_tsum hle hsum_s hsum

lemma Er_mono_summable {r : ℕ} (hr : 1 ≤ r) {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    Summable (fun k : ℕ => ErCoeff r k * t^(2*k+1)) := by
  refine Summable.of_nonneg_of_le (fun k => ?_) (fun k => ?_) (summable_ErCoeff hr)
  · exact mul_nonneg (ErCoeff_nonneg_m hr k) (pow_nonneg h0 _)
  · calc ErCoeff r k * t^(2*k+1) ≤ ErCoeff r k * 1 :=
          mul_le_mul_of_nonneg_left (pow_le_one₀ h0 h1) (ErCoeff_nonneg_m hr k)
      _ = ErCoeff r k := by ring

/-! ## 8b. Strict monotonicity of `Er r` on `[0,1]` -/

lemma pow_sub_pow_nonneg {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (m : ℕ) :
    0 ≤ t^(2*m+1) - s^(2*m+1) :=
  sub_nonneg.mpr (pow_le_pow_left₀ hs hst _)

/-- `Er r` is strictly increasing on `[0,1]` for `r ≥ 1`. -/
theorem Er_strictMono_proof {r : ℕ} (hr : 1 ≤ r) {s t : ℝ} (hs : 0 ≤ s) (hst : s < t)
    (ht : t ≤ 1) : Er r s < Er r t := by
  have hstle : s ≤ t := le_of_lt hst
  have hs1 : s ≤ 1 := le_trans hstle ht
  -- summability of the difference series
  have ht0 : (0:ℝ) ≤ t := le_trans hs hstle
  have hdiff : Summable (fun k : ℕ => ErCoeff r k * t^(2*k+1) - ErCoeff r k * s^(2*k+1)) :=
    (Er_mono_summable hr ht0 ht).sub (Er_mono_summable hr hs hs1)
  have hnonneg : ∀ k, 0 ≤ (ErCoeff r k * t^(2*k+1) - ErCoeff r k * s^(2*k+1)) := by
    intro k
    have h := pow_sub_pow_nonneg hs hstle k
    have h2 : ErCoeff r k * t^(2*k+1) - ErCoeff r k * s^(2*k+1)
        = ErCoeff r k * (t^(2*k+1) - s^(2*k+1)) := by ring
    rw [h2]
    exact mul_nonneg (ErCoeff_nonneg_m hr k) h
  have hpos0 : 0 < ErCoeff r 0 * t^(2*0+1) - ErCoeff r 0 * s^(2*0+1) := by
    have hC : 0 < Cr r := Cr_pos hr
    have hE0 : ErCoeff r 0 = Cr r := by
      unfold ErCoeff
      norm_num [risingFact]
    have hE : 0 < ErCoeff r 0 := by rw [hE0]; exact hC
    have hpow : ∀ x : ℝ, x^(2*0+1) = x := by intro x; norm_num
    have : ErCoeff r 0 * t^(2*0+1) - ErCoeff r 0 * s^(2*0+1) = ErCoeff r 0 * (t - s) := by
      rw [hpow t, hpow s]; ring
    rw [this]
    exact mul_pos hE (sub_pos.mpr hst)
  have htsum : 0 < ∑' k : ℕ, (ErCoeff r k * t^(2*k+1) - ErCoeff r k * s^(2*k+1)) :=
    hdiff.tsum_pos hnonneg 0 hpos0
  have hsplit : (∑' k : ℕ, (ErCoeff r k * t^(2*k+1) - ErCoeff r k * s^(2*k+1)))
      = Er r t - Er r s := by
    show (∑' k : ℕ, (ErCoeff r k * t^(2*k+1) - ErCoeff r k * s^(2*k+1)))
        = (∑' k : ℕ, ErCoeff r k * t^(2*k+1)) - (∑' k : ℕ, ErCoeff r k * s^(2*k+1))
    rw [Summable.tsum_sub (Er_mono_summable hr ht0 ht) (Er_mono_summable hr hs hs1)]
  rw [hsplit] at htsum
  linarith

/-! ## 8c. Oddness and injectivity of `Er r` -/

lemma summable_Er_abs {r : ℕ} (hr : 1 ≤ r) {t : ℝ} (ht : |t| ≤ 1) :
    Summable (fun k : ℕ => ErCoeff r k * t^(2*k+1)) := by
  have hb : ∀ k : ℕ, ‖ErCoeff r k * t^(2*k+1)‖ ≤ ErCoeff r k := by
    intro k
    have h1 : |t|^(2*k+1) ≤ 1 := (pow_le_one₀ (abs_nonneg t) ht : |t|^(2*k+1) ≤ 1)
    rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg (ErCoeff_nonneg_m hr k)]
    calc ErCoeff r k * |t|^(2*k+1) ≤ ErCoeff r k * 1 :=
          mul_le_mul_of_nonneg_left h1 (ErCoeff_nonneg_m hr k)
      _ = ErCoeff r k := by ring
  exact Summable.of_norm_bounded (summable_ErCoeff hr) hb

lemma neg_pow_odd (t : ℝ) (k : ℕ) : (-t)^(2*k+1) = -(t^(2*k+1)) := by
  rw [neg_pow]
  have h1 : (-1:ℝ)^(2*k+1) = -1 := by
    rw [show 2*k+1 = 2*k + 1 by ring, pow_succ, Even.neg_one_pow ⟨k, by ring⟩]
    ring
  rw [h1]
  ring

/-- `Er r` is odd. -/
theorem Er_neg_m {r : ℕ} (hr : 1 ≤ r) {t : ℝ} (ht : |t| ≤ 1) : Er r (-t) = -Er r t := by
  have hcongr : (fun k : ℕ => ErCoeff r k * (-t)^(2*k+1))
      = fun k : ℕ => -(ErCoeff r k * t^(2*k+1)) := by
    funext k
    rw [neg_pow_odd t k]
    ring
  rw [Er, hcongr, tsum_neg]
  rfl

/-- `Er r` is injective on `[0,1]` for `r ≥ 1`. -/
theorem Er_injOn_Icc {r : ℕ} (hr : 1 ≤ r) : Set.InjOn (Er r) (Set.Icc (0:ℝ) 1) := by
  intro s hs t ht h
  rcases lt_trichotomy s t with hlt | heq | hgt
  · exact absurd h (ne_of_lt (Er_strictMono_proof hr hs.1 hlt ht.2))
  · exact heq
  · exact absurd h.symm (ne_of_lt (Er_strictMono_proof hr ht.1 hgt hs.2))

/-- The `r = 1` instance of Gauss's evaluation `E_r(1) = 1`. -/
theorem Er_one_one : Er 1 1 = 1 := by
  have h := Er_one_Icc (t := 1) (Set.mem_Icc.mpr ⟨by norm_num, le_rfl⟩)
  have harc : Real.arcsin 1 = Real.pi / 2 := Real.arcsin_eq_pi_div_two.mpr le_rfl
  rw [harc] at h
  have hpi : (0:ℝ) < Real.pi := Real.pi_pos
  rw [h]
  field_simp

/-- `E_1` maps `[-1,1]` into `[-1,1]`. -/
theorem Er_one_maps (t : ℝ) (ht : t ∈ Set.Icc (-1:ℝ) 1) :
    Er 1 t ∈ Set.Icc (-1:ℝ) 1 :=
  Set.mem_Icc.mpr ⟨neg_le_of_abs_le (abs_Er_one_le_one ht), le_of_abs_le (abs_Er_one_le_one ht)⟩

/-! ## 1. The sign of `E_r` -/

/-- `E_r` is nonnegative on `[0,1]`: the series has nonnegative coefficients. -/
theorem Er_nonneg_Icc {r : ℕ} (hr : 1 ≤ r) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    0 ≤ Er r t := by
  have hsum : Summable (fun k : ℕ => ErCoeff r k * t ^ (2 * k + 1)) :=
    Er_mono_summable hr ht.1 ht.2
  rw [Er]
  exact tsum_nonneg fun k => mul_nonneg (ErCoeff_nonneg_m hr k) (pow_nonneg ht.1 _)

/-- `E_r` is at most `1` on `[0,1]`: monotonicity plus the published endpoint `E_r(1) = 1`. -/
theorem Er_le_one_Icc {r : ℕ} (hr : 1 ≤ r) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    Er r t ≤ 1 := by
  have h := Er_mono hr ht (Set.mem_Icc.mpr ⟨zero_le_one, le_rfl⟩) ht.2
  rwa [Er_one_proof r hr] at h

/-- `E_r` maps `[0,1]` into `[0,1]`. -/
theorem Er_mapsTo_Icc01 {r : ℕ} (hr : 1 ≤ r) :
    Set.MapsTo (Er r) (Set.Icc (0 : ℝ) 1) (Set.Icc (0 : ℝ) 1) :=
  fun _ ht => Set.mem_Icc.mpr ⟨Er_nonneg_Icc hr ht, Er_le_one_Icc hr ht⟩

/-- `E_r` is positive on `(0,1]`. -/
theorem Er_pos {r : ℕ} (hr : 1 ≤ r) {t : ℝ} (h0 : 0 < t) (h1 : t ≤ 1) : 0 < Er r t := by
  have h := Er_strictMono_proof (r := r) hr (le_refl (0 : ℝ)) h0 h1
  rwa [Er_zero_m r] at h

/-- `E_r` is negative on `(-∞,0)`, by oddness. -/
theorem Er_neg_of_neg {r : ℕ} (hr : 1 ≤ r) {t : ℝ} (h0 : -1 ≤ t) (h1 : t < 0) :
    Er r t < 0 := by
  have hodd : Er r t = -Er r (-t) := by
    have h := Er_neg r (-t)
    simpa using h
  have hp : 0 < Er r (-t) := Er_pos hr (by linarith) (by linarith)
  rw [hodd]
  linarith

/-! ## 2. The strict bound `|E_r t| < 1` -/

/-- `|E_r t| < 1` for `t ∈ (-1,1)`. -/
theorem abs_Er_lt_one {r : ℕ} (hr : 1 ≤ r) {t : ℝ} (ht : t ∈ Set.Ioo (-1 : ℝ) 1) :
    |Er r t| < 1 := by
  obtain ⟨ht1, ht2⟩ := ht
  rcases lt_trichotomy t 0 with h | h | h
  · have hodd : Er r t = -Er r (-t) := by
      have hh := Er_neg r (-t)
      simpa using hh
    have hp : 0 ≤ Er r (-t) := Er_nonneg_Icc hr ⟨by linarith, by linarith⟩
    have hlt : Er r (-t) < 1 := by
      have hh := Er_strictMono_proof (r := r) hr (show (0 : ℝ) ≤ -t by linarith)
        (show -t < 1 by linarith) (le_refl (1 : ℝ))
      rwa [Er_one_proof r hr] at hh
    rw [hodd, abs_neg, abs_of_nonneg hp]
    exact hlt
  · subst h
    rw [Er_zero_m r]
    norm_num
  · have h1 : Er r t < 1 := by
      have hh := Er_strictMono_proof (r := r) hr (le_of_lt h) ht2 (le_refl (1 : ℝ))
      rwa [Er_one_proof r hr] at hh
    have h0 : 0 ≤ Er r t := Er_nonneg_Icc hr ⟨le_of_lt h, le_of_lt ht2⟩
    rwa [abs_of_nonneg h0]

/-- `E_r(-1) = -1`. -/
theorem Er_neg_one {r : ℕ} (hr : 1 ≤ r) : Er r (-1) = -1 := by
  have hh := Er_neg r 1
  rw [Er_one_proof r hr] at hh
  simpa using hh

/-- `|E_r t| ≤ 1` on `[-1,1]`, with equality only at `t = ±1`. -/
theorem abs_Er_le_one {r : ℕ} (hr : 1 ≤ r) {t : ℝ} (ht : t ∈ Set.Icc (-1 : ℝ) 1) :
    |Er r t| ≤ 1 := by
  rcases lt_or_eq_of_le ht.1 with h1 | h1
  · rcases lt_or_eq_of_le ht.2 with h2 | h2
    · exact le_of_lt (abs_Er_lt_one hr ⟨h1, h2⟩)
    · rw [h2, Er_one_proof r hr]; norm_num
  · rw [← h1, Er_neg_one hr]; norm_num

/-- `E_r` maps `[-1,1]` into `[-1,1]`. -/
theorem Er_mapsTo_Icc {r : ℕ} (hr : 1 ≤ r) :
    Set.MapsTo (Er r) (Set.Icc (-1 : ℝ) 1) (Set.Icc (-1 : ℝ) 1) :=
  fun _ ht =>
    Set.mem_Icc.mpr ⟨neg_le_of_abs_le (abs_Er_le_one hr ht), le_of_abs_le (abs_Er_le_one hr ht)⟩

/-! ## 3. Strict monotonicity on the whole interval `[-1,1]` -/

/-- `E_r` is strictly increasing on `[-1,1]`.  The published node `Er_strictMono` gives this on
`[0,1]`; oddness of `E_r` transports it to all of `[-1,1]`. -/
theorem Er_strictMonoOn {r : ℕ} (hr : 1 ≤ r) :
    StrictMonoOn (Er r) (Set.Icc (-1 : ℝ) 1) := by
  intro s hs t ht hst
  obtain ⟨hs1, hs2⟩ := hs
  obtain ⟨ht1, ht2⟩ := ht
  rcases lt_trichotomy s 0 with hs0 | hs0 | hs0
  · -- `s < 0`
    rcases lt_trichotomy t 0 with ht0 | ht0 | ht0
    · -- both negative: reduce to `0 < -t < -s ≤ 1` by oddness
      have hodd_s : Er r s = -Er r (-s) := by
        have hh := Er_neg r (-s)
        simpa using hh
      have hodd_t : Er r t = -Er r (-t) := by
        have hh := Er_neg r (-t)
        simpa using hh
      have hmono : Er r (-t) < Er r (-s) :=
        Er_strictMono_proof (r := r) hr (show (0 : ℝ) ≤ -t by linarith)
          (show -t < -s by linarith) (show -s ≤ 1 by linarith)
      rw [hodd_s, hodd_t]
      linarith
    · -- `t = 0`
      subst ht0
      rw [Er_zero_m r]
      exact Er_neg_of_neg hr hs1 hs0
    · -- `s < 0 < t`
      have hneg : Er r s < 0 := Er_neg_of_neg hr hs1 hs0
      have hpos : 0 ≤ Er r t := Er_nonneg_Icc hr ⟨le_of_lt ht0, ht2⟩
      linarith
  · -- `s = 0 < t`
    subst hs0
    rw [Er_zero_m r]
    exact Er_pos hr hst ht2
  · -- `0 < s < t`
    exact Er_strictMono_proof (r := r) hr (le_of_lt hs0) hst ht2

/-- `E_r` is injective on `[-1,1]`. -/
theorem Er_injOn_Icc' {r : ℕ} (hr : 1 ≤ r) :
    Set.InjOn (Er r) (Set.Icc (-1 : ℝ) 1) :=
  (Er_strictMonoOn hr).injOn

/-! ## 4. Surjectivity: `E_r '' [-1,1] = [-1,1]` -/

/-- `E_r` maps `[0,1]` onto `[0,1]` (intermediate value theorem plus the endpoints). -/
theorem Er_surjOn_Icc01 {r : ℕ} (hr : 1 ≤ r) :
    Set.Icc (0 : ℝ) 1 ⊆ (Er r) '' Set.Icc (0 : ℝ) 1 := by
  have hcont : ContinuousOn (fun t => Er r t) (Set.Icc (0 : ℝ) 1) :=
    (continuousOn_Er hr).mono (Set.Icc_subset_Icc (by norm_num) le_rfl)
  have h := IsPreconnected.intermediate_value (isPreconnected_Icc (a := (0 : ℝ)) (b := 1))
    (Set.left_mem_Icc.mpr zero_le_one) (Set.right_mem_Icc.mpr zero_le_one) hcont
  rwa [Er_zero_m r, Er_one_proof r hr] at h

/-- `E_r` maps `[-1,1]` onto `[-1,1]`. -/
theorem Er_surjOn {r : ℕ} (hr : 1 ≤ r) :
    Set.SurjOn (Er r) (Set.Icc (-1 : ℝ) 1) (Set.Icc (-1 : ℝ) 1) := by
  intro y hy
  obtain ⟨hy1, hy2⟩ := hy
  have h01 := Er_surjOn_Icc01 hr
  rcases le_or_gt 0 y with h | h
  · obtain ⟨x, hx, hxy⟩ := h01 (Set.mem_Icc.mpr ⟨h, hy2⟩)
    exact ⟨x, Set.mem_Icc.mpr ⟨le_trans (by norm_num) hx.1, hx.2⟩, hxy⟩
  · obtain ⟨x, hx, hxy⟩ :=
      h01 (show -y ∈ Set.Icc (0 : ℝ) 1 from Set.mem_Icc.mpr ⟨by linarith, by linarith⟩)
    obtain ⟨hx1, hx2⟩ := hx
    refine ⟨-x, Set.mem_Icc.mpr ⟨by linarith, by linarith⟩, ?_⟩
    rw [Er_neg r x, hxy]
    ring

/-- `E_r '' [-1,1] = [-1,1]`. -/
theorem Er_image_Icc {r : ℕ} (hr : 1 ≤ r) :
    (Er r) '' Set.Icc (-1 : ℝ) 1 = Set.Icc (-1 : ℝ) 1 :=
  Set.SurjOn.image_eq_of_mapsTo (Er_surjOn hr) (Er_mapsTo_Icc hr)

/-- `E_r` is a bijection of `[-1,1]` onto itself. -/
theorem Er_bijOn {r : ℕ} (hr : 1 ≤ r) :
    Set.BijOn (Er r) (Set.Icc (-1 : ℝ) 1) (Set.Icc (-1 : ℝ) 1) :=
  ⟨Er_mapsTo_Icc hr, Er_injOn_Icc' hr, Er_surjOn hr⟩

/-! ## 5. The inverse `E_r⁻¹`: characterisation on `[-1,1]`

From here on nothing unfolds `Function.invFunOn`: the identities below, plus `ErInv_mem`, are
the complete interface used by the rest of Section 3. -/

/-- `E_r⁻¹` is a right inverse of `E_r` on `[-1,1]`. -/
theorem Er_ErInv {r : ℕ} (hr : 1 ≤ r) {y : ℝ} (hy : y ∈ Set.Icc (-1 : ℝ) 1) :
    Er r (ErInv r y) = y :=
  (Er_surjOn hr).rightInvOn_invFunOn hy

/-- `E_r⁻¹` is a left inverse of `E_r` on `[-1,1]`. -/
theorem ErInv_Er {r : ℕ} (hr : 1 ≤ r) {x : ℝ} (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    ErInv r (Er r x) = x :=
  (Er_injOn_Icc' hr).leftInvOn_invFunOn hx

/-- `E_r⁻¹` maps `[-1,1]` into `[-1,1]`. -/
theorem ErInv_mem {r : ℕ} (hr : 1 ≤ r) {y : ℝ} (hy : y ∈ Set.Icc (-1 : ℝ) 1) :
    ErInv r y ∈ Set.Icc (-1 : ℝ) 1 :=
  (Er_surjOn hr).mapsTo_invFunOn hy

/-- `E_r⁻¹` is strictly increasing on `[-1,1]`. -/
theorem ErInv_strictMonoOn {r : ℕ} (hr : 1 ≤ r) :
    StrictMonoOn (ErInv r) (Set.Icc (-1 : ℝ) 1) := by
  intro y₁ hy₁ y₂ hy₂ hlt
  have h1 := ErInv_mem hr hy₁
  have h2 := ErInv_mem hr hy₂
  have e1 := Er_ErInv hr hy₁
  have e2 := Er_ErInv hr hy₂
  rcases lt_trichotomy (ErInv r y₁) (ErInv r y₂) with h | h | h
  · exact h
  · rw [h] at e1
    linarith
  · have := (Er_strictMonoOn hr) h2 h1 h
    rw [e1, e2] at this
    linarith

/-- `E_r⁻¹` is a bijection of `[-1,1]` onto itself. -/
theorem ErInv_bijOn {r : ℕ} (hr : 1 ≤ r) :
    Set.BijOn (ErInv r) (Set.Icc (-1 : ℝ) 1) (Set.Icc (-1 : ℝ) 1) :=
  ⟨fun _ hy => ErInv_mem hr hy, (ErInv_strictMonoOn hr).injOn, by
    intro x hx
    exact ⟨Er r x, Er_mapsTo_Icc hr hx, ErInv_Er hr hx⟩⟩

/-- The inverse of `E_r` at the three special points of the paper. -/
theorem ErInv_zero {r : ℕ} (hr : 1 ≤ r) : ErInv r 0 = 0 := by
  have h := ErInv_Er (r := r) hr (x := 0) (Set.mem_Icc.mpr ⟨by norm_num, by norm_num⟩)
  rwa [Er_zero_m r] at h

theorem ErInv_one {r : ℕ} (hr : 1 ≤ r) : ErInv r 1 = 1 := by
  have h := ErInv_Er (r := r) hr (x := 1) (Set.mem_Icc.mpr ⟨by norm_num, by norm_num⟩)
  rwa [Er_one_proof r hr] at h

theorem ErInv_neg_one {r : ℕ} (hr : 1 ≤ r) : ErInv r (-1) = -1 := by
  have h := ErInv_Er (r := r) hr (x := -1) (Set.mem_Icc.mpr ⟨by norm_num, by norm_num⟩)
  rwa [Er_neg_one hr] at h

/-- `E_r⁻¹` is odd, like `E_r`. -/
theorem ErInv_neg {r : ℕ} (hr : 1 ≤ r) {y : ℝ} (hy : y ∈ Set.Icc (-1 : ℝ) 1) :
    ErInv r (-y) = -ErInv r y := by
  have hy' : -y ∈ Set.Icc (-1 : ℝ) 1 := Set.mem_Icc.mpr ⟨by linarith [hy.2], by linarith [hy.1]⟩
  have hy₂ : -ErInv r y ∈ Set.Icc (-1 : ℝ) 1 :=
    Set.mem_Icc.mpr ⟨by linarith [(ErInv_mem hr hy).2], by linarith [(ErInv_mem hr hy).1]⟩
  refine Er_injOn_Icc' hr (ErInv_mem hr hy') hy₂ ?_
  rw [Er_ErInv hr hy', Er_neg r, Er_ErInv hr hy]

end Grothendieck

/-! ## Axiom check -/

open Grothendieck in
theorem solution (r : ℕ) (hr : 1 ≤ r) :
    (∀ y ∈ Set.Icc (-1 : ℝ) 1, Er r (ErInv r y) = y) ∧
      (∀ x ∈ Set.Icc (-1 : ℝ) 1, ErInv r (Er r x) = x) :=
  ⟨fun y hy => Grothendieck.Er_ErInv hr hy, fun x hx => Grothendieck.ErInv_Er hr hx⟩
