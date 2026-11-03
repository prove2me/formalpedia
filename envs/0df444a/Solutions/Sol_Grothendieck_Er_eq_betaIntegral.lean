-- Prove2me | solution 1 for Grothendieck.Er_eq_betaIntegral
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-02T14:23:52.448541+00:00
-- url     : https://prove2.me/submissions/17abe278-9608-4468-bf3e-b70bb21c0c91

import Mathlib
import Definitions.Def_Grothendieck_Series
import Definitions.Def_Grothendieck_Gaussian

set_option autoImplicit false

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
theorem Er_eq_betaIntegral_proof (r : ℕ) (hr : 1 ≤ r) {t : ℝ} (ht : |t| < 1) :
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

#print axioms Grothendieck.risingFact_eq_Gamma_div
#print axioms Grothendieck.betaIntegral_real
#print axioms Grothendieck.hasSum_rpow_neg_of_abs_lt_one
#print axioms Grothendieck.integral_rpow_weight
#print axioms Grothendieck.ErCoeff_eq_Gamma
#print axioms Grothendieck.Er_eq_betaIntegral_proof

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
  rw [hbeta r n hr u v hu hv hne, Er_eq_betaIntegral_proof r hr hne]

#print axioms Grothendieck.matrix_grothendieck_identity_of_beta

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

#print axioms Grothendieck.risingFact_half_le_factorial
#print axioms Grothendieck.ErCoeff_le_Cr
#print axioms Grothendieck.summable_ErCoeff_mul_pow



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
        exact (Er_eq_betaIntegral_proof r hr habs).symm
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
        exact (Er_eq_betaIntegral_proof r hr habs).symm
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

#print axioms Grothendieck.integral_rpow_neg_half_exp
#print axioms Grothendieck.intervalIntegrable_beta_weight
#print axioms Grothendieck.integral_weight_one
#print axioms Grothendieck.tendsto_integral_weight
#print axioms Grothendieck.Er_one

end Grothendieck

open Grothendieck in
theorem solution (r : ℕ) (hr : 1 ≤ r) {t : ℝ} (ht : |t| < 1) :
    Er r t = Real.Gamma (((r : ℝ) + 1) / 2)
        / (Real.sqrt Real.pi * Real.Gamma ((r : ℝ) / 2)) *
      (t * ∫ u in (0 : ℝ)..1, u ^ (-(1/2) : ℝ) * (1 - u) ^ (((r : ℝ) - 1) / 2) *
        (1 - t ^ 2 * u) ^ (-(1/2) : ℝ)) :=
  Er_eq_betaIntegral_proof r hr ht
