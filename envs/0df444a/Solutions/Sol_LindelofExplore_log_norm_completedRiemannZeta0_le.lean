-- Prove2me | solution 1 for LindelofExplore.log_norm_completedRiemannZeta0_le
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-11-01T16:39:42.058841+00:00
-- url     : https://prove2.me/submissions/efa46a45-0320-4e12-9719-fc0d98de008d

import Mathlib

/-!
# Growth of the completed zeta function on Re s ≥ 2

Submission-shaped version of the Lindelöf exploration growth bound.
It contains,
verbatim, the three lemmas verified in the modular files
(`GammaNorm.lean`, `ZetaBound.lean`, `RealGammaBound.lean`), followed by
the assembly: for `2 ≤ Re s`, `log ‖Λ₀(s)‖ ≤ 3 + (Re s) * log (Re s)`,
where `Λ₀ = completedRiemannZeta₀`. By symmetry `Λ₀(1 − s) = Λ₀(s)` the
same bound holds on `Re s ≤ −1` with `1 − Re s` in place of `Re s`.
The strip `−1 < Re s < 2` is NOT covered here — bounding `ζ` there is
the remaining blocker (see STATUS.md). The content was verified locally
in LambdaGrowth.lean (targeted imports, same proofs, main theorem named
log_norm_completedRiemannZeta₀_le); this submission-shaped copy (import
Mathlib, theorem renamed to solution) was NOT itself compiled. Nothing
has been submitted to Prove2Me; publication needs a new platform problem
created first, then a per-item submission tap.
-/

open Complex MeasureTheory Set Filter Real
open scoped Topology

/-!
# Complex Gamma bounded by real Gamma

For `0 < z.re`, `‖Γ(z)‖ ≤ Γ(z.re)`, by taking norms inside Euler's
integral. This is the first step of a crude growth bound for the
completed zeta function on the half-plane `Re s ≥ 2`.
-/


/-- The complex Gamma function is bounded by the real Gamma function
of its real part. -/
theorem norm_Gamma_le_Gamma_re {z : ℂ} (hz : 0 < z.re) :
    ‖Gamma z‖ ≤ Real.Gamma z.re := by
  rw [Complex.Gamma_eq_integral hz, Complex.GammaIntegral,
    Real.Gamma_eq_integral hz]
  have hnorm : ‖∫ x in Ioi (0 : ℝ), ↑(Real.exp (-x)) * (↑x : ℂ) ^ (z - 1)‖
      ≤ ∫ x in Ioi (0 : ℝ), ‖↑(Real.exp (-x)) * (↑x : ℂ) ^ (z - 1)‖ :=
    MeasureTheory.norm_integral_le_integral_norm _
  refine hnorm.trans_eq ?_
  refine setIntegral_congr_fun measurableSet_Ioi fun x hx ↦ ?_
  have hx0 : (0 : ℝ) < x := mem_Ioi.mp hx
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx0]
  simp only [Complex.ofReal_exp, Complex.norm_exp, Complex.ofReal_re,
    Complex.sub_re, Complex.one_re]

/-!
# Zeta bounded by ζ(2) on Re s ≥ 2

For `2 ≤ Re s`, `‖ζ(s)‖ ≤ π²/6`, by the Dirichlet series: termwise
`‖1/(n+1)^s‖ = (n+1)^(-Re s) ≤ (n+1)^(-2)`, and `∑ (n+1)^(-2) = ζ(2)`.
-/


/-- The Riemann zeta function is bounded by `π²/6` on `Re s ≥ 2`. -/
theorem norm_riemannZeta_le_pi_sq_div_six {s : ℂ} (hs : 2 ≤ s.re) :
    ‖riemannZeta s‖ ≤ Real.pi ^ 2 / 6 := by
  have hs1 : 1 < s.re := by linarith
  rw [zeta_eq_tsum_one_div_nat_add_one_cpow hs1]
  have hnorm : ∀ n : ℕ, ‖(1 : ℂ) / ((n : ℂ) + 1) ^ s‖
      = (((n : ℝ) + 1)) ^ (-(s.re)) := by
    intro n
    have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hcast : ((n : ℂ) + 1) = (((n : ℝ) + 1 : ℝ) : ℂ) := by simp
    rw [norm_div, norm_one, hcast, Complex.norm_cpow_eq_rpow_re_of_pos hpos,
      Real.rpow_neg (le_of_lt hpos), one_div]
  have hle : ∀ n : ℕ, ‖(1 : ℂ) / ((n : ℂ) + 1) ^ s‖
      ≤ (((n + 1 : ℕ) : ℝ)) ^ (-(2 : ℝ)) := by
    intro n
    rw [hnorm n]
    have hcast : ((n : ℝ) + 1) = ((n + 1 : ℕ) : ℝ) := by push_cast; ring
    rw [hcast]
    apply Real.rpow_le_rpow_of_exponent_le
    · have h : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith
    · linarith
  -- The comparison series `∑ (n+1)^(-2)` is summable and equals `π²/6`.
  have hzeta2 : HasSum (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2) (Real.pi ^ 2 / 6) :=
    hasSum_zeta_two
  have hsum2 : Summable (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2) := hzeta2.summable
  have hshift_sum : Summable (fun n : ℕ => (((n + 1 : ℕ) : ℝ)) ^ (-(2 : ℝ))) := by
    have h : Summable (fun n : ℕ => (1 : ℝ) / ((n + 1 : ℕ) : ℝ) ^ 2) :=
      (summable_nat_add_iff 1).mpr hsum2
    refine h.congr fun n ↦ ?_
    rw [Real.rpow_neg (by positivity : (0 : ℝ) ≤ ((n + 1 : ℕ) : ℝ))]
    simp [div_eq_mul_inv]
  have hshift_val : ∑' n : ℕ, (((n + 1 : ℕ) : ℝ)) ^ (-(2 : ℝ))
      = Real.pi ^ 2 / 6 := by
    have htsum := hsum2.tsum_eq_zero_add
    rw [hzeta2.tsum_eq] at htsum
    simp at htsum
    rw [htsum]
    refine tsum_congr fun n ↦ ?_
    rw [Real.rpow_neg (by positivity : (0 : ℝ) ≤ ((n + 1 : ℕ) : ℝ))]
    push_cast
    simp [one_div]
  have hsumm : Summable (fun n : ℕ => ‖(1 : ℂ) / ((n : ℂ) + 1) ^ s‖) :=
    Summable.of_nonneg_of_le (fun n ↦ norm_nonneg _) hle hshift_sum
  calc ‖∑' n : ℕ, (1 : ℂ) / ((n : ℂ) + 1) ^ s‖
      ≤ ∑' n : ℕ, ‖(1 : ℂ) / ((n : ℂ) + 1) ^ s‖ :=
        norm_tsum_le_tsum_norm hsumm
    _ ≤ ∑' n : ℕ, (((n + 1 : ℕ) : ℝ)) ^ (-(2 : ℝ)) :=
        Summable.tsum_le_tsum hle hsumm hshift_sum
    _ = Real.pi ^ 2 / 6 := hshift_val

/-!
# A crude upper bound for the real Gamma function

For `1 ≤ x`, `Γ(x) ≤ (2x)^x`, hence `log Γ(x) ≤ x * log (2x)`.
The proof uses the one-variable inequality `u^a * exp(-u) ≤ a^a * exp(-a)`
(from `log y ≤ y − 1`), applied with `a = x − 1`, `u = t/2`: the Gamma
integrand `exp(-t) * t^(x-1)` is at most `(2x)^(x-1) * exp(-t/2)`, whose
integral over `(0, ∞)` is `(2x)^(x-1) * 2 = (2x)^x / x ≤ (2x)^x`.
-/


/-- The function `u ↦ u^a * exp(-u)` is maximized at `u = a`. -/
theorem rpow_mul_exp_neg_le {a u : ℝ} (ha : 0 ≤ a) (hu : 0 < u) :
    u ^ a * Real.exp (-u) ≤ a ^ a * Real.exp (-a) := by
  rcases ha.eq_or_lt with rfl | ha0
  · rw [Real.rpow_zero, Real.rpow_zero, neg_zero, Real.exp_zero, mul_one, one_mul]
    exact Real.exp_le_one_iff.mpr (by linarith)
  · set y := u / a with hy_def
    have hy : 0 < y := div_pos hu ha0
    have hu_eq : u = a * y := by rw [hy_def]; field_simp
    have hlog : Real.log y ≤ y - 1 := Real.log_le_sub_one_of_pos hy
    have hkey : Real.log y * a + -(a * y) ≤ -a := by
      have h : a * (Real.log y - y + 1) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos ha0.le (by linarith)
      linarith
    calc u ^ a * Real.exp (-u)
        = a ^ a * Real.exp (Real.log y * a + -(a * y)) := by
          rw [hu_eq, Real.mul_rpow ha0.le hy.le, Real.rpow_def_of_pos hy, mul_assoc,
            ← Real.exp_add]
      _ ≤ a ^ a * Real.exp (-a) :=
          mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hkey)
            (Real.rpow_nonneg ha0.le a)


/-- Crude upper bound for the real Gamma function. -/
theorem Real_gamma_le {x : ℝ} (hx : 1 ≤ x) :
    Real.Gamma x ≤ (2 * x) ^ x := by
  have hx0 : 0 < x := by linarith
  have hx1 : 0 ≤ x - 1 := by linarith
  rw [Real.Gamma_eq_integral hx0]
  have hbound : ∀ t ∈ Set.Ioi (0 : ℝ), Real.exp (-t) * t ^ (x - 1)
      ≤ (2 * x) ^ (x - 1) * Real.exp (-(t / 2)) := by
    intro t ht
    have ht0 : 0 < t := ht
    have h1 : t ^ (x - 1) * Real.exp (-(t / 2))
        ≤ (2 * (x - 1)) ^ (x - 1) * Real.exp (-(x - 1)) := by
      have h2 : (t / 2) ^ (x - 1) * Real.exp (-(t / 2))
          ≤ (x - 1) ^ (x - 1) * Real.exp (-(x - 1)) :=
        rpow_mul_exp_neg_le hx1 (by linarith)
      have h3 : t ^ (x - 1) = (2 : ℝ) ^ (x - 1) * (t / 2) ^ (x - 1) := by
        have h : (2 : ℝ) * (t / 2) = t := by ring
        conv_lhs => rw [← h]
        rw [Real.mul_rpow (by norm_num) (by linarith : (0 : ℝ) ≤ t / 2)]
      rw [h3, mul_assoc]
      calc (2 : ℝ) ^ (x - 1) * ((t / 2) ^ (x - 1) * Real.exp (-(t / 2)))
          ≤ (2 : ℝ) ^ (x - 1) * ((x - 1) ^ (x - 1) * Real.exp (-(x - 1))) :=
            mul_le_mul_of_nonneg_left h2 (Real.rpow_nonneg (by norm_num) _)
        _ = (2 * (x - 1)) ^ (x - 1) * Real.exp (-(x - 1)) := by
            rw [Real.mul_rpow (by norm_num) hx1]; ring
    have h4 : (2 * (x - 1)) ^ (x - 1) * Real.exp (-(x - 1))
        ≤ (2 * x) ^ (x - 1) := by
      have hle : (2 * (x - 1)) ^ (x - 1) ≤ (2 * x) ^ (x - 1) :=
        Real.rpow_le_rpow (by linarith) (by linarith) hx1
      have hexp : Real.exp (-(x - 1)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
      calc (2 * (x - 1)) ^ (x - 1) * Real.exp (-(x - 1))
          ≤ (2 * (x - 1)) ^ (x - 1) * 1 :=
            mul_le_mul_of_nonneg_left hexp (Real.rpow_nonneg (by linarith) _)
        _ ≤ (2 * x) ^ (x - 1) := by rw [mul_one]; exact hle
    have h5 : Real.exp (-t) * t ^ (x - 1)
        = (t ^ (x - 1) * Real.exp (-(t / 2))) * Real.exp (-(t / 2)) := by
      have e : Real.exp (-(t / 2)) * Real.exp (-(t / 2)) = Real.exp (-t) := by
        rw [← Real.exp_add]; congr 1; ring
      calc Real.exp (-t) * t ^ (x - 1) = t ^ (x - 1) * Real.exp (-t) := by ring
        _ = t ^ (x - 1) * (Real.exp (-(t / 2)) * Real.exp (-(t / 2))) := by rw [e]
        _ = (t ^ (x - 1) * Real.exp (-(t / 2))) * Real.exp (-(t / 2)) := by ring
    calc Real.exp (-t) * t ^ (x - 1)
        = (t ^ (x - 1) * Real.exp (-(t / 2))) * Real.exp (-(t / 2)) := h5
      _ ≤ (2 * x) ^ (x - 1) * Real.exp (-(t / 2)) :=
          mul_le_mul_of_nonneg_right (h1.trans h4) (Real.exp_nonneg _)
  have hint1 : IntegrableOn (fun t : ℝ => Real.exp (-t) * t ^ (x - 1))
      (Set.Ioi 0) := Real.GammaIntegral_convergent hx0
  have hint2 : IntegrableOn
      (fun t : ℝ => (2 * x) ^ (x - 1) * Real.exp (-(t / 2))) (Set.Ioi 0) := by
    have h : IntegrableOn (fun t : ℝ => Real.exp (-(1 / 2 : ℝ) * t)) (Set.Ioi 0) :=
      exp_neg_integrableOn_Ioi 0 (show (0 : ℝ) < 1 / 2 by norm_num)
    have hconv : (fun t : ℝ => Real.exp (-(1 / 2 : ℝ) * t))
        = (fun t : ℝ => Real.exp (-(t / 2))) := by
      funext t; congr 1; ring
    rw [hconv] at h
    exact h.const_mul _
  have hint : ∫ t in Set.Ioi (0 : ℝ), Real.exp (-t) * t ^ (x - 1)
      ≤ ∫ t in Set.Ioi (0 : ℝ), (2 * x) ^ (x - 1) * Real.exp (-(t / 2)) :=
    MeasureTheory.setIntegral_mono_on hint1 hint2 measurableSet_Ioi hbound
  have hexp2 : ∫ t in Set.Ioi (0 : ℝ), Real.exp (-(t / 2)) = 2 := by
    have h := MeasureTheory.integral_comp_mul_left_Ioi'
      (fun u : ℝ => Real.exp (-u)) (0 : ℝ) (show (0 : ℝ) < 1 / 2 by norm_num)
    rw [mul_zero, integral_exp_neg_Ioi_zero] at h
    have hconv : (fun u : ℝ => Real.exp (-((1 / 2) * u)))
        = (fun u : ℝ => Real.exp (-(u / 2))) := by
      funext u; congr 1; ring
    rw [hconv, smul_eq_mul] at h
    linarith
  have hval : ∫ t in Set.Ioi (0 : ℝ), (2 * x) ^ (x - 1) * Real.exp (-(t / 2))
      = (2 * x) ^ (x - 1) * 2 := by
    rw [MeasureTheory.integral_const_mul, hexp2]
  calc ∫ t in Set.Ioi (0 : ℝ), Real.exp (-t) * t ^ (x - 1)
      ≤ (2 * x) ^ (x - 1) * 2 := hint.trans_eq hval
    _ ≤ (2 * x) ^ x := by
        have hpow : (2 * x) ^ x = (2 * x) ^ (x - 1) * (2 * x) := by
          rw [← Real.rpow_add_one (by positivity : (2 : ℝ) * x ≠ 0)]
          congr 1
          ring
        rw [hpow]
        have hnn : 0 ≤ (2 * x) ^ (x - 1) := Real.rpow_nonneg (by linarith) _
        calc (2 * x) ^ (x - 1) * 2 ≤ (2 * x) ^ (x - 1) * (2 * x) :=
              mul_le_mul_of_nonneg_left (by linarith) hnn

/-- Growth bound for the completed zeta function on `Re s ≥ 2`. -/
theorem solution {s : ℂ} (hs : 2 ≤ s.re) :
    Real.log ‖completedRiemannZeta₀ s‖ ≤ 3 + s.re * Real.log s.re := by
  have hs1 : 1 < s.re := by linarith
  have hLam : completedRiemannZeta s
      = (Real.pi : ℂ) ^ (-s / 2) * Complex.Gamma (s / 2) * riemannZeta s := by
    rw [completedZeta_eq_tsum_of_one_lt_re hs1,
      zeta_eq_tsum_one_div_nat_cpow hs1]
  have hGpos : 0 < Real.Gamma (s.re / 2) :=
    Real.Gamma_pos_of_pos (by linarith)
  have hpi : ‖(Real.pi : ℂ) ^ (-s / 2)‖ ≤ 1 := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
    apply Real.rpow_le_one_of_one_le_of_nonpos (by linarith [Real.two_le_pi])
    have hre : (-s / 2 : ℂ).re = -s.re / 2 := by
      simp [Complex.neg_re]
    rw [hre]
    linarith
  have hGam : ‖Complex.Gamma (s / 2)‖ ≤ Real.Gamma (s.re / 2) := by
    have hdiv : (s / 2 : ℂ).re = s.re / 2 := by simp
    rw [← hdiv]
    exact norm_Gamma_le_Gamma_re (by rw [hdiv]; linarith)
  have hZet : ‖riemannZeta s‖ ≤ Real.pi ^ 2 / 6 :=
    norm_riemannZeta_le_pi_sq_div_six hs
  have hLamNorm : ‖completedRiemannZeta s‖
      ≤ (Real.pi ^ 2 / 6) * Real.Gamma (s.re / 2) := by
    rw [hLam]
    calc ‖(Real.pi : ℂ) ^ (-s / 2) * Complex.Gamma (s / 2) * riemannZeta s‖
        ≤ ‖(Real.pi : ℂ) ^ (-s / 2)‖ * ‖Complex.Gamma (s / 2)‖ * ‖riemannZeta s‖ := by
          rw [norm_mul, norm_mul]
      _ ≤ 1 * Real.Gamma (s.re / 2) * (Real.pi ^ 2 / 6) := by
          apply mul_le_mul _ hZet (norm_nonneg _) _
          · exact mul_le_mul hpi hGam (norm_nonneg _) (by norm_num)
          · rw [one_mul]; exact hGpos.le
      _ = (Real.pi ^ 2 / 6) * Real.Gamma (s.re / 2) := by ring
  have hLam0 : completedRiemannZeta₀ s
      = completedRiemannZeta s + 1 / s + 1 / (1 - s) := by
    have h := completedRiemannZeta_eq s
    rw [h]; abel
  have h1s : ‖(1 : ℂ) / s‖ ≤ 1 / 2 := by
    rw [norm_div, norm_one]
    have hs_norm : (2 : ℝ) ≤ ‖s‖ := by
      calc (2 : ℝ) ≤ |s.re| := by
            rw [abs_of_nonneg (by linarith)]; exact hs
        _ ≤ ‖s‖ := Complex.abs_re_le_norm s
    rw [one_div_le_one_div (by linarith : (0 : ℝ) < ‖s‖) (by norm_num : (0 : ℝ) < 2)]
    exact hs_norm
  have h1ms : ‖(1 : ℂ) / (1 - s)‖ ≤ 1 := by
    rw [norm_div, norm_one]
    have hnorm : (1 : ℝ) ≤ ‖1 - s‖ := by
      calc (1 : ℝ) ≤ |1 - s.re| := by
            rw [abs_of_neg (by linarith : (1 : ℝ) - s.re < 0)]; linarith
        _ ≤ ‖1 - s‖ := by
            have h := Complex.abs_re_le_norm (1 - s)
            simpa [Complex.sub_re] using h
    calc (1 : ℝ) / ‖1 - s‖ ≤ 1 / 1 := by
          rw [one_div_le_one_div (by linarith : (0 : ℝ) < ‖1 - s‖)
            (by norm_num : (0 : ℝ) < 1)]
          exact hnorm
      _ = 1 := by norm_num
  have htri : ‖completedRiemannZeta s + 1 / s + 1 / (1 - s)‖
      ≤ ‖completedRiemannZeta s‖ + ‖1 / s‖ + ‖1 / (1 - s)‖ := by
    calc ‖completedRiemannZeta s + 1 / s + 1 / (1 - s)‖
        ≤ ‖completedRiemannZeta s + 1 / s‖ + ‖1 / (1 - s)‖ := norm_add_le _ _
      _ ≤ ‖completedRiemannZeta s‖ + ‖1 / s‖ + ‖1 / (1 - s)‖ := by
          have h := norm_add_le (completedRiemannZeta s) (1 / s)
          linarith
  have hNorm0 : ‖completedRiemannZeta₀ s‖
      ≤ (Real.pi ^ 2 / 6) * Real.Gamma (s.re / 2) + 3 / 2 := by
    rw [hLam0]
    calc ‖completedRiemannZeta s + 1 / s + 1 / (1 - s)‖
        ≤ ‖completedRiemannZeta s‖ + ‖1 / s‖ + ‖1 / (1 - s)‖ := htri
      _ ≤ (Real.pi ^ 2 / 6) * Real.Gamma (s.re / 2) + 1 / 2 + 1 :=
          add_le_add (add_le_add hLamNorm h1s) h1ms
      _ = (Real.pi ^ 2 / 6) * Real.Gamma (s.re / 2) + 3 / 2 := by ring
  have hG : Real.Gamma (s.re / 2) ≤ s.re ^ (s.re / 2) := by
    have h := Real_gamma_le (show (1 : ℝ) ≤ s.re / 2 by linarith)
    rwa [show (2 : ℝ) * (s.re / 2) = s.re by ring] at h
  have hA : (2 : ℝ) ≤ s.re ^ (s.re / 2) := by
    calc (2 : ℝ) = (2 : ℝ) ^ (1 : ℝ) := by simp
      _ ≤ (2 : ℝ) ^ (s.re / 2) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      _ ≤ s.re ^ (s.re / 2) :=
          Real.rpow_le_rpow (by norm_num) hs (by linarith)
  have hA0 : (0 : ℝ) ≤ s.re ^ (s.re / 2) := by linarith
  have hpi2 : Real.pi ^ 2 ≤ 16 := by
    nlinarith [Real.pi_le_four, Real.pi_nonneg]
  have htot : ‖completedRiemannZeta₀ s‖ ≤ 5 * s.re ^ (s.re / 2) := by
    have hG' : (Real.pi ^ 2 / 6) * Real.Gamma (s.re / 2)
        ≤ (Real.pi ^ 2 / 6) * s.re ^ (s.re / 2) :=
      mul_le_mul_of_nonneg_left hG (by positivity)
    have h1 : (Real.pi ^ 2 / 6) * s.re ^ (s.re / 2)
        ≤ (8 / 3) * s.re ^ (s.re / 2) :=
      mul_le_mul_of_nonneg_right (by linarith) hA0
    have h2 : (3 : ℝ) / 2 ≤ (3 / 4) * s.re ^ (s.re / 2) := by linarith
    linarith [hNorm0, hG', h1, h2]
  have hlog5 : Real.log 5 ≤ 3 := by
    have h2 : (2 : ℝ) ≤ Real.exp 1 := by
      have h := Real.add_one_le_exp (1 : ℝ); linarith
    have hlog2 : Real.log 2 ≤ 1 := by
      calc Real.log 2 ≤ Real.log (Real.exp 1) := Real.log_le_log (by norm_num) h2
        _ = 1 := Real.log_exp 1
    calc Real.log 5 ≤ Real.log 8 := Real.log_le_log (by norm_num) (by norm_num)
      _ = 3 * Real.log 2 := by
          rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; norm_num
      _ ≤ 3 := by linarith
  have hle : (s.re / 2) * Real.log s.re ≤ s.re * Real.log s.re :=
    mul_le_mul_of_nonneg_right (by linarith) (Real.log_nonneg (by linarith))
  rcases eq_or_lt_of_le (norm_nonneg (completedRiemannZeta₀ s)) with h0 | hpos
  · rw [← h0]
    simp only [Real.log_zero]
    have hnn : 0 ≤ s.re * Real.log s.re :=
      mul_nonneg (by linarith) (Real.log_nonneg (by linarith))
    linarith
  · calc Real.log ‖completedRiemannZeta₀ s‖ ≤ Real.log (5 * s.re ^ (s.re / 2)) :=
        Real.log_le_log hpos htot
      _ = Real.log 5 + (s.re / 2) * Real.log s.re := by
          rw [Real.log_mul (by norm_num)
            (ne_of_gt (by linarith : (0 : ℝ) < s.re ^ (s.re / 2))),
            Real.log_rpow (by linarith : (0 : ℝ) < s.re)]
      _ ≤ 3 + s.re * Real.log s.re := by linarith

