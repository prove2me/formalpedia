-- Prove2me | solution 1 for Grothendieck.integral_add_mul_sq_rpow_neg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:09:38.862008+00:00
-- url     : https://prove2.me/submissions/065ca2bf-685d-4042-b1af-8c0c47ff3518

import Mathlib

set_option autoImplicit false

open MeasureTheory
open scoped BigOperators Real Topology

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

set_option autoImplicit false

open MeasureTheory intervalIntegral
open scoped BigOperators Real Topology

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
theorem integral_one_add_sq_rpow_neg_proof {M : ℝ} (hM : 1 / 2 < M) :
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

open MeasureTheory in
open Grothendieck in

open MeasureTheory
open scoped BigOperators Real Topology

namespace Grothendieck

/-- **The paper's `p`-integral.** For `A, B > 0` and `M > 1/2`,
`∫₀^∞ (A + B p²)^{-M} dp = A^{1/2-M} B^{-1/2} · ½ Γ(½) Γ(M-½) / Γ(M)`. -/
theorem integral_add_mul_sq_rpow_neg_proof {A B M : ℝ} (hA : 0 < A) (hB : 0 < B) (hM : 1 / 2 < M) :
    (∫ p in Set.Ioi (0:ℝ), (A + B * p ^ 2) ^ (-M))
      = A ^ (1 / 2 - M) * B ^ (-(1 / 2) : ℝ) *
          (1 / 2 * Real.Gamma (1 / 2) * Real.Gamma (M - 1 / 2) / Real.Gamma M) := by
  rw [integral_add_mul_sq_rpow_neg_eq hA hB, integral_one_add_sq_rpow_neg_proof hM]
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

open MeasureTheory in
open Grothendieck in
theorem solution {A B M : ℝ} (hA : 0 < A) (hB : 0 < B) (hM : 1 / 2 < M) :
    (∫ p in Set.Ioi (0:ℝ), (A + B * p ^ 2) ^ (-M))
      = A ^ (1 / 2 - M) * B ^ (-(1 / 2) : ℝ) *
          (1 / 2 * Real.Gamma (1 / 2) * Real.Gamma (M - 1 / 2) / Real.Gamma M) :=
  integral_add_mul_sq_rpow_neg_proof hA hB hM
