-- Prove2me | solution 1 for N25.etaAnalytic25_normalized_hasSum
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:35:52.760207+00:00
-- url     : https://prove2.me/submissions/db5f8103-c964-485b-834b-eb65d456eac4

import Mathlib
import Definitions.Def_N25_UnitAnalytic
import Theorems.Thm_N25_etaResidueSeries25_hasSum
import Theorems.Thm_N25_etaResidueProduct25_eq
import Theorems.Thm_N25_etaAnalytic25_eq_product

set_option autoImplicit false

open scoped BigOperators

namespace N25

/-- Dividing the literal eta factor by its exponential prefactor leaves its integral residue series. -/
theorem _root_.solution
    (g : ℕ) (hg : 0 < g) (hg25 : g < 25) (τ : UpperHalfPlane) :
    HasSum (fun n : ℕ => ((PowerSeries.coeff n (etaResidueSeries25 g) : ℤ) : ℂ) *
      Complex.exp (2 * Real.pi * Complex.I * (τ : ℂ)) ^ n)
      (etaAnalytic25 g τ / Complex.exp (Real.pi * Complex.I *
        (((g : ℂ) / 25) ^ 2 - (g : ℂ) / 25 + 1 / 6) * (25 * (τ : ℂ)))) := by
  let q := Complex.exp (2 * Real.pi * Complex.I * (τ : ℂ))
  have hq : ‖q‖ < 1 := by
    rw [Complex.norm_exp, Real.exp_lt_one_iff]
    have hp := mul_pos Real.pi_pos τ.im_pos
    change 0 < Real.pi * (τ : ℂ).im at hp
    simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im] at *
    norm_num at *
    nlinarith
  have hs := etaResidueSeries25_hasSum g hg hg25 q hq
  rw [etaResidueProduct25_eq g hg hg25 q hq] at hs
  have he : etaAnalytic25 g τ / Complex.exp (Real.pi * Complex.I *
      (((g : ℂ) / 25) ^ 2 - (g : ℂ) / 25 + 1 / 6) * (25 * (τ : ℂ))) =
      ∏' n : ℕ, ((1 - q ^ (25 * n + g)) * (1 - q ^ (25 * (n + 1) - g))) := by
    rw [etaAnalytic25_eq_product g hg hg25 τ]
    exact mul_div_cancel_left₀ _ (Complex.exp_ne_zero _)
  rw [he]
  exact hs

end N25
