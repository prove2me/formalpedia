-- Prove2me | solution 1 for MasulloRH.HeightTwoScalar.theta_row_sound
-- status  : ACCEPTED   (prove)
-- author  : @sflicht
-- created : 2026-11-21T20:11:06.961776+00:00
-- url     : https://prove2.me/submissions/50d64efb-be63-43df-bbf1-2c4ec77930b8

import Mathlib
import Definitions.Def_MasulloRH_ThetaCertificate

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 16384

open scoped BigOperators
open _root_.MasulloRH.CertifiedExp _root_.MasulloRH.Certificates
open _root_.MasulloRH.HeightTwoScalar

namespace N5ThetaCertificateProof

namespace MasulloRH.CertifiedExp

theorem enclosure_of_argument_interval {x a b l u : ℝ}
    (hx : a ≤ x ∧ x ≤ b) (hl : l ≤ Real.exp a) (hu : Real.exp b ≤ u) :
    l ≤ Real.exp x ∧ Real.exp x ≤ u :=
  ⟨hl.trans (Real.exp_le_exp.mpr hx.1), (Real.exp_le_exp.mpr hx.2).trans hu⟩

end MasulloRH.CertifiedExp

/- Embedded checked source: Solutions/ThetaPolynomialCertificateCore.lean -/
set_option autoImplicit false

namespace MasulloRH.CertifiedExp

theorem nonneg_product_enclosure {x y a b c d : ℝ}
    (ha : 0 ≤ a) (hc : 0 ≤ c)
    (hx : a ≤ x ∧ x ≤ b) (hy : c ≤ y ∧ y ≤ d) :
    a * c ≤ x * y ∧ x * y ≤ b * d :=
  ⟨mul_le_mul hx.1 hy.1 hc (ha.trans hx.1),
    mul_le_mul hx.2 hy.2 (hc.trans hy.1) (ha.trans (hx.1.trans hx.2))⟩

/-- The left factor is nonnegative; the right factor may straddle zero.
The four extra inequalities are finite rational arithmetic in applications. -/
theorem nonneg_left_product_enclosure {x y a b c d L U : ℝ}
    (ha : 0 ≤ a) (hx : a ≤ x ∧ x ≤ b) (hy : c ≤ y ∧ y ≤ d)
    (hL₁ : L ≤ a * c) (hL₂ : L ≤ b * c)
    (hU₁ : a * d ≤ U) (hU₂ : b * d ≤ U) :
    L ≤ x * y ∧ x * y ≤ U := by
  have hx0 := ha.trans hx.1
  have hlo : L ≤ x * c := by
    rcases le_total 0 c with hc | hc
    · exact hL₁.trans (mul_le_mul_of_nonneg_right hx.1 hc)
    · exact hL₂.trans (mul_le_mul_of_nonpos_right hx.2 hc)
  have hhi : x * d ≤ U := by
    rcases le_total 0 d with hd | hd
    · exact (mul_le_mul_of_nonneg_right hx.2 hd).trans hU₂
    · exact (mul_le_mul_of_nonpos_right hx.1 hd).trans hU₁
  exact ⟨hlo.trans (mul_le_mul_of_nonneg_left hy.1 hx0),
    (mul_le_mul_of_nonneg_left hy.2 hx0).trans hhi⟩

theorem thetaPolynomial_six_eq (r : ℝ) :
    thetaPolynomial 6 r = r - 2 * r ^ 4 + r ^ 9 + r ^ 25 - 2 * r ^ 36 -
      r ^ 64 - 3 * r ^ 100 - r ^ 144 + 2 * r ^ 256 + 2 * r ^ 400 + 2 * r ^ 576 := by
  norm_num [thetaPolynomial, Finset.sum_range_succ]
  ring

/-- A compact enclosure using exact cancellation in the six-term dyadic sum.
Only powers up to 64 appear in the certificate's rational arithmetic. -/
theorem thetaPolynomial_six_enclosure {r lo hi : ℝ}
    (hlo : 0 ≤ lo) (hhi : hi ≤ 1) (hr : lo ≤ r ∧ r ≤ hi) :
    lo - 2 * hi ^ 4 + lo ^ 9 + lo ^ 25 - 2 * hi ^ 36 - 5 * hi ^ 64 ≤
      thetaPolynomial 6 r ∧
    thetaPolynomial 6 r ≤
      hi - 2 * lo ^ 4 + hi ^ 9 + hi ^ 25 - 2 * lo ^ 36 + 6 * hi ^ 64 := by
  have hr0 := hlo.trans hr.1
  have hhi0 := hr0.trans hr.2
  have hpow (n : ℕ) (hn : 64 ≤ n) : 0 ≤ r ^ n ∧ r ^ n ≤ hi ^ 64 := by
    exact ⟨pow_nonneg hr0 n,
      (pow_le_pow_left₀ hr0 hr.2 n).trans (pow_le_pow_of_le_one hhi0 hhi hn)⟩
  have h64 := hpow 64 (by decide)
  have h100 := hpow 100 (by decide)
  have h144 := hpow 144 (by decide)
  have h256 := hpow 256 (by decide)
  have h400 := hpow 400 (by decide)
  have h576 := hpow 576 (by decide)
  have hl4 := pow_le_pow_left₀ hlo hr.1 4
  have hu4 := pow_le_pow_left₀ hr0 hr.2 4
  have hl9 := pow_le_pow_left₀ hlo hr.1 9
  have hu9 := pow_le_pow_left₀ hr0 hr.2 9
  have hl25 := pow_le_pow_left₀ hlo hr.1 25
  have hu25 := pow_le_pow_left₀ hr0 hr.2 25
  have hl36 := pow_le_pow_left₀ hlo hr.1 36
  have hu36 := pow_le_pow_left₀ hr0 hr.2 36
  rw [thetaPolynomial_six_eq]
  constructor <;> linarith

theorem thetaPolynomial_six_enclosure_of_bounds {r lo hi L U : ℝ}
    (hlo : 0 ≤ lo) (hhi : hi ≤ 1) (hr : lo ≤ r ∧ r ≤ hi)
    (hL : L ≤ lo - 2 * hi ^ 4 + lo ^ 9 + lo ^ 25 - 2 * hi ^ 36 - 5 * hi ^ 64)
    (hU : hi - 2 * lo ^ 4 + hi ^ 9 + hi ^ 25 - 2 * lo ^ 36 + 6 * hi ^ 64 ≤ U) :
    L ≤ thetaPolynomial 6 r ∧ thetaPolynomial 6 r ≤ U := by
  have h := thetaPolynomial_six_enclosure hlo hhi hr
  exact ⟨hL.trans h.1, h.2.trans hU⟩


end MasulloRH.CertifiedExp

/- Embedded checked source: Solutions/ThetaHeightTwoScalarCore.lean -/
set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace MasulloRH.HeightTwoScalar
open MasulloRH.CertifiedExp

theorem pi_enclosure :
    (314159265358979 / 100000000000000 : ℝ) ≤ Real.pi ∧
      Real.pi ≤ (314159265358980 / 100000000000000 : ℝ) := by
  constructor <;> linarith [Real.pi_gt_d20, Real.pi_lt_d20]

theorem pulse_coefficient_enclosure :
    (1692568750643 / 1000000000000 : ℝ) ≤ 3 / Real.sqrt Real.pi ∧
      3 / Real.sqrt Real.pi ≤ (1692568750644 / 1000000000000 : ℝ) := by
  have hroot : (177245385090551 / 100000000000000 : ℝ) ≤ Real.sqrt Real.pi ∧
      Real.sqrt Real.pi ≤ (177245385090552 / 100000000000000 : ℝ) := by
    constructor
    · apply Real.le_sqrt_of_sq_le
      nlinarith [Real.pi_gt_d20]
    · apply (Real.sqrt_le_left (by norm_num :
        (0 : ℝ) ≤ 177245385090552 / 100000000000000)).2
      nlinarith [Real.pi_lt_d20]
  have hp : 0 < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
  constructor
  · apply (le_div_iff₀ hp).2
    nlinarith [hroot.2]
  · apply (div_le_iff₀ hp).2
    nlinarith [hroot.1]

theorem thetaMomentPolynomial_six_eq (r : ℝ) :
    thetaMomentPolynomial 6 r = r - 8*r^4 + 9*r^9 + 25*r^25 - 72*r^36 -
      64*r^64 - 300*r^100 - 144*r^144 + 512*r^256 + 800*r^400 + 1152*r^576 := by
  norm_num [thetaMomentPolynomial, Finset.sum_range_succ]
  ring

theorem thetaMomentPolynomial_six_enclosure {r lo hi : ℝ}
    (hlo : 0 ≤ lo) (hhi : hi ≤ 1) (hr : lo ≤ r ∧ r ≤ hi) :
    lo - 8*hi^4 + 9*lo^9 + 25*lo^25 - 72*hi^36 - 508*hi^64 ≤
      thetaMomentPolynomial 6 r ∧
    thetaMomentPolynomial 6 r ≤
      hi - 8*lo^4 + 9*hi^9 + 25*hi^25 - 72*lo^36 + 2464*hi^64 := by
  have hr0 := hlo.trans hr.1
  have hhi0 := hr0.trans hr.2
  have hpow (n : ℕ) (hn : 64 ≤ n) : 0 ≤ r^n ∧ r^n ≤ hi^64 := by
    exact ⟨pow_nonneg hr0 n,
      (pow_le_pow_left₀ hr0 hr.2 n).trans (pow_le_pow_of_le_one hhi0 hhi hn)⟩
  have h64 := hpow 64 (by decide)
  have h100 := hpow 100 (by decide)
  have h144 := hpow 144 (by decide)
  have h256 := hpow 256 (by decide)
  have h400 := hpow 400 (by decide)
  have h576 := hpow 576 (by decide)
  have hl4 := pow_le_pow_left₀ hlo hr.1 4
  have hu4 := pow_le_pow_left₀ hr0 hr.2 4
  have hl9 := pow_le_pow_left₀ hlo hr.1 9
  have hu9 := pow_le_pow_left₀ hr0 hr.2 9
  have hl25 := pow_le_pow_left₀ hlo hr.1 25
  have hu25 := pow_le_pow_left₀ hr0 hr.2 25
  have hl36 := pow_le_pow_left₀ hlo hr.1 36
  have hu36 := pow_le_pow_left₀ hr0 hr.2 36
  rw [thetaMomentPolynomial_six_eq]
  constructor <;> linarith

theorem polynomial_of_check (r : ℝ) (lo hi L U : ℚ)
    (hr : (lo : ℝ) ≤ r ∧ r ≤ (hi : ℝ)) (h : PolynomialCheck lo hi L U) :
    (L : ℝ) ≤ thetaPolynomial 6 r ∧ thetaPolynomial 6 r ≤ (U : ℝ) := by
  rcases h with ⟨hlo, hhi, hL, hU⟩
  apply thetaPolynomial_six_enclosure_of_bounds
    (show (0 : ℝ) ≤ (lo : ℝ) by exact_mod_cast hlo)
    (show (hi : ℝ) ≤ 1 by exact_mod_cast hhi) hr
  · exact_mod_cast hL
  · exact_mod_cast hU

theorem moment_of_check (r : ℝ) (lo hi L U : ℚ)
    (hr : (lo : ℝ) ≤ r ∧ r ≤ (hi : ℝ)) (h : MomentCheck lo hi L U) :
    (L : ℝ) ≤ thetaMomentPolynomial 6 r ∧ thetaMomentPolynomial 6 r ≤ (U : ℝ) := by
  rcases h with ⟨hlo, hhi, hL, hU⟩
  have ht := thetaMomentPolynomial_six_enclosure
    (show (0 : ℝ) ≤ (lo : ℝ) by exact_mod_cast hlo)
    (show (hi : ℝ) ≤ 1 by exact_mod_cast hhi) hr
  constructor
  · apply le_trans _ ht.1
    exact_mod_cast hL
  · apply le_trans ht.2
    exact_mod_cast hU

theorem product_enclosure {x y a b c d L U : ℝ}
    (hx : a ≤ x ∧ x ≤ b) (hy : c ≤ y ∧ y ≤ d)
    (hLac : L ≤ a*c) (hLad : L ≤ a*d) (hLbc : L ≤ b*c) (hLbd : L ≤ b*d)
    (hUac : a*c ≤ U) (hUad : a*d ≤ U) (hUbc : b*c ≤ U) (hUbd : b*d ≤ U) :
    L ≤ x*y ∧ x*y ≤ U := by
  constructor
  · rcases le_total 0 y with hy0 | hy0
    · apply le_trans _ (mul_le_mul_of_nonneg_right hx.1 hy0)
      rcases le_total 0 a with ha | ha
      · exact hLac.trans (mul_le_mul_of_nonneg_left hy.1 ha)
      · exact hLad.trans (mul_le_mul_of_nonpos_left hy.2 ha)
    · apply le_trans _ (mul_le_mul_of_nonpos_right hx.2 hy0)
      rcases le_total 0 b with hb | hb
      · exact hLbc.trans (mul_le_mul_of_nonneg_left hy.1 hb)
      · exact hLbd.trans (mul_le_mul_of_nonpos_left hy.2 hb)
  · rcases le_total 0 y with hy0 | hy0
    · apply le_trans (mul_le_mul_of_nonneg_right hx.2 hy0)
      rcases le_total 0 b with hb | hb
      · exact (mul_le_mul_of_nonneg_left hy.2 hb).trans hUbd
      · exact (mul_le_mul_of_nonpos_left hy.1 hb).trans hUbc
    · apply le_trans (mul_le_mul_of_nonpos_right hx.1 hy0)
      rcases le_total 0 a with ha | ha
      · exact (mul_le_mul_of_nonneg_left hy.2 ha).trans hUad
      · exact (mul_le_mul_of_nonpos_left hy.1 ha).trans hUac

theorem product_of_check (x y : ℝ) (a b c d L U : ℚ)
    (hx : (a : ℝ) ≤ x ∧ x ≤ (b : ℝ)) (hy : (c : ℝ) ≤ y ∧ y ≤ (d : ℝ))
    (h : ProductCheck a b c d L U) :
    (L : ℝ) ≤ x*y ∧ x*y ≤ (U : ℝ) := by
  rcases h with ⟨hLac, hLad, hLbc, hLbd, hUac, hUad, hUbc, hUbd⟩
  apply product_enclosure hx hy
  all_goals first | exact_mod_cast hLac | exact_mod_cast hLad |
    exact_mod_cast hLbc | exact_mod_cast hLbd | exact_mod_cast hUac |
    exact_mod_cast hUad | exact_mod_cast hUbc | exact_mod_cast hUbd

end MasulloRH.HeightTwoScalar

/- Embedded checked source: Solutions/ThetaHeightTwoRowAssembler.lean -/
/-!
# Shared assembly of rational theta-row enclosures

The numerical table supplies only rational fields and closed arithmetic
checks, together with independently proved bounds on exponential values at
rational arguments.  This module performs the real interval arithmetic once
for each branch, so generated rows can apply a theorem directly.

These theorems concern the finite analytic branch models.  Their connection to
the actual theta sum remains the proved finite-model truncation bridge; no
numerical claim or branch validity condition is hidden in this assembler.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace MasulloRH.HeightTwoScalar
open Set MasulloRH.CertifiedExp MasulloRH.Certificates

theorem pi_rat_enclosure :
    (piLowerQ : ℝ) ≤ Real.pi ∧ Real.pi ≤ (piUpperQ : ℝ) := by
  simpa only [piLowerQ, piUpperQ, Rat.cast_div, Rat.cast_ofNat] using pi_enclosure

theorem theta_direct_row (q : ThetaRow) (hc : DirectCheck q)
    (eiL : (q.iL : ℝ) ≤ Real.exp (q.iArgL : ℝ))
    (eiU : Real.exp (q.iArgU : ℝ) ≤ (q.iU : ℝ))
    (erL : (q.rL : ℝ) ≤ Real.exp (q.rArgL : ℝ))
    (erU : Real.exp (q.rArgU : ℝ) ≤ (q.rU : ℝ))
    (x : ℝ) (hx : x ∈ Icc (q.left : ℝ) (q.right : ℝ)) :
    ((q.valueL : ℝ) ≤ thetaBranchModel 6 false x ∧
      thetaBranchModel 6 false x ≤ (q.valueU : ℝ)) ∧
    ((q.derivL : ℝ) ≤ thetaBranchDerivative 6 false x ∧
      thetaBranchDerivative 6 false x ≤ (q.derivU : ℝ)) := by
  rcases hc with ⟨_hlr, hiArgL, hiArgU, hrArgL, hrArgU,
    hPi, hP, hM, hAM, hvL, hvU, hdL, hdU⟩
  have hiArgLr : (q.iArgL : ℝ) = 2*(q.left : ℝ) := by exact_mod_cast hiArgL
  have hiArgUr : (q.iArgU : ℝ) = 2*(q.right : ℝ) := by exact_mod_cast hiArgU
  have hrArgLr : (q.rArgL : ℝ) = -(q.alphaU : ℝ) := by exact_mod_cast hrArgL
  have hrArgUr : (q.rArgU : ℝ) = -(q.alphaL : ℝ) := by exact_mod_cast hrArgU
  have hi : (q.iL : ℝ) ≤ Real.exp (2*x) ∧ Real.exp (2*x) ≤ (q.iU : ℝ) := by
    exact enclosure_of_argument_interval
      (by constructor <;> linarith only [hx.1, hx.2, hiArgLr, hiArgUr]) eiL eiU
  have ha := product_of_check Real.pi (Real.exp (2*x))
    piLowerQ piUpperQ q.iL q.iU q.alphaL q.alphaU pi_rat_enclosure hi hPi
  have hr : (q.rL : ℝ) ≤ Real.exp (-Real.pi * Real.exp (2*x)) ∧
      Real.exp (-Real.pi * Real.exp (2*x)) ≤ (q.rU : ℝ) := by
    exact enclosure_of_argument_interval
      (by constructor <;> linarith only [ha.1, ha.2, hrArgLr, hrArgUr]) erL erU
  have hp := polynomial_of_check (Real.exp (-Real.pi * Real.exp (2*x)))
    q.rL q.rU q.pL q.pU hr hP
  have hm := moment_of_check (Real.exp (-Real.pi * Real.exp (2*x)))
    q.rL q.rU q.mL q.mU hr hM
  have ham := product_of_check (Real.pi * Real.exp (2*x))
    (thetaMomentPolynomial 6 (Real.exp (-Real.pi * Real.exp (2*x))))
    q.alphaL q.alphaU q.mL q.mU q.amL q.amU ha hm hAM
  have hvLr : (q.valueL : ℝ) ≤ 2*(q.pL : ℝ) := by exact_mod_cast hvL
  have hvUr : 2*(q.pU : ℝ) ≤ (q.valueU : ℝ) := by exact_mod_cast hvU
  have hdLr : (q.derivL : ℝ) ≤ -4*(q.amU : ℝ) := by exact_mod_cast hdL
  have hdUr : -4*(q.amL : ℝ) ≤ (q.derivU : ℝ) := by exact_mod_cast hdU
  constructor
  · simp only [thetaBranchModel, thetaDirectModel, Bool.false_eq_true, ↓reduceIte]
    constructor <;> linarith only [hp.1, hp.2, hvLr, hvUr]
  · simp only [thetaBranchDerivative, thetaDirectDerivative, Bool.false_eq_true, ↓reduceIte]
    constructor <;> linarith only [ham.1, ham.2, hdLr, hdUr]

/-- Assemble one reflected theta row.  Prefactor bounds are independent
endpoint exponential enclosures, and all products are checked rationally. -/
theorem theta_reflected_row (q : ThetaRow) (hc : ReflectedCheck q)
    (eiL : (q.iL : ℝ) ≤ Real.exp (q.iArgL : ℝ))
    (eiU : Real.exp (q.iArgU : ℝ) ≤ (q.iU : ℝ))
    (erL : (q.rL : ℝ) ≤ Real.exp (q.rArgL : ℝ))
    (erU : Real.exp (q.rArgU : ℝ) ≤ (q.rU : ℝ))
    (efL : (q.prefL : ℝ) ≤ Real.exp (q.prefArgL : ℝ))
    (efU : Real.exp (q.prefArgU : ℝ) ≤ (q.prefU : ℝ))
    (x : ℝ) (hx : x ∈ Icc (q.left : ℝ) (q.right : ℝ)) :
    ((q.valueL : ℝ) ≤ thetaBranchModel 6 true x ∧
      thetaBranchModel 6 true x ≤ (q.valueU : ℝ)) ∧
    ((q.derivL : ℝ) ≤ thetaBranchDerivative 6 true x ∧
      thetaBranchDerivative 6 true x ≤ (q.derivU : ℝ)) := by
  rcases hc with ⟨_hlr, hiArgL, hiArgU, hrArgL, hrArgU, hfArgL, hfArgU,
    hPi, hP, hM, hAM, hinL, hinU, hValue, hDeriv⟩
  have hiArgLr : (q.iArgL : ℝ) = -2*(q.right : ℝ) := by exact_mod_cast hiArgL
  have hiArgUr : (q.iArgU : ℝ) = -2*(q.left : ℝ) := by exact_mod_cast hiArgU
  have hrArgLr : (q.rArgL : ℝ) = -(q.alphaU : ℝ) := by exact_mod_cast hrArgL
  have hrArgUr : (q.rArgU : ℝ) = -(q.alphaL : ℝ) := by exact_mod_cast hrArgU
  have hfArgLr : (q.prefArgL : ℝ) = -(q.right : ℝ) := by exact_mod_cast hfArgL
  have hfArgUr : (q.prefArgU : ℝ) = -(q.left : ℝ) := by exact_mod_cast hfArgU
  have hi : (q.iL : ℝ) ≤ Real.exp (-2*x) ∧ Real.exp (-2*x) ≤ (q.iU : ℝ) := by
    exact enclosure_of_argument_interval
      (by constructor <;> linarith only [hx.1, hx.2, hiArgLr, hiArgUr]) eiL eiU
  have ha0 := product_of_check Real.pi (Real.exp (-2*x))
    piLowerQ piUpperQ q.iL q.iU (16*q.alphaL) (16*q.alphaU) pi_rat_enclosure hi hPi
  have ha : (q.alphaL : ℝ) ≤ Real.pi/16 * Real.exp (-2*x) ∧
      Real.pi/16 * Real.exp (-2*x) ≤ (q.alphaU : ℝ) := by
    push_cast at ha0
    constructor <;> linarith only [ha0.1, ha0.2]
  have hr : (q.rL : ℝ) ≤ Real.exp (-(Real.pi/16) * Real.exp (-2*x)) ∧
      Real.exp (-(Real.pi/16) * Real.exp (-2*x)) ≤ (q.rU : ℝ) := by
    exact enclosure_of_argument_interval
      (by constructor <;> linarith only [ha.1, ha.2, hrArgLr, hrArgUr]) erL erU
  have hp := polynomial_of_check (Real.exp (-(Real.pi/16) * Real.exp (-2*x)))
    q.rL q.rU q.pL q.pU hr hP
  have hm := moment_of_check (Real.exp (-(Real.pi/16) * Real.exp (-2*x)))
    q.rL q.rU q.mL q.mU hr hM
  have ham := product_of_check (Real.pi/16 * Real.exp (-2*x))
    (thetaMomentPolynomial 6 (Real.exp (-(Real.pi/16) * Real.exp (-2*x))))
    q.alphaL q.alphaU q.mL q.mU q.amL q.amU ha hm hAM
  have hf : (q.prefL : ℝ) ≤ Real.exp (-x) ∧ Real.exp (-x) ≤ (q.prefU : ℝ) := by
    exact enclosure_of_argument_interval
      (by constructor <;> linarith only [hx.1, hx.2, hfArgLr, hfArgUr]) efL efU
  have hv := product_of_check (Real.exp (-x))
    (thetaPolynomial 6 (Real.exp (-(Real.pi/16) * Real.exp (-2*x))))
    q.prefL q.prefU q.pL q.pU q.valueL q.valueU hf hp hValue
  have hinLr : (q.insideL : ℝ) ≤ -(q.pU : ℝ)+2*(q.amL : ℝ) := by exact_mod_cast hinL
  have hinUr : -(q.pL : ℝ)+2*(q.amU : ℝ) ≤ (q.insideU : ℝ) := by exact_mod_cast hinU
  have hin :
      (q.insideL : ℝ) ≤
        -thetaPolynomial 6 (Real.exp (-(Real.pi/16) * Real.exp (-2*x))) +
          2*(Real.pi/16 * Real.exp (-2*x))*
            thetaMomentPolynomial 6 (Real.exp (-(Real.pi/16) * Real.exp (-2*x))) ∧
      -thetaPolynomial 6 (Real.exp (-(Real.pi/16) * Real.exp (-2*x))) +
          2*(Real.pi/16 * Real.exp (-2*x))*
            thetaMomentPolynomial 6 (Real.exp (-(Real.pi/16) * Real.exp (-2*x))) ≤
        (q.insideU : ℝ) := by
    constructor <;> linarith only [hp.1, hp.2, ham.1, ham.2, hinLr, hinUr]
  have hd := product_of_check (Real.exp (-x))
    (-thetaPolynomial 6 (Real.exp (-(Real.pi/16) * Real.exp (-2*x))) +
      2*(Real.pi/16 * Real.exp (-2*x))*
        thetaMomentPolynomial 6 (Real.exp (-(Real.pi/16) * Real.exp (-2*x))))
    q.prefL q.prefU q.insideL q.insideU q.derivL q.derivU hf hin hDeriv
  constructor
  · simpa only [thetaBranchModel, thetaReflectedModel, ↓reduceIte] using hv
  · simpa only [thetaBranchDerivative, thetaReflectedDerivative, ↓reduceIte] using hd

end MasulloRH.HeightTwoScalar

end N5ThetaCertificateProof

/-- Boolean dispatch of a checked rational theta row. Exponential premises are
supplied by valid exponential rows through `exp_row_sound`. -/
theorem solution
    (q : ThetaRow) (reflected : Bool) (hq : q.Valid reflected)
    (eiL : (q.iL : ℝ) ≤ Real.exp (q.iArgL : ℝ))
    (eiU : Real.exp (q.iArgU : ℝ) ≤ (q.iU : ℝ))
    (erL : (q.rL : ℝ) ≤ Real.exp (q.rArgL : ℝ))
    (erU : Real.exp (q.rArgU : ℝ) ≤ (q.rU : ℝ))
    (epref : reflected = true →
      (q.prefL : ℝ) ≤ Real.exp (q.prefArgL : ℝ) ∧
        Real.exp (q.prefArgU : ℝ) ≤ (q.prefU : ℝ)) :
    ∀ x ∈ Set.Icc (q.left : ℝ) (q.right : ℝ),
      ((q.valueL : ℝ) ≤ thetaBranchModel 6 reflected x ∧
        thetaBranchModel 6 reflected x ≤ (q.valueU : ℝ)) ∧
      ((q.derivL : ℝ) ≤ thetaBranchDerivative 6 reflected x ∧
        thetaBranchDerivative 6 reflected x ≤ (q.derivU : ℝ)) := by
  intro x hx
  cases reflected
  · exact N5ThetaCertificateProof.MasulloRH.HeightTwoScalar.theta_direct_row q
      (by simpa only [ThetaRow.Valid, Bool.false_eq_true, ↓reduceIte] using hq)
      eiL eiU erL erU x hx
  · exact N5ThetaCertificateProof.MasulloRH.HeightTwoScalar.theta_reflected_row q
      (by simpa only [ThetaRow.Valid, ↓reduceIte] using hq)
      eiL eiU erL erU (epref rfl).1 (epref rfl).2 x hx

#print axioms solution
