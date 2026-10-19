-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff.cutoff50
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-10-16T12:11:17.487665+00:00
-- url     : https://prove2.me/submissions/d330f0b8-1e2d-4dd2-b245-cc01401f2e4d

import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Cyclic
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_ScalarBounds
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Localization
import Definitions.Def_HlawkaSchatten_GapComparison
import Mathlib
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_BoxHessian
import Theorems.Thm_HlawkaSchatten_DiagonalConstruction_exists_normalized_failure
import Theorems.Thm_HlawkaSchatten_DiagonalConstruction_normalized_pair_sum_le
import Theorems.Thm_HlawkaSchatten_DiagonalConstruction_antitoneOn_scalarEnvelope
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Coordinates
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_BoxConvexity
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_NormHessian
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_BoxGeometry
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_BoxCoordinates
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_CyclicWitness
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_OrbitAveraging
import Theorems.Thm_HlawkaSchatten_DiagonalConstruction_cyclic_denominator_pos
import Theorems.Thm_HlawkaSchatten_DiagonalConstruction_real_bound_of_fin_three
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff_real_bound62
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_ComplexTransfer
import Theorems.Thm_HlawkaSchatten_DiagonalConstruction_cyclicConstant_le_of_complex_constant

/- Cutoff 50 for the sharp diagonal Hlawka constant. Builds on Ezzeri Esa's Apache-2.0 Hlawka-Schatten
construction and the accepted cutoff-62 development on Prove2Me; new here: the singleton lower bound that
tightens the localization box, the asymmetric-box Hessian margins on [50, 62], and the scalar window on [50, 62]. -/

set_option autoImplicit false

/-
Scalar estimates on the window 50 ≤ p ≤ 62.

Adapted from the accepted scalar section for the window [62,63], which builds on
Ezzeri Esa's Apache-2.0 formalization of the diagonal construction.

The witness is t = (3/(4p))^{1/p}. Writing x = 1/p, the cyclic numerator and
denominator at the witness are bounded by explicit polynomials in x
(`Nlo`, `Dup`), the envelope deficit by `Glo`, and the two resulting
polynomial certificates are checked on x ∈ [1/62, 1/50] by expansion around
x = 1/62. The bound `log p ≤ log(225/4) + 4p/225 - 1` (tangent at p = 225/4)
is used uniformly over the whole window. The file is self-contained: the
denominator positivity and the boundedness of the ratio are proved here.
-/

namespace HlawkaSchatten.DiagonalCutoff50

open HlawkaSchatten.DiagonalConstruction

/-! ### Elementary analytic bounds -/

lemma exp_quartic {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    Real.exp x ≤ 1+x+x^2/2+x^3/6+x^4/12 := by
  have h := Real.exp_bound' hx hx1 (n := 4) (by norm_num)
  norm_num [Finset.sum_range_succ, Nat.factorial] at h
  nlinarith [pow_nonneg hx 4]

lemma exp_neg_quartic_lower {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    1-x+x^2/2-x^3/6-x^4/12 ≤ Real.exp (-x) := by
  have h := Real.exp_bound (x := -x) (n := 4)
    (by simpa only [abs_neg, abs_of_nonneg hx] using hx1) (by norm_num)
  have hh := (abs_sub_le_iff.mp h).2
  norm_num [Finset.sum_range_succ, Nat.factorial, abs_of_nonneg hx] at hh
  nlinarith [pow_nonneg hx 4]

lemma one_sub_exp_neg_quartic {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    x-x^2/2+x^3/6-x^4/12 ≤ 1-Real.exp (-x) := by
  have h := Real.exp_bound (x := -x) (n := 4)
    (by simpa only [abs_neg, abs_of_nonneg hx] using hx1) (by norm_num)
  have hh := (abs_sub_le_iff.mp h).1
  norm_num [Finset.sum_range_succ, Nat.factorial, abs_of_nonneg hx] at hh
  nlinarith [pow_nonneg hx 4]

lemma log_one_add_upper {u : ℝ} (hu : 0 ≤ u) (hu1 : u ≤ 1/2) :
    Real.log (1+u) ≤ u-u^2/2+2*u^3 := by
  have h := Real.abs_log_sub_add_sum_range_le
    (x := -u) (by rw [abs_neg, abs_of_nonneg hu]; linarith) 2
  have hh := (abs_le.mp h).2
  norm_num [Finset.sum_range_succ, abs_of_nonneg hu] at hh
  have hd : 0 < 1-u := by linarith
  have he : u^3/(1-u) ≤ 2*u^3 := by
    apply (div_le_iff₀ hd).mpr
    nlinarith [mul_nonneg (pow_nonneg hu 3) (show 0 ≤ 1-2*u by linarith)]
  linarith

lemma log_two_add_upper {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    Real.log (2+x) ≤ 6931471808/10^10+x/2-x^2/8+x^3/4 := by
  have h := log_one_add_upper (u := x/2) (by positivity) (by linarith)
  have he : Real.log (2+x) = Real.log 2+Real.log (1+x/2) := by
    rw [← Real.log_mul (by norm_num) (by positivity)]
    congr 1
    ring
  rw [he]
  nlinarith [Real.log_two_lt_d9]

lemma log_two_add {x : ℝ} (hx : 0 ≤ x) :
    6931471803 / 10 ^ 10 + x / 2 - x ^ 2 / 4 ≤ Real.log (2 + x) := by
  have hsplit : Real.log (2 + x) = Real.log 2 + Real.log ((2 + x) / 2) := by
    rw [Real.log_div (by positivity) (by norm_num)]
    ring
  have hlo := Real.one_sub_inv_le_log_of_pos (show 0 < (2 + x) / 2 by positivity)
  have hinv : 1 - ((2 + x) / 2)⁻¹ = x / (2 + x) := by field_simp; ring
  have hfrac : x / 2 - x ^ 2 / 4 ≤ x / (2 + x) := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith [pow_nonneg hx 3]
  rw [hsplit]; linarith [Real.log_two_gt_d9]

lemma log_three_quarters_neg : Real.log (3 / 4 : ℝ) < 0 :=
  Real.log_neg (by norm_num) (by norm_num)

/-! ### Basic facts about the cyclic quantities -/

lemma cyclicB_nonneg (p t : ℝ) : 0 ≤ cyclicB p t := by
  unfold cyclicB
  positivity

lemma cyclicA_nonneg (p : ℝ) {t : ℝ} (ht : 0 ≤ t) : 0 ≤ cyclicA p t := by
  unfold cyclicA
  have := Real.rpow_nonneg ht p
  positivity

lemma cyclicB_rpow {p : ℝ} (hp : 0 < p) (t : ℝ) :
    cyclicB p t ^ p = 2 * |1 - t| ^ p + (2 : ℝ) ^ p := by
  rw [cyclicB, ← Real.rpow_mul (by positivity :
    0 ≤ 2 * |1 - t| ^ p + (2 : ℝ) ^ p), one_div_mul_cancel hp.ne', Real.rpow_one]

lemma cyclicA_rpow {p t : ℝ} (hp : 0 < p) (ht : 0 ≤ t) :
    cyclicA p t ^ p = t ^ p + 2 := by
  rw [cyclicA, ← Real.rpow_mul (by positivity : 0 ≤ t ^ p + 2),
    one_div_mul_cancel hp.ne', Real.rpow_one]

lemma cyclicB_ge_two {p t : ℝ} (hp : 0 < p) : 2 ≤ cyclicB p t := by
  apply (Real.rpow_le_rpow_iff (by norm_num) (cyclicB_nonneg p t) hp).mp
  rw [cyclicB_rpow hp]
  have hn := Real.rpow_nonneg (abs_nonneg (1 - t)) p
  linarith

/-- Positivity of the cyclic denominator (proved here for `1 < p`, `0 ≤ t`). -/
lemma denominator_pos {p t : ℝ} (hp : 1 < p) (ht : 0 ≤ t) :
    0 < 6 * cyclicA p t - 3 * cyclicB p t := by
  have hp0 : 0 < p := by linarith
  have habs : |1 - t| ^ p ≤ 1 + t ^ p := by
    rcases le_total t 1 with h | h
    · have h1 : |1 - t| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
      have := Real.rpow_le_rpow (abs_nonneg _) h1 hp0.le
      rw [Real.one_rpow] at this
      linarith [Real.rpow_nonneg ht p]
    · have h1 : |1 - t| ≤ t := abs_le.mpr ⟨by linarith, by linarith⟩
      have := Real.rpow_le_rpow (abs_nonneg _) h1 hp0.le
      linarith
  have htwo : (2 : ℝ) < 2 ^ p := by
    have := Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1 : ℝ) < 2) hp
    simpa using this
  have htp : 0 ≤ t ^ p := Real.rpow_nonneg ht p
  have hlt : cyclicB p t ^ p < (2 * cyclicA p t) ^ p := by
    rw [Real.mul_rpow (by norm_num) (cyclicA_nonneg p ht), cyclicA_rpow hp0 ht, cyclicB_rpow hp0]
    nlinarith
  have hBA : cyclicB p t < 2 * cyclicA p t :=
    (Real.rpow_lt_rpow_iff (cyclicB_nonneg p t)
      (by have := cyclicA_nonneg p ht; positivity) hp0).mp hlt
  linarith

/-! ### The witness `(3/(4p))^{1/p}` -/

/-- The cyclic witness `(3/(4p))^{1/p}`. -/
noncomputable def witness (p : ℝ) : ℝ :=
  Real.exp (-((Real.log p - Real.log (3 / 4)) * p⁻¹))

lemma witness_power {p : ℝ} (hp : 0 < p) :
    witness p ^ p = 3 / 4 * p⁻¹ := by
  rw [witness, Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
  have he : -((Real.log p - Real.log (3 / 4)) * p⁻¹) * p = Real.log (3 / 4) - Real.log p := by
    field_simp
    ring
  rw [he, Real.exp_sub, Real.exp_log hp, Real.exp_log (by norm_num)]
  field_simp

lemma inverse_bounds {p : ℝ} (hp : 50 ≤ p) :
    0 < p⁻¹ ∧ p⁻¹ ≤ 1/50 := by
  exact ⟨inv_pos.mpr (by linarith), by simpa using one_div_le_one_div_of_le (by norm_num) hp⟩

lemma inverse_lower {p : ℝ} (hp : 50 ≤ p) (hhi : p ≤ 62) : 1/62 ≤ p⁻¹ := by
  rw [← one_div]
  exact one_div_le_one_div_of_le (by linarith) hhi

/-- Tangent bound for `log p` at `p = 225/4`, scaled by `1/p`. -/
lemma witness_scaled_tangent {p : ℝ} (hp : 0 < p) :
    (Real.log p - Real.log (3/4)) * p⁻¹ ≤ (3317488114/10^9 : ℝ) * p⁻¹ + 4/225 := by
  have h1 : Real.log (p / (3/4)) = Real.log p - Real.log (3/4) :=
    Real.log_div hp.ne' (by norm_num)
  have h2 := Real.log_le_sub_one_of_pos (show 0 < p / (3/4) / 75 by positivity)
  have h3 : Real.log (p / (3/4) / 75) = Real.log (p / (3/4)) - Real.log 75 :=
    Real.log_div (by positivity) (by norm_num)
  have h4 : Real.log (75 : ℝ) = Real.log 3 + 2 * Real.log 5 := by
    rw [show (75 : ℝ) = 3 * 5 ^ 2 by norm_num, Real.log_mul (by norm_num) (by norm_num),
      Real.log_pow]
    push_cast
    ring
  have h5 : p / (3/4) / 75 = 4/225 * p := by ring
  have hb : Real.log p - Real.log (3/4) ≤ 3317488114/10^9 + 4/225 * p := by
    rw [h3, h1, h4, h5] at h2
    linarith [Real.log_three_lt_d9, Real.log_five_lt_d9]
  have hm := mul_le_mul_of_nonneg_right hb (inv_nonneg.mpr hp.le)
  have he : (3317488114/10^9 + 4/225 * p) * p⁻¹ = (3317488114/10^9 : ℝ) * p⁻¹ + 4/225 := by
    field_simp
  linarith

lemma scaled {p : ℝ} (hp : 50 ≤ p) :
    0 ≤ (Real.log p-Real.log (3/4))*p⁻¹ ∧
    (Real.log p-Real.log (3/4))*p⁻¹ ≤ (3317488114/10^9 : ℝ)*p⁻¹+4/225 ∧
    (3317488114/10^9 : ℝ)*p⁻¹+4/225 < 1/10 := by
  have hi := inverse_bounds hp
  have h0 : 0 ≤ Real.log p-Real.log (3/4) := by
    linarith [Real.log_nonneg (show 1 ≤ p by linarith), log_three_quarters_neg]
  exact ⟨mul_nonneg h0 hi.1.le, witness_scaled_tangent (by linarith), by linarith [hi.2]⟩

lemma witness_bounds {p : ℝ} (hp : 50 ≤ p) :
    1/2 ≤ witness p ∧ witness p ≤ 1 := by
  have hl := scaled hp
  have h := Real.add_one_le_exp (-((Real.log p-Real.log (3/4))*p⁻¹))
  exact ⟨by dsimp [witness]; linarith [hl.2.1,hl.2.2],
    Real.exp_le_one_iff.mpr (neg_nonpos.mpr hl.1)⟩

lemma cyclicA_exp {p : ℝ} (hp : 50 ≤ p) :
    cyclicA p (witness p) = Real.exp (Real.log (2+3/4*p⁻¹)*p⁻¹) := by
  rw [cyclicA, witness_power (by linarith), add_comm,
    Real.rpow_def_of_pos (by positivity)]
  simp only [one_div]

/-! ### Polynomial bounds in `x = 1/p` -/

/-- Lower bound for the cyclic numerator at the witness. -/
noncomputable def Nlo (x : ℝ) : ℝ :=
  let z := (3317488114/10^9 : ℝ)*x+4/225
  let y := (6931471803/10^10+3/8*x-9/64*x^2)*x
  let c := (1098612289/10^9 : ℝ)*x
  3*(1+y+y^2/2)-(1+c+c^2/2+c^3/6+c^4/12)*(1+z-z^2/2+z^3/6+z^4/12)

/-- Upper bound for the cyclic denominator at the witness. -/
noncomputable def Dup (x : ℝ) : ℝ :=
  let t := (6931471808/10^10+3/8*x-9/128*x^2+27/256*x^3)*x
  6*(t+t^2/2+t^3/6+t^4/12)

/-- Lower bound for the envelope deficit. -/
noncomputable def Glo (x : ℝ) : ℝ :=
  let g := (6931471803/10^10-x^2/1000)*x
  g-(6931471808/10^10*x)^2/2+g^3/6-(6931471808/10^10*x)^4/12

set_option maxHeartbeats 4000000 in
/-- Polynomial certificate for the linear lower bound, on `x ∈ [1/62, 1/50]`. -/
theorem linear_certificate {x : ℝ} (hlo : 1/62 ≤ x) (hhi : x ≤ 1/50) :
    (457/1000 : ℝ) * Dup x < x * Nlo x := by
  obtain ⟨s, hs, rfl⟩ : ∃ s, 0 ≤ s ∧ x = 1/62 + s := ⟨x - 1/62, by linarith, by ring⟩
  have hh : s ≤ 3/775 := by linarith
  have p2 := pow_le_pow_left₀ hs hh 2
  have p3 := pow_le_pow_left₀ hs hh 3
  have p4 := pow_le_pow_left₀ hs hh 4
  have p5 := pow_le_pow_left₀ hs hh 5
  have p6 := pow_le_pow_left₀ hs hh 6
  have p7 := pow_le_pow_left₀ hs hh 7
  have p8 := pow_le_pow_left₀ hs hh 8
  have p9 := pow_le_pow_left₀ hs hh 9
  have p10 := pow_le_pow_left₀ hs hh 10
  have p11 := pow_le_pow_left₀ hs hh 11
  have p12 := pow_le_pow_left₀ hs hh 12
  have p13 := pow_le_pow_left₀ hs hh 13
  have p14 := pow_le_pow_left₀ hs hh 14
  have p15 := pow_le_pow_left₀ hs hh 15
  have p16 := pow_le_pow_left₀ hs hh 16
  have q2 := pow_nonneg hs 2
  have q3 := pow_nonneg hs 3
  have q4 := pow_nonneg hs 4
  have q5 := pow_nonneg hs 5
  have q6 := pow_nonneg hs 6
  have q7 := pow_nonneg hs 7
  have q8 := pow_nonneg hs 8
  have q9 := pow_nonneg hs 9
  have q10 := pow_nonneg hs 10
  have q11 := pow_nonneg hs 11
  have q12 := pow_nonneg hs 12
  have q13 := pow_nonneg hs 13
  have q14 := pow_nonneg hs 14
  have q15 := pow_nonneg hs 15
  have q16 := pow_nonneg hs 16
  dsimp only [Dup, Nlo]
  ring_nf
  ring_nf at p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16
  linarith

set_option maxHeartbeats 4000000 in
/-- Polynomial certificate for the envelope comparison, on `x ∈ [1/62, 1/50]`. -/
theorem envelope_certificate {x : ℝ} (hlo : 1/62 ≤ x) (hhi : x ≤ 1/50) :
    (1 - 37/100 : ℝ) * Dup x < Nlo x * (2 * Glo x) := by
  obtain ⟨s, hs, rfl⟩ : ∃ s, 0 ≤ s ∧ x = 1/62 + s := ⟨x - 1/62, by linarith, by ring⟩
  have hh : s ≤ 3/775 := by linarith
  have p2 := pow_le_pow_left₀ hs hh 2
  have p3 := pow_le_pow_left₀ hs hh 3
  have p4 := pow_le_pow_left₀ hs hh 4
  have p5 := pow_le_pow_left₀ hs hh 5
  have p6 := pow_le_pow_left₀ hs hh 6
  have p7 := pow_le_pow_left₀ hs hh 7
  have p8 := pow_le_pow_left₀ hs hh 8
  have p9 := pow_le_pow_left₀ hs hh 9
  have p10 := pow_le_pow_left₀ hs hh 10
  have p11 := pow_le_pow_left₀ hs hh 11
  have p12 := pow_le_pow_left₀ hs hh 12
  have p13 := pow_le_pow_left₀ hs hh 13
  have p14 := pow_le_pow_left₀ hs hh 14
  have p15 := pow_le_pow_left₀ hs hh 15
  have p16 := pow_le_pow_left₀ hs hh 16
  have p17 := pow_le_pow_left₀ hs hh 17
  have q2 := pow_nonneg hs 2
  have q3 := pow_nonneg hs 3
  have q4 := pow_nonneg hs 4
  have q5 := pow_nonneg hs 5
  have q6 := pow_nonneg hs 6
  have q7 := pow_nonneg hs 7
  have q8 := pow_nonneg hs 8
  have q9 := pow_nonneg hs 9
  have q10 := pow_nonneg hs 10
  have q11 := pow_nonneg hs 11
  have q12 := pow_nonneg hs 12
  have q13 := pow_nonneg hs 13
  have q14 := pow_nonneg hs 14
  have q15 := pow_nonneg hs 15
  have q16 := pow_nonneg hs 16
  have q17 := pow_nonneg hs 17
  dsimp only [Dup, Nlo, Glo]
  ring_nf
  ring_nf at p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17
  linarith

/-! ### Bounds at the witness -/

set_option maxHeartbeats 4000000 in
lemma numerator_lower {p : ℝ} (hp : 50 ≤ p) :
    Nlo p⁻¹ ≤ 3*cyclicA p (witness p)-(3 : ℝ)^(1/p)*|2-witness p| := by
  set x := p⁻¹ with hxdef
  have hi := inverse_bounds hp
  have hx0 : 0 ≤ x := hi.1.le
  have ht := witness_bounds hp
  have hl := scaled hp
  let C : ℝ := 1098612289/10^9*x
  let Z : ℝ := 3317488114/10^9*x+4/225
  have hc0 : 0 ≤ C := by dsimp [C]; positivity
  have hc1 : C ≤ 1 := by dsimp [C]; linarith [hi.2]
  have hz0 : 0 ≤ Z := by dsimp [Z]; positivity
  have hz1 : Z ≤ 1 := by dsimp [Z]; linarith [hl.2.2]
  have hroot : (3 : ℝ)^(1/p) = Real.exp (Real.log 3*x) := by
    rw [Real.rpow_def_of_pos (by norm_num), one_div]
  have hc : Real.log 3*x ≤ C := by
    apply mul_le_mul_of_nonneg_right _ hx0
    linarith [Real.log_three_lt_d9]
  have hr := (Real.exp_le_exp.mpr hc).trans (exp_quartic hc0 hc1)
  have hw : Real.exp (-Z) ≤ witness p := by
    apply Real.exp_le_exp.mpr
    dsimp [Z]
    linarith [hl.2.1]
  have htup : 2-witness p ≤ 1+Z-Z^2/2+Z^3/6+Z^4/12 := by
    have h := exp_neg_quartic_lower hz0 hz1
    linarith
  have habs : |2-witness p| = 2-witness p := abs_of_nonneg (by linarith [ht.2])
  have hprod := mul_le_mul hr htup (show 0 ≤ 2-witness p by linarith [ht.2])
    (show 0 ≤ 1+C+C^2/2+C^3/6+C^4/12 by positivity)
  have ha := log_two_add (show 0 ≤ 3/4*x by positivity)
  have hA := Real.quadratic_le_exp_of_nonneg
    (mul_nonneg (Real.log_nonneg (by linarith : (1 : ℝ) ≤ 2+3/4*x)) hx0)
  rw [← cyclicA_exp hp] at hA
  have hy0 : 0 ≤ (6931471803/10^10+3/4*x/2-(3/4*x)^2/4)*x := by
    apply mul_nonneg _ hx0
    nlinarith [hi.2]
  have hyy := mul_le_mul_of_nonneg_right ha hx0
  have hAmono : 1+(6931471803/10^10+3/4*x/2-(3/4*x)^2/4)*x+
      ((6931471803/10^10+3/4*x/2-(3/4*x)^2/4)*x)^2/2 ≤
      1+Real.log (2+3/4*x)*x+(Real.log (2+3/4*x)*x)^2/2 := by
    have h2 := pow_le_pow_left₀ hy0 hyy 2
    linarith
  rw [hroot,habs]
  dsimp [Nlo,C,Z] at hprod ⊢
  nlinarith

set_option maxHeartbeats 4000000 in
lemma denominator_upper {p : ℝ} (hp : 50 ≤ p) :
    6*cyclicA p (witness p)-3*cyclicB p (witness p) ≤ Dup p⁻¹ := by
  set x := p⁻¹ with hxdef
  have hi := inverse_bounds hp
  have hx0 : 0 ≤ x := hi.1.le
  have hk0 : 0 ≤ 3/4*x := by positivity
  have hk1 : 3/4*x ≤ 1 := by linarith [hi.2]
  have ha := log_two_add_upper hk0 hk1
  have hy0 : 0 ≤ Real.log (2+3/4*x)*x :=
    mul_nonneg (Real.log_nonneg (by linarith)) hx0
  let T : ℝ := (6931471808/10^10+3/8*x-9/128*x^2+27/256*x^3)*x
  have hyy : Real.log (2+3/4*x)*x ≤ T := by
    have h := mul_le_mul_of_nonneg_right ha hx0
    dsimp [T]
    nlinarith
  have ht0 : 0 ≤ T := hy0.trans hyy
  have hx2 := pow_le_pow_left₀ hx0 hi.2 2
  have hx3 := pow_le_pow_left₀ hx0 hi.2 3
  have ht1 : T ≤ 1 := by
    dsimp [T]
    have hinner : 6931471808/10^10+3/8*x-9/128*x^2+27/256*x^3 ≤ 1 := by
      nlinarith [sq_nonneg x]
    have h := mul_le_mul_of_nonneg_right hinner hx0
    nlinarith [hi.2]
  have hE := (Real.exp_le_exp.mpr hyy).trans (exp_quartic ht0 ht1)
  rw [← cyclicA_exp hp] at hE
  have hB := cyclicB_ge_two (t := witness p) (show 0 < p by linarith)
  dsimp [Dup,T] at hE ⊢
  linarith

lemma Dup_pos {x : ℝ} (hx : 0 < x) (hhi : x ≤ 1/50) : 0 < Dup x := by
  have hx2 := pow_le_pow_left₀ hx.le hhi 2
  have h : 0 < 6931471808/10^10+3/8*x-9/128*x^2+27/256*x^3 := by
    nlinarith [pow_nonneg hx.le 3]
  dsimp [Dup]
  positivity

lemma Nlo_pos {x : ℝ} (hlo : 1/62 ≤ x) (hhi : x ≤ 1/50) : 0 < Nlo x := by
  have hx : 0 < x := by linarith
  have hc := linear_certificate hlo hhi
  have hd := Dup_pos hx hhi
  nlinarith

lemma Glo_pos {x : ℝ} (hlo : 1/62 ≤ x) (hhi : x ≤ 1/50) : 0 < Glo x := by
  have hx : 0 < x := by linarith
  have hx2 := pow_le_pow_left₀ hx.le hhi 2
  have hx4 := pow_le_pow_left₀ hx.le hhi 4
  have hg : 0 ≤ (6931471803/10^10-x^2/1000)*x := by
    apply mul_nonneg _ hx.le
    nlinarith
  dsimp [Glo]
  nlinarith [pow_nonneg hg 3]

/-! ### Upper bound `cyclicRatio ≤ p/2` -/

lemma cyclicA_lower {p t : ℝ} (hp : 0 < p) (ht : 0 ≤ t) :
    1 + (693 / 1000 : ℝ) / p ≤ cyclicA p t := by
  have hlog : (693 / 1000 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have he := Real.add_one_le_exp (Real.log 2 * (1 / p))
  have hr : 1 + (693 / 1000 : ℝ) / p ≤ (2 : ℝ) ^ (1 / p) := by
    rw [Real.rpow_def_of_pos (by norm_num)]
    have hm := mul_le_mul_of_nonneg_right hlog (one_div_nonneg.mpr hp.le)
    simp only [div_eq_mul_inv, one_mul] at he hm ⊢
    linarith
  exact hr.trans (Real.rpow_le_rpow (by norm_num)
    (by linarith [Real.rpow_nonneg ht p])
    (one_div_nonneg.mpr hp.le))

lemma cyclicB_upper {p t : ℝ} (hp : 50 ≤ p) (ht : t ∈ Set.Icc (1 / 2) 2) :
    cyclicB p t ≤ 2 + (1 / p) / 1000000 := by
  have hp0 : 0 < p := by linarith
  have hx0 : 0 ≤ 1 / p := by positivity
  have hx1 : 1 / p ≤ 1 := (div_le_iff₀ hp0).mpr (by linarith)
  have habs : |1-t| ≤ 1 := abs_le.mpr ⟨by linarith [ht.2], by linarith [ht.1]⟩
  have hpow : (2 : ℝ) ^ p ≥ 4194304 := by
    have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
      (show (22 : ℝ) ≤ p by linarith)
    norm_num at h
    linarith
  have htwo : 0 < (2 : ℝ) ^ p := Real.rpow_pos_of_pos (by norm_num) _
  have htail : 4 / (2 : ℝ) ^ p ≤ 1 / 1000000 := by
    rw [div_le_iff₀ htwo]
    linarith
  have hb : cyclicB p t ≤ (2 + (2 : ℝ) ^ p) ^ (1 / p) := by
    apply Real.rpow_le_rpow (by positivity) _ hx0
    have h := Real.rpow_le_rpow (abs_nonneg _) habs hp0.le
    simp only [Real.one_rpow] at h
    linarith
  have heq : (2 + (2 : ℝ) ^ p) ^ (1 / p) =
      2 * (1 + 2 / (2 : ℝ) ^ p) ^ (1 / p) := by
    rw [show 2 + (2 : ℝ) ^ p = (2 : ℝ) ^ p * (1 + 2 / (2 : ℝ) ^ p) by
      field_simp; ring,
      Real.mul_rpow htwo.le (by positivity), ← Real.rpow_mul (by norm_num),
      mul_one_div_cancel hp0.ne', Real.rpow_one]
  have hconc := rpow_one_add_le_one_add_mul_self
    (s := 2 / (2 : ℝ) ^ p)
    (by linarith [div_nonneg (by norm_num : (0 : ℝ) ≤ 2) htwo.le]) hx0 hx1
  rw [heq] at hb
  have hm := mul_le_mul_of_nonneg_left hconc (by norm_num : (0 : ℝ) ≤ 2)
  have ht0 := mul_le_mul_of_nonneg_right htail hx0
  have halg : 2 * (1 + (1/p) * (2 / (2 : ℝ) ^ p)) =
      2 + (4 / (2 : ℝ) ^ p) * (1/p) := by ring
  rw [halg] at hm
  nlinarith

lemma cyclicRatio_le_half_exponent {p t : ℝ} (hp : 50 ≤ p)
    (ht : t ∈ Set.Icc (1 / 2) 2) : cyclicRatio p t ≤ p / 2 := by
  have hp0 : 0 < p := by linarith
  have ht0 : 0 ≤ t := by linarith [ht.1]
  have hden := denominator_pos (show 1 < p by linarith) ht0
  have hA := cyclicA_lower (t := t) hp0 ht0
  have hB := cyclicB_upper hp ht
  have hthree : 1 ≤ (3 : ℝ) ^ (1/p) := Real.one_le_rpow (by norm_num) (by positivity)
  have hnum : 3 * cyclicA p t - (3 : ℝ) ^ (1/p) * |2-t| ≤ 4 * cyclicA p t - 2 := by
    have htA : t ≤ cyclicA p t := by
      have h := Real.rpow_le_rpow (Real.rpow_nonneg ht0 p)
        (show t ^ p ≤ t ^ p + 2 by linarith) (one_div_nonneg.mpr hp0.le)
      rw [← Real.rpow_mul ht0, mul_one_div_cancel hp0.ne', Real.rpow_one] at h
      exact h
    have h := mul_le_mul_of_nonneg_right hthree (abs_nonneg (2-t))
    rw [abs_of_nonneg (by linarith [ht.2])] at h
    rw [abs_of_nonneg (by linarith [ht.2])]
    nlinarith
  have hpx : p * (1/p) = 1 := mul_one_div_cancel hp0.ne'
  have hAl := mul_le_mul_of_nonneg_left hA (show 0 ≤ 3*p-4 by linarith)
  have hBu := mul_le_mul_of_nonneg_left hB (show 0 ≤ 3*p/2 by positivity)
  have hx : 1 / p ≤ 1 / 50 := one_div_le_one_div_of_le (by norm_num) hp
  have hfinal : 4 * cyclicA p t - 2 ≤ (p/2) * (6 * cyclicA p t - 3 * cyclicB p t) := by
    simp only [div_eq_mul_inv, one_mul] at hAl hBu hpx hx ⊢
    nlinarith
  exact (div_le_iff₀ hden).mpr (hnum.trans hfinal)

lemma cyclicRatio_bddAbove {p : ℝ} (hp : 50 ≤ p) :
    BddAbove (cyclicRatio p '' Set.Icc (1 / 2 : ℝ) 2) := by
  refine ⟨p / 2, ?_⟩
  rintro _ ⟨t, ht, rfl⟩
  exact cyclicRatio_le_half_exponent hp ht

lemma cyclicRatio_le_constant {p t : ℝ} (hp : 50 ≤ p)
    (ht : t ∈ Set.Icc (1 / 2 : ℝ) 2) : cyclicRatio p t ≤ cyclicConstant p :=
  le_csSup (cyclicRatio_bddAbove hp) (Set.mem_image_of_mem (cyclicRatio p) ht)

lemma cyclicConstant_le_half_exponent {p : ℝ} (hp : 50 ≤ p) :
    cyclicConstant p ≤ p / 2 := by
  apply csSup_le
  · exact ⟨cyclicRatio p 1, Set.mem_image_of_mem _ ⟨by norm_num, by norm_num⟩⟩
  · rintro _ ⟨t, ht, rfl⟩
    exact cyclicRatio_le_half_exponent hp ht

/-! ### The two lower bounds -/

lemma cyclicConstant_gt_linear {p : ℝ} (hp : 50 ≤ p) (hp' : p ≤ 62) :
    (457 / 1000 : ℝ) * p < cyclicConstant p := by
  have hp0 : 0 < p := by linarith
  have hi := inverse_bounds hp
  have hi' := inverse_lower hp hp'
  have ht := witness_bounds hp
  have hD := denominator_pos (show 1 < p by linarith)
    (show 0 ≤ witness p by linarith [ht.1])
  have hn := numerator_lower hp
  have hd := denominator_upper hp
  have hc := linear_certificate hi' hi.2
  have hpi : p * p⁻¹ = 1 := mul_inv_cancel₀ hp0.ne'
  have hr : (457 / 1000 : ℝ) * p < cyclicRatio p (witness p) := by
    rw [cyclicRatio, lt_div_iff₀ hD]
    have hcp := mul_lt_mul_of_pos_left hc hp0
    have hdp := mul_le_mul_of_nonneg_left hd (show (0 : ℝ) ≤ 457 / 1000 * p by positivity)
    have : p * (p⁻¹ * Nlo p⁻¹) = Nlo p⁻¹ := by
      rw [← mul_assoc, hpi, one_mul]
    nlinarith
  exact hr.trans_le (cyclicRatio_le_constant hp ⟨ht.1, by linarith [ht.2]⟩)

lemma power_tail {p : ℝ} (hp : 50 ≤ p) (hp' : p ≤ 62) :
    (37/100 : ℝ) ^ p < (p⁻¹) ^ 2 / 1000 := by
  have hp0 : 0 < p := by linarith
  have h := one_add_mul_self_le_rpow_one_add (s := (1 : ℝ)) (by norm_num)
    (show 1 ≤ p - 20 by linarith)
  norm_num at h
  have heq : (2 : ℝ) ^ p = 1048576 * (2 : ℝ) ^ (p - 20) := by
    rw [show p = (p - 20) + 20 by ring, Real.rpow_add (by norm_num)]
    norm_num
    ring
  have htwo : 1000 * p ^ 2 < (2 : ℝ) ^ p := by rw [heq]; nlinarith
  calc
    (37/100 : ℝ) ^ p ≤ (1 / 2 : ℝ) ^ p :=
      Real.rpow_le_rpow (by norm_num) (by norm_num) hp0.le
    _ = ((2 : ℝ) ^ p)⁻¹ := by rw [one_div, Real.inv_rpow (by norm_num)]
    _ < (1000 * p ^ 2)⁻¹ := inv_strictAnti₀ (by positivity) htwo
    _ = (p⁻¹) ^ 2 / 1000 := by field_simp

lemma envelope_deficit {p : ℝ} (hp : 50 ≤ p) (hp' : p ≤ 62) :
    Glo p⁻¹ < 1-scalarEnvelopeRoot p (37/100) := by
  have hi := inverse_bounds hp
  set x := p⁻¹ with hxdef
  let a := (37/100 : ℝ)^p
  have ha0 : 0 ≤ a := Real.rpow_nonneg (by norm_num) p
  have ha : a < x^2/1000 := power_tail hp hp'
  let d := Real.log 2-Real.log (1+a)
  have hdLower : Real.log 2-x^2/1000 < d := by
    have h := Real.log_le_sub_one_of_pos (show 0 < 1+a by positivity)
    dsimp [d]
    linarith
  have hdUpper : d ≤ Real.log 2 := by
    have h := Real.log_nonneg (show 1 ≤ 1+a by linarith)
    dsimp [d]
    linarith
  have hL : (6931471803/10^10 : ℝ) < Real.log 2 ∧ Real.log 2 <6931471808/10^10 := by
    constructor <;> linarith [Real.log_two_gt_d9,Real.log_two_lt_d9]
  have hx2 : x^2/1000 ≤ 1/1000 := by nlinarith [hi.1,hi.2]
  have hd0 : 0 ≤ d := by linarith [hL.1]
  have hdx0 : 0 ≤ d*x := mul_nonneg hd0 hi.1.le
  have hdx1 : d*x ≤ 1 := by nlinarith [hL.2,hi.2]
  have he := one_sub_exp_neg_quartic hdx0 hdx1
  have hdx : d*x ≤ 6931471808/10^10*x :=
    mul_le_mul_of_nonneg_right (by linarith) hi.1.le
  have hsq := pow_le_pow_left₀ hdx0 hdx 2
  have hfour := pow_le_pow_left₀ hdx0 hdx 4
  have hgl : (6931471803/10^10-x^2/1000)*x < d*x :=
    mul_lt_mul_of_pos_right (by linarith) hi.1
  have hg0 : 0 ≤ (6931471803/10^10-x^2/1000)*x := by
    apply mul_nonneg _ hi.1.le
    linarith [hL.1]
  have hcube := pow_le_pow_left₀ hg0 hgl.le 3
  have hroot : scalarEnvelopeRoot p (37/100) = Real.exp (-(d*x)) := by
    rw [scalarEnvelopeRoot, Real.rpow_def_of_pos (by positivity),
      Real.log_div (by positivity) (by norm_num)]
    congr 1
    dsimp [d,a]
    simp only [one_div,hxdef]
    ring
  rw [hroot]
  dsimp [Glo]
  linarith

lemma envelope_lt {p : ℝ} (hp : 50 ≤ p) (hp' : p ≤ 62) :
    scalarEnvelope p (37/100) < cyclicConstant p := by
  have hi := inverse_bounds hp
  have hi' := inverse_lower hp hp'
  have ht := witness_bounds hp
  have hD := denominator_pos (show 1 < p by linarith)
    (show 0 ≤ witness p by linarith [ht.1])
  have hn := numerator_lower hp
  have hd := denominator_upper hp
  have hg := envelope_deficit hp hp'
  have hc := envelope_certificate hi' hi.2
  have hN0 := Nlo_pos hi' hi.2
  have hG0 := Glo_pos hi' hi.2
  have henvD : 0 < 2 * (1 - scalarEnvelopeRoot p (37/100)) := by linarith
  have hr : scalarEnvelope p (37/100) < cyclicRatio p (witness p) := by
    rw [scalarEnvelope, cyclicRatio, div_lt_div_iff₀ henvD hD]
    calc
      _ ≤ (1 - (37/100 : ℝ)) * Dup p⁻¹ :=
        mul_le_mul_of_nonneg_left hd (by norm_num)
      _ < Nlo p⁻¹ * (2 * Glo p⁻¹) := hc
      _ ≤ (3 * cyclicA p (witness p) -
          (3 : ℝ) ^ (1 / p) * |2 - witness p|) *
          (2 * (1 - scalarEnvelopeRoot p (37/100))) :=
        mul_le_mul hn (by linarith) (by linarith) (hN0.le.trans hn)
  exact hr.trans_le (cyclicRatio_le_constant hp ⟨ht.1, by linarith [ht.2]⟩)

end HlawkaSchatten.DiagonalCutoff50

open HlawkaSchatten HlawkaSchatten.DiagonalConstruction

theorem HlawkaSchatten.DiagonalCutoff50.scalar_window50 : ∀ p : ℝ, 50 ≤ p → p ≤ 62 →
    (457 / 1000 : ℝ) * p < cyclicConstant p ∧
    scalarEnvelope p (37 / 100) < cyclicConstant p ∧
    cyclicConstant p ≤ p / 2 := by
  intro p hp hp'
  exact ⟨HlawkaSchatten.DiagonalCutoff50.cyclicConstant_gt_linear hp hp',
    HlawkaSchatten.DiagonalCutoff50.envelope_lt hp hp',
    HlawkaSchatten.DiagonalCutoff50.cyclicConstant_le_half_exponent hp⟩

set_option autoImplicit false

namespace Hl50LocGeometry
open HlawkaSchatten.DiagonalConstruction

/-- Target box (scaled by 3): diagonal in [-111/100, -6894/10000],
off-diagonal in [8091/10000, 111/100]. -/
def asymmetricBox : Set Triple := {X | ∀ j i,
  if j = i then -(111 / 100 : ℝ) ≤ X j i ∧ X j i ≤ -(6894 / 10000 : ℝ)
  else (8091 / 10000 : ℝ) ≤ X j i ∧ X j i ≤ (111 / 100 : ℝ)}

/-- Coarse box for the unscaled oriented triple. -/
def coarseBox : Set Triple := {X | ∀ j i,
  if j = i then -(37 / 100 : ℝ) ≤ X j i ∧ X j i ≤ -(4 / 25 : ℝ)
  else (21 / 100 : ℝ) ≤ X j i ∧ X j i ≤ (37 / 100 : ℝ)}

/-- With column total at most A = 111/100 and pair deficit delta = 453/5000, each
scaled singleton norm exceeds (3 - A - delta)/2, which tightens every entry. -/
theorem asymmetricBox_of_norm_data (X : Triple) (N : Fin 3 → ℝ)
    (hS : ∑ j, N j = 3) (hN : ∀ j, N j ≤ 111 / 100)
    (hcoord : ∀ j i, |X j i| ≤ N j)
    (hT : ∀ i, ∑ j, X j i ≤ 111 / 100)
    (hpair : ∀ i, 3 - N i - (453 / 5000 : ℝ) ≤ (∑ j, X j i) - X i i) :
    X ∈ asymmetricBox := by
  have hlow : ∀ i, (3 - 111 / 100 - 453 / 5000 : ℝ) / 2 ≤ N i := by
    intro i
    have h1 := hT i
    have h2 := hpair i
    have h3 := abs_le.mp (hcoord i i)
    linarith
  simp only [Fin.sum_univ_three] at hS hT hpair
  intro j i
  have hc0 := abs_le.mp (hcoord 0 i)
  have hc1 := abs_le.mp (hcoord 1 i)
  have hc2 := abs_le.mp (hcoord 2 i)
  have hl0 := hlow 0
  have hl1 := hlow 1
  have hl2 := hlow 2
  have hn0 := hN 0
  have hn1 := hN 1
  have hn2 := hN 2
  have ht := hT i
  have hp := hpair i
  fin_cases j <;> fin_cases i <;> simp at hc0 hc1 hc2 ht hp ⊢ <;> constructor <;> linarith

end Hl50LocGeometry

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Hl50LocLocalization
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction
open Hl50LocGeometry (asymmetricBox)

variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E]


theorem lpNorm_nonneg (p : ℝ) (x : ι → E) : 0 ≤ lpNorm p x :=
  Real.rpow_nonneg (Finset.sum_nonneg fun _ _ ↦ Real.rpow_nonneg (norm_nonneg _) _) _


theorem lpNorm_eq_piLp {p : ℝ} (hp : 0 < p) (x : ι → E) :
    lpNorm p x = ‖WithLp.toLp (ENNReal.ofReal p) x‖ := by
  rw [PiLp.norm_eq_sum (by simpa only [ENNReal.toReal_ofReal hp.le] using hp)]
  simp [lpNorm, ENNReal.toReal_ofReal hp.le]

@[simp]

theorem lpNorm_zero {p : ℝ} (hp : 0 < p) : lpNorm p (0 : ι → E) = 0 := by
  simp [lpNorm, hp.ne']

@[simp]

theorem lpNorm_neg (p : ℝ) (x : ι → E) : lpNorm p (-x) = lpNorm p x := by
  simp [lpNorm]


theorem lpNorm_add {p : ℝ} (hp : 1 ≤ p) (x y : ι → E) :
    lpNorm p (x + y) ≤ lpNorm p x + lpNorm p y := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  let : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr hp⟩
  simpa only [lpNorm_eq_piLp hp0, ← WithLp.toLp_add] using
    norm_add_le (WithLp.toLp (ENNReal.ofReal p) x) (WithLp.toLp (ENNReal.ofReal p) y)


theorem norm_apply_le_lpNorm {p : ℝ} (hp : 1 ≤ p) (x : ι → E) (i : ι) :
    ‖x i‖ ≤ lpNorm p x := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  let : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr hp⟩
  rw [lpNorm_eq_piLp hp0]
  exact PiLp.norm_apply_le (WithLp.toLp (ENNReal.ofReal p) x) i



/-- The two non-dominant coordinates retain their positive power contribution. -/
theorem norm_le_dominant_with_tail {p : ℝ} (hp : 1 < p)
    (v : Fin 3 → ℝ) (k : Fin 3) (hm : 0 ≤ v k)
    (hsmall : ∀ i, i ≠ k → |v i| ≤ v k * (5 / 6)) :
    lpNorm p v ≤ v k * (1 + 2 * (5 / 6 : ℝ) ^ p / p) := by
  have hp0 : 0 < p := by linarith
  have hpow (i : Fin 3) (hi : i ≠ k) :
      |v i| ^ p ≤ (v k) ^ p * (5 / 6 : ℝ) ^ p := by
    have h := Real.rpow_le_rpow (abs_nonneg (v i)) (hsmall i hi) hp0.le
    rw [Real.mul_rpow hm (by norm_num)] at h
    exact h
  have hsum : (∑ i, |v i| ^ p) ≤ (v k) ^ p * (1 + 2 * (5 / 6 : ℝ) ^ p) := by
    fin_cases k
    · change 0 ≤ v 0 at hm
      have hleft : |v 1| ^ p ≤ v 0 ^ p * (5 / 6 : ℝ) ^ p := hpow 1 (by decide)
      have hright : |v 2| ^ p ≤ v 0 ^ p * (5 / 6 : ℝ) ^ p := hpow 2 (by decide)
      simp only [Fin.sum_univ_three]
      change |v 0| ^ p + |v 1| ^ p + |v 2| ^ p ≤ v 0 ^ p * (1 + 2 * (5 / 6 : ℝ) ^ p)
      rw [abs_of_nonneg hm]
      nlinarith
    · change 0 ≤ v 1 at hm
      have hleft : |v 0| ^ p ≤ v 1 ^ p * (5 / 6 : ℝ) ^ p := hpow 0 (by decide)
      have hright : |v 2| ^ p ≤ v 1 ^ p * (5 / 6 : ℝ) ^ p := hpow 2 (by decide)
      simp only [Fin.sum_univ_three]
      change |v 0| ^ p + |v 1| ^ p + |v 2| ^ p ≤ v 1 ^ p * (1 + 2 * (5 / 6 : ℝ) ^ p)
      rw [abs_of_nonneg hm]
      nlinarith
    · change 0 ≤ v 2 at hm
      have hleft : |v 0| ^ p ≤ v 2 ^ p * (5 / 6 : ℝ) ^ p := hpow 0 (by decide)
      have hright : |v 1| ^ p ≤ v 2 ^ p * (5 / 6 : ℝ) ^ p := hpow 1 (by decide)
      simp only [Fin.sum_univ_three]
      change |v 0| ^ p + |v 1| ^ p + |v 2| ^ p ≤ v 2 ^ p * (1 + 2 * (5 / 6 : ℝ) ^ p)
      rw [abs_of_nonneg hm]
      nlinarith
  have hnorm := Real.rpow_le_rpow
    (Finset.sum_nonneg fun i _ ↦ Real.rpow_nonneg (abs_nonneg (v i)) p)
    hsum (one_div_nonneg.mpr hp0.le)
  rw [Real.mul_rpow (Real.rpow_nonneg hm _) (by positivity),
    ← Real.rpow_mul hm, mul_one_div_cancel hp0.ne', Real.rpow_one] at hnorm
  have hroot := rpow_one_add_le_one_add_mul_self
    (s := 2 * (5 / 6 : ℝ) ^ p) (p := 1 / p) (by have h := Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ 5/6) p; linarith)
    (by positivity) (by simpa using (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hp.le))
  have hmul := mul_le_mul_of_nonneg_left hroot hm
  change lpNorm p v ≤ _ at hnorm
  calc
    _ ≤ v k * (1 + 1 / p * (2 * (5 / 6 : ℝ) ^ p)) := hnorm.trans hmul
    _ = _ := by ring


/-- The strict pair gap absorbs a uniformly bounded, nonzero tail. -/
theorem pair_coordinate_deficit {p : ℝ} (hp : 50 ≤ p)
    (x y : Fin 3 → ℝ) (k : Fin 3)
    (hx : lpNorm p x ≤ 37/100) (hy : lpNorm p y ≤ 37/100)
    (hgap : pairGap (lpNorm p) x y < 3 / (2 * p))
    (hm : 0 ≤ x k + y k)
    (hsmall : ∀ i, i ≠ k → |x i + y i| ≤ (5 / 6) * (x k + y k)) :
    lpNorm p x + lpNorm p y - (x k + y k) < 151 / (100 * p) := by
  have hp0 : 0 < p := by linarith
  have hp1 : 1 ≤ p := by linarith
  have ha : (5 / 6 : ℝ) ^ p ≤ 1 / 8000 := by
    have hpow : (5 / 6 : ℝ) ^ p ≤ (5 / 6) ^ (50 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) (by linarith)
    have h50 : (5 / 6 : ℝ) ^ (50 : ℝ) < 1 / 8000 := by
      have h50real : (5 / 6 : ℝ) ^ (50 : ℝ) = (5 / 6) ^ (50 : ℕ) := Real.rpow_natCast _ _
      rw [h50real]
      norm_num
    exact hpow.trans h50.le
  have hsmall' : ∀ i, i ≠ k → |(x + y) i| ≤ (x + y) k * (5 / 6) := by
    intro i hi
    simpa [Pi.add_apply, mul_comm] using hsmall i hi
  have hnorm := norm_le_dominant_with_tail (by linarith : 1 < p) (x + y) k hm hsmall'
  have hm' : x k + y k ≤ 74/100 := by
    have hxk := (le_abs_self (x k)).trans (norm_apply_le_lpNorm hp1 x k)
    have hyk := (le_abs_self (y k)).trans (norm_apply_le_lpNorm hp1 y k)
    linarith
  have ht0 : 0 ≤ 2 * (5 / 6 : ℝ) ^ p / p := by positivity
  have ht : 2 * (5 / 6 : ℝ) ^ p / p ≤ 1 / (4000 * p) := by
    apply (mul_le_mul_iff_left₀ hp0).mp
    field_simp
    linarith [ha]
  have hm1 := mul_le_mul_of_nonneg_left ht hm
  have hm2 := mul_le_mul_of_nonneg_right hm' (show 0 ≤ 1 / (4000 * p) by positivity)
  have htail : (74/100 : ℝ) * (1 / (4000 * p)) < 1 / (600 * p) := by
    apply (mul_lt_mul_iff_left₀ hp0).mp
    field_simp
    norm_num
  change lpNorm p (x + y) ≤ (x k + y k) * (1 + 2 * (5 / 6 : ℝ) ^ p / p) at hnorm
  have hE : 3 / (2 * p) + 1 / (600 * p) < 151 / (100 * p) := by
    apply (mul_lt_mul_iff_left₀ hp0).mp
    field_simp
    norm_num
  dsimp only [pairGap] at hgap
  nlinarith


/-- A coarse asymmetric box is sufficient for the refined coordinate estimate. -/
theorem coarse_pair_dominance (X : Triple)
    (hbox : X ∈ Hl50LocGeometry.coarseBox)
    (a b k : Fin 3) (hab : a ≠ b) (hak : a ≠ k) (hbk : b ≠ k) :
    0 ≤ X a k + X b k ∧
      ∀ i, i ≠ k → |X a i + X b i| ≤ (5 / 6) * (X a k + X b k) := by
  have hak' := hbox a k
  have hbk' := hbox b k
  simp only [if_neg hak, if_neg hbk] at hak' hbk'
  refine ⟨by linarith, ?_⟩
  intro i hik
  have ha := hbox a i
  have hb := hbox b i
  have hie : i = a ∨ i = b := by
    fin_cases a <;> fin_cases b <;> fin_cases k <;> fin_cases i <;> simp_all
  rcases hie with rfl | rfl
  · simp only [ite_true, if_neg (Ne.symm hab)] at ha hb
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  · simp only [ite_true, if_neg hab] at ha hb
    exact abs_le.mpr ⟨by linarith, by linarith⟩


/-- The second localization stage keeps the orientation fixed. -/
theorem bootstrap50 {p : ℝ} (hp : 50 ≤ p) (x y z : Fin 3 → ℝ)
    (hS : lpNorm p x + lpNorm p y + lpNorm p z = 1)
    (hx : lpNorm p x ≤ 37/100) (hy : lpNorm p y ≤ 37/100) (hz : lpNorm p z ≤ 37/100)
    (hT : lpNorm p (x+y+z) ≤ 37/100)
    (hgap : pairGapSum (lpNorm p) x y z < 3/(2*p))
    (hbox : (![x,y,z] : Triple) ∈ Hl50LocGeometry.coarseBox) :
    ![(3 : ℝ) • x, (3 : ℝ) • y, (3 : ℝ) • z] ∈ asymmetricBox := by
  have hp1 : 1 ≤ p := by linarith
  have hxy0 : 0 ≤ pairGap (lpNorm p) x y := sub_nonneg.mpr (lpNorm_add hp1 x y)
  have hxz0 : 0 ≤ pairGap (lpNorm p) x z := sub_nonneg.mpr (lpNorm_add hp1 x z)
  have hyz0 : 0 ≤ pairGap (lpNorm p) y z := sub_nonneg.mpr (lpNorm_add hp1 y z)
  have hxy := coarse_pair_dominance ![x,y,z] hbox 0 1 2 (by decide) (by decide) (by decide)
  have hxz := coarse_pair_dominance ![x,y,z] hbox 0 2 1 (by decide) (by decide) (by decide)
  have hyz := coarse_pair_dominance ![x,y,z] hbox 1 2 0 (by decide) (by decide) (by decide)
  dsimp only [pairGapSum] at hgap
  have hxyE := pair_coordinate_deficit hp x y 2 hx hy (by linarith) hxy.1 hxy.2
  have hxzE := pair_coordinate_deficit hp x z 1 hx hz (by linarith) hxz.1 hxz.2
  have hyzE := pair_coordinate_deficit hp y z 0 hy hz (by linarith) hyz.1 hyz.2
  have hE : 151/(100*p) ≤ (151/5000 : ℝ) := by
    rw [div_le_iff₀ (by positivity)]
    linarith
  have hxi (i : Fin 3) := abs_le.mp (norm_apply_le_lpNorm hp1 x i)
  have hyi (i : Fin 3) := abs_le.mp (norm_apply_le_lpNorm hp1 y i)
  have hzi (i : Fin 3) := abs_le.mp (norm_apply_le_lpNorm hp1 z i)
  have ht (i : Fin 3) : x i+y i+z i ≤ 37/100 :=
    ((le_abs_self _).trans (norm_apply_le_lpNorm hp1 (x+y+z) i)).trans hT
  apply Hl50LocGeometry.asymmetricBox_of_norm_data
    ![(3 : ℝ) • x, (3 : ℝ) • y, (3 : ℝ) • z]
    ![3*lpNorm p x, 3*lpNorm p y, 3*lpNorm p z]
  · rw [Fin.sum_univ_three]
    change 3*lpNorm p x + 3*lpNorm p y + 3*lpNorm p z = 3
    linarith
  · intro j
    fin_cases j <;> norm_num <;> linarith
  · intro j i
    fin_cases j <;> simp [Pi.smul_apply, smul_eq_mul, abs_mul]
    all_goals first
    | exact norm_apply_le_lpNorm hp1 x i
    | exact norm_apply_le_lpNorm hp1 y i
    | exact norm_apply_le_lpNorm hp1 z i
  · intro i
    rw [Fin.sum_univ_three]
    change 3*x i+3*y i+3*z i ≤ (111/100 : ℝ)
    linarith [ht i]
  · intro i
    rw [Fin.sum_univ_three]
    fin_cases i
    · change 3-3*lpNorm p x-(453/5000 : ℝ) ≤ (3*x 0+3*y 0+3*z 0)-3*x 0
      linarith [hS,hyzE,hE]
    · change 3-3*lpNorm p y-(453/5000 : ℝ) ≤ (3*x 1+3*y 1+3*z 1)-3*y 1
      linarith [hS,hxzE,hE]
    · change 3-3*lpNorm p z-(453/5000 : ℝ) ≤ (3*x 2+3*y 2+3*z 2)-3*z 2
      linarith [hS,hxyE,hE]


theorem lpNorm_smul [NormedSpace ℝ E] {p : ℝ} (hp : 0 < p)
    (c : ℝ) (x : ι → E) : lpNorm p (c • x) = |c| * lpNorm p x := by
  unfold lpNorm
  simp only [Pi.smul_apply, norm_smul, Real.norm_eq_abs,
    Real.mul_rpow (abs_nonneg c) (norm_nonneg _), ← Finset.mul_sum]
  rw [Real.mul_rpow (Real.rpow_nonneg (abs_nonneg c) _)
    (Finset.sum_nonneg fun i _ ↦ Real.rpow_nonneg (norm_nonneg (x i)) _),
    ← Real.rpow_mul (abs_nonneg c), mul_one_div_cancel hp.ne', Real.rpow_one]


theorem lpNorm_comp_equiv {κ : Type*} [Fintype κ]
    (p : ℝ) (x : κ → E) (e : ι ≃ κ) : lpNorm p (x ∘ e) = lpNorm p x := by
  unfold lpNorm
  congr 1
  exact e.sum_comp (fun i ↦ ‖x i‖ ^ p)


theorem pairGap_nonneg {p : ℝ} (hp : 1 ≤ p) (x y : ι → E) :
    0 ≤ pairGap (lpNorm p) x y := sub_nonneg.mpr (lpNorm_add hp x y)


theorem pairGapSum_nonneg {p : ℝ} (hp : 1 ≤ p) (x y z : ι → E) :
    0 ≤ pairGapSum (lpNorm p) x y z :=
  add_nonneg (add_nonneg (pairGap_nonneg hp x y) (pairGap_nonneg hp x z))
    (pairGap_nonneg hp y z)


theorem hlawkaDeficit_eq (p K : ℝ) (x y z : ι → ℝ) :
    hlawkaDeficit p K x y z =
      K * pairGapSum (lpNorm p) x y z - tripleGap (lpNorm p) x y z := by
  unfold hlawkaDeficit pairGapSum pairGap tripleGap
  ring


theorem hlawkaDeficit_swap_left (p K : ℝ) (x y z : ι → ℝ) :
    hlawkaDeficit p K y x z = hlawkaDeficit p K x y z := by
  simp only [hlawkaDeficit, add_comm, add_left_comm, add_assoc]


theorem hlawkaDeficit_swap_right (p K : ℝ) (x y z : ι → ℝ) :
    hlawkaDeficit p K x z y = hlawkaDeficit p K x y z := by
  simp only [hlawkaDeficit, add_comm, add_left_comm, add_assoc]


theorem hlawkaDeficit_smul {p : ℝ} (hp : 0 < p) (K c : ℝ) (x y z : ι → ℝ) :
    hlawkaDeficit p K (c • x) (c • y) (c • z) = |c| * hlawkaDeficit p K x y z := by
  simp only [hlawkaDeficit, ← smul_add, lpNorm_smul hp]
  ring


theorem scalarEnvelopeRoot_lt_one {p q : ℝ} (hp : 0 < p) (hq : 0 ≤ q) (hq1 : q < 1) :
    scalarEnvelopeRoot p q < 1 := by
  have hpow : q ^ p < 1 := by
    simpa only [Real.one_rpow] using Real.rpow_lt_rpow hq hq1 hp
  have hbase : 0 ≤ (1 + q ^ p) / 2 := by positivity
  have hroot := Real.rpow_lt_rpow hbase (show (1 + q ^ p) / 2 < 1 by linarith)
    (one_div_pos.mpr hp)
  simpa only [Real.one_rpow, scalarEnvelopeRoot] using hroot


theorem scalarEnvelope_denominator_pos {p q : ℝ} (hp : 0 < p) (hq : 0 ≤ q) (hq1 : q < 1) :
    0 < 2 * (1 - scalarEnvelopeRoot p q) := by
  have h := scalarEnvelopeRoot_lt_one hp hq hq1
  linarith


theorem failure_ne_zero {p K : ℝ} (hp : 1 ≤ p) (hK : 1 ≤ K)
    (x y z : ι → ℝ) (hf : hlawkaDeficit p K x y z < 0) :
    x ≠ 0 ∧ y ≠ 0 ∧ z ≠ 0 := by
  have hfirst (u v w : ι → ℝ) (h : hlawkaDeficit p K u v w < 0) : u ≠ 0 := by
    intro hu
    subst u
    simp only [hlawkaDeficit, lpNorm_zero (zero_lt_one.trans_le hp), zero_add] at h
    have ht := lpNorm_add hp v w
    have hm := mul_nonneg (sub_nonneg.mpr hK)
      (show 0 ≤ lpNorm p v + lpNorm p w - lpNorm p (v + w) by linarith)
    nlinarith
  refine ⟨hfirst x y z hf, hfirst y x z ?_, hfirst z x y ?_⟩
  · rwa [hlawkaDeficit_swap_left]
  · rwa [hlawkaDeficit_swap_left, hlawkaDeficit_swap_right]


theorem normalized_failure_total_lt_one {p K : ℝ} (hp : 1 ≤ p) (hK : 0 ≤ K)
    (x y z : ι → ℝ) (hS : lpNorm p x + lpNorm p y + lpNorm p z = 1)
    (hf : hlawkaDeficit p K x y z < 0) : lpNorm p (x + y + z) < 1 := by
  rw [hlawkaDeficit_eq, tripleGap, hS] at hf
  have hprod := mul_nonneg hK (pairGapSum_nonneg hp x y z)
  linarith


theorem normalized_failure_ratio_lt_envelope {p K : ℝ} (hp : 1 < p) (hK : 1 ≤ K)
    (x y z : ι → ℝ) (hS : lpNorm p x + lpNorm p y + lpNorm p z = 1)
    (hf : hlawkaDeficit p K x y z < 0) :
    K < scalarEnvelope p (lpNorm p (x + y + z)) := by
  have hp0 := zero_lt_one.trans hp
  have hn := failure_ne_zero hp.le hK x y z hf
  have hq0 := lpNorm_nonneg p (x + y + z)
  have hq1 := normalized_failure_total_lt_one hp.le (by linarith) x y z hS hf
  have hP := normalized_pair_sum_le hp x y z hn.1 hn.2.1 hn.2.2 hS
  have hden := scalarEnvelope_denominator_pos hp0 hq0 hq1
  have hgap : 2 * (1 - scalarEnvelopeRoot p (lpNorm p (x + y + z))) ≤
      pairGapSum (lpNorm p) x y z := by
    dsimp only [pairGapSum, pairGap]
    linarith
  have hgap0 : 0 < pairGapSum (lpNorm p) x y z := hden.trans_le hgap
  have hR : K < (1 - lpNorm p (x + y + z)) / pairGapSum (lpNorm p) x y z := by
    rw [lt_div_iff₀ hgap0]
    rw [hlawkaDeficit_eq, tripleGap, hS] at hf
    linarith
  exact hR.trans_le (div_le_div_of_nonneg_left (by linarith) hden hgap)


theorem normalized_failure_total_lt_q0 {p : ℝ} (hp : 50 ≤ p)
    (hlinear : (457 / 1000 : ℝ) * p < cyclicConstant p)
    (henvelope : scalarEnvelope p (37/100) < cyclicConstant p)
    (x y z : ι → ℝ) (hS : lpNorm p x + lpNorm p y + lpNorm p z = 1)
    (hf : hlawkaDeficit p (cyclicConstant p) x y z < 0) :
    lpNorm p (x + y + z) < 37/100 := by
  have hp1 : 1 < p := by linarith
  have hK : 1 ≤ cyclicConstant p := by linarith
  have hq1 := normalized_failure_total_lt_one hp1.le (by linarith) x y z hS hf
  have henv := normalized_failure_ratio_lt_envelope hp1 hK x y z hS hf
  by_contra hn
  have hq0 : (37/100 : ℝ) ≤ lpNorm p (x + y + z) := le_of_not_gt hn
  have hm := antitoneOn_scalarEnvelope hp1.le
    (show (37/100 : ℝ) ∈ Set.Ico 0 1 by norm_num)
    (show lpNorm p (x + y + z) ∈ Set.Ico 0 1 from ⟨lpNorm_nonneg p _, hq1⟩) hq0
  linarith [henvelope]


/-- The scalar data used by the coordinate argument. -/
theorem normalized_failure_confinement {p : ℝ} (hp : 50 ≤ p)
    (hlinear : (457 / 1000 : ℝ) * p < cyclicConstant p)
    (henvelope : scalarEnvelope p (37/100) < cyclicConstant p)
    (x y z : ι → ℝ) (hS : lpNorm p x + lpNorm p y + lpNorm p z = 1)
    (hx : lpNorm p x ≤ lpNorm p (x + y + z))
    (hy : lpNorm p y ≤ lpNorm p (x + y + z))
    (hz : lpNorm p z ≤ lpNorm p (x + y + z))
    (hf : hlawkaDeficit p (cyclicConstant p) x y z < 0) :
    (1 / 3 ≤ lpNorm p (x + y + z) ∧ lpNorm p (x + y + z) < 37/100) ∧
      pairGapSum (lpNorm p) x y z < 3 / (2 * p) ∧
      (13/50 < lpNorm p x ∧ lpNorm p x < 37/100) ∧
      (13/50 < lpNorm p y ∧ lpNorm p y < 37/100) ∧
      (13/50 < lpNorm p z ∧ lpNorm p z < 37/100) := by
  have hp1 : 1 < p := by linarith
  have hq := normalized_failure_total_lt_q0 hp hlinear henvelope x y z hS hf
  have hqLower : 1 / 3 ≤ lpNorm p (x + y + z) := by linarith
  have hD := pairGapSum_nonneg hp1.le x y z
  have hK := hlinear
  have hmul := mul_le_mul_of_nonneg_right hK.le hD
  have hf' := hf
  rw [hlawkaDeficit_eq, tripleGap, hS] at hf'
  have hsmall : pairGapSum (lpNorm p) x y z < 3 / (2 * p) := by
    rw [lt_div_iff₀ (show 0 < 2 * p by linarith)]
    nlinarith
  exact ⟨⟨hqLower, hq⟩, hsmall, ⟨by linarith, hx.trans_lt hq⟩,
    ⟨by linarith, hy.trans_lt hq⟩, ⟨by linarith, hz.trans_lt hq⟩⟩


theorem lpNorm_le_three_root_mul_max {p : ℝ} (hp : 0 < p) (x : Fin 3 → ℝ)
    (i : Fin 3) (hi : ∀ j, |x j| ≤ |x i|) :
    lpNorm p x ≤ (3 : ℝ) ^ (1 / p) * |x i| := by
  have hsum : (∑ j, |x j| ^ p) ≤ 3 * |x i| ^ p := by
    calc
      _ ≤ ∑ _ : Fin 3, |x i| ^ p :=
        Finset.sum_le_sum fun j _ ↦ Real.rpow_le_rpow (abs_nonneg _) (hi j) hp.le
      _ = _ := by simp
  have h := Real.rpow_le_rpow
    (Finset.sum_nonneg fun j _ ↦ Real.rpow_nonneg (abs_nonneg (x j)) p)
    hsum (one_div_nonneg.mpr hp.le)
  rw [Real.mul_rpow (by norm_num) (Real.rpow_nonneg (abs_nonneg _) _),
    ← Real.rpow_mul (abs_nonneg (x i)), mul_one_div_cancel hp.ne', Real.rpow_one] at h
  simpa only [lpNorm, Real.norm_eq_abs] using h


theorem inverse_three_root_deficit (p : ℝ) :
    1 - ((3 : ℝ) ^ (1 / p))⁻¹ ≤ Real.log 3 / p := by
  have h := Real.add_one_le_exp (-(Real.log 3 / p))
  have he : ((3 : ℝ) ^ (1 / p))⁻¹ = Real.exp (-(Real.log 3 / p)) := by
    rw [Real.rpow_def_of_pos (by norm_num), ← Real.exp_neg]
    congr 1
    ring
  rw [he]
  linarith


theorem signed_entry_le_norm {p s : ℝ} (hp : 1 ≤ p) (hs : |s| = 1)
    (x : Fin 3 → ℝ) (i : Fin 3) : s * x i ≤ lpNorm p x := by
  calc
    _ ≤ |s * x i| := le_abs_self _
    _ = |x i| := by rw [abs_mul, hs, one_mul]
    _ ≤ _ := norm_apply_le_lpNorm hp x i


/-- Small pair gap forces two large entries with one common sign. -/
theorem exists_large_signed_pair {p : ℝ} (hp : 50 ≤ p) (x y : Fin 3 → ℝ)
    (hx : lpNorm p x < 37/100) (hy : lpNorm p y < 37/100)
    (hgap : pairGap (lpNorm p) x y < 3 / (2 * p)) :
    ∃ i : Fin 3, ∃ s : ℝ, (s = 1 ∨ s = -1) ∧
      lpNorm p x - 12 / (5 * p) < s * x i ∧
      lpNorm p y - 12 / (5 * p) < s * y i := by
  have hp0 : 0 < p := by linarith
  have hp1 : 1 ≤ p := by linarith
  obtain ⟨i, _, hi⟩ := Finset.univ.exists_max_image (fun i ↦ |(x + y) i|)
    Finset.univ_nonempty
  have hmax := lpNorm_le_three_root_mul_max hp0 (x + y) i (fun j ↦ hi j (Finset.mem_univ _))
  let c := ((3 : ℝ) ^ (1 / p))⁻¹
  have hc0 : 0 < c := by dsimp [c]; positivity
  have hc1 : c ≤ 1 := by
    apply inv_le_one_of_one_le₀
    exact Real.one_le_rpow (by norm_num) (by positivity)
  have hmax' : c * lpNorm p (x + y) ≤ |x i + y i| := by
    have hm := mul_le_mul_of_nonneg_left hmax hc0.le
    have he : c * ((3 : ℝ) ^ (1 / p) * |(x + y) i|) = |(x + y) i| := by
      dsimp [c]
      rw [← mul_assoc, inv_mul_cancel₀ (by positivity), one_mul]
    rw [he] at hm
    exact hm
  have hd : 1 - c ≤ Real.log 3 / p := inverse_three_root_deficit p
  have hlog3 : Real.log 3 < 11 / 10 := by linarith [Real.log_three_lt_d9]
  have hs0 : 0 ≤ lpNorm p x + lpNorm p y := add_nonneg (lpNorm_nonneg p x) (lpNorm_nonneg p y)
  have hbound : lpNorm p x + lpNorm p y - |x i + y i| < 12 / (5 * p) := by
    have hS : lpNorm p x + lpNorm p y < 74/100 := by linarith
    have hdef := mul_le_mul_of_nonneg_right hd hs0
    have hg := pairGap_nonneg hp1 x y
    have hgap' := mul_le_mul_of_nonneg_right hc1 hg
    have hlogP : 0 ≤ Real.log 3 / p := by positivity
    have hSlog := mul_le_mul_of_nonneg_left hS.le hlogP
    have hlogDiv := (div_lt_div_iff_of_pos_right hp0).mpr hlog3
    have hlogLast := mul_lt_mul_of_pos_right hlogDiv (by norm_num : (0 : ℝ) < 74/100)
    dsimp only [pairGap] at hgap hg hgap'
    have hnum : Real.log 3 / p * (74/100 : ℝ) + 3 / (2 * p) < 12 / (5 * p) := by
      have hrat : (11 / 10 : ℝ) / p * (74/100) + 3 / (2 * p) < 12 / (5 * p) := by
        apply (mul_lt_mul_iff_left₀ hp0).mp
        field_simp
        norm_num
      linarith
    nlinarith
  by_cases hi0 : 0 ≤ x i + y i
  · rw [abs_of_nonneg hi0] at hbound
    have hxi := signed_entry_le_norm hp1 (s := 1) (by norm_num) x i
    have hyi := signed_entry_le_norm hp1 (s := 1) (by norm_num) y i
    exact ⟨i, 1, Or.inl rfl, by linarith, by linarith⟩
  · rw [abs_of_neg (lt_of_not_ge hi0)] at hbound
    have hxi := signed_entry_le_norm hp1 (s := -1) (by norm_num) x i
    have hyi := signed_entry_le_norm hp1 (s := -1) (by norm_num) y i
    exact ⟨i, -1, Or.inr rfl, by linarith, by linarith⟩


theorem orient_add (e : Equiv.Perm (Fin 3)) (s x y : Fin 3 → ℝ) :
    orient e s (x + y) = orient e s x + orient e s y := by
  ext i
  exact mul_add _ _ _


theorem lpNorm_orient (p : ℝ) (e : Equiv.Perm (Fin 3)) (s x : Fin 3 → ℝ)
    (hs : ∀ i, |s i| = 1) : lpNorm p (orient e s x) = lpNorm p x := by
  calc
    _ = lpNorm p (x ∘ e) := by simp [lpNorm, orient, hs, Real.norm_eq_abs]
    _ = _ := lpNorm_comp_equiv p x e


theorem hlawkaDeficit_orient (p K : ℝ) (e : Equiv.Perm (Fin 3)) (s x y z : Fin 3 → ℝ)
    (hs : ∀ i, |s i| = 1) :
    hlawkaDeficit p K (orient e s x) (orient e s y) (orient e s z) =
      hlawkaDeficit p K x y z := by
  simp only [hlawkaDeficit, ← orient_add, lpNorm_orient p e s _ hs]


private theorem signed_row_conflict {a b c A B C q E s r : ℝ}
    (hs : s = 1 ∨ s = -1) (hr : r = 1 ∨ r = -1)
    (ha : E < A) (hsum : q < A + B + C - 3 * E)
    (hsa : A - E < s * a) (hsb : B - E < s * b)
    (hra : A - E < r * a) (hrc : C - E < r * c)
    (habs : |a + b + c| ≤ q) : False := by
  have heq : r = s := by
    rcases hs with rfl | rfl <;> rcases hr with rfl | rfl <;> first | rfl | exfalso; linarith
  subst r
  have hsabs : |s| = 1 := by rcases hs with rfl | rfl <;> norm_num
  have hu : s * (a + b + c) ≤ q := by
    calc
      _ ≤ |s * (a + b + c)| := le_abs_self _
      _ = |a + b + c| := by rw [abs_mul, hsabs, one_mul]
      _ ≤ q := habs
  nlinarith


private theorem oriented_triple_in_coarse_box {p : ℝ} (hp : 50 ≤ p)
    (x y z : Fin 3 → ℝ)
    (hS : lpNorm p x + lpNorm p y + lpNorm p z = 1)
    (hx : 13/50 < lpNorm p x ∧ lpNorm p x < 37/100)
    (hy : 13/50 < lpNorm p y ∧ lpNorm p y < 37/100)
    (hz : 13/50 < lpNorm p z ∧ lpNorm p z < 37/100)
    (hT : lpNorm p (x + y + z) < 37/100)
    (hx1 : lpNorm p x - 12 / (5 * p) < x 1)
    (hx2 : lpNorm p x - 12 / (5 * p) < x 2)
    (hy0 : lpNorm p y - 12 / (5 * p) < y 0)
    (hy2 : lpNorm p y - 12 / (5 * p) < y 2)
    (hz0 : lpNorm p z - 12 / (5 * p) < z 0)
    (hz1 : lpNorm p z - 12 / (5 * p) < z 1) :
    (![x,y,z] : Triple) ∈ Hl50LocGeometry.coarseBox := by
  have hp1 : 1 ≤ p := by linarith
  have hE : 12 / (5 * p) ≤ (6/125 : ℝ) := by
    rw [div_le_iff₀ (by positivity)]
    linarith
  have hxi (i : Fin 3) := abs_le.mp (norm_apply_le_lpNorm hp1 x i)
  have hyi (i : Fin 3) := abs_le.mp (norm_apply_le_lpNorm hp1 y i)
  have hzi (i : Fin 3) := abs_le.mp (norm_apply_le_lpNorm hp1 z i)
  have ht (i : Fin 3) : x i + y i + z i < 37/100 :=
    ((le_abs_self (x i + y i + z i)).trans
      (norm_apply_le_lpNorm hp1 (x + y + z) i)).trans_lt hT
  simp only [Hl50LocGeometry.coarseBox, Set.mem_ofPred_eq]
  intro j i
  fin_cases j <;> fin_cases i <;>
    norm_num <;>
    constructor <;> linarith! [hxi 0, hxi 1, hxi 2, hyi 0, hyi 1, hyi 2,
      hzi 0, hzi 1, hzi 2, ht 0, ht 1, ht 2]



theorem exists_failure_in_asymmetricBox50 {p : ℝ} (hp : 50 ≤ p)
    (hlinear : (457 / 1000 : ℝ) * p < cyclicConstant p)
    (henvelope : scalarEnvelope p (37/100) < cyclicConstant p)
    (x y z : Fin 3 → ℝ) (hf : hlawkaDeficit p (cyclicConstant p) x y z < 0) :
    ∃ X ∈ asymmetricBox, tripleDeficit p (cyclicConstant p) X < 0 := by
  have hp0 : 0 < p := by linarith
  have hp1 : 1 < p := by linarith
  obtain ⟨x, y, z, hf, hS, hxT, hyT, hzT⟩ :=
    exists_normalized_failure hp0 (by linarith : 1 ≤ cyclicConstant p) x y z hf
  obtain ⟨⟨_, hT⟩, hgap, hx, hy, hz⟩ :=
    normalized_failure_confinement hp hlinear henvelope x y z hS hxT hyT hzT hf
  have hxy0 := pairGap_nonneg hp1.le x y
  have hxz0 := pairGap_nonneg hp1.le x z
  have hyz0 := pairGap_nonneg hp1.le y z
  have hgapTotal := hgap
  dsimp only [pairGapSum] at hgap
  obtain ⟨i, s, hs, hsx, hsy⟩ := exists_large_signed_pair hp x y hx.2 hy.2 (by linarith)
  obtain ⟨j, r, hr, hrx, hrz⟩ := exists_large_signed_pair hp x z hx.2 hz.2 (by linarith)
  obtain ⟨k, t, ht, hty, htz⟩ := exists_large_signed_pair hp y z hy.2 hz.2 (by linarith)
  have hE : 12 / (5 * p) ≤ (6/125 : ℝ) := by
    rw [div_le_iff₀ (by positivity)]
    linarith
  have habs (l : Fin 3) : |x l + y l + z l| ≤ lpNorm p (x + y + z) :=
    norm_apply_le_lpNorm hp1.le (x + y + z) l
  have hij : i ≠ j := by
    intro heq
    subst j
    exact signed_row_conflict hs hr (by linarith [hx.1]) (by linarith)
      hsx hsy hrx hrz (habs i)
  have hik : i ≠ k := by
    intro heq
    subst k
    have hsym : |y i + x i + z i| ≤ lpNorm p (x + y + z) := by
      simpa only [add_comm, add_left_comm, add_assoc] using habs i
    exact signed_row_conflict hs ht (by linarith [hy.1]) (by linarith)
      hsy hsx hty htz hsym
  have hjk : j ≠ k := by
    intro heq
    subst k
    have hsym : |z j + x j + y j| ≤ lpNorm p (x + y + z) := by
      simpa only [add_comm, add_left_comm, add_assoc] using habs j
    exact signed_row_conflict hr ht (by linarith [hz.1]) (by linarith)
      hrz hrx htz hty hsym
  let f : Fin 3 → Fin 3 := ![k, j, i]
  have hfInj : Function.Injective f := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all [f, Ne.symm hij, Ne.symm hik, Ne.symm hjk]
  let e : Equiv.Perm (Fin 3) := Equiv.ofBijective f hfInj.bijective_of_finite
  let signs : Fin 3 → ℝ := ![t, r, s]
  have hsigns : ∀ l, |signs l| = 1 := by
    intro l
    fin_cases l
    · rcases ht with rfl | rfl <;> norm_num [signs]
    · rcases hr with rfl | rfl <;> norm_num [signs]
    · rcases hs with rfl | rfl <;> norm_num [signs]
  let u := orient e signs x
  let v := orient e signs y
  let w := orient e signs z
  have hu : lpNorm p u = lpNorm p x := lpNorm_orient p e signs x hsigns
  have hv : lpNorm p v = lpNorm p y := lpNorm_orient p e signs y hsigns
  have hw : lpNorm p w = lpNorm p z := lpNorm_orient p e signs z hsigns
  have hsumNorm : lpNorm p (u + v + w) = lpNorm p (x + y + z) := by
    dsimp [u, v, w]
    rw [← orient_add, ← orient_add, lpNorm_orient p e signs _ hsigns]
  have hcoarse : (![u,v,w] : Triple) ∈ Hl50LocGeometry.coarseBox := by
    apply oriented_triple_in_coarse_box hp u v w
    · rwa [hu, hv, hw]
    · rwa [hu]
    · rwa [hv]
    · rwa [hw]
    · rwa [hsumNorm]
    · simpa [hu, u, orient, e, f, signs] using hrx
    · simpa [hu, u, orient, e, f, signs] using hsx
    · simpa [hv, v, orient, e, f, signs] using hty
    · simpa [hv, v, orient, e, f, signs] using hsy
    · simpa [hw, w, orient, e, f, signs] using htz
    · simpa [hw, w, orient, e, f, signs] using hrz
  have hgapOriented : pairGapSum (lpNorm p) u v w < 3 / (2 * p) := by
    dsimp [u,v,w]
    simpa only [pairGapSum, pairGap, ← orient_add, lpNorm_orient p e signs _ hsigns] using hgapTotal
  refine ⟨![(3 : ℝ) • u, (3 : ℝ) • v, (3 : ℝ) • w], ?_, ?_⟩
  · apply bootstrap50 hp u v w
    · rwa [hu,hv,hw]
    · rw [hu]; exact hx.2.le
    · rw [hv]; exact hy.2.le
    · rw [hw]; exact hz.2.le
    · rw [hsumNorm]; exact hT.le
    · exact hgapOriented
    · exact hcoarse
  · change hlawkaDeficit p (cyclicConstant p) ((3 : ℝ) • u) ((3 : ℝ) • v) ((3 : ℝ) • w) < 0
    rw [hlawkaDeficit_smul hp0]
    have hfail : hlawkaDeficit p (cyclicConstant p) u v w < 0 := by
      dsimp [u, v, w]
      rwa [hlawkaDeficit_orient p (cyclicConstant p) e signs x y z hsigns]
    norm_num only [abs_of_pos (by norm_num : (0 : ℝ) < 3)]
    linarith

end Hl50LocLocalization

open HlawkaSchatten HlawkaSchatten.DiagonalConstruction

theorem HlawkaSchatten.DiagonalCutoff50.local_failure50 : ∀ p : ℝ, 50 ≤ p →
    (457 / 1000 : ℝ) * p < cyclicConstant p →
    scalarEnvelope p (37 / 100) < cyclicConstant p →
    ∀ x y z : Fin 3 → ℝ,
      hlawkaDeficit p (cyclicConstant p) x y z < 0 →
        ∃ X ∈ ({X : Triple | ∀ j i,
          if j = i then -(111 / 100 : ℝ) ≤ X j i ∧ X j i ≤ -(6894 / 10000 : ℝ)
          else (8091 / 10000 : ℝ) ≤ X j i ∧ X j i ≤ (111 / 100 : ℝ)} : Set Triple),
          tripleDeficit p (cyclicConstant p) X < 0 := by
  intro p hp hlin henv x y z hf
  exact Hl50LocLocalization.exists_failure_in_asymmetricBox50 hp hlin henv x y z hf

set_option autoImplicit false

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Hl50CvxNorm
open HlawkaSchatten.DiagonalConstruction

section Basic
variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E]

theorem lpNorm_nonneg (p : ℝ) (x : ι → E) : 0 ≤ lpNorm p x :=
  Real.rpow_nonneg (Finset.sum_nonneg fun _ _ ↦ Real.rpow_nonneg (norm_nonneg _) _) _


theorem lpNorm_eq_piLp {p : ℝ} (hp : 0 < p) (x : ι → E) :
    lpNorm p x = ‖WithLp.toLp (ENNReal.ofReal p) x‖ := by
  rw [PiLp.norm_eq_sum (by simpa only [ENNReal.toReal_ofReal hp.le] using hp)]
  simp [lpNorm, ENNReal.toReal_ofReal hp.le]


theorem lpNorm_zero {p : ℝ} (hp : 0 < p) : lpNorm p (0 : ι → E) = 0 := by
  simp [lpNorm, hp.ne']


theorem norm_apply_le_lpNorm {p : ℝ} (hp : 1 ≤ p) (x : ι → E) (i : ι) :
    ‖x i‖ ≤ lpNorm p x := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  let : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr hp⟩
  rw [lpNorm_eq_piLp hp0]
  exact PiLp.norm_apply_le (WithLp.toLp (ENNReal.ofReal p) x) i


theorem lpNorm_rpow {p : ℝ} (hp : 0 < p) (x : ι → E) :
    lpNorm p x ^ p = ∑ i, ‖x i‖ ^ p := by
  unfold lpNorm
  rw [← Real.rpow_mul (Finset.sum_nonneg fun i _ ↦ Real.rpow_nonneg (norm_nonneg _) _)]
  rw [one_div_mul_cancel hp.ne', Real.rpow_one]


theorem lpNorm_eq_zero_iff {p : ℝ} (hp : 0 < p) (x : ι → E) :
    lpNorm p x = 0 ↔ x = 0 := by
  constructor
  · intro h
    have hs : (∑ i, ‖x i‖ ^ p) = 0 := by
      rw [← lpNorm_rpow hp x, h, Real.zero_rpow hp.ne']
    have hi := (Finset.sum_eq_zero_iff_of_nonneg
      (fun i (_ : i ∈ Finset.univ) ↦ Real.rpow_nonneg (norm_nonneg (x i)) p)).mp hs
    funext i
    exact norm_eq_zero.mp ((Real.rpow_eq_zero (norm_nonneg (x i)) hp.ne').mp
      (hi i (Finset.mem_univ i)))
  · rintro rfl
    exact lpNorm_zero hp


theorem lpNorm_pos {p : ℝ} (hp : 0 < p) {x : ι → E} (hx : x ≠ 0) :
    0 < lpNorm p x :=
  lt_of_le_of_ne (lpNorm_nonneg p x) (Ne.symm ((lpNorm_eq_zero_iff hp x).not.mpr hx))


theorem continuous_lpNorm {p : ℝ} (hp : 0 < p) :
    Continuous (lpNorm p : (ι → E) → ℝ) := by
  exact (continuous_finsetSum _ fun i _ ↦
    (continuous_apply i).norm.rpow_const (fun _ ↦ Or.inr hp.le)).rpow_const
      (fun _ ↦ Or.inr (one_div_nonneg.mpr hp.le))


theorem lpNorm_le_card_root_mul {p M : ℝ} (hp : 0 < p) (hM : 0 ≤ M)
    (x : ι → E) (hx : ∀ i, ‖x i‖ ≤ M) :
    lpNorm p x ≤ (Fintype.card ι : ℝ) ^ (1 / p) * M := by
  have hsum : (∑ i, ‖x i‖ ^ p) ≤ (Fintype.card ι : ℝ) * M ^ p := by
    calc
      _ ≤ ∑ _ : ι, M ^ p :=
        Finset.sum_le_sum fun i _ ↦ Real.rpow_le_rpow (norm_nonneg _) (hx i) hp.le
      _ = _ := by simp
  have h := Real.rpow_le_rpow
    (Finset.sum_nonneg fun i _ ↦ Real.rpow_nonneg (norm_nonneg (x i)) p)
    hsum (one_div_nonneg.mpr hp.le)
  rw [Real.mul_rpow (Nat.cast_nonneg _) (Real.rpow_nonneg hM _),
    ← Real.rpow_mul hM, mul_one_div_cancel hp.ne', Real.rpow_one] at h
  exact h

end Basic

section Norm
variable {ι : Type*} [Fintype ι]

theorem powerSum_nonneg (p : ℝ) (v : ι → ℝ) : 0 ≤ powerSum p v :=
  Finset.sum_nonneg fun i _ ↦ Real.rpow_nonneg (abs_nonneg (v i)) p


theorem powerSum_eq_lpNorm_rpow {p : ℝ} (hp : 0 < p) (v : ι → ℝ) :
    powerSum p v = lpNorm p v ^ p := by
  rw [lpNorm_rpow hp]
  rfl


theorem powerSum_pos {p : ℝ} (hp : 0 < p) {v : ι → ℝ} (hv : v ≠ 0) : 0 < powerSum p v := by
  rw [powerSum_eq_lpNorm_rpow hp]
  exact Real.rpow_pos_of_pos (lpNorm_pos hp hv) p

omit [Fintype ι] in

private theorem abs_rpow_mul_sq {q : ℝ} (hq : 0 < q) (x : ℝ) :
    |x| ^ q * x ^ 2 = |x| ^ (q + 2) := by
  by_cases hx : x = 0
  · simp [hx, hq.ne', show q + 2 ≠ 0 by linarith]
  · rw [← sq_abs, ← Real.rpow_two, ← Real.rpow_add (abs_pos.mpr hx)]


theorem powerQuad_self {p : ℝ} (hp : 2 < p) (v : ι → ℝ) :
    powerQuad p v v = powerSum p v := by
  unfold powerQuad powerSum
  apply Finset.sum_congr rfl
  intro i _
  simpa only [sub_add_cancel] using abs_rpow_mul_sq (by linarith : 0 < p - 2) (v i)


theorem powerResidual_eq {p : ℝ} (hp : 2 < p) (v h : ι → ℝ) (a : ℝ) :
    powerResidual p v h a = powerQuad p v h - 2 * a * powerPair p v h + a ^ 2 * powerSum p v := by
  rw [← powerQuad_self hp v]
  simp only [powerResidual, powerQuad, powerPair, Finset.mul_sum, ← Finset.sum_sub_distrib,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring


theorem powerResidual_radial {p : ℝ} (hp : 2 < p) (v h : ι → ℝ) (hv : v ≠ 0) :
    powerResidual p v h (radialCoefficient p v h) =
      powerQuad p v h - powerPair p v h ^ 2 / powerSum p v := by
  rw [powerResidual_eq hp, radialCoefficient]
  field_simp [(powerSum_pos (by linarith : 0 < p) hv).ne']
  ring


theorem powerResidual_min {p : ℝ} (hp : 2 < p) (v h : ι → ℝ) (hv : v ≠ 0) (a : ℝ) :
    powerResidual p v h (radialCoefficient p v h) ≤ powerResidual p v h a := by
  have hS := powerSum_pos (by linarith : 0 < p) hv
  rw [powerResidual_radial hp v h hv, powerResidual_eq hp]
  have hn := mul_nonneg hS.le (sq_nonneg (a - powerPair p v h / powerSum p v))
  have hmul : powerSum p v * (powerPair p v h / powerSum p v) = powerPair p v h :=
    mul_div_cancel₀ _ hS.ne'
  have hmul2 : powerSum p v * (powerPair p v h / powerSum p v) ^ 2 =
      powerPair p v h ^ 2 / powerSum p v := by field_simp
  nlinarith [congrArg (fun x : ℝ ↦ a * x) hmul]


theorem powerResidual_nonneg (p : ℝ) (v h : ι → ℝ) (a : ℝ) : 0 ≤ powerResidual p v h a :=
  Finset.sum_nonneg fun i _ ↦ mul_nonneg
    (Real.rpow_nonneg (abs_nonneg (v i)) (p - 2)) (sq_nonneg (h i - a * v i))


theorem normHessian_nonneg {p : ℝ} (hp : 1 ≤ p) (v h : ι → ℝ) : 0 ≤ normHessian p v h :=
  mul_nonneg (mul_nonneg (sub_nonneg.mpr hp) (Real.rpow_nonneg (powerSum_nonneg p v) _))
    (powerResidual_nonneg p v h _)


theorem normHessian_le_residual {p : ℝ} (hp : 2 < p) (v h : ι → ℝ) (hv : v ≠ 0) (a : ℝ) :
    normHessian p v h ≤ (p - 1) * powerSum p v ^ (1 / p - 1) * powerResidual p v h a := by
  exact mul_le_mul_of_nonneg_left (powerResidual_min hp v h hv a)
    (mul_nonneg (by linarith) (Real.rpow_nonneg (powerSum_nonneg p v) _))

omit [Fintype ι] in

private theorem hasDerivAt_abs_power_slope {p : ℝ} (hp : 4 < p) (x : ℝ) :
    HasDerivAt (fun x : ℝ ↦ |x| ^ (p - 2) * x) ((p - 1) * |x| ^ (p - 2)) x := by
  have h := (hasDerivAt_abs_rpow x (by linarith : 1 < p - 2)).mul (hasDerivAt_id x)
  have heq : ((p - 2) * |x| ^ (p - 2 - 2) * x) * x + |x| ^ (p - 2) * 1 =
      (p - 1) * |x| ^ (p - 2) := by
    have hh := abs_rpow_mul_sq (by linarith : 0 < p - 2 - 2) x
    have hcancel : p - 2 - 2 + 2 = p - 2 := by ring
    rw [hcancel] at hh
    nlinarith
  convert! h using 1
  simpa only [id_eq] using heq.symm


theorem hasDerivAt_powerSum_line {p : ℝ} (hp : 1 < p) (v h : ι → ℝ) (t : ℝ) :
    HasDerivAt (fun s : ℝ ↦ powerSum p (v + s • h))
      (p * powerPair p (v + t • h) h) t := by
  have hi (i : ι) : HasDerivAt (fun s : ℝ ↦ |v i + s * h i| ^ p)
      (p * |v i + t * h i| ^ (p - 2) * (v i + t * h i) * h i) t := by
    simpa only [one_mul, id_eq, Function.comp_def] using
      (hasDerivAt_abs_rpow _ hp).comp t (((hasDerivAt_id t).mul_const (h i)).const_add (v i))
  simpa only [powerSum, powerPair, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum,
    mul_assoc] using HasDerivAt.fun_sum (u := Finset.univ) (fun i _ ↦ hi i)


theorem hasDerivAt_powerPair_line {p : ℝ} (hp : 4 < p) (v h : ι → ℝ) (t : ℝ) :
    HasDerivAt (fun s : ℝ ↦ powerPair p (v + s • h) h)
      ((p - 1) * powerQuad p (v + t • h) h) t := by
  have hi (i : ι) := ((hasDerivAt_abs_power_slope hp (v i + t * h i)).comp t
    (((hasDerivAt_id t).mul_const (h i)).const_add (v i))).mul_const (h i)
  simpa only [powerPair, powerQuad, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum,
    pow_two, mul_assoc, Function.comp_def, id_eq, one_mul] using
      HasDerivAt.fun_sum (u := Finset.univ) (fun i _ ↦ hi i)


theorem hasDerivAt_lpNorm_line {p : ℝ} (hp : 1 < p) (v h : ι → ℝ) (t : ℝ)
    (hv : v + t • h ≠ 0) :
    HasDerivAt (fun s : ℝ ↦ lpNorm p (v + s • h)) (normSlope p (v + t • h) h) t := by
  have hp0 := zero_lt_one.trans hp
  have hh := (hasDerivAt_powerSum_line hp v h t).rpow_const (p := 1 / p)
    (Or.inl (powerSum_pos hp0 hv).ne')
  have he : p * powerPair p (v + t • h) h * (1 / p) * powerSum p (v + t • h) ^ (1 / p - 1) =
      normSlope p (v + t • h) h := by
    unfold normSlope
    field_simp
  convert hh using 1
  · rfl
  · exact he.symm


theorem hasDerivAt_normSlope_line {p : ℝ} (hp : 4 < p) (v h : ι → ℝ) (t : ℝ)
    (hv : v + t • h ≠ 0) :
    HasDerivAt (fun s : ℝ ↦ normSlope p (v + s • h) h) (normHessian p (v + t • h) h) t := by
  have hp0 : 0 < p := by linarith
  have hS := powerSum_pos hp0 hv
  have hh := ((hasDerivAt_powerSum_line (by linarith) v h t).rpow_const (p := 1 / p - 1)
    (Or.inl hS.ne')).mul (hasDerivAt_powerPair_line hp v h t)
  have hpow : powerSum p (v + t • h) ^ (1 / p - 1 - 1) =
      powerSum p (v + t • h) ^ (1 / p - 1) / powerSum p (v + t • h) := by
    rw [Real.rpow_sub hS, Real.rpow_one]
  have he : (p * powerPair p (v + t • h) h * (1 / p - 1) *
      powerSum p (v + t • h) ^ (1 / p - 1 - 1)) * powerPair p (v + t • h) h +
      powerSum p (v + t • h) ^ (1 / p - 1) * ((p - 1) * powerQuad p (v + t • h) h) =
        normHessian p (v + t • h) h := by
    rw [normHessian, powerResidual_radial (by linarith) _ _ hv, hpow]
    field_simp
    ring
  rwa [he] at hh


theorem powerPair_sub_smul {p : ℝ} (hp : 2 < p) (v h : ι → ℝ) (a : ℝ) :
    powerPair p v (h - a • v) = powerPair p v h - a * powerSum p v := by
  rw [← powerQuad_self hp v]
  simp only [powerPair, powerQuad, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
    Finset.mul_sum, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ ↦ by ring


theorem normHessian_sub_smul {p : ℝ} (hp : 2 < p) (v h : ι → ℝ) (hv : v ≠ 0) (a : ℝ) :
    normHessian p v (h - a • v) = normHessian p v h := by
  simp only [normHessian, powerResidual_radial hp v _ hv, powerPair_sub_smul hp]
  congr 1
  have hquad : powerQuad p v (h - a • v) = powerResidual p v h a := rfl
  rw [hquad, powerResidual_eq hp]
  field_simp [(powerSum_pos (by linarith : 0 < p) hv).ne']
  ring


theorem powerSum_root_pred {p : ℝ} (hp : 0 < p) (v : ι → ℝ) :
    powerSum p v ^ (1 / p - 1) = (lpNorm p v ^ (p - 1))⁻¹ := by
  rw [powerSum_eq_lpNorm_rpow hp, ← Real.rpow_mul (lpNorm_nonneg p v),
    show p * (1 / p - 1) = -(p - 1) by field_simp; ring,
    Real.rpow_neg (lpNorm_nonneg p v)]


theorem normHessian_eq_div {p : ℝ} (hp : 0 < p) (v h : ι → ℝ) :
    normHessian p v h = (p - 1) / lpNorm p v ^ (p - 1) *
      powerResidual p v h (radialCoefficient p v h) := by
  rw [normHessian, powerSum_root_pred hp]
  rfl

end Norm

theorem euclideanSq_nonneg (v : Fin 3 → ℝ) : 0 ≤ euclideanSq v :=
  Finset.sum_nonneg fun i _ ↦ sq_nonneg (v i)


theorem frobeniusSq_nonneg (X : Triple) : 0 ≤ frobeniusSq X :=
  Finset.sum_nonneg fun j _ ↦ euclideanSq_nonneg (X j)


theorem euclideanSq_add_le (u v : Fin 3 → ℝ) :
    euclideanSq (u + v) ≤ 2 * euclideanSq u + 2 * euclideanSq v := by
  simp only [euclideanSq, Finset.mul_sum, ← Finset.sum_add_distrib, Pi.add_apply]
  exact Finset.sum_le_sum fun i _ ↦ by nlinarith [sq_nonneg (u i - v i)]


theorem euclideanSq_neg (v : Fin 3 → ℝ) : euclideanSq (-v) = euclideanSq v := by
  simp [euclideanSq]


theorem euclideanSq_sub_le (u v : Fin 3 → ℝ) :
    euclideanSq (u - v) ≤ 2 * euclideanSq u + 2 * euclideanSq v := by
  simpa only [sub_eq_add_neg, euclideanSq_neg] using euclideanSq_add_le u (-v)


theorem euclideanSq_smul (a : ℝ) (v : Fin 3 → ℝ) :
    euclideanSq (a • v) = a ^ 2 * euclideanSq v := by
  simp only [euclideanSq, Pi.smul_apply, smul_eq_mul, mul_pow, Finset.mul_sum]


theorem euclideanSq_total_le (X : Triple) : euclideanSq (totalTriple X) ≤ 3 * frobeniusSq X := by
  have hi (i : Fin 3) : ((∑ j, X j i) ^ 2) ≤ 3 * ∑ j, (X j i) ^ 2 := by
    simpa using Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ : Fin 3 ↦ (1 : ℝ)) (fun j ↦ X j i)
  calc
    _ ≤ ∑ i, 3 * ∑ j, (X j i) ^ 2 := Finset.sum_le_sum fun i _ ↦ hi i
    _ = _ := by
      simp only [frobeniusSq, euclideanSq, ← Finset.mul_sum]
      rw [Finset.sum_comm]


theorem lpNorm_pred_le_three_mul {p M : ℝ} (hp : 1 < p) (hM : 0 ≤ M)
    (v : Fin 3 → ℝ) (hv : ∀ i, |v i| ≤ M) :
    lpNorm p v ^ (p - 1) ≤ 3 * M ^ (p - 1) := by
  have hp0 := zero_lt_one.trans hp
  have hN := lpNorm_le_card_root_mul hp0 hM v hv
  simp only [Fintype.card_fin, Nat.cast_ofNat] at hN
  have hpower := Real.rpow_le_rpow (lpNorm_nonneg p v) hN (by linarith : 0 ≤ p - 1)
  rw [Real.mul_rpow (by positivity) hM, ← Real.rpow_mul (by norm_num)] at hpower
  have he : 1 / p * (p - 1) = 1 - 1 / p := by field_simp
  rw [he] at hpower
  have hthree : (3 : ℝ) ^ (1 - 1 / p) ≤ 3 := by
    have h := Real.rpow_le_rpow_of_exponent_le (x := (3 : ℝ)) (by norm_num)
      (show 1 - 1 / p ≤ 1 by have := one_div_nonneg.mpr hp0.le; linarith)
    simpa only [Real.rpow_one] using h
  exact hpower.trans (mul_le_mul_of_nonneg_right hthree (Real.rpow_nonneg hM _))



section Generic
noncomputable def lowerCoefficient (p m M : ℝ) : ℝ :=
  (p - 1) * m ^ (p - 2) / (3 * M ^ (p - 1))

theorem normHessian_lower_generic {p : ℝ} (hp : 2 < p) (v h : Fin 3 → ℝ) (m M : ℝ) (hm : 0 < m) (hM : 0 < M)
    (hlo : ∀ i, m ≤ |v i|) (hhi : ∀ i, |v i| ≤ M) :
    lowerCoefficient p m M * euclideanSq (h - radialCoefficient p v h • v) ≤
      normHessian p v h := by
  have hp0 : 0 < p := by linarith
  have hpred : 0 ≤ p - 1 := by linarith
  have hv : v ≠ 0 := by
    intro hv
    have hh := hlo 0
    simp only [hv, Pi.zero_apply, abs_zero] at hh
    linarith
  have hN := lpNorm_pos hp0 hv
  have hden := lpNorm_pred_le_three_mul (p := p) (by linarith) hM.le v hhi
  have hweight : (m : ℝ) ^ (p - 2) *
      euclideanSq (h - radialCoefficient p v h • v) ≤
        powerResidual p v h (radialCoefficient p v h) := by
    simp only [euclideanSq, powerResidual, Finset.mul_sum, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    apply Finset.sum_le_sum
    intro i _
    exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hm.le (hlo i) (by linarith))
      (sq_nonneg _)
  have hcoefficient : lowerCoefficient p m M ≤
      ((p - 1) / lpNorm p v ^ (p - 1)) * (m : ℝ) ^ (p - 2) := by
    have hh := div_le_div_of_nonneg_left
      (show 0 ≤ (p - 1) * (m : ℝ) ^ (p - 2) by positivity)
      (Real.rpow_pos_of_pos hN _) hden
    change (p - 1) * m ^ (p - 2) / (3 * M ^ (p - 1)) ≤ _
    calc
      _ ≤ ((p - 1) * (m : ℝ) ^ (p - 2)) / lpNorm p v ^ (p - 1) := hh
      _ = _ := by ring
  rw [normHessian_eq_div hp0]
  calc
    _ ≤ (((p - 1) / lpNorm p v ^ (p - 1)) * (m : ℝ) ^ (p - 2)) *
        euclideanSq (h - radialCoefficient p v h • v) :=
      mul_le_mul_of_nonneg_right hcoefficient (euclideanSq_nonneg _)
    _ = ((p - 1) / lpNorm p v ^ (p - 1)) *
        ((m : ℝ) ^ (p - 2) * euclideanSq (h - radialCoefficient p v h • v)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hweight (by positivity)



theorem normHessian_upper_canceled {p : ℝ} (hp : 2 < p)
    (v h : Fin 3 → ℝ) (k : Fin 3) (m M : ℝ) (hm : 0 < m) (hM : 0 ≤ M)
    (hk : m ≤ |v k|) (hi : ∀ i, i ≠ k → |v i| ≤ M) :
    normHessian p v h ≤
      ((p - 1) * M ^ (p - 2) / m ^ (p - 1)) *
        (∑ i ∈ Finset.univ.erase k, (h i - h k / v k * v i) ^ 2) := by
  have hp0 : 0 < p := by linarith
  have hpred : 0 ≤ p - 1 := by linarith
  have hkv : v k ≠ 0 := by
    intro he
    simp only [he, abs_zero] at hk
    linarith
  have hv : v ≠ 0 := by intro he; apply hkv; simp [he]
  have hN := lpNorm_pos hp0 hv
  have hlarge : m ≤ lpNorm p v := hk.trans (norm_apply_le_lpNorm (by linarith) v k)
  have hden : m ^ (p - 1) ≤ lpNorm p v ^ (p - 1) :=
    Real.rpow_le_rpow hm.le hlarge (by linarith)
  have hres : powerResidual p v h (h k / v k) ≤
      M ^ (p - 2) * (∑ i ∈ Finset.univ.erase k, (h i - h k / v k * v i) ^ 2) := by
    have hz : |v k| ^ (p - 2) * (h k - h k / v k * v k) ^ 2 = 0 := by
      simp [div_mul_cancel₀ _ hkv]
    rw [powerResidual, ← Finset.sum_erase_add _ _ (Finset.mem_univ k), hz, add_zero,
      Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi'
    exact mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow (abs_nonneg _) (hi i (Finset.mem_erase.mp hi').1) (by linarith))
      (sq_nonneg _)
  have hcoef : (p - 1) / lpNorm p v ^ (p - 1) ≤ (p - 1) / m ^ (p - 1) :=
    div_le_div_of_nonneg_left (by linarith) (Real.rpow_pos_of_pos hm _) hden
  have hmin := normHessian_le_residual hp v h hv (h k / v k)
  rw [powerSum_root_pred hp0] at hmin
  change normHessian p v h ≤
    (p - 1) / lpNorm p v ^ (p - 1) * powerResidual p v h (h k / v k) at hmin
  calc
    _ ≤ _ := hmin
    _ ≤ ((p - 1) / lpNorm p v ^ (p - 1)) *
        (M ^ (p - 2) * (∑ i ∈ Finset.univ.erase k, (h i - h k / v k * v i) ^ 2)) :=
      mul_le_mul_of_nonneg_left hres (by positivity)
    _ ≤ ((p - 1) / m ^ (p - 1)) *
        (M ^ (p - 2) * (∑ i ∈ Finset.univ.erase k, (h i - h k / v k * v i) ^ 2)) :=
      mul_le_mul_of_nonneg_right hcoef (mul_nonneg (Real.rpow_nonneg hM _)
        (Finset.sum_nonneg fun i _ ↦ sq_nonneg _))
    _ = _ := by ring
end Generic

end Hl50CvxNorm

set_option autoImplicit false
namespace Hl50CvxGeometry
open HlawkaSchatten.DiagonalConstruction

/-- Diagonal magnitudes lie in `[6894/10000, 111/100]`, off-diagonals in `[8091/10000, 111/100]`. -/
def asymmetricBox : Set Triple := {X | ∀ j i,
  if j = i then -(111 / 100 : ℝ) ≤ X j i ∧ X j i ≤ -(6894 / 10000 : ℝ)
  else (8091 / 10000 : ℝ) ≤ X j i ∧ X j i ≤ (111 / 100 : ℝ)}

theorem column_total_bounds (X : Triple) (hX : X ∈ asymmetricBox) (i : Fin 3) :
    (2541 / 5000 : ℝ) ≤ ∑ j, X j i ∧ ∑ j, X j i ≤ 7653 / 5000 := by
  have h0 := hX 0 i
  have h1 := hX 1 i
  have h2 := hX 2 i
  fin_cases i <;> norm_num [Fin.sum_univ_three, Fin.ext_iff] at * <;> constructor <;> linarith!

end Hl50CvxGeometry

set_option autoImplicit false

namespace Hl50CvxCoefficients

noncomputable def lowerTotal (p : ℝ) : ℝ :=
  (p - 1) * (2541/5000 : ℝ) ^ (p - 2) /
    (3 * (7653/5000 : ℝ) ^ (p - 1))

noncomputable def lowerColumn (p : ℝ) : ℝ :=
  (p - 1) * (3447/5000 : ℝ) ^ (p - 2) /
    (3 * (111/100 : ℝ) ^ (p - 1))

noncomputable def upperPair (p : ℝ) : ℝ :=
  (9 / 8) * (p - 1) * (2103/5000 : ℝ) ^ (p - 2) /
    (8091/5000 : ℝ) ^ (p - 1)

theorem total_ratio (p : ℝ) :
    upperPair p = lowerTotal p * (22959/7192) *
      (1788251/2284359 : ℝ) ^ (p - 2) := by
  have hM : (7653/5000 : ℝ) ^ (p - 1) =
      (7653/5000 : ℝ) ^ (p - 2) * (7653/5000) := by
    rw [← Real.rpow_add_one (by norm_num)]
    congr 1
    ring
  have hL : (8091/5000 : ℝ) ^ (p - 1) =
      (8091/5000 : ℝ) ^ (p - 2) * (8091/5000) := by
    rw [← Real.rpow_add_one (by norm_num)]
    congr 1
    ring
  have hbase : (1788251/2284359 : ℝ) ^ (p - 2) =
      ((2103/5000 : ℝ) ^ (p - 2) * (7653/5000 : ℝ) ^ (p - 2)) /
        ((8091/5000 : ℝ) ^ (p - 2) * (2541/5000 : ℝ) ^ (p - 2)) := by
    rw [show (1788251/2284359 : ℝ) =
      ((2103/5000) * (7653/5000)) / ((8091/5000) * (2541/5000)) by norm_num,
      Real.div_rpow (by norm_num) (by norm_num),
      Real.mul_rpow (by norm_num) (by norm_num), Real.mul_rpow (by norm_num) (by norm_num)]
  rw [upperPair, lowerTotal, hM, hL, hbase]
  field_simp
  ring

theorem column_ratio (p : ℝ) :
    upperPair p = lowerColumn p * (8325/3596) *
      (1296850/3098853 : ℝ) ^ (p - 2) := by
  have hM : (111/100 : ℝ) ^ (p - 1) =
      (111/100 : ℝ) ^ (p - 2) * (111/100) := by
    rw [← Real.rpow_add_one (by norm_num)]
    congr 1
    ring
  have hL : (8091/5000 : ℝ) ^ (p - 1) =
      (8091/5000 : ℝ) ^ (p - 2) * (8091/5000) := by
    rw [← Real.rpow_add_one (by norm_num)]
    congr 1
    ring
  have hbase : (1296850/3098853 : ℝ) ^ (p - 2) =
      ((2103/5000 : ℝ) ^ (p - 2) * (111/100 : ℝ) ^ (p - 2)) /
        ((8091/5000 : ℝ) ^ (p - 2) * (3447/5000 : ℝ) ^ (p - 2)) := by
    rw [show (1296850/3098853 : ℝ) =
      ((2103/5000) * (111/100)) / ((8091/5000) * (3447/5000)) by norm_num,
      Real.div_rpow (by norm_num) (by norm_num),
      Real.mul_rpow (by norm_num) (by norm_num), Real.mul_rpow (by norm_num) (by norm_num)]
  rw [upperPair, lowerColumn, hM, hL, hbase]
  field_simp
  ring

theorem lowerTotal_pos {p : ℝ} (hp : 1 < p) : 0 < lowerTotal p := by
  unfold lowerTotal
  positivity

theorem lowerColumn_pos {p : ℝ} (hp : 1 < p) : 0 < lowerColumn p := by
  unfold lowerColumn
  positivity

/-- For `p ∈ [50, 62]`, a base `r ≤ q < 1` gives `r ^ (p - 2) ≤ q ^ 48`. -/
theorem rpow_le_pow48 {r q p : ℝ} (hr : 0 ≤ r) (hrq : r ≤ q) (hq0 : 0 < q) (hq1 : q ≤ 1)
    (hp : 50 ≤ p) : r ^ (p - 2) ≤ q ^ (48 : ℕ) := by
  have h1 := Real.rpow_le_rpow hr hrq (show 0 ≤ p - 2 by linarith)
  have h2 := Real.rpow_le_rpow_of_exponent_ge hq0 hq1 (show (48 : ℝ) ≤ p - 2 by linarith)
  have h3 : q ^ (48 : ℝ) = q ^ (48 : ℕ) := by
    rw [← Real.rpow_natCast]
    norm_num
  rw [← h3]
  exact h1.trans h2

theorem total_comparison {p : ℝ} (hp : 50 ≤ p) (hp' : p ≤ 62) :
    7 * (p / 2) * upperPair p < lowerTotal p := by
  have hl := lowerTotal_pos (show 1 < p by linarith)
  have hpow := rpow_le_pow48 (r := (1788251/2284359 : ℝ)) (q := 4 / 5) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hp
  have hratio : upperPair p ≤ lowerTotal p * ((16 / 5) * (4 / 5 : ℝ) ^ (48 : ℕ)) := by
    rw [total_ratio, mul_assoc]
    apply mul_le_mul_of_nonneg_left _ hl.le
    exact mul_le_mul (by norm_num) hpow (by positivity) (by norm_num)
  have hsmall : (7 : ℝ) * 31 * ((16 / 5) * (4 / 5 : ℝ) ^ (48 : ℕ)) < 1 := by norm_num
  have hc : 0 ≤ (16 / 5) * (4 / 5 : ℝ) ^ (48 : ℕ) := by positivity
  have hup := mul_le_mul_of_nonneg_left hratio (show 0 ≤ 7 * (p / 2) by linarith)
  have hlin : 7 * (p / 2) * (lowerTotal p * ((16 / 5) * (4 / 5 : ℝ) ^ (48 : ℕ))) ≤
      lowerTotal p * ((7 : ℝ) * 31 * ((16 / 5) * (4 / 5 : ℝ) ^ (48 : ℕ))) := by
    have := mul_le_mul_of_nonneg_left (show p / 2 ≤ 31 by linarith) (mul_nonneg hl.le hc)
    nlinarith
  have hfin := mul_lt_mul_of_pos_left hsmall hl
  linarith

theorem column_comparison {p : ℝ} (hp : 50 ≤ p) :
    2000 * upperPair p < (447 / 500 : ℝ) * lowerColumn p := by
  have hl := lowerColumn_pos (show 1 < p by linarith)
  have hpow := rpow_le_pow48 (r := (1296850/3098853 : ℝ)) (q := 1 / 2) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hp
  have hratio : upperPair p ≤ lowerColumn p * (3 * (1 / 2 : ℝ) ^ (48 : ℕ)) := by
    rw [column_ratio, mul_assoc]
    apply mul_le_mul_of_nonneg_left _ hl.le
    exact mul_le_mul (by norm_num) hpow (by positivity) (by norm_num)
  have hsmall : (2000 : ℝ) * (3 * (1 / 2 : ℝ) ^ (48 : ℕ)) < 447 / 500 := by norm_num
  have hup := mul_le_mul_of_nonneg_left hratio (show (0 : ℝ) ≤ 2000 by norm_num)
  have hfin := mul_lt_mul_of_pos_left hsmall hl
  nlinarith

end Hl50CvxCoefficients
set_option autoImplicit false
set_option maxHeartbeats 800000
namespace Hl50CvxCurvature
open HlawkaSchatten.DiagonalConstruction
open Hl50CvxCoefficients
open Hl50CvxNorm (normHessian_lower_generic normHessian_upper_canceled)
abbrev entryBox : Set Triple := Hl50CvxGeometry.asymmetricBox
theorem entryBox_off_lower {X : Triple} (hX : X ∈ entryBox)
    (j i : Fin 3) (hij : i ≠ j) : (8091/10000 : ℝ) ≤ X j i := by
  have h := hX j i
  simp only [if_neg (Ne.symm hij)] at h
  exact h.1
theorem entryBox_diag_upper {X : Triple} (hX : X ∈ entryBox) (j : Fin 3) :
    X j j ≤ -(6894/10000 : ℝ) := by
  have h := hX j j
  simp only [ite_true] at h
  exact h.2
theorem totalTriple_eq (X : Triple) : totalTriple X = X 0 + X 1 + X 2 := by
  simp [totalTriple, Fin.sum_univ_three]
theorem entryBox_column_bounds {X : Triple} (hX : X ∈ entryBox) (j i : Fin 3) :
    3447/5000 ≤ |X j i| ∧ |X j i| ≤ 111/100 := by
  have h := hX j i
  by_cases he : j = i
  · simp only [if_pos he] at h
    rw [abs_of_neg (by linarith : X j i < 0)]
    constructor <;> linarith
  · simp only [if_neg he] at h
    rw [abs_of_pos (by linarith : 0 < X j i)]
    constructor <;> linarith
theorem entryBox_total_bounds {X : Triple} (hX : X ∈ entryBox) (i : Fin 3) :
    2541/5000 ≤ totalTriple X i ∧ totalTriple X i ≤ 7653/5000 :=
  Hl50CvxGeometry.column_total_bounds X hX i
theorem entryBox_pair_large {X : Triple} (hX : X ∈ entryBox) (j : Fin 3) :
    8091/5000 ≤ |pairTriple X j j| := by
  have h0 := hX 0 j
  have h1 := hX 1 j
  have h2 := hX 2 j
  have hl : (8091/5000 : ℝ) ≤ pairTriple X j j := by
    fin_cases j <;> norm_num [pairTriple, Fin.ext_iff] at h0 h1 h2 ⊢ <;> linarith!
  exact hl.trans (le_abs_self _)
theorem entryBox_pair_small {X : Triple} (hX : X ∈ entryBox) (j i : Fin 3) (hij : i ≠ j) :
    |pairTriple X j i| ≤ 2103/5000 := by
  have h0 := hX 0 i
  have h1 := hX 1 i
  have h2 := hX 2 i
  fin_cases j <;> fin_cases i <;> first
  | exact (hij rfl).elim
  | norm_num [pairTriple, Fin.ext_iff, abs_le] at h0 h1 h2 ⊢
    constructor <;> linarith!
theorem entryBox_column_ne_zero {X : Triple} (hX : X ∈ entryBox) (j : Fin 3) : X j ≠ 0 := by
  intro he
  have h := (entryBox_column_bounds hX j 0).1
  norm_num [he] at h
theorem entryBox_total_ne_zero {X : Triple} (hX : X ∈ entryBox) : totalTriple X ≠ 0 := by
  intro he
  have h := (entryBox_total_bounds hX 0).1
  norm_num [he] at h
theorem entryBox_pair_ne_zero {X : Triple} (hX : X ∈ entryBox) (j : Fin 3) : pairTriple X j ≠ 0 := by
  intro he
  have h := entryBox_pair_large hX j
  norm_num [he] at h

theorem pair_hessian_canceled_bound {p : ℝ} (hp : 2 < p)
    {X : Triple} (hX : X ∈ entryBox) (Z : Triple) (j : Fin 3) :
    normHessian p (pairTriple X j) (pairTriple Z j) ≤ upperPair p *
      (∑ i ∈ Finset.univ.erase j,
        (pairTriple Z j i - pairTriple Z j j / pairTriple X j j * pairTriple X j i) ^ 2) := by
  have h := normHessian_upper_canceled hp (pairTriple X j) (pairTriple Z j) j
    (8091/5000) (2103/5000) (by norm_num) (by norm_num)
    (entryBox_pair_large hX j) (entryBox_pair_small hX j)
  have hc : (p - 1) * (2103/5000 : ℝ) ^ (p - 2) / (8091/5000 : ℝ) ^ (p - 1) ≤
      upperPair p := by
    unfold upperPair
    have hpred : 0 ≤ p - 1 := by linarith
    have hnon : 0 ≤ (p - 1) * (2103/5000 : ℝ) ^ (p - 2) /
        (8091/5000 : ℝ) ^ (p - 1) := by positivity
    calc
      _ ≤ (9 / 8) * ((p - 1) * (2103/5000 : ℝ) ^ (p - 2) /
          (8091/5000 : ℝ) ^ (p - 1)) := by nlinarith [hnon]
      _ = _ := by ring
  exact h.trans (mul_le_mul_of_nonneg_right hc (Finset.sum_nonneg fun i _ ↦ sq_nonneg _))

end Hl50CvxCurvature
set_option autoImplicit false

namespace Hl50CvxGeometry

/-! Recover coefficient spread from two coordinates of a cyclic-box image.
The total-coordinate terms disappear from the antisymmetric combination.
This preserves geometry that the earlier uniform inverse estimate discarded.
-/

theorem extreme_pair_separation
    (m t0 t1 x00 x10 x20 x01 x11 x21 a0 a1 a2 : ℝ)
    (ht0 : 0 ≤ t0) (ht1 : 0 ≤ t1)
    (hrow0 : t0 = x00 + x10 + x20)
    (hrow1 : t1 = x01 + x11 + x21)
    (h00 : x00 ≤ -m) (h11 : x11 ≤ -m)
    (h10 : m ≤ x10) (h01 : m ≤ x01)
    (ha1 : a1 ≤ a2) (ha0 : a2 ≤ a0) :
    m * (t0 + t1) * (a0 - a1) ≤
      t0 * (x01 * a0 + x11 * a1 + x21 * a2) -
        t1 * (x00 * a0 + x10 * a1 + x20 * a2) := by
  have hgap : 0 ≤ a0 - a1 := by linarith
  by_cases hc : 0 ≤ t0 * x21 - t1 * x20
  · have hbase : m * (t0 + t1) ≤ t0 * x01 - t1 * x00 := by
      nlinarith [mul_nonneg ht0 (sub_nonneg.mpr h01),
        mul_nonneg ht1 (show 0 ≤ -x00 - m by linarith)]
    have hprod := mul_le_mul_of_nonneg_right hbase hgap
    have htail := mul_nonneg hc (sub_nonneg.mpr ha1)
    have heq : t0 * (x01 * a0 + x11 * a1 + x21 * a2) -
        t1 * (x00 * a0 + x10 * a1 + x20 * a2) =
        (t0 * x01 - t1 * x00) * (a0 - a1) +
          (t0 * x21 - t1 * x20) * (a2 - a1) := by
      rw [hrow0, hrow1]
      ring
    rw [heq]
    linarith
  · have hc' : 0 ≤ -(t0 * x21 - t1 * x20) := by linarith
    have hbase : m * (t0 + t1) ≤ t1 * x10 - t0 * x11 := by
      nlinarith [mul_nonneg ht1 (sub_nonneg.mpr h10),
        mul_nonneg ht0 (show 0 ≤ -x11 - m by linarith)]
    have hprod := mul_le_mul_of_nonneg_right hbase hgap
    have htail := mul_nonneg hc' (sub_nonneg.mpr ha0)
    have heq : t0 * (x01 * a0 + x11 * a1 + x21 * a2) -
        t1 * (x00 * a0 + x10 * a1 + x20 * a2) =
        (t1 * x10 - t0 * x11) * (a0 - a1) -
          (t0 * x21 - t1 * x20) * (a0 - a2) := by
      rw [hrow0, hrow1]
      ring
    rw [heq]
    linarith

theorem total_pair_shape (s t : ℝ)
    (hslo : 2541/5000 ≤ s) (hshi : s ≤ 7653/5000)
    (htlo : 2541/5000 ≤ t) (hthi : t ≤ 7653/5000) :
    s ^ 2 + t ^ 2 ≤ (4/3 : ℝ) * (3447/5000) ^ 2 * (s + t) ^ 2 := by
  have ha : 0 ≤ (7653/5000 : ℝ) * s - (2541/5000) * t := by
    nlinarith
  have hb : 0 ≤ (7653/5000 : ℝ) * t - (2541/5000) * s := by
    nlinarith
  have hprod := mul_nonneg ha hb
  nlinarith [sq_nonneg (s + t)]

theorem spread_from_residual_pair (t0 t1 r0 r1 gap : ℝ)
    (ht0lo : 2541/5000 ≤ t0) (ht0hi : t0 ≤ 7653/5000)
    (ht1lo : 2541/5000 ≤ t1) (ht1hi : t1 ≤ 7653/5000)
    (hgap : 0 ≤ gap)
    (hseparate : (3447/5000 : ℝ) * (t0 + t1) * gap ≤ t0 * r1 - t1 * r0) :
    gap ^ 2 ≤ (4/3 : ℝ) * (r0 ^ 2 + r1 ^ 2) := by
  have hleft : 0 ≤ (3447/5000 : ℝ) * (t0 + t1) * gap := by positivity
  have hsquare := mul_self_le_mul_self hleft hseparate
  have hcauchy : (t0 * r1 - t1 * r0) ^ 2 ≤
      (t0 ^ 2 + t1 ^ 2) * (r0 ^ 2 + r1 ^ 2) := by
    nlinarith [sq_nonneg (t0 * r0 + t1 * r1)]
  have hshape := total_pair_shape t0 t1 ht0lo ht0hi ht1lo ht1hi
  have hbound := mul_le_mul_of_nonneg_right hshape
    (show 0 ≤ r0 ^ 2 + r1 ^ 2 by positivity)
  have hscale : 0 < (3447/5000 : ℝ) ^ 2 * (t0 + t1) ^ 2 := by positivity
  apply (mul_le_mul_iff_right₀ hscale).mp
  nlinarith

theorem spread_with_error (t0 t1 d0 d1 u0 u1 gap : ℝ)
    (ht0lo : 2541/5000 ≤ t0) (ht0hi : t0 ≤ 7653/5000)
    (ht1lo : 2541/5000 ≤ t1) (ht1hi : t1 ≤ 7653/5000)
    (hgap : 0 ≤ gap)
    (hseparate : (3447/5000 : ℝ) * (t0 + t1) * gap ≤
      t0 * (d1 - u1) - t1 * (d0 - u0)) :
    gap ^ 2 ≤ (101/75 : ℝ) * (d0 ^ 2 + d1 ^ 2) +
      (404/3 : ℝ) * (u0 ^ 2 + u1 ^ 2) := by
  have h := spread_from_residual_pair t0 t1 (d0 - u0) (d1 - u1) gap
    ht0lo ht0hi ht1lo ht1hi hgap hseparate
  have h0 : (d0 - u0) ^ 2 ≤ (101 / 100 : ℝ) * d0 ^ 2 + 101 * u0 ^ 2 := by
    nlinarith [sq_nonneg (d0 / 10 + 10 * u0)]
  have h1 : (d1 - u1) ^ 2 ≤ (101 / 100 : ℝ) * d1 ^ 2 + 101 * u1 ^ 2 := by
    nlinarith [sq_nonneg (d1 / 10 + 10 * u1)]
  nlinarith

theorem ordered_pair_difference_sum (a b c : ℝ) (h1 : b ≤ c) (h2 : c ≤ a) :
    (a - b) ^ 2 + (a - c) ^ 2 + (b - c) ^ 2 ≤ 2 * (a - b) ^ 2 := by
  nlinarith [mul_nonneg (sub_nonneg.mpr h1) (sub_nonneg.mpr h2)]

end Hl50CvxGeometry

theorem Hl50CvxGeometry.solution (t0 t1 r0 r1 gap : ℝ)
    (ht0lo : 2541/5000 ≤ t0) (ht0hi : t0 ≤ 7653/5000)
    (ht1lo : 2541/5000 ≤ t1) (ht1hi : t1 ≤ 7653/5000)
    (hgap : 0 ≤ gap)
    (hseparate : (3447/5000 : ℝ) * (t0 + t1) * gap ≤ t0 * r1 - t1 * r0) :
    gap ^ 2 ≤ (4/3 : ℝ) * (r0 ^ 2 + r1 ^ 2) :=
  Hl50CvxGeometry.spread_from_residual_pair t0 t1 r0 r1 gap
    ht0lo ht0hi ht1lo ht1hi hgap hseparate
set_option autoImplicit false

namespace Hl50CvxPairs

theorem weighted_component_bound (a b c d M : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : |c| ≤ M) (hd : |d| ≤ M) :
    |(b * c - a * d) / (a + b)| ≤ M := by
  have hab : 0 < a + b := by positivity
  rw [abs_div, abs_of_pos hab, div_le_iff₀ hab]
  calc
    |b * c - a * d| ≤ |b * c| + |a * d| := abs_sub _ _
    _ = b * |c| + a * |d| := by rw [abs_mul, abs_mul, abs_of_pos hb, abs_of_pos ha]
    _ ≤ b * M + a * M := by gcongr
    _ = M * (a + b) := by ring

theorem four_term_sq (a b c d : ℝ) :
    (a + b + c + d) ^ 2 ≤ 4 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - d),
    sq_nonneg (b - c), sq_nonneg (b - d), sq_nonneg (c - d)]

theorem error_component_sq (u v w z eta : ℝ) (heta : |eta| ≤ 1) :
    (u + v - eta * (w + z)) ^ 2 ≤ 4 * (u ^ 2 + v ^ 2 + w ^ 2 + z ^ 2) := by
  have he : eta ^ 2 ≤ 1 := by
    have hs := abs_le.mp heta
    nlinarith [sq_abs eta]
  have hw := mul_le_mul_of_nonneg_right he (sq_nonneg w)
  have hz := mul_le_mul_of_nonneg_right he (sq_nonneg z)
  have h := four_term_sq u v (-eta * w) (-eta * z)
  nlinarith

theorem two_error_components_sq (u0 u1 u2 v0 v1 v2 eta0 eta1 : ℝ)
    (h0 : |eta0| ≤ 1) (h1 : |eta1| ≤ 1) :
    (u0 + v0 - eta0 * (u2 + v2)) ^ 2 +
      (u1 + v1 - eta1 * (u2 + v2)) ^ 2 ≤
      8 * (u0 ^ 2 + u1 ^ 2 + u2 ^ 2 + v0 ^ 2 + v1 ^ 2 + v2 ^ 2) := by
  have he0 := error_component_sq u0 v0 u2 v2 eta0 h0
  have he1 := error_component_sq u1 v1 u2 v2 eta1 h1
  nlinarith [sq_nonneg u0, sq_nonneg u1, sq_nonneg v0, sq_nonneg v1]

theorem young_pair_sq (r e : ℝ) :
    (r + e) ^ 2 ≤ (101 / 100 : ℝ) * r ^ 2 + 101 * e ^ 2 := by
  nlinarith [sq_nonneg (r / 10 - 10 * e)]

/-- The rational constants close the proposed weighted Hessian estimate.
Its premises still have to be supplied for the actual norm Hessians. -/
theorem weighted_pair_bound (P dp D U A R E : ℝ)
    (hdp : 0 ≤ dp) (hD : 0 ≤ D) (hU : 0 ≤ U)
    (hspread : A ≤ (101/75 : ℝ) * D + (404 : ℝ) * U)
    (hdiff : R ≤ 2 * A) (herror : E ≤ 16 * U)
    (hpair : P ≤ dp * ((101 / 100 : ℝ) * 2 * (111/100 : ℝ) ^ 2 * R + 101 * E)) :
    P ≤ dp * (7 * D + 4000 * U) := by
  have hbound : (101 / 100 : ℝ) * 2 * (111/100 : ℝ) ^ 2 * R + 101 * E ≤
      7 * D + 4000 * U := by
    nlinarith
  exact hpair.trans (mul_le_mul_of_nonneg_left hbound hdp)

end Hl50CvxPairs

theorem Hl50CvxPairs.solution (P dp D U A R E : ℝ)
    (hdp : 0 ≤ dp) (hD : 0 ≤ D) (hU : 0 ≤ U)
    (hspread : A ≤ (101/75 : ℝ) * D + (404 : ℝ) * U)
    (hdiff : R ≤ 2 * A) (herror : E ≤ 16 * U)
    (hpair : P ≤ dp * ((101 / 100 : ℝ) * 2 * (111/100 : ℝ) ^ 2 * R + 101 * E)) :
    P ≤ dp * (7 * D + 4000 * U) :=
  Hl50CvxPairs.weighted_pair_bound P dp D U A R E hdp hD hU
    hspread hdiff herror hpair
set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Hl50CvxCurvature
open HlawkaSchatten.DiagonalConstruction
open Hl50CvxGeometry
open Hl50CvxNorm (euclideanSq_total_le)

def pairLeft : Fin 3 → Fin 3 := ![1, 0, 0]
def pairRight : Fin 3 → Fin 3 := ![2, 2, 1]
def pairDifference (a : Fin 3 → ℝ) : Fin 3 → ℝ := fun j ↦ a (pairLeft j) - a (pairRight j)

theorem pairTriple_eq_indices (X : Triple) (j : Fin 3) :
    pairTriple X j = X (pairLeft j) + X (pairRight j) := by
  fin_cases j <;> rfl

theorem sum_three_distinct (v : Fin 3 → ℝ) (j k l : Fin 3)
    (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l) :
    (∑ i, v i) = v j + v k + v l := by
  fin_cases j <;> fin_cases k <;> fin_cases l <;>
    simp_all [Fin.sum_univ_three] <;> ring

theorem exists_ordered_indices (a : Fin 3 → ℝ) :
    ∃ j k l : Fin 3, j ≠ k ∧ j ≠ l ∧ k ≠ l ∧ a k ≤ a l ∧ a l ≤ a j := by
  by_cases h01 : a 0 ≤ a 1
  · by_cases h12 : a 1 ≤ a 2
    · exact ⟨2, 0, 1, by decide, by decide, by decide, h01, h12⟩
    · by_cases h02 : a 0 ≤ a 2
      · exact ⟨1, 0, 2, by decide, by decide, by decide, h02, le_of_not_ge h12⟩
      · exact ⟨1, 2, 0, by decide, by decide, by decide, le_of_not_ge h02, h01⟩
  · by_cases h02 : a 0 ≤ a 2
    · exact ⟨2, 1, 0, by decide, by decide, by decide, le_of_not_ge h01, h02⟩
    · by_cases h12 : a 1 ≤ a 2
      · exact ⟨0, 1, 2, by decide, by decide, by decide, h12, le_of_not_ge h02⟩
      · exact ⟨0, 2, 1, by decide, by decide, by decide, le_of_not_ge h12, le_of_not_ge h01⟩

theorem pair_difference_ordered (a : Fin 3 → ℝ) (j k l : Fin 3)
    (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l) (hlo : a k ≤ a l) (hhi : a l ≤ a j) :
    (∑ i, pairDifference a i ^ 2) ≤ 2 * (a j - a k) ^ 2 := by
  have hs : (∑ i, pairDifference a i ^ 2) =
      (a j - a k) ^ 2 + (a j - a l) ^ 2 + (a k - a l) ^ 2 := by
    fin_cases j <;> fin_cases k <;> fin_cases l <;>
      simp_all [pairDifference, pairLeft, pairRight, Fin.sum_univ_three] <;> ring
  rw [hs]
  exact ordered_pair_difference_sum _ _ _ hlo hhi

theorem two_coordinates_sq_le (v : Fin 3 → ℝ) (j k : Fin 3) (hjk : j ≠ k) :
    v j ^ 2 + v k ^ 2 ≤ euclideanSq v := by
  have h := Finset.sum_le_sum_of_subset_of_nonneg
    (s := {j, k}) (t := Finset.univ) (f := fun i ↦ v i ^ 2)
    (Finset.subset_univ _) (fun i _ _ ↦ sq_nonneg _)
  simpa [euclideanSq, Finset.sum_pair hjk] using h

theorem ordered_spread_bound {X : Triple} (hX : X ∈ entryBox)
    (a : Fin 3 → ℝ) (b : ℝ) (U : Triple) (D : Fin 3 → ℝ)
    (hD : D = applyTriple X a + totalTriple U - b • totalTriple X)
    (j k l : Fin 3) (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l)
    (hlo : a k ≤ a l) (hhi : a l ≤ a j) :
    (a j - a k) ^ 2 ≤ (101/75 : ℝ) * euclideanSq D +
      (404 : ℝ) * frobeniusSq U := by
  have hjj : X j j ≤ -(3447/5000 : ℝ) := by
    have h := entryBox_diag_upper hX j
    linarith
  have hkk : X k k ≤ -(3447/5000 : ℝ) := by
    have h := entryBox_diag_upper hX k
    linarith
  have hkj : (3447/5000 : ℝ) ≤ X k j := by
    have h := entryBox_off_lower hX k j hjk
    linarith
  have hjk' : (3447/5000 : ℝ) ≤ X j k := by
    have h := entryBox_off_lower hX j k (Ne.symm hjk)
    linarith
  have htj := entryBox_total_bounds hX j
  have htk := entryBox_total_bounds hX k
  have hsep := extreme_pair_separation (3447/5000) (totalTriple X j) (totalTriple X k)
    (X j j) (X k j) (X l j) (X j k) (X k k) (X l k) (a j) (a k) (a l)
    (by linarith) (by linarith)
    (sum_three_distinct (fun i ↦ X i j) j k l hjk hjl hkl)
    (sum_three_distinct (fun i ↦ X i k) j k l hjk hjl hkl)
    hjj hkk hkj hjk' hlo hhi
  have happly (i : Fin 3) : applyTriple X a i = X j i * a j + X k i * a k + X l i * a l := by
    rw [applyTriple, sum_three_distinct _ j k l hjk hjl hkl]
    ring
  have hc : totalTriple X j * (D k - totalTriple U k) -
      totalTriple X k * (D j - totalTriple U j) =
      totalTriple X j * (X j k * a j + X k k * a k + X l k * a l) -
      totalTriple X k * (X j j * a j + X k j * a k + X l j * a l) := by
    rw [hD]
    simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, happly]
    ring
  have hs := spread_with_error (totalTriple X j) (totalTriple X k) (D j) (D k)
    (totalTriple U j) (totalTriple U k) (a j - a k) htj.1 htj.2 htk.1 htk.2
    (by linarith) (by rw [hc]; exact hsep)
  have hd := two_coordinates_sq_le D j k hjk
  have hu := two_coordinates_sq_le (totalTriple U) j k hjk
  have hut := euclideanSq_total_le U
  nlinarith

theorem coefficient_differences_bound {X : Triple} (hX : X ∈ entryBox)
    (a : Fin 3 → ℝ) (b : ℝ) (U : Triple) (D : Fin 3 → ℝ)
    (hD : D = applyTriple X a + totalTriple U - b • totalTriple X) :
    (∑ i, pairDifference a i ^ 2) ≤ 2 *
      ((101/75 : ℝ) * euclideanSq D + (404 : ℝ) * frobeniusSq U) := by
  obtain ⟨j,k,l,hjk,hjl,hkl,hlo,hhi⟩ := exists_ordered_indices a
  have hs := ordered_spread_bound hX a b U D hD j k l hjk hjl hkl hlo hhi
  have hd := pair_difference_ordered a j k l hjk hjl hkl hlo hhi
  linarith

end Hl50CvxCurvature
set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Hl50CvxCurvature
open HlawkaSchatten.DiagonalConstruction
open Hl50CvxNorm
open Hl50CvxCoefficients Hl50CvxPairs

noncomputable def pairRadial (X : Triple) (a : Fin 3 → ℝ) (j i : Fin 3) : ℝ :=
  pairDifference a j *
    ((X (pairRight j) j * X (pairLeft j) i - X (pairLeft j) j * X (pairRight j) i) /
      (X (pairLeft j) j + X (pairRight j) j))

noncomputable def pairError (X U : Triple) (j i : Fin 3) : ℝ :=
  pairTriple U j i - (pairTriple X j i / pairTriple X j j) * pairTriple U j j

noncomputable def canceledPairSq (X Z : Triple) (j : Fin 3) : ℝ :=
  ∑ i ∈ Finset.univ.erase j,
    (pairTriple Z j i - pairTriple Z j j / pairTriple X j j * pairTriple X j i) ^ 2

noncomputable def radialPairSq (X : Triple) (a : Fin 3 → ℝ) (j : Fin 3) : ℝ :=
  ∑ i ∈ Finset.univ.erase j, pairRadial X a j i ^ 2

noncomputable def errorPairSq (X U : Triple) (j : Fin 3) : ℝ :=
  ∑ i ∈ Finset.univ.erase j, pairError X U j i ^ 2

theorem pair_indices_off (j : Fin 3) : j ≠ pairLeft j ∧ j ≠ pairRight j := by
  fin_cases j <;> decide

theorem canceled_pair_decomposition {X : Triple} (hX : X ∈ entryBox)
    (Z U : Triple) (a : Fin 3 → ℝ) (hZ : ∀ j i, Z j i = a j * X j i + U j i)
    (j i : Fin 3) :
    pairTriple Z j i - pairTriple Z j j / pairTriple X j j * pairTriple X j i =
      pairRadial X a j i + pairError X U j i := by
  have ho := pair_indices_off j
  have hl := entryBox_off_lower hX (pairLeft j) j ho.1
  have hr := entryBox_off_lower hX (pairRight j) j ho.2
  have hden : X (pairLeft j) j + X (pairRight j) j ≠ 0 := by linarith
  simp only [pairRadial, pairError, pairDifference, pairTriple_eq_indices, Pi.add_apply, hZ]
  field_simp
  ring

theorem radial_pair_component_sq {X : Triple} (hX : X ∈ entryBox)
    (a : Fin 3 → ℝ) (j i : Fin 3) :
    pairRadial X a j i ^ 2 ≤ (111/100 : ℝ) ^ 2 * pairDifference a j ^ 2 := by
  have ho := pair_indices_off j
  have hl := entryBox_off_lower hX (pairLeft j) j ho.1
  have hr := entryBox_off_lower hX (pairRight j) j ho.2
  have hc := weighted_component_bound (X (pairLeft j) j) (X (pairRight j) j)
    (X (pairLeft j) i) (X (pairRight j) i) (111/100)
    (by linarith) (by linarith)
    (entryBox_column_bounds hX (pairLeft j) i).2
    (entryBox_column_bounds hX (pairRight j) i).2
  have hs := (sq_le_sq₀ (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 111/100)).mpr hc
  rw [sq_abs] at hs
  have hm := mul_le_mul_of_nonneg_left hs (sq_nonneg (pairDifference a j))
  simpa only [pairRadial, mul_pow, mul_comm] using hm

theorem radial_pair_sq_bound {X : Triple} (hX : X ∈ entryBox)
    (a : Fin 3 → ℝ) (j : Fin 3) :
    radialPairSq X a j ≤ 2 * (111/100 : ℝ) ^ 2 * pairDifference a j ^ 2 := by
  have hh := Finset.sum_le_sum (s := Finset.univ.erase j)
    (fun i _ ↦ radial_pair_component_sq hX a j i)
  simpa [radialPairSq, Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ j),
    mul_assoc] using hh

theorem error_pair_sq_bound {X : Triple} (hX : X ∈ entryBox)
    (U : Triple) (j : Fin 3) :
    errorPairSq X U j ≤ 8 * (euclideanSq (U (pairLeft j)) + euclideanSq (U (pairRight j))) := by
  have hlarge := entryBox_pair_large hX j
  have heta (i : Fin 3) (hij : i ≠ j) : |pairTriple X j i / pairTriple X j j| ≤ 1 := by
    rw [abs_div, div_le_iff₀ (by linarith : 0 < |pairTriple X j j|)]
    linarith [entryBox_pair_small hX j i hij]
  have hi (i : Fin 3) (hij : i ≠ j) : pairError X U j i ^ 2 ≤
      4 * (U (pairLeft j) i ^ 2 + U (pairRight j) i ^ 2 +
        U (pairLeft j) j ^ 2 + U (pairRight j) j ^ 2) := by
    simpa only [pairError, pairTriple_eq_indices, Pi.add_apply] using
      error_component_sq (U (pairLeft j) i) (U (pairRight j) i)
        (U (pairLeft j) j) (U (pairRight j) j) _ (heta i hij)
  have hh := Finset.sum_le_sum (s := Finset.univ.erase j)
    (fun i hi' ↦ hi i (Finset.mem_erase.mp hi').1)
  have hsL : (∑ i ∈ Finset.univ.erase j, U (pairLeft j) i ^ 2) + U (pairLeft j) j ^ 2 =
      euclideanSq (U (pairLeft j)) := Finset.sum_erase_add _ _ (Finset.mem_univ j)
  have hsR : (∑ i ∈ Finset.univ.erase j, U (pairRight j) i ^ 2) + U (pairRight j) j ^ 2 =
      euclideanSq (U (pairRight j)) := Finset.sum_erase_add _ _ (Finset.mem_univ j)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
    Finset.card_erase_of_mem (Finset.mem_univ j), Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul] at hh
  change errorPairSq X U j ≤ _ at hh
  norm_num only [Nat.reduceSub, Nat.cast_ofNat] at hh
  have hsL0 := Finset.sum_nonneg (s := Finset.univ.erase j) (fun i _ ↦ sq_nonneg (U (pairLeft j) i))
  have hsR0 := Finset.sum_nonneg (s := Finset.univ.erase j) (fun i _ ↦ sq_nonneg (U (pairRight j) i))
  linarith

theorem error_pairs_sq_bound {X : Triple} (hX : X ∈ entryBox) (U : Triple) :
    (∑ j, errorPairSq X U j) ≤ 16 * frobeniusSq U := by
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun j _ ↦ error_pair_sq_bound hX U j)
  have hs : (∑ j, 8 * (euclideanSq (U (pairLeft j)) + euclideanSq (U (pairRight j)))) =
      16 * frobeniusSq U := by
    simp only [pairLeft, pairRight, frobeniusSq, Fin.sum_univ_three]
    simp
    ring
  rwa [hs] at hh

theorem canceled_pair_sq_bound {X : Triple} (hX : X ∈ entryBox)
    (Z U : Triple) (a : Fin 3 → ℝ) (hZ : ∀ j i, Z j i = a j * X j i + U j i) (j : Fin 3) :
    canceledPairSq X Z j ≤ (101 / 100 : ℝ) * radialPairSq X a j + 101 * errorPairSq X U j := by
  unfold canceledPairSq radialPairSq errorPairSq
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  rw [canceled_pair_decomposition hX Z U a hZ j i]
  exact young_pair_sq _ _

theorem canceled_pairs_sq_bound {X : Triple} (hX : X ∈ entryBox)
    (Z U : Triple) (a : Fin 3 → ℝ) (b : ℝ) (D : Fin 3 → ℝ)
    (hZ : ∀ j i, Z j i = a j * X j i + U j i)
    (hD : D = applyTriple X a + totalTriple U - b • totalTriple X) :
    (∑ j, canceledPairSq X Z j) ≤ 7 * euclideanSq D + 4000 * frobeniusSq U := by
  have hr := Finset.sum_le_sum (s := Finset.univ) (fun j _ ↦ radial_pair_sq_bound hX a j)
  rw [← Finset.mul_sum] at hr
  have he := error_pairs_sq_bound hX U
  have hc := Finset.sum_le_sum (s := Finset.univ) (fun j _ ↦ canceled_pair_sq_bound hX Z U a hZ j)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at hc
  have hr' := mul_le_mul_of_nonneg_left hr (by norm_num : (0 : ℝ) ≤ 101 / 100)
  have hd := coefficient_differences_bound hX a b U D hD
  have hp : (∑ j, canceledPairSq X Z j) ≤ (1 : ℝ) *
      ((101 / 100 : ℝ) * 2 * (111/100 : ℝ) ^ 2 * (∑ j, pairDifference a j ^ 2) +
        101 * (∑ j, errorPairSq X U j)) := by linarith
  simpa only [one_mul] using weighted_pair_bound (∑ j, canceledPairSq X Z j) 1
    (euclideanSq D) (frobeniusSq U)
    ((101/75 : ℝ) * euclideanSq D + (404 : ℝ) * frobeniusSq U)
    (∑ j, pairDifference a j ^ 2) (∑ j, errorPairSq X U j)
    (by norm_num) (euclideanSq_nonneg D) (frobeniusSq_nonneg U) le_rfl hd he hp

theorem pair_hessian_sum_bound {p : ℝ} (hp : 2 < p)
    {X : Triple} (hX : X ∈ entryBox)
    (Z U : Triple) (a : Fin 3 → ℝ) (b : ℝ) (D : Fin 3 → ℝ)
    (hZ : ∀ j i, Z j i = a j * X j i + U j i)
    (hD : D = applyTriple X a + totalTriple U - b • totalTriple X) :
    (∑ j, normHessian p (pairTriple X j) (pairTriple Z j)) ≤
      upperPair p * (7 * euclideanSq D + 4000 * frobeniusSq U) := by
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun j _ ↦ pair_hessian_canceled_bound hp hX Z j)
  change (∑ j, normHessian p (pairTriple X j) (pairTriple Z j)) ≤
    ∑ j, upperPair p * canceledPairSq X Z j at hh
  rw [← Finset.mul_sum] at hh
  have hpred : 0 ≤ p - 1 := by linarith
  have hcoef : 0 ≤ upperPair p := by unfold upperPair; positivity
  exact hh.trans (mul_le_mul_of_nonneg_left (canceled_pairs_sq_bound hX Z U a b D hZ hD) hcoef)

end Hl50CvxCurvature
set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Hl50CvxCurvature
open HlawkaSchatten.DiagonalConstruction
open Hl50CvxNorm
open Hl50CvxCoefficients

theorem deficitHessian_nonneg {p K : ℝ} (hp : 50 ≤ p) (hp' : p ≤ 62)
    (hKlo : (457 / 1000 : ℝ) * p ≤ K) (hKhi : K ≤ p / 2)
    {X : Triple} (hX : X ∈ entryBox) (Z : Triple) :
    0 ≤ deficitHessian p K X Z := by
  have hp0 : 0 ≤ p := by linarith
  have hp1 : 1 < p := by linarith
  have hp2 : 2 < p := by linarith
  let a : Fin 3 → ℝ := fun j ↦ radialCoefficient p (X j) (Z j)
  let b := radialCoefficient p (totalTriple X) (totalTriple Z)
  let U : Triple := fun j ↦ Z j - a j • X j
  let D := totalTriple Z - b • totalTriple X
  have hZ : ∀ j i, Z j i = a j * X j i + U j i := by
    intro j i
    dsimp [U]
    ring
  have htotal : totalTriple Z = applyTriple X a + totalTriple U := by
    funext i
    change (∑ j, Z j i) = (∑ j, a j * X j i) + (∑ j, U j i)
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ ↦ hZ j i
  have hD : D = applyTriple X a + totalTriple U - b • totalTriple X := by
    dsimp only [D]
    rw [htotal]
  have hcol (j : Fin 3) : lowerColumn p * euclideanSq (U j) ≤
      normHessian p (X j) (Z j) := by
    simpa only [lowerColumn, lowerCoefficient, U, a] using
      normHessian_lower_generic hp2 (X j) (Z j) (3447/5000) (111/100)
        (by norm_num) (by norm_num)
        (fun i ↦ (entryBox_column_bounds hX j i).1)
        (fun i ↦ (entryBox_column_bounds hX j i).2)
  have hcols : lowerColumn p * frobeniusSq U ≤ ∑ j, normHessian p (X j) (Z j) := by
    have hh := Finset.sum_le_sum (s := Finset.univ) (fun j _ ↦ hcol j)
    rwa [← Finset.mul_sum] at hh
  have htotal : lowerTotal p * euclideanSq D ≤
      normHessian p (totalTriple X) (totalTriple Z) := by
    apply normHessian_lower_generic hp2 _ _ (2541/5000) (7653/5000)
      (by norm_num) (by norm_num)
    · intro i
      have hi := entryBox_total_bounds hX i
      rw [abs_of_pos (by linarith : 0 < totalTriple X i)]
      exact hi.1
    · intro i
      have hi := entryBox_total_bounds hX i
      rw [abs_of_pos (by linarith : 0 < totalTriple X i)]
      exact hi.2
  have hcols0 : 0 ≤ ∑ j, normHessian p (X j) (Z j) :=
    Finset.sum_nonneg fun j _ ↦ normHessian_nonneg hp1.le _ _
  have hweight : (447 / 500 : ℝ) * p ≤ 2 * K - 1 := by linarith
  have hpos1 := mul_le_mul_of_nonneg_left hcols (show 0 ≤ (447 / 500 : ℝ) * p by positivity)
  have hpos2 := mul_le_mul_of_nonneg_right hweight hcols0
  have hpairs := pair_hessian_sum_bound hp2 hX Z U a b D hZ hD
  have hpair0 : 0 ≤ ∑ j, normHessian p (pairTriple X j) (pairTriple Z j) :=
    Finset.sum_nonneg fun j _ ↦ normHessian_nonneg hp1.le _ _
  have hneg1 := mul_le_mul_of_nonneg_left hpairs (show 0 ≤ p / 2 by linarith)
  have hneg2 := mul_le_mul_of_nonneg_right hKhi hpair0
  have hD0 := euclideanSq_nonneg D
  have hU0 := frobeniusSq_nonneg U
  have hmarginD := mul_le_mul_of_nonneg_right (total_comparison hp hp').le hD0
  have hdpos : 0 ≤ upperPair p := by
    have hpred : 0 ≤ p - 1 := by linarith
    unfold upperPair
    positivity
  have hmarginUp := mul_le_mul_of_nonneg_left (column_comparison hp).le hp0
  have hmarginUcoef : 4000 * (p / 2) * upperPair p ≤ (447 / 500 : ℝ) * p * lowerColumn p := by
    nlinarith [mul_nonneg hp0 hdpos]
  have hmarginU := mul_le_mul_of_nonneg_right hmarginUcoef hU0
  unfold deficitHessian
  nlinarith

end Hl50CvxCurvature

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Hl50CvxCurvature
open HlawkaSchatten.DiagonalConstruction
open Hl50CvxNorm

theorem convex_entryBox : Convex ℝ entryBox := by
  intro X hX Y hY a b ha hb hab j i
  have hx := hX j i
  have hy := hY j i
  have hw (l u : ℝ) (hx : l ≤ X j i ∧ X j i ≤ u) (hy : l ≤ Y j i ∧ Y j i ≤ u) :
      l ≤ (a • X+b • Y) j i ∧ (a • X+b • Y) j i ≤ u := by
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have hlo := add_le_add (mul_le_mul_of_nonneg_left hx.1 ha) (mul_le_mul_of_nonneg_left hy.1 hb)
    have hhi := add_le_add (mul_le_mul_of_nonneg_left hx.2 ha) (mul_le_mul_of_nonneg_left hy.2 hb)
    rw [← add_mul, hab, one_mul] at hlo hhi
    exact ⟨hlo,hhi⟩
  by_cases he : j = i
  · simp only [if_pos he] at hx hy ⊢
    exact hw _ _ hx hy
  · simp only [if_neg he] at hx hy ⊢
    exact hw _ _ hx hy

theorem tripleDeficit_eq_sums (p K : ℝ) (X : Triple) :
    tripleDeficit p K X = (2 * K - 1) * (∑ j, lpNorm p (X j)) +
      lpNorm p (totalTriple X) - K * (∑ j, lpNorm p (pairTriple X j)) := by
  simp only [tripleDeficit, hlawkaDeficit, totalTriple_eq, pairTriple, Fin.sum_univ_three,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons]
  ring


theorem totalTriple_add_smul (X Z : Triple) (t : ℝ) :
    totalTriple (X + t • Z) = totalTriple X + t • totalTriple Z := by
  simp [totalTriple, Finset.sum_add_distrib, Finset.smul_sum]


theorem pairTriple_add_smul (X Z : Triple) (t : ℝ) :
    pairTriple (X + t • Z) = pairTriple X + t • pairTriple Z := by
  ext j i
  fin_cases j <;> simp [pairTriple] <;> ring


theorem hasDerivAt_tripleDeficit_line {p : ℝ} (hp : 1 < p) (K : ℝ) (X Z : Triple) (t : ℝ)
    (ht : X + t • Z ∈ entryBox) :
    HasDerivAt (fun s : ℝ ↦ tripleDeficit p K (X + s • Z))
      (deficitSlope p K (X + t • Z) Z) t := by
  have hcol (j : Fin 3) := hasDerivAt_lpNorm_line hp (X j) (Z j) t
    (entryBox_column_ne_zero ht j)
  have htotal := hasDerivAt_lpNorm_line hp (totalTriple X) (totalTriple Z) t
    (by rw [← totalTriple_add_smul]; exact entryBox_total_ne_zero ht)
  have hpair (j : Fin 3) := hasDerivAt_lpNorm_line hp (pairTriple X j) (pairTriple Z j) t
    (by change (pairTriple X + t • pairTriple Z) j ≠ 0
        rw [← pairTriple_add_smul]; exact entryBox_pair_ne_zero ht j)
  have h := (((HasDerivAt.fun_sum (u := Finset.univ) (fun j _ ↦ hcol j)).const_mul (2 * K - 1)).add
    htotal).sub ((HasDerivAt.fun_sum (u := Finset.univ) (fun j _ ↦ hpair j)).const_mul K)
  convert! h using 1 <;>
    simp only [tripleDeficit_eq_sums, deficitSlope, totalTriple_add_smul, pairTriple_add_smul,
      Pi.add_apply, Pi.smul_apply]
  rfl


theorem hasDerivAt_deficitSlope_line {p : ℝ} (hp : 4 < p) (K : ℝ) (X Z : Triple) (t : ℝ)
    (ht : X + t • Z ∈ entryBox) :
    HasDerivAt (fun s : ℝ ↦ deficitSlope p K (X + s • Z) Z)
      (deficitHessian p K (X + t • Z) Z) t := by
  have hcol (j : Fin 3) := hasDerivAt_normSlope_line hp (X j) (Z j) t
    (entryBox_column_ne_zero ht j)
  have htotal := hasDerivAt_normSlope_line hp (totalTriple X) (totalTriple Z) t
    (by rw [← totalTriple_add_smul]; exact entryBox_total_ne_zero ht)
  have hpair (j : Fin 3) := hasDerivAt_normSlope_line hp (pairTriple X j) (pairTriple Z j) t
    (by change (pairTriple X + t • pairTriple Z) j ≠ 0
        rw [← pairTriple_add_smul]; exact entryBox_pair_ne_zero ht j)
  have h := (((HasDerivAt.fun_sum (u := Finset.univ) (fun j _ ↦ hcol j)).const_mul (2 * K - 1)).add
    htotal).sub ((HasDerivAt.fun_sum (u := Finset.univ) (fun j _ ↦ hpair j)).const_mul K)
  convert! h using 1 <;>
    simp only [deficitSlope, deficitHessian, totalTriple_add_smul, pairTriple_add_smul,
      Pi.add_apply, Pi.smul_apply]
  rfl


theorem continuous_tripleDeficit {p : ℝ} (hp : 0 < p) (K : ℝ) :
    Continuous (tripleDeficit p K) := by
  have hc (j : Fin 3) : Continuous (fun X : Triple ↦ lpNorm p (X j)) :=
    (continuous_lpNorm hp).comp (continuous_apply j)
  have ht : Continuous (fun X : Triple ↦ lpNorm p (X 0 + X 1 + X 2)) :=
    (continuous_lpNorm hp).comp
      (((continuous_apply 0).add (continuous_apply 1)).add (continuous_apply 2))
  have hpairs (j k : Fin 3) : Continuous (fun X : Triple ↦ lpNorm p (X j + X k)) :=
    (continuous_lpNorm hp).comp ((continuous_apply j).add (continuous_apply k))
  exact ((continuous_const.mul (((hc 0).add (hc 1)).add (hc 2))).add ht).sub
    (continuous_const.mul (((hpairs 0 1).add (hpairs 0 2)).add (hpairs 1 2)))


theorem convexOn_tripleDeficit {p K : ℝ} (hp : 50 ≤ p) (hp' : p ≤ 62)
    (hK : (457 / 1000 : ℝ) * p ≤ K) (hKp : K ≤ p / 2) :
    ConvexOn ℝ entryBox (tripleDeficit p K) := by
  refine ⟨convex_entryBox, ?_⟩
  intro X hX Y hY a b ha hb hab
  let Z := Y - X
  have hline (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) : X + t • Z ∈ entryBox := by
    have he : X + t • Z = (1 - t) • X + t • Y := by
      dsimp [Z]
      module
    rw [he]
    exact convex_entryBox hX hY (by linarith [ht.2]) ht.1 (by ring)
  have hcont : Continuous (fun t : ℝ ↦ tripleDeficit p K (X + t • Z)) :=
    (continuous_tripleDeficit (by linarith : 0 < p) K).comp
      (continuous_const.add (continuous_id.smul continuous_const))
  have hconv : ConvexOn ℝ (Set.Icc (0 : ℝ) 1) (fun t : ℝ ↦ tripleDeficit p K (X + t • Z)) := by
    apply convexOn_of_hasDerivWithinAt2_nonneg (convex_Icc 0 1) hcont.continuousOn
      (f' := fun t ↦ deficitSlope p K (X + t • Z) Z)
      (f'' := fun t ↦ deficitHessian p K (X + t • Z) Z)
    · intro t ht
      exact (hasDerivAt_tripleDeficit_line (by linarith : 1 < p) K X Z t
        (hline t (interior_subset ht))).hasDerivWithinAt
    · intro t ht
      exact (hasDerivAt_deficitSlope_line (by linarith : 4 < p) K X Z t
        (hline t (interior_subset ht))).hasDerivWithinAt
    · intro t ht
      exact deficitHessian_nonneg hp hp' hK hKp (hline t (interior_subset ht)) Z
  have h := hconv.2 (show (0 : ℝ) ∈ Set.Icc 0 1 by norm_num)
    (show (1 : ℝ) ∈ Set.Icc 0 1 by norm_num) ha hb hab
  have hpoint : X + b • Z = a • X + b • Y := by
    have haeq : a = 1 - b := by linarith
    rw [haeq]
    dsimp [Z]
    module
  simpa only [smul_eq_mul, mul_zero, mul_one, zero_add, zero_smul, add_zero, one_smul,
    Z, add_sub_cancel, hpoint] using h


end Hl50CvxCurvature

open HlawkaSchatten HlawkaSchatten.DiagonalConstruction

theorem HlawkaSchatten.DiagonalCutoff50.convex_box50 : ∀ p K : ℝ, 50 ≤ p → p ≤ 62 →
    (457 / 1000 : ℝ) * p ≤ K → K ≤ p / 2 →
    ConvexOn ℝ {X : Triple | ∀ j i,
      if j = i then -(111 / 100 : ℝ) ≤ X j i ∧ X j i ≤ -(6894 / 10000 : ℝ)
      else (8091 / 10000 : ℝ) ≤ X j i ∧ X j i ≤ (111 / 100 : ℝ)}
      (tripleDeficit p K) := by
  intro p K hp hp' hK hKp
  exact Hl50CvxCurvature.convexOn_tripleDeficit hp hp' hK hKp

set_option autoImplicit false

namespace HlawkaCert50Geometry
open HlawkaSchatten.DiagonalConstruction
noncomputable abbrev diagMin : ℝ := 6894/10000
noncomputable abbrev offMin : ℝ := 8091/10000
noncomputable abbrev entryMax : ℝ := 111/100
abbrev certEntryBox : Set Triple := {X | ∀ j i,
  if j = i then -entryMax ≤ X j i ∧ X j i ≤ -diagMin
  else offMin ≤ X j i ∧ X j i ≤ entryMax}
end HlawkaCert50Geometry

namespace HlawkaCert50Curvature
open HlawkaSchatten.DiagonalConstruction
abbrev certEntryBox : Set Triple := HlawkaCert50Geometry.certEntryBox
theorem convex_certEntryBox : Convex ℝ certEntryBox := by
  intro X hX Y hY a b ha hb hab j i
  have hx := hX j i
  have hy := hY j i
  have hw (l u : ℝ) (hx : l ≤ X j i ∧ X j i ≤ u) (hy : l ≤ Y j i ∧ Y j i ≤ u) :
      l ≤ (a • X+b • Y) j i ∧ (a • X+b • Y) j i ≤ u := by
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have hlo := add_le_add (mul_le_mul_of_nonneg_left hx.1 ha) (mul_le_mul_of_nonneg_left hy.1 hb)
    have hhi := add_le_add (mul_le_mul_of_nonneg_left hx.2 ha) (mul_le_mul_of_nonneg_left hy.2 hb)
    rw [← add_mul, hab, one_mul] at hlo hhi
    exact ⟨hlo,hhi⟩
  by_cases he : j = i
  · simp only [if_pos he] at hx hy ⊢
    exact hw _ _ hx hy
  · simp only [if_neg he] at hx hy ⊢
    exact hw _ _ hx hy
end HlawkaCert50Curvature

namespace HlawkaCert50Localization
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction
variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E]

theorem lpNorm_smul [NormedSpace ℝ E] {p : ℝ} (hp : 0 < p)
    (c : ℝ) (x : ι → E) : lpNorm p (c • x) = |c| * lpNorm p x := by
  unfold lpNorm
  simp only [Pi.smul_apply, norm_smul, Real.norm_eq_abs,
    Real.mul_rpow (abs_nonneg c) (norm_nonneg _), ← Finset.mul_sum]
  rw [Real.mul_rpow (Real.rpow_nonneg (abs_nonneg c) _)
    (Finset.sum_nonneg fun i _ ↦ Real.rpow_nonneg (norm_nonneg (x i)) _),
    ← Real.rpow_mul (abs_nonneg c), mul_one_div_cancel hp.ne', Real.rpow_one]

theorem lpNorm_comp_equiv {κ : Type*} [Fintype κ]
    (p : ℝ) (x : κ → E) (e : ι ≃ κ) : lpNorm p (x ∘ e) = lpNorm p x := by
  unfold lpNorm
  congr 1
  exact e.sum_comp (fun i ↦ ‖x i‖ ^ p)

theorem hlawkaDeficit_eq (p K : ℝ) (x y z : ι → ℝ) :
    hlawkaDeficit p K x y z =
      K * pairGapSum (lpNorm p) x y z - tripleGap (lpNorm p) x y z := by
  unfold hlawkaDeficit pairGapSum pairGap tripleGap
  ring

theorem hlawkaDeficit_smul {p : ℝ} (hp : 0 < p) (K c : ℝ) (x y z : ι → ℝ) :
    hlawkaDeficit p K (c • x) (c • y) (c • z) = |c| * hlawkaDeficit p K x y z := by
  simp only [hlawkaDeficit, ← smul_add, lpNorm_smul hp]
  ring
end HlawkaCert50Localization

set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace HlawkaCert50Integration
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction
open HlawkaCert50Curvature (certEntryBox convex_certEntryBox)
open HlawkaCert50Localization (hlawkaDeficit_eq hlawkaDeficit_smul lpNorm_comp_equiv)

theorem continuous_cyclicA {p : ℝ} (hp : 0 < p) : Continuous (cyclicA p) := by
  exact ((Real.continuous_rpow_const hp.le).add continuous_const).rpow_const
    (fun _ ↦ Or.inr (one_div_nonneg.mpr hp.le))

theorem continuous_cyclicB {p : ℝ} (hp : 0 < p) : Continuous (cyclicB p) := by
  apply Continuous.rpow_const _ (fun _ ↦ Or.inr (one_div_nonneg.mpr hp.le))
  exact (continuous_const.mul
    ((continuous_const.sub continuous_id).abs.rpow_const
      (fun _ ↦ Or.inr hp.le))).add continuous_const

theorem continuousOn_cyclicRatio {p : ℝ} (hp : 1 < p) :
    ContinuousOn (cyclicRatio p) (Set.Ici 0) := by
  have hp0 : 0 < p := zero_lt_one.trans hp
  apply ContinuousOn.div
  · exact ((continuous_const.mul (continuous_cyclicA hp0)).sub
      (continuous_const.mul (continuous_const.sub continuous_id).abs)).continuousOn
  · exact ((continuous_const.mul (continuous_cyclicA hp0)).sub
      (continuous_const.mul (continuous_cyclicB hp0))).continuousOn
  · intro t ht
    exact (cyclic_denominator_pos hp ht).ne'

theorem lpNorm_const {p : ℝ} (hp : 0 < p) {ι : Type*} [Fintype ι] (x : ℝ) :
    lpNorm p (fun _ : ι ↦ x) = (Fintype.card ι : ℝ) ^ (1 / p) * |x| := by
  unfold lpNorm
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Real.norm_eq_abs]
  rw [Real.mul_rpow (Nat.cast_nonneg _) (Real.rpow_nonneg (abs_nonneg _) _),
    ← Real.rpow_mul (abs_nonneg x), mul_one_div_cancel hp.ne', Real.rpow_one]

theorem lpNorm_cyclicX {p t : ℝ} (ht : 0 ≤ t) :
    lpNorm p (cyclicX t) = cyclicA p t := by
  simp [lpNorm, cyclicX, cyclicA, Fin.sum_univ_three, abs_of_nonneg ht]
  congr 1
  ring

theorem lpNorm_cyclicY {p t : ℝ} (ht : 0 ≤ t) :
    lpNorm p (cyclicY t) = cyclicA p t := by
  simp [lpNorm, cyclicY, cyclicA, Fin.sum_univ_three, abs_of_nonneg ht]
  congr 1
  ring

theorem lpNorm_cyclicZ {p t : ℝ} (ht : 0 ≤ t) :
    lpNorm p (cyclicZ t) = cyclicA p t := by
  simp [lpNorm, cyclicZ, cyclicA, Fin.sum_univ_three, abs_of_nonneg ht]
  congr 1
  ring

theorem lpNorm_cyclicXY {p t : ℝ} (ht : 0 ≤ t) :
    lpNorm p (cyclicX t + cyclicY t) = cyclicB p t := by
  simp [lpNorm, cyclicX, cyclicY, cyclicB, Fin.sum_univ_three, abs_of_nonneg ht]
  congr 1
  ring

theorem lpNorm_cyclicXZ {p t : ℝ} (ht : 0 ≤ t) :
    lpNorm p (cyclicX t + cyclicZ t) = cyclicB p t := by
  simp [lpNorm, cyclicX, cyclicZ, cyclicB, Fin.sum_univ_three, abs_of_nonneg ht]
  congr 1
  ring

theorem lpNorm_cyclicYZ {p t : ℝ} (ht : 0 ≤ t) :
    lpNorm p (cyclicY t + cyclicZ t) = cyclicB p t := by
  simp [lpNorm, cyclicY, cyclicZ, cyclicB, Fin.sum_univ_three, abs_of_nonneg ht]
  congr 1
  ring

theorem cyclic_tripleGap {p t : ℝ} (hp : 0 < p) (ht : 0 ≤ t) :
    tripleGap (lpNorm p) (cyclicX t) (cyclicY t) (cyclicZ t) =
      3 * cyclicA p t - (3 : ℝ) ^ (1 / p) * |2 - t| := by
  have hsum : cyclicX t + cyclicY t + cyclicZ t = fun _ : Fin 3 ↦ 2 - t := by
    ext i
    fin_cases i <;> simp [cyclicX, cyclicY, cyclicZ] <;> ring
  rw [tripleGap, lpNorm_cyclicX ht, lpNorm_cyclicY ht, lpNorm_cyclicZ ht, hsum,
    lpNorm_const hp, Fintype.card_fin]
  ring

theorem cyclic_pairGapSum {p t : ℝ} (ht : 0 ≤ t) :
    pairGapSum (lpNorm p) (cyclicX t) (cyclicY t) (cyclicZ t) =
      6 * cyclicA p t - 3 * cyclicB p t := by
  simp only [pairGapSum, pairGap, lpNorm_cyclicX ht, lpNorm_cyclicY ht,
    lpNorm_cyclicZ ht, lpNorm_cyclicXY ht, lpNorm_cyclicXZ ht, lpNorm_cyclicYZ ht]
  ring

theorem cyclicRatio_le_constant {p t : ℝ} (hp : 1 < p)
    (ht : t ∈ Set.Icc (1 / 2 : ℝ) 2) : cyclicRatio p t ≤ cyclicConstant p := by
  have hc := (continuousOn_cyclicRatio hp).mono
    (show Set.Icc (1 / 2 : ℝ) 2 ⊆ Set.Ici 0 from fun s hs ↦ by
      simp only [Set.mem_Ici]; linarith [hs.1])
  exact le_csSup (isCompact_Icc.image_of_continuousOn hc).bddAbove
    (Set.mem_image_of_mem (cyclicRatio p) ht)

theorem one_le_cyclicConstant {p : ℝ} (hp : 1 < p) : 1 ≤ cyclicConstant p := by
  have htwo : cyclicRatio p 2 = 1 := by
    have hB : cyclicB p 2 = cyclicA p 2 := by
      norm_num [cyclicA, cyclicB, add_comm]
    rw [cyclicRatio, hB]
    norm_num only [sub_self, abs_zero, mul_zero, sub_zero]
    have hden : 6 * cyclicA p 2 - 3 * cyclicA p 2 = 3 * cyclicA p 2 := by ring
    rw [hden, div_self (by
      have : 0 < cyclicA p 2 := by
        unfold cyclicA
        exact Real.rpow_pos_of_pos (by positivity) _
      positivity)]
  rw [← htwo]
  exact cyclicRatio_le_constant hp (by norm_num)
theorem conjugate_mem_certEntryBox (e : Equiv.Perm (Fin 3)) {X : Triple} (hX : X ∈ certEntryBox) :
    conjugate e X ∈ certEntryBox := by
  intro j i
  simpa [conjugate, e.injective.eq_iff] using hX (e j) (e i)

private def permutations : Fin 6 → Equiv.Perm (Fin 3) :=
  ![Equiv.refl _, Equiv.swap 0 1, Equiv.swap 0 2, Equiv.swap 1 2,
    (Equiv.swap 0 1).trans (Equiv.swap 1 2), (Equiv.swap 1 2).trans (Equiv.swap 0 1)]


private theorem tripleDeficit_conjugate_six (p K : ℝ) (X : Triple) (k : Fin 6) :
    tripleDeficit p K (conjugate (permutations k) X) = tripleDeficit p K X := by
  have he (e : Equiv.Perm (Fin 3)) :
      tripleDeficit p K (conjugate e X) = hlawkaDeficit p K (X (e 0)) (X (e 1)) (X (e 2)) := by
    have hsum (u v : Fin 3 → ℝ) : u ∘ e + v ∘ e = (u + v) ∘ e := rfl
    change hlawkaDeficit p K (X (e 0) ∘ e) (X (e 1) ∘ e) (X (e 2) ∘ e) = _
    simp only [hlawkaDeficit, hsum, lpNorm_comp_equiv]
  rw [he]
  fin_cases k <;> simp [permutations, tripleDeficit, hlawkaDeficit, Equiv.swap_apply_def,
    add_comm, add_left_comm, add_assoc]


theorem orbitAverage_apply (X : Triple) (j i : Fin 3) :
    orbitAverage X j i = if i = j then averageDiagonal X else averageOffDiagonal X := by
  fin_cases j <;> fin_cases i <;>
    norm_num [orbitAverage, permutations, conjugate, Fin.sum_univ_succ, Equiv.swap_apply_def,
      averageDiagonal, averageOffDiagonal, Fin.ext_iff] <;> ring!


theorem orbitAverage_mem_certEntryBox {X : Triple} (hX : X ∈ certEntryBox) : orbitAverage X ∈ certEntryBox := by
  apply convex_certEntryBox.sum_mem (t := Finset.univ)
  · intros; norm_num
  · norm_num
  · intro k _
    exact conjugate_mem_certEntryBox _ hX


theorem tripleDeficit_orbitAverage_le {p K : ℝ}
    (hc : ConvexOn ℝ certEntryBox (tripleDeficit p K)) {X : Triple} (hX : X ∈ certEntryBox) :
    tripleDeficit p K (orbitAverage X) ≤ tripleDeficit p K X := by
  have h := hc.map_sum_le (t := Finset.univ) (w := fun _ : Fin 6 ↦ (1 / 6 : ℝ))
    (p := fun k ↦ conjugate (permutations k) X) (by intros; norm_num) (by norm_num)
    (fun _ _ ↦ conjugate_mem_certEntryBox _ hX)
  change tripleDeficit p K (orbitAverage X) ≤ _ at h
  simp only [tripleDeficit_conjugate_six, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul, nsmul_eq_mul] at h
  norm_num at h
  linarith


theorem average_parameter_bounds {X : Triple} (hX : X ∈ certEntryBox) :
    0 < averageOffDiagonal X ∧ -averageDiagonal X / averageOffDiagonal X ∈ Set.Icc (1 / 2) 2 := by
  have hbar := orbitAverage_mem_certEntryBox hX
  have hd := hbar 0 0
  have ho := hbar 0 1
  rw [orbitAverage_apply] at hd ho
  norm_num [HlawkaCert50Geometry.diagMin,HlawkaCert50Geometry.offMin,HlawkaCert50Geometry.entryMax] at hd ho
  have hop : 0 < averageOffDiagonal X := by linarith
  exact ⟨hop, (le_div_iff₀ hop).mpr (by linarith), (div_le_iff₀ hop).mpr (by linarith)⟩


theorem orbitAverage_eq_cyclic (X : Triple) (ho : averageOffDiagonal X ≠ 0) :
    orbitAverage X = ![averageOffDiagonal X • cyclicX (-averageDiagonal X / averageOffDiagonal X),
      averageOffDiagonal X • cyclicY (-averageDiagonal X / averageOffDiagonal X),
      averageOffDiagonal X • cyclicZ (-averageDiagonal X / averageOffDiagonal X)] := by
  ext j i
  rw [orbitAverage_apply]
  fin_cases j <;> fin_cases i <;> norm_num [cyclicX, cyclicY, cyclicZ] <;> field_simp


theorem tripleDeficit_orbitAverage_nonneg {p : ℝ} (hp : 1 < p) {X : Triple} (hX : X ∈ certEntryBox) :
    0 ≤ tripleDeficit p (cyclicConstant p) (orbitAverage X) := by
  obtain ⟨ho, ht⟩ := average_parameter_bounds hX
  let t := -averageDiagonal X / averageOffDiagonal X
  have ht0 : 0 ≤ t := by dsimp [t]; linarith [ht.1]
  have hratio := cyclicRatio_le_constant hp ht
  have hD := cyclic_denominator_pos hp ht0
  rw [cyclicRatio, div_le_iff₀ hD] at hratio
  have hcyclic : 0 ≤ hlawkaDeficit p (cyclicConstant p) (cyclicX t) (cyclicY t) (cyclicZ t) := by
    rw [hlawkaDeficit_eq, cyclic_tripleGap (zero_lt_one.trans hp) ht0, cyclic_pairGapSum ht0]
    exact sub_nonneg.mpr hratio
  rw [orbitAverage_eq_cyclic X ho.ne']
  change 0 ≤ hlawkaDeficit p (cyclicConstant p) (averageOffDiagonal X • cyclicX t)
    (averageOffDiagonal X • cyclicY t) (averageOffDiagonal X • cyclicZ t)
  rw [hlawkaDeficit_smul (zero_lt_one.trans hp)]
  exact mul_nonneg (abs_nonneg _) hcyclic


theorem tripleDeficit_nonneg_of_convex {p : ℝ} (hp : 1 < p)
    (hc : ConvexOn ℝ certEntryBox (tripleDeficit p (cyclicConstant p)))
    {X : Triple} (hX : X ∈ certEntryBox) : 0 ≤ tripleDeficit p (cyclicConstant p) X :=
  (tripleDeficit_orbitAverage_nonneg hp hX).trans (tripleDeficit_orbitAverage_le hc hX)


/-- Localization and convexity suffice for the real three-coordinate bound. -/
theorem real_bound_of_box_convex {p : ℝ} (hp : 1 < p)
    (hlocal : ∀ x y z : Fin 3 → ℝ,
      hlawkaDeficit p (cyclicConstant p) x y z < 0 →
        ∃ X ∈ certEntryBox, tripleDeficit p (cyclicConstant p) X < 0)
    (hc : ConvexOn ℝ certEntryBox (tripleDeficit p (cyclicConstant p))) :
    HasHlawkaConstant (lpNorm p : (Fin 3 → ℝ) → ℝ) (cyclicConstant p) := by
  intro x y z
  by_contra hn
  have hf : hlawkaDeficit p (cyclicConstant p) x y z < 0 := by
    rw [hlawkaDeficit_eq]
    linarith
  obtain ⟨X, hX, hneg⟩ := hlocal x y z hf
  exact (not_lt_of_ge (tripleDeficit_nonneg_of_convex hp hc hX)) hneg


end HlawkaCert50Integration

open HlawkaSchatten HlawkaSchatten.DiagonalConstruction
theorem HlawkaCut50.real_bound50 : ∀ p : ℝ, 50 ≤ p → ∀ n : ℕ,
    HasHlawkaConstant (lpNorm p : (Fin n → ℝ) → ℝ) (cyclicConstant p) := by
  intro p hp n
  by_cases h62 : 62 ≤ p
  · exact HlawkaSchatten.DiagonalCutoff.real_bound62 p h62 n
  have hp62 : p ≤ 62 := by linarith
  have hscalar := HlawkaSchatten.DiagonalCutoff50.scalar_window50 p hp hp62
  have hK : 1 / 2 ≤ cyclicConstant p := by
    have h := HlawkaCert50Integration.one_le_cyclicConstant (p := p) (by linarith)
    linarith
  have hlocal : ∀ x y z : Fin 3 → ℝ,
      hlawkaDeficit p (cyclicConstant p) x y z < 0 →
        ∃ X ∈ HlawkaCert50Curvature.certEntryBox,
          tripleDeficit p (cyclicConstant p) X < 0 :=
    HlawkaSchatten.DiagonalCutoff50.local_failure50 p hp hscalar.1 hscalar.2.1
  have hc : ConvexOn ℝ HlawkaCert50Curvature.certEntryBox
      (tripleDeficit p (cyclicConstant p)) :=
    HlawkaSchatten.DiagonalCutoff50.convex_box50 p (cyclicConstant p) hp hp62 hscalar.1.le hscalar.2.2
  exact real_bound_of_fin_three (by linarith) hK
    (HlawkaCert50Integration.real_bound_of_box_convex (by linarith) hlocal hc)



set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace HlawkaCertComplex80Transfer
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction MeasureTheory

section NormLaws
variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E]


theorem lpNorm_const {p : ℝ} (hp : 0 < p) (x : E) :
    _root_.HlawkaSchatten.DiagonalConstruction.lpNorm p (fun _ : ι ↦ x) = (Fintype.card ι : ℝ) ^ (1 / p) * ‖x‖ := by
  unfold _root_.HlawkaSchatten.DiagonalConstruction.lpNorm
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [Real.mul_rpow (Nat.cast_nonneg _) (Real.rpow_nonneg (norm_nonneg _) _),
    ← Real.rpow_mul (norm_nonneg x), mul_one_div_cancel hp.ne', Real.rpow_one]


theorem lpNorm_smul [NormedSpace ℝ E] {p : ℝ} (hp : 0 < p)
    (c : ℝ) (x : ι → E) : _root_.HlawkaSchatten.DiagonalConstruction.lpNorm p (c • x) = |c| * _root_.HlawkaSchatten.DiagonalConstruction.lpNorm p x := by
  unfold _root_.HlawkaSchatten.DiagonalConstruction.lpNorm
  simp only [Pi.smul_apply, norm_smul, Real.norm_eq_abs,
    Real.mul_rpow (abs_nonneg c) (norm_nonneg _), ← Finset.mul_sum]
  rw [Real.mul_rpow (Real.rpow_nonneg (abs_nonneg c) _)
    (Finset.sum_nonneg fun i _ ↦ Real.rpow_nonneg (norm_nonneg (x i)) _),
    ← Real.rpow_mul (abs_nonneg c), mul_one_div_cancel hp.ne', Real.rpow_one]


theorem lpNorm_comp_equiv {κ : Type*} [Fintype κ]
    (p : ℝ) (x : κ → E) (e : ι ≃ κ) : lpNorm p (x ∘ e) = lpNorm p x := by
  unfold HlawkaSchatten.DiagonalConstruction.lpNorm
  congr 1
  exact e.sum_comp (fun i ↦ ‖x i‖ ^ p)

end NormLaws


theorem cyclicA_pos {p t : ℝ} (ht : 0 ≤ t) : 0 < cyclicA p t := by
  unfold cyclicA
  exact Real.rpow_pos_of_pos (by positivity) _


theorem continuous_cyclicA {p : ℝ} (hp : 0 < p) : Continuous (cyclicA p) := by
  exact ((Real.continuous_rpow_const hp.le).add continuous_const).rpow_const
    (fun _ ↦ Or.inr (one_div_nonneg.mpr hp.le))


theorem continuous_cyclicB {p : ℝ} (hp : 0 < p) : Continuous (cyclicB p) := by
  apply Continuous.rpow_const _ (fun _ ↦ Or.inr (one_div_nonneg.mpr hp.le))
  exact (continuous_const.mul
    ((continuous_const.sub continuous_id).abs.rpow_const
      (fun _ ↦ Or.inr hp.le))).add continuous_const


theorem continuousOn_cyclicRatio {p : ℝ} (hp : 1 < p) :
    ContinuousOn (cyclicRatio p) (Set.Ici 0) := by
  have hp0 : 0 < p := zero_lt_one.trans hp
  apply ContinuousOn.div
  · exact ((continuous_const.mul (continuous_cyclicA hp0)).sub
      (continuous_const.mul (continuous_const.sub continuous_id).abs)).continuousOn
  · exact ((continuous_const.mul (continuous_cyclicA hp0)).sub
      (continuous_const.mul (continuous_cyclicB hp0))).continuousOn
  · intro t ht
    exact (cyclic_denominator_pos hp ht).ne'


theorem cyclicRatio_le_constant {p t : ℝ} (hp : 1 < p)
    (ht : t ∈ Set.Icc (1 / 2 : ℝ) 2) : cyclicRatio p t ≤ cyclicConstant p := by
  have hc := (continuousOn_cyclicRatio hp).mono
    (show Set.Icc (1 / 2 : ℝ) 2 ⊆ Set.Ici 0 from fun s hs ↦ by
      simp only [Set.mem_Ici]; linarith [hs.1])
  exact le_csSup (isCompact_Icc.image_of_continuousOn hc).bddAbove
    (Set.mem_image_of_mem (cyclicRatio p) ht)


theorem cyclicRatio_two (p : ℝ) : cyclicRatio p 2 = 1 := by
  have hA : 0 < cyclicA p 2 := cyclicA_pos (by norm_num)
  have hB : cyclicB p 2 = cyclicA p 2 := by
    norm_num [cyclicA, cyclicB, add_comm]
  rw [cyclicRatio, hB]
  norm_num only [sub_self, abs_zero, mul_zero, sub_zero]
  have hden : 6 * cyclicA p 2 - 3 * cyclicA p 2 = 3 * cyclicA p 2 := by ring
  rw [hden, div_self (by positivity)]


theorem one_le_cyclicConstant {p : ℝ} (hp : 1 < p) : 1 ≤ cyclicConstant p := by
  rw [← cyclicRatio_two p]
  exact cyclicRatio_le_constant hp (by norm_num)


theorem lpNorm_cyclicX {p t : ℝ} (ht : 0 ≤ t) :
    _root_.HlawkaSchatten.DiagonalConstruction.lpNorm p (cyclicX t) = cyclicA p t := by
  simp [_root_.HlawkaSchatten.DiagonalConstruction.lpNorm, cyclicX, cyclicA, Fin.sum_univ_three, abs_of_nonneg ht]
  congr 1
  ring


theorem lpNorm_cyclicY {p t : ℝ} (ht : 0 ≤ t) :
    _root_.HlawkaSchatten.DiagonalConstruction.lpNorm p (cyclicY t) = cyclicA p t := by
  simp [_root_.HlawkaSchatten.DiagonalConstruction.lpNorm, cyclicY, cyclicA, Fin.sum_univ_three, abs_of_nonneg ht]
  congr 1
  ring


theorem lpNorm_cyclicZ {p t : ℝ} (ht : 0 ≤ t) :
    _root_.HlawkaSchatten.DiagonalConstruction.lpNorm p (cyclicZ t) = cyclicA p t := by
  simp [_root_.HlawkaSchatten.DiagonalConstruction.lpNorm, cyclicZ, cyclicA, Fin.sum_univ_three, abs_of_nonneg ht]
  congr 1
  ring


theorem lpNorm_cyclicXY (p t : ℝ) :
    _root_.HlawkaSchatten.DiagonalConstruction.lpNorm p (cyclicX t + cyclicY t) = cyclicB p t := by
  have he : cyclicX t + cyclicY t = ![1 - t, 1 - t, 2] := by
    ext i
    fin_cases i <;> simp [cyclicX, cyclicY] <;> ring
  rw [he]
  simp [_root_.HlawkaSchatten.DiagonalConstruction.lpNorm, cyclicB, Fin.sum_univ_three]
  congr 1
  ring


theorem lpNorm_cyclicXZ (p t : ℝ) :
    _root_.HlawkaSchatten.DiagonalConstruction.lpNorm p (cyclicX t + cyclicZ t) = cyclicB p t := by
  have he : cyclicX t + cyclicZ t = ![1 - t, 2, 1 - t] := by
    ext i
    fin_cases i <;> simp [cyclicX, cyclicZ] <;> ring
  rw [he]
  simp [_root_.HlawkaSchatten.DiagonalConstruction.lpNorm, cyclicB, Fin.sum_univ_three]
  congr 1
  ring


theorem lpNorm_cyclicYZ (p t : ℝ) :
    _root_.HlawkaSchatten.DiagonalConstruction.lpNorm p (cyclicY t + cyclicZ t) = cyclicB p t := by
  have he : cyclicY t + cyclicZ t = ![2, 1 - t, 1 - t] := by
    ext i
    fin_cases i <;> simp [cyclicY, cyclicZ] <;> ring
  rw [he]
  simp [_root_.HlawkaSchatten.DiagonalConstruction.lpNorm, cyclicB, Fin.sum_univ_three]
  congr 1
  ring


theorem lpNorm_cyclicXYZ {p : ℝ} (hp : 0 < p) (t : ℝ) :
    _root_.HlawkaSchatten.DiagonalConstruction.lpNorm p (cyclicX t + cyclicY t + cyclicZ t) =
      (3 : ℝ) ^ (1 / p) * |2 - t| := by
  have he : cyclicX t + cyclicY t + cyclicZ t = fun _ ↦ 2 - t := by
    ext i
    fin_cases i <;> simp [cyclicX, cyclicY, cyclicZ] <;> ring
  rw [he, lpNorm_const hp]
  simp


theorem cyclic_tripleGap {p t : ℝ} (hp : 0 < p) (ht : 0 ≤ t) :
    tripleGap (_root_.HlawkaSchatten.DiagonalConstruction.lpNorm p) (cyclicX t) (cyclicY t) (cyclicZ t) =
      3 * cyclicA p t - (3 : ℝ) ^ (1 / p) * |2 - t| := by
  rw [tripleGap, lpNorm_cyclicX ht, lpNorm_cyclicY ht, lpNorm_cyclicZ ht,
    lpNorm_cyclicXYZ hp]
  ring


theorem cyclic_pairGapSum {p t : ℝ} (ht : 0 ≤ t) :
    pairGapSum (_root_.HlawkaSchatten.DiagonalConstruction.lpNorm p) (cyclicX t) (cyclicY t) (cyclicZ t) =
      6 * cyclicA p t - 3 * cyclicB p t := by
  simp only [pairGapSum, pairGap, lpNorm_cyclicX ht, lpNorm_cyclicY ht,
    lpNorm_cyclicZ ht, lpNorm_cyclicXY, lpNorm_cyclicXZ, lpNorm_cyclicYZ]
  ring

section Deficit
variable {ι : Type*} [Fintype ι]


theorem hlawkaDeficit_eq (p K : ℝ) (x y z : ι → ℝ) :
    hlawkaDeficit p K x y z =
      K * pairGapSum (_root_.HlawkaSchatten.DiagonalConstruction.lpNorm p) x y z - tripleGap (_root_.HlawkaSchatten.DiagonalConstruction.lpNorm p) x y z := by
  unfold hlawkaDeficit pairGapSum pairGap tripleGap
  ring


theorem hlawkaDeficit_smul {p : ℝ} (hp : 0 < p) (K c : ℝ) (x y z : ι → ℝ) :
    hlawkaDeficit p K (c • x) (c • y) (c • z) = |c| * hlawkaDeficit p K x y z := by
  simp only [hlawkaDeficit, ← smul_add, lpNorm_smul hp]
  ring

end Deficit


section CircleTransfer

instance circleMeasure_isProbability : IsProbabilityMeasure circleMeasure :=
  ⟨by simpa only [TopologicalSpace.PositiveCompacts.coe_top] using
    (Measure.haarMeasure_self (K₀ := (⊤ : TopologicalSpace.PositiveCompacts Circle)))⟩


theorem continuous_circle_projection_power {p : ℝ} (hp : 0 < p) (z : ℂ) :
    Continuous (fun u : Circle ↦ |((u : ℂ) * z).re| ^ p) := by
  exact ((Complex.continuous_re.comp (continuous_subtype_val.mul continuous_const)).abs).rpow_const
    (fun _ ↦ Or.inr hp.le)


theorem circleMoment_pos {p : ℝ} (hp : 0 < p) : 0 < circleMoment p := by
  have hc : Continuous (fun u : Circle ↦ |(u : ℂ).re| ^ p) := by
    simpa only [mul_one] using continuous_circle_projection_power hp 1
  exact integral_pos_of_integrable_nonneg_nonzero hc
    (hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    (fun u ↦ Real.rpow_nonneg (abs_nonneg _) _) (x := (1 : Circle)) (by simp)


theorem integral_circle_projection_power {p : ℝ} (hp : 0 < p) (z : ℂ) :
    (∫ u : Circle, |((u : ℂ) * z).re| ^ p ∂circleMeasure) = circleMoment p * ‖z‖ ^ p := by
  by_cases hz : z = 0
  · simp [hz, hp.ne']
  have hn : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
  let v : Circle := ⟨z / (‖z‖ : ℂ), mem_sphere_zero_iff_norm.mpr (by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg z), div_self hn])⟩
  have hv : (v : ℂ) * (‖z‖ : ℂ) = z := div_mul_cancel₀ _ (Complex.ofReal_ne_zero.mpr hn)
  have hre (u : Circle) : ((u : ℂ) * z).re = ‖z‖ * ((v * u : Circle) : ℂ).re := by
    calc
      _ = (((v : ℂ) * (u : ℂ)) * (‖z‖ : ℂ)).re := by
        congr 1
        conv_lhs => rw [← hv]
        ring
      _ = _ := by simp only [Circle.coe_mul, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, mul_zero, sub_zero]; ring
  simp_rw [hre, abs_mul, abs_of_nonneg (norm_nonneg z),
    Real.mul_rpow (norm_nonneg z) (abs_nonneg _)]
  rw [integral_const_mul]
  have hrot : (∫ a : Circle, |((v * a : Circle) : ℂ).re| ^ p ∂circleMeasure) = circleMoment p :=
    integral_mul_left_eq_self (μ := circleMeasure) (fun a : Circle ↦ |(a : ℂ).re| ^ p) v
  change ‖z‖ ^ p * (∫ a : Circle, |((v * a : Circle) : ℂ).re| ^ p ∂circleMeasure) = _
  rw [hrot]
  exact mul_comm _ _

variable {ι : Type*} [Fintype ι]


theorem continuous_projectionPower {p : ℝ} (hp : 0 < p) (z : ι → ℂ) :
    Continuous (projectionPower p z) :=
  continuous_finsetSum _ fun i _ ↦ continuous_circle_projection_power hp (z i)


theorem integral_projectionPower {p : ℝ} (hp : 0 < p) (z : ι → ℂ) :
    (∫ u : Circle, projectionPower p z u ∂circleMeasure) = circleMoment p * ∑ i, ‖z i‖ ^ p := by
  unfold projectionPower
  rw [integral_finsetSum Finset.univ (fun i _ ↦
    (continuous_circle_projection_power hp (z i)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _))]
  simp only [integral_circle_projection_power hp, Finset.mul_sum]

variable {κ : Type*} [Fintype κ]

omit [Fintype ι] [Fintype κ] in

theorem finiteProjection_add (p : ℝ) (w : κ → ℝ) (u : κ → Circle) (z v : ι → ℂ) :
    finiteProjection p w u (z + v) = finiteProjection p w u z + finiteProjection p w u v := by
  ext k
  simp [finiteProjection, mul_add, Complex.add_re]


theorem lpNorm_finiteProjection {p : ℝ} (hp : 0 < p) (w : κ → ℝ) (u : κ → Circle)
    (hw : ∀ k, 0 ≤ w k) (z : ι → ℂ) :
    _root_.HlawkaSchatten.DiagonalConstruction.lpNorm p (finiteProjection p w u z) = (∑ k, w k * projectionPower p z (u k)) ^ (1 / p) := by
  unfold _root_.HlawkaSchatten.DiagonalConstruction.lpNorm
  congr 1
  simp only [finiteProjection, Fintype.sum_prod_type, Real.norm_eq_abs, abs_mul,
    abs_of_nonneg (Real.rpow_nonneg (hw _) _)]
  simp_rw [Real.mul_rpow (Real.rpow_nonneg (hw _) _) (abs_nonneg _),
    ← Real.rpow_mul (hw _), one_div_mul_cancel hp.ne', Real.rpow_one]
  simp only [projectionPower, Finset.mul_sum]


theorem continuous_powerDeficit {p : ℝ} (hp : 0 < p) (K : ℝ) : Continuous (powerDeficit p K) := by
  have hc (i : Fin 7) : Continuous (fun a : Fin 7 → ℝ ↦ (a i) ^ (1 / p)) :=
    (continuous_apply i).rpow_const (fun _ ↦ Or.inr (one_div_nonneg.mpr hp.le))
  exact ((continuous_const.mul (((hc 0).add (hc 1)).add (hc 2))).add (hc 6)).sub
    (continuous_const.mul (((hc 3).add (hc 4)).add (hc 5)))


theorem continuous_sevenProjections {p : ℝ} (hp : 0 < p) (x y z : ι → ℂ) :
    Continuous (sevenProjections p x y z) :=
  continuous_pi fun k ↦ continuous_projectionPower hp (sevenVectors x y z k)


theorem powerDeficit_nonneg_on_projection_hull {p : ℝ} (hp : 1 < p)
    (hreal : HasHlawkaConstant (lpNorm p : (Fin 3 → ℝ) → ℝ) (cyclicConstant p)) (x y z : ι → ℂ) :
    convexHull ℝ (Set.range (sevenProjections p x y z)) ⊆
      {a | 0 ≤ powerDeficit p (cyclicConstant p) a} := by
  classical
  intro a ha
  have hp0 : 0 < p := by linarith
  obtain ⟨κ, _, w, points, hw, _, hpoints, hsum⟩ := mem_convexHull_iff_exists_fintype.mp ha
  choose u hu using hpoints
  have hsum' : ∑ k, w k • sevenProjections p x y z (u k) = a := by
    simpa only [hu] using hsum
  let R : (ι → ℂ) → κ × ι → ℝ := finiteProjection p w u
  have hadd (v v' : ι → ℂ) : R (v + v') = R v + R v' := finiteProjection_add p w u v v'
  have hn (k : Fin 7) : lpNorm p (R (sevenVectors x y z k)) = (a k) ^ (1 / p) := by
    rw [lpNorm_finiteProjection hp0 w u hw]
    congr 1
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, sevenProjections] using
      congrFun hsum' k
  have h0 := hn 0
  have h1 := hn 1
  have h2 := hn 2
  have h3 := hn 3
  have h4 := hn 4
  have h5 := hn 5
  have h6 := hn 6
  change lpNorm p (R x) = (a 0) ^ (1 / p) at h0
  change lpNorm p (R y) = (a 1) ^ (1 / p) at h1
  change lpNorm p (R z) = (a 2) ^ (1 / p) at h2
  change lpNorm p (R (x + y)) = (a 3) ^ (1 / p) at h3
  change lpNorm p (R (x + z)) = (a 4) ^ (1 / p) at h4
  change lpNorm p (R (y + z)) = (a 5) ^ (1 / p) at h5
  change lpNorm p (R (x + y + z)) = (a 6) ^ (1 / p) at h6
  have h := real_bound_of_fin_three hp (by linarith [one_le_cyclicConstant hp]) hreal (R x) (R y) (R z)
  simp only [tripleGap, pairGapSum, pairGap, ← hadd] at h
  change 0 ≤ powerDeficit p (cyclicConstant p) a
  unfold powerDeficit
  rw [← h0, ← h1, ← h2, ← h3, ← h4, ← h5, ← h6]
  nlinarith


/-- The sharp constant passes from real coordinates to complex coordinates. -/
theorem complex_hlawka_bound {p : ℝ} (hp : 1 < p)
    (hreal : HasHlawkaConstant (lpNorm p : (Fin 3 → ℝ) → ℝ) (cyclicConstant p)) :
    HasHlawkaConstant (lpNorm p : (ι → ℂ) → ℝ) (cyclicConstant p) := by
  intro x y z
  have hp0 : 0 < p := by linarith
  let F := sevenProjections p x y z
  let m : Fin 7 → ℝ := ∫ u : Circle, F u ∂circleMeasure
  have hcont : Continuous F := continuous_sevenProjections hp0 x y z
  have hfi : Integrable F circleMeasure :=
    hcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hm : m ∈ closure (convexHull ℝ (Set.range F)) := by
    apply (convex_convexHull ℝ (Set.range F)).closure.integral_mem isClosed_closure _ hfi
    exact Filter.Eventually.of_forall fun u ↦
      subset_closure (subset_convexHull ℝ (Set.range F) (Set.mem_range_self u))
  have hclosed : IsClosed {a | 0 ≤ powerDeficit p (cyclicConstant p) a} :=
    isClosed_le continuous_const (continuous_powerDeficit hp0 _)
  have hnon : 0 ≤ powerDeficit p (cyclicConstant p) m :=
    (closure_minimal (powerDeficit_nonneg_on_projection_hull hp hreal x y z) hclosed) hm
  have hcoord (k : Fin 7) : m k = circleMoment p * ∑ i, ‖sevenVectors x y z k i‖ ^ p := by
    calc
      _ = ∫ u : Circle, F u k ∂circleMeasure :=
        ((ContinuousLinearMap.proj k : (Fin 7 → ℝ) →L[ℝ] ℝ).integral_comp_comm hfi).symm
      _ = _ := integral_projectionPower hp0 (sevenVectors x y z k)
  let c := circleMoment p ^ (1 / p)
  have hc : 0 < c := Real.rpow_pos_of_pos (circleMoment_pos hp0) _
  have hroot (k : Fin 7) : (m k) ^ (1 / p) = c * lpNorm p (sevenVectors x y z k) := by
    rw [hcoord, Real.mul_rpow (circleMoment_pos hp0).le
      (Finset.sum_nonneg fun i _ ↦ Real.rpow_nonneg (norm_nonneg _) _)]
    rfl
  simp only [powerDeficit, hroot] at hnon
  change 0 ≤ (2 * cyclicConstant p - 1) *
      (c * lpNorm p x + c * lpNorm p y + c * lpNorm p z) + c * lpNorm p (x + y + z) -
    cyclicConstant p * (c * lpNorm p (x + y) + c * lpNorm p (x + z) + c * lpNorm p (y + z)) at hnon
  have hscaled : 0 ≤ c * (cyclicConstant p * pairGapSum (lpNorm p) x y z -
      tripleGap (lpNorm p) x y z) := by
    convert hnon using 1
    unfold pairGapSum pairGap tripleGap
    ring
  exact sub_nonneg.mp ((mul_nonneg_iff_of_pos_left hc).mp hscaled)

end CircleTransfer


/-- A real bound in dimension three gives uniform complex sharpness,
including the empty coordinate dimension. -/
theorem isLeast_of_real_bound {p : ℝ} (hp : 1 < p)
    (hreal : HasHlawkaConstant (lpNorm p : (Fin 3 → ℝ) → ℝ) (cyclicConstant p)) :
    IsLeast {C : ℝ | ∀ n : ℕ,
      HasHlawkaConstant (lpNorm p : (Fin n → ℂ) → ℝ) C} (cyclicConstant p) := by
  constructor
  · intro n
    exact complex_hlawka_bound hp hreal
  · intro C hC
    exact cyclicConstant_le_of_complex_constant hp (n := 3) (by rfl) (hC 3)

end HlawkaCertComplex80Transfer



set_option autoImplicit false
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction
theorem solution : ∀ p : ℝ, 50 ≤ p →
    IsLeast {C : ℝ | ∀ n : ℕ,
      HasHlawkaConstant (lpNorm p : (Fin n → ℂ) → ℝ) C} (cyclicConstant p) := by
  intro p hp
  exact HlawkaCertComplex80Transfer.isLeast_of_real_bound (by linarith)
    (HlawkaCut50.real_bound50 p hp 3)

