-- Prove2me | solution 3 for HlawkaSchatten.LpThreshold.cyclicConstant_le_one_below
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-19T05:59:04.566635+00:00
-- url     : https://prove2.me/submissions/3370e558-b627-4f13-82ec-952289580554

import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Basic
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Cyclic
import Definitions.Def_HlawkaSchatten_GapComparison
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases

set_option autoImplicit false
set_option maxHeartbeats 4000000

open HlawkaSchatten HlawkaSchatten.DiagonalConstruction

namespace HlawkaSchatten.LpThreshold

/-- Minkowski's inequality for the coordinate `p`-norm on `Fin 3 → ℝ`. -/
lemma lpNorm_add_fin3 {p : ℝ} (hp : 1 ≤ p) (x y : Fin 3 → ℝ) :
    lpNorm p (x + y) ≤ lpNorm p x + lpNorm p y := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hpi : ∀ z : Fin 3 → ℝ, lpNorm p z = ‖WithLp.toLp (ENNReal.ofReal p) z‖ := by
    intro z
    rw [PiLp.norm_eq_sum (by simpa only [ENNReal.toReal_ofReal hp0.le] using hp0)]
    simp [lpNorm, ENNReal.toReal_ofReal hp0.le]
  let _ : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr hp⟩
  simpa only [hpi, ← WithLp.toLp_add] using
    norm_add_le (WithLp.toLp (ENNReal.ofReal p) x) (WithLp.toLp (ENNReal.ofReal p) y)

/-- The denominator of `cyclicRatio` is strictly positive for `p > 1` and `t ≥ 0`. -/
lemma cyclic_denom_pos {p t : ℝ} (hp : 1 < p) (ht : 0 ≤ t) :
    0 < 6 * cyclicA p t - 3 * cyclicB p t := by
  have hp0 : 0 < p := zero_lt_one.trans hp
  have habs : |1 - t| ^ p ≤ 1 + t ^ p := by
    rcases le_total t 1 with h | h
    · have hpow := Real.rpow_le_rpow (abs_nonneg (1 - t))
        (show |1 - t| ≤ 1 by rw [abs_of_nonneg (sub_nonneg.mpr h)]; linarith) hp0.le
      rw [Real.one_rpow] at hpow
      linarith [Real.rpow_nonneg ht p]
    · have hpow := Real.rpow_le_rpow (abs_nonneg (1 - t))
        (show |1 - t| ≤ t by rw [abs_of_nonpos (sub_nonpos.mpr h)]; linarith) hp0.le
      linarith
  have htwo : (2 : ℝ) < (2 : ℝ) ^ p := by
    simpa using Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1 : ℝ) < 2) hp
  have hBp : cyclicB p t ^ p < (2 * cyclicA p t) ^ p := by
    have hA0 : 0 ≤ cyclicA p t := by unfold cyclicA; positivity
    have h1 : cyclicB p t ^ p = 2 * |1 - t| ^ p + (2 : ℝ) ^ p := by
      rw [cyclicB, ← Real.rpow_mul (by positivity), one_div_mul_cancel hp0.ne', Real.rpow_one]
    have h2 : (2 * cyclicA p t) ^ p = (2 : ℝ) ^ p * (t ^ p + 2) := by
      rw [Real.mul_rpow (by norm_num) hA0, cyclicA,
        ← Real.rpow_mul (by positivity), one_div_mul_cancel hp0.ne', Real.rpow_one]
    rw [h1, h2]
    have htp : 0 ≤ t ^ p := Real.rpow_nonneg ht p
    nlinarith
  have hB0 : 0 ≤ cyclicB p t := by unfold cyclicB; positivity
  have hlt : cyclicB p t < 2 * cyclicA p t := by
    by_contra hge
    have hge' : 2 * cyclicA p t ≤ cyclicB p t := le_of_not_gt hge
    have h2A : 0 ≤ 2 * cyclicA p t := by unfold cyclicA; positivity
    exact not_le_of_gt hBp (Real.rpow_le_rpow h2A hge' hp0.le)
  linarith

/-- Rational lower certificate for `((c : ℝ) / d) ^ ((m : ℝ) / k)`. -/
lemma rational_rpow_ge (a b c d m k : ℕ) (hb : 0 < b) (hd : 0 < d) (hk : 0 < k)
    (h : a ^ k * d ^ m ≤ c ^ m * b ^ k) :
    (a : ℝ) / b ≤ ((c : ℝ) / d) ^ ((m : ℝ) / k) := by
  have hb' : (0 : ℝ) < b := Nat.cast_pos.mpr hb
  have hd' : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  have hpow : ((a : ℝ) / b) ^ k ≤ ((c : ℝ) / d) ^ m := by
    rw [div_pow, div_pow, div_le_div_iff₀ (pow_pos hb' k) (pow_pos hd' m)]
    exact_mod_cast h
  have hbase : 0 ≤ (c : ℝ) / d := by positivity
  have hab0 : 0 ≤ (a : ℝ) / b := by positivity
  have he : ((c : ℝ) / d) ^ ((m : ℝ) / k) = (((c : ℝ) / d) ^ m) ^ ((k : ℝ)⁻¹) := by
    rw [show ((m : ℝ) / k) = (m : ℝ) * (k : ℝ)⁻¹ by ring, Real.rpow_mul hbase, Real.rpow_natCast]
  rw [he]
  calc (a : ℝ) / b = (((a : ℝ) / b) ^ k) ^ ((k : ℝ)⁻¹) :=
        (Real.pow_rpow_inv_natCast hab0 hk.ne').symm
    _ ≤ (((c : ℝ) / d) ^ m) ^ ((k : ℝ)⁻¹) :=
        Real.rpow_le_rpow (by positivity) hpow (by positivity)

/-- Rational upper certificate for `((c : ℝ) / d) ^ ((m : ℝ) / k)`. -/
lemma rational_rpow_le (a b c d m k : ℕ) (hb : 0 < b) (hd : 0 < d) (hk : 0 < k)
    (h : c ^ m * b ^ k ≤ a ^ k * d ^ m) :
    ((c : ℝ) / d) ^ ((m : ℝ) / k) ≤ (a : ℝ) / b := by
  have hb' : (0 : ℝ) < b := Nat.cast_pos.mpr hb
  have hd' : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  have hpow : ((c : ℝ) / d) ^ m ≤ ((a : ℝ) / b) ^ k := by
    rw [div_pow, div_pow, div_le_div_iff₀ (pow_pos hd' m) (pow_pos hb' k)]
    exact_mod_cast h
  have hbase : 0 ≤ (c : ℝ) / d := by positivity
  have hab0 : 0 ≤ (a : ℝ) / b := by positivity
  have he : ((c : ℝ) / d) ^ ((m : ℝ) / k) = (((c : ℝ) / d) ^ m) ^ ((k : ℝ)⁻¹) := by
    rw [show ((m : ℝ) / k) = (m : ℝ) * (k : ℝ)⁻¹ by ring, Real.rpow_mul hbase, Real.rpow_natCast]
  rw [he]
  calc (((c : ℝ) / d) ^ m) ^ ((k : ℝ)⁻¹) ≤ (((a : ℝ) / b) ^ k) ^ ((k : ℝ)⁻¹) :=
        Real.rpow_le_rpow (by positivity) hpow (by positivity)
    _ = (a : ℝ) / b := Real.pow_rpow_inv_natCast hab0 hk.ne'

/-- Quadratic lower bound `1 + p x + (p / 2) x^2 ≤ (1 + x)^p` for `p ≥ 2` and `x ≥ -1`. -/
lemma rpow_one_add_quad_le {p x : ℝ} (hp : 2 ≤ p) (hx : -1 ≤ x) :
    1 + p * x + (p / 2) * x ^ 2 ≤ (1 + x) ^ p := by
  have h1x : 0 ≤ 1 + x := by linarith
  have hz : -1 ≤ 2 * x + x ^ 2 := by nlinarith [sq_nonneg (1 + x)]
  have hp2 : 1 ≤ p / 2 := by linarith
  have hb := one_add_mul_self_le_rpow_one_add hz hp2
  have heq : (1 + (2 * x + x ^ 2)) ^ (p / 2) = (1 + x) ^ p := by
    rw [show 1 + (2 * x + x ^ 2) = (1 + x) ^ 2 by ring,
      ← Real.rpow_natCast (1 + x) 2, ← Real.rpow_mul h1x]
    congr 1
    norm_num
    ring
  linarith

/-- First-order tangent lower bound for `x ^ p` (`p ≥ 1`, `x0 > 0`, `x ≥ 0`). -/
lemma rpow_tangent_le {p x0 x : ℝ} (hp : 1 ≤ p) (hx0 : 0 < x0) (hx : 0 ≤ x) :
    x0 ^ p + p * x0 ^ (p - 1) * (x - x0) ≤ x ^ p := by
  have hz : -1 ≤ (x - x0) / x0 := by
    have hdiv : 0 ≤ x / x0 := div_nonneg hx hx0.le
    have heq : 1 + (x - x0) / x0 = x / x0 := by field_simp; ring
    linarith
  have hb := one_add_mul_self_le_rpow_one_add hz hp
  have hmul := mul_le_mul_of_nonneg_left hb (Real.rpow_nonneg hx0.le p)
  have hrhs : x0 ^ p * (1 + (x - x0) / x0) ^ p = x ^ p := by
    have heq : 1 + (x - x0) / x0 = x / x0 := by field_simp; ring
    rw [heq, ← Real.mul_rpow hx0.le (div_nonneg hx hx0.le), mul_div_cancel₀ x hx0.ne']
  have hlhs : x0 ^ p * (1 + p * ((x - x0) / x0)) = x0 ^ p + p * x0 ^ (p - 1) * (x - x0) := by
    have hsub : x0 ^ (p - 1) = x0 ^ p / x0 := by
      rw [Real.rpow_sub hx0, Real.rpow_one]
    rw [hsub]
    field_simp
  linarith

/-- Secant upper bound for `x ^ p` on `[xa, xb]` (`p ≥ 1`, `0 ≤ xa < xb`). -/
lemma rpow_secant_ge {p xa xb x : ℝ} (hp : 1 ≤ p) (hxa : 0 ≤ xa) (hab : xa < xb)
    (hlo : xa ≤ x) (hhi : x ≤ xb) :
    x ^ p ≤ ((xb - x) / (xb - xa)) * xa ^ p + ((x - xa) / (xb - xa)) * xb ^ p := by
  have hden : 0 < xb - xa := sub_pos.mpr hab
  have ha : 0 ≤ (xb - x) / (xb - xa) := div_nonneg (sub_nonneg.mpr hhi) hden.le
  have hb : 0 ≤ (x - xa) / (xb - xa) := div_nonneg (sub_nonneg.mpr hlo) hden.le
  have hsum : (xb - x) / (xb - xa) + (x - xa) / (xb - xa) = 1 := by field_simp; ring
  have hx_eq : ((xb - x) / (xb - xa)) * xa + ((x - xa) / (xb - xa)) * xb = x := by
    field_simp; ring
  have hconv := (convexOn_rpow hp).2 (Set.mem_Ici.mpr hxa)
    (Set.mem_Ici.mpr (hxa.trans hab.le)) ha hb hsum
  simp only [smul_eq_mul] at hconv
  rwa [hx_eq] at hconv

/-- Generic tangent-secant box lemma on `ta ≤ t ≤ tb ≤ 1`. -/
lemma tangent_secant_box_left {p t pa pb ta tb a0 b0 ca cb Alo Blo A1lo A1hi B1lo B1hi CAhi CBhi Mlo Mhi : ℝ}
    (hpa1 : 2 ≤ pa) (hpa : pa ≤ p) (hpb : p ≤ pb)
    (hta : ta ≤ t) (htb : t ≤ tb)
    (htab : ta < tb) (htb1 : tb ≤ 1) (hta0 : 0 ≤ ta)
    (ha0_eq : a0 = (1 + (ta + tb) / 2) / 3)
    (hb0_eq : b0 = (5 - (ta + tb) / 2) / 6)
    (hca_eq : ca = (1 - ta) / 2)
    (hcb_eq : cb = (1 - tb) / 2)
    (hAlo : Alo ≤ a0 ^ pb) (hBlo : Blo ≤ b0 ^ pb)
    (hA1lo : A1lo ≤ a0 ^ (pb - 1)) (hA1hi : a0 ^ (pa - 1) ≤ A1hi)
    (hB1lo : B1lo ≤ b0 ^ (pb - 1)) (hB1hi : b0 ^ (pa - 1) ≤ B1hi)
    (hCAhi : ca ^ pa ≤ CAhi) (hCBhi : cb ^ pa ≤ CBhi)
    (hMlo1 : Mlo ≤ pa * ((A1lo - B1hi) / 3))
    (hMlo2 : Mlo ≤ pb * ((A1lo - B1hi) / 3))
    (hMhi1 : pa * ((A1hi - B1lo) / 3) ≤ Mhi)
    (hMhi2 : pb * ((A1hi - B1lo) / 3) ≤ Mhi)
    (hV1 : 1 ≤ Alo + 2 * Blo - Mhi * ((tb - ta) / 2) - 2 * CAhi)
    (hV2 : 1 ≤ Alo + 2 * Blo - (CAhi + CBhi))
    (hV3 : 1 ≤ Alo + 2 * Blo + Mlo * ((tb - ta) / 2) - 2 * CBhi) :
    1 + 2 * (|1 - t| / 2) ^ p ≤ ((1 + t) / 3) ^ p + 2 * ((5 - t) / 6) ^ p := by
  have hp1 : 1 ≤ p := by linarith
  have ha0_pos : 0 < a0 := by rw [ha0_eq]; linarith
  have ha0_le1 : a0 ≤ 1 := by rw [ha0_eq]; linarith
  have hb0_pos : 0 < b0 := by rw [hb0_eq]; linarith
  have hb0_le1 : b0 ≤ 1 := by rw [hb0_eq]; linarith
  let t0 : ℝ := (ta + tb) / 2
  have ht1 : a0 ^ p + p * a0 ^ (p - 1) * ((1 + t) / 3 - a0) ≤ ((1 + t) / 3) ^ p :=
    rpow_tangent_le hp1 ha0_pos (by linarith)
  have ht2 : b0 ^ p + p * b0 ^ (p - 1) * ((5 - t) / 6 - b0) ≤ ((5 - t) / 6) ^ p :=
    rpow_tangent_le hp1 hb0_pos (by linarith)
  have ha_pow : Alo ≤ a0 ^ p :=
    hAlo.trans (Real.rpow_le_rpow_of_exponent_ge' ha0_pos.le ha0_le1 (by linarith) hpb)
  have hb_pow : Blo ≤ b0 ^ p :=
    hBlo.trans (Real.rpow_le_rpow_of_exponent_ge' hb0_pos.le hb0_le1 (by linarith) hpb)
  have ha1_lo : A1lo ≤ a0 ^ (p - 1) :=
    hA1lo.trans (Real.rpow_le_rpow_of_exponent_ge' ha0_pos.le ha0_le1 (by linarith) (by linarith))
  have ha1_hi : a0 ^ (p - 1) ≤ A1hi :=
    (Real.rpow_le_rpow_of_exponent_ge' ha0_pos.le ha0_le1 (by linarith) (by linarith)).trans hA1hi
  have hb1_lo : B1lo ≤ b0 ^ (p - 1) :=
    hB1lo.trans (Real.rpow_le_rpow_of_exponent_ge' hb0_pos.le hb0_le1 (by linarith) (by linarith))
  have hb1_hi : b0 ^ (p - 1) ≤ B1hi :=
    (Real.rpow_le_rpow_of_exponent_ge' hb0_pos.le hb0_le1 (by linarith) (by linarith)).trans hB1hi
  have hcb0 : 0 ≤ cb := by rw [hcb_eq]; linarith
  have hca_le1 : ca ≤ 1 := by rw [hca_eq]; linarith
  have hcb_lt_ca : cb < ca := by rw [hca_eq, hcb_eq]; linarith
  have hc_eq : |1 - t| / 2 = (1 - t) / 2 := by rw [abs_of_nonneg (by linarith)]
  have hsec := rpow_secant_ge hp1 hcb0 hcb_lt_ca
    (show cb ≤ (1 - t) / 2 by rw [hcb_eq]; linarith)
    (show (1 - t) / 2 ≤ ca by rw [hca_eq]; linarith)
  have hca_pow : ca ^ p ≤ CAhi :=
    (Real.rpow_le_rpow_of_exponent_ge' (hcb0.trans hcb_lt_ca.le) hca_le1 (by linarith) hpa).trans hCAhi
  have hcb_pow : cb ^ p ≤ CBhi :=
    (Real.rpow_le_rpow_of_exponent_ge' hcb0 (hcb_lt_ca.le.trans hca_le1) (by linarith) hpa).trans hCBhi
  have hw1 : (ca - (1 - t) / 2) / (ca - cb) = (t - ta) / (tb - ta) := by
    rw [hca_eq, hcb_eq, show (1 - ta) / 2 - (1 - t) / 2 = (t - ta) / 2 by ring,
      show (1 - ta) / 2 - (1 - tb) / 2 = (tb - ta) / 2 by ring,
      div_div_div_cancel_right₀ (by norm_num : (2 : ℝ) ≠ 0)]
  have hw2 : ((1 - t) / 2 - cb) / (ca - cb) = (tb - t) / (tb - ta) := by
    rw [hca_eq, hcb_eq, show (1 - t) / 2 - (1 - tb) / 2 = (tb - t) / 2 by ring,
      show (1 - ta) / 2 - (1 - tb) / 2 = (tb - ta) / 2 by ring,
      div_div_div_cancel_right₀ (by norm_num : (2 : ℝ) ≠ 0)]
  rw [hc_eq]
  rw [hw1, hw2] at hsec
  have hden : 0 < tb - ta := sub_pos.mpr htab
  have hsec_hi : ((1 - t) / 2) ^ p ≤
      ((tb - t) / (tb - ta)) * CAhi + ((t - ta) / (tb - ta)) * CBhi := by
    have h1 := mul_le_mul_of_nonneg_left hcb_pow (div_nonneg (sub_nonneg.mpr hta) hden.le)
    have h2 := mul_le_mul_of_nonneg_left hca_pow (div_nonneg (sub_nonneg.mpr htb) hden.le)
    linarith
  let D : ℝ := (a0 ^ (p - 1) - b0 ^ (p - 1)) / 3
  have hD_lo : (A1lo - B1hi) / 3 ≤ D := by dsimp [D]; linarith
  have hD_hi : D ≤ (A1hi - B1lo) / 3 := by dsimp [D]; linarith
  have hpD_lo : Mlo ≤ p * D := by
    rcases le_total 0 ((A1lo - B1hi) / 3) with hpos | hneg
    · exact hMlo1.trans (mul_le_mul hpa hD_lo hpos (by linarith))
    · have : pb * ((A1lo - B1hi) / 3) ≤ p * ((A1lo - B1hi) / 3) :=
        mul_le_mul_of_nonpos_right hpb hneg
      exact hMlo2.trans (this.trans (mul_le_mul_of_nonneg_left hD_lo (by linarith)))
  have hpD_hi : p * D ≤ Mhi := by
    rcases le_total 0 ((A1hi - B1lo) / 3) with hpos | hneg
    · have : p * D ≤ p * ((A1hi - B1lo) / 3) := mul_le_mul_of_nonneg_left hD_hi (by linarith)
      exact (this.trans (mul_le_mul_of_nonneg_right hpb hpos)).trans hMhi2
    · have : p * D ≤ p * ((A1hi - B1lo) / 3) := mul_le_mul_of_nonneg_left hD_hi (by linarith)
      exact (this.trans (mul_le_mul_of_nonpos_right hpa hneg)).trans hMhi1
  have hcomb : Alo + 2 * Blo + (p * D) * (t - t0) ≤ ((1 + t) / 3) ^ p + 2 * ((5 - t) / 6) ^ p := by
    have hlin : (p * a0 ^ (p - 1) * ((1 + t) / 3 - a0)) + 2 * (p * b0 ^ (p - 1) * ((5 - t) / 6 - b0)) =
        (p * D) * (t - t0) := by
      dsimp [D, t0]; rw [ha0_eq, hb0_eq]; ring
    linarith
  rcases le_total t t0 with htt0 | htt0
  · have hM : Mhi * (t - t0) ≤ (p * D) * (t - t0) :=
      mul_le_mul_of_nonpos_right hpD_hi (sub_nonpos.mpr htt0)
    -- Affine on [ta, t0]: express t as convex combination of ta and t0!
    let lam : ℝ := (t0 - t) / ((tb - ta) / 2)
    have hlam0 : 0 ≤ lam := div_nonneg (sub_nonneg.mpr htt0) (by linarith)
    have hlam1 : 0 ≤ 1 - lam := by
      have : 1 - lam = (t - ta) / ((tb - ta) / 2) := by dsimp [lam, t0]; field_simp; ring
      rw [this]; exact div_nonneg (sub_nonneg.mpr hta) (by linarith)
    have haff : 1 ≤ Alo + 2 * Blo + Mhi * (t - t0) -
        2 * (((tb - t) / (tb - ta)) * CAhi + ((t - ta) / (tb - ta)) * CBhi) := by
      have hid : Alo + 2 * Blo + Mhi * (t - t0) -
          2 * (((tb - t) / (tb - ta)) * CAhi + ((t - ta) / (tb - ta)) * CBhi) =
          lam * (Alo + 2 * Blo - Mhi * ((tb - ta) / 2) - 2 * CAhi) +
          (1 - lam) * (Alo + 2 * Blo - (CAhi + CBhi)) := by
        dsimp [lam, t0]; field_simp; ring
      rw [hid]
      nlinarith
    linarith
  · have hM : Mlo * (t - t0) ≤ (p * D) * (t - t0) :=
      mul_le_mul_of_nonneg_right hpD_lo (sub_nonneg.mpr htt0)
    let lam : ℝ := (t - t0) / ((tb - ta) / 2)
    have hlam0 : 0 ≤ lam := div_nonneg (sub_nonneg.mpr htt0) (by linarith)
    have hlam1 : 0 ≤ 1 - lam := by
      have : 1 - lam = (tb - t) / ((tb - ta) / 2) := by dsimp [lam, t0]; field_simp; ring
      rw [this]; exact div_nonneg (sub_nonneg.mpr htb) (by linarith)
    have haff : 1 ≤ Alo + 2 * Blo + Mlo * (t - t0) -
        2 * (((tb - t) / (tb - ta)) * CAhi + ((t - ta) / (tb - ta)) * CBhi) := by
      have hid : Alo + 2 * Blo + Mlo * (t - t0) -
          2 * (((tb - t) / (tb - ta)) * CAhi + ((t - ta) / (tb - ta)) * CBhi) =
          (1 - lam) * (Alo + 2 * Blo - (CAhi + CBhi)) +
          lam * (Alo + 2 * Blo + Mlo * ((tb - ta) / 2) - 2 * CBhi) := by
        dsimp [lam, t0]; field_simp; ring
      rw [hid]
      nlinarith
    linarith

/-- Generic tangent-secant box lemma on `1 ≤ ta ≤ t ≤ tb ≤ 2`. -/
lemma tangent_secant_box_right {p t pa pb ta tb a0 b0 ca cb Alo Blo A1lo A1hi B1lo B1hi CAhi CBhi Mlo Mhi : ℝ}
    (hpa1 : 2 ≤ pa) (hpa : pa ≤ p) (hpb : p ≤ pb)
    (hta : ta ≤ t) (htb : t ≤ tb)
    (htab : ta < tb) (hta1 : 1 ≤ ta) (htb2 : tb ≤ 2)
    (ha0_eq : a0 = (1 + (ta + tb) / 2) / 3)
    (hb0_eq : b0 = (5 - (ta + tb) / 2) / 6)
    (hca_eq : ca = (ta - 1) / 2)
    (hcb_eq : cb = (tb - 1) / 2)
    (hAlo : Alo ≤ a0 ^ pb) (hBlo : Blo ≤ b0 ^ pb)
    (hA1lo : A1lo ≤ a0 ^ (pb - 1)) (hA1hi : a0 ^ (pa - 1) ≤ A1hi)
    (hB1lo : B1lo ≤ b0 ^ (pb - 1)) (hB1hi : b0 ^ (pa - 1) ≤ B1hi)
    (hCAhi : ca ^ pa ≤ CAhi) (hCBhi : cb ^ pa ≤ CBhi)
    (hMlo1 : Mlo ≤ pa * ((A1lo - B1hi) / 3))
    (hMlo2 : Mlo ≤ pb * ((A1lo - B1hi) / 3))
    (hMhi1 : pa * ((A1hi - B1lo) / 3) ≤ Mhi)
    (hMhi2 : pb * ((A1hi - B1lo) / 3) ≤ Mhi)
    (hV1 : 1 ≤ Alo + 2 * Blo - Mhi * ((tb - ta) / 2) - 2 * CAhi)
    (hV2 : 1 ≤ Alo + 2 * Blo - (CAhi + CBhi))
    (hV3 : 1 ≤ Alo + 2 * Blo + Mlo * ((tb - ta) / 2) - 2 * CBhi) :
    1 + 2 * (|1 - t| / 2) ^ p ≤ ((1 + t) / 3) ^ p + 2 * ((5 - t) / 6) ^ p := by
  have hp1 : 1 ≤ p := by linarith
  have ha0_pos : 0 < a0 := by rw [ha0_eq]; linarith
  have ha0_le1 : a0 ≤ 1 := by rw [ha0_eq]; linarith
  have hb0_pos : 0 < b0 := by rw [hb0_eq]; linarith
  have hb0_le1 : b0 ≤ 1 := by rw [hb0_eq]; linarith
  let t0 : ℝ := (ta + tb) / 2
  have ht1 : a0 ^ p + p * a0 ^ (p - 1) * ((1 + t) / 3 - a0) ≤ ((1 + t) / 3) ^ p :=
    rpow_tangent_le hp1 ha0_pos (by linarith)
  have ht2 : b0 ^ p + p * b0 ^ (p - 1) * ((5 - t) / 6 - b0) ≤ ((5 - t) / 6) ^ p :=
    rpow_tangent_le hp1 hb0_pos (by linarith)
  have ha_pow : Alo ≤ a0 ^ p :=
    hAlo.trans (Real.rpow_le_rpow_of_exponent_ge' ha0_pos.le ha0_le1 (by linarith) hpb)
  have hb_pow : Blo ≤ b0 ^ p :=
    hBlo.trans (Real.rpow_le_rpow_of_exponent_ge' hb0_pos.le hb0_le1 (by linarith) hpb)
  have ha1_lo : A1lo ≤ a0 ^ (p - 1) :=
    hA1lo.trans (Real.rpow_le_rpow_of_exponent_ge' ha0_pos.le ha0_le1 (by linarith) (by linarith))
  have ha1_hi : a0 ^ (p - 1) ≤ A1hi :=
    (Real.rpow_le_rpow_of_exponent_ge' ha0_pos.le ha0_le1 (by linarith) (by linarith)).trans hA1hi
  have hb1_lo : B1lo ≤ b0 ^ (p - 1) :=
    hB1lo.trans (Real.rpow_le_rpow_of_exponent_ge' hb0_pos.le hb0_le1 (by linarith) (by linarith))
  have hb1_hi : b0 ^ (p - 1) ≤ B1hi :=
    (Real.rpow_le_rpow_of_exponent_ge' hb0_pos.le hb0_le1 (by linarith) (by linarith)).trans hB1hi
  have hca0 : 0 ≤ ca := by rw [hca_eq]; linarith
  have hcb_le1 : cb ≤ 1 := by rw [hcb_eq]; linarith
  have hca_lt_cb : ca < cb := by rw [hca_eq, hcb_eq]; linarith
  have hc_eq : |1 - t| / 2 = (t - 1) / 2 := by
    rw [abs_of_nonpos (by linarith)]; ring
  have hsec := rpow_secant_ge hp1 hca0 hca_lt_cb
    (show ca ≤ (t - 1) / 2 by rw [hca_eq]; linarith)
    (show (t - 1) / 2 ≤ cb by rw [hcb_eq]; linarith)
  have hca_pow : ca ^ p ≤ CAhi :=
    (Real.rpow_le_rpow_of_exponent_ge' hca0 (hca_lt_cb.le.trans hcb_le1) (by linarith) hpa).trans hCAhi
  have hcb_pow : cb ^ p ≤ CBhi :=
    (Real.rpow_le_rpow_of_exponent_ge' (hca0.trans hca_lt_cb.le) hcb_le1 (by linarith) hpa).trans hCBhi
  have hw1 : (cb - (t - 1) / 2) / (cb - ca) = (tb - t) / (tb - ta) := by
    rw [hca_eq, hcb_eq, show (tb - 1) / 2 - (t - 1) / 2 = (tb - t) / 2 by ring,
      show (tb - 1) / 2 - (ta - 1) / 2 = (tb - ta) / 2 by ring,
      div_div_div_cancel_right₀ (by norm_num : (2 : ℝ) ≠ 0)]
  have hw2 : ((t - 1) / 2 - ca) / (cb - ca) = (t - ta) / (tb - ta) := by
    rw [hca_eq, hcb_eq, show (t - 1) / 2 - (ta - 1) / 2 = (t - ta) / 2 by ring,
      show (tb - 1) / 2 - (ta - 1) / 2 = (tb - ta) / 2 by ring,
      div_div_div_cancel_right₀ (by norm_num : (2 : ℝ) ≠ 0)]
  rw [hc_eq]
  rw [hw1, hw2] at hsec
  have hden : 0 < tb - ta := sub_pos.mpr htab
  have hsec_hi : ((t - 1) / 2) ^ p ≤
      ((tb - t) / (tb - ta)) * CAhi + ((t - ta) / (tb - ta)) * CBhi := by
    have h1 := mul_le_mul_of_nonneg_left hca_pow (div_nonneg (sub_nonneg.mpr htb) hden.le)
    have h2 := mul_le_mul_of_nonneg_left hcb_pow (div_nonneg (sub_nonneg.mpr hta) hden.le)
    linarith
  let D : ℝ := (a0 ^ (p - 1) - b0 ^ (p - 1)) / 3
  have hD_lo : (A1lo - B1hi) / 3 ≤ D := by dsimp [D]; linarith
  have hD_hi : D ≤ (A1hi - B1lo) / 3 := by dsimp [D]; linarith
  have hpD_lo : Mlo ≤ p * D := by
    rcases le_total 0 ((A1lo - B1hi) / 3) with hpos | hneg
    · exact hMlo1.trans (mul_le_mul hpa hD_lo hpos (by linarith))
    · have : pb * ((A1lo - B1hi) / 3) ≤ p * ((A1lo - B1hi) / 3) :=
        mul_le_mul_of_nonpos_right hpb hneg
      exact hMlo2.trans (this.trans (mul_le_mul_of_nonneg_left hD_lo (by linarith)))
  have hpD_hi : p * D ≤ Mhi := by
    rcases le_total 0 ((A1hi - B1lo) / 3) with hpos | hneg
    · have : p * D ≤ p * ((A1hi - B1lo) / 3) := mul_le_mul_of_nonneg_left hD_hi (by linarith)
      exact (this.trans (mul_le_mul_of_nonneg_right hpb hpos)).trans hMhi2
    · have : p * D ≤ p * ((A1hi - B1lo) / 3) := mul_le_mul_of_nonneg_left hD_hi (by linarith)
      exact (this.trans (mul_le_mul_of_nonpos_right hpa hneg)).trans hMhi1
  have hcomb : Alo + 2 * Blo + (p * D) * (t - t0) ≤ ((1 + t) / 3) ^ p + 2 * ((5 - t) / 6) ^ p := by
    have hlin : (p * a0 ^ (p - 1) * ((1 + t) / 3 - a0)) + 2 * (p * b0 ^ (p - 1) * ((5 - t) / 6 - b0)) =
        (p * D) * (t - t0) := by
      dsimp [D, t0]; rw [ha0_eq, hb0_eq]; ring
    linarith
  rcases le_total t t0 with htt0 | htt0
  · have hM : Mhi * (t - t0) ≤ (p * D) * (t - t0) :=
      mul_le_mul_of_nonpos_right hpD_hi (sub_nonpos.mpr htt0)
    let lam : ℝ := (t0 - t) / ((tb - ta) / 2)
    have hlam0 : 0 ≤ lam := div_nonneg (sub_nonneg.mpr htt0) (by linarith)
    have hlam1 : 0 ≤ 1 - lam := by
      have : 1 - lam = (t - ta) / ((tb - ta) / 2) := by dsimp [lam, t0]; field_simp; ring
      rw [this]; exact div_nonneg (sub_nonneg.mpr hta) (by linarith)
    have haff : 1 ≤ Alo + 2 * Blo + Mhi * (t - t0) -
        2 * (((tb - t) / (tb - ta)) * CAhi + ((t - ta) / (tb - ta)) * CBhi) := by
      have hid : Alo + 2 * Blo + Mhi * (t - t0) -
          2 * (((tb - t) / (tb - ta)) * CAhi + ((t - ta) / (tb - ta)) * CBhi) =
          lam * (Alo + 2 * Blo - Mhi * ((tb - ta) / 2) - 2 * CAhi) +
          (1 - lam) * (Alo + 2 * Blo - (CAhi + CBhi)) := by
        dsimp [lam, t0]; field_simp; ring
      rw [hid]
      nlinarith
    linarith
  · have hM : Mlo * (t - t0) ≤ (p * D) * (t - t0) :=
      mul_le_mul_of_nonneg_right hpD_lo (sub_nonneg.mpr htt0)
    let lam : ℝ := (t - t0) / ((tb - ta) / 2)
    have hlam0 : 0 ≤ lam := div_nonneg (sub_nonneg.mpr htt0) (by linarith)
    have hlam1 : 0 ≤ 1 - lam := by
      have : 1 - lam = (tb - t) / ((tb - ta) / 2) := by dsimp [lam, t0]; field_simp; ring
      rw [this]; exact div_nonneg (sub_nonneg.mpr htb) (by linarith)
    have haff : 1 ≤ Alo + 2 * Blo + Mlo * (t - t0) -
        2 * (((tb - t) / (tb - ta)) * CAhi + ((t - ta) / (tb - ta)) * CBhi) := by
      have hid : Alo + 2 * Blo + Mlo * (t - t0) -
          2 * (((tb - t) / (tb - ta)) * CAhi + ((t - ta) / (tb - ta)) * CBhi) =
          (1 - lam) * (Alo + 2 * Blo - (CAhi + CBhi)) +
          lam * (Alo + 2 * Blo + Mlo * ((tb - ta) / 2) - 2 * CBhi) := by
        dsimp [lam, t0]; field_simp; ring
      rw [hid]
      nlinarith
    linarith

/-- Threshold consequences for `p ≤ log 3 / log (3 / 2)`. -/
lemma threshold_bounds {p : ℝ} (hpT : p ≤ Real.log 3 / Real.log (3 / 2)) :
    p ≤ 68 / 25 ∧ 1 ≤ 3 * (2 / 3 : ℝ) ^ p := by
  have hlog32 : 0 < Real.log (3 / 2 : ℝ) := Real.log_pos (by norm_num)
  have hplog : p * Real.log (3 / 2 : ℝ) ≤ Real.log 3 :=
    (le_div_iff₀ hlog32).mp hpT
  constructor
  · have hpow : (3 : ℝ) ^ (25 : ℕ) < (3 / 2 : ℝ) ^ (68 : ℕ) := by norm_num
    have hlog_lt := Real.log_lt_log (by positivity) hpow
    rw [Real.log_pow, Real.log_pow] at hlog_lt
    have hdiv : Real.log 3 / Real.log (3 / 2 : ℝ) < 68 / 25 := by
      rw [div_lt_div_iff₀ hlog32 (by norm_num)]
      linarith
    exact hpT.trans hdiv.le
  · have h32p : (3 / 2 : ℝ) ^ p ≤ 3 := by
      rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 3 / 2)]
      calc Real.exp (Real.log (3 / 2 : ℝ) * p)
          ≤ Real.exp (Real.log 3) := Real.exp_le_exp.mpr (by linarith)
        _ = 3 := Real.exp_log (by norm_num)
    have hprod : (2 / 3 : ℝ) ^ p * (3 / 2 : ℝ) ^ p = 1 := by
      rw [← Real.mul_rpow (by norm_num) (by norm_num)]
      norm_num
    have h23pos : 0 < (2 / 3 : ℝ) ^ p := Real.rpow_pos_of_pos (by norm_num) p
    nlinarith

/-- Analytic region 1: near `t = 1` (`t ∈ [7/9, 11/9]`) for `p ∈ [5/2, 68/25]` and `1 ≤ 3*(2/3)^p`. -/
lemma region_near_one {p t : ℝ} (hp : 5 / 2 ≤ p) (h23 : 1 ≤ 3 * (2 / 3 : ℝ) ^ p)
    (hta : 7 / 9 ≤ t) (htb : t ≤ 11 / 9) :
    1 + 2 * (|1 - t| / 2) ^ p ≤ ((1 + t) / 3) ^ p + 2 * ((5 - t) / 6) ^ p := by
  let w : ℝ := (1 - t) / 2
  have hw_lo : -1 / 9 ≤ w := by dsimp [w]; linarith
  have hw_hi : w ≤ 1 / 9 := by dsimp [w]; linarith
  have hw_abs : |w| ≤ 1 / 9 := abs_le.mpr ⟨by linarith, hw_hi⟩
  have hp2 : 2 ≤ p := by linarith
  have hq1 := rpow_one_add_quad_le hp2 (show -1 ≤ -w by linarith)
  have hq2 := rpow_one_add_quad_le hp2 (show -1 ≤ w / 2 by linarith)
  have hsum_quad : 3 + (15 / 8 : ℝ) * w ^ 2 ≤ (1 - w) ^ p + 2 * (1 + w / 2) ^ p := by
    have hpw : (15 / 8 : ℝ) * w ^ 2 ≤ (3 * p / 4) * w ^ 2 :=
      mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg w)
    have hlin : 3 + (3 * p / 4) * w ^ 2 ≤
        (1 + p * (-w) + (p / 2) * (-w) ^ 2) + 2 * (1 + p * (w / 2) + (p / 2) * (w / 2) ^ 2) := by
      nlinarith
    have he1 : 1 + -w = 1 - w := by ring
    rw [he1] at hq1
    linarith
  have htail : 2 * (3 / 2 * |w|) ^ p ≤ (15 / 8 : ℝ) * w ^ 2 := by
    have h32w_nonneg : 0 ≤ (3 / 2 : ℝ) * |w| := by positivity
    have h32w_le1 : (3 / 2 : ℝ) * |w| ≤ 1 / 6 := by linarith
    have hexp : ((3 / 2 : ℝ) * |w|) ^ p ≤ ((3 / 2 : ℝ) * |w|) ^ (5 / 2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_ge' h32w_nonneg (by linarith) (by norm_num) hp
    have hsplit : ((3 / 2 : ℝ) * |w|) ^ (5 / 2 : ℝ) =
        (9 / 4 : ℝ) * w ^ 2 * ((3 / 2 : ℝ) * |w|) ^ (1 / 2 : ℝ) := by
      have h25 : (5 / 2 : ℝ) = (2 : ℕ) + (1 / 2 : ℝ) := by norm_num
      rw [h25, Real.rpow_add' h32w_nonneg (by norm_num), Real.rpow_natCast]
      have hw2 : ((3 / 2 : ℝ) * |w|) ^ 2 = (9 / 4 : ℝ) * w ^ 2 := by
        rw [mul_pow, sq_abs]; ring
      rw [hw2]
    have hhalf : ((3 / 2 : ℝ) * |w|) ^ (1 / 2 : ℝ) ≤ 5 / 12 := by
      calc ((3 / 2 : ℝ) * |w|) ^ (1 / 2 : ℝ)
          ≤ (1 / 6 : ℝ) ^ (1 / 2 : ℝ) := Real.rpow_le_rpow h32w_nonneg h32w_le1 (by norm_num)
        _ ≤ 5 / 12 := by
          simpa using rational_rpow_le 5 12 1 6 1 2 (by decide) (by decide) (by decide) (by decide)
    nlinarith [sq_nonneg w]
  have hcore : 3 + 2 * (3 / 2 * |w|) ^ p ≤ (1 - w) ^ p + 2 * (1 + w / 2) ^ p := by linarith
  have hscale := mul_le_mul_of_nonneg_left hcore
    (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2 / 3) p)
  have ha_eq : (2 / 3 : ℝ) ^ p * (1 - w) ^ p = ((1 + t) / 3) ^ p := by
    rw [← Real.mul_rpow (by norm_num) (by dsimp [w]; linarith)]
    congr 1; dsimp [w]; ring
  have hb_eq : (2 / 3 : ℝ) ^ p * (1 + w / 2) ^ p = ((5 - t) / 6) ^ p := by
    rw [← Real.mul_rpow (by norm_num) (by dsimp [w]; linarith)]
    congr 1; dsimp [w]; ring
  have hc_eq : (2 / 3 : ℝ) ^ p * (3 / 2 * |w|) ^ p = (|1 - t| / 2) ^ p := by
    rw [← Real.mul_rpow (by norm_num) (by positivity)]
    congr 1; dsimp [w]; rw [abs_div, show |(2 : ℝ)| = 2 by norm_num]; ring
  nlinarith

/-- Parameterized analytic lemma near `t = 2` (`t ∈ [tlo, 2]`) for `p ∈ [2, pb]`. -/
lemma region_near_two_param {p t pb tlo H : ℝ} (hp2 : 2 ≤ p) (hpb : p ≤ pb)
    (htlo_lo : 1 < tlo) (htlo_hi : tlo < 2)
    (hta : tlo ≤ t) (htb : t ≤ 2)
    (_hH_pos : 0 ≤ H) (hH : H ≤ (1 / 2 : ℝ) ^ pb)
    (hcoef : 1 ≤ H * (2 + 6 / (1 + pb * (2 - tlo)))) :
    1 + 2 * (|1 - t| / 2) ^ p ≤ ((1 + t) / 3) ^ p + 2 * ((5 - t) / 6) ^ p := by
  let s : ℝ := (2 - t) / 6
  let ymax : ℝ := 2 - tlo
  have hs0 : 0 ≤ s := by dsimp [s]; linarith
  have hymax_pos : 0 < ymax := by dsimp [ymax]; linarith
  have h6s_le : 6 * s ≤ ymax := by dsimp [s, ymax]; linarith
  have h6s_lt1 : 6 * s < 1 := by dsimp [s]; linarith
  have hp1 : 1 ≤ p := by linarith
  have hp0 : 0 < p := by linarith
  have hpb0 : 0 < pb := by linarith
  have hb1 : 1 - 2 * p * s ≤ (1 - 2 * s) ^ p := by
    have h := one_add_mul_self_le_rpow_one_add (show -1 ≤ -(2 * s) by dsimp [s]; linarith) hp1
    have he : 1 + -(2 * s) = 1 - 2 * s := by ring
    rw [he] at h
    linarith
  have hb2 : 1 + 2 * p * s ≤ (1 + 2 * s) ^ p := by
    have h := one_add_mul_self_le_rpow_one_add (show -1 ≤ 2 * s by linarith) hp1
    linarith
  have hb3 : (1 - 6 * s) ^ p ≤ 1 - (6 * p / (1 + p * ymax)) * s := by
    have h1my_nonneg : 0 ≤ 1 - 6 * s := by linarith
    have h1py_pos : 0 < 1 + 6 * s := by linarith
    have hsub_le_inv : 1 - 6 * s ≤ 1 / (1 + 6 * s) := by
      rw [le_div_iff₀ h1py_pos]
      nlinarith [sq_nonneg (6 * s)]
    have hpow_le : (1 - 6 * s) ^ p ≤ 1 / (1 + 6 * s) ^ p := by
      calc (1 - 6 * s) ^ p ≤ (1 / (1 + 6 * s)) ^ p :=
            Real.rpow_le_rpow h1my_nonneg hsub_le_inv hp0.le
        _ = 1 / (1 + 6 * s) ^ p := by rw [one_div, Real.inv_rpow h1py_pos.le, one_div]
    have hp_pos : 0 < 1 + 6 * p * s := by positivity
    have h1 := one_add_mul_self_le_rpow_one_add (show -1 ≤ 6 * s by linarith) hp1
    have hpow_inv : (1 - 6 * s) ^ p ≤ 1 / (1 + 6 * p * s) :=
      hpow_le.trans (div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 1) hp_pos (by linarith))
    have hd_pos : 0 < 1 + p * ymax := by positivity
    have hrat : 1 / (1 + 6 * p * s) ≤ 1 - (6 * p / (1 + p * ymax)) * s := by
      have hkey : 6 * p * s ≤ p * ymax := by
        calc 6 * p * s = p * (6 * s) := by ring
          _ ≤ p * ymax := mul_le_mul_of_nonneg_left h6s_le hp0.le
      have hprod : 1 + p * ymax ≤ (1 + p * ymax - 6 * p * s) * (1 + 6 * p * s) := by
        nlinarith [mul_nonneg (mul_nonneg hp0.le hs0) (sub_nonneg.mpr hkey)]
      have heq : 1 - (6 * p / (1 + p * ymax)) * s = (1 + p * ymax - 6 * p * s) / (1 + p * ymax) := by
        field_simp
      rw [heq, div_le_div_iff₀ hp_pos hd_pos]
      linarith
    exact hpow_inv.trans hrat
  have hhalf_lo : H ≤ (1 / 2 : ℝ) ^ p :=
    hH.trans (Real.rpow_le_rpow_of_exponent_ge' (by norm_num) (by norm_num) hp0.le hpb)
  have hhalf_pos : 0 ≤ (1 / 2 : ℝ) ^ p := by positivity
  have hmid1 : (1 / 2 + s) ^ p = (1 / 2 : ℝ) ^ p * (1 + 2 * s) ^ p := by
    rw [← Real.mul_rpow (by norm_num) (by linarith)]; congr 1; ring
  have hmid2 : (1 / 2 - 3 * s) ^ p = (1 / 2 : ℝ) ^ p * (1 - 6 * s) ^ p := by
    rw [← Real.mul_rpow (by norm_num) (by linarith)]; congr 1; ring
  have ha_eq : (1 + t) / 3 = 1 - 2 * s := by dsimp [s]; ring
  have hb_eq : (5 - t) / 6 = 1 / 2 + s := by dsimp [s]; ring
  have hc_eq : |1 - t| / 2 = 1 / 2 - 3 * s := by
    rw [abs_of_nonpos (by linarith)]; dsimp [s]; ring
  rw [ha_eq, hb_eq, hc_eq, hmid1, hmid2]
  have hd_pos : 0 < 1 + p * ymax := by positivity
  have hdiff : (2 + 6 / (1 + p * ymax)) * (p * s) ≤ (1 + 2 * s) ^ p - (1 - 6 * s) ^ p := by
    have hcalc : (2 + 6 / (1 + p * ymax)) * (p * s) = 2 * p * s + (6 * p / (1 + p * ymax)) * s := by
      field_simp
    linarith
  have hcoef_ge : 2 + 6 / (1 + pb * ymax) ≤ 2 + 6 / (1 + p * ymax) := by
    have hle : 1 + p * ymax ≤ 1 + pb * ymax := by
      have := mul_le_mul_of_nonneg_right hpb hymax_pos.le; linarith
    have hdiv := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 6) hd_pos hle
    linarith
  have hps0 : 0 ≤ p * s := mul_nonneg hp0.le hs0
  have hm1 : (2 + 6 / (1 + pb * ymax)) * (p * s) ≤ (2 + 6 / (1 + p * ymax)) * (p * s) :=
    mul_le_mul_of_nonneg_right hcoef_ge hps0
  have hbd_pos : 0 < 1 + pb * ymax := by positivity
  have hm2 : H * ((2 + 6 / (1 + pb * ymax)) * (p * s)) ≤
      (1 / 2 : ℝ) ^ p * ((1 + 2 * s) ^ p - (1 - 6 * s) ^ p) :=
    mul_le_mul hhalf_lo (hm1.trans hdiff) (by positivity) hhalf_pos
  have hfin : 2 * (p * s) ≤ 2 * (H * ((2 + 6 / (1 + pb * ymax)) * (p * s))) := by
    have := mul_le_mul_of_nonneg_right hcoef hps0
    dsimp [ymax] at hm2 ⊢
    linarith
  dsimp [ymax] at hm2
  linarith

private lemma box_leaf_0 {p t : ℝ} (hpa : (2 : ℝ) ≤ p) (hpb : p ≤ (9 / 4 : ℝ))
    (hta : (1 / 2 : ℝ) ≤ t) (htb : t ≤ (1 : ℝ)) :
    1 + 2 * (|1 - t| / 2) ^ p ≤ ((1 + t) / 3) ^ p + 2 * ((5 - t) / 6) ^ p :=
  tangent_secant_box_left
    (pa := (2 : ℝ)) (pb := (9 / 4 : ℝ)) (ta := (1 / 2 : ℝ)) (tb := (1 : ℝ))
    (a0 := (7 / 12 : ℝ)) (b0 := (17 / 24 : ℝ)) (ca := (1 / 4 : ℝ)) (cb := (0 : ℝ))
    (Alo := (3717 / 12500 : ℝ)) (Blo := (46027 / 100000 : ℝ))
    (A1lo := (50977 / 100000 : ℝ)) (A1hi := (1823 / 3125 : ℝ))
    (B1lo := (3249 / 5000 : ℝ)) (B1hi := (17709 / 25000 : ℝ))
    (CAhi := (1563 / 25000 : ℝ)) (CBhi := (0 : ℝ))
    (Mlo := (-59577 / 400000 : ℝ)) (Mhi := (-1661 / 37500 : ℝ))
    (by norm_num) hpa hpb hta htb
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
    (by have h := rational_rpow_ge 3717 12500 7 12 9 4 (by decide) (by decide) (by decide) (by decide +kernel); norm_num at h ⊢; try exact h)
    (by have h := rational_rpow_ge 46027 100000 17 24 9 4 (by decide) (by decide) (by decide) (by decide +kernel); norm_num at h ⊢; try exact h)
    (by have h := rational_rpow_ge 50977 100000 7 12 5 4 (by decide) (by decide) (by decide) (by decide +kernel); norm_num at h ⊢; try exact h)
    (by have h := rational_rpow_le 1823 3125 7 12 1 1 (by decide) (by decide) (by decide) (by decide +kernel); norm_num at h ⊢; try exact h)
    (by have h := rational_rpow_ge 3249 5000 17 24 5 4 (by decide) (by decide) (by decide) (by decide +kernel); norm_num at h ⊢; try exact h)
    (by have h := rational_rpow_le 17709 25000 17 24 1 1 (by decide) (by decide) (by decide) (by decide +kernel); norm_num at h ⊢; try exact h)
    (by have h := rational_rpow_le 1563 25000 1 4 2 1 (by decide) (by decide) (by decide) (by decide +kernel); norm_num at h ⊢; try exact h)
    (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

private lemma box_leaf_1 {p t : ℝ} (hpa : (2 : ℝ) ≤ p) (hpb : p ≤ (9 / 4 : ℝ))
    (hta : (1 : ℝ) ≤ t) (htb : t ≤ (3 / 2 : ℝ)) :
    1 + 2 * (|1 - t| / 2) ^ p ≤ ((1 + t) / 3) ^ p + 2 * ((5 - t) / 6) ^ p :=
  tangent_secant_box_right
    (pa := (2 : ℝ)) (pb := (9 / 4 : ℝ)) (ta := (1 : ℝ)) (tb := (3 / 2 : ℝ))
    (a0 := (3 / 4 : ℝ)) (b0 := (5 / 8 : ℝ)) (ca := (0 : ℝ)) (cb := (1 / 4 : ℝ))
    (Alo := (6543 / 12500 : ℝ)) (Blo := (3473 / 10000 : ℝ))
    (A1lo := (69793 / 100000 : ℝ)) (A1hi := (37501 / 50000 : ℝ))
    (B1lo := (55569 / 100000 : ℝ)) (B1hi := (31251 / 50000 : ℝ))
    (CAhi := (0 : ℝ)) (CBhi := (1563 / 25000 : ℝ))
    (Mlo := (7291 / 150000 : ℝ)) (Mhi := (58299 / 400000 : ℝ))
    (by norm_num) hpa hpb hta htb
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
    (by have h := rational_rpow_ge 6543 12500 3 4 9 4 (by decide) (by decide) (by decide) (by decide +kernel); norm_num at h ⊢; try exact h)
    (by have h := rational_rpow_ge 3473 10000 5 8 9 4 (by decide) (by decide) (by decide) (by decide +kernel); norm_num at h ⊢; try exact h)
    (by have h := rational_rpow_ge 69793 100000 3 4 5 4 (by decide) (by decide) (by decide) (by decide +kernel); norm_num at h ⊢; try exact h)
    (by have h := rational_rpow_le 37501 50000 3 4 1 1 (by decide) (by decide) (by decide) (by decide +kernel); norm_num at h ⊢; try exact h)
    (by have h := rational_rpow_ge 55569 100000 5 8 5 4 (by decide) (by decide) (by decide) (by decide +kernel); norm_num at h ⊢; try exact h)
    (by have h := rational_rpow_le 31251 50000 5 8 1 1 (by decide) (by decide) (by decide) (by decide +kernel); norm_num at h ⊢; try exact h)
    (by norm_num)
    (by have h := rational_rpow_le 1563 25000 1 4 2 1 (by decide) (by decide) (by decide) (by decide +kernel); norm_num at h ⊢; try exact h)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

private lemma box_leaf_2 {p t : ℝ} (hpa : (9 / 4 : ℝ) ≤ p) (hpb : p ≤ (5 / 2 : ℝ))
    (hta : (1 / 2 : ℝ) ≤ t) (htb : t ≤ (1 : ℝ)) :
    1 + 2 * (|1 - t| / 2) ^ p ≤ ((1 + t) / 3) ^ p + 2 * ((5 - t) / 6) ^ p :=
  tangent_secant_box_left
    (pa := (9 / 4 : ℝ)) (pb := (5 / 2 : ℝ)) (ta := (1 / 2 : ℝ)) (tb := (1 : ℝ))
    (a0 := (7 / 12 : ℝ)) (b0 := (17 / 24 : ℝ)) (ca := (1 / 4 : ℝ)) (cb := (0 : ℝ))
    (Alo := (25987 / 100000 : ℝ)) (Blo := (1689 / 4000 : ℝ))
    (A1lo := (891 / 2000 : ℝ)) (A1hi := (25491 / 50000 : ℝ))
    (B1lo := (59613 / 100000 : ℝ)) (B1hi := (12997 / 20000 : ℝ))
    (CAhi := (2211 / 50000 : ℝ)) (CBhi := (0 : ℝ))
    (Mlo := (-4087 / 24000 : ℝ)) (Mhi := (-25893 / 400000 : ℝ))
    (by norm_num) hpa hpb hta htb
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
    (by have h := rational_rpow_ge 25987 100000 7 12 5 2 (by decide) (by decide) (by decide) (by decide +kernel); norm_num at h ⊢; try exact h)
    (by have h := rational_rpow_ge 1689 4000 17 24 5 2 (by decide) (by decide) (by decide) (by decide +kernel); norm_num at h ⊢; try exact h)
    (by have h := rational_rpow_ge 891 2000 7 12 3 2 (by decide) (by decide) (by decide) (by decide +kernel); norm_num at h ⊢; try exact h)
    (by have h := rational_rpow_le 25491 50000 7 12 5 4 (by decide) (by decide) (by decide) (by decide +kernel); norm_num at h ⊢; try exact h)
    (by have h := rational_rpow_ge 59613 100000 17 24 3 2 (by decide) (by decide) (by decide) (by decide +kernel); norm_num at h ⊢; try exact h)
    (by have h := rational_rpow_le 12997 20000 17 24 5 4 (by decide) (by decide) (by decide) (by decide +kernel); norm_num at h ⊢; try exact h)
    (by have h := rational_rpow_le 2211 50000 1 4 9 4 (by decide) (by decide) (by decide) (by decide +kernel); norm_num at h ⊢; try exact h)
    (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

private lemma box_leaf_3 {p t : ℝ} (hpa : (9 / 4 : ℝ) ≤ p) (hpb : p ≤ (5 / 2 : ℝ))
    (hta : (1 : ℝ) ≤ t) (htb : t ≤ (11 / 8 : ℝ)) :
    1 + 2 * (|1 - t| / 2) ^ p ≤ ((1 + t) / 3) ^ p + 2 * ((5 - t) / 6) ^ p :=
  tangent_secant_box_right
    (pa := (9 / 4 : ℝ)) (pb := (5 / 2 : ℝ)) (ta := (1 : ℝ)) (tb := (11 / 8 : ℝ))
    (a0 := (35 / 48 : ℝ)) (b0 := (61 / 96 : ℝ)) (ca := (0 : ℝ)) (cb := (3 / 16 : ℝ))
    (Alo := (45399 / 100000 : ℝ)) (Blo := (16091 / 50000 : ℝ))
    (A1lo := (31131 / 50000 : ℝ)) (A1hi := (67383 / 100000 : ℝ))
    (B1lo := (6331 / 12500 : ℝ)) (B1hi := (28367 / 50000 : ℝ))
    (CAhi := (0 : ℝ)) (CBhi := (579 / 25000 : ℝ))
    (Mlo := (2073 / 50000 : ℝ)) (Mhi := (3347 / 24000 : ℝ))
    (by norm_num) hpa hpb hta htb
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
    (by have h := rational_rpow_ge 45399 100000 35 48 5 2 (by decide) (by decide) (by decide) (by decide +kernel); norm_num at h ⊢; try exact h)
    (by have h := rational_rpow_ge 16091 50000 61 96 5 2 (by decide) (by decide) (by decide) (by decide +kernel); norm_num at h ⊢; try exact h)
    (by have h := rational_rpow_ge 31131 50000 35 48 3 2 (by decide) (by decide) (by decide) (by decide +kernel); norm_num at h ⊢; try exact h)
    (by have h := rational_rpow_le 67383 100000 35 48 5 4 (by decide) (by decide) (by decide) (by decide +kernel); norm_num at h ⊢; try exact h)
    (by have h := rational_rpow_ge 6331 12500 61 96 3 2 (by decide) (by decide) (by decide) (by decide +kernel); norm_num at h ⊢; try exact h)
    (by have h := rational_rpow_le 28367 50000 61 96 5 4 (by decide) (by decide) (by decide) (by decide +kernel); norm_num at h ⊢; try exact h)
    (by norm_num)
    (by have h := rational_rpow_le 579 25000 3 16 9 4 (by decide) (by decide) (by decide) (by decide +kernel); norm_num at h ⊢; try exact h)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

private lemma box_leaf_4 {p t : ℝ} (hpa : (9 / 4 : ℝ) ≤ p) (hpb : p ≤ (5 / 2 : ℝ))
    (hta : (11 / 8 : ℝ) ≤ t) (htb : t ≤ (25 / 16 : ℝ)) :
    1 + 2 * (|1 - t| / 2) ^ p ≤ ((1 + t) / 3) ^ p + 2 * ((5 - t) / 6) ^ p :=
  tangent_secant_box_right
    (pa := (9 / 4 : ℝ)) (pb := (5 / 2 : ℝ)) (ta := (11 / 8 : ℝ)) (tb := (25 / 16 : ℝ))
    (a0 := (79 / 96 : ℝ)) (b0 := (113 / 192 : ℝ)) (ca := (3 / 16 : ℝ)) (cb := (9 / 32 : ℝ))
    (Alo := (61429 / 100000 : ℝ)) (Blo := (26571 / 100000 : ℝ))
    (A1lo := (9331 / 12500 : ℝ)) (A1hi := (78381 / 100000 : ℝ))
    (B1lo := (11287 / 25000 : ℝ)) (B1hi := (1611 / 3125 : ℝ))
    (CAhi := (579 / 25000 : ℝ)) (CBhi := (5763 / 100000 : ℝ))
    (Mlo := (8661 / 50000 : ℝ)) (Mhi := (33233 / 120000 : ℝ))
    (by norm_num) hpa hpb hta htb
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
    (by have h := rational_rpow_ge 61429 100000 79 96 5 2 (by decide) (by decide) (by decide) (by decide +kernel); norm_num at h ⊢; try exact h)
    (by have h := rational_rpow_ge 26571 100000 113 192 5 2 (by decide) (by decide) (by decide) (by decide +kernel); norm_num at h ⊢; try exact h)
    (by have h := rational_rpow_ge 9331 12500 79 96 3 2 (by decide) (by decide) (by decide) (by decide +kernel); norm_num at h ⊢; try exact h)
    (by have h := rational_rpow_le 78381 100000 79 96 5 4 (by decide) (by decide) (by decide) (by decide +kernel); norm_num at h ⊢; try exact h)
    (by have h := rational_rpow_ge 11287 25000 113 192 3 2 (by decide) (by decide) (by decide) (by decide +kernel); norm_num at h ⊢; try exact h)
    (by have h := rational_rpow_le 1611 3125 113 192 5 4 (by decide) (by decide) (by decide) (by decide +kernel); norm_num at h ⊢; try exact h)
    (by have h := rational_rpow_le 579 25000 3 16 9 4 (by decide) (by decide) (by decide) (by decide +kernel); norm_num at h ⊢; try exact h)
    (by have h := rational_rpow_le 5763 100000 9 32 9 4 (by decide) (by decide) (by decide) (by decide +kernel); norm_num at h ⊢; try exact h)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

private lemma box_leaf_5 {p t : ℝ} (hpa : (9 / 4 : ℝ) ≤ p) (hpb : p ≤ (5 / 2 : ℝ))
    (hta : (25 / 16 : ℝ) ≤ t) (htb : t ≤ (7 / 4 : ℝ)) :
    1 + 2 * (|1 - t| / 2) ^ p ≤ ((1 + t) / 3) ^ p + 2 * ((5 - t) / 6) ^ p :=
  tangent_secant_box_right
    (pa := (9 / 4 : ℝ)) (pb := (5 / 2 : ℝ)) (ta := (25 / 16 : ℝ)) (tb := (7 / 4 : ℝ))
    (a0 := (85 / 96 : ℝ)) (b0 := (107 / 192 : ℝ)) (ca := (9 / 32 : ℝ)) (cb := (3 / 8 : ℝ))
    (Alo := (36883 / 50000 : ℝ)) (Blo := (11591 / 50000 : ℝ))
    (A1lo := (5207 / 6250 : ℝ)) (A1hi := (85891 / 100000 : ℝ))
    (B1lo := (52 / 125 : ℝ)) (B1hi := (48153 / 100000 : ℝ))
    (CAhi := (5763 / 100000 : ℝ)) (CBhi := (11007 / 100000 : ℝ))
    (Mlo := (105477 / 400000 : ℝ)) (Mhi := (44291 / 120000 : ℝ))
    (by norm_num) hpa hpb hta htb
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
    (by have h := rational_rpow_ge 36883 50000 85 96 5 2 (by decide) (by decide) (by decide) (by decide +kernel); norm_num at h ⊢; try exact h)
    (by have h := rational_rpow_ge 11591 50000 107 192 5 2 (by decide) (by decide) (by decide) (by decide +kernel); norm_num at h ⊢; try exact h)
    (by have h := rational_rpow_ge 5207 6250 85 96 3 2 (by decide) (by decide) (by decide) (by decide +kernel); norm_num at h ⊢; try exact h)
    (by have h := rational_rpow_le 85891 100000 85 96 5 4 (by decide) (by decide) (by decide) (by decide +kernel); norm_num at h ⊢; try exact h)
    (by have h := rational_rpow_ge 52 125 107 192 3 2 (by decide) (by decide) (by decide) (by decide +kernel); norm_num at h ⊢; try exact h)
    (by have h := rational_rpow_le 48153 100000 107 192 5 4 (by decide) (by decide) (by decide) (by decide +kernel); norm_num at h ⊢; try exact h)
    (by have h := rational_rpow_le 5763 100000 9 32 9 4 (by decide) (by decide) (by decide) (by decide +kernel); norm_num at h ⊢; try exact h)
    (by have h := rational_rpow_le 11007 100000 3 8 9 4 (by decide) (by decide) (by decide) (by decide +kernel); norm_num at h ⊢; try exact h)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

private lemma box_leaf_6 {p t : ℝ} (hpa : (5 / 2 : ℝ) ≤ p) (hpb : p ≤ (13 / 5 : ℝ))
    (hta : (1 / 2 : ℝ) ≤ t) (htb : t ≤ (7 / 9 : ℝ)) :
    1 + 2 * (|1 - t| / 2) ^ p ≤ ((1 + t) / 3) ^ p + 2 * ((5 - t) / 6) ^ p :=
  tangent_secant_box_left
    (pa := (5 / 2 : ℝ)) (pb := (13 / 5 : ℝ)) (ta := (1 / 2 : ℝ)) (tb := (7 / 9 : ℝ))
    (a0 := (59 / 108 : ℝ)) (b0 := (157 / 216 : ℝ)) (ca := (1 / 4 : ℝ)) (cb := (1 / 9 : ℝ))
    (Alo := (10381 / 50000 : ℝ)) (Blo := (349 / 800 : ℝ))
    (A1lo := (19003 / 50000 : ℝ)) (A1hi := (2019 / 5000 : ℝ))
    (B1lo := (3001 / 5000 : ℝ)) (B1hi := (61971 / 100000 : ℝ))
    (CAhi := (3127 / 100000 : ℝ)) (CBhi := (207 / 50000 : ℝ))
    (Mlo := (-62309 / 300000 : ℝ)) (Mhi := (-491 / 3000 : ℝ))
    (by norm_num) hpa hpb hta htb
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
    (by have h := rational_rpow_ge 10381 50000 59 108 13 5 (by decide) (by decide) (by decide) (by decide +kernel); norm_num at h ⊢; try exact h)
    (by have h := rational_rpow_ge 349 800 157 216 13 5 (by decide) (by decide) (by decide) (by decide +kernel); norm_num at h ⊢; try exact h)
    (by have h := rational_rpow_ge 19003 50000 59 108 8 5 (by decide) (by decide) (by decide) (by decide +kernel); norm_num at h ⊢; try exact h)
    (by have h := rational_rpow_le 2019 5000 59 108 3 2 (by decide) (by decide) (by decide) (by decide +kernel); norm_num at h ⊢; try exact h)
    (by have h := rational_rpow_ge 3001 5000 157 216 8 5 (by decide) (by decide) (by decide) (by decide +kernel); norm_num at h ⊢; try exact h)
    (by have h := rational_rpow_le 61971 100000 157 216 3 2 (by decide) (by decide) (by decide) (by decide +kernel); norm_num at h ⊢; try exact h)
    (by have h := rational_rpow_le 3127 100000 1 4 5 2 (by decide) (by decide) (by decide) (by decide +kernel); norm_num at h ⊢; try exact h)
    (by have h := rational_rpow_le 207 50000 1 9 5 2 (by decide) (by decide) (by decide) (by decide +kernel); norm_num at h ⊢; try exact h)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

private lemma box_leaf_7 {p t : ℝ} (hpa : (5 / 2 : ℝ) ≤ p) (hpb : p ≤ (13 / 5 : ℝ))
    (hta : (11 / 9 : ℝ) ≤ t) (htb : t ≤ (281 / 180 : ℝ)) :
    1 + 2 * (|1 - t| / 2) ^ p ≤ ((1 + t) / 3) ^ p + 2 * ((5 - t) / 6) ^ p :=
  tangent_secant_box_right
    (pa := (5 / 2 : ℝ)) (pb := (13 / 5 : ℝ)) (ta := (11 / 9 : ℝ)) (tb := (281 / 180 : ℝ))
    (a0 := (287 / 360 : ℝ)) (b0 := (433 / 720 : ℝ)) (ca := (1 / 9 : ℝ)) (cb := (101 / 360 : ℝ))
    (Alo := (27737 / 50000 : ℝ)) (Blo := (13327 / 50000 : ℝ))
    (A1lo := (4349 / 6250 : ℝ)) (A1hi := (4449 / 6250 : ℝ))
    (B1lo := (22161 / 50000 : ℝ)) (B1hi := (583 / 1250 : ℝ))
    (CAhi := (207 / 50000 : ℝ)) (CBhi := (1043 / 25000 : ℝ))
    (Mlo := (239 / 1250 : ℝ)) (Mhi := (58201 / 250000 : ℝ))
    (by norm_num) hpa hpb hta htb
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
    (by have h := rational_rpow_ge 27737 50000 287 360 13 5 (by decide) (by decide) (by decide) (by decide +kernel); norm_num at h ⊢; try exact h)
    (by have h := rational_rpow_ge 13327 50000 433 720 13 5 (by decide) (by decide) (by decide) (by decide +kernel); norm_num at h ⊢; try exact h)
    (by have h := rational_rpow_ge 4349 6250 287 360 8 5 (by decide) (by decide) (by decide) (by decide +kernel); norm_num at h ⊢; try exact h)
    (by have h := rational_rpow_le 4449 6250 287 360 3 2 (by decide) (by decide) (by decide) (by decide +kernel); norm_num at h ⊢; try exact h)
    (by have h := rational_rpow_ge 22161 50000 433 720 8 5 (by decide) (by decide) (by decide) (by decide +kernel); norm_num at h ⊢; try exact h)
    (by have h := rational_rpow_le 583 1250 433 720 3 2 (by decide) (by decide) (by decide) (by decide +kernel); norm_num at h ⊢; try exact h)
    (by have h := rational_rpow_le 207 50000 1 9 5 2 (by decide) (by decide) (by decide) (by decide +kernel); norm_num at h ⊢; try exact h)
    (by have h := rational_rpow_le 1043 25000 101 360 5 2 (by decide) (by decide) (by decide) (by decide +kernel); norm_num at h ⊢; try exact h)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

private lemma box_leaf_8 {p t : ℝ} (hpa : (5 / 2 : ℝ) ≤ p) (hpb : p ≤ (13 / 5 : ℝ))
    (hta : (281 / 180 : ℝ) ≤ t) (htb : t ≤ (623 / 360 : ℝ)) :
    1 + 2 * (|1 - t| / 2) ^ p ≤ ((1 + t) / 3) ^ p + 2 * ((5 - t) / 6) ^ p :=
  tangent_secant_box_right
    (pa := (5 / 2 : ℝ)) (pb := (13 / 5 : ℝ)) (ta := (281 / 180 : ℝ)) (tb := (623 / 360 : ℝ))
    (a0 := (127 / 144 : ℝ)) (b0 := (161 / 288 : ℝ)) (ca := (101 / 360 : ℝ)) (cb := (263 / 720 : ℝ))
    (Alo := (72133 / 100000 : ℝ)) (Blo := (22043 / 100000 : ℝ))
    (A1lo := (81789 / 100000 : ℝ)) (A1hi := (20707 / 25000 : ℝ))
    (B1lo := (19717 / 50000 : ℝ)) (B1hi := (209 / 500 : ℝ))
    (CAhi := (1043 / 25000 : ℝ)) (CBhi := (8067 / 100000 : ℝ))
    (Mlo := (39989 / 120000 : ℝ)) (Mhi := (282061 / 750000 : ℝ))
    (by norm_num) hpa hpb hta htb
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
    (by have h := rational_rpow_ge 72133 100000 127 144 13 5 (by decide) (by decide) (by decide) (by decide +kernel); norm_num at h ⊢; try exact h)
    (by have h := rational_rpow_ge 22043 100000 161 288 13 5 (by decide) (by decide) (by decide) (by decide +kernel); norm_num at h ⊢; try exact h)
    (by have h := rational_rpow_ge 81789 100000 127 144 8 5 (by decide) (by decide) (by decide) (by decide +kernel); norm_num at h ⊢; try exact h)
    (by have h := rational_rpow_le 20707 25000 127 144 3 2 (by decide) (by decide) (by decide) (by decide +kernel); norm_num at h ⊢; try exact h)
    (by have h := rational_rpow_ge 19717 50000 161 288 8 5 (by decide) (by decide) (by decide) (by decide +kernel); norm_num at h ⊢; try exact h)
    (by have h := rational_rpow_le 209 500 161 288 3 2 (by decide) (by decide) (by decide) (by decide +kernel); norm_num at h ⊢; try exact h)
    (by have h := rational_rpow_le 1043 25000 101 360 5 2 (by decide) (by decide) (by decide) (by decide +kernel); norm_num at h ⊢; try exact h)
    (by have h := rational_rpow_le 8067 100000 263 720 5 2 (by decide) (by decide) (by decide) (by decide +kernel); norm_num at h ⊢; try exact h)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

private lemma box_leaf_9 {p t : ℝ} (hpa : (5 / 2 : ℝ) ≤ p) (hpb : p ≤ (13 / 5 : ℝ))
    (hta : (623 / 360 : ℝ) ≤ t) (htb : t ≤ (1307 / 720 : ℝ)) :
    1 + 2 * (|1 - t| / 2) ^ p ≤ ((1 + t) / 3) ^ p + 2 * ((5 - t) / 6) ^ p :=
  tangent_secant_box_right
    (pa := (5 / 2 : ℝ)) (pb := (13 / 5 : ℝ)) (ta := (623 / 360 : ℝ)) (tb := (1307 / 720 : ℝ))
    (a0 := (1331 / 1440 : ℝ)) (b0 := (1549 / 2880 : ℝ)) (ca := (263 / 720 : ℝ)) (cb := (587 / 1440 : ℝ))
    (Alo := (81491 / 100000 : ℝ)) (Blo := (19937 / 100000 : ℝ))
    (A1lo := (22041 / 25000 : ℝ)) (A1hi := (44433 / 50000 : ℝ))
    (B1lo := (3707 / 10000 : ℝ)) (B1hi := (39447 / 100000 : ℝ))
    (CAhi := (8067 / 100000 : ℝ)) (CBhi := (2653 / 25000 : ℝ))
    (Mlo := (16239 / 40000 : ℝ)) (Mhi := (168337 / 375000 : ℝ))
    (by norm_num) hpa hpb hta htb
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
    (by have h := rational_rpow_ge 81491 100000 1331 1440 13 5 (by decide) (by decide) (by decide) (by decide +kernel); norm_num at h ⊢; try exact h)
    (by have h := rational_rpow_ge 19937 100000 1549 2880 13 5 (by decide) (by decide) (by decide) (by decide +kernel); norm_num at h ⊢; try exact h)
    (by have h := rational_rpow_ge 22041 25000 1331 1440 8 5 (by decide) (by decide) (by decide) (by decide +kernel); norm_num at h ⊢; try exact h)
    (by have h := rational_rpow_le 44433 50000 1331 1440 3 2 (by decide) (by decide) (by decide) (by decide +kernel); norm_num at h ⊢; try exact h)
    (by have h := rational_rpow_ge 3707 10000 1549 2880 8 5 (by decide) (by decide) (by decide) (by decide +kernel); norm_num at h ⊢; try exact h)
    (by have h := rational_rpow_le 39447 100000 1549 2880 3 2 (by decide) (by decide) (by decide) (by decide +kernel); norm_num at h ⊢; try exact h)
    (by have h := rational_rpow_le 8067 100000 263 720 5 2 (by decide) (by decide) (by decide) (by decide +kernel); norm_num at h ⊢; try exact h)
    (by have h := rational_rpow_le 2653 25000 587 1440 5 2 (by decide) (by decide) (by decide) (by decide +kernel); norm_num at h ⊢; try exact h)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

private lemma box_leaf_10 {p t : ℝ} (hpa : (5 / 2 : ℝ) ≤ p) (hpb : p ≤ (13 / 5 : ℝ))
    (hta : (1307 / 720 : ℝ) ≤ t) (htb : t ≤ (19 / 10 : ℝ)) :
    1 + 2 * (|1 - t| / 2) ^ p ≤ ((1 + t) / 3) ^ p + 2 * ((5 - t) / 6) ^ p :=
  tangent_secant_box_right
    (pa := (5 / 2 : ℝ)) (pb := (13 / 5 : ℝ)) (ta := (1307 / 720 : ℝ)) (tb := (19 / 10 : ℝ))
    (a0 := (823 / 864 : ℝ)) (b0 := (905 / 1728 : ℝ)) (ca := (587 / 1440 : ℝ)) (cb := (9 / 20 : ℝ))
    (Alo := (88123 / 100000 : ℝ)) (Blo := (4651 / 25000 : ℝ))
    (A1lo := (46257 / 50000 : ℝ)) (A1hi := (9297 / 10000 : ℝ))
    (B1lo := (1421 / 4000 : ℝ)) (B1hi := (2369 / 6250 : ℝ))
    (CAhi := (2653 / 25000 : ℝ)) (CBhi := (13587 / 100000 : ℝ))
    (Mlo := (5461 / 12000 : ℝ)) (Mhi := (149357 / 300000 : ℝ))
    (by norm_num) hpa hpb hta htb
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
    (by have h := rational_rpow_ge 88123 100000 823 864 13 5 (by decide) (by decide) (by decide) (by decide +kernel); norm_num at h ⊢; try exact h)
    (by have h := rational_rpow_ge 4651 25000 905 1728 13 5 (by decide) (by decide) (by decide) (by decide +kernel); norm_num at h ⊢; try exact h)
    (by have h := rational_rpow_ge 46257 50000 823 864 8 5 (by decide) (by decide) (by decide) (by decide +kernel); norm_num at h ⊢; try exact h)
    (by have h := rational_rpow_le 9297 10000 823 864 3 2 (by decide) (by decide) (by decide) (by decide +kernel); norm_num at h ⊢; try exact h)
    (by have h := rational_rpow_ge 1421 4000 905 1728 8 5 (by decide) (by decide) (by decide) (by decide +kernel); norm_num at h ⊢; try exact h)
    (by have h := rational_rpow_le 2369 6250 905 1728 3 2 (by decide) (by decide) (by decide) (by decide +kernel); norm_num at h ⊢; try exact h)
    (by have h := rational_rpow_le 2653 25000 587 1440 5 2 (by decide) (by decide) (by decide) (by decide +kernel); norm_num at h ⊢; try exact h)
    (by have h := rational_rpow_le 13587 100000 9 20 5 2 (by decide) (by decide) (by decide) (by decide +kernel); norm_num at h ⊢; try exact h)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

private lemma box_leaf_11 {p t : ℝ} (hpa : (13 / 5 : ℝ) ≤ p) (hpb : p ≤ (67 / 25 : ℝ))
    (hta : (1 / 2 : ℝ) ≤ t) (htb : t ≤ (7 / 9 : ℝ)) :
    1 + 2 * (|1 - t| / 2) ^ p ≤ ((1 + t) / 3) ^ p + 2 * ((5 - t) / 6) ^ p :=
  tangent_secant_box_left
    (pa := (13 / 5 : ℝ)) (pb := (67 / 25 : ℝ)) (ta := (1 / 2 : ℝ)) (tb := (7 / 9 : ℝ))
    (a0 := (59 / 108 : ℝ)) (b0 := (157 / 216 : ℝ)) (ca := (1 / 4 : ℝ)) (cb := (1 / 9 : ℝ))
    (Alo := (19781 / 100000 : ℝ)) (Blo := (21263 / 50000 : ℝ))
    (A1lo := (9053 / 25000 : ℝ)) (A1hi := (38011 / 100000 : ℝ))
    (B1lo := (58507 / 100000 : ℝ)) (B1hi := (2401 / 4000 : ℝ))
    (CAhi := (2723 / 100000 : ℝ)) (CBhi := (333 / 100000 : ℝ))
    (Mlo := (-1595471 / 7500000 : ℝ)) (Mhi := (-5551 / 31250 : ℝ))
    (by norm_num) hpa hpb hta htb
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
    (by have h := rational_rpow_ge 19781 100000 59 108 67 25 (by decide) (by decide) (by decide) (by decide +kernel); norm_num at h ⊢; try exact h)
    (by have h := rational_rpow_ge 21263 50000 157 216 67 25 (by decide) (by decide) (by decide) (by decide +kernel); norm_num at h ⊢; try exact h)
    (by have h := rational_rpow_ge 9053 25000 59 108 42 25 (by decide) (by decide) (by decide) (by decide +kernel); norm_num at h ⊢; try exact h)
    (by have h := rational_rpow_le 38011 100000 59 108 8 5 (by decide) (by decide) (by decide) (by decide +kernel); norm_num at h ⊢; try exact h)
    (by have h := rational_rpow_ge 58507 100000 157 216 42 25 (by decide) (by decide) (by decide) (by decide +kernel); norm_num at h ⊢; try exact h)
    (by have h := rational_rpow_le 2401 4000 157 216 8 5 (by decide) (by decide) (by decide) (by decide +kernel); norm_num at h ⊢; try exact h)
    (by have h := rational_rpow_le 2723 100000 1 4 13 5 (by decide) (by decide) (by decide) (by decide +kernel); norm_num at h ⊢; try exact h)
    (by have h := rational_rpow_le 333 100000 1 9 13 5 (by decide) (by decide) (by decide) (by decide +kernel); norm_num at h ⊢; try exact h)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

private lemma box_leaf_12 {p t : ℝ} (hpa : (13 / 5 : ℝ) ≤ p) (hpb : p ≤ (67 / 25 : ℝ))
    (hta : (11 / 9 : ℝ) ≤ t) (htb : t ≤ (281 / 180 : ℝ)) :
    1 + 2 * (|1 - t| / 2) ^ p ≤ ((1 + t) / 3) ^ p + 2 * ((5 - t) / 6) ^ p :=
  tangent_secant_box_right
    (pa := (13 / 5 : ℝ)) (pb := (67 / 25 : ℝ)) (ta := (11 / 9 : ℝ)) (tb := (281 / 180 : ℝ))
    (a0 := (287 / 360 : ℝ)) (b0 := (433 / 720 : ℝ)) (ca := (1 / 9 : ℝ)) (cb := (101 / 360 : ℝ))
    (Alo := (54477 / 100000 : ℝ)) (Blo := (25591 / 100000 : ℝ))
    (A1lo := (34167 / 50000 : ℝ)) (A1hi := (69589 / 100000 : ℝ))
    (B1lo := (8511 / 20000 : ℝ)) (B1hi := (44327 / 100000 : ℝ))
    (CAhi := (333 / 100000 : ℝ)) (CBhi := (1837 / 50000 : ℝ))
    (Mlo := (312091 / 1500000 : ℝ)) (Mhi := (905639 / 3750000 : ℝ))
    (by norm_num) hpa hpb hta htb
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
    (by have h := rational_rpow_ge 54477 100000 287 360 67 25 (by decide) (by decide) (by decide) (by decide +kernel); norm_num at h ⊢; try exact h)
    (by have h := rational_rpow_ge 25591 100000 433 720 67 25 (by decide) (by decide) (by decide) (by decide +kernel); norm_num at h ⊢; try exact h)
    (by have h := rational_rpow_ge 34167 50000 287 360 42 25 (by decide) (by decide) (by decide) (by decide +kernel); norm_num at h ⊢; try exact h)
    (by have h := rational_rpow_le 69589 100000 287 360 8 5 (by decide) (by decide) (by decide) (by decide +kernel); norm_num at h ⊢; try exact h)
    (by have h := rational_rpow_ge 8511 20000 433 720 42 25 (by decide) (by decide) (by decide) (by decide +kernel); norm_num at h ⊢; try exact h)
    (by have h := rational_rpow_le 44327 100000 433 720 8 5 (by decide) (by decide) (by decide) (by decide +kernel); norm_num at h ⊢; try exact h)
    (by have h := rational_rpow_le 333 100000 1 9 13 5 (by decide) (by decide) (by decide) (by decide +kernel); norm_num at h ⊢; try exact h)
    (by have h := rational_rpow_le 1837 50000 101 360 13 5 (by decide) (by decide) (by decide) (by decide +kernel); norm_num at h ⊢; try exact h)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

private lemma box_leaf_13 {p t : ℝ} (hpa : (13 / 5 : ℝ) ≤ p) (hpb : p ≤ (67 / 25 : ℝ))
    (hta : (281 / 180 : ℝ) ≤ t) (htb : t ≤ (623 / 360 : ℝ)) :
    1 + 2 * (|1 - t| / 2) ^ p ≤ ((1 + t) / 3) ^ p + 2 * ((5 - t) / 6) ^ p :=
  tangent_secant_box_right
    (pa := (13 / 5 : ℝ)) (pb := (67 / 25 : ℝ)) (ta := (281 / 180 : ℝ)) (tb := (623 / 360 : ℝ))
    (a0 := (127 / 144 : ℝ)) (b0 := (161 / 288 : ℝ)) (ca := (101 / 360 : ℝ)) (cb := (263 / 720 : ℝ))
    (Alo := (71411 / 100000 : ℝ)) (Blo := (21041 / 100000 : ℝ))
    (A1lo := (80971 / 100000 : ℝ)) (A1hi := (40897 / 50000 : ℝ))
    (B1lo := (37641 / 100000 : ℝ)) (B1hi := (39439 / 100000 : ℝ))
    (CAhi := (1837 / 50000 : ℝ)) (CBhi := (3647 / 50000 : ℝ))
    (Mlo := (44993 / 125000 : ℝ)) (Mhi := (2958251 / 7500000 : ℝ))
    (by norm_num) hpa hpb hta htb
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
    (by have h := rational_rpow_ge 71411 100000 127 144 67 25 (by decide) (by decide) (by decide) (by decide +kernel); norm_num at h ⊢; try exact h)
    (by have h := rational_rpow_ge 21041 100000 161 288 67 25 (by decide) (by decide) (by decide) (by decide +kernel); norm_num at h ⊢; try exact h)
    (by have h := rational_rpow_ge 80971 100000 127 144 42 25 (by decide) (by decide) (by decide) (by decide +kernel); norm_num at h ⊢; try exact h)
    (by have h := rational_rpow_le 40897 50000 127 144 8 5 (by decide) (by decide) (by decide) (by decide +kernel); norm_num at h ⊢; try exact h)
    (by have h := rational_rpow_ge 37641 100000 161 288 42 25 (by decide) (by decide) (by decide) (by decide +kernel); norm_num at h ⊢; try exact h)
    (by have h := rational_rpow_le 39439 100000 161 288 8 5 (by decide) (by decide) (by decide) (by decide +kernel); norm_num at h ⊢; try exact h)
    (by have h := rational_rpow_le 1837 50000 101 360 13 5 (by decide) (by decide) (by decide) (by decide +kernel); norm_num at h ⊢; try exact h)
    (by have h := rational_rpow_le 3647 50000 263 720 13 5 (by decide) (by decide) (by decide) (by decide +kernel); norm_num at h ⊢; try exact h)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

private lemma box_leaf_14 {p t : ℝ} (hpa : (13 / 5 : ℝ) ≤ p) (hpb : p ≤ (67 / 25 : ℝ))
    (hta : (623 / 360 : ℝ) ≤ t) (htb : t ≤ (1307 / 720 : ℝ)) :
    1 + 2 * (|1 - t| / 2) ^ p ≤ ((1 + t) / 3) ^ p + 2 * ((5 - t) / 6) ^ p :=
  tangent_secant_box_right
    (pa := (13 / 5 : ℝ)) (pb := (67 / 25 : ℝ)) (ta := (623 / 360 : ℝ)) (tb := (1307 / 720 : ℝ))
    (a0 := (1331 / 1440 : ℝ)) (b0 := (1549 / 2880 : ℝ)) (ca := (263 / 720 : ℝ)) (cb := (587 / 1440 : ℝ))
    (Alo := (80979 / 100000 : ℝ)) (Blo := (4743 / 25000 : ℝ))
    (A1lo := (87611 / 100000 : ℝ)) (A1hi := (88169 / 100000 : ℝ))
    (B1lo := (8819 / 25000 : ℝ)) (B1hi := (1483 / 4000 : ℝ))
    (CAhi := (3647 / 50000 : ℝ)) (CBhi := (9701 / 100000 : ℝ))
    (Mlo := (82121 / 187500 : ℝ)) (Mhi := (1181277 / 2500000 : ℝ))
    (by norm_num) hpa hpb hta htb
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
    (by have h := rational_rpow_ge 80979 100000 1331 1440 67 25 (by decide) (by decide) (by decide) (by decide +kernel); norm_num at h ⊢; try exact h)
    (by have h := rational_rpow_ge 4743 25000 1549 2880 67 25 (by decide) (by decide) (by decide) (by decide +kernel); norm_num at h ⊢; try exact h)
    (by have h := rational_rpow_ge 87611 100000 1331 1440 42 25 (by decide) (by decide) (by decide) (by decide +kernel); norm_num at h ⊢; try exact h)
    (by have h := rational_rpow_le 88169 100000 1331 1440 8 5 (by decide) (by decide) (by decide) (by decide +kernel); norm_num at h ⊢; try exact h)
    (by have h := rational_rpow_ge 8819 25000 1549 2880 42 25 (by decide) (by decide) (by decide) (by decide +kernel); norm_num at h ⊢; try exact h)
    (by have h := rational_rpow_le 1483 4000 1549 2880 8 5 (by decide) (by decide) (by decide) (by decide +kernel); norm_num at h ⊢; try exact h)
    (by have h := rational_rpow_le 3647 50000 263 720 13 5 (by decide) (by decide) (by decide) (by decide +kernel); norm_num at h ⊢; try exact h)
    (by have h := rational_rpow_le 9701 100000 587 1440 13 5 (by decide) (by decide) (by decide) (by decide +kernel); norm_num at h ⊢; try exact h)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

private lemma box_leaf_15 {p t : ℝ} (hpa : (13 / 5 : ℝ) ≤ p) (hpb : p ≤ (67 / 25 : ℝ))
    (hta : (1307 / 720 : ℝ) ≤ t) (htb : t ≤ (19 / 10 : ℝ)) :
    1 + 2 * (|1 - t| / 2) ^ p ≤ ((1 + t) / 3) ^ p + 2 * ((5 - t) / 6) ^ p :=
  tangent_secant_box_right
    (pa := (13 / 5 : ℝ)) (pb := (67 / 25 : ℝ)) (ta := (1307 / 720 : ℝ)) (tb := (19 / 10 : ℝ))
    (a0 := (823 / 864 : ℝ)) (b0 := (905 / 1728 : ℝ)) (ca := (587 / 1440 : ℝ)) (cb := (9 / 20 : ℝ))
    (Alo := (87781 / 100000 : ℝ)) (Blo := (8833 / 50000 : ℝ))
    (A1lo := (18431 / 20000 : ℝ)) (A1hi := (92519 / 100000 : ℝ))
    (B1lo := (16867 / 50000 : ℝ)) (B1hi := (3553 / 10000 : ℝ))
    (CAhi := (9701 / 100000 : ℝ)) (CBhi := (392 / 3125 : ℝ))
    (Mlo := (1963 / 4000 : ℝ)) (Mhi := (262573 / 500000 : ℝ))
    (by norm_num) hpa hpb hta htb
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
    (by have h := rational_rpow_ge 87781 100000 823 864 67 25 (by decide) (by decide) (by decide) (by decide +kernel); norm_num at h ⊢; try exact h)
    (by have h := rational_rpow_ge 8833 50000 905 1728 67 25 (by decide) (by decide) (by decide) (by decide +kernel); norm_num at h ⊢; try exact h)
    (by have h := rational_rpow_ge 18431 20000 823 864 42 25 (by decide) (by decide) (by decide) (by decide +kernel); norm_num at h ⊢; try exact h)
    (by have h := rational_rpow_le 92519 100000 823 864 8 5 (by decide) (by decide) (by decide) (by decide +kernel); norm_num at h ⊢; try exact h)
    (by have h := rational_rpow_ge 16867 50000 905 1728 42 25 (by decide) (by decide) (by decide) (by decide +kernel); norm_num at h ⊢; try exact h)
    (by have h := rational_rpow_le 3553 10000 905 1728 8 5 (by decide) (by decide) (by decide) (by decide +kernel); norm_num at h ⊢; try exact h)
    (by have h := rational_rpow_le 9701 100000 587 1440 13 5 (by decide) (by decide) (by decide) (by decide +kernel); norm_num at h ⊢; try exact h)
    (by have h := rational_rpow_le 392 3125 9 20 13 5 (by decide) (by decide) (by decide) (by decide +kernel); norm_num at h ⊢; try exact h)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

private lemma box_leaf_16 {p t : ℝ} (hpa : (67 / 25 : ℝ) ≤ p) (hpb : p ≤ (68 / 25 : ℝ))
    (hta : (1 / 2 : ℝ) ≤ t) (htb : t ≤ (23 / 36 : ℝ)) :
    1 + 2 * (|1 - t| / 2) ^ p ≤ ((1 + t) / 3) ^ p + 2 * ((5 - t) / 6) ^ p :=
  tangent_secant_box_left
    (pa := (67 / 25 : ℝ)) (pb := (68 / 25 : ℝ)) (ta := (1 / 2 : ℝ)) (tb := (23 / 36 : ℝ))
    (a0 := (113 / 216 : ℝ)) (b0 := (319 / 432 : ℝ)) (ca := (1 / 4 : ℝ)) (cb := (13 / 72 : ℝ))
    (Alo := (17163 / 100000 : ℝ)) (Blo := (4383 / 10000 : ℝ))
    (A1lo := (3281 / 10000 : ℝ)) (A1hi := (8419 / 25000 : ℝ))
    (B1lo := (59357 / 100000 : ℝ)) (B1hi := (30043 / 50000 : ℝ))
    (CAhi := (2437 / 100000 : ℝ)) (CBhi := (51 / 5000 : ℝ))
    (Mlo := (-38641 / 156250 : ℝ)) (Mhi := (-1720627 / 7500000 : ℝ))
    (by norm_num) hpa hpb hta htb
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
    (by have h := rational_rpow_ge 17163 100000 113 216 68 25 (by decide) (by decide) (by decide) (by decide +kernel); norm_num at h ⊢; try exact h)
    (by have h := rational_rpow_ge 4383 10000 319 432 68 25 (by decide) (by decide) (by decide) (by decide +kernel); norm_num at h ⊢; try exact h)
    (by have h := rational_rpow_ge 3281 10000 113 216 43 25 (by decide) (by decide) (by decide) (by decide +kernel); norm_num at h ⊢; try exact h)
    (by have h := rational_rpow_le 8419 25000 113 216 42 25 (by decide) (by decide) (by decide) (by decide +kernel); norm_num at h ⊢; try exact h)
    (by have h := rational_rpow_ge 59357 100000 319 432 43 25 (by decide) (by decide) (by decide) (by decide +kernel); norm_num at h ⊢; try exact h)
    (by have h := rational_rpow_le 30043 50000 319 432 42 25 (by decide) (by decide) (by decide) (by decide +kernel); norm_num at h ⊢; try exact h)
    (by have h := rational_rpow_le 2437 100000 1 4 67 25 (by decide) (by decide) (by decide) (by decide +kernel); norm_num at h ⊢; try exact h)
    (by have h := rational_rpow_le 51 5000 13 72 67 25 (by decide) (by decide) (by decide) (by decide +kernel); norm_num at h ⊢; try exact h)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

private lemma box_leaf_17 {p t : ℝ} (hpa : (67 / 25 : ℝ) ≤ p) (hpb : p ≤ (68 / 25 : ℝ))
    (hta : (23 / 36 : ℝ) ≤ t) (htb : t ≤ (7 / 9 : ℝ)) :
    1 + 2 * (|1 - t| / 2) ^ p ≤ ((1 + t) / 3) ^ p + 2 * ((5 - t) / 6) ^ p :=
  tangent_secant_box_left
    (pa := (67 / 25 : ℝ)) (pb := (68 / 25 : ℝ)) (ta := (23 / 36 : ℝ)) (tb := (7 / 9 : ℝ))
    (a0 := (41 / 72 : ℝ)) (b0 := (103 / 144 : ℝ)) (ca := (13 / 72 : ℝ)) (cb := (1 / 9 : ℝ))
    (Alo := (1351 / 6250 : ℝ)) (Blo := (1256 / 3125 : ℝ))
    (A1lo := (18981 / 50000 : ℝ)) (A1hi := (2427 / 6250 : ℝ))
    (B1lo := (1756 / 3125 : ℝ)) (B1hi := (14239 / 25000 : ℝ))
    (CAhi := (51 / 5000 : ℝ)) (CBhi := (7 / 2500 : ℝ))
    (Mlo := (-161449 / 937500 : ℝ)) (Mhi := (-14539 / 93750 : ℝ))
    (by norm_num) hpa hpb hta htb
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
    (by have h := rational_rpow_ge 1351 6250 41 72 68 25 (by decide) (by decide) (by decide) (by decide +kernel); norm_num at h ⊢; try exact h)
    (by have h := rational_rpow_ge 1256 3125 103 144 68 25 (by decide) (by decide) (by decide) (by decide +kernel); norm_num at h ⊢; try exact h)
    (by have h := rational_rpow_ge 18981 50000 41 72 43 25 (by decide) (by decide) (by decide) (by decide +kernel); norm_num at h ⊢; try exact h)
    (by have h := rational_rpow_le 2427 6250 41 72 42 25 (by decide) (by decide) (by decide) (by decide +kernel); norm_num at h ⊢; try exact h)
    (by have h := rational_rpow_ge 1756 3125 103 144 43 25 (by decide) (by decide) (by decide) (by decide +kernel); norm_num at h ⊢; try exact h)
    (by have h := rational_rpow_le 14239 25000 103 144 42 25 (by decide) (by decide) (by decide) (by decide +kernel); norm_num at h ⊢; try exact h)
    (by have h := rational_rpow_le 51 5000 13 72 67 25 (by decide) (by decide) (by decide) (by decide +kernel); norm_num at h ⊢; try exact h)
    (by have h := rational_rpow_le 7 2500 1 9 67 25 (by decide) (by decide) (by decide) (by decide +kernel); norm_num at h ⊢; try exact h)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

private lemma box_leaf_18 {p t : ℝ} (hpa : (67 / 25 : ℝ) ≤ p) (hpb : p ≤ (68 / 25 : ℝ))
    (hta : (11 / 9 : ℝ) ≤ t) (htb : t ≤ (167 / 120 : ℝ)) :
    1 + 2 * (|1 - t| / 2) ^ p ≤ ((1 + t) / 3) ^ p + 2 * ((5 - t) / 6) ^ p :=
  tangent_secant_box_right
    (pa := (67 / 25 : ℝ)) (pb := (68 / 25 : ℝ)) (ta := (11 / 9 : ℝ)) (tb := (167 / 120 : ℝ))
    (a0 := (1661 / 2160 : ℝ)) (b0 := (2659 / 4320 : ℝ)) (ca := (1 / 9 : ℝ)) (cb := (47 / 240 : ℝ))
    (Alo := (48941 / 100000 : ℝ)) (Blo := (2671 / 10000 : ℝ))
    (A1lo := (15911 / 25000 : ℝ)) (A1hi := (64321 / 100000 : ℝ))
    (B1lo := (43397 / 100000 : ℝ)) (B1hi := (44253 / 100000 : ℝ))
    (CAhi := (7 / 2500 : ℝ)) (CBhi := (317 / 25000 : ℝ))
    (Mlo := (1299197 / 7500000 : ℝ)) (Mhi := (88927 / 468750 : ℝ))
    (by norm_num) hpa hpb hta htb
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
    (by have h := rational_rpow_ge 48941 100000 1661 2160 68 25 (by decide) (by decide) (by decide) (by decide +kernel); norm_num at h ⊢; try exact h)
    (by have h := rational_rpow_ge 2671 10000 2659 4320 68 25 (by decide) (by decide) (by decide) (by decide +kernel); norm_num at h ⊢; try exact h)
    (by have h := rational_rpow_ge 15911 25000 1661 2160 43 25 (by decide) (by decide) (by decide) (by decide +kernel); norm_num at h ⊢; try exact h)
    (by have h := rational_rpow_le 64321 100000 1661 2160 42 25 (by decide) (by decide) (by decide) (by decide +kernel); norm_num at h ⊢; try exact h)
    (by have h := rational_rpow_ge 43397 100000 2659 4320 43 25 (by decide) (by decide) (by decide) (by decide +kernel); norm_num at h ⊢; try exact h)
    (by have h := rational_rpow_le 44253 100000 2659 4320 42 25 (by decide) (by decide) (by decide) (by decide +kernel); norm_num at h ⊢; try exact h)
    (by have h := rational_rpow_le 7 2500 1 9 67 25 (by decide) (by decide) (by decide) (by decide +kernel); norm_num at h ⊢; try exact h)
    (by have h := rational_rpow_le 317 25000 47 240 67 25 (by decide) (by decide) (by decide) (by decide +kernel); norm_num at h ⊢; try exact h)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

private lemma box_leaf_19 {p t : ℝ} (hpa : (67 / 25 : ℝ) ≤ p) (hpb : p ≤ (68 / 25 : ℝ))
    (hta : (167 / 120 : ℝ) ≤ t) (htb : t ≤ (281 / 180 : ℝ)) :
    1 + 2 * (|1 - t| / 2) ^ p ≤ ((1 + t) / 3) ^ p + 2 * ((5 - t) / 6) ^ p :=
  tangent_secant_box_right
    (pa := (67 / 25 : ℝ)) (pb := (68 / 25 : ℝ)) (ta := (167 / 120 : ℝ)) (tb := (281 / 180 : ℝ))
    (a0 := (1783 / 2160 : ℝ)) (b0 := (2537 / 4320 : ℝ)) (ca := (47 / 240 : ℝ)) (cb := (101 / 360 : ℝ))
    (Alo := (59347 / 100000 : ℝ)) (Blo := (23507 / 100000 : ℝ))
    (A1lo := (8987 / 12500 : ℝ)) (A1hi := (14491 / 20000 : ℝ))
    (B1lo := (40029 / 100000 : ℝ)) (B1hi := (8179 / 20000 : ℝ))
    (CAhi := (317 / 25000 : ℝ)) (CBhi := (3319 / 100000 : ℝ))
    (Mlo := (2077067 / 7500000 : ℝ)) (Mhi := (275621 / 937500 : ℝ))
    (by norm_num) hpa hpb hta htb
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
    (by have h := rational_rpow_ge 59347 100000 1783 2160 68 25 (by decide) (by decide) (by decide) (by decide +kernel); norm_num at h ⊢; try exact h)
    (by have h := rational_rpow_ge 23507 100000 2537 4320 68 25 (by decide) (by decide) (by decide) (by decide +kernel); norm_num at h ⊢; try exact h)
    (by have h := rational_rpow_ge 8987 12500 1783 2160 43 25 (by decide) (by decide) (by decide) (by decide +kernel); norm_num at h ⊢; try exact h)
    (by have h := rational_rpow_le 14491 20000 1783 2160 42 25 (by decide) (by decide) (by decide) (by decide +kernel); norm_num at h ⊢; try exact h)
    (by have h := rational_rpow_ge 40029 100000 2537 4320 43 25 (by decide) (by decide) (by decide) (by decide +kernel); norm_num at h ⊢; try exact h)
    (by have h := rational_rpow_le 8179 20000 2537 4320 42 25 (by decide) (by decide) (by decide) (by decide +kernel); norm_num at h ⊢; try exact h)
    (by have h := rational_rpow_le 317 25000 47 240 67 25 (by decide) (by decide) (by decide) (by decide +kernel); norm_num at h ⊢; try exact h)
    (by have h := rational_rpow_le 3319 100000 101 360 67 25 (by decide) (by decide) (by decide) (by decide +kernel); norm_num at h ⊢; try exact h)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

private lemma box_leaf_20 {p t : ℝ} (hpa : (67 / 25 : ℝ) ≤ p) (hpb : p ≤ (68 / 25 : ℝ))
    (hta : (281 / 180 : ℝ) ≤ t) (htb : t ≤ (623 / 360 : ℝ)) :
    1 + 2 * (|1 - t| / 2) ^ p ≤ ((1 + t) / 3) ^ p + 2 * ((5 - t) / 6) ^ p :=
  tangent_secant_box_right
    (pa := (67 / 25 : ℝ)) (pb := (68 / 25 : ℝ)) (ta := (281 / 180 : ℝ)) (tb := (623 / 360 : ℝ))
    (a0 := (127 / 144 : ℝ)) (b0 := (161 / 288 : ℝ)) (ca := (101 / 360 : ℝ)) (cb := (263 / 720 : ℝ))
    (Alo := (71053 / 100000 : ℝ)) (Blo := (20557 / 100000 : ℝ))
    (A1lo := (16113 / 20000 : ℝ)) (A1hi := (5061 / 6250 : ℝ))
    (B1lo := (1471 / 4000 : ℝ)) (B1hi := (18823 / 50000 : ℝ))
    (CAhi := (3319 / 100000 : ℝ)) (CBhi := (673 / 10000 : ℝ))
    (Mlo := (2875573 / 7500000 : ℝ)) (Mhi := (751417 / 1875000 : ℝ))
    (by norm_num) hpa hpb hta htb
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
    (by have h := rational_rpow_ge 71053 100000 127 144 68 25 (by decide) (by decide) (by decide) (by decide +kernel); norm_num at h ⊢; try exact h)
    (by have h := rational_rpow_ge 20557 100000 161 288 68 25 (by decide) (by decide) (by decide) (by decide +kernel); norm_num at h ⊢; try exact h)
    (by have h := rational_rpow_ge 16113 20000 127 144 43 25 (by decide) (by decide) (by decide) (by decide +kernel); norm_num at h ⊢; try exact h)
    (by have h := rational_rpow_le 5061 6250 127 144 42 25 (by decide) (by decide) (by decide) (by decide +kernel); norm_num at h ⊢; try exact h)
    (by have h := rational_rpow_ge 1471 4000 161 288 43 25 (by decide) (by decide) (by decide) (by decide +kernel); norm_num at h ⊢; try exact h)
    (by have h := rational_rpow_le 18823 50000 161 288 42 25 (by decide) (by decide) (by decide) (by decide +kernel); norm_num at h ⊢; try exact h)
    (by have h := rational_rpow_le 3319 100000 101 360 67 25 (by decide) (by decide) (by decide) (by decide +kernel); norm_num at h ⊢; try exact h)
    (by have h := rational_rpow_le 673 10000 263 720 67 25 (by decide) (by decide) (by decide) (by decide +kernel); norm_num at h ⊢; try exact h)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

private lemma box_leaf_21 {p t : ℝ} (hpa : (67 / 25 : ℝ) ≤ p) (hpb : p ≤ (68 / 25 : ℝ))
    (hta : (623 / 360 : ℝ) ≤ t) (htb : t ≤ (19 / 10 : ℝ)) :
    1 + 2 * (|1 - t| / 2) ^ p ≤ ((1 + t) / 3) ^ p + 2 * ((5 - t) / 6) ^ p :=
  tangent_secant_box_right
    (pa := (67 / 25 : ℝ)) (pb := (68 / 25 : ℝ)) (ta := (623 / 360 : ℝ)) (tb := (19 / 10 : ℝ))
    (a0 := (2027 / 2160 : ℝ)) (b0 := (2293 / 4320 : ℝ)) (ca := (263 / 720 : ℝ)) (cb := (9 / 20 : ℝ))
    (Alo := (84123 / 100000 : ℝ)) (Blo := (17853 / 100000 : ℝ))
    (A1lo := (89643 / 100000 : ℝ)) (A1hi := (22469 / 25000 : ℝ))
    (B1lo := (16819 / 50000 : ℝ)) (B1hi := (17253 / 50000 : ℝ))
    (CAhi := (673 / 10000 : ℝ)) (CBhi := (1471 / 12500 : ℝ))
    (Mlo := (1231393 / 2500000 : ℝ)) (Mhi := (159341 / 312500 : ℝ))
    (by norm_num) hpa hpb hta htb
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
    (by have h := rational_rpow_ge 84123 100000 2027 2160 68 25 (by decide) (by decide) (by decide) (by decide +kernel); norm_num at h ⊢; try exact h)
    (by have h := rational_rpow_ge 17853 100000 2293 4320 68 25 (by decide) (by decide) (by decide) (by decide +kernel); norm_num at h ⊢; try exact h)
    (by have h := rational_rpow_ge 89643 100000 2027 2160 43 25 (by decide) (by decide) (by decide) (by decide +kernel); norm_num at h ⊢; try exact h)
    (by have h := rational_rpow_le 22469 25000 2027 2160 42 25 (by decide) (by decide) (by decide) (by decide +kernel); norm_num at h ⊢; try exact h)
    (by have h := rational_rpow_ge 16819 50000 2293 4320 43 25 (by decide) (by decide) (by decide) (by decide +kernel); norm_num at h ⊢; try exact h)
    (by have h := rational_rpow_le 17253 50000 2293 4320 42 25 (by decide) (by decide) (by decide) (by decide +kernel); norm_num at h ⊢; try exact h)
    (by have h := rational_rpow_le 673 10000 263 720 67 25 (by decide) (by decide) (by decide) (by decide +kernel); norm_num at h ⊢; try exact h)
    (by have h := rational_rpow_le 1471 12500 9 20 67 25 (by decide) (by decide) (by decide) (by decide +kernel); norm_num at h ⊢; try exact h)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

private lemma band_0_0 {p t : ℝ} (hpa : (2 : ℝ) ≤ p) (hpb : p ≤ (9 / 4 : ℝ))
    (hta : (1 / 2 : ℝ) ≤ t) (htb : t ≤ (1 : ℝ)) :
    1 + 2 * (|1 - t| / 2) ^ p ≤ ((1 + t) / 3) ^ p + 2 * ((5 - t) / 6) ^ p := by
  exact box_leaf_0 hpa hpb hta htb

private lemma band_0_1 {p t : ℝ} (hpa : (2 : ℝ) ≤ p) (hpb : p ≤ (9 / 4 : ℝ))
    (hta : (1 : ℝ) ≤ t) (htb : t ≤ (3 / 2 : ℝ)) :
    1 + 2 * (|1 - t| / 2) ^ p ≤ ((1 + t) / 3) ^ p + 2 * ((5 - t) / 6) ^ p := by
  exact box_leaf_1 hpa hpb hta htb

private lemma band_1_0 {p t : ℝ} (hpa : (9 / 4 : ℝ) ≤ p) (hpb : p ≤ (5 / 2 : ℝ))
    (hta : (1 / 2 : ℝ) ≤ t) (htb : t ≤ (1 : ℝ)) :
    1 + 2 * (|1 - t| / 2) ^ p ≤ ((1 + t) / 3) ^ p + 2 * ((5 - t) / 6) ^ p := by
  exact box_leaf_2 hpa hpb hta htb

private lemma band_1_1 {p t : ℝ} (hpa : (9 / 4 : ℝ) ≤ p) (hpb : p ≤ (5 / 2 : ℝ))
    (hta : (1 : ℝ) ≤ t) (htb : t ≤ (7 / 4 : ℝ)) :
    1 + 2 * (|1 - t| / 2) ^ p ≤ ((1 + t) / 3) ^ p + 2 * ((5 - t) / 6) ^ p := by
  rcases le_total t (11 / 8 : ℝ) with htm | htm
  · have htb : t ≤ (11 / 8 : ℝ) := htm
    exact box_leaf_3 hpa hpb hta htb
  · have hta : (11 / 8 : ℝ) ≤ t := htm
    rcases le_total t (25 / 16 : ℝ) with htm | htm
    · have htb : t ≤ (25 / 16 : ℝ) := htm
      exact box_leaf_4 hpa hpb hta htb
    · have hta : (25 / 16 : ℝ) ≤ t := htm
      exact box_leaf_5 hpa hpb hta htb

private lemma band_2_0 {p t : ℝ} (hpa : (5 / 2 : ℝ) ≤ p) (hpb : p ≤ (13 / 5 : ℝ))
    (hta : (1 / 2 : ℝ) ≤ t) (htb : t ≤ (7 / 9 : ℝ)) :
    1 + 2 * (|1 - t| / 2) ^ p ≤ ((1 + t) / 3) ^ p + 2 * ((5 - t) / 6) ^ p := by
  exact box_leaf_6 hpa hpb hta htb

private lemma band_2_1 {p t : ℝ} (hpa : (5 / 2 : ℝ) ≤ p) (hpb : p ≤ (13 / 5 : ℝ))
    (hta : (11 / 9 : ℝ) ≤ t) (htb : t ≤ (19 / 10 : ℝ)) :
    1 + 2 * (|1 - t| / 2) ^ p ≤ ((1 + t) / 3) ^ p + 2 * ((5 - t) / 6) ^ p := by
  rcases le_total t (281 / 180 : ℝ) with htm | htm
  · have htb : t ≤ (281 / 180 : ℝ) := htm
    exact box_leaf_7 hpa hpb hta htb
  · have hta : (281 / 180 : ℝ) ≤ t := htm
    rcases le_total t (623 / 360 : ℝ) with htm | htm
    · have htb : t ≤ (623 / 360 : ℝ) := htm
      exact box_leaf_8 hpa hpb hta htb
    · have hta : (623 / 360 : ℝ) ≤ t := htm
      rcases le_total t (1307 / 720 : ℝ) with htm | htm
      · have htb : t ≤ (1307 / 720 : ℝ) := htm
        exact box_leaf_9 hpa hpb hta htb
      · have hta : (1307 / 720 : ℝ) ≤ t := htm
        exact box_leaf_10 hpa hpb hta htb

private lemma band_3_0 {p t : ℝ} (hpa : (13 / 5 : ℝ) ≤ p) (hpb : p ≤ (67 / 25 : ℝ))
    (hta : (1 / 2 : ℝ) ≤ t) (htb : t ≤ (7 / 9 : ℝ)) :
    1 + 2 * (|1 - t| / 2) ^ p ≤ ((1 + t) / 3) ^ p + 2 * ((5 - t) / 6) ^ p := by
  exact box_leaf_11 hpa hpb hta htb

private lemma band_3_1 {p t : ℝ} (hpa : (13 / 5 : ℝ) ≤ p) (hpb : p ≤ (67 / 25 : ℝ))
    (hta : (11 / 9 : ℝ) ≤ t) (htb : t ≤ (19 / 10 : ℝ)) :
    1 + 2 * (|1 - t| / 2) ^ p ≤ ((1 + t) / 3) ^ p + 2 * ((5 - t) / 6) ^ p := by
  rcases le_total t (281 / 180 : ℝ) with htm | htm
  · have htb : t ≤ (281 / 180 : ℝ) := htm
    exact box_leaf_12 hpa hpb hta htb
  · have hta : (281 / 180 : ℝ) ≤ t := htm
    rcases le_total t (623 / 360 : ℝ) with htm | htm
    · have htb : t ≤ (623 / 360 : ℝ) := htm
      exact box_leaf_13 hpa hpb hta htb
    · have hta : (623 / 360 : ℝ) ≤ t := htm
      rcases le_total t (1307 / 720 : ℝ) with htm | htm
      · have htb : t ≤ (1307 / 720 : ℝ) := htm
        exact box_leaf_14 hpa hpb hta htb
      · have hta : (1307 / 720 : ℝ) ≤ t := htm
        exact box_leaf_15 hpa hpb hta htb

private lemma band_4_0 {p t : ℝ} (hpa : (67 / 25 : ℝ) ≤ p) (hpb : p ≤ (68 / 25 : ℝ))
    (hta : (1 / 2 : ℝ) ≤ t) (htb : t ≤ (7 / 9 : ℝ)) :
    1 + 2 * (|1 - t| / 2) ^ p ≤ ((1 + t) / 3) ^ p + 2 * ((5 - t) / 6) ^ p := by
  rcases le_total t (23 / 36 : ℝ) with htm | htm
  · have htb : t ≤ (23 / 36 : ℝ) := htm
    exact box_leaf_16 hpa hpb hta htb
  · have hta : (23 / 36 : ℝ) ≤ t := htm
    exact box_leaf_17 hpa hpb hta htb

private lemma band_4_1 {p t : ℝ} (hpa : (67 / 25 : ℝ) ≤ p) (hpb : p ≤ (68 / 25 : ℝ))
    (hta : (11 / 9 : ℝ) ≤ t) (htb : t ≤ (19 / 10 : ℝ)) :
    1 + 2 * (|1 - t| / 2) ^ p ≤ ((1 + t) / 3) ^ p + 2 * ((5 - t) / 6) ^ p := by
  rcases le_total t (281 / 180 : ℝ) with htm | htm
  · have htb : t ≤ (281 / 180 : ℝ) := htm
    rcases le_total t (167 / 120 : ℝ) with htm | htm
    · have htb : t ≤ (167 / 120 : ℝ) := htm
      exact box_leaf_18 hpa hpb hta htb
    · have hta : (167 / 120 : ℝ) ≤ t := htm
      exact box_leaf_19 hpa hpb hta htb
  · have hta : (281 / 180 : ℝ) ≤ t := htm
    rcases le_total t (623 / 360 : ℝ) with htm | htm
    · have htb : t ≤ (623 / 360 : ℝ) := htm
      exact box_leaf_20 hpa hpb hta htb
    · have hta : (623 / 360 : ℝ) ≤ t := htm
      exact box_leaf_21 hpa hpb hta htb

/-- Global power inequality across `[2, log 3 / log (3 / 2)] × [1 / 2, 2]`. -/
lemma power_ineq_below {p t : ℝ} (hp2 : 2 ≤ p) (hpT : p ≤ Real.log 3 / Real.log (3 / 2))
    (hta : 1 / 2 ≤ t) (htb : t ≤ 2) :
    1 + 2 * (|1 - t| / 2) ^ p ≤ ((1 + t) / 3) ^ p + 2 * ((5 - t) / 6) ^ p := by
  obtain ⟨hp68, h23⟩ := threshold_bounds hpT
  rcases le_total p (9 / 4 : ℝ) with hp94 | hp94
  · rcases le_total t 1 with ht1 | ht1
    · exact band_0_0 hp2 hp94 hta ht1
    · rcases le_total t (3 / 2 : ℝ) with ht32 | ht32
      · exact band_0_1 hp2 hp94 ht1 ht32
      · exact region_near_two_param (H := (21 / 100 : ℝ)) hp2 hp94 (by norm_num) (by norm_num) ht32 htb (by norm_num)
          (by simpa using rational_rpow_ge 21 100 1 2 9 4 (by decide) (by decide) (by decide) (by decide +kernel))
          (by norm_num)
  · rcases le_total p (5 / 2 : ℝ) with hp52 | hp52
    · rcases le_total t 1 with ht1 | ht1
      · exact band_1_0 hp94 hp52 hta ht1
      · rcases le_total t (7 / 4 : ℝ) with ht74 | ht74
        · exact band_1_1 hp94 hp52 ht1 ht74
        · exact region_near_two_param (H := (22 / 125 : ℝ)) hp2 hp52 (by norm_num) (by norm_num) ht74 htb (by norm_num)
            (by simpa using rational_rpow_ge 22 125 1 2 5 2 (by decide) (by decide) (by decide) (by decide +kernel))
            (by norm_num)
    · rcases le_total t (7 / 9 : ℝ) with ht79 | ht79
      · rcases le_total p (13 / 5 : ℝ) with hp135 | hp135
        · exact band_2_0 hp52 hp135 hta ht79
        · rcases le_total p (67 / 25 : ℝ) with hp67 | hp67
          · exact band_3_0 hp135 hp67 hta ht79
          · exact band_4_0 hp67 hp68 hta ht79
      · rcases le_total t (11 / 9 : ℝ) with ht119 | ht119
        · exact region_near_one hp52 h23 ht79 ht119
        · rcases le_total t (19 / 10 : ℝ) with ht19 | ht19
          · rcases le_total p (13 / 5 : ℝ) with hp135 | hp135
            · exact band_2_1 hp52 hp135 ht119 ht19
            · rcases le_total p (67 / 25 : ℝ) with hp67 | hp67
              · exact band_3_1 hp135 hp67 ht119 ht19
              · exact band_4_1 hp67 hp68 ht119 ht19
          · exact region_near_two_param (H := (151 / 1000 : ℝ)) hp2 hp68 (by norm_num) (by norm_num) ht19 htb (by norm_num)
              (by simpa using rational_rpow_ge 151 1000 1 2 68 25 (by decide) (by decide) (by decide) (by decide +kernel))
              (by norm_num)

/-- Complete unconditional proof of `cyclicConstant_le_one_below`. -/
theorem cyclicConstant_le_one_below :
    ∀ p : ℝ, 2 ≤ p → p ≤ Real.log 3 / Real.log (3 / 2) → cyclicConstant p ≤ 1 := by
  intro p hp2 hpT
  have hp0 : 0 < p := by linarith
  have hp1 : 1 < p := by linarith
  refine csSup_le ⟨cyclicRatio p 2, 2, by norm_num, rfl⟩ ?_
  rintro _ ⟨t, ht, rfl⟩
  have hta : 1 / 2 ≤ t := ht.1
  have htb : t ≤ 2 := ht.2
  have ht0 : 0 ≤ t := by linarith
  have hden : 0 < 6 * cyclicA p t - 3 * cyclicB p t := cyclic_denom_pos hp1 ht0
  rw [cyclicRatio, abs_of_nonneg (show 0 ≤ 2 - t by linarith), div_le_one hden]
  -- Reduce to Minkowski inequality on `![t, 1, 1]` and `![(2 - t)/3, (2 - t)/3, (2 - t)/3]`.
  let u : Fin 3 → ℝ := ![t, 1, 1]
  let v : Fin 3 → ℝ := ![(2 - t) / 3, (2 - t) / 3, (2 - t) / 3]
  have hvec3 : ∀ a b c : ℝ, lpNorm p (![a, b, c] : Fin 3 → ℝ) = (|a| ^ p + |b| ^ p + |c| ^ p) ^ (1 / p) := by
    intro a b c; simp [lpNorm, Fin.sum_univ_three]
  have hu_norm : lpNorm p u = cyclicA p t := by
    dsimp [u]; rw [hvec3, cyclicA, abs_of_nonneg ht0, abs_one, Real.one_rpow]
    congr 1; ring
  have hv_norm : lpNorm p v = (3 : ℝ) ^ (1 / p) * ((2 - t) / 3) := by
    have hs0 : 0 ≤ (2 - t) / 3 := by linarith
    dsimp [v]; rw [hvec3, abs_of_nonneg hs0,
      show ((2 - t) / 3) ^ p + ((2 - t) / 3) ^ p + ((2 - t) / 3) ^ p =
        3 * ((2 - t) / 3) ^ p by ring,
      Real.mul_rpow (by norm_num) (Real.rpow_nonneg hs0 p),
      ← Real.rpow_mul hs0, mul_one_div_cancel hp0.ne', Real.rpow_one]
  have huv_norm : lpNorm p (u + v) =
      (((2 + 2 * t) / 3) ^ p + 2 * ((5 - t) / 3) ^ p) ^ (1 / p) := by
    have h1 : 0 ≤ (2 + 2 * t) / 3 := by linarith
    have h2 : 0 ≤ (5 - t) / 3 := by linarith
    have huv_eq : u + v = ![(2 + 2 * t) / 3, (5 - t) / 3, (5 - t) / 3] := by
      ext i; fin_cases i <;> simp [u, v, Pi.add_apply] <;> ring
    rw [huv_eq, hvec3, abs_of_nonneg h1, abs_of_nonneg h2]
    congr 1; ring
  have hmink := lpNorm_add_fin3 hp1.le u v
  rw [hu_norm, hv_norm, huv_norm] at hmink
  have hpwr := power_ineq_below hp2 hpT hta htb
  have hscale := mul_le_mul_of_nonneg_left hpwr (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ p)
  have hlhs : (2 : ℝ) ^ p * (1 + 2 * (|1 - t| / 2) ^ p) = 2 * |1 - t| ^ p + (2 : ℝ) ^ p := by
    have hmul : (2 : ℝ) ^ p * (|1 - t| / 2) ^ p = |1 - t| ^ p := by
      rw [← Real.mul_rpow (by norm_num) (by positivity)]
      congr 1; ring
    linarith
  have hrhs : (2 : ℝ) ^ p * (((1 + t) / 3) ^ p + 2 * ((5 - t) / 6) ^ p) =
      ((2 + 2 * t) / 3) ^ p + 2 * ((5 - t) / 3) ^ p := by
    have hm1 : (2 : ℝ) ^ p * ((1 + t) / 3) ^ p = ((2 + 2 * t) / 3) ^ p := by
      rw [← Real.mul_rpow (by norm_num) (by linarith)]; congr 1; ring
    have hm2 : (2 : ℝ) ^ p * ((5 - t) / 6) ^ p = ((5 - t) / 3) ^ p := by
      rw [← Real.mul_rpow (by norm_num) (by linarith)]; congr 1; ring
    linarith
  rw [hlhs, hrhs] at hscale
  have hB_le : cyclicB p t ≤ (((2 + 2 * t) / 3) ^ p + 2 * ((5 - t) / 3) ^ p) ^ (1 / p) := by
    unfold cyclicB
    exact Real.rpow_le_rpow (by positivity) hscale (by positivity)
  linarith

end HlawkaSchatten.LpThreshold

theorem solution :
    ∀ p : ℝ, 2 ≤ p → p ≤ Real.log 3 / Real.log (3 / 2) → cyclicConstant p ≤ 1 :=
  HlawkaSchatten.LpThreshold.cyclicConstant_le_one_below

#print axioms solution
