-- Prove2me | solution 1 for OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB1_5_2I1_sound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T06:29:37.966191+00:00
-- url     : https://prove2.me/submissions/31f4bf56-e242-4ba2-9f17-5d2fec8eccb7

import Mathlib
import Definitions.Def_OAIQ254M006
import Definitions.Def_OAIQ254M010
import Definitions.Def_OAIQ254M011

section
-- module Solutions.OAIQ254_MF.MatrixFields_Certificates_CertificatesReplay
attribute [-simp] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryIncomingMasks.append_singletons
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
namespace MatrixMultiplication.Foundation.RationalLogCertificate

open scoped BigOperators

theorem symmetric_expansion_error (t : ℝ) (ht : |t| < 1) (n : ℕ) :
    |(Real.log (1 + t) - Real.log (1 - t)) -
        (sumPower t n - sumPower (-t) n)| ≤
      2 * (|t| ^ (n + 1) / (1 - |t|)) := by
  have hminus : |sumPower t n + Real.log (1 - t)| ≤
      |t| ^ (n + 1) / (1 - |t|) :=
    Real.abs_log_sub_add_sum_range_le ht n
  have hplus : |sumPower (-t) n + Real.log (1 + t)| ≤
      |t| ^ (n + 1) / (1 - |t|) := by
    simpa only [sumPower, abs_neg, sub_neg_eq_add] using
      Real.abs_log_sub_add_sum_range_le (by simpa using ht : |-t| < 1) n
  calc
    _ = |(sumPower (-t) n + Real.log (1 + t)) -
        (sumPower t n + Real.log (1 - t))| := by congr 1; ring
    _ ≤ |sumPower (-t) n + Real.log (1 + t)| +
        |sumPower t n + Real.log (1 - t)| := abs_sub _ _
    _ ≤ 2 * (|t| ^ (n + 1) / (1 - |t|)) := by linarith

theorem normalized_variable_bounds (x : ℝ) (hlo : 1 ≤ x) (hhi : x ≤ 2) :
    0 ≤ (x - 1) / (x + 1) ∧ (x - 1) / (x + 1) ≤ 1 / 3 := by
  have hden : 0 < x + 1 := by linarith
  constructor
  · exact div_nonneg (sub_nonneg.mpr hlo) hden.le
  · apply (div_le_iff₀ hden).2
    linarith

theorem normalized_log_error (x : ℝ) (hlo : 1 ≤ x) (hhi : x ≤ 2) (n : ℕ) :
    |Real.log x - realApprox n x| ≤
      2 * (((x - 1) / (x + 1)) ^ (n + 1) / (1 - (x - 1) / (x + 1))) := by
  let t := (x - 1) / (x + 1)
  obtain ⟨ht0, ht3⟩ := normalized_variable_bounds x hlo hhi
  have ht1 : t < 1 := by dsimp [t] <;> linarith
  have hden : x + 1 ≠ 0 := by linarith
  have hminus : 1 - t ≠ 0 := by linarith
  have hplus : 1 + t ≠ 0 := by dsimp [t] <;> linarith
  have hratio : (1 + t) / (1 - t) = x := by
    dsimp [t]
    field_simp [hden]
    ring
  have hlog : Real.log x = Real.log (1 + t) - Real.log (1 - t) := by
    rw [← hratio]
    exact Real.log_div hplus hminus
  have ht0' : 0 ≤ t := ht0
  have herror := symmetric_expansion_error t (by rwa [abs_of_nonneg ht0']) n
  rw [abs_of_nonneg ht0'] at herror
  simpa only [realApprox, ← hlog, t] using herror

end MatrixMultiplication.Foundation.RationalLogCertificate

end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
namespace MatrixMultiplication.AllFieldCertificates

open MatrixMultiplication.Foundation.RationalLogCertificate

namespace Ball

theorem nonnegative_radius {b : Ball} {x : ℝ} (h : b.Encloses x) : 0 ≤ b.radius := by
  have : (0 : ℝ) ≤ b.radius := (abs_nonneg _).trans h
  exact_mod_cast this

theorem bounds {b : Ball} {x : ℝ} (h : b.Encloses x) :
    (b.lower : ℝ) ≤ x ∧ x ≤ (b.upper : ℝ) := by
  obtain ⟨hl, hu⟩ := abs_le.mp h
  simp only [lower, upper, Rat.cast_sub, Rat.cast_add]
  constructor <;> linarith

theorem ofBounds_sound {lo hi : ℚ} {x : ℝ}
    (hlo : (lo : ℝ) ≤ x) (hhi : x ≤ (hi : ℝ)) :
    (ofBounds lo hi).Encloses x := by
  simp only [Encloses, ofBounds, Rat.cast_add, Rat.cast_div, Rat.cast_ofNat,
    Rat.cast_sub]
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem exact_sound (q : ℚ) : (exact q).Encloses (q : ℝ) := by
  simp [Encloses, exact]

theorem add_sound {a b : Ball} {x y : ℝ} (hx : a.Encloses x) (hy : b.Encloses y) :
    (add a b).Encloses (x + y) := by
  unfold Encloses add
  simp only [Rat.cast_add]
  calc
    _ = |(x - (a.center : ℝ)) + (y - (b.center : ℝ))| := by congr 1; ring
    _ ≤ |x - (a.center : ℝ)| + |y - (b.center : ℝ)| := abs_add_le _ _
    _ ≤ _ := add_le_add hx hy

theorem neg_sound {a : Ball} {x : ℝ} (hx : a.Encloses x) :
    (neg a).Encloses (-x) := by
  simpa only [Encloses, neg, Rat.cast_neg, neg_sub_neg, abs_sub_comm] using hx

theorem mul_sound {a b : Ball} {x y : ℝ} (hx : a.Encloses x) (hy : b.Encloses y) :
    (mul a b).Encloses (x * y) := by
  have ha : (0 : ℝ) ≤ a.radius := by exact_mod_cast nonnegative_radius hx
  have hb : (0 : ℝ) ≤ b.radius := by exact_mod_cast nonnegative_radius hy
  unfold Encloses mul
  simp only [Rat.cast_mul, Rat.cast_add, Rat.cast_abs]
  calc
    _ = |(a.center : ℝ) * (y - (b.center : ℝ)) +
          (b.center : ℝ) * (x - (a.center : ℝ)) +
          (x - (a.center : ℝ)) * (y - (b.center : ℝ))| := by congr 1; ring
    _ ≤ |(a.center : ℝ) * (y - (b.center : ℝ))| +
          |(b.center : ℝ) * (x - (a.center : ℝ))| +
          |(x - (a.center : ℝ)) * (y - (b.center : ℝ))| :=
      (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) (le_refl _))
    _ = |(a.center : ℝ)| * |y - (b.center : ℝ)| +
          |(b.center : ℝ)| * |x - (a.center : ℝ)| +
          |x - (a.center : ℝ)| * |y - (b.center : ℝ)| := by simp only [abs_mul]
    _ ≤ _ := add_le_add
      (add_le_add (mul_le_mul_of_nonneg_left hy (abs_nonneg _))
        (mul_le_mul_of_nonneg_left hx (abs_nonneg _)))
      (mul_le_mul hx hy (abs_nonneg _) ha)

theorem widen_sound {a b : Ball} {x : ℝ} (hx : a.Encloses x)
    (h : |a.center - b.center| + a.radius ≤ b.radius) : b.Encloses x := by
  have hc : |(a.center : ℝ) - (b.center : ℝ)| + (a.radius : ℝ) ≤ (b.radius : ℝ) := by
    exact_mod_cast h
  unfold Encloses
  calc
    _ = |(x - (a.center : ℝ)) + ((a.center : ℝ) - (b.center : ℝ))| := by congr 1; ring
    _ ≤ |x - (a.center : ℝ)| + |(a.center : ℝ) - (b.center : ℝ)| := abs_add_le _ _
    _ ≤ (a.radius : ℝ) + |(a.center : ℝ) - (b.center : ℝ)| := add_le_add hx (le_refl _)
    _ ≤ _ := by linarith

theorem inv_sound {a : Ball} {x : ℝ} (hx : a.Encloses x)
    (hpos : 0 < a.lower) : (inv a).Encloses x⁻¹ := by
  have hlo : (0 : ℝ) < a.lower := by exact_mod_cast hpos
  obtain ⟨hl, hu⟩ := bounds hx
  have hxp : 0 < x := lt_of_lt_of_le hlo hl
  apply ofBounds_sound
  · simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_inv, one_div] using
      one_div_le_one_div_of_le hxp hu
  · simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_inv, one_div] using
      one_div_le_one_div_of_le hlo hl

end Ball

theorem log_center_lipschitz {b : Ball} {x : ℝ} (hx : b.Encloses x)
    (hpos : 0 < b.lower) :
    |Real.log x - Real.log (b.center : ℝ)| ≤ (b.radius / b.lower : ℚ) := by
  have hr : (0 : ℝ) ≤ b.radius := by exact_mod_cast Ball.nonnegative_radius hx
  have hl : (0 : ℝ) < b.lower := by exact_mod_cast hpos
  have hcl : (b.lower : ℝ) ≤ b.center := by
    simp only [Ball.lower, Rat.cast_sub]
    linarith
  have hc : (0 : ℝ) < b.center := hl.trans_le hcl
  obtain ⟨hxl, _⟩ := Ball.bounds hx
  have hxp : 0 < x := hl.trans_le hxl
  have logs (a c : ℝ) (ha : 0 < a) (hc : 0 < c) :
      Real.log a - Real.log c ≤ (a - c) / c := by
    rw [← Real.log_div ha.ne' hc.ne']
    have h := Real.log_le_sub_one_of_pos (div_pos ha hc)
    have he : a / c - 1 = (a - c) / c := by field_simp
    rwa [he] at h
  have hup : Real.log x - Real.log (b.center : ℝ) ≤ (b.radius : ℝ) / (b.lower : ℝ) := by
    calc
      _ ≤ (x - (b.center : ℝ)) / (b.center : ℝ) := logs _ _ hxp hc
      _ ≤ (b.radius : ℝ) / (b.center : ℝ) :=
        div_le_div_of_nonneg_right (abs_le.mp hx).2 hc.le
      _ ≤ _ := div_le_div_of_nonneg_left hr hl hcl
  have hdown : Real.log (b.center : ℝ) - Real.log x ≤
      (b.radius : ℝ) / (b.lower : ℝ) := by
    calc
      _ ≤ ((b.center : ℝ) - x) / x := logs _ _ hc hxp
      _ ≤ (b.radius : ℝ) / x :=
        div_le_div_of_nonneg_right (by linarith [(abs_le.mp hx).1]) hxp.le
      _ ≤ _ := div_le_div_of_nonneg_left hr hl hxl
  rw [Rat.cast_div]
  exact abs_le.mpr ⟨by linarith, hup⟩

end MatrixMultiplication.AllFieldCertificates

end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
namespace MatrixMultiplication.AllFieldCertificates.Replay

open MatrixMultiplication.Foundation.RationalLogCertificate

theorem contains_sound {a b : Ball} {x : ℝ}
    (ha : a.Encloses x) (hab : contains a b = true) : b.Encloses x :=
  Ball.widen_sound ha (of_decide_eq_true hab)

theorem checkPolynomial_sound {t : Ball} {x : ℝ} (hx : t.Encloses x)
    (as : List ℚ) (trace : List Ball)
    (h : checkPolynomial t as trace = true) :
    (traceHead trace).Encloses (polynomial x as) := by
  induction as generalizing trace with
  | nil =>
      cases trace with
      | nil => simpa [traceHead, polynomial] using Ball.exact_sound 0
      | cons b bs => simp [checkPolynomial] at h
  | cons a as ih =>
      cases trace with
      | nil => simp [checkPolynomial] at h
      | cons b bs =>
          simp only [checkPolynomial, Bool.and_eq_true] at h
          exact contains_sound
            (Ball.add_sound (Ball.exact_sound a) (Ball.mul_sound hx (ih bs h.2))) h.1

theorem realApprox_eq_polynomial (x : ℝ) :
    realApprox 48 x =
      2 * ((x - 1) / (x + 1)) *
        polynomial (((x - 1) / (x + 1)) ^ 2) logCoefficients := by
  simp only [realApprox, sumPower]
  norm_num [Finset.sum_range_succ, logCoefficients, List.range_succ,
    polynomial, List.map_append, List.foldr_append]
  ring

theorem normalized_log_error_48 (x : ℝ) (hlo : 1 ≤ x) (hhi : x ≤ 2) :
    |Real.log x - realApprox 48 x| < 1 / (2 : ℝ) ^ 72 := by
  obtain ⟨ht0, ht3⟩ := normalized_variable_bounds x hlo hhi
  apply lt_of_le_of_lt (normalized_log_error x hlo hhi 48)
  calc
    _ ≤ 2 * (((1 : ℝ) / 3) ^ 49 / (1 - 1 / 3)) := by gcongr
    _ < 1 / (2 : ℝ) ^ 72 := by norm_num

theorem pad_sound {b : Ball} {x y : ℝ} {error : ℚ}
    (hx : b.Encloses x) (hxy : |y - x| ≤ (error : ℝ)) :
    (pad b error).Encloses y := by
  unfold Ball.Encloses pad at *
  simp only [Rat.cast_add]
  calc
    _ = |(y - x) + (x - (b.center : ℝ))| := by congr 1; ring
    _ ≤ |y - x| + |x - (b.center : ℝ)| := abs_add_le _ _
    _ ≤ (error : ℝ) + (b.radius : ℝ) := add_le_add hxy hx
    _ = _ := by ring

theorem normalizedLogBall_sound {m : ℚ} {trace : List Ball}
    (hlo : 1 ≤ m) (hhi : m ≤ 2)
    (hc : checkPolynomial (.exact (logVariable m ^ 2)) logCoefficients trace = true) :
    (normalizedLogBall m trace).Encloses (Real.log (m : ℝ)) := by
  have hp := checkPolynomial_sound (Ball.exact_sound (logVariable m ^ 2))
    logCoefficients trace hc
  have hv : (logVariable m : ℝ) = ((m : ℝ) - 1) / ((m : ℝ) + 1) := by
    simp [logVariable]
  have ha : (Ball.mul (.exact (2 * logVariable m)) (traceHead trace)).Encloses
      (realApprox 48 (m : ℝ)) := by
    rw [realApprox_eq_polynomial]
    convert Ball.mul_sound (Ball.exact_sound (2 * logVariable m)) hp using 1
    all_goals try with_reducible_and_instances rfl
    simp [hv]
  apply pad_sound ha
  have h := (normalized_log_error_48 (m : ℝ)
    (by exact_mod_cast hlo) (by exact_mod_cast hhi)).le
  simpa using h

end MatrixMultiplication.AllFieldCertificates.Replay

namespace MatrixMultiplication.CompactCertificate

namespace NInterval

lemma div_floor_bounds (n d : ℕ) (hd : 0 < d) :
    ((n / d : ℕ) : ℝ) ≤ (n : ℝ) / d ∧
    (n : ℝ) / d ≤ ((n / d : ℕ) : ℝ) + 1 := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  constructor
  · apply (le_div_iff₀ hd').2
    exact_mod_cast Nat.div_mul_le_self n d
  · apply (div_le_iff₀ hd').2
    have h := Nat.lt_div_mul_add (a := n) hd
    exact_mod_cast (by simpa only [Nat.add_mul, Nat.one_mul] using h.le : n ≤ (n / d + 1) * d)

lemma zero_sound (S : ℕ) : Encloses S zero 0 := by simp [Encloses, zero]

lemma nonneg {S : ℕ} {a : NInterval} {x : ℝ} (h : Encloses S a x) : 0 ≤ x :=
  (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)).trans h.1

lemma add_sound {S : ℕ} {a b : NInterval} {x y : ℝ}
    (hx : Encloses S a x) (hy : Encloses S b y) :
    Encloses S (add a b) (x + y) := by
  simpa [Encloses, add, Nat.cast_add, add_div] using And.intro (add_le_add hx.1 hy.1) (add_le_add hx.2 hy.2)

lemma mul_sound {S : ℕ} (hS : 0 < S) {a b : NInterval} {x y : ℝ}
    (hx : Encloses S a x) (hy : Encloses S b y) :
    Encloses S (mul S a b) (x * y) := by
  have hS' : (0 : ℝ) < S := by exact_mod_cast hS
  have hlo := (div_floor_bounds (a.lo * b.lo) S hS).1
  have hhi := (div_floor_bounds (a.hi * b.hi) S hS).2
  unfold Encloses mul
  simp only [Nat.cast_add, Nat.cast_one]
  constructor
  · calc
      _ ≤ ((a.lo : ℝ) * b.lo / S) / S := by
        exact div_le_div_of_nonneg_right (by simpa only [Nat.cast_mul] using hlo) hS'.le
      _ = ((a.lo : ℝ) / S) * ((b.lo : ℝ) / S) := by ring
      _ ≤ x * y := mul_le_mul hx.1 hy.1 (by positivity) (nonneg hx)
  · calc
      x * y ≤ ((a.hi : ℝ) / S) * ((b.hi : ℝ) / S) :=
        mul_le_mul hx.2 hy.2 (nonneg hy) (by positivity)
      _ = ((a.hi : ℝ) * b.hi / S) / S := by ring
      _ ≤ _ := div_le_div_of_nonneg_right (by simpa only [Nat.cast_mul] using hhi) hS'.le

lemma frac_sound {S n d : ℕ} (hS : 0 < S) (hd : 0 < d) :
    Encloses S (frac S n d) ((n : ℝ) / d) := by
  have hS' : (0 : ℝ) < S := by exact_mod_cast hS
  have hb := div_floor_bounds (n * S) d hd
  unfold Encloses frac
  simp only [Nat.cast_add, Nat.cast_one]
  constructor
  · calc
      _ ≤ ((n : ℝ) * S / d) / S :=
        div_le_div_of_nonneg_right (by simpa only [Nat.cast_mul] using hb.1) hS'.le
      _ = _ := by field_simp
  · calc
      (n : ℝ) / d = ((n : ℝ) * S / d) / S := by field_simp
      _ ≤ _ := div_le_div_of_nonneg_right (by simpa only [Nat.cast_mul] using hb.2) hS'.le

lemma oddHorner_sound {S : ℕ} (hS : 0 < S) {t : NInterval} {x : ℝ}
    (hx : Encloses S t x) (start n : ℕ) :
    Encloses S (oddHorner S t start n) (oddPolynomial x start n) := by
  induction n generalizing start with
  | zero => exact zero_sound S
  | succ n ih =>
    apply add_sound
    · simpa only [Nat.cast_one, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
        using (frac_sound (n := 1) hS (by omega : 0 < 2 * start + 1))
    · exact mul_sound hS hx (ih (start + 1))

end NInterval
end MatrixMultiplication.CompactCertificate

namespace MatrixMultiplication.CompactCertificate
open AllFieldCertificates AllFieldCertificates.Replay
open Foundation.RationalLogCertificate

lemma oddPolynomial_eq (x : ℝ) :
    NInterval.oddPolynomial x 0 24 = polynomial x logCoefficients := by
  norm_num [NInterval.oddPolynomial, polynomial, logCoefficients, List.range_succ]

lemma scale_pos : 0 < scale := by decide

lemma logApprox_sound {n d : ℕ} (hd : 0 < d) (hlo : d ≤ n) :
    (logApprox n d).Encloses scale (realApprox 48 ((n : ℝ) / d)) := by
  have hd' : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  have hsum : 0 < n + d := by omega
  have hu := NInterval.frac_sound (n := n - d) scale_pos hsum
  have heq : (((n : ℝ) / d - 1) / ((n : ℝ) / d + 1)) =
      ((n - d : ℕ) : ℝ) / (n + d : ℕ) := by
    rw [Nat.cast_sub hlo, Nat.cast_add]
    field_simp
  rw [realApprox_eq_polynomial, heq, ← oddPolynomial_eq]
  simpa only [logApprox, two_mul, pow_two] using
    NInterval.mul_sound scale_pos (NInterval.add_sound hu hu)
      (NInterval.oddHorner_sound scale_pos (NInterval.mul_sound scale_pos hu hu) 0 24)

lemma NInterval.ball_sound {a : NInterval} {x : ℝ} (h : a.Encloses scale x) :
    a.ball.Encloses x := by
  apply Ball.ofBounds_sound
  · simpa only [Rat.cast_div, Rat.cast_natCast] using h.1
  · simpa only [Rat.cast_div, Rat.cast_natCast] using h.2

lemma normalized_sound {n d : ℕ} (hd : 0 < d) (hlo : d ≤ n) (hhi : n ≤ 2 * d) :
    (normalized n d).Encloses (Real.log ((n : ℝ) / d)) := by
  apply pad_sound (NInterval.ball_sound (logApprox_sound hd hlo))
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have hl : 1 ≤ (n : ℝ) / d := (le_div_iff₀ hd').2 (by simpa only [one_mul] using (Nat.cast_le.mpr hlo : (d : ℝ) ≤ n))
  have hh : (n : ℝ) / d ≤ 2 := (div_le_iff₀ hd').2 (by exact_mod_cast hhi)
  simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_pow, Rat.cast_ofNat] using
    (normalized_log_error_48 ((n : ℝ) / d) hl hh).le

lemma checkLog_sound {two a b : Ball} {w : LogData} {x : ℝ}
    (htwo : two.Encloses (Real.log 2)) (hx : a.Encloses x)
    (h : checkLog two a b w = true) : b.Encloses (Real.log x) := by
  simp only [checkLog, Bool.and_eq_true] at h
  obtain ⟨hpos, hd, hlo, hhi, heq⟩ := of_decide_eq_true h.1
  have hm : (0 : ℝ) < (w.numerator : ℝ) / w.denominator := by
    have hn : 0 < w.numerator := lt_of_lt_of_le hd hlo
    exact div_pos (Nat.cast_pos.mpr hn) (Nat.cast_pos.mpr hd)
  have heq' : (a.center : ℝ) = ((w.numerator : ℝ) / w.denominator) * (2 : ℝ) ^ w.exponent := by
    simpa only [Rat.cast_mul, Rat.cast_zpow, Rat.cast_ofNat, Rat.cast_div, Rat.cast_natCast] using
      congrArg (fun q : ℚ => (q : ℝ)) heq
  have hlog : Real.log (a.center : ℝ) =
      Real.log ((w.numerator : ℝ) / w.denominator) + (w.exponent : ℝ) * Real.log 2 := by
    rw [heq', Real.log_mul (ne_of_gt hm) (zpow_ne_zero _ (by norm_num)), Real.log_zpow]
  have hcenter : (Ball.add (normalized w.numerator w.denominator)
      (Ball.mul (.exact w.exponent) two)).Encloses (Real.log (a.center : ℝ)) := by
    rw [hlog]
    exact Ball.add_sound (normalized_sound hd hlo hhi)
      (by simpa using Ball.mul_sound (Ball.exact_sound (w.exponent : ℚ)) htwo)
  exact contains_sound (pad_sound hcenter (log_center_lipschitz hx hpos)) h.2

end MatrixMultiplication.CompactCertificate

namespace MatrixMultiplication.AllFieldCertificates.Replay

theorem checkLog_sound {two a b : Ball} {w : LogWitness} {x : ℝ}
    (htwo : two.Encloses (Real.log 2)) (hx : a.Encloses x)
    (h : checkLog two a b w = true) : b.Encloses (Real.log x) :=
  MatrixMultiplication.CompactCertificate.checkLog_sound htwo hx h

end MatrixMultiplication.AllFieldCertificates.Replay

end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Entropy_ZeroLeafRateFormula
attribute [-simp] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryIncomingMasks.append_singletons
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

namespace MatrixMultiplication.CompactCertificate
open AllFieldCertificates AllFieldCertificates.Replay

lemma EntropyDatum.sound {two : Ball} (htwo : two.Encloses (Real.log 2))
    {c : EntropyDatum} (hc : c.check two = true) {x : ℝ}
    (hx : c.input.Encloses x) : c.output.Encloses (Foundation.entropyTerm x) := by
  cases c with
  | zero =>
    have hb := Ball.bounds hx
    have h : x = 0 := by
      norm_num [EntropyDatum.input, Ball.lower, Ball.upper, Ball.exact] at hb
      linarith
    simp only [h, Foundation.entropyTerm, neg_zero, zero_mul]
    simpa only [EntropyDatum.output, Rat.cast_zero] using Ball.exact_sound 0
  | log p e l w =>
    simp only [EntropyDatum.check, Bool.and_eq_true] at hc
    obtain ⟨hl, he⟩ := hc
    exact contains_sound (Ball.mul_sound (Ball.neg_sound hx)
      (checkLog_sound htwo hx hl)) he

lemma entropyLookup_check {two : Ball} {cs : List EntropyDatum}
    (h : cs.all (fun c => c.check two) = true) (i : ℕ) :
    (entropyLookup cs i).check two = true := by
  induction cs generalizing i with
  | nil => simp [entropyLookup, EntropyDatum.check]
  | cons c cs ih =>
    simp only [List.all_cons, Bool.and_eq_true] at h
    cases i with
    | zero => simpa [entropyLookup] using h.1
    | succ i => simpa [entropyLookup] using ih h.2 i

lemma entropyLookup_sound {two : Ball} (htwo : two.Encloses (Real.log 2))
    {cs : List EntropyDatum} (h : cs.all (fun c => c.check two) = true)
    (i : ℕ) {x : ℝ} (hx : (entropyLookup cs i).input.Encloses x) :
    (entropyLookup cs i).output.Encloses (Foundation.entropyTerm x) :=
  EntropyDatum.sound htwo (entropyLookup_check h i) hx

end MatrixMultiplication.CompactCertificate

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Certificates_SparseContraction
attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldConstructionData.tagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinalState.wordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.tagsFintype
attribute [-simp] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.shapeValue_relot _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalStatisticLaws.history_inl _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalStatisticLaws.law_inl
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.AllFieldInitialEntropyCertificate
open AllFieldParameters AllFieldCertificates AllFieldCertificates.Replay
open scoped BigOperators

lemma exponential_polynomial_cast (n : ℤ) :
    (((∑ j ∈ Finset.range 17, ((n : ℚ) / 640000) ^ j /
      Nat.factorial j : ℚ) : ℝ)) =
    polynomial (((n : ℚ) / 640000 : ℚ) : ℝ) exponentialCoefficients := by
  simp only [Rat.cast_sum, Rat.cast_div, Rat.cast_pow, Rat.cast_natCast]
  norm_num [Finset.sum_range_succ, exponentialCoefficients, List.range_succ,
    polynomial, List.map_append]
  ring

lemma weight_enclosed_of_trace (n : ℤ) (trace : List Ball)
    (b₁ b₂ b₃ b₄ b₅ b₆ : Ball)
    (hp : checkPolynomial (.exact ((n : ℚ) / 640000))
      exponentialCoefficients trace = true)
    (h₁ : contains (.mul (traceHead trace) (traceHead trace)) b₁ = true)
    (h₂ : contains (.mul b₁ b₁) b₂ = true)
    (h₃ : contains (.mul b₂ b₂) b₃ = true)
    (h₄ : contains (.mul b₃ b₃) b₄ = true)
    (h₅ : contains (.mul b₄ b₄) b₅ = true)
    (h₆ : contains (.mul b₅ b₅) b₆ = true) :
    b₆.Encloses (weight n : ℝ) := by
  have p := checkPolynomial_sound (Ball.exact_sound ((n : ℚ) / 640000))
    exponentialCoefficients trace hp
  rw [← exponential_polynomial_cast] at p
  have p₁ := contains_sound (Ball.mul_sound p p) h₁
  have p₂ := contains_sound (Ball.mul_sound p₁ p₁) h₂
  have p₃ := contains_sound (Ball.mul_sound p₂ p₂) h₃
  have p₄ := contains_sound (Ball.mul_sound p₃ p₃) h₄
  have p₅ := contains_sound (Ball.mul_sound p₄ p₄) h₅
  have p₆ := contains_sound (Ball.mul_sound p₅ p₅) h₆
  convert p₆ using 1
  all_goals try with_reducible_and_instances rfl
  simp only [weight, Rat.cast_pow]
  ring

lemma listSumBall_sound {α : Type*} (xs : List α) (b : α → Ball) (v : α → ℝ)
    (h : ∀ x ∈ xs, (b x).Encloses (v x)) :
    (listSumBall xs b).Encloses ((xs.map v).sum) := by
  induction xs with
  | nil => simpa [listSumBall] using Ball.exact_sound 0
  | cons x xs ih =>
    simpa only [listSumBall, List.foldr_cons, List.map_cons, List.sum_cons] using
      Ball.add_sound (h x (by simp)) (ih (fun y hy => h y (by simp [hy])))

lemma finSumBall_sound (n : ℕ) (b : Fin n → Ball) (v : Fin n → ℝ)
    (h : ∀ i, (b i).Encloses (v i)) :
    (finSumBall n b).Encloses (∑ i, v i) := by
  induction n with
  | zero => simpa [finSumBall] using Ball.exact_sound 0
  | succ n ih =>
    rw [Fin.sum_univ_succ]
    exact Ball.add_sound (h 0) (ih _ _ (fun i => h i.succ))

lemma logTwoBall_sound : logTwoBall.Encloses (Real.log 2) := by
  have h := normalizedLogBall_sound (m := 2) (trace := logTwoTrace)
    (by norm_num) (by norm_num) (by decide +kernel)
  exact contains_sound h (by decide +kernel)

end MatrixMultiplication.AllFieldInitialEntropyCertificate

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate
open scoped BigOperators

lemma splitWeight_three_enclosed (parents : List Shape) (data : List ℤ)
    (s u : Shape) (n₀ n₁ n₂ : ℤ) (b₀ b₁ b₂ : Ball)
    (hsig : splitSignature parents data s u = (Matrix.vecCons (n₀) (Matrix.vecCons (n₁) (Matrix.vecCons (n₂) Matrix.vecEmpty))))
    (h₀ : b₀.Encloses (weight n₀ : ℝ))
    (h₁ : b₁.Encloses (weight n₁ : ℝ))
    (h₂ : b₂.Encloses (weight n₂ : ℝ)) :
    (Ball.mul b₀ (Ball.mul b₁ b₂)).Encloses (splitWeight parents data s u : ℝ) := by
  convert Ball.mul_sound h₀ (Ball.mul_sound h₁ h₂) using 1
  all_goals try with_reducible_and_instances rfl
  simp [splitWeight, hsig, Fin.prod_univ_succ]

lemma list_cast_enclosed {A : Type*} (xs : List A) (b : A → Ball) (v : A → ℚ)
    (h : ∀ a ∈ xs, (b a).Encloses (v a : ℝ)) :
    (listSumBall xs b).Encloses ((xs.map v).sum : ℝ) := by
  simpa only [Rat.cast_list_sum, List.map_map, Function.comp_def] using
    listSumBall_sound xs b (fun a => (v a : ℝ)) h

lemma product_fin6_enclosed (bs : Fin 6 → Fin 6 → Ball) (v : PairSlot → ℝ)
    (h : ∀ i j, (bs i j).Encloses (v (i,j))) :
    (finSumBall 6 (fun i => finSumBall 6 (bs i))).Encloses (∑ s : PairSlot, v s) := by
  rw [Fintype.sum_prod_type]
  exact finSumBall_sound 6 _ _ (fun i => finSumBall_sound 6 _ _ (h i))

lemma entropyTerm_ball {p : ℝ} {b l : Ball} (hb : b.Encloses p)
    (hl : l.Encloses (Real.log p)) :
    (Ball.mul (Ball.neg b) l).Encloses (Foundation.entropyTerm p) :=
  Ball.mul_sound (Ball.neg_sound hb) hl

lemma entropyTerm_zero_ball {p : ℝ} (hp : (Ball.exact 0).Encloses p) :
    (Ball.exact 0).Encloses (Foundation.entropyTerm p) := by
  have hb := Ball.bounds hp
  have h : p = 0 := by norm_num [Ball.lower, Ball.upper, Ball.exact] at hb <;> linarith
  simp only [h, Foundation.entropyTerm, neg_zero, zero_mul]
  simpa only [Rat.cast_zero] using Ball.exact_sound 0

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators

lemma exact_rat_enclosed {q r : ℚ} (h : q = r) : (Ball.exact q).Encloses (r : ℝ) := by
  rw [h]
  exact Ball.exact_sound r

lemma pairSumBall_sound (bs : PairSlot → Ball) (v : PairSlot → ℝ)
    (h : ∀ a, (bs a).Encloses (v a)) :
    (pairSumBall bs).Encloses (∑ a, v a) := by
  exact product_fin6_enclosed _ _ (fun i j => h (i,j))

lemma entropyFin_enclosed (n : ℕ) (p : Fin n → ℝ) (bs : Fin n → Ball)
    (h : ∀ i, (bs i).Encloses (Foundation.entropyTerm (p i))) :
    (finSumBall n bs).Encloses (Foundation.finiteEntropy p) :=
  finSumBall_sound n _ _ h

lemma entropyPair_enclosed (p : PairSlot → ℝ) (bs : PairSlot → Ball)
    (h : ∀ i, (bs i).Encloses (Foundation.entropyTerm (p i))) :
    (pairSumBall bs).Encloses (Foundation.finiteEntropy p) :=
  pairSumBall_sound _ _ h

lemma homogeneous_enclosed {A : Type*} [Fintype A] (p : A → ℝ)
    {b e : Ball} (hb : b.Encloses (Foundation.entropyTerm (∑ a, p a)))
    (he : e.Encloses (Foundation.finiteEntropy p)) :
    (Ball.add (Ball.neg b) e).Encloses (homogeneousEntropy p) := by
  convert Ball.add_sound (Ball.neg_sound hb) he using 1
  all_goals try with_reducible_and_instances rfl
  simp only [homogeneousEntropy, Foundation.entropyTerm, neg_mul, neg_neg]

lemma pairLawBall_sound_on {A : Type*} [Fintype A] (support : List Shape) (s : Shape)
    (bs : Shape → Ball) (p : Shape → ℝ) (bq : Shape → A → Ball) (q : Shape → A → ℝ)
    (hp : ∀ u ∈ support, (bs u).Encloses (p u))
    (hq : ∀ u ∈ support, ∀ a, (bq u a).Encloses (q u a))
    (hcq : ∀ u ∈ support, ∀ a, (bq (complement s u) a).Encloses (q (complement s u) a))
    (ij : A × A) :
    (pairLawBall support s bs bq ij).Encloses (pairLaw support s p q ij) := by
  apply listSumBall_sound
  intro u hu
  exact Ball.mul_sound (Ball.mul_sound (hp u hu) (hq u hu ij.1)) (hcq u hu ij.2)

lemma residualBall_sound_on {A : Type*} [Fintype A] (support : List Shape)
    (bs : Shape → Ball) (p : Shape → ℝ) (priority : Placement) (position : Fin 3)
    (bq : Shape → A → Ball) (q : Shape → A → ℝ)
    (hp : ∀ u ∈ support, (bs u).Encloses (p u))
    (hq : ∀ u ∈ support, ∀ a, (bq u a).Encloses (q u a)) (k : Fin 17) (a : A) :
    (residualBall support bs priority position bq k a).Encloses
      (residualLaw support p priority position q k a) := by
  apply listSumBall_sound
  intro u hu
  by_cases hk : ¬ designated priority position u ∧ u (priority position) = k.val
  · simpa only [ite_eq_left hk] using Ball.mul_sound (hp u hu) (hq u hu a)
  · simpa only [hk, ite_false, if_false, Rat.cast_zero] using Ball.exact_sound 0

lemma singletonBall_sound {A : Type*} [Fintype A] (support : List Shape)
    (bs : Shape → Ball) (p : Shape → ℝ) (priority : Placement) (position : Fin 3)
    (be : Shape → Ball) (q : Shape → A → ℝ)
    (hp : ∀ u ∈ support, (bs u).Encloses (p u))
    (he : ∀ u ∈ support, designated priority position u →
      (be u).Encloses (homogeneousEntropy (q u))) :
    (singletonBall support bs priority position be).Encloses
      (singletonEntropy support p priority position q) := by
  apply listSumBall_sound
  intro u hu
  by_cases hk : designated priority position u
  · simpa only [hk, ite_true, if_true] using Ball.mul_sound (hp u hu) (he u hu hk)
  · simpa only [hk, ite_false, if_false, Rat.cast_zero] using Ball.exact_sound 0

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Certificates_Weights2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate
open scoped BigOperators
lemma w64_sound : w64.Encloses (weight (-32184) : ℝ) := by
  exact weight_enclosed_of_trace (-32184) w64Trace w64S0 w64S1 w64S2 w64S3 w64S4 w64S5
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end MatrixMultiplication.NativeNumerics

end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Certificates_Zero0_1_7
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate
open scoped BigOperators
lemma w195_sound : w195.Encloses (weight 0 : ℝ) := by
  have he : weight 0 = 1 := by decide +kernel
  rw [he, Rat.cast_one]
  simpa only [w195, Rat.cast_one] using Ball.exact_sound 1

end MatrixMultiplication.NativeNumerics

end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Certificates_SplitB5_1_2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate
open scoped BigOperators
lemma w164_sound : w164.Encloses (weight (-5716) : ℝ) := by
  exact weight_enclosed_of_trace (-5716) w164Trace w164S0 w164S1 w164S2 w164S3 w164S4 w164S5
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

lemma B1_5_2_below : below (shape 1 5 2) = [
  (shape 0 2 2),
  (shape 0 3 1),
  (shape 0 4 0),
  (shape 1 1 2),
  (shape 1 2 1),
  (shape 1 3 0)] := by decide +kernel
lemma B1_5_2Raw_0_2_2 : (B1_5_2Raw (shape 0 2 2)).Encloses (splitWeight positiveSecond tablep (shape 1 5 2) (shape 0 2 2) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveSecond tablep (shape 1 5 2) (shape 0 2 2)
    (0) (0) (-5716) w195 w195 w164
    (by decide +kernel) w195_sound w195_sound w164_sound) (by decide +kernel)
lemma B1_5_2Raw_0_3_1 : (B1_5_2Raw (shape 0 3 1)).Encloses (splitWeight positiveSecond tablep (shape 1 5 2) (shape 0 3 1) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveSecond tablep (shape 1 5 2) (shape 0 3 1)
    (0) (0) (0) w195 w195 w195
    (by decide +kernel) w195_sound w195_sound w195_sound) (by decide +kernel)
lemma B1_5_2Raw_0_4_0 : (B1_5_2Raw (shape 0 4 0)).Encloses (splitWeight positiveSecond tablep (shape 1 5 2) (shape 0 4 0) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveSecond tablep (shape 1 5 2) (shape 0 4 0)
    (0) (-32184) (-5716) w195 w64 w164
    (by decide +kernel) w195_sound w64_sound w164_sound) (by decide +kernel)
lemma B1_5_2Raw_1_1_2 : (B1_5_2Raw (shape 1 1 2)).Encloses (splitWeight positiveSecond tablep (shape 1 5 2) (shape 1 1 2) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveSecond tablep (shape 1 5 2) (shape 1 1 2)
    (0) (-32184) (-5716) w195 w64 w164
    (by decide +kernel) w195_sound w64_sound w164_sound) (by decide +kernel)
lemma B1_5_2Raw_1_2_1 : (B1_5_2Raw (shape 1 2 1)).Encloses (splitWeight positiveSecond tablep (shape 1 5 2) (shape 1 2 1) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveSecond tablep (shape 1 5 2) (shape 1 2 1)
    (0) (0) (0) w195 w195 w195
    (by decide +kernel) w195_sound w195_sound w195_sound) (by decide +kernel)
lemma B1_5_2Raw_1_3_0 : (B1_5_2Raw (shape 1 3 0)).Encloses (splitWeight positiveSecond tablep (shape 1 5 2) (shape 1 3 0) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveSecond tablep (shape 1 5 2) (shape 1 3 0)
    (0) (0) (-5716) w195 w195 w164
    (by decide +kernel) w195_sound w195_sound w164_sound) (by decide +kernel)
lemma B1_5_2Raw_sound (u : Shape) (hu : u ∈ below (shape 1 5 2)) :
    (B1_5_2Raw u).Encloses (splitWeight positiveSecond tablep (shape 1 5 2) u : ℝ) := by
  rw [B1_5_2_below] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl
  · exact B1_5_2Raw_0_2_2
  · exact B1_5_2Raw_0_3_1
  · exact B1_5_2Raw_0_4_0
  · exact B1_5_2Raw_1_1_2
  · exact B1_5_2Raw_1_2_1
  · exact B1_5_2Raw_1_3_0
lemma B1_5_2Den_sound : B1_5_2Den.Encloses (((below (shape 1 5 2)).map (splitWeight positiveSecond tablep (shape 1 5 2))).sum : ℝ) := by
  exact contains_sound (list_cast_enclosed (below (shape 1 5 2)) B1_5_2Raw (splitWeight positiveSecond tablep (shape 1 5 2)) B1_5_2Raw_sound) (by decide +kernel)
lemma B1_5_2Den_positive : 0 < B1_5_2Den.lower := by decide +kernel
lemma B1_5_2Law_check_0_2_2 : contains (.mul (B1_5_2Raw (shape 0 2 2)) (.inv B1_5_2Den)) (B1_5_2Table (shape 0 2 2)) = true := by decide +kernel
lemma B1_5_2Law_check_0_3_1 : contains (.mul (B1_5_2Raw (shape 0 3 1)) (.inv B1_5_2Den)) (B1_5_2Table (shape 0 3 1)) = true := by decide +kernel
lemma B1_5_2Law_check_0_4_0 : contains (.mul (B1_5_2Raw (shape 0 4 0)) (.inv B1_5_2Den)) (B1_5_2Table (shape 0 4 0)) = true := by decide +kernel
lemma B1_5_2Law_check_1_1_2 : contains (.mul (B1_5_2Raw (shape 1 1 2)) (.inv B1_5_2Den)) (B1_5_2Table (shape 1 1 2)) = true := by decide +kernel
lemma B1_5_2Law_check_1_2_1 : contains (.mul (B1_5_2Raw (shape 1 2 1)) (.inv B1_5_2Den)) (B1_5_2Table (shape 1 2 1)) = true := by decide +kernel
lemma B1_5_2Law_check_1_3_0 : contains (.mul (B1_5_2Raw (shape 1 3 0)) (.inv B1_5_2Den)) (B1_5_2Table (shape 1 3 0)) = true := by decide +kernel
lemma B1_5_2Law_check (u : Shape) (hu : u ∈ below (shape 1 5 2)) :
    contains (.mul (B1_5_2Raw u) (.inv B1_5_2Den)) (B1_5_2Table u) = true := by
  rw [B1_5_2_below] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl
  · exact B1_5_2Law_check_0_2_2
  · exact B1_5_2Law_check_0_3_1
  · exact B1_5_2Law_check_0_4_0
  · exact B1_5_2Law_check_1_1_2
  · exact B1_5_2Law_check_1_2_1
  · exact B1_5_2Law_check_1_3_0
lemma B1_5_2Law_sound (u : Shape) :
    (B1_5_2Law u).Encloses (stageBLaw (shape 1 5 2) u : ℝ) := by
  by_cases hu : u ∈ below (shape 1 5 2)
  · have h := contains_sound (Ball.mul_sound (B1_5_2Raw_sound u hu)
      (Ball.inv_sound B1_5_2Den_sound B1_5_2Den_positive)) (B1_5_2Law_check u hu)
    simpa only [B1_5_2Law, hu, ite_true, if_true, stageBLaw, splitLaw,
      Rat.cast_div, Rat.cast_mul, Rat.cast_inv, div_eq_mul_inv] using h
  · simp only [B1_5_2Law, hu, ite_false, if_false, stageBLaw, splitLaw, Rat.cast_zero]
    simpa only [Rat.cast_zero] using Ball.exact_sound 0

end MatrixMultiplication.NativeNumerics

end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Certificates_LittleB1_3_4
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
lemma shapes4_list : shapes 4 = [
  (shape 0 0 4),
  (shape 0 1 3),
  (shape 0 2 2),
  (shape 0 3 1),
  (shape 0 4 0),
  (shape 1 0 3),
  (shape 1 1 2),
  (shape 1 2 1),
  (shape 1 3 0),
  (shape 2 0 2),
  (shape 2 1 1),
  (shape 2 2 0),
  (shape 3 0 1),
  (shape 3 1 0),
  (shape 4 0 0)] := by decide +kernel

end MatrixMultiplication.NativeNumerics

end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Certificates_LittleB1_5_2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
lemma B1_5_2Binary_eq (u : Shape) (hu : u ∈ shapes 4) :
    binaryParameter (shape 1 5 2) u = B1_5_2Binary u := by
  rw [shapes4_list] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel

lemma B1_5_2Little_sound (u : Shape) (w : Fin 3) (i : Fin 6) :
    (B1_5_2Little u w i).Encloses (littleLaw (shape 1 5 2) u w i : ℝ) := by
  by_cases hu : u ∈ shapes 4
  · simp only [B1_5_2Little, hu, ite_true, if_true]
    apply exact_rat_enclosed
    simp only [B1_5_2LittleRat, littleLaw, B1_5_2Binary_eq u hu]
  · simp only [B1_5_2Little, hu, ite_false, if_false]
    exact Ball.exact_sound _

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityB_CapB1_5_2I1
attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldConstructionData.tagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinalState.wordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.tagsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
lemma CB1_5_2I1PairRaw_sound (a : PairSlot) :
    (CB1_5_2I1PairRaw a).Encloses (CB1_5_2I1PairValue a) := by
  exact pairLawBall_sound_on (below (shape 1 5 2)) (shape 1 5 2) B1_5_2Law (fun u => (stageBLaw (shape 1 5 2) u : ℝ)) (fun u => B1_5_2Little u ((stageBPriority (shape 1 5 2)) 1)) (fun u a => (littleLaw (shape 1 5 2) u ((stageBPriority (shape 1 5 2)) 1) a : ℝ)) (fun u _ => B1_5_2Law_sound u) (fun u _ a => B1_5_2Little_sound u ((stageBPriority (shape 1 5 2)) 1) a) (fun u _ a => B1_5_2Little_sound (complement (shape 1 5 2) u) ((stageBPriority (shape 1 5 2)) 1) a) a
lemma CB1_5_2I1PairCertificates_valid :
    CB1_5_2I1PairCertificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
lemma CB1_5_2I1PairP_check : ∀ a : PairSlot, contains (CB1_5_2I1PairRaw a) (CB1_5_2I1PairP a) = true := by
  decide +kernel
lemma CB1_5_2I1PairP_sound (a : PairSlot) :
    (CB1_5_2I1PairP a).Encloses (CB1_5_2I1PairValue a) :=
  contains_sound (CB1_5_2I1PairRaw_sound a) (CB1_5_2I1PairP_check a)
lemma CB1_5_2I1PairTerms_sound (a : PairSlot) :
    (CB1_5_2I1PairTerms a).Encloses (Foundation.entropyTerm (CB1_5_2I1PairValue a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB1_5_2I1PairCertificates_valid
    (CB1_5_2I1PairCertificateIndex a) (CB1_5_2I1PairP_sound a)
lemma CB1_5_2I1PairEntropy_sound : CB1_5_2I1PairEntropy.Encloses (Foundation.finiteEntropy CB1_5_2I1PairValue) := by
  exact contains_sound (entropyPair_enclosed CB1_5_2I1PairValue CB1_5_2I1PairTerms CB1_5_2I1PairTerms_sound) (by decide +kernel)
lemma CB1_5_2I1PairMass_sound : CB1_5_2I1PairMass.Encloses (∑ a, CB1_5_2I1PairValue a) := by
  exact contains_sound (pairSumBall_sound CB1_5_2I1PairP CB1_5_2I1PairValue CB1_5_2I1PairP_sound) (by decide +kernel)
lemma CB1_5_2I1PairMassTermLog_sound : CB1_5_2I1PairMassTermLog.Encloses (Real.log ((∑ a, CB1_5_2I1PairValue a))) := by
  exact checkLog_sound logTwoBall_sound (CB1_5_2I1PairMass_sound) (w := CB1_5_2I1PairMassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
lemma CB1_5_2I1PairMassTerm_sound : CB1_5_2I1PairMassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB1_5_2I1PairValue a))) := by
  exact contains_sound (entropyTerm_ball (CB1_5_2I1PairMass_sound) CB1_5_2I1PairMassTermLog_sound) (by decide +kernel)
lemma CB1_5_2I1PairH_sound : CB1_5_2I1PairH.Encloses (homogeneousEntropy CB1_5_2I1PairValue) := by
  exact contains_sound (homogeneous_enclosed CB1_5_2I1PairValue CB1_5_2I1PairMassTerm_sound CB1_5_2I1PairEntropy_sound) (by decide +kernel)

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
lemma CB1_5_2I1R0Raw_sound (a : Fin 6) :
    (CB1_5_2I1R0Raw a).Encloses (CB1_5_2I1R0Value a) := by
  exact residualBall_sound_on (below (shape 1 5 2)) B1_5_2Law (fun u => (stageBLaw (shape 1 5 2) u : ℝ)) (stageBPriority (shape 1 5 2)) 1 (fun u => B1_5_2Little u ((stageBPriority (shape 1 5 2)) 1)) (fun u a => (littleLaw (shape 1 5 2) u ((stageBPriority (shape 1 5 2)) 1) a : ℝ)) (fun u _ => B1_5_2Law_sound u) (fun u _ a => B1_5_2Little_sound u ((stageBPriority (shape 1 5 2)) 1) a) 0 a
lemma CB1_5_2I1R0Certificates_valid :
    CB1_5_2I1R0Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
lemma CB1_5_2I1R0P_check : ∀ a : Fin 6, contains (CB1_5_2I1R0Raw a) (CB1_5_2I1R0P a) = true := by
  decide +kernel
lemma CB1_5_2I1R0P_sound (a : Fin 6) :
    (CB1_5_2I1R0P a).Encloses (CB1_5_2I1R0Value a) :=
  contains_sound (CB1_5_2I1R0Raw_sound a) (CB1_5_2I1R0P_check a)
lemma CB1_5_2I1R0Terms_sound (a : Fin 6) :
    (CB1_5_2I1R0Terms a).Encloses (Foundation.entropyTerm (CB1_5_2I1R0Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB1_5_2I1R0Certificates_valid
    (CB1_5_2I1R0CertificateIndex a) (CB1_5_2I1R0P_sound a)
lemma CB1_5_2I1R0Entropy_sound : CB1_5_2I1R0Entropy.Encloses (Foundation.finiteEntropy CB1_5_2I1R0Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB1_5_2I1R0Value CB1_5_2I1R0Terms CB1_5_2I1R0Terms_sound) (by decide +kernel)
lemma CB1_5_2I1R0Mass_sound : CB1_5_2I1R0Mass.Encloses (∑ a, CB1_5_2I1R0Value a) := by
  exact contains_sound (finSumBall_sound 6 CB1_5_2I1R0P CB1_5_2I1R0Value CB1_5_2I1R0P_sound) (by decide +kernel)
lemma CB1_5_2I1R0MassTermLog_sound : CB1_5_2I1R0MassTermLog.Encloses (Real.log ((∑ a, CB1_5_2I1R0Value a))) := by
  exact checkLog_sound logTwoBall_sound (CB1_5_2I1R0Mass_sound) (w := CB1_5_2I1R0MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
lemma CB1_5_2I1R0MassTerm_sound : CB1_5_2I1R0MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB1_5_2I1R0Value a))) := by
  exact contains_sound (entropyTerm_ball (CB1_5_2I1R0Mass_sound) CB1_5_2I1R0MassTermLog_sound) (by decide +kernel)
lemma CB1_5_2I1R0H_sound : CB1_5_2I1R0H.Encloses (homogeneousEntropy CB1_5_2I1R0Value) := by
  exact contains_sound (homogeneous_enclosed CB1_5_2I1R0Value CB1_5_2I1R0MassTerm_sound CB1_5_2I1R0Entropy_sound) (by decide +kernel)
lemma CB1_5_2I1R1Raw_sound (a : Fin 6) :
    (CB1_5_2I1R1Raw a).Encloses (CB1_5_2I1R1Value a) := by
  exact residualBall_sound_on (below (shape 1 5 2)) B1_5_2Law (fun u => (stageBLaw (shape 1 5 2) u : ℝ)) (stageBPriority (shape 1 5 2)) 1 (fun u => B1_5_2Little u ((stageBPriority (shape 1 5 2)) 1)) (fun u a => (littleLaw (shape 1 5 2) u ((stageBPriority (shape 1 5 2)) 1) a : ℝ)) (fun u _ => B1_5_2Law_sound u) (fun u _ a => B1_5_2Little_sound u ((stageBPriority (shape 1 5 2)) 1) a) 1 a
lemma CB1_5_2I1R1Certificates_valid :
    CB1_5_2I1R1Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
lemma CB1_5_2I1R1P_check : ∀ a : Fin 6, contains (CB1_5_2I1R1Raw a) (CB1_5_2I1R1P a) = true := by
  decide +kernel
lemma CB1_5_2I1R1P_sound (a : Fin 6) :
    (CB1_5_2I1R1P a).Encloses (CB1_5_2I1R1Value a) :=
  contains_sound (CB1_5_2I1R1Raw_sound a) (CB1_5_2I1R1P_check a)
lemma CB1_5_2I1R1Terms_sound (a : Fin 6) :
    (CB1_5_2I1R1Terms a).Encloses (Foundation.entropyTerm (CB1_5_2I1R1Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB1_5_2I1R1Certificates_valid
    (CB1_5_2I1R1CertificateIndex a) (CB1_5_2I1R1P_sound a)
lemma CB1_5_2I1R1Entropy_sound : CB1_5_2I1R1Entropy.Encloses (Foundation.finiteEntropy CB1_5_2I1R1Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB1_5_2I1R1Value CB1_5_2I1R1Terms CB1_5_2I1R1Terms_sound) (by decide +kernel)
lemma CB1_5_2I1R1Mass_sound : CB1_5_2I1R1Mass.Encloses (∑ a, CB1_5_2I1R1Value a) := by
  exact contains_sound (finSumBall_sound 6 CB1_5_2I1R1P CB1_5_2I1R1Value CB1_5_2I1R1P_sound) (by decide +kernel)
lemma CB1_5_2I1R1MassTermLog_sound : CB1_5_2I1R1MassTermLog.Encloses (Real.log ((∑ a, CB1_5_2I1R1Value a))) := by
  exact checkLog_sound logTwoBall_sound (CB1_5_2I1R1Mass_sound) (w := CB1_5_2I1R1MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
lemma CB1_5_2I1R1MassTerm_sound : CB1_5_2I1R1MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB1_5_2I1R1Value a))) := by
  exact contains_sound (entropyTerm_ball (CB1_5_2I1R1Mass_sound) CB1_5_2I1R1MassTermLog_sound) (by decide +kernel)
lemma CB1_5_2I1R1H_sound : CB1_5_2I1R1H.Encloses (homogeneousEntropy CB1_5_2I1R1Value) := by
  exact contains_sound (homogeneous_enclosed CB1_5_2I1R1Value CB1_5_2I1R1MassTerm_sound CB1_5_2I1R1Entropy_sound) (by decide +kernel)
lemma CB1_5_2I1R2Raw_sound (a : Fin 6) :
    (CB1_5_2I1R2Raw a).Encloses (CB1_5_2I1R2Value a) := by
  exact residualBall_sound_on (below (shape 1 5 2)) B1_5_2Law (fun u => (stageBLaw (shape 1 5 2) u : ℝ)) (stageBPriority (shape 1 5 2)) 1 (fun u => B1_5_2Little u ((stageBPriority (shape 1 5 2)) 1)) (fun u a => (littleLaw (shape 1 5 2) u ((stageBPriority (shape 1 5 2)) 1) a : ℝ)) (fun u _ => B1_5_2Law_sound u) (fun u _ a => B1_5_2Little_sound u ((stageBPriority (shape 1 5 2)) 1) a) 2 a
lemma CB1_5_2I1R2Certificates_valid :
    CB1_5_2I1R2Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
lemma CB1_5_2I1R2P_check : ∀ a : Fin 6, contains (CB1_5_2I1R2Raw a) (CB1_5_2I1R2P a) = true := by
  decide +kernel
lemma CB1_5_2I1R2P_sound (a : Fin 6) :
    (CB1_5_2I1R2P a).Encloses (CB1_5_2I1R2Value a) :=
  contains_sound (CB1_5_2I1R2Raw_sound a) (CB1_5_2I1R2P_check a)
lemma CB1_5_2I1R2Terms_sound (a : Fin 6) :
    (CB1_5_2I1R2Terms a).Encloses (Foundation.entropyTerm (CB1_5_2I1R2Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB1_5_2I1R2Certificates_valid
    (CB1_5_2I1R2CertificateIndex a) (CB1_5_2I1R2P_sound a)
lemma CB1_5_2I1R2Entropy_sound : CB1_5_2I1R2Entropy.Encloses (Foundation.finiteEntropy CB1_5_2I1R2Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB1_5_2I1R2Value CB1_5_2I1R2Terms CB1_5_2I1R2Terms_sound) (by decide +kernel)
lemma CB1_5_2I1R2Mass_sound : CB1_5_2I1R2Mass.Encloses (∑ a, CB1_5_2I1R2Value a) := by
  exact contains_sound (finSumBall_sound 6 CB1_5_2I1R2P CB1_5_2I1R2Value CB1_5_2I1R2P_sound) (by decide +kernel)
lemma CB1_5_2I1R2MassTermLog_sound : CB1_5_2I1R2MassTermLog.Encloses (Real.log ((∑ a, CB1_5_2I1R2Value a))) := by
  exact checkLog_sound logTwoBall_sound (CB1_5_2I1R2Mass_sound) (w := CB1_5_2I1R2MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
lemma CB1_5_2I1R2MassTerm_sound : CB1_5_2I1R2MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB1_5_2I1R2Value a))) := by
  exact contains_sound (entropyTerm_ball (CB1_5_2I1R2Mass_sound) CB1_5_2I1R2MassTermLog_sound) (by decide +kernel)
lemma CB1_5_2I1R2H_sound : CB1_5_2I1R2H.Encloses (homogeneousEntropy CB1_5_2I1R2Value) := by
  exact contains_sound (homogeneous_enclosed CB1_5_2I1R2Value CB1_5_2I1R2MassTerm_sound CB1_5_2I1R2Entropy_sound) (by decide +kernel)
lemma CB1_5_2I1R3Raw_sound (a : Fin 6) :
    (CB1_5_2I1R3Raw a).Encloses (CB1_5_2I1R3Value a) := by
  exact residualBall_sound_on (below (shape 1 5 2)) B1_5_2Law (fun u => (stageBLaw (shape 1 5 2) u : ℝ)) (stageBPriority (shape 1 5 2)) 1 (fun u => B1_5_2Little u ((stageBPriority (shape 1 5 2)) 1)) (fun u a => (littleLaw (shape 1 5 2) u ((stageBPriority (shape 1 5 2)) 1) a : ℝ)) (fun u _ => B1_5_2Law_sound u) (fun u _ a => B1_5_2Little_sound u ((stageBPriority (shape 1 5 2)) 1) a) 3 a
lemma CB1_5_2I1R3Certificates_valid :
    CB1_5_2I1R3Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
lemma CB1_5_2I1R3P_check : ∀ a : Fin 6, contains (CB1_5_2I1R3Raw a) (CB1_5_2I1R3P a) = true := by
  decide +kernel
lemma CB1_5_2I1R3P_sound (a : Fin 6) :
    (CB1_5_2I1R3P a).Encloses (CB1_5_2I1R3Value a) :=
  contains_sound (CB1_5_2I1R3Raw_sound a) (CB1_5_2I1R3P_check a)
lemma CB1_5_2I1R3Terms_sound (a : Fin 6) :
    (CB1_5_2I1R3Terms a).Encloses (Foundation.entropyTerm (CB1_5_2I1R3Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB1_5_2I1R3Certificates_valid
    (CB1_5_2I1R3CertificateIndex a) (CB1_5_2I1R3P_sound a)
lemma CB1_5_2I1R3Entropy_sound : CB1_5_2I1R3Entropy.Encloses (Foundation.finiteEntropy CB1_5_2I1R3Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB1_5_2I1R3Value CB1_5_2I1R3Terms CB1_5_2I1R3Terms_sound) (by decide +kernel)
lemma CB1_5_2I1R3Mass_sound : CB1_5_2I1R3Mass.Encloses (∑ a, CB1_5_2I1R3Value a) := by
  exact contains_sound (finSumBall_sound 6 CB1_5_2I1R3P CB1_5_2I1R3Value CB1_5_2I1R3P_sound) (by decide +kernel)
lemma CB1_5_2I1R3MassTerm_sound : CB1_5_2I1R3MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB1_5_2I1R3Value a))) :=
  entropyTerm_zero_ball (CB1_5_2I1R3Mass_sound)
lemma CB1_5_2I1R3H_sound : CB1_5_2I1R3H.Encloses (homogeneousEntropy CB1_5_2I1R3Value) := by
  exact contains_sound (homogeneous_enclosed CB1_5_2I1R3Value CB1_5_2I1R3MassTerm_sound CB1_5_2I1R3Entropy_sound) (by decide +kernel)
lemma CB1_5_2I1R4Raw_sound (a : Fin 6) :
    (CB1_5_2I1R4Raw a).Encloses (CB1_5_2I1R4Value a) := by
  exact residualBall_sound_on (below (shape 1 5 2)) B1_5_2Law (fun u => (stageBLaw (shape 1 5 2) u : ℝ)) (stageBPriority (shape 1 5 2)) 1 (fun u => B1_5_2Little u ((stageBPriority (shape 1 5 2)) 1)) (fun u a => (littleLaw (shape 1 5 2) u ((stageBPriority (shape 1 5 2)) 1) a : ℝ)) (fun u _ => B1_5_2Law_sound u) (fun u _ a => B1_5_2Little_sound u ((stageBPriority (shape 1 5 2)) 1) a) 4 a
lemma CB1_5_2I1R4Certificates_valid :
    CB1_5_2I1R4Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
lemma CB1_5_2I1R4P_check : ∀ a : Fin 6, contains (CB1_5_2I1R4Raw a) (CB1_5_2I1R4P a) = true := by
  decide +kernel
lemma CB1_5_2I1R4P_sound (a : Fin 6) :
    (CB1_5_2I1R4P a).Encloses (CB1_5_2I1R4Value a) :=
  contains_sound (CB1_5_2I1R4Raw_sound a) (CB1_5_2I1R4P_check a)
lemma CB1_5_2I1R4Terms_sound (a : Fin 6) :
    (CB1_5_2I1R4Terms a).Encloses (Foundation.entropyTerm (CB1_5_2I1R4Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB1_5_2I1R4Certificates_valid
    (CB1_5_2I1R4CertificateIndex a) (CB1_5_2I1R4P_sound a)
lemma CB1_5_2I1R4Entropy_sound : CB1_5_2I1R4Entropy.Encloses (Foundation.finiteEntropy CB1_5_2I1R4Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB1_5_2I1R4Value CB1_5_2I1R4Terms CB1_5_2I1R4Terms_sound) (by decide +kernel)
lemma CB1_5_2I1R4Mass_sound : CB1_5_2I1R4Mass.Encloses (∑ a, CB1_5_2I1R4Value a) := by
  exact contains_sound (finSumBall_sound 6 CB1_5_2I1R4P CB1_5_2I1R4Value CB1_5_2I1R4P_sound) (by decide +kernel)
lemma CB1_5_2I1R4MassTerm_sound : CB1_5_2I1R4MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB1_5_2I1R4Value a))) :=
  entropyTerm_zero_ball (CB1_5_2I1R4Mass_sound)
lemma CB1_5_2I1R4H_sound : CB1_5_2I1R4H.Encloses (homogeneousEntropy CB1_5_2I1R4Value) := by
  exact contains_sound (homogeneous_enclosed CB1_5_2I1R4Value CB1_5_2I1R4MassTerm_sound CB1_5_2I1R4Entropy_sound) (by decide +kernel)
lemma CB1_5_2I1R5Raw_sound (a : Fin 6) :
    (CB1_5_2I1R5Raw a).Encloses (CB1_5_2I1R5Value a) := by
  exact residualBall_sound_on (below (shape 1 5 2)) B1_5_2Law (fun u => (stageBLaw (shape 1 5 2) u : ℝ)) (stageBPriority (shape 1 5 2)) 1 (fun u => B1_5_2Little u ((stageBPriority (shape 1 5 2)) 1)) (fun u a => (littleLaw (shape 1 5 2) u ((stageBPriority (shape 1 5 2)) 1) a : ℝ)) (fun u _ => B1_5_2Law_sound u) (fun u _ a => B1_5_2Little_sound u ((stageBPriority (shape 1 5 2)) 1) a) 5 a
lemma CB1_5_2I1R5Certificates_valid :
    CB1_5_2I1R5Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
lemma CB1_5_2I1R5P_check : ∀ a : Fin 6, contains (CB1_5_2I1R5Raw a) (CB1_5_2I1R5P a) = true := by
  decide +kernel
lemma CB1_5_2I1R5P_sound (a : Fin 6) :
    (CB1_5_2I1R5P a).Encloses (CB1_5_2I1R5Value a) :=
  contains_sound (CB1_5_2I1R5Raw_sound a) (CB1_5_2I1R5P_check a)
lemma CB1_5_2I1R5Terms_sound (a : Fin 6) :
    (CB1_5_2I1R5Terms a).Encloses (Foundation.entropyTerm (CB1_5_2I1R5Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB1_5_2I1R5Certificates_valid
    (CB1_5_2I1R5CertificateIndex a) (CB1_5_2I1R5P_sound a)
lemma CB1_5_2I1R5Entropy_sound : CB1_5_2I1R5Entropy.Encloses (Foundation.finiteEntropy CB1_5_2I1R5Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB1_5_2I1R5Value CB1_5_2I1R5Terms CB1_5_2I1R5Terms_sound) (by decide +kernel)
lemma CB1_5_2I1R5Mass_sound : CB1_5_2I1R5Mass.Encloses (∑ a, CB1_5_2I1R5Value a) := by
  exact contains_sound (finSumBall_sound 6 CB1_5_2I1R5P CB1_5_2I1R5Value CB1_5_2I1R5P_sound) (by decide +kernel)
lemma CB1_5_2I1R5MassTerm_sound : CB1_5_2I1R5MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB1_5_2I1R5Value a))) :=
  entropyTerm_zero_ball (CB1_5_2I1R5Mass_sound)
lemma CB1_5_2I1R5H_sound : CB1_5_2I1R5H.Encloses (homogeneousEntropy CB1_5_2I1R5Value) := by
  exact contains_sound (homogeneous_enclosed CB1_5_2I1R5Value CB1_5_2I1R5MassTerm_sound CB1_5_2I1R5Entropy_sound) (by decide +kernel)
lemma CB1_5_2I1R6Raw_sound (a : Fin 6) :
    (CB1_5_2I1R6Raw a).Encloses (CB1_5_2I1R6Value a) := by
  exact residualBall_sound_on (below (shape 1 5 2)) B1_5_2Law (fun u => (stageBLaw (shape 1 5 2) u : ℝ)) (stageBPriority (shape 1 5 2)) 1 (fun u => B1_5_2Little u ((stageBPriority (shape 1 5 2)) 1)) (fun u a => (littleLaw (shape 1 5 2) u ((stageBPriority (shape 1 5 2)) 1) a : ℝ)) (fun u _ => B1_5_2Law_sound u) (fun u _ a => B1_5_2Little_sound u ((stageBPriority (shape 1 5 2)) 1) a) 6 a
lemma CB1_5_2I1R6Certificates_valid :
    CB1_5_2I1R6Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
lemma CB1_5_2I1R6P_check : ∀ a : Fin 6, contains (CB1_5_2I1R6Raw a) (CB1_5_2I1R6P a) = true := by
  decide +kernel
lemma CB1_5_2I1R6P_sound (a : Fin 6) :
    (CB1_5_2I1R6P a).Encloses (CB1_5_2I1R6Value a) :=
  contains_sound (CB1_5_2I1R6Raw_sound a) (CB1_5_2I1R6P_check a)
lemma CB1_5_2I1R6Terms_sound (a : Fin 6) :
    (CB1_5_2I1R6Terms a).Encloses (Foundation.entropyTerm (CB1_5_2I1R6Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB1_5_2I1R6Certificates_valid
    (CB1_5_2I1R6CertificateIndex a) (CB1_5_2I1R6P_sound a)
lemma CB1_5_2I1R6Entropy_sound : CB1_5_2I1R6Entropy.Encloses (Foundation.finiteEntropy CB1_5_2I1R6Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB1_5_2I1R6Value CB1_5_2I1R6Terms CB1_5_2I1R6Terms_sound) (by decide +kernel)
lemma CB1_5_2I1R6Mass_sound : CB1_5_2I1R6Mass.Encloses (∑ a, CB1_5_2I1R6Value a) := by
  exact contains_sound (finSumBall_sound 6 CB1_5_2I1R6P CB1_5_2I1R6Value CB1_5_2I1R6P_sound) (by decide +kernel)
lemma CB1_5_2I1R6MassTerm_sound : CB1_5_2I1R6MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB1_5_2I1R6Value a))) :=
  entropyTerm_zero_ball (CB1_5_2I1R6Mass_sound)
lemma CB1_5_2I1R6H_sound : CB1_5_2I1R6H.Encloses (homogeneousEntropy CB1_5_2I1R6Value) := by
  exact contains_sound (homogeneous_enclosed CB1_5_2I1R6Value CB1_5_2I1R6MassTerm_sound CB1_5_2I1R6Entropy_sound) (by decide +kernel)
lemma CB1_5_2I1R7Raw_sound (a : Fin 6) :
    (CB1_5_2I1R7Raw a).Encloses (CB1_5_2I1R7Value a) := by
  exact residualBall_sound_on (below (shape 1 5 2)) B1_5_2Law (fun u => (stageBLaw (shape 1 5 2) u : ℝ)) (stageBPriority (shape 1 5 2)) 1 (fun u => B1_5_2Little u ((stageBPriority (shape 1 5 2)) 1)) (fun u a => (littleLaw (shape 1 5 2) u ((stageBPriority (shape 1 5 2)) 1) a : ℝ)) (fun u _ => B1_5_2Law_sound u) (fun u _ a => B1_5_2Little_sound u ((stageBPriority (shape 1 5 2)) 1) a) 7 a
lemma CB1_5_2I1R7Certificates_valid :
    CB1_5_2I1R7Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
lemma CB1_5_2I1R7P_check : ∀ a : Fin 6, contains (CB1_5_2I1R7Raw a) (CB1_5_2I1R7P a) = true := by
  decide +kernel
lemma CB1_5_2I1R7P_sound (a : Fin 6) :
    (CB1_5_2I1R7P a).Encloses (CB1_5_2I1R7Value a) :=
  contains_sound (CB1_5_2I1R7Raw_sound a) (CB1_5_2I1R7P_check a)
lemma CB1_5_2I1R7Terms_sound (a : Fin 6) :
    (CB1_5_2I1R7Terms a).Encloses (Foundation.entropyTerm (CB1_5_2I1R7Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB1_5_2I1R7Certificates_valid
    (CB1_5_2I1R7CertificateIndex a) (CB1_5_2I1R7P_sound a)
lemma CB1_5_2I1R7Entropy_sound : CB1_5_2I1R7Entropy.Encloses (Foundation.finiteEntropy CB1_5_2I1R7Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB1_5_2I1R7Value CB1_5_2I1R7Terms CB1_5_2I1R7Terms_sound) (by decide +kernel)
lemma CB1_5_2I1R7Mass_sound : CB1_5_2I1R7Mass.Encloses (∑ a, CB1_5_2I1R7Value a) := by
  exact contains_sound (finSumBall_sound 6 CB1_5_2I1R7P CB1_5_2I1R7Value CB1_5_2I1R7P_sound) (by decide +kernel)
lemma CB1_5_2I1R7MassTerm_sound : CB1_5_2I1R7MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB1_5_2I1R7Value a))) :=
  entropyTerm_zero_ball (CB1_5_2I1R7Mass_sound)
lemma CB1_5_2I1R7H_sound : CB1_5_2I1R7H.Encloses (homogeneousEntropy CB1_5_2I1R7Value) := by
  exact contains_sound (homogeneous_enclosed CB1_5_2I1R7Value CB1_5_2I1R7MassTerm_sound CB1_5_2I1R7Entropy_sound) (by decide +kernel)
lemma CB1_5_2I1R8Raw_sound (a : Fin 6) :
    (CB1_5_2I1R8Raw a).Encloses (CB1_5_2I1R8Value a) := by
  exact residualBall_sound_on (below (shape 1 5 2)) B1_5_2Law (fun u => (stageBLaw (shape 1 5 2) u : ℝ)) (stageBPriority (shape 1 5 2)) 1 (fun u => B1_5_2Little u ((stageBPriority (shape 1 5 2)) 1)) (fun u a => (littleLaw (shape 1 5 2) u ((stageBPriority (shape 1 5 2)) 1) a : ℝ)) (fun u _ => B1_5_2Law_sound u) (fun u _ a => B1_5_2Little_sound u ((stageBPriority (shape 1 5 2)) 1) a) 8 a
lemma CB1_5_2I1R8Certificates_valid :
    CB1_5_2I1R8Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
lemma CB1_5_2I1R8P_check : ∀ a : Fin 6, contains (CB1_5_2I1R8Raw a) (CB1_5_2I1R8P a) = true := by
  decide +kernel
lemma CB1_5_2I1R8P_sound (a : Fin 6) :
    (CB1_5_2I1R8P a).Encloses (CB1_5_2I1R8Value a) :=
  contains_sound (CB1_5_2I1R8Raw_sound a) (CB1_5_2I1R8P_check a)
lemma CB1_5_2I1R8Terms_sound (a : Fin 6) :
    (CB1_5_2I1R8Terms a).Encloses (Foundation.entropyTerm (CB1_5_2I1R8Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB1_5_2I1R8Certificates_valid
    (CB1_5_2I1R8CertificateIndex a) (CB1_5_2I1R8P_sound a)
lemma CB1_5_2I1R8Entropy_sound : CB1_5_2I1R8Entropy.Encloses (Foundation.finiteEntropy CB1_5_2I1R8Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB1_5_2I1R8Value CB1_5_2I1R8Terms CB1_5_2I1R8Terms_sound) (by decide +kernel)
lemma CB1_5_2I1R8Mass_sound : CB1_5_2I1R8Mass.Encloses (∑ a, CB1_5_2I1R8Value a) := by
  exact contains_sound (finSumBall_sound 6 CB1_5_2I1R8P CB1_5_2I1R8Value CB1_5_2I1R8P_sound) (by decide +kernel)
lemma CB1_5_2I1R8MassTerm_sound : CB1_5_2I1R8MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB1_5_2I1R8Value a))) :=
  entropyTerm_zero_ball (CB1_5_2I1R8Mass_sound)
lemma CB1_5_2I1R8H_sound : CB1_5_2I1R8H.Encloses (homogeneousEntropy CB1_5_2I1R8Value) := by
  exact contains_sound (homogeneous_enclosed CB1_5_2I1R8Value CB1_5_2I1R8MassTerm_sound CB1_5_2I1R8Entropy_sound) (by decide +kernel)
lemma CB1_5_2I1R9Raw_sound (a : Fin 6) :
    (CB1_5_2I1R9Raw a).Encloses (CB1_5_2I1R9Value a) := by
  exact residualBall_sound_on (below (shape 1 5 2)) B1_5_2Law (fun u => (stageBLaw (shape 1 5 2) u : ℝ)) (stageBPriority (shape 1 5 2)) 1 (fun u => B1_5_2Little u ((stageBPriority (shape 1 5 2)) 1)) (fun u a => (littleLaw (shape 1 5 2) u ((stageBPriority (shape 1 5 2)) 1) a : ℝ)) (fun u _ => B1_5_2Law_sound u) (fun u _ a => B1_5_2Little_sound u ((stageBPriority (shape 1 5 2)) 1) a) 9 a
lemma CB1_5_2I1R9Certificates_valid :
    CB1_5_2I1R9Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
lemma CB1_5_2I1R9P_check : ∀ a : Fin 6, contains (CB1_5_2I1R9Raw a) (CB1_5_2I1R9P a) = true := by
  decide +kernel
lemma CB1_5_2I1R9P_sound (a : Fin 6) :
    (CB1_5_2I1R9P a).Encloses (CB1_5_2I1R9Value a) :=
  contains_sound (CB1_5_2I1R9Raw_sound a) (CB1_5_2I1R9P_check a)
lemma CB1_5_2I1R9Terms_sound (a : Fin 6) :
    (CB1_5_2I1R9Terms a).Encloses (Foundation.entropyTerm (CB1_5_2I1R9Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB1_5_2I1R9Certificates_valid
    (CB1_5_2I1R9CertificateIndex a) (CB1_5_2I1R9P_sound a)
lemma CB1_5_2I1R9Entropy_sound : CB1_5_2I1R9Entropy.Encloses (Foundation.finiteEntropy CB1_5_2I1R9Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB1_5_2I1R9Value CB1_5_2I1R9Terms CB1_5_2I1R9Terms_sound) (by decide +kernel)
lemma CB1_5_2I1R9Mass_sound : CB1_5_2I1R9Mass.Encloses (∑ a, CB1_5_2I1R9Value a) := by
  exact contains_sound (finSumBall_sound 6 CB1_5_2I1R9P CB1_5_2I1R9Value CB1_5_2I1R9P_sound) (by decide +kernel)
lemma CB1_5_2I1R9MassTerm_sound : CB1_5_2I1R9MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB1_5_2I1R9Value a))) :=
  entropyTerm_zero_ball (CB1_5_2I1R9Mass_sound)
lemma CB1_5_2I1R9H_sound : CB1_5_2I1R9H.Encloses (homogeneousEntropy CB1_5_2I1R9Value) := by
  exact contains_sound (homogeneous_enclosed CB1_5_2I1R9Value CB1_5_2I1R9MassTerm_sound CB1_5_2I1R9Entropy_sound) (by decide +kernel)
lemma CB1_5_2I1R10Raw_sound (a : Fin 6) :
    (CB1_5_2I1R10Raw a).Encloses (CB1_5_2I1R10Value a) := by
  exact residualBall_sound_on (below (shape 1 5 2)) B1_5_2Law (fun u => (stageBLaw (shape 1 5 2) u : ℝ)) (stageBPriority (shape 1 5 2)) 1 (fun u => B1_5_2Little u ((stageBPriority (shape 1 5 2)) 1)) (fun u a => (littleLaw (shape 1 5 2) u ((stageBPriority (shape 1 5 2)) 1) a : ℝ)) (fun u _ => B1_5_2Law_sound u) (fun u _ a => B1_5_2Little_sound u ((stageBPriority (shape 1 5 2)) 1) a) 10 a
lemma CB1_5_2I1R10Certificates_valid :
    CB1_5_2I1R10Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
lemma CB1_5_2I1R10P_check : ∀ a : Fin 6, contains (CB1_5_2I1R10Raw a) (CB1_5_2I1R10P a) = true := by
  decide +kernel
lemma CB1_5_2I1R10P_sound (a : Fin 6) :
    (CB1_5_2I1R10P a).Encloses (CB1_5_2I1R10Value a) :=
  contains_sound (CB1_5_2I1R10Raw_sound a) (CB1_5_2I1R10P_check a)
lemma CB1_5_2I1R10Terms_sound (a : Fin 6) :
    (CB1_5_2I1R10Terms a).Encloses (Foundation.entropyTerm (CB1_5_2I1R10Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB1_5_2I1R10Certificates_valid
    (CB1_5_2I1R10CertificateIndex a) (CB1_5_2I1R10P_sound a)
lemma CB1_5_2I1R10Entropy_sound : CB1_5_2I1R10Entropy.Encloses (Foundation.finiteEntropy CB1_5_2I1R10Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB1_5_2I1R10Value CB1_5_2I1R10Terms CB1_5_2I1R10Terms_sound) (by decide +kernel)
lemma CB1_5_2I1R10Mass_sound : CB1_5_2I1R10Mass.Encloses (∑ a, CB1_5_2I1R10Value a) := by
  exact contains_sound (finSumBall_sound 6 CB1_5_2I1R10P CB1_5_2I1R10Value CB1_5_2I1R10P_sound) (by decide +kernel)
lemma CB1_5_2I1R10MassTerm_sound : CB1_5_2I1R10MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB1_5_2I1R10Value a))) :=
  entropyTerm_zero_ball (CB1_5_2I1R10Mass_sound)
lemma CB1_5_2I1R10H_sound : CB1_5_2I1R10H.Encloses (homogeneousEntropy CB1_5_2I1R10Value) := by
  exact contains_sound (homogeneous_enclosed CB1_5_2I1R10Value CB1_5_2I1R10MassTerm_sound CB1_5_2I1R10Entropy_sound) (by decide +kernel)
lemma CB1_5_2I1R11Raw_sound (a : Fin 6) :
    (CB1_5_2I1R11Raw a).Encloses (CB1_5_2I1R11Value a) := by
  exact residualBall_sound_on (below (shape 1 5 2)) B1_5_2Law (fun u => (stageBLaw (shape 1 5 2) u : ℝ)) (stageBPriority (shape 1 5 2)) 1 (fun u => B1_5_2Little u ((stageBPriority (shape 1 5 2)) 1)) (fun u a => (littleLaw (shape 1 5 2) u ((stageBPriority (shape 1 5 2)) 1) a : ℝ)) (fun u _ => B1_5_2Law_sound u) (fun u _ a => B1_5_2Little_sound u ((stageBPriority (shape 1 5 2)) 1) a) 11 a
lemma CB1_5_2I1R11Certificates_valid :
    CB1_5_2I1R11Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
lemma CB1_5_2I1R11P_check : ∀ a : Fin 6, contains (CB1_5_2I1R11Raw a) (CB1_5_2I1R11P a) = true := by
  decide +kernel
lemma CB1_5_2I1R11P_sound (a : Fin 6) :
    (CB1_5_2I1R11P a).Encloses (CB1_5_2I1R11Value a) :=
  contains_sound (CB1_5_2I1R11Raw_sound a) (CB1_5_2I1R11P_check a)
lemma CB1_5_2I1R11Terms_sound (a : Fin 6) :
    (CB1_5_2I1R11Terms a).Encloses (Foundation.entropyTerm (CB1_5_2I1R11Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB1_5_2I1R11Certificates_valid
    (CB1_5_2I1R11CertificateIndex a) (CB1_5_2I1R11P_sound a)
lemma CB1_5_2I1R11Entropy_sound : CB1_5_2I1R11Entropy.Encloses (Foundation.finiteEntropy CB1_5_2I1R11Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB1_5_2I1R11Value CB1_5_2I1R11Terms CB1_5_2I1R11Terms_sound) (by decide +kernel)
lemma CB1_5_2I1R11Mass_sound : CB1_5_2I1R11Mass.Encloses (∑ a, CB1_5_2I1R11Value a) := by
  exact contains_sound (finSumBall_sound 6 CB1_5_2I1R11P CB1_5_2I1R11Value CB1_5_2I1R11P_sound) (by decide +kernel)
lemma CB1_5_2I1R11MassTerm_sound : CB1_5_2I1R11MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB1_5_2I1R11Value a))) :=
  entropyTerm_zero_ball (CB1_5_2I1R11Mass_sound)
lemma CB1_5_2I1R11H_sound : CB1_5_2I1R11H.Encloses (homogeneousEntropy CB1_5_2I1R11Value) := by
  exact contains_sound (homogeneous_enclosed CB1_5_2I1R11Value CB1_5_2I1R11MassTerm_sound CB1_5_2I1R11Entropy_sound) (by decide +kernel)
lemma CB1_5_2I1R12Raw_sound (a : Fin 6) :
    (CB1_5_2I1R12Raw a).Encloses (CB1_5_2I1R12Value a) := by
  exact residualBall_sound_on (below (shape 1 5 2)) B1_5_2Law (fun u => (stageBLaw (shape 1 5 2) u : ℝ)) (stageBPriority (shape 1 5 2)) 1 (fun u => B1_5_2Little u ((stageBPriority (shape 1 5 2)) 1)) (fun u a => (littleLaw (shape 1 5 2) u ((stageBPriority (shape 1 5 2)) 1) a : ℝ)) (fun u _ => B1_5_2Law_sound u) (fun u _ a => B1_5_2Little_sound u ((stageBPriority (shape 1 5 2)) 1) a) 12 a
lemma CB1_5_2I1R12Certificates_valid :
    CB1_5_2I1R12Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
lemma CB1_5_2I1R12P_check : ∀ a : Fin 6, contains (CB1_5_2I1R12Raw a) (CB1_5_2I1R12P a) = true := by
  decide +kernel
lemma CB1_5_2I1R12P_sound (a : Fin 6) :
    (CB1_5_2I1R12P a).Encloses (CB1_5_2I1R12Value a) :=
  contains_sound (CB1_5_2I1R12Raw_sound a) (CB1_5_2I1R12P_check a)
lemma CB1_5_2I1R12Terms_sound (a : Fin 6) :
    (CB1_5_2I1R12Terms a).Encloses (Foundation.entropyTerm (CB1_5_2I1R12Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB1_5_2I1R12Certificates_valid
    (CB1_5_2I1R12CertificateIndex a) (CB1_5_2I1R12P_sound a)
lemma CB1_5_2I1R12Entropy_sound : CB1_5_2I1R12Entropy.Encloses (Foundation.finiteEntropy CB1_5_2I1R12Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB1_5_2I1R12Value CB1_5_2I1R12Terms CB1_5_2I1R12Terms_sound) (by decide +kernel)
lemma CB1_5_2I1R12Mass_sound : CB1_5_2I1R12Mass.Encloses (∑ a, CB1_5_2I1R12Value a) := by
  exact contains_sound (finSumBall_sound 6 CB1_5_2I1R12P CB1_5_2I1R12Value CB1_5_2I1R12P_sound) (by decide +kernel)
lemma CB1_5_2I1R12MassTerm_sound : CB1_5_2I1R12MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB1_5_2I1R12Value a))) :=
  entropyTerm_zero_ball (CB1_5_2I1R12Mass_sound)
lemma CB1_5_2I1R12H_sound : CB1_5_2I1R12H.Encloses (homogeneousEntropy CB1_5_2I1R12Value) := by
  exact contains_sound (homogeneous_enclosed CB1_5_2I1R12Value CB1_5_2I1R12MassTerm_sound CB1_5_2I1R12Entropy_sound) (by decide +kernel)
lemma CB1_5_2I1R13Raw_sound (a : Fin 6) :
    (CB1_5_2I1R13Raw a).Encloses (CB1_5_2I1R13Value a) := by
  exact residualBall_sound_on (below (shape 1 5 2)) B1_5_2Law (fun u => (stageBLaw (shape 1 5 2) u : ℝ)) (stageBPriority (shape 1 5 2)) 1 (fun u => B1_5_2Little u ((stageBPriority (shape 1 5 2)) 1)) (fun u a => (littleLaw (shape 1 5 2) u ((stageBPriority (shape 1 5 2)) 1) a : ℝ)) (fun u _ => B1_5_2Law_sound u) (fun u _ a => B1_5_2Little_sound u ((stageBPriority (shape 1 5 2)) 1) a) 13 a
lemma CB1_5_2I1R13Certificates_valid :
    CB1_5_2I1R13Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
lemma CB1_5_2I1R13P_check : ∀ a : Fin 6, contains (CB1_5_2I1R13Raw a) (CB1_5_2I1R13P a) = true := by
  decide +kernel
lemma CB1_5_2I1R13P_sound (a : Fin 6) :
    (CB1_5_2I1R13P a).Encloses (CB1_5_2I1R13Value a) :=
  contains_sound (CB1_5_2I1R13Raw_sound a) (CB1_5_2I1R13P_check a)
lemma CB1_5_2I1R13Terms_sound (a : Fin 6) :
    (CB1_5_2I1R13Terms a).Encloses (Foundation.entropyTerm (CB1_5_2I1R13Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB1_5_2I1R13Certificates_valid
    (CB1_5_2I1R13CertificateIndex a) (CB1_5_2I1R13P_sound a)
lemma CB1_5_2I1R13Entropy_sound : CB1_5_2I1R13Entropy.Encloses (Foundation.finiteEntropy CB1_5_2I1R13Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB1_5_2I1R13Value CB1_5_2I1R13Terms CB1_5_2I1R13Terms_sound) (by decide +kernel)
lemma CB1_5_2I1R13Mass_sound : CB1_5_2I1R13Mass.Encloses (∑ a, CB1_5_2I1R13Value a) := by
  exact contains_sound (finSumBall_sound 6 CB1_5_2I1R13P CB1_5_2I1R13Value CB1_5_2I1R13P_sound) (by decide +kernel)
lemma CB1_5_2I1R13MassTerm_sound : CB1_5_2I1R13MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB1_5_2I1R13Value a))) :=
  entropyTerm_zero_ball (CB1_5_2I1R13Mass_sound)
lemma CB1_5_2I1R13H_sound : CB1_5_2I1R13H.Encloses (homogeneousEntropy CB1_5_2I1R13Value) := by
  exact contains_sound (homogeneous_enclosed CB1_5_2I1R13Value CB1_5_2I1R13MassTerm_sound CB1_5_2I1R13Entropy_sound) (by decide +kernel)
lemma CB1_5_2I1R14Raw_sound (a : Fin 6) :
    (CB1_5_2I1R14Raw a).Encloses (CB1_5_2I1R14Value a) := by
  exact residualBall_sound_on (below (shape 1 5 2)) B1_5_2Law (fun u => (stageBLaw (shape 1 5 2) u : ℝ)) (stageBPriority (shape 1 5 2)) 1 (fun u => B1_5_2Little u ((stageBPriority (shape 1 5 2)) 1)) (fun u a => (littleLaw (shape 1 5 2) u ((stageBPriority (shape 1 5 2)) 1) a : ℝ)) (fun u _ => B1_5_2Law_sound u) (fun u _ a => B1_5_2Little_sound u ((stageBPriority (shape 1 5 2)) 1) a) 14 a
lemma CB1_5_2I1R14Certificates_valid :
    CB1_5_2I1R14Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
lemma CB1_5_2I1R14P_check : ∀ a : Fin 6, contains (CB1_5_2I1R14Raw a) (CB1_5_2I1R14P a) = true := by
  decide +kernel
lemma CB1_5_2I1R14P_sound (a : Fin 6) :
    (CB1_5_2I1R14P a).Encloses (CB1_5_2I1R14Value a) :=
  contains_sound (CB1_5_2I1R14Raw_sound a) (CB1_5_2I1R14P_check a)
lemma CB1_5_2I1R14Terms_sound (a : Fin 6) :
    (CB1_5_2I1R14Terms a).Encloses (Foundation.entropyTerm (CB1_5_2I1R14Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB1_5_2I1R14Certificates_valid
    (CB1_5_2I1R14CertificateIndex a) (CB1_5_2I1R14P_sound a)
lemma CB1_5_2I1R14Entropy_sound : CB1_5_2I1R14Entropy.Encloses (Foundation.finiteEntropy CB1_5_2I1R14Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB1_5_2I1R14Value CB1_5_2I1R14Terms CB1_5_2I1R14Terms_sound) (by decide +kernel)
lemma CB1_5_2I1R14Mass_sound : CB1_5_2I1R14Mass.Encloses (∑ a, CB1_5_2I1R14Value a) := by
  exact contains_sound (finSumBall_sound 6 CB1_5_2I1R14P CB1_5_2I1R14Value CB1_5_2I1R14P_sound) (by decide +kernel)
lemma CB1_5_2I1R14MassTerm_sound : CB1_5_2I1R14MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB1_5_2I1R14Value a))) :=
  entropyTerm_zero_ball (CB1_5_2I1R14Mass_sound)
lemma CB1_5_2I1R14H_sound : CB1_5_2I1R14H.Encloses (homogeneousEntropy CB1_5_2I1R14Value) := by
  exact contains_sound (homogeneous_enclosed CB1_5_2I1R14Value CB1_5_2I1R14MassTerm_sound CB1_5_2I1R14Entropy_sound) (by decide +kernel)
lemma CB1_5_2I1R15Raw_sound (a : Fin 6) :
    (CB1_5_2I1R15Raw a).Encloses (CB1_5_2I1R15Value a) := by
  exact residualBall_sound_on (below (shape 1 5 2)) B1_5_2Law (fun u => (stageBLaw (shape 1 5 2) u : ℝ)) (stageBPriority (shape 1 5 2)) 1 (fun u => B1_5_2Little u ((stageBPriority (shape 1 5 2)) 1)) (fun u a => (littleLaw (shape 1 5 2) u ((stageBPriority (shape 1 5 2)) 1) a : ℝ)) (fun u _ => B1_5_2Law_sound u) (fun u _ a => B1_5_2Little_sound u ((stageBPriority (shape 1 5 2)) 1) a) 15 a
lemma CB1_5_2I1R15Certificates_valid :
    CB1_5_2I1R15Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
lemma CB1_5_2I1R15P_check : ∀ a : Fin 6, contains (CB1_5_2I1R15Raw a) (CB1_5_2I1R15P a) = true := by
  decide +kernel
lemma CB1_5_2I1R15P_sound (a : Fin 6) :
    (CB1_5_2I1R15P a).Encloses (CB1_5_2I1R15Value a) :=
  contains_sound (CB1_5_2I1R15Raw_sound a) (CB1_5_2I1R15P_check a)
lemma CB1_5_2I1R15Terms_sound (a : Fin 6) :
    (CB1_5_2I1R15Terms a).Encloses (Foundation.entropyTerm (CB1_5_2I1R15Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB1_5_2I1R15Certificates_valid
    (CB1_5_2I1R15CertificateIndex a) (CB1_5_2I1R15P_sound a)
lemma CB1_5_2I1R15Entropy_sound : CB1_5_2I1R15Entropy.Encloses (Foundation.finiteEntropy CB1_5_2I1R15Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB1_5_2I1R15Value CB1_5_2I1R15Terms CB1_5_2I1R15Terms_sound) (by decide +kernel)
lemma CB1_5_2I1R15Mass_sound : CB1_5_2I1R15Mass.Encloses (∑ a, CB1_5_2I1R15Value a) := by
  exact contains_sound (finSumBall_sound 6 CB1_5_2I1R15P CB1_5_2I1R15Value CB1_5_2I1R15P_sound) (by decide +kernel)
lemma CB1_5_2I1R15MassTerm_sound : CB1_5_2I1R15MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB1_5_2I1R15Value a))) :=
  entropyTerm_zero_ball (CB1_5_2I1R15Mass_sound)
lemma CB1_5_2I1R15H_sound : CB1_5_2I1R15H.Encloses (homogeneousEntropy CB1_5_2I1R15Value) := by
  exact contains_sound (homogeneous_enclosed CB1_5_2I1R15Value CB1_5_2I1R15MassTerm_sound CB1_5_2I1R15Entropy_sound) (by decide +kernel)
lemma CB1_5_2I1R16Raw_sound (a : Fin 6) :
    (CB1_5_2I1R16Raw a).Encloses (CB1_5_2I1R16Value a) := by
  exact residualBall_sound_on (below (shape 1 5 2)) B1_5_2Law (fun u => (stageBLaw (shape 1 5 2) u : ℝ)) (stageBPriority (shape 1 5 2)) 1 (fun u => B1_5_2Little u ((stageBPriority (shape 1 5 2)) 1)) (fun u a => (littleLaw (shape 1 5 2) u ((stageBPriority (shape 1 5 2)) 1) a : ℝ)) (fun u _ => B1_5_2Law_sound u) (fun u _ a => B1_5_2Little_sound u ((stageBPriority (shape 1 5 2)) 1) a) 16 a
lemma CB1_5_2I1R16Certificates_valid :
    CB1_5_2I1R16Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
lemma CB1_5_2I1R16P_check : ∀ a : Fin 6, contains (CB1_5_2I1R16Raw a) (CB1_5_2I1R16P a) = true := by
  decide +kernel
lemma CB1_5_2I1R16P_sound (a : Fin 6) :
    (CB1_5_2I1R16P a).Encloses (CB1_5_2I1R16Value a) :=
  contains_sound (CB1_5_2I1R16Raw_sound a) (CB1_5_2I1R16P_check a)
lemma CB1_5_2I1R16Terms_sound (a : Fin 6) :
    (CB1_5_2I1R16Terms a).Encloses (Foundation.entropyTerm (CB1_5_2I1R16Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB1_5_2I1R16Certificates_valid
    (CB1_5_2I1R16CertificateIndex a) (CB1_5_2I1R16P_sound a)
lemma CB1_5_2I1R16Entropy_sound : CB1_5_2I1R16Entropy.Encloses (Foundation.finiteEntropy CB1_5_2I1R16Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB1_5_2I1R16Value CB1_5_2I1R16Terms CB1_5_2I1R16Terms_sound) (by decide +kernel)
lemma CB1_5_2I1R16Mass_sound : CB1_5_2I1R16Mass.Encloses (∑ a, CB1_5_2I1R16Value a) := by
  exact contains_sound (finSumBall_sound 6 CB1_5_2I1R16P CB1_5_2I1R16Value CB1_5_2I1R16P_sound) (by decide +kernel)
lemma CB1_5_2I1R16MassTerm_sound : CB1_5_2I1R16MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB1_5_2I1R16Value a))) :=
  entropyTerm_zero_ball (CB1_5_2I1R16Mass_sound)
lemma CB1_5_2I1R16H_sound : CB1_5_2I1R16H.Encloses (homogeneousEntropy CB1_5_2I1R16Value) := by
  exact contains_sound (homogeneous_enclosed CB1_5_2I1R16Value CB1_5_2I1R16MassTerm_sound CB1_5_2I1R16Entropy_sound) (by decide +kernel)
lemma CB1_5_2I1ResidualEntropies_sound (k : Fin 17) :
    (CB1_5_2I1ResidualEntropies k).Encloses (homogeneousEntropy
      (residualLaw (below (shape 1 5 2)) (fun u => (stageBLaw (shape 1 5 2) u : ℝ)) (stageBPriority (shape 1 5 2)) 1 (fun u a => (littleLaw (shape 1 5 2) u ((stageBPriority (shape 1 5 2)) 1) a : ℝ)) k)) := by
  fin_cases k
  · exact CB1_5_2I1R0H_sound
  · exact CB1_5_2I1R1H_sound
  · exact CB1_5_2I1R2H_sound
  · exact CB1_5_2I1R3H_sound
  · exact CB1_5_2I1R4H_sound
  · exact CB1_5_2I1R5H_sound
  · exact CB1_5_2I1R6H_sound
  · exact CB1_5_2I1R7H_sound
  · exact CB1_5_2I1R8H_sound
  · exact CB1_5_2I1R9H_sound
  · exact CB1_5_2I1R10H_sound
  · exact CB1_5_2I1R11H_sound
  · exact CB1_5_2I1R12H_sound
  · exact CB1_5_2I1R13H_sound
  · exact CB1_5_2I1R14H_sound
  · exact CB1_5_2I1R15H_sound
  · exact CB1_5_2I1R16H_sound
lemma CB1_5_2I1Singles_sound (u : Shape) (hu : u ∈ below (shape 1 5 2))
    (hd : designated (stageBPriority (shape 1 5 2)) 1 u) :
    (CB1_5_2I1Singles u).Encloses (homogeneousEntropy ((fun u a => (littleLaw (shape 1 5 2) u ((stageBPriority (shape 1 5 2)) 1) a : ℝ)) u)) := by
  rw [B1_5_2_below] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl
  · exact (show ¬ designated (stageBPriority (shape 1 5 2)) 1 (shape 0 2 2) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (stageBPriority (shape 1 5 2)) 1 (shape 0 3 1) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (stageBPriority (shape 1 5 2)) 1 (shape 0 4 0) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (stageBPriority (shape 1 5 2)) 1 (shape 1 1 2) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (stageBPriority (shape 1 5 2)) 1 (shape 1 2 1) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (stageBPriority (shape 1 5 2)) 1 (shape 1 3 0) by decide +kernel) hd |>.elim
lemma CB1_5_2I1Singleton_sound : CB1_5_2I1Singleton.Encloses
    (singletonEntropy (below (shape 1 5 2)) (fun u => (stageBLaw (shape 1 5 2) u : ℝ)) (stageBPriority (shape 1 5 2)) 1 (fun u a => (littleLaw (shape 1 5 2) u ((stageBPriority (shape 1 5 2)) 1) a : ℝ))) := by
  exact contains_sound (singletonBall_sound (below (shape 1 5 2)) B1_5_2Law (fun u => (stageBLaw (shape 1 5 2) u : ℝ)) (stageBPriority (shape 1 5 2)) 1
    CB1_5_2I1Singles (fun u a => (littleLaw (shape 1 5 2) u ((stageBPriority (shape 1 5 2)) 1) a : ℝ)) (fun u _ => B1_5_2Law_sound u) CB1_5_2I1Singles_sound) (by decide +kernel)
lemma CB1_5_2I1Group_sound : CB1_5_2I1Group.Encloses
    (groupedEntropy (below (shape 1 5 2)) (fun u => (stageBLaw (shape 1 5 2) u : ℝ)) (stageBPriority (shape 1 5 2)) 1 (fun u a => (littleLaw (shape 1 5 2) u ((stageBPriority (shape 1 5 2)) 1) a : ℝ))) := by
  exact contains_sound (Ball.add_sound CB1_5_2I1Singleton_sound
    (finSumBall_sound 17 CB1_5_2I1ResidualEntropies _ CB1_5_2I1ResidualEntropies_sound)) (by decide +kernel)

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
lemma CB1_5_2I1_sound_oai : CB1_5_2I1H.Encloses (stageBCapacity (shape 1 5 2) 1) := by
  have hb := contains_sound (Ball.add_sound CB1_5_2I1PairH_sound
    (Ball.neg_sound (Ball.mul_sound
      (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2) CB1_5_2I1Group_sound)))
    (show contains (.add CB1_5_2I1PairH (.neg (.mul (.exact 2) CB1_5_2I1Group))) CB1_5_2I1H = true by decide +kernel)
  unfold CB1_5_2I1PairValue at hb
  simpa only [stageBCapacity, nativeCapacity,
    show (1 : Fin 3) ≠ 0 by decide, ite_false, if_false, sub_eq_add_neg] using hb

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

theorem solution : type_of% @OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB1_5_2I1_sound_oai := @OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB1_5_2I1_sound_oai
