-- Prove2me | solution 1 for MomentComparison.polynomialGrowth
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T11:17:16.111827+00:00
-- url     : https://prove2.me/submissions/f5f061c4-b7d4-4463-8cf6-d9dcacfb091a

module
public import Mathlib.Analysis.Complex.AbsMax
public import Mathlib.Analysis.Complex.RemovableSingularity
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Definitions.Def_MomentComparison_Lens
public import Definitions.Def_MomentComparison_ComplexPower
public import Definitions.Def_MomentComparison_LensAngle
public import Definitions.Def_MomentComparison_LensEvaluation
public import Mathlib.Algebra.Polynomial.Eval.Degree
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Definitions.Def_MomentComparison_Conformal
public import Theorems.Thm_MomentComparison_polynomialGrowth_of_disk
public import Theorems.Thm_MomentComparison_arg_cpow_ofReal
public import Theorems.Thm_MomentComparison_cpow_div_of_arg_sub
public import Theorems.Thm_MomentComparison_inverse_disk_at_one_of_p
public import Theorems.Thm_MomentComparison_lensParameters

section
public section
open scoped BigOperators
open Set Metric
namespace MomentComparison
private lemma re_diskPlus_nonneg {t : ℂ} (ht : t ∈ closedBall 0 1) : 0 ≤ (1 + t).re := by
  have hn := mem_closedBall_zero_iff.mp ht
  have habs := abs_le.mp ((Complex.abs_re_le_norm t).trans hn)
  simpa using (show 0 ≤ 1 + t.re by linarith)
private lemma re_diskMinus_nonneg {t : ℂ} (ht : t ∈ closedBall 0 1) : 0 ≤ (1 - t).re := by
  have hn := mem_closedBall_zero_iff.mp ht
  have habs := abs_le.mp ((Complex.abs_re_le_norm t).trans hn)
  simpa using sub_nonneg.mpr habs.2
private lemma re_diskPlus_pos {t : ℂ} (ht : t ∈ ball 0 1) : 0 < (1 + t).re := by
  have hn := mem_ball_zero_iff.mp ht
  have habs := abs_lt.mp ((Complex.abs_re_le_norm t).trans_lt hn)
  simpa using (show 0 < 1 + t.re by linarith)
private lemma re_diskMinus_pos {t : ℂ} (ht : t ∈ ball 0 1) : 0 < (1 - t).re := by
  have hn := mem_ball_zero_iff.mp ht
  have habs := abs_lt.mp ((Complex.abs_re_le_norm t).trans_lt hn)
  simpa using sub_pos.mpr habs.2
private lemma cpow_iterate_of_re_nonneg {β : ℝ} (hb : 0 < β) (hb' : β < 2)
    {z : ℂ} (hz : 0 ≤ z.re) :
    (z ^ (β : ℂ)) ^ ((β⁻¹ : ℝ) : ℂ) = z := by
  have ha := abs_le.mp (Complex.abs_arg_le_pi_div_two_iff.mpr hz)
  have h₁ := mul_le_mul_of_nonneg_right ha.1 hb.le
  have h₂ := mul_le_mul_of_nonneg_right ha.2 hb.le
  have h₃ := mul_lt_mul_of_pos_left hb' (half_pos Real.pi_pos)
  rw [← Complex.cpow_mul]
  · rw [← Complex.ofReal_mul, mul_inv_cancel₀ hb.ne', Complex.ofReal_one, Complex.cpow_one]
  · simp only [Complex.mul_im, Complex.ofReal_im, mul_zero, zero_add, Complex.ofReal_re,
      Complex.log_im]
    linarith
  · simp only [Complex.mul_im, Complex.ofReal_im, mul_zero, zero_add, Complex.ofReal_re,
      Complex.log_im]
    linarith
private lemma diskDenominator_ne_zero {β : ℝ} (hb : 0 < β) (hb' : β < 2)
    {t : ℂ} (ht : t ∈ closedBall 0 1) (ht0 : t ≠ 0) :
    diskDenominator β t ≠ 0 := by
  intro he
  have he' : diskMinus β t = diskPlus β t := sub_eq_zero.mp he
  have hi := congrArg (fun w : ℂ => w ^ ((β⁻¹ : ℝ) : ℂ)) he'
  dsimp [diskMinus, diskPlus] at hi
  rw [cpow_iterate_of_re_nonneg hb hb' (re_diskMinus_nonneg ht),
    cpow_iterate_of_re_nonneg hb hb' (re_diskPlus_nonneg ht)] at hi
  exact ht0 (by linear_combination -hi / 2)
private lemma diffContOnCl_diskPlus {β : ℝ} (hb : 0 < β) :
    DiffContOnCl ℂ (diskPlus β) (ball 0 1) := by
  constructor
  · intro t ht
    have hder := (hasDerivAt_id t).const_add (1 : ℂ)
    exact (hder.cpow_const (c := (β : ℂ)) (Or.inl (re_diskPlus_pos ht))).differentiableAt.differentiableWithinAt
  · intro t ht
    rw [closure_ball _ one_ne_zero] at ht
    have hc := Complex.continuousAt_cpow_const_of_re_pos
      (w := (β : ℂ)) (Or.inl (re_diskPlus_nonneg ht)) (by simpa)
    exact (hc.comp (continuousAt_const.add continuousAt_id)).continuousWithinAt
private lemma diffContOnCl_diskMinus {β : ℝ} (hb : 0 < β) :
    DiffContOnCl ℂ (diskMinus β) (ball 0 1) := by
  constructor
  · intro t ht
    have hder := (hasDerivAt_id t).const_sub (1 : ℂ)
    exact (hder.cpow_const (c := (β : ℂ)) (Or.inl (re_diskMinus_pos ht))).differentiableAt.differentiableWithinAt
  · intro t ht
    rw [closure_ball _ one_ne_zero] at ht
    have hc := Complex.continuousAt_cpow_const_of_re_pos
      (w := (β : ℂ)) (Or.inl (re_diskMinus_nonneg ht)) (by simpa)
    exact (hc.comp (continuousAt_const.sub continuousAt_id)).continuousWithinAt
private lemma hasDerivAt_diskDenominator_zero (β : ℝ) :
    HasDerivAt (diskDenominator β) (-2 * (β : ℂ)) 0 := by
  have ha := ((hasDerivAt_id (0 : ℂ)).const_sub (1 : ℂ)).cpow_const
    (c := (β : ℂ)) (Or.inl (by norm_num))
  have hb := ((hasDerivAt_id (0 : ℂ)).const_add (1 : ℂ)).cpow_const
    (c := (β : ℂ)) (Or.inl (by norm_num))
  have hsub := ha.sub hb
  have hfn : (fun x => (1 - id x) ^ (β : ℂ)) - (fun x => (1 + id x) ^ (β : ℂ)) = diskDenominator β := by
    funext x; rfl
  have hval : (β : ℂ) * (1 - id (0 : ℂ)) ^ ((β : ℂ) - 1) * -1 - (β : ℂ) * (1 + id (0 : ℂ)) ^ ((β : ℂ) - 1) * 1 = -2 * (β : ℂ) := by
    simp; ring
  rw [hfn, hval] at hsub
  exact hsub
private lemma diffContOnCl_dslope_diskDenominator {β : ℝ} (hb : 0 < β) :
    DiffContOnCl ℂ (dslope (diskDenominator β) 0) (ball 0 1) := by
  have h := (diffContOnCl_diskMinus hb).sub (diffContOnCl_diskPlus hb)
  constructor
  · exact (Complex.differentiableOn_dslope
      (isOpen_ball.mem_nhds (mem_ball_self zero_lt_one))).2 h.differentiableOn
  · have hnhds := isOpen_ball.mem_nhds (mem_ball_self (x := (0 : ℂ)) zero_lt_one)
    exact (continuousOn_dslope (Filter.mem_of_superset hnhds subset_closure)).2
      ⟨h.continuousOn, (hasDerivAt_diskDenominator_zero β).differentiableAt⟩
private lemma dslope_diskDenominator_ne_zero {β : ℝ} (hb : 0 < β) (hb' : β < 2)
    {t : ℂ} (ht : t ∈ closedBall 0 1) :
    dslope (diskDenominator β) 0 t ≠ 0 := by
  by_cases ht0 : t = 0
  · subst t
    rw [dslope_same, (hasDerivAt_diskDenominator_zero β).deriv]
    exact mul_ne_zero (by norm_num) (by exact_mod_cast hb.ne')
  · rw [dslope_of_ne _ ht0, slope_def_module]
    have h0 : diskDenominator β 0 = 0 := by simp [diskDenominator, diskMinus, diskPlus]
    rw [h0, sub_zero, sub_zero, smul_eq_mul]
    exact mul_ne_zero (inv_ne_zero ht0) (diskDenominator_ne_zero hb hb' ht ht0)
private lemma normalizedInverse_eq {β r : ℝ} {t : ℂ} (ht : t ≠ 0) :
    normalizedInverse β r t / t =
      diskNumerator β t / diskDenominator β t / (Complex.I * (r : ℂ)) := by
  simp only [normalizedInverse, dslope_of_ne _ ht, slope_def_module, sub_zero, smul_eq_mul]
  have h0 : diskDenominator β 0 = 0 := by simp [diskDenominator, diskMinus, diskPlus]
  rw [h0, sub_zero]
  by_cases hr : (r : ℂ) = 0
  · simp [hr]
  by_cases hD : diskDenominator β t = 0
  · simp [hD]
  field_simp [Complex.I_ne_zero]
private lemma diffContOnCl_normalizedInverse {β r : ℝ} (hb : 0 < β) (hb' : β < 2) :
    DiffContOnCl ℂ (normalizedInverse β r) (ball 0 1) := by
  have hN := (diffContOnCl_diskMinus hb).add (diffContOnCl_diskPlus hb)
  have hD := diffContOnCl_dslope_diskDenominator hb
  have hD0 (t : ℂ) (ht : t ∈ closure (ball (0 : ℂ) 1)) :
      dslope (diskDenominator β) 0 t ≠ 0 := by
    rw [closure_ball _ one_ne_zero] at ht
    exact dslope_diskDenominator_ne_zero hb hb' ht
  constructor
  · exact (hN.differentiableOn.div hD.differentiableOn
      (fun t ht => hD0 t (subset_closure ht))).div_const _
  · exact (hN.continuousOn.div hD.continuousOn hD0).div_const _
private lemma norm_le_of_normSq_le {z : ℂ} {a : ℝ} (ha : 0 ≤ a)
    (h : Complex.normSq z ≤ a ^ 2) : ‖z‖ ≤ a := by
  rw [← Complex.sq_norm] at h
  nlinarith [norm_nonneg z]
private lemma inLens_of_rotated_coordinates {p r : ℝ} (hp : 2 < p) (hr : 0 < r)
    (hrs : r ^ 2 = p - 1) {z : ℂ}
    (hz : Complex.normSq z + (p - 2) / r * |z.im| ≤ 1) :
    inLens p (z / (Complex.I * (r : ℂ))) := by
  let k := (p - 2) / (2 * r)
  let a := (p - 2) / (2 * (p - 1))
  let R := p / (2 * (p - 1))
  let iR := Complex.I * (r : ℂ)
  let w := z / iR
  have hk : 0 ≤ k := by dsimp [k]; positivity
  have hR : 0 ≤ R := by dsimp [R]; exact div_nonneg (by linarith) (by linarith)
  have hiR : iR ≠ 0 := mul_ne_zero Complex.I_ne_zero (by exact_mod_cast hr.ne')
  have hri : ‖iR‖ = r := by
    simp [iR, abs_of_pos hr]
  have hAr : a * r = k := by
    dsimp [a, k]
    rw [← hrs]
    field_simp
  have hRR : (r * R) ^ 2 = 1 + k ^ 2 := by
    dsimp [R, k]
    rw [← hrs]
    field_simp
    nlinarith [congrArg (fun x : ℝ => x * (4 * r ^ 2)) hrs,
      congrArg (fun x : ℝ => x * (4 * p)) hrs]
  have hk2 : 2 * k = (p - 2) / r := by dsimp [k]; ring
  have hnorm (v : ℂ) (hv : ‖iR * v‖ ≤ r * R) : ‖v‖ ≤ R := by
    rw [norm_mul, hri] at hv
    exact le_of_mul_le_mul_left hv hr
  change ‖w - (a : ℂ)‖ ≤ R ∧ ‖w + (a : ℂ)‖ ≤ R
  constructor
  · apply hnorm
    have he : iR * (w - (a : ℂ)) = z - Complex.I * (k : ℂ) := by
      rw [mul_sub]
      have hw : iR * w = z := by dsimp [w]; field_simp
      rw [hw]
      simp only [iR, mul_assoc, ← Complex.ofReal_mul, mul_comm r a, hAr]
    rw [he]
    apply norm_le_of_normSq_le (mul_nonneg hr.le hR)
    rw [hRR, Complex.normSq_sub]
    simp only [Complex.normSq_I, one_mul, Complex.normSq_ofReal,
      map_mul, Complex.conj_I, Complex.conj_ofReal, Complex.mul_re, Complex.mul_im,
      Complex.neg_re, Complex.I_re, Complex.I_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, mul_zero, zero_sub, sub_zero, zero_add,
      one_mul, mul_neg, neg_mul, neg_neg]
    have hb := mul_le_mul_of_nonneg_left (neg_le_abs z.im) (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hk)
    rw [← hk2] at hz
    nlinarith [hb]
  · apply hnorm
    have he : iR * (w + (a : ℂ)) = z + Complex.I * (k : ℂ) := by
      rw [mul_add]
      have hw : iR * w = z := by dsimp [w]; field_simp
      rw [hw]
      simp only [iR, mul_assoc, ← Complex.ofReal_mul, mul_comm r a, hAr]
    rw [he]
    apply norm_le_of_normSq_le (mul_nonneg hr.le hR)
    rw [hRR, Complex.normSq_add]
    simp only [Complex.normSq_I, one_mul, Complex.normSq_ofReal,
      map_mul, Complex.conj_I, Complex.conj_ofReal, Complex.mul_re, Complex.mul_im,
      Complex.neg_re, Complex.I_re, Complex.I_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, mul_zero, zero_sub, sub_zero, zero_add,
      one_mul, mul_neg, neg_mul, neg_neg]
    have hb := mul_le_mul_of_nonneg_left (le_abs_self z.im) (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hk)
    rw [← hk2] at hz
    nlinarith [hb]
private lemma rotated_coordinates_of_cayley {ζ : ℂ} (hζ : ζ ≠ 1) {k : ℝ}
    (hz : ζ.re + k * |ζ.im| ≤ 0) :
    let z := ((1 : ℂ) + ζ) / (1 - ζ)
    Complex.normSq z + 2 * k * |z.im| ≤ 1 := by
  let D := Complex.normSq (1 - ζ)
  have hD : 0 < D := Complex.normSq_pos.mpr (sub_ne_zero.mpr hζ.symm)
  have him : (((1 : ℂ) + ζ) / (1 - ζ)).im = 2 * ζ.im / D := by
    rw [Complex.div_im]
    simp only [Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
      Complex.one_re, Complex.one_im, zero_add, zero_sub]
    change ζ.im * (1 - ζ.re) / D - (1 + ζ.re) * (-ζ.im) / D = _
    ring
  change Complex.normSq (((1 : ℂ) + ζ) / (1 - ζ)) + _ ≤ _
  rw [Complex.normSq_div, him, abs_div, abs_of_pos hD, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  change Complex.normSq (1 + ζ) / D + 2 * k * (2 * |ζ.im| / D) ≤ 1
  rw [← mul_div_assoc, ← add_div, div_le_iff₀ hD, one_mul]
  have hs : Complex.normSq (1 + ζ) - D = 4 * ζ.re := by
    dsimp [D]
    simp [Complex.normSq_apply]
    ring
  nlinarith only [hs, hz]
private lemma cayley_re_zero_of_norm_eq_one {t : ℂ} (h : ‖t‖ = 1) :
    (((1 : ℂ) + t) / (1 - t)).re = 0 := by
  rw [Complex.div_re]
  simp only [Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
    Complex.one_re, Complex.one_im, zero_add, zero_sub, ← add_div]
  have he : (1 + t.re) * (1 - t.re) + t.im * -t.im = 0 := by
    have ht := Complex.sq_norm t
    rw [Complex.normSq_apply, h] at ht
    nlinarith
  rw [he, zero_div]
private lemma phase_bound_on_boundary {q : ℂ} (hq : q ≠ 0) (hqr : q.re = 0)
    {β k : ℝ} (hb : 0 < β) (hb' : β < 2)
    (htrig : Real.cos (β * Real.pi / 2) + k * Real.sin (β * Real.pi / 2) = 0) :
    let ζ := q ^ (β : ℂ)
    ζ.re + k * |ζ.im| ≤ 0 := by
  let ζ := q ^ (β : ℂ)
  have hqim : q.im ≠ 0 := by
    intro hi
    exact hq (Complex.ext hqr hi)
  have hζ : ζ ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl hq)
  let a := β * Real.pi / 2
  have ha0 : 0 ≤ a := by dsimp [a]; positivity
  have haπ : a ≤ Real.pi := by
    dsimp [a]
    have := mul_lt_mul_of_pos_right hb' Real.pi_pos
    linarith
  have hsin := Real.sin_nonneg_of_nonneg_of_le_pi ha0 haπ
  have hphase : ζ.arg = a ∨ ζ.arg = -a := by
    have hangle (b : ℝ) (hr : q.arg = b) (h₁ : -Real.pi < b * β) (h₂ : b * β ≤ Real.pi) :
        ζ.arg = b * β := by
      simpa only [ζ, hr] using arg_cpow_ofReal hq (by rwa [hr]) (by rwa [hr])
    rcases lt_or_gt_of_ne hqim with hn | hp
    · have harg := Complex.arg_eq_neg_pi_div_two_iff.mpr ⟨hqr, hn⟩
      right
      calc
        ζ.arg = -(Real.pi / 2) * β :=
          hangle _ harg (by nlinarith [mul_lt_mul_of_pos_right hb' Real.pi_pos]) (by linarith [mul_nonneg (half_pos Real.pi_pos).le hb.le])
        _ = -a := by dsimp [a]; ring
    · have harg := Complex.arg_eq_pi_div_two_iff.mpr ⟨hqr, hp⟩
      left
      calc
        ζ.arg = Real.pi / 2 * β :=
          hangle _ harg (by linarith [mul_nonneg (half_pos Real.pi_pos).le hb.le, Real.pi_pos]) (by nlinarith [mul_lt_mul_of_pos_right hb' Real.pi_pos])
        _ = a := by dsimp [a]; ring
  have hcos : ζ.re = ‖ζ‖ * Real.cos a := by
    have he := (eq_div_iff (norm_ne_zero_iff.mpr hζ)).mp (Complex.cos_arg hζ)
    rcases hphase with h | h <;> rw [h] at he <;> simpa [mul_comm] using he.symm
  have him : |ζ.im| = ‖ζ‖ * Real.sin a := by
    have he := (eq_div_iff (norm_ne_zero_iff.mpr hζ)).mp (Complex.sin_arg ζ)
    rw [← he, abs_mul, abs_norm, mul_comm]
    rcases hphase with h | h <;> simp [h, abs_of_nonneg hsin]
  change ζ.re + k * |ζ.im| ≤ 0
  rw [hcos, him]
  linarith only [congrArg (‖ζ‖ * ·) htrig]
private lemma normalizedInverse_maps_boundary {p r β : ℝ} (hp : 2 < p) (hr : 0 < r)
    (hrs : r ^ 2 = p - 1) (hb : 0 < β) (hb' : β < 2)
    (htrig : Real.cos (β * Real.pi / 2) +
      (p - 2) / (2 * r) * Real.sin (β * Real.pi / 2) = 0)
    {t : ℂ} (ht : t ∈ sphere (0 : ℂ) 1) :
    inLens p (normalizedInverse β r t / t) := by
  have ht' := mem_sphere_zero_iff_norm.mp ht
  have htc := sphere_subset_closedBall ht
  have ht0 : t ≠ 0 := by
    intro h
    simp [h] at ht'
  rw [normalizedInverse_eq ht0]
  apply inLens_of_rotated_coordinates hp hr hrs
  let k := (p - 2) / (2 * r)
  have hk2 : 2 * k = (p - 2) / r := by dsimp [k]; ring
  rw [← hk2]
  have hb0 : (β : ℂ) ≠ 0 := by exact_mod_cast hb.ne'
  rcases eq_or_ne t 1 with rfl | htp
  · have h2 : (2 : ℂ) ^ (β : ℂ) ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl (by norm_num))
    simp [diskNumerator, diskDenominator, diskMinus, diskPlus, Complex.zero_cpow hb0,
      show (1 : ℂ) + 1 = 2 by norm_num, h2]
  rcases eq_or_ne t (-1) with rfl | htm
  · have h2 : (2 : ℂ) ^ (β : ℂ) ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl (by norm_num))
    simp [diskNumerator, diskDenominator, diskMinus, diskPlus, Complex.zero_cpow hb0,
      show (1 : ℂ) - -1 = 2 by norm_num, h2]
  have hm : 1 - t ≠ 0 := sub_ne_zero.mpr htp.symm
  have hp' : 1 + t ≠ 0 := by
    intro he
    exact htm (by linear_combination he)
  let q := (1 + t) / (1 - t)
  have hq : q ≠ 0 := div_ne_zero hp' hm
  have hqr : q.re = 0 := cayley_re_zero_of_norm_eq_one ht'
  let ζ := q ^ (β : ℂ)
  have hrp : 0 < (1 + t).re := by
    have h₁ := re_diskPlus_nonneg htc
    by_contra! h
    have hre : t.re = -1 := by simp only [Complex.add_re, Complex.one_re] at h₁ h; linarith
    have hnorm := Complex.sq_norm t
    rw [ht', Complex.normSq_apply, hre] at hnorm
    have him : t.im = 0 := by nlinarith
    exact htm (Complex.ext (by simpa using hre) (by simpa using him))
  have hrm : 0 < (1 - t).re := by
    have h₁ := re_diskMinus_nonneg htc
    by_contra! h
    have hre : t.re = 1 := by simp only [Complex.sub_re, Complex.one_re] at h₁ h; linarith
    have hnorm := Complex.sq_norm t
    rw [ht', Complex.normSq_apply, hre] at hnorm
    have him : t.im = 0 := by nlinarith
    exact htp (Complex.ext hre him)
  have hcmp : ζ = diskPlus β t / diskMinus β t := by
    have ha := abs_lt.mp (Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hrp))
    have hc := abs_lt.mp (Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hrm))
    exact cpow_div_of_arg_sub hp' hm (by linarith) (by linarith) _
  have hDm : diskMinus β t ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl hm)
  have hD := diskDenominator_ne_zero hb hb' htc ht0
  have hζ : ζ ≠ 1 := by
    rw [hcmp]
    intro he
    have hsame : diskPlus β t = diskMinus β t := by
      simpa using (div_eq_iff hDm).mp he
    exact hD (sub_eq_zero.mpr hsame.symm)
  have heq : ((1 : ℂ) + ζ) / (1 - ζ) =
      diskNumerator β t / diskDenominator β t := by
    rw [hcmp]
    unfold diskNumerator diskDenominator
    field_simp
  rw [← heq]
  exact rotated_coordinates_of_cayley hζ (phase_bound_on_boundary hq hqr hb hb' htrig)
end MomentComparison
end
end

set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open Set Metric
open MomentComparison
namespace MomentComparison
theorem _root_.solution {p : ℝ} (hp : 2 < p) {P : Polynomial ℂ} {d : ℕ}
    (hP : P.natDegree ≤ d) {M : ℝ} (_hM : 0 ≤ M)
    (hbound : ∀ w, inLens p w → ‖P.eval w‖ ≤ M) :
    ‖P.eval 1‖ ≤ lensFactor p ^ d * M := by
  let r := Real.sqrt (p - 1)
  let β := (2 * Real.pi - 2 * Real.arcsin (2 * r / p)) / Real.pi
  let z := Complex.I * (r : ℂ)
  let a := (z - 1) ^ ((β⁻¹ : ℝ) : ℂ)
  let b := (z + 1) ^ ((β⁻¹ : ℝ) : ℂ)
  let t := (a - b) / (a + b)
  obtain ⟨hr, hrs, hb, hb', htrig⟩ := lensParameters hp
  have heval :
      ‖t‖ < 1 ∧ t ≠ 0 ∧
        diskNumerator β t / diskDenominator β t / z = 1 :=
    inverse_disk_at_one_of_p hp
  obtain ⟨ht, ht0, he⟩ := heval
  have hnorm : ‖t‖⁻¹ = lensFactor p := by
    rw [← norm_inv]
    have hα : β⁻¹ = Real.pi / (2 * Real.pi - 2 * Real.arcsin (2 * r / p)) := by
      rw [show β = _ from rfl, inv_div]
    simp only [t, inv_div, a, b, hα, lensFactor, z, r]
  have h := polynomialGrowth_of_disk P hP (diffContOnCl_normalizedInverse hb hb')
    (fun s hs => hbound _ (normalizedInverse_maps_boundary hp hr hrs hb hb' htrig hs))
    (t := t) (mem_closedBall_zero_iff.mpr ht.le) ht0
  rwa [normalizedInverse_eq ht0, he, hnorm] at h
end MomentComparison
