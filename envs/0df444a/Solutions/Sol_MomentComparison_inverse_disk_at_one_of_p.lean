-- Prove2me | solution 1 for MomentComparison.inverse_disk_at_one_of_p
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T11:08:36.172293+00:00
-- url     : https://prove2.me/submissions/911ba7bf-11b4-488b-bfbe-9dfa6888b3e7

module
public import Definitions.Def_MomentComparison_ComplexPower
public import Definitions.Def_MomentComparison_LensAngle
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Definitions.Def_MomentComparison_LensEvaluation
public import Theorems.Thm_MomentComparison_arg_cpow_ofReal
public import Theorems.Thm_MomentComparison_arg_div_of_arg_sub
public import Theorems.Thm_MomentComparison_cpow_div_of_arg_sub
public import Theorems.Thm_MomentComparison_lensAngle_eq_four_arctan

section
public section
namespace MomentComparison
private theorem norm_sub_one_lt_norm_add_one {q : ℂ} (hq : 0 < q.re) :
    ‖q - 1‖ < ‖q + 1‖ := by
  have he₁ := Complex.sq_norm (q - 1)
  have he₂ := Complex.sq_norm (q + 1)
  simp only [Complex.normSq_apply, Complex.add_re, Complex.sub_re, Complex.add_im,
    Complex.sub_im, Complex.one_re, Complex.one_im, add_zero, sub_zero] at he₁ he₂
  have hsq : ‖q - 1‖ ^ 2 < ‖q + 1‖ ^ 2 := by nlinarith only [he₁, he₂, hq]
  exact lt_of_not_ge fun h =>
    hsq.not_ge (pow_le_pow_left₀ (norm_nonneg _) h 2)
private theorem exponent_at_one {r : ℝ} (hr : 0 < r) :
    let z := Complex.I * (r : ℂ)
    (z - 1).arg - (z + 1).arg = 2 * Real.arctan r⁻¹ := by
  dsimp
  have hminus : (Complex.I * (r : ℂ) - 1).re < 0 := by simp
  have hi : 0 ≤ (Complex.I * (r : ℂ) - 1).im := by simpa using hr.le
  rw [Complex.arg_of_re_neg_of_im_nonneg hminus hi, Complex.arg_of_re_nonneg (by simp)]
  have hn₁ : ‖Complex.I * (r : ℂ) - 1‖ = Real.sqrt (1 + r ^ 2) := by
    simp [Complex.norm_def, Complex.normSq_apply, pow_two]
  have hn₂ : ‖Complex.I * (r : ℂ) + 1‖ = Real.sqrt (1 + r ^ 2) := by
    simp [Complex.norm_def, Complex.normSq_apply, pow_two]
  rw [hn₁, hn₂]
  simp only [Complex.neg_im, Complex.sub_im, Complex.add_im, Complex.I_mul_im,
    Complex.ofReal_re, Complex.one_im, sub_zero, add_zero, neg_div, Real.arcsin_neg]
  rw [← Real.arctan_eq_arcsin, Real.arctan_inv_of_pos hr]
  ring
private theorem inverse_disk_at_one {r : ℝ} (hr : 1 < r) :
    let β := (2 * Real.pi - 4 * Real.arctan r⁻¹) / Real.pi
    let z := Complex.I * (r : ℂ)
    let a := (z - 1) ^ ((β⁻¹ : ℝ) : ℂ)
    let b := (z + 1) ^ ((β⁻¹ : ℝ) : ℂ)
    let t := (a - b) / (a + b)
    ‖t‖ < 1 ∧ t ≠ 0 ∧
      ((1 - t) ^ (β : ℂ) + (1 + t) ^ (β : ℂ)) /
        ((1 - t) ^ (β : ℂ) - (1 + t) ^ (β : ℂ)) / z = 1 := by
  dsimp only
  let δ := 2 * Real.arctan r⁻¹
  let β := (2 * Real.pi - 4 * Real.arctan r⁻¹) / Real.pi
  let α := β⁻¹
  let z := Complex.I * (r : ℂ)
  let a := (z - 1) ^ (α : ℂ)
  let b := (z + 1) ^ (α : ℂ)
  let t := (a - b) / (a + b)
  let u := (z - 1) / (z + 1)
  let q := a / b
  change ‖t‖ < 1 ∧ t ≠ 0 ∧
    ((1 - t) ^ (β : ℂ) + (1 + t) ^ (β : ℂ)) /
      ((1 - t) ^ (β : ℂ) - (1 + t) ^ (β : ℂ)) / z = 1
  have hr₀ : 0 < r := by linarith
  have hδ : 0 < δ := by
    exact mul_pos (by norm_num) (Real.arctan_pos.2 (inv_pos.2 hr₀))
  have hδ' : δ < Real.pi / 2 := by
    have h := Real.arctan_strictMono (inv_lt_one_of_one_lt₀ hr)
    rw [Real.arctan_one] at h
    dsimp [δ]
    linarith
  have hβ : 1 < β := by
    apply (lt_div_iff₀ Real.pi_pos).2
    change 1 * Real.pi < 2 * Real.pi - 4 * Real.arctan r⁻¹
    dsimp [δ] at hδ'
    linarith
  have hα : 0 < α := inv_pos.2 (by linarith)
  have hα' : α < 1 := inv_lt_one_of_one_lt₀ hβ
  have hδa : δ * α < Real.pi / 2 := (mul_lt_of_lt_one_right hδ hα').trans hδ'
  have hz : z ≠ 0 := mul_ne_zero Complex.I_ne_zero (by exact_mod_cast hr₀.ne')
  have hm : z - 1 ≠ 0 := by
    intro h
    have he := congrArg Complex.re h
    norm_num [z] at he
  have hp : z + 1 ≠ 0 := by
    intro h
    have he := congrArg Complex.re h
    norm_num [z] at he
  have hu : u ≠ 0 := div_ne_zero hm hp
  have hu₁ : u ≠ 1 := by
    intro h
    have he := (div_eq_iff hp).mp h
    have htwo : (2 : ℂ) = 0 := by linear_combination -he
    exact (by norm_num : (2 : ℂ) ≠ 0) htwo
  have harg : (z - 1).arg - (z + 1).arg = δ := exponent_at_one hr₀
  have hlo : -Real.pi < (z - 1).arg - (z + 1).arg := by rw [harg]; linarith [Real.pi_pos]
  have hhi : (z - 1).arg - (z + 1).arg ≤ Real.pi := by rw [harg]; linarith [Real.pi_pos]
  have huarg : u.arg = δ := (arg_div_of_arg_sub hm hp hlo hhi).trans harg
  have hq : u ^ (α : ℂ) = q := cpow_div_of_arg_sub hm hp hlo hhi _
  have hqa : q.arg = δ * α := by
    rw [← hq, arg_cpow_ofReal hu, huarg]
    · rw [huarg]; linarith [mul_pos hδ hα, Real.pi_pos]
    · rw [huarg]; linarith [Real.pi_pos]
  have hb : b ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl hp)
  have ha : a ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl hm)
  have hqre : 0 < q.re := by
    have h := (Complex.abs_arg_lt_pi_div_two_iff).mp
      (show |q.arg| < Real.pi / 2 by rw [hqa, abs_of_pos (mul_pos hδ hα)]; exact hδa)
    exact h.resolve_right (div_ne_zero ha hb)
  have hqβ : q ^ (β : ℂ) = u := by
    rw [← hq, ← Complex.cpow_mul]
    · rw [← Complex.ofReal_mul, inv_mul_cancel₀ (by linarith : β ≠ 0),
        Complex.ofReal_one, Complex.cpow_one]
    all_goals
      simp only [Complex.mul_im, Complex.ofReal_im, mul_zero, zero_add,
        Complex.ofReal_re, Complex.log_im, huarg]
      linarith [mul_pos hδ hα, Real.pi_pos]
  have hq₁ : q ≠ 1 := by
    intro he
    exact hu₁ (by simpa [he] using hqβ.symm)
  have hqplus : q + 1 ≠ 0 := by
    intro h
    have he := congrArg Complex.re h
    simp only [Complex.add_re, Complex.one_re, Complex.zero_re] at he
    linarith
  have hab : a + b ≠ 0 := by
    have he : a + b = (q + 1) * b := by dsimp [q]; rw [add_mul, div_mul_cancel₀ _ hb, one_mul]
    rw [he]
    exact mul_ne_zero hqplus hb
  have htq : t = (q - 1) / (q + 1) := by
    dsimp [t, q]
    field_simp [hb, hab, hqplus]
  have ht : ‖t‖ < 1 := by
    rw [htq, norm_div, div_lt_one (norm_pos_iff.mpr hqplus)]
    exact norm_sub_one_lt_norm_add_one hqre
  have ht₀ : t ≠ 0 := by rw [htq]; exact div_ne_zero (sub_ne_zero.mpr hq₁) hqplus
  refine ⟨ht, ht₀, ?_⟩
  have hplus : 0 < (1 + t).re := by
    simp only [Complex.add_re, Complex.one_re]
    have h := (Complex.abs_re_le_norm t).trans_lt ht
    linarith [(abs_lt.mp h).1]
  have hminus : 0 < (1 - t).re := by
    simp only [Complex.sub_re, Complex.one_re]
    exact sub_pos.mpr ((abs_le.mp (Complex.abs_re_le_norm t)).2.trans_lt ht)
  have hplus₀ : 1 + t ≠ 0 := by
    intro h; rw [h] at hplus; exact lt_irrefl 0 hplus
  have hminus₀ : 1 - t ≠ 0 := by
    intro h; rw [h] at hminus; exact lt_irrefl 0 hminus
  have hplusarg := abs_lt.mp ((Complex.abs_arg_lt_pi_div_two_iff).mpr (Or.inl hplus))
  have hminusarg := abs_lt.mp ((Complex.abs_arg_lt_pi_div_two_iff).mpr (Or.inl hminus))
  have htquot : (1 + t) / (1 - t) = q := by
    rw [htq]
    field_simp [hqplus]
    ring
  have hquot := cpow_div_of_arg_sub hplus₀ hminus₀ (by linarith [hplusarg.1, hminusarg.2])
    (by linarith [hplusarg.2, hminusarg.1]) (β : ℂ)
  rw [htquot, hqβ] at hquot
  let x := (1 - t) ^ (β : ℂ)
  let y := (1 + t) ^ (β : ℂ)
  have hx : x ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl hminus₀)
  have hy : y = u * x := (div_eq_iff hx).mp hquot.symm
  change (x + y) / (x - y) / z = 1
  have he₁ : x + u * x = (1 + u) * x := by ring
  have he₂ : x - u * x = (1 - u) * x := by ring
  rw [hy, he₁, he₂, mul_div_mul_right _ _ hx]
  apply (div_eq_iff hz).2
  rw [one_mul]
  have hu' : 1 - u ≠ 0 := sub_ne_zero.mpr hu₁.symm
  apply (div_eq_iff hu').2
  dsimp [u]
  field_simp [hp]
  ring
end MomentComparison
end
end

set_option autoImplicit true
@[expose] public section
public section
open MomentComparison
namespace MomentComparison
theorem _root_.solution {p : ℝ} (hp : 2 < p) :
    let r := Real.sqrt (p - 1)
    let β := (2 * Real.pi - 2 * Real.arcsin (2 * r / p)) / Real.pi
    let z := Complex.I * (r : ℂ)
    let a := (z - 1) ^ ((β⁻¹ : ℝ) : ℂ)
    let b := (z + 1) ^ ((β⁻¹ : ℝ) : ℂ)
    let t := (a - b) / (a + b)
    ‖t‖ < 1 ∧ t ≠ 0 ∧
      ((1 - t) ^ (β : ℂ) + (1 + t) ^ (β : ℂ)) /
        ((1 - t) ^ (β : ℂ) - (1 + t) ^ (β : ℂ)) / z = 1 := by
  dsimp only
  rw [lensAngle_eq_four_arctan hp]
  exact inverse_disk_at_one ((Real.lt_sqrt (by norm_num)).2 (by linarith))
end MomentComparison
