-- Prove2me | solution 1 for OAI.SKGap.scalar_closed_isolation_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T11:00:31.988732+00:00
-- url     : https://prove2.me/submissions/e9a3ab8d-e8ab-46f8-bef3-b1bb2e8ad921

import Mathlib
import Definitions.Def_OAIQ072A000

section
-- module Solutions.OAIQ074_CM.Compat
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem dite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : p) :
    dite p a b = a h := dif_pos h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ074_CM.SKGap_Entropy_EntropyEll
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Real Set Filter
open scoped NNReal ENNReal Topology
noncomputable section
open Real Set
namespace SKGap

theorem entropyEll_hasDerivAt {u : ℝ} (hu : u < 1) :
    HasDerivAt entropyEll (u / (1 - u)) u := by
  have hd := ((((hasDerivAt_id u).const_sub 1).log (by linarith : 1 - u ≠ 0)).neg).sub
    (hasDerivAt_id u)
  convert! hd using 1
  all_goals try with_reducible_and_instances rfl
  dsimp
  field_simp [show 1 - u ≠ 0 by linarith]
  ring

theorem entropyEll_nonneg {u : ℝ} (hu : u < 1) : 0 ≤ entropyEll u := by
  have h := log_le_sub_one_of_pos (by linarith : 0 < 1 - u)
  dsimp [entropyEll]
  linarith

theorem entropyEll_le_half_sq_of_nonpos {u : ℝ} (hu : u ≤ 0) :
    entropyEll u ≤ u ^ 2 / 2 := by
  let f : ℝ → ℝ := fun x => x ^ 2 / 2 - entropyEll x
  have hd (x : ℝ) (hx : x < 1) : HasDerivAt f (-x ^ 2 / (1 - x)) x := by
    convert! (((hasDerivAt_id x).pow 2).div_const 2).sub (entropyEll_hasDerivAt hx) using 1
    all_goals try with_reducible_and_instances rfl
    dsimp
    field_simp [show 1 - x ≠ 0 by linarith]
    ring
  have hm : AntitoneOn f (Iic 0) := by
    apply antitoneOn_of_deriv_nonpos (convex_Iic 0)
    · intro x hx
      exact (hd x (by simp only [mem_Iic] at hx; linarith)).continuousAt.continuousWithinAt
    · intro x hx
      have hx0 : x < 0 := by simpa only [interior_Iic, mem_Iio] using hx
      exact (hd x (by linarith)).differentiableAt.differentiableWithinAt
    · intro x hx
      have hx0 : x < 0 := by simpa only [interior_Iic, mem_Iio] using hx
      rw [(hd x (by linarith)).deriv]
      exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg _)) (by linarith)
  have h := hm (show u ∈ Iic 0 from hu) (show (0 : ℝ) ∈ Iic 0 by simp) hu
  simpa [f, entropyEll] using h

theorem entropySlack_pos_of_neg {B u : ℝ} (hB0 : 0 ≤ B) (hB1 : B < 1) (hu : u < 0) :
    0 < entropySlack B u := by
  have he := mul_le_mul_of_nonneg_left (entropyEll_le_half_sq_of_nonpos hu.le) hB0
  have hs : 0 < u ^ 2 := sq_pos_of_ne_zero hu.ne
  dsimp [entropySlack]
  nlinarith

theorem value_le_of_deriv_nonneg {f g : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hd : ∀ x ∈ Icc a b, HasDerivAt f (g x) x)
    (hg : ∀ x ∈ Icc a b, 0 ≤ g x) : f a ≤ f b := by
  have hm : MonotoneOn f (Icc a b) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc a b)
    · intro x hx
      exact (hd x hx).continuousAt.continuousWithinAt
    · intro x hx
      exact (hd x (interior_subset hx)).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [(hd x (interior_subset hx)).deriv]
      exact hg x (interior_subset hx)
  exact hm ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩ hab

theorem half_sq_le_entropyEll {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) :
    u ^ 2 / 2 ≤ entropyEll u := by
  let f : ℝ → ℝ := fun x => entropyEll x - x ^ 2 / 2
  have hd (x : ℝ) (hx : x < 1) : HasDerivAt f (x ^ 2 / (1 - x)) x := by
    convert! (entropyEll_hasDerivAt hx).sub (((hasDerivAt_id x).pow 2).div_const 2) using 1
    all_goals try with_reducible_and_instances rfl
    dsimp
    field_simp [show 1 - x ≠ 0 by linarith]
    ring
  have h := value_le_of_deriv_nonneg hu0 (fun x hx => hd x (hx.2.trans_lt hu1))
    (fun x hx => div_nonneg (sq_nonneg x) (by linarith [hx.2]))
  simpa [f, entropyEll] using h

theorem entropySlack_cubic_lower {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) :
    u ^ 3 / 6 ≤ entropySlack (1 - u) u := by
  let f : ℝ → ℝ := fun x => entropySlack (1 - x) x - x ^ 3 / 6
  have hd (x : ℝ) (hx : x < 1) : HasDerivAt f (entropyEll x - x ^ 2 / 2) x := by
    convert! ((((hasDerivAt_id x).pow 2).div_const 2).sub
      (((hasDerivAt_id x).const_sub 1).mul (entropyEll_hasDerivAt hx))).sub
        (((hasDerivAt_id x).pow 3).div_const 6) using 1
    all_goals try with_reducible_and_instances rfl
    dsimp
    field_simp [show 1 - x ≠ 0 by linarith]
    ring
  have h := value_le_of_deriv_nonneg hu0 (fun x hx => hd x (hx.2.trans_lt hu1))
    (fun x hx => sub_nonneg.mpr (half_sq_le_entropyEll hx.1 (hx.2.trans_lt hu1)))
  simpa [f, entropySlack, entropyEll] using h

theorem entropySlack_cubic_lower_of_le {B u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1)
    (hB : B ≤ 1 - u) : u ^ 3 / 6 ≤ entropySlack B u := by
  have h := mul_le_mul_of_nonneg_right hB (entropyEll_nonneg hu1)
  have hl := entropySlack_cubic_lower hu0 hu1
  dsimp [entropySlack] at *
  linarith

theorem entropySlack_pos {B u : ℝ} (hB0 : 0 ≤ B) (hB1 : B < 1)
    (huB : u ≤ 1 - B) (hu1 : u < 1) (hu0 : u ≠ 0) : 0 < entropySlack B u := by
  rcases hu0.lt_or_gt with hneg | hpos
  · exact entropySlack_pos_of_neg hB0 hB1 hneg
  · have h := entropySlack_cubic_lower_of_le hpos.le hu1 (by linarith : B ≤ 1 - u)
    exact (div_pos (pow_pos hpos 3) (by norm_num : (0 : ℝ) < 6)).trans_le h

theorem log_one_add_cubic_upper {x : ℝ} (hx : 0 ≤ x) :
    log (1 + x) ≤ x - x ^ 2 / 2 + x ^ 3 / 3 := by
  let f : ℝ → ℝ := fun y => y - y ^ 2 / 2 + y ^ 3 / 3 - log (1 + y)
  have hd (y : ℝ) (hy : 0 ≤ y) : HasDerivAt f (y ^ 3 / (1 + y)) y := by
    convert! (((hasDerivAt_id y).sub (((hasDerivAt_id y).pow 2).div_const 2)).add
      (((hasDerivAt_id y).pow 3).div_const 3)).sub
        (((hasDerivAt_id y).const_add 1).log (by linarith : 1 + y ≠ 0)) using 1
    all_goals try with_reducible_and_instances rfl
    dsimp
    field_simp [show 1 + y ≠ 0 by linarith]
    ring
  have h := value_le_of_deriv_nonneg hx (fun y hy => hd y hy.1)
    (fun y hy => div_nonneg (pow_nonneg hy.1 3) (by linarith [hy.1]))
  simpa [f] using h

theorem entropyVarianceSlack_hasDerivAt {k B C : ℝ} (hk : 0 < k) (hC : 0 < C) :
    HasDerivAt (entropyVarianceSlack k B) (entropyVarianceSlope k B C) C := by
  have hden : C ^ 2 / k ≠ 0 := div_ne_zero (pow_ne_zero 2 hC.ne') hk.ne'
  convert! (((((hasDerivAt_id C).pow 2).div_const k).sub_const 1).sub
    ((((hasDerivAt_id C).pow 2).div_const k).log hden)).sub
      ((((hasDerivAt_id C).sub_const B).pow 2).div_const (1 + k)) using 1
  all_goals try with_reducible_and_instances rfl
  dsimp [entropyVarianceSlope]
  field_simp

theorem entropyVarianceSlope_hasDerivAt {k B C : ℝ} (hk : 0 < k) (hC : 0 < C) :
    HasDerivAt (entropyVarianceSlope k B) (2 / (k * (1 + k)) + 2 / C ^ 2) C := by
  convert! ((((hasDerivAt_id C).const_mul 2).div_const k).sub
    ((hasDerivAt_const C (2 : ℝ)).div (hasDerivAt_id C) hC.ne')).sub
      ((((hasDerivAt_id C).sub_const B).const_mul 2).div_const (1 + k)) using 1
  all_goals try with_reducible_and_instances rfl
  dsimp
  field_simp
  ring

theorem entropyVariance_curvature_one {k C : ℝ} (hk0 : 0 < k) (hk1 : k ≤ 1) (_hC : 0 < C) :
    1 ≤ 2 / (k * (1 + k)) + 2 / C ^ 2 := by
  have hp : 0 < k * (1 + k) := mul_pos hk0 (by linarith)
  have hk2 : k * (1 + k) ≤ 2 := by nlinarith
  have hdiv : 1 ≤ 2 / (k * (1 + k)) := by rwa [le_div_iff₀ hp, one_mul]
  have hpos : 0 ≤ 2 / C ^ 2 := div_nonneg (by norm_num) (sq_nonneg _)
  linarith

theorem entropyVariance_taylor_lower {k B C₀ C : ℝ} (hk0 : 0 < k) (hk1 : k ≤ 1)
    (hC₀ : 0 < C₀) (hC : C₀ ≤ C) :
    entropyVarianceSlack k B C₀ + entropyVarianceSlope k B C₀ * (C - C₀) +
      (C - C₀)^2 / 2 ≤ entropyVarianceSlack k B C := by
  have hslope (x : ℝ) (hx : C₀ ≤ x) :
      entropyVarianceSlope k B C₀ + (x - C₀) ≤ entropyVarianceSlope k B x := by
    have h := value_le_of_deriv_nonneg hx
      (f := fun y => entropyVarianceSlope k B y - y)
      (g := fun y => 2 / (k * (1 + k)) + 2 / y ^ 2 - 1)
      (fun y hy => (entropyVarianceSlope_hasDerivAt hk0 (hC₀.trans_le hy.1)).sub (hasDerivAt_id y))
      (fun y hy => sub_nonneg.mpr (entropyVariance_curvature_one hk0 hk1 (hC₀.trans_le hy.1)))
    linarith
  have hd (x : ℝ) (hx : C₀ ≤ x) :
      HasDerivAt (fun y => entropyVarianceSlack k B y -
        entropyVarianceSlope k B C₀ * (y - C₀) - (y - C₀)^2 / 2)
        (entropyVarianceSlope k B x - entropyVarianceSlope k B C₀ - (x - C₀)) x := by
    convert! ((entropyVarianceSlack_hasDerivAt hk0 (hC₀.trans_le hx)).sub
      (((hasDerivAt_id x).sub_const C₀).const_mul (entropyVarianceSlope k B C₀))).sub
        ((((hasDerivAt_id x).sub_const C₀).pow 2).div_const 2) using 1
    all_goals try with_reducible_and_instances rfl
    dsimp
    ring
  have h := value_le_of_deriv_nonneg hC (fun x hx => hd x hx.1)
    (fun x hx => by linarith [hslope x hx.1])
  simp only [sub_self, mul_zero, zero_pow (by norm_num : 2 ≠ 0), zero_div, sub_zero] at h
  linarith

theorem entropyVariance_at_base_lower {k a : ℝ} (hk0 : 0 < k) (hk1 : k ≤ 1) (ha : 0 ≤ a) :
    -(2 * a ^ 3 / 3) ≤ entropyVarianceSlack k (1 - a) (1 + k * a) := by
  have hC : 0 < 1 + k * a := by positivity
  have heq : entropyVarianceSlack k (1 - a) (1 + k * a) =
      1 / k - 1 + log k + 2 * a - a ^ 2 - 2 * log (1 + k * a) := by
    unfold entropyVarianceSlack
    rw [log_div (pow_ne_zero 2 hC.ne') hk0.ne', log_pow]
    field_simp
    ring
  rw [heq]
  have hlogk := one_sub_inv_le_log_of_pos hk0
  have hlog := log_le_log hC (show 1 + k * a ≤ 1 + a by nlinarith)
  have hcubic := log_one_add_cubic_upper ha
  simp only [one_div] at *
  linarith

theorem entropyVarianceSlope_at_base {k a : ℝ} (hk : 0 < k) (ha : 0 ≤ a) :
    entropyVarianceSlope k (1 - a) (1 + k * a) = 2 / k - 2 / (1 + k * a) := by
  unfold entropyVarianceSlope
  field_simp
  ring

theorem entropyVarianceSlope_at_base_lower {k a : ℝ} (hk0 : 0 < k) (hk1 : k ≤ 1) (ha : 0 ≤ a) :
    2 * a / (1 + a) ≤ entropyVarianceSlope k (1 - a) (1 + k * a) := by
  rw [entropyVarianceSlope_at_base hk0 ha]
  have hkp : 0 < 1 + k * a := by positivity
  have hap : 0 < 1 + a := by positivity
  have heq : 1 / k - 1 / (1 + k * a) - a / (1 + a) =
      (1 - k) * (1 + a + k * a ^ 2) / (k * (1 + k * a) * (1 + a)) := by
    field_simp
    ring
  have hnonneg : 0 ≤ 1 / k - 1 / (1 + k * a) - a / (1 + a) := by
    rw [heq]
    positivity
  have h2 := mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hnonneg
  ring_nf at h2 ⊢
  linarith

theorem entropyVariance_pos_large {k a C : ℝ} (hk0 : 0 < k) (hk1 : k ≤ 1)
    (ha0 : 0 < a) (ha1 : a < 1) (hC : 1 + k * a ≤ C)
    (hlarge : (1 + k) * a ^ 3 / 3 ≤ (C - (1 + k * a)) ^ 2) :
    0 < entropyVarianceSlack k (1 - a) C := by
  let Δ := C - (1 + k * a)
  have hΔ : 0 ≤ Δ := sub_nonneg.mpr hC
  have hΔsq : a ^ 3 / 3 ≤ Δ ^ 2 := by
    dsimp [Δ]
    have hp := mul_nonneg hk0.le (pow_nonneg ha0.le 3)
    nlinarith
  have hΔlower : a ^ 2 / 2 < Δ := by
    by_contra h
    have hle : Δ ≤ a ^ 2 / 2 := le_of_not_gt h
    have hsq := mul_self_le_mul_self hΔ hle
    have hp := mul_pos (pow_pos ha0 3) (show 0 < 4 - 3 * a by linarith)
    nlinarith
  have hlinslope : a ≤ 2 * a / (1 + a) := by
    rw [le_div_iff₀ (show 0 < 1 + a by positivity)]
    nlinarith [mul_nonneg ha0.le (sub_nonneg.mpr ha1.le)]
  have hlinear : a ^ 3 / 2 < entropyVarianceSlope k (1 - a) (1 + k * a) * Δ := by
    have hprod := mul_le_mul_of_nonneg_right
      (hlinslope.trans (entropyVarianceSlope_at_base_lower hk0 hk1 ha0.le)) hΔ
    have hstrict := mul_lt_mul_of_pos_left hΔlower ha0
    nlinarith
  have ht := entropyVariance_taylor_lower (B := 1 - a) hk0 hk1
    (show 0 < 1 + k * a by positivity) hC
  have hb := entropyVariance_at_base_lower hk0 hk1 ha0.le
  change entropyVarianceSlack k (1 - a) (1 + k * a) +
    entropyVarianceSlope k (1 - a) (1 + k * a) * Δ + Δ ^ 2 / 2 ≤ _ at ht
  linarith

theorem entropy_transport_complete_square {k B C u : ℝ} (hk : 0 < k) :
    u * (C - B) - k * u ^ 2 / 2 - B * entropyEll u -
      (C - B) ^ 2 / (2 * (1 + k)) =
    entropySlack B u - (C - B - (1 + k) * u) ^ 2 / (2 * (1 + k)) := by
  unfold entropySlack
  field_simp
  ring

theorem entropy_scalar_optimization {k B C R : ℝ} (hk0 : 0 < k) (hk1 : k ≤ 1)
    (hB0 : 0 < B) (hB1 : B < 1) (hR : 0 ≤ R)
    (htransport : ∀ u < 1, u * (C - B) - k * u ^ 2 / 2 - B * entropyEll u ≤ R)
    (hvariance : 1 < C → C ^ 2 / k - 1 - log (C ^ 2 / k) ≤ 2 * R) :
    (C - B) ^ 2 / (2 * (1 + k)) ≤ R ∧
      (C ≠ B → (C - B) ^ 2 / (2 * (1 + k)) < R) := by
  have hkp : 0 < 1 + k := by linarith
  have hstrict (hCB : C ≠ B) : (C - B) ^ 2 / (2 * (1 + k)) < R := by
    let a := 1 - B
    have ha0 : 0 < a := sub_pos.mpr hB1
    have ha1 : a < 1 := by dsimp [a]; linarith
    by_cases hsmall : (C - B) / (1 + k) ≤ a
    · let u := (C - B) / (1 + k)
      have hu1 : u < 1 := hsmall.trans_lt ha1
      have hu0 : u ≠ 0 := div_ne_zero (sub_ne_zero.mpr hCB) hkp.ne'
      have hs := entropySlack_pos hB0.le hB1 hsmall hu1 hu0
      have ht := htransport u hu1
      have he := entropy_transport_complete_square (B := B) (C := C) (u := u) hk0
      have hzero : C - B - (1 + k) * u = 0 := by dsimp [u]; field_simp; ring
      rw [hzero] at he
      norm_num at he
      linarith
    · have hC : 1 + k * a < C := by
        have ht := (lt_div_iff₀ hkp).mp (lt_of_not_ge hsmall)
        dsimp [a] at *
        nlinarith
      by_cases hlarge : (1 + k) * a ^ 3 / 3 ≤ (C - (1 + k * a)) ^ 2
      · have hf := entropyVariance_pos_large hk0 hk1 ha0 ha1 hC.le hlarge
        have hv := hvariance (by have hp := mul_pos hk0 ha0; linarith)
        have hB : 1 - a = B := by dsimp [a]; ring
        rw [hB] at hf
        unfold entropyVarianceSlack at hf
        have he : (C - B) ^ 2 / (1 + k) = 2 * ((C - B) ^ 2 / (2 * (1 + k))) := by field_simp
        rw [he] at hf
        linarith
      · have hs := entropySlack_cubic_lower ha0.le ha1
        have hB : 1 - a = B := by dsimp [a]; ring
        rw [hB] at hs
        have ht := htransport a ha1
        have he := entropy_transport_complete_square (B := B) (C := C) (u := a) hk0
        have hdelta : C - B - (1 + k) * a = C - (1 + k * a) := by dsimp [a]; ring
        rw [hdelta] at he
        have hbound : (C - (1 + k * a)) ^ 2 / (2 * (1 + k)) < a ^ 3 / 6 := by
          rw [div_lt_iff₀ (by positivity : 0 < 2 * (1 + k))]
          linarith [lt_of_not_ge hlarge]
        linarith
  refine ⟨?_, hstrict⟩
  by_cases hCB : C = B
  · simpa [hCB] using hR
  · exact (hstrict hCB).le

theorem entropy_variance_function_mono {w v : ℝ} (hw : 1 ≤ w) (hv : w ≤ v) :
    w - 1 - log w ≤ v - 1 - log v := by
  apply value_le_of_deriv_nonneg hv
    (g := fun x => 1 - 1 / x)
  · intro x hx
    have hxp : 0 < x := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (hw.trans hx.1)
    convert! ((hasDerivAt_id x).sub_const 1).sub ((hasDerivAt_id x).log hxp.ne') using 1
  · intro x hx
    have hx1 : 1 ≤ x := hw.trans hx.1
    rw [sub_nonneg, div_le_one (by linarith : 0 < x)]
    exact hx1

theorem entropy_variance_scale {j w : ℝ} (hj0 : 0 < j) (hj1 : j ≤ 1) (hw : 1 ≤ w) :
    w - 1 - log w ≤ j * (w / j - 1 - log (w / j)) := by
  have hwp : 0 < w := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hw
  rw [log_div hwp.ne' hj0.ne']
  have hlog := mul_le_mul_of_nonneg_left (one_sub_inv_le_log_of_pos hj0) hj0.le
  have hextra := mul_nonneg (sub_nonneg.mpr hj1) (log_nonneg hw)
  have heq : j * (1 - j⁻¹) = j - 1 := by field_simp
  rw [heq] at hlog
  have hcancel : j * (w / j) = w := mul_div_cancel₀ w hj0.ne'
  nlinarith

theorem entropy_variance_scaled_lower {j k C v D : ℝ}
    (hj0 : 0 < j) (hj1 : j ≤ 1) (hk0 : 0 < k) (hk1 : k ≤ 1) (hC : 1 < C)
    (hcv : C ^ 2 / (j * k) ≤ v) (hD : (v - 1 - log v) / 2 ≤ D) :
    C ^ 2 / k - 1 - log (C ^ 2 / k) ≤ 2 * (j * D) := by
  have hw : 1 ≤ C ^ 2 / k := by rw [le_div_iff₀ hk0]; nlinarith
  have hwj : 1 ≤ C ^ 2 / (j * k) := by
    rw [le_div_iff₀ (mul_pos hj0 hk0)]
    nlinarith [mul_le_mul_of_nonneg_right hj1 hk0.le]
  have hm := entropy_variance_function_mono hwj hcv
  have hs := entropy_variance_scale hj0 hj1 hw
  have heq : C ^ 2 / k / j = C ^ 2 / (j * k) := by field_simp
  rw [heq] at hs
  have hmj := mul_le_mul_of_nonneg_left hm hj0.le
  have hdj := mul_le_mul_of_nonneg_left hD hj0.le
  linarith

end SKGap

end
end
end

end OAI
end

section
-- module Solutions.OAIQ074_CM.SKGap_Localization_ScalarParametersJoined
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Real
open scoped NNReal ENNReal BoundedContinuousFunction

namespace SKGap

lemma momentCut_nonneg (n : ℕ) (x : ℝ) : 0 ≤ momentCut n x :=
  le_min (Nat.cast_nonneg _) (sq_nonneg _)

lemma momentCut_tendsto (x : ℝ) : Tendsto (fun n => momentCut n x) atTop (𝓝 (x^2)) := by
  have he : ∀ᶠ n : ℕ in atTop, momentCut n x = x^2 := by
    obtain ⟨N,hN⟩ := exists_nat_ge (x^2)
    filter_upwards [eventually_ge_atTop N] with n hn
    exact min_eq_right (hN.trans (by exact_mod_cast hn))
  exact (tendsto_congr' he).2 tendsto_const_nhds

lemma momentBall_iff (R : ℝ) (hR : 0 ≤ R) (P : ProbabilityMeasure ℝ) :
    P ∈ momentBall R ↔ ∀ n, (∫ x, momentCut n x ∂P) ≤ R := by
  constructor
  · intro h n
    apply (ENNReal.ofReal_le_ofReal_iff hR).mp
    rw [ofReal_integral_eq_lintegral_ofReal ((momentCut n).integrable (μ := (P : Measure ℝ)))
      (ae_of_all _ (momentCut_nonneg n))]
    exact (lintegral_mono (fun x => ENNReal.ofReal_le_ofReal (min_le_right _ _))).trans h
  · intro h
    have ht : Tendsto (fun n => ∫⁻ x, ENNReal.ofReal (momentCut n x) ∂P) atTop
        (𝓝 (∫⁻ x : ℝ, ENNReal.ofReal (x^2) ∂P)) := by
      apply lintegral_tendsto_of_tendsto_of_monotone
      · intro n; exact (ENNReal.continuous_ofReal.comp (momentCut n).continuous).aemeasurable
      · exact ae_of_all _ (fun x a b hab => ENNReal.ofReal_le_ofReal (min_le_min_right _ (by exact_mod_cast hab)))
      · exact ae_of_all _ (fun x => ENNReal.continuous_ofReal.continuousAt.tendsto.comp (momentCut_tendsto x))
    apply le_of_tendsto ht
    exact Eventually.of_forall (fun n => by
      rw [← ofReal_integral_eq_lintegral_ofReal ((momentCut n).integrable (μ := (P : Measure ℝ))) (ae_of_all _ (momentCut_nonneg n))]
      exact ENNReal.ofReal_le_ofReal (h n))

lemma isClosed_momentBall (R : ℝ) : IsClosed (momentBall R) := by
  have he : momentBall R = momentBall (max 0 R) := by simp only [momentBall, ENNReal.ofReal_max, ENNReal.ofReal_zero, max_eq_right (show (0:ℝ≥0∞) ≤ ENNReal.ofReal R from bot_le)]
  rw [he]
  have hR : 0 ≤ max 0 R := le_max_left _ _
  have hes : momentBall (max 0 R) = ⋂ n, {P : ProbabilityMeasure ℝ | (∫ x, momentCut n x ∂P) ≤ max 0 R} := by
    ext P; simp only [mem_iInter, mem_ofPred_eq]; exact momentBall_iff _ hR P
  rw [hes]
  exact isClosed_iInter (fun n => isClosed_le (ProbabilityMeasure.continuous_integral_boundedContinuousFunction _) continuous_const)

lemma momentBall_integrable {R : ℝ} {P : ProbabilityMeasure ℝ} (hP : P ∈ momentBall R) :
    Integrable (fun x : ℝ => x^2) (P : Measure ℝ) := by
  refine ⟨(by fun_prop), ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ (fun x : ℝ => sq_nonneg x))]
  exact lt_of_le_of_lt hP ENNReal.ofReal_lt_top

lemma momentBall_integral_le {R : ℝ} (hR : 0 ≤ R) {P : ProbabilityMeasure ℝ} (hP : P ∈ momentBall R) :
    (∫ x : ℝ, x^2 ∂P) ≤ R := by
  apply (ENNReal.ofReal_le_ofReal_iff hR).mp
  rw [ofReal_integral_eq_lintegral_ofReal (momentBall_integrable hP) (ae_of_all _ (fun x : ℝ => sq_nonneg x))]
  exact hP

lemma momentBall_tail {R K : ℝ} (hK : 0 < K) {P : ProbabilityMeasure ℝ}
    (hP : P ∈ momentBall R) :
    (P : Measure ℝ) (Metric.closedBall 0 K)ᶜ ≤ ENNReal.ofReal R / ENNReal.ofReal (K^2) := by
  have hmeas : Measurable (fun x : ℝ => ENNReal.ofReal (x^2)) := by fun_prop
  calc
    _ ≤ (P : Measure ℝ) {x : ℝ | ENNReal.ofReal (K^2) ≤ ENNReal.ofReal (x^2)} := by
      apply measure_mono
      intro x hx
      have hx' : K < |x| := by simpa only [mem_compl_iff, Metric.mem_closedBall, Real.dist_eq, sub_zero, not_le] using hx
      apply ENNReal.ofReal_le_ofReal
      nlinarith [sq_abs x]
    _ ≤ (∫⁻ x : ℝ, ENNReal.ofReal (x^2) ∂P) / ENNReal.ofReal (K^2) :=
      meas_ge_le_lintegral_div hmeas.aemeasurable
        (ENNReal.ofReal_ne_zero_iff.mpr (sq_pos_of_pos hK)) ENNReal.ofReal_ne_top
    _ ≤ _ := ENNReal.div_le_div_right hP _

lemma isTight_momentBall (R : ℝ) :
    IsTightMeasureSet {((P : ProbabilityMeasure ℝ) : Measure ℝ) | P ∈ momentBall R} := by
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
  intro ε hε
  obtain ⟨δ, _, hδ, hδε⟩ := ENNReal.lt_iff_exists_real_btwn.mp hε
  have hd : 0 < δ := ENNReal.ofReal_pos.mp hδ
  let K := max 0 R / δ + 1
  have hK : 0 < K := by dsimp [K]; positivity
  refine ⟨Metric.closedBall 0 K, isCompact_closedBall _ _, ?_⟩
  rintro _ ⟨P,hP,rfl⟩
  calc
    _ ≤ ENNReal.ofReal R / ENNReal.ofReal (K^2) := momentBall_tail hK hP
    _ ≤ ENNReal.ofReal δ := by
      rw [← ENNReal.ofReal_div_of_pos (sq_pos_of_pos hK)]
      apply ENNReal.ofReal_le_ofReal
      rw [div_le_iff₀ (sq_pos_of_pos hK)]
      have hK1 : 1 ≤ K := by dsimp [K]; linarith [div_nonneg (le_max_left 0 R) hd.le]
      have he : δ * (K-1) = max 0 R := by dsimp [K]; field_simp; ring
      have hab : 0 ≤ (K-1)^2 := sq_nonneg _
      nlinarith [le_max_right 0 R, mul_nonneg hd.le hab]
    _ ≤ ε := hδε.le

lemma isCompact_momentBall (R : ℝ) : IsCompact (momentBall R) := by
  have h := isCompact_closure_of_isTightMeasureSet (isTight_momentBall R)
  simpa only [(isClosed_momentBall R).closure_eq] using h

lemma integrable_of_linear_bound {P : Measure ℝ} [IsProbabilityMeasure P]
    (hP : Integrable (fun x : ℝ => x^2) P) {f : ℝ → ℝ} (hf : Continuous f)
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ x, |f x| ≤ C*(1+|x|)) : Integrable f P := by
  apply (((integrable_const (2:ℝ)).add hP).const_mul C).mono' hf.aestronglyMeasurable
  exact ae_of_all _ (fun x => by
    rw [Real.norm_eq_abs]
    have hx : |x| ≤ 1+x^2 := by nlinarith [sq_nonneg (|x|-1), sq_abs x]
    exact (hb x).trans (mul_le_mul_of_nonneg_left (by change 1+|x| ≤ 2+x^2; linarith) hC))

lemma momentClip_error {n : ℕ} (hn : 0 < n) (x : ℝ) :
    |x - max (-(n:ℝ)) (min (n:ℝ) x)| ≤ x^2/(n:ℝ) := by
  have hn' : 0 < (n:ℝ) := by exact_mod_cast hn
  rw [le_div_iff₀ hn']
  by_cases hx : x ≤ (n:ℝ)
  · rw [min_eq_right hx]
    by_cases hx' : -(n:ℝ) ≤ x
    · rw [max_eq_right hx', sub_self, abs_zero, zero_mul]; positivity
    · rw [max_eq_left (le_of_not_ge hx'), abs_of_nonpos (by linarith)]
      nlinarith [sq_nonneg (x+(n:ℝ))]
  · rw [min_eq_left (le_of_not_ge hx), max_eq_right (by linarith), abs_of_nonneg (by linarith)]
    nlinarith [sq_nonneg (x-(n:ℝ))]

lemma moment_integral_approx {R C : ℝ} (hR : 0 ≤ R) (hC : 0 ≤ C)
    {f : ℝ → ℝ} (hf : Continuous f) (hb : ∀ x, |f x| ≤ C*(1+|x|))
    {n : ℕ} (hn : 0 < n) {P : ProbabilityMeasure ℝ} (hP : P ∈ momentBall R) :
    |(∫ x, f x ∂P) - (∫ x, momentClip hf n x ∂P)| ≤ 2*C^2*(1+R)/(n:ℝ) := by
  have hpi := momentBall_integrable hP
  have hfi := integrable_of_linear_bound hpi hf hC hb
  have hn' : 0 < (n:ℝ) := by exact_mod_cast hn
  rw [← integral_sub hfi ((momentClip hf n).integrable (μ := (P : Measure ℝ))), ← Real.norm_eq_abs]
  have hbound : ∀ x, ‖f x - momentClip hf n x‖ ≤ (2*C^2/(n:ℝ))*(1+x^2) := by
    intro x
    rw [Real.norm_eq_abs]
    change |f x - max (-(n:ℝ)) (min (n:ℝ) (f x))| ≤ _
    apply (momentClip_error hn (f x)).trans
    rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right hn']
    have hsq : (f x)^2 ≤ (C*(1+|x|))^2 := by
      have h := mul_self_le_mul_self (abs_nonneg (f x)) (hb x)
      simpa only [← sq, sq_abs] using h
    have hs : (1+|x|)^2 ≤ 2*(1+x^2) := by nlinarith [sq_nonneg (|x|-1), sq_abs x]
    calc
      _ ≤ (C*(1+|x|))^2 := hsq
      _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hs (sq_nonneg C)]
  have he := norm_integral_le_of_norm_le
    (((integrable_const (1:ℝ)).add hpi).const_mul (2*C^2/(n:ℝ))) (ae_of_all _ hbound)
  calc
    _ ≤ ∫ x, (2*C^2/(n:ℝ))*(1+x^2) ∂P := he
    _ = (2*C^2/(n:ℝ))*(1+∫ x : ℝ, x^2 ∂P) := by
      rw [integral_const_mul, integral_add (integrable_const 1) hpi]
      simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
    _ ≤ (2*C^2/(n:ℝ))*(1+R) := mul_le_mul_of_nonneg_left
      (by linarith [momentBall_integral_le hR hP]) (by positivity)
    _ = _ := by ring

lemma continuousOn_integral_of_linear_bound {R C : ℝ} (hR : 0 ≤ R) (hC : 0 ≤ C)
    {f : ℝ → ℝ} (hf : Continuous f) (hb : ∀ x, |f x| ≤ C*(1+|x|)) :
    ContinuousOn (fun P : ProbabilityMeasure ℝ => ∫ x, f x ∂P) (momentBall R) := by
  have ht : TendstoUniformlyOn (fun n (P : ProbabilityMeasure ℝ) => ∫ x, momentClip hf n x ∂P)
      (fun P : ProbabilityMeasure ℝ => ∫ x, f x ∂P) atTop (momentBall R) := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    have he := (tendsto_const_div_atTop_nhds_zero_nat (2*C^2*(1+R))).eventually (gt_mem_nhds hε)
    filter_upwards [he, eventually_gt_atTop 0] with n hn hn0
    intro P hP
    rw [Real.dist_eq]
    exact (moment_integral_approx hR hC hf hb hn0 hP).trans_lt hn
  apply ht.continuousOn
  exact Frequently.of_forall (fun n => (ProbabilityMeasure.continuous_integral_boundedContinuousFunction (momentClip hf n)).continuousOn)

end SKGap

namespace SKGap

lemma continuous_scalarM : Continuous scalarM := by
  let f : ℝ →ᵇ ℝ := BoundedContinuousFunction.ofNormedAddCommGroup tanh continuous_tanh 1
    (fun x => by simpa only [Real.norm_eq_abs] using (abs_tanh_lt_one x).le)
  exact ProbabilityMeasure.continuous_integral_boundedContinuousFunction f

lemma continuous_scalarQMoment : Continuous scalarQMoment := by
  let f : ℝ →ᵇ ℝ := BoundedContinuousFunction.ofNormedAddCommGroup (fun x => tanh x^2) (by fun_prop) 1
    (fun x => by simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (tanh x))] using (tanh_sq_lt_one x).le)
  exact ProbabilityMeasure.continuous_integral_boundedContinuousFunction f

lemma continuous_scalarD (j : ℝ) : Continuous (scalarD j) :=
  (continuous_fst.comp continuous_snd).add (continuous_const.mul (continuous_scalarM.comp continuous_fst))

lemma continuous_scalarS (j : ℝ) : Continuous (scalarS j) :=
  ((continuous_fst.comp continuous_snd).add ((continuous_snd.comp continuous_snd).pow 2)).add
    (continuous_const.mul (continuous_scalarQMoment.comp continuous_fst))

lemma scalarQMoment_bounds (P : ProbabilityMeasure ℝ) : 0 ≤ scalarQMoment P ∧ scalarQMoment P ≤ 1 := by
  refine ⟨integral_nonneg (fun x => sq_nonneg _), ?_⟩
  have hi : Integrable (fun x : ℝ => tanh x^2) (P : Measure ℝ) := Integrable.of_bound
    (by fun_prop) 1 (ae_of_all _ (fun x => by simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (tanh x))] using (tanh_sq_lt_one x).le))
  have h := integral_mono hi (integrable_const (1:ℝ)) (fun x => (tanh_sq_lt_one x).le)
  simpa only [scalarQMoment, integral_const, probReal_univ, smul_eq_mul, one_mul] using h

lemma scalarM_bounds (P : ProbabilityMeasure ℝ) : |scalarM P| ≤ 1 := by
  have h := norm_integral_le_of_norm_le (μ := (P : Measure ℝ)) (f := tanh) (integrable_const (1:ℝ))
    (ae_of_all _ (fun x : ℝ => by simpa only [Real.norm_eq_abs] using (abs_tanh_lt_one x).le))
  simpa only [scalarM, Real.norm_eq_abs, integral_const, probReal_univ, smul_eq_mul, one_mul] using h

lemma continuousOn_scalarA {R : ℝ} (hR : 0 ≤ R) (j : ℝ) :
    ContinuousOn (scalarA j) (scalarMomentDomain R) := by
  have hi := continuousOn_integral_of_linear_bound hR (C := 1) zero_le_one
    (show Continuous (fun x : ℝ => x*tanh x) by fun_prop) (fun x => by
      rw [abs_mul, one_mul]
      have hm := mul_le_mul_of_nonneg_left (abs_tanh_lt_one x).le (abs_nonneg x)
      linarith)
  have hc : ContinuousOn (fun p : ScalarPoint => ∫ x, x*tanh x ∂p.1) (scalarMomentDomain R) :=
    hi.comp continuous_fst.continuousOn (fun p hp => hp.1)
  exact hc.sub ((continuous_scalarD j).mul (continuous_scalarM.comp continuous_fst)).continuousOn

lemma scalarA_eq {R : ℝ} {p : ScalarPoint} (hp : p ∈ scalarMomentDomain R) (j : ℝ) :
    scalarA j p = ∫ x, (x-scalarD j p)*tanh x ∂p.1 := by
  have hi := integrable_of_linear_bound (momentBall_integrable hp.1)
    (show Continuous (fun x : ℝ => x*tanh x) by fun_prop) zero_le_one (fun x => by
      rw [abs_mul, one_mul]
      have hm := mul_le_mul_of_nonneg_left (abs_tanh_lt_one x).le (abs_nonneg x)
      linarith)
  have ht : Integrable tanh (p.1 : Measure ℝ) := Integrable.of_bound
    continuous_tanh.aestronglyMeasurable 1 (ae_of_all _ (fun x => by simpa only [Real.norm_eq_abs] using (abs_tanh_lt_one x).le))
  simp_rw [sub_mul]
  rw [integral_sub hi (ht.const_mul _), integral_const_mul]
  rfl

lemma continuousOn_scalarPsi {R : ℝ} (hR : 0 ≤ R) (j : ℝ) :
    ContinuousOn (scalarPsi j) (scalarMomentDomain R ∩ {p | scalarS j p ≠ 0 ∧ scalarS j p+j*scalarQMoment p.1 ≠ 0}) := by
  unfold scalarPsi
  apply ContinuousOn.div
  · exact continuousOn_const.mul ((((continuousOn_scalarA hR j).mono inter_subset_left).sub
      ((continuous_scalarS j).continuousOn.mul (continuousOn_const.sub (continuous_scalarQMoment.comp continuous_fst).continuousOn))).pow 2)
  · exact (continuous_const.mul (continuous_scalarS j)).continuousOn.mul
      ((continuous_scalarS j).add (continuous_const.mul (continuous_scalarQMoment.comp continuous_fst))).continuousOn
  · intro p hp; exact mul_ne_zero (mul_ne_zero (by norm_num) hp.2.1) hp.2.2

lemma continuous_scalarLogMoment (f : ℝ →ᵇ ℝ) :
    Continuous (fun p : ℝ×ℝ => scalarLogMoment f p.1 p.2) := by
  have hc := continuous_gaussianAverage (continuous_exp.comp f.continuous)
    (C := exp ‖f‖) (fun x => by
      simp only [Function.comp_def]; rw [Real.norm_eq_abs, abs_of_pos (exp_pos _)]
      exact exp_le_exp.mpr ((le_abs_self _).trans (f.norm_coe_le_norm x)))
  apply hc.log
  intro p
  apply ne_of_gt
  exact integral_pos_iff_support_of_nonneg (fun _ => (exp_pos _).le)
    (integrable_gaussian_comp_of_bound (continuous_exp.comp f.continuous)
      (C := exp ‖f‖) (fun x => by
        simp only [Function.comp_def]; rw [Real.norm_eq_abs, abs_of_pos (exp_pos _)]
        exact exp_le_exp.mpr ((le_abs_self _).trans (f.norm_coe_le_norm x))) p.1 p.2) |>.mpr
      (by simp [Function.support, (exp_pos _).ne'])

lemma scalarLogMoment_eq (f : ℝ →ᵇ ℝ) (d : ℝ) {s : ℝ} (hs : 0 ≤ s) :
    scalarLogMoment f d s = log (∫ x, exp (f x) ∂gaussianReal d s.toNNReal) := by
  unfold scalarLogMoment
  congr 1
  exact gaussianAverage_eq_integral (continuous_exp.comp f.continuous) d hs

end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ074_CM.SKGap_Localization_ScalarFixedPointJoined
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Real Set
open scoped NNReal ENNReal

namespace SKGap
open Filter
open scoped Topology

lemma gaussianAverage_hasDerivAt_mean {f f' : ℝ → ℝ} (hf : Continuous f) (hf' : Continuous f')
    (hd : ∀ y, HasDerivAt f (f' y) y) {C C' : ℝ}
    (hb : ∀ y, ‖f y‖ ≤ C) (hb' : ∀ y, ‖f' y‖ ≤ C') (d s : ℝ) :
    HasDerivAt (fun d => gaussianAverage f d s) (gaussianAverage f' d s) d := by
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := gaussianReal 0 1) (s := univ) (x₀ := d)
    (F := fun d x => f (d+sqrt s*x)) (F' := fun d x => f' (d+sqrt s*x))
    (bound := fun _ => C') univ_mem
    (Eventually.of_forall (fun d => (by fun_prop : Continuous (fun x : ℝ => f (d+sqrt s*x))).aestronglyMeasurable))
    (integrable_gaussian_comp_of_bound hf hb d s)
    (by fun_prop)
    (ae_of_all _ (fun x d _ => hb' _))
    (integrable_const _)
    (ae_of_all _ (fun x d _ => by
      convert! (hd (d+sqrt s*x)).comp d ((hasDerivAt_id d).add_const (sqrt s*x)) using 1
      all_goals try with_reducible_and_instances rfl
      simp))).2

lemma gaussianAverage_tanh_mean_deriv (d s : ℝ) :
    HasDerivAt (fun d => gaussianAverage tanh d s)
      (gaussianAverage (fun y => 1-tanh y^2) d s) d := by
  apply gaussianAverage_hasDerivAt_mean continuous_tanh (by fun_prop) hasDerivAt_tanh
    (C := 1) (C' := 1)
  · intro y; simpa using (abs_tanh_lt_one y).le
  · intro y
    rw [Real.norm_eq_abs, abs_le]
    constructor <;> nlinarith [tanh_sq_lt_one y, sq_nonneg (tanh y)]

lemma gaussianAverage_tanh_diff_deriv (d s : ℝ) :
    HasDerivAt (fun d => gaussianAverage (fun y => tanh y-tanh y^2) d s)
      (gaussianAverage (fun y => (1-tanh y^2)*(1-2*tanh y)) d s) d := by
  apply gaussianAverage_hasDerivAt_mean (by fun_prop) (by fun_prop)
    (C := 2) (C' := 3)
  · intro y
    convert! (hasDerivAt_tanh y).sub ((hasDerivAt_tanh y).pow 2) using 1
    all_goals try with_reducible_and_instances rfl
    ring
  · intro y
    calc
      ‖tanh y-tanh y^2‖ ≤ ‖tanh y‖+‖tanh y^2‖ := norm_sub_le _ _
      _ ≤ 2 := by
        rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (tanh y))]
        linarith [(abs_tanh_lt_one y).le, (tanh_sq_lt_one y).le]
  · intro y
    rw [norm_mul]
    have h1 : ‖1-tanh y^2‖ ≤ 1 := by
      rw [Real.norm_eq_abs, abs_le]; constructor <;> nlinarith [tanh_sq_lt_one y, sq_nonneg (tanh y)]
    have h2 : ‖1-2*tanh y‖ ≤ 3 := by
      have ht := (abs_le.mp (abs_tanh_lt_one y).le)
      rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith
    exact (mul_le_mul h1 h2 (norm_nonneg _) (by norm_num)).trans_eq (by norm_num)

end SKGap

namespace SKGap
open Filter
open scoped Topology

lemma gaussian_mean_lipschitz (s : ℝ) : LipschitzWith 1 (fun d => gaussianAverage tanh d s) := by
  apply lipschitzWith_of_nnnorm_deriv_le
    (fun d => (gaussianAverage_tanh_mean_deriv d s).differentiableAt)
  intro d
  rw [(gaussianAverage_tanh_mean_deriv d s).deriv]
  have hm (y : ℝ) : 0 ≤ 1-tanh y^2 ∧ 1-tanh y^2 ≤ 1 :=
    ⟨sub_nonneg.mpr (tanh_sq_lt_one y).le, by nlinarith [sq_nonneg (tanh y)]⟩
  have hlo : 0 ≤ gaussianAverage (fun y => 1-tanh y^2) d s :=
    MeasureTheory.integral_nonneg (f := fun x => 1-tanh (d+sqrt s*x)^2) (fun x => (hm _).1)
  have hhi : gaussianAverage (fun y => 1-tanh y^2) d s ≤ 1 := by
    have hi := integrable_gaussian_comp_of_bound (f := fun y => 1-tanh y^2) (by fun_prop)
      (C := 1) (fun y => by rw [Real.norm_eq_abs, abs_of_nonneg (hm y).1]; exact (hm y).2) d s
    have h := integral_mono hi (integrable_const 1) (fun x => (hm _).2)
    simpa [gaussianAverage] using h
  exact_mod_cast (show ‖gaussianAverage (fun y => 1-tanh y^2) d s‖ ≤ 1 by
    rw [Real.norm_eq_abs, abs_of_nonneg hlo]; exact hhi)

lemma gaussian_mean_zero (s : ℝ) : gaussianAverage tanh 0 s = 0 := by
  have hn : HasLaw (fun x : ℝ => -x) (gaussianReal 0 1) (gaussianReal 0 1) := by
    simpa only [neg_zero, Pi.neg_def, id_eq] using gaussianReal_neg (HasLaw.id (μ := gaussianReal 0 1))
  have h := hn.integral_comp (f := fun x => tanh (sqrt s*x)) (by fun_prop)
  simp only [Function.comp_def, mul_neg, tanh_neg, integral_neg] at h
  dsimp [gaussianAverage]
  simp only [zero_add]
  linarith

lemma gaussian_mean_fixed_nonneg {j t d s : ℝ} (hj : 0 < j) (hj1 : j < 1) (ht : 0 ≤ t)
    (hd : d = t+j*gaussianAverage tanh d s) : 0 ≤ d := by
  by_contra hh
  have hdneg : d < 0 := lt_of_not_ge hh
  have h := (gaussian_mean_lipschitz s).dist_le_mul d 0
  rw [gaussian_mean_zero, dist_zero_right, NNReal.coe_one, one_mul, dist_zero_right,
    Real.norm_eq_abs, Real.norm_eq_abs, abs_of_neg hdneg] at h
  have hm := (abs_le.mp h).1
  have hmul := mul_le_mul_of_nonneg_left hm hj.le
  nlinarith

lemma gaussian_H_derivative_bounds {d s : ℝ} (hd : 0 ≤ d) (hs : 0 ≤ s) :
    -1 ≤ gaussianAverage (fun y => (1-tanh y^2)*(1-2*tanh y)) d s ∧
      gaussianAverage (fun y => (1-tanh y^2)*(1-2*tanh y)) d s ≤ 1 := by
  rw [gaussianAverage_eq_integral (by fun_prop) d hs]
  have he (y : ℝ) : (1-tanh y^2)*(1-2*tanh y) = (1-tanh y^2)-2*oddVariance y := by
    dsimp [oddVariance]; ring
  have hi : Integrable (fun y => (1-tanh y^2)*(1-2*tanh y)) (gaussianReal d s.toNNReal) := by
    simp_rw [he]
    exact ((integrable_const 1).sub integrable_tanh_sq).sub (integrable_oddVariance.const_mul 2)
  constructor
  · have hp (y : ℝ) : -1 ≤ (1-tanh y^2)*(1-2*tanh y) := by
      have hm := (abs_le.mp (abs_tanh_lt_one y).le)
      have hv : 0 ≤ 1-tanh y^2 := sub_nonneg.mpr (tanh_sq_lt_one y).le
      have h1 : -1 ≤ 1-2*tanh y := by linarith
      have h2 := mul_le_mul_of_nonneg_left h1 hv
      nlinarith [sq_nonneg (tanh y)]
    have h := integral_mono (integrable_const (-1)) hi hp
    simpa using h
  · simp_rw [he]
    rw [integral_sub (f := fun y => 1-tanh y^2) (g := fun y => 2*oddVariance y)
      ((integrable_const 1).sub (integrable_tanh_sq (P := gaussianReal d s.toNNReal)))
      (integrable_oddVariance.const_mul 2),
      integral_sub (integrable_const 1) (integrable_tanh_sq (P := gaussianReal d s.toNNReal)),
      integral_const_mul, integral_const]
    simp only [probReal_univ, smul_eq_mul, one_mul]
    have ho := gaussian_odd_sign hd s.toNNReal
    have hq : 0 ≤ ∫ y, tanh y^2 ∂gaussianReal d s.toNNReal :=
      MeasureTheory.integral_nonneg (f := fun y => tanh y^2) (fun y => sq_nonneg _)
    linarith

lemma gaussian_H_lipschitz {s : ℝ} (hs : 0 ≤ s) :
    LipschitzOnWith 1 (fun d => gaussianAverage (fun y => tanh y-tanh y^2) d s) (Ici 0) := by
  apply Convex.lipschitzOnWith_of_nnnorm_deriv_le
    (fun d _ => (gaussianAverage_tanh_diff_deriv d s).differentiableAt) _ (convex_Ici 0)
  intro d hd
  rw [(gaussianAverage_tanh_diff_deriv d s).deriv]
  exact_mod_cast (show ‖gaussianAverage (fun y => (1-tanh y^2)*(1-2*tanh y)) d s‖ ≤ 1 by
    rw [Real.norm_eq_abs, abs_le]; exact gaussian_H_derivative_bounds hd hs)

lemma gaussian_H_diagonal_zero {s : ℝ} (hs : 0 ≤ s) :
    gaussianAverage (fun y => tanh y-tanh y^2) s s = 0 := by
  rw [gaussianAverage_eq_integral (by fun_prop) s hs,
    integral_sub integrable_tanh integrable_tanh_sq]
  have he := gaussian_nishimori s.toNNReal
  rw [Real.coe_toNNReal _ hs] at he
  exact sub_eq_zero.mpr he

lemma consistent_gaussian_diagonal {j t d : ℝ} {s : ℝ≥0}
    (hj : 0 < j) (hj1 : j < 1) (ht : 0 ≤ t)
    (hd : d = t+j*(∫ y, tanh y ∂gaussianReal d s))
    (hs : (s:ℝ) = t+j*(∫ y, tanh y^2 ∂gaussianReal d s)) : d = s := by
  have he (f : ℝ → ℝ) (hf : Continuous f) : gaussianAverage f d s = ∫ y, f y ∂gaussianReal d s := by
    simpa only [Real.toNNReal_coe] using gaussianAverage_eq_integral hf d s.coe_nonneg
  have hd0 := gaussian_mean_fixed_nonneg hj hj1 ht (hd.trans (by rw [he tanh continuous_tanh]))
  have h := (gaussian_H_lipschitz s.coe_nonneg).dist_le_mul d hd0 s s.coe_nonneg
  rw [gaussian_H_diagonal_zero s.coe_nonneg, dist_zero_right, NNReal.coe_one, one_mul,
    Real.norm_eq_abs, Real.dist_eq] at h
  have hdiff : d-(s:ℝ) = j*gaussianAverage (fun y => tanh y-tanh y^2) d s := by
    rw [he _ (by fun_prop), integral_sub integrable_tanh integrable_tanh_sq]
    linarith
  have ha := congrArg abs hdiff
  rw [abs_mul, abs_of_pos hj] at ha
  have hh : |gaussianAverage (fun y => tanh y-tanh y^2) d s| = 0 := by
    nlinarith [abs_nonneg (gaussianAverage (fun y => tanh y-tanh y^2) d s)]
  have hz := abs_eq_zero.mp hh
  rw [hz, mul_zero] at hdiff
  exact sub_eq_zero.mp hdiff

end SKGap

namespace SKGap

lemma scalarFixedPoint_spec {j t : ℝ} (hj : 0 < j) (hj1 : j < 1) (ht : 0 ≤ t) :
    0 ≤ scalarFixedPoint j t ∧ scalarFixedPoint j t = t+j*gaussianF (scalarFixedPoint j t) := by
  simp only [scalarFixedPoint, dite_eq_left (show 0 < j ∧ j < 1 ∧ 0 ≤ t from ⟨hj, hj1, ht⟩)]
  exact (exists_gaussian_fixed hj hj1 ht).choose_spec.1

lemma consistent_gaussian_unique {j t d : ℝ} {s : ℝ≥0}
    (hj : 0 < j) (hj1 : j < 1) (ht : 0 ≤ t)
    (hd : d = t+j*(∫ y, tanh y ∂gaussianReal d s))
    (hs : (s:ℝ) = t+j*(∫ y, tanh y^2 ∂gaussianReal d s)) :
    d = scalarFixedPoint j t ∧ (s:ℝ) = scalarFixedPoint j t := by
  have hds := consistent_gaussian_diagonal hj hj1 ht hd hs
  have he : (s:ℝ) = t+j*gaussianF s := by
    rw [hds] at hd
    rw [gaussianF, gaussianAverage_eq_integral continuous_tanh _ s.coe_nonneg,
      Real.toNNReal_coe]
    exact hd
  have hroot := scalarFixedPoint_spec hj hj1 ht
  have hh := gaussian_fixed_unique hj hj1 s.coe_nonneg hroot.1 he hroot.2
  exact ⟨hds.trans hh, hh⟩

end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ074_CM.SKGap_Entropy_EntropyTransport
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Real Set Filter
open scoped NNReal ENNReal Topology
namespace SKGap

theorem entropyTransport_hasDerivAt (u y : ℝ) :
    HasDerivAt (entropyTransport u) (entropyTransportDeriv u y) y := by
  exact (hasDerivAt_id y).sub ((hasDerivAt_tanh y).const_mul u)

theorem entropyTransportDeriv_pos {u : ℝ} (hu : u < 1) (y : ℝ) :
    0 < entropyTransportDeriv u y := by
  have hm := tanh_sq_lt_one y
  have hm0 := sq_nonneg (tanh y)
  dsimp [entropyTransportDeriv]
  by_cases hu0 : 0 ≤ u
  · nlinarith
  · nlinarith

theorem entropyTransport_strictMono {u : ℝ} (hu : u < 1) :
    StrictMono (entropyTransport u) :=
  strictMono_of_hasDerivAt_pos (entropyTransport_hasDerivAt u) (entropyTransportDeriv_pos hu)

theorem entropyTransport_continuous (u : ℝ) : Continuous (entropyTransport u) :=
  continuous_iff_continuousAt.mpr (fun y => (entropyTransport_hasDerivAt u y).continuousAt)

theorem entropyTransport_sub_abs_le (u y : ℝ) : |entropyTransport u y - y| ≤ |u| := by
  calc
    _ = |u| * |tanh y| := by simp [entropyTransport, abs_mul]
    _ ≤ |u| * 1 := mul_le_mul_of_nonneg_left (abs_tanh_lt_one y).le (abs_nonneg _)
    _ = _ := mul_one _

theorem entropyTransport_surjective (u : ℝ) : Function.Surjective (entropyTransport u) := by
  apply (entropyTransport_continuous u).surjective
  · apply tendsto_atTop_mono' atTop (Eventually.of_forall (fun y => ?_))
      (tendsto_atTop_add_const_right atTop (-|u|) tendsto_id)
    have h := (abs_le.mp (entropyTransport_sub_abs_le u y)).1
    dsimp [id]
    linarith
  · apply tendsto_atBot_mono' atBot (Eventually.of_forall (fun y => ?_))
      (tendsto_atBot_add_const_right atBot |u| tendsto_id)
    have h := (abs_le.mp (entropyTransport_sub_abs_le u y)).2
    dsimp [id]
    linarith

theorem log_entropyTransportDeriv_lower {u : ℝ} (hu : u < 1) (y : ℝ) :
    (1 - tanh y ^ 2) * log (1 - u) ≤ log (entropyTransportDeriv u y) := by
  have hm0 := sq_nonneg (tanh y)
  have hm1 := (tanh_sq_lt_one y).le
  have h := strictConcaveOn_log_Ioi.concaveOn.2 (show 0 < (1 : ℝ) by norm_num)
    (show 0 < 1 - u by linarith) hm0 (sub_nonneg.mpr hm1)
    (show tanh y ^ 2 + (1 - tanh y ^ 2) = 1 by ring)
  simp only [smul_eq_mul, log_one, mul_zero, zero_add] at h
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  dsimp [entropyTransportDeriv]
  ring

theorem entropyTransportDeriv_bounds {u : ℝ} (_hu : u < 1) (y : ℝ) :
    min 1 (1 - u) ≤ entropyTransportDeriv u y ∧
      entropyTransportDeriv u y ≤ max 1 (1 - u) := by
  have hm0 := sq_nonneg (tanh y)
  have hm1 := (tanh_sq_lt_one y).le
  dsimp [entropyTransportDeriv]
  by_cases hu0 : 0 ≤ u
  · rw [min_eq_right (by linarith), max_eq_left (by linarith)]
    constructor <;> nlinarith
  · rw [min_eq_left (by linarith), max_eq_right (by linarith)]
    constructor <;> nlinarith

theorem integrable_log_entropyTransportDeriv {P : Measure ℝ} [IsFiniteMeasure P]
    {u : ℝ} (hu : u < 1) : Integrable (fun y => log (entropyTransportDeriv u y)) P := by
  have hm : Continuous (fun y => log (entropyTransportDeriv u y)) := by
    apply Continuous.log
    · unfold entropyTransportDeriv
      fun_prop
    · exact fun y => (entropyTransportDeriv_pos hu y).ne'
  apply Integrable.of_bound hm.aestronglyMeasurable
    (|log (min 1 (1 - u))| + |log (max 1 (1 - u))|)
  apply ae_of_all
  intro y
  have hp : 0 < min 1 (1 - u) := lt_min (by norm_num) (by linarith)
  have hlo := log_le_log hp (entropyTransportDeriv_bounds hu y).1
  have hhi := log_le_log (entropyTransportDeriv_pos hu y)
    (entropyTransportDeriv_bounds hu y).2
  rw [Real.norm_eq_abs, abs_le]
  constructor <;> linarith [neg_abs_le (log (min 1 (1 - u))),
    le_abs_self (log (max 1 (1 - u))), abs_nonneg (log (min 1 (1 - u))),
    abs_nonneg (log (max 1 (1 - u)))]

theorem integrable_sub_mul_tanh {P : Measure ℝ} [IsFiniteMeasure P]
    (hP : Integrable id P) (d : ℝ) : Integrable (fun y => (y - d) * tanh y) P := by
  simpa only [Pi.sub_apply, id_eq, mul_comm] using
    (hP.sub (integrable_const d)).bdd_mul continuous_tanh.aestronglyMeasurable
      (ae_of_all _ (fun y => by simpa using (abs_tanh_lt_one y).le))

theorem integrable_entropyTransportLog {P : Measure ℝ} [IsFiniteMeasure P]
    (hP : Integrable id P) {u : ℝ} (hu : u < 1) (d s : ℝ) :
    Integrable (entropyTransportLog u d s) P :=
  (((integrable_sub_mul_tanh hP d).const_mul (u / s)).sub
    (integrable_tanh_sq.const_mul (u ^ 2 / (2 * s)))).add
      (integrable_log_entropyTransportDeriv hu)

theorem gaussianPDF_mul_exp_transport {u d : ℝ} {s : ℝ≥0} (hu : u < 1) (y : ℝ) :
    gaussianPDFReal d s y * exp (entropyTransportLog u d s y) =
      entropyTransportDeriv u y * gaussianPDFReal d s (entropyTransport u y) := by
  unfold gaussianPDFReal entropyTransportLog
  rw [exp_add, exp_log (entropyTransportDeriv_pos hu y)]
  calc
    _ = entropyTransportDeriv u y * (1 / sqrt (2 * π * (s : ℝ))) *
      (exp (-(y - d) ^ 2 / (2 * (s : ℝ))) *
       exp (u / (s : ℝ) * ((y - d) * tanh y) - u ^ 2 / (2 * (s : ℝ)) * tanh y ^ 2)) := by ring
    _ = _ := by
      rw [← exp_add]
      rw [mul_assoc]
      have he : -(y - d) ^ 2 / (2 * (s : ℝ)) +
        (u / (s : ℝ) * ((y - d) * tanh y) - u ^ 2 / (2 * (s : ℝ)) * tanh y ^ 2) =
        -(entropyTransport u y - d) ^ 2 / (2 * (s : ℝ)) := by
          unfold entropyTransport
          ring
      rw [he]
      simp only [one_div]

theorem integrable_exp_entropyTransportLog {u d : ℝ} {s : ℝ≥0}
    (hu : u < 1) (hs : s ≠ 0) :
    Integrable (fun y => exp (entropyTransportLog u d s y)) (gaussianReal d s) := by
  rw [integrable_gaussian_iff hs]
  simp_rw [gaussianPDF_mul_exp_transport hu]
  have heq : entropyTransport u '' univ = univ := (by rw [Set.image_univ, Set.range_eq_univ.mpr (entropyTransport_surjective u)] : entropyTransport u '' univ = univ)
  have h := (integrableOn_image_iff_integrableOn_deriv_smul_of_monotoneOn MeasurableSet.univ
    (fun x _ => (entropyTransport_hasDerivAt u x).hasDerivWithinAt)
    ((entropyTransport_strictMono hu).monotone.monotoneOn univ) (gaussianPDFReal d s)).mp
  rw [heq, integrableOn_univ, integrableOn_univ] at h
  simpa only [smul_eq_mul] using h (integrable_gaussianPDFReal d s)

theorem integral_exp_entropyTransportLog {u d : ℝ} {s : ℝ≥0}
    (hu : u < 1) (hs : s ≠ 0) :
    (∫ y, exp (entropyTransportLog u d s y) ∂gaussianReal d s) = 1 := by
  rw [integral_gaussianReal_eq_integral_smul hs]
  simp only [smul_eq_mul]
  simp_rw [gaussianPDF_mul_exp_transport hu]
  have h := integral_image_eq_integral_deriv_smul_of_monotoneOn MeasurableSet.univ
    (fun x _ => (entropyTransport_hasDerivAt u x).hasDerivWithinAt)
    ((entropyTransport_strictMono hu).monotone.monotoneOn univ) (gaussianPDFReal d s)
  rw [(by rw [Set.image_univ, Set.range_eq_univ.mpr (entropyTransport_surjective u)] : entropyTransport u '' univ = univ)] at h
  simp only [Measure.restrict_univ, smul_eq_mul, integral_gaussianPDFReal_eq_one d hs] at h
  exact h.symm

theorem log_gaussianPDFReal {d : ℝ} {s : ℝ≥0} (hs : s ≠ 0) (y : ℝ) :
    log (gaussianPDFReal d s y) = -log (2 * π * (s : ℝ)) / 2 -
      (y - d) ^ 2 / (2 * (s : ℝ)) := by
  have hsp : 0 < (s : ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hs)
  have hp : 0 < 2 * π * (s : ℝ) := by positivity
  unfold gaussianPDFReal
  rw [log_mul (by positivity) (exp_pos _).ne', log_inv, log_sqrt hp.le, log_exp]
  ring

theorem gaussianRatioLog_formula {d : ℝ} {s r : ℝ≥0} (hs : s ≠ 0) (hr : r ≠ 0) (y : ℝ) :
    gaussianRatioLog d s r y = (log (s : ℝ) - log (r : ℝ)) / 2 +
      (1 / (2 * (s : ℝ)) - 1 / (2 * (r : ℝ))) * (y - d) ^ 2 := by
  have hsp : (s : ℝ) ≠ 0 := NNReal.coe_ne_zero.mpr hs
  have hrp : (r : ℝ) ≠ 0 := NNReal.coe_ne_zero.mpr hr
  rw [gaussianRatioLog, log_gaussianPDFReal hr, log_gaussianPDFReal hs,
    log_mul (by positivity : (2 : ℝ) * π ≠ 0) hrp,
    log_mul (by positivity : (2 : ℝ) * π ≠ 0) hsp]
  ring

theorem gaussianPDF_mul_exp_ratio {d : ℝ} {s r : ℝ≥0} (hs : s ≠ 0) (hr : r ≠ 0) (y : ℝ) :
    gaussianPDFReal d s y * exp (gaussianRatioLog d s r y) = gaussianPDFReal d r y := by
  rw [gaussianRatioLog, exp_sub, exp_log (gaussianPDFReal_pos d r y hr),
    exp_log (gaussianPDFReal_pos d s y hs)]
  exact mul_div_cancel₀ _ (gaussianPDFReal_pos d s y hs).ne'

theorem integrable_gaussianRatioLog {P : Measure ℝ} [IsFiniteMeasure P]
    {d : ℝ} {s r : ℝ≥0} (hs : s ≠ 0) (hr : r ≠ 0)
    (hP : Integrable (fun y => (y - d) ^ 2) P) : Integrable (gaussianRatioLog d s r) P := by
  change Integrable (fun y => gaussianRatioLog d s r y) P
  simp_rw [gaussianRatioLog_formula hs hr]
  exact (integrable_const ((log (s : ℝ) - log (r : ℝ)) / 2)).add (hP.const_mul _)

theorem integrable_exp_gaussianRatioLog {d : ℝ} {s r : ℝ≥0} (hs : s ≠ 0) (hr : r ≠ 0) :
    Integrable (fun y => exp (gaussianRatioLog d s r y)) (gaussianReal d s) := by
  rw [integrable_gaussian_iff hs]
  simp_rw [gaussianPDF_mul_exp_ratio hs hr]
  exact integrable_gaussianPDFReal d r

theorem integral_exp_gaussianRatioLog {d : ℝ} {s r : ℝ≥0} (hs : s ≠ 0) (hr : r ≠ 0) :
    (∫ y, exp (gaussianRatioLog d s r y) ∂gaussianReal d s) = 1 := by
  rw [integral_gaussianReal_eq_integral_smul hs]
  simp only [smul_eq_mul]
  simp_rw [gaussianPDF_mul_exp_ratio hs hr]
  exact integral_gaussianPDFReal_eq_one d hr

theorem secondMoment_integrable {P : Measure ℝ} [IsFiniteMeasure P]
    (hP : Integrable (fun y : ℝ => y ^ 2) P) : Integrable id P := by
  exact ((memLp_two_iff_integrable_sq (by fun_prop : AEStronglyMeasurable id P)).mpr hP).integrable (by norm_num)

theorem centered_secondMoment_integrable {P : Measure ℝ} [IsFiniteMeasure P]
    (hP : Integrable (fun y : ℝ => y ^ 2) P) (d : ℝ) :
    Integrable (fun y => (y - d) ^ 2) P := by
  have hm : MemLp id 2 P := (memLp_two_iff_integrable_sq (by fun_prop)).mpr hP
  exact (memLp_two_iff_integrable_sq (by fun_prop : AEStronglyMeasurable (fun y : ℝ => y - d) P)).mp
    (hm.sub (memLp_const d))

theorem entropy_q_lt_one {P : Measure ℝ} [IsProbabilityMeasure P] :
    (∫ y, tanh y ^ 2 ∂P) < 1 := by
  have hi : Integrable (fun y : ℝ => 1 - tanh y ^ 2) P := (integrable_const 1).sub integrable_tanh_sq
  have hsupp : Function.support (fun y : ℝ => 1 - tanh y ^ 2) = univ := by
    ext y
    simp only [Function.mem_support, mem_univ, iff_true]
    exact (sub_pos.mpr (tanh_sq_lt_one y)).ne'
  have hp := (integral_pos_iff_support_of_nonneg (fun y => (sub_pos.mpr (tanh_sq_lt_one y)).le) hi).mpr
    (by rw [hsupp]; simp)
  rw [integral_sub (integrable_const 1) integrable_tanh_sq] at hp
  simpa using hp

theorem entropy_moment_cauchy {P : Measure ℝ} [IsProbabilityMeasure P]
    (hP : Integrable (fun y : ℝ => y ^ 2) P) (d : ℝ)
    (hq : 0 < ∫ y, tanh y ^ 2 ∂P) :
    (∫ y, (y - d) * tanh y ∂P) ^ 2 ≤
      (∫ y, tanh y ^ 2 ∂P) * (∫ y, (y - d) ^ 2 ∂P) := by
  let a := ∫ y, (y - d) * tanh y ∂P
  let q := ∫ y, tanh y ^ 2 ∂P
  have hp : 0 ≤ ∫ y : ℝ, ((y - d) - (a / q) * tanh y) ^ 2 ∂P :=
    integral_nonneg (fun y => sq_nonneg _)
  have he (y : ℝ) : ((y - d) - (a / q) * tanh y) ^ 2 =
      (y - d) ^ 2 - (2 * a / q) * ((y - d) * tanh y) + (a / q) ^ 2 * tanh y ^ 2 := by ring
  simp_rw [he] at hp
  have hv := centered_secondMoment_integrable hP d
  have ha := integrable_sub_mul_tanh (secondMoment_integrable hP) d
  rw [integral_add (f := fun y => (y - d) ^ 2 - (2 * a / q) * ((y - d) * tanh y))
      (hv.sub (ha.const_mul (2 * a / q))) (integrable_tanh_sq.const_mul ((a / q) ^ 2)),
    integral_sub hv (ha.const_mul (2 * a / q)), integral_const_mul, integral_const_mul] at hp
  change 0 ≤ (∫ y, (y - d) ^ 2 ∂P) - 2 * a / q * a + (a / q) ^ 2 * q at hp
  have hqp : 0 < q := hq
  have hm := mul_nonneg hp hqp.le
  field_simp at hm
  dsimp [a, q] at hm
  nlinarith

end SKGap

end
end

end OAI
end

section
-- module Solutions.OAIQ074_CM.SKGap_Entropy_ScalarEntropyTarget
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Real Set Filter
open scoped NNReal ENNReal Topology
noncomputable section
open Real Set

noncomputable section
open MeasureTheory ProbabilityTheory Real Set Filter
open scoped Topology NNReal ENNReal BoundedContinuousFunction
namespace SKGap

lemma realClip_abs (n : ℕ) (x : ℝ) : |realClip n x| ≤ |x| := by
  rw [abs_le]
  constructor
  · exact le_sup_of_le_right (le_min (by linarith [abs_nonneg x]) (neg_abs_le x))
  · exact sup_le (by linarith [abs_nonneg x]) ((min_le_right _ _).trans (le_abs_self x))

lemma realClip_le (n : ℕ) (x : ℝ) : realClip n x ≤ max 0 x :=
  max_le (by linarith [le_max_left (0:ℝ) x]) ((min_le_right _ _).trans (le_max_right _ _))

lemma tendsto_realClip (x : ℝ) : Tendsto (fun n : ℕ => realClip n x) atTop (𝓝 x) := by
  have he : ∀ᶠ n : ℕ in atTop, realClip n x = x := by
    obtain ⟨N, hN⟩ := exists_nat_ge |x|
    filter_upwards [eventually_ge_atTop N] with n hn
    have hb : |x| ≤ (n:ℝ) := hN.trans (by exact_mod_cast hn)
    have hx := abs_le.mp hb
    simp only [realClip, min_eq_right hx.2, max_eq_right hx.1]
  exact (tendsto_congr' he).2 tendsto_const_nhds

lemma entropyTestBound_continuous {P Q : Measure ℝ} [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] {D : ℝ} (hD : EntropyTestBound P Q D)
    {f : ℝ → ℝ} (hf : Continuous f) (hi : Integrable f P)
    (he : Integrable (fun x => exp (f x)) Q) :
    (∫ x, f x ∂P) - log (∫ x, exp (f x) ∂Q) ≤ D := by
  have hP : Tendsto (fun n => ∫ x, clippedBC hf n x ∂P) atTop (𝓝 (∫ x, f x ∂P)) := by
    apply tendsto_integral_of_dominated_convergence (fun x => |f x|)
    · intro n; exact (clippedBC hf n).continuous.aestronglyMeasurable
    · exact hi.abs
    · intro n; exact ae_of_all _ (fun x => by
        change ‖realClip n (f x)‖ ≤ |f x|
        rw [Real.norm_eq_abs]; exact realClip_abs n (f x))
    · exact ae_of_all _ (fun x => tendsto_realClip (f x))
  have hQ : Tendsto (fun n => ∫ x, exp (clippedBC hf n x) ∂Q) atTop (𝓝 (∫ x, exp (f x) ∂Q)) := by
    apply tendsto_integral_of_dominated_convergence (fun x => 1+exp (f x))
    · intro n; exact (by fun_prop : Continuous (fun x => exp (clippedBC hf n x))).aestronglyMeasurable
    · exact (integrable_const 1).add he
    · intro n; exact ae_of_all _ (fun x => by
        rw [Real.norm_eq_abs, abs_of_pos (exp_pos _)]
        calc
          _ ≤ exp (max 0 (f x)) := exp_le_exp.mpr (realClip_le n (f x))
          _ ≤ 1+exp (f x) := by
            by_cases hx : 0 ≤ f x
            · rw [max_eq_right hx]; linarith
            · rw [max_eq_left (le_of_not_ge hx), exp_zero]; linarith [exp_pos (f x)])
    · exact ae_of_all _ (fun x => continuous_exp.continuousAt.tendsto.comp (tendsto_realClip (f x)))
  have hpos : 0 < ∫ x, exp (f x) ∂Q := integral_pos_iff_support_of_nonneg
    (fun x => (exp_pos (f x)).le) he |>.mpr (by simp [Function.support, (exp_pos _).ne'])
  exact le_of_tendsto (hP.sub ((continuousAt_log hpos.ne').tendsto.comp hQ))
    (Eventually.of_forall (fun n => hD (clippedBC hf n)))

lemma entropyTestBound_normalized {P Q : Measure ℝ} [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] {D : ℝ} (hD : EntropyTestBound P Q D)
    {f : ℝ → ℝ} (hf : Continuous f) (hi : Integrable f P)
    (he : Integrable (fun x => exp (f x)) Q) (hZ : ∫ x, exp (f x) ∂Q = 1) :
    (∫ x, f x ∂P) ≤ D := by
  simpa only [hZ, log_one, sub_zero] using entropyTestBound_continuous hD hf hi he

lemma integrable_exp_boundedContinuous {Q : Measure ℝ} [IsFiniteMeasure Q] (f : ℝ →ᵇ ℝ) (t : ℝ) :
    Integrable (fun x => exp (t*f x)) Q := by
  apply Integrable.of_bound (by fun_prop) (exp (|t| * ‖f‖))
  exact ae_of_all _ (fun x => by
    rw [Real.norm_eq_abs, abs_of_pos (exp_pos _)]
    apply exp_le_exp.mpr
    calc
      t*f x ≤ |t*f x| := le_abs_self _
      _ = |t| * |f x| := abs_mul _ _
      _ ≤ |t| * ‖f‖ := mul_le_mul_of_nonneg_left (by simpa only [Real.norm_eq_abs] using f.norm_coe_le_norm x) (abs_nonneg _))

lemma boundedContinuous_mgf_deriv {Q : Measure ℝ} [IsProbabilityMeasure Q] (f : ℝ →ᵇ ℝ) :
    HasDerivAt (fun t : ℝ => ∫ x, exp (t*f x) ∂Q) (∫ x, f x ∂Q) 0 := by
  have hset : integrableExpSet (fun x => f x) Q = univ := by
    ext t; exact iff_true_intro (integrable_exp_boundedContinuous f t)
  have h := hasDerivAt_mgf (X := fun x => f x) (μ := Q) (t := 0) (by simp [hset])
  convert! h using 1; simp

lemma entropyTestBound_zero_eq {P Q : Measure ℝ} [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] (hD : EntropyTestBound P Q 0) : P = Q := by
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro f
  let g : ℝ → ℝ := fun t => log (∫ x, exp (t*f x) ∂Q) - t*(∫ x, f x ∂P)
  have hg0 : g 0 = 0 := by simp [g]
  have hmin : IsLocalMin g 0 := by
    apply Filter.Eventually.of_forall
    intro t
    have h := hD (t • f)
    simp only [BoundedContinuousFunction.smul_apply, smul_eq_mul, integral_const_mul] at h
    rw [hg0]
    dsimp [g]
    exact (show 0 ≤ log (∫ x, exp (t*f x) ∂Q)-t*(∫ x, f x ∂P) by linarith)
  have hder : HasDerivAt g ((∫ x, f x ∂Q)-(∫ x, f x ∂P)) 0 := by
    have h := (boundedContinuous_mgf_deriv (Q := Q) f).log (by simp)
    convert! h.sub ((hasDerivAt_id (0:ℝ)).mul_const (∫ x, f x ∂P)) using 1; simp
  have hz := hmin.hasDerivAt_eq_zero hder
  linarith

lemma entropyTestBound_nonneg {P Q : Measure ℝ} [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] {D : ℝ} (hD : EntropyTestBound P Q D) : 0 ≤ D := by
  simpa using hD 0

end SKGap

end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ074_CM.SKGap_Entropy_EntropyTestBoundQPos
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Real Set Filter
open scoped NNReal ENNReal Topology
noncomputable section
open Real Set
noncomputable section
open MeasureTheory ProbabilityTheory Real Set Filter
open scoped Topology NNReal ENNReal BoundedContinuousFunction
namespace SKGap

lemma entropyTestBound_q_pos {P : Measure ℝ} [IsProbabilityMeasure P]
    {d D : ℝ} {s : ℝ≥0} (hs : s ≠ 0) (hD : EntropyTestBound P (gaussianReal d s) D) :
    0 < ∫ y, tanh y^2 ∂P := by
  have hn : 0 ≤ ∫ y, tanh y^2 ∂P := integral_nonneg (fun y => sq_nonneg (tanh y))
  by_contra hh
  have hzero : (∫ y, tanh y^2 ∂P) = 0 := le_antisymm (le_of_not_gt hh) hn
  let F : ℕ → ℝ → ℝ := fun n y => exp (-(n:ℝ)*tanh y^2)
  have hFn (n : ℕ) (y : ℝ) : ‖F n y‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_of_pos (exp_pos _)]
    exact exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Nat.cast_nonneg n)) (sq_nonneg _))
  have hFi (n : ℕ) : Integrable (F n) (gaussianReal d s) :=
    Integrable.of_bound (by dsimp [F]; fun_prop) 1 (ae_of_all _ (hFn n))
  have h_lower (n : ℕ) : exp (-D) ≤ ∫ y, F n y ∂gaussianReal d s := by
    have h := entropyTestBound_continuous hD (f := fun y => -(n:ℝ)*tanh y^2)
      (by fun_prop) (integrable_tanh_sq.const_mul _) (hFi n)
    rw [integral_const_mul, hzero, mul_zero, zero_sub] at h
    have hz := integral_exp_pos (hFi n)
    calc
      _ ≤ exp (log (∫ y, F n y ∂gaussianReal d s)) := exp_le_exp.mpr (by linarith)
      _ = _ := exp_log hz
  have := nullSingletonClass_gaussianReal (μ := d) hs
  have hlim : Tendsto (fun n => ∫ y, F n y ∂gaussianReal d s) atTop (𝓝 0) := by
    have hh : Tendsto (fun n => ∫ y, F n y ∂gaussianReal d s) atTop
        (𝓝 (∫ _ : ℝ, (0:ℝ) ∂gaussianReal d s)) := by
      apply tendsto_integral_of_dominated_convergence (fun _ => (1:ℝ))
      · intro n; exact (hFi n).aestronglyMeasurable
      · exact integrable_const 1
      · intro n; exact ae_of_all _ (hFn n)
      · filter_upwards [(gaussianReal d s).ae_ne 0] with y hy
        have hm : tanh y ≠ 0 := fun hz => hy (tanh_injective (by simpa only [tanh_zero] using hz))
        have hc : 0 < tanh y^2 := sq_pos_of_ne_zero hm
        have hnat : Tendsto (fun n : ℕ => (n:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
        have hneg := tendsto_neg_atTop_atBot.comp (hnat.atTop_mul_const hc)
        exact tendsto_exp_atBot.comp (by simpa only [Function.comp_def, neg_mul] using hneg)
    simpa using hh
  have hle := ge_of_tendsto hlim (Eventually.of_forall h_lower)
  exact (not_le_of_gt (exp_pos (-D))) hle

@[fun_prop] lemma continuous_entropyTransportLog {u d s : ℝ} (hu : u < 1) :
    Continuous (entropyTransportLog u d s) := by
  have hc : Continuous (entropyTransportDeriv u) := by unfold entropyTransportDeriv; fun_prop
  have hl := hc.log (fun y => (entropyTransportDeriv_pos hu y).ne')
  unfold entropyTransportLog
  exact ((continuous_const.mul ((continuous_id.sub continuous_const).mul continuous_tanh)).sub
    (continuous_const.mul (continuous_tanh.pow 2))).add hl

theorem test_transport_lower {P : Measure ℝ} [IsProbabilityMeasure P]
    (hP : Integrable id P) {u d : ℝ} {s : ℝ≥0} (hu : u < 1) (hs : s ≠ 0)
    {D : ℝ} (hD : EntropyTestBound P (gaussianReal d s) D) :
    u / (s : ℝ) * (∫ y, (y - d) * tanh y ∂P) -
      u ^ 2 / (2 * (s : ℝ)) * (∫ y, tanh y ^ 2 ∂P) +
      (1 - ∫ y, tanh y ^ 2 ∂P) * log (1 - u) ≤ D := by
  have hlog := integral_mono
    (((integrable_const (1 : ℝ)).sub integrable_tanh_sq).mul_const (log (1 - u)))
    (integrable_log_entropyTransportDeriv (P := P) hu) (log_entropyTransportDeriv_lower hu)
  simp only [Pi.sub_apply] at hlog
  rw [integral_mul_const, integral_sub (integrable_const 1) integrable_tanh_sq,
    integral_const, probReal_univ, smul_eq_mul, one_mul] at hlog
  have h := entropyTestBound_normalized hD (continuous_entropyTransportLog hu) (integrable_entropyTransportLog hP hu d s)
    (integrable_exp_entropyTransportLog hu hs) (integral_exp_entropyTransportLog hu hs)
  unfold entropyTransportLog at h
  rw [integral_add (f := fun y => u / (s : ℝ) * ((y - d) * tanh y) -
      u ^ 2 / (2 * (s : ℝ)) * tanh y ^ 2)
      (((integrable_sub_mul_tanh hP d).const_mul _).sub (integrable_tanh_sq.const_mul _))
      (integrable_log_entropyTransportDeriv hu),
    integral_sub ((integrable_sub_mul_tanh hP d).const_mul _) (integrable_tanh_sq.const_mul _),
    integral_const_mul, integral_const_mul] at h
  linarith

lemma continuous_gaussianRatioLog {d : ℝ} {s r : ℝ≥0} (hs : s ≠ 0) (hr : r ≠ 0) :
    Continuous (gaussianRatioLog d s r) := by
  have he : gaussianRatioLog d s r = fun y => (log (s : ℝ) - log (r : ℝ)) / 2 +
      (1 / (2 * (s : ℝ)) - 1 / (2 * (r : ℝ))) * (y - d)^2 := funext (gaussianRatioLog_formula hs hr)
  rw [he]; fun_prop

theorem test_variance_comparison {P : Measure ℝ} [IsProbabilityMeasure P]
    {d : ℝ} {s r : ℝ≥0} (hs : s ≠ 0) (hr : r ≠ 0)
    (hP : Integrable (fun y => (y - d) ^ 2) P)
    {D : ℝ} (hD : EntropyTestBound P (gaussianReal d s) D) :
    (log (s : ℝ) - log (r : ℝ)) / 2 +
      (1 / (2 * (s : ℝ)) - 1 / (2 * (r : ℝ))) * (∫ y, (y - d) ^ 2 ∂P) ≤
      D := by
  have h := entropyTestBound_normalized hD (continuous_gaussianRatioLog hs hr) (integrable_gaussianRatioLog hs hr hP)
    (integrable_exp_gaussianRatioLog hs hr) (integral_exp_gaussianRatioLog hs hr)
  simp_rw [gaussianRatioLog_formula hs hr] at h
  rw [integral_add (integrable_const _) (hP.const_mul _), integral_const_mul] at h
  simpa using h

theorem test_variance_lower {P : Measure ℝ} [IsProbabilityMeasure P]
    {d : ℝ} {s : ℝ≥0} (hs : s ≠ 0)
    (hP : Integrable (fun y => (y - d) ^ 2) P)
    {D : ℝ} (hD : EntropyTestBound P (gaussianReal d s) D) {v : ℝ} (hv : 0 < v)
    (hvar : ∫ y, (y - d) ^ 2 ∂P = (s : ℝ) * v) :
    (v - 1 - log v) / 2 ≤ D := by
  let r : ℝ≥0 := s * ⟨v, hv.le⟩
  have hr : r ≠ 0 := mul_ne_zero hs (NNReal.coe_ne_zero.mp hv.ne')
  have h := test_variance_comparison hs hr hP hD
  change (log (s : ℝ) - log ((s : ℝ) * v)) / 2 +
    (1 / (2 * (s : ℝ)) - 1 / (2 * ((s : ℝ) * v))) *
      (∫ y, (y - d) ^ 2 ∂P) ≤ _ at h
  have hsp : (s : ℝ) ≠ 0 := NNReal.coe_ne_zero.mpr hs
  rw [log_mul hsp hv.ne', hvar] at h
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  field_simp
  ring

theorem test_scalar_inequality {P : Measure ℝ} [IsProbabilityMeasure P]
    (hP : Integrable (fun y : ℝ => y ^ 2) P)
    {j d : ℝ} {s : ℝ≥0} (hj0 : 0 < j) (hj1 : j < 1) (hs : s ≠ 0)
    (hcons : j * (∫ y, tanh y ^ 2 ∂P) ≤ (s : ℝ))
    {D : ℝ} (hD : EntropyTestBound P (gaussianReal d s) D) :
    let q := ∫ y, tanh y ^ 2 ∂P
    let a := ∫ y, (y - d) * tanh y ∂P
    let T := j * (a - (s : ℝ) * (1 - q)) ^ 2 / (2 * (s : ℝ) * ((s : ℝ) + j * q))
    T ≤ D ∧
      (a ≠ (s : ℝ) * (1 - q) → T < D) := by
  dsimp only
  let q := ∫ y, tanh y ^ 2 ∂P
  let a := ∫ y, (y - d) * tanh y ∂P
  let k := j * q / (s : ℝ)
  let B := j * (1 - q)
  let C := j * a / (s : ℝ)
  have hsp : 0 < (s : ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hs)
  have hq0 : 0 < q := entropyTestBound_q_pos hs hD
  have hq1 : q < 1 := entropy_q_lt_one
  have hk0 : 0 < k := div_pos (mul_pos hj0 hq0) hsp
  have hk1 : k ≤ 1 := (div_le_one hsp).mpr hcons
  have hB0 : 0 < B := mul_pos hj0 (sub_pos.mpr hq1)
  have hB1 : B < 1 := by dsimp [B]; nlinarith
  have htransport (u : ℝ) (hu : u < 1) :
      u * (C - B) - k * u ^ 2 / 2 - B * entropyEll u ≤ j * D := by
    have h := mul_le_mul_of_nonneg_left (test_transport_lower (secondMoment_integrable hP) hu hs hD) hj0.le
    change j * (u / (s : ℝ) * a - u ^ 2 / (2 * (s : ℝ)) * q + (1 - q) * log (1 - u)) ≤ j * D at h
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    dsimp [k, B, C, entropyEll]
    field_simp
    ring
  have hvariance (hC : 1 < C) : C ^ 2 / k - 1 - log (C ^ 2 / k) ≤ 2 * (j * D) := by
    let v := (∫ y, (y - d) ^ 2 ∂P) / (s : ℝ)
    have hcauchy := entropy_moment_cauchy hP d hq0
    have hcv : C ^ 2 / (j * k) ≤ v := by
      have heq : C ^ 2 / (j * k) * (s : ℝ) = a ^ 2 / q := by
        dsimp [C, k]
        field_simp
      dsimp [v]
      rw [le_div_iff₀ hsp, heq, div_le_iff₀ hq0]
      simpa only [q, a, mul_comm] using hcauchy
    have hv : 0 < v := (div_pos (pow_pos (by linarith : 0 < C) 2) (mul_pos hj0 hk0)).trans_le hcv
    have hvar : (∫ y, (y - d) ^ 2 ∂P) = (s : ℝ) * v := by dsimp [v]; field_simp
    have hbound := test_variance_lower hs (centered_secondMoment_integrable hP d) hD hv hvar
    exact entropy_variance_scaled_lower hj0 hj1.le hk0 hk1 hC hcv hbound
  have hopt := entropy_scalar_optimization hk0 hk1 hB0 hB1
    (mul_nonneg hj0.le (entropyTestBound_nonneg hD)) htransport hvariance
  have heq : (C - B) ^ 2 / (2 * (1 + k)) =
      j * (j * (a - (s : ℝ) * (1 - q)) ^ 2 / (2 * (s : ℝ) * ((s : ℝ) + j * q))) := by
    dsimp [C, B, k]
    field_simp
  rw [heq] at hopt
  refine ⟨le_of_mul_le_mul_left hopt.1 hj0, ?_⟩
  intro ha
  have hCB : C ≠ B := by
    intro h
    apply ha
    dsimp [C, B] at h
    have he := (div_eq_iff hsp.ne').mp h
    nlinarith
  exact lt_of_mul_lt_mul_left (hopt.2 hCB) hj0.le

theorem scalar_strict_witness {P : Measure ℝ} [IsProbabilityMeasure P]
    (hP : Integrable (fun y : ℝ => y^2) P)
    {j d : ℝ} {s : ℝ≥0} (hj : 0 < j) (hj1 : j < 1) (hs : s ≠ 0)
    (hcons : j * (∫ y, tanh y^2 ∂P) ≤ (s:ℝ)) (hne : P ≠ gaussianReal d s) :
    ∃ f : ℝ →ᵇ ℝ, scalarEntropyTarget P j d s <
      (∫ y, f y ∂P) - log (∫ y, exp (f y) ∂gaussianReal d s) := by
  by_contra h
  push Not at h
  have hD : EntropyTestBound P (gaussianReal d s) (scalarEntropyTarget P j d s) := h
  have hop := test_scalar_inequality hP hj hj1 hs hcons hD
  have he : (∫ y, (y-d)*tanh y ∂P) = (s:ℝ)*(1-∫ y, tanh y^2 ∂P) := by
    by_contra hh
    exact lt_irrefl _ (hop.2 hh)
  have hzero : scalarEntropyTarget P j d s = 0 := by simp [scalarEntropyTarget, he]
  rw [hzero] at hD
  exact hne (entropyTestBound_zero_eq hD)

end SKGap

end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ074_CM.SKGap_Localization_EmpiricalLaw
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Topology Real
open scoped NNReal ENNReal BoundedContinuousFunction
namespace SKGap

variable {ι : Type*} [Fintype ι] [Nonempty ι]

lemma empiricalLaw_coe (y : ι → ℝ) : (empiricalLaw y : Measure ℝ) =
    (Fintype.card ι : ℝ≥0∞)⁻¹ • ∑ i, Measure.dirac (y i) := rfl

lemma integrable_empiricalLaw (y : ι → ℝ) (f : ℝ → ℝ) : Integrable f (empiricalLaw y : Measure ℝ) := by
  rw [empiricalLaw_coe]
  apply Integrable.smul_measure
  · exact integrable_finsetSum_measure.mpr (fun i _ => integrable_dirac (by simp))
  · exact ENNReal.inv_ne_top.mpr (by exact_mod_cast ((Fintype.card_pos (α := ι)).ne'))

lemma integral_empiricalLaw (y : ι → ℝ) (f : ℝ → ℝ) :
    (∫ x, f x ∂empiricalLaw y) = (Fintype.card ι : ℝ)⁻¹ * ∑ i, f (y i) := by
  rw [empiricalLaw_coe, integral_smul_measure,
    integral_finsetSum_measure (fun i _ => integrable_dirac (by simp))]
  simp only [integral_dirac, ENNReal.toReal_inv, ENNReal.toReal_natCast, smul_eq_mul]

lemma card_mul_integral_empiricalLaw (y : ι → ℝ) (f : ℝ → ℝ) :
    (Fintype.card ι : ℝ)*(∫ x, f x ∂empiricalLaw y) = ∑ i, f (y i) := by
  rw [integral_empiricalLaw, ← mul_assoc, mul_inv_cancel₀ (by exact_mod_cast (Fintype.card_pos (α := ι)).ne'), one_mul]

end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ074_CM.SKGap_Matrix_NormalLogConst
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Real Set Filter
open scoped NNReal ENNReal Topology
noncomputable section
open Real Set
noncomputable section
open MeasureTheory ProbabilityTheory Real Set Filter
open scoped Topology NNReal ENNReal BoundedContinuousFunction
open MeasureTheory ProbabilityTheory Filter Set Topology Real
open scoped NNReal ENNReal BoundedContinuousFunction
noncomputable section
open Set Filter Topology
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Topology Real
open scoped NNReal ENNReal BoundedContinuousFunction
namespace SKGap

variable {ι : Type*} [Fintype ι]

lemma exp_normalLogDensity (d : ℝ) {s : ℝ} (hs : 0 < s) (x : ℝ) :
    exp (normalLogDensity d s x) = gaussianPDFReal d s.toNNReal x := by
  have hsp : 0 < sqrt (2*Real.pi*s) := sqrt_pos.mpr (by positivity)
  have he : normalLogDensity d s x = -log (sqrt (2*Real.pi*s)) - (x-d)^2/(2*s) := by
    unfold normalLogDensity normalLogConst
    field_simp
    ring
  rw [he, sub_eq_add_neg, exp_add, exp_neg, exp_log hsp]
  simp only [gaussianPDFReal, Real.coe_toNNReal s hs.le]
  congr 1
  congr 1
  ring

lemma continuousOn_normalLogConst : ContinuousOn (fun p : ℝ×ℝ => normalLogConst p.1 p.2)
    {p | 0 < p.2} := by
  unfold normalLogConst
  apply ContinuousOn.sub
  · apply ContinuousOn.neg
    apply ContinuousOn.log
    · fun_prop
    · intro p hp
      have hp' : 0 < p.2 := hp
      exact (sqrt_pos.mpr (by positivity : 0 < 2*Real.pi*p.2)).ne'
  · exact (continuous_fst.pow 2).continuousOn.div (continuous_const.mul continuous_snd).continuousOn
      (fun p hp => mul_ne_zero (by norm_num) (ne_of_gt hp))

lemma normalLogDensity_sub_le (d' s' d s x : ℝ) :
    normalLogDensity d' s' x-normalLogDensity d s x ≤
      |normalLogConst d' s'-normalLogConst d s| + |d'/s'-d/s| *|x| +
        |1/(2*s')-1/(2*s)| *x^2 := by
  have hx := le_abs_self ((d'/s'-d/s)*x)
  rw [abs_mul] at hx
  have hq := neg_le_abs (1/(2*s')-1/(2*s))
  have hm := mul_le_mul_of_nonneg_right hq (sq_nonneg x)
  have hc := le_abs_self (normalLogConst d' s'-normalLogConst d s)
  have he : normalLogDensity d' s' x-normalLogDensity d s x =
      (normalLogConst d' s'-normalLogConst d s)+(d'/s'-d/s)*x -
        (1/(2*s')-1/(2*s))*x^2 := by
    unfold normalLogDensity
    ring
  rw [he]
  linarith

lemma normalLogDensity_sum_sub_le {y : ι → ℝ} {R : ℝ}
    (hy : ∑ i, (y i)^2 ≤ (Fintype.card ι : ℝ)*R) (d' s' d s : ℝ) :
    (∑ i, normalLogDensity d' s' (y i))-(∑ i, normalLogDensity d s (y i)) ≤
      (Fintype.card ι : ℝ) * (|normalLogConst d' s'-normalLogConst d s| +
        |d'/s'-d/s| *(1+R)+|1/(2*s')-1/(2*s)| *R) := by
  have hl : ∑ i, |y i| ≤ (Fintype.card ι : ℝ)*(1+R) := by
    calc
      _ ≤ ∑ i, (1+(y i)^2) := Finset.sum_le_sum (fun i _ => by
        nlinarith [sq_abs (y i), sq_nonneg (|y i|-1)])
      _ = (Fintype.card ι : ℝ) + ∑ i, (y i)^2 := by simp [Finset.sum_add_distrib]
      _ ≤ _ := by nlinarith
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun i _ => normalLogDensity_sub_le d' s' d s (y i))
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, ← Finset.mul_sum] at hh
  have h1 := mul_le_mul_of_nonneg_left hl (abs_nonneg (d'/s'-d/s))
  have h2 := mul_le_mul_of_nonneg_left hy (abs_nonneg (1/(2*s')-1/(2*s)))
  calc
    _ ≤ _ := hh
    _ ≤ _ := by nlinarith

lemma productNormal_eq_exp (d : ℝ) {s : ℝ} (hs : 0 < s) (y : ι → ℝ) :
    productNormal d s y = exp (∑ i, normalLogDensity d s (y i)) := by
  rw [exp_sum]
  unfold productNormal
  apply Finset.prod_congr rfl
  intro i hi
  exact (exp_normalLogDensity d hs (y i)).symm

lemma productNormal_nonneg (d s : ℝ) (y : ι → ℝ) : 0 ≤ productNormal d s y :=
  Finset.prod_nonneg (fun i _ => gaussianPDFReal_nonneg d s.toNNReal (y i))

lemma integrable_tiltedNormal (f : ℝ →ᵇ ℝ) (d : ℝ) (s : ℝ≥0) :
    Integrable (fun x => exp (f x)*gaussianPDFReal d s x) := by
  have h := (integrable_gaussianPDFReal d s).bdd_mul
    (continuous_exp.comp f.continuous).aestronglyMeasurable
    (c := exp ‖f‖) (ae_of_all _ (fun x => by
      dsimp only [Function.comp_def]
      rw [Real.norm_eq_abs, abs_of_pos (exp_pos _)]
      exact exp_le_exp.mpr ((le_abs_self _).trans (f.norm_coe_le_norm x))))
  exact h

lemma integral_tiltedNormal (f : ℝ →ᵇ ℝ) (d : ℝ) {s : ℝ≥0} (hs : s ≠ 0) :
    (∫ x, exp (f x)*gaussianPDFReal d s x) = ∫ x, exp (f x) ∂gaussianReal d s := by
  rw [integral_gaussianReal_eq_integral_smul hs]
  simp only [smul_eq_mul, mul_comm]

lemma tiltedNormal_mass_pos (f : ℝ →ᵇ ℝ) (d : ℝ) (s : ℝ≥0) :
    0 < ∫ x, exp (f x) ∂gaussianReal d s := by
  have hi : Integrable (fun x => exp (f x)) (gaussianReal d s) := Integrable.of_bound
    (by fun_prop) (exp ‖f‖) (ae_of_all _ (fun x => by
      rw [Real.norm_eq_abs, abs_of_pos (exp_pos _)]
      exact exp_le_exp.mpr ((le_abs_self _).trans (f.norm_coe_le_norm x))))
  exact integral_pos_iff_support_of_nonneg (fun _ => (exp_pos _).le) hi |>.mpr
    (by simp [Function.support, (exp_pos _).ne'])

lemma product_tiltedNormal_integral (f : ℝ →ᵇ ℝ) (d : ℝ) {s : ℝ} (hs : 0 < s) :
    (∫ y : ι → ℝ, exp (∑ i, f (y i))*productNormal d s y) =
      exp ((Fintype.card ι : ℝ)*log (∫ x, exp (f x) ∂gaussianReal d s.toNNReal)) := by
  have hs' : s.toNNReal ≠ 0 := ne_of_gt (Real.toNNReal_pos.mpr hs)
  have he (y : ι → ℝ) : exp (∑ i, f (y i))*productNormal d s y =
      ∏ i, (exp (f (y i))*gaussianPDFReal d s.toNNReal (y i)) := by
    rw [exp_sum, productNormal, Finset.prod_mul_distrib]
  simp_rw [he]
  rw [integral_fintype_prod_volume_eq_pow (fun x : ℝ => exp (f x)*gaussianPDFReal d s.toNNReal x), integral_tiltedNormal f d hs',
    exp_nat_mul, exp_log (tiltedNormal_mass_pos f d s.toNNReal)]

lemma product_tiltedNormal_integrable (f : ℝ →ᵇ ℝ) (d s : ℝ) :
    Integrable (fun y : ι → ℝ => exp (∑ i, f (y i))*productNormal d s y) := by
  have h := Integrable.fintype_prod (fun _ : ι => integrable_tiltedNormal f d s.toNNReal)
  simpa only [exp_sum, productNormal, Finset.prod_mul_distrib, volume_pi] using h

end SKGap

namespace SKGap

lemma normalDensityError_self (R d s : ℝ) : normalDensityError R d s d s = 0 := by
  simp [normalDensityError]

lemma continuous_normalDensityError {X : Type*} [TopologicalSpace X]
    {d s : X → ℝ} (hd : Continuous d) (hs : Continuous s) (hspos : ∀ x, 0 < s x)
    (R d₀ s₀ : ℝ) : Continuous (fun x => normalDensityError R (d x) (s x) d₀ s₀) := by
  have hlog : Continuous (fun x => normalLogConst (d x) (s x)) :=
    continuousOn_normalLogConst.comp_continuous (hd.prodMk hs) (fun x => hspos x)
  have hdiv := hd.div hs (fun x => (hspos x).ne')
  have hinv : Continuous (fun x => (1 : ℝ)/(2*s x)) := continuous_const.div (continuous_const.mul hs) (fun x => mul_ne_zero (by norm_num) (hspos x).ne')
  exact ((hlog.sub continuous_const).abs.add ((hdiv.sub continuous_const).abs.mul continuous_const)).add
    ((hinv.sub continuous_const).abs.mul continuous_const)

theorem finite_gaussian_test_cover {X : Type*} [TopologicalSpace X] {K : Set X}
    (hK : IsCompact K) {P : X → ProbabilityMeasure ℝ} {d s ψ : X → ℝ}
    (hP : ContinuousOn P K) (hd : ContinuousOn d K) (hs : ContinuousOn s K)
    (hψ : ContinuousOn ψ K) (hpos : ∀ x ∈ K, 0 < s x) (R r : ℝ)
    (hW : ∀ x ∈ K, ∃ f : ℝ →ᵇ ℝ, ψ x-(∫ y, f y ∂P x)+
      log (∫ y, exp (f y) ∂gaussianReal (d x) (s x).toNNReal) < r) :
    ∃ (C : Finset K) (f : K → ℝ →ᵇ ℝ), ∀ z ∈ K, ∃ x ∈ C,
      ψ z-(∫ y, f x y ∂P z)+normalDensityError R (d z) (s z) (d x) (s x)+
      log (∫ y, exp (f x y) ∂gaussianReal (d x) (s x).toNNReal) < r := by
  classical
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  choose f hf using (fun x : K => hW x.1 x.2)
  let U (x : K) : Set K := {z | ψ z-(∫ y, f x y ∂P z)+
    normalDensityError R (d z) (s z) (d x) (s x)+
      log (∫ y, exp (f x y) ∂gaussianReal (d x) (s x).toNNReal) < r}
  have hU (x : K) : IsOpen (U x) := by
    apply isOpen_lt _ continuous_const
    have hint : Continuous (fun z : K => ∫ y, f x y ∂P z) :=
      (ProbabilityMeasure.continuous_integral_boundedContinuousFunction (f x)).comp hP.domRestrict
    exact ((hψ.domRestrict.sub hint).add
      (continuous_normalDensityError hd.domRestrict hs.domRestrict
        (fun z : K => hpos z.1 z.2) R (d x) (s x))).add continuous_const
  have hcov : (univ : Set K) ⊆ ⋃ x : K, U x := by
    intro z _
    refine mem_iUnion.mpr ⟨z, ?_⟩
    change ψ z-(∫ y, f z y ∂P z)+normalDensityError R (d z) (s z) (d z) (s z)+
      log (∫ y, exp (f z y) ∂gaussianReal (d z) (s z).toNNReal) < r
    simpa only [normalDensityError_self, add_zero] using hf z
  obtain ⟨C,hC⟩ := isCompact_univ.elim_finite_subcover U hU hcov
  refine ⟨C,f,?_⟩
  intro z hz
  have hh := hC (mem_univ (⟨z,hz⟩ : K))
  obtain ⟨x,hx⟩ := mem_iUnion.mp hh
  obtain ⟨hxC,hxU⟩ := mem_iUnion.mp hx
  exact ⟨x,hxC,hxU⟩

end SKGap
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ074_CM.SKGap_Gaussian_GaussianTiltMass
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Real Set Filter
open scoped NNReal ENNReal Topology
noncomputable section
open Real Set
noncomputable section
open MeasureTheory ProbabilityTheory Real Set Filter
open scoped Topology NNReal ENNReal BoundedContinuousFunction
open MeasureTheory ProbabilityTheory Filter Set Topology Real
open scoped NNReal ENNReal BoundedContinuousFunction
noncomputable section
open Set Filter Topology
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Topology Real
open scoped NNReal ENNReal BoundedContinuousFunction
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Topology Real
open scoped NNReal ENNReal BoundedContinuousFunction

namespace SKGap
variable {ι : Type*} [Fintype ι] [Nonempty ι]

omit [Nonempty ι] in
lemma gaussian_tilt_mass (f : ℝ →ᵇ ℝ) (d : ℝ) {s : ℝ} (hs : 0 < s) (r : ℝ) :
    (∫ y : ι → ℝ, exp ((Fintype.card ι : ℝ)*r -
      (Fintype.card ι : ℝ)*log (∫ x, exp (f x) ∂gaussianReal d s.toNNReal)) *
      (exp (∑ i, f (y i))*productNormal d s y)) = exp ((Fintype.card ι : ℝ)*r) := by
  rw [integral_const_mul, product_tiltedNormal_integral f d hs, ← exp_add]
  congr 1
  ring

theorem gaussian_covered_laplace {X : Type*} (C : Finset X) (f : X → ℝ →ᵇ ℝ)
    (d₀ s₀ : X → ℝ) (hs₀ : ∀ x ∈ C, 0 < s₀ x)
    (d s ψ : (ι → ℝ) → ℝ) (R r : ℝ) {E : Set (ι → ℝ)} (hE : MeasurableSet E)
    (hpos : ∀ y ∈ E, 0 < s y)
    (hmom : ∀ y ∈ E, ∑ i, (y i)^2 ≤ (Fintype.card ι : ℝ)*R)
    (hcover : ∀ y ∈ E, ∃ x ∈ C,
      ψ y-(∫ u, f x u ∂empiricalLaw y)+normalDensityError R (d y) (s y) (d₀ x) (s₀ x)+
        log (∫ u, exp (f x u) ∂gaussianReal (d₀ x) (s₀ x).toNNReal) < r) :
    (∫⁻ y in E, ENNReal.ofReal (exp ((Fintype.card ι : ℝ)*ψ y)*productNormal (d y) (s y) y)) ≤
      ENNReal.ofReal ((C.card : ℝ)*exp ((Fintype.card ι : ℝ)*r)) := by
  classical
  let F (x : X) (y : ι → ℝ) : ℝ :=
    exp ((Fintype.card ι : ℝ)*r-(Fintype.card ι : ℝ)*
      log (∫ u, exp (f x u) ∂gaussianReal (d₀ x) (s₀ x).toNNReal)) *
      (exp (∑ i, f x (y i))*productNormal (d₀ x) (s₀ x) y)
  have hFi (x : X) : Integrable (F x) :=
    (product_tiltedNormal_integrable (f x) (d₀ x) (s₀ x)).const_mul _
  have hFnn (x : X) (y : ι → ℝ) : 0 ≤ F x y :=
    mul_nonneg (exp_pos _).le (mul_nonneg (exp_pos _).le (productNormal_nonneg _ _ _))
  have hnorm (x : X) (hx : x ∈ C) : ∫ y, F x y = exp ((Fintype.card ι : ℝ)*r) :=
    gaussian_tilt_mass (f x) (d₀ x) (hs₀ x hx) r
  have hdom (y : ι → ℝ) (hy : y ∈ E) :
      exp ((Fintype.card ι : ℝ)*ψ y)*productNormal (d y) (s y) y ≤ ∑ x ∈ C, F x y := by
    obtain ⟨x,hx,hc⟩ := hcover y hy
    have hdens := normalLogDensity_sum_sub_le (hmom y hy) (d y) (s y) (d₀ x) (s₀ x)
    change _ ≤ (Fintype.card ι : ℝ)*normalDensityError R (d y) (s y) (d₀ x) (s₀ x) at hdens
    have hn : (0 : ℝ) < Fintype.card ι := by exact_mod_cast (Fintype.card_pos (α := ι))
    have hc' := mul_lt_mul_of_pos_left hc hn
    have hemp := card_mul_integral_empiricalLaw y (f x)
    have hsmall : exp ((Fintype.card ι : ℝ)*ψ y)*productNormal (d y) (s y) y ≤ F x y := by
      dsimp only [F]
      rw [productNormal_eq_exp _ (hpos y hy), productNormal_eq_exp _ (hs₀ x hx),
        ← exp_add, ← exp_add, ← exp_add]
      apply exp_le_exp.mpr
      nlinarith
    exact hsmall.trans (Finset.single_le_sum (fun a _ => hFnn a y) hx)
  have hsumI : Integrable (fun y => ∑ x ∈ C, F x y) := integrable_finsetSum C (fun x _ => hFi x)
  calc
    _ ≤ ∫⁻ y in E, ENNReal.ofReal (∑ x ∈ C, F x y) := lintegral_mono_ae
      ((ae_restrict_mem hE).mono (fun y hy => ENNReal.ofReal_le_ofReal (hdom y hy)))
    _ ≤ ∫⁻ y, ENNReal.ofReal (∑ x ∈ C, F x y) := lintegral_mono' Measure.restrict_le_self (fun _ => le_rfl)
    _ = ENNReal.ofReal (∫ y, ∑ x ∈ C, F x y) :=
      (ofReal_integral_eq_lintegral_ofReal hsumI (ae_of_all _ (fun y => Finset.sum_nonneg (fun x _ => hFnn x y)))).symm
    _ = _ := by
      rw [integral_finsetSum C (fun x _ => hFi x)]
      simp_rw [Finset.sum_congr rfl hnorm]
      simp

end SKGap

namespace SKGap

theorem gaussian_compact_laplace {X : Type*} [TopologicalSpace X] {K : Set X}
    (hK : IsCompact K) {P : X → ProbabilityMeasure ℝ} {d s ψ : X → ℝ}
    (hP : ContinuousOn P K) (hd : ContinuousOn d K) (hs : ContinuousOn s K)
    (hψ : ContinuousOn ψ K) (hpos : ∀ x ∈ K, 0 < s x) (R r : ℝ)
    (hW : ∀ x ∈ K, ∃ f : ℝ →ᵇ ℝ, ψ x-(∫ y, f y ∂P x)+
      log (∫ y, exp (f y) ∂gaussianReal (d x) (s x).toNNReal) < r) :
    ∃ M : ℕ, ∀ n : ℕ, ∀ hn : 0 < n, ∀ z : (Fin n → ℝ) → X,
      ∀ E : Set (Fin n → ℝ), MeasurableSet E →
      (∀ y ∈ E, z y ∈ K) →
      (∀ y ∈ E, P (z y) = @empiricalLaw (Fin n) _ ⟨⟨0,hn⟩⟩ y) →
      (∀ y ∈ E, ∑ i, (y i)^2 ≤ (n:ℝ)*R) →
      (∫⁻ y in E, ENNReal.ofReal (exp ((n:ℝ)*ψ (z y))*productNormal (d (z y)) (s (z y)) y)) ≤
        ENNReal.ofReal ((M:ℝ)*exp ((n:ℝ)*r)) := by
  classical
  obtain ⟨C,f,hC⟩ := finite_gaussian_test_cover hK hP hd hs hψ hpos R r hW
  refine ⟨C.card, ?_⟩
  intro n hn z E hE hz hemp hmom
  let : Nonempty (Fin n) := ⟨⟨0,hn⟩⟩
  have hh := gaussian_covered_laplace C f (fun x : K => d x) (fun x : K => s x)
      (fun x _ => hpos x x.2) (fun y => d (z y)) (fun y => s (z y))
      (fun y => ψ (z y)) R r hE (fun y hy => hpos (z y) (hz y hy))
      (by simpa only [Fintype.card_fin] using hmom) (fun y hy => by
        obtain ⟨x,hx,hcx⟩ := hC (z y) (hz y hy)
        rw [hemp y hy] at hcx
        exact ⟨x,hx,hcx⟩)
  simpa only [Fintype.card_fin] using hh

lemma absorb_finite_exponential_factor (M : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ r : ℝ,
      (M:ℝ)*exp ((n:ℝ)*r) ≤ exp ((n:ℝ)*(r+ε)) := by
  obtain ⟨N,hN⟩ := exists_nat_gt (log ((M:ℝ)+1)/ε)
  refine ⟨N,?_⟩
  intro n hn r
  have hcast : (N:ℝ) ≤ n := by exact_mod_cast hn
  have hnlog : log ((M:ℝ)+1) ≤ (n:ℝ)*ε := by
    have h := (div_lt_iff₀ hε).mp hN
    nlinarith
  have he : (M:ℝ) ≤ exp ((n:ℝ)*ε) := by
    have h := exp_le_exp.mpr hnlog
    rw [exp_log (by positivity)] at h
    linarith
  calc
    _ ≤ exp ((n:ℝ)*ε)*exp ((n:ℝ)*r) := mul_le_mul_of_nonneg_right he (exp_pos _).le
    _ = _ := by rw [← exp_add]; congr 1; ring

theorem gaussian_compact_rate {X : Type*} [TopologicalSpace X] {K : Set X}
    (hK : IsCompact K) {P : X → ProbabilityMeasure ℝ} {d s ψ : X → ℝ}
    (hP : ContinuousOn P K) (hd : ContinuousOn d K) (hs : ContinuousOn s K)
    (hψ : ContinuousOn ψ K) (hpos : ∀ x ∈ K, 0 < s x) (R r : ℝ)
    (hW : ∀ x ∈ K, ∃ f : ℝ →ᵇ ℝ, ψ x-(∫ y, f y ∂P x)+
      log (∫ y, exp (f y) ∂gaussianReal (d x) (s x).toNNReal) < r)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ hn : 0 < n, ∀ z : (Fin n → ℝ) → X,
      ∀ E : Set (Fin n → ℝ), MeasurableSet E →
      (∀ y ∈ E, z y ∈ K) →
      (∀ y ∈ E, P (z y) = @empiricalLaw (Fin n) _ ⟨⟨0,hn⟩⟩ y) →
      (∀ y ∈ E, ∑ i, (y i)^2 ≤ (n:ℝ)*R) →
      (∫⁻ y in E, ENNReal.ofReal (exp ((n:ℝ)*ψ (z y))*productNormal (d (z y)) (s (z y)) y)) ≤
        ENNReal.ofReal (exp ((n:ℝ)*(r+ε))) := by
  obtain ⟨M,hM⟩ := gaussian_compact_laplace hK hP hd hs hψ hpos R r hW
  obtain ⟨N,hN⟩ := absorb_finite_exponential_factor M hε
  refine ⟨N,?_⟩
  intro n hn hn' z E hE hz hemp hmom
  exact (hM n hn' z E hE hz hemp hmom).trans (ENNReal.ofReal_le_ofReal (hN n hn r))

end SKGap

end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ074_CM.SKGap_Localization_ScalarConsistency
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Real Set Filter
open scoped NNReal ENNReal Topology
noncomputable section
open Real Set
noncomputable section
open MeasureTheory ProbabilityTheory Real Set Filter
open scoped Topology NNReal ENNReal BoundedContinuousFunction

open MeasureTheory ProbabilityTheory Filter Set Topology Real
open scoped NNReal ENNReal BoundedContinuousFunction

namespace SKGap

lemma scalar_consistency {j : ℝ} {p : ScalarPoint} (ht : 0 ≤ p.2.1) :
    j*scalarQMoment p.1 ≤ scalarS j p := by
  unfold scalarS
  nlinarith [sq_nonneg p.2.2]

lemma scalarPsi_eq_entropy {R j : ℝ} {p : ScalarPoint}
    (hp : p ∈ scalarMomentDomain R) (hs : 0 ≤ scalarS j p) :
    scalarPsi j p = scalarEntropyTarget (p.1 : Measure ℝ) j (scalarD j p) (scalarS j p).toNNReal := by
  simp only [scalarPsi, scalarEntropyTarget, Real.coe_toNNReal _ hs, scalarA_eq hp, scalarQMoment]

lemma scalar_strict_test {R j : ℝ} {p : ScalarPoint}
    (hp : p ∈ scalarMomentDomain R) (hj : 0 < j) (hj1 : j < 1)
    (ht : 0 ≤ p.2.1) (hs : 0 < scalarS j p)
    (hne : (p.1 : Measure ℝ) ≠ gaussianReal (scalarD j p) (scalarS j p).toNNReal) :
    ∃ f : ℝ →ᵇ ℝ, scalarPsi j p-(∫ y, f y ∂p.1)+
      log (∫ y, exp (f y) ∂gaussianReal (scalarD j p) (scalarS j p).toNNReal) < 0 := by
  have hcons : j * (∫ y, tanh y^2 ∂p.1) ≤ ((scalarS j p).toNNReal : ℝ) := by
    rw [Real.coe_toNNReal _ hs.le]
    exact scalar_consistency ht
  obtain ⟨f,hf⟩ := scalar_strict_witness (momentBall_integrable hp.1) hj hj1
    (ne_of_gt (Real.toNNReal_pos.mpr hs)) hcons hne
  rw [← scalarPsi_eq_entropy hp hs.le] at hf
  exact ⟨f, by linarith⟩

lemma scalar_gaussian_curve {j : ℝ} {p : ScalarPoint}
    (hj : 0 < j) (hj1 : j < 1) (ht : 0 ≤ p.2.1)
    (hσ : p.2.2 = 0) (hs : 0 ≤ scalarS j p)
    (hP : (p.1 : Measure ℝ) = gaussianReal (scalarD j p) (scalarS j p).toNNReal) :
    p.1 = scalarCurve j p.2.1 := by
  have hd : scalarD j p = p.2.1+j*(∫ y, tanh y ∂gaussianReal (scalarD j p) (scalarS j p).toNNReal) := by
    rw [← hP]
    rfl
  have hv : ((scalarS j p).toNNReal : ℝ) =
      p.2.1+j*(∫ y, tanh y^2 ∂gaussianReal (scalarD j p) (scalarS j p).toNNReal) := by
    rw [Real.coe_toNNReal _ hs, ← hP]
    simp [scalarS, scalarQMoment, hσ]
  obtain ⟨hd',hs'⟩ := consistent_gaussian_unique hj hj1 ht hd hv
  rw [Real.coe_toNNReal _ hs] at hs'
  apply ProbabilityMeasure.toMeasure_injective
  change (p.1 : Measure ℝ) = gaussianReal (scalarFixedPoint j p.2.1) (scalarFixedPoint j p.2.1).toNNReal
  rw [hP, hd', hs']

lemma continuousOn_scalar_test {R j : ℝ} (hR : 0 ≤ R) (hj : 0 ≤ j)
    (f : ℝ →ᵇ ℝ) : ContinuousOn (fun p : ScalarPoint =>
      scalarPsi j p-(∫ y, f y ∂p.1)+scalarLogMoment f (scalarD j p) (scalarS j p))
      (scalarMomentDomain R ∩ {p | 0 < scalarS j p}) := by
  have hψ : ContinuousOn (scalarPsi j)
      (scalarMomentDomain R ∩ {p | 0 < scalarS j p}) := (continuousOn_scalarPsi hR j).mono (by
        intro p hp
        refine ⟨hp.1,hp.2.ne',ne_of_gt ?_⟩
        exact add_pos_of_pos_of_nonneg hp.2 (mul_nonneg hj (scalarQMoment_bounds p.1).1))
  exact (hψ.sub ((ProbabilityMeasure.continuous_integral_boundedContinuousFunction f).comp
    continuous_fst).continuousOn).add
    ((continuous_scalarLogMoment f).comp ((continuous_scalarD j).prodMk (continuous_scalarS j))).continuousOn

end SKGap

noncomputable section
open Set Filter Topology
namespace SKGap

lemma finite_pos_lower_bound {X : Type*} (C : Finset X) (a : X → ℝ)
    (ha : ∀ x ∈ C, 0 < a x) : ∃ ε > 0, ∀ x ∈ C, ε ≤ a x := by
  classical
  induction C using Finset.induction_on with
  | empty => exact ⟨1,by norm_num,by simp⟩
  | insert x C hx ih =>
    obtain ⟨ε,hε,he⟩ := ih (fun y hy => ha y (Finset.mem_insert_of_mem hy))
    refine ⟨min (a x) ε, lt_min (ha x (Finset.mem_insert_self _ _)) hε, ?_⟩
    intro y hy
    rcases Finset.mem_insert.mp hy with rfl | hy
    · exact min_le_left _ _
    · exact (min_le_right _ _).trans (he y hy)

theorem compact_strict_witness {X F : Type*} [TopologicalSpace X] {K : Set X}
    (hK : IsCompact K) (w : F → X → ℝ) (hw : ∀ f, ContinuousOn (w f) K)
    (hW : ∀ x ∈ K, ∃ f, w f x < 0) :
    ∃ a > 0, ∀ x ∈ K, ∃ f, w f x < -a := by
  classical
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  choose f hf using fun x : K => hW x.1 x.2
  let a (x : K) := -(w (f x) x)/2
  have ha (x : K) : 0 < a x := by dsimp [a]; linarith [hf x]
  let U (x : K) : Set K := {z | w (f x) z < -a x}
  have hU (x : K) : IsOpen (U x) := isOpen_lt (hw (f x)).domRestrict continuous_const
  have hcov : (univ : Set K) ⊆ ⋃ x, U x := by
    intro x _
    apply mem_iUnion.mpr
    refine ⟨x,?_⟩
    change w (f x) x < -a x
    dsimp [a]
    linarith [hf x]
  obtain ⟨C,hC⟩ := isCompact_univ.elim_finite_subcover U hU hcov
  obtain ⟨ε,hε,he⟩ := finite_pos_lower_bound C a (fun x _ => ha x)
  refine ⟨ε,hε,?_⟩
  intro z hz
  obtain ⟨x,hx⟩ := mem_iUnion.mp (hC (mem_univ (⟨z,hz⟩ : K)))
  obtain ⟨hxC,hxz⟩ := mem_iUnion.mp hx
  refine ⟨f x,?_⟩
  change w (f x) z < -a x at hxz
  linarith [he x hxC]

lemma compact_zero_fiber_neighborhood {X : Type*} [TopologicalSpace X] [CompactSpace X]
    {σ : X → ℝ} (hσ : Continuous σ) (hnn : ∀ x, 0 ≤ σ x)
    {U : Set X} (hU : IsOpen U) (hzero : ∀ x, σ x = 0 → x ∈ U) :
    ∃ δ > 0, ∀ x, σ x ≤ δ → x ∈ U := by
  by_cases he : Uᶜ = ∅
  · refine ⟨1,by norm_num,?_⟩
    intro x _
    by_contra hx
    have hx' : x ∈ Uᶜ := hx
    simp only [he, mem_empty_iff_false] at hx'
  obtain ⟨x,hx,hmin⟩ := hU.isClosed_compl.isCompact.exists_isMinOn (nonempty_iff_ne_empty.mpr he) hσ.continuousOn
  have hxpos : 0 < σ x := lt_of_le_of_ne (hnn x) (by
    intro hh
    exact hx (hzero x hh.symm))
  refine ⟨σ x/2,by positivity,?_⟩
  intro y hy
  by_contra hny
  have h : σ x ≤ σ y := hmin hny
  linarith

theorem compact_small_noise_witness {X F : Type*} [TopologicalSpace X] {K : Set X}
    (hK : IsCompact K) (w : F → X → ℝ) (hw : ∀ f, ContinuousOn (w f) K)
    {σ : X → ℝ} (hσ : ContinuousOn σ K) (hnn : ∀ x ∈ K, 0 ≤ σ x)
    (hW : ∀ x ∈ K, σ x = 0 → ∃ f, w f x < 0) :
    ∃ a > 0, ∃ δ > 0, ∀ x ∈ K, σ x ≤ δ → ∃ f, w f x < -a := by
  classical
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let Z : Set K := {x | σ x = 0}
  have hZ : IsCompact Z := (isClosed_eq hσ.domRestrict continuous_const).isCompact
  obtain ⟨a,ha,hA⟩ := compact_strict_witness hZ (fun f (x : K) => w f x)
    (fun f => (hw f).domRestrict.continuousOn) (fun x hx => hW x.1 x.2 hx)
  let U : Set K := {x | ∃ f, w f x < -(a/2)}
  have hU : IsOpen U := by
    have hu : U = ⋃ f : F, {x : K | w f x < -(a/2)} := by ext x; simp [U]
    rw [hu]
    exact isOpen_iUnion (fun f => isOpen_lt (hw f).domRestrict continuous_const)
  have hzU (x : K) (hx : σ x = 0) : x ∈ U := by
    obtain ⟨f,hf⟩ := hA x hx
    exact ⟨f,by linarith⟩
  obtain ⟨δ,hδ,hd⟩ := compact_zero_fiber_neighborhood hσ.domRestrict
    (fun x : K => hnn x.1 x.2) hU hzU
  exact ⟨a/2,by positivity,δ,hδ,fun x hx hσx => hd ⟨x,hx⟩ hσx⟩

end SKGap

end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ074_CM.SKGap_Localization_ScalarSmallNoiseTests
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Real Set Filter
open scoped NNReal ENNReal Topology
noncomputable section
open Real Set
noncomputable section
open MeasureTheory ProbabilityTheory Real Set Filter
open scoped Topology NNReal ENNReal BoundedContinuousFunction
open MeasureTheory ProbabilityTheory Filter Set Topology Real
open scoped NNReal ENNReal BoundedContinuousFunction
noncomputable section
open Set Filter Topology
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Topology Real
open scoped NNReal ENNReal BoundedContinuousFunction
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Topology Real
open scoped NNReal ENNReal BoundedContinuousFunction
namespace SKGap

lemma scalar_small_noise_tests {j R : ℝ} (hj : 0 < j) (hj1 : j < 1) (hR : 0 ≤ R)
    {K : Set ScalarPoint} (hK : IsCompact K)
    (hmom : K ⊆ scalarMomentDomain R) (ht : ∀ p ∈ K, 0 ≤ p.2.1)
    (hσ : ∀ p ∈ K, 0 ≤ p.2.2) (hs : ∀ p ∈ K, 0 < scalarS j p)
    (hne : ∀ p ∈ K, p.2.2 = 0 → p.1 ≠ scalarCurve j p.2.1) :
    ∃ a > 0, ∃ δ > 0, ∀ p ∈ K, p.2.2 ≤ δ → ∃ f : ℝ →ᵇ ℝ,
      scalarPsi j p-(∫ y, f y ∂p.1)+
        log (∫ y, exp (f y) ∂gaussianReal (scalarD j p) (scalarS j p).toNNReal) < -a := by
  have hw (f : ℝ →ᵇ ℝ) : ContinuousOn (fun p : ScalarPoint =>
      scalarPsi j p-(∫ y, f y ∂p.1)+scalarLogMoment f (scalarD j p) (scalarS j p)) K :=
    (continuousOn_scalar_test hR hj.le f).mono (fun p hp => ⟨hmom hp,hs p hp⟩)
  have hW (p : ScalarPoint) (hp : p ∈ K) (hz : p.2.2 = 0) :
      ∃ f : ℝ →ᵇ ℝ, scalarPsi j p-(∫ y, f y ∂p.1)+scalarLogMoment f (scalarD j p) (scalarS j p) < 0 := by
    have hng : (p.1 : Measure ℝ) ≠ gaussianReal (scalarD j p) (scalarS j p).toNNReal := by
      intro he
      exact hne p hp hz (scalar_gaussian_curve hj hj1 (ht p hp) hz (hs p hp).le he)
    obtain ⟨f,hf⟩ := scalar_strict_test (hmom hp) hj hj1 (ht p hp) (hs p hp) hng
    rw [← scalarLogMoment_eq f _ (hs p hp).le] at hf
    exact ⟨f,hf⟩
  obtain ⟨a,ha,δ,hδ,hall⟩ := compact_small_noise_witness hK _ hw
    (σ := fun p : ScalarPoint => p.2.2) (by fun_prop) hσ hW
  refine ⟨a,ha,δ,hδ,?_⟩
  intro p hp hδp
  obtain ⟨f,hf⟩ := hall p hp hδp
  rw [scalarLogMoment_eq f _ (hs p hp).le] at hf
  exact ⟨f,hf⟩

lemma continuousOn_scalarPsi_of_pos {j R : ℝ} (hj : 0 ≤ j) (hR : 0 ≤ R)
    {K : Set ScalarPoint} (hmom : K ⊆ scalarMomentDomain R) (hs : ∀ p ∈ K, 0 < scalarS j p) :
    ContinuousOn (scalarPsi j) K := (continuousOn_scalarPsi hR j).mono (by
      intro p hp
      exact ⟨hmom hp,(hs p hp).ne',ne_of_gt (add_pos_of_pos_of_nonneg (hs p hp)
        (mul_nonneg hj (scalarQMoment_bounds p.1).1))⟩)

theorem scalar_compact_isolation {j R : ℝ} (hj : 0 < j) (hj1 : j < 1) (hR : 0 ≤ R)
    {K : Set ScalarPoint} (hK : IsCompact K)
    (hmom : K ⊆ scalarMomentDomain R) (ht : ∀ p ∈ K, 0 ≤ p.2.1)
    (hσ : ∀ p ∈ K, 0 ≤ p.2.2) (hs : ∀ p ∈ K, 0 < scalarS j p)
    (hne : ∀ p ∈ K, p.2.2 = 0 → p.1 ≠ scalarCurve j p.2.1) :
    ∃ a > 0, ∃ δ > 0, ∃ N : ℕ, ∀ n ≥ N, ∀ hn : 0 < n,
      ∀ z : (Fin n → ℝ) → ScalarPoint, ∀ E : Set (Fin n → ℝ), MeasurableSet E →
      (∀ y ∈ E, z y ∈ K ∧ (z y).2.2 ≤ δ) →
      (∀ y ∈ E, (z y).1 = @empiricalLaw (Fin n) _ ⟨⟨0,hn⟩⟩ y) →
      (∀ y ∈ E, ∑ i, (y i)^2 ≤ (n:ℝ)*R) →
      (∫⁻ y in E, ENNReal.ofReal (exp ((n:ℝ)*scalarPsi j (z y))*
        productNormal (scalarD j (z y)) (scalarS j (z y)) y)) ≤ ENNReal.ofReal (exp (-a*(n:ℝ))) := by
  obtain ⟨a,ha,δ,hδ,hW⟩ := scalar_small_noise_tests hj hj1 hR hK hmom ht hσ hs hne
  let K' := K ∩ {p : ScalarPoint | p.2.2 ≤ δ}
  have hK' : IsCompact K' := hK.inter_right (isClosed_le (by fun_prop) continuous_const)
  have hmom' : K' ⊆ scalarMomentDomain R := fun _ hp => hmom hp.1
  have hs' : ∀ p ∈ K', 0 < scalarS j p := fun p hp => hs p hp.1
  obtain ⟨N,hN⟩ := gaussian_compact_rate hK' (P := fun p : ScalarPoint => p.1)
    continuous_fst.continuousOn (continuous_scalarD j).continuousOn (continuous_scalarS j).continuousOn
    (continuousOn_scalarPsi_of_pos hj.le hR hmom' hs') hs' R (-a)
    (fun p hp => hW p hp.1 hp.2) (half_pos ha)
  refine ⟨a/2,half_pos ha,δ,hδ,N,?_⟩
  intro n hn hn' z E hE hz hemp hmomE
  have hh := hN n hn hn' z E hE hz hemp hmomE
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  ring_nf

end SKGap
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Topology Real
open scoped NNReal ENNReal
namespace SKGap

lemma scalar_quadratic_envelope {j q a s Q : ℝ} (hj : 0 ≤ j) (hq : 0 ≤ q)
    (hq1 : q ≤ 1) (hs : 0 < s) (hc : j*q ≤ s) (hQ : 0 ≤ Q) (ha : a^2 ≤ q*Q) :
    j*(a-s*(1-q))^2/(2*s*(s+j*q)) ≤ 3*Q/(8*s)+3*j/2 := by
  have hS : 0 < s+j*q := add_pos_of_pos_of_nonneg hs (mul_nonneg hj hq)
  have hsq : (a-s*(1-q))^2 ≤ 3/2*a^2+3*(s*(1-q))^2 := by
    nlinarith [sq_nonneg (a+2*s*(1-q))]
  have hb : (1-q)^2 ≤ 1 := by nlinarith
  have hb' := mul_le_mul_of_nonneg_left hb (sq_nonneg s)
  have ha' := mul_le_mul_of_nonneg_left ha (show 0 ≤ 3/2*j by positivity)
  have hc' := mul_le_mul_of_nonneg_right hc hQ
  have hss := mul_nonneg hs.le (mul_nonneg hj hq)
  have hsqj := mul_le_mul_of_nonneg_left hsq hj
  have hb'' := mul_le_mul_of_nonneg_left hb' (show 0 ≤ 3*j by positivity)
  apply (div_le_iff₀ (by positivity : 0 < 2*s*(s+j*q))).mpr
  have he : (3*Q/(8*s)+3*j/2)*(2*s*(s+j*q)) = 3/4*Q*(s+j*q)+3*j*s*(s+j*q) := by
    field_simp
    ring
  rw [he]
  have hjs := mul_nonneg hj hss
  nlinarith

lemma sum_centered_sq_lower {ι : Type*} [Fintype ι] (y : ι → ℝ) (d : ℝ) :
    (∑ i, (y i)^2)/2-(Fintype.card ι:ℝ)*d^2 ≤ ∑ i, (y i-d)^2 := by
  have h := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
    show (y i)^2/2-d^2 ≤ (y i-d)^2 by nlinarith [sq_nonneg (y i-2*d)])
  simpa only [Finset.sum_sub_distrib, Finset.sum_div, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul] using h

lemma multiple_gaussian_integrable {ι : Type*} [Fintype ι] {c : ℝ} (hc : 0 < c) :
    Integrable (fun y : ι → ℝ => exp (-c*∑ i, (y i)^2)) := by
  have h := Integrable.fintype_prod (fun _ : ι => integrable_exp_neg_mul_sq hc)
  simpa only [volume_pi, ← exp_sum, ← Finset.mul_sum] using h

lemma multiple_gaussian_integral {ι : Type*} [Fintype ι] {c : ℝ} (hc : 0 < c) :
    (∫ y : ι → ℝ, exp (-c*∑ i, (y i)^2)) = exp ((Fintype.card ι:ℝ)*log (sqrt (Real.pi/c))) := by
  have he (y : ι → ℝ) : exp (-c*∑ i, (y i)^2) = ∏ i, exp (-c*(y i)^2) := by
    rw [Finset.mul_sum, exp_sum]
  simp_rw [he]
  rw [integral_fintype_prod_volume_eq_pow (fun x : ℝ => exp (-c*x^2)), integral_gaussian]
  rw [exp_nat_mul, exp_log (sqrt_pos.mpr (div_pos Real.pi_pos hc))]

theorem quadratic_envelope_tail {ι : Type*} [Fintype ι] {c C R : ℝ} (hc : 0 < c)
    {E : Set (ι → ℝ)} (hE : MeasurableSet E) (f : (ι → ℝ) → ℝ)
    (hf : ∀ y ∈ E, f y ≤ exp ((Fintype.card ι:ℝ)*C-c*∑ i, (y i)^2))
    (htail : ∀ y ∈ E, (Fintype.card ι:ℝ)*R ≤ ∑ i, (y i)^2) :
    (∫⁻ y in E, ENNReal.ofReal (f y)) ≤ ENNReal.ofReal
      (exp ((Fintype.card ι:ℝ)*(C-c*R/2+log (sqrt (Real.pi/(c/2)))))) := by
  let g (y : ι → ℝ) := exp ((Fintype.card ι:ℝ)*(C-c*R/2))*exp (-(c/2)*∑ i, (y i)^2)
  have hg : Integrable g := (multiple_gaussian_integrable (half_pos hc)).const_mul _
  have hgnn (y : ι → ℝ) : 0 ≤ g y := mul_nonneg (exp_pos _).le (exp_pos _).le
  have hdom (y : ι → ℝ) (hy : y ∈ E) : f y ≤ g y := by
    refine (hf y hy).trans ?_
    dsimp [g]
    rw [← exp_add]
    apply exp_le_exp.mpr
    have h := mul_le_mul_of_nonneg_left (htail y hy) hc.le
    nlinarith
  calc
    _ ≤ ∫⁻ y in E, ENNReal.ofReal (g y) := lintegral_mono_ae
      ((ae_restrict_mem hE).mono (fun y hy => ENNReal.ofReal_le_ofReal (hdom y hy)))
    _ ≤ ∫⁻ y, ENNReal.ofReal (g y) := lintegral_mono' Measure.restrict_le_self (fun _ => le_rfl)
    _ = ENNReal.ofReal (∫ y, g y) := (ofReal_integral_eq_lintegral_ofReal hg (ae_of_all _ hgnn)).symm
    _ = _ := by
      congr 1
      dsimp [g]
      rw [integral_const_mul, multiple_gaussian_integral (half_pos hc), ← exp_add]
      congr 1
      ring

lemma choose_quadratic_tail_radius {c C : ℝ} (hc : 0 < c) (L : ℝ) :
    ∃ R > 0, C-c*R/2+log (sqrt (Real.pi/(c/2))) ≤ -L := by
  let R := max 1 (2*(C+log (sqrt (Real.pi/(c/2)))+L)/c)
  refine ⟨R, (by dsimp [R]; exact lt_of_lt_of_le zero_lt_one (le_max_left _ _)), ?_⟩
  have h : 2*(C+log (sqrt (Real.pi/(c/2)))+L)/c ≤ R := le_max_right _ _
  rw [div_le_iff₀ hc] at h
  nlinarith

end SKGap

end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ074_CM.SKGap_Matrix_NormalLogDensityCentered
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Real Set Filter
open scoped NNReal ENNReal Topology
noncomputable section
open Real Set
noncomputable section
open MeasureTheory ProbabilityTheory Real Set Filter
open scoped Topology NNReal ENNReal BoundedContinuousFunction
open MeasureTheory ProbabilityTheory Filter Set Topology Real
open scoped NNReal ENNReal BoundedContinuousFunction
noncomputable section
open Set Filter Topology
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Topology Real
open scoped NNReal ENNReal BoundedContinuousFunction
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Topology Real
open scoped NNReal ENNReal BoundedContinuousFunction
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Topology Real
open scoped NNReal ENNReal
namespace SKGap
lemma normalLogDensity_centered (d s x : ℝ) :
    normalLogDensity d s x = -log (sqrt (2*Real.pi*s))-(x-d)^2/(2*s) := by
  unfold normalLogDensity normalLogConst
  ring

lemma gaussian_pointwise_envelope {ι : Type*} [Fintype ι] (y : ι → ℝ)
    {d s j D smin smax ψ : ℝ} (hsmin : 0 < smin) (hsl : smin ≤ s) (hsu : s ≤ smax)
    (hd : d^2 ≤ D^2)
    (hψ : (Fintype.card ι:ℝ)*ψ ≤ 3/(8*s)*(∑ i, (y i-d)^2)+3*(Fintype.card ι:ℝ)*j/2) :
    exp ((Fintype.card ι:ℝ)*ψ)*productNormal d s y ≤
      exp ((Fintype.card ι:ℝ)*(|log (sqrt (2*Real.pi*smin))|+3*j/2+D^2/(8*smin))-
        (1/(16*smax))*∑ i, (y i)^2) := by
  have hs : 0 < s := hsmin.trans_le hsl
  have hmax : 0 < smax := hs.trans_le hsu
  have hn : (0:ℝ) ≤ Fintype.card ι := Nat.cast_nonneg _
  have hQ : 0 ≤ ∑ i, (y i)^2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hc := sum_centered_sq_lower y d
  have hnd := mul_le_mul_of_nonneg_left hd hn
  have h1 : -(∑ i, (y i-d)^2)/(8*s) ≤
      -(∑ i, (y i)^2)/(16*s)+(Fintype.card ι:ℝ)*D^2/(8*s) := by
    have he : -(∑ i, (y i)^2)/(16*s)+(Fintype.card ι:ℝ)*D^2/(8*s) =
        (-(∑ i, (y i)^2)/2+(Fintype.card ι:ℝ)*D^2)/(8*s) := by ring
    rw [he]
    apply div_le_div_of_nonneg_right _ (by positivity : 0 ≤ 8*s)
    linarith
  have h2 : -(∑ i, (y i)^2)/(16*s) ≤ -(∑ i, (y i)^2)/(16*smax) := by
    rw [neg_div, neg_div, neg_le_neg_iff]
    gcongr
  have h3 : (Fintype.card ι:ℝ)*D^2/(8*s) ≤ (Fintype.card ι:ℝ)*D^2/(8*smin) := by
    gcongr
  have hp : 0 < sqrt (2*Real.pi*smin) := sqrt_pos.mpr (by positivity)
  have hlog : log (sqrt (2*Real.pi*smin)) ≤ log (sqrt (2*Real.pi*s)) :=
    log_le_log hp (sqrt_le_sqrt (by nlinarith [Real.pi_pos]))
  have hlog' : -log (sqrt (2*Real.pi*s)) ≤ |log (sqrt (2*Real.pi*smin))| :=
    (neg_le_neg hlog).trans (neg_le_abs _)
  have hnlog := mul_le_mul_of_nonneg_left hlog' hn
  have he : (∑ i, normalLogDensity d s (y i)) =
      -(Fintype.card ι:ℝ)*log (sqrt (2*Real.pi*s))-(∑ i, (y i-d)^2)/(2*s) := by
    simp only [normalLogDensity_centered, Finset.sum_sub_distrib, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul, Finset.sum_div]
    ring
  rw [productNormal_eq_exp _ hs, ← exp_add, he]
  apply exp_le_exp.mpr
  calc
    _ ≤ 3/(8*s)*(∑ i, (y i-d)^2)+3*(Fintype.card ι:ℝ)*j/2+
        (-(Fintype.card ι:ℝ)*log (sqrt (2*Real.pi*s))-(∑ i, (y i-d)^2)/(2*s)) :=
      by linarith only [hψ]
    _ = (Fintype.card ι:ℝ)*(-log (sqrt (2*Real.pi*s)))+3*(Fintype.card ι:ℝ)*j/2+
        (-(∑ i, (y i-d)^2)/(8*s)) := by ring
    _ ≤ (Fintype.card ι:ℝ)*|log (sqrt (2*Real.pi*smin))|+3*(Fintype.card ι:ℝ)*j/2+
        (-(∑ i, (y i)^2)/(16*smax)+(Fintype.card ι:ℝ)*D^2/(8*smin)) :=
      add_le_add (by linarith only [hnlog]) (h1.trans (add_le_add h2 h3))
    _ = _ := by ring

end SKGap

end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ074_CM.SKGap_Localization_ScalarEmpirical
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Real Set Filter
open scoped NNReal ENNReal Topology
noncomputable section
open Real Set
noncomputable section
open MeasureTheory ProbabilityTheory Real Set Filter
open scoped Topology NNReal ENNReal BoundedContinuousFunction
open MeasureTheory ProbabilityTheory Filter Set Topology Real
open scoped NNReal ENNReal BoundedContinuousFunction
noncomputable section
open Set Filter Topology
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Topology Real
open scoped NNReal ENNReal BoundedContinuousFunction
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Topology Real
open scoped NNReal ENNReal BoundedContinuousFunction
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Topology Real
open scoped NNReal ENNReal
namespace SKGap
variable {ι : Type*} [Fintype ι] [Nonempty ι]

lemma scalarA_empirical (y : ι → ℝ) (j t σ : ℝ) :
    scalarA j (scalarEmpirical y t σ) = (Fintype.card ι:ℝ)⁻¹ *
      ∑ i, (y i-scalarD j (scalarEmpirical y t σ))*tanh (y i) := by
  unfold scalarA scalarM scalarEmpirical
  simp only [integral_empiricalLaw, sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum]
  ring

lemma empirical_scalar_cauchy (y : ι → ℝ) (j t σ : ℝ) :
    (scalarA j (scalarEmpirical y t σ))^2 ≤ scalarQMoment (empiricalLaw y)*
      ((Fintype.card ι:ℝ)⁻¹ * ∑ i, (y i-scalarD j (scalarEmpirical y t σ))^2) := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun i => y i-scalarD j (scalarEmpirical y t σ)) (fun i => tanh (y i))
  have hh := mul_le_mul_of_nonneg_left h (sq_nonneg (Fintype.card ι:ℝ)⁻¹)
  rw [scalarA_empirical, scalarQMoment, integral_empiricalLaw]
  nlinarith only [hh]

lemma scalar_empirical_quadratic_envelope (y : ι → ℝ) {j t σ : ℝ}
    (hj : 0 ≤ j) (ht : 0 ≤ t) (hs : 0 < scalarS j (scalarEmpirical y t σ)) :
    (Fintype.card ι:ℝ)*scalarPsi j (scalarEmpirical y t σ) ≤
      3/(8*scalarS j (scalarEmpirical y t σ)) *
        (∑ i, (y i-scalarD j (scalarEmpirical y t σ))^2)+3*(Fintype.card ι:ℝ)*j/2 := by
  have hn : (0:ℝ) < Fintype.card ι := by exact_mod_cast (Fintype.card_pos (α := ι))
  have h := scalar_quadratic_envelope hj (scalarQMoment_bounds (empiricalLaw y)).1
    (scalarQMoment_bounds (empiricalLaw y)).2 hs (scalar_consistency (p := scalarEmpirical y t σ) ht)
    (show 0 ≤ (Fintype.card ι:ℝ)⁻¹*∑ i, (y i-scalarD j (scalarEmpirical y t σ))^2 by positivity)
    (empirical_scalar_cauchy y j t σ)
  have hh := mul_le_mul_of_nonneg_left h hn.le
  change (Fintype.card ι:ℝ)*scalarPsi j (scalarEmpirical y t σ) ≤ _ at hh
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  field_simp

lemma scalar_empirical_parameter_bounds (y : ι → ℝ) {j t σ T : ℝ}
    (hj : 0 ≤ j) (ht : 0 ≤ t) (htT : t ≤ T) (hσ : 0 ≤ σ) (hσ1 : σ ≤ 1) :
    |scalarD j (scalarEmpirical y t σ)| ≤ T+j ∧ scalarS j (scalarEmpirical y t σ) ≤ T+1+j := by
  have hM := scalarM_bounds (empiricalLaw y)
  have hq := (scalarQMoment_bounds (empiricalLaw y)).2
  constructor
  · unfold scalarD scalarEmpirical
    dsimp only
    calc
      |t+j*scalarM (empiricalLaw y)| ≤ |t|+|j*scalarM (empiricalLaw y)| := abs_add_le _ _
      _ ≤ T+j := by
        rw [abs_of_nonneg ht, abs_mul, abs_of_nonneg hj]
        nlinarith
  · unfold scalarS scalarEmpirical
    dsimp only
    have hsq : σ^2 ≤ 1 := by nlinarith
    nlinarith

theorem scalar_integrand_envelope {j T smin : ℝ} (hj : 0 ≤ j) (hT : 0 ≤ T) (hsmin : 0 < smin)
    (y : ι → ℝ) {t σ : ℝ} (ht : 0 ≤ t) (htT : t ≤ T) (hσ : 0 ≤ σ) (hσ1 : σ ≤ 1)
    (hsl : smin ≤ scalarS j (scalarEmpirical y t σ)) :
    scalarIntegrand j t σ y ≤
      exp ((Fintype.card ι:ℝ)*(|log (sqrt (2*Real.pi*smin))|+3*j/2+(T+j)^2/(8*smin))-
        (1/(16*(T+1+j)))*∑ i, (y i)^2) := by
  have hb := scalar_empirical_parameter_bounds y hj ht htT hσ hσ1
  have hd : (scalarD j (scalarEmpirical y t σ))^2 ≤ (T+j)^2 := by
    have hD : 0 ≤ T+j := add_nonneg hT hj
    have hsq := (sq_le_sq₀ (abs_nonneg _) hD).mpr hb.1
    simpa only [sq_abs] using hsq
  exact gaussian_pointwise_envelope y hsmin hsl hb.2 hd
    (scalar_empirical_quadratic_envelope y hj ht (hsmin.trans_le hsl))

end SKGap

namespace SKGap

lemma empirical_momentBall {ι : Type*} [Fintype ι] [Nonempty ι]
    (y : ι → ℝ) {R : ℝ} (_hR : 0 ≤ R)
    (h : ∑ i, (y i)^2 ≤ (Fintype.card ι:ℝ)*R) : empiricalLaw y ∈ momentBall R := by
  change (∫⁻ x : ℝ, ENNReal.ofReal (x^2) ∂empiricalLaw y) ≤ ENNReal.ofReal R
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_empiricalLaw y _) (ae_of_all _ sq_nonneg)]
  apply ENNReal.ofReal_le_ofReal
  rw [integral_empiricalLaw]
  have hn : (0:ℝ) < Fintype.card ι := by exact_mod_cast (Fintype.card_pos (α := ι))
  have hh := mul_le_mul_of_nonneg_left h (inv_nonneg.mpr hn.le)
  simpa only [← mul_assoc, inv_mul_cancel₀ hn.ne', one_mul] using hh

lemma isCompact_scalarBox (j R T smin : ℝ) : IsCompact (scalarBox j R T smin) :=
  ((isCompact_momentBall R).prod (isCompact_Icc.prod isCompact_Icc)).inter_right
    (isClosed_le continuous_const (continuous_scalarS j))

theorem scalar_uniform_tail {j T smin : ℝ} (hj : 0 ≤ j) (hT : 0 ≤ T) (hsmin : 0 < smin)
    (L : ℝ) : ∃ R > 0, ∀ n : ℕ, ∀ hn : 0 < n,
      ∀ t ∈ Icc 0 T, ∀ σ ∈ Icc 0 1, ∀ E : Set (Fin n → ℝ), MeasurableSet E →
      (∀ y ∈ E, smin ≤ scalarS j (@scalarEmpirical (Fin n) _ ⟨⟨0,hn⟩⟩ y t σ)) →
      (∀ y ∈ E, (n:ℝ)*R ≤ ∑ i, (y i)^2) →
      (∫⁻ y in E, ENNReal.ofReal (@scalarIntegrand (Fin n) _ ⟨⟨0,hn⟩⟩ j t σ y)) ≤
        ENNReal.ofReal (exp (-L*(n:ℝ))) := by
  let c := 1/(16*(T+1+j))
  let C := |log (sqrt (2*Real.pi*smin))|+3*j/2+(T+j)^2/(8*smin)
  have hc : 0 < c := by dsimp [c]; positivity
  obtain ⟨R,hR,hrate⟩ := choose_quadratic_tail_radius (C := C) hc L
  refine ⟨R,hR,?_⟩
  intro n hn t ht σ hσ E hE hs htE
  let : Nonempty (Fin n) := ⟨⟨0,hn⟩⟩
  have he := quadratic_envelope_tail (C := C) hc hE (scalarIntegrand j t σ)
    (fun y hy => scalar_integrand_envelope hj hT hsmin y ht.1 ht.2 hσ.1 hσ.2 (hs y hy))
    (by simpa only [Fintype.card_fin] using htE)
  simp only [Fintype.card_fin] at he
  refine he.trans (ENNReal.ofReal_le_ofReal (exp_le_exp.mpr ?_))
  have h := mul_le_mul_of_nonneg_left hrate (show (0:ℝ) ≤ n from Nat.cast_nonneg _)
  nlinarith only [h]

lemma lintegral_split_le {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (f : α → ℝ≥0∞) (E B : Set α) :
    (∫⁻ x in E, f x ∂μ) ≤ (∫⁻ x in E ∩ B, f x ∂μ)+(∫⁻ x in E ∩ Bᶜ, f x ∂μ) := by
  have h : E = (E ∩ B) ∪ (E ∩ Bᶜ) := by aesop
  conv_lhs => rw [h]
  exact lintegral_union_le _ _ _

end SKGap

end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ074_CM.SKGap_Localization_ScalarClosedIsolation
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Real Set Filter
open scoped NNReal ENNReal Topology
noncomputable section
open Real Set
noncomputable section
open MeasureTheory ProbabilityTheory Real Set Filter
open scoped Topology NNReal ENNReal BoundedContinuousFunction
open MeasureTheory ProbabilityTheory Filter Set Topology Real
open scoped NNReal ENNReal BoundedContinuousFunction
noncomputable section
open Set Filter Topology
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Topology Real
open scoped NNReal ENNReal BoundedContinuousFunction
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Topology Real
open scoped NNReal ENNReal BoundedContinuousFunction
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Topology Real
open scoped NNReal ENNReal
namespace SKGap

theorem scalar_closed_isolation_s2_oai {j T smin : ℝ} (hj : 0 < j) (hj1 : j < 1)
    (hT : 0 ≤ T) (hsmin : 0 < smin) {C : Set ScalarPoint} (hC : IsClosed C)
    (hne : ∀ p ∈ C, p.2.1 ∈ Icc 0 T → p.2.2 = 0 → p.1 ≠ scalarCurve j p.2.1) :
    ∃ a > 0, ∃ δ > 0, ∃ N : ℕ, ∀ n ≥ N, ∀ hn : 0 < n, ∀ t ∈ Icc 0 T,
      ∀ σ ∈ Icc 0 (min δ 1), ∀ E : Set (Fin n → ℝ), MeasurableSet E →
      (∀ y ∈ E, @scalarEmpirical (Fin n) _ ⟨⟨0,hn⟩⟩ y t σ ∈ C) →
      (∀ y ∈ E, smin ≤ scalarS j (@scalarEmpirical (Fin n) _ ⟨⟨0,hn⟩⟩ y t σ)) →
      (∫⁻ y in E, ENNReal.ofReal (@scalarIntegrand (Fin n) _ ⟨⟨0,hn⟩⟩ j t σ y)) ≤
        ENNReal.ofReal (exp (-a*(n:ℝ))) := by
  obtain ⟨R,hR,hTail⟩ := scalar_uniform_tail hj.le hT hsmin 1
  let K := scalarBox j R T smin ∩ C
  have hK : IsCompact K := (isCompact_scalarBox j R T smin).inter_right hC
  have hmom : K ⊆ scalarMomentDomain R := fun p hp => ⟨hp.1.1.1,mem_univ _⟩
  obtain ⟨a,ha,δ,hδ,N,hN⟩ := scalar_compact_isolation hj hj1 hR.le hK hmom
    (fun p hp => hp.1.1.2.1.1) (fun p hp => hp.1.1.2.2.1)
    (fun p hp => hsmin.trans_le hp.1.2) (fun p hp hz => hne p hp.2 hp.1.1.2.1 hz)
  let b := min a 1
  have hb : 0 < b := lt_min ha zero_lt_one
  obtain ⟨M,hM⟩ := absorb_finite_exponential_factor 2 (half_pos hb)
  refine ⟨b/2,half_pos hb,δ,hδ,max N M,?_⟩
  intro n hn hn' t ht σ hσ E hE hforbid hs
  let : Nonempty (Fin n) := ⟨⟨0,hn'⟩⟩
  have hσ' : σ ∈ Icc (0:ℝ) 1 := ⟨hσ.1,hσ.2.trans (min_le_right _ _)⟩
  let B : Set (Fin n → ℝ) := {y | ∑ i, (y i)^2 ≤ (n:ℝ)*R}
  have hB : MeasurableSet B := isClosed_le (by fun_prop) continuous_const |>.measurableSet
  have hc := hN n (le_trans (le_max_left _ _) hn) hn' (fun y => scalarEmpirical y t σ)
    (E ∩ B) (hE.inter hB) (fun y hy => ⟨⟨⟨⟨empirical_momentBall y hR.le
      (by simpa only [Fintype.card_fin] using (show ∑ i, (y i)^2 ≤ (n:ℝ)*R from hy.2)),ht,hσ'⟩,
      hs y hy.1⟩,hforbid y hy.1⟩,hσ.2.trans (min_le_left _ _)⟩)
    (fun _ _ => rfl) (fun _ hy => hy.2)
  have hc' : (∫⁻ y in E ∩ B, ENNReal.ofReal (scalarIntegrand j t σ y)) ≤
      ENNReal.ofReal (exp (-b*(n:ℝ))) := by
    have hab : exp (-a*(n:ℝ)) ≤ exp (-b*(n:ℝ)) := exp_le_exp.mpr (by
      have hh := mul_le_mul_of_nonneg_right (min_le_left a 1) (Nat.cast_nonneg (α := ℝ) n)
      dsimp [b]; linarith only [hh])
    simpa only [scalarIntegrand, Fintype.card_fin] using hc.trans (ENNReal.ofReal_le_ofReal hab)
  have htail := hTail n hn' t ht σ hσ' (E ∩ Bᶜ) (hE.inter hB.compl)
    (fun y hy => hs y hy.1) (fun y hy => le_of_lt (not_le.mp hy.2))
  have he : exp (-(1:ℝ)*(n:ℝ)) ≤ exp (-b*(n:ℝ)) := exp_le_exp.mpr (by
    have hh := mul_le_mul_of_nonneg_right (min_le_right a 1) (Nat.cast_nonneg (α := ℝ) n)
    dsimp [b]; linarith only [hh])
  have htotal := (lintegral_split_le volume (fun y => ENNReal.ofReal (scalarIntegrand j t σ y)) E B).trans
    (add_le_add hc' (htail.trans (ENNReal.ofReal_le_ofReal he)))
  have hadd : ENNReal.ofReal (exp (-b*(n:ℝ)))+ENNReal.ofReal (exp (-b*(n:ℝ))) =
      ENNReal.ofReal (2*exp ((n:ℝ)*(-b))) := by
    rw [← ENNReal.ofReal_add (exp_pos _).le (exp_pos _).le]
    congr 1
    ring_nf
  rw [hadd] at htotal
  refine htotal.trans (ENNReal.ofReal_le_ofReal ?_)
  convert hM n (le_trans (le_max_right _ _) hn) (-b) using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  ring

end SKGap

end
end
end
end
end
end
end
end

end OAI
end

theorem solution : type_of% @OAI.SKGap.scalar_closed_isolation_s2_oai := @OAI.SKGap.scalar_closed_isolation_s2_oai
