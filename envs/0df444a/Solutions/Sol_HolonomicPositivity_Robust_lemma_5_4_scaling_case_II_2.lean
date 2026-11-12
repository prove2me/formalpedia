-- Prove2me | solution 1 for HolonomicPositivity.Robust.lemma_5_4_scaling_case_II_2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T15:42:56.725432+00:00
-- url     : https://prove2.me/submissions/9bf93a82-80d2-4d4e-a178-eadace19167e

import Mathlib
import Definitions.Def_HolonomicPositivity_Robust_Comparison
import Definitions.Def_HolonomicPositivity_Robust_Conditions

section
set_option autoImplicit false
open Filter Topology Asymptotics

namespace HolonomicPositivity.Dev.RatExp
open HolonomicPositivity.Robust

lemma ev_eq (U : RatFunc ℝ) (x : ℝ) : ev U x = U.num.eval x / U.denom.eval x := by
  simp [ev, RatFunc.eval, Polynomial.eval₂_id]

lemma eventually_denom_ne (U : RatFunc ℝ) : ∀ᶠ x : ℝ in atTop, U.denom.eval x ≠ 0 := by
  filter_upwards [Polynomial.eventually_atTop_not_isRoot U.denom U.denom_ne_zero] with x hx
  exact hx

lemma eventually_ev_ne (U : RatFunc ℝ) (hU : U ≠ 0) : ∀ᶠ x : ℝ in atTop, ev U x ≠ 0 := by
  filter_upwards [Polynomial.eventually_atTop_not_isRoot U.denom U.denom_ne_zero,
    Polynomial.eventually_atTop_not_isRoot U.num (RatFunc.num_ne_zero hU)] with x h1 h2
  rw [ev_eq]
  exact div_ne_zero h2 h1

lemma ev_add (U V : RatFunc ℝ) : ∀ᶠ x : ℝ in atTop, ev (U + V) x = ev U x + ev V x := by
  filter_upwards [eventually_denom_ne U, eventually_denom_ne V] with x hU hV
  exact RatFunc.eval_add _ _ (by simpa using hU) (by simpa using hV)

lemma ev_mul (U V : RatFunc ℝ) : ∀ᶠ x : ℝ in atTop, ev (U * V) x = ev U x * ev V x := by
  filter_upwards [eventually_denom_ne U, eventually_denom_ne V] with x hU hV
  exact RatFunc.eval_mul _ _ (by simpa using hU) (by simpa using hV)

lemma ev_inv (U : RatFunc ℝ) : ∀ᶠ x : ℝ in atTop, ev U⁻¹ x = (ev U x)⁻¹ := by
  by_cases hU : U = 0
  · subst hU; simp [ev]
  · filter_upwards [ev_mul U U⁻¹, eventually_ev_ne U hU] with x h1 h2
    rw [mul_inv_cancel₀ hU] at h1
    have : ev (1 : RatFunc ℝ) x = 1 := by simp [ev]
    rw [this] at h1
    exact eq_inv_of_mul_eq_one_right h1.symm

/-- `f` agrees eventually (at `+∞`) with the evaluation of the rational function `U`. -/
def Rep (f : ℝ → ℝ) (U : RatFunc ℝ) : Prop := ∀ᶠ x : ℝ in atTop, f x = ev U x

lemma Rep.add {f g : ℝ → ℝ} {U V : RatFunc ℝ} (hf : Rep f U) (hg : Rep g V) :
    Rep (fun x => f x + g x) (U + V) := by
  filter_upwards [hf, hg, ev_add U V] with x h1 h2 h3
  rw [h3, h1, h2]

lemma Rep.mul {f g : ℝ → ℝ} {U V : RatFunc ℝ} (hf : Rep f U) (hg : Rep g V) :
    Rep (fun x => f x * g x) (U * V) := by
  filter_upwards [hf, hg, ev_mul U V] with x h1 h2 h3
  rw [h3, h1, h2]

lemma Rep.inv {f : ℝ → ℝ} {U : RatFunc ℝ} (hf : Rep f U) :
    Rep (fun x => (f x)⁻¹) U⁻¹ := by
  filter_upwards [hf, ev_inv U] with x h1 h2
  rw [h2, h1]

lemma Rep.const (c : ℝ) : Rep (fun _ => c) (RatFunc.C c) :=
  Eventually.of_forall fun x => by simp [ev]

lemma Rep.X : Rep (fun x => x) RatFunc.X :=
  Eventually.of_forall fun x => by simp [ev]


/-! ### Eventual sign of a rational function -/

/-! ### Taylor expansion at infinity -/

end HolonomicPositivity.Dev.RatExp
end

section
set_option autoImplicit false

namespace HolonomicPositivity.Dev.Iface
open HolonomicPositivity.Robust

/-- What a case of Lemma 5.4 must produce: a scaling S satisfying (1), B > 0, inequality (6) for A/(B B(x-1)), and (3). -/
def Goal (P Q : RatFunc ℝ) : Prop :=
  ∃ S : RatFunc ℝ, EventuallyGE (ev S) (fun _ => 0) ∧ EventuallyGT (scaledB S) (fun _ => 0) ∧
    SatisfiesInequalitySix (scaledA P S) (scaledB S) ∧ EventuallyGE (scaledC P Q S) (fun _ => 0)

def Case2Stmt : Prop :=
  ∀ (P Q : RatFunc ℝ) (p₀ p₁ p₂ p₃ : ℝ), HasTaylorExpansion P p₀ p₁ p₂ p₃ →
    GeMod (ev P) (fun x => -(1 / 3) - 1 / (9 * x ^ 2)) (-3) →
    LtMod (ev P) (fun x => 1 - 2 / x) (-2) →
    p₀ = -(1 / 3) → 0 < p₁ → GeMod (ev Q) (thresholdTwo p₁) (-2) → Goal P Q

end HolonomicPositivity.Dev.Iface
end

section
set_option autoImplicit false
open Filter Topology Asymptotics

namespace HolonomicPositivity.Dev.Util54
open HolonomicPositivity.Robust HolonomicPositivity.Dev.RatExp

/-- The explicit scaling `a + b/x + c/x²`. -/
noncomputable def Sf (a b c x : ℝ) : ℝ := a + b / x + c / x ^ 2

lemma exists_S (a b c : ℝ) : ∃ S : RatFunc ℝ, ∀ᶠ x : ℝ in atTop, ev S x = Sf a b c x := by
  have h : Rep (fun x : ℝ => a + b * x⁻¹ + c * (x⁻¹ * x⁻¹))
      (RatFunc.C a + RatFunc.C b * RatFunc.X⁻¹ + RatFunc.C c * (RatFunc.X⁻¹ * RatFunc.X⁻¹)) :=
    ((Rep.const a).add ((Rep.const b).mul Rep.X.inv)).add ((Rep.const c).mul (Rep.X.inv.mul Rep.X.inv))
  refine ⟨RatFunc.C a + RatFunc.C b * RatFunc.X⁻¹ + RatFunc.C c * (RatFunc.X⁻¹ * RatFunc.X⁻¹), ?_⟩
  filter_upwards [h] with x hx
  rw [← hx]
  simp only [Sf, div_eq_mul_inv]
  ring

lemma shift_eq {S : RatFunc ℝ} {f : ℝ → ℝ} (h : ∀ᶠ x : ℝ in atTop, ev S x = f x) (c : ℝ) :
    ∀ᶠ x : ℝ in atTop, ev S (x + c) = f (x + c) :=
  (tendsto_atTop_add_const_right atTop c tendsto_id).eventually h

lemma geMod_congr {U U' V : ℝ → ℝ} {v : ℤ} (h : ∀ᶠ x : ℝ in atTop, U' x = U x)
    (hU : GeMod U V v) : GeMod U' V v := by
  rcases hU with hU | hU
  · left
    unfold EventuallyGT at *
    filter_upwards [h, hU] with x h1 h2
    rw [h1]; exact h2
  · right
    unfold EqMod at *
    exact hU.congr' (h.mono fun x hx => by simp only [hx]) EventuallyEq.rfl

lemma goal_of (P Q S : RatFunc ℝ) (Sf' : ℝ → ℝ) (hS : ∀ᶠ x : ℝ in atTop, ev S x = Sf' x)
    (h0 : ∀ᶠ x : ℝ in atTop, 0 ≤ Sf' x)
    (hB : ∀ᶠ x : ℝ in atTop, 0 < 1 - Sf' (x + 2))
    (h6 : GeMod (fun x => ((1 - Sf' (x + 2)) * Sf' (x + 1) + ev P x) /
        ((1 - Sf' (x + 2)) * (1 - Sf' (x - 1 + 2)))) (fun x => -(1 / 4) - 1 / (16 * x ^ 2)) (-3))
    (hC : ∀ᶠ x : ℝ in atTop,
      0 ≤ ((1 - Sf' (x + 2)) * Sf' (x + 1) + ev P x) * Sf' x + ev Q x) :
    HolonomicPositivity.Dev.Iface.Goal P Q := by
  have hS0 := shift_eq hS 0
  have hS1 := shift_eq hS 1
  have hS2 := shift_eq hS 2
  simp only [add_zero] at hS0
  refine ⟨S, ?_, ?_, ?_, ?_⟩
  · unfold EventuallyGE
    filter_upwards [hS0, h0] with x a b
    rw [a]; exact b
  · unfold EventuallyGT
    filter_upwards [hS2, hB] with x a b
    unfold scaledB
    rw [a]; exact b
  · unfold SatisfiesInequalitySix
    refine geMod_congr ?_ h6
    filter_upwards [hS1, hS2] with x a b
    simp only [scaledA, scaledB]
    rw [show x - 1 + 2 = x + 1 by ring, a, b]
  · unfold EventuallyGE
    filter_upwards [hS0, hS1, hS2, hC] with x a0 a1 a2 c
    simp only [scaledC, scaledA, scaledB]
    rw [a0, a1, a2]; exact c

lemma tendsto_h {h f : ℝ → ℝ} (hc : ContinuousAt h 0) (hf : ∀ᶠ x : ℝ in atTop, f x = h (1 / x)) :
    Tendsto f atTop (𝓝 (h 0)) := by
  have h1 : Tendsto (fun x : ℝ => 1 / x) atTop (𝓝 0) := by
    simpa using tendsto_inv_atTop_zero (𝕜 := ℝ)
  exact (hc.tendsto.comp h1).congr' (hf.mono fun x hx => hx.symm)

lemma tendsto_Sf (a b c d : ℝ) : Tendsto (fun x : ℝ => Sf a b c (x + d)) atTop (𝓝 a) := by
  have hx : Tendsto (fun x : ℝ => x + d) atTop atTop :=
    tendsto_atTop_add_const_right atTop d tendsto_id
  have h1 : Tendsto (fun x : ℝ => b / (x + d)) atTop (𝓝 0) := tendsto_const_nhds.div_atTop hx
  have h2 : Tendsto (fun x : ℝ => c / (x + d) ^ 2) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop ((tendsto_pow_atTop (by norm_num : 2 ≠ 0)).comp hx)
  simpa [Sf] using (tendsto_const_nhds (x := a)).add h1 |>.add h2

lemma eqMod_bound {U V : ℝ → ℝ} {v : ℤ} {n : ℕ} (hv : v = -(n : ℤ)) (h : EqMod U V v) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ x : ℝ in atTop, |U x - V x| ≤ K / x ^ n := by
  subst hv
  obtain ⟨C, hC⟩ := h.bound
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  filter_upwards [hC, eventually_gt_atTop (0 : ℝ)] with x h1 h2
  rw [Real.norm_eq_abs, Real.norm_eq_abs, zpow_neg, zpow_natCast, abs_inv,
    abs_of_pos (pow_pos h2 n)] at h1
  calc |U x - V x| ≤ C * (x ^ n)⁻¹ := h1
    _ ≤ max C 0 * (x ^ n)⁻¹ := by
      gcongr; exact le_max_left _ _
    _ = max C 0 / x ^ n := by rw [div_eq_mul_inv]

lemma geMod_lower {U V : ℝ → ℝ} {v : ℤ} {n : ℕ} (hv : v = -(n : ℤ)) (h : GeMod U V v) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ᶠ x : ℝ in atTop, V x - M / x ^ n ≤ U x := by
  rcases h with h | h
  · refine ⟨0, le_rfl, ?_⟩
    filter_upwards [h] with x hx
    simp only [zero_div, sub_zero]; exact hx.le
  · obtain ⟨K, hK, hb⟩ := eqMod_bound hv h
    refine ⟨K, hK, ?_⟩
    filter_upwards [hb] with x hx
    have := (abs_le.mp hx).1
    linarith

lemma tendsto_pow_mul_zero {E : ℝ → ℝ} {K : ℝ} {n k : ℕ} (hk : k < n)
    (hE : ∀ᶠ x : ℝ in atTop, |E x| ≤ K / x ^ n) :
    Tendsto (fun x => x ^ k * E x) atTop (𝓝 0) := by
  obtain ⟨j, rfl⟩ : ∃ j, n = k + j + 1 := ⟨n - k - 1, by omega⟩
  have hlim : Tendsto (fun x : ℝ => K / x ^ (j + 1)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_pow_atTop (by omega))
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [hE, eventually_gt_atTop (0 : ℝ)] with x h1 h2
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (pow_pos h2 k)]
  calc x ^ k * |E x| ≤ x ^ k * (K / x ^ (k + j + 1)) := by gcongr
    _ = K / x ^ (j + 1) := by
      field_simp
      ring

end HolonomicPositivity.Dev.Util54
end

section
set_option autoImplicit false
open Filter Topology Asymptotics

namespace HolonomicPositivity.Dev.Case2
open HolonomicPositivity.Robust HolonomicPositivity.Dev.RatExp HolonomicPositivity.Dev.Util54

/-- `x * F1 (x)` as a rational function of `t = 1/x` (case II-2, inequality (6)). -/
noncomputable def h2a (p1 p2 s : ℝ) (t : ℝ) : ℝ :=
  (8*p1*t^2 + 12*p1*t + 4*p1 + 8*p2*t^3 + 12*p2*t^2 + 4*p2*t - 3*s^2*t + 2*s*t) /
    (4*(t + 1)*(2*t + 1))

noncomputable def h2b (p1 p2 s : ℝ) (t : ℝ) : ℝ :=
  (18*p1*s*t^2 + 27*p1*s*t + 9*p1*s + 18*p2*s*t^3 + 27*p2*s*t^2 + 9*p2*s*t + 6*p2*t^2 + 9*p2*t + 3*p2 - 9*s^3*t + 9*s^2*t - 2*s*t) /
    (9*(t + 1)*(2*t + 1))

theorem case2 : HolonomicPositivity.Dev.Iface.Case2Stmt := by
  intro P Q p0 p1 p2 p3 hT _ _ hp0 hp1 hQ
  subst hp0
  obtain ⟨K, hK0, hK⟩ := eqMod_bound (n := 4) (by norm_num) hT
  obtain ⟨M, hM0, hM⟩ := geMod_lower (n := 2) (by norm_num) hQ
  set s : ℝ := (M + 1 - p2 / 3) / p1 with hs
  have hps : p1 * s = M + 1 - p2 / 3 := by rw [hs]; field_simp
  obtain ⟨S, hS⟩ := exists_S (1 / 3) s 0
  have hE : Tendsto (fun x : ℝ => x ^ 2 * (ev P x - (-(1 / 3) + p1 / x + p2 / x ^ 2 + p3 / x ^ 3)))
      atTop (𝓝 0) := tendsto_pow_mul_zero (by norm_num) hK
  have hε2 : Tendsto (fun x : ℝ => x ^ 2 * (ev P x - (-(1 / 3) + p1 / x + p2 / x ^ 2)))
      atTop (𝓝 0) := by
    have h3 : Tendsto (fun x : ℝ => p3 / x) atTop (𝓝 0) := tendsto_const_nhds.div_atTop tendsto_id
    have := h3.add hE
    rw [add_zero] at this
    refine this.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    field_simp
    ring
  have hε1 : Tendsto (fun x : ℝ => x * (ev P x - (-(1 / 3) + p1 / x + p2 / x ^ 2)))
      atTop (𝓝 0) := by
    have := tendsto_inv_atTop_zero.mul hε2
    rw [mul_zero] at this
    refine this.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    field_simp
  have hid1 : ∀ᶠ x : ℝ in atTop,
      x * (((1 - Sf (1 / 3) s 0 (x + 2)) * Sf (1 / 3) s 0 (x + 1) + (-(1 / 3) + p1 / x + p2 / x ^ 2))
        + (1 - Sf (1 / 3) s 0 (x + 2)) * (1 - Sf (1 / 3) s 0 (x - 1 + 2)) / 4) = h2a p1 p2 s (1 / x) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    have h0 : x ≠ 0 := hx.ne'
    have h1 : x + 1 ≠ 0 := by positivity
    have h2 : x + 2 ≠ 0 := by positivity
    have h3 : 1 + x ≠ 0 := by positivity
    have h4 : 2 + x ≠ 0 := by positivity
    rw [show x - 1 + 2 = x + 1 by ring]
    simp only [Sf, h2a]
    field_simp
    ring
  have hc1 : ContinuousAt (h2a p1 p2 s) 0 := by
    unfold h2a; fun_prop (disch := norm_num)
  have hF1 := (tendsto_h hc1 hid1).add hε1
  have hl1 : h2a p1 p2 s 0 = p1 := by unfold h2a; norm_num
  rw [hl1, add_zero] at hF1
  have hBt : ∀ d : ℝ, Tendsto (fun x : ℝ => 1 - Sf (1 / 3) s 0 (x + d)) atTop (𝓝 (2 / 3)) := by
    intro d
    have h := (tendsto_const_nhds (x := (1 : ℝ))).sub (tendsto_Sf (1 / 3) s 0 d)
    rwa [show (1 : ℝ) - 1 / 3 = 2 / 3 by norm_num] at h
  have hB1 : Tendsto (fun x : ℝ => 1 - Sf (1 / 3) s 0 (x - 1 + 2)) atTop (𝓝 (2 / 3)) := by
    simpa only [show ∀ x : ℝ, x - 1 + 2 = x + 1 from fun x => by ring] using hBt 1
  have hS0 : Tendsto (Sf (1 / 3) s 0) atTop (𝓝 (1 / 3)) := by
    simpa only [add_zero] using tendsto_Sf (1 / 3) s 0 0
  refine goal_of P Q S (Sf (1 / 3) s 0) hS ?_ ?_ ?_ ?_
  · exact (hS0.eventually_const_lt (by norm_num : (0 : ℝ) < 1 / 3)).mono fun x hx => hx.le
  · exact (hBt 2).eventually_const_lt (by norm_num)
  · left
    unfold EventuallyGT
    filter_upwards [hF1.eventually_const_lt hp1, (hBt 2).eventually_const_lt (by norm_num : (0 : ℝ) < 2 / 3),
      hB1.eventually_const_lt (by norm_num : (0 : ℝ) < 2 / 3), eventually_gt_atTop (0 : ℝ)]
      with x h1 hB hB1' hx
    have e : x * (((1 - Sf (1 / 3) s 0 (x + 2)) * Sf (1 / 3) s 0 (x + 1) + (-(1 / 3) + p1 / x + p2 / x ^ 2))
        + (1 - Sf (1 / 3) s 0 (x + 2)) * (1 - Sf (1 / 3) s 0 (x - 1 + 2)) / 4)
        + x * (ev P x - (-(1 / 3) + p1 / x + p2 / x ^ 2)) =
        x * ((1 - Sf (1 / 3) s 0 (x + 2)) * Sf (1 / 3) s 0 (x + 1) + ev P x
          + (1 - Sf (1 / 3) s 0 (x + 2)) * (1 - Sf (1 / 3) s 0 (x - 1 + 2)) / 4) := by ring
    rw [e] at h1
    have hpos : 0 < (1 - Sf (1 / 3) s 0 (x + 2)) * Sf (1 / 3) s 0 (x + 1) + ev P x
          + (1 - Sf (1 / 3) s 0 (x + 2)) * (1 - Sf (1 / 3) s 0 (x - 1 + 2)) / 4 := by
      by_contra hneg
      push Not at hneg
      nlinarith [mul_nonneg hx.le (neg_nonneg.mpr hneg)]
    rw [lt_div_iff₀ (mul_pos hB hB1')]
    have hq : 0 < 1 / (16 * x ^ 2) * ((1 - Sf (1 / 3) s 0 (x + 2)) *
        (1 - Sf (1 / 3) s 0 (x - 1 + 2))) := by positivity
    nlinarith
  · have hid2 : ∀ᶠ x : ℝ in atTop,
        x ^ 2 * (((1 - Sf (1 / 3) s 0 (x + 2)) * Sf (1 / 3) s 0 (x + 1) + (-(1 / 3) + p1 / x + p2 / x ^ 2))
          * Sf (1 / 3) s 0 x + (1 / 27 - p1 / (3 * x))) = h2b p1 p2 s (1 / x) := by
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
      have h0 : x ≠ 0 := hx.ne'
      have h1 : x + 1 ≠ 0 := by positivity
      have h2 : x + 2 ≠ 0 := by positivity
      have h3 : 1 + x ≠ 0 := by positivity
      have h4 : 2 + x ≠ 0 := by positivity
      simp only [Sf, h2b]
      field_simp
      ring
    have hc2 : ContinuousAt (h2b p1 p2 s) 0 := by
      unfold h2b; fun_prop (disch := norm_num)
    have hF2 := (tendsto_h hc2 hid2).add (hε2.mul hS0)
    have hl2 : h2b p1 p2 s 0 + 0 * (1 / 3) = M + 1 := by
      unfold h2b; norm_num; linarith
    rw [hl2] at hF2
    filter_upwards [hF2.eventually_const_lt (by linarith : M < M + 1), hM, eventually_gt_atTop (0 : ℝ)]
      with x h1 hMx hx
    unfold thresholdTwo at hMx
    have e : x ^ 2 * (((1 - Sf (1 / 3) s 0 (x + 2)) * Sf (1 / 3) s 0 (x + 1) + (-(1 / 3) + p1 / x + p2 / x ^ 2))
          * Sf (1 / 3) s 0 x + (1 / 27 - p1 / (3 * x)))
        + x ^ 2 * (ev P x - (-(1 / 3) + p1 / x + p2 / x ^ 2)) * Sf (1 / 3) s 0 x =
        x ^ 2 * (((1 - Sf (1 / 3) s 0 (x + 2)) * Sf (1 / 3) s 0 (x + 1) + ev P x)
          * Sf (1 / 3) s 0 x + (1 / 27 - p1 / (3 * x))) := by ring
    rw [e] at h1
    have h2 : M / x ^ 2 < ((1 - Sf (1 / 3) s 0 (x + 2)) * Sf (1 / 3) s 0 (x + 1) + ev P x)
          * Sf (1 / 3) s 0 x + (1 / 27 - p1 / (3 * x)) := by
      rw [div_lt_iff₀ (by positivity)]
      nlinarith
    linarith

end HolonomicPositivity.Dev.Case2
end

section
set_option autoImplicit false

namespace HolonomicPositivity.Robust

theorem chk_lemma_5_4_scaling_case_II_2 (P Q : RatFunc ℝ) (p₀ p₁ p₂ p₃ : ℝ)
    (hT : HasTaylorExpansion P p₀ p₁ p₂ p₃)
    (hge : GeMod (ev P) (fun x => -(1 / 3) - 1 / (9 * x ^ 2)) (-3))
    (hlt : LtMod (ev P) (fun x => 1 - 2 / x) (-2))
    (hp1 : p₀ = -(1 / 3))
    (hp2 : 0 < p₁)
    (hq : GeMod (ev Q) (thresholdTwo p₁) (-2)) :
    ∃ S : RatFunc ℝ, EventuallyGE (ev S) (fun _ => 0) ∧ EventuallyGT (scaledB S) (fun _ => 0) ∧
      SatisfiesInequalitySix (scaledA P S) (scaledB S) ∧ EventuallyGE (scaledC P Q S) (fun _ => 0) :=
  HolonomicPositivity.Dev.Case2.case2 P Q p₀ p₁ p₂ p₃ hT hge hlt hp1 hp2 hq

end HolonomicPositivity.Robust
end

theorem solution : type_of% @HolonomicPositivity.Robust.chk_lemma_5_4_scaling_case_II_2 := @HolonomicPositivity.Robust.chk_lemma_5_4_scaling_case_II_2
