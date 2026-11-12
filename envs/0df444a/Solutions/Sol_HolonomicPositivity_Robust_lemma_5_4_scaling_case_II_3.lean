-- Prove2me | solution 1 for HolonomicPositivity.Robust.lemma_5_4_scaling_case_II_3
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T15:42:58.649532+00:00
-- url     : https://prove2.me/submissions/c36eb096-e28e-40a8-8b82-74cb855e2a9a

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

def Case3Stmt : Prop :=
  ∀ (P Q : RatFunc ℝ) (p₀ p₁ p₂ p₃ : ℝ), HasTaylorExpansion P p₀ p₁ p₂ p₃ →
    GeMod (ev P) (fun x => -(1 / 3) - 1 / (9 * x ^ 2)) (-3) →
    LtMod (ev P) (fun x => 1 - 2 / x) (-2) →
    p₀ = -(1 / 3) → p₁ = 0 → GeMod (ev Q) (thresholdThree p₂ p₃) (-4) → Goal P Q

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

lemma eqMod_of_tendsto {U V : ℝ → ℝ} {n : ℕ} {L : ℝ}
    (h : Tendsto (fun x => x ^ n * (U x - V x)) atTop (𝓝 L)) : EqMod U V (-(n : ℤ)) := by
  have hb : ∀ᶠ x : ℝ in atTop, |x ^ n * (U x - V x)| ≤ |L| + 1 := by
    have := h.abs
    filter_upwards [this.eventually (gt_mem_nhds (lt_add_one |L|))] with x hx using hx.le
  refine IsBigO.of_bound (|L| + 1) ?_
  filter_upwards [hb, eventually_gt_atTop (0 : ℝ)] with x h1 h2
  rw [Real.norm_eq_abs, Real.norm_eq_abs, zpow_neg, zpow_natCast, abs_inv,
    abs_of_pos (pow_pos h2 n)]
  rw [abs_mul, abs_of_pos (pow_pos h2 n)] at h1
  rw [← div_eq_mul_inv, le_div_iff₀ (pow_pos h2 n)]
  linarith [mul_comm (x ^ n) |U x - V x|]

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

namespace HolonomicPositivity.Dev.Case3
open HolonomicPositivity.Robust HolonomicPositivity.Dev.RatExp HolonomicPositivity.Dev.Util54

/-- `x³ · (A + B B'/4 + B B'/(16x²))` and `x⁴ · (A S + R_P)` as rational functions of `t = 1/x`
(case II-3), after substituting `s₁ = 1/3 - u`, `p₂ = 3u²/4 - 1/9`. -/
noncomputable def h3a (p3 s2 u : ℝ) (t : ℝ) : ℝ :=
  (576*p3*t^4 + 1728*p3*t^3 + 1872*p3*t^2 + 864*p3*t + 144*p3 + 9*s2^2*t^3 - 108*s2^2*t - 27*s2*t^3*u - 21*s2*t^3 - 18*s2*t^2*u - 30*s2*t^2 + 324*s2*t*u + 96*s2*t + 216*s2*u + 72*s2 + 450*t^3*u^2 + 24*t^3*u - 58*t^3 + 1323*t^2*u^2 + 60*t^2*u - 167*t^2 + 1197*t*u^2 + 48*t*u - 149*t + 324*u^2 + 12*u - 40) /
    (144*(t + 1)^2*(2*t + 1)^2)

noncomputable def h3b (p3 s2 u : ℝ) (t : ℝ) : ℝ :=
  (144*p3*s2*t^5 + 432*p3*s2*t^4 + 468*p3*s2*t^3 + 216*p3*s2*t^2 + 36*p3*s2*t - 144*p3*t^4*u + 48*p3*t^4 - 432*p3*t^3*u + 144*p3*t^3 - 468*p3*t^2*u + 156*p3*t^2 - 216*p3*t*u + 72*p3*t - 36*p3*u + 12*p3 - 36*s2^3*t^2 + 108*s2^2*t^2*u + 48*s2^2*t^2 + 108*s2^2*t*u + 36*s2^2*t + 108*s2*t^4*u^2 - 16*s2*t^4 + 324*s2*t^3*u^2 - 48*s2*t^3 + 279*s2*t^2*u^2 - 24*s2*t^2*u - 52*s2*t^2 - 54*s2*t*u^2 - 72*s2*t*u - 24*s2*t - 81*s2*u^2 - 36*s2*u - 4*s2 - 144*t^3*u^3 + 16*t^3*u - 432*t^2*u^3 + 48*t^2*u - 396*t*u^3 + 44*t*u - 108*u^3 + 12*u) /
    (36*(t + 1)^2*(2*t + 1)^2)


lemma cConst_eq (u p3 : ℝ) (hu : 0 ≤ u) :
    cConst (3 * u ^ 2 / 4 - 1 / 9) p3 = ((3 * u ^ 2 / 4 - 1 / 9) + p3) / 3 + u ^ 3 / 4 := by
  unfold cConst
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hs : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  have ha : 0 ≤ 3 * Real.sqrt 3 / 2 * u := by positivity
  have hw : 1 + 9 * (3 * u ^ 2 / 4 - 1 / 9) = (3 * Real.sqrt 3 / 2 * u) ^ 2 := by
    rw [mul_pow, div_pow, mul_pow, h3]; ring
  rw [hw, ← Real.rpow_natCast (3 * Real.sqrt 3 / 2 * u) 2, ← Real.rpow_mul ha]
  norm_num
  field_simp
  rw [h3]
  ring

noncomputable abbrev F3 (u s2 : ℝ) : ℝ → ℝ := Sf (1 / 3) (1 / 3 - u) s2

set_option maxHeartbeats 1600000 in
lemma id1 (u p2 p3 s2 x : ℝ) (hp2 : p2 = 3 * u ^ 2 / 4 - 1 / 9) (hx : 0 < x) :

        x ^ 3 * (((1 - F3 u s2 (x + 2)) * F3 u s2 (x + 1)
            + (-(1 / 3) + p2 / x ^ 2 + p3 / x ^ 3))
          + (1 - F3 u s2 (x + 2)) * (1 - F3 u s2 (x - 1 + 2)) / 4
          + (1 - F3 u s2 (x + 2)) * (1 - F3 u s2 (x - 1 + 2))
            / (16 * x ^ 2)) = h3a p3 s2 u (1 / x) := by
  have h0 : x ≠ 0 := hx.ne'
  have h1 : x + 1 ≠ 0 := by positivity
  have h2 : x + 2 ≠ 0 := by positivity
  have h3 : 1 + x ≠ 0 := by positivity
  have h4 : 2 + x ≠ 0 := by positivity
  rw [show x - 1 + 2 = x + 1 by ring, hp2]
  simp only [F3, Sf, h3a]
  field_simp
  ring

set_option maxHeartbeats 1600000 in
lemma id2 (u p2 p3 s2 x : ℝ) (hp2 : p2 = 3 * u ^ 2 / 4 - 1 / 9) (hx : 0 < x) :

        x ^ 4 * (((1 - F3 u s2 (x + 2)) * F3 u s2 (x + 1)
            + (-(1 / 3) + p2 / x ^ 2 + p3 / x ^ 3)) * F3 u s2 x
          + (1 / 27 - p2 / (3 * x ^ 2) - ((p2 + p3) / 3 + u ^ 3 / 4) / x ^ 3)) =
        h3b p3 s2 u (1 / x) := by
  have h0 : x ≠ 0 := hx.ne'
  have h1 : x + 1 ≠ 0 := by positivity
  have h2 : x + 2 ≠ 0 := by positivity
  have h3 : 1 + x ≠ 0 := by positivity
  have h4 : 2 + x ≠ 0 := by positivity
  rw [hp2]
  simp only [F3, Sf, h3b]
  field_simp
  ring

set_option maxHeartbeats 1600000 in
theorem case3 : HolonomicPositivity.Dev.Iface.Case3Stmt := by
  intro P Q p0 p1 p2 p3 hT hP1 _ hp0 hp1 hQ
  subst hp0
  subst hp1
  obtain ⟨K, hK0, hK⟩ := eqMod_bound (n := 4) (by norm_num) hT
  obtain ⟨M, hM0, hM⟩ := geMod_lower (n := 4) (by norm_num) hQ
  obtain ⟨ε, hε⟩ : ∃ ε : ℝ → ℝ, ∀ x, ε x = ev P x - (-(1 / 3) + 0 / x + p2 / x ^ 2 + p3 / x ^ 3) :=
    ⟨_, fun _ => rfl⟩
  have hPe : ∀ x, ev P x = -(1 / 3) + p2 / x ^ 2 + p3 / x ^ 3 + ε x := by
    intro x; rw [hε]; ring
  have hK' : ∀ᶠ x : ℝ in atTop, |ε x| ≤ K / x ^ 4 := hK.mono fun x hx => by rw [hε]; exact hx
  have hε3 : Tendsto (fun x : ℝ => x ^ 3 * ε x) atTop (𝓝 0) := tendsto_pow_mul_zero (by norm_num) hK'
  have hε2 : Tendsto (fun x : ℝ => x ^ 2 * ε x) atTop (𝓝 0) := tendsto_pow_mul_zero (by norm_num) hK'
  -- p2 ≥ -1/9
  have hp2ge : -(1 / 9) ≤ p2 := by
    have hlim : Tendsto (fun x : ℝ => x ^ 2 * (ev P x - (-(1 / 3) - 1 / (9 * x ^ 2)))) atTop
        (𝓝 (p2 + 1 / 9)) := by
      have h3 : Tendsto (fun x : ℝ => p3 / x) atTop (𝓝 0) := tendsto_const_nhds.div_atTop tendsto_id
      have := ((tendsto_const_nhds (x := p2 + 1 / 9)).add h3).add hε2
      rw [add_zero, add_zero] at this
      refine this.congr' ?_
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
      rw [hPe x]
      field_simp
      ring
    rcases hP1 with h | h
    · have : 0 ≤ p2 + 1 / 9 := by
        refine ge_of_tendsto hlim ?_
        filter_upwards [h] with x hx
        exact mul_nonneg (sq_nonneg x) (sub_nonneg.2 hx.le)
      linarith
    · obtain ⟨K', _, hK''⟩ := eqMod_bound (n := 3) (by norm_num) h
      have h0 := tendsto_pow_mul_zero (k := 2) (by norm_num) hK''
      have := tendsto_nhds_unique hlim h0
      linarith
  obtain ⟨u, hu0, hp2⟩ : ∃ u : ℝ, 0 ≤ u ∧ p2 = 3 * u ^ 2 / 4 - 1 / 9 := by
    refine ⟨Real.sqrt ((4 / 27) * (1 + 9 * p2)), Real.sqrt_nonneg _, ?_⟩
    rw [Real.sq_sqrt (by linarith)]
    ring
  have hc := cConst_eq u p3 hu0
  rw [← hp2] at hc
  have hα : 0 < 81 * u ^ 2 + 36 * u + 4 := by positivity
  set β : ℝ := (12 * p3 - 36 * p3 * u - 108 * u ^ 3 + 12 * u) / 36 with hβ
  set s2 : ℝ := (M + K + 1 - β) / (-(81 * u ^ 2 + 36 * u + 4) / 36) with hs2
  have hps : (-(81 * u ^ 2 + 36 * u + 4) / 36) * s2 = M + K + 1 - β := by
    rw [hs2]; field_simp
  obtain ⟨S, hS⟩ := exists_S (1 / 3) (1 / 3 - u) s2
  have hBt : ∀ d : ℝ, Tendsto (fun x : ℝ => 1 - F3 u s2 (x + d)) atTop
      (𝓝 (2 / 3)) := by
    intro d
    have h := (tendsto_const_nhds (x := (1 : ℝ))).sub (tendsto_Sf (1 / 3) (1 / 3 - u) s2 d)
    rwa [show (1 : ℝ) - 1 / 3 = 2 / 3 by norm_num] at h
  have hB1 : Tendsto (fun x : ℝ => 1 - F3 u s2 (x - 1 + 2)) atTop (𝓝 (2 / 3)) := by
    simpa only [show ∀ x : ℝ, x - 1 + 2 = x + 1 from fun x => by ring] using hBt 1
  have hS0 : Tendsto (F3 u s2) atTop (𝓝 (1 / 3)) := by
    simpa only [add_zero] using tendsto_Sf (1 / 3) (1 / 3 - u) s2 0
  refine goal_of P Q S (F3 u s2) hS ?_ ?_ ?_ ?_
  · exact (hS0.eventually_const_lt (by norm_num : (0 : ℝ) < 1 / 3)).mono fun x hx => hx.le
  · exact (hBt 2).eventually_const_lt (by norm_num)
  · right
    have hid1 : ∀ᶠ x : ℝ in atTop,
        x ^ 3 * (((1 - F3 u s2 (x + 2)) * F3 u s2 (x + 1)
            + (-(1 / 3) + p2 / x ^ 2 + p3 / x ^ 3))
          + (1 - F3 u s2 (x + 2)) * (1 - F3 u s2 (x - 1 + 2)) / 4
          + (1 - F3 u s2 (x + 2)) * (1 - F3 u s2 (x - 1 + 2))
            / (16 * x ^ 2)) = h3a p3 s2 u (1 / x) := by
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
      exact id1 u p2 p3 s2 x hp2 hx
    have hc1 : ContinuousAt (h3a p3 s2 u) 0 := by
      unfold h3a; fun_prop (disch := norm_num)
    have hN := (tendsto_h hc1 hid1).add hε3
    have hDen := (hBt 2).mul hB1
    have hQuot := hN.div hDen (by norm_num)
    rw [show (-3 : ℤ) = -((3 : ℕ) : ℤ) by norm_num]
    refine eqMod_of_tendsto (hQuot.congr' ?_)
    filter_upwards [eventually_gt_atTop (0 : ℝ), (hBt 2).eventually_const_lt (by norm_num : (0 : ℝ) < 2 / 3),
      hB1.eventually_const_lt (by norm_num : (0 : ℝ) < 2 / 3)] with x hx hB hB1'
    have h0 : x ≠ 0 := hx.ne'
    have hne : (1 - F3 u s2 (x + 2)) * (1 - F3 u s2 (x - 1 + 2)) ≠ 0 :=
      (mul_pos hB hB1').ne'
    simp only [Pi.div_apply]
    rw [hPe x]
    have hb : 1 - F3 u s2 (x + 2) ≠ 0 := hB.ne'
    have hb1 : 1 - F3 u s2 (x - 1 + 2) ≠ 0 := hB1'.ne'
    generalize 1 - F3 u s2 (x + 2) = b at hb ⊢
    generalize 1 - F3 u s2 (x - 1 + 2) = b1 at hb1 ⊢
    generalize F3 u s2 (x + 1) = sv
    field_simp
    ring
  · have hid2 : ∀ᶠ x : ℝ in atTop,
        x ^ 4 * (((1 - F3 u s2 (x + 2)) * F3 u s2 (x + 1)
            + (-(1 / 3) + p2 / x ^ 2 + p3 / x ^ 3)) * F3 u s2 x
          + (1 / 27 - p2 / (3 * x ^ 2) - ((p2 + p3) / 3 + u ^ 3 / 4) / x ^ 3)) =
        h3b p3 s2 u (1 / x) := by
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
      exact id2 u p2 p3 s2 x hp2 hx
    have hc2 : ContinuousAt (h3b p3 s2 u) 0 := by
      unfold h3b; fun_prop (disch := norm_num)
    have hF2 := tendsto_h hc2 hid2
    have hl2 : h3b p3 s2 u 0 = M + K + 1 := by
      rw [hβ] at hps
      unfold h3b
      linear_combination hps
    rw [hl2] at hF2
    filter_upwards [hF2.eventually_const_lt (by linarith : M + K < M + K + 1), hM,
      eventually_gt_atTop (0 : ℝ), hK', hS0.eventually_const_lt (by norm_num : (0 : ℝ) < 1 / 3),
      hS0.eventually_lt_const (by norm_num : (1 / 3 : ℝ) < 1)] with x h1 hMx hx hε' hSp hSl
    unfold thresholdThree at hMx
    rw [hc] at hMx
    have hx4 : 0 < x ^ 4 := by positivity
    have hD : |x ^ 4 * ε x| ≤ K := by
      rw [abs_mul, abs_of_pos hx4]
      calc x ^ 4 * |ε x| ≤ x ^ 4 * (K / x ^ 4) := by gcongr
        _ = K := by field_simp
    have hD1 := (abs_le.mp hD).1
    have key : x ^ 4 * (((1 - F3 u s2 (x + 2)) * F3 u s2 (x + 1)
          + ev P x) * F3 u s2 x
        + (1 / 27 - p2 / (3 * x ^ 2) - ((p2 + p3) / 3 + u ^ 3 / 4) / x ^ 3)) =
        x ^ 4 * (((1 - F3 u s2 (x + 2)) * F3 u s2 (x + 1)
            + (-(1 / 3) + p2 / x ^ 2 + p3 / x ^ 3)) * F3 u s2 x
          + (1 / 27 - p2 / (3 * x ^ 2) - ((p2 + p3) / 3 + u ^ 3 / 4) / x ^ 3))
        + (x ^ 4 * ε x) * F3 u s2 x := by
      rw [hPe x]; ring
    have h2 : M / x ^ 4 < ((1 - F3 u s2 (x + 2)) * F3 u s2 (x + 1)
          + ev P x) * F3 u s2 x
        + (1 / 27 - p2 / (3 * x ^ 2) - ((p2 + p3) / 3 + u ^ 3 / 4) / x ^ 3) := by
      rw [div_lt_iff₀ hx4]
      have hDS : -K ≤ (x ^ 4 * ε x) * F3 u s2 x := by
        nlinarith [mul_nonneg (by linarith : 0 ≤ x ^ 4 * ε x + K) hSp.le,
          mul_nonneg hK0 (by linarith : 0 ≤ 1 - F3 u s2 x)]
      rw [mul_comm, key]
      linarith
    linarith

end HolonomicPositivity.Dev.Case3
end

section
set_option autoImplicit false

namespace HolonomicPositivity.Robust

theorem chk_lemma_5_4_scaling_case_II_3 (P Q : RatFunc ℝ) (p₀ p₁ p₂ p₃ : ℝ)
    (hT : HasTaylorExpansion P p₀ p₁ p₂ p₃)
    (hge : GeMod (ev P) (fun x => -(1 / 3) - 1 / (9 * x ^ 2)) (-3))
    (hlt : LtMod (ev P) (fun x => 1 - 2 / x) (-2))
    (hp1 : p₀ = -(1 / 3))
    (hp2 : p₁ = 0)
    (hq : GeMod (ev Q) (thresholdThree p₂ p₃) (-4)) :
    ∃ S : RatFunc ℝ, EventuallyGE (ev S) (fun _ => 0) ∧ EventuallyGT (scaledB S) (fun _ => 0) ∧
      SatisfiesInequalitySix (scaledA P S) (scaledB S) ∧ EventuallyGE (scaledC P Q S) (fun _ => 0) :=
  HolonomicPositivity.Dev.Case3.case3 P Q p₀ p₁ p₂ p₃ hT hge hlt hp1 hp2 hq

end HolonomicPositivity.Robust
end

theorem solution : type_of% @HolonomicPositivity.Robust.chk_lemma_5_4_scaling_case_II_3 := @HolonomicPositivity.Robust.chk_lemma_5_4_scaling_case_II_3
