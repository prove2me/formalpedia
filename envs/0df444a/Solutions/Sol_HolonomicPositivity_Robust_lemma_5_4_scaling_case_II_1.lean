-- Prove2me | solution 1 for HolonomicPositivity.Robust.lemma_5_4_scaling_case_II_1
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T15:42:58.672376+00:00
-- url     : https://prove2.me/submissions/d0a149ec-9502-41c3-af48-0006cc42d3cf

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

def Case1Stmt : Prop :=
  ∀ (P Q : RatFunc ℝ) (p₀ p₁ p₂ p₃ : ℝ), HasTaylorExpansion P p₀ p₁ p₂ p₃ →
    GeMod (ev P) (fun x => -(1 / 3) - 1 / (9 * x ^ 2)) (-3) →
    LtMod (ev P) (fun x => 1 - 2 / x) (-2) →
    -(1 / 3) < p₀ → GeMod (ev Q) (thresholdOne p₀ p₁ p₂) (-3) → Goal P Q

end HolonomicPositivity.Dev.Iface
end

section
set_option autoImplicit false
open Filter Topology Asymptotics

namespace HolonomicPositivity.Dev.Case1Alg

/-- the scaling `S(y) = a + s1/y + s2/y^2` as a real function -/
noncomputable def fS (a s1 s2 : ℝ) (y : ℝ) : ℝ := a + s1 * y⁻¹ + s2 * (y⁻¹ * y⁻¹)

/-- numerator polynomial (in `t = 1/x`) of `x^3 (G + R)` -/
noncomputable def Npoly (r s1 s2 p2 p3 t : ℝ) : ℝ := 4*p2*s1*t^4 + 12*p2*s1*t^3 + 13*p2*s1*t^2 + 6*p2*s1*t + p2*s1 + 4*p2*s2*t^5 + 12*p2*s2*t^4 + 13*p2*s2*t^3 + 6*p2*s2*t^2 + p2*s2*t + 4*p3*r*t^4/3 + 4*p3*r*t^3 + 13*p3*r*t^2/3 + 2*p3*r*t + p3*r/3 + 4*p3*s1*t^5 + 12*p3*s1*t^4 + 13*p3*s1*t^3 + 6*p3*s1*t^2 + p3*s1*t + 4*p3*s2*t^6 + 12*p3*s2*t^5 + 13*p3*s2*t^4 + 6*p3*s2*t^3 + p3*s2*t^2 + 4*p3*t^4/3 + 4*p3*t^3 + 13*p3*t^2/3 + 2*p3*t + p3/3 - 4*r^2*s1*t^3/3 - 28*r^2*s1*t^2/9 - 7*r^2*s1*t/3 - 5*r^2*s1/9 - 4*r^2*s2*t^4/3 - 28*r^2*s2*t^3/9 - 5*r^2*s2*t^2/3 + r^2*s2*t/3 + r^2*s2/3 + 4*r*s1^2*t^3 + 10*r*s1^2*t^2 + 8*r*s1^2*t + 2*r*s1^2 + 8*r*s1*s2*t^4 + 22*r*s1*s2*t^3 + 20*r*s1*s2*t^2 + 6*r*s1*s2*t - 4*r*s1*t^3/3 - 32*r*s1*t^2/9 - 3*r*s1*t - 7*r*s1/9 - 5*r*s2^2*t^3/3 - 2*r*s2^2*t^2 - r*s2^2*t - 4*r*s2*t^4/3 - 32*r*s2*t^3/9 - 3*r*s2*t^2 - r*s2*t/3 + r*s2/3 - 2*s1^3*t^2 - 3*s1^3*t - s1^3 - 2*s1^2*s2*t^3 - 6*s1^2*s2*t^2 - 3*s1^2*s2*t + 2*s1^2*t^2 + 3*s1^2*t + s1^2 - 3*s1*s2^2*t^3 - 3*s1*s2^2*t^2 + 2*s1*s2*t^3 + 6*s1*s2*t^2 + 3*s1*s2*t - 4*s1*t^2/9 - 2*s1*t/3 - 2*s1/9 - s2^3*t^3 + 7*s2^2*t^3/3 + 2*s2^2*t^2 - 4*s2*t^3/9 - 4*s2*t^2/3 - 2*s2*t/3

/-- `R_P` in terms of `r = √(1+3p0)` and `s1`. -/
noncomputable def Rexpl (r s1 p2 x : ℝ) : ℝ :=
  ((1 + r) / 3) ^ 3 - ((1 + r) / 3) ^ 2 - ((r ^ 2 - 1) / 3) * ((1 + r) / 3)
    - (2 * r * s1 - (1 + r) / 3 - (r ^ 2 - 1) / 3) * ((1 + r) / 3) / x
    - (p2 * ((1 + r) / 3) + r * s1 ^ 2) / x ^ 2

/-- explicit part of `C - Q` -/
noncomputable def Gf (r s1 s2 p2 p3 x : ℝ) : ℝ :=
  ((1 - fS ((1 + r) / 3) s1 s2 (x + 2)) * fS ((1 + r) / 3) s1 s2 (x + 1) +
    ((r ^ 2 - 1) / 3 + (2 * r * s1 - (1 + r) / 3 - (r ^ 2 - 1) / 3) / x + p2 / x ^ 2 + p3 / x ^ 3))
    * fS ((1 + r) / 3) s1 s2 x

lemma core_id (r s1 s2 p2 p3 x : ℝ) (hx : 0 < x) :
    x ^ 3 * (Gf r s1 s2 p2 p3 x + Rexpl r s1 p2 x) =
      Npoly r s1 s2 p2 p3 x⁻¹ / ((1 + x⁻¹) ^ 2 * (1 + 2 * x⁻¹) ^ 2) := by
  have h1 : x + 1 ≠ 0 := by positivity
  have h2 : x + 2 ≠ 0 := by positivity
  have hx0 : x ≠ 0 := hx.ne'
  have h3 : (1 + x⁻¹) ≠ 0 := by positivity
  have h4 : (1 + 2 * x⁻¹) ≠ 0 := by positivity
  unfold Gf Rexpl fS Npoly
  field_simp
  ring

lemma tendsto_core (r s1 s2 p2 p3 : ℝ) :
    Tendsto (fun x => x ^ 3 * (Gf r s1 s2 p2 p3 x + Rexpl r s1 p2 x)) atTop
      (𝓝 (Npoly r s1 s2 p2 p3 0)) := by
  have hc : Continuous (fun t => Npoly r s1 s2 p2 p3 t) := by unfold Npoly; fun_prop
  have hca : ContinuousAt (fun t => Npoly r s1 s2 p2 p3 t / ((1 + t) ^ 2 * (1 + 2 * t) ^ 2)) 0 :=
    hc.continuousAt.div (by fun_prop) (by norm_num)
  have ht := hca.tendsto.comp (tendsto_inv_atTop_zero (𝕜 := ℝ))
  have h0 : Npoly r s1 s2 p2 p3 0 / ((1 + 0) ^ 2 * (1 + 2 * 0) ^ 2) = Npoly r s1 s2 p2 p3 0 := by
    norm_num
  rw [h0] at ht
  refine ht.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  exact (core_id r s1 s2 p2 p3 x hx).symm

lemma Npoly_zero (r s1 s2 p2 p3 : ℝ) :
    Npoly r s1 s2 p2 p3 0 = Npoly r s1 0 p2 p3 0 + ((1 + r) / 3 * r) * s2 := by
  unfold Npoly; ring

/-- `x^k E(x) → 0` for `E = O(x⁻⁴)`, `k < 4`. -/
lemma E_small (E : ℝ → ℝ) (hE : E =O[atTop] fun x : ℝ => x ^ (-4 : ℤ)) (k : ℕ) (hk : k < 4) :
    Tendsto (fun x => x ^ k * E x) atTop (𝓝 0) := by
  have h1 := (isBigO_refl (fun x : ℝ => x ^ k) atTop).mul hE
  have h2 : Tendsto (fun x : ℝ => x ^ (k : ℤ) * x ^ (-4 : ℤ)) atTop (𝓝 0) := by
    refine (tendsto_zpow_atTop_zero (show (k : ℤ) + (-4) < 0 by omega)).congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    rw [zpow_add₀ hx.ne']
  refine IsBigO.trans_tendsto ?_ h2
  refine h1.congr' (Eventually.of_forall fun x => rfl) (Eventually.of_forall fun x => ?_)
  show x ^ k * x ^ (-4 : ℤ) = x ^ (k : ℤ) * x ^ (-4 : ℤ)
  rw [zpow_natCast]

lemma tendsto_fS (a s1 s2 : ℝ) (g : ℝ → ℝ) (hg : Tendsto g atTop atTop) :
    Tendsto (fun x => fS a s1 s2 (g x)) atTop (𝓝 a) := by
  have hi := (tendsto_inv_atTop_zero (𝕜 := ℝ)).comp hg
  have := (tendsto_const_nhds (x := a)).add (hi.const_mul s1) |>.add ((hi.mul hi).const_mul s2)
  simpa [fS] using this

/-- the analytic core of case II-1: a good `s2` exists. -/
lemma condC (r s1 p2 p3 : ℝ) (hr : 0 < r) (Pf Qf : ℝ → ℝ)
    (hP : (fun x => Pf x - ((r ^ 2 - 1) / 3 + (2 * r * s1 - (1 + r) / 3 - (r ^ 2 - 1) / 3) / x
        + p2 / x ^ 2 + p3 / x ^ 3)) =O[atTop] fun x : ℝ => x ^ (-4 : ℤ))
    (M : ℝ) (hQ : ∀ᶠ x in atTop, Rexpl r s1 p2 x - M / x ^ 3 ≤ Qf x) :
    ∃ s2 : ℝ, ∀ᶠ x in atTop,
      0 ≤ ((1 - fS ((1 + r) / 3) s1 s2 (x + 2)) * fS ((1 + r) / 3) s1 s2 (x + 1) + Pf x) *
        fS ((1 + r) / 3) s1 s2 x + Qf x := by
  have hk : 0 < (1 + r) / 3 * r := by positivity
  set k := (1 + r) / 3 * r with hkdef
  refine ⟨(M + 2 - Npoly r s1 0 p2 p3 0) / k, ?_⟩
  set s2 := (M + 2 - Npoly r s1 0 p2 p3 0) / k with hs2
  have hN : Npoly r s1 s2 p2 p3 0 = M + 2 := by
    rw [Npoly_zero, hs2]; field_simp; ring
  have hG := (tendsto_core r s1 s2 p2 p3)
  rw [hN] at hG
  have hu := hG.eventually (Ioi_mem_nhds (show M + 1 < M + 2 by linarith))
  have hE := E_small _ hP 3 (by norm_num)
  have hS := tendsto_fS ((1 + r) / 3) s1 s2 (fun x => x) tendsto_id
  have hw := (hE.mul hS).eventually (Ioi_mem_nhds (show (-1 : ℝ) < 0 * ((1 + r) / 3) by
    simp))
  filter_upwards [hu, hw, hQ, eventually_gt_atTop (0 : ℝ)] with x hu hw hQ hx
  have hx3 : 0 < x ^ 3 := by positivity
  have hv : -M ≤ x ^ 3 * (Qf x - Rexpl r s1 p2 x) := by
    have : -M / x ^ 3 ≤ Qf x - Rexpl r s1 p2 x := by
      have := hQ; rw [neg_div]; linarith [div_neg_eq_neg_div M (x^3)]
    rw [div_le_iff₀ hx3] at this
    nlinarith
  have key : x ^ 3 * (((1 - fS ((1 + r) / 3) s1 s2 (x + 2)) * fS ((1 + r) / 3) s1 s2 (x + 1) + Pf x) *
        fS ((1 + r) / 3) s1 s2 x + Qf x) =
      x ^ 3 * (Gf r s1 s2 p2 p3 x + Rexpl r s1 p2 x) + x ^ 3 * (Qf x - Rexpl r s1 p2 x) +
        (x ^ 3 * (Pf x - ((r ^ 2 - 1) / 3 + (2 * r * s1 - (1 + r) / 3 - (r ^ 2 - 1) / 3) / x
        + p2 / x ^ 2 + p3 / x ^ 3))) * fS ((1 + r) / 3) s1 s2 x := by
    unfold Gf; ring
  have : 0 < x ^ 3 * (((1 - fS ((1 + r) / 3) s1 s2 (x + 2)) * fS ((1 + r) / 3) s1 s2 (x + 1) + Pf x) *
        fS ((1 + r) / 3) s1 s2 x + Qf x) := by
    rw [key]; linarith
  exact (pos_of_mul_pos_right this hx3.le).le

end HolonomicPositivity.Dev.Case1Alg
end

section
set_option autoImplicit false
open Filter Topology Asymptotics

namespace HolonomicPositivity.Dev.Case1
open HolonomicPositivity.Robust HolonomicPositivity.Dev.RatExp HolonomicPositivity.Dev.Case1Alg

noncomputable def Sfun (a s1 s2 : ℝ) : RatFunc ℝ :=
  RatFunc.C a + RatFunc.C s1 * RatFunc.X⁻¹ + RatFunc.C s2 * (RatFunc.X⁻¹ * RatFunc.X⁻¹)

lemma rep_S (a s1 s2 : ℝ) : Rep (fS a s1 s2) (Sfun a s1 s2) := by
  unfold fS Sfun
  exact ((Rep.const a).add ((Rep.const s1).mul Rep.X.inv)).add
    ((Rep.const s2).mul (Rep.X.inv.mul Rep.X.inv))

lemma ev_S_comp (a s1 s2 : ℝ) (g : ℝ → ℝ) (hg : Tendsto g atTop atTop) :
    ∀ᶠ x in atTop, ev (Sfun a s1 s2) (g x) = fS a s1 s2 (g x) :=
  (hg.eventually (rep_S a s1 s2)).mono fun x h => h.symm

lemma hgc (c : ℝ) : Tendsto (fun x : ℝ => x + c) atTop atTop :=
  tendsto_atTop_add_const_right _ c tendsto_id

/-! ### Facts from the Taylor expansion -/

lemma tay_lim (Pf : ℝ → ℝ) (p0 p1 p2 p3 : ℝ)
    (hT : (fun x => Pf x - (p0 + p1 / x + p2 / x ^ 2 + p3 / x ^ 3)) =O[atTop] fun x : ℝ => x ^ (-4 : ℤ)) :
    Tendsto Pf atTop (𝓝 p0) := by
  have hE := E_small _ hT 0 (by norm_num)
  have hi := tendsto_inv_atTop_zero (𝕜 := ℝ)
  have h := ((((tendsto_const_nhds (x := p0)).add (hi.const_mul p1)).add
    ((hi.pow 2).const_mul p2)).add ((hi.pow 3).const_mul p3)).add hE
  rw [show p0 + p1 * 0 + p2 * 0 ^ 2 + p3 * 0 ^ 3 + 0 = p0 by norm_num] at h
  refine h.congr' ?_
  filter_upwards [eventually_ne_atTop (0 : ℝ)] with x hx
  simp only [pow_zero, one_mul, div_eq_mul_inv, inv_pow]
  ring

lemma tay_lim1 (Pf : ℝ → ℝ) (p1 p2 p3 : ℝ)
    (hT : (fun x => Pf x - (1 + p1 / x + p2 / x ^ 2 + p3 / x ^ 3)) =O[atTop] fun x : ℝ => x ^ (-4 : ℤ)) :
    Tendsto (fun x => x * (Pf x - 1)) atTop (𝓝 p1) := by
  have hE := E_small _ hT 1 (by norm_num)
  have hi := tendsto_inv_atTop_zero (𝕜 := ℝ)
  have h := (((tendsto_const_nhds (x := p1)).add (hi.const_mul p2)).add
    ((hi.pow 2).const_mul p3)).add hE
  rw [show p1 + p2 * 0 + p3 * 0 ^ 2 + 0 = p1 by norm_num] at h
  refine h.congr' ?_
  filter_upwards [eventually_ne_atTop (0 : ℝ)] with x hx
  field_simp
  ring

lemma tay_lim2 (Pf : ℝ → ℝ) (p2 p3 : ℝ)
    (hT : (fun x => Pf x - (1 + -2 / x + p2 / x ^ 2 + p3 / x ^ 3)) =O[atTop] fun x : ℝ => x ^ (-4 : ℤ)) :
    Tendsto (fun x => x ^ 2 * (Pf x - (1 - 2 / x))) atTop (𝓝 p2) := by
  have hE := E_small _ hT 2 (by norm_num)
  have hi := tendsto_inv_atTop_zero (𝕜 := ℝ)
  have h := ((tendsto_const_nhds (x := p2)).add (hi.const_mul p3)).add hE
  rw [show p2 + p3 * 0 + 0 = p2 by norm_num] at h
  refine h.congr' ?_
  filter_upwards [eventually_ne_atTop (0 : ℝ)] with x hx
  field_simp
  ring

lemma P_facts (Pf : ℝ → ℝ) (p0 p1 p2 p3 : ℝ)
    (hT : (fun x => Pf x - (p0 + p1 / x + p2 / x ^ 2 + p3 / x ^ 3)) =O[atTop] fun x : ℝ => x ^ (-4 : ℤ))
    (hle : ∀ᶠ x in atTop, Pf x ≤ 1 - 2 / x)
    (hne : ¬ (fun x => Pf x - (1 - 2 / x)) =O[atTop] fun x : ℝ => x ^ (-2 : ℤ)) :
    p0 ≤ 1 ∧ (p0 = 1 → p1 < -2) := by
  have hlim := tay_lim Pf p0 p1 p2 p3 hT
  have h1 : Tendsto (fun x : ℝ => 1 - 2 / x) atTop (𝓝 1) := by
    have := (tendsto_const_nhds (x := (1 : ℝ))).sub
      ((tendsto_const_nhds (x := (2 : ℝ))).div_atTop (tendsto_id (α := ℝ) (x := atTop)))
    simpa using this
  refine ⟨le_of_tendsto_of_tendsto hlim h1 hle, ?_⟩
  rintro rfl
  have hl1 := tay_lim1 Pf p1 p2 p3 hT
  have hp : p1 ≤ -2 := by
    refine le_of_tendsto hl1 ?_
    filter_upwards [hle, eventually_gt_atTop (0 : ℝ)] with x hx hx0
    have : x * (Pf x - 1) ≤ x * (-2 / x) := mul_le_mul_of_nonneg_left (by
      have : -2 / x = -(2 / x) := by ring
      linarith) hx0.le
    rwa [mul_div_cancel₀ _ hx0.ne'] at this
  refine lt_of_le_of_ne hp ?_
  rintro rfl
  apply hne
  have hl2 := tay_lim2 Pf p2 p3 hT
  have hb := hl2.isBigO_one ℝ
  have := hb.mul (isBigO_refl (fun x : ℝ => x ^ (-2 : ℤ)) atTop)
  refine (this.congr' ?_ ?_)
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    rw [zpow_neg]
    simp
    field_simp
  · filter_upwards with x
    simp

lemma Q_bound (Qf R : ℝ → ℝ) (h : GeMod Qf R (-3)) :
    ∃ M : ℝ, ∀ᶠ x in atTop, R x - M / x ^ 3 ≤ Qf x := by
  rcases h with h | h
  · exact ⟨0, by filter_upwards [h] with x hx; simp; linarith⟩
  · obtain ⟨c, hc⟩ := h.bound
    refine ⟨c, ?_⟩
    filter_upwards [hc, eventually_gt_atTop (0 : ℝ)] with x hx hx0
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (zpow_pos hx0 _)] at hx
    have h3 : x ^ (-3 : ℤ) = 1 / x ^ 3 := by
      rw [zpow_neg]; simp
    rw [h3] at hx
    have := neg_abs_le (Qf x - R x)
    have h4 : c * (1 / x ^ 3) = c / x ^ 3 := by ring
    rw [h4] at hx
    linarith

lemma thr_eq (r s1 p2 : ℝ) (hr : 0 < r) :
    thresholdOne ((r ^ 2 - 1) / 3) (2 * r * s1 - (1 + r) / 3 - (r ^ 2 - 1) / 3) p2 = Rexpl r s1 p2 := by
  funext x
  simp only [thresholdOne, aConst, bConst, Rexpl]
  rw [show 1 + 3 * ((r ^ 2 - 1) / 3) = r ^ 2 by ring, Real.sqrt_sq hr.le]
  have : (1 + r) / 3 + (r ^ 2 - 1) / 3 + (2 * r * s1 - (1 + r) / 3 - (r ^ 2 - 1) / 3) = 2 * r * s1 := by ring
  rw [this]
  field_simp
  ring

theorem case1 : HolonomicPositivity.Dev.Iface.Case1Stmt := by
  intro P Q p0 p1 p2 p3 hT _ hLt hp0 hQ
  obtain ⟨r, hr, rfl⟩ : ∃ r : ℝ, 0 < r ∧ p0 = (r ^ 2 - 1) / 3 :=
    ⟨Real.sqrt (1 + 3 * p0), Real.sqrt_pos.2 (by linarith),
      by rw [Real.sq_sqrt (by linarith)]; ring⟩
  obtain ⟨s1, rfl⟩ : ∃ s1 : ℝ, p1 = 2 * r * s1 - (1 + r) / 3 - (r ^ 2 - 1) / 3 :=
    ⟨(p1 + (1 + r) / 3 + (r ^ 2 - 1) / 3) / (2 * r), by field_simp; ring⟩
  rw [thr_eq r s1 p2 hr] at hQ
  obtain ⟨M, hM⟩ := Q_bound _ _ hQ
  obtain ⟨s2, hs2⟩ := condC r s1 p2 p3 hr (ev P) (ev Q) hT M hM
  obtain ⟨hr1, hr2⟩ := P_facts (ev P) _ _ p2 p3 hT hLt.1 hLt.2
  have hr2' : r ≤ 2 := by nlinarith
  have hPlim := tay_lim (ev P) _ _ p2 p3 hT
  -- notation
  set a : ℝ := (1 + r) / 3 with ha
  have ha0 : 0 < a := by positivity
  set S := Sfun a s1 s2 with hS
  have e0 : ∀ᶠ x in atTop, ev S x = fS a s1 s2 x := by
    simpa using ev_S_comp a s1 s2 (fun x => x) tendsto_id
  have e1 : ∀ᶠ x in atTop, ev S (x + 1) = fS a s1 s2 (x + 1) := ev_S_comp a s1 s2 _ (hgc 1)
  have e2 : ∀ᶠ x in atTop, ev S (x + 2) = fS a s1 s2 (x + 2) := ev_S_comp a s1 s2 _ (hgc 2)
  have hfa : Tendsto (fun x => fS a s1 s2 x) atTop (𝓝 a) :=
    tendsto_fS a s1 s2 (fun x => x) tendsto_id
  have hB : Tendsto (scaledB S) atTop (𝓝 (1 - a)) := by
    have := (tendsto_const_nhds (x := (1 : ℝ))).sub (tendsto_fS a s1 s2 _ (hgc 2))
    refine this.congr' ?_
    filter_upwards [e2] with x h
    show 1 - fS a s1 s2 (x + 2) = 1 - ev S (x + 2)
    rw [h]
  have hsub : Tendsto (fun x : ℝ => x - 1) atTop atTop :=
    tendsto_atTop_atTop.2 fun b => ⟨b + 1, fun x hx => by linarith⟩
  have hB1 : Tendsto (fun x => scaledB S (x - 1)) atTop (𝓝 (1 - a)) := hB.comp hsub
  have hS1 : Tendsto (fun x => ev S (x + 1)) atTop (𝓝 a) := by
    refine (tendsto_fS a s1 s2 _ (hgc 1)).congr' ?_
    filter_upwards [e1] with x h
    exact h.symm
  have hA : Tendsto (scaledA P S) atTop (𝓝 ((1 - a) * a + (r ^ 2 - 1) / 3)) := by
    have := (hB.mul hS1).add hPlim
    exact this
  -- B > 0
  have hBpos : ∀ᶠ x in atTop, 0 < scaledB S x := by
    rcases hr2'.lt_or_eq with hlt | heq
    · have : 0 < 1 - a := by rw [ha]; linarith
      exact hB.eventually (Ioi_mem_nhds this)
    · subst heq
      have hs1 : s1 < 0 := by
        have := hr2 (by norm_num)
        nlinarith
      have hinv : Tendsto (fun x : ℝ => (x + 2)⁻¹) atTop (𝓝 0) :=
        (tendsto_inv_atTop_zero (𝕜 := ℝ)).comp (hgc 2)
      have ht : Tendsto (fun x : ℝ => (x + 2) * scaledB S x) atTop (𝓝 (-s1 - s2 * 0)) := by
        have := (tendsto_const_nhds (x := -s1)).sub (hinv.const_mul s2)
        refine this.congr' ?_
        filter_upwards [e2, eventually_gt_atTop (0 : ℝ)] with x h hx
        have hx2 : x + 2 ≠ 0 := by positivity
        show -s1 - s2 * (x + 2)⁻¹ = (x + 2) * (1 - ev S (x + 2))
        rw [h]
        unfold fS
        field_simp
        ring
      have hpos := ht.eventually (Ioi_mem_nhds (show (0 : ℝ) < -s1 - s2 * 0 by linarith))
      filter_upwards [hpos, eventually_gt_atTop (0 : ℝ)] with x h hx
      have : 0 < x + 2 := by linarith
      exact pos_of_mul_pos_right h this.le
  refine ⟨S, ?_, hBpos, ?_, ?_⟩
  · -- S ≥ 0
    have := hfa.eventually (Ioi_mem_nhds ha0)
    filter_upwards [this, e0] with x h h0
    show 0 ≤ ev S x
    rw [h0]; exact le_of_lt h
  · -- inequality (6)
    left
    have hlow : ∀ x : ℝ, 0 < x → -(1 / 4) - 1 / (16 * x ^ 2) < -(1 / 4) := fun x hx => by
      have : 0 < 1 / (16 * x ^ 2) := by positivity
      linarith
    rcases hr2'.lt_or_eq with hlt | heq
    · have h1a : 0 < 1 - a := by rw [ha]; linarith
      have hq := hA.div (hB.mul hB1) (by positivity)
      have hL : -(1 / 4) < ((1 - a) * a + (r ^ 2 - 1) / 3) / ((1 - a) * (1 - a)) := by
        rw [lt_div_iff₀ (by positivity)]
        have : (1 - a) * a + (r ^ 2 - 1) / 3 + (1 - a) * (1 - a) / 4 = r ^ 2 / 4 := by
          rw [ha]; ring
        nlinarith [sq_pos_of_pos hr]
      filter_upwards [hq.eventually (Ioi_mem_nhds hL), eventually_gt_atTop (0 : ℝ)] with x h hx
      have := hlow x hx
      show -(1 / 4) - 1 / (16 * x ^ 2) < scaledA P S x / (scaledB S x * scaledB S (x - 1))
      exact lt_trans this h
    · subst heq
      have hApos := hA.eventually (Ioi_mem_nhds (show (0 : ℝ) < (1 - a) * a + (2 ^ 2 - 1) / 3 by
        rw [ha]; norm_num))
      have hBpos1 : ∀ᶠ x in atTop, 0 < scaledB S (x - 1) := hsub.eventually hBpos
      filter_upwards [hApos, hBpos, hBpos1, eventually_gt_atTop (0 : ℝ)] with x hA' hB' hB1' hx
      have := hlow x hx
      show -(1 / 4) - 1 / (16 * x ^ 2) < scaledA P S x / (scaledB S x * scaledB S (x - 1))
      have : 0 < scaledA P S x / (scaledB S x * scaledB S (x - 1)) := by positivity
      linarith [hlow x hx]
  · -- C ≥ 0
    filter_upwards [hs2, e0, e1, e2] with x h h0 h1 h2
    show 0 ≤ scaledC P Q S x
    unfold scaledC scaledA scaledB
    rw [h0, h1, h2]
    exact h

end HolonomicPositivity.Dev.Case1
end

section
set_option autoImplicit false

namespace HolonomicPositivity.Robust

theorem chk_lemma_5_4_scaling_case_II_1 (P Q : RatFunc ℝ) (p₀ p₁ p₂ p₃ : ℝ)
    (hT : HasTaylorExpansion P p₀ p₁ p₂ p₃)
    (hge : GeMod (ev P) (fun x => -(1 / 3) - 1 / (9 * x ^ 2)) (-3))
    (hlt : LtMod (ev P) (fun x => 1 - 2 / x) (-2))
    (hp1 : -(1 / 3) < p₀)
    (hq : GeMod (ev Q) (thresholdOne p₀ p₁ p₂) (-3)) :
    ∃ S : RatFunc ℝ, EventuallyGE (ev S) (fun _ => 0) ∧ EventuallyGT (scaledB S) (fun _ => 0) ∧
      SatisfiesInequalitySix (scaledA P S) (scaledB S) ∧ EventuallyGE (scaledC P Q S) (fun _ => 0) :=
  HolonomicPositivity.Dev.Case1.case1 P Q p₀ p₁ p₂ p₃ hT hge hlt hp1 hq

end HolonomicPositivity.Robust
end

theorem solution : type_of% @HolonomicPositivity.Robust.chk_lemma_5_4_scaling_case_II_1 := @HolonomicPositivity.Robust.chk_lemma_5_4_scaling_case_II_1
