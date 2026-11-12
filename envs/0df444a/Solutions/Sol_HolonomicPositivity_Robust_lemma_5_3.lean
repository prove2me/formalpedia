-- Prove2me | solution 1 for HolonomicPositivity.Robust.lemma_5_3
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T14:51:31.762749+00:00
-- url     : https://prove2.me/submissions/7bc7473c-f0dc-4727-a821-b3b09f113cf5

import Mathlib
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

lemma Rep.self (U : RatFunc ℝ) : Rep (ev U) U := Eventually.of_forall fun _ => rfl

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

lemma Rep.neg {f : ℝ → ℝ} {U : RatFunc ℝ} (hf : Rep f U) :
    Rep (fun x => - f x) (RatFunc.C (-1) * U) := by
  have := (Rep.const (-1)).mul hf
  refine this.mono fun x hx => ?_
  simpa using hx

lemma Rep.sub {f g : ℝ → ℝ} {U V : RatFunc ℝ} (hf : Rep f U) (hg : Rep g V) :
    Rep (fun x => f x - g x) (U + RatFunc.C (-1) * V) := by
  have := hf.add hg.neg
  refine this.mono fun x hx => ?_
  simpa [sub_eq_add_neg] using hx

lemma Rep.div {f g : ℝ → ℝ} {U V : RatFunc ℝ} (hf : Rep f U) (hg : Rep g V) :
    Rep (fun x => f x / g x) (U * V⁻¹) := by
  have := hf.mul hg.inv
  refine this.mono fun x hx => ?_
  simpa [div_eq_mul_inv] using hx

lemma Rep.congr {f g : ℝ → ℝ} {U : RatFunc ℝ} (hf : Rep f U) (h : ∀ᶠ x : ℝ in atTop, g x = f x) :
    Rep g U := by
  filter_upwards [hf, h] with x h1 h2
  rw [h2, h1]

/-- Shift of a rational function: `(shiftRF c U)(x) = U(x + c)`. -/
noncomputable def shiftRF (c : ℝ) (U : RatFunc ℝ) : RatFunc ℝ :=
  algebraMap (Polynomial ℝ) (RatFunc ℝ) (U.num.comp (Polynomial.X + Polynomial.C c)) /
    algebraMap (Polynomial ℝ) (RatFunc ℝ) (U.denom.comp (Polynomial.X + Polynomial.C c))

lemma ev_alg (p : Polynomial ℝ) (x : ℝ) :
    ev (algebraMap (Polynomial ℝ) (RatFunc ℝ) p) x = p.eval x := by
  simp [ev]

lemma ev_shiftRF (c : ℝ) (U : RatFunc ℝ) : ∀ᶠ x : ℝ in atTop,
    ev (shiftRF c U) x = ev U (x + c) := by
  have h1 := ev_mul (algebraMap (Polynomial ℝ) (RatFunc ℝ) (U.num.comp (Polynomial.X + Polynomial.C c)))
    (algebraMap (Polynomial ℝ) (RatFunc ℝ) (U.denom.comp (Polynomial.X + Polynomial.C c)))⁻¹
  have h2 := ev_inv (algebraMap (Polynomial ℝ) (RatFunc ℝ) (U.denom.comp (Polynomial.X + Polynomial.C c)))
  filter_upwards [h1, h2] with x e1 e2
  unfold shiftRF
  rw [div_eq_mul_inv, e1, e2, ev_alg, ev_alg, ev_eq U (x + c)]
  simp [div_eq_mul_inv]

lemma Rep.shift {f : ℝ → ℝ} {U : RatFunc ℝ} (hf : Rep f U) (c : ℝ) :
    Rep (fun x => f (x + c)) (shiftRF c U) := by
  have h : ∀ᶠ x : ℝ in atTop, f (x + c) = ev U (x + c) :=
    (tendsto_atTop_add_const_right atTop c tendsto_id).eventually hf
  filter_upwards [h, ev_shiftRF c U] with x h1 h2
  rw [h1, h2]


/-! ### Eventual sign of a rational function -/

lemma poly_sign (p : Polynomial ℝ) :
    (∀ᶠ x : ℝ in atTop, 0 < p.eval x) ∨ (∀ᶠ x : ℝ in atTop, p.eval x = 0) ∨
      (∀ᶠ x : ℝ in atTop, p.eval x < 0) := by
  by_cases hp : p = 0
  · right; left; simp [hp]
  · have hlc : p.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hp
    have h := (p.isEquivalent_atTop_lead).isLittleO.def (c := 1 / 2) (by norm_num)
    have hx := eventually_gt_atTop (0 : ℝ)
    rcases lt_or_gt_of_ne hlc with hneg | hpos
    · right; right
      filter_upwards [h, hx] with x h1 h2
      have hv : p.leadingCoeff * x ^ p.natDegree < 0 := mul_neg_of_neg_of_pos hneg (pow_pos h2 _)
      simp only [Pi.sub_apply, Real.norm_eq_abs, abs_of_neg hv] at h1
      have := (abs_le.mp h1).2
      linarith
    · left
      filter_upwards [h, hx] with x h1 h2
      have hv : 0 < p.leadingCoeff * x ^ p.natDegree := mul_pos hpos (pow_pos h2 _)
      simp only [Pi.sub_apply, Real.norm_eq_abs, abs_of_pos hv] at h1
      have := (abs_le.mp h1).1
      linarith

/-- A rational function is eventually positive, eventually zero, or eventually negative. -/
lemma ev_sign (W : RatFunc ℝ) :
    (∀ᶠ x : ℝ in atTop, 0 < ev W x) ∨ (∀ᶠ x : ℝ in atTop, ev W x = 0) ∨
      (∀ᶠ x : ℝ in atTop, ev W x < 0) := by
  have hd := eventually_denom_ne W
  rcases poly_sign W.num with hn | hn | hn <;> rcases poly_sign W.denom with hq | hq | hq
  · left; filter_upwards [hn, hq] with x a b; rw [ev_eq]; exact div_pos a b
  · exfalso; obtain ⟨x, h1, h2⟩ := (hd.and hq).exists; exact h1 h2
  · right; right; filter_upwards [hn, hq] with x a b; rw [ev_eq]; exact div_neg_of_pos_of_neg a b
  · right; left; filter_upwards [hn] with x a; rw [ev_eq, a]; simp
  · exfalso; obtain ⟨x, h1, h2⟩ := (hd.and hq).exists; exact h1 h2
  · right; left; filter_upwards [hn] with x a; rw [ev_eq, a]; simp
  · right; right; filter_upwards [hn, hq] with x a b; rw [ev_eq]; exact div_neg_of_neg_of_pos a b
  · exfalso; obtain ⟨x, h1, h2⟩ := (hd.and hq).exists; exact h1 h2
  · left; filter_upwards [hn, hq] with x a b; rw [ev_eq]; exact div_pos_of_neg_of_neg a b

/-! ### Taylor expansion at infinity -/

lemma exists_sub_lt (p q : Polynomial ℝ) (hq : q ≠ 0) (h : p.degree ≤ q.degree) :
    ∃ c : ℝ, (p - Polynomial.C c * q).degree < q.degree := by
  rcases lt_or_eq_of_le h with hlt | heq
  · exact ⟨0, by simpa using hlt⟩
  · have hp : p ≠ 0 := by
      intro hp0
      rw [hp0, Polynomial.degree_zero] at heq
      exact hq (Polynomial.degree_eq_bot.mp heq.symm)
    have hlq : q.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hq
    have hlp : p.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hp
    set c := p.leadingCoeff / q.leadingCoeff with hc
    have hc0 : c ≠ 0 := div_ne_zero hlp hlq
    have hdeg : (Polynomial.C c * q).degree = p.degree := by
      rw [Polynomial.degree_C_mul hc0, heq]
    have hlead : (Polynomial.C c * q).leadingCoeff = p.leadingCoeff := by
      rw [Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C, hc]
      field_simp
    refine ⟨c, ?_⟩
    have := Polynomial.degree_sub_lt_left (p := p) (q := Polynomial.C c * q) hdeg.symm hp hlead.symm
    rwa [heq] at this

lemma taylor_step (p q : Polynomial ℝ) (hq : q ≠ 0) (h : p.degree ≤ q.degree) :
    ∃ c : ℝ, ∃ p' : Polynomial ℝ, p'.degree ≤ q.degree ∧
      ∀ x : ℝ, x ≠ 0 → q.eval x ≠ 0 → p.eval x / q.eval x = c + (1 / x) * (p'.eval x / q.eval x) := by
  obtain ⟨c, hc⟩ := exists_sub_lt p q hq h
  refine ⟨c, Polynomial.X * (p - Polynomial.C c * q), ?_, ?_⟩
  · by_cases hr : p - Polynomial.C c * q = 0
    · rw [hr]; simp
    · rw [Polynomial.degree_mul, Polynomial.degree_X,
        Polynomial.degree_eq_natDegree hr, Polynomial.degree_eq_natDegree hq]
      rw [Polynomial.degree_eq_natDegree hr, Polynomial.degree_eq_natDegree hq] at hc
      have : (p - Polynomial.C c * q).natDegree < q.natDegree := by exact_mod_cast hc
      exact_mod_cast (show 1 + (p - Polynomial.C c * q).natDegree ≤ q.natDegree by omega)
  · intro x hx hqx
    simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
    field_simp
    ring


lemma taylor_poly (p q : Polynomial ℝ) (hq : q ≠ 0) (h : p.degree ≤ q.degree) :
    ∃ c0 c1 c2 c3 : ℝ, ∃ r : Polynomial ℝ, r.degree ≤ q.degree ∧
      ∀ x : ℝ, x ≠ 0 → q.eval x ≠ 0 → p.eval x / q.eval x =
        c0 + c1 / x + c2 / x ^ 2 + c3 / x ^ 3 + (1 / x ^ 4) * (r.eval x / q.eval x) := by
  obtain ⟨c0, p1, h1, e1⟩ := taylor_step p q hq h
  obtain ⟨c1, p2, h2, e2⟩ := taylor_step p1 q hq h1
  obtain ⟨c2, p3, h3, e3⟩ := taylor_step p2 q hq h2
  obtain ⟨c3, p4, h4, e4⟩ := taylor_step p3 q hq h3
  refine ⟨c0, c1, c2, c3, p4, h4, fun x hx hqx => ?_⟩
  rw [e1 x hx hqx, e2 x hx hqx, e3 x hx hqx, e4 x hx hqx]
  field_simp
  ring

/-- **Taylor expansion at infinity.** A rational function that is bounded at `+∞` has an
expansion `c₀ + c₁/x + c₂/x² + c₃/x³ + O(x⁻⁴)`. -/
theorem taylor_of_bounded (U : RatFunc ℝ) (hb : ∃ K : ℝ, ∀ᶠ x : ℝ in atTop, |ev U x| ≤ K) :
    ∃ c0 c1 c2 c3 : ℝ,
      EqMod (ev U) (fun x => c0 + c1 / x + c2 / x ^ 2 + c3 / x ^ 3) (-4) := by
  obtain ⟨K, hK⟩ := hb
  have hdeg : U.num.degree ≤ U.denom.degree := by
    by_contra hlt
    push Not at hlt
    have := (Polynomial.abs_div_tendsto_atTop_atTop_of_degree_gt U.num U.denom hlt
      U.denom_ne_zero).eventually_gt_atTop K
    obtain ⟨x, h1, h2⟩ := (hK.and this).exists
    rw [ev_eq] at h1
    linarith
  obtain ⟨c0, c1, c2, c3, r, hr, e⟩ := taylor_poly U.num U.denom U.denom_ne_zero hdeg
  refine ⟨c0, c1, c2, c3, ?_⟩
  have hO := (Polynomial.isBigO_atTop_of_degree_le r U.denom hr).bound
  obtain ⟨C, hC⟩ := hO
  unfold EqMod
  refine IsBigO.of_bound C ?_
  filter_upwards [hC, eventually_denom_ne U, eventually_gt_atTop (0 : ℝ)] with x h1 h2 h3
  have := e x h3.ne' h2
  rw [ev_eq, this]
  simp only [Real.norm_eq_abs] at h1 ⊢
  have h4 : |r.eval x / U.denom.eval x| ≤ C := by
    rw [abs_div, div_le_iff₀ (abs_pos.mpr h2)]; exact h1
  have : c0 + c1 / x + c2 / x ^ 2 + c3 / x ^ 3 + 1 / x ^ 4 * (Polynomial.eval x r / Polynomial.eval x U.denom)
      - (c0 + c1 / x + c2 / x ^ 2 + c3 / x ^ 3) = 1 / x ^ 4 * (Polynomial.eval x r / Polynomial.eval x U.denom) := by ring
  rw [this, abs_mul, zpow_neg, abs_inv]
  have h5 : |x ^ (4 : ℤ)| = x ^ 4 := by
    rw [abs_of_pos (zpow_pos h3 _)]; norm_cast
  rw [h5, abs_of_pos (by positivity : (0:ℝ) < 1 / x ^ 4)]
  have : (1 : ℝ) / x ^ 4 = (x ^ 4)⁻¹ := one_div _
  rw [this]
  exact mul_le_mul_of_nonneg_left h4 (by positivity) |>.trans (by rw [mul_comm])

end HolonomicPositivity.Dev.RatExp

namespace HolonomicPositivity.Dev.L53
open HolonomicPositivity.Robust HolonomicPositivity.Dev.RatExp

lemma shift_ev {P : ℝ → Prop} (h : ∀ᶠ x : ℝ in atTop, P (x + 1)) : ∀ᶠ x : ℝ in atTop, P x := by
  have := (tendsto_atTop_add_const_right atTop (-1 : ℝ) tendsto_id).eventually h
  filter_upwards [this] with x hx
  simpa using hx

lemma shift_fwd {P : ℝ → Prop} (c : ℝ) (h : ∀ᶠ x : ℝ in atTop, P x) :
    ∀ᶠ x : ℝ in atTop, P (x + c) :=
  (tendsto_atTop_add_const_right atTop c tendsto_id).eventually h

/-! ### Forward direction: real-variable estimate -/

lemma fwd_real (C : ℝ) (hC : 0 ≤ C) : ∃ s : ℝ, ∀ᶠ x : ℝ in atTop,
    0 < 1 / 2 + 1 / (4 * (x - s)) ∧ 1 / 2 + 1 / (4 * (x + 1 - s)) < 1 ∧
    0 < 1 / 2 + 1 / (4 * (x + 1 - s)) ∧
    1 / 4 + 1 / (16 * x ^ 2) + C / x ^ 3 ≤
      (1 / 2 + 1 / (4 * (x - s))) * (1 - (1 / 2 + 1 / (4 * (x + 1 - s)))) := by
  refine ⟨8 * C + 3 / 2, ?_⟩
  set s : ℝ := 8 * C + 3 / 2 with hs
  have hs0 : 0 < s := by rw [hs]; linarith
  set c1 : ℝ := s * (s - 1) - 16 * C * (16 * C + 2) with hc1
  set c2 : ℝ := 16 * C * (s * (s - 1)) with hc2
  filter_upwards [eventually_ge_atTop (s + 1 + |c1| + |c2| + 1)] with x hx
  have hx1 : 1 ≤ x := by
    have := abs_nonneg c1; have := abs_nonneg c2; linarith
  have hxs : 1 < x - s := by
    have := abs_nonneg c1; have := abs_nonneg c2; linarith
  have hu : 0 < x - s := by linarith
  have hu1 : 0 < x + 1 - s := by linarith
  have hx0 : 0 < x := by linarith
  have e1 : 0 < 1 / (4 * (x - s)) := by positivity
  have e2 : 0 < 1 / (4 * (x + 1 - s)) := by positivity
  have e3 : 1 / (4 * (x + 1 - s)) < 1 / 2 := by
    rw [div_lt_div_iff₀ (by positivity) (by norm_num)]
    linarith
  refine ⟨by linarith, by linarith, by linarith, ?_⟩
  have key : (1 / 2 + 1 / (4 * (x - s))) * (1 - (1 / 2 + 1 / (4 * (x + 1 - s)))) =
      1 / 4 + 1 / (16 * ((x - s) * (x + 1 - s))) := by
    field_simp
    ring
  rw [key]
  have key2 : 1 / (16 * x ^ 2) + C / x ^ 3 = (x + 16 * C) / (16 * x ^ 3) := by
    field_simp
  have : (x + 16 * C) / (16 * x ^ 3) ≤ 1 / (16 * ((x - s) * (x + 1 - s))) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have hp : (x + 16 * C) * (16 * ((x - s) * (x + 1 - s))) = 16 * (x ^ 3 - (2 * x ^ 2 - c1 * x - c2)) := by
      rw [hc1, hc2, hs]; ring
    have h2 : c1 * x ≤ |c1| * x := mul_le_mul_of_nonneg_right (le_abs_self _) hx0.le
    have h3 : c2 ≤ |c2| * x := by
      calc c2 ≤ |c2| := le_abs_self _
        _ ≤ |c2| * x := le_mul_of_one_le_right (abs_nonneg _) hx1
    have h4 : x * (|c1| + |c2| + 1) ≤ x * x := mul_le_mul_of_nonneg_left (by linarith [abs_nonneg c1, abs_nonneg c2]) hx0.le
    nlinarith
  linarith

/-! ### Backward direction: the Riccati bound -/

lemma riccati_real (M : ℝ → ℝ) (m0 m1 m2 K : ℝ) (hK : 0 ≤ K)
    (h : ∀ᶠ x : ℝ in atTop, |M x - (m0 + m1 / x + m2 / x ^ 2)| ≤ K / x ^ 3) :
    ∃ C : ℝ, ∀ᶠ x : ℝ in atTop, M x * (1 - M (x + 1)) ≤ 1 / 4 + 1 / (16 * x ^ 2) + C / x ^ 3 := by
  have h' : ∀ᶠ x : ℝ in atTop, |M (x + 1) - (m0 + m1 / (x + 1) + m2 / (x + 1) ^ 2)| ≤
      K / (x + 1) ^ 3 := shift_fwd 1 h
  by_cases hm : m0 = 1 / 2
  · subst hm
    refine ⟨(3 * |m2| + 2 * K) / 2 + 2 * (|m1| * (|m2| + K)) + (|m2| + K) ^ 2, ?_⟩
    filter_upwards [h, h', eventually_ge_atTop (1 : ℝ)] with x hx hx' hx1
    have hx0 : 0 < x := by linarith
    have hxx : 0 < x + 1 := by linarith
    obtain ⟨t, ht⟩ : ∃ t, t = M x - 1 / 2 - m1 / x := ⟨_, rfl⟩
    obtain ⟨t', ht'⟩ : ∃ t', t' = M (x + 1) - 1 / 2 - m1 / (x + 1) := ⟨_, rfl⟩
    obtain ⟨a, ha⟩ : ∃ a, a = m1 / x := ⟨_, rfl⟩
    obtain ⟨a', ha'⟩ : ∃ a', a' = m1 / (x + 1) := ⟨_, rfl⟩
    have hMx : M x = 1 / 2 + a + t := by rw [ha, ht]; ring
    have hMx' : M (x + 1) = 1 / 2 + a' + t' := by rw [ha', ht']; ring
    -- bounds
    have hKx : K / x ^ 3 ≤ K / x ^ 2 := by
      apply div_le_div_of_nonneg_left hK (by positivity)
      nlinarith [sq_nonneg x]
    have hKx' : K / (x + 1) ^ 3 ≤ K / x ^ 3 := by
      apply div_le_div_of_nonneg_left hK (by positivity)
      exact pow_le_pow_left₀ hx0.le (by linarith) 3
    have hm2x : |m2 / (x + 1) ^ 2| ≤ |m2| / x ^ 2 := by
      rw [abs_div, abs_of_pos (by positivity : (0:ℝ) < (x + 1) ^ 2)]
      apply div_le_div_of_nonneg_left (abs_nonneg _) (by positivity)
      exact pow_le_pow_left₀ hx0.le (by linarith) 2
    have ht1 : |t - m2 / x ^ 2| ≤ K / x ^ 3 := by
      rw [ht]; convert hx using 2; ring
    have ht1' : |t' - m2 / (x + 1) ^ 2| ≤ K / (x + 1) ^ 3 := by
      rw [ht']; convert hx' using 2; ring
    have hbt : |t| ≤ (|m2| + K) / x ^ 2 := by
      have := abs_sub_abs_le_abs_sub t (m2 / x ^ 2)
      rw [abs_div, abs_of_pos (by positivity : (0:ℝ) < x ^ 2)] at this
      rw [add_div]; linarith
    have hbt' : |t'| ≤ (|m2| + K) / x ^ 2 := by
      have := abs_sub_abs_le_abs_sub t' (m2 / (x + 1) ^ 2)
      rw [add_div]; linarith
    have hba : |a| ≤ |m1| / x := by rw [ha, abs_div, abs_of_pos hx0]
    have hba' : |a'| ≤ |m1| / x := by
      rw [ha', abs_div, abs_of_pos hxx]
      exact div_le_div_of_nonneg_left (abs_nonneg _) hx0 (by linarith)
    have hdt : |t - t'| ≤ (3 * |m2| + 2 * K) / x ^ 3 := by
      have e1 : t - t' = m2 * (1 / x ^ 2 - 1 / (x + 1) ^ 2) + ((t - m2 / x ^ 2) - (t' - m2 / (x + 1) ^ 2)) := by ring
      have e2 : 1 / x ^ 2 - 1 / (x + 1) ^ 2 = (2 * x + 1) / (x ^ 2 * (x + 1) ^ 2) := by
        field_simp; ring
      have e3 : (2 * x + 1) / (x ^ 2 * (x + 1) ^ 2) ≤ 3 / x ^ 3 := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [sq_nonneg x, mul_nonneg hx0.le (sq_nonneg x), mul_nonneg hx0.le hx0.le,
          mul_nonneg (mul_nonneg hx0.le hx0.le) (mul_nonneg hx0.le hx0.le)]
      have e4 : 0 ≤ (2 * x + 1) / (x ^ 2 * (x + 1) ^ 2) := by positivity
      have e5 : |m2 * (1 / x ^ 2 - 1 / (x + 1) ^ 2)| ≤ 3 * |m2| / x ^ 3 := by
        rw [abs_mul, e2, abs_of_nonneg e4]
        calc |m2| * ((2 * x + 1) / (x ^ 2 * (x + 1) ^ 2)) ≤ |m2| * (3 / x ^ 3) :=
              mul_le_mul_of_nonneg_left e3 (abs_nonneg _)
          _ = 3 * |m2| / x ^ 3 := by ring
      have e6 := abs_sub (t - m2 / x ^ 2) (t' - m2 / (x + 1) ^ 2)
      rw [e1]
      refine (abs_add_le _ _).trans ?_
      have : (3 * |m2| + 2 * K) / x ^ 3 = 3 * |m2| / x ^ 3 + 2 * (K / x ^ 3) := by ring
      rw [this]
      linarith
    have hKk : 0 ≤ |m2| + K := by positivity
    have hat : |a * t'| ≤ |m1| * (|m2| + K) / x ^ 3 := by
      rw [abs_mul]
      calc |a| * |t'| ≤ (|m1| / x) * ((|m2| + K) / x ^ 2) :=
            mul_le_mul hba hbt' (abs_nonneg _) (by positivity)
        _ = |m1| * (|m2| + K) / x ^ 3 := by field_simp
    have hta : |t * a'| ≤ |m1| * (|m2| + K) / x ^ 3 := by
      rw [abs_mul]
      calc |t| * |a'| ≤ ((|m2| + K) / x ^ 2) * (|m1| / x) :=
            mul_le_mul hbt hba' (abs_nonneg _) (by positivity)
        _ = |m1| * (|m2| + K) / x ^ 3 := by field_simp
    have htt : |t * t'| ≤ (|m2| + K) ^ 2 / x ^ 3 := by
      rw [abs_mul]
      calc |t| * |t'| ≤ ((|m2| + K) / x ^ 2) * ((|m2| + K) / x ^ 2) :=
            mul_le_mul hbt hbt' (abs_nonneg _) (by positivity)
        _ = (|m2| + K) ^ 2 / x ^ 4 := by field_simp
        _ ≤ (|m2| + K) ^ 2 / x ^ 3 := by
            apply div_le_div_of_nonneg_left (by positivity) (by positivity)
            nlinarith [pow_pos hx0 3]
    have hP0 : (a - a') / 2 - a * a' - 1 / (16 * x ^ 2) ≤ 0 := by
      have : (a - a') / 2 - a * a' - 1 / (16 * x ^ 2) =
          -((m1 - 1 / 4) ^ 2 / (x * (x + 1)) + 1 / (16 * x ^ 2 * (x + 1))) := by
        rw [ha, ha']; field_simp; ring
      rw [this]
      have : 0 ≤ (m1 - 1 / 4) ^ 2 / (x * (x + 1)) + 1 / (16 * x ^ 2 * (x + 1)) := by positivity
      linarith
    have hkey : M x * (1 - M (x + 1)) =
        1 / 4 + 1 / (16 * x ^ 2) + ((a - a') / 2 - a * a' - 1 / (16 * x ^ 2)) +
          (t - t') / 2 - (a * t' + t * a' + t * t') := by
      rw [hMx, hMx']; ring
    have f1 := abs_le.mp hdt
    have f2 := abs_le.mp hat
    have f3 := abs_le.mp hta
    have f4 := abs_le.mp htt
    have hC : ((3 * |m2| + 2 * K) / 2 + 2 * (|m1| * (|m2| + K)) + (|m2| + K) ^ 2) / x ^ 3 =
        (3 * |m2| + 2 * K) / x ^ 3 / 2 + 2 * (|m1| * (|m2| + K) / x ^ 3) + (|m2| + K) ^ 2 / x ^ 3 := by
      ring
    rw [hkey, hC]
    linarith
  · refine ⟨0, ?_⟩
    have h0 : Tendsto (fun x => M x - (m0 + m1 / x + m2 / x ^ 2)) atTop (𝓝 0) := by
      refine squeeze_zero_norm' (a := fun x : ℝ => K / x ^ 3) ?_ ((tendsto_const_nhds (x := K)).div_atTop (tendsto_pow_atTop (by norm_num : (3:ℕ) ≠ 0)))
      filter_upwards [h] with x hx
      simpa [Real.norm_eq_abs] using hx
    have h1 : Tendsto (fun x : ℝ => m0 + m1 / x + m2 / x ^ 2) atTop (𝓝 m0) := by
      have := (tendsto_const_nhds (x := m0)).add ((tendsto_const_nhds (x := m1)).div_atTop tendsto_id) |>.add
        ((tendsto_const_nhds (x := m2)).div_atTop (tendsto_pow_atTop (by norm_num : (2:ℕ) ≠ 0)))
      simpa using this
    have hT : Tendsto M atTop (𝓝 m0) := by
      have := h0.add h1
      simpa using this.congr (fun x => by simp)
    have hT' : Tendsto (fun x => M (x + 1)) atTop (𝓝 m0) :=
      hT.comp (tendsto_atTop_add_const_right atTop 1 tendsto_id)
    have hΦ : Tendsto (fun x => M x * (1 - M (x + 1))) atTop (𝓝 (m0 * (1 - m0))) :=
      hT.mul (tendsto_const_nhds.sub hT')
    have hlt : m0 * (1 - m0) < 1 / 4 := by
      have : 0 < (m0 - 1 / 2) ^ 2 := by
        have : m0 - 1 / 2 ≠ 0 := sub_ne_zero.mpr hm
        positivity
      nlinarith
    filter_upwards [hΦ.eventually_lt_const hlt] with x hx
    have : 0 ≤ 1 / (16 * x ^ 2) := by positivity
    simp only [zero_div, add_zero]
    linarith

lemma riccati_bound (V : RatFunc ℝ) (hb : ∃ K : ℝ, ∀ᶠ x : ℝ in atTop, |ev V x| ≤ K) :
    ∃ C : ℝ, ∀ᶠ x : ℝ in atTop,
      ev V x * (1 - ev V (x + 1)) ≤ 1 / 4 + 1 / (16 * x ^ 2) + C / x ^ 3 := by
  obtain ⟨c0, c1, c2, c3, hE⟩ := taylor_of_bounded V hb
  obtain ⟨K', hK'⟩ := hE.bound
  apply riccati_real (ev V) c0 c1 c2 (|K'| + |c3|) (by positivity)
  filter_upwards [hK', eventually_ge_atTop (1 : ℝ)] with x h1 hx
  have hx0 : 0 < x := by linarith
  have hn : ‖x ^ (-4 : ℤ)‖ = 1 / x ^ 4 := by
    rw [Real.norm_eq_abs, abs_of_pos (zpow_pos hx0 _)]
    simp [zpow_neg]
  rw [hn, Real.norm_eq_abs] at h1
  have e1 : |c3 / x ^ 3| = |c3| / x ^ 3 := by
    rw [abs_div, abs_of_pos (by positivity : (0:ℝ) < x ^ 3)]
  have e2 : K' * (1 / x ^ 4) ≤ |K'| / x ^ 3 := by
    calc K' * (1 / x ^ 4) ≤ |K'| * (1 / x ^ 4) :=
          mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
      _ ≤ |K'| * (1 / x ^ 3) := by
          apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
          apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
          nlinarith [pow_pos hx0 3]
      _ = |K'| / x ^ 3 := by ring
  have e3 := abs_sub (ev V x - (c0 + c1 / x + c2 / x ^ 2 + c3 / x ^ 3)) (c3 / x ^ 3)
  have e4 : ev V x - (c0 + c1 / x + c2 / x ^ 2) =
      (ev V x - (c0 + c1 / x + c2 / x ^ 2 + c3 / x ^ 3)) + c3 / x ^ 3 := by ring
  rw [e4]
  refine (abs_add_le _ _).trans ?_
  have : (|K'| + |c3|) / x ^ 3 = |K'| / x ^ 3 + |c3| / x ^ 3 := add_div _ _ _
  rw [this, e1]
  linarith


/-- Conclude `GeMod` from a one-sided `O(x⁻³)` bound, using that `R - T` is rational. -/
lemma geMod_of_rat (R T : ℝ → ℝ) (W : RatFunc ℝ) (hW : Rep (fun x => R x - T x) W) (C : ℝ)
    (hC : ∀ᶠ x : ℝ in atTop, -(C / x ^ 3) ≤ R x - T x) : GeMod R T (-3) := by
  rcases ev_sign W with hp | hz | hn
  · left
    filter_upwards [hp, hW] with x h1 h2
    show T x < R x
    have : R x - T x = ev W x := h2
    linarith
  · right
    refine IsBigO.of_bound 0 ?_
    filter_upwards [hz, hW] with x h1 h2
    have : R x - T x = 0 := by rw [h2, h1]
    simp [this]
  · right
    refine IsBigO.of_bound |C| ?_
    filter_upwards [hn, hW, hC, eventually_gt_atTop (0 : ℝ)] with x h1 h2 h3 hx
    have h4 : R x - T x < 0 := by rw [h2]; exact h1
    have hn : ‖x ^ (-3 : ℤ)‖ = 1 / x ^ 3 := by
      rw [Real.norm_eq_abs, abs_of_pos (zpow_pos hx _)]
      simp [zpow_neg]
    simp only [Real.norm_eq_abs] at hn ⊢
    rw [hn, abs_of_neg h4]
    have : C / x ^ 3 ≤ |C| * (1 / x ^ 3) := by
      rw [← mul_one_div]
      exact mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
    linarith

/-! ### The two directions -/

lemma forward (A B : RatFunc ℝ) (hB : ∀ᶠ x : ℝ in atTop, 0 < ev B x)
    (h6 : SatisfiesInequalitySix (ev A) (ev B)) : ∃ L : RatFunc ℝ, IsRiccatiWitness (ev A) (ev B) L := by
  -- Step 1: a one-sided bound for R
  obtain ⟨C, hC0, hC⟩ : ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ x : ℝ in atTop,
      -(1 / 4) - 1 / (16 * x ^ 2) - C / x ^ 3 ≤ ev A x / (ev B x * ev B (x - 1)) := by
    rcases h6 with h | h
    · refine ⟨0, le_refl _, ?_⟩
      filter_upwards [h] with x hx
      have : (fun x : ℝ => -(1 / 4) - 1 / (16 * x ^ 2)) x < ev A x / (ev B x * ev B (x - 1)) := hx
      simp only [zero_div, sub_zero]
      linarith
    · obtain ⟨K, hK⟩ := h.bound
      refine ⟨|K|, abs_nonneg _, ?_⟩
      filter_upwards [hK, eventually_gt_atTop (0 : ℝ)] with x h1 hx
      have hn : ‖x ^ (-3 : ℤ)‖ = 1 / x ^ 3 := by
        rw [Real.norm_eq_abs, abs_of_pos (zpow_pos hx _)]
        simp [zpow_neg]
      simp only [Real.norm_eq_abs] at h1 hn
      rw [hn] at h1
      have h2 := (abs_le.mp h1).1
      have h3 : K * (1 / x ^ 3) ≤ |K| / x ^ 3 := by
        calc K * (1 / x ^ 3) ≤ |K| * (1 / x ^ 3) :=
              mul_le_mul_of_nonneg_right (le_abs_self K) (by positivity)
          _ = |K| / x ^ 3 := mul_one_div _ _
      have h4 : (K * (1 / x ^ 3)) = K / x ^ 3 := by ring
      linarith
  obtain ⟨s, hs⟩ := fwd_real C hC0
  obtain ⟨M0, hm⟩ : ∃ M0 : RatFunc ℝ, Rep (fun x => 1 / 2 + 1 / (4 * (x - s))) M0 := by
    have := (Rep.const (1 / 2 : ℝ)).add ((Rep.const (1 / 4 : ℝ)).mul (Rep.X.sub (Rep.const s)).inv)
    exact ⟨_, this.congr (Eventually.of_forall fun x => by field_simp)⟩
  have hBsh : Rep (fun x => ev B (x + -1)) (shiftRF (-1) B) := (Rep.self B).shift (-1)
  have hLrep := hBsh.mul hm
  set L : RatFunc ℝ := shiftRF (-1) B * M0 with hLdef
  have hL1 : ∀ᶠ x : ℝ in atTop, ev B (x + 1 + -1) * (1 / 2 + 1 / (4 * (x + 1 - s))) = ev L (x + 1) :=
    shift_fwd 1 hLrep
  have hL0 : ∀ᶠ x : ℝ in atTop, ev B (x + -1) * (1 / 2 + 1 / (4 * (x - s))) = ev L x := hLrep
  have hBm : ∀ᶠ x : ℝ in atTop, 0 < ev B (x + -1) := shift_fwd (-1) hB
  refine ⟨L, ?_, ?_, ?_⟩
  · filter_upwards [hL1, hB, hs] with x h1 h2 h3
    have : x + 1 + -1 = x := by ring
    rw [this] at h1
    rw [← h1]
    exact mul_pos h2 h3.2.2.1
  · filter_upwards [hL1, hB, hs] with x h1 h2 h3
    have : x + 1 + -1 = x := by ring
    rw [this] at h1
    show ev L (x + 1) < ev B x
    rw [← h1]
    nlinarith [h3.2.1]
  · filter_upwards [hL1, hL0, hB, hBm, hs, hC] with x h1 h0 h2 h3 h4 h5
    have : x + 1 + -1 = x := by ring
    rw [this] at h1
    show 0 ≤ ev L x * (ev B x - ev L (x + 1)) + ev A x
    rw [← h1, ← h0]
    have h5' : -(1 / 4) - 1 / (16 * x ^ 2) - C / x ^ 3 ≤ ev A x / (ev B x * ev B (x + -1)) := by
      rw [← sub_eq_add_neg]; exact h5
    set m := 1 / 2 + 1 / (4 * (x - s))
    set m' := 1 / 2 + 1 / (4 * (x + 1 - s))
    have hbb : 0 < ev B x * ev B (x + -1) := mul_pos h2 h3
    have e1 : ev A x = (ev A x / (ev B x * ev B (x + -1))) * (ev B x * ev B (x + -1)) := by
      field_simp
    have e2 : 0 ≤ m * (1 - m') + ev A x / (ev B x * ev B (x + -1)) := by linarith [h4.2.2.2]
    have e3 : ev B (x + -1) * m * (ev B x - ev B x * m') + ev A x =
        (ev B x * ev B (x + -1)) * (m * (1 - m') + ev A x / (ev B x * ev B (x + -1))) := by
      field_simp
    rw [e3]
    exact mul_nonneg hbb.le e2


lemma backward (A B : RatFunc ℝ) (hB : ∀ᶠ x : ℝ in atTop, 0 < ev B x) (L : RatFunc ℝ)
    (hL : IsRiccatiWitness (ev A) (ev B) L) : SatisfiesInequalitySix (ev A) (ev B) := by
  obtain ⟨hL1, hL2, hL3⟩ := hL
  have hBsh : Rep (fun x => ev B (x + -1)) (shiftRF (-1) B) := (Rep.self B).shift (-1)
  have hV : Rep (fun x => ev L x / ev B (x + -1)) (L * (shiftRF (-1) B)⁻¹) :=
    (Rep.self L).div hBsh
  set V : RatFunc ℝ := L * (shiftRF (-1) B)⁻¹ with hVdef
  have hV0 : ∀ᶠ x : ℝ in atTop, ev L x / ev B (x + -1) = ev V x := hV
  have hV1 : ∀ᶠ x : ℝ in atTop, ev L (x + 1) / ev B (x + 1 + -1) = ev V (x + 1) := shift_fwd 1 hV
  have hBm : ∀ᶠ x : ℝ in atTop, 0 < ev B (x + -1) := shift_fwd (-1) hB
  have hVb : ∀ᶠ x : ℝ in atTop, 0 < ev V x ∧ ev V x < 1 := by
    apply shift_ev
    filter_upwards [hV1, hL1, hL2, hB] with x h1 h2 h3 h4
    have e : x + 1 + -1 = x := by ring
    rw [e] at h1
    have h2' : 0 < ev L (x + 1) := h2
    have h3' : ev L (x + 1) < ev B x := h3
    rw [← h1]
    exact ⟨div_pos h2' h4, (div_lt_one h4).mpr h3'⟩
  have hbd : ∃ K : ℝ, ∀ᶠ x : ℝ in atTop, |ev V x| ≤ K :=
    ⟨1, hVb.mono fun x h => by rw [abs_of_pos h.1]; exact h.2.le⟩
  obtain ⟨C, hC⟩ := riccati_bound V hbd
  have hR : ∀ᶠ x : ℝ in atTop,
      -(ev V x * (1 - ev V (x + 1))) ≤ ev A x / (ev B x * ev B (x + -1)) := by
    filter_upwards [hV0, hV1, hL3, hB, hBm] with x h0 h1 h3 h4 h5
    have e : x + 1 + -1 = x := by ring
    rw [e] at h1
    have h3' : 0 ≤ ev L x * (ev B x - ev L (x + 1)) + ev A x := h3
    rw [← h0, ← h1]
    have : ev A x / (ev B x * ev B (x + -1)) - -(ev L x / ev B (x + -1) * (1 - ev L (x + 1) / ev B x)) =
        (ev L x * (ev B x - ev L (x + 1)) + ev A x) / (ev B x * ev B (x + -1)) := by
      field_simp
      ring
    have h6 : 0 ≤ (ev L x * (ev B x - ev L (x + 1)) + ev A x) / (ev B x * ev B (x + -1)) :=
      div_nonneg h3' (mul_pos h4 h5).le
    linarith
  obtain ⟨Tr, hTr⟩ : ∃ Tr : RatFunc ℝ, Rep (fun x => -(1 / 4) - 1 / (16 * x ^ 2)) Tr :=
    ⟨_, ((Rep.const (-(1 / 4 : ℝ))).sub ((Rep.const (1 : ℝ)).div
      ((Rep.const (16 : ℝ)).mul (Rep.X.mul Rep.X)))).congr
      (Eventually.of_forall fun x => by ring)⟩
  have hRrep : Rep (fun x => ev A x / (ev B x * ev B (x + -1))) _ :=
    (Rep.self A).div ((Rep.self B).mul hBsh)
  have hW := (hRrep.sub hTr)
  refine geMod_of_rat _ _ _ (hW.congr (Eventually.of_forall fun x => ?_)) C ?_
  · simp only [sub_eq_add_neg]
  · filter_upwards [hR, hC] with x h1 h2
    have e : ev B (x - 1) = ev B (x + -1) := by rw [sub_eq_add_neg]
    show -(C / x ^ 3) ≤ ev A x / (ev B x * ev B (x - 1)) - (-(1 / 4) - 1 / (16 * x ^ 2))
    rw [e]
    linarith

end HolonomicPositivity.Dev.L53

namespace HolonomicPositivity.Robust
open HolonomicPositivity.Dev.L53 in
theorem chk_lemma_5_3 (A B : RatFunc ℝ) (hB : EventuallyGT (ev B) (fun _ => 0)) :
    SatisfiesInequalitySix (ev A) (ev B) ↔ ∃ L : RatFunc ℝ, IsRiccatiWitness (ev A) (ev B) L :=
  ⟨forward A B hB, fun ⟨L, hL⟩ => backward A B hB L hL⟩

end HolonomicPositivity.Robust
end

theorem solution : type_of% @HolonomicPositivity.Robust.chk_lemma_5_3 := @HolonomicPositivity.Robust.chk_lemma_5_3
