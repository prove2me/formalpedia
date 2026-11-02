-- Prove2me | solution 1 for MemoryScreen.Menu.perfect_memory_derivative
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T22:25:22.43597+00:00
-- url     : https://prove2.me/submissions/d6db5dfd-077f-4b8b-a80e-26703279a005

import Mathlib
import Definitions.Def_MemoryScreen_Menu_Model

open MeasureTheory

namespace MemScreenAux
open MemoryScreen.Menu Filter Topology

variable {P : Params}

lemma fcont (hS : P.Standing) : Continuous P.f := hS.2.2.2.2.1
lemma fnn (hS : P.Standing) (b : ℝ) : 0 ≤ P.f b := hS.2.2.2.2.2.1 b
lemma fint (hS : P.Standing) : Integrable P.f := hS.2.2.2.2.2.2.1
lemma bfint (hS : P.Standing) : Integrable (fun b => b * P.f b) := hS.2.2.2.2.2.2.2.2

lemma gint (hS : P.Standing) (A B : ℝ) : Integrable (fun b => (A - b - B) * P.f b) := by
  have : (fun b => (A - b - B) * P.f b) = fun b => (A - B) * P.f b - b * P.f b := by
    funext b; ring
  rw [this]; exact ((fint hS).const_mul _).sub (bfint hS)

lemma gcont (hS : P.Standing) (A B : ℝ) : Continuous (fun b => (A - b - B) * P.f b) := by
  have := fcont hS; fun_prop

lemma key (hS : P.Standing) (A B u : ℝ) :
    ∫ b in Set.Iic u, (A - b - B) * P.f b =
      (A - B) * F P u - ∫ b in Set.Iic u, b * P.f b := by
  have : (fun b => (A - b - B) * P.f b) = fun b => (A - B) * P.f b - b * P.f b := by
    funext b; ring
  rw [this, integral_sub ((fint hS).integrableOn.const_mul _) (bfint hS).integrableOn,
    integral_const_mul]
  rfl

lemma cint (k u : ℝ) : ∫ b in Set.Iic u, k * P.f b = k * F P u := by
  rw [integral_const_mul]; rfl

lemma EU_eq (hS : P.Standing) (T p α αt : ℝ) :
    EU P T p α αt = (α - p) * F P (αt - p) - (∫ b in Set.Iic (αt - p), b * P.f b) - T := by
  unfold EU; rw [key hS]

lemma EU_shift (T s p α αt : ℝ) : EU P (T + s) p α αt = EU P T p α αt - s := by
  unfold EU; ring

lemma profit_eq (M : Menu) : profit P M =
    P.θ * (M.TH + (M.pH - P.c) * F P (P.αH - M.pH)) +
      (1 - P.θ) * (M.TL + (M.pL - P.c) * F P (P.αL - M.pL)) := by
  unfold profit; rw [cint, cint]

lemma reducedObj_eq (hS : P.Standing) (pH pL : ℝ) : reducedObj P pH pL =
    P.θ * (((P.αH - P.c) * F P (P.αH - pH) - ∫ b in Set.Iic (P.αH - pH), b * P.f b) -
      (P.αH - P.αL) * F P (P.αL - pL)) +
    (1 - P.θ) * ((P.αL - P.c) * F P (P.αL - pL) - ∫ b in Set.Iic (P.αL - pL), b * P.f b) := by
  unfold reducedObj; rw [key hS, key hS]

lemma F_nonneg (hS : P.Standing) (x : ℝ) : 0 ≤ F P x :=
  setIntegral_nonneg measurableSet_Iic (fun b _ => fnn hS b)

lemma F_mono (hS : P.Standing) {x y : ℝ} (h : x ≤ y) : F P x ≤ F P y := by
  have e := intervalIntegral.integral_Iic_sub_Iic (μ := volume) (fint hS).integrableOn
    (fint hS).integrableOn (a := x) (b := y)
  have : 0 ≤ ∫ b in x..y, P.f b := intervalIntegral.integral_nonneg h (fun b _ => fnn hS b)
  have e2 : F P y - F P x = ∫ b in x..y, P.f b := e
  linarith

lemma hasDerivAt_Iic {g : ℝ → ℝ} (hg : Continuous g) (hgi : Integrable g) (x : ℝ) :
    HasDerivAt (fun u => ∫ b in Set.Iic u, g b) (g x) x := by
  have h : (fun u => ∫ b in Set.Iic u, g b) =
      fun u => (∫ b in Set.Iic x, g b) + ∫ b in x..u, g b := by
    funext u
    rw [← intervalIntegral.integral_Iic_sub_Iic hgi.integrableOn hgi.integrableOn]; ring
  rw [h]
  exact ((hg.integral_hasStrictDerivAt x x).hasDerivAt).const_add _

lemma F_deriv (hS : P.Standing) (x : ℝ) : HasDerivAt (F P) (P.f x) x :=
  hasDerivAt_Iic (fcont hS) (fint hS) x

lemma N_deriv (hS : P.Standing) (x : ℝ) :
    HasDerivAt (fun u => ∫ b in Set.Iic u, b * P.f b) (x * P.f x) x :=
  hasDerivAt_Iic (g := fun b => b * P.f b) (by have := fcont hS; fun_prop) (bfint hS) x

lemma F_cont (hS : P.Standing) : Continuous (F P) :=
  continuous_iff_continuousAt.2 fun x => (F_deriv hS x).continuousAt

lemma comp_sub {φ : ℝ → ℝ} {φ' : ℝ} (A x : ℝ) (h : HasDerivAt φ φ' (A - x)) :
    HasDerivAt (fun y => φ (A - y)) (-φ') x :=
  (h.comp x ((hasDerivAt_id x).const_sub A)).congr_deriv (by simp)

/-- the reduced objective split into its two separate pieces -/
lemma red_split (hS : P.Standing) (pH pL : ℝ) : reducedObj P pH pL =
    P.θ * (∫ b in Set.Iic (P.αH - pH), (P.αH - b - P.c) * P.f b) +
      (1 - P.θ) * ∫ b in Set.Iic (P.αL - pL), (P.αL - b - pStarL P) * P.f b := by
  rw [reducedObj_eq hS, key hS, key hS]
  have hθ : (1 : ℝ) - P.θ ≠ 0 := by have := hS.2.2.1; linarith
  have h : (1 - P.θ) * (P.θ / (1 - P.θ)) = P.θ := by field_simp
  unfold pStarL
  linear_combination (P.αH - P.αL) * F P (P.αL - pL) * h

lemma max_le' (hS : P.Standing) (A B u : ℝ) :
    ∫ b in Set.Iic u, (A - b - B) * P.f b ≤ ∫ b in Set.Iic (A - B), (A - b - B) * P.f b := by
  have hgi := gint hS A B
  rw [← sub_nonpos, intervalIntegral.integral_Iic_sub_Iic hgi.integrableOn hgi.integrableOn]
  rcases le_total (A - B) u with h | h
  · have := intervalIntegral.integral_nonneg (μ := volume)
      (f := fun x => -((A - x - B) * P.f x)) h (fun x hx => by
        nlinarith [mul_nonneg (by linarith [hx.1] : 0 ≤ x - (A - B)) (fnn hS x)])
    rw [intervalIntegral.integral_neg] at this; linarith
  · rw [intervalIntegral.integral_symm]
    have := intervalIntegral.integral_nonneg (μ := volume)
      (f := fun x => (A - x - B) * P.f x) h (fun x hx =>
        mul_nonneg (by linarith [hx.2]) (fnn hS x))
    linarith

lemma max_eq' (hS : P.Standing) (A B bl bu : ℝ) (hbl : bl < A - B) (hbu : A - B < bu)
    (hpos : ∀ b ∈ Set.Ioo bl bu, 0 < P.f b) (u : ℝ)
    (heq : ∫ b in Set.Iic u, (A - b - B) * P.f b = ∫ b in Set.Iic (A - B), (A - b - B) * P.f b) :
    u = A - B := by
  have hgi := gint hS A B
  have hgc := gcont hS A B
  by_contra hne
  have e := intervalIntegral.integral_Iic_sub_Iic hgi.integrableOn hgi.integrableOn
    (a := A - B) (b := u) (μ := volume)
  have hk : ∫ x in (A - B)..u, (A - x - B) * P.f x < 0 := by
    rcases lt_or_gt_of_ne hne with h | h
    · have hm : max u bl < A - B := max_lt h hbl
      have h1 : 0 < ∫ x in (max u bl)..(A - B), (A - x - B) * P.f x :=
        intervalIntegral.intervalIntegral_pos_of_pos_on (hgc.intervalIntegrable _ _)
          (fun x hx => mul_pos (by linarith [hx.2])
            (hpos x ⟨lt_of_le_of_lt (le_max_right _ _) hx.1, by linarith [hx.2]⟩)) hm
      have h2 : 0 ≤ ∫ x in u..(max u bl), (A - x - B) * P.f x :=
        intervalIntegral.integral_nonneg (le_max_left _ _)
          (fun x hx => mul_nonneg (by linarith [hx.2]) (fnn hS x))
      have h3 := intervalIntegral.integral_add_adjacent_intervals
        (hgc.intervalIntegrable u (max u bl)) (hgc.intervalIntegrable (max u bl) (A - B))
        (μ := volume)
      rw [intervalIntegral.integral_symm]; linarith
    · have hm : A - B < min u bu := lt_min h hbu
      have h1 : 0 < ∫ x in (A - B)..(min u bu), -((A - x - B) * P.f x) :=
        intervalIntegral.intervalIntegral_pos_of_pos_on (hgc.neg.intervalIntegrable _ _)
          (fun x hx => by
            have := hpos x ⟨by linarith [hx.1], lt_of_lt_of_le hx.2 (min_le_right _ _)⟩
            nlinarith [mul_pos (by linarith [hx.1] : 0 < x - (A - B)) this]) hm
      have h2 : 0 ≤ ∫ x in (min u bu)..u, -((A - x - B) * P.f x) :=
        intervalIntegral.integral_nonneg (min_le_left _ _)
          (fun x hx => by
            nlinarith [mul_nonneg (by linarith [hx.1] : 0 ≤ x - (A - B)) (fnn hS x)])
      have h3 := intervalIntegral.integral_add_adjacent_intervals
        (hgc.intervalIntegrable (A - B) (min u bu)) (hgc.intervalIntegrable (min u bu) u)
        (μ := volume)
      rw [intervalIntegral.integral_neg] at h1 h2
      linarith
  linarith

lemma pStar_gt (hS : P.Standing) : P.c < pStarL P := by
  unfold pStarL
  have h1 : 0 < P.θ / (1 - P.θ) := div_pos hS.2.1 (by linarith [hS.2.2.1])
  have h2 : 0 < P.αH - P.αL := by linarith [hS.1]
  nlinarith [mul_pos h1 h2]

/-! ### Milestone statements -/

theorem m_integration_by_parts (P : Params) (hS : P.Standing) :
    (∀ x : ℝ, (∫ b in Set.Iic x, (x - b) * P.f b) =
      ∫ b in Set.Iic x, F P b) ∧
    (∀ T p α : ℝ, EU P T p α α = (∫ b in Set.Iic (α - p), F P b) - T) := by
  have hG : ∀ y : ℝ, (∫ b in Set.Iic y, (y - b) * P.f b) =
      y * F P y - ∫ b in Set.Iic y, b * P.f b := by
    intro y
    have := key hS y 0 y
    simp only [sub_zero] at this
    exact this
  have hGd : ∀ y : ℝ, HasDerivAt (fun y => y * F P y - ∫ b in Set.Iic y, b * P.f b)
      (F P y) y := by
    intro y
    exact (((hasDerivAt_id y).mul (F_deriv hS y)).sub (N_deriv hS y)).congr_deriv
      (by simp)
  have hGnn : ∀ y : ℝ, 0 ≤ y * F P y - ∫ b in Set.Iic y, b * P.f b := by
    intro y
    rw [← hG y]
    exact setIntegral_nonneg measurableSet_Iic
      (fun b hb => mul_nonneg (sub_nonneg.2 hb) (fnn hS b))
  have hFc := F_cont hS
  -- N tends to 0 at -∞
  have hN : Tendsto (fun a => ∫ b in Set.Iic a, b * P.f b) atBot (𝓝 0) := by
    have hi := (bfint hS)
    have h := intervalIntegral_tendsto_integral_Iic (μ := volume) 0 hi.integrableOn tendsto_id
    have h2 : Tendsto (fun a => (∫ x in Set.Iic 0, x * P.f x) - ∫ x in a..0, x * P.f x) atBot
        (𝓝 ((∫ x in Set.Iic 0, x * P.f x) - ∫ x in Set.Iic 0, x * P.f x)) :=
      tendsto_const_nhds.sub h
    rw [sub_self] at h2
    refine h2.congr (fun a => ?_)
    rw [← intervalIntegral.integral_Iic_sub_Iic hi.integrableOn hi.integrableOn]; simp
  have hlim : Tendsto (fun y => y * F P y - ∫ b in Set.Iic y, b * P.f b) atBot (𝓝 0) := by
    have hN' : Tendsto (fun a => -∫ b in Set.Iic a, b * P.f b) atBot (𝓝 0) := by
      simpa using hN.neg
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hN'
      (Eventually.of_forall hGnn) ?_
    filter_upwards [eventually_le_atBot (0 : ℝ)] with y hy
    nlinarith [mul_nonpos_of_nonpos_of_nonneg hy (F_nonneg hS y)]
  have part1 : ∀ x : ℝ, (∫ b in Set.Iic x, (x - b) * P.f b) = ∫ b in Set.Iic x, F P b := by
    intro x
    have hint : IntegrableOn (F P) (Set.Iic x) := by
      refine integrableOn_Iic_of_intervalIntegral_norm_bounded
        (x * F P x - ∫ b in Set.Iic x, b * P.f b) x
        (fun i => (hFc.integrableOn_Icc).mono_set Set.Ioc_subset_Icc_self) tendsto_id ?_
      filter_upwards [eventually_le_atBot x] with i hi
      have hn : (fun b => ‖F P b‖) = F P := by
        funext b; exact Real.norm_of_nonneg (F_nonneg hS b)
      simp only [id]
      rw [hn, intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y _ => hGd y)
        (hFc.intervalIntegrable i x)]
      linarith [hGnn i]
    rw [integral_Iic_of_hasDerivAt_of_tendsto' (fun y _ => hGd y) hint hlim, hG x, sub_zero]
  refine ⟨part1, fun T p α => ?_⟩
  unfold EU
  rw [← part1]
  congr 2
  funext b
  ring_nf

theorem m_information_rent (P : Params) (hS : P.Standing) :
    (∀ (T p α α' αt : ℝ),
      EU P T p α' αt - EU P T p α αt = (α' - α) * F P (αt - p)) ∧
    (∀ (T pL : ℝ),
      EU P T pL P.αH P.αL - EU P T pL P.αL P.αL =
        (P.αH - P.αL) * F P (P.αL - pL)) := by
  have h : ∀ (T p α α' αt : ℝ),
      EU P T p α' αt - EU P T p α αt = (α' - α) * F P (αt - p) := by
    intro T p α α' αt
    rw [EU_eq hS, EU_eq hS]; ring
  exact ⟨h, fun T pL => h _ _ _ _ _⟩

theorem m_binding_reduction (P : Params) (hS : P.Standing) :
    (∀ M : Menu, Feasible P M → profit P M ≤ reducedObj P M.pH M.pL) ∧
    (∀ pH pL : ℝ, profit P (bindingMenu P pH pL) = reducedObj P pH pL) ∧
    (∀ M : Menu, IsOptimal P M →
      EU P M.TL M.pL P.αL P.αL = 0 ∧
      EU P M.TL M.pL P.αH P.αL = EU P M.TH M.pH P.αH P.αH) := by
  have hθ := hS.2.1
  have hθ1 := hS.2.2.1
  have hd : 0 ≤ P.αH - P.αL := by linarith [hS.1]
  refine ⟨?_, ?_, ?_⟩
  · intro M hM
    obtain ⟨_, h2, h3, _⟩ := hM
    rw [EU_eq hS, EU_eq hS] at h3
    rw [EU_eq hS] at h2
    rw [profit_eq, reducedObj_eq hS]
    nlinarith [mul_nonneg hθ.le (sub_nonneg.2 h3)]
  · intro pH pL
    simp only [profit_eq, reducedObj_eq hS, bindingMenu, key hS]
    ring
  · intro M hM
    obtain ⟨⟨h1, h2, h3, h4⟩, hmax⟩ := hM
    -- rent identity
    have hrent : EU P M.TL M.pL P.αH P.αL =
        EU P M.TL M.pL P.αL P.αL + (P.αH - P.αL) * F P (P.αL - M.pL) := by
      rw [EU_eq hS, EU_eq hS]; ring
    have hFL := mul_nonneg hd (F_nonneg hS (P.αL - M.pL))
    constructor
    · by_contra hne
      set s := EU P M.TL M.pL P.αL P.αL with hs
      have hspos : 0 < s := lt_of_le_of_ne h2 (Ne.symm hne)
      let M' : Menu := ⟨M.TH + s, M.pH, M.TL + s, M.pL⟩
      have hF : Feasible P M' := by
        refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [M', EU_shift] <;> linarith
      have := hmax M' hF
      rw [profit_eq, profit_eq] at this
      simp only [M'] at this
      nlinarith
    · by_contra hne
      set s := EU P M.TH M.pH P.αH P.αH - EU P M.TL M.pL P.αH P.αL with hs
      have hspos : 0 < s := by
        have : EU P M.TL M.pL P.αH P.αL < EU P M.TH M.pH P.αH P.αH := lt_of_le_of_ne h3 hne
        linarith
      let M' : Menu := ⟨M.TH + s, M.pH, M.TL, M.pL⟩
      have hF : Feasible P M' := by
        refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [M', EU_shift] <;> linarith
      have := hmax M' hF
      rw [profit_eq, profit_eq] at this
      simp only [M'] at this
      nlinarith

theorem m_ic_low_high (P : Params) (hS : P.Standing) (pH pL : ℝ)
    (hprice : pH < pL) : Feasible P (bindingMenu P pH pL) := by
  have hd : 0 ≤ P.αH - P.αL := by linarith [hS.1]
  have hFL := mul_nonneg hd (F_nonneg hS (P.αL - pL))
  have hmono := mul_le_mul_of_nonneg_left
    (F_mono hS (by linarith [hS.1] : P.αL - pL ≤ P.αH - pH)) hd
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [bindingMenu, EU_eq hS, key hS] <;> nlinarith

theorem m_reduced_derivatives (P : Params) (hS : P.Standing) (pH pL : ℝ) :
    HasDerivAt (fun x : ℝ => reducedObj P x pL)
      (P.θ * (P.c - pH) * P.f (P.αH - pH)) pH ∧
    HasDerivAt (reducedObj P pH)
      (((1 - P.θ) * (P.c - pL) + P.θ * (P.αH - P.αL)) *
        P.f (P.αL - pL)) pL := by
  constructor
  · have e : (fun x : ℝ => reducedObj P x pL) = fun x =>
        P.θ * (((P.αH - P.c) * F P (P.αH - x) - ∫ b in Set.Iic (P.αH - x), b * P.f b) -
          (P.αH - P.αL) * F P (P.αL - pL)) +
        (1 - P.θ) * ((P.αL - P.c) * F P (P.αL - pL) -
          ∫ b in Set.Iic (P.αL - pL), b * P.f b) := by
      funext x; exact reducedObj_eq hS x pL
    rw [e]
    have hF := comp_sub P.αH pH (F_deriv hS (P.αH - pH))
    have hN := comp_sub P.αH pH (N_deriv hS (P.αH - pH))
    exact ((((hF.const_mul (P.αH - P.c)).sub hN).sub_const _).const_mul P.θ).add_const _
      |>.congr_deriv (by ring)
  · have e : reducedObj P pH = fun x =>
        P.θ * (((P.αH - P.c) * F P (P.αH - pH) - ∫ b in Set.Iic (P.αH - pH), b * P.f b) -
          (P.αH - P.αL) * F P (P.αL - x)) +
        (1 - P.θ) * ((P.αL - P.c) * F P (P.αL - x) -
          ∫ b in Set.Iic (P.αL - x), b * P.f b) := by
      funext x; exact reducedObj_eq hS pH x
    rw [e]
    have hF := comp_sub P.αL pL (F_deriv hS (P.αL - pL))
    have hN := comp_sub P.αL pL (N_deriv hS (P.αL - pL))
    exact (((hF.const_mul (P.αH - P.αL)).const_sub _).const_mul P.θ).add
      (((hF.const_mul (P.αL - P.c)).sub hN).const_mul (1 - P.θ))
      |>.congr_deriv (by ring)

theorem m_reduced_maximizer (P : Params) (hS : P.Standing) :
    (∀ pH pL : ℝ, reducedObj P pH pL ≤ reducedObj P P.c (pStarL P)) ∧
    (∀ bl bu : ℝ, bl < P.αL - pStarL P → P.αH - P.c < bu →
      (∀ b ∈ Set.Ioo bl bu, 0 < P.f b) →
      ∀ pH pL : ℝ, reducedObj P pH pL = reducedObj P P.c (pStarL P) →
        pH = P.c ∧ pL = pStarL P) := by
  have hθ := hS.2.1
  have hθ1 : 0 < 1 - P.θ := by linarith [hS.2.2.1]
  refine ⟨fun pH pL => ?_, fun bl bu hbl hbu hpos pH pL heq => ?_⟩
  · rw [red_split hS, red_split hS]
    exact add_le_add (mul_le_mul_of_nonneg_left (max_le' hS _ _ _) hθ.le)
      (mul_le_mul_of_nonneg_left (max_le' hS _ _ _) hθ1.le)
  · rw [red_split hS, red_split hS] at heq
    have m1 := max_le' hS P.αH P.c (P.αH - pH)
    have m2 := max_le' hS P.αL (pStarL P) (P.αL - pL)
    have e1 : ∫ b in Set.Iic (P.αH - pH), (P.αH - b - P.c) * P.f b =
        ∫ b in Set.Iic (P.αH - P.c), (P.αH - b - P.c) * P.f b := by
      nlinarith [mul_le_mul_of_nonneg_left m1 hθ.le, mul_le_mul_of_nonneg_left m2 hθ1.le,
        mul_pos hθ hθ1]
    have e2 : ∫ b in Set.Iic (P.αL - pL), (P.αL - b - pStarL P) * P.f b =
        ∫ b in Set.Iic (P.αL - pStarL P), (P.αL - b - pStarL P) * P.f b := by
      nlinarith [mul_le_mul_of_nonneg_left m1 hθ.le, mul_le_mul_of_nonneg_left m2 hθ1.le,
        mul_pos hθ hθ1]
    have hp := pStar_gt hS
    have hα := hS.1
    have u1 := max_eq' hS P.αH P.c bl bu (by linarith) hbu hpos _ e1
    have u2 := max_eq' hS P.αL (pStarL P) bl bu hbl (by linarith) hpos _ e2
    constructor <;> linarith

theorem m_perfect_memory_derivative (P : Params) (hS : P.Standing) :
    (∀ pH pL : ℝ,
      HasDerivAt (perfectObj P pH)
        (P.θ * (F P (P.αH - pL) - F P (P.αL - pL)) +
          (1 - P.θ) * (P.c - pL) * P.f (P.αL - pL)) pL) ∧
    (0 < deriv (perfectObj P P.c) (pStarL P) ↔
      P.f (P.αL - pStarL P) <
        (F P (P.αH - pStarL P) - F P (P.αL - pStarL P)) /
          (P.αH - P.αL)) := by
  have hFc := F_cont hS
  have hd : ∀ pH pL : ℝ,
      HasDerivAt (perfectObj P pH)
        (P.θ * (F P (P.αH - pL) - F P (P.αL - pL)) +
          (1 - P.θ) * (P.c - pL) * P.f (P.αL - pL)) pL := by
    intro pH pL
    have e : perfectObj P pH = fun x =>
        P.θ * (((P.αH - P.c) * F P (P.αH - pH) - ∫ b in Set.Iic (P.αH - pH), b * P.f b) -
          ((∫ b in (0:ℝ)..(P.αH - x), F P b) - ∫ b in (0:ℝ)..(P.αL - x), F P b)) +
        (1 - P.θ) * ((P.αL - P.c) * F P (P.αL - x) -
          ∫ b in Set.Iic (P.αL - x), b * P.f b) := by
      funext x
      unfold perfectObj
      rw [intervalIntegral.integral_interval_sub_left (hFc.intervalIntegrable _ _)
        (hFc.intervalIntegrable _ _), key hS, key hS]
    rw [e]
    have hG1 := comp_sub P.αH pL ((hFc.integral_hasStrictDerivAt 0 (P.αH - pL)).hasDerivAt)
    have hG2 := comp_sub P.αL pL ((hFc.integral_hasStrictDerivAt 0 (P.αL - pL)).hasDerivAt)
    have hF := comp_sub P.αL pL (F_deriv hS (P.αL - pL))
    have hN := comp_sub P.αL pL (N_deriv hS (P.αL - pL))
    exact (((hG1.sub hG2).const_sub _).const_mul P.θ).add
      (((hF.const_mul (P.αL - P.c)).sub hN).const_mul (1 - P.θ))
      |>.congr_deriv (by ring)
  refine ⟨hd, ?_⟩
  rw [(hd P.c (pStarL P)).deriv]
  have hθ := hS.2.1
  have hθ1 : (1 : ℝ) - P.θ ≠ 0 := by linarith [hS.2.2.1]
  have hα : 0 < P.αH - P.αL := by linarith [hS.1]
  have h : (1 - P.θ) * (P.c - pStarL P) = -(P.θ * (P.αH - P.αL)) := by
    unfold pStarL; field_simp; ring
  rw [lt_div_iff₀ hα]
  have h2 : (1 - P.θ) * (P.c - pStarL P) * P.f (P.αL - pStarL P) =
      -(P.θ * (P.αH - P.αL)) * P.f (P.αL - pStarL P) := by rw [h]
  rw [h2]
  have h3 : P.θ * (F P (P.αH - pStarL P) - F P (P.αL - pStarL P)) +
      -(P.θ * (P.αH - P.αL)) * P.f (P.αL - pStarL P) =
      P.θ * ((F P (P.αH - pStarL P) - F P (P.αL - pStarL P)) -
        P.f (P.αL - pStarL P) * (P.αH - P.αL)) := by ring
  rw [h3, mul_pos_iff_of_pos_left hθ, sub_pos]

end MemScreenAux

open MemoryScreen.Menu in
theorem solution (P : Params) (hS : P.Standing) :
    (∀ pH pL : ℝ,
      HasDerivAt (perfectObj P pH)
        (P.θ * (F P (P.αH - pL) - F P (P.αL - pL)) +
          (1 - P.θ) * (P.c - pL) * P.f (P.αL - pL)) pL) ∧
    (0 < deriv (perfectObj P P.c) (pStarL P) ↔
      P.f (P.αL - pStarL P) <
        (F P (P.αH - pStarL P) - F P (P.αL - pStarL P)) /
          (P.αH - P.αL)) :=
  MemScreenAux.m_perfect_memory_derivative P hS
