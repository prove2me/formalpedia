-- Prove2me | solution 1 for HedgePSNV.riskneutral_nv_maximizer_exists
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-08T00:22:58.568199+00:00
-- url     : https://prove2.me/submissions/41acf7e4-934c-4a54-a646-911d1f5c2898

import Mathlib
import Definitions.Def_HedgePSNV_Model

set_option autoImplicit false
set_option linter.unusedSectionVars false

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace HedgePSNVNVExist

open HedgePSNV

/-! ### The newsvendor problem for a market-size law `ν` on `ℝ` -/

section Core

variable (ν : Measure ℝ) [IsProbabilityMeasure ν]

/-- `Gf R = E[(R - A)^+]`. -/
noncomputable def Gf (R : ℝ) : ℝ := ∫ a, max (R - a) 0 ∂ν

/-- The expected payoff `(P - c)(R - bP) - (P - s) E[(R - A)^+]`. -/
noncomputable def Vf (p : Params) (P R : ℝ) : ℝ := (P - p.c) * (R - p.b * P) - (P - p.s) * Gf ν R

lemma integ (hint : Integrable (fun a : ℝ => max (-a) 0) ν) (R : ℝ) :
    Integrable (fun a : ℝ => max (R - a) 0) ν := by
  have hc : Continuous (fun a : ℝ => max (R - a) 0) := by fun_prop
  refine ((integrable_const |R|).add hint).mono' hc.aestronglyMeasurable
    (Eventually.of_forall fun a => ?_)
  show ‖max (R - a) 0‖ ≤ |R| + max (-a) 0
  rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
  have h1 := le_abs_self R
  have h2 := le_max_left (-a) 0
  have h3 : (0 : ℝ) ≤ max (-a) 0 := le_max_right _ _
  have h4 := abs_nonneg R
  exact max_le (by linarith) (by linarith)

lemma Gf_nonneg (R : ℝ) : 0 ≤ Gf ν R :=
  integral_nonneg fun _ => le_max_right _ _

lemma nv_eq (p : Params) (hint : Integrable (fun a : ℝ => max (-a) 0) ν) (P R : ℝ) :
    nvValue p ν id P R = Vf ν p P R := by
  unfold nvValue payoff Vf Gf
  simp only [id]
  rw [integral_sub (integrable_const _) ((integ ν hint R).const_mul _), integral_const,
    integral_const_mul]
  simp

lemma subgrad (hint : Integrable (fun a : ℝ => max (-a) 0) ν) (x R : ℝ) :
    Gf ν x + cdf ν x * (R - x) ≤ Gf ν R := by
  have hg : Integrable (fun a : ℝ => (Iic x).indicator (fun _ => R - x) a) ν :=
    (integrable_const (R - x)).indicator measurableSet_Iic
  have hind : ∫ a, (Iic x).indicator (fun _ => R - x) a ∂ν = cdf ν x * (R - x) := by
    rw [integral_indicator_const _ measurableSet_Iic, cdf_eq_real, smul_eq_mul]
  have heq : ∫ a, (max (x - a) 0 + (Iic x).indicator (fun _ => R - x) a) ∂ν =
      ∫ a, max (x - a) 0 ∂ν + ∫ a, (Iic x).indicator (fun _ => R - x) a ∂ν :=
    integral_add (integ ν hint x) hg
  have hle : ∫ a, (max (x - a) 0 + (Iic x).indicator (fun _ => R - x) a) ∂ν ≤
      ∫ a, max (R - a) 0 ∂ν := by
    refine integral_mono ((integ ν hint x).add hg) (integ ν hint R) (fun a => ?_)
    show max (x - a) 0 + (Iic x).indicator (fun _ => R - x) a ≤ max (R - a) 0
    by_cases ha : a ≤ x
    · rw [indicator_of_mem (show a ∈ Iic x from ha), max_eq_left (by linarith)]
      have := le_max_left (R - a) 0
      linarith
    · rw [indicator_of_notMem (show a ∉ Iic x from ha), max_eq_right (by linarith)]
      have := le_max_right (R - a) 0
      linarith
  unfold Gf
  linarith

lemma facts (h1 : Assumption1 ν) : ∃ f r r' : ℝ → ℝ,
    (∀ a, HasDerivAt (cdf ν) (f a) a) ∧ (∀ a, 0 < r a) ∧ (∀ a, cdf ν a < 1) ∧
    (∀ a, f a = r a * (1 - cdf ν a)) ∧ (∀ a, HasDerivAt r (r' a) a) ∧
    (∀ a, 0 < 2 * r a ^ 2 + r' a) ∧
    Tendsto (fun a => (1 - cdf ν a) ^ 2 / r a) atTop (𝓝 0) := by
  obtain ⟨f, r, r', hf, hr, hr', hpos, hw, -⟩ := h1
  have hf' : ∀ a, HasDerivAt (cdf ν) (f a) a := hf
  have hf0 : ∀ a, 0 ≤ f a := fun a => by
    have h := (monotone_cdf ν).deriv_nonneg (x := a)
    rwa [(hf' a).deriv] at h
  have hr0 : ∀ a, 0 ≤ r a := fun a => by
    rw [hr a]; exact div_nonneg (hf0 a) (by linarith [cdf_le_one ν a])
  have hrpos : ∀ a, 0 < r a := fun a => by
    rcases (hr0 a).lt_or_eq with h | h
    · exact h
    · exfalso
      have hmin : IsLocalMin r a := Eventually.of_forall fun y => by rw [← h]; exact hr0 y
      have hz := hmin.hasDerivAt_eq_zero (hr' a)
      have := hpos a
      rw [← h, hz] at this
      norm_num at this
  have hS : ∀ a, cdf ν a < 1 := fun a => by
    by_contra hc
    have h1' : cdf ν a = 1 := le_antisymm (cdf_le_one ν a) (not_lt.1 hc)
    have := hrpos a
    rw [hr a, h1', sub_self, div_zero] at this
    exact lt_irrefl _ this
  have hfr : ∀ a, f a = r a * (1 - cdf ν a) := fun a => by
    rw [hr a, div_mul_cancel₀ _ (sub_pos.2 (hS a)).ne']
  exact ⟨f, r, r', hf', hrpos, hS, hfr, hr', hpos, hw⟩

lemma Gf_deriv (hint : Integrable (fun a : ℝ => max (-a) 0) ν) (hFc : Continuous (cdf ν))
    (x : ℝ) : HasDerivAt (Gf ν) (cdf ν x) x := by
  rw [hasDerivAt_iff_tendsto_slope]
  have hlo : Tendsto (fun y => min (cdf ν x) (cdf ν y)) (𝓝[≠] x) (𝓝 (cdf ν x)) := by
    have h : Tendsto (fun y => min (cdf ν x) (cdf ν y)) (𝓝 x) (𝓝 (min (cdf ν x) (cdf ν x))) :=
      ((continuous_const.min hFc).tendsto x)
    rw [min_self] at h
    exact h.mono_left nhdsWithin_le_nhds
  have hhi : Tendsto (fun y => max (cdf ν x) (cdf ν y)) (𝓝[≠] x) (𝓝 (cdf ν x)) := by
    have h : Tendsto (fun y => max (cdf ν x) (cdf ν y)) (𝓝 x) (𝓝 (max (cdf ν x) (cdf ν x))) :=
      ((continuous_const.max hFc).tendsto x)
    rw [max_self] at h
    exact h.mono_left nhdsWithin_le_nhds
  have hb : ∀ y, y ≠ x → min (cdf ν x) (cdf ν y) ≤ slope (Gf ν) x y ∧
      slope (Gf ν) x y ≤ max (cdf ν x) (cdf ν y) := by
    intro y hy
    have h1 := subgrad ν hint y x
    have h2 := subgrad ν hint x y
    rw [slope_def_field]
    rcases lt_or_gt_of_ne hy with h | h
    · have hn : y - x < 0 := by linarith
      rw [min_eq_right (monotone_cdf ν h.le), max_eq_left (monotone_cdf ν h.le),
        le_div_iff_of_neg hn, div_le_iff_of_neg hn]
      constructor <;> nlinarith
    · have hp : 0 < y - x := by linarith
      rw [min_eq_left (monotone_cdf ν h.le), max_eq_right (monotone_cdf ν h.le),
        le_div_iff₀ hp, div_le_iff₀ hp]
      constructor <;> nlinarith
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hhi ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with y hy using (hb y hy).1
  · filter_upwards [self_mem_nhdsWithin] with y hy using (hb y hy).2

/-- The key tail estimate: `(1 - F x) * (x - G x) → 0` from above (Assumption 1). -/
lemma core_lim (hint : Integrable (fun a : ℝ => max (-a) 0) ν) (h1 : Assumption1 ν)
    (ε : ℝ) (hε : 0 < ε) : ∃ X, ∀ x, X ≤ x → (1 - cdf ν x) * (x - Gf ν x) ≤ ε := by
  obtain ⟨f, r, r', hf, hrpos, hS, hfr, hr', hpos, hw⟩ := facts ν h1
  have hFc : Continuous (cdf ν) := continuous_iff_continuousAt.2 fun a => (hf a).continuousAt
  have hGd := Gf_deriv ν hint hFc
  -- w = S^2 / r is antitone
  have hwanti : Antitone (fun a => (1 - cdf ν a) ^ 2 / r a) := by
    refine antitone_of_hasDerivAt_nonpos
      (fun a => (((hasDerivAt_const a (1 : ℝ)).sub (hf a)).pow 2).div (hr' a) (hrpos a).ne') ?_
    intro a
    simp only [Pi.zero_apply]
    rw [div_le_iff₀ (pow_pos (hrpos a) 2), zero_mul, hfr a]
    have hq : 0 < (1 - cdf ν a) ^ 2 * (2 * r a ^ 2 + r' a) :=
      mul_pos (pow_pos (sub_pos.2 (hS a)) 2) (hpos a)
    norm_num
    nlinarith
  -- the comparison function
  have hphi : ∀ y x, y ≤ x → x - Gf ν x ≤ (y - Gf ν y) - (1 - cdf ν y) ^ 2 / r y / (1 - cdf ν y)
      + (1 - cdf ν y) ^ 2 / r y / (1 - cdf ν x) := by
    intro y x hxy
    set c0 := (1 - cdf ν y) ^ 2 / r y with hc0
    have hd : ∀ t, HasDerivAt (fun t => (t - Gf ν t) - c0 / (1 - cdf ν t))
        ((1 - cdf ν t) - (0 * (1 - cdf ν t) - c0 * (0 - f t)) / (1 - cdf ν t) ^ 2) t := by
      intro t
      exact ((hasDerivAt_id' t).sub (hGd t)).sub
        ((hasDerivAt_const t c0).div ((hasDerivAt_const t (1 : ℝ)).sub (hf t))
          (sub_pos.2 (hS t)).ne')
    have hanti : AntitoneOn (fun t => (t - Gf ν t) - c0 / (1 - cdf ν t)) (Ici y) := by
      refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici y)
        (fun t _ => (hd t).continuousAt.continuousWithinAt)
        (fun t _ => (hd t).hasDerivWithinAt) ?_
      intro t ht
      rw [interior_Ici] at ht
      have hyt : y ≤ t := le_of_lt ht
      have hSt : 0 < 1 - cdf ν t := sub_pos.2 (hS t)
      have hwt : (1 - cdf ν t) ^ 2 / r t ≤ c0 := hwanti hyt
      have hcr : (1 - cdf ν t) ^ 2 ≤ c0 * r t := (div_le_iff₀ (hrpos t)).1 hwt
      rw [hfr t]
      have heq : (0 * (1 - cdf ν t) - c0 * (0 - r t * (1 - cdf ν t))) / (1 - cdf ν t) ^ 2
          = c0 * r t / (1 - cdf ν t) := by
        field_simp
        ring
      rw [heq, sub_nonpos, le_div_iff₀ hSt]
      nlinarith
    have := hanti (show y ∈ Ici y from le_refl y) (show x ∈ Ici y from hxy) hxy
    simpa using this
  -- choose y with w y small
  obtain ⟨y, hy⟩ := eventually_atTop.1 (hw.eventually (gt_mem_nhds (half_pos hε)))
  have hwy := hy y le_rfl
  set K := (y - Gf ν y) - (1 - cdf ν y) ^ 2 / r y / (1 - cdf ν y) with hK
  have hS0 : Tendsto (fun x => (1 - cdf ν x) * |K|) atTop (𝓝 0) := by
    have h := ((tendsto_const_nhds (x := (1 : ℝ))).sub (tendsto_cdf_atTop ν)).mul_const |K|
    simpa using h
  obtain ⟨X1, hX1⟩ := eventually_atTop.1 (hS0.eventually (gt_mem_nhds (half_pos hε)))
  refine ⟨max y X1, fun x hx => ?_⟩
  have hyx : y ≤ x := le_trans (le_max_left _ _) hx
  have hX1x : X1 ≤ x := le_trans (le_max_right _ _) hx
  have hSx : 0 < 1 - cdf ν x := sub_pos.2 (hS x)
  have hb := hphi y x hyx
  have hw0 : 0 ≤ (1 - cdf ν y) ^ 2 / r y := div_nonneg (sq_nonneg _) (hrpos y).le
  have h2 : (1 - cdf ν x) * (x - Gf ν x) ≤ (1 - cdf ν x) * K + (1 - cdf ν y) ^ 2 / r y := by
    have := mul_le_mul_of_nonneg_left hb hSx.le
    have hc : (1 - cdf ν x) * ((1 - cdf ν y) ^ 2 / r y / (1 - cdf ν x)) =
        (1 - cdf ν y) ^ 2 / r y := by field_simp
    nlinarith
  have h3 : (1 - cdf ν x) * K ≤ (1 - cdf ν x) * |K| :=
    mul_le_mul_of_nonneg_left (le_abs_self K) hSx.le
  have h4 := hX1 x hX1x
  linarith

/-- Large prices are not optimal. -/
lemma P_bound (p : Params) (hint : Integrable (fun a : ℝ => max (-a) 0) ν) (h1 : Assumption1 ν)
    (Vref : ℝ) : ∃ P0, p.c < P0 ∧ ∀ P R, P0 ≤ P → Vf ν p P R < Vref := by
  obtain ⟨f, r, r', hf, hrpos, hS, hfr, hr', hpos, hw⟩ := facts ν h1
  have hFc : Continuous (cdf ν) := continuous_iff_continuousAt.2 fun a => (hf a).continuousAt
  have hcs : 0 < p.c - p.s := sub_pos.2 p.hsc
  have hb := p.hb
  obtain ⟨X, hX⟩ := core_lim ν hint h1 (p.b * (p.c - p.s) / 2) (by positivity)
  set X' := max X 0 with hX'
  have hSX : 0 < 1 - cdf ν X' := sub_pos.2 (hS X')
  refine ⟨max (max (p.c + 1) (2 * (p.c - p.s) + 1))
    (max (p.s + (p.c - p.s) / (1 - cdf ν X') + 1) (p.s ^ 2 + 2 * |Vref| / p.b + 1)),
    by
      have := le_max_left (max (p.c + 1) (2 * (p.c - p.s) + 1))
        (max (p.s + (p.c - p.s) / (1 - cdf ν X') + 1) (p.s ^ 2 + 2 * |Vref| / p.b + 1))
      have := le_max_left (p.c + 1) (2 * (p.c - p.s) + 1)
      linarith, fun P R hP => ?_⟩
  have hA := le_trans (le_max_left _ _) hP
  have hB := le_trans (le_max_right _ _) hP
  have hP1 : p.c + 1 ≤ P := le_trans (le_max_left _ _) hA
  have hP2 : 2 * (p.c - p.s) + 1 ≤ P := le_trans (le_max_right _ _) hA
  have hP3 : p.s + (p.c - p.s) / (1 - cdf ν X') + 1 ≤ P := le_trans (le_max_left _ _) hB
  have hP4 : p.s ^ 2 + 2 * |Vref| / p.b + 1 ≤ P := le_trans (le_max_right _ _) hB
  have hPs : 0 < P - p.s := by linarith
  set τ := (P - p.c) / (P - p.s) with hτ
  have hτ0 : 0 < τ := div_pos (by linarith) hPs
  have hτ1 : τ < 1 := (div_lt_one hPs).2 (by linarith)
  obtain ⟨a, ha⟩ := ((tendsto_cdf_atBot ν).eventually (gt_mem_nhds hτ0)).exists
  obtain ⟨b', hb'⟩ := ((tendsto_cdf_atTop ν).eventually (lt_mem_nhds hτ1)).exists
  obtain ⟨x, hx⟩ := intermediate_value_univ a b' hFc ⟨ha.le, hb'.le⟩
  have hFx : (P - p.s) * cdf ν x = P - p.c := by
    rw [hx, hτ]; field_simp
  have hSx : (P - p.s) * (1 - cdf ν x) = p.c - p.s := by linarith
  have hxX : X' < x := by
    by_contra hcon
    push Not at hcon
    have hm := monotone_cdf ν hcon
    have h5 : (p.c - p.s) / (1 - cdf ν X') < P - p.s := by linarith
    rw [div_lt_iff₀ hSX] at h5
    have h6 : (P - p.s) * (1 - cdf ν X') ≤ (P - p.s) * (1 - cdf ν x) :=
      mul_le_mul_of_nonneg_left (by linarith) hPs.le
    linarith
  have hx0 : 0 ≤ x := le_trans (le_max_right _ _) hxX.le
  have hXx : X ≤ x := le_trans (le_max_left _ _) hxX.le
  have hcore := hX x hXx
  have hxG : x - Gf ν x ≤ p.b * (P - p.s) / 2 := by
    have h7 : (P - p.s) * ((1 - cdf ν x) * (x - Gf ν x)) ≤ (P - p.s) * (p.b * (p.c - p.s) / 2) :=
      mul_le_mul_of_nonneg_left hcore hPs.le
    have h8 : (p.c - p.s) * (x - Gf ν x) ≤ (p.c - p.s) * (p.b * (P - p.s) / 2) := by
      rw [← mul_assoc, hSx] at h7; linarith
    exact le_of_mul_le_mul_left h8 hcs
  have hsub := subgrad ν hint x R
  have h1' : (P - p.s) * (Gf ν x + cdf ν x * (R - x)) ≤ (P - p.s) * Gf ν R :=
    mul_le_mul_of_nonneg_left hsub hPs.le
  have h2' : (P - p.s) * (Gf ν x + cdf ν x * (R - x)) =
      (P - p.s) * Gf ν x + (P - p.c) * (R - x) := by
    rw [mul_add, ← mul_assoc, hFx]
  have h3' : (P - p.c) * x ≤ (P - p.s) * x := mul_le_mul_of_nonneg_right (by linarith) hx0
  have h4' : (P - p.s) * (x - Gf ν x) ≤ (P - p.s) * (p.b * (P - p.s) / 2) :=
    mul_le_mul_of_nonneg_left hxG hPs.le
  have h5' : P ≤ P * (P - 2 * (p.c - p.s)) := by
    have := mul_le_mul_of_nonneg_left (show (1 : ℝ) ≤ P - 2 * (p.c - p.s) by linarith)
      (show (0 : ℝ) ≤ P by linarith)
    linarith
  have h6' : p.b * P ≤ p.b * (P * (P - 2 * (p.c - p.s))) := mul_le_mul_of_nonneg_left h5' hb.le
  have h7' : p.b * (p.s ^ 2 + 2 * |Vref| / p.b + 1) ≤ p.b * P := mul_le_mul_of_nonneg_left hP4 hb.le
  have h8' : p.b * (2 * |Vref| / p.b) = 2 * |Vref| := by field_simp
  have h9' := neg_abs_le Vref
  unfold Vf
  nlinarith

/-- For bounded prices, large `R` are not optimal. -/
lemma R_bound (p : Params) (hint : Integrable (fun a : ℝ => max (-a) 0) ν) (h1 : Assumption1 ν)
    (P0 : ℝ) (hP0 : p.c < P0) (Vref : ℝ) :
    ∃ R0, ∀ P R, p.c ≤ P → P ≤ P0 → Vref ≤ Vf ν p P R → R ≤ R0 := by
  obtain ⟨f, r, r', hf, hrpos, hS, hfr, hr', hpos, hw⟩ := facts ν h1
  have hcs : 0 < p.c - p.s := sub_pos.2 p.hsc
  have hb := p.hb
  have hP0s : 0 < P0 - p.s := by linarith
  set δ := (p.c - p.s) / (2 * (P0 - p.s)) with hδ
  have hδ0 : 0 < δ := div_pos hcs (by linarith)
  have hS0 : Tendsto (fun x => 1 - cdf ν x) atTop (𝓝 0) := by
    have h := (tendsto_const_nhds (x := (1 : ℝ))).sub (tendsto_cdf_atTop ν)
    simpa using h
  obtain ⟨x1, hx1⟩ := (hS0.eventually (gt_mem_nhds hδ0)).exists
  set K := (P0 - p.c) * (|x1| + p.b * (|p.c| + |P0|)) with hK
  refine ⟨|x1| + 2 * |K - Vref| / (p.c - p.s), fun P R hcP hPP0 hV => ?_⟩
  have hq : 0 ≤ 2 * |K - Vref| / (p.c - p.s) := by positivity
  by_cases hR : R ≤ x1
  · linarith [le_abs_self x1]
  push Not at hR
  have hPs : 0 < P - p.s := by linarith [p.hsc]
  have hsub := subgrad ν hint x1 R
  have h1' : (P - p.s) * (Gf ν x1 + cdf ν x1 * (R - x1)) ≤ (P - p.s) * Gf ν R :=
    mul_le_mul_of_nonneg_left hsub hPs.le
  have hG0 := Gf_nonneg ν x1
  have hG0' : 0 ≤ (P - p.s) * Gf ν x1 := mul_nonneg hPs.le hG0
  have hSx1 : 0 ≤ 1 - cdf ν x1 := sub_nonneg.2 (cdf_le_one ν x1)
  have hc1 : (P - p.s) * (1 - cdf ν x1) ≤ (P0 - p.s) * δ :=
    mul_le_mul (by linarith) hx1.le hSx1 hP0s.le
  have hc2 : (P0 - p.s) * δ = (p.c - p.s) / 2 := by rw [hδ]; field_simp
  have hcoef : (P - p.c) - (P - p.s) * cdf ν x1 ≤ -((p.c - p.s) / 2) := by nlinarith
  have hprod : ((P - p.c) - (P - p.s) * cdf ν x1) * (R - x1) ≤ (-((p.c - p.s) / 2)) * (R - x1) :=
    mul_le_mul_of_nonneg_right hcoef (by linarith)
  have habsP : -P ≤ |p.c| + |P0| := by
    rcases le_total 0 P with h | h
    · linarith [abs_nonneg p.c, abs_nonneg P0]
    · have : p.c ≤ P := hcP
      linarith [neg_abs_le p.c, abs_nonneg P0]
  have hB0 : 0 ≤ |x1| + p.b * (|p.c| + |P0|) := by positivity
  have hxb : x1 - p.b * P ≤ |x1| + p.b * (|p.c| + |P0|) := by
    have := mul_le_mul_of_nonneg_left habsP hb.le
    linarith [le_abs_self x1]
  have hK1 : (P - p.c) * (x1 - p.b * P) ≤ K := by
    have h1 := mul_le_mul_of_nonneg_left hxb (show 0 ≤ P - p.c by linarith)
    have h2 := mul_le_mul_of_nonneg_right (show P - p.c ≤ P0 - p.c by linarith) hB0
    linarith
  have hfin : (p.c - p.s) / 2 * (R - x1) ≤ K - Vref := by
    unfold Vf at hV
    nlinarith
  have hfin2 : R - x1 ≤ 2 * |K - Vref| / (p.c - p.s) := by
    rw [le_div_iff₀ hcs]
    have := le_abs_self (K - Vref)
    nlinarith
  linarith [le_abs_self x1]

/-- Existence of a maximizer for a market-size law satisfying Assumption 1. -/
theorem core_exists (p : Params) (hint : Integrable (fun a : ℝ => max (-a) 0) ν)
    (h1 : Assumption1 ν) : ∃ P R, IsNVMaximizer p ν id P R := by
  obtain ⟨f, r, r', hf, -, -, -, -, -, -⟩ := facts ν h1
  have hFc : Continuous (cdf ν) := continuous_iff_continuousAt.2 fun a => (hf a).continuousAt
  have hGc : Continuous (Gf ν) :=
    continuous_iff_continuousAt.2 fun a => (Gf_deriv ν hint hFc a).continuousAt
  have hVc : Continuous (fun q : ℝ × ℝ => Vf ν p q.1 q.2) := by
    unfold Vf
    exact ((continuous_fst.sub continuous_const).mul
      (continuous_snd.sub (continuous_const.mul continuous_fst))).sub
      ((continuous_fst.sub continuous_const).mul (hGc.comp continuous_snd))
  set Vref := Vf ν p p.c (p.b * p.c) with hVref
  obtain ⟨P0, hcP0, hP0⟩ := P_bound ν p hint h1 Vref
  obtain ⟨R0, hR0⟩ := R_bound ν p hint h1 P0 hcP0 Vref
  set L : Set (ℝ × ℝ) := {q | p.c ≤ q.1} ∩ ({q | p.b * q.1 ≤ q.2} ∩
    {q | Vref ≤ Vf ν p q.1 q.2}) with hL
  have hclosed : IsClosed L :=
    (isClosed_le continuous_const continuous_fst).inter
      ((isClosed_le (continuous_const.mul continuous_fst) continuous_snd).inter
        (isClosed_le continuous_const hVc))
  have hsub : L ⊆ Icc ((p.c, p.b * p.c) : ℝ × ℝ) (P0, R0) := by
    intro q hq
    obtain ⟨h1q, h2q, h3q⟩ := hq
    have hq1 : q.1 ≤ P0 := by
      by_contra hc
      push Not at hc
      have := hP0 q.1 q.2 hc.le
      exact absurd h3q (not_le.2 this)
    have hbq : p.b * p.c ≤ q.2 :=
      le_trans (mul_le_mul_of_nonneg_left h1q p.hb.le) h2q
    exact ⟨Prod.le_def.2 ⟨h1q, hbq⟩, Prod.le_def.2 ⟨hq1, hR0 q.1 q.2 h1q hq1 h3q⟩⟩
  have hLc : IsCompact L := (isCompact_Icc).of_isClosed_subset hclosed hsub
  have hne : ((p.c, p.b * p.c) : ℝ × ℝ) ∈ L :=
    ⟨show p.c ≤ p.c from le_refl _, show p.b * p.c ≤ p.b * p.c from le_refl _, show Vref ≤ Vf ν p p.c (p.b * p.c) from hVref.le⟩
  obtain ⟨q, hqL, hqmax⟩ := hLc.exists_isMaxOn ⟨_, hne⟩ hVc.continuousOn
  refine ⟨q.1, q.2, ⟨hqL.1, hqL.2.1⟩, fun P' R' hD => ?_⟩
  rw [nv_eq ν p hint, nv_eq ν p hint]
  by_cases hV : Vref ≤ Vf ν p P' R'
  · exact isMaxOn_iff.1 hqmax (P', R') ⟨hD.1, hD.2, hV⟩
  · push Not at hV
    exact le_trans hV.le hqL.2.2

end Core

/-! ### Transfer from the model to the law of `A_T` under `P^M` -/

lemma I_zero_ae {p : Params} {Ω : Type*} [MeasurableSpace Ω] (M : Model p Ω)
    (hM : M.Standing) : M.I 0 =ᵐ[M.P] fun _ => (0 : ℝ) := by
  obtain ⟨a, -, -, -, hlim⟩ := hM.I_ito.2 0
  have hsum : ∀ n, EthierKurtz.itoStepSum M.B 0 n (a n) = fun _ => (0 : ℝ) := by
    intro n
    funext ω
    unfold EthierKurtz.itoStepSum
    simp
  have h0 : TendstoInMeasure M.P (fun n => EthierKurtz.itoStepSum M.B 0 n (a n)) Filter.atTop
      (fun _ => (0 : ℝ)) := by
    intro ε hε
    simp [hsum, not_le.mpr hε]
  exact tendstoInMeasure_ae_unique hlim h0

lemma PM_prob {p : Params} {Ω : Type*} [MeasurableSpace Ω] (M : Model p Ω)
    (hM : M.Standing) (h5 : M.Assumption5) : IsProbabilityMeasure M.PM := by
  have := hM.prob
  have hZ0 : M.Z 0 =ᵐ[M.P] fun _ => (1 : ℝ) := by
    filter_upwards [I_zero_ae M hM] with ω hω
    simp [Model.Z, hω]
  have hint : Integrable (M.Z p.T) M.P := (h5.1.2.1 p.T le_rfl)
  have hce := h5.1.2.2 0 p.T zero_le le_rfl
  have hE : ∫ ω, M.Z p.T ω ∂M.P = 1 := by
    rw [← integral_condExp (M.F.le 0)]
    rw [integral_congr_ae (hce.trans hZ0)]
    simp
  constructor
  unfold Model.PM
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal hint
      (Filter.Eventually.of_forall fun ω => (Real.exp_pos _).le), hE, ENNReal.ofReal_one]

lemma AT_aemeas {p : Params} {Ω : Type*} [MeasurableSpace Ω] (M : Model p Ω)
    (hM : M.Standing) : AEMeasurable M.AT M.P := by
  have hCm : Measurable (M.C p.T) := ((hM.C_adapted p.T).mono (M.G.le p.T)).measurable
  have hBm : AEMeasurable (M.Bt p.T) M.P :=
    (hM.brownBt.toIsPreBrownianReal.hasLaw_eval p.T).aemeasurable
  show AEMeasurable (fun ω => M.C p.T ω + p.σt * M.Bt p.T ω) M.P
  fun_prop

lemma PM_ac {p : Params} {Ω : Type*} [MeasurableSpace Ω] (M : Model p Ω) : M.PM ≪ M.P :=
  withDensity_absolutelyContinuous _ _

lemma nvValue_map (p : Params) {Ω : Type*} [MeasurableSpace Ω] (Q : Measure Ω) (A : Ω → ℝ)
    (hA : AEMeasurable A Q) (P R : ℝ) :
    nvValue p (Q.map A) id P R = nvValue p Q A P R := by
  unfold nvValue
  rw [integral_map hA]
  · rfl
  · have : Continuous (fun a => payoff p P R (id a)) := by
      unfold payoff; fun_prop
    exact this.aestronglyMeasurable

lemma isNVMax_map (p : Params) {Ω : Type*} [MeasurableSpace Ω] (Q : Measure Ω) (A : Ω → ℝ)
    (hA : AEMeasurable A Q) (P R : ℝ) :
    IsNVMaximizer p (Q.map A) id P R ↔ IsNVMaximizer p Q A P R := by
  unfold IsNVMaximizer
  simp only [nvValue_map p Q A hA]

lemma negPart_int_PM {p : Params} {Ω : Type*} [MeasurableSpace Ω] (M : Model p Ω)
    (hL2 : M.NegPartL2) (h5 : M.Assumption5) : M.NegPartIntegrable M.PM := by
  unfold Model.NegPartIntegrable Model.PM
  have hZm : StronglyMeasurable (M.Z p.T) := (h5.1.1 p.T le_rfl).mono (M.F.le p.T)
  rw [integrable_withDensity_iff_integrable_smul' hZm.measurable.ennreal_ofReal
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  have hZpos : ∀ ω, 0 ≤ M.Z p.T ω := fun ω => by
    simp only [Model.Z]; exact (Real.exp_pos _).le
  simp_rw [ENNReal.toReal_ofReal (hZpos _), smul_eq_mul]
  exact (h5.2 p.T le_rfl).integrable_mul hL2

lemma negPart_AT_PM {p : Params} {Ω : Type*} [MeasurableSpace Ω] (M : Model p Ω)
    (hM : M.Standing) (hintM : M.NegPartIntegrable M.PM) (h5 : M.Assumption5) :
    Integrable (fun ω => max (-(M.AT ω)) 0) M.PM := by
  have := hM.prob
  have hBlaw : HasLaw (M.Bt p.T) (gaussianReal 0 p.T) M.P :=
    hM.brownBt.toIsPreBrownianReal.hasLaw_eval p.T
  have hBm : AEMeasurable (M.Bt p.T) M.P := hBlaw.aemeasurable
  have hB2 : MemLp (M.Bt p.T) 2 M.P := by
    have h := memLp_id_gaussianReal' (μ := 0) (v := p.T) 2 (by simp)
    rw [← hBlaw.map_eq] at h
    exact (memLp_map_measure_iff aestronglyMeasurable_id hBm).1 h
  have hBPM : Integrable (fun ω => |M.Bt p.T ω|) M.PM := by
    unfold Model.PM
    have hZm : StronglyMeasurable (M.Z p.T) := (h5.1.1 p.T le_rfl).mono (M.F.le p.T)
    rw [integrable_withDensity_iff_integrable_smul' hZm.measurable.ennreal_ofReal
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    have hZpos : ∀ ω, 0 ≤ M.Z p.T ω := fun ω => by
      simp only [Model.Z]; exact (Real.exp_pos _).le
    simp_rw [ENNReal.toReal_ofReal (hZpos _), smul_eq_mul]
    exact (h5.2 p.T le_rfl).integrable_mul hB2.abs
  have hg : Integrable (fun ω => max (-(M.C p.T ω)) 0 + |p.σt| * |M.Bt p.T ω|) M.PM :=
    hintM.add (hBPM.const_mul |p.σt|)
  have hmeas : AEStronglyMeasurable (fun ω => max (-(M.AT ω)) 0) M.PM := by
    have h := (AT_aemeas M hM).mono_ac (PM_ac M)
    exact (by fun_prop : AEMeasurable (fun ω => max (-(M.AT ω)) 0) M.PM).aestronglyMeasurable
  refine hg.mono' hmeas (Filter.Eventually.of_forall fun ω => ?_)
  have h1 : -(p.σt * M.Bt p.T ω) ≤ |p.σt| * |M.Bt p.T ω| :=
    (neg_le_abs _).trans_eq (abs_mul _ _)
  have h3 := le_max_left (-(M.C p.T ω)) 0
  have h4 : (0 : ℝ) ≤ max (-(M.C p.T ω)) 0 := le_max_right _ _
  have h5' : (0 : ℝ) ≤ |p.σt| * |M.Bt p.T ω| := by positivity
  rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
  show max (-(M.C p.T ω + p.σt * M.Bt p.T ω)) 0 ≤ _
  exact max_le (by linarith) (by linarith)

end HedgePSNVNVExist

open HedgePSNV in
theorem solution (p : Params) {Ω : Type*} [MeasurableSpace Ω]
    (M : Model p Ω) (hM : M.Standing) (hL2 : M.NegPartL2) (h5 : M.Assumption5)
    (h1M : Assumption1 (M.PM.map M.AT)) :
    ∃ P R : ℝ, IsNVMaximizer p M.PM M.AT P R := by
  have hPM := HedgePSNVNVExist.PM_prob M hM h5
  have hA : AEMeasurable M.AT M.PM :=
    (HedgePSNVNVExist.AT_aemeas M hM).mono_ac (HedgePSNVNVExist.PM_ac M)
  have : IsProbabilityMeasure (M.PM.map M.AT) := Measure.isProbabilityMeasure_map hA
  have hint : Integrable (fun a : ℝ => max (-a) 0) (M.PM.map M.AT) := by
    rw [integrable_map_measure (by fun_prop) hA]
    exact HedgePSNVNVExist.negPart_AT_PM M hM (HedgePSNVNVExist.negPart_int_PM M hL2 h5) h5
  obtain ⟨P, R, h⟩ := HedgePSNVNVExist.core_exists (M.PM.map M.AT) p hint h1M
  exact ⟨P, R, (HedgePSNVNVExist.isNVMax_map p M.PM M.AT hA P R).1 h⟩
