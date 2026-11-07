-- Prove2me | solution 1 for HedgePSNV.proposition_1
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-06T17:09:21.708214+00:00
-- url     : https://prove2.me/submissions/48185529-9d40-456c-b704-3473972e2c7a

import Mathlib
import Definitions.Def_HedgePSNV_Newsvendor

set_option autoImplicit false
set_option linter.unusedSectionVars false

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace HedgePSNVProp1

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


lemma min_int (hint : Integrable (fun a : ℝ => max (-a) 0) ν) (R : ℝ) :
    ∫ a, min R a ∂ν = R - Gf ν R := by
  have hpt : (fun a : ℝ => min R a) = fun a => R - max (R - a) 0 := by
    funext a
    rcases le_total R a with h | h
    · rw [min_eq_left h, max_eq_right (by linarith)]; ring
    · rw [min_eq_right h, max_eq_left (by linarith)]; ring
  rw [hpt, integral_sub (integrable_const _) (integ ν hint R), integral_const]
  simp [Gf]

lemma hint_of (p : Params) (P R : ℝ) (hP : p.s < P) (hpos : 0 < nvValue p ν id P R) :
    Integrable (fun a : ℝ => max (-a) 0) ν := by
  have hI : Integrable (fun a : ℝ => payoff p P R a) ν := by
    by_contra h
    unfold nvValue at hpos
    simp only [id] at hpos
    rw [integral_undef h] at hpos
    exact lt_irrefl _ hpos
  have hne : P - p.s ≠ 0 := (sub_pos.2 hP).ne'
  have hG : Integrable (fun a : ℝ => max (R - a) 0) ν := by
    have h2 : Integrable
        (fun a : ℝ => ((P - p.c) * (R - p.b * P) - payoff p P R a) / (P - p.s)) ν :=
      ((integrable_const _).sub hI).div_const _
    refine h2.congr (Eventually.of_forall fun a => ?_)
    simp only [payoff]
    rw [div_eq_iff hne]
    ring
  have hc : Continuous (fun a : ℝ => max (-a) 0) := by fun_prop
  refine (hG.add (integrable_const |R|)).mono' hc.aestronglyMeasurable
    (Eventually.of_forall fun a => ?_)
  show ‖max (-a) 0‖ ≤ max (R - a) 0 + |R|
  rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
  have h1 := neg_abs_le R
  have h2 := le_max_left (R - a) 0
  have h3 := le_max_right (R - a) 0
  have h4 := abs_nonneg R
  exact max_le (by linarith) (by linarith)

end Core

/-! ### One-variable calculus: the profile in `R` -/

section Calc

/-- `φ(R) = (P*(R) − s)(1 − F R)` with `P*(R) = (R − G R + bc)/(2b)`. -/
noncomputable def phi (G F : ℝ → ℝ) (b c s : ℝ) (x : ℝ) : ℝ :=
  ((x - G x + b * c) / (2 * b) - s) * (1 - F x)

/-- The profile value `V(P*(R), R)`. -/
noncomputable def vprof (G : ℝ → ℝ) (b c s : ℝ) (x : ℝ) : ℝ :=
  (x - G x + b * c) * (x - G x + b * c) / (4 * b) - c * x + s * G x

/-- `χ(R) = (1 − F R)/r R − (R − G R + bc − 2bs)`; `χ' = −(1−F)(2r²+r')/r² < 0`. -/
noncomputable def chi (G F r : ℝ → ℝ) (b c s : ℝ) (x : ℝ) : ℝ :=
  (1 - F x) / r x - (x - G x + b * c - 2 * b * s)

variable {G F f r r' : ℝ → ℝ} {b c s : ℝ}

lemma phi_deriv (hb : 0 < b) (hG : ∀ x, HasDerivAt G (F x) x) (hF : ∀ x, HasDerivAt F (f x) x)
    (hr : ∀ x, 0 < r x) (hfr : ∀ x, f x = r x * (1 - F x)) (x : ℝ) :
    HasDerivAt (phi G F b c s) ((1 - F x) * r x / (2 * b) * chi G F r b c s x) x := by
  have h : HasDerivAt (phi G F b c s) ((1 - F x) / (2 * b) * (1 - F x) +
      ((x - G x + b * c) / (2 * b) - s) * (-f x)) x := by
    unfold phi
    exact (((((hasDerivAt_id' x).sub (hG x)).add_const (b * c)).div_const (2 * b)).sub_const
      s).mul ((hF x).const_sub 1)
  refine h.congr_deriv ?_
  unfold chi
  rw [hfr x]
  have := (hr x).ne'
  field_simp
  ring

lemma vprof_deriv (hb : 0 < b) (hG : ∀ x, HasDerivAt G (F x) x) (x : ℝ) :
    HasDerivAt (vprof G b c s) (phi G F b c s x - (c - s)) x := by
  have hu := ((hasDerivAt_id' x).sub (hG x)).add_const (b * c)
  have h : HasDerivAt (vprof G b c s) (((1 - F x) * (x - G x + b * c) +
      (x - G x + b * c) * (1 - F x)) / (4 * b) - c * 1 + s * F x) x := by
    unfold vprof
    exact (((hu.mul hu).div_const (4 * b)).sub ((hasDerivAt_id' x).const_mul c)).add
      ((hG x).const_mul s)
  refine h.congr_deriv ?_
  unfold phi
  field_simp
  ring

lemma chi_anti (hG : ∀ x, HasDerivAt G (F x) x) (hF : ∀ x, HasDerivAt F (f x) x)
    (hr : ∀ x, 0 < r x) (hF1 : ∀ x, F x < 1) (hfr : ∀ x, f x = r x * (1 - F x))
    (hr' : ∀ x, HasDerivAt r (r' x) x) (hpos : ∀ x, 0 < 2 * r x ^ 2 + r' x) :
    StrictAnti (chi G F r b c s) := by
  have hd : ∀ x, HasDerivAt (chi G F r b c s)
      (-((1 - F x) * (2 * r x ^ 2 + r' x)) / r x ^ 2) x := by
    intro x
    have h : HasDerivAt (chi G F r b c s)
        ((-f x * r x - (1 - F x) * r' x) / r x ^ 2 - (1 - F x)) x := by
      unfold chi
      exact (((hF x).const_sub 1).div (hr' x) (hr x).ne').sub
        ((((hasDerivAt_id' x).sub (hG x)).add_const (b * c)).sub_const (2 * b * s))
    refine h.congr_deriv ?_
    rw [hfr x]
    have := (hr x).ne'
    field_simp
    ring
  refine strictAnti_of_hasDerivAt_neg hd (fun x => ?_)
  have h1 : 0 < (1 - F x) * (2 * r x ^ 2 + r' x) := mul_pos (sub_pos.2 (hF1 x)) (hpos x)
  have h2 : 0 < r x ^ 2 := by have := hr x; positivity
  rw [neg_div]
  exact neg_neg_of_pos (div_pos h1 h2)

lemma vprof_lt (hb : 0 < b) (hG : ∀ x, HasDerivAt G (F x) x) (hF : ∀ x, HasDerivAt F (f x) x)
    (hr : ∀ x, 0 < r x) (hF1 : ∀ x, F x < 1) (hfr : ∀ x, f x = r x * (1 - F x))
    (hr' : ∀ x, HasDerivAt r (r' x) x) (hpos : ∀ x, 0 < 2 * r x ^ 2 + r' x)
    {R1 R2 : ℝ} (h12 : R1 < R2) (e1 : phi G F b c s R1 = c - s) (e2 : phi G F b c s R2 = c - s) :
    vprof G b c s R1 < vprof G b c s R2 := by
  have hchi := chi_anti (b := b) (c := c) (s := s) hG hF hr hF1 hfr hr' hpos
  have hK : ∀ x, 0 < (1 - F x) * r x / (2 * b) := fun x =>
    div_pos (mul_pos (sub_pos.2 (hF1 x)) (hr x)) (by linarith)
  have hpc : ContinuousOn (phi G F b c s) (Icc R1 R2) :=
    (continuous_iff_continuousAt.2 fun x => (phi_deriv hb hG hF hr hfr x).continuousAt).continuousOn
  have hmid : ∀ t ∈ Ioo R1 R2, c - s < phi G F b c s t := by
    intro t ht
    by_contra hcon
    push Not at hcon
    obtain ⟨ξ1, hξ1, hd1⟩ := exists_hasDerivAt_eq_slope (phi G F b c s)
      (fun x => (1 - F x) * r x / (2 * b) * chi G F r b c s x) ht.1
      (hpc.mono (Icc_subset_Icc_right ht.2.le)) (fun x _ => phi_deriv hb hG hF hr hfr x)
    obtain ⟨ξ2, hξ2, hd2⟩ := exists_hasDerivAt_eq_slope (phi G F b c s)
      (fun x => (1 - F x) * r x / (2 * b) * chi G F r b c s x) ht.2
      (hpc.mono (Icc_subset_Icc_left ht.1.le)) (fun x _ => phi_deriv hb hG hF hr hfr x)
    have f1 : (1 - F ξ1) * r ξ1 / (2 * b) * chi G F r b c s ξ1 ≤ 0 := by
      rw [hd1]
      exact div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith [ht.1])
    have f2 : 0 ≤ (1 - F ξ2) * r ξ2 / (2 * b) * chi G F r b c s ξ2 := by
      rw [hd2]
      exact div_nonneg (by linarith) (by linarith [ht.2])
    have c1 : chi G F r b c s ξ1 ≤ 0 := by
      by_contra h
      push Not at h
      linarith [mul_pos (hK ξ1) h]
    have c2 : 0 ≤ chi G F r b c s ξ2 := by
      by_contra h
      push Not at h
      linarith [mul_neg_of_pos_of_neg (hK ξ2) h]
    have := hchi (hξ1.2.trans hξ2.1)
    linarith
  have hvc : ContinuousOn (vprof G b c s) (Icc R1 R2) :=
    (continuous_iff_continuousAt.2 fun x => (vprof_deriv (s := s) (c := c) hb hG x).continuousAt).continuousOn
  obtain ⟨ξ, hξ, hd⟩ := exists_hasDerivAt_eq_slope (vprof G b c s)
    (fun x => phi G F b c s x - (c - s)) h12 hvc (fun x _ => vprof_deriv hb hG x)
  have hm := hmid ξ hξ
  have hq : 0 < (vprof G b c s R2 - vprof G b c s R1) / (R2 - R1) := by
    rw [← hd]; linarith
  have := (div_pos_iff_of_pos_right (show (0 : ℝ) < R2 - R1 by linarith)).1 hq
  linarith

lemma phi_eq (hb : 0 < b) {P R : ℝ} (h1 : R - 2 * b * P + b * c - G R = 0)
    (h2 : (P - c) - (P - s) * F R = 0) : phi G F b c s R = c - s := by
  have hP : (R - G R + b * c) / (2 * b) = P := by
    rw [div_eq_iff (by positivity)]; linarith
  unfold phi
  rw [hP]
  linear_combination h2

lemma vprof_eq (hb : 0 < b) {P R : ℝ} (h1 : R - 2 * b * P + b * c - G R = 0) :
    vprof G b c s R = (P - c) * (R - b * P) - (P - s) * G R := by
  have hP : R - G R + b * c = 2 * b * P := by linarith
  unfold vprof
  rw [hP]
  have e : 2 * b * P * (2 * b * P) / (4 * b) = b * P ^ 2 := by field_simp; ring
  rw [e]
  linear_combination (-P) * h1

end Calc

/-! ### Assembly -/

theorem main (p : Params) (ν : Measure ℝ) [IsProbabilityMeasure ν] (h1 : Assumption1 ν)
    (PNV RNV : ℝ) (hNV : IsNVMaximizer p ν id PNV RNV) (h2 : Assumption2 p ν id PNV RNV) :
    (∀ P R : ℝ, IsNVMaximizer p ν id P R → P = PNV ∧ R = RNV) ∧
    2 * p.b * PNV - p.b * p.c = ∫ a, min RNV a ∂ν ∧
    cdf ν RNV = (PNV - p.c) / (PNV - p.s) := by
  obtain ⟨hcP, hRb, hval⟩ := h2
  have hs := p.hsc
  have hb := p.hb
  have hint := hint_of ν p PNV RNV (by linarith) hval
  obtain ⟨f, r, r', hf, hr, hF1, hfr, hr', hpos, -⟩ := facts ν h1
  have hFc : Continuous (cdf ν) := continuous_iff_continuousAt.2 fun a => (hf a).continuousAt
  have hG := Gf_deriv ν hint hFc
  have hvalV : 0 < Vf ν p PNV RNV := by rwa [nv_eq ν p hint] at hval
  -- every maximizer has the same value and is interior
  have hsame : ∀ P R, IsNVMaximizer p ν id P R → Vf ν p P R = Vf ν p PNV RNV := by
    intro P R hm
    have a1 := hm.2 PNV RNV hNV.1
    have a2 := hNV.2 P R hm.1
    rw [nv_eq ν p hint, nv_eq ν p hint] at a1 a2
    linarith
  have hinter : ∀ P R, IsNVMaximizer p ν id P R → p.c < P ∧ p.b * P < R := by
    intro P R hm
    have hv : 0 < Vf ν p P R := by rw [hsame P R hm]; exact hvalV
    have hd := hm.1
    have g0 := Gf_nonneg ν R
    unfold Vf at hv
    obtain ⟨hd1, hd2⟩ := hd
    constructor
    · by_contra hcon
      have e : P = p.c := le_antisymm (not_lt.1 hcon) hd1
      rw [e, sub_self, zero_mul, zero_sub] at hv
      nlinarith
    · by_contra hcon
      have e : R - p.b * P = 0 := by
        have : R ≤ p.b * P := not_lt.1 hcon
        simp only at hd2
        linarith
      rw [e, mul_zero, zero_sub] at hv
      nlinarith
  have hfoc : ∀ P R, IsNVMaximizer p ν id P R →
      R - 2 * p.b * P + p.b * p.c - Gf ν R = 0 ∧ (P - p.c) - (P - p.s) * cdf ν R = 0 := by
    intro P R hm
    obtain ⟨hcP', hRb'⟩ := hinter P R hm
    have hRb'' : P < R / p.b := by rw [lt_div_iff₀ hb]; linarith
    constructor
    · have hlm : IsLocalMax (fun P' => Vf ν p P' R) P := by
        filter_upwards [lt_mem_nhds hcP', gt_mem_nhds hRb''] with P' h1' h2'
        have h2'' : P' * p.b < R := (lt_div_iff₀ hb).1 h2'
        have hdom : (P', R) ∈ decisionDomain p := ⟨h1'.le, by show p.b * P' ≤ R; linarith⟩
        have := hm.2 P' R hdom
        rwa [nv_eq ν p hint, nv_eq ν p hint] at this
      have hd : HasDerivAt (fun P' => Vf ν p P' R)
          (R - 2 * p.b * P + p.b * p.c - Gf ν R) P := by
        unfold Vf
        exact ((((hasDerivAt_id' P).sub_const p.c).mul
          (((hasDerivAt_id' P).const_mul p.b).const_sub R)).sub
          (((hasDerivAt_id' P).sub_const p.s).mul_const (Gf ν R))).congr_deriv (by ring)
      exact hlm.hasDerivAt_eq_zero hd
    · have hlm : IsLocalMax (fun R' => Vf ν p P R') R := by
        filter_upwards [lt_mem_nhds hRb'] with R' h1'
        have hdom : (P, R') ∈ decisionDomain p := ⟨hcP'.le, by show p.b * P ≤ R'; linarith⟩
        have := hm.2 P R' hdom
        rwa [nv_eq ν p hint, nv_eq ν p hint] at this
      have hd : HasDerivAt (fun R' => Vf ν p P R') ((P - p.c) - (P - p.s) * cdf ν R) R := by
        unfold Vf
        exact ((((hasDerivAt_id' R).sub_const (p.b * P)).const_mul (P - p.c)).sub
          ((hG R).const_mul (P - p.s))).congr_deriv (by ring)
      exact hlm.hasDerivAt_eq_zero hd
  obtain ⟨n1, n2⟩ := hfoc PNV RNV hNV
  refine ⟨fun P R hm => ?_, ?_, ?_⟩
  · obtain ⟨m1, m2⟩ := hfoc P R hm
    have hv := hsame P R hm
    have ph1 := phi_eq (G := Gf ν) (F := cdf ν) hb m1 m2
    have ph2 := phi_eq (G := Gf ν) (F := cdf ν) hb n1 n2
    have vp1 := vprof_eq (s := p.s) hb m1
    have vp2 := vprof_eq (s := p.s) hb n1
    have hVf : ∀ P R, Vf ν p P R = (P - p.c) * (R - p.b * P) - (P - p.s) * Gf ν R :=
      fun _ _ => rfl
    rw [hVf, hVf] at hv
    have hR : R = RNV := by
      rcases lt_trichotomy R RNV with h | h | h
      · have := vprof_lt hb hG hf hr hF1 hfr hr' hpos h ph1 ph2
        linarith
      · exact h
      · have := vprof_lt hb hG hf hr hF1 hfr hr' hpos h ph2 ph1
        linarith
    subst hR
    refine ⟨?_, rfl⟩
    have : 2 * p.b * P = 2 * p.b * PNV := by linarith
    have h2b : (2 * p.b) ≠ 0 := by positivity
    exact mul_left_cancel₀ h2b this
  · rw [min_int ν hint]; linarith
  · have hne : PNV - p.s ≠ 0 := by linarith
    rw [eq_div_iff hne]; linarith

end HedgePSNVProp1

open HedgePSNV MeasureTheory ProbabilityTheory in
theorem solution (p : Params) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (h1 : Assumption1 ν)
    (PNV RNV : ℝ) (hNV : IsNVMaximizer p ν id PNV RNV) (h2 : Assumption2 p ν id PNV RNV) :
    (∀ P R : ℝ, IsNVMaximizer p ν id P R → P = PNV ∧ R = RNV) ∧
    2 * p.b * PNV - p.b * p.c = ∫ a, min RNV a ∂ν ∧
    cdf ν RNV = (PNV - p.c) / (PNV - p.s) := by
  exact HedgePSNVProp1.main p ν h1 PNV RNV hNV h2
