-- Prove2me | solution 1 for MultiItemRev.BundlingOpt.revenue_le_majorant
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T17:07:26.932663+00:00
-- url     : https://prove2.me/submissions/8ad9e99a-74e4-4d58-976a-5446b4368ee7

import Mathlib
import Definitions.Def_MultiItemRev_BundlingOpt_Model
import Definitions.Def_MultiItemRev_BundlingOpt_Bundling
import Theorems.Thm_MultiItemRev_BundlingOpt_display_18
import Theorems.Thm_MultiItemRev_BundlingOpt_bundled_majorant_ic_ir
open MeasureTheory
open scoped NNReal ENNReal

namespace MultiItemRev.BundlingOpt.RevMaj

open MultiItemRev.BundlingOpt

/-! ### Part A: elementary facts about IC mechanisms -/

section A
variable (M : Mechanism (Fin 2))

lemma ic_rearr (hIC : IsIC M) (x x' : Fin 2 → ℝ≥0) :
    buyerPayoff M x' - buyerPayoff M x ≤ ∑ i, M.q x' i * ((x' i : ℝ) - x i) := by
  have h := hIC x x'
  unfold buyerPayoff at h ⊢
  simp only [Fin.sum_univ_two] at h ⊢
  linarith

lemma b_mono (hM : IsAdmissible M) (x x' : Fin 2 → ℝ≥0) (h : ∀ i, x i ≤ x' i) :
    buyerPayoff M x ≤ buyerPayoff M x' := by
  have h1 := ic_rearr M hM.2.1 x' x
  simp only [Fin.sum_univ_two] at h1
  have e0 : ((x 0 : ℝ) - x' 0) ≤ 0 := by have := h 0; simp only [sub_nonpos]; exact_mod_cast this
  have e1 : ((x 1 : ℝ) - x' 1) ≤ 0 := by have := h 1; simp only [sub_nonpos]; exact_mod_cast this
  have q0 := (hM.1 x 0).1
  have q1 := (hM.1 x 1).1
  nlinarith [mul_nonpos_of_nonneg_of_nonpos q0 e0, mul_nonpos_of_nonneg_of_nonpos q1 e1]

lemma b_lip (hM : IsAdmissible M) (x x' : Fin 2 → ℝ≥0) :
    |buyerPayoff M x - buyerPayoff M x'| ≤ |(x 0 : ℝ) - x' 0| + |(x 1 : ℝ) - x' 1| := by
  have h1 := ic_rearr M hM.2.1 x x'
  have h2 := ic_rearr M hM.2.1 x' x
  simp only [Fin.sum_univ_two] at h1 h2
  obtain ⟨a0, b0⟩ := hM.1 x 0
  obtain ⟨a1, b1⟩ := hM.1 x 1
  obtain ⟨c0, d0⟩ := hM.1 x' 0
  obtain ⟨c1, d1⟩ := hM.1 x' 1
  have k1 : M.q x' 0 * ((x' 0 : ℝ) - x 0) ≤ |(x 0 : ℝ) - x' 0| := by
    rw [abs_sub_comm]
    calc _ ≤ |M.q x' 0 * ((x' 0 : ℝ) - x 0)| := le_abs_self _
      _ = |M.q x' 0| * |(x' 0 : ℝ) - x 0| := abs_mul _ _
      _ ≤ 1 * |(x' 0 : ℝ) - x 0| := by
          apply mul_le_mul_of_nonneg_right _ (abs_nonneg _); rw [abs_of_nonneg c0]; exact d0
      _ = _ := one_mul _
  have k2 : M.q x' 1 * ((x' 1 : ℝ) - x 1) ≤ |(x 1 : ℝ) - x' 1| := by
    rw [abs_sub_comm]
    calc _ ≤ |M.q x' 1 * ((x' 1 : ℝ) - x 1)| := le_abs_self _
      _ = |M.q x' 1| * |(x' 1 : ℝ) - x 1| := abs_mul _ _
      _ ≤ 1 * |(x' 1 : ℝ) - x 1| := by
          apply mul_le_mul_of_nonneg_right _ (abs_nonneg _); rw [abs_of_nonneg c1]; exact d1
      _ = _ := one_mul _
  have k3 : M.q x 0 * ((x 0 : ℝ) - x' 0) ≤ |(x 0 : ℝ) - x' 0| := by
    calc _ ≤ |M.q x 0 * ((x 0 : ℝ) - x' 0)| := le_abs_self _
      _ = |M.q x 0| * |(x 0 : ℝ) - x' 0| := abs_mul _ _
      _ ≤ 1 * |(x 0 : ℝ) - x' 0| := by
          apply mul_le_mul_of_nonneg_right _ (abs_nonneg _); rw [abs_of_nonneg a0]; exact b0
      _ = _ := one_mul _
  have k4 : M.q x 1 * ((x 1 : ℝ) - x' 1) ≤ |(x 1 : ℝ) - x' 1| := by
    calc _ ≤ |M.q x 1 * ((x 1 : ℝ) - x' 1)| := le_abs_self _
      _ = |M.q x 1| * |(x 1 : ℝ) - x' 1| := abs_mul _ _
      _ ≤ 1 * |(x 1 : ℝ) - x' 1| := by
          apply mul_le_mul_of_nonneg_right _ (abs_nonneg _); rw [abs_of_nonneg a1]; exact b1
      _ = _ := one_mul _
  rw [abs_le]
  constructor <;> linarith

lemma b_cont (hM : IsAdmissible M) : Continuous (buyerPayoff M) := by
  refine (LipschitzWith.of_dist_le_mul (K := 2) fun x x' => ?_).continuous
  rw [Real.dist_eq]
  refine (b_lip M hM x x').trans ?_
  have h0 : |(x 0 : ℝ) - x' 0| ≤ dist x x' := by
    rw [← NNReal.dist_eq]; exact dist_le_pi_dist x x' 0
  have h1 : |(x 1 : ℝ) - x' 1| ≤ dist x x' := by
    rw [← NNReal.dist_eq]; exact dist_le_pi_dist x x' 1
  push_cast
  linarith

lemma b_meas (hM : IsAdmissible M) : Measurable (buyerPayoff M) := (b_cont M hM).measurable

/-- Upper Lipschitz bound in the increasing direction. -/
lemma b_lip_up (hM : IsAdmissible M) (x x' : Fin 2 → ℝ≥0) (h : ∀ i, x i ≤ x' i) :
    buyerPayoff M x' ≤ buyerPayoff M x + (((x' 0 : ℝ) - x 0) + ((x' 1 : ℝ) - x 1)) := by
  have := b_lip M hM x' x
  have e0 : (x 0 : ℝ) ≤ x' 0 := by exact_mod_cast h 0
  have e1 : (x 1 : ℝ) ≤ x' 1 := by exact_mod_cast h 1
  rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ x' 0 - x 0),
    abs_of_nonneg (by linarith : (0:ℝ) ≤ x' 1 - x 1)] at this
  linarith [le_abs_self (buyerPayoff M x' - buyerPayoff M x)]

lemma b_swap (hsym : IsSymmetric M) (x : Fin 2 → ℝ≥0) :
    buyerPayoff M (swap2 x) = buyerPayoff M x := by
  obtain ⟨hq, hs⟩ := hsym x
  obtain ⟨hq', _⟩ := hsym (swap2 x)
  have hss : swap2 (swap2 x) = x := by
    funext i; simp [swap2, Function.comp, Equiv.swap_apply_self]
  rw [hss] at hq'
  unfold buyerPayoff
  simp only [Fin.sum_univ_two]
  have e0 : swap2 x 0 = x 1 := by simp [swap2]
  have e1 : swap2 x 1 = x 0 := by simp [swap2]
  rw [e0, e1, ← hq, hq', ← hs]
  ring

/-- `t ↦ q₁(t − a, a)` is nondecreasing. -/
lemma Q_mono (hM : IsAdmissible M) (a : ℝ≥0) :
    Monotone (fun t : ℝ≥0 => M.q ![t - a, a] 0) := by
  intro t t' htt
  have ht : t - a ≤ t' - a := tsub_le_tsub_right htt a
  have h1 := ic_rearr M hM.2.1 ![t - a, a] ![t' - a, a]
  have h2 := ic_rearr M hM.2.1 ![t' - a, a] ![t - a, a]
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, sub_self,
    mul_zero, add_zero] at h1 h2
  have hlt : ((t - a : ℝ≥0) : ℝ) ≤ ((t' - a : ℝ≥0) : ℝ) := by exact_mod_cast ht
  rcases eq_or_lt_of_le hlt with h | h
  · have : t - a = t' - a := by exact_mod_cast h
    simp only [this]; exact le_rfl
  · by_contra hc
    push Not at hc
    nlinarith

end A

/-! ### Part C: condition (9) -/

section C
variable (a : ℝ) (ha : 0 < a) (f : ℝ → ℝ) (hf_nonneg : ∀ x, 0 ≤ f x)
    (hf_diff : ∀ x, a < x → DifferentiableAt ℝ f x)
    (h9 : ∀ x, a < x → x * deriv f x + 3 / 2 * f x ≤ 0)

include ha hf_nonneg hf_diff h9 in
/-- (9) says that `x³ f(x)²` (equivalently `x^{3/2} f(x)`) is nonincreasing on `(a, ∞)`. -/
lemma k_anti : AntitoneOn (fun x => x ^ 3 * f x ^ 2) (Set.Ioi a) := by
  have hd : ∀ x, a < x → HasDerivAt (fun x => x ^ 3 * f x ^ 2)
      (((3 : ℕ) : ℝ) * x ^ (3 - 1) * f x ^ 2 + x ^ 3 * (((2 : ℕ) : ℝ) * f x ^ (2 - 1) * deriv f x)) x :=
    fun x hx => (hasDerivAt_pow 3 x).mul ((hf_diff x hx).hasDerivAt.pow 2)
  apply antitoneOn_of_deriv_nonpos (convex_Ioi a)
  · intro x hx; exact (hd x hx).continuousAt.continuousWithinAt
  · rw [interior_Ioi]; intro x hx; exact (hd x hx).differentiableAt.differentiableWithinAt
  · rw [interior_Ioi]
    intro x hx
    rw [(hd x hx).deriv]
    have hx' : a < x := hx
    have h9x := h9 x hx'
    have hfx := hf_nonneg x
    have hx0 : 0 < x := ha.trans hx'
    norm_num
    have : x ^ 2 * f x * (2 * (x * deriv f x + 3 / 2 * f x)) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith)
    nlinarith [this]

include ha hf_nonneg hf_diff h9 in
lemma f_scale (c : ℝ) (hc : 1 ≤ c) (u : ℝ) (hu : c ^ 2 * a < u) : c ^ 3 * f u ≤ f (u / c ^ 2) := by
  have hc0 : 0 < c := by linarith
  have hc2 : 0 < c ^ 2 := by positivity
  set w := u / c ^ 2 with hw
  have hwa : a < w := by rw [hw, lt_div_iff₀ hc2]; linarith
  have huw : u = c ^ 2 * w := by rw [hw]; field_simp
  have hle : w ≤ u := by
    rw [huw]; have : 1 ≤ c ^ 2 := by nlinarith
    nlinarith [ha.trans hwa]
  have hk := k_anti a ha f hf_nonneg hf_diff h9 hwa (hwa.trans_le hle) hle
  simp only at hk
  rw [huw] at hk
  have hw0 : 0 < w := ha.trans hwa
  have h1 : (c ^ 3 * f u) ^ 2 ≤ f w ^ 2 := by
    rw [← huw] at hk
    have e : u ^ 3 * f u ^ 2 = w ^ 3 * (c ^ 3 * f u) ^ 2 := by rw [huw]; ring
    rw [e] at hk
    have hw3 : 0 < w ^ 3 := by positivity
    exact le_of_mul_le_mul_left (by linarith) hw3
  exact (pow_le_pow_iff_left₀ (by have := hf_nonneg u; positivity) (hf_nonneg w) two_ne_zero).1 h1

end C

/-! ### Part D: scaling inequalities for the law with density `f` -/

section D
variable (a : ℝ) (f : ℝ → ℝ) (hf_meas : Measurable f) (hf_nonneg : ∀ x, 0 ≤ f x)

lemma toNNReal_scale (c : ℝ≥0) (hc : 0 < c) (u : ℝ) :
    c ^ 2 * Real.toNNReal ((((c : ℝ) ^ 2)⁻¹) * u) = Real.toNNReal u := by
  have hc2 : (0 : ℝ) < (c : ℝ) ^ 2 := by positivity
  ext
  push_cast
  rcases le_total 0 u with h | h
  · rw [Real.coe_toNNReal _ (by positivity), Real.coe_toNNReal _ h]
    field_simp
  · rw [Real.toNNReal_of_nonpos (mul_nonpos_of_nonneg_of_nonpos (by positivity) h),
      Real.toNNReal_of_nonpos h]
    simp

include hf_meas in
lemma scale1 (c : ℝ≥0) (hc : 1 ≤ c)
    (hscale : ∀ u : ℝ, (c : ℝ) ^ 2 * a < u → (c : ℝ) ^ 3 * f u ≤ f (u / (c : ℝ) ^ 2))
    (ha : 0 < a) (ψ : ℝ≥0 → ℝ≥0∞) (hψ : Measurable ψ) :
    ENNReal.ofReal c * ∫⁻ x, (Set.Ioi (c ^ 2 * a.toNNReal)).indicator ψ x ∂(densityLaw f) ≤
      ∫⁻ x, ψ (c ^ 2 * x) ∂(densityLaw f) := by
  have hc0 : 0 < c := lt_of_lt_of_le zero_lt_one hc
  have hc2 : (0 : ℝ) < (c : ℝ) ^ 2 := by positivity
  have hF : Measurable (fun x => ENNReal.ofReal (f x)) := ENNReal.measurable_ofReal.comp hf_meas
  have hψ2 : Measurable (fun x : ℝ≥0 => ψ (c ^ 2 * x)) := hψ.comp (measurable_const_mul _)
  have hψi : Measurable ((Set.Ioi (c ^ 2 * a.toNNReal)).indicator ψ) :=
    hψ.indicator measurableSet_Ioi
  have m1 : Measurable (fun y : ℝ => ψ (c ^ 2 * y.toNNReal)) := hψ2.comp measurable_real_toNNReal
  have m2 : Measurable (fun y : ℝ => (Set.Ioi (c ^ 2 * a.toNNReal)).indicator ψ y.toNNReal) :=
    hψi.comp measurable_real_toNNReal
  unfold densityLaw
  rw [lintegral_map hψ2 measurable_real_toNNReal, lintegral_map hψi measurable_real_toNNReal,
    lintegral_withDensity_eq_lintegral_mul _ hF m1, lintegral_withDensity_eq_lintegral_mul _ hF m2]
  -- change of variables `y = u / c²`
  set G : ℝ → ℝ≥0∞ := fun y => ENNReal.ofReal (f y) * ψ (c ^ 2 * Real.toNNReal y) with hG
  have hGm : Measurable G := hF.mul (hψ2.comp measurable_real_toNNReal)
  have hH : Measurable (fun u : ℝ => G (((c : ℝ) ^ 2)⁻¹ * u)) := hGm.comp (measurable_const_mul _)
  have hsub : ∫⁻ y, G y = ENNReal.ofReal (((c : ℝ) ^ 2)⁻¹) * ∫⁻ u, G (((c : ℝ) ^ 2)⁻¹ * u) := by
    have hm := Real.map_volume_mul_left (a := (c : ℝ) ^ 2) hc2.ne'
    have e1 : ∫⁻ y, G y = ∫⁻ y, G (((c : ℝ) ^ 2)⁻¹ * ((c : ℝ) ^ 2 * y)) := by
      congr 1; funext y; rw [← mul_assoc, inv_mul_cancel₀ hc2.ne', one_mul]
    rw [e1, ← lintegral_map hH (measurable_const_mul _), hm, lintegral_smul_measure,
      abs_of_pos (inv_pos.2 hc2)]
    rfl
  show ENNReal.ofReal c * ∫⁻ y, (fun x => ENNReal.ofReal (f x)) y *
      ((Set.Ioi (c ^ 2 * a.toNNReal)).indicator ψ) (Real.toNNReal y) ≤ ∫⁻ y, G y
  rw [hsub]
  refine le_trans (le_of_eq (lintegral_const_mul _ (hF.mul m2)).symm) ?_
  refine le_trans ?_ (le_of_eq (lintegral_const_mul _ hH))
  refine lintegral_mono fun u => ?_
  simp only [hG]
  rw [toNNReal_scale c hc0 u]
  simp only [Pi.mul_apply]
  by_cases hu : Real.toNNReal u ∈ Set.Ioi (c ^ 2 * a.toNNReal)
  · rw [Set.indicator_of_mem hu]
    have hu' : (c : ℝ) ^ 2 * a < u := by
      have h1 : c ^ 2 * a.toNNReal < Real.toNNReal u := hu
      have h2 : ((c ^ 2 * a.toNNReal : ℝ≥0) : ℝ) < ((Real.toNNReal u : ℝ≥0) : ℝ) := by exact_mod_cast h1
      have hu0 : 0 < u := by
        by_contra hh; push Not at hh; rw [Real.toNNReal_of_nonpos hh] at h1; simp at h1
      push_cast at h2
      rwa [Real.coe_toNNReal _ ha.le, Real.coe_toNNReal _ hu0.le] at h2
    have key := hscale u hu'
    rw [← mul_assoc, ← mul_assoc]
    refine mul_le_mul_left ?_ _
    rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    have : ((c : ℝ) ^ 2)⁻¹ * f (u / (c : ℝ) ^ 2) ≥ ((c : ℝ) ^ 2)⁻¹ * ((c : ℝ) ^ 3 * f u) :=
      mul_le_mul_of_nonneg_left key (by positivity)
    have e : ((c : ℝ) ^ 2)⁻¹ * ((c : ℝ) ^ 3 * f u) = (c : ℝ) * f u := by
      field_simp
    have e2 : u / (c : ℝ) ^ 2 = ((c : ℝ) ^ 2)⁻¹ * u := by ring
    rw [e2] at this
    linarith
  · rw [Set.indicator_of_notMem hu]
    simp

end D

section D2
variable (a : ℝ) (f : ℝ → ℝ) (hf_meas : Measurable f)

/-- `(x, y) ↦ ![x, y]` through the measurable equivalence. -/
noncomputable abbrev P (x y : ℝ≥0) : Fin 2 → ℝ≥0 :=
  (MeasurableEquiv.finTwoArrow (α := ℝ≥0)).symm (x, y)

lemma P0 (x y : ℝ≥0) : P x y 0 = x := rfl
lemma P1 (x y : ℝ≥0) : P x y 1 = y := rfl

lemma P_smul (r x y : ℝ≥0) : r • P x y = P (r * x) (r * y) := by
  funext i; fin_cases i <;> rfl

lemma P_eta (x : Fin 2 → ℝ≥0) : P (x 0) (x 1) = x := by
  funext i; fin_cases i <;> rfl

lemma lintegral_pi_two (ν : Measure ℝ≥0) [IsFiniteMeasure ν] (Φ : (Fin 2 → ℝ≥0) → ℝ≥0∞)
    (hΦ : Measurable Φ) :
    ∫⁻ x, Φ x ∂(Measure.pi fun _ : Fin 2 => ν) = ∫⁻ x, ∫⁻ y, Φ (P x y) ∂ν ∂ν := by
  have hmp := MeasurePreserving.symm _ (measurePreserving_finTwoArrow ν)
  rw [← hmp.lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _) Φ]
  exact lintegral_prod (fun p => Φ (P p.1 p.2)) (hΦ.comp (MeasurableEquiv.measurable _)).aemeasurable

include hf_meas in
lemma scale2 [IsFiniteMeasure (densityLaw f)] (c : ℝ≥0) (hc : 1 ≤ c)
    (hscale : ∀ u : ℝ, (c : ℝ) ^ 2 * a < u → (c : ℝ) ^ 3 * f u ≤ f (u / (c : ℝ) ^ 2))
    (ha : 0 < a) (φ : (Fin 2 → ℝ≥0) → ℝ≥0∞) (hφ : Measurable φ) :
    ENNReal.ofReal c * ENNReal.ofReal c *
        ∫⁻ x, {x : Fin 2 → ℝ≥0 | c ^ 2 * a.toNNReal < x 0 ∧ c ^ 2 * a.toNNReal < x 1}.indicator φ x
          ∂(Measure.pi fun _ : Fin 2 => densityLaw f) ≤
      ∫⁻ x, φ (c ^ 2 • x) ∂(Measure.pi fun _ : Fin 2 => densityLaw f) := by
  set ν := densityLaw f
  set S := Set.Ioi (c ^ 2 * a.toNNReal)
  have hPm : Measurable (fun p : ℝ≥0 × ℝ≥0 => P p.1 p.2) := MeasurableEquiv.measurable _
  set Cs := {x : Fin 2 → ℝ≥0 | c ^ 2 * a.toNNReal < x 0 ∧ c ^ 2 * a.toNNReal < x 1} with hCs
  have hcore : MeasurableSet {x : Fin 2 → ℝ≥0 | c ^ 2 * a.toNNReal < x 0 ∧ c ^ 2 * a.toNNReal < x 1} :=
    (measurableSet_lt measurable_const (by fun_prop)).inter
      (measurableSet_lt measurable_const (by fun_prop))
  rw [lintegral_pi_two ν _ (hφ.indicator hcore),
    lintegral_pi_two ν (fun x => φ (c ^ 2 • x)) (hφ.comp (measurable_const_smul _))]
  -- the inner function
  set F : ℝ≥0 × ℝ≥0 → ℝ≥0∞ := fun p => S.indicator (fun y => φ (P p.1 y)) p.2 with hF
  have hFm : Measurable F := by
    have : F = (Prod.snd ⁻¹' S).indicator (fun p => φ (P p.1 p.2)) := by
      funext p; simp [hF, Set.indicator]
    rw [this]
    exact (hφ.comp hPm).indicator (measurable_snd measurableSet_Ioi)
  set J : ℝ≥0 → ℝ≥0∞ := fun x => ∫⁻ y, F (x, y) ∂ν with hJ
  have hJm : Measurable J := hFm.lintegral_prod_right'
  have step1 : ∀ x, ENNReal.ofReal c * J (c ^ 2 * x) ≤ ∫⁻ y, φ (c ^ 2 • P x y) ∂ν := by
    intro x
    have := scale1 a f hf_meas c hc hscale ha (fun y => φ (P (c ^ 2 * x) y))
      (hφ.comp (hPm.comp (measurable_const.prodMk measurable_id)))
    simp only [P_smul]
    exact this
  calc ENNReal.ofReal c * ENNReal.ofReal c *
        ∫⁻ x, ∫⁻ y, {x : Fin 2 → ℝ≥0 | c ^ 2 * a.toNNReal < x 0 ∧ c ^ 2 * a.toNNReal < x 1}.indicator
          φ (P x y) ∂ν ∂ν
      = ENNReal.ofReal c * (ENNReal.ofReal c * ∫⁻ x, S.indicator J x ∂ν) := by
        rw [mul_assoc]
        congr 2
        refine lintegral_congr fun x => ?_
        by_cases hx : x ∈ S
        · rw [Set.indicator_of_mem hx]
          refine lintegral_congr fun y => ?_
          by_cases hy : y ∈ S
          · rw [Set.indicator_of_mem (show P x y ∈ Cs from ⟨hx, hy⟩)]
            simp [hF, Set.indicator_of_mem hy]
          · rw [Set.indicator_of_notMem (show P x y ∉ Cs from fun h => hy h.2)]
            simp [hF, Set.indicator_of_notMem hy]
        · rw [Set.indicator_of_notMem hx]
          have hn : ∀ y, P x y ∉ Cs := fun y h => hx h.1
          rw [lintegral_congr fun y => Set.indicator_of_notMem (hn y) φ, lintegral_zero]
    _ ≤ ENNReal.ofReal c * ∫⁻ x, J (c ^ 2 * x) ∂ν := by
        gcongr
        exact scale1 a f hf_meas c hc hscale ha J hJm
    _ = ∫⁻ x, ENNReal.ofReal c * J (c ^ 2 * x) ∂ν :=
        (lintegral_const_mul _ (hJm.comp (measurable_const_mul _))).symm
    _ ≤ ∫⁻ x, ∫⁻ y, φ (c ^ 2 • P x y) ∂ν ∂ν := lintegral_mono step1

end D2

/-! ### Part F: pointwise inequalities -/

section F
variable (M : Mechanism (Fin 2)) (a : ℝ≥0)

/-- `b̂(x) = b(x₀ + x₁ − a, a)`. -/
noncomputable def bh (x : Fin 2 → ℝ≥0) : ℝ := buyerPayoff M ![x 0 + x 1 - a, a]

/-- `Q(t) = q₁(t − a, a)`. -/
noncomputable def Qf (t : ℝ≥0) : ℝ := M.q ![t - a, a] 0

lemma vec_eta (x : Fin 2 → ℝ≥0) : ![x 0, x 1] = x := by
  funext i; fin_cases i <;> rfl

lemma payoff_B (x : Fin 2 → ℝ≥0) : buyerPayoff (bundledMajorant M a) x = bh M a x := by
  unfold buyerPayoff bh bundledMajorant
  simp only
  ring

lemma s_B (x : Fin 2 → ℝ≥0) :
    (bundledMajorant M a).s x = Qf M a (x 0 + x 1) * ((x 0 : ℝ) + x 1) - bh M a x := by
  unfold bh Qf bundledMajorant
  simp only [Fin.sum_univ_two]
  ring

lemma q_B (x : Fin 2 → ℝ≥0) (i : Fin 2) : (bundledMajorant M a).q x i = Qf M a (x 0 + x 1) := rfl

lemma F1 (hIC : IsIC M) (l : ℝ≥0) (x : Fin 2 → ℝ≥0) :
    ((l : ℝ) - 1) * M.s x + l * buyerPayoff M x ≤ buyerPayoff M (l • x) := by
  have h := hIC (l • x) x
  unfold buyerPayoff at h ⊢
  simp only [Fin.sum_univ_two, Pi.smul_apply, smul_eq_mul, NNReal.coe_mul] at h ⊢
  nlinarith [h]

lemma F2 (hM : IsAdmissible M) (hsym : IsSymmetric M) (l : ℝ≥0) (hl : 1 ≤ l)
    (x : Fin 2 → ℝ≥0) (hx : ∀ i, a ≤ x i) :
    bh M a (l • x) ≤ bh M a x + ((l : ℝ) - 1) * Qf M a (l * (x 0 + x 1)) * ((x 0 : ℝ) + x 1) := by
  obtain ⟨_, hIC2, _, _⟩ := bundled_majorant_ic_ir M hM hsym a
  have hlx : ∀ i, a ≤ (l • x) i := fun i => by
    simp only [Pi.smul_apply, smul_eq_mul]
    calc a ≤ x i := hx i
      _ = 1 * x i := (one_mul _).symm
      _ ≤ l * x i := mul_le_mul_of_nonneg_right hl (by simp)
  have h := hIC2 x (l • x) hx hlx
  rw [payoff_B, s_B] at h
  simp only [q_B, Fin.sum_univ_two, Pi.smul_apply, smul_eq_mul, NNReal.coe_mul] at h
  have e : l * x 0 + l * x 1 = l * (x 0 + x 1) := (mul_add _ _ _).symm
  rw [e] at h
  push_cast at h
  nlinarith [h]

lemma F3 (hIC : IsIC M) (hsym : IsSymmetric M) (x : Fin 2 → ℝ≥0) (hx : ∀ i, a ≤ x i) :
    buyerPayoff M x ≤ bh M a x := by
  have := display_18 M hIC hsym a (x 0) (x 1) (hx 0) (hx 1)
  rwa [vec_eta] at this

lemma F4 (hM : IsAdmissible M) (hsym : IsSymmetric M) (x : Fin 2 → ℝ≥0) (hx : ∀ i, a ≤ x i)
    (r : ℝ≥0) (hr : x 0 ≤ r ∨ x 1 ≤ r) :
    bh M a x - buyerPayoff M x ≤ (r : ℝ) - a := by
  have h0 : (a : ℝ) ≤ x 0 := by exact_mod_cast hx 0
  have h1 : (a : ℝ) ≤ x 1 := by exact_mod_cast hx 1
  have hT : ((x 0 + x 1 - a : ℝ≥0) : ℝ) = (x 0 : ℝ) + x 1 - a := by
    rw [NNReal.coe_sub (le_trans (hx 0) le_self_add)]; push_cast; ring
  rcases hr with hr | hr
  · -- use symmetry: `b̂(x) = b(a, x₀ + x₁ − a)`
    have hs : bh M a x = buyerPayoff M ![a, x 0 + x 1 - a] := by
      unfold bh
      rw [← b_swap M hsym ![x 0 + x 1 - a, a]]
      congr 1
      funext i; fin_cases i <;> rfl
    have hup := b_lip_up M hM ![a, x 1] ![a, x 0 + x 1 - a] (by
      intro i; fin_cases i
      · exact le_rfl
      · show x 1 ≤ x 0 + x 1 - a
        exact le_tsub_of_add_le_left (add_le_add (hx 0) le_rfl))
    have hmono := b_mono M hM ![a, x 1] x (by
      intro i; fin_cases i
      · exact hx 0
      · exact le_rfl)
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hup
    rw [hT] at hup
    have hr' : (x 0 : ℝ) ≤ r := by exact_mod_cast hr
    rw [hs]
    linarith
  · have hup := b_lip_up M hM ![x 0, a] ![x 0 + x 1 - a, a] (by
      intro i; fin_cases i
      · show x 0 ≤ x 0 + x 1 - a
        exact le_tsub_of_add_le_right (add_le_add le_rfl (hx 1))
      · exact le_rfl)
    have hmono := b_mono M hM ![x 0, a] x (by
      intro i; fin_cases i
      · exact le_rfl
      · exact hx 1)
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hup
    rw [hT] at hup
    have hr' : (x 1 : ℝ) ≤ r := by exact_mod_cast hr
    unfold bh
    linarith

lemma F5 (hM : IsAdmissible M) (hNPT : IsNPT M) (hsym : IsSymmetric M) (x : Fin 2 → ℝ≥0)
    (hx : ∀ i, a ≤ x i) : 0 ≤ (bundledMajorant M a).s x := by
  rw [s_B]
  set T := x 0 + x 1 with hTdef
  have haT : a + a ≤ T := add_le_add (hx 0) (hx 1)
  have haT' : a ≤ T := le_trans le_add_self haT
  set y : Fin 2 → ℝ≥0 := ![T - a, a] with hy
  have hic := ic_rearr M hM.2.1 ![a, a] y
  simp only [Fin.sum_univ_two, hy, Matrix.cons_val_zero, Matrix.cons_val_one, sub_self, mul_zero,
    add_zero] at hic
  have hQ : Qf M a T = M.q y 0 := rfl
  have hbh : bh M a x = buyerPayoff M y := rfl
  have hTa : ((T - a : ℝ≥0) : ℝ) = (T : ℝ) - a := NNReal.coe_sub haT'
  rw [hTa] at hic
  -- symmetry at `(a, a)`
  have hsa : swap2 ![a, a] = ![a, a] := by funext i; fin_cases i <;> rfl
  have hq2 : M.q ![a, a] 0 = M.q ![a, a] 1 := by have := (hsym ![a, a]).1; rwa [hsa] at this
  have hbaa : buyerPayoff M ![a, a] = 2 * a * M.q ![a, a] 0 - M.s ![a, a] := by
    unfold buyerPayoff; simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [← hq2]; ring
  -- monotonicity `Q(T) ≥ Q(2a) = q₁(a, a)`
  have hmono : M.q ![a, a] 0 ≤ Qf M a T := by
    have := Q_mono M hM a haT
    simp only at this
    have e : a + a - a = a := add_tsub_cancel_right a a
    rw [e] at this
    exact this
  have hs0 := hNPT ![a, a]
  have hTr : (T : ℝ) = (x 0 : ℝ) + x 1 := by rw [hTdef]; push_cast; ring
  have hTge : (2 : ℝ) * a ≤ T := by
    have : ((a + a : ℝ≥0) : ℝ) ≤ T := by exact_mod_cast haT
    push_cast at this
    linarith
  rw [← hTr, hbh]
  have hic' : buyerPayoff M y - buyerPayoff M ![a, a] ≤ Qf M a T * ((T : ℝ) - a - a) := hic
  rw [hbaa] at hic'
  have hQ0 : 0 ≤ Qf M a T := le_trans (hM.1 _ 0).1 hmono
  nlinarith

end F

/-! ### Part E: null sets for the law with density `f` -/

section E
variable (a : ℝ) (ha : 0 < a) (f : ℝ → ℝ) (hf_supp : ∀ x, x < a → f x = 0)

lemma densityLaw_prob (hf_mass : ∫⁻ x, ENNReal.ofReal (f x) = 1) :
    IsProbabilityMeasure (densityLaw f) := by
  constructor
  rw [densityLaw, Measure.map_apply measurable_real_toNNReal MeasurableSet.univ, Set.preimage_univ,
    withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, hf_mass]

include hf_supp in
lemma wd_Iio : (volume.withDensity (fun x => ENNReal.ofReal (f x))) (Set.Iio a) = 0 := by
  rw [withDensity_apply _ measurableSet_Iio,
    setLIntegral_congr_fun measurableSet_Iio (g := fun _ => 0) (fun x hx => by
      simp [hf_supp x hx])]
  simp

include ha hf_supp in
lemma densityLaw_Iio : densityLaw f (Set.Iio a.toNNReal) = 0 := by
  rw [densityLaw, Measure.map_apply measurable_real_toNNReal measurableSet_Iio]
  refine measure_mono_null (fun x hx => ?_) (wd_Iio a f hf_supp)
  have hx' : x.toNNReal < a.toNNReal := hx
  exact (Real.toNNReal_lt_toNNReal_iff ha).1 hx'

include ha hf_supp in
lemma densityLaw_singleton (t : ℝ≥0) : densityLaw f {t} = 0 := by
  rw [densityLaw, Measure.map_apply measurable_real_toNNReal (measurableSet_singleton t)]
  have hsub : Real.toNNReal ⁻¹' {t} ⊆ {(t : ℝ)} ∪ Set.Iio a := by
    intro y hy
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at hy
    by_cases hya : y < a
    · exact Or.inr hya
    · left
      push Not at hya
      have hy0 : 0 ≤ y := ha.le.trans hya
      simp only [Set.mem_singleton_iff]
      rw [← hy, Real.coe_toNNReal _ hy0]
  refine measure_mono_null hsub (measure_union_null ?_ (wd_Iio a f hf_supp))
  exact withDensity_absolutelyContinuous _ _ (Real.volume_singleton)

include ha hf_supp in
lemma densityLaw_noAtoms : NullSingletonClass (densityLaw f) := ⟨densityLaw_singleton a ha f hf_supp⟩

include ha hf_supp in
lemma densityLaw_Iic : densityLaw f (Set.Iic a.toNNReal) = 0 := by
  rw [← Set.Iio_union_right]
  exact measure_union_null (densityLaw_Iio a ha f hf_supp) (densityLaw_singleton a ha f hf_supp _)

include ha hf_supp in
lemma ae_quad [IsProbabilityMeasure (densityLaw f)] :
    ∀ᵐ x ∂(Measure.pi fun _ : Fin 2 => densityLaw f), ∀ i, a.toNNReal ≤ x i := by
  have h1 : ∀ᵐ t ∂(densityLaw f), a.toNNReal ≤ t := by
    rw [ae_iff]; simp only [not_le]; exact densityLaw_Iio a ha f hf_supp
  have h0 := (Measure.quasiMeasurePreserving_eval (fun _ : Fin 2 => densityLaw f) 0).ae h1
  have h1' := (Measure.quasiMeasurePreserving_eval (fun _ : Fin 2 => densityLaw f) 1).ae h1
  filter_upwards [h0, h1'] with x hx0 hx1
  intro i; fin_cases i
  · exact hx0
  · exact hx1

include ha hf_supp in
lemma sum_countable_null [IsProbabilityMeasure (densityLaw f)] (C : Set ℝ≥0) (hC : C.Countable) :
    (Measure.pi fun _ : Fin 2 => densityLaw f) {x | x 0 + x 1 ∈ C} = 0 := by
  haveI := densityLaw_noAtoms a ha f hf_supp
  have hA : MeasurableSet {x : Fin 2 → ℝ≥0 | x 0 + x 1 ∈ C} :=
    (by fun_prop : Measurable fun x : Fin 2 → ℝ≥0 => x 0 + x 1) hC.measurableSet
  rw [← lintegral_indicator_one hA, lintegral_pi_two _ _ (measurable_one.indicator hA)]
  refine lintegral_eq_zero_of_ae_eq_zero ?_ |>.trans (by simp)
  refine Filter.Eventually.of_forall fun x => ?_
  simp only [Pi.zero_apply]
  have hsub : {y : ℝ≥0 | x + y ∈ C} ⊆ (fun c => c - x) '' C := by
    intro y hy
    exact ⟨x + y, hy, add_tsub_cancel_left x y⟩
  have hnull : densityLaw f {y : ℝ≥0 | x + y ∈ C} = 0 :=
    measure_mono_null hsub ((hC.image _).measure_zero _)
  have hm : MeasurableSet {y : ℝ≥0 | x + y ∈ C} :=
    (by fun_prop : Measurable fun y : ℝ≥0 => x + y) hC.measurableSet
  rw [← lintegral_indicator_one hm] at hnull
  rw [← hnull]
  rfl

lemma pi_coord_le [IsProbabilityMeasure (densityLaw f)] (r : ℝ≥0) (i : Fin 2) :
    (Measure.pi fun _ : Fin 2 => densityLaw f) {x | x i ≤ r} = densityLaw f (Set.Iic r) := by
  have : {x : Fin 2 → ℝ≥0 | x i ≤ r} =
      Set.univ.pi (fun j => if j = i then Set.Iic r else Set.univ) := by
    ext x; simp only [Set.mem_setOf_eq, Set.mem_pi, Set.mem_univ, true_implies]
    constructor
    · intro h j; split_ifs with hj
      · subst hj; exact h
      · trivial
    · intro h; simpa using h i
  rw [this, Measure.pi_pi]
  rw [Finset.prod_eq_single i]
  · simp
  · intro j _ hj; simp [hj]
  · simp

lemma core_compl_le [IsProbabilityMeasure (densityLaw f)] (r : ℝ≥0) :
    (Measure.pi fun _ : Fin 2 => densityLaw f) {x | ¬ (r < x 0 ∧ r < x 1)} ≤
      densityLaw f (Set.Iic r) + densityLaw f (Set.Iic r) := by
  have : {x : Fin 2 → ℝ≥0 | ¬ (r < x 0 ∧ r < x 1)} = {x | x 0 ≤ r} ∪ {x | x 1 ≤ r} := by
    ext x; simp only [Set.mem_setOf_eq, Set.mem_union, not_and_or, not_lt]
  rw [this]
  refine (measure_union_le _ _).trans ?_
  rw [pi_coord_le f r 0, pi_coord_le f r 1]

end E

/-! ### Part G: the truncated comparison `r_K(b) ≤ r_K(b̂)` -/

section G

/-- The box `[0, K]²`. -/
def box (K : ℝ≥0) : Set (Fin 2 → ℝ≥0) := {x | x 0 ≤ K ∧ x 1 ≤ K}

lemma box_meas (K : ℝ≥0) : MeasurableSet (box K) :=
  (measurableSet_le (by fun_prop) measurable_const).inter
    (measurableSet_le (by fun_prop) measurable_const)

lemma vec_meas (a : ℝ≥0) : Measurable (fun x : Fin 2 → ℝ≥0 => ![x 0 + x 1 - a, a]) := by
  refine measurable_pi_iff.2 fun i => ?_
  fin_cases i
  · simp only [Fin.zero_eta, Matrix.cons_val_zero]; fun_prop
  · simp only [Fin.mk_one, Matrix.cons_val_one]; exact measurable_const

lemma bh_meas (M : Mechanism (Fin 2)) (hM : IsAdmissible M) (a : ℝ≥0) : Measurable (bh M a) :=
  (b_meas M hM).comp (vec_meas a)

lemma Qf_meas (M : Mechanism (Fin 2)) (hM : IsAdmissible M) (a : ℝ≥0) : Measurable (Qf M a) :=
  (Q_mono M hM a).measurable

lemma bh_bound (M : Mechanism (Fin 2)) (hM : IsAdmissible M) (a : ℝ≥0) (x : Fin 2 → ℝ≥0) :
    bh M a x ≤ |buyerPayoff M 0| + ((x 0 : ℝ) + x 1) + a := by
  have h := b_lip M hM ![x 0 + x 1 - a, a] 0
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Pi.zero_apply, NNReal.coe_zero,
    sub_zero] at h
  have e1 : ((x 0 + x 1 - a : ℝ≥0) : ℝ) ≤ (x 0 : ℝ) + x 1 := by
    have : x 0 + x 1 - a ≤ x 0 + x 1 := tsub_le_self
    exact_mod_cast this
  rw [abs_of_nonneg (NNReal.coe_nonneg _), abs_of_nonneg (NNReal.coe_nonneg _)] at h
  unfold bh
  have := le_abs_self (buyerPayoff M ![x 0 + x 1 - a, a] - buyerPayoff M 0)
  have := neg_abs_le (buyerPayoff M 0)
  linarith [le_abs_self (buyerPayoff M 0)]

variable (M : Mechanism (Fin 2)) (hM : IsAdmissible M) (hNPT : IsNPT M) (hsym : IsSymmetric M)
  (a : ℝ) (ha : 0 < a) (f : ℝ → ℝ) (hf_meas : Measurable f) (hf_supp : ∀ x, x < a → f x = 0)

include hM hNPT hsym ha hf_meas hf_supp in
lemma box_ineq [IsProbabilityMeasure (densityLaw f)] (K c : ℝ≥0) (hc : 1 < c)
    (hscale : ∀ u : ℝ, (c : ℝ) ^ 2 * a < u → (c : ℝ) ^ 3 * f u ≤ f (u / (c : ℝ) ^ 2)) :
    ∫⁻ x in box K, ENNReal.ofReal (M.s x) ∂(Measure.pi fun _ : Fin 2 => densityLaw f) +
        ∫⁻ x in box K, ENNReal.ofReal (bh M a.toNNReal x) ∂(Measure.pi fun _ : Fin 2 => densityLaw f) ≤
      ∫⁻ x in box K, ENNReal.ofReal (Qf M a.toNNReal (c ^ 2 * (x 0 + x 1)) * ((x 0 : ℝ) + x 1))
          ∂(Measure.pi fun _ : Fin 2 => densityLaw f) +
        ENNReal.ofReal ((c : ℝ) ^ 2) * ENNReal.ofReal a *
          (Measure.pi fun _ : Fin 2 => densityLaw f)
            {x | ¬ (c ^ 2 * a.toNNReal < x 0 ∧ c ^ 2 * a.toNNReal < x 1)} := by
  set μ := Measure.pi fun _ : Fin 2 => densityLaw f with hμ
  set a' := a.toNNReal with ha'
  have ha'r : (a' : ℝ) = a := Real.coe_toNNReal _ ha.le
  set l : ℝ≥0 := c ^ 2 with hl
  have hl1 : 1 < l := one_lt_pow₀ hc two_ne_zero
  have hlr : (l : ℝ) = (c : ℝ) ^ 2 := by rw [hl]; push_cast; ring
  set e : ℝ := (l : ℝ) - 1 with he
  have he0 : 0 < e := by rw [he]; have : (1 : ℝ) < l := by exact_mod_cast hl1
                         linarith
  set Cs := {x : Fin 2 → ℝ≥0 | ¬ (l * a' < x 0 ∧ l * a' < x 1)} with hCs
  set Core := {x : Fin 2 → ℝ≥0 | l * a' < x 0 ∧ l * a' < x 1} with hCore
  have hCoreM : MeasurableSet Core :=
    (measurableSet_lt measurable_const (by fun_prop)).inter
      (measurableSet_lt measurable_const (by fun_prop))
  have hCsM : MeasurableSet Cs := hCoreM.compl
  set D := box K with hD
  have hDm : MeasurableSet D := box_meas K
  have hquad : ∀ᵐ x ∂μ, ∀ i, a' ≤ x i := ae_quad a ha f hf_supp
  have hquadD : ∀ᵐ x ∂(μ.restrict D), ∀ i, a' ≤ x i := ae_restrict_of_ae hquad
  -- measurability
  have ms : Measurable M.s := hM.2.2.2
  have mb : Measurable (buyerPayoff M) := b_meas M hM
  have mbh : Measurable (bh M a') := bh_meas M hM a'
  have msm : Measurable (fun x : Fin 2 → ℝ≥0 => l • x) := measurable_const_smul l
  have mQT : Measurable (fun x : Fin 2 → ℝ≥0 => Qf M a' (l * (x 0 + x 1)) * ((x 0 : ℝ) + x 1)) :=
    ((Qf_meas M hM a').comp (by fun_prop)).mul (by fun_prop)
  have hquad_l : ∀ x : Fin 2 → ℝ≥0, (∀ i, a' ≤ x i) → ∀ i, a' ≤ (l • x) i := by
    intro x hx i
    simp only [Pi.smul_apply, smul_eq_mul]
    calc a' ≤ x i := hx i
      _ = 1 * x i := (one_mul _).symm
      _ ≤ l * x i := mul_le_mul_of_nonneg_right hl1.le (by simp)
  have hbnn : ∀ x, 0 ≤ buyerPayoff M x := hM.2.2.1
  have hbh_ge : ∀ x : Fin 2 → ℝ≥0, (∀ i, a' ≤ x i) → buyerPayoff M x ≤ bh M a' x :=
    fun x hx => F3 M a' hM.2.1 hsym x hx
  set g : (Fin 2 → ℝ≥0) → ℝ≥0∞ := fun x => ENNReal.ofReal (bh M a' x - buyerPayoff M x) with hg
  have mg : Measurable g := (mbh.sub mb).ennreal_ofReal
  have hEe : ENNReal.ofReal e ≠ 0 := (ENNReal.ofReal_pos.2 he0).ne'
  -- (1)
  have h1 : ENNReal.ofReal e * ∫⁻ x in D, ENNReal.ofReal (M.s x) ∂μ +
      ENNReal.ofReal l * ∫⁻ x in D, ENNReal.ofReal (buyerPayoff M x) ∂μ ≤
      ∫⁻ x in D, ENNReal.ofReal (buyerPayoff M (l • x)) ∂μ := by
    rw [← lintegral_const_mul _ ms.ennreal_ofReal, ← lintegral_const_mul _ mb.ennreal_ofReal,
      ← lintegral_add_left (ms.ennreal_ofReal.const_mul _)]
    refine lintegral_mono fun x => ?_
    rw [← ENNReal.ofReal_mul he0.le, ← ENNReal.ofReal_mul (NNReal.coe_nonneg _),
      ← ENNReal.ofReal_add (mul_nonneg he0.le (hNPT x)) (mul_nonneg (NNReal.coe_nonneg _) (hbnn x))]
    exact ENNReal.ofReal_le_ofReal (F1 M hM.2.1 l x)
  -- (2)
  have h2 : ∫⁻ x in D, ENNReal.ofReal (buyerPayoff M (l • x)) ∂μ +
      ∫⁻ x in D, g (l • x) ∂μ = ∫⁻ x in D, ENNReal.ofReal (bh M a' (l • x)) ∂μ := by
    have mbl : Measurable (fun x : Fin 2 → ℝ≥0 => ENNReal.ofReal (buyerPayoff M (l • x))) :=
      (mb.comp msm).ennreal_ofReal
    rw [← lintegral_add_left mbl]
    refine lintegral_congr_ae (hquadD.mono fun x hx => ?_)
    have hx' := hquad_l x hx
    simp only [hg]
    rw [← ENNReal.ofReal_add (hbnn _) (sub_nonneg.2 (hbh_ge _ hx'))]
    congr 1; ring
  -- (3)
  have h3 : ∫⁻ x in D, ENNReal.ofReal (bh M a' (l • x)) ∂μ ≤
      ∫⁻ x in D, ENNReal.ofReal (bh M a' x) ∂μ + ENNReal.ofReal e *
        ∫⁻ x in D, ENNReal.ofReal (Qf M a' (l * (x 0 + x 1)) * ((x 0 : ℝ) + x 1)) ∂μ := by
    rw [← lintegral_const_mul _ mQT.ennreal_ofReal, ← lintegral_add_left mbh.ennreal_ofReal]
    refine lintegral_mono_ae (hquadD.mono fun x hx => ?_)
    have hQ0 : 0 ≤ Qf M a' (l * (x 0 + x 1)) := (hM.1 _ 0).1
    have hT0 : (0 : ℝ) ≤ (x 0 : ℝ) + x 1 := by positivity
    rw [← ENNReal.ofReal_mul he0.le,
      ← ENNReal.ofReal_add ((hbnn x).trans (hbh_ge x hx)) (mul_nonneg he0.le (mul_nonneg hQ0 hT0))]
    refine ENNReal.ofReal_le_ofReal ?_
    have := F2 M a' hM hsym l hl1.le x hx
    rw [he]; linarith
  -- (4)
  have h4 : ENNReal.ofReal l * ∫⁻ x, Core.indicator (D.indicator g) x ∂μ ≤
      ∫⁻ x in D, g (l • x) ∂μ := by
    set φ := (box (l * K)).indicator g with hφ
    have hsc := scale2 a f hf_meas c hc.le hscale ha φ (mg.indicator (box_meas _))
    have eL : ENNReal.ofReal c * ENNReal.ofReal c = ENNReal.ofReal l := by
      rw [← ENNReal.ofReal_mul (NNReal.coe_nonneg _)]; congr 1; rw [hlr]; ring
    rw [eL] at hsc
    have eHl : ∫⁻ x, φ (c ^ 2 • x) ∂μ = ∫⁻ x in D, g (l • x) ∂μ := by
      rw [← lintegral_indicator hDm]
      refine lintegral_congr fun x => ?_
      have hiff : c ^ 2 • x ∈ box (l * K) ↔ x ∈ D := by
        simp only [hD, box, Set.mem_setOf_eq, Pi.smul_apply, smul_eq_mul, hl]
        have hc2 : 0 < c ^ 2 := by positivity
        rw [mul_le_mul_iff_right₀ hc2, mul_le_mul_iff_right₀ hc2]
      simp only [hφ]
      by_cases hx : x ∈ D
      · rw [Set.indicator_of_mem hx, Set.indicator_of_mem (hiff.2 hx)]
      · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem (fun h => hx (hiff.1 h))]
    rw [eHl] at hsc
    refine le_trans (mul_le_mul' le_rfl (lintegral_mono fun x => ?_)) hsc
    have hsub : D ⊆ box (l * K) := by
      intro y hy
      simp only [hD, box, Set.mem_setOf_eq] at hy ⊢
      have : K ≤ l * K := le_mul_of_one_le_left (by simp) hl1.le
      exact ⟨hy.1.trans this, hy.2.trans this⟩
    by_cases hx : x ∈ Core
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]
      exact Set.indicator_le_indicator_of_subset hsub (fun _ => by simp) x
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx]
  -- (5)
  have h5 : ∫⁻ x in D, g x ∂μ ≤ ∫⁻ x, Core.indicator (D.indicator g) x ∂μ +
      ENNReal.ofReal e * ENNReal.ofReal a' * μ Cs := by
    rw [← lintegral_indicator hDm]
    have hrhs : ∫⁻ x, Core.indicator (D.indicator g) x ∂μ +
        ENNReal.ofReal e * ENNReal.ofReal a' * μ Cs =
        ∫⁻ x, (Core.indicator (D.indicator g) x +
          ENNReal.ofReal e * ENNReal.ofReal a' * Cs.indicator 1 x) ∂μ := by
      rw [lintegral_add_left ((mg.indicator hDm).indicator hCoreM),
        lintegral_const_mul _ (measurable_one.indicator hCsM),
        lintegral_indicator_one hCsM]
    rw [hrhs]
    refine lintegral_mono_ae (hquad.mono fun x hx => ?_)
    by_cases hxc : x ∈ Core
    · rw [Set.indicator_of_mem hxc]; exact le_self_add
    · rw [Set.indicator_of_notMem hxc, zero_add, Set.indicator_of_mem (show x ∈ Cs from hxc),
        Pi.one_apply, mul_one]
      refine (Set.indicator_le_self _ _ x).trans ?_
      simp only [hg]
      rw [← ENNReal.ofReal_mul he0.le]
      refine ENNReal.ofReal_le_ofReal ?_
      have hor : x 0 ≤ l * a' ∨ x 1 ≤ l * a' := by
        by_contra hh; push Not at hh; exact hxc ⟨hh.1, hh.2⟩
      have := F4 M a' hM hsym x hx (l * a') hor
      push_cast at this
      rw [he]; nlinarith
  -- (6)
  have h6 : ∫⁻ x in D, ENNReal.ofReal (bh M a' x) ∂μ =
      ∫⁻ x in D, ENNReal.ofReal (buyerPayoff M x) ∂μ + ∫⁻ x in D, g x ∂μ := by
    rw [← lintegral_add_left mb.ennreal_ofReal]
    refine lintegral_congr_ae (hquadD.mono fun x hx => ?_)
    simp only [hg]
    rw [← ENNReal.ofReal_add (hbnn _) (sub_nonneg.2 (hbh_ge _ hx))]
    congr 1; ring
  -- finiteness of `∫ b̂`
  have hBh : ∫⁻ x in D, ENNReal.ofReal (bh M a' x) ∂μ ≠ ⊤ := by
    have hle : ∫⁻ x in D, ENNReal.ofReal (bh M a' x) ∂μ ≤
        ∫⁻ _ in D, ENNReal.ofReal (|buyerPayoff M 0| + (K + K) + a') ∂μ := by
      refine setLIntegral_mono measurable_const fun x hx => ENNReal.ofReal_le_ofReal ?_
      have hb := bh_bound M hM a' x
      have hx0 : (x 0 : ℝ) ≤ K := by exact_mod_cast hx.1
      have hx1 : (x 1 : ℝ) ≤ K := by exact_mod_cast hx.2
      linarith
    refine ne_top_of_le_ne_top ?_ hle
    rw [setLIntegral_const]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)
  have hL : ENNReal.ofReal l = 1 + ENNReal.ofReal e := by
    rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_add zero_le_one he0.le]
    congr 1; rw [he]; ring
  have eL : ENNReal.ofReal l = ENNReal.ofReal ((c : ℝ) ^ 2) := by rw [hlr]
  have eα : ENNReal.ofReal a' = ENNReal.ofReal a := by rw [ha'r]
  -- algebra
  set S := ∫⁻ x in D, ENNReal.ofReal (M.s x) ∂μ
  set Bb := ∫⁻ x in D, ENNReal.ofReal (buyerPayoff M x) ∂μ
  set H := ∫⁻ x in D, g x ∂μ
  set Bl := ∫⁻ x in D, ENNReal.ofReal (buyerPayoff M (l • x)) ∂μ
  set Hl := ∫⁻ x in D, g (l • x) ∂μ
  set Bhl := ∫⁻ x in D, ENNReal.ofReal (bh M a' (l • x)) ∂μ
  set QT := ∫⁻ x in D, ENNReal.ofReal (Qf M a' (l * (x 0 + x 1)) * ((x 0 : ℝ) + x 1)) ∂μ
  set Bh := ∫⁻ x in D, ENNReal.ofReal (bh M a' x) ∂μ
  set Hc := ∫⁻ x, Core.indicator (D.indicator g) x ∂μ
  set Lm := μ Cs
  set E := ENNReal.ofReal e
  set L := ENNReal.ofReal (l : ℝ)
  set α := ENNReal.ofReal (a' : ℝ)
  have hEt : E ≠ ⊤ := ENNReal.ofReal_ne_top
  have key : Bh + E * (S + Bh) ≤ Bh + E * (QT + L * α * Lm) := by
    calc Bh + E * (S + Bh) = E * S + L * Bb + L * H := by
            rw [hL, h6]; ring
      _ ≤ E * S + L * Bb + L * (Hc + E * α * Lm) := by gcongr
      _ = (E * S + L * Bb) + L * Hc + L * E * α * Lm := by ring
      _ ≤ Bl + Hl + L * E * α * Lm := by gcongr
      _ = Bhl + L * E * α * Lm := by rw [h2]
      _ ≤ Bh + E * QT + L * E * α * Lm := by gcongr
      _ = Bh + E * (QT + L * α * Lm) := by ring
  have key2 := (ENNReal.add_le_add_iff_left hBh).1 key
  have key3 := (ENNReal.mul_le_mul_iff_right hEe hEt).1 key2
  rw [eL, eα] at key3
  exact key3

end G

/-! ### Part H: letting the scale tend to `1`, then the box to `ℝ²₊` -/

section H

/-- The scales `c_n = 1 + 1/(n+1) ↓ 1`. -/
noncomputable def cs (n : ℕ) : ℝ≥0 := 1 + 1 / ((n : ℝ≥0) + 1)

lemma cs_coe (n : ℕ) : ((cs n : ℝ≥0) : ℝ) = 1 + 1 / ((n : ℝ) + 1) := by
  simp [cs]

lemma one_lt_cs (n : ℕ) : 1 < cs n := by
  have : (1 : ℝ) < cs n := by
    rw [cs_coe]
    have : (0:ℝ) < 1 / ((n:ℝ) + 1) := by positivity
    linarith
  exact_mod_cast this

lemma cs_le_two (n : ℕ) : cs n ≤ 2 := by
  have : ((cs n : ℝ≥0) : ℝ) ≤ 2 := by
    rw [cs_coe]
    have : 1 / ((n : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]; have : (0:ℝ) ≤ n := Nat.cast_nonneg n
      linarith
    linarith
  exact_mod_cast this

lemma cs_anti : Antitone cs := by
  intro n m hnm
  have : ((cs m : ℝ≥0) : ℝ) ≤ cs n := by
    rw [cs_coe, cs_coe]
    have : (n : ℝ) ≤ m := by exact_mod_cast hnm
    gcongr
  exact_mod_cast this

lemma cs_tendsto : Filter.Tendsto cs Filter.atTop (nhds 1) := by
  rw [← NNReal.tendsto_coe]
  simp only [cs_coe, NNReal.coe_one]
  simpa using (tendsto_const_nhds (x := (1 : ℝ))).add tendsto_one_div_add_atTop_nhds_zero_nat

lemma cs2_tendsto : Filter.Tendsto (fun n => cs n ^ 2) Filter.atTop (nhds 1) := by
  simpa using cs_tendsto.pow 2

variable (M : Mechanism (Fin 2)) (hM : IsAdmissible M) (hNPT : IsNPT M) (hsym : IsSymmetric M)
  (a : ℝ) (ha : 0 < a) (f : ℝ → ℝ) (hf_meas : Measurable f) (hf_nonneg : ∀ x, 0 ≤ f x)
  (hf_supp : ∀ x, x < a → f x = 0)
  (hf_diff : ∀ x, a < x → DifferentiableAt ℝ f x)
  (h9 : ∀ x, a < x → x * deriv f x + 3 / 2 * f x ≤ 0)

include ha hf_supp in
lemma Iic_tendsto [IsProbabilityMeasure (densityLaw f)] :
    Filter.Tendsto (fun n => densityLaw f (Set.Iic (cs n ^ 2 * a.toNNReal))) Filter.atTop
      (nhds 0) := by
  have hanti : Antitone (fun n => Set.Iic (cs n ^ 2 * a.toNNReal)) := by
    intro n m hnm
    apply Set.Iic_subset_Iic.2
    have := cs_anti hnm
    gcongr
  have h := tendsto_measure_iInter_atTop (μ := densityLaw f)
    (fun n => measurableSet_Iic.nullMeasurableSet) hanti ⟨0, measure_ne_top _ _⟩
  have hI : (⋂ n, Set.Iic (cs n ^ 2 * a.toNNReal)) = Set.Iic a.toNNReal := by
    ext t
    simp only [Set.mem_iInter, Set.mem_Iic]
    constructor
    · intro ht
      have hlim : Filter.Tendsto (fun n => cs n ^ 2 * a.toNNReal) Filter.atTop
          (nhds (1 * a.toNNReal)) := cs2_tendsto.mul_const _
      rw [one_mul] at hlim
      exact ge_of_tendsto' hlim ht
    · intro ht n
      calc t ≤ a.toNNReal := ht
        _ = 1 * a.toNNReal := (one_mul _).symm
        _ ≤ cs n ^ 2 * a.toNNReal := by
            gcongr
            exact one_le_pow₀ (one_lt_cs n).le
  rw [hI, densityLaw_Iic a ha f hf_supp] at h
  exact h

include hM hsym in
lemma bh_nonneg (a' : ℝ≥0) (x : Fin 2 → ℝ≥0) (hx : ∀ i, a' ≤ x i) : 0 ≤ bh M a' x :=
  (hM.2.2.1 x).trans (F3 M a' hM.2.1 hsym x hx)

include hM hNPT hsym ha hf_meas hf_nonneg hf_supp hf_diff h9 in
lemma box_lim [IsProbabilityMeasure (densityLaw f)] (K : ℝ≥0) :
    ∫⁻ x in box K, ENNReal.ofReal (M.s x) ∂(Measure.pi fun _ : Fin 2 => densityLaw f) ≤
      ∫⁻ x in box K, ENNReal.ofReal ((bundledMajorant M a.toNNReal).s x)
        ∂(Measure.pi fun _ : Fin 2 => densityLaw f) := by
  set μ := Measure.pi fun _ : Fin 2 => densityLaw f with hμ
  set a' := a.toNNReal with ha'
  set D := box K with hD
  have hDm : MeasurableSet D := box_meas K
  have hquad : ∀ᵐ x ∂μ, ∀ i, a' ≤ x i := ae_quad a ha f hf_supp
  have hquadD : ∀ᵐ x ∂(μ.restrict D), ∀ i, a' ≤ x i := ae_restrict_of_ae hquad
  set Q := Qf M a' with hQ
  have mQ : Measurable Q := Qf_meas M hM a'
  -- the inequality at each scale
  have hn : ∀ n : ℕ,
      ∫⁻ x in D, ENNReal.ofReal (M.s x) ∂μ + ∫⁻ x in D, ENNReal.ofReal (bh M a' x) ∂μ ≤
        ∫⁻ x in D, ENNReal.ofReal (Q (cs n ^ 2 * (x 0 + x 1)) * ((x 0 : ℝ) + x 1)) ∂μ +
          ENNReal.ofReal 4 * ENNReal.ofReal a *
            (densityLaw f (Set.Iic (cs n ^ 2 * a')) + densityLaw f (Set.Iic (cs n ^ 2 * a'))) := by
    intro n
    have hb := box_ineq M hM hNPT hsym a ha f hf_meas hf_supp K (cs n) (one_lt_cs n)
      (fun u hu => f_scale a ha f hf_nonneg hf_diff h9 (cs n) (by exact_mod_cast (one_lt_cs n).le) u hu)
    refine hb.trans (add_le_add le_rfl ?_)
    gcongr
    · have h2 : ((cs n : ℝ≥0) : ℝ) ≤ 2 := by exact_mod_cast cs_le_two n
      have h0 : (0 : ℝ) ≤ cs n := NNReal.coe_nonneg _
      nlinarith
    · exact core_compl_le f _
  -- the limit
  have hlimQ : Filter.Tendsto
      (fun n : ℕ => ∫⁻ x in D, ENNReal.ofReal (Q (cs n ^ 2 * (x 0 + x 1)) * ((x 0 : ℝ) + x 1)) ∂μ)
      Filter.atTop (nhds (∫⁻ x in D, ENNReal.ofReal (Q (x 0 + x 1) * ((x 0 : ℝ) + x 1)) ∂μ)) := by
    refine tendsto_lintegral_of_dominated_convergence (fun _ => ENNReal.ofReal ((K : ℝ) + K))
      (fun n => ?_) (fun n => ?_) ?_ ?_
    · exact ((mQ.comp (by fun_prop)).mul (by fun_prop)).ennreal_ofReal
    · filter_upwards [ae_restrict_mem hDm] with x hx
      refine ENNReal.ofReal_le_ofReal ?_
      have hq := hM.1 ![cs n ^ 2 * (x 0 + x 1) - a', a'] 0
      have hx0 : (x 0 : ℝ) ≤ K := by exact_mod_cast hx.1
      have hx1 : (x 1 : ℝ) ≤ K := by exact_mod_cast hx.2
      have hT0 : (0 : ℝ) ≤ (x 0 : ℝ) + x 1 := by positivity
      have : Q (cs n ^ 2 * (x 0 + x 1)) ≤ 1 := hq.2
      have : 0 ≤ Q (cs n ^ 2 * (x 0 + x 1)) := hq.1
      nlinarith
    · rw [setLIntegral_const]
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)
    · -- continuity of `Q` at `x₀ + x₁` for almost every `x`
      have hcount := (Q_mono M hM a').countable_not_continuousAt
      have hnull := sum_countable_null a ha f hf_supp _ hcount
      have hae : ∀ᵐ x ∂μ, ContinuousAt Q (x 0 + x 1) := by
        rw [ae_iff]
        exact hnull
      filter_upwards [ae_restrict_of_ae hae] with x hx
      refine (ENNReal.continuous_ofReal.tendsto _).comp (Filter.Tendsto.mul_const _ ?_)
      refine hx.tendsto.comp ?_
      simpa using cs2_tendsto.mul_const (x 0 + x 1)
  have hlimL : Filter.Tendsto (fun n : ℕ => ENNReal.ofReal 4 * ENNReal.ofReal a *
      (densityLaw f (Set.Iic (cs n ^ 2 * a')) + densityLaw f (Set.Iic (cs n ^ 2 * a'))))
      Filter.atTop (nhds 0) := by
    have h := Iic_tendsto a ha f hf_supp
    have h2 := h.add h
    rw [add_zero] at h2
    have := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal 4 * ENNReal.ofReal a) h2
      (Or.inr (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top))
    rwa [mul_zero] at this
  have hlim := hlimQ.add hlimL
  rw [add_zero] at hlim
  have hmain := ge_of_tendsto' hlim hn
  -- identify the limit
  have hid : ∫⁻ x in D, ENNReal.ofReal (Q (x 0 + x 1) * ((x 0 : ℝ) + x 1)) ∂μ =
      ∫⁻ x in D, ENNReal.ofReal ((bundledMajorant M a').s x) ∂μ +
        ∫⁻ x in D, ENNReal.ofReal (bh M a' x) ∂μ := by
    rw [← lintegral_add_right _ (bh_meas M hM a').ennreal_ofReal]
    refine lintegral_congr_ae (hquadD.mono fun x hx => ?_)
    dsimp only
    rw [← ENNReal.ofReal_add (F5 M a' hM hNPT hsym x hx) (bh_nonneg M hM hsym a' x hx), s_B]
    congr 1; ring
  rw [hid] at hmain
  have hBh : ∫⁻ x in D, ENNReal.ofReal (bh M a' x) ∂μ ≠ ⊤ := by
    have hle : ∫⁻ x in D, ENNReal.ofReal (bh M a' x) ∂μ ≤
        ∫⁻ _ in D, ENNReal.ofReal (|buyerPayoff M 0| + (K + K) + a') ∂μ := by
      refine setLIntegral_mono measurable_const fun x hx => ENNReal.ofReal_le_ofReal ?_
      have hb := bh_bound M hM a' x
      have hx0 : (x 0 : ℝ) ≤ K := by exact_mod_cast hx.1
      have hx1 : (x 1 : ℝ) ≤ K := by exact_mod_cast hx.2
      linarith
    refine ne_top_of_le_ne_top ?_ hle
    rw [setLIntegral_const]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)
  exact (ENNReal.add_le_add_iff_right hBh).1 hmain

end H

end MultiItemRev.BundlingOpt.RevMaj

open MultiItemRev.BundlingOpt MultiItemRev.BundlingOpt.RevMaj in
theorem solution (a : ℝ) (ha : 0 < a) (f : ℝ → ℝ) (hf_meas : Measurable f) (hf_nonneg : ∀ x, 0 ≤ f x)
    (hf_supp : ∀ x, x < a → f x = 0)
    (hf_mass : ∫⁻ x, ENNReal.ofReal (f x) = 1)
    (hf_diff : ∀ x, a < x → DifferentiableAt ℝ f x)
    (h9 : ∀ x, a < x → x * deriv f x + 3 / 2 * f x ≤ 0)
    (M : Mechanism (Fin 2)) (hM : IsAdmissible M ∧ IsNPT M) (hsym : IsSymmetric M) :
    expRevenue (Measure.pi (fun _ : Fin 2 => densityLaw f)) M ≤
      expRevenue (Measure.pi (fun _ : Fin 2 => densityLaw f)) (bundledMajorant M a.toNNReal) := by
  haveI := densityLaw_prob f hf_mass
  obtain ⟨hA, hNPT⟩ := hM
  set μ := Measure.pi fun _ : Fin 2 => densityLaw f with hμ
  have hquad : ∀ᵐ x ∂μ, ∀ i, a.toNNReal ≤ x i := ae_quad a ha f hf_supp
  have n1 : ∫⁻ x, ENNReal.ofReal (-M.s x) ∂μ = 0 := by
    refine (lintegral_congr fun x => ?_).trans lintegral_zero
    exact ENNReal.ofReal_of_nonpos (by linarith [hNPT x])
  have n2 : ∫⁻ x, ENNReal.ofReal (-(bundledMajorant M a.toNNReal).s x) ∂μ = 0 := by
    refine (lintegral_congr_ae (hquad.mono fun x hx => ?_)).trans lintegral_zero
    exact ENNReal.ofReal_of_nonpos (by linarith [F5 M a.toNNReal hA hNPT hsym x hx])
  unfold expRevenue
  rw [n1, n2]
  simp only [EReal.coe_ennreal_zero, sub_zero]
  refine EReal.coe_ennreal_le_coe_ennreal_iff.2 ?_
  have hU : (⋃ K : ℕ, box (K : ℝ≥0)) = Set.univ := by
    refine Set.eq_univ_of_forall fun x => ?_
    obtain ⟨K, hK⟩ := exists_nat_ge (max (x 0) (x 1))
    exact Set.mem_iUnion.2 ⟨K, (le_max_left _ _).trans hK, (le_max_right _ _).trans hK⟩
  have hdir : Directed (· ⊆ ·) (fun K : ℕ => box (K : ℝ≥0)) := by
    refine Monotone.directed_le fun K K' hKK' x hx => ?_
    have : (K : ℝ≥0) ≤ K' := by exact_mod_cast hKK'
    exact ⟨hx.1.trans this, hx.2.trans this⟩
  rw [← setLIntegral_univ, ← hU, setLIntegral_iUnion_of_directed _ hdir]
  refine iSup_le fun K => (box_lim M hA hNPT hsym a ha f hf_meas hf_nonneg hf_supp hf_diff h9 K).trans ?_
  exact setLIntegral_le_lintegral _ _
