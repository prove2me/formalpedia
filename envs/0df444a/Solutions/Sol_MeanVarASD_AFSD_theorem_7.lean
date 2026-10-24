-- Prove2me | solution 1 for MeanVarASD.AFSD.theorem_7
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-24T04:46:23.53423+00:00
-- url     : https://prove2.me/submissions/e7920349-806b-4f5d-ba4d-882f31a9def7

import Mathlib
import Definitions.Def_MeanVarASD_AFSD_Defs

set_option autoImplicit false

open MeasureTheory ProbabilityTheory

namespace MeanVarASD.AFSD

lemma deriv_bounds {γ : ℝ} (hγ : 0 < γ) {u : ℝ → ℝ} (hu : u ∈ UClass γ γ) :
    (∀ a, 0 ≤ deriv u a) ∧ ∀ a b, γ * deriv u a ≤ deriv u b := by
  obtain ⟨_, h⟩ := hu
  refine ⟨fun a => ?_, fun a b => ?_⟩
  · have := (h a a le_rfl).1
    by_contra hc
    push_neg at hc
    nlinarith
  · rcases le_total a b with hab | hab
    · exact (h a b hab).2.2.2
    · exact (h b a hab).2.1

lemma pw_upper {u : ℝ → ℝ} (hd : Differentiable ℝ u) {K γ : ℝ}
    (hK1 : ∀ a, deriv u a ≤ K) (hK2 : ∀ a, γ * K ≤ deriv u a) (δ x : ℝ) :
    u x ≤ u δ + K * (γ * (x - δ) + (1 - γ) * max (x - δ) 0) := by
  rcases le_total δ x with h | h
  · rw [max_eq_left (sub_nonneg.2 h)]
    have := image_sub_le_mul_sub_of_deriv_le hd hK1 h
    nlinarith
  · rw [max_eq_right (by linarith)]
    have := mul_sub_le_image_sub_of_le_deriv hd hK2 h
    nlinarith

lemma pw_lower {u : ℝ → ℝ} (hd : Differentiable ℝ u) {K γ : ℝ}
    (hK1 : ∀ a, deriv u a ≤ K) (hK2 : ∀ a, γ * K ≤ deriv u a) (δ x : ℝ) :
    u δ + K * (γ * (x - δ) + (-(1 - γ)) * max (δ - x) 0) ≤ u x := by
  rcases le_total δ x with h | h
  · rw [max_eq_right (by linarith)]
    have := mul_sub_le_image_sub_of_le_deriv hd hK2 h
    nlinarith
  · rw [max_eq_left (sub_nonneg.2 h)]
    have := image_sub_le_mul_sub_of_deriv_le hd hK1 h
    nlinarith

lemma mv_bound {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : Ω → ℝ) (hZ : MemLp Z 2 P) :
    ∫ ω, max (Z ω) 0 ∂P ≤
      (∫ ω, Z ω ∂P + Real.sqrt (variance Z P + (∫ ω, Z ω ∂P) ^ 2)) / 2 := by
  have hZi := hZ.integrable one_le_two
  have hA : MemLp (fun ω => |Z ω|) 2 P := by simpa [Real.norm_eq_abs] using hZ.norm
  have hAi := hA.integrable one_le_two
  have e1 : (fun ω => max (Z ω) 0) = fun ω => (Z ω + |Z ω|) / 2 := by
    funext ω
    rcases le_total (Z ω) 0 with h | h
    · rw [max_eq_right h, abs_of_nonpos h]; ring
    · rw [max_eq_left h, abs_of_nonneg h]; ring
  rw [e1, integral_div, integral_add hZi hAi]
  have hv := variance_eq_sub hA
  have hv0 := variance_nonneg (fun ω => |Z ω|) P
  have hvZ := variance_eq_sub hZ
  have e2 : ∫ ω, ((fun ω => |Z ω|) ^ 2) ω ∂P = ∫ ω, (Z ^ 2) ω ∂P := by
    congr 1
    funext ω
    simp [sq_abs]
  have key : (∫ ω, |Z ω| ∂P) ^ 2 ≤ variance Z P + (∫ ω, Z ω ∂P) ^ 2 := by
    rw [e2] at hv
    linarith
  have := le_trans (le_abs_self _) (Real.abs_le_sqrt key)
  linarith

lemma int_aff {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (f g : Ω → ℝ) (hf : Integrable f P) (hg : Integrable g P) (c K γ δ e : ℝ) :
    Integrable (fun ω => c + K * (γ * (f ω - δ) + e * g ω)) P ∧
    ∫ ω, (c + K * (γ * (f ω - δ) + e * g ω)) ∂P =
      c + K * (γ * (∫ ω, f ω ∂P - δ) + e * ∫ ω, g ω ∂P) := by
  have heq : (fun ω => c + K * (γ * (f ω - δ) + e * g ω)) =
      fun ω => (c - K * γ * δ) + ((K * γ) * f ω + (K * e) * g ω) := by
    funext ω; ring
  have hI : Integrable (fun ω => (K * γ) * f ω + (K * e) * g ω) P :=
    (hf.const_mul _).add (hg.const_mul _)
  refine ⟨?_, ?_⟩
  · rw [heq]; exact (integrable_const _).add hI
  · rw [heq, integral_add (integrable_const _) hI, integral_add (hf.const_mul _) (hg.const_mul _),
      integral_const, integral_const_mul, integral_const_mul]
    simp
    ring

lemma gamma_pos (μX μY σX σY : ℝ) (hσX : 0 ≤ σX) (hσY : 0 ≤ σY) (hμ : μX < μY) :
    0 < gammaStar (tStat μX μY σX σY) := by
  unfold gammaStar tStat
  have ht : 0 ≤ (μY - μX) / (σY + σX) := div_nonneg (by linarith) (by linarith)
  have hr := Real.sqrt_nonneg (((μY - μX) / (σY + σX)) ^ 2 + 1)
  apply div_pos one_pos
  nlinarith

lemma alg (μX μY σX σY γ : ℝ) (hσX : 0 ≤ σX) (hσY : 0 ≤ σY) (hμ : μX < μY)
    (hγ : gammaStar (tStat μX μY σX σY) ≤ γ) (hγ1 : γ ≤ 1) :
    ∃ δ : ℝ, γ * (μX - δ) + (1 - γ) * (((μX - δ) + Real.sqrt (σX ^ 2 + (μX - δ) ^ 2)) / 2) ≤
      γ * (μY - δ) - (1 - γ) * (((δ - μY) + Real.sqrt (σY ^ 2 + (δ - μY) ^ 2)) / 2) := by
  unfold gammaStar tStat at hγ
  by_cases hs : σY + σX = 0
  · rw [hs, div_zero] at hγ
    have h1 : γ = 1 := le_antisymm hγ1 (by simpa using hγ)
    subst h1
    refine ⟨0, ?_⟩
    simp
    linarith
  · have hspos : 0 < σY + σX := lt_of_le_of_ne (by linarith) (Ne.symm hs)
    set s := σY + σX with hsdef
    set t := (μY - μX) / s with htdef
    have ht : 0 < t := div_pos (by linarith) hspos
    set r := Real.sqrt (t ^ 2 + 1) with hrdef
    have hr0 : 0 ≤ r := Real.sqrt_nonneg _
    have hr2 : r ^ 2 = t ^ 2 + 1 := Real.sq_sqrt (by positivity)
    have hden : 1 + 2 * t * (t + r) = (t + r) ^ 2 := by nlinarith
    rw [hden] at hγ
    have htr : 0 < t + r := by linarith
    have hγ' : 1 ≤ γ * (t + r) ^ 2 := by
      rw [div_le_iff₀ (by positivity)] at hγ; linarith
    have key : r - t ≤ γ * (t + r) := by
      have h3 : (r - t) * (t + r) = 1 := by nlinarith
      by_contra hc
      push_neg at hc
      nlinarith
    have htm : μY - μX = t * s := by rw [htdef]; field_simp
    refine ⟨(μX * σY + μY * σX) / s, ?_⟩
    have eX : μX - (μX * σY + μY * σX) / s = -(σX * t) := by
      rw [eq_neg_iff_add_eq_zero]
      field_simp
      rw [hsdef] at htm ⊢
      nlinarith
    have eY : (μX * σY + μY * σX) / s - μY = -(σY * t) := by
      rw [eq_neg_iff_add_eq_zero]
      field_simp
      rw [hsdef] at htm ⊢
      nlinarith
    have eY' : μY - (μX * σY + μY * σX) / s = σY * t := by linarith
    have sX : Real.sqrt (σX ^ 2 + (-(σX * t)) ^ 2) = σX * r := by
      rw [show σX ^ 2 + (-(σX * t)) ^ 2 = (σX * r) ^ 2 by rw [mul_pow, hr2]; ring]
      exact Real.sqrt_sq (mul_nonneg hσX hr0)
    have sY : Real.sqrt (σY ^ 2 + (-(σY * t)) ^ 2) = σY * r := by
      rw [show σY ^ 2 + (-(σY * t)) ^ 2 = (σY * r) ^ 2 by rw [mul_pow, hr2]; ring]
      exact Real.sqrt_sq (mul_nonneg hσY hr0)
    rw [eX, eY, eY', sX, sY]
    have h1γ : 0 ≤ 1 - γ := by linarith
    have hk : (1 - γ) * (r - t) ≤ 2 * γ * t := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hk hσX, mul_le_mul_of_nonneg_left hk hσY]

end MeanVarASD.AFSD

open MeasureTheory ProbabilityTheory MeanVarASD.AFSD in
theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X Y : Ω → ℝ) (hX : MemLp X 2 P) (hY : MemLp Y 2 P)
    (hμ : ∫ ω, X ω ∂P < ∫ ω, Y ω ∂P) (γ : ℝ)
    (hγ : gammaStar (tStat (∫ ω, X ω ∂P) (∫ ω, Y ω ∂P)
            (Real.sqrt (variance X P)) (Real.sqrt (variance Y P))) ≤ γ)
    (hγ1 : γ ≤ 1) :
    SDle γ γ P X Y := by
  have hXi := hX.integrable one_le_two
  have hYi := hY.integrable one_le_two
  have hγpos : 0 < γ :=
    lt_of_lt_of_le (gamma_pos _ _ _ _ (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) hμ) hγ
  refine ⟨hγpos.le, hγ1, hγpos.le, hγ1, hXi, hYi, ?_⟩
  intro u hu huX huY
  obtain ⟨hd0, hdb⟩ := deriv_bounds hγpos hu
  have hd : Differentiable ℝ u := hu.1.differentiable one_ne_zero
  have hbdd : BddAbove (Set.range (deriv u)) := by
    refine ⟨deriv u 0 / γ, ?_⟩
    rintro _ ⟨a, rfl⟩
    rw [le_div_iff₀ hγpos]
    linarith [hdb a 0]
  set K := sSup (Set.range (deriv u)) with hKdef
  have hK1 : ∀ a, deriv u a ≤ K := fun a => le_csSup hbdd ⟨a, rfl⟩
  have hK2 : ∀ b, γ * K ≤ deriv u b := by
    intro b
    have : K ≤ deriv u b / γ := by
      refine csSup_le (Set.range_nonempty _) ?_
      rintro _ ⟨a, rfl⟩
      rw [le_div_iff₀ hγpos]
      linarith [hdb a b]
    rw [le_div_iff₀ hγpos] at this
    linarith
  have hK0 : 0 ≤ K := le_trans (hd0 0) (hK1 0)
  obtain ⟨δ, hδ⟩ := alg _ _ _ _ γ (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) hμ hγ hγ1
  rw [Real.sq_sqrt (variance_nonneg _ _), Real.sq_sqrt (variance_nonneg _ _)] at hδ
  have hmX := mv_bound P (fun ω => X ω - δ) (hX.sub (memLp_const δ))
  have hmY := mv_bound P (fun ω => δ - Y ω) ((memLp_const δ).sub hY)
  have eX : ∫ ω, (X ω - δ) ∂P = ∫ ω, X ω ∂P - δ := by
    rw [integral_sub hXi (integrable_const _)]; simp
  have eY : ∫ ω, (δ - Y ω) ∂P = δ - ∫ ω, Y ω ∂P := by
    rw [integral_sub (integrable_const _) hYi]; simp
  rw [eX, variance_sub_const hX.aestronglyMeasurable] at hmX
  rw [eY, variance_const_sub hY.aestronglyMeasurable] at hmY
  have gX : Integrable (fun ω => max (X ω - δ) 0) P := (hXi.sub (integrable_const δ)).pos_part
  have gY : Integrable (fun ω => max (δ - Y ω) 0) P := ((integrable_const δ).sub hYi).pos_part
  obtain ⟨iX, jX⟩ := int_aff P X _ hXi gX (u δ) K γ δ (1 - γ)
  obtain ⟨iY, jY⟩ := int_aff P Y _ hYi gY (u δ) K γ δ (-(1 - γ))
  have h1 : ∫ ω, u (X ω) ∂P ≤ ∫ ω, (u δ + K * (γ * (X ω - δ) + (1 - γ) * max (X ω - δ) 0)) ∂P :=
    integral_mono huX iX (fun ω => pw_upper hd hK1 hK2 δ (X ω))
  have h2 : ∫ ω, (u δ + K * (γ * (Y ω - δ) + (-(1 - γ)) * max (δ - Y ω) 0)) ∂P ≤
      ∫ ω, u (Y ω) ∂P :=
    integral_mono iY huY (fun ω => pw_lower hd hK1 hK2 δ (Y ω))
  rw [jX] at h1
  rw [jY] at h2
  have h1γ : 0 ≤ 1 - γ := by linarith
  have hin : γ * (∫ ω, X ω ∂P - δ) + (1 - γ) * ∫ ω, max (X ω - δ) 0 ∂P ≤
      γ * (∫ ω, Y ω ∂P - δ) + (-(1 - γ)) * ∫ ω, max (δ - Y ω) 0 ∂P := by
    nlinarith [mul_le_mul_of_nonneg_left hmX h1γ, mul_le_mul_of_nonneg_left hmY h1γ]
  have := mul_le_mul_of_nonneg_left hin hK0
  linarith
