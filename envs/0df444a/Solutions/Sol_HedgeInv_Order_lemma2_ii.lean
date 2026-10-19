-- Prove2me | solution 1 for HedgeInv.Order.lemma2_ii
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-18T20:25:56.964803+00:00
-- url     : https://prove2.me/submissions/c0dbde8c-a6f2-448e-a487-9ab539b9f645

import Mathlib
set_option autoImplicit false

open MeasureTheory

lemma l2_ae_zero (μ : Measure ℝ) (f : ℝ → ℝ) (hfi : Integrable f μ)
    (hmean : ∫ x, f x ∂μ = 0) (h : (∀ x, 0 ≤ f x) ∨ (∀ x, f x ≤ 0)) : f =ᵐ[μ] 0 := by
  rcases h with h | h
  · exact (integral_eq_zero_iff_of_nonneg h hfi).1 hmean
  · have h' : (fun x => -f x) =ᵐ[μ] 0 := by
      refine (integral_eq_zero_iff_of_nonneg (fun x => neg_nonneg.2 (h x)) hfi.neg).1 ?_
      rw [integral_neg, hmean]; simp
    filter_upwards [h'] with x hx
    simpa using hx

theorem solution (μ : Measure ℝ) [IsProbabilityMeasure μ] (f w : ℝ → ℝ)
    (hf : Antitone f) (hw : Monotone w) (hw0 : ∀ x, 0 ≤ w x)
    (hfi : Integrable f μ) (hwfi : Integrable (fun x => w x * f x) μ)
    (hmean : ∫ x, f x ∂μ = 0) :
    ∫ x, w x * f x ∂μ ≤ 0 := by
  have zero_case : ((∀ x, 0 ≤ f x) ∨ (∀ x, f x ≤ 0)) → ∫ x, w x * f x ∂μ ≤ 0 := by
    intro h
    have hae := l2_ae_zero μ f hfi hmean h
    have : ∫ x, w x * f x ∂μ = ∫ x, (0:ℝ) ∂μ := by
      refine integral_congr_ae ?_
      filter_upwards [hae] with x hx
      simp [hx]
    rw [this]; simp
  set S : Set ℝ := {x | 0 < f x} with hS
  by_cases hne : S.Nonempty
  · by_cases hbdd : BddAbove S
    · set a := sSup S with ha
      have key : ∀ x, (w x - w a) * f x ≤ 0 := by
        intro x
        rcases lt_trichotomy x a with hx | hx | hx
        · obtain ⟨s, hs, hxs⟩ := (lt_csSup_iff hbdd hne).1 hx
          have h1 : 0 < f x := lt_of_lt_of_le hs (hf hxs.le)
          have h2 : w x - w a ≤ 0 := sub_nonpos.2 (hw hx.le)
          exact mul_nonpos_of_nonpos_of_nonneg h2 h1.le
        · subst hx; simp
        · have hnot : x ∉ S := fun hxS => absurd (le_csSup hbdd hxS) (not_le.2 hx)
          have h1 : f x ≤ 0 := not_lt.1 hnot
          have h2 : 0 ≤ w x - w a := sub_nonneg.2 (hw hx.le)
          exact mul_nonpos_of_nonneg_of_nonpos h2 h1
      have hint : Integrable (fun x => (w x - w a) * f x) μ := by
        have := hwfi.sub (hfi.const_mul (w a))
        refine this.congr (Filter.Eventually.of_forall fun x => ?_)
        simp only [Pi.sub_apply]; ring
      have h0 : ∫ x, (w x - w a) * f x ∂μ ≤ 0 := integral_nonpos key
      have : ∫ x, (w x - w a) * f x ∂μ = ∫ x, w x * f x ∂μ := by
        have e : (fun x => (w x - w a) * f x) = fun x => w x * f x - w a * f x := by
          funext x; ring
        rw [e, integral_sub hwfi (hfi.const_mul _), integral_const_mul, hmean]; simp
      rwa [this] at h0
    · apply zero_case; left
      intro x
      by_contra hneg
      push_neg at hneg
      apply hbdd
      refine ⟨x, fun s hs => ?_⟩
      by_contra hsx
      push_neg at hsx
      have : f s ≤ f x := hf hsx.le
      have : 0 < f s := hs
      linarith
  · apply zero_case; right
    intro x
    by_contra h; push_neg at h
    exact hne ⟨x, h⟩
