-- Prove2me | solution 1 for GlobalTheory.Lin.abel_primesIoc_weight
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T19:00:38.320862+00:00
-- url     : https://prove2.me/submissions/92b06d2b-2054-4a7f-bb5a-01bf54ff7588

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_ZerosDisc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_SumPrimesIocEqSumIndicator
import Theorems.Thm_GlobalTheory_Lin_mem_primesIoc_bounds
import Theorems.Thm_GlobalTheory_Lin_sum_primesIoc_eq_sum_indicator
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology GlobalTheory.Lin
open scoped Classical
namespace GlobalTheory.Lin
private lemma intervalIntegrable_indicator_Ici_of_intervalIntegrable {E : Type*} [NormedAddCommGroup E] {f : ℝ → E} {x y p : ℝ}
    (hf : IntervalIntegrable f MeasureTheory.volume x y) :
    IntervalIntegrable ((Set.Ici p).indicator f) MeasureTheory.volume x y := by
  rw [intervalIntegrable_iff] at hf ⊢
  exact hf.indicator measurableSet_Ici
private lemma integral_indicator_Ici_deriv_eq_sub_of_hasDerivAt {J J' : ℝ → ℝ} {x y p : ℝ} (hxp : x < p) (hpy : p ≤ y)
    (hJ : ∀ t ∈ Set.Icc x y, HasDerivAt J (J' t) t) (hc : ContinuousOn J' (Set.Icc x y)) :
    ∫ t in x..y, (Set.Ici p).indicator (fun t => (J' t : ℂ)) t = (J y : ℂ) - J p := by
  have hxy : x ≤ y := hxp.le.trans hpy
  rw [intervalIntegral.integral_of_le hxy, MeasureTheory.setIntegral_indicator measurableSet_Ici]
  have hset : Set.Ioc x y ∩ Set.Ici p = Set.Icc p y := by
    ext t
    simp only [Set.mem_inter_iff, Set.mem_Ioc, Set.mem_Ici, Set.mem_Icc]
    constructor
    · rintro ⟨⟨_, h2⟩, h3⟩
      exact ⟨h3, h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨⟨hxp.trans_le h1, h2⟩, h1⟩
  rw [hset, MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hpy]
  have hsub : Set.uIcc p y ⊆ Set.Icc x y := by
    rw [Set.uIcc_of_le hpy]
    exact Set.Icc_subset_Icc hxp.le le_rfl
  have hc' : ContinuousOn (fun t => (J' t : ℂ)) (Set.Icc x y) :=
    Complex.continuous_ofReal.comp_continuousOn hc
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t ht => (hJ t (hsub ht)).ofReal_comp)
    ((hc'.mono hsub).intervalIntegrable)
end GlobalTheory.Lin
end

set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology GlobalTheory.Lin
open scoped Classical
open GlobalTheory GlobalTheory.Lin
namespace GlobalTheory.Lin
theorem _root_.solution (a : ℕ → ℂ) (J J' : ℝ → ℝ) (x y r : ℝ) (hx : 1 ≤ x) (hxy : x ≤ y)
    (hJ : ∀ t ∈ Set.Icc x y, HasDerivAt J (J' t) t) (hc : ContinuousOn J' (Set.Icc x y))
    (hb : ∀ t ∈ Set.Icc x y, |J' t| ≤ r / t) :
    ‖∑ p ∈ primesIoc x y, a p * ((J p - J y : ℝ) : ℂ)‖
      ≤ r * ∫ t in x..y, ‖∑ p ∈ primesIoc x t, a p‖ / t := by
  have hx0 : (0 : ℝ) ≤ x := zero_le_one.trans hx
  obtain ⟨S, hS⟩ : ∃ S : ℝ → ℂ, S = fun t => ∑ p ∈ primesIoc x y, (Set.Ici (p : ℝ)).indicator (fun _ => a p) t :=
    ⟨_, rfl⟩
  have hIcc : Set.uIcc x y = Set.Icc x y := Set.uIcc_of_le hxy
  have hc' : ContinuousOn (fun t => (J' t : ℂ)) (Set.Icc x y) :=
    Complex.continuous_ofReal.comp_continuousOn hc
  have hJi : IntervalIntegrable (fun t => (J' t : ℂ)) MeasureTheory.volume x y :=
    (hc'.mono hIcc.subset).intervalIntegrable
  have hterm : ∀ p ∈ primesIoc x y, IntervalIntegrable
      (fun t => a p * (Set.Ici (p : ℝ)).indicator (fun t => (J' t : ℂ)) t) MeasureTheory.volume x y :=
    fun p _ => (intervalIntegrable_indicator_Ici_of_intervalIntegrable hJi).const_mul (a p)
  have hpt : ∀ t, (J' t : ℂ) * S t
      = ∑ p ∈ primesIoc x y, a p * (Set.Ici (p : ℝ)).indicator (fun t => (J' t : ℂ)) t := by
    intro t
    rw [hS, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    by_cases h : t ∈ Set.Ici (p : ℝ)
    · simp only [Set.indicator_of_mem h]
      ring
    · simp [Set.indicator_of_notMem h]
  have hL : ∑ p ∈ primesIoc x y, a p * ((J p - J y : ℝ) : ℂ) = -∫ t in x..y, (J' t : ℂ) * S t := by
    simp_rw [hpt]
    rw [intervalIntegral.integral_finsetSum hterm, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun p hp => ?_)
    have hb := mem_primesIoc_bounds hx0 hxy hp
    rw [intervalIntegral.integral_const_mul, integral_indicator_Ici_deriv_eq_sub_of_hasDerivAt hb.1 hb.2 hJ hc]
    push_cast
    ring
  have hSi : IntervalIntegrable S MeasureTheory.volume x y := by
    have hS' : S = ∑ p ∈ primesIoc x y, (Set.Ici (p : ℝ)).indicator (fun _ => a p) := by
      rw [hS]
      funext t
      simp [Finset.sum_apply]
    rw [hS']
    exact IntervalIntegrable.sum _ (fun p _ => intervalIntegrable_indicator_Ici_of_intervalIntegrable intervalIntegrable_const)
  have hinv : ContinuousOn (fun t : ℝ => t⁻¹) (Set.uIcc x y) := by
    apply ContinuousOn.inv₀ continuousOn_id
    intro t ht
    rw [hIcc] at ht
    exact (lt_of_lt_of_le zero_lt_one (hx.trans ht.1)).ne'
  have hg : IntervalIntegrable (fun t => r * (‖S t‖ / t)) MeasureTheory.volume x y := by
    have := (hSi.norm.mul_continuousOn hinv).const_mul r
    simpa [div_eq_mul_inv] using this
  have hf : IntervalIntegrable (fun t => ‖(J' t : ℂ) * S t‖) MeasureTheory.volume x y := by
    have hsum := IntervalIntegrable.sum _ hterm
    have he : (fun t => (J' t : ℂ) * S t)
        = ∑ p ∈ primesIoc x y, (fun t => a p * (Set.Ici (p : ℝ)).indicator (fun t => (J' t : ℂ)) t) := by
      funext t
      rw [hpt, Finset.sum_apply]
    rw [← he] at hsum
    exact hsum.norm
  have hA : ∀ t ∈ Set.uIcc x y, ‖∑ p ∈ primesIoc x t, a p‖ / t = ‖S t‖ / t := by
    intro t ht
    rw [hIcc] at ht
    rw [sum_primesIoc_eq_sum_indicator a (hx0.trans ht.1) ht.2, hS]
  rw [hL, norm_neg, intervalIntegral.integral_congr hA, ← intervalIntegral.integral_const_mul]
  refine (intervalIntegral.norm_integral_le_integral_norm hxy).trans ?_
  refine intervalIntegral.integral_mono_on hxy hf hg (fun t ht => ?_)
  have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one (hx.trans ht.1)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  calc |J' t| * ‖S t‖ ≤ r / t * ‖S t‖ := mul_le_mul_of_nonneg_right (hb t ht) (norm_nonneg _)
    _ = r * (‖S t‖ / t) := by ring
end GlobalTheory.Lin
