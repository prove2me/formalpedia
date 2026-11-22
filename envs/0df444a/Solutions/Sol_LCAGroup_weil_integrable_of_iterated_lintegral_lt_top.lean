-- Prove2me | solution 1 for LCAGroup.weil_integrable_of_iterated_lintegral_lt_top
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T15:40:18.876693+00:00
-- url     : https://prove2.me/submissions/3e789e2b-d9c9-4505-96fc-ebbe48b21491

import Mathlib
import Theorems.Thm_LCAGroup_weil_quotient_integral_formula

open MeasureTheory Topology

set_option autoImplicit false

open LCAGroup

theorem solution
    (G : Type*) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (H : Subgroup G) (hH : IsClosed (H : Set G))
    [MeasurableSpace (G ⧸ H)] [BorelSpace (G ⧸ H)]
    (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular] [SigmaFinite μ]
    (μH : Measure H) [μH.IsHaarMeasure] [μH.Regular]
    (ν : Measure (G ⧸ H)) [ν.IsHaarMeasure] [ν.Regular]
    (hν : ∀ φ : G → ℂ, Continuous φ → HasCompactSupport φ →
      ∫ x, φ x ∂μ = ∫ q : G ⧸ H, (∫ h : H, φ (q.out * (h : G)) ∂μH) ∂ν)
    (f : G → ℂ) (hf : AEStronglyMeasurable f μ)
    (hfin : ∫⁻ q : G ⧸ H, (∫⁻ h : H, ‖f (q.out * (h : G))‖ₑ ∂μH) ∂ν < ⊤) :
    Integrable f μ ∧
    ∫ x, f x ∂μ = ∫ q : G ⧸ H, (∫ h : H, f (q.out * (h : G)) ∂μH) ∂ν := by
  classical
  -- Truncations of `‖f‖` along the spanning sets of the σ-finite measure `μ`.
  let S : ℕ → Set G := spanningSets μ
  let r : ℕ → G → ℝ := fun n x => (S n).indicator (fun y => min ‖f y‖ (n : ℝ)) x
  have hr_nonneg : ∀ n x, 0 ≤ r n x := fun n x =>
    Set.indicator_nonneg (fun y _ => le_min (norm_nonneg _) (Nat.cast_nonneg n)) x
  have hr_le : ∀ n x, r n x ≤ ‖f x‖ := fun n x => by
    by_cases hx : x ∈ S n
    · simp only [r, Set.indicator_of_mem hx]; exact min_le_left _ _
    · simp only [r, Set.indicator_of_notMem hx]; exact norm_nonneg _
  have hr_mono : ∀ x, Monotone fun n => r n x := fun x m n hmn => by
    by_cases hx : x ∈ S m
    · have hx' : x ∈ S n := monotone_spanningSets μ hmn hx
      simp only [r, Set.indicator_of_mem hx, Set.indicator_of_mem hx']
      exact min_le_min_left _ (Nat.cast_le.mpr hmn)
    · simp only [r, Set.indicator_of_notMem hx]; exact hr_nonneg n x
  have hr_int : ∀ n, Integrable (r n) μ := by
    intro n
    have hm : MeasurableSet (S n) := measurableSet_spanningSets μ n
    have : IsFiniteMeasure (μ.restrict (S n)) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact measure_spanningSets_lt_top μ n⟩
    refine IntegrableOn.integrable_indicator ?_ hm
    have hmeas : AEStronglyMeasurable (fun y => min ‖f y‖ (n : ℝ)) μ :=
      (continuous_id.min continuous_const).comp_aestronglyMeasurable hf.norm
    refine Integrable.of_bound hmeas.restrict (n : ℝ) ?_
    refine Filter.Eventually.of_forall fun y => ?_
    rw [Real.norm_of_nonneg (le_min (norm_nonneg _) (Nat.cast_nonneg n))]
    exact min_le_right _ _
  -- Each truncation is controlled by the iterated integral, via Weil's L¹ formula.
  have key : ∀ n, ENNReal.ofReal (∫ x, r n x ∂μ) ≤
      ∫⁻ q : G ⧸ H, (∫⁻ h : H, ‖f (q.out * (h : G))‖ₑ ∂μH) ∂ν := by
    intro n
    have hW := (weil_quotient_integral_formula G H hH μ μH ν hν
      (fun x => (r n x : ℂ)) (hr_int n).ofReal).2.2
    have h1 : ENNReal.ofReal (∫ x, r n x ∂μ) = ‖∫ x, (r n x : ℂ) ∂μ‖ₑ := by
      rw [integral_complex_ofReal, ← ofReal_norm, Complex.norm_real,
        Real.norm_of_nonneg (integral_nonneg (hr_nonneg n))]
    rw [h1, hW]
    calc ‖∫ q : G ⧸ H, (∫ h : H, (r n (q.out * (h : G)) : ℂ) ∂μH) ∂ν‖ₑ
        ≤ ∫⁻ q : G ⧸ H, ‖∫ h : H, (r n (q.out * (h : G)) : ℂ) ∂μH‖ₑ ∂ν :=
          enorm_integral_le_lintegral_enorm _
      _ ≤ ∫⁻ q : G ⧸ H, (∫⁻ h : H, ‖(r n (q.out * (h : G)) : ℂ)‖ₑ ∂μH) ∂ν :=
          lintegral_mono fun q => enorm_integral_le_lintegral_enorm _
      _ ≤ ∫⁻ q : G ⧸ H, (∫⁻ h : H, ‖f (q.out * (h : G))‖ₑ ∂μH) ∂ν := by
          refine lintegral_mono fun q => lintegral_mono fun h => ?_
          rw [← ofReal_norm, ← ofReal_norm, Complex.norm_real,
            Real.norm_of_nonneg (hr_nonneg n _)]
          exact ENNReal.ofReal_le_ofReal (hr_le n _)
  -- Monotone convergence: `∫⁻ ‖f‖ₑ = ⨆ n, ∫⁻ ofReal (r n)`.
  have hsup : ∀ x, ‖f x‖ₑ = ⨆ n, ENNReal.ofReal (r n x) := by
    intro x
    apply le_antisymm
    · let n : ℕ := max (spanningSetsIndex μ x) ⌈‖f x‖⌉₊
      have hxS : x ∈ S n := mem_spanningSets_of_index_le μ x (le_max_left _ _)
      have hn : ‖f x‖ ≤ (n : ℝ) :=
        (Nat.le_ceil _).trans (Nat.cast_le.mpr (le_max_right _ _))
      have hrn : r n x = ‖f x‖ := by
        simp only [r, Set.indicator_of_mem hxS]; exact min_eq_left hn
      rw [← ofReal_norm, ← hrn]
      exact le_iSup (fun n => ENNReal.ofReal (r n x)) n
    · refine iSup_le fun n => ?_
      rw [← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal (hr_le n x)
  have hlint : ∫⁻ x, ‖f x‖ₑ ∂μ ≤
      ∫⁻ q : G ⧸ H, (∫⁻ h : H, ‖f (q.out * (h : G))‖ₑ ∂μH) ∂ν := by
    rw [lintegral_congr (fun x => hsup x),
      lintegral_iSup' (fun n => (hr_int n).aemeasurable.ennreal_ofReal)
        (Filter.Eventually.of_forall fun x m n hmn =>
          ENNReal.ofReal_le_ofReal (hr_mono x hmn))]
    refine iSup_le fun n => ?_
    rw [← ofReal_integral_eq_lintegral_ofReal (hr_int n)
      (Filter.Eventually.of_forall (hr_nonneg n))]
    exact key n
  have hint : Integrable f μ :=
    ⟨hf, hasFiniteIntegral_iff_enorm.mpr (lt_of_le_of_lt hlint hfin)⟩
  exact ⟨hint, (weil_quotient_integral_formula G H hH μ μH ν hν f hint).2.2⟩
