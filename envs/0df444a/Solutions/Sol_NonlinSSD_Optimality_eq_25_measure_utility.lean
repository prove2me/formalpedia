-- Prove2me | solution 1 for NonlinSSD.Optimality.eq_25_measure_utility
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-07T04:05:07.747391+00:00
-- url     : https://prove2.me/submissions/da0cb1c1-e0db-439f-968a-0aa2cda74fa0

import Mathlib
import Definitions.Def_NonlinSSD_Optimality_Basic
import Theorems.Thm_DualSSD_Duality_secondPerformance_eq_expectedShortfall

open MeasureTheory NonlinSSD.Optimality

theorem nl2_neg_u_eq (a b : ℝ) (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hsupp : μ (Set.Icc a b)ᶜ = 0) (t : ℝ) :
    -uOfMeasure μ b t = ∫ η in Set.Icc a b, max (η - t) 0 ∂μ := by
  have hres : μ.restrict (Set.Icc a b) = μ :=
    Measure.restrict_eq_self_of_ae_mem (measure_eq_zero_iff_ae_notMem.1 hsupp |>.mono
      (fun x hx => by simpa using hx))
  unfold uOfMeasure
  split_ifs with htb
  · rw [neg_neg, intervalIntegral.integral_of_le htb.le]
    -- μ.real (Icc τ b) as an integral
    have h1 : ∀ τ, μ.real (Set.Icc τ b) =
        ∫ η, (Set.Icc τ b).indicator (fun _ => (1 : ℝ)) η ∂μ := fun τ =>
      (integral_indicator_one measurableSet_Icc).symm
    simp_rw [h1]
    set F : ℝ → ℝ → ℝ := fun τ η => (Set.Icc τ b).indicator (fun _ => (1 : ℝ)) η with hF
    have hS : MeasurableSet {p : ℝ × ℝ | p.1 ≤ p.2 ∧ p.2 ≤ b} :=
      (measurableSet_le measurable_fst measurable_snd).inter
        (measurableSet_le measurable_snd measurable_const)
    have hFu : Function.uncurry F = {p : ℝ × ℝ | p.1 ≤ p.2 ∧ p.2 ≤ b}.indicator (fun _ => 1) := by
      funext p
      simp only [Function.uncurry, F, Set.indicator, Set.mem_Icc, Set.mem_ofPred_eq]
    have hint : Integrable (Function.uncurry F) ((volume.restrict (Set.Ioc t b)).prod μ) := by
      rw [hFu]; exact (integrable_const (1 : ℝ)).indicator hS
    rw [integral_integral_swap hint]
    rw [hres]
    have hae : ∀ᵐ η ∂μ, η ∈ Set.Icc a b :=
      measure_eq_zero_iff_ae_notMem.1 hsupp |>.mono (fun x hx => by simpa using hx)
    refine integral_congr_ae (hae.mono (fun η hη => ?_))
    have e1 : ∫ τ in Set.Ioc t b, F τ η = ∫ τ in Set.Ioc t b, (Set.Iic η).indicator (fun _ => (1:ℝ)) τ := by
      refine setIntegral_congr_fun measurableSet_Ioc (fun τ hτ => ?_)
      simp only [F, Set.indicator, Set.mem_Icc, Set.mem_Iic]
      by_cases h : τ ≤ η
      · simp [h, hη.2]
      · simp [h]
    show ∫ τ in Set.Ioc t b, F τ η = max (η - t) 0
    rw [e1, integral_indicator_const (1:ℝ) measurableSet_Iic, smul_eq_mul, mul_one,
      measureReal_restrict_apply measurableSet_Iic]
    have e2 : Set.Iic η ∩ Set.Ioc t b = Set.Ioc t η := by
      ext τ; simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Ioc]
      constructor
      · rintro ⟨h1, h2, -⟩; exact ⟨h2, h1⟩
      · rintro ⟨h1, h2⟩; exact ⟨h2, h1, h2.trans hη.2⟩
    rw [e2, Real.volume_real_Ioc]
  · push Not at htb
    rw [neg_zero]
    symm
    rw [setIntegral_congr_fun measurableSet_Icc (g := fun _ => (0:ℝ)) (fun η hη => by
      simp only; exact max_eq_right (by linarith [hη.2]))]
    simp

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (a b : ℝ) (hab : a ≤ b) (μ : Measure ℝ)
    (hfinite : μ Set.univ < ⊤)
    (hsupp : μ (Set.Icc a b)ᶜ = 0)
    (X : Ω → ℝ) (hX : Integrable X P) :
    (∫ η in Set.Icc a b, F2 P X η ∂μ) =
      -(∫ ω, uOfMeasure μ b (X ω) ∂P) := by
  have : IsFiniteMeasure μ := ⟨hfinite⟩
  have hF2 : ∀ η, F2 P X η = ∫ ω, max (η - X ω) 0 ∂P := fun η =>
    (DualSSD.Duality.secondPerformance_eq_expectedShortfall P X hX η).2
  have e0 : (∫ η in Set.Icc a b, F2 P X η ∂μ) =
      ∫ η in Set.Icc a b, ∫ ω, max (η - X ω) 0 ∂P ∂μ :=
    integral_congr_ae (ae_of_all _ (fun η => hF2 η))
  set ν := μ.restrict (Set.Icc a b) with hν
  have habs : Integrable (fun η : ℝ => |η|) ν :=
    continuous_abs.continuousOn.integrableOn_compact isCompact_Icc
  have hint : Integrable (Function.uncurry fun (η : ℝ) (ω : Ω) => max (η - X ω) 0)
      (ν.prod P) := by
    refine Integrable.mono' ((habs.comp_fst P).add (hX.abs.comp_snd ν)) ?_ ?_
    · have hm : AEStronglyMeasurable (fun p : ℝ × Ω => (p.1, X p.2)) (ν.prod P) :=
        measurable_fst.aestronglyMeasurable.prodMk hX.1.comp_snd
      exact (by fun_prop : Continuous fun q : ℝ × ℝ => max (q.1 - q.2) 0).comp_aestronglyMeasurable hm
    · refine ae_of_all _ (fun p => ?_)
      simp only [Function.uncurry, Real.norm_eq_abs, Pi.add_apply]
      rw [abs_of_nonneg (le_max_right _ _)]
      refine max_le ?_ (by positivity)
      linarith [le_abs_self p.1, neg_abs_le (X p.2)]
  rw [e0, integral_integral_swap hint, ← integral_neg]
  refine integral_congr_ae (ae_of_all _ (fun ω => ?_))
  exact (nl2_neg_u_eq a b μ hsupp (X ω)).symm
