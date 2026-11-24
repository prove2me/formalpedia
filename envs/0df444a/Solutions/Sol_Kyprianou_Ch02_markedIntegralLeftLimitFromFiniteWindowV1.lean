-- Prove2me | solution 1 for Kyprianou.Ch02.markedIntegralLeftLimitFromFiniteWindowV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T22:57:41.802944+00:00
-- url     : https://prove2.me/submissions/7017567b-ec5a-41c8-b757-21e791853ed7

import Theorems.Thm_Kyprianou_Ch02_markedIocIndicatorTendstoLeftV1
import Definitions.Def_Kyprianou_Ch02_CompensatedSmallJumpBand
import Definitions.Def_Kyprianou_Ch02_CompletedPoissonFiltration
import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_Construction
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch02_IndependentComponents
import Definitions.Def_Kyprianou_Ch02_LargeJumpProcess

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    (μ : Measure (ℝ × ℝ)) (A : Set ℝ) (hA : MeasurableSet A)
    (hsmall : ∀ x ∈ A, |x| < 1)
    (T t : ℝ≥0) (htT : t ≤ T)
    (hfin : μ (Set.Ioc (0 : ℝ) (T : ℝ) ×ˢ A) < ⊤) :
    Tendsto (fun s : ℝ≥0 => ∫ z in Set.Ioc (0 : ℝ) (s : ℝ) ×ˢ A, z.2 ∂μ)
      (nhdsWithin t (Set.Iio t))
      (nhds (∫ z in Set.Ioo (0 : ℝ) (t : ℝ) ×ˢ A, z.2 ∂μ)) := by
  let R (s : ℝ≥0) : Set (ℝ × ℝ) := Set.Ioc (0 : ℝ) (s : ℝ) ×ˢ A
  let L : Set (ℝ × ℝ) := Set.Ioo (0 : ℝ) (t : ℝ) ×ˢ A
  let ρ := μ.restrict (R T)
  let F (s : ℝ≥0) : ℝ × ℝ → ℝ := (R s).indicator Prod.snd
  let f : ℝ × ℝ → ℝ := L.indicator Prod.snd
  have hR (s : ℝ≥0) : MeasurableSet (R s) := measurableSet_Ioc.prod hA
  have hL : MeasurableSet L := measurableSet_Ioo.prod hA
  letI : IsFiniteMeasure ρ := ⟨by simpa [ρ, Measure.restrict_apply_univ] using hfin⟩
  have hle (s : ℝ≥0) (hs : s ≤ T) : R s ⊆ R T := by
    intro z hz
    exact ⟨⟨hz.1.1, hz.1.2.trans (by exact_mod_cast hs)⟩, hz.2⟩
  have hLt : L ⊆ R t := fun _ hz => ⟨⟨hz.1.1, hz.1.2.le⟩, hz.2⟩
  have hstay : ∀ᶠ s in nhdsWithin t (Set.Iio t), s < t := self_mem_nhdsWithin
  have hlim : Tendsto (fun s => ∫ z, F s z ∂ρ)
      (nhdsWithin t (Set.Iio t)) (nhds (∫ z, f z ∂ρ)) := by
    apply tendsto_integral_filter_of_dominated_convergence (fun _ => (1 : ℝ))
    · exact Eventually.of_forall fun s =>
        (measurable_snd.indicator (hR s)).aestronglyMeasurable
    · filter_upwards [] with s
      filter_upwards [ae_restrict_mem (hR T)] with z hz
      by_cases hz' : z ∈ R s
      · simpa [F, hz', Real.norm_eq_abs] using (hsmall z.2 hz.2).le
      · simp [F, hz']
    · exact integrable_const _
    · exact Eventually.of_forall (Kyprianou.Ch02.markedIocIndicatorTendstoLeftV1 A t)
  have hleft : (∫ z, f z ∂ρ) = ∫ z in L, z.2 ∂μ := by
    rw [show f = L.indicator Prod.snd from rfl, integral_indicator hL]
    change ∫ z, z.2 ∂(ρ.restrict L) = _
    rw [show ρ.restrict L = μ.restrict L from
      Measure.restrict_restrict_of_subset (hLt.trans (hle t htT))]
  rw [hleft] at hlim
  apply hlim.congr'
  filter_upwards [hstay] with s hs
  rw [show F s = (R s).indicator Prod.snd from rfl, integral_indicator (hR s)]
  change ∫ z, z.2 ∂(ρ.restrict (R s)) = _
  rw [show ρ.restrict (R s) = μ.restrict (R s) from
    Measure.restrict_restrict_of_subset (hle s (hs.le.trans htT))]
