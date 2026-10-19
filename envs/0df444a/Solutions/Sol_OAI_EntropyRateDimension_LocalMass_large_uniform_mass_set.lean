-- Prove2me | solution 1 for OAI.EntropyRateDimension.LocalMass.large_uniform_mass_set
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T06:30:00.080789+00:00
-- url     : https://prove2.me/submissions/e8f85831-e1c9-4702-b483-ea44c81541e3

import Mathlib
import Definitions.Def_SelfSimilar
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Basic
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteEntropy
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteDistribution
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_MeasureEntropy
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_RandomGrid
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Boundary
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_TranslationGain
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FairPairs
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_ProductLaw
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_GridCoupling
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteRefinement
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_SumsetBound
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_WordTypes
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_DigitSumset

open OAI OAI.EntropyRateDimension
open scoped BigOperators ENNReal
open MeasureTheory
open MeasureTheory Metric Set Filter
open scoped Topology ENNReal
theorem h41n_meas_cb (μ : Measure ℝ) [IsProbabilityMeasure μ] (q : ℝ) :
    Measurable (fun x => μ.real (Metric.closedBall x q)) := by
  have hs : MeasurableSet {p : ℝ × ℝ | dist p.2 p.1 ≤ q} :=
    (isClosed_le (continuous_snd.dist continuous_fst) continuous_const).measurableSet
  have h := measurable_measure_prodMk_left (ν := μ) hs
  exact h.ennreal_toReal

theorem solution (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {e η : ℝ} (he : 0 ≤ e) (hη : 0 < η)
    (hlocal : ∀ᵐ x ∂μ, ∃ R : ℝ, 0 < R ∧ ∀ r : ℝ, 0 < r → r < R →
      r^e ≤ μ.real (closedBall x r)) :
    ∃ E : Set ℝ, MeasurableSet E ∧ μ.real Eᶜ ≤ η ∧
      ∃ R : ℝ, 0 < R ∧ ∀ x ∈ E, ∀ r : ℝ, 0 < r → r < R →
        (r/2)^e ≤ μ.real (ball x r) := by
  classical
  let E : ℕ → Set ℝ := fun k => {x | ∀ q : ℚ, 0 < (q:ℝ) → (q:ℝ) < 1/((k:ℝ)+1) →
    (q:ℝ)^e ≤ μ.real (closedBall x q)}
  have hEm : ∀ k, MeasurableSet (E k) := by
    intro k
    simp only [E, Set.setOf_forall]
    refine MeasurableSet.iInter fun q => MeasurableSet.iInter fun _ => MeasurableSet.iInter fun _ => ?_
    exact measurableSet_le measurable_const (h41n_meas_cb μ q)
  have hmono : Monotone E := by
    intro k l hkl x hx q hq hql
    apply hx q hq (lt_of_lt_of_le hql _)
    apply one_div_le_one_div_of_le (by positivity)
    have : (k:ℝ) ≤ l := by exact_mod_cast hkl
    linarith
  have hcov : ∀ᵐ x ∂μ, x ∈ ⋃ k, E k := by
    filter_upwards [hlocal] with x hx
    obtain ⟨R, hR, h⟩ := hx
    obtain ⟨k, hk⟩ := exists_nat_one_div_lt hR
    exact Set.mem_iUnion.mpr ⟨k, fun q hq hqk => h q hq (hqk.trans hk)⟩
  have hnull : μ (⋂ k, (E k)ᶜ) = 0 := by
    rw [← Set.compl_iUnion]
    exact ae_iff.mp hcov
  have ht : Tendsto (fun k => μ (E k)ᶜ) atTop (𝓝 (μ (⋂ k, (E k)ᶜ))) :=
    tendsto_measure_iInter_atTop (fun k => (hEm k).compl.nullMeasurableSet)
      (fun k l hkl => Set.compl_subset_compl.mpr (hmono hkl)) ⟨0, measure_ne_top _ _⟩
  rw [hnull] at ht
  have hev := ht.eventually (gt_mem_nhds (ENNReal.ofReal_pos.mpr hη))
  obtain ⟨k, hk⟩ := hev.exists
  refine ⟨E k, hEm k, ?_, 2/((k:ℝ)+1), by positivity, ?_⟩
  · exact ENNReal.toReal_le_of_le_ofReal hη.le hk.le
  · intro x hx r hr hrR
    have h1 : r/2 < min r (1/((k:ℝ)+1)) := by
      apply lt_min (by linarith)
      have : r/2 < 1/((k:ℝ)+1) := by
        rw [lt_div_iff₀ (by positivity)]
        rw [lt_div_iff₀ (by positivity)] at hrR
        linarith
      exact this
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn h1
    have hq0 : 0 < (q:ℝ) := by linarith
    calc (r/2)^e ≤ (q:ℝ)^e := Real.rpow_le_rpow (by linarith) hq1.le he
      _ ≤ μ.real (closedBall x q) := hx q hq0 (lt_of_lt_of_le hq2 (min_le_right _ _))
      _ ≤ μ.real (Metric.ball x r) :=
          measureReal_mono (Metric.closedBall_subset_ball (lt_of_lt_of_le hq2 (min_le_left _ _)))

