-- Prove2me | solution 1 for OAI.EntropyRateDimension.BallRatios.logRatio_bounds
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T06:12:21.529371+00:00
-- url     : https://prove2.me/submissions/e558b9d4-6353-47a9-b799-857d7eef8da2

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
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Bernoulli
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Coding
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_InvariantLaw
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_BallRatios

open OAI OAI.EntropyRateDimension OAI.EntropyRateDimension.BallRatios
open scoped BigOperators ENNReal
open MeasureTheory
open MeasureTheory Metric Set Filter
open scoped Topology ENNReal
open MeasureTheory Filter Set ProbabilityTheory
open scoped Topology
open MeasureTheory Metric Set Filter
open scoped ENNReal Topology
theorem h41n_ball_tendsto (μ : Measure ℝ) [IsFiniteMeasure μ] (x r : ℝ) :
    Tendsto (fun q => μ (closedBall x q)) (𝓝[>] r) (𝓝 (μ (closedBall x r))) := by
  have h := tendsto_measure_biInter_gt (μ := μ) (s := fun q => closedBall x q) (a := r)
    (fun q _ => measurableSet_closedBall.nullMeasurableSet)
    (fun i j _ hij => Metric.closedBall_subset_closedBall hij)
    ⟨r+1, by linarith, measure_ne_top _ _⟩
  rw [biInter_gt_closedBall] at h
  exact h

theorem solution (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hν : ν ≤ μ) : ∀ᵐ x ∂ν, ∀ r : ℝ, 0 < r → r < 1 →
      0 ≤ logRatio μ ν x r ∧ logRatio μ ν x r ≤ logEnvelope μ ν x := by
  filter_upwards [Besicovitch.ae_tendsto_rnDeriv μ ν, Measure.rnDeriv_lt_top μ ν,
    (Measure.support_mem_ae : ν.support ∈ ae ν)] with x hx htop hsupp
  have hνpos : ∀ r, 0 < r → 0 < ν (closedBall x r) := fun r hr =>
    (Measure.mem_support_iff_forall x).mp hsupp _ (closedBall_mem_nhds x hr)
  have hge1 : ∀ r, 0 < r → 1 ≤ μ (closedBall x r) / ν (closedBall x r) := fun r hr => by
    rw [ENNReal.le_div_iff_mul_le (Or.inl (hνpos r hr).ne') (Or.inl (measure_ne_top _ _)), one_mul]
    exact Measure.le_iff'.1 hν _
  have hfin : ∀ r, 0 < r → μ (closedBall x r) / ν (closedBall x r) ≠ ⊤ := fun r hr =>
    ENNReal.div_ne_top (measure_ne_top _ _) (hνpos r hr).ne'
  have hMfin : maximal μ ν x ≠ ⊤ := by
    have hev : ∀ᶠ r in 𝓝[>] (0:ℝ),
        μ (closedBall x r) / ν (closedBall x r) < μ.rnDeriv ν x + 1 :=
      hx.eventually (gt_mem_nhds (ENNReal.lt_add_right htop.ne one_ne_zero))
    obtain ⟨u, hu, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hev
    have hu0 : (0:ℝ) < u := hu
    have h1 : μ.rnDeriv ν x + 1 ≠ ⊤ := ENNReal.add_ne_top.2 ⟨htop.ne, ENNReal.one_ne_top⟩
    have h2 : μ univ / ν (closedBall x (u/2)) ≠ ⊤ :=
      ENNReal.div_ne_top (measure_ne_top _ _) (hνpos _ (by linarith)).ne'
    apply ne_top_of_le_ne_top (max_lt h1.lt_top h2.lt_top).ne
    unfold maximal
    apply iSup_le
    intro q
    rcases lt_or_ge (q.val : ℝ) u with hq | hq
    · exact le_max_of_le_left (hsub ⟨q.property.1, hq⟩).le
    · apply le_max_of_le_right
      exact ENNReal.div_le_div (measure_mono (Set.subset_univ _))
        (measure_mono (Metric.closedBall_subset_closedBall (by linarith)))
  have hRle : ∀ r, 0 < r → r < 1 → μ (closedBall x r) / ν (closedBall x r) ≤ maximal μ ν x := by
    intro r hr hr1
    by_contra hlt
    rw [not_le] at hlt
    have ht := ENNReal.Tendsto.div (h41n_ball_tendsto μ x r) (Or.inr (hνpos r hr).ne') (h41n_ball_tendsto ν x r)
      (Or.inl (measure_ne_top _ _))
    have hev := ht.eventually (lt_mem_nhds hlt)
    have hev2 : ∀ᶠ q in 𝓝[>] r, q < 1 := (eventually_lt_nhds hr1).filter_mono nhdsWithin_le_nhds
    obtain ⟨u, hu, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp (hev.and hev2)
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show r < u from hu)
    have hqm := hsub ⟨hq1, hq2⟩
    have hle : μ (closedBall x (q:ℝ)) / ν (closedBall x (q:ℝ)) ≤ maximal μ ν x := by
      unfold maximal
      exact le_iSup (fun q : Radius => μ (closedBall x (q.val : ℝ)) / ν (closedBall x (q.val : ℝ)))
        ⟨q, by linarith, hqm.2.le⟩
    exact absurd hle (not_le.mpr hqm.1)
  intro r hr hr1
  have hT : 1 ≤ (μ (closedBall x r) / ν (closedBall x r)).toReal := by
    simpa using ENNReal.toReal_mono (hfin r hr) (hge1 r hr)
  unfold logRatio logEnvelope
  refine ⟨Real.log_nonneg hT, le_max_of_le_right ?_⟩
  exact Real.log_le_log (by linarith) (ENNReal.toReal_mono hMfin (hRle r hr hr1))

