-- Prove2me | solution 1 for GraphonMF.DenseLLN.coupling_bound
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T01:45:24.909485+00:00
-- url     : https://prove2.me/submissions/3cf0cd01-ce8b-4884-a0a6-6218c0c6d2f9

import Mathlib
import Definitions.Def_GraphonMF_DenseLLN_Setting

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

open GraphonMF.DenseLLN in
theorem solution {T : ℝ≥0} {d : ℕ} (n : ℕ) (hn : 0 < n) (x y : Fin n → GraphonMF.Stability.Cd T d) :
    GraphonMF.Stability.W2T (empiricalMeasure x) (empiricalMeasure y) ^ 2 ≤
      (1 / (n : ℝ≥0∞)) * ∑ i : Fin n, ‖x i - y i‖ₑ ^ 2 := by
  set π : Measure (GraphonMF.Stability.Cd T d × GraphonMF.Stability.Cd T d) :=
    (n : ℝ≥0∞)⁻¹ • ∑ i, Measure.dirac (x i, y i) with hπ
  have h1 : π.map Prod.fst = empiricalMeasure x := by
    simp only [hπ, empiricalMeasure, Measure.map_smul]
    rw [Measure.map_finset_sum' measurable_fst.aemeasurable]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Measure.map_dirac' measurable_fst]
  have h2 : π.map Prod.snd = empiricalMeasure y := by
    simp only [hπ, empiricalMeasure, Measure.map_smul]
    rw [Measure.map_finset_sum' measurable_snd.aemeasurable]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Measure.map_dirac' measurable_snd]
  have hint : ∫⁻ p, ENNReal.ofReal (‖p.1 - p.2‖ ^ (2 : ℝ)) ∂π =
      (1 / (n : ℝ≥0∞)) * ∑ i : Fin n, ‖x i - y i‖ₑ ^ 2 := by
    rw [hπ, lintegral_smul_measure, lintegral_finsetSum_measure]
    simp only [lintegral_dirac, one_div, smul_eq_mul]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Real.rpow_two, ← ofReal_norm, ENNReal.ofReal_pow (norm_nonneg _)]
  have hle : (⨅ (π' : Measure (GraphonMF.Stability.Cd T d × GraphonMF.Stability.Cd T d))
      (_ : π'.map Prod.fst = empiricalMeasure x ∧ π'.map Prod.snd = empiricalMeasure y),
      ∫⁻ p, ENNReal.ofReal (‖p.1 - p.2‖ ^ (2 : ℝ)) ∂π') ≤
      (1 / (n : ℝ≥0∞)) * ∑ i : Fin n, ‖x i - y i‖ₑ ^ 2 := by
    rw [← hint]
    exact iInf₂_le π ⟨h1, h2⟩
  unfold GraphonMF.Stability.W2T WassersteinDRO.Duality.wassersteinDistance
  set A := (⨅ (π' : Measure (GraphonMF.Stability.Cd T d × GraphonMF.Stability.Cd T d))
      (_ : π'.map Prod.fst = empiricalMeasure x ∧ π'.map Prod.snd = empiricalMeasure y),
      ∫⁻ p, ENNReal.ofReal (‖p.1 - p.2‖ ^ (2 : ℝ)) ∂π')
  have : (A ^ (1 / (2 : ℝ))) ^ 2 = A := by
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    norm_num
  rw [this]
  exact hle
