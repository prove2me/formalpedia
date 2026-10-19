-- Prove2me | solution 1 for OAI.EntropyRateDimension.exists_nat_log_small
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T06:23:25.811724+00:00
-- url     : https://prove2.me/submissions/f081786f-82d5-4c0e-a818-4fa8aed6325e

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
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_BallIntegrability
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_CodingIntegrals
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_ErgodicAverages
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_TriangularAverages
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_BallLimits
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_RadiusGrowth
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_RadialLimit
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_ExactDimension
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_UpperBound
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Conditioning
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_PairGain
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_TypedLaw
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_TailConvolution
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteVariance
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_SuffixLaw
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_WordAverage
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_BlockWords
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_EntropyBudget
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_RetainedLoss
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_PairBands

open OAI OAI.EntropyRateDimension
universe uα uβ
open scoped BigOperators Topology
open Filter


theorem solution {ε : ℝ} (hε : 0 < ε) (K : ℝ) :
    ∃ k : ℕ, 0 < k ∧ K*Real.log (k+1) < ε*k := by
  -- log(k+1)/k → 0
  have ht : Filter.Tendsto (fun k : ℕ => Real.log ((k:ℝ)+1) / (k:ℝ)) Filter.atTop (nhds 0) := by
    have h1 := (Real.isLittleO_log_id_atTop).tendsto_div_nhds_zero
    have h2 : Filter.Tendsto (fun k : ℕ => (k:ℝ) + 1) Filter.atTop Filter.atTop :=
      Filter.tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
    have h3 := h1.comp h2
    have h4 : Filter.Tendsto (fun k : ℕ => ((k:ℝ)+1) / (k:ℝ)) Filter.atTop (nhds 1) := by
      have : Filter.Tendsto (fun k : ℕ => 1 + 1 / (k:ℝ)) Filter.atTop (nhds (1 + 0)) :=
        tendsto_const_nhds.add tendsto_one_div_atTop_nhds_zero_nat
      rw [add_zero] at this
      refine this.congr' ?_
      filter_upwards [Filter.eventually_gt_atTop 0] with k hk
      have : (k:ℝ) ≠ 0 := by exact_mod_cast hk.ne'
      field_simp
    have := h3.mul h4
    rw [zero_mul] at this
    refine this.congr' ?_
    filter_upwards [Filter.eventually_gt_atTop 0] with k hk
    have : (k:ℝ) ≠ 0 := by exact_mod_cast hk.ne'
    have : (k:ℝ) + 1 ≠ 0 := by positivity
    simp only [Function.comp, id]
    field_simp
  have hev : ∀ᶠ k : ℕ in Filter.atTop, (|K| + 1) * (Real.log ((k:ℝ)+1) / (k:ℝ)) < ε := by
    have := (tendsto_const_nhds (x := |K| + 1)).mul ht
    rw [mul_zero] at this
    exact this.eventually (gt_mem_nhds hε)
  obtain ⟨k, hk⟩ := (hev.and (Filter.eventually_gt_atTop 0)).exists
  refine ⟨k, hk.2, ?_⟩
  have hkpos : (0:ℝ) < k := by exact_mod_cast hk.2
  have hlog : 0 ≤ Real.log ((k:ℝ)+1) := Real.log_nonneg (by linarith)
  have h1 := hk.1
  rw [mul_div_assoc', div_lt_iff₀ hkpos] at h1
  have : K * Real.log ((k:ℝ)+1) ≤ (|K| + 1) * Real.log ((k:ℝ)+1) :=
    mul_le_mul_of_nonneg_right (by linarith [le_abs_self K]) hlog
  linarith

