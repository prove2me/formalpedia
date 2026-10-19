-- Prove2me | solution 1 for OAI.EntropyRateDimension.MeasureEntropy.CompactlyCarried.mixture
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T05:19:15.336866+00:00
-- url     : https://prove2.me/submissions/d1f64242-1722-4106-837e-1cd571483429

import Mathlib
import Definitions.Def_SelfSimilar
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Basic
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteEntropy
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteDistribution
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_MeasureEntropy

open OAI OAI.EntropyRateDimension OAI.EntropyRateDimension.MeasureEntropy
universe uι uα uβ uγ uδ
open scoped BigOperators ENNReal
open MeasureTheory


theorem solution {ι : Type uι} [Fintype ι]
    (ν : ι → Measure ℝ) (hν : ∀ i, CompactlyCarried (ν i)) (w : ι → ℝ) :
    CompactlyCarried (∑ i, ENNReal.ofReal (w i) • ν i) := by
  choose B hB0 hB using hν
  refine ⟨∑ i, B i, Finset.sum_nonneg (fun i _ => hB0 i), ?_⟩
  simp only [Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply]
  apply Finset.sum_eq_zero
  intro i _
  have hle : B i ≤ ∑ j, B j := Finset.single_le_sum (fun j _ => hB0 j) (Finset.mem_univ i)
  rw [measure_mono_null (Set.compl_subset_compl.mpr (Set.Icc_subset_Icc (by linarith) hle)) (hB i),
    smul_zero]

