-- Prove2me | solution 1 for OAI.EntropyRateDimension.Windows.multiples_disjoint
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T05:50:15.988767+00:00
-- url     : https://prove2.me/submissions/3973c885-4f1e-4af6-86a5-557fcb1894d4

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

open OAI OAI.EntropyRateDimension
universe uα
open scoped BigOperators ENNReal
open MeasureTheory


theorem solution {n j k : ℕ} (hjk : j ≠ k) :
    Disjoint (Finset.Ico (j * n) (j * n + n)) (Finset.Ico (k * n) (k * n + n)) := by
  rw [Finset.disjoint_left]
  intro x hx hy
  simp only [Finset.mem_Ico] at hx hy
  rcases Nat.lt_or_gt_of_ne hjk with h | h
  · have h1 : (j+1)*n ≤ k*n := Nat.mul_le_mul_right _ h
    rw [add_mul, one_mul] at h1
    omega
  · have h1 : (k+1)*n ≤ j*n := Nat.mul_le_mul_right _ h
    rw [add_mul, one_mul] at h1
    omega

