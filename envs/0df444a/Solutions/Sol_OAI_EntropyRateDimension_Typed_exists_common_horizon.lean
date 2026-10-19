-- Prove2me | solution 1 for OAI.EntropyRateDimension.Typed.exists_common_horizon
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T06:23:09.209994+00:00
-- url     : https://prove2.me/submissions/1b3cdbfe-0a8a-4eba-91b4-43072a379b8f

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
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_WindowCount
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_WindowGain

open OAI OAI.EntropyRateDimension OAI.EntropyRateDimension.Typed
universe uα uβ
open scoped BigOperators
variable {α : Type uα} {β : Type uβ} [Fintype α] [DecidableEq β]


theorem solution {q : ℕ} (n : Fin q → ℕ) (hn : ∀ i, 0 < n i) (B : Fin q → ℤ) :
    ∃ H : ℕ, 0 < H ∧ (∀ i, n i ∣ H) ∧ (∀ i, B i ≤ (H : ℤ)) := by
  classical
  refine ⟨(∏ i, n i) * (1 + ∑ i, (B i).toNat), ?_, ?_, ?_⟩
  · apply Nat.mul_pos (Finset.prod_pos (fun i _ => hn i)) (by omega)
  · intro i
    exact Dvd.dvd.mul_right (Finset.dvd_prod_of_mem n (Finset.mem_univ i)) _
  · intro i
    have h1 : 1 ≤ ∏ i, n i := Finset.prod_pos (fun i _ => hn i)
    have h2 : (B i).toNat ≤ ∑ i, (B i).toNat :=
      Finset.single_le_sum (f := fun i => (B i).toNat) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    have h3 : B i ≤ ((B i).toNat : ℤ) := Int.self_le_toNat (B i)
    have h4 : (B i).toNat ≤ (∏ i, n i) * (1 + ∑ i, (B i).toNat) := by nlinarith
    calc B i ≤ ((B i).toNat : ℤ) := h3
      _ ≤ _ := by exact_mod_cast h4

