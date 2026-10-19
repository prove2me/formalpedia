-- Prove2me | solution 2 for OAI.EntropyRateDimension.Typed.exists_common_horizon
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T12:12:14.163997+00:00
-- url     : https://prove2.me/submissions/6dd42fdd-bcb6-4c4a-bde7-6c2c0f2a89c4

-- Generated from openai/math@1581d4c lean/OAI/MeasureTheory/SelfSimilar/BandSelection.lean:L80-L99
-- (upload_full_project.md Phase 4): solution for node OAI.EntropyRateDimension.Typed.exists_common_horizon. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
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

-- ---- from OAI.MeasureTheory.SelfSimilar.BandSelection ----
namespace OAI

universe uα uβ

namespace EntropyRateDimension.Typed
open scoped BigOperators

variable {α : Type uα} {β : Type uβ} [Fintype α] [DecidableEq β]

theorem exists_common_horizon {q : ℕ} (n : Fin q → ℕ) (hn : ∀ i, 0 < n i) (B : Fin q → ℤ) :
    ∃ H : ℕ, 0 < H ∧ (∀ i, n i ∣ H) ∧ (∀ i, B i ≤ (H : ℤ)) := by
  classical
  let P := ∏ i, n i
  let R := 1+∑ i, (B i).toNat
  have hP : 0 < P := Finset.prod_pos (fun i _ => hn i)
  have hR : 0 < R := by dsimp [R]; omega
  refine ⟨R*P,Nat.mul_pos hR hP,?_,?_⟩
  · intro i
    exact dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem n (Finset.mem_univ i)) R
  · intro i
    have hBi : (B i).toNat ≤ ∑ i, (B i).toNat := Finset.single_le_sum (fun j _ => Nat.zero_le ((B j).toNat)) (Finset.mem_univ i)
    have hle : (B i).toNat ≤ R*P := by
      have hP1 : 1 ≤ P := hP
      have hRP : R ≤ R*P := by simpa only [mul_one] using Nat.mul_le_mul_left R hP1
      apply le_trans _ hRP
      dsimp only [R]
      omega
    have hh : ((B i).toNat : ℤ) ≤ ((R*P : ℕ) : ℤ) := by exact_mod_cast hle
    omega

end EntropyRateDimension.Typed

end OAI

-- ---- platform node ----
open OAI OAI.EntropyRateDimension OAI.EntropyRateDimension.Typed
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.EntropyRateDimension.Typed.exists_common_horizon := @_root_.OAI.EntropyRateDimension.Typed.exists_common_horizon
