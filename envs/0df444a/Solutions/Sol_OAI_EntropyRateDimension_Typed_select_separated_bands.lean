-- Prove2me | solution 1 for OAI.EntropyRateDimension.Typed.select_separated_bands
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T06:33:04.637446+00:00
-- url     : https://prove2.me/submissions/02fb9b3e-a154-4354-ba0d-a6a85d8d6c1c

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


theorem solution (S : System α) (tag : α → β)
    {A A' c : ℝ} (hA : 0 < A) (hAA : A' < A) {N : ℕ}
    (hb : ∀ n, N ≤ n → ∃ B : ℤ, bandStart A n ≤ B ∧
      c*n ≤ pairBudget S tag A' (bandStart A n) B n) (q : ℕ) :
    ∃ n : Fin q → ℕ, ∃ B : Fin q → ℤ,
      (∀ i, 0 < n i) ∧ (∀ i, 1 ≤ bandStart A (n i)) ∧
      (∀ i, c*n i ≤ pairBudget S tag A' (bandStart A (n i)) (B i) (n i)) ∧
      (∀ i h : Fin q, h < i → (B h : ℝ)<(bandStart A (n i) : ℝ)-A'*n i-1) := by
  have hAA' : 0 < A - A' := by linarith
  induction q with
  | zero => exact ⟨fun i => i.elim0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0,
      fun i => i.elim0, fun i => i.elim0⟩
  | succ q ih =>
    obtain ⟨n0, B0, h1, h2, h3, h4⟩ := ih
    set M : ℝ := ∑ h, |(B0 h : ℝ)| with hM
    obtain ⟨m, hm⟩ := exists_nat_gt ((M + 3)/(A - A') + 1/A)
    have hM0 : 0 ≤ M := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
    have hX : 0 ≤ (M+3)/(A-A') := div_nonneg (by linarith) hAA'.le
    have hY : 0 < 1/A := by positivity
    set nn := m + N + 1 with hnn
    have hnm : (m:ℝ) ≤ nn := by rw [hnn]; push_cast; linarith [(N.cast_nonneg : (0:ℝ) ≤ N)]
    have hm1 : (M + 3)/(A - A') < nn := by linarith
    have hm2 : 1/A < nn := by linarith
    have hsepn : M + 3 < (A - A') * nn := by rwa [div_lt_iff₀' hAA'] at hm1
    have hAn : 1 < A * nn := by rwa [div_lt_iff₀' hA] at hm2
    obtain ⟨Bn, hBn1, hBn2⟩ := hb nn (by omega)
    have hbs : (A * nn) - 1 ≤ ((bandStart A nn : ℤ) : ℝ) := by
      unfold bandStart; push_cast; linarith [Int.le_ceil (A * (nn:ℝ))]
    refine ⟨Fin.snoc n0 nn, Fin.snoc B0 Bn, ?_, ?_, ?_, ?_⟩
    · intro i
      induction i using Fin.lastCases with
      | last => simp only [Fin.snoc_last]; omega
      | cast i => simp only [Fin.snoc_castSucc]; exact h1 i
    · intro i
      induction i using Fin.lastCases with
      | last =>
        simp only [Fin.snoc_last]
        have : (1:ℝ) ≤ ((bandStart A nn : ℤ) : ℝ) := by
          unfold bandStart; push_cast
          have := Int.ceil_lt_add_one (A * (nn:ℝ))
          have h2 : (1:ℤ) < ⌈A * (nn:ℝ)⌉ := by
            rw [Int.lt_ceil]; push_cast; exact hAn
          have : (2:ℝ) ≤ (⌈A * (nn:ℝ)⌉ : ℝ) := by exact_mod_cast h2
          linarith
        exact_mod_cast this
      | cast i => simp only [Fin.snoc_castSucc]; exact h2 i
    · intro i
      induction i using Fin.lastCases with
      | last => simp only [Fin.snoc_last]; exact hBn2
      | cast i => simp only [Fin.snoc_castSucc]; exact h3 i
    · intro i h hhi
      induction i using Fin.lastCases with
      | last =>
        induction h using Fin.lastCases with
        | last => exact absurd hhi (lt_irrefl _)
        | cast h =>
          simp only [Fin.snoc_last, Fin.snoc_castSucc]
          have hle : |(B0 h : ℝ)| ≤ M :=
            Finset.single_le_sum (f := fun h => |(B0 h : ℝ)|) (fun _ _ => abs_nonneg _) (Finset.mem_univ h)
          have := le_abs_self (B0 h : ℝ)
          nlinarith
      | cast i =>
        induction h using Fin.lastCases with
        | last => exact absurd hhi (not_lt.mpr (Fin.castSucc_lt_last i).le)
        | cast h =>
          simp only [Fin.snoc_castSucc]
          exact h4 i h (Fin.castSucc_lt_castSucc_iff.mp hhi)

